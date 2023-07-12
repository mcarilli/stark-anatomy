from fri import *
from univariate import *
from multivariate import *
from functools import reduce
import os

class Stark:
    def __init__( self, field, expansion_factor, num_colinearity_checks, security_level, num_registers, num_cycles, transition_constraints_degree=2 ):
        assert(len(bin(field.p)) - 2 >= security_level), "p must have at least as many bits as security level"
        assert(expansion_factor & (expansion_factor - 1) == 0), "expansion factor must be a power of 2"
        assert(expansion_factor >= 4), "expansion factor must be 4 or greater"
        assert(num_colinearity_checks * 2 >= security_level), "number of colinearity checks must be at least half of security level"

        self.field = field
        self.expansion_factor = expansion_factor
        self.num_colinearity_checks = num_colinearity_checks
        self.security_level = security_level

        self.num_randomizers = 4*num_colinearity_checks

        self.num_registers = num_registers
        self.original_trace_length = num_cycles
        
        randomized_trace_length = self.original_trace_length + self.num_randomizers
        omicron_domain_length = 1 << len(bin(randomized_trace_length * transition_constraints_degree)[2:])
        fri_domain_length = omicron_domain_length * expansion_factor

        print("transition_constraints_degree {}\noriginal_trace_length {}\nrandomized_trace_length {}\nomicron_domain_length {}".format(
               transition_constraints_degree, self.original_trace_length,     randomized_trace_length,     omicron_domain_length))

        self.generator = self.field.generator()
        self.omega = self.field.primitive_nth_root(fri_domain_length)
        self.omicron = self.field.primitive_nth_root(omicron_domain_length)
        self.omicron_domain = [self.omicron^i for i in range(omicron_domain_length)]

        self.fri = Fri(self.generator, self.omega, fri_domain_length, self.expansion_factor, self.num_colinearity_checks)

    def transition_degree_bounds( self, transition_constraints ):
        """
        https://aszepieniec.github.io/stark-anatomy/stark#prove
        "Another difference is that the transition constraints have 2 w + 1 variables rather than 2 w.
        The extra variable takes the value of the evaluation domain over which the execution trace is interpolated.
        This feature anticipates constraints that depend on the cycle, for instance to evaluate a hash function
        that uses round constants that are different in each round."
        In other words each transition polynomial p_i is
        p_i(t_X(X), t0(X), ...t_{w-1}(X), t0(o * X), ...t_{w-1}(o * X)) where t_X(X) = X.
        Why can't any p_is include direct terms involving X (as opposed to t_*(X))?
          I think that is what t_X(X) = X provides. The caller can attach any degree of t_X to any term in a given p_i.
          first_step_constants and second_step_constants are direct functions of the cycle index X.
          Afaict the constraint builder inserts these direct functions as a function of the first variable in the MPolynomial,
          anticipating that the prover will pass t_X = X to the MPolynomial's first symbolic variable slot and the verifier
          will pass domain_current_index to that slot.
        Alternatively, one could imagine a "purpose built" prover and verifier where the prover internally holds
          t_0 = <polynomial that interpolates some constants> and passes that during codeword construction,
          verifier internally knows the evaluations of t_0 and passes them when it checks the codeword,
          and the constraint builder uses t_0 anticipating the prover and verifier will do so.
          But then we might need two "t_0"s, for first_step and second_step.
        NB: The trace and boundary polynomials vary for different inputs/proof runs. The round constant interpolants dont.
          If we wanted a "one-off" prover and verifier to verify just one input value, we could define the constraint polynomials
          entirely in terms of X. For different inputs, we can only do so for the round constant interpolants.
        NB: Constraint polynomials are independently known and applied by prover and verifier.

        A given (k, v) entry represents one term, ie
        (7, 0, 0, 1, 0) 238501873350547807154239999251679632315
        represents
        238501873350547807154239999251679632315 * X^7 * t0(o * X)^1
        """
        point_degrees = [1] + [self.original_trace_length+self.num_randomizers-1] * 2*self.num_registers
        # print(point_degrees)
        # for k, v in transition_constraints[0].dictionary.items():
        #     print(k, v)
        ret = [max( sum(r*l for r, l in zip(point_degrees, k)) for k, v in a.dictionary.items()) for a in transition_constraints]
        print(ret)
        return ret

    def transition_quotient_degree_bounds( self, transition_constraints ):
        return [d - (self.original_trace_length-1) for d in self.transition_degree_bounds(transition_constraints)]

    def max_degree( self, transition_constraints ):
        md = max(self.transition_quotient_degree_bounds(transition_constraints))
        return (1 << (len(bin(md)[2:]))) - 1

    def transition_zerofier( self ):
        domain = self.omicron_domain[0:(self.original_trace_length-1)]
        return Polynomial.zerofier_domain(domain)

    def boundary_zerofiers( self, boundary ):
        zerofiers = []
        for s in range(self.num_registers):
            points = [self.omicron^c for c, r, v in boundary if r == s]
            zerofiers = zerofiers + [Polynomial.zerofier_domain(points)]
        return zerofiers

    def boundary_interpolants( self, boundary ):
        interpolants = []
        for s in range(self.num_registers):
            points = [(c,v) for c, r, v in boundary if r == s]
            domain = [self.omicron^c for c,v in points]
            values = [v for c,v in points]
            interpolants = interpolants + [Polynomial.interpolate_domain(domain, values)]
        return interpolants

    def boundary_quotient_degree_bounds( self, randomized_trace_length, boundary ):
        randomized_trace_degree = randomized_trace_length - 1
        return [randomized_trace_degree - bz.degree() for bz in self.boundary_zerofiers(boundary)]

    def sample_weights( self, number, randomness ):
        return [self.field.sample(blake2b(randomness + bytes(i)).digest()) for i in range(0, number)]

    def prove( self, trace, transition_constraints, boundary, proof_stream=None ):
        # create proof stream object if necessary
        if proof_stream == None:
            proof_stream = ProofStream()

        print("len(trace) {}".format(len(trace)))
        
        # concatenate randomizers
        for k in range(self.num_randomizers):
            trace = trace + [[self.field.sample(os.urandom(17)) for s in range(self.num_registers)]]

        # interpolate
        trace_domain = [self.omicron^i for i in range(len(trace))]
        trace_polynomials = []
        for s in range(self.num_registers):
            single_trace = [trace[c][s] for c in range(len(trace))]
            trace_polynomials = trace_polynomials + [Polynomial.interpolate_domain(trace_domain, single_trace)]

        # subtract boundary interpolants and divide out boundary zerofiers
        boundary_quotients = []
        for s in range(self.num_registers):
            interpolant = self.boundary_interpolants(boundary)[s]
            zerofier = self.boundary_zerofiers(boundary)[s]
            quotient = (trace_polynomials[s] - interpolant) / zerofier
            boundary_quotients += [quotient]

        # commit to boundary quotients
        fri_domain = self.fri.eval_domain()
        boundary_quotient_codewords = []
        boundary_quotient_Merkle_roots = []
        for s in range(self.num_registers):
            boundary_quotient_codewords = boundary_quotient_codewords + [boundary_quotients[s].evaluate_domain(fri_domain)]
            merkle_root = Merkle.commit(boundary_quotient_codewords[s])
            proof_stream.push(merkle_root)

        # symbolically evaluate transition constraints
        point = [Polynomial([self.field.zero(), self.field.one()])] + trace_polynomials + [tp.scale(self.omicron) for tp in trace_polynomials]
        # this could be done in a different order (first compress constraints then evaluate_symbolic(point) once)
        transition_polynomials = [a.evaluate_symbolic(point) for a in transition_constraints]
        r_weights = self.sample_weights(len(transition_polynomials), proof_stream.prover_fiat_shamir())
        print("r_weights in prover", [r.value for r in r_weights])
        master_transition_polynomial = reduce(lambda a, b : a + b,
                                              [Polynomial([r_weights[i]]) * transition_polynomials[i] for i in range(len(r_weights))],
                                              Polynomial([]))

        # divide out zerofier
        master_transition_quotient = master_transition_polynomial / self.transition_zerofier()

        # commit to randomizer polynomial
        randomizer_polynomial = Polynomial([self.field.sample(os.urandom(17)) for i in range(self.max_degree(transition_constraints)+1)])
        randomizer_codeword = randomizer_polynomial.evaluate_domain(fri_domain) 
        randomizer_root = Merkle.commit(randomizer_codeword)
        proof_stream.push(randomizer_root)

        # get weights for nonlinear combination
        #  - 1 randomizer
        #  - 2 for every transition quotient
        #  - 2 for every boundary quotient
        weights = self.sample_weights(1 + 2 + 2 * len(boundary_quotients), proof_stream.prover_fiat_shamir())

        assert master_transition_quotient.degree() == max(self.transition_quotient_degree_bounds(transition_constraints)), \
               "transition quotient degrees do not match with expectation"

        # compute terms of nonlinear combination polynomial
        x = Polynomial([self.field.zero(), self.field.one()])
        max_degree = self.max_degree(transition_constraints)
        print("max_degree {}".format(max_degree))
        terms = []
        terms += [randomizer_polynomial]
        terms += [master_transition_quotient]
        shift = max_degree - master_transition_quotient.degree()
        terms += [(x^shift) * master_transition_quotient]
        for i in range(self.num_registers):
            terms += [boundary_quotients[i]]
            shift = max_degree - self.boundary_quotient_degree_bounds(len(trace), boundary)[i]
            terms += [(x^shift) * boundary_quotients[i]]

        # take weighted sum
        # combination = sum(weights[i] * terms[i] for all i)
        combination = reduce(lambda a, b : a+b, [Polynomial([weights[i]]) * terms[i] for i in range(len(terms))], Polynomial([]))

        # compute matching codeword
        combined_codeword = combination.evaluate_domain(fri_domain)

        # prove low degree of combination polynomial, and collect indices
        indices = self.fri.prove(combined_codeword, proof_stream)
        print("indices", indices)

        # process indices
        duplicated_indices = [i for i in indices] + [(i + self.expansion_factor) % self.fri.domain_length for i in indices]
        quadrupled_indices = [i for i in duplicated_indices] + [(i + (self.fri.domain_length // 2)) % self.fri.domain_length for i in duplicated_indices]
        quadrupled_indices.sort()

        # open indicated positions in the boundary quotient codewords
        for bqc in boundary_quotient_codewords:
            for i in quadrupled_indices:
                proof_stream.push(bqc[i])
                path = Merkle.open(i, bqc)
                proof_stream.push(path)

        # ... as well as in the randomizer
        for i in quadrupled_indices:
            proof_stream.push(randomizer_codeword[i])
            path = Merkle.open(i, randomizer_codeword)
            proof_stream.push(path)

        # the final proof is just the serialized stream
        return proof_stream.serialize()

    def verify( self, proof, transition_constraints, boundary, proof_stream=None ):
        H = blake2b

        # infer trace length from boundary conditions
        original_trace_length = 1 + max(c for c, r, v in boundary)
        randomized_trace_length = original_trace_length + self.num_randomizers

        # deserialize with right proof stream
        if proof_stream == None:
            proof_stream = ProofStream()
        proof_stream = proof_stream.deserialize(proof)

        # get Merkle roots of boundary quotient codewords
        boundary_quotient_roots = []
        for s in range(self.num_registers):
            boundary_quotient_roots = boundary_quotient_roots + [proof_stream.pull()]

        r_weights = self.sample_weights(len(transition_constraints), proof_stream.verifier_fiat_shamir())
        print("r_weights in verifier", [r.value for r in r_weights])
        # we could combine transition_constraints into one master constraint here, doing some symbolic algebra here
        # to avoid multiple explicit point evaluations for master_transition_constraint_value below

        # get Merkle root of randomizer polynomial
        randomizer_root = proof_stream.pull()

        # get weights for nonlinear combination
        #  - 1 randomizer
        #  - 2 for every transition quotient
        #  - 2 for every boundary quotient
        weights = self.sample_weights(1 + 2 + 2*len(self.boundary_interpolants(boundary)), proof_stream.verifier_fiat_shamir())

        # verify low degree of combination polynomial
        polynomial_values = []
        verifier_accepts = self.fri.verify(proof_stream, polynomial_values)
        polynomial_values.sort(key=lambda iv : iv[0])
        if not verifier_accepts:
            return False

        indices = [i for i,v in polynomial_values]
        values = [v for i,v in polynomial_values]
        print("indices in verifier", indices)

        # read and verify leafs, which are elements of boundary quotient codewords
        duplicated_indices = [i for i in indices] + [(i + self.expansion_factor) % self.fri.domain_length for i in indices]
        duplicated_indices.sort()
        leafs = []
        for r in range(len(boundary_quotient_roots)):
            leafs = leafs + [dict()]
            for i in duplicated_indices:
                leafs[r][i] = proof_stream.pull()
                path = proof_stream.pull()
                verifier_accepts = verifier_accepts and Merkle.verify(boundary_quotient_roots[r], i, path, leafs[r][i])
                if not verifier_accepts:
                    return False
        print("len(leafs[0])", len(leafs[0]))

        # read and verify randomizer leafs
        randomizer = dict()
        for i in duplicated_indices:
            randomizer[i] = proof_stream.pull()
            path = proof_stream.pull()
            verifier_accepts = verifier_accepts and Merkle.verify(randomizer_root, i, path, randomizer[i])
            if not verifier_accepts:
                return False

        # verify leafs of combination polynomial
        for i in range(len(indices)):
            current_index = indices[i] # do need i

            # get trace values by applying a correction to the boundary quotient values (which are the leafs)
            domain_current_index = self.generator * (self.omega^current_index)
            next_index = (current_index + self.expansion_factor) % self.fri.domain_length
            domain_next_index = self.generator * (self.omega^next_index)
            current_trace = [self.field.zero() for s in range(self.num_registers)]
            next_trace = [self.field.zero() for s in range(self.num_registers)]
            for s in range(self.num_registers):
                zerofier = self.boundary_zerofiers(boundary)[s]
                interpolant = self.boundary_interpolants(boundary)[s]

                current_trace[s] = leafs[s][current_index] * zerofier.evaluate(domain_current_index) + interpolant.evaluate(domain_current_index)
                next_trace[s] = leafs[s][next_index] * zerofier.evaluate(domain_next_index) + interpolant.evaluate(domain_next_index)

            point = [domain_current_index] + current_trace + next_trace
            master_transition_constraint_value = reduce(lambda a, b: a + b,
                                                        [r_weights[s] * transition_constraints[s].evaluate(point) for s in range(len(transition_constraints))],
                                                        self.field.zero())

            # compute nonlinear combination
            counter = 0
            terms = []
            terms += [randomizer[current_index]]

            quotient = master_transition_constraint_value / self.transition_zerofier().evaluate(domain_current_index)
            terms += [quotient]
            shift = self.max_degree(transition_constraints) - max(self.transition_quotient_degree_bounds(transition_constraints))
            terms += [quotient * (domain_current_index^shift)]

            for s in range(self.num_registers):
                bqv = leafs[s][current_index] # boundary quotient value
                terms += [bqv]
                shift = self.max_degree(transition_constraints) - self.boundary_quotient_degree_bounds(randomized_trace_length, boundary)[s]
                terms += [bqv * (domain_current_index^shift)]
            combination = reduce(lambda a, b : a+b, [terms[j] * weights[j] for j in range(len(terms))], self.field.zero())

            # verify against combination polynomial value
            verifier_accepts = verifier_accepts and (combination == values[i])
            if not verifier_accepts:
                return False

        return verifier_accepts

