// Necessary standard library encodings
require open Stdlib.Set Stdlib.Prop Stdlib.FOL Stdlib.Epsilon Stdlib.HOL Stdlib.Eq Stdlib.Impred Stdlib.Nat Stdlib.Bool Stdlib.List Stdlib.Classic;

// Encodings derived in the scope of the Leo-III encoding effort
require open lambdapi-examples.simpRules lambdapi-examples.literalLevelOperations lambdapi-examples.userDefinedTacticsPrelim;

/***************************************************************************
 This file documents the encoding of the rules of the EP calculus as presented in:
    Alexander Steen, *Extensional Paramodulation for Higher-Order Logic 
    and its Effective Implementation Leo-III*, Dissertation, Freie 
    Universität Berlin, 2018. Published in the series *Dissertations in 
    Artificial Intelligence (DISKI)*, Volume 345, ISBN 978-3-89838-739-2.

 The naming conventions and categorization of rules follow those used in
 Steen’s dissertation. The rules are grouped into the following categories:
    • Unification Rules
    • Clausification Rules
    • Extensionality Rules
    • Primary Inference Rules
    • Extended Calculus

 For each rule, we provide:

 (1) A discussion of its encoding, which falls into one of the following types:
       (i)  an explicit encoding as an equational or functional theorem in Lambdapi
       (ii) a procedure describing how to encode applications using 
            existing theorems or tactics
       (iii) a justification why no encoding is required

 (2) An indication of whether the rule is implemented in the current Lambdapi 
     output of Leo-III.

 (3) A minimal example illustrating the rule’s use. The following naming
     conventions are used for each rule R:

       symbol axiom_R_example   – a clause that contains the relevant literal(s)
       symbol proof_R_example   – a proof term that eliminates or transforms them

 Notes: 
     • Generated proofs often rely on additional implicit transformations and
       performed by the Leo-III implementation (e.g. permutation of clauses, simplifications, ...). 
       These are omitted here but can generally be encoded using additional steps in proofs.
     • Here we define a new symbol for rule applications that - in the automatically generated
       encodings of longer proofs - would each be defined as a sub-step in longer proofs. This does
       not affect the proofs themselves but only defines the symbols representing the encoded steps
       locally. 
****************************************************************************/

// Declaration of various constants used in the examples:
symbol c : Prop;
symbol d : Prop;

symbol s : τ ι;
symbol t : τ ι;
symbol u : τ ι;
symbol v : τ ι;

symbol f : τ (ι ⤳ ι);
symbol g : τ (ι ⤳ ι);
symbol f_2 : τ (ι ⤳ ι ⤳ ι);
symbol g_2 : τ (ι ⤳ ι ⤳ ι);

symbol p : τ (ι ⤳ o);


/******************************************************************************
 *  Unification Rules                                                 
 ******************************************************************************/

 // ────────── (Triv) 
 // Implemented
 // 
 // Description:
 //    Eliminates literals of the form ¬(s = s), which are logically equivalent to ⊥.
 //    These typically appear as unification constraints after instantiation.
 
 //  Encoding:
 //    In a first step, we prove the implication c ∨ ¬(s = s) ⇒ c
 //    This is proved via a sequence of simplification steps:
 //      - `¬=_idem`    rewrites ¬(s = s) to ⊥
 //      - `∨⊥` or `⊥∨` removes ⊥ from the disjunction
 //    The resulting implication  c ⇒ c  can be proven via:
 //      - `⇒_idem`     collapses trivial implications to ⊤
 //      - `⊤ᵢ`         completes the proof of the goal
 //    These steps can be applied manually or via the user-defined tactic below:
 symbol Triv ≔ #and (#and (#rewrite ¬=_idem) ((#rewrite ∨⊥) #orelse (#rewrite ⊥∨))) (#and (#rewrite ⇒_idem) (#refine ⊤ᵢ));

 // Example application
 symbol axiom_Triv_example: π (c ∨ ¬(s = s));
 symbol proof_Triv_example: π (c)≔
 begin
    // Proof the implication
    have Triv_inst : π (c ∨ ¬(s = s) ⇒ c)
        {eval Triv};
    // Use the proven implication to derive the conjecture
    refine Triv_inst axiom_Triv_example
 end;


 // ────────── (Bind)
 // Implemented
 //
 //  Description:
 //    The (Bind) rule handles so-called unification constraints of the form ¬(X = s),
 //    where X is a free variable and s is a term. These constraints are resolved by
 //    substituting X with s in the remainder of the clause.
 
 //  Encoding:
 //    Applying (Bind) requires the instantiation of the variable X via application and
 //    leads to a literal ¬(s = s), which is then eliminated using the (Triv) rule.
 //    Thus, (Bind) reduces to two steps:
 //      1. Instantiation of a free variable
 //      2. Elimination of the resulting ¬(s = s) using the `Triv` tactic
 //
 //  Example:
 symbol axiom_Bind_example: Π x, π (p x ∨ ¬(x = s));
 symbol proof_Bind_example: π (p s)≔
 begin
    // Instantiation of a free variable
    have Axiom_inst: π (p s ∨ ¬(s = s))
        {refine axiom_Bind_example s};
    // Elimination of the resulting ¬(s = s) using the `Triv` tactic
    have Triv_inst : π ((p s ∨ ¬(s = s)) ⇒ p s)
        {eval Triv};
    refine Triv_inst Axiom_inst
 end;


 // ────────── (Decomp) 
 // Not implemented
 //  Description:
 //    From an inequality between two applied terms ¬(f s₀ ... sₙ = f t₀ ... tₙ), infer 
 //    that at least one of the arguments differ.

 //  Encoding:
 //    The theorem `Decomp` takes a literal ¬(f s = g t) and derives that either 
 //    ¬(f = g) or ¬(s = t). This allows the use of the theorem for repeated applications,
 //    as it also handles unidentical head symbols. For the final application with identical 
 //    head symbols, the rule derives ¬(f = f) ∨ ¬(s = t), the former can be removed using Triv.
 //    The rule is applied using the `transform` theorem.
 symbol Decomp [a b : Set] (s t : τ a) (f g : τ(a ⤳ b)): 
    π (¬ (f s = g t)) → π (¬ (s = t) ∨ ¬ (f = g)) ≔
 begin
    assume a b s t f g h0;
    refine ∨ₑ (em (s = t)) _ _
        {assume h1; refine ∨ₑ (em (f = g)) _ _
            {assume h2;
            refine ⊥ₑ [¬ (s = t) ∨ ¬ (f = g)] (h0 (ind_eq h1 (λ x, f x = g t) (ind_eq h2 (λ x, x t = g t) (eq_refl (g t)))))}
            {assume h2; refine ∨ᵢ₂ h2}}
        {assume h1; refine ∨ᵢ₁ h1}
 end;

 // Example 
 symbol axiom_Decomp_example: π (c ∨ ¬((f_2 s t) = (f_2 u v)));
 symbol proof_Decomp_example: π (c ∨ ¬(t = v) ∨ ¬(s = u))≔
 begin
    // Repeated application of `Decomp`
    have Decomp_Inst_1 : π (¬ (f_2 s t = f_2 u v)) → π (¬ (t = v) ∨ ¬ (f_2 s = f_2 u))
        {refine Decomp [ι] [ι] t v (f_2 s) (f_2 u)};
    have Decomp_App1 : π (c ∨ ¬ (t = v) ∨ ¬ (f_2 s = f_2 u))
        {refine transform [¬(t = v) ∨ ¬ (f_2 s = f_2 u)] (c ⸬ ¬((f_2 s t) = (f_2 u v)) ⸬ □) 1 Decomp_Inst_1 axiom_Decomp_example};
    have Decomp_Inst_2 : π (¬ (f_2 s = f_2 u)) → π (¬ (s = u) ∨ ¬ (f_2 = f_2))
        {refine Decomp [ι] [ι ⤳ ι] s u f_2 f_2};
    have Decomp_App_2 : π (c ∨ ¬(t = v) ∨ ¬(s = u) ∨ ¬(f_2 = f_2))
        {refine transform (c ⸬  ¬ (t = v) ⸬ ¬(f_2 s = f_2 u) ⸬ □) 2 Decomp_Inst_2 Decomp_App1};
    // Removal from the ¬(f_2 = f_2) using `Triv`
    have Triv_inst : π ((c ∨ ¬(t = v) ∨ ¬(s = u) ∨ ¬(f_2 = f_2)) ⇒ (c ∨ ¬(t = v) ∨ ¬(s = u)))
        {eval Triv};
    refine Triv_inst Decomp_App_2
 end;


 // ────────── (FlexRigid)
 // Not implemented
 //
 //  Description:
 //    This rule addresses unification of a flexible term and a rigid term. It introduces 
 //    an unification constraint equating the flexible head to a concrete approximation.
 
 //  Encoding:
 //    No custom theorem is needed—this is handled directly via `∨ᵢ`.

 // Example 
 symbol axiom_FlexRigid_example: Π (x : τ (ι ⤳ ι)),  π (c ∨ ¬(x t = f_2 s t));
 symbol proof_FlexRigid_example: Π (x : τ (ι ⤳ ι)),  π ((c ∨ ¬ (x t = f_2 s t)) ∨ (x = f_2 s))≔
 begin
    assume x;
    refine ∨ᵢ₁ [c ∨ ¬((x t) = (f_2 s t))] [(x = f_2 s)] (axiom_FlexRigid_example x);
 end;


 // ────────── (FlexFlex)
 // As empirical evidence showed this rule can in practice be omitted, it is not implemented 
 // in Leo-III and thus needs not be encoded.


 /******************************************************************************
 *  Clausification Rules                                                 
 ******************************************************************************/

 // ─────── Boolean Equalities Used Implicitly During Clausification
 // Not implemented
 //
 //  Description:
 //     During the clausification process, several standard Boolean equivalences
 //     are applied automatically, though they are not listed as explicit rules
 //     in the EP calculus. These include, for instance, conversion of implication 
 //     into disjunction

 //  Encoding:
 //     Equational theorems were encoded covering these rules. They can be found in 
 //     the file `clausificationRules` and can be applied using the `rewrite` tactic.

 require open lambdapi-examples.clausificationRules;

 // Example 
 symbol axiom_CNF_example: π (c ∧ (((p s) ∨ (f s = g s)) ⇒ p u));
 symbol proof_CNF_example: π (c ∧ (¬ (p s) ∨ p u) ∧ (¬ (f s = g s) ∨ p u)) ≔
 begin
    have RuleApplication : π ((c ∧ (((p s) ∨ (f s = g s)) ⇒ p u)) = (c ∧ ((¬ (p s) ∨ p u) ∧ (¬ (f s = g s) ∨ p u))))
        {rewrite ⇒=∨;
         rewrite deMorgan_∨;
         rewrite ∧∨_dist_l;
         reflexivity};
    rewrite left RuleApplication;
    refine axiom_CNF_example;
 end; 


 // ─────── (CNFConj)
 // Not implemented
 //
 // Description:
 //    This rule selects an individual clause from a conjunction of clauses.

 // Encoding 
 //    The `select` rule handles conjunctions of arbitrary length by working with
 //    sequents and indexed positions. It relies on the same infrastructure as `transform`
 //    and the proof can likewise be found in `literalLevelOperations.lp`

 // Example 
 symbol proof_CNFConj_example: π (¬ (p s) ∨ p u) ≔
 begin
    refine select 1 (c ⸬ (¬ (p s) ∨ p u) ⸬ (¬ (f s = g s) ∨ p u) ⸬ □) ⊤ᵢ proof_CNF_example; 
 end;
    

 // ────────── (CNFDisj), (CNFNeg) (not implemented) and (LiftEq) (implemented)
 //  Description:
 //    • (CNFDisj): Converts nested disjunctions inside literals to top-level disjunctions of literals\n
 //    • (CNFNeg):  Removes negation inside a literal and changes the polarity of it
 //    • (LiftEq):  Lifts literals with equalities to equational literals

 //  Encoding:
 //    No explicit encoding is required in our framework: the chosen representation
 //    of literals in Lambdapi already abstracts away the structural distinctions.
 //    However, as seen in te case of (LiftEq), some cases will require the application of 
 //    boolean identities as the new formation of literals can for instance reorder sides of
 //    equalities or literals in a clause. These instances can be handled by the already 
 //    encoded implicit transformations.

 // Example
 symbol axiom_LiftEq_example: Π x,  π (c ∨ (x = s));
 symbol proof_LiftEq_example: Π x,  π (c ∨ (s = x))≔
 begin
    assume x;
    rewrite =_sym [ι];
    refine axiom_LiftEq_example x
 end;


 // ────────── (CNFAll) 
 // Not implemented
 //  Description:
 //    This rule removes universal quantifiers at the outermost level of literals
 //    and replaces them with implicitly quantified variables (Encoded using dependant types).
 
 //  Encoding:
 //     In our encoding, object-level universal quantifiers at the outer scope are by default
 //     identified with dependant types via the rewrite-system. For individual literals, the
 //     rule application thus needs no encoding. When the literal is part of a longer clause,
 //     the identification is carried out via the `transform` rule.
 
 // Example 
 symbol axiom_CNFAll_example: π (c ∨ (`∀ x, p x));
 symbol proof_CNFAll_example: Π y, π (c ∨ p y)≔
 begin
    // Instanciate free variables
    assume y;
    // Prove the lift of the OL-quantifier
    have CNFAll : π (`∀ x, p x) → π (p y)
        {assume h0; refine h0 y};
    // Use transform to apply the rule
    refine transform (c ⸬ (`∀ x, p x) ⸬ □) 1 CNFAll axiom_CNFAll_example;
 end;


 // ────────── (CNFExist)
 // Not implemented
 //
 // Description:
 //    This rule uses skolemisazion to eliminate existential quantifiers.

 // Encoding 
 //     The rule can be proven as an equational theorem (relying on choice)
 //     and can then be applied using the rewrite tactic
 opaque symbol CNFExist (a: Set) (p: τ a → Prop) :  
 π (¬ (∀ p) = ¬ (p (ε (λ x, ¬ (p x)))))≔
 begin
    assume a p; 
    rewrite ¬∀=∃¬;
    refine  propExt (`∃ x, ¬ (p x)) (¬ (p (ε (λ x, ¬ (p x))))) _ _
        {assume h; refine ind_eq (eq_sym (∃_skolem a (λ x, ¬ (p x)))) (λ x, x) h}
        {assume h; refine ind_eq (∃_skolem a (λ x, ¬ (p x))) (λ x, x) h}
 end;

 // Example:
 symbol axiom_CNFExist_example: π (c ∨ ¬(∀ p));
 // Declare the newly introduced skolem term and define it using the choice operator
 symbol sk1 : τ ι;
 symbol sk1_def : π (sk1 = ε (λ x, ¬ (p x)));
 symbol proof_CNFExist_example: π (c ∨ ¬ (p sk1))≔
 begin
    have Skolemisazion : π (¬ (p sk1) = ¬(∀ p))
        {rewrite CNFExist;
        rewrite sk1_def;
        reflexivity};
    rewrite Skolemisazion;
    refine axiom_CNFExist_example
 end;

 // Cases with free variables are handled analogously:
 symbol axiom_CNFExist_example_2: Π (x : τ ι), π (c ∨ ¬(∀ (λ y, x = y)));
 symbol sk2 : τ ι;
 symbol sk2_def : Π z, π (sk2 = ε (λ (y : τ ι), ¬ (z = y)));
 symbol proof_CNFExist_example_2: Π (x : τ ι),  π (c ∨ ¬ ((λ y, x = y) sk2))≔
 begin
    assume x;
    have Skolemisazion : π (¬ ((λ y, x = y) sk2) = ¬(∀ (λ y, x = y)))
        {rewrite CNFExist;
        rewrite (sk2_def x);
        reflexivity};
    rewrite Skolemisazion;
    refine axiom_CNFExist_example_2 x
 end;


/******************************************************************************
 *  Extensionality Rules                                                 
 ******************************************************************************/

 // ────────── (PBE)
 // Implemented
 // 
 // Description:
 //     Derives the mutual implication of two propositions s and t from their
 //     equality (s = t). In Leo-III, this is split into two new clauses, one 
 //     containing the literals ¬s and t, the other one s and ¬ t

 // Encoding
 //    Encoded as two functions deriving the two possible resulting clauses. 
 //    can be applied to individual literals via the use of the `transform` theorem.
 opaque symbol PBE_r x y: 
   π(x = y) → π(x ∨ ¬ y)≔
 begin
   assume x y h;
   refine ind_eq h (λ z, z ∨ ¬ y) (em y);
 end;

 opaque symbol PBE_l x y: π(x = y) → π(¬ x ∨ y)≔
 begin
   assume x y h;
   have em_sym: π(¬ y ∨ y)
    {refine ∨ₑ(em y)  _ _ 
       {assume h2;
       refine ∨ᵢ₂ h2}
       {assume h2;
       refine ∨ᵢ₁ h2}};
   refine ind_eq h (λ z, ¬ z ∨ y) em_sym;
 end;

 // Example
 symbol axiom_PBE_example: Π x,  π (c ∨ (p s = p x));
 symbol proof_PBE_example: Π x,  π (c ∨ ¬(p s) ∨ (p x))≔
 begin
    assume x;
    refine transform (c ⸬ (p s = p x) ⸬ □) 1 (PBE_l (p s) (p x)) (axiom_PBE_example x);
 end;

 // ────────── (NBE)
 // Implemented
 // 
 // Description:
 //     Analogous to (PBE) for negated qualities between propositions.
 //     This version allows to derive both (s ∨ t) and (¬ s ∨ ¬ t) from
 //     ¬ (s = t).

 // Encoding 
 opaque symbol NBE_p x y:
    π(¬(x = y)) → π(x ∨ y)≔
 begin
    assume x y h1;
    refine ∨ₑ (em x) _ _
        {assume h2;
        refine ∨ᵢ₁ h2}
        {assume h2;
        have H1: π y
            {have H2: π (¬ y) → π ⊥
                {assume h3;
                have H3: π x → π y
                    {assume h4;
                    refine ⊥ₑ (h2 h4)};
                have H4: π y → π x
                    {assume h4;
                    refine ⊥ₑ (h3 h4)};
                refine h1 (propExt x y H3 H4)};
            refine ¬¬ₑ y H2};
        refine ∨ᵢ₂ H1};
 end;
 opaque symbol NBE_n x y: π(¬(x = y)) → π(¬ x ∨ ¬ y)≔
 begin
    assume x y h1;
    refine ∨ₑ (em x) _ _
        {assume h2;
        have H1: π (y) → π ⊥
            {assume h3;
            have H2: π x → π y
                {assume h4;
                refine h3};
            have H3: π y → π x
                {assume h4;
                refine h2};
            refine h1 (propExt x y H2 H3)};
        refine ∨ᵢ₂ H1}
        {assume h2;
        refine ∨ᵢ₁ h2}
 end;

 // Example 
 symbol axiom_NBE_example: Π x,  π (c ∨ ¬(p s = p x));
 symbol proof_NBE_example: Π x,  π (c ∨ (p s ∨ p x))≔
 begin
    assume x;
    refine transform (c ⸬ ¬ (p s = p x) ⸬ □) 1 (NBE_p (p s) (p x)) (axiom_NBE_example x);
 end;


 // ────────── (PFE)
 // Implemented
 // 
 // Description:
 //     Derives the equality of two applied functions (on a fresh variable) 
 //     from the equality of the unapplied functions.

 // Encoding 
 // Encoded as a function that can be applied to individual literals via the
 // `transform` theorem:
 opaque symbol PFE [T] [S] (f g : τ (S ⤳ T)) (x : τ S): 
   π (f = g) → π (f x = g x) ≔
 begin
   assume T S f g x h;
   refine ind_eq h (λ y, y x = g x) (eq_refl [T] (g x))
 end;

 // Example 
 symbol axiom_PFE_example: π (c ∨ (f = g));
 symbol proof_PFE_example: Π x,  π (c ∨ (f x = g x))≔
 begin
    assume x;
    refine transform (c ⸬ (f = g) ⸬ □) 1 (PFE f g x) axiom_PFE_example;
 end;

 // ────────── (NFE)
 // Not implemented
 // 
 //  Description:
 //    From the inequality of two functions f and g, derive that there exists an
 //    input on which they differ and instantiate it with a corresponding Skolem term.

 // Encoding
 //     Encoded as a function that can be applied to individual literals via the 
 //     `transform` theorem.
 symbol NFE [a b : Set]  (f g : τ(a ⤳ b)) : 
    π (¬ (f = g)) → π (¬ (f (ε (λ x, ¬(f x = g x))) = g (ε (λ x, ¬(f x = g x)))))≔
 begin
    assume a b f g h0;
    have H0 : π (`∃ (x: τ a), ¬ (f x = g x))
        {refine ∨ₑ (em (`∀ (x: τ a), (f x = g x))) _ _
            {assume h1;
            refine ⊥ₑ ( h0 (funExt f g h1))}
            {assume h1;
            type ¬∀=∃¬ a (λ x, f x = g x);
            refine ind_eq (eq_sym (¬∀=∃¬ a (λ x, f x = g x))) (λ x, x) h1}};
    refine εᵢ (λ x,  ¬ (f x = g x)) H0
 end;

 // Example
 symbol axiom_NFE_example: π (c ∨ ¬(f = g));
 // Declare the newly introduced Skolem term and define it using the choice operator:
 symbol sk3 : τ ι;
 symbol sk3_def : π (sk3 = ε (λ x, ¬ (f x = g x)));
 symbol proof_NFE_example: π (c ∨ ¬ (f sk3 = g sk3))≔
 begin
    // Instanciate the rule
    have NFE_inst : π ((¬ (f = g)) ⇒ (¬ (f sk3 = g sk3)))
        {rewrite sk3_def;
        refine NFE [ι] [ι] f g};
    // Apply it to prove the conjecture 
    refine transform (c ⸬ (¬(f = g)) ⸬ □) 1 NFE_inst axiom_NFE_example
 end;


/******************************************************************************
 *  Primary Inference Rules                                                 
 ******************************************************************************/

 // ────────── (Fac) 
 // Implemented

 //  Description:
 //    This rule implements equal factoring in Leo-III, relying on the introduction
 //    of unification constraints

 // Encoding
 // Encoded in a version for positive literals and one for negative literals. 
 // In case of longer clauses, affected literals must first be moved to the tail end 
 // of the clause (using `permute`), then the rule can be applied via `transform`
 opaque symbol EqFact_p [T : Set] (x y z v : τ T): 
        (π (x = y ∨ z = v)) → (π (x = y ∨ ¬ (x = z) ∨ ¬ (y = v)))≔
 begin
    assume T x y z v h1;
    refine ∨ₑ (em (x = y)) _ _ 
                {assume h2;
                type ∨ᵢ₁ [x = y] [¬ (x = z)] h2;
                refine ∨ᵢ₁ h2}
                {assume h3;
                refine ∨ₑ (em (x = z)) _ _ 
                    {assume h4;
                    refine ∨ₑ (em (y = v)) _ _ 
                        {assume h5;
                        have H1: π (z = v)
                            {refine ∨ₑ h1 _ _
                                {assume h6;
                                refine ⊥ₑ (h3 h6)}
                                {assume h7;
                                refine h7}};
                        have H2: π(x = v)
                            {refine ind_eq h4 (λ a, a = v) H1};
                        have H3: π(v = y)
                            {refine ind_eq h5 (λ a, v = a) (eq_refl [T] v)};
                        have H4: π(x = y)
                            {refine ind_eq H2 (λ a, a = y) H3};
                        refine ⊥ₑ (h3 H4)}
                        {assume h8;
                        refine ∨ᵢ₂ (∨ᵢ₂ h8)}}
                    {assume h9;
                    refine ∨ᵢ₂ (∨ᵢ₁ h9)}}
 end;
 opaque symbol EqFact_n [T] x y z v: 
        π (¬ (x = y) ∨ ¬ (z = v)) → π (¬ (x = y) ∨ ¬ (x = z) ∨ ¬ (y = v))≔
 begin
    assume T x y z v h1;
    refine (∨ₑ (em (x = y)) _ _ )
                {assume h3;
                refine (∨ₑ (em (x = z)) _ _ ) 
                    {assume h4;
                    refine (∨ₑ (em (y = v)) _ _ )
                        {assume h5;
                        have H1: π(z = x)
                            {refine ind_eq h4 (λ a, z = a) (eq_refl [T] z)};
                        have H2: π(z = y)
                            {refine ind_eq H1 (λ a, a = y) h3};
                        have H3: π( ¬ (z = v))
                            {refine ∨ₑ h1 _ _
                                {assume h6;
                                refine ⊥ₑ (h6 h3)}
                                {assume h6;
                                refine h6}};
                        have H4: π(z = v)
                            {refine ind_eq  H2 (λ a, a = v) h5};
                        refine ⊥ₑ (H3 H4)}
                        {assume h6;
                        refine ∨ᵢ₂ (∨ᵢ₂ h6)}}
                    {assume h4;
                    refine ∨ᵢ₂ (∨ᵢ₁  h4)}}
                {assume h3;
                refine ∨ᵢ₁ h3}
 end;

 // Example
 symbol axiom_EqFact_example: Π x,  π (c ∨ (f_2 s = f_2 x) ∨ (f_2 t = g));
 symbol proof_EqFact_example: Π x,  π (c ∨ (f_2 s = f_2 x) ∨ (¬ (f_2 s = f_2 t) ∨ ¬ (f_2 x = g)))≔
 begin
   assume x;
   refine transform (c ⸬ ((f_2 s = f_2 x) ∨ (f_2 t = g)) ⸬ □) 1 (EqFact_p (f_2 s) (f_2 x) (f_2 t) g) (axiom_EqFact_example x);
 end;


 // ────────── (Para)
 // Not implemented
 //
 //  Description:
 //    Paramodulation performs a conditional rewriting of a subterm using an 
 //    equational literal from another clause. Given two clauses:
 //      • one containing an equality literal (l = r)
 //      • another containing a literal (s = t), where some subterm of s unifies with l
 //    we may derive a clause where:
 //      • the subterm in s is replaced with t
 //      • the unification constraint ¬(s|_pos = l) is added
 //      • the remaining literals from both clauses are preserved

 //  Encoding:
 //    Paramodulation steps must be implemented case-by-case, via concrete rewrite steps,
 //    instantiations, and disjunction handling (∨-introduction/elimination).
 //    Literal-level transformation theorems or user-defined tactics may be introduced to 
 //    simplify such steps in the future.

 // Example 
 symbol axiom_0_Para_example: Π x, π ((p x ∨ p t) = (s = t));
 symbol axiom_1_Para_example: π (p s = p t);
 symbol proof_Para_example: Π x, π ( ¬(p x = p s) ∨ ((p t ∨ p t) = (s = t)))≔
 begin
    assume x;
    rewrite left ⇒=∨;
    assume h0;
    rewrite left .[x in (x ∨ _) = _] axiom_1_Para_example;
    rewrite left h0;
    refine axiom_0_Para_example x;
 end;

 //  Example (with additional literals):
 symbol axiom_0_Para_example_2: Π x, π (c ∨ ((p x ∨ p t) = (s = t)));
 symbol axiom_1_Para_example_2: π (d ∨ (p s = p t));
 symbol proof_Para_example_2: Π x, π ( ¬(p x = p s) ∨ c ∨ ((p t ∨ p t) = (s = t)) ∨ d)≔
 begin
    assume x;
    rewrite left ⇒=∨;
    assume h0;
    refine ∨ₑ axiom_1_Para_example_2 _ _
        {assume h1;
        refine ∨ᵢ₂ [c] (∨ᵢ₂ [(((p t ∨ p t) = (s = t)))] h1)}
        {assume h1;
        rewrite left .[x in _ ∨ ((x ∨ _) = _) ∨ _] h1;
        rewrite left h0;
        refine ∨ₑ (axiom_0_Para_example_2 x) _ _
            {assume h2;
            refine ∨ᵢ₁ [c] [((p x ∨ p t) = (s = t)) ∨ d] h2}
            {assume h2;
            type ∨ᵢ₁ [(p x ∨ p t) = (s = t)] [d] h2;
            refine ∨ᵢ₂ [c] (∨ᵢ₁ [(p x ∨ p t) = (s = t)] [d] h2)}}
 end;


 // ────────── (Prim)
 // Not implemented
 // 
 // Description:
 //     This rule introduces a binding to approximate the structure of a literal
 //     with a flexible head. The instantiation is added as a disjunct (unification-
 //     constraint).

 // Encoding:
 //     Like (FlexRigid), this rule can be verified as an instance of ∨ᵢ₁ and no
 //     new theorem is necessary.

 // Example:
 symbol axiom_Prim_example: Π (x : τ (ι ⤳ ι ⤳ o)),  π (c ∨ ¬(x t s));
 symbol proof_Prim_example: Π (x : τ (ι ⤳ ι ⤳ o)),  π ((c ∨ ¬(x t s)) ∨ (x = (=) [ι]))≔
 begin
    assume x;
    refine ∨ᵢ₁ [c ∨ ¬(x t s)] [x = (=) [ι]] (axiom_Prim_example x);
 end;


/******************************************************************************
 *  Extended Calculus                                               
 ******************************************************************************/

 // ────────── (RW) 
 // Implemented
 //
 // Description:
 //     Given a clause consisting only of an equational literal (s = t), use it
 //     to rewrite a subterm in another clause.
 
 // Encoding:
 //     No additional encoding is necessary as this can be handled directly using 
 //     the standard `rewrite` tactic.
 
 // Example:
 symbol axiom_0_RW_example: π (c ∨ p s);
 symbol axiom_1_RW_example: Π x,  π (p x = ⊤);
 symbol proof_RW_example: π (c ∨ ⊤)≔
 begin
    rewrite left (axiom_1_RW_example s);
    refine axiom_0_RW_example
 end;

 
 // ────────── (DD)
 // Implemented
 //
 // Description:
 //     Justifies the removal of duplicate literals within a single clause.
 
 // Encoding:
 //    Encoded as the rule `delete`, which relies on the same infrastructure
 //    as `transform` and the proof can likewise be found in `literalLevelOperations.lp`
 
 // Example:
 symbol axiom_DD_example: Π x,  π (c ∨ p x ∨ p x);
 symbol proof_DD_example: Π x,  π (c ∨ p x)≔
 begin
   assume x;
   refine delete (0 ⸬ 1 ⸬ 1 ⸬ □) (0 ⸬ 1 ⸬ □) (c ⸬ (p x) ⸬ (p x) ⸬ □) ⊤ᵢ (axiom_DD_example x);
 end;


 // ────────── (Simp)
 // Implemented
 //
 // Description:
 //     Exhaustively applies Boolean identities (such as (x ∨ x) = x) as simplifications.
 //
 // Encoding:
 //     The encoding consists of a total of  of 40 proven Boolean equalities, located in
 //     `simpRules.lp`. These are bundled into a Lambdapi tactic (`applyAllSimplifications`) 
 //     that applies all of them exhaustively using repeated `rewrite` applications.
 //
 // Example:
 symbol axiom_Simp_example: Π x,  π (¬ ((c ⇒ (c ∨ ⊥)) ∨ (p x ∨ p x) = ⊤));
 symbol proof_Simp_example: π ⊥ ≔
 begin
   have SimpApp : π (¬ ((c ⇒ (c ∨ ⊥)) ∨ (p (el ι) ∨ p (el ι)) = ⊤) ⇒ ⊥)
      {eval applyAllSimplifications};
   refine SimpApp (axiom_Simp_example (el ι))
 end;


 // ────────── (TD1), (TD2), (CS), (ACD) 
 //     These rules are used internally by the prover to remove clauses from the
 //     search space. Since they do not contribute to the derivation of the final conclusion,
 //     they are never explicitly referenced in proof certificates and need not be encoded.


 // ────────── (HeuInst)
 // Not implemented
 //
 // Description:
 //     This rule heuristically instantiates universally quantified variables in a
 //     formula. 

 // Encoding:
 //     In Lambdapi, heuristic instantiation is achieved simply by function application 
 //     to the quantified (sub-)term. In some cases, the formula may need to be instantiated inside
 //     nested structures. For this, additional structural lemmas (e.g., for conjunction) that can 
 //     be encoded as equational theorems. Here we give one example for such a rule:
 symbol nestedApp_∧_l x y z : π (x ⇒ z) → π (x ∧ y) → π (z ∧ y)≔
 begin
    assume x y z h0 h1;
    refine ∧ᵢ (h0 (∧ₑ₁ h1)) (∧ₑ₂ h1)
 end;

 // Example (direct instantiation):
 symbol axiom_HeuInst_example_1: π (c ∨ `∀ x, x = (x ∨ x));
 symbol proof_HeuInst_example_1: π (c ∨ ⊤ = (⊤ ∨ ⊤))≔
 begin
     have Inst : π ((`∀ x, x = (x ∨ x)) ⇒ (⊤ = (⊤ ∨ ⊤)))
         {assume h;
         refine h ⊤};
     refine transform (c ⸬ (`∀ x, x = (x ∨ x)) ⸬ □) 1 Inst axiom_HeuInst_example_1
 end;

 // Example (nested instantiation inside a conjunction):
 symbol axiom_HeuInst_example_2: π (c ∨ ((`∀ x, x = (x ∨ x)) ∧ c));
 symbol proof_HeuInst_example_2: π (c ∨ (⊤ = (⊤ ∨ ⊤) ∧ c))≔
 begin
    have Inst : π ((`∀ x, x = (x ∨ x)) ⇒ (⊤ = (⊤ ∨ ⊤)))
         {assume h;
         refine h ⊤};
         type nestedApp_∧_l (`∀ x, x = (x ∨ x)) c (⊤ = (⊤ ∨ ⊤)) Inst;
    have NestedAppliation : π (((`∀ x, x = (x ∨ x)) ∧ c) ⇒ ((⊤ = (⊤ ∨ ⊤)) ∧ c))
        {refine nestedApp_∧_l (`∀ x, x = (x ∨ x)) c (⊤ = (⊤ ∨ ⊤)) Inst};
    refine transform (c ⸬ ((`∀ x, x = (x ∨ x)) ∧ c) ⸬ □) 1 NestedAppliation axiom_HeuInst_example_2
 end;



 // ────────── (PSR), (NSR)
 // Not implemented
 //
 // Description:
 //     These rules allow us to remove equality literals from clauses when they contradict
 //     an already established equality in the proof:
 //     • (PSR) – Positive Superposition Resolution:
 //         From two clauses:  c ∨ ¬(s = t)       and      l = r
 //         If:                there exists σ such that σ(l = r) = (s = t)
 //         Then:              derive c
 //     • (NSR) – Negative Superposition Resolution:
 //         Analogous, but applies to positive equality literals and matching negative ones.

 // Encoding (PSR):
 //     No standalone theorem is required. The encoding is realized using the following steps:
 //     1. Instantiate the equality clause (l = r) so that it becomes (s = t),
 //        then prove (s = t) = ⊤ using the rule `=⊤`.
 //     2. Rewrite the literal ¬(s = t) in the clause to ¬⊥ and then 
 //     3. Eliminate ⊥ from the clause via simplification (e.g. `∨⊥`)
 //    Once again, we can define a tactic carrying out these steps:

 symbol PSR_simp [p : Prop] (rwEq : π (p = ⊤)) ≔ #and (#and (#and (#rewrite rwEq) (#rewrite  ¬⊤)) 
                   ((#rewrite  ∨⊥) #orelse (#rewrite ⊥∨))) (#and (#rewrite ⇒_idem) (#refine ⊤ᵢ));

 // Example
 symbol axiom_0_PSR_example_2: Π y ,π (c ∨ ¬(f t = f_2 t y));
 symbol axiom_1_PSR_example_2: Π x y, π ((f x = f_2 t y));
 symbol proof_PSR_example_2: π c ≔
 begin
    have isTrue : π ((f t = f_2 t (el ι)) = ⊤)
        {rewrite =⊤;
        refine axiom_1_PSR_example_2 t (el ι)};
    have PSR : π ((c ∨ ¬(f t = f_2 t (el ι))) ⇒ c )
        {eval PSR_simp isTrue};
    refine PSR (axiom_0_PSR_example_2 (el ι))
 end;
 // Note:
 //    We use the placeholder constant `el` to denote an arbitrary representative of a given type, 
 //    to instantiate variables as needed. This is justified by the occupation of types in HOL

 // NSR is handled analogously.


 // ────────── (LEQ)
 // Not implemented
 //
 // Description:
 //     Replaces user-defined Leibniz equalities with standard equality.
 //
 //     In the clausified form, a Leibniz equality defined as:
 //         λ x. λ y. `∀ p, p x ⇒ p y
 //     results in two literals: ¬(p x) and (p y), with an implicitly quantified predicate p.
 //     Leo-III handles this by instantiating p with (λ x, s = x).
 //
 // Encoding:
 //     The instantiation is performed directly via application.
 //     The resulting clause can then be simplified using the following lemma:
 symbol LEQ [a : Set] x (s t : τ a): π (x ∨ (¬ (s = s) ∨ (s = t)) ⇒ x ∨ (s = t))≔
 begin
    assume a z s t;
        rewrite ¬=_idem;
        rewrite ⊥∨;
        assume h; refine h
 end;
       
 // Example
 symbol axiom_LEQ_example: Π (q : τ(ι ⤳ o)) , π ((`∀ x, p x ⇒ q x) ∨ ¬(q s) ∨ (q t));
 symbol proof_LEQ_example: π ((`∀ x, p x ⇒ (λ x, s = x) x) ∨ (s = t))≔
 begin
    refine LEQ (`∀ x, p x ⇒ (λ x, s = x) x) s t (axiom_LEQ_example (λ x, s = x));
 end;


 // ────────── (AEQ)
 // Not implemented
 //
 // Description:
 //     Replaces user-defined Andrews equality with standard equality.
 //
 //     Andrews equality is defined as:
 //         λ x. λ y. `∀ r, ∀ z, r z z ⇒ r x y
 //
 //     In clausified form, it may appear as a unification constraint ¬(r s s),
 //     with an implicitly quantified r. Leo-III handles this by instantiating r with (=).
 //
 // Encoding:
 //     Instantiation is done via application. The resulting clause simplifies using:
 symbol AEQ [a : Set] x (s : τ a): π (x ∨ ¬ (s = s) ⇒ x)≔
 begin
    assume a z s;
        rewrite ¬=_idem;
        rewrite ∨⊥;
        assume h; refine h
 end;
       
 // Example 
 symbol axiom_AEQ_example: Π (r : τ(ι ⤳ ι ⤳ o)) , π ((`∀ x, r x s ⇒ p x) ∨ ¬(r s s));
 symbol proof_AEQ_example: π (`∀ x, x = s ⇒ p x)≔
 begin
    refine AEQ (`∀ x, x = s ⇒ p x) s (axiom_AEQ_example (=));
 end;


 // ────────── (ACI)
 // Not implemented
 //
 // Description:
 //     Instantiates the axiom of choice by introducing a choice term ε f
 //     for a predicate f.  

 // Encoding:
 //     This rule is encoded as a Lambdapi theorem, which can be instantiated 
 //     with any predicate:
 symbol ACI [a: Set] (f: (τ a → Prop)) : Π (x : τ a), π (¬ (f x) ∨ (f (ε f)))≔
 begin
    assume a f x;
    rewrite left ⇒=∨;
    assume h0;
    refine εᵢ f (∃ᵢ [a] [f] x h0)
 end;

 // Example
 symbol ACI_example : Π x: τ ι, π (¬ (p x) ∨ p (ε p)) ≔ ACI p;