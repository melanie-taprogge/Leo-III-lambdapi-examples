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

 (2) An indication of whether the the atomated generation of verifiable Lambdapi
        output is implemented for proof steps generated using the rule.

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
    • The automatically generated artifacts make use of user-defined Lambdapi tactics, which 
      encapsulate several operations that are written out explicitly in the examples. In addition, 
      certain examples are expanded into more sub-steps here. These decisions are deliberate and 
      intended to enhance readability.
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
symbol q : τ (ι ⤳ o);


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

 // Note that many of the following examples will involve an application of this 
 //  precise procedure encoded as a substep "Triv_inst".
 
 // Example application
 symbol axiom_Triv_example: π (c ∨ ¬(s = s));
 symbol proof_Triv_example: π (c)≔
 begin
    // Proof the implication
    have Triv_inst : π (c ∨ ¬(s = s) ⇒ c)
        {rewrite ¬=_idem; rewrite ∨⊥; rewrite ⇒_idem; refine ⊤ᵢ};
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
        {rewrite ¬=_idem; rewrite ∨⊥; rewrite ⇒_idem; refine ⊤ᵢ};
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
        {rewrite ¬=_idem; rewrite ∨⊥; rewrite ⇒_idem; refine ⊤ᵢ};
    refine Triv_inst Decomp_App_2
 end;


 // ────────── (FlexRigid) and (FlexFlex)
 // Not implemented
 //
 //  Description:
 //    These rules address unification of a flexible term and - in the case of (FlexRigid) - a 
 //    rigid term or - in the case of (FlexFlex)- a flexible one. They introduce
 //    unification constraints equating the flexible head to a concrete approximation.

 //  Note that as empirical evidence showed that (FlexFlex) can in practice be omitted, it is not 
 //  implemented in Leo-III. It could however be handled exactly like (FlexRigid).
 
 //  Encoding:
 //    No custom theorem is needed—this is handled directly via `∨ᵢ`.

 // Example 
 symbol axiom_FlexRigid_example: Π (x : τ (ι ⤳ ι)),  π (c ∨ ¬(x t = f_2 s t));
 symbol proof_FlexRigid_example: Π (x : τ (ι ⤳ ι)),  π ((c ∨ ¬ (x t = f_2 s t)) ∨ (x = f_2 s))≔
 begin
    assume x;
    refine ∨ᵢ₁ [c ∨ ¬((x t) = (f_2 s t))] [(x = f_2 s)] (axiom_FlexRigid_example x);
 end;


 /******************************************************************************
 *  Clausification Rules                                                 
 ******************************************************************************/

// Note: In our implementation, we rely on user-defined Lambdapi tactics to perform
// the clausification verification steps without reconstructing the exact term
// positions or the precise order of rule applications performed by Leo-III.

 // ─────── Boolean Equalities Used Implicitly During Clausification
 // Implemented
 //
 //  Description:
 //     During the clausification process, several standard Boolean equivalences
 //     are applied automatically, though they are not listed as explicit rules
 //     in the EP calculus. These include, for instance, conversion of implication 
 //     into disjunction.

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
 // Implemented
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
    

 // ────────── (CNFDisj), (CNFNeg), (LiftEq) 
 // Implemented
 //  Description:
 //    • (CNFDisj): Converts nested disjunctions inside literals to top-level disjunctions of literals\n
 //    • (CNFNeg):  Removes negation inside a literal and changes the polarity of it
 //    • (LiftEq):  Lifts literals with equalities to equational literals

 //  Encoding:
 //    No explicit encoding is required in our framework: the chosen representation
 //    of literals in Lambdapi already abstracts away the structural distinctions.
 //    However, as shown in te case of (LiftEq), some cases will require the application of 
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
 //    This rule removes universal quantifiers at the outermost scope of clauses
 //    and replaces them with implicitly quantified variables (Encoded using dependant types).
 
 //  Encoding:
 //     In our encoding, object-level universal quantifiers at the outer scope are by default
 //     identified with dependant types via the rewrite-system. For unit clauses, the
 //     rule application thus needs no encoding. When the literal is part of a longer clause,
 //     the quantifiers can be moved to the outer scope step by step using rules like ∀∨_dist_r 
 //     and ∀∨_dist_l. We can then prove in a sub-step that the premise and conclusion - both 
 //     given as universally quantified terms - are equivalent using ∀_ext.
 
opaque symbol ∀∨_dist_r t a (p : τ(t ⤳ o)): π ((a ∨ ∀ p) = (`∀ x, a ∨ p x))≔
begin
    assume t a p;
    refine propExt (a ∨ ∀ p) (∀(λ x, a ∨ p x)) _ _
        {assume h x;
        refine ∨ₑ h _ _
            {assume h0;
            refine ∨ᵢ₁ h0}
            {assume h0;
            refine ∨ᵢ₂ ((=⇒ (eta_exp_∀ p) h0) x)}}
        {assume h;
        refine ∨ₑ (em (∀ p)) _ _
            {assume h1;
            refine ∨ᵢ₂ h1}
            {assume h1;
            have H0: π (¬ (p (ε (λ x, ¬ (p x)))))
                {refine =⇒ (∀_skolem t p) h1};
            refine ∨ₑ (h (ε (λ x, ¬ (p x)))) _ _
                {assume h0;
                refine ∨ᵢ₁ h0}
                {assume h0;
                refine ⊥ₑ (H0 h0)}}}
end;

opaque symbol ∀∨_dist_l t a (p : τ(t ⤳ o)): π ((∀ p ∨ a) = (`∀ x,p x ∨ a))≔
begin
    assume t a p;
    refine propExt (∀ p ∨ a) (`∀ x,p x ∨ a) _ _
        {assume h0 x;
        rewrite ∨_com;
        refine (=⇒ ((∀∨_dist_r t a p)) (=⇒ (∨_com (∀ p) a) h0)) x}
        {assume h0;
        rewrite ∨_com;
        have H0: π (`∀ x, a ∨ p x)
            {assume x;
            rewrite ∨_com;
            refine h0 x};
        refine =⇒ (eq_sym (∀∨_dist_r t a p)) H0};
end;

opaque symbol ∀_ext [t: Set] [p q] : π(`∀ (x : τ t), p x = q x) → π ((`∀ (x: τ t), p x) = (`∀ (x: τ t), q x))≔
begin
    assume t p q h;
    refine propExt (`∀ (x: τ t), p x) (`∀ (x: τ t), q x) _ _
        {assume h1 x;
        refine =⇒ (h x) (h1 x)}
        {assume h1 x;
        refine =⇒ (eq_sym (h x)) (h1 x)}
end;


 // Example 
 symbol axiom_CNFAll_example: π (c ∨ (`∀ x, p x));
 symbol proof_CNFAll_example: Π y, π (c ∨ p y)≔
 begin
    // substep showing that the axiom is equivalent to the clausfied term
    have CNF_app : π ((c ∨ (`∀ x, p x)) = (`∀ x, (c ∨ p x)))
        {rewrite ∀∨_dist_r;
        refine ∀_ext _;
        assume x; reflexivity};
    refine =⇒ CNF_app axiom_CNFAll_example;
 end;


 symbol axiom_CNFAll_example_2: π (c ∨ (`∀ x, p x) ∨ (`∀ x, q x));

symbol proof_CNFAll_example_2: Π y, Π z, π (c ∨ p y ∨ q z)≔
 begin
    have Clausification: π ((c ∨ (`∀ y, p y) ∨ (`∀ z, q z)) = `∀ z, `∀ y, (c ∨ p y ∨ q z))
        {//eval (#repeat ((assumeVars ("y" ⸬ "z" ⸬ □)) #orelse (#and ((#rewrite  "" "" ∀∨_dist_r) #orelse (#rewrite "" "" ∀∨_dist_l)) #simplify_beta)));
        rewrite ∀∨_dist_r;
        rewrite ∀∨_dist_r;
        refine ∀_ext _; 
        assume x;
        rewrite ∀∨_dist_l;
        rewrite ∀∨_dist_r;
        refine ∀_ext _; 
        assume y;
        reflexivity};
        assume y z;
    refine (=⇒ Clausification axiom_CNFAll_example_2) z y;
 end;


 // ────────── (CNFExist)
 // Implemented
 //
 // Description:
 //    This rule uses Skolemisazion to eliminate existential quantifiers.

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
    have Skolemisazion : π (c ∨ ¬(∀ p) ⇒ c ∨ ¬ (p sk1))
        {rewrite CNFExist; rewrite sk1_def;
        rewrite ⇒_idem; refine ⊤ᵢ};
    refine Skolemisazion axiom_CNFExist_example;
 end;

 // Cases with free variables are handled analogously:
 symbol axiom_CNFExist_example_2: Π (x : τ ι), π (c ∨ ¬(∀ (λ y, x = y)));
 symbol sk2 : τ ι;
 symbol sk2_def : Π z, π (sk2 = ε (λ (y : τ ι), ¬ (z = y)));
 symbol proof_CNFExist_example_2: Π (x : τ ι),  π (c ∨ ¬ ((λ y, x = y) sk2))≔
 begin
    assume x;
    have Skolemisazion : π ((c ∨ ¬(∀ (λ y, x = y))) ⇒ (c ∨ ¬ ((λ y, x = y) sk2)))
        {rewrite CNFExist; rewrite (sk2_def x); simplify rule off;
        rewrite ⇒_idem; refine ⊤ᵢ};
    refine Skolemisazion (axiom_CNFExist_example_2 x)
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
 //     containing the literals ¬ s and t, the other one s and ¬ t

 // Encoding
 //    Encoded as two functions deriving the two possible resulting clauses. 
 //    This rule can be applied to individual literals via the use of the `transform` theorem.
 opaque symbol PBE_r x y: 
   π(x = y) → π(x ∨ ¬ y)≔
 begin
   assume x y h;
   refine ind_eq h (λ z, z ∨ ¬ y) (em y);
 end;

 opaque symbol PBE_l x y: 
    π(x = y) → π(¬ x ∨ y)≔
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
 //     Encoded as an equality and applied via the rewrite tactic.

 // Necessary Lemma
 symbol funExt_neg [a b]  (f g : τ(a ⤳ b)) : π (`∃ x, ¬ (f x = g x)) → π (¬ (f = g))≔
 begin
    assume a b f g h0;
    refine ¬¬ₑ (¬ (f = g)) _; 
    assume h1;
    have Contra : π ((`∃ x, ¬ (f x = g x)) ⇒ ⊥)
        {rewrite  ¬¬ₑ (f = g) h1;
        assume h2;
        refine ∃ₑ h2 _;
        assume x h3;
        refine =⇒ (¬=_idem b (g x)) h3};
    refine Contra h0
 end;

  symbol NFE [a b : Set]  (f g : τ(a ⤳ b)) : 
    π ((¬ (f = g)) = (¬ (f (ε (λ x, ¬(f x = g x))) = g (ε (λ x, ¬(f x = g x))))))≔
 begin
    assume a b f g;
    refine propExt (¬ (f = g)) (¬ (f (ε (λ x, ¬(f x = g x))) = g (ε (λ x, ¬(f x = g x))))) _ _
        {assume h0;
        have H0 : π (`∃ (x: τ a), ¬ (f x = g x))
        {refine ∨ₑ (em (`∀ (x: τ a), (f x = g x))) _ _
            {assume h1;
            refine ⊥ₑ ( h0 (funExt f g h1))}
            {assume h1;
            refine ind_eq (eq_sym (¬∀=∃¬ a (λ x, f x = g x))) (λ x, x) h1}};
        refine εᵢ (λ x,  ¬ (f x = g x)) H0}
        {assume h0;
        have H0: π (`∃ x, ¬ (f x = g x))
            {refine ∃ᵢ [a] [λ x , (¬ (f x = g x))] (ε (λ x, ¬ (f x = g x))) h0};
        refine funExt_neg f g H0}
 end;

 // Example
 symbol axiom_NFE_example: π (c ∨ ¬(f = g));
 // Declare the newly introduced Skolem term and define it using the choice operator:
 symbol sk3 : τ ι;
 symbol sk3_def : π (sk3 = ε (λ x, ¬ (f x = g x)));
 symbol proof_NFE_example2: π (c ∨ ¬ (f sk3 = g sk3))≔
 begin
    rewrite sk3_def;
    rewrite left NFE;
    refine axiom_NFE_example
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
 // Implemented
 //
 // Description:
 //   Paramodulation performs a conditional rewrite of a subterm using an
 //   equational literal from another clause. Given two clauses:
 //     • one containing an equality literal (l = r)
 //     • another containing a literal (s = t), where some subterm s|_pos unifies with l
 //   we derive a clause where:
 //     • the subterm s|_pos is rewritten to r at position pos
 //     • the unification constraint ¬(s|_pos = l) (UF) is added
 //     • the remaining literals from both clauses are preserved
 //
 // Encoding:
 //   Implemented relying on the rewrite tactic, instantiations, and
 //   disjunction handling (∨-intro/elims). The general procedure:
 //     • Case split on UF (using excluded middle, encoded as `em`):
 //       A) UF holds: perform the targeted rewrite. If the clause containing the equational 
 //          literal we perform the rewrite operation with has multiple literals,
 //          use ∨-elimination (the branch containining the rest of the clause can be 
 //          closed using ∨-introdcution). 
 //       B) ¬UF holds: close via ∨-introdcution based on the the negated constraint.
 //
 //   No dedicated Lambdapi rule is required, we do however rely on literal-level transformation
 //   theorems (n-ary ∨-introduction) from "multiND.lp".
 require open lambdapi-examples.multiND;


 // Excluded middle for the UF of this example
 symbol axiom_0_Para_example: Π x, π ((p x ∨ p t) = (s = t));
 symbol axiom_1_Para_example: π (p s = p t);
 symbol proof_Para_example: Π x, π (((p t ∨ p t) = (s = t)) ∨  ¬(p x = p s))≔
 begin
    assume x;
    // Case split on UF: (p x = p s) ∨ ¬(p x = p s)
    refine ∨ₑ (em  (p x = p s)) _ _
        {// Case A: UF is TRUE
        assume UF;

        // rewriting with both equalities will render the first literal equal to `axiom_0_Para_example`
        rewrite left .[x in ((x ∨ _) = _) ∨ _] axiom_1_Para_example;
        rewrite left .[x in ((x ∨ _) = _) ∨ _] UF;

        // refine using ∨ introduction:
        refine ∨ᵢ₁ (axiom_0_Para_example x)}

        {// Case B: UF is FALSE
        assume nUF;
        // Close by introducing the left disjunct ¬UF
        refine ∨ᵢ₂ nUF}
end;


 //  Example (with additional literals):
 symbol axiom_0_Para_example_2: Π x, π (c ∨ ((p x ∨ p t) = (s = t)));
 symbol axiom_1_Para_example_2: π (d ∨ (p s = p t));
 symbol proof_Para_example_2: Π x, π (c ∨ ((p t ∨ p t) = (s = t)) ∨ d ∨ ¬(p x = p s))≔
 begin
    assume x;
    // Case split on UF: (p x = p s) ∨ ¬(p x = p s)
    refine ∨ₑ (em (p x = p s)) _ _
        {// Case A: UF is TRUE
        assume UF;
        // Case split on clause axiom_1_Para_example_2
        refine ∨ₑ axiom_1_Para_example_2 _ _
            {// Case A: the rest of example clause holds
            assume restClause;
            // we can thus refine using ∨-indtoruction
            refine (∨ᵢₙ₂ (c ⸬ ((p t ∨ p t) = (s = t))  ⸬ □) (d ⸬ ¬ (p x = p s) ⸬ □) (∨ᵢ₁ restClause))}

            // Case B: Equational literal of example clause holds
            {assume EL;
            // rewriting with both equalities will render the first half of the clause equal to `axiom_0_Para_example`
            rewrite left .[x in (_ ∨ (((x ∨ _) = _) ∨ _ ∨ _))] EL;
            rewrite left .[x in (_ ∨ (((x ∨ _) = _) ∨ _ ∨ _))] UF;
            // we can thus refine using ∨-indtoruction
            refine ∨ᵢₙ₁ (c ⸬ (((p x ∨ p t) = (s = t))) ⸬ □) (d ⸬ ¬ (p x = p s) ⸬ □) (axiom_0_Para_example_2 x)}}

        {// Case B: UF is FALSE
        assume nUF;
        // Close by introducing the left disjunct ¬UF
        refine ∨ᵢₙ₂ (c ⸬ (((p t ∨ p t) = (s = t))) ⸬ d ⸬ □) (¬ (p x = p s) ⸬ □) nUF}
 end;


 // ────────── (Prim)
 // Not implemented
 // 
 // Description:
 //     This rule introduces a binding to approximate the structure of a literal
 //     with a flexible head. The instantiation is added as a unification-constraint.

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
 //     No standalone theorem is required. In the encoding we can simply define a substep
 //     that proves the remaining clause `c` from the clause `c ∨ ¬(s = t)` by using the
 //     rewrite tactic with the instanciated unit-clause `l = r` and then deleting the resulting
 //     trivially false equational literal using the procedure defined for (Triv).

 // Example
 symbol axiom_0_PSR_example_2: Π y ,π (c ∨ ¬(f t = f_2 t y));
 symbol axiom_1_PSR_example_2: Π x y, π ((f x = f_2 t y));
 symbol proof_PSR_example_2: π c ≔
 begin
    have Triv_inst : π (((c ∨ ¬(f t = f_2 t (el ι)))) ⇒ c)
        {rewrite axiom_1_PSR_example_2 t (el ι);
        rewrite ¬=_idem; rewrite ∨⊥; rewrite ⇒_idem; refine ⊤ᵢ};
    refine Triv_inst (axiom_0_PSR_example_2 (el ι))
 end;
 // Note:
 //    We use the placeholder constant `el` to denote an arbitrary representative of a given type, 
 //    to instantiate variables disappearing from the clause as a result of the rule application as needed. 
 //    This is justified by the occupation of types in HOL.

 // NSR is handled similarly, but here we have to do a case-split on the literals of the clause `c ∨ (f t = f_2 t y)`
 // In the first case, we reason under the assumtion of `c`, which can simply be used to instanciate the goal. 
 // In the second case, we assume `(f t = f_2 t y)`, this can be used with the rewrite tactic to derive a contradition
 // with `(¬(f x = f_2 t y))`:
 symbol axiom_0_NSR_example_2: Π y ,π (c ∨ (f t = f_2 t y));
 symbol axiom_1_NSR_example_2: Π x y, π (¬(f x = f_2 t y));
 symbol proof_NSR_example_2: π c ≔
 begin
    refine ∨ₑ (axiom_0_NSR_example_2 (el ι)) _ _
        {assume piC; refine piC}
        {assume eqLit; 
        have Triv_inst : π (¬(f t = f_2 t (el ι)) ⇒ ⊥)
            {rewrite eqLit ;
            rewrite ¬=_idem; rewrite ⇒_idem; refine ⊤ᵢ};
        refine ⊥ₑ (Triv_inst (axiom_1_NSR_example_2 t (el ι)))};
 end;


 // ────────── (LEQ)
 // Not implemented
 //
 // Description:
 //     Replaces user-defined Leibniz equalities with standard equality.
 //
 //     In the clausified form, a Leibniz equality defined as:
 //         λ x. λ y. `∀ p, p x ⇒ p y
 //     results in two literals: ¬(p x) and (p y), with the universally quantified predicate p.
 //     Leo-III handles this by instantiating p with (λ x, s = x).
 //
 // Encoding:
 //     The instantiation is performed directly via application.
 //     The resulting clause can then be simplified using the encoding of (Triv):

 // Example
 symbol axiom_LEQ_example: Π (q : τ(ι ⤳ o)) , π (c ∨ ¬(q s) ∨ (q t));
 symbol proof_LEQ_example: π (c ∨ (s = t))≔
 begin
    have Substitution: π (c ∨ (¬ (s = s)) ∨ (s = t))
        {refine axiom_LEQ_example (λ x, s = x)};
    have Triv_inst: π ((c ∨ (¬ (s = s)) ∨ (s = t)) ⇒ (c ∨ (s = t)))
        {rewrite ¬=_idem; rewrite ⊥∨; rewrite ⇒_idem; refine ⊤ᵢ};
    refine Triv_inst Substitution
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
 //     with an implicitly quantified p. Leo-III handles this by instantiating p with (=).
 //
 // Encoding:
 //     Instantiation is done via application. The resulting clause simplifies the procedure introduced in (Triv):
 symbol AEQ [a : Set] x (s : τ a): π (x ∨ ¬ (s = s) ⇒ x)≔
 begin
    assume a z s;
        rewrite ¬=_idem;
        rewrite ∨⊥;
        assume h; refine h
 end;
       
 // Example 
 symbol axiom_AEQ_example: Π (p : τ(ι ⤳ ι ⤳ o)) , π ((`∀ x, p x s ⇒ q x) ∨ ¬(p s s));
 symbol proof_AEQ_example: π (`∀ x, x = s ⇒ q x)≔
 begin
    have Substitution : π ((`∀ x, (x = s) ⇒ q x) ∨ ¬ (s = s))
        {refine  axiom_AEQ_example (=)};
    have Triv_inst : π (((`∀ x, (x = s) ⇒ q x) ∨ ¬ (s = s)) ⇒ (`∀ x, x = s ⇒ q x))
        {rewrite ¬=_idem; rewrite ∨⊥; rewrite ⇒_idem; refine ⊤ᵢ};
    refine Triv_inst Substitution
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


 // ────────── (INJ)
 // Not implemented
 //
 // Description:
 //     This rule scans for instances of injective functions and proves the existence of
 //     inverse functions for them.
 //
 // Encoding:
 //     We prove the rule as a function that proves the existence of an inverse. We can then 
 //     proceed as in the verification of skolemisazion steps to proof the application
 //     of the inference rule based on the proof of the existence given by our encoding of (INJ).

symbol INJ [a b: Set] (f : τ (a ⤳ b)) : π (`∀ x, `∀ y, (¬ (f x = f y) ∨ (x = y))) → π (`∃ (f_in : τ (b ⤳ a)), `∀ x, f_in (f x) = x)≔
 begin
    assume a b f h0;
    refine ¬¬ₑ (`∃ (f_in : τ (b ⤳ a)), `∀ x, f_in (f x) = x) _;
    assume negConj;
    have H0: π (`∀ (f_in : τ (b ⤳ a)), ¬ (`∀ x0, f_in (f x0) = x0))
        {refine ¬∃ (λ (f_in : τ (b ⤳ a)), `∀ x, f_in (f x) = x) negConj};
    have H1: π (`∀ (f_in : τ (b ⤳ a)), (`∃ x0, ¬ (f_in (f x0) = x0)))
        {assume f_in;
        refine =⇒ (¬∀=∃¬ a (λ x, (f_in (f x) = x))) _;
        refine H0 f_in};
    set f_invv ≔  λ (y : τ b), ε (λ (x: τ a), f x = y);
    refine ∃ₑ (H1 f_invv) _;
    assume x h1;
    refine ∨ₑ (h0 x (f_invv (f x))) _ _
        {assume h2; 
        have H2 :  π (f x = f (f_invv (f x)))
            {symmetry;
            refine εᵢ [a] (λ (z: τ a), f z = f x) _;
            refine ∃ᵢ x _;
            reflexivity};
        refine h2 H2}
        {assume h2;
        refine h1 (eq_sym h2)};
 end;

symbol axiom_INJ_example x y: π (¬ (f x = f y) ∨ (x = y));
symbol sk4 : τ (ι ⤳ ι);
symbol sk4_def : π (sk4 = (ε (λ f_in, `∀ x1, f_in (f x1) = x1)));
 symbol proof_INJ_example x: π ((sk4 (f x)) = x) ≔
 begin
    assume x;
    rewrite sk4_def;
    refine εᵢ [ι ⤳ ι] ((λ f_in, `∀ x0, f_in (f x0) = x0)) (INJ [ι] [ι] f axiom_INJ_example) x;
 end;

 // Cases with multiple arguments are more complicated and may require permuting the arguments first:
 symbol axiom_INJ_example_2 x y z: π (¬ (f_2 x z = f_2 y z) ∨ (x = y));
 symbol sk5 : τ (ι ⤳ ι ⤳ ι);
 symbol sk5_def z : π (sk5 = (ε (λ (f_inv : τ (ι ⤳ ι ⤳ ι)), `∀ (x : τ ι), (f_inv z (f_2 x z)) = x)));
 symbol proof_INJ_example_2 x z: π ((sk5 z (f_2 x z)) = x) ≔
 begin
    have proofForPermutedArgs : Π z, π (`∃ (f_inv : τ (ι ⤳ ι ⤳ ι)), `∀ (x : τ ι), (f_inv z (f_2 x z)) = x)
        {assume z;
        set f_2'' ≔ λ x, λ y, f_2 y x;

    have changedPos' : Π (x : τ ι), Π (y : τ ι),  π (¬ (f_2'' z x = f_2'' z y) ∨ (x = y))
        {assume x y;
        simplify;
        refine axiom_INJ_example_2 x y z};

    refine ∃ₑ (INJ (f_2'' z) changedPos') _;
    assume f_inv0 h0;
    set f_inv ≔ λ (x : τ ι), f_inv0;
    refine ∃ᵢ f_inv _;
    refine h0};
    assume x z;
    rewrite sk5_def z;
    refine εᵢ [ι ⤳ ι ⤳ ι] (λ f_inv, `∀ x, f_inv z (f_2 x z) = x) (proofForPermutedArgs z) x;
 end;


// ────────── (FS)

 //  Description:
 //    Function synthesis from negative equational constraints.
 //    Leo-III scans for clauses that contain constraints of the form
 //      ¬(F s^{k,1} … s^{k,n} = t^k)   (k = 1..m),
 //    i.e., the clause “specifies” the values that F should take on the listed
 //    arguments. (FS) instanciates F by a λ-term defined via choice that satisfies
 //    all these specifications.

 //  Encoding:
 //    We instantiate the clause with the synthesized function
 //      F := λ X^1 … X^n. ε Z.\, ∧_{k=1}^m ( (∧_{j=1}^n X^j = s^{k,j}) → Z = t^k )

 // Example:
 symbol axiom_FS_example :
        Π (F : τ(ι ⤳ ι)), π ((F s = v) ∨ ¬(F s = t) ∨ ¬(F u = v));

 // For readiablility, we define the intorduced unification constraint here:
 symbol F_inst : τ (ι ⤳ ι) ≔
        λ x, ε (λ z, ((x = s) ⇒ z = t) ∧ ((x = u) ⇒ z = v));

 symbol proof_FS_example :
        π ((F_inst s = v) ∨ ¬(F_inst s = t) ∨ ¬(F_inst u = v))≔
    begin
        refine axiom_FS_example F_inst
    end;
