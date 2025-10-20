// Necessary standard library encodings
require open Stdlib.Set Stdlib.Prop Stdlib.FOL Stdlib.Epsilon Stdlib.HOL Stdlib.Eq Stdlib.Impred Stdlib.Nat Stdlib.Bool Stdlib.List Stdlib.Classic;

// Encodings derived in the scope of the Leo-III encoding effort
require open lambdapi-examples.simpRules lambdapi-examples.epCalculus lambdapi-examples.implicitTransformations lambdapi-examples.literalLevelOperations;


// Example of the encoding of a straight-froward ND proof:

constant symbol a : τ o;
constant symbol b : τ o;
symbol p : π (a ∧ a);
symbol q : τ (ι ⤳ o);
symbol conjecture: π a ≔ ∧ₑ₁ p;


// Example of the direct application of an inference rule encoded 
// as a function (PFE):

constant symbol f : τ (o ⤳ o);
constant symbol g : τ (o ⤳ o);

symbol PFE_premise : π(f = g);
symbol PFE_example : Π x, π (f x = g x)≔
begin
    assume x;
    refine PFE f g x PFE_premise;
end;


// Example of the application of an inference rule encoded as a 
// function (PFE) using transform:

constant symbol l : τ o;

symbol PFE_premise' : π (f = g ∨ l);
symbol PFE_example' : Π x, π (f x = g x ∨ l)≔
begin
    assume x;
    refine transform ((f = g) ⸬ l ⸬ □) 0 (PFE f g x) PFE_premise'
end;

// Example of the application of simplification:

symbol Simp_premise : π ((a ∧ a) = b);
symbol Simp_example : π (a = b)≔
begin
    have SimpApp : π (((a ∧ a) = b) ⇒ (a = b))  
        {rewrite ∧_idem;
        rewrite ⇒_idem;
        refine ⊤ᵢ};
    refine SimpApp Simp_premise
end;

 symbol CNFE_Premise: π (c ∨ ¬(∀ q));
 // Declare the newly introduced skolem term and define it using the choice operator
 symbol sk1 : τ ι;
 symbol sk1_def : π (sk1 = ε (λ x, ¬ (q x)));
 symbol CNFE_Example: π (c ∨ ¬ (q sk1))≔
 begin
    have Skolemisazion : π (c ∨ ¬(∀ q) ⇒ c ∨ ¬ (q sk1))
        {rewrite CNFExist; rewrite sk1_def;
        rewrite ⇒_idem; refine ⊤ᵢ};
    refine Skolemisazion CNFE_Premise;
 end;

// Example of the application of (Triv):

symbol Triv_premise : π (¬ (a = a) ∨ b);
symbol Triv_example : π b ≔
begin
    have TrivApp : π ((¬ (a = a) ∨ b) ⇒ b)  
        {rewrite ¬=_idem; rewrite ⊥∨;
        rewrite ⇒_idem; refine ⊤ᵢ};
    refine TrivApp Triv_premise
end;

// Example of the application of (Bind):

symbol Bind_premise : Π x, π (f x ∨ ¬(x = a));
symbol Bind_example : π (f a) ≔
begin
    have Substitution :  π (f a ∨ ¬(a = a)) {refine Bind_premise a};
    have TrivApp : π ((f a ∨ ¬(a = a)) ⇒ (f a))  
        {rewrite ¬=_idem; rewrite ∨⊥;
        rewrite ⇒_idem; refine ⊤ᵢ};
    refine TrivApp Substitution
end;


// Example of the encoding of an inference step requiring implicit 
// transformations:

symbol PFE_example'' : Π x, π (l ∨ g x = f x)≔
begin
    // Step 1
    assume x; 
    // Step 3
    have PFE_app: π (f x = g x ∨ l) 
        {refine transform ((f = g) ⸬ l ⸬ □) 0 (PFE f g x) 
            PFE_premise'};
    // Step 4
    rewrite eqSym (g x) (f x); 
    have Permutation: π (l ∨ (f x = g x))
        {refine permute (1 ⸬ 0 ⸬ □) ((f x = g x) ⸬ l ⸬ □) ⊤ᵢ 
            PFE_app};
    // Step 5
    refine Permutation
end;