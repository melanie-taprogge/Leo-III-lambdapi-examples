/* 
---------------------------------------------------------------------------
This file contains the examples used throughout the (unpublished) paper 
"Formal Verification of Proofs from Automated Theorem Provers for 
Higher-Order Logic"

Note: 
Here we define a new symbol for rule applications that - in the automatically 
generated encodings of longer proofs - would each be defined as a sub-step 
in longer proofs. This is also the way we present these examples in the paper.
This difference in representation does not affect the proofs themselves but 
only defines the symbols representing the encoded steps locally. 
---------------------------------------------------------------------------
*/

// Necessary standard library encodings
require open Stdlib.Set Stdlib.Prop Stdlib.FOL Stdlib.Epsilon Stdlib.HOL Stdlib.Eq Stdlib.Impred Stdlib.Nat Stdlib.Bool Stdlib.List Stdlib.Classic;

// Encodings derived in the scope of the Leo-III encoding effort
require open lambdapi-examples.simpRules lambdapi-examples.epCalculus lambdapi-examples.implicitTransformations lambdapi-examples.Disj;


// Symbols used throughout the examples
constant symbol a : τ o;
constant symbol b : τ o;
symbol p : τ (ι ⤳ o);


// Example of the direct application of an inference rule encoded 
// as a function (PFE):

constant symbol f : τ (o ⤳ o);
constant symbol g : τ (o ⤳ o);

symbol PFE_premise : π(f = g);
symbol PFE_example : Π x, π(f x = g x)≔
begin
    assume x; 
    refine PFE f g x PFE_premise
end;


// Example of the application of an inference rule encoded as a 
// function (PFE) using the theorem transform:

constant symbol l : τ o;

symbol PFE_premise' : π (f = g ∨ l);
symbol PFE_example' : Π x, π (f x = g x ∨ l)≔
begin
    assume x;
    refine transform ((f = g) ⸬ l ⸬ □) 0 (PFE f g x) PFE_premise'
end;


// Example of the application of term simplification of Leo-III:

symbol Simp_premise : π ((a ∧ a) = b);
symbol Simp_example : π (a = b)≔
begin
    have SimpApp : π (((a ∧ a) = b) ⇒ (a = b))
        {rewrite ∧_idem; rewrite ⇒_idem; refine ⊤ᵢ};
    refine SimpApp Simp_premise
end;


// Example of a clausification step including Skolemization

symbol CNFEx_premise: π (c ∨ ¬(∀ p));
symbol sk1 ≔  ε (λ x, ¬ (p x));
symbol CNFEx_example: π (c ∨ ¬ (p sk1))≔
begin
    have Skolemization : π (c ∨ ¬(∀ p) ⇒ c ∨ ¬ (p sk1))
        {rewrite CNFExist; simplify sk1; 
         rewrite ⇒_idem; refine ⊤ᵢ};
    refine Skolemization CNFEx_premise
end;


// Example of the verification of an application of (Bind):

symbol Bind_premise : Π x, π (f x ∨ ¬(x = a));
symbol Bind_example : π (f a) ≔
begin
    have Substitution : π (f a ∨ ¬(a = a))
        {refine Bind_premise a};
    have RemoveConstraint : π ((f a ∨ ¬(a = a)) ⇒ (f a))  
        {rewrite ¬=_idem; rewrite ∨⊥; rewrite ⇒_idem; refine ⊤ᵢ};
    refine RemoveConstraint Substitution
end;


// Example of the encoding of an inference step requiring implicit 
// transformations:

symbol PFE_example'' : Π x, π (l ∨ g x = f x)≔
begin
    assume x;  // Step 1
    have PFE_app: π (f x = g x ∨ l)  // Step 3
        {refine transform ((f = g) ⸬ l ⸬ □) 0 (PFE f g x) PFE_premise'};
        rewrite eqSym (g x) (f x);  // Step 4
    have Permutation: π (l ∨ (f x = g x))
        {refine permute (1 ⸬ 0 ⸬ □) ((f x = g x) ⸬ l ⸬ □) ⊤ᵢ PFE_app};
    refine Permutation // Step 5
end;