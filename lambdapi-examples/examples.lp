// Necessary standard library encodings
require open Stdlib.Set Stdlib.Prop Stdlib.FOL Stdlib.Epsilon Stdlib.HOL Stdlib.Eq Stdlib.Impred Stdlib.Nat Stdlib.Bool Stdlib.List Stdlib.Classic;

// Encodings derived in the scope of the Leo-III encoding effort
require open lambdapi-examples.simpRules lambdapi-examples.epCalculus lambdapi-examples.implicitTransformations lambdapi-examples.literalLevelOperations;


// Example of the encoding of a straight-froward ND proof:

constant symbol a : τ o;
symbol p : π (a ∧ a);
symbol conjecture: π a ≔ ∧ₑ₁ p;


// Example of the direct application of an inference rule encoded 
// as a function (PFE):

constant symbol f : τ (o ⤳ o);
constant symbol g : τ (o ⤳ o);

symbol step_n : π(f = g);
symbol step_m : Π x, π (f x = g x)≔
begin
    assume x;
    refine PFE f g x step_n;
end;


// Example of the application of an inference rule encoded as a 
// function (PFE) using transform:

constant symbol l : τ o;

symbol step_n' : π (f = g ∨ l);
symbol step_m' : Π x, π (f x = g x ∨ l)≔
begin
    assume x;
    refine transform ((f = g) ⸬ l ⸬ □) 0 (PFE f g x) step_n'
end;


// Example of the encoding of an inference step requiring implicit 
// transformations:

symbol step_m'' : Π x, π (l ∨ g x = f x)≔
begin
    // Step 1
    assume x; 
    // Step 3
    have PFE_app: π (f x = g x ∨ l) 
        {refine transform ((f = g) ⸬ l ⸬ □) 0 (PFE f g x) 
            step_n'};
    // Step 4
    rewrite eqSym (g x) (f x); 
    have Permutation: π (l ∨ (f x = g x))
        {refine permute (1 ⸬ 0 ⸬ □) ((f x = g x) ⸬ l ⸬ □) ⊤ᵢ 
            PFE_app};
    // Step 5
    refine Permutation
end;