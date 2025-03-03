require open Stdlib.Set Stdlib.HOL Stdlib.Prop Stdlib.FOL 
Stdlib.Eq Stdlib.Impred;

// Extensionality axioms

symbol propExt x y : 
         (π x → π y) → (π y → π x) → π (x = y);
symbol funExt [T S] (f g : (τ (T ⤳ S))) : 
          π(∀(λ x, (f x) = (g x))) → π(f = g);


// Classical notions:

symbol dne x : π(¬ ¬ x) → π x;

symbol em x : π((x ∨ ¬ x))≔
begin
    assume x;
    refine dne (x ∨ ¬ x) _;
    assume h1;
    have H1: π x → π ⊥
        {assume h2;
        refine h1 (∨ᵢ₁ [x] [¬ x] h2)};
    have H2: π (¬ x) → π ⊥
        {assume h2;
        refine h1 (∨ᵢ₂ [x] [¬ x] h2)};
    refine H2 H1
end;

