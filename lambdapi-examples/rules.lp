require open Stdlib.Set Stdlib.Prop Stdlib.FOL Stdlib.Eq Stdlib.Nat Stdlib.Bool 
Stdlib.List Stdlib.HOL Stdlib.Impred lambdapi-examples.extt;

///////////////////////////////////////////////////////////////////////////////////////
////////////////////////////// CALCULUS RULES /////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////////////

////////// Extensionality  

opaque symbol PFE [T] [S] (f g : τ (S ⤳ T)) (x : τ S): 
      π (f = g) → π (f x = g x) ≔
begin
	assume T S f g x h;
    refine ind_eq h (λ y, y x = g x) (eq_refl [T] (g x))
end;

opaque symbol PBE_r x y: π(x = y) → π(x ∨ ¬ y)≔
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


////////// Equal Factoring

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


///////////////////////////////////////////////////////////////////////////////////////
////////////////////////////// SIMPLIFICATION RULES /////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////////////

opaque symbol ∨⊥ x: (π (x = (x ∨ ⊥)))≔
begin
    assume x;
    refine propExt x (x ∨ ⊥) _ _ 
        {assume h1;
        refine ∨ᵢ₁ h1}
        {assume h1;
        refine ∨ₑ h1 _ _
            {assume h2;
            refine h2}
            {assume h2;
            refine ⊥ₑ h2}}
end;

opaque symbol ¬⊤ : (π (⊥ = (¬ ⊤)))≔
begin
    refine propExt ⊥ (¬ ⊤) _ _ 
        {assume h1;
        refine ⊥ₑ h1}
        {assume h1;
        refine h1 ⊤ᵢ}
end;

opaque symbol ¬eqxx (T : Set) (x : τ T): (π (⊥ = ¬ (x = x)))≔
begin
    assume T x;
    refine propExt ⊥ (¬ (x = x)) _ _ 
        {assume h1;
        refine ⊥ₑ h1}
        {assume h1;
        have H1: π (x = x) → π ⊥
            {assume h2;
            refine h1 h2};
        refine H1 (eq_refl [T] x)}
end;

opaque symbol ¬¬ₑ_eq x: (π (x = ¬ ¬ x))≔
begin
    assume x;
    refine propExt x (¬ ¬ x) _ _ 
        {assume h1 h2;
        refine h2 h1}
        {assume h1;
        refine dne x h1}
end;



///////////////////////////////////////////////////////////////////////////////////////
///////////////////////// IMPLICIT TRANSFORMATIONS ////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////////////

// Switching order within equality literals:

opaque symbol eqSym [T] (x y : τ T) : π((x = y) = (y = x))≔
begin
    assume T x y;
    have H1: π(x = y) → π(y = x)
        {assume h;
        symmetry;
        refine h};
    have H2: π(y = x) → π(x = y)
        {assume h;
        symmetry;
        refine h};
    refine propExt (x = y) (y = x) H1 H2
end;


// Conversions between notations:

opaque symbol posPropNegEq x: π (x = ¬ (¬ x = ⊤))≔
begin
    assume x;
    refine propExt x (¬ (¬ x = ⊤)) _ _
    {assume h1 h2;
    refine ((ind_eq h2 (λ z, z)) ⊤ᵢ) h1}
    {assume h1;
        refine ∨ₑ [x] [¬ x] [x] (em x) _ _
            {assume h2;
            refine h2}
            {assume h2;
            have H1: π((¬ x) = ⊤)
                {refine propExt (¬ x) ⊤ _ _
                    {assume h3;
                    refine ⊤ᵢ}
                    {assume h3;
                    refine h2}};
            refine ⊥ₑ (h1 H1)}}
end;

opaque symbol negEqPosProp x: π (¬ (¬ x = ⊤) = x)≔
begin
    assume x;
    symmetry;
    refine propExt x (¬ (¬ x = ⊤)) _ _
    {assume h1 h2;
    refine ((ind_eq h2 (λ z, z)) ⊤ᵢ) h1}
    {assume h1;
        refine ∨ₑ (em x) _ _ 
            {assume h2;
            refine h2}
            {assume h2;
            have H1: π((¬ x) = ⊤)
                {refine propExt (¬ x) ⊤ _ _
                    {assume h3;
                    refine ⊤ᵢ}
                    {assume h3;
                    refine h2}};
            refine ⊥ₑ (h1 H1)}}
end;

opaque symbol negEqNegProp x: π ((¬ (x = ⊤)) = ¬ x)≔
begin
    assume x;
    symmetry;
    refine propExt (¬ x) (¬ (x = ⊤)) _ _
        {assume h1 h2;
        refine h1 (ind_eq h2 (λ z, z) ⊤ᵢ)}
        {assume h1 h2;
        have H1: π(x = ⊤)
            {refine propExt x ⊤ _ _
                {assume h3;
                refine ⊤ᵢ}
                {assume h3;
                refine h2}};
        refine h1 H1}
end;

opaque symbol negPropNegEq x: π (¬ x = ¬ (x = ⊤))≔
begin
    assume x;
    refine propExt (¬ x) (¬ (x = ⊤)) _ _
        {assume h1 h2;
        refine h1 (ind_eq h2 (λ z, z) ⊤ᵢ)}
        {assume h1 h2;
        have H1: π(x = ⊤)
            {refine propExt x ⊤ _ _
                {assume h3;
                refine ⊤ᵢ}
                {assume h3;
                refine h2}};
        refine h1 H1}
end;

opaque symbol posEqNegProp x: π ((¬ x = ⊤) = ¬ x)≔
begin
    assume x;
    symmetry;
    refine propExt (¬ x) (¬ x = ⊤) _ _
        {assume h1;
        refine propExt (¬ x) ⊤ _ _ 
            {assume h2;
            refine ⊤ᵢ}
            {assume h2;
            refine h1}}
        {assume h1;
        have H1: π((¬ x) = ⊤) → π(¬ x)
            {assume h2;
            refine (ind_eq  h2 (λ z, z)) ⊤ᵢ};
        refine H1 h1}
end;

opaque symbol posEqPosProp x: π ((x = ⊤) = x)≔
begin
    assume x;
    symmetry;
    refine propExt x (x = ⊤) _ _
        {assume h1;
        refine propExt x ⊤ _ _ 
            {assume h2;
            refine ⊤ᵢ}
            {assume h2;
            refine h1}}
        {assume h2;
        refine (ind_eq h2 (λ z, z)) ⊤ᵢ}
end;

opaque symbol negPropPosEq x: π (¬ x = (¬ x = ⊤))≔
begin
    assume x;
    refine propExt (¬ x) (¬ x = ⊤) _ _
        {assume h1;
        refine propExt (¬ x) ⊤ _ _ 
            {assume h2;
            refine ⊤ᵢ}
            {assume h2;
            refine h1}}
        {assume h1;
        have H1: π(¬ x = ⊤) → π(¬ x)
            {assume h2;
            refine (ind_eq h2 (λ z, z)) ⊤ᵢ};
        refine H1 h1}
end;

opaque symbol botNegProp x: π ((⊥ = x) = ¬ x)≔ 
begin
    assume x;
    refine propExt (⊥ = x) (¬ x) _ _
        {assume h1;
        have H1 : π x → π x
            {assume h2;
            refine h2};
        refine ind_eq h1 (λ z, x ⇒ z) H1}
        {assume h1;
        refine propExt ⊥ x _ _
            {assume h2;
            refine ⊥ₑ h2}
            {assume h2;
            refine h1 h2}}
end;