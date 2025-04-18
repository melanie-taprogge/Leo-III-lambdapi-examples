require open Stdlib.Set Stdlib.Prop Stdlib.FOL Stdlib.Eq Stdlib.Nat Stdlib.Bool Stdlib.Classic
Stdlib.List Stdlib.HOL Stdlib.Impred lambdapi-examples.simpRules;

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