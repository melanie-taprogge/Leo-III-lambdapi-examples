require open Stdlib.Set Stdlib.Prop Stdlib.Classic Stdlib.FOL Stdlib.HOL Stdlib.Eq Stdlib.Impred Stdlib.FunExt lambdapi-examples.simpRules Stdlib.Nat Stdlib.Bool Stdlib.List Stdlib.Epsilon lambdapi-examples.metaTheorems;

/******************************************************************************
 *  De Morgan's Laws on ∧ and ∨
 ******************************************************************************/

 symbol deMorgan_∧ x y : 
 π (¬(x ∧ y) = (¬ x ∨ ¬ y))≔
begin
 assume x y;
 refine propExt (¬(x ∧ y)) (¬ x ∨ ¬ y) _ _
 {assume h;
     refine ∨ₑ (em x) _ _
     {assume hx; refine ∨ᵢ₂ (λ hy, h (∧ᵢ hx hy))}
     {assume hx; refine ∨ᵢ₁ hx}}
 {assume h hxy; 
     refine ∨ₑ h _ _
     {assume hnx; refine hnx (∧ₑ₁ hxy)}
     {assume hny; refine hny (∧ₑ₂ hxy)}}
end;

symbol deMorgan_∨ x y : 
 π (¬(x ∨ y) = (¬ x ∧ ¬ y))≔
begin
 assume x y;
 refine propExt (¬(x ∨ y)) (¬ x ∧ ¬ y) _ _
 {assume h; refine ∧ᵢ _ _ 
     {assume hx; refine h (∨ᵢ₁ hx)} 
     {assume hy; refine h (∨ᵢ₂ hy)}}
 {assume h hxy;
     refine ∨ₑ hxy _ _
     {assume hx; refine (∧ₑ₁ h) hx}
     {assume hy; refine (∧ₑ₂ h) hy}}
end;

/******************************************************************************
*  Implication Equivalences
******************************************************************************/

symbol ⇒=∨ x y :  
 π ((x ⇒ y) = (¬ x ∨ y))≔
begin
 assume x y;
 refine propExt (x ⇒ y) (¬ x ∨ y) _ _
 {assume h;
     refine ∨ₑ (em x) _ _
     {assume hx; refine ∨ᵢ₂ (h hx)}
     {assume hnx; refine ∨ᵢ₁ hnx}}
 {assume h hx;
     refine ∨ₑ h _ _
     {assume hnx; refine ⊥ₑ (hnx hx)}
     {assume hy; refine hy}}
end;

symbol ¬⇒=∧¬ x y : 
 π (¬(x ⇒ y) = (x ∧ ¬ y))≔
begin
 assume x y;
 refine propExt (¬(x ⇒ y)) (x ∧ ¬ y) _ _
 {assume h;
     refine ∧ᵢ _ _
     {refine ∨ₑ (em x) _ _
         {assume hx; refine hx}
         {assume hnx; refine ⊥ₑ (h (λ z, ⊥ₑ (hnx z)))}}
     {assume hy; refine h (λ _, hy)}}
 {assume h himp;
     refine (∧ₑ₂ h) (himp (∧ₑ₁ h))}
end;

/******************************************************************************
*  Distributivity
******************************************************************************/

// ... to mimic splitting in leo-III

symbol ∧∨_dist_l x y z : 
 π (((x ∧ y) ∨ z) = ((x ∨ z) ∧ (y ∨ z)))≔
begin
 assume x y z;
 refine propExt ((x ∧ y) ∨ z) ((x ∨ z) ∧ (y ∨ z)) _ _
 {assume h;
     refine ∧ᵢ _ _
     {refine ∨ₑ h _ _
         {assume hxy; refine ∨ᵢ₁ (∧ₑ₁ hxy)}
         {assume hz; refine ∨ᵢ₂ hz}}
     {refine ∨ₑ h _ _
         {assume hxy; refine ∨ᵢ₁ (∧ₑ₂ hxy)}
         {assume hz; refine ∨ᵢ₂ hz}}}
 {assume h;
     refine ∨ₑ (em z) _ _
     {assume hz; refine ∨ᵢ₂ hz}
     {assume hnz;
         have hx : π x 
             {refine ∨ₑ (∧ₑ₁ h) _ _
                 {assume hx; refine hx}
                 {assume hz; refine ⊥ₑ (hnz hz)}};
         have hy : π y 
             {refine ∨ₑ (∧ₑ₂ h) _ _
                 {assume hy; refine hy}
                 {assume hz; refine ⊥ₑ (hnz hz)}};
         refine ∨ᵢ₁ (∧ᵢ hx hy)}}
end;

symbol ∧∨_dist_r x y z : 
 π ((z ∨ (x ∧ y)) = ((z ∨ x) ∧ (z ∨ y)))≔
 begin
     assume x y z;
     rewrite ∨_com;
     rewrite ∧∨_dist_l;
     rewrite ∨_com z x;
     rewrite ∨_com z y;
     reflexivity
 end;

/******************************************************************************
*  Associativity of ∧
******************************************************************************/

symbol ∧_assoc x y z : 
 π (((x ∧ y) ∧ z) = (x ∧ (y ∧ z)))≔
begin
 assume x y z;
 refine propExt ((x ∧ y) ∧ z) (x ∧ (y ∧ z)) _ _
 {assume h;
 refine ∧ᵢ (∧ₑ₁ (∧ₑ₁ h)) (∧ᵢ (∧ₑ₂ (∧ₑ₁ h)) (∧ₑ₂ h))}
 {assume h;
 refine ∧ᵢ (∧ᵢ (∧ₑ₁ h) (∧ₑ₁ (∧ₑ₂ h))) (∧ₑ₂ (∧ₑ₂ h))}
end;

/******************************************************************************
 *  Classical Quantifier De Morgan
 ******************************************************************************/

 opaque symbol ¬∀=∃¬ (t : Set) (p : τ (t ⤳ o)) : 
 π (¬(∀ p) = (`∃ (x : τ t), ¬ (p x)))≔
begin
 assume t p;
 refine propExt (¬ (∀ p)) (`∃ x, ¬ (p x)) _ _
 {assume h;
     refine ∨ₑ (em (`∃ x, ¬ p x)) _ _
     {assume he; refine he}
     {assume hne;
         have forall_p : Π x : τ t, π (p x)
             {assume a; refine ¬¬ₑ (p a) (λ hp, hne (∃ᵢ [t] [λ y, ¬ p y] a hp))};
         refine ⊥ₑ (h (λ a, forall_p a))}}
 {assume h h2;
     refine ∃ₑ [t] [λ y, ¬ p y] h (λ a hna, hna (h2 a))}
end;

opaque symbol ¬∃=∀¬ (t : Set) (p : τ (t ⤳ o)) : 
 π (¬(∃ p) = (`∀ (x : τ t), ¬ p x))≔     
begin
 assume t p;
 refine propExt (¬ (∃ p)) (`∀ x, ¬ p x) _ _
 {assume h a ha; refine h (∃ᵢ [t] [p] a ha)}
 {assume h1 h2; refine ∃ₑ [t] [p] h2 (λ a ha, (h1 a) ha)}
end;


/******************************************************************************
*  Skolemisazion
******************************************************************************/

opaque symbol εᵢ_rev :  Π [a: Set], Π p: (τ a → Prop),  
 π (p (ε p)) → π (∃ p)≔
begin
 assume a p h;
 refine ∃ᵢ [a] [p] (ε p) h
end;

opaque symbol ∃_skolem (a: Set) (p: τ a → Prop) :  
 π ((∃ p) = (p (ε p)))≔
begin
 assume a p;
 refine propExt (∃ p) (p (ε p)) (εᵢ [a] p) (εᵢ_rev [a] p)
end;
