/***************************************************************************
This file provides an axiom and various theorems for propositional equality.        
The theorems are grouped into sections by theme:  
- Symmetry and polarity  
- Various Simplifications                              
****************************************************************************/

require open Stdlib.Set Stdlib.Prop Stdlib.FOL Stdlib.Eq Stdlib.Impred Stdlib.Classic Stdlib.HOL Stdlib.List lambdapi-examples.userDefinedTacticsPrelim;

symbol propExt x y : (π x → π y) → (π y → π x) → π (x = y);

symbol funExt [a b] (f g : τ (a ⤳ b)) : π(`∀ x, f x = g x) → π(f = g);


/******************************************************************************
 *  Commutativity, symmetry and polarity                                                     
 ******************************************************************************/

 opaque symbol ∨_com x y:
 π ((x ∨ y) = (y ∨ x)) ≔
begin
  assume x y;
  refine propExt (x ∨ y) (y ∨ x) _ _
    {assume h;
    refine ∨ₑ h _ _
      {assume h1; refine ∨ᵢ₂ h1}
      {assume h2; refine ∨ᵢ₁ h2}}
    {assume h;
    refine ∨ₑ h _ _
      {assume h1; refine ∨ᵢ₂ h1}
      {assume h2; refine ∨ᵢ₁ h2}}
end;

opaque symbol ∧_com x y:
 π ((x ∧ y) = (y ∧ x)) ≔
begin
  assume x y;
  refine propExt (x ∧ y) (y ∧ x) _ _
    {assume h; refine ∧ᵢ (∧ₑ₂ h) (∧ₑ₁ h)}
    {assume h; refine ∧ᵢ (∧ₑ₂ h) (∧ₑ₁ h)}
end;

opaque symbol ⇔_com x y:
 π ((x ⇔ y) = (y ⇔ x)) ≔
begin
  assume x y;
  refine propExt (x ⇔ y) (y ⇔ x) _ _
    {assume h; refine ∧ᵢ (∧ₑ₂ h) (∧ₑ₁ h)}
    {assume h; refine ∧ᵢ (∧ₑ₂ h) (∧ₑ₁ h)}
end;

opaque symbol =_sym [T] (x y : τ T) : 
 π((x = y) = (y = x))≔
begin
  assume T x y;
  have H1: π(x = y) → π(y = x)
    {assume h; symmetry; refine h};
  have H2: π(y = x) → π(x = y)
    {assume h; symmetry;refine h};
  refine propExt (x = y) (y = x) H1 H2
end;

opaque symbol polarity_switch x y :
π ((¬ x = ¬ y) = (x = y)) ≔
begin
  assume x y;
  refine propExt (¬ x = ¬ y) (x = y) _ _
    {assume h1;
    have H1: π(¬ y = ¬ x)
      {symmetry; refine h1};
    refine propExt x y _ _
      {assume h2;
        have H2: π(¬ ¬ x)
          {assume h3; refine h3 h2};
        refine (¬¬ₑ y) (ind_eq H1 (λ x, ¬ x) H2)}
      {assume h2;
        have H2: π(¬ (¬ y))
          {assume h3; refine h3 h2};
        refine (¬¬ₑ x) (ind_eq h1 (λ x, ¬ x) H2)}}
    {assume h1;
    have H1: π(y = x)
      {symmetry; refine h1};
    refine propExt (¬ x) (¬ y) _ _
      {assume h2; refine ind_eq H1 (λ x, ¬ x) h2}
      {assume h2; refine ind_eq h1 (λ x, ¬ x) h2}}
end;


/******************************************************************************
 *  Simplifications          
 ******************************************************************************/

// Idempotence and Contradiction for ∧ and ∨

opaque symbol ∨_idem x :
  π ((x ∨ x) = x) ≔
begin
  assume x;
  refine propExt (x ∨ x) x _ _
    {assume h1;
     refine ∨ₑ h1 _ _
       {assume h2; refine h2}
       {assume h2; refine h2}}
    {assume h2; refine ∨ᵢ₁ h2}
end;

opaque symbol ∧_idem x :
  π ((x ∧ x) = x) ≔
begin
  assume x;
  refine propExt (x ∧ x) x _ _
    {assume h1; refine ∧ₑ₁ h1}
    {assume h1; refine ∧ᵢ h1 h1}
end;

opaque symbol ∧_contra_l x :
  π ((¬ x ∧ x) = ⊥) ≔
begin
  assume x;
  refine propExt (¬ x ∧ x) ⊥ _ _
    {assume h1;
     refine (∧ₑ₁ h1) (∧ₑ₂ h1)}
     {assume h1; refine ⊥ₑ h1}
end;

opaque symbol ∧_contra_r x :
  π ((x ∧ ¬ x ) = ⊥) ≔
begin
  assume x; rewrite ∧_com; refine ∧_contra_l x;
end;


// Disjunction/Conjunction with ⊤ / ⊥      

opaque symbol ∨⊤ x :
  π ((x ∨ ⊤) = ⊤) ≔
begin
  assume x;
  refine propExt (x ∨ ⊤) ⊤ _ _
    {assume h1; refine ⊤ᵢ}
    {assume h2; refine ∨ᵢ₂ h2}
end;

opaque symbol ⊤∨ x :
  π ((⊤ ∨ x) = ⊤) ≔
begin
  assume x; rewrite ∨_com; refine ∨⊤ x
end;

opaque symbol ∧⊤ x :
  π ((x ∧ ⊤) = x) ≔
begin
  assume x;
  refine propExt (x ∧ ⊤) x _ _
    {assume h1; refine ∧ₑ₁ h1}
    {assume h1; refine ∧ᵢ h1 ⊤ᵢ}
end;

opaque symbol ⊤∧ x :
  π ((⊤ ∧ x) = x) ≔
begin
  assume x; rewrite ∧_com; refine ∧⊤ x
end;

opaque symbol ∨⊥ x :
  π ((x ∨ ⊥) = x) ≔
begin
  assume x;
  refine propExt (x ∨ ⊥) x _ _
    {assume h1;
     refine ∨ₑ h1 _ _
       {assume h2; refine h2}
       {assume h2; refine ⊥ₑ h2}}
    {assume h1; refine ∨ᵢ₁ h1}
end;

opaque symbol ⊥∨ x :
  π ((⊥ ∨ x) = x) ≔
begin
  assume x; rewrite ∨_com; refine ∨⊥ x
end;

opaque symbol ∧⊥ x :
  π ((x ∧ ⊥) = ⊥) ≔
begin
  assume x;
  refine propExt (x ∧ ⊥) ⊥ _ _
    {assume h1; refine ∧ₑ₂ h1}
    {assume h1;
     type ⊥ₑ h1;
     refine ∧ᵢ (⊥ₑ h1) h1}
end;

opaque symbol ⊥∧ x :
  π ((⊥ ∧ x) = ⊥) ≔
begin
  assume x; rewrite ∧_com; refine ∧⊥ x
end;


// Negation of ⊤ and ⊥  

opaque symbol ¬⊥ :
  π (¬ ⊥ = ⊤) ≔
begin
  refine propExt (¬ ⊥) ⊤ _ _
    {assume h1; refine ⊤ᵢ}
    {assume h1 h2; refine h2}
end;

opaque symbol ¬⊤ :
  π (¬ ⊤ = ⊥) ≔
begin
  refine propExt (¬ ⊤) ⊥ _ _
    {assume h1; refine h1 ⊤ᵢ}
    {assume h1; refine ⊥ₑ h1}
end;


// Simplifications on Equalities 

opaque symbol =_idem (t : Set) (x : τ t) : 
  π ((x = x) = ⊤) ≔
begin
  assume t x;
  refine propExt (x = x) ⊤ _ _
    {assume h1; refine ⊤ᵢ}
    {assume h1; refine eq_refl x}
end;

opaque symbol ¬=_idem (t : Set) (x : τ t) :
  π (¬ (x = x) = ⊥) ≔
begin
  assume t x;
  refine propExt (¬ (x = x)) ⊥ _ _
    {assume h1;
     have xx_ineq: π(x = x) → π ⊥
       {assume h2; refine h1 h2};
     refine xx_ineq (eq_refl x)}
    {assume h1; refine ⊥ₑ h1}
end;

opaque symbol =⊤ x :
  π ((x = ⊤) = x) ≔
begin
  assume x;
  refine propExt (x = ⊤) x _ _
    {assume h1;
     refine (ind_eq h1 (λ z, z)) ⊤ᵢ}
    {assume h1;
     refine propExt x ⊤ _ _
        {assume h2; refine ⊤ᵢ}
        {assume h2; refine h1}}
end;

opaque symbol ⊤= x :
  π ((⊤ = x) = x) ≔
begin
  assume x; rewrite .[x in x = _] (=_sym [o]); refine =⊤ x
end;

opaque symbol ¬=⊤ x :
  π (¬(x = ⊤) = ¬ x) ≔
begin
  assume x;
  refine propExt (¬(x = ⊤)) (¬ x) _ _
    {assume h1 h2;
     refine h1 (propExt x ⊤ _ _)
        {assume h3; refine ⊤ᵢ}
        {assume h3; refine h2}}
    {assume h1 h2;
     have x_true: π x
       {refine ind_eq h2 (λ z, z) ⊤ᵢ};
     refine h1 x_true}
end;

opaque symbol ¬⊤= x :
  π (¬(⊤ = x) = ¬ x) ≔
begin
  assume x; rewrite .[x in (¬ x) = _] (=_sym [o]); refine ¬=⊤ x
end;

opaque symbol =⊥ x :
  π ((x = ⊥) = ¬ x) ≔
begin
  assume x;
  refine propExt (x = ⊥) (¬ x) _ _
  {assume h1 h2;
   refine (ind_eq (eq_sym h1) (λ z, z)) h2}
  {assume h2;
   refine propExt x ⊥ _ _
   {assume h3; refine h2 h3}
   {assume h3; refine ⊥ₑ h3}}
end;

opaque symbol ⊥= x :
  π ((⊥ = x) = ¬ x) ≔
begin
  assume x; rewrite .[x in x = _] (=_sym [o]); refine  =⊥ x
end;

opaque symbol  ¬=⊥ x :
  π (¬ (x = ⊥) = x) ≔
begin
  assume x;
  refine propExt (¬(x = ⊥)) x _ _
  {assume h1;
   refine ∨ₑ (em x) _ _
   {assume h2; refine h2}
   {assume h2;
    have eq_x_⊥: π (x = ⊥)
    {refine propExt x ⊥ _ _
     {assume h3; refine h2 h3}
     {assume h3; refine ⊥ₑ h3}};
    have contra: π ⊥
    {refine h1 eq_x_⊥};
    refine ⊥ₑ contra}}
  {assume h2 eq_x_⊥;
   refine (ind_eq (eq_sym eq_x_⊥) (λ z, z)) h2}
end;

opaque symbol ¬⊥= x :
  π (¬ (⊥ = x) = x) ≔
begin
  assume x; rewrite .[x in (¬ x) = _] (=_sym [o]); refine ¬=⊥ x;
end;


// Simplifications on Equalities with negations

opaque symbol neg=⊤ x :
  π ((¬ x = ⊤) = ¬ x) ≔
begin
  assume x;
  symmetry;
  refine propExt (¬ x) (¬ x = ⊤) _ _
    {assume h1;
     refine propExt (¬ x) ⊤ _ _
        {assume h2; refine ⊤ᵢ}
        {assume h2; refine h1}}
    {assume h1;
     have H1: π(¬ x = ⊤) → π(¬ x)
       {assume h2;
        refine (ind_eq h2 (λ z, z)) ⊤ᵢ};
     refine H1 h1}
end;

opaque symbol ⊤=neg x :
π ((⊤ = ¬ x) = ¬ x) ≔
begin
  assume x; rewrite .[x in x = _] (=_sym [o]); refine neg=⊤ x
end;

opaque symbol ¬neg=⊤ x :
  π (¬(¬ x = ⊤) = x) ≔
begin
  assume x;
  symmetry;
  refine propExt x (¬ (¬ x = ⊤)) _ _
    {assume h1 h2;
     refine ((ind_eq h2 (λ z, z)) ⊤ᵢ) h1}
    {assume h1;
     refine ∨ₑ (em x) _ _
        {assume h2; refine h2}
        {assume h2;
         have H1: π(¬ x = ⊤)
          {refine propExt (¬ x) ⊤ _ _
            {assume h3; refine ⊤ᵢ}
            {assume h3; refine h2}};
         refine ⊥ₑ (h1 H1)}}
end;

opaque symbol ¬⊤neg= x :
  π (¬(⊤ = ¬ x) = x) ≔
begin
  assume x; rewrite .[x in ¬ x = _] (=_sym [o]); refine ¬neg=⊤ x
end;

opaque symbol neg=⊥ x :
  π ((¬ x = ⊥) = x) ≔
begin
  assume x;
  refine propExt (¬ x = ⊥) x _ _
    {assume h1;
    refine ¬¬ₑ x (ind_eq h1 (λ y, ¬ y) (λ h: π ⊥, h))}
    {assume h1;
     refine propExt (¬ x) ⊥ _ _
       {assume h2; refine h2 h1}
       {assume h2; refine ⊥ₑ h2}}
end;

opaque symbol ⊥=neg x :
  π ((⊥ = ¬ x ) = x) ≔
begin
  assume x; rewrite .[x in x = _] (=_sym [o]); refine neg=⊥ x
end;

opaque symbol ¬neg=⊥ x :
  π (¬(¬ x = ⊥) = ¬ x) ≔
begin
  assume x;
  refine ind_eq (polarity_switch (¬ x = ⊥) x) (λ z, z) (neg=⊥ x);
end;

opaque symbol ¬⊥=neg x :
  π (¬(⊥ = ¬ x) = ¬ x) ≔
begin
  assume x; rewrite .[x in ¬ x = _] (=_sym [o]); refine ¬neg=⊥ x
end;


// Simplifications on Implication

opaque symbol ⇒_idem x :
  π ((x ⇒ x) = ⊤) ≔
begin
  assume x;
  refine propExt (x ⇒ x) ⊤ _ _
  {assume h1; refine ⊤ᵢ}
  {assume h2 y; refine y}
end;

opaque symbol ⊤⇒ x :
  π ((⊤ ⇒ x) = x) ≔
begin
  assume x;
  refine propExt (⊤ ⇒ x) x _ _
  {assume h1; refine h1 ⊤ᵢ}
  {assume h2 y; refine h2}
end;

opaque symbol ⇒⊤ x :
  π ((x ⇒ ⊤) = ⊤) ≔
begin
  assume x;
  refine propExt (x ⇒ ⊤) ⊤ _ _
  {assume h1; refine ⊤ᵢ}
  {assume h2 y; refine ⊤ᵢ}
end;

opaque symbol ⊥⇒ x :
  π ((⊥ ⇒ x) = ⊤) ≔
begin
  assume x;
  refine propExt (⊥ ⇒ x) ⊤ _ _
  {assume h1; refine ⊤ᵢ}
  {assume h2 h3; refine ⊥ₑ h3}
end;

opaque symbol ⇒⊥ x :
  π ((x ⇒ ⊥) = ¬ x) ≔
begin
  assume x;
  refine propExt (x ⇒ ⊥) (¬ x) _ _
  {assume h1 h2; refine h1 h2}
  {assume h2 y; refine h2 y}
end;


// Simplifications on Bi-Implication

opaque symbol ⇔_idem x :
  π ((x ⇔ x) = ⊤) ≔
begin
  assume x;
  refine propExt (x ⇔ x) ⊤ _ _
  {assume h1; refine ⊤ᵢ}
  {assume h2;
   refine ∧ᵢ _ _
   {assume h3; refine h3}
   {assume h3; refine h3}}
end;

opaque symbol ⇔⊤ x :
  π ((x ⇔ ⊤) = x) ≔
begin
  assume x;
  refine propExt (x ⇔ ⊤) x _ _
  {assume h1;
   refine ∧ₑ₂ h1 ⊤ᵢ}
  {assume h2;
   refine ∧ᵢ _ _
   {assume h3; refine ⊤ᵢ} 
   {assume h3; refine h2}}
end;

opaque symbol ⊤⇔ x :
  π ((⊤ ⇔ x) = x) ≔
begin
  assume x; rewrite ⇔_com; refine ⇔⊤ x;
end;

opaque symbol ⇔⊥ x :
  π ((x ⇔ ⊥) = ¬ x) ≔
begin
  assume x;
  refine propExt (x ⇔ ⊥) (¬ x) _ _
  {assume h1;
   refine ∧ₑ₁ h1}
  {assume h2;
   refine ∧ᵢ _ _
   {assume h3; refine h2 h3}
   {assume h3; refine ⊥ₑ h3}}
end;

opaque symbol ⊥⇔ x :
  π ((⊥ ⇔ x) = ¬ x) ≔
begin
  assume x; rewrite ⇔_com; refine ⇔⊥ x;
end;


// Simplifications on Quantifiers

opaque symbol ∀_const (t : Set) (p : τ o) : π ((`∀ (_ : τ t), p) = p)≔
begin
    assume t p;
    refine propExt (`∀ x, p) p _ _
        {assume h; refine h (el t)}
        {assume h a; refine h}
end;

opaque symbol ∃_const (t : Set) (p : τ o) : π ((`∃ (_ : τ t), p) = p)≔
begin
    assume t p;
    refine propExt (`∃ x, p) p _ _
        {assume h; 
         have p_holds : Π (x : τ t), π p → π p
          {assume x h2; refine h2};
         refine ∃ₑ [t] [λ y, p] h p_holds}
        {assume h; 
         have p_holds : π ((λ x , p) (el t))
          {refine h};
         refine ∃ᵢ [t] [λ y, p] (el t) p_holds}
end;


// Simplifications reflecting Classical Principles

opaque symbol em_eq_l x :
  π ((¬ x ∨ x) = ⊤) ≔
begin
  assume x;
  refine propExt (¬ x ∨ x) ⊤ _ _
    {assume h1; refine ⊤ᵢ}
    {assume h1;
     have em_sym: π(¬ x ∨ x)
       {refine ∨ₑ (em x) _ _
         {assume h3; refine ∨ᵢ₂ h3}
         {assume h3; refine ∨ᵢ₁ h3}};
     refine em_sym}
end;

opaque symbol em_eq_r x :
  π ((x ∨ ¬ x) = ⊤) ≔
begin
  assume x; rewrite ∨_com; refine em_eq_l x;
end;

opaque symbol ¬¬ₑ_eq x :
  π (¬ ¬ x = x) ≔
begin
  assume x;
  refine propExt (¬ ¬ x) x _ _
    {assume h1; refine ¬¬ₑ x h1}
    {assume h1 h2; refine h2 h1}
end;


/******************************************************************************
  *  Definition of combined Simplification tactic        
  ******************************************************************************/
 
  symbol applyAny : 𝕃 tactic → Tactic;
  rule applyAny ($t0 ⸬ $tl) ↪ $t0 #orelse (applyAny $tl)
  with applyAny □ ↪ #fail;
  
  symbol listOfAllSimpRules ≔ ((#rewrite "" "" ∨_idem) ⸬ (#rewrite "" "" em_eq_l) ⸬ (#rewrite "" "" em_eq_r) ⸬ (#rewrite "" "" ∨⊤) ⸬ 
      (#rewrite "" "" ⊤∨) ⸬ (#rewrite "" "" ∨⊥) ⸬ (#rewrite "" "" ⊥∨) ⸬ (#rewrite "" "" ∧_idem) ⸬ (#rewrite "" "" ∧_contra_r) ⸬ (#rewrite "" "" ∧_contra_l) ⸬ 
      (#rewrite "" "" ∧⊤) ⸬ (#rewrite "" "" ⊤∧) ⸬ (#rewrite "" "" ∧⊥) ⸬ (#rewrite "" "" ⊥∧) ⸬ (#rewrite "" "" ⇒⊤) ⸬ (#rewrite "" "" ⊥⇒) ⸬ (#rewrite "" "" ⊤⇒) ⸬ 
      (#rewrite "" "" ⇒⊥) ⸬ (#rewrite "" "" ⇒_idem) ⸬ (#rewrite "" "" ⇔⊤) ⸬ (#rewrite "" "" ⊤⇔) ⸬ (#rewrite "" "" ⊥⇔) ⸬ (#rewrite "" "" ⇔⊥) ⸬ 
      (#rewrite "" "" ⇔_idem) ⸬ (#rewrite "" "" ¬⊤) ⸬ (#rewrite "" "" ¬⊥) ⸬ (#rewrite "" "" ¬¬ₑ_eq) ⸬ (#rewrite "" "" =⊤) ⸬ (#rewrite "" "" ⊤=) ⸬ 
      (#rewrite "" "" =⊥) ⸬ (#rewrite "" "" ⊥=) ⸬ (#rewrite "" "" =_idem) ⸬ (#rewrite "" "" ¬=⊥) ⸬ (#rewrite "" "" ¬⊥=) ⸬ (#rewrite "" "" ¬=⊤) ⸬ 
      (#rewrite "" "" ¬⊤=) ⸬ (#rewrite "" "" ¬=_idem) ⸬ (#rewrite "" "" ∀_const) ⸬ (#rewrite "" "" ∃_const) ⸬ (#rewrite "" "" polarity_switch) ⸬ (#refine "⊤ᵢ") ⸬ □);
  
symbol applyAllSimplifications ≔ #repeat (applyAny listOfAllSimpRules);