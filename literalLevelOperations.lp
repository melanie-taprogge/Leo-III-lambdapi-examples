require open Stdlib.Set Stdlib.Prop Stdlib.FOL Stdlib.Eq Stdlib.Nat 
Stdlib.Bool Stdlib.List Stdlib.Impred;

///////////////////////////////////////////////////////////////////////
//////////////////////// ENCODINGS ////////////////////////////////////
///////////////////////////////////////////////////////////////////////

// literals 
// (defined by nth ⊥) returns the literal at a given index of a 
// list of literals
symbol literal ≔ nth ⊥;

// nths
// Takes a list of natural numbers and a list of objects of type a,
// and returns a new list where the objects are reordered according
// to the sequence of natural numbers.
symbol nths [a : Set] : τ a → 𝕃 a → 𝕃 nat → 𝕃 a;
rule nths $b $l $n ↪ map (nth $b $l) $n;
symbol literals ≔ nths ⊥;

// disj
// Takes a list of terms of type o and returns a disjunction of the
// given terms.
symbol disj : 𝕃 o → τ o;
rule disj ($l1 ⸬ ($c ⸬ $l)) ↪ ($l1 ∨ disj ($c ⸬ $l))
with disj ($l1 ⸬ □) ↪ $l1 
with disj □ ↪ ⊥;

// ⊆
// Takes a computable equality relation on type a and two lists of type a
// and returns true if the first list in included in the second, false
// otherwise
symbol ⊆  [a] : (τ a → τ a → 𝔹) → 𝕃 a → 𝕃 a → 𝔹;
rule ⊆ $beq ($k0 ⸬ $k) $l ↪ (∈ $beq $k0 $l) and (⊆ $beq $k $l)
with ⊆ _ □ _ ↪ true;
// ⊆ₙ (defined with respect to ⊆)
symbol ⊆ₙ ≔ ⊆ eqn;
notation ⊆ₙ infix right 30.000000;

// ∈ₙ (defined with respect to ∈)
symbol ∈ₙ ≔ ∈ eqn;
notation ∈ₙ infix right 30.000000;

// preserves_contents
// Takes a list of terms of type o and a list of natural numbers and returns 
// true if the indices of the list of terms of type o are include  in the list
// of natural numbers
symbol preserves_contents: 𝕃 nat → 𝕃 o → 𝔹;
rule preserves_contents  $f $l ↪ (indexes $l) ⊆ₙ $f;


///////////////////////////////////////////////////////////////////////
//////////////////////// PROOFS ///////////////////////////////////////
///////////////////////////////////////////////////////////////////////

opaque symbol literal_ext (l: 𝕃 o) (l0 : τ o) (n: τ nat) : 
    π (literal l n) → π (literal (l0 ⸬ l) (n +1)) ≔
begin
    assume l l0 n;
    assume h1;
    refine h1
end;

opaque symbol disj_head (l0 : τ o) (l : 𝕃 o) : 
    π (l0) → π (disj (l0 ⸬ l)) ≔
begin
    assume l0;
    induction
        {assume h1;
        refine h1}   
        {assume x0 l1 h1; 
        assume h2; 
        refine ∨ᵢ₁ h2}
end; 

opaque symbol disj_tail (l0 : τ o) (l : 𝕃 o) : 
    π (disj l) → π (disj (l0 ⸬ l)) ≔
begin
    assume l0;
    induction
        {assume h1;
        refine ⊥ₑ h1}
        {assume x1 l1 h1 h2;
        refine ∨ᵢ₂ h2}
end;

opaque symbol disj_correct (l0 : τ o) (l : 𝕃 o) : 
    π (disj (l0 ⸬ l)) → π (l0 ∨ disj l) ≔
begin
    assume l0;
    induction
        {assume h1;
        refine ∨ᵢ₁ h1}
        {assume x1 l1 h1 h2;
        refine h2}
end;

opaque symbol lit_imp_disj_pos (c: 𝕃 o) (ks: 𝕃 nat) : 
    π (`∃ x, (literal c x) ∧ (x ∈ₙ ks)) → π (disj (literals c ks)) ≔
begin
    assume c;
    induction
        {simplify;
        assume h1;
        have H0: (Π x: τ nat, π ((λ x1, literal c x1 ∧ ⊥) x) → π ⊥)
            {assume x h2;
            refine ∧ₑ₂ h2};
        refine ∃ₑ h1 H0}
        {assume n l;
        simplify;
        assume h1 h2;
        have H1 : Π x: τ nat, π ((λ x1, literal c x1 ∧ (eqn x1 n or x1 ∈ₙ l)) x) → π (disj (literal c n ⸬ literals c l))
            {assume m h3;
            have H0 : π ((eqn m n) ∨ (m ∈ₙ l))
                {refine ∨_istrue [eqn m n] [m ∈ₙ l] (∧ₑ₂ h3)};
            have H1 : π (eqn m n) → π (disj (literal c n ⸬ literals c l))
                {assume h4;
                have H1_0 : π (literal c n)
                    {have H1_0_0 : π (n = m)
                        {symmetry;
                        refine eqn_correct m n h4};
                    rewrite H1_0_0;
                    refine ∧ₑ₁ h3};
                refine disj_head (literal c n) (literals c l) H1_0};
            have H2 : π (m ∈ₙ l) → π (disj (literal c n ⸬ literals c l))
                {assume h4;
                have H2_0 : π `∃ x, literal c x ∧ (x ∈ₙ l)
                    {have H2_0_0 : π ((λ x, literal c x ∧ (x ∈ₙ l)) m)
                        {refine ∧ᵢ (∧ₑ₁ h3) h4};
                    refine ∃ᵢ m H2_0_0};
                refine disj_tail (literal c n) (literals c l) (h1 H2_0)};
            refine ∨ₑ H0 H1 H2
            };
        refine ∃ₑ h2 H1}   
end;

opaque symbol disj_imp_lit (l: 𝕃 o) : 
    π (disj l) → π (`∃ (x : τ nat), (literal l x) ∧ (x ∈ₙ (indexes l))) ≔
begin
    induction
        {assume h1;
        refine ⊥ₑ h1}
        {assume l0 l h1 h2;
        have H0: π (l0 ∨ disj l)
            {refine disj_correct l0 l h2};
        have H1: π l0 → π (`∃ x, (literal (l0 ⸬ l) x) ∧ (x ∈ₙ (indexes (l0 ⸬ l))))
            {assume h3;
            have H1_0 : π (literal (l0 ⸬ l) 0)
                {simplify;
                refine h3};
            have H1_1 : π ((λ x, literal (l0 ⸬ l) x ∧ (x ∈ₙ (indexes (l0 ⸬ l)))) 0)
                {simplify;
                refine ∧ᵢ H1_0 (0∈indexes⸬ l0 l)};
            refine ∃ᵢ [nat] [(λ x, literal (l0 ⸬ l) x ∧ (x ∈ₙ (indexes (l0 ⸬ l))))] 0 H1_1};
        have H2: π (disj l) → π (`∃ x, (literal (l0 ⸬ l) x) ∧ (x ∈ₙ (indexes (l0 ⸬ l))))
            {assume h3;
            have H2_0 : Π x0 , π ((λ x, literal l x ∧ (x ∈ₙ(indexes l))) x0) → π (`∃ x, (literal (l0 ⸬ l) x) ∧ (x ∈ₙ (indexes (l0 ⸬ l))))
                {assume n h4;
                have H2_0_0 : π ((λ x , (literal (l0 ⸬ l) x) ∧ (x ∈ₙ(indexes (l0 ⸬ l)))) (n +1))
                    {refine ∧ᵢ (literal_ext l l0 n ((∧ₑ₁ h4))) (+1∈indexes⸬ o n l l0 ((∧ₑ₂ h4)))};
                refine ∃ᵢ [nat] [λ x , (literal (l0 ⸬ l) x) ∧ (x ∈ₙ(indexes (l0 ⸬ l)))] (n +1) H2_0_0
                };
            refine ∃ₑ (h1 h3) [`∃ x, (literal (l0 ⸬ l) x) ∧ (x ∈ₙ(indexes (l0 ⸬ l)))] H2_0};
        refine ∨ₑ H0 H1 H2};
end;

opaque symbol x_in_x⸬ [a] (l: 𝕃 a) (l0 : τ a) (beq: τ a → τ a → 𝔹) : 
    (Π x, π (beq x x)) → π (∈ beq l0 (l0 ⸬ l)) ≔
begin
    assume a l l0 beq h1;
    type mem_head beq l0 l;
    type h1 l0;
    print istrue;
    refine orᵢ₁ [beq l0 l0] (∈ beq l0 l) (h1 l0)
end;

opaque symbol mem_tail [a] (beq: τ a → τ a → 𝔹) (n m: τ a) (l: 𝕃 a) : 
    π (∈ beq n l) → π (∈ beq n (m ⸬ l)) ≔
begin
    assume a beq n m;
    induction
        {assume h1;
        refine ⊥ₑ h1}
        {assume n0 l;
        assume h1 h2;
        have H0: π (beq n n0) →  π (beq n m or (beq n n0 or ∈ beq n l))
            {assume h3;
            refine orᵢ₂ (beq n m) [beq n n0 or ∈ beq n l] (orᵢ₁ [beq n n0] (∈ beq n l) h3)};
        have H1: π (∈ beq n l) →  π (beq n m or (beq n n0 or ∈ beq n l))
            {assume h3;
            refine orᵢ₂ (beq n m) [beq n n0 or ∈ beq n l] (orᵢ₂ (beq n n0) [∈ beq n l] h3)};
        refine orₑ [beq n n0] [∈ beq n l] (beq n m or (beq n n0 or ∈ beq n l)) h2 H0 H1}
end;

opaque symbol disj_imp_lit_pos (c: 𝕃 o) (ks: 𝕃 nat): 
    π (disj (literals c ks)) → π (`∃ (x : τ nat), (literal c x) ∧ (x ∈ₙ ks)) ≔
begin
    assume c;
    induction
        {assume h1;
        refine ⊥ₑ h1}
        {assume l0 ks;
        assume h1 h2;
        have H0: π ((literal c l0) ∨ disj (literals c ks))
            {refine disj_correct (literal c l0) (literals c ks) h2};
        have H1: π (literal c l0) → π (`∃ x, literal c x ∧ (x ∈ₙ(l0 ⸬ ks)))
            {assume h3;
            have H1_0 : π (literal c l0)
                {refine h3};
            have H1_1 : π ((λ x, literal  c x ∧ (x ∈ₙ(l0 ⸬ ks))) l0)
                {type mem_head eqn l0 ks;
                type eqn_complete l0 l0 (eq_refl l0);
                compute istrue (eqn l0 l0);
                type (λ x, (eqn_complete x x (eq_refl x)));
                type x_in_x⸬ ks l0 eqn (λ x, (eqn_complete x x (eq_refl x)));
                refine ∧ᵢ H1_0 (x_in_x⸬ ks l0 eqn (λ x, (eqn_complete x x (eq_refl x))))};
        refine ∃ᵢ [nat] [λ x, literal c x ∧ (x ∈ₙ(l0 ⸬ ks))] l0 H1_1};
        have H2: π (disj (literals c ks)) → π (`∃ x, literal c x ∧ (x ∈ₙ(l0 ⸬ ks)))
            {assume h3;
            have H2_0: (Π x: τ nat, π ((λ x1, literal c x1 ∧ (x1 ∈ₙ ks)) x) → π (`∃ x1, literal c x1 ∧ (x1 ∈ₙ (l0 ⸬ ks))))
                {assume n h4;
                have H2_0_0 : π ((λ x, literal c x ∧ (x ∈ₙ(l0 ⸬ ks))) n)
                    {refine ∧ᵢ (∧ₑ₁ h4) (mem_tail eqn n l0 ks (∧ₑ₂ h4))};
                refine ∃ᵢ [nat]  [λ x , literal c x ∧ (x ∈ₙ(l0 ⸬ ks))] n H2_0_0};
            refine ∃ₑ (h1 h3) [`∃ x, literal c x ∧ (x ∈ₙ(l0 ⸬ ks))] H2_0};    
        refine ∨ₑ H0 H1 H2}
end;

opaque symbol ⊆_el (n: τ nat) (σ: 𝕃 nat) (ln: 𝕃 nat): 
    π (ln ⊆ₙ σ) → π (n ∈ₙ ln) → π (n ∈ₙ σ) ≔
begin
    assume n σ;
    induction
        {assume h1 h2;
        refine ⊥ₑ h2}
        {assume m ln h1 h2 h3;
        have H1: π (eqn n m) → π (n ∈ₙ σ) 
            {assume h4;
            have H1_0 : π (n = m)
                {refine eqn_correct n m h4};
            rewrite H1_0;
            refine andₑ₁ [m ∈ₙ σ] [ln ⊆ₙ σ] h2};
        have H2: π (n ∈ₙ ln) → π (n ∈ₙ σ)
            {assume h4;
            refine h1 (andₑ₂ [m ∈ₙ σ] [ln ⊆ₙ σ] h2) h4};
        refine orₑ [eqn n m] [n ∈ₙ ln] (n ∈ₙ σ) h3 H1 H2}
end;

opaque symbol preserves_contents_el (n: τ nat) (σ : 𝕃 nat) (l: 𝕃 o) : 
    π (preserves_contents σ l) →  π (n ∈ₙ (indexes l)) → π (n ∈ₙ σ) ≔
begin
    assume n σ l;
    simplify;
    assume h1 h2;
    refine ⊆_el n σ (indexes l) h1 h2;   
end;


////////////////////////////////////////////////////////////////////////////////
///////////////////////////////// META-THEOREMS ////////////////////////////////
////////////////////////////////////////////////////////////////////////////////

opaque symbol permute (σ : 𝕃 nat) (c: 𝕃 o) : 
    π (preserves_contents σ c) → π(disj c) → π(disj (literals c σ)) ≔
begin
    assume σ c h1 h2;

    have H1: (Π x: τ nat, π ((λ x1, (literal c x1) ∧ (x1 ∈ₙ (indexes c))) x) → π (`∃ y ,(literal c y) ∧ (y ∈ₙ σ)))
        {assume x0 h3;
        refine (∃ᵢ [nat] [λ y ,(literal c y) ∧ (y ∈ₙ σ)] x0) (∧ᵢ (∧ₑ₁ h3) (preserves_contents_el x0 σ c h1 (∧ₑ₂ h3)))};
    
    have H2: π (`∃ y ,(literal c y) ∧ (y ∈ₙ σ))
        {refine ∃ₑ (disj_imp_lit c h2) H1};

    refine  lit_imp_disj_pos c σ H2;
end;

assert l0 l1 l2 ⊢ permute (1 ⸬ 2 ⸬ 0 ⸬ 3 ⸬ □) (l0 ⸬ l1 ⸬ l2 ⸬ l0 ⸬ □) ⊤ᵢ : π (l0 ∨ l1 ∨ l2 ∨ l0) → π (l1 ∨ l2 ∨ l0 ∨ l0);

opaque symbol transform [l : τ o] (c: 𝕃 o) (n : τ nat) : 
    π ((literal c n) ⇒ l) → π (disj c) → π (disj (set_nth ⊥ c n l)) ≔
begin
    assume l;
    induction
        {simplify;
        assume x h1 h2;
        refine ⊥ₑ h2}
        {assume x clause h1;
        induction
            {simplify;
            assume h2 h3;
            have H0: π (x ∨ (disj clause))
                {refine disj_correct x clause h3};
            have H1: π x → π (disj (l ⸬ clause))
                {assume h4;
                refine disj_head l clause (h2 h4)};
            have H2: π (disj clause) → π (disj (l ⸬ clause))
                {assume h4;
                refine disj_tail l clause h4};   
            refine ∨ₑ H0 H1 H2}
            {assume n h2 h3 h4;
            have H00: π (x ∨ (disj clause)) 
                {refine disj_correct x clause h4};
            have H10: π x → π (disj (x ⸬ set_nth ⊥ clause n l))
                {assume h5;
                refine disj_head x (set_nth ⊥ clause n l) h5};
            have H20:  π (disj clause) → π (disj (x ⸬ set_nth ⊥ clause n l))
                {assume h5;
                have H2_0 : π (disj (set_nth ⊥ clause n l))
                    {refine h1 n h3 h5};
                refine disj_tail x (set_nth ⊥ clause n l) H2_0};
            refine ∨ₑ H00 H10 H20}}
end;
