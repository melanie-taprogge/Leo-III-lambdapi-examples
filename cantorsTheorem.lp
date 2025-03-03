require open Stdlib.Set Stdlib.Prop Stdlib.FOL Stdlib.HOL Stdlib.Eq 
Stdlib.Impred Stdlib.Nat Stdlib.Bool Stdlib.List 
Leo-III-lambdapi-examples.extt Leo-III-lambdapi-examples.rules;

// OBJECT DECLARATIONS ///////////////////////////////////

symbol sk1: τ (ι ⤳ (ι ⤳ o));
symbol sk2: (τ ((ι ⤳ o) ⤳ ι));


// PROOF ENCODING ////////////////////////////////////////

opaque symbol encodedProof:π ¬ `∃ (A : τ (ι ⤳ (ι ⤳ o))), 
    `∀ (B : τ (ι ⤳ o)), `∃ (C : τ ι), A C = B ≔
begin
	refine dne (¬ `∃ (A : τ (ι ⤳ (ι ⤳ o))), 
        `∀ (B : τ (ι ⤳ o)), `∃ (C : τ ι), A C = B) _;
	assume negatedConjecture;
	// Rule "PolaritySwitch"
	have step4 : π `∃ (A : τ (ι ⤳ (ι ⤳ o))), 
        `∀ (B : τ (ι ⤳ o)), `∃ (C : τ ι), A C = B
		{have PolaritySwitch_lit0 : π ((`∃ (A : τ (ι ⤳ (ι ⤳ o))), 
            `∀ (B : τ (ι ⤳ o)), `∃ (C : τ ι), A C = B) = 
            (¬ (¬ `∃ (A : τ (ι ⤳ (ι ⤳ o))), 
            `∀ (B : τ (ι ⤳ o)), `∃ (C : τ ι), A C = B)))
			{refine ¬¬ₑ_eq (`∃ (A : τ (ι ⤳ (ι ⤳ o))), 
                `∀ (B : τ (ι ⤳ o)), `∃ (C : τ ι), A C = B)};
		rewrite PolaritySwitch_lit0;
		refine negatedConjecture};
	// Rule "CNF" (unencoded)
	have step5 : Π (A : τ (ι ⤳ o)), π ((sk1 (sk2 A)) = A)
		{admit};
	// Rule "FuncExt"
	have step7 : Π (B : τ ι), Π (A : τ (ι ⤳ o)), 
        π ((sk1 (sk2 A) B) = A B)
		{assume B A;
		have PFE_0 : (π ((sk1 (sk2 A)) = A) 
            → π ((sk1 (sk2 A) B) = A B))
			{refine (PFE (sk1 (sk2 A)) A B)};
		have FunExtApplication : π ((sk1 (sk2 A) B) = A B)
			{refine (PFE_0 (step5 A))};
		refine (FunExtApplication)};
	// Rule "BoolExt"
	have step9 : Π (B : τ ι), Π (A : τ (ι ⤳ o)), 
        π ((sk1 (sk2 A) B) ∨ ¬ A B)
		{assume B A;
		refine ((PBE_r (sk1 (sk2 A) B) (A B)) (step7 B A))};
	// Rule "OrderedEqFac"
	have step252 : Π (B : τ ι), Π (A : τ (ι ⤳ o)), 
        π((sk1 (sk2 A) B) ∨ (¬(A B = ¬ sk1 (sk2 A) B))∨ ¬ ⊤)
		{assume B A;
		have WholeEqFactStep : (π ((sk1 (sk2 A) B) ∨ ¬ A B) → π(
            (sk1 (sk2 A) B)∨(¬(A B = ¬ sk1 (sk2 A) B))∨ ¬ ⊤))
			{assume h1;
			have pre_eqFac_transform : π (¬(¬(sk1 (sk2 A) B) = ⊤) ∨ 
                ¬ (A B = ⊤))
				{rewrite .[x in x ∨ _] negEqPosProp;
				rewrite .[x in _ ∨ x] negEqNegProp;
				refine (h1)};
			have EqFact : π (¬ (¬ (sk1 (sk2 A) B) = ⊤) ∨ 
                (¬ (¬ sk1 (sk2 A) B = A B)) ∨ ¬ (⊤ = ⊤))
				{refine (EqFact_n [o] (¬ (sk1 (sk2 A) B)) ⊤ (A B) ⊤) 
                    pre_eqFac_transform};
			have post_eqFac_transform : π ((sk1 (sk2 A) B) ∨ 
                ¬ (A B = ¬ (sk1 (sk2 A) B)) ∨ ¬ ⊤)
				{rewrite .[x in x ∨ _ ∨ _] posPropNegEq;
				rewrite .[x in _ ∨ (¬ x) ∨ _] eqSym [o];
				rewrite .[x in _ ∨ _ ∨ x] negPropNegEq;
				rewrite .[x in _ ∨ _ ∨ (¬ x)] eqSym [o];
				refine EqFact};
			refine post_eqFac_transform};
		refine WholeEqFactStep (step9 B A)};
	// Rule "PreUni"
	have step269 : π (sk1 (sk2 (λ (A : τ ι), ¬ (sk1 A A))) 
        (sk2 (λ (A : τ ι), ¬ (sk1 A A))))
		{have Substitution : π((sk1 (sk2 (λ(C : τ ι),¬(sk1 C C))) 
            (sk2 (λ (C : τ ι),¬(sk1 C C))))∨ ¬(((λ (C : τ ι), 
            ¬ (sk1 C C)) (sk2 (λ (C : τ ι), ¬ (sk1 C C)))) = 
            ¬ (sk1 (sk2 (λ (C : τ ι), ¬ (sk1 C C))) 
            (sk2 (λ (C : τ ι), ¬ (sk1 C C))))) ∨ ¬ ⊤)
			{refine (step252 (sk2 (λ (C : τ ι), 
			    ¬ (sk1 C C))) (λ (C : τ ι), ¬ (sk1 C C)))};
		rewrite ∨⊥;
		rewrite .[x in _ ∨ x] (¬eqxx o ((λ (C : τ ι), 
            ¬ (sk1 C C)) (sk2 (λ (C : τ ι), ¬ (sk1 C C)))));
		rewrite .[x in _ ∨ x] ∨⊥;
		rewrite .[x in _ ∨ _ ∨ x] ¬⊤;
		refine Substitution};
	// Rule "BoolExt"
	have step8 : Π (B : τ ι), Π (A : τ (ι ⤳ o)), 
	    π (¬ (sk1 (sk2 A) B) ∨ A B)
		{assume B A;
		refine (PBE_l (sk1 (sk2 A) B) (A B)) (step7 B A)};
	// Rule "OrderedEqFac"
	have step18 : Π (B : τ ι), Π (A : τ (ι ⤳ o)), 
	    π (¬(sk1 (sk2 A) B) ∨ ¬(A B = ¬(sk1 (sk2 A) B)) ∨ ¬ ⊤)
		{assume B A;
		have WholeEqFactStep : π (¬ (sk1 (sk2 A) B) ∨ A B) → 
            π (¬ (sk1 (sk2 A) B) ∨ 
            ¬ (A B = ¬ (sk1 (sk2 A) B)) ∨ ¬ ⊤)
			{assume h1;
			have pre_eqFac_transform : π ((¬ (sk1 (sk2 A) B) = ⊤) ∨ (A B = ⊤))
				{rewrite .[x in x ∨ _] posEqNegProp;
				rewrite .[x in _ ∨ x] posEqPosProp;
				refine h1};
			have EqFact : π ((¬ (sk1 (sk2 A) B) = ⊤) ∨ 
                ¬ ((¬ (sk1 (sk2 A) B)) = A B) ∨ ¬ (⊤ = ⊤))
				{refine (EqFact_p [o] (¬ (sk1 (sk2 A) B)) ⊤ (A B) ⊤) 
                    pre_eqFac_transform};
			have post_eqFac_transform : π (¬ (sk1 (sk2 A) B) ∨ 
			    ¬ ((A B) = (¬ (sk1 (sk2 A) B))) ∨ ¬ ⊤)
				{rewrite .[x in x ∨ _ ∨ _] negPropPosEq;
				rewrite .[x in _ ∨ (¬ x) ∨ _] eqSym [o];
				rewrite .[x in _ ∨ _ ∨ x] negPropNegEq;
				rewrite .[x in _ ∨ _ ∨ (¬ x)] eqSym [o];
				refine EqFact};
			refine post_eqFac_transform};
		refine WholeEqFactStep (step8 B A)};
	// Rule "PreUni"
	have step33 : π (¬ (sk1 (sk2 (λ (A : τ ι), ¬ (sk1 A A))) 
	    (sk2 (λ (A : τ ι), ¬ (sk1 A A)))))
		{have Substitution : π (¬ (sk1 (sk2 (λ (C : τ ι), 
		    ¬ (sk1 C C)))) (sk2 (λ (C : τ ι),  ¬ (sk1 C C))) ∨ 
		    ¬ (((λ (C : τ ι), ¬ (sk1 C C))) (sk2 (λ (C : τ ι), 
		    ¬ (sk1 C C))) = ¬ (sk1 (sk2 (λ (C : τ ι), ¬ (sk1 C 
		    C)))) (sk2 (λ (C : τ ι), ¬ (sk1 C C)))) ∨ ¬ ⊤)
			{refine (step18 (sk2 (λ (C : τ ι), 
			    ¬ (sk1 C C))) (λ (C : τ ι), ¬ (sk1 C C)))};
		rewrite ∨⊥;
		rewrite .[x in _ ∨ x] ¬eqxx o ((λ (C : τ ι), 
		    (¬ (sk1 C C))) (sk2 (λ (C : τ ι), ¬ (sk1 C C))));
		rewrite .[x in _ ∨ x] ∨⊥;
		rewrite .[x in _ ∨ _ ∨ x] ¬⊤;
		refine Substitution};
	// Rule "RewriteSimp"
	have step384 : π ⊥
		{have TransformToEqLits_1 : π(⊥ = (sk1 (sk2 (λ (A : τ ι), 
            ¬ (sk1 A A)))) (sk2 (λ (A : τ ι), ¬ (sk1 A A))))
			{rewrite botNegProp;
			refine step33};
		rewrite .[x in x] TransformToEqLits_1;
		refine step269};
	refine step384
end;