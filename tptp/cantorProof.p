% Time passed: 1424ms (effective reasoning time: 997ms)
% Solved by strategy<name(default),share(1.0),primSubst(3),sos(false),unifierCount(4),uniDepth(8),boolExt(true),choice(true),renaming(true),funcspec(false), domConstr(0),specialInstances(39),restrictUniAttempts(true),termOrdering(CPO)>
% Axioms used in derivation (0): 
% No. of inferences in proof: 15
% SZS status Theorem for sur_cantor.p : 1424 ms resp. 997 ms w/o parsing
% SZS output start Refutation for sur_cantor.p

thf(sk1_type, type, 
    sk1: ($i > ($i > $o))).

thf(sk2_type, type, 
    sk2: (($i > $o) > $i)).

thf(1,conjecture,
    ((~ (? [A:($i > ($i > $o))]: 
        ! [B:($i > $o)]: 
        ? [C:$i]: ((A @ C) = B)))),
        file('sur_cantor.p',sur_cantor)).

thf(2,negated_conjecture,
    ((~ (~ (? [A:($i > ($i > $o))]: 
            ! [B:($i > $o)]: 
            ? [C:$i]: ((A @ C) = B))))),
            inference(neg_conjecture,[status(cth)],[1])).

thf(3,plain,
    ((~ (~ (? [A:($i > ($i > $o))]: 
            ! [B:($i > $o)]: 
            ? [C:$i]: ((A @ C) = (B)))))),
            inference(defexp_and_simp_and_etaexpand,[status(thm)],[2])).

thf(4,plain,
    ((? [A:($i > ($i > $o))]: 
    ! [B:($i > $o)]: 
    ? [C:$i]: ((A @ C) = (B)))),
    inference(polarity_switch,[status(thm)],[3])).

thf(5,plain,
    (! [A:($i > $o)] : 
    (((sk1 @ (sk2 @ A)) = (A)))),
    inference(cnf,[status(esa)],[4])).

thf(6,plain,
    (! [A:($i > $o)] : 
    (((sk1 @ (sk2 @ A)) = (A)))),
    inference(lifteq,[status(thm)],[5])).

thf(7,plain,
    (! [B:$i,A:($i > $o)] : 
    (((sk1 @ (sk2 @ (A)) @ B) = (A @ B)))),
    inference(func_ext,[status(esa)],[6])).

thf(9,plain,
    (! [B:$i,A:($i > $o)] : 
    ((sk1 @ (sk2 @ (A)) @ B) | (~ (A @ B)))),
    inference(bool_ext,[status(thm)],[7])).

thf(250,plain,
    (! [B:$i,A:($i > $o)] : 
    ((sk1 @ (sk2 @ (A)) @ B) | ((A @ B) != (~ (sk1 @ (sk2 @ (A)) @ B))) | ~ (($true)))),
    inference(eqfactor_ordered,[status(thm)],[9])).

thf(268,plain,
    ((sk1 @ (sk2 @ (^ [A:$i]: ~ (sk1 @ A @ A))) @ (sk2 @ (^ [A:$i]: ~ (sk1 @ A @ A))))),
    inference(pre_uni,[status(thm)],[250:[bind(A, $thf(^ [C:$i]: ~ (sk1 @ C @ C))),bind(B, $thf(sk2 @ (^ [C:$i]: ~ (sk1 @ C @ C))))]])).

thf(8,plain,
    (! [B:$i,A:($i > $o)] : 
    ((~ (sk1 @ (sk2 @ (A)) @ B)) | (A @ B))),
    inference(bool_ext,[status(thm)],[7])).

thf(18,plain,
    (! [B:$i,A:($i > $o)] : 
    ((~ (sk1 @ (sk2 @ (A)) @ B)) | ((A @ B) != (~ (sk1 @ (sk2 @ (A)) @ B))) | ~ (($true)))),
    inference(eqfactor_ordered,[status(thm)],[8])).

thf(32,plain,
    ((~ (sk1 @ (sk2 @ (^ [A:$i]: ~ (sk1 @ A @ A))) @ (sk2 @ (^ [A:$i]: ~ (sk1 @ A @ A)))))),
    inference(pre_uni,[status(thm)],[18:[bind(A, $thf(^ [C:$i]: ~ (sk1 @ C @ C))),bind(B, $thf(sk2 @ (^ [C:$i]: ~ (sk1 @ C @ C))))]])).

thf(400,plain,
    (($false)),
    inference(rewrite,[status(thm)],[268,32])).

thf(401,plain,
    (($false)),
    inference(simp,[status(thm)],[400])).

% SZS output end Refutation for cantorProblem.p