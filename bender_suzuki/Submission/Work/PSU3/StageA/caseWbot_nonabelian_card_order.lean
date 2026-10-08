import Mathlib
import Submission.Work.PSU3.StageA.caseWbot_setup
import Submission.Work.PSU3.StageA.caseWbot_branch_one_false_of_card_square
import Submission.Work.PSU3.StageA.caseWbot_branch_one_false_of_card_cube
import Submission.Work.PSU3.StageA.caseWbot_branch_three_false
import Submission.Work.PSU3.StageA.caseWbot_branch_two_false_of_card_cube

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.PSU3.StageA.caseWbot_nonabelian_card_order`

Peterfalvi II Ch. VI §1, the non-abelian branch with `W = C_V(K) = ⊥`: for the structure-identity
data `s ∈ Q`, `r ∈ Q` (`t s t = r⁻¹ t r`) the group `Q` has order `q²` (`q = |Q0sub H|`) and
`s * t` has order `5` (case b) of the Proposition of Ch. VI §1).

The proof is the case analysis of Ch. V §2 Lemma 2 c) (`Work.PSU3.StageA.lemma2cHig`) combined
with Higman's dichotomy `|Q| = q²` or `q³` (`Work.PSU3.StageA.caseWbot_setup`).  For
`P ≤ V = centD H t` of prime order the local trichotomy gives one of

* **(i)** `orderOf (s*t) = 3`, `C = Q ⊓ C_G(P)` abelian, `|C| = ℓ`;
* **(ii)** `orderOf (s*t) = 5`, `C` non-abelian, `|C| = ℓ²` (and equal squares lie in `Q0sub H`);
* **(iii)** `orderOf (s*t) = 3`, `|C| = ℓ³`, with a witness `x ∈ D ⊓ C_G(P) ∖ P` centralising
  `C_{Q₀}(P)`,

where `ℓ = |Q0sub H ⊓ C_G(P)|`.  The three sibling modules exclude (i) (both for `|Q| = q²` —
`caseWbot_branch_one_false_of_card_square` — and for `|Q| = q³` —
`caseWbot_branch_one_false_of_card_cube`), (ii) in the case `|Q| = q³`
(`caseWbot_branch_two_false_of_card_cube`) and (iii) (`caseWbot_branch_three_false`).  Hence for
`|Q| = q²` only (ii) survives, giving the result, and for `|Q| = q³` all branches are impossible,
which is also the result (ex falso).
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Work.PSU3.StageA

open LeanEval.GroupTheory.Defs
open Submission.Blueprint

variable {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G}

/-! ## Assembly of the target

For `P ≤ V = centD H t` of prime order, `lemma2cHig` (Ch. V §2 Lemma 2 c) gives the trichotomy
```
(i)   orderOf (s*t) = 3, C abelian,        |C| = ℓ        (PSL(2,ℓ)),
(ii)  orderOf (s*t) = 5, C non-abelian,    |C| = ℓ², …    (Sz(ℓ)),
(iii) orderOf (s*t) = 3,                   |C| = ℓ³, and a witness `x` (PSU(3,ℓ)),
```
with `C = Q ⊓ C_G(P)`, `ℓ = |Q0sub H ⊓ C_G(P)|`, and `|Q| = q²` or `q³` (Higman).  The three
branch exclusions proved in the sibling modules kill every branch except (ii) with `|Q| = q²`,
which is exactly the conclusion:

* `caseWbot_branch_one_false_of_card_square` / `.._of_card_cube`: branch (i) forces
  `C ⊆ Q0sub H`, i.e. `P` fixed-point-free on `Q/Q0sub H`, which the fibrewise counting argument
  (`|{x ∈ Q | x² = s}| = q` resp. `q(q+1)`, congruent to `|F_s ∩ C| = ℓ` mod `p`) contradicts;
* `caseWbot_branch_three_false`: branch (iii)'s witness `x ∈ D ⊓ C_G(P) ∖ P` centralises
  `C_{Q₀}(P) ∋ s`, hence lies in `V = D ⊓ C_G(s)`, and the Galois step
  (`galois_step_of_Ksub`, Ch. V §1 Prop. 3) puts it in `P · W = P`;
* `caseWbot_branch_two_false_of_card_cube`: branch (ii) with `|Q| = q³` would give
  `q(q+1) ≡ ℓ (mod p)` with `q = 2ⁿ = 2^{pm}`, `ℓ = 2^m`, i.e. `p ∣ 2`.
-/

theorem caseWbot_nonabelian_card_order {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G}
    {s r : G} (hS : Work.PSU3.PSU3Hyp H Q t) (hC4 : Submission.Blueprint.ChIIFourProp)
    (hFT : Submission.Blueprint.FeitThompsonProp)
    (hs : s ∈ Q) (hs2 : orderOf s = 2) (hr : r ∈ Q) (hsr : t * s * t = r⁻¹ * t * r)
    (hW : Work.ThmF.W H t = ⊥)
    (hnab : ¬ Submission.Blueprint.IsAbelianSubgroup Q) :
    Nat.card Q = Nat.card (Work.ThmF.Q0sub H) ^ 2 ∧ orderOf (s * t) = 5 := by
  obtain ⟨P, hP, hp⟩ := caseWbot_exists_prime_subgroup_centD (H := H) (Q := Q) (t := t) hS
  have htri := Work.PSU3.StageA.lemma2cHig hS hC4 Work.PSU3.benderSTProp hs hs2 hr hsr hP hp
  rcases caseWbot_card_dichotomy hS hFT hC4 hnab with hcard2 | hcard3
  · -- `|Q| = q²`: branches (i) and (iii) are impossible, so branch (ii) holds
    rcases htri with h1 | h2 | h3
    · exact absurd h1
        (caseWbot_branch_one_false_of_card_square hS hC4 hFT hs hs2 hr hsr hnab hcard2 hP hp)
    · exact ⟨hcard2, h2.1⟩
    · exact absurd h3.2.2 (caseWbot_branch_three_false hS hC4 hFT hW hP hp)
  · -- `|Q| = q³`: all three branches are impossible
    rcases htri with h1 | h2 | h3
    · exact absurd h1
        (caseWbot_branch_one_false_of_card_cube hS hC4 hFT hs hs2 hr hsr hW hnab hcard3 hP hp)
    · exact absurd h2
        (caseWbot_branch_two_false_of_card_cube hS hC4 hFT hs hs2 hr hsr hW hnab hcard3 hP hp)
    · exact absurd h3.2.2 (caseWbot_branch_three_false hS hC4 hFT hW hP hp)

end Work.PSU3.StageA
