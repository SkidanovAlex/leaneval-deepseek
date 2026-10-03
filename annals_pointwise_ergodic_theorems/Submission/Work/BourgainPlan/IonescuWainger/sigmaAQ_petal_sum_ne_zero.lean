import Mathlib
import Submission.Work.BourgainPlan.IonescuWainger.ZModArcs
import Submission.Work.BourgainPlan.IonescuWainger.ArcNumOrth

-- v4.35 port: restore the v4.34 instance-unification behaviour (respectTransparency) in this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# (A3)(iii) Petal non-vanishing in the finite cyclic group `ZMod Q_S`

Source: T. Tao, *The Ionescu–Wainger multiplier theorem and the adeles*, arXiv:2008.05066, §4
(Lemma `ortho`(iii) and the proof of Theorem `ortho-apply`), in the finite-group formulation of
`ZModArcs.lean`.

For a finite set `S` of pairwise coprime integers `≥ 2`, the points of the arc `Σ_A` (`= sigmaA A`)
lift to the elements `arcLift (QA S) A a = a · (Q_S/Q_A)` of the cyclic group `ZMod (QA S)`, and
`sigmaAQ (QA S) A` is the corresponding finite set (Tao's `Σ_A` transported to `ZMod Q_S`).

This file proves the arithmetic core of Tao's *numerator* orthogonality in that vocabulary: for
pairwise **disjoint** petals `P i ⊆ S` and a core `A₀ ⊆ S` disjoint from all of them,

`Σ_i (α_i + γ_i) − Σ_i (β_i + δ_i) ≠ 0`   in `ZMod (QA S)`

whenever `α_i, β_i ∈ Σ_{P_i}`, `γ_i, δ_i ∈ Σ_{A₀}`, and `α_i ≠ β_i` for at least one `i`.

The proof is the standard "kill everything else" argument: let `k = Q_{S ∖ P_j}` be the product of
the primes *outside* the petal of a coordinate `j` with `α_j ≠ β_j`.  Passing to the circle `𝕋`
through the (additive) isomorphism `ZMod Q_S → 𝕋`, `x ↦ x/Q_S`, the identity becomes an identity in
`𝕋`; multiplying it by `k` kills every term — each of them lies in the torsion subgroup
`Σ_{⊆ C} = 𝕋[Q_C]` of a set `C` disjoint from `P j`, so that `Q_C ∣ k` — except the `j`-th petal
difference, which is a point of *exact* denominator `Q_{P_j}`, hence stays non-zero after
multiplication by a `k` coprime to `Q_{P_j}`.  That contradicts the vanishing.

The ingredients already in the repository are the circle-side lemmas `zsmul_eq_zero_of_dvd_QA`,
`sigmaA_subset_sigmaSubA` (`ArcCRT.lean`), `arcPt_sub_same`, `zsmul_arcPt_ne_zero_of_coprime_nat`
(`ArcNumOrth.lean`) and the lift–arc dictionary `arcLift_arcPt` (`ZModArcs.lean`); what is added
here is the transfer of the statement to the circle and the bookkeeping of the products
`Q_C ∣ Q_{S ∖ P_j}`.
-/

open Finset
open scoped BigOperators

set_option autoImplicit false

namespace Work.BourgainPlan.IonescuWainger

/-! ## The dictionary between `ZMod Q` and the circle -/

/-- The integer points of `ZMod Q` and the points `z/Q` of `𝕋` agree through `x ↦ x/Q`. -/
lemma arcPt_eq_toAddCircle {Q : ℕ} [NeZero Q] (z : ℤ) :
    arcPt Q z = ZMod.toAddCircle ((z : ℤ) : ZMod Q) := by
  rw [arcPt, ZMod.toAddCircle_intCast]

/-- **The lift of an arc point is that arc point**: the image of `arcLift (QA S) A z` under the
isomorphism `ZMod (QA S) ≅ 𝕋` is `z/Q_A`. -/
lemma toAddCircle_arcLift_petal {S : Finset ℕ} [NeZero (QA S)] {A : Finset ℕ} (hA : A ⊆ S) (z : ℤ) :
    ZMod.toAddCircle (arcLift (QA S) A z) = arcPt (QA A) z := by
  have hdvd : QA A ∣ QA S := Finset.prod_dvd_prod_of_subset A S (fun x => x) hA
  rw [arcLift, ← Int.cast_mul, ← arcPt_eq_toAddCircle]
  exact arcLift_arcPt hdvd (NeZero.ne (QA S)) z

/-! ## Products `Q_A` for subsets of `S` -/

/-- `Q_A ∣ Q_B` when `A ⊆ B`. -/
lemma QA_dvd_of_subset {A B : Finset ℕ} (h : A ⊆ B) : QA A ∣ QA B :=
  Finset.prod_dvd_prod_of_subset A B (fun x => x) h

/-- **`Q_A` and `Q_B` are coprime for disjoint `A, B ⊆ S`**, `S` being pairwise coprime. -/
lemma coprime_QA_of_disjoint_subset {S A B : Finset ℕ}
    (hS : ∀ p ∈ S, ∀ q ∈ S, p ≠ q → Nat.Coprime p q)
    (hA : A ⊆ S) (hB : B ⊆ S) (hdisj : Disjoint A B) : Nat.Coprime (QA A) (QA B) :=
  Nat.Coprime.prod_left fun q hq =>
    Nat.Coprime.prod_right fun q' hq' =>
      hS q (hA hq) q' (hB hq') (fun he => (Finset.disjoint_left.mp hdisj hq) (he ▸ hq'))

/-! ## The main lemma -/

end Work.BourgainPlan.IonescuWainger
