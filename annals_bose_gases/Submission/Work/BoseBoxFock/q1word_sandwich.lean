import ChallengeDeps
import Submission.Work.BoseBoxFock.chiRowDefs2
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.q1word_sandwich`

The `q1word` sandwich shape used by the χ-row chapter: the corpus's `n₀`-sandwich
form of `q1word` (`Submission.Work.Q1Peel.q1word_eq_sandwich_f2`, eq:Q1n0) with

* the localized kernels `wLoc ℓ (g₀ v h) 0`, `wLoc ℓ (g₂ v h) 0` replaced by the
  (definitionally identical) `wPairC ℓ (g₀ v h)`, `wPairC ℓ (g₂ v h)` — at `u = 0`
  the cell bump `χU ℓ 0` is the plain scaled bump `chiScale ℓ`, so `wLoc · 0 = wPairC`;
* the `i`-slot `Q`-argument `∑_{j ≠ i} aP ℓ j Φ` relaxed to the full `∑_j aP ℓ j Φ`
  — the two differ by the `i`-summand `aP ℓ i Φ`, which is invariant in slot `i`
  and therefore annihilated by `aQ ℓ i`.

Both helper lemmas below are unconditional and independent of each other.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace Work.BoseBoxFock

/-- At `u = 0` the localized kernel is the (unlocalized) renormalized pair kernel:
`wLoc ℓ h 0 = wPairC ℓ h` (definitional, since `chiU ℓ 0 = chiScale ℓ`). -/
lemma wLoc_zero_eq_wPairC (ℓ : ℝ) (h : EuclideanSpace ℝ (Fin 3) → ℝ) :
    Submission.BoseGases.wLoc ℓ h 0 = Submission.BoseGases.wPairC ℓ h := by
  funext x y
  simp [Submission.BoseGases.wLoc, Submission.BoseGases.wPairC, Submission.BoseGases.wPair,
        Submission.BoseGases.chiU, Submission.BoseGases.chiScale]

/-- `aQ ℓ i` does not see the `i`-summand of `∑_j aP ℓ j Φ`: the slot-`i`
complement projection of the full condensate sum equals that of the
`j ≠ i`-restricted sum. -/
lemma aQ_sum_aP_eq {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (i : Fin N)
    {Φ : Submission.BoseGases.X N → ℝ} (hΦc : Continuous Φ)
    (x : Submission.BoseGases.X N) :
    Submission.BoseGases.aQ ℓ i (fun y => ∑ j : Fin N, Submission.BoseGases.aP ℓ j Φ y) x
      = Submission.BoseGases.aQ ℓ i
          (fun y => ∑ j : Fin N, if j ≠ i then Submission.BoseGases.aP ℓ j Φ y else 0) x := by
  set A : Submission.BoseGases.X N → ℝ :=
    fun z => ∑ j : Fin N, if j ≠ i then Submission.BoseGases.aP ℓ j Φ z else 0 with hA
  set H : Submission.BoseGases.X N → ℝ := Submission.BoseGases.aP ℓ i Φ with hH
  have hAc : Continuous A := by
    rw [hA]
    refine continuous_finsetSum _ ?_
    intro j _
    by_cases hji : j ≠ i
    · simpa [hji] using Submission.BoseGases.aP_continuous hℓ j hΦc
    · simpa [hji] using continuous_const
  have hHc : Continuous H := by
    rw [hH]; exact Submission.BoseGases.aP_continuous hℓ i hΦc
  have hAH : (fun z : Submission.BoseGases.X N =>
        ∑ j : Fin N, Submission.BoseGases.aP ℓ j Φ z) = A + H := by
    rw [hA, hH]
    funext z
    simp only [Pi.add_apply]
    have h3 : (∑ j : Fin N, if j ≠ i then Submission.BoseGases.aP ℓ j Φ z else 0)
        = ∑ j : Fin N, (Submission.BoseGases.aP ℓ j Φ z
            - (if j = i then Submission.BoseGases.aP ℓ j Φ z else 0)) := by
      refine Finset.sum_congr rfl ?_
      intro j _
      by_cases hji : j = i <;> simp [hji]
    have h2 : (∑ j : Fin N, if j ≠ i then Submission.BoseGases.aP ℓ j Φ z else 0)
        = (∑ j : Fin N, Submission.BoseGases.aP ℓ j Φ z) - Submission.BoseGases.aP ℓ i Φ z := by
      rw [h3, Finset.sum_sub_distrib, Finset.sum_ite_eq']
      simp
    rw [h2]; ring
  have hAHy : Submission.BoseGases.aP ℓ i (A + H) x
      = Submission.BoseGases.aP ℓ i A x + H x := by
    rw [Submission.BoseGases.aP_add hℓ i hAc hHc x, hH]
    rw [Submission.BoseGases.aP_idem hℓ i hΦc x]
  have hQ : Submission.BoseGases.aQ ℓ i (A + H) x = Submission.BoseGases.aQ ℓ i A x := by
    simp only [Submission.BoseGases.aQ]
    rw [Pi.add_apply, hAHy]
    ring
  calc Submission.BoseGases.aQ ℓ i
        (fun y => ∑ j : Fin N, Submission.BoseGases.aP ℓ j Φ y) x
      = Submission.BoseGases.aQ ℓ i (A + H) x := by rw [hAH]
    _ = Submission.BoseGases.aQ ℓ i A x := hQ
    _ = Submission.BoseGases.aQ ℓ i
          (fun y => ∑ j : Fin N, if j ≠ i then Submission.BoseGases.aP ℓ j Φ y else 0) x := by
        rw [hA]

theorem q1word_sandwich {n : ℕ} {ℓ μ : ℝ} (hℓ : 0 < ℓ) {v : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hv : 0 ≤ v) (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R) (h : Work.UBB.ScatSol v)
    (hRℓ : R ≤ ℓ * Submission.BoseGases.chiR0) {Φ : Submission.BoseGases.X n → ℝ}
    (hΦc : Continuous Φ) :
    Submission.BoseGases.q1word (N := n) ℓ μ
        (Submission.BoseGases.wLoc ℓ (Submission.BoseGases.g0 v h) 0)
        (Submission.BoseGases.wLoc ℓ (Submission.BoseGases.g2 v h) 0) Φ
      = 2 * (ℓ ^ 3)⁻¹ * (∑ i : Fin n, ∫ x in Submission.BoseGases.abox n ℓ,
            Submission.BoseGases.aP ℓ i Φ x *
              (Submission.BoseGases.w1Fibre ℓ (Submission.BoseGases.wLoc ℓ (Submission.BoseGases.g2 v h) 0) (x i)) *
              (Submission.BoseGases.aQ ℓ i (fun y : Submission.BoseGases.X n =>
                ∑ j : Fin n, Submission.BoseGases.aP ℓ j Φ y) x))
        - 2 * μ * (∑ i : Fin n, ∫ x in Submission.BoseGases.abox n ℓ,
            (Submission.BoseGases.aQ ℓ i Φ x) * (Submission.BoseGases.aP ℓ i Φ x) *
              (Submission.BoseGases.w1Fibre ℓ (Submission.BoseGases.wLoc ℓ (Submission.BoseGases.g0 v h) 0) (x i))) := by
  have hw0 : Submission.BoseGases.wLoc ℓ (Submission.BoseGases.g0 v h) 0
      = Submission.BoseGases.wPairC ℓ (Submission.BoseGases.g0 v h) :=
    wLoc_zero_eq_wPairC ℓ _
  have hw2 : Submission.BoseGases.wLoc ℓ (Submission.BoseGases.g2 v h) 0
      = Submission.BoseGases.wPairC ℓ (Submission.BoseGases.g2 v h) :=
    wLoc_zero_eq_wPairC ℓ _
  rw [hw0, hw2,
    Submission.BoseGases.q1word_eq_sandwich_f2 (N := n) (μ := μ) hℓ hv hvrad hR hv_supp h hRℓ hΦc]
  -- only the slot-`i` `Q`-argument of the pair line differs
  have hS : (∑ i : Fin n, ∫ x in Submission.BoseGases.abox n ℓ,
        Submission.BoseGases.aP ℓ i Φ x *
          (Submission.BoseGases.w1Fibre ℓ
            (Submission.BoseGases.wPairC ℓ (Submission.BoseGases.g2 v h)) (x i)) *
          (Submission.BoseGases.aQ ℓ i (fun y : Submission.BoseGases.X n =>
            ∑ j : Fin n, Submission.BoseGases.aP ℓ j Φ y) x))
      = (∑ i : Fin n, ∫ x in Submission.BoseGases.abox n ℓ,
        Submission.BoseGases.aP ℓ i Φ x *
          (Submission.BoseGases.w1Fibre ℓ
            (Submission.BoseGases.wPairC ℓ (Submission.BoseGases.g2 v h)) (x i)) *
          (Submission.BoseGases.aQ ℓ i (fun y : Submission.BoseGases.X n =>
            ∑ j : Fin n, if j ≠ i then Submission.BoseGases.aP ℓ j Φ y else 0) x)) := by
    refine Finset.sum_congr rfl ?_
    intro i _
    refine integral_congr_ae ?_
    filter_upwards with x
    rw [aQ_sum_aP_eq hℓ i hΦc x]
    try rfl
  rw [hS]
  try rfl

end Work.BoseBoxFock
