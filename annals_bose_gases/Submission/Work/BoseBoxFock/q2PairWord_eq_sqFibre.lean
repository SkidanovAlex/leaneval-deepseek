import ChallengeDeps
import Submission.Work.BoseBoxFock.q2wordAux
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseBoxFock

open MeasureTheory
open scoped BigOperators

/-!
# `Work.BoseBoxFock.q2PairWord_eq_sqFibre`

The T₂ pair word `q2PairWord` (the `P_iQ_j w₂ P_jQ_i` term of FS `eq:DefQ2`, with the
chosen kernel `w₂ = wPairC ℓ (g₂ v h)`) is a sum over ordered distinct pairs of the
Φ-integral of `(P_iQ_jΦ)²·w₂(x_i,x_j)`.  This file rewrites it in the *squared-fibre*
form used by the box ↔ model Q₂ dictionary:

    q2PairWord = (ℓ³)⁻¹ · Σ_i Σ_{j≠i} ∫_{Λ(ℓ)^N} (P_jQ_iΦ)² · fibre₂(x_i) ,

where `fibre₂(z) = ∫_{acube ℓ} w₂(z,y) dy = w1Fibre ℓ (wPairC ℓ (g₂ v h)) z`.

The only analytic input is the per-pair peel identity
`Submission.BoseGases.q2QQ_lhs_closed` (proved in `Submission/Work/Q2Mass.lean` for a
particle number written as `p + 2`): since `(P_jQ_iΦ)²` is a constant function of the
`j`-th coordinate, integrating out that coordinate over the cube turns `w₂(·,x_i)` into
its fibre.  The helper `q2lhs_closed_gen` below removes the `p + 2`-spelling restriction
(the cases `N ≤ 1` are vacuous because `i ≠ j` cannot hold).

The remaining steps are purely combinatorial: the square rewrite
`(P_jQ_iΦ)·(Q_jP_iΦ) = (P_jQ_iΦ)²` (`aP_aQ_comm`), the reindexing of the ordered pair
sum by its second component (`pairSet_sum_swap_split`), and pulling the constant `(ℓ³)⁻¹`
out of the double sum.
-/

/-- The per-pair peel identity `∫_x (P_jQ_iΦ)²·w₂(x_j,x_i) = (ℓ³)⁻¹∫_x (P_jQ_iΦ)²·fibre₂(x_i)`
for an **arbitrary** particle number `N` (`Submission.BoseGases.q2QQ_lhs_closed` is stated
for `X (p + 2)`; the cases `N ≤ 1` carry no distinct `i j`). -/
lemma q2lhs_closed_gen {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ)
    {v : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hv_nonneg : 0 ≤ v) (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    (h : ∃ w : EuclideanSpace ℝ (Fin 3) → ℝ,
      _root_.BoseGases.IsRadial w ∧ _root_.BoseGases.IsScatteringSolution w v)
    (hRℓ : R ≤ ℓ * Submission.BoseGases.chiR0)
    (i j : Fin N) (hij : i ≠ j) {Φ : Submission.BoseGases.X N → ℝ} (hΦc : Continuous Φ) :
    (∫ x in Submission.BoseGases.abox N ℓ,
        (Submission.BoseGases.aP ℓ j (Submission.BoseGases.aQ ℓ i Φ) x) ^ 2 *
          Submission.BoseGases.wPairC ℓ (Submission.BoseGases.g2 v h) (x j) (x i))
    = (ℓ ^ 3)⁻¹ * (∫ x in Submission.BoseGases.abox N ℓ,
        (Submission.BoseGases.aP ℓ j (Submission.BoseGases.aQ ℓ i Φ) x) ^ 2 *
          (Submission.BoseGases.w1Fibre ℓ
            (Submission.BoseGases.wPairC ℓ (Submission.BoseGases.g2 v h)) (x i))) := by
  obtain ⟨m, rfl⟩ : ∃ m, N = m + 2 := by
    have hne : (i : ℕ) ≠ (j : ℕ) := fun hh => hij (Fin.ext hh)
    exact ⟨N - 2, by omega⟩
  exact Submission.BoseGases.q2QQ_lhs_closed (p := m) hℓ hv_nonneg hvrad hR hv_supp h hRℓ
    i j hij hΦc

theorem q2PairWord_eq_sqFibre {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ)
    {v : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hv_nonneg : 0 ≤ v) (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    (h : ∃ w : EuclideanSpace ℝ (Fin 3) → ℝ,
      _root_.BoseGases.IsRadial w ∧ _root_.BoseGases.IsScatteringSolution w v)
    (hRℓ : R ≤ ℓ * Submission.BoseGases.chiR0)
    {Φ : Submission.BoseGases.X N → ℝ} (hΦc : Continuous Φ) :
    Submission.BoseGases.q2PairWord (ℓ := ℓ) (v := v) h (Φ := Φ)
      = (ℓ ^ 3)⁻¹ * ∑ i : Fin N, ∑ j : Fin N, (if j ≠ i then
          (∫ x in Submission.BoseGases.abox N ℓ,
            (Submission.BoseGases.aP ℓ j (Submission.BoseGases.aQ ℓ i Φ) x) ^ 2
              * Submission.BoseGases.w1Fibre ℓ
                  (Submission.BoseGases.wPairC ℓ (Submission.BoseGases.g2 v h)) (x i))
          else 0) := by
  classical
  -- 1. unfold `q2PairWord`
  have hq : Submission.BoseGases.q2PairWord (ℓ := ℓ) (v := v) h (Φ := Φ)
      = ∑ p ∈ Submission.BoseGases.pairSet N, ∫ x in Submission.BoseGases.abox N ℓ,
          (Submission.BoseGases.aP ℓ p.1 (Submission.BoseGases.aQ ℓ p.2 Φ) x) *
            (Submission.BoseGases.aQ ℓ p.2 (Submission.BoseGases.aP ℓ p.1 Φ) x) *
            Submission.BoseGases.wPairC ℓ (Submission.BoseGases.g2 v h) (x p.1) (x p.2) := rfl
  -- 2. `Q_jP_iΦ = P_iQ_jΦ` turns the word into its square form
  have hsq : (∑ p ∈ Submission.BoseGases.pairSet N, ∫ x in Submission.BoseGases.abox N ℓ,
          (Submission.BoseGases.aP ℓ p.1 (Submission.BoseGases.aQ ℓ p.2 Φ) x) *
            (Submission.BoseGases.aQ ℓ p.2 (Submission.BoseGases.aP ℓ p.1 Φ) x) *
            Submission.BoseGases.wPairC ℓ (Submission.BoseGases.g2 v h) (x p.1) (x p.2))
      = ∑ p ∈ Submission.BoseGases.pairSet N, ∫ x in Submission.BoseGases.abox N ℓ,
          (Submission.BoseGases.aP ℓ p.1 (Submission.BoseGases.aQ ℓ p.2 Φ) x) ^ 2 *
            Submission.BoseGases.wPairC ℓ (Submission.BoseGases.g2 v h) (x p.1) (x p.2) := by
    apply Finset.sum_congr rfl
    intro p hp
    have hpij : p.1 ≠ p.2 := by
      simpa [Submission.BoseGases.pairSet] using (Finset.mem_filter.mp hp).2
    apply integral_congr_ae
    refine ae_of_all _ (fun x => ?_)
    change Submission.BoseGases.aP ℓ p.1 (Submission.BoseGases.aQ ℓ p.2 Φ) x *
        Submission.BoseGases.aQ ℓ p.2 (Submission.BoseGases.aP ℓ p.1 Φ) x *
          Submission.BoseGases.wPairC ℓ (Submission.BoseGases.g2 v h) (x p.1) (x p.2)
      = (Submission.BoseGases.aP ℓ p.1 (Submission.BoseGases.aQ ℓ p.2 Φ) x) ^ 2 *
          Submission.BoseGases.wPairC ℓ (Submission.BoseGases.g2 v h) (x p.1) (x p.2)
    rw [← Submission.BoseGases.aP_aQ_comm hℓ hpij hΦc x]
    ring
  -- 3. reindex the ordered pair sum by its second component
  have hre : (∑ p ∈ Submission.BoseGases.pairSet N, ∫ x in Submission.BoseGases.abox N ℓ,
          (Submission.BoseGases.aP ℓ p.1 (Submission.BoseGases.aQ ℓ p.2 Φ) x) ^ 2 *
            Submission.BoseGases.wPairC ℓ (Submission.BoseGases.g2 v h) (x p.1) (x p.2))
      = ∑ i : Fin N, ∑ j : Fin N, (if j ≠ i then
          (∫ x in Submission.BoseGases.abox N ℓ,
            (Submission.BoseGases.aP ℓ j (Submission.BoseGases.aQ ℓ i Φ) x) ^ 2 *
              Submission.BoseGases.wPairC ℓ (Submission.BoseGases.g2 v h) (x j) (x i))
          else 0) := by
    have hsp := Submission.BoseGases.pairSet_sum_swap_split (N := N)
      (f := fun a b : Fin N => ∫ x in Submission.BoseGases.abox N ℓ,
          (Submission.BoseGases.aP ℓ a (Submission.BoseGases.aQ ℓ b Φ) x) ^ 2 *
            Submission.BoseGases.wPairC ℓ (Submission.BoseGases.g2 v h) (x a) (x b))
    simpa using hsp
  -- 4. the per-pair peel identity
  have hsum : (∑ i : Fin N, ∑ j : Fin N, (if j ≠ i then
          (∫ x in Submission.BoseGases.abox N ℓ,
            (Submission.BoseGases.aP ℓ j (Submission.BoseGases.aQ ℓ i Φ) x) ^ 2 *
              Submission.BoseGases.wPairC ℓ (Submission.BoseGases.g2 v h) (x j) (x i))
          else 0))
      = ∑ i : Fin N, ∑ j : Fin N, (if j ≠ i then
          ((ℓ ^ 3)⁻¹ * (∫ x in Submission.BoseGases.abox N ℓ,
            (Submission.BoseGases.aP ℓ j (Submission.BoseGases.aQ ℓ i Φ) x) ^ 2 *
              (Submission.BoseGases.w1Fibre ℓ
                (Submission.BoseGases.wPairC ℓ (Submission.BoseGases.g2 v h)) (x i))))
          else 0) := by
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    by_cases hji : j ≠ i
    · rw [if_pos hji, if_pos hji]
      exact q2lhs_closed_gen hℓ hv_nonneg hvrad hR hv_supp h hRℓ i j hji.symm hΦc
    · rw [if_neg hji, if_neg hji]
  -- 5. pull the constant `(ℓ³)⁻¹` out of the double sum
  have hconst : (∑ i : Fin N, ∑ j : Fin N, (if j ≠ i then
          ((ℓ ^ 3)⁻¹ * (∫ x in Submission.BoseGases.abox N ℓ,
            (Submission.BoseGases.aP ℓ j (Submission.BoseGases.aQ ℓ i Φ) x) ^ 2 *
              (Submission.BoseGases.w1Fibre ℓ
                (Submission.BoseGases.wPairC ℓ (Submission.BoseGases.g2 v h)) (x i))))
          else 0))
      = (ℓ ^ 3)⁻¹ * ∑ i : Fin N, ∑ j : Fin N, (if j ≠ i then
          (∫ x in Submission.BoseGases.abox N ℓ,
            (Submission.BoseGases.aP ℓ j (Submission.BoseGases.aQ ℓ i Φ) x) ^ 2
              * Submission.BoseGases.w1Fibre ℓ
                  (Submission.BoseGases.wPairC ℓ (Submission.BoseGases.g2 v h)) (x i))
          else 0) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    split_ifs <;> ring
  rw [hq, hsq, hre, hsum, hconst]

end Work.BoseBoxFock
