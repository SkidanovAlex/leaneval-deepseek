import ChallengeDeps
import Submission.Work.BoseFixB1S.flatBranchDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseFixB1S

open MeasureTheory
open scoped BigOperators

set_option maxHeartbeats 800000

/-- **The box flat count of a `Q = 0` state is `n‖Φ‖²`.**  `mfS = Σ_i∫(P_{B(u),i}Φ)²` and
`mfQ = Σ_i∫(Q_{B(u),i}Φ)² = 0`, so the Parseval splitting
`Work.BoseFixB1S.boxC1_add_cnPlus` gives `mfS = Σ_i∫1_{B(u)}(x_i)Φ²`, and the support hypothesis
`mfSupp` (`Φ x ≠ 0 ⟹ ∀i, x_i ∈ B(u)`) gives `1_{B(u)}(x_i)Φ² = Φ²` a.e. for each slot, hence
`mfS = n·mfI`.
IMPORTANT: do NOT use `Work.BoseFixB1S.boxSupport_count_eq`
(`Submission/Work/BoseFixB1S/boxSupport_count_eq.lean`) — it is still a skeleton carrying a
`sorry`, so anything depending on it fails the axiom check.  Prove the support collapse directly
(`integral_congr_ae` with the a.e. identity `1_{B(u)}(x i)·Φ² = Φ²` read off `hsupp`, then
`Finset.sum_const`). -/
theorem mf_boxFlatCount_eq {v : EuclideanSpace ℝ (Fin 3) → ℝ} {μ : ℝ} {n : ℕ}
    {Φ : Submission.BoseGases.X n → ℝ} {u : EuclideanSpace ℝ (Fin 3)}
    (hℓ : 0 < Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) (hΦc : Continuous Φ)
    (hsupp : Work.BoseFixB1S.mfSupp v μ n Φ u) (hQ : Work.BoseFixB1S.mfQ v μ n Φ u = 0) :
    Work.BoseFixB1S.mfS v μ n Φ u = (n : ℝ) * Work.BoseFixB1S.mfI v μ n Φ := by
  -- The `Q = 0` hypothesis, in the `cnPlusBoxInd` form of the Parseval identity.
  have hQ' : Work.UBBInputs8.cnPlusBoxInd (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
      (Submission.BoseGases.dlBox (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
        (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
      (Work.SmallBoxSliding.boxMass (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
        (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u) Φ = 0 := hQ
  -- The Parseval splitting: flat count `+` excited count `=` box mass.
  have hC1 := boxC1_add_cnPlus (N := n)
    (ℓ := Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
    (d := (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d) hℓ u hΦc
  -- Support collapse, slot by slot: the indicator integrand is `Φ²` in the box.
  have hterm : ∀ i : Fin n,
      (∫ x in Submission.BoseGases.abox n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)),
        (Submission.BoseGases.dlBox (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
            (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u).indicator
              (fun _ => (1 : ℝ)) (x i) * (Φ x) ^ 2)
        = Work.BoseFixB1S.mfI v μ n Φ := by
    intro i
    rw [Work.BoseFixB1S.mfI]
    refine integral_congr_ae ?_
    filter_upwards [hsupp] with x hx
    by_cases hmem : x i ∈ Submission.BoseGases.dlBox
        (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
        (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u
    · rw [Set.indicator_of_mem hmem, one_mul]
    · -- off the box the indicator vanishes and `mfSupp` forces `Φ x = 0`
      have hΦ : Φ x = 0 := by
        by_contra hc
        exact hmem (hx hc i)
      rw [Set.indicator_of_notMem hmem, hΦ]
      ring
  -- The box mass is `n · ‖Φ‖²`.
  have hR : (∑ i : Fin n,
        ∫ x in Submission.BoseGases.abox n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)),
          (Submission.BoseGases.dlBox (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
              (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u).indicator
                (fun _ => (1 : ℝ)) (x i) * (Φ x) ^ 2)
      = (n : ℝ) * Work.BoseFixB1S.mfI v μ n Φ := by
    rw [Finset.sum_congr rfl (fun i _ => hterm i), Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
  -- Hence the flat count is the box mass, since the excited count vanishes.
  have hS : (∑ i : Fin n,
        ∫ x in Submission.BoseGases.abox n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)),
          (Work.UBBInputs8.boxPInd
            (Work.SmallBoxSliding.boxMass (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
              (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
            (Submission.BoseGases.dlBox (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
              (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u) i Φ x) ^ 2)
      = (n : ℝ) * Work.BoseFixB1S.mfI v μ n Φ := by
    linarith [hC1, hR, hQ']
  exact hS

end Work.BoseFixB1S
