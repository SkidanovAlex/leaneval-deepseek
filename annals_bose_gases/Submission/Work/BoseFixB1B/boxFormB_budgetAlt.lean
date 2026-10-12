import ChallengeDeps
import Submission.Work.BoseFixB1B.isLowB_chemBoundAlt
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1B.boxFormB_budgetAlt`

The **trade-off budget** for a low box state.  `IsLowB` says

`wordB = boxFormB ≤ ℓ³·Theta (a v) J μ·‖Φ‖²`,  `ℓ = sideAt μ (a v)`,

with `Theta A J ρ = −4πρ²A(1 − J√(ρA³))` and `wordB = boxFormB`.  The splitting
`boxFormB = kinFormB + chemPartB + pairPartB` (`boxFormB_eq_parts_of_integrable`) together with the
identity `chemPartB = −μ·M` for the flat one-body mass

`M = ∫_{abox n ℓ} Φ²·(Σᵢ ∫_y wLoc ℓ (g₀ v h) 0 (xᵢ) y)`

turns the hypothesis into

`kinFormB + pairPartB − μ·M ≤ ℓ³·Theta (a v) J μ·‖Φ‖²`,
i.e. `kinFormB + pairPartB + 4πμ²(a v)ℓ³(1 − J√(μ(a v)³))‖Φ‖² ≤ μM`,

which is exactly the statement.  No sign hypothesis on `μ`, on `a v`, or on `1 − J√(μ(a v)³)` is
needed: the inequality direction is automatic.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped Topology Real BigOperators ENNReal

namespace Work.BoseFixB1B

open _root_.BoseGases Submission.BoseGases Work.BoseBoxFix Work.BoseBox Work.UBB

set_option autoImplicit false
set_option linter.unusedVariables false

local notation "E3" => EuclideanSpace ℝ (Fin 3)

theorem boxFormB_budgetAlt {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v) (hv : 0 ≤ v) {J μ : ℝ}
    (hJ : 0 ≤ J) {n : ℕ} {Φ : Work.BoseKinLoc.BoxState n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))}
    (hL : Work.BoseBoxFix.IsLowB v h J μ n (Φ : Submission.BoseGases.X n → ℝ))
    (hA : MeasureTheory.IntegrableOn (fun x : Submission.BoseGases.X n => ((Φ : Submission.BoseGases.X n → ℝ) x) ^ 2 *
      (-μ * (∑ i : Fin n, ∫ y : EuclideanSpace ℝ (Fin 3),
        Submission.BoseGases.wLoc (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) (Submission.BoseGases.g0 v h) 0 (x i) y)))
      (Submission.BoseGases.abox n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))))
    (hB : MeasureTheory.IntegrableOn (fun x : Submission.BoseGases.X n => ((Φ : Submission.BoseGases.X n → ℝ) x) ^ 2 *
      (∑ ij : {ij : Fin n × Fin n | ij.1 < ij.2},
        Submission.BoseGases.wLoc (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) v 0 (x ij.1.1) (x ij.1.2)))
      (Submission.BoseGases.abox n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)))) :
    Work.BoseKinLoc.kinFormB n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d
        (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).eT
        (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).b (Φ : Submission.BoseGases.X n → ℝ)
      + Work.BoseKinLoc.pairPartB n v (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) (Φ : Submission.BoseGases.X n → ℝ)
      + 4 * Real.pi * μ ^ 2 * (_root_.BoseGases.a v) * Work.BoseBox.sideAt μ (_root_.BoseGases.a v) ^ 3
          * (1 - J * Real.sqrt (μ * (_root_.BoseGases.a v) ^ 3))
          * (Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ))
      ≤ μ * (∫ x in Submission.BoseGases.abox n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)),
          ((Φ : Submission.BoseGases.X n → ℝ) x) ^ 2 *
            (∑ i : Fin n, ∫ y : EuclideanSpace ℝ (Fin 3),
              Submission.BoseGases.wLoc (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                (Submission.BoseGases.g0 v h) 0 (x i) y)) := by
  let ℓ : ℝ := Work.BoseBox.sideAt μ (_root_.BoseGases.a v)
  let P : Work.BoseBox.FSParams := Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)
  -- the splitting of the box word
  have hsplit : Work.BoseKinLoc.boxFormB n v (Submission.BoseGases.g0 v h) ℓ μ P.d P.s P.eT P.b
        (Φ : Submission.BoseGases.X n → ℝ)
      = Work.BoseKinLoc.kinFormB n ℓ P.d P.s P.eT P.b (Φ : Submission.BoseGases.X n → ℝ)
        + Work.BoseKinLoc.chemPartB n (Submission.BoseGases.g0 v h) ℓ μ (Φ : Submission.BoseGases.X n → ℝ)
        + Work.BoseKinLoc.pairPartB n v ℓ (Φ : Submission.BoseGases.X n → ℝ) :=
    Work.BoseKinLoc.Word.boxFormB_eq_parts_of_integrable (Φ : Submission.BoseGases.X n → ℝ) hA hB
  have hL' : Work.BoseKinLoc.boxFormB n v (Submission.BoseGases.g0 v h) ℓ μ P.d P.s P.eT P.b
        (Φ : Submission.BoseGases.X n → ℝ)
      ≤ ℓ ^ 3 * Work.UBB.Theta (_root_.BoseGases.a v) J μ *
          Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ) := by
    simp only [Work.BoseBoxFix.IsLowB, Work.BoseBoxFix.wordB, Work.BoseBoxFix.normB] at hL
    exact hL
  -- `chemPartB = -μ·M`
  have hchem_eq : Work.BoseKinLoc.chemPartB n (Submission.BoseGases.g0 v h) ℓ μ
        (Φ : Submission.BoseGases.X n → ℝ)
      = -μ * (∫ x in Submission.BoseGases.abox n ℓ,
          ((Φ : Submission.BoseGases.X n → ℝ) x) ^ 2 *
            (∑ i : Fin n, ∫ y : E3,
              Submission.BoseGases.wLoc ℓ (Submission.BoseGases.g0 v h) 0 (x i) y)) := by
    have hfun : (fun x : Submission.BoseGases.X n => ((Φ : Submission.BoseGases.X n → ℝ) x) ^ 2 *
          (-μ * (∑ i : Fin n, ∫ y : E3,
            Submission.BoseGases.wLoc ℓ (Submission.BoseGases.g0 v h) 0 (x i) y)))
        = fun x : Submission.BoseGases.X n => -μ * (((Φ : Submission.BoseGases.X n → ℝ) x) ^ 2 *
            (∑ i : Fin n, ∫ y : E3,
              Submission.BoseGases.wLoc ℓ (Submission.BoseGases.g0 v h) 0 (x i) y)) := by
      funext x; ring
    unfold Work.BoseKinLoc.chemPartB
    rw [hfun, MeasureTheory.integral_const_mul]
  -- `kinFormB + pairPartB ≤ ℓ³·Theta·‖Φ‖² + μ·M`
  have hkey : Work.BoseKinLoc.kinFormB n ℓ P.d P.s P.eT P.b (Φ : Submission.BoseGases.X n → ℝ)
        + Work.BoseKinLoc.pairPartB n v ℓ (Φ : Submission.BoseGases.X n → ℝ)
      ≤ ℓ ^ 3 * Work.UBB.Theta (_root_.BoseGases.a v) J μ *
          Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ)
        + μ * (∫ x in Submission.BoseGases.abox n ℓ,
            ((Φ : Submission.BoseGases.X n → ℝ) x) ^ 2 *
              (∑ i : Fin n, ∫ y : E3,
                Submission.BoseGases.wLoc ℓ (Submission.BoseGases.g0 v h) 0 (x i) y)) := by
    rw [hchem_eq] at hsplit
    linarith [hsplit, hL']
  -- `-ℓ³·Theta·‖Φ‖² = 4πμ²(a v)ℓ³(1 - J√(μ(a v)³))·‖Φ‖²`
  have hTheta : -(ℓ ^ 3 * Work.UBB.Theta (_root_.BoseGases.a v) J μ *
        Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ))
      = 4 * Real.pi * μ ^ 2 * (_root_.BoseGases.a v) * ℓ ^ 3
        * (1 - J * Real.sqrt (μ * (_root_.BoseGases.a v) ^ 3))
        * (Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ)) := by
    unfold Work.UBB.Theta
    ring
  have hgoal : Work.BoseKinLoc.kinFormB n ℓ P.d P.s P.eT P.b (Φ : Submission.BoseGases.X n → ℝ)
        + Work.BoseKinLoc.pairPartB n v ℓ (Φ : Submission.BoseGases.X n → ℝ)
        + 4 * Real.pi * μ ^ 2 * (_root_.BoseGases.a v) * ℓ ^ 3
            * (1 - J * Real.sqrt (μ * (_root_.BoseGases.a v) ^ 3))
            * (Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ))
      ≤ μ * (∫ x in Submission.BoseGases.abox n ℓ,
          ((Φ : Submission.BoseGases.X n → ℝ) x) ^ 2 *
            (∑ i : Fin n, ∫ y : E3,
              Submission.BoseGases.wLoc ℓ (Submission.BoseGases.g0 v h) 0 (x i) y)) := by
    linarith [hkey, hTheta]
  exact hgoal

end Work.BoseFixB1B
