import ChallengeDeps
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Submission.Work.BoseFixB1.RungDefs
import Submission.Work.BoseFixB1S.boxM1Info
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

noncomputable section

open MeasureTheory
open scoped Real BigOperators ENNReal

namespace Work.BoseFixB1

open _root_.BoseGases Submission.BoseGases

set_option autoImplicit false

/-- The sliding box `A = dlBox ℓ d u`. -/
abbrev q1Box (ℓ d : ℝ) (u : E3) : Set E3 := Submission.BoseGases.dlBox ℓ d u

/-- The box volume `V = boxMass ℓ d u = |dlBox ℓ d u|`. -/
noncomputable def q1Vol (ℓ d : ℝ) (u : E3) : ℝ := Work.SmallBoxSliding.boxMass ℓ d u

/-- `P_i = boxPInd V A i` at the sliding box. -/
noncomputable def q1P {N : ℕ} (ℓ d : ℝ) (u : E3) (i : Fin N) (Ψ : X N → ℝ) : X N → ℝ :=
  Work.UBBInputs8.boxPInd (q1Vol ℓ d u) (q1Box ℓ d u) i Ψ

/-- `Q_i = boxQInd V A i` at the sliding box. -/
noncomputable def q1Q {N : ℕ} (ℓ d : ℝ) (u : E3) (i : Fin N) (Ψ : X N → ℝ) : X N → ℝ :=
  Work.UBBInputs8.boxQInd (q1Vol ℓ d u) (q1Box ℓ d u) i Ψ

/-- The localised `g₀`-kernel `w₁ = wSmall1Pair h M ℓ d u`. -/
noncomputable def q1W1 {v : E3 → ℝ} (h : Work.UBB.ScatSol v) (M : ℕ) (ℓ d : ℝ) (u : E3) :
    E3 → E3 → ℝ :=
  Submission.BoseGases.wSmall1Pair h M ℓ d u

/-- The localised `g₂`-kernel `w₂ = wSmallPair M ℓ d u (g₂ v h)`. -/
noncomputable def q1W2 {v : E3 → ℝ} (h : Work.UBB.ScatSol v) (M : ℕ) (ℓ d : ℝ) (u : E3) :
    E3 → E3 → ℝ :=
  Submission.BoseGases.wSmallPair M ℓ d u (Submission.BoseGases.g2 v h)

/-- `fib₁(z) = ∫_{acube ℓ} w₁(z,y) dy`. -/
noncomputable def q1Fib1 {v : E3 → ℝ} (h : Work.UBB.ScatSol v) (M : ℕ) (ℓ d : ℝ) (u : E3) :
    E3 → ℝ :=
  Submission.BoseGases.w1Fibre ℓ (Submission.BoseGases.wSmall1Pair h M ℓ d u)

/-- `fib₂(z) = ∫_{acube ℓ} w₂(z,y) dy`. -/
noncomputable def q1Fib2 {v : E3 → ℝ} (h : Work.UBB.ScatSol v) (M : ℕ) (ℓ d : ℝ) (u : E3) :
    E3 → ℝ :=
  Submission.BoseGases.w1Fibre ℓ (Submission.BoseGases.wSmallPair M ℓ d u (Submission.BoseGases.g2 v h))

/-- The pair sum of FS `eq:Q1n0`'s first line (before the `2`):
`Σ_{p∈pairSet N} ∫ (P_{p.1}Q_{p.2}Φ)(P_{p.1}P_{p.2}Φ) W(x_{p.1},x_{p.2})`. -/
noncomputable def q1PairSum {N : ℕ} (V ℓ : ℝ) (A : Set E3) (W : E3 → E3 → ℝ)
    (Φ : X N → ℝ) : ℝ :=
  ∑ p ∈ Submission.BoseGases.pairSet N, ∫ x in abox N ℓ,
    (Work.UBBInputs8.boxPInd V A p.1 (Work.UBBInputs8.boxQInd V A p.2 Φ) x)
      * (Work.UBBInputs8.boxPInd V A p.1 (Work.UBBInputs8.boxPInd V A p.2 Φ) x)
      * W (x p.1) (x p.2)

/-- The sandwich sum `Σ_i ∫ (Q_iF) fib(x_i) (P_iΦ)` (the `n₀`-form of the pair part). -/
noncomputable def q1SandSum {N : ℕ} (V ℓ : ℝ) (A : Set E3) (fib : E3 → ℝ)
    (Φ : X N → ℝ) : ℝ :=
  ∑ i : Fin N, ∫ x in abox N ℓ,
    (Work.UBBInputs8.boxQInd V A i (rungF V A Φ) x) * fib (x i)
      * (Work.UBBInputs8.boxPInd V A i Φ x)

/-! ## The structural facts about the sliding box -/

lemma q1Box_measurableSet (ℓ d : ℝ) (u : E3) : MeasurableSet (q1Box ℓ d u) :=
  Work.SmallBoxSliding.measurableSet_dlBox ℓ d u

lemma q1Box_subset_acube (ℓ d : ℝ) (u : E3) : q1Box ℓ d u ⊆ Submission.BoseGases.acube ℓ :=
  Work.SmallBoxSliding.dlBox_subset_acube ℓ d u

lemma q1Vol_eq_real (ℓ d : ℝ) (u : E3) :
    q1Vol ℓ d u = (volume : Measure E3).real (q1Box ℓ d u) :=
  Work.SmallBoxSliding.boxMass_eq_measureReal ℓ d u

lemma q1Vol_nonneg (ℓ d : ℝ) (u : E3) : 0 ≤ q1Vol ℓ d u := by
  have h := q1Vol_eq_real ℓ d u
  rw [h]
  exact MeasureTheory.measureReal_nonneg

/-! ## Kernel facts for the `g₂`-kernel -/

/-- Symmetry of the localised `g₂`-kernel (`g₂` is even). -/
lemma q1W2_symm {v : E3 → ℝ} (h : Work.UBB.ScatSol v) {M : ℕ} (hM : 1 ≤ M)
    (hvrad : _root_.BoseGases.IsRadial v) {ℓ d : ℝ} (u : E3) (x y : E3) :
    q1W2 h M ℓ d u x y = q1W2 h M ℓ d u y x := by
  simpa [q1W2] using
    (Submission.BoseGases.wSmallPair_symm (M := M) hM u
      (Submission.BoseGases.g2_even hvrad h) x y)

/-- The localised `g₂`-kernel vanishes when a slot leaves the sliding box. -/
lemma q1W2_eq_zero_of_notMem {v : E3 → ℝ} (h : Work.UBB.ScatSol v) {M : ℕ} (hM : 1 ≤ M)
    {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d) (u : E3) {x y : E3}
    (hx : x ∉ q1Box ℓ d u ∨ y ∉ q1Box ℓ d u) : q1W2 h M ℓ d u x y = 0 := by
  simpa [q1W2, q1Box] using
    (Work.BoseFixB1S.wSmallPair_eq_zero_of_notMem_dlBox (M := M) hM hℓ hd u
      (f := Submission.BoseGases.g2 v h) hx)

/-- **First-slot fibre of the `g₂`-kernel**: `∫_{acube ℓ} w₂(y,z) dy = fib₂(z)`. -/
lemma q1W2_fibre_first {v : E3 → ℝ} (h : Work.UBB.ScatSol v) {M : ℕ} (hM : 1 ≤ M)
    (hvrad : _root_.BoseGases.IsRadial v) {ℓ d : ℝ} (u : E3) (z : E3) :
    (∫ y in Submission.BoseGases.acube ℓ, q1W2 h M ℓ d u y z) = q1Fib2 h M ℓ d u z := by
  have hsym : ∀ y : E3, q1W2 h M ℓ d u y z = q1W2 h M ℓ d u z y := fun y =>
    q1W2_symm h hM hvrad u y z
  calc (∫ y in Submission.BoseGases.acube ℓ, q1W2 h M ℓ d u y z)
      = ∫ y in Submission.BoseGases.acube ℓ, q1W2 h M ℓ d u z y := by
        apply integral_congr_ae
        exact ae_of_all _ hsym
    _ = q1Fib2 h M ℓ d u z := by
        simp [q1Fib2, q1W2, Submission.BoseGases.w1Fibre]

/-- The same fibre identity with the box indicator inserted in the first slot. -/
lemma q1W2_fibre_first_indicator {v : E3 → ℝ} (h : Work.UBB.ScatSol v) {M : ℕ} (hM : 1 ≤ M)
    (hvrad : _root_.BoseGases.IsRadial v) {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d) (u : E3)
    (z : E3) :
    (∫ y in Submission.BoseGases.acube ℓ,
        (q1Box ℓ d u).indicator (fun _ => (1 : ℝ)) y * q1W2 h M ℓ d u y z)
      = q1Fib2 h M ℓ d u z := by
  have hpt : ∀ y : E3, (q1Box ℓ d u).indicator (fun _ => (1 : ℝ)) y * q1W2 h M ℓ d u y z
      = q1W2 h M ℓ d u y z := by
    intro y
    by_cases hy : y ∈ q1Box ℓ d u
    · simp [Set.indicator_of_mem hy]
    · have hz : q1W2 h M ℓ d u y z = 0 :=
        q1W2_eq_zero_of_notMem h hM hℓ hd u (Or.inl hy)
      simp [Set.indicator_of_notMem hy, hz]
  rw [show (∫ y in Submission.BoseGases.acube ℓ,
        (q1Box ℓ d u).indicator (fun _ => (1 : ℝ)) y * q1W2 h M ℓ d u y z)
      = ∫ y in Submission.BoseGases.acube ℓ, q1W2 h M ℓ d u y z from by
        apply integral_congr_ae
        exact ae_of_all _ hpt]
  exact q1W2_fibre_first h hM hvrad u z

/-- The box indicator integrates to the box mass over the analysis cube. -/
lemma q1_indicator_acube {ℓ d : ℝ} (hℓ : 0 < ℓ) (u : E3) :
    (∫ y in Submission.BoseGases.acube ℓ,
        (q1Box ℓ d u).indicator (fun _ => (1 : ℝ)) y) = q1Vol ℓ d u := by
  have hEq : (∫ y in Submission.BoseGases.acube ℓ,
        (q1Box ℓ d u).indicator (fun _ => (1 : ℝ)) y)
      = ∫ y : E3, (q1Box ℓ d u).indicator (fun _ => (1 : ℝ)) y := by
    rw [← MeasureTheory.integral_indicator
      (Submission.BoseGases.acube_measurable ℓ)]
    apply integral_congr_ae
    refine ae_of_all _ (fun y => ?_)
    by_cases hy : y ∈ Submission.BoseGases.acube ℓ
    · simp [Set.indicator_of_mem hy]
    · have hA : y ∉ q1Box ℓ d u := fun h => hy (q1Box_subset_acube ℓ d u h)
      simp [Set.indicator_of_notMem hy, Set.indicator_of_notMem hA]
  rw [hEq]
  simp [q1Vol, Work.SmallBoxSliding.boxMass, Work.SmallBoxSliding.boxInd, q1Box]

end Work.BoseFixB1
