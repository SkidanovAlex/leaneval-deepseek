import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB1S.boxPIndSelfAdjoint
import Submission.Work.BoseFixB1S.boxPairQCount_eq
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

noncomputable section

open MeasureTheory
open scoped Real BigOperators ENNReal

namespace Work.BoseFixB1S

open Submission.BoseGases

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

/-- **Idempotence of the box projection** (pointwise): `Pᵢ(PᵢΨ) = PᵢΨ`. -/
theorem boxPInd_idempotent {N : ℕ} {ℓ volA : ℝ} (hℓ : 0 < ℓ) (hvol : 0 < volA)
    {A : Set E3} (hA : MeasurableSet A) (hvolA : volA = (MeasureTheory.volume A).toReal)
    (hAc : A ⊆ acube ℓ) (i : Fin N) (Ψ : X N → ℝ) (x : X N) :
    Work.UBBInputs8.boxPInd volA A i (Work.UBBInputs8.boxPInd volA A i Ψ) x
      = Work.UBBInputs8.boxPInd volA A i Ψ x := by
  have hupd : ∀ u : E3, Work.UBBInputs8.boxPInd volA A i Ψ (Function.update x i u)
      = (1 / volA) * (∫ z in A, Ψ (Function.update x i z))
        * A.indicator (fun _ => (1 : ℝ)) u := by
    intro u
    simp only [Work.UBBInputs8.boxPInd, Function.update_idem, Function.update_self]
  rw [show Work.UBBInputs8.boxPInd volA A i (Work.UBBInputs8.boxPInd volA A i Ψ) x
      = (1 / volA) * (∫ u in A, Work.UBBInputs8.boxPInd volA A i Ψ (Function.update x i u))
        * A.indicator (fun _ => (1 : ℝ)) (x i) from rfl]
  rw [show (∫ u in A, Work.UBBInputs8.boxPInd volA A i Ψ (Function.update x i u))
      = ∫ u in A, ((1 / volA) * (∫ z in A, Ψ (Function.update x i z))
          * A.indicator (fun _ => (1 : ℝ)) u) from
    MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hupd)]
  rw [MeasureTheory.integral_const_mul]
  have h1A : (∫ u in A, A.indicator (fun _ => (1 : ℝ)) u) = volA := by
    have hpt : ∀ᵐ u ∂(MeasureTheory.volume.restrict A),
        A.indicator (fun _ => (1 : ℝ)) u = (1 : ℝ) := by
      rw [MeasureTheory.ae_restrict_iff' hA]
      exact Filter.Eventually.of_forall (fun u hu => Set.indicator_of_mem hu _)
    rw [MeasureTheory.integral_congr_ae hpt, MeasureTheory.setIntegral_const, smul_eq_mul,
      mul_one]
    exact hvolA.symm
  rw [h1A]
  rw [show Work.UBBInputs8.boxPInd volA A i Ψ x
      = (1 / volA) * (∫ z in A, Ψ (Function.update x i z))
        * A.indicator (fun _ => (1 : ℝ)) (x i) from rfl]
  have hvolne : volA ≠ 0 := ne_of_gt hvol
  field_simp

/-- **The slot-`j` box indicator may be moved across `Pᵢ` inside the square** (`j ≠ i`):
`∫ 1_A(xⱼ)·(PᵢΦ)² = ∫ 1_A(xⱼ)·(PᵢΦ)·Φ`. -/
theorem boxPInd_indicator_sq_mul {N : ℕ} {ℓ volA : ℝ} (hℓ : 0 < ℓ) (hvol : 0 < volA)
    {A : Set E3} (hA : MeasurableSet A) (hvolA : volA = (MeasureTheory.volume A).toReal)
    (hAc : A ⊆ acube ℓ) {i j : Fin N} (hij : i ≠ j) {Φ : X N → ℝ} (hΦc : Continuous Φ) :
    (∫ x in abox N ℓ, A.indicator (fun _ => (1 : ℝ)) (x j)
        * (Work.UBBInputs8.boxPInd volA A i Φ x) ^ 2)
      = ∫ x in abox N ℓ, A.indicator (fun _ => (1 : ℝ)) (x j)
          * Work.UBBInputs8.boxPInd volA A i Φ x * Φ x := by
  obtain ⟨C, _hC0, hCb⟩ := exists_abox_bound (N := N) hℓ hΦc
  have hΦm : Measurable Φ := hΦc.measurable
  have hσm : Measurable (fun x : X N => A.indicator (fun _ => (1 : ℝ)) (x j)) :=
    (measurable_const.indicator hA).comp (measurable_pi_apply j)
  have hσb : ∀ x : X N, |A.indicator (fun _ => (1 : ℝ)) (x j)| ≤ 1 := by
    intro x
    by_cases hx : x j ∈ A
    · rw [Set.indicator_of_mem hx]; norm_num
    · rw [Set.indicator_of_notMem hx]; norm_num
  have hσΦb : ∀ x ∈ abox N ℓ,
      |A.indicator (fun _ => (1 : ℝ)) (x j) * Φ x| ≤ C := by
    intro x hx
    rw [abs_mul]
    calc |A.indicator (fun _ => (1 : ℝ)) (x j)| * |Φ x| ≤ 1 * C :=
          mul_le_mul (hσb x) (hCb x hx) (abs_nonneg _) zero_le_one
      _ = C := one_mul C
  have hPm : Measurable (Work.UBBInputs8.boxPInd volA A i
      (fun y => A.indicator (fun _ => (1 : ℝ)) (y j) * Φ y)) :=
    measurable_boxPInd volA A hA i (hσm.mul hΦm)
  have hPb : ∀ x ∈ abox N ℓ,
      |Work.UBBInputs8.boxPInd volA A i
        (fun y => A.indicator (fun _ => (1 : ℝ)) (y j) * Φ y) x| ≤ C :=
    abs_boxPInd_le hℓ hvol hA hvolA hAc i hσΦb
  -- self-adjointness of `Pᵢ` with the second argument `Pᵢ(σⱼΦ)`
  have hSA : (∫ x in abox N ℓ, Work.UBBInputs8.boxPInd volA A i Φ x
        * Work.UBBInputs8.boxPInd volA A i
            (fun y => A.indicator (fun _ => (1 : ℝ)) (y j) * Φ y) x)
      = ∫ x in abox N ℓ, Φ x * Work.UBBInputs8.boxPInd volA A i
          (Work.UBBInputs8.boxPInd volA A i
            (fun y => A.indicator (fun _ => (1 : ℝ)) (y j) * Φ y)) x :=
    boxPIndSelfAdjoint (N := N) (ℓ := ℓ) (volA := volA) hℓ hvol hA hvolA hAc i
      hΦm hCb hPm hPb
  -- step 1: `σⱼ·a² = a·(Pᵢ(σⱼΦ))`
  have h1 : (∫ x in abox N ℓ, A.indicator (fun _ => (1 : ℝ)) (x j)
        * (Work.UBBInputs8.boxPInd volA A i Φ x) ^ 2)
      = ∫ x in abox N ℓ, Work.UBBInputs8.boxPInd volA A i Φ x
          * Work.UBBInputs8.boxPInd volA A i
              (fun y => A.indicator (fun _ => (1 : ℝ)) (y j) * Φ y) x := by
    apply MeasureTheory.integral_congr_ae
    filter_upwards with x
    have h := congrFun (boxPInd_indicator_mul (volA := volA) (A := A) hij Φ) x
    rw [h]
    ring
  -- step 3: idempotence
  have h3 : (∫ x in abox N ℓ, Φ x * Work.UBBInputs8.boxPInd volA A i
          (Work.UBBInputs8.boxPInd volA A i
            (fun y => A.indicator (fun _ => (1 : ℝ)) (y j) * Φ y)) x)
      = ∫ x in abox N ℓ, Φ x * Work.UBBInputs8.boxPInd volA A i
          (fun y => A.indicator (fun _ => (1 : ℝ)) (y j) * Φ y) x := by
    apply MeasureTheory.integral_congr_ae
    filter_upwards with x
    rw [boxPInd_idempotent hℓ hvol hA hvolA hAc i _ x]
  -- step 4: `Φ·(Pᵢ(σⱼΦ)) = σⱼ·a·Φ`
  have h4 : (∫ x in abox N ℓ, Φ x * Work.UBBInputs8.boxPInd volA A i
          (fun y => A.indicator (fun _ => (1 : ℝ)) (y j) * Φ y) x)
      = ∫ x in abox N ℓ, A.indicator (fun _ => (1 : ℝ)) (x j)
          * Work.UBBInputs8.boxPInd volA A i Φ x * Φ x := by
    apply MeasureTheory.integral_congr_ae
    filter_upwards with x
    have h := congrFun (boxPInd_indicator_mul (volA := volA) (A := A) hij Φ) x
    rw [h]
    ring
  rw [h1, hSA, h3, h4]

end Work.BoseFixB1S
