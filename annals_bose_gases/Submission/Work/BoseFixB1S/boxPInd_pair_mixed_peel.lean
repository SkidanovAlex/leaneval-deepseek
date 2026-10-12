import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB1S.BoxPIndFlat
import Submission.Work.BoseFixB1S.BoxQIndCore
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

set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

/-! ## 1. Idempotence of the FS box projection -/

/-- `Pᵢ · Pᵢ = Pᵢ` for the FS box projection `Pᵢ = boxPInd volA A i` (`A ⊆ acube ℓ` of measure
`volA`), as an identity of functions on the whole configuration space. -/
private theorem boxPInd_idem_gen {N : ℕ} {ℓ volA : ℝ} (hℓ : 0 < ℓ) (hvol : 0 < volA)
    {A : Set E3} (hA : MeasurableSet A) (hvolA : volA = (MeasureTheory.volume A).toReal)
    (hAc : A ⊆ acube ℓ) (i : Fin N) (Ψ : X N → ℝ) :
    Work.UBBInputs8.boxPInd volA A i (Work.UBBInputs8.boxPInd volA A i Ψ)
      = Work.UBBInputs8.boxPInd volA A i Ψ := by
  funext x
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

/-! ## 2. Self-adjointness of the FS box projection -/

/-- `Pᵢ = boxPInd volA A i` is self-adjoint on `L²(abox N ℓ)`: for measurable `Φ`, `Ψ` bounded
on the box,

    `∫_{abox N ℓ} (PᵢΦ)·Ψ = ∫_{abox N ℓ} Φ·(PᵢΨ)`. -/
private theorem boxPInd_selfadj_gen {N : ℕ} {ℓ volA : ℝ} (hℓ : 0 < ℓ) (hvol : 0 < volA)
    {A : Set E3} (hA : MeasurableSet A) (hvolA : volA = (MeasureTheory.volume A).toReal)
    (hAc : A ⊆ acube ℓ) (i : Fin N) {Φ Ψ : X N → ℝ}
    (hΦm : Measurable Φ) {CΦ : ℝ} (hΦb : ∀ x ∈ abox N ℓ, |Φ x| ≤ CΦ)
    (hΨm : Measurable Ψ) {CΨ : ℝ} (hΨb : ∀ x ∈ abox N ℓ, |Ψ x| ≤ CΨ) :
    (∫ x in abox N ℓ, Work.UBBInputs8.boxPInd volA A i Φ x * Ψ x)
      = ∫ x in abox N ℓ, Φ x * Work.UBBInputs8.boxPInd volA A i Ψ x := by
  have hI1 : IntegrableOn (fun x : X N => Work.UBBInputs8.boxPInd volA A i Ψ x * Φ x)
      (abox N ℓ) MeasureTheory.volume :=
    integrableOn_mul_of_bound hℓ (measurable_boxPInd volA A hA i hΨm) hΦm
      (abs_boxPInd_le hℓ hvol hA hvolA hAc i hΨb) hΦb
  have hI2 : IntegrableOn (fun x : X N => Work.UBBInputs8.boxPInd volA A i Φ x * Ψ x)
      (abox N ℓ) MeasureTheory.volume :=
    integrableOn_mul_of_bound hℓ (measurable_boxPInd volA A hA i hΦm) hΨm
      (abs_boxPInd_le hℓ hvol hA hvolA hAc i hΦb) hΨb
  cases N with
  | zero => exact absurd i.isLt (Nat.not_lt_zero _)
  | succ n =>
    have hP1 := abox_integral_peel (i := i)
      (F := fun x : X (n + 1) => Work.UBBInputs8.boxPInd volA A i Φ x * Ψ x) hI2
    have hP2 := abox_integral_peel (i := i)
      (F := fun x : X (n + 1) => Φ x * Work.UBBInputs8.boxPInd volA A i Ψ x)
      (by simpa only [mul_comm] using hI1)
    have hpoint : ∀ r : X n,
        (∫ y in acube ℓ,
            Work.UBBInputs8.boxPInd volA A i Φ (kcInsN n i (y, r)) * Ψ (kcInsN n i (y, r)))
          = ∫ y in acube ℓ,
            Φ (kcInsN n i (y, r)) * Work.UBBInputs8.boxPInd volA A i Ψ (kcInsN n i (y, r)) := by
      intro r
      have hL : (∫ y in acube ℓ,
            Work.UBBInputs8.boxPInd volA A i Φ (kcInsN n i (y, r)) * Ψ (kcInsN n i (y, r)))
          = (1 / volA) * (∫ z in A, Φ (kcInsN n i (z, r)))
            * (∫ z in A, Ψ (kcInsN n i (z, r))) := by
        have hcongr : (∫ y in acube ℓ,
              Work.UBBInputs8.boxPInd volA A i Φ (kcInsN n i (y, r)) * Ψ (kcInsN n i (y, r)))
            = ∫ y in acube ℓ, ((1 / volA) * (∫ z in A, Φ (kcInsN n i (z, r))))
                * (A.indicator (fun _ => (1 : ℝ)) y * Ψ (kcInsN n i (y, r))) := by
          apply MeasureTheory.integral_congr_ae
          filter_upwards with y
          rw [boxPInd_kcInsN]
          ring
        rw [hcongr, MeasureTheory.integral_const_mul,
          setIntegral_indicator_one_mul hA hAc (fun z : E3 => Ψ (kcInsN n i (z, r)))]
        try ring
      have hR : (∫ y in acube ℓ,
            Φ (kcInsN n i (y, r)) * Work.UBBInputs8.boxPInd volA A i Ψ (kcInsN n i (y, r)))
          = (1 / volA) * (∫ z in A, Φ (kcInsN n i (z, r)))
            * (∫ z in A, Ψ (kcInsN n i (z, r))) := by
        have hcongr : (∫ y in acube ℓ,
              Φ (kcInsN n i (y, r)) * Work.UBBInputs8.boxPInd volA A i Ψ (kcInsN n i (y, r)))
            = ∫ y in acube ℓ, ((1 / volA) * (∫ z in A, Ψ (kcInsN n i (z, r))))
                * (A.indicator (fun _ => (1 : ℝ)) y * Φ (kcInsN n i (y, r))) := by
          apply MeasureTheory.integral_congr_ae
          filter_upwards with y
          rw [boxPInd_kcInsN]
          ring
        rw [hcongr, MeasureTheory.integral_const_mul,
          setIntegral_indicator_one_mul hA hAc (fun z : E3 => Φ (kcInsN n i (z, r)))]
        ring
      rw [hL, hR]
    calc
      (∫ x in abox (n + 1) ℓ, Work.UBBInputs8.boxPInd volA A i Φ x * Ψ x)
          = ∫ r : X n, (∫ y in acube ℓ,
              Work.UBBInputs8.boxPInd volA A i Φ (kcInsN n i (y, r)) * Ψ (kcInsN n i (y, r)))
            ∂((MeasureTheory.volume : Measure (X n)).restrict (abox n ℓ)) := hP1
      _ = ∫ r : X n, (∫ y in acube ℓ,
              Φ (kcInsN n i (y, r)) * Work.UBBInputs8.boxPInd volA A i Ψ (kcInsN n i (y, r)))
            ∂((MeasureTheory.volume : Measure (X n)).restrict (abox n ℓ)) := by
            apply MeasureTheory.integral_congr_ae
            filter_upwards with r
            exact hpoint r
      _ = (∫ x in abox (n + 1) ℓ, Φ x * Work.UBBInputs8.boxPInd volA A i Ψ x) := hP2.symm

/-! ## 3. The mixed pair peel -/

theorem boxPInd_pair_mixed_peel {N : ℕ} {ℓ volA : ℝ} (hℓ : 0 < ℓ) (hvol : 0 < volA)
    {A : Set (EuclideanSpace ℝ (Fin 3))} (hA : MeasurableSet A)
    (hvolA : volA = (MeasureTheory.volume A).toReal)
    (hAc : A ⊆ Submission.BoseGases.acube ℓ)
    {i j : Fin N} (hij : i ≠ j)
    {Φ : Submission.BoseGases.X N → ℝ} (hΦc : Continuous Φ) :
    (∫ x in Submission.BoseGases.abox N ℓ,
        Work.UBBInputs8.boxPInd volA A i Φ x
          * Work.UBBInputs8.boxPInd volA A i (Work.UBBInputs8.boxPInd volA A j Φ) x)
      = ∫ x in Submission.BoseGases.abox N ℓ,
          (Work.UBBInputs8.boxPInd volA A i (Work.UBBInputs8.boxPInd volA A j Φ) x) ^ 2 := by
  obtain ⟨B, hB⟩ := (abox_compact N hℓ).exists_bound_of_continuousOn
    (s := abox N ℓ) (f := Φ) hΦc.continuousOn
  have hCb : ∀ x ∈ abox N ℓ, |Φ x| ≤ |B| := by
    intro x hx
    have h1 : |Φ x| ≤ B := by
      have h2 := hB x hx
      rwa [Real.norm_eq_abs] at h2
    exact le_trans h1 (le_abs_self B)
  have hmPi : Measurable (Work.UBBInputs8.boxPInd volA A i Φ) :=
    measurable_boxPInd volA A hA i hΦc.measurable
  have hmPj : Measurable (Work.UBBInputs8.boxPInd volA A j Φ) :=
    measurable_boxPInd volA A hA j hΦc.measurable
  have hbPi : ∀ x ∈ abox N ℓ, |Work.UBBInputs8.boxPInd volA A i Φ x| ≤ |B| :=
    abs_boxPInd_le hℓ hvol hA hvolA hAc i hCb
  have hbPj : ∀ x ∈ abox N ℓ, |Work.UBBInputs8.boxPInd volA A j Φ x| ≤ |B| :=
    abs_boxPInd_le hℓ hvol hA hvolA hAc j hCb
  -- self-adjointness of `Pᵢ`, at `Φ := PᵢΦ`, `Ψ := PⱼΦ`
  have hsym := boxPInd_selfadj_gen (volA := volA) hℓ hvol hA hvolA hAc i
    (Φ := Work.UBBInputs8.boxPInd volA A i Φ) (Ψ := Work.UBBInputs8.boxPInd volA A j Φ)
    hmPi hbPi hmPj hbPj
  rw [← hsym]
  -- idempotence `PᵢPᵢΦ = PᵢΦ`
  rw [show Work.UBBInputs8.boxPInd volA A i (Work.UBBInputs8.boxPInd volA A i Φ)
      = Work.UBBInputs8.boxPInd volA A i Φ from
    boxPInd_idem_gen hℓ hvol hA hvolA hAc i Φ]
  -- the corpus mixed pair identity
  have hvolA' : volA = (MeasureTheory.volume : Measure E3).real A := by
    rw [MeasureTheory.Measure.real_def]; exact hvolA
  exact Q0C.pair_mixed_N (volA := volA) hℓ hvol hA hvolA' hAc hij hΦc

end Work.BoseFixB1S
