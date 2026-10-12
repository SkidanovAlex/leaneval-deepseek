import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.BombNExcDefs
import Submission.Work.BoseBoxFock.BoxFockDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseBoxFock

open MeasureTheory

set_option autoImplicit false
set_option linter.unusedVariables false

theorem boxSlotOf_evec_zero_eq_aPC {m d : ℕ} [NeZero m] {ℓ : ℝ} (hℓ : 0 < ℓ)
    {e : Fin m → Work.BoseDict.Sp → ℂ}
    (hbdd : ∀ l, MeasureTheory.MemLp (e l) ⊤)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    (hc : ∃ c : ℂ, (starRingEnd ℂ) c * c = (ℓ ^ 3)⁻¹ ∧
      (∀ᵐ x ∂(MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))),
        e 0 x = c * Work.BoseK15.corpusBox.thetaFun ℓ x))
    (Θ : Work.BoseDict.Xn d → ℂ)
    (hΘs : Function.support Θ ⊆ Submission.BoseGases.abox d ℓ) :
    ∀ j : Fin d, ∀ᵐ x ∂(MeasureTheory.volume.restrict (Submission.BoseGases.abox d ℓ)),
      Work.BoseDict.boxSlotOf e (Work.BoseB4.evec m 0) (Work.BoseB4.evec m 0) j Θ x
        = Work.BoseBoxFock.aPC ℓ j Θ x := by
  classical
  obtain ⟨c, hcstar, hcae⟩ := hc
  -- The sharp box indicator `θ_Λ = 1_{boxL ℓ}` is the indicator of the centred cube `acube ℓ`.
  have hθind : Work.BoseK15.corpusBox.thetaFun ℓ
      = Set.indicator (Submission.BoseGases.acube ℓ) (fun _ => (1 : ℂ)) :=
    Work.BoseBoxFock.thetaFun_eq_indicator hℓ
  -- `θ_Λ` is fixed by complex conjugation.
  have hθstar : ∀ y, (starRingEnd ℂ) (Work.BoseK15.corpusBox.thetaFun ℓ y)
      = Work.BoseK15.corpusBox.thetaFun ℓ y := by
    intro y
    rw [hθind]
    by_cases hy : y ∈ Submission.BoseGases.acube ℓ
    · rw [Set.indicator_of_mem hy]; simp
    · rw [Set.indicator_of_notMem hy]; simp
  intro j
  -- ## Step 1: the marginal.  `e 0 (x j) = c · θ_Λ (x j)` for a.e. `x` in the box.
  set N : Set Work.BoseDict.Sp :=
    {y | ¬ (e 0 y = c * Work.BoseK15.corpusBox.thetaFun ℓ y)} with hNdef
  have hNvol : (volume : Measure Work.BoseDict.Sp) N = 0 := MeasureTheory.ae_iff.mp hcae
  set μ0 : Measure Work.BoseDict.Sp :=
    (volume : Measure Work.BoseDict.Sp).restrict (Submission.BoseGases.acube ℓ) with hμ0def
  have hNμ0 : μ0 N = 0 := by
    have hle : μ0 N ≤ (volume : Measure Work.BoseDict.Sp) N :=
      MeasureTheory.Measure.restrict_le_self N
    rw [hNvol] at hle
    exact le_antisymm hle bot_le
  have hae_mu0 : ∀ᵐ y ∂μ0,
      e 0 y = c * Work.BoseK15.corpusBox.thetaFun ℓ y := MeasureTheory.ae_iff.mpr hNμ0
  have huh : ∀ᵐ x ∂(MeasureTheory.Measure.pi (fun _ : Fin d => μ0)),
      e 0 (x j) = c * Work.BoseK15.corpusBox.thetaFun ℓ (x j) :=
    (MeasureTheory.Measure.tendsto_eval_ae_ae (μ := fun _ : Fin d => μ0) (i := j)).eventually
      hae_mu0
  have habox : ∀ᵐ x ∂(MeasureTheory.volume.restrict (Submission.BoseGases.abox d ℓ)),
      e 0 (x j) = c * Work.BoseK15.corpusBox.thetaFun ℓ (x j) := by
    rw [Submission.BoseGases.restrict_abox_eq_pi d ℓ]
    exact huh
  -- ## Step 2: the `z`-integral.  `∫ conj (e 0) · Θ = conj c · ∫_{acube ℓ} Θ`.
  have hint : ∀ x : Work.BoseDict.Xn d,
      (∫ z : Work.BoseDict.Sp, (starRingEnd ℂ) (e 0 z) * Θ (Function.update x j z))
        = (starRingEnd ℂ) c
          * ∫ y in Submission.BoseGases.acube ℓ, Θ (Function.update x j y) := by
    intro x
    have h1 : (fun z : Work.BoseDict.Sp =>
          (starRingEnd ℂ) (e 0 z) * Θ (Function.update x j z))
        =ᵐ[(volume : Measure Work.BoseDict.Sp)]
          (fun z : Work.BoseDict.Sp => (starRingEnd ℂ) c
            * (Work.BoseK15.corpusBox.thetaFun ℓ z * Θ (Function.update x j z))) := by
      filter_upwards [hcae] with z hz
      rw [hz, map_mul, hθstar z]
      ring
    have h2 : (fun z : Work.BoseDict.Sp =>
          Work.BoseK15.corpusBox.thetaFun ℓ z * Θ (Function.update x j z))
        = (Submission.BoseGases.acube ℓ).indicator
            (fun z => Θ (Function.update x j z)) := by
      funext z
      rw [hθind]
      by_cases hz : z ∈ Submission.BoseGases.acube ℓ
      · rw [Set.indicator_of_mem hz, Set.indicator_of_mem hz, one_mul]
      · rw [Set.indicator_of_notMem hz, Set.indicator_of_notMem hz, zero_mul]
    calc (∫ z : Work.BoseDict.Sp, (starRingEnd ℂ) (e 0 z) * Θ (Function.update x j z))
        = ∫ z : Work.BoseDict.Sp, (starRingEnd ℂ) c
            * (Work.BoseK15.corpusBox.thetaFun ℓ z * Θ (Function.update x j z)) :=
          MeasureTheory.integral_congr_ae h1
      _ = (starRingEnd ℂ) c * ∫ z : Work.BoseDict.Sp,
            Work.BoseK15.corpusBox.thetaFun ℓ z * Θ (Function.update x j z) :=
          MeasureTheory.integral_const_mul _ _
      _ = (starRingEnd ℂ) c * ∫ y in Submission.BoseGases.acube ℓ,
            Θ (Function.update x j y) := by
          rw [h2, MeasureTheory.integral_indicator (Submission.BoseGases.acube_measurable ℓ)]
  -- ## Step 3: assembly.
  filter_upwards [habox,
    MeasureTheory.ae_restrict_mem (Submission.BoseGases.abox_measurable d ℓ)] with x hx hxmem
  have hxj : x j ∈ Submission.BoseGases.acube ℓ :=
    (Submission.BoseGases.mem_abox_iff d ℓ x).mp hxmem j
  have hθ1 : Work.BoseK15.corpusBox.thetaFun ℓ (x j) = 1 := by
    rw [hθind]
    exact Set.indicator_of_mem hxj _
  have he0 : e 0 (x j) = c := by rw [hx, hθ1, mul_one]
  rw [show Work.BoseDict.boxSlotOf e (Work.BoseB4.evec m 0) (Work.BoseB4.evec m 0) j Θ
      = Work.BoseBoxFock.uSlot (e 0) j Θ from
        Work.BoseBoxFock.boxSlotOf_evec0_eq_uSlot e j Θ]
  simp only [Work.BoseBoxFock.uSlot, Work.BoseBoxFock.aPC]
  rw [he0, hint x, ← mul_assoc, mul_comm c ((starRingEnd ℂ) c), hcstar, one_div]

end Work.BoseBoxFock
