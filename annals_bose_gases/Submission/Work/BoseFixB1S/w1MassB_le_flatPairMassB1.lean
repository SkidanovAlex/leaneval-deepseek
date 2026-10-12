import ChallengeDeps
import Mathlib.Order.CompletePartialOrder
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseFixB1.integrable_psiPairKernel
import Submission.Work.BoseFixB1.psiAutocorrIdentity
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1S.w1MassB_le_flatPairMassB1` — the one-body mass is dominated by the flat pair mass

    w1MassB h M ℓ d u = ∫_x ∫_y w_{1,B(u)}(x,y)  ≤  ∫_x ∫_y w_{2,B(u)}(x,y) = flatPairMass v M ℓ d u

(the one-body kernel has numerator `g₀ = v(1−ω₀)`, the pair kernel on the right has numerator `v`).
Since `0 ≤ v` and `0 ≤ ω₀` a.e., we have `g₀ ≤ v` a.e.; the two kernels share the same
(nonnegative) cutoffs `χ_{B(u)}` and the same renormalisation denominators
`convScaleSmall M (ℓd)·convScale ℓ` (also nonnegative), so the pointwise comparison of the
numerators gives the pointwise a.e. domination of the integrands.

The two masses are turned into the same one-dimensional *lag* integral

    `∫_z (f z / E z) · A(z)`,  `E = convScaleSmall M (ℓd)·convScale ℓ`,
    `A = autocorr ℓ d u = ∫_x χ_B(x)·χ_B(x−z)` (≥ 0),

by the Fubini/autocorrelation identity `Work.BoseFixB1.psiAutocorrIdentity` (valid because the lag
kernel is jointly integrable, `Work.BoseFixB1.integrable_psiPairKernel`), and the comparison is then
`MeasureTheory.integral_mono_ae` — the integrability of both sides being
`Integrable.integral_prod_right` of that joint integrability.
-/

namespace Work.BoseFixB1S

noncomputable section

open MeasureTheory Metric Filter
open scoped Topology Real ENNReal BigOperators

set_option autoImplicit false
set_option linter.unusedVariables false

theorem w1MassB_le_flatPairMassB1 {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v)
    (hv : 0 ≤ v) (hvrad : _root_.BoseGases.IsRadial v) (hv1 : MeasureTheory.MemLp v 1)
    {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    {M : ℕ} (hM : 1 ≤ M) {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d)
    (hR16 : R ≤ ℓ * d / 16) (hRχ : R ≤ ℓ * Submission.BoseGases.chiR0)
    (u : EuclideanSpace ℝ (Fin 3)) :
    Work.BoseFixB1.w1MassB h M ℓ d u
      ≤ Work.BoseFixB1.flatPairMass v M ℓ d u := by
  classical
  -- ## Notations
  set E : EuclideanSpace ℝ (Fin 3) → ℝ := fun z =>
      Submission.BoseGases.convScaleSmall M (ℓ * d) z * Submission.BoseGases.convScale ℓ z with hE
  set A : EuclideanSpace ℝ (Fin 3) → ℝ := fun z =>
      Work.BoseFixB1.autocorr (M := M) ℓ d u z with hA
  -- ## The chosen scattering solution and the integrability of the two numerators
  have hw0 := Classical.choose_spec h
  have hg_int : MeasureTheory.Integrable (Submission.BoseGases.g0 v h) := by
    have h' := Submission.BoseGases.scatG_integrable (v := v) (w := Classical.choose h)
      (R := R) hv_supp hw0.2
    show MeasureTheory.Integrable (fun x => v x * (1 - Classical.choose h x))
    exact h'
  have hg_mlp : MeasureTheory.MemLp (Submission.BoseGases.g0 v h) 1 :=
    MeasureTheory.memLp_one_iff_integrable.mpr hg_int
  have hg_supp : tsupport (Submission.BoseGases.g0 v h) ⊆
      Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R := by
    have hsub : Function.support (Submission.BoseGases.g0 v h) ⊆ tsupport v := by
      intro z hz
      refine subset_tsupport v ?_
      intro hv0
      exact (Function.mem_support.mp hz) (by simp [Submission.BoseGases.g0, hv0])
    calc tsupport (Submission.BoseGases.g0 v h)
        = closure (Function.support (Submission.BoseGases.g0 v h)) := rfl
      _ ⊆ closure (tsupport v) := closure_mono hsub
      _ = tsupport v := (isClosed_tsupport v).closure_eq
      _ ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R := hv_supp
  -- ## Joint integrability of the two lag kernels (for `v` and for `g₀`)
  have hIv := Work.BoseFixB1.integrable_psiPairKernel (v := v) (R0 := R) hR hv_supp hv1
    hM hℓ hd hR16 hRχ u
  have hIg := Work.BoseFixB1.integrable_psiPairKernel (v := Submission.BoseGases.g0 v h)
    (R0 := R) hR hg_supp hg_mlp hM hℓ hd hR16 hRχ u
  -- ## The two mass identities as lag integrals
  have e1 := Work.BoseFixB1.psiAutocorrIdentity (f := v) (M := M) (ℓ := ℓ) (d := d) u hIv
  have e2 := Work.BoseFixB1.psiAutocorrIdentity (f := Submission.BoseGases.g0 v h) (M := M)
    (ℓ := ℓ) (d := d) u hIg
  -- ## Integrability of the two weighted autocorrelations
  have hAAv : MeasureTheory.Integrable (fun z => (v z / E z) * A z) := by
    refine (hIv.integral_prod_right).congr (Filter.Eventually.of_forall (fun z => ?_))
    simp only [Work.BoseFixB1.psiPairKernel_apply, hE, hA, Work.BoseFixB1.autocorr_apply]
    rw [← MeasureTheory.integral_const_mul]
    apply MeasureTheory.integral_congr_ae
    filter_upwards with x
    ring
  have hAAg : MeasureTheory.Integrable
      (fun z => (Submission.BoseGases.g0 v h z / E z) * A z) := by
    refine (hIg.integral_prod_right).congr (Filter.Eventually.of_forall (fun z => ?_))
    simp only [Work.BoseFixB1.psiPairKernel_apply, hE, hA, Work.BoseFixB1.autocorr_apply]
    rw [← MeasureTheory.integral_const_mul]
    apply MeasureTheory.integral_congr_ae
    filter_upwards with x
    ring
  -- ## The autocorrelation and the renormalisation denominator are nonnegative
  have hA0 : ∀ z : EuclideanSpace ℝ (Fin 3), 0 ≤ A z := fun z => by
    simp only [hA, Work.BoseFixB1.autocorr_apply]
    exact integral_nonneg (fun x => mul_nonneg
      (Work.SmallBoxSliding.chiSmallB_nonneg M ℓ d u x)
      (Work.SmallBoxSliding.chiSmallB_nonneg M ℓ d u (x - z)))
  have hE0 : ∀ z : EuclideanSpace ℝ (Fin 3), 0 ≤ E z := fun z => by
    simp only [hE]
    exact mul_nonneg (Work.BoseFixB1.convScaleSmall_nonneg M (ℓ * d) z)
      (Submission.BoseGases.convScale_nonneg ℓ z)
  -- ## `g₀ ≤ v` a.e.
  have hg0_le : ∀ᵐ z ∂(MeasureTheory.volume :
      MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))),
      Submission.BoseGases.g0 v h z ≤ v z := by
    have hb := Submission.BoseGases.scattering_bounds_ae (v := v) (w := Classical.choose h)
      (R := R) hR hv hvrad hv_supp hw0.1 hw0.2
    filter_upwards [hb.1] with z hz0
    have hvz : 0 ≤ v z := hv z
    simp only [Submission.BoseGases.g0]
    calc v z * (1 - Classical.choose h z) ≤ v z * 1 :=
          mul_le_mul_of_nonneg_left (by linarith) hvz
      _ = v z := by ring
  -- ## The pointwise a.e. comparison of the lag integrands
  have hmono : (fun z => (Submission.BoseGases.g0 v h z / E z) * A z)
      ≤ᵐ[MeasureTheory.volume] (fun z => (v z / E z) * A z) := by
    filter_upwards [hg0_le] with z hz
    exact mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hz (hE0 z)) (hA0 z)
  have hkey : (∫ z, (Submission.BoseGases.g0 v h z / E z) * A z)
      ≤ ∫ z, (v z / E z) * A z :=
    MeasureTheory.integral_mono_ae hAAg hAAv hmono
  -- ## Identification of the two masses with the lag integrals
  have hfp : Work.BoseFixB1.flatPairMass v M ℓ d u = ∫ z, (v z / E z) * A z := by
    rw [Work.BoseFixB1.flatPairMass]
    simpa only [hE, hA] using e1
  have hw1 : Work.BoseFixB1.w1MassB h M ℓ d u
      = ∫ z, (Submission.BoseGases.g0 v h z / E z) * A z := by
    rw [Work.BoseFixB1.w1MassB]
    simp only [Submission.BoseGases.wSmall1Pair]
    simpa only [hE, hA] using e2
  rw [hw1, hfp]
  exact hkey

end

end Work.BoseFixB1S
