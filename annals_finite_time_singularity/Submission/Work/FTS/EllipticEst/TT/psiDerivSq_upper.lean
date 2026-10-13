import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.EllipticEst.TT.ang1HkMem
import Submission.Work.FTS.EllipticEst.TT.WeakDefs
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.AngSecond.Defs
import Submission.Work.FTS.EllipticEst.AngSecond.I4_tan_mul_sub_deriv
import Submission.Work.FTS.EllipticEst.StraightDefs
import Submission.Work.FTS.EllipticEst.remov.pth_zero_of_HkMem

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.TT

/-- In the weak class `EllWeakPos α 0 F Ψ` (plus `HkMem α 0 Ψ` and `HkMem α 0 (z ∂_zΨ)`), the
square of the `θ`-derivative of the slice variable `θ ↦ Ψ z θ / cos θ`, against
`σ θ = sin(2θ)^{-η}` (`η = 99/100`), is integrable on the **upper half** `(π/4, π/2)` for every
`z > 0`.

Route.  `Work.FTS.EllipticEst.AngSecond.I4_tan_mul_sub_deriv` gives, on the open quadrant,

`U z θ - Ψ z θ = sin θ · (∂_θ(Ψ z · / cos ·))(θ)`,  `U := ∂_θ(tan θ · Ψ)`,

so on `(π/4, π/2)`, where `sin θ ≥ 1/√2`,

`(ψ' θ)² σ θ ≤ 2 (U z θ - Ψ z θ)² σ θ ≤ 4 U z θ² σ θ + 4 (Ψ z θ)² σ θ`.

For the second term: `HkMem α 0 Ψ` gives, for `z > 0`, the slicewise integrability of
`θ ↦ (Ψ z θ)² σ θ` (the `HkIntegrand` at level `0` is `(g · w/s^{η/2})²`; for `z > 0` the factor
`w z² ≠ 0` can be divided out -- `Submission.Work.FTS.EllipticEst.remov.pth_zero_of_HkMem`
contains the pointwise identity `HkIntegrand_zero_eq`; do not use `HkMem_zero_slices`, which
demands `SmoothNbhd`).  For the first term use `HkMem α 0 U`, which is the conclusion of the
sibling `Work.FTS.EllipticEst.TT.ang1HkMem`, and then the same slicewise transfer with `g := U`.
Finally `Integrable.mono'` on `Ioo (π/4) (π/2)` with the a.e. strong measurability of `(ψ')²σ`,
where `ψ'` is continuous on `(0, π/2)` (the slice `θ ↦ Ψ z θ` is `C^∞` there by
`EllWeakPos.smooth`, and `cos > 0`). -/
theorem psiDerivSq_upper : ∀ (α : ℝ) (F Ψ : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 / 4 →
    Work.FTS.EllipticEst.TT.EllWeakPos α 0 F Ψ →
    Work.Spaces.HkMem α 0 Ψ →
    Work.Spaces.HkMem α 0 (fun z θ => z * Work.Spaces.pz Ψ z θ) →
    ∀ z : ℝ, 0 < z → MeasureTheory.IntegrableOn
      (fun θ => (deriv (fun θ' => Ψ z θ' / Real.cos θ') θ) ^ 2
        * Work.FTS.EllipticEst.AngSecond.sig θ)
      (Set.Ioo (Real.pi / 4) (Real.pi / 2)) := by
  intro α F Ψ hα hα4 hE hΨ hG z hz
  -- The angular first-order quantity `U = ∂_θ(tan θ · Ψ)` is again honest.
  set U : ℝ → ℝ → ℝ := fun z θ => deriv (fun θ' => Real.tan θ' * Ψ z θ') θ with hUdef
  have hU : Work.Spaces.HkMem α 0 U := by
    rw [hUdef]
    exact Work.FTS.EllipticEst.TT.ang1HkMem α F Ψ hα hα4 hE hΨ hG
  -- Slicewise `σ`-honesty transferred from `HkMem α 0 g` (the `k = 0` integrand).
  have slice_mem : ∀ {g : ℝ → ℝ → ℝ}, Work.Spaces.HkMem α 0 g →
      MeasureTheory.IntegrableOn
        (fun θ => (g z θ) ^ 2 * Work.FTS.EllipticEst.AngSecond.sig θ) Work.Spaces.Iθ := by
    intro g hm
    have h0 : MeasureTheory.Integrable (fun θ => Work.Spaces.HkIntegrand α 0 g z θ)
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) := hm.1 z (le_of_lt hz)
    have h1 : MeasureTheory.IntegrableOn
        (fun θ => (1 / (Work.Spaces.w z) ^ 2) * Work.Spaces.HkIntegrand α 0 g z θ)
        Work.Spaces.Iθ := MeasureTheory.Integrable.const_mul h0 _
    have hw : Work.Spaces.w z ≠ 0 := by rw [Work.Spaces.w]; positivity
    refine h1.congr_fun (fun θ hθ => ?_) measurableSet_Icc
    show (1 / Work.Spaces.w z ^ 2) * Work.Spaces.HkIntegrand α 0 g z θ
        = g z θ ^ 2 * Work.FTS.EllipticEst.AngSecond.sig θ
    rw [Work.FTS.EllipticEst.AngSecond.sig,
      Work.FTS.EllipticEst.remov.HkIntegrand_zero_eq α g z hθ]
    field_simp
  have hsub : Set.Ioo (Real.pi / 4) (Real.pi / 2) ⊆ Work.Spaces.Iθ :=
    fun θ hθ => ⟨le_of_lt (by linarith [hθ.1, Real.pi_pos]), le_of_lt hθ.2⟩
  have hUint : MeasureTheory.IntegrableOn
      (fun θ => (U z θ) ^ 2 * Work.FTS.EllipticEst.AngSecond.sig θ)
      (Set.Ioo (Real.pi / 4) (Real.pi / 2)) := (slice_mem hU).mono_set hsub
  have hPint : MeasureTheory.IntegrableOn
      (fun θ => (Ψ z θ) ^ 2 * Work.FTS.EllipticEst.AngSecond.sig θ)
      (Set.Ioo (Real.pi / 4) (Real.pi / 2)) := (slice_mem hΨ).mono_set hsub
  have hmaj : MeasureTheory.Integrable
      (fun θ => 4 * ((U z θ) ^ 2 * Work.FTS.EllipticEst.AngSecond.sig θ)
        + 4 * ((Ψ z θ) ^ 2 * Work.FTS.EllipticEst.AngSecond.sig θ))
      (MeasureTheory.volume.restrict (Set.Ioo (Real.pi / 4) (Real.pi / 2))) :=
    MeasureTheory.Integrable.add (MeasureTheory.Integrable.const_mul hUint 4)
      (MeasureTheory.Integrable.const_mul hPint 4)
  -- a.e. strong measurability of `(ψ')²σ` from the `C¹`-regularity of the slice.
  have hsub' : Set.Ioo (Real.pi / 4) (Real.pi / 2) ⊆ Set.Ioo 0 (Real.pi / 2) :=
    fun θ hθ => ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩
  have hcos_ne : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), Real.cos θ ≠ 0 := by
    intro θ hθ
    exact ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩)
  have hslice1 : ContDiffOn ℝ 1 (fun θ' => Ψ z θ') (Set.Ioo 0 (Real.pi / 2)) := by
    have hmap : Set.MapsTo (fun θ' : ℝ => (z, θ')) (Set.Ioo 0 (Real.pi / 2))
        (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := fun θ' hθ' => ⟨hz, hθ'⟩
    exact (hE.smooth 1).comp (by fun_prop) hmap
  have hquot : ContDiffOn ℝ 1 (fun θ' => Ψ z θ' / Real.cos θ') (Set.Ioo 0 (Real.pi / 2)) :=
    hslice1.div Real.contDiff_cos.contDiffOn hcos_ne
  have hcontD : ContinuousOn (deriv (fun θ' => Ψ z θ' / Real.cos θ'))
      (Set.Ioo 0 (Real.pi / 2)) :=
    hquot.continuousOn_deriv_of_isOpen isOpen_Ioo (by norm_num)
  have hcontD' : ContinuousOn (deriv (fun θ' => Ψ z θ' / Real.cos θ'))
      (Set.Ioo (Real.pi / 4) (Real.pi / 2)) := hcontD.mono hsub'
  have hsig_cont : ContinuousOn Work.FTS.EllipticEst.AngSecond.sig
      (Set.Ioo (Real.pi / 4) (Real.pi / 2)) := by
    have hf : ContinuousOn (fun θ => Real.sin (2 * θ)) (Set.Ioo (Real.pi / 4) (Real.pi / 2)) :=
      (Real.continuous_sin.comp (continuous_const.mul continuous_id)).continuousOn
    have hne : ∀ θ ∈ Set.Ioo (Real.pi / 4) (Real.pi / 2), Real.sin (2 * θ) ≠ 0 := by
      intro θ hθ
      exact ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1, Real.pi_pos])
        (by linarith [hθ.2, Real.pi_pos]))
    exact hf.rpow_const (p := -(Work.Spaces.eta)) (fun θ hθ => Or.inl (hne θ hθ))
  have haesm : MeasureTheory.AEStronglyMeasurable
      (fun θ => (deriv (fun θ' => Ψ z θ' / Real.cos θ') θ) ^ 2
        * Work.FTS.EllipticEst.AngSecond.sig θ)
      (MeasureTheory.volume.restrict (Set.Ioo (Real.pi / 4) (Real.pi / 2))) :=
    ((hcontD'.pow 2).mul hsig_cont).aestronglyMeasurable measurableSet_Ioo
  -- the pointwise bound on `(π/4, π/2)`, where `sin θ ≥ 1/√2`.
  have hpoint : ∀ θ ∈ Set.Ioo (Real.pi / 4) (Real.pi / 2),
      (deriv (fun θ' => Ψ z θ' / Real.cos θ') θ) ^ 2 * Work.FTS.EllipticEst.AngSecond.sig θ
        ≤ 4 * ((U z θ) ^ 2 * Work.FTS.EllipticEst.AngSecond.sig θ)
          + 4 * ((Ψ z θ) ^ 2 * Work.FTS.EllipticEst.AngSecond.sig θ) := by
    intro θ hθ
    have hθI : θ ∈ Set.Ioo 0 (Real.pi / 2) := ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩
    have hdiff : DifferentiableAt ℝ (fun θ' => Ψ z θ') θ :=
      (hslice1.differentiableOn (by norm_num)).differentiableAt (isOpen_Ioo.mem_nhds hθI)
    have hid : Real.sin θ * deriv (fun θ' => Ψ z θ' / Real.cos θ') θ = U z θ - Ψ z θ := by
      have h := Work.FTS.EllipticEst.AngSecond.I4_tan_mul_sub_deriv
        (fun θ' => Ψ z θ') hθI hdiff
      rw [← h]
    have hsin2 : (1 / 2 : ℝ) ≤ Real.sin θ ^ 2 := by
      have hmem1 : θ ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) :=
        ⟨by linarith [hθ.1, Real.pi_pos], le_of_lt (by linarith [hθ.2, Real.pi_pos])⟩
      have hmem2 : Real.pi / 4 ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) :=
        ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
      have hsin := Real.strictMonoOn_sin hmem2 hmem1 hθ.1
      rw [Real.sin_pi_div_four] at hsin
      have h0 : (0 : ℝ) ≤ Real.sqrt 2 / 2 := by positivity
      have hlt := pow_lt_pow_left₀ hsin h0 (by norm_num : (2 : ℕ) ≠ 0)
      have hsq : (Real.sqrt 2 / 2) ^ 2 = 1 / 2 := by
        rw [div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]; norm_num
      linarith [hlt, hsq]
    have hB : (deriv (fun θ' => Ψ z θ' / Real.cos θ') θ) ^ 2
        ≤ 4 * (U z θ) ^ 2 + 4 * (Ψ z θ) ^ 2 := by
      have heq : (Real.sin θ) ^ 2 * (deriv (fun θ' => Ψ z θ' / Real.cos θ') θ) ^ 2
          = (U z θ - Ψ z θ) ^ 2 := by rw [← hid]; ring
      have hhalf : (1 / 2) * (deriv (fun θ' => Ψ z θ' / Real.cos θ') θ) ^ 2
          ≤ (U z θ - Ψ z θ) ^ 2 := by
        rw [← heq]
        nlinarith [hsin2, sq_nonneg (deriv (fun θ' => Ψ z θ' / Real.cos θ') θ)]
      have hB' : (U z θ - Ψ z θ) ^ 2 ≤ 2 * (U z θ) ^ 2 + 2 * (Ψ z θ) ^ 2 := by
        nlinarith [sq_nonneg (U z θ + Ψ z θ)]
      nlinarith [hhalf, hB']
    have hsig : 0 ≤ Work.FTS.EllipticEst.AngSecond.sig θ :=
      Work.FTS.EllipticEst.AngSecond.sig_nonneg (θ := θ) ⟨le_of_lt hθI.1, le_of_lt hθI.2⟩
    calc (deriv (fun θ' => Ψ z θ' / Real.cos θ') θ) ^ 2 * Work.FTS.EllipticEst.AngSecond.sig θ
        ≤ (4 * (U z θ) ^ 2 + 4 * (Ψ z θ) ^ 2) * Work.FTS.EllipticEst.AngSecond.sig θ :=
          mul_le_mul_of_nonneg_right hB hsig
      _ = 4 * ((U z θ) ^ 2 * Work.FTS.EllipticEst.AngSecond.sig θ)
            + 4 * ((Ψ z θ) ^ 2 * Work.FTS.EllipticEst.AngSecond.sig θ) := by ring
  refine MeasureTheory.Integrable.mono' hmaj haesm ?_
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with θ hθ
  rw [Real.norm_eq_abs,
    abs_of_nonneg (mul_nonneg (sq_nonneg (deriv (fun θ' => Ψ z θ' / Real.cos θ') θ))
      (Work.FTS.EllipticEst.AngSecond.sig_nonneg (θ := θ)
        ⟨le_of_lt (by linarith [hθ.1, Real.pi_pos]), le_of_lt hθ.2⟩))]
  exact hpoint θ hθ

end Work.FTS.EllipticEst.TT
