/-
Work module for the Elgindi finite-time singularity project.

# Honesty of the `∂_zΨ`-slice against the angular weight `sin θ cos²θ`

For a datum of the weak class `Work.FTS.EllipticEst.TT.EllWeakPos α 0 F Ψ` (the class of
Proposition `prop:L2` of Elgindi's paper, at level `0`) and every `z > 0`, the angular slice

  `θ ↦ ∂_zΨ(z,θ) · sin θ cos²θ`

is integrable on `Iθ = [0,π/2]`.

## The route

The hypotheses only control the *squared* weighted `θ`-energies of `F`, of `z²∂_zzΨ` and of
`∂_θθΨ` (`Work.Spaces.HkMem α 0`); `∂_zΨ` itself is not among them.  It is recovered from the
equation `bslOp α Ψ = F` on the open quadrant:

  `α(5+α) z ∂_zΨ = Lzero Ψ - α²z²∂_zzΨ - F`   on `(0,π/2)`,

and each of the five summands of `Lzero Ψ = -∂_θθΨ + ∂_θ(tan θ · Ψ) - 6Ψ` is shown to be
integrable against `sinθcos²θ`:

* `F`, `z²∂_zzΨ`, `∂_θθΨ`: `abs_mul_sinCos2_le_weighted`
  (`|g·sinθcos²θ| ≤ (g·w/sin(2θ)^{η/2})² + 1`) together with the `HkMem α 0` hypotheses, via
  `remov.ws_absMoment`;
* `∂_θ(tan θ · Ψ) = Ψ/cos²θ + tan θ ∂_θΨ` on the open interval (product rule), and both
  `Ψ·sinθcos²θ` and `tan θ ∂_θΨ · sinθcos²θ` are dominated by the *bounded* quantities `|Ψ|`
  and `|∂_θΨ|` (because `tan θ sinθcos²θ = sin²θ cos θ` and `cos θ·(Ψ/cos²θ)·sinθcos²θ =
  sin θ · Ψ` are bounded by `1` resp. `|Ψ|`).  The boundedness of the slice `Ψ(z,·)` and of its
  derivative `∂_θΨ(z,·)` on `(0,π/2)` is `remov.abs_le_of_sq_mul_sEta`, applied to the honest
  weighted energy of `∂_θθΨ` (an `HkMem α 0` hypothesis).
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.EllipticEst.TT.WeakDefs
import Submission.Work.FTS.EllipticEst.StraightDefs
import Submission.Work.FTS.EllipticEst.remov.wsAux
import Submission.Work.FTS.EllipticEst.remov.weakSliceRegular
import Submission.Work.FTS.EllipticEst.remov.wsMomentId

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.WeakMoment

set_option autoImplicit false

/-! ## Elementary helpers -/

/-- The angular profile `sin θ cos²θ` is a.e. strongly measurable. -/
private lemma aesm_sinCos2 :
    MeasureTheory.AEStronglyMeasurable (fun θ : ℝ => Work.Elliptic.sinCos2 θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
  show MeasureTheory.AEStronglyMeasurable (fun θ : ℝ => Real.sin θ * Real.cos θ ^ 2) _
  fun_prop

/-- Multiplication by the angular profile preserves a.e. strong measurability. -/
private lemma aesm_mul_sinCos2 {g : ℝ → ℝ}
    (hg : MeasureTheory.AEStronglyMeasurable g (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :
    MeasureTheory.AEStronglyMeasurable (fun θ => g θ * Work.Elliptic.sinCos2 θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
  hg.mul aesm_sinCos2

/-- If `g` is a.e. strongly measurable and `|g·sinθcos²θ|` is bounded on the open interval by
`C`, then `g·sinθcos²θ` is integrable on `Iθ` (a set of finite measure). -/
private lemma integrableOn_mul_sinCos2_of_norm_bound {g : ℝ → ℝ} {C : ℝ}
    (hg : MeasureTheory.AEStronglyMeasurable g (MeasureTheory.volume.restrict Work.Spaces.Iθ))
    (hb : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      |g θ * Work.Elliptic.sinCos2 θ| ≤ C) :
    MeasureTheory.IntegrableOn (fun θ => g θ * Work.Elliptic.sinCos2 θ) Work.Spaces.Iθ := by
  refine MeasureTheory.Integrable.mono'
    (MeasureTheory.integrableOn_const (C := C) (μ := MeasureTheory.volume) (s := Work.Spaces.Iθ)
      (by rw [Work.Spaces.Iθ, Real.volume_Icc]; exact ENNReal.ofReal_ne_top) (by simp)) ?_ ?_
  · exact aesm_mul_sinCos2 hg
  · refine Work.FTS.EllipticEst.ae_restrict_Icc_of_forall_Ioo (fun θ hθ => ?_)
    rw [Real.norm_eq_abs]
    exact hb θ hθ

/-- On the open interval, `tan θ · sin θ cos²θ = sin²θ cos θ`, whose absolute value is at
most `1`. -/
private lemma abs_tan_mul_sinCos2_le_one {θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    |Real.tan θ * Work.Elliptic.sinCos2 θ| ≤ 1 := by
  have hπ : 0 < Real.pi := Real.pi_pos
  have hc : Real.cos θ ≠ 0 :=
    ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, hπ], hθ.2⟩)
  have hsin0 : 0 ≤ Real.sin θ :=
    Real.sin_nonneg_of_nonneg_of_le_pi (le_of_lt hθ.1) (by linarith [hθ.2, hπ])
  have hcos0 : 0 ≤ Real.cos θ :=
    le_of_lt (Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, hπ], hθ.2⟩)
  have hs1 : Real.sin θ ≤ 1 := Real.sin_le_one θ
  have hc1 : Real.cos θ ≤ 1 := Real.cos_le_one θ
  have heq : Real.tan θ * Work.Elliptic.sinCos2 θ = Real.sin θ ^ 2 * Real.cos θ := by
    rw [Real.tan_eq_sin_div_cos, Work.Elliptic.sinCos2]
    field_simp
  rw [heq, abs_of_nonneg (by positivity)]
  nlinarith [sq_nonneg (Real.sin θ), hsin0, hs1, hc1, hcos0]

/-- The product rule for `∂_θ(tan θ · u)` along a `θ`-slice: at an interior angle,
`∂_θ(tan θ · Ψ) = Ψ/cos²θ + tan θ · ∂_θΨ`. -/
private lemma pth_tan_mul_slice {Ψ : ℝ → ℝ → ℝ} {z θ : ℝ}
    (hdΨ : DifferentiableAt ℝ (fun θ' => Ψ z θ') θ) (hc : Real.cos θ ≠ 0) :
    Work.Spaces.pth (fun z θ' => Real.tan θ' * Ψ z θ') z θ
      = Ψ z θ / Real.cos θ ^ 2 + Real.tan θ * Work.Spaces.pth (fun z θ' => Ψ z θ') z θ := by
  have h := (Real.hasDerivAt_tan hc).mul hdΨ.hasDerivAt
  have hd : deriv (fun θ' => Real.tan θ' * Ψ z θ') θ
      = Real.tan θ * deriv (fun θ' => Ψ z θ') θ + (1 / Real.cos θ ^ 2) * Ψ z θ := by
    rw [add_comm]
    exact h.deriv
  simp only [Work.Spaces.pth]
  rw [hd]
  field_simp
  ring

/-! ## The main result -/

theorem PzSliceIntegrable (α : ℝ) (F Ψ : ℝ → ℝ → ℝ) (hα : 0 < α)
    (h : Work.FTS.EllipticEst.TT.EllWeakPos α 0 F Ψ) :
    ∀ z : ℝ, 0 < z → MeasureTheory.IntegrableOn
      (fun θ : ℝ => Work.Spaces.pz Ψ z θ * Work.Elliptic.sinCos2 θ) Work.Spaces.Iθ := by
  intro z hz
  -- the `C^∞`-on-the-open-quadrant structure of the three `HkMem` slots
  have hΨ : Work.FTS.EllipticEst.SmoothOpen Ψ := Work.FTS.EllipticEst.smoothOpen_of_forall h.smooth
  have hF : Work.FTS.EllipticEst.SmoothOpen F := Work.FTS.EllipticEst.remov.ws_smoothOpen_F h
  have hA : Work.FTS.EllipticEst.SmoothOpen (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) :=
    Work.FTS.EllipticEst.remov.ws_smoothOpen_zsq hΨ
  have hB : Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.pthIter 2 Ψ) := (hΨ.pth).pth
  -- the honest weighted energy of `∂_θθΨ`
  have hE : MeasureTheory.IntegrableOn
      (fun θ => (Work.Spaces.pthIter 2 Ψ z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
      Work.Spaces.Iθ := by
    have := Work.FTS.EllipticEst.remov.ws_slot_slice hB h.memB 0 (by omega) hz
    simpa using this
  -- the slice `Ψ(z,·)` and its derivative are bounded on the open interval
  obtain ⟨C, _hCpos, hC⟩ := Work.FTS.EllipticEst.remov.abs_le_of_sq_mul_sEta
    (Work.FTS.EllipticEst.remov.ws_contDiffOn_slice hΨ hz)
    (by simpa only [Work.Spaces.pthIter_succ, Work.Spaces.pthIter_zero, Work.Spaces.pth] using hE)
  -- the three `HkMem` slots, paired with `sinθcos²θ`
  have hFsg : MeasureTheory.IntegrableOn (fun θ => F z θ * Work.Elliptic.sinCos2 θ)
      Work.Spaces.Iθ :=
    (Work.FTS.EllipticEst.remov.ws_absMoment (Work.FTS.EllipticEst.remov.ws_aesm_slice hF hz)
      (Work.FTS.EllipticEst.remov.ws_slot_slice hF h.memF 0 (by omega) hz)).1
  have hAsg : MeasureTheory.IntegrableOn
      (fun θ => (z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) * Work.Elliptic.sinCos2 θ)
      Work.Spaces.Iθ :=
    (Work.FTS.EllipticEst.remov.ws_absMoment (Work.FTS.EllipticEst.remov.ws_aesm_slice hA hz)
      (Work.FTS.EllipticEst.remov.ws_slot_slice hA h.memA 0 (by omega) hz)).1
  have hMsg : MeasureTheory.IntegrableOn
      (fun θ => Work.Spaces.pthIter 2 Ψ z θ * Work.Elliptic.sinCos2 θ) Work.Spaces.Iθ :=
    (Work.FTS.EllipticEst.remov.ws_absMoment (Work.FTS.EllipticEst.remov.ws_aesm_slice hB hz)
      hE).1
  -- the bounded pieces `Ψ·sinθcos²θ` and `tan θ ∂_θΨ · sinθcos²θ`
  have hDsg : MeasureTheory.IntegrableOn (fun θ => Ψ z θ * Work.Elliptic.sinCos2 θ)
      Work.Spaces.Iθ := by
    refine integrableOn_mul_sinCos2_of_norm_bound (g := fun θ => Ψ z θ) (C := C)
      (Work.FTS.EllipticEst.remov.ws_aesm_slice hΨ hz) (fun θ hθ => ?_)
    rw [abs_mul]
    have h1 : |Work.Elliptic.sinCos2 θ| ≤ 1 :=
      Work.FTS.EllipticEst.abs_sinCos2_le_one ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
    calc |Ψ z θ| * |Work.Elliptic.sinCos2 θ| ≤ |Ψ z θ| * 1 :=
          mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
      _ = |Ψ z θ| := by ring
      _ ≤ C := (hC θ hθ).2
  have hEsg : MeasureTheory.IntegrableOn
      (fun θ => Real.tan θ * Work.Spaces.pth Ψ z θ * Work.Elliptic.sinCos2 θ)
      Work.Spaces.Iθ := by
    have htanm : Measurable Real.tan := by
      have h : Real.tan = fun θ => Real.sin θ / Real.cos θ := funext Real.tan_eq_sin_div_cos
      rw [h]
      exact Real.measurable_sin.div Real.measurable_cos
    refine integrableOn_mul_sinCos2_of_norm_bound
      (g := fun θ => Real.tan θ * Work.Spaces.pth Ψ z θ) (C := C)
      (htanm.aestronglyMeasurable.mul
        (Work.FTS.EllipticEst.remov.ws_aesm_slice hΨ.pth hz)) (fun θ hθ => ?_)
    have hre : Real.tan θ * Work.Spaces.pth Ψ z θ * Work.Elliptic.sinCos2 θ
        = (Real.tan θ * Work.Elliptic.sinCos2 θ) * Work.Spaces.pth Ψ z θ := by ring
    rw [hre, abs_mul]
    calc |Real.tan θ * Work.Elliptic.sinCos2 θ| * |Work.Spaces.pth Ψ z θ| ≤ 1 * C :=
          mul_le_mul (abs_tan_mul_sinCos2_le_one hθ)
            (by simpa [Work.Spaces.pth] using (hC θ hθ).1) (abs_nonneg _) (by norm_num)
      _ = C := by ring
  -- the angular term `∂_θ(tan θ Ψ)` of `Lzero`, via the product rule
  have hTsg : MeasureTheory.IntegrableOn
      (fun θ => Work.Spaces.pth (fun z θ => Real.tan θ * Ψ z θ) z θ
        * Work.Elliptic.sinCos2 θ) Work.Spaces.Iθ := by
    have hdΨ : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
        DifferentiableAt ℝ (fun θ' => Ψ z θ') θ := by
      intro θ hθ
      exact ((hΨ.curry_θ hz).contDiffAt (isOpen_Ioo.mem_nhds hθ)).differentiableAt (by norm_num)
    have key : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
        |Work.Spaces.pth (fun z θ => Real.tan θ * Ψ z θ) z θ * Work.Elliptic.sinCos2 θ|
          ≤ 2 * C := by
      intro θ hθ
      have hπ : 0 < Real.pi := Real.pi_pos
      have hcos : Real.cos θ ≠ 0 :=
        ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, hπ], hθ.2⟩)
      rw [pth_tan_mul_slice (hdΨ θ hθ) hcos]
      have heq : (Ψ z θ / Real.cos θ ^ 2 + Real.tan θ * Work.Spaces.pth Ψ z θ)
          * Work.Elliptic.sinCos2 θ
          = Real.sin θ * Ψ z θ
            + (Real.tan θ * Work.Elliptic.sinCos2 θ) * Work.Spaces.pth Ψ z θ := by
        rw [Real.tan_eq_sin_div_cos, Work.Elliptic.sinCos2]
        field_simp
      rw [heq]
      have ha : |Real.sin θ * Ψ z θ| ≤ C := by
        rw [abs_mul]
        calc |Real.sin θ| * |Ψ z θ| ≤ 1 * C :=
              mul_le_mul (Real.abs_sin_le_one θ) (hC θ hθ).2 (abs_nonneg _) (by norm_num)
          _ = C := by ring
      have hb : |(Real.tan θ * Work.Elliptic.sinCos2 θ) * Work.Spaces.pth Ψ z θ| ≤ C := by
        rw [abs_mul]
        calc |Real.tan θ * Work.Elliptic.sinCos2 θ| * |Work.Spaces.pth Ψ z θ| ≤ 1 * C :=
              mul_le_mul (abs_tan_mul_sinCos2_le_one hθ)
                (by simpa [Work.Spaces.pth] using (hC θ hθ).1) (abs_nonneg _) (by norm_num)
          _ = C := by ring
      calc |Real.sin θ * Ψ z θ
            + (Real.tan θ * Work.Elliptic.sinCos2 θ) * Work.Spaces.pth Ψ z θ|
          ≤ |Real.sin θ * Ψ z θ|
            + |(Real.tan θ * Work.Elliptic.sinCos2 θ) * Work.Spaces.pth Ψ z θ| := abs_add_le _ _
        _ ≤ C + C := by linarith
        _ = 2 * C := by ring
    exact integrableOn_mul_sinCos2_of_norm_bound
      (by
        show MeasureTheory.AEStronglyMeasurable
          (deriv (fun θ' => Real.tan θ' * Ψ z θ')) (MeasureTheory.volume.restrict Work.Spaces.Iθ)
        exact (measurable_deriv _).aestronglyMeasurable) key
  -- `Lzero Ψ` against `sinθcos²θ`
  have hLzerosg : MeasureTheory.IntegrableOn
      (fun θ => Work.Elliptic.Lzero Ψ z θ * Work.Elliptic.sinCos2 θ) Work.Spaces.Iθ := by
    have hneg : MeasureTheory.IntegrableOn
        (fun θ => -(Work.Spaces.pthIter 2 Ψ z θ) * Work.Elliptic.sinCos2 θ) Work.Spaces.Iθ := by
      refine MeasureTheory.Integrable.congr hMsg.neg ?_
      filter_upwards with θ
      simp only [Pi.neg_apply]
      ring
    have hsix : MeasureTheory.IntegrableOn
        (fun θ => (6 * Ψ z θ) * Work.Elliptic.sinCos2 θ) Work.Spaces.Iθ := by
      refine MeasureTheory.Integrable.congr (hDsg.const_mul 6) ?_
      filter_upwards with θ
      ring
    have hcomb : MeasureTheory.IntegrableOn
        (fun θ => (-(Work.Spaces.pthIter 2 Ψ z θ)
          + Work.Spaces.pth (fun z θ => Real.tan θ * Ψ z θ) z θ - 6 * Ψ z θ)
            * Work.Elliptic.sinCos2 θ) Work.Spaces.Iθ := by
      refine MeasureTheory.Integrable.congr ((hneg.add hTsg).sub hsix) ?_
      filter_upwards with θ
      simp only [Pi.add_apply, Pi.sub_apply]
      ring
    simpa only [Work.Elliptic.Lzero] using hcomb
  -- the right-hand side of the equation against `sinθcos²θ`
  have hRHS : MeasureTheory.IntegrableOn
      (fun θ => (Work.Elliptic.Lzero Ψ z θ - α ^ 2 * z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ
        - F z θ) * Work.Elliptic.sinCos2 θ) Work.Spaces.Iθ := by
    have ha : MeasureTheory.IntegrableOn
        (fun θ => (α ^ 2 * z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) * Work.Elliptic.sinCos2 θ)
        Work.Spaces.Iθ := by
      refine MeasureTheory.Integrable.congr (hAsg.const_mul (α ^ 2)) ?_
      filter_upwards with θ
      ring
    refine MeasureTheory.Integrable.congr ((hLzerosg.sub ha).sub hFsg) ?_
    filter_upwards with θ
    simp only [Pi.sub_apply]
    ring
  -- the equation identifies `∂_zΨ · sinθcos²θ` a.e. with a multiple of the right-hand side
  have hae : (fun θ => (α * (5 + α) * z)⁻¹ * ((Work.Elliptic.Lzero Ψ z θ
        - α ^ 2 * z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ - F z θ)
          * Work.Elliptic.sinCos2 θ))
      =ᵐ[MeasureTheory.volume.restrict Work.Spaces.Iθ]
      (fun θ => Work.Spaces.pz Ψ z θ * Work.Elliptic.sinCos2 θ) := by
    refine Work.FTS.EllipticEst.ae_restrict_Icc_of_forall_Ioo (fun θ hθ => ?_)
    have heq := h.eq z hz θ hθ.1 hθ.2
    rw [Work.Elliptic.bslOp_apply] at heq
    have hden : α * (5 + α) * z ≠ 0 := by
      have : 0 < α * (5 + α) * z := by positivity
      exact ne_of_gt this
    have hkey : Work.Elliptic.Lzero Ψ z θ - α ^ 2 * z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ
        - F z θ = α * (5 + α) * z * Work.Spaces.pz Ψ z θ := by linarith
    show (α * (5 + α) * z)⁻¹ * ((Work.Elliptic.Lzero Ψ z θ
        - α ^ 2 * z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ - F z θ)
          * Work.Elliptic.sinCos2 θ) = Work.Spaces.pz Ψ z θ * Work.Elliptic.sinCos2 θ
    rw [hkey]
    field_simp
  exact (hRHS.const_mul ((α * (5 + α) * z)⁻¹)).congr hae

end Work.FTS.EllipticEst.WeakMoment
