/-
# `qzero f` decays like `exp (-4 π Im τ)`

For `f : ℍ → ℂ` write `v = fstDiff f = f(·+1) - f` and `u = qzero f = f - τ · v`, so that
`f = u + τ · v` with `u` and `v` both one-periodic whenever `(T - I)² f = 0`.

The main analytic input of the rigidity chapter (`lem:noPsolutions`) is that a solution of
`(T - I)² f = 0` whose strip decay is `o(e^{-2π Im τ})` has `q`-expansion of order two: both
`v` and `u` decay like `e^{-4π Im τ}`.  The case of `v` is `Work.Rigidity.fstDiff_q2_bound`;
this file is the case of `u = qzero f`, which enters the proof through the splitting of `f`
into its `S`-eigenspaces.

The argument.  Since `f = u + τ · v` with `v = O(e^{-4π Im τ})` and `f = o(e^{-2π Im τ})` in
the strip, and since `u` is one-periodic, `u` itself is `o(e^{-2π Im τ})`: at a point of the
strip, `‖u τ‖ ≤ φ(im τ) e^{-2π im τ} + (1 + im τ) C e^{-4π im τ}`, and the second term is
`o(e^{-2π im τ})` because `(1 + y) e^{-2π y} → 0`.  Equivalently, the one-periodic holomorphic
function `u / q` (`q = exp (2π i τ)`) tends to `0` at the cusp `i∞`, so it has a `q`-expansion
with vanishing constant term, i.e. `u / q = O(q)`, i.e. `u = O(q²)`.

Formally, this "one extra order of decay for a periodic function vanishing at the cusp" is
exactly the content of `Work.Rigidity.PeriodicDecay.periodic_exp_decay_sq_contOn`: applied to
the pullback `z ↦ u (ofComplex (z + I))` — which is `1`-periodic, continuous on
`{z | -1 < z.im}` and holomorphic at `i∞` — with the weight function
`ψ (y) = (φ (y+1) + (1 + (y+1)) C) e^{-2π}`, it yields `‖u τ‖ ≤ C' e^{-4π im τ}`.

## Main result

* `Work.Rigidity.QzeroOrderTwo`.
-/
import Mathlib
import Submission.Work.Rigidity.TwelvePlusSetup
import Submission.Work.Rigidity.fstDiff_q2_bound
import Submission.Work.Rigidity.PeriodicDecay.periodic_exp_decay_sq_contOn
import Submission.Work.Rigidity.PeriodicDecay.periodic_bound_all
import Submission.Work.Rigidity.PeriodicDecay.periodic_shift_lift_periodic
import Submission.Work.Rigidity.PeriodicDecay.mdiff_shift_lift

noncomputable section

open UpperHalfPlane Filter
open scoped Topology

namespace Work.Rigidity

theorem QzeroOrderTwo {f : UpperHalfPlane → ℂ} (hP : Work.Kernels.InP f)
    (hT2 : Work.Rigidity.AnnT2 f) (hdec : Work.Rigidity.StripDecay 1 f) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ τ : UpperHalfPlane, 1 ≤ τ.im →
      ‖Work.Rigidity.qzero f τ‖ ≤ C * Real.exp (-(4 * Real.pi * τ.im)) := by
  obtain ⟨Cv, hCv0, hCv⟩ := fstDiff_q2_bound hP.1 hT2 hdec
  obtain ⟨φ, hφ, hφ'⟩ := hdec
  -- the weight function of the strip bound for `qzero f`
  set Ψ : ℝ → ℝ := fun y => φ y + (1 + y) * Cv * Real.exp (-(2 * Real.pi * y)) with hΨ
  -- `qzero f = f - τ · fstDiff f` decays like `Ψ (im τ) · q` in the strip
  have hstrip : ∀ τ : UpperHalfPlane, InStrip τ → 1 ≤ τ.im →
      ‖qzero f τ‖ ≤ Ψ τ.im * Real.exp (-(2 * Real.pi * τ.im)) := by
    intro τ hτS hτ1
    have hnorm : ‖(τ : ℂ)‖ ≤ 1 + τ.im := by
      have hre : |τ.re| ≤ 1 := abs_le.mpr ⟨hτS.1, hτS.2⟩
      calc ‖(τ : ℂ)‖ ≤ |(τ : ℂ).re| + |(τ : ℂ).im| := Complex.norm_le_abs_re_add_abs_im _
        _ = |τ.re| + τ.im := by
              rw [UpperHalfPlane.coe_re, UpperHalfPlane.coe_im, abs_of_pos τ.im_pos]
        _ ≤ 1 + τ.im := by linarith
    have h1 : ‖f τ‖ ≤ φ τ.im * Real.exp (-(2 * Real.pi * τ.im)) := by
      simpa using hφ' τ hτS
    have h2 : ‖(τ : ℂ) * fstDiff f τ‖
        ≤ (1 + τ.im) * (Cv * Real.exp (-(4 * Real.pi * τ.im))) := by
      rw [norm_mul]
      exact mul_le_mul hnorm (hCv τ hτ1) (norm_nonneg _) (by linarith)
    rw [qzero_apply]
    have h3 : Real.exp (-(4 * Real.pi * τ.im))
        = Real.exp (-(2 * Real.pi * τ.im)) * Real.exp (-(2 * Real.pi * τ.im)) := by
      rw [← Real.exp_add]; congr 1; ring
    calc ‖f τ - (τ : ℂ) * fstDiff f τ‖ ≤ ‖f τ‖ + ‖(τ : ℂ) * fstDiff f τ‖ := norm_sub_le _ _
      _ ≤ φ τ.im * Real.exp (-(2 * Real.pi * τ.im))
            + (1 + τ.im) * (Cv * Real.exp (-(4 * Real.pi * τ.im))) := add_le_add h1 h2
      _ = Ψ τ.im * Real.exp (-(2 * Real.pi * τ.im)) := by
            rw [hΨ, h3]
            simp only []
            ring
  have hper : ∀ τ : UpperHalfPlane, qzero f ((1 : ℝ) +ᵥ τ) = qzero f τ := qzero_vadd_one hT2
  -- periodicity spreads the strip bound to all of `ℍ` above `Im = 1`
  have hglob : ∀ τ : UpperHalfPlane, 1 ≤ τ.im →
      ‖qzero f τ‖ ≤ Ψ τ.im * Real.exp (-(2 * Real.pi * τ.im)) :=
    Work.Rigidity.PeriodicDecay.periodic_bound_all hper hstrip
  -- pull back to the plane along `z ↦ ofComplex (z + I)`
  set V : ℂ → ℂ := fun z => qzero f (UpperHalfPlane.ofComplex (z + Complex.I)) with hV
  have hVper : Function.Periodic V 1 := by
    rw [hV]
    exact Work.Rigidity.PeriodicDecay.periodic_shift_lift_periodic hper
  have hudiff : DifferentiableOn ℂ (qzero f ∘ UpperHalfPlane.ofComplex) {z : ℂ | 0 < z.im} :=
    UpperHalfPlane.mdifferentiable_iff.mp (inP_qzero hP).1
  have hVlift := Work.Rigidity.PeriodicDecay.mdiff_shift_lift hudiff
  have hVcont : ContinuousOn V {z : ℂ | -1 < z.im} := by
    rw [hV]; exact hVlift.1
  have hVhol : ∀ᶠ z : ℂ in Filter.comap Complex.im Filter.atTop, DifferentiableAt ℂ V z := by
    rw [hV]; exact hVlift.2
  -- the weight function on the plane
  have hφ1 : Tendsto (fun y : ℝ => φ (y + 1)) atTop (𝓝 0) :=
    hφ.comp (Filter.tendsto_atTop_add_const_right Filter.atTop (1 : ℝ) Filter.tendsto_id)
  have hy1 : Tendsto (fun y : ℝ => y * Real.exp (-(2 * Real.pi * y))) atTop (𝓝 0) := by
    have h := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 1 (2 * Real.pi) (by positivity)
    simpa using h
  have hy0 : Tendsto (fun y : ℝ => Real.exp (-(2 * Real.pi * y))) atTop (𝓝 0) := by
    have h := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 0 (2 * Real.pi) (by positivity)
    simpa using h
  have h23 : Tendsto (fun y : ℝ => (y + 2) * Real.exp (-(2 * Real.pi * y))) atTop (𝓝 0) := by
    have h := hy1.add (hy0.const_mul 2)
    simpa [add_mul] using h
  have h2 : Tendsto (fun y : ℝ => (1 + (y + 1)) * Cv * Real.exp (-(2 * Real.pi * (y + 1))))
      atTop (𝓝 0) := by
    have h := h23.const_mul (Cv * Real.exp (-(2 * Real.pi)))
    have hfun : (fun y : ℝ => Cv * Real.exp (-(2 * Real.pi))
          * ((y + 2) * Real.exp (-(2 * Real.pi * y))))
        = fun y : ℝ => (1 + (y + 1)) * Cv * Real.exp (-(2 * Real.pi * (y + 1))) := by
      funext y
      rw [show -(2 * Real.pi * (y + 1)) = -(2 * Real.pi * y) + -(2 * Real.pi) by ring,
        Real.exp_add]
      ring
    rw [hfun] at h
    simpa using h
  have hψ : Tendsto (fun y : ℝ => Ψ (y + 1) * Real.exp (-(2 * Real.pi))) atTop (𝓝 0) := by
    have hsum := (hφ1.add h2).mul_const (Real.exp (-(2 * Real.pi)))
    simpa [hΨ] using hsum
  -- the hypothesis of the `q²`-decay theorem
  have hbd : ∀ z : ℂ, 0 < z.im →
      ‖V z‖ ≤ (Ψ (z.im + 1) * Real.exp (-(2 * Real.pi))) * Real.exp (-(2 * Real.pi * z.im)) := by
    intro z hz
    have hzI : 0 < (z + Complex.I).im := by
      simp only [Complex.add_im, Complex.I_im]; linarith
    have hτim : (UpperHalfPlane.ofComplex (z + Complex.I)).im = z.im + 1 := by
      rw [← UpperHalfPlane.coe_im, UpperHalfPlane.ofComplex_apply_of_im_pos hzI]
      simp only [Complex.add_im, Complex.I_im]
    have h1 : 1 ≤ (UpperHalfPlane.ofComplex (z + Complex.I)).im := by rw [hτim]; linarith
    have h := hglob (UpperHalfPlane.ofComplex (z + Complex.I)) h1
    rw [hτim] at h
    have hVz : V z = qzero f (UpperHalfPlane.ofComplex (z + Complex.I)) := by rw [hV]
    rw [hVz]
    refine le_trans h (le_of_eq ?_)
    rw [show -(2 * Real.pi * (z.im + 1)) = -(2 * Real.pi * z.im) + -(2 * Real.pi) by ring,
      Real.exp_add]
    ring
  obtain ⟨C, hC0, hC⟩ :=
    Work.Rigidity.PeriodicDecay.periodic_exp_decay_sq_contOn hVper hVcont hVhol hψ hbd
  refine ⟨C * Real.exp (4 * Real.pi), by positivity, fun τ hτ => ?_⟩
  set z : ℂ := (τ : ℂ) - Complex.I with hzdef
  have hz0 : 0 ≤ z.im := by
    rw [hzdef]
    simp only [Complex.sub_im, Complex.I_im, UpperHalfPlane.coe_im]
    linarith
  have h := hC z hz0
  have hVτ : V z = qzero f τ := by
    rw [hV, hzdef]
    show qzero f (UpperHalfPlane.ofComplex ((τ : ℂ) - Complex.I + Complex.I)) = qzero f τ
    rw [sub_add_cancel, UpperHalfPlane.ofComplex_apply]
  rw [hVτ] at h
  have him : z.im = τ.im - 1 := by
    rw [hzdef]
    simp only [Complex.sub_im, Complex.I_im, UpperHalfPlane.coe_im]
  rw [him] at h
  have hexp : Real.exp (-(4 * Real.pi * (τ.im - 1)))
      = Real.exp (4 * Real.pi) * Real.exp (-(4 * Real.pi * τ.im)) := by
    rw [← Real.exp_add]; congr 1; ring
  calc ‖qzero f τ‖ ≤ C * Real.exp (-(4 * Real.pi * (τ.im - 1))) := h
    _ = C * (Real.exp (4 * Real.pi) * Real.exp (-(4 * Real.pi * τ.im))) := by rw [hexp]
    _ = (C * Real.exp (4 * Real.pi)) * Real.exp (-(4 * Real.pi * τ.im)) := by ring

end Work.Rigidity
