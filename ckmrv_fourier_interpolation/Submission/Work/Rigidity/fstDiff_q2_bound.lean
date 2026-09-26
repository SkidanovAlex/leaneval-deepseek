/-
# The first difference of an `AnnT2` function decays like `q²`

This file proves that if `f : ℍ → ℂ` is holomorphic, is annihilated by `(T - I)²`, and
decays like `o(e^{-2π Im τ})` along the strip `-1 ≤ Re τ ≤ 1`, then its first difference
`fstDiff f τ = f(τ+1) - f(τ)` decays like `e^{-4π Im τ}`: in terms of `q = e^{2πiτ}` the
`q`-expansion of `fstDiff f` starts at order `q²`.

The point is the q-expansion argument of the paper: writing `f = u + τ·v` with `u, v`
one-periodic (`v = fstDiff f`) and expanding `f = Σ (b_n + τ a_n) q^n`, the decay of `f`
along the strip forces `a_n = b_n = 0` for `n ≤ 0` and `a_1 = 0`; hence `v = Σ_{n ≥ 2} a_n q^n`.

Formally we avoid q-expansions.  Because `v = fstDiff f` is one-periodic, holomorphic, and
`v = O(ψ(Im τ) q)` with `ψ → 0`, the function `v/q` is one-periodic, holomorphic and tends
to `0` at the cusp; Mathlib's `Function.Periodic.exp_decay_of_zero_at_inf` then gives
`v/q = O(q)`, i.e. `v = O(q²)`.  The translation of `v` to a function on `ℂ` is the
`i`-shifted translate `z ↦ fstDiff f (ofComplex (z + i))`.

## Main result

* `Work.Rigidity.fstDiff_q2_bound`.
-/
import Mathlib
import Submission.Work.Rigidity.Basic
import Submission.Work.Rigidity.Diff
import Submission.Work.Rigidity.PeriodicDecay.periodic_exp_decay_sq_contOn
import Submission.Work.Rigidity.PeriodicDecay.fstDiff_bound_all
import Submission.Work.Rigidity.PeriodicDecay.fstDiff_shift_periodic
import Submission.Work.Rigidity.PeriodicDecay.fstDiff_shift_differentiableOn

namespace Work.Rigidity

open UpperHalfPlane ModularForm ModularGroup Matrix
open scoped MatrixGroups ModularForm Modular Manifold Bundle Topology

open Filter

noncomputable section

theorem fstDiff_q2_bound {f : ℍ → ℂ} (hf : MDiff f) (hT : Work.Rigidity.AnnT2 f)
    (hd : Work.Rigidity.StripDecay 1 f) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ τ : ℍ, 1 ≤ τ.im →
      ‖Work.Rigidity.fstDiff f τ‖ ≤ C * Real.exp (-(4 * Real.pi * τ.im)) := by
  -- the first difference is `1`-periodic
  have hper : ∀ τ : ℍ, fstDiff f ((1 : ℝ) +ᵥ τ) = fstDiff f τ :=
    (fstDiff_vadd_one_iff f).mp hT
  -- the strip decay of `f` gives a strip decay bound for `fstDiff f` ...
  obtain ⟨ψ, hψ, hψbd⟩ := fstDiff_stripDecay hT hd
  -- ... which, by periodicity, holds everywhere
  have hglob : ∀ τ : ℍ, ‖fstDiff f τ‖ ≤ ψ τ.im * Real.exp (-(2 * Real.pi * 1 * τ.im)) :=
    PeriodicDecay.fstDiff_bound_all hper hψbd
  -- the translate of `fstDiff f` to the `ℂ`-plane (shifted by `i` to stay in `ℍ`)
  let V : ℂ → ℂ := fun z => fstDiff f (ofComplex (z + Complex.I))
  have hVper : Function.Periodic V 1 := PeriodicDecay.fstDiff_shift_periodic hT
  have hVdiff : DifferentiableOn ℂ V {z : ℂ | -1 < z.im} :=
    PeriodicDecay.fstDiff_shift_differentiableOn ((UpperHalfPlane.mdifferentiable_iff).mp hf)
  have hVcont : ContinuousOn V {z : ℂ | -1 < z.im} := hVdiff.continuousOn
  have hVhol : ∀ᶠ z : ℂ in Filter.comap Complex.im Filter.atTop, DifferentiableAt ℂ V z := by
    rw [Filter.eventually_comap, Filter.eventually_atTop]
    refine ⟨0, fun b hb z hz => ?_⟩
    have hz1 : (-1 : ℝ) < z.im := by rw [hz]; linarith
    exact hVdiff.differentiableAt
      ((isOpen_lt continuous_const Complex.continuous_im).mem_nhds hz1)
  -- the rescaled weight function
  have hψ' : Tendsto (fun y : ℝ => ψ (y + 1) * Real.exp (-(2 * Real.pi))) atTop (𝓝 0) := by
    have h1 : Tendsto (fun y : ℝ => ψ (y + 1)) atTop (𝓝 0) :=
      hψ.comp (Filter.tendsto_atTop_add_const_right Filter.atTop (1 : ℝ) Filter.tendsto_id)
    simpa using h1.mul_const (Real.exp (-(2 * Real.pi)))
  have hbd : ∀ z : ℂ, 0 < z.im →
      ‖V z‖ ≤ (ψ (z.im + 1) * Real.exp (-(2 * Real.pi))) * Real.exp (-(2 * Real.pi * z.im)) := by
    intro z hz
    have hz1 : 0 < (z + Complex.I).im := by
      simp only [Complex.add_im, Complex.I_im]
      linarith
    have him : (ofComplex (z + Complex.I)).im = z.im + 1 := by
      simp [UpperHalfPlane.ofComplex_apply_of_im_pos hz1]
    have hexp : Real.exp (-(2 * Real.pi * 1 * (z.im + 1)))
        = Real.exp (-(2 * Real.pi)) * Real.exp (-(2 * Real.pi * z.im)) := by
      rw [← Real.exp_add]
      congr 1
      ring
    have h := hglob (ofComplex (z + Complex.I))
    rw [him, hexp] at h
    calc ‖V z‖ = ‖fstDiff f (ofComplex (z + Complex.I))‖ := rfl
      _ ≤ ψ (z.im + 1) * (Real.exp (-(2 * Real.pi)) * Real.exp (-(2 * Real.pi * z.im))) := h
      _ = (ψ (z.im + 1) * Real.exp (-(2 * Real.pi))) * Real.exp (-(2 * Real.pi * z.im)) := by
          ring
  obtain ⟨C, hC0, hC⟩ :=
    PeriodicDecay.periodic_exp_decay_sq_contOn (F := V) hVper hVcont hVhol hψ' hbd
  refine ⟨C * Real.exp (4 * Real.pi), by positivity, fun τ hτ => ?_⟩
  set z : ℂ := (τ : ℂ) - Complex.I with hzdef
  have hz0 : 0 ≤ z.im := by
    rw [hzdef]
    simp only [Complex.sub_im, Complex.I_im, UpperHalfPlane.coe_im]
    linarith
  have h := hC z hz0
  have hVτ : V z = fstDiff f τ := by
    show fstDiff f (ofComplex (z + Complex.I)) = fstDiff f τ
    rw [hzdef, sub_add_cancel, UpperHalfPlane.ofComplex_apply]
  rw [hVτ] at h
  have him : z.im = τ.im - 1 := by
    rw [hzdef]
    simp only [Complex.sub_im, Complex.I_im, UpperHalfPlane.coe_im]
  rw [him] at h
  have hexp : Real.exp (-(4 * Real.pi * (τ.im - 1)))
      = Real.exp (4 * Real.pi) * Real.exp (-(4 * Real.pi * τ.im)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  calc ‖fstDiff f τ‖ ≤ C * Real.exp (-(4 * Real.pi * (τ.im - 1))) := h
    _ = C * (Real.exp (4 * Real.pi) * Real.exp (-(4 * Real.pi * τ.im))) := by rw [hexp]
    _ = (C * Real.exp (4 * Real.pi)) * Real.exp (-(4 * Real.pi * τ.im)) := by ring

end

end Work.Rigidity
