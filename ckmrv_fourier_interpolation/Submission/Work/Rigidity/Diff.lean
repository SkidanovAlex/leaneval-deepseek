/-
# The first difference of an `AnnT2` function

A function killed by `(T − I)²` is encoded by its first difference

  `fstDiff f τ = f(τ+1) − f(τ)`,

which is periodic of period one.  Every proof of `lem:noPsolutions` starts by splitting
`f = u + τ·v` with `u, v` one-periodic (`v = fstDiff f`, `u = f − τ·v`); the point of this
file is that the strip decay of `f` is inherited by `v`, so that the two periodic pieces
are subject to the same bound.

## Main results

* `Work.Rigidity.fstDiff` : the first difference.
* `Work.Rigidity.fstDiff_vadd_one_iff` : `fstDiff f` is `1`-periodic iff `(T − I)² f = 0`.
* `Work.Rigidity.fstDiff_stripDecay` : the first difference inherits `StripDecay`.
* `Work.Rigidity.sub_smul_fstDiff_periodic` : `u = f − τ·fstDiff f` is `1`-periodic.
-/
import Mathlib
import Submission.Work.Rigidity.Basic

noncomputable section

open UpperHalfPlane ModularForm ModularGroup Matrix
open scoped MatrixGroups ModularForm Modular Manifold Bundle Topology

namespace Work.Rigidity

open Filter

/-- The first difference `fstDiff f τ = f(τ + 1) - f(τ)`. -/
def fstDiff (f : ℍ → ℂ) : ℍ → ℂ := fun τ => f ((1 : ℝ) +ᵥ τ) - f τ

lemma fstDiff_apply (f : ℍ → ℂ) (τ : ℍ) :
    fstDiff f τ = f ((1 : ℝ) +ᵥ τ) - f τ := rfl

/-- `(T − I)² f = 0` says exactly that `fstDiff f` has period one. -/
theorem fstDiff_vadd_one_iff (f : ℍ → ℂ) :
    AnnT2 f ↔ ∀ τ : ℍ, fstDiff f ((1 : ℝ) +ᵥ τ) = fstDiff f τ := by
  constructor
  · intro hf τ
    have h := congrFun hf τ
    simp only [Work.Kernels.T2op, Pi.zero_apply] at h
    rw [fstDiff_apply, fstDiff_apply, ← Work.Kernels.vadd_one_add_one]
    linear_combination h
  · intro h
    funext τ
    have hh := h τ
    simp only [Work.Kernels.T2op, Pi.zero_apply]
    rw [fstDiff_apply, fstDiff_apply, ← Work.Kernels.vadd_one_add_one] at hh
    linear_combination hh

lemma im_vadd (x : ℝ) (τ : ℍ) : (x +ᵥ τ).im = τ.im := by
  rw [← UpperHalfPlane.coe_im, UpperHalfPlane.coe_vadd, ← UpperHalfPlane.coe_im,
    Complex.add_im, Complex.ofReal_im, zero_add]

lemma re_vadd (x : ℝ) (τ : ℍ) : (x +ᵥ τ).re = x + τ.re := by
  rw [← UpperHalfPlane.coe_re, UpperHalfPlane.coe_vadd, ← UpperHalfPlane.coe_re,
    Complex.add_re, Complex.ofReal_re]

lemma vadd_sub_vadd (τ : ℍ) : (1 : ℝ) +ᵥ ((-1 : ℝ) +ᵥ τ) = τ := by
  rw [UpperHalfPlane.ext_iff]
  simp only [UpperHalfPlane.coe_vadd]
  push_cast
  ring

/-- The first difference inherits the strip decay: for `τ` in the strip one may shift `τ`
by an integer (periodicity of `fstDiff`) so that both `τ` and `τ + 1` lie in the strip. -/
theorem fstDiff_stripDecay {c : ℝ} {f : ℍ → ℂ} (hf : AnnT2 f) (hd : StripDecay c f) :
    StripDecay c (fstDiff f) := by
  obtain ⟨φ, hφ, hφ'⟩ := hd
  have hper : ∀ u : ℍ, fstDiff f ((1 : ℝ) +ᵥ u) = fstDiff f u :=
    (fstDiff_vadd_one_iff f).mp hf
  refine ⟨fun y => 2 * φ y, by simpa using hφ.const_mul 2, fun τ hτ => ?_⟩
  rcases lt_or_ge τ.re 0 with hlt | hge
  · have h2 : InStrip ((1 : ℝ) +ᵥ τ) :=
      ⟨by rw [re_vadd]; linarith [hτ.1], by rw [re_vadd]; linarith [hτ.2]⟩
    have h1 := hφ' τ hτ
    have h2' := hφ' ((1 : ℝ) +ᵥ τ) h2
    rw [im_vadd] at h2'
    rw [fstDiff_apply]
    calc ‖f ((1 : ℝ) +ᵥ τ) - f τ‖ ≤ ‖f ((1 : ℝ) +ᵥ τ)‖ + ‖f τ‖ := norm_sub_le _ _
      _ ≤ φ τ.im * Real.exp (-(2 * Real.pi * c * τ.im))
            + φ τ.im * Real.exp (-(2 * Real.pi * c * τ.im)) := add_le_add h2' h1
      _ = (2 * φ τ.im) * Real.exp (-(2 * Real.pi * c * τ.im)) := by ring
  · set u : ℍ := (-1 : ℝ) +ᵥ τ with hu
    have hure : u.re = -1 + τ.re := by rw [hu, re_vadd]
    have huim : u.im = τ.im := by rw [hu, im_vadd]
    have hstep : fstDiff f τ = fstDiff f u := by
      have h := hper u
      rw [hu, vadd_sub_vadd] at h
      exact h
    have h1 : InStrip u := ⟨by rw [hure]; linarith, by rw [hure]; linarith [hτ.2]⟩
    have h2 : InStrip ((1 : ℝ) +ᵥ u) :=
      ⟨by rw [re_vadd, hure]; linarith [hτ.1], by rw [re_vadd, hure]; linarith [hτ.2]⟩
    have hA := hφ' u h1
    have hB := hφ' ((1 : ℝ) +ᵥ u) h2
    rw [im_vadd, huim] at hB
    rw [huim] at hA
    rw [hstep, fstDiff_apply]
    calc ‖f ((1 : ℝ) +ᵥ u) - f u‖ ≤ ‖f ((1 : ℝ) +ᵥ u)‖ + ‖f u‖ := norm_sub_le _ _
      _ ≤ φ τ.im * Real.exp (-(2 * Real.pi * c * τ.im))
            + φ τ.im * Real.exp (-(2 * Real.pi * c * τ.im)) := add_le_add hB hA
      _ = (2 * φ τ.im) * Real.exp (-(2 * Real.pi * c * τ.im)) := by ring

/-- `u = f − τ·fstDiff f` is periodic of period one whenever `(T − I)² f = 0`; together
with `Work.Rigidity.fstDiff` this is the splitting `f = u + τ·v` with `u, v` one-periodic. -/
theorem sub_smul_fstDiff_periodic {f : ℍ → ℂ} (hf : AnnT2 f) :
    ∀ τ : ℍ, f ((1 : ℝ) +ᵥ τ) - (((1 : ℝ) +ᵥ τ : ℍ) : ℂ) * fstDiff f ((1 : ℝ) +ᵥ τ)
      = f τ - (τ : ℂ) * fstDiff f τ := by
  intro τ
  have hv : fstDiff f ((1 : ℝ) +ᵥ τ) = fstDiff f τ := (fstDiff_vadd_one_iff f).mp hf τ
  rw [hv, UpperHalfPlane.coe_vadd, fstDiff_apply]
  push_cast
  ring

end Work.Rigidity
