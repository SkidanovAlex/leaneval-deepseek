/-
# `Work.FIArea6Hecke.R.ConductorGaussSumDefs`

The finite-algebra vocabulary for the conductor Gauss sum duality
(`Work.FIArea6Hecke.conductorGaussSumDuality`).

For `M : ℤ[i]`, `M ≠ 0`, with `N = gnorm M`:

* `gdot x y = Re(x · conj y) : ℤ`;
* `ekern M w s = e^{2πi·gdot s w / N}` — the additive character of `ℤ[i]/N` (the kernel of
  `condGaussSum`, with frequency `w`);
* `gbox N = [0,N)² ⊂ ℤ[i]` — the index set over which `condGaussSum` sums;
* `boxSum N f = ∑_{s ∈ gbox N} f s`;
* `IsCRS M S` — `S` is a complete residue system modulo `M`;
* `Gs M chi S a = ∑_{s ∈ S} chi s · e^{2πi·Re(s a / M)}` — the Gauss sum of the multiplicative
  weight `chi` over the CRS `S`, at the *reduced* frequency `a` (this is `Σ_s chi s *
  ekern M (M * star a) s`).

The main duality is stated about `Gs`: for a primitive `chi` mod `M`,
`Gs M chi S a = star (chi a) · Gs M chi S 1` for all `a`, and `Gs M chi S 1 ≠ 0`.
-/
import Mathlib
import Submission.Work.FIArea6Hecke.R.ConductorThetaDefs

set_option autoImplicit false

namespace Work.FIArea6Hecke.R

open scoped BigOperators

noncomputable section

/-- `gdot x y = Re(x · conj y)`. -/
def gdot (x y : GaussianInt) : ℤ := x.re * y.re + x.im * y.im

/-- The additive-character kernel `e^{2πi·gdot s w / N}` with `N = gnorm M`, i.e.
`e^{2πi Re(s·conj w)/N}`.  For `w = ξ` this is exactly the kernel of `condGaussSum M chi ξ`. -/
def ekern (M : GaussianInt) (w s : GaussianInt) : ℂ :=
  Complex.exp
    (((2 * Real.pi * (gdot s w : ℤ) / (Work.FIPlan.gnorm M : ℕ) : ℝ) : ℂ) * Complex.I)

/-- The box `[0,N)² ⊂ ℤ[i]`, the index set of `condGaussSum`. -/
def gbox (N : ℕ) : Finset GaussianInt :=
  ((Finset.range N).product (Finset.range N)).image
    (fun p : ℕ × ℕ => (⟨(p.1 : ℤ), (p.2 : ℤ)⟩ : GaussianInt))

/-- `boxSum N f = ∑_{s ∈ [0,N)²} f s`. -/
def boxSum (N : ℕ) (f : GaussianInt → ℂ) : ℂ := ∑ s ∈ gbox N, f s

/-- `S` is a complete residue system modulo `M`. -/
def IsCRS (M : GaussianInt) (S : Finset GaussianInt) : Prop :=
  ∀ z : GaussianInt, ∃! s : GaussianInt, s ∈ S ∧ M ∣ (z - s)

/-- The Gauss sum of the multiplicative weight `chi` over the complete residue system `S`, at the
reduced frequency `a`: `Gs M chi S a = ∑_{s ∈ S} chi s · e^{2πi·Re(s a / M)}`. -/
def Gs (M : GaussianInt) (chi : GaussianInt → ℂ) (S : Finset GaussianInt)
    (a : GaussianInt) : ℂ :=
  ∑ s ∈ S, chi s * ekern M (M * star a) s

/-! ## Elementary algebra of `gdot` and `ekern` -/

lemma gdot_comm (x y : GaussianInt) : gdot x y = gdot y x := by
  simp only [gdot]
  ring

@[simp] lemma gdot_zero_right (x : GaussianInt) : gdot x 0 = 0 := by simp [gdot]

@[simp] lemma gdot_neg_right (x y : GaussianInt) : gdot x (-y) = -gdot x y := by
  simp only [gdot, Zsqrtd.re_neg, Zsqrtd.im_neg]
  ring

@[simp] lemma ekern_zero (M : GaussianInt) (w : GaussianInt) : ekern M w 0 = 1 := by
  simp [ekern, gdot]

@[simp] lemma ekern_zero_left (M : GaussianInt) (s : GaussianInt) : ekern M 0 s = 1 := by
  simp [ekern, gdot]

lemma norm_ekern (M : GaussianInt) (w s : GaussianInt) : ‖ekern M w s‖ = 1 := by
  rw [ekern]
  exact Complex.norm_exp_ofReal_mul_I _

lemma ekern_add_left (M : GaussianInt) (w w' s : GaussianInt) :
    ekern M (w + w') s = ekern M w s * ekern M w' s := by
  rw [ekern, ekern, ekern, ← Complex.exp_add]
  congr 1
  simp only [gdot, Zsqrtd.re_add, Zsqrtd.im_add]
  push_cast
  ring_nf

lemma ekern_add_right (M : GaussianInt) (w s t : GaussianInt) :
    ekern M w (s + t) = ekern M w s * ekern M w t := by
  rw [ekern, ekern, ekern, ← Complex.exp_add]
  congr 1
  simp only [gdot, Zsqrtd.re_add, Zsqrtd.im_add]
  push_cast
  ring_nf

lemma star_ekern (M : GaussianInt) (w s : GaussianInt) :
    star (ekern M w s) = ekern M (-w) s := by
  have hneg : ekern M (-w) s
      = Complex.exp (-(((2 * Real.pi * (gdot s w : ℤ) / (Work.FIPlan.gnorm M : ℕ) : ℝ) : ℂ)
          * Complex.I)) := by
    rw [ekern]
    congr 1
    simp only [gdot, Zsqrtd.re_neg, Zsqrtd.im_neg]
    push_cast
    ring
  rw [hneg, Complex.exp_neg, Complex.star_def, ← Complex.inv_eq_conj (norm_ekern M w s), ekern]

lemma ekern_mul_star (M : GaussianInt) (w s : GaussianInt) :
    ekern M w s * star (ekern M w s) = 1 := by
  rw [star_ekern, ← ekern_add_left, add_neg_cancel, ekern_zero_left]

end

end Work.FIArea6Hecke.R
