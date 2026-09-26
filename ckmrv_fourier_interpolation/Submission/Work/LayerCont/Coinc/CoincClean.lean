/-
# `j`-cleanliness of the imaginary axis from orbit-exclusion hypotheses

The far-side layer identities remove the two axis intervals

* `I₁` around the *pole* height `t₀` (where the pole `τ - 1` sits for `Re τ < 1`), and
* `I₂` around the *coincidence* height `t₀⁻¹ = 1/τ.im`,

and bound the (re-added) integrals over them via `Work.LayerCont.GapBoundKaxisLow`, which needs
`j`-cleanliness of the compact interval.  On the far side `Re τ > 1` this is *derived*, not
assumed:

* on `I₁` because the swept rectangle `[-ξ₁,0] × [t₀-A₁,t₀+A₁]` is orbit-free (`hcl₁`);
* on `I₂` because the only `SL(2,ℤ)`-translate of `τ` in `[-ξ₂,0] × [t₀⁻¹-A₂,t₀⁻¹+A₂]` is the
  removable coincidence `S • (-1 +ᵥ τ)`, which is off the imaginary axis (`hcoinc`).

The two lemmas below are exactly these derivations, stated uniformly for an arbitrary rectangle.
-/
import Mathlib
import Submission.Work.LayerCont.Coinc.Defs
import Submission.Work.Asymptotics.jInvariantFun_eq_smul_of_eq

set_option maxHeartbeats 800000
set_option linter.unusedVariables false

noncomputable section

open UpperHalfPlane MeasureTheory Filter
open scoped Topology

namespace Work.LayerCont.Coinc

open Work.Asymptotics

/-- The imaginary-axis point `i t` lies in the closed left rectangle as soon as its height does
(its real part `0` is an endpoint of `[-ξ, 0]`). -/
lemma imagAxis_mem_leftRect {c A ξ t : ℝ} (ht : 0 < t) (hξ : 0 < ξ)
    (htI : t ∈ Set.Icc (c - A) (c + A)) :
    Work.Asymptotics.leftRect c A ξ (Work.Kernels.imagAxis t ht) := by
  rw [Work.Asymptotics.leftRect, imagAxis_re t ht, imagAxis_im t ht]
  exact ⟨by linarith, le_rfl, htI.1, htI.2⟩

/-- **`j`-cleanliness of a compact axis piece from orbit-freeness of its rectangle.**

If no `SL(2,ℤ)`-translate of `τ` lies in the closed left rectangle `[-ξ,0] × [c-A,c+A]`, then no
imaginary-axis point of that rectangle has `j`-value `j τ`. -/
theorem jInvariantFun_ne_imagAxis_of_orbitFree (τ : UpperHalfPlane) {c A ξ : ℝ}
    (hcl : ∀ (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) (z : UpperHalfPlane),
        Work.Asymptotics.leftRect c A ξ z → z ≠ γ • τ)
    {t : ℝ} (ht : 0 < t) (hleft : Work.Asymptotics.leftRect c A ξ (Work.Kernels.imagAxis t ht)) :
    Work.Kernels.jInvariantFun τ ≠ Work.Kernels.jInvariantFun (Work.Kernels.imagAxis t ht) := by
  intro hjeq
  obtain ⟨γ, hγ⟩ := Work.Asymptotics.jInvariantFun_eq_smul_of_eq hjeq
  have hz : Work.Kernels.imagAxis t ht = γ⁻¹ • τ := (smul_eq_iff_eq_inv_smul γ).mp hγ
  exact hcl γ⁻¹ (Work.Kernels.imagAxis t ht) hleft hz

/-- **`j`-cleanliness of a compact axis piece from coincidence-cleanliness of its rectangle.**

If the only `SL(2,ℤ)`-translate of `τ` in the closed left rectangle `[-ξ,0] × [c-A,c+A]` is the
removable coincidence, and the coincidence is off the imaginary axis (`(coincℂ τ).re < 0`), then no
imaginary-axis point of that rectangle has `j`-value `j τ`. -/
theorem jInvariantFun_ne_imagAxis_of_coinc (τ : UpperHalfPlane) {c A ξ : ℝ}
    (hcl : ∀ (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) (z : UpperHalfPlane),
        Work.Asymptotics.leftRect c A ξ z →
          (z ≠ γ • τ ∨ z = ModularGroup.S • ((-1 : ℝ) +ᵥ τ)))
    (hre : (coincℂ τ).re < 0)
    {t : ℝ} (ht : 0 < t) (hleft : Work.Asymptotics.leftRect c A ξ (Work.Kernels.imagAxis t ht)) :
    Work.Kernels.jInvariantFun τ ≠ Work.Kernels.jInvariantFun (Work.Kernels.imagAxis t ht) := by
  intro hjeq
  obtain ⟨γ, hγ⟩ := Work.Asymptotics.jInvariantFun_eq_smul_of_eq hjeq
  have hz : Work.Kernels.imagAxis t ht = γ⁻¹ • τ := (smul_eq_iff_eq_inv_smul γ).mp hγ
  rcases hcl γ⁻¹ (Work.Kernels.imagAxis t ht) hleft with h' | h'
  · exact h' hz
  · exact imagAxis_ne_smul_neg_one_vadd hre t ht h'

/-- The real part of the coincidence is negative as soon as the coincidence lies in the open left
rectangle. -/
lemma coincℂ_re_neg_of_mem_openLeftRectℂ {c A ξ : ℝ} {τ : UpperHalfPlane}
    (h : coincℂ τ ∈ Work.Asymptotics.openLeftRectℂ c A ξ) : (coincℂ τ).re < 0 := by
  simp only [Work.Asymptotics.openLeftRectℂ, Set.mem_ofPred_eq] at h
  exact h.2.1

end Work.LayerCont.Coinc
