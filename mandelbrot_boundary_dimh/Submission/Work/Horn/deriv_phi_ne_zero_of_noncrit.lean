import Mathlib
import Submission.Work.Interfaces.Parabolic
import Submission.Work.Parab.Setup
import Submission.Work.Parab.inversion.deriv_ne_zero_of_injOn

/-!
# HORN: `deriv φ w ≠ 0` off the critical inverse orbits

Shishikura, §5, last line of the proof of Lemma 5.1:
`φ₀(w) = f₀^n ∘ φ₀(w - n)` for `w ∈ Dom(φ₀)` and `φ'₀ ≠ 0` in `Q₀` (the repelling sector,
where `φ₀` is injective), hence `φ'₀(w) ≠ 0` as soon as the backward orbit
`φ₀(w-1), φ₀(w-2), …` consists of non-critical points.

Formally, for a point `w` of the maximal domain `d.Dφ` of the Fatou coordinate:

* `φ(w) = f₀^n (φ (w - n))` for every `n` (`φ_abel`, `left_inv`), so
  `φ'(w) = (f₀^n)'(φ (w-n)) · φ'(w-n)`; by the chain rule this is a *telescoping product*
  `∏_{j=1}^{n} f₀'(φ (w-j)) · φ'(w-n)`, hence
  `φ'(w) = 0 ⟹ φ'(w-n) = 0` whenever the factors are non-zero.
* `exhaust` supplies an `n` with `w - n ∈ Q₀`, and on the (open) sector `Q₀` the coordinate `φ`
  is injective, so `φ'(w - n) ≠ 0` (`Work.Parab.inversion.deriv_ne_zero_of_injOn`).

The chain rule is used only in its one-step form `φ'(w) = f₀'(φ(w-1)) · φ'(w-1)` below; the
hypothesis `deriv f₀ (φ (w-j)) ≠ 0` (j ≥ 1) also *supplies* the differentiability of `f₀` at the
points `φ(w-j)` (`deriv` is `0` at non-differentiable points).
-/

namespace Work.Horn

open Filter Topology
open scoped Topology

noncomputable section

variable {f₀ : ℂ → ℂ} {D₀ : Set ℂ}

/-- A non-zero value of `deriv` can only come from a genuine derivative: `deriv f z = 0`
whenever `f` is not differentiable at `z`. -/
lemma differentiableAt_of_deriv_ne_zero {f : ℂ → ℂ} {z : ℂ} (h : deriv f z ≠ 0) :
    DifferentiableAt ℂ f z := by
  by_contra hc
  exact h (deriv_zero_of_not_differentiableAt hc)

/-- The backward orbit of a point of `Dφ` stays in `Dφ`: the maximal domain is closed under
`w ↦ w - 1` (`ParabData.left_inv`). -/
lemma sub_nat_mem_Dφ (d : MandelDim.ParabData f₀ D₀) {w : ℂ} (hw : w ∈ d.Dφ) (j : ℕ) :
    w - (j : ℂ) ∈ d.Dφ := by
  induction j with
  | zero => simpa using hw
  | succ m ih =>
      have h : (w - (m : ℂ)) - 1 ∈ d.Dφ := d.left_inv (w - (m : ℂ)) ih
      have harith : (w - (m : ℂ)) - 1 = w - ((m + 1 : ℕ) : ℂ) := by push_cast; ring
      rwa [harith] at h

/-- **One-step chain rule** for the maximally extended Fatou coordinate:
`φ'(w) = f₀'(φ(w-1)) · φ'(w-1)` for `w ∈ Dφ` and `f₀` differentiable at `φ(w-1)`.
Both sides are honest derivatives: `w`, `w - 1 ∈ Dφ` and `Dφ` is open. -/
lemma deriv_phi_step (d : MandelDim.ParabData f₀ D₀) {w : ℂ} (hw : w ∈ d.Dφ)
    (hf : DifferentiableAt ℂ f₀ (d.φ (w - 1))) :
    deriv d.φ w = deriv f₀ (d.φ (w - 1)) * deriv d.φ (w - 1) := by
  have hw1 : w - 1 ∈ d.Dφ := d.left_inv w hw
  have hφ1 : HasDerivAt d.φ (deriv d.φ (w - 1)) (w - 1) :=
    (d.φ_holo.differentiableAt (d.Dφ_open.mem_nhds hw1)).hasDerivAt
  have hshift : HasDerivAt (fun x : ℂ => x - 1) 1 w := (hasDerivAt_id w).sub_const 1
  have hcomp : HasDerivAt (fun x : ℂ => d.φ (x - 1)) (deriv d.φ (w - 1)) w := by
    have h := hφ1.comp w hshift
    simpa [Function.comp_def, mul_one] using h
  have hF : HasDerivAt (fun x : ℂ => f₀ (d.φ (x - 1)))
      (deriv f₀ (d.φ (w - 1)) * deriv d.φ (w - 1)) w := by
    have h := hf.hasDerivAt.comp w hcomp
    simpa [Function.comp_def, mul_one] using h
  have heq : (fun x : ℂ => f₀ (d.φ (x - 1))) =ᶠ[𝓝 w] d.φ := by
    filter_upwards [d.Dφ_open.mem_nhds hw] with x hx
    have hx1 : x - 1 ∈ d.Dφ := d.left_inv x hx
    have h := d.φ_abel (x - 1) hx1 (by simpa using hx)
    simpa using h.symm
  exact (hF.congr_of_eventuallyEq heq.symm).deriv

/-- Zeros of `φ'` propagate to the whole backward orbit `w, w-1, w-2, …`: if `φ'(w) = 0` then
`φ'(w - n) = 0`, provided all the points `φ(w-j)` (`j ≥ 1`) are non-critical points of `f₀`. -/
lemma deriv_phi_eq_zero_sub (d : MandelDim.ParabData f₀ D₀) {w : ℂ} (hw : w ∈ d.Dφ)
    (hnc : ∀ j : ℕ, 1 ≤ j → deriv f₀ (d.φ (w - (j : ℂ))) ≠ 0) :
    ∀ n : ℕ, deriv d.φ w = 0 → deriv d.φ (w - (n : ℂ)) = 0 := by
  intro n
  induction n with
  | zero => intro h; simpa using h
  | succ m ih =>
      intro h
      have hmem : w - (m : ℂ) ∈ d.Dφ := sub_nat_mem_Dφ d hw m
      have harith : (w - (m : ℂ)) - 1 = w - ((m + 1 : ℕ) : ℂ) := by push_cast; ring
      have hf : DifferentiableAt ℂ f₀ (d.φ ((w - (m : ℂ)) - 1)) := by
        rw [harith]
        exact differentiableAt_of_deriv_ne_zero (hnc (m + 1) (by omega))
      have hstep := deriv_phi_step d hmem hf
      rw [ih h] at hstep
      rcases mul_eq_zero.mp hstep.symm with h2 | h2
      · exact absurd (by rwa [harith] at h2) (hnc (m + 1) (by omega))
      · rwa [harith] at h2

set_option linter.unusedVariables false in
theorem deriv_phi_ne_zero_of_noncrit (f₀ : ℂ → ℂ) (D₀ : Set ℂ) (d : MandelDim.ParabData f₀ D₀)
    {w : ℂ} (hw : w ∈ d.Dφ)
    (hD₀ : ∀ j : ℕ, 1 ≤ j → d.φ (w - (j : ℂ)) ∈ D₀)
    (hnc : ∀ j : ℕ, 1 ≤ j → deriv f₀ (d.φ (w - (j : ℂ))) ≠ 0) :
    deriv d.φ w ≠ 0 := by
  obtain ⟨n, hn⟩ := d.exhaust w hw
  have hQdiff : DifferentiableOn ℂ d.φ (MandelDim.QLeft d.ξ₀) := d.φ_holo.mono d.Q_sub
  have hne : deriv d.φ (w - (n : ℂ)) ≠ 0 :=
    Work.Parab.inversion.deriv_ne_zero_of_injOn (Work.Parab.isOpen_QLeft d.ξ₀) hQdiff
      d.φ_inj (w - (n : ℂ)) hn
  intro hzero
  exact hne (deriv_phi_eq_zero_sub d hw hnc n hzero)

end

end Work.Horn
