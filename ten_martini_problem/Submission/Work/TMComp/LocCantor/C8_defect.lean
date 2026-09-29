import Mathlib
import Submission.Work.TMComp.LocCantor.C8_jump
import Submission.Work.TMComp.LocCantor.excess_seq
import Submission.Work.TMComp.LocCantor.K2_integral_of_excess
import Submission.Work.TMComp.LocCantor.jump_tendsto_ae
import Submission.Work.TMComp.Kotani.ell_defect_le
import Submission.Work.TMComp.Kotani.cayley_defect

/-!
# C8: (H) ⟹ the defect vanishes a.e. (the `L¹`-jump form)

The chain assembled here is the "defect vanishes" step of the Kotani route
(`RedC8/NOTES_route.md`, `LocCantor/NOTES_C8_jump.md`):

* `excess_seq` turns the integrated form of (H) — `ℓ(E+iε) ≤ C·ε` uniformly on `K` — into a
  sequence `ε_j ↓ 0` with `∫_K g(·,ε_j) → 0`, `g := ℓ/ε - ∂_εℓ`;
* `K2_integral_of_excess` turns that into the `(K2)`-integral smallness
  `∫_{K×(0,1]} K2 → 0` (and the integrability of the integrand);
* `jump_tendsto_ae` (whose key input is the pointwise bound `Psi_jump_cube_le_eight_K2`)
  produces, for a.e. phase `y`, a sequence of heights along which the jump of `cayley ∘ Ψ_y`
  across the real axis is small in `L¹(dE)`.

This is exactly the input of `RedC8.rectangle_extension`, and hence of the reconstruction of
the extension of the `m`-function across the interval.
-/

open MeasureTheory Filter Topology Set
open Work.TMComp.Kotani

noncomputable section

namespace Work.TMComp.LocCantor

/-- The integrand of `∂_ε ℓ` is nonnegative, hence its `y`-integral is. -/
theorem integral_im_neg_one_div_defect_nonneg (α lam : ℝ) {E : ℂ} (hE : 0 < E.im) :
    0 ≤ ∫ y in (0 : ℝ)..1, (-1 / defect α lam E y).im := by
  refine intervalIntegral.integral_nonneg (by norm_num) fun y _ => ?_
  rw [neg_one_div_im (defect_ne_zero α lam hE y)]
  exact div_nonneg (le_of_lt (defect_im_pos α lam hE y)) (by positivity)

/-- **(H) ⟹ the defect vanishes a.e.**  If `ℓ(E+iε) ≤ C·ε` uniformly for `E ∈ K`,
`0 < ε ≤ 1`, then for a.e. phase `y` there is a sequence `ε_j ↓ 0` along which the Euclidean
jump of `cayley ∘ Ψ_y` across the real axis is small in `L¹(dE)` over `K`. -/
theorem jump_tendsto_ae_of_H (α lam : ℝ) {K : Set ℝ} (hK : MeasurableSet K)
    (hKfin : volume K < ⊤)
    (hH : ∃ C : ℝ, 0 < C ∧ ∀ E ∈ K, ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      ell α lam ((E : ℂ) + (ε : ℂ) * Complex.I) ≤ C * ε) :
    ∀ᵐ y ∂((volume : Measure ℝ).restrict (Set.Ioc (0 : ℝ) 1)),
      ∃ e : ℕ → ℝ, (∀ j : ℕ, 0 < e j) ∧ Tendsto e atTop (nhds 0) ∧
        Tendsto (fun j : ℕ => ∫ E in K,
          ‖cayley (Psi α lam ((E : ℂ) + (e j : ℂ) * Complex.I) y)
            - cayley (Psi α lam ((E : ℂ) - (e j : ℂ) * Complex.I) y)‖) atTop (nhds 0) := by
  obtain ⟨C, hCpos, hC⟩ := hH
  obtain ⟨e, he, he0, hexc⟩ := excess_seq α lam hK hKfin ⟨C, hCpos, hC⟩
  -- the excess is bounded above by `C` (since its second term is `≥ 0`)
  have hbound : ∀ j : ℕ, ∀ E ∈ K,
      (ell α lam ((E : ℂ) + (e j : ℂ) * Complex.I) / e j
        - ∫ y in (0 : ℝ)..1, (-1 / defect α lam ((E : ℂ) + (e j : ℂ) * Complex.I) y).im)
      ≤ C := by
    intro j E hE
    have hej : 0 < e j := (he j).1
    have him : 0 < ((E : ℂ) + (e j : ℂ) * Complex.I).im := by
      simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
        Complex.I_re, Complex.I_im, mul_one, add_zero]
      linarith
    have h1 : ell α lam ((E : ℂ) + (e j : ℂ) * Complex.I) / e j ≤ C := by
      rw [div_le_iff₀ hej]
      exact hC E hE (e j) hej (he j).2
    have h2 := integral_im_neg_one_div_defect_nonneg α lam him
    linarith
  -- the `(K2)`-integral smallness (and integrability)
  obtain ⟨hint, hK2⟩ := K2_integral_of_excess α lam hK hKfin e (fun j => (he j).1) hbound hexc
  -- the a.e. phase statement
  exact jump_tendsto_ae α lam hK hKfin e (fun j => (he j).1) he0 hint hK2

end Work.TMComp.LocCantor
