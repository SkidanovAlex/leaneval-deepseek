import Mathlib.Order.CompletePartialOrder
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Submission.Work.BoseFixB1.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1.chiB_unifDeriv`

The `u`-localised cutoff `χ_{B(u)} = chiB ℓ d u = χ_ℓ · (χ_{ℓd}(· − ℓd·u))`
(FS `eq:chiBdefinition`, corpus `Submission.BoseGases.chiB`) is

* supported in a ball of radius `ℓ/2` around the origin, **uniformly in `u`**
  (the factor `χ_ℓ` already forces `‖z‖ ≤ ℓ/2`), and
* has iterated derivatives of every order `k ≤ 3` bounded by a constant `G k`
  **uniformly in `u`**: the first factor is fixed, and the second one is a
  translate of `χ_{ℓd}` — the iterated derivative of a translate is the
  translate of the iterated derivative (`iteratedFDeriv_comp_sub`), and the
  Leibniz rule `norm_iteratedFDeriv_mul_le` bounds the product.

This is the "uniformly bounded window" input used whenever a
`u`-integral of derivative-carrying quantities has to be interchanged or
estimated.
-/

noncomputable section

open Submission.BoseGases
open scoped ContDiff

namespace Work.BoseFixB1

local notation "E3" => EuclideanSpace ℝ (Fin 3)

theorem chiB_unifDeriv {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d) :
    ∃ R : ℝ, 0 < R ∧ ∃ G : ℕ → ℝ, (∀ k, 0 ≤ G k) ∧
      (∀ (u z : EuclideanSpace ℝ (Fin 3)), Submission.BoseGases.chiB ℓ d u z ≠ 0 → ‖z‖ ≤ R) ∧
      (∀ (u : EuclideanSpace ℝ (Fin 3)) (k : ℕ), k ≤ 3 → ∀ z : EuclideanSpace ℝ (Fin 3),
        ‖iteratedFDeriv ℝ k (fun z => (Submission.BoseGases.chiB ℓ d u z : ℂ)) z‖ ≤ G k) := by
  have hld : 0 < ℓ * d := mul_pos hℓ hd
  -- derivative bounds for the two windows
  obtain ⟨Bl, hBl0, hBl⟩ := exists_iteratedFDeriv_chiScaleC_le hℓ
  obtain ⟨Bd, hBd0, hBd⟩ := exists_iteratedFDeriv_chiScaleC_le hld
  refine ⟨ℓ / 2, by positivity,
    (fun k => ∑ j ∈ Finset.range (k + 1), (k.choose j : ℝ) * Bl j * Bd (k - j)),
    ?_, ?_, ?_⟩
  · -- nonnegativity of `G`
    intro k
    exact Finset.sum_nonneg
      (fun j _ => mul_nonneg (mul_nonneg (by positivity) (hBl0 j)) (hBd0 (k - j)))
  · -- uniform support
    intro u z hz
    have h1 : chiScale ℓ z ≠ 0 := fun h => hz (by simp [chiB, h])
    exact chiScale_support_le hℓ h1
  · -- uniform derivative bounds
    intro u k hk z
    have hf : ContDiff ℝ 3 (fun w : E3 => (chiScale ℓ w : ℂ)) := contDiff_chiScaleC ℓ hℓ
    have hg : ContDiff ℝ 3 (fun w : E3 => (chiScale (ℓ * d) (w - (ℓ * d) • u) : ℂ)) := by
      have h1 : ContDiff ℝ 3 (fun w : E3 => w - (ℓ * d) • u) := contDiff_id.sub contDiff_const
      exact (contDiff_chiScaleC (ℓ * d) hld).comp h1
    have hprod : (fun w : E3 => (chiB ℓ d u w : ℂ))
        = (fun w : E3 => (chiScale ℓ w : ℂ)) *
          (fun w : E3 => (chiScale (ℓ * d) (w - (ℓ * d) • u) : ℂ)) := by
      funext w
      simp only [Pi.mul_apply, chiB]
      push_cast
      ring
    rw [hprod]
    refine le_trans (norm_iteratedFDeriv_mul_le hf hg z (n := k) (by exact_mod_cast hk)) ?_
    refine Finset.sum_le_sum (fun j _ => ?_)
    have h1 : ‖iteratedFDeriv ℝ j (fun w : E3 => (chiScale ℓ w : ℂ)) z‖ ≤ Bl j := hBl j z
    have h2 : ‖iteratedFDeriv ℝ (k - j)
        (fun w : E3 => (chiScale (ℓ * d) (w - (ℓ * d) • u) : ℂ)) z‖ ≤ Bd (k - j) := by
      rw [iteratedFDeriv_comp_sub (f := fun w : E3 => (chiScale (ℓ * d) w : ℂ))
        (k - j) ((ℓ * d) • u) z]
      exact hBd (k - j) (z - (ℓ * d) • u)
    have hb : (0 : ℝ) ≤ (k.choose j : ℝ) * Bl j := mul_nonneg (by positivity) (hBl0 j)
    have h1' : (k.choose j : ℝ) * ‖iteratedFDeriv ℝ j (fun w : E3 => (chiScale ℓ w : ℂ)) z‖
        ≤ (k.choose j : ℝ) * Bl j := mul_le_mul_of_nonneg_left h1 (by positivity)
    exact mul_le_mul h1' h2 (norm_nonneg _) hb

end Work.BoseFixB1
