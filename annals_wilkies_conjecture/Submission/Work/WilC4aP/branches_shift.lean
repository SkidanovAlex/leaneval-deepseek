import Mathlib
import Submission.Work.WilC4aP.Basic
import Submission.Work.WilC4aP.PzAlg

namespace Work.WilC4aP

open Polynomial

/-- Substituting `X ↦ X + C b` into `X - C a` yields `X - C (a - b)`.  This is the
linear change of variable that "unshifts" a root production. -/
lemma sub_C_comp_X_add_C (a b : ℂ) :
    (X - C a : ℂ[X]).comp (X + C b) = X - C (a - b) := by
  rw [Polynomial.sub_comp, Polynomial.X_comp, Polynomial.C_comp, Polynomial.C_sub]
  ring

lemma branches_shift {m : ℕ} (P : Polynomial (ℂ → ℂ)) (d : ℂ → ℂ) {N : ℕ} (η : Fin m → ℂ → ℂ)
    {ρ : ℝ} (hρ : 0 < ρ)
    (hfact : ∀ u ∈ Metric.ball (0 : ℂ) ρ,
      Pz (P.comp (Polynomial.X + Polynomial.C d)) (u ^ N) =
        ∏ j, (Polynomial.X - Polynomial.C (η j u))) :
    ∀ u ∈ Metric.ball (0 : ℂ) ρ, Pz P (u ^ N) = ∏ j, (Polynomial.X - Polynomial.C (η j u + d (u ^ N))) := by
  intro u hu
  -- The fibre of `P` after the shift by `d (u ^ N)` is the factored product.
  have hkey := hfact u hu
  rw [Pz_comp_X_add_C] at hkey
  -- Unshift: substitution of `X + C (d (u ^ N))` is injective on `ℂ[X]`.
  have hgoal : (Pz P (u ^ N)).comp (X + C (d (u ^ N))) =
      (∏ j, (X - C (η j u + d (u ^ N)))).comp (X + C (d (u ^ N))) := by
    rw [hkey, Polynomial.prod_comp]
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [sub_C_comp_X_add_C, add_sub_cancel_right]
  exact comp_X_add_C_injective (d (u ^ N)) hgoal

end Work.WilC4aP
