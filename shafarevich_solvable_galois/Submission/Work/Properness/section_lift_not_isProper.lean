import Mathlib
import Submission.Work.Properness.Defs
import Submission.Work.Properness.isProper_iff_map_HK_eq_A
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# A splitting section never gives a proper solution

If the quotient map `π : E →* Q` has a section `σ : Q →* E` (`π ∘ σ = id`), then the
embedding problem along any `ρ : H →* Q` has the solution `ψ = σ ∘ ρ`, and this solution is
proper (surjective) only in the degenerate case where the kernel `A = ker π` is trivial: `σ` is
injective with image a complement of `A`, so it misses every non-trivial element of `A`.

In the paper's language: a *split* embedding problem has a solution for free — the section — but
properness is strictly stronger, and genuinely needs the arithmetic input (Grunwald–Wang).
-/

namespace Work.Properness

set_option autoImplicit true
set_option linter.unusedVariables false

theorem section_lift_not_isProper {u v w : Universe} {S : Work.Properness.Setup.{u, v, w}} (σ : S.Q →* S.E) (hσ : S.π.comp σ = MonoidHom.id S.Q) (hA : S.A ≠ ⊥) : ∃ ψ : S.Lift, (∀ h : S.H, (ψ : S.H → S.E) h = σ (S.ρ h)) ∧ ¬ S.IsProper ψ := by
  -- `σ ∘ ρ` is a lift of `ρ`.
  have hcomp : S.π.comp (σ.comp S.ρ) = S.ρ := by
    ext h
    exact DFunLike.congr_fun hσ (S.ρ h)
  -- The function `h ↦ σ (ρ h)` is not surjective: a non-trivial `a ∈ A` is outside its range,
  -- because `π (σ q) = q` while `π a = 1`.
  have key : ¬ Function.Surjective (fun h : S.H => σ (S.ρ h)) := by
    intro hsurj
    obtain ⟨a, ha⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hA
    obtain ⟨h, hh⟩ := hsurj (a : S.E)
    dsimp only at hh
    have hρh : S.ρ h = 1 := by
      have h1 : S.π (σ (S.ρ h)) = S.ρ h := DFunLike.congr_fun hσ (S.ρ h)
      rw [hh, a.2] at h1
      exact h1.symm
    have : a = 1 := by
      apply Subtype.ext
      show (a : S.E) = 1
      rw [← hh, hρh, map_one]
    exact ha this
  exact ⟨⟨σ.comp S.ρ, hcomp⟩, fun h => rfl, key⟩

end Work.Properness
