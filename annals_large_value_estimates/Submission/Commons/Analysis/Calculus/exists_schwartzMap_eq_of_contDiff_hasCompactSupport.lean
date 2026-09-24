import Mathlib.Analysis.Distribution.SchwartzSpace.Basic

namespace Commons.Analysis.Calculus

/-- A smooth compactly supported function from `ℝ` to `ℂ` agrees with a Schwartz function. -/
theorem exists_schwartzMap_eq_of_contDiff_hasCompactSupport {f : ℝ → ℂ}
    (hf : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f) (hcs : HasCompactSupport f) :
    ∃ g : SchwartzMap ℝ ℂ, ∀ x, g x = f x :=
  ⟨hcs.toSchwartzMap hf, fun _ => rfl⟩

end Commons.Analysis.Calculus