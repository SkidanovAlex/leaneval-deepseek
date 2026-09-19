import Mathlib.Data.Complex.Basic
import Mathlib.NumberTheory.DirichletCharacter.Basic
import Submission.Commons.NumberTheory.DirichletCharacter.isPrimitive_inv

open DirichletCharacter

namespace Commons.NumberTheory.DirichletCharacter

/-- A primitive Dirichlet character of level `q ≥ 2` is nontrivial. Indeed, `IsPrimitive`
means the conductor equals the level `q`, while the trivial character has conductor `1`. -/
lemma isPrimitive_ne_one {q : ℕ} (hq : 2 ≤ q) (χ : DirichletCharacter ℂ q)
    (h : χ.IsPrimitive) : χ ≠ 1 := by
  have : NeZero q := ⟨by omega⟩
  intro hχ
  have h1 : conductor χ = 1 := eq_one_iff_conductor_eq_one.mp hχ
  have h2 : conductor χ = q := (isPrimitive_def χ).mp h
  omega

end Commons.NumberTheory.DirichletCharacter