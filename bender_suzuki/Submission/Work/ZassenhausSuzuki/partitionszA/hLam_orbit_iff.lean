import Mathlib
import Submission.Work.ZassenhausSuzuki.Defs

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# The `Λ`-orbit criterion in `A(K,θ)`

For two elements of `A(K,θ)` with non-zero first coordinate, being in the same orbit under the
standard torus `Λ = h(Kˣ)` (`SzA.hLam`) is equivalent to the equality of the invariants
`b / (a · θ a)`.

This refines `Work.ZassenhausSuzuki.orbit_classification` (which exhibits `⟨1,c⟩` as the
representative of every orbit with non-zero first coordinate) and is the combinatorial input for
the Suzuki-partition argument on `A(K,θ)^#` (BG 5.16–5.17 / HB XI 11.11).
-/

set_option autoImplicit false
set_option linter.unusedVariables false

open LeanEval.GroupTheory.Defs
open Submission.Blueprint

namespace Work.ZassenhausSuzuki

/-- **The `Λ`-orbit criterion.** -/
theorem hLam_orbit_iff {K : Type} [Field K] [CharP K 2] (θ : K ≃+* K)
    {x y : SzA K θ} (hx : x.a ≠ 0) (hy : y.a ≠ 0) :
    (∃ lam : Kˣ, y = SzA.hLam θ (lam : K) x) ↔
      y.b / (y.a * θ y.a) = x.b / (x.a * θ x.a) := by
  have hθx : θ x.a ≠ 0 := θ.map_ne_zero_iff.mpr hx
  have hθy : θ y.a ≠ 0 := θ.map_ne_zero_iff.mpr hy
  have hxa : x.a * θ x.a ≠ 0 := mul_ne_zero hx hθx
  have hya : y.a * θ y.a ≠ 0 := mul_ne_zero hy hθy
  constructor
  · rintro ⟨lam, rfl⟩
    have hlam : (lam : K) ≠ 0 := Units.ne_zero lam
    have hθlam : θ (lam : K) ≠ 0 := θ.map_ne_zero_iff.mpr hlam
    simp only [SzA.hLam_a, SzA.hLam_b, map_mul]
    field_simp
  · intro h
    refine ⟨Units.mk0 (y.a / x.a) (div_ne_zero hy hx), ?_⟩
    have h1 : (y.a / x.a) * x.a = y.a := div_mul_cancel₀ y.a hx
    have hcross : y.b * (x.a * θ x.a) = x.b * (y.a * θ y.a) := by
      rw [div_eq_div_iff hya hxa] at h
      exact h
    have h2 : (y.a / x.a * θ (y.a / x.a)) * (x.a * θ x.a) = y.a * θ y.a := by
      rw [show (y.a / x.a * θ (y.a / x.a)) * (x.a * θ x.a)
            = (y.a / x.a * x.a) * (θ (y.a / x.a) * θ x.a) from by ring,
        ← map_mul, h1]
    have hya' : y.b = y.a / x.a * θ (y.a / x.a) * x.b := by
      apply mul_right_cancel₀ hxa
      calc y.b * (x.a * θ x.a) = x.b * (y.a * θ y.a) := hcross
        _ = x.b * ((y.a / x.a * θ (y.a / x.a)) * (x.a * θ x.a)) := by rw [h2]
        _ = y.a / x.a * θ (y.a / x.a) * x.b * (x.a * θ x.a) := by ring
    ext
    · simp only [SzA.hLam_a, Units.val_mk0]
      exact h1.symm
    · simp only [SzA.hLam_b, Units.val_mk0, SzA.hLam_a]
      exact hya'

end Work.ZassenhausSuzuki
