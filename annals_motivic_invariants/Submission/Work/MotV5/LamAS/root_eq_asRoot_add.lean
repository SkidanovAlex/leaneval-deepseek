import Mathlib
import Submission.Work.MotV5.Defs
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The roots of the Artin–Schreier polynomial `X⁵ - X - g`

`Work.MotV5.asRoot g` is one root of `X⁵ - X - g` in `Kb 𝕜 = AlgebraicClosure (RatFunc 𝕜)`
(`Work.MotV5.asRoot_spec`).  This file identifies **all** of them: in characteristic `5` the
differences of two roots of `X⁵ - X - g` are exactly the elements of the prime field `𝔽₅`, i.e.
the Artin–Schreier map `℘(x) = x⁵ - x` has kernel `𝔽₅ = {0,1,2,3,4}`:

* `exists_fin_five_of_pow_five_sub_eq_zero` — in any field `K` of characteristic `5`, every `a`
  with `a⁵ - a = 0` is the image of some `k : Fin 5`;
* `root_eq_asRoot_add` — every `β` with `β⁵ - β = g` is `asRoot g + k` for some `k : Fin 5`.

The proof of the first statement is elementary: `a⁵ - a = a (a⁴ - 1)`, and in characteristic `5`
the quartic factors as `a⁴ - 1 = (a - 1)(a - 2)(a - 3)(a - 4)` (pairing the outermost and the
innermost factor: `(a - 1)(a - 4) = a² - 1`, `(a - 2)(a - 3) = a² + 1`, using `5 = 0` and
`4 = -1`, `6 = 1` in `ℤ/5`).  The Artin–Schreier map is additive in characteristic `5`
(`sub_pow_char`), which transfers this to differences of roots.
-/

set_option autoImplicit false

namespace Work.MotV5.LamAS

/-- **The kernel of `℘(x) = x⁵ - x` in characteristic `5` is the prime field.**  Every `a` of a
field `K` of characteristic `5` with `a⁵ - a = 0` is the image of some `k : Fin 5`. -/
theorem exists_fin_five_of_pow_five_sub_eq_zero {K : Type*} [Field K] [CharP K 5] (a : K)
    (ha : a ^ 5 - a = 0) : ∃ k : Fin 5, a = ((k : Fin 5) : K) := by
  have h5 : (5 : K) = 0 := CharP.cast_eq_zero K 5
  have h4 : (4 : K) = -1 := by
    rw [eq_neg_iff_add_eq_zero, show (4 : K) + 1 = (5 : K) by norm_num, h5]
  have h6 : (6 : K) = 1 := by
    rw [show (6 : K) = (5 : K) + 1 by norm_num, h5, zero_add]
  rcases eq_or_ne a 0 with h0 | h0
  · exact ⟨0, by rw [h0]; simp⟩
  · -- `a ≠ 0`, so `a⁵ = a` gives `a⁴ = 1`, whence `(a-1)(a-2)(a-3)(a-4) = a⁴ - 1 = 0`.
    have h4a : a ^ 4 = 1 := by
      have hm : a * a ^ 4 = a * 1 := by
        rw [mul_one, ← pow_succ', ← sub_eq_zero]
        exact ha
      exact mul_left_cancel₀ h0 hm
    have hA : (a - 1) * (a - 4) = a ^ 2 - 1 := by
      have h : (a - 1) * (a - 4) = a ^ 2 - a * 5 + 4 := by ring
      rw [h, h5, h4]
      first | refl_ring1 | ring
    have hB : (a - 2) * (a - 3) = a ^ 2 + 1 := by
      have h : (a - 2) * (a - 3) = a ^ 2 - a * 5 + 6 := by ring
      rw [h, h5, h6]
      first | refl_ring1 | ring
    have hfac : (a - 1) * (a - 2) * (a - 3) * (a - 4) = 0 := by
      have hperm : (a - 1) * (a - 2) * (a - 3) * (a - 4)
          = ((a - 1) * (a - 4)) * ((a - 2) * (a - 3)) := by ring
      have h : (a - 1) * (a - 2) * (a - 3) * (a - 4) = a ^ 4 - 1 := by
        rw [hperm, hA, hB]
        first | refl_ring1 | ring
      rw [h, h4a, sub_self]
    rcases mul_eq_zero.mp hfac with h123 | h4''
    · rcases mul_eq_zero.mp h123 with h12 | h3
      · rcases mul_eq_zero.mp h12 with h1 | h2
        · exact ⟨1, by rw [sub_eq_zero.mp h1]; norm_num⟩
        · exact ⟨2, by rw [sub_eq_zero.mp h2]; norm_num⟩
      · exact ⟨3, by rw [sub_eq_zero.mp h3]; norm_num⟩
    · exact ⟨4, by rw [sub_eq_zero.mp h4'']; norm_num⟩

/-- **All roots of `X⁵ - X - g` differ from `asRoot g` by an element of the prime field `𝔽₅`.**

The Artin–Schreier map `℘(x) = x⁵ - x` is additive in characteristic `5`
(`(x - y)⁵ = x⁵ - y⁵`), so `β - asRoot g` lies in the kernel of `℘`, which is the prime field by
`exists_fin_five_of_pow_five_sub_eq_zero`. -/
theorem root_eq_asRoot_add {𝕜 : Type} [Field 𝕜] [CharP 𝕜 5]
    (g : RatFunc 𝕜) {β : Work.MotV.Kb 𝕜}
    (hβ : β ^ 5 - β = algebraMap (RatFunc 𝕜) (Work.MotV.Kb 𝕜) g) :
    ∃ k : Fin 5, β = Work.MotV5.asRoot g + algebraMap ℤ (Work.MotV.Kb 𝕜) ((k : Fin 5) : ℤ) := by
  have hfact : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  -- `β - asRoot g` is killed by `℘`
  have hα : (β - Work.MotV5.asRoot g) ^ 5 - (β - Work.MotV5.asRoot g) = 0 := by
    have hkey : (β - Work.MotV5.asRoot g) ^ 5 - (β - Work.MotV5.asRoot g)
        = (β ^ 5 - β) - ((Work.MotV5.asRoot g) ^ 5 - Work.MotV5.asRoot g) := by
      rw [sub_pow_char]
      first | refl_ring1 | ring
    rw [hkey, hβ, Work.MotV5.asRoot_spec g, sub_self]
  obtain ⟨k, hk⟩ := exists_fin_five_of_pow_five_sub_eq_zero (β - Work.MotV5.asRoot g) hα
  rw [sub_eq_iff_eq_add] at hk
  refine ⟨k, ?_⟩
  rw [hk, show ((k : Fin 5) : Work.MotV.Kb 𝕜)
      = algebraMap ℤ (Work.MotV.Kb 𝕜) ((k : Fin 5) : ℤ) from by simp, add_comm]

end Work.MotV5.LamAS
