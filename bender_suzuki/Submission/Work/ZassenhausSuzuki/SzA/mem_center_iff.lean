import Mathlib
import Submission.Work.ZassenhausSuzuki.Defs

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.ZassenhausSuzuki.SzA

/-- In Higman's group `A(K,θ)` the centre is `{(0,b)}`, for any `θ ≠ 1`: an element `x` is
central if and only if its first coordinate `x.a` is zero.

The forward direction is where `θ ≠ 1` enters: `x` central forces `x.a * θ c = c * x.a` for all
`c`, and after showing `θ x.a = x.a` this reads `(θ c - c) * x.a = 0`; since a field is
commutative, `x.a ≠ 0` would make `θ = 1`. -/
theorem mem_center_iff {K : Type*} [Field K] (θ : K ≃+* K) (hθ : θ ≠ 1)
    (x : Work.ZassenhausSuzuki.SzA K θ) :
    x ∈ Subgroup.center (Work.ZassenhausSuzuki.SzA K θ) ↔ x.a = 0 := by
  constructor
  · -- `x` central ⟹ `x.a = 0`.
    intro hx
    rw [Subgroup.mem_center_iff] at hx
    -- Testing against `(1,0)` gives `θ x.a = x.a`.
    have hfix : θ x.a = x.a := by
      have h := congrArg (fun y : Work.ZassenhausSuzuki.SzA K θ => y.b)
        (hx (⟨1, 0⟩ : Work.ZassenhausSuzuki.SzA K θ))
      simp only [mul_b, zero_add, add_zero, one_mul, mul_one, map_one] at h
      exact add_left_cancel h
    by_contra hne
    -- Testing against `(c,0)` gives `c * θ x.a = x.a * θ c` for every `c`.
    apply hθ
    ext c
    have hc := congrArg (fun y : Work.ZassenhausSuzuki.SzA K θ => y.b)
      (hx (⟨c, 0⟩ : Work.ZassenhausSuzuki.SzA K θ))
    simp only [mul_b, zero_add, add_zero] at hc
    rw [hfix] at hc
    have hc' : c * x.a = x.a * θ c := add_left_cancel hc
    have h2 : x.a * θ c = x.a * c := by rw [← hc', mul_comm c x.a]
    simpa using mul_left_cancel₀ hne h2
  · -- `x.a = 0` ⟹ `x` central: `x = (0,b)` commutes with everything.
    intro ha
    rw [Subgroup.mem_center_iff]
    intro g
    ext <;> simp [ha, add_comm]

end Work.ZassenhausSuzuki.SzA
