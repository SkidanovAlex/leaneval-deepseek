import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.HallHigman

/-- A block diagonal endomorphism is unipotent of index at most `k` iff both blocks are. -/
theorem pow_sub_one_eq_zero_prodMap {K M N : Type*} [Field K] [AddCommGroup M] [Module K M]
    [AddCommGroup N] [Module K N] (f : Module.End K M) (g : Module.End K N) (k : ℕ) :
    (f.prodMap g - 1) ^ k = 0 ↔ (f - 1) ^ k = 0 ∧ (g - 1) ^ k = 0 := by
  have hpow : ∀ k : ℕ, (f.prodMap g - 1) ^ k = ((f - 1) ^ k).prodMap ((g - 1) ^ k) := by
    intro k
    rw [show f.prodMap g - 1 = (f - 1).prodMap (g - 1) from by
      ext x <;> simp [LinearMap.prodMap_apply]]
    induction k with
    | zero => simp
    | succ n ih => rw [pow_succ, pow_succ, pow_succ, ih, LinearMap.prodMap_mul]
  have hzero : ∀ (a : Module.End K M) (b : Module.End K N),
      a.prodMap b = 0 ↔ a = 0 ∧ b = 0 := by
    intro a b
    constructor
    · intro h
      have ha : a = 0 := by
        ext x
        have hx := congrArg (fun L : M × N →ₗ[K] M × N => (L (x, 0)).1) h
        simpa [LinearMap.prodMap_apply] using hx
      have hb : b = 0 := by
        ext y
        have hy := congrArg (fun L : M × N →ₗ[K] M × N => (L (0, y)).2) h
        simpa [LinearMap.prodMap_apply] using hy
      exact ⟨ha, hb⟩
    · rintro ⟨rfl, rfl⟩
      simp
  rw [hpow k, hzero]

end Work.HallHigman
