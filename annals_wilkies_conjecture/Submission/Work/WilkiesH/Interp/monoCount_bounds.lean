import Mathlib
import Submission.Work.WilkiesH.Defs

namespace Work.WilkiesH.Interp

/-- `monoCount n d` is the number of exponent vectors `Fin n → Fin (d+1)` with total
degree `≤ d`.  It satisfies the elementary two-sided bounds `≤ (d+1)^n` (it is a subtype
of all such vectors) and `≥ (m+1)^n` with `d = n*m` (every vector with entries `≤ m` has
total degree `≤ n*m`). -/
theorem monoCount_bounds (n d m : ℕ) :
    Work.WilkiesH.monoCount n d ≤ (d + 1) ^ n ∧ (m + 1) ^ n ≤ Work.WilkiesH.monoCount n (n * m) := by
  constructor
  · -- Upper bound: `ExpVec n d` is a subtype of `Fin n → Fin (d+1)`.
    have h := Fintype.card_subtype_le (α := Fin n → Fin (d + 1))
      (fun f => ∑ i, ((f i : ℕ)) ≤ d)
    simpa [Work.WilkiesH.monoCount, Work.WilkiesH.ExpVec, Fintype.card_fun] using h
  · rcases Nat.eq_zero_or_pos n with hn | hn
    · -- `n = 0`: both sides equal `1`.
      subst hn
      simp [Work.WilkiesH.monoCount, Work.WilkiesH.ExpVec]
    · -- Lower bound: any `g : Fin n → Fin (m+1)` has exponent sum `≤ n*m`.
      have hmul : m ≤ n * m := Nat.le_mul_of_pos_left m hn
      have hcast : m + 1 ≤ n * m + 1 := Nat.succ_le_succ hmul
      have key : Fintype.card (Fin n → Fin (m + 1)) ≤
          Fintype.card (Work.WilkiesH.ExpVec n (n * m)) :=
        Fintype.card_le_of_injective
          (fun g : Fin n → Fin (m + 1) => ⟨fun i => Fin.castLE hcast (g i), by
            calc ∑ i, ((Fin.castLE hcast (g i) : Fin (n * m + 1)) : ℕ)
                = ∑ i, ((g i : Fin (m + 1)) : ℕ) := by simp
              _ ≤ ∑ _i : Fin n, m := Finset.sum_le_sum fun i _ => by
                    have := (g i).isLt; omega
              _ = n * m := by simp⟩)
          (by
            intro g g' h
            funext i
            have h2 := congrFun (congrArg Subtype.val h) i
            exact Fin.castLE_injective hcast h2)
      simpa [Work.WilkiesH.monoCount, Fintype.card_fun] using key

end Work.WilkiesH.Interp
