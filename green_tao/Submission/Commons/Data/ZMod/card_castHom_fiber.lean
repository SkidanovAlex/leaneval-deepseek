import Mathlib.Data.ZMod.Basic

namespace Commons.Data.ZMod

/-- The fibre condition for `ZMod.castHom` stated in terms of representatives. -/
lemma castHom_eq_iff_val_mod {m n : ℕ} [NeZero m] [NeZero n] (h : m ∣ n) (c : ZMod m)
    (y : ZMod n) : ZMod.castHom h (ZMod m) y = c ↔ y.val % m = c.val := by
  have h1 : ZMod.castHom h (ZMod m) y = (y.val : ZMod m) := by
    rw [ZMod.castHom_apply]
    exact (ZMod.natCast_val y).symm
  rw [h1]
  constructor
  · intro hc
    have : (y.val : ZMod m) = (c.val : ZMod m) := by rw [hc, ZMod.natCast_zmod_val]
    rw [ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt (ZMod.val_lt c)] at this
    exact this
  · intro hc
    rw [← ZMod.natCast_zmod_val c, ZMod.natCast_eq_natCast_iff',
      Nat.mod_eq_of_lt (ZMod.val_lt c)]
    exact hc

theorem card_castHom_fiber {m n : ℕ} [NeZero m] [NeZero n] (h : m ∣ n) (c : ZMod m) :
    (Finset.univ.filter (fun y : ZMod n => ZMod.castHom h (ZMod m) y = c)).card = n / m := by
  have hm : 0 < m := Nat.pos_of_ne_zero (NeZero.ne m)
  have key : (Finset.univ.filter (fun y : ZMod n => ZMod.castHom h (ZMod m) y = c))
      = (Finset.univ.filter (fun y : ZMod n => y.val % m = c.val)) :=
    Finset.filter_congr (fun y _ => castHom_eq_iff_val_mod h c y)
  have key2 : n / m = (Finset.univ : Finset (Fin (n / m))).card := by
    rw [Finset.card_univ, Fintype.card_fin]
  rw [key, key2]
  refine Finset.card_bij (fun y _ => (⟨y.val / m, ?_⟩ : Fin (n / m))) (fun y _ => Finset.mem_univ _)
    ?_ ?_
  · -- the representative quotient stays below `n / m`
    rw [Nat.div_lt_iff_lt_mul hm, Nat.div_mul_cancel h]
    exact ZMod.val_lt y
  · -- injectivity
    intro y hy z hz h
    have hdiv : y.val / m = z.val / m := congrArg Fin.val h
    have hy' : y.val % m = c.val := (Finset.mem_filter.mp hy).2
    have hz' : z.val % m = c.val := (Finset.mem_filter.mp hz).2
    apply ZMod.val_injective n
    rw [← Nat.div_add_mod y.val m, ← Nat.div_add_mod z.val m, hdiv, hy', hz']
  · -- surjectivity
    intro b _
    have hlt : m * b.val + c.val < n := by
      have h1 : m * b.val + c.val < m * (b.val + 1) := by
        rw [Nat.mul_succ]
        exact Nat.add_lt_add_left (ZMod.val_lt c) _
      have h2 : m * (b.val + 1) ≤ m * (n / m) :=
        Nat.mul_le_mul_left m (Nat.succ_le_of_lt b.isLt)
      exact lt_of_lt_of_le (lt_of_lt_of_le h1 h2) (le_of_eq (Nat.mul_div_cancel' h))
    refine ⟨((m * b.val + c.val : ℕ) : ZMod n), ?_, ?_⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        by rw [ZMod.val_natCast_of_lt hlt, Nat.mul_add_mod, Nat.mod_eq_of_lt (ZMod.val_lt c)]⟩
    · apply Fin.ext
      change ((m * b.val + c.val : ℕ) : ZMod n).val / m = b.val
      rw [ZMod.val_natCast_of_lt hlt, Nat.mul_add_div hm, Nat.div_eq_of_lt (ZMod.val_lt c),
        Nat.add_zero]

end Commons.Data.ZMod