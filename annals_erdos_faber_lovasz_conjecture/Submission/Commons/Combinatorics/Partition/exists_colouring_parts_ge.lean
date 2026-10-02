import Mathlib.Algebra.GroupWithZero.Nat
import Mathlib.Data.Fintype.EquivFin

namespace Commons.Combinatorics.Partition

/-- **Splitting a finite set into `t` parts each of size at least `m`.**

If `t ≥ 1` and `t * m ≤ |ι|`, there is a function `f : ι → Fin t` such that
every part `{i | f i = j}` has at least `m` elements. -/
theorem exists_colouring_parts_ge {ι : Type*} [Fintype ι] [DecidableEq ι]
    (t m : ℕ) (ht : 1 ≤ t) (hm : t * m ≤ Fintype.card ι) :
    ∃ f : ι → Fin t, ∀ j : Fin t,
      m ≤ (Finset.univ.filter (fun i => f i = j)).card := by
  -- Number elements along a fixed enumeration `ι ≃ Fin |ι|` and colour
  -- `x` by `x mod t` (round-robin).  Every colour class then contains at
  -- least `|ι| / t ≥ m` elements.
  have htpos : 0 < t := ht
  let g : Fin (Fintype.card ι) → Fin t := fun x => ⟨x.val % t, Nat.mod_lt x.val htpos⟩
  have hmt : m ≤ Fintype.card ι / t := by
    rw [Nat.le_div_iff_mul_le htpos]
    calc m * t = t * m := Nat.mul_comm _ _
      _ ≤ Fintype.card ι := hm
  refine ⟨fun i => g (Fintype.equivFin ι i), ?_⟩
  intro j
  refine le_trans hmt ?_
  have hcard : Fintype.card {i : ι // g (Fintype.equivFin ι i) = j}
      = (Finset.univ.filter (fun i : ι => g (Fintype.equivFin ι i) = j)).card :=
    Fintype.card_subtype _
  rw [← hcard]
  set e : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι with he
  -- the `k`-th element congruent to `j` modulo `t`
  have hmod : ∀ k : Fin (Fintype.card ι / t), (j.val + k.val * t) % t = j.val := by
    intro k
    rw [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt j.isLt]
  have hbound : ∀ k : Fin (Fintype.card ι / t), j.val + k.val * t < Fintype.card ι := by
    intro k
    have hk : k.val + 1 ≤ Fintype.card ι / t := Nat.succ_le_of_lt k.isLt
    have hmul : (k.val + 1) * t ≤ Fintype.card ι :=
      le_trans (Nat.mul_le_mul_right t hk) (Nat.div_mul_le_self _ _)
    have hmul' : k.val * t + t ≤ Fintype.card ι := by
      rw [Nat.add_mul, one_mul] at hmul
      exact hmul
    omega
  let φ : Fin (Fintype.card ι / t) → {i : ι // g (e i) = j} :=
    fun k => ⟨e.symm ⟨j.val + k.val * t, hbound k⟩, by
      show g (e (e.symm ⟨j.val + k.val * t, hbound k⟩)) = j
      rw [Equiv.apply_symm_apply]
      exact Fin.ext (hmod k)⟩
  have hinj : Function.Injective φ := by
    intro k k' h
    have h1 : (φ k).val = (φ k').val := congrArg Subtype.val h
    have h2 : (⟨j.val + k.val * t, hbound k⟩ : Fin (Fintype.card ι))
        = ⟨j.val + k'.val * t, hbound k'⟩ := by
      have := congrArg e h1
      simpa [φ] using this
    have h3 : j.val + k.val * t = j.val + k'.val * t := congrArg Fin.val h2
    have h4 : k.val * t = k'.val * t := Nat.add_left_cancel h3
    have h5 : k.val = k'.val := Nat.mul_right_cancel htpos h4
    exact Fin.ext h5
  simpa using Fintype.card_le_of_injective φ hinj

end Commons.Combinatorics.Partition