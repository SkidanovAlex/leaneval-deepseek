import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW.es2

/-- If a finite multiset `t` of complex numbers is stable under the map `z ↦ z ^ p`
(`p > 1`), then every nonzero element of `t` is a root of unity. -/
theorem exists_pow_eq_one_of_multiset_map_pow_eq_self {t : Multiset ℂ} {p : ℕ} (hp : 1 < p)
    (h : t.map (fun z => z ^ p) = t) {z : ℂ} (hz : z ∈ t) (hz0 : z ≠ 0) :
    ∃ m : ℕ, 0 < m ∧ z ^ m = 1 := by
  -- `t` is closed under `w ↦ w ^ p`
  have hstep : ∀ w ∈ t, w ^ p ∈ t := by
    intro w hw
    have h' : w ^ p ∈ t.map (fun z => z ^ p) := by
      rw [Multiset.mem_map]; exact ⟨w, hw, rfl⟩
    rwa [h] at h'
  -- the orbit `k ↦ z ^ (p ^ k)` stays inside `t`
  let f : ℕ → ℂ := fun k => z ^ (p ^ k)
  have hf_mem : ∀ k, f k ∈ t := by
    intro k
    induction k with
    | zero => simpa [f] using hz
    | succ k ih =>
      have hfk : f (k + 1) = (f k) ^ p := by
        simp only [f]
        rw [pow_succ, pow_mul]
      rw [hfk]; exact hstep (f k) ih
  -- pigeonhole: `t.toFinset.card + 1` values inside a set of card `t.toFinset.card`
  let g : Fin (t.toFinset.card + 1) → ↥t.toFinset :=
    fun i => ⟨f (i : ℕ), by rw [Multiset.mem_toFinset]; exact hf_mem (i : ℕ)⟩
  have hcard : Fintype.card ↥t.toFinset < Fintype.card (Fin (t.toFinset.card + 1)) := by
    rw [Fintype.card_coe, Fintype.card_fin]
    exact Nat.lt_succ_self _
  obtain ⟨a, b, hab_ne, hab_eq⟩ := Fintype.exists_ne_map_eq_of_card_lt g hcard
  have hneq : (a : ℕ) ≠ (b : ℕ) := by
    intro hh; exact hab_ne (Fin.ext hh)
  have hval_eq : f (a : ℕ) = f (b : ℕ) := by
    simpa [g] using congrArg Subtype.val hab_eq
  -- from `z ^ (p^s) = z ^ (p^u)` with `s < u` and `z ≠ 0`, get `z ^ (p^u - p^s) = 1`
  have key : ∀ {s u : ℕ}, s < u → z ^ (p ^ s) = z ^ (p ^ u) → z ^ (p ^ u - p ^ s) = 1 := by
    intro s u hsu heq
    have hle : p ^ s ≤ p ^ u := le_of_lt (Nat.pow_lt_pow_right hp hsu)
    have h1 : z ^ (p ^ s) * z ^ (p ^ u - p ^ s) = z ^ (p ^ s) * 1 := by
      rw [mul_one, ← pow_add, Nat.add_sub_of_le hle, heq]
    exact mul_left_cancel₀ (pow_ne_zero _ hz0) h1
  rcases lt_or_gt_of_ne hneq with hlt | hgt
  · refine ⟨p ^ (b : ℕ) - p ^ (a : ℕ),
      Nat.sub_pos_of_lt (Nat.pow_lt_pow_right hp hlt), key hlt hval_eq⟩
  · refine ⟨p ^ (a : ℕ) - p ^ (b : ℕ),
      Nat.sub_pos_of_lt (Nat.pow_lt_pow_right hp hgt), key hgt hval_eq.symm⟩

end Work.BW.es2
