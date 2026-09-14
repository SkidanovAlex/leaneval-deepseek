import Mathlib

set_option linter.style.haveILetI false

namespace Commons.NumberTheory.FriedlanderIwaniec

lemma sq_roots_neg_one_count_eq_fin_count {n : ℕ} (hn : 0 < n) :
    ({α : ZMod n | α ^ 2 = -1}.ncard) =
      ({x : Fin n | n ∣ (x : ℕ) ^ 2 + 1}.ncard) := by
  haveI : NeZero n := ⟨hn.ne'⟩
  let f : Fin n → ZMod n := fun x => (x : ℕ)
  have hf_inj : Function.Injective f := by
    intro x y hxy
    simp only [f] at hxy
    have h : (x : ℕ) = (y : ℕ) := by
      have h' : (x : ℕ) % n = (y : ℕ) % n := (ZMod.natCast_eq_natCast_iff' _ _ _).mp hxy
      rwa [Nat.mod_eq_of_lt x.isLt, Nat.mod_eq_of_lt y.isLt] at h'
    exact Fin.ext h
  have himg : f '' {x : Fin n | n ∣ (x : ℕ) ^ 2 + 1} = {α : ZMod n | α ^ 2 = -1} := by
    ext α
    constructor
    · rintro ⟨x, hx, rfl⟩
      change ((x : ℕ) : ZMod n) ^ 2 = -1
      have h0 : (((x : ℕ) ^ 2 + 1 : ℕ) : ZMod n) = 0 :=
        (ZMod.natCast_eq_zero_iff ((x : ℕ) ^ 2 + 1) n).mpr hx
      push_cast at h0
      rw [eq_neg_iff_add_eq_zero]
      exact h0
    · intro hα
      refine ⟨⟨α.val, α.val_lt⟩, ?_, ?_⟩
      · have h0 : ((α.val ^ 2 + 1 : ℕ) : ZMod n) = 0 := by
          rw [Nat.cast_add, Nat.cast_pow, Nat.cast_one, ZMod.natCast_zmod_val, hα]
          ring
        exact (ZMod.natCast_eq_zero_iff (α.val ^ 2 + 1) n).mp h0
      · change ((α.val : ℕ) : ZMod n) = α
        exact ZMod.natCast_zmod_val α
  calc
    ({α : ZMod n | α ^ 2 = -1}.ncard)
        = (f '' {x : Fin n | n ∣ (x : ℕ) ^ 2 + 1}).ncard := by rw [himg]
    _ = ({x : Fin n | n ∣ (x : ℕ) ^ 2 + 1}).ncard :=
          Set.ncard_image_of_injective _ hf_inj

end Commons.NumberTheory.FriedlanderIwaniec
