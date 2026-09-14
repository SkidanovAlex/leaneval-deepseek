import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Data.Nat.GCD.BigOperators
import Mathlib.Data.ZMod.Basic
import Submission.Commons.NumberTheory.Nat.crt_combination_bijective

set_option linter.style.haveILetI false
namespace Commons.Data.ZMod

open scoped BigOperators

theorem crt_combination_reduction (s : Finset ℕ) (_hprime : ∀ p ∈ s, Nat.Prime p)
    (n : ℕ) (p₀ : ℕ) (hp₀ : p₀ ∈ s) (a : ∀ p : {p // p ∈ s}, Fin n → ZMod (p : ℕ))
    (i : Fin n) :
    ((∑ p : {p // p ∈ s}, (((a p i).val : ℕ) : ZMod (∏ p ∈ s, p)) *
        (((∏ p ∈ s, p) / (p : ℕ) : ℕ) : ZMod (∏ p ∈ s, p)))).val % p₀ = 0
      ↔ a ⟨p₀, hp₀⟩ i = 0 := by
  classical
  have hp0prime : Nat.Prime p₀ := _hprime p₀ hp₀
  haveI : NeZero p₀ := ⟨hp0prime.ne_zero⟩
  set M : ℕ := ∏ p ∈ s, p with hM
  have hMpos : 0 < M := by
    rw [hM]
    exact Finset.prod_pos (fun p hp => (_hprime p hp).pos)
  haveI : NeZero M := ⟨ne_of_gt hMpos⟩
  have hdvd : p₀ ∣ M := by
    rw [hM]
    exact Finset.dvd_prod_of_mem (fun x : ℕ => x) hp₀
  -- Casting each summand down to `ZMod p₀`.
  have hterm : ∀ p : {p // p ∈ s},
      ZMod.castHom hdvd (ZMod p₀)
          ((((a p i).val : ℕ) : ZMod M) * (((M / (p : ℕ) : ℕ) : ℕ) : ZMod M))
        = (((a p i).val : ℕ) : ZMod p₀) * (((M / (p : ℕ) : ℕ) : ℕ) : ZMod p₀) := by
    intro p
    rw [map_mul, map_natCast, map_natCast]
  have hzero : ∀ p : {p // p ∈ s}, p ≠ ⟨p₀, hp₀⟩ →
      (((M / (p : ℕ) : ℕ) : ℕ) : ZMod p₀) = 0 := by
    intro p hpne
    rw [ZMod.natCast_eq_zero_iff]
    have hp_pos : 0 < (p : ℕ) := (_hprime p p.property).pos
    have hprod := Finset.prod_erase_mul s (fun x : ℕ => x) p.property
    have hMdiv : M / (p : ℕ) = ∏ x ∈ s.erase (p : ℕ), x := by
      rw [hM, ← hprod]
      exact Nat.mul_div_cancel _ hp_pos
    rw [hMdiv]
    apply Finset.dvd_prod_of_mem (fun x : ℕ => x)
    rw [Finset.mem_erase]
    exact ⟨fun h => hpne (Subtype.ext h.symm), hp₀⟩
  have hcast : ZMod.castHom hdvd (ZMod p₀)
      (∑ p : {p // p ∈ s}, (((a p i).val : ℕ) : ZMod M) *
        (((M / (p : ℕ) : ℕ) : ℕ) : ZMod M))
      = a ⟨p₀, hp₀⟩ i * (((M / p₀ : ℕ) : ℕ) : ZMod p₀) := by
    rw [map_sum]
    rw [Finset.sum_congr rfl (fun p _ => hterm p)]
    rw [Finset.sum_eq_single (s := Finset.univ) (⟨p₀, hp₀⟩ : {p // p ∈ s})]
    · rw [ZMod.natCast_zmod_val]
    · intro p _ hpne
      rw [hzero p hpne, mul_zero]
    · intro h
      exact absurd (Finset.mem_univ _) h
  -- The factor `M / p₀` is a unit mod `p₀`.
  have hu : IsUnit (((M / p₀ : ℕ) : ℕ) : ZMod p₀) := by
    rw [ZMod.isUnit_iff_coprime]
    have hp_pos : 0 < p₀ := hp0prime.pos
    have hprod := Finset.prod_erase_mul s (fun x : ℕ => x) hp₀
    have hMdiv : M / p₀ = ∏ x ∈ s.erase p₀, x := by
      rw [hM, ← hprod]
      exact Nat.mul_div_cancel _ hp_pos
    rw [hMdiv]
    apply Nat.Coprime.prod_left
    intro x hx
    obtain ⟨hxne, hxs⟩ := Finset.mem_erase.mp hx
    exact (Nat.coprime_primes (_hprime x hxs) hp0prime).mpr hxne
  have key : ZMod.castHom hdvd (ZMod p₀)
        (∑ p : {p // p ∈ s}, (((a p i).val : ℕ) : ZMod M) *
          (((M / (p : ℕ) : ℕ) : ℕ) : ZMod M)) = 0
      ↔ a ⟨p₀, hp₀⟩ i = 0 := by
    rw [hcast]
    constructor
    · intro h
      have h2 : a ⟨p₀, hp₀⟩ i * (((M / p₀ : ℕ) : ℕ) : ZMod p₀) =
          0 * (((M / p₀ : ℕ) : ℕ) : ZMod p₀) := by rw [h, zero_mul]
      exact (IsUnit.mul_left_inj hu).mp h2
    · intro h; rw [h, zero_mul]
  rw [← key]
  rw [ZMod.castHom_apply, ZMod.cast_eq_val]
  rw [ZMod.natCast_eq_zero_iff]
  exact ⟨Nat.dvd_of_mod_eq_zero, Nat.mod_eq_zero_of_dvd⟩

end Commons.Data.ZMod