import Mathlib
import Submission.Work.LinnikBurgess.frame_step_defs

/-!
# Auxiliary lemmas for the multi-prime frame step (`frame_step_card_d`)

This file contains the elementary local input used by the frame step: a unit of `ZMod (p ^ k)`
has at most three cube roots.  The two ingredients are

* in a *commutative* group, the solutions of `x ^ 3 = a` are a coset of the group
  `{u | u ^ 3 = 1}` of cube roots of unity (`fcd_card_pow_eq_le_of_kernel`);
* the cube roots of unity in `(ZMod (p ^ k))ˣ` are at most three: for odd `p` the unit group is
  cyclic (`ZMod.isCyclic_units_of_prime_pow`, so `IsCyclic.card_pow_eq_one_le` applies), while
  for `p = 2` the group has order `2 ^ (k-1)`, which is coprime to `3`.
-/

open scoped BigOperators
open Finset

namespace Work.LinnikBurgess

open Polynomial

/-- `a2` is admissible for the frame `(a0, a1, b)` at the prime power `p ^ k`: there is a `y`
which is a `p`-adic unit for all six shifts `y + a l`, `y + b l` and at which both `critN` and its
derivative vanish modulo `p ^ k`. -/
def fcd_frameAdm (p k : ℕ) (a0 a1 : ℕ) (b : Fin 3 → ℕ) (a2 : ℕ) : Prop :=
  ∃ y : ℕ, UnitAt p y ![a0, a1, a2] b
    ∧ ((p ^ k : ℕ) : ℤ) ∣ (critN ![a0, a1, a2] b).eval (y : ℤ)
    ∧ ((p ^ k : ℕ) : ℤ) ∣ (Polynomial.derivative (critN ![a0, a1, a2] b)).eval (y : ℤ)

/-- In a commutative group, the solutions of `x ^ 3 = a` are a coset of the cube roots of unity. -/
theorem fcd_card_pow_eq_le_of_kernel {G : Type*} [CommGroup G] [Fintype G] [DecidableEq G]
    {D : ℕ} (hK : ((Finset.univ : Finset G).filter (fun u => u ^ 3 = 1)).card ≤ D) (a : G) :
    ((Finset.univ : Finset G).filter (fun x => x ^ 3 = a)).card ≤ D := by
  by_cases hne : ((Finset.univ : Finset G).filter (fun x => x ^ 3 = a)).Nonempty
  · obtain ⟨x0, hx0⟩ := hne
    have hx03 : x0 ^ 3 = a := (Finset.mem_filter.mp hx0).2
    have hcard : ((Finset.univ : Finset G).filter (fun x => x ^ 3 = a)).card
        = ((Finset.univ : Finset G).filter (fun u => u ^ 3 = 1)).card := by
      refine Finset.card_bij (fun x _ => x0⁻¹ * x) ?_ ?_ ?_
      · intro x hx
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
        rw [mul_pow, hx, inv_pow, hx03, inv_mul_cancel]
      · intro x _ y _ h
        simpa using mul_left_cancel h
      · intro y hy
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢
        exact ⟨x0 * y, by rw [mul_pow, hy, hx03, mul_one], by group⟩
    omega
  · have h0 : ((Finset.univ : Finset G).filter (fun x => x ^ 3 = a)) = ∅ :=
      Finset.not_nonempty_iff_eq_empty.mp hne
    simp [h0]

/-- The cube roots of unity in `(ZMod (2 ^ k))ˣ`: at most three (in fact at most one). -/
theorem fcd_cube_one_units_card_le_three_two (k : ℕ) :
    ((Finset.univ : Finset (ZMod (2 ^ k))ˣ).filter (fun u => u ^ 3 = 1)).card ≤ 3 := by
  rcases Nat.eq_zero_or_pos k with hk | hk
  · subst hk
    calc ((Finset.univ : Finset (ZMod (2 ^ 0))ˣ).filter (fun u => u ^ 3 = 1)).card
        ≤ Fintype.card (ZMod (2 ^ 0))ˣ := Finset.card_le_univ _
      _ = 1 := by rw [ZMod.card_units_eq_totient]; simp
      _ ≤ 3 := by norm_num
  · have hsub : ((Finset.univ : Finset (ZMod (2 ^ k))ˣ).filter (fun u => u ^ 3 = 1)) ⊆ {1} := by
      intro u hu
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu
      simp only [Finset.mem_singleton]
      haveI : NeZero (2 ^ k) := ⟨pow_ne_zero k (by omega)⟩
      have h3 : orderOf u ∣ 3 := orderOf_dvd_iff_pow_eq_one.mpr hu
      have hc : orderOf u ∣ Nat.card (ZMod (2 ^ k))ˣ := orderOf_dvd_natCard u
      have hcard : Nat.card (ZMod (2 ^ k))ˣ = 2 ^ (k - 1) := by
        rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient]
        obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
        rw [Nat.totient_prime_pow_succ Nat.prime_two]
        simp
      rw [hcard] at hc
      have hnd : ¬ 3 ∣ 2 ^ (k - 1) := by
        intro hd
        have h32 : (3 : ℕ) ∣ 2 := Nat.Prime.dvd_of_dvd_pow Nat.prime_three hd
        omega
      have hcop : Nat.Coprime 3 (2 ^ (k - 1)) :=
        (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hnd
      have h1 : orderOf u ∣ 1 := by
        have := Nat.dvd_gcd h3 hc
        rwa [hcop.gcd_eq_one] at this
      simpa [orderOf_eq_one_iff] using Nat.dvd_one.mp h1
    calc ((Finset.univ : Finset (ZMod (2 ^ k))ˣ).filter (fun u => u ^ 3 = 1)).card
        ≤ ({1} : Finset _).card := Finset.card_le_card hsub
      _ = 1 := by simp
      _ ≤ 3 := by norm_num

/-- The cube roots of unity in `(ZMod (p ^ k))ˣ` are at most three. -/
theorem fcd_cube_one_units_card_le_three (p k : ℕ) [Fact p.Prime] :
    ((Finset.univ : Finset (ZMod (p ^ k))ˣ).filter (fun u => u ^ 3 = 1)).card ≤ 3 := by
  rcases eq_or_ne p 2 with h2 | h2
  · subst h2; exact fcd_cube_one_units_card_le_three_two k
  · have hp : p.Prime := Fact.out
    haveI : IsCyclic (ZMod (p ^ k))ˣ := ZMod.isCyclic_units_of_prime_pow p hp h2 k
    have h := IsCyclic.card_pow_eq_one_le (α := (ZMod (p ^ k))ˣ) (n := 3) (by norm_num)
    simpa using h

/-- **A unit of `ZMod (p ^ k)` has at most three cube roots.** -/
theorem fcd_cube_root_card_le_three (p k : ℕ) [Fact p.Prime] (a : ZMod (p ^ k))
    (ha : IsUnit a) :
    ((Finset.univ : Finset (ZMod (p ^ k))).filter (fun x => x ^ 3 = a)).card ≤ 3 := by
  have hunit : ∀ x : ZMod (p ^ k), x ^ 3 = a → IsUnit x := by
    intro x hx
    rw [isUnit_iff_dvd_one] at ha ⊢
    exact dvd_trans (dvd_pow_self x (by norm_num)) (hx ▸ ha)
  have hmain : ((Finset.univ : Finset (ZMod (p ^ k))).filter (fun x => x ^ 3 = a)).card
      ≤ ((Finset.univ : Finset (ZMod (p ^ k))ˣ).filter (fun u => u ^ 3 = ha.unit)).card := by
    refine Finset.card_le_card_of_injOn
      (fun x : ZMod (p ^ k) => if h : IsUnit x then h.unit else 1) ?_ ?_
    · intro x hx
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
      have hun : IsUnit x := hunit x hx
      simp only [dif_pos hun]
      apply Units.ext
      show ((hun.unit : (ZMod (p ^ k))ˣ) : ZMod (p ^ k)) ^ 3 = ((ha.unit : (ZMod (p ^ k))ˣ) : ZMod (p ^ k))
      rw [IsUnit.unit_spec hun, IsUnit.unit_spec ha, hx]
    · intro x hx y hy hxy
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hx hy
      have hunx : IsUnit x := hunit x hx
      have huny : IsUnit y := hunit y hy
      simp only [dif_pos hunx, dif_pos huny] at hxy
      have : (x : ZMod (p ^ k)) = (y : ZMod (p ^ k)) := by
        rw [← IsUnit.unit_spec hunx, ← IsUnit.unit_spec huny, hxy]
      exact this
  exact le_trans hmain
    (fcd_card_pow_eq_le_of_kernel (fcd_cube_one_units_card_le_three p k) ha.unit)

end Work.LinnikBurgess
