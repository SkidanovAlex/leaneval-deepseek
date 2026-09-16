import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.NumberTheory.Divisors

namespace Commons.NumberTheory.ArithmeticFunction

open Finset

theorem card_tuples_prod_lcm_eq_le (k M : ℕ) :
    ((Finset.univ : Finset ((Fin k → Fin (M + 1)) × (Fin k → Fin (M + 1)))).filter (fun p =>
      (∀ i : Fin k, 0 < ((p.1 i : ℕ)).lcm ((p.2 i : ℕ))) ∧
      (∏ i : Fin k, ((p.1 i : ℕ)).lcm ((p.2 i : ℕ))) = M)).card ≤
      (M.divisors.card) ^ (3 * k) := by
  classical
  set S := (Finset.univ : Finset ((Fin k → Fin (M + 1)) × (Fin k → Fin (M + 1)))).filter (fun p =>
      (∀ i : Fin k, 0 < ((p.1 i : ℕ)).lcm ((p.2 i : ℕ))) ∧
      (∏ i : Fin k, ((p.1 i : ℕ)).lcm ((p.2 i : ℕ))) = M) with hS
  -- the defining condition of S
  have hcond : ∀ p, p ∈ S → (∀ i : Fin k, 0 < ((p.1 i : ℕ)).lcm ((p.2 i : ℕ))) ∧
      (∏ i : Fin k, ((p.1 i : ℕ)).lcm ((p.2 i : ℕ))) = M := by
    intro p hp
    rw [hS] at hp
    exact (Finset.mem_filter.mp hp).2
  -- lcm value at each coordinate divides M
  have hdvd : ∀ p, p ∈ S → ∀ i : Fin k,
      ((p.1 i : ℕ)).lcm ((p.2 i : ℕ)) ∣ M := by
    intro p hp i
    have hprod := (hcond p hp).2
    have hd : ((p.1 i : ℕ)).lcm ((p.2 i : ℕ)) ∣
        ∏ j : Fin k, ((p.1 j : ℕ)).lcm ((p.2 j : ℕ)) :=
      Finset.dvd_prod_of_mem (fun j : Fin k => ((p.1 j : ℕ)).lcm ((p.2 j : ℕ)))
        (Finset.mem_univ i)
    rw [hprod] at hd
    exact hd
  -- M ≠ 0 for p ∈ S
  have hMne : ∀ p, p ∈ S → M ≠ 0 := by
    intro p hp
    have hpos := (hcond p hp).1
    have hprod := (hcond p hp).2
    have : 0 < ∏ i : Fin k, ((p.1 i : ℕ)).lcm ((p.2 i : ℕ)) :=
      Finset.prod_pos (fun i _ => hpos i)
    omega
  -- the injection: send p to its two components and the lcm-values, all in M.divisors
  let g : {p // p ∈ S} → ((Fin k → M.divisors) × (Fin k → M.divisors)) × (Fin k → M.divisors) :=
    fun x =>
      (((fun i : Fin k => ⟨(x.1.1 i : ℕ),
          Nat.mem_divisors.mpr ⟨(Nat.dvd_lcm_left _ _).trans (hdvd x.1 x.2 i), hMne x.1 x.2⟩⟩
          : Fin k → M.divisors),
        (fun i : Fin k => ⟨(x.1.2 i : ℕ),
          Nat.mem_divisors.mpr ⟨(Nat.dvd_lcm_right _ _).trans (hdvd x.1 x.2 i), hMne x.1 x.2⟩⟩
          : Fin k → M.divisors)),
       (fun i : Fin k => ⟨((x.1.1 i : ℕ)).lcm ((x.1.2 i : ℕ)),
          Nat.mem_divisors.mpr ⟨hdvd x.1 x.2 i, hMne x.1 x.2⟩⟩ : Fin k → M.divisors))
  have hinj : Function.Injective g := by
    intro x y hxy
    have h1 : ∀ i, (x.1.1 i : ℕ) = (y.1.1 i : ℕ) := by
      intro i
      have h := congrFun (congrArg (fun w => w.1.1) hxy) i
      simpa [g] using congrArg Subtype.val h
    have h2 : ∀ i, (x.1.2 i : ℕ) = (y.1.2 i : ℕ) := by
      intro i
      have h := congrFun (congrArg (fun w => w.1.2) hxy) i
      simpa [g] using congrArg Subtype.val h
    have hfst : x.1.1 = y.1.1 := funext fun i => Fin.ext (h1 i)
    have hsnd : x.1.2 = y.1.2 := funext fun i => Fin.ext (h2 i)
    exact Subtype.ext (Prod.ext hfst hsnd)
  have hcard := Fintype.card_le_of_injective g hinj
  have hL : Fintype.card {p // p ∈ S} = S.card := Fintype.card_coe S
  have hR : Fintype.card
      (((Fin k → M.divisors) × (Fin k → M.divisors)) × (Fin k → M.divisors))
      = (M.divisors.card) ^ (3 * k) := by
    have h1 : Fintype.card
        (((Fin k → M.divisors) × (Fin k → M.divisors)) × (Fin k → M.divisors))
        = M.divisors.card ^ k * M.divisors.card ^ k * M.divisors.card ^ k := by
      simp [Fintype.card_prod, Fintype.card_coe, Fintype.card_fin]
    rw [h1, ← pow_add, ← pow_add]
    congr 1
    ring
  calc S.card = Fintype.card {p // p ∈ S} := hL.symm
    _ ≤ Fintype.card (((Fin k → M.divisors) × (Fin k → M.divisors)) × (Fin k → M.divisors)) := hcard
    _ = (M.divisors.card) ^ (3 * k) := hR

end Commons.NumberTheory.ArithmeticFunction