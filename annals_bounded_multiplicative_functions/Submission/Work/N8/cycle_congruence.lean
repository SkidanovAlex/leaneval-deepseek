import Mathlib
import Submission.Work.BMF.Defs
import Submission.Work.BMF.polyrel_basic

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# `Work.N8.cycle_congruence`

Telescoping a cycle of lattice congruences.  If for every `j : Fin m`

`γ_j (p₂ j ·) - γ_{j+1} (p₁ j ·)`  is integral on `ℤ`   (`j+1` read cyclically),

then the product-dilated difference at the base point, `γ_0 ((∏ p₂) ·) - γ_0 ((∏ p₁) ·)`,
is integral on `ℤ`.  This is the "telescoping around each cycle" step of the argument
(MRTTZ Prop. 3.7; step 7 of `Work.BMF.adi_cycles`).
-/

namespace Work.N8

open Polynomial Finset

/-- `∏_{i : Fin m} (if i < t then p₁ i else p₂ i)`: the multiplier obtained from `∏ p₂` after
replacing the factors `p₂ i` by `p₁ i` for `i < t`. -/
def Bprod (m : ℕ) (p₁ p₂ : Fin m → ℕ) (t : ℕ) : ℕ :=
  ∏ i : Fin m, (if (i : ℕ) < t then p₁ i else p₂ i)

lemma Bprod_zero {m : ℕ} {p₁ p₂ : Fin m → ℕ} :
    Bprod m p₁ p₂ 0 = Finset.univ.prod p₂ := by
  simp [Bprod]

lemma Bprod_top {m : ℕ} {p₁ p₂ : Fin m → ℕ} :
    Bprod m p₁ p₂ m = Finset.univ.prod p₁ := by
  simp [Bprod]

/-- Splitting off the `k`-th factor of `Bprod`: `Bprod k = C · p₂ k` and
`Bprod (k+1) = C · p₁ k` for the same multiplier `C` (the product over `i ≠ k`). -/
lemma Bprod_step (m : ℕ) (p₁ p₂ : Fin m → ℕ) (k : Fin m) :
    Bprod m p₁ p₂ (k : ℕ)
        = (∏ i ∈ (Finset.univ : Finset (Fin m)).erase k,
            (if (i : ℕ) < (k : ℕ) then p₁ i else p₂ i)) * p₂ k ∧
    Bprod m p₁ p₂ ((k : ℕ) + 1)
        = (∏ i ∈ (Finset.univ : Finset (Fin m)).erase k,
            (if (i : ℕ) < (k : ℕ) then p₁ i else p₂ i)) * p₁ k := by
  have key : (∏ i ∈ (Finset.univ : Finset (Fin m)).erase k,
      (if (i : ℕ) < (k : ℕ) + 1 then p₁ i else p₂ i))
      = (∏ i ∈ (Finset.univ : Finset (Fin m)).erase k,
          (if (i : ℕ) < (k : ℕ) then p₁ i else p₂ i)) := by
    refine Finset.prod_congr rfl ?_
    intro i hi
    have hne : (i : ℕ) ≠ (k : ℕ) := by
      intro h
      exact (Finset.mem_erase.mp hi).1 (Fin.ext h)
    have hiff : ((i : ℕ) < (k : ℕ) + 1) ↔ ((i : ℕ) < (k : ℕ)) := by
      rw [Nat.lt_succ_iff]
      exact ⟨fun h => lt_of_le_of_ne h hne, fun h => le_of_lt h⟩
    exact if_congr hiff rfl rfl
  refine ⟨?_, ?_⟩ <;> simp only [Bprod]
  · rw [← Finset.mul_prod_erase (Finset.univ : Finset (Fin m))
      (fun i : Fin m => if (i : ℕ) < (k : ℕ) then p₁ i else p₂ i) (Finset.mem_univ k)]
    simp [mul_comm]
  · rw [← Finset.mul_prod_erase (Finset.univ : Finset (Fin m))
      (fun i : Fin m => if (i : ℕ) < (k : ℕ) + 1 then p₁ i else p₂ i) (Finset.mem_univ k)]
    rw [key]
    simp [mul_comm]

/-- Dilating an integer-valued polynomial by a natural number keeps it integer-valued. -/
lemma dil_nat_integral {γ : ℝ[X]} (h : Work.BMF.IntegralOn 1 γ) (n : ℕ) :
    Work.BMF.IntegralOn 1 (Work.BMF.dil (n : ℝ) γ) := by
  intro z
  obtain ⟨m, hm⟩ := h ((n : ℤ) * z)
  refine ⟨m, ?_⟩
  rw [Work.BMF.dil, Polynomial.eval_comp, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_X]
  have hz : (n : ℝ) * (1 * (z : ℝ)) = 1 * (((n : ℤ) * z : ℤ) : ℝ) := by push_cast; ring
  rw [hz]
  exact hm

/-- `dil` is additive on differences. -/
lemma dil_sub_eq (a : ℝ) (P Q : ℝ[X]) :
    Work.BMF.dil a (P - Q) = Work.BMF.dil a P - Work.BMF.dil a Q := by
  rw [Work.BMF.dil, Work.BMF.dil, Work.BMF.dil, Polynomial.sub_comp]

theorem cycle_congruence (m : ℕ) (hm : 1 ≤ m) (γ : Fin m → Polynomial ℝ) (p₁ p₂ : Fin m → ℕ)
    (hrel : ∀ j : Fin m, Work.BMF.IntegralOn 1
      (Work.BMF.dil ((p₂ j : ℕ) : ℝ) (γ j) -
        Work.BMF.dil ((p₁ j : ℕ) : ℝ) (γ ⟨((j : ℕ) + 1) % m, Nat.mod_lt _ (by omega)⟩))) :
    Work.BMF.IntegralOn 1
      (Work.BMF.dil (((Finset.univ.prod p₂ : ℕ)) : ℝ) (γ ⟨0, by omega⟩) -
        Work.BMF.dil (((Finset.univ.prod p₁ : ℕ)) : ℝ) (γ ⟨0, by omega⟩)) := by
  have hm0 : 0 < m := by omega
  -- The telescoped invariant, for all `t ≤ m`:
  --   `dil (Bprod 0) γ_0 - dil (Bprod t) γ_{t mod m} ∈ ℤ`.
  have keyNat : ∀ t : ℕ, t ≤ m → Work.BMF.IntegralOn 1
      (Work.BMF.dil ((Bprod m p₁ p₂ 0 : ℕ) : ℝ) (γ ⟨0, hm0⟩) -
        Work.BMF.dil ((Bprod m p₁ p₂ t : ℕ) : ℝ) (γ ⟨t % m, Nat.mod_lt t hm0⟩)) := by
    intro t
    induction t with
    | zero =>
      intro _
      rw [show (⟨0 % m, Nat.mod_lt 0 hm0⟩ : Fin m) = ⟨0, hm0⟩ from
        Fin.ext (Nat.zero_mod m)]
      rw [sub_self]
      exact Work.BMF.IntegralOn.zero 1
    | succ t ih =>
      intro ht
      have hlt : t < m := by omega
      have ih' := ih (by omega)
      -- the `t`-th relation, multiplied by the common factor `C`
      have hstep : Work.BMF.IntegralOn 1
          (Work.BMF.dil ((Bprod m p₁ p₂ t : ℕ) : ℝ) (γ ⟨t, hlt⟩) -
            Work.BMF.dil ((Bprod m p₁ p₂ (t + 1) : ℕ) : ℝ)
              (γ ⟨(t + 1) % m, Nat.mod_lt (t + 1) hm0⟩)) := by
        have hk := hrel ⟨t, hlt⟩
        set C : ℕ := ∏ i ∈ (Finset.univ : Finset (Fin m)).erase ⟨t, hlt⟩,
            (if (i : ℕ) < t then p₁ i else p₂ i) with hC
        have hC2 := dil_nat_integral hk C
        rw [dil_sub_eq, Work.BMF.dil_mul, Work.BMF.dil_mul] at hC2
        have h1 : (C : ℝ) * (p₂ ⟨t, hlt⟩ : ℝ) = ((Bprod m p₁ p₂ t : ℕ) : ℝ) := by
          rw [← Nat.cast_mul, (Bprod_step m p₁ p₂ ⟨t, hlt⟩).1]
        have h2 : (C : ℝ) * (p₁ ⟨t, hlt⟩ : ℝ) = ((Bprod m p₁ p₂ (t + 1) : ℕ) : ℝ) := by
          rw [← Nat.cast_mul, (Bprod_step m p₁ p₂ ⟨t, hlt⟩).2]
        rw [h1, h2] at hC2
        exact hC2
      have hgoal : (Work.BMF.dil ((Bprod m p₁ p₂ 0 : ℕ) : ℝ) (γ ⟨0, hm0⟩) -
            Work.BMF.dil ((Bprod m p₁ p₂ (t + 1) : ℕ) : ℝ)
              (γ ⟨(t + 1) % m, Nat.mod_lt (t + 1) hm0⟩))
          = (Work.BMF.dil ((Bprod m p₁ p₂ 0 : ℕ) : ℝ) (γ ⟨0, hm0⟩) -
              Work.BMF.dil ((Bprod m p₁ p₂ t : ℕ) : ℝ)
                (γ ⟨t % m, Nat.mod_lt t hm0⟩))
            + (Work.BMF.dil ((Bprod m p₁ p₂ t : ℕ) : ℝ) (γ ⟨t, hlt⟩) -
              Work.BMF.dil ((Bprod m p₁ p₂ (t + 1) : ℕ) : ℝ)
                (γ ⟨(t + 1) % m, Nat.mod_lt (t + 1) hm0⟩)) := by
        rw [show (⟨t % m, Nat.mod_lt t hm0⟩ : Fin m) = ⟨t, hlt⟩ from
          Fin.ext (Nat.mod_eq_of_lt hlt)]
        abel
      rw [hgoal]
      exact ih'.add hstep
  have h := keyNat m le_rfl
  rw [Bprod_zero, Bprod_top] at h
  rw [show (⟨m % m, Nat.mod_lt m hm0⟩ : Fin m) = ⟨0, hm0⟩ from
    Fin.ext (Nat.mod_self m)] at h
  exact h

end Work.N8
