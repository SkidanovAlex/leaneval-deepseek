import Mathlib
import Submission.Work.NumberTheory.Chen.BTermCount.BLodDefs
import Submission.Work.NumberTheory.Chen.BTermCount.bRemCorrCharSum

open Finset
open scoped BigOperators

namespace Work.NumberTheory.Chen.BTermCount

open Commons.NumberTheory.Chen.ChenEight

attribute [local instance] Classical.propDecidable

/-!
# Möbius decomposition of the twisted `B̄`-sum at a raised level

The twisted sum `bProdCharSum x M Y (r * e) (changeLevel ψ)` of a character `ψ` of level `r`
raised to level `r * e` vanishes on the `n` which are not coprime to `r * e`.  Since a Dirichlet
character already vanishes on the `n` not coprime to its level `r`, the raised sum is

  `Σ_{n ∈ B̄, (n,e) = 1} ψ n`,

and Möbius inversion (over the divisors of `e`) turns this into the alternating combination
`Σ_{t ∣ e} μ t · Σ_{n ∈ B̄, t ∣ n} ψ n` of the `t`-twisted sums.  The triangle inequality
then bounds its norm by the sum of the norms of the individual `t`-twisted sums.
-/

/-- The `t`-twisted character sum of the ternary sequence `B̄ = bProdSet x M Y`:
the sum of `ψ n` over the `n ∈ B̄` divisible by `t`. -/
noncomputable def bProdCharSumDiv (x M Y r t : ℕ) (ψ : DirichletCharacter ℂ r) : ℂ :=
  ∑ n ∈ (bProdSet x M Y).filter (fun n => t ∣ n), ψ ((n:ℕ) : ZMod r)

/-- **Möbius**: `Σ_{d ∣ m} μ d = 1` if `m = 1` and `0` otherwise. -/
theorem sum_moebius_divisors_eq_ite (m : ℕ) :
    ∑ d ∈ m.divisors, (ArithmeticFunction.moebius d : ℂ) = if m = 1 then 1 else 0 := by
  have h : ((↑ArithmeticFunction.zeta : ArithmeticFunction ℂ) * ↑ArithmeticFunction.moebius) m
      = ((1 : ArithmeticFunction ℂ) m) := by
    rw [ArithmeticFunction.coe_zeta_mul_coe_moebius]
  rw [ArithmeticFunction.coe_zeta_mul_apply] at h
  simp only [ArithmeticFunction.intCoe_apply] at h
  rw [h, ArithmeticFunction.one_apply]

/-- **Möbius inversion of the coprimality indicator**: for `e ≠ 0`,
`1_{(n,e)=1} = Σ_{t ∣ e} μ t · 1_{t ∣ n}`. -/
theorem coprime_ite_eq_sum_moebius_divisors (e n : ℕ) (he : e ≠ 0) :
    (if Nat.Coprime n e then (1:ℂ) else 0)
      = ∑ t ∈ e.divisors, (ArithmeticFunction.moebius t : ℂ) * (if t ∣ n then (1:ℂ) else 0) := by
  have hgcd_ne : Nat.gcd n e ≠ 0 := ne_of_gt (Nat.gcd_pos_of_pos_right n (Nat.pos_of_ne_zero he))
  have hset : e.divisors.filter (fun t => t ∣ n) = (Nat.gcd n e).divisors := by
    ext t
    simp only [Finset.mem_filter, Nat.mem_divisors]
    constructor
    · rintro ⟨⟨hte, -⟩, htn⟩
      exact ⟨Nat.dvd_gcd htn hte, hgcd_ne⟩
    · rintro ⟨htg, -⟩
      exact ⟨⟨Nat.dvd_trans htg (Nat.gcd_dvd_right n e), he⟩,
        Nat.dvd_trans htg (Nat.gcd_dvd_left n e)⟩
  have h1 : (∑ t ∈ e.divisors, (ArithmeticFunction.moebius t : ℂ) * (if t ∣ n then (1:ℂ) else 0))
      = ∑ t ∈ e.divisors.filter (fun t => t ∣ n), (ArithmeticFunction.moebius t : ℂ) := by
    rw [Finset.sum_filter]
    exact Finset.sum_congr rfl (fun t _ => by by_cases h : t ∣ n <;> simp [h])
  rw [h1, hset, sum_moebius_divisors_eq_ite (Nat.gcd n e)]

/-- The Möbius function has complex norm at most `1`. -/
theorem norm_moebius_le_one (t : ℕ) : ‖(ArithmeticFunction.moebius t : ℂ)‖ ≤ 1 := by
  rcases ArithmeticFunction.moebius_eq_or t with h | h | h <;> rw [h] <;> norm_num

/-- `bProdCharSumDiv` as a sum over all of `B̄` with an indicator. -/
theorem bProdCharSumDiv_eq_sum_indicator (x M Y r t : ℕ) (ψ : DirichletCharacter ℂ r) :
    bProdCharSumDiv x M Y r t ψ
      = ∑ n ∈ bProdSet x M Y,
          ψ ((n:ℕ) : ZMod r) * (if t ∣ n then (1:ℂ) else 0) := by
  rw [bProdCharSumDiv, Finset.sum_filter]
  exact Finset.sum_congr rfl (fun n _ => by by_cases h : t ∣ n <;> simp [h])

/-- **The raised-level twisted sum only sees the coprimality to `e`.**  For `r ∣ d` the lift of a
character of level `r` to level `d` vanishes outside the units, and a character already vanishes
outside the units of its own level; hence the twisted sum of the lift equals the twisted sum of `ψ`
restricted to the `n` coprime to `e`. -/
theorem bProdCharSum_changeLevel_eq (x M Y r e : ℕ) [NeZero (r*e)]
    (ψ : DirichletCharacter ℂ r) :
    bProdCharSum x M Y (r*e)
        (DirichletCharacter.changeLevel (R:=ℂ) (n:=r) (m:=r*e) (dvd_mul_right r e) ψ)
      = ∑ n ∈ bProdSet x M Y,
          ψ ((n:ℕ) : ZMod r) * (if Nat.Coprime n e then (1:ℂ) else 0) := by
  unfold bProdCharSum
  refine Finset.sum_congr rfl (fun n _ => ?_)
  rw [changeLevel_apply_nat (dvd_mul_right r e) ψ n]
  by_cases hre : Nat.Coprime n (r*e)
  · rw [if_pos hre]
    have hne : Nat.Coprime n e := hre.coprime_dvd_right (dvd_mul_left e r)
    rw [if_pos hne, mul_one]
  · rw [if_neg hre]
    by_cases hne : Nat.Coprime n e
    · rw [if_pos hne, mul_one]
      have hnr : ¬ Nat.Coprime n r := fun hr => hre (Nat.Coprime.mul_right hr hne)
      exact (MulChar.map_nonunit ψ (fun hu => hnr ((ZMod.isUnit_iff_coprime n r).mp hu))).symm
    · rw [if_neg hne, mul_zero]

/-- **Möbius bound.**  The twisted `B̄`-sum of the lift of `ψ` from level `r` to level `r * e` is an
alternating (Möbius-weighted) combination of the `t`-twisted sums for `t ∣ e`, whence its norm is
at most the sum of the norms of those `t`-twisted sums. -/
theorem BLodMobiusBound (x M Y r e : ℕ) [NeZero (r*e)] (ψ : DirichletCharacter ℂ r) :
    ‖bProdCharSum x M Y (r*e)
        (DirichletCharacter.changeLevel (R:=ℂ) (n:=r) (m:=r*e) (dvd_mul_right r e) ψ)‖
      ≤ ∑ t ∈ e.divisors, ‖bProdCharSumDiv x M Y r t ψ‖ := by
  classical
  have he : e ≠ 0 := fun h => NeZero.ne (r * e) (by rw [h, mul_zero])
  have hmain : bProdCharSum x M Y (r*e)
        (DirichletCharacter.changeLevel (R:=ℂ) (n:=r) (m:=r*e) (dvd_mul_right r e) ψ)
      = ∑ t ∈ e.divisors,
          (ArithmeticFunction.moebius t : ℂ) * bProdCharSumDiv x M Y r t ψ := by
    rw [bProdCharSum_changeLevel_eq]
    -- expand the coprimality indicator by Möbius inversion
    trans ∑ n ∈ bProdSet x M Y,
        ψ ((n:ℕ) : ZMod r)
          * (∑ t ∈ e.divisors,
              (ArithmeticFunction.moebius t : ℂ) * (if t ∣ n then (1:ℂ) else 0))
    · exact Finset.sum_congr rfl (fun n _ => by
        rw [coprime_ite_eq_sum_moebius_divisors e n he])
    · -- distribute and swap the order of summation
      rw [Finset.sum_congr rfl
        (fun n _ => Finset.mul_sum e.divisors (fun t =>
          (ArithmeticFunction.moebius t : ℂ) * (if t ∣ n then (1:ℂ) else 0))
            (ψ ((n:ℕ) : ZMod r)))]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun t _ => ?_)
      have h2 : (∑ n ∈ bProdSet x M Y, ψ ((n:ℕ) : ZMod r)
            * ((ArithmeticFunction.moebius t : ℂ) * (if t ∣ n then (1:ℂ) else 0)))
          = (ArithmeticFunction.moebius t : ℂ)
            * (∑ n ∈ bProdSet x M Y, ψ ((n:ℕ) : ZMod r) * (if t ∣ n then (1:ℂ) else 0)) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun n _ => by ring)
      rw [h2, ← bProdCharSumDiv_eq_sum_indicator x M Y r t ψ]
  rw [hmain]
  calc ‖∑ t ∈ e.divisors,
          (ArithmeticFunction.moebius t : ℂ) * bProdCharSumDiv x M Y r t ψ‖
      ≤ ∑ t ∈ e.divisors,
          ‖(ArithmeticFunction.moebius t : ℂ) * bProdCharSumDiv x M Y r t ψ‖ :=
        norm_sum_le _ _
    _ = ∑ t ∈ e.divisors,
          ‖(ArithmeticFunction.moebius t : ℂ)‖ * ‖bProdCharSumDiv x M Y r t ψ‖ :=
        Finset.sum_congr rfl (fun t _ => norm_mul _ _)
    _ ≤ ∑ t ∈ e.divisors, ‖bProdCharSumDiv x M Y r t ψ‖ :=
        Finset.sum_le_sum (fun t _ =>
          mul_le_of_le_one_left (norm_nonneg _) (norm_moebius_le_one t))

end Work.NumberTheory.Chen.BTermCount
