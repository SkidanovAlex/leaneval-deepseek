import Mathlib
import Submission.Work.NumberTheory.Chen.BTermCount.BLodAssembly
import Submission.Work.NumberTheory.Chen.BTermCount.BLodMobiusBound

namespace Work.NumberTheory.Chen.BTermCount

attribute [local instance] Classical.propDecidable

/-!
# The character reduction for the `B̄`-term level of distribution

The main bound `BLodCharReduction` replaces, in the totient-weighted sum over odd `d ≤ D`
of the corrected remainders, the primitive-character sum at the raised level `d`

  `Σ_{c ∣ d, c ≥ 2} Σ_{ψ primitive mod c} ‖bProdCharSum x M Y d (changeLevel_{c→d} ψ)‖`

by the sum of the `t`-twisted sums at the *conductor* level `c`:

  `Σ_{c ∣ d, c ≥ 2} Σ_{t ∣ d/c} bProdCharSumDivSum x M Y t c`.

The point of the reduction is that the twisted sums at level `c` involve only
`t ∣ d / c ≤ D` divisors, so that the bilinear (large-sieve) estimates can be
applied at level `c` rather than at the raised level `d`.

The mathematical content is the Möbius inversion of the coprimality indicator:
for `c ∣ d` and any character `ψ` of level `c`,

  `bProdCharSum x M Y d (changeLevel_{c→d} ψ) = Σ_{t ∣ d/c} μ t · bProdCharSumDiv x M Y c t ψ`,

whence the triangle inequality.  This generalizes `BLodMobiusBound`, which is
stated only for the concrete level `r * e` with the divisibility proof
`dvd_mul_right r e`, to an arbitrary level `d` together with an arbitrary proof
of `c ∣ d` — this is what allows the reduction to be applied directly at the
levels occurring in the target statement.
-/

/-- **The change-of-level evaluation at an arbitrary divisible level.**  For `r ∣ d` the lift
of `ψ` from level `r` to level `d` is `ψ` on the integers coprime to `d` and `0` on the others;
since the lift is already gone once `n` is not coprime to `d = r · (d/r)`, the twisted sum over
`B̄` is the `(d/r)`-coprime part of the `ψ`-twisted sum at level `r`. -/
theorem bProdCharSum_changeLevel_eq_gen (x M Y r d : ℕ) [NeZero d] (h : r ∣ d)
    (ψ : DirichletCharacter ℂ r) :
    bProdCharSum x M Y d (DirichletCharacter.changeLevel h ψ)
      = ∑ n ∈ bProdSet x M Y,
          ψ ((n:ℕ) : ZMod r) * (if Nat.Coprime n (d / r) then (1:ℂ) else 0) := by
  have hd : r * (d / r) = d := Nat.mul_div_cancel' h
  unfold bProdCharSum
  refine Finset.sum_congr rfl (fun n _ => ?_)
  rw [changeLevel_apply_nat h ψ n]
  by_cases hcd : Nat.Coprime n d
  · rw [if_pos hcd, if_pos (hcd.coprime_dvd_right (Nat.div_dvd_of_dvd h)), mul_one]
  · rw [if_neg hcd]
    by_cases hce : Nat.Coprime n (d / r)
    · rw [if_pos hce, mul_one]
      have hnr : ¬ Nat.Coprime n r := fun hr => hcd (hd ▸ hr.mul_right hce)
      exact (MulChar.map_nonunit ψ (fun hu => hnr ((ZMod.isUnit_iff_coprime n r).mp hu))).symm
    · rw [if_neg hce, mul_zero]

/-- **Möbius bound at an arbitrary divisible level.**  The twisted `B̄`-sum of the lift of `ψ`
from level `r` to a level `d` which is a multiple of `r` is an alternating (Möbius-weighted)
combination of the `t`-twisted sums for `t ∣ d / r`, whence its norm is at most the sum of the
norms of those `t`-twisted sums. -/
theorem bProdMobiusBound_gen (x M Y r d : ℕ) [NeZero d] (h : r ∣ d)
    (ψ : DirichletCharacter ℂ r) :
    ‖bProdCharSum x M Y d (DirichletCharacter.changeLevel h ψ)‖
      ≤ ∑ t ∈ (d / r).divisors, ‖bProdCharSumDiv x M Y r t ψ‖ := by
  classical
  have hd : r * (d / r) = d := Nat.mul_div_cancel' h
  have he : d / r ≠ 0 := by
    intro h0
    exact NeZero.ne d (by rw [← hd, h0, mul_zero])
  have hmain : bProdCharSum x M Y d (DirichletCharacter.changeLevel h ψ)
      = ∑ t ∈ (d / r).divisors,
          (ArithmeticFunction.moebius t : ℂ) * bProdCharSumDiv x M Y r t ψ := by
    rw [bProdCharSum_changeLevel_eq_gen x M Y r d h ψ]
    trans ∑ n ∈ bProdSet x M Y,
        ψ ((n:ℕ) : ZMod r)
          * (∑ t ∈ (d / r).divisors,
              (ArithmeticFunction.moebius t : ℂ) * (if t ∣ n then (1:ℂ) else 0))
    · exact Finset.sum_congr rfl (fun n _ => by
        rw [coprime_ite_eq_sum_moebius_divisors (d / r) n he])
    · rw [Finset.sum_congr rfl
        (fun n _ => Finset.mul_sum (d / r).divisors (fun t =>
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
  calc ‖∑ t ∈ (d / r).divisors,
          (ArithmeticFunction.moebius t : ℂ) * bProdCharSumDiv x M Y r t ψ‖
      ≤ ∑ t ∈ (d / r).divisors,
          ‖(ArithmeticFunction.moebius t : ℂ) * bProdCharSumDiv x M Y r t ψ‖ :=
        norm_sum_le _ _
    _ = ∑ t ∈ (d / r).divisors,
          ‖(ArithmeticFunction.moebius t : ℂ)‖ * ‖bProdCharSumDiv x M Y r t ψ‖ :=
        Finset.sum_congr rfl (fun t _ => norm_mul _ _)
    _ ≤ ∑ t ∈ (d / r).divisors, ‖bProdCharSumDiv x M Y r t ψ‖ :=
        Finset.sum_le_sum (fun t _ =>
          mul_le_of_le_one_left (norm_nonneg _) (norm_moebius_le_one t))

/-- **The per-conductor reduction.**  For `c ∣ d`, the sum over the primitive characters of
level `c` of the norms of the twisted sums of their lifts to level `d` is at most the sum over
`t ∣ d / c` of the `t`-twisted primitive-character sums at level `c`. -/
theorem bProdCharSumDivSum_le_divisors (x M Y d c : ℕ) [NeZero d] (h : c ∣ d) :
    (∑ ψ : {ψ' : DirichletCharacter ℂ c // ψ'.IsPrimitive},
        ‖bProdCharSum x M Y d (DirichletCharacter.changeLevel h ψ.1)‖)
      ≤ ∑ t ∈ (d / c).divisors, bProdCharSumDivSum x M Y t c := by
  have hL : (∑ ψ : {ψ' : DirichletCharacter ℂ c // ψ'.IsPrimitive},
        ‖bProdCharSum x M Y d (DirichletCharacter.changeLevel h ψ.1)‖)
      = ∑ ψ ∈ (Finset.univ.filter (fun ψ : DirichletCharacter ℂ c => ψ.IsPrimitive)),
          ‖bProdCharSum x M Y d (DirichletCharacter.changeLevel h ψ)‖ := by
    rw [← Finset.sum_subtype_eq_sum_filter (s := Finset.univ)
      (f := fun ψ : DirichletCharacter ℂ c =>
        ‖bProdCharSum x M Y d (DirichletCharacter.changeLevel h ψ)‖)]
    simp [Finset.subtype_univ]
  rw [hL]
  simp only [bProdCharSumDivSum]
  rw [Finset.sum_comm]
  exact Finset.sum_le_sum (fun ψ _ => bProdMobiusBound_gen x M Y c d h ψ)

attribute [local instance] Classical.propDecidable
theorem BLodCharReduction (x M Y D : ℕ) (hD : 2 ≤ D) :
    (∑ d ∈ (Finset.Icc 1 D).filter (fun d => d % 2 = 1),
        ((3:ℝ)^(d.primeFactors.card) / (Nat.totient d : ℝ)) *
          (∑ c ∈ (d.divisors.attach.filter (fun c => 2 ≤ c.1)),
            ∑ ψ : {ψ' : DirichletCharacter ℂ c.1 // ψ'.IsPrimitive},
              ‖Work.NumberTheory.Chen.BTermCount.bProdCharSum x M Y d
                (DirichletCharacter.changeLevel (Nat.mem_divisors.mp c.2).1 ψ.1)‖))
      ≤ ∑ d ∈ (Finset.Icc 1 D).filter (fun d => d % 2 = 1),
          ((3:ℝ)^(d.primeFactors.card) / (Nat.totient d : ℝ)) *
            (∑ c ∈ (d.divisors.attach.filter (fun c => 2 ≤ c.1)),
              ∑ t ∈ (d / c.1).divisors,
                Work.NumberTheory.Chen.BTermCount.bProdCharSumDivSum x M Y t c.1) := by
  refine Finset.sum_le_sum (fun d hd => ?_)
  obtain ⟨hdmem, -⟩ := Finset.mem_filter.mp hd
  have hd1 : 1 ≤ d := (Finset.mem_Icc.mp hdmem).1
  haveI : NeZero d := ⟨by omega⟩
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  exact Finset.sum_le_sum (fun c _ =>
    bProdCharSumDivSum_le_divisors x M Y d c.1 (Nat.mem_divisors.mp c.2).1)

end Work.NumberTheory.Chen.BTermCount
