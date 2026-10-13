import Mathlib
import Submission.Work.DSM2p.CSCompletionPos_faithfullyFlat
import Submission.Work.DSM2p.ConstructionPos
import Submission.Work.DSM2p.CSIntegralClosurePos_isSMulRegular
import Submission.Work.DSFFP.flat_of_flat_mod_nilpotent
import Submission.Work.DSFFP.flat_quot_quot_pow
import Submission.Work.DSFFP.idxInj_quot_pow
import Submission.Work.DSPB2.Basic

/-!
# Flatness of `A' ⧸ pA'` over `A ⧸ (p)` from flatness of `A' ⧸ ϖA'` over `A ⧸ (ϖ)`

Let `A` be a perfectoid ring with pseudo-uniformizer `ϖ = P.ϖ 0`, so that `ϖ ^ p = p · v` for a
unit `v`, and let `A' = CSIntegralClosurePos A p ϖ`.  Since `(ϖ ^ p) = (p)` as ideals of `A`
(and of `A'`), the quotient `A ⧸ (p)` is a *nilpotent* thickening of `A ⧸ (ϖ)`: the class `ϖ̄` of
`ϖ` in `A ⧸ (p)` is nilpotent of order `p` (because `p = 0` there and `ϖ ^ p = p · v`).  The
classical local flatness criterion for a nilpotent ideal (Stacks tag 051C,
`Work.DSFFP.flat_of_flat_mod_nilpotent`) therefore upgrades flatness over `A ⧸ (ϖ)` to flatness
over `A ⧸ (p)`.

The two hypotheses of the criterion are

* `Work.DSFFP.flat_quot_quot_span` — `h2`, the flatness of the "mod `ϖ`" quotient
  `A' ⧸ ϖA'` over `A ⧸ (ϖ)`, transported to the double quotients `(A ⧸ (p)) ⧸ (ϖ̄)` and
  `(A' ⧸ pA') ⧸ ϖ̄`;
* `Work.DSFFP.idxInj_span_iff` — `h1`, the `Tor₁`-vanishing, which reduces to the statement
  `ϖ · y ∈ pA' ⇒ y ∈ ϖ ^ (p - 1) A'` (i.e. the `ϖ`-torsion-freeness of `A' ⧸ pA'`), and uses only
  that `ϖ` is a non-zero-divisor on `A'` together with `pA' = ϖ ^ p A'`.
-/

namespace Work.DSM2p

universe u

set_option maxHeartbeats 1600000

/-- `ϖ = P.ϖ 0` is a non-zero-divisor on the `p`-integral closure `A' = CSIntegralClosurePos A p ϖ`.
Indeed `ϖ ^ p = p · v` for a unit `v` of `A'` (`P.unit`), and `p` is a non-zero-divisor on `A'`. -/
lemma isSMulRegular_varpi_CSIntegralClosurePos (p : ℕ) [Fact p.Prime] (A : Type*) [CommRing A]
    (P : DSMap.PerfectoidData p A) :
    IsSMulRegular ↥(CSIntegralClosurePos A p (P.ϖ 0))
      (algebraMap A ↥(CSIntegralClosurePos A p (P.ϖ 0)) (P.ϖ 0)) := by
  obtain ⟨v, hv⟩ := P.unit
  have hp : IsSMulRegular A (p : A) := P.torsionFree
  have hA'p : IsSMulRegular ↥(CSIntegralClosurePos A p (P.ϖ 0))
      (p : ↥(CSIntegralClosurePos A p (P.ϖ 0))) :=
    CSIntegralClosurePos_isSMulRegular A p (P.ϖ 0) hp
  have hpow : (algebraMap A ↥(CSIntegralClosurePos A p (P.ϖ 0)) (P.ϖ 0)) ^ p
      = (p : ↥(CSIntegralClosurePos A p (P.ϖ 0)))
        * algebraMap A ↥(CSIntegralClosurePos A p (P.ϖ 0)) (↑v) := by
    rw [← map_pow, hv, map_mul, map_natCast]
  have hu : IsUnit (algebraMap A ↥(CSIntegralClosurePos A p (P.ϖ 0)) (↑v)) :=
    IsUnit.map
      ((algebraMap A ↥(CSIntegralClosurePos A p (P.ϖ 0)) : A →+*
        ↥(CSIntegralClosurePos A p (P.ϖ 0))) : A →* ↥(CSIntegralClosurePos A p (P.ϖ 0)))
      v.isUnit
  have hreg : IsSMulRegular ↥(CSIntegralClosurePos A p (P.ϖ 0))
      ((algebraMap A ↥(CSIntegralClosurePos A p (P.ϖ 0)) (P.ϖ 0)) ^ p) := by
    rw [hpow]
    exact hA'p.mul (IsUnit.isSMulRegular _ hu)
  exact (IsSMulRegular.pow_iff (Fact.out : Nat.Prime p).pos).mp hreg

theorem flat_quot_p_of_flat_quot_varpi_CSIntegralClosurePos (p : ℕ) [Fact p.Prime] (A : Type*)
    [CommRing A] (P : DSMap.PerfectoidData p A)
    (h : Module.Flat (A ⧸ Ideal.span {(P.ϖ 0 : A)})
      (↥(CSIntegralClosurePos A p (P.ϖ 0)) ⧸
        (Ideal.span {(P.ϖ 0 : A)}).map (algebraMap A ↥(CSIntegralClosurePos A p (P.ϖ 0))))) :
    Module.Flat (A ⧸ Ideal.span {(p : A)})
      (↥(CSIntegralClosurePos A p (P.ϖ 0)) ⧸
        (Ideal.span {(p : A)}).map (algebraMap A ↥(CSIntegralClosurePos A p (P.ϖ 0)))) := by
  -- `(p) = (ϖ ^ p)` as ideals of `A`.
  have hspan : Ideal.span {(p : A)} = Ideal.span {(P.ϖ 0 : A) ^ p} :=
    (Work.DSPB2.span_varpi_pow_eq_span_p p A P).symm
  have hppos : 0 < p := (Fact.out : Nat.Prime p).pos
  have hp1 : p - 1 + 1 = p := by omega
  -- `ϖ` is a non-zero-divisor on `A'`.
  have hϖA' := isSMulRegular_varpi_CSIntegralClosurePos p A P
  -- `(p) ≤ (ϖ)`.
  have hle : Ideal.span {(p : A)} ≤ Ideal.span {(P.ϖ 0 : A)} :=
    hspan.trans_le (by
      rw [Ideal.span_singleton_le_span_singleton]
      exact dvd_pow_self _ hppos.ne')
  -- Hypothesis `h2` of the criterion: the "mod `ϖ`" quotient, flat by hypothesis.
  have h2 := Work.DSFFP.flat_quot_quot_span (Ideal.span {(p : A)}) (P.ϖ 0) hle h
  -- Nilpotence: `ϖ̄ ^ p = 0` in `A ⧸ (p)`.
  have hI : (Ideal.span {Ideal.Quotient.mk (Ideal.span {(p : A)}) (P.ϖ 0)}) ^ p = ⊥ := by
    rw [Ideal.span_singleton_pow]
    refine Ideal.span_singleton_eq_bot.mpr ?_
    rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem, hspan]
    exact Ideal.mem_span_singleton_self _
  -- Hypothesis `h1` of the criterion: `Tor₁`-vanishing for the principal ideal `(ϖ̄)`.
  have h1 : Work.DSFFP.IdxInj
      (Ideal.span {Ideal.Quotient.mk (Ideal.span {(p : A)}) (P.ϖ 0)})
      (↥(CSIntegralClosurePos A p (P.ϖ 0)) ⧸
        (Ideal.span {(p : A)}).map (algebraMap A ↥(CSIntegralClosurePos A p (P.ϖ 0)))) := by
    rw [Work.DSFFP.idxInj_span_iff]
    intro t ht
    rw [LinearMap.mem_ker] at ht
    -- lift `t` to `y : A'`
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective t
    rw [LinearMap.lsmul_apply] at ht
    rw [Ideal.Quotient.mk_smul_mk_quotient_map_quotient] at ht
    -- `ϖ · y ∈ pA'`
    have hy : algebraMap A ↥(CSIntegralClosurePos A p (P.ϖ 0)) (P.ϖ 0) * y
        ∈ Ideal.map (algebraMap A ↥(CSIntegralClosurePos A p (P.ϖ 0))) (Ideal.span {(p : A)}) :=
      Ideal.Quotient.eq_zero_iff_mem.mp ht
    -- `pA' = (ϖ')^p A'`
    have hmap : Ideal.map (algebraMap A ↥(CSIntegralClosurePos A p (P.ϖ 0))) (Ideal.span {(p : A)})
        = Ideal.span {(algebraMap A ↥(CSIntegralClosurePos A p (P.ϖ 0)) (P.ϖ 0)) ^ p} := by
      rw [hspan, Ideal.map_span, Set.image_singleton, map_pow]
    rw [hmap] at hy
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.mp hy
    -- cancel `ϖ`: `y = ϖ ^ (p - 1) · c`
    have hcancel : y
        = (algebraMap A ↥(CSIntegralClosurePos A p (P.ϖ 0)) (P.ϖ 0)) ^ (p - 1) * c := by
      refine hϖA' ?_
      simp only [smul_eq_mul]
      rw [hc]
      rw [show (algebraMap A ↥(CSIntegralClosurePos A p (P.ϖ 0)) (P.ϖ 0)) ^ p * c
            = (algebraMap A ↥(CSIntegralClosurePos A p (P.ϖ 0)) (P.ϖ 0))
              * ((algebraMap A ↥(CSIntegralClosurePos A p (P.ϖ 0)) (P.ϖ 0)) ^ (p - 1) * c) by
          rw [← mul_assoc,
            ← pow_succ' (algebraMap A ↥(CSIntegralClosurePos A p (P.ϖ 0)) (P.ϖ 0)) (p - 1),
            hp1]]
    rw [hcancel, ← map_pow]
    -- `mk (ϖ ^ (p-1) · c) = ϖ̄ ^ (p-1) • mk c`
    rw [← Ideal.Quotient.mk_smul_mk_quotient_map_quotient]
    rw [show Ideal.Quotient.mk (Ideal.span {(p : A)}) (P.ϖ 0 ^ (p - 1))
          = (Ideal.Quotient.mk (Ideal.span {(p : A)}) (P.ϖ 0)) ^ (p - 1) from map_pow _ _ _]
    refine Submodule.smul_mem_smul ?_ Submodule.mem_top
    -- `ϖ̄ ^ (p-1) ∈ ann (ϖ̄)`, because `ϖ̄ ^ p = 0`
    rw [Submodule.mem_annihilator_span_singleton, smul_eq_mul, ← pow_succ, hp1]
    rw [show (Ideal.Quotient.mk (Ideal.span {(p : A)}) (P.ϖ 0)) ^ p
          = Ideal.Quotient.mk (Ideal.span {(p : A)}) (P.ϖ 0 ^ p) from (map_pow _ _ _).symm]
    rw [Ideal.Quotient.eq_zero_iff_mem, hspan]
    exact Ideal.mem_span_singleton_self _
  exact Work.DSFFP.flat_of_flat_mod_nilpotent
    (Ideal.span {Ideal.Quotient.mk (Ideal.span {(p : A)}) (P.ϖ 0)})
    (↥(CSIntegralClosurePos A p (P.ϖ 0)) ⧸
      (Ideal.span {(p : A)}).map (algebraMap A ↥(CSIntegralClosurePos A p (P.ϖ 0))))
    p hI h1 h2

end Work.DSM2p
