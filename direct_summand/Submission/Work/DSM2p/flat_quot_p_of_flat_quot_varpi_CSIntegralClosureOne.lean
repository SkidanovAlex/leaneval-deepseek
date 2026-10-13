import Mathlib
import Submission.Work.DSM2p.One
import Submission.Work.DSM2p.CSIntegralClosureOne_isSMulRegular
import Submission.Work.DSM2p.flat_quot_p_of_flat_quot_varpi_CSIntegralClosurePos

/-!
# Flatness of `A'_F ⧸ pA'_F` over `A ⧸ (p)` from flatness of `A'_F ⧸ ϖA'_F` over `A ⧸ (ϖ)`

Let `A` be a perfectoid ring (`DSMap.PerfectoidData p A`) with pseudo-uniformizer `ϖ = P.ϖ 0`,
so that `ϖ ^ p = p · v` for a unit `v` of `A`, and let `A'_F = CSIntegralClosureOne A p ϖ F` be
the one-polynomial `p`-integral closure.  This is the `One`-version of
`flat_quot_p_of_flat_quot_varpi_CSIntegralClosurePos`, and the proof is the same.

Since `(ϖ ^ p) = (p)` as ideals of `A` (and of `A'_F`), the quotient `A ⧸ (p)` is a *nilpotent*
thickening of `A ⧸ (ϖ)`: the class `ϖ̄` of `ϖ` in `A ⧸ (p)` is nilpotent of order `p` (because
`p = 0` there and `ϖ ^ p = p · v`).  The classical local flatness criterion for a nilpotent ideal
(Stacks tag 051C, `Work.DSFFP.flat_of_flat_mod_nilpotent`) therefore upgrades flatness over
`A ⧸ (ϖ)` to flatness over `A ⧸ (p)`.

The two hypotheses of the criterion are

* `Work.DSFFP.flat_quot_quot_span` — `h2`, the flatness of the "mod `ϖ`" quotient
  `A'_F ⧸ ϖA'_F` over `A ⧸ (ϖ)`, transported to the double quotients `(A ⧸ (p)) ⧸ (ϖ̄)` and
  `(A'_F ⧸ pA'_F) ⧸ ϖ̄`;
* `Work.DSFFP.idxInj_span_iff` — `h1`, the `Tor₁`-vanishing, which reduces to the statement
  `ϖ · y ∈ pA'_F ⇒ y ∈ ϖ ^ (p - 1) A'_F` (i.e. the `ϖ`-torsion-freeness of `A'_F ⧸ pA'_F`), and
  uses only that `ϖ` is a non-zero-divisor on `A'_F` together with `pA'_F = ϖ ^ p A'_F`.
-/

namespace Work.DSM2p

universe u

set_option maxHeartbeats 1600000

/-- `ϖ = P.ϖ 0` is a non-zero-divisor on the one-polynomial `p`-integral closure
`A'_F = CSIntegralClosureOne A p ϖ F`.  Indeed `ϖ ^ p = p · v` for a unit `v` of `A`
(`P.unit`), and `p` is a non-zero-divisor on `A'_F`. -/
lemma isSMulRegular_varpi_CSIntegralClosureOne (p : ℕ) [Fact p.Prime] (A : Type*) [CommRing A]
    (P : DSMap.PerfectoidData p A) (F : Polynomial A) :
    IsSMulRegular ↥(CSIntegralClosureOne A p (P.ϖ 0) F)
      (algebraMap A ↥(CSIntegralClosureOne A p (P.ϖ 0) F) (P.ϖ 0)) := by
  obtain ⟨v, hv⟩ := P.unit
  have hA'p : IsSMulRegular ↥(CSIntegralClosureOne A p (P.ϖ 0) F)
      (p : ↥(CSIntegralClosureOne A p (P.ϖ 0) F)) :=
    CSIntegralClosureOne_isSMulRegular A p (P.ϖ 0) F P.torsionFree
  have hpow : (algebraMap A ↥(CSIntegralClosureOne A p (P.ϖ 0) F) (P.ϖ 0)) ^ p
      = (p : ↥(CSIntegralClosureOne A p (P.ϖ 0) F))
        * algebraMap A ↥(CSIntegralClosureOne A p (P.ϖ 0) F) (↑v) := by
    rw [← map_pow, hv, map_mul, map_natCast]
  have hu : IsUnit (algebraMap A ↥(CSIntegralClosureOne A p (P.ϖ 0) F) (↑v)) :=
    IsUnit.map
      ((algebraMap A ↥(CSIntegralClosureOne A p (P.ϖ 0) F) : A →+*
        ↥(CSIntegralClosureOne A p (P.ϖ 0) F)) : A →* ↥(CSIntegralClosureOne A p (P.ϖ 0) F))
      v.isUnit
  have hreg : IsSMulRegular ↥(CSIntegralClosureOne A p (P.ϖ 0) F)
      ((algebraMap A ↥(CSIntegralClosureOne A p (P.ϖ 0) F) (P.ϖ 0)) ^ p) := by
    rw [hpow]
    exact hA'p.mul (IsUnit.isSMulRegular _ hu)
  exact (IsSMulRegular.pow_iff (Fact.out : Nat.Prime p).pos).mp hreg

set_option synthInstance.maxHeartbeats 1600000 in
theorem flat_quot_p_of_flat_quot_varpi_CSIntegralClosureOne (p : ℕ) [Fact p.Prime] (A : Type*)
    [CommRing A] (P : DSMap.PerfectoidData p A) (F : Polynomial A)
    (h : Module.Flat (A ⧸ Ideal.span {(P.ϖ 0 : A)})
      (↥(CSIntegralClosureOne A p (P.ϖ 0) F) ⧸
        (Ideal.span {(P.ϖ 0 : A)}).map (algebraMap A ↥(CSIntegralClosureOne A p (P.ϖ 0) F)))) :
    Module.Flat (A ⧸ Ideal.span {(p : A)})
      (↥(CSIntegralClosureOne A p (P.ϖ 0) F) ⧸
        (Ideal.span {(p : A)}).map (algebraMap A ↥(CSIntegralClosureOne A p (P.ϖ 0) F))) := by
  -- `(p) = (ϖ ^ p)` as ideals of `A`.
  have hspan : Ideal.span {(p : A)} = Ideal.span {(P.ϖ 0 : A) ^ p} :=
    (Work.DSPB2.span_varpi_pow_eq_span_p p A P).symm
  have hppos : 0 < p := (Fact.out : Nat.Prime p).pos
  have hp1 : p - 1 + 1 = p := by omega
  -- `ϖ` is a non-zero-divisor on `A'_F`.
  have hϖA' := isSMulRegular_varpi_CSIntegralClosureOne p A P F
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
      (↥(CSIntegralClosureOne A p (P.ϖ 0) F) ⧸
        (Ideal.span {(p : A)}).map (algebraMap A ↥(CSIntegralClosureOne A p (P.ϖ 0) F))) := by
    rw [Work.DSFFP.idxInj_span_iff]
    intro t ht
    rw [LinearMap.mem_ker] at ht
    -- lift `t` to `y : A'_F`
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective t
    rw [LinearMap.lsmul_apply] at ht
    rw [Ideal.Quotient.mk_smul_mk_quotient_map_quotient] at ht
    -- `ϖ · y ∈ pA'_F`
    have hy : algebraMap A ↥(CSIntegralClosureOne A p (P.ϖ 0) F) (P.ϖ 0) * y
        ∈ Ideal.map (algebraMap A ↥(CSIntegralClosureOne A p (P.ϖ 0) F)) (Ideal.span {(p : A)}) :=
      Ideal.Quotient.eq_zero_iff_mem.mp ht
    -- `pA'_F = (ϖ')^p A'_F`
    have hmap : Ideal.map (algebraMap A ↥(CSIntegralClosureOne A p (P.ϖ 0) F)) (Ideal.span {(p : A)})
        = Ideal.span {(algebraMap A ↥(CSIntegralClosureOne A p (P.ϖ 0) F) (P.ϖ 0)) ^ p} := by
      rw [hspan, Ideal.map_span, Set.image_singleton, map_pow]
    rw [hmap] at hy
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.mp hy
    -- cancel `ϖ`: `y = ϖ ^ (p - 1) · c`
    have hcancel : y
        = (algebraMap A ↥(CSIntegralClosureOne A p (P.ϖ 0) F) (P.ϖ 0)) ^ (p - 1) * c := by
      refine hϖA' ?_
      simp only [smul_eq_mul]
      rw [hc]
      rw [show (algebraMap A ↥(CSIntegralClosureOne A p (P.ϖ 0) F) (P.ϖ 0)) ^ p * c
            = (algebraMap A ↥(CSIntegralClosureOne A p (P.ϖ 0) F) (P.ϖ 0))
              * ((algebraMap A ↥(CSIntegralClosureOne A p (P.ϖ 0) F) (P.ϖ 0)) ^ (p - 1) * c) by
          rw [← mul_assoc,
            ← pow_succ' (algebraMap A ↥(CSIntegralClosureOne A p (P.ϖ 0) F) (P.ϖ 0)) (p - 1),
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
    (↥(CSIntegralClosureOne A p (P.ϖ 0) F) ⧸
      (Ideal.span {(p : A)}).map (algebraMap A ↥(CSIntegralClosureOne A p (P.ϖ 0) F)))
    p hI h1 h2

end Work.DSM2p
