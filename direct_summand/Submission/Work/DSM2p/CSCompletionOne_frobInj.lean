import Mathlib
import Submission.Work.DSM2p.One
import Submission.Work.DSM2p.LamOne
import Submission.Work.DSM2p.exists_mul_of_pow_mem
import Submission.Work.DSM2p.adicCompletion_ker_eval_one
import Submission.Work.DSM2p.CSIntegralClosurePos_isSMulRegular
import Submission.Work.DSM2p.rootClosure_flat

/-!
# Frobenius injectivity modulo `ϖ ^ p` for the one-polynomial cover `B_F`

This is the single-polynomial version of `CSCompletionPos_frobInj`, on the ring
`B_F = CSCompletionOne A p ϖ F = AdicCompletion (p) A'_F` of `One.lean`, where
`A'_F = CSIntegralClosureOne A p ϖ F = pIntClosure p (CSAlgOne A p ϖ F)` is the `p`-integral
closure of the one-polynomial `A_∞` inside `Λ[1/ϖ]`.  The statement is the `frobInj` field of
`PerfectoidData p B_F` restricted to a single polynomial `F`:

`x ^ p ∈ (ϖ ^ p)B_F → x ∈ ϖ B_F`.

## The argument

1. `(p) = (ϖ ^ p)` in `B_F` (because `ϖ ^ p = p · u` with `u` a unit of `A`); so the hypothesis
   reads `x ^ p ∈ pB_F`, and the conclusion `x ∈ ϖB_F` follows from `x ∈ pB_F + ϖB_F` because
   `p ∈ (ϖ)B_F`.

2. **Reduction to `A'_F`.**  Since `B_F` is the `p`-adic completion of `A'_F`, the level-`1`
   reduction `A'_F/pA'_F → B_F/pB_F` is an isomorphism: `ker(evalOneₐ (p)) = pB_F`
   (`AdicCompletion.ker_evalOneₐ_eq_map`, which only needs `(p).FG`).  Explicitly, for `b : A'_F`
   one has `algebraMap A'_F B_F b ∈ pB_F ↔ b ∈ pA'_F`.

3. Hence there is `a : A'_F` with `of a - x ∈ pB_F`.  Then `(of a) ^ p ≡ x ^ p ≡ 0 (mod pB_F)` —
   the difference `(of a) ^ p - x ^ p` is divisible by `of a - x` — so `of (a ^ p) ∈ pB_F`, i.e.
   `a ^ p ∈ pA'_F`.

4. **Frobenius injectivity on `A'_F`.**  In `A'_F`, `(p) = (ϖ ^ p)`, and `A'_F` is `p`-integrally
   closed in `Λ[1/ϖ]` (`CSIntegralClosureOne_isPIntegrallyClosed`), where `ϖ` is a unit;
   `exists_mul_of_pow_mem` (ČS `p-int-cl-lem`) then produces `a' : A'_F` with `a = ϖ · a'`.

5. Combining: `x = of a - (of a - x) ∈ ϖB_F + pB_F ⊆ ϖB_F`, since `p ∈ (ϖ)B_F`.
-/

open scoped Classical

-- `A'_F` and `B_F` are built from a fair amount of structure (`pIntClosure` of a
-- `Subring.closure` inside a localization), so the default heartbeat budget is not enough for
-- the (few) `change`/`show` and instance searches below.
set_option maxHeartbeats 1600000

namespace Work.DSM2p

/-- The image of `P.ϖ 0` in `A'_F` is a unit of `Λ[1/ϖ]` — this is the `IsUnit` hypothesis of
`exists_mul_of_pow_mem` in the ambient localization. -/
theorem isUnit_algebraMap_varpi_CSIntegralClosureOne (p : ℕ) (A : Type*) [CommRing A]
    (P : DSMap.PerfectoidData p A) (F : Polynomial A) :
    IsUnit ((algebraMap A (CSIntegralClosureOne A p (P.ϖ 0) F) (P.ϖ 0) :
      CSIntegralClosureOne A p (P.ϖ 0) F) : Lam1Loc A p (P.ϖ 0)) := by
  show IsUnit (algebraMap (Lam1 A p) (Lam1Loc A p (P.ϖ 0))
    (algebraMap A (Lam1 A p) (P.ϖ 0)))
  exact IsLocalization.Away.algebraMap_isUnit _

/-- In `A'_F` the ideals `(p)` and `(ϖ ^ p)` agree, since `ϖ ^ p = p · u` with `u` a unit of
`A`. -/
theorem span_p_eq_span_varpi_pow_CSIntegralClosureOne (p : ℕ) (A : Type*) [CommRing A]
    (P : DSMap.PerfectoidData p A) (F : Polynomial A) :
    Ideal.span {(p : CSIntegralClosureOne A p (P.ϖ 0) F)}
      = Ideal.span {(algebraMap A (CSIntegralClosureOne A p (P.ϖ 0) F) (P.ϖ 0)) ^ p} := by
  obtain ⟨v, hv⟩ := P.unit
  have hkey : (algebraMap A (CSIntegralClosureOne A p (P.ϖ 0) F) (P.ϖ 0)) ^ p =
      (p : CSIntegralClosureOne A p (P.ϖ 0) F) *
        algebraMap A (CSIntegralClosureOne A p (P.ϖ 0) F) (↑v : A) := by
    rw [← map_pow, hv, map_mul, map_natCast]
  rw [hkey, Ideal.span_singleton_mul_right_unit (IsUnit.map _ v.isUnit)]

/-- **ČS `p-int-cl-lem`, injective direction, for `A'_F`.**  The `p`-integral closure of the
one-polynomial `A_∞` is `p`-integrally closed in `Λ[1/ϖ]`, where `ϖ` is a unit; hence
`a ^ p ∈ (p)` implies `a ∈ (ϖ)`. -/
theorem frobInj_CSIntegralClosureOne (p : ℕ) (A : Type*) [CommRing A]
    (P : DSMap.PerfectoidData p A) (F : Polynomial A) (a : CSIntegralClosureOne A p (P.ϖ 0) F) :
    a ^ p ∈ Ideal.span {(p : CSIntegralClosureOne A p (P.ϖ 0) F)} →
    a ∈ Ideal.span {algebraMap A (CSIntegralClosureOne A p (P.ϖ 0) F) (P.ϖ 0)} := by
  intro ha
  rw [span_p_eq_span_varpi_pow_CSIntegralClosureOne p A P F] at ha
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.mp ha
  obtain ⟨y, hy, hyeq⟩ := exists_mul_of_pow_mem (p := p)
      (CSIntegralClosureOne A p (P.ϖ 0) F)
      (CSIntegralClosureOne_isPIntegrallyClosed A p (P.ϖ 0) F)
      (isUnit_algebraMap_varpi_CSIntegralClosureOne p A P F)
      (x := (a : Lam1Loc A p (P.ϖ 0))) a.2
      ⟨(c : Lam1Loc A p (P.ϖ 0)), c.2, by
        rw [← Subring.coe_pow, hc, Subring.coe_mul, Subring.coe_pow]⟩
  refine Ideal.mem_span_singleton.mpr ⟨⟨y, hy⟩, ?_⟩
  apply Subtype.coe_injective
  show (a : Lam1Loc A p (P.ϖ 0)) =
    ((algebraMap A (CSIntegralClosureOne A p (P.ϖ 0) F) (P.ϖ 0) * ⟨y, hy⟩ :
      CSIntegralClosureOne A p (P.ϖ 0) F) : Lam1Loc A p (P.ϖ 0))
  rw [Subring.coe_mul]
  exact hyeq

theorem CSCompletionOne_frobInj (A : Type*) [CommRing A] (p : ℕ) [Fact p.Prime]
    (P : DSMap.PerfectoidData p A) (F : Polynomial A) (x : CSCompletionOne A p (P.ϖ 0) F) :
    x ^ p ∈ Ideal.span {algebraMap A (CSCompletionOne A p (P.ϖ 0) F) (P.ϖ 0 ^ p)} →
    x ∈ Ideal.span {algebraMap A (CSCompletionOne A p (P.ϖ 0) F) (P.ϖ 0)} := by
  intro hx
  -- `(p)` and `(ϖ ^ p)` agree in `B_F`
  have hspanB : Ideal.span {algebraMap A (CSCompletionOne A p (P.ϖ 0) F) (P.ϖ 0 ^ p)}
      = Ideal.span {(p : CSCompletionOne A p (P.ϖ 0) F)} := by
    obtain ⟨v, hv⟩ := P.unit
    have hkey : algebraMap A (CSCompletionOne A p (P.ϖ 0) F) (P.ϖ 0 ^ p)
        = (p : CSCompletionOne A p (P.ϖ 0) F) *
          algebraMap A (CSCompletionOne A p (P.ϖ 0) F) (↑v : A) := by
      rw [hv, map_mul, map_natCast]
    rw [hkey, Ideal.span_singleton_mul_right_unit (IsUnit.map _ v.isUnit)]
  rw [hspanB] at hx
  -- `ker(A'_F → A'_F/p) = pB_F`: the level-`1` reduction of the completion
  have hker : RingHom.ker (AdicCompletion.evalOneₐ
      (Ideal.span {(p : CSIntegralClosureOne A p (P.ϖ 0) F)})).toRingHom
      = Ideal.span {(p : CSCompletionOne A p (P.ϖ 0) F)} := by
    rw [AdicCompletion.ker_evalOneₐ_eq_map _
      (Submodule.fg_span_singleton (p : CSIntegralClosureOne A p (P.ϖ 0) F))]
    rw [Ideal.map_span, Set.image_singleton, map_natCast]
  -- the level-`1` reduction of an element of `A'_F`
  have hca : ∀ b : CSIntegralClosureOne A p (P.ϖ 0) F,
      (AdicCompletion.evalOneₐ
        (Ideal.span {(p : CSIntegralClosureOne A p (P.ϖ 0) F)})).toRingHom
        (algebraMap (CSIntegralClosureOne A p (P.ϖ 0) F) (CSCompletionOne A p (P.ϖ 0) F) b)
      = Ideal.Quotient.mk (Ideal.span {(p : CSIntegralClosureOne A p (P.ϖ 0) F)}) b := by
    intro b
    rw [AdicCompletion.algebraMap_apply]
    show (AdicCompletion.evalOneₐ (Ideal.span {(p : CSIntegralClosureOne A p (P.ϖ 0) F)}))
      (AdicCompletion.of _ _ (algebraMap (CSIntegralClosureOne A p (P.ϖ 0) F)
        (CSIntegralClosureOne A p (P.ϖ 0) F) b))
      = Ideal.Quotient.mk (Ideal.span {(p : CSIntegralClosureOne A p (P.ϖ 0) F)}) b
    rw [AdicCompletion.evalOneₐ_of]
    exact congrArg (Ideal.Quotient.mk (Ideal.span {(p : CSIntegralClosureOne A p (P.ϖ 0) F)}))
      (Algebra.algebraMap_self_apply b)
  -- step 2: lift `x` modulo `pB_F` to an element `a` of `A'_F`
  obtain ⟨a, ha_eq⟩ : ∃ a : CSIntegralClosureOne A p (P.ϖ 0) F,
      (AdicCompletion.evalOneₐ
        (Ideal.span {(p : CSIntegralClosureOne A p (P.ϖ 0) F)})).toRingHom x
      = Ideal.Quotient.mk (Ideal.span {(p : CSIntegralClosureOne A p (P.ϖ 0) F)}) a := by
    obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective
      (I := Ideal.span {(p : CSIntegralClosureOne A p (P.ϖ 0) F)})
      ((AdicCompletion.evalOneₐ (Ideal.span {(p : CSIntegralClosureOne A p (P.ϖ 0) F)})) x)
    exact ⟨a, ha.symm⟩
  have hmem : algebraMap (CSIntegralClosureOne A p (P.ϖ 0) F) (CSCompletionOne A p (P.ϖ 0) F) a
      - x ∈ Ideal.span {(p : CSCompletionOne A p (P.ϖ 0) F)} := by
    rw [← hker, RingHom.mem_ker]
    show (AdicCompletion.evalOneₐ (Ideal.span
      {(p : CSIntegralClosureOne A p (P.ϖ 0) F)}))
      (algebraMap (CSIntegralClosureOne A p (P.ϖ 0) F) (CSCompletionOne A p (P.ϖ 0) F) a - x) = 0
    rw [map_sub]
    change (AdicCompletion.evalOneₐ
        (Ideal.span {(p : CSIntegralClosureOne A p (P.ϖ 0) F)})).toRingHom
      (algebraMap (CSIntegralClosureOne A p (P.ϖ 0) F) (CSCompletionOne A p (P.ϖ 0) F) a)
      - (AdicCompletion.evalOneₐ
          (Ideal.span {(p : CSIntegralClosureOne A p (P.ϖ 0) F)})).toRingHom x = 0
    rw [hca a, ha_eq, sub_self]
  -- membership of `b : A'_F` in `pB_F` is membership of `b` in `pA'_F`
  have hmem_iff : ∀ b : CSIntegralClosureOne A p (P.ϖ 0) F,
      algebraMap (CSIntegralClosureOne A p (P.ϖ 0) F) (CSCompletionOne A p (P.ϖ 0) F) b
        ∈ Ideal.span {(p : CSCompletionOne A p (P.ϖ 0) F)}
      ↔ b ∈ Ideal.span {(p : CSIntegralClosureOne A p (P.ϖ 0) F)} := by
    intro b
    rw [← hker, RingHom.mem_ker, hca b, Ideal.Quotient.eq_zero_iff_mem]
  -- step 3: `a ^ p ∈ pA'_F`
  have hofap : (algebraMap (CSIntegralClosureOne A p (P.ϖ 0) F)
      (CSCompletionOne A p (P.ϖ 0) F) a) ^ p
      ∈ Ideal.span {(p : CSCompletionOne A p (P.ϖ 0) F)} := by
    obtain ⟨c, hc⟩ := sub_dvd_pow_sub_pow
      (algebraMap (CSIntegralClosureOne A p (P.ϖ 0) F) (CSCompletionOne A p (P.ϖ 0) F) a) x p
    have h1 : (algebraMap (CSIntegralClosureOne A p (P.ϖ 0) F)
          (CSCompletionOne A p (P.ϖ 0) F) a) ^ p
        = x ^ p + (algebraMap (CSIntegralClosureOne A p (P.ϖ 0) F)
            (CSCompletionOne A p (P.ϖ 0) F) a - x) * c :=
      sub_eq_iff_eq_add'.mp hc
    rw [h1]
    exact Ideal.add_mem _ hx (Ideal.mul_mem_right _ _ hmem)
  have hap : a ^ p ∈ Ideal.span {(p : CSIntegralClosureOne A p (P.ϖ 0) F)} := by
    refine (hmem_iff (a ^ p)).mp ?_
    rw [map_pow]
    exact hofap
  -- step 4: `a ∈ ϖ A'_F`
  have ha_key : a ∈ Ideal.span {algebraMap A (CSIntegralClosureOne A p (P.ϖ 0) F) (P.ϖ 0)} :=
    frobInj_CSIntegralClosureOne p A P F a hap
  have hmem_span : algebraMap (CSIntegralClosureOne A p (P.ϖ 0) F)
      (CSCompletionOne A p (P.ϖ 0) F) a
      ∈ Ideal.span {algebraMap A (CSCompletionOne A p (P.ϖ 0) F) (P.ϖ 0)} := by
    obtain ⟨y₀, hy₀⟩ := Ideal.mem_span_singleton.mp ha_key
    rw [hy₀, map_mul]
    have hcompat : algebraMap (CSIntegralClosureOne A p (P.ϖ 0) F)
        (CSCompletionOne A p (P.ϖ 0) F)
        (algebraMap A (CSIntegralClosureOne A p (P.ϖ 0) F) (P.ϖ 0))
        = algebraMap A (CSCompletionOne A p (P.ϖ 0) F) (P.ϖ 0) := rfl
    rw [hcompat]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)
  -- step 5: `p ∈ (ϖ)B_F`, so `pB_F ⊆ ϖB_F`, and `x = of a - (of a - x)`
  have hple : Ideal.span {(p : CSCompletionOne A p (P.ϖ 0) F)}
      ≤ Ideal.span {algebraMap A (CSCompletionOne A p (P.ϖ 0) F) (P.ϖ 0)} := by
    rw [← hspanB, map_pow]
    exact Ideal.span_singleton_le_span_singleton.mpr
      (dvd_pow_self _ (Fact.out : p.Prime).ne_zero)
  have hx_split : x = algebraMap (CSIntegralClosureOne A p (P.ϖ 0) F)
      (CSCompletionOne A p (P.ϖ 0) F) a
      - (algebraMap (CSIntegralClosureOne A p (P.ϖ 0) F)
          (CSCompletionOne A p (P.ϖ 0) F) a - x) :=
    (sub_sub_self (algebraMap (CSIntegralClosureOne A p (P.ϖ 0) F)
      (CSCompletionOne A p (P.ϖ 0) F) a) x).symm
  rw [hx_split]
  exact Ideal.sub_mem _ hmem_span (hple hmem)

end Work.DSM2p
