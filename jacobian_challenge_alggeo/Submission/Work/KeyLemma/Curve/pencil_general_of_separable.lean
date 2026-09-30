import Mathlib
import Submission.Work.KeyLemma.Sum
import Submission.Work.KeyLemma.Sum.toDiv_injective
import Submission.Work.KeyLemma.Sum.isSplit_iff
import Submission.Work.KeyLemma.Curve.genericSum
import Submission.Work.KeyLemma.Curve.sumOfPoints_pow_of_pow_eq
import Submission.Work.CurveBasics.Order.exists_pow_eq_of_not_separable
import Submission.Work.CurveBasics.Order.finrank_adjoin_pow_eq_prime
import Submission.Work.CurveBasics.Order.finiteDimensional_adjoin_functionField
import Submission.Work.KeyLemma.Basic
import Submission.Work.KeyLemma.Pencil

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


namespace Work.KeyLemma.Curve

open CategoryTheory AlgebraicGeometry Limits
open scoped Classical MonObj MonoidalCategory CartesianMonoidalCategory

universe u

set_option linter.style.haveILetI false
set_option maxHeartbeats 1000000

/-! ## Auxiliary field-theoretic and divisor-theoretic lemmas

The two field-theoretic facts below are the ones needed for the degree decrease in the
inseparable case of `pencil_general_of_separable`: if `u` is transcendental over `k` and
`p ≥ 2`, then `u ∉ k(u ^ p)` and `[k(u) : k(u ^ p)] > 1`, so that `[K(C) : k(u)] < [K(C) : k(u^p)]`.
-/

/-- If `u` is transcendental over `k` and `2 ≤ p`, then `u` is not a rational function of
`u ^ p`: `u ∉ k(u ^ p)`.  The proof is a degree argument: an expression `u = R(u^p)` with
`R = r/s ∈ k(X)` gives `X * s(X^p) = r(X^p)` in `k[X]`, whose two sides have degrees
congruent to `1` resp. `0` modulo `p`. -/
theorem not_mem_adjoin_pow_self {k F : Type u} [Field k] [Field F] [Algebra k F] {u : F}
    (hu : Transcendental k u) {p : ℕ} (hp : 2 ≤ p) :
    u ∉ IntermediateField.adjoin k ({u ^ p} : Set F) := by
  intro hmem
  rw [IntermediateField.mem_adjoin_simple_iff] at hmem
  obtain ⟨r, s, hrs⟩ := hmem
  have hu0 : u ≠ 0 := by
    intro h
    have hX : Polynomial.X = 0 :=
      (transcendental_iff.mp hu) Polynomial.X (by rw [Polynomial.aeval_X, h])
    exact Polynomial.X_ne_zero hX
  have hs0 : (Polynomial.aeval (u ^ p)) s ≠ 0 := by
    intro h0
    rw [h0, div_zero] at hrs
    exact hu0 hrs
  have heq : u * (Polynomial.aeval (u ^ p)) s = (Polynomial.aeval (u ^ p)) r := by
    nth_rewrite 1 [hrs]
    rw [div_mul_cancel₀ _ hs0]
  have hexp : ∀ f : Polynomial k,
      (Polynomial.aeval u) (Polynomial.expand k p f) = (Polynomial.aeval (u ^ p)) f := by
    intro f
    rw [Polynomial.expand_eq_comp_X_pow, Polynomial.aeval_comp, map_pow, Polynomial.aeval_X]
  have hsum : (Polynomial.aeval u) (Polynomial.X * Polynomial.expand k p s)
      = (Polynomial.aeval u) (Polynomial.expand k p r) := by
    rw [map_mul, Polynomial.aeval_X, hexp s, hexp r]
    exact heq
  have hpoly : Polynomial.X * Polynomial.expand k p s = Polynomial.expand k p r := by
    have hzero : (Polynomial.aeval u)
        (Polynomial.X * Polynomial.expand k p s - Polynomial.expand k p r) = 0 := by
      rw [map_sub, hsum, sub_self]
    exact sub_eq_zero.mp ((transcendental_iff.mp hu) _ hzero)
  have hS : Polynomial.expand k p s ≠ 0 := by
    intro h0
    exact hs0 (by rw [← hexp s, h0, map_zero])
  have hnd : 1 + s.natDegree * p = r.natDegree * p := by
    have h1 : (Polynomial.X * Polynomial.expand k p s).natDegree
        = (Polynomial.expand k p r).natDegree := congrArg Polynomial.natDegree hpoly
    rw [Polynomial.natDegree_mul Polynomial.X_ne_zero hS, Polynomial.natDegree_X,
      Polynomial.natDegree_expand, Polynomial.natDegree_expand] at h1
    omega
  have hdvd1 : p ∣ 1 := by
    have h : p ∣ 1 + s.natDegree * p := by rw [hnd]; exact dvd_mul_left p r.natDegree
    rw [add_comm] at h
    exact (Nat.dvd_add_iff_right (dvd_mul_left p s.natDegree)).mpr h
  have hle : p ≤ 1 := Nat.le_of_dvd (by norm_num) hdvd1
  omega

/-- **The degree decreases along the `p`-th root.**  If `u` is transcendental over `k` and
`2 ≤ p`, then `[k(u) : F] < [k(u ^ p) : F]` for any field `F` finite over `k(u)`. -/
theorem finrank_pow_adjoin_lt {k F : Type u} [Field k] [Field F] [Algebra k F] {u : F}
    (hu : Transcendental k u) {p : ℕ} (hp : 2 ≤ p)
    [FiniteDimensional ↥(IntermediateField.adjoin k ({u} : Set F)) F] :
    Module.finrank ↥(IntermediateField.adjoin k ({u} : Set F)) F <
      Module.finrank ↥(IntermediateField.adjoin k ({u ^ p} : Set F)) F := by
  let A : IntermediateField k F := IntermediateField.adjoin k ({u ^ p} : Set F)
  let B : IntermediateField k F := IntermediateField.adjoin k ({u} : Set F)
  have hle : A ≤ B := by
    apply IntermediateField.adjoin_le_iff.mpr
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst hx
    exact pow_mem (IntermediateField.mem_adjoin_simple_self k u) p
  have heq : IntermediateField.extendScalars hle = IntermediateField.adjoin ↥A ({u} : Set F) := by
    refine IntermediateField.restrictScalars_injective k ?_
    rw [IntermediateField.extendScalars_restrictScalars,
      IntermediateField.restrictScalars_adjoin_eq_sup]
    exact (sup_eq_right.mpr hle).symm
  have hrel_ne : A.relfinrank B ≠ 1 := by
    intro h1
    have hBA : B ≤ A := IntermediateField.relfinrank_eq_one_iff.mp h1
    exact not_mem_adjoin_pow_self hu hp (hBA (IntermediateField.mem_adjoin_simple_self k u))
  have hrel_pos : 1 ≤ A.relfinrank B := by
    rw [IntermediateField.relfinrank_eq_finrank_of_le hle, heq]
    have hint : IsIntegral ↥A u := by
      refine ⟨Polynomial.X ^ p - Polynomial.C ⟨u ^ p,
        IntermediateField.mem_adjoin_simple_self k (u ^ p)⟩,
        Polynomial.monic_X_pow_sub_C _ (by omega), ?_⟩
      simp
    haveI : FiniteDimensional ↥A ↥(IntermediateField.adjoin ↥A ({u} : Set F)) :=
      IntermediateField.adjoin.finiteDimensional hint
    exact Module.finrank_pos
  have hrel2 : 2 ≤ A.relfinrank B := by omega
  have hBpos : 1 ≤ Module.finrank ↥B F := Module.finrank_pos
  have htower := IntermediateField.relfinrank_mul_finrank_top hle
  have h2 : Module.finrank ↥B F < A.relfinrank B * Module.finrank ↥B F := by
    calc Module.finrank ↥B F = 1 * Module.finrank ↥B F := (one_mul _).symm
      _ < A.relfinrank B * Module.finrank ↥B F :=
          Nat.mul_lt_mul_of_pos_right hrel2 hBpos
  exact lt_of_lt_of_eq h2 htower

/-- The negative part of a `p`-th power: `negPart C (u ^ p) = p • negPart C u`, the pole
divisor analogue of `posPart_pow`. -/
theorem negPart_pow {k : Type u} [Field k] (C : Work.CurveBasics.Curve k)
    (u : C.functionField) (p : ℕ) :
    negPart C (u ^ p) = p • negPart C u := by
  ext Q
  have h : C.div (u ^ p) Q = (p : ℤ) * C.div u Q := by
    rw [div_pow, Finsupp.smul_apply, nsmul_eq_mul]
  rw [negPart, negPart, Finsupp.mapRange_apply, Finsupp.smul_apply, Finsupp.mapRange_apply,
    nsmul_eq_mul, h]
  rw [show -((p : ℤ) * C.div u Q) = (p : ℤ) * (-(C.div u Q)) by ring]
  by_cases hle : 0 ≤ -(C.div u Q)
  · rw [max_eq_left (mul_nonneg (Nat.cast_nonneg p) hle), max_eq_left hle]
  · rw [max_eq_right (mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg p) (le_of_lt (not_le.mp hle))),
      max_eq_right (le_of_lt (not_le.mp hle)), mul_zero]

namespace SumDiv

/-- If the divisor of a multiset of points is `p` times the divisor of another (`p` fixed
throughout), then the first sum is the `p`-th power of the second.  This is the reduction step
of the inseparable case in the form used below, in which only the divisors (and not the
`posPart` of any specific function) appear. -/
theorem sumOfPoints_pow_of_toDiv_eq {k : Type u} [Field k]
    {C : Work.CurveBasics.Curve k}
    {A : CategoryTheory.Over (AlgebraicGeometry.Spec (CommRingCat.of k))}
    [CategoryTheory.GrpObj A] [CategoryTheory.IsCommMonObj A]
    (f : C.toOver ⟶ A) (p : ℕ) (s sp : SumDiv C)
    (hsp : toDiv C s = p • toDiv C sp) :
    sumOfPoints C f s = (sumOfPoints C f sp) ^ p := by
  have h : toDiv C s = toDiv C (p • sp) := by rw [hsp, toDiv_nsmul]
  rw [Work.KeyLemma.Sum.toDiv_injective C h, sumOfPoints_nsmul]

end SumDiv

/-- The inseparable case of the pencil statement is a degree reduction: if the pencil case holds
whenever `K(C)/k(h)` is separable, then it holds in general over a perfect field.  (Same content as
`KeyLemma/Curve/pencil_of_separable_case`, delegated under a free path because a reviewer's scratch
copy occupies that path.)

Proof strategy (strong induction on `N = [K(C) : k(h)]`, i.e. on
`Module.finrank ↥(baseField C h) ↥C.functionField`):

* `h ≠ 0` and `¬ IsConstant C h` give `Transcendental k h` (`Work.CurveBasics.Basic.eq_algebraMap_of_isAlgebraic`),
  hence `[K(C) : k(h)]` is finite (`finiteDimensional_adjoin_functionField`);
* if `K(C)/k(h)` is separable, apply `H`;
* otherwise (`k` of characteristic `p > 0`) `exists_pow_eq_of_not_separable` gives `u` with
  `u ^ p = h`; `u` is again nonconstant, and `[K(C) : k(u)] = [K(C) : k(h)] / p < [K(C) : k(h)]`
  (tower law together with `finrank_adjoin_pow_eq_prime`), so the induction hypothesis applies to
  `u`; the same applies to `u⁻¹` because `h⁻¹ = (u⁻¹) ^ p` and `posPart C (h⁻¹) = negPart C h`.
  Conclude with `sumOfPoints_pow_of_pow_eq`: `Σ f(s₀) = (Σ f(s₀')) ^ p = (Σ f(s₁')) ^ p = Σ f(s₁)`,
  where `s₀'`, `s₁'` are models of `posPart C u` and `posPart C (u⁻¹)` obtained by dividing the
  multiplicities of `s₀`, `s₁` by `p` (`posPart C h = p • posPart C u` and `placeOfPoint` is
  injective). -/
theorem pencil_general_of_separable {k : Type u} [Field k] [PerfectField k]
    {C : Work.CurveBasics.Curve k}
    {A : CategoryTheory.Over (AlgebraicGeometry.Spec (CommRingCat.of k))}
    [CategoryTheory.GrpObj A] [CategoryTheory.IsCommMonObj A]
    (f : C.toOver ⟶ A)
    (H : ∀ (h : C.functionField), h ≠ 0 → ¬ Work.KeyLemma.Curve.IsConstant C h →
      Algebra.IsSeparable ↥(Work.KeyLemma.Curve.baseField C h) ↥C.functionField →
      ∀ s₀ s₁ : Work.KeyLemma.Curve.SumDiv C,
        Work.KeyLemma.Curve.SumDiv.toDiv C s₀ = Work.KeyLemma.Curve.posPart C h →
        Work.KeyLemma.Curve.SumDiv.toDiv C s₁ = Work.KeyLemma.Curve.negPart C h →
        Work.KeyLemma.Curve.SumDiv.sumOfPoints C f s₀
          = Work.KeyLemma.Curve.SumDiv.sumOfPoints C f s₁) :
    ∀ (h : C.functionField), h ≠ 0 → ¬ Work.KeyLemma.Curve.IsConstant C h →
      ∀ s₀ s₁ : Work.KeyLemma.Curve.SumDiv C,
        Work.KeyLemma.Curve.SumDiv.toDiv C s₀ = Work.KeyLemma.Curve.posPart C h →
        Work.KeyLemma.Curve.SumDiv.toDiv C s₁ = Work.KeyLemma.Curve.negPart C h →
        Work.KeyLemma.Curve.SumDiv.sumOfPoints C f s₀
          = Work.KeyLemma.Curve.SumDiv.sumOfPoints C f s₁ := by
  intro h hh hnc s₀ s₁ hs₀ hs₁
  suffices key : ∀ N, ∀ (h : C.functionField),
      Module.finrank ↥(baseField C h) ↥C.functionField = N → h ≠ 0 → ¬ IsConstant C h →
      ∀ s₀ s₁ : SumDiv C,
        SumDiv.toDiv C s₀ = posPart C h → SumDiv.toDiv C s₁ = negPart C h →
        SumDiv.sumOfPoints C f s₀ = SumDiv.sumOfPoints C f s₁ by
    exact key _ h rfl hh hnc s₀ s₁ hs₀ hs₁
  intro N
  refine Nat.strong_induction_on N ?_
  intro n ih
  intro h hN hh hnc s₀ s₁ hs₀ hs₁
  by_cases hsep : Algebra.IsSeparable ↥(baseField C h) ↥C.functionField
  · exact H h hh hnc hsep s₀ s₁ hs₀ hs₁
  · have htr : Transcendental k h := fun halg =>
      hnc (Work.CurveBasics.Basic.eq_algebraMap_of_isAlgebraic C halg)
    have hchar : ¬ CharZero k := by
      intro hcz
      haveI := hcz
      haveI hfd : FiniteDimensional ↥(baseField C h) ↥C.functionField :=
        Work.CurveBasics.Order.finiteDimensional_adjoin_functionField C htr
      haveI : CharZero ↥(baseField C h) := inferInstance
      haveI : PerfectField ↥(baseField C h) := PerfectField.ofCharZero
      exact hsep inferInstance
    have hprime : (ringChar k).Prime := by
      rcases CharP.char_is_prime_or_zero k (ringChar k) with hp | h0
      · exact hp
      · exact absurd ((CharP.ringChar_zero_iff_CharZero k).mp h0) hchar
    obtain ⟨u, hu⟩ := Work.CurveBasics.Order.exists_pow_eq_of_not_separable C h htr
      (p := ringChar k) hprime hsep
    have hu0 : u ≠ 0 := by
      intro h0
      rw [h0, zero_pow hprime.pos.ne'] at hu
      exact hh hu.symm
    have hun : ¬ IsConstant C u := by
      rintro ⟨c, hc⟩
      refine hnc ⟨c ^ (ringChar k), ?_⟩
      rw [← hu, hc, ← map_pow]
    have hutr : Transcendental k u := by
      intro halg
      exact htr (hu ▸ halg.pow (ringChar k))
    haveI hfin : FiniteDimensional ↥(baseField C u) ↥C.functionField :=
      Work.CurveBasics.Order.finiteDimensional_adjoin_functionField C hutr
    have hlt : Module.finrank ↥(baseField C u) ↥C.functionField <
        Module.finrank ↥(baseField C h) ↥C.functionField := by
      rw [← hu]
      exact finrank_pow_adjoin_lt hutr hprime.two_le
    have hlt' : Module.finrank ↥(baseField C u) ↥C.functionField < n := hlt.trans_eq hN
    have hpos : posPart C h = ringChar k • posPart C u := by
      rw [← hu, posPart_pow]
    have hneg : negPart C h = ringChar k • negPart C u := by
      rw [← hu, negPart_pow]
    have hsplit₀ : IsSplit C (posPart C h) :=
      (Work.KeyLemma.Sum.isSplit_iff C (posPart_isEffective C h)).mpr ⟨s₀, hs₀⟩
    have hsplit₁ : IsSplit C (negPart C h) :=
      (Work.KeyLemma.Sum.isSplit_iff C (negPart_isEffective C h)).mpr ⟨s₁, hs₁⟩
    have hsplitu : IsSplit C (posPart C u) :=
      IsSplit.mono (posPart_isEffective C u) hsplit₀ (fun Q => by
        rw [hpos, Finsupp.smul_apply, nsmul_eq_mul]
        have hp1 : (1 : ℤ) ≤ ringChar k := by exact_mod_cast hprime.one_le
        have hnn : 0 ≤ (posPart C u) Q := posPart_isEffective C u Q
        nlinarith)
    have hsplitv : IsSplit C (negPart C u) :=
      IsSplit.mono (negPart_isEffective C u) hsplit₁ (fun Q => by
        rw [hneg, Finsupp.smul_apply, nsmul_eq_mul]
        have hp1 : (1 : ℤ) ≤ ringChar k := by exact_mod_cast hprime.one_le
        have hnn : 0 ≤ (negPart C u) Q := negPart_isEffective C u Q
        nlinarith)
    obtain ⟨sp₀, hsp₀⟩ :=
      (Work.KeyLemma.Sum.isSplit_iff C (posPart_isEffective C u)).mp hsplitu
    obtain ⟨sp₁, hsp₁⟩ :=
      (Work.KeyLemma.Sum.isSplit_iff C (negPart_isEffective C u)).mp hsplitv
    have hIH : SumDiv.sumOfPoints C f sp₀ = SumDiv.sumOfPoints C f sp₁ :=
      ih _ hlt' u rfl hu0 hun sp₀ sp₁ hsp₀ hsp₁
    have e0 : SumDiv.sumOfPoints C f s₀
        = (SumDiv.sumOfPoints C f sp₀) ^ (ringChar k) :=
      SumDiv.sumOfPoints_pow_of_toDiv_eq f (ringChar k) s₀ sp₀ (by rw [hs₀, hpos, hsp₀])
    have e1 : SumDiv.sumOfPoints C f s₁
        = (SumDiv.sumOfPoints C f sp₁) ^ (ringChar k) :=
      SumDiv.sumOfPoints_pow_of_toDiv_eq f (ringChar k) s₁ sp₁ (by rw [hs₁, hneg, hsp₁])
    rw [e0, e1, hIH]

end Work.KeyLemma.Curve
