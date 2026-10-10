import Mathlib
import Submission.Work.MotK.TGen.FwVec4Defs
import Submission.Work.MotK.TGen.FwVec4FracRange
import Submission.Work.MotK.TGen.FdivNeZero

set_option linter.unusedVariables false -- v435-speed

/-!
# `Work.MotK.TGen.FwVec4Height2` — the kernel of the parametrisation of `{f̂₄ = 0}` has height 1

The presentation map `fwTheta a b h : K[x₀,x₁,x₂] →ₐ[K] K(u,v)` of the quartic (junk) divisor
`f̂₄ = fwVec a b h 4` of the `T`-twisted link is the substitution `x_j ↦ p_j = pl_{j+1}/pl₄` of
`Submission/Work/MotK/TGen/FwVec4Rational.lean`.  The present file proves that its kernel is a
homogeneous (height one) ideal of `K[x₀,x₁,x₂]` from the four parametrisation facts of
`Work.MotK.TGen.FwVec4Param`:

* `θ f̂₄ = 0`, `θ f̂₃ ≠ 0`, `u · θ f̂₃ = θ f̂₁`, `v · θ f̂₃ = θ f̂₂`.

The mathematical content is the dimension count

  `height (ker θ) = dim K[x₀,x₁,x₂] - dim (im θ) = 3 - trdeg_K K(u,v) = 1`,

formalised without the `dim = trdeg` bridge: `im θ` is a finitely generated domain over `K` whose
fraction field is the two-variable rational function field `RatFunc (RatFunc K)` (this is
`Work.MotK.TGen.FwVec4FracRange`, whose hypotheses are exactly `h3`, `h1`, `h2`), hence the
quotient `K[x₀,x₁,x₂] ⧸ ker θ` carries a chain of two primes (`two_primes_of_trdeg` below, proved
by Noether normalisation: a finitely generated domain over a field whose fraction field has
transcendence degree `≥ 2` has dimension `≥ 2`); pulling the chain back to `K[x₀,x₁,x₂]` along
`Ideal.Quotient.mk (ker θ)` and using `height p + 1 ≤ height q` for a strictly increasing chain of
primes gives

  `height (ker θ) + 2 ≤ ringKrullDim K[x₀,x₁,x₂] = 3`,  i.e.  `height (ker θ) ≤ 1`.

The reverse inequality is `f̂₄ ∈ ker θ` with `f̂₄ ≠ 0`.
-/

universe u

namespace Work.MotK.TGen

open MvPolynomial

/-- A finitely generated domain `A` over a field `K` (in the same universe) whose fraction field
has transcendence degree at least two has two nested primes, one of which is non-zero.

Proof: Noether normalisation (`exists_finite_inj_algHom_of_fg`) writes `A` as a finite
`K[T₁,…,T_s]`-algebra with `s = trdeg_K (FractionRing A) ≥ 2`; the prime `(T₁)` of height one of
`K[T]` lifts to `A` by lying over, and going up lifts a chain of length two ending in a prime of
height `≥ 2`, giving a strictly increasing pair `𝔭₁ < 𝔭₂` whose lower member is non-zero
(incomparability of the integral extension). -/
private theorem two_primes_of_trdeg {K A : Type u} [Field K] [CommRing A] [IsDomain A]
    [Algebra K A] [Algebra.FiniteType K A] (h : 2 ≤ Algebra.trdeg K (FractionRing A)) :
    ∃ 𝔭₁ 𝔭₂ : Ideal A, 𝔭₁.IsPrime ∧ 𝔭₂.IsPrime ∧ 𝔭₁ < 𝔭₂ ∧ 𝔭₁ ≠ ⊥ := by
  obtain ⟨s, g, hg_inj, hg_fin⟩ := exists_finite_inj_algHom_of_fg K A
  letI : Algebra (MvPolynomial (Fin s) K) A := g.toRingHom.toAlgebra
  haveI hFin : Module.Finite (MvPolynomial (Fin s) K) A := hg_fin
  haveI hInt : Algebra.IsIntegral (MvPolynomial (Fin s) K) A := Algebra.IsIntegral.of_finite _ _
  have hinj : Function.Injective (algebraMap (MvPolynomial (Fin s) K) A) := by
    show Function.Injective (g : MvPolynomial (Fin s) K → A)
    exact hg_inj
  haveI hFaith : FaithfulSMul (MvPolynomial (Fin s) K) A :=
    (faithfulSMul_iff_algebraMap_injective (MvPolynomial (Fin s) K) A).mpr hinj
  -- the transcendence degree of the normalisation equals `s`
  have htrA : Algebra.trdeg K (FractionRing A) = Algebra.trdeg K A := by
    haveI : Algebra.IsAlgebraic A (FractionRing A) :=
      (IsFractionRing.comap_isAlgebraic_iff (A := A) (K := FractionRing A)
        (C := FractionRing A)).mpr inferInstance
    have hh := trdeg_add_eq K A (A := FractionRing A)
    have hz : Algebra.trdeg A (FractionRing A) = 0 := trdeg_eq_zero
    rw [hz, add_zero] at hh
    exact hh.symm
  have htr : Algebra.trdeg K A = Algebra.trdeg K (MvPolynomial (Fin s) K) := by
    have hh := trdeg_add_eq K (MvPolynomial (Fin s) K) (A := A)
    have hz : Algebra.trdeg (MvPolynomial (Fin s) K) A = 0 := trdeg_eq_zero
    rw [hz, add_zero] at hh
    exact hh.symm
  have hs : 2 ≤ s := by
    have h2 := h
    rw [htrA, htr, MvPolynomial.trdeg_of_isDomain, Cardinal.mk_fin,
      Cardinal.lift_natCast] at h2
    exact Nat.cast_le.mp h2
  -- `K[T₁, …, T_s]` has a prime of height at least two
  have hdimS : ringKrullDim (MvPolynomial (Fin s) K) = s := by
    rw [MvPolynomial.ringKrullDim_of_isNoetherianRing_of_finite, ringKrullDim_eq_zero_of_field,
      zero_add, Nat.card_fin]
  obtain ⟨p, hp, hpht⟩ := Ideal.exists_isPrime_le_height
    (R := MvPolynomial (Fin s) K) (n := 2) (by rw [hdimS]; exact_mod_cast hs)
  haveI := hp
  obtain ⟨l, -, hlen⟩ := Order.exists_series_of_le_height (⟨p, hp⟩ : PrimeSpectrum _)
    (n := 2) (by rw [← PrimeSpectrum.height_eq_orderHeight]; exact hpht)
  -- lift the chain of length two along the integral extension `K[T] → A`
  have hker : Ideal.under (MvPolynomial (Fin s) K) (⊥ : Ideal A)
      ≤ (RelSeries.head l).asIdeal := by
    rw [Ideal.under_def, ← RingHom.ker_eq_comap_bot,
      (RingHom.injective_iff_ker_eq_bot _).mp hinj]
    exact bot_le
  obtain ⟨P₀, -, hP₀, hP₀over⟩ :=
    Ideal.exists_ideal_over_prime_of_isIntegral (RelSeries.head l).asIdeal (⊥ : Ideal A) hker
  haveI := hP₀
  have hlo : P₀.LiesOver (RelSeries.head l).asIdeal := (Ideal.liesOver_iff _ _).mpr hP₀over.symm
  obtain ⟨L, hLlen, -, -⟩ := Ideal.exists_ltSeries_of_hasGoingUp l P₀
  -- two of the primes of the lifted chain
  set i₁ : Fin (L.length + 1) := ⟨1, by omega⟩ with hi₁
  set i₂ : Fin (L.length + 1) := ⟨2, by omega⟩ with hi₂
  have hlt12 : i₁ < i₂ := by
    rw [hi₁, hi₂, Fin.lt_def]
    norm_num
  refine ⟨(L i₁).asIdeal, (L i₂).asIdeal, (L i₁).isPrime, (L i₂).isPrime,
    L.strictMono hlt12, ?_⟩
  intro hbot
  set i₀ : Fin (L.length + 1) := ⟨0, by omega⟩ with hi₀
  have hlt01 : i₀ < i₁ := by
    rw [hi₀, hi₁, Fin.lt_def]
    norm_num
  have hunder := Ideal.IsIntegral.under_lt_under (R := MvPolynomial (Fin s) K)
    (I := (L i₀).asIdeal) (J := (L i₁).asIdeal) (L.strictMono hlt01)
  have hbot_under : (⊥ : Ideal A).under (MvPolynomial (Fin s) K) = ⊥ := by
    rw [Ideal.under_def, ← RingHom.ker_eq_comap_bot,
      (RingHom.injective_iff_ker_eq_bot _).mp hinj]
  rw [hbot, hbot_under] at hunder
  exact absurd hunder (not_lt_of_ge bot_le)

/-- `RatFunc K = Frac K[t]` is algebraic over `K[t]`, so `trdeg_K RatFunc K = trdeg_K K[t] = 1`. -/
private lemma trdeg_ratFunc_eq_one (K : Type*) [Field K] : Algebra.trdeg K (RatFunc K) = 1 := by
  haveI : Algebra.IsAlgebraic (Polynomial K) (RatFunc K) :=
    (IsFractionRing.comap_isAlgebraic_iff (A := Polynomial K) (K := RatFunc K)
      (C := RatFunc K)).mpr inferInstance
  have hz : Algebra.trdeg (Polynomial K) (RatFunc K) = 0 := trdeg_eq_zero
  have h := trdeg_add_eq K (Polynomial K) (A := RatFunc K)
  rw [hz, add_zero] at h
  rw [Polynomial.trdeg_of_isDomain] at h
  exact h.symm

/-- `trdeg_K RatFunc (RatFunc K) = 2`: the tower law, both layers contributing one. -/
private lemma trdeg_ratFunc_ratFunc_eq_two (K : Type*) [Field K] :
    Algebra.trdeg K (RatFunc (RatFunc K)) = 2 := by
  have h1 : Algebra.trdeg K (RatFunc K) = 1 := trdeg_ratFunc_eq_one K
  have h2 : Algebra.trdeg (RatFunc K) (RatFunc (RatFunc K)) = 1 := by
    haveI : Algebra.IsAlgebraic (Polynomial (RatFunc K)) (RatFunc (RatFunc K)) :=
      (IsFractionRing.comap_isAlgebraic_iff (A := Polynomial (RatFunc K))
        (K := RatFunc (RatFunc K)) (C := RatFunc (RatFunc K))).mpr inferInstance
    have hz : Algebra.trdeg (Polynomial (RatFunc K)) (RatFunc (RatFunc K)) = 0 := trdeg_eq_zero
    have h := trdeg_add_eq (RatFunc K) (Polynomial (RatFunc K)) (A := RatFunc (RatFunc K))
    rw [hz, add_zero] at h
    rw [Polynomial.trdeg_of_isDomain] at h
    exact h.symm
  have h := trdeg_add_eq K (RatFunc K) (A := RatFunc (RatFunc K))
  rw [h1, h2] at h
  rw [← h]
  norm_num

theorem FwVec4Height2 {K : Type} [Field K] (a b h : K) (ha : a ≠ 0) (hb : b ≠ 0) (hh : h ≠ 0)
    (h4 : Work.MotK.TGen.fwTheta a b h (Work.MotK.TGen.fwVec a b h 4) = 0)
    (h3 : Work.MotK.TGen.fwTheta a b h (Work.MotK.TGen.fwVec a b h 3) ≠ 0)
    (h1 : Work.MotK.TGen.fwU K * Work.MotK.TGen.fwTheta a b h (Work.MotK.TGen.fwVec a b h 3)
      = Work.MotK.TGen.fwTheta a b h (Work.MotK.TGen.fwVec a b h 1))
    (h2 : Work.MotK.TGen.fwV K * Work.MotK.TGen.fwTheta a b h (Work.MotK.TGen.fwVec a b h 3)
      = Work.MotK.TGen.fwTheta a b h (Work.MotK.TGen.fwVec a b h 2)) :
    (RingHom.ker (Work.MotK.TGen.fwTheta a b h)).height = 1 := by
  set P : Ideal (MvPolynomial (Fin 3) K) := RingHom.ker (fwTheta a b h)
  haveI hPprime : P.IsPrime := RingHom.ker_isPrime _
  -- The fraction field of `K[x₀,x₁,x₂] ⧸ ker θ` is the two-variable rational function field.
  have htr : 2 ≤ Algebra.trdeg K (FractionRing (MvPolynomial (Fin 3) K ⧸ P)) := by
    obtain ⟨e⟩ := FwVec4FracRange a b h ha hb hh h3 h1 h2
    have e1 : (MvPolynomial (Fin 3) K ⧸ RingHom.ker (fwTheta a b h)) ≃ₐ[K]
        (fwTheta a b h).range :=
      Ideal.quotientKerEquivRange (fwTheta a b h)
    obtain ⟨e2⟩ := Work.CrauderKatz.BlowUp.fractionRing_algEquiv_of_algEquiv e1
    have e3 : FractionRing (MvPolynomial (Fin 3) K ⧸ P) ≃ₐ[K] RatFunc (RatFunc K) := e2.trans e
    have hte := AlgEquiv.trdeg_eq e3
    rw [hte, trdeg_ratFunc_ratFunc_eq_two]
  -- Two nested primes in the quotient, and their pullbacks to `K[x₀,x₁,x₂]`.
  obtain ⟨𝔭₁, 𝔭₂, h𝔭₁, h𝔭₂, hlt, hne⟩ :=
    two_primes_of_trdeg (A := MvPolynomial (Fin 3) K ⧸ P) htr
  haveI := h𝔭₁
  haveI := h𝔭₂
  have hQ₁prime : (𝔭₁.comap (Ideal.Quotient.mk P)).IsPrime := Ideal.comap_isPrime _ _
  have hQ₂prime : (𝔭₂.comap (Ideal.Quotient.mk P)).IsPrime := Ideal.comap_isPrime _ _
  haveI := hQ₁prime
  haveI := hQ₂prime
  have hPQ₁ : P ≤ 𝔭₁.comap (Ideal.Quotient.mk P) := by
    have h := Ideal.ker_le_comap (Ideal.Quotient.mk P) (K := 𝔭₁)
    rwa [Ideal.mk_ker] at h
  have hlt₁ : P < 𝔭₁.comap (Ideal.Quotient.mk P) := by
    refine lt_of_le_of_ne hPQ₁ fun heq => hne ?_
    have hm := Ideal.map_comap_of_surjective (Ideal.Quotient.mk P)
      Ideal.Quotient.mk_surjective 𝔭₁
    have hmap : Ideal.map (Ideal.Quotient.mk P) (Ideal.comap (Ideal.Quotient.mk P) 𝔭₁) = ⊥ := by
      rw [heq.symm, Ideal.map_quotient_self]
    exact hm.symm.trans hmap
  have hlt₂ : 𝔭₁.comap (Ideal.Quotient.mk P) < 𝔭₂.comap (Ideal.Quotient.mk P) := by
    refine lt_of_le_of_ne (Ideal.comap_mono hlt.le) fun heq => ?_
    have hA := Ideal.map_comap_of_surjective (Ideal.Quotient.mk P)
      Ideal.Quotient.mk_surjective 𝔭₁
    have hB := Ideal.map_comap_of_surjective (Ideal.Quotient.mk P)
      Ideal.Quotient.mk_surjective 𝔭₂
    have hAB : 𝔭₁ = 𝔭₂ := by rw [← hA, ← hB, heq]
    exact absurd hAB (ne_of_lt hlt)
  -- `ringKrullDim K[x₀,x₁,x₂] = 3`, so a chain of length two above `ker θ` gives `height ≤ 1`.
  have hdim : ringKrullDim (MvPolynomial (Fin 3) K) = 3 := by
    rw [MvPolynomial.ringKrullDim_of_isNoetherianRing_of_finite, ringKrullDim_eq_zero_of_field]
    norm_num
  have ha1 : P.height + 1 ≤ (𝔭₁.comap (Ideal.Quotient.mk P)).height :=
    Ideal.height_add_one_le_of_lt_of_isPrime hlt₁
  have hb1 : (𝔭₁.comap (Ideal.Quotient.mk P)).height + 1
      ≤ (𝔭₂.comap (Ideal.Quotient.mk P)).height :=
    Ideal.height_add_one_le_of_lt_of_isPrime hlt₂
  have hc2 : (𝔭₂.comap (Ideal.Quotient.mk P)).height ≤ 3 := by
    have h := Ideal.height_le_ringKrullDim_of_isPrime (I := 𝔭₂.comap (Ideal.Quotient.mk P))
    rw [hdim] at h
    exact WithBot.coe_le_coe.mp h
  have hle : P.height ≤ 1 := by
    have key : P.height + (1 + 1) ≤ 1 + (1 + 1) := by
      calc P.height + (1 + 1) = (P.height + 1) + 1 := by rw [add_assoc]
        _ ≤ (𝔭₁.comap (Ideal.Quotient.mk P)).height + 1 := add_le_add ha1 le_rfl
        _ ≤ (𝔭₂.comap (Ideal.Quotient.mk P)).height := hb1
        _ ≤ 3 := hc2
        _ = 1 + (1 + 1) := by norm_num
    exact (ENat.add_le_add_iff_right (by norm_num : ((1 : ℕ∞) + 1) ≠ ⊤)).mp key
  -- `f̂₄ ∈ ker θ` is non-zero, so the height is at least one.
  have hf4 : fwVec a b h 4 ≠ 0 := by
    intro h0
    have hF : Fdiv a b h = Work.MotK.GambT a b h * fwVec a b h 4 := rfl
    exact FdivNeZero a b h ha hb hh (by rw [hF, h0, mul_zero])
  have hge : (1 : ℕ∞) ≤ P.height := by
    have hmem : fwVec a b h 4 ∈ nonZeroDivisors (MvPolynomial (Fin 3) K) := by
      rw [mem_nonZeroDivisors_iff]
      refine ⟨?_, ?_⟩
      · intro x hx
        rcases mul_eq_zero.mp hx with hc | hc
        · exact absurd hc hf4
        · exact hc
      · intro x hx
        rcases mul_eq_zero.mp hx with hc | hc
        · exact hc
        · exact absurd hc hf4
    have hone := Ideal.one_le_height_span_singleton_of_mem_nonZeroDivisors hmem
    have hle' : Ideal.span {fwVec a b h 4} ≤ P := by
      rw [Ideal.span_le, Set.singleton_subset_iff]
      exact RingHom.mem_ker.mpr h4
    exact hone.trans (Ideal.height_mono hle')
  exact le_antisymm hle hge

end Work.MotK.TGen
