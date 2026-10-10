import Mathlib.RingTheory.Henselian
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Data.Int.Star
import Mathlib.FieldTheory.PurelyInseparable.Exponent
import Mathlib.NumberTheory.RamificationInertia.Galois
import Mathlib.NumberTheory.RamificationInertia.Valuation
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Algebra.Order.Ring.Star
import Submission.Work.SSGRoute.H2locAux.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open scoped NumberField WithZero
open NumberField

namespace Work.SSGRoute

/-! ## Auxiliary lemmas -/

/-- In the discrete value group `ℤᵐ⁰`, if a power of an element equals `exp (-e)`, then the
exponent divides `e`. -/
private lemma dvd_of_pow_eq_exp_neg {y : ℤᵐ⁰} {n e : ℕ}
    (h : y ^ n = WithZero.exp (-(e : ℤ))) : n ∣ e := by
  have hlog : (n : ℤ) * y.log = -(e : ℤ) := by
    have hc := congrArg WithZero.log h
    rw [WithZero.log_pow, WithZero.log_exp, nsmul_eq_mul] at hc
    exact hc
  have h1 : (e : ℤ) = (n : ℤ) * (-y.log) := by linarith
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    rw [Nat.zero_dvd]
    have : (e : ℤ) = 0 := by simpa using h1
    exact_mod_cast this
  · have hk : 0 ≤ -y.log := by
      have h2 : 0 ≤ (n : ℤ) * (-y.log) := by rw [← h1]; positivity
      exact nonneg_of_mul_nonneg_right h2 (by exact_mod_cast hn)
    refine ⟨(-y.log).toNat, ?_⟩
    have hnat : ((-y.log).toNat : ℤ) = -y.log := Int.toNat_of_nonneg hk
    have : (e : ℤ) = ((n * (-y.log).toNat : ℕ) : ℤ) := by
      rw [h1, Nat.cast_mul, hnat]
    exact_mod_cast this

/-- `(exp (-1)) ^ n = exp (-n)` in the discrete value group `ℤᵐ⁰`. -/
private lemma exp_neg_one_pow (n : ℕ) :
    (WithZero.exp (-1 : ℤ) : ℤᵐ⁰) ^ n = WithZero.exp (-(n : ℤ)) := by
  rw [← WithZero.exp_nsmul, nsmul_eq_mul]
  congr 1
  ring

/-- An element of `𝔭 ∖ 𝔭²` has `𝔭`-adic valuation `exp (-1)` (it is a prime element at `𝔭`). -/
private lemma intValuation_eq_exp_neg_one_of_mem_notMem_sq {K : Type*} [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) {x : 𝓞 K}
    (h1 : x ∈ v.asIdeal) (h2 : x ∉ v.asIdeal ^ 2) :
    v.intValuation x = WithZero.exp (-1 : ℤ) := by
  have hle : v.intValuation x ≤ WithZero.exp (-1 : ℤ) := by
    have := (IsDedekindDomain.HeightOneSpectrum.intValuation_le_pow_iff_mem v x 1).mpr
      (by simpa using h1)
    simpa using this
  have hgt : WithZero.exp (-2 : ℤ) < v.intValuation x := by
    refine lt_of_not_ge ?_
    intro hc
    exact h2 ((IsDedekindDomain.HeightOneSpectrum.intValuation_le_pow_iff_mem v x 2).mp
      (by simpa using hc))
  have hpos : v.intValuation x ≠ 0 := ne_of_gt (lt_of_lt_of_le WithZero.exp_pos hgt.le)
  obtain ⟨m, hm⟩ : ∃ m : ℤ, v.intValuation x = WithZero.exp m :=
    ⟨_, (WithZero.exp_log hpos).symm⟩
  rw [hm] at hle hgt ⊢
  have hmle : m ≤ -1 := WithZero.exp_le_exp.mp hle
  have hmgt : -2 < m := WithZero.exp_lt_exp.mp hgt
  have : m = -1 := by omega
  rw [this]

/-- **The valuation of the base field in a local extension**: for `K ⊆ L` number fields, places
`Q` of `K` and `q` of `L` with `q | Q`, and `a : K`, the `q`-adic valuation of `a` is the
`e(q|Q)`-th power of its `Q`-adic valuation. -/
private lemma val_liesOver_pow {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L]
    (Q : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) (q : IsDedekindDomain.HeightOneSpectrum (𝓞 L))
    (hq : q.asIdeal.LiesOver Q.asIdeal) (a : K) :
    (Q.valuation K a) ^ (q.asIdeal.ramificationIdx (𝓞 K)) = q.valuation L (algebraMap K L a) := by
  haveI : q.asIdeal.LiesOver Q.asIdeal := hq
  exact IsDedekindDomain.HeightOneSpectrum.valuation_liesOver L Q q a

/-- **A place lies over the place below it**, in the valuation-ring form: if the valuation ring of
`w` restricts to the valuation ring of `Q` then `w.asIdeal` lies over `Q.asIdeal`. -/
private lemma liesOver_of_comap_valuationSubringAtPrime {K L : Type*} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L]
    (Q : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) (w : IsDedekindDomain.HeightOneSpectrum (𝓞 L))
    (h : (IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime L w).comap (algebraMap K L)
        = IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime K Q) :
    w.asIdeal.LiesOver Q.asIdeal := by
  classical
  set C := IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime K Q with hC
  set W := IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime L w with hW
  have hCval : C = (Q.valuation K).valuationSubring := by
    rw [hC, IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring]
  have hWval : W = (w.valuation L).valuationSubring := by
    rw [hW, IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring]
  have eqQC : (Q.valuation K).IsEquiv C.valuation := by
    rw [Valuation.isEquiv_iff_valuationSubring, ValuationSubring.valuationSubring_valuation, hCval]
  have eqWL : W.valuation.IsEquiv (w.valuation L) := by
    rw [Valuation.isEquiv_iff_valuationSubring, ValuationSubring.valuationSubring_valuation, hWval]
  have key : ∀ a : K, W.valuation (algebraMap K L a) < 1 ↔ C.valuation a < 1 := by
    intro a
    have hsub : (Valuation.comap (algebraMap K L) W.valuation).valuationSubring = C := by
      ext y
      rw [Valuation.mem_valuationSubring_iff, Valuation.comap_apply, ← h, ValuationSubring.mem_comap,
        ValuationSubring.valuation_le_one_iff]
    have heq : (Valuation.comap (algebraMap K L) W.valuation).IsEquiv C.valuation := by
      rw [Valuation.isEquiv_iff_valuationSubring, hsub, ValuationSubring.valuationSubring_valuation]
    have hh := heq.lt_one_iff_lt_one (x := a)
    rwa [Valuation.comap_apply] at hh
  refine Ideal.LiesOver.mk ?_
  ext x
  rw [Ideal.mem_comap]
  rw [← IsDedekindDomain.HeightOneSpectrum.valuation_lt_one_iff_mem (K := K) Q x,
      ← IsDedekindDomain.HeightOneSpectrum.valuation_lt_one_iff_mem (K := L) w
        (algebraMap (𝓞 K) (𝓞 L) x)]
  rw [eqQC.lt_one_iff_lt_one, ← key (algebraMap (𝓞 K) K x),
      ← eqWL.lt_one_iff_lt_one, ← IsScalarTower.algebraMap_apply (𝓞 K) K L,
      show (algebraMap (𝓞 K) L x) = ((algebraMap (𝓞 K) (𝓞 L) x : 𝓞 L) : L) from rfl]

/-! ## The main result -/

/-- **There are finite levels whose inertia at the place has order divisible by an arbitrarily
large power of `p`.**

`k` a number field, `Ω` an algebraic closure, `A` a finite place of `Ω` over `k` in which `p` is
a unit (`h`), `n : ℕ`.  Then there is a finite normal level `M/k` whose inertia subgroup at the
prime of `𝓞 M` below `A` has order divisible by `p ^ n`.

Mathematical content: there are tamely ramified extensions of the local field of degree `p^n` for
every `n` (`k_𝔭(π^{1/p^n})/k_𝔭`, with `π` a uniformizer, is tamely totally ramified of degree
`p^n` because `p ≠ ℓ`, where `ℓ` is the residue characteristic).

Route.  Let `𝔭` be the prime of `k` below `A` and pick `x ∈ 𝔭 ∖ 𝔭²` (a prime element at `𝔭`;
exists since `𝔭 ≠ 𝔭²` for a nonzero prime in a Dedekind domain).  Pick `β ∈ Ω` with
`β ^ (p^n) = x` (`Ω` is algebraically closed) and let `M` be the normal closure of `k(β)` over
`k` inside `Ω` (finite, normal, and a `NumberField`).  Let `P = levelPrimeOf k Ω A hA M` be the
prime below `A` and `e := (the prime of k below A).asIdeal.ramificationIdxIn (𝓞 ↥M)`.  Then
`p ^ n ∣ e`:

* `β` is integral over `𝓞 k` (a root of the monic `T ^ (p^n) - x`), hence `β ∈ 𝓞 (k(β))`;
* factorising the principal ideal `(x)` in the Dedekind domain `𝓞 (k(β))`: the exponent of a prime
  `P' | 𝔭` in `(x)` is `e(P'|𝔭) · v_𝔭(x) = e(P'|𝔭)`, while in `(β)^{p^n} = (x)` it is
  `p^n · (the exponent of β)`, so `p^n ∣ e(P'|𝔭)`;
* ramification indices are multiplicative in towers, so `p^n ∣ e(P|𝔭)`;
* finally `Nat.card (Ideal.inertia Gal(M/k) P.asIdeal) = e` by
  `Ideal.card_inertia_eq_ramificationIdxIn` (its hypotheses hold since the residue field of a
  number field at a finite prime is finite, hence perfect).

This is `Work.SSGRoute.levelInertiaCardGrowth`.  Useful on disk:
`Ideal.card_inertia_eq_ramificationIdxIn`, `Ideal.primesOver`, `Ideal.ramificationIdx_tower`,
`Submission/Work/SSGRoute/ramificationIdx_mul_inertiaDeg_dvd_finrank.lean`. -/
theorem levelInertiaCardGrowth
    (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (A : ValuationSubring Ω) (hA : _root_.SSGRoute.IsFinPlace k A)
    (h : ¬ A.valuation ((p : ℚ) : Ω) < 1) (n : ℕ) :
    ∃ (M : IntermediateField k Ω) (_ : FiniteDimensional k M) (_ : Normal k M)
      (_ : NumberField ↥M),
      p ^ n ∣ Nat.card (Work.SSGRoute.levelInertiaOf k Ω A hA M) := by
  classical
  haveI : IsSepClosure k Ω := inferInstance
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed k
  -- The prime `𝔭` of `k` below `A`, and a prime element `x` at `𝔭`.
  set 𝔭 : IsDedekindDomain.HeightOneSpectrum (𝓞 k) := Submission.NeukirchUchida.primeOf A hA
    with h𝔭def
  have h𝔭 : A.comap (algebraMap k Ω)
      = IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime k 𝔭 :=
    Submission.NeukirchUchida.primeOf_spec A hA
  have hlt : 𝔭.asIdeal ^ 2 < 𝔭.asIdeal := by
    rw [← Ideal.dvdNotUnit_iff_lt]
    exact ⟨𝔭.ne_bot, 𝔭.asIdeal, Ideal.isUnit_iff.not.mpr 𝔭.isPrime.ne_top, sq 𝔭.asIdeal⟩
  obtain ⟨x, hx1, hx2⟩ := SetLike.exists_of_lt hlt
  have hxval : 𝔭.intValuation x = WithZero.exp (-1 : ℤ) :=
    intValuation_eq_exp_neg_one_of_mem_notMem_sq 𝔭 hx1 hx2
  -- A `p ^ n`-th root `β` of `x` in `Ω`, and the normal closure `M` of `k(β)`.
  obtain ⟨β, hβ⟩ := IsAlgClosed.exists_pow_nat_eq (algebraMap k Ω (algebraMap (𝓞 k) k x))
    (pow_pos (Fact.out : p.Prime).pos n)
  have hint : IsIntegral k β := by
    apply IsIntegral.of_pow (pow_pos (Fact.out : p.Prime).pos n)
    rw [hβ]
    exact IsIntegral.algebraMap (Algebra.IsIntegral.isIntegral (algebraMap (𝓞 k) k x))
  let L : IntermediateField k Ω := IntermediateField.adjoin k ({β} : Set Ω)
  have hLfin : FiniteDimensional k L := IntermediateField.adjoin.finiteDimensional hint
  let M : IntermediateField k Ω := IntermediateField.normalClosure k ↥L Ω
  have hMfin : FiniteDimensional k M := normalClosure.is_finiteDimensional k ↥L Ω
  have hLM : L ≤ M := IntermediateField.le_normalClosure L
  haveI : Algebra.IsAlgebraic k ↥L := Algebra.IsAlgebraic.of_finite k ↥L
  have hMIN : IsNormalClosure k ↥L ↥M :=
    Algebra.IsAlgebraic.isNormalClosure_normalClosure (fun z => IsAlgClosed.splits _)
  haveI hMnorm : Normal k M := hMIN.normal
  haveI hMint : Algebra.IsIntegral k ↥M := Algebra.IsIntegral.of_finite k ↥M
  haveI hMsep : Algebra.IsSeparable k ↥M := Algebra.IsSeparable.of_integral k ↥M
  haveI hMgal : IsGalois k ↥M := isGalois_iff.mpr ⟨hMsep, hMnorm⟩
  haveI hMcz : CharZero ↥M := inferInstance
  haveI hMfdq : FiniteDimensional ℚ ↥M := FiniteDimensional.trans ℚ k ↥M
  haveI hMNF : NumberField ↥M := NumberField.mk
  -- `β` sits in `M`, and `β ^ (p ^ n) = x` there.
  have hβL : β ∈ L := IntermediateField.subset_adjoin k ({β} : Set Ω) (Set.mem_singleton β)
  have hβM : β ∈ M := hLM hβL
  let βM : ↥M := ⟨β, hβM⟩
  have hβMpow : βM ^ (p ^ n) = algebraMap (𝓞 k) ↥M x := by
    apply Subtype.ext
    rw [SubmonoidClass.coe_pow]
    change β ^ (p ^ n) = ((algebraMap (𝓞 k) ↥M x : ↥M) : Ω)
    rw [hβ, ← IsScalarTower.algebraMap_apply (𝓞 k) k Ω]
    rfl
  -- The prime `P` of `𝓞 M` below `A` lies over `𝔭`.
  let P : IsDedekindDomain.HeightOneSpectrum (𝓞 ↥M) := Work.SSGRoute.levelPrimeOf k Ω A hA M
  have hP : A.comap (algebraMap ↥M Ω)
      = IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥M P :=
    NK.Reconstruct.primeOfLevel_spec A M (NK.Reconstruct.comap_level_ne_top hA M)
  have hcomap : (IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥M P).comap
        (algebraMap k ↥M)
      = IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime k 𝔭 := by
    rw [← hP, ← h𝔭, ValuationSubring.comap_comap, IsScalarTower.algebraMap_eq k ↥M Ω]
  have hLies : P.asIdeal.LiesOver 𝔭.asIdeal :=
    liesOver_of_comap_valuationSubringAtPrime 𝔭 P hcomap
  -- The valuation computation.
  have hvalx : 𝔭.valuation k (algebraMap (𝓞 k) k x) = WithZero.exp (-1 : ℤ) := by
    rw [IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap]
    exact hxval
  have hvalM_x : P.valuation ↥M (algebraMap (𝓞 k) ↥M x)
      = WithZero.exp (-(P.asIdeal.ramificationIdx (𝓞 k) : ℤ)) := by
    rw [IsScalarTower.algebraMap_apply (𝓞 k) k ↥M]
    rw [← val_liesOver_pow 𝔭 P hLies (algebraMap (𝓞 k) k x)]
    rw [hvalx, exp_neg_one_pow]
  have hkey : (P.valuation ↥M βM) ^ (p ^ n)
      = WithZero.exp (-(P.asIdeal.ramificationIdx (𝓞 k) : ℤ)) := by
    rw [← Valuation.map_pow, hβMpow]
    exact hvalM_x
  have hdvd : p ^ n ∣ P.asIdeal.ramificationIdx (𝓞 k) :=
    dvd_of_pow_eq_exp_neg (y := P.valuation ↥M βM) (n := p ^ n)
      (e := P.asIdeal.ramificationIdx (𝓞 k)) hkey
  -- Assemble.
  refine ⟨M, hMfin, hMnorm, hMNF, ?_⟩
  haveI hLiesI : P.asIdeal.LiesOver 𝔭.asIdeal := hLies
  haveI h𝔭prime : 𝔭.asIdeal.IsPrime := 𝔭.isPrime
  haveI hPprime : P.asIdeal.IsPrime := P.isPrime
  haveI hperf : PerfectField 𝔭.asIdeal.ResidueField :=
    Commons.NumberTheory.NumberField.perfectField_residueField_heightOneSpectrum 𝔭
  have hcard : Nat.card (Work.SSGRoute.levelInertiaOf k Ω A hA M)
      = 𝔭.asIdeal.ramificationIdxIn (𝓞 ↥M) :=
    Ideal.card_inertia_eq_ramificationIdxIn (G := ↥M ≃ₐ[k] ↥M) 𝔭.asIdeal P.asIdeal
  rw [hcard, Ideal.ramificationIdxIn_eq_ramificationIdx 𝔭.asIdeal P.asIdeal (↥M ≃ₐ[k] ↥M)]
  exact hdvd

end Work.SSGRoute
