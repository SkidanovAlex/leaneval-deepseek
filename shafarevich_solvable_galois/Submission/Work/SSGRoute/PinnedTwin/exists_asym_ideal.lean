import Mathlib.RingTheory.Henselian
import Mathlib.Data.Int.Star
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.RingTheory.IntegralClosure.IntegralRestrict
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.NumberTheory.NumberField.Completion.InfinitePlace
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import Submission.Work.SSGRoute.PinnedTwin.Basic
import Submission.Work.SSGRoute.PinnedTwin.exists_primes_not_conj_avoid
import Submission.Work.SSGRoute.PinnedTwin.exists_signPattern_notMem_range
import Submission.Work.SSGRoute.ZDataMup.weakApprox_pos_numberField
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# An asymmetric ideal for an involution of a number field

This file proves `Work.SSGRoute.PinnedTwin.exists_asym_ideal`: given an involution `ρ` of a finite
Galois extension `k ⊆ K` of number fields, an ideal `A₀ ≠ 0` whose class is `ρ`-stable with twist
unit `u₀` (`rhoIdeal ρ A₀ = A₀ · (u₀)`), there are a modulus `𝔪` (with `𝔪.pos = ∅`, `ρ`-stable
exponents, and support coprime to `A₀`) and an ideal `I = A₀·(y)` (coprime to `𝔪`) whose ray class
modulo `𝔪` is *not* fixed by `ρ`:

`classOfIdeal K U(𝔪) (rhoIdeal ρ I) ≠ classOfIdeal K U(𝔪) I` .

## Strategy

The ray class of `I` is `ρ`-fixed iff the twist `u₀·ρ(y)/y` is congruent to a global unit modulo
`𝔪`.  Taking `𝔪` supported (with exponent `2`) on a `ρ`-stable set `s ⊔ ρ(s)` of primes and taking
`y` so that `y ≡ u₀ σ_p` and `y ≡ 1` modulo the squares of `p` and `ρp` respectively, the fixedness
of the ray class of `I` forces `e ≡ σ_p (mod p²)` for every `p ∈ s`; choosing the sign pattern `σ`
so that it is not attained by the unit group (`exists_signPattern_notMem_range`) gives the
contradiction.

The two construction inputs are

* `exists_moved_primes` — arbitrarily many primes outside a given finite set and outside their own
  `ρ`-translate (via the fixed field `K^ρ` and the Dirichlet density of the completely split
  primes, `NK.UchidaKummer.exists_splitsCompletely_notMem` plus freeness);
* `ZDataMup.weakApprox_pos_numberField` — the approximation which realises the prescribed
  residues of `y`.
-/

namespace Work.SSGRoute.PinnedTwin

set_option linter.unusedSectionVars false

open NumberField IsDedekindDomain
open scoped NumberField nonZeroDivisors
open Commons.NumberTheory.NumberField.Completion (placeSmul)

attribute [local instance] Classical.propDecidable

set_option maxHeartbeats 12000000

section MovedPrimes

variable {k K : Type} [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K]
  [FiniteDimensional k K] [IsGalois k K]

/-- The fixed field of `⟨ρ⟩`: the subfield of elements fixed by the involution `ρ`. -/
private noncomputable def fixedFieldOf (ρ : K ≃ₐ[k] K) : IntermediateField k K :=
  IntermediateField.fixedField (Subgroup.zpowers ρ)

private theorem rho_fixes_fixedFieldOf (ρ : K ≃ₐ[k] K) {x : K} (hx : x ∈ fixedFieldOf ρ) :
    ρ x = x :=
  (IntermediateField.mem_fixedField_iff (Subgroup.zpowers ρ) x).mp hx ρ (Subgroup.mem_zpowers ρ)

/-- `ρ` viewed as an automorphism of `K` over its fixed field `K^ρ`.  The two automorphisms have the
same underlying map, hence the same action on primes. -/
private noncomputable def rhoL (ρ : K ≃ₐ[k] K) :
    K ≃ₐ[↥(fixedFieldOf ρ)] K :=
  AlgEquiv.ofRingEquiv (R := ↥(fixedFieldOf ρ)) (f := ρ.toRingEquiv)
    (fun x => rho_fixes_fixedFieldOf ρ x.2)

private theorem rhoL_apply (ρ : K ≃ₐ[k] K) (x : K) : rhoL ρ x = ρ x := rfl

/-- The action of `ρ` and of `ρ` viewed over the fixed field `K^ρ` on the primes of `𝓞 K` agree. -/
private theorem placeSmul_rhoL_eq (ρ : K ≃ₐ[k] K) (q : HeightOneSpectrum (𝓞 K)) :
    Commons.NumberTheory.NumberField.Completion.placeSmul
        (K := ↥(fixedFieldOf ρ)) (L := K) (rhoL ρ) q
      = Commons.NumberTheory.NumberField.Completion.placeSmul ρ q := by
  apply IsDedekindDomain.HeightOneSpectrum.ext
  rw [Commons.NumberTheory.NumberField.Completion.placeSmul_asIdeal,
    Commons.NumberTheory.NumberField.Completion.placeSmul_asIdeal]
  congr 1

/-- **A prime moved by a nontrivial involution, outside a prescribed finite set.**

`ρ ≠ 1` means that the fixed field `K^ρ` is a proper subfield of `K`; the primes of `K` above a
prime of `K^ρ` which splits completely in `K` come in pairs exchanged by `ρ`.  Completely split
primes have positive Dirichlet density, hence their set is infinite and meets the complement of any
finite set of primes of `K^ρ`. -/
private theorem exists_prime_placeSmul_ne_avoid (ρ : K ≃ₐ[k] K) (hρ1 : ρ ≠ 1)
    (F : Finset (HeightOneSpectrum (𝓞 K))) :
    ∃ q : HeightOneSpectrum (𝓞 K), q ∉ F ∧
      Commons.NumberTheory.NumberField.Completion.placeSmul ρ q ≠ q := by
  classical
  haveI : FiniteDimensional ↥(fixedFieldOf ρ) K := inferInstance
  haveI : IsGalois ↥(fixedFieldOf ρ) K := IsGalois.of_fixed_field K (Subgroup.zpowers ρ)
  haveI : NumberField ↥(fixedFieldOf ρ) :=
    Commons.NumberTheory.NumberField.numberField_of_intermediateField (fixedFieldOf ρ)
  set T : Finset (HeightOneSpectrum (𝓞 ↥(fixedFieldOf ρ))) :=
    F.image (fun q => HeightOneSpectrum.under (𝓞 ↥(fixedFieldOf ρ)) q) with hT
  obtain ⟨p, hpT, hp⟩ :=
    NK.UchidaKummer.exists_splitsCompletely_notMem (K := ↥(fixedFieldOf ρ)) (L := K) T
  obtain ⟨Q, hQ⟩ := NK.Chebotarev.exists_primeIdeal_liesOver
    (K := ↥(fixedFieldOf ρ)) (L := K) p
  refine ⟨Q, ?_, ?_⟩
  · intro hQF
    have h1 : HeightOneSpectrum.under (𝓞 ↥(fixedFieldOf ρ)) Q ∈ T :=
      Finset.mem_image.mpr ⟨Q, hQF, rfl⟩
    have h2 : HeightOneSpectrum.under (𝓞 ↥(fixedFieldOf ρ)) Q = p := by
      apply IsDedekindDomain.HeightOneSpectrum.ext
      rw [IsDedekindDomain.HeightOneSpectrum.under_asIdeal, hQ.over]
    rw [h2] at h1
    exact hpT h1
  · intro hfix
    have hfixL : Commons.NumberTheory.NumberField.Completion.placeSmul
        (K := ↥(fixedFieldOf ρ)) (L := K) (rhoL ρ) Q = Q := by
      rw [placeSmul_rhoL_eq]; exact hfix
    have h1 : rhoL ρ = 1 :=
      NK.UchidaKummer.eq_one_of_placeSmul_eq_of_splitsCompletely hp hQ hfixL
    refine hρ1 (AlgEquiv.ext fun x => ?_)
    have h2 := congrArg (fun (f : K ≃ₐ[↥(fixedFieldOf ρ)] K) => f x) h1
    simpa [rhoL_apply] using h2

/-- **Arbitrarily many primes moved by the involution, avoiding a finite set.**

Iterating `exists_prime_placeSmul_ne_avoid` and keeping track of the conjugates already chosen
gives a set `s` of `N` primes, none in the bad set `F`, none of which has its `ρ`-translate in `s`
(in particular, each of them is moved by `ρ`). -/
private theorem exists_moved_primes (ρ : K ≃ₐ[k] K) (hρ2 : ρ ^ 2 = 1) (hρ1 : ρ ≠ 1)
    (F : Finset (HeightOneSpectrum (𝓞 K))) (N : ℕ) :
    ∃ s : Finset (HeightOneSpectrum (𝓞 K)),
      s.card = N ∧ (∀ p ∈ s, p ∉ F) ∧
      (∀ p ∈ s, Commons.NumberTheory.NumberField.Completion.placeSmul ρ p ∉ s) := by
  classical
  induction N with
  | zero => exact ⟨∅, rfl, by simp, by simp⟩
  | succ n ih =>
    obtain ⟨s, hcard, hF, hmoved⟩ := ih
    obtain ⟨q, hq, hqne⟩ := exists_prime_placeSmul_ne_avoid ρ hρ1
      (F ∪ s ∪ s.image (Commons.NumberTheory.NumberField.Completion.placeSmul ρ))
    have hqF : q ∉ F := fun h => hq (Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inl h))))
    have hqs : q ∉ s := fun h => hq (Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inr h))))
    have hqconj : ∀ p ∈ s, Commons.NumberTheory.NumberField.Completion.placeSmul ρ p ≠ q := by
      intro p hp hpq
      exact hq (Finset.mem_union.mpr (Or.inr (Finset.mem_image.mpr ⟨p, hp, hpq⟩)))
    refine ⟨insert q s, ?_, ?_, ?_⟩
    · rw [Finset.card_insert_of_notMem hqs, hcard]
    · intro p hp
      rw [Finset.mem_insert] at hp
      rcases hp with rfl | hp
      · exact hqF
      · exact hF p hp
    · intro p hp
      rcases Finset.mem_insert.mp hp with hpq | hps
      · -- `p = q`: the conjugate `ρ q` is not in `insert q s`
        intro hmem
        rcases Finset.mem_insert.mp hmem with hconj | hconjs
        · exact hqne (hpq ▸ hconj)
        · exact hq (Finset.mem_union.mpr (Or.inr (Finset.mem_image.mpr
            ⟨Commons.NumberTheory.NumberField.Completion.placeSmul ρ p, hconjs,
              by rw [placeSmul_placeSmul ρ hρ2 p, hpq]⟩)))
      · intro hmem
        rcases Finset.mem_insert.mp hmem with hconj | hconjs
        · exact hqconj p hps hconj
        · exact hmoved p hps hconjs

end MovedPrimes

section Core

variable {k K : Type} [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K]
  [FiniteDimensional k K] [IsGalois k K]

open IsDedekindDomain

/-- **Equivariance of the `q`-adic valuation under the Galois action.** -/
private theorem valuation_placeSmul (ρ : K ≃ₐ[k] K) (q : HeightOneSpectrum (𝓞 K)) (x : K) :
    (Commons.NumberTheory.NumberField.Completion.placeSmul ρ q).valuation K (ρ x)
      = q.valuation K x := by
  exact Commons.RingTheory.DedekindDomain.valuation_map_of_map_eq
    (R := 𝓞 K) (K := K) (rhoRing ρ) ρ.toRingEquiv
    (fun r => (algebraMap_galRestrict_apply (𝓞 k) ρ r).symm) q
    (Commons.NumberTheory.NumberField.Completion.placeSmul ρ q)
    (Commons.NumberTheory.NumberField.Completion.placeSmul_asIdeal ρ q) x

/-- **The local step of the contradiction.**

Suppose `u₀` and `e` are units at `q`, the residues of `y` and of `ρy` at `q²` are `u₀σ` and `1`,
and `u₀·ρy·e ≡ y (mod q²)`.  Then `e ≡ σ (mod q²)`.  The point is that the two residues `y|q`
and `ρy|q` are *linked* by `ρ` (they come from one global element), so the freedom available in
choosing the residue of `y` at `q` and at `ρq` forces the residue of `e`. -/
private theorem cong_step (ρ : K ≃ₐ[k] K) {q : HeightOneSpectrum (𝓞 K)} {u₀ y e σ : K}
    (hu : q.valuation K u₀ = 1) (he : q.valuation K e = 1)
    (hy : q.valuation K (y - u₀ * σ) ≤ WithZero.exp (-(2 : ℤ)))
    (hρy : q.valuation K (ρ y - 1) ≤ WithZero.exp (-(2 : ℤ)))
    (hcong : q.valuation K (u₀ * ρ y * e - y) ≤ WithZero.exp (-(2 : ℤ))) :
    q.valuation K (e - σ) ≤ WithZero.exp (-(2 : ℤ)) := by
  have hkey : u₀ * e - u₀ * σ
      = (u₀ * ρ y * e - y) + (y - u₀ * σ) + (u₀ * e) * (1 - ρ y) := by ring
  have h3 : q.valuation K ((u₀ * e) * (1 - ρ y)) ≤ WithZero.exp (-(2 : ℤ)) := by
    rw [show (u₀ * e) * (1 - ρ y) = -((u₀ * e) * (ρ y - 1)) by ring, Valuation.map_neg,
      Valuation.map_mul, Valuation.map_mul, hu, he, one_mul, one_mul]
    exact hρy
  have h12 : q.valuation K ((u₀ * ρ y * e - y) + (y - u₀ * σ))
      ≤ WithZero.exp (-(2 : ℤ)) :=
    (Valuation.map_add_le_max' _ _ _).trans (max_le hcong hy)
  have hsum : q.valuation K ((u₀ * ρ y * e - y) + (y - u₀ * σ) + (u₀ * e) * (1 - ρ y))
      ≤ WithZero.exp (-(2 : ℤ)) :=
    (Valuation.map_add_le_max' _ _ _).trans (max_le h12 h3)
  rw [← hkey] at hsum
  rwa [show u₀ * e - u₀ * σ = u₀ * (e - σ) by ring, Valuation.map_mul, hu, one_mul] at hsum

/-- Congruence test for the quotient `𝓞 K ⧸ q ^ n`. -/
private theorem quot_eq_of_sub_mem {q : HeightOneSpectrum (𝓞 K)} {n : ℕ} {x a : 𝓞 K}
    (h : x - a ∈ q.asIdeal ^ n) :
    Ideal.Quotient.mk (q.asIdeal ^ n) x = Ideal.Quotient.mk (q.asIdeal ^ n) a :=
  (Ideal.Quotient.eq (I := q.asIdeal ^ n)).mpr (by simpa using h)

/-- The valuation bound `v_q(x - a) ≤ exp(-n)` for integral elements is the congruence
`x ≡ a (mod qⁿ)`. -/
private theorem mem_pow_of_valuation_le {q : HeightOneSpectrum (𝓞 K)} {n : ℕ} {x a : 𝓞 K}
    (h : q.valuation K ((x - a : 𝓞 K) : K) ≤ WithZero.exp (-(n : ℤ))) :
    x - a ∈ q.asIdeal ^ n := by
  refine (HeightOneSpectrum.intValuation_le_pow_iff_mem (v := q) (x - a) n).mp ?_
  rwa [HeightOneSpectrum.valuation_of_algebraMap] at h

end Core

section Build

variable {k K : Type} [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K]
  [FiniteDimensional k K] [IsGalois k K]

open IsDedekindDomain

/-- The modulus with exponent `2` on a finite set `S` of primes and `pos = ∅`. -/
private noncomputable def modulusOf (S : Finset (HeightOneSpectrum (𝓞 K))) :
    NK.NUV2.RouteB.Modulus K := by
  classical
  exact
    { exps := fun r => if r ∈ S then 2 else 0
      finite_support := by
        rw [NK.NUV2.RouteB.HasFiniteSupport, Filter.eventually_cofinite]
        refine S.finite_toSet.subset fun r hr => by
          by_contra h
          exact hr (by rw [if_neg (by simpa using h)])
      pos := ∅ }

private theorem modulusOf_exps (S : Finset (HeightOneSpectrum (𝓞 K))) (r : HeightOneSpectrum (𝓞 K)) :
    (modulusOf S).exps r = if r ∈ S then 2 else 0 := rfl

private theorem modulusOf_pos (S : Finset (HeightOneSpectrum (𝓞 K))) :
    (modulusOf S).pos = ∅ := rfl

private theorem modulusOf_stable (ρ : K ≃ₐ[k] K)
    (S : Finset (HeightOneSpectrum (𝓞 K))) (hS : ∀ r, placeSmul ρ r ∈ S ↔ r ∈ S) :
    ∀ r, (modulusOf S).exps (placeSmul ρ r) = (modulusOf S).exps r := by
  intro r
  change (if placeSmul ρ r ∈ S then 2 else 0) = (if r ∈ S then 2 else 0)
  by_cases h : placeSmul ρ r ∈ S
  · rw [if_pos h, if_pos ((hS r).mp h)]
  · rw [if_neg h, if_neg (fun hc => h ((hS r).mpr hc))]

/-- The valuations of a unit of `𝓞 K` are trivial. -/
private theorem unit_valuation_eq_one (q : HeightOneSpectrum (𝓞 K)) (e : (𝓞 K)ˣ) :
    q.valuation K ((e : 𝓞 K) : K) = 1 := by
  rw [HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_eq_one_iff]
  intro hmem
  exact q.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem q.asIdeal hmem e.isUnit)

/-- Cancelling a nonzero fractional ideal. -/
private theorem spanSingleton_eq_of_mul_eq {A : FractionalIdeal (nonZeroDivisors (𝓞 K)) K}
    (hA : A ≠ 0) {α w : K}
    (h : A * FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K)) α
      = A * FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K)) w) :
    FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K)) α
      = FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K)) w :=
  mul_left_cancel₀ hA h

/-- Two elements generating the same principal fractional ideal differ by a unit of `𝓞 K`. -/
private theorem exists_unit_mul_eq_of_spanSingleton_eq {α w : K}
    (h : FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K)) α
      = FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K)) w) :
    ∃ e : (𝓞 K)ˣ, α = ((e : 𝓞 K) : K) * w := by
  obtain ⟨z, hz⟩ := FractionalIdeal.spanSingleton_eq_spanSingleton.mp h
  have hz' : ((z : 𝓞 K) : K) * α = w := by
    rw [← hz, Units.smul_def, Algebra.smul_def]
  have hzne : ((z : 𝓞 K) : K) ≠ 0 := by
    intro h0
    have h1 : ((z⁻¹ : (𝓞 K)ˣ) : 𝓞 K) * (z : 𝓞 K) = 1 := by simp
    have h2 : (((z⁻¹ : (𝓞 K)ˣ) : 𝓞 K) : K) * (((z : 𝓞 K) : K)) = 1 := by
      rw [← map_mul, h1]
      exact map_one _
    rw [h0, mul_zero] at h2
    exact one_ne_zero h2.symm
  refine ⟨z⁻¹, ?_⟩
  have hmul : (((z⁻¹ : (𝓞 K)ˣ) : 𝓞 K) : K) * (((z : 𝓞 K) : K)) = 1 := by
    rw [← map_mul, Units.inv_mul, map_one]
  have hinv : (((z⁻¹ : (𝓞 K)ˣ) : 𝓞 K) : K) = (((z : 𝓞 K) : K))⁻¹ :=
    eq_inv_of_mul_eq_one_left hmul
  rw [hinv, ← hz', ← mul_assoc, inv_mul_cancel₀ hzne, one_mul]

/-- Multiplying a congruence by a unit at `q`. -/
private theorem cong_mul_unit {q : HeightOneSpectrum (𝓞 K)} {x a y : K}
    (hy : q.valuation K y = 1)
    (h : q.valuation K (x - a) ≤ WithZero.exp (-(2 : ℤ))) :
    q.valuation K (x * y - a * y) ≤ WithZero.exp (-(2 : ℤ)) := by
  rw [show x * y - a * y = (x - a) * y by ring, Valuation.map_mul, hy, mul_one]
  exact h

/-- `ρ` acts on ideals as an involution. -/
private theorem rhoIdeal_rhoIdeal (ρ : K ≃ₐ[k] K) (hρ2 : ρ ^ 2 = 1) (I : Ideal (𝓞 K)) :
    rhoIdeal ρ (rhoIdeal ρ I) = I := by
  rw [rhoIdeal, rhoIdeal, Ideal.map_map]
  conv_rhs => rw [← Ideal.map_id I]
  congr 1
  ext x
  simpa using rhoRing_mul_self ρ hρ2 x

/-- Divisibility is transported by `ρ`. -/
private theorem dvd_rhoIdeal (ρ : K ≃ₐ[k] K) {I J : Ideal (𝓞 K)} (h : I ∣ J) :
    rhoIdeal ρ I ∣ rhoIdeal ρ J := by
  obtain ⟨c, rfl⟩ := h
  exact ⟨rhoIdeal ρ c, by rw [rhoIdeal_mul]⟩

/-- An element congruent to `1` modulo `q²` is a unit at `q`. -/
private theorem valuation_eq_one_of_sub_one {q : HeightOneSpectrum (𝓞 K)} {x : K}
    (h : q.valuation K (x - 1) ≤ WithZero.exp (-(2 : ℤ))) :
    q.valuation K x = 1 := by
  have h1 : q.valuation K (1 : K) = 1 := Valuation.map_one _
  have hlt : q.valuation K (x - 1) < q.valuation K (1 : K) := by
    rw [h1]
    exact lt_of_le_of_lt h (WithZero.exp_lt_exp.mpr (by norm_num))
  rw [show x = (x - 1) + 1 by ring,
    Valuation.map_add_eq_of_lt_right (q.valuation K) (x := x - 1) (y := 1) hlt, h1]

/-- An element congruent to a unit `a` modulo `q²` is a unit at `q`. -/
private theorem valuation_eq_of_sub_le {q : HeightOneSpectrum (𝓞 K)} {x a : K}
    (ha : q.valuation K a = 1)
    (h : q.valuation K (x - a) ≤ WithZero.exp (-(2 : ℤ))) :
    q.valuation K x = 1 := by
  have hlt : q.valuation K (x - a) < q.valuation K a := by
    rw [ha]
    exact lt_of_le_of_lt h (WithZero.exp_lt_exp.mpr (by norm_num))
  rw [show x = (x - a) + a by ring,
    Valuation.map_add_eq_of_lt_right (q.valuation K) (x := x - a) (y := a) hlt, ha]

/-- A principal fractional ideal that is a multiple of `(y)` for an algebraic integer `y`. -/
private theorem coeIdeal_mul_span_singleton (I : Ideal (𝓞 K)) (y : 𝓞 K) :
    ((I * Ideal.span {y} : Ideal (𝓞 K)) : FractionalIdeal (nonZeroDivisors (𝓞 K)) K)
      = (I : FractionalIdeal (nonZeroDivisors (𝓞 K)) K)
        * FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K)) ((y : 𝓞 K) : K) := by
  rw [FractionalIdeal.coeIdeal_mul, FractionalIdeal.coeIdeal_span_singleton]

end Build

theorem exists_asym_ideal {k K : Type} [Field k] [NumberField k] [Field K] [NumberField K]
    [Algebra k K] [FiniteDimensional k K] [IsGalois k K]
    (ρ : K ≃ₐ[k] K) (hρ2 : ρ ^ 2 = 1) (hρ1 : ρ ≠ 1)
    (A₀ : Ideal (NumberField.RingOfIntegers K)) (hA₀ : A₀ ≠ 0) (u₀ : Kˣ)
    (hu₀ : ((Work.SSGRoute.PinnedTwin.rhoIdeal ρ A₀ :
        Ideal (NumberField.RingOfIntegers K)) :
        FractionalIdeal (nonZeroDivisors (NumberField.RingOfIntegers K)) K)
        = (A₀ : FractionalIdeal (nonZeroDivisors (NumberField.RingOfIntegers K)) K) *
          FractionalIdeal.spanSingleton (nonZeroDivisors (NumberField.RingOfIntegers K)) (u₀ : K)) :
    ∃ (𝔪 : NK.NUV2.RouteB.Modulus K)
      (I : Ideal (NumberField.RingOfIntegers K)),
      𝔪.pos = ∅ ∧
      (∀ q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
        𝔪.exps (Commons.NumberTheory.NumberField.Completion.placeSmul ρ q) = 𝔪.exps q) ∧
      (∀ q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
        𝔪.exps q ≠ 0 → ¬ q.asIdeal ∣ A₀) ∧
      I ≠ 0 ∧
      (∀ q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
        𝔪.exps q ≠ 0 → ¬ q.asIdeal ∣ I) ∧
      (∃ y : Kˣ, (I : FractionalIdeal (nonZeroDivisors (NumberField.RingOfIntegers K)) K)
        = (A₀ : FractionalIdeal (nonZeroDivisors (NumberField.RingOfIntegers K)) K) *
          FractionalIdeal.spanSingleton (nonZeroDivisors (NumberField.RingOfIntegers K)) (y : K)) ∧
      NK.HeckeL.classOfIdeal K (NK.NUV2.RouteB.CongSubgroup K 𝔪)
          (Work.SSGRoute.PinnedTwin.rhoIdeal ρ I) ≠
        NK.HeckeL.classOfIdeal K (NK.NUV2.RouteB.CongSubgroup K 𝔪) I := by
  -- ## The bad set: the primes dividing `2` or `A₀`, together with their `ρ`-translates
  have h2fin : {q : HeightOneSpectrum (𝓞 K) | (2 : 𝓞 K) ∈ q.asIdeal}.Finite :=
    finite_setOf_two_mem_asIdeal K
  have hAfin : {q : HeightOneSpectrum (𝓞 K) | q.asIdeal ∣ A₀}.Finite := Ideal.finite_factors hA₀
  set F₀ : Finset (HeightOneSpectrum (𝓞 K)) := h2fin.toFinset ∪ hAfin.toFinset with hF₀def
  have hF₀mem : ∀ q, q ∈ F₀ ↔ (2 : 𝓞 K) ∈ q.asIdeal ∨ q.asIdeal ∣ A₀ := by
    intro q
    rw [hF₀def, Finset.mem_union, Set.Finite.mem_toFinset h2fin,
      Set.Finite.mem_toFinset hAfin]
    simp only [Set.mem_setOf_eq]
  set F : Finset (HeightOneSpectrum (𝓞 K)) := F₀ ∪ F₀.image (fun q => placeSmul ρ q) with hFdef
  have hFmem : ∀ q, q ∈ F ↔ q ∈ F₀ ∨ ∃ a ∈ F₀, placeSmul ρ a = q := by
    intro q
    rw [hFdef, Finset.mem_union, Finset.mem_image]
  have hFρ : ∀ q, q ∈ F → placeSmul ρ q ∈ F := by
    intro q hq
    rw [hFmem] at hq ⊢
    rcases hq with hq | ⟨a, ha, haq⟩
    · exact Or.inr ⟨q, hq, rfl⟩
    · left
      rw [← haq, placeSmul_placeSmul ρ hρ2]
      exact ha
  have hFρ' : ∀ q, placeSmul ρ q ∈ F → q ∈ F := by
    intro q hq
    have h := hFρ (placeSmul ρ q) hq
    rwa [placeSmul_placeSmul ρ hρ2 q] at h
  have hF2 : ∀ q, (2 : 𝓞 K) ∈ q.asIdeal → q ∈ F := by
    intro q hq
    exact hFρ' q (by
      rw [hFmem]
      exact Or.inr ⟨q, (hF₀mem q).mpr (Or.inl hq), rfl⟩)
  have hFA : ∀ q, q.asIdeal ∣ A₀ → q ∈ F := by
    intro q hq
    exact hFρ' q (by
      rw [hFmem]
      exact Or.inr ⟨q, (hF₀mem q).mpr (Or.inr hq), rfl⟩)
  have hA0ne : (A₀ : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) ≠ 0 :=
    FractionalIdeal.coeIdeal_ne_zero.mpr hA₀
  have hρA0neFrac : (rhoIdeal ρ A₀ : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) ≠ 0 := by
    rw [hu₀]
    exact mul_ne_zero hA0ne
      (FractionalIdeal.spanSingleton_ne_zero_iff.mpr (Units.ne_zero u₀))
  have hρA0ne : rhoIdeal ρ A₀ ≠ 0 := by
    intro h
    refine hρA0neFrac ?_
    rw [h, Ideal.zero_eq_bot]
    exact FractionalIdeal.coeIdeal_bot
  by_cases hcase : ∃ q, q ∉ F ∧ placeSmul ρ q ≠ q ∧ q.valuation K (u₀ : K) ≠ 1
  · -- ## Case 1: `u₀` fails to be a unit at a moved prime outside the bad set
    obtain ⟨q, hqF, hqne, hqu⟩ := hcase
    have hqFA : ¬ q.asIdeal ∣ A₀ := fun h => hqF (hFA q h)
    have hq'F : placeSmul ρ q ∉ F := fun h => hqF (hFρ' q h)
    have hq'FA : ¬ (placeSmul ρ q).asIdeal ∣ A₀ := fun h => hq'F (hFA (placeSmul ρ q) h)
    set S : Finset (HeightOneSpectrum (𝓞 K)) := {q, placeSmul ρ q} with hSdef
    have hqS : q ∈ S := by rw [hSdef]; exact Finset.mem_insert_self q _
    have hSρ : ∀ r, placeSmul ρ r ∈ S ↔ r ∈ S := by
      intro r
      rw [hSdef, Finset.mem_insert, Finset.mem_singleton, Finset.mem_insert,
        Finset.mem_singleton]
      constructor
      · rintro (h | h)
        · right; rw [← placeSmul_placeSmul ρ hρ2 r, h]
        · left; rw [← placeSmul_placeSmul ρ hρ2 r, h, placeSmul_placeSmul ρ hρ2 q]
      · rintro (h | h)
        · right; rw [h]
        · left; rw [h, placeSmul_placeSmul ρ hρ2 q]
    have hcopA : ∀ r, (modulusOf S).exps r ≠ 0 → ¬ r.asIdeal ∣ A₀ := by
      intro r hr
      have hrS : r ∈ S := by
        by_contra h
        exact hr (by rw [modulusOf_exps, if_neg h])
      rcases Finset.mem_insert.mp hrS with h | h
      · rw [h]; exact hqFA
      · rw [Finset.mem_singleton.mp h]; exact hq'FA
    have hcopρA : ∀ r, (modulusOf S).exps r ≠ 0 → ¬ r.asIdeal ∣ rhoIdeal ρ A₀ := by
      intro r hr
      have hrS : r ∈ S := by
        by_contra h
        exact hr (by rw [modulusOf_exps, if_neg h])
      rcases Finset.mem_insert.mp hrS with h | h
      · rw [h]
        intro hdvd
        have h2 : (placeSmul ρ q).asIdeal ∣ A₀ := by
          have h3 := dvd_rhoIdeal ρ hdvd
          rwa [rhoIdeal_asIdeal ρ q, rhoIdeal_rhoIdeal ρ hρ2] at h3
        exact hq'F (hFA _ h2)
      · rw [Finset.mem_singleton.mp h]
        intro hdvd
        have h2 : q.asIdeal ∣ A₀ := by
          have h3 := dvd_rhoIdeal ρ hdvd
          rwa [rhoIdeal_asIdeal ρ (placeSmul ρ q), placeSmul_placeSmul ρ hρ2 q,
            rhoIdeal_rhoIdeal ρ hρ2] at h3
        exact hqF (hFA q h2)
    refine ⟨modulusOf S, A₀, modulusOf_pos S, modulusOf_stable ρ S hSρ, hcopA, hA₀, hcopA,
      ⟨1, ?_⟩, ?_⟩
    · rw [show ((1 : Kˣ) : K) = (1 : K) from rfl, FractionalIdeal.spanSingleton_one, mul_one]
    · intro heq
      have hcrit := NK.NUV2.RouteB.RayModulus.classOfIdeal_eq_iff K (modulusOf S)
        (rhoIdeal ρ A₀) A₀ hρA0ne hA₀ hcopρA hcopA
      obtain ⟨α, hαne, hαcong, hαeq⟩ := hcrit.mp heq
      have hspan : FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K)) α
          = FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K)) (u₀ : K) :=
        spanSingleton_eq_of_mul_eq hA0ne (hαeq.symm.trans hu₀)
      obtain ⟨e, he⟩ := exists_unit_mul_eq_of_spanSingleton_eq hspan
      have hqexps : (modulusOf S).exps q ≠ 0 := by
        rw [modulusOf_exps, if_pos hqS]
        norm_num
      have hqexp2 : (modulusOf S).exps q = 2 := by rw [modulusOf_exps, if_pos hqS]
      have hbound := hαcong.1 q hqexps
      rw [Commons.NumberTheory.NumberField.val_algebraMap_adicCompletion_eq, hqexp2] at hbound
      have hαval : q.valuation K α ≠ 1 := by
        rw [he, Valuation.map_mul, unit_valuation_eq_one q e, one_mul]
        exact hqu
      have h1 : q.valuation K (-1 : K) = 1 := by
        rw [show (-1 : K) = -(1 : K) by ring, Valuation.map_neg, Valuation.map_one]
      rw [show α - 1 = α + (-1) by ring] at hbound
      rcases lt_or_gt_of_ne hαval with hlt | hgt
      · rw [Valuation.map_add_eq_of_lt_right _ (by rw [h1]; exact hlt), h1] at hbound
        exact absurd hbound (not_le.mpr (WithZero.exp_lt_exp.mpr (by norm_num)))
      · rw [Valuation.map_add_eq_of_lt_left _ (by rw [h1]; exact hgt)] at hbound
        exact absurd hbound
          (not_le.mpr (lt_trans (WithZero.exp_lt_exp.mpr (by norm_num)) hgt))
  · -- ## Case 2: `u₀` is a unit at every moved prime outside the bad set
    push Not at hcase
    obtain ⟨s, hscard, hsF, hsmoved⟩ :=
      exists_moved_primes ρ hρ2 hρ1 F (NumberField.Units.rank K + 2)
    have hsrank : NumberField.Units.rank K + 1 < s.card := by rw [hscard]; omega
    have hs2 : ∀ q ∈ s, (2 : 𝓞 K) ∉ q.asIdeal := fun q hq hmem => hsF q hq (hF2 q hmem)
    obtain ⟨ε, hε⟩ := exists_signPattern_notMem_range s hs2 hsrank
    let sp : HeightOneSpectrum (𝓞 K) → 𝓞 K := fun q => if ε q = 0 then 1 else -1
    let S : Finset (HeightOneSpectrum (𝓞 K)) := s ∪ s.image (fun q => placeSmul ρ q)
    have hSdef : S = s ∪ s.image (fun q => placeSmul ρ q) := rfl
    have hSρ : ∀ r, placeSmul ρ r ∈ S ↔ r ∈ S := by
      intro r
      rw [hSdef, Finset.mem_union, Finset.mem_union, Finset.mem_image, Finset.mem_image]
      constructor
      · rintro (h | ⟨p, hp, hpr⟩)
        · right; exact ⟨placeSmul ρ r, h, placeSmul_placeSmul ρ hρ2 r⟩
        · left
          rw [← placeSmul_placeSmul ρ hρ2 r, ← hpr, placeSmul_placeSmul ρ hρ2 p]
          exact hp
      · rintro (h | ⟨p, hp, hpr⟩)
        · right; exact ⟨r, h, rfl⟩
        · left
          rw [← hpr, placeSmul_placeSmul ρ hρ2 p]
          exact hp
    -- `u₀` is a unit at every prime of `S`
    have hunit : ∀ r ∈ S, r.valuation K (u₀ : K) = 1 := by
      intro r hrS
      have hr := hrS
      rw [hSdef] at hr
      rcases Finset.mem_union.mp hr with hr | hr
      · exact hcase r (fun h => hsF r hr h) (fun h => hsmoved r hr (by rw [h]; exact hr))
      · obtain ⟨p, hp, hpr⟩ := Finset.mem_image.mp hr
        refine hcase r (fun hF => hsF p hp (hFρ' p (by rw [hpr]; exact hF))) (fun h => ?_)
        have hpsmul : placeSmul ρ p = p := by
          calc placeSmul ρ p = r := hpr
            _ = placeSmul ρ r := h.symm
            _ = placeSmul ρ (placeSmul ρ p) := by rw [hpr]
            _ = p := placeSmul_placeSmul ρ hρ2 p
        exact hsmoved p hp (by rw [hpsmul]; exact hp)
    have hspval : ∀ r : HeightOneSpectrum (𝓞 K), r.valuation K ((sp r : 𝓞 K) : K) = 1 := by
      intro r
      by_cases hε : ε r = 0
      · rw [show sp r = (1 : 𝓞 K) from by simp only [sp, if_pos hε]]
        exact Valuation.map_one _
      · rw [show sp r = (-1 : 𝓞 K) from by simp only [sp, if_neg hε],
          show (((-1 : 𝓞 K)) : K) = -(1 : K) by simp, Valuation.map_neg, Valuation.map_one]
    -- weak approximation
    obtain ⟨y, hyne, hyapprox, _⟩ :=
      Work.SSGRoute.ZDataMup.weakApprox_pos_numberField (K := K) S (fun _ => 2)
        (fun q _ => by norm_num)
        (fun q => if q ∈ s then
            (algebraMap K (q.adicCompletion K)) ((u₀ : K) * ((sp q : 𝓞 K) : K)) else 1)
        (by
          intro q hq
          by_cases hqs : q ∈ s
          · rw [if_pos hqs, Commons.NumberTheory.NumberField.val_algebraMap_adicCompletion_eq,
              Valuation.map_mul, hunit q hq, hspval q, mul_one]
          · rw [if_neg hqs]; exact le_of_eq (Valuation.map_one _))
    have hy0 : ((y : 𝓞 K) : K) ≠ 0 :=
      fun h => hyne ((IsFractionRing.injective (𝓞 K) K) h)
    have hyapprox' : ∀ p ∈ s, p.valuation K (((y : 𝓞 K) : K) - (u₀ : K) * ((sp p : 𝓞 K) : K))
        ≤ WithZero.exp (-(2 : ℤ)) := by
      intro p hp
      have hpS : p ∈ S := by rw [hSdef]; exact Finset.mem_union_left _ hp
      have h := hyapprox p hpS
      rw [if_pos hp] at h
      rw [← RingHom.map_sub, Commons.NumberTheory.NumberField.val_algebraMap_adicCompletion_eq] at h
      exact h
    have hρy1 : ∀ p ∈ s, (placeSmul ρ p).valuation K (((y : 𝓞 K) : K) - 1)
        ≤ WithZero.exp (-(2 : ℤ)) := by
      intro p hp
      have hqS : placeSmul ρ p ∈ S := by
        rw [hSdef]
        exact Finset.mem_union_right _ (Finset.mem_image_of_mem _ hp)
      have h := hyapprox (placeSmul ρ p) hqS
      rw [if_neg (hsmoved p hp)] at h
      rw [show (1 : (placeSmul ρ p).adicCompletion K)
          = algebraMap K ((placeSmul ρ p).adicCompletion K) (1 : K) from (map_one _).symm] at h
      rw [← RingHom.map_sub,
        Commons.NumberTheory.NumberField.val_algebraMap_adicCompletion_eq] at h
      exact h
    have hρyapprox : ∀ p ∈ s, p.valuation K (ρ ((y : 𝓞 K) : K) - 1)
        ≤ WithZero.exp (-(2 : ℤ)) := by
      intro p hp
      have h2 : p.valuation K (ρ (((y : 𝓞 K) : K) - 1))
          = (placeSmul ρ p).valuation K (((y : 𝓞 K) : K) - 1) := by
        conv_lhs => rw [← placeSmul_placeSmul ρ hρ2 p]
        exact valuation_placeSmul ρ (placeSmul ρ p) (((y : 𝓞 K) : K) - 1)
      have h3 : ρ (((y : 𝓞 K) : K)) - 1 = ρ (((y : 𝓞 K) : K) - 1) := by
        rw [map_sub, map_one]
      rw [h3, h2]
      exact hρy1 p hp
    have hyunit : ∀ r ∈ S, r.valuation K ((y : 𝓞 K) : K) = 1 := by
      intro r hrS
      have hr := hrS
      rw [hSdef] at hr
      rcases Finset.mem_union.mp hr with hr | hr
      · exact valuation_eq_of_sub_le
          (a := (u₀ : K) * ((sp r : 𝓞 K) : K))
          (by rw [Valuation.map_mul, hunit r hrS, hspval r, one_mul])
          (hyapprox' r hr)
      · obtain ⟨p, hp, hpr⟩ := Finset.mem_image.mp hr
        rw [← hpr]
        exact valuation_eq_one_of_sub_one (hρy1 p hp)
    have hcopA : ∀ r ∈ S, ¬ r.asIdeal ∣ A₀ := by
      intro r hrS
      have hr := hrS
      rw [hSdef] at hr
      rcases Finset.mem_union.mp hr with hr | hr
      · exact fun h => hsF r hr (hFA r h)
      · obtain ⟨p, hp, hpr⟩ := Finset.mem_image.mp hr
        rw [← hpr]
        exact fun h => hsF p hp (hFρ' p (hFA (placeSmul ρ p) h))
    -- the twist and the ideal
    set w : K := (u₀ : K) * ρ ((y : 𝓞 K) : K) / ((y : 𝓞 K) : K) with hwdef
    set I : Ideal (𝓞 K) := A₀ * Ideal.span {y} with hIdef
    have hIne : I ≠ 0 := by
      rw [hIdef]
      exact mul_ne_zero hA₀ (by rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]; exact hyne)
    have hIneFrac : (I : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) ≠ 0 :=
      FractionalIdeal.coeIdeal_ne_zero.mpr hIne
    have hImul : (I : FractionalIdeal (nonZeroDivisors (𝓞 K)) K)
        = (A₀ : FractionalIdeal (nonZeroDivisors (𝓞 K)) K)
          * FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K)) ((y : 𝓞 K) : K) := by
      rw [hIdef]; exact coeIdeal_mul_span_singleton A₀ y
    have hspan : FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K)) (u₀ : K)
          * FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K)) (ρ ((y : 𝓞 K) : K))
        = FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K)) ((y : 𝓞 K) : K)
          * FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K)) w := by
      have hyeq : ((y : 𝓞 K) : K) * w = (u₀ : K) * ρ ((y : 𝓞 K) : K) := by
        rw [hwdef]
        field_simp
      rw [FractionalIdeal.spanSingleton_mul_spanSingleton,
        FractionalIdeal.spanSingleton_mul_spanSingleton, hyeq]
    have hweq : ((rhoIdeal ρ I : Ideal (𝓞 K)) : FractionalIdeal (nonZeroDivisors (𝓞 K)) K)
        = (I : FractionalIdeal (nonZeroDivisors (𝓞 K)) K)
          * FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K)) w := by
      have hcoe : (algebraMap (𝓞 K) K) (rhoRing ρ y) = ρ ((algebraMap (𝓞 K) K) y) :=
        algebraMap_galRestrict_apply (𝓞 k) ρ y
      have hL : ((rhoIdeal ρ I : Ideal (𝓞 K)) : FractionalIdeal (nonZeroDivisors (𝓞 K)) K)
          = (A₀ : FractionalIdeal (nonZeroDivisors (𝓞 K)) K)
            * FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K)) (u₀ : K)
            * FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K)) (ρ ((y : 𝓞 K) : K)) := by
        rw [hIdef, rhoIdeal_mul, rhoIdeal_span_singleton, FractionalIdeal.coeIdeal_mul,
          FractionalIdeal.coeIdeal_span_singleton, hu₀, hcoe]
      have hR : (I : FractionalIdeal (nonZeroDivisors (𝓞 K)) K)
            * FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K)) w
          = (A₀ : FractionalIdeal (nonZeroDivisors (𝓞 K)) K)
            * FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K)) ((y : 𝓞 K) : K)
            * FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K)) w := by
        rw [hImul]
      rw [hL, hR, mul_assoc, hspan, mul_assoc]
    have hρIneFrac : (rhoIdeal ρ I : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) ≠ 0 := by
      rw [hweq]
      refine mul_ne_zero hIneFrac (FractionalIdeal.spanSingleton_ne_zero_iff.mpr ?_)
      rw [hwdef]
      exact div_ne_zero (mul_ne_zero (Units.ne_zero u₀)
        (fun h => hy0 (ρ.injective (by rw [h, map_zero])))) hy0
    have hρIne : rhoIdeal ρ I ≠ 0 := by
      intro h
      refine hρIneFrac ?_
      rw [h, Ideal.zero_eq_bot]
      exact FractionalIdeal.coeIdeal_bot
    have hyc : ∀ r ∈ S, y ∉ r.asIdeal := by
      intro r hrS hmem
      have hv : r.valuation K ((y : 𝓞 K) : K) < 1 :=
        (HeightOneSpectrum.valuation_lt_one_iff_mem (v := r) y).mpr hmem
      rw [hyunit r hrS] at hv
      exact lt_irrefl _ hv
    have hcopIall : ∀ r ∈ S, ¬ r.asIdeal ∣ I := by
      intro r hrS hdvd
      rw [hIdef, Ideal.dvd_iff_le] at hdvd
      have hAle : A₀ ≤ r.asIdeal := by
        intro a ha
        have hmem : a * y ∈ A₀ * Ideal.span {y} :=
          Ideal.mul_mem_mul ha (Ideal.subset_span (Set.mem_singleton y))
        exact (r.isPrime.mem_or_mem (hdvd hmem)).resolve_right (hyc r hrS)
      exact hcopA r hrS (Ideal.dvd_iff_le.mpr hAle)
    refine ⟨modulusOf S, I, modulusOf_pos S, modulusOf_stable ρ S hSρ, ?_, hIne, ?_,
      ⟨Units.mk0 ((y : 𝓞 K) : K) hy0, hImul⟩, ?_⟩
    · intro r hr
      have hrS : r ∈ S := by
        by_contra h
        exact hr (by rw [modulusOf_exps, if_neg h])
      exact hcopA r hrS
    · intro r hr
      have hrS : r ∈ S := by
        by_contra h
        exact hr (by rw [modulusOf_exps, if_neg h])
      exact hcopIall r hrS
    · -- the asymmetry
      intro heq
      have hcopρI : ∀ r, (modulusOf S).exps r ≠ 0 → ¬ r.asIdeal ∣ rhoIdeal ρ I := by
        intro r hr
        have hrS : r ∈ S := by
          by_contra h
          exact hr (by rw [modulusOf_exps, if_neg h])
        intro hdvd
        have h3 := dvd_rhoIdeal ρ hdvd
        rw [rhoIdeal_rhoIdeal ρ hρ2, rhoIdeal_asIdeal ρ r] at h3
        exact hcopIall (placeSmul ρ r) ((hSρ r).mpr hrS) h3
      have hcopI : ∀ r, (modulusOf S).exps r ≠ 0 → ¬ r.asIdeal ∣ I := by
        intro r hr
        have hrS : r ∈ S := by
          by_contra h
          exact hr (by rw [modulusOf_exps, if_neg h])
        exact hcopIall r hrS
      have hcrit := NK.NUV2.RouteB.RayModulus.classOfIdeal_eq_iff K (modulusOf S)
        (rhoIdeal ρ I) I hρIne hIne hcopρI hcopI
      obtain ⟨α, hαne, hαcong, hαeq⟩ := hcrit.mp heq
      have hspan : FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K)) α
          = FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K)) w :=
        spanSingleton_eq_of_mul_eq hIneFrac (hαeq.symm.trans hweq)
      obtain ⟨e, he⟩ := exists_unit_mul_eq_of_spanSingleton_eq hspan
      have hyw : ((y : 𝓞 K) : K) * w = (u₀ : K) * ρ ((y : 𝓞 K) : K) := by
        rw [hwdef]; field_simp
      have hforce : ∀ p ∈ s, p.valuation K (((e : 𝓞 K) : K) - ((sp p : 𝓞 K) : K))
          ≤ WithZero.exp (-(2 : ℤ)) := by
        intro p hp
        have hpS : p ∈ S := by rw [hSdef]; exact Finset.mem_union_left _ hp
        have hpexps : (modulusOf S).exps p = 2 := by rw [modulusOf_exps, if_pos hpS]
        have hpb := hαcong.1 p (by rw [hpexps]; norm_num)
        rw [Commons.NumberTheory.NumberField.val_algebraMap_adicCompletion_eq, hpexps] at hpb
        have hpb' : p.valuation K ((u₀ : K) * ρ ((y : 𝓞 K) : K) * ((e : 𝓞 K) : K)
            - ((y : 𝓞 K) : K)) ≤ WithZero.exp (-(2 : ℤ)) := by
          have hy1 : p.valuation K ((y : 𝓞 K) : K) = 1 := hyunit p hpS
          have hkey : ((y : 𝓞 K) : K) * (α - 1)
              = (u₀ : K) * ρ ((y : 𝓞 K) : K) * ((e : 𝓞 K) : K) - ((y : 𝓞 K) : K) := by
            rw [he,
              show ((y : 𝓞 K) : K) * (((e : 𝓞 K) : K) * w - 1)
                = ((e : 𝓞 K) : K) * (((y : 𝓞 K) : K) * w) - ((y : 𝓞 K) : K) by ring,
              hyw]
            ring
          calc p.valuation K ((u₀ : K) * ρ ((y : 𝓞 K) : K) * ((e : 𝓞 K) : K)
                - ((y : 𝓞 K) : K))
              = p.valuation K (((y : 𝓞 K) : K) * (α - 1)) := by rw [hkey]
            _ = p.valuation K ((y : 𝓞 K) : K) * p.valuation K (α - 1) := Valuation.map_mul _ _ _
            _ = p.valuation K (α - 1) := by rw [hy1, one_mul]
            _ ≤ _ := hpb
        exact cong_step ρ (hunit p hpS) (unit_valuation_eq_one p e)
          (hyapprox' p hp) (hρyapprox p hp) hpb'
      obtain ⟨p, hp, hpcontr⟩ := hε e
      refine hpcontr ?_
      refine quot_eq_of_sub_mem ?_
      have := hforce p hp
      rw [← RingHom.map_sub] at this
      exact mem_pow_of_valuation_le (q := p) (n := 2) this

end Work.SSGRoute.PinnedTwin
