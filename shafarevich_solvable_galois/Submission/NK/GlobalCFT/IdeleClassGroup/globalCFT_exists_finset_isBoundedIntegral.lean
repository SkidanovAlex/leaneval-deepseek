/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import Submission.NK.GlobalCFT.IdeleClassGroup.CompactDefs
import Submission.NK.GlobalCFT.IdeleClassGroup.count_spanSingleton_eq
import Submission.NK.GlobalCFT.IdeleClassGroup.norm_pow_le_norm_of_exp_le
import Submission.NK.GlobalCFT.IdeleClassGroup.exists_units_mul_toPrincipalIdeal_eq_of_mk_eq
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The bounded-integral representative lemma for the idèle class group

For a number field `K` there is a finite set `S` of nonarchimedean places and a constant `C ≥ 1`
such that *every* idèle becomes bounded-integral at `S` with bound `C` after multiplication by a
suitable principal idèle.  This is the arithmetic input to the compactness of the norm-one idèle
class group: it shows that every idèle class has a representative in the compact set
`normOneBounded K S C`.

## Main results

* `NK.GlobalCFT.Idele.exp`: the `q`-adic exponent of an idèle at a finite place,
* `NK.GlobalCFT.Idele.idealOf`: the fractional ideal of a number field attached to an idèle,
* `NK.GlobalCFT.IdeleClassGroup.globalCFT_exists_finset_isBoundedIntegral`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open scoped NumberField RestrictedProduct nonZeroDivisors
open NumberField IsDedekindDomain

noncomputable section

namespace NK.GlobalCFT

namespace Idele

variable {K : Type*} [Field K] [NumberField K]

/-- The `q`-adic exponent of an idèle at the finite place `q`: the integer `n` with
`Valued.v (x q) = exp (-n)`, so that `n` is the order of vanishing of `x` at `q`. -/
def exp (q : HeightOneSpectrum (𝓞 K)) (x : Idele K) : ℤ :=
  -WithZero.log (Valued.v (x (Place.ofFinite q) : q.adicCompletion K))

@[simp] theorem exp_def (q : HeightOneSpectrum (𝓞 K)) (x : Idele K) :
    exp q x = -WithZero.log (Valued.v (x (Place.ofFinite q) : q.adicCompletion K)) := rfl

/-- The valuation of a component of an idèle, in terms of `exp`. -/
theorem exp_val (q : HeightOneSpectrum (𝓞 K)) (x : Idele K) :
    Valued.v (x (Place.ofFinite q) : q.adicCompletion K) = WithZero.exp (-(exp q x)) := by
  have h : Valued.v (x (Place.ofFinite q) : q.adicCompletion K) ≠ 0 :=
    (Valuation.ne_zero_iff _).mpr (Units.ne_zero _)
  rw [exp_def, neg_neg, WithZero.exp_log h]

theorem exp_mul (q : HeightOneSpectrum (𝓞 K)) (x y : Idele K) :
    exp q (x * y) = exp q x + exp q y := by
  have hx : Valued.v (x (Place.ofFinite q) : q.adicCompletion K) ≠ 0 :=
    (Valuation.ne_zero_iff _).mpr (Units.ne_zero _)
  have hy : Valued.v (y (Place.ofFinite q) : q.adicCompletion K) ≠ 0 :=
    (Valuation.ne_zero_iff _).mpr (Units.ne_zero _)
  rw [exp_def, exp_def, exp_def, mul_apply, Units.val_mul, map_mul, WithZero.log_mul hx hy]
  ring

theorem exp_one (q : HeightOneSpectrum (𝓞 K)) : exp q (1 : Idele K) = 0 := by
  rw [exp_def, one_apply]
  simp

/-- The exponent of a principal idèle at `q` is (the negative of) the `q`-adic valuation of the
underlying element of `K`. -/
theorem exp_principalIdele (q : HeightOneSpectrum (𝓞 K)) (k : Kˣ) :
    exp q (principalIdele K k) = -WithZero.log (q.valuation K (k : K)) := by
  rw [exp_def]
  change -WithZero.log
      (Valued.v ((principalIdele K k (Place.ofFinite q)) : q.adicCompletion K))
    = -WithZero.log (q.valuation K (k : K))
  have h : Valued.v ((principalIdele K k (Place.ofFinite q)) : q.adicCompletion K)
      = q.valuation K (k : K) := by
    rw [principalIdele_apply, Units.coe_map]
    exact HeightOneSpectrum.valuedAdicCompletion_eq_valuation' q (k : K)
  rw [h]

theorem exp_eq_zero_of_mem_localUnits {q : HeightOneSpectrum (𝓞 K)} {x : Idele K}
    (h : x (Place.ofFinite q) ∈ Place.localUnits K (Place.ofFinite q)) : exp q x = 0 := by
  rw [exp_def, (Place.mem_localUnits_ofFinite_iff_valued_eq_one).mp h, WithZero.log_one,
    neg_zero]

/-- For an idèle, all but finitely many `q`-adic exponents vanish. -/
theorem finite_exp_support (x : Idele K) :
    {q : HeightOneSpectrum (𝓞 K) | exp q x ≠ 0}.Finite := by
  have h1 : {v : Place K | x v ∉ Place.localUnits K v}.Finite :=
    Filter.eventually_cofinite.mp x.2
  have h2 : {q : HeightOneSpectrum (𝓞 K) |
      x (Place.ofFinite q) ∉ Place.localUnits K (Place.ofFinite q)}.Finite :=
    h1.preimage (f := Place.ofFinite) (fun a _ b _ hab => Place.ofFinite_inj.mp hab)
  exact h2.subset fun q hq hcon => hq (exp_eq_zero_of_mem_localUnits hcon)

/-- The finitely supported exponent function of an idèle. -/
noncomputable def expFinsupp (x : Idele K) : HeightOneSpectrum (𝓞 K) →₀ ℤ :=
  Finsupp.mk (finite_exp_support x).toFinset (fun q => exp q x)
    (fun q => (Set.Finite.mem_toFinset _).trans Iff.rfl)

theorem expFinsupp_apply (x : Idele K) (q : HeightOneSpectrum (𝓞 K)) :
    expFinsupp x q = exp q x := rfl

/-- The fractional ideal of `K` attached to an idèle: the product `∏_q q ^ (exp q x)`. -/
def idealOf (x : Idele K) : FractionalIdeal (𝓞 K)⁰ K :=
  (expFinsupp x).prod fun q n => ((q.asIdeal : FractionalIdeal (𝓞 K)⁰ K) ^ n)

theorem count_idealOf (x : Idele K) (q : HeightOneSpectrum (𝓞 K)) :
    FractionalIdeal.count K q (idealOf x) = exp q x := by
  rw [idealOf, FractionalIdeal.count_finsuppProd, expFinsupp_apply]

theorem idealOf_ne_zero (x : Idele K) : idealOf x ≠ 0 := by
  rw [idealOf, Finsupp.prod]
  exact Finset.prod_ne_zero_iff.mpr
    (fun q _ => zpow_ne_zero _ (FractionalIdeal.coeIdeal_ne_zero.mpr q.ne_bot))

/-- Multiplying an idèle by a principal idèle multiplies its fractional ideal by the principal
fractional ideal generated by the multiplier. -/
theorem idealOf_principalIdele_mul (x : Idele K) (k : Kˣ) :
    idealOf (principalIdele K k * x)
      = FractionalIdeal.spanSingleton (𝓞 K)⁰ (k : K) * idealOf x := by
  have h1 := FractionalIdeal.finprod_heightOneSpectrum_factorization' (K := K)
    (I := idealOf (principalIdele K k * x)) (idealOf_ne_zero _)
  have h2 := FractionalIdeal.finprod_heightOneSpectrum_factorization' (K := K)
    (I := FractionalIdeal.spanSingleton (𝓞 K)⁰ (k : K) * idealOf x)
    (mul_ne_zero (FractionalIdeal.spanSingleton_ne_zero_iff.mpr (Units.ne_zero k))
      (idealOf_ne_zero x))
  rw [← h1, ← h2]
  exact finprod_congr fun q => by
    rw [count_idealOf, exp_mul, exp_principalIdele, FractionalIdeal.count_mul K q
      (FractionalIdeal.spanSingleton_ne_zero_iff.mpr (Units.ne_zero k)) (idealOf_ne_zero x),
      NK.GlobalCFT.IdeleClassGroup.count_spanSingleton_eq q (Units.ne_zero k),
      count_idealOf]

end Idele

namespace IdeleClassGroup

variable {K : Type*} [Field K] [NumberField K]

/-! ### Chosen integral representatives of the ideal classes -/

/-- A chosen nonzero integral ideal in each ideal class. -/
noncomputable def classRep (K : Type*) [Field K] [NumberField K]
    (c : ClassGroup (𝓞 K)) : (Ideal (𝓞 K))⁰ :=
  Classical.choose (ClassGroup.mk0_surjective c)

theorem mk0_classRep (K : Type*) [Field K] [NumberField K] (c : ClassGroup (𝓞 K)) :
    ClassGroup.mk0 (classRep K c) = c :=
  Classical.choose_spec (ClassGroup.mk0_surjective c)

/-- The finite set of finite places at which an ideal has nonzero `q`-adic order of vanishing. -/
noncomputable def supportFinset (K : Type*) [Field K] [NumberField K] (J : Ideal (𝓞 K)) :
    Finset (HeightOneSpectrum (𝓞 K)) :=
  (Filter.eventually_cofinite.mp
    (FractionalIdeal.finite_factors (K := K) (J : FractionalIdeal (𝓞 K)⁰ K))).toFinset

theorem mem_supportFinset {J : Ideal (𝓞 K)} {q : HeightOneSpectrum (𝓞 K)} :
    q ∈ supportFinset K J ↔
      FractionalIdeal.count K q (J : FractionalIdeal (𝓞 K)⁰ K) ≠ 0 := by
  rw [supportFinset, Set.Finite.mem_toFinset]
  rfl

/-- The finite set of places supporting all the chosen class representatives. -/
noncomputable def goodS (K : Type*) [Field K] [NumberField K] :
    Finset (HeightOneSpectrum (𝓞 K)) := by
  classical
  exact Finset.univ.biUnion fun c : ClassGroup (𝓞 K) => supportFinset K (classRep K c)

theorem mem_goodS {q : HeightOneSpectrum (𝓞 K)} :
    q ∈ goodS K ↔ ∃ c : ClassGroup (𝓞 K), q ∈ supportFinset K (classRep K c) := by
  classical
  simp only [goodS, Finset.mem_biUnion, Finset.mem_univ, true_and]

/-- A uniform bound for the orders of vanishing of all chosen class representatives. -/
noncomputable def goodN (K : Type*) [Field K] [NumberField K] : ℕ := by
  classical
  exact (Finset.univ : Finset (ClassGroup (𝓞 K))).sup fun c =>
    (supportFinset K (classRep K c)).sup fun q =>
      (FractionalIdeal.count K q
        ((classRep K c : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K)).toNat

theorem count_classRep_le_goodN {c : ClassGroup (𝓞 K)} {q : HeightOneSpectrum (𝓞 K)}
    (hq : q ∈ goodS K) :
    FractionalIdeal.count K q
        ((classRep K c : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) ≤ (goodN K : ℤ) := by
  classical
  by_cases h : q ∈ supportFinset K (classRep K c : Ideal (𝓞 K))
  · have h1 : (FractionalIdeal.count K q
        ((classRep K c : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K)).toNat ≤ goodN K :=
      le_trans
        (Finset.le_sup (s := supportFinset K (classRep K c : Ideal (𝓞 K)))
          (f := fun q => (FractionalIdeal.count K q
            ((classRep K c : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K)).toNat) h)
        (Finset.le_sup (s := (Finset.univ : Finset (ClassGroup (𝓞 K))))
          (f := fun c => (supportFinset K (classRep K c)).sup fun q =>
            (FractionalIdeal.count K q
              ((classRep K c : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K)).toNat)
          (Finset.mem_univ c))
    have h2 := FractionalIdeal.count_coe_nonneg (K := K) q (classRep K c : Ideal (𝓞 K))
    calc FractionalIdeal.count K q
          ((classRep K c : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K)
        = ((FractionalIdeal.count K q
            ((classRep K c : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K)).toNat : ℤ) :=
          (Int.toNat_of_nonneg h2).symm
      _ ≤ (goodN K : ℤ) := by exact_mod_cast h1
  · have hz : FractionalIdeal.count K q
        ((classRep K c : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) = 0 := by
      by_contra hne
      exact h (mem_supportFinset.mpr hne)
    rw [hz]
    exact Nat.cast_nonneg _

theorem count_classRep_eq_zero_of_notMem_goodS {c : ClassGroup (𝓞 K)}
    {q : HeightOneSpectrum (𝓞 K)} (hq : q ∉ goodS K) :
    FractionalIdeal.count K q
        ((classRep K c : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) = 0 := by
  classical
  by_contra hne
  exact hq (mem_goodS.mpr ⟨c, mem_supportFinset.mpr hne⟩)

/-- A uniformizer at a finite place `q`, i.e. an element of `K` of `q`-adic valuation `1`. -/
noncomputable def uniformizer (K : Type*) [Field K] [NumberField K]
    (q : HeightOneSpectrum (𝓞 K)) : K :=
  Classical.choose (HeightOneSpectrum.valuation_exists_uniformizer K q)

theorem uniformizer_spec (K : Type*) [Field K] [NumberField K]
    (q : HeightOneSpectrum (𝓞 K)) :
    q.valuation K (uniformizer K q) = WithZero.exp (-1 : ℤ) :=
  Classical.choose_spec (HeightOneSpectrum.valuation_exists_uniformizer K q)

theorem uniformizer_ne_zero (K : Type*) [Field K] [NumberField K]
    (q : HeightOneSpectrum (𝓞 K)) : uniformizer K q ≠ 0 := by
  intro h0
  have h := uniformizer_spec K q
  rw [h0, map_zero] at h
  exact WithZero.exp_ne_zero h.symm

/-- The constant `C` bounding the local norms inside `goodS`: the largest of the inverses of the
`N`-th powers of the norms of the chosen uniformizers. -/
noncomputable def goodC (K : Type*) [Field K] [NumberField K] : ℝ :=
  max 1 (∑ q ∈ goodS K, (‖(uniformizer K q : q.adicCompletion K)‖ ^ goodN K)⁻¹)

theorem one_le_goodC (K : Type*) [Field K] [NumberField K] : 1 ≤ goodC K :=
  le_max_left _ _

theorem inv_goodC_le_norm_pow (K : Type*) [Field K] [NumberField K]
    {q : HeightOneSpectrum (𝓞 K)} (hq : q ∈ goodS K) :
    (goodC K)⁻¹ ≤ ‖(uniformizer K q : q.adicCompletion K)‖ ^ goodN K := by
  classical
  set a : ℝ := (‖(uniformizer K q : q.adicCompletion K)‖ ^ goodN K)⁻¹ with ha
  have hne : (uniformizer K q : q.adicCompletion K) ≠ 0 := by
    intro h0
    have h1 : Valued.v (uniformizer K q : q.adicCompletion K) = 0 :=
      (Valuation.zero_iff _).mpr h0
    rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation', uniformizer_spec K q] at h1
    exact WithZero.exp_ne_zero h1
  have hnorm : 0 < ‖(uniformizer K q : q.adicCompletion K)‖ := norm_pos_iff.mpr hne
  have ha0 : 0 < a := by
    rw [ha]; exact inv_pos.mpr (pow_pos hnorm _)
  have hac : a ≤ goodC K := by
    rw [ha, goodC]
    exact le_trans
      (Finset.single_le_sum
        (f := fun q => (‖(uniformizer K q : q.adicCompletion K)‖ ^ goodN K)⁻¹)
        (fun i _ => inv_nonneg.mpr (pow_nonneg (norm_nonneg _) _)) hq)
      (le_max_right _ _)
  have hC0 : 0 < goodC K := lt_of_lt_of_le zero_lt_one (one_le_goodC K)
  calc (goodC K)⁻¹ ≤ a⁻¹ := (inv_le_inv₀ hC0 ha0).mpr hac
    _ = ‖(uniformizer K q : q.adicCompletion K)‖ ^ goodN K := by rw [ha, inv_inv]

/-- **Choosing the representative.**  For every idèle `x` whose ideal class is `c`, some principal
multiple of `x` has the chosen representative `classRep K c` as its fractional ideal. -/
theorem exists_principalIdele_idealOf_eq_classRep (x : Idele K) (c : ClassGroup (𝓞 K))
    (hc : c = ClassGroup.mk K (Units.mk0 (Idele.idealOf x) (Idele.idealOf_ne_zero x))) :
    ∃ t : Kˣ, Idele.idealOf (Idele.principalIdele K t * x)
      = ((classRep K c : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) := by
  have hclass : ClassGroup.mk K (Units.mk0 (Idele.idealOf x) (Idele.idealOf_ne_zero x))
      = ClassGroup.mk K (FractionalIdeal.mk0 K (classRep K c)) := by
    rw [ClassGroup.mk_mk0, mk0_classRep]
    exact hc.symm
  obtain ⟨t, ht⟩ := exists_units_mul_toPrincipalIdeal_eq_of_mk_eq hclass
  refine ⟨t, ?_⟩
  have h := congrArg (fun z : (FractionalIdeal (𝓞 K)⁰ K)ˣ => (z : FractionalIdeal (𝓞 K)⁰ K)) ht
  simp only [Units.val_mul, Units.val_mk0, coe_toPrincipalIdeal, FractionalIdeal.coe_mk0] at h
  rw [Idele.idealOf_principalIdele_mul,
    mul_comm (FractionalIdeal.spanSingleton (𝓞 K)⁰ (t : K)) (Idele.idealOf x)]
  exact h

end IdeleClassGroup

end NK.GlobalCFT

namespace NK.GlobalCFT.IdeleClassGroup

theorem globalCFT_exists_finset_isBoundedIntegral {K : Type*} [Field K] [NumberField K] :
    ∃ (S : Finset (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) (C : ℝ),
      1 ≤ C ∧ ∀ x : NK.GlobalCFT.Idele K, ∃ k : Kˣ,
        NK.GlobalCFT.IdeleClassGroup.IsBoundedIntegral K S C
          (NK.GlobalCFT.Idele.principalIdele K k * x) := by
  classical
  refine ⟨goodS K, goodC K, one_le_goodC K, fun x => ?_⟩
  set c : ClassGroup (𝓞 K) :=
    ClassGroup.mk K (Units.mk0 (Idele.idealOf x) (Idele.idealOf_ne_zero x)) with hc
  obtain ⟨t, ht⟩ := exists_principalIdele_idealOf_eq_classRep x c hc
  refine ⟨t, ?_⟩
  have hexp : ∀ q, Idele.exp q (Idele.principalIdele K t * x)
      = FractionalIdeal.count K q ((classRep K c : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) := by
    intro q
    rw [← Idele.count_idealOf, ht]
  refine ⟨?_, ?_⟩
  · intro q hq
    have h1 : FractionalIdeal.count K q
        ((classRep K c : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) = 0 :=
      count_classRep_eq_zero_of_notMem_goodS hq
    have h2 : Idele.exp q (Idele.principalIdele K t * x) = 0 := by rw [hexp q, h1]
    have h3 : Valued.v
        (((Idele.principalIdele K t * x) (Place.ofFinite q)) : q.adicCompletion K) = 1 := by
      rw [Idele.exp_val, h2, neg_zero, WithZero.exp_zero]
    exact norm_eq_one_of_mem_localUnits_ofFinite
      ((Place.mem_localUnits_ofFinite_iff_valued_eq_one).mpr h3)
  · intro q hq
    have hle : FractionalIdeal.count K q
        ((classRep K c : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) ≤ (goodN K : ℤ) :=
      count_classRep_le_goodN hq
    have hnn : (0 : ℤ) ≤ FractionalIdeal.count K q
        ((classRep K c : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) :=
      FractionalIdeal.count_coe_nonneg (K := K) q (classRep K c : Ideal (𝓞 K))
    have hval : Valued.v
        (((Idele.principalIdele K t * x) (Place.ofFinite q)) : q.adicCompletion K)
        = WithZero.exp (-(Idele.exp q (Idele.principalIdele K t * x))) :=
      Idele.exp_val q _
    constructor
    · have hb : WithZero.exp (-(goodN K : ℤ)) ≤ Valued.v
          (((Idele.principalIdele K t * x) (Place.ofFinite q)) : q.adicCompletion K) := by
        rw [hval, hexp q]
        exact WithZero.exp_le_exp.mpr (by omega)
      exact le_trans (inv_goodC_le_norm_pow K hq)
        (norm_pow_le_norm_of_exp_le q (uniformizer_spec K q) hb)
    · rw [Valued.toNormedField.norm_le_one_iff, hval, hexp q]
      exact WithZero.exp_le_exp.mpr (by omega)

end NK.GlobalCFT.IdeleClassGroup
