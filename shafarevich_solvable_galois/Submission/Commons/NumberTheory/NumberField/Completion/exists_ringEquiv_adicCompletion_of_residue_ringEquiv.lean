import Mathlib
import Submission.Commons.NumberTheory.NumberField.Completion.natCard_residueField_adicCompletion_eq_pow_inertiaDeg
import Submission.Commons.RingTheory.Henselian.adicCompletionMap_mem_integers
import Submission.Commons.RingTheory.Henselian.adicCompletionMap_val_lt_one
import Submission.Commons.NumberTheory.NumberField.adicCompletion_residueField_equiv_exists
import Submission.Commons.NumberTheory.NumberField.Completion.exists_inertiaSubgroup_adicCompletion_card_eq_ramificationIdx
import Submission.Commons.NumberTheory.NumberField.Completion.natCard_algEquiv_adicCompletion_eq_ramificationIdx_mul_inertiaDeg
import Submission.Commons.NumberTheory.NumberField.Completion.exists_inertiaSubgroup_adicCompletion_isNormal_card_quotient
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option maxHeartbeats 1600000
set_option linter.style.haveILetI false
set_option linter.unusedVariables false

namespace Commons.NumberTheory.NumberField.Completion

open IsDedekindDomain.HeightOneSpectrum Polynomial

/-! ## The integer ring map and the natural map of residue fields

For the extension `L / K` of number fields and the places `q | Q` we construct, from
`adicCompletionMap Q q hq`, the ring homomorphism of integer rings
`intCompletionMap Q q hq : Q.adicCompletionIntegers K →+* q.adicCompletionIntegers L`, and the
induced map `natResidueMap Q q hq` of residue fields.  The latter is the natural map
`k_Q → k_q`; the key point in its construction is that `adicCompletionMap` maps the maximal ideal
of `Q.adicCompletionIntegers K` into the maximal ideal of `q.adicCompletionIntegers L`
(`adicCompletionMap_val_lt_one`). -/

/-- The local homomorphism of integer rings induced by `adicCompletionMap`. -/
noncomputable def intCompletionMap {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L]
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
    (hq : q.asIdeal.LiesOver Q.asIdeal) :
    Q.adicCompletionIntegers K →+* q.adicCompletionIntegers L where
  toFun x := ⟨Commons.RingTheory.Henselian.adicCompletionMap Q q hq (x : Q.adicCompletion K),
    Commons.RingTheory.Henselian.adicCompletionMap_mem_integers Q q hq x.2⟩
  map_one' := Subtype.ext (by simp)
  map_mul' x y := Subtype.ext (by simp)
  map_add' x y := Subtype.ext (by simp)
  map_zero' := Subtype.ext (by simp)

lemma intCompletionMap_coe {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L]
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
    (hq : q.asIdeal.LiesOver Q.asIdeal) (x : Q.adicCompletionIntegers K) :
    ((intCompletionMap Q q hq x : q.adicCompletionIntegers L) : q.adicCompletion L) =
      Commons.RingTheory.Henselian.adicCompletionMap Q q hq (x : Q.adicCompletion K) := rfl

/-- `adicCompletionMap` maps the maximal ideal of the integers of `K_Q` into the maximal ideal of
the integers of `L_q`. -/
lemma intCompletionMap_mem_maximalIdeal {K L : Type*} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L]
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
    (hq : q.asIdeal.LiesOver Q.asIdeal) {x : Q.adicCompletionIntegers K}
    (hx : x ∈ IsLocalRing.maximalIdeal (Q.adicCompletionIntegers K)) :
    intCompletionMap Q q hq x ∈ IsLocalRing.maximalIdeal (q.adicCompletionIntegers L) := by
  rw [Commons.NumberTheory.NumberField.adicCompletionIntegers_mem_maximalIdeal_iff_valued_lt_one]
  have hx' := (Commons.NumberTheory.NumberField.adicCompletionIntegers_mem_maximalIdeal_iff_valued_lt_one
    Q x).mp hx
  have h := Commons.RingTheory.Henselian.adicCompletionMap_val_lt_one Q q hq hx'
  rw [show ((intCompletionMap Q q hq x : q.adicCompletionIntegers L) : q.adicCompletion L) =
    Commons.RingTheory.Henselian.adicCompletionMap Q q hq (x : Q.adicCompletion K) from
      intCompletionMap_coe Q q hq x]
  exact h

/-- The natural ring homomorphism `k_Q → k_q` between the residue fields of the two adic
completions. -/
noncomputable def natResidueMap {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L]
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
    (hq : q.asIdeal.LiesOver Q.asIdeal) :
    IsLocalRing.ResidueField (Q.adicCompletionIntegers K) →+*
      IsLocalRing.ResidueField (q.adicCompletionIntegers L) :=
  Ideal.Quotient.lift (IsLocalRing.maximalIdeal (Q.adicCompletionIntegers K))
    ((IsLocalRing.residue (q.adicCompletionIntegers L)).comp (intCompletionMap Q q hq))
    (fun _ ha => by
      rw [RingHom.comp_apply, IsLocalRing.residue_eq_zero_iff]
      exact intCompletionMap_mem_maximalIdeal Q q hq ha)

lemma natResidueMap_residue {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L]
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
    (hq : q.asIdeal.LiesOver Q.asIdeal) (a : Q.adicCompletionIntegers K) :
    natResidueMap Q q hq (IsLocalRing.residue (Q.adicCompletionIntegers K) a) =
      IsLocalRing.residue (q.adicCompletionIntegers L) (intCompletionMap Q q hq a) :=
  Ideal.Quotient.lift_mk _ _ _

lemma natResidueMap_injective {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L]
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
    (hq : q.asIdeal.LiesOver Q.asIdeal) :
    Function.Injective (natResidueMap Q q hq) :=
  RingHom.injective _

/-- **Two ring homomorphisms from a finite field into a field have the same range.**

Let `k` be a finite field and `R` a field.  Then any two ring homomorphisms `k →+* R` have the
same image, namely the unique subfield of `R` with `#k` elements (which may fail to exist, in
which case there are no such homomorphisms at all). -/
theorem ringHom_range_eq_of_finite_field {k R : Type*} [Field k] [Fintype k] [Field R]
    (f g : k →+* R) : f.range = g.range := by
  set q := Fintype.card k with hq
  have hqne : q ≠ 1 := by
    have := Fintype.one_lt_card (α := k); omega
  have hq1 : 1 ≤ q := by
    have := Fintype.card_pos (α := k); omega
  have hp : (X ^ q - X : R[X]) ≠ 0 := by
    intro h
    have hc := congrArg (fun p : R[X] => Polynomial.coeff p q) h
    rw [Polynomial.coeff_sub, Polynomial.coeff_zero, Polynomial.coeff_X_pow_self,
      Polynomial.coeff_X_of_ne_one hqne, sub_zero] at hc
    exact one_ne_zero hc
  have haeval : ∀ x : R, Polynomial.aeval x (X ^ q - X : R[X]) = x ^ q - x := by
    intro x
    simp [Polynomial.aeval_def]
  have hmem : ∀ x : R, x ∈ (X ^ q - X : R[X]).rootSet R ↔ x ^ q = x := by
    intro x
    rw [Polynomial.mem_rootSet, haeval x]
    exact ⟨fun h => sub_eq_zero.mp h.2, fun h => ⟨hp, sub_eq_zero.mpr h⟩⟩
  have hZeq : ({x : R | x ^ q = x} : Set R) = (X ^ q - X : R[X]).rootSet R := by
    ext x; exact (hmem x).symm
  have hZfin : ({x : R | x ^ q = x} : Set R).Finite := by
    rw [hZeq]; exact Polynomial.rootSet_finite _ R
  have hZbound : ({x : R | x ^ q = x} : Set R).ncard ≤ q := by
    rw [hZeq]
    calc ((X ^ q - X : R[X]).rootSet R).ncard
        ≤ (X ^ q - X : R[X]).natDegree := Polynomial.ncard_rootSet_le _ R
      _ ≤ max (X ^ q : R[X]).natDegree (X : R[X]).natDegree := Polynomial.natDegree_sub_le _ _
      _ = q := by simp [Nat.max_eq_left hq1]
  have key : ∀ h : k →+* R, (h.range : Set R) = {x : R | x ^ q = x} := by
    intro h
    have hle : (h.range : Set R) ⊆ {x : R | x ^ q = x} := by
      rintro x ⟨y, rfl⟩
      change (h y) ^ q = h y
      rw [← map_pow, FiniteField.pow_card]
    have hcard : (h.range : Set R).ncard = q := by
      have hinj : Function.Injective h := RingHom.injective h
      have h1 : (h.range : Set R) = h '' Set.univ := by
        ext x; simp
      rw [h1, Set.ncard_image_of_injective _ hinj, Set.ncard_univ, Nat.card_eq_fintype_card]
    exact Set.eq_of_subset_of_ncard_le hle (by rw [hcard]; exact hZbound) hZfin
  refine Subring.ext fun x => ?_
  show x ∈ (f.range : Set R) ↔ x ∈ (g.range : Set R)
  rw [key f, key g]

/-- **The subgroup of ring automorphisms of `R` fixing the image of `φ` pointwise.** -/
def fixSubgroup {S R : Type*} [Semiring S] [Semiring R] (φ : S →+* R) : Subgroup (RingAut R) where
  carrier := {α | ∀ a : S, α (φ a) = φ a}
  mul_mem' := fun {α β} hα hβ a => by
    simp only [Set.mem_ofPred_eq] at hα hβ ⊢
    rw [show (α * β) (φ a) = α (β (φ a)) from rfl, hβ, hα]
  one_mem' := fun a => rfl
  inv_mem' := fun {α} hα a => by
    have h : α⁻¹ (α (φ a)) = α⁻¹ (φ a) := congrArg (fun z => α⁻¹ z) (hα a)
    simpa using h.symm

/-- The subgroup of `RingAut R` fixing `φ`'s image pointwise is the group of `S`-algebra
automorphisms of `R`, for the `S`-algebra structure induced by `φ`. -/
noncomputable def fixSubgroupMulEquiv {S R : Type*} [CommSemiring S] [CommSemiring R]
    (φ : S →+* R) :
    letI : Algebra S R := φ.toAlgebra
    fixSubgroup φ ≃* (R ≃ₐ[S] R) := by
  letI : Algebra S R := φ.toAlgebra
  refine
  { toFun := fun α => AlgEquiv.ofRingEquiv (f := (α : RingAut R)) (fun x => α.2 x)
    invFun := fun β => ⟨(β : R ≃+* R), fun a => β.commutes a⟩
    left_inv := fun α => Subtype.ext rfl
    right_inv := fun β => AlgEquiv.ext fun x => rfl
    map_mul' := fun α β => AlgEquiv.ext fun x => rfl }

/-- **The number of `S`-algebra automorphisms of the residue field of an adic completion is the
inertia degree.**  Here `S` is the residue field of `Q.adicCompletionIntegers K` embedded in the
residue field `R` of `q.adicCompletionIntegers L` by an arbitrary *injective* ring homomorphism
`φ`; the extension `R / S` of finite fields is then Galois with `[R : S] = f(q|Q)`. -/
theorem natCard_algEquiv_residueField_eq_inertiaDeg_of_injective {K L : Type*} [Field K]
    [NumberField K] [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L]
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
    (hq : q.asIdeal.LiesOver Q.asIdeal)
    (φ : IsLocalRing.ResidueField (Q.adicCompletionIntegers K) →+*
        IsLocalRing.ResidueField (q.adicCompletionIntegers L))
    (hφ : Function.Injective φ) :
    (letI := φ.toAlgebra
     Nat.card (IsLocalRing.ResidueField (q.adicCompletionIntegers L) ≃ₐ[
         IsLocalRing.ResidueField (Q.adicCompletionIntegers K)]
       IsLocalRing.ResidueField (q.adicCompletionIntegers L)) =
      q.asIdeal.inertiaDeg (NumberField.RingOfIntegers K)) := by
  letI := φ.toAlgebra
  let ResK := IsLocalRing.ResidueField (Q.adicCompletionIntegers K)
  let ResL := IsLocalRing.ResidueField (q.adicCompletionIntegers L)
  change Nat.card (ResL ≃ₐ[ResK] ResL) = q.asIdeal.inertiaDeg (NumberField.RingOfIntegers K)
  haveI hK : Finite ResK := finite_residueField_adicCompletion K Q
  haveI hL : Finite ResL := finite_residueField_adicCompletion L q
  have hcard : Nat.card (ResL ≃ₐ[ResK] ResL) = Module.finrank ResK ResL :=
    IsGalois.card_aut_eq_finrank (F := ResK) (E := ResL)
  have hpow : Nat.card ResL = Nat.card ResK ^ Module.finrank ResK ResL :=
    Module.natCard_eq_pow_finrank (K := ResK) (V := ResL)
  have hpow' : Nat.card ResL =
      Nat.card ResK ^ q.asIdeal.inertiaDeg (NumberField.RingOfIntegers K) :=
    natCard_residueField_adicCompletion_eq_pow_inertiaDeg K L Q q hq
  have hbase : 2 ≤ Nat.card ResK := Finite.one_lt_card
  have hfin : Module.finrank ResK ResL = q.asIdeal.inertiaDeg (NumberField.RingOfIntegers K) :=
    Nat.pow_right_injective hbase (hpow.symm.trans hpow')
  rw [hcard, hfin]

theorem exists_ringEquiv_adicCompletion_of_residue_ringEquiv {K L : Type*} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
    (hq : q.asIdeal.LiesOver Q.asIdeal)
    (φ : IsLocalRing.ResidueField (Q.adicCompletionIntegers K) →+*
        IsLocalRing.ResidueField (q.adicCompletionIntegers L))
    (hφ : Function.Injective φ)
    (τ : IsLocalRing.ResidueField (q.adicCompletionIntegers L) ≃+*
        IsLocalRing.ResidueField (q.adicCompletionIntegers L))
    (hτ : ∀ a : IsLocalRing.ResidueField (Q.adicCompletionIntegers K), τ (φ a) = φ a) :
    ∃ σ : q.adicCompletion L ≃+* q.adicCompletion L,
      (∀ y : Q.adicCompletion K,
        σ (Commons.RingTheory.Henselian.adicCompletionMap Q q hq y) =
          Commons.RingTheory.Henselian.adicCompletionMap Q q hq y) ∧
      ∀ (x : q.adicCompletionIntegers L)
        (hx : σ (x : q.adicCompletion L) ∈ q.adicCompletionIntegers L),
        τ (IsLocalRing.residue (q.adicCompletionIntegers L) x) =
          IsLocalRing.residue (q.adicCompletionIntegers L) ⟨σ (x : q.adicCompletion L), hx⟩ := by
  classical
  letI : Algebra (Q.adicCompletion K) (q.adicCompletion L) :=
    RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap Q q hq)
  let A := Q.adicCompletionIntegers K
  let B := q.adicCompletionIntegers L
  let KK := Q.adicCompletion K
  let LL := q.adicCompletion L
  let ResK := IsLocalRing.ResidueField A
  let ResL := IsLocalRing.ResidueField B
  haveI hKfin : Finite ResK := finite_residueField_adicCompletion K Q
  haveI hLfin : Finite ResL := finite_residueField_adicCompletion L q
  haveI hKft : Fintype ResK := Fintype.ofFinite ResK
  -- the inertia subgroup of the local Galois group
  obtain ⟨I, hI, hIcard⟩ := exists_inertiaSubgroup_adicCompletion_card_eq_ramificationIdx Q q hq
  -- a `K_Q`-algebra automorphism of `L_q` preserves the ring of integers
  have hpres : ∀ (σ : LL ≃ₐ[KK] LL) (y : LL), σ y ∈ B ↔ y ∈ B :=
    fun σ y => algEquiv_mem_adicCompletionIntegers_iff_adicCompletion Q q hq σ y
  -- hence restricts to a ring automorphism of `B`
  let restr : (LL ≃ₐ[KK] LL) → B ≃+* B := fun σ =>
    { toFun := fun x => ⟨σ (x : LL), (hpres σ (x : LL)).mpr x.2⟩
      invFun := fun y => ⟨σ.symm (y : LL), (hpres σ.symm (y : LL)).mpr y.2⟩
      left_inv := fun x => Subtype.ext (by simp)
      right_inv := fun y => Subtype.ext (by simp)
      map_mul' := fun x y => Subtype.ext (by simp)
      map_add' := fun x y => Subtype.ext (by simp) }
  have restr_coe : ∀ (σ : LL ≃ₐ[KK] LL) (x : B), ((restr σ x : B) : LL) = σ (x : LL) :=
    fun _ _ => rfl
  have restr_sub_coe : ∀ (σ : LL ≃ₐ[KK] LL) (x : B),
      ((restr σ x - x : B) : LL) = σ (x : LL) - (x : LL) := by
    intro σ x
    simp [restr_coe]
  have restr_one : restr 1 = 1 := by
    refine RingEquiv.ext fun x => Subtype.ext ?_
    rw [restr_coe]
    exact AlgEquiv.one_apply (x : LL)
  have restr_mul : ∀ σ σ' : LL ≃ₐ[KK] LL, restr (σ * σ') = restr σ * restr σ' := by
    intro σ σ'
    refine RingEquiv.ext fun x => Subtype.ext ?_
    change ((restr (σ * σ')) x : LL) = ((restr σ) ((restr σ') x) : LL)
    rw [restr_coe, restr_coe, restr_coe, AlgEquiv.mul_apply]
  let restrHom : (LL ≃ₐ[KK] LL) →* RingAut B :=
    { toFun := restr, map_one' := restr_one, map_mul' := restr_mul }
  -- the induced action on the residue field
  let ρ : (LL ≃ₐ[KK] LL) →* RingAut ResL :=
    (IsLocalRing.ResidueField.mapAut : RingAut B →* RingAut ResL).comp restrHom
  have ρ_apply_residue : ∀ (σ : LL ≃ₐ[KK] LL) (x : B),
      ρ σ (IsLocalRing.residue B x) = IsLocalRing.residue B (restr σ x) := by
    intro σ x
    show IsLocalRing.ResidueField.mapAut (restrHom σ) (IsLocalRing.residue B x) =
      IsLocalRing.residue B (restr σ x)
    rw [IsLocalRing.ResidueField.mapAut_apply, IsLocalRing.ResidueField.mapEquiv_apply,
      IsLocalRing.ResidueField.map_residue]
    rfl
  -- the kernel of `ρ` is the inertia subgroup
  have hker : ρ.ker = I := by
    ext σ
    rw [MonoidHom.mem_ker, hI]
    constructor
    · intro h x
      have hx : IsLocalRing.residue B (restr σ x) = IsLocalRing.residue B x := by
        rw [← ρ_apply_residue σ x, h]; rfl
      have hzero : IsLocalRing.residue B (restr σ x - x) = 0 := by
        rw [map_sub, hx, sub_self]
      have hmem : restr σ x - x ∈ IsLocalRing.maximalIdeal B :=
        (IsLocalRing.residue_eq_zero_iff _).mp hzero
      have hval := (Commons.NumberTheory.NumberField.adicCompletionIntegers_mem_maximalIdeal_iff_valued_lt_one
        q (restr σ x - x)).mp hmem
      rwa [restr_sub_coe] at hval
    · intro h
      refine RingEquiv.ext fun r => ?_
      show ρ σ r = r
      obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective r
      rw [ρ_apply_residue σ x]
      have hzero : IsLocalRing.residue B (restr σ x - x) = 0 := by
        rw [map_sub]
        have hmem : restr σ x - x ∈ IsLocalRing.maximalIdeal B := by
          refine (Commons.NumberTheory.NumberField.adicCompletionIntegers_mem_maximalIdeal_iff_valued_lt_one
            q _).mpr ?_
          rw [restr_sub_coe]
          exact h x
        exact (IsLocalRing.residue_eq_zero_iff _).mpr hmem
      have hsub : IsLocalRing.residue B (restr σ x) - IsLocalRing.residue B x = 0 := by
        simpa using hzero
      exact sub_eq_zero.mp hsub
  -- the cardinality of the range of `ρ`
  have hGcard : Nat.card (LL ≃ₐ[KK] LL) =
      q.asIdeal.ramificationIdx (NumberField.RingOfIntegers K) *
        q.asIdeal.inertiaDeg (NumberField.RingOfIntegers K) :=
    natCard_algEquiv_adicCompletion_eq_ramificationIdx_mul_inertiaDeg Q q hq
  have hrange : Nat.card ρ.range = q.asIdeal.inertiaDeg (NumberField.RingOfIntegers K) := by
    have h1 : Nat.card ((LL ≃ₐ[KK] LL) ⧸ ρ.ker) * Nat.card ρ.ker = Nat.card (LL ≃ₐ[KK] LL) := by
      simpa only [Subgroup.index_eq_card] using Subgroup.index_mul_card ρ.ker
    rw [hker, hIcard, hGcard] at h1
    have he : 0 < q.asIdeal.ramificationIdx (NumberField.RingOfIntegers K) :=
      Ideal.ramificationIdx_pos (NumberField.RingOfIntegers K) q.asIdeal
    have h2 : Nat.card ((LL ≃ₐ[KK] LL) ⧸ I) =
        q.asIdeal.inertiaDeg (NumberField.RingOfIntegers K) := by
      rw [mul_comm (q.asIdeal.ramificationIdx (NumberField.RingOfIntegers K))
        (q.asIdeal.inertiaDeg (NumberField.RingOfIntegers K))] at h1
      exact Nat.mul_right_cancel he h1
    have h3 : Nat.card ((LL ≃ₐ[KK] LL) ⧸ ρ.ker) = Nat.card ρ.range :=
      Nat.card_congr (QuotientGroup.quotientKerEquivRange ρ).toEquiv
    rw [← h3, hker, h2]
  -- the natural map of residue fields
  let ψ : ResK →+* ResL := natResidueMap Q q hq
  have hψinj : Function.Injective ψ := natResidueMap_injective Q q hq
  have hcardFix : Nat.card (fixSubgroup ψ) =
      q.asIdeal.inertiaDeg (NumberField.RingOfIntegers K) := by
    have h := natCard_algEquiv_residueField_eq_inertiaDeg_of_injective Q q hq ψ hψinj
    rw [Nat.card_congr (fixSubgroupMulEquiv ψ).toEquiv]
    exact h
  -- the range of `ρ` is exactly the group of automorphisms of `ResL` fixing `ψ`'s image
  have hle : ρ.range ≤ fixSubgroup ψ := by
    rintro α ⟨σ, rfl⟩ a
    obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective a
    rw [natResidueMap_residue, ρ_apply_residue]
    congr 1
    exact Subtype.ext (by rw [restr_coe, intCompletionMap_coe]; exact σ.commutes (x : KK))
  have hfixeq : ρ.range = fixSubgroup ψ := by
    haveI : Finite (RingAut ResL) := by
      haveI : Finite (ResL → ResL) := inferInstance
      exact Finite.of_injective (fun f : RingAut ResL => (f : ResL → ResL))
        (fun f g h => by ext x; exact congrFun h x)
    exact Subgroup.eq_of_le_of_card_ge hle (by rw [hrange, hcardFix])
  -- `τ` fixes the image of `φ`, and `φ` and `ψ` have the same image
  have hfixτ : τ ∈ fixSubgroup ψ := by
    intro a
    have hmem : ψ a ∈ φ.range := by
      rw [← ringHom_range_eq_of_finite_field ψ φ]
      exact ⟨a, rfl⟩
    obtain ⟨b, hb⟩ := hmem
    rw [← hb, hτ b]
  have hτmem : τ ∈ ρ.range := by rw [hfixeq]; exact hfixτ
  obtain ⟨σ, hσ⟩ := MonoidHom.mem_range.mp hτmem
  refine ⟨(σ : LL ≃+* LL), ?_, ?_⟩
  · intro y
    rw [← RingHom.algebraMap_toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap Q q hq)]
    exact σ.commutes y
  · intro x hx
    have h1 : ρ σ (IsLocalRing.residue B x) = IsLocalRing.residue B (restr σ x) :=
      ρ_apply_residue σ x
    have h2 : τ (IsLocalRing.residue B x) = IsLocalRing.residue B (restr σ x) := by
      rw [← hσ]; exact h1
    rw [h2]
    congr 1

end Commons.NumberTheory.NumberField.Completion
