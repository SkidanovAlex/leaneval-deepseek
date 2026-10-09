import Mathlib
import Submission.Commons.NumberTheory.NumberField.Completion.exists_inertiaSubgroup_adicCompletion
import Submission.Commons.NumberTheory.NumberField.Completion.natCard_algEquiv_adicCompletion_eq_ramificationIdx_mul_inertiaDeg
import Submission.Commons.NumberTheory.NumberField.Completion.ringOfIntegers_dense_in_adicIntegers
import Submission.Commons.NumberTheory.NumberField.adicCompletion_residueField_equiv_exists
import Submission.Commons.NumberTheory.NumberField.perfectField_residueField_heightOneSpectrum
import Submission.Commons.NumberTheory.NumberField.finite_quotient_heightOneSpectrum
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open scoped NumberField Pointwise
set_option autoImplicit false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1600000

namespace Commons.NumberTheory.NumberField.Completion

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]

/-! ## Preliminaries: the action of the decomposition group on the residue field -/

/-- **The decomposition group acts on the ring of integers of `𝓞 L` correctly.**

For `σ` in the decomposition group of the place `q` and `r : 𝓞 L`, the extension of `σ` to the
`q`-adic completion `L_q` sends the image of `r` to the image of `σ • r`. -/
theorem decompositionToAdicCompletion_algebraMap_ringOfIntegers
    (q : IsDedekindDomain.HeightOneSpectrum (𝓞 L)) (σ : decompositionSubgroup (K := K) q)
    (r : 𝓞 L) :
    decompositionToAdicCompletion (K := K) q σ
        ((algebraMap (𝓞 L) (q.adicCompletionIntegers L) r : q.adicCompletionIntegers L) :
          q.adicCompletion L) =
      ((algebraMap (𝓞 L) (q.adicCompletionIntegers L)
          (galRestrict (𝓞 K) K L (𝓞 L) σ.1 r) : q.adicCompletionIntegers L) :
        q.adicCompletion L) := by
  rw [show ((algebraMap (𝓞 L) (q.adicCompletionIntegers L) r : q.adicCompletionIntegers L) :
      q.adicCompletion L) = ((algebraMap (𝓞 L) L r : L) : q.adicCompletion L) from rfl]
  rw [decompositionToAdicCompletion_coe]
  rw [show ((algebraMap (𝓞 L) (q.adicCompletionIntegers L)
        (galRestrict (𝓞 K) K L (𝓞 L) σ.1 r) : q.adicCompletionIntegers L) :
      q.adicCompletion L) = ((algebraMap (𝓞 L) L
        (galRestrict (𝓞 K) K L (𝓞 L) σ.1 r) : L) : q.adicCompletion L) from rfl]
  rw [← algebraMap_galRestrict_apply (𝓞 K) σ.1 r]

/-- The residue field of the ring of integers of the `q`-adic completion is the residue field
`𝓞 L / q`; explicitly, an element `r : 𝓞 L` maps into the maximal ideal of the completion's
ring of integers exactly when `r ∈ q`. -/
theorem algebraMap_ringOfIntegers_mem_maximalIdeal_iff
    (q : IsDedekindDomain.HeightOneSpectrum (𝓞 L)) (r : 𝓞 L) :
    algebraMap (𝓞 L) (q.adicCompletionIntegers L) r ∈
        IsLocalRing.maximalIdeal (q.adicCompletionIntegers L) ↔ r ∈ q.asIdeal := by
  have hker := Commons.NumberTheory.NumberField.quotientMap_ker_eq_asIdeal (K := L) q
  rw [← hker, RingHom.mem_ker, RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem]

/-- **The decomposition group preserves the ring of integers of the completion.**

Every element of the decomposition group of `q`, acting on the `q`-adic completion `L_q`,
preserves the ring of integers `q.adicCompletionIntegers L`. -/
theorem decompositionToAdicCompletion_mem_adicCompletionIntegers
    (q : IsDedekindDomain.HeightOneSpectrum (𝓞 L)) (σ : decompositionSubgroup (K := K) q)
    (x : q.adicCompletionIntegers L) :
    decompositionToAdicCompletion (K := K) q σ (x : q.adicCompletion L) ∈
      q.adicCompletionIntegers L := by
  have hOclosed : IsClosed ((q.adicCompletionIntegers L : Set (q.adicCompletion L))) :=
    Valued.isClosed_valuationSubring (q.adicCompletion L)
      (Γ₀ := WithZero (Multiplicative ℤ))
  have hset : {y : q.adicCompletion L | ∃ r : 𝓞 L,
        algebraMap L (q.adicCompletion L) (r : L) = y} =
      Set.range (fun r : 𝓞 L =>
        (algebraMap (𝓞 L) (q.adicCompletionIntegers L) r : q.adicCompletion L)) := by
    ext y
    constructor
    · rintro ⟨r, rfl⟩
      exact ⟨r, rfl⟩
    · rintro ⟨r, rfl⟩
      exact ⟨r, rfl⟩
  have hxmem : (x : q.adicCompletion L) ∈ closure (Set.range (fun r : 𝓞 L =>
      (algebraMap (𝓞 L) (q.adicCompletionIntegers L) r : q.adicCompletion L))) := by
    have h := ringOfIntegers_dense_in_adicIntegers L q x
    rwa [hset] at h
  have hSsub : Set.range (fun r : 𝓞 L =>
      (algebraMap (𝓞 L) (q.adicCompletionIntegers L) r : q.adicCompletion L)) ⊆
      (q.adicCompletionIntegers L : Set (q.adicCompletion L)) := by
    rintro y ⟨r, rfl⟩
    exact (algebraMap (𝓞 L) (q.adicCompletionIntegers L) r).2
  have himagecl : decompositionToAdicCompletion (K := K) q σ ''
      closure (Set.range (fun r : 𝓞 L =>
        (algebraMap (𝓞 L) (q.adicCompletionIntegers L) r : q.adicCompletion L))) ⊆
      closure (decompositionToAdicCompletion (K := K) q σ ''
        Set.range (fun r : 𝓞 L =>
          (algebraMap (𝓞 L) (q.adicCompletionIntegers L) r : q.adicCompletion L))) :=
    image_closure_subset_closure_image (continuous_decompositionToAdicCompletion (K := K) q σ)
  have hmem : decompositionToAdicCompletion (K := K) q σ (x : q.adicCompletion L) ∈
      decompositionToAdicCompletion (K := K) q σ ''
      closure (Set.range (fun r : 𝓞 L =>
        (algebraMap (𝓞 L) (q.adicCompletionIntegers L) r : q.adicCompletion L))) :=
    ⟨(x : q.adicCompletion L), hxmem, rfl⟩
  have h2 := himagecl hmem
  have h3 : closure (decompositionToAdicCompletion (K := K) q σ ''
        Set.range (fun r : 𝓞 L =>
          (algebraMap (𝓞 L) (q.adicCompletionIntegers L) r : q.adicCompletion L))) ⊆
      (q.adicCompletionIntegers L : Set (q.adicCompletion L)) := by
    apply closure_minimal _ hOclosed
    rintro y ⟨z, ⟨r, rfl⟩, rfl⟩
    rw [decompositionToAdicCompletion_algebraMap_ringOfIntegers (K := K) q σ r]
    exact (algebraMap (𝓞 L) (q.adicCompletionIntegers L)
      (galRestrict (𝓞 K) K L (𝓞 L) σ.1 r)).2
  exact h3 h2

/-- The image of a unit under a ring equivalence is a unit. (Helper for the next lemma.) -/
private theorem isUnit_ringEquiv_iff {R S : Type*} [CommSemiring R] [CommSemiring S]
    (e : R ≃+* S) (x : R) : IsUnit (e x) ↔ IsUnit x := by
  constructor
  · intro h
    have h2 := IsUnit.map (e.symm : S →+* R) h
    simpa using h2
  · intro h
    exact IsUnit.map (e : R →+* S) h

/-- **The inverse of the action of the decomposition group on the completion.** -/
theorem decompositionToAdicCompletion_inv (q : IsDedekindDomain.HeightOneSpectrum (𝓞 L))
    (σ : decompositionSubgroup (K := K) q) :
    (decompositionToAdicCompletion (K := K) q σ)⁻¹ =
      decompositionToAdicCompletion (K := K) q σ⁻¹ := by
  have h : decompositionToAdicCompletion (K := K) q σ *
      decompositionToAdicCompletion (K := K) q σ⁻¹ = 1 := by
    rw [← map_mul, mul_inv_cancel, map_one]
  exact eq_inv_of_mul_eq_one_right h

/-- **The action of the decomposition group on the ring of integers of the completion.**

Every element of the decomposition group of `q`, acting on the `q`-adic completion `L_q`,
restricts to a ring automorphism of `q.adicCompletionIntegers L`. -/
noncomputable def decompositionToAdicCompletionIntegersRingEquiv
    (q : IsDedekindDomain.HeightOneSpectrum (𝓞 L)) (σ : decompositionSubgroup (K := K) q) :
    q.adicCompletionIntegers L ≃+* q.adicCompletionIntegers L where
  toFun x := ⟨decompositionToAdicCompletion (K := K) q σ (x : q.adicCompletion L),
    decompositionToAdicCompletion_mem_adicCompletionIntegers (K := K) q σ x⟩
  invFun y := ⟨(decompositionToAdicCompletion (K := K) q σ)⁻¹ (y : q.adicCompletion L), by
    rw [decompositionToAdicCompletion_inv]
    exact decompositionToAdicCompletion_mem_adicCompletionIntegers (K := K) q σ⁻¹ y⟩
  left_inv x := Subtype.ext (by simp)
  right_inv y := Subtype.ext (by simp)
  map_mul' x y := Subtype.ext (by simp)
  map_add' x y := Subtype.ext (by simp)

@[simp]
theorem decompositionToAdicCompletionIntegersRingEquiv_apply
    (q : IsDedekindDomain.HeightOneSpectrum (𝓞 L)) (σ : decompositionSubgroup (K := K) q)
    (x : q.adicCompletionIntegers L) :
    ((decompositionToAdicCompletionIntegersRingEquiv (K := K) q σ x :
        q.adicCompletionIntegers L) : q.adicCompletion L) =
      decompositionToAdicCompletion (K := K) q σ (x : q.adicCompletion L) := rfl

/-- **The decomposition group preserves the maximal ideal of the ring of integers.** -/
theorem decompositionToAdicCompletion_mem_maximalIdeal
    (q : IsDedekindDomain.HeightOneSpectrum (𝓞 L)) (σ : decompositionSubgroup (K := K) q)
    {y : q.adicCompletionIntegers L}
    (hy : y ∈ IsLocalRing.maximalIdeal (q.adicCompletionIntegers L)) :
    decompositionToAdicCompletionIntegersRingEquiv (K := K) q σ y ∈
      IsLocalRing.maximalIdeal (q.adicCompletionIntegers L) := by
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hy ⊢
  intro h
  exact hy ((isUnit_ringEquiv_iff _ _).mp h)

/-- The action of the decomposition group on an element of the ring of integers coming from
`𝓞 L` is again of that form. -/
theorem decompositionToAdicCompletionIntegersRingEquiv_algebraMap
    (q : IsDedekindDomain.HeightOneSpectrum (𝓞 L)) (δ : decompositionSubgroup (K := K) q)
    (r : 𝓞 L) :
    decompositionToAdicCompletionIntegersRingEquiv (K := K) q δ
        (algebraMap (𝓞 L) (q.adicCompletionIntegers L) r) =
      algebraMap (𝓞 L) (q.adicCompletionIntegers L)
        (galRestrict (𝓞 K) K L (𝓞 L) δ.1 r) := by
  apply Subtype.ext
  show decompositionToAdicCompletion (K := K) q δ
      ((algebraMap (𝓞 L) (q.adicCompletionIntegers L) r : q.adicCompletionIntegers L) :
        q.adicCompletion L) =
    ((algebraMap (𝓞 L) (q.adicCompletionIntegers L)
      (galRestrict (𝓞 K) K L (𝓞 L) δ.1 r) : q.adicCompletionIntegers L) :
        q.adicCompletion L)
  exact decompositionToAdicCompletion_algebraMap_ringOfIntegers (K := K) q δ r

/-- **The local inertia subgroup of the decomposition group.**

For `δ` in the decomposition group of the place `q` of `L` over `K`, the extension of `δ` to the
`q`-adic completion `L_q` acts trivially on the residue field of `L_q` — i.e. moves every element
of the ring of integers `q.adicCompletionIntegers L` by an element of valuation `< 1` — if and
only if `δ` acts trivially on the residue field `𝓞 L ⧸ q` of the place of `L`. -/
theorem decompositionToAdicCompletion_residueTrivial_iff_mem_inertia
    (q : IsDedekindDomain.HeightOneSpectrum (𝓞 L)) (δ : decompositionSubgroup (K := K) q) :
    letI : MulSemiringAction Gal(L/K) (𝓞 L) :=
      IsIntegralClosure.MulSemiringAction (𝓞 K) K L (𝓞 L)
    ((∀ x : q.adicCompletionIntegers L,
        Valued.v (R := q.adicCompletion L) (Γ₀ := WithZero (Multiplicative ℤ))
          (decompositionToAdicCompletion (K := K) q δ (x : q.adicCompletion L) -
            (x : q.adicCompletion L)) < 1) ↔
      δ.1 ∈ q.asIdeal.inertia Gal(L/K)) := by
  letI : MulSemiringAction Gal(L/K) (𝓞 L) :=
    IsIntegralClosure.MulSemiringAction (𝓞 K) K L (𝓞 L)
  have hmem_iff : δ.1 ∈ q.asIdeal.inertia Gal(L/K) ↔
      ∀ r : 𝓞 L, galRestrict (𝓞 K) K L (𝓞 L) δ.1 r - r ∈ q.asIdeal := by
    rw [Ideal.inertia, AddSubgroup.mem_inertia]
    constructor
    · intro h r
      have h' := h r
      rw [show (δ.1 • r - r : 𝓞 L) =
        galRestrict (𝓞 K) K L (𝓞 L) δ.1 r - r from rfl] at h'
      exact (Submodule.mem_toAddSubgroup _).mp h'
    · intro h r
      have h' := h r
      rw [show (δ.1 • r - r : 𝓞 L) =
        galRestrict (𝓞 K) K L (𝓞 L) δ.1 r - r from rfl]
      exact (Submodule.mem_toAddSubgroup _).mpr h'
  -- the action on the image of `𝓞 L` differs from the identity by the image of `δ • r - r`
  have hkey : ∀ r : 𝓞 L,
      decompositionToAdicCompletionIntegersRingEquiv (K := K) q δ
          (algebraMap (𝓞 L) (q.adicCompletionIntegers L) r) -
        algebraMap (𝓞 L) (q.adicCompletionIntegers L) r =
      algebraMap (𝓞 L) (q.adicCompletionIntegers L)
        (galRestrict (𝓞 K) K L (𝓞 L) δ.1 r - r) := by
    intro r
    rw [decompositionToAdicCompletionIntegersRingEquiv_algebraMap (K := K) q δ r]
    rw [show ((algebraMap (𝓞 L) (q.adicCompletionIntegers L)
        (galRestrict (𝓞 K) K L (𝓞 L) δ.1 r) : q.adicCompletionIntegers L) :
        q.adicCompletionIntegers L) -
        algebraMap (𝓞 L) (q.adicCompletionIntegers L) r =
      algebraMap (𝓞 L) (q.adicCompletionIntegers L) (galRestrict (𝓞 K) K L (𝓞 L) δ.1 r) -
        algebraMap (𝓞 L) (q.adicCompletionIntegers L) r from rfl]
    rw [← map_sub]
  constructor
  · -- residue-triviality implies triviality on `𝓞 L ⧸ q`
    intro hres
    rw [hmem_iff]
    intro r
    let A : q.adicCompletionIntegers L := algebraMap (𝓞 L) (q.adicCompletionIntegers L) r
    have hmem : decompositionToAdicCompletion (K := K) q δ (A : q.adicCompletion L) -
        (A : q.adicCompletion L) ∈ q.adicCompletionIntegers L :=
      sub_mem (decompositionToAdicCompletion_mem_adicCompletionIntegers (K := K) q δ A) A.2
    have hmemA : (⟨decompositionToAdicCompletion (K := K) q δ (A : q.adicCompletion L) -
        (A : q.adicCompletion L), hmem⟩ : q.adicCompletionIntegers L) ∈
        IsLocalRing.maximalIdeal (q.adicCompletionIntegers L) :=
      (adicCompletionIntegers_mem_maximalIdeal_iff_valued_lt_one q _).mpr (hres A)
    have heq : (⟨decompositionToAdicCompletion (K := K) q δ (A : q.adicCompletion L) -
          (A : q.adicCompletion L), hmem⟩ : q.adicCompletionIntegers L) =
        algebraMap (𝓞 L) (q.adicCompletionIntegers L)
          (galRestrict (𝓞 K) K L (𝓞 L) δ.1 r - r) :=
      hkey r
    rw [heq] at hmemA
    exact (algebraMap_ringOfIntegers_mem_maximalIdeal_iff q _).mp hmemA
  · -- triviality on `𝓞 L ⧸ q` implies residue-triviality
    intro hin x
    rw [hmem_iff] at hin
    obtain ⟨r, hr⟩ := Commons.NumberTheory.NumberField.exists_sub_ringOfIntegers_mem_maximalIdeal q x
    let A : q.adicCompletionIntegers L := algebraMap (𝓞 L) (q.adicCompletionIntegers L) r
    have h1 : decompositionToAdicCompletionIntegersRingEquiv (K := K) q δ
        (x - A) ∈ IsLocalRing.maximalIdeal (q.adicCompletionIntegers L) :=
      decompositionToAdicCompletion_mem_maximalIdeal (K := K) q δ hr
    have h2 : decompositionToAdicCompletionIntegersRingEquiv (K := K) q δ A - A ∈
        IsLocalRing.maximalIdeal (q.adicCompletionIntegers L) := by
      have h2' : decompositionToAdicCompletionIntegersRingEquiv (K := K) q δ A - A =
          algebraMap (𝓞 L) (q.adicCompletionIntegers L)
            (galRestrict (𝓞 K) K L (𝓞 L) δ.1 r - r) := hkey r
      rw [h2']
      exact (algebraMap_ringOfIntegers_mem_maximalIdeal_iff q _).mpr (hin r)
    have h3 : A - x ∈ IsLocalRing.maximalIdeal (q.adicCompletionIntegers L) := by
      have h3' : A - x = -(x - A) := by ring
      rw [h3']
      exact neg_mem hr
    have hsum : decompositionToAdicCompletionIntegersRingEquiv (K := K) q δ x - x ∈
        IsLocalRing.maximalIdeal (q.adicCompletionIntegers L) := by
      have e : decompositionToAdicCompletionIntegersRingEquiv (K := K) q δ x - x =
          (decompositionToAdicCompletionIntegersRingEquiv (K := K) q δ (x - A) +
            (decompositionToAdicCompletionIntegersRingEquiv (K := K) q δ A - A)) +
          (A - x) := by
        rw [map_sub]
        abel
      rw [e]
      exact add_mem (add_mem h1 h2) h3
    have := (adicCompletionIntegers_mem_maximalIdeal_iff_valued_lt_one q
      (decompositionToAdicCompletionIntegersRingEquiv (K := K) q δ x - x)).mp hsum
    simpa using this


/-- The identification of the decomposition group with the local Galois group, evaluated on
elements of the completion. -/
theorem decompositionSubgroupMulEquivLocalGalois_apply_coe
    (Q : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (q : IsDedekindDomain.HeightOneSpectrum (𝓞 L)) (hq : q.asIdeal.LiesOver Q.asIdeal)
    (δ : decompositionSubgroup (K := K) q) (x : q.adicCompletion L) :
    letI : Algebra (Q.adicCompletion K) (q.adicCompletion L) :=
      RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap Q q hq)
    decompositionSubgroupMulEquivLocalGalois Q q hq δ x =
      decompositionToAdicCompletion (K := K) q δ x := by
  letI : Algebra (Q.adicCompletion K) (q.adicCompletion L) :=
    RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap Q q hq)
  simp only [decompositionSubgroupMulEquivLocalGalois, MulEquiv.ofBijective_apply,
    decompositionToLocalGalois, MonoidHom.coe_mk, OneHom.coe_mk]
  exact congrFun (decompositionToLocalGaloisFun_apply Q q hq δ) x

/-- The identification of the decomposition group with the local Galois group, as an equality of
functions on the completion. -/
theorem decompositionSubgroupMulEquivLocalGalois_coe_adicCompletion
    (Q : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (q : IsDedekindDomain.HeightOneSpectrum (𝓞 L)) (hq : q.asIdeal.LiesOver Q.asIdeal)
    (δ : decompositionSubgroup (K := K) q) :
    letI : Algebra (Q.adicCompletion K) (q.adicCompletion L) :=
      RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap Q q hq)
    (⇑(decompositionSubgroupMulEquivLocalGalois Q q hq δ) :
        q.adicCompletion L → q.adicCompletion L) =
      ⇑(decompositionToAdicCompletion (K := K) q δ) := by
  letI : Algebra (Q.adicCompletion K) (q.adicCompletion L) :=
    RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap Q q hq)
  funext x
  exact decompositionSubgroupMulEquivLocalGalois_apply_coe (K := K) Q q hq δ x

/-- The identification of the decomposition group with the local Galois group, in the form used
for the membership computation of the inertia subgroup. -/
theorem decompositionSubgroupMulEquivLocalGalois_toMonoidHom_apply
    (Q : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (q : IsDedekindDomain.HeightOneSpectrum (𝓞 L)) (hq : q.asIdeal.LiesOver Q.asIdeal)
    (δ : decompositionSubgroup (K := K) q) (x : q.adicCompletion L) :
    letI : Algebra (Q.adicCompletion K) (q.adicCompletion L) :=
      RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap Q q hq)
    (decompositionSubgroupMulEquivLocalGalois Q q hq).toMonoidHom δ x =
      decompositionToAdicCompletion (K := K) q δ x := by
  letI : Algebra (Q.adicCompletion K) (q.adicCompletion L) :=
    RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap Q q hq)
  exact congrFun (decompositionSubgroupMulEquivLocalGalois_coe_adicCompletion (K := K) Q q hq δ) x

set_option backward.isDefEq.respectTransparency false in
/-- **The inertia subgroup of the local Galois group has order the ramification index.**

Let `L / K` be a finite Galois extension of number fields, `Q` a height one prime of `𝓞 K` and
`q` a height one prime of `𝓞 L` lying over `Q`.  Then the inertia subgroup of the local Galois
group `Gal(L_q / K_Q)` — the group of `K_Q`-algebra automorphisms of `L_q` acting trivially on
the residue field — has order the ramification index `e(q|Q)`.  This is Neukirch–Schmidt–Wingberg,
*Cohomology of Number Fields*, Theorem 12.2.1. -/
theorem exists_inertiaSubgroup_adicCompletion_card_eq_ramificationIdx {K L : Type*} [Field K]
    [NumberField K] [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
    (hq : q.asIdeal.LiesOver Q.asIdeal) :
    letI : Algebra (Q.adicCompletion K) (q.adicCompletion L) :=
      RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap Q q hq)
    ∃ I : Subgroup (q.adicCompletion L ≃ₐ[Q.adicCompletion K] q.adicCompletion L),
      (∀ σ : q.adicCompletion L ≃ₐ[Q.adicCompletion K] q.adicCompletion L,
        σ ∈ I ↔ ∀ x : q.adicCompletionIntegers L,
          Valued.v (R := q.adicCompletion L) (Γ₀ := WithZero (Multiplicative ℤ))
            (σ (x : q.adicCompletion L) - (x : q.adicCompletion L)) < 1) ∧
      Nat.card I = q.asIdeal.ramificationIdx (NumberField.RingOfIntegers K) := by
  letI : Algebra (Q.adicCompletion K) (q.adicCompletion L) :=
    RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap Q q hq)
  letI : MulSemiringAction Gal(L/K) (𝓞 L) :=
    IsIntegralClosure.MulSemiringAction (𝓞 K) K L (𝓞 L)
  haveI hGal : IsGaloisGroup Gal(L/K) (𝓞 K) (𝓞 L) :=
    IsGaloisGroup.of_isFractionRing Gal(L/K) (𝓞 K) (𝓞 L) K L
  haveI hperfect : PerfectField Q.asIdeal.ResidueField :=
    Commons.NumberTheory.NumberField.perfectField_residueField_heightOneSpectrum Q
  haveI hlies : q.asIdeal.LiesOver Q.asIdeal := hq
  have hstab : decompositionSubgroup (K := K) q =
      MulAction.stabilizer Gal(L/K) q.asIdeal := by
    ext σ
    rw [mem_decompositionSubgroup_iff_smul, MulAction.mem_stabilizer_iff]
  have hle : q.asIdeal.inertia Gal(L/K) ≤ decompositionSubgroup (K := K) q := by
    rw [hstab]
    exact Ideal.inertia_le_stabilizer q.asIdeal
  refine ⟨((q.asIdeal.inertia Gal(L/K)).subgroupOf (decompositionSubgroup (K := K) q)).map
      (decompositionSubgroupMulEquivLocalGalois Q q hq).toMonoidHom, ?_, ?_⟩
  · intro σ
    rw [Subgroup.mem_map]
    constructor
    · rintro ⟨δ, hδ, rfl⟩
      have hδ' : δ.1 ∈ q.asIdeal.inertia Gal(L/K) := (Subgroup.mem_subgroupOf).mp hδ
      have h := (decompositionToAdicCompletion_residueTrivial_iff_mem_inertia (K := K) q δ).mpr hδ'
      intro x
      rw [decompositionSubgroupMulEquivLocalGalois_toMonoidHom_apply (K := K) Q q hq δ x]
      exact h x
    · intro hσ
      refine ⟨(decompositionSubgroupMulEquivLocalGalois Q q hq).symm σ, ?_, ?_⟩
      · rw [Subgroup.mem_subgroupOf]
        refine (decompositionToAdicCompletion_residueTrivial_iff_mem_inertia (K := K) q
          ((decompositionSubgroupMulEquivLocalGalois Q q hq).symm σ)).mp ?_
        intro x
        have hf : (⇑(decompositionToAdicCompletion (K := K) q
              ((decompositionSubgroupMulEquivLocalGalois Q q hq).symm σ)) :
                q.adicCompletion L → q.adicCompletion L) =
            ⇑((decompositionSubgroupMulEquivLocalGalois Q q hq)
              ((decompositionSubgroupMulEquivLocalGalois Q q hq).symm σ)) :=
          (decompositionSubgroupMulEquivLocalGalois_coe_adicCompletion (K := K) Q q hq _).symm
        rw [congrFun hf x, MulEquiv.apply_symm_apply]
        exact hσ x
      · exact MulEquiv.apply_symm_apply _ σ
  · have h1 : Nat.card ((q.asIdeal.inertia Gal(L/K)).subgroupOf
          (decompositionSubgroup (K := K) q)) =
        Nat.card (((q.asIdeal.inertia Gal(L/K)).subgroupOf
          (decompositionSubgroup (K := K) q)).map
        (decompositionSubgroupMulEquivLocalGalois Q q hq).toMonoidHom) :=
      Nat.card_congr (Subgroup.equivMapOfInjective _
        (decompositionSubgroupMulEquivLocalGalois Q q hq).toMonoidHom
        (decompositionSubgroupMulEquivLocalGalois Q q hq).injective).toEquiv
    have h2 : Nat.card ((q.asIdeal.inertia Gal(L/K)).subgroupOf
        (decompositionSubgroup (K := K) q)) = Nat.card (q.asIdeal.inertia Gal(L/K)) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv
    rw [← h1, h2]
    rw [Ideal.card_inertia_eq_ramificationIdxIn (G := Gal(L/K)) Q.asIdeal q.asIdeal,
      Ideal.ramificationIdxIn_eq_ramificationIdx Q.asIdeal q.asIdeal Gal(L/K)]
