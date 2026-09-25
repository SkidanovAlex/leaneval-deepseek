import Mathlib
import Submission.Commons.NumberTheory.NumberField.Completion.exists_inertiaSubgroup_adicCompletion_card_eq_ramificationIdx
import Submission.Commons.NumberTheory.NumberField.Completion.natCard_algEquiv_adicCompletion_eq_ramificationIdx_mul_inertiaDeg
import Submission.Commons.NumberTheory.NumberField.Completion.isIntegralClosure_adicCompletionIntegers_extension
import Submission.Commons.NumberTheory.NumberField.adicCompletion_residueField_equiv_exists

open scoped NumberField
set_option autoImplicit false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1600000

namespace Commons.NumberTheory.NumberField.Completion

/-- A ring equivalence preserves the property of being a unit. -/
private lemma isUnit_ringEquiv_iff_aux {R S : Type*} [CommSemiring R] [CommSemiring S]
    (e : R ≃+* S) (x : R) : IsUnit (e x) ↔ IsUnit x := by
  constructor
  · intro h
    have h2 := IsUnit.map (e.symm : S →+* R) h
    simpa using h2
  · intro h
    exact IsUnit.map (e : R →+* S) h

/-- **Every `K_Q`-algebra automorphism of `L_q` preserves the ring of integers.**

Let `L / K` be a finite Galois extension of number fields, `Q` a height one prime of `𝓞 K` and
`q` a height one prime of `𝓞 L` lying over `Q`.  Then the ring of integers
`q.adicCompletionIntegers L` of the `q`-adic completion is the integral closure of
`Q.adicCompletionIntegers K`, and every `K_Q`-algebra automorphism of `L_q` fixes `K_Q` and hence
permutes the integral elements. -/
theorem algEquiv_mem_adicCompletionIntegers_iff_adicCompletion {K L : Type*} [Field K]
    [NumberField K] [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L]
    [IsGalois K L]
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
    (hq : q.asIdeal.LiesOver Q.asIdeal) :
    letI : Algebra (Q.adicCompletion K) (q.adicCompletion L) :=
      RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap Q q hq)
    ∀ (σ : q.adicCompletion L ≃ₐ[Q.adicCompletion K] q.adicCompletion L)
      (x : q.adicCompletion L),
      σ x ∈ q.adicCompletionIntegers L ↔ x ∈ q.adicCompletionIntegers L := by
  letI : Algebra (Q.adicCompletion K) (q.adicCompletion L) :=
    RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap Q q hq)
  letI : Algebra (Q.adicCompletionIntegers K) (q.adicCompletion L) :=
    RingHom.toAlgebra ((Commons.RingTheory.Henselian.adicCompletionMap Q q hq).comp
      (Q.adicCompletionIntegers K).subtype)
  haveI hic : IsIntegralClosure (q.adicCompletionIntegers L) (Q.adicCompletionIntegers K)
      (q.adicCompletion L) := isIntegralClosure_adicCompletionIntegers_extension Q q hq
  have hIntiff : ∀ x : q.adicCompletion L,
      IsIntegral (Q.adicCompletionIntegers K) x ↔ x ∈ q.adicCompletionIntegers L := by
    intro x
    rw [IsIntegralClosure.isIntegral_iff (A := q.adicCompletionIntegers L)
      (R := Q.adicCompletionIntegers K) (B := q.adicCompletion L)]
    constructor
    · rintro ⟨y, rfl⟩; exact y.2
    · intro hx; exact ⟨⟨x, hx⟩, rfl⟩
  have hkey : ∀ (τ : q.adicCompletion L ≃ₐ[Q.adicCompletion K] q.adicCompletion L),
      ∀ y, IsIntegral (Q.adicCompletionIntegers K) y →
        IsIntegral (Q.adicCompletionIntegers K) (τ y) := by
    intro τ y hy
    have hφ : ∀ a : Q.adicCompletionIntegers K,
        τ ((algebraMap (Q.adicCompletionIntegers K) (q.adicCompletion L)) a) =
          (algebraMap (Q.adicCompletionIntegers K) (q.adicCompletion L)) a := by
      intro a
      change τ ((Commons.RingTheory.Henselian.adicCompletionMap Q q hq)
          (a : Q.adicCompletion K)) =
        (Commons.RingTheory.Henselian.adicCompletionMap Q q hq) (a : Q.adicCompletion K)
      exact τ.commutes (a : Q.adicCompletion K)
    let τAlg : q.adicCompletion L →ₐ[Q.adicCompletionIntegers K] q.adicCompletion L :=
      { toRingHom := (τ : q.adicCompletion L →+* q.adicCompletion L)
        commutes' := hφ }
    exact IsIntegral.map τAlg hy
  intro σ x
  constructor
  · intro hx
    have h1 : IsIntegral (Q.adicCompletionIntegers K) (σ x) := (hIntiff (σ x)).mpr hx
    have h2 : IsIntegral (Q.adicCompletionIntegers K) (σ⁻¹ (σ x)) := hkey σ⁻¹ (σ x) h1
    have h2' : IsIntegral (Q.adicCompletionIntegers K) x := by simpa using h2
    exact (hIntiff x).mp h2'
  · intro hx
    exact (hIntiff (σ x)).mp (hkey σ x ((hIntiff x).mpr hx))

/-- **The inertia subgroup of the local Galois group is normal, with quotient of order the
inertia degree.**

Let `L / K` be a finite Galois extension of number fields, `Q` a height one prime of `𝓞 K` and
`q` a height one prime of `𝓞 L` lying over `Q`.  Then the local Galois group
`Gal(L_q / K_Q)` of the extension of completions contains the inertia subgroup `I` consisting of
the automorphisms acting trivially on the residue field; `I` is normal in `Gal(L_q / K_Q)` and the
quotient has order the inertia degree `f(q|Q)`.  This is Neukirch–Schmidt–Wingberg, *Cohomology of
Number Fields*, Theorem 12.2.1. -/
theorem exists_inertiaSubgroup_adicCompletion_isNormal_card_quotient {K L : Type*} [Field K]
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
      I.Normal ∧
      Nat.card ((q.adicCompletion L ≃ₐ[Q.adicCompletion K] q.adicCompletion L) ⧸ I) =
        q.asIdeal.inertiaDeg (NumberField.RingOfIntegers K) := by
  letI : Algebra (Q.adicCompletion K) (q.adicCompletion L) :=
    RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap Q q hq)
  have hpres : ∀ (τ : q.adicCompletion L ≃ₐ[Q.adicCompletion K] q.adicCompletion L)
      (y : q.adicCompletion L),
      τ y ∈ q.adicCompletionIntegers L ↔ y ∈ q.adicCompletionIntegers L :=
    algEquiv_mem_adicCompletionIntegers_iff_adicCompletion Q q hq
  have hring : ∀ τ : q.adicCompletion L ≃ₐ[Q.adicCompletion K] q.adicCompletion L,
      ∃ e : q.adicCompletionIntegers L ≃+* q.adicCompletionIntegers L,
        ∀ x : q.adicCompletionIntegers L,
          (e x : q.adicCompletion L) = τ (x : q.adicCompletion L) := by
    intro τ
    let e : q.adicCompletionIntegers L ≃+* q.adicCompletionIntegers L :=
      { toFun := fun x => ⟨τ (x : q.adicCompletion L),
            (hpres τ (x : q.adicCompletion L)).mpr x.2⟩
        invFun := fun y => ⟨τ⁻¹ (y : q.adicCompletion L),
            (hpres τ⁻¹ (y : q.adicCompletion L)).mpr y.2⟩
        left_inv := fun x => Subtype.ext (by simp)
        right_inv := fun y => Subtype.ext (by simp)
        map_mul' := fun x y => Subtype.ext (by simp)
        map_add' := fun x y => Subtype.ext (by simp) }
    exact ⟨e, fun x => rfl⟩
  have hm_pres : ∀ (τ : q.adicCompletion L ≃ₐ[Q.adicCompletion K] q.adicCompletion L)
      (u : q.adicCompletionIntegers L),
      u ∈ IsLocalRing.maximalIdeal (q.adicCompletionIntegers L) →
      (⟨τ (u : q.adicCompletion L),
        (hpres τ (u : q.adicCompletion L)).mpr u.2⟩ :
          q.adicCompletionIntegers L) ∈
        IsLocalRing.maximalIdeal (q.adicCompletionIntegers L) := by
    intro τ u hu
    obtain ⟨e, he⟩ := hring τ
    have hum : e u ∈ IsLocalRing.maximalIdeal (q.adicCompletionIntegers L) := by
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hu ⊢
      intro h
      exact hu ((isUnit_ringEquiv_iff_aux e u).mp h)
    have hEq : e u = (⟨τ (u : q.adicCompletion L),
        (hpres τ (u : q.adicCompletion L)).mpr u.2⟩ : q.adicCompletionIntegers L) :=
      Subtype.ext (he u)
    rwa [hEq] at hum
  obtain ⟨I, hI, hcardI⟩ :=
    exists_inertiaSubgroup_adicCompletion_card_eq_ramificationIdx Q q hq
  refine ⟨I, hI, ?_, ?_⟩
  · refine ⟨fun n hn a => ?_⟩
    rw [hI]
    intro y
    have hz : (a⁻¹ (y : q.adicCompletion L)) ∈ q.adicCompletionIntegers L :=
      (hpres a⁻¹ (y : q.adicCompletion L)).mpr y.2
    have hnz : Valued.v (R := q.adicCompletion L) (Γ₀ := WithZero (Multiplicative ℤ))
        (n (a⁻¹ (y : q.adicCompletion L)) - (a⁻¹ (y : q.adicCompletion L))) < 1 :=
      (hI n).mp hn ⟨a⁻¹ (y : q.adicCompletion L), hz⟩
    have hwmem : (n (a⁻¹ (y : q.adicCompletion L)) - (a⁻¹ (y : q.adicCompletion L))) ∈
        q.adicCompletionIntegers L := by
      rw [IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers]
      exact le_of_lt hnz
    have hwm : (⟨n (a⁻¹ (y : q.adicCompletion L)) - (a⁻¹ (y : q.adicCompletion L)),
        hwmem⟩ : q.adicCompletionIntegers L) ∈
        IsLocalRing.maximalIdeal (q.adicCompletionIntegers L) :=
      (Commons.NumberTheory.NumberField.adicCompletionIntegers_mem_maximalIdeal_iff_valued_lt_one
        q _).mpr hnz
    have haw : (⟨a (n (a⁻¹ (y : q.adicCompletion L)) - (a⁻¹ (y : q.adicCompletion L))),
        (hpres a _).mpr hwmem⟩ : q.adicCompletionIntegers L) ∈
        IsLocalRing.maximalIdeal (q.adicCompletionIntegers L) :=
      hm_pres a ⟨_, hwmem⟩ hwm
    have hawval : Valued.v (R := q.adicCompletion L) (Γ₀ := WithZero (Multiplicative ℤ))
        (a (n (a⁻¹ (y : q.adicCompletion L)) - (a⁻¹ (y : q.adicCompletion L)))) < 1 := by
      have h := (Commons.NumberTheory.NumberField.adicCompletionIntegers_mem_maximalIdeal_iff_valued_lt_one
        q (⟨a (n (a⁻¹ (y : q.adicCompletion L)) - (a⁻¹ (y : q.adicCompletion L))),
            (hpres a _).mpr hwmem⟩ : q.adicCompletionIntegers L)).mp haw
      exact h
    have hEq : ((a * n * a⁻¹) (y : q.adicCompletion L) - (y : q.adicCompletion L)) =
        a (n (a⁻¹ (y : q.adicCompletion L)) - (a⁻¹ (y : q.adicCompletion L))) := by
      have h1 : ((a * n * a⁻¹) (y : q.adicCompletion L)) =
          a (n (a⁻¹ (y : q.adicCompletion L))) := by
        simp only [AlgEquiv.mul_apply]
      have h2 : a (a⁻¹ (y : q.adicCompletion L)) = (y : q.adicCompletion L) := by simp
      rw [h1, map_sub, h2]
    rw [hEq]
    exact hawval
  · have hG := natCard_algEquiv_adicCompletion_eq_ramificationIdx_mul_inertiaDeg Q q hq
    have h1 : Nat.card ((q.adicCompletion L ≃ₐ[Q.adicCompletion K] q.adicCompletion L) ⧸ I) *
        Nat.card I =
        Nat.card (q.adicCompletion L ≃ₐ[Q.adicCompletion K] q.adicCompletion L) := by
      simpa only [Subgroup.index_eq_card] using Subgroup.index_mul_card I
    rw [hcardI, hG] at h1
    have he : 0 < q.asIdeal.ramificationIdx (NumberField.RingOfIntegers K) :=
      Ideal.ramificationIdx_pos q.asIdeal (NumberField.RingOfIntegers K)
    rw [mul_comm (q.asIdeal.ramificationIdx (NumberField.RingOfIntegers K))
      (q.asIdeal.inertiaDeg (NumberField.RingOfIntegers K))] at h1
    exact Nat.mul_right_cancel he h1

end Commons.NumberTheory.NumberField.Completion
