import Mathlib
import Submission.Work.SSGRoute.Interfaces
import Submission.Work.SSGRoute.PTDefs
import Submission.Work.SSGRoute.InvAux
import Submission.Work.SSGRoute.InvAux.conjugate_of_ringEquiv
import Submission.Work.SSGRoute.InvAux.eq_of_fixes_fixSub
import Submission.Work.SSGRoute.ZDataTwo.exists_orderEmbedding_fixSub
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The archimedean place linked to an involution of `G_k`

Let `k` be a number field, `Ω` an algebraic closure of `k`, and `K` a finite Galois extension of `k`
inside `Ω` (`K` a number field).  For an involution `c` of `G_k = Gal(Ω/k)`, `c ≠ 1`, this file
produces a ring homomorphism `φ : Ω →+* ℂ` intertwining `c` with complex conjugation, and shows
that the infinite place `w` of `K` induced by `φ` has decomposition group exactly `⟨res c⟩`.

The existence of `φ` is the Artin–Schreier statement that the fixed field `F = Ω^c` of the
involution is (formally) real: the workspace file `SSGRoute/InvAux.lean` builds on `F` the linear
order whose positive cone is the set of norms `x · c x`, the file
`SSGRoute/ZDataTwo/exists_orderEmbedding_fixSub.lean` embeds the resulting ordered field in `ℝ`
(it is Archimedean because `Ω` is algebraic over `ℚ`), and an extension of that embedding to
`Ω →+* ℂ` intertwines `c` with complex conjugation (`InvAux/eq_of_fixes_fixSub.lean`).
-/

noncomputable section

open scoped Classical

namespace Work.SSGRoute.ArchPlace

open NumberField

/-- **The link with complex conjugation.**  Every non-trivial involution `c` of `G_k = Gal(Ω/k)`
(`Ω` an algebraic closure of the number field `k`) is the complex conjugation for some embedding of
`Ω` into `ℂ`: there is a ring homomorphism `φ : Ω →+* ℂ` with `φ (c x) = conj (φ x)` for all `x`.

The proof uses the fixed field `F = Ω^c`: the workspace has already shown that `F` carries the
structure of an Archimedean linearly ordered field (`SSGRoute/InvAux.lean`,
`SSGRoute/ZDataTwo/exists_orderEmbedding_fixSub.lean`), hence admits an order embedding
`ρ : F →+*o ℝ`.  Extending `ρ` along `ℝ ⊆ ℂ` to `Ω` (everything is algebraic over `F`) and
comparing the resulting involution with `c` (`InvAux/eq_of_fixes_fixSub.lean`) gives the link. -/
theorem exists_conjEmbedding (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (c : Ω ≃ₐ[k] Ω) (hc2 : c ^ 2 = 1) (hc1 : c ≠ 1) :
    ∃ φ : Ω →+* ℂ, ∀ x : Ω, φ (c x) = starRingEnd ℂ (φ x) := by
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed k
  haveI : CharZero Ω :=
    charZero_of_injective_algebraMap (FaithfulSMul.algebraMap_injective k Ω)
  haveI : Algebra.IsAlgebraic ℚ Ω := Algebra.IsAlgebraic.trans ℚ k Ω
  -- The underlying ring automorphism, as an involution.
  let c' : Ω ≃+* Ω := c.toRingEquiv
  have hc'mul : c' * c' = 1 := by
    ext x
    show c (c x) = x
    have h2 : c * c = 1 := by rw [← pow_two]; exact hc2
    have h3 := congrFun (congrArg (fun e : Ω ≃ₐ[k] Ω => (e : Ω → Ω)) h2) x
    simpa using h3
  have hc'1 : c' ≠ 1 := by
    intro h
    apply hc1
    ext x
    have hx := congrArg (fun e : Ω ≃+* Ω => e x) h
    simpa [c'] using hx
  haveI : Fact (c' * c' = 1) := ⟨hc'mul⟩
  haveI : Fact (c' ≠ 1) := ⟨hc'1⟩
  -- The order embedding of the fixed field into `ℝ`.
  obtain ⟨ρ, -, -⟩ := Work.SSGRoute.ZDataTwo.exists_orderEmbedding_fixSub (Ω := Ω) (c := c')
  let F : Subfield Ω := Work.SSGRoute.InvAux.fixSub c'
  let ρℂ : ↥F →+* ℂ := (algebraMap ℝ ℂ).comp (ρ : ↥F →+* ℝ)
  haveI : Algebra.IsAlgebraic ↥F Ω :=
    Work.SSGRoute.InvAux.algebra_isAlgebraic_over_fixSub hc'mul
  -- Extend it to `Ω`.
  let φ : Ω →+* ℂ := NumberField.ComplexEmbedding.lift Ω ρℂ
  have hφR : ∀ a : ↥F, φ ((algebraMap ↥F Ω) a) = ρℂ a := fun a =>
    NumberField.ComplexEmbedding.lift_algebraMap_apply Ω ρℂ a
  -- `φ` is real on the fixed field.
  have hreal : NumberField.ComplexEmbedding.IsReal (φ.comp (algebraMap ↥F Ω)) := by
    rw [NumberField.ComplexEmbedding.isReal_iff]
    rw [← NumberField.ComplexEmbedding.conjugate_comp]
    ext a
    simp only [RingHom.comp_apply]
    rw [NumberField.ComplexEmbedding.conjugate_coe_eq, hφR a]
    exact Complex.conj_ofReal (ρ a)
  -- Hence an involution `τ` of `Gal(Ω/F)` with `φ ∘ τ = conj ∘ φ`.
  haveI : IsAlgClosure ↥F Ω := ⟨inferInstance, inferInstance⟩
  haveI : IsGalois ↥F Ω := IsAlgClosure.isGalois ↥F Ω
  obtain ⟨σ, hσ⟩ := NumberField.ComplexEmbedding.exists_comp_symm_eq_of_comp_eq
      (k := ↥F) (K := Ω) φ (NumberField.ComplexEmbedding.conjugate φ) (by
        rw [NumberField.ComplexEmbedding.conjugate_comp]
        exact hreal.symm)
  let τ : Ω ≃ₐ[↥F] Ω := σ.symm
  have hτconj : NumberField.ComplexEmbedding.IsConj φ τ := hσ.symm
  have hτmul : (τ : Ω ≃+* Ω) * (τ : Ω ≃+* Ω) = 1 := by
    ext x
    exact NumberField.ComplexEmbedding.isConj_apply_apply hτconj x
  -- `φ` is not real valued, so `τ` is non-trivial.
  have hnotreal : ¬ NumberField.ComplexEmbedding.IsReal φ := by
    intro hrealφ
    obtain ⟨i, hi⟩ : ∃ i : Ω, i ^ 2 = -1 :=
      IsAlgClosed.exists_pow_nat_eq (-1 : Ω) (by norm_num : 0 < 2)
    have h3 : (((hrealφ.embedding i : ℝ)) : ℂ) ^ 2 = -1 := by
      rw [NumberField.ComplexEmbedding.IsReal.coe_embedding_apply hrealφ i, ← map_pow, hi]
      simp
    have h4 : (hrealφ.embedding i) ^ 2 = -1 := by
      apply Complex.ofReal_injective
      rw [Complex.ofReal_pow]
      simpa using h3
    nlinarith [sq_nonneg (hrealφ.embedding i)]
  have hτ1' : τ ≠ 1 :=
    (NumberField.ComplexEmbedding.isConj_ne_one_iff hτconj).mpr hnotreal
  have hτ1 : (τ : Ω ≃+* Ω) ≠ 1 := by
    intro h
    apply hτ1'
    apply AlgEquiv.ext
    intro x
    have hx := congrArg (fun e : Ω ≃+* Ω => e x) h
    simpa using hx
  -- `τ` fixes the fixed field of `c`, hence `τ = c`.
  have hfix : ∀ x : Ω, c' x = x → (τ : Ω ≃+* Ω) x = x := by
    intro x hx
    have hmem : x ∈ F := Work.SSGRoute.InvAux.mem_fixSub.mpr hx
    exact τ.commutes ⟨x, hmem⟩
  have hτeq : (τ : Ω ≃+* Ω) = c' :=
    Work.SSGRoute.InvAux.eq_of_fixes_fixSub hc'mul hc'1 hτmul hτ1 hfix
  refine ⟨φ, fun x => ?_⟩
  have h1 := NumberField.ComplexEmbedding.IsConj.eq hτconj x
  have harg : c x = τ x := by
    have hh : (τ : Ω ≃+* Ω) x = c' x := by rw [hτeq]
    simpa [c'] using hh.symm
  rw [harg, h1, starRingEnd_apply]

/-- **The archimedean place attached to a linked embedding.**  If `φ : Ω →+* ℂ` intertwines the
involution `c ∈ G_k` with complex conjugation, then the infinite place of `K` induced by
`φ ∘ (K ↪ Ω)` has decomposition group exactly `(zpowers c).map (res k K)`, and it is not a finite
place. -/
theorem decompK_of_conjEmbedding (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    [NumberField ↥K] (c : Ω ≃ₐ[k] Ω) (hc2 : c ^ 2 = 1) (hc1 : c ≠ 1)
    (φ : Ω →+* ℂ) (hφ : ∀ x : Ω, φ (c x) = starRingEnd ℂ (φ x)) :
    (∀ q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥K),
        NK.GlobalCFT.Place.ofInfinite
            (NumberField.InfinitePlace.mk (φ.comp (algebraMap ↥K Ω))) ≠
          NK.GlobalCFT.Place.ofFinite q) ∧
      (Subgroup.zpowers c).map (SSGRoute.res k K) =
        SSGRoute.PTExt.decompK (k := k)
          (NK.GlobalCFT.Place.ofInfinite
            (NumberField.InfinitePlace.mk (φ.comp (algebraMap ↥K Ω)))) := by
  classical
  set ψ : ↥K →+* ℂ := φ.comp (algebraMap ↥K Ω) with hψ
  set w : NK.GlobalCFT.Place ↥K :=
    NK.GlobalCFT.Place.ofInfinite (NumberField.InfinitePlace.mk ψ) with hw
  -- `c` is an involution, so is `res c`, and `(res c) y = c y` on `K`.
  have hcmul : c * c = 1 := by rw [← pow_two]; exact hc2
  have hcc : ∀ x : Ω, c (c x) = x := by
    intro x
    have h3 := congrFun (congrArg (fun e : Ω ≃ₐ[k] Ω => (e : Ω → Ω)) hcmul) x
    simpa using h3
  have hres_apply : ∀ y : ↥K,
      (algebraMap ↥K Ω) ((SSGRoute.res k K c) y) = c ((algebraMap ↥K Ω) y) :=
    fun y => AlgEquiv.restrictNormalHom_apply K c y
  have hresinv : (SSGRoute.res k K c)⁻¹ = SSGRoute.res k K c :=
    inv_eq_of_mul_eq_one_left (by rw [← map_mul, hcmul, map_one])
  have hresinv' : (SSGRoute.res k K c).symm = SSGRoute.res k K c := hresinv
  -- The stabiliser of `w` consists of `1` and `res c`.
  have hsmul : ∀ γ : ↥K ≃ₐ[k] ↥K, γ • w = NK.GlobalCFT.Place.ofInfinite
      (NumberField.InfinitePlace.mk (ψ.comp (γ.symm : ↥K →+* ↥K))) := fun γ => by
    rw [hw, NK.GlobalCFT.Place.smul_ofInfinite, NumberField.InfinitePlace.smul_mk]
  have key : ∀ γ : ↥K ≃ₐ[k] ↥K,
      γ • w = w ↔ γ = 1 ∨ γ = SSGRoute.res k K c := by
    intro γ
    constructor
    · intro hγ
      rw [hsmul, NK.GlobalCFT.Place.ofInfinite_inj,
        NumberField.InfinitePlace.mk_eq_iff] at hγ
      rcases hγ with h | h
      · -- `ψ ∘ γ⁻¹ = ψ` forces `γ = 1`.
        left
        apply AlgEquiv.ext
        intro y
        have hy := RingHom.congr_fun h y
        simp only [hψ, RingHom.comp_apply] at hy
        have hsym : γ.symm y = y := Subtype.ext (φ.injective hy)
        have h4 := congrArg γ hsym
        rw [AlgEquiv.apply_symm_apply] at h4
        rw [AlgEquiv.one_apply]
        exact h4.symm
      · -- `conj ∘ ψ ∘ γ⁻¹ = ψ` forces `γ = res c`.
        right
        have hy : ∀ y : ↥K,
            φ (c ((algebraMap ↥K Ω) (γ.symm y))) = φ ((algebraMap ↥K Ω) y) := by
          intro y
          have h1 := RingHom.congr_fun h y
          simp only [hψ, RingHom.comp_apply, NumberField.ComplexEmbedding.conjugate_coe_eq] at h1
          rw [hφ ((algebraMap ↥K Ω) (γ.symm y))]
          exact h1
        have h2 : ∀ y : ↥K,
            (algebraMap ↥K Ω) (γ.symm y) = c ((algebraMap ↥K Ω) y) := by
          intro y
          have h4 : c ((algebraMap ↥K Ω) (γ.symm y)) = (algebraMap ↥K Ω) y :=
            φ.injective (hy y)
          have h5 := congrArg c h4
          rwa [hcc] at h5
        have h6 : γ.symm = SSGRoute.res k K c := by
          apply AlgEquiv.ext
          intro y
          exact Subtype.ext ((h2 y).trans (hres_apply y).symm)
        have h7 : γ = (SSGRoute.res k K c)⁻¹ := by
          rw [← h6]
          exact (AlgEquiv.symm_symm γ).symm
        rwa [hresinv] at h7
    · rintro (h | h)
      · rw [h]; exact one_smul _ w
      · rw [h]
        rw [hsmul, NK.GlobalCFT.Place.ofInfinite_inj, NumberField.InfinitePlace.mk_eq_iff]
        right
        rw [hresinv']
        have hconj : ψ.comp (↑(SSGRoute.res k K c) : ↥K →+* ↥K) =
            NumberField.ComplexEmbedding.conjugate ψ := by
          ext y
          show ψ ((SSGRoute.res k K c) y) = starRingEnd ℂ (ψ y)
          rw [hψ]
          show φ ((algebraMap ↥K Ω) ((SSGRoute.res k K c) y)) =
            starRingEnd ℂ (φ ((algebraMap ↥K Ω) y))
          rw [hres_apply y, hφ ((algebraMap ↥K Ω) y)]
        rw [hconj]
        simpa using (star_star ψ)
  refine ⟨fun q => NK.GlobalCFT.Place.ofInfinite_ne_ofFinite _ q, ?_⟩
  rw [MonoidHom.map_zpowers]
  apply le_antisymm
  · rw [Subgroup.zpowers_le, MulAction.mem_stabilizer_iff]
    exact (key (SSGRoute.res k K c)).mpr (Or.inr rfl)
  · intro γ hγ
    rw [show SSGRoute.PTExt.decompK (k := k) w =
        MulAction.stabilizer (↥K ≃ₐ[k] ↥K) w from rfl,
      MulAction.mem_stabilizer_iff] at hγ
    rcases (key γ).mp hγ with h | h
    · rw [h]; exact Subgroup.one_mem _
    · rw [h]; exact Subgroup.mem_zpowers _

theorem linkedPlaceOfInvolution (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    [NumberField ↥K] (c : Ω ≃ₐ[k] Ω) (hc2 : c ^ 2 = 1) (hc1 : c ≠ 1) :
    ∃ (w : NK.GlobalCFT.Place ↥K) (φ : Ω →+* ℂ),
      (∀ q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥K),
        w ≠ NK.GlobalCFT.Place.ofFinite q) ∧
      w = NK.GlobalCFT.Place.ofInfinite
        (NumberField.InfinitePlace.mk (φ.comp (algebraMap ↥K Ω))) ∧
      (∀ x : Ω, φ (c x) = starRingEnd ℂ (φ x)) ∧
      (Subgroup.zpowers c).map (SSGRoute.res k K) = SSGRoute.PTExt.decompK (k := k) w := by
  obtain ⟨φ, hφ⟩ := exists_conjEmbedding k Ω c hc2 hc1
  exact ⟨NK.GlobalCFT.Place.ofInfinite (NumberField.InfinitePlace.mk (φ.comp (algebraMap ↥K Ω))),
    φ, (decompK_of_conjEmbedding k Ω K c hc2 hc1 φ hφ).1, rfl, hφ,
    (decompK_of_conjEmbedding k Ω K c hc2 hc1 φ hφ).2⟩

end Work.SSGRoute.ArchPlace
