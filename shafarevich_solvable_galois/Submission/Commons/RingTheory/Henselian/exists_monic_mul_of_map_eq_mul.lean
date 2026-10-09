import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Polynomial.UniversalFactorizationRing
import Mathlib.RingTheory.Unramified.LocalStructure
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option linter.style.haveILetI false

open Polynomial IsLocalRing

namespace Commons.RingTheory.Henselian

/-- Hensel's lemma, root-lifting over an arbitrary field quotient of a Henselian local ring. -/
theorem exists_root_of_eval₂_of_surjective {A K : Type*} [CommRing A] [HenselianLocalRing A]
    [Field K] (φ : A →+* K) (hφ : Function.Surjective φ) {f : Polynomial A} (hf : f.Monic)
    {a₀ : K} (h₁ : f.eval₂ φ a₀ = 0) (h₂ : f.derivative.eval₂ φ a₀ ≠ 0) :
    ∃ a : A, f.IsRoot a ∧ φ a = a₀ := by
  obtain ⟨a₁, rfl⟩ := hφ a₀
  have hker : RingHom.ker φ = maximalIdeal A :=
    eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective φ hφ)
  have hmem : f.eval a₁ ∈ maximalIdeal A := by
    rw [← hker, RingHom.mem_ker, ← Polynomial.eval₂_at_apply φ a₁]
    exact h₁
  have hunit : IsUnit (f.derivative.eval a₁) := by
    rw [← notMem_maximalIdeal, ← hker, RingHom.mem_ker, ← Polynomial.eval₂_at_apply φ a₁]
    exact h₂
  obtain ⟨a, ha, ha'⟩ := HenselianLocalRing.is_henselian f hf a₁ hmem hunit
  refine ⟨a, ha, ?_⟩
  have h2 : φ (a - a₁) = 0 := by
    rw [← hker, RingHom.mem_ker] at ha'; exact ha'
  rwa [map_sub, sub_eq_zero] at h2

/-- The Henselian retraction lemma: an étale algebra over a Henselian local ring with a point
over the maximal ideal having the same residue field admits a compatible retraction. -/
theorem exists_algHom_retract_of_isEtale
    {A B : Type*} [CommRing A] [HenselianLocalRing A]
    [CommRing B] [Algebra A B] (hB : Algebra.Etale A B)
    (Q : Ideal B) [Q.IsPrime] [Q.LiesOver (maximalIdeal A)]
    (hres : Function.Bijective (Ideal.ResidueField.mapₐ (maximalIdeal A) Q
        (Algebra.ofId A B) (Ideal.over_def Q (maximalIdeal A)))) :
    ∃ τ : B →ₐ[A] A, ∀ b : B,
      algebraMap A (maximalIdeal A).ResidueField (τ b) =
        (AlgEquiv.ofBijective _ hres).symm (algebraMap B Q.ResidueField b) := by
  haveI : Algebra.FinitePresentation A B := hB.finitePresentation
  haveI hEt : Algebra.IsEtaleAt A Q := inferInstance
  obtain ⟨g₀, hg₀Q, hSE⟩ := Algebra.IsEtaleAt.exists_isStandardEtale (R := A) Q
  let S := Localization.Away g₀
  haveI : Algebra.IsStandardEtale A S := hSE
  obtain ⟨P⟩ := Algebra.IsStandardEtale.nonempty_standardEtalePresentation (R := A) (S := S)
  let k := (maximalIdeal A).ResidueField
  let Φ := Ideal.ResidueField.mapₐ (maximalIdeal A) Q (Algebra.ofId A B)
    (Ideal.over_def Q (maximalIdeal A))
  let Φe : k ≃ₐ[A] Q.ResidueField := AlgEquiv.ofBijective Φ hres
  let φ₀ : B →ₐ[A] k := Φe.symm.toAlgHom.comp (IsScalarTower.toAlgHom A B Q.ResidueField)
  have hφ₀unit : IsUnit (φ₀ g₀) := by
    have h0 : algebraMap B Q.ResidueField g₀ ≠ 0 :=
      fun h => hg₀Q (Ideal.algebraMap_residueField_eq_zero.mp h)
    exact (isUnit_iff_ne_zero.mpr h0).map Φe.symm.toAlgHom
  let φ₁ : S →ₐ[A] k := IsLocalization.Away.liftAlgHom g₀ (f := φ₀) hφ₀unit
  have hφ₁ : ∀ b : B, φ₁ (algebraMap B S b) = φ₀ b := by
    intro b
    have hh := IsLocalization.Away.lift_comp (R := B) (S := S) (P := k) g₀ hφ₀unit
      (g := φ₀.toRingHom)
    have h2 := RingHom.congr_fun hh b
    simpa [φ₁, IsLocalization.Away.coe_liftAlgHom] using h2
  let φ₂ : P.Ring →ₐ[A] k := φ₁.comp P.equivRing.symm.toAlgHom
  let a₀ : k := φ₂ P.X
  have ha₀ : P.P.HasMap a₀ := by
    have := P.hasMap.map φ₁
    simpa [a₀, φ₂, StandardEtalePresentation.equivRing_symm_X] using this
  have hderiv : P.P.f.derivative.eval₂ (algebraMap A k) a₀ ≠ 0 := by
    have h := ha₀.isUnit_derivative_f
    rw [isUnit_iff_ne_zero] at h
    simpa [Polynomial.aeval_def] using h
  obtain ⟨α, hαroot, hαres⟩ :=
    exists_root_of_eval₂_of_surjective (algebraMap A k) (Ideal.algebraMap_residueField_surjective _)
      P.P.monic_f ha₀.1 hderiv
  have hα : P.P.HasMap α := by
    refine ⟨?_, ?_⟩
    · simpa [Polynomial.aeval_def, Polynomial.eval₂_id] using hαroot
    · have hg : IsUnit (P.P.g.eval α) := by
        rw [← notMem_maximalIdeal]
        intro hmem
        have h0 : algebraMap A k (P.P.g.eval α) = 0 :=
          Ideal.algebraMap_residueField_eq_zero.mpr hmem
        have hthis : (aeval a₀) P.P.g = 0 := by
          rw [Polynomial.aeval_def, ← hαres, Polynomial.eval₂_at_apply]
          exact h0
        exact (isUnit_iff_ne_zero.mp ha₀.2) hthis
      simpa [Polynomial.aeval_def, Polynomial.eval₂_id] using hg
  let τS : S →ₐ[A] A := (P.P.lift α hα).comp P.equivRing.toAlgHom
  refine ⟨τS.comp (IsScalarTower.toAlgHom A B S), ?_⟩
  have hkey : ∀ s : S, algebraMap A k (τS s) = φ₁ s := by
    have hcomp : (Algebra.ofId A k).comp τS = φ₁ := by
      apply P.hom_ext
      show algebraMap A k (τS P.x) = φ₁ P.x
      rw [show τS P.x = α by
        simp [τS, StandardEtalePresentation.equivRing_x, StandardEtalePair.lift_X],
        show φ₁ P.x = a₀ by
          simp [a₀, φ₂, StandardEtalePresentation.equivRing_symm_X]]
      exact hαres
    intro s
    exact AlgHom.congr_fun hcomp s
  intro b
  show algebraMap A k (τS ((IsScalarTower.toAlgHom A B S) b)) = Φe.symm (algebraMap B Q.ResidueField b)
  rw [IsScalarTower.toAlgHom_apply, hkey, hφ₁]
  rfl

end Commons.RingTheory.Henselian

namespace Commons.RingTheory.Henselian

theorem exists_monic_mul_of_map_eq_mul
    {A : Type*} [CommRing A] [HenselianLocalRing A]
    {f : Polynomial A} (hf : f.Monic)
    {g h : Polynomial (IsLocalRing.ResidueField A)} (hg : g.Monic) (hh : h.Monic)
    (hcop : IsCoprime g h)
    (hfac : Polynomial.map (IsLocalRing.residue A) f = g * h) :
    ∃ g' h' : Polynomial A, g'.Monic ∧ h'.Monic
      ∧ Polynomial.map (IsLocalRing.residue A) g' = g
      ∧ Polynomial.map (IsLocalRing.residue A) h' = h
      ∧ f = g' * h' := by
  set 𝔪 := maximalIdeal A with h𝔪
  haveI : 𝔪.IsMaximal := IsLocalRing.maximalIdeal.isMaximal A
  haveI : 𝔪.IsPrime := inferInstance
  set 𝔨 := 𝔪.ResidueField with h𝔨
  let e : IsLocalRing.ResidueField A ≃+* 𝔨 :=
    RingEquiv.ofBijective (algebraMap (IsLocalRing.ResidueField A) 𝔨)
      (Ideal.bijective_algebraMap_quotient_residueField 𝔪)
  have he_apply : ∀ x : IsLocalRing.ResidueField A,
      e x = algebraMap (IsLocalRing.ResidueField A) 𝔨 x :=
    fun x => RingEquiv.ofBijective_apply _ _ x
  have hmap_eq : (algebraMap A 𝔨 : A →+* 𝔨) = e.toRingHom.comp (IsLocalRing.residue A) := by
    ext x
    show (algebraMap A 𝔨) x = e ((IsLocalRing.residue A) x)
    rw [he_apply, ← IsLocalRing.ResidueField.algebraMap_eq,
      ← IsScalarTower.algebraMap_apply A (IsLocalRing.ResidueField A) 𝔨]
  have hfac' : Polynomial.map (algebraMap A 𝔨) f = g.map e.toRingHom * h.map e.toRingHom := by
    rw [hmap_eq, ← Polynomial.map_map, hfac, Polynomial.map_mul]
  obtain ⟨A', hRA', hAlg, hEt, Q, hQp, hQLO, f₁, g₂, hres, hf₁, hg₂, hfmul, hcop₁, hredf, hredg⟩ :=
    Algebra.exists_etale_bijective_residueFieldMap_and_map_eq_mul_and_isCoprime 𝔪 f
      (g.map e.toRingHom) (h.map e.toRingHom) hf (hg.map e.toRingHom) (hh.map e.toRingHom)
      hfac' (hcop.map (Polynomial.mapRingHom e.toRingHom))
  letI := hRA'
  letI := hAlg
  haveI := hEt
  haveI := hQp
  haveI := hQLO
  obtain ⟨τ, hτ⟩ := exists_algHom_retract_of_isEtale (A := A) (B := A') hEt Q hres
  let Φ := Ideal.ResidueField.mapₐ 𝔪 Q (Algebra.ofId A A') (Ideal.over_def Q 𝔪)
  let Φe : 𝔨 ≃ₐ[A] Q.ResidueField := AlgEquiv.ofBijective Φ hres
  have hres_τ : ∀ b : A', IsLocalRing.residue A (τ b) =
      e.symm (Φe.symm (algebraMap A' Q.ResidueField b)) := by
    intro b
    have h1 : (algebraMap A 𝔨) (τ b) = e (IsLocalRing.residue A (τ b)) := by
      rw [hmap_eq, RingHom.comp_apply]
      rfl
    have h2 : e (IsLocalRing.residue A (τ b)) = Φe.symm (algebraMap A' Q.ResidueField b) := by
      rw [← h1]; exact hτ b
    have := congrArg e.symm h2
    simpa using this
  have hcomp_τ : (IsLocalRing.residue A).comp (τ : A' →+* A) =
      e.symm.toRingHom.comp (Φe.symm.toRingHom.comp (algebraMap A' Q.ResidueField)) := by
    ext b
    exact hres_τ b
  have hΦe2 : Φe.toAlgHom = Φ := by
    apply AlgHom.ext; intro x
    change (AlgEquiv.ofBijective Φ hres) x = Φ x
    rw [AlgEquiv.ofBijective_apply]
  have hΦeh : Φe.toRingEquiv.toRingHom = Φ.toRingHom := by
    apply RingHom.ext
    intro x
    change (AlgEquiv.ofBijective Φ hres) x = Φ x
    rw [AlgEquiv.ofBijective_apply]
  have hΦesymm : Φe.symm.toRingEquiv.toRingHom.comp Φ.toRingHom = RingHom.id 𝔨 := by
    rw [AlgEquiv.symm_toRingEquiv, ← hΦeh]
    exact RingEquiv.symm_toRingHom_comp_toRingHom Φe.toRingEquiv
  have hee : e.symm.toRingHom.comp e.toRingHom = RingHom.id (IsLocalRing.ResidueField A) :=
    RingEquiv.symm_toRingHom_comp_toRingHom e
  refine ⟨f₁.map (τ : A' →+* A), g₂.map (τ : A' →+* A), hf₁.map (τ : A' →+* A), hg₂.map (τ : A' →+* A),
    ?_, ?_, ?_⟩
  · have step : Polynomial.map Φe.symm.toRingEquiv.toRingHom (Polynomial.map Φ.toRingHom
        (Polynomial.map e.toRingHom g)) = Polynomial.map e.toRingHom g := by
      rw [Polynomial.map_map, hΦesymm, Polynomial.map_id]
    rw [Polynomial.map_map, hcomp_τ, ← Polynomial.map_map, ← Polynomial.map_map, ← hredf, step,
      Polynomial.map_map, hee, Polynomial.map_id]
  · have step : Polynomial.map Φe.symm.toRingEquiv.toRingHom (Polynomial.map Φ.toRingHom
        (Polynomial.map e.toRingHom h)) = Polynomial.map e.toRingHom h := by
      rw [Polynomial.map_map, hΦesymm, Polynomial.map_id]
    rw [Polynomial.map_map, hcomp_τ, ← Polynomial.map_map, ← Polynomial.map_map, ← hredg, step,
      Polynomial.map_map, hee, Polynomial.map_id]
  · have h2 : Polynomial.map (τ : A' →+* A) (Polynomial.map (algebraMap A A') f) = f := by
      rw [Polynomial.map_map, AlgHom.comp_algebraMap,
        show (algebraMap A A : A →+* A) = RingHom.id A from rfl, Polynomial.map_id]
    rw [← Polynomial.map_mul, ← hfmul]
    exact h2.symm
end Commons.RingTheory.Henselian