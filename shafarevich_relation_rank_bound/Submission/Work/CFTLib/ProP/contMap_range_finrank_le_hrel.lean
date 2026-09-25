import Mathlib
import Submission.Work.CFTLib.ShafDeps
import Submission.Work.CFTLib.ProP.Galois
import Submission.Work.CFTLib.ProP.isGalois_maximalUnramifiedProPF
import Submission.Work.CFT.MaxProP.ContCohomology.Defs
import Submission.Work.CFT.MaxProP.ContCohomology.FiniteLevel.H2FpCont_finite

/-!
# The range of the transition map `contMap` of the maximal unramified pro-`p` extension

The transition maps of the direct system defining `H²_cont(G, 𝔽_p)` (where `G` is the Galois
group of the maximal everywhere unramified pro-`p` extension of a number field `F`) are the
inflation maps between the cohomology of the finite quotients.  For open normal subgroups
`U ≤ U'` of `G` the range of the transition map

`contMap p G U U' : H²(G ⧸ U, 𝔽_p) → H²(G ⧸ U', 𝔽_p)`

is (up to isomorphism) the range of the inflation map between the cohomology of the fixed fields,
so that the relative Shafarevich bound `CFTLib.RelShafBound` applies to it.

## Main result

* `Work.CFTLib.ProP.contMap_range_finrank_le_hrel`
-/

set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

open NumberField

noncomputable section

namespace Work.CFTLib.ProP

open LeanEval.NumberTheory

/-- The inflation map `KochTransfer.infl` of the Koch-transfer vocabulary agrees with the map
induced on abstract group cohomology by `groupCohomology.map`. -/
theorem infl_eq_mapHom {p : ℕ} {G Q : Type} [Group G] [Group Q] (f : G →* Q) :
    Work.CFT.KochTransfer.infl (p := p) f =
      (groupCohomology.map f (CategoryTheory.CategoryStruct.id (Rep.trivial (ZMod p) G (ZMod p)) :
          Rep.res f (Rep.trivial (ZMod p) Q (ZMod p)) ⟶
            Rep.trivial (ZMod p) G (ZMod p)) 2).hom := by
  refine LinearMap.ext fun x => ?_
  refine groupCohomology.H2_induction_on x fun c => ?_
  rw [Work.CFT.KochTransfer.infl_H2π, groupCohomology.H2π_comp_map_apply]
  rfl

/-- Isomorphic pre- and post-composition with linear equivalences does not change the
dimension of the range. -/
theorem finrank_range_sandwich {R M M' N N' : Type*} [Ring R]
    [AddCommGroup M] [Module R M] [AddCommGroup M'] [Module R M']
    [AddCommGroup N] [Module R N] [AddCommGroup N'] [Module R N']
    (P : N ≃ₗ[R] N') (Q : M' ≃ₗ[R] M) (f : M →ₗ[R] N) :
    Module.finrank R (LinearMap.range (P.toLinearMap.comp (f.comp Q.toLinearMap)))
      = Module.finrank R (LinearMap.range f) := by
  rw [LinearMap.range_comp, LinearMap.range_comp,
    LinearMap.range_eq_top.mpr Q.surjective, Submodule.map_top]
  exact LinearEquiv.finrank_map_eq P (LinearMap.range f)

/-- The same identity, with the identity morphism written at the source of `map` (the form in
which it arises in `CFTLib.RelShafBound`). -/
theorem infl_eq_mapHom' {p : ℕ} {G Q : Type} [Group G] [Group Q] (f : G →* Q) :
    Work.CFT.KochTransfer.infl (p := p) f =
      (groupCohomology.map f
        (CategoryTheory.CategoryStruct.id (Rep.res f (Rep.trivial (ZMod p) Q (ZMod p))) :
          Rep.res f (Rep.trivial (ZMod p) Q (ZMod p)) ⟶
            Rep.trivial (ZMod p) G (ZMod p)) 2).hom :=
  infl_eq_mapHom f

/-- Conjugation by an `F`-algebra isomorphism `e : K ≃ₐ[F] Kf`: the `MulEquiv`
`Gal(Kf/F) ≃* Gal(K/F)` which sends `σ` to `e⁻¹ ∘ σ ∘ e`. -/
def conjMulEquiv {F K Kf : Type} [Field F] [Field K] [Field Kf]
    [Algebra F K] [Algebra F Kf] (e : K ≃ₐ[F] Kf) :
    (Kf ≃ₐ[F] Kf) ≃* (K ≃ₐ[F] K) where
  toFun σ := e.trans (σ.trans e.symm)
  invFun β := e.symm.trans (β.trans e)
  left_inv σ := by ext x; simp [AlgEquiv.trans_apply]
  right_inv β := by ext x; simp [AlgEquiv.trans_apply]
  map_mul' σ τ := by ext x; simp [AlgEquiv.trans_apply]

@[simp]
theorem conjMulEquiv_apply {F K Kf : Type} [Field F] [Field K] [Field Kf]
    [Algebra F K] [Algebra F Kf] (e : K ≃ₐ[F] Kf) (σ : Kf ≃ₐ[F] Kf) (x : K) :
    conjMulEquiv e σ x = e.symm (σ (e x)) := rfl

@[simp]
theorem conjMulEquiv_symm_apply {F K Kf : Type} [Field F] [Field K] [Field Kf]
    [Algebra F K] [Algebra F Kf] (e : K ≃ₐ[F] Kf) (β : K ≃ₐ[F] K) (x : Kf) :
    (conjMulEquiv e).symm β x = e (β (e.symm x)) := rfl

/-- **Compatibility of algebra isomorphisms.**  Let `Kf ⊆ Kf' ⊆ E` be a tower of fields with
`Kf/F` and `Kf'/F` normal and `E/F` normal, `incl : Kf →ₐ[F] Kf'` the inclusion, and
`e : K ≃ₐ[F] Kf`, `e₀ : K' ≃ₐ[F] Kf'` two isomorphisms.  Then `e₀` can be adjusted by an
automorphism of `Kf'` so that it extends `e` along the embedding `K ⊆ K'`:
`e' (algebraMap K K' y) = incl (e y)` for every `y : K`. -/
theorem exists_compat_algEquiv
    {F K K' Kf Kf' E : Type*}
    [Field F] [Field K] [Field K'] [Field Kf] [Field Kf'] [Field E]
    [Algebra F K] [Algebra F K'] [Algebra K K'] [IsScalarTower F K K']
    [Algebra F Kf] [Algebra F Kf'] [Algebra F E]
    [Algebra Kf E] [Algebra Kf' E] [IsScalarTower F Kf E] [IsScalarTower F Kf' E]
    [FaithfulSMul Kf' E]
    [Normal F Kf] [Normal F Kf'] [Normal F E]
    (incl : Kf →ₐ[F] Kf') (hincl : ∀ z : Kf, algebraMap Kf' E (incl z) = algebraMap Kf E z)
    (e : K ≃ₐ[F] Kf) (e₀ : K' ≃ₐ[F] Kf') :
    ∃ e' : K' ≃ₐ[F] Kf', ∀ y : K, e' (algebraMap K K' y) = incl (e y) := by
  let ι : Kf →ₐ[F] Kf' :=
    (e₀.toAlgHom).comp ((IsScalarTower.toAlgHom F K K').comp (e.symm.toAlgHom))
  let φ : Kf →ₐ[F] E := (IsScalarTower.toAlgHom F Kf' E).comp ι
  let θ₁ : Kf ≃ₐ[F] Kf := Normal.algHomEquivAut F E Kf φ
  have hφ : (IsScalarTower.toAlgHom F Kf E).comp θ₁.toAlgHom = φ :=
    Equiv.symm_apply_apply (Normal.algHomEquivAut F E Kf) φ
  have hφz : ∀ z : Kf, algebraMap Kf' E (ι z) = algebraMap Kf E (θ₁ z) := by
    intro z
    have h := congrArg (fun f : Kf →ₐ[F] E => f z) hφ
    simp only [AlgHom.comp_apply, IsScalarTower.toAlgHom_apply, φ] at h
    exact h.symm
  have hι : ∀ z : Kf, ι z = incl (θ₁ z) := by
    intro z
    refine FaithfulSMul.algebraMap_injective Kf' E ?_
    rw [hincl]
    exact hφz z
  obtain ⟨αt, hαt⟩ := AlgEquiv.restrictNormalHom_surjective (K₁ := Kf) E θ₁⁻¹
  have hαt' : αt.restrictNormal Kf = θ₁⁻¹ := hαt
  let α : Kf' ≃ₐ[F] Kf' := αt.restrictNormal Kf'
  have hα : ∀ z : Kf, α (incl z) = incl (θ₁⁻¹ z) := by
    intro z
    refine FaithfulSMul.algebraMap_injective Kf' E ?_
    rw [hincl, AlgEquiv.restrictNormal_commutes, hincl, ← AlgEquiv.restrictNormal_commutes]
    rw [congrArg (fun f : Kf ≃ₐ[F] Kf => f z) hαt']
  refine ⟨e₀.trans α, fun y => ?_⟩
  have hy : e₀ (algebraMap K K' y) = ι (e y) := by simp [ι]
  rw [show (e₀.trans α) (algebraMap K K' y) = α (e₀ (algebraMap K K' y)) from rfl, hy, hι, hα]
  simp

/-- **The range of the transition map `contMap` is bounded by the relative Shafarevich bound.** -/
theorem contMap_range_finrank_le_hrel (F : Type) [Field F] [NumberField F] (p : ℕ)
    [Fact (Nat.Prime p)] (hrel : CFTLib.RelShafBound)
    (hgalE : IsGalois F ↥(LeanEval.NumberTheory.maximalUnramifiedProPF F p))
    (K K' : Type) [Field K] [NumberField K] [Field K'] [NumberField K']
    [Algebra F K] [Algebra F K'] [Algebra K K'] [IsScalarTower F K K']
    [FiniteDimensional F K] [FiniteDimensional F K'] [IsGalois F K] [IsGalois F K']
    (U U' : Work.CFT.MaxProP.OpenNormal (LeanEval.NumberTheory.MaxUnramifiedProPGaloisGroup F p))
    (hUU' : U ≤ U')
    (hK : Nonempty (K ≃ₐ[F] ↥(IntermediateField.fixedField U.carrier)))
    (hK' : Nonempty (K' ≃ₐ[F] ↥(IntermediateField.fixedField U'.carrier)))
    (huni : CFTLib.IsUnramified F K')
    (hp : IsPGroup p (K' ≃ₐ[F] K'))
    (hmax : ∀ (L : Type) [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L],
        (∀ a b : L ≃ₐ[K] L, a * b = b * a) → IsPGroup p (L ≃ₐ[K] L) → CFTLib.IsUnramified K L →
        Nonempty (L →ₐ[K] K')) :
    Module.finrank (ZMod p) (LinearMap.range (Work.CFT.MaxProP.contMap p
        (LeanEval.NumberTheory.MaxUnramifiedProPGaloisGroup F p) U U' hUU')) ≤
      Module.finrank (ZMod p) (Work.Tower.Shafarevich.H1Fp p (K' ≃ₐ[F] K')) +
        (NumberField.InfinitePlace.nrRealPlaces F + NumberField.InfinitePlace.nrComplexPlaces F - 1) +
        CFTLib.delta F p :=
by
  classical
  -- ===== setup =====
  have hle : (IntermediateField.fixedField U.carrier ≤ IntermediateField.fixedField U'.carrier) :=
    IntermediateField.fixedField_antitone (Work.CFT.MaxProP.OpenNormal.le_def.mp hUU')
  haveI hgalKf : IsGalois F ↥(IntermediateField.fixedField U.carrier) :=
    Work.CFTLib.ProP.fixedField_isGalois hgalE U.normal U.isOpen
  haveI hgalKf' : IsGalois F ↥(IntermediateField.fixedField U'.carrier) :=
    Work.CFTLib.ProP.fixedField_isGalois hgalE U'.normal U'.isOpen
  haveI hgalE' : IsGalois F ↥(LeanEval.NumberTheory.maximalUnramifiedProPF F p) := hgalE
  obtain ⟨e⟩ := hK
  obtain ⟨e₀⟩ := hK'
  let incl : ↥(IntermediateField.fixedField U.carrier) →ₐ[F]
      ↥(IntermediateField.fixedField U'.carrier) := IntermediateField.inclusion hle
  have hco : ∀ z : ↥(IntermediateField.fixedField U.carrier),
      ((incl z : ↥(IntermediateField.fixedField U'.carrier)) :
        ↥(LeanEval.NumberTheory.maximalUnramifiedProPF F p))
        = (z : ↥(LeanEval.NumberTheory.maximalUnramifiedProPF F p)) := by
    intro z
    rw [IntermediateField.coe_inclusion]
  have hincl : ∀ z : ↥(IntermediateField.fixedField U.carrier),
      algebraMap ↥(IntermediateField.fixedField U'.carrier)
          ↥(LeanEval.NumberTheory.maximalUnramifiedProPF F p) (incl z)
        = algebraMap ↥(IntermediateField.fixedField U.carrier)
          ↥(LeanEval.NumberTheory.maximalUnramifiedProPF F p) z := by
    intro z
    exact hco z
  obtain ⟨e', he'⟩ := exists_compat_algEquiv (F := F) (K := K) (K' := K')
    (Kf := ↥(IntermediateField.fixedField U.carrier))
    (Kf' := ↥(IntermediateField.fixedField U'.carrier))
    (E := ↥(LeanEval.NumberTheory.maximalUnramifiedProPF F p)) incl hincl e e₀
  let rK : (K' ≃ₐ[F] K') →* (K ≃ₐ[F] K) := AlgEquiv.restrictNormalHom (K₁ := K') K
  -- ===== the canonical restriction isomorphisms =====
  let Uc : ClosedSubgroup Gal(↥(LeanEval.NumberTheory.maximalUnramifiedProPF F p)/F) :=
    ⟨U.carrier, U.carrier.isClosed_of_isOpen U.isOpen⟩
  let Uc' : ClosedSubgroup Gal(↥(LeanEval.NumberTheory.maximalUnramifiedProPF F p)/F) :=
    ⟨U'.carrier, U'.carrier.isClosed_of_isOpen U'.isOpen⟩
  haveI hUcn : Uc.Normal := U.normal
  haveI hUcn' : Uc'.Normal := U'.normal
  let qU : (LeanEval.NumberTheory.MaxUnramifiedProPGaloisGroup F p) ⧸ U.carrier ≃*
      (↥(IntermediateField.fixedField U.carrier) ≃ₐ[F]
        ↥(IntermediateField.fixedField U.carrier)) := InfiniteGalois.normalAutEquivQuotient Uc
  let qU' : (LeanEval.NumberTheory.MaxUnramifiedProPGaloisGroup F p) ⧸ U'.carrier ≃*
      (↥(IntermediateField.fixedField U'.carrier) ≃ₐ[F]
        ↥(IntermediateField.fixedField U'.carrier)) := InfiniteGalois.normalAutEquivQuotient Uc'
  have hqU : ∀ σ : LeanEval.NumberTheory.MaxUnramifiedProPGaloisGroup F p,
      qU (QuotientGroup.mk σ)
        = (AlgEquiv.restrictNormalHom (↥(IntermediateField.fixedField U.carrier))) σ :=
    fun σ => InfiniteGalois.normalAutEquivQuotient_apply Uc σ
  have hqU' : ∀ σ : LeanEval.NumberTheory.MaxUnramifiedProPGaloisGroup F p,
      qU' (QuotientGroup.mk σ)
        = (AlgEquiv.restrictNormalHom (↥(IntermediateField.fixedField U'.carrier))) σ :=
    fun σ => InfiniteGalois.normalAutEquivQuotient_apply Uc' σ
  -- value form
  have hqUval : ∀ (σ : Gal(↥(LeanEval.NumberTheory.maximalUnramifiedProPF F p)/F))
      (z : ↥(IntermediateField.fixedField U.carrier)),
      algebraMap ↥(IntermediateField.fixedField U.carrier)
          ↥(LeanEval.NumberTheory.maximalUnramifiedProPF F p)
          ((qU (QuotientGroup.mk (σ : LeanEval.NumberTheory.MaxUnramifiedProPGaloisGroup F p))) z)
        = σ (algebraMap ↥(IntermediateField.fixedField U.carrier)
              ↥(LeanEval.NumberTheory.maximalUnramifiedProPF F p) z) := by
    intro σ z
    rw [hqU σ]
    exact AlgEquiv.restrictNormal_commutes σ _ z
  have hqU'val : ∀ (σ : Gal(↥(LeanEval.NumberTheory.maximalUnramifiedProPF F p)/F))
      (z : ↥(IntermediateField.fixedField U'.carrier)),
      algebraMap ↥(IntermediateField.fixedField U'.carrier)
          ↥(LeanEval.NumberTheory.maximalUnramifiedProPF F p)
          ((qU' (QuotientGroup.mk (σ : LeanEval.NumberTheory.MaxUnramifiedProPGaloisGroup F p))) z)
        = σ (algebraMap ↥(IntermediateField.fixedField U'.carrier)
              ↥(LeanEval.NumberTheory.maximalUnramifiedProPF F p) z) := by
    intro σ z
    rw [hqU' σ]
    exact AlgEquiv.restrictNormal_commutes σ _ z
  -- ===== the isomorphisms λ, λ' and the transported map Ψ =====
  let c := conjMulEquiv e
  let c' := conjMulEquiv e'
  let lam : (LeanEval.NumberTheory.MaxUnramifiedProPGaloisGroup F p) ⧸ U.carrier ≃*
      (K ≃ₐ[F] K) := qU.trans c
  let lam' : (LeanEval.NumberTheory.MaxUnramifiedProPGaloisGroup F p) ⧸ U'.carrier ≃*
      (K' ≃ₐ[F] K') := qU'.trans c'
  let pK : (LeanEval.NumberTheory.MaxUnramifiedProPGaloisGroup F p) ⧸ U'.carrier →*
      (LeanEval.NumberTheory.MaxUnramifiedProPGaloisGroup F p) ⧸ U.carrier :=
    Work.CFT.MaxProP.OpenNormal.quotientMap U U' hUU'
  let Ψ : (K' ≃ₐ[F] K') →* (K ≃ₐ[F] K) :=
    lam.toMonoidHom.comp (pK.comp lam'.symm.toMonoidHom)
  have hpKmk : ∀ σ : LeanEval.NumberTheory.MaxUnramifiedProPGaloisGroup F p,
      pK (QuotientGroup.mk σ) = QuotientGroup.mk σ := by
    intro σ
    simp only [pK, Work.CFT.MaxProP.OpenNormal.quotientMap, QuotientGroup.lift_mk',
      QuotientGroup.mk'_apply]
  -- ===== Ψ agrees with the restriction map =====
  have hΨeq : Ψ = rK := by
    refine MonoidHom.ext fun τ => AlgEquiv.ext fun x => ?_
    refine FaithfulSMul.algebraMap_injective K K' ?_
    refine e'.injective ?_
    obtain ⟨σ, hσ⟩ : ∃ σ : LeanEval.NumberTheory.MaxUnramifiedProPGaloisGroup F p,
        QuotientGroup.mk σ = qU'.symm (c'.symm τ) := QuotientGroup.mk_surjective _
    have hσ' : qU' (QuotientGroup.mk σ) = c'.symm τ := by
      rw [hσ, MulEquiv.apply_symm_apply]
    have hres : σ.restrictNormal (↥(IntermediateField.fixedField U'.carrier)) = c'.symm τ :=
      (hqU' σ).symm.trans hσ'
    -- left hand side
    have hL : e' (algebraMap K K' (Ψ τ x))
        = incl ((qU (QuotientGroup.mk σ)) (e x)) := by
      have h0 : lam'.symm τ = QuotientGroup.mk σ := by
        rw [show lam'.symm τ = qU'.symm (c'.symm τ) from rfl]
        exact hσ.symm
      have h1 : (Ψ τ) x = e.symm ((qU (pK (QuotientGroup.mk σ))) (e x)) := by
        have h2 : Ψ τ = lam (pK (QuotientGroup.mk σ)) := by
          change lam (pK (lam'.symm τ)) = lam (pK (QuotientGroup.mk σ))
          rw [h0]
        rw [h2]
        simp only [lam, MulEquiv.trans_apply, c, conjMulEquiv_apply]
      rw [h1, hpKmk σ, he', AlgEquiv.apply_symm_apply]
    -- right hand side
    have hR : e' (algebraMap K K' ((AlgEquiv.restrictNormalHom (K₁ := K') K) τ x))
        = (c'.symm τ) (incl (e x)) := by
      have h1 : e' (algebraMap K K' (rK τ x)) = e' (τ (algebraMap K K' x)) := by
        simp only [rK, AlgEquiv.restrictNormalHom, MonoidHom.mk'_apply,
          AlgEquiv.restrictNormal_commutes]
      have h2 : e' (τ (algebraMap K K' x)) = (c'.symm τ) (e' (algebraMap K K' x)) := by
        simp only [c', conjMulEquiv_symm_apply, AlgEquiv.symm_apply_apply]
      rw [h1, h2, he' x]
    rw [hL, hR]
    refine FaithfulSMul.algebraMap_injective ↥(IntermediateField.fixedField U'.carrier)
      ↥(LeanEval.NumberTheory.maximalUnramifiedProPF F p) ?_
    rw [hincl, hqUval σ (e x), ← hσ', ← hincl]
    exact (hqU'val σ (incl (e x))).symm
  -- ===== transport of the range =====
  have htransport : Module.finrank (ZMod p)
      (LinearMap.range (Work.CFT.MaxProP.contMap p
        (LeanEval.NumberTheory.MaxUnramifiedProPGaloisGroup F p) U U' hUU'))
      = Module.finrank (ZMod p) (LinearMap.range (Work.CFT.KochTransfer.infl (p := p) rK)) := by
    have hcomp : ((Work.CFT.KochTransfer.inflEquiv p lam').toLinearMap).comp
        (((Work.CFT.KochTransfer.infl (p := p) pK)).comp
          ((Work.CFT.KochTransfer.inflEquiv p lam.symm).toLinearMap))
        = Work.CFT.KochTransfer.infl (p := p) Ψ := by
      let lamH : (LeanEval.NumberTheory.MaxUnramifiedProPGaloisGroup F p) ⧸ U.carrier →*
          (K ≃ₐ[F] K) := lam
      let lam'H : (K' ≃ₐ[F] K') →*
          (LeanEval.NumberTheory.MaxUnramifiedProPGaloisGroup F p) ⧸ U'.carrier := lam'.symm
      have e1 : ((Work.CFT.KochTransfer.inflEquiv p lam').toLinearMap)
          = Work.CFT.KochTransfer.infl (p := p) lam'H := rfl
      have e2 : ((Work.CFT.KochTransfer.inflEquiv p lam.symm).toLinearMap)
          = Work.CFT.KochTransfer.infl (p := p) lamH := rfl
      have hΨunfold : Ψ = lamH.comp (pK.comp lam'H) := rfl
      rw [e1, e2, hΨunfold]
      rw [← Work.CFT.KochTransfer.infl_comp (p := p) pK lamH]
      rw [← Work.CFT.KochTransfer.infl_comp (p := p) lam'H (lamH.comp pK)]
      simp only [MonoidHom.comp_assoc]
    have hcontMap : Work.CFT.MaxProP.contMap p
        (LeanEval.NumberTheory.MaxUnramifiedProPGaloisGroup F p) U U' hUU'
        = Work.CFT.KochTransfer.infl (p := p) pK := rfl
    rw [hcontMap, ← hΨeq, ← hcomp, finrank_range_sandwich]
  -- ===== apply the relative Shafarevich bound =====
  have hb := hrel F K K' p hp huni hmax
  rw [show (AlgEquiv.restrictNormalHom (K₁ := K') K) = rK from rfl] at hb
  rw [← infl_eq_mapHom' rK] at hb
  exact le_of_eq htransport |>.trans hb


end Work.CFTLib.ProP
