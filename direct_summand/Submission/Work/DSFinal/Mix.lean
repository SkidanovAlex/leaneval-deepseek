import Submission.Work.DSMap.Gaps
import Submission.Work.DSFinal.Roots
import Submission.Work.DSM8m2.Main
import Submission.Work.DSMX0U.Main
import Submission.Work.DSMX0bU.Main
import Submission.Work.DSF1.Main
import Submission.Work.DSCHART.Main
import Submission.Work.DSM1p.Main
import Submission.Work.DSM2b.Main
import Submission.Work.DSM7p.Main
import Submission.Work.DSSEC.Main
import Submission.Work.DSDEN.Main
import Submission.Work.DSM5c.Main
import Submission.Work.DSAMR.Main
import Submission.Work.DSAM2.Main
import Submission.Work.DSFFP.Main
import Submission.Work.DSREG.Main
import Submission.Work.DSCOH.Main
import Submission.Work.DSM4p.Main

/-! # DSFinal.Mix — LEAD-OWNED final wiring (curric-46, 10-14)

Copies of `Mix2.modSplit_descent_p`, `Mix2.area_M5d`, `Gaps.area_M6Gpos1`, `Gaps.area_MIX2pos1`
(and of `DSMX0U.cechZ_homology_finite`) citing the PROVED area deliverables.  Remaining frozen
leaves: `DSMap.Gaps.area_M2pos1` (via `m2pos1_any`), `DSMap.Mix2.area_M4p`, `DSMap.area_COH`. -/

open CategoryTheory AlgebraicGeometry IsLocalRing Limits Opposite

attribute [local instance] MvPolynomial.gradedAlgebra

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

namespace Work.DSFinal

open DSMap DSMap.Mix DSMap.Mix2

universe a b c

/-- FFP + AM2 (proved) : copy of `Mix2.modSplit_descent_p`. -/
theorem modSplit_descent_p_final (p : ℕ) {A : Type a} [CommRing A]
    (P : CochainComplex (ModuleCat.{a} A) ℤ) (hP : IsBddFinFree P) (ε : ModuleCat.of A A ⟶ P.X 0)
    (hε : ∀ k, ε ≫ P.d 0 k = 0) {D D' : Type a} [CommRing D] [CommRing D'] [Algebra D D']
    (ψ : A →+* D) (hD : IsSMulRegular D (p : D)) (hD' : IsSMulRegular D' (p : D'))
    (hff : Module.FaithfullyFlat (D ⧸ Ideal.span {(p : D)})
      (D' ⧸ (Ideal.span {(p : D)}).map (algebraMap D D'))) (m : ℕ) (c : D)
    (h : ModSplit P ε ((algebraMap D D').comp ψ) (Ideal.span {(p : D') ^ m})
      (algebraMap D D' c)) :
    ModSplit P ε ψ (Ideal.span {(p : D) ^ m}) c := by
  refine DSMap.Mix.modSplit_descent_proved P hP ε hε ψ _
    (DSMap.Mix2.ff_mod_pow_proved p hD hD' hff m) c ?_
  rwa [Ideal.map_span, Set.image_singleton, map_pow, map_natCast]

example : @modSplit_descent_p_final.{a} = @DSMap.Mix2.modSplit_descent_p.{a} := rfl

theorem area_M5d_final (p : ℕ) [Fact p.Prime] (W : Type a) [CommRing W] (QW : PerfectoidData p W)
    {ι : Type a} [Finite ι] [DecidableEq ι] (t : ι → W) (tr : ι → ℕ → W)
    (htr0 : ∀ i, tr i 0 = t i) (htr : ∀ i k, tr i (k + 1) ^ p = tr i k)
    (j₀ : ι) (e : ℕ) (hj₀ : t j₀ = QW.ϖ 0 ^ e)
    {A : Type a} [CommRing A] (ψ : A →+* W) (P : CochainComplex (ModuleCat.{a} A) ℤ)
    (hP : IsBddFinFree P) (ε : ModuleCat.of A A ⟶ P.X 0) (hε : ∀ k, ε ≫ P.d 0 k = 0)
    (ρ : P ⟶ chartCechA ψ t)
    (hρ : ε ≫ ρ.f 0 ≫ (ModuleCat.restrictScalars ψ).map
      ((chartCech t).extendXIso ComplexShape.embeddingUpNat (i := 0) rfl).hom =
        chartCoaugA ψ t) :
    ∀ m k, ModSplit P ε ψ (Ideal.span {(p : W) ^ m}) (QW.ϖ k) := by
  obtain ⟨Dp, η, hD⟩ := DSMap.Mix2.area_M5c_proved p W QW t tr htr0 htr j₀ e hj₀
  intro m k
  let φ := (cechComplexFunctor (chartIdx ι)).map η
  refine DSMap.Mix2.modSplit_of_almostAcyc_proved p ψ QW.ϖ QW.root _ _ _ (hD m) P hP ε hε
    (ρ ≫ ((ModuleCat.restrictScalars ψ).mapHomologicalComplex _).map
      (HomologicalComplex.extendMap φ ComplexShape.embeddingUpNat : chartCechZ t ⟶ _)) ?_ k
  rw [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f,
    HomologicalComplex.extendMap_f φ ComplexShape.embeddingUpNat (i := 0) (i' := 0) rfl]
  simp only [Functor.map_comp, Category.assoc]
  erw [Iso.inv_hom_id_map, Category.comp_id]
  refine ((reassoc_of% hρ) ((ModuleCat.restrictScalars ψ).map (φ.f 0))).trans ?_
  rw [chartCoaugA, Category.assoc]

example : @area_M5d_final.{a} = @DSMap.Mix2.area_M5d.{a} := rfl

/-- F1 (proved) + COH (frozen): copy of `Work.DSMX0U.cechZ_homology_finite`. -/
theorem cechZ_homology_finite_final {A : Type a} [CommRing A] [IsNoetherianRing A]
    {X : Scheme.{a}} (f : X ⟶ Spec (.of A)) [IsProper f] (hp : DSMap.IsProjOver A f)
    {ι : Type a} [Finite ι] (U : ι → X.Opens) (hU : ∀ i, IsAffineOpen (U i))
    (hcov : ⨆ i, U i = ⊤) :
    ∃ N : ℤ, ∀ i : ℤ, Module.Finite A ((DSMap.cechZ A X f U).homology i) ∧
      (N < i → CategoryTheory.Limits.IsZero ((DSMap.cechZ A X f U).homology i)) := by
  letI : HasDerivedCategory (ModuleCat.{a} A) := HasDerivedCategory.standard _
  letI : HasDerivedCategory (SheafOfModules X.ringCatSheaf) := HasDerivedCategory.standard _
  haveI hEn : EnoughInjectives (SheafOfModules X.ringCatSheaf) :=
    inferInstanceAs (EnoughInjectives (Scheme.Modules X))
  haveI hQC : QuasiCompact f := Work.DSMX0bU.quasiCompact_of_isProper f
  obtain ⟨N, hN⟩ := DSMap.area_COH_proved A X f hp
  obtain ⟨cc, e, -, -⟩ := DSMap.area_F1_cech_proved A X f U hU hcov
  refine ⟨N, fun i => ⟨?_, ?_⟩⟩
  · have iso := (DerivedCategory.homologyFunctor (ModuleCat.{a} A) i).mapIso e ≪≫
      (DerivedCategory.homologyFunctorFactors (ModuleCat.{a} A) i).app (DSMap.cechZ A X f U)
    haveI := (hN i).1
    exact Module.Finite.equiv iso.toLinearEquiv
  · intro hi
    have iso := (DerivedCategory.homologyFunctor (ModuleCat.{a} A) i).mapIso e ≪≫
      (DerivedCategory.homologyFunctorFactors (ModuleCat.{a} A) i).app (DSMap.cechZ A X f U)
    exact IsZero.of_iso ((hN i).2 hi) iso.symm

/-- MX0U from the clean coherence form, fed with F1 (proved) + COH (frozen). -/
theorem area_MX0U_final (A : Type a) [CommRing A] [IsNoetherianRing A] (X : Scheme.{a})
    (f : X ⟶ Spec (.of A)) [IsProper f] (hp : IsProjOver A f) {ι : Type a} [Finite ι]
    (U : ι → X.Opens) (hU : ∀ i, IsAffineOpen (U i)) (hcov : ⨆ i, U i = ⊤) :
    ∃ (P : CochainComplex (ModuleCat.{a} A) ℤ) (ε : ModuleCat.of A A ⟶ P.X 0),
      IsFinFreeModelU A X f U P ε :=
  Work.DSMX0U.area_MX0U_of_coherence A X f hp U hU hcov
    (cechZ_homology_finite_final (A := A) f hp U hU hcov)

example : @area_MX0U_final.{a} = @DSMap.Mix2.area_MX0U.{a} := rfl

/-- MX0bU from the clean `area_MX0bU_of_F1`, fed with F1 (proved). -/
theorem area_MX0bU_final (A : Type a) [CommRing A] (X : Scheme.{a}) (f : X ⟶ Spec (.of A))
    [IsProper f] {ι : Type a} [Finite ι] (U : ι → X.Opens) (hU : ∀ i, IsAffineOpen (U i))
    (hcov : ⨆ i, U i = ⊤) (P : CochainComplex (ModuleCat.{a} A) ℤ)
    (ε : ModuleCat.of A A ⟶ P.X 0) (hP : IsFinFreeModelU A X f U P ε)
    (h : ModSplit P ε (RingHom.id A) ⊥ 1) : DSplit.{a, b, c} A X f :=
  DSMap.Mix2.area_MX0bU_of_F1.{a, b, c} A X f U hU hcov P ε hP h (by
    intro hb hc hEn
    letI := hb
    letI := hc
    letI := hEn
    haveI : QuasiCompact f := Work.DSMX0bU.quasiCompact_of_isProper f
    exact DSMap.area_F1_cech_proved A X f U hU hcov)

example : type_of% (@area_MX0bU_final.{a, b, c}) = type_of% (@DSMap.Mix2.area_MX0bU.{a, b, c}) :=
  rfl

theorem area_M6Gpos1_final (p : ℕ) [Fact p.Prime] (A : Type a) [CommRing A] (X : Scheme.{a})
    (f : X ⟶ Spec (.of A)) (g : A) (N : ℕ) (i : X ⟶ PSpace A N) (j : Fin (N + 1))
    (F : Polynomial A)
    (θ : Γ(X, chartCover i ⟨j⟩) →+*
      Localization.Away (algebraMap A (AdjoinRoot F) ((p : A) * g)))
    (hi : IsClosedImmersion i) (hif : i ≫ PSpace.toSpec A N = f) (hF : F.Monic)
    (hFd : 0 < F.natDegree)
    (hθ : θ.comp (phiU A X f (chartCover i ⟨j⟩)) =
      (algebraMap (AdjoinRoot F) _).comp (algebraMap A (AdjoinRoot F)))
    (P : CochainComplex (ModuleCat.{a} A) ℤ) (ε : ModuleCat.of A A ⟶ P.X 0)
    (hP : IsFinFreeModelU A X f (chartCover i) P ε)
    (D : Type a) [CommRing D] (QD : PerfectoidData p D) (ψ : A →+* D) (n : ℕ)
    (hdiv : ψ g ∣ (p : D) ^ n) :
    ∀ m k, ModSplit P ε ψ (Ideal.span {(p : D) ^ m}) (QD.ϖ k) := by
  intro m k
  obtain ⟨hP1, hP2, φ, -, hφ⟩ := hP
  -- 1. André on `D` for `F`: a root `r 0 ∈ W₁`
  obtain ⟨W₁, _, _, Q₁, hQ₁, hFF₁, r, hr0, -⟩ := Work.DSFinal.m2pos1_any_final p D QD (F.map ψ) (hF.map ψ)
    (fun h => by haveI := h; rw [hF.natDegree_map ψ]; exact hFd)
  let ψ₁ : A →+* W₁ := (algebraMap D W₁).comp ψ
  have hFr : F.eval₂ ψ₁ (r 0) = 0 := by
    rw [Polynomial.aeval_def, Polynomial.eval₂_map] at hr0; exact hr0
  let L₀ : AdjoinRoot F →+* W₁ := AdjoinRoot.lift ψ₁ (r 0) hFr
  have hL₀ : ∀ x : A, L₀ (algebraMap A (AdjoinRoot F) x) = ψ₁ x := fun x => by
    rw [AdjoinRoot.algebraMap_eq]; exact AdjoinRoot.lift_of hFr
  have hu₁ : IsUnit (((algebraMap W₁ (Localization.Away (p : W₁))).comp L₀)
      (algebraMap A (AdjoinRoot F) ((p : A) * g))) := by
    rw [RingHom.comp_apply, hL₀, map_mul, map_mul, map_natCast]
    refine (IsLocalization.Away.algebraMap_isUnit _).mul ?_
    obtain ⟨y, hy⟩ := hdiv
    refine isUnit_of_dvd_unit ⟨algebraMap W₁ _ (algebraMap D W₁ y), ?_⟩
      ((IsLocalization.Away.algebraMap_isUnit (p : W₁)).pow n)
    change _ = algebraMap W₁ _ (algebraMap D W₁ (ψ g)) * _
    rw [← map_mul, ← map_mul, ← hy]
    simp
  let L₁ : Localization.Away (algebraMap A (AdjoinRoot F) ((p : A) * g)) →+*
      Localization.Away (p : W₁) := IsLocalization.Away.lift _ hu₁
  let θ₁ := L₁.comp θ
  -- 2. homogeneous coordinates `t₁ ∈ W₁` of the point, normalised `t₁ j = ϖ₀^{pe}`
  obtain ⟨e, t₀, ht₀⟩ := DSMap.Mix2.exists_chart_gens_proved p W₁ Q₁
    (fun k : ULift.{a} (Fin (N + 1)) => θ₁ (xiSec i j k.down))
  let t₁ : ULift.{a} (Fin (N + 1)) → W₁ := Function.update t₀ ⟨j⟩ (Q₁.ϖ 0 ^ (p * e))
  have ht₁j : t₁ ⟨j⟩ = Q₁.ϖ 0 ^ (p * e) := Function.update_self _ _ _
  -- 3. roots of the `t₁ k` in a second André extension `W₂`
  obtain ⟨W₂, _, _, Q₂, hQ₂, hFF₂, tr, htr0, htr⟩ := area_ROOTS_final p W₁ Q₁ t₁
  let ψ₂ : A →+* W₂ := (algebraMap W₁ W₂).comp ψ₁
  let t₂ : ULift.{a} (Fin (N + 1)) → W₂ := fun k => algebraMap W₁ W₂ (t₁ k)
  have hu₂ : IsUnit (((algebraMap W₂ (Localization.Away (p : W₂))).comp (algebraMap W₁ W₂))
      (p : W₁)) := by
    rw [RingHom.comp_apply, map_natCast]; exact IsLocalization.Away.algebraMap_isUnit _
  let L₂ : Localization.Away (p : W₁) →+* Localization.Away (p : W₂) :=
    IsLocalization.Away.lift _ hu₂
  have hL₂ : ∀ x : W₁, L₂ (algebraMap W₁ _ x) = algebraMap W₂ _ (algebraMap W₁ W₂ x) :=
    fun x => IsLocalization.Away.lift_eq _ hu₂ x
  let θ₂ := L₂.comp θ₁
  have hθ₂ : θ₂.comp (phiU A X f (chartCover i ⟨j⟩)) = (algebraMap W₂ _).comp ψ₂ := by
    ext x
    have := congrArg (fun φ => φ x) hθ
    simp only [RingHom.comp_apply] at this ⊢
    change L₂ (L₁ (θ _)) = _
    rw [this, IsLocalization.Away.lift_eq, RingHom.comp_apply, hL₀, hL₂]
    rfl
  have ht₂j : t₂ ⟨j⟩ = Q₂.ϖ 0 ^ (p * e) := by
    change algebraMap W₁ W₂ (t₁ ⟨j⟩) = _; rw [ht₁j, map_pow, hQ₂]
  have hθ₂k : ∀ k, k ≠ j → algebraMap W₂ (Localization.Away (p : W₂)) (t₂ ⟨k⟩) =
      algebraMap W₂ _ (t₂ ⟨j⟩) * θ₂ (xiSec i j k) := by
    intro k hk
    have hne : (⟨k⟩ : ULift.{a} (Fin (N + 1))) ≠ ⟨j⟩ := fun h => hk (congrArg ULift.down h)
    have h1 : t₁ ⟨k⟩ = t₀ ⟨k⟩ := Function.update_of_ne hne _ _
    change algebraMap W₂ _ (algebraMap W₁ W₂ (t₁ ⟨k⟩)) =
      algebraMap W₂ _ (algebraMap W₁ W₂ (t₁ ⟨j⟩)) * L₂ (θ₁ (xiSec i j k))
    rw [← hL₂, ← hL₂, ← map_mul, h1, ht₁j, ht₀ ⟨k⟩]
  -- 4. the chart chain map (SEC) and blowup almost splitting (M5d) over `W₂`
  obtain ⟨χ, hχ⟩ := DSMap.Mix2.area_SEC_proved p A X f N i hi hif j W₂ Q₂.torsionFree ψ₂ θ₂ hθ₂ t₂
    (by rw [ht₂j]; exact isUnit_varpi_pow p Q₂ _) hθ₂k
  have h5 := area_M5d_final p W₂ Q₂ t₂ tr htr0 htr ⟨j⟩ (p * e) ht₂j ψ₂ P hP1 ε hP2 (φ ≫ χ) (by
    have hφ' : ε ≫ φ.f 0 = coaug0 A X f (chartCover i) ≫
        ((cech A X f (chartCover i)).extendXIso ComplexShape.embeddingUpNat (i := 0) rfl).inv := by
      apply (Iso.eq_comp_inv _).2
      exact (Category.assoc _ _ _).trans hφ
    rw [HomologicalComplex.comp_f, Category.assoc, ← Category.assoc ε, hφ']
    exact (Category.assoc _ _ _).trans hχ) m k
  -- 5. descend `W₂ → W₁ → D` (AM2 + FFP)
  have h6 : ModSplit P ε ψ₁ (Ideal.span {(p : W₁) ^ m}) (Q₁.ϖ k) := by
    refine modSplit_descent_p_final p P hP1 ε hP2 ψ₁ Q₁.torsionFree Q₂.torsionFree hFF₂ m _ ?_
    rw [← hQ₂]; exact h5
  refine modSplit_descent_p_final p P hP1 ε hP2 ψ QD.torsionFree Q₁.torsionFree hFF₁ m _ ?_
  rw [← hQ₁]; exact h6

example : @area_M6Gpos1_final.{a} = @DSMap.Gaps.area_M6Gpos1.{a} := rfl

theorem area_MIX2pos1_final (A : Type a) [CommRing A] [IsRegularLocalRing A]
    [IsAdicComplete (maximalIdeal A) A] [IsAlgClosed (ResidueField A)] (p : ℕ) [Fact p.Prime]
    [CharZero A] [CharP (ResidueField A) p] (X : Scheme.{a}) [IsIntegral X]
    (f : X ⟶ Spec (.of A)) [IsProper f] (hs : Function.Surjective f) (hg : IsGenFinite A f)
    (hp : IsProjOver A f) :
    DSplit.{a, b, c} A X f := by
  have : IsDomain A := DSMap.area_REG_proved A
  obtain ⟨g, N, i, j, F, θ, hgp, hi, hif, hF, hFd, hθ⟩ := Work.DSM8m2.area_M8mpos A p X f hs hg hp
  obtain ⟨P, ε, hP⟩ := area_MX0U_final A X f hp (chartCover i) (DSMap.Mix2.chartCover_affine_proved i hi)
    (DSMap.Mix2.chartCover_iSup_proved i)
  refine area_MX0bU_final A X f (chartCover i) (DSMap.Mix2.chartCover_affine_proved i hi) (DSMap.Mix2.chartCover_iSup_proved i) P ε hP ?_
  obtain ⟨B₁, _, _, P₁, hFF₁⟩ := Work.DSM1p.area_M1'_proved A p
  obtain ⟨B₂, _, _, Q₂, -, hFF₁₂, r, hr0, hr⟩ := Work.DSFinal.m2pos1_any_final p B₁ P₁
    (Polynomial.X - Polynomial.C (algebraMap A B₁ g)) (Polynomial.monic_X_sub_C _)
    (fun h => by haveI := h; rw [Polynomial.natDegree_X_sub_C]; exact Nat.one_pos)
  let _ : Algebra A B₂ := ((algebraMap B₁ B₂).comp (algebraMap A B₁)).toAlgebra
  have : IsScalarTower A B₁ B₂ := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have : Module.FaithfullyFlat A B₂ := DSMap.Mix.area_M2b_proved A p B₁ B₂ Q₂ hFF₁₂
  have hr0' : r 0 = algebraMap A B₂ g := by
    simp only [map_sub, Polynomial.aeval_X, Polynomial.aeval_C, sub_eq_zero] at hr0
    rw [hr0]; rfl
  obtain ⟨D, _, _, QD, tr, hQD, hdiv, hq⟩ := DSMap.Mix2.area_M4p_proved p B₂ Q₂ r hr
  refine DSMap.Mix2.area_M7p_proved A p P ε hP.1 hP.2.1 B₂ Q₂ g hgp r hr0' hr D QD tr hQD hq ?_
  intro n m k
  refine area_M6Gpos1_final p A X f g N i j F θ hi hif hF hFd hθ P ε hP (D n) (QD n) _ n ?_ m k
  obtain ⟨y, hy⟩ := hdiv n
  refine ⟨y, ?_⟩
  rw [← hy, RingHom.comp_apply, ← hr0']

example : type_of% (@area_MIX2pos1_final.{a, b, c}) = type_of% (@DSMap.area_MIX.{a, b, c}) := rfl

end Work.DSFinal
