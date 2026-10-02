import Mathlib
import Submission.Work.ThomBordism.punctBallIncl_bijective
import Submission.Work.ThomBordism.ambientLocalDefs
import Submission.Work.ThomBordism.ambientLocalDefs2
import Submission.Work.ThomBordism.localChartBallDefs
import Submission.Work.ThomBordism.localChartClass_ne_zero
import Submission.Work.ThomBordism.stdModelGen_pm_stdThomGen
import Submission.Work.Serre.isIso_relCohMap_excision_of_interior
import Submission.Work.Tubular.Defs
import Submission.Work.Cohomology.localCohomology

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

/-!
# The chart model class generates the *local* cohomology of the normal bundle at `0_x`

`Work.ThomBordism.chartModelClass_locSpan` is the "local half" of
`Work.ThomBordism.chartModelClass_span_top`: whereas the latter asks for the class
`Θ^*(stdModelGen (8+k))` (with `Θ = chartAffine E x ∘ cap E ε`) to generate the relative cohomology
`H^{8+k}(ν, ν∖0)` of the *whole* normal bundle, the statement here asks the same only of the
*local* pair `(ν, ν∖{0_x})` at the base point `0_x = zeroSectionNormal E x`.

The proof is a direct consequence of the geometry already on disk
(`Work.ThomBordism.localChartClass_pairHomeo`): on the open disc bundle
`V := {p | normalNorm E p < ε}` the capping is the identity and `Θ` restricts to a *homeomorphism of
pairs* `Φ : (V, V∖0_x) ≅ (V₀, V₀∖0)` onto the chart neighbourhood `V₀ = chartNbhd E C x` of `0`.
Hence

* `Φ^*(ι^*(stdModelGen))` generates `H^{8+k}(V, V∖0_x)` — the pullback along a homeomorphism of
  pairs of a generator is a generator, and `ι^*(stdModelGen)` generates `H^{8+k}(V₀, V₀∖0)`
  because `ι` (the inclusion of the chart neighbourhood) is an *excision* isomorphism and
  `stdModelGen` generates `H^{8+k}(ℝ^{8+k}, ℝ^{8+k}∖0)`;
* functoriality identifies `Φ^*(ι^*(stdModelGen))` with the image of `Θ^*(stdModelGen)` under the
  pullback along the inclusion `V ↪ ν`;
* and that inclusion is again an excision isomorphism
  (`Work.Serre.isIso_relCohMap_excision_of_interior`, since `(ν∖0_x) ∪ V = ν` and both are open),
  so it is injective: a class whose image generates generates.
-/

namespace Work.ThomBordism

noncomputable section

open CategoryTheory

variable {V : Work.ThomBordism.Man8} {k : ℕ}

/-- The norm of the zero-section point at `x` is zero. -/
theorem normalNorm_zeroSectionNormal
    (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k)) (x : V.pt) :
    Work.Tubular.normalNorm E (Work.Tubular.zeroSectionNormal E x) = 0 := by
  rw [Work.Tubular.zeroSectionNormal_apply]
  simp [Work.Tubular.normalNorm]

/-- **Two generators that are related by an injective linear map.**  If `f x` generates and `f` is
injective, then `x` generates. -/
theorem span_singleton_eq_top_of_injective {M N : Type*} [AddCommGroup M] [Module ℤ M]
    [AddCommGroup N] [Module ℤ N] (f : M →ₗ[ℤ] N) (hf : Function.Injective f) {x : M}
    (hx : Submodule.span ℤ ({f x} : Set N) = ⊤) : Submodule.span ℤ ({x} : Set M) = ⊤ := by
  have key : ∀ y : M, y ∈ Submodule.span ℤ ({x} : Set M) := by
    intro y
    have h1 : Submodule.map f (Submodule.span ℤ ({x} : Set M))
        = Submodule.span ℤ ({f x} : Set N) := by
      rw [Submodule.map_span]
      simp
    have hy : f y ∈ Submodule.map f (Submodule.span ℤ ({x} : Set M)) := by
      rw [h1, hx]
      exact Submodule.mem_top
    obtain ⟨z, hz, hfz⟩ := Submodule.mem_map.mp hy
    rwa [hf hfz] at hz
  exact Submodule.eq_top_iff'.mpr key

theorem chartModelClass_locSpan {V : Work.ThomBordism.Man8} [ConnectedSpace V.pt] {k : ℕ}
    (hk : 1 ≤ k)
    (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k)) {ε : ℝ}
    (C : Work.Tubular.TubeChart E ε) (x : V.pt)
    (hcont : Continuous fun p : Work.Tubular.NormalTotal E =>
      Work.ThomBordism.chartAffine E x (Work.ThomBordism.cap E ε p))
    (hmem : ∀ p ∈ {p : Work.Tubular.NormalTotal E | p ≠ Work.Tubular.zeroSectionNormal E x},
      Work.ThomBordism.chartAffine E x (Work.ThomBordism.cap E ε p) ∈
        ({0}ᶜ : Set (Work.Tubular.Euc (8 + k)))) :
    Submodule.span ℤ
      ({((Work.Thom.relCohMap
          ⟨fun p : Work.Tubular.NormalTotal E =>
            Work.ThomBordism.chartAffine E x (Work.ThomBordism.cap E ε p), hcont⟩
          {p : Work.Tubular.NormalTotal E | p ≠ Work.Tubular.zeroSectionNormal E x}
          ({0}ᶜ : Set (Work.Tubular.Euc (8 + k))) hmem ℤ (8 + k)).hom
        (Work.ThomBordism.stdModelGen (8 + k)))} : Set
        (Work.Thom.RelCoh ℤ (8 + k) (TopCat.of (Work.Tubular.NormalTotal E))
          {p : Work.Tubular.NormalTotal E | p ≠ Work.Tubular.zeroSectionNormal E x})) = ⊤ := by
  classical
  let Θ : C(Work.Tubular.NormalTotal E, Work.Tubular.Euc (8 + k)) :=
    ⟨fun p => Work.ThomBordism.chartAffine E x (Work.ThomBordism.cap E ε p), hcont⟩
  let P : Set (Work.Tubular.NormalTotal E) := {p | p ≠ Work.Tubular.zeroSectionNormal E x}
  -- the geometry: the capped chart map is a homeomorphism of pairs on the open disc bundle
  obtain ⟨Φ, hVopen, h0V, hΦval, hpair⟩ :=
    Work.ThomBordism.localChartClass_pairHomeo E C x hcont
      (fun p hp => Set.mem_compl_singleton_iff.mp (hmem p hp))
  let ι : C(↥(Work.ThomBordism.chartOpenBall E ε), Work.Tubular.NormalTotal E) :=
    ⟨Subtype.val, continuous_subtype_val⟩
  let AU : Set ↥(Work.ThomBordism.chartOpenBall E ε) :=
    {p | (p : Work.Tubular.NormalTotal E) ∈ P}
  let incl0 : C(↥(Work.ThomBordism.chartNbhd E C x), Work.Tubular.Euc (8 + k)) :=
    ⟨Subtype.val, continuous_subtype_val⟩
  let Vpunct : Set ↥(Work.ThomBordism.chartNbhd E C x) :=
    {y | (y : Work.Tubular.Euc (8 + k)) ∈ ({0}ᶜ : Set (Work.Tubular.Euc (8 + k)))}
  have hAU : ∀ p ∈ AU, ι p ∈ P := fun p hp => hp
  have hB : ∀ y ∈ Vpunct, incl0 y ∈ ({0}ᶜ : Set (Work.Tubular.Euc (8 + k))) := fun y hy => hy
  have hΘι : ∀ p ∈ AU, Θ (ι p) ∈ ({0}ᶜ : Set (Work.Tubular.Euc (8 + k))) :=
    fun p hp => hmem (ι p) (hAU p hp)
  have he : ∀ p : ↥(Work.ThomBordism.chartOpenBall E ε),
      p ∈ AU ↔ (Φ : C(↥(Work.ThomBordism.chartOpenBall E ε),
        ↥(Work.ThomBordism.chartNbhd E C x))) p ∈ Vpunct := fun p => hpair p
  have hΦ : ∀ p ∈ AU, (Φ : C(↥(Work.ThomBordism.chartOpenBall E ε),
      ↥(Work.ThomBordism.chartNbhd E C x))) p ∈ Vpunct := fun p hp => (hpair p).mp hp
  have hΦ0 : ∀ p ∈ AU, (incl0.comp (Φ : C(↥(Work.ThomBordism.chartOpenBall E ε),
      ↥(Work.ThomBordism.chartNbhd E C x)))) p ∈ ({0}ᶜ : Set (Work.Tubular.Euc (8 + k))) :=
    fun p hp => hB _ (hΦ p hp)
  -- the pullback along a homeomorphism of pairs is bijective
  have hBijΦ : Function.Bijective (Work.Thom.relCohMap
      (Φ : C(↥(Work.ThomBordism.chartOpenBall E ε), ↥(Work.ThomBordism.chartNbhd E C x)))
      AU Vpunct hΦ ℤ (8 + k)).hom :=
    Work.Thom.bijective_relCohMap_of_homeomorphA AU Vpunct Φ he ℤ (8 + k)
  -- excision on the chart neighbourhood of `0`
  have hExcision0 : CategoryTheory.IsIso (Work.Thom.relCohMap incl0 Vpunct
      ({0}ᶜ : Set (Work.Tubular.Euc (8 + k))) hB ℤ (8 + k)) := by
    have hcov0 : interior ({0}ᶜ : Set (Work.Tubular.Euc (8 + k)))
        ∪ interior (Work.ThomBordism.chartNbhd E C x) = Set.univ := by
      rw [isOpen_compl_singleton.interior_eq, hVopen.interior_eq]
      apply Set.eq_univ_iff_forall.mpr
      intro y
      by_cases hy : y = 0
      · subst hy; exact Or.inr h0V
      · exact Or.inl hy
    exact Work.Serre.isIso_relCohMap_excision_of_interior ℤ
      ({0}ᶜ : Set (Work.Tubular.Euc (8 + k))) (Work.ThomBordism.chartNbhd E C x) hcov0 (8 + k)
  have hsurj0 : Function.Surjective (Work.Thom.relCohMap incl0 Vpunct
      ({0}ᶜ : Set (Work.Tubular.Euc (8 + k))) hB ℤ (8 + k)).hom :=
    ((CategoryTheory.ConcreteCategory.isIso_iff_bijective _).mp hExcision0).2
  -- the pullback of `stdModelGen` to the chart neighbourhood generates
  have hgen0 : Submodule.span ℤ ({((Work.Thom.relCohMap incl0 Vpunct
      ({0}ᶜ : Set (Work.Tubular.Euc (8 + k))) hB ℤ (8 + k)).hom
        (Work.ThomBordism.stdModelGen (8 + k)))} : Set (Work.Thom.RelCoh ℤ (8 + k)
          ↥(Work.ThomBordism.chartNbhd E C x) Vpunct)) = ⊤ :=
    Work.Tubular.span_singleton_map_eq_top
      (Work.Thom.relCohMap incl0 Vpunct ({0}ᶜ : Set (Work.Tubular.Euc (8 + k))) hB ℤ (8 + k)).hom
      hsurj0 (Work.ThomBordism.stdModelGen (8 + k))
      (Work.ThomBordism.stdModelGen_span (8 + k) (by omega))
  -- hence so does its image under the homeomorphism
  have hgen1 : Submodule.span ℤ ({((Work.Thom.relCohMap
      (Φ : C(↥(Work.ThomBordism.chartOpenBall E ε), ↥(Work.ThomBordism.chartNbhd E C x)))
      AU Vpunct hΦ ℤ (8 + k)).hom ((Work.Thom.relCohMap incl0 Vpunct
        ({0}ᶜ : Set (Work.Tubular.Euc (8 + k))) hB ℤ (8 + k)).hom
        (Work.ThomBordism.stdModelGen (8 + k))))} : Set (Work.Thom.RelCoh ℤ (8 + k)
          ↥(Work.ThomBordism.chartOpenBall E ε) AU)) = ⊤ :=
    Work.Tubular.span_singleton_map_eq_top
      (Work.Thom.relCohMap (Φ : C(↥(Work.ThomBordism.chartOpenBall E ε),
        ↥(Work.ThomBordism.chartNbhd E C x))) AU Vpunct hΦ ℤ (8 + k)).hom hBijΦ.2
      ((Work.Thom.relCohMap incl0 Vpunct ({0}ᶜ : Set (Work.Tubular.Euc (8 + k))) hB
        ℤ (8 + k)).hom (Work.ThomBordism.stdModelGen (8 + k))) hgen0
  -- functoriality: the two composites with the chart map agree
  have hcomp1 := Work.Thom.relCohMap_compA AU P ({0}ᶜ : Set (Work.Tubular.Euc (8 + k)))
    ι Θ hAU hmem hΘι ℤ (8 + k)
  have hcomp2 := Work.Thom.relCohMap_compA AU Vpunct ({0}ᶜ : Set (Work.Tubular.Euc (8 + k)))
    (Φ : C(↥(Work.ThomBordism.chartOpenBall E ε), ↥(Work.ThomBordism.chartNbhd E C x))) incl0
    hΦ hB hΦ0 ℤ (8 + k)
  have hmap : incl0.comp (Φ : C(↥(Work.ThomBordism.chartOpenBall E ε),
      ↥(Work.ThomBordism.chartNbhd E C x))) = Θ.comp ι := by
    apply ContinuousMap.ext
    intro p
    rw [ContinuousMap.comp_apply, ContinuousMap.comp_apply]
    exact hΦval p
  have hC := Work.Thom.relCohMap_congrA AU ({0}ᶜ : Set (Work.Tubular.Euc (8 + k)))
    hmap hΦ0 hΘι ℤ (8 + k)
  -- the image of `Θ^* stdModelGen` under `ι^*` is `Φ^*(ι^* stdModelGen)`
  have hkey : (Work.Thom.relCohMap ι AU P hAU ℤ (8 + k)).hom
        ((Work.Thom.relCohMap Θ P ({0}ᶜ : Set (Work.Tubular.Euc (8 + k))) hmem
          ℤ (8 + k)).hom (Work.ThomBordism.stdModelGen (8 + k)))
      = (Work.Thom.relCohMap (Φ : C(↥(Work.ThomBordism.chartOpenBall E ε),
            ↥(Work.ThomBordism.chartNbhd E C x))) AU Vpunct hΦ ℤ (8 + k)).hom
        ((Work.Thom.relCohMap incl0 Vpunct ({0}ᶜ : Set (Work.Tubular.Euc (8 + k))) hB
          ℤ (8 + k)).hom (Work.ThomBordism.stdModelGen (8 + k))) := by
    have h1 : (Work.Thom.relCohMap ι AU P hAU ℤ (8 + k)).hom
        ((Work.Thom.relCohMap Θ P ({0}ᶜ : Set (Work.Tubular.Euc (8 + k))) hmem
          ℤ (8 + k)).hom (Work.ThomBordism.stdModelGen (8 + k)))
        = (Work.Thom.relCohMap (Θ.comp ι) AU ({0}ᶜ : Set (Work.Tubular.Euc (8 + k)))
          hΘι ℤ (8 + k)).hom (Work.ThomBordism.stdModelGen (8 + k)) := by
      have h := congrArg ModuleCat.Hom.hom hcomp1
      rw [ModuleCat.hom_comp] at h
      exact LinearMap.congr_fun h _
    have h2 : (Work.Thom.relCohMap (Φ : C(↥(Work.ThomBordism.chartOpenBall E ε),
            ↥(Work.ThomBordism.chartNbhd E C x))) AU Vpunct hΦ ℤ (8 + k)).hom
        ((Work.Thom.relCohMap incl0 Vpunct ({0}ᶜ : Set (Work.Tubular.Euc (8 + k))) hB
          ℤ (8 + k)).hom (Work.ThomBordism.stdModelGen (8 + k)))
        = (Work.Thom.relCohMap (incl0.comp (Φ : C(↥(Work.ThomBordism.chartOpenBall E ε),
            ↥(Work.ThomBordism.chartNbhd E C x)))) AU
            ({0}ᶜ : Set (Work.Tubular.Euc (8 + k))) hΦ0 ℤ (8 + k)).hom
          (Work.ThomBordism.stdModelGen (8 + k)) := by
      have h := congrArg ModuleCat.Hom.hom hcomp2
      rw [ModuleCat.hom_comp] at h
      exact LinearMap.congr_fun h _
    rw [h1, h2, hC]
  -- excision on the pair `(ν, ν∖0_x)` at the open disc bundle
  have hVopen' : IsOpen (Work.ThomBordism.chartOpenBall E ε) := by
    change IsOpen {p : Work.Tubular.NormalTotal E | Work.Tubular.normalNorm E p < ε}
    exact isOpen_lt (Work.Tubular.continuous_normalNorm E) continuous_const
  have hPopen : IsOpen P := by
    change IsOpen ({Work.Tubular.zeroSectionNormal E x} : Set (Work.Tubular.NormalTotal E))ᶜ
    exact isOpen_compl_singleton
  have hcov : interior P ∪ interior (Work.ThomBordism.chartOpenBall E ε) = Set.univ := by
    rw [hPopen.interior_eq, hVopen'.interior_eq]
    apply Set.eq_univ_iff_forall.mpr
    intro p
    by_cases hp : p ∈ P
    · exact Or.inl hp
    · right
      rw [Work.ThomBordism.mem_chartOpenBall]
      have hz : p = Work.Tubular.zeroSectionNormal E x := by
        by_contra h
        exact hp h
      rw [hz, normalNorm_zeroSectionNormal]
      exact C.eps_pos
  have hExcision : CategoryTheory.IsIso (Work.Thom.relCohMap ι AU P hAU ℤ (8 + k)) :=
    Work.Serre.isIso_relCohMap_excision_of_interior ℤ P
      (Work.ThomBordism.chartOpenBall E ε) hcov (8 + k)
  have hinj : Function.Injective (Work.Thom.relCohMap ι AU P hAU ℤ (8 + k)).hom :=
    ((CategoryTheory.ConcreteCategory.isIso_iff_bijective _).mp hExcision).1
  -- the image of `Θ^* stdModelGen` generates, hence so does `Θ^* stdModelGen`
  have hgenV : Submodule.span ℤ ({((Work.Thom.relCohMap ι AU P hAU ℤ (8 + k)).hom
      ((Work.Thom.relCohMap Θ P ({0}ᶜ : Set (Work.Tubular.Euc (8 + k))) hmem ℤ (8 + k)).hom
        (Work.ThomBordism.stdModelGen (8 + k))))} : Set (Work.Thom.RelCoh ℤ (8 + k)
          ↥(Work.ThomBordism.chartOpenBall E ε) AU)) = ⊤ := by
    rw [hkey]
    exact hgen1
  exact span_singleton_eq_top_of_injective
    (Work.Thom.relCohMap ι AU P hAU ℤ (8 + k)).hom hinj hgenV

end

end Work.ThomBordism
