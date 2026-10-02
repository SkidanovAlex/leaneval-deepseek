import Mathlib
import Submission.Work.ThomBordism.valuePmOneV2Defs
import Submission.Work.ThomBordism.chartNbhd_pairHomeo
import Submission.Work.ThomBordism.chartModelClass_ne_zero
import Submission.Work.ThomBordism.stdModelGen_pm_stdThomGen
import Submission.Work.Serre.isIso_relCohMap_excision_of_interior
import Submission.Work.Thom.ATools
import Submission.Work.Tubular.ThomRepOfLocalDegree

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false

/-!
# The pullback of the standard model generator to the point pair of the tube

The target `Work.ThomBordism.tubeTrans_modelSpan` says that the pullback of the standard model
generator `stdModelGen (8+k)` along the translation `y ↦ y - E.e x` generates the relative
cohomology `H^{8+k}(C.U, C.U ∖ {E.e x}; ℤ)` of the pair (closed tube, complement of the point).

The proof routes through the chart model class: the tube is the image of the closed disc bundle of
the normal bundle under the tubular map `tubeMap` (a homeomorphism of pairs), and on the disc bundle
the capped chart map `p ↦ chartAffine E x (cap E ε p)` is the translation composed with `tubeMap`.
That class generates `H^{8+k}(ν, ν∖{0_x})` (`Work.ThomBordism.chartModelClass_locSpan`, here in the
form `cappedChartLocSpan`, without the connectedness hypothesis), and excision transfers the
statement down to the closed disc bundle.
-/

namespace Work.ThomBordism

noncomputable section

open CategoryTheory

variable {V : Work.ThomBordism.Man8} {k : ℕ}

/-! ## A general lemma about generators -/

/-- **A generator survives an injective linear map.**  If `f x` generates and `f` is injective then
`x` generates. -/
theorem ttm_span_singleton_eq_top_of_injective {M N : Type*} [AddCommGroup M] [Module ℤ M]
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

/-! ## Continuity of the capping and of the capped chart map -/

theorem ttm_continuous_radialRescale_fun
    (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k)) (φ : ℝ → ℝ)
    (hφ : Continuous φ) :
    Continuous fun p : Work.Tubular.NormalTotal E =>
      ((p : V.pt × Work.Tubular.Euc (8 + k)).1,
        φ (Work.Tubular.normalNorm E p) • (p : V.pt × Work.Tubular.Euc (8 + k)).2) :=
  Continuous.prodMk (Work.Tubular.NormalTotal.continuous_proj E)
    ((hφ.comp (Work.Tubular.continuous_normalNorm E)).smul continuous_subtype_val.snd)

theorem ttm_continuous_radialRescale
    (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k)) (φ : ℝ → ℝ)
    (hφ : Continuous φ) : Continuous (Work.ThomBordism.radialRescale E φ) :=
  (continuous_induced_rng (f := (Subtype.val :
      Work.Tubular.NormalTotal E → V.pt × Work.Tubular.Euc (8 + k)))
    (g := Work.ThomBordism.radialRescale E φ)).mpr
    (ttm_continuous_radialRescale_fun E φ hφ)

theorem ttm_continuous_cap (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k))
    {ε : ℝ} (hε : 0 < ε) : Continuous (Work.ThomBordism.cap E ε) :=
  ttm_continuous_radialRescale E (Work.ThomBordism.capCoeff ε)
    (Work.ThomBordism.continuous_capCoeff hε)

theorem ttm_continuous_chartAffine (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k))
    (x : V.pt) : Continuous (Work.ThomBordism.chartAffine E x) := by
  have h1 : Continuous fun p : Work.Tubular.NormalTotal E =>
      (p : V.pt × Work.Tubular.Euc (8 + k)) := continuous_subtype_val
  have h2 : Continuous fun p : Work.Tubular.NormalTotal E =>
      E.e ((p : V.pt × Work.Tubular.Euc (8 + k)).1) :=
    E.smooth.continuous.comp (continuous_fst.comp h1)
  have h3 : Continuous fun p : Work.Tubular.NormalTotal E =>
      (p : V.pt × Work.Tubular.Euc (8 + k)).2 := continuous_snd.comp h1
  have h4 : Work.ThomBordism.chartAffine E x = fun p : Work.Tubular.NormalTotal E =>
      E.e ((p : V.pt × Work.Tubular.Euc (8 + k)).1)
        + (p : V.pt × Work.Tubular.Euc (8 + k)).2 - E.e x := by
    funext p; rw [Work.ThomBordism.chartAffine_apply]
  rw [h4]
  exact (h2.add h3).sub continuous_const

theorem ttm_continuous_chartAffine_cap
    (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k)) {ε : ℝ}
    (C : Work.Tubular.TubeChart E ε) (x : V.pt) :
    Continuous fun p : Work.Tubular.NormalTotal E =>
      Work.ThomBordism.chartAffine E x (Work.ThomBordism.cap E ε p) :=
  (ttm_continuous_chartAffine E x).comp (ttm_continuous_cap E C.eps_pos)

/-- The norm of the zero-section point at `x` is zero. -/
theorem ttm_normalNorm_zeroSectionNormal
    (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k)) (x : V.pt) :
    Work.Tubular.normalNorm E (Work.Tubular.zeroSectionNormal E x) = 0 := by
  rw [Work.Tubular.zeroSectionNormal]
  simp

/-! ## The capped chart class generates the local relative group at `0_x` -/

/-- **The capped chart class generates the local relative cohomology `H^{8+k}(ν, ν∖{0_x})`.**

This is `Work.ThomBordism.chartModelClass_locSpan` without the (unused) connectedness hypothesis and
without the superfluous `1 ≤ k`; the proof is the same, with
`Work.ThomBordism.chartNbhd_pairHomeo` supplying the homeomorphism of pairs (so that the extra
hypothesis `hcap` of `localChartClass_pairHomeo` is not needed). -/
theorem cappedChartLocSpan {V : Work.ThomBordism.Man8} {k : ℕ}
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
    Work.ThomBordism.chartNbhd_pairHomeo E C x hcont
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
      rw [hz, ttm_normalNorm_zeroSectionNormal]
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
  exact ttm_span_singleton_eq_top_of_injective
    (Work.Thom.relCohMap ι AU P hAU ℤ (8 + k)).hom hinj hgenV

/-! ## The tubular map on the closed disc bundle, as a homeomorphism of pairs -/

/-- **The tubular map identifies the closed disc bundle with the closed tube**, with inverse the
tube inverse: a homeomorphism of `NormalDiscSub E ε` with `↥C.U`. -/
noncomputable def ttm_discTubeHomeo
    (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k)) {ε : ℝ}
    (C : Work.Tubular.TubeChart E ε) : Work.Tubular.NormalDiscSub E ε ≃ₜ ↥C.U where
  toFun p := ⟨Work.Tubular.tubeMap E (p : Work.Tubular.NormalTotal E), C.mem_U _ p.2⟩
  invFun y := ⟨C.inv (y : Work.Tubular.Euc (8 + k)), C.inv_mem _ y.2⟩
  left_inv p := Subtype.ext (C.inv_tubeMap (p : Work.Tubular.NormalTotal E) p.2)
  right_inv y := Subtype.ext (C.tubeMap_inv (y : Work.Tubular.Euc (8 + k)) y.2)
  continuous_toFun :=
    ((Work.Tubular.continuous_tubeMap E).comp continuous_subtype_val).subtype_mk
      (fun p => C.mem_U _ p.2)
  continuous_invFun :=
    (C.continuousOn_inv.comp_continuous continuous_subtype_val (fun y => y.2)).subtype_mk
      (fun y => C.inv_mem _ y.2)

/-- **The homeomorphism of pairs**: `ttm_discTubeHomeo` carries the punctured closed disc bundle to
the punctured tube `tubePtSet`. -/
theorem ttm_discTubeHomeo_pair
    (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k)) {ε : ℝ}
    (C : Work.Tubular.TubeChart E ε) (x : V.pt) :
    ∀ p : Work.Tubular.NormalDiscSub E ε,
      ((p : Work.Tubular.NormalTotal E) ≠ Work.Tubular.zeroSectionNormal E x)
        ↔ (ttm_discTubeHomeo E C p : ↥C.U) ∈ tubePtSet E C x := by
  intro p
  have hcoe : ((ttm_discTubeHomeo E C p : ↥C.U) : Work.Tubular.Euc (8 + k))
      = Work.Tubular.tubeMap E (p : Work.Tubular.NormalTotal E) := rfl
  rw [mem_tubePtSet, hcoe]
  constructor
  · intro hp hmap
    have hzero : Work.Tubular.normalNorm E (Work.Tubular.zeroSectionNormal E x) = 0 :=
      ttm_normalNorm_zeroSectionNormal E x
    have hle0 : Work.Tubular.normalNorm E (Work.Tubular.zeroSectionNormal E x) ≤ ε := by
      rw [hzero]; exact C.eps_pos.le
    refine hp ?_
    have h2 : (p : Work.Tubular.NormalTotal E)
        = C.inv (Work.Tubular.tubeMap E (p : Work.Tubular.NormalTotal E)) :=
      (C.inv_tubeMap (p : Work.Tubular.NormalTotal E) p.2).symm
    have h3 : C.inv (Work.Tubular.tubeMap E (p : Work.Tubular.NormalTotal E))
        = C.inv (E.e x) := by rw [hmap]
    have h4 : C.inv (E.e x)
        = C.inv (Work.Tubular.tubeMap E (Work.Tubular.zeroSectionNormal E x)) := by
      rw [tubeMap_zeroSectionNormal E x]
    have h5 : C.inv (Work.Tubular.tubeMap E (Work.Tubular.zeroSectionNormal E x))
        = Work.Tubular.zeroSectionNormal E x :=
      C.inv_tubeMap (Work.Tubular.zeroSectionNormal E x) hle0
    rw [h2, h3, h4, h5]
  · intro hmap hp
    exact hmap (by rw [hp]; exact tubeMap_zeroSectionNormal E x)

/-! ## The target -/

theorem tubeTrans_modelSpan {V : Work.ThomBordism.Man8} {k : ℕ}
    (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k)) {ε : ℝ}
    (C : Work.Tubular.TubeChart E ε) (x : V.pt) :
    Submodule.span ℤ
      ({ ((Work.Thom.relCohMap (Work.ThomBordism.tubeTransMap E C x)
            (Work.ThomBordism.tubePtSet E C x)
            ({0}ᶜ : Set (Work.Tubular.Euc (8 + k))) (Work.ThomBordism.tubeTransMap_mem E C x)
            ℤ (8 + k)).hom (Work.ThomBordism.stdModelGen (8 + k))) } :
        Set (Work.Thom.RelCoh ℤ (8 + k) (TopCat.of ↥C.U) (Work.ThomBordism.tubePtSet E C x))) = ⊤ := by
  classical
  -- the capped chart map and its pair condition
  let hcont : Continuous fun p : Work.Tubular.NormalTotal E =>
      Work.ThomBordism.chartAffine E x (Work.ThomBordism.cap E ε p) :=
    ttm_continuous_chartAffine_cap E C x
  let Θ : C(Work.Tubular.NormalTotal E, Work.Tubular.Euc (8 + k)) :=
    ⟨fun p => Work.ThomBordism.chartAffine E x (Work.ThomBordism.cap E ε p), hcont⟩
  let P : Set (Work.Tubular.NormalTotal E) := {p | p ≠ Work.Tubular.zeroSectionNormal E x}
  have hmemΘ : ∀ p ∈ P, Θ p ∈ ({0}ᶜ : Set (Work.Tubular.Euc (8 + k))) :=
    fun p hp => Set.mem_compl_singleton_iff.mpr
      (chartAffine_cap_ne_zero_of_ne_zeroSection' E C x hp)
  -- the ν-side class and its generating property (the local model computation)
  let τ : Work.Thom.RelCoh ℤ (8 + k) (TopCat.of (Work.Tubular.NormalTotal E)) P :=
    (Work.Thom.relCohMap Θ P ({0}ᶜ : Set (Work.Tubular.Euc (8 + k))) hmemΘ ℤ (8 + k)).hom
      (Work.ThomBordism.stdModelGen (8 + k))
  have hspanτ : Submodule.span ℤ ({τ} : Set (Work.Thom.RelCoh ℤ (8 + k)
      (TopCat.of (Work.Tubular.NormalTotal E)) P)) = ⊤ :=
    cappedChartLocSpan E C x hcont hmemΘ
  -- the disc bundle and the excision
  let Ds : Set (Work.Tubular.NormalTotal E) := Work.Tubular.normalClosedDiscSet E ε
  let iE : C(↥Ds, Work.Tubular.NormalTotal E) := ⟨Subtype.val, continuous_subtype_val⟩
  let A1 : Set ↥Ds := {p | (p : Work.Tubular.NormalTotal E) ∈ P}
  have hiE : ∀ p ∈ A1, iE p ∈ P := fun p hp => hp
  have hPopen : IsOpen P := by
    change IsOpen ({Work.Tubular.zeroSectionNormal E x} : Set (Work.Tubular.NormalTotal E))ᶜ
    exact isOpen_compl_singleton
  have hDint : Work.Tubular.normalDiscSet E ε ⊆ interior Ds :=
    interior_maximal Work.Tubular.normalDiscSet_subset_closedDiscSet
      (isOpen_lt (Work.Tubular.continuous_normalNorm E) continuous_const)
  have hcov : interior P ∪ interior Ds = Set.univ := by
    rw [hPopen.interior_eq]
    apply Set.eq_univ_iff_forall.mpr
    intro p
    by_cases hp : p ∈ P
    · exact Or.inl hp
    · refine Or.inr (hDint ?_)
      rw [Work.Tubular.mem_normalDiscSet]
      have hz : p = Work.Tubular.zeroSectionNormal E x := by
        by_contra h
        exact hp h
      rw [hz, ttm_normalNorm_zeroSectionNormal]
      exact C.eps_pos
  have hExcisionD : CategoryTheory.IsIso (Work.Thom.relCohMap iE A1 P hiE ℤ (8 + k)) :=
    Work.Serre.isIso_relCohMap_excision_of_interior ℤ P Ds hcov (8 + k)
  have hsurjD : Function.Surjective (Work.Thom.relCohMap iE A1 P hiE ℤ (8 + k)).hom :=
    ((CategoryTheory.ConcreteCategory.isIso_iff_bijective _).mp hExcisionD).2
  let τD : Work.Thom.RelCoh ℤ (8 + k) (TopCat.of ↥Ds) A1 :=
    (Work.Thom.relCohMap iE A1 P hiE ℤ (8 + k)).hom τ
  have hspanD : Submodule.span ℤ ({τD} : Set (Work.Thom.RelCoh ℤ (8 + k)
      (TopCat.of ↥Ds) A1)) = ⊤ :=
    Work.Tubular.span_singleton_map_eq_top
      (f := (Work.Thom.relCohMap iE A1 P hiE ℤ (8 + k)).hom) hsurjD (x := τ) hspanτ
  -- the homeomorphism of pairs and the transfer
  let φ : ↥Ds ≃ₜ ↥C.U := ttm_discTubeHomeo E C
  let AU : Set ↥C.U := tubePtSet E C x
  have heφ : ∀ p : ↥Ds, p ∈ A1 ↔ φ p ∈ AU := by
    intro p
    exact ttm_discTubeHomeo_pair E C x p
  have hφmem : ∀ p ∈ A1, φ p ∈ AU := fun p hp => (heφ p).mp hp
  have hBijφ : Function.Bijective
      (Work.Thom.relCohMap (φ : C(↥Ds, ↥C.U)) A1 AU hφmem ℤ (8 + k)).hom :=
    Work.Thom.bijective_relCohMap_of_homeomorphA A1 AU φ heφ ℤ (8 + k)
  -- the target class
  set target : Work.Thom.RelCoh ℤ (8 + k) (TopCat.of ↥C.U) AU :=
    (Work.Thom.relCohMap (Work.ThomBordism.tubeTransMap E C x) AU
      ({0}ᶜ : Set (Work.Tubular.Euc (8 + k))) (Work.ThomBordism.tubeTransMap_mem E C x)
      ℤ (8 + k)).hom (Work.ThomBordism.stdModelGen (8 + k)) with htarget
  -- the two composites agree on the disc bundle
  have hmem1 : ∀ p ∈ A1, Work.ThomBordism.tubeTransMap E C x (φ p)
      ∈ ({0}ᶜ : Set (Work.Tubular.Euc (8 + k))) :=
    fun p hp => Work.ThomBordism.tubeTransMap_mem E C x (φ p) (hφmem p hp)
  have hmem2 : ∀ p ∈ A1, Θ (iE p) ∈ ({0}ᶜ : Set (Work.Tubular.Euc (8 + k))) :=
    fun p hp => hmemΘ (iE p) (hiE p hp)
  have hmap : (Work.ThomBordism.tubeTransMap E C x).comp (φ : C(↥Ds, ↥C.U)) = Θ.comp iE := by
    apply ContinuousMap.ext
    intro p
    rw [ContinuousMap.comp_apply, ContinuousMap.comp_apply]
    show (((φ p : ↥C.U) : Work.Tubular.Euc (8 + k)) - E.e x)
      = Work.ThomBordism.chartAffine E x (Work.ThomBordism.cap E ε (p : Work.Tubular.NormalTotal E))
    have h1 : ((φ p : ↥C.U) : Work.Tubular.Euc (8 + k))
        = Work.Tubular.tubeMap E (p : Work.Tubular.NormalTotal E) := rfl
    have h2 := chartAffine_cap_add_eq_tubeMap E C x
      (p := (p : Work.Tubular.NormalTotal E)) p.2
    rw [h1, ← h2]
    abel
  have hcongr := Work.Thom.relCohMap_congrA A1 ({0}ᶜ : Set (Work.Tubular.Euc (8 + k)))
    hmap hmem1 hmem2 ℤ (8 + k)
  have hcomp1 := Work.Thom.relCohMap_compA A1 AU ({0}ᶜ : Set (Work.Tubular.Euc (8 + k)))
    (φ : C(↥Ds, ↥C.U)) (Work.ThomBordism.tubeTransMap E C x) hφmem
    (Work.ThomBordism.tubeTransMap_mem E C x) hmem1 ℤ (8 + k)
  have hcomp2 := Work.Thom.relCohMap_compA A1 P ({0}ᶜ : Set (Work.Tubular.Euc (8 + k)))
    iE Θ hiE hmemΘ hmem2 ℤ (8 + k)
  have e1 : (Work.Thom.relCohMap (φ : C(↥Ds, ↥C.U)) A1 AU hφmem ℤ (8 + k)).hom target
      = (Work.Thom.relCohMap ((Work.ThomBordism.tubeTransMap E C x).comp (φ : C(↥Ds, ↥C.U)))
          A1 ({0}ᶜ : Set (Work.Tubular.Euc (8 + k))) hmem1 ℤ (8 + k)).hom
        (Work.ThomBordism.stdModelGen (8 + k)) := by
    have h := congrArg ModuleCat.Hom.hom hcomp1
    rw [ModuleCat.hom_comp] at h
    have h' := LinearMap.congr_fun h (Work.ThomBordism.stdModelGen (8 + k))
    simpa [target, LinearMap.comp_apply] using h'
  have e2 : (Work.Thom.relCohMap iE A1 P hiE ℤ (8 + k)).hom τ
      = (Work.Thom.relCohMap (Θ.comp iE) A1 ({0}ᶜ : Set (Work.Tubular.Euc (8 + k))) hmem2
          ℤ (8 + k)).hom (Work.ThomBordism.stdModelGen (8 + k)) := by
    have h := congrArg ModuleCat.Hom.hom hcomp2
    rw [ModuleCat.hom_comp] at h
    have h' := LinearMap.congr_fun h (Work.ThomBordism.stdModelGen (8 + k))
    simpa [τ, LinearMap.comp_apply] using h'
  have e3 : (Work.Thom.relCohMap ((Work.ThomBordism.tubeTransMap E C x).comp (φ : C(↥Ds, ↥C.U)))
        A1 ({0}ᶜ : Set (Work.Tubular.Euc (8 + k))) hmem1 ℤ (8 + k)).hom
        (Work.ThomBordism.stdModelGen (8 + k))
      = (Work.Thom.relCohMap (Θ.comp iE) A1 ({0}ᶜ : Set (Work.Tubular.Euc (8 + k))) hmem2
          ℤ (8 + k)).hom (Work.ThomBordism.stdModelGen (8 + k)) := by
    rw [hcongr]
  have hkey : (Work.Thom.relCohMap (φ : C(↥Ds, ↥C.U)) A1 AU hφmem ℤ (8 + k)).hom target = τD := by
    rw [e1, e3]
    exact e2.symm
  -- conclude
  refine ttm_span_singleton_eq_top_of_injective
    (f := (Work.Thom.relCohMap (φ : C(↥Ds, ↥C.U)) A1 AU hφmem ℤ (8 + k)).hom) hBijφ.1 ?_
  rw [hkey]
  exact hspanD

end

end Work.ThomBordism
