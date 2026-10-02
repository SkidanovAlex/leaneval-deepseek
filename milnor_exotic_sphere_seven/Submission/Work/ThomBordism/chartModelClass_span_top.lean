import Mathlib
import Submission.Work.ThomBordism.chartModelClassDefs
import Submission.Work.ThomBordism.ambientLocalDefs2
import Submission.Work.ThomBordism.radialRescale_homologyMap_id
import Submission.Work.ThomBordism.stdModelGen_pm_stdThomGen
import Submission.Work.ThomBordism.chartModelClass_locSpan
import Submission.Work.ThomBordism.chartModelClass_ne_zero
import Submission.Work.ThomBordism.localisation_surjective_zeroSection

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

namespace Work.ThomBordism

noncomputable section

open CategoryTheory

variable {V : Work.ThomBordism.Man8} {k : ℕ}

/-! ## Auxiliary vocabulary for the chart model class on the normal bundle -/

/-- The punctured part of the closed `ε`-disc bundle of the normal bundle. -/
def cmcPunctDisc (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k)) (ε : ℝ) :
    Set (Work.Tubular.NormalDiscSub E ε) :=
  {p | (p : Work.Tubular.NormalTotal E) ∈ Work.Tubular.normalNonzero E}

@[simp] theorem cmc_mem_punctDisc {E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k)}
    {ε : ℝ} {p : Work.Tubular.NormalDiscSub E ε} :
    p ∈ cmcPunctDisc E ε ↔ (p : Work.Tubular.NormalTotal E) ∈ Work.Tubular.normalNonzero E :=
  Iff.rfl

/-- A positive fibrewise radial rescaling is continuous. -/
theorem cmc_continuous_radialRescale (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k))
    (φ : ℝ → ℝ) (hφ : Continuous φ) : Continuous (radialRescale E φ) := by
  have h1 : Continuous (fun p : Work.Tubular.NormalTotal E =>
      ((p : V.pt × Work.Tubular.Euc (8 + k)).1, φ (Work.Tubular.normalNorm E p) •
        (p : V.pt × Work.Tubular.Euc (8 + k)).2)) :=
    (continuous_subtype_val.fst).prodMk
      (((hφ.comp (Work.Tubular.continuous_normalNorm E)).smul continuous_subtype_val.snd))
  have h2 : ∀ p : Work.Tubular.NormalTotal E, ((p : V.pt × Work.Tubular.Euc (8 + k)).1,
      φ (Work.Tubular.normalNorm E p) • (p : V.pt × Work.Tubular.Euc (8 + k)).2) ∈
      {q : V.pt × Work.Tubular.Euc (8 + k) | q.2 ∈ Work.Tubular.normalSpace E q.1} :=
    fun p => Submodule.smul_mem (Work.Tubular.normalSpace E p.1.1) _ p.2
  exact h1.subtype_mk h2

/-- The capping is continuous. -/
theorem cmc_continuous_cap (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k))
    {ε : ℝ} (hε : 0 < ε) : Continuous (cap E ε) :=
  cmc_continuous_radialRescale E (capCoeff ε) (continuous_capCoeff hε)

/-- **The capping, as a map into the closed disc bundle.** -/
def cmcCapDisc (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k)) {ε : ℝ}
    (C : Work.Tubular.TubeChart E ε) :
    C(Work.Tubular.NormalTotal E, Work.Tubular.NormalDiscSub E ε) :=
  ⟨fun p => ⟨cap E ε p, Work.ThomBordism.cap_mem_disc E C.eps_pos.le p⟩,
    (cmc_continuous_cap E C.eps_pos).subtype_mk
      (fun p => Work.ThomBordism.cap_mem_disc E C.eps_pos.le p)⟩

@[simp] theorem cmcCapDisc_apply (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k))
    {ε : ℝ} (C : Work.Tubular.TubeChart E ε) (p : Work.Tubular.NormalTotal E) :
    ((cmcCapDisc E C p : Work.Tubular.NormalDiscSub E ε) : Work.Tubular.NormalTotal E)
      = cap E ε p := rfl

/-- The capping maps the punctured total space into the punctured disc bundle. -/
theorem cmcCapDisc_mem (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k)) {ε : ℝ}
    (C : Work.Tubular.TubeChart E ε) :
    ∀ p ∈ Work.Tubular.normalNonzero E, cmcCapDisc E C p ∈ cmcPunctDisc E ε := by
  intro p hp
  rw [cmc_mem_punctDisc, cmcCapDisc_apply]
  exact radialRescale_mem_normalNonzero E (capCoeff ε)
    (fun r hr => capCoeff_pos C.eps_pos r hr) hp

/-- The inclusion of the closed disc bundle in the total space. -/
def cmcInclDisc (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k)) (ε : ℝ) :
    C(Work.Tubular.NormalDiscSub E ε, Work.Tubular.NormalTotal E) :=
  ⟨Subtype.val, continuous_subtype_val⟩

@[simp] theorem cmcInclDisc_apply (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k))
    (ε : ℝ) (p : Work.Tubular.NormalDiscSub E ε) : cmcInclDisc E ε p = p.1 := rfl

/-- The capping is the identity on the closed disc bundle. -/
theorem cmcCapDisc_comp_inclDisc (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k))
    {ε : ℝ} (C : Work.Tubular.TubeChart E ε) :
    (cmcCapDisc E C).comp (cmcInclDisc E ε) = ContinuousMap.id (Work.Tubular.NormalDiscSub E ε) := by
  apply ContinuousMap.ext
  intro p
  apply Subtype.ext
  show cap E ε (p : Work.Tubular.NormalTotal E) = (p : Work.Tubular.NormalTotal E)
  exact cap_eq_self_of_le E C.eps_pos.le p.2

/-- **The homotopy from the composite `incl ∘ cap` to the identity**, through positive fibrewise
radial rescalings. -/
def cmcCapDiscHomotopy (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k))
    {ε : ℝ} (C : Work.Tubular.TubeChart E ε) :
    ((cmcInclDisc E ε).comp (cmcCapDisc E C)).Homotopy
      (ContinuousMap.id (Work.Tubular.NormalTotal E)) where
  toContinuousMap := radialRescaleHomotopy E (capCoeff ε) (continuous_capCoeff C.eps_pos)
  map_zero_left := fun p => by
    change radialRescaleHomotopyFun E (capCoeff ε) ((0 : unitInterval), p)
      = ((cmcInclDisc E ε).comp (cmcCapDisc E C)) p
    rw [radialRescaleHomotopyFun_zero]
    rfl
  map_one_left := fun p => by
    change radialRescaleHomotopyFun E (capCoeff ε) ((1 : unitInterval), p)
      = (ContinuousMap.id (Work.Tubular.NormalTotal E)) p
    rw [radialRescaleHomotopyFun_one]
    rfl

/-- **The other composite is homotopic to the identity**, through positive fibrewise radial
rescalings, hence through maps of pairs `(ν, ν∖0) → (ν, ν∖0)`. -/
theorem cmcCapDisc_homotopy (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k))
    {ε : ℝ} (C : Work.Tubular.TubeChart E ε) :
    ((cmcInclDisc E ε).comp (cmcCapDisc E C)).Homotopic
      (ContinuousMap.id (Work.Tubular.NormalTotal E)) :=
  ⟨cmcCapDiscHomotopy E C⟩

/-- **The pullback along the capping is surjective** on the relative cohomology of the pair
`(ν, ν∖0)`: the capping has the inclusion of the closed disc bundle as a section and is homotopic
to the identity. -/
theorem cmcCapDisc_pullback_surjective (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k))
    {ε : ℝ} (C : Work.Tubular.TubeChart E ε) (m : ℕ) :
    Function.Surjective ((Work.Thom.relCohMap (cmcCapDisc E C) (Work.Tubular.normalNonzero E)
      (cmcPunctDisc E ε) (cmcCapDisc_mem E C) ℤ m).hom) := by
  let A : Set (Work.Tubular.NormalTotal E) := Work.Tubular.normalNonzero E
  let B : Set (Work.Tubular.NormalDiscSub E ε) := cmcPunctDisc E ε
  have hAB : ∀ p ∈ A, cmcCapDisc E C p ∈ B := fun p hp => cmcCapDisc_mem E C p hp
  have hBA : ∀ p ∈ B, cmcInclDisc E ε p ∈ A := fun p hp => hp
  have hAA : ∀ p ∈ A, cmcInclDisc E ε (cmcCapDisc E C p) ∈ A := fun p hp => hBA _ (hAB p hp)
  have hH : ∀ (t : unitInterval) (p : Work.Tubular.NormalTotal E), p ∈ A →
      (cmcCapDiscHomotopy E C) (t, p) ∈ A :=
    fun t p hp => radialRescaleHomotopyFun_mem_normalNonzero E (capCoeff ε)
      (fun r hr => capCoeff_pos C.eps_pos r hr) hp
  -- the pullback along the composite `incl ∘ cap` equals the pullback along the identity
  have hhom : (Work.Thom.relCohMap ((cmcInclDisc E ε).comp (cmcCapDisc E C)) A A hAA ℤ m)
      = Work.Thom.relCohMap (ContinuousMap.id (Work.Tubular.NormalTotal E)) A A
          (fun _ h => h) ℤ m :=
    @Work.Thom.relCohMap_homotopic (Work.Tubular.NormalTotal E) (Work.Tubular.NormalTotal E)
      _ _ A A ((cmcInclDisc E ε).comp (cmcCapDisc E C))
      (ContinuousMap.id (Work.Tubular.NormalTotal E)) hAA (fun _ h => h)
      (cmcCapDiscHomotopy E C) hH ℤ _ m
  -- functoriality: the pullback along `cap` composed with the pullback along `incl` is the identity
  have hcomp := Work.Thom.relCohMap_compA A B A (cmcCapDisc E C) (cmcInclDisc E ε)
    hAB hBA hAA ℤ m
  have hfinal := hcomp.trans (hhom.trans (Work.Thom.relCohMap_idA A ℤ m))
  have h := congrArg ModuleCat.Hom.hom hfinal
  rw [ModuleCat.hom_comp, ModuleCat.hom_id] at h
  intro y
  refine ⟨(Work.Thom.relCohMap (cmcInclDisc E ε) B A hBA ℤ m).hom y, ?_⟩
  simpa using LinearMap.congr_fun h y

/-- **`chartModelClass E C x hcont` generates `H^{8+k}(ν, ν∖0)`.**

The class is the pullback of the standard generator `stdModelGen (8+k)` of
`H^{8+k}(ℝ^{8+k}, {0}ᶜ)` along the capped ambient chart map `p ↦ chartAffine E x (cap E ε p)`, which
is a map of pairs `(ν,ν∖0) → (ℝ^{8+k},{0}ᶜ)`; it is a *local* homeomorphism of pairs at the
zero-section point `0_x` (`chartModelClass_locSpan`: the local class generates the local group
`H^{8+k}(ν, ν∖{0_x}) ≅ ℤ`), and the cohomological localisation
`H^{8+k}(ν,ν∖{0_x}) → H^{8+k}(ν,ν∖0)` is surjective (`localisation_surjective_zeroSection`), so the
generator of the local group maps to a generator of `H^{8+k}(ν,ν∖0) ≅ ℤ`. -/
theorem chartModelClass_span_top {V : Work.ThomBordism.Man8} [ConnectedSpace V.pt] {k : ℕ}
    (hk : 1 ≤ k)
    (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k)) {ε : ℝ}
    (C : Work.Tubular.TubeChart E ε) (x : V.pt)
    (hcont : Continuous fun p : Work.Tubular.NormalTotal E =>
      Work.ThomBordism.chartAffine E x (Work.ThomBordism.cap E ε p)) :
    Submodule.span ℤ
      ({ Work.ThomBordism.chartModelClass E C x hcont } : Set
        (Work.Thom.RelCoh ℤ (8 + k) (TopCat.of (Work.Tubular.NormalTotal E))
          (Work.Tubular.normalNonzero E))) = ⊤ := by
  classical
  let Θ : C(Work.Tubular.NormalTotal E, Work.Tubular.Euc (8 + k)) :=
    ⟨fun p => Work.ThomBordism.chartAffine E x (Work.ThomBordism.cap E ε p), hcont⟩
  have hsub : Work.Tubular.normalNonzero E ⊆
      ({p : Work.Tubular.NormalTotal E | p ≠ Work.Tubular.zeroSectionNormal E x}) := by
    intro p hp
    intro h
    refine (Work.Tubular.mem_normalNonzero (E := E)).mp hp ?_
    have h2 : p = Work.Tubular.zeroSectionNormal E x := h
    rw [h2]; simp
  have hcap : ∀ p : Work.Tubular.NormalTotal E, p ≠ Work.Tubular.zeroSectionNormal E x →
      Work.ThomBordism.chartAffine E x (Work.ThomBordism.cap E ε p) ≠ 0 :=
    fun p hp => Work.ThomBordism.chartAffine_cap_ne_zero_of_ne_zeroSection' E C x hp
  -- the local generator condition
  have hmem : ∀ p ∈ ({p : Work.Tubular.NormalTotal E |
      p ≠ Work.Tubular.zeroSectionNormal E x}),
      Work.ThomBordism.chartAffine E x (Work.ThomBordism.cap E ε p) ∈
        ({0}ᶜ : Set (Work.Tubular.Euc (8 + k))) := fun p hp => hcap p hp
  -- (1) the local class generates the local group
  have hspan : Submodule.span ℤ
      ({((Work.Thom.relCohMap Θ
          ({p : Work.Tubular.NormalTotal E | p ≠ Work.Tubular.zeroSectionNormal E x})
          ({0}ᶜ : Set (Work.Tubular.Euc (8 + k))) hmem ℤ (8 + k)).hom
        (Work.ThomBordism.stdModelGen (8 + k)))} : Set
        (Work.Thom.RelCoh ℤ (8 + k) (TopCat.of (Work.Tubular.NormalTotal E))
          ({p : Work.Tubular.NormalTotal E | p ≠ Work.Tubular.zeroSectionNormal E x}))) = ⊤ :=
    Work.ThomBordism.chartModelClass_locSpan hk E C x hcont hmem
  -- (2) the cohomological localisation is surjective
  have hsurj : Function.Surjective ((Work.Thom.relCohMap (ContinuousMap.id
      (Work.Tubular.NormalTotal E)) (Work.Tubular.normalNonzero E)
      ({p : Work.Tubular.NormalTotal E | p ≠ Work.Tubular.zeroSectionNormal E x}) hsub
      ℤ (8 + k)).hom) :=
    Work.ThomBordism.localisation_surjective_zeroSection hk E x
  -- (3) the chart model class is the localisation of the local class
  have hrel : Work.ThomBordism.chartModelClass E C x hcont =
      (Work.Thom.relCohMap (ContinuousMap.id (Work.Tubular.NormalTotal E))
        (Work.Tubular.normalNonzero E)
        ({p : Work.Tubular.NormalTotal E | p ≠ Work.Tubular.zeroSectionNormal E x})
        hsub ℤ (8 + k)).hom
      ((Work.Thom.relCohMap Θ
        ({p : Work.Tubular.NormalTotal E | p ≠ Work.Tubular.zeroSectionNormal E x})
        ({0}ᶜ : Set (Work.Tubular.Euc (8 + k))) hmem ℤ (8 + k)).hom
        (Work.ThomBordism.stdModelGen (8 + k))) := by
    have hmemA : ∀ p ∈ Work.Tubular.normalNonzero E,
        Θ p ∈ ({0}ᶜ : Set (Work.Tubular.Euc (8 + k))) := fun p hp => hcap p (hsub hp)
    have h2 := Work.Thom.relCohMap_compA_apply
      (Work.Tubular.normalNonzero E)
      ({p : Work.Tubular.NormalTotal E | p ≠ Work.Tubular.zeroSectionNormal E x})
      ({0}ᶜ : Set (Work.Tubular.Euc (8 + k)))
      (ContinuousMap.id (Work.Tubular.NormalTotal E)) Θ hsub hmem hmemA
      ℤ (8 + k) (Work.ThomBordism.stdModelGen (8 + k))
    have h1 : (Work.Thom.relCohMap (Θ.comp (ContinuousMap.id (Work.Tubular.NormalTotal E)))
          (Work.Tubular.normalNonzero E) ({0}ᶜ : Set (Work.Tubular.Euc (8 + k)))
          hmemA ℤ (8 + k)).hom (Work.ThomBordism.stdModelGen (8 + k))
        = (Work.Thom.relCohMap Θ (Work.Tubular.normalNonzero E)
          ({0}ᶜ : Set (Work.Tubular.Euc (8 + k)))
          hmemA ℤ (8 + k)).hom (Work.ThomBordism.stdModelGen (8 + k)) :=
      LinearMap.congr_fun
        (congrArg (fun φ => ModuleCat.Hom.hom φ)
          (Work.Thom.relCohMap_congrA (Work.Tubular.normalNonzero E)
            ({0}ᶜ : Set (Work.Tubular.Euc (8 + k))) (ContinuousMap.comp_id Θ)
            hmemA hmemA ℤ (8 + k)))
        (Work.ThomBordism.stdModelGen (8 + k))
    rw [Work.ThomBordism.chartModelClass]
    rw [h2, h1]
  -- (4) assemble: the localisation of a generator is a generator
  rw [hrel]
  exact Work.Tubular.span_singleton_map_eq_top _ hsurj _ hspan

end

end Work.ThomBordism
