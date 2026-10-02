import Mathlib
import Submission.Work.ThomBordism.ambientClassDefs
import Submission.Work.ThomBordism.chartModelClassDefs
import Submission.Work.Tubular.relKronH_natural
import Submission.Work.Tubular.ThomRepOfLocalDegree
import Submission.Work.ThomBordism.chartModelClass_pairing_eq_pm_one
import Submission.Work.ThomBordism.localisationHurewicz
import Submission.Work.ThomBordism.cappedChart_homotopic_translation
import Submission.Work.Stems.Hurewicz
import Submission.Work.ThomBordism.value_eq_chartModelClass
import Submission.Work.ThomBordism.cla_uniformity
import Submission.Work.ThomBordism.valuePmOneV2
import Submission.Work.ThomBordism.valuePmOneV2Defs
import Submission.Work.ThomBordism.relCohMap_eq_of_homotopicOn
import Submission.Work.ThomBordism.somePullbackCompPullV2
import Submission.Work.ThomBordism.blowPsiStage_mem_fine
import Submission.Work.ThomBordism.blowPsiStage_one_relCohMap_eq_incl_fine

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

open CategoryTheory

namespace Work.ThomBordism

noncomputable section

variable {V : Work.ThomBordism.Man8} {k : ℕ}

/-!
# `collapseLocalisation_ambientV2`: the ambient collapse localisation

## The target

There is `κ = ±1` such that for **every** datum (embedding `E` of a closed oriented smooth
`8`-manifold, tube chart `C`, pinned collapse `g`, box radius `R`, point `x`) and every relative
chain `δ` whose tube avatar is the collapse class `collapseRelK8`, the pairing

  `⟨ambientStandardClass E C x, δ⟩`

is `κ`.

## The reduction proved in this file (`value_eq_chart`)

`ambientStandardClass E C x` is (by definition) the pull-back of the model generator
`stdModelGen (8+k)` along the translation `y ↦ y - E.e x` on the tube; writing
`chartModelClass E C x` for its ν-side avatar (the pull-back of `stdModelGen` along
`p ↦ chartAffine E x (cap E ε p)`, `Submission/Work/ThomBordism/chartModelClassDefs.lean`), the
identity `ambientStandardClass_eq_chartModelClass` says that the tube inverse pulls the chart model
class back to the ambient standard class.  Applying the naturality of the relative Kronecker pairing
(`Work.Tubular.relKronH_natural`) along the tube inverse and the hypothesis on `δ` gives the
**assembly**

  `⟨ambientStandardClass E C x, δ⟩ = ⟨chartModelClass E C x, collapseRelK8⟩`,

proved below as `value_eq_chart` (with the degree bookkeeping `k + 8 ↔ 8 + k`).

## The mathematical content that remains

Everything is now expressed through the two *explicit* maps

* `Φ_x := chartAffine E x ∘ cap E ε : ν → ℝ^{8+k}`  (the capped ambient chart),
* `F : S^{8+k} → ν⁺`  (the Pontryagin–Thom collapse),  together with the model generator
  `stdModelGen` and the sphere generator `Work.Stems.sphereGenerator`,

and the value is the pairing of the model generator with the push-forward of the collapse class.
The proof that this is a *datum-independent* `±1` proceeds in three steps (worked out in detail in
`NOTE_AMBIENTV2_STRATEGY.md`, this directory):

1. **(localisation)** the pairing localises at the zero-section point `0_x`: for
   `W := Φ_x ∘ F` (the collapse read in the ambient chart — defined near the preimage `y₀` of `0_x`)

     `value = ⟨(germ of W at y₀)^* stdModelGen, loc_{y₀} sphereGenerator⟩`;

   here `loc_{y}` is the canonical localisation `H_n(S^n) → H_n(S^n, S^n ∖ {y})`, and the
   identification of the localisation of the collapse class with the germ-push-forward of the
   sphere generator is the "the collapse is a local homeomorphism of degree one" statement.
2. **(homotopy)** — **PROVED**, see `Work.ThomBordism.chartBlowUp_homotopic_translation`
   (`Submission/Work/ThomBordism/chartBlowUp_homotopic_translation.lean`, sorry-free): the germ of
   `W` at `y₀` is homotopic, through maps of pairs, to the germ of the *translation* `τ_{−E.e x}`:  both are `y ↦ Φ_x (blowUp (C.inv y))` up to the radial rescaling
   homotopy `blowUp ≍ id` (`Work.ThomBordism.radialRescale_homologyMap_id`), and
   `Φ_x ∘ C.inv = τ_{−E.e x}` *exactly* (`chartAffine_inv`), so the two local degrees cancel.
3. **(evaluation)** `τ_*(loc_{y₀}(sphereGenerator)) = loc_{0}(sphereGenerator)` by functoriality of
   the localisation, since the translation is homotopic to the identity (`τ_* = id` on `H_n(S^n)`).

Consequently the value is the *fixed* number `⟨stdModelGen, loc_0 (sphereGenerator)⟩ ∈ ℤ`, which is
±1 by the unimodularity of the (localised) Kronecker pairing, giving the target with
`κ := ⟨stdModelGen, loc_0 (sphereGenerator)⟩`.

In particular the *datum-dependent* factors (the tube chart, the collapse map `g`, the radius `R`,
the point `x`, the embedding `E`) cancel: the tube-inverse and the collapse's chart inverse are
inverse maps at corresponding points, and the radial maps involved are homotopic to the identity
through *positive* radial rescalings (which preserve the punctured total space).  This is why the
sign is universal and why no "local degree/orientation" chapter is needed.
-/

/-- The embedding map is continuous. -/
theorem continuous_E_e (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k)) :
    Continuous E.e := E.smooth.continuous

/-- The map into the ambient product underlying a radial rescaling. -/
theorem continuous_radialRescale_fun (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k))
    (φ : ℝ → ℝ) (hφ : Continuous φ) :
    Continuous fun p : Work.Tubular.NormalTotal E =>
      ((p : V.pt × Work.Tubular.Euc (8 + k)).1,
        φ (Work.Tubular.normalNorm E p) • (p : V.pt × Work.Tubular.Euc (8 + k)).2) :=
  Continuous.prodMk ((Work.Tubular.NormalTotal.continuous_proj E))
    ((hφ.comp (Work.Tubular.continuous_normalNorm E)).smul continuous_subtype_val.snd)

/-- A radial rescaling is continuous. -/
theorem continuous_radialRescale (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k))
    (φ : ℝ → ℝ) (hφ : Continuous φ) : Continuous (radialRescale E φ) := by
  refine (continuous_induced_rng (f := (Subtype.val :
      Work.Tubular.NormalTotal E → V.pt × Work.Tubular.Euc (8 + k)))
    (g := radialRescale E φ)).mpr ?_
  exact continuous_radialRescale_fun E φ hφ

/-- The ambient chart map is continuous. -/
theorem continuous_chartAffine (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k))
    (x : V.pt) : Continuous (chartAffine E x) := by
  have h1 : Continuous fun p : Work.Tubular.NormalTotal E =>
      (p : V.pt × Work.Tubular.Euc (8 + k)) := continuous_subtype_val
  have h2 : Continuous fun p : Work.Tubular.NormalTotal E =>
      (E.e ((p : V.pt × Work.Tubular.Euc (8 + k)).1)) :=
    (continuous_E_e E).comp (continuous_fst.comp h1)
  have h3 : Continuous fun p : Work.Tubular.NormalTotal E =>
      (p : V.pt × Work.Tubular.Euc (8 + k)).2 := continuous_snd.comp h1
  have h4 : chartAffine E x = fun p : Work.Tubular.NormalTotal E =>
      E.e ((p : V.pt × Work.Tubular.Euc (8 + k)).1)
        + (p : V.pt × Work.Tubular.Euc (8 + k)).2 - E.e x := by
    funext p; rw [chartAffine_apply]
  rw [h4]
  exact (h2.add h3).sub continuous_const

/-- The capped ambient chart map is continuous (the hypothesis `hcont` of `chartModelClass`). -/
theorem continuous_chartAffine_cap (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k))
    {ε : ℝ} (C : Work.Tubular.TubeChart E ε) (x : V.pt) :
    Continuous fun p : Work.Tubular.NormalTotal E =>
      Work.ThomBordism.chartAffine E x (Work.ThomBordism.cap E ε p) :=
  (continuous_chartAffine E x).comp (continuous_cap E C.eps_pos)

/-- The cast of a `homologyMap` for a cochain complex. -/
theorem cochainHomologyMap_cast {K L : CochainComplex (ModuleCat ℤ) ℕ} (φ : K ⟶ L) {a b : ℕ}
    (h : a = b) (x : K.homology a) :
    (HomologicalComplex.homologyMap φ b).hom (h ▸ x)
      = h ▸ ((HomologicalComplex.homologyMap φ a).hom x) := by
  cases h; rfl

/-- **The assembly**: the target's value is the pairing of the chart model class with the collapse
class, at the target's degree `k + 8`. -/
theorem value_eq_chart (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k))
    {ε : ℝ} (C : Work.Tubular.TubeChart E ε)
    (g : C(OnePoint (Work.Tubular.Euc (8 + k)), OnePoint (Work.Tubular.NormalTotal E)))
    (hg : ∀ y, y ∉ C.openTube → g (OnePoint.some y) = OnePoint.infty)
    {R : ℝ} (hR : 0 ≤ R) (hbox : ∀ y ∈ C.U, ∀ j : Fin (8 + k), |y j| < R) (x : V.pt)
    (δ : (Work.Cohomology.relChains (TopCat.of ↥C.U)
        (Work.ThomBordism.tubeInvPunct E C)).homology (k + 8))
    (hδ : Work.ThomBordism.tubeInvHomology E C δ
        = Work.Tubular.collapseRelK8 C g hg hR hbox) :
    Work.Tubular.relKronH (TopCat.of ↥C.U) (Work.ThomBordism.tubeInvPunct E C) (k + 8)
        ((Nat.add_comm 8 k) ▸ Work.ThomBordism.ambientStandardClass E C x) δ
      = Work.Tubular.relKronH (TopCat.of (Work.Tubular.NormalTotal E))
          (Work.Tubular.normalNonzero E) (k + 8)
          ((Nat.add_comm 8 k) ▸ chartModelClass E C x (continuous_chartAffine_cap E C x))
          (Work.Tubular.collapseRelK8 C g hg hR hbox) := by
  have hh : 8 + k = k + 8 := Nat.add_comm 8 k
  -- (2) the ambient class is the tube-inverse pullback of the chart model class
  rw [← Work.ThomBordism.ambientStandardClass_eq_chartModelClass E C x
    (continuous_chartAffine_cap E C x)]
  -- (2b) move the degree cast past the pullback (cohomology side)
  have hcast := cochainHomologyMap_cast
    (Work.Cohomology.relComplexMap (X₁ := TopCat.of ↥C.U)
      (X₂ := TopCat.of (Work.Tubular.NormalTotal E)) ℤ
      (Work.ThomBordism.tubeInvPunct E C) (Work.Tubular.normalNonzero E)
      (TopCat.ofHom (Work.ThomBordism.tubeInvMap E C)) (fun y hy => hy))
    (a := 8 + k) (b := k + 8) hh
    (show (Work.Cohomology.relComplex ℤ (TopCat.of (Work.Tubular.NormalTotal E))
        (Work.Tubular.normalNonzero E)).homology (8 + k) from
      chartModelClass E C x (continuous_chartAffine_cap E C x))
  rw [← hcast]
  -- (3) naturality of the relative Kronecker pairing along the tube inverse
  rw [Work.Tubular.relKronH_natural (X := TopCat.of ↥C.U)
      (Y := TopCat.of (Work.Tubular.NormalTotal E))
      (A := Work.ThomBordism.tubeInvPunct E C) (B := Work.Tubular.normalNonzero E)
      (f := TopCat.ofHom (Work.ThomBordism.tubeInvMap E C))
      (g := tubeInvSub E C) (hf := fun y hy => hy) (w := tubeInv_compat E C)
      (n := k + 8)]
  -- (4) the pushforward of δ is the tube-avatar of the collapse class
  rw [show (HomologicalComplex.homologyMap (Work.Cohomology.relChainsMapOf (TopCat.of ↥C.U)
      (TopCat.of (Work.Tubular.NormalTotal E))
      (Work.ThomBordism.tubeInvPunct E C) (Work.Tubular.normalNonzero E)
      (TopCat.ofHom (Work.ThomBordism.tubeInvMap E C)) (tubeInvSub E C)
      (tubeInv_compat E C)) (k + 8)).hom δ
      = Work.ThomBordism.tubeInvHomology E C δ from rfl]
  rw [hδ]

/-! ## The reduction to the translation on the tube -/

/-- **The capped ambient chart, read on the tube inverse, is the translation.** -/
theorem chartAffine_cap_inv (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k)) {ε : ℝ}
    (C : Work.Tubular.TubeChart E ε) (x : V.pt) {y : Work.Tubular.Euc (8 + k)} (hy : y ∈ C.U) :
    chartAffine E x (cap E ε (C.inv y)) = y - E.e x := by
  rw [cap_inv E C hy, chartAffine_inv E C x hy]

/-- The capped ambient chart, read in the coordinates of the tube. -/
theorem chartAffine_cap_inv_coe (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k))
    {ε : ℝ} (C : Work.Tubular.TubeChart E ε) (x : V.pt) (y : ↥C.U) :
    chartAffine E x (cap E ε (C.inv (y : Work.Tubular.Euc (8 + k)))) =
      (y : Work.Tubular.Euc (8 + k)) - E.e x :=
  chartAffine_cap_inv E C x y.2

/-- The translation on the punctured part of the tube. -/
noncomputable def tubeTransSub (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k))
    {ε : ℝ} (C : Work.Tubular.TubeChart E ε) (x : V.pt) :
    C(↥(tubeInvPunct E C), ↥({0}ᶜ : Set (Work.Tubular.Euc (8 + k)))) :=
  ⟨fun y => ⟨((y.1 : ↥C.U) : Work.Tubular.Euc (8 + k)) - E.e x,
      Set.mem_compl_singleton_iff.mpr (sub_ne_zero.mpr (tubeInvPunct_sub E C x y.2))⟩,
    Continuous.subtype_mk
      ((continuous_subtype_val.comp continuous_subtype_val).sub continuous_const) _⟩

theorem tubeTrans_mem (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k))
    {ε : ℝ} (C : Work.Tubular.TubeChart E ε) (x : V.pt) :
    ∀ y ∈ tubeInvPunct E C,
      tubeTransMap E C x y ∈ ({0}ᶜ : Set (Work.Tubular.Euc (8 + k))) :=
  fun y hy => Set.mem_compl_singleton_iff.mpr (sub_ne_zero.mpr (tubeInvPunct_sub E C x hy))

theorem tubeTrans_compat (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k))
    {ε : ℝ} (C : Work.Tubular.TubeChart E ε) (x : V.pt) :
    Work.Cohomology.subtypeIncl (TopCat.of ↥C.U) (tubeInvPunct E C)
        ≫ TopCat.ofHom (tubeTransMap E C x)
      = TopCat.ofHom (tubeTransSub E C x)
        ≫ Work.Cohomology.subtypeIncl (TopCat.of (Work.Tubular.Euc (8 + k)))
            ({0}ᶜ : Set (Work.Tubular.Euc (8 + k))) := by
  apply TopCat.ext
  intro a
  rfl

/-- The induced map on relative chains of the translation, at the target's degree `k + 8`. -/
noncomputable def tubeTransChains (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k))
    {ε : ℝ} (C : Work.Tubular.TubeChart E ε) (x : V.pt) :
    Work.Cohomology.relChains (TopCat.of ↥C.U) (tubeInvPunct E C) ⟶
      Work.Cohomology.relChains (TopCat.of (Work.Tubular.Euc (8 + k)))
        ({0}ᶜ : Set (Work.Tubular.Euc (8 + k))) :=
  Work.Cohomology.relChainsMapOf (TopCat.of ↥C.U) (TopCat.of (Work.Tubular.Euc (8 + k)))
    (tubeInvPunct E C) ({0}ᶜ : Set (Work.Tubular.Euc (8 + k)))
    (TopCat.ofHom (tubeTransMap E C x)) (TopCat.ofHom (tubeTransSub E C x))
    (tubeTrans_compat E C x)

/-- **The value is the pairing of the model generator with the translation-avatar of `δ`.** -/
theorem value_eq_stdModelGen (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k))
    {ε : ℝ} (C : Work.Tubular.TubeChart E ε) (x : V.pt)
    (δ : (Work.Cohomology.relChains (TopCat.of ↥C.U) (tubeInvPunct E C)).homology (k + 8)) :
    Work.Tubular.relKronH (TopCat.of ↥C.U) (tubeInvPunct E C) (k + 8)
        ((Nat.add_comm 8 k) ▸ ambientStandardClass E C x) δ
      = Work.Tubular.relKronH (TopCat.of (Work.Tubular.Euc (8 + k)))
          ({0}ᶜ : Set (Work.Tubular.Euc (8 + k))) (k + 8)
          ((Nat.add_comm 8 k) ▸ stdModelGen (8 + k))
          ((HomologicalComplex.homologyMap (tubeTransChains E C x) (k + 8)).hom δ) := by
  have hamb : ambientStandardClass E C x
      = (Work.Thom.relCohMap (tubeTransMap E C x) (tubeInvPunct E C)
          ({0}ᶜ : Set (Work.Tubular.Euc (8 + k))) (tubeTrans_mem E C x) ℤ (8 + k)).hom
        (stdModelGen (8 + k)) := rfl
  rw [hamb, ← Work.Tubular.relCohMap_cast (tubeTransMap E C x) (tubeTrans_mem E C x)
    (Nat.add_comm 8 k) (stdModelGen (8 + k))]
  exact Work.Tubular.relKronH_natural (TopCat.ofHom (tubeTransMap E C x))
    (TopCat.ofHom (tubeTransSub E C x)) (tubeTrans_mem E C x) (tubeTrans_compat E C x)
    (k + 8) ((Nat.add_comm 8 k) ▸ stdModelGen (8 + k)) δ

/-! ## The two avatars of the collapse class -/

/-- The capped ambient chart as a map of pairs `(ν, ν∖0) → (ℝ^{8+k}, {0}ᶜ)`. -/
noncomputable def capChartMap (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k))
    {ε : ℝ} (C : Work.Tubular.TubeChart E ε) (x : V.pt)
    (hcont : Continuous fun p : Work.Tubular.NormalTotal E =>
      chartAffine E x (cap E ε p)) : C(Work.Tubular.NormalTotal E, Work.Tubular.Euc (8 + k)) :=
  ⟨fun p => chartAffine E x (cap E ε p), hcont⟩

theorem capChartMap_mem (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k))
    {ε : ℝ} (C : Work.Tubular.TubeChart E ε) (x : V.pt)
    (hcont : Continuous fun p : Work.Tubular.NormalTotal E =>
      chartAffine E x (cap E ε p)) :
    ∀ p ∈ Work.Tubular.normalNonzero E,
      capChartMap E C x hcont p ∈ ({0}ᶜ : Set (Work.Tubular.Euc (8 + k))) :=
  fun p hp => Set.mem_compl_singleton_iff.mpr (chartAffine_cap_ne_zero E C x hp)

theorem chartModelClass_eq (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k))
    {ε : ℝ} (C : Work.Tubular.TubeChart E ε) (x : V.pt)
    (hcont : Continuous fun p : Work.Tubular.NormalTotal E =>
      chartAffine E x (cap E ε p)) :
    chartModelClass E C x hcont
      = (Work.Thom.relCohMap (capChartMap E C x hcont) (Work.Tubular.normalNonzero E)
          ({0}ᶜ : Set (Work.Tubular.Euc (8 + k))) (capChartMap_mem E C x hcont) ℤ (8 + k)).hom
        (stdModelGen (8 + k)) := rfl

/-- The subtype map on the punctured parts induced by the capped ambient chart. -/
noncomputable def capChartSub (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k))
    {ε : ℝ} (C : Work.Tubular.TubeChart E ε) (x : V.pt)
    (hcont : Continuous fun p : Work.Tubular.NormalTotal E =>
      chartAffine E x (cap E ε p)) :
    TopCat.of ↥(Work.Tubular.normalNonzero E) ⟶
      TopCat.of ↥({0}ᶜ : Set (Work.Tubular.Euc (8 + k))) :=
  TopCat.ofHom ⟨fun p : ↥(Work.Tubular.normalNonzero E) =>
      ⟨capChartMap E C x hcont (p : Work.Tubular.NormalTotal E),
        capChartMap_mem E C x hcont (p : Work.Tubular.NormalTotal E) p.2⟩,
    Continuous.subtype_mk ((capChartMap E C x hcont).continuous.comp continuous_subtype_val) _⟩

theorem capChartSub_compat (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k))
    {ε : ℝ} (C : Work.Tubular.TubeChart E ε) (x : V.pt)
    (hcont : Continuous fun p : Work.Tubular.NormalTotal E =>
      chartAffine E x (cap E ε p)) :
    Work.Cohomology.subtypeIncl (TopCat.of (Work.Tubular.NormalTotal E))
        (Work.Tubular.normalNonzero E) ≫ TopCat.ofHom (capChartMap E C x hcont)
      = capChartSub E C x hcont
        ≫ Work.Cohomology.subtypeIncl (TopCat.of (Work.Tubular.Euc (8 + k)))
            ({0}ᶜ : Set (Work.Tubular.Euc (8 + k))) := by
  apply TopCat.ext
  intro a
  rfl

/-- The induced map on relative chains of the capped ambient chart, at degree `k + 8`. -/
noncomputable def capChartChains (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k))
    {ε : ℝ} (C : Work.Tubular.TubeChart E ε) (x : V.pt)
    (hcont : Continuous fun p : Work.Tubular.NormalTotal E =>
      chartAffine E x (cap E ε p)) :
    Work.Cohomology.relChains (TopCat.of (Work.Tubular.NormalTotal E))
        (Work.Tubular.normalNonzero E) ⟶
      Work.Cohomology.relChains (TopCat.of (Work.Tubular.Euc (8 + k)))
        ({0}ᶜ : Set (Work.Tubular.Euc (8 + k))) :=
  Work.Cohomology.relChainsMapOf (TopCat.of (Work.Tubular.NormalTotal E))
    (TopCat.of (Work.Tubular.Euc (8 + k))) (Work.Tubular.normalNonzero E)
    ({0}ᶜ : Set (Work.Tubular.Euc (8 + k))) (TopCat.ofHom (capChartMap E C x hcont))
    (capChartSub E C x hcont) (capChartSub_compat E C x hcont)

/-- The composite `Φ_x ∘ C.inv` on the tube. -/
noncomputable def capChartInvMap (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k))
    {ε : ℝ} (C : Work.Tubular.TubeChart E ε) (x : V.pt)
    (hcont : Continuous fun p : Work.Tubular.NormalTotal E =>
      chartAffine E x (cap E ε p)) : C(↥C.U, Work.Tubular.Euc (8 + k)) :=
  (capChartMap E C x hcont).comp (Work.ThomBordism.tubeInvMap E C)

theorem capChartInvMap_eq_tubeTransMap (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k))
    {ε : ℝ} (C : Work.Tubular.TubeChart E ε) (x : V.pt)
    (hcont : Continuous fun p : Work.Tubular.NormalTotal E =>
      chartAffine E x (cap E ε p)) :
    capChartInvMap E C x hcont = tubeTransMap E C x :=
  ContinuousMap.ext (fun y => chartAffine_cap_inv_coe E C x y)

/-- **The pushforward of `δ` along the translation is the pushforward of the collapse class along
the capped ambient chart.** -/
theorem tubeTransChains_homology_eq (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k))
    {ε : ℝ} (C : Work.Tubular.TubeChart E ε)
    (g : C(OnePoint (Work.Tubular.Euc (8 + k)), OnePoint (Work.Tubular.NormalTotal E)))
    (hg : ∀ y, y ∉ C.openTube → g (OnePoint.some y) = OnePoint.infty)
    {R : ℝ} (hR : 0 ≤ R) (hbox : ∀ y ∈ C.U, ∀ j : Fin (8 + k), |y j| < R) (x : V.pt)
    (hcont : Continuous fun p : Work.Tubular.NormalTotal E =>
      chartAffine E x (cap E ε p))
    (δ : (Work.Cohomology.relChains (TopCat.of ↥C.U) (tubeInvPunct E C)).homology (k + 8))
    (hδ : (HomologicalComplex.homologyMap
        (Work.Cohomology.relChainsMapOf (TopCat.of ↥C.U)
          (TopCat.of (Work.Tubular.NormalTotal E)) (tubeInvPunct E C)
          (Work.Tubular.normalNonzero E) (TopCat.ofHom (Work.ThomBordism.tubeInvMap E C))
          (tubeInvSub E C) (tubeInv_compat E C)) (k + 8)).hom δ
      = Work.Tubular.collapseRelK8 C g hg hR hbox) :
    (HomologicalComplex.homologyMap (tubeTransChains E C x) (k + 8)).hom δ
      = (HomologicalComplex.homologyMap (capChartChains E C x hcont) (k + 8)).hom
          (Work.Tubular.collapseRelK8 C g hg hR hbox) := by
  -- the compatibility of the composite `C.inv ≫ Φ_x` with the translation
  have W2 : Work.Cohomology.subtypeIncl (TopCat.of ↥C.U) (tubeInvPunct E C)
        ≫ TopCat.ofHom (capChartInvMap E C x hcont)
      = TopCat.ofHom (tubeTransSub E C x)
        ≫ Work.Cohomology.subtypeIncl (TopCat.of (Work.Tubular.Euc (8 + k)))
            ({0}ᶜ : Set (Work.Tubular.Euc (8 + k))) := by
    apply TopCat.ext
    intro a
    exact chartAffine_cap_inv E C x (((a.1 : ↥C.U)).2)
  -- the two maps on the punctured parts agree
  have hg_eq : (tubeInvSub E C ≫ capChartSub E C x hcont)
      = TopCat.ofHom (tubeTransSub E C x) := by
    apply TopCat.ext
    intro a
    apply Subtype.ext
    exact chartAffine_cap_inv E C x (((a.1 : ↥C.U)).2)
  -- functoriality of `relChainsMapOf`
  have hcomp := Work.Cohomology.relChainsMapOf_comp (X := TopCat.of ↥C.U)
    (Y := TopCat.of (Work.Tubular.NormalTotal E))
    (Z := TopCat.of (Work.Tubular.Euc (8 + k)))
    (A := tubeInvPunct E C) (B := Work.Tubular.normalNonzero E)
    (C := ({0}ᶜ : Set (Work.Tubular.Euc (8 + k))))
    (f := TopCat.ofHom (Work.ThomBordism.tubeInvMap E C)) (g := tubeInvSub E C)
    (w := tubeInv_compat E C)
    (f' := TopCat.ofHom (capChartMap E C x hcont)) (g' := capChartSub E C x hcont)
    (w' := capChartSub_compat E C x hcont)
    (w'' := by apply TopCat.ext; intro a; rfl)
  -- `tubeTransChains` is the relative chain map of the composite `C.inv ≫ Φ_x`
  have hT : tubeTransChains E C x
      = Work.Cohomology.relChainsMapOf (TopCat.of ↥C.U)
          (TopCat.of (Work.Tubular.Euc (8 + k))) (tubeInvPunct E C)
          ({0}ᶜ : Set (Work.Tubular.Euc (8 + k)))
          (TopCat.ofHom (capChartInvMap E C x hcont)) (TopCat.ofHom (tubeTransSub E C x)) W2 :=
    Work.ThomBordism.doubleFC.relChainsMapOf_congr
      (X := TopCat.of ↥C.U) (Y := TopCat.of (Work.Tubular.Euc (8 + k)))
      (A := tubeInvPunct E C) (B := ({0}ᶜ : Set (Work.Tubular.Euc (8 + k))))
      (f := TopCat.ofHom (tubeTransMap E C x))
      (f' := TopCat.ofHom (capChartInvMap E C x hcont))
      (g := TopCat.ofHom (tubeTransSub E C x)) (g' := TopCat.ofHom (tubeTransSub E C x))
      (hf := congrArg TopCat.ofHom (capChartInvMap_eq_tubeTransMap E C x hcont).symm) (hg := rfl)
      (tubeTrans_compat E C x) W2
  have hCap : capChartChains E C x hcont
      = Work.Cohomology.relChainsMapOf (TopCat.of (Work.Tubular.NormalTotal E))
          (TopCat.of (Work.Tubular.Euc (8 + k))) (Work.Tubular.normalNonzero E)
          ({0}ᶜ : Set (Work.Tubular.Euc (8 + k)))
          (TopCat.ofHom (capChartMap E C x hcont)) (capChartSub E C x hcont)
          (capChartSub_compat E C x hcont) := rfl
  -- the relative chain map of the composite is the composite of the relative chain maps
  have hL : Work.Cohomology.relChainsMapOf (TopCat.of ↥C.U)
        (TopCat.of (Work.Tubular.Euc (8 + k))) (tubeInvPunct E C)
        ({0}ᶜ : Set (Work.Tubular.Euc (8 + k)))
        (TopCat.ofHom (capChartInvMap E C x hcont)) (TopCat.ofHom (tubeTransSub E C x)) W2
      = Work.Cohomology.relChainsMapOf (TopCat.of ↥C.U)
          (TopCat.of (Work.Tubular.NormalTotal E)) (tubeInvPunct E C)
          (Work.Tubular.normalNonzero E) (TopCat.ofHom (Work.ThomBordism.tubeInvMap E C))
          (tubeInvSub E C) (tubeInv_compat E C)
        ≫ Work.Cohomology.relChainsMapOf (TopCat.of (Work.Tubular.NormalTotal E))
            (TopCat.of (Work.Tubular.Euc (8 + k))) (Work.Tubular.normalNonzero E)
            ({0}ᶜ : Set (Work.Tubular.Euc (8 + k)))
            (TopCat.ofHom (capChartMap E C x hcont)) (capChartSub E C x hcont)
            (capChartSub_compat E C x hcont) :=
    (Work.ThomBordism.doubleFC.relChainsMapOf_congr rfl hg_eq _ _).symm.trans hcomp.symm
  rw [hT, hCap, hL, HomologicalComplex.homologyMap_comp]
  change (ModuleCat.Hom.hom (HomologicalComplex.homologyMap
      (Work.Cohomology.relChainsMapOf (TopCat.of (Work.Tubular.NormalTotal E))
        (TopCat.of (Work.Tubular.Euc (8 + k))) (Work.Tubular.normalNonzero E)
        ({0}ᶜ : Set (Work.Tubular.Euc (8 + k)))
        (TopCat.ofHom (capChartMap E C x hcont)) (capChartSub E C x hcont)
        (capChartSub_compat E C x hcont)) (k + 8)))
      ((ModuleCat.Hom.hom (HomologicalComplex.homologyMap
        (Work.Cohomology.relChainsMapOf (TopCat.of ↥C.U)
          (TopCat.of (Work.Tubular.NormalTotal E)) (tubeInvPunct E C)
          (Work.Tubular.normalNonzero E) (TopCat.ofHom (Work.ThomBordism.tubeInvMap E C))
          (tubeInvSub E C) (tubeInv_compat E C)) (k + 8))) δ)
    = (ModuleCat.Hom.hom (HomologicalComplex.homologyMap
        (Work.Cohomology.relChainsMapOf (TopCat.of (Work.Tubular.NormalTotal E))
          (TopCat.of (Work.Tubular.Euc (8 + k))) (Work.Tubular.normalNonzero E)
          ({0}ᶜ : Set (Work.Tubular.Euc (8 + k)))
          (TopCat.ofHom (capChartMap E C x hcont)) (capChartSub E C x hcont)
          (capChartSub_compat E C x hcont)) (k + 8)))
      (Work.Tubular.collapseRelK8 C g hg hR hbox)
  rw [hδ]

/-! ## The capping composes with itself -/

theorem capCoeff_capCoeff {ε ε' r : ℝ} (hε' : 0 < ε') (hle : ε' ≤ ε) (hr : 0 ≤ r) :
    capCoeff ε' (min r ε) * capCoeff ε r = capCoeff ε' r := by
  have hε : 0 ≤ ε := le_trans (le_of_lt hε') hle
  have hs : 0 ≤ min r ε := le_min hr hε
  have h1 : capCoeff ε' (min r ε) * min r ε = min r ε' := by
    rw [capCoeff_mul (ε := ε') (le_of_lt hε') hs, min_comm (min r ε) ε', ← min_assoc,
      min_comm ε' r, min_assoc, min_eq_left hle]
  have h2 : capCoeff ε r * r = min r ε := capCoeff_mul hε hr
  have h3 : capCoeff ε' r * r = min r ε' := capCoeff_mul (ε := ε') (le_of_lt hε') hr
  rcases eq_or_lt_of_le hr with h | h
  · subst h
    simp [capCoeff, min_eq_left hε]
  · exact mul_right_cancel₀ (ne_of_gt h) (by rw [mul_assoc, h2, h1, h3])

theorem cap_cap (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k)) {ε ε' : ℝ}
    (hε' : 0 < ε') (hle : ε' ≤ ε) (p : Work.Tubular.NormalTotal E) :
    cap E ε' (cap E ε p) = cap E ε' p := by
  have hε : 0 ≤ ε := le_trans (le_of_lt hε') hle
  have hr : 0 ≤ Work.Tubular.normalNorm E p := Work.Tubular.normalNorm_nonneg E p
  refine Subtype.ext (Prod.ext ?_ ?_)
  · simp only [cap, Work.ThomBordism.radialRescale_proj]
  · simp only [cap, Work.ThomBordism.radialRescale_coe]
    rw [Work.ThomBordism.normalNorm_radialRescale,
      abs_of_nonneg (Work.ThomBordism.capCoeff_nonneg hε hr),
      Work.ThomBordism.capCoeff_mul hε hr, smul_smul]
    congr 1
    exact capCoeff_capCoeff hε' hle hr

/-! ## Positive dilations of the model space -/

/-- The dilation `v ↦ a • v` of `ℝ^k`. -/
noncomputable def dilMap (k : ℕ) (a : ℝ) : C(Work.Tubular.Euc k, Work.Tubular.Euc k) :=
  ⟨fun v => a • v, continuous_id.const_smul a⟩

theorem dilMap_apply (k : ℕ) (a : ℝ) (v : Work.Tubular.Euc k) : dilMap k a v = a • v := rfl

theorem dilMap_mem (k : ℕ) {a : ℝ} (ha : a ≠ 0) :
    ∀ v ∈ ({0}ᶜ : Set (Work.Tubular.Euc k)), dilMap k a v ∈ ({0}ᶜ : Set (Work.Tubular.Euc k)) :=
  fun v hv => by
    rw [Set.mem_compl_iff, Set.mem_singleton_iff] at hv ⊢
    rw [dilMap_apply]
    exact smul_ne_zero ha hv

/-- **A positive dilation of the model space does not change the model class.** -/
theorem dilMap_pullback_stdModelGen (k : ℕ) {a : ℝ} (ha : 0 < a) :
    (Work.Thom.relCohMap (dilMap k a) ({0}ᶜ : Set (Work.Tubular.Euc k))
        ({0}ᶜ : Set (Work.Tubular.Euc k)) (dilMap_mem k (ne_of_gt ha)) ℤ k).hom
        (stdModelGen k)
      = stdModelGen k := by
  have hbase : Continuous fun p : unitInterval × Work.Tubular.Euc k =>
      ((1 - (p.1 : ℝ)) * a + (p.1 : ℝ)) • p.2 :=
    (((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).mul
        continuous_const).add (continuous_subtype_val.comp continuous_fst)).smul continuous_snd
  have hpos : ∀ p : unitInterval × Work.Tubular.Euc k,
      0 < (1 - (p.1 : ℝ)) * a + (p.1 : ℝ) := by
    intro p
    have h1 : (0 : ℝ) ≤ (p.1 : ℝ) := unitInterval.nonneg p.1
    have h2 : (p.1 : ℝ) ≤ 1 := unitInterval.le_one p.1
    rcases lt_or_eq_of_le h2 with h3 | h3
    · have h4 : 0 < 1 - (p.1 : ℝ) := by linarith
      nlinarith [mul_pos h4 ha]
    · rw [h3]; norm_num
  have hmem : ∀ (t : unitInterval) x, x ∈ ({0}ᶜ : Set (Work.Tubular.Euc k)) →
      (((1 - (t : ℝ)) * a + (t : ℝ)) • x) ∈ ({0}ᶜ : Set (Work.Tubular.Euc k)) := by
    intro t x hx
    rw [Set.mem_compl_iff, Set.mem_singleton_iff] at hx ⊢
    exact smul_ne_zero (ne_of_gt (hpos (t, x))) hx
  have hhom := Work.Thom.relCohMap_homotopic ({0}ᶜ : Set (Work.Tubular.Euc k))
    ({0}ᶜ : Set (Work.Tubular.Euc k)) (dilMap_mem k (ne_of_gt ha))
    (fun _ hx => hx)
    (ContinuousMap.Homotopy.mk ⟨fun p : unitInterval × Work.Tubular.Euc k =>
        ((1 - (p.1 : ℝ)) * a + (p.1 : ℝ)) • p.2, hbase⟩
      (fun v => by
        show ((1 - ((0 : unitInterval) : ℝ)) * a + ((0 : unitInterval) : ℝ)) • v
          = dilMap k a v
        rw [dilMap_apply]; norm_num)
      (fun v => by
        show ((1 - ((1 : unitInterval) : ℝ)) * a + ((1 : unitInterval) : ℝ)) • v
          = (ContinuousMap.id (Work.Tubular.Euc k)) v
        norm_num))
    hmem ℤ k
  have hone : Work.Thom.relCohMap (ContinuousMap.id (Work.Tubular.Euc k))
      ({0}ᶜ : Set (Work.Tubular.Euc k)) ({0}ᶜ : Set (Work.Tubular.Euc k)) (fun _ hx => hx)
      ℤ k = 𝟙 ((Work.Thom.RelCoh ℤ k (Work.Tubular.Euc k)
        ({0}ᶜ : Set (Work.Tubular.Euc k)))) := Work.Thom.relCohMap_id _ ℤ k
  rw [hhom, hone]
  rfl



/-! ## The zero-section point is not on the punctured set -/

/-- The zero-section point over `x` does not lie on the punctured zero section. -/
theorem zeroSectionPunctPt_notMem {V : Work.ThomBordism.Man8} {k : ℕ}
    (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k)) (x : V.pt) :
    Work.Tubular.zeroSectionPunctPt E x ∉ Work.Tubular.onePointNonzero E := by
  rw [Work.Tubular.mem_onePointNonzero]
  rintro (h | ⟨q, hq, hqeq⟩)
  · exact OnePoint.coe_ne_infty _ h
  · have h2 : q = Work.Tubular.zeroSectionNormal E x := by
      have h3 : (OnePoint.some q : OnePoint (Work.Tubular.NormalTotal E))
          = OnePoint.some (Work.Tubular.zeroSectionNormal E x) := by
        rw [hqeq]
        rfl
      exact OnePoint.coe_injective h3
    rw [h2, Work.Tubular.zeroSectionNormal_apply, Work.Tubular.normalNorm_mk,
      norm_zero] at hq
    exact hq rfl

/-! ## The naturality of the cokernel projection along an inclusion of complements -/

/-- **The cokernel projection is natural in the complement**: for `A ⊆ B` and an absolute class `x`,
the `B`-localisation is the image of the `A`-localisation under the canonical map. -/
theorem coker_pi_incl_homology (X : TopCat) (A B : Set ↥X) (hAB : A ⊆ B) (n : ℕ)
    (x : (Work.Cohomology.singularChains ℤ X).homology n) :
    (ModuleCat.Hom.hom (HomologicalComplex.homologyMap
        (CategoryTheory.Limits.cokernel.π (Work.Cohomology.inclChains X B)) n)) x
      = (ModuleCat.Hom.hom (HomologicalComplex.homologyMap
          (Work.Cohomology.relChainsMapOf X X A B (𝟙 X)
            (TopCat.ofHom ⟨fun y : ↥A => ⟨y.1, hAB y.2⟩,
              Continuous.subtype_mk continuous_subtype_val _⟩)
            (by apply TopCat.ext; intro a; rfl)) n))
        ((ModuleCat.Hom.hom (HomologicalComplex.homologyMap
          (CategoryTheory.Limits.cokernel.π (Work.Cohomology.inclChains X A)) n)) x) := by
  have h := Work.Tubular.TubeClass.cokernel_pi_chainMap_homology
    (X := X) (Y := X) (A := A) (B := B) (f := 𝟙 X)
    (g := TopCat.ofHom ⟨fun y : ↥A => ⟨y.1, hAB y.2⟩,
      Continuous.subtype_mk continuous_subtype_val _⟩)
    (w := by apply TopCat.ext; intro a; rfl) n x
  have h1 : HomologicalComplex.homologyMap (Work.Cohomology.chainMap ℤ X X (𝟙 X)) n = 𝟙 _ := by
    rw [show Work.Cohomology.chainMap ℤ X X (𝟙 X) = 𝟙 _ from
      CategoryTheory.Functor.map_id _ _]
    exact HomologicalComplex.homologyMap_id _ n
  rw [h1] at h
  simpa using h

/-! ## The reduction to the `ν⁺`-world -/

/-- **The value is the pairing, in the Thom-space world `(ν⁺, onePointNonzero E)`, of the
`ν⁺`-avatar `β` of the chart model class with the image of the collapse's Hurewicz class.** -/
theorem value_eq_piStar {V : Work.ThomBordism.Man8} {k : ℕ}
    (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k)) {ε : ℝ}
    (C : Work.Tubular.TubeChart E ε)
    (g : C(OnePoint (Work.Tubular.Euc (8 + k)), OnePoint (Work.Tubular.NormalTotal E)))
    (hg : ∀ y, y ∉ C.openTube → g (OnePoint.some y) = OnePoint.infty)
    {R : ℝ} (hR : 0 ≤ R) (hbox : ∀ y ∈ C.U, ∀ j : Fin (8 + k), |y j| < R) (x : V.pt)
    (δ : (Work.Cohomology.relChains (TopCat.of ↥C.U)
        (Work.ThomBordism.tubeInvPunct E C)).homology (k + 8))
    (hδ : Work.ThomBordism.tubeInvHomology E C δ
        = Work.Tubular.collapseRelK8 C g hg hR hbox)
    (β : Work.Thom.RelCoh ℤ (k + 8) (OnePoint (Work.Tubular.NormalTotal E))
      (Work.Tubular.onePointNonzero E))
    (hβ : Work.Tubular.compPull E (k + 8) β
      = (Nat.add_comm 8 k) ▸ chartModelClass E C x (continuous_chartAffine_cap E C x)) :
    Work.Tubular.relKronH (TopCat.of ↥C.U) (Work.ThomBordism.tubeInvPunct E C) (k + 8)
        ((Nat.add_comm 8 k) ▸ ambientStandardClass E C x) δ
      = Work.Tubular.relKronH (TopCat.of (OnePoint (Work.Tubular.NormalTotal E)))
          (Work.Tubular.onePointNonzero E) (k + 8) β
          ((ModuleCat.Hom.hom (HomologicalComplex.homologyMap
            (CategoryTheory.Limits.cokernel.π
              (Work.Cohomology.inclChains (TopCat.of (OnePoint (Work.Tubular.NormalTotal E)))
                (Work.Tubular.onePointNonzero E))) (k + 8)))
            ((Nat.add_comm 8 k) ▸ Work.Stems.hurewiczChain (8 + k) (by omega) OnePoint.infty
              (Work.Tubular.tubeGenLoopOnePoint C g hg hR hbox))) := by
  rw [value_eq_chart E C g hg hR hbox x δ hδ, ← hβ]
  exact (Work.Tubular.relKronH_collapseRelK8 C g hg hR hbox β).symm

/-- **The value localises at the zero-section point**: it is the pairing of any extension `βf` of the
`ν⁺`-avatar of the chart model class to the pair `(ν⁺, ν⁺∖{x₀})` with the localisation at `x₀` of the
collapse's Hurewicz class. -/
theorem value_eq_piStar_fine {V : Work.ThomBordism.Man8} {k : ℕ}
    (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k)) {ε : ℝ}
    (C : Work.Tubular.TubeChart E ε)
    (g : C(OnePoint (Work.Tubular.Euc (8 + k)), OnePoint (Work.Tubular.NormalTotal E)))
    (hg : ∀ y, y ∉ C.openTube → g (OnePoint.some y) = OnePoint.infty)
    {R : ℝ} (hR : 0 ≤ R) (hbox : ∀ y ∈ C.U, ∀ j : Fin (8 + k), |y j| < R) (x : V.pt)
    (δ : (Work.Cohomology.relChains (TopCat.of ↥C.U)
        (Work.ThomBordism.tubeInvPunct E C)).homology (k + 8))
    (hδ : Work.ThomBordism.tubeInvHomology E C δ
        = Work.Tubular.collapseRelK8 C g hg hR hbox)
    (β : Work.Thom.RelCoh ℤ (k + 8) (OnePoint (Work.Tubular.NormalTotal E))
      (Work.Tubular.onePointNonzero E))
    (hβ : Work.Tubular.compPull E (k + 8) β
      = (Nat.add_comm 8 k) ▸ chartModelClass E C x (continuous_chartAffine_cap E C x))
    (βf : Work.Thom.RelCoh ℤ (k + 8) (OnePoint (Work.Tubular.NormalTotal E))
      ({Work.Tubular.zeroSectionPunctPt E x}ᶜ : Set (OnePoint (Work.Tubular.NormalTotal E))))
    (hβf : (Work.Thom.relCohMap (ContinuousMap.id (OnePoint (Work.Tubular.NormalTotal E)))
        (Work.Tubular.onePointNonzero E)
        ({Work.Tubular.zeroSectionPunctPt E x}ᶜ : Set (OnePoint (Work.Tubular.NormalTotal E)))
        (fun y hy => fun hcon => zeroSectionPunctPt_notMem E x (hcon ▸ hy)) ℤ (k + 8)).hom βf = β) :
    Work.Tubular.relKronH (TopCat.of ↥C.U) (Work.ThomBordism.tubeInvPunct E C) (k + 8)
        ((Nat.add_comm 8 k) ▸ ambientStandardClass E C x) δ
      = Work.Tubular.relKronH (TopCat.of (OnePoint (Work.Tubular.NormalTotal E)))
          ({Work.Tubular.zeroSectionPunctPt E x}ᶜ : Set (OnePoint (Work.Tubular.NormalTotal E)))
          (k + 8) βf
          ((ModuleCat.Hom.hom (HomologicalComplex.homologyMap
            (CategoryTheory.Limits.cokernel.π
              (Work.Cohomology.inclChains (TopCat.of (OnePoint (Work.Tubular.NormalTotal E)))
                ({Work.Tubular.zeroSectionPunctPt E x}ᶜ :
                  Set (OnePoint (Work.Tubular.NormalTotal E))))) (k + 8)))
            ((Nat.add_comm 8 k) ▸ Work.Stems.hurewiczChain (8 + k) (by omega) OnePoint.infty
              (Work.Tubular.tubeGenLoopOnePoint C g hg hR hbox))) := by
  rw [value_eq_piStar E C g hg hR hbox x δ hδ β hβ]
  have hAB : Work.Tubular.onePointNonzero E ⊆
      ({Work.Tubular.zeroSectionPunctPt E x}ᶜ : Set (OnePoint (Work.Tubular.NormalTotal E))) :=
    fun y hy => fun hcon => zeroSectionPunctPt_notMem E x (hcon ▸ hy)
  rw [coker_pi_incl_homology (TopCat.of (OnePoint (Work.Tubular.NormalTotal E)))
    (Work.Tubular.onePointNonzero E)
    ({Work.Tubular.zeroSectionPunctPt E x}ᶜ : Set (OnePoint (Work.Tubular.NormalTotal E)))
    hAB (k + 8)]
  rw [hβf.symm]
  exact Work.Tubular.relKronH_natural (X := TopCat.of (OnePoint (Work.Tubular.NormalTotal E)))
    (Y := TopCat.of (OnePoint (Work.Tubular.NormalTotal E)))
    (A := Work.Tubular.onePointNonzero E)
    (B := ({Work.Tubular.zeroSectionPunctPt E x}ᶜ : Set (OnePoint (Work.Tubular.NormalTotal E))))
    (f := 𝟙 (TopCat.of (OnePoint (Work.Tubular.NormalTotal E))))
    (g := TopCat.ofHom ⟨fun y : ↥(Work.Tubular.onePointNonzero E) => ⟨y.1, hAB y.2⟩,
      Continuous.subtype_mk continuous_subtype_val _⟩)
    (hf := hAB) (w := by apply TopCat.ext; intro a; rfl) (n := k + 8) βf _

/-! ## The localisation of the Hurewicz class of the collapse -/

/-- The base point `y₀` of the sphere at which the collapse maps to the zero-section point. -/
noncomputable def collapsePt {k : ℕ} (q₀ : Fin (8 + k) → unitInterval) : Work.Stems.sphere (8 + k) :=
  Work.Stems.collapseMap (8 + k) (by omega) q₀

/-- The collapse `S^{8+k} → ν⁺` as a map of pairs `(S^{8+k}, S^{8+k}∖{y₀}) → (ν⁺, ν⁺∖{x₀})`. -/
noncomputable def collapsePairMap {V : Work.ThomBordism.Man8} {k : ℕ}
    {E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k)} {ε : ℝ}
    (C : Work.Tubular.TubeChart E ε) {R : ℝ} (hR : 0 ≤ R)
    (hbox : ∀ y ∈ C.U, ∀ i : Fin (8 + k), |y i| < R)
    (g : C(OnePoint (Work.Tubular.Euc (8 + k)), OnePoint (Work.Tubular.NormalTotal E)))
    (hg : ∀ y, y ∉ C.openTube → g (OnePoint.some y) = OnePoint.infty)
    (hg2 : ∀ y, y ∈ C.openTube →
      g (OnePoint.some y) = OnePoint.some (Work.Tubular.normalBlowUp E ε (C.inv y)))
    (v₀ : V.pt) (q₀ : Fin (8 + k) → unitInterval)
    (hq₀ : Work.Tubular.cubeToEuc (8 + k) R q₀ = E.e v₀) :
    TopCat.of ↥({collapsePt q₀}ᶜ : Set (Work.Stems.sphere (8 + k))) ⟶
      TopCat.of ↥({Work.Tubular.zeroSectionPunctPt E v₀}ᶜ :
        Set (OnePoint (Work.Tubular.NormalTotal E))) :=
  TopCat.ofHom ⟨fun y : ↥({collapsePt q₀}ᶜ : Set (Work.Stems.sphere (8 + k))) =>
      ⟨(Work.Stems.cubeLift (8 + k) (by omega)
          (Work.Tubular.tubeGenLoopOnePoint C g hg hR hbox)) y.1,
        fun hcon => y.2 (Work.Tubular.TubeClass.collapseFibre C hR hbox g hg hg2 v₀ q₀
          hq₀ y.1 hcon)⟩,
    Continuous.subtype_mk ((Work.Stems.cubeLift (8 + k) (by omega)
        (Work.Tubular.tubeGenLoopOnePoint C g hg hR hbox)).continuous.comp
      continuous_subtype_val) _⟩

/-- The compatibility of the collapse map with the subspace inclusions. -/
theorem collapsePairMap_compat {V : Work.ThomBordism.Man8} {k : ℕ}
    {E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k)} {ε : ℝ}
    (C : Work.Tubular.TubeChart E ε) {R : ℝ} (hR : 0 ≤ R)
    (hbox : ∀ y ∈ C.U, ∀ i : Fin (8 + k), |y i| < R)
    (g : C(OnePoint (Work.Tubular.Euc (8 + k)), OnePoint (Work.Tubular.NormalTotal E)))
    (hg : ∀ y, y ∉ C.openTube → g (OnePoint.some y) = OnePoint.infty)
    (hg2 : ∀ y, y ∈ C.openTube →
      g (OnePoint.some y) = OnePoint.some (Work.Tubular.normalBlowUp E ε (C.inv y)))
    (v₀ : V.pt) (q₀ : Fin (8 + k) → unitInterval)
    (hq₀ : Work.Tubular.cubeToEuc (8 + k) R q₀ = E.e v₀) :
    Work.Cohomology.subtypeIncl (TopCat.of (Work.Stems.sphere (8 + k)))
        ({collapsePt q₀}ᶜ : Set (Work.Stems.sphere (8 + k)))
        ≫ TopCat.ofHom (Work.Stems.cubeLift (8 + k) (by omega)
            (Work.Tubular.tubeGenLoopOnePoint C g hg hR hbox))
      = collapsePairMap C hR hbox g hg hg2 v₀ q₀ hq₀
        ≫ Work.Cohomology.subtypeIncl (TopCat.of (OnePoint (Work.Tubular.NormalTotal E)))
            ({Work.Tubular.zeroSectionPunctPt E v₀}ᶜ :
              Set (OnePoint (Work.Tubular.NormalTotal E))) := by
  apply TopCat.ext
  intro a
  rfl

/-- **(C)**  The localisation at the zero-section point of the Hurewicz class of the collapse is the
push-forward, along the collapse viewed as a map of pairs
`(S^{8+k}, S^{8+k}∖{y₀}) → (ν⁺, ν⁺∖{x₀})`, of the localisation of the sphere generator at `y₀`. -/
theorem localisation_hurewiczChain_collapse {V : Work.ThomBordism.Man8} {k : ℕ}
    {E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k)} {ε : ℝ}
    (C : Work.Tubular.TubeChart E ε) {R : ℝ} (hR : 0 ≤ R)
    (hbox : ∀ y ∈ C.U, ∀ i : Fin (8 + k), |y i| < R)
    (g : C(OnePoint (Work.Tubular.Euc (8 + k)), OnePoint (Work.Tubular.NormalTotal E)))
    (hg : ∀ y, y ∉ C.openTube → g (OnePoint.some y) = OnePoint.infty)
    (hg2 : ∀ y, y ∈ C.openTube →
      g (OnePoint.some y) = OnePoint.some (Work.Tubular.normalBlowUp E ε (C.inv y)))
    (v₀ : V.pt) (q₀ : Fin (8 + k) → unitInterval)
    (hq₀ : Work.Tubular.cubeToEuc (8 + k) R q₀ = E.e v₀) :
    Work.Tubular.localisationPunct E v₀ (8 + k)
        (Work.Stems.hurewiczChain (8 + k) (by omega) OnePoint.infty
          (Work.Tubular.tubeGenLoopOnePoint C g hg hR hbox))
      = (ModuleCat.Hom.hom (HomologicalComplex.homologyMap
          (Work.Cohomology.relChainsMapOf
            (TopCat.of (Work.Stems.sphere (8 + k)))
            (TopCat.of (OnePoint (Work.Tubular.NormalTotal E)))
            ({collapsePt q₀}ᶜ : Set (Work.Stems.sphere (8 + k)))
            ({Work.Tubular.zeroSectionPunctPt E v₀}ᶜ : Set (OnePoint (Work.Tubular.NormalTotal E)))
            (TopCat.ofHom (Work.Stems.cubeLift (8 + k) (by omega)
              (Work.Tubular.tubeGenLoopOnePoint C g hg hR hbox)))
            (collapsePairMap C hR hbox g hg hg2 v₀ q₀ hq₀)
            (collapsePairMap_compat C hR hbox g hg hg2 v₀ q₀ hq₀)) (8 + k)))
        ((ModuleCat.Hom.hom (HomologicalComplex.homologyMap
          (CategoryTheory.Limits.cokernel.π (Work.Cohomology.inclChains
            (TopCat.of (Work.Stems.sphere (8 + k)))
            ({collapsePt q₀}ᶜ : Set (Work.Stems.sphere (8 + k)))))
          (8 + k))) (Work.Stems.sphereGenerator (8 + k) (by omega))) := by
  exact Work.Tubular.TubeClass.cokernel_pi_chainMap_homology _ (8 + k) _

/-- The collapse `S^{8+k} → ν⁺` keeps the complement of `y₀` inside the complement of `x₀`. -/
theorem collapseLift_pair {V : Work.ThomBordism.Man8} {k : ℕ}
    {E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k)} {ε : ℝ}
    (C : Work.Tubular.TubeChart E ε) {R : ℝ} (hR : 0 ≤ R)
    (hbox : ∀ y ∈ C.U, ∀ i : Fin (8 + k), |y i| < R)
    (g : C(OnePoint (Work.Tubular.Euc (8 + k)), OnePoint (Work.Tubular.NormalTotal E)))
    (hg : ∀ y, y ∉ C.openTube → g (OnePoint.some y) = OnePoint.infty)
    (hg2 : ∀ y, y ∈ C.openTube →
      g (OnePoint.some y) = OnePoint.some (Work.Tubular.normalBlowUp E ε (C.inv y)))
    (v₀ : V.pt) (q₀ : Fin (8 + k) → unitInterval)
    (hq₀ : Work.Tubular.cubeToEuc (8 + k) R q₀ = E.e v₀) :
    ∀ y ∈ ({collapsePt q₀}ᶜ : Set (Work.Stems.sphere (8 + k))),
      (Work.Stems.cubeLift (8 + k) (by omega)
        (Work.Tubular.tubeGenLoopOnePoint C g hg hR hbox)) y
        ∈ ({Work.Tubular.zeroSectionPunctPt E v₀}ᶜ :
            Set (OnePoint (Work.Tubular.NormalTotal E))) :=
  fun y hy => fun hcon =>
    hy (Work.Tubular.TubeClass.collapseFibre C hR hbox g hg hg2 v₀ q₀ hq₀ y hcon)

/-- **The localisation of the collapse's Hurewicz class, read against a `ν⁺`-class**: the pairing on
`(ν⁺, ν⁺∖{x₀})` of a class with the localised Hurewicz class is the pairing on the sphere of its
pull-back with the localised sphere generator. -/
theorem localisation_eq_F {V : Work.ThomBordism.Man8} {k : ℕ}
    {E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k)} {ε : ℝ}
    (C : Work.Tubular.TubeChart E ε) {R : ℝ} (hR : 0 ≤ R)
    (hbox : ∀ y ∈ C.U, ∀ i : Fin (8 + k), |y i| < R)
    (g : C(OnePoint (Work.Tubular.Euc (8 + k)), OnePoint (Work.Tubular.NormalTotal E)))
    (hg : ∀ y, y ∉ C.openTube → g (OnePoint.some y) = OnePoint.infty)
    (hg2 : ∀ y, y ∈ C.openTube →
      g (OnePoint.some y) = OnePoint.some (Work.Tubular.normalBlowUp E ε (C.inv y)))
    (v₀ : V.pt) (q₀ : Fin (8 + k) → unitInterval)
    (hq₀ : Work.Tubular.cubeToEuc (8 + k) R q₀ = E.e v₀)
    (βf : Work.Thom.RelCoh ℤ (8 + k) (OnePoint (Work.Tubular.NormalTotal E))
      ({Work.Tubular.zeroSectionPunctPt E v₀}ᶜ : Set (OnePoint (Work.Tubular.NormalTotal E)))) :
    Work.Tubular.relKronH (TopCat.of (OnePoint (Work.Tubular.NormalTotal E)))
        ({Work.Tubular.zeroSectionPunctPt E v₀}ᶜ : Set (OnePoint (Work.Tubular.NormalTotal E)))
        (8 + k) βf
        (Work.Tubular.localisationPunct E v₀ (8 + k)
          (Work.Stems.hurewiczChain (8 + k) (by omega) OnePoint.infty
            (Work.Tubular.tubeGenLoopOnePoint C g hg hR hbox)))
      = Work.Tubular.relKronH (TopCat.of (Work.Stems.sphere (8 + k)))
          ({collapsePt q₀}ᶜ : Set (Work.Stems.sphere (8 + k))) (8 + k)
          ((Work.Thom.relCohMap (Work.Stems.cubeLift (8 + k) (by omega)
              (Work.Tubular.tubeGenLoopOnePoint C g hg hR hbox))
            ({collapsePt q₀}ᶜ : Set (Work.Stems.sphere (8 + k)))
            ({Work.Tubular.zeroSectionPunctPt E v₀}ᶜ :
              Set (OnePoint (Work.Tubular.NormalTotal E)))
            (collapseLift_pair C hR hbox g hg hg2 v₀ q₀ hq₀) ℤ (8 + k)).hom βf)
          ((ModuleCat.Hom.hom (HomologicalComplex.homologyMap
            (CategoryTheory.Limits.cokernel.π (Work.Cohomology.inclChains
              (TopCat.of (Work.Stems.sphere (8 + k)))
              ({collapsePt q₀}ᶜ : Set (Work.Stems.sphere (8 + k))))) (8 + k)))
            (Work.Stems.sphereGenerator (8 + k) (by omega))) := by
  rw [localisation_hurewiczChain_collapse C hR hbox g hg hg2 v₀ q₀ hq₀]
  exact (Work.Tubular.relKronH_natural (X := TopCat.of (Work.Stems.sphere (8 + k)))
    (Y := TopCat.of (OnePoint (Work.Tubular.NormalTotal E)))
    (A := ({collapsePt q₀}ᶜ : Set (Work.Stems.sphere (8 + k))))
    (B := ({Work.Tubular.zeroSectionPunctPt E v₀}ᶜ :
      Set (OnePoint (Work.Tubular.NormalTotal E))))
    (f := TopCat.ofHom (Work.Stems.cubeLift (8 + k) (by omega)
      (Work.Tubular.tubeGenLoopOnePoint C g hg hR hbox)))
    (g := collapsePairMap C hR hbox g hg hg2 v₀ q₀ hq₀)
    (hf := collapseLift_pair C hR hbox g hg hg2 v₀ q₀ hq₀)
    (w := collapsePairMap_compat C hR hbox g hg hg2 v₀ q₀ hq₀)
    (n := 8 + k) βf _).symm

/-! ## The reduction of the value to the ambient sphere

The value is the pairing, on the sphere `S^{8+k} = OnePoint (ℝ^{8+k})`, of the translated standard
class `(T_{-p})^*σ` with the push-forward of the tube class `δ` into the sphere.  This separates the
one *convention* (`σ`, `u₀`) from the datum: by `constancy_translated_local_pairing` the pairing with
a *fixed* local class `locClass u₀ (some p)` is independent of `p` — hence of the whole datum.
-/

/-- The inclusion of the tube into the one-point compactification `S^{8+k} = OnePoint (ℝ^{8+k})`. -/
noncomputable def tubeToSphereMap {V : Work.ThomBordism.Man8} {k : ℕ}
    {E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k)} {ε : ℝ}
    (C : Work.Tubular.TubeChart E ε) : C(↥C.U, OnePoint (Work.Tubular.Euc (8 + k))) :=
  ⟨fun y => OnePoint.some (y : Work.Tubular.Euc (8 + k)),
    OnePoint.continuous_coe.comp continuous_subtype_val⟩

/-- The same inclusion on the punctured parts. -/
noncomputable def tubeToSphereSub {V : Work.ThomBordism.Man8} {k : ℕ}
    {E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k)} {ε : ℝ}
    (C : Work.Tubular.TubeChart E ε) (x : V.pt) :
    C(↥(Work.ThomBordism.tubeInvPunct E C),
      ↥(({OnePoint.some (E.e x)}ᶜ : Set (OnePoint (Work.Tubular.Euc (8 + k)))))) :=
  ⟨fun y => ⟨OnePoint.some ((y.1 : ↥C.U) : Work.Tubular.Euc (8 + k)),
      fun hcon => Work.ThomBordism.tubeInvPunct_sub E C x y.2 (OnePoint.coe_injective hcon)⟩,
    Continuous.subtype_mk
      (OnePoint.continuous_coe.comp
        (continuous_subtype_val.comp continuous_subtype_val)) _⟩

/-- The two inclusions of the tube pair are compatible. -/
theorem tubeToSphere_compat {V : Work.ThomBordism.Man8} {k : ℕ}
    {E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k)} {ε : ℝ}
    (C : Work.Tubular.TubeChart E ε) (x : V.pt) :
    Work.Cohomology.subtypeIncl (TopCat.of ↥C.U) (Work.ThomBordism.tubeInvPunct E C)
        ≫ TopCat.ofHom (tubeToSphereMap C)
      = TopCat.ofHom (tubeToSphereSub C x)
        ≫ Work.Cohomology.subtypeIncl (TopCat.of (OnePoint (Work.Tubular.Euc (8 + k))))
            (({OnePoint.some (E.e x)}ᶜ : Set (OnePoint (Work.Tubular.Euc (8 + k))))) := by
  apply TopCat.ext
  intro a
  show tubeToSphereMap C (a : ↥C.U)
    = ((tubeToSphereSub C x a : ↥({OnePoint.some (E.e x)}ᶜ :
        Set (OnePoint (Work.Tubular.Euc (8 + k))))) : OnePoint (Work.Tubular.Euc (8 + k)))
  rfl

/-- The inclusion `ν ↪ ν⁺` as a map of pairs. -/
noncomputable def eucToOnePoint {k : ℕ} :
    C(Work.Tubular.Euc (8 + k), OnePoint (Work.Tubular.Euc (8 + k))) :=
  ⟨OnePoint.some, OnePoint.continuous_coe⟩

theorem eucToOnePoint_mem {k : ℕ} :
    ∀ v ∈ ({0}ᶜ : Set (Work.Tubular.Euc (8 + k))),
      eucToOnePoint v ∈ ({OnePoint.some (0 : Work.Tubular.Euc (8 + k))}ᶜ :
        Set (OnePoint (Work.Tubular.Euc (8 + k)))) :=
  fun v hv => fun hcon => hv (OnePoint.coe_injective hcon)

theorem eucToOnePoint_mem_comp {V : Work.ThomBordism.Man8} {k : ℕ}
    {E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k)} {ε : ℝ}
    (C : Work.Tubular.TubeChart E ε) (x : V.pt) :
    ∀ y ∈ Work.ThomBordism.tubeInvPunct E C,
      ((eucToOnePoint (k := k)).comp (Work.ThomBordism.tubeTransMap E C x)) y
        ∈ ({OnePoint.some (0 : Work.Tubular.Euc (8 + k))}ᶜ :
          Set (OnePoint (Work.Tubular.Euc (8 + k)))) :=
  fun y hy => eucToOnePoint_mem (k := k) _
    (Work.ThomBordism.tubeTrans_mem E C x y hy)

theorem transT_pair_mem {V : Work.ThomBordism.Man8} {k : ℕ}
    {E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k)} {ε : ℝ}
    (C : Work.Tubular.TubeChart E ε) (x : V.pt) :
    ∀ y ∈ Work.ThomBordism.tubeInvPunct E C,
      tubeToSphereMap C y
        ∈ ({OnePoint.some (E.e x)}ᶜ : Set (OnePoint (Work.Tubular.Euc (8 + k)))) :=
  fun y hy => fun hcon =>
    Work.ThomBordism.tubeInvPunct_sub E C x hy (OnePoint.coe_injective hcon)

theorem transT_pair_mem_comp {V : Work.ThomBordism.Man8} {k : ℕ}
    {E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k)} {ε : ℝ}
    (C : Work.Tubular.TubeChart E ε) (x : V.pt) :
    ∀ y ∈ Work.ThomBordism.tubeInvPunct E C,
      ((transT (-(E.e x))).comp (tubeToSphereMap C)) y
        ∈ ({OnePoint.some (0 : Work.Tubular.Euc (8 + k))}ᶜ :
          Set (OnePoint (Work.Tubular.Euc (8 + k)))) := by
  intro y hy
  show transT (-(E.e x)) (tubeToSphereMap C y)
    ∈ ({OnePoint.some (0 : Work.Tubular.Euc (8 + k))}ᶜ :
      Set (OnePoint (Work.Tubular.Euc (8 + k))))
  rw [show tubeToSphereMap C y = OnePoint.some (y : Work.Tubular.Euc (8 + k)) from rfl,
    transT_some, Set.mem_compl_iff, Set.mem_singleton_iff]
  exact fun h => Work.ThomBordism.tubeInvPunct_sub E C x hy
    (sub_eq_zero.mp (OnePoint.coe_injective h))

/-- **The value, transported to the ambient sphere.**  The pairing is the one of the class
`(T_{-p})^*σ` — obtained from a class `σ` of `(S^{8+k}, S^{8+k}∖{0})` restricting to `stdModelGen` —
with the push-forward of the tube class `δ` into the sphere. -/
theorem value_eq_translated_local {V : Work.ThomBordism.Man8} {k : ℕ}
    (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k)) {ε : ℝ}
    (C : Work.Tubular.TubeChart E ε)
    (g : C(OnePoint (Work.Tubular.Euc (8 + k)), OnePoint (Work.Tubular.NormalTotal E)))
    (hg : ∀ y, y ∉ C.openTube → g (OnePoint.some y) = OnePoint.infty)
    {R : ℝ} (hR : 0 ≤ R) (hbox : ∀ y ∈ C.U, ∀ j : Fin (8 + k), |y j| < R) (x : V.pt)
    (δ : (Work.Cohomology.relChains (TopCat.of ↥C.U)
        (Work.ThomBordism.tubeInvPunct E C)).homology (k + 8))
    (σ : Work.Thom.RelCoh ℤ (8 + k) (OnePoint (Work.Tubular.Euc (8 + k)))
      ({OnePoint.some (0 : Work.Tubular.Euc (8 + k))}ᶜ :
        Set (OnePoint (Work.Tubular.Euc (8 + k)))))
    (hσ : (Work.Thom.relCohMap (eucToOnePoint (k := k)) ({0}ᶜ : Set (Work.Tubular.Euc (8 + k)))
        ({OnePoint.some (0 : Work.Tubular.Euc (8 + k))}ᶜ) (eucToOnePoint_mem (k := k))
        ℤ (8 + k)).hom σ = stdModelGen (8 + k)) :
    Work.Tubular.relKronH (TopCat.of ↥C.U) (Work.ThomBordism.tubeInvPunct E C) (k + 8)
        ((Nat.add_comm 8 k) ▸ ambientStandardClass E C x) δ
      = Work.Tubular.relKronH (TopCat.of (OnePoint (Work.Tubular.Euc (8 + k))))
          (({OnePoint.some (E.e x)}ᶜ : Set (OnePoint (Work.Tubular.Euc (8 + k))))) (k + 8)
          ((Nat.add_comm 8 k) ▸ ((Work.Thom.relCohMap (transT (-(E.e x)))
            (({OnePoint.some (E.e x)}ᶜ : Set (OnePoint (Work.Tubular.Euc (8 + k)))))
            ({OnePoint.some (0 : Work.Tubular.Euc (8 + k))}ᶜ)
            (transT_pair (E.e x)) ℤ (8 + k)).hom σ))
          ((ModuleCat.Hom.hom (HomologicalComplex.homologyMap
            (Work.Cohomology.relChainsMapOf (TopCat.of ↥C.U)
              (TopCat.of (OnePoint (Work.Tubular.Euc (8 + k))))
              (Work.ThomBordism.tubeInvPunct E C)
              (({OnePoint.some (E.e x)}ᶜ : Set (OnePoint (Work.Tubular.Euc (8 + k)))))
              (TopCat.ofHom (tubeToSphereMap C)) (TopCat.ofHom (tubeToSphereSub C x))
              (tubeToSphere_compat C x)) (k + 8))) δ) := by
  -- the tube pullback of the translated class is the ambient standard class, at degree `8 + k`
  have hcomp := Work.Thom.relCohMap_compA
    (A := Work.ThomBordism.tubeInvPunct E C)
    (B := ({OnePoint.some (E.e x)}ᶜ : Set (OnePoint (Work.Tubular.Euc (8 + k)))))
    (C := ({OnePoint.some (0 : Work.Tubular.Euc (8 + k))}ᶜ :
      Set (OnePoint (Work.Tubular.Euc (8 + k)))))
    (f := tubeToSphereMap C) (g := transT (-(E.e x)))
    (hf := transT_pair_mem C x) (hg := transT_pair (E.e x))
    (hgf := transT_pair_mem_comp C x) ℤ (8 + k)
  have h1 : ((Work.Thom.relCohMap (tubeToSphereMap C)
        (Work.ThomBordism.tubeInvPunct E C)
        (({OnePoint.some (E.e x)}ᶜ : Set (OnePoint (Work.Tubular.Euc (8 + k)))))
        (transT_pair_mem C x) ℤ (8 + k)).hom
      ((Work.Thom.relCohMap (transT (-(E.e x)))
        (({OnePoint.some (E.e x)}ᶜ : Set (OnePoint (Work.Tubular.Euc (8 + k)))))
        ({OnePoint.some (0 : Work.Tubular.Euc (8 + k))}ᶜ)
        (transT_pair (E.e x)) ℤ (8 + k)).hom σ))
      = ambientStandardClass E C x := by
    rw [← ModuleCat.comp_apply, hcomp]
    have hfun : (transT (-(E.e x))).comp (tubeToSphereMap C)
        = (eucToOnePoint (k := k)).comp (Work.ThomBordism.tubeTransMap E C x) := by
      ext y
      rfl
    rw [show Work.Thom.relCohMap ((transT (-(E.e x))).comp (tubeToSphereMap C))
          (Work.ThomBordism.tubeInvPunct E C)
          ({OnePoint.some (0 : Work.Tubular.Euc (8 + k))}ᶜ)
          (transT_pair_mem_comp C x) ℤ (8 + k)
        = Work.Thom.relCohMap ((eucToOnePoint (k := k)).comp
            (Work.ThomBordism.tubeTransMap E C x))
          (Work.ThomBordism.tubeInvPunct E C)
          ({OnePoint.some (0 : Work.Tubular.Euc (8 + k))}ᶜ)
          (transT_pair_mem_comp C x) ℤ (8 + k) from
      Work.Thom.relCohMap_congrA _ _ hfun _ _ ℤ (8 + k)]
    have hcomp2 := Work.Thom.relCohMap_compA
      (A := Work.ThomBordism.tubeInvPunct E C)
      (B := ({0}ᶜ : Set (Work.Tubular.Euc (8 + k))))
      (C := ({OnePoint.some (0 : Work.Tubular.Euc (8 + k))}ᶜ :
        Set (OnePoint (Work.Tubular.Euc (8 + k)))))
      (f := Work.ThomBordism.tubeTransMap E C x) (g := eucToOnePoint (k := k))
      (hf := Work.ThomBordism.tubeTrans_mem E C x) (hg := eucToOnePoint_mem (k := k))
      (hgf := eucToOnePoint_mem_comp (k := k) C x) ℤ (8 + k)
    rw [show Work.Thom.relCohMap ((eucToOnePoint (k := k)).comp
          (Work.ThomBordism.tubeTransMap E C x))
          (Work.ThomBordism.tubeInvPunct E C)
          ({OnePoint.some (0 : Work.Tubular.Euc (8 + k))}ᶜ)
          (transT_pair_mem_comp C x) ℤ (8 + k)
        = Work.Thom.relCohMap (eucToOnePoint (k := k))
            ({0}ᶜ : Set (Work.Tubular.Euc (8 + k)))
            ({OnePoint.some (0 : Work.Tubular.Euc (8 + k))}ᶜ)
            (eucToOnePoint_mem (k := k)) ℤ (8 + k)
          ≫ Work.Thom.relCohMap (Work.ThomBordism.tubeTransMap E C x)
            (Work.ThomBordism.tubeInvPunct E C)
            ({0}ᶜ : Set (Work.Tubular.Euc (8 + k)))
            (Work.ThomBordism.tubeTrans_mem E C x) ℤ (8 + k) from hcomp2.symm]
    rw [ModuleCat.comp_apply, hσ]
    rfl
  -- assemble at degree `8 + k`, then transport the two casts out
  have key : Work.Tubular.relKronH (TopCat.of ↥C.U)
        (Work.ThomBordism.tubeInvPunct E C) (8 + k) (ambientStandardClass E C x)
        (Work.ThomBordism.chainsHomologyCast (Nat.add_comm 8 k).symm δ)
      = Work.Tubular.relKronH (TopCat.of (OnePoint (Work.Tubular.Euc (8 + k))))
          (({OnePoint.some (E.e x)}ᶜ : Set (OnePoint (Work.Tubular.Euc (8 + k))))) (8 + k)
          ((Work.Thom.relCohMap (transT (-(E.e x)))
            (({OnePoint.some (E.e x)}ᶜ : Set (OnePoint (Work.Tubular.Euc (8 + k)))))
            ({OnePoint.some (0 : Work.Tubular.Euc (8 + k))}ᶜ)
            (transT_pair (E.e x)) ℤ (8 + k)).hom σ)
          ((ModuleCat.Hom.hom (HomologicalComplex.homologyMap
            (Work.Cohomology.relChainsMapOf (TopCat.of ↥C.U)
              (TopCat.of (OnePoint (Work.Tubular.Euc (8 + k))))
              (Work.ThomBordism.tubeInvPunct E C)
              (({OnePoint.some (E.e x)}ᶜ : Set (OnePoint (Work.Tubular.Euc (8 + k)))))
              (TopCat.ofHom (tubeToSphereMap C)) (TopCat.ofHom (tubeToSphereSub C x))
              (tubeToSphere_compat C x)) (8 + k))) (Work.ThomBordism.chainsHomologyCast (Nat.add_comm 8 k).symm δ)) := by
    rw [← h1]
    exact Work.Tubular.relKronH_natural (TopCat.ofHom (tubeToSphereMap C))
      (TopCat.ofHom (tubeToSphereSub C x)) (transT_pair_mem C x)
      (tubeToSphere_compat C x) (8 + k) _
      (Work.ThomBordism.chainsHomologyCast (Nat.add_comm 8 k).symm δ)
  rw [Work.ThomBordism.relKronH_cast_right (X := TopCat.of ↥C.U)
      (A := Work.ThomBordism.tubeInvPunct E C) (Nat.add_comm 8 k) (ambientStandardClass E C x) δ,
    Work.ThomBordism.relKronH_cast_right (X := TopCat.of (OnePoint (Work.Tubular.Euc (8 + k))))
      (A := ({OnePoint.some (E.e x)}ᶜ : Set (OnePoint (Work.Tubular.Euc (8 + k)))))
      (Nat.add_comm 8 k)
      ((Work.Thom.relCohMap (transT (-(E.e x)))
        (({OnePoint.some (E.e x)}ᶜ : Set (OnePoint (Work.Tubular.Euc (8 + k)))))
        ({OnePoint.some (0 : Work.Tubular.Euc (8 + k))}ᶜ)
        (transT_pair (E.e x)) ℤ (8 + k)).hom σ)
      ((ModuleCat.Hom.hom (HomologicalComplex.homologyMap
        (Work.Cohomology.relChainsMapOf (TopCat.of ↥C.U)
          (TopCat.of (OnePoint (Work.Tubular.Euc (8 + k))))
          (Work.ThomBordism.tubeInvPunct E C)
          (({OnePoint.some (E.e x)}ᶜ : Set (OnePoint (Work.Tubular.Euc (8 + k)))))
          (TopCat.ofHom (tubeToSphereMap C)) (TopCat.ofHom (tubeToSphereSub C x))
          (tubeToSphere_compat C x)) (k + 8))) δ),
    ← Work.Tubular.homologyMap_cast_nat (Work.Cohomology.relChainsMapOf (TopCat.of ↥C.U)
          (TopCat.of (OnePoint (Work.Tubular.Euc (8 + k))))
          (Work.ThomBordism.tubeInvPunct E C)
          (({OnePoint.some (E.e x)}ᶜ : Set (OnePoint (Work.Tubular.Euc (8 + k)))))
          (TopCat.ofHom (tubeToSphereMap C)) (TopCat.ofHom (tubeToSphereSub C x))
          (tubeToSphere_compat C x)) (Nat.add_comm 8 k).symm δ]
  exact key

/-- **The exact form of the remaining input.**  A fixed class `u₀ ∈ H_{8+k}(S^{8+k})` whose
localisation at `some (E.e x)` is the push-forward of *every* tube collapse class into the sphere.

This is the "the local degree of the collapse at the zero section is `+1`" statement, in its
sign-blind, datum-uniform form: the push-forward of the collapse class depends on the datum only
through the point `E.e x` of the sphere. -/
def UniformLocalClass (k : ℕ) : Prop :=
  ∃ u₀ : (Work.Cohomology.singularChains ℤ (TopCat.of (OnePoint (Work.Tubular.Euc (8 + k))))).homology
      (8 + k),
    ∀ {V : Work.ThomBordism.Man8} [ConnectedSpace V.pt]
      (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k)) {ε : ℝ}
      (C : Work.Tubular.TubeChart E ε)
      (g : C(OnePoint (Work.Tubular.Euc (8 + k)), OnePoint (Work.Tubular.NormalTotal E)))
      (hg : ∀ y, y ∉ C.openTube → g (OnePoint.some y) = OnePoint.infty)
      (hg2 : ∀ y, y ∈ C.openTube →
        g (OnePoint.some y) = OnePoint.some (Work.Tubular.normalBlowUp E ε (C.inv y)))
      {R : ℝ} (hR : 0 ≤ R)
      (hbox : ∀ y ∈ C.U, ∀ j : Fin (8 + k), |y j| < R) (x : V.pt)
      (δ : (Work.Cohomology.relChains (TopCat.of ↥C.U)
        (Work.ThomBordism.tubeInvPunct E C)).homology (k + 8)),
      Work.ThomBordism.tubeInvHomology E C δ
        = Work.Tubular.collapseRelK8 C g hg hR hbox →
      (ModuleCat.Hom.hom (HomologicalComplex.homologyMap
        (Work.Cohomology.relChainsMapOf (TopCat.of ↥C.U)
          (TopCat.of (OnePoint (Work.Tubular.Euc (8 + k))))
          (Work.ThomBordism.tubeInvPunct E C)
          (({OnePoint.some (E.e x)}ᶜ : Set (OnePoint (Work.Tubular.Euc (8 + k)))))
          (TopCat.ofHom (tubeToSphereMap C)) (TopCat.ofHom (tubeToSphereSub C x))
          (tubeToSphere_compat C x)) (k + 8))) δ
      = (Nat.add_comm 8 k) ▸ Work.Orient.locClass
          (TopCat.of (OnePoint (Work.Tubular.Euc (8 + k)))) (8 + k) u₀
          (OnePoint.some (E.e x))

/-- **The constancy of the value, given `UniformLocalClass`.**  Two data have the same value: each
equals the pairing of the translated standard class `(T_{-p})^*σ` with the local class of the *fixed*
`u₀` at `some p`, and `constancy_translated_local_pairing` (proved in `cla_uniformity`) shows that
this pairing is independent of `p`. -/
theorem value_eq_of_uniformLocalClass (k : ℕ) (hk : 1 ≤ k) (hU : UniformLocalClass k)
    (σ : Work.Thom.RelCoh ℤ (8 + k) (OnePoint (Work.Tubular.Euc (8 + k)))
      ({OnePoint.some (0 : Work.Tubular.Euc (8 + k))}ᶜ :
        Set (OnePoint (Work.Tubular.Euc (8 + k)))))
    (hσ : (Work.Thom.relCohMap (eucToOnePoint (k := k)) ({0}ᶜ : Set (Work.Tubular.Euc (8 + k)))
        ({OnePoint.some (0 : Work.Tubular.Euc (8 + k))}ᶜ) (eucToOnePoint_mem (k := k))
        ℤ (8 + k)).hom σ = stdModelGen (8 + k))
    {Va : Work.ThomBordism.Man8} [ConnectedSpace Va.pt]
    (Ea : Work.ThomBordism.PontryaginThom.EmbeddingData Va (8 + k)) {εa : ℝ}
    (Ca : Work.Tubular.TubeChart Ea εa)
    (ga : C(OnePoint (Work.Tubular.Euc (8 + k)), OnePoint (Work.Tubular.NormalTotal Ea)))
    (hga : ∀ y, y ∉ Ca.openTube → ga (OnePoint.some y) = OnePoint.infty)
    (hg2a : ∀ y, y ∈ Ca.openTube →
      ga (OnePoint.some y) = OnePoint.some (Work.Tubular.normalBlowUp Ea εa (Ca.inv y)))
    {Ra : ℝ} (hRa : 0 ≤ Ra)
    (hboxa : ∀ y ∈ Ca.U, ∀ j : Fin (8 + k), |y j| < Ra) (xa : Va.pt)
    (δa : (Work.Cohomology.relChains (TopCat.of ↥Ca.U)
      (Work.ThomBordism.tubeInvPunct Ea Ca)).homology (k + 8))
    (hδa : Work.ThomBordism.tubeInvHomology Ea Ca δa
      = Work.Tubular.collapseRelK8 Ca ga hga hRa hboxa)
    {Vb : Work.ThomBordism.Man8} [ConnectedSpace Vb.pt]
    (Eb : Work.ThomBordism.PontryaginThom.EmbeddingData Vb (8 + k)) {εb : ℝ}
    (Cb : Work.Tubular.TubeChart Eb εb)
    (gb : C(OnePoint (Work.Tubular.Euc (8 + k)), OnePoint (Work.Tubular.NormalTotal Eb)))
    (hgb : ∀ y, y ∉ Cb.openTube → gb (OnePoint.some y) = OnePoint.infty)
    (hg2b : ∀ y, y ∈ Cb.openTube →
      gb (OnePoint.some y) = OnePoint.some (Work.Tubular.normalBlowUp Eb εb (Cb.inv y)))
    {Rb : ℝ} (hRb : 0 ≤ Rb)
    (hboxb : ∀ y ∈ Cb.U, ∀ j : Fin (8 + k), |y j| < Rb) (xb : Vb.pt)
    (δb : (Work.Cohomology.relChains (TopCat.of ↥Cb.U)
      (Work.ThomBordism.tubeInvPunct Eb Cb)).homology (k + 8))
    (hδb : Work.ThomBordism.tubeInvHomology Eb Cb δb
      = Work.Tubular.collapseRelK8 Cb gb hgb hRb hboxb) :
      Work.Tubular.relKronH (TopCat.of ↥Ca.U) (Work.ThomBordism.tubeInvPunct Ea Ca) (k + 8)
        ((Nat.add_comm 8 k) ▸ Work.ThomBordism.ambientStandardClass Ea Ca xa) δa
      = Work.Tubular.relKronH (TopCat.of ↥Cb.U) (Work.ThomBordism.tubeInvPunct Eb Cb) (k + 8)
        ((Nat.add_comm 8 k) ▸ Work.ThomBordism.ambientStandardClass Eb Cb xb) δb := by
  obtain ⟨u₀, hu₀⟩ := hU
  rw [value_eq_translated_local Ea Ca ga hga hRa hboxa xa δa σ hσ,
    hu₀ Ea Ca ga hga hg2a hRa hboxa xa δa hδa,
    Work.Tubular.relKronH_cast (Nat.add_comm 8 k)
      ((Work.Thom.relCohMap (transT (-(Ea.e xa)))
        (({OnePoint.some (Ea.e xa)}ᶜ : Set (OnePoint (Work.Tubular.Euc (8 + k)))))
        ({OnePoint.some (0 : Work.Tubular.Euc (8 + k))}ᶜ)
        (transT_pair (Ea.e xa)) ℤ (8 + k)).hom σ)
      (Work.Orient.locClass (TopCat.of (OnePoint (Work.Tubular.Euc (8 + k)))) (8 + k) u₀
        (OnePoint.some (Ea.e xa))),
    value_eq_translated_local Eb Cb gb hgb hRb hboxb xb δb σ hσ,
    hu₀ Eb Cb gb hgb hg2b hRb hboxb xb δb hδb,
    Work.Tubular.relKronH_cast (Nat.add_comm 8 k)
      ((Work.Thom.relCohMap (transT (-(Eb.e xb)))
        (({OnePoint.some (Eb.e xb)}ᶜ : Set (OnePoint (Work.Tubular.Euc (8 + k)))))
        ({OnePoint.some (0 : Work.Tubular.Euc (8 + k))}ᶜ)
        (transT_pair (Eb.e xb)) ℤ (8 + k)).hom σ)
      (Work.Orient.locClass (TopCat.of (OnePoint (Work.Tubular.Euc (8 + k)))) (8 + k) u₀
        (OnePoint.some (Eb.e xb)))]
  exact Work.ThomBordism.constancy_translated_local_pairing (8 + k) σ u₀ (Ea.e xa) (Eb.e xb)

/-- **The target follows from the uniformity of the local class** (`UniformLocalClass`) together with
a class `σ ∈ H^{8+k}(S^{8+k}, S^{8+k}∖{0})` restricting to the standard model generator. -/
theorem collapseLocalisation_ambientV2_of_uniformLocalClass (k : ℕ) (hk : 1 ≤ k)
    (hU : UniformLocalClass k)
    (σ : Work.Thom.RelCoh ℤ (8 + k) (OnePoint (Work.Tubular.Euc (8 + k)))
      ({OnePoint.some (0 : Work.Tubular.Euc (8 + k))}ᶜ :
        Set (OnePoint (Work.Tubular.Euc (8 + k)))))
    (hσ : (Work.Thom.relCohMap (eucToOnePoint (k := k)) ({0}ᶜ : Set (Work.Tubular.Euc (8 + k)))
        ({OnePoint.some (0 : Work.Tubular.Euc (8 + k))}ᶜ) (eucToOnePoint_mem (k := k))
        ℤ (8 + k)).hom σ = stdModelGen (8 + k)) :
    ∃ κ : ℤ, (κ = 1 ∨ κ = -1) ∧
    ∀ {V : Work.ThomBordism.Man8} [ConnectedSpace V.pt]
      (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k)) {ε : ℝ}
      (C : Work.Tubular.TubeChart E ε)
      (g : C(OnePoint (Work.Tubular.Euc (8 + k)), OnePoint (Work.Tubular.NormalTotal E)))
      (hg : ∀ y, y ∉ C.openTube → g (OnePoint.some y) = OnePoint.infty)
      (hg2 : ∀ y, y ∈ C.openTube →
        g (OnePoint.some y) = OnePoint.some (Work.Tubular.normalBlowUp E ε (C.inv y)))
      {R : ℝ} (hR : 0 ≤ R)
      (hbox : ∀ y ∈ C.U, ∀ j : Fin (8 + k), |y j| < R) (x : V.pt)
      (δ : (Work.Cohomology.relChains (TopCat.of ↥C.U)
        (Work.ThomBordism.tubeInvPunct E C)).homology (k + 8)),
      Work.ThomBordism.tubeInvHomology E C δ
        = Work.Tubular.collapseRelK8 C g hg hR hbox →
      Work.Tubular.relKronH (TopCat.of ↥C.U) (Work.ThomBordism.tubeInvPunct E C) (k + 8)
        ((Nat.add_comm 8 k) ▸ Work.ThomBordism.ambientStandardClass E C x) δ = κ := by
  classical
  by_cases hex : ∃ (V : Work.ThomBordism.Man8) (hV : ConnectedSpace V.pt)
      (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k)) (ε : ℝ)
      (C : Work.Tubular.TubeChart E ε)
      (g : C(OnePoint (Work.Tubular.Euc (8 + k)), OnePoint (Work.Tubular.NormalTotal E)))
      (hg : ∀ y, y ∉ C.openTube → g (OnePoint.some y) = OnePoint.infty)
      (hg2 : ∀ y, y ∈ C.openTube →
        g (OnePoint.some y) = OnePoint.some (Work.Tubular.normalBlowUp E ε (C.inv y)))
      (R : ℝ) (hR : 0 ≤ R) (hbox : ∀ y ∈ C.U, ∀ j : Fin (8 + k), |y j| < R) (x : V.pt)
      (δ : (Work.Cohomology.relChains (TopCat.of ↥C.U)
        (Work.ThomBordism.tubeInvPunct E C)).homology (k + 8))
      (hδ : Work.ThomBordism.tubeInvHomology E C δ
        = Work.Tubular.collapseRelK8 C g hg hR hbox), True
  · obtain ⟨V, hV, E, ε, C, g, hg, hg2, R, hR, hbox, x, δ, hδ, -⟩ := hex
    letI : ConnectedSpace V.pt := hV
    refine ⟨_, Work.ThomBordism.valuePmOneV2 k hk E C g hg hg2 hR hbox x δ hδ, ?_⟩
    rintro V' hV' E' ε' C' g' hg' hg2' R' hR' hbox' x' δ' hδ'
    letI : ConnectedSpace V'.pt := hV'
    exact (value_eq_of_uniformLocalClass k hk hU σ hσ E C g hg hg2 hR hbox x δ hδ
      E' C' g' hg' hg2' hR' hbox' x' δ' hδ').symm
  · refine ⟨1, Or.inl rfl, ?_⟩
    rintro V hV E ε C g hg hg2 R hR hbox x δ hδ
    exact absurd ⟨V, hV, E, ε, C, g, hg, hg2, R, hR, hbox, x, δ, hδ, trivial⟩ hex





variable {V : Work.ThomBordism.Man8} {k : ℕ}

/-- The fixed Hurewicz class of the standard stereographic cube collapse. -/
noncomputable def stdRelK (k : ℕ) :
    ((Work.Cohomology.singularChains ℤ (TopCat.of (OnePoint (Work.Tubular.Euc (8 + k))))).homology
      (8 + k)) :=
  Work.Stems.hurewiczChain (8 + k) (by omega) OnePoint.infty
    (⟨⟨fun q => Work.Stems.cubeToOnePoint (8 + k) q,
        Work.Stems.cubeToOnePoint_continuous (8 + k)⟩,
      fun t ht => Work.Stems.cubeToOnePoint_eq_infty_of_mem_boundary ht⟩ :
        GenLoop (Fin (8 + k)) (OnePoint (Work.Tubular.Euc (8 + k))) OnePoint.infty)

/-- `g` fixes `∞`. -/
theorem collapse_infty (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k))
    {ε : ℝ} (C : Work.Tubular.TubeChart E ε)
    (g : C(OnePoint (Work.Tubular.Euc (8 + k)), OnePoint (Work.Tubular.NormalTotal E)))
    (hg : ∀ y, y ∉ C.openTube → g (OnePoint.some y) = OnePoint.infty)
    {R : ℝ} (hR : 0 ≤ R) (hbox : ∀ y ∈ C.U, ∀ j : Fin (8 + k), |y j| < R) :
    g OnePoint.infty = OnePoint.infty := by
  obtain ⟨j₀⟩ : Nonempty (Fin (8 + k)) := ⟨⟨0, by omega⟩⟩
  set a : ℝ := R + 1 with ha
  have ha0 : 0 < a := by rw [ha]; linarith
  set v : Work.Tubular.Euc (8 + k) := EuclideanSpace.single j₀ a with hv
  have hvj : v j₀ = a := by
    rw [hv]; simp
  have hnorm : ∀ n : ℕ, ‖(n : ℝ) • v‖ = (n : ℝ) * a := by
    intro n
    rw [hv, norm_smul]
    simp only [PiLp.norm_single, Real.norm_eq_abs, abs_of_pos ha0,
      abs_of_nonneg (show (0 : ℝ) ≤ (n : ℝ) from Nat.cast_nonneg n)]
  have hSn : ∀ n : ℕ, R + 2 < (n : ℝ) * a → ((n : ℝ) • v) ∉ C.openTube := by
    intro n hn hnmem
    rcases hnmem with ⟨p, hp, hpy⟩
    have h2 : ((n : ℝ) • v) ∈ C.U := hpy ▸ C.mem_U p (le_of_lt hp)
    have h3 := hbox _ h2 j₀
    have h4 : (((n : ℝ) • v) : Work.Tubular.Euc (8 + k)) j₀ = (n : ℝ) * a := by
      simp only [PiLp.smul_apply, hvj, smul_eq_mul]
    rw [h4] at h3
    obtain ⟨h3a, h3b⟩ := abs_lt.mp h3
    linarith
  have hcl : OnePoint.infty ∈ closure (OnePoint.some ''
      {y : Work.Tubular.Euc (8 + k) | y ∉ C.openTube}) := by
    rw [mem_closure_iff]
    intro t ht hxt
    have ht' : t ∈ nhds (OnePoint.infty : OnePoint (Work.Tubular.Euc (8 + k))) :=
      ht.mem_nhds hxt
    obtain ⟨K, ⟨hKc, hKcomp⟩, hKsub⟩ := OnePoint.hasBasis_nhds_infty.mem_iff.mp ht'
    obtain ⟨R', hR'⟩ := (Metric.isBounded_iff_subset_closedBall
      (0 : Work.Tubular.Euc (8 + k))).mp hKcomp.isBounded
    obtain ⟨n, hn⟩ : ∃ n : ℕ, max R' (R + 2) < (n : ℝ) * a := by
      have hceil : max R' (R + 2) / a ≤ (Nat.ceil (max R' (R + 2) / a) : ℝ) :=
        Nat.le_ceil _
      have hprod : (max R' (R + 2) / a) * a
          ≤ (Nat.ceil (max R' (R + 2) / a) : ℝ) * a :=
        mul_le_mul_of_nonneg_right hceil ha0.le
      have hlt : (Nat.ceil (max R' (R + 2) / a) : ℝ) * a
          < ((Nat.ceil (max R' (R + 2) / a) : ℝ) + 1) * a :=
        mul_lt_mul_of_pos_right (by linarith) ha0
      have hcancel : (max R' (R + 2) / a) * a = max R' (R + 2) :=
        div_mul_cancel₀ _ (ne_of_gt ha0)
      refine ⟨Nat.ceil (max R' (R + 2) / a) + 1, ?_⟩
      calc max R' (R + 2) = (max R' (R + 2) / a) * a := hcancel.symm
        _ ≤ (Nat.ceil (max R' (R + 2) / a) : ℝ) * a := hprod
        _ < ((Nat.ceil (max R' (R + 2) / a) : ℝ) + 1) * a := hlt
        _ ≤ (((Nat.ceil (max R' (R + 2) / a) + 1 : ℕ)) : ℝ) * a := by
            have hle : (Nat.ceil (max R' (R + 2) / a) : ℝ) + 1
                ≤ ((Nat.ceil (max R' (R + 2) / a) + 1 : ℕ) : ℝ) := by push_cast; linarith
            exact mul_le_mul_of_nonneg_right hle ha0.le
    have hKmem : ((n : ℝ) • v) ∉ K := by
      intro hmem
      have h1 : ((n : ℝ) • v) ∈ Metric.closedBall (0 : Work.Tubular.Euc (8 + k)) R' := hR' hmem
      rw [Metric.mem_closedBall, dist_zero_right, hnorm n] at h1
      linarith [le_max_left R' (R + 2)]
    exact ⟨OnePoint.some ((n : ℝ) • v), hKsub (Or.inl ⟨_, hKmem, rfl⟩),
      ⟨_, hSn n (lt_of_le_of_lt (le_max_right R' (R + 2)) hn), rfl⟩⟩
  have himg : g '' (OnePoint.some '' {y : Work.Tubular.Euc (8 + k) | y ∉ C.openTube})
      ⊆ {OnePoint.infty} := by
    rintro _ ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    exact hg y hy
  have h1 : g OnePoint.infty ∈ closure
      (g '' (OnePoint.some '' {y : Work.Tubular.Euc (8 + k) | y ∉ C.openTube})) :=
    image_closure_subset_closure_image g.continuous ⟨OnePoint.infty, hcl, rfl⟩
  have h2 : closure (g '' (OnePoint.some '' {y : Work.Tubular.Euc (8 + k) | y ∉ C.openTube}))
      ⊆ {OnePoint.infty} := isClosed_singleton.closure_subset_iff.mpr himg
  exact h2 h1





variable {V : Work.ThomBordism.Man8} {k : ℕ}

theorem zeroSectionPunctPt_ne_infty (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k))
    (x : V.pt) :
    (Work.Tubular.zeroSectionPunctPt E x : OnePoint (Work.Tubular.NormalTotal E)) ≠ OnePoint.infty :=
  OnePoint.coe_ne_infty _



/-- The blow-up of a point of the open disc bundle is a zero-section point only for zero-section
points. -/
theorem normalBlowUp_eq_zeroSection (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k))
    {ε : ℝ} (hε : 0 < ε) {q : Work.Tubular.NormalTotal E} (hq : Work.Tubular.normalNorm E q < ε)
    (x : V.pt) (h : Work.Tubular.normalBlowUp E ε q = Work.Tubular.zeroSectionNormal E x) :
    q = Work.Tubular.zeroSectionNormal E x := by
  have hco : (Work.Tubular.normalBlowUp E ε q)
      = radialRescale E (fun r => ε * (ε - r)⁻¹) q :=
    normalBlowUp_eq_radialRescale E ε q
  have h' : (radialRescale E (fun r => ε * (ε - r)⁻¹) q : V.pt × Work.Tubular.Euc (8 + k))
      = (Work.Tubular.zeroSectionNormal E x : V.pt × Work.Tubular.Euc (8 + k)) := by
    rw [← hco, h]
  rw [radialRescale_coe] at h'
  have h1 : q.1.1 = x := by
    have := congrArg (fun p : V.pt × Work.Tubular.Euc (8 + k) => p.1) h'
    simpa [Work.Tubular.zeroSectionNormal_apply] using this
  have h2 : (ε * (ε - Work.Tubular.normalNorm E q)⁻¹) • q.1.2 = 0 := by
    have := congrArg (fun p : V.pt × Work.Tubular.Euc (8 + k) => p.2) h'
    simpa [Work.Tubular.zeroSectionNormal_apply] using this
  have hcpos : 0 < (ε * (ε - Work.Tubular.normalNorm E q)⁻¹) :=
    mul_pos hε (inv_pos.mpr (by linarith))
  have h3 : q.1.2 = 0 := by
    have := smul_eq_zero.mp h2
    rcases this with h | h
    · exact absurd h (ne_of_gt hcpos)
    · exact h
  apply Subtype.ext
  apply Prod.ext
  · exact h1
  · exact h3


/-- The pair condition of `g` for the *fine* pair `(S, S∖{p₀}) → (ν⁺, ν⁺∖{x₀})`. -/
theorem collapse_g_mem_fine (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k))
    {ε : ℝ} (C : Work.Tubular.TubeChart E ε) (x : V.pt)
    (g : C(OnePoint (Work.Tubular.Euc (8 + k)), OnePoint (Work.Tubular.NormalTotal E)))
    (hg : ∀ y, y ∉ C.openTube → g (OnePoint.some y) = OnePoint.infty)
    (hg2 : ∀ y, y ∈ C.openTube →
      g (OnePoint.some y) = OnePoint.some (Work.Tubular.normalBlowUp E ε (C.inv y)))
    {R : ℝ} (hR : 0 ≤ R) (hbox : ∀ y ∈ C.U, ∀ j : Fin (8 + k), |y j| < R) :
    ∀ z ∈ ({OnePoint.some (E.e x)}ᶜ : Set (OnePoint (Work.Tubular.Euc (8 + k)))),
      g z ∈ ({Work.Tubular.zeroSectionPunctPt E x}ᶜ :
        Set (OnePoint (Work.Tubular.NormalTotal E))) := by
  intro z hz
  rw [Set.mem_compl_iff, Set.mem_singleton_iff] at hz ⊢
  induction z using OnePoint.rec with
  | infty =>
      rw [collapse_infty E C g hg hR hbox]
      exact (zeroSectionPunctPt_ne_infty E x).symm
  | coe y =>
      by_cases hy : y ∈ C.openTube
      · rw [hg2 y hy]
        intro hcon
        have h1 : Work.Tubular.normalBlowUp E ε (C.inv y) = Work.Tubular.zeroSectionNormal E x :=
          OnePoint.coe_injective hcon
        have h2 : C.inv y = Work.Tubular.zeroSectionNormal E x :=
          normalBlowUp_eq_zeroSection E C.eps_pos (C.normalNorm_inv_lt hy) x h1
        exact hz (by
          rw [← C.tubeMap_inv y (C.openTube_subset_U hy), h2,
            Work.ThomBordism.tubeMap_zeroSectionNormal])
      · rw [hg y hy]
        exact (zeroSectionPunctPt_ne_infty E x).symm



/-- The inclusion `ν ↪ ν⁺` as a map into the *fine* pair. -/
theorem someNu_fine_mem (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k))
    (x : V.pt) :
    ∀ p ∈ Work.Tubular.normalNonzero E,
      (⟨OnePoint.some, OnePoint.continuous_coe⟩ :
        C(Work.Tubular.NormalTotal E, OnePoint (Work.Tubular.NormalTotal E))) p
        ∈ ({Work.Tubular.zeroSectionPunctPt E x}ᶜ :
            Set (OnePoint (Work.Tubular.NormalTotal E))) := by
  intro p hp
  simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
  intro hcon
  rw [Work.Tubular.zeroSectionPunctPt, Work.Tubular.zeroSectionOnePoint_apply] at hcon
  have h2 : p = Work.Tubular.zeroSectionNormal E x := OnePoint.coe_injective hcon
  rw [Work.Tubular.mem_normalNonzero, h2, Work.Tubular.zeroSectionNormal_apply,
    Work.Tubular.normalNorm_mk, norm_zero] at hp
  exact hp rfl

/-- **(C1')**: the avatar of the fine extension `βf` on `(ν, ν∖0)` is the coarse avatar `β`, whose
`compPull` is the chart model class. -/
theorem someNu_pullback_eq_compPull (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k))
    (x : V.pt)
    (β : Work.Thom.RelCoh ℤ (8 + k) (OnePoint (Work.Tubular.NormalTotal E))
      (Work.Tubular.onePointNonzero E))
    (βf : Work.Thom.RelCoh ℤ (8 + k) (OnePoint (Work.Tubular.NormalTotal E))
      ({Work.Tubular.zeroSectionPunctPt E x}ᶜ : Set (OnePoint (Work.Tubular.NormalTotal E))))
    (hβf : (Work.Thom.relCohMap (ContinuousMap.id (OnePoint (Work.Tubular.NormalTotal E)))
        (Work.Tubular.onePointNonzero E)
        ({Work.Tubular.zeroSectionPunctPt E x}ᶜ : Set (OnePoint (Work.Tubular.NormalTotal E)))
        (fun y hy => fun hcon => zeroSectionPunctPt_notMem E x (hcon ▸ hy)) ℤ (8 + k)).hom βf
      = β) :
    (Work.Thom.relCohMap (⟨OnePoint.some, OnePoint.continuous_coe⟩ :
        C(Work.Tubular.NormalTotal E, OnePoint (Work.Tubular.NormalTotal E)))
      (Work.Tubular.normalNonzero E)
      ({Work.Tubular.zeroSectionPunctPt E x}ᶜ : Set (OnePoint (Work.Tubular.NormalTotal E)))
      (someNu_fine_mem E x) ℤ (8 + k)).hom βf
      = Work.Tubular.compPull E (8 + k) β := by
  classical
  -- the coarse avatar of `βf`
  have hcoarse : (Work.Thom.relCohMap (ContinuousMap.id (OnePoint (Work.Tubular.NormalTotal E)))
      (Work.Tubular.onePointNonzero E)
      ({Work.Tubular.zeroSectionPunctPt E x}ᶜ : Set (OnePoint (Work.Tubular.NormalTotal E)))
      (fun y hy => fun hcon => zeroSectionPunctPt_notMem E x (hcon ▸ hy)) ℤ (8 + k)).hom βf
      = β := hβf
  -- step 1: the fine avatar is the coarse avatar in disguise
  have h1 := Work.Thom.relCohMap_compA
    (A := Work.Tubular.normalNonzero E) (B := Work.Tubular.onePointNonzero E)
    (C := ({Work.Tubular.zeroSectionPunctPt E x}ᶜ : Set (OnePoint (Work.Tubular.NormalTotal E))))
    (f := (⟨OnePoint.some, OnePoint.continuous_coe⟩ :
      C(Work.Tubular.NormalTotal E, OnePoint (Work.Tubular.NormalTotal E))))
    (g := ContinuousMap.id (OnePoint (Work.Tubular.NormalTotal E)))
    (hf := fun p hp => Work.Tubular.mem_onePointNonzero.mpr (Or.inr ⟨p, Work.Tubular.mem_normalNonzero.mp hp, rfl⟩))
    (hg := fun y hy => fun hcon => zeroSectionPunctPt_notMem E x (hcon ▸ hy))
    (hgf := someNu_fine_mem E x) ℤ (8 + k)
  have hcomp_id : (ContinuousMap.id (OnePoint (Work.Tubular.NormalTotal E))).comp
      (⟨OnePoint.some, OnePoint.continuous_coe⟩ :
        C(Work.Tubular.NormalTotal E, OnePoint (Work.Tubular.NormalTotal E)))
      = ⟨OnePoint.some, OnePoint.continuous_coe⟩ := ContinuousMap.id_comp _
  rw [show (Work.Thom.relCohMap
        (⟨OnePoint.some, OnePoint.continuous_coe⟩ :
          C(Work.Tubular.NormalTotal E, OnePoint (Work.Tubular.NormalTotal E)))
        (Work.Tubular.normalNonzero E)
        ({Work.Tubular.zeroSectionPunctPt E x}ᶜ : Set (OnePoint (Work.Tubular.NormalTotal E)))
        (someNu_fine_mem E x) ℤ (8 + k))
      = Work.Thom.relCohMap ((ContinuousMap.id (OnePoint (Work.Tubular.NormalTotal E))).comp
          (⟨OnePoint.some, OnePoint.continuous_coe⟩ :
            C(Work.Tubular.NormalTotal E, OnePoint (Work.Tubular.NormalTotal E))))
          (Work.Tubular.normalNonzero E)
          ({Work.Tubular.zeroSectionPunctPt E x}ᶜ : Set (OnePoint (Work.Tubular.NormalTotal E)))
          (someNu_fine_mem E x) ℤ (8 + k) from
    Work.Thom.relCohMap_congrA _ _
      (ContinuousMap.id_comp _).symm (someNu_fine_mem E x) (someNu_fine_mem E x) ℤ (8 + k)]
  rw [← h1, ModuleCat.comp_apply]
  -- step 2: apply to `βf` and use the coarse avatar
  rw [show (Work.Thom.relCohMap (ContinuousMap.id (OnePoint (Work.Tubular.NormalTotal E)))
        (Work.Tubular.onePointNonzero E)
        ({Work.Tubular.zeroSectionPunctPt E x}ᶜ : Set (OnePoint (Work.Tubular.NormalTotal E)))
        (fun y hy => fun hcon => zeroSectionPunctPt_notMem E x (hcon ▸ hy)) ℤ (8 + k)).hom βf
      = β from hcoarse]
  rw [show (Work.Thom.relCohMap
        (⟨OnePoint.some, OnePoint.continuous_coe⟩ :
          C(Work.Tubular.NormalTotal E, OnePoint (Work.Tubular.NormalTotal E)))
        (Work.Tubular.normalNonzero E) (Work.Tubular.onePointNonzero E)
        (fun p hp => Work.Tubular.mem_onePointNonzero.mpr (Or.inr ⟨p, Work.Tubular.mem_normalNonzero.mp hp, rfl⟩))
        ℤ (8 + k))
      = (Work.Thom.relCohMap
        (⟨OnePoint.some, OnePoint.continuous_coe⟩ :
          C(Work.Tubular.NormalTotal E, OnePoint (Work.Tubular.NormalTotal E)))
        (Work.Tubular.normalNonzero E) (Work.Tubular.onePointNonzero E)
        (fun x hx => Work.Tubular.mem_onePointNonzero.mpr
          (Or.inr ⟨x, Work.Tubular.mem_normalNonzero.mp hx, rfl⟩)) ℤ (8 + k)) from
    Work.Thom.relCohMap_congrA _ _ rfl _ _ ℤ (8 + k)]
  exact Work.ThomBordism.some_pullback_eq_compPull E (8 + k) β




end

end Work.ThomBordism
