import Submission.Work.Tubular.OnePointModel
import Submission.Work.Tubular.TotalMapProper
import Submission.Work.Tubular.GenLoop
import Submission.Work.Tubular.Global
import Submission.Work.Tubular.Rank
import Submission.Work.Thom.Iso

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-!
# The Gauss/classifying map of the normal bundle, and the Pontryagin–Thom class `α_V`

Given a bundle isomorphism `ν ≅ gauss^*γ` (the content of the Gauss map of the Grassmann chapter,
`Work.ThomBordism.PontryaginThom.NormalGaussData.classifies`), the pullback map of total spaces
`gauss^*γ.TotalSpace → γ.TotalSpace` is proper (`Work.Tubular.continuous_onePointMap_totalMap`), hence
extends to the one-point compactifications.  Composing with the isomorphism finishes:

`Work.Tubular.gaussThomMap` — the induced continuous map of **Thom spaces**
`Th(ν) → Th(γ)` in the metric-free model `Th = OnePoint (TotalSpace)`, fixing `∞`.

Composing this with the metric-free collapse `Work.Tubular.collapseToOnePoint` and passing to
Mathlib's cube model `GenLoop` gives the **Pontryagin–Thom class** `α_V`
(`Work.Tubular.tubeGenLoopOnePoint`, `Work.Tubular.alphaV`): the element of `π_{8+k}(Th γ)` that the
Pontryagin–Thom chapter (`Work.ThomBordism.PontryaginThom.PTRep.collapse`) consumes.
-/

open scoped Manifold ContDiff Topology unitInterval
open Function Topology Set Filter

open Work.ThomBordism.PontryaginThom (EmbeddingData)

namespace Work.Tubular

noncomputable section

open Work.TangentClasses Work.Thom

/-! ## The map of Thom spaces induced by a bundle map -/

variable {B B' : Type} [TopologicalSpace B] [TopologicalSpace B']
  {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] {ι κ : Type}

/-- **The map of Thom spaces induced by a map of bundles.**  For bundles `Z` over `B`,
`Z'` over the **compact** base `B'`, a continuous `g : B' → B` and an isomorphism
`e : g^*Z ≅ Z'`, the composite `Z'_x ≅ (g^*Z)_x = Z_{g x}` extends to the one-point
compactifications, giving `Th(Z') → Th(Z)` with `∞ ↦ ∞`. -/
def gaussThomMap [CompactSpace B] [CompactSpace B'] [T2Space B] [ProperSpace F]
    (Z : RealBundle B F κ) (Z' : RealBundle B' F ι) (g : C(B', B))
    (e : BundleIso (bundleComap Z g) Z') :
    C(OnePoint Z'.TotalSpace, OnePoint Z.TotalSpace) :=
  ⟨(OnePoint.map (totalMap Z g)) ∘ (Homeomorph.onePointCongr e.toHomeomorph).symm,
    (continuous_onePointMap_totalMap Z g).comp
      (Homeomorph.onePointCongr e.toHomeomorph).symm.continuous⟩

@[simp] theorem gaussThomMap_infty [CompactSpace B] [CompactSpace B'] [T2Space B] [ProperSpace F]
    (Z : RealBundle B F κ) (Z' : RealBundle B' F ι) (g : C(B', B))
    (e : BundleIso (bundleComap Z g) Z') :
    gaussThomMap Z Z' g e OnePoint.infty = OnePoint.infty := by
  show OnePoint.map (totalMap Z g)
    ((Homeomorph.onePointCongr e.toHomeomorph).symm OnePoint.infty) = OnePoint.infty
  have h1 : (Homeomorph.onePointCongr e.toHomeomorph).symm OnePoint.infty = OnePoint.infty := by
    rw [Homeomorph.symm_apply_eq, Homeomorph.onePointCongr_apply, OnePoint.map_infty]
  rw [h1, OnePoint.map_infty]

/-! ## The collapse in the metric-free model, in the cube model -/

/-- The inclusion of the cube of radius `R` into the one-point compactification of `ℝ^{8+k}`. -/
def cubeToOnePoint (k : ℕ) (R : ℝ) : C(Fin (8 + k) → unitInterval, OnePoint (Euc (8 + k))) :=
  ⟨fun t => OnePoint.some (cubeToEuc (8 + k) R t),
    OnePoint.continuous_coe.comp (cubeToEuc (8 + k) R).continuous⟩

@[simp] theorem cubeToOnePoint_apply (k : ℕ) (R : ℝ) (t : Fin (8 + k) → unitInterval) :
    cubeToOnePoint k R t = OnePoint.some (cubeToEuc (8 + k) R t) := rfl

/-- The composite of the metric-free collapse with the inclusion of the cube of radius `R` into
`ℝ^{8+k} = Euc (8+k)`: a map of cubes into `Th(ν) = ν⁺`. -/
def tubeCollapseCubeOnePoint {V : Work.ThomBordism.Man8} {k : ℕ} {E : EmbeddingData V (8 + k)}
    (g : C(OnePoint (Euc (8 + k)), OnePoint (NormalTotal E))) (R : ℝ) :
    C(Fin (8 + k) → unitInterval, OnePoint (NormalTotal E)) :=
  g.comp (cubeToOnePoint k R)

@[simp] theorem tubeCollapseCubeOnePoint_apply {V : Work.ThomBordism.Man8} {k : ℕ}
    {E : EmbeddingData V (8 + k)}
    (g : C(OnePoint (Euc (8 + k)), OnePoint (NormalTotal E))) (R : ℝ)
    (t : Fin (8 + k) → unitInterval) :
    tubeCollapseCubeOnePoint g R t = g (OnePoint.some (cubeToEuc (8 + k) R t)) := rfl

/-- **On the boundary of the cube the collapse is the basepoint.** -/
theorem tubeCollapseCubeOnePoint_boundary {V : Work.ThomBordism.Man8} {k : ℕ}
    {E : EmbeddingData V (8 + k)} {ε : ℝ} (C : TubeChart E ε)
    (g : C(OnePoint (Euc (8 + k)), OnePoint (NormalTotal E)))
    (hg : ∀ y, y ∉ C.openTube → g (OnePoint.some y) = OnePoint.infty)
    {R : ℝ} (hR : 0 ≤ R) (hbox : ∀ y ∈ C.U, ∀ i : Fin (8 + k), |y i| < R)
    {t : Fin (8 + k) → unitInterval} (ht : t ∈ Cube.boundary (Fin (8 + k))) :
    tubeCollapseCubeOnePoint g R t = OnePoint.infty := by
  rw [tubeCollapseCubeOnePoint_apply]
  refine hg _ (fun hmem => ?_)
  obtain ⟨i, hi⟩ := cubeToEuc_boundary (8 + k) hR ht
  have h := hbox (cubeToEuc (8 + k) R t) (C.openTube_subset_U hmem) i
  rw [hi] at h
  exact absurd h (lt_irrefl R)

/-- **The Pontryagin–Thom class of a tubular neighbourhood, in the metric-free model and the cube
model**: an element of `π_{8+k}(Th ν)` realised by the collapse. -/
def tubeGenLoopOnePoint {V : Work.ThomBordism.Man8} {k : ℕ} {E : EmbeddingData V (8 + k)}
    {ε : ℝ} (C : TubeChart E ε) (g : C(OnePoint (Euc (8 + k)), OnePoint (NormalTotal E)))
    (hg : ∀ y, y ∉ C.openTube → g (OnePoint.some y) = OnePoint.infty)
    {R : ℝ} (hR : 0 ≤ R) (hbox : ∀ y ∈ C.U, ∀ i : Fin (8 + k), |y i| < R) :
    GenLoop (Fin (8 + k)) (OnePoint (NormalTotal E)) OnePoint.infty :=
  ⟨tubeCollapseCubeOnePoint g R,
    fun t ht => tubeCollapseCubeOnePoint_boundary C g hg hR hbox ht⟩

/-- **`α_V`: the Pontryagin–Thom class of the tubular neighbourhood composed with a based map.**
This is the map `Th(ν) → Y` (the Gauss/classifying map) applied to the collapse; the conclusion
`J ∞ = ∞` is what makes the collapse's boundary value land on the basepoint. -/
def alphaV {V : Work.ThomBordism.Man8} {k : ℕ} {E : EmbeddingData V (8 + k)} {ε : ℝ}
    (C : TubeChart E ε) {R : ℝ} (hR : 0 ≤ R)
    (hbox : ∀ y ∈ C.U, ∀ i : Fin (8 + k), |y i| < R)
    {Y : Type} [TopologicalSpace Y] (y₀ : Y)
    (J : C(OnePoint (NormalTotal E), Y)) (hJ : J OnePoint.infty = y₀)
    (g : C(OnePoint (Euc (8 + k)), OnePoint (NormalTotal E)))
    (hg : ∀ y, y ∉ C.openTube → g (OnePoint.some y) = OnePoint.infty) :
    GenLoop (Fin (8 + k)) Y y₀ :=
  ⟨J.comp (tubeCollapseCubeOnePoint g R),
    genLoop_comp J hJ (tubeGenLoopOnePoint C g hg hR hbox).2⟩

/-- **The Gauss/classifying map of Thom spaces**, as a single continuous map: the composition of
the map `Th(ν) → Th(γ)` induced by the bundle isomorphism `e : gauss^*γ ≅ ν`
(`Work.Tubular.gaussThomMap`) with the homeomorphism of one-point compactifications induced by
`Φ : NormalTotal E ≃ₜ ν.TotalSpace`.  This is the `J` of `Work.Tubular.alphaV` in the situation of
`Work.Tubular.exists_alphaV_gauss`. -/
def gaussMapOnePoint {V : Work.ThomBordism.Man8} {k : ℕ} {E : EmbeddingData V (8 + k)}
    {G : Type} [TopologicalSpace G] [CompactSpace G] [T2Space G]
    {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [ProperSpace F] {ι κ : Type}
    {γ : RealBundle G F κ} {ν : RealBundle V.pt F ι}
    (gauss : C(V.pt, G)) (e : BundleIso (bundleComap γ gauss) ν)
    (Φ : NormalTotal E ≃ₜ ν.TotalSpace) :
    C(OnePoint (NormalTotal E), OnePoint γ.TotalSpace) :=
  (gaussThomMap γ ν gauss e).comp
    ⟨(Homeomorph.onePointCongr Φ : OnePoint (NormalTotal E) → OnePoint ν.TotalSpace),
      (Homeomorph.onePointCongr Φ).continuous⟩

/-- `Work.Tubular.gaussMapOnePoint` fixes `∞`. -/
theorem gaussMapOnePoint_infty {V : Work.ThomBordism.Man8} {k : ℕ} {E : EmbeddingData V (8 + k)}
    {G : Type} [TopologicalSpace G] [CompactSpace G] [T2Space G]
    {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [ProperSpace F] {ι κ : Type}
    {γ : RealBundle G F κ} {ν : RealBundle V.pt F ι}
    (gauss : C(V.pt, G)) (e : BundleIso (bundleComap γ gauss) ν)
    (Φ : NormalTotal E ≃ₜ ν.TotalSpace) :
    gaussMapOnePoint gauss e Φ OnePoint.infty = OnePoint.infty := by
  have hΦ : (Homeomorph.onePointCongr Φ) OnePoint.infty = OnePoint.infty := by
    rw [Homeomorph.onePointCongr_apply, OnePoint.map_infty]
  show gaussThomMap γ ν gauss e ((Homeomorph.onePointCongr Φ) OnePoint.infty) = OnePoint.infty
  rw [hΦ, gaussThomMap_infty]

/-! ## The class `α_V` of an embedded manifold -/

/-- **The Pontryagin–Thom class exists.**  For an embedding `E : V ↪ ℝ^{8+k}` with `0 < k` (so the
normal sphere bundle is nonempty) and a based map `J` out of `Th(ν) = ν⁺` into a based space
`(Y, y₀)`, the composite of the Pontryagin–Thom collapse with `J` is an element of
`π_{8+k}(Y, y₀)` — in particular, composing with the Gauss map `Th(ν) → Th(γ)` gives `α_V`. -/
theorem exists_alphaV {V : Work.ThomBordism.Man8} {k : ℕ} (E : EmbeddingData V (8 + k))
    [Nonempty V.pt] (hk : 0 < k) {Y : Type} [TopologicalSpace Y] (y₀ : Y)
    (J : C(OnePoint (NormalTotal E), Y)) (hJ : J OnePoint.infty = y₀) :
    ∃ (ε : ℝ) (hε : 0 < ε) (C : TubeChart E ε) (q : NormalSphSub E ε) (R : ℝ) (hR : 0 ≤ R)
      (hbox : ∀ y ∈ C.U, ∀ i : Fin (8 + k), |y i| < R)
      (g : C(OnePoint (Euc (8 + k)), OnePoint (NormalTotal E)))
      (hg : ∀ y, y ∉ C.openTube → g (OnePoint.some y) = OnePoint.infty),
      ∃ α : GenLoop (Fin (8 + k)) Y y₀, α = alphaV C hR hbox y₀ J hJ g hg := by
  obtain ⟨ε, hε, ⟨C⟩⟩ := hasTubularNeighbourhood E
  haveI : CompactSpace (NormalDiscSub E ε) := compactSpace_normalDiscSub E ε
  obtain ⟨q⟩ := nonempty_normalSphSub E hε (by omega : 8 < 8 + k)
  have hU : IsCompact C.U := C.isCompact_U
  obtain ⟨g, _, hg2, _⟩ := collapseToOnePoint E C q hU
  obtain ⟨R, hR, hbox⟩ := C.exists_box
  exact ⟨ε, hε, C, q, R, hR.le, hbox, g, hg2,
    alphaV C hR.le hbox y₀ J hJ g hg2, rfl⟩

/-- **The class `α_V` of an embedded manifold, with the Gauss map.**  Given a bundle isomorphism
`ν ≅ gauss^*γ` over the compact base `V.pt` (`NormalGaussData.classifies`) and a homeomorphism
`NormalTotal E ≃ₜ ν.TotalSpace` (this is `Work.Tubular.normalTotalIso` for the normal bundle of
`E`), the collapse composed with the Gauss map `Th(ν) → Th(γ)` is an element of
`π_{8+k}(Th γ)`: the Pontryagin–Thom class of `V` in the universal Thom space. -/
theorem exists_alphaV_gauss {V : Work.ThomBordism.Man8} {k m : ℕ} (E : EmbeddingData V (8 + k))
    [Nonempty V.pt] (hk : 0 < k) {G : Type} [TopologicalSpace G] [CompactSpace G] [T2Space G]
    {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [ProperSpace F] {ι κ : Type}
    {γ : RealBundle G F κ} {ν : RealBundle V.pt F ι}
    (gauss : C(V.pt, G)) (e : BundleIso (bundleComap γ gauss) ν) (Φ : NormalTotal E ≃ₜ ν.TotalSpace) :
    ∃ (ε : ℝ) (hε : 0 < ε) (C : TubeChart E ε) (q : NormalSphSub E ε) (R : ℝ) (hR : 0 ≤ R)
      (hbox : ∀ y ∈ C.U, ∀ i : Fin (8 + k), |y i| < R)
      (g : C(OnePoint (Euc (8 + k)), OnePoint (NormalTotal E)))
      (hg : ∀ y, y ∉ C.openTube → g (OnePoint.some y) = OnePoint.infty),
      ∃ α : GenLoop (Fin (8 + k)) (OnePoint γ.TotalSpace) OnePoint.infty,
        α = alphaV C hR hbox OnePoint.infty (gaussMapOnePoint gauss e Φ)
              (gaussMapOnePoint_infty gauss e Φ) g hg := by
  obtain ⟨ε, hε, C, q, R, hR, hbox, g, hg, a, ha⟩ :=
    exists_alphaV E hk OnePoint.infty (gaussMapOnePoint gauss e Φ)
      (gaussMapOnePoint_infty gauss e Φ)
  exact ⟨ε, hε, C, q, R, hR, hbox, g, hg, a, ha⟩

end

end Work.Tubular
