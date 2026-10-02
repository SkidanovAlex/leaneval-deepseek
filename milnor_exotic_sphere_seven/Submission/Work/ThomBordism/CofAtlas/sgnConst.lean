import Mathlib
import Submission.Work.ThomBordism.CofAtlas.Signs
import Submission.Work.ThomBordism.CofAtlas.Omega_eq_fderiv
import Submission.Work.ThomBordism.CofAtlas.range_chartIota_eq_ker_Omega

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# Constancy and nonvanishing of the sign `D.sgn x` on the source `D.src x`

`Work.ThomBordism.CofAtlas.sgnConst`: for `D : Cof k n M` and an *interior* point `x` of the level
set, the sign `D.sgn x p` of the `Lvl` chart at `x` (relative to the canonical orientation given by
the ambient orientation `hMdet` and the coframing `hcof`) is constant in `p ∈ D.src x` and never
vanishes.  This is item P7 of `CofAtlas/NOTES.md`: it is what makes the *correction* sign
`D.flipSign x` well defined and, in the final assembly of
`Work.ThomBordism.levelSet_positiveAtlas_of_coframing`, what makes the corrected atlas positive
together with the crux `sign_lvlTransition`.

The proof has three ingredients.

* **Nonvanishing.**  `D.phiD x p = (β_x, Ω_x(p))` is injective: if `Ω_x(p) v = 0` then
  `v ∈ ker Ω_x(p) = range (chartIota x)` (`Cof`-`range_chartIota_eq_ker_Omega`) and `β_x` is a left
  inverse of `chartIota x` (`Setup.chartBeta_iota`), so `β_x v = 0` forces `v = 0`.  Hence
  `σ ∘ phiD x p` is an injective endomorphism of the finite-dimensional `ModN k`, so its
  determinant is a unit, in particular nonzero.
* **Continuity.**  On `D.src x` (all of whose points are interior when `x` is) one has
  `Ω_x(p) = fderiv ℝ (fun z ↦ ℓ (jx x) (v ((domExt x).symm z))) (domExt x p)`
  (`Cof`-`Omega_eq_fderiv`); the chart expression of `v` is `C^∞` near `domExt x p`, so its
  `fderiv` is continuous there, and `p ↦ domExt x p` is continuous.  Composing with the continuous
  map `Ω ↦ det (σ ∘ (β_x).prod Ω)` gives the continuity of `p ↦ D.sgn x p`.
* **Constancy.**  `D.src x` is preconnected and `SignType` is discrete, so a continuous function
  into `SignType` on it is constant (`IsPreconnected.constant`), applied to
  `SignType.sign ∘ det ∘ phiD`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open scoped Manifold ContDiff Topology
open Function Set Topology Manifold Filter ModelWithCorners
open Work.PTGeometric
open Work.PTGeometric.Lvl

namespace Work.ThomBordism.CofAtlas

noncomputable section

variable {k n : ℕ} {M : Type} [TopologicalSpace M] [T2Space M] [CompactSpace M]
  [ChartedSpace (EuclideanHalfSpace (NN k)) M]
  [IsManifold (𝓡∂ (NN k)) ((⊤ : ENat) : WithTop ENat) M]

/-! ## The elementary pieces -/

/-- An interior point of `M` is a point of the interior of the model with corners. -/
theorem mem_interior_of_notMem_boundary {z : M} (hz : z ∉ (𝓡∂ (NN k)).boundary M) :
    z ∈ (𝓡∂ (NN k)).interior M := by
  by_contra hc
  exact hz (by simpa only [← ModelWithCorners.compl_interior, Set.mem_compl_iff] using hc)

/-- A continuous function on a preconnected set that does not vanish has constant sign on it. -/
theorem sign_eq_of_preconnected {X : Type*} [TopologicalSpace X] {s : Set X}
    (hs : IsPreconnected s) {g : X → ℝ} (hg : ContinuousOn g s) (hne : ∀ y ∈ s, g y ≠ 0)
    {a b : X} (ha : a ∈ s) (hb : b ∈ s) : SignType.sign (g a) = SignType.sign (g b) := by
  have hcont : ContinuousOn (fun y => SignType.sign (g y)) s := fun y hy =>
    (continuousAt_sign_of_ne_zero (hne y hy)).comp_continuousWithinAt (hg y hy)
  exact hs.constant hcont ha hb

/-- **`D.phiD x p` is injective** for `p` in the source of the chart at an interior centre: its two
components are the normal-form splitting `β_x` and the coframing `Ω_x(p)`, whose kernel is exactly
`range (chartIota x)` and on which `β_x` is a left inverse of `chartIota x`. -/
theorem phiD_injective (D : Cof k n M) (x : D.S.Pre) {p : D.S.Pre}
    (hp : p ∈ D.src x) (hpint : (p : M) ∈ (𝓡∂ (NN k)).interior M) :
    Function.Injective (D.phiD x (p : M)) := by
  intro a b hab
  have hb : ((D.S.chartBeta x) a, D.Omega x (p : M) a)
      = ((D.S.chartBeta x) b, D.Omega x (p : M) b) := by
    simpa only [Cof.phiD, ContinuousLinearMap.prod_apply] using hab
  have hβ : (D.S.chartBeta x) a = (D.S.chartBeta x) b := congrArg Prod.fst hb
  have hΩ : (D.Omega x (p : M)) a = (D.Omega x (p : M)) b := congrArg Prod.snd hb
  have h1 : (D.S.chartBeta x) (a - b) = 0 := by rw [map_sub, hβ, sub_self]
  have h2 : (D.Omega x (p : M)) (a - b) = 0 := by rw [map_sub, hΩ, sub_self]
  have hmem : a - b ∈ LinearMap.range (D.S.chartIota x).toLinearMap := by
    rw [range_chartIota_eq_ker_Omega D x hp hpint]
    exact LinearMap.mem_ker.mpr h2
  obtain ⟨y, hy⟩ := hmem
  have hy0 : y = 0 := by
    have h3 : (D.S.chartBeta x) (a - b) = y := by
      rw [← hy]
      exact Work.PTGeometric.Lvl.Setup.chartBeta_iota D.S x y
    rw [h1] at h3
    exact h3.symm
  exact sub_eq_zero.mp (by rw [← hy, hy0, map_zero])

/-- **The determinant `det (σ ∘ phiD x p)` does not vanish** on the source of an interior chart: it
is the determinant of an injective endomorphism of the finite-dimensional space `ModN k`. -/
theorem det_phiD_ne_zero (D : Cof k n M) (x : D.S.Pre) {p : D.S.Pre} (hp : p ∈ D.src x)
    (hpint : (p : M) ∈ (𝓡∂ (NN k)).interior M) :
    LinearMap.det (((sigma k).toLinearMap).comp (D.phiD x (p : M)).toLinearMap) ≠ 0 := by
  let L : ModN k →ₗ[ℝ] ModN k :=
    ((sigma k).toLinearMap).comp (D.phiD x (p : M)).toLinearMap
  have hinj : Function.Injective L := by
    intro a b hab
    have h3 : ((sigma k).toLinearMap) ((D.phiD x (p : M)).toLinearMap a)
        = ((sigma k).toLinearMap) ((D.phiD x (p : M)).toLinearMap b) := by
      simpa only [L, LinearMap.comp_apply] using hab
    have h2 : (D.phiD x (p : M)) a = (D.phiD x (p : M)) b := (sigma k).injective h3
    exact phiD_injective D x hp hpint h2
  have hunit : IsUnit L := (LinearMap.isUnit_iff_ker_eq_bot L).mpr (LinearMap.ker_eq_bot.mpr hinj)
  have hone : IsUnit (LinearMap.det L) := (LinearMap.isUnit_iff_isUnit_det L).mp hunit
  show LinearMap.det L ≠ 0
  exact hone.ne_zero

/-! ## Continuity of the coframing in normal-form coordinates -/

/-- **The coframing `Ω_x` is continuous on `src x`** for an interior centre `x`.  On `src x` it is
the derivative of the (smooth) chart expression `z ↦ ℓ (jx x) (v ((domExt x).symm z))`, and both
`fderiv` (of a `C^∞` function) and `domExt x` are continuous. -/
theorem contOmega (D : Cof k n M) (x : D.S.Pre)
    (hx : (x : M) ∉ (𝓡∂ (NN k)).boundary M) :
    ContinuousOn (fun p : D.S.Pre => D.Omega x (p : M)) (D.src x) := by
  set G : ModN k → EuclideanSpace ℝ (Fin k) :=
    fun z => (D.ℓ (D.jx x)) (D.v ((D.domExt x).symm z)) with hG
  have hn : (((⊤ : ENat) : WithTop ENat) : ℕ∞ω) ≠ 0 := by simp
  have hdomxmax : D.domChart x ∈ IsManifold.maximalAtlas (𝓡∂ (NN k)) ((⊤ : ENat) : WithTop ENat) M :=
    Work.PTGeometric.Lvl.Setup.domChartAt_mem_maximalAtlas D.S x
  have hEqOn : ∀ p ∈ D.src x, D.Omega x (p : M) = fderiv ℝ G (D.domExt x (p : M)) := by
    intro p hp
    have hcs : p ∈ D.S.chartSource x := D.src_subset_chartSource x hp
    have hint : (p : M) ∈ (𝓡∂ (NN k)).interior M :=
      mem_interior_of_notMem_boundary (D.src_interior x hx hp)
    exact Omega_eq_fderiv D x hcs hint
  have hVcd : ∀ p ∈ D.src x, ContDiffAt ℝ ∞ (fun z : ModN k => D.v ((D.domExt x).symm z))
      (D.domExt x (p : M)) := by
    intro p hp
    have hcs : p ∈ D.S.chartSource x := D.src_subset_chartSource x hp
    have hint : (p : M) ∈ (𝓡∂ (NN k)).interior M :=
      mem_interior_of_notMem_boundary (D.src_interior x hx hp)
    have hz0 : D.domExt x (p : M) ∈ interior (range (𝓡∂ (NN k))) :=
      tcD_mem_interior_range (𝓡∂ (NN k)) hn hdomxmax hcs.1 hint
    have hmax' : chartAt (EuclideanSpace ℝ (Fin n)) (D.v (p : M)) ∈
        IsManifold.maximalAtlas (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ((⊤ : ENat) : WithTop ENat)
          (EuclideanSpace ℝ (Fin n)) :=
      IsManifold.chart_mem_maximalAtlas _
    have hiff := (contMDiffAt_iff_of_mem_maximalAtlas (I := 𝓡∂ (NN k))
      (I' := 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) (f := D.v) (n := ((⊤ : ENat) : WithTop ENat))
      (x := (p : M)) (e := D.domChart x) (e' := chartAt (EuclideanSpace ℝ (Fin n)) (D.v (p : M)))
      hdomxmax hmax' hcs.1 (mem_chart_source _ _)).mp (D.hvsm.contMDiffAt)
    have hkey : ((chartAt (EuclideanSpace ℝ (Fin n)) (D.v (p : M))).extend
          (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∘ D.v ∘ (D.domExt x).symm)
        = (fun z : ModN k => D.v ((D.domExt x).symm z)) := by
      funext z
      simp only [Function.comp_apply]
      show (↑(extChartAt (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) (D.v (p : M))) :
        EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
        (D.v ((D.domExt x).symm z)) = D.v ((D.domExt x).symm z)
      simp only [extChartAt_self_eq, modelWithCornersSelf_coe, id_eq]
    rw [hkey] at hiff
    exact hiff.2.contDiffAt (mem_of_superset (isOpen_interior.mem_nhds hz0) interior_subset)
  intro p hp
  have hfderiv : ContinuousAt (fderiv ℝ G) (D.domExt x (p : M)) :=
    (((D.ℓ (D.jx x)).contDiff.contDiffAt.comp (D.domExt x (p : M)) (hVcd p hp)
      ).continuousAt_fderiv) hn
  have hdomCont : ContinuousAt (fun q : D.S.Pre => D.domExt x (q : M)) p :=
    (OpenPartialHomeomorph.continuousAt_extend (D.domChart x) (I := 𝓡∂ (NN k))
      (D.src_subset_chartSource x hp).1).comp continuous_subtype_val.continuousAt
  have hcont : ContinuousAt (fun q : D.S.Pre => fderiv ℝ G (D.domExt x (q : M))) p :=
    hfderiv.comp (f := fun q : D.S.Pre => D.domExt x (q : M)) hdomCont
  exact (hcont.continuousWithinAt).congr (fun y hy => hEqOn y hy) (hEqOn p hp)

/-- **`Ω ↦ det (σ ∘ β.prod Ω)` is continuous**, for a fixed `β`. -/
theorem contDetProd (k : ℕ)
    (β : EuclideanSpace ℝ (Fin ((8 + k) + 1)) →L[ℝ] EuclideanSpace ℝ (Fin 9)) :
    Continuous (fun Ω : EuclideanSpace ℝ (Fin ((8 + k) + 1)) →L[ℝ] EuclideanSpace ℝ (Fin k) =>
      LinearMap.det ((sigma k).toLinearMap.comp ((β.prod Ω).toLinearMap))) := by
  have h1 : Continuous (fun Ω : EuclideanSpace ℝ (Fin ((8 + k) + 1)) →L[ℝ] EuclideanSpace ℝ (Fin k) =>
      (β.prod Ω : EuclideanSpace ℝ (Fin ((8 + k) + 1)) →L[ℝ]
        (EuclideanSpace ℝ (Fin 9) × EuclideanSpace ℝ (Fin k)))) := by
    have hplt := (ContinuousLinearMap.prodL ℝ :
      ((EuclideanSpace ℝ (Fin ((8 + k) + 1)) →L[ℝ] EuclideanSpace ℝ (Fin 9)) ×
        (EuclideanSpace ℝ (Fin ((8 + k) + 1)) →L[ℝ] EuclideanSpace ℝ (Fin k))) ≃L[ℝ]
        (EuclideanSpace ℝ (Fin ((8 + k) + 1)) →L[ℝ]
          (EuclideanSpace ℝ (Fin 9) × EuclideanSpace ℝ (Fin k)))).continuous
    have hc : Continuous (fun _ : EuclideanSpace ℝ (Fin ((8 + k) + 1)) →L[ℝ]
        EuclideanSpace ℝ (Fin k) => β) := continuous_const
    have hi : Continuous (fun Ω : EuclideanSpace ℝ (Fin ((8 + k) + 1)) →L[ℝ]
        EuclideanSpace ℝ (Fin k) => Ω) := continuous_id
    exact (hplt.comp (hc.prodMk hi)).congr
      (fun Ω => by rw [Function.comp_apply, ContinuousLinearMap.prodL_apply])
  have h3 : Continuous (fun Ω : EuclideanSpace ℝ (Fin ((8 + k) + 1)) →L[ℝ]
      EuclideanSpace ℝ (Fin k) =>
      (((sigma k).toLinearMap.toContinuousLinearMap).comp (β.prod Ω)).det) :=
    ContinuousLinearMap.continuous_det.comp
      ((ContinuousLinearMap.compL ℝ _ _ _
        ((sigma k).toLinearMap.toContinuousLinearMap)).continuous.comp h1)
  refine h3.congr (fun Ω => ?_)
  rfl

/-- **The determinant of `σ ∘ phiD x p` is continuous in `p` on `src x`** for an interior centre. -/
theorem continuousOn_sgnDet (D : Cof k n M) (x : D.S.Pre)
    (hx : (x : M) ∉ (𝓡∂ (NN k)).boundary M) :
    ContinuousOn (fun p : D.S.Pre =>
      LinearMap.det (((sigma k).toLinearMap).comp (D.phiD x (p : M)).toLinearMap)) (D.src x) := by
  have h1 : ContinuousOn (fun p : D.S.Pre => D.Omega x (p : M)) (D.src x) := contOmega D x hx
  have h2 : Continuous (fun Ω : ModN k →L[ℝ] EuclideanSpace ℝ (Fin k) =>
      LinearMap.det (((sigma k).toLinearMap).comp (((D.S.chartBeta x).prod Ω).toLinearMap))) :=
    contDetProd k (D.S.chartBeta x)
  have h3 := h2.comp_continuousOn h1
  show ContinuousOn (fun p : D.S.Pre =>
      LinearMap.det (((sigma k).toLinearMap).comp
        (((D.S.chartBeta x).prod (D.Omega x (p : M))).toLinearMap))) (D.src x)
  exact h3

/-! ## The target -/

theorem sgnConst
    {k n : ℕ} {M : Type} [TopologicalSpace M] [T2Space M] [CompactSpace M]
    [ChartedSpace (EuclideanHalfSpace ((8 + k) + 1)) M]
    [IsManifold (modelWithCornersEuclideanHalfSpace ((8 + k) + 1)) ((⊤ : ENat) : WithTop ENat) M]
    (D : Work.ThomBordism.CofAtlas.Cof k n M) (x : D.S.Pre)
    (hx : (x : M) ∉ (modelWithCornersEuclideanHalfSpace ((8 + k) + 1)).boundary M) :
    (∀ p : D.S.Pre, p ∈ D.src x → D.sgn x (p : M) = D.sgn x (x : M)) ∧
    (∀ p : D.S.Pre, p ∈ D.src x → D.sgn x (p : M) ≠ 0) := by
  have hint : ∀ (p : D.S.Pre), p ∈ D.src x → (p : M) ∈ (𝓡∂ (NN k)).interior M :=
    fun p hp => mem_interior_of_notMem_boundary (D.src_interior x hx hp)
  have hne : ∀ p ∈ D.src x,
      LinearMap.det (((sigma k).toLinearMap).comp (D.phiD x (p : M)).toLinearMap) ≠ 0 :=
    fun p hp => det_phiD_ne_zero D x hp (hint p hp)
  have hcont : ContinuousOn (fun p : D.S.Pre =>
      LinearMap.det (((sigma k).toLinearMap).comp (D.phiD x (p : M)).toLinearMap)) (D.src x) :=
    continuousOn_sgnDet D x hx
  constructor
  · intro p hp
    exact sign_eq_of_preconnected (D.isPreconnected_src x) hcont hne hp (D.mem_src_self x)
  · intro p hp
    exact sign_ne_zero.mpr (hne p hp)

end

end Work.ThomBordism.CofAtlas
