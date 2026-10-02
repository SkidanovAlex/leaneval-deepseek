import Mathlib
import Submission.Work.Thom.Iso
import Submission.Work.Thom.continuousOn_chartExpressionCLM
import Submission.Work.Thom.coreMorphism
import Submission.Work.Thom.complexPullback

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

/-!
# Pullback of a bundle isomorphism

A `BundleIso Z Z'` of two gluing data over a common base `B` pulls back along any continuous map
`f : C(B', B)` to a `BundleIso` of the pulled-back gluing data `bundleComap Z f`,
`bundleComap Z' f`: the fibrewise map at `b : B'` is `e.hom (f b)`.  This module provides that
construction together with the (field-general) continuity of the chart expression of a bundle
isomorphism, on which the continuity of the pulled-back total-space map rests.

Everything here is universe-polymorphic (`𝕜 : Type*`): the monomorphic
`Work.Thom.continuous_totalSpaceMap_clm` of `Submission/Work/Thom/coreMorphism.lean` cannot be
applied to a variable field of scalars, so a polymorphic copy is proved below.
-/

namespace Work.Thom

noncomputable section

open Work.TangentClasses

/-- **The fibrewise map of a bundle isomorphism, as a continuous linear map** (arbitrary complete
field of scalars and arbitrary finite-dimensional fibres).  A `𝕜`-linear map between
finite-dimensional spaces over a complete field is automatically continuous. -/
def BundleIso.clmGen {𝕜 : Type*} [RCLike 𝕜] {B : Type*} [TopologicalSpace B]
    {F F' : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] [FiniteDimensional 𝕜 F]
    [NormedAddCommGroup F'] [NormedSpace 𝕜 F'] {ι ι' : Type*}
    {Z : VectorBundleCore 𝕜 B F ι} {Z' : VectorBundleCore 𝕜 B F' ι'}
    (e : BundleIso Z Z') (b : B) : F →L[𝕜] F' :=
  let g : F →ₗ[𝕜] F' := e.hom b
  LinearMap.toContinuousLinearMap (𝕜 := 𝕜) (E := F) g

theorem BundleIso.clmGen_apply {𝕜 : Type*} [RCLike 𝕜] {B : Type*} [TopologicalSpace B]
    {F F' : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] [FiniteDimensional 𝕜 F]
    [NormedAddCommGroup F'] [NormedSpace 𝕜 F'] {ι ι' : Type*}
    {Z : VectorBundleCore 𝕜 B F ι} {Z' : VectorBundleCore 𝕜 B F' ι'}
    (e : BundleIso Z Z') (b : B) (v : F) : e.clmGen b v = e.hom b v := by
  show (LinearMap.toContinuousLinearMap (𝕜 := 𝕜) (E := F)
    (e.hom b : F →ₗ[𝕜] F')) v = e.hom b v
  rfl

/-- **Continuity of the total-space map of a bundle morphism over `f`, with a varying fibre map**
(universe-polymorphic version of `Work.Thom.continuous_totalSpaceMap_clm`).  If
`T : B' → (F →L[𝕜] F')` is such that, in every pair of charts `(i₁, i₂)`, the trivialised matrix
`b ↦ Z₂.coordChange (Z₂.indexAt (f b)) i₂ (f b) ∘ T b ∘ Z₁.coordChange i₁ (Z₁.indexAt b) b` is
continuous on the overlap, then `⟨x, v⟩ ↦ ⟨f x, T x v⟩` is a continuous map of total spaces. -/
theorem continuous_totalSpaceMap_clm_gen {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {B B' : Type*} [TopologicalSpace B] [TopologicalSpace B'] {F F' : Type*}
    [NormedAddCommGroup F] [NormedSpace 𝕜 F] [NormedAddCommGroup F'] [NormedSpace 𝕜 F']
    {ι ι' : Type*} (Z₁ : VectorBundleCore 𝕜 B' F ι) (Z₂ : VectorBundleCore 𝕜 B F' ι')
    (f : C(B', B)) (T : B' → F →L[𝕜] F')
    (hT : ∀ (i₁ : ι) (i₂ : ι'), ContinuousOn (fun b : B' =>
        (Z₂.coordChange (Z₂.indexAt (f b)) i₂ (f b)).comp
          ((T b).comp (Z₁.coordChange i₁ (Z₁.indexAt b) b)))
        (Z₁.baseSet i₁ ∩ f ⁻¹' Z₂.baseSet i₂)) :
    Continuous (fun p : Z₁.TotalSpace => (⟨f p.1, T p.1 p.2⟩ : Z₂.TotalSpace)) := by
  have hgOn : ∀ (i₁ : ι) (i₂ : ι'),
      ContinuousOn (fun p : Z₁.TotalSpace => (⟨f p.1, T p.1 p.2⟩ : Z₂.TotalSpace))
        ((Z₁.localTriv i₁).source ∩ Z₁.proj ⁻¹' (f ⁻¹' Z₂.baseSet i₂)) := by
    intro i₁ i₂
    have hcont : ContinuousOn (fun p : Z₁.TotalSpace =>
        (⟨f p.1, (Z₂.coordChange (Z₂.indexAt (f p.1)) i₂ (f p.1)) (T p.1 p.2)⟩ : B × F'))
        ((Z₁.localTriv i₁).source ∩ Z₁.proj ⁻¹' (f ⁻¹' Z₂.baseSet i₂)) := by
      have hrw : ∀ p ∈ (Z₁.localTriv i₁).source ∩ Z₁.proj ⁻¹' (f ⁻¹' Z₂.baseSet i₂),
          (⟨f p.1, (Z₂.coordChange (Z₂.indexAt (f p.1)) i₂ (f p.1)) (T p.1 p.2)⟩ : B × F')
            = (⟨f p.1, ((Z₂.coordChange (Z₂.indexAt (f p.1)) i₂ (f p.1)).comp
                ((T p.1).comp (Z₁.coordChange i₁ (Z₁.indexAt p.1) p.1)))
                ((Z₁.localTriv i₁) p).2⟩ : B × F') := by
        intro p hp
        congr 1
        have hinner : ((Z₁.localTriv i₁) p).2 = Z₁.coordChange (Z₁.indexAt p.1) i₁ p.1 p.2 := by
          rw [VectorBundleCore.localTriv_apply]
        have hcomp' : (Z₁.coordChange i₁ (Z₁.indexAt p.1) p.1)
            ((Z₁.coordChange (Z₁.indexAt p.1) i₁ p.1) p.2) = p.2 := by
          have hx : p.1 ∈ Z₁.baseSet (Z₁.indexAt p.1) ∩ Z₁.baseSet i₁ :=
            ⟨Z₁.mem_baseSet_at p.1, (VectorBundleCore.mem_localTriv_source Z₁ i₁ p).mp hp.1⟩
          have h := Z₁.coordChange_comp (Z₁.indexAt p.1) i₁ (Z₁.indexAt p.1) p.1
            ⟨hx, Z₁.mem_baseSet_at p.1⟩ p.2
          rwa [Z₁.coordChange_self (Z₁.indexAt p.1) p.1 (Z₁.mem_baseSet_at p.1) p.2] at h
        rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, hinner]
        exact congrArg (fun w => (Z₂.coordChange (Z₂.indexAt (f p.1)) i₂ (f p.1)) (T p.1 w))
          hcomp'.symm
      refine ContinuousOn.congr ?_ hrw
      have h1 : ContinuousOn (fun p : Z₁.TotalSpace => f p.1)
          ((Z₁.localTriv i₁).source ∩ Z₁.proj ⁻¹' (f ⁻¹' Z₂.baseSet i₂)) :=
        f.continuous.comp_continuousOn
          ((FiberBundle.continuous_proj F Z₁.Fiber).continuousOn)
      have hclm : ContinuousOn (fun p : Z₁.TotalSpace =>
          (Z₂.coordChange (Z₂.indexAt (f p.1)) i₂ (f p.1)).comp
            ((T p.1).comp (Z₁.coordChange i₁ (Z₁.indexAt p.1) p.1)))
          ((Z₁.localTriv i₁).source ∩ Z₁.proj ⁻¹' (f ⁻¹' Z₂.baseSet i₂)) := by
        have hb : Set.MapsTo (fun p : Z₁.TotalSpace => p.1)
            ((Z₁.localTriv i₁).source ∩ Z₁.proj ⁻¹' (f ⁻¹' Z₂.baseSet i₂))
            (Z₁.baseSet i₁ ∩ f ⁻¹' Z₂.baseSet i₂) := fun p hp =>
          ⟨(VectorBundleCore.mem_localTriv_source Z₁ i₁ p).mp hp.1, hp.2⟩
        exact ContinuousOn.comp (hT i₁ i₂)
          (FiberBundle.continuous_proj F Z₁.Fiber).continuousOn hb
      have hsnd : ContinuousOn (fun p : Z₁.TotalSpace => ((Z₁.localTriv i₁) p).2)
          ((Z₁.localTriv i₁).source ∩ Z₁.proj ⁻¹' (f ⁻¹' Z₂.baseSet i₂)) :=
        (Continuous.comp_continuousOn continuous_snd (Z₁.localTriv i₁).continuousOn).mono
          (fun x hx => hx.1)
      exact ContinuousOn.prodMk h1 (hclm.clm_apply hsnd)
    intro p hp
    have hmem : (⟨f p.1, (Z₂.coordChange (Z₂.indexAt (f p.1)) i₂ (f p.1)) (T p.1 p.2)⟩ : B × F')
        ∈ (Z₂.localTriv i₂).target := by
      rw [VectorBundleCore.mem_localTriv_target]; exact hp.2
    have hcomp : ContinuousWithinAt (fun p : Z₁.TotalSpace =>
        (⟨f p.1, (Z₂.coordChange (Z₂.indexAt (f p.1)) i₂ (f p.1)) (T p.1 p.2)⟩ : B × F'))
        ((Z₁.localTriv i₁).source ∩ Z₁.proj ⁻¹' (f ⁻¹' Z₂.baseSet i₂)) p :=
      hcont.continuousWithinAt hp
    let Ψ : B × F' → Z₂.TotalSpace := fun q => ⟨q.1, (Z₂.localTriv i₂).symm q.1 q.2⟩
    let Φ : Z₁.TotalSpace → B × F' := fun p =>
      (⟨f p.1, (Z₂.coordChange (Z₂.indexAt (f p.1)) i₂ (f p.1)) (T p.1 p.2)⟩ : B × F')
    have hsymm : ContinuousWithinAt Ψ ((Z₂.localTriv i₂).baseSet ×ˢ Set.univ) (Φ p) :=
      (Z₂.localTriv i₂).continuousOn_symm.continuousWithinAt (by
        simp only [Set.mem_prod, Set.mem_univ, and_true]; exact hp.2)
    have hfinal : ContinuousWithinAt (Ψ ∘ Φ)
        ((Z₁.localTriv i₁).source ∩ Z₁.proj ⁻¹' (f ⁻¹' Z₂.baseSet i₂)) p :=
      hsymm.comp hcomp (fun q hq =>
        (VectorBundleCore.mem_localTriv_target Z₂ i₂ (Φ q)).mpr
          (by simpa [Φ, VectorBundleCore.baseSet_at] using hq.2))
    have hpt : ∀ q ∈ (Z₁.localTriv i₁).source ∩ Z₁.proj ⁻¹' (f ⁻¹' Z₂.baseSet i₂),
        (⟨f q.1, T q.1 q.2⟩ : Z₂.TotalSpace) = Ψ (Φ q) := by
      intro q hq
      have hq2 : f q.1 ∈ Z₂.baseSet i₂ := hq.2
      show (⟨f q.1, T q.1 q.2⟩ : Z₂.TotalSpace)
        = (⟨f q.1, (Z₂.localTriv i₂).symm (f q.1)
        ((Z₂.coordChange (Z₂.indexAt (f q.1)) i₂ (f q.1)) (T q.1 q.2))⟩ : Z₂.TotalSpace)
      rw [VectorBundleCore.localTriv_symm_apply Z₂ i₂ hq2]
      congr 1
      have hcc := Z₂.coordChange_comp (Z₂.indexAt (f q.1)) i₂ (Z₂.indexAt (f q.1)) (f q.1)
        ⟨⟨Z₂.mem_baseSet_at (f q.1), hq2⟩, Z₂.mem_baseSet_at (f q.1)⟩ ((T q.1) q.2)
      rw [hcc, Z₂.coordChange_self (Z₂.indexAt (f q.1)) (f q.1)
        (Z₂.mem_baseSet_at (f q.1))]
    exact hfinal.congr hpt (hpt p hp)
  rw [continuous_iff_continuousAt]
  intro p
  refine (hgOn (Z₁.indexAt p.1) (Z₂.indexAt (f p.1))).continuousAt ?_
  refine (IsOpen.inter ?_ ?_).mem_nhds ⟨?_, ?_⟩
  · exact (Z₁.localTriv (Z₁.indexAt p.1)).open_source
  · exact (Z₂.isOpen_baseSet (Z₂.indexAt (f p.1))).preimage f.continuous
      |>.preimage (FiberBundle.continuous_proj F Z₁.Fiber)
  · exact (VectorBundleCore.mem_localTriv_source Z₁ (Z₁.indexAt p.1) p).mpr
      (Z₁.mem_baseSet_at p.1)
  · exact Z₂.mem_baseSet_at (f p.1)

/-- **A family of bounded linear maps between finite-dimensional spaces is continuous as soon as
its evaluations are.**  The expansion of `F` in a finite basis identifies `(Fin n → F')` with
`F →L[𝕜] F'` linearly. -/
theorem continuous_clm_of_continuous_apply_gen {𝕜 : Type*} [RCLike 𝕜]
    {F F' : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] [FiniteDimensional 𝕜 F]
    [NormedAddCommGroup F'] [NormedSpace 𝕜 F'] [FiniteDimensional 𝕜 F']
    {X : Type*} [TopologicalSpace X] (D : X → (F →L[𝕜] F'))
    (h : Continuous fun p : X × F => D p.1 p.2) : Continuous D := by
  classical
  let b : Module.Basis (Fin (Module.finrank 𝕜 F)) 𝕜 F := Module.finBasis 𝕜 F
  let L : (Fin (Module.finrank 𝕜 F) → F') →ₗ[𝕜] (F →ₗ[𝕜] F') := (b.constr 𝕜).toLinearMap
  let Ψ : (Fin (Module.finrank 𝕜 F) → F') →ₗ[𝕜] (F →L[𝕜] F') :=
    (LinearMap.toContinuousLinearMap (𝕜 := 𝕜)).toLinearMap.comp L
  have hΨ : Continuous Ψ := LinearMap.continuous_of_finiteDimensional Ψ
  have hL : ∀ (w : Fin (Module.finrank 𝕜 F) → F') (i : Fin (Module.finrank 𝕜 F)),
      L w (b i) = w i := by
    intro w i
    show (b.constr 𝕜 w) (b i) = w i
    rw [Module.Basis.constr_basis]
  have hD : ∀ x, Ψ (fun i => D x (b i)) = D x := by
    intro x
    apply ContinuousLinearMap.coe_injective
    apply b.ext
    intro i
    show L (fun i => D x (b i)) (b i) = D x (b i)
    rw [hL]
  have hcont : Continuous (fun x : X => fun i => D x (b i)) :=
    continuous_pi (fun i => h.comp (continuous_id.prodMk continuous_const))
  rw [show D = fun x => Ψ (fun i => D x (b i)) from funext (fun x => (hD x).symm)]
  exact hΨ.comp hcont

/-- **The chart expression of a bundle isomorphism is continuous** (arbitrary field of scalars,
arbitrary finite-dimensional fibres).  For a bundle isomorphism `e : Z ≅ Z'` over a common base,
the composite of the transition function into the chart `i` of `Z`, the fibrewise map of `e` (as a
continuous linear map), and the transition function out of the chart `i'` of `Z'` is continuous on
`Z.baseSet i ∩ Z'.baseSet i'`. -/
theorem continuousOn_chartExpressionCLM_gen {𝕜 : Type*} [RCLike 𝕜] {B : Type*}
    [TopologicalSpace B] {F F' : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    [FiniteDimensional 𝕜 F] [NormedAddCommGroup F'] [NormedSpace 𝕜 F'] [FiniteDimensional 𝕜 F']
    {ι ι' : Type*} (Z : VectorBundleCore 𝕜 B F ι) (Z' : VectorBundleCore 𝕜 B F' ι')
    (e : BundleIso Z Z') (i : ι) (i' : ι') :
    ContinuousOn (fun b : B =>
      (Z'.coordChange (Z'.indexAt b) i' b).comp
        ((e.clmGen b).comp (Z.coordChange i (Z.indexAt b) b)))
      (Z.baseSet i ∩ Z'.baseSet i') := by
  let T : Set B := Z.baseSet i ∩ Z'.baseSet i'
  let D : B → (F →L[𝕜] F') := fun b =>
    (Z'.coordChange (Z'.indexAt b) i' b).comp
      ((e.clmGen b).comp (Z.coordChange i (Z.indexAt b) b))
  change ContinuousOn D T
  have hΦ : ContinuousOn (fun p : B × F => ((Z'.localTriv i')
      (e.toTotalSpace ((Z.localTriv i).toOpenPartialHomeomorph.symm p))).2)
      (T ×ˢ (Set.univ : Set F)) := by
    have h1 : ContinuousOn (fun p : B × F => (Z.localTriv i).toOpenPartialHomeomorph.symm p)
        (Z.baseSet i ×ˢ (Set.univ : Set F)) :=
      (Z.localTriv i).toOpenPartialHomeomorph.continuousOn_symm
    have h1' : ContinuousOn (fun p : B × F => (Z.localTriv i).toOpenPartialHomeomorph.symm p)
        (T ×ˢ (Set.univ : Set F)) :=
      h1.mono (fun p hp => ⟨hp.1.1, hp.2⟩)
    have h2 : ContinuousOn (fun p : B × F =>
        e.toTotalSpace ((Z.localTriv i).toOpenPartialHomeomorph.symm p))
        (T ×ˢ (Set.univ : Set F)) :=
      e.continuous_hom.continuousOn.comp h1' (fun p _ => Set.mem_univ _)
    have h3 : ContinuousOn (fun p : B × F => (Z'.localTriv i')
        (e.toTotalSpace ((Z.localTriv i).toOpenPartialHomeomorph.symm p)))
        (T ×ˢ (Set.univ : Set F)) :=
      (Z'.localTriv i').continuousOn.comp h2 (fun p hp => by
        rw [Bundle.Trivialization.mem_source]
        show (e.toTotalSpace ((Z.localTriv i).toOpenPartialHomeomorph.symm p)).1 ∈ Z'.baseSet i'
        rw [show (e.toTotalSpace ((Z.localTriv i).toOpenPartialHomeomorph.symm p)).1 = p.1
          from rfl]
        exact hp.1.2)
    exact h3.snd
  have hkey : ∀ (b : ↥T) (v : F),
      ((Z'.localTriv i')
        (e.toTotalSpace ((Z.localTriv i).toOpenPartialHomeomorph.symm ((b : B), v)))).2
        = D (b : B) v := by
    intro b v
    show (Z'.coordChange (Z'.indexAt (b : B)) i' (b : B))
        (e.hom (b : B) ((Z.coordChange i (Z.indexAt (b : B)) (b : B)) v))
      = ((Z'.coordChange (Z'.indexAt (b : B)) i' (b : B)).comp
          ((e.clmGen (b : B)).comp
            (Z.coordChange i (Z.indexAt (b : B)) (b : B)))) v
    rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
      BundleIso.clmGen_apply]
  have hg : Continuous (fun p : ↥T × F => (((p.1 : ↥T) : B), p.2)) :=
    (continuous_subtype_val.comp continuous_fst).prodMk continuous_snd
  have hjoint : Continuous (fun p : ↥T × F => D (p.1 : B) p.2) := by
    have hc := hΦ.comp_continuous hg (fun p => by exact ⟨p.1.2, Set.mem_univ _⟩)
    exact hc.congr (fun p => hkey p.1 p.2)
  have hD : Continuous (fun b : ↥T => D (b : B)) :=
    continuous_clm_of_continuous_apply_gen (fun b : ↥T => D (b : B)) hjoint
  exact (continuousOn_iff_continuous_domRestrict (f := D) (s := T)).mpr hD

/-- **Pullback of a bundle isomorphism.**  A bundle isomorphism `e : Z ≅ Z'` between two gluing
data over `B` pulls back along a continuous map `f : C(B', B)` to an isomorphism of the pulled-back
gluing data; the fibrewise linear map at `b : B'` is `e.hom (f b)`. -/
theorem BundleIso_comap_exists {𝕜 : Type*} [RCLike 𝕜] {B B' : Type*} [TopologicalSpace B]
    [TopologicalSpace B'] {F F' : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    [FiniteDimensional 𝕜 F] [NormedAddCommGroup F'] [NormedSpace 𝕜 F'] [FiniteDimensional 𝕜 F']
    {ι ι' : Type*} (Z : VectorBundleCore 𝕜 B F ι) (Z' : VectorBundleCore 𝕜 B F' ι')
    (e : BundleIso Z Z') (f : C(B', B)) :
    Nonempty (BundleIso (bundleComap Z f) (bundleComap Z' f)) := by
  have hT : ∀ (i₁ : ι) (i₂ : ι'), ContinuousOn (fun b : B' =>
      ((bundleComap Z' f).coordChange ((bundleComap Z' f).indexAt b) i₂ b).comp
        ((e.clmGen (f b)).comp
          ((bundleComap Z f).coordChange i₁ ((bundleComap Z f).indexAt b) b)))
      ((bundleComap Z f).baseSet i₁ ∩ (bundleComap Z' f).baseSet i₂) := by
    intro i₁ i₂
    have hbase := continuousOn_chartExpressionCLM_gen Z Z' e i₁ i₂
    have hcomp : ContinuousOn (fun b : B' =>
        (Z'.coordChange (Z'.indexAt (f b)) i₂ (f b)).comp
          ((e.clmGen (f b)).comp (Z.coordChange i₁ (Z.indexAt (f b)) (f b))))
        (f ⁻¹' (Z.baseSet i₁ ∩ Z'.baseSet i₂)) :=
      hbase.comp f.continuous.continuousOn (fun x hx => hx)
    simpa only [bundleComap_baseSet, Set.preimage_inter, bundleComap_coordChange,
      bundleComap_indexAt] using hcomp
  have hT' : ∀ (i₁ : ι') (i₂ : ι), ContinuousOn (fun b : B' =>
      ((bundleComap Z f).coordChange ((bundleComap Z f).indexAt b) i₂ b).comp
        (((BundleIso.symm e).clmGen (f b)).comp
          ((bundleComap Z' f).coordChange i₁ ((bundleComap Z' f).indexAt b) b)))
      ((bundleComap Z' f).baseSet i₁ ∩ (bundleComap Z f).baseSet i₂) := by
    intro i₁ i₂
    have hbase := continuousOn_chartExpressionCLM_gen Z' Z (BundleIso.symm e) i₁ i₂
    have hcomp : ContinuousOn (fun b : B' =>
        (Z.coordChange (Z.indexAt (f b)) i₂ (f b)).comp
          (((BundleIso.symm e).clmGen (f b)).comp
            (Z'.coordChange i₁ (Z'.indexAt (f b)) (f b))))
        (f ⁻¹' (Z'.baseSet i₁ ∩ Z.baseSet i₂)) :=
      hbase.comp f.continuous.continuousOn (fun x hx => hx)
    simpa only [bundleComap_baseSet, Set.preimage_inter, bundleComap_coordChange,
      bundleComap_indexAt] using hcomp
  refine ⟨{ hom := fun b => e.hom (f b)
            inv := fun b => e.inv (f b)
            left_inv := fun b x => e.left_inv (f b) x
            right_inv := fun b y => e.right_inv (f b) y
            continuous_hom := ?_
            continuous_inv := ?_ }⟩
  · have hc := continuous_totalSpaceMap_clm_gen (bundleComap Z f) (bundleComap Z' f)
      (ContinuousMap.id B') (fun b : B' => e.clmGen (f b)) (by
        intro i₁ i₂
        simpa using hT i₁ i₂)
    refine hc.congr (fun p => ?_)
    apply Bundle.TotalSpace.ext
    · rfl
    · exact heq_of_eq (BundleIso.clmGen_apply e (f p.1) p.2)
  · have hc := continuous_totalSpaceMap_clm_gen (bundleComap Z' f) (bundleComap Z f)
      (ContinuousMap.id B') (fun b : B' => (BundleIso.symm e).clmGen (f b)) (by
        intro i₁ i₂
        simpa using hT' i₁ i₂)
    refine hc.congr (fun p => ?_)
    apply Bundle.TotalSpace.ext
    · rfl
    · exact heq_of_eq (BundleIso.clmGen_apply (BundleIso.symm e) (f p.1) p.2)

end

end Work.Thom
