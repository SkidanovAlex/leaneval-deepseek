import Mathlib
import Submission.Work.Thom.tautQuotientCore_defs

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false

namespace Work.Thom

open Bundle

/-- **A family of endomorphisms of a finite-dimensional space is continuous as soon as its
evaluations are.**  This is the "matrix entries" criterion for a family of continuous linear
endomorphisms of a finite-dimensional normed space over a complete field: the expansion in a
finite basis identifies `F →L[𝕜] F` with `Fin n → F` linearly, and both spaces are
finite-dimensional, so this identification is a homeomorphism. -/
theorem continuous_clm_of_continuous_apply_finD {𝕜 : Type*} [RCLike 𝕜]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] [FiniteDimensional 𝕜 F]
    {X : Type*} [TopologicalSpace X] (D : X → (F →L[𝕜] F))
    (h : Continuous fun p : X × F => D p.1 p.2) : Continuous D := by
  classical
  let b : Module.Basis (Fin (Module.finrank 𝕜 F)) 𝕜 F := Module.finBasis 𝕜 F
  let L : (Fin (Module.finrank 𝕜 F) → F) →ₗ[𝕜] (F →ₗ[𝕜] F) := (b.constr 𝕜).toLinearMap
  let Ψ : (Fin (Module.finrank 𝕜 F) → F) →ₗ[𝕜] (F →L[𝕜] F) :=
    (LinearMap.toContinuousLinearMap (𝕜 := 𝕜)).toLinearMap.comp L
  have hΨ : Continuous Ψ := LinearMap.continuous_of_finiteDimensional Ψ
  have hL : ∀ (w : Fin (Module.finrank 𝕜 F) → F) (i : Fin (Module.finrank 𝕜 F)),
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

/-- **The chart expression of a bundle isomorphism is continuous.**  For a bundle isomorphism
`f : Z ≅ Z'` between two gluing data of rank `m+1` over a common base, the composite of the
transition function into the chart `i` of `Z`, the fibrewise map of `f`, and the transition
function out of the chart `i'` of `Z'` is continuous on `Z.baseSet i ∩ Z'.baseSet i'`.

The proof reads the expression in the trivializations `Z.localTriv i` and `Z'.localTriv i'`: on
`Z.baseSet i ∩ Z'.baseSet i'` it is the second component of
`(Z'.localTriv i') ∘ f.toTotalSpace ∘ (Z.localTriv i).symm`, which is continuous by the continuity
of the two trivializations (on their sources) and of the map of total spaces induced by `f`, and
the fibrewise statement follows from `continuous_clm_of_continuous_apply_finD`. -/
theorem continuousOn_chartExpressionCLM {m : ℕ} {B : Type} [TopologicalSpace B] {ι ι' : Type}
    (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin (m+1))) ι)
    (Z' : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin (m+1))) ι')
    (f : Work.Thom.BundleIso Z Z') (i : ι) (i' : ι') :
    ContinuousOn (fun b : B =>
      (Z'.coordChange (Z'.indexAt b) i' b).comp ((f.clm b).comp (Z.coordChange i (Z.indexAt b) b)))
      (Z.baseSet i ∩ Z'.baseSet i') := by
  let F := EuclideanSpace ℂ (Fin (m+1))
  let T : Set B := Z.baseSet i ∩ Z'.baseSet i'
  let D : B → (F →L[ℂ] F) := fun b =>
    (Z'.coordChange (Z'.indexAt b) i' b).comp ((f.clm b).comp (Z.coordChange i (Z.indexAt b) b))
  change ContinuousOn D T
  have hΦ : ContinuousOn (fun p : B × F => ((Z'.localTriv i')
      (f.toTotalSpace ((Z.localTriv i).toOpenPartialHomeomorph.symm p))).2)
      (T ×ˢ (Set.univ : Set F)) := by
    have h1 : ContinuousOn (fun p : B × F => (Z.localTriv i).toOpenPartialHomeomorph.symm p)
        (Z.baseSet i ×ˢ (Set.univ : Set F)) :=
      (Z.localTriv i).toOpenPartialHomeomorph.continuousOn_symm
    have h1' : ContinuousOn (fun p : B × F => (Z.localTriv i).toOpenPartialHomeomorph.symm p)
        (T ×ˢ (Set.univ : Set F)) :=
      h1.mono (fun p hp => ⟨hp.1.1, hp.2⟩)
    have h2 : ContinuousOn (fun p : B × F =>
        f.toTotalSpace ((Z.localTriv i).toOpenPartialHomeomorph.symm p))
        (T ×ˢ (Set.univ : Set F)) :=
      f.continuous_hom.continuousOn.comp h1' (fun p _ => Set.mem_univ _)
    have h3 : ContinuousOn (fun p : B × F => (Z'.localTriv i')
        (f.toTotalSpace ((Z.localTriv i).toOpenPartialHomeomorph.symm p)))
        (T ×ˢ (Set.univ : Set F)) :=
      (Z'.localTriv i').continuousOn.comp h2 (fun p hp => by
        rw [Bundle.Trivialization.mem_source]
        show (f.toTotalSpace ((Z.localTriv i).toOpenPartialHomeomorph.symm p)).1 ∈ Z'.baseSet i'
        rw [show (f.toTotalSpace ((Z.localTriv i).toOpenPartialHomeomorph.symm p)).1 = p.1
          from rfl]
        exact hp.1.2)
    exact h3.snd
  have hkey : ∀ (b : ↥T) (v : F),
      ((Z'.localTriv i')
        (f.toTotalSpace ((Z.localTriv i).toOpenPartialHomeomorph.symm ((b : B), v)))).2
        = D (b : B) v := by
    intro b v
    show (Z'.coordChange (Z'.indexAt (b:B)) i' (b:B))
        (f.hom (b:B) ((Z.coordChange i (Z.indexAt (b:B)) (b:B)) v))
      = ((Z'.coordChange (Z'.indexAt (b:B)) i' (b:B)).comp
          ((f.clm (b:B)).comp (Z.coordChange i (Z.indexAt (b:B)) (b:B)))) v
    rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
      Work.Thom.BundleIso.clm_apply]
  have hg : Continuous (fun p : ↥T × F => (((p.1 : ↥T) : B), p.2)) :=
    (continuous_subtype_val.comp continuous_fst).prodMk continuous_snd
  have hjoint : Continuous (fun p : ↥T × F => D (p.1 : B) p.2) := by
    have hc := hΦ.comp_continuous hg (fun p => by exact ⟨p.1.2, Set.mem_univ _⟩)
    exact hc.congr (fun p => hkey p.1 p.2)
  have hD : Continuous (fun b : ↥T => D (b : B)) :=
    continuous_clm_of_continuous_apply_finD (fun b : ↥T => D (b : B)) hjoint
  exact (continuousOn_iff_continuous_domRestrict (f := D) (s := T)).mpr hD

end Work.Thom
