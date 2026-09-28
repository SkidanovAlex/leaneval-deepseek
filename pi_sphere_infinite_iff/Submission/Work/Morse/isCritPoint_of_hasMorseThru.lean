import Mathlib
import Submission.Work.Morse.Basic

set_option synthInstance.maxHeartbeats 400000

namespace Work.Morse

open scoped Manifold ContDiff Topology

/-!
# A point at which `f - f x` is a quadratic form in a chart is critical

`HasMorseThru f x` says that in some chart `e` at `x` (centred at `0`, i.e. `e x = 0`) the function
`f - f x` is *exactly* the quadratic form `y ↦ A y y` of a (nondegenerate) bilinear form, near `0`.
Since a quadratic form has vanishing derivative at the origin, `f` is critical at `x`.

The proof is a computation with the manifold derivative.  Writing `g = f ∘ e.symm`, the hypothesis
makes `g` equal to a quadratic form near `0`, whence `mfderiv g 0 = fderiv ℝ g 0 = 0`; this also
gives that `g` is differentiable at `0`, and reading differentiability in the chart `e`
(`mdifferentiableWithinAt_iff_source_of_mem_maximalAtlas`) gives that `f` is differentiable at `x`.
The chain rule for `e.symm ∘ e` identifies `(mfderiv e.symm 0) ∘ (mfderiv e x) = id`, and the chain
rule for `f ∘ e.symm` gives
`(mfderiv f x) ∘ (mfderiv e.symm 0) = mfderiv (f ∘ e.symm) 0 = 0`, so that
`mfderiv f x = (mfderiv f x) ∘ (mfderiv e.symm 0) ∘ (mfderiv e x) = 0`.
-/

set_option backward.isDefEq.respectTransparency false in
/-- If, in some chart `e` at `x` of the `C^∞` maximal atlas with `e x = 0`, the function
`f - f x` agrees near `0` with the quadratic form `y ↦ A y y` of a continuous bilinear form `A`,
then the manifold derivative of `f` at `x` vanishes. -/
theorem mfderiv_eq_zero_of_eventuallyEq_quadraticForm {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    {f : M → ℝ} {x : M} {e : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))}
    (he : e ∈ IsManifold.maximalAtlas (𝓡 n) ∞ M) (hx : x ∈ e.source) (hep : e x = 0)
    (A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)
    (hAeq : ∀ᶠ y in 𝓝 (0 : EuclideanSpace ℝ (Fin n)), f (e.symm y) - f x = A y y) :
    mfderiv (𝓡 n) 𝓘(ℝ,ℝ) f x = 0 := by
  have he1 : e ∈ IsManifold.maximalAtlas (𝓡 n) 1 M :=
    IsManifold.maximalAtlas_subset_of_le (I := 𝓡 n) (M := M) (m := 1) (n := ∞) (by simp) he
  -- `f ∘ e.symm` agrees with a quadratic form near `0`
  have hev : (fun y : EuclideanSpace ℝ (Fin n) => f (e.symm y)) =ᶠ[𝓝 0]
      (fun y : EuclideanSpace ℝ (Fin n) => f x + A y y) := by
    filter_upwards [hAeq] with y hy
    linarith
  -- a quadratic form is differentiable at `0` with vanishing derivative
  have hquad : HasFDerivAt (fun y : EuclideanSpace ℝ (Fin n) => A y y)
      (0 : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) 0 := by
    have hh := ContinuousLinearMap.hasFDerivAt_of_bilinear (𝕜 := ℝ) (B := A)
      (G' := EuclideanSpace ℝ (Fin n))
      (f := fun y : EuclideanSpace ℝ (Fin n) => y)
      (g := fun y : EuclideanSpace ℝ (Fin n) => y)
      (f' := ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n)))
      (g' := ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n)))
      (x := 0)
      (hasFDerivAt_id (𝕜 := ℝ) (E := EuclideanSpace ℝ (Fin n)) 0)
      (hasFDerivAt_id (𝕜 := ℝ) (E := EuclideanSpace ℝ (Fin n)) 0)
    simpa using hh
  have hFdiff : DifferentiableAt ℝ (fun y : EuclideanSpace ℝ (Fin n) => f (e.symm y)) 0 :=
    (hev.differentiableAt_iff).2 (hquad.differentiableAt.const_add (f x))
  -- hence `mfderiv (f ∘ e.symm) 0 = 0`
  have hFzero : mfderiv (𝓡 n) 𝓘(ℝ,ℝ)
      (fun y : EuclideanSpace ℝ (Fin n) => f (e.symm y)) 0 = 0 := by
    have hkey : mfderiv (𝓡 n) 𝓘(ℝ,ℝ) (fun y : EuclideanSpace ℝ (Fin n) => f (e.symm y)) 0
        = mfderiv (𝓡 n) 𝓘(ℝ,ℝ) (fun y : EuclideanSpace ℝ (Fin n) => f x + A y y) 0 :=
      Filter.EventuallyEq.mfderiv_eq (𝕜 := ℝ) (I := 𝓡 n) (I' := 𝓘(ℝ,ℝ)) hev
    rw [hkey, mfderiv_eq_fderiv, fderiv_const_add, hquad.fderiv]
    -- Lean v4.35 / Mathlib 5e0c4e5: `mfderiv_eq_fderiv` now leaves explicit `fromTangentSpace` casts
    all_goals first | rfl | simp
  -- `f` is differentiable at `x`, by reading differentiability in the chart `e`
  have hfmd : MDifferentiableAt (𝓡 n) 𝓘(ℝ,ℝ) f x := by
    rw [← mdifferentiableWithinAt_univ]
    rw [mdifferentiableWithinAt_iff_source_of_mem_maximalAtlas (𝕜 := ℝ) (I := 𝓡 n) (I' := 𝓘(ℝ,ℝ))
      (H := EuclideanSpace ℝ (Fin n)) (M' := ℝ) he1 hx (s := Set.univ)]
    have hfun : (f ∘ ⇑(e.extend (𝓡 n)).symm)
        = (fun y : EuclideanSpace ℝ (Fin n) => f (e.symm y)) := by
      funext y
      simp only [Function.comp_apply, OpenPartialHomeomorph.extend_coe_symm,
        modelWithCornersSelf_coe_symm, id_eq]
    have hset : (⇑(e.extend (𝓡 n)).symm ⁻¹' (Set.univ : Set M) ∩ Set.range (𝓡 n))
        = (Set.univ : Set (EuclideanSpace ℝ (Fin n))) := by
      rw [ModelWithCorners.range_eq_univ (𝓡 n), Set.preimage_univ, Set.univ_inter]
    have hpt : (e.extend (𝓡 n)) x = 0 := by
      rw [OpenPartialHomeomorph.extend_coe]
      simp only [Function.comp_apply, modelWithCornersSelf_coe, id_eq, hep]
    rw [hfun, hset, hpt, mdifferentiableWithinAt_iff_differentiableWithinAt,
      differentiableWithinAt_univ]
    exact hFdiff
  -- the derivatives of `e` and `e.symm` are mutually inverse
  have hde : MDifferentiableAt (𝓡 n) (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) (⇑e) x :=
    mdifferentiableAt_of_mem_maximalAtlas (I := 𝓡 n) he1 hx
  have hdsymm : MDifferentiableAt (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) (𝓡 n) (⇑e.symm) (e x) :=
    mdifferentiableAt_symm_of_mem_maximalAtlas (I := 𝓡 n) he1 (e.map_source hx)
  have hid_eq : (id : M → M) =ᶠ[𝓝 x] (⇑e.symm ∘ ⇑e) := by
    filter_upwards [e.open_source.mem_nhds hx] with y hy
    exact (e.left_inv hy).symm
  have hcomp : (mfderiv (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) (𝓡 n) (⇑e.symm) 0).comp
      (mfderiv (𝓡 n) (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) (⇑e) x)
      = ContinuousLinearMap.id ℝ (TangentSpace (𝓡 n) x) := by
    have h := mfderiv_comp (𝕜 := ℝ) (I := 𝓡 n) (I' := 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
      (I'' := 𝓡 n) (f := ⇑e) (g := ⇑e.symm) x hdsymm hde
    rw [hep] at h
    have hid : mfderiv (𝓡 n) (𝓡 n) (id : M → M) x
        = mfderiv (𝓡 n) (𝓡 n) (⇑e.symm ∘ ⇑e) x :=
      Filter.EventuallyEq.mfderiv_eq (𝕜 := ℝ) (I := 𝓡 n) (I' := 𝓡 n) hid_eq
    rw [← h, ← hid]
    exact mfderiv_id
  -- and the chain rule for `f ∘ e.symm`
  have hchain : (mfderiv (𝓡 n) 𝓘(ℝ,ℝ) f x).comp
      (mfderiv (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) (𝓡 n) (⇑e.symm) 0)
      = mfderiv (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) 𝓘(ℝ,ℝ)
          (fun y : EuclideanSpace ℝ (Fin n) => f (e.symm y)) 0 := by
    have hdsymm0 : MDifferentiableAt (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) (𝓡 n) (⇑e.symm) 0 := by
      simpa only [hep] using hdsymm
    have hsymm0 : e.symm (0 : EuclideanSpace ℝ (Fin n)) = x := by
      rw [← hep]
      exact e.left_inv hx
    have hfmd' : MDifferentiableAt (𝓡 n) 𝓘(ℝ,ℝ) f (e.symm 0) := by
      rw [hsymm0]
      exact hfmd
    have h := mfderiv_comp (𝕜 := ℝ) (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) (I' := 𝓡 n)
      (I'' := 𝓘(ℝ,ℝ)) (f := ⇑e.symm) (g := f) 0 hfmd' hdsymm0
    rw [hsymm0] at h
    exact h.symm
  -- putting the three identities together
  have h1 : (mfderiv (𝓡 n) 𝓘(ℝ,ℝ) f x).comp
        ((mfderiv (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) (𝓡 n) (⇑e.symm) 0).comp
          (mfderiv (𝓡 n) (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) (⇑e) x))
      = mfderiv (𝓡 n) 𝓘(ℝ,ℝ) f x := by
    rw [hcomp, ContinuousLinearMap.comp_id]
  have h2 : (mfderiv (𝓡 n) 𝓘(ℝ,ℝ) f x).comp
        ((mfderiv (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) (𝓡 n) (⇑e.symm) 0).comp
          (mfderiv (𝓡 n) (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) (⇑e) x)) = 0 := by
    rw [← ContinuousLinearMap.comp_assoc, hchain, hFzero, ContinuousLinearMap.zero_comp]
  exact h1.symm.trans h2

/-- A point at which `f - f x` is exactly a quadratic form in some chart (the conclusion of the
Morse lemma, `HasMorseThru`) is a critical point of `f`. -/
theorem isCritPoint_of_hasMorseThru {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    {f : M → ℝ} {x : M} (h : HasMorseThru (n := n) f x) : IsCritPoint (n := n) f x := by
  obtain ⟨e, he, hx, hep, A, _, hAeq⟩ := h
  rw [IsCritPoint]
  exact mfderiv_eq_zero_of_eventuallyEq_quadraticForm he hx hep A hAeq

end Work.Morse
