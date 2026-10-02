import Mathlib
import Submission.Work.Surgery.BoundaryInstances

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Restriction of a diffeomorphism of manifolds with boundary to the boundary

For an `(n+1)`-manifold `M` with boundary modelled on the half-space `EuclideanHalfSpace (n+1)`,
the boundary `∂M = (𝓡∂ (n+1)).boundary M` carries the preferred charted space structure
`Work.Surgery.boundaryChartedSpace` of `Submission/Work/Surgery/Boundary.lean`, and is a smooth
`n`-manifold modelled on the boundaryless model `𝓡 n` (`bnd_isManifold`, registered as the
instance `bndIsManifold`).

This file proves **`Work.Surgery.bnd_diffeomorph`**: a diffeomorphism `Φ : M ≃ₘ⟮𝓡∂ (n+1)⟯ N`
of manifolds with boundary restricts to a diffeomorphism `∂M ≃ₘ⟮𝓡 n⟯ ∂N` of their boundaries.

The construction is the evident one: `Equiv`-wise it is the restriction of `Φ`, which is a
bijection of `∂M` onto `∂N` because `Φ '' ∂M = ∂N` (`Diffeomorph.image_boundary`).  Smoothness
of the restriction is checked in the boundary charts: by `contMDiffWithinAt_iff'` it is enough to
test the composite

`(boundaryChartAt (Φ p)) ∘ Φ ∘ (boundaryChartAt p).symm`

on the set where it is defined, and there (using the formulas `boundaryChartAt_apply` and
`boundaryChartAt_symm`) it is the composition of the ambient chart transition
`z ↦ extChartAt (Φ p) (Φ ((extChartAt p).symm z))` -- smooth because `Φ` is -- with the linear
insertion `consZeroCLM n` of a zero first coordinate and the linear deletion `tailCLM n`.
-/

open scoped Manifold Topology ContDiff
open Function Set

namespace Work.Surgery

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace (n + 1)) M]
    [IsManifold (modelWithCornersEuclideanHalfSpace (n + 1)) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    {N : Type*} [TopologicalSpace N] [ChartedSpace (EuclideanHalfSpace (n + 1)) N]
    [IsManifold (modelWithCornersEuclideanHalfSpace (n + 1)) ((⊤ : ℕ∞) : WithTop ℕ∞) N]

/-! ## Rewriting the extended charts of the boundary (modelled on `𝓡 n`)

On the boundary manifold, whose model is the *boundaryless* self model `𝓡 n`, the extended chart
`extChartAt (𝓡 n) p` is just the preferred chart `boundaryChartAt p`, and similarly for its
source, target, inverse and value at the centre. -/

theorem extChartAt_bnd_apply (p : (𝓡∂ (n + 1)).boundary M) :
    ⇑(extChartAt (𝓡 n) p) = ⇑(boundaryChartAt (n := n) (M := M) p) := by simp

theorem extChartAt_bnd_symm (p : (𝓡∂ (n + 1)).boundary M) :
    ⇑(extChartAt (𝓡 n) p).symm = ⇑(boundaryChartAt (n := n) (M := M) p).symm := by simp

theorem extChartAt_bnd_source (p : (𝓡∂ (n + 1)).boundary M) :
    (extChartAt (𝓡 n) p).source = (boundaryChartAt (n := n) (M := M) p).source := by simp

theorem extChartAt_bnd_target (p : (𝓡∂ (n + 1)).boundary M) :
    (extChartAt (𝓡 n) p).target = (boundaryChartAt (n := n) (M := M) p).target := by simp

/-! ## The restriction of `Φ` to the boundary, as a bijection -/

/-- A diffeomorphism of manifolds with boundary maps the boundary onto the boundary. -/
theorem bnd_mapsTo (Φ : M ≃ₘ⟮𝓡∂ (n + 1), 𝓡∂ (n + 1)⟯ N) :
    MapsTo Φ ((𝓡∂ (n + 1)).boundary M) ((𝓡∂ (n + 1)).boundary N) := by
  intro x hx
  rw [← Diffeomorph.image_boundary (I := 𝓡∂ (n + 1)) (I' := 𝓡∂ (n + 1))
    (n := (∞ : WithTop ℕ∞)) (by simp) Φ]
  exact mem_image_of_mem Φ hx

/-- **The restriction of a diffeomorphism to the boundary**, as a bijection. -/
def bndEquiv (Φ : M ≃ₘ⟮𝓡∂ (n + 1), 𝓡∂ (n + 1)⟯ N) :
    ((𝓡∂ (n + 1)).boundary M) ≃ ((𝓡∂ (n + 1)).boundary N) where
  toFun p := ⟨Φ p.1, bnd_mapsTo Φ p.2⟩
  invFun q := ⟨Φ.symm q.1, bnd_mapsTo Φ.symm q.2⟩
  left_inv p := Subtype.ext (Diffeomorph.symm_apply_apply Φ p.1)
  right_inv q := Subtype.ext (Diffeomorph.apply_symm_apply Φ q.1)

@[simp] theorem bndEquiv_apply_coe (Φ : M ≃ₘ⟮𝓡∂ (n + 1), 𝓡∂ (n + 1)⟯ N)
    (p : (𝓡∂ (n + 1)).boundary M) : (bndEquiv Φ p).1 = Φ p.1 := rfl

@[simp] theorem bndEquiv_symm_apply_coe (Φ : M ≃ₘ⟮𝓡∂ (n + 1), 𝓡∂ (n + 1)⟯ N)
    (q : (𝓡∂ (n + 1)).boundary N) : ((bndEquiv Φ).symm q).1 = Φ.symm q.1 := rfl

/-- The inverse of the boundary bijection is the boundary bijection of the inverse diffeomorphism.
-/
theorem bndEquiv_symm_eq (Φ : M ≃ₘ⟮𝓡∂ (n + 1), 𝓡∂ (n + 1)⟯ N) :
    (bndEquiv Φ).symm = bndEquiv Φ.symm :=
  Equiv.ext fun _ => rfl

/-! ## Smoothness of the restriction -/

/-- **The restriction of a diffeomorphism to the boundary is smooth.**

The proof is the chart computation described in the module docstring.  For `p : ∂M` we test
smoothness at `p` in the source set `s = (boundaryChartAt p).source`.  By `contMDiffWithinAt_iff'`
we have to show that

`w ↦ extChartAt (𝓡 n) (Φ p) (Φ ((extChartAt (𝓡 n) p).symm w))`

is `C^∞` on the set `S` on which it is defined, i.e. on the set of `w` in the target of the
boundary chart at `p` such that `Φ ((boundaryChartAt p).symm w)` lies in the source of the
boundary chart at `Φ p`.  On `S` this function equals

`w ↦ tailCLM n (extChartAt (𝓡∂ (n+1)) (Φ p) (Φ ((extChartAt (𝓡∂ (n+1)) p).symm (consZeroCLM n w))))`,

which is a composition of the (within-`range`) smooth ambient chart transition of `Φ` with the
linear maps `consZeroCLM n` and `tailCLM n`. -/
theorem contMDiff_bndEquiv (Φ : M ≃ₘ⟮𝓡∂ (n + 1), 𝓡∂ (n + 1)⟯ N) :
    ContMDiff (𝓡 n) (𝓡 n) (∞ : WithTop ℕ∞) (bndEquiv Φ) := by
  intro p
  -- the source set used for `contMDiffWithinAt_iff'`
  let S : Set (EuclideanSpace ℝ (Fin n)) :=
    (extChartAt (𝓡 n) p).target ∩ (extChartAt (𝓡 n) p).symm ⁻¹'
      ((boundaryChartAt (n := n) (M := M) p).source ∩
        (⇑(bndEquiv Φ)) ⁻¹' (extChartAt (𝓡 n) (bndEquiv Φ p)).source)
  -- the source of the boundary chart at `p` is a neighbourhood of `p`
  have hs : (boundaryChartAt (n := n) (M := M) p).source ∈ 𝓝 p :=
    (boundaryChartAt (n := n) (M := M) p).open_source.mem_nhds
      (boundaryChartAt_mem_source (n := n) (M := M) p)
  -- the restriction is continuous
  have hcont : ContinuousWithinAt (⇑(bndEquiv Φ))
      (boundaryChartAt (n := n) (M := M) p).source p := by
    refine Continuous.continuousWithinAt ?_
    exact Continuous.subtype_mk (Φ.continuous.comp continuous_subtype_val)
      (fun q => bnd_mapsTo Φ q.2)
  -- smoothness of the ambient chart transition of `Φ` within the half-space
  have hG : ContDiffWithinAt ℝ (∞ : WithTop ℕ∞)
      (fun z : EuclideanSpace ℝ (Fin (n + 1)) => extChartAt (𝓡∂ (n + 1)) (Φ p.1)
        (Φ ((extChartAt (𝓡∂ (n + 1)) p.1).symm z)))
      (range (𝓡∂ (n + 1))) (extChartAt (𝓡∂ (n + 1)) p.1 p.1) := by
    have h := (contMDiffAt_iff (I := 𝓡∂ (n + 1)) (I' := 𝓡∂ (n + 1))
      (f := ⇑Φ) (x := p.1)).mp (Φ.contMDiffAt (x := p.1))
    simpa only [Function.comp_def] using h.2
  -- inserting a zero first coordinate recovers the centre of the ambient chart at `p`
  have hpoint : consZeroCLM n (boundaryChartAt (n := n) (M := M) p p)
      = extChartAt (𝓡∂ (n + 1)) p.1 p.1 := by
    rw [boundaryChartAt_apply (n := n) (M := M) p p
      (boundaryChartAt_mem_source (n := n) (M := M) p)]
    exact consZeroCLM_tailCLM n _
      (mem_hyperplane_iff.mp (extChartAt_mem_hyperplane (n := n) (M := M)
        (mem_extChartAt_source (I := 𝓡∂ (n + 1)) p.1) p.2))
  have hG' : ContDiffWithinAt ℝ (∞ : WithTop ℕ∞)
      (fun z : EuclideanSpace ℝ (Fin (n + 1)) => extChartAt (𝓡∂ (n + 1)) (Φ p.1)
        (Φ ((extChartAt (𝓡∂ (n + 1)) p.1).symm z)))
      (range (𝓡∂ (n + 1))) (consZeroCLM n (boundaryChartAt (n := n) (M := M) p p)) := by
    rw [hpoint]
    exact hG
  -- `consZeroCLM` maps `S` into the half-space
  have hmaps : MapsTo (consZeroCLM n) S (range (𝓡∂ (n + 1))) := by
    intro w hw
    have h1 : consZeroCLM n w ∈ (extChartAt (𝓡∂ (n + 1)) p.1).target := by
      have h := hw.1
      rw [extChartAt_bnd_target, boundaryChartAt_target] at h
      exact h
    exact extChartAt_target_subset_range (I := 𝓡∂ (n + 1)) p.1 h1
  -- hence the composite is smooth
  have hcomp : ContDiffWithinAt ℝ (∞ : WithTop ℕ∞)
      ((fun z : EuclideanSpace ℝ (Fin (n + 1)) => extChartAt (𝓡∂ (n + 1)) (Φ p.1)
        (Φ ((extChartAt (𝓡∂ (n + 1)) p.1).symm z))) ∘ (consZeroCLM n))
      S (boundaryChartAt (n := n) (M := M) p p) :=
    hG'.comp _ ((consZeroCLM n).contDiff.contDiffWithinAt) hmaps
  have htail : ContDiffWithinAt ℝ (∞ : WithTop ℕ∞)
      (fun w : EuclideanSpace ℝ (Fin n) => tailCLM n
        (extChartAt (𝓡∂ (n + 1)) (Φ p.1)
          (Φ ((extChartAt (𝓡∂ (n + 1)) p.1).symm (consZeroCLM n w)))))
      S (boundaryChartAt (n := n) (M := M) p p) := by
    have := (tailCLM n).contDiff.contDiffWithinAt.comp _ hcomp (fun _ _ => mem_univ _)
    simpa only [Function.comp_def] using this
  -- the centre of the chart at `p` lies in `S`
  have hS_mem : extChartAt (𝓡 n) p p ∈ S := by
    refine ⟨PartialEquiv.map_source _ (mem_extChartAt_source (I := 𝓡 n) p), ?_⟩
    rw [Set.mem_preimage, PartialEquiv.left_inv _ (mem_extChartAt_source (I := 𝓡 n) p)]
    refine ⟨boundaryChartAt_mem_source (n := n) (M := M) p, ?_⟩
    rw [Set.mem_preimage, extChartAt_bnd_source (n := n) (M := N) (p := bndEquiv Φ p)]
    exact boundaryChartAt_mem_source (n := n) (M := N) (bndEquiv Φ p)
  -- on `S` the chart composite is the explicit formula
  have heq : ∀ w ∈ S,
      (⇑(extChartAt (𝓡 n) (bndEquiv Φ p)) ∘ (bndEquiv Φ) ∘
          ⇑(extChartAt (𝓡 n) p).symm) w
        = tailCLM n (extChartAt (𝓡∂ (n + 1)) (Φ p.1)
            (Φ ((extChartAt (𝓡∂ (n + 1)) p.1).symm (consZeroCLM n w)))) := by
    intro w hw
    have hwt : w ∈ (boundaryChartAt (n := n) (M := M) p).target := by
      have h := hw.1
      rwa [extChartAt_bnd_target] at h
    have hsrc : (bndEquiv Φ) ((boundaryChartAt (n := n) (M := M) p).symm w)
        ∈ (boundaryChartAt (n := n) (M := N) (bndEquiv Φ p)).source := by
      have h := hw.2.2
      rw [extChartAt_bnd_symm, extChartAt_bnd_source] at h
      exact h
    simp only [Function.comp_apply]
    rw [extChartAt_bnd_apply, extChartAt_bnd_symm]
    rw [boundaryChartAt_apply (n := n) (M := N) (bndEquiv Φ p) _ hsrc]
    rw [bndEquiv_apply_coe, bndEquiv_apply_coe]
    rw [boundaryChartAt_symm (n := n) (M := M) p w hwt]
  -- assemble
  have hcd : ContDiffWithinAt ℝ (∞ : WithTop ℕ∞)
      (⇑(extChartAt (𝓡 n) (bndEquiv Φ p)) ∘ (bndEquiv Φ) ∘
        ⇑(extChartAt (𝓡 n) p).symm) S (extChartAt (𝓡 n) p p) :=
    htail.congr heq (heq _ hS_mem)
  exact ((contMDiffWithinAt_iff' (I := 𝓡 n) (I' := 𝓡 n) (f := ⇑(bndEquiv Φ))
    (s := (boundaryChartAt (n := n) (M := M) p).source) (x := p)).mpr
      ⟨hcont, hcd⟩).contMDiffAt hs

/-- The inverse of the restriction of `Φ` is smooth. -/
theorem contMDiff_bndEquiv_symm (Φ : M ≃ₘ⟮𝓡∂ (n + 1), 𝓡∂ (n + 1)⟯ N) :
    ContMDiff (𝓡 n) (𝓡 n) (∞ : WithTop ℕ∞) (bndEquiv Φ).symm := by
  rw [bndEquiv_symm_eq]
  exact contMDiff_bndEquiv Φ.symm

end

/-! ## The main statement -/

/-- **A diffeomorphism of manifolds with boundary restricts to a diffeomorphism of the
boundaries.** -/
theorem bnd_diffeomorph (n : ℕ) {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace (n + 1)) M]
    [IsManifold (modelWithCornersEuclideanHalfSpace (n + 1)) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    {N : Type*} [TopologicalSpace N] [ChartedSpace (EuclideanHalfSpace (n + 1)) N]
    [IsManifold (modelWithCornersEuclideanHalfSpace (n + 1)) ((⊤ : ℕ∞) : WithTop ℕ∞) N]
    (Φ : Diffeomorph (modelWithCornersEuclideanHalfSpace (n + 1))
      (modelWithCornersEuclideanHalfSpace (n + 1)) M N ((⊤ : ℕ∞) : WithTop ℕ∞)) :
    Nonempty (Diffeomorph (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
      ((modelWithCornersEuclideanHalfSpace (n + 1)).boundary M)
      ((modelWithCornersEuclideanHalfSpace (n + 1)).boundary N) ((⊤ : ℕ∞) : WithTop ℕ∞)) :=
  ⟨{ toEquiv := bndEquiv Φ
     contMDiff_toFun := contMDiff_bndEquiv Φ
     contMDiff_invFun := contMDiff_bndEquiv_symm Φ }⟩

end Work.Surgery
