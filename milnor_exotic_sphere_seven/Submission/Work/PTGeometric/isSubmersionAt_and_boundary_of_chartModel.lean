import Mathlib
import Submission.Work.Surgery.BoundaryInstances
import Submission.Work.Surgery.Boundary
import Submission.Work.PTGeometric.isSubmersionAt_of_boundary_linearization
import Submission.Work.PTGeometric.exists_chart_extend_of_openPartialHomeomorph_range

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# `IsSubmersionAt` at a boundary point, and on the boundary

Mathlib's `Manifold.IsSubmersionAt` is the local-normal-form notion; a surjective derivative alone is
not enough at a boundary point, and a boundary point behaves differently from an interior one
(see `Work.PTGeometric.isSubmersionAt_of_boundary_linearization` for the interior-free sufficient
condition proved here).

This file proves `Work.PTGeometric.isSubmersionAt_and_boundary_of_chartModel`: if `f : M → ℝ^k` is
written near a boundary point `x` of an `(n+1)`-manifold with boundary as `g ∘ (e.extend I)` for a
chart `e` of the maximal atlas, where `g` is `C^∞` near `(e.extend I) x`, has surjective derivative
there, and whose derivative kills a vector with nonvanishing zeroth coordinate, then

* `f` is a submersion at `x` (the boundary case of the normal-form theorem), **and**
* the restriction `f|∂M` is a submersion at `x` (seen as a point of the boundaryless `n`-manifold
  `∂M`).

The second statement is the more subtle one: the normal form for `f` in a suitable chart `e'` makes
`f` *linear* in the chart coordinates of `e'`; restricted to the boundary — where the zeroth
coordinate vanishes — this linear map becomes `L ∘ consZeroCLM`, and the hypothesis on the kernel
vector makes *that* surjective, which is exactly the linear-algebra content of the claim.
-/

namespace Work.PTGeometric

open scoped Manifold ContDiff Topology
open Function Set Topology Manifold Filter

noncomputable section

set_option maxHeartbeats 1000000
set_option linter.style.haveILetI false

/-- **The linearizing chart at a boundary point, with the normal form.**

Under the hypotheses of `isSubmersionAt_of_boundary_linearization` (in particular `x` is an
arbitrary point of `e.source`, no interiority and no vanishing of `f x` is needed), the map `f`
agrees, on the source of a chart `e'` of the maximal atlas through `x`, with the linear map
`fderiv ℝ g ((e.extend I) x)` read in the chart `e'`:

`f y = (fderiv ℝ g ((e.extend I) x)) ((e'.extend I) y)` for `y ∈ e'.source`.

This is proved exactly as in `Work.PTGeometric.isSubmersionAt_of_boundary_linearization`
(straightening `g` near `c = (e.extend I) x` by `T w = w + σ (g w - L w)`, so that `L ∘ T = g` and
`T` preserves the half space, and conjugating the chart `e` by `T`), only with the normal form made
explicit.  The first conjunct is the `IsSubmersionAt` conclusion of that reference. -/
theorem exists_chart_boundary_linearization {n k : ℕ} {M : Type} [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace (n + 1)) M]
    [IsManifold (modelWithCornersEuclideanHalfSpace (n + 1)) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    {e : OpenPartialHomeomorph M (EuclideanHalfSpace (n + 1))}
    (he : e ∈ IsManifold.maximalAtlas (modelWithCornersEuclideanHalfSpace (n + 1))
      ((⊤ : ℕ∞) : WithTop ℕ∞) M)
    {x : M} (hxe : x ∈ e.source)
    {f : M → EuclideanSpace ℝ (Fin k)}
    {g : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin k)}
    (hg : ∃ U ∈ nhds ((e.extend (modelWithCornersEuclideanHalfSpace (n + 1))) x),
      ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g U)
    (hagree : Filter.EventuallyEq (nhds x) f
      (fun y => g ((e.extend (modelWithCornersEuclideanHalfSpace (n + 1))) y)))
    (hsurj : Function.Surjective (fderiv ℝ g
      ((e.extend (modelWithCornersEuclideanHalfSpace (n + 1))) x)))
    (hnorm : ∃ v : EuclideanSpace ℝ (Fin (n + 1)),
      fderiv ℝ g ((e.extend (modelWithCornersEuclideanHalfSpace (n + 1))) x) v = 0 ∧ v 0 ≠ 0) :
    Manifold.IsSubmersionAt (modelWithCornersEuclideanHalfSpace (n + 1))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin k))) ((⊤ : ℕ∞) : WithTop ℕ∞) f x ∧
    ∃ e' : OpenPartialHomeomorph M (EuclideanHalfSpace (n + 1)),
      e' ∈ IsManifold.maximalAtlas (modelWithCornersEuclideanHalfSpace (n + 1))
        ((⊤ : ℕ∞) : WithTop ℕ∞) M ∧ x ∈ e'.source ∧
      ∀ y ∈ e'.source, f y =
        fderiv ℝ g ((e.extend (modelWithCornersEuclideanHalfSpace (n + 1))) x)
          ((e'.extend (modelWithCornersEuclideanHalfSpace (n + 1))) y) := by
  classical
  set c : EuclideanSpace ℝ (Fin (n + 1)) := (e.extend (𝓡∂ (n + 1))) x with hc_def
  set L : EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ] EuclideanSpace ℝ (Fin k) := fderiv ℝ g c with hL_def
  have hsurjL : Function.Surjective L := by rw [hL_def, hc_def]; exact hsurj
  obtain ⟨v, hv, hv0⟩ := hnorm
  have hLv : L v = 0 := by rw [hL_def, hc_def]; exact hv
  obtain ⟨σ, hσ, hσ0⟩ := exists_rightInverse_coord_eq_zero hLv hv0 hsurjL
  -- the open neighbourhood on which `g` is smooth
  obtain ⟨U, hUmem, hgU⟩ := hg
  obtain ⟨U', hU'sub, hU'open, hcU'⟩ := mem_nhds_iff.mp hUmem
  -- the straightening local diffeomorphism of the model space
  obtain ⟨T, hcT, hTχ, hTlin, hTsm, hTsm_inv⟩ :=
    exists_localDiffeomorph_eq_linear_of_coord_preserving_smooth (g := g) (L := L) (c := c)
      (U := U') (χ := coordFun (n + 1)) (σ := σ) hU'open hcU' (hgU.mono hU'sub)
      (by rw [hL_def]) hσ hσ0
  -- `T` preserves the half space, both ways
  have hrange : Set.range (𝓡∂ (n + 1)) = {w : EuclideanSpace ℝ (Fin (n + 1)) | 0 ≤ w 0} := by
    rw [range_modelWithCornersEuclideanHalfSpace]
  have hTmap : ∀ ⦃w : EuclideanSpace ℝ (Fin (n + 1))⦄, w ∈ T.source →
      w ∈ Set.range (𝓡∂ (n + 1)) → T w ∈ Set.range (𝓡∂ (n + 1)) := by
    intro w hw hwr
    rw [hrange] at hwr ⊢
    simp only [Set.mem_ofPred_eq] at hwr ⊢
    rw [← coordFun_apply, hTχ w hw, coordFun_apply]
    exact hwr
  have hTsmap : ∀ ⦃w : EuclideanSpace ℝ (Fin (n + 1))⦄, w ∈ T.target →
      w ∈ Set.range (𝓡∂ (n + 1)) → T.symm w ∈ Set.range (𝓡∂ (n + 1)) := by
    intro w hw hwr
    rw [hrange] at hwr ⊢
    simp only [Set.mem_ofPred_eq] at hwr ⊢
    have h1 : T.symm w ∈ T.source := T.map_target hw
    have h2 : coordFun (n + 1) (T (T.symm w)) = coordFun (n + 1) w :=
      congrArg (coordFun (n + 1)) (T.right_inv hw)
    rw [hTχ (T.symm w) h1] at h2
    rw [← coordFun_apply, h2, coordFun_apply]
    exact hwr
  -- the conjugated chart
  obtain ⟨e', he'mem, hxe', he'conj⟩ :=
    exists_chart_extend_of_openPartialHomeomorph_range_smooth (𝓡∂ (n + 1)) he hxe hTsm hTsm_inv
      hTmap hTsmap hcT
  -- cut down to the set where `f` agrees with `g ∘ (e.extend _)`
  obtain ⟨S₁, hS₁sub, hS₁open, hxS₁⟩ := mem_nhds_iff.mp hagree
  set S : Set M := e'.source ∩ S₁ with hS_def
  have hSopen : IsOpen S := e'.open_source.inter hS₁open
  set e'' : OpenPartialHomeomorph M (EuclideanHalfSpace (n + 1)) := e'.restr S with he''_def
  have he''_src : e''.source = e'.source ∩ S₁ := by
    rw [he''_def, OpenPartialHomeomorph.restr_source, hSopen.interior_eq, hS_def]
    exact Set.inter_eq_right.mpr Set.inter_subset_left
  have hx'' : x ∈ e''.source := by
    rw [he''_src]; exact ⟨hxe', hxS₁⟩
  have he''_ext : ∀ y : M, (e''.extend (𝓡∂ (n + 1))) y = (e'.extend (𝓡∂ (n + 1))) y := by
    intro y
    rw [OpenPartialHomeomorph.extend_coe, OpenPartialHomeomorph.extend_coe,
      OpenPartialHomeomorph.restr_apply]
  have he''_mem : e'' ∈ IsManifold.maximalAtlas (𝓡∂ (n + 1)) ((⊤ : ℕ∞) : WithTop ℕ∞) M := by
    rw [he''_def]
    exact restr_mem_maximalAtlas (contDiffGroupoid ((⊤ : ℕ∞) : WithTop ℕ∞) (𝓡∂ (n + 1)))
      he'mem hSopen
  -- the linear equivalence `ℝ^{n+1} ≃L (ℝ^k × ker L)` with first component `L`
  have hσ' : ∀ y : EuclideanSpace ℝ (Fin k), L (σ y) = y := hσ
  let φ : EuclideanSpace ℝ (Fin (n + 1)) →ₗ[ℝ]
      (EuclideanSpace ℝ (Fin k) × L.ker) :=
    { toFun := fun w => (L w, ⟨w - σ (L w), by
        show L (w - σ (L w)) = 0
        rw [map_sub, hσ', sub_self]⟩)
      map_add' := fun a b => by
        refine Prod.ext ?_ ?_
        · show L (a + b) = L a + L b
          rw [map_add]
        · refine Subtype.ext ?_
          show (a + b) - σ (L (a + b)) = (a - σ (L a)) + (b - σ (L b))
          rw [map_add, map_add]
          abel
      map_smul' := fun r a => by
        refine Prod.ext ?_ ?_
        · show L (r • a) = r • L a
          rw [map_smul]
        · refine Subtype.ext ?_
          show (r • a) - σ (L (r • a)) = r • (a - σ (L a))
          rw [map_smul, map_smul, smul_sub] }
  have hbij : Function.Bijective φ := by
    constructor
    · intro a b hab
      have h1 : L a = L b := congrArg (fun p => p.1) hab
      have h2 : (a - σ (L a)) = (b - σ (L b)) :=
        congrArg (fun p => (p.2 : EuclideanSpace ℝ (Fin (n + 1)))) hab
      calc a = σ (L a) + (a - σ (L a)) := by abel
        _ = σ (L b) + (b - σ (L b)) := by rw [h2, h1]
        _ = b := by abel
    · intro p
      obtain ⟨y, w⟩ := p
      refine ⟨σ y + w, ?_⟩
      refine Prod.ext ?_ ?_
      · show L (σ y + w) = y
        rw [map_add, hσ']
        have hw : L (w : EuclideanSpace ℝ (Fin (n + 1))) = 0 := w.2
        rw [hw, add_zero]
      · refine Subtype.ext ?_
        show ((σ y + w : EuclideanSpace ℝ (Fin (n + 1)))
            - σ (L (σ y + (w : EuclideanSpace ℝ (Fin (n + 1))))))
          = (w : EuclideanSpace ℝ (Fin (n + 1)))
        rw [map_add, hσ']
        have hw : L (w : EuclideanSpace ℝ (Fin (n + 1))) = 0 := w.2
        rw [hw, add_zero, add_sub_cancel_left]
  let equ : EuclideanSpace ℝ (Fin (n + 1)) ≃L[ℝ] (EuclideanSpace ℝ (Fin k) × L.ker) :=
    (LinearEquiv.ofBijective φ hbij).toContinuousLinearEquiv
  -- the normal form
  have hkey : ∀ w ∈ (e''.extend (𝓡∂ (n + 1))).target,
      f ((e''.extend (𝓡∂ (n + 1))).symm w) = L w := by
    intro w hw
    set y : M := (e''.extend (𝓡∂ (n + 1))).symm w with hy_def
    have hy_src : y ∈ e''.source := by
      rw [← OpenPartialHomeomorph.extend_source (f := e'') (I := 𝓡∂ (n + 1))]
      exact (e''.extend (𝓡∂ (n + 1))).map_target hw
    have hy' : y ∈ e'.source := by rw [he''_src] at hy_src; exact hy_src.1
    have hyS₁ : y ∈ S₁ := by rw [he''_src] at hy_src; exact hy_src.2
    have hwy : (e''.extend (𝓡∂ (n + 1))) y = w := (e''.extend (𝓡∂ (n + 1))).right_inv hw
    have hconj' : (e.extend (𝓡∂ (n + 1))) y ∈ T.source ∧
        (e''.extend (𝓡∂ (n + 1))) y = T ((e.extend (𝓡∂ (n + 1))) y) := by
      obtain ⟨h1, h2⟩ := he'conj y hy'
      exact ⟨h1, by rw [he''_ext y]; exact h2⟩
    calc f y = g ((e.extend (𝓡∂ (n + 1))) y) := hS₁sub hyS₁
      _ = L (T ((e.extend (𝓡∂ (n + 1))) y)) := (hTlin _ hconj'.1).symm
      _ = L ((e''.extend (𝓡∂ (n + 1))) y) := by rw [hconj'.2]
      _ = L w := by rw [hwy]
  refine ⟨?_, e'', he''_mem, hx'', ?_⟩
  · refine Manifold.IsSubmersionAt.mk_of_charts (F := L.ker) equ e'' (OpenPartialHomeomorph.refl _)
      hx'' (mem_univ _) he''_mem
      (StructureGroupoid.id_mem_maximalAtlas
        (G := contDiffGroupoid ((⊤ : ℕ∞) : WithTop ℕ∞) (𝓡 k)))
      (fun _ _ => mem_univ _) ?_
    intro w hw
    exact hkey w hw
  · intro y hy
    have hy_tgt : (e''.extend (𝓡∂ (n + 1))) y ∈ (e''.extend (𝓡∂ (n + 1))).target :=
      PartialEquiv.map_source _ (by rw [OpenPartialHomeomorph.extend_source]; exact hy)
    have h1 := hkey ((e''.extend (𝓡∂ (n + 1))) y) hy_tgt
    rwa [PartialEquiv.left_inv _ (by rw [OpenPartialHomeomorph.extend_source]; exact hy)] at h1




/-! ### The boundary chart of a chart of the maximal atlas -/

/-- Membership in `contDiffGroupoid ∞ (𝓡 n)` of a local homeomorphism of the model space `ℝⁿ` is
just `C^∞`-ness of the map and of its inverse (on their respective sources). -/
theorem mem_contDiffGroupoid_self {n : ℕ}
    {e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin n))} :
    e ∈ contDiffGroupoid ((⊤ : ℕ∞) : WithTop ℕ∞) (𝓡 n) ↔
      ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (⇑e) e.source ∧
      ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (⇑e.symm) e.target := by
  rw [contDiffGroupoid, mem_groupoid_of_pregroupoid, contDiffPregroupoid]
  simp only [modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm, Set.preimage_id_eq,
    Set.range_id, Set.inter_univ, Function.id_comp, Function.comp_id, id_eq]

/-- The transition `β ∘ bc.symm` from a preferred boundary chart `bc = boundaryChartAt q` to the
boundary chart of a maximal-atlas chart `φ` is smooth (as a map `ℝⁿ → ℝⁿ`). -/
theorem contDiffOn_bnd_target {n : ℕ} {M : Type} [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace (n + 1)) M]
    [IsManifold (modelWithCornersEuclideanHalfSpace (n + 1)) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    {φ : OpenPartialHomeomorph M (EuclideanHalfSpace (n + 1))}
    (hφ : φ ∈ IsManifold.maximalAtlas (modelWithCornersEuclideanHalfSpace (n + 1))
      ((⊤ : ℕ∞) : WithTop ℕ∞) M)
    (q : (modelWithCornersEuclideanHalfSpace (n + 1)).boundary M)
    {S : Set (EuclideanSpace ℝ (Fin n))}
    (hS : ∀ w ∈ S, Work.Surgery.consZeroCLM n w ∈ (extChartAt (𝓡∂ (n + 1)) q.1).target ∧
      (extChartAt (𝓡∂ (n + 1)) q.1).symm (Work.Surgery.consZeroCLM n w) ∈ φ.source) :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun w : EuclideanSpace ℝ (Fin n) =>
      Work.Surgery.tailCLM n ((φ.extend (𝓡∂ (n + 1)))
        ((extChartAt (𝓡∂ (n + 1)) q.1).symm (Work.Surgery.consZeroCLM n w)))) S := by
  have h1 : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) (𝓡∂ (n + 1))
      ((⊤ : ℕ∞) : WithTop ℕ∞) (⇑(extChartAt (𝓡∂ (n + 1)) q.1).symm)
      (extChartAt (𝓡∂ (n + 1)) q.1).target :=
    contMDiffOn_extChartAt_symm (I := 𝓡∂ (n + 1)) q.1
  have h2 : ContMDiffOn (𝓡∂ (n + 1)) (𝓡∂ (n + 1)) ((⊤ : ℕ∞) : WithTop ℕ∞) (⇑φ) φ.source :=
    contMDiffOn_of_mem_maximalAtlas hφ
  have h3 : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) (𝓡∂ (n + 1))
      ((⊤ : ℕ∞) : WithTop ℕ∞) (⇑φ ∘ ⇑(extChartAt (𝓡∂ (n + 1)) q.1).symm)
      ((extChartAt (𝓡∂ (n + 1)) q.1).target ∩
        (extChartAt (𝓡∂ (n + 1)) q.1).symm ⁻¹' φ.source) := h2.comp' h1
  have h4 : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1)))
      𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (⇑(𝓡∂ (n + 1)) ∘ (⇑φ ∘ ⇑(extChartAt (𝓡∂ (n + 1)) q.1).symm))
      ((extChartAt (𝓡∂ (n + 1)) q.1).target ∩
        (extChartAt (𝓡∂ (n + 1)) q.1).symm ⁻¹' φ.source) :=
    (ModelWithCorners.contMDiff (𝓡∂ (n + 1))).contMDiffOn.comp (t := Set.univ) h3
      (fun _ _ => Set.mem_univ _)
  have h5 : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (⇑(𝓡∂ (n + 1)) ∘ (⇑φ ∘ ⇑(extChartAt (𝓡∂ (n + 1)) q.1).symm))
      ((extChartAt (𝓡∂ (n + 1)) q.1).target ∩
        (extChartAt (𝓡∂ (n + 1)) q.1).symm ⁻¹' φ.source) :=
    contMDiffOn_iff_contDiffOn.mp h4
  have hmaps : Set.MapsTo (Work.Surgery.consZeroCLM n) S
      ((extChartAt (𝓡∂ (n + 1)) q.1).target ∩
        (extChartAt (𝓡∂ (n + 1)) q.1).symm ⁻¹' φ.source) := by
    intro w hw
    exact ⟨(hS w hw).1, by simpa only [Set.mem_preimage] using (hS w hw).2⟩
  have h6 : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      ((⇑(𝓡∂ (n + 1)) ∘ (⇑φ ∘ ⇑(extChartAt (𝓡∂ (n + 1)) q.1).symm)) ∘
        (Work.Surgery.consZeroCLM n)) S :=
    h5.comp ((Work.Surgery.consZeroCLM n).contDiff.contDiffOn) hmaps
  have h7 : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun w : EuclideanSpace ℝ (Fin n) =>
      Work.Surgery.tailCLM n ((⇑(𝓡∂ (n + 1)) ∘ (⇑φ ∘ ⇑(extChartAt (𝓡∂ (n + 1)) q.1).symm))
        (Work.Surgery.consZeroCLM n w))) S :=
    (Work.Surgery.tailCLM n).contDiff.contDiffOn.comp h6 (fun _ _ => Set.mem_univ _)
  exact h7.congr (fun w _ => by
    simp only [OpenPartialHomeomorph.extend_coe, Function.comp_apply])

/-- The transition `bc ∘ β.symm` from the boundary chart of a maximal-atlas chart `φ` to a preferred
boundary chart `bc = boundaryChartAt q` is smooth (as a map `ℝⁿ → ℝⁿ`). -/
theorem contDiffOn_bnd_source {n : ℕ} {M : Type} [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace (n + 1)) M]
    [IsManifold (modelWithCornersEuclideanHalfSpace (n + 1)) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    {φ : OpenPartialHomeomorph M (EuclideanHalfSpace (n + 1))}
    (hφ : φ ∈ IsManifold.maximalAtlas (modelWithCornersEuclideanHalfSpace (n + 1))
      ((⊤ : ℕ∞) : WithTop ℕ∞) M)
    (q : (modelWithCornersEuclideanHalfSpace (n + 1)).boundary M)
    {S : Set (EuclideanSpace ℝ (Fin n))}
    (hS : ∀ w ∈ S, (𝓡∂ (n + 1)).symm (Work.Surgery.consZeroCLM n w) ∈ φ.target ∧
      φ.symm ((𝓡∂ (n + 1)).symm (Work.Surgery.consZeroCLM n w)) ∈
        (extChartAt (𝓡∂ (n + 1)) q.1).source) :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun w : EuclideanSpace ℝ (Fin n) =>
      Work.Surgery.tailCLM n ((extChartAt (𝓡∂ (n + 1)) q.1)
        (φ.symm ((𝓡∂ (n + 1)).symm (Work.Surgery.consZeroCLM n w))))) S := by
  have h1 : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) (𝓡∂ (n + 1))
      ((⊤ : ℕ∞) : WithTop ℕ∞) (⇑(𝓡∂ (n + 1)).symm) (Set.range (𝓡∂ (n + 1))) :=
    ModelWithCorners.contMDiffOn_symm (𝓡∂ (n + 1))
  have h2 : ContMDiffOn (𝓡∂ (n + 1)) (𝓡∂ (n + 1)) ((⊤ : ℕ∞) : WithTop ℕ∞) (⇑φ.symm) φ.target :=
    contMDiffOn_symm_of_mem_maximalAtlas hφ
  have h3 : ContMDiffOn (𝓡∂ (n + 1)) 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1)))
      ((⊤ : ℕ∞) : WithTop ℕ∞) (⇑(extChartAt (𝓡∂ (n + 1)) q.1))
      (extChartAt (𝓡∂ (n + 1)) q.1).source := by
    change ContMDiffOn (𝓡∂ (n + 1)) 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1)))
      ((⊤ : ℕ∞) : WithTop ℕ∞)
      (⇑((chartAt (EuclideanHalfSpace (n + 1)) q.1).extend (𝓡∂ (n + 1))))
      ((chartAt (EuclideanHalfSpace (n + 1)) q.1).extend (𝓡∂ (n + 1))).source
    rw [OpenPartialHomeomorph.extend_source]
    exact contMDiffOn_extChartAt (I := 𝓡∂ (n + 1)) (x := q.1)
  have h4 : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1)))
      𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (⇑(extChartAt (𝓡∂ (n + 1)) q.1) ∘ (⇑φ.symm ∘ ⇑(𝓡∂ (n + 1)).symm))
      ((Set.range (𝓡∂ (n + 1)) ∩ (𝓡∂ (n + 1)).symm ⁻¹' φ.target) ∩
        (⇑φ.symm ∘ ⇑(𝓡∂ (n + 1)).symm) ⁻¹' (extChartAt (𝓡∂ (n + 1)) q.1).source) :=
    h3.comp' (h2.comp' h1)
  have h5 : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (⇑(extChartAt (𝓡∂ (n + 1)) q.1) ∘ (⇑φ.symm ∘ ⇑(𝓡∂ (n + 1)).symm))
      ((Set.range (𝓡∂ (n + 1)) ∩ (𝓡∂ (n + 1)).symm ⁻¹' φ.target) ∩
        (⇑φ.symm ∘ ⇑(𝓡∂ (n + 1)).symm) ⁻¹' (extChartAt (𝓡∂ (n + 1)) q.1).source) :=
    contMDiffOn_iff_contDiffOn.mp h4
  have hmaps : Set.MapsTo (Work.Surgery.consZeroCLM n) S
      ((Set.range (𝓡∂ (n + 1)) ∩ (𝓡∂ (n + 1)).symm ⁻¹' φ.target) ∩
        (⇑φ.symm ∘ ⇑(𝓡∂ (n + 1)).symm) ⁻¹' (extChartAt (𝓡∂ (n + 1)) q.1).source) := by
    intro w hw
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [range_modelWithCornersEuclideanHalfSpace]
      exact Work.Surgery.consZeroCLM_mem_halfSpace n w
    · simpa only [Set.mem_preimage] using (hS w hw).1
    · simpa only [Set.mem_preimage, Function.comp_apply] using (hS w hw).2
  have h6 : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      ((⇑(extChartAt (𝓡∂ (n + 1)) q.1) ∘ (⇑φ.symm ∘ ⇑(𝓡∂ (n + 1)).symm)) ∘
        (Work.Surgery.consZeroCLM n)) S :=
    h5.comp ((Work.Surgery.consZeroCLM n).contDiff.contDiffOn) hmaps
  exact ((Work.Surgery.tailCLM n).contDiff.contDiffOn.comp h6 (fun _ _ => Set.mem_univ _)).congr
    (fun w _ => rfl)

/-- **The boundary chart of a chart of the maximal atlas, as data.**  For a chart `φ` of the maximal
atlas of an `(n+1)`-manifold with boundary `M` and a boundary point `p₀`, the chart of `∂M` given by
restricting `φ` to the boundary and deleting the (vanishing) first coordinate is an open partial
homeomorphism of `∂M` onto `ℝⁿ`, with the source/target/forward/inverse formulas used in
`Work.Surgery.bnd_chart_exists` (which is the same construction for the preferred charts
`extChartAt (𝓡∂ (n+1)) p₀.1` in place of `φ`).  The base point `p₀` only enters as the junk value of
the (total) inverse function off its source. -/
theorem bndChart_self_data {n : ℕ} {M : Type} [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace (n + 1)) M]
    [IsManifold (modelWithCornersEuclideanHalfSpace (n + 1)) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    (φ : OpenPartialHomeomorph M (EuclideanHalfSpace (n + 1)))
    (hφ : φ ∈ IsManifold.maximalAtlas (modelWithCornersEuclideanHalfSpace (n + 1))
      ((⊤ : ℕ∞) : WithTop ℕ∞) M)
    (p₀ : (modelWithCornersEuclideanHalfSpace (n + 1)).boundary M) :
    ∃ β : OpenPartialHomeomorph ((modelWithCornersEuclideanHalfSpace (n + 1)).boundary M)
        (EuclideanSpace ℝ (Fin n)),
      β.source = {p | p.1 ∈ φ.source} ∧
      β.target = {w : EuclideanSpace ℝ (Fin n) | Work.Surgery.consZeroCLM n w ∈
        (φ.extend (modelWithCornersEuclideanHalfSpace (n + 1))).target} ∧
      (∀ p, β p = Work.Surgery.tailCLM n
        ((φ.extend (modelWithCornersEuclideanHalfSpace (n + 1))) p.1)) ∧
      (∀ w ∈ β.target, (β.symm w).1 =
        (φ.extend (modelWithCornersEuclideanHalfSpace (n + 1))).symm
          (Work.Surgery.consZeroCLM n w)) := by
  classical
  -- the inverse of `φ.extend I` on the hyperplane lands in the boundary
  have hbnd : ∀ w : EuclideanSpace ℝ (Fin n),
      Work.Surgery.consZeroCLM n w ∈ (φ.extend (𝓡∂ (n + 1))).target →
      (φ.extend (𝓡∂ (n + 1))).symm (Work.Surgery.consZeroCLM n w) ∈
        (modelWithCornersEuclideanHalfSpace (n + 1)).boundary M := by
    intro w hw
    refine (Work.ThomBordism.Transversality.Preimage.mem_boundary_iff_extend_apply_coord_eq_zero
      (m := n + 1) hφ ?_).mpr ?_
    · simpa only [OpenPartialHomeomorph.extend_source] using PartialEquiv.map_target _ hw
    · rw [PartialEquiv.right_inv _ hw]
      exact Work.Surgery.consZeroCLM_apply_zero n w
  let src : Set ((modelWithCornersEuclideanHalfSpace (n + 1)).boundary M) := {p | p.1 ∈ φ.source}
  let tgt : Set (EuclideanSpace ℝ (Fin n)) :=
    {w | Work.Surgery.consZeroCLM n w ∈ (φ.extend (𝓡∂ (n + 1))).target}
  let toF : ((modelWithCornersEuclideanHalfSpace (n + 1)).boundary M) →
      EuclideanSpace ℝ (Fin n) :=
    fun p => Work.Surgery.tailCLM n ((φ.extend (𝓡∂ (n + 1))) p.1)
  let invF : EuclideanSpace ℝ (Fin n) →
      ((modelWithCornersEuclideanHalfSpace (n + 1)).boundary M) :=
    fun w => if hw : Work.Surgery.consZeroCLM n w ∈ (φ.extend (𝓡∂ (n + 1))).target
      then ⟨(φ.extend (𝓡∂ (n + 1))).symm (Work.Surgery.consZeroCLM n w), hbnd w hw⟩
      else p₀
  have hinvF : ∀ (w : EuclideanSpace ℝ (Fin n))
      (hw : Work.Surgery.consZeroCLM n w ∈ (φ.extend (𝓡∂ (n + 1))).target),
      invF w = ⟨(φ.extend (𝓡∂ (n + 1))).symm (Work.Surgery.consZeroCLM n w), hbnd w hw⟩ := by
    intro w hw
    exact dif_pos hw
  have htoF : ∀ p : ((modelWithCornersEuclideanHalfSpace (n + 1)).boundary M),
      toF p = Work.Surgery.tailCLM n ((φ.extend (𝓡∂ (n + 1))) p.1) := fun p => rfl
  refine ⟨{ toFun := toF
            invFun := invF
            source := src
            target := tgt
            map_source' := ?_
            map_target' := ?_
            left_inv' := ?_
            right_inv' := ?_
            continuousOn_toFun := ?_
            continuousOn_invFun := ?_
            open_source := ?_
            open_target := ?_ }, ?_, ?_, ?_, ?_⟩
  · intro p hp
    have hp' : p.1 ∈ (φ.extend (𝓡∂ (n + 1))).source := by
      rw [OpenPartialHomeomorph.extend_source]; exact hp
    have h0 : ((φ.extend (𝓡∂ (n + 1))) p.1).ofLp 0 = 0 :=
      (Work.ThomBordism.Transversality.Preimage.mem_boundary_iff_extend_apply_coord_eq_zero
        (m := n + 1) hφ hp).mp p.2
    show Work.Surgery.consZeroCLM n (Work.Surgery.tailCLM n ((φ.extend (𝓡∂ (n + 1))) p.1))
      ∈ (φ.extend (𝓡∂ (n + 1))).target
    rw [Work.Surgery.consZeroCLM_tailCLM n _ h0]
    exact PartialEquiv.map_source _ hp'
  · intro w hw
    have hw' : Work.Surgery.consZeroCLM n w ∈ (φ.extend (𝓡∂ (n + 1))).target := hw
    rw [hinvF w hw']
    show (φ.extend (𝓡∂ (n + 1))).symm (Work.Surgery.consZeroCLM n w) ∈ φ.source
    simpa only [OpenPartialHomeomorph.extend_source] using
      PartialEquiv.map_target (φ.extend (𝓡∂ (n + 1))) hw'
  · intro p hp
    have hp' : p.1 ∈ (φ.extend (𝓡∂ (n + 1))).source := by
      rw [OpenPartialHomeomorph.extend_source]; exact hp
    have h0 : ((φ.extend (𝓡∂ (n + 1))) p.1).ofLp 0 = 0 :=
      (Work.ThomBordism.Transversality.Preimage.mem_boundary_iff_extend_apply_coord_eq_zero
        (m := n + 1) hφ hp).mp p.2
    have hmem : Work.Surgery.consZeroCLM n
        (Work.Surgery.tailCLM n ((φ.extend (𝓡∂ (n + 1))) p.1))
        ∈ (φ.extend (𝓡∂ (n + 1))).target := by
      rw [Work.Surgery.consZeroCLM_tailCLM n _ h0]
      exact PartialEquiv.map_source _ hp'
    have harg : Work.Surgery.consZeroCLM n (toF p) = (φ.extend (𝓡∂ (n + 1))) p.1 := by
      rw [htoF p, Work.Surgery.consZeroCLM_tailCLM n _ h0]
    rw [hinvF (toF p) hmem]
    apply Subtype.ext
    show (φ.extend (𝓡∂ (n + 1))).symm (Work.Surgery.consZeroCLM n (toF p)) = p.1
    rw [harg]
    exact PartialEquiv.left_inv _ hp'
  · intro w hw
    have hw' : Work.Surgery.consZeroCLM n w ∈ (φ.extend (𝓡∂ (n + 1))).target := hw
    rw [htoF, hinvF w hw']
    show (Work.Surgery.tailCLM n) ((φ.extend (𝓡∂ (n + 1)))
      ((φ.extend (𝓡∂ (n + 1))).symm (Work.Surgery.consZeroCLM n w))) = w
    rw [PartialEquiv.right_inv _ hw']
    exact Work.Surgery.tailCLM_consZeroCLM n w
  · rw [continuousOn_iff_continuous_domRestrict]
    exact (Work.Surgery.tailCLM n).continuous.comp
      ((OpenPartialHomeomorph.continuousOn_extend φ (I := 𝓡∂ (n + 1))).comp_continuous
        (continuous_subtype_val.comp continuous_subtype_val)
        (fun y => by rw [OpenPartialHomeomorph.extend_source]; exact y.2))
  · rw [continuousOn_iff_continuous_domRestrict]
    have hcont : Continuous (fun w : ↥tgt =>
        (φ.extend (𝓡∂ (n + 1))).symm (Work.Surgery.consZeroCLM n w.1)) :=
      (OpenPartialHomeomorph.continuousOn_extend_symm φ (I := 𝓡∂ (n + 1))).comp_continuous
        ((Work.Surgery.consZeroCLM n).continuous.comp continuous_subtype_val)
        (fun w => w.2)
    have hagree : tgt.domRestrict invF = fun w : ↥tgt =>
        ⟨(φ.extend (𝓡∂ (n + 1))).symm (Work.Surgery.consZeroCLM n w.1), hbnd w.1 w.2⟩ := by
      funext w
      rw [Set.domRestrict_apply]
      exact hinvF w.1 w.2
    rw [hagree]
    exact Continuous.subtype_mk hcont _
  · show IsOpen src
    exact φ.open_source.preimage continuous_subtype_val
  · show IsOpen tgt
    have hcont : Continuous (fun w : EuclideanSpace ℝ (Fin n) =>
        (𝓡∂ (n + 1)).symm (Work.Surgery.consZeroCLM n w)) :=
      (𝓡∂ (n + 1)).continuous_symm.comp (Work.Surgery.consZeroCLM n).continuous
    have hset : tgt = (fun w : EuclideanSpace ℝ (Fin n) =>
        (𝓡∂ (n + 1)).symm (Work.Surgery.consZeroCLM n w)) ⁻¹' φ.target := by
      ext w
      change (Work.Surgery.consZeroCLM n w ∈ (φ.extend (𝓡∂ (n + 1))).target) ↔
        ((𝓡∂ (n + 1)).symm (Work.Surgery.consZeroCLM n w)) ∈ φ.target
      rw [OpenPartialHomeomorph.extend_target]
      simp only [Set.mem_inter_iff, Set.mem_preimage]
      constructor
      · exact fun h => h.1
      · intro h
        refine ⟨h, ?_⟩
        rw [range_modelWithCornersEuclideanHalfSpace]
        exact Work.Surgery.consZeroCLM_mem_halfSpace n w
    rw [hset]
    exact φ.open_target.preimage hcont
  · rfl
  · rfl
  · intro p
    rfl
  · intro w hw
    show (invF w).1 = (φ.extend (𝓡∂ (n + 1))).symm (Work.Surgery.consZeroCLM n w)
    rw [hinvF w hw]

/-- **The boundary chart of a chart of the maximal atlas lies in the maximal atlas of `∂M`.** -/
theorem bndChart_self_maximalAtlas {n : ℕ} {M : Type} [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace (n + 1)) M]
    [IsManifold (modelWithCornersEuclideanHalfSpace (n + 1)) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    (φ : OpenPartialHomeomorph M (EuclideanHalfSpace (n + 1)))
    (hφ : φ ∈ IsManifold.maximalAtlas (modelWithCornersEuclideanHalfSpace (n + 1))
      ((⊤ : ℕ∞) : WithTop ℕ∞) M)
    (p₀ : (modelWithCornersEuclideanHalfSpace (n + 1)).boundary M) :
    ∃ β : OpenPartialHomeomorph ((modelWithCornersEuclideanHalfSpace (n + 1)).boundary M)
        (EuclideanSpace ℝ (Fin n)),
      β ∈ IsManifold.maximalAtlas (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
            ((⊤ : ℕ∞) : WithTop ℕ∞) ((modelWithCornersEuclideanHalfSpace (n + 1)).boundary M) ∧
      β.source = {p | p.1 ∈ φ.source} ∧
      β.target = {w : EuclideanSpace ℝ (Fin n) | Work.Surgery.consZeroCLM n w ∈
        (φ.extend (modelWithCornersEuclideanHalfSpace (n + 1))).target} ∧
      (∀ p, β p = Work.Surgery.tailCLM n
        ((φ.extend (modelWithCornersEuclideanHalfSpace (n + 1))) p.1)) ∧
      (∀ w ∈ β.target, (β.symm w).1 =
        (φ.extend (modelWithCornersEuclideanHalfSpace (n + 1))).symm
          (Work.Surgery.consZeroCLM n w)) := by
  obtain ⟨β, hsrc, htgt, happ, hsymm⟩ := bndChart_self_data φ hφ p₀
  refine ⟨β, ?_, hsrc, htgt, happ, hsymm⟩
  rw [IsManifold.mem_maximalAtlas_iff, mem_maximalAtlas_iff]
  intro e₀ he₀
  have he₀' : e₀ ∈ Set.range (Work.Surgery.boundaryChartAt (n := n) (M := M)) := by
    simpa only [Work.Surgery.boundaryChartedSpace_atlas] using he₀
  obtain ⟨q, rfl⟩ := he₀'
  -- the two transition maps
  have hI : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (⇑(β.symm ≫ₕ Work.Surgery.boundaryChartAt q))
      (β.symm ≫ₕ Work.Surgery.boundaryChartAt q).source := by
    refine (contDiffOn_bnd_source hφ q
      (S := (β.symm ≫ₕ Work.Surgery.boundaryChartAt q).source) ?_).congr ?_
    · intro w hw
      rw [OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source,
        Set.mem_inter_iff, Set.mem_preimage] at hw
      obtain ⟨hwt, hws⟩ := hw
      have h1 : Work.Surgery.consZeroCLM n w ∈ (φ.extend (𝓡∂ (n + 1))).target := by
        have h1' := hwt
        rw [htgt] at h1'
        exact h1'
      rw [OpenPartialHomeomorph.extend_target] at h1
      refine ⟨h1.1, ?_⟩
      rw [Work.Surgery.boundaryChartAt_source] at hws
      have h2 : (φ.extend (𝓡∂ (n + 1))).symm (Work.Surgery.consZeroCLM n w) ∈
          (extChartAt (𝓡∂ (n + 1)) q.1).source := by
        have h3 : (β.symm w).1 ∈ (extChartAt (𝓡∂ (n + 1)) q.1).source := hws
        rwa [hsymm w hwt] at h3
      simpa only [OpenPartialHomeomorph.extend_coe_symm, Function.comp_apply] using h2
    · intro w hw
      rw [OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source,
        Set.mem_inter_iff, Set.mem_preimage] at hw
      obtain ⟨hwt, hws⟩ := hw
      rw [OpenPartialHomeomorph.trans_apply]
      rw [Work.Surgery.boundaryChartAt_apply q (β.symm w) hws]
      rw [hsymm w hwt]
      simp only [OpenPartialHomeomorph.extend_coe_symm, Function.comp_apply]
  have hII : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (⇑((Work.Surgery.boundaryChartAt q).symm ≫ₕ β))
      ((Work.Surgery.boundaryChartAt q).symm ≫ₕ β).source := by
    refine (contDiffOn_bnd_target hφ q
      (S := ((Work.Surgery.boundaryChartAt q).symm ≫ₕ β).source) ?_).congr ?_
    · intro w hw
      rw [OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source,
        Set.mem_inter_iff, Set.mem_preimage] at hw
      obtain ⟨hwt, hws⟩ := hw
      have hsym := Work.Surgery.boundaryChartAt_symm q w hwt
      refine ⟨?_, ?_⟩
      · rwa [Work.Surgery.boundaryChartAt_target] at hwt
      · have h3 : ((Work.Surgery.boundaryChartAt q).symm w).1 ∈ φ.source := by
          have h3' := hws
          rw [hsrc] at h3'
          exact h3'
        rwa [hsym] at h3
    · intro w hw
      rw [OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source,
        Set.mem_inter_iff, Set.mem_preimage] at hw
      obtain ⟨hwt, hws⟩ := hw
      rw [OpenPartialHomeomorph.trans_apply, happ]
      rw [Work.Surgery.boundaryChartAt_symm q w hwt]
  rw [mem_contDiffGroupoid_self, mem_contDiffGroupoid_self]
  constructor
  · refine ⟨hI, ?_⟩
    rw [← OpenPartialHomeomorph.symm_source
        (e := β.symm ≫ₕ Work.Surgery.boundaryChartAt q),
      OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm, OpenPartialHomeomorph.symm_symm]
    exact hII
  · refine ⟨hII, ?_⟩
    rw [← OpenPartialHomeomorph.symm_source
        (e := (Work.Surgery.boundaryChartAt q).symm ≫ₕ β),
      OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm, OpenPartialHomeomorph.symm_symm]
    exact hI
/-- **The boundary restriction of a submersion, from a linear normal form.**  If `f : M → ℝ^k` is,
on the source of a chart `e'` of the maximal atlas through a boundary point `x`, the linear map
`L` read in the chart `e'` (`f y = L ((e'.extend I) y)`), where `L` is surjective and kills a vector
whose zeroth coordinate is nonzero, then the restriction of `f` to the boundary `∂M` is a submersion
at `x` (as a point of the boundaryless `n`-manifold `∂M`).

The point is that on the boundary the chart `β` of `bndChart_self_maximalAtlas` makes `f` linear in
the *coordinates* of the boundary, with linear part `L ∘ consZeroCLM n`, and that linear map is
surjective: a right inverse of `L` whose image lies in the hyperplane `{z | z 0 = 0}` (which exists by
`exists_rightInverse_coord_eq_zero`, using the kernel vector) provides a right inverse `v ↦ tailCLM n (σ v)`
of `L ∘ consZeroCLM n`. -/
theorem isSubmersionAt_boundary_of_linearization {n k : ℕ} {M : Type} [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace (n + 1)) M]
    [IsManifold (modelWithCornersEuclideanHalfSpace (n + 1)) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    {f : M → EuclideanSpace ℝ (Fin k)} {x : M}
    (hxb : x ∈ (modelWithCornersEuclideanHalfSpace (n + 1)).boundary M)
    {e' : OpenPartialHomeomorph M (EuclideanHalfSpace (n + 1))}
    (he' : e' ∈ IsManifold.maximalAtlas (modelWithCornersEuclideanHalfSpace (n + 1))
      ((⊤ : ℕ∞) : WithTop ℕ∞) M)
    (hxe' : x ∈ e'.source)
    {L : EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ] EuclideanSpace ℝ (Fin k)}
    (hLsurj : Function.Surjective L)
    (hnorm : ∃ v : EuclideanSpace ℝ (Fin (n + 1)), L v = 0 ∧ v 0 ≠ 0)
    (hnf : ∀ y ∈ e'.source, f y = L ((e'.extend (𝓡∂ (n + 1))) y)) :
    Manifold.IsSubmersionAt (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin k))) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun y : ↥((modelWithCornersEuclideanHalfSpace (n + 1)).boundary M) => f y.1)
      ⟨x, hxb⟩ := by
  classical
  obtain ⟨v, hv, hv0⟩ := hnorm
  obtain ⟨σ, hσ, hσ0⟩ := exists_rightInverse_coord_eq_zero hv hv0 hLsurj
  -- the linear part of `f` on the boundary
  let L₀ : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin k) :=
    L.comp (Work.Surgery.consZeroCLM n)
  have hL₀surj : Function.Surjective L₀ := by
    intro y
    refine ⟨Work.Surgery.tailCLM n (σ y), ?_⟩
    show L (Work.Surgery.consZeroCLM n (Work.Surgery.tailCLM n (σ y))) = y
    rw [Work.Surgery.consZeroCLM_tailCLM n _ (hσ0 y)]
    exact hσ y
  -- a right inverse of `L₀` and the resulting linear equivalence
  obtain ⟨σ₀, hσ₀⟩ := ContinuousLinearMap.exists_rightInverse_of_surjective L₀
    (LinearMap.range_eq_top.mpr hL₀surj)
  have hσ₀' : ∀ y, L₀ (σ₀ y) = y := fun y => by
    have h := congrArg (fun (g : EuclideanSpace ℝ (Fin k) →L[ℝ] EuclideanSpace ℝ (Fin k)) => g y)
      hσ₀
    simpa using h
  let φeq : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] (EuclideanSpace ℝ (Fin k) × L₀.ker) :=
    { toFun := fun w => (L₀ w, ⟨w - σ₀ (L₀ w), by
        show L₀ (w - σ₀ (L₀ w)) = 0
        rw [map_sub, hσ₀', sub_self]⟩)
      map_add' := fun a b => by
        refine Prod.ext ?_ ?_
        · show L₀ (a + b) = L₀ a + L₀ b
          rw [map_add]
        · refine Subtype.ext ?_
          show (a + b) - σ₀ (L₀ (a + b)) = (a - σ₀ (L₀ a)) + (b - σ₀ (L₀ b))
          rw [map_add, map_add]
          abel
      map_smul' := fun r a => by
        refine Prod.ext ?_ ?_
        · show L₀ (r • a) = r • L₀ a
          rw [map_smul]
        · refine Subtype.ext ?_
          show (r • a) - σ₀ (L₀ (r • a)) = r • (a - σ₀ (L₀ a))
          rw [map_smul, map_smul, smul_sub] }
  have hbij : Function.Bijective φeq := by
    constructor
    · intro a b hab
      have h1 : L₀ a = L₀ b := congrArg (fun p => p.1) hab
      have h2 : (a - σ₀ (L₀ a)) = (b - σ₀ (L₀ b)) :=
        congrArg (fun p => (p.2 : EuclideanSpace ℝ (Fin n))) hab
      calc a = σ₀ (L₀ a) + (a - σ₀ (L₀ a)) := by abel
        _ = σ₀ (L₀ b) + (b - σ₀ (L₀ b)) := by rw [h2, h1]
        _ = b := by abel
    · intro p
      obtain ⟨y, w⟩ := p
      refine ⟨σ₀ y + w, ?_⟩
      refine Prod.ext ?_ ?_
      · show L₀ (σ₀ y + w) = y
        rw [map_add, hσ₀']
        have hw : L₀ (w : EuclideanSpace ℝ (Fin n)) = 0 := w.2
        rw [hw, add_zero]
      · refine Subtype.ext ?_
        show ((σ₀ y + w : EuclideanSpace ℝ (Fin n))
            - σ₀ (L₀ (σ₀ y + (w : EuclideanSpace ℝ (Fin n)))))
          = (w : EuclideanSpace ℝ (Fin n))
        rw [map_add, hσ₀']
        have hw : L₀ (w : EuclideanSpace ℝ (Fin n)) = 0 := w.2
        rw [hw, add_zero, add_sub_cancel_left]
  let B : EuclideanSpace ℝ (Fin n) ≃L[ℝ] (EuclideanSpace ℝ (Fin k) × L₀.ker) :=
    (LinearEquiv.ofBijective φeq hbij).toContinuousLinearEquiv
  -- the boundary chart of `e'`
  obtain ⟨β, hβmem, hβsrc, hβtgt, hβapp, hβsymm⟩ := bndChart_self_maximalAtlas e' he' ⟨x, hxb⟩
  have hβext_tgt : (β.extend (𝓡 n)).target = β.target := by
    rw [OpenPartialHomeomorph.extend_target', modelWithCornersSelf_coe]
    simp
  have hβext_symm : ∀ u : EuclideanSpace ℝ (Fin n), (β.extend (𝓡 n)).symm u = β.symm u := by
    intro u
    have h := congrFun (OpenPartialHomeomorph.extend_coe_symm β (I := 𝓡 n)) u
    simpa only [modelWithCornersSelf_coe_symm, Function.comp_apply, id_eq] using h
  -- the normal form on the boundary
  have hkey : ∀ u ∈ (β.extend (𝓡 n)).target,
      f ((β.extend (𝓡 n)).symm u).1 = L₀ u := by
    intro u hu
    have hu' : u ∈ β.target := by rw [← hβext_tgt]; exact hu
    rw [hβext_symm u]
    have h1 : (β.symm u).1 ∈ e'.source := by
      have hm : β.symm u ∈ β.source := β.map_target hu'
      rw [hβsrc] at hm
      exact hm
    have h3 : ((e'.extend (𝓡∂ (n + 1))) (β.symm u).1).ofLp 0 = 0 :=
      (Work.ThomBordism.Transversality.Preimage.mem_boundary_iff_extend_apply_coord_eq_zero
        (m := n + 1) he' h1).mp (β.symm u).2
    have h2 : (e'.extend (𝓡∂ (n + 1))) (β.symm u).1 = Work.Surgery.consZeroCLM n u := by
      rw [← Work.Surgery.consZeroCLM_tailCLM n _ h3, ← hβapp (β.symm u), β.right_inv hu']
    rw [hnf (β.symm u) h1, h2]
    rfl
  refine Manifold.IsSubmersionAt.mk_of_charts (F := L₀.ker) B β
    (OpenPartialHomeomorph.refl (EuclideanSpace ℝ (Fin k)))
    ?_ (mem_univ _) hβmem
    (StructureGroupoid.id_mem_maximalAtlas
      (G := contDiffGroupoid ((⊤ : ℕ∞) : WithTop ℕ∞) (𝓡 k)))
    (fun _ _ => mem_univ _) ?_
  · rw [hβsrc]
    exact hxe'
  · intro u hu
    exact hkey u hu

theorem isSubmersionAt_and_boundary_of_chartModel {n k : ℕ} {M : Type} [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace (n + 1)) M]
    [IsManifold (modelWithCornersEuclideanHalfSpace (n + 1)) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    {e : OpenPartialHomeomorph M (EuclideanHalfSpace (n + 1))}
    (he : e ∈ IsManifold.maximalAtlas (modelWithCornersEuclideanHalfSpace (n + 1))
      ((⊤ : ℕ∞) : WithTop ℕ∞) M)
    {x : M} (hxe : x ∈ e.source)
    (hxb : x ∈ (modelWithCornersEuclideanHalfSpace (n + 1)).boundary M)
    {f : M → EuclideanSpace ℝ (Fin k)}
    {g : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin k)}
    (hg : ∃ U ∈ nhds ((e.extend (modelWithCornersEuclideanHalfSpace (n + 1))) x),
      ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g U)
    (hagree : Filter.EventuallyEq (nhds x) f
      (fun y => g ((e.extend (modelWithCornersEuclideanHalfSpace (n + 1))) y)))
    (hsurj : Function.Surjective (fderiv ℝ g
      ((e.extend (modelWithCornersEuclideanHalfSpace (n + 1))) x)))
    (hnorm : ∃ v : EuclideanSpace ℝ (Fin (n + 1)),
      fderiv ℝ g ((e.extend (modelWithCornersEuclideanHalfSpace (n + 1))) x) v = 0 ∧ v 0 ≠ 0) :
    Manifold.IsSubmersionAt (modelWithCornersEuclideanHalfSpace (n + 1))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin k))) ((⊤ : ℕ∞) : WithTop ℕ∞) f x ∧
    Manifold.IsSubmersionAt (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin k))) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun y : ↥((modelWithCornersEuclideanHalfSpace (n + 1)).boundary M) => f y.1) ⟨x, hxb⟩ := by
  obtain ⟨hsub, e', he', hxe', hnf⟩ :=
    exists_chart_boundary_linearization he hxe hg hagree hsurj hnorm
  exact ⟨hsub,
    isSubmersionAt_boundary_of_linearization hxb he' hxe' hsurj hnorm hnf⟩

end

end Work.PTGeometric
