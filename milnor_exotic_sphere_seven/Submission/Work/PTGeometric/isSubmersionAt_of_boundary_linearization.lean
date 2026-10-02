import Mathlib
import Submission.Work.ThomBordism.Transversality.TransverseSard.LocalRep
import Submission.Work.PTGeometric.FDerivInChart
import Submission.Work.PTGeometric.exists_rightInverse_coord_eq_zero
import Submission.Work.PTGeometric.exists_localDiffeomorph_eq_linear_of_coord_preserving_smooth
import Submission.Work.PTGeometric.exists_chart_extend_of_openPartialHomeomorph_range_smooth

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# `IsSubmersionAt` at a boundary point from a linearisation in a chart

Mathlib's `Manifold.IsSubmersionAt` is the *local normal form* notion: `f` is a submersion at `x`
if there are charts near `x` and `f x` in which `f` is the standard projection.  The equivalence
with surjectivity of `mfderiv` is a TODO of Mathlib; for *interior* points it is proved in
`Work.ThomBordism.Transversality.TransverseSard.isSubmersionAt_of_surjective_fderiv_localRep`.

At a **boundary** point the situation is genuinely different, and a surjective derivative is *not*
enough: the fibre of a submersion at a boundary point has to meet the boundary there as well, which
forces the kernel of the derivative to contain a direction transverse to the boundary hyperplane.
This file proves the corresponding sufficient condition:

`isSubmersionAt_of_boundary_linearization`: if in a chart `e` of the maximal atlas at `x` the map
`f` agrees near `x` with `g ∘ (e.extend _)`, where `g : ℝ^N → ℝ^k` is `C^∞` near `c := e.extend x`
with `g c = 0`, `fderiv ℝ g c` surjective and with some `v ∈ ker (fderiv ℝ g c)` whose zeroth
coordinate is nonzero, then `f` is a submersion at `x`.

The proof straightens `g` near `c` by the explicit local diffeomorphism
`T w = w + σ (g w - L w)`, where `L = fderiv ℝ g c` and `σ` is a right inverse of `L` whose image
lies in the hyperplane `{w | w 0 = 0}` (which exists precisely because a kernel vector has nonzero
zeroth coordinate).  `T` therefore *preserves the half space* `{w | w 0 ≥ 0}`, so conjugating the
chart `e` by `T` gives a chart of `M` at `x` in which `f` is the linear map `L` — this is the
conjugation lemma `exists_chart_extend_of_openPartialHomeomorph_range_smooth`, a variant of
`exists_chart_extend_of_openPartialHomeomorph` in which the *interiority* hypotheses on the source
and target of `T` are replaced by the half-space preservation, which is what makes the boundary
case accessible.

(The hypotheses `hfx` and `hg0` are kept for compatibility with the interface; the argument does
not need them, the codomain chart being the identity.)
-/

namespace Work.PTGeometric

open scoped Manifold ContDiff Topology
open Function Set Topology Manifold Filter

noncomputable section

set_option maxHeartbeats 1000000
set_option linter.style.haveILetI false

theorem isSubmersionAt_of_boundary_linearization {N k : ℕ} [NeZero N] {M : Type*}
    [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace N) M]
    [IsManifold (𝓡∂ N) ∞ M]
    {e : OpenPartialHomeomorph M (EuclideanHalfSpace N)}
    (he : e ∈ IsManifold.maximalAtlas (𝓡∂ N) ∞ M) {x : M} (hx : x ∈ e.source)
    {f : M → EuclideanSpace ℝ (Fin k)}
    {g : EuclideanSpace ℝ (Fin N) → EuclideanSpace ℝ (Fin k)}
    (hg : ∃ U ∈ 𝓝 ((e.extend (𝓡∂ N)) x), ContDiffOn ℝ ∞ g U)
    (hfx : f x = 0) (hg0 : g ((e.extend (𝓡∂ N)) x) = 0)
    (hagree : f =ᶠ[𝓝 x] fun y => g ((e.extend (𝓡∂ N)) y))
    (hsurj : Function.Surjective (fderiv ℝ g ((e.extend (𝓡∂ N)) x)))
    (hnorm : ∃ v : EuclideanSpace ℝ (Fin N), fderiv ℝ g ((e.extend (𝓡∂ N)) x) v = 0 ∧ v 0 ≠ 0) :
    Manifold.IsSubmersionAt (𝓡∂ N) (𝓡 k) ∞ f x := by
  classical
  set c : EuclideanSpace ℝ (Fin N) := (e.extend (𝓡∂ N)) x with hc_def
  set L : EuclideanSpace ℝ (Fin N) →L[ℝ] EuclideanSpace ℝ (Fin k) := fderiv ℝ g c with hL_def
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
      (U := U') (χ := coordFun N) (σ := σ) hU'open hcU' (hgU.mono hU'sub)
      (by rw [hL_def]) hσ hσ0
  -- `T` preserves the half space, both ways
  have hrange : Set.range (𝓡∂ N) = {w : EuclideanSpace ℝ (Fin N) | 0 ≤ w 0} := by
    rw [range_modelWithCornersEuclideanHalfSpace]
  have hTmap : ∀ ⦃w : EuclideanSpace ℝ (Fin N)⦄, w ∈ T.source →
      w ∈ Set.range (𝓡∂ N) → T w ∈ Set.range (𝓡∂ N) := by
    intro w hw hwr
    rw [hrange] at hwr ⊢
    simp only [Set.mem_ofPred_eq] at hwr ⊢
    rw [← coordFun_apply, hTχ w hw, coordFun_apply]
    exact hwr
  have hTsmap : ∀ ⦃w : EuclideanSpace ℝ (Fin N)⦄, w ∈ T.target →
      w ∈ Set.range (𝓡∂ N) → T.symm w ∈ Set.range (𝓡∂ N) := by
    intro w hw hwr
    rw [hrange] at hwr ⊢
    simp only [Set.mem_ofPred_eq] at hwr ⊢
    have h1 : T.symm w ∈ T.source := T.map_target hw
    have h2 : coordFun N (T (T.symm w)) = coordFun N w := congrArg (coordFun N) (T.right_inv hw)
    rw [hTχ (T.symm w) h1] at h2
    rw [← coordFun_apply, h2, coordFun_apply]
    exact hwr
  -- the conjugated chart
  obtain ⟨e', he'mem, hxe', he'conj⟩ :=
    exists_chart_extend_of_openPartialHomeomorph_range_smooth (𝓡∂ N) he hx hTsm hTsm_inv hTmap hTsmap hcT
  -- cut down to the set where `f` agrees with `g ∘ (e.extend _)`
  obtain ⟨S₁, hS₁sub, hS₁open, hxS₁⟩ := mem_nhds_iff.mp hagree
  set S : Set M := e'.source ∩ S₁ with hS_def
  have hSopen : IsOpen S := e'.open_source.inter hS₁open
  set e'' : OpenPartialHomeomorph M (EuclideanHalfSpace N) := e'.restr S with he''_def
  have he''_src : e''.source = e'.source ∩ S₁ := by
    rw [he''_def, OpenPartialHomeomorph.restr_source, hSopen.interior_eq, hS_def]
    exact Set.inter_eq_right.mpr Set.inter_subset_left
  have hx'' : x ∈ e''.source := by
    rw [he''_src]; exact ⟨hxe', hxS₁⟩
  have he''_ext : ∀ y : M, (e''.extend (𝓡∂ N)) y = (e'.extend (𝓡∂ N)) y := by
    intro y
    rw [OpenPartialHomeomorph.extend_coe, OpenPartialHomeomorph.extend_coe,
      OpenPartialHomeomorph.restr_apply]
  have he''_mem : e'' ∈ IsManifold.maximalAtlas (𝓡∂ N) ∞ M := by
    rw [he''_def]
    exact restr_mem_maximalAtlas (contDiffGroupoid ∞ (𝓡∂ N)) he'mem hSopen
  -- the linear equivalence `E ≃L (ℝ^k × ker L)` with first component `L`
  have hσ' : ∀ y : EuclideanSpace ℝ (Fin k), L (σ y) = y := hσ
  let φ : EuclideanSpace ℝ (Fin N) →ₗ[ℝ] (EuclideanSpace ℝ (Fin k) × L.ker) :=
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
        congrArg (fun p => (p.2 : EuclideanSpace ℝ (Fin N))) hab
      calc a = σ (L a) + (a - σ (L a)) := by abel
        _ = σ (L b) + (b - σ (L b)) := by rw [h2, h1]
        _ = b := by abel
    · intro p
      obtain ⟨y, w⟩ := p
      refine ⟨σ y + w, ?_⟩
      refine Prod.ext ?_ ?_
      · show L (σ y + w) = y
        rw [map_add, hσ']
        have hw : L (w : EuclideanSpace ℝ (Fin N)) = 0 := w.2
        rw [hw, add_zero]
      · refine Subtype.ext ?_
        show ((σ y + w : EuclideanSpace ℝ (Fin N)) - σ (L (σ y + (w : EuclideanSpace ℝ (Fin N)))))
          = (w : EuclideanSpace ℝ (Fin N))
        rw [map_add, hσ']
        have hw : L (w : EuclideanSpace ℝ (Fin N)) = 0 := w.2
        rw [hw, add_zero, add_sub_cancel_left]
  let equ : EuclideanSpace ℝ (Fin N) ≃L[ℝ] (EuclideanSpace ℝ (Fin k) × L.ker) :=
    (LinearEquiv.ofBijective φ hbij).toContinuousLinearEquiv
  have hequ_pr : ∀ w : EuclideanSpace ℝ (Fin N), (equ w).1 = L w := fun w => rfl
  refine Manifold.IsSubmersionAt.mk_of_charts (F := L.ker) equ e'' (OpenPartialHomeomorph.refl _)
    hx'' (mem_univ _) he''_mem
    (StructureGroupoid.id_mem_maximalAtlas (G := contDiffGroupoid ∞ (𝓡 k)))
    (fun _ _ => mem_univ _) ?_
  intro w hw
  set y : M := (e''.extend (𝓡∂ N)).symm w with hy_def
  have hy_src : y ∈ e''.source := by
    rw [← OpenPartialHomeomorph.extend_source (f := e'') (I := 𝓡∂ N)]
    exact (e''.extend (𝓡∂ N)).map_target hw
  have hy' : y ∈ e'.source := by rw [he''_src] at hy_src; exact hy_src.1
  have hyS₁ : y ∈ S₁ := by rw [he''_src] at hy_src; exact hy_src.2
  have hwy : (e''.extend (𝓡∂ N)) y = w := (e''.extend (𝓡∂ N)).right_inv hw
  have hconj' : (e.extend (𝓡∂ N)) y ∈ T.source ∧
      (e''.extend (𝓡∂ N)) y = T ((e.extend (𝓡∂ N)) y) := by
    obtain ⟨h1, h2⟩ := he'conj y hy'
    exact ⟨h1, by rw [he''_ext y]; exact h2⟩
  have key : f y = L w := by
    calc f y = g ((e.extend (𝓡∂ N)) y) := hS₁sub hyS₁
      _ = L (T ((e.extend (𝓡∂ N)) y)) := (hTlin _ hconj'.1).symm
      _ = L ((e''.extend (𝓡∂ N)) y) := by rw [hconj'.2]
      _ = L w := by rw [hwy]
  show f ((e''.extend (𝓡∂ N)).symm w) = L w
  rw [show (e''.extend (𝓡∂ N)).symm w = y from rfl]
  exact key

end

end Work.PTGeometric
