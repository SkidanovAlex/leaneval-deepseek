import Mathlib
import Submission.Work.Smooth.OneManifold.Plane.Basic

/-!
# The plane model of a transverse corner

Let `f g : ℝ × ℝ → ℝ` be `C¹` at `p` with `f p = g p = 0` and with the pair of derivatives
`(fderiv f p, fderiv g p)` invertible.  Then `(f, g)` is a local homeomorphism at `p`, and the
zero set of the maximum,
`{q | max (f q) (g q) = 0}`,
is locally the standard corner `{(a, b) | max a b = 0}` — the union of the two negative coordinate
half-axes, which is homeomorphic to `ℝ` (`Work.Smooth.OneManifold.isLocallyArc_max_zero`).  Hence
it is locally an arc.
-/

open Set

namespace Work.Smooth.OneManifold

noncomputable section

open scoped Topology

/-- **A transverse corner of a level set of a maximum is locally an arc.** -/
theorem isLocallyArc_max_of_isInvertible {f g : ℝ × ℝ → ℝ} {p : ℝ × ℝ}
    (hf : ContDiffAt ℝ 1 f p) (hg : ContDiffAt ℝ 1 g p) (hfp : f p = 0) (hgp : g p = 0)
    (hinv : ((fderiv ℝ f p).prod (fderiv ℝ g p)).IsInvertible) :
    ∃ V : Set (ℝ × ℝ), IsOpen V ∧ p ∈ V ∧
      Work.Smooth.SphereJordan.IsLocallyArc ↥(V ∩ {q : ℝ × ℝ | max (f q) (g q) = 0}) := by
  obtain ⟨A, hA⟩ := hinv
  have hn : (1 : WithTop ℕ∞) ≠ 0 := by norm_num
  have hAstrict : HasStrictFDerivAt (fun q : ℝ × ℝ => (f q, g q))
      (A : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ)) p := by
    have h := (hf.hasStrictFDerivAt hn).prodMk (hg.hasStrictFDerivAt hn)
    rwa [← hA] at h
  let Φ : OpenPartialHomeomorph (ℝ × ℝ) (ℝ × ℝ) :=
    hAstrict.toOpenPartialHomeomorph (fun q : ℝ × ℝ => (f q, g q))
  have hpsrc : p ∈ Φ.source := hAstrict.mem_toOpenPartialHomeomorph_source
  have hΦ : ∀ q ∈ Φ.source, (Φ q : ℝ × ℝ) = (f q, g q) := fun q _ => rfl
  -- the corner model in the target plane
  set W : Set (ℝ × ℝ) := {z : ℝ × ℝ | max z.1 z.2 = 0} with hWdef
  have h1 : Work.Smooth.SphereJordan.IsLocallyArc ↥(W ∩ Φ.target) :=
    isLocallyArc_inter_of_isOpen isLocallyArc_max_zero Φ.open_target
  -- transport to the source plane along `Φ`
  have h2 : Work.Smooth.SphereJordan.IsLocallyArc
      ↥(Subtype.val ⁻¹' (W ∩ Φ.target) : Set ↥Φ.target) :=
    isLocallyArc_preimage_subtypeVal (show W ∩ Φ.target ⊆ Φ.target from inter_subset_right) h1
  have h3 : Work.Smooth.SphereJordan.IsLocallyArc
      ↥(Φ.toHomeomorphSourceTarget.symm '' (Subtype.val ⁻¹' (W ∩ Φ.target))) :=
    isLocallyArc_image_of_homeomorph Φ.toHomeomorphSourceTarget.symm h2
  have h4 : Work.Smooth.SphereJordan.IsLocallyArc
      ↥(Subtype.val '' (Φ.toHomeomorphSourceTarget.symm ''
        (Subtype.val ⁻¹' (W ∩ Φ.target)))) :=
    isLocallyArc_subtypeVal_image h3
  -- identify the transported set with `Φ.source ∩ {max (f q) (g q) = 0}`
  have hset : Subtype.val '' (Φ.toHomeomorphSourceTarget.symm ''
        (Subtype.val ⁻¹' (W ∩ Φ.target)))
      = Φ.source ∩ {q : ℝ × ℝ | max (f q) (g q) = 0} := by
    ext z
    constructor
    · rintro ⟨y, ⟨w, hw, hwy⟩, hyz⟩
      have hwW : (w : ℝ × ℝ) ∈ W := hw.1
      have hyval : (y : ℝ × ℝ) = Φ.symm (w : ℝ × ℝ) := by
        have h := congrArg (fun t : ↥Φ.source => (t : ℝ × ℝ)) hwy
        simpa using h.symm
      have hwΦ : (w : ℝ × ℝ) = Φ (y : ℝ × ℝ) := by
        rw [hyval]
        exact (Φ.right_inv w.2).symm
      have hmax : max (Φ (y : ℝ × ℝ)).1 (Φ (y : ℝ × ℝ)).2 = 0 := by
        rw [← hwΦ]
        exact hwW
      rw [hΦ (y : ℝ × ℝ) y.2] at hmax
      refine ⟨by rw [← hyz]; exact y.2, ?_⟩
      rwa [hyz] at hmax
    · rintro ⟨hzsrc, hzmax⟩
      have hzw : ((Φ.toHomeomorphSourceTarget (⟨z, hzsrc⟩ : ↥Φ.source) : ℝ × ℝ)) ∈ W ∩ Φ.target := by
        refine ⟨?_, (Φ.toHomeomorphSourceTarget (⟨z, hzsrc⟩ : ↥Φ.source)).2⟩
        show (Φ (⟨z, hzsrc⟩ : ↥Φ.source) : ℝ × ℝ) ∈ W
        rw [hWdef, hΦ (⟨z, hzsrc⟩ : ↥Φ.source) hzsrc]
        exact hzmax
      refine ⟨(⟨z, hzsrc⟩ : ↥Φ.source),
        ⟨Φ.toHomeomorphSourceTarget (⟨z, hzsrc⟩ : ↥Φ.source), hzw, ?_⟩, rfl⟩
      exact Homeomorph.symm_apply_apply Φ.toHomeomorphSourceTarget (⟨z, hzsrc⟩ : ↥Φ.source)
  exact ⟨Φ.source, Φ.open_source, hpsrc, isLocallyArc_of_eq hset h4⟩

end

end Work.Smooth.OneManifold
