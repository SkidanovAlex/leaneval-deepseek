import Mathlib
import Submission.Work.Projection.dimH_image_le_of_contDiffOn
import Submission.Work.Projection.isInvertible_one_add
import Submission.Work.Projection.dimH_le_of_local_param

/-!
# The Hausdorff dimension of a regular level set

We prove that the zero set of a `C¹` function `Φ : ℝ^m → ℝ` whose derivative does not vanish
on that zero set has Hausdorff dimension at most `m - 1`.

The argument is the "easy half" of Sard's theorem for level sets, and proceeds exactly as the
classical proof that a regular level set is a `C¹` submanifold of codimension one:

* at a point `x` of the level set, pick `e` with `(fderiv ℝ Φ x) e ≠ 0`;
* the "coordinate replacement" map `T y = y + (Φ y - ℓ y) • e`, where `ℓ = ((fderiv ℝ Φ x) e)⁻¹ • fderiv ℝ Φ x`
  is a linear functional with `ℓ e = 1`, is a local diffeomorphism at `x` (its derivative is
  `w ↦ w + (A w - ℓ w) • e` with `A = fderiv ℝ Φ x`, which is invertible because `A e ≠ 0`);
* the level set near `x` is the image under the (local) inverse of `T` of the hyperplane
  `ker ℓ`, which has dimension `m - 1`;
* `Work.Projection.dimH_le_of_local_param` then combines the local parametrisations into a
  countable cover using the Lindelöf property of `ℝ^m`.
-/

namespace Work.Projection

open scoped Manifold ContDiff
open Topology MeasureTheory Filter

/-- The "coordinate replacement" map `y ↦ y + (Φ y - ℓ y) • e`.  Its `i`-th coordinate (in the
sense of the functional `ℓ`) is replaced by `Φ y`. -/
noncomputable def levelMap {m : ℕ} (Φ : EuclideanSpace ℝ (Fin m) → ℝ)
    (ℓ : EuclideanSpace ℝ (Fin m) →L[ℝ] ℝ) (e : EuclideanSpace ℝ (Fin m)) :
    EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin m) :=
  fun y => y + (Φ y - ℓ y) • e

@[simp] lemma levelMap_apply {m : ℕ} (Φ : EuclideanSpace ℝ (Fin m) → ℝ)
    (ℓ : EuclideanSpace ℝ (Fin m) →L[ℝ] ℝ) (e : EuclideanSpace ℝ (Fin m))
    (y : EuclideanSpace ℝ (Fin m)) : levelMap Φ ℓ e y = y + (Φ y - ℓ y) • e := rfl

lemma contDiff_levelMap {m : ℕ} (Φ : EuclideanSpace ℝ (Fin m) → ℝ) (hΦ : ContDiff ℝ 1 Φ)
    (ℓ : EuclideanSpace ℝ (Fin m) →L[ℝ] ℝ) (e : EuclideanSpace ℝ (Fin m)) :
    ContDiff ℝ 1 (levelMap Φ ℓ e) := by
  unfold levelMap
  exact contDiff_id.add ((hΦ.sub ℓ.contDiff).smul contDiff_const)

lemma hasFDerivAt_levelMap {m : ℕ} (Φ : EuclideanSpace ℝ (Fin m) → ℝ) (hΦ : ContDiff ℝ 1 Φ)
    (ℓ : EuclideanSpace ℝ (Fin m) →L[ℝ] ℝ) (e : EuclideanSpace ℝ (Fin m))
    (x : EuclideanSpace ℝ (Fin m)) :
    HasFDerivAt (levelMap Φ ℓ e) (1 + (fderiv ℝ Φ x - ℓ).smulRight e) x := by
  unfold levelMap
  have h : HasFDerivAt (fun y : EuclideanSpace ℝ (Fin m) => Φ y - ℓ y)
      (fderiv ℝ Φ x - ℓ) x :=
    ((hΦ.differentiable (by norm_num) x).hasFDerivAt.sub ℓ.hasFDerivAt)
  exact (hasFDerivAt_id x).add (h.smul_const e)

/-- Near a point `x` at which the derivative of `Φ` does not vanish, the level set `Φ ⁻¹' {0}` is
the image of a `C¹` map defined on an open subset of a subspace of dimension at most `m - 1`.
Concretely, the subspace is the kernel of a linear functional `ℓ` with `ℓ e = 1`, for a direction
`e` in which the derivative of `Φ` at `x` does not vanish, and the parametrisation is the inverse
of the local diffeomorphism `levelMap Φ ℓ e` composed with the inclusion of that kernel. -/
theorem exists_local_param {m : ℕ} (Φ : EuclideanSpace ℝ (Fin m) → ℝ) (hΦ : ContDiff ℝ 1 Φ)
    (x : EuclideanSpace ℝ (Fin m)) (hA : fderiv ℝ Φ x ≠ 0) :
    ∃ (H : Submodule ℝ (EuclideanSpace ℝ (Fin m))) (g : H → EuclideanSpace ℝ (Fin m))
      (V : Set H) (U : Set (EuclideanSpace ℝ (Fin m))),
      Module.finrank ℝ H ≤ m - 1 ∧ IsOpen V ∧ ContDiffOn ℝ 1 g V ∧ IsOpen U ∧ x ∈ U ∧
      {y | Φ y = 0} ∩ U ⊆ g '' V := by
  -- a direction `e` in which the derivative of `Φ` at `x` does not vanish
  obtain ⟨e, he⟩ : ∃ e : EuclideanSpace ℝ (Fin m), (fderiv ℝ Φ x) e ≠ 0 := by
    by_contra h
    simp only [not_exists, not_not] at h
    exact hA (ContinuousLinearMap.ext fun v => by simp [h v])
  set A := fderiv ℝ Φ x with hA_def
  -- the functional `ℓ` with `ℓ e = 1`
  set ℓ : EuclideanSpace ℝ (Fin m) →L[ℝ] ℝ := (A e)⁻¹ • A with hℓ_def
  have hℓe : ℓ e = 1 := by
    rw [hℓ_def, smul_apply]
    exact inv_mul_cancel₀ he
  have hTcont : ContDiff ℝ 1 (levelMap Φ ℓ e) := contDiff_levelMap Φ hΦ ℓ e
  have hTfd : HasFDerivAt (levelMap Φ ℓ e) (1 + (A - ℓ).smulRight e) x := by
    rw [hA_def]; exact hasFDerivAt_levelMap Φ hΦ ℓ e x
  obtain ⟨L', hL'⟩ := isInvertible_one_add A ℓ e hℓe he
  have hTfd' : HasFDerivAt (levelMap Φ ℓ e) (L' : EuclideanSpace ℝ (Fin m) →L[ℝ]
      EuclideanSpace ℝ (Fin m)) x := hTfd.congr_fderiv hL'.symm
  have hTstrict : HasStrictFDerivAt (levelMap Φ ℓ e) (L' : EuclideanSpace ℝ (Fin m) →L[ℝ]
      EuclideanSpace ℝ (Fin m)) x :=
    hTcont.contDiffAt.hasStrictFDerivAt' hTfd' (by norm_num)
  -- the inverse function theorem: `levelMap Φ ℓ e` is a local homeomorphism at `x`
  let ee := hTstrict.toOpenPartialHomeomorph (levelMap Φ ℓ e)
  have hee : (⇑ee) = levelMap Φ ℓ e := HasStrictFDerivAt.toOpenPartialHomeomorph_coe hTstrict
  have hxsrc : x ∈ ee.source := hTstrict.mem_toOpenPartialHomeomorph_source
  have hxtgt : levelMap Φ ℓ e x ∈ ee.target :=
    hTstrict.image_mem_toOpenPartialHomeomorph_target
  -- the open set of points where the derivative of `levelMap Φ ℓ e` stays invertible
  have hWopen : IsOpen {y : EuclideanSpace ℝ (Fin m) | (fderiv ℝ Φ y) e ≠ 0} := by
    refine isOpen_ne.preimage ?_
    exact (hΦ.continuous_fderiv_apply (by norm_num)).comp (continuous_id.prodMk continuous_const)
  set W : Set (EuclideanSpace ℝ (Fin m)) := {y | (fderiv ℝ Φ y) e ≠ 0} ∩ ee.source with hW_def
  have hWopen' : IsOpen W := hWopen.inter ee.open_source
  have hxW : x ∈ W := ⟨he, hxsrc⟩
  set Tset : Set (EuclideanSpace ℝ (Fin m)) := ee.target ∩ ee.symm ⁻¹' W with hTset_def
  have hTset_open : IsOpen Tset := ee.isOpen_inter_preimage_symm hWopen'
  have hTxt : levelMap Φ ℓ e x ∈ Tset := by
    refine ⟨hxtgt, ?_⟩
    have h1 : ee.symm (levelMap Φ ℓ e x) = x := by
      rw [← hee]; exact ee.left_inv hxsrc
    rw [Set.mem_preimage, h1]
    exact hxW
  -- the inverse of `levelMap Φ ℓ e` is `C¹` on `Tset`
  have hsymm : ContDiffOn ℝ 1 (⇑ee.symm) Tset := by
    intro a ha
    rw [contDiffWithinAt_iff_contDiffAt (hTset_open.mem_nhds ha)]
    have hyW : ee.symm a ∈ W := ha.2
    obtain ⟨e'', he''⟩ :=
      isInvertible_one_add (fderiv ℝ Φ (ee.symm a)) ℓ e hℓe hyW.1
    have h1 : ContDiffAt ℝ 1 (⇑ee) (ee.symm a) := hTcont.contDiffAt
    have h3 : HasFDerivAt (⇑ee) (fderiv ℝ (levelMap Φ ℓ e) (ee.symm a)) (ee.symm a) :=
      (hTcont.differentiable (by norm_num) (ee.symm a)).hasFDerivAt
    have h4 : (e'' : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m))
        = fderiv ℝ (levelMap Φ ℓ e) (ee.symm a) := by
      rw [he'', (hasFDerivAt_levelMap Φ hΦ ℓ e (ee.symm a)).fderiv]
    exact ee.contDiffAt_symm ha.1 (h3.congr_fderiv h4.symm) h1
  -- the parametrisation is the inverse of `levelMap Φ ℓ e`, restricted to the hyperplane `ker ℓ`
  refine ⟨LinearMap.ker (ℓ : EuclideanSpace ℝ (Fin m) →ₗ[ℝ] ℝ),
      fun w => ee.symm (w : EuclideanSpace ℝ (Fin m)),
      {w : LinearMap.ker (ℓ : EuclideanSpace ℝ (Fin m) →ₗ[ℝ] ℝ) |
        (w : EuclideanSpace ℝ (Fin m)) ∈ Tset},
      ee.source ∩ levelMap Φ ℓ e ⁻¹' Tset, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- the hyperplane `ker ℓ` is proper, hence has dimension at most `m - 1`
    have hne : LinearMap.ker (ℓ : EuclideanSpace ℝ (Fin m) →ₗ[ℝ] ℝ) ≠ ⊤ := by
      intro h
      have hmem : (ℓ : EuclideanSpace ℝ (Fin m) →ₗ[ℝ] ℝ) e = 0 := by
        have : e ∈ LinearMap.ker (ℓ : EuclideanSpace ℝ (Fin m) →ₗ[ℝ] ℝ) := by rw [h]; trivial
        simpa using this
      have h0 : ℓ e = 0 := hmem
      rw [h0] at hℓe
      exact one_ne_zero hℓe.symm
    have hlt := Submodule.finrank_lt hne
    rw [finrank_euclideanSpace, Fintype.card_fin] at hlt
    omega
  · exact hTset_open.preimage (Submodule.subtypeL _).continuous
  · have hsub : ContDiff ℝ 1 (⇑(Submodule.subtypeL
        (LinearMap.ker (ℓ : EuclideanSpace ℝ (Fin m) →ₗ[ℝ] ℝ)))) :=
      ContinuousLinearMap.contDiff _
    exact hsymm.comp hsub.contDiffOn (fun w hw => hw)
  · exact ee.open_source.inter (hTset_open.preimage hTcont.continuous)
  · exact ⟨hxsrc, hTxt⟩
  · -- every point of the level set near `x` is such an image
    rintro y ⟨hy0, hyU⟩
    refine ⟨⟨levelMap Φ ℓ e y, ?_⟩, hyU.2, ?_⟩
    · rw [LinearMap.mem_ker]
      show ℓ (levelMap Φ ℓ e y) = 0
      rw [levelMap_apply, map_add, map_smul, hℓe, hy0]
      simp
    · exact ee.left_inv hyU.1

/-- A `C¹` hypersurface given as a level set: if the derivative of `Φ : ℝ^m → ℝ` does not vanish
at any point of `Φ ⁻¹' {0}`, then that level set has Hausdorff dimension at most `m - 1`.  This is
the zero-set analogue of `Work.Projection.dimH_image_le_of_contDiffOn` (the "easy half" of Sard for
level sets): near each point the implicit function map exhibits the level set as a graph over `m - 1`
coordinates, so it is covered by countably many images of `C¹` maps defined on open subsets of a
space of dimension `m - 1`. -/
theorem dimH_levelSet_le {m : ℕ} (Φ : EuclideanSpace ℝ (Fin m) → ℝ)
    (hΦ : ContDiff ℝ 1 Φ) (hreg : ∀ x, Φ x = 0 → fderiv ℝ Φ x ≠ 0) :
    dimH {x : EuclideanSpace ℝ (Fin m) | Φ x = 0} ≤ m - 1 := by
  rcases Nat.eq_zero_or_pos m with hm | hm
  · -- in dimension `0` the hypotheses are contradictory, so the level set is empty
    subst hm
    have hempty : {x : EuclideanSpace ℝ (Fin 0) | Φ x = 0} = ∅ := by
      rw [Set.eq_empty_iff_forall_notMem]
      intro x hx
      exact hreg x hx (by
        ext v
        rw [show v = 0 from Subsingleton.elim v 0, map_zero]
        simp)
    rw [hempty, dimH_empty]
    simp
  · -- in positive dimension, cover the level set by the local parametrisations
    have hmain : dimH {x : EuclideanSpace ℝ (Fin m) | Φ x = 0} ≤ ((m - 1 : ℕ) : ENNReal) := by
      refine dimH_le_of_local_param fun x => ?_
      by_cases hx : Φ x = 0
      · obtain ⟨H, g, V, U, hfin, hVopen, hg, hUopen, hxU, hsub⟩ :=
          exists_local_param Φ hΦ x (hreg x hx)
        exact ⟨H, g, V, U, by exact_mod_cast hfin, hVopen, hg, hUopen, hxU, hsub⟩
      · refine ⟨⊥, fun _ => x, Set.univ, {y | Φ y ≠ 0}, by simp, isOpen_univ,
          contDiffOn_const, isOpen_ne.preimage hΦ.continuous, hx, ?_⟩
        rintro y ⟨hy0, hy1⟩
        exact absurd hy0 hy1
    simpa using hmain

end Work.Projection
