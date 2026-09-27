import Mathlib
import Submission.Work.Projection.Defs
import Submission.Work.Projection.SharpDefs
import Submission.Work.Projection.dimH_image_le_of_contDiffOn
import Submission.Work.Projection.dimH_badImmCharts

/-!
# The sharp bound for the Hausdorff dimension of the immersion-bad directions

`badImmCharts f p` is the set of projection directions `u ∈ ℝ^k` such that the projection along
the kernel spanned by `(u, 1)` fails to be an immersion: chartwise, `(u,1)` lies in the image of
`D_y (chartRep f (p i))` for some `y` in the target of the chart at `p i`.

The map `(y, w) ↦ extract (D_y w)` whose image is the bad set is defined on a `2n`-dimensional
space, and the crude bound of `dimH_badImmCharts` is `2n`.  The point of the present file is that
`extract` is invariant under non-zero scaling, so that `(y, w) ↦ extract (D_y w)` depends only on
the *direction* of `w`.  Directions are parametrised by the `n` affine charts `{w | w j = 1}`,
each `(n-1)`-dimensional; summing with the `n` dimensions of `y` gives the sharp value `2n - 1`.

Concretely, for `n = m + 1` we exhibit, for each `j : Fin (m+1)`, the `C¹` map
`sharpParam f p j` on the open set `sharpDom f p j ⊆ ℝ^{m+1} × (Fin m → ℝ)` (of dimension
`(m+1) + m = 2n - 1`) whose images over the chart indices exhaust `badImmCharts f p`.
-/

namespace Work.Projection

open scoped Manifold ContDiff ENNReal
open Topology MeasureTheory

/-- `(2 : ℕ∞ω) ≤ ∞`. -/
private lemma two_le_infty_sharp : (2 : ℕ∞ω) ≤ (∞ : ℕ∞ω) := by
  show ((2 : ℕ∞) : ℕ∞ω) ≤ ((⊤ : ℕ∞) : ℕ∞ω)
  exact WithTop.coe_le_coe.mpr le_top

/-- The arithmetic identity relating the dimension `(m+1) + m` of the sharp parameter space to
the bound `2*n - 1` with `n = m + 1`. -/
private lemma two_mul_sub_one_cast (m : ℕ) :
    (2 : ℝ≥0∞) * (↑(m + 1)) - 1 = (↑(2 * (m + 1) - 1) : ℝ≥0∞) := by
  rw [ENNReal.natCast_sub]
  push_cast
  ring

/-- The map `(y, t) ↦ (fderiv ℝ (chartRep f p) y) (dirVec j t)` is `C^1` on
`(chartAt p).target × univ`. -/
private lemma contDiffOn_fderiv_dirVec_chartRep {m k : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin (m + 1))) M] [IsManifold (𝓡 (m + 1)) ∞ M]
    (f : M → EuclideanSpace ℝ (Fin (k + 1))) (hf : ContMDiff (𝓡 (m + 1)) (𝓡 (k + 1)) ∞ f)
    (p : M) (j : Fin (m + 1)) :
    ContDiffOn ℝ 1 (fun yt : EuclideanSpace ℝ (Fin (m + 1)) × (Fin m → ℝ) =>
        (fderiv ℝ (chartRep f p) yt.1) (dirVec j yt.2))
      ((chartAt (EuclideanSpace ℝ (Fin (m + 1))) p).target ×ˢ Set.univ) := by
  have h2 : ContDiffOn ℝ 2 (chartRep f p)
      (chartAt (EuclideanSpace ℝ (Fin (m + 1))) p).target :=
    (contDiffOn_chartRep f hf p).of_le two_le_infty_sharp
  have hfd : ContDiffOn ℝ 1 (fderiv ℝ (chartRep f p))
      (chartAt (EuclideanSpace ℝ (Fin (m + 1))) p).target :=
    h2.fderiv_of_isOpen (chartAt (EuclideanSpace ℝ (Fin (m + 1))) p).open_target (by norm_num)
  have hfd' : ContDiffOn ℝ 1 (fun yt : EuclideanSpace ℝ (Fin (m + 1)) × (Fin m → ℝ) =>
      fderiv ℝ (chartRep f p) yt.1)
      ((chartAt (EuclideanSpace ℝ (Fin (m + 1))) p).target ×ˢ Set.univ) :=
    hfd.comp contDiffOn_fst (fun x hx => hx.1)
  have hdir : ContDiffOn ℝ 1 (fun yt : EuclideanSpace ℝ (Fin (m + 1)) × (Fin m → ℝ) =>
      dirVec j yt.2)
      ((chartAt (EuclideanSpace ℝ (Fin (m + 1))) p).target ×ˢ Set.univ) :=
    (contDiff_dirVec j).comp_contDiffOn contDiffOn_snd
  exact hfd'.clm_apply hdir

/-- The domain of the sharp parametrisation is open. -/
private lemma isOpen_sharpDom_smooth {m k : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin (m + 1))) M] [IsManifold (𝓡 (m + 1)) ∞ M]
    (f : M → EuclideanSpace ℝ (Fin (k + 1))) (hf : ContMDiff (𝓡 (m + 1)) (𝓡 (k + 1)) ∞ f)
    (p : M) (j : Fin (m + 1)) : IsOpen (sharpDom (k := k) f p j) := by
  have hcont : ContinuousOn
      (fun yw : EuclideanSpace ℝ (Fin (m + 1)) × EuclideanSpace ℝ (Fin (m + 1)) =>
        (fderiv ℝ (chartRep (n := m + 1) f p) yw.1) yw.2)
      ((chartAt (EuclideanSpace ℝ (Fin (m + 1))) p).target ×ˢ Set.univ) :=
    (contDiffOn_fderivApply_chartRep (n := m + 1) (k := k) f hf p).continuousOn
  have hΦ : ContinuousOn
      (fun yt : EuclideanSpace ℝ (Fin (m + 1)) × (Fin m → ℝ) =>
        ((yt.1 : EuclideanSpace ℝ (Fin (m + 1))), dirVec j yt.2))
      ((chartAt (EuclideanSpace ℝ (Fin (m + 1))) p).target ×ˢ Set.univ) :=
    (continuous_fst.prodMk
      ((contDiff_dirVec (m := m) j).continuous.comp continuous_snd)).continuousOn
  have hg : ContinuousOn
      (fun yt : EuclideanSpace ℝ (Fin (m + 1)) × (Fin m → ℝ) =>
        (fderiv ℝ (chartRep (n := m + 1) f p) yt.1) (dirVec j yt.2))
      ((chartAt (EuclideanSpace ℝ (Fin (m + 1))) p).target ×ˢ Set.univ) :=
    hcont.comp hΦ (fun yt hyt => by
      rw [Set.mem_prod] at hyt ⊢
      exact ⟨hyt.1, trivial⟩)
  have hlast : ContinuousOn
      (fun yt : EuclideanSpace ℝ (Fin (m + 1)) × (Fin m → ℝ) =>
        ((fderiv ℝ (chartRep (n := m + 1) f p) yt.1) (dirVec j yt.2)) (Fin.last k))
      ((chartAt (EuclideanSpace ℝ (Fin (m + 1))) p).target ×ˢ Set.univ) :=
    (by fun_prop : Continuous
      (fun z : EuclideanSpace ℝ (Fin (k + 1)) => z (Fin.last k))).comp_continuousOn hg
  have hset : sharpDom (k := k) f p j =
      ((chartAt (EuclideanSpace ℝ (Fin (m + 1))) p).target ×ˢ Set.univ) ∩
        (fun yt : EuclideanSpace ℝ (Fin (m + 1)) × (Fin m → ℝ) =>
          ((fderiv ℝ (chartRep (n := m + 1) f p) yt.1) (dirVec j yt.2)) (Fin.last k)) ⁻¹'
          ({0}ᶜ : Set ℝ) := by
    ext yt
    simp only [sharpDom, Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_prod, Set.mem_univ,
      and_true, Set.mem_preimage, Set.mem_compl_iff, Set.mem_singleton_iff]
  rw [hset]
  exact hlast.isOpen_inter_preimage
    ((chartAt (EuclideanSpace ℝ (Fin (m + 1))) p).open_target.prod isOpen_univ)
    (isOpen_compl_singleton (x := (0 : ℝ)))

/-- The sharp parametrisation of the immersion-bad directions of the chart at `p` is `C^1` on
its domain. -/
private lemma contDiffOn_sharpParam_smooth {m k : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin (m + 1))) M] [IsManifold (𝓡 (m + 1)) ∞ M]
    (f : M → EuclideanSpace ℝ (Fin (k + 1))) (hf : ContMDiff (𝓡 (m + 1)) (𝓡 (k + 1)) ∞ f)
    (p : M) (j : Fin (m + 1)) :
    ContDiffOn ℝ 1 (sharpParam (k := k) f p j) (sharpDom (k := k) f p j) := by
  have hH : ContDiffOn ℝ 1 (fun yt : EuclideanSpace ℝ (Fin (m + 1)) × (Fin m → ℝ) =>
      (fderiv ℝ (chartRep f p) yt.1) (dirVec j yt.2))
      (sharpDom (k := k) f p j) :=
    (contDiffOn_fderiv_dirVec_chartRep (m := m) (k := k) f hf p j).mono
      (fun yt hyt => ⟨hyt.1, trivial⟩)
  exact (contDiffOn_extract (k := k)).comp hH (fun yt hyt => hyt.2)

/-- Every immersion-bad direction is a value of the sharp parametrisation: since `w ≠ 0`, some
coordinate `w j` does not vanish, and `extract` is invariant under scaling by `(w j)⁻¹`. -/
private lemma badImmCharts_subset_sharpParam_smooth {m k : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin (m + 1))) M] [IsManifold (𝓡 (m + 1)) ∞ M]
    (f : M → EuclideanSpace ℝ (Fin (k + 1))) (p : ℕ → M) :
    badImmCharts (n := m + 1) (k := k) f p ⊆
      ⋃ i, ⋃ j : Fin (m + 1),
        sharpParam (k := k) f (p i) j '' sharpDom (k := k) f (p i) j := by
  rintro u ⟨i, y, hy, w, hw⟩
  -- `w` cannot be zero, since `vVec u ≠ 0`.
  have hwne : w ≠ 0 := by
    intro h
    rw [h, map_zero] at hw
    exact vVec_ne_zero u hw.symm
  -- choose a direction chart in which `w` has a non-zero coordinate
  obtain ⟨j, hj⟩ : ∃ j : Fin (m + 1), w j ≠ 0 := by
    by_contra h
    rw [not_exists] at h
    exact hwne (by ext a; exact not_not.mp (h a))
  refine Set.mem_iUnion.2 ⟨i, Set.mem_iUnion.2 ⟨j, ?_⟩⟩
  -- normalise `w` so that its `j`-th coordinate becomes `1`
  set t : Fin m → ℝ := fun a => w (j.succAbove a) / w j with ht
  have hd : dirVec (m := m) j t = (w j)⁻¹ • w := by
    rw [ht]
    ext a
    rcases Fin.eq_self_or_eq_succAbove j a with rfl | ⟨b, rfl⟩
    · rw [dirVec_apply_same]
      simp [hj]
    · rw [dirVec_apply_succAbove, div_eq_inv_mul]
      rw [WithLp.ofLp_smul 2, Pi.smul_apply, smul_eq_mul]
  -- the last coordinate of `D_y (dirVec j t)` is `(w j)⁻¹ ≠ 0`
  have hlast : ((fderiv ℝ (chartRep (n := m + 1) f (p i)) y)
      (dirVec (m := m) j t)) (Fin.last k) ≠ 0 := by
    rw [hd, map_smul, hw]
    simpa using inv_ne_zero hj
  -- and `sharpParam` recovers `u` from it
  have hparam : sharpParam (k := k) f (p i) j (y, t) = u := by
    simp only [sharpParam]
    rw [hd, map_smul, hw]
    exact extract_smul_vVec u (inv_ne_zero hj)
  exact ⟨(y, t), ⟨hy, hlast⟩, hparam⟩

/-- The set of "immersion-bad" projection directions has Hausdorff dimension at most `2*n - 1`:
this is the sharp bound, since the maps `w ↦ extract (D_y w)` are invariant under scaling `w` and
hence factor through the `(n-1)`-dimensional space of directions. -/
theorem dimH_badImmCharts_sharp {n k : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    (f : M → EuclideanSpace ℝ (Fin (k+1))) (hf : ContMDiff (𝓡 n) (𝓡 (k+1)) ∞ f)
    (p : ℕ → M) : dimH (Work.Projection.badImmCharts (n := n) (k := k) f p) ≤ 2 * n - 1 := by
  rcases n with _ | m
  · -- `n = 0`: there are no non-zero tangent directions, so the bad set is empty.
    have hempty : badImmCharts (n := 0) (k := k) f p = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.2
      rintro u ⟨i, y, hy, w, hw⟩
      have hw0 : w = 0 := by
        ext i
        exact Fin.elim0 i
      rw [hw0] at hw
      simp only [map_zero] at hw
      exact (vVec_ne_zero u) hw.symm
    rw [hempty, dimH_empty]
    norm_num
  · -- `n = m + 1`: every bad direction is `extract (D_y (dirVec j t))` for some `j`, `y`, `t`,
    -- and `(y, t)` ranges over the `(m+1) + m = 2n - 1` dimensional space
    -- `ℝ^{m+1} × (Fin m → ℝ)`.
    calc dimH (badImmCharts (n := m + 1) (k := k) f p)
        ≤ dimH (⋃ i, ⋃ j : Fin (m + 1),
            sharpParam (k := k) f (p i) j '' sharpDom (k := k) f (p i) j) :=
          dimH_mono (badImmCharts_subset_sharpParam_smooth (k := k) f p)
      _ = ⨆ i, ⨆ j : Fin (m + 1),
            dimH (sharpParam (k := k) f (p i) j '' sharpDom (k := k) f (p i) j) := by
          simp only [dimH_iUnion]
      _ ≤ 2 * (↑(m + 1)) - 1 := by
          refine iSup_le fun i => iSup_le fun j => ?_
          calc dimH (sharpParam (k := k) f (p i) j '' sharpDom (k := k) f (p i) j)
              ≤ Module.finrank ℝ (EuclideanSpace ℝ (Fin (m + 1)) × (Fin m → ℝ)) :=
                dimH_image_le_of_contDiffOn (isOpen_sharpDom_smooth f hf (p i) j)
                  (contDiffOn_sharpParam_smooth f hf (p i) j) (Set.Subset.refl _)
            _ = (↑((m + 1) + m) : ℝ≥0∞) := by
                rw [Module.finrank_prod, finrank_euclideanSpace, Module.finrank_fin_fun,
                  Fintype.card_fin]
            _ = 2 * (↑(m + 1)) - 1 := by
                rw [two_mul_sub_one_cast]
                congr 1
                omega

end Work.Projection
