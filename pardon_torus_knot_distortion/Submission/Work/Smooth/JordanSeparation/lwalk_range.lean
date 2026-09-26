import Mathlib
import Submission.Work.Smooth.JordanSeparation.lwalk_curve_defs
import Submission.Work.Smooth.JordanSeparation.lwalk_basic
import Submission.Work.Smooth.JordanSeparation.lwalk_curve_injOn

/-!
# The trace of a lattice walk: curve, polygon and edge set

`LWalk.curve W` (the `2π`-periodic curve obtained from `polyF`), `LWalk.polyF` (the parametrisation
by edge coordinate) and `LWalk.polyG` (the affine parametrisation of the edges) all have the same
image: the union of the unit lattice edges of the walk, together with the base point.  In
particular `Set.range W.curve = Set.range W.path` (`range_path` describes the latter).

This is the identification of the *trace* of the walk with its edge set, used everywhere in the
cut/peel argument (`_LWALK_PEEL_NOTES.md`, step 1).
-/

namespace Work.Smooth.JordanSeparation

open Set

noncomputable section

namespace LWalk

variable (W : LWalk)

/-! ### The clamping map `cl` and the behaviour of `polyG` -/

theorem cl_cl (u : ℝ) : W.cl (W.cl u) = W.cl u := by
  show max 0 (min (W.cl u) (W.n : ℝ)) = W.cl u
  rw [min_eq_left (W.cl_le u), max_eq_right (W.cl_nonneg u)]

theorem polyG_cl (u : ℝ) : W.polyG u = W.polyG (W.cl u) := by
  simp only [polyG, W.cl_cl u]

/-- `polyG` is constant `W.pt 0` at and below `0`. -/
theorem polyG_of_nonpos {u : ℝ} (hu : u ≤ 0) : W.polyG u = W.pt 0 := by
  have hcl : W.cl u = 0 := by
    refine le_antisymm ?_ (W.cl_nonneg u)
    show max 0 (min u (W.n : ℝ)) ≤ 0
    exact max_le le_rfl (le_trans (min_le_left _ _) hu)
  rw [W.polyG_cl u, hcl, W.polyG_zero]

/-- `polyG` is constant `W.pt 0` at and above `W.n`. -/
theorem polyG_of_n_le {u : ℝ} (hu : (W.n : ℝ) ≤ u) : W.polyG u = W.pt 0 := by
  have hcl : W.cl u = (W.n : ℝ) := by
    refine le_antisymm (W.cl_le u) ?_
    show (W.n : ℝ) ≤ max 0 (min u (W.n : ℝ))
    exact le_trans (le_min hu le_rfl) (le_max_right _ _)
  rw [W.polyG_cl u, hcl, W.polyG_n]

/-! ### The image of `polyG` is the union of the edges -/

/-- Every value of `polyG` is on one of the edges of the walk. -/
theorem range_polyG_subset :
    Set.range W.polyG ⊆ (⋃ k, ⋃ (_ : k < W.n), Set.range (W.edge k)) ∪ {W.pt 0} := by
  rintro z ⟨u, rfl⟩
  have hcl : W.polyG u = W.polyG (W.cl u) := W.polyG_cl u
  rw [hcl]
  have hv0 : 0 ≤ W.cl u := W.cl_nonneg u
  have hvn : W.cl u ≤ (W.n : ℝ) := W.cl_le u
  rcases lt_or_eq_of_le hvn with hlt | heq
  · have hk : Nat.floor (W.cl u) < W.n := by
      have h : (Nat.floor (W.cl u) : ℝ) < (W.n : ℝ) :=
        lt_of_le_of_lt (Nat.floor_le hv0) hlt
      exact_mod_cast h
    have hvI : W.cl u ∈ Set.Icc ((Nat.floor (W.cl u) : ℝ)) ((Nat.floor (W.cl u) : ℝ) + 1) :=
      ⟨Nat.floor_le hv0, le_of_lt (Nat.lt_floor_add_one (W.cl u))⟩
    rw [W.polyG_eq_of_mem_Icc hk hvI]
    refine Or.inl (Set.mem_iUnion.mpr ⟨Nat.floor (W.cl u),
      Set.mem_iUnion.mpr ⟨hk, ?_⟩⟩)
    rw [LWalk.edge, segPath_range, segment_eq_image]
    refine ⟨W.cl u - (Nat.floor (W.cl u) : ℝ),
      ⟨by linarith [Nat.floor_le hv0], by linarith [Nat.lt_floor_add_one (W.cl u)]⟩, ?_⟩
    simp only [Complex.real_smul]
    push_cast
    ring
  · rw [heq, W.polyG_n]
    exact Or.inr rfl

/-- Conversely, every point of every edge is a value of `polyG`. -/
theorem subset_range_polyG :
    (⋃ k, ⋃ (_ : k < W.n), Set.range (W.edge k)) ∪ {W.pt 0} ⊆ Set.range W.polyG := by
  rintro z (hz | hz)
  · obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hz
    obtain ⟨hk', hzk'⟩ := Set.mem_iUnion.mp hk
    obtain ⟨s, hs⟩ := hzk'
    refine ⟨(k : ℝ) + (s : ℝ), ?_⟩
    rw [← hs]
    have hseg : W.edge k s = (1 - (s : ℝ)) • W.pt k + (s : ℝ) • W.pt (k + 1) := by
      show segPath (W.pt k) (W.pt (k + 1)) s = _
      simp only [segPath, Path.segment_apply]
      rw [AffineMap.lineMap_apply_module]
    rw [hseg]
    have hpoly : W.polyG ((k : ℝ) + (s : ℝ))
        = W.pt k + ((((k : ℝ) + (s : ℝ)) - (k : ℝ) : ℝ) : ℂ) * (W.pt (k + 1) - W.pt k) :=
      W.polyG_eq_of_mem_Icc hk' ⟨by linarith [s.2.1], by push_cast; linarith [s.2.2]⟩
    rw [hpoly, Complex.real_smul, Complex.real_smul]
    push_cast
    ring
  · rw [Set.mem_singleton_iff] at hz
    exact ⟨0, by rw [hz, W.polyG_zero]⟩

/-- **The image of `polyG` is the union of the edges together with the base point.** -/
theorem range_polyG_eq :
    Set.range W.polyG = (⋃ k, ⋃ (_ : k < W.n), Set.range (W.edge k)) ∪ {W.pt 0} :=
  Set.Subset.antisymm W.range_polyG_subset W.subset_range_polyG

/-- **The image of `polyG` is the trace of the walk.** -/
theorem range_polyG_eq_range_path : Set.range W.polyG = Set.range W.path := by
  rw [W.range_polyG_eq, W.range_path]

/-! ### The clamping is invisible to `polyF` -/

theorem min_clamp (s : ℝ) : min (max 0 (min s (2 * Real.pi))) (2 * Real.pi)
    = max 0 (min s (2 * Real.pi)) :=
  min_eq_left (max_le (by positivity) (min_le_right _ _))

theorem max_clamp (s : ℝ) :
    max 0 (max 0 (min s (2 * Real.pi))) = max 0 (min s (2 * Real.pi)) :=
  max_eq_right (le_max_left _ _)

theorem polyF_clamp (s : ℝ) :
    W.polyF s = W.polyF (max 0 (min s (2 * Real.pi))) := by
  simp only [polyF, min_clamp, max_clamp]

/-- **The image of `polyF` is the image of `polyG`.** -/
theorem range_polyF_eq : Set.range W.polyF = Set.range W.polyG := by
  refine Set.Subset.antisymm ?_ ?_
  · rintro z ⟨s, rfl⟩
    exact ⟨_, rfl⟩
  · rintro z ⟨u, rfl⟩
    rw [W.polyG_cl u]
    have hv0 : 0 ≤ W.cl u := W.cl_nonneg u
    have hvn : W.cl u ≤ (W.n : ℝ) := W.cl_le u
    rcases eq_or_lt_of_le hvn with heq | hlt
    · -- `W.cl u = W.n`: both sides are the base point
      refine ⟨0, ?_⟩
      have h1 : W.polyF 0 = W.polyG 0 := by
        simp only [polyF, min_eq_left (show (0:ℝ) ≤ 2 * Real.pi by positivity),
          max_eq_right le_rfl, mul_zero, zero_div]
      rw [h1, W.polyG_zero]
      exact (by rw [heq, W.polyG_n] : W.polyG (W.cl u) = W.pt 0).symm
    · have hnpos : (0 : ℝ) < (W.n : ℝ) := lt_of_le_of_lt hv0 hlt
      refine ⟨W.cl u * (2 * Real.pi) / (W.n : ℝ), ?_⟩
      have hs2 : W.cl u * (2 * Real.pi) / (W.n : ℝ) ≤ 2 * Real.pi := by
        rw [div_le_iff₀ hnpos]
        nlinarith [hvn, Real.pi_pos]
      have hs0 : (0 : ℝ) ≤ W.cl u * (2 * Real.pi) / (W.n : ℝ) := by positivity
      show W.polyF (W.cl u * (2 * Real.pi) / (W.n : ℝ)) = W.polyG (W.cl u)
      simp only [polyF, min_eq_left hs2, max_eq_right hs0]
      congr 1
      field_simp

/-! ### The curve and `polyF` -/

/-- The curve is the `liftIco` of `polyF`; its values are values of `polyF`. -/
theorem range_curve_subset_range_polyF : Set.range W.curve ⊆ Set.range W.polyF := by
  rintro z ⟨t, rfl⟩
  exact ⟨(↑((AddCircle.equivIco (2 * Real.pi) 0) (t : AddCircle (2 * Real.pi))) : ℝ), rfl⟩

/-- Every value of `polyF` is a value of the curve. -/
theorem polyF_mem_range_curve (s : ℝ) : W.polyF s ∈ Set.range W.curve := by
  set v := max 0 (min s (2 * Real.pi)) with hv
  have hv0 : 0 ≤ v := le_max_left _ _
  have hv2 : v ≤ 2 * Real.pi := max_le (by positivity) (min_le_right _ _)
  rcases lt_or_eq_of_le hv2 with hlt | heq
  · refine ⟨v, ?_⟩
    rw [W.polyF_clamp s, W.curve_eq_polyF ⟨hv0, hlt⟩]
  · refine ⟨2 * Real.pi, ?_⟩
    have h1 : W.polyF v = W.pt 0 := by
      rw [heq]
      show W.polyG ((W.n : ℝ) * max 0 (min (2 * Real.pi) (2 * Real.pi)) / (2 * Real.pi)) = W.pt 0
      rw [min_self, max_eq_right (show (0:ℝ) ≤ 2 * Real.pi by positivity),
        mul_div_cancel_right₀ _ (show (2 * Real.pi : ℝ) ≠ 0 by positivity)]
      exact W.polyG_n
    have h2 : W.curve (2 * Real.pi) = W.pt 0 := by
      rw [show (2 * Real.pi : ℝ) = 0 + 2 * Real.pi from by ring, W.periodic_curve 0,
        W.curve_eq_polyF ⟨le_refl 0, by positivity⟩, W.polyF_zero]
    rw [h2, ← h1, W.polyF_clamp s]

/-- **The trace of the walk is the trace of its curve.** -/
theorem range_curve_eq_range_path : Set.range W.curve = Set.range W.path := by
  refine Set.Subset.antisymm ?_ ?_
  · intro z hz
    have h1 : z ∈ Set.range W.polyF := W.range_curve_subset_range_polyF hz
    rw [W.range_polyF_eq] at h1
    rwa [W.range_polyG_eq_range_path] at h1
  · intro z hz
    rw [← W.range_polyG_eq_range_path] at hz
    rw [← W.range_polyF_eq] at hz
    obtain ⟨s, rfl⟩ := hz
    exact W.polyF_mem_range_curve s

/-- Consequence: the trace of the walk is contained in any set containing the walk. -/
theorem range_curve_subset_of_path {U : Set ℂ} (hval : ∀ t, W.path t ∈ U) :
    Set.range W.curve ⊆ U := by
  rw [W.range_curve_eq_range_path]
  rintro z ⟨t, rfl⟩
  exact hval t

end LWalk

end

end Work.Smooth.JordanSeparation
