import Mathlib
import Submission.Work.Surf.defs
import Submission.Work.Surf.tame_cut_parity
import Submission.Work.Surf.smooth_cut_parity
import Submission.Work.Surf.smooth_reduction_alt

namespace Work.Surf

open Set

noncomputable section

/-! ## Elementary facts about the ray-meet set and the square

The ray-meet set `rayMeet F v = {x | ∃ r > 0, F x = r • v}` depends only on the *ray* of `v`, so it
is unchanged when `v` is replaced by a positive multiple; and the unit square is compact, so a
continuous map on it is bounded.  These two facts are what lets the smooth reduction above be fed to
`Work.Surf.smooth_cut_parity`, whose hypothesis `‖F x‖ < ‖v‖` is on the whole square. -/

/-- The ray-meet set only depends on the ray, not on the (positive) multiple of the direction. -/
lemma rayMeet_smul' {F : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2)}
    {v : EuclideanSpace ℝ (Fin 2)} {c : ℝ} (hc : 0 < c) :
    rayMeet F (c • v) = rayMeet F v := by
  ext x
  constructor
  · rintro ⟨r, hr, hrv⟩
    exact ⟨r * c, mul_pos hr hc, by rw [hrv, smul_smul]⟩
  · rintro ⟨r, hr, hrv⟩
    exact ⟨r / c, div_pos hr hc, by rw [hrv, smul_smul, div_mul_cancel₀ r (ne_of_gt hc)]⟩

/-- The unit square is compact. -/
lemma isCompact_sqBox' : IsCompact sqBox := by
  have h : sqBox = (PiLp.homeomorph 2 (fun _ : Fin 2 => ℝ)) ⁻¹'
      (Set.univ.pi fun _ : Fin 2 => Set.Icc (0 : ℝ) 1) := by
    ext x
    simp only [sqBox, Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_univ_pi]
    constructor
    · intro h i; fin_cases i
      · exact h.1
      · exact h.2
    · intro h; exact ⟨h 0, h 1⟩
  rw [h]
  exact (Homeomorph.isCompact_preimage _).mpr (isCompact_univ_pi fun _ => isCompact_Icc)

/-- A continuous map on the unit square is bounded by a positive constant. -/
lemma exists_bound_on_sqBox {F : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2)}
    (hF : Continuous F) : ∃ M : ℝ, 0 < M ∧ ∀ x ∈ sqBox, ‖F x‖ ≤ M := by
  obtain ⟨x₀, hx₀, hmax⟩ := isCompact_sqBox'.exists_isMaxOn
    (⟨0, by simp [sqBox]⟩ : sqBox.Nonempty) hF.continuousOn.norm
  refine ⟨‖F x₀‖ + 1, by positivity, fun x hx => ?_⟩
  have hle : ‖F x‖ ≤ ‖F x₀‖ := by simpa using hmax hx
  linarith

/-- The `ncard` of the boundary ray-meeting set is unchanged under rescaling the direction, since
the set itself is. -/
lemma ncard_rayMeet_smul {F : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2)}
    {v : EuclideanSpace ℝ (Fin 2)} {c : ℝ} (hc : 0 < c) :
    (rayMeet F (c • v) ∩ sqBdry : Set (EuclideanSpace ℝ (Fin 2))).ncard =
      (rayMeet F v ∩ sqBdry : Set (EuclideanSpace ℝ (Fin 2))).ncard := by
  rw [rayMeet_smul' hc]

/-! ## The mod-2 degree theorem (cut/ray form) -/

/-- **The mod-2 degree theorem (cut/ray form).**  Let `F : ℝ² → ℝ²` be `C¹` on the plane, nowhere
zero on the boundary of the unit square `Work.Surf.sqBox = [0,1]²`, with every zero in the square a
regular point (surjective derivative), and suppose that the boundary crossings of the ray
`{r • v : 0 < r}` occur in the *interior* of a face of the square (not at a corner), finitely many,
and transversally, i.e. at such a boundary point `x` the derivative of `F` in the direction along the
face containing `x` is not parallel to `v`.  Then the number of zeros of `F` in the square and the
number of boundary points at which `F` takes a value on the ray have the same parity.

(The hypothesis `hcorner` is needed: without it, at a corner both face directions can be transverse to
`v` while the boundary curve only *touches* the ray there — e.g. `F x = (1 + x₀x₁, x₀ + x₁)`, `v =
(1,0)`, where the only boundary ray-meeting is the corner `0` and the counts are `0` and `1`.  The
interior transversality `fderiv` surjective at ray-points is *not* assumed; the interior count is
handled by degree theory.  `hbig` is a harmless normalisation, mirroring
`Work.Surf.even_ncard_zeros_add_bdyRay`; it can always be achieved by rescaling `v`.) -/
theorem even_ncard_zeros_add_boundary_ray
    (F : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2))
    (hF : ContDiff ℝ 1 F)
    (hbdry : ∀ x ∈ Work.Surf.sqBdry, F x ≠ 0)
    (hreg : ∀ x ∈ Work.Surf.sqBox, F x = 0 → Function.Surjective (fderiv ℝ F x))
    {v : EuclideanSpace ℝ (Fin 2)} (hv : v ≠ 0)
    (hbig : ∀ x ∈ Work.Surf.sqBdry, ‖F x‖ < ‖v‖)
    (hcorner : ∀ x ∈ Work.Surf.sqBdry, (∃ r : ℝ, 0 < r ∧ F x = r • v) →
      ¬ ((x 0 = 0 ∨ x 0 = 1) ∧ (x 1 = 0 ∨ x 1 = 1)))
    (htrans_bdry : ∀ x ∈ Work.Surf.sqBdry, (∃ r : ℝ, 0 < r ∧ F x = r • v) →
      ((x 1 = 0 ∨ x 1 = 1) →
        Work.Drive.det2 (fderiv ℝ F x (EuclideanSpace.single 0 1)) v ≠ 0) ∧
      ((x 0 = 0 ∨ x 0 = 1) →
        Work.Drive.det2 (fderiv ℝ F x (EuclideanSpace.single 1 1)) v ≠ 0))
    (hfin : (Work.Surf.rayMeet F v ∩ Work.Surf.sqBdry).Finite) :
    Even (({x ∈ Work.Surf.sqBox | F x = 0} : Set (EuclideanSpace ℝ (Fin 2))).ncard +
      (Work.Surf.rayMeet F v ∩ Work.Surf.sqBdry : Set (EuclideanSpace ℝ (Fin 2))).ncard) := by
  -- Step 1: approximate `F` by a smooth map with the same two counts and the same hypotheses.
  obtain ⟨F', hF'sm, hbdry', hreg', hbig', hcorner', htrans', hfin', hZ, hR⟩ :=
    smooth_reduction_alt F hF hbdry hreg hv hbig hcorner htrans_bdry hfin
  -- Step 2: rescale `v` so that the bound holds on the whole square.
  obtain ⟨M, hMpos, hM⟩ := exists_bound_on_sqBox hF'sm.continuous
  set c : ℝ := (M + 1) / ‖v‖ with hcdef
  have hcpos : 0 < c := div_pos (by linarith) (norm_pos_iff.mpr hv)
  have hcne : c ≠ 0 := ne_of_gt hcpos
  have hv'ne : c • v ≠ 0 := smul_ne_zero hcne hv
  have hnorm : ‖c • v‖ = M + 1 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hcpos, hcdef]
    field_simp
  have hbig'' : ∀ x ∈ Work.Surf.sqBox, ‖F' x‖ < ‖c • v‖ := by
    intro x hx
    rw [hnorm]
    linarith [hM x hx]
  -- the ray condition is unchanged by the rescaling
  have hraycond : ∀ x : EuclideanSpace ℝ (Fin 2),
      (∃ r : ℝ, 0 < r ∧ F' x = r • (c • v)) ↔ (∃ r : ℝ, 0 < r ∧ F' x = r • v) := by
    intro x
    constructor
    · rintro ⟨r, hr, hrv⟩
      exact ⟨r * c, mul_pos hr hcpos, by rw [hrv, smul_smul]⟩
    · rintro ⟨r, hr, hrv⟩
      exact ⟨r / c, div_pos hr hcpos, by rw [hrv, smul_smul, div_mul_cancel₀ r hcne]⟩
  have hcorner'' : ∀ x ∈ Work.Surf.sqBdry, (∃ r : ℝ, 0 < r ∧ F' x = r • (c • v)) →
      ¬ ((x 0 = 0 ∨ x 0 = 1) ∧ (x 1 = 0 ∨ x 1 = 1)) := by
    intro x hx hcon
    exact hcorner' x hx ((hraycond x).mp hcon)
  have htrans'' : ∀ x ∈ Work.Surf.sqBdry, (∃ r : ℝ, 0 < r ∧ F' x = r • (c • v)) →
      ((x 1 = 0 ∨ x 1 = 1) →
        Work.Drive.det2 (fderiv ℝ F' x (EuclideanSpace.single 0 1)) (c • v) ≠ 0) ∧
      ((x 0 = 0 ∨ x 0 = 1) →
        Work.Drive.det2 (fderiv ℝ F' x (EuclideanSpace.single 1 1)) (c • v) ≠ 0) := by
    intro x hx hcon
    obtain ⟨h1, h2⟩ := htrans' x hx ((hraycond x).mp hcon)
    refine ⟨fun hface => ?_, fun hface => ?_⟩
    · rw [Work.Drive.det2_smul_right]
      exact mul_ne_zero hcne (h1 hface)
    · rw [Work.Drive.det2_smul_right]
      exact mul_ne_zero hcne (h2 hface)
  have hfin'' : (Work.Surf.rayMeet F' (c • v) ∩ Work.Surf.sqBdry).Finite := by
    rw [rayMeet_smul' hcpos]
    exact hfin'
  -- Step 3: apply the smooth cut/ray parity theorem for the rescaled direction.
  have hmain := smooth_cut_parity F' hF'sm hbdry' hreg' hv'ne hbig'' hcorner'' htrans'' hfin''
  rw [rayMeet_smul' hcpos] at hmain
  rw [← hZ, ← hR] at hmain
  exact hmain

end

end Work.Surf
