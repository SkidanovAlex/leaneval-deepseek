import Mathlib
import Submission.Work.Drive.Mono.CylRegionDefs
import Submission.Work.Drive.Mono.interior_cReg_cCyl_eq_cInt

/-!
# The interior of the closed cylindrical region

For a plane set `S` and functions `α β` continuous on `S`, the interior of the closed cylindrical
region `cCyl S α β` is the *interior cylindrical region* `cInt S α β`: the points whose projection
lies in `interior S` and whose third coordinate lies strictly between `α` and `β` of the
projection.

This is the target `Work.Drive.Mono.FiberModel.interior_cCyl_of_continuousOn`.  Note that it needs
*none* of the disc-parametrisation hypotheses and no strict inequality `α < β` on `S`: only
continuity of `α` and `β` on `S`.

Both inclusions are proved directly:

* `cInt S α β ⊆ interior (cCyl S α β)` — continuity: around a point of `cInt`, a whole ball stays
  in the open region `cReg ⊆ cCyl`;
* `interior (cCyl S α β) ⊆ cInt S α β` — perturbation: a point with `clast p ≤ α (cproj p)`, or
  `β (cproj p) ≤ clast p`, or `cproj p ∉ interior S`, has neighbours outside `cCyl`.
-/

namespace Work.Drive.Mono.FiberModel

open Work.Drive.Mono

open Set

noncomputable section

/-! ## Elementary metric facts about `cproj`, `clast` and `cmk` -/

private theorem priv_norm_cmk_zero_snd (x : EuclideanSpace ℝ (Fin 2)) : ‖cmk x 0‖ = ‖x‖ := by
  have h : ‖cmk x 0‖ ^ 2 = ‖x‖ ^ 2 := by
    rw [norm_sq_cmk]; ring
  calc ‖cmk x 0‖ = Real.sqrt (‖cmk x 0‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
    _ = Real.sqrt (‖x‖ ^ 2) := by rw [h]
    _ = ‖x‖ := Real.sqrt_sq (norm_nonneg _)

private theorem priv_norm_cmk_zero_fst (t : ℝ) :
    ‖cmk (0 : EuclideanSpace ℝ (Fin 2)) t‖ = |t| := by
  have h : ‖cmk (0 : EuclideanSpace ℝ (Fin 2)) t‖ ^ 2 = t ^ 2 := by
    rw [norm_sq_cmk]; simp
  calc ‖cmk (0 : EuclideanSpace ℝ (Fin 2)) t‖
      = Real.sqrt (‖cmk (0 : EuclideanSpace ℝ (Fin 2)) t‖ ^ 2) :=
        (Real.sqrt_sq (norm_nonneg _)).symm
    _ = Real.sqrt (t ^ 2) := by rw [h]
    _ = |t| := Real.sqrt_sq_eq_abs t

/-- Shifting the projection alone changes the distance in the projection only. -/
private theorem priv_dist_cmk_cproj (p : EuclideanSpace ℝ (Fin 3))
    (x : EuclideanSpace ℝ (Fin 2)) : dist (cmk x (clast p)) p = dist x (cproj p) := by
  rw [dist_eq_norm, dist_eq_norm]
  have h : cmk x (clast p) - p = cmk (x - cproj p) 0 := by
    rw [← cmk_cproj_clast p, cmk_sub]; simp
  rw [h, priv_norm_cmk_zero_snd]

/-- Shifting the third coordinate alone changes the distance by that shift. -/
private theorem priv_dist_cmk_clast (p : EuclideanSpace ℝ (Fin 3)) (y : ℝ) :
    dist (cmk (cproj p) y) p = |y - clast p| := by
  rw [dist_eq_norm]
  have h : cmk (cproj p) y - p = cmk (0 : EuclideanSpace ℝ (Fin 2)) (y - clast p) := by
    rw [← cmk_cproj_clast p, cmk_sub]; simp
  rw [h, priv_norm_cmk_zero_fst]

private theorem priv_dist_cproj_coord_le (p q : EuclideanSpace ℝ (Fin 3)) :
    dist (cproj p) (cproj q) ≤ dist p q := by
  rw [dist_eq_norm, dist_eq_norm, ← cproj_sub]
  exact norm_cproj_le _

private theorem priv_dist_clast_le (p q : EuclideanSpace ℝ (Fin 3)) :
    dist (clast p) (clast q) ≤ dist p q := by
  rw [Real.dist_eq, dist_eq_norm, ← clast_sub]
  exact abs_clast_le _

/-! ## Perturbation lemmas: points on the boundary of the cylinder are not interior -/

/-- If `clast p ≤ α (cproj p)` then `p` is not in the interior of `cCyl S α β`: every ball around
`p` contains a point with the same projection and a slightly smaller third coordinate. -/
private theorem priv_not_mem_interior_cCyl_of_alpha_ge
    {S : Set (EuclideanSpace ℝ (Fin 2))} {α β : EuclideanSpace ℝ (Fin 2) → ℝ}
    {p : EuclideanSpace ℝ (Fin 3)} (h : clast p ≤ α (cproj p)) :
    p ∉ interior (cCyl S α β) := by
  intro hp
  obtain ⟨ε, hε, hsub⟩ := Metric.mem_nhds_iff.mp (isOpen_interior.mem_nhds hp)
  set t := ε / 2 with ht
  have htpos : 0 < t := by rw [ht]; linarith
  have htlt : t < ε := by rw [ht]; linarith
  set q := cmk (cproj p) (clast p - t) with hq
  have hqball : q ∈ Metric.ball p ε := by
    rw [Metric.mem_ball]
    have hdist : dist q p = t := by
      rw [hq, priv_dist_cmk_clast]
      rw [show clast p - t - clast p = -t by ring, abs_neg, abs_of_pos htpos]
    rw [hdist]; exact htlt
  have hcyl : q ∈ cCyl S α β := interior_subset (hsub hqball)
  have h1 : α (cproj q) ≤ clast q := hcyl.2.1
  simp only [hq, cproj_cmk, clast_cmk] at h1
  linarith

/-- If `β (cproj p) ≤ clast p` then `p` is not in the interior of `cCyl S α β`: every ball around
`p` contains a point with the same projection and a slightly larger third coordinate. -/
private theorem priv_not_mem_interior_cCyl_of_beta_le
    {S : Set (EuclideanSpace ℝ (Fin 2))} {α β : EuclideanSpace ℝ (Fin 2) → ℝ}
    {p : EuclideanSpace ℝ (Fin 3)} (h : β (cproj p) ≤ clast p) :
    p ∉ interior (cCyl S α β) := by
  intro hp
  obtain ⟨ε, hε, hsub⟩ := Metric.mem_nhds_iff.mp (isOpen_interior.mem_nhds hp)
  set t := ε / 2 with ht
  have htpos : 0 < t := by rw [ht]; linarith
  have htlt : t < ε := by rw [ht]; linarith
  set q := cmk (cproj p) (clast p + t) with hq
  have hqball : q ∈ Metric.ball p ε := by
    rw [Metric.mem_ball]
    have hdist : dist q p = t := by
      rw [hq, priv_dist_cmk_clast]
      rw [show clast p + t - clast p = t by ring, abs_of_pos htpos]
    rw [hdist]; exact htlt
  have hcyl : q ∈ cCyl S α β := interior_subset (hsub hqball)
  have h1 : clast q ≤ β (cproj q) := hcyl.2.2
  simp only [hq, cproj_cmk, clast_cmk] at h1
  linarith

/-- A point of the interior of `cCyl S α β` projects into the interior of `S`: otherwise every ball
around `p` contains a point whose projection is near `cproj p` but outside `S`. -/
private theorem priv_cproj_mem_interior_of_mem_interior_cCyl
    {S : Set (EuclideanSpace ℝ (Fin 2))} {α β : EuclideanSpace ℝ (Fin 2) → ℝ}
    {p : EuclideanSpace ℝ (Fin 3)} (hp : p ∈ interior (cCyl S α β)) :
    cproj p ∈ interior S := by
  by_contra hx
  have hball_out : ∀ r > 0, ∃ x : EuclideanSpace ℝ (Fin 2), ‖x - cproj p‖ < r ∧ x ∉ S := by
    intro r hr
    by_contra h
    push Not at h
    have hsub : Metric.ball (cproj p) r ⊆ S := by
      intro x hxm
      rw [Metric.mem_ball] at hxm
      rw [dist_eq_norm] at hxm
      exact h x hxm
    exact hx (mem_interior_iff_mem_nhds.mpr
      (Filter.mem_of_superset (Metric.ball_mem_nhds _ hr) hsub))
  obtain ⟨ε, hε, hsub⟩ := Metric.mem_nhds_iff.mp (isOpen_interior.mem_nhds hp)
  obtain ⟨x, hxr, hxS⟩ := hball_out ε hε
  set q := cmk x (clast p) with hq
  have hqball : q ∈ Metric.ball p ε := by
    rw [Metric.mem_ball, hq, priv_dist_cmk_cproj, dist_eq_norm]
    exact hxr
  have hcyl : q ∈ cCyl S α β := interior_subset (hsub hqball)
  have : cproj q ∈ S := hcyl.1
  rw [hq, cproj_cmk] at this
  exact hxS this

/-- The interior of the closed cylindrical region is contained in the interior region. -/
private theorem priv_interior_cCyl_subset_cInt
    {S : Set (EuclideanSpace ℝ (Fin 2))} {α β : EuclideanSpace ℝ (Fin 2) → ℝ} :
    interior (cCyl S α β) ⊆ cInt S α β := by
  intro p hp
  refine ⟨priv_cproj_mem_interior_of_mem_interior_cCyl hp, ?_, ?_⟩
  · by_contra hcon
    exact priv_not_mem_interior_cCyl_of_alpha_ge (not_lt.mp hcon) hp
  · by_contra hcon
    exact priv_not_mem_interior_cCyl_of_beta_le (not_lt.mp hcon) hp

/-! ## The interior region is contained in the interior of the open cylindrical region -/

/-- Continuity of `α` and `β` on `S`: near a point of `cInt` a whole ball stays in `cReg`. -/
private theorem priv_cInt_subset_interior_cReg
    {S : Set (EuclideanSpace ℝ (Fin 2))} {α β : EuclideanSpace ℝ (Fin 2) → ℝ}
    (hα : ContinuousOn α S) (hβ : ContinuousOn β S) :
    cInt S α β ⊆ interior (cReg S α β) := by
  intro p hp
  obtain ⟨hxS, h1, h2⟩ := hp
  have hnhdsS : interior S ∈ nhds (cproj p) := isOpen_interior.mem_nhds hxS
  obtain ⟨r, hr, hrS⟩ := Metric.mem_nhds_iff.mp hnhdsS
  have hcα : ContinuousAt α (cproj p) := (hα.mono interior_subset).continuousAt hnhdsS
  have hcβ : ContinuousAt β (cproj p) := (hβ.mono interior_subset).continuousAt hnhdsS
  set ρ := min (clast p - α (cproj p)) (β (cproj p) - clast p) / 2 with hρdef
  have hρpos : 0 < ρ := by
    rw [hρdef]
    exact div_pos (lt_min (by linarith) (by linarith)) (by norm_num)
  have hρ1 : ρ ≤ (clast p - α (cproj p)) / 2 := by
    rw [hρdef]; exact div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num)
  have hρ2 : ρ ≤ (β (cproj p) - clast p) / 2 := by
    rw [hρdef]; exact div_le_div_of_nonneg_right (min_le_right _ _) (by norm_num)
  obtain ⟨δα, hδαpos, hδα⟩ := Metric.continuousAt_iff.mp hcα ρ hρpos
  obtain ⟨δβ, hδβpos, hδβ⟩ := Metric.continuousAt_iff.mp hcβ ρ hρpos
  set δ := min (min r ρ) (min δα δβ) with hδdef
  have hδpos : 0 < δ := by
    rw [hδdef]; exact lt_min (lt_min hr hρpos) (lt_min hδαpos hδβpos)
  refine mem_interior_iff_mem_nhds.mpr (Metric.mem_nhds_iff.mpr ⟨δ, hδpos, ?_⟩)
  intro q hq
  rw [Metric.mem_ball] at hq
  have hδr : δ ≤ r := le_trans (min_le_left _ _) (min_le_left _ _)
  have hδρ : δ ≤ ρ := le_trans (min_le_left _ _) (min_le_right _ _)
  have hδδα : δ ≤ δα := le_trans (min_le_right _ _) (min_le_left _ _)
  have hδδβ : δ ≤ δβ := le_trans (min_le_right _ _) (min_le_right _ _)
  have hcq : dist (cproj q) (cproj p) ≤ dist q p := priv_dist_cproj_coord_le q p
  have hqS : cproj q ∈ S :=
    interior_subset (hrS (by
      rw [Metric.mem_ball]
      exact lt_of_le_of_lt hcq (lt_of_lt_of_le hq hδr)))
  have hαq : dist (α (cproj q)) (α (cproj p)) < ρ :=
    hδα (lt_of_le_of_lt hcq (lt_of_lt_of_le hq hδδα))
  have hβq : dist (β (cproj q)) (β (cproj p)) < ρ :=
    hδβ (lt_of_le_of_lt hcq (lt_of_lt_of_le hq hδδβ))
  rw [Real.dist_eq] at hαq hβq
  have hcl : |clast q - clast p| < ρ := by
    have h := priv_dist_clast_le q p
    rw [Real.dist_eq] at h
    exact lt_of_le_of_lt h (lt_of_lt_of_le hq hδρ)
  have hcl1 : clast p - ρ < clast q := by have := (abs_lt.mp hcl).1; linarith
  have hcl2 : clast q < clast p + ρ := by have := (abs_lt.mp hcl).2; linarith
  refine ⟨hqS, ?_, ?_⟩
  · have h := (abs_lt.mp hαq).2
    linarith
  · have h := (abs_lt.mp hβq).1
    linarith

/-! ## The target -/

theorem interior_cCyl_of_continuousOn {S : Set (EuclideanSpace ℝ (Fin 2))}
    {α β : EuclideanSpace ℝ (Fin 2) → ℝ} (hα : ContinuousOn α S) (hβ : ContinuousOn β S) :
    interior (Work.Drive.Mono.cCyl S α β) = Work.Drive.Mono.cInt S α β := by
  have h1 : cInt S α β ⊆ interior (cCyl S α β) :=
    (priv_cInt_subset_interior_cReg hα hβ).trans
      (interior_mono fun p hp => ⟨hp.1, le_of_lt hp.2.1, le_of_lt hp.2.2⟩)
  exact Subset.antisymm priv_interior_cCyl_subset_cInt h1

end

end Work.Drive.Mono.FiberModel
