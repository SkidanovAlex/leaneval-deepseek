import Mathlib
import Submission.Work.Drive.quadrisecantSpreadDefs
import Submission.Work.Drive.collapseResistanceDefs
import Submission.Work.Drive.separation_of_far_parameters
import Submission.Work.Drive.shortSecantsFree_of_noInflection
import Submission.Work.Drive.secantDiskAPI
import Submission.Work.Drive.quadrisecantConsecutive
import Submission.Work.Drive.isUnknotted_of_close
import Submission.Work.Drive.consecutive_interiorFree_of_noFiveCollinear
import Submission.Work.Drive.genericFullDefs

namespace Work.Drive

open LeanEval.KnotTheory.Quadrisecant
open scoped Topology

set_option maxHeartbeats 4000000

noncomputable section

/-! ## Auxiliary estimates -/

/-- A speed bound for a smooth knot (continuity + periodicity + compactness). -/
private lemma exists_velocity_bound {r : ℝ → Space} (hr : IsSmoothKnot r) :
    ∃ V : ℝ, ∀ t : ℝ, ‖velocity r t‖ ≤ V := by
  have hcont : Continuous (velocity r) := hr.smooth.continuous_deriv le_top
  obtain ⟨x, -, hmax⟩ := (isCompact_Icc.image hcont).exists_isMaxOn
    (f := fun y : Space => ‖y‖)
    ⟨velocity r 0, 0, ⟨le_rfl, period_pos.le⟩, rfl⟩ continuous_norm.continuousOn
  refine ⟨‖x‖, fun t => ?_⟩
  set k : ℤ := ⌊t / period⌋ with hk
  have hle : ((k : ℝ)) * period ≤ t := by
    have h := Int.floor_le (t / period)
    have h2 := mul_le_mul_of_nonneg_right h period_pos.le
    rw [div_mul_cancel₀ t (ne_of_gt period_pos)] at h2
    exact h2
  have hlt : t < (k : ℝ) * period + period := by
    have h := Int.lt_floor_add_one (t / period)
    have h2 := mul_lt_mul_of_pos_right h period_pos
    rw [div_mul_cancel₀ t (ne_of_gt period_pos), add_mul, one_mul] at h2
    linarith
  have hper : velocity r t = velocity r (t - (k : ℝ) * period) := by
    have hper' : Function.Periodic (velocity r) period := hr.velocity_periodic
    have h := hper'.zsmul k (t - (k : ℝ) * period)
    rw [zsmul_eq_mul] at h
    have h2 : t - (k : ℝ) * period + (k : ℝ) * period = t := by ring
    rw [h2] at h
    exact h
  rw [hper]
  exact hmax ⟨t - (k : ℝ) * period, ⟨by linarith, by linarith⟩, rfl⟩

/-- **Lipschitz bound for the knot map** on the parameter circle, from a speed bound. -/
private lemma knotMap_lipschitz {r : ℝ → Space} (hr : IsSmoothKnot r) {M : ℝ}
    (hM : ∀ t : ℝ, ‖velocity r t‖ ≤ M) :
    ∀ a b : AddCircle period, ‖knotMap r a - knotMap r b‖ ≤ M * dist a b := by
  intro a b
  obtain ⟨t, s, ht, hs, hts⟩ := exists_representatives_dist a b
  have h1 : knotMap r a = r t := by rw [← ht, knotMap_eq_r hr t]
  have h2 : knotMap r b = r s := by rw [← hs, knotMap_eq_r hr s]
  rw [h1, h2, hts.symm]
  exact norm_sub_le_of_velocity_bound hr.smooth hM s t

/-- For representatives in `[0, period)` the circular separation is the circle distance. -/
private lemma circSep_eq_dist {a b : AddCircle period} {t s : ℝ}
    (ht : (t : AddCircle period) = a) (hs : (s : AddCircle period) = b) :
    circSep t s = dist a b := by
  rw [circSep, ht, hs]

end

open LeanEval.KnotTheory.Quadrisecant

/-- **The strengthened bookkeeping (Kuperberg §6).**  As `SpreadQuadrisecantNoFiveClose`, but the
approximants are additionally required to be in *tangent-chord general position*
(`Work.Drive.TangentChordGP`) and to have a finite meridian trace
(`Work.Drive.FiniteMeridianFibre`) — the two hypotheses that the corrected crux (brick (d′) + the
Layer-B sweep pin, `Work.Drive.OPrimeSweepFamily`) carries. -/
def SpreadQuadrisecantFullCloseK_v2 : Prop :=
  ∀ r : ℝ → Space, IsSmoothKnot r → ¬ IsUnknotted r →
    ∃ δ : ℝ, 0 < δ ∧ ∃ ε : ℝ, 0 < ε ∧
      ∀ r' : ℝ → Space, IsSmoothKnot r' → TorusGeneralPositionTransverse r' →
        (∀ t : ℝ, LinearIndependent ℝ ![deriv r' t, deriv (deriv r') t]) →
        NoFiveCollinear r' → TangentChordGP r' → FiniteMeridianFibre r' →
        QuadrisecantIsolated r' →
        (∀ t : ℝ, ‖r' t - r t‖ < ε ∧ ‖velocity r' t - velocity r t‖ < ε ∧
          ‖deriv (deriv r') t - deriv (deriv r) t‖ < ε) →
        ∃ a b z w : ℝ, SpreadQuad δ a b z w ∧
          IsMiddleOnChord r' (a : KnotParam) (b : KnotParam) (z : KnotParam) ∧
          IsMiddleOnChord r' (a : KnotParam) (b : KnotParam) (w : KnotParam)

/-- **The bookkeeping of the generic reduction (Kuperberg §6).**  Granting the non-trivial
quadrisecant of a generic approximant and the collapse resistance, the four parameters of the
quadrisecant are uniformly separated — provided the approximant has no five collinear points, which
is what makes the consecutive sub-secants interior-free. -/
theorem spreadBookkeepingFullK_v2
    (hnq : ∀ r : ℝ → Space, IsSmoothKnot r → TorusGeneralPositionTransverse r →
      (∀ t : ℝ, LinearIndependent ℝ ![deriv r t, deriv (deriv r) t]) →
      TangentChordGP r → FiniteMeridianFibre r → NoFiveCollinear r → QuadrisecantIsolated r →
      ¬ IsUnknotted r →
      ∃ a b z w : AddCircle period, QuadDistinct a b z w ∧
        IsMiddleOnChord r a b z ∧ IsMiddleOnChord r a b w ∧
        NontrivialSecant r a b ∧ NontrivialSecant r a z ∧ NontrivialSecant r a w ∧
        NontrivialSecant r z w ∧ NontrivialSecant r z b ∧ NontrivialSecant r w b)
    (hcr : CollapseResistance) : SpreadQuadrisecantFullCloseK_v2 := by
  intro r hr hnu
  obtain ⟨εu, hεupos, hu⟩ := isUnknotted_of_close hr
  obtain ⟨εs, hεspos, hs⟩ := separation_of_far_parameters hr
  obtain ⟨εc, hεcpos, δc, hδcpos, hcr'⟩ := hcr r hr
  obtain ⟨V, hV⟩ := exists_velocity_bound hr
  set M : ℝ := max 1 (V + 1) with hMdef
  have hM1 : 1 ≤ M := le_max_left _ _
  have hMpos : 0 < M := lt_of_lt_of_le zero_lt_one hM1
  set ε₀ : ℝ := min εu (min εs (min εc 1)) with hε₀
  have hε₀pos : 0 < ε₀ := by
    simp only [hε₀]; positivity
  have hε₀u : ε₀ ≤ εu := by simp only [hε₀]; exact min_le_left _ _
  have hε₀s : ε₀ ≤ εs := by
    simp only [hε₀]; exact le_trans (min_le_right _ _) (min_le_left _ _)
  have hε₀c : ε₀ ≤ εc := by
    simp only [hε₀]
    exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _))
  have hε₀1 : ε₀ ≤ 1 := by
    simp only [hε₀]
    exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _))
  have hηpos : 0 < δc / M := by positivity
  obtain ⟨δsp, hδsppos, hδsp⟩ := hs (δc / M) hηpos
  refine ⟨min (δc / M) (2 * δsp / M), by positivity, ε₀, hε₀pos, ?_⟩
  intro r' hr' hg hinfl hn5 htc' hfib' hqi hclose
  have hcl : ∀ t : ℝ, ‖r' t - r t‖ < ε₀ ∧ ‖velocity r' t - velocity r t‖ < ε₀ :=
    fun t => ⟨(hclose t).1, (hclose t).2.1⟩
  have hcl_u : ∀ t : ℝ, ‖r' t - r t‖ < εu ∧ ‖velocity r' t - velocity r t‖ < εu :=
    fun t => ⟨lt_of_lt_of_le (hcl t).1 hε₀u, lt_of_lt_of_le (hcl t).2 hε₀u⟩
  have hcl_s : ∀ t : ℝ, ‖r' t - r t‖ < εs ∧ ‖velocity r' t - velocity r t‖ < εs :=
    fun t => ⟨lt_of_lt_of_le (hcl t).1 hε₀s, lt_of_lt_of_le (hcl t).2 hε₀s⟩
  have hcl_c : ∀ t : ℝ, ‖r' t - r t‖ < εc ∧ ‖velocity r' t - velocity r t‖ < εc :=
    fun t => ⟨lt_of_lt_of_le (hcl t).1 hε₀c, lt_of_lt_of_le (hcl t).2 hε₀c⟩
  have hcl_1 : ∀ t : ℝ, ‖r' t - r t‖ < 1 ∧ ‖velocity r' t - velocity r t‖ < 1 :=
    fun t => ⟨lt_of_lt_of_le (hcl t).1 hε₀1, lt_of_lt_of_le (hcl t).2 hε₀1⟩
  have hnu' : ¬ IsUnknotted r' := fun hun => hnu (hu r' hr' hcl_u hun)
  obtain ⟨A, B, Z, W, hd, hz, hw, hnt⟩ := hnq r' hr' hg hinfl htc' hfib' hn5 hqi hnu'
  obtain ⟨hntAB, hntAZ, hntAW, hntZW, hntZB, hntWB⟩ := hnt
  obtain ⟨hAB, hAZ, hAW, hBZ, hBW, hZW⟩ := hd
  -- Lipschitz bound
  have hMbound : ∀ t : ℝ, ‖velocity r' t‖ ≤ M := by
    intro t
    calc ‖velocity r' t‖ = ‖velocity r t + (velocity r' t - velocity r t)‖ := by
          rw [add_sub_cancel]
      _ ≤ ‖velocity r t‖ + ‖velocity r' t - velocity r t‖ := norm_add_le _ _
      _ ≤ V + 1 := by linarith [hV t, (hcl_1 t).2]
      _ ≤ M := le_max_right _ _
  have hLip : ∀ a b : AddCircle period, ‖knotMap r' a - knotMap r' b‖ ≤ M * dist a b :=
    knotMap_lipschitz hr' hMbound
  -- a non-trivial interior-free secant is far
  have hkey : ∀ P Q : AddCircle period, NontrivialSecant r' P Q → ChordInteriorFree r' P Q →
      δc / M ≤ dist P Q := by
    intro P Q hntPQ hif
    by_contra hlt
    have hlt' : dist P Q < δc / M := lt_of_not_ge hlt
    have h1 : ‖knotMap r' P - knotMap r' Q‖ < δc := by
      calc ‖knotMap r' P - knotMap r' Q‖ ≤ M * dist P Q := hLip P Q
        _ < M * (δc / M) := mul_lt_mul_of_pos_left hlt' hMpos
        _ = δc := by field_simp
    have h2 : dist P Q < δc := by
      have hle : δc / M ≤ δc := by
        rw [div_le_iff₀ hMpos]; nlinarith [hδcpos, hM1]
      exact lt_of_lt_of_le hlt' hle
    exact hntPQ (hcr' r' hr' hcl_c P Q h2 h1 hif)
  have hIF := consecutive_interiorFree_of_noFiveCollinear hr' hn5
    ⟨hAB, hAZ, hAW, hBZ, hBW, hZW⟩ hz hw
  -- a distance lower bound for the "long" pairs, from collinearity
  have longbound : ∀ {P Q R : AddCircle period}, IsMiddleOnChord r' P Q R →
      dist (knotMap r' P) (knotMap r' Q) = dist (knotMap r' P) (knotMap r' R)
        + dist (knotMap r' R) (knotMap r' Q) := by
    intro P Q R hmid
    have hseg : knotMap r' R ∈ segment ℝ (knotMap r' P) (knotMap r' Q) :=
      openSegment_subset_segment ℝ _ _ (by simpa [IsMiddleOnChord, IsMiddleOnOpenChord] using hmid)
    exact ((dist_add_dist_eq_iff).mpr (mem_segment_iff_wbtw.mp hseg)).symm
  have hshort : ∀ {P Q : AddCircle period}, δc / M ≤ dist P Q →
      min (δc / M) (2 * δsp / M) ≤ dist P Q :=
    fun h => le_trans (min_le_left _ _) h
  have hlong : ∀ {P Q : AddCircle period}, 2 * δsp / M ≤ dist P Q →
      min (δc / M) (2 * δsp / M) ≤ dist P Q :=
    fun h => le_trans (min_le_right _ _) h
  have hlongsp : ∀ {P Q : AddCircle period}, 2 * δsp ≤ dist (knotMap r' P) (knotMap r' Q) →
      2 * δsp / M ≤ dist P Q := by
    intro P Q hsp
    by_contra hlt
    have hlt' : dist P Q < 2 * δsp / M := lt_of_not_ge hlt
    have : dist (knotMap r' P) (knotMap r' Q) < 2 * δsp := by
      calc dist (knotMap r' P) (knotMap r' Q) ≤ M * dist P Q := hLip P Q
        _ < M * (2 * δsp / M) := mul_lt_mul_of_pos_left hlt' hMpos
        _ = 2 * δsp := by field_simp
    linarith
  -- extract the four real representatives
  obtain ⟨a, ha_mem, ha⟩ := AddCircle.eq_coe_Ico A
  obtain ⟨b, hb_mem, hb⟩ := AddCircle.eq_coe_Ico B
  obtain ⟨z, hz_mem, hzc⟩ := AddCircle.eq_coe_Ico Z
  obtain ⟨w, hw_mem, hwc⟩ := AddCircle.eq_coe_Ico W
  have hzwne : Z ≠ W := hZW
  have hspread :
      min (δc / M) (2 * δsp / M) ≤ dist A B → min (δc / M) (2 * δsp / M) ≤ dist A Z →
      min (δc / M) (2 * δsp / M) ≤ dist A W → min (δc / M) (2 * δsp / M) ≤ dist B Z →
      min (δc / M) (2 * δsp / M) ≤ dist B W → min (δc / M) (2 * δsp / M) ≤ dist Z W →
      SpreadQuad (min (δc / M) (2 * δsp / M)) a b z w := by
    intro hAB hAZ hAW hBZ hBW hZW
    refine ⟨ha_mem, hb_mem, hz_mem, hw_mem, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [circSep_eq_dist ha hb]; exact hAB
    · rw [circSep_eq_dist ha hzc]; exact hAZ
    · rw [circSep_eq_dist ha hwc]; exact hAW
    · rw [circSep_eq_dist hb hzc]; exact hBZ
    · rw [circSep_eq_dist hb hwc]; exact hBW
    · rw [circSep_eq_dist hzc hwc]; exact hZW
  have hmidA : IsMiddleOnChord r' (a : KnotParam) (b : KnotParam) (z : KnotParam) := by
    rw [ha, hb, hzc]; exact hz
  have hmidB : IsMiddleOnChord r' (a : KnotParam) (b : KnotParam) (w : KnotParam) := by
    rw [ha, hb, hwc]; exact hw
  rcases middle_dichotomy hr' hz hw hZW with hord | hord
  · -- the order is A, W, Z, B
    have hif : ChordInteriorFree r' A W ∧ ChordInteriorFree r' W Z ∧ ChordInteriorFree r' Z B := by
      rcases hIF with h | h
      · exact (h.1 W hord).elim
      · exact h
    have dAW := hkey A W hntAW hif.1
    have dWZ := hkey W Z ((NontrivialSecant_swap r' Z W).mp hntZW) hif.2.1
    have dZB := hkey Z B hntZB hif.2.2
    have sAW := hδsp r' hr' hcl_s A W dAW
    have sWZ := hδsp r' hr' hcl_s W Z dWZ
    have sZB := hδsp r' hr' hcl_s Z B dZB
    have addAZ := longbound hord
    have addWB := longbound (middle_transfer_left hz hord)
    have addAB := longbound hz
    have dAZ : 2 * δsp / M ≤ dist A Z := by
      apply hlongsp
      have h1 : δsp ≤ dist (knotMap r' A) (knotMap r' W) := by rw [dist_eq_norm]; exact sAW
      have h2 : δsp ≤ dist (knotMap r' W) (knotMap r' Z) := by rw [dist_eq_norm]; exact sWZ
      rw [addAZ]; linarith [h1, h2]
    have dWB : 2 * δsp / M ≤ dist W B := by
      apply hlongsp
      have h1 : δsp ≤ dist (knotMap r' W) (knotMap r' Z) := by rw [dist_eq_norm]; exact sWZ
      have h2 : δsp ≤ dist (knotMap r' Z) (knotMap r' B) := by rw [dist_eq_norm]; exact sZB
      rw [addWB]; linarith [h1, h2]
    have dAB : 2 * δsp / M ≤ dist A B := by
      apply hlongsp
      have h1 : δsp ≤ dist (knotMap r' A) (knotMap r' W) := by rw [dist_eq_norm]; exact sAW
      have h2 : δsp ≤ dist (knotMap r' W) (knotMap r' Z) := by rw [dist_eq_norm]; exact sWZ
      have h3 : δsp ≤ dist (knotMap r' Z) (knotMap r' B) := by rw [dist_eq_norm]; exact sZB
      rw [addAB]; linarith [h1, h2, h3]
    exact ⟨a, b, z, w,
      hspread (hlong dAB) (hlong dAZ) (hshort dAW)
        (hshort ((dist_comm Z B) ▸ dZB)) (hlong ((dist_comm W B) ▸ dWB))
        (hshort ((dist_comm W Z) ▸ dWZ)),
      hmidA, hmidB⟩
  · -- the order is A, Z, W, B
    have hif : ChordInteriorFree r' A Z ∧ ChordInteriorFree r' Z W ∧ ChordInteriorFree r' W B := by
      rcases hIF with h | h
      · exact h
      · exact (h.1 Z hord).elim
    have dAZ := hkey A Z hntAZ hif.1
    have dZW := hkey Z W hntZW hif.2.1
    have dWB := hkey W B hntWB hif.2.2
    have sAZ := hδsp r' hr' hcl_s A Z dAZ
    have sZW := hδsp r' hr' hcl_s Z W dZW
    have sWB := hδsp r' hr' hcl_s W B dWB
    have addAW := longbound hord
    have addZB := longbound (middle_transfer_left (r := r') (a := A) (b := B) (z := W) (w := Z) hw hord)
    have addAB := longbound hw
    have dAW : 2 * δsp / M ≤ dist A W := by
      apply hlongsp
      have h1 : δsp ≤ dist (knotMap r' A) (knotMap r' Z) := by rw [dist_eq_norm]; exact sAZ
      have h2 : δsp ≤ dist (knotMap r' Z) (knotMap r' W) := by rw [dist_eq_norm]; exact sZW
      rw [addAW]; linarith [h1, h2]
    have dZB : 2 * δsp / M ≤ dist Z B := by
      apply hlongsp
      have h1 : δsp ≤ dist (knotMap r' Z) (knotMap r' W) := by rw [dist_eq_norm]; exact sZW
      have h2 : δsp ≤ dist (knotMap r' W) (knotMap r' B) := by rw [dist_eq_norm]; exact sWB
      rw [addZB]; linarith [h1, h2]
    have dAB : 2 * δsp / M ≤ dist A B := by
      apply hlongsp
      have h1 : δsp ≤ dist (knotMap r' A) (knotMap r' Z) := by rw [dist_eq_norm]; exact sAZ
      have h2 : δsp ≤ dist (knotMap r' Z) (knotMap r' W) := by rw [dist_eq_norm]; exact sZW
      have h3 : δsp ≤ dist (knotMap r' W) (knotMap r' B) := by rw [dist_eq_norm]; exact sWB
      rw [addAB]; linarith [h1, h2, h3]
    exact ⟨a, b, z, w,
      hspread (hlong dAB) (hshort dAZ) (hlong dAW)
        (hlong ((dist_comm Z B) ▸ dZB)) (hshort ((dist_comm W B) ▸ dWB)) (hshort dZW),
      hmidA, hmidB⟩

end Work.Drive
