/-
# Scale separation for the mandelbar endgame

Let `Mb` be the connectedness locus of the unicritical antiholomorphic family and `Φ` Nakane's
parameter Böttcher coordinate, subject to the abstract interface `NakaneData`
(`Submission/Work/Top/Defs.lean`).  Fix a Jordan-curve input `JordanForm`
(`Submission/Work/Top/Jordan.lean`), a point `c₀` of the parameter plane, a set `Nm` and angles
`a₁ a₂ θ ε`.

Every path `γ` in `Mb` from a point `p ∈ Mb` lying in the closure of the parameter ray of angle
`θ` to `1/4`, which lies in the closure of the ray of angle `0`, has to meet `Nm` arbitrarily
close to `c₀`.

The proof is the "pinch" argument of the endgame.  At the given scale `r'` the hypothesis `hX`
supplies a straight segment inside `Nm ∩ ball c₀ r'` carrying two points `e₁`, `e₂` off `Mb`
whose external angles are pinned in the windows around `a₁` and `a₂` (so that `β₁ < θ < β₂`).
Replacing `eⱼ` by the point `Eⱼ` where the potential is maximal on the part of the `βⱼ`-ray lying
on the segment, and choosing the level `R` above everything on the segment, the four pieces

`rayPiece β₁ (potential E₁) R ∪ eqArc β₁ β₂ R ∪ rayPiece β₂ (potential E₂) R ∪ segment E₂ E₁`

form a Jordan curve `J` (`Work.Top.pinch_curve_jordan`) whose intersection with `Mb` is contained
in the segment, hence in `Nm ∩ ball c₀ r'`.  The ray of angle `0` misses `J`, is connected and
unbounded, so it lies in the unbounded side `O` of `J`; as `1/4` lies in the closure of that ray
and not on `J`, it belongs to `O`.  The ray of angle `θ` crosses `J` exactly at the equipotential
point of level `R`; the part below level `R` misses `J`, is connected, and is pushed into the
bounded side `I` by the local two-sidedness of `J` at the crossing point
(`Sides.sides_of_halves`, with the cross box supplied by `Work.Top.exists_crossBox`).  Since `p`
lies in the closure of that part and not on `J`, it belongs to `I`.  Hence the path `γ` from
`p ∈ I` to `1/4 ∈ O` must meet `J`, and therefore `Nm ∩ ball c₀ r`.
-/
import Mathlib
import Submission.Work.Top.Defs
import Submission.Work.Top.Jordan
import Submission.Work.Top.pinch_curve_jordan
import Submission.Work.Top.exists_max_potential_on_segment_in_ray
import Submission.Work.Top.mem_paramRay_extAngle
import Submission.Work.Top.mem_eqArc_of
import Submission.Work.Top.isPreconnected_paramRay_lt
import Submission.Work.Top.isPreconnected_box_small
import Submission.Work.Top.isPreconnected_box_gt
import Submission.Work.Top.isPreconnected_gt_potential
import Submission.Work.Top.paramRay_unbounded
import Submission.Work.Top.rayPt_angle_continuous
import Submission.Work.Top.extAngle_of_mem_paramRay
import Submission.Work.Top.isOpen_crossBox
import Submission.Work.Top.isPreconnected_paramRay
import Submission.Work.Top.exists_crossBox

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Classical Filter Set
open scoped Topology

noncomputable section

set_option linter.unusedVariables false

namespace Work.Top

/-! ## Two parameter rays of different angles are disjoint -/

/-- Two parameter rays of angles in `[0,1)` which are different are disjoint: a common point
would be the point of both rays at the same level `‖Φ c‖ > 1`, and `rayPt` is injective in the
angle on `[0,1)`. -/
theorem paramRay_disjoint_of_ne {Mb : Set ℂ} {Φ : ℂ → ℂ} (hN : NakaneData Mb Φ)
    {θ α : ℝ} (hθ₀ : 0 ≤ θ) (hθ₁ : θ < 1) (hα₀ : 0 ≤ α) (hα₁ : α < 1) (hne : α ≠ θ) :
    Disjoint (NakaneData.paramRay hN θ) (NakaneData.paramRay hN α) := by
  rw [Set.disjoint_left]
  intro c hc hc'
  have h1 := (paramRay_rayPt_norm hN hc).1
  have h2 := (paramRay_rayPt_norm hN hc').1
  have hs : 1 < ‖Φ c‖ := hN.Phi_mem_exteriorDisc (NakaneData.paramRay_subset_compl hN θ hc)
  exact hne ((rayPt_injOn hN hα₀ hα₁ hθ₀ hθ₁ hs hs (by rw [← h2]; exact h1)).1)

/-! ## The main lemma -/

theorem scale_separation {Mb : Set ℂ} {Φ : ℂ → ℂ} (hN : Work.Top.NakaneData Mb Φ)
    (hJ : Work.Top.JordanForm) {c₀ : ℂ} {Nm : Set ℂ} {a₁ a₂ θ ε : ℝ}
    (hwin : 0 < a₁ - ε ∧ a₁ + ε < θ ∧ θ < a₂ - ε ∧ a₂ + ε < 1)
    (hθ : c₀ ∉ closure (Work.Top.NakaneData.paramRay hN θ))
    (hreal : (1/4 : ℂ) ∈ Mb ∧ (1/4 : ℂ) ∈ closure (Work.Top.NakaneData.paramRay hN 0) ∧
      c₀ ∉ closure (Work.Top.NakaneData.paramRay hN 0))
    (hX : ∀ r > 0, ∃ x y : ℂ, segment ℝ x y ⊆ Nm ∩ Metric.ball c₀ r ∧
        ∃ e₁ ∈ segment ℝ x y, ∃ e₂ ∈ segment ℝ x y, e₁ ∉ Mb ∧ e₂ ∉ Mb ∧
        Work.Top.NakaneData.extAngle Φ e₁ ∈ Set.Ioo (a₁ - ε) (a₁ + ε) ∧
        Work.Top.NakaneData.extAngle Φ e₂ ∈ Set.Ioo (a₂ - ε) (a₂ + ε))
    {p : ℂ} (hp : p ∈ Mb) (hpcl : p ∈ closure (Work.Top.NakaneData.paramRay hN θ))
    (hpq : p ≠ (1/4 : ℂ))
    {γ : C(unitInterval, ℂ)} (hγ0 : γ 0 = p) (hγ1 : γ 1 = (1/4 : ℂ))
    (hγmem : ∀ t, γ t ∈ Mb) {r : ℝ} (hr : 0 < r) (hrp : r < dist p c₀)
    (hrq : r < dist (1/4 : ℂ) c₀) :
    ∃ t, γ t ∈ Nm ∧ dist c₀ (γ t) < r := by
  obtain ⟨hwin1, hwin2, hwin3, hwin4⟩ := hwin
  obtain ⟨hquarter_mb, hquarter_cl, hc0_ray0⟩ := hreal
  -- ### Step 1: a scale `r' ≤ r` at which both rays avoid the disc of radius `r'` about `c₀`
  have hρθex : ∃ ρ : ℝ, 0 < ρ ∧ Metric.ball c₀ ρ ∩ Work.Top.NakaneData.paramRay hN θ = ∅ := by
    have hopen : IsOpen (closure (Work.Top.NakaneData.paramRay hN θ))ᶜ :=
      isClosed_closure.isOpen_compl
    obtain ⟨ρ, hρpos, hρsub⟩ := Metric.isOpen_iff.mp hopen c₀ hθ
    exact ⟨ρ, hρpos, Set.not_nonempty_iff_eq_empty.mp (by
      rintro ⟨z, hz1, hz2⟩
      exact hρsub hz1 (subset_closure hz2))⟩
  have hρ₀ex : ∃ ρ : ℝ, 0 < ρ ∧ Metric.ball c₀ ρ ∩ Work.Top.NakaneData.paramRay hN 0 = ∅ := by
    have hopen : IsOpen (closure (Work.Top.NakaneData.paramRay hN 0))ᶜ :=
      isClosed_closure.isOpen_compl
    obtain ⟨ρ, hρpos, hρsub⟩ := Metric.isOpen_iff.mp hopen c₀ hc0_ray0
    exact ⟨ρ, hρpos, Set.not_nonempty_iff_eq_empty.mp (by
      rintro ⟨z, hz1, hz2⟩
      exact hρsub hz1 (subset_closure hz2))⟩
  obtain ⟨ρθ, hρθpos, hρθball⟩ := hρθex
  obtain ⟨ρ₀, hρ₀pos, hρ₀ball⟩ := hρ₀ex
  set r' : ℝ := min r (min ρθ ρ₀) / 2 with hr'def
  have hr'pos : 0 < r' := by
    rw [hr'def]
    have : 0 < min r (min ρθ ρ₀) := lt_min hr (lt_min hρθpos hρ₀pos)
    linarith
  have hr'le : r' ≤ r := by
    rw [hr'def]
    have : min r (min ρθ ρ₀) ≤ r := min_le_left _ _
    linarith
  have hr'θ : r' < ρθ := by
    rw [hr'def]
    have h1 : min r (min ρθ ρ₀) ≤ min ρθ ρ₀ := min_le_right _ _
    have h2 : min ρθ ρ₀ ≤ ρθ := min_le_left _ _
    linarith
  have hr'₀ : r' < ρ₀ := by
    rw [hr'def]
    have h1 : min r (min ρθ ρ₀) ≤ min ρθ ρ₀ := min_le_right _ _
    have h2 : min ρθ ρ₀ ≤ ρ₀ := min_le_right _ _
    linarith
  have hballθ' : Metric.ball c₀ r' ∩ Work.Top.NakaneData.paramRay hN θ = ∅ :=
    Set.not_nonempty_iff_eq_empty.mp (by
      rintro ⟨z, hz, hz'⟩
      exact (Set.not_nonempty_iff_eq_empty.mpr hρθball)
        ⟨z, (by rw [Metric.mem_ball] at hz ⊢; exact lt_trans hz hr'θ), hz'⟩)
  have hball₀' : Metric.ball c₀ r' ∩ Work.Top.NakaneData.paramRay hN 0 = ∅ :=
    Set.not_nonempty_iff_eq_empty.mp (by
      rintro ⟨z, hz, hz'⟩
      exact (Set.not_nonempty_iff_eq_empty.mpr hρ₀ball)
        ⟨z, (by rw [Metric.mem_ball] at hz ⊢; exact lt_trans hz hr'₀), hz'⟩)
  -- ### Step 2: the pinch data at scale `r'`
  obtain ⟨x, y, hsegN, e₁, he₁, e₂, he₂, he₁Mb, he₂Mb, hang₁, hang₂⟩ := hX r' hr'pos
  set β₁ : ℝ := Work.Top.NakaneData.extAngle Φ e₁ with hβ₁def
  set β₂ : ℝ := Work.Top.NakaneData.extAngle Φ e₂ with hβ₂def
  have hang₁' : β₁ ∈ Set.Ioo (a₁ - ε) (a₁ + ε) := by rw [hβ₁def]; exact hang₁
  have hang₂' : β₂ ∈ Set.Ioo (a₂ - ε) (a₂ + ε) := by rw [hβ₂def]; exact hang₂
  have hβ₁gt : a₁ - ε < β₁ := hang₁'.1
  have hβ₁lt : β₁ < a₁ + ε := hang₁'.2
  have hβ₂gt : a₂ - ε < β₂ := hang₂'.1
  have hβ₂lt : β₂ < a₂ + ε := hang₂'.2
  have hβ₁pos : 0 < β₁ := lt_trans hwin1 hβ₁gt
  have hβ₁₀ : 0 ≤ β₁ := le_of_lt hβ₁pos
  have hβ₁θ : β₁ < θ := lt_trans hβ₁lt hwin2
  have hθβ₂ : θ < β₂ := lt_trans hwin3 hβ₂gt
  have hβ₂₁ : β₂ < 1 := lt_trans hβ₂lt hwin4
  have hθ₀ : 0 < θ := lt_trans hβ₁pos hβ₁θ
  have hθ₁ : θ < 1 := lt_trans hθβ₂ hβ₂₁
  have hβ₁₁ : β₁ < 1 := lt_trans hβ₁θ hθ₁
  have hβ₂pos : 0 < β₂ := lt_trans hθ₀ hθβ₂
  have hβ₂₀ : 0 ≤ β₂ := le_of_lt hβ₂pos
  have hβ : β₁ < β₂ := lt_trans hβ₁θ hθβ₂
  -- ### Step 3: the two pinch points `E₁`, `E₂` of maximal potential on the segment
  have he₁ray : e₁ ∈ Work.Top.NakaneData.paramRay hN β₁ := by
    rw [hβ₁def]; exact mem_paramRay_extAngle hN he₁Mb
  have he₂ray : e₂ ∈ Work.Top.NakaneData.paramRay hN β₂ := by
    rw [hβ₂def]; exact mem_paramRay_extAngle hN he₂Mb
  obtain ⟨E₁, hE₁, hmax₁⟩ := exists_max_potential_on_segment_in_ray hN x y β₁ ⟨he₁, he₁ray⟩
  obtain ⟨E₂, hE₂, hmax₂⟩ := exists_max_potential_on_segment_in_ray hN x y β₂ ⟨he₂, he₂ray⟩
  have hE₁mb : E₁ ∉ Mb := NakaneData.paramRay_subset_compl hN β₁ hE₁.2
  have hE₂mb : E₂ ∉ Mb := NakaneData.paramRay_subset_compl hN β₂ hE₂.2
  have hsegE : segment ℝ E₂ E₁ ⊆ segment ℝ x y :=
    Convex.segment_subset (convex_segment x y) hE₂.1 hE₁.1
  -- ### Step 4: the level `R`, above everything on the segment
  have hseg_cpt : IsCompact (segment ℝ x y) := by
    rw [← convexHull_pair (𝕜 := ℝ) x y]
    exact (Set.finite_singleton y).insert x |>.isCompact_convexHull ℝ
  obtain ⟨cM, _hcMmem, hcMmax⟩ :=
    hseg_cpt.exists_isMaxOn ⟨E₁, hE₁.1⟩ hN.continuous_potential.continuousOn
  set M : ℝ := potential Mb Φ cM with hMdef
  set R : ℝ := max (Real.exp M) (max ‖Φ E₁‖ ‖Φ E₂‖) + 1 with hRdef
  have hR1 : 1 < R := by
    rw [hRdef]
    have h1 : 0 < Real.exp M := Real.exp_pos M
    have h2 : Real.exp M ≤ max (Real.exp M) (max ‖Φ E₁‖ ‖Φ E₂‖) := le_max_left _ _
    linarith
  have hRE₁ : ‖Φ E₁‖ < R := by
    rw [hRdef]
    have h2 : ‖Φ E₁‖ ≤ max (Real.exp M) (max ‖Φ E₁‖ ‖Φ E₂‖) :=
      le_trans (le_max_left _ _) (le_max_right _ _)
    linarith
  have hRE₂ : ‖Φ E₂‖ < R := by
    rw [hRdef]
    have h2 : ‖Φ E₂‖ ≤ max (Real.exp M) (max ‖Φ E₁‖ ‖Φ E₂‖) :=
      le_trans (le_max_right _ _) (le_max_right _ _)
    linarith
  have hseg : ∀ c ∈ segment ℝ x y, potential Mb Φ c < Real.log R := by
    intro c hc
    have hcM : potential Mb Φ c ≤ M := hcMmax hc
    by_cases hcMb : c ∈ Mb
    · rw [potential_of_mem hcMb]; exact Real.log_pos hR1
    · rw [potential_of_not_mem hcMb]
      have hφ : 0 < ‖Φ c‖ := norm_pos_iff.mpr (hN.Phi_ne_zero hcMb)
      have h1 : ‖Φ c‖ ≤ Real.exp M := by
        rw [← Real.exp_log hφ, ← potential_of_not_mem hcMb]
        exact Real.exp_le_exp.mpr hcM
      have h2 : Real.exp M < R := by
        rw [hRdef]
        have h3 : Real.exp M ≤ max (Real.exp M) (max ‖Φ E₁‖ ‖Φ E₂‖) := le_max_left _ _
        linarith
      exact Real.log_lt_log hφ (lt_of_le_of_lt h1 h2)
  -- ### Step 5: the pinch curve `J` and its intersection with `Mb`
  set J : Set ℂ := Work.Top.NakaneData.rayPiece hN β₁ (potential Mb Φ E₁) R ∪
      Work.Top.NakaneData.eqArc hN β₁ β₂ R ∪
      Work.Top.NakaneData.rayPiece hN β₂ (potential Mb Φ E₂) R ∪ segment ℝ E₂ E₁ with hJdef
  have hJc : IsJordanCurve J := by
    rw [hJdef]
    exact pinch_curve_jordan hN hβ₁₀ hβ hβ₂₁ hR1 hE₁ hE₂ hmax₁ hmax₂ hRE₁ hRE₂ hseg
  have hJle : ∀ z ∈ J, potential Mb Φ z ≤ Real.log R := by
    intro z hzJ
    rw [hJdef] at hzJ
    rcases hzJ with ((h | h) | h) | h
    · exact NakaneData.rayPiece_subset_le h
    · exact le_of_eq (eqArc_subset_potential hN hR1 h)
    · exact NakaneData.rayPiece_subset_le h
    · exact le_of_lt (hseg z (hsegE h))
  have hJmb : J ∩ Mb ⊆ Nm ∩ Metric.ball c₀ r' := by
    intro z hz
    obtain ⟨hzJ, hzMb⟩ := hz
    rw [hJdef] at hzJ
    have hpotz : potential Mb Φ z = 0 := potential_of_mem hzMb
    rcases hzJ with ((h | h) | h) | h
    · exfalso
      have h1 : potential Mb Φ E₁ ≤ potential Mb Φ z := NakaneData.rayPiece_subset_ge h
      have h2 : 0 < potential Mb Φ E₁ := (hN.potential_pos_iff E₁).mpr hE₁mb
      linarith
    · exfalso
      have h1 : potential Mb Φ z = Real.log R := eqArc_subset_potential hN hR1 h
      have h2 : 0 < Real.log R := Real.log_pos hR1
      linarith
    · exfalso
      have h1 : potential Mb Φ E₂ ≤ potential Mb Φ z := NakaneData.rayPiece_subset_ge h
      have h2 : 0 < potential Mb Φ E₂ := (hN.potential_pos_iff E₂).mpr hE₂mb
      linarith
    · exact hsegN (hsegE h)
  set S : Sides J := hJ.sides J hJc with hSdef
  -- ### Step 6: `1/4` lies in the unbounded side of `J`
  have hparam0J : Work.Top.NakaneData.paramRay hN 0 ⊆ Jᶜ := by
    intro z hz
    rw [Set.mem_compl_iff]
    intro hzJ
    rw [hJdef] at hzJ
    rcases hzJ with ((h | h) | h) | h
    · exact Set.disjoint_left.mp (paramRay_disjoint_of_ne hN le_rfl (by norm_num) hβ₁₀ hβ₁₁
        (ne_of_gt hβ₁pos)) hz (NakaneData.rayPiece_subset_paramRay h)
    · obtain ⟨s, rfl⟩ := h
      have hs := s.2
      have h1 : NakaneData.extAngle Φ (NakaneData.rayPt hN s.1 R) = 0 :=
        extAngle_of_mem_paramRay hN le_rfl (by norm_num) hz
      have h2 : NakaneData.extAngle Φ (NakaneData.rayPt hN s.1 R) = s.1 :=
        extAngle_rayPt hN (le_trans hβ₁₀ hs.1) (lt_of_le_of_lt hs.2 hβ₂₁) hR1
      have hzero : s.1 = 0 := by rw [← h2, h1]
      linarith [lt_of_lt_of_le hβ₁pos hs.1]
    · exact Set.disjoint_left.mp (paramRay_disjoint_of_ne hN le_rfl (by norm_num) hβ₂₀ hβ₂₁
        (ne_of_gt hβ₂pos)) hz (NakaneData.rayPiece_subset_paramRay h)
    · exfalso
      exact (Set.not_nonempty_iff_eq_empty.mpr hball₀') ⟨z, (hsegN (hsegE h)).2, hz⟩
  have hparam0O : Work.Top.NakaneData.paramRay hN 0 ⊆ S.O :=
    S.subset_O_of_unbounded (isPreconnected_paramRay hN 0) hparam0J (paramRay_unbounded hN 0)
  have hquarter_notJ : (1/4 : ℂ) ∉ J := by
    intro h
    have h1 := (hJmb ⟨h, hquarter_mb⟩).2
    rw [Metric.mem_ball] at h1
    linarith
  have hquarterO : (1/4 : ℂ) ∈ S.O := by
    have hcl : (1/4 : ℂ) ∈ closure S.O := closure_mono hparam0O hquarter_cl
    rw [closure_eq_self_union_frontier, S.frontier_O] at hcl
    rcases hcl with h | h
    · exact h
    · exact absurd h hquarter_notJ
  -- ### Step 7: the cross box at the equipotential point `z₀ = rayPt θ R`
  have hηpos : 0 < min (θ - β₁) (β₂ - θ) / 2 := by
    have h1 : 0 < θ - β₁ := by linarith
    have h2 : 0 < β₂ - θ := by linarith
    linarith [lt_min h1 h2]
  set η : ℝ := min (θ - β₁) (β₂ - θ) / 2 with hηdef
  have hηpos' : 0 < η := by rw [hηdef]; exact hηpos
  have hηβ₁ : η ≤ θ - β₁ := by
    rw [hηdef]; linarith [min_le_left (θ - β₁) (β₂ - θ)]
  have hηβ₂ : η ≤ β₂ - θ := by
    rw [hηdef]; linarith [min_le_right (θ - β₁) (β₂ - θ)]
  set z₀ : ℂ := NakaneData.rayPt hN θ R with hz₀def
  have hz₀Φ : Φ z₀ = NakaneData.rayPoint θ R := by rw [hz₀def]; exact hN.Phi_rayPt hR1
  have hz₀ray : z₀ ∈ Work.Top.NakaneData.paramRay hN θ :=
    ⟨hN.rayPt_notMem hR1, R, hR1, by rw [hz₀def]; exact hN.Phi_rayPt hR1⟩
  have hz₀dist : r' < dist z₀ c₀ := by
    by_contra hcon
    rw [not_lt] at hcon
    have hmem : z₀ ∈ Metric.ball c₀ ρθ := by
      rw [Metric.mem_ball]
      linarith
    exact (Set.not_nonempty_iff_eq_empty.mpr hρθball) ⟨z₀, hmem, hz₀ray⟩
  have hεpos : 0 < (dist z₀ c₀ - r') / 2 := by linarith
  obtain ⟨a, b, ha, hb, haR1, hangle, hball⟩ :=
    exists_crossBox hN hθ₀ hθ₁ hR1 hz₀Φ hηpos' hεpos
  set Bx : Set ℂ := {c : ℂ | c ∉ Mb ∧ |(rayRot θ (Φ c)).re - R| < a ∧
      |(rayRot θ (Φ c)).im| < b} with hBxdef
  set P : Set ℂ := {c : ℂ | c ∉ Mb ∧ |(rayRot θ (Φ c)).re - R| < a ∧
      |(rayRot θ (Φ c)).im| < b ∧ ‖Φ c‖ < R} with hPdef
  set Q : Set ℂ := {c : ℂ | c ∉ Mb ∧ |(rayRot θ (Φ c)).re - R| < a ∧
      |(rayRot θ (Φ c)).im| < b ∧ R < ‖Φ c‖} with hQdef
  have hPconn : IsPreconnected P := by
    rw [hPdef]; exact isPreconnected_box_small hN ha hb hR1 haR1
  have hQconn : IsPreconnected Q := by
    rw [hQdef]; exact isPreconnected_box_gt hN ha hb hR1 (lt_of_le_of_lt haR1 (by linarith))
  have hBopen : IsOpen Bx := by
    rw [hBxdef]; exact isOpen_crossBox hN θ R a b
  have hz₀B : z₀ ∈ Bx := by
    rw [hBxdef]
    refine ⟨hN.rayPt_notMem hR1, ?_, ?_⟩
    · rw [hz₀Φ, rayRot_rayPoint_self]; simpa using ha
    · rw [hz₀Φ, rayRot_rayPoint_self]; simpa using hb
  have hz₀J : z₀ ∈ J := by
    rw [hJdef, hz₀def]
    exact Or.inl (Or.inl (Or.inr ⟨⟨θ, ⟨le_of_lt hβ₁θ, le_of_lt hθβ₂⟩⟩, rfl⟩))
  have hBC : (Bx ∩ J).Nonempty := ⟨z₀, hz₀B, hz₀J⟩
  have hcov : Bx \ J ⊆ P ∪ Q := by
    intro z hz
    obtain ⟨hzB, hzJ⟩ := hz
    rw [hBxdef] at hzB
    obtain ⟨hzMb, hbox1, hbox2⟩ := hzB
    have hang := hangle z hzMb hbox1 hbox2
    have hne : ‖Φ z‖ ≠ R := by
      intro hnorm
      apply hzJ
      rw [hJdef]
      refine Or.inl (Or.inl (Or.inr ?_))
      refine mem_eqArc_of hN hR1 hzMb ?_ ?_
      · rw [potential_of_not_mem hzMb, hnorm]
      · obtain ⟨h1, h2⟩ := abs_lt.mp hang
        exact ⟨by linarith [hηβ₁], by linarith [hηβ₂]⟩
    rcases lt_or_gt_of_ne hne with h | h
    · exact Or.inl (by rw [hPdef]; exact ⟨hzMb, hbox1, hbox2, h⟩)
    · exact Or.inr (by rw [hQdef]; exact ⟨hzMb, hbox1, hbox2, h⟩)
  have hnotJ : ∀ z : ℂ, z ∈ Bx → ‖Φ z‖ ≠ R → z ∉ J := by
    intro z hzB hne hzJ
    rw [hBxdef] at hzB
    obtain ⟨hzMb, hbox1, hbox2⟩ := hzB
    have hang := hangle z hzMb hbox1 hbox2
    have hdist := hball z hzMb hbox1 hbox2
    rw [hJdef] at hzJ
    rcases hzJ with ((h | h) | h) | h
    · exact absurd (extAngle_of_mem_paramRay hN hβ₁₀ hβ₁₁
          (NakaneData.rayPiece_subset_paramRay h)) (by
        intro hext
        have hthis := hang
        rw [hext] at hthis
        rw [abs_of_neg (by linarith : β₁ - θ < 0)] at hthis
        linarith [hηβ₁])
    · have h1 : potential Mb Φ z = Real.log R := eqArc_subset_potential hN hR1 h
      have hpos : 0 < ‖Φ z‖ := norm_pos_iff.mpr (hN.Phi_ne_zero hzMb)
      have hexp : Real.exp (Real.log ‖Φ z‖) = Real.exp (Real.log R) := by
        rw [← potential_of_not_mem hzMb, h1]
      rw [Real.exp_log hpos, Real.exp_log (by linarith : (0:ℝ) < R)] at hexp
      exact hne hexp
    · exact absurd (extAngle_of_mem_paramRay hN hβ₂₀ hβ₂₁
          (NakaneData.rayPiece_subset_paramRay h)) (by
        intro hext
        have hthis := hang
        rw [hext] at hthis
        rw [abs_of_pos (by linarith : 0 < β₂ - θ)] at hthis
        linarith [hηβ₂])
    · exfalso
      have hzxy : z ∈ segment ℝ x y := hsegE h
      have hzb : z ∈ Metric.ball c₀ r' := (hsegN hzxy).2
      rw [Metric.mem_ball] at hzb
      have h3 : dist z₀ c₀ ≤ dist z₀ z + dist z c₀ := dist_triangle _ _ _
      rw [dist_comm z₀ z] at h3
      linarith [hz₀dist]
  have hPC : Disjoint P J := by
    rw [Set.disjoint_left]
    intro z hzP hzJ
    rw [hPdef] at hzP
    exact hnotJ z (by rw [hBxdef]; exact ⟨hzP.1, hzP.2.1, hzP.2.2.1⟩) (ne_of_lt hzP.2.2.2) hzJ
  have hQC : Disjoint Q J := by
    rw [Set.disjoint_left]
    intro z hzQ hzJ
    rw [hQdef] at hzQ
    exact hnotJ z (by rw [hBxdef]; exact ⟨hzQ.1, hzQ.2.1, hzQ.2.2.1⟩) (ne_of_gt hzQ.2.2.2) hzJ
  have hsuperO : {z : ℂ | Real.log R < potential Mb Φ z} ⊆ S.O := by
    refine S.subset_O_of_unbounded (isPreconnected_gt_potential hN hR1) ?_ ?_
    · intro z hz
      rw [Set.mem_compl_iff]
      intro hzJ
      exact absurd (hJle z hzJ) (not_le.mpr hz)
    · intro n
      obtain ⟨R₀, hR₀⟩ := hN.tendsto_potential (Real.log R + 1)
      refine ⟨((max R₀ (n : ℝ) + 1 : ℝ) : ℂ), ?_, ?_⟩
      · have h1 : R₀ ≤ ‖(((max R₀ (n : ℝ) + 1 : ℝ)) : ℂ)‖ := by
          rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
          have := le_max_left R₀ (n : ℝ); linarith
        exact lt_of_lt_of_le (lt_add_one (Real.log R)) (hR₀ _ h1)
      · rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
        have := le_max_right R₀ (n : ℝ)
        linarith
  have hQz : ∃ z ∈ Q, z ∈ S.O := by
    have h1 : 1 < R + a / 2 := by linarith
    refine ⟨NakaneData.rayPt hN θ (R + a / 2), ?_, ?_⟩
    · rw [hQdef]
      refine ⟨hN.rayPt_notMem h1, ?_, ?_, ?_⟩
      · rw [hN.Phi_rayPt h1, rayRot_rayPoint_self]
        simp only [Complex.ofReal_re]
        rw [abs_lt]; exact ⟨by linarith, by linarith⟩
      · rw [hN.Phi_rayPt h1, rayRot_rayPoint_self]; simpa using hb
      · rw [hN.Phi_rayPt h1, NakaneData.norm_rayPoint, abs_of_pos (by linarith)]
        linarith
    · apply hsuperO
      rw [Set.mem_ofPred_eq, hN.potential_rayPt h1]
      exact Real.log_lt_log (by linarith) (by linarith)
  have hPI : P ⊆ S.I :=
    S.sides_of_halves (B := Bx) (P := P) (Q := Q) hBopen hBC hcov hPconn hQconn hPC hQC hQz
  -- ### Step 8: the part of the `θ`-ray below level `R` lies in the bounded side
  set T : Set ℂ := {c : ℂ | c ∈ Work.Top.NakaneData.paramRay hN θ ∧
      potential Mb Φ c < Real.log R} with hTdef
  have hTconn : IsPreconnected T := by
    rw [hTdef]; exact isPreconnected_paramRay_lt hN θ hR1
  have hTsub : T ⊆ Jᶜ := by
    intro z hz
    rw [hTdef] at hz
    obtain ⟨hzray, hzpot⟩ := hz
    rw [Set.mem_compl_iff]
    intro hzJ
    rw [hJdef] at hzJ
    rcases hzJ with ((h | h) | h) | h
    · exact Set.disjoint_left.mp (paramRay_disjoint_of_ne hN (le_of_lt hθ₀) hθ₁ hβ₁₀ hβ₁₁
        (ne_of_lt hβ₁θ)) hzray (NakaneData.rayPiece_subset_paramRay h)
    · exact absurd (eqArc_subset_potential hN hR1 h) (ne_of_lt hzpot)
    · exact Set.disjoint_left.mp (paramRay_disjoint_of_ne hN (le_of_lt hθ₀) hθ₁ hβ₂₀ hβ₂₁
        (ne_of_gt hθβ₂)) hzray (NakaneData.rayPiece_subset_paramRay h)
    · exfalso
      exact (Set.not_nonempty_iff_eq_empty.mpr hballθ') ⟨z, (hsegN (hsegE h)).2, hzray⟩
  set t₀ : ℝ := (max 1 (R - a) + R) / 2 with ht₀def
  have ht₀1 : 1 < t₀ := by
    rw [ht₀def]; have := le_max_left (1 : ℝ) (R - a); linarith
  have ht₀R : t₀ < R := by
    rw [ht₀def]
    have hm : max 1 (R - a) < R := max_lt hR1 (by linarith)
    linarith
  have hzt₀P : NakaneData.rayPt hN θ t₀ ∈ P := by
    rw [hPdef]
    refine ⟨hN.rayPt_notMem ht₀1, ?_, ?_, ?_⟩
    · rw [hN.Phi_rayPt ht₀1, rayRot_rayPoint_self]
      simp only [Complex.ofReal_re]
      rw [abs_lt]
      have := le_max_right (1 : ℝ) (R - a)
      exact ⟨by linarith, by linarith⟩
    · rw [hN.Phi_rayPt ht₀1, rayRot_rayPoint_self]; simpa using hb
    · rw [hN.Phi_rayPt ht₀1, NakaneData.norm_rayPoint, abs_of_pos (by linarith)]
      exact ht₀R
  have hzt₀T : NakaneData.rayPt hN θ t₀ ∈ T := by
    rw [hTdef]
    refine ⟨⟨hN.rayPt_notMem ht₀1, t₀, ht₀1, hN.Phi_rayPt ht₀1⟩, ?_⟩
    rw [hN.potential_rayPt ht₀1]
    exact Real.log_lt_log (by linarith) ht₀R
  have hTI : T ⊆ S.I := by
    rcases S.subset_of_preconnected hTconn hTsub with h | h
    · exact h
    · exact absurd (h hzt₀T) (S.notMem_O_of_mem_I (hPI hzt₀P))
  -- ### Step 9: `p` lies in the closure of that part, hence in the bounded side
  have hpT : p ∈ closure T := by
    rw [mem_closure_iff]
    intro o ho hpo
    have hVopen : IsOpen {c : ℂ | potential Mb Φ c < Real.log R} :=
      isOpen_lt hN.continuous_potential continuous_const
    have hpV : p ∈ {c : ℂ | potential Mb Φ c < Real.log R} := by
      rw [Set.mem_ofPred_eq, potential_of_mem hp]; exact Real.log_pos hR1
    obtain ⟨z, ⟨hzo, hzV⟩, hzray⟩ :=
      mem_closure_iff.mp hpcl _ (ho.inter hVopen) ⟨hpo, hpV⟩
    exact ⟨z, hzo, by rw [hTdef]; exact ⟨hzray, hzV⟩⟩
  have hpnotJ : p ∉ J := by
    intro hpJ
    have h1 := (hJmb ⟨hpJ, hp⟩).2
    rw [Metric.mem_ball] at h1
    linarith
  have hpI : p ∈ S.I := by
    have h1 : p ∈ closure S.I := closure_mono hTI hpT
    rw [closure_eq_self_union_frontier, S.frontier_I] at h1
    rcases h1 with h | h
    · exact h
    · exact absurd h hpnotJ
  -- ### Step 10: the path meets the pinch curve
  obtain ⟨t, ht⟩ := S.path_meets (f := γ) (by rw [hγ0]; exact hpI) (by rw [hγ1]; exact hquarterO)
  obtain ⟨hNm, hball'⟩ := hJmb ⟨ht, hγmem t⟩
  refine ⟨t, hNm, ?_⟩
  have h2 : dist (γ t) c₀ < r' := by rwa [Metric.mem_ball] at hball'
  rw [dist_comm]
  linarith

end Work.Top
