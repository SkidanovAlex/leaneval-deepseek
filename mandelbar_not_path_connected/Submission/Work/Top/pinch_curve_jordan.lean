/-
# The pinch curve of the mandelbar endgame is a Jordan curve

Let `Mb` be the connectedness locus and `Φ` Nakane's parameter Böttcher coordinate, subject to the
abstract interface `NakaneData` (`Submission/Work/Top/Defs.lean`).  Given

* a straight segment `segment ℝ x y` lying strictly below the equipotential of level `R > 1`
  (`hseg`),
* two parameter rays of angles `0 ≤ β₁ < β₂ < 1`, meeting the segment in the points `E₁`, `E₂` which
  *maximise* the potential among the points of the segment lying on the respective ray (`hmax₁`,
  `hmax₂`), with `‖Φ Eⱼ‖ < R`,

the set

`rayPiece β₁ (potential E₁) R ∪ eqArc β₁ β₂ R ∪ rayPiece β₂ (potential E₂) R ∪ segment E₂ E₁`

— the piece of the `β₁`-ray from `E₁` out to level `R`, the equipotential arc at level `R` from
`β₁` to `β₂`, the piece of the `β₂`-ray back down to `E₂`, and the straight segment from `E₂`
to `E₁` — is a Jordan curve.

The four pieces are exhibited as four continuous injective arcs which meet cyclically only in their
common endpoints (and pairwise disjointly otherwise), so that
`Work.Top.four_arcs_jordan` applies; the geometric content is that

* a ray piece and the equipotential arc meet only in the ray point at level `R`
  (`Work.Top.rayPiece_inter_eqArc`),
* a ray piece and the segment meet only in the maximising point `Eⱼ`
  (`Work.Top.segment_inter_rayPiece_eq_singleton`),
* ray pieces of different angles are disjoint (`Work.Top.disjoint_rayPiece`),
* the equipotential arc and the segment are disjoint because their potentials are `= log R` and
  `< log R` respectively (`Work.Top.disjoint_eqArc_segment`).
-/
import Mathlib
import Submission.Work.Top.Defs
import Submission.Work.Top.Jordan
import Submission.Work.Top.rayPt_injOn
import Submission.Work.Top.continuousOn_rayPt
import Submission.Work.Top.eqArc_subset_potential
import Submission.Work.Top.paramRay_rayPt_norm
import Submission.Work.Top.rayPiece_eq_image_Icc
import Submission.Work.Top.rayPiece_inter_eqArc
import Submission.Work.Top.segment_inter_rayPiece_eq_singleton
import Submission.Work.Top.disjoint_rayPiece
import Submission.Work.Top.disjoint_eqArc_segment
import Submission.Work.Top.four_arcs_jordan

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Classical Set
open scoped Topology

noncomputable section

namespace Work.Top

/-! ## Continuity of the ray parametrisation -/

/-- The point `rayPoint θ R` of the Böttcher plane depends continuously on the angle `θ`. -/
theorem continuous_rayPoint (R : ℝ) :
    Continuous fun θ : ℝ => NakaneData.rayPoint θ R := by
  have h : Continuous fun θ : ℝ => (2 * (Real.pi : ℂ) * (θ : ℂ) * Complex.I) := by fun_prop
  exact continuous_const.mul (Complex.continuous_exp.comp h)

/-- The point of the parameter ray of angle `θ` at the fixed level `R > 1` depends continuously
on `θ`. -/
theorem continuous_rayPt_angle {Mb : Set ℂ} {Φ : ℂ → ℂ} (hN : NakaneData Mb Φ)
    {R : ℝ} (hR : 1 < R) :
    Continuous fun θ : ℝ => NakaneData.rayPt hN θ R := by
  have hbase : Continuous fun θ : ℝ => ((hN.e.symm
      (⟨NakaneData.rayPoint θ R,
        NakaneData.rayPoint_mem_exteriorDisc hR⟩ : ↥exteriorDisc) : ↥Mbᶜ) : ℂ) :=
    continuous_subtype_val.comp (hN.e.symm.continuous.comp
      (Continuous.subtype_mk (continuous_rayPoint R)
        (fun θ => NakaneData.rayPoint_mem_exteriorDisc hR)))
  refine hbase.congr fun θ => ?_
  exact (NakaneData.rayPt_eq_symm hN hR).symm

/-- Continuity of the ray parametrisation in the level, along a continuous reparametrisation
`g` of `unitInterval` which stays above level `1`. -/
theorem continuous_rayPt_level_interval {Mb : Set ℂ} {Φ : ℂ → ℂ} (hN : NakaneData Mb Φ) (β : ℝ)
    {g : unitInterval → ℝ} (hg : Continuous g) (hg1 : ∀ s, 1 < g s) :
    Continuous fun s : unitInterval => NakaneData.rayPt hN β (g s) :=
  ContinuousOn.comp_continuous (continuousOn_rayPt hN β) hg hg1

/-- Continuity of the ray parametrisation in the angle, along a continuous reparametrisation `g`
of `unitInterval`, at a fixed level `R > 1`. -/
theorem continuous_rayPt_angle_interval {Mb : Set ℂ} {Φ : ℂ → ℂ} (hN : NakaneData Mb Φ)
    {R : ℝ} (hR : 1 < R) {g : unitInterval → ℝ} (hg : Continuous g) :
    Continuous fun s : unitInterval => NakaneData.rayPt hN (g s) R :=
  (continuous_rayPt_angle hN hR).comp hg

/-! ## Ranges of affine reparametrisations of `unitInterval` -/

/-- The range of `s ↦ f s` on `unitInterval` is the image of `[0,1]` under `f`. -/
theorem range_subtype_unitInterval {α : Type*} (f : ℝ → α) :
    Set.range (fun s : unitInterval => f s.1) = f '' Set.Icc 0 1 := by
  rw [show (fun s : unitInterval => f s.1) = f ∘ (Subtype.val : unitInterval → ℝ) from rfl,
    Set.range_comp, Subtype.range_val]

/-- The increasing affine reparametrisation `s ↦ a + s (b - a)` maps `[0,1]` onto `[a,b]`. -/
theorem range_affine_Icc {a b : ℝ} (hab : a ≤ b) :
    Set.range (fun s : unitInterval => a + s.1 * (b - a)) = Set.Icc a b := by
  have hf : ContinuousOn (fun t : ℝ => a + t * (b - a)) (Set.Icc 0 1) := by fun_prop
  have hmono : MonotoneOn (fun t : ℝ => a + t * (b - a)) (Set.Icc 0 1) := by
    intro x _ y _ hxy
    have h : (x - y) * (b - a) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hxy) (sub_nonneg.mpr hab)
    linarith
  rw [range_subtype_unitInterval (fun t : ℝ => a + t * (b - a)),
    ContinuousOn.image_Icc_of_monotoneOn (show (0 : ℝ) ≤ 1 by norm_num) hf hmono]
  ring_nf

/-- The decreasing affine reparametrisation `s ↦ b + s (a - b)` maps `[0,1]` onto `[a,b]`. -/
theorem range_affine_Icc_rev {a b : ℝ} (hab : a ≤ b) :
    Set.range (fun s : unitInterval => b + s.1 * (a - b)) = Set.Icc a b := by
  have hf : ContinuousOn (fun t : ℝ => b + t * (a - b)) (Set.Icc 0 1) := by fun_prop
  have hanti : AntitoneOn (fun t : ℝ => b + t * (a - b)) (Set.Icc 0 1) := by
    intro x _ y _ hxy
    have h : 0 ≤ (y - x) * (b - a) :=
      mul_nonneg (sub_nonneg.mpr hxy) (sub_nonneg.mpr hab)
    linarith
  rw [range_subtype_unitInterval (fun t : ℝ => b + t * (a - b)),
    ContinuousOn.image_Icc_of_antitoneOn (show (0 : ℝ) ≤ 1 by norm_num) hf hanti]
  ring_nf

/-! ## The four arcs as images of intervals -/

/-- The piece of the parameter ray of angle `β` between the levels `a` and `b`, parametrised
increasingly by `s ↦ rayPt hN β (a + s (b - a))`. -/
theorem range_rayPt_level {Mb : Set ℂ} {Φ : ℂ → ℂ} (hN : NakaneData Mb Φ) {β a b : ℝ}
    (hab : a ≤ b) :
    Set.range (fun s : unitInterval => NakaneData.rayPt hN β (a + s.1 * (b - a)))
      = NakaneData.rayPt hN β '' Set.Icc a b := by
  have h1 : (fun s : unitInterval => NakaneData.rayPt hN β (a + s.1 * (b - a)))
      = (fun t : ℝ => NakaneData.rayPt hN β t) ∘
        (fun s : unitInterval => a + s.1 * (b - a)) := rfl
  rw [h1, Set.range_comp, range_affine_Icc hab]

/-- The piece of the parameter ray of angle `β` between the levels `a` and `b`, parametrised
decreasingly by `s ↦ rayPt hN β (b + s (a - b))`. -/
theorem range_rayPt_level_rev {Mb : Set ℂ} {Φ : ℂ → ℂ} (hN : NakaneData Mb Φ) {β a b : ℝ}
    (hab : a ≤ b) :
    Set.range (fun s : unitInterval => NakaneData.rayPt hN β (b + s.1 * (a - b)))
      = NakaneData.rayPt hN β '' Set.Icc a b := by
  have h1 : (fun s : unitInterval => NakaneData.rayPt hN β (b + s.1 * (a - b)))
      = (fun t : ℝ => NakaneData.rayPt hN β t) ∘
        (fun s : unitInterval => b + s.1 * (a - b)) := rfl
  rw [h1, Set.range_comp, range_affine_Icc_rev hab]

/-- The equipotential arc of level `R` between the angles `β₁ ≤ β₂`, parametrised by
`s ↦ rayPt hN (β₁ + s (β₂ - β₁)) R`. -/
theorem range_rayPt_angle {Mb : Set ℂ} {Φ : ℂ → ℂ} (hN : NakaneData Mb Φ) {β₁ β₂ R : ℝ}
    (hβ : β₁ ≤ β₂) :
    Set.range (fun s : unitInterval => NakaneData.rayPt hN (β₁ + s.1 * (β₂ - β₁)) R)
      = NakaneData.eqArc hN β₁ β₂ R := by
  have h1 : (fun s : unitInterval => NakaneData.rayPt hN (β₁ + s.1 * (β₂ - β₁)) R)
      = (fun θ : ℝ => NakaneData.rayPt hN θ R) ∘
        (fun s : unitInterval => β₁ + s.1 * (β₂ - β₁)) := rfl
  have h2 : NakaneData.eqArc hN β₁ β₂ R
      = (fun θ : ℝ => NakaneData.rayPt hN θ R) '' Set.Icc β₁ β₂ := by
    rw [NakaneData.eqArc]
    rw [show (fun s : Set.Icc β₁ β₂ => NakaneData.rayPt hN s.1 R)
        = (fun θ : ℝ => NakaneData.rayPt hN θ R) ∘ (Subtype.val : Set.Icc β₁ β₂ → ℝ)
        from rfl, Set.range_comp, Subtype.range_val]
  rw [h1, Set.range_comp, range_affine_Icc hβ, h2]

/-- The straight segment from `E₂` to `E₁`, parametrised by `s ↦ (1 - s) • E₂ + s • E₁`. -/
theorem range_segment_unitInterval (E₁ E₂ : ℂ) :
    Set.range (fun s : unitInterval => (1 - s.1) • E₂ + s.1 • E₁) = segment ℝ E₂ E₁ := by
  rw [range_subtype_unitInterval (fun θ : ℝ => (1 - θ) • E₂ + θ • E₁), segment_eq_image]

/-! ## Injectivity of the four arcs -/

/-- A ray of fixed angle, reparametrised by an injective map into the levels `> 1`, is
injective. -/
theorem injective_rayPt_interval {Mb : Set ℂ} {Φ : ℂ → ℂ} (hN : NakaneData Mb Φ) {β : ℝ}
    (hβ₀ : 0 ≤ β) (hβ₁ : β < 1) {g : unitInterval → ℝ} (hg : Function.Injective g)
    (hg1 : ∀ s, 1 < g s) :
    Function.Injective fun s : unitInterval => NakaneData.rayPt hN β (g s) := by
  intro s s' h
  exact hg (rayPt_injOn hN hβ₀ hβ₁ hβ₀ hβ₁ (hg1 s) (hg1 s') h).2

/-- The affine parametrisation of the straight segment from `E₂` to `E₁` is injective for
`E₁ ≠ E₂`. -/
theorem injective_segment_unitInterval {E₁ E₂ : ℂ} (hne : E₁ ≠ E₂) :
    Function.Injective fun s : unitInterval => (1 - s.1) • E₂ + s.1 • E₁ := by
  have hrw : ∀ s : unitInterval,
      (1 - s.1) • E₂ + s.1 • E₁ = E₂ + s.1 • (E₁ - E₂) := by
    intro s
    module
  intro s s' h
  have h' : (1 - s.1) • E₂ + s.1 • E₁ = (1 - s'.1) • E₂ + s'.1 • E₁ := h
  rw [hrw s, hrw s'] at h'
  have h2 : s.1 • (E₁ - E₂) = s'.1 • (E₁ - E₂) := add_left_cancel h'
  have h3 : (s.1 - s'.1) • (E₁ - E₂) = 0 := by rw [sub_smul, h2, sub_self]
  rcases smul_eq_zero.mp h3 with h4 | h4
  · exact Subtype.ext (sub_eq_zero.mp h4)
  · exact absurd (sub_eq_zero.mp h4) hne

/-! ## The straight segment meets a ray piece only in its maximiser -/

/-- If `E` maximises the potential on `segment ℝ x y ∩ paramRay hN β` and `F ∈ segment ℝ x y`,
then the ray piece of angle `β` from the level of `E` to `R` meets `segment ℝ E F` only in `E`. -/
theorem rayPiece_inter_segment_eq_singleton {Mb : Set ℂ} {Φ : ℂ → ℂ} (hN : NakaneData Mb Φ)
    {x y E F : ℂ} {β R : ℝ} (hF : F ∈ segment ℝ x y)
    (hE : E ∈ segment ℝ x y ∩ NakaneData.paramRay hN β)
    (hmax : ∀ c ∈ segment ℝ x y ∩ NakaneData.paramRay hN β,
      Work.Top.potential Mb Φ c ≤ Work.Top.potential Mb Φ E)
    (hle : Work.Top.potential Mb Φ E ≤ Real.log R) :
    NakaneData.rayPiece hN β (Work.Top.potential Mb Φ E) R ∩ segment ℝ E F = {E} := by
  have hsub : segment ℝ E F ⊆ segment ℝ x y :=
    (convex_segment x y).segment_subset hE.1 hF
  have hmain := segment_inter_rayPiece_eq_singleton hN hE hmax hle
  rw [Set.inter_comm] at hmain
  refine Set.Subset.antisymm ?_ ?_
  · rintro c ⟨hcp, hcs⟩
    have : c ∈ NakaneData.rayPiece hN β (Work.Top.potential Mb Φ E) R ∩ segment ℝ x y :=
      ⟨hcp, hsub hcs⟩
    rwa [hmain] at this
  · intro c hc
    rw [Set.mem_singleton_iff] at hc
    have hleft : E ∈ segment ℝ E F := by
      rw [segment_eq_image]
      exact ⟨0, by norm_num, by simp⟩
    rw [hc]
    exact ⟨⟨hE.2, le_refl _, hle⟩, hleft⟩

/-! ## The pinch curve is a Jordan curve -/

theorem pinch_curve_jordan {Mb : Set ℂ} {Φ : ℂ → ℂ} (hN : Work.Top.NakaneData Mb Φ)
    {x y E₁ E₂ : ℂ} {β₁ β₂ R : ℝ}
    (hβ₁₀ : 0 ≤ β₁) (hβ : β₁ < β₂) (hβ₂₁ : β₂ < 1) (hR : 1 < R)
    (hE₁ : E₁ ∈ segment ℝ x y ∧ E₁ ∈ Work.Top.NakaneData.paramRay hN β₁)
    (hE₂ : E₂ ∈ segment ℝ x y ∧ E₂ ∈ Work.Top.NakaneData.paramRay hN β₂)
    (hmax₁ : ∀ c ∈ segment ℝ x y ∩ Work.Top.NakaneData.paramRay hN β₁,
      Work.Top.potential Mb Φ c ≤ Work.Top.potential Mb Φ E₁)
    (hmax₂ : ∀ c ∈ segment ℝ x y ∩ Work.Top.NakaneData.paramRay hN β₂,
      Work.Top.potential Mb Φ c ≤ Work.Top.potential Mb Φ E₂)
    (hR₁ : ‖Φ E₁‖ < R) (hR₂ : ‖Φ E₂‖ < R)
    (hseg : ∀ c ∈ segment ℝ x y, Work.Top.potential Mb Φ c < Real.log R) :
    Work.Top.IsJordanCurve
      (Work.Top.NakaneData.rayPiece hN β₁ (Work.Top.potential Mb Φ E₁) R ∪
        Work.Top.NakaneData.eqArc hN β₁ β₂ R ∪
        Work.Top.NakaneData.rayPiece hN β₂ (Work.Top.potential Mb Φ E₂) R ∪
        segment ℝ E₂ E₁) := by
  obtain ⟨hE₁seg, hE₁ray⟩ := hE₁
  obtain ⟨hE₂seg, hE₂ray⟩ := hE₂
  -- ### normal forms for the two pinch points
  have hE₁eq : E₁ = NakaneData.rayPt hN β₁ ‖Φ E₁‖ := (paramRay_rayPt_norm hN hE₁ray).1
  have hE₂eq : E₂ = NakaneData.rayPt hN β₂ ‖Φ E₂‖ := (paramRay_rayPt_norm hN hE₂ray).1
  have hpot₁ : Work.Top.potential Mb Φ E₁ = Real.log ‖Φ E₁‖ :=
    (paramRay_rayPt_norm hN hE₁ray).2
  have hpot₂ : Work.Top.potential Mb Φ E₂ = Real.log ‖Φ E₂‖ :=
    (paramRay_rayPt_norm hN hE₂ray).2
  have ht₁ : 1 < ‖Φ E₁‖ := hN.Phi_mem_exteriorDisc (NakaneData.paramRay_subset_compl hN β₁ hE₁ray)
  have ht₂ : 1 < ‖Φ E₂‖ := hN.Phi_mem_exteriorDisc (NakaneData.paramRay_subset_compl hN β₂ hE₂ray)
  have hle₁ : Work.Top.potential Mb Φ E₁ ≤ Real.log R := by
    rw [hpot₁]
    exact Real.log_le_log (lt_trans zero_lt_one ht₁) (le_of_lt hR₁)
  have hle₂ : Work.Top.potential Mb Φ E₂ ≤ Real.log R := by
    rw [hpot₂]
    exact Real.log_le_log (lt_trans zero_lt_one ht₂) (le_of_lt hR₂)
  have hpos₁ : 0 < Work.Top.potential Mb Φ E₁ := by
    rw [hpot₁]; exact Real.log_pos ht₁
  have hpos₂ : 0 < Work.Top.potential Mb Φ E₂ := by
    rw [hpot₂]; exact Real.log_pos ht₂
  have hβ₁₁ : β₁ < 1 := lt_trans hβ hβ₂₁
  have hβ₂₀ : 0 ≤ β₂ := le_trans hβ₁₀ (le_of_lt hβ)
  have hEne : E₁ ≠ E₂ := by
    intro hcon
    have hray₁ : E₁ ∈ NakaneData.paramRay hN β₂ := hcon ▸ hE₂ray
    have h₂ := (paramRay_rayPt_norm hN hray₁).1
    have h3 := (rayPt_injOn hN hβ₁₀ hβ₁₁ hβ₂₀ hβ₂₁ ht₁ ht₁ (hE₁eq.symm.trans h₂)).1
    exact absurd h3 (ne_of_lt hβ)
  -- ### the four reparametrisations
  have hg₁cont : Continuous fun s : unitInterval => ‖Φ E₁‖ + s.1 * (R - ‖Φ E₁‖) := by fun_prop
  have hg₁gt : ∀ s : unitInterval, 1 < ‖Φ E₁‖ + s.1 * (R - ‖Φ E₁‖) := by
    intro s
    have hs := s.2
    rcases le_or_gt (‖Φ E₁‖) R with h | h
    · nlinarith [mul_nonneg hs.1 (sub_nonneg.mpr h)]
    · nlinarith [mul_le_mul_of_nonneg_right hs.2 (sub_nonneg.mpr h.le)]
  have hg₁inj : Function.Injective fun s : unitInterval => ‖Φ E₁‖ + s.1 * (R - ‖Φ E₁‖) := by
    intro s s' h
    have hne : R - ‖Φ E₁‖ ≠ 0 := sub_ne_zero.mpr (ne_of_gt hR₁)
    have he : (s.1 - s'.1) * (R - ‖Φ E₁‖) = 0 := by nlinarith [h]
    have hs : s.1 - s'.1 = 0 := by
      rcases mul_eq_zero.mp he with h1 | h1
      · exact h1
      · exact absurd h1 hne
    exact Subtype.ext (sub_eq_zero.mp hs)
  have hg₃cont : Continuous fun s : unitInterval => R + s.1 * (‖Φ E₂‖ - R) := by fun_prop
  have hg₃gt : ∀ s : unitInterval, 1 < R + s.1 * (‖Φ E₂‖ - R) := by
    intro s
    have hs := s.2
    rcases le_or_gt R (‖Φ E₂‖) with h | h
    · nlinarith [mul_nonneg hs.1 (sub_nonneg.mpr h)]
    · nlinarith [mul_le_mul_of_nonneg_right hs.2 (sub_nonneg.mpr h.le)]
  have hg₃inj : Function.Injective fun s : unitInterval => R + s.1 * (‖Φ E₂‖ - R) := by
    intro s s' h
    have hne : ‖Φ E₂‖ - R ≠ 0 := sub_ne_zero.mpr (ne_of_lt hR₂)
    have he : (s.1 - s'.1) * (‖Φ E₂‖ - R) = 0 := by nlinarith [h]
    have hs : s.1 - s'.1 = 0 := by
      rcases mul_eq_zero.mp he with h1 | h1
      · exact h1
      · exact absurd h1 hne
    exact Subtype.ext (sub_eq_zero.mp hs)
  have hg₂mem : ∀ s : unitInterval, β₁ + s.1 * (β₂ - β₁) ∈ Set.Ico (0 : ℝ) 1 := by
    intro s
    have hs := s.2
    constructor
    · nlinarith [mul_nonneg hs.1 (sub_nonneg.mpr (le_of_lt hβ))]
    · nlinarith [mul_le_mul_of_nonneg_right hs.2 (sub_nonneg.mpr (le_of_lt hβ))]
  have hg₂inj : Function.Injective fun s : unitInterval => β₁ + s.1 * (β₂ - β₁) := by
    intro s s' h
    have hne : β₂ - β₁ ≠ 0 := sub_ne_zero.mpr (ne_of_gt hβ)
    have he : (s.1 - s'.1) * (β₂ - β₁) = 0 := by nlinarith [h]
    have hs : s.1 - s'.1 = 0 := by
      rcases mul_eq_zero.mp he with h1 | h1
      · exact h1
      · exact absurd h1 hne
    exact Subtype.ext (sub_eq_zero.mp hs)
  -- ### the four arcs
  let γ₁ : C(unitInterval, ℂ) :=
    ⟨fun s => NakaneData.rayPt hN β₁ (‖Φ E₁‖ + s.1 * (R - ‖Φ E₁‖)),
      continuous_rayPt_level_interval hN β₁ hg₁cont hg₁gt⟩
  let γ₂ : C(unitInterval, ℂ) :=
    ⟨fun s => NakaneData.rayPt hN (β₁ + s.1 * (β₂ - β₁)) R,
      continuous_rayPt_angle_interval hN hR (g := fun s : unitInterval => β₁ + s.1 * (β₂ - β₁))
        (by fun_prop)⟩
  let γ₃ : C(unitInterval, ℂ) :=
    ⟨fun s => NakaneData.rayPt hN β₂ (R + s.1 * (‖Φ E₂‖ - R)),
      continuous_rayPt_level_interval hN β₂ hg₃cont hg₃gt⟩
  let γ₄ : C(unitInterval, ℂ) :=
    ⟨fun s => (1 - s.1) • E₂ + s.1 • E₁, by fun_prop⟩
  -- ### injectivity of the four arcs
  have hinj₁ : Function.Injective γ₁ := by
    show Function.Injective
      fun s : unitInterval => NakaneData.rayPt hN β₁ (‖Φ E₁‖ + s.1 * (R - ‖Φ E₁‖))
    exact injective_rayPt_interval hN hβ₁₀ hβ₁₁ hg₁inj hg₁gt
  have hinj₂ : Function.Injective γ₂ := by
    show Function.Injective
      fun s : unitInterval => NakaneData.rayPt hN (β₁ + s.1 * (β₂ - β₁)) R
    intro s s' h
    have h2 := rayPt_injOn hN (hg₂mem s).1 (hg₂mem s).2 (hg₂mem s').1 (hg₂mem s').2 hR hR h
    exact hg₂inj h2.1
  have hinj₃ : Function.Injective γ₃ := by
    show Function.Injective
      fun s : unitInterval => NakaneData.rayPt hN β₂ (R + s.1 * (‖Φ E₂‖ - R))
    exact injective_rayPt_interval hN hβ₂₀ hβ₂₁ hg₃inj hg₃gt
  have hinj₄ : Function.Injective γ₄ := by
    show Function.Injective fun s : unitInterval => (1 - s.1) • E₂ + s.1 • E₁
    exact injective_segment_unitInterval hEne
  -- ### the ranges of the four arcs
  have hr₁ : Set.range γ₁ = NakaneData.rayPiece hN β₁ (Work.Top.potential Mb Φ E₁) R := by
    show Set.range
      (fun s : unitInterval => NakaneData.rayPt hN β₁ (‖Φ E₁‖ + s.1 * (R - ‖Φ E₁‖)))
      = NakaneData.rayPiece hN β₁ (Work.Top.potential Mb Φ E₁) R
    rw [range_rayPt_level hN (le_of_lt hR₁),
      rayPiece_eq_image_Icc hN hpos₁ (lt_trans zero_lt_one hR)]
    have hexp : Real.exp (Work.Top.potential Mb Φ E₁) = ‖Φ E₁‖ := by
      rw [hpot₁, Real.exp_log (by positivity)]
    rw [hexp]
  have hr₂ : Set.range γ₂ = NakaneData.eqArc hN β₁ β₂ R := by
    show Set.range
      (fun s : unitInterval => NakaneData.rayPt hN (β₁ + s.1 * (β₂ - β₁)) R)
      = NakaneData.eqArc hN β₁ β₂ R
    exact range_rayPt_angle hN (le_of_lt hβ)
  have hr₃ : Set.range γ₃ = NakaneData.rayPiece hN β₂ (Work.Top.potential Mb Φ E₂) R := by
    show Set.range
      (fun s : unitInterval => NakaneData.rayPt hN β₂ (R + s.1 * (‖Φ E₂‖ - R)))
      = NakaneData.rayPiece hN β₂ (Work.Top.potential Mb Φ E₂) R
    rw [range_rayPt_level_rev hN (le_of_lt hR₂),
      rayPiece_eq_image_Icc hN hpos₂ (lt_trans zero_lt_one hR)]
    have hexp : Real.exp (Work.Top.potential Mb Φ E₂) = ‖Φ E₂‖ := by
      rw [hpot₂, Real.exp_log (by positivity)]
    rw [hexp]
  have hr₄ : Set.range γ₄ = segment ℝ E₂ E₁ := by
    show Set.range (fun s : unitInterval => (1 - s.1) • E₂ + s.1 • E₁) = segment ℝ E₂ E₁
    exact range_segment_unitInterval E₁ E₂
  -- ### the endpoints
  have hγ₁0 : γ₁ 0 = E₁ := by
    show NakaneData.rayPt hN β₁ (‖Φ E₁‖ + ((0 : unitInterval) : ℝ) * (R - ‖Φ E₁‖)) = E₁
    rw [show ((0 : unitInterval) : ℝ) = 0 from rfl, zero_mul, add_zero]
    exact hE₁eq.symm
  have hγ₁1 : γ₁ 1 = NakaneData.rayPt hN β₁ R := by
    show NakaneData.rayPt hN β₁ (‖Φ E₁‖ + ((1 : unitInterval) : ℝ) * (R - ‖Φ E₁‖))
      = NakaneData.rayPt hN β₁ R
    rw [show ((1 : unitInterval) : ℝ) = 1 from rfl,
      show ‖Φ E₁‖ + 1 * (R - ‖Φ E₁‖) = R by ring]
  have hγ₂0 : γ₂ 0 = NakaneData.rayPt hN β₁ R := by
    show NakaneData.rayPt hN (β₁ + ((0 : unitInterval) : ℝ) * (β₂ - β₁)) R
      = NakaneData.rayPt hN β₁ R
    rw [show ((0 : unitInterval) : ℝ) = 0 from rfl, zero_mul, add_zero]
  have hγ₂1 : γ₂ 1 = NakaneData.rayPt hN β₂ R := by
    show NakaneData.rayPt hN (β₁ + ((1 : unitInterval) : ℝ) * (β₂ - β₁)) R
      = NakaneData.rayPt hN β₂ R
    rw [show ((1 : unitInterval) : ℝ) = 1 from rfl,
      show β₁ + 1 * (β₂ - β₁) = β₂ by ring]
  have hγ₃0 : γ₃ 0 = NakaneData.rayPt hN β₂ R := by
    show NakaneData.rayPt hN β₂ (R + ((0 : unitInterval) : ℝ) * (‖Φ E₂‖ - R))
      = NakaneData.rayPt hN β₂ R
    rw [show ((0 : unitInterval) : ℝ) = 0 from rfl, zero_mul, add_zero]
  have hγ₃1 : γ₃ 1 = E₂ := by
    show NakaneData.rayPt hN β₂ (R + ((1 : unitInterval) : ℝ) * (‖Φ E₂‖ - R)) = E₂
    rw [show ((1 : unitInterval) : ℝ) = 1 from rfl,
      show R + 1 * (‖Φ E₂‖ - R) = ‖Φ E₂‖ by ring]
    exact hE₂eq.symm
  have hγ₄0 : γ₄ 0 = E₂ := by
    show (1 - ((0 : unitInterval) : ℝ)) • E₂ + ((0 : unitInterval) : ℝ) • E₁ = E₂
    rw [show ((0 : unitInterval) : ℝ) = 0 from rfl]
    simp
  have hγ₄1 : γ₄ 1 = E₁ := by
    show (1 - ((1 : unitInterval) : ℝ)) • E₂ + ((1 : unitInterval) : ℝ) • E₁ = E₁
    rw [show ((1 : unitInterval) : ℝ) = 1 from rfl]
    simp
  -- ### gluing and intersection hypotheses
  have h₁₂ : γ₁ 1 = γ₂ 0 := by rw [hγ₁1, hγ₂0]
  have h₂₃ : γ₂ 1 = γ₃ 0 := by rw [hγ₂1, hγ₃0]
  have h₃₄ : γ₃ 1 = γ₄ 0 := by rw [hγ₃1, hγ₄0]
  have h₄₁ : γ₄ 1 = γ₁ 0 := by rw [hγ₄1, hγ₁0]
  have hsub : segment ℝ E₂ E₁ ⊆ segment ℝ x y :=
    (convex_segment x y).segment_subset hE₂seg hE₁seg
  have hd₁₂ : Set.range γ₁ ∩ Set.range γ₂ = {γ₁ 1} := by
    rw [hr₁, hr₂, hγ₁1]
    exact rayPiece_inter_eqArc hN ⟨le_refl β₁, le_of_lt hβ⟩ hR hle₁
  have hd₂₃ : Set.range γ₂ ∩ Set.range γ₃ = {γ₂ 1} := by
    rw [hr₂, hr₃, hγ₂1, Set.inter_comm]
    exact rayPiece_inter_eqArc hN ⟨le_of_lt hβ, le_refl β₂⟩ hR hle₂
  have hd₃₄ : Set.range γ₃ ∩ Set.range γ₄ = {γ₃ 1} := by
    rw [hr₃, hr₄, hγ₃1]
    exact rayPiece_inter_segment_eq_singleton hN hE₁seg ⟨hE₂seg, hE₂ray⟩ hmax₂ hle₂
  have hd₄₁ : Set.range γ₄ ∩ Set.range γ₁ = {γ₄ 1} := by
    rw [hr₄, hr₁, hγ₄1, Set.inter_comm, segment_symm]
    exact rayPiece_inter_segment_eq_singleton hN hE₂seg ⟨hE₁seg, hE₁ray⟩ hmax₁ hle₁
  have hd₁₃ : Disjoint (Set.range γ₁) (Set.range γ₃) := by
    rw [hr₁, hr₃]
    exact disjoint_rayPiece hN hβ₁₀ hβ₁₁ hβ₂₀ hβ₂₁ (ne_of_lt hβ)
  have hd₂₄ : Disjoint (Set.range γ₂) (Set.range γ₄) := by
    rw [hr₂, hr₄]
    exact disjoint_eqArc_segment hN hR (fun c hc => hseg c (hsub hc))
  -- ### assembly
  have hJ := four_arcs_jordan γ₁ γ₂ γ₃ γ₄ hinj₁ hinj₂ hinj₃ hinj₄ h₁₂ h₂₃ h₃₄ h₄₁
    hd₁₂ hd₂₃ hd₃₄ hd₄₁ hd₁₃ hd₂₄
  simpa only [hr₁, hr₂, hr₃, hr₄] using hJ

end Work.Top
