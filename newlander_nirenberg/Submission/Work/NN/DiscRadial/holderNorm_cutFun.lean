/-
Copyright: none.  Part of the `Newlander-Nirenberg` formalisation project.

# The `C^{k,α}` norm of the radial cutoff `cutFun` is finite

`cutFun b p = χ (b (‖p.2‖ - 1))` is the cutoff factor of the radial Seeley extension, a
function on `X × ℂ` which depends only on `‖p.2‖`.  This file proves that its `C^{k,α}` norm
on any product `U ×ˢ annR b` (`U ⊆ X` open) is bounded by a constant depending only on `k`
(and on `α`, `b`), which is the form needed when the cutoff is used as a factor in the
estimates for the extension.

The proof proceeds in three steps:

* `cutRadial b z = χ (2 ‖z‖ - 3) * χ (b (‖z‖ - 1))` is a smooth radial function on `ℂ`
  which agrees with the cutoff on the annulus `annR b` and has compact support (the first
  factor vanishes near `0` and for `‖z‖ ≥ 5/2`, so the singularity of `‖·‖` at `0` is
  invisible).  Hence its `C^{k,α}` norm on all of `ℂ` is finite, by
  `holderNorm_univ_ne_top_of_hasCompactSupport'`.
* `holderNorm_snd_le`: the `C^{k,α}` norm of `p ↦ f p.2` on `univ ×ˢ V` is bounded by that of
  `f` on `V`, because the within-derivatives compose with `Prod.snd`
  (`ContinuousLinearMap.iteratedFDerivWithin_comp_right`) and `‖Prod.snd‖ ≤ 1`.
* the `X`-dependence is eliminated by monotonicity in the set and congruence on the open set
  `U ×ˢ annR b`, where `cutFun b` agrees with `cutRadial b ∘ Prod.snd`.
-/
import Mathlib
import Submission.Work.NN.DiscRadial.DiscRadialAux
import Submission.Work.CR.Flat.Cauchy.holderNorm_mul_le_of_hasCompactSupport

noncomputable section

open scoped NNReal ENNReal ContDiff Topology
open Set Metric

namespace Work.NN.DiscRadial

open Work.NN.Final Work.CR.Flat

/-! ## A smooth compactly supported radial majorant of the cutoff -/

/-- The radial factor of the compactly supported majorant: `χ (2 s - 3) * χ (b (s - 1))`,
as a complex valued function of the real variable `s`.

The first factor is `1` exactly for `s ∈ [1,2]` and vanishes for `s ≤ 1/2` and for `s ≥ 5/2`;
the second factor is the cutoff `χ (b (s - 1))` of the radial Seeley extension. -/
def radialCut (b s : ℝ) : ℂ := ((seeleyCut (2 * s - 3) * seeleyCut (b * (s - 1)) : ℝ) : ℂ)

/-- The compactly supported majorant of the cutoff, as a function of `z : ℂ`: it only
depends on `‖z‖`. -/
def cutRadial (b : ℝ) : ℂ → ℂ := fun z => radialCut b ‖z‖

lemma contDiff_radialCut (b : ℝ) (n : ℕ∞) : ContDiff ℝ (n : ℕ∞ω) (radialCut b) := by
  have hsc : ContDiff ℝ (n : ℕ∞ω) seeleyCut :=
    seeleyCut_contDiff.of_le (WithTop.coe_le_coe.mpr le_top)
  unfold radialCut
  refine Complex.ofRealCLM.contDiff.comp ?_
  refine ContDiff.mul ?_ ?_
  · exact hsc.comp (ContDiff.sub (contDiff_const.mul contDiff_id) contDiff_const)
  · exact hsc.comp (ContDiff.mul contDiff_const (ContDiff.sub contDiff_id contDiff_const))

/-- `cutRadial b` is smooth: it is a smooth function of `‖z‖`, and `‖·‖` is smooth away from
`0`, while `cutRadial b` vanishes identically on the ball of radius `1/2` around `0`. -/
lemma contDiff_cutRadial (b : ℝ) (n : ℕ∞) : ContDiff ℝ (n : ℕ∞ω) (cutRadial b) := by
  rw [contDiff_iff_contDiffAt]
  intro z
  by_cases hz : z = 0
  · subst hz
    refine ContDiffAt.congr_of_eventuallyEq (f := fun _ : ℂ => (0 : ℂ)) (f₁ := cutRadial b)
      (x := 0) contDiffAt_const ?_
    filter_upwards [Metric.ball_mem_nhds (0 : ℂ) (by norm_num : (0 : ℝ) < 1 / 2)] with w hw
    show cutRadial b w = 0
    rw [Metric.mem_ball, dist_eq_norm, sub_zero] at hw
    rw [cutRadial, radialCut]
    have hcut : seeleyCut (2 * ‖w‖ - 3) = 0 := by
      apply seeleyCut_eq_zero
      rw [abs_of_neg (by linarith)]
      linarith
    simp [hcut]
  · exact (contDiff_radialCut b n).contDiffAt.comp z (contDiffAt_norm ℝ hz)

/-- `cutRadial b` is supported in the closed ball of radius `5/2`. -/
lemma hasCompactSupport_cutRadial (b : ℝ) : HasCompactSupport (cutRadial b) := by
  refine HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall (0 : ℂ) 2.5) ?_
  intro z hz
  rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]
  by_contra h
  push Not at h
  have hcut : seeleyCut (2 * ‖z‖ - 3) = 0 := by
    apply seeleyCut_eq_zero
    rw [abs_of_nonneg (by linarith)]
    linarith
  exact hz (by rw [cutRadial, radialCut]; simp [hcut])

/-! ## Agreeing with the cutoff on the annulus -/

lemma isOpen_annR (b : ℝ) : IsOpen (annR b) :=
  (isOpen_lt continuous_const continuous_norm).inter (isOpen_lt continuous_norm continuous_const)

/-- On the annulus `annR b` the majorant `cutRadial b` agrees with the cutoff
`z ↦ χ (b (‖z‖ - 1))`: there `‖z‖ ∈ (1, 1 + 2/b] ⊆ [1, 2]`, where the first factor
`χ (2 ‖z‖ - 3)` equals `1`. -/
lemma cutRadial_eq_seeley {b : ℝ} (hb : 2 ≤ b) {z : ℂ} (hz : z ∈ annR b) :
    cutRadial b z = ((seeleyCut (b * (‖z‖ - 1)) : ℝ) : ℂ) := by
  obtain ⟨h1, h2⟩ := hz
  have hnorm2 : ‖z‖ ≤ 2 := by
    have hbpos : 0 < b := by linarith
    have h2b : 2 / b ≤ 1 := (div_le_one hbpos).mpr hb
    linarith
  have hcut : seeleyCut (2 * ‖z‖ - 3) = 1 := by
    apply seeleyCut_eq_one
    rw [abs_le]
    constructor <;> linarith
  simp only [cutRadial, radialCut, hcut, one_mul]

/-- The majorant, composed with `Prod.snd`, equals the cutoff on `X ×ˢ annR b`. -/
lemma cutRadial_snd_eq_cutFun {X : Type*} {b : ℝ} (hb : 2 ≤ b) {p : X × ℂ}
    (hp : p.2 ∈ annR b) : cutRadial b p.2 = cutFun b p := by
  rw [cutRadial_eq_seeley hb hp]
  rfl

/-! ## The slice estimate -/

/-- **The `X`-variable costs nothing.**  For `f : Y → ℂ`, the `C^{k,α}` norm of
`p ↦ f p.2` on `univ ×ˢ V` is bounded by the `C^{k,α}` norm of `f` on `V`.

Indeed the within-derivatives compose with `Prod.snd`
(`ContinuousLinearMap.iteratedFDerivWithin_comp_right`), and `‖Prod.snd‖ ≤ 1`, so on the
product each iterated derivative has the same or smaller norm, and each divided difference
has the same or smaller quotient (since `‖p - q‖ ≥ ‖p.2 - q.2‖` and `α > 0`). -/
lemma holderNorm_snd_le {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] {k : ℕ} {α : ℝ} (hα : 0 < α) {f : Y → ℂ}
    {V : Set Y} (hV : IsOpen V) (hf : ∀ i ≤ k, ContDiffOn ℝ ((i : ℕ) : ℕ∞ω) f V) :
    Work.CR.Flat.holderNorm k α (fun p : X × Y => f p.2) (Set.univ ×ˢ V)
      ≤ Work.CR.Flat.holderNorm k α f V := by
  have hpreP : Prod.snd ⁻¹' V = (Set.univ ×ˢ V : Set (X × Y)) := by ext p; simp
  have hpreC : ⇑(ContinuousLinearMap.snd ℝ X Y) ⁻¹' V = (Set.univ ×ˢ V : Set (X × Y)) := by
    ext p; simp
  have hderiv : ∀ (i : ℕ), i ≤ k → ∀ p : X × Y, p.2 ∈ V →
      iteratedFDerivWithin ℝ i (fun p : X × Y => f p.2) (Set.univ ×ˢ V) p
        = (iteratedFDerivWithin ℝ i f V p.2).compContinuousLinearMap
            (fun _ => (ContinuousLinearMap.snd ℝ X Y)) := by
    intro i hi p hp
    have h := (ContinuousLinearMap.snd ℝ X Y).iteratedFDerivWithin_comp_right
      (f := f) (s := V) (n := (i : ℕ∞ω)) (hf i hi) hV.uniqueDiffOn
      (by rw [hpreC]; exact (isOpen_univ.prod hV).uniqueDiffOn) hp (by exact le_refl _)
    rw [← hpreP]
    exact h
  have hprod : ∀ (i : ℕ), ∏ _ : Fin i, ‖(ContinuousLinearMap.snd ℝ X Y)‖ ≤ 1 := by
    intro i
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    exact pow_le_one₀ (norm_nonneg _) (ContinuousLinearMap.norm_snd_le ℝ X Y)
  rw [Work.CR.Flat.holderNorm, Work.CR.Flat.holderNorm]
  refine Finset.sum_le_sum fun i hi => ?_
  have hik : i ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  refine add_le_add ?_ ?_
  · rw [Work.CR.Flat.iterDerivNorm, Work.CR.Flat.iterDerivNorm]
    refine iSup₂_le fun p hp => ?_
    rw [hderiv i hik p hp.2]
    refine le_trans (ENNReal.ofReal_le_ofReal ?_) (le_iSup₂_of_le p.2 hp.2 le_rfl)
    calc ‖(iteratedFDerivWithin ℝ i f V p.2).compContinuousLinearMap
            (fun _ => (ContinuousLinearMap.snd ℝ X Y))‖
        ≤ ‖iteratedFDerivWithin ℝ i f V p.2‖ * ∏ _ : Fin i,
            ‖(ContinuousLinearMap.snd ℝ X Y)‖ :=
          ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _
      _ ≤ ‖iteratedFDerivWithin ℝ i f V p.2‖ * 1 :=
          mul_le_mul_of_nonneg_left (hprod i) (norm_nonneg _)
      _ = ‖iteratedFDerivWithin ℝ i f V p.2‖ := mul_one _
  · rw [Work.CR.Flat.holderSeminorm, Work.CR.Flat.holderSeminorm]
    refine iSup₂_le fun p hp => iSup₂_le fun q hq => iSup_le fun hpq => ?_
    rw [hderiv i hik p hp.2, hderiv i hik q hq.2]
    by_cases hpq2 : p.2 = q.2
    · simp [hpq2]
    · have hsub : (iteratedFDerivWithin ℝ i f V p.2).compContinuousLinearMap
              (fun _ => (ContinuousLinearMap.snd ℝ X Y))
            - (iteratedFDerivWithin ℝ i f V q.2).compContinuousLinearMap
              (fun _ => (ContinuousLinearMap.snd ℝ X Y))
          = ((iteratedFDerivWithin ℝ i f V p.2)
              - (iteratedFDerivWithin ℝ i f V q.2)).compContinuousLinearMap
              (fun _ => (ContinuousLinearMap.snd ℝ X Y)) := by
        ext m
        simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply, sub_apply]
      rw [hsub]
      refine le_trans (ENNReal.ofReal_le_ofReal ?_)
        (le_holderSeminorm i α f V hp.2 hq.2 hpq2)
      have hnorm : ‖((iteratedFDerivWithin ℝ i f V p.2)
            - (iteratedFDerivWithin ℝ i f V q.2)).compContinuousLinearMap
            (fun _ => (ContinuousLinearMap.snd ℝ X Y))‖
          ≤ ‖(iteratedFDerivWithin ℝ i f V p.2)
              - (iteratedFDerivWithin ℝ i f V q.2)‖ := by
        calc _ ≤ ‖(iteratedFDerivWithin ℝ i f V p.2)
                - (iteratedFDerivWithin ℝ i f V q.2)‖
              * ∏ _ : Fin i, ‖(ContinuousLinearMap.snd ℝ X Y)‖ :=
              ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _
          _ ≤ _ * 1 := mul_le_mul_of_nonneg_left (hprod i) (norm_nonneg _)
          _ = _ := mul_one _
      refine le_trans (div_le_div_of_nonneg_right hnorm (Real.rpow_nonneg (norm_nonneg _) α)) ?_
      refine div_le_div_of_nonneg_left (norm_nonneg _) (Real.rpow_pos_of_pos ?_ α) ?_
      · exact norm_pos_iff.mpr (sub_ne_zero.mpr hpq2)
      · have hle : ‖p.2 - q.2‖ ≤ ‖p - q‖ := by
          have := norm_snd_le (p - q)
          simpa using this
        exact Real.rpow_le_rpow (norm_nonneg _) hle hα.le

/-! ## The cutoff has finite `C^{k,α}` norm on `U ×ˢ annR b` -/

theorem holderNorm_cutFun {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] {α : ℝ}
    (hα : 0 < α) (hα1 : α ≤ 1) (b : ℝ) (hb : 2 ≤ b) :
    ∃ D : ℕ → ℝ, (∀ k, 0 < D k) ∧
      ∀ (k : ℕ) (U : Set X), IsOpen U →
        Work.CR.Flat.holderNorm k α (Work.NN.DiscRadial.cutFun (X := X) b)
          (U ×ˢ Work.NN.DiscRadial.annR b) ≤ ENNReal.ofReal (D k) := by
  refine ⟨fun k => (Work.CR.Flat.holderNorm k α (cutRadial b) Set.univ).toReal + 1, ?_, ?_⟩
  · intro k
    have := ENNReal.toReal_nonneg (a := Work.CR.Flat.holderNorm k α (cutRadial b) Set.univ)
    linarith
  · intro k U hU
    have hann : IsOpen (annR b) := isOpen_annR b
    have hUann : IsOpen (U ×ˢ annR b) := hU.prod hann
    have hfin : Work.CR.Flat.holderNorm k α (cutRadial b) Set.univ ≠ ⊤ :=
      Work.CR.Flat.Cauchy.holderNorm_univ_ne_top_of_hasCompactSupport' (X := ℂ) hα.le hα1
        (contDiff_cutRadial b ((k + 1 : ℕ) : ℕ∞)) (hasCompactSupport_cutRadial b)
    have hcongr : Work.CR.Flat.holderNorm k α (cutFun (X := X) b) (U ×ˢ annR b)
        = Work.CR.Flat.holderNorm k α (fun p : X × ℂ => cutRadial b p.2) (U ×ˢ annR b) :=
      Work.NN.Final.holderNorm_congr_of_isOpen hUann
        (fun p hp => (cutRadial_snd_eq_cutFun (X := X) hb hp.2).symm) k α
    calc Work.CR.Flat.holderNorm k α (cutFun (X := X) b) (U ×ˢ annR b)
        = Work.CR.Flat.holderNorm k α (fun p : X × ℂ => cutRadial b p.2)
            (U ×ˢ annR b) := hcongr
      _ ≤ Work.CR.Flat.holderNorm k α (fun p : X × ℂ => cutRadial b p.2)
            (Set.univ ×ˢ annR b) :=
          Work.CR.Flat.holderNorm_mono_set (isOpen_univ.prod hann) hUann
            (Set.prod_mono (Set.subset_univ U) subset_rfl) k α _
      _ ≤ Work.CR.Flat.holderNorm k α (cutRadial b) (annR b) :=
          holderNorm_snd_le hα hann
            (fun i _ => ((contDiff_cutRadial b ((i : ℕ) : ℕ∞)).contDiffOn).mono
              (Set.subset_univ _))
      _ ≤ Work.CR.Flat.holderNorm k α (cutRadial b) Set.univ :=
          Work.CR.Flat.holderNorm_mono_set isOpen_univ hann (Set.subset_univ _) k α _
      _ ≤ ENNReal.ofReal
            ((Work.CR.Flat.holderNorm k α (cutRadial b) Set.univ).toReal + 1) :=
          calc Work.CR.Flat.holderNorm k α (cutRadial b) Set.univ
              = ENNReal.ofReal (Work.CR.Flat.holderNorm k α (cutRadial b) Set.univ).toReal :=
                (ENNReal.ofReal_toReal hfin).symm
            _ ≤ ENNReal.ofReal
                  ((Work.CR.Flat.holderNorm k α (cutRadial b) Set.univ).toReal + 1) :=
                ENNReal.ofReal_le_ofReal (le_add_of_nonneg_right (by norm_num : (0 : ℝ) ≤ 1))

end Work.NN.DiscRadial
