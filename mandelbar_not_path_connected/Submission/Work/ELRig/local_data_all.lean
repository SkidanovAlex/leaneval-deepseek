import Mathlib
import Submission.Work.ELRig.CylLift
import Submission.Work.ELRig.TailBand
import Submission.Work.ELRig.chart_sphere_crossings

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Classical Filter Set
open scoped Topology

noncomputable section

namespace Work.ELRig

/-- If `φ` is differentiable at `s₀` with nonvanishing derivative `D`, then near `s₀` (and off it)
the quantity `(φ s - φ s₀) * (s - s₀) * D` is positive: the transversal sign condition. -/
private theorem exists_sign_neighbourhood (φ : ℝ → ℝ) (x₀ s₀ : ℝ) (hφ : φ s₀ = x₀)
    (D : ℝ) (hD : D ≠ 0) (hderiv : HasDerivAt φ D s₀) :
    ∃ η₁ > 0, ∀ s, 0 < |s - s₀| → |s - s₀| < η₁ → 0 < (φ s - x₀) * (s - s₀) * D := by
  have hDabs : 0 < |D| := abs_pos.mpr hD
  have hε : 0 < |D| / 2 := by linarith
  have hslope : Tendsto (fun s => (φ s - φ s₀) / (s - s₀)) (𝓝[≠] s₀) (𝓝 D) := by
    simpa only [slope_fun_def_field] using hderiv.tendsto_slope
  have hev : ∀ᶠ s in 𝓝[≠] s₀, (φ s - φ s₀) / (s - s₀) ∈ Metric.ball D (|D| / 2) :=
    hslope (Metric.ball_mem_nhds D hε)
  rw [eventually_nhdsWithin_iff] at hev
  obtain ⟨η₁, hη₁pos, hη₁⟩ := Metric.eventually_nhds_iff.mp hev
  refine ⟨η₁, hη₁pos, fun s hs0 hslt => ?_⟩
  have hsne : s ≠ s₀ := by rintro rfl; simp at hs0
  have hmem : (φ s - φ s₀) / (s - s₀) ∈ Metric.ball D (|D| / 2) := by
    refine hη₁ ?_ hsne
    rw [Real.dist_eq]; exact hslt
  rw [Metric.mem_ball, Real.dist_eq] at hmem
  have hq := abs_lt.mp hmem
  set q := (φ s - φ s₀) / (s - s₀) with hqdef
  have hqd : q * D > 0 := by
    rcases lt_or_gt_of_ne hD with hDneg | hDpos
    · have h2 : q < D / 2 := by
        have := hq.2; rw [abs_of_neg hDneg] at this; linarith
      nlinarith [hDneg, h2]
    · have h2 : q > D / 2 := by
        have := hq.1; rw [abs_of_pos hDpos] at this; linarith
      nlinarith [hDpos, h2]
  have hqx : φ s - x₀ = q * (s - s₀) := by
    rw [hqdef, hφ]; field_simp
  rw [hqx]
  have hsq : 0 < (s - s₀) * (s - s₀) := mul_self_pos.mpr (sub_ne_zero.mpr hsne)
  nlinarith [hqd, hsq]

theorem local_data_all {c : ℂ} (d : Work.EL.RootParabolic c)
    (fl : Work.EL.ParabolicFlower (Work.EL.F c) ((LeanEval.ComplexAnalysis.Tantibar c)^[5]) d.z₁)
    (L : Work.ELRig.RayCylLift d fl) {x₀ : ℝ} (hx : x₀ < -L.R) {s₀ : ℝ} (hs : (L.γ₁ s₀).re = x₀)
    (hcross : deriv (fun t : ℝ => (L.γ₁ t).re) s₀ ≠ 0) :
    ∃ ρ₀ > 0, ∃ η > 0,
      (∀ s : ℝ, 0 < |s - s₀| → |s - s₀| < η →
        0 < ((L.γ₁ s).re - x₀) * (s - s₀) * deriv (fun t : ℝ => (L.γ₁ t).re) s₀) ∧
      (∀ ρ : ℝ, 0 < ρ → ρ ≤ ρ₀ → ∃ s₁ s₂ : ℝ, s₁ < s₀ ∧ s₀ < s₂ ∧
        (∀ s ∈ Set.Icc s₁ s₂, s ≠ s₁ → s ≠ s₂ → dist (L.γ₁ s) (L.γ₁ s₀) < ρ) ∧
        dist (L.γ₁ s₁) (L.γ₁ s₀) = ρ ∧ dist (L.γ₁ s₂) (L.γ₁ s₀) = ρ ∧
        (∀ s : ℝ, dist (L.γ₁ s) (L.γ₁ s₀) < ρ → s ∈ Set.Ioo s₁ s₂) ∧
        (∀ s : ℝ, dist (L.γ₁ s) (L.γ₁ s₀) ≤ ρ → |s - s₀| < η)) := by
  have hre : (L.γ₁ s₀).re < -L.R := by rw [hs]; exact hx
  have hdiff : DifferentiableAt ℝ (fun t : ℝ => (L.γ₁ t).re) s₀ := by
    by_contra h
    exact hcross (deriv_zero_of_not_differentiableAt h)
  have hderiv : HasDerivAt (fun t : ℝ => (L.γ₁ t).re)
      (deriv (fun t : ℝ => (L.γ₁ t).re) s₀) s₀ := hdiff.hasDerivAt
  obtain ⟨η₁, hη₁pos, hsign⟩ :=
    exists_sign_neighbourhood (fun t : ℝ => (L.γ₁ t).re) x₀ s₀ hs
      (deriv (fun t : ℝ => (L.γ₁ t).re) s₀) hcross hderiv
  obtain ⟨δ', hδ'pos, r_loc, hr_loc_pos, hloc⟩ := Work.ELRig.local_exit_crossings (L := L) hre
  obtain ⟨ε_no, hεnopos, hno⟩ :=
    Work.ELRig.exists_no_crossing_radius L.cont₁ (Work.ELRig.rayCylLift_injective L)
      (Work.ELRig.rayCylLift_norm_growth L) (s₀ := s₀) rfl hδ'pos
  set η : ℝ := min η₁ δ' with hηdef
  have hηpos : 0 < η := by rw [hηdef]; exact lt_min hη₁pos hδ'pos
  have hη_le_η₁ : η ≤ η₁ := by rw [hηdef]; exact min_le_left _ _
  have hη_le_δ' : η ≤ δ' := by rw [hηdef]; exact min_le_right _ _
  have hFcont : Continuous (fun s : ℝ => dist (L.γ₁ s) (L.γ₁ s₀)) :=
    continuous_dist.comp (L.cont₁.prodMk continuous_const)
  have hKne : (Set.Icc (s₀ - δ') (s₀ - η)).Nonempty :=
    ⟨s₀ - δ', Set.mem_Icc.mpr ⟨le_rfl, by linarith [hη_le_δ']⟩⟩
  have hKpos : ∀ s ∈ Set.Icc (s₀ - δ') (s₀ - η), 0 < dist (L.γ₁ s) (L.γ₁ s₀) := by
    intro s hsmem
    have hne : dist (L.γ₁ s) (L.γ₁ s₀) ≠ 0 := by
      intro h0
      have heq : L.γ₁ s = L.γ₁ s₀ := dist_eq_zero.mp h0
      have hs_eq : s = s₀ := Work.ELRig.rayCylLift_injective L heq
      have hthis : s ≤ s₀ - η := hsmem.2
      rw [hs_eq] at hthis
      linarith [hηpos]
    exact lt_of_le_of_ne dist_nonneg (Ne.symm hne)
  obtain ⟨m, hmK, hmmin⟩ := isCompact_Icc.exists_isMinOn hKne hFcont.continuousOn
  have hmpos : 0 < dist (L.γ₁ m) (L.γ₁ s₀) := hKpos m hmK
  have hK₂ne : (Set.Icc (s₀ + η) (s₀ + δ')).Nonempty :=
    ⟨s₀ + η, Set.mem_Icc.mpr ⟨le_rfl, by linarith [hη_le_δ']⟩⟩
  have hK₂pos : ∀ s ∈ Set.Icc (s₀ + η) (s₀ + δ'), 0 < dist (L.γ₁ s) (L.γ₁ s₀) := by
    intro s hsmem
    have hne : dist (L.γ₁ s) (L.γ₁ s₀) ≠ 0 := by
      intro h0
      have heq : L.γ₁ s = L.γ₁ s₀ := dist_eq_zero.mp h0
      have hs_eq : s = s₀ := Work.ELRig.rayCylLift_injective L heq
      have hthis : s₀ + η ≤ s := hsmem.1
      rw [hs_eq] at hthis
      linarith [hηpos]
    exact lt_of_le_of_ne dist_nonneg (Ne.symm hne)
  obtain ⟨m₂, hm₂K, hm₂min⟩ := isCompact_Icc.exists_isMinOn hK₂ne hFcont.continuousOn
  have hm₂pos : 0 < dist (L.γ₁ m₂) (L.γ₁ s₀) := hK₂pos m₂ hm₂K
  set C : ℝ := min ε_no
      (min r_loc (min (dist (L.γ₁ m) (L.γ₁ s₀)) (dist (L.γ₁ m₂) (L.γ₁ s₀)))) with hCdef
  have hCpos : 0 < C := by
    rw [hCdef]
    exact lt_min hεnopos (lt_min hr_loc_pos (lt_min hmpos hm₂pos))
  set ρ₀ : ℝ := C / 2 with hρ₀def
  have hρ₀pos : 0 < ρ₀ := by rw [hρ₀def]; linarith
  have hρ₀_lt_C : ρ₀ < C := by rw [hρ₀def]; linarith
  have hC_le_ε : C ≤ ε_no := by rw [hCdef]; exact min_le_left _ _
  have hC_le_rloc : C ≤ r_loc := by
    rw [hCdef]; exact le_trans (min_le_right _ _) (min_le_left _ _)
  have hC_le_m : C ≤ dist (L.γ₁ m) (L.γ₁ s₀) := by
    rw [hCdef]; exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _))
  have hC_le_m₂ : C ≤ dist (L.γ₁ m₂) (L.γ₁ s₀) := by
    rw [hCdef]; exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _))
  refine ⟨ρ₀, hρ₀pos, η, hηpos, ?_, ?_⟩
  · intro s hs0 hslt
    exact hsign s hs0 (lt_of_lt_of_le hslt hη_le_η₁)
  · intro ρ hρpos hρle
    have hρ_lt_C : ρ < C := lt_of_le_of_lt hρle hρ₀_lt_C
    have hρ_lt_ε : ρ < ε_no := lt_of_lt_of_le hρ_lt_C hC_le_ε
    have hρ_lt_rloc : ρ < r_loc := lt_of_lt_of_le hρ_lt_C hC_le_rloc
    have hρ_lt_m : ρ < dist (L.γ₁ m) (L.γ₁ s₀) := lt_of_lt_of_le hρ_lt_C hC_le_m
    have hρ_lt_m₂ : ρ < dist (L.γ₁ m₂) (L.γ₁ s₀) := lt_of_lt_of_le hρ_lt_C hC_le_m₂
    obtain ⟨⟨sL, ⟨hsLmem, hsLeq⟩, hsLuniq⟩, ⟨sR, ⟨hsRmem, hsReq⟩, hsRuniq⟩⟩ :=
      hloc ρ ⟨hρpos, hρ_lt_rloc⟩
    have hFsL : dist (L.γ₁ sL) (L.γ₁ s₀) = ρ := by rw [dist_eq_norm]; exact hsLeq
    have hFsR : dist (L.γ₁ sR) (L.γ₁ s₀) = ρ := by rw [dist_eq_norm]; exact hsReq
    have hsL_g1 : s₀ - δ' < sL := hsLmem.1
    have hsL_g2 : sL < s₀ := hsLmem.2
    have hsR_g1 : s₀ < sR := hsRmem.1
    have hsR_g2 : sR < s₀ + δ' := hsRmem.2
    have hwin : ∀ s, dist (L.γ₁ s) (L.γ₁ s₀) < ρ → s ∈ Set.Ioo (s₀ - δ') (s₀ + δ') := by
      intro s hslt
      refine hno s ?_
      rw [dist_eq_norm] at hslt
      exact lt_of_lt_of_le hslt hρ_lt_ε.le
    have hleftmid : ∀ s, s ∈ Set.Ioo sL s₀ → dist (L.γ₁ s) (L.γ₁ s₀) < ρ := by
      intro s hsio
      by_contra hcon
      rw [not_lt] at hcon
      rcases lt_or_eq_of_le hcon with hgt | heq
      · obtain ⟨cc, hcmem, hceq⟩ := intermediate_value_Icc'
          (f := fun t : ℝ => dist (L.γ₁ t) (L.γ₁ s₀)) (le_of_lt hsio.2) hFcont.continuousOn
          (show ρ ∈ Set.Icc (dist (L.γ₁ s₀) (L.γ₁ s₀)) (dist (L.γ₁ s) (L.γ₁ s₀)) from
            ⟨by rw [dist_self]; exact hρpos.le, hgt.le⟩)
        have hceq_d : dist (L.γ₁ cc) (L.γ₁ s₀) = ρ := hceq
        have hceq' : ‖L.γ₁ cc - L.γ₁ s₀‖ = ρ := by rw [dist_eq_norm] at hceq_d; exact hceq_d
        have hc1 : s₀ - δ' < cc := lt_of_lt_of_le (lt_trans hsL_g1 hsio.1) hcmem.1
        have hc2 : cc < s₀ := by
          rcases lt_or_eq_of_le hcmem.2 with h | h
          · exact h
          · exfalso; rw [h, dist_self] at hceq_d; linarith [hρpos]
        have hc_eq : cc = sL := hsLuniq cc ⟨⟨hc1, hc2⟩, hceq'⟩
        linarith [hcmem.1, hsio.1, hc_eq]
      · have heq' : ‖L.γ₁ s - L.γ₁ s₀‖ = ρ := by rw [dist_eq_norm] at heq; exact heq.symm
        have hc_eq : s = sL := hsLuniq s ⟨⟨lt_trans hsL_g1 hsio.1, hsio.2⟩, heq'⟩
        linarith [hsio.1, hc_eq]
    have hmval_le : dist (L.γ₁ m) (L.γ₁ s₀) ≤ dist (L.γ₁ (s₀ - δ')) (L.γ₁ s₀) :=
      hmmin (Set.mem_Icc.mpr ⟨le_rfl, by linarith [hη_le_δ']⟩)
    have hFδ'_gt : dist (L.γ₁ (s₀ - δ')) (L.γ₁ s₀) > ρ :=
      lt_of_lt_of_le hρ_lt_m hmval_le
    have hleftouter : ∀ s, s ∈ Set.Ioo (s₀ - δ') sL → dist (L.γ₁ s) (L.γ₁ s₀) > ρ := by
      intro s hsio
      by_contra hcon
      rw [not_lt] at hcon
      rcases lt_or_eq_of_le hcon with hlt | heq
      · obtain ⟨cc, hcmem, hceq⟩ := intermediate_value_Icc'
          (f := fun t : ℝ => dist (L.γ₁ t) (L.γ₁ s₀)) (le_of_lt hsio.1) hFcont.continuousOn
          (show ρ ∈ Set.Icc (dist (L.γ₁ s) (L.γ₁ s₀)) (dist (L.γ₁ (s₀ - δ')) (L.γ₁ s₀)) from
            ⟨hlt.le, hFδ'_gt.le⟩)
        have hceq_d : dist (L.γ₁ cc) (L.γ₁ s₀) = ρ := hceq
        have hceq' : ‖L.γ₁ cc - L.γ₁ s₀‖ = ρ := by rw [dist_eq_norm] at hceq_d; exact hceq_d
        have hc1 : s₀ - δ' < cc := by
          rcases lt_or_eq_of_le hcmem.1 with h | h
          · exact h
          · exfalso; rw [← h] at hceq_d; linarith [hFδ'_gt, hceq_d]
        have hc2 : cc < sL := lt_of_le_of_lt hcmem.2 hsio.2
        have hc_eq : cc = sL := hsLuniq cc ⟨⟨hc1, lt_trans hc2 hsL_g2⟩, hceq'⟩
        linarith [hc2, hc_eq]
      · have heq' : ‖L.γ₁ s - L.γ₁ s₀‖ = ρ := by rw [dist_eq_norm] at heq; exact heq
        have hc_eq : s = sL := hsLuniq s ⟨⟨hsio.1, lt_trans hsio.2 hsL_g2⟩, heq'⟩
        linarith [hsio.2, hc_eq]
    have hrightmid : ∀ s, s ∈ Set.Ioo s₀ sR → dist (L.γ₁ s) (L.γ₁ s₀) < ρ := by
      intro s hsio
      by_contra hcon
      rw [not_lt] at hcon
      rcases lt_or_eq_of_le hcon with hgt | heq
      · obtain ⟨cc, hcmem, hceq⟩ := intermediate_value_Icc
          (f := fun t : ℝ => dist (L.γ₁ t) (L.γ₁ s₀)) (le_of_lt hsio.1) hFcont.continuousOn
          (show ρ ∈ Set.Icc (dist (L.γ₁ s₀) (L.γ₁ s₀)) (dist (L.γ₁ s) (L.γ₁ s₀)) from
            ⟨by rw [dist_self]; exact hρpos.le, hgt.le⟩)
        have hceq_d : dist (L.γ₁ cc) (L.γ₁ s₀) = ρ := hceq
        have hceq' : ‖L.γ₁ cc - L.γ₁ s₀‖ = ρ := by rw [dist_eq_norm] at hceq_d; exact hceq_d
        have hc1 : s₀ < cc := by
          rcases lt_or_eq_of_le hcmem.1 with h | h
          · exact h
          · exfalso; rw [← h, dist_self] at hceq_d; linarith [hρpos]
        have hc2 : cc < s₀ + δ' := lt_of_le_of_lt hcmem.2 (lt_trans hsio.2 hsR_g2)
        have hc_eq : cc = sR := hsRuniq cc ⟨⟨hc1, hc2⟩, hceq'⟩
        linarith [hcmem.2, hsio.2, hc_eq]
      · have heq' : ‖L.γ₁ s - L.γ₁ s₀‖ = ρ := by rw [dist_eq_norm] at heq; exact heq.symm
        have hc_eq : s = sR := hsRuniq s ⟨⟨hsio.1, lt_trans hsio.2 hsR_g2⟩, heq'⟩
        linarith [hsio.2, hc_eq]
    have hm₂val_le : dist (L.γ₁ m₂) (L.γ₁ s₀) ≤ dist (L.γ₁ (s₀ + δ')) (L.γ₁ s₀) :=
      hm₂min (Set.mem_Icc.mpr ⟨by linarith [hη_le_δ'], le_rfl⟩)
    have hFδ''_gt : dist (L.γ₁ (s₀ + δ')) (L.γ₁ s₀) > ρ :=
      lt_of_lt_of_le hρ_lt_m₂ hm₂val_le
    have hrightouter : ∀ s, s ∈ Set.Ioo sR (s₀ + δ') → dist (L.γ₁ s) (L.γ₁ s₀) > ρ := by
      intro s hsio
      by_contra hcon
      rw [not_lt] at hcon
      rcases lt_or_eq_of_le hcon with hlt | heq
      · obtain ⟨cc, hcmem, hceq⟩ := intermediate_value_Icc
          (f := fun t : ℝ => dist (L.γ₁ t) (L.γ₁ s₀)) (le_of_lt hsio.2) hFcont.continuousOn
          (show ρ ∈ Set.Icc (dist (L.γ₁ s) (L.γ₁ s₀)) (dist (L.γ₁ (s₀ + δ')) (L.γ₁ s₀)) from
            ⟨hlt.le, hFδ''_gt.le⟩)
        have hceq_d : dist (L.γ₁ cc) (L.γ₁ s₀) = ρ := hceq
        have hceq' : ‖L.γ₁ cc - L.γ₁ s₀‖ = ρ := by rw [dist_eq_norm] at hceq_d; exact hceq_d
        have hc1 : sR < cc := lt_of_lt_of_le hsio.1 hcmem.1
        have hc2 : cc < s₀ + δ' := by
          rcases lt_or_eq_of_le hcmem.2 with h | h
          · exact h
          · exfalso; rw [h] at hceq_d; linarith [hFδ''_gt, hceq_d]
        have hc_eq : cc = sR := hsRuniq cc ⟨⟨lt_trans hsR_g1 hc1, hc2⟩, hceq'⟩
        linarith [hc1, hc_eq]
      · have heq' : ‖L.γ₁ s - L.γ₁ s₀‖ = ρ := by rw [dist_eq_norm] at heq; exact heq
        have hc_eq : s = sR := hsRuniq s ⟨⟨lt_trans hsR_g1 hsio.1, hsio.2⟩, heq'⟩
        linarith [hsio.1, hc_eq]
    have hsL_gt : s₀ - η < sL := by
      by_contra hcon
      rw [not_lt] at hcon
      have hmemK : sL ∈ Set.Icc (s₀ - δ') (s₀ - η) := ⟨hsL_g1.le, hcon⟩
      have hle : dist (L.γ₁ m) (L.γ₁ s₀) ≤ dist (L.γ₁ sL) (L.γ₁ s₀) := hmmin hmemK
      rw [hFsL] at hle
      linarith [hρ_lt_m, hle]
    have hsR_lt : sR < s₀ + η := by
      by_contra hcon
      rw [not_lt] at hcon
      have hmemK : sR ∈ Set.Icc (s₀ + η) (s₀ + δ') := ⟨hcon, hsR_g2.le⟩
      have hle : dist (L.γ₁ m₂) (L.γ₁ s₀) ≤ dist (L.γ₁ sR) (L.γ₁ s₀) := hm₂min hmemK
      rw [hFsR] at hle
      linarith [hρ_lt_m₂, hle]
    have hlt_Ioo : ∀ s, dist (L.γ₁ s) (L.γ₁ s₀) < ρ → s ∈ Set.Ioo sL sR := by
      intro s hslt
      have hsB := hwin s hslt
      refine ⟨?_, ?_⟩
      · by_contra hcon; rw [not_lt] at hcon
        rcases lt_or_eq_of_le hcon with h | h
        · exact absurd hslt (not_lt_of_gt (hleftouter s ⟨hsB.1, h⟩))
        · rw [h, hFsL] at hslt; exact absurd hslt (lt_irrefl ρ)
      · by_contra hcon; rw [not_lt] at hcon
        rcases lt_or_eq_of_le hcon with h | h
        · exact absurd hslt (not_lt_of_gt (hrightouter s ⟨h, hsB.2⟩))
        · rw [← h, hFsR] at hslt; exact absurd hslt (lt_irrefl ρ)
    refine ⟨sL, sR, hsL_g2, hsR_g1, ?_, hFsL, hFsR, hlt_Ioo, ?_⟩
    · intro s hsmem h1 h2
      have hsio : s ∈ Set.Ioo sL sR :=
        ⟨lt_of_le_of_ne (Set.mem_Icc.mp hsmem).1 (Ne.symm h1),
         lt_of_le_of_ne (Set.mem_Icc.mp hsmem).2 h2⟩
      rcases lt_trichotomy s s₀ with h | h | h
      · exact hleftmid s ⟨hsio.1, h⟩
      · subst h; rw [dist_self]; exact hρpos
      · exact hrightmid s ⟨h, hsio.2⟩
    · intro s hsle
      have hsle' : ‖L.γ₁ s - L.γ₁ s₀‖ < ε_no := by
        rw [dist_eq_norm] at hsle
        exact lt_of_le_of_lt hsle hρ_lt_ε
      have hsB := hno s hsle'
      rcases lt_or_eq_of_le hsle with hlt | heq
      · have hio := hlt_Ioo s hlt
        rw [abs_lt]
        exact ⟨by linarith [hio.1, hsL_gt, hηpos], by linarith [hio.2, hsR_lt, hηpos]⟩
      · have hmem : s = sL ∨ s = sR := by
          rcases lt_trichotomy s s₀ with h | h | h
          · left
            have heq' : ‖L.γ₁ s - L.γ₁ s₀‖ = ρ := by rw [dist_eq_norm] at heq; exact heq
            exact hsLuniq s ⟨⟨hsB.1, h⟩, heq'⟩
          · exfalso; subst h; rw [dist_self] at heq; linarith [hρpos]
          · right
            have heq' : ‖L.γ₁ s - L.γ₁ s₀‖ = ρ := by rw [dist_eq_norm] at heq; exact heq
            exact hsRuniq s ⟨⟨h, hsB.2⟩, heq'⟩
        rcases hmem with h | h
        · rw [h, abs_lt]
          exact ⟨by linarith [hsL_gt, hηpos], by linarith [hsL_g2, hηpos]⟩
        · rw [h, abs_lt]
          exact ⟨by linarith [hsR_g1, hηpos], by linarith [hsR_lt, hηpos]⟩

end Work.ELRig
