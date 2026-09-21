import Mathlib
import Submission.Commons.Geometry.Ulam.volterra_perturbation_exists_v3

noncomputable section

open scoped Topology
open Filter Set
open MeasureTheory
open scoped Interval

set_option linter.unusedVariables false
set_option maxHeartbeats 800000

namespace Commons.Geometry.Ulam

lemma volterra_perturbation_exists_continuous_theta_small
    {a b : ℝ} (hab : a < b)
    {G0 : ℝ → EuclideanSpace ℝ (Fin 4) → EuclideanSpace ℝ (Fin 4)}
    {Θ0 : ℝ → ℝ → EuclideanSpace ℝ (Fin 4) → EuclideanSpace ℝ (Fin 4)}
    {Ξ0 : ℝ → EuclideanSpace ℝ (Fin 4)} {Z0 : ℝ → EuclideanSpace ℝ (Fin 4)}
    {Q : EuclideanSpace ℝ (Fin 4) ≃L[ℝ] EuclideanSpace ℝ (Fin 4)}
    {B_G0 B_Θ0 B_Ξ0 : ℝ} {K_G L_Θ : NNReal}
    (hcontract : (K_G : ℝ) + ‖(Q.symm : EuclideanSpace ℝ (Fin 4) →L[ℝ] EuclideanSpace ℝ (Fin 4))‖ * (L_Θ : ℝ) * (b - a) < 1)
    (hQ : fderiv ℝ (fun z : EuclideanSpace ℝ (Fin 4) => G0 b z) (Z0 b) = Q.toContinuousLinearMap)
    (hG0_bound : ∀ s ∈ Set.Icc a b, ∀ z ∈ Metric.closedBall (Z0 b) 1, ‖G0 s z‖ ≤ B_G0)
    (hΘ0_bound : ∀ s ∈ Set.Icc a b, ∀ σ ∈ Set.Icc a b, ∀ z ∈ Metric.closedBall (Z0 b) 1,
      ‖Θ0 s σ z‖ ≤ B_Θ0)
    (hΞ0_bound : ∀ s ∈ Set.Icc a b, ‖Ξ0 s‖ ≤ B_Ξ0)
    (hbase : ∀ s ∈ Set.Icc a b,
      G0 s (Z0 s) = (∫ σ in s..b, Θ0 s σ (Z0 σ)) + Ξ0 s)
    (hdet : (fderiv ℝ (fun z : EuclideanSpace ℝ (Fin 4) => G0 b z) (Z0 b)).det ≠ 0)
    (hG_cont_at_base : ContinuousAt
      (fun p : ℝ × EuclideanSpace ℝ (Fin 4) => fderiv ℝ (fun z => G0 p.1 z) p.2) (b, Z0 b))
    (hZ0_cont : ContinuousOn Z0 (Set.Icc a b))
    (hΘ0_cont : ContinuousOn (fun p : ℝ × ℝ × EuclideanSpace ℝ (Fin 4) => Θ0 p.1 p.2.1 p.2.2)
      (Set.Icc a b ×ˢ Set.Icc a b ×ˢ Metric.closedBall (Z0 b) 1)) :
    ∃ ε > 0, ∃ δ > 0, ε ≤ 1 / 4 ∧ δ ≤ (b - a) / 3 ∧
    ∀ (G : ℝ → EuclideanSpace ℝ (Fin 4) → EuclideanSpace ℝ (Fin 4))
      (Θ : ℝ → ℝ → EuclideanSpace ℝ (Fin 4) → EuclideanSpace ℝ (Fin 4))
      (Ξ : ℝ → EuclideanSpace ℝ (Fin 4)),
      Continuous (fun p : ℝ × EuclideanSpace ℝ (Fin 4) => G p.1 p.2) →
      Continuous (fun p : ℝ × ℝ × EuclideanSpace ℝ (Fin 4) => Θ p.1 p.2.1 p.2.2) →
      Continuous Ξ →
      (∀ s ∈ Set.Icc a b, ∀ z ∈ Metric.closedBall (Z0 b) 1,
        dist (G s z) (G0 s z) < ε) →
      (∀ s ∈ Set.Icc a b, ∀ σ ∈ Set.Icc a b, ∀ z ∈ Metric.closedBall (Z0 b) 1,
        dist (Θ s σ z) (Θ0 s σ z) < ε) →
      (∀ s ∈ Set.Icc a b, dist (Ξ s) (Ξ0 s) < ε) →
      (∀ s ∈ Set.Icc a b, LipschitzOnWith K_G (fun z : EuclideanSpace ℝ (Fin 4) =>
        z - Q.symm (G s z)) (Metric.closedBall (Z0 b) 1)) →
      (∀ s ∈ Set.Icc a b, ∀ σ ∈ Set.Icc a b, LipschitzOnWith L_Θ
        (fun z : EuclideanSpace ℝ (Fin 4) => Θ s σ z) (Metric.closedBall (Z0 b) 1)) →
        ∃ Z : ℝ → EuclideanSpace ℝ (Fin 4),
          ContinuousOn Z (Set.Icc (b - 3 * δ) b) ∧
          (∀ s ∈ Set.Icc (b - 3 * δ) b,
            G s (Z s) = (∫ σ in s..b, Θ s σ (Z σ)) + Ξ s) ∧
          (∀ s ∈ Set.Icc (b - 3 * δ) b, dist (Z s) (Z0 s) < 1 / 2) := by
  classical
  let CQ : ℝ := ‖(Q.symm : EuclideanSpace ℝ (Fin 4) →L[ℝ] EuclideanSpace ℝ (Fin 4))‖
  let lam : ℝ := (K_G : ℝ) + CQ * (L_Θ : ℝ) * (b - a)
  have hb_sub_nonneg : 0 ≤ b - a := sub_nonneg.mpr hab.le
  have hCQ_nonneg : 0 ≤ CQ := by dsimp [CQ]; exact norm_nonneg _
  have hlam_nonneg : 0 ≤ lam := by dsimp [lam]; positivity
  have hlam_lt : lam < 1 := by dsimp [lam, CQ]; simpa using hcontract
  let r0 : ℝ := 1 / 4
  have hr0_pos : 0 < r0 := by norm_num [r0]
  have hr0_nonneg : 0 ≤ r0 := le_of_lt hr0_pos
  let margin : ℝ := (1 - lam) * r0
  have hmargin_pos : 0 < margin := by dsimp [margin]; positivity
  let den : ℝ := max 1 (CQ * (2 + (b - a)))
  have hden_pos : 0 < den := by dsimp [den]; exact lt_max_of_lt_left one_pos
  have hden_ne : den ≠ 0 := ne_of_gt hden_pos
  let ε : ℝ := min (1 / 4) (margin / den)
  have hε_pos : 0 < ε := by
    dsimp [ε]
    exact lt_min (by norm_num) (div_pos hmargin_pos hden_pos)
  have hε_le : ε ≤ 1 / 4 := by dsimp [ε]; exact min_le_left _ _
  have hε_den : ε ≤ margin / den := by dsimp [ε]; exact min_le_right _ _
  have hCQden : CQ * (2 + (b - a)) ≤ den := by dsimp [den]; exact le_max_right _ _
  have hsmall : CQ * (2 + (b - a)) * ε ≤ den * (margin / den) := by
    exact mul_le_mul hCQden hε_den (le_of_lt hε_pos) (le_of_lt hden_pos)
  have hden_mul : den * (margin / den) = margin := by field_simp [hden_ne]
  have hε_small : CQ * (2 + (b - a)) * ε ≤ margin := by simpa [hden_mul] using hsmall
  -- choose δ from continuity of Z0 at b
  let Z0sub : Set.Icc a b → EuclideanSpace ℝ (Fin 4) := fun s => Z0 s.1
  have hZ0sub_cont : Continuous Z0sub := by
    exact continuousOn_iff_continuous_domRestrict.mp hZ0_cont
  let Z0ext : ℝ → EuclideanSpace ℝ (Fin 4) := Set.IccExtend hab.le Z0sub
  have hZ0ext_cont : Continuous Z0ext := by
    dsimp [Z0ext]
    exact hZ0sub_cont.Icc_extend'
  have hZ0ext_of_mem : ∀ {s : ℝ}, s ∈ Set.Icc a b → Z0ext s = Z0 s := by
    intro s hs
    dsimp [Z0ext, Z0sub]
    exact Set.IccExtend_of_mem (h := hab.le) (f := Z0sub) hs
  have hb_mem : b ∈ Set.Icc a b := ⟨hab.le, le_rfl⟩
  have hZ0ext_b : Z0ext b = Z0 b := hZ0ext_of_mem hb_mem
  have hZ0contAt : ContinuousAt Z0ext b := hZ0ext_cont.continuousAt
  rcases (Metric.continuousAt_iff.mp hZ0contAt (1 / 2) (by norm_num)) with
    ⟨δZ, hδZ_pos, hδZ⟩
  let δ : ℝ := min ((b - a) / 3) (δZ / 4)
  have hδ_pos : 0 < δ := by
    dsimp [δ]
    exact lt_min (div_pos (sub_pos.mpr hab) (by norm_num)) (div_pos hδZ_pos (by norm_num))
  have hδ_le_ab : δ ≤ (b - a) / 3 := by dsimp [δ]; exact min_le_left _ _
  have hδ_lt_δZ : 3 * δ < δZ := by
    have h1 : δ ≤ δZ / 4 := by dsimp [δ]; exact min_le_right _ _
    nlinarith [hδZ_pos]
  refine ⟨ε, hε_pos, δ, hδ_pos, hε_le, hδ_le_ab, ?_⟩
  intro G Θ Ξ hG_cont hΘ_cont hΞ_cont hG_close hΘ_close hΞ_close hG_lip hΘ_lip
  let J : Set ℝ := Set.Icc (b - 3 * δ) b
  have hJle : b - 3 * δ ≤ b := by linarith [hδ_pos]
  have hJsub_ab : J ⊆ Set.Icc a b := by
    intro s hs
    rcases hs with ⟨hs1, hs2⟩
    have hlow : a ≤ b - 3 * δ := by
      have h3δ : 3 * δ ≤ b - a := by nlinarith [hδ_le_ab]
      linarith
    exact ⟨le_trans hlow hs1, hs2⟩
  let C : BoundedContinuousFunction J (EuclideanSpace ℝ (Fin 4)) :=
    BoundedContinuousFunction.mkOfCompact
      { toFun := fun s : J => Z0ext s.1
        continuous_toFun := hZ0ext_cont.comp continuous_subtype_val }
  have hC_val : ∀ s : J, C s = Z0ext (s : ℝ) := by intro s; rfl
  have hC_Z0 : ∀ s : J, C s = Z0 (s : ℝ) := by
    intro s
    rw [hC_val, hZ0ext_of_mem (hJsub_ab s.2)]
  let T : BoundedContinuousFunction J (EuclideanSpace ℝ (Fin 4)) →
          BoundedContinuousFunction J (EuclideanSpace ℝ (Fin 4)) :=
    volterraOpBcf (a := b - 3 * δ) (b := b) hJle Q G Θ Ξ hG_cont hΘ_cont hΞ_cont
  have hT_apply : ∀ (Z : BoundedContinuousFunction J (EuclideanSpace ℝ (Fin 4))) (s : J),
      (T Z) s = volterraOp (a := b - 3 * δ) (b := b) Q G Θ Ξ (bcfExt hJle Z) (s : ℝ) := by
    intro Z s
    exact volterraOpBcf_apply hJle Q G Θ Ξ hG_cont hΘ_cont hΞ_cont Z s
  let K_J_real : ℝ := (K_G : ℝ) + CQ * (L_Θ : ℝ) * (3 * δ)
  have hK_J_nonneg : 0 ≤ K_J_real := by dsimp [K_J_real]; positivity
  have hK_J_lt_real : K_J_real < 1 := by
    dsimp [K_J_real, lam]
    have hlen : 3 * δ ≤ b - a := by nlinarith [hδ_le_ab]
    have hL_nonneg : 0 ≤ (L_Θ : ℝ) := L_Θ.2
    have hmulnonneg : 0 ≤ CQ * (L_Θ : ℝ) := mul_nonneg hCQ_nonneg hL_nonneg
    have hle : CQ * (L_Θ : ℝ) * (3 * δ) ≤ CQ * (L_Θ : ℝ) * (b - a) :=
      mul_le_mul_of_nonneg_left hlen hmulnonneg
    nlinarith [hlam_lt, hle]
  let K_J : NNReal := ⟨K_J_real, hK_J_nonneg⟩
  have hK_J_lt : K_J < 1 := by
    exact_mod_cast hK_J_lt_real
  have hC_big : ∀ s : J, bcfExt hJle C (s : ℝ) ∈ Metric.closedBall (Z0 b) 1 := by
    intro s
    have hs_ab : (s : ℝ) ∈ Set.Icc a b := hJsub_ab s.2
    have hnear : dist (Z0ext (s : ℝ)) (Z0ext b) < 1 / 2 := by
      have hdist_sb : dist (s : ℝ) b < δZ := by
        rw [dist_eq_norm, Real.norm_eq_abs, abs_of_nonpos (sub_nonpos.mpr s.2.2)]
        have hle : b - (s : ℝ) ≤ 3 * δ := by linarith [s.2.1]
        nlinarith
      exact hδZ hdist_sb
    rw [Metric.mem_closedBall]
    have hCeq : bcfExt hJle C (s : ℝ) = C s := bcfExt_of_mem hJle C s.2
    rw [hCeq, hC_val]
    have hb_dist : dist (Z0ext (s : ℝ)) (Z0 b) < 1 / 2 := by
      simpa [hZ0ext_b] using hnear
    linarith
  have hZbig : ∀ Z : BoundedContinuousFunction J (EuclideanSpace ℝ (Fin 4)),
      Z ∈ Metric.closedBall C r0 → ∀ s : J, bcfExt hJle Z (s : ℝ) ∈ Metric.closedBall (Z0 b) 1 := by
    intro Z hZ s
    have hZ_le_C : dist Z C ≤ r0 := Metric.mem_closedBall.mp hZ
    have hpt := BoundedContinuousFunction.dist_coe_le_dist (f := Z) (g := C) s
    have hZCs : dist (bcfExt hJle Z (s : ℝ)) (C s) ≤ r0 := by
      rw [bcfExt_of_mem hJle Z s.2]
      exact hpt.trans hZ_le_C
    have hC_near : dist (C s) (Z0 b) < 1 / 2 := by
      rw [hC_val]
      have hnear : dist (Z0ext (s : ℝ)) (Z0ext b) < 1 / 2 := by
        have hdist_sb : dist (s : ℝ) b < δZ := by
          rw [dist_eq_norm, Real.norm_eq_abs, abs_of_nonpos (sub_nonpos.mpr s.2.2)]
          have hle : b - (s : ℝ) ≤ 3 * δ := by linarith [s.2.1]
          nlinarith
        exact hδZ hdist_sb
      simpa [hZ0ext_b] using hnear
    rw [Metric.mem_closedBall]
    have htri := dist_triangle (bcfExt hJle Z (s : ℝ)) (C s) (Z0 b)
    have hZCs' : dist (bcfExt hJle Z (s : ℝ)) (C s) ≤ 1 / 4 := by simpa [r0] using hZCs
    linarith
  have hG_lipJ : ∀ s : J, LipschitzOnWith K_G
      (fun z => z - Q.symm (G (s : ℝ) z)) (Metric.closedBall (Z0 b) 1) := by
    intro s
    exact hG_lip (s : ℝ) (hJsub_ab s.2)
  have hΘ_lipJ : ∀ s σ : J, LipschitzOnWith L_Θ
      (fun z => Θ (s : ℝ) (σ : ℝ) z) (Metric.closedBall (Z0 b) 1) := by
    intro s σ
    exact hΘ_lip (s : ℝ) (hJsub_ab s.2) (σ : ℝ) (hJsub_ab σ.2)
  have hΘ_int_fun : ∀ s : J,
      IntervalIntegrable (fun σ => Θ (s : ℝ) σ (Z0ext σ)) volume (s : ℝ) b := by
    intro s
    have hcont : Continuous (fun σ : ℝ => Θ (s : ℝ) σ (Z0ext σ)) := by
      have hpair : Continuous (fun σ : ℝ => ((s : ℝ), σ, Z0ext σ)) := by fun_prop
      exact hΘ_cont.comp hpair
    exact hcont.intervalIntegrable (s : ℝ) b
  have hZ0ext_big : ∀ s : J, Z0ext (s : ℝ) ∈ Metric.closedBall (Z0 b) 1 := by
    intro s
    have hs_ab : (s : ℝ) ∈ Set.Icc a b := hJsub_ab s.2
    have hnear : dist (Z0ext (s : ℝ)) (Z0ext b) < 1 / 2 := by
      have hdist_sb : dist (s : ℝ) b < δZ := by
        rw [dist_eq_norm, Real.norm_eq_abs, abs_of_nonpos (sub_nonpos.mpr s.2.2)]
        have hle : b - (s : ℝ) ≤ 3 * δ := by linarith [s.2.1]
        nlinarith
      exact hδZ hdist_sb
    rw [Metric.mem_closedBall]
    have hb_dist : dist (Z0ext (s : ℝ)) (Z0 b) < 1 / 2 := by
      simpa [hZ0ext_b] using hnear
    linarith
  have hΘ0_int_fun : ∀ s : J,
      IntervalIntegrable (fun σ => Θ0 (s : ℝ) σ (Z0ext σ)) volume (s : ℝ) b := by
    intro s
    let φ : ℝ → ℝ × ℝ × EuclideanSpace ℝ (Fin 4) := fun σ => ((s : ℝ), σ, Z0ext σ)
    have hφ_cont : ContinuousOn φ (Set.Icc (s : ℝ) b) := by
      dsimp [φ]
      fun_prop
    have hφ_maps : Set.MapsTo φ (Set.Icc (s : ℝ) b)
        (Set.Icc a b ×ˢ Set.Icc a b ×ˢ Metric.closedBall (Z0 b) 1) := by
      intro σ hσ
      have hs_ab : (s : ℝ) ∈ Set.Icc a b := hJsub_ab s.2
      have hσab : σ ∈ Set.Icc a b := ⟨le_trans hs_ab.1 hσ.1, hσ.2⟩
      have hσJ : σ ∈ J := ⟨le_trans s.2.1 hσ.1, hσ.2⟩
      have hZ0σ_big : Z0ext σ ∈ Metric.closedBall (Z0 b) 1 := hZ0ext_big ⟨σ, hσJ⟩
      exact ⟨hs_ab, hσab, hZ0σ_big⟩
    have hcontOn : ContinuousOn (fun σ => Θ0 (s : ℝ) σ (Z0ext σ)) (Set.Icc (s : ℝ) b) := by
      have hcomp := hΘ0_cont.comp' hφ_cont hφ_maps
      simpa [φ] using hcomp
    exact hcontOn.intervalIntegrable_of_Icc s.2.2
  have hres_Z0ext : ∀ s : J,
      dist (volterraOp (a := b - 3 * δ) (b := b) Q G Θ Ξ Z0ext (s : ℝ)) (Z0ext (s : ℝ)) ≤ margin := by
    intro s
    have hs_ab : (s : ℝ) ∈ Set.Icc a b := hJsub_ab s.2
    have hZ0ext_s_big : Z0ext (s : ℝ) ∈ Metric.closedBall (Z0 b) 1 := hZ0ext_big s
    have hG_close_s : dist (G (s : ℝ) (Z0ext (s : ℝ))) (G0 (s : ℝ) (Z0ext (s : ℝ))) < ε := by
      exact hG_close (s : ℝ) hs_ab (Z0ext (s : ℝ)) hZ0ext_s_big
    have hΘ_close_s : ∀ σ ∈ Set.Icc (s : ℝ) b,
        dist (Θ (s : ℝ) σ (Z0ext σ)) (Θ0 (s : ℝ) σ (Z0ext σ)) < ε := by
      intro σ hσ
      have hσab : σ ∈ Set.Icc a b := ⟨le_trans hs_ab.1 hσ.1, hσ.2⟩
      have hσJ : σ ∈ J := ⟨le_trans s.2.1 hσ.1, hσ.2⟩
      exact hΘ_close (s : ℝ) hs_ab σ hσab (Z0ext σ) (hZ0ext_big ⟨σ, hσJ⟩)
    have hbase_s : G0 (s : ℝ) (Z0ext (s : ℝ)) =
        (∫ σ in (s : ℝ)..b, Θ0 (s : ℝ) σ (Z0ext σ)) + Ξ0 (s : ℝ) := by
      have hI : (∫ σ in (s : ℝ)..b, Θ0 (s : ℝ) σ (Z0ext σ)) =
          (∫ σ in (s : ℝ)..b, Θ0 (s : ℝ) σ (Z0 σ)) := by
        apply intervalIntegral.integral_congr
        intro σ hσ
        rw [Set.uIcc_of_le s.2.2] at hσ
        have hσab : σ ∈ Set.Icc a b := ⟨le_trans hs_ab.1 hσ.1, hσ.2⟩
        change Θ0 (s : ℝ) σ (Z0ext σ) = Θ0 (s : ℝ) σ (Z0 σ)
        rw [hZ0ext_of_mem hσab]
      rw [hZ0ext_of_mem hs_ab, hI]
      exact hbase (s : ℝ) hs_ab
    have hnorm := volterraOp_sub_Z0_norm_le_of_close (a := b - 3 * δ) (b := b) (s := (s : ℝ))
      s.2 (Q := Q) (G0 := G0) (Θ0 := Θ0) (Ξ0 := Ξ0) (G := G) (Θ := Θ) (Ξ := Ξ)
      (Z0 := Z0ext) (ε := ε) (le_of_lt hε_pos) hG_close_s hΘ_close_s
      (hΞ_close (s : ℝ) hs_ab) hbase_s (hΘ_int_fun s) (hΘ0_int_fun s)
    have hle : (2 + (b - (s : ℝ))) * ε ≤ (2 + (b - a)) * ε := by
      have hb_s_le_ab : b - (s : ℝ) ≤ b - a := by
        have hs_ab_low : a ≤ (s : ℝ) := (hJsub_ab s.2).1
        linarith
      have hsum : 2 + (b - (s : ℝ)) ≤ 2 + (b - a) := by linarith
      exact mul_le_mul_of_nonneg_right hsum (le_of_lt hε_pos)
    have hCQle : CQ * ((2 + (b - (s : ℝ))) * ε) ≤ CQ * ((2 + (b - a)) * ε) :=
      mul_le_mul_of_nonneg_left hle hCQ_nonneg
    have hCQle2 : CQ * ((2 + (b - a)) * ε) ≤ margin := by
      rw [← mul_assoc]
      exact hε_small
    have hle_margin : CQ * ((2 + (b - (s : ℝ))) * ε) ≤ margin := hCQle.trans hCQle2
    have hnorm_le_margin : ‖volterraOp (a := b - 3 * δ) (b := b) Q G Θ Ξ Z0ext (s : ℝ) - Z0ext (s : ℝ)‖ ≤ margin :=
      hnorm.trans hle_margin
    simpa [dist_eq_norm] using hnorm_le_margin
  have hEqOn_C : Set.EqOn (bcfExt hJle C) Z0ext J := by
    intro t ht
    rw [bcfExt_of_mem hJle C ht, hC_val]
  have hres_C : ∀ s : J,
      dist (volterraOp (a := b - 3 * δ) (b := b) Q G Θ Ξ (bcfExt hJle C) (s : ℝ)) (C s) ≤ margin := by
    intro s
    have hvol_eq := volterraOp_congr_Z_of_eqOn (a := b - 3 * δ) (b := b) (s := (s : ℝ)) s.2
      (Q := Q) (G := G) (Θ := Θ) (Ξ := Ξ) (Z := bcfExt hJle C) (W := Z0ext) hEqOn_C
    have hdist_Z0 := hres_Z0ext s
    have hCeq : C s = Z0ext (s : ℝ) := hC_val s
    simpa [hvol_eq, hCeq] using hdist_Z0
  have hK_J_le_lam : K_J_real ≤ lam := by
    change (K_G : ℝ) + CQ * (L_Θ : ℝ) * (3 * δ) ≤ (K_G : ℝ) + CQ * (L_Θ : ℝ) * (b - a)
    have hlen : 3 * δ ≤ b - a := by nlinarith [hδ_le_ab]
    have hmulnonneg : 0 ≤ CQ * (L_Θ : ℝ) := by positivity
    have hle_mul : CQ * (L_Θ : ℝ) * (3 * δ) ≤ CQ * (L_Θ : ℝ) * (b - a) :=
      mul_le_mul_of_nonneg_left hlen hmulnonneg
    linarith
  have hKJ_margin : K_J_real * r0 + margin ≤ r0 := by
    have hmul : K_J_real * r0 ≤ lam * r0 := mul_le_mul_of_nonneg_right hK_J_le_lam hr0_nonneg
    dsimp [margin]
    nlinarith
  have hmapsTo : Set.MapsTo T (Metric.closedBall C r0) (Metric.closedBall C r0) := by
    intro Z hZ
    rw [Metric.mem_closedBall] at hZ ⊢
    apply bcf_dist_le_of_pointwise hr0_nonneg
    intro s
    have hpoint := volterraOpBcf_dist_center_le_of_lipschitzOn hJle
      (K_G := K_G) (L_Θ := L_Θ) (Q := Q) (G := G) (Θ := Θ) (Ξ := Ξ)
      (Z := Z) (C := C) (z0 := Z0 b) (r := r0) (res := margin)
      (hZbig Z hZ) hC_big hG_lipJ hΘ_lipJ hΘ_cont hres_C hZ s
    have hTZ := hT_apply Z s
    have hle : dist (T Z s) (C s) ≤ K_J_real * r0 + margin := by
      rw [hTZ]
      simpa [K_J_real, CQ, show b - (b - 3 * δ) = 3 * δ by ring] using hpoint
    exact hle.trans hKJ_margin
  have hcontraction_point : ∀ Z W : BoundedContinuousFunction J (EuclideanSpace ℝ (Fin 4)),
      Z ∈ Metric.closedBall C r0 → W ∈ Metric.closedBall C r0 →
      ∀ s : J, dist (T Z s) (T W s) ≤ K_J_real * dist Z W := by
    intro Z W hZ hW s
    have hpoint := volterraOpBcf_dist_le_of_lipschitzOn hJle
      (K_G := K_G) (L_Θ := L_Θ) (Q := Q) (G := G) (Θ := Θ) (Ξ := Ξ)
      (Z := Z) (W := W) (z0 := Z0 b)
      (hZbig Z hZ) (hZbig W hW) hG_lipJ hΘ_lipJ hΘ_cont s
    have hTZ := hT_apply Z s
    have hTW := hT_apply W s
    rw [hTZ, hTW]
    simpa [K_J_real, CQ] using hpoint
  have hcontr_sub : ContractingWith K_J
      (hmapsTo.restrict T (Metric.closedBall C r0) (Metric.closedBall C r0)) := by
    refine ⟨hK_J_lt, ?_⟩
    apply LipschitzWith.of_dist_le_mul
    intro Z W
    apply bcf_dist_le_of_pointwise (mul_nonneg K_J.2 dist_nonneg)
    intro s
    have hle := hcontraction_point Z.1 W.1 Z.2 W.2 s
    simpa [Subtype.dist_eq, K_J] using hle
  have hfixed : ∃ Z ∈ Metric.closedBall C r0, Function.IsFixedPt T Z := by
    have h := ContractingWith.exists_fixedPoint' (f := T) (s := Metric.closedBall C r0)
      (Metric.isClosed_closedBall.isComplete) hmapsTo hcontr_sub
      (x := C) (Metric.mem_closedBall_self hr0_nonneg) (edist_ne_top C (T C))
    rcases h with ⟨Zcur, hZcur_mem, hfix, -, -⟩
    exact ⟨Zcur, hZcur_mem, hfix⟩
  rcases hfixed with ⟨Zcur, hZcur_mem, hfix⟩
  let Z : ℝ → EuclideanSpace ℝ (Fin 4) := Set.IccExtend hJle (fun s : J => Zcur s)
  have hZ_cont : Continuous Z := by
    dsimp [Z]
    exact Zcur.continuous.Icc_extend'
  have hZ_cur : ∀ s : J, Z (s : ℝ) = Zcur s := by
    intro s
    dsimp [Z]
    exact Set.IccExtend_val (h := hJle) (f := fun s : J => Zcur s) s
  have hZ_on : ContinuousOn Z J := hZ_cont.continuousOn
  have hvol : ∀ s ∈ J, volterraOp (a := b - 3 * δ) (b := b) Q G Θ Ξ (bcfExt hJle Zcur) s = bcfExt hJle Zcur s := by
    intro s hs
    have hTZ := hT_apply Zcur ⟨s, hs⟩
    have hfixs : (T Zcur) ⟨s, hs⟩ = Zcur ⟨s, hs⟩ := by
      exact congrFun (congrArg DFunLike.coe hfix) ⟨s, hs⟩
    have hvol_val : volterraOp (a := b - 3 * δ) (b := b) Q G Θ Ξ (bcfExt hJle Zcur) s = Zcur ⟨s, hs⟩ := by
      rw [← hTZ, hfixs]
    rw [hvol_val, bcfExt_of_mem hJle Zcur hs]
  have hEq_bcf : ∀ s ∈ J,
      G s (bcfExt hJle Zcur s) = (∫ σ in s..b, Θ s σ (bcfExt hJle Zcur σ)) + Ξ s := by
    exact volterraOp_fixedPoint_solves (a := b - 3 * δ) (b := b) Q G Θ Ξ (bcfExt hJle Zcur) hvol
  refine ⟨Z, ?_, ?_, ?_⟩
  · exact hZ_on
  · intro s hs
    have hbcf_s : bcfExt hJle Zcur s = Z s := by
      rw [bcfExt_of_mem hJle Zcur hs, hZ_cur ⟨s, hs⟩]
    have hbcf_int : (∫ σ in s..b, Θ s σ (bcfExt hJle Zcur σ)) =
        (∫ σ in s..b, Θ s σ (Z σ)) := by
      apply intervalIntegral.integral_congr
      intro σ hσ
      rw [Set.uIcc_of_le hs.2] at hσ
      have hσJ : σ ∈ J := ⟨le_trans hs.1 hσ.1, hσ.2⟩
      change Θ s σ (bcfExt hJle Zcur σ) = Θ s σ (Z σ)
      rw [bcfExt_of_mem hJle Zcur hσJ, hZ_cur ⟨σ, hσJ⟩]
    simpa [hbcf_s, hbcf_int] using hEq_bcf s hs
  · intro s hs
    have hZcur_le : dist (Zcur ⟨s, hs⟩) (C ⟨s, hs⟩) ≤ r0 := by
      exact (BoundedContinuousFunction.dist_coe_le_dist (f := Zcur) (g := C) ⟨s, hs⟩).trans
        (Metric.mem_closedBall.mp hZcur_mem)
    have hC_s : C ⟨s, hs⟩ = Z0 s := hC_Z0 ⟨s, hs⟩
    have hZ_s : Z s = Zcur ⟨s, hs⟩ := hZ_cur ⟨s, hs⟩
    calc
      dist (Z s) (Z0 s) = dist (Zcur ⟨s, hs⟩) (C ⟨s, hs⟩) := by rw [hZ_s, hC_s]
      _ ≤ r0 := hZcur_le
      _ < 1 / 2 := by norm_num [r0]

lemma volterra_perturbation_exists_v3_small
    {a b : ℝ} (hab : a < b)
    {G0 : ℝ → EuclideanSpace ℝ (Fin 4) → EuclideanSpace ℝ (Fin 4)}
    {Θ0 : ℝ → ℝ → EuclideanSpace ℝ (Fin 4) → EuclideanSpace ℝ (Fin 4)}
    {Ξ0 : ℝ → EuclideanSpace ℝ (Fin 4)} {Z0 : ℝ → EuclideanSpace ℝ (Fin 4)}
    {Q : EuclideanSpace ℝ (Fin 4) ≃L[ℝ] EuclideanSpace ℝ (Fin 4)}
    {B_G0 B_Θ0 B_Ξ0 : ℝ} {K_G L_Θ : NNReal}
    (hcontract : (K_G : ℝ) + ‖(Q.symm : EuclideanSpace ℝ (Fin 4) →L[ℝ] EuclideanSpace ℝ (Fin 4))‖ * (L_Θ : ℝ) * (b - a) < 1)
    (hQ : fderiv ℝ (fun z : EuclideanSpace ℝ (Fin 4) => G0 b z) (Z0 b) = Q.toContinuousLinearMap)
    (hG0_bound : ∀ s ∈ Set.Icc a b, ∀ z ∈ Metric.closedBall (Z0 b) 1, ‖G0 s z‖ ≤ B_G0)
    (hΘ0_bound : ∀ s ∈ Set.Icc a b, ∀ σ ∈ Set.Icc a b, ∀ z ∈ Metric.closedBall (Z0 b) 1,
      ‖Θ0 s σ z‖ ≤ B_Θ0)
    (hΞ0_bound : ∀ s ∈ Set.Icc a b, ‖Ξ0 s‖ ≤ B_Ξ0)
    (hbase : ∀ s ∈ Set.Icc a b,
      G0 s (Z0 s) = (∫ σ in s..b, Θ0 s σ (Z0 σ)) + Ξ0 s)
    (hdet : (fderiv ℝ (fun z : EuclideanSpace ℝ (Fin 4) => G0 b z) (Z0 b)).det ≠ 0)
    (hG_cont_at_base : ContinuousAt
      (fun p : ℝ × EuclideanSpace ℝ (Fin 4) => fderiv ℝ (fun z => G0 p.1 z) p.2) (b, Z0 b))
    (hZ0_cont : ContinuousOn Z0 (Set.Icc a b)) :
    ∃ ε > 0, ∃ δ > 0, ε ≤ 1 / 4 ∧ δ ≤ (b - a) / 3 ∧
    ∀ (G : ℝ → EuclideanSpace ℝ (Fin 4) → EuclideanSpace ℝ (Fin 4))
      (Θ : ℝ → ℝ → EuclideanSpace ℝ (Fin 4) → EuclideanSpace ℝ (Fin 4))
      (Ξ : ℝ → EuclideanSpace ℝ (Fin 4)),
      Continuous (fun p : ℝ × EuclideanSpace ℝ (Fin 4) => G p.1 p.2) →
      Continuous (fun p : ℝ × ℝ × EuclideanSpace ℝ (Fin 4) => Θ p.1 p.2.1 p.2.2) →
      Continuous Ξ →
      (∀ s ∈ Set.Icc a b, ∀ z ∈ Metric.closedBall (Z0 b) 1,
        dist (G s z) (G0 s z) < ε) →
      (∀ s ∈ Set.Icc a b, ∀ σ ∈ Set.Icc a b, ∀ z ∈ Metric.closedBall (Z0 b) 1,
        dist (Θ s σ z) (Θ0 s σ z) < ε) →
      (∀ s ∈ Set.Icc a b, dist (Ξ s) (Ξ0 s) < ε) →
      (∀ s ∈ Set.Icc a b, LipschitzOnWith K_G (fun z : EuclideanSpace ℝ (Fin 4) =>
        z - Q.symm (G s z)) (Metric.closedBall (Z0 b) 1)) →
      (∀ s ∈ Set.Icc a b, ∀ σ ∈ Set.Icc a b, LipschitzOnWith L_Θ
        (fun z : EuclideanSpace ℝ (Fin 4) => Θ s σ z) (Metric.closedBall (Z0 b) 1)) →
        ∃ Z : ℝ → EuclideanSpace ℝ (Fin 4),
          ContinuousOn Z (Set.Icc (b - 3 * δ) b) ∧
          (∀ s ∈ Set.Icc (b - 3 * δ) b,
            G s (Z s) = (∫ σ in s..b, Θ s σ (Z σ)) + Ξ s) ∧
          (∀ s ∈ Set.Icc (b - 3 * δ) b, dist (Z s) (Z0 s) < 1 / 2) := by
  classical
  let Ω : Set (ℝ × ℝ × EuclideanSpace ℝ (Fin 4)) :=
    Set.Icc a b ×ˢ Set.Icc a b ×ˢ Metric.closedBall (Z0 b) 1
  by_cases hΘ0cont : ContinuousOn (fun p : ℝ × ℝ × EuclideanSpace ℝ (Fin 4) => Θ0 p.1 p.2.1 p.2.2) Ω
  · exact volterra_perturbation_exists_continuous_theta_small hab hcontract hQ hG0_bound hΘ0_bound
      hΞ0_bound hbase hdet hG_cont_at_base hZ0_cont hΘ0cont
  · let Θ0dom : Ω → EuclideanSpace ℝ (Fin 4) := fun p => Θ0 p.1.1 p.1.2.1 p.1.2.2
    have hΘ0dom_not_cont : ¬ Continuous Θ0dom := by
      intro hc
      apply hΘ0cont
      exact continuousOn_iff_continuous_domRestrict.mpr hc
    obtain ⟨ε0, hε0_pos, hε0_bad⟩ :=
      exists_pos_dist_continuous_of_not_continuous (f := Θ0dom) hΘ0dom_not_cont
    let ε := min (1 / 4) ε0
    let δ : ℝ := (b - a) / 3
    have hε_pos : 0 < ε := by
      dsimp [ε]
      exact lt_min (by norm_num) hε0_pos
    have hε_le : ε ≤ 1 / 4 := by dsimp [ε]; exact min_le_left _ _
    have hδ_pos : 0 < δ := by
      dsimp [δ]
      exact div_pos (sub_pos.mpr hab) (by norm_num)
    have hδ_le : δ ≤ (b - a) / 3 := le_rfl
    refine ⟨ε, hε_pos, δ, hδ_pos, hε_le, hδ_le, ?_⟩
    intro G Θ Ξ hG_cont hΘ_cont hΞ_cont hG_close hΘ_close hΞ_close hG_lip hΘ_lip
    exfalso
    let g : Ω → EuclideanSpace ℝ (Fin 4) := fun p => Θ p.1.1 p.1.2.1 p.1.2.2
    have hg_cont : Continuous g := by
      have hcontOn : ContinuousOn (fun p : ℝ × ℝ × EuclideanSpace ℝ (Fin 4) => Θ p.1 p.2.1 p.2.2) Ω :=
        hΘ_cont.continuousOn
      exact continuousOn_iff_continuous_domRestrict.mp hcontOn
    rcases hε0_bad g hg_cont with ⟨p, hp⟩
    have hclose : dist (Θ p.1.1 p.1.2.1 p.1.2.2) (Θ0 p.1.1 p.1.2.1 p.1.2.2) < ε := by
      exact hΘ_close p.1.1 p.2.1 p.1.2.1 p.2.2.1 p.1.2.2 p.2.2.2
    have hε_le0 : ε ≤ ε0 := by dsimp [ε]; exact min_le_right _ _
    have hclose0 : dist (Θ0dom p) (g p) < ε0 := by
      change dist (Θ0 p.1.1 p.1.2.1 p.1.2.2) (Θ p.1.1 p.1.2.1 p.1.2.2) < ε0
      rw [dist_comm]
      exact lt_of_lt_of_le hclose hε_le0
    linarith

end Commons.Geometry.Ulam
