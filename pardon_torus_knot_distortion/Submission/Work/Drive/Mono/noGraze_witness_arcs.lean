import Mathlib
import Submission.Work.Drive.Mono.NoGrazeDefs
import Submission.Work.Drive.Mono.Band.bandData_core_exists
import Submission.Work.Drive.Mono.noGraze_cover
import Submission.Work.Drive.Mono.noGraze_mvt_coord
import Submission.Work.Drive.Mono.noGraze_mvt_vertVel
import Submission.Work.Drive.Mono.Band.heightGood_exists_in
import Submission.Work.Drive.Mono.exists_unitOrth_avoid
import Submission.Work.Drive.Mono.arcFamilyBounds

set_option maxHeartbeats 1000000

namespace Work.Drive.Mono

open LeanEval.KnotTheory.PardonDistortion MeasureTheory Set
open scoped ENNReal _root_.Topology RealInnerProductSpace
open Work.Drive.Mono.Band

noncomputable section

/-- From `a ≤ c / b` with `b > 0` conclude `a * b ≤ c`. -/
private lemma rb_mul_le_of_le_div {a b c : ℝ} (hb : 0 < b) (h : a ≤ c / b) : a * b ≤ c := by
  rwa [le_div_iff₀ hb] at h

/-- The reverse triangle inequality in the form needed below. -/
private lemma rb_le_abs_add (a b : ℝ) : |a| - |b| ≤ |a + b| := by
  have h := abs_sub_abs_le_abs_sub a (-b)
  simpa [abs_neg, sub_neg_eq_add] using h

/-- `|a| - |b| - |c| ≤ |a + b + c|`. -/
private lemma rb_abs_add_three (a b c : ℝ) : |a| - |b| - |c| ≤ |a + b + c| := by
  have h1 : |a + b| - |c| ≤ |a + b + c| := rb_le_abs_add (a + b) c
  have h2 : |a| - |b| ≤ |a + b| := rb_le_abs_add a b
  linarith only [h1, h2]

/-- For a unit vector `n`, the absolute value of `⟪n, w⟫` is at most `‖w‖`. -/
private lemma rb_abs_inner_unit_le {n w : R3} (hn : ‖n‖ = 1) : |inner ℝ n w| ≤ ‖w‖ := by
  have h := abs_real_inner_le_norm n w
  rwa [hn, one_mul] at h

/-- From `a ≤ c / b / 4` with `b > 0` conclude `a * (4 * b) ≤ c`. -/
private lemma rb_mul_le_of_le_quarter {a b c : ℝ} (hb : 0 < b) (h : a ≤ c / b / 4) :
    a * (4 * b) ≤ c := by
  rw [le_div_iff₀ (show (0 : ℝ) < 4 by norm_num)] at h
  rw [le_div_iff₀ hb] at h
  nlinarith only [h]

theorem noGraze_witness_arcs
    (ψ : Submission.Diffeo) (K : LeanEval.KnotTheory.PardonDistortion.Knot) {r s u : ℝ}
    (hr : 0 < r) (hrs : r < s) (hu : |u| < Submission.eps * r)
    (c : LeanEval.KnotTheory.PardonDistortion.R3) (σ : Equiv.Perm (Fin 3))
    (hcut : Work.Drive.Mono.CutTransverse K s c σ u)
    {εg δg θ' : ℝ} (hεg : 0 < εg) (hδg : 0 < δg) (hθ' : 0 < θ')
    (hnograz : ∀ v : LeanEval.KnotTheory.PardonDistortion.R3, ‖v‖ = 1 →
        ‖v - Work.BoxShrink.shiftVσ σ 1‖ < εg →
        ∀ t : ℝ, K.curve t ∈ Submission.PBox s c σ →
          deriv (fun r : ℝ => inner ℝ v (K.curve r)) t = 0 →
          δg ≤ |inner ℝ v (K.curve t) - (inner ℝ v c + u)|)
    (hnobend : ∀ t : ℝ, K.curve t ∈ closure (Submission.PBox s c σ) →
        (K.curve t) (σ 2) = c (σ 2) + u →
        Work.Drive.Mono.vertVel K (Work.BoxShrink.shiftVσ σ 1) t = 0 →
        Work.Drive.Mono.vertAcc K (Work.BoxShrink.shiftVσ σ 1) t = 0)
    {N : ℕ} {γ : Fin N → ℝ → LeanEval.KnotTheory.PardonDistortion.R3} {η : ℝ} (hη : 0 < η)
    (hγ : ∀ k, ContDiffOn ℝ 3 (γ k) (Set.Icc (-η) η))
    (hγh : ∀ k, ∀ t ∈ Set.Icc (-η) η, (γ k t) (σ 2) = c (σ 2) + u + t)
    (hbend : ∀ k, deriv (γ k) 0 = Work.BoxShrink.shiftVσ σ 1 →
        deriv (deriv (γ k)) 0 = 0) :
    ∃ (v n : LeanEval.KnotTheory.PardonDistortion.R3) (h ρ : ℝ),
      ‖v‖ = 1 ∧ ‖n‖ = 1 ∧ inner ℝ v n = 0 ∧ Work.Drive.Mono.Band.HeightGood ψ n ∧
      ‖v - Work.BoxShrink.shiftVσ σ 1‖ ≤ θ' ∧
      ‖v - Work.BoxShrink.shiftVσ σ 1‖ ≤ εg / 4 ∧
      0 < h ∧ 0 < ρ ∧
      2 * (‖v - Work.BoxShrink.shiftVσ σ 1‖ * (5 / 2 * s)) < h ∧
      (∀ t : ℝ, Submission.boxNorm c σ (K.curve t) = s →
          h ≤ |inner ℝ v (K.curve t) - (inner ℝ v c + u)|) ∧
      (∀ t : ℝ, K.curve t ∈ Submission.PBox s c σ →
          deriv (fun r : ℝ => inner ℝ v (K.curve r)) t = 0 →
          h ≤ |inner ℝ v (K.curve t) - (inner ℝ v c + u)|) ∧
      (∀ nn : LeanEval.KnotTheory.PardonDistortion.R3, ‖nn‖ = 1 → ‖nn - n‖ < ρ → ∀ t : ℝ,
          K.curve t ∈ Submission.PBox s c σ →
          |inner ℝ v (K.curve t) - (inner ℝ v c + u)| ≤ h →
          deriv (fun r : ℝ => inner ℝ nn (K.curve r)) t ≠ 0) ∧
      (∀ t : ℝ, K.curve t ∈ Submission.PBox s c σ →
          |inner ℝ v (K.curve t) - (inner ℝ v c + u)| = h →
          deriv (fun r : ℝ => inner ℝ v (K.curve r)) t ≠ 0) ∧
      (∀ k, ∀ t : ℝ, t ∈ Set.Ioo (-η) η → |t| ≤ 2 * h →
          ∀ nn : LeanEval.KnotTheory.PardonDistortion.R3, ‖nn‖ = 1 → ‖nn - n‖ < ρ →
            inner ℝ nn (deriv (γ k) t) ≠ 0) ∧
      (∀ k, ∀ t : ℝ, t ∈ Set.Ioo (-η) η → |t| ≤ 2 * h →
          (1 / 2 : ℝ) ≤ inner ℝ v (deriv (γ k) t)) := by
  classical
  -- ## 0. Basic data
  have hs : 0 < s := lt_trans hr hrs
  have hs0 : 0 ≤ s := le_of_lt hs
  set e : R3 := Work.BoxShrink.shiftVσ σ 1 with hedef
  have he1 : ‖e‖ = 1 := by rw [hedef]; exact norm_shiftVσ_one σ
  -- ## 0b. the intrinsic data of the arcs
  have hee_e : inner ℝ e e = 1 := by rw [real_inner_self_eq_norm_sq, he1]; norm_num
  obtain ⟨MA1, MA2, MA4, hMA10, hMA20, hMA40, hMAspec⟩ := arcFamilyBounds hη hγ
  have hcoord_all : ∀ k (t : ℝ), t ∈ Set.Ioo (-η) η → (deriv (γ k) t) (σ 2) = 1 := by
    intro k t ht
    have hIcc : Set.Icc (-η) η ∈ 𝓝 t :=
      Filter.mem_of_superset (isOpen_Ioo.mem_nhds ht) (fun r hr => ⟨le_of_lt hr.1, le_of_lt hr.2⟩)
    have hdiff : DifferentiableAt ℝ (γ k) t :=
      ((hγ k).contDiffAt hIcc).differentiableAt (by norm_num)
    have h1 : deriv (fun r : ℝ => (γ k r) (σ 2)) t = (deriv (γ k) t) (σ 2) := by
      have h2 : (fun r : ℝ => (γ k r) (σ 2)) = fun r : ℝ => inner ℝ (unitCoord σ 2) (γ k r) := by
        funext r; rw [inner_unitCoord]
      rw [h2, deriv_inner_apply ℝ (differentiableAt_const _) hdiff, inner_unitCoord]
      simp
    rw [← h1]
    have hEv : (fun r : ℝ => (γ k r) (σ 2)) =ᶠ[𝓝 t] fun r : ℝ => c (σ 2) + u + r := by
      filter_upwards [isOpen_Ioo.mem_nhds ht] with r hr
      exact hγh k r ⟨le_of_lt hr.1, le_of_lt hr.2⟩
    rw [Filter.EventuallyEq.deriv_eq hEv]
    simp
  have hdperp : ∀ k, inner ℝ e (deriv (γ k) 0 - e) = 0 := by
    intro k
    have h0 : inner ℝ e (deriv (γ k) 0) = 1 := by
      rw [hedef, inner_shiftVσ_one]
      exact hcoord_all k 0 ⟨by linarith, by linarith⟩
    rw [inner_sub_right, h0, hee_e, sub_self]
  obtain ⟨lam, m, ρc, hlam0, hm0, hρc0, hlam, hmargin, hcover⟩ := noGraze_cover K c σ hcut
  obtain ⟨M1, hM10, hM1⟩ := exists_bound_deriv_curve K
  obtain ⟨M2, hM20, hM2⟩ := exists_bound_deriv2_curve K
  obtain ⟨Cv, dv, hCv0, hdv0, hCv⟩ := exists_uniform_sq_bound_vertVel K e he1
  obtain ⟨R2, hR20, hR2⟩ := exists_bound_boxNorm_eq s c σ
  obtain ⟨mbox, hmbox0, hmbox⟩ := exists_margin_boxSphere K c σ hs hcut
  set R1 : ℝ := 5 / 2 * s with hR1def
  have hR1b : ∀ y ∈ Submission.PBox s c σ, ‖y - c‖ ≤ R1 := by
    intro y hy
    rw [hR1def]
    exact norm_sub_le_of_mem_PBox hs0 hy
  -- a unit vector orthogonal to `e`
  set e₂ : R3 := unitCoord σ 0 with he₂def
  have he₂1 : ‖e₂‖ = 1 := by rw [he₂def]; exact norm_unitCoord σ 0
  have he₂orth : inner ℝ e₂ e = 0 := by
    rw [hedef, he₂def, inner_unitCoord, Work.BoxShrink.shiftVσ_apply]
    have h : σ 0 ≠ σ 2 := fun hc => absurd (σ.injective hc) (by decide)
    simp [h]
  -- ## 1. the crossing set and the avoidance direction
  set W : Finset R3 := ((crossingSet K c σ s u hcut).filter (fun t => vertVel K e t ≠ 0)).image
      (fun t => vertVel K e t) ∪ Finset.univ.image (fun k : Fin N => deriv (γ k) 0 - e) with hW
  have hWorth : ∀ w ∈ W, inner ℝ e w = 0 := by
    intro w hw
    rw [hW] at hw
    rcases Finset.mem_union.mp hw with h | h
    · obtain ⟨t, -, rfl⟩ := Finset.mem_image.mp h
      exact inner_e_vertVel K e he1 t
    · obtain ⟨k, -, rfl⟩ := Finset.mem_image.mp h
      exact hdperp k
  obtain ⟨Ñ₀, hÑ₀1, hÑ₀orth, hÑ₀avoid⟩ :=
    exists_unitOrth_avoid e e₂ he1 he₂1 he₂orth W hWorth
  have hÑ₀orth' : inner ℝ e Ñ₀ = 0 := by rw [real_inner_comm, hÑ₀orth]
  have hc00 : ∃ c00 : ℝ, 0 < c00 ∧
      (∀ t ∈ crossingSet K c σ s u hcut, vertVel K e t ≠ 0 →
        c00 ≤ |inner ℝ Ñ₀ (vertVel K e t)|) ∧
      (∀ k : Fin N, deriv (γ k) 0 - e ≠ 0 →
        c00 ≤ |inner ℝ Ñ₀ (deriv (γ k) 0 - e)|) := by
    classical
    by_cases hne : (W.filter (fun w => w ≠ 0)).Nonempty
    · obtain ⟨w₁, hw₁, hmin⟩ := Finset.exists_min_image (W.filter (fun w => w ≠ 0))
        (fun w => |inner ℝ Ñ₀ w|) hne
      have hw₁W : w₁ ∈ W := (Finset.mem_filter.mp hw₁).1
      have hw₁0 : w₁ ≠ 0 := (Finset.mem_filter.mp hw₁).2
      refine ⟨|inner ℝ Ñ₀ w₁|, abs_pos.mpr (hÑ₀avoid w₁ hw₁W hw₁0), ?_, ?_⟩
      · intro t htT hvn
        refine hmin _ (Finset.mem_filter.mpr ⟨?_, hvn⟩)
        rw [hW]
        exact Finset.mem_union_left _
          (Finset.mem_image.mpr ⟨t, Finset.mem_filter.mpr ⟨htT, hvn⟩, rfl⟩)
      · intro k hk
        refine hmin _ (Finset.mem_filter.mpr ⟨?_, hk⟩)
        rw [hW]
        exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨k, Finset.mem_univ k, rfl⟩)
    · refine ⟨1, one_pos, ?_, ?_⟩
      · intro t htT hvn
        exact absurd ⟨vertVel K e t, Finset.mem_filter.mpr ⟨by
          rw [hW]
          exact Finset.mem_union_left _
            (Finset.mem_image.mpr ⟨t, Finset.mem_filter.mpr ⟨htT, hvn⟩, rfl⟩), hvn⟩⟩ hne
      · intro k hk
        exact absurd ⟨deriv (γ k) 0 - e, Finset.mem_filter.mpr ⟨by
          rw [hW]
          exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨k, Finset.mem_univ k, rfl⟩), hk⟩⟩ hne
  obtain ⟨c00, hc000, hc00le, hc00arc⟩ := hc00
  -- ## 2. the smallness parameters
  set X1 : ℝ := εg with hX1
  set X2 : ℝ := δg / (6 * s + 1) with hX2
  set X3 : ℝ := mbox / (6 * s + R2 + 2) with hX3
  set X4 : ℝ := m / (6 * s + R1 + 2) with hX4
  set X5 : ℝ := dv * lam / (2 * (6 * s + R1 + 2)) with hX5
  set X6 : ℝ := lam ^ 2 / (8 * M2 * (6 * s + R1) + 8) with hX6
  set X7 : ℝ := lam ^ 3 / (24 * Cv * (6 * s + R1) ^ 2 + 1) with hX7
  set X8 : ℝ := c00 * lam / (16 * M2 * (6 * s + R1) + 16) with hX8
  set X9 : ℝ := c00 / (16 * (M1 + 1)) with hX9
  set X10 : ℝ := 1 with hX10
  set X11 : ℝ := c00 / (4 * (M1 + 1)) with hX11
  set X12 : ℝ := 1 / 4 with hX12
  set X13 : ℝ := η / (96 * s + 96) with hX13
  set X14 : ℝ := 1 / (16 * (MA1 + 2)) with hX14
  set X15 : ℝ := 1 / (144 * MA4 * s ^ 2 + 1) with hX15
  set X16 : ℝ := c00 / (144 * MA2 * s + 1) with hX16
  set X17 : ℝ := c00 / (96 * (MA1 + 1)) with hX17
  set caps : Finset ℝ := {X1, X2, X3, X4, X5, X6, X7, X8, X9, X10, X11, X12, X13, X14, X15,
    X16, X17, θ'} with hcaps
  have hcapsne : caps.Nonempty := ⟨X1, by rw [hcaps]; simp⟩
  obtain ⟨I, hImem, hIle⟩ := Finset.exists_min_image caps (fun x : ℝ => x) hcapsne
  have hIpos : 0 < I := by
    rw [hcaps] at hImem
    simp only [Finset.mem_insert, Finset.mem_singleton] at hImem
    rcases hImem with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · rw [h, hX1]; exact hεg
    · rw [h, hX2]; exact div_pos hδg (by linarith [hs])
    · rw [h, hX3]; exact div_pos hmbox0 (by linarith [hs, hR20])
    · rw [h, hX4]; exact div_pos hm0 (by linarith [hs, hR1def])
    · rw [h, hX5]; exact div_pos (mul_pos hdv0 hlam0) (by linarith [hs, hR1def])
    · rw [h, hX6]; exact div_pos (pow_pos hlam0 2) (by nlinarith [hs, hR1def, hM20])
    · rw [h, hX7]; exact div_pos (pow_pos hlam0 3)
        (by nlinarith [hCv0, hs, hR1def, sq_nonneg (6 * s + R1)])
    · rw [h, hX8]; exact div_pos (mul_pos hc000 hlam0) (by nlinarith [hs, hR1def, hM20])
    · rw [h, hX9]; exact div_pos hc000 (by linarith [hM10])
    · rw [h, hX10]; norm_num
    · rw [h, hX11]; exact div_pos hc000 (by linarith [hM10])
    · rw [h, hX12]; norm_num
    · rw [h, hX13]; exact div_pos hη (by linarith only [hs])
    · rw [h, hX14]; exact div_pos one_pos (by positivity)
    · rw [h, hX15]; exact div_pos one_pos (by positivity)
    · rw [h, hX16]; exact div_pos hc000 (by positivity)
    · rw [h, hX17]; exact div_pos hc000 (by linarith only [hMA10])
    · rw [h]; exact hθ'
  set ηb : ℝ := I / 24 with hηbdef
  set ζ : ℝ := I / 48 with hζ
  have hηb0 : 0 < ηb := by rw [hηbdef]; exact div_pos hIpos (by norm_num)
  have hζ0 : 0 < ζ := by rw [hζ]; exact div_pos hIpos (by norm_num)
  have hζ_eq : ζ = ηb / 2 := by rw [hηbdef, hζ]; ring
  have hηb_le : ηb ≤ 1 / 24 := by
    have h := hIle X10 (by rw [hcaps]; simp)
    rw [hX10] at h
    rw [hηbdef]; linarith
  -- ## 3. the base direction `n₀` and the admissible ball
  set n₀ : R3 := ηb • e + Real.sqrt (1 - ηb ^ 2) • Ñ₀ with hn₀def
  have hee : inner ℝ e e = 1 := by rw [real_inner_self_eq_norm_sq, he1]; norm_num
  have hÑÑ : inner ℝ Ñ₀ Ñ₀ = 1 := by rw [real_inner_self_eq_norm_sq, hÑ₀1]; norm_num
  have hn₀_sq : inner ℝ n₀ n₀ = 1 := by
    have hsq : Real.sqrt (1 - ηb ^ 2) ^ 2 = 1 - ηb ^ 2 :=
      Real.sq_sqrt (by nlinarith only [hηb_le, hηb0])
    simp only [hn₀def, inner_add_left, inner_add_right, real_inner_smul_left,
      real_inner_smul_right, hee, hÑÑ, hÑ₀orth, hÑ₀orth', mul_one, mul_zero, add_zero]
    ring_nf
    linarith only [hsq]
  have hn₀_norm : ‖n₀‖ = 1 := by
    have h : ‖n₀‖ ^ 2 = 1 := by rw [← real_inner_self_eq_norm_sq, hn₀_sq]
    calc ‖n₀‖ = Real.sqrt (‖n₀‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
      _ = Real.sqrt 1 := by rw [h]
      _ = 1 := Real.sqrt_one
  have he_n₀ : inner ℝ e n₀ = ηb := by
    simp only [hn₀def, inner_add_right, real_inner_smul_right, hee, hÑ₀orth',
      mul_one, mul_zero, add_zero]
  set U : Set R3 := Metric.ball n₀ ζ with hU
  have hUopen : IsOpen U := by rw [hU]; exact Metric.isOpen_ball
  have hUne : U.Nonempty := ⟨n₀, by rw [hU, Metric.mem_ball, dist_self]; exact hζ0⟩
  obtain ⟨ng, hngU, hngGood⟩ := heightGood_exists_in ψ hUopen hUne
  have hngbd : ‖ng - n₀‖ < ζ := by
    rw [hU, Metric.mem_ball, dist_eq_norm] at hngU
    exact hngU
  have hζ_le : ζ ≤ 1 / 4 := by
    have h := hIle X12 (by rw [hcaps]; simp)
    rw [hX12] at h
    rw [hζ]; linarith
  have hng_low : 1 - ζ ≤ ‖ng‖ := by
    have h1 : ‖n₀‖ - ‖ng‖ ≤ ‖n₀ - ng‖ := (abs_le.mp (abs_norm_sub_norm_le n₀ ng)).2
    rw [hn₀_norm, norm_sub_rev] at h1
    linarith only [h1, hngbd]
  have hng_high : ‖ng‖ ≤ 1 + ζ := by
    have h1 : ‖ng‖ - ‖n₀‖ ≤ ‖ng - n₀‖ := (abs_le.mp (abs_norm_sub_norm_le ng n₀)).2
    rw [hn₀_norm] at h1
    linarith only [h1, hngbd]
  have hng_ne : ng ≠ 0 := by
    intro h0
    have h1 : ‖ng‖ = 0 := by rw [h0, norm_zero]
    linarith [hng_low, hζ_le]
  have he_ng : |inner ℝ e ng - ηb| < ζ := by
    have h1 : inner ℝ e ng - ηb = inner ℝ e (ng - n₀) := by
      rw [inner_sub_right, he_n₀]
    rw [h1]
    calc |inner ℝ e (ng - n₀)| ≤ ‖e‖ * ‖ng - n₀‖ := abs_real_inner_le_norm _ _
      _ = ‖ng - n₀‖ := by rw [he1, one_mul]
      _ < ζ := hngbd
  -- ## 4. the witness
  set n : R3 := unitDir ng with hndef
  have hn1 : ‖n‖ = 1 := by rw [hndef]; exact unitDir_norm ng hng_ne
  set v : R3 := orthDir e n with hvdef
  set τ : ℝ := ‖v - e‖ with hτdef
  have hκ_eq : inner ℝ e n = (‖ng‖)⁻¹ * inner ℝ e ng := by
    rw [hndef, real_inner_comm, inner_unitDir, real_inner_comm]
  have hκ_pos : ηb / 3 ≤ inner ℝ e n := by
    rw [hκ_eq]
    have h1 : ηb / 2 ≤ inner ℝ e ng := by
      have hh := (abs_lt.mp he_ng).1
      have h2 : ζ = ηb / 2 := hζ_eq
      linarith only [hh, h2]
    have h2 : (‖ng‖)⁻¹ ≥ 2 / 3 := by
      have h3 : (1 : ℝ) + ζ ≤ 5 / 4 := by linarith only [hζ_le]
      have h4 : (‖ng‖)⁻¹ ≥ ((1 : ℝ) + ζ)⁻¹ := by
        have hpos : 0 < ‖ng‖ := by linarith only [hng_low, hζ_le]
        have hh := one_div_le_one_div_of_le hpos hng_high
        simpa [one_div] using hh
      have h5 : ((1 : ℝ) + ζ)⁻¹ ≥ 2 / 3 := by
        rw [ge_iff_le, ← one_div, le_div_iff₀ (by linarith only [hζ0] : (0:ℝ) < 1 + ζ)]
        linarith only [h3]
      linarith only [h4, h5]
    calc ηb / 3 = (2 / 3) * (ηb / 2) := by ring
      _ ≤ (‖ng‖)⁻¹ * inner ℝ e ng :=
          mul_le_mul h2 h1 (by linarith only [hηb0]) (inv_nonneg.mpr (norm_nonneg _))
  have hκ_le : inner ℝ e n ≤ 3 * ηb := by
    rw [hκ_eq]
    have h1 : inner ℝ e ng ≤ 3 * ηb / 2 := by
      have hh := (abs_lt.mp he_ng).2
      linarith only [hh, hζ_eq]
    have h2 : (‖ng‖)⁻¹ ≤ 2 := by
      have h3 : (3 : ℝ) / 4 ≤ ‖ng‖ := by linarith only [hng_low, hζ_le]
      have h4 : (‖ng‖)⁻¹ ≤ 4 / 3 := by
        have hh := one_div_le_one_div_of_le (show (0 : ℝ) < (3:ℝ)/4 by norm_num) h3
        simpa [one_div] using hh
      linarith only [h4]
    have h4 : 0 < inner ℝ e ng := by
      have hh := (abs_lt.mp he_ng).1
      linarith only [hh, hζ_eq, hηb0]
    calc (‖ng‖)⁻¹ * inner ℝ e ng ≤ 2 * (3 * ηb / 2) :=
          mul_le_mul h2 h1 (le_of_lt h4) (by linarith only [hηb0])
      _ = 3 * ηb := by ring
  have hκ_half : |inner ℝ e n| ≤ 1 / 2 := by
    rw [abs_of_nonneg (by linarith only [hκ_pos, hηb0])]
    have h := hIle X10 (by rw [hcaps]; simp)
    rw [hX10] at h
    nlinarith only [hκ_le, hηbdef, h]
  obtain ⟨hv1, hvn, hev, hτ_up, hτ_low⟩ :=
    orthDir_spec (e := e) (m := n) he1 hn1 (s := inner ℝ e n) rfl hκ_half
  have hτ_pos : 0 < τ := by
    have h : |inner ℝ e n| ≤ τ := by rw [hτdef]; exact hτ_low
    have h2 : 0 < |inner ℝ e n| := abs_pos.mpr (by
      intro h0
      have h3 := hκ_pos
      rw [h0] at h3
      linarith only [h3, hηb0])
    linarith only [h, h2]
  have hτ_I : τ ≤ I / 4 := by
    have h1 : τ ≤ Real.sqrt 2 * (3 * ηb) := by
      calc τ ≤ Real.sqrt 2 * |inner ℝ e n| := hτ_up
        _ ≤ Real.sqrt 2 * (3 * ηb) := by
            apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg 2)
            rw [abs_of_nonneg (by linarith only [hκ_pos, hηb0])]
            exact hκ_le
    have h2 : Real.sqrt 2 ≤ 2 := by
      nlinarith only [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), Real.sqrt_nonneg 2]
    have h5 : 0 ≤ 3 * ηb := by linarith only [hηb0]
    calc τ ≤ Real.sqrt 2 * (3 * ηb) := h1
      _ ≤ 2 * (3 * ηb) := mul_le_mul_of_nonneg_right h2 h5
      _ = I / 4 := by rw [hηbdef]; ring
  set h : ℝ := 6 * s * τ with hhdef
  have hh_pos : 0 < h := by rw [hhdef]; exact mul_pos (mul_pos (by norm_num) hs) hτ_pos
  -- the robustness radius
  set ρ : ℝ := min (τ / 12) (min (c00 / (96 * (M1 + 1)))
    (c00 / (96 * (MA1 + 1)))) with hρdef
  have hρpos : 0 < ρ := by
    rw [hρdef]
    exact lt_min (by linarith only [hτ_pos]) (lt_min (div_pos hc000 (by linarith only [hM10]))
      (div_pos hc000 (by linarith only [hMA10])))
  have hρ_le_tau : ρ ≤ τ / 12 := by rw [hρdef]; exact min_le_left _ _
  have hρMA1 : ρ * MA1 ≤ c00 / 96 := by
    have h1 : ρ ≤ c00 / (96 * (MA1 + 1)) := by
      rw [hρdef]; exact le_trans (min_le_right _ _) (min_le_right _ _)
    have h2 : ρ * MA1 ≤ c00 / (96 * (MA1 + 1)) * MA1 :=
      mul_le_mul_of_nonneg_right h1 (le_of_lt hMA10)
    have h3 : c00 / (96 * (MA1 + 1)) * MA1 ≤ c00 / 96 := by
      rw [div_mul_eq_mul_div,
        div_le_div_iff₀ (by linarith only [hMA10]) (by norm_num : (0:ℝ) < 96)]
      nlinarith only [hc000, hMA10]
    linarith only [h2, h3]
  have hρM1 : ρ * M1 ≤ c00 / 96 := by
    have h1 : ρ ≤ c00 / (96 * (M1 + 1)) := by
      rw [hρdef]; exact le_trans (min_le_right _ _) (min_le_left _ _)
    have h2 : ρ * M1 ≤ c00 / (96 * (M1 + 1)) * M1 := mul_le_mul_of_nonneg_right h1 hM10
    have h3 : c00 / (96 * (M1 + 1)) * M1 ≤ c00 / 96 := by
      rw [div_mul_eq_mul_div, div_le_div_iff₀ (by linarith only [hM10]) (by norm_num : (0:ℝ) < 96)]
      nlinarith only [hc000, hM10]
    linarith only [h2, h3]
  -- ## 5. the constraints
  have hI2 : I ≤ δg / (6 * s + 1) := by
    have h := hIle X2 (by rw [hcaps]; simp); rwa [hX2] at h
  have hI3 : I ≤ mbox / (6 * s + R2 + 2) := by
    have h := hIle X3 (by rw [hcaps]; simp); rwa [hX3] at h
  have hI4 : I ≤ m / (6 * s + R1 + 2) := by
    have h := hIle X4 (by rw [hcaps]; simp); rwa [hX4] at h
  have hI5 : I ≤ dv * lam / (2 * (6 * s + R1 + 2)) := by
    have h := hIle X5 (by rw [hcaps]; simp); rwa [hX5] at h
  have hI6 : I ≤ lam ^ 2 / (8 * M2 * (6 * s + R1) + 8) := by
    have h := hIle X6 (by rw [hcaps]; simp); rwa [hX6] at h
  have hI7 : I ≤ lam ^ 3 / (24 * Cv * (6 * s + R1) ^ 2 + 1) := by
    have h := hIle X7 (by rw [hcaps]; simp); rwa [hX7] at h
  have hI8 : I ≤ c00 * lam / (16 * M2 * (6 * s + R1) + 16) := by
    have h := hIle X8 (by rw [hcaps]; simp); rwa [hX8] at h
  have hI9 : I ≤ c00 / (16 * (M1 + 1)) := by
    have h := hIle X9 (by rw [hcaps]; simp); rwa [hX9] at h
  have hI11 : I ≤ c00 / (4 * (M1 + 1)) := by
    have h := hIle X11 (by rw [hcaps]; simp); rwa [hX11] at h
  have hτ_theta : τ ≤ θ' := by
    have h : I ≤ θ' := hIle θ' (by rw [hcaps]; simp)
    linarith only [hτ_I, h, hθ']
  have hτ_eps : τ ≤ εg / 4 := by
    have h : I ≤ εg := by
      have h := hIle X1 (by rw [hcaps]; simp); rwa [hX1] at h
    linarith only [hτ_I, h]
  -- (c1) the tilt is small enough for the no-grazing hypothesis
  have hc1 : τ < εg := by linarith only [hτ_eps, hεg]
  -- (c2) `h < δg`
  have hc2 : h < δg := by
    have h : τ * (4 * (6 * s + 1)) ≤ δg :=
      rb_mul_le_of_le_quarter (by linarith only [hs]) (by linarith only [hτ_I, hI2])
    have hh : 6 * s * τ ≤ δg / 4 := by nlinarith only [h, hs, hτ_pos]
    rw [hhdef]
    linarith only [hh, hδg]
  -- (c3) the bound on the box sphere
  have hc3 : τ * (6 * s + R2) ≤ mbox := by
    have h : τ * (4 * (6 * s + R2 + 2)) ≤ mbox :=
      rb_mul_le_of_le_quarter (by linarith only [hs, hR20])
        (by linarith only [hτ_I, hI3])
    nlinarith only [h, hs, hR20, hτ_pos]
  -- (c4) the covering constraint
  have hc4 : τ * (6 * s + R1) < m := by
    have h : τ * (4 * (6 * s + R1 + 2)) ≤ m :=
      rb_mul_le_of_le_quarter (by linarith only [hs, hR1def])
        (by linarith only [hτ_I, hI4])
    nlinarith only [h, hs, hR1def, hτ_pos, hm0]
  -- (c5a) `2H/lam ≤ dv`
  have hc5a : 2 * (τ * (6 * s + R1)) ≤ dv * lam := by
    have h : τ * (4 * (2 * (6 * s + R1 + 2))) ≤ dv * lam :=
      rb_mul_le_of_le_quarter (by linarith only [hs, hR1def])
        (by linarith only [hτ_I, hI5])
    nlinarith only [h, hs, hR1def, hτ_pos]
  -- (c5b) `M2 * (2H/lam) ≤ lam/2`
  have hc5b : 2 * M2 * (τ * (6 * s + R1)) ≤ lam ^ 2 / 2 := by
    have h : τ * (4 * (8 * M2 * (6 * s + R1) + 8)) ≤ lam ^ 2 :=
      rb_mul_le_of_le_quarter (by nlinarith only [hs, hR1def, hM20])
        (by linarith only [hτ_I, hI6])
    nlinarith only [h, hs, hR1def, hM20, hτ_pos, hlam0]
  -- (c5c) the vertical-crossing positivity
  have hc5c : 4 * Cv * τ ^ 2 * (6 * s + R1) ^ 2 / lam ^ 2 < τ * lam / 6 := by
    have h : τ * (4 * (24 * Cv * (6 * s + R1) ^ 2 + 1)) ≤ lam ^ 3 :=
      rb_mul_le_of_le_quarter
        (by nlinarith only [hCv0, hs, hR1def, sq_nonneg (6 * s + R1)])
        (by linarith only [hτ_I, hI7])
    have h2 : 24 * Cv * (6 * s + R1) ^ 2 * τ ≤ lam ^ 3 / 4 := by
      nlinarith only [h, hτ_pos, hCv0, hs, hR1def]
    have h3 : 4 * Cv * (6 * s + R1) ^ 2 * τ ≤ lam ^ 3 / 24 := by linarith only [h2]
    have h4 : 4 * Cv * (6 * s + R1) ^ 2 * τ * τ ≤ (lam ^ 3 / 24) * τ :=
      mul_le_mul_of_nonneg_right h3 (le_of_lt hτ_pos)
    have hX : 0 < τ * lam ^ 3 := mul_pos hτ_pos (pow_pos hlam0 3)
    have h5 : τ * lam ^ 3 / 24 < τ * lam ^ 3 / 6 := by linarith only [hX]
    have h6 : 4 * Cv * τ ^ 2 * (6 * s + R1) ^ 2 ≤ τ * lam ^ 3 / 24 := by
      nlinarith only [h4]
    rw [div_lt_iff₀ (pow_pos hlam0 2)]
    linarith only [h5, h6]
  -- (c6a) the non-vertical-crossing bound
  have hc6a : 2 * M2 * (τ * (6 * s + R1)) ≤ c00 * lam / 16 := by
    have h : τ * (4 * (16 * M2 * (6 * s + R1) + 16)) ≤ c00 * lam :=
      rb_mul_le_of_le_quarter (by nlinarith only [hs, hR1def, hM20])
        (by linarith only [hτ_I, hI8])
    nlinarith only [h, hs, hR1def, hM20, hτ_pos, hlam0, hc000]
  -- (c6b) the other non-vertical-crossing bound
  have hc6b : inner ℝ e n * M1 ≤ c00 / 16 := by
    have h2 : 3 * ηb ≤ I / 8 := by rw [hηbdef]; linarith only []
    have h3 : inner ℝ e n ≤ (c00 / (16 * (M1 + 1))) / 8 := by
      linarith only [hκ_le, h2, hI9]
    have h4 : inner ℝ e n * M1 ≤ ((c00 / (16 * (M1 + 1))) / 8) * M1 :=
      mul_le_mul_of_nonneg_right h3 hM10
    have h5 : ((c00 / (16 * (M1 + 1))) / 8) * M1 ≤ c00 / 16 := by
      have h6 : (c00 / (16 * (M1 + 1))) / 8 = c00 / (128 * (M1 + 1)) := by
        rw [div_div, show (16 * (M1 + 1)) * 8 = 128 * (M1 + 1) by ring]
      rw [h6, div_mul_eq_mul_div,
        div_le_div_iff₀ (by linarith only [hM10]) (by norm_num : (0:ℝ) < 16)]
      nlinarith only [hM10, hc000]
    linarith only [h4, h5]
  -- (c7) the ball radius constraints
  have hc7a : ζ ≤ 1 / 2 := by linarith only [hζ_le]
  have hc7b : ζ * M1 ≤ c00 / 4 := by
    have h1 : ζ * (192 * (M1 + 1)) ≤ c00 := by
      have h3 : (c00 / (4 * (M1 + 1))) / 48 = c00 / (192 * (M1 + 1)) := by
        rw [div_div, show (4 * (M1 + 1)) * 48 = 192 * (M1 + 1) by ring]
      have h4 : ζ ≤ c00 / (192 * (M1 + 1)) := by
        calc ζ = I / 48 := hζ
          _ ≤ (c00 / (4 * (M1 + 1))) / 48 := div_le_div_of_nonneg_right hI11 (by norm_num)
          _ = c00 / (192 * (M1 + 1)) := h3
      exact rb_mul_le_of_le_div (by linarith only [hM10]) h4
    have hden : 0 < 192 * (M1 + 1) := by linarith only [hM10]
    have h1' : ζ * (192 * (M1 + 1)) * M1 ≤ c00 * M1 := mul_le_mul_of_nonneg_right h1 hM10
    have h6 : ζ * M1 ≤ (c00 * M1) / (192 * (M1 + 1)) := by
      rw [le_div_iff₀ hden]; nlinarith only [h1']
    have h7 : (c00 * M1) / (192 * (M1 + 1)) ≤ c00 / 4 := by
      rw [div_le_div_iff₀ hden (by norm_num : (0:ℝ) < 4)]
      nlinarith only [hM10, hc000]
    linarith only [h6, h7]
  -- ## 5b. the arc constraints
  have hI13 : I ≤ X13 := hIle X13 (by rw [hcaps]; simp)
  have hI14 : I ≤ X14 := hIle X14 (by rw [hcaps]; simp)
  have hI15 : I ≤ X15 := hIle X15 (by rw [hcaps]; simp)
  have hI16 : I ≤ X16 := hIle X16 (by rw [hcaps]; simp)
  have hI17 : I ≤ X17 := hIle X17 (by rw [hcaps]; simp)
  have hX17' : X17 = c00 / (96 * (MA1 + 1)) := hX17
  -- the `h`-interval of the arc clauses sits inside `Ioo (-η) η`
  have h2h_half : 2 * h ≤ η / 2 := by
    have hτ13 : τ ≤ η / (384 * s + 384) := by
      have h2 : (η / (96 * s + 96)) / 4 = η / (384 * s + 384) := by
        rw [div_div, show (96 * s + 96) * 4 = 384 * s + 384 by ring]
      rw [hX13] at hI13
      linarith only [hτ_I, hI13, h2]
    have h24 : 24 * s * τ ≤ η := by
      have h1 : 24 * s * τ ≤ 24 * s * (η / (384 * s + 384)) :=
        mul_le_mul_of_nonneg_left hτ13 (by positivity)
      have h2 : 24 * s * (η / (384 * s + 384)) ≤ η := by
        rw [mul_div_assoc', div_le_iff₀ (by positivity : (0:ℝ) < 384 * s + 384)]
        nlinarith only [hη.le, hs.le]
      linarith only [h1, h2]
    rw [hhdef]; linarith only [h24]
  -- the arc directions have bounded speed
  have hτMA1 : τ * MA1 ≤ 1 / 4 := by
    have hτ14 : τ ≤ 1 / (64 * (MA1 + 2)) := by
      have h2 : (1 / (16 * (MA1 + 2))) / 4 = 1 / (64 * (MA1 + 2)) := by
        rw [div_div, show (16 * (MA1 + 2)) * 4 = 64 * (MA1 + 2) by ring]
      rw [hX14] at hI14
      linarith only [hτ_I, hI14, h2]
    have h3 : τ * MA1 ≤ (1 / (64 * (MA1 + 2))) * MA1 :=
      mul_le_mul_of_nonneg_right hτ14 (le_of_lt hMA10)
    have h4 : (1 / (64 * (MA1 + 2))) * MA1 ≤ 1 / 4 := by
      rw [div_mul_eq_mul_div,
        div_le_div_iff₀ (by positivity) (by norm_num : (0:ℝ) < 4)]
      nlinarith only [hMA10]
    linarith only [h3, h4]
  -- the quadratic bound for a vertical arc
  have hMA4sq : ∀ t : ℝ, |t| ≤ 2 * h → MA4 * t ^ 2 ≤ τ / 4 := by
    intro t ht
    have ht2 : t ^ 2 ≤ 144 * s ^ 2 * τ ^ 2 := by
      have h1 := abs_le.mp ht
      have h2 : 2 * h = 12 * s * τ := by rw [hhdef]; ring
      nlinarith only [h1.1, h1.2, h2, hs, hτ_pos]
    have hτ15 : τ ≤ 1 / (576 * MA4 * s ^ 2 + 4) := by
      have h2 : (1 / (144 * MA4 * s ^ 2 + 1)) / 4 = 1 / (576 * MA4 * s ^ 2 + 4) := by
        rw [div_div, show (144 * MA4 * s ^ 2 + 1) * 4 = 576 * MA4 * s ^ 2 + 4 by ring]
      rw [hX15] at hI15
      linarith only [hτ_I, hI15, h2]
    have hkey : MA4 * s ^ 2 * τ ≤ 1 / 576 := by
      have h3 : MA4 * s ^ 2 * τ ≤ MA4 * s ^ 2 * (1 / (576 * MA4 * s ^ 2 + 4)) :=
        mul_le_mul_of_nonneg_left hτ15 (by positivity)
      have h4 : MA4 * s ^ 2 * (1 / (576 * MA4 * s ^ 2 + 4)) ≤ 1 / 576 := by
        rw [mul_one_div, div_le_div_iff₀ (by positivity) (by norm_num : (0:ℝ) < 576)]
        nlinarith only [hMA40, hs, sq_nonneg s]
      linarith only [h3, h4]
    calc MA4 * t ^ 2 ≤ MA4 * (144 * s ^ 2 * τ ^ 2) :=
          mul_le_mul_of_nonneg_left ht2 (le_of_lt hMA40)
      _ = 144 * (MA4 * s ^ 2 * τ) * τ := by ring
      _ ≤ 144 * (1 / 576) * τ := by
          have h9 := mul_le_mul_of_nonneg_right hkey (le_of_lt hτ_pos)
          nlinarith only [h9]
      _ = τ / 4 := by ring
  -- the Lipschitz bound for the arc directions
  have h12MA2 : 12 * MA2 * s * τ ≤ c00 / 48 := by
    have hτ16 : τ ≤ c00 / (576 * MA2 * s + 4) := by
      have h2 : (c00 / (144 * MA2 * s + 1)) / 4 = c00 / (576 * MA2 * s + 4) := by
        rw [div_div, show (144 * MA2 * s + 1) * 4 = 576 * MA2 * s + 4 by ring]
      rw [hX16] at hI16
      linarith only [hτ_I, hI16, h2]
    have h3 : 12 * MA2 * s * τ ≤ 12 * MA2 * s * (c00 / (576 * MA2 * s + 4)) :=
      mul_le_mul_of_nonneg_left hτ16 (by positivity)
    have h4 : 12 * MA2 * s * (c00 / (576 * MA2 * s + 4)) ≤ c00 / 48 := by
      rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num : (0:ℝ) < 48)]
      nlinarith only [hMA20, hs, hc000]
    linarith only [h3, h4]
  have h3ηb : 3 * ηb ≤ c00 / 12 := by
    have h : I ≤ c00 / 16 := by
      refine le_trans hI9 ?_
      rw [div_le_div_iff₀ (by linarith only [hM10]) (by norm_num : (0:ℝ) < 16)]
      nlinarith only [hc000, hM10]
    rw [hηbdef]; linarith only [h, hc000]
  have hζMA1 : ζ * (MA1 + 1) ≤ c00 / 4 := by
    have h1 : ζ ≤ c00 / (4608 * (MA1 + 1)) := by
      calc ζ = I / 48 := hζ
        _ ≤ X17 / 48 := div_le_div_of_nonneg_right hI17 (by norm_num)
        _ = c00 / (4608 * (MA1 + 1)) := by
            rw [hX17', div_div, show (96 * (MA1 + 1)) * 48 = 4608 * (MA1 + 1) by ring]
    have h2 : ζ * (MA1 + 1) ≤ (c00 / (4608 * (MA1 + 1))) * (MA1 + 1) :=
      mul_le_mul_of_nonneg_right h1 (by linarith only [hMA10])
    have h3 : (c00 / (4608 * (MA1 + 1))) * (MA1 + 1) ≤ c00 / 4 := by
      rw [div_mul_eq_mul_div,
        div_le_div_iff₀ (by positivity) (by norm_num : (0:ℝ) < 4)]
      nlinarith only [hc000, hMA10]
    linarith only [h2, h3]
  -- ## 6. the witness
  have hv1' : ‖v‖ = 1 := by rw [hvdef]; exact hv1
  have hvn' : inner ℝ v n = 0 := by rw [hvdef]; exact hvn
  have hgood : HeightGood ψ n := by
    rw [hndef, unitDir]
    exact (heightGood_smul_iff ψ (inv_ne_zero (norm_ne_zero_iff.mpr hng_ne)) ng).mpr hngGood
  refine ⟨v, n, h, ρ, hv1', hn1, hvn', hgood, ?_, ?_, hh_pos, hρpos, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_⟩
  · -- `‖v - e‖ ≤ θ'`
    have hτeq : ‖v - Work.BoxShrink.shiftVσ σ 1‖ = τ := by rw [← hedef]
    rw [hτeq]
    exact hτ_theta
  · -- `‖v - e‖ ≤ εg / 4`
    have hτeq : ‖v - Work.BoxShrink.shiftVσ σ 1‖ = τ := by rw [← hedef]
    rw [hτeq]
    exact hτ_eps
  · -- the size condition
    have hτeq : ‖v - Work.BoxShrink.shiftVσ σ 1‖ = τ := by rw [← hedef]
    rw [hτeq, hhdef]
    have h5 : 0 < s * τ := mul_pos hs hτ_pos
    have h6 : 2 * (τ * R1) = 5 * (s * τ) := by rw [hR1def]; ring
    linarith only [h5, h6]
  · -- clause 1: on the box sphere
    intro t ht
    have hsb : slabHeight K c u v t = inner ℝ v (K.curve t) - (inner ℝ v c + u) := rfl
    rw [← hsb]
    have hR2b : ‖K.curve t - c‖ ≤ R2 := hR2 _ ht
    have hmb : mbox ≤ |flatHeight K c σ u t| := by
      rw [flatHeight_apply]; exact hmbox t ht
    have hdiff : |slabHeight K c u v t - flatHeight K c σ u t| ≤ τ * R2 := by
      rw [slabHeight_sub_flatHeight]
      calc |inner ℝ (v - e) (K.curve t - c)| ≤ ‖v - e‖ * ‖K.curve t - c‖ :=
            abs_real_inner_le_norm _ _
        _ ≤ τ * R2 := by rw [hτdef]; exact mul_le_mul_of_nonneg_left hR2b (norm_nonneg _)
    have hkey : mbox - τ * R2 ≤ |slabHeight K c u v t| := by
      have h1 := abs_sub_abs_le_abs_sub (flatHeight K c σ u t) (slabHeight K c u v t)
      rw [abs_sub_comm (flatHeight K c σ u t) (slabHeight K c u v t)] at h1
      linarith only [h1, hmb, hdiff]
    rw [hhdef]
    linarith only [hkey, hc3]
  · -- clause 2: at the critical points of the tilted height
    intro t htbox hderiv
    have hve : ‖v - Work.BoxShrink.shiftVσ σ 1‖ < εg := by
      rw [← hedef, show ‖v - e‖ = τ from rfl]
      linarith only [hτ_eps, hεg]
    have := hnograz v hv1' hve t htbox hderiv
    rw [hhdef]
    linarith only [this, hc2]
  · -- clause 3: the slab region, robustly in the normal direction
    intro nn hnn1 hnnnear t htbox hslab
    obtain ⟨t', ht'Icc, hct', hdt'⟩ := exists_period_reduce K t
    have ht'box : K.curve t' ∈ Submission.PBox s c σ := by rw [hct']; exact htbox
    have ht'cl : K.curve t' ∈ closure (Submission.PBox s c σ) := subset_closure ht'box
    have hslab' : |slabHeight K c u v t'| ≤ h := by
      rw [slabHeight_apply, hct']
      exact hslab
    have hdiff' : |slabHeight K c u v t' - flatHeight K c σ u t'| ≤ τ * R1 := by
      rw [slabHeight_sub_flatHeight]
      calc |inner ℝ (v - e) (K.curve t' - c)| ≤ ‖v - e‖ * ‖K.curve t' - c‖ :=
            abs_real_inner_le_norm _ _
        _ ≤ τ * R1 := by
            rw [hτdef]
            exact mul_le_mul_of_nonneg_left (hR1b _ ht'box) (norm_nonneg _)
    have hφ : |flatHeight K c σ u t'| ≤ τ * (6 * s + R1) := by
      have h1 := abs_sub_abs_le_abs_sub (flatHeight K c σ u t') (slabHeight K c u v t')
      rw [abs_sub_comm (flatHeight K c σ u t') (slabHeight K c u v t')] at h1
      linarith only [h1, hslab', hdiff']
    have hderiv_eq : deriv (fun r : ℝ => inner ℝ nn (K.curve r)) t
        = deriv (fun r : ℝ => inner ℝ nn (K.curve r)) t' := by
      rw [deriv_inner_curve_const, deriv_inner_curve_const, hdt']
    rw [hderiv_eq, deriv_inner_eq_mul_add_vertVel K he1 t', inner_shiftVσ_one,
      show inner ℝ nn e = inner ℝ e nn from real_inner_comm e nn,
      mul_comm (inner ℝ e nn) ((deriv K.curve t') (σ 2))]
    by_cases hfar : |flatHeight K c σ u t'| < m
    · obtain ⟨ts, htsT, hbt⟩ := hcover t' ht'Icc ht'cl hfar
      have htsIcc : ts ∈ Set.Icc 0 (2 * Real.pi) := (mem_crossingSet.mp htsT).1
      have htscl : K.curve ts ∈ closure (Submission.PBox s c σ) := (mem_crossingSet.mp htsT).2.1
      have htslv : (K.curve ts) (σ 2) = c (σ 2) + u := (mem_crossingSet.mp htsT).2.2
      have hspd : lam ≤ |deriv (flatHeight K c σ u) ts| := hlam ts htsT
      have hspd' : lam ≤ |(deriv K.curve ts) (σ 2)| := by
        rw [← deriv_flatHeight]; exact hspd
      have hdist : |t' - ts| ≤ 2 * (τ * (6 * s + R1)) / lam := by
        have h1 : lam * |t' - ts| ≤ 2 * (τ * (6 * s + R1)) :=
          le_trans hbt (by linarith only [hφ])
        rw [le_div_iff₀ hlam0]
        linarith only [h1]
      by_cases hv : vertVel K e ts = 0
      · -- the crossing is vertical
        have hacc : vertAcc K e ts = 0 := hnobend ts htscl htslv hv
        have hquad : ‖vertVel K e t'‖ ≤ Cv * (t' - ts) ^ 2 := by
          refine hCv ts hv hacc t' ?_
          have h2H : 2 * (τ * (6 * s + R1)) / lam ≤ dv := by
            rw [div_le_iff₀ hlam0]; nlinarith only [hc5a]
          linarith only [hdist, h2H]
        have hα_low : lam / 2 ≤ |(deriv K.curve t') (σ 2)| := by
          have hmvt := noGraze_mvt_coord (K := K) hM2 σ t' ts
          have h3 : M2 * |t' - ts| ≤ lam / 2 := by
            have h4 : M2 * (2 * (τ * (6 * s + R1))) ≤ lam ^ 2 / 2 := by
              linarith only [hc5b]
            have h5 : M2 * (2 * (τ * (6 * s + R1))) / lam ≤ lam / 2 := by
              rw [div_le_iff₀ hlam0]
              nlinarith only [h4, hlam0]
            have h6 : M2 * (2 * (τ * (6 * s + R1)) / lam)
                = M2 * (2 * (τ * (6 * s + R1))) / lam := by ring
            calc M2 * |t' - ts| ≤ M2 * (2 * (τ * (6 * s + R1)) / lam) :=
                  mul_le_mul_of_nonneg_left hdist hM20
              _ = M2 * (2 * (τ * (6 * s + R1))) / lam := h6
              _ ≤ lam / 2 := h5
          have h7 : |(deriv K.curve ts) (σ 2)| - |(deriv K.curve t') (σ 2)| ≤ M2 * |t' - ts| := by
            have h8 := abs_sub_abs_le_abs_sub ((deriv K.curve ts) (σ 2)) ((deriv K.curve t') (σ 2))
            rw [abs_sub_comm ((deriv K.curve ts) (σ 2)) ((deriv K.curve t') (σ 2))] at h8
            linarith only [h8, hmvt]
          linarith only [h7, h3, hspd']
        have hκge : τ / 2 ≤ |inner ℝ e n| := by
          have h1 : τ ≤ Real.sqrt 2 * |inner ℝ e n| := hτ_up
          have h2 : Real.sqrt 2 ≤ 2 := by
            nlinarith only [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num),
              Real.sqrt_nonneg 2]
          nlinarith only [h1, h2, abs_nonneg (inner ℝ e n)]
        have hκge_nn : τ / 2 - ρ ≤ |inner ℝ e nn| := by
          have h1 : |inner ℝ e n| - |inner ℝ e nn| ≤ |inner ℝ e n - inner ℝ e nn| :=
            abs_sub_abs_le_abs_sub _ _
          have h2 : |inner ℝ e n - inner ℝ e nn| ≤ ‖nn - n‖ := by
            rw [← inner_sub_right]
            calc |inner ℝ e (n - nn)| ≤ ‖e‖ * ‖n - nn‖ := abs_real_inner_le_norm _ _
              _ = ‖nn - n‖ := by rw [he1, one_mul, norm_sub_rev]
          linarith only [h1, h2, hnnnear, hκge]
        have hA : lam / 2 * (τ / 2 - ρ) - Cv * (t' - ts) ^ 2
            ≤ |(deriv K.curve t') (σ 2) * inner ℝ e nn + inner ℝ nn (vertVel K e t')| := by
          have h1 : lam / 2 * (τ / 2 - ρ) ≤ |(deriv K.curve t') (σ 2)| * |inner ℝ e nn| :=
            mul_le_mul hα_low hκge_nn (by linarith only [hτ_pos, hρ_le_tau]) (abs_nonneg _)
          have h2 : |inner ℝ nn (vertVel K e t')| ≤ ‖vertVel K e t'‖ :=
            rb_abs_inner_unit_le hnn1
          have h3 := rb_le_abs_add ((deriv K.curve t') (σ 2) * inner ℝ e nn)
            (inner ℝ nn (vertVel K e t'))
          have h4 : |(deriv K.curve t') (σ 2) * inner ℝ e nn|
              = |(deriv K.curve t') (σ 2)| * |inner ℝ e nn| := abs_mul _ _
          linarith only [h1, h2, h3, h4, hquad]
        have hfinal : 0 < lam / 2 * (τ / 2 - ρ) - Cv * (t' - ts) ^ 2 := by
          have hsq : (t' - ts) ^ 2 ≤ (2 * (τ * (6 * s + R1)) / lam) ^ 2 := by
            have h2 := abs_le.mp hdist
            have hh0 : 0 ≤ 2 * (τ * (6 * s + R1)) / lam :=
              div_nonneg (by nlinarith only [hτ_pos, hs, hR1def]) (le_of_lt hlam0)
            nlinarith only [h2.1, h2.2, hh0]
          have h1 : Cv * (t' - ts) ^ 2 ≤ Cv * (2 * (τ * (6 * s + R1)) / lam) ^ 2 :=
            mul_le_mul_of_nonneg_left hsq (le_of_lt hCv0)
          have h2 : Cv * (2 * (τ * (6 * s + R1)) / lam) ^ 2 < τ * lam / 6 := by
            have h3 : (2 * (τ * (6 * s + R1)) / lam) ^ 2
                = 4 * τ ^ 2 * (6 * s + R1) ^ 2 / lam ^ 2 := by
              rw [div_pow, mul_pow]
              ring
            rw [h3]
            have h4 : Cv * (4 * τ ^ 2 * (6 * s + R1) ^ 2 / lam ^ 2) < τ * lam / 6 := by
              have h4b : Cv * (4 * τ ^ 2 * (6 * s + R1) ^ 2 / lam ^ 2)
                  = 4 * Cv * τ ^ 2 * (6 * s + R1) ^ 2 / lam ^ 2 := by ring
              rw [h4b]; exact hc5c
            linarith only [h4]
          have hρb : lam / 2 * ρ ≤ lam * τ / 24 := by
            have h := mul_le_mul_of_nonneg_left hρ_le_tau
              (by linarith only [hlam0] : (0 : ℝ) ≤ lam / 2)
            nlinarith only [h]
          nlinarith only [h1, h2, hρb, hτ_pos, hlam0]
        exact abs_pos.mp (by linarith only [hA, hfinal])
      · -- the crossing is not vertical
        have hc00t : c00 ≤ |inner ℝ Ñ₀ (vertVel K e ts)| := hc00le ts htsT hv
        have hng_le : ‖ng‖ ≤ 3 / 2 := by linarith only [hng_high, hζ_le]
        have hng_ge : (1 : ℝ) / 2 ≤ ‖ng‖ := by linarith only [hng_low, hζ_le]
        have hw0 : inner ℝ e (vertVel K e ts) = 0 := by
          rw [real_inner_comm (vertVel K e ts) e]
          exact inner_vertVel_eq_zero K he1 ts
        have hn₀w : inner ℝ n₀ (vertVel K e ts)
            = Real.sqrt (1 - ηb ^ 2) * inner ℝ Ñ₀ (vertVel K e ts) := by
          rw [hn₀def, inner_add_left, real_inner_smul_left, real_inner_smul_left, hw0,
            mul_zero, zero_add]
        have h1 : c00 / 2 ≤ |inner ℝ n₀ (vertVel K e ts)| := by
          rw [hn₀w, abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
          have h2 : (1 : ℝ) / 2 ≤ Real.sqrt (1 - ηb ^ 2) := by
            rw [← Real.sqrt_sq (show (0 : ℝ) ≤ 1 / 2 by norm_num)]
            apply Real.sqrt_le_sqrt
            nlinarith only [hηb_le, hηb0]
          calc c00 / 2 = (1 / 2) * c00 := by ring
            _ ≤ Real.sqrt (1 - ηb ^ 2) * |inner ℝ Ñ₀ (vertVel K e ts)| :=
                mul_le_mul h2 hc00t (le_of_lt hc000) (Real.sqrt_nonneg _)
        have h2 : c00 / 4 ≤ |inner ℝ ng (vertVel K e ts)| := by
          have h3 : |inner ℝ ng (vertVel K e ts) - inner ℝ n₀ (vertVel K e ts)|
              ≤ ‖ng - n₀‖ * ‖vertVel K e ts‖ := by
            rw [← inner_sub_left]
            exact abs_real_inner_le_norm _ _
          have hwM1 : ‖vertVel K e ts‖ ≤ M1 :=
            le_trans (norm_perpProj_le (e := e) (x := deriv K.curve ts) he1) (hM1 ts)
          have h4 : ‖ng - n₀‖ * ‖vertVel K e ts‖ ≤ ζ * M1 :=
            mul_le_mul (le_of_lt hngbd) hwM1 (norm_nonneg _) (le_of_lt hζ0)
          have h5 : |inner ℝ n₀ (vertVel K e ts)| - ζ * M1
              ≤ |inner ℝ ng (vertVel K e ts)| := by
            have hh := abs_sub_abs_le_abs_sub (inner ℝ n₀ (vertVel K e ts))
              (inner ℝ ng (vertVel K e ts))
            rw [abs_sub_comm (inner ℝ n₀ (vertVel K e ts)) (inner ℝ ng (vertVel K e ts))] at hh
            linarith only [hh, h3, h4]
          linarith only [h1, h5, hc7b]
        have h3 : c00 / 6 ≤ |inner ℝ n (vertVel K e ts)| := by
          have hunit : inner ℝ n (vertVel K e ts)
              = (‖ng‖)⁻¹ * inner ℝ ng (vertVel K e ts) := by
            rw [hndef, inner_unitDir]
          rw [hunit, abs_mul, abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _))]
          have h4 : (3 / 2 : ℝ)⁻¹ ≤ (‖ng‖)⁻¹ := by
            have hh := one_div_le_one_div_of_le (by linarith only [hng_ge]) hng_le
            simpa [one_div] using hh
          calc c00 / 6 = (3 / 2 : ℝ)⁻¹ * (c00 / 4) := by ring
            _ ≤ (‖ng‖)⁻¹ * |inner ℝ ng (vertVel K e ts)| :=
                mul_le_mul h4 h2 (by linarith only [hc000]) (inv_nonneg.mpr (norm_nonneg _))
        have h4 : c00 / 6 - c00 / 16 ≤ |inner ℝ n (vertVel K e t')| := by
          have h5 : |inner ℝ n (vertVel K e t') - inner ℝ n (vertVel K e ts)|
              ≤ ‖vertVel K e t' - vertVel K e ts‖ := by
            rw [← inner_sub_right]
            exact rb_abs_inner_unit_le (n := n) (w := vertVel K e t' - vertVel K e ts) hn1
          have h6 := noGraze_mvt_vertVel (K := K) he1 hM2 t' ts
          have h7 : M2 * |t' - ts| ≤ 2 * M2 * (τ * (6 * s + R1)) / lam := by
            have h7b : M2 * (2 * (τ * (6 * s + R1)) / lam)
                = M2 * (2 * (τ * (6 * s + R1))) / lam := by ring
            calc M2 * |t' - ts| ≤ M2 * (2 * (τ * (6 * s + R1)) / lam) :=
                  mul_le_mul_of_nonneg_left hdist hM20
              _ = M2 * (2 * (τ * (6 * s + R1))) / lam := h7b
              _ = 2 * M2 * (τ * (6 * s + R1)) / lam := by ring
          have h8 : 2 * M2 * (τ * (6 * s + R1)) / lam ≤ c00 / 16 := by
            rw [div_le_iff₀ hlam0]; nlinarith only [hc6a, hlam0]
          have h9 : |inner ℝ n (vertVel K e ts)| - |inner ℝ n (vertVel K e t')|
              ≤ |inner ℝ n (vertVel K e t') - inner ℝ n (vertVel K e ts)| := by
            have hh := abs_sub_abs_le_abs_sub (inner ℝ n (vertVel K e ts))
              (inner ℝ n (vertVel K e t'))
            rw [abs_sub_comm (inner ℝ n (vertVel K e ts)) (inner ℝ n (vertVel K e t'))] at hh
            exact hh
          linarith only [h3, h5, h6, h7, h8, h9]
        have h4nn : c00 / 6 - c00 / 16 - ρ * M1 ≤ |inner ℝ nn (vertVel K e t')| := by
          have h5 : |inner ℝ nn (vertVel K e t') - inner ℝ n (vertVel K e t')|
              ≤ ‖nn - n‖ * ‖vertVel K e t'‖ := by
            rw [← inner_sub_left]
            exact abs_real_inner_le_norm _ _
          have hwM1 : ‖vertVel K e t'‖ ≤ M1 :=
            le_trans (norm_perpProj_le (e := e) (x := deriv K.curve t') he1) (hM1 t')
          have h6 : ‖nn - n‖ * ‖vertVel K e t'‖ ≤ ρ * M1 :=
            mul_le_mul (le_of_lt hnnnear) hwM1 (norm_nonneg _) (le_of_lt hρpos)
          have h7 : |inner ℝ n (vertVel K e t')| - |inner ℝ nn (vertVel K e t')| ≤ ρ * M1 := by
            have hh := abs_sub_abs_le_abs_sub (inner ℝ n (vertVel K e t'))
              (inner ℝ nn (vertVel K e t'))
            rw [abs_sub_comm (inner ℝ n (vertVel K e t')) (inner ℝ nn (vertVel K e t'))] at hh
            linarith only [hh, h5, h6]
          linarith only [h4, h7]
        have hx_up : |(deriv K.curve t') (σ 2) * inner ℝ e nn| ≤ c00 / 16 + M1 * ρ := by
          have hα_le : |(deriv K.curve t') (σ 2)| ≤ M1 := by
            have h10 := abs_real_inner_le_norm e (deriv K.curve t')
            rw [he1, one_mul, inner_shiftVσ_one] at h10
            exact le_trans h10 (hM1 t')
          have hκnn : |inner ℝ e nn| ≤ inner ℝ e n + ρ := by
            have hκen : |inner ℝ e n| = inner ℝ e n :=
              abs_of_nonneg (by linarith only [hκ_pos, hηb0])
            have h2 : |inner ℝ e (nn - n)| ≤ ‖nn - n‖ := by
              calc |inner ℝ e (nn - n)| ≤ ‖e‖ * ‖nn - n‖ := abs_real_inner_le_norm _ _
                _ = ‖nn - n‖ := by rw [he1, one_mul]
            have hsplit : inner ℝ e nn = inner ℝ e n + inner ℝ e (nn - n) := by
              rw [← inner_add_right]; congr 1; abel
            calc |inner ℝ e nn| = |inner ℝ e n + inner ℝ e (nn - n)| := by rw [hsplit]
              _ ≤ |inner ℝ e n| + |inner ℝ e (nn - n)| := abs_add_le _ _
              _ ≤ inner ℝ e n + ρ := by rw [hκen]; linarith only [h2, hnnnear]
          rw [abs_mul]
          calc |(deriv K.curve t') (σ 2)| * |inner ℝ e nn| ≤ M1 * (inner ℝ e n + ρ) :=
                mul_le_mul hα_le hκnn (abs_nonneg _) hM10
            _ = M1 * inner ℝ e n + M1 * ρ := by ring
            _ ≤ c00 / 16 + M1 * ρ := by
                have hb : M1 * inner ℝ e n ≤ c00 / 16 := by
                  rw [mul_comm]; exact hc6b
                linarith only [hb]
        have hA : c00 / 6 - c00 / 16 - ρ * M1 - (c00 / 16 + M1 * ρ)
            ≤ |(deriv K.curve t') (σ 2) * inner ℝ e nn + inner ℝ nn (vertVel K e t')| := by
          have h1 := rb_le_abs_add (inner ℝ nn (vertVel K e t'))
            ((deriv K.curve t') (σ 2) * inner ℝ e nn)
          rw [add_comm] at h1
          linarith only [h1, h4nn, hx_up]
        have hfrac : 0 < c00 / 6 - c00 / 16 - ρ * M1 - (c00 / 16 + M1 * ρ) := by
          nlinarith only [hc000, hρM1]
        exact abs_pos.mp (by linarith only [hA, hfrac])
    · -- far from every crossing: the slab misses the knot
      exfalso
      push Not at hfar
      have h1 := abs_sub_abs_le_abs_sub (flatHeight K c σ u t') (slabHeight K c u v t')
      rw [abs_sub_comm (flatHeight K c σ u t') (slabHeight K c u v t')] at h1
      linarith only [h1, hdiff', hfar, hslab', hc4]
  · -- clause 4: the slab boundary
    intro t htbox hEq hderiv
    exfalso
    have hve : ‖v - Work.BoxShrink.shiftVσ σ 1‖ < εg := by
      rw [← hedef, show ‖v - e‖ = τ from rfl]
      linarith only [hτ_eps, hεg]
    have := hnograz v hv1' hve t htbox hderiv
    rw [hEq] at this
    linarith only [this, hc2]

  · -- clause 5: the level function is regular along the arcs
    intro k t htIoo ht2h nn hnn1 hnnnear
    have ht_half : |t| ≤ η / 2 := le_trans ht2h h2h_half
    obtain ⟨hbM, hbL, hbQ⟩ := hMAspec k t htIoo ht_half
    by_cases hd0 : deriv (γ k) 0 - e = 0
    · -- the arc is vertical at the crossing
      have hder0 : deriv (γ k) 0 = e := sub_eq_zero.mp hd0
      have hquad : ‖deriv (γ k) t - deriv (γ k) 0‖ ≤ MA4 * t ^ 2 := hbQ (hbend k hder0)
      have hquad' : ‖deriv (γ k) t - e‖ ≤ MA4 * t ^ 2 := by rw [← hder0]; exact hquad
      have hbd : ‖deriv (γ k) t - e‖ ≤ τ / 4 := le_trans hquad' (hMA4sq t ht2h)
      have hκge : τ / 2 ≤ |inner ℝ e n| := by
        have h1 : τ ≤ Real.sqrt 2 * |inner ℝ e n| := hτ_up
        have h2 : Real.sqrt 2 ≤ 2 := by
          nlinarith only [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), Real.sqrt_nonneg 2]
        nlinarith only [h1, h2, abs_nonneg (inner ℝ e n)]
      have hκge_nn₀ : τ / 2 - ρ ≤ |inner ℝ e nn| := by
        have h1 : |inner ℝ e n| - |inner ℝ e nn| ≤ |inner ℝ e n - inner ℝ e nn| :=
          abs_sub_abs_le_abs_sub _ _
        have h2 : |inner ℝ e n - inner ℝ e nn| ≤ ‖nn - n‖ := by
          rw [← inner_sub_right]
          calc |inner ℝ e (n - nn)| ≤ ‖e‖ * ‖n - nn‖ := abs_real_inner_le_norm _ _
            _ = ‖nn - n‖ := by rw [he1, one_mul, norm_sub_rev]
        linarith only [h1, h2, hnnnear, hκge]
      have hκge_nn : τ / 2 - ρ ≤ |inner ℝ nn e| := by
        simpa [real_inner_comm] using hκge_nn₀
      have hsplit : inner ℝ nn (deriv (γ k) t)
          = inner ℝ nn e + inner ℝ nn (deriv (γ k) t - e) := by
        conv_lhs => rw [show deriv (γ k) t = e + (deriv (γ k) t - e) by abel]
        rw [inner_add_right]
      have hsmall : |inner ℝ nn (deriv (γ k) t - e)| ≤ τ / 4 := by
        calc |inner ℝ nn (deriv (γ k) t - e)| ≤ ‖nn‖ * ‖deriv (γ k) t - e‖ :=
              abs_real_inner_le_norm _ _
          _ = ‖deriv (γ k) t - e‖ := by rw [hnn1, one_mul]
          _ ≤ τ / 4 := hbd
      have hb : |inner ℝ nn e| - |inner ℝ nn (deriv (γ k) t - e)|
          ≤ |inner ℝ nn (deriv (γ k) t)| := by
        rw [hsplit]
        exact rb_le_abs_add _ _
      refine abs_pos.mp ?_
      linarith only [hb, hκge_nn, hsmall, hρ_le_tau, hτ_pos]
    · -- the arc is not vertical: the avoided direction gives the margin
      have hc00d : c00 ≤ |inner ℝ Ñ₀ (deriv (γ k) 0 - e)| := hc00arc k hd0
      have hed : inner ℝ e (deriv (γ k) 0 - e) = 0 := hdperp k
      have hMd : ‖deriv (γ k) 0 - e‖ ≤ MA1 + 1 := by
        have hb0 : ‖deriv (γ k) 0‖ ≤ MA1 :=
          (hMAspec k 0 ⟨by linarith, by linarith⟩ (by rw [abs_zero]; linarith)).1
        calc ‖deriv (γ k) 0 - e‖ ≤ ‖deriv (γ k) 0‖ + ‖e‖ := norm_sub_le _ _
          _ ≤ MA1 + 1 := by rw [he1]; linarith only [hb0]
      have hng_le : ‖ng‖ ≤ 3 / 2 := by linarith only [hng_high, hζ_le]
      have hng_ge : (1 : ℝ) / 2 ≤ ‖ng‖ := by linarith only [hng_low, hζ_le]
      have hn₀d : inner ℝ n₀ (deriv (γ k) 0 - e)
          = Real.sqrt (1 - ηb ^ 2) * inner ℝ Ñ₀ (deriv (γ k) 0 - e) := by
        rw [hn₀def, inner_add_left, real_inner_smul_left, real_inner_smul_left, hed, mul_zero,
          zero_add]
      have hsqrt : (1 / 2 : ℝ) ≤ Real.sqrt (1 - ηb ^ 2) := by
        rw [← Real.sqrt_sq (show (0 : ℝ) ≤ 1 / 2 by norm_num)]
        apply Real.sqrt_le_sqrt
        nlinarith only [hηb_le, hηb0]
      have hA : c00 / 2 ≤ |inner ℝ n₀ (deriv (γ k) 0 - e)| := by
        rw [hn₀d, abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
        calc c00 / 2 = (1 / 2) * c00 := by ring
          _ ≤ Real.sqrt (1 - ηb ^ 2) * |inner ℝ Ñ₀ (deriv (γ k) 0 - e)| :=
              mul_le_mul hsqrt hc00d (le_of_lt hc000) (Real.sqrt_nonneg _)
      have hB : |inner ℝ n₀ (deriv (γ k) 0 - e)| - ζ * (MA1 + 1)
          ≤ |inner ℝ ng (deriv (γ k) 0 - e)| := by
        have h3 : |inner ℝ ng (deriv (γ k) 0 - e) - inner ℝ n₀ (deriv (γ k) 0 - e)|
            ≤ ‖ng - n₀‖ * ‖deriv (γ k) 0 - e‖ := by
          rw [← inner_sub_left]
          exact abs_real_inner_le_norm _ _
        have h4 : ‖ng - n₀‖ * ‖deriv (γ k) 0 - e‖ ≤ ζ * (MA1 + 1) :=
          mul_le_mul (le_of_lt hngbd) hMd (norm_nonneg _) (le_of_lt hζ0)
        have hh := abs_sub_abs_le_abs_sub (inner ℝ n₀ (deriv (γ k) 0 - e))
          (inner ℝ ng (deriv (γ k) 0 - e))
        rw [abs_sub_comm (inner ℝ n₀ (deriv (γ k) 0 - e))
          (inner ℝ ng (deriv (γ k) 0 - e))] at hh
        linarith only [hh, h3, h4]
      have hC : c00 / 4 ≤ |inner ℝ ng (deriv (γ k) 0 - e)| := by
        linarith only [hA, hB, hζMA1]
      have hD4 : c00 / 6 ≤ |inner ℝ n (deriv (γ k) 0 - e)| := by
        have hunit : inner ℝ n (deriv (γ k) 0 - e)
            = (‖ng‖)⁻¹ * inner ℝ ng (deriv (γ k) 0 - e) := by rw [hndef, inner_unitDir]
        rw [hunit, abs_mul, abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _))]
        have h4 : (3 / 2 : ℝ)⁻¹ ≤ (‖ng‖)⁻¹ := by
          have hh := one_div_le_one_div_of_le (by linarith only [hng_ge]) hng_le
          simpa [one_div] using hh
        calc c00 / 6 = (3 / 2 : ℝ)⁻¹ * (c00 / 4) := by
              rw [show (3 / 2 : ℝ)⁻¹ = 2 / 3 by norm_num]; ring
          _ ≤ (‖ng‖)⁻¹ * |inner ℝ ng (deriv (γ k) 0 - e)| :=
              mul_le_mul h4 hC (by linarith only [hc000]) (inv_nonneg.mpr (norm_nonneg _))
      have hE : c00 / 12 ≤ |inner ℝ n (deriv (γ k) 0)| := by
        have h1 : |inner ℝ n e| ≤ 3 * ηb := by
          rw [real_inner_comm]
          rw [abs_of_nonneg (by linarith only [hκ_pos, hηb0])]
          exact hκ_le
        have h2 : |inner ℝ n (deriv (γ k) 0 - e)| - |inner ℝ n e|
            ≤ |inner ℝ n (deriv (γ k) 0)| := by
          have hh : inner ℝ n (deriv (γ k) 0)
              = inner ℝ n (deriv (γ k) 0 - e) + inner ℝ n e := by
            conv_lhs => rw [show deriv (γ k) 0 = (deriv (γ k) 0 - e) + e by abel]
            rw [inner_add_right]
          rw [hh]
          exact rb_le_abs_add _ _
        linarith only [h2, hD4, h1, h3ηb]
      have hdecomp : inner ℝ nn (deriv (γ k) t)
          = inner ℝ n (deriv (γ k) 0) + inner ℝ n (deriv (γ k) t - deriv (γ k) 0)
            + inner ℝ (nn - n) (deriv (γ k) t) := by
        rw [inner_sub_left, inner_sub_right]
        ring
      have hb1 : |inner ℝ n (deriv (γ k) t - deriv (γ k) 0)| ≤ MA2 * |t| := by
        calc |inner ℝ n (deriv (γ k) t - deriv (γ k) 0)|
              ≤ ‖n‖ * ‖deriv (γ k) t - deriv (γ k) 0‖ := abs_real_inner_le_norm _ _
          _ = ‖deriv (γ k) t - deriv (γ k) 0‖ := by rw [hn1, one_mul]
          _ ≤ MA2 * |t| := hbL
      have hb1' : MA2 * |t| ≤ c00 / 48 := by
        have h1 : MA2 * |t| ≤ MA2 * (2 * h) := mul_le_mul_of_nonneg_left ht2h (le_of_lt hMA20)
        have h2 : MA2 * (2 * h) = 12 * MA2 * s * τ := by rw [hhdef]; ring
        linarith only [h1, h2, h12MA2]
      have hb2 : |inner ℝ (nn - n) (deriv (γ k) t)| ≤ ρ * MA1 := by
        calc |inner ℝ (nn - n) (deriv (γ k) t)| ≤ ‖nn - n‖ * ‖deriv (γ k) t‖ :=
              abs_real_inner_le_norm _ _
          _ ≤ ρ * MA1 := mul_le_mul (le_of_lt hnnnear) hbM (norm_nonneg _) (le_of_lt hρpos)
      have hthree := rb_abs_add_three (inner ℝ n (deriv (γ k) 0))
        (inner ℝ n (deriv (γ k) t - deriv (γ k) 0)) (inner ℝ (nn - n) (deriv (γ k) t))
      rw [hdecomp]
      refine abs_pos.mp ?_
      linarith only [hthree, hE, hb1, hb1', hb2, hρMA1, hc000]
  · -- clause 6: the slab coordinate grows along the arcs
    intro k t htIoo ht2h
    have ht_half : |t| ≤ η / 2 := le_trans ht2h h2h_half
    obtain ⟨hbM, -, -⟩ := hMAspec k t htIoo ht_half
    have hinner_e : inner ℝ e (deriv (γ k) t) = 1 := by
      rw [hedef, inner_shiftVσ_one]
      exact hcoord_all k t htIoo
    have hbd : |inner ℝ (v - e) (deriv (γ k) t)| ≤ τ * MA1 := by
      calc |inner ℝ (v - e) (deriv (γ k) t)| ≤ ‖v - e‖ * ‖deriv (γ k) t‖ :=
            abs_real_inner_le_norm _ _
        _ ≤ τ * MA1 := by rw [hτdef]; exact mul_le_mul_of_nonneg_left hbM (norm_nonneg _)
    have hsplit : inner ℝ v (deriv (γ k) t)
        = inner ℝ e (deriv (γ k) t) + inner ℝ (v - e) (deriv (γ k) t) := by
      conv_lhs => rw [show v = e + (v - e) by abel]
      rw [inner_add_left]
    rw [hsplit]
    have h1 : -(τ * MA1) ≤ inner ℝ (v - e) (deriv (γ k) t) := (abs_le.mp hbd).1
    linarith only [hinner_e, h1, hτMA1]


end

end Work.Drive.Mono
