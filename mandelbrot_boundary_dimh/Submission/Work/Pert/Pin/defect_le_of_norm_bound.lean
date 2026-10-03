import Mathlib
import Submission.Work.Pert.Ksub2.defect_le_fix
import Submission.Work.Interfaces.Parabolic

namespace Work.Pert.Pin

/-!
# `Work.Pert.Pin.defect_le_of_norm_bound`

`Work.Pert.Ksub2.defect_le_fix` with the compactness of `Kd` replaced by an explicit norm bound
`hKdbd`, so that `Kd` may be the OPEN ball `Metric.ball (Xc d (-M)) (M/40)`.

The proof is that of `Submission/Work/Pert/Ksub2/defect_le_fix.lean` verbatim; the ONLY change is
that `obtain ⟨M₀, hM₀pos, hM₀⟩ := hKdc.isBounded.exists_pos_norm_le` is replaced by `M := max Mb 1`
together with `hMbound := fun z hz => le_trans (hKdbd z hz) (le_max_left _ _)`,
`hMpos := lt_of_lt_of_le zero_lt_one (le_max_right Mb 1)` and `hMge1 := le_max_right Mb 1`.
-/

open MandelDim Complex Set Metric Filter Topology
open scoped Topology

noncomputable section

set_option maxHeartbeats 2000000

/-- The `min` of a list of positive reals is positive. -/
private lemma foldr_min_pos {l : List ℝ} {z : ℝ} (hz : 0 < z) (hl : ∀ a ∈ l, 0 < a) :
    0 < l.foldr min z := by
  induction l with
  | nil => simpa using hz
  | cons b t ih =>
      simp only [List.foldr_cons]
      exact lt_min (hl b (by simp)) (ih (fun a ha => hl a (by simp [ha])))

/-- Every element of a list bounds the `foldr min` from above. -/
private lemma foldr_min_le {l : List ℝ} {z : ℝ} {a : ℝ} (ha : a ∈ l) : l.foldr min z ≤ a := by
  induction l with
  | nil => simp at ha
  | cons b t ih =>
      simp only [List.foldr_cons]
      rcases List.mem_cons.mp ha with rfl | hmem
      · exact min_le_left _ _
      · exact le_trans (min_le_right _ _) (ih hmem)

/-- `Work.Pert.Ksub2.defect_le_fix` with the compactness of `Kd` replaced by an explicit norm bound
`hKdbd`, so that `Kd` may be the OPEN ball `Metric.ball (Xc d (-M)) (M/40)`.  Copy that lemma's
proof (`Submission/Work/Pert/Ksub2/defect_le_fix.lean`); the ONLY change is that
`obtain ⟨M₀, hM₀pos, hM₀⟩ := hKdc.isBounded.exists_pos_norm_le` is replaced by
`M := max Mb 1` together with `hMbound := fun z hz => le_trans (hKdbd z hz) (le_max_left _ _)`,
`hMpos := lt_of_lt_of_le zero_lt_one (le_max_right Mb 1)`, `hMge1 := le_max_right Mb 1`.
Everything else is verbatim. -/
theorem defect_le_of_norm_bound {f₀ : ℂ → ℂ} {D₀ : Set ℂ} (hd : MandelDim.IsParabolicGerm f₀ D₀)
    {ξ : ℝ} (hξ : 0 < ξ) {Kd : Set ℂ} {Mb : ℝ} (hKdbd : ∀ z ∈ Kd, ‖z‖ ≤ Mb)
    (hKd : Kd ⊆ MandelDim.Qreg none (some (-(ξ : ℂ)))) (hfar : ∀ z ∈ Kd, 1 < ‖z‖)
    {hF : ℂ → ℂ} {ρ D : ℝ} (hρ : 0 < ρ) (hρ8 : ρ ≤ 1 / 8) (hD : 0 ≤ D)
    (hfe : ∀ z ∈ Metric.ball 0 ρ, f₀ z = z + z ^ 2 * hF z)
    (hFd : DifferentiableOn ℂ hF (Metric.ball 0 ρ))
    (hFl : ∀ z ∈ Metric.ball 0 ρ, ‖deriv hF z‖ ≤ D)
    (hFb : ∀ z ∈ Metric.ball 0 ρ, ‖hF z‖ ≤ 3 / 2)
    (hroom : Metric.closedBall 0 ρ ⊆ D₀)
    (hdepth : ∀ w ∈ Kd, ‖MandelDim.tau0 w‖ ≤ ρ / 8) :
    ∀ ε : ℝ, 0 < ε → ∃ L : Set ℂ, IsCompact L ∧ L ⊆ D₀ ∧ ∃ δ₀ η : ℝ, 0 < δ₀ ∧ 0 < η ∧
      ∀ (f : ℂ → ℂ) (Df : Set ℂ) (rr : ℝ) (u : ℂ → ℂ) (σ α : ℂ),
        MandelDim.NearOn f₀ f Df L δ₀ → f 0 = 0 → α ≠ 0 → ‖α‖ ≤ η → 0 < rr →
        DifferentiableOn ℂ u (Metric.ball 0 rr) →
        (∀ z ∈ Metric.ball 0 rr, 1 / 2 ≤ ‖u z‖ ∧ ‖u z‖ ≤ 2) →
        (∀ z ∈ Metric.ball 0 rr, f z = z + z * (z - σ) * u z) →
        (∀ w ∈ Kd, Work.Pert.tauC σ α w ∈ Metric.ball 0 rr) →
        ‖u 0 - 1‖ ≤ η →
        1 - σ * u 0 = Complex.exp (2 * Real.pi * Complex.I * α) →
        ∀ w ∈ Kd, ‖Work.Pert.liftF u σ α w - Work.Pert.F0f f₀ w‖ ≤ ε := by
  intro ε hε
  -- ## constants coming from the norm bound on `Kd`
  set M : ℝ := max Mb 1 with hMdef
  have hMpos : 0 < M := lt_of_lt_of_le zero_lt_one (le_max_right Mb 1)
  have hMge1 : 1 ≤ M := le_max_right Mb 1
  have hMbound : ∀ z ∈ Kd, ‖z‖ ≤ M := fun z hz => le_trans (hKdbd z hz) (le_max_left _ _)
  -- ## the four numerical constants of the statement
  set A : ℝ := 1 + 8 * M ^ 2 * (1 / 2 + 3 * Real.pi * ρ) with hAdef
  have hApos : 0 < A := by rw [hAdef]; positivity
  set Kc : ℝ := 1000 * (D + 1) * (1 + 8 * M ^ 2 * (1 / 2 + 3 * Real.pi * ρ) + 64 * M) with hKcdef
  have hKcpos : 0 < Kc := by
    rw [hKcdef]
    have h1 : 0 < D + 1 := by linarith
    positivity
  set η : ℝ := ([(1 : ℝ) / 1000, 1 / (1000 * A), 1 / (2 * Real.pi), ρ / (512 * M),
      1 / (128 * M ^ 2), 1 / (32 * Real.pi * M), 1 / (2 * M), 6 / (8 * Real.pi + 4),
      ε / Kc] : List ℝ).foldr min (ε / Kc) with hηdef
  have hηpos : 0 < η := by
    rw [hηdef]
    refine foldr_min_pos (by positivity) ?_
    intro a ha
    simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> positivity
  have hη₁ : η ≤ 1 / 1000 := by rw [hηdef]; exact foldr_min_le (by simp)
  have hη₂ : η ≤ 1 / (1000 * A) := by rw [hηdef]; exact foldr_min_le (by simp)
  have hη₃ : η ≤ 1 / (2 * Real.pi) := by rw [hηdef]; exact foldr_min_le (by simp)
  have hη₄ : η ≤ ρ / (512 * M) := by rw [hηdef]; exact foldr_min_le (by simp)
  have hη₅ : η ≤ 1 / (128 * M ^ 2) := by rw [hηdef]; exact foldr_min_le (by simp)
  have hη₆ : η ≤ 1 / (32 * Real.pi * M) := by rw [hηdef]; exact foldr_min_le (by simp)
  have hη₇ : η ≤ 1 / (2 * M) := by rw [hηdef]; exact foldr_min_le (by simp)
  have hη₈ : η ≤ 6 / (8 * Real.pi + 4) := by rw [hηdef]; exact foldr_min_le (by simp)
  have hη₉ : η ≤ ε / Kc := by rw [hηdef]; exact foldr_min_le (by simp)
  -- ## the numerical consequences of the choice of `η`
  have hη2M : η * M ≤ 1 / 2 := by
    have h := mul_le_mul_of_nonneg_right hη₇ hMpos.le
    have h' : (1 / (2 * M)) * M = 1 / 2 := by field_simp; try ring
    linarith [h, h'.le, h'.ge]
  have hη512 : 64 * M * η ≤ ρ / 8 := by
    have h := mul_le_mul_of_nonneg_left hη₄ (by positivity : (0 : ℝ) ≤ 64 * M)
    have h' : 64 * M * (ρ / (512 * M)) = ρ / 8 := by field_simp; try ring
    linarith [h, h'.le, h'.ge]
  have hη128 : 64 * M * η ≤ 1 / (2 * M) := by
    have h := mul_le_mul_of_nonneg_left hη₅ (by positivity : (0 : ℝ) ≤ 64 * M)
    have h' : 64 * M * (1 / (128 * M ^ 2)) = 1 / (2 * M) := by field_simp; try ring
    linarith [h, h'.le, h'.ge]
  have hη32π : 8 * Real.pi * η ≤ 1 / (4 * M) := by
    have h := mul_le_mul_of_nonneg_left hη₆ (by positivity : (0 : ℝ) ≤ 8 * Real.pi)
    have h' : 8 * Real.pi * (1 / (32 * Real.pi * M)) = 1 / (4 * M) := by field_simp; try ring
    linarith [h, h'.le, h'.ge]
  have hη32 : η * M ≤ 1 / (32 * Real.pi) := by
    have h := mul_le_mul_of_nonneg_right hη₆ hMpos.le
    have h' : (1 / (32 * Real.pi * M)) * M = 1 / (32 * Real.pi) := by field_simp; try ring
    linarith [h, h'.le, h'.ge]
  have hηA : η * A ≤ 1 / 1000 := by
    have h := mul_le_mul_of_nonneg_right hη₂ (le_of_lt hApos)
    have h' : (1 / (1000 * A)) * A = 1 / 1000 := by field_simp; try ring
    linarith [h, h'.le, h'.ge]
  have hη1000 : 8 * M ^ 2 * (η / 2 + 3 * Real.pi * ρ * η) ≤ 1 / 1000 := by
    have h1 : 8 * M ^ 2 * (η / 2 + 3 * Real.pi * ρ * η) = η * (8 * M ^ 2 * (1 / 2 + 3 * Real.pi * ρ)) := by ring
    have h2 : η * (8 * M ^ 2 * (1 / 2 + 3 * Real.pi * ρ)) ≤ η * A := by
      exact mul_le_mul_of_nonneg_left (by rw [hAdef]; linarith) (le_of_lt hηpos)
    linarith [h1, h2, hηA]
  -- ## the frame of the statement
  refine ⟨Metric.closedBall 0 ρ, isCompact_closedBall 0 ρ, hroom, η / 2, η, by linarith, hηpos, ?_⟩
  intro f Df rr u σ α hnear hf0 hα hαη hrr hud hbox huf hτball hu0 hnorm w hwK
  -- ## where `w` sits, and the two working points `τ₀ = -1/w`, `τ = τ_f w`
  have hwgt : 1 < ‖w‖ := hfar w hwK
  have hwle : ‖w‖ ≤ M := hMbound w hwK
  have hwne : w ≠ 0 := by
    intro h; rw [h] at hwgt; simp at hwgt; linarith
  have hM1 : 1 ≤ M := le_trans hwgt.le hwle
  have hτ0norm : ‖MandelDim.tau0 w‖ = 1 / ‖w‖ := by simp [MandelDim.tau0]
  have hτ0le : ‖MandelDim.tau0 w‖ ≤ ρ / 8 := hdepth w hwK
  have hτ0mem : MandelDim.tau0 w ∈ Metric.ball 0 ρ := by
    rw [Metric.mem_ball, dist_eq_norm, sub_zero]
    have h : 1 / ‖w‖ ≤ ρ / 8 := by rw [← hτ0norm]; exact hτ0le
    linarith [hρ]
  -- ## `σ` and `α` are small
  have hηhalf : η ≤ 1 / 2 := by linarith [hη₁]
  have hu0half : ‖u 0 - 1‖ ≤ 1 / 2 := le_trans hu0 hηhalf
  have hαπ : ‖α‖ ≤ 1 / (2 * Real.pi) := le_trans hαη hη₃
  have hπpos : 0 < Real.pi := Real.pi_pos
  have hσb : ‖σ / α + 2 * Real.pi * Complex.I‖ ≤ (8 * Real.pi ^ 2 + 4 * Real.pi) * η :=
    le_trans (sigma_alpha_close hα hαπ hu0half hnorm).1
      (by
        have h1 : 8 * Real.pi ^ 2 * ‖α‖ ≤ 8 * Real.pi ^ 2 * η :=
          mul_le_mul_of_nonneg_left hαη (by positivity)
        have h2 : 4 * Real.pi * ‖u 0 - 1‖ ≤ 4 * Real.pi * η :=
          mul_le_mul_of_nonneg_left hu0 (by positivity)
        linarith [h1, h2])
  have hσ8 : ‖σ‖ ≤ 8 * Real.pi * η := by
    refine le_trans (sigma_alpha_close hα hαπ hu0half hnorm).2 ?_
    have hb : 8 * Real.pi ^ 2 * ‖α‖ + 4 * Real.pi * ‖u 0 - 1‖ + 2 * Real.pi ≤ 8 * Real.pi := by
      have h1 : 8 * Real.pi ^ 2 * ‖α‖ ≤ 8 * Real.pi ^ 2 * η :=
        mul_le_mul_of_nonneg_left hαη (by positivity)
      have h2 : 4 * Real.pi * ‖u 0 - 1‖ ≤ 4 * Real.pi * η :=
        mul_le_mul_of_nonneg_left hu0 (by positivity)
      have h3 : (8 * Real.pi + 4) * η ≤ 6 := by
        have h := mul_le_mul_of_nonneg_left hη₈ (by positivity : (0 : ℝ) ≤ 8 * Real.pi + 4)
        have h' : (8 * Real.pi + 4) * (6 / (8 * Real.pi + 4)) = 6 := by field_simp; try ring
        linarith [h, h'.le, h'.ge]
      have h4 : 8 * Real.pi ^ 2 * η + 4 * Real.pi * η ≤ 6 * Real.pi := by nlinarith [h3, Real.pi_pos]
      linarith [h1, h2, h4]
    calc ‖α‖ * (8 * Real.pi ^ 2 * ‖α‖ + 4 * Real.pi * ‖u 0 - 1‖ + 2 * Real.pi)
        ≤ η * (8 * Real.pi) := mul_le_mul hαη hb (by positivity) (le_of_lt hηpos)
      _ = 8 * Real.pi * η := by ring
  -- ## `τ_f w` is close to `τ₀ w` and lies where we need it
  set δ₂ : ℝ := ‖σ / α + 2 * Real.pi * Complex.I‖ * M / Real.pi + 4 * Real.pi * ‖α‖ with hδ₂def
  have hδ₂nn : 0 ≤ δ₂ := by rw [hδ₂def]; positivity
  have hδ₂le : ‖Work.Pert.tauC σ α w - MandelDim.tau0 w‖ ≤ δ₂ := by
    have hm0 : 0 < (1 : ℝ) / M := by positivity
    have hmw : (1 : ℝ) / M ≤ ‖w‖ := by
      rw [div_le_iff₀ hMpos]; nlinarith [hM1, hwgt]
    have hsmall : 2 * Real.pi * ‖α‖ * ‖w‖ ≤ 1 / 2 := by
      have h1 : ‖α‖ * ‖w‖ ≤ η * M := mul_le_mul hαη hwle (norm_nonneg _) (le_of_lt hηpos)
      have h2 : η * M ≤ 1 / (32 * Real.pi) := hη32
      have h6 : ‖α‖ * ‖w‖ ≤ 1 / (32 * Real.pi) := le_trans h1 h2
      have h3 : 2 * Real.pi * (‖α‖ * ‖w‖) ≤ 2 * Real.pi * (1 / (32 * Real.pi)) :=
        mul_le_mul_of_nonneg_left h6 (by positivity)
      have h4 : 2 * Real.pi * (1 / (32 * Real.pi)) = 1 / 16 := by field_simp; try ring
      nlinarith [h3, h4.le, h4.ge]
    have h := tauC_add_inv_le σ α w hα hwne hm0 hmw hsmall
    have hEq : Work.Pert.tauC σ α w + 1 / w = Work.Pert.tauC σ α w - MandelDim.tau0 w := by
      rw [MandelDim.tau0]; ring
    rw [← hEq]
    have h2 : ‖σ / α + 2 * Real.pi * Complex.I‖ / (Real.pi * (1 / M))
        + (2 * Real.pi) ^ 2 * ‖α‖ / Real.pi = δ₂ := by
      rw [hδ₂def]; field_simp; ring
    linarith [h, h2.le, h2.ge]
  have hδ₂b : δ₂ ≤ 64 * M * η := by
    have h1 : ‖σ / α + 2 * Real.pi * Complex.I‖ * M / Real.pi ≤ (8 * Real.pi + 4) * M * η := by
      rw [div_le_iff₀ hπpos]
      have h := mul_le_mul_of_nonneg_right hσb (le_of_lt hMpos)
      nlinarith [h, Real.pi_pos]
    have h2 : 4 * Real.pi * ‖α‖ ≤ 4 * Real.pi * η := mul_le_mul_of_nonneg_left hαη (by positivity)
    have h3 : (8 * Real.pi + 4) * M * η + 4 * Real.pi * η ≤ 64 * M * η := by
      have hp4 : Real.pi ≤ 4 := Real.pi_le_four
      nlinarith [hMge1, hηpos.le, hp4]
    rw [hδ₂def]; linarith
  have hδ₂ρ : δ₂ ≤ ρ / 8 := le_trans hδ₂b hη512
  have hδ₂M : δ₂ ≤ 1 / (2 * M) := le_trans hδ₂b hη128
  have hτge : 1 / (2 * M) ≤ ‖Work.Pert.tauC σ α w‖ := by
    have h1 : ‖MandelDim.tau0 w‖ - ‖Work.Pert.tauC σ α w - MandelDim.tau0 w‖
        ≤ ‖Work.Pert.tauC σ α w‖ := by
      have h := abs_norm_sub_norm_le (Work.Pert.tauC σ α w) (MandelDim.tau0 w)
      rw [abs_le] at h; linarith [h.1, h.2]
    have h2 : 1 / M ≤ ‖MandelDim.tau0 w‖ := by
      rw [hτ0norm]
      exact one_div_le_one_div_of_le (by linarith [hwgt]) hwle
    have hmid : 1 / M - 1 / (2 * M) = 1 / (2 * M) := by field_simp; try ring
    have h3 : 1 / (2 * M) ≤ 1 / M - δ₂ := by linarith [hδ₂M, hmid.le, hmid.ge]
    linarith [h1, h2, h3, hδ₂le]
  have hτσge : 1 / (4 * M) ≤ ‖Work.Pert.tauC σ α w - σ‖ := by
    have h1 : ‖Work.Pert.tauC σ α w‖ - ‖σ‖ ≤ ‖Work.Pert.tauC σ α w - σ‖ := by
      have h := abs_norm_sub_norm_le (Work.Pert.tauC σ α w) σ
      rw [abs_le] at h; linarith [h.2]
    have h2 : 1 / (4 * M) ≤ ‖Work.Pert.tauC σ α w‖ - ‖σ‖ := by
      have h3 : ‖σ‖ ≤ 1 / (4 * M) := le_trans hσ8 hη32π
      have h4 : 1 / (2 * M) - 1 / (4 * M) = 1 / (4 * M) := by field_simp; try ring
      linarith [hτge, h3, h4.le, h4.ge]
    linarith [h1, h2]
  have hτle : ‖Work.Pert.tauC σ α w‖ ≤ ρ / 4 := by
    have h1 : ‖Work.Pert.tauC σ α w‖
        ≤ ‖Work.Pert.tauC σ α w - MandelDim.tau0 w‖ + ‖MandelDim.tau0 w‖ := by
      have h := norm_add_le (Work.Pert.tauC σ α w - MandelDim.tau0 w) (MandelDim.tau0 w)
      simpa using h
    linarith [h1, hδ₂le, hδ₂ρ, hτ0le]
  have hτmem : Work.Pert.tauC σ α w ∈ Metric.ball 0 ρ := by
    rw [Metric.mem_ball, dist_eq_norm, sub_zero]; linarith [hτle, hρ]
  have hτL : Work.Pert.tauC σ α w ∈ Metric.closedBall 0 ρ := by
    rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]; linarith [hτle, hρ]
  -- ## `u` versus `hF` at the working point `τ`
  set ηc : ℝ := max η (8 * M ^ 2 * (η / 2 + 3 * Real.pi * ρ * η)) with hηcdef
  have hηcpos : 0 < ηc := by rw [hηcdef]; exact lt_of_lt_of_le hηpos (le_max_left _ _)
  have hηcη : η ≤ ηc := by rw [hηcdef]; exact le_max_left _ _
  have hηc1000 : ηc ≤ 1 / 1000 := by
    rw [hηcdef]
    refine max_le hη₁ ?_
    exact hη1000
  have hτballmem : Work.Pert.tauC σ α w ∈ Metric.ball 0 rr := hτball w hwK
  have hform := huf (Work.Pert.tauC σ α w) hτballmem
  have hfeτ : f₀ (Work.Pert.tauC σ α w)
      = Work.Pert.tauC σ α w + Work.Pert.tauC σ α w ^ 2 * hF (Work.Pert.tauC σ α w) :=
    hfe _ hτmem
  have hτne : Work.Pert.tauC σ α w ≠ 0 := by
    intro h
    have h0 : ‖Work.Pert.tauC σ α w‖ = 0 := by rw [h, norm_zero]
    have hpos : (0 : ℝ) < 1 / (2 * M) := by positivity
    linarith [hτge, hpos]
  have hτσne : Work.Pert.tauC σ α w - σ ≠ 0 := by
    intro h
    have h0 : ‖Work.Pert.tauC σ α w - σ‖ = 0 := by rw [h, norm_zero]
    have hpos : (0 : ℝ) < 1 / (4 * M) := by positivity
    linarith [hτσge, hpos]
  have hu_eq : u (Work.Pert.tauC σ α w)
      = (f (Work.Pert.tauC σ α w) - Work.Pert.tauC σ α w)
        / (Work.Pert.tauC σ α w * (Work.Pert.tauC σ α w - σ)) := by
    rw [hform]; field_simp; ring
  have hdiff : u (Work.Pert.tauC σ α w) - hF (Work.Pert.tauC σ α w)
      = ((f (Work.Pert.tauC σ α w) - f₀ (Work.Pert.tauC σ α w))
          + Work.Pert.tauC σ α w * σ * hF (Work.Pert.tauC σ α w))
        / (Work.Pert.tauC σ α w * (Work.Pert.tauC σ α w - σ)) := by
    rw [hu_eq, hfeτ]; field_simp; ring
  have hclose : ‖f (Work.Pert.tauC σ α w) - f₀ (Work.Pert.tauC σ α w)‖ < η / 2 :=
    hnear.2.2.2 _ hτL
  have hnum : ‖(f (Work.Pert.tauC σ α w) - f₀ (Work.Pert.tauC σ α w))
      + Work.Pert.tauC σ α w * σ * hF (Work.Pert.tauC σ α w)‖ ≤ η / 2 + 3 * Real.pi * ρ * η := by
    have h1 : ‖f (Work.Pert.tauC σ α w) - f₀ (Work.Pert.tauC σ α w)‖ ≤ η / 2 := le_of_lt hclose
    have h2 : ‖Work.Pert.tauC σ α w * σ * hF (Work.Pert.tauC σ α w)‖
        ≤ (ρ / 4) * (8 * Real.pi * η) * (3 / 2) := by
      rw [norm_mul, norm_mul]
      exact mul_le_mul (mul_le_mul hτle hσ8 (norm_nonneg _) (by positivity)) (hFb _ hτmem)
        (by positivity) (by positivity)
    have h3 : (ρ / 4) * (8 * Real.pi * η) * (3 / 2) ≤ 3 * Real.pi * ρ * η := by
      nlinarith [hρ, hηpos, Real.pi_pos]
    have h4 := norm_add_le (f (Work.Pert.tauC σ α w) - f₀ (Work.Pert.tauC σ α w))
      (Work.Pert.tauC σ α w * σ * hF (Work.Pert.tauC σ α w))
    linarith [h4, h1, h2, h3]
  have hden : (1 / (2 * M)) * (1 / (4 * M)) ≤ ‖Work.Pert.tauC σ α w * (Work.Pert.tauC σ α w - σ)‖ := by
    rw [norm_mul]
    exact mul_le_mul hτge hτσge (by positivity) (norm_nonneg _)
  have hut : ‖u (Work.Pert.tauC σ α w) - hF (Work.Pert.tauC σ α w)‖ ≤ ηc := by
    rw [hdiff, norm_div]
    have hdenpos : 0 < (1 / (2 * M)) * (1 / (4 * M)) := by positivity
    have hstep : (η / 2 + 3 * Real.pi * ρ * η) / ((1 / (2 * M)) * (1 / (4 * M)))
        = 8 * M ^ 2 * (η / 2 + 3 * Real.pi * ρ * η) := by field_simp; try ring
    calc ‖(f (Work.Pert.tauC σ α w) - f₀ (Work.Pert.tauC σ α w))
            + Work.Pert.tauC σ α w * σ * hF (Work.Pert.tauC σ α w)‖
          / ‖Work.Pert.tauC σ α w * (Work.Pert.tauC σ α w - σ)‖
        ≤ (η / 2 + 3 * Real.pi * ρ * η) / ((1 / (2 * M)) * (1 / (4 * M))) :=
          div_le_div₀ (by positivity : (0 : ℝ) ≤ η / 2 + 3 * Real.pi * ρ * η) hnum hdenpos hden
      _ = 8 * M ^ 2 * (η / 2 + 3 * Real.pi * ρ * η) := hstep
      _ ≤ ηc := by rw [hηcdef]; exact le_max_right _ _
  -- ## the pointwise model comparison
  have hηcπ : ‖α‖ ≤ 1 / (2 * Real.pi) := hαπ
  have hδsum : ρ / 8 + δ₂ ≤ ρ / 4 := by linarith [hδ₂ρ, hρ]
  have hwu : ‖α‖ * ‖w‖ ≤ 1 / 2 := by
    refine le_trans (mul_le_mul hαη hwle (norm_nonneg _) (le_of_lt hηpos)) ?_
    exact hη2M
  have hcore := Work.Pert.Ksub2.liftF_sub_model_le_pointwise (u := u) (hF := hF) (σ := σ)
    (α := α) (w := w)
    (ρ := ρ) (D := D) (η := ηc) (δ₁ := ρ / 8) (δ₂ := δ₂)
    hρ (by linarith [hρ8]) hD hηcpos hηc1000 hτ0le (by linarith [hρ8]) hδ₂le hδ₂nn hδsum
    hFd hFl hFb hut (le_trans hu0 hηcη) hα (le_trans hαη hηcη) hηcπ hnorm hwne hwu
  have hmodel : Work.Pert.F0f f₀ w
      = w + hF (MandelDim.tau0 w) / (1 + MandelDim.tau0 w * hF (MandelDim.tau0 w)) := by
    refine Work.Pert.Ksub2.F0f_eq_model hwne (hfe _ hτ0mem) ?_
    intro h
    have h1 : ‖MandelDim.tau0 w * hF (MandelDim.tau0 w)‖ = 1 := by
      have h2 : MandelDim.tau0 w * hF (MandelDim.tau0 w) = -1 := by linear_combination h
      rw [h2, norm_neg, norm_one]
    have h3 : ‖MandelDim.tau0 w * hF (MandelDim.tau0 w)‖ ≤ (ρ / 8) * (3 / 2) := by
      rw [norm_mul]
      exact mul_le_mul hτ0le (hFb _ hτ0mem) (norm_nonneg _) (by positivity)
    have h4 : (ρ / 8) * (3 / 2) < 1 := by nlinarith [hρ8]
    linarith [h1, h3, h4]
  -- ## conclusion
  calc ‖Work.Pert.liftF u σ α w - Work.Pert.F0f f₀ w‖
      = ‖Work.Pert.liftF u σ α w
          - (w + hF (MandelDim.tau0 w) / (1 + MandelDim.tau0 w * hF (MandelDim.tau0 w)))‖ := by
        rw [hmodel]
    _ ≤ 1000 * (D + 1) * (ηc + δ₂) := hcore
    _ ≤ ε := by
        have h1 : ηc + δ₂ ≤ η * (1 + 8 * M ^ 2 * (1 / 2 + 3 * Real.pi * ρ) + 64 * M) := by
          have ha : ηc ≤ η + η * (8 * M ^ 2 * (1 / 2 + 3 * Real.pi * ρ)) := by
            rw [hηcdef]
            have hnn : (0 : ℝ) ≤ η * (8 * M ^ 2 * (1 / 2 + 3 * Real.pi * ρ)) := by positivity
            refine max_le (by linarith) ?_
            have hb : 8 * M ^ 2 * (η / 2 + 3 * Real.pi * ρ * η)
                = η * (8 * M ^ 2 * (1 / 2 + 3 * Real.pi * ρ)) := by ring
            linarith [hb.le, hb.ge]
          linarith [ha, hδ₂b]
        have h2 : 1000 * (D + 1) * (η * (1 + 8 * M ^ 2 * (1 / 2 + 3 * Real.pi * ρ) + 64 * M))
            = Kc * η := by rw [hKcdef]; ring
        have h3 : Kc * η ≤ ε := by
          have h4 : η * Kc ≤ ε := by
            rw [le_div_iff₀ hKcpos] at hη₉
            exact hη₉
          linarith [h4]
        calc 1000 * (D + 1) * (ηc + δ₂)
            ≤ 1000 * (D + 1) * (η * (1 + 8 * M ^ 2 * (1 / 2 + 3 * Real.pi * ρ) + 64 * M)) := by
              refine mul_le_mul_of_nonneg_left h1 ?_
              have : 0 < D + 1 := by linarith
              positivity
          _ = Kc * η := h2
          _ ≤ ε := h3

end

end Work.Pert.Pin
