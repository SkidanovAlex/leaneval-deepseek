import Mathlib
import Submission.Work.Pert.Setup
import Submission.Work.Pert.Basic
import Submission.Work.Pert.liftF_defect_le_tauC
import Submission.Work.Pert.scale_lattice
import Submission.Work.Interfaces.Parabolic
import Submission.Work.Interfaces.Fatou
import Submission.Work.Interfaces.FatouNarrow
import Submission.Work.Pert.norm_sigma_lt_rr
import Submission.Work.Pert.exists_lipschitz_near_of_diffOn
import Submission.Work.Pert.sfun_lower_exp_bound
import Submission.Work.Pert.liftF_lower_ends

namespace Work.Pert

open MandelDim Complex Metric

set_option linter.unusedVariables false

theorem Phi_dev_le_on_gate_lower {f₀ : ℂ → ℂ} {D₀ : Set ℂ} (d : MandelDim.ParabData f₀ D₀)
    (hF : MandelDim.FatouStatement)
    {Ξ rr M : ℝ} {α σ : ℂ} {u Φm : ℂ → ℂ} {z₀ : ℂ}
    (hΞ : 0 < Ξ) (hrr : 0 < rr) (hM : 0 ≤ M)
    (hInF1 : MandelDim.InF1 α) (hα64 : ‖α‖ ≤ 1 / 64)
    (hQAdm : MandelDim.QAdm (some ((Ξ : ℂ) - 1 / α)) (some (-(Ξ : ℂ))))
    (hσ : σ ≠ 0) (hnorm : 1 - σ * u 0 = Complex.exp (2 * Real.pi * Complex.I * α))
    (hu : DifferentiableOn ℂ u (Metric.ball (0 : ℂ) rr))
    (hu2 : ∀ z ∈ Metric.ball (0 : ℂ) rr, 1 / 2 ≤ ‖u z‖ ∧ ‖u z‖ ≤ 2)
    (hτQ : ∀ z ∈ Work.Pert.Qm Ξ α, Work.Pert.tauC σ α z ∈ Metric.ball (0 : ℂ) rr)
    (hNT : MandelDim.NearTranslationL1 (Work.Pert.liftF u σ α) (Work.Pert.Qm Ξ α))
    (hΦm : MandelDim.IsFatouCoordOn (Work.Pert.liftF u σ α) Φm (Work.Pert.Qm Ξ α))
    (hz₀ : z₀ ∈ Work.Pert.Qm Ξ α) (hz₀re : -(M + 1) ≤ z₀.re) (hz₀re' : z₀.re ≤ -M + 1)
    (hz₀im : |z₀.im| ≤ 1)
    (hpin : Φm z₀ = (((-M : ℝ)) : ℂ)) :
    ∃ Y₀ K : ℝ, 0 < Y₀ ∧ 0 < K ∧ ∀ z : ℂ, z ∈ Work.Pert.Qm Ξ α → -(Ξ + 1) ≤ z.re →
      z.re ≤ 2 → z.im ≤ -Y₀ →
      (Φm z - z).re ≤ 2 + K * (1 + Real.log (2 + M) + Ξ + Real.log (2 + |z.im|))
        + |z.im| / 8 + |z.re| / 8 := by
  -- the value form of the near-translation bound on the gate
  have hval : ∀ z ∈ Work.Pert.Qm Ξ α, ‖Work.Pert.liftF u σ α z - (z + 1)‖ ≤ 1 / 32 :=
    fun z hz => (hNT.1.2 z hz).1
  -- `σ` lies strictly inside the disc of holomorphy of `u`
  have hσr : ‖σ‖ < rr :=
    norm_sigma_lt_rr hΞ hrr hInF1 hα64 hQAdm hσ hnorm hu2 hτQ
  -- `u` is Lipschitz at `σ`
  have hub : ∀ z ∈ Metric.ball (0 : ℂ) rr, ‖u z‖ ≤ 2 := fun z hz => (hu2 z hz).2
  obtain ⟨C, δ, hC, hδ, huL⟩ := exists_lipschitz_near_of_diffOn hrr hu hub hσr
  -- the lower-end limit of `1 - sfun`, exponentially
  obtain ⟨M₁, κ₁, Y₁, hM₁, hκ₁, hsfun⟩ :=
    sfun_lower_exp_bound (Ξ := Ξ) (rr := rr) (C := C) (δ := δ)
      hΞ hInF1 hα64 hσ hnorm hrr hσr hu2 hC hδ huL hτQ hval
  -- the translation `ρ` at the lower end and the exponential closeness of `F` to it
  obtain ⟨ρ, hρ, M₂, κ₂, Y₂, hM₂, hκ₂, hclose⟩ :=
    liftF_lower_ends (Ξ := Ξ) (rr := rr) (M := M₁) (κ := κ₁) (Y := Y₁)
      hΞ hInF1 hα64 hQAdm hσ hnorm hrr hσr hu2 hM₁ hκ₁ hsfun hval
  -- Shishikura's lemma on the ends, lower branch: `Φm z = z / ρ + c + o(1)`
  obtain ⟨c, hc⟩ :=
    (hF.2.2.2.2.2 (some ((Ξ : ℂ) - 1 / α)) (some (-(Ξ : ℂ))) (Work.Pert.liftF u σ α) Φm
        ρ M₂ κ₂ Y₂ hQAdm hNT.1 hΦm hκ₂ hρ).2 hclose
  -- ## covering the region by finitely many width-`2` vertical strips
  set N : ℕ := ⌊(Ξ + 3) / 2⌋₊ + 1 with hNdef
  have hNpos : 0 < N := Nat.succ_pos _
  have hYexists : ∀ j : ℕ, ∃ Y' : ℝ, ∀ z : ℂ, z ∈ Work.Pert.Qm Ξ α → z.im < -Y' →
      |z.re - (-(Ξ + 1) + 2 * (j : ℝ))| ≤ 2 → ‖Φm z - z / ρ - c‖ < 1 := by
    intro j
    obtain ⟨Y', hY'⟩ := hc (-(Ξ + 1) + 2 * (j : ℝ)) 1 (by norm_num)
    exact ⟨Y', fun z hzQ hzim hstrip => hY' z hzQ hzim hstrip⟩
  choose Yf hYf using hYexists
  have hne : (Finset.range N).Nonempty := Finset.nonempty_range_iff.mpr (Nat.ne_of_gt hNpos)
  set Y₀ : ℝ := max ((Finset.range N).sup' hne Yf + 1) 1 with hY₀def
  have hY₀pos : 0 < Y₀ := lt_of_lt_of_le one_pos (le_max_right _ _)
  refine ⟨Y₀, max 1 (‖c‖ + 3), hY₀pos, lt_max_iff.mpr (Or.inl one_pos), ?_⟩
  intro z hzQ hzre₁ hzre₂ hzim
  -- the strip index and its properties
  set j : ℕ := ⌊(z.re + (Ξ + 1)) / 2⌋₊ with hjdef
  have hjle : (j : ℝ) ≤ (z.re + (Ξ + 1)) / 2 := Nat.floor_le (by linarith)
  have hjlt : (z.re + (Ξ + 1)) / 2 < (j : ℝ) + 1 := Nat.lt_floor_add_one _
  have hjN : j < N := by
    rw [hNdef]
    exact Nat.lt_succ_of_le (Nat.floor_mono (by linarith))
  have hstrip : |z.re - (-(Ξ + 1) + 2 * (j : ℝ))| ≤ 2 := by
    have h1 : -(Ξ + 1) + 2 * (j : ℝ) ≤ z.re := by linarith
    have h2 : z.re - (-(Ξ + 1) + 2 * (j : ℝ)) < 2 := by linarith
    rw [abs_of_nonneg (by linarith)]
    linarith
  have hdeep : z.im < -Yf j := by
    have hsup : Yf j ≤ (Finset.range N).sup' hne Yf :=
      Finset.le_sup' Yf (Finset.mem_range.mpr hjN)
    have hle : (Finset.range N).sup' hne Yf + 1 ≤ Y₀ := le_max_left _ _
    linarith
  have hmain : ‖Φm z - z / ρ - c‖ < 1 := hYf j z hzQ hdeep hstrip
  -- ## the final arithmetic
  have hρnorm : (31 : ℝ) / 32 ≤ ‖ρ‖ := by
    have h1 : (1 : ℝ) ≤ ‖ρ‖ + ‖ρ - 1‖ := by
      have he : (1 : ℂ) = ρ - (ρ - 1) := by ring
      calc (1 : ℝ) = ‖ρ - (ρ - 1)‖ := by rw [← he]; simp
        _ ≤ ‖ρ‖ + ‖ρ - 1‖ := norm_sub_le _ _
    linarith
  have hρne : ρ ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hρnorm
    norm_num at hρnorm
  have hinv : ‖1 / ρ - 1‖ ≤ 1 / 8 := by
    have he : 1 / ρ - 1 = (1 - ρ) / ρ := by field_simp
    rw [he, norm_div]
    have h1 : ‖1 - ρ‖ ≤ 1 / 32 := by rw [norm_sub_rev]; exact hρ
    calc ‖1 - ρ‖ / ‖ρ‖ ≤ (1 / 32) / (31 / 32) :=
          div_le_div₀ (by norm_num) h1 (by norm_num) hρnorm
      _ = 1 / 31 := by norm_num
      _ ≤ 1 / 8 := by norm_num
  have hzdeb : (z / ρ - z).re ≤ ‖1 / ρ - 1‖ * ‖z‖ := by
    have he : z / ρ - z = (1 / ρ - 1) * z := by ring
    rw [he]
    calc ((1 / ρ - 1) * z).re ≤ |((1 / ρ - 1) * z).re| := le_abs_self _
      _ ≤ ‖(1 / ρ - 1) * z‖ := Complex.abs_re_le_norm _
      _ = ‖1 / ρ - 1‖ * ‖z‖ := norm_mul _ _
  have hdecomp : (Φm z - z).re = (z / ρ - z).re + c.re + (Φm z - z / ρ - c).re := by
    have he : Φm z - z = (z / ρ - z) + c + (Φm z - z / ρ - c) := by ring
    rw [he, Complex.add_re, Complex.add_re]
  have hcle : c.re ≤ ‖c‖ := le_trans (le_abs_self c.re) (Complex.abs_re_le_norm c)
  have hres : (Φm z - z / ρ - c).re ≤ 1 :=
    le_trans (le_trans (le_abs_self _) (Complex.abs_re_le_norm _)) (le_of_lt hmain)
  have hbracket : (1 : ℝ) ≤ 1 + Real.log (2 + M) + Ξ + Real.log (2 + |z.im|) := by
    have h1 : 0 ≤ Real.log (2 + M) := Real.log_nonneg (by linarith)
    have h2 : 0 ≤ Real.log (2 + |z.im|) := Real.log_nonneg (by linarith [abs_nonneg z.im])
    linarith
  have hKnonneg : (0 : ℝ) ≤ max 1 (‖c‖ + 3) := le_trans zero_le_one (le_max_left _ _)
  have hKbound : ‖c‖ + 1 ≤ 2 + max 1 (‖c‖ + 3) *
      (1 + Real.log (2 + M) + Ξ + Real.log (2 + |z.im|)) := by
    have hKge : ‖c‖ + 1 ≤ max 1 (‖c‖ + 3) := by
      have h3 : ‖c‖ + 1 ≤ ‖c‖ + 3 := by linarith
      exact le_trans h3 (le_max_right _ _)
    have hmono : max 1 (‖c‖ + 3) * 1 ≤ max 1 (‖c‖ + 3) *
        (1 + Real.log (2 + M) + Ξ + Real.log (2 + |z.im|)) :=
      mul_le_mul_of_nonneg_left hbracket hKnonneg
    have h41 : max 1 (‖c‖ + 3) * 1 = max 1 (‖c‖ + 3) := mul_one _
    linarith [hKge, hmono, h41.le, h41.ge]
  have hznorm : ‖z‖ ≤ |z.re| + |z.im| := Complex.norm_le_abs_re_add_abs_im z
  have hstep : ‖1 / ρ - 1‖ * ‖z‖ ≤ (|z.re| + |z.im|) / 8 := by
    have h1 : ‖1 / ρ - 1‖ * ‖z‖ ≤ (1 / 8) * (|z.re| + |z.im|) := by
      have hz0 : (0 : ℝ) ≤ |z.re| + |z.im| := by positivity
      calc ‖1 / ρ - 1‖ * ‖z‖ ≤ (1 / 8) * ‖z‖ := mul_le_mul_of_nonneg_right hinv (norm_nonneg z)
        _ ≤ (1 / 8) * (|z.re| + |z.im|) := mul_le_mul_of_nonneg_left hznorm (by norm_num)
    linarith [h1]
  calc (Φm z - z).re = (z / ρ - z).re + c.re + (Φm z - z / ρ - c).re := hdecomp
    _ ≤ (|z.re| + |z.im|) / 8 + ‖c‖ + 1 := by linarith [hzdeb, hcle, hres, hstep]
    _ ≤ 2 + max 1 (‖c‖ + 3) * (1 + Real.log (2 + M) + Ξ + Real.log (2 + |z.im|))
          + |z.im| / 8 + |z.re| / 8 := by linarith [hKbound]

end Work.Pert
