import Mathlib
import Submission.Work.Pert.Ksub2.Setup
import Submission.Work.PertCrux.f0_amp_uniform_K
import Submission.Work.Pert.Ksub2.deriv_phi_bounds_walk
import Submission.Work.Pert.Ksub2.deriv_phi_deep_upper
import Submission.Work.Pert.Ksub2.deriv_phi_strip_lower
import Submission.Work.Pert.Ksub2.Xc_strip_nhd_bounds
import Submission.Work.Pert.Ksub2.deriv_phi_le_high_strip
import Submission.Work.PertCrux.Xc_deep_ball_data
import Submission.Work.Pert.Ksub2.Xc_strip_nhd_bounds_bdd
import Submission.Work.PertCrux.Xc_strip_ball_geometry
import Submission.Work.PertCrux.Xc_local_three
import Submission.Work.Pert.Ksub2.Xcurve_bounds
import Submission.Work.Pert.exists_norm_add_clog_bound
import Submission.Work.Parab.inversion.exists_mul_log_lt

/-!
# `Work.Pert.Ksub2.f0_amp_band`

Uniform-in-`M` amplification of `f₀`-orbits on the **band** `{|Re w| ≤ 1, y₁ ≤ |Im w| ≤ Tb}`
(with `Tb` allowed to grow with `M`, subject to `C (1 + Tb) ≤ M`), replacing the compact `K'` of
`Work.PertCrux.f0_amp_uniform_K` by an unbounded band.

**Statement.**  For §4.1 data `d : ParabData f₀ D₀` and `y₁ > d.η₀` there is `C ≥ 1` such that for
all `M, Tb` with `C (1 + Tb) ≤ M`, `y₁ ≤ Tb`, all `w` with `|Re w| ≤ 1`, `y₁ ≤ |Im w| ≤ Tb`, all
`u ∈ Dstrip M Tb` with `u + n = w`, all `k ≤ n` and all `z` with `‖z - d.φ u‖ < 1/(C M²)`,

`‖f₀^[k] z - f₀^[k] (d.φ u)‖ ≤ C M² ‖z - d.φ u‖`.

**Proof.**  Two observations make the compactness of `f0_amp_uniform_K` unnecessary.

* The walk `u, u + 1, …, u + n = w` has **constant imaginary part** `w.im` (it is translated by
  real integers), so `|Im (u+i)| = |w.im| ≥ y₁ > η₀` on the whole walk.  Hence the `ρe`-balls
  around the walk points stay in `Dφ` (`ParabData.ends_sub`), and `deriv φ₀` is bounded there by
  the *band* bound `deriv_phi_le_high_strip` (`‖φ₀'‖ ≤ Cd` on `{|Im| ≥ y, Re ≤ B}`, `M`-free).
* The `Tb`-dependent thresholds of the strip lemmas (`Xc_strip_nhd_bounds_bdd`,
  `Xc_strip_ball_geometry`) are all *linear* in `Tb` (`≤ K₀ (1 + Tb)` for an explicit datum
  constant `K₀`), so the hypothesis `C (1 + Tb) ≤ M` with `C ≥ K₀` discharges them uniformly.

With that, the reusable core `Work.PertCrux.amp_core` (Rouché covering of `τ₀ '' ball` by the
Cayley curve `Xc d = τ₀ ∘ φ₀`, coercivity of `Xc`, mean value theorem at the far end of the walk)
applies verbatim, with `T₀ := Tb - 1`, `C₀ = 1`, `Kk = 1` and the walk radius `ρe`.
-/

namespace Work.Pert.Ksub2

open MandelDim Complex Set Metric

noncomputable section

set_option maxHeartbeats 4000000

/-- `1 + log (2 M) ≤ M / 16` once `M ≥ 1024`. -/
private lemma one_add_log_two_mul_le {M : ℝ} (hM : 1024 ≤ M) :
    1 + Real.log (2 * M) ≤ M / 16 := by
  have hMpos : 0 < M := by linarith
  have hlog2 : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
    linarith
  have h1024 : (1024 : ℝ) = 2 ^ 10 := by norm_num
  have hlog1024 : Real.log (1024 : ℝ) ≤ 10 := by
    have h : Real.log ((2 : ℝ) ^ 10) = 10 * Real.log 2 := Real.log_pow 2 10
    rw [← h1024] at h
    rw [h]
    linarith
  have hsplit : Real.log (2 * M) = Real.log 2 + Real.log M :=
    Real.log_mul (by norm_num) (ne_of_gt hMpos)
  have hsplit2 : Real.log M = Real.log (M / 1024) + Real.log (1024 : ℝ) := by
    rw [← Real.log_mul (by positivity) (by norm_num : (1024 : ℝ) ≠ 0)]
    congr 1
    ring
  have hsub : Real.log (M / 1024) ≤ M / 1024 - 1 :=
    Real.log_le_sub_one_of_pos (by positivity)
  rw [hsplit, hsplit2]
  linarith

theorem f0_amp_band {f₀ : ℂ → ℂ} {D₀ : Set ℂ} (d : MandelDim.ParabData f₀ D₀) {y₁ : ℝ}
    (hy₁ : d.η₀ < y₁) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ M Tb : ℝ, C * (1 + Tb) ≤ M → y₁ ≤ Tb →
      ∀ w : ℂ, |w.re| ≤ 1 → y₁ ≤ |w.im| → |w.im| ≤ Tb →
      ∀ u ∈ Work.Pert.Dstrip M Tb, ∀ n : ℕ, u + (n : ℂ) = w → ∀ k : ℕ, k ≤ n →
        ∀ z : ℂ, ‖z - d.φ u‖ < 1 / (C * M * M) →
          ‖f₀^[k] z - f₀^[k] (d.φ u)‖ ≤ C * M * M * ‖z - d.φ u‖ := by
  -- ## (1) the walk-ball radius and the uniform derivative bound on the band
  set ρe : ℝ := (y₁ - d.η₀) / 2 with hρedef
  have hρepos : 0 < ρe := by rw [hρedef]; linarith
  have hρele : ρe ≤ y₁ - d.η₀ := by rw [hρedef]; linarith
  have hyρ : d.η₀ < y₁ - ρe := by rw [hρedef]; linarith
  obtain ⟨Cd, hCdpos, hCd⟩ := deriv_phi_le_high_strip d (y := y₁ - ρe) (B := 1 + ρe) hyρ
  set Ce₀ : ℝ := max Cd 1 with hCe₀def
  have hCe₀1 : 1 ≤ Ce₀ := le_max_right _ _
  have hCe₀pos : 0 < Ce₀ := lt_of_lt_of_le one_pos hCe₀1
  have hCdle : Cd ≤ Ce₀ := le_max_left _ _
  -- ## (2) the deep-strip constants (independent of `M` and `Tb`)
  obtain ⟨R₀, hR₀pos, hloc⟩ := Work.PertCrux.Xc_local_three d
  obtain ⟨Mg, hMgpos, hgeom⟩ := Work.PertCrux.Xc_strip_ball_geometry d R₀
  -- ## (3) the Cayley-curve constants of the datum
  obtain ⟨C1, hC1pos, hXcur⟩ := Xcurve_bounds d
  obtain ⟨as, bs, hasym⟩ := d.φ_asymp
  obtain ⟨RA, hRA⟩ := hasym 1 one_pos
  obtain ⟨RB, hRB⟩ := Work.Pert.exists_norm_add_clog_bound as bs 1 one_pos
  obtain ⟨RL, hRLpos, hRL⟩ :=
    Work.Parab.inversion.exists_mul_log_lt_aux (a := C1) (b := C1) (c := 1 / 4) (by norm_num)
  -- ## (4) the threshold constant
  set K₀ : ℝ := 100000 + (d.ξ₀ + |d.ξ₀|) + |C1| + |RA| + |RB| + |RL| + |R₀| + |Mg| + Mg
    with hK₀def
  have hξnn : 0 ≤ d.ξ₀ + |d.ξ₀| := by have := neg_le_abs d.ξ₀; linarith
  have hξabs : 0 ≤ |d.ξ₀| := abs_nonneg d.ξ₀
  have hξle : d.ξ₀ ≤ |d.ξ₀| := le_abs_self d.ξ₀
  have hC1abs : 0 ≤ |C1| := abs_nonneg C1
  have hC1le : C1 ≤ |C1| := le_abs_self C1
  have hRAabs : 0 ≤ |RA| := abs_nonneg RA
  have hRBabs : 0 ≤ |RB| := abs_nonneg RB
  have hRLabs : 0 ≤ |RL| := abs_nonneg RL
  have hR0abs : 0 ≤ |R₀| := abs_nonneg R₀
  have hMgabs : 0 ≤ |Mg| := abs_nonneg Mg
  have hMgnn : 0 ≤ Mg := hMgpos.le
  have hK₀1 : 1 ≤ K₀ := by
    rw [hK₀def]; linarith [hξnn, hC1abs, hRAabs, hRBabs, hRLabs, hR0abs, hMgabs, hMgnn]
  have hK₀3 : 3 ≤ K₀ := by
    rw [hK₀def]; linarith [hξnn, hC1abs, hRAabs, hRBabs, hRLabs, hR0abs, hMgabs, hMgnn]
  have hK₀1024 : 1024 ≤ K₀ := by
    rw [hK₀def]; linarith [hξnn, hC1abs, hRAabs, hRBabs, hRLabs, hR0abs, hMgabs, hMgnn]
  have hK₀C1 : C1 + 2 ≤ K₀ := by
    rw [hK₀def]
    linarith [hξnn, hC1le, hRAabs, hRBabs, hRLabs, hR0abs, hMgabs, hMgnn]
  have hK₀ξ : d.ξ₀ + 2 ≤ K₀ := by
    rw [hK₀def]
    linarith [hξabs, hξle, hξnn, hC1abs, hRAabs, hRBabs, hRLabs, hR0abs, hMgabs, hMgnn]
  have hmaxR : max RA RB ≤ |RA| + |RB| := by
    refine max_le ?_ ?_
    · have h := abs_nonneg RB; have h' := le_abs_self RA; linarith
    · have h := abs_nonneg RA; have h' := le_abs_self RB; linarith
  have hK₀RA : max RA RB + 1 ≤ K₀ := by
    rw [hK₀def]
    linarith [hξnn, hmaxR, hC1abs, hRAabs, hRBabs, hRLabs, hR0abs, hMgabs, hMgnn]
  have hK₀RL : RL + 1 ≤ K₀ := by
    rw [hK₀def]
    have h := le_abs_self RL
    linarith [hξnn, hC1abs, hRAabs, hRBabs, hRLabs, hR0abs, hMgabs, hMgnn]
  have hK₀Mg : Mg ≤ K₀ := by
    rw [hK₀def]; linarith [hξnn, hC1abs, hRAabs, hRBabs, hRLabs, hR0abs, hMgabs, hMgnn]
  have hK₀G : (10 / 9) * d.ξ₀ + 14 / 9 ≤ K₀ := by
    rw [hK₀def]
    have h := le_abs_self d.ξ₀
    linarith [hξnn, hC1abs, hRAabs, hRBabs, hRLabs, hR0abs, hMgabs, hMgnn]
  -- ## (5) the small constant and the final constant
  set cc₀ : ℝ := min (min (1 / 18) (ρe / 200)) (1 / 400) with hcc₀def
  have hcc₀pos : 0 < cc₀ := by
    rw [hcc₀def]
    exact lt_min (lt_min (by norm_num) (by positivity)) (by norm_num)
  have hcc₀18 : cc₀ ≤ 1 / 18 := by
    rw [hcc₀def]; exact le_trans (min_le_left _ _) (min_le_left _ _)
  have hcc₀ρe : cc₀ ≤ ρe / 200 := by
    rw [hcc₀def]; exact le_trans (min_le_left _ _) (min_le_right _ _)
  have hcc₀400 : cc₀ ≤ 1 / 400 := by
    rw [hcc₀def]; exact min_le_right _ _
  have h36 : 36 * cc₀ < ρe := by
    have h := mul_le_mul_of_nonneg_left hcc₀ρe (by norm_num : (0 : ℝ) ≤ 36)
    nlinarith [h, hρepos]
  have h72 : 72 * cc₀ < 1 := by
    have h := mul_le_mul_of_nonneg_left hcc₀400 (by norm_num : (0 : ℝ) ≤ 72)
    linarith
  set C : ℝ := max 1 (max K₀ (max (2 * Ce₀ / cc₀) (1 / cc₀))) with hCdef
  have hC1' : 1 ≤ C := le_max_left _ _
  have hCK₀ : K₀ ≤ C := le_trans (le_max_left _ _) (le_max_right _ _)
  have hCCe : 2 * Ce₀ / cc₀ ≤ C :=
    le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_right _ _)
  have hCinv : 1 / cc₀ ≤ C :=
    le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _))
  have hCcc : 1 ≤ C * cc₀ := by
    have h := mul_le_mul_of_nonneg_right hCinv hcc₀pos.le
    rw [one_div_mul_cancel (ne_of_gt hcc₀pos)] at h
    linarith
  refine ⟨C, hC1', ?_⟩
  intro M Tb hCM hTb
  intro w hwre hw1 hw2
  have hTb0 : 0 ≤ Tb := le_trans (abs_nonneg w.im) hw2
  -- ## (6) the explicit strip bounds for the Cayley curve at width `Tb`
  obtain ⟨Enh, hEnhpos, hEnhle, hnh⟩ :=
    Xc_strip_nhd_bounds_bdd (d := d) (T := Tb) (C := C1) (R_A := RA) (R_B := RB)
      (R_L := RL) (a := as) (b := bs) hC1pos hXcur hRA hRB
      (fun x hx => by have := hRL x hx; linarith)
  -- ## (7) the thresholds, all of them linear in `Tb`
  set T₀ : ℝ := Tb - 1 with hT₀def
  have hT₀1 : T₀ + 1 = Tb := by rw [hT₀def]; ring
  set M₁ : ℝ := K₀ * (1 + Tb) with hM₁def
  have hK₀le : K₀ ≤ K₀ * (1 + Tb) := by nlinarith [hK₀1, hTb0]
  have hTble : Tb ≤ K₀ * (1 + Tb) := by nlinarith [hK₀1, hTb0]
  have hM₁ge : (1 : ℝ) ≤ K₀ * (1 + Tb) := by
    have h1 : (1 : ℝ) ≤ 1 + Tb := by linarith
    calc (1 : ℝ) = 1 * 1 := by ring
      _ ≤ K₀ * (1 + Tb) := mul_le_mul hK₀1 h1 (by norm_num) (by linarith [hK₀1])
  have hCM1 : M₁ ≤ M := by
    rw [hM₁def]
    refine le_trans (mul_le_mul_of_nonneg_right hCK₀ (by linarith)) hCM
  have hM₁1 : 1 ≤ M₁ := by rw [hM₁def]; exact hM₁ge
  have hKkM : 6 * cc₀ ≤ 1 * M₁ := by
    have h : 6 * cc₀ ≤ 1 / 3 := by linarith [hcc₀18]
    have h2 : (1 : ℝ) ≤ M₁ := hM₁1
    linarith
  have hthr : max 1 (max (C1 + 2) (max (Tb + 3) (max (d.ξ₀ + 2) (max (max RA RB + 1)
      (max RL ((10 / 9) * (d.ξ₀ + 1 / 4 + (Tb + 3 / 2) / 10 + 1))))))) ≤ K₀ * (1 + Tb) := by
    refine max_le hM₁ge (max_le ?_ (max_le ?_ (max_le ?_ (max_le ?_ (max_le ?_ ?_)))))
    · -- `C1 + 2 ≤ K₀ * (1 + Tb)`
      linarith [hK₀C1, hK₀le]
    · -- `Tb + 3 ≤ K₀ * (1 + Tb)`
      have h1 : Tb + 3 ≤ 3 * (1 + Tb) := by linarith
      have h2 : 3 * (1 + Tb) ≤ K₀ * (1 + Tb) :=
        mul_le_mul_of_nonneg_right hK₀3 (by linarith)
      linarith
    · -- `d.ξ₀ + 2 ≤ K₀ * (1 + Tb)`
      linarith [hK₀ξ, hK₀le]
    · -- `max RA RB + 1 ≤ K₀ * (1 + Tb)`
      linarith [hK₀RA, hK₀le]
    · -- `RL ≤ K₀ * (1 + Tb)`
      linarith [hK₀RL, hK₀le]
    · -- the logarithmic term
      have h1 : (10 / 9) * (d.ξ₀ + 1 / 4 + (Tb + 3 / 2) / 10 + 1)
          = (10 / 9) * d.ξ₀ + Tb / 9 + 14 / 9 := by ring
      have h2 : Tb / 9 ≤ Tb * K₀ := by nlinarith [hTb0, hK₀1]
      rw [h1]
      nlinarith [hK₀G, h2, hTb0, hK₀1]
  -- ## (8) the three hypotheses of `amp_core`
  have hwalk : ∀ M' : ℝ, M₁ ≤ M' →
      ∀ w' ∈ ({w : ℂ | |w.re| ≤ 1 ∧ y₁ ≤ |w.im| ∧ |w.im| ≤ Tb} : Set ℂ),
      ∀ u' ∈ Work.Pert.Dstrip M' (T₀ + 1), ∀ n' : ℕ, u' + (n' : ℂ) = w' → ∀ i : ℕ, i ≤ n' →
        Metric.ball (u' + (i : ℂ)) ρe ⊆ d.Dφ ∧
        ∀ z : ℂ, z ∈ d.Dφ → ‖z - (u' + (i : ℂ))‖ ≤ ρe → ‖deriv d.φ z‖ ≤ Ce₀ := by
    intro M' _ w' hw' u' _ n' hn' i hi
    simp only [Set.mem_setOf_eq] at hw'
    obtain ⟨hwre', hwim1', hwim2'⟩ := hw'
    have him' : (u' + (i : ℂ)).im = w'.im := by
      have h := congrArg Complex.im hn'
      simpa using h
    have hre' : (u' + (i : ℂ)).re ≤ w'.re := by
      have h := congrArg Complex.re hn'
      have h1 : (u' + (n' : ℂ)).re = u'.re + (n' : ℝ) := by simp
      have h2 : (u' + (i : ℂ)).re = u'.re + (i : ℝ) := by simp
      rw [h1] at h
      rw [h2]
      have hi' : (i : ℝ) ≤ (n' : ℝ) := by exact_mod_cast hi
      linarith
    have hwre1 : w'.re ≤ 1 := le_trans (le_abs_self w'.re) hwre'
    constructor
    · -- the `ρe`-ball around the walk point lies in `Dφ`
      intro z hz
      rw [Metric.mem_ball, dist_eq_norm] at hz
      refine (d.ends_sub z ?_).1
      have h2 : |z.im - (u' + (i : ℂ)).im| ≤ ‖z - (u' + (i : ℂ))‖ := by
        have h := Complex.abs_im_le_norm (z - (u' + (i : ℂ)))
        rwa [Complex.sub_im] at h
      rw [him'] at h2
      have h3 : |w'.im| ≤ |z.im| + |z.im - w'.im| := by
        have h := abs_sub_abs_le_abs_sub w'.im z.im
        rw [abs_sub_comm] at h
        linarith
      linarith
    · -- the derivative bound on the band
      intro z hzD hzu
      refine le_trans (hCd z hzD ?_ ?_) hCdle
      · have h2 : |z.im - (u' + (i : ℂ)).im| ≤ ‖z - (u' + (i : ℂ))‖ := by
          have h := Complex.abs_im_le_norm (z - (u' + (i : ℂ)))
          rwa [Complex.sub_im] at h
        rw [him'] at h2
        have h3 : |w'.im| ≤ |z.im| + |z.im - w'.im| := by
          have h := abs_sub_abs_le_abs_sub w'.im z.im
          rw [abs_sub_comm] at h
          linarith
        linarith
      · have h2 : |z.re - (u' + (i : ℂ)).re| ≤ ‖z - (u' + (i : ℂ))‖ := by
          have h := Complex.abs_re_le_norm (z - (u' + (i : ℂ)))
          rwa [Complex.sub_re] at h
        have h3 : z.re ≤ (u' + (i : ℂ)).re + ρe := by
          have h4 := (abs_le.mp h2).2
          linarith
        linarith
  have hstrip : ∀ M' : ℝ, M₁ ≤ M' → ∀ u' ∈ Work.Pert.Dstrip M' (T₀ + 1),
      ‖Work.Pert.Xc d u'‖ ≤ 3 * M' ∧ d.φ u' ≠ 0 := by
    intro M' hM' u' hu'
    rw [hT₀1] at hu'
    have hM'M : K₀ * (1 + Tb) ≤ M' := by rw [hM₁def] at hM'; exact hM'
    have hK₀M' : K₀ ≤ M' := le_trans hK₀le hM'M
    have hthr' : Enh ≤ M' := le_trans hEnhle (le_trans hthr hM'M)
    have huQ : u' ∈ MandelDim.QLeft d.ξ₀ :=
      Work.Pert.Dstrip_sub_QLeft (M := M') (T := Tb) (ξ := d.ξ₀)
        (by linarith [hK₀ξ, hK₀M'] : d.ξ₀ + 1 ≤ M') hu'
    have huDφ : u' ∈ d.Dφ := d.Q_sub huQ
    obtain ⟨-, h2, h3⟩ := hnh M' hthr' u' hu' u' huDφ (by simp)
    exact ⟨h2, h3⟩
  have hdeep : ∀ M' : ℝ, M₁ ≤ M' → ∀ u' ∈ Work.Pert.Dstrip M' (T₀ + 1),
      (∀ z : ℂ, ‖z - u'‖ ≤ 1 * (1 + Real.log (2 * M')) → z ∈ MandelDim.QLeft d.ξ₀) ∧
      (∀ z : ℂ, ‖z - u'‖ ≤ 1 * (1 + Real.log (2 * M')) →
        DifferentiableAt ℂ (Work.Pert.Xc d) z) ∧
      (∀ z : ℂ, ‖z - u'‖ ≤ 1 * (1 + Real.log (2 * M')) →
        ‖deriv (Work.Pert.Xc d) z - 1‖ ≤ 1 / 2) := by
    intro M' hM' u' hu'
    rw [hT₀1] at hu'
    have hM'M : K₀ * (1 + Tb) ≤ M' := by rw [hM₁def] at hM'; exact hM'
    have hK₀M' : K₀ ≤ M' := le_trans hK₀le hM'M
    have hMgM' : Mg ≤ M' := le_trans hK₀Mg hK₀M'
    have hTbM' : Tb ≤ M' := le_trans hTble hM'M
    have hM'1024 : 1024 ≤ M' := le_trans hK₀1024 hK₀M'
    have hlog : 1 + Real.log (2 * M') ≤ M' / 16 := one_add_log_two_mul_le hM'1024
    have hr0 : 0 ≤ 1 + Real.log (2 * M') := by
      have h : 0 ≤ Real.log (2 * M') := Real.log_nonneg (by linarith)
      linarith
    have hgm : ∀ z : ℂ, ‖z - u'‖ ≤ 1 + Real.log (2 * M') →
        z ∈ MandelDim.QLeft d.ξ₀ ∧ Metric.ball z (‖z‖ / 10) ⊆ MandelDim.QLeft d.ξ₀ ∧
          R₀ ≤ ‖z‖ :=
      fun z hz => hgeom M' hMgM' Tb hTb0 hTbM' (1 + Real.log (2 * M')) hr0 hlog u' hu' z hz
    refine ⟨fun z hz => (hgm z (by simpa using hz)).1, ?_, ?_⟩
    · intro z hz
      have hz' : ‖z - u'‖ ≤ 1 + Real.log (2 * M') := by simpa using hz
      exact (hloc z (hgm z hz').1 (hgm z hz').2.2 (hgm z hz').2.1).1
    · intro z hz
      have hz' : ‖z - u'‖ ≤ 1 + Real.log (2 * M') := by simpa using hz
      exact (hloc z (hgm z hz').1 (hgm z hz').2.2 (hgm z hz').2.1).2
  -- ## (9) the amplification core
  have hamp := Work.PertCrux.amp_core
    (K' := ({w : ℂ | |w.re| ≤ 1 ∧ y₁ ≤ |w.im| ∧ |w.im| ≤ Tb} : Set ℂ))
    (T₀ := T₀) (ρe := ρe) (Ce₀ := Ce₀) (cc₀ := cc₀) (C₀ := 1) (M₁ := M₁) (Kk := 1)
    d hρepos hCe₀pos hcc₀pos one_pos (by norm_num) hcc₀18 (by simpa using h36)
      (by simpa using h72) hM₁1 hKkM hwalk hstrip hdeep
  -- ## (10) the conclusion
  intro u hu n hn k hk z hz
  have hMpos : 0 < M := lt_of_lt_of_le one_pos (le_trans hM₁1 hCM1)
  have hMMpos : 0 < M * M := mul_pos hMpos hMpos
  have hCpos : 0 < C := lt_of_lt_of_le one_pos hC1'
  have hle : 1 / (C * M * M) ≤ cc₀ / (1 * M * M) := by
    rw [div_le_div_iff₀ (mul_pos (mul_pos hCpos hMpos) hMpos)
      (mul_pos (mul_pos one_pos hMpos) hMpos)]
    nlinarith [hCcc, hMMpos, hcc₀pos]
  have hz' : ‖z - d.φ u‖ < cc₀ / (1 * M * M) := lt_of_lt_of_le hz hle
  have huT : u ∈ Work.Pert.Dstrip M (T₀ + 1) := by rw [hT₀1]; exact hu
  have hwK : w ∈ ({w : ℂ | |w.re| ≤ 1 ∧ y₁ ≤ |w.im| ∧ |w.im| ≤ Tb} : Set ℂ) :=
    ⟨hwre, hw1, hw2⟩
  have hmain := hamp M hCM1 w hwK u huT n hn k hk z hz'
  have hkey : 2 * Ce₀ * M * M / cc₀ ≤ C * M * M := by
    calc 2 * Ce₀ * M * M / cc₀ = (2 * Ce₀ / cc₀) * (M * M) := by ring
      _ ≤ C * (M * M) := mul_le_mul_of_nonneg_right hCCe hMMpos.le
      _ = C * M * M := by ring
  calc ‖f₀^[k] z - f₀^[k] (d.φ u)‖
      ≤ (2 * Ce₀ * M * M / cc₀) * ‖z - d.φ u‖ := hmain
    _ ≤ (C * M * M) * ‖z - d.φ u‖ := mul_le_mul_of_nonneg_right hkey (norm_nonneg _)

end

end Work.Pert.Ksub2
