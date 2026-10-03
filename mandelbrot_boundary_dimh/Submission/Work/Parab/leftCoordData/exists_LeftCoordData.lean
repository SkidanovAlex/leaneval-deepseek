import Mathlib
import Submission.Work.Parab.LeftData
import Submission.Work.Parab.Setup
import Submission.Work.FatouCoord.Setup
import Submission.Work.FatouCoord.Exist.fatouCoordW_abel
import Submission.Work.FatouCoord.Exist.fatouCoordW_tsum_bound
import Submission.Work.FatouCoord.Exist.fatouCoordW_differentiable
import Submission.Work.FatouCoord.Exist.fatouCoordW_injOn
import Submission.Work.FatouCoord.Exist.fatouCoordW_deriv_close
import Submission.Work.FatouCoord.Estimate.wMap_iterate_deriv_bound
import Submission.Work.FatouCoord.Petal.reflected_inverse_germ
import Submission.Work.Parab.basinEnters.petal_capture
import Submission.Work.Parab.leftCoord.escC
import Submission.Work.Parab.leftCoord.levelData
import Submission.Work.Parab.leftCoord.wMap_large_estimates
import Submission.Work.Parab.leftCoord.wMap_orbit_estimates
import Submission.Work.Parab.leftCoord.wMap_orbit_facts
import Submission.Work.Parab.leftCoordData.orbit_ends_control
import Submission.Work.Parab.leftCoordData.psi_approx_of_ends
import Submission.Work.Parab.leftCoordData.image_QLeft

/-!
# The left coordinate data of a parabolic germ

We assemble `Work.Parab.LeftCoordData f D` for an arbitrary parabolic germ `f` on `D`, from the
reflected inverse germ `F u = -finv (-u)` (whose chart dynamics `G = wMap F` moves real parts to
the right) together with the *closed* extension `PsiC N G ψ` of the Fatou coordinate
`ψ = fatouCoordW F (1 - (2 - a))` (`Submission.Work.Parab.leftCoord.escC`, needed because the
strict `Esc` misses points whose orbit passes through the level `N` exactly).

The coordinate is

`Φ ζ = - PsiC N (wMap F) ψ (-ζ)` on
`L = {Re ζ < -M₀} ∪ {-ζ ∈ EscC N (wMap F), M₁ < |Im ζ|, Re ζ < 3|Im ζ|}`,

a branch of the repelling (left) Ecalle coordinate: it satisfies `Φ (wMap f ζ) = Φ ζ + 1` (the
reflection `F` converts the `f`-dynamics into the inverse `F`-dynamics), is holomorphic and
injective on `L`, has the asymptotic `Φ ζ = ζ - (1-a) log (-ζ) + o(1)`, and its image covers the
far part of Shishikura's sector `QLeft`.
-/

namespace Work.Parab.leftCoordData

set_option maxHeartbeats 2000000

open Complex Set Metric Filter Topology
open scoped Topology

noncomputable section

variable {f h : ℂ → ℂ} {a : ℂ} {r A A' : ℝ}

/-- **The `FatouCoord` estimates at a single level**, packaged as `LevelFacts`. -/
theorem exists_levelFacts (hb : Work.FatouCoord.ParabolicBounds f h a r A A') :
    ∃ N : ℝ, Work.Parab.leftCoord.LevelFacts f h a r N := by
  obtain ⟨Nab, -, hNabr, habel⟩ := Work.FatouCoord.Exist.fatouCoordW_abel hb
  obtain ⟨Nts, Kts, -, hNtsr, hKtsnn, htsum⟩ := Work.FatouCoord.Exist.fatouCoordW_tsum_bound hb
  obtain ⟨Nd, -, hNdr, hψdiff⟩ := Work.FatouCoord.Exist.fatouCoordW_differentiable hb
  obtain ⟨Ni, -, hNir, hψinj⟩ := Work.FatouCoord.Exist.fatouCoordW_injOn hb
  obtain ⟨Ndc, -, hNdcr, hdc⟩ := Work.FatouCoord.Exist.fatouCoordW_deriv_close hb
  obtain ⟨Nsb, Ksb, -, hNsbr, hKsbnn, hstep⟩ := Work.Parab.leftCoord.wMap_step_bound_norm hb
  obtain ⟨Rl, Kl, -, hRlr, hKlnn, hest⟩ := Work.Parab.leftCoord.wMap_large_estimates hb
  obtain ⟨ρ, hρpos, -, hinjρ⟩ := Work.Parab.leftCoord.injOn_ball_of_parabolicBounds hb
  set N : ℝ := |Nab| + |Nts| + |Nd| + |Ni| + |Ndc| + |Nsb| + |Rl| + |1 / r| + |1 / ρ| + 10
    with hNdef
  have hNpos : 0 < N := by rw [hNdef]; positivity
  have hNabN : Nab < N := by
    rw [hNdef]
    linarith [le_abs_self Nab, abs_nonneg Nts, abs_nonneg Nd, abs_nonneg Ni, abs_nonneg Ndc,
      abs_nonneg Nsb, abs_nonneg Rl, abs_nonneg (1 / r), abs_nonneg (1 / ρ)]
  have hNtsN : Nts < N := by
    rw [hNdef]
    linarith [le_abs_self Nts, abs_nonneg Nab, abs_nonneg Nd, abs_nonneg Ni, abs_nonneg Ndc,
      abs_nonneg Nsb, abs_nonneg Rl, abs_nonneg (1 / r), abs_nonneg (1 / ρ)]
  have hNdN : Nd < N := by
    rw [hNdef]
    linarith [le_abs_self Nd, abs_nonneg Nab, abs_nonneg Nts, abs_nonneg Ni, abs_nonneg Ndc,
      abs_nonneg Nsb, abs_nonneg Rl, abs_nonneg (1 / r), abs_nonneg (1 / ρ)]
  have hNiN : Ni < N := by
    rw [hNdef]
    linarith [le_abs_self Ni, abs_nonneg Nab, abs_nonneg Nts, abs_nonneg Nd, abs_nonneg Ndc,
      abs_nonneg Nsb, abs_nonneg Rl, abs_nonneg (1 / r), abs_nonneg (1 / ρ)]
  have hNdcN : Ndc < N := by
    rw [hNdef]
    linarith [le_abs_self Ndc, abs_nonneg Nab, abs_nonneg Nts, abs_nonneg Nd, abs_nonneg Ni,
      abs_nonneg Nsb, abs_nonneg Rl, abs_nonneg (1 / r), abs_nonneg (1 / ρ)]
  have hNsbN : Nsb < N := by
    rw [hNdef]
    linarith [le_abs_self Nsb, abs_nonneg Nab, abs_nonneg Nts, abs_nonneg Nd, abs_nonneg Ni,
      abs_nonneg Ndc, abs_nonneg Rl, abs_nonneg (1 / r), abs_nonneg (1 / ρ)]
  have hRlN : Rl < N := by
    rw [hNdef]
    linarith [le_abs_self Rl, abs_nonneg Nab, abs_nonneg Nts, abs_nonneg Nd, abs_nonneg Ni,
      abs_nonneg Ndc, abs_nonneg Nsb, abs_nonneg (1 / r), abs_nonneg (1 / ρ)]
  have h1rN : 1 / r < N := by
    rw [hNdef]
    linarith [le_abs_self (1 / r), abs_nonneg Nab, abs_nonneg Nts, abs_nonneg Nd, abs_nonneg Ni,
      abs_nonneg Ndc, abs_nonneg Nsb, abs_nonneg Rl, abs_nonneg (1 / ρ)]
  have h1ρN : 1 / ρ < N := by
    rw [hNdef]
    linarith [le_abs_self (1 / ρ), abs_nonneg Nab, abs_nonneg Nts, abs_nonneg Nd, abs_nonneg Ni,
      abs_nonneg Ndc, abs_nonneg Nsb, abs_nonneg Rl, abs_nonneg (1 / r)]
  have h4N : (4 : ℝ) < N := by
    rw [hNdef]
    linarith [abs_nonneg Nab, abs_nonneg Nts, abs_nonneg Nd, abs_nonneg Ni, abs_nonneg Ndc,
      abs_nonneg Nsb, abs_nonneg Rl, abs_nonneg (1 / r), abs_nonneg (1 / ρ)]
  refine ⟨N, hNpos, h1rN, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine ⟨max Kl Ksb, le_max_of_le_left hKlnn, fun x hx => ?_⟩
    have hxpos : 0 < ‖x‖ := lt_trans hNpos hx
    obtain ⟨h1, h2, h3⟩ := hest x (lt_trans hRlN hx)
    obtain ⟨h4, h5⟩ := hstep x (lt_trans hNsbN hx)
    have hK1 : Kl / ‖x‖ ≤ max Kl Ksb / ‖x‖ :=
      div_le_div_of_nonneg_right (le_max_left _ _) (le_of_lt hxpos)
    have hK2 : Kl / ‖x‖ ^ 2 ≤ max Kl Ksb / ‖x‖ ^ 2 :=
      div_le_div_of_nonneg_right (le_max_left _ _) (by positivity)
    exact ⟨le_trans h1 hK1, le_trans h2 hK2, le_trans h3 hK2, h5⟩
  · exact fun x hx =>
      Work.FatouCoord.Estimate.differentiableAt_wMap hb (lt_trans h1rN hx)
        (le_of_lt (lt_trans h4N hx))
  · refine Work.Parab.leftCoord.injOn_wMap_of_injOn_ball hinjρ (fun x hx => ?_)
    have hx0 : x ≠ 0 := by
      rintro rfl
      have h := hx
      simp only [Set.mem_ofPred_eq, norm_zero] at h
      linarith [hNpos]
    refine ⟨hx0, ?_⟩
    have hlt : (‖x‖)⁻¹ < ρ :=
      (inv_lt_comm₀ hρpos (lt_trans hNpos hx)).mp (by rw [inv_eq_one_div]; exact lt_trans h1ρN hx)
    simpa only [Metric.mem_ball, dist_eq_norm, sub_zero, Work.FatouCoord.norm_chart hx0] using hlt
  · exact fun x hx => habel x (lt_trans hNabN hx)
  · exact hψdiff.mono fun x hx => lt_trans hNdN hx
  · exact hψinj.mono fun x hx => lt_trans hNiN hx
  · exact fun x hx => hdc x (lt_trans hNdcN hx)
  · exact ⟨Kts, hKtsnn, fun w hw => htsum w (lt_trans hNtsN hw)⟩

/-- **The reflection identity.**  For the reflected inverse germ `F u = -finv (-u)` of `f`, the
`f`-chart dynamics in the `ζ`-plane is the inverse of the `F`-chart dynamics on the `-ζ` side:
`wMap F (- (wMap f ζ)) = -ζ` for `‖ζ‖` large. -/
theorem wMap_F_neg_wMap {finv F : ℂ → ℂ} {r' : ℝ}
    (hb : Work.FatouCoord.ParabolicBounds f h a r A A')
    (hr' : 0 < r')
    (hfinv : ∀ z ∈ ball 0 r', finv (f z) = z) (hFdef : ∀ u ∈ ball 0 r', F u = -finv (-u))
    {b : ℝ} (hb1 : 1 / r + 4 ≤ b) (hb2 : 4 / r' + 4 ≤ b) {ζ : ℂ} (hζ : b ≤ ‖ζ‖) :
    Work.FatouCoord.wMap F (-(Work.FatouCoord.wMap f ζ)) = -ζ := by
  have hb0 : 0 < b := lt_of_lt_of_le (by linarith [one_div_pos.mpr hb.hr]) hb1
  have hζnorm : 0 < ‖ζ‖ := lt_of_lt_of_le hb0 hζ
  have hζ0 : ζ ≠ 0 := norm_pos_iff.mp hζnorm
  have hζbig : 4 / r' < ‖ζ‖ := by linarith
  have hζr : 1 / r < ‖ζ‖ := by linarith
  have hznorm : ‖-1 / ζ‖ = 1 / ‖ζ‖ := by rw [norm_div, norm_neg, norm_one]
  -- `-1/ζ ∈ ball 0 r'`
  have hz1 : -1 / ζ ∈ ball 0 r' := by
    rw [Metric.mem_ball, dist_eq_norm, sub_zero, hznorm]
    have h14 : 1 / r' < 4 / r' := by
      rw [div_lt_div_iff_of_pos_right hr']; norm_num
    simpa only [inv_eq_one_div] using
      (inv_lt_comm₀ hr' hζnorm).mp (by rw [inv_eq_one_div]; exact lt_trans h14 hζbig)
  have hzball : -1 / ζ ∈ ball 0 r := by
    rw [Metric.mem_ball, dist_eq_norm, sub_zero, hznorm]
    rw [div_lt_iff₀ hζnorm]
    rw [div_lt_iff₀ hb.hr] at hζr
    linarith
  have hbnd_h : ‖h (-1/ζ)‖ ≤ 2 := hb.h_bound _ hzball
  have hsmall : ‖-1 / ζ‖ ≤ 1 / 2 := by
    rw [hznorm, div_le_iff₀ hζnorm]
    have h2 : (2:ℝ) ≤ ‖ζ‖ := by
      linarith [show (0:ℝ) < 4 / r' by positivity]
    nlinarith
  have hfz : f (-1 / ζ) = (-1 / ζ) * (1 + (-1 / ζ) * h (-1 / ζ)) := by
    rw [hb.f_eq _ hzball]; ring
  have hden : ‖1 + (-1 / ζ) * h (-1 / ζ)‖ ≤ 2 := by
    have h1 : ‖1 + (-1 / ζ) * h (-1 / ζ)‖ ≤ 1 + ‖(-1 / ζ) * h (-1 / ζ)‖ := by
      simpa using norm_add_le (1 : ℂ) ((-1 / ζ) * h (-1 / ζ))
    have h2 : ‖(-1 / ζ) * h (-1 / ζ)‖ ≤ ‖-1/ζ‖ * 2 := by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left hbnd_h (norm_nonneg _)
    linarith
  have hfball : -(f (-1 / ζ)) ∈ ball 0 r' := by
    rw [Metric.mem_ball, dist_eq_norm, sub_zero, norm_neg, hfz, norm_mul]
    calc ‖-1 / ζ‖ * ‖1 + (-1 / ζ) * h (-1 / ζ)‖ ≤ ‖-1/ζ‖ * 2 :=
          mul_le_mul_of_nonneg_left hden (norm_nonneg _)
      _ = 2 / ‖ζ‖ := by rw [hznorm]; ring
      _ < r' := by
          rw [div_lt_iff₀ hζnorm]
          rw [div_lt_iff₀ hr'] at hζbig
          linarith
  have hfin : finv (f (-1 / ζ)) = -1 / ζ := hfinv _ hz1
  have hFv : F (-(f (-1 / ζ))) = -finv (f (-1 / ζ)) := by
    simpa only [neg_neg] using hFdef _ hfball
  have hkey : -1 / (-(Work.FatouCoord.wMap f ζ)) = -(f (-1 / ζ)) := by
    rw [Work.FatouCoord.wMap_apply]
    field_simp
  rw [Work.FatouCoord.wMap_apply, hkey, hFv, hfin]
  have hlast : -1 / (-(-1 / ζ)) = -ζ := by field_simp
  exact hlast


/-- **The left coordinate data of a parabolic germ.** -/
theorem exists_LeftCoordData {f : ℂ → ℂ} {D : Set ℂ} (hg : MandelDim.IsParabolicGerm f D) :
    Nonempty (Work.Parab.LeftCoordData f D) := by
  classical
  -- ## 0. the quantitative data of `f` and of the reflected inverse germ `F`
  obtain ⟨h, a, r, A, A', hb, -⟩ := Work.Parab.basinEnters.exists_parabolicBounds_of_germ hg
  obtain ⟨finv, F, hF, r', A'', A''', hbF, hfinv, hffinv, hFdef⟩ :=
    Work.FatouCoord.Petal.reflected_inverse_germ hb
  obtain ⟨N, LF⟩ := exists_levelFacts hbF
  obtain ⟨Kts, hKtsnn, hrem⟩ := LF.rem
  have hr' : 0 < r' := hbF.hr
  -- ## 1. the orbit and asymptotic inputs
  obtain ⟨Mo, Co, hMopos, hConn, horb⟩ :=
    Work.Parab.leftCoordData.orbit_ends_control hbF (N := N) LF.pos
  obtain ⟨Na, hNapos, hNar, hasymF⟩ := Work.Parab.leftCoordData.psi_approx_of_ends hbF
  -- ## 2. the constants
  obtain ⟨M₀, hM0def⟩ : ∃ M : ℝ, M = |Mo| + |Na| + |N| + |1 / r| + |4 / r| + |4 / r'| + 10 :=
    ⟨_, rfl⟩
  obtain ⟨M₁, hM1def⟩ : ∃ M : ℝ,
      M = |Mo| + |Na| + |4 * N| + |1 / r| + |4 / r| + |4 / r'| + 20 := ⟨_, rfl⟩
  have hM0pos : 0 < M₀ := by rw [hM0def]; positivity
  have hM1pos : 0 < M₁ := by rw [hM1def]; positivity
  have hM0N : N ≤ M₀ := by rw [hM0def]; linarith [le_abs_self N,abs_nonneg Mo, abs_nonneg Na, abs_nonneg N, abs_nonneg (4 * N), abs_nonneg (1 / r), abs_nonneg (4 / r), abs_nonneg (4 / r')]
  have hM0Mo : Mo ≤ M₀ := by rw [hM0def]; linarith [le_abs_self Mo,abs_nonneg Mo, abs_nonneg Na, abs_nonneg N, abs_nonneg (4 * N), abs_nonneg (1 / r), abs_nonneg (4 / r), abs_nonneg (4 / r')]
  have hM0Na : Na ≤ M₀ := by rw [hM0def]; linarith [le_abs_self Na,abs_nonneg Mo, abs_nonneg Na, abs_nonneg N, abs_nonneg (4 * N), abs_nonneg (1 / r), abs_nonneg (4 / r), abs_nonneg (4 / r')]
  have hM0b : max (1 / r + 4) (4 / r' + 4) ≤ M₀ := by
    rw [hM0def]
    refine max_le ?_ ?_
    · linarith [le_abs_self (1 / r),abs_nonneg Mo, abs_nonneg Na, abs_nonneg N, abs_nonneg (4 * N), abs_nonneg (1 / r), abs_nonneg (4 / r), abs_nonneg (4 / r')]
    · linarith [le_abs_self (4 / r'),abs_nonneg Mo, abs_nonneg Na, abs_nonneg N, abs_nonneg (4 * N), abs_nonneg (1 / r), abs_nonneg (4 / r), abs_nonneg (4 / r')]
  have hM1Mo : Mo ≤ M₁ := by rw [hM1def]; linarith [le_abs_self Mo,abs_nonneg Mo, abs_nonneg Na, abs_nonneg N, abs_nonneg (4 * N), abs_nonneg (1 / r), abs_nonneg (4 / r), abs_nonneg (4 / r')]
  have hM1Na : Na ≤ M₁ := by rw [hM1def]; linarith [le_abs_self Na,abs_nonneg Mo, abs_nonneg Na, abs_nonneg N, abs_nonneg (4 * N), abs_nonneg (1 / r), abs_nonneg (4 / r), abs_nonneg (4 / r')]
  have hM1_4N : 4 * N ≤ M₁ := by rw [hM1def]; linarith [le_abs_self (4 * N),abs_nonneg Mo, abs_nonneg Na, abs_nonneg N, abs_nonneg (4 * N), abs_nonneg (1 / r), abs_nonneg (4 / r), abs_nonneg (4 / r')]
  have hM1b : max (1 / r + 4) (4 / r' + 4) ≤ M₁ := by
    rw [hM1def]
    refine max_le ?_ ?_
    · linarith [le_abs_self (1 / r),abs_nonneg Mo, abs_nonneg Na, abs_nonneg N, abs_nonneg (4 * N), abs_nonneg (1 / r), abs_nonneg (4 / r), abs_nonneg (4 / r')]
    · linarith [le_abs_self (4 / r'),abs_nonneg Mo, abs_nonneg Na, abs_nonneg N, abs_nonneg (4 * N), abs_nonneg (1 / r), abs_nonneg (4 / r), abs_nonneg (4 / r')]
  -- ## 3. the domain and the coordinate
  obtain ⟨L, hLdef⟩ : ∃ S : Set ℂ, S = ({ζ : ℂ | ζ.re < -M₀} ∪
      {ζ : ℂ | -ζ ∈ Work.Parab.leftCoord.EscC N (Work.FatouCoord.wMap F) ∧
        M₁ < |ζ.im| ∧ ζ.re < 3 * |ζ.im|}) := ⟨_, rfl⟩
  obtain ⟨Φ, hΦdef⟩ : ∃ g : ℂ → ℂ, g = (fun ζ => -Work.Parab.leftCoord.PsiC N
      (Work.FatouCoord.wMap F) (Work.FatouCoord.fatouCoordW F (1 - (2 - a))) (-ζ)) :=
    ⟨_, rfl⟩
  -- ## 4. the basic hypotheses of the extension lemmas
  have hGN : ∀ x : ℂ, N < x.re → N < (Work.FatouCoord.wMap F x).re := by
    intro x hx
    have hxnorm : N < ‖x‖ := lt_of_lt_of_le hx (Complex.re_le_norm x)
    have h := (LF.step.choose_spec.2 x hxnorm).2.2.2
    linarith
  have hmono : ∀ x : ℂ, N < ‖x‖ → x.re ≤ (Work.FatouCoord.wMap F x).re := by
    intro x hx
    have h := (LF.step.choose_spec.2 x hx).2.2.2
    linarith
  have hLsub : ∀ ζ ∈ L, -ζ ∈ Work.Parab.leftCoord.EscC N (Work.FatouCoord.wMap F) := by
    intro ζ hζ
    rw [hLdef] at hζ
    rcases hζ with h | ⟨h1, -, -⟩
    · have hmem : ζ.re < -M₀ := h
      refine ⟨0, Work.Parab.leftCoord.GoodC.zero ?_⟩
      have hgoal : N < -ζ.re := by linarith
      simpa only [Complex.neg_re] using hgoal
    · exact h1
  have hLim_le : ∀ ζ : ℂ, M₁ < |ζ.im| → ζ.re < 3 * |ζ.im| → ζ ∈ L := by
    intro ζ h1 h2
    rw [hLdef]
    refine Or.inr ⟨?_, h1, h2⟩
    obtain ⟨n, hn1, -, hn3, -, -⟩ := horb (-ζ)
      (by simpa only [Complex.neg_im, abs_neg] using lt_of_le_of_lt hM1Mo h1)
      (by simp only [Complex.neg_re, Complex.neg_im, abs_neg]; linarith)
    refine ⟨n, ?_, hn1⟩
    intro k hk
    have hk' := hn3 k hk
    simp only [Complex.neg_im, abs_neg] at hk'
    have h4 : N < |ζ.im| / 4 := by linarith
    linarith
  -- ## 5. the fields
  have hLopen : IsOpen L := by
    rw [hLdef]
    refine IsOpen.union (isOpen_lt Complex.continuous_re continuous_const) ?_
    exact ((Work.Parab.leftCoord.isOpen_EscC (N := N) (G := Work.FatouCoord.wMap F)
      LF.gdiff).preimage continuous_neg).inter
      ((isOpen_lt continuous_const (Continuous.abs Complex.continuous_im)).inter
        (isOpen_lt Complex.continuous_re
          (continuous_const.mul (Continuous.abs Complex.continuous_im))))
  have hΦholo : DifferentiableOn ℂ Φ L := by
    have h1 : DifferentiableOn ℂ (Work.Parab.leftCoord.PsiC N (Work.FatouCoord.wMap F)
        (Work.FatouCoord.fatouCoordW F (1 - (2 - a))))
        (Work.Parab.leftCoord.EscC N (Work.FatouCoord.wMap F)) :=
      Work.Parab.leftCoord.PsiC_differentiableOn LF.abel hmono LF.gdiff LF.ψdiff
    have h2 : DifferentiableOn ℂ (fun ζ : ℂ => Work.Parab.leftCoord.PsiC N
        (Work.FatouCoord.wMap F) (Work.FatouCoord.fatouCoordW F (1 - (2 - a))) (-ζ)) L :=
      h1.comp differentiable_neg.differentiableOn fun ζ hζ => hLsub ζ hζ
    have h3 : DifferentiableOn ℂ (fun ζ : ℂ => -Work.Parab.leftCoord.PsiC N
        (Work.FatouCoord.wMap F) (Work.FatouCoord.fatouCoordW F (1 - (2 - a))) (-ζ)) L :=
      h2.neg
    rwa [hΦdef]
  have hΦinj : Set.InjOn Φ L := by
    intro ζ1 hζ1 ζ2 hζ2 heq
    have hinj := Work.Parab.leftCoord.PsiC_injOn hGN LF.abel hmono LF.ψinj LF.ginj
    have h := hinj (hLsub ζ1 hζ1) (hLsub ζ2 hζ2) (by
      have h2 := congrArg (fun u : ℂ => -u) heq
      simp only [hΦdef] at h2
      simpa only [neg_neg] using h2)
    simpa using h
  have hΦabel : ∀ ζ ∈ L, Work.FatouCoord.wMap f ζ ∈ L →
      Φ (Work.FatouCoord.wMap f ζ) = Φ ζ + 1 := by
    intro ζ hζ hGζ
    have hx : -(Work.FatouCoord.wMap f ζ) ∈
        Work.Parab.leftCoord.EscC N (Work.FatouCoord.wMap F) := hLsub _ hGζ
    have hbnd : max (1 / r + 4) (4 / r' + 4) ≤ ‖ζ‖ := by
      rw [hLdef] at hζ
      rcases hζ with h | ⟨-, h2, -⟩
      · have hmem : ζ.re < -M₀ := h
        have h3 : -ζ.re ≤ ‖ζ‖ := by
          have h4 : |ζ.re| ≤ ‖ζ‖ := Complex.abs_re_le_norm ζ
          have h5 : -ζ.re ≤ |ζ.re| := neg_le_abs ζ.re
          linarith
        have h4 : M₀ ≤ -ζ.re := by linarith
        exact le_trans hM0b (le_trans h4 h3)
      · have h3 : M₁ ≤ ‖ζ‖ := by
          have h4 := Complex.abs_im_le_norm ζ
          linarith
        exact le_trans hM1b h3
    have hid : Work.FatouCoord.wMap F (-(Work.FatouCoord.wMap f ζ)) = -ζ :=
      wMap_F_neg_wMap hb hr' hfinv hFdef (le_max_left _ _) (le_max_right _ _) hbnd
    have habel := Work.Parab.leftCoord.PsiC_abel hGN LF.abel hx
    rw [hid] at habel
    have hmain : -Work.Parab.leftCoord.PsiC N (Work.FatouCoord.wMap F)
        (Work.FatouCoord.fatouCoordW F (1 - (2 - a))) (-(Work.FatouCoord.wMap f ζ))
        = -Work.Parab.leftCoord.PsiC N (Work.FatouCoord.wMap F)
          (Work.FatouCoord.fatouCoordW F (1 - (2 - a))) (-ζ) + 1 := by
      rw [habel]; ring
    simpa only [hΦdef] using hmain
  have hΦasym : ∀ ε > 0, ∃ R : ℝ, ∀ ζ ∈ L, R < ‖ζ‖ →
      ‖Φ ζ - (ζ - (1 - a) * Complex.log (-ζ) - 0)‖ < ε := by
    intro ε hε
    obtain ⟨R2, R2', hasym2⟩ := hasymF ε hε
    obtain ⟨Ld, hLddef⟩ : ∃ M : ℝ, M = max N (max Na (Kts / ε + R2' + 2)) + 1 := ⟨_, rfl⟩
    have hLdpos : 0 < Ld := by rw [hLddef]; positivity
    have hLdN : N ≤ Ld := by
      rw [hLddef]; linarith [le_max_left N (max Na (Kts / ε + R2' + 2))]
    have h0d : (0:ℝ) ≤ Kts / ε := div_nonneg hKtsnn hε.le
    have hLdNa : Na ≤ Ld := by
      rw [hLddef]
      linarith [le_trans (le_max_left Na (Kts / ε + R2' + 2))
        (le_max_right N (max Na (Kts / ε + R2' + 2)))]
    have hLdR : R2' ≤ Ld := by
      rw [hLddef]
      linarith [le_trans (le_max_right Na (Kts / ε + R2' + 2))
        (le_max_right N (max Na (Kts / ε + R2' + 2)))]
    obtain ⟨M2, C2, hM2pos, hC2nn, horb2⟩ :=
      Work.Parab.leftCoordData.orbit_ends_control hbF (N := Ld) hLdpos
    obtain ⟨M2', hM2def⟩ : ∃ M : ℝ, M = max (M2 + 1) (max (4 * N + 1) (R2 + 1)) := ⟨_, rfl⟩
    have hM2'lt : M2 < M2' := by
      rw [hM2def]; linarith [le_max_left (M2 + 1) (max (4 * N + 1) (R2 + 1))]
    have hM2'4N : 4 * N + 1 ≤ M2' := by
      rw [hM2def]
      linarith [le_trans (le_max_left (4 * N + 1) (R2 + 1))
        (le_max_right (M2 + 1) (max (4 * N + 1) (R2 + 1)))]
    have hM2'R2 : R2 + 1 ≤ M2' := by
      rw [hM2def]
      linarith [le_trans (le_max_right (4 * N + 1) (R2 + 1))
        (le_max_right (M2 + 1) (max (4 * N + 1) (R2 + 1)))]
    have hM2'pos : 0 < M2' := lt_trans hM2pos hM2'lt
    refine ⟨max (M₀ + 4 * M2' + 1) (Kts / ε + M2' + 2), ?_⟩
    have endsCase : ∀ ζ : ℂ, M2' < |ζ.im| → ζ.re < 3 * |ζ.im| →
        ‖Φ ζ - (ζ - (1 - a) * Complex.log (-ζ) - 0)‖ < ε := by
      intro ζ him hre
      obtain ⟨n, hn1, -, hn3, -, -⟩ := horb2 (-ζ)
        (by simp only [Complex.neg_im, abs_neg]; exact lt_trans hM2'lt him)
        (by simp only [Complex.neg_re, Complex.neg_im, abs_neg]; linarith)
      have hgood : Work.Parab.leftCoord.GoodC N (Work.FatouCoord.wMap F) (-ζ) n := by
        refine ⟨fun k hk => ?_, by linarith⟩
        have hk' := hn3 k hk
        simp only [Complex.neg_im, abs_neg] at hk'
        have h4 : N < |ζ.im| / 4 := by linarith
        linarith
      have hxEsc : -ζ ∈ Work.Parab.leftCoord.EscC N (Work.FatouCoord.wMap F) := ⟨n, hgood⟩
      have hnle : Work.Parab.leftCoord.nIdxC N (Work.FatouCoord.wMap F) (-ζ) ≤ n :=
        Work.Parab.leftCoord.nIdxC_le hgood
      have hstab := Work.Parab.leftCoord.psiC_iterate_ge hGN LF.abel hmono hxEsc hnle
      have hnorm := hasym2 (-ζ)
        (by simp only [Complex.neg_im, abs_neg]
            exact lt_trans (by linarith [hM2'R2] : R2 < M2') him)
        (by simp only [Complex.neg_re, Complex.neg_im, abs_neg]; linarith) n
        (fun k hk => by
          have hk' := hn3 k hk
          simpa only [Complex.neg_im, abs_neg] using hk')
        (by linarith [hLdNa, hn1]) (by linarith [hLdR, hn1])
      have hval : Φ ζ = -(Work.FatouCoord.fatouCoordW F (1 - (2 - a))
          ((Work.FatouCoord.wMap F)^[n] (-ζ)) - (n : ℂ)) := by
        have hPsi : Work.Parab.leftCoord.PsiC N (Work.FatouCoord.wMap F)
            (Work.FatouCoord.fatouCoordW F (1 - (2 - a))) (-ζ)
            = Work.FatouCoord.fatouCoordW F (1 - (2 - a))
              ((Work.FatouCoord.wMap F)^[n] (-ζ)) - (n : ℂ) := by
          rw [hstab]; ring
        simp only [hΦdef, hPsi]
      rw [hval]
      have hgoal : -(Work.FatouCoord.fatouCoordW F (1 - (2 - a))
              ((Work.FatouCoord.wMap F)^[n] (-ζ)) - (n : ℂ))
            - (ζ - (1 - a) * Complex.log (-ζ) - 0)
          = -(Work.FatouCoord.fatouCoordW F (1 - (2 - a))
              ((Work.FatouCoord.wMap F)^[n] (-ζ)) - (n : ℂ)
              - ((-ζ) - (1 - (2 - a)) * Complex.log (-ζ))) := by
        ring
      rw [hgoal]
      simpa only [norm_neg] using hnorm
    intro ζ hζ hR
    rw [hLdef] at hζ
    by_cases hbig : M2' < |ζ.im|
    · refine endsCase ζ hbig ?_
      rcases hζ with h | ⟨-, -, h3⟩
      · have hmem : ζ.re < -M₀ := h
        have h2 : (0:ℝ) < |ζ.im| := lt_trans hM2'pos hbig
        linarith
      · exact h3
    · have hfar : ζ.re < -M₀ := by
        by_contra hcon
        push_neg at hcon
        have hends : M₁ < |ζ.im| ∧ ζ.re < 3 * |ζ.im| := by
          rcases hζ with h | h
          · have hmem : ζ.re < -M₀ := h
            exfalso; linarith
          · exact ⟨h.2.1, h.2.2⟩
        obtain ⟨h1im, h1re⟩ := hends
        have hbnd : ‖ζ‖ ≤ M₀ + 4 * M2' := by
          have hsq : ‖ζ‖ ^ 2 = ζ.re ^ 2 + ζ.im ^ 2 := by
            rw [Complex.sq_norm, Complex.normSq_apply]; ring
          have him : |ζ.im| ≤ M2' := not_lt.mp hbig
          have him2 : ζ.im ^ 2 ≤ M2' ^ 2 := by
            rw [← sq_abs]
            exact pow_le_pow_left₀ (abs_nonneg _) him 2
          have hre_lo : -M₀ ≤ ζ.re := hcon
          have hre_hi : ζ.re ≤ 3 * M2' := by
            have h7 : 3 * |ζ.im| ≤ 3 * M2' := by linarith
            linarith
          have habsre : |ζ.re| ≤ M₀ + 3 * M2' := by
            rw [abs_le]; constructor <;> linarith
          have hre2 : ζ.re ^ 2 ≤ (M₀ + 3 * M2') ^ 2 := by
            rw [← sq_abs]
            exact pow_le_pow_left₀ (abs_nonneg _) habsre 2
          have hmain : ‖ζ‖ ^ 2 ≤ (M₀ + 4 * M2') ^ 2 := by
            have h9 : ζ.re ^ 2 + ζ.im ^ 2 ≤ (M₀ + 3 * M2') ^ 2 + M2' ^ 2 := by linarith
            have h10 : (M₀ + 3 * M2') ^ 2 + M2' ^ 2 ≤ (M₀ + 4 * M2') ^ 2 := by
              nlinarith [hM0pos, hM2'pos, mul_pos hM0pos hM2'pos]
            linarith [hsq]
          have h := sq_le_sq.mp hmain
          rw [abs_of_nonneg (norm_nonneg ζ),
            abs_of_nonneg (by linarith : (0:ℝ) ≤ M₀ + 4 * M2')] at h
          exact h
        have hRle : M₀ + 4 * M2' + 1 ≤ max (M₀ + 4 * M2' + 1) (Kts / ε + M2' + 2) :=
          le_max_left _ _
        linarith
      have hn0 : Work.Parab.leftCoord.nIdxC N (Work.FatouCoord.wMap F) (-ζ) = 0 := by
        refine Nat.le_zero.mp (Work.Parab.leftCoord.nIdxC_le ?_)
        refine Work.Parab.leftCoord.GoodC.zero ?_
        simp only [Complex.neg_re]
        linarith
      have hpsi : Work.Parab.leftCoord.PsiC N (Work.FatouCoord.wMap F)
          (Work.FatouCoord.fatouCoordW F (1 - (2 - a))) (-ζ)
          = Work.FatouCoord.fatouCoordW F (1 - (2 - a)) (-ζ) := by
        rw [Work.Parab.leftCoord.PsiC_apply, hn0]
        simp
      have hremζ : ‖Work.FatouCoord.fatouCoordW F (1 - (2 - a)) (-ζ)
          - Work.FatouCoord.approxCoord (1 - (2 - a)) (-ζ)‖ ≤ Kts / (-ζ).re :=
        hrem _ (by simp only [Complex.neg_re]; linarith)
      have hdecomp : Φ ζ - (ζ - (1 - a) * Complex.log (-ζ) - 0)
          = -(Work.FatouCoord.fatouCoordW F (1 - (2 - a)) (-ζ)
              - Work.FatouCoord.approxCoord (1 - (2 - a)) (-ζ)) := by
        simp only [hΦdef, hpsi, Work.FatouCoord.approxCoord_apply]
        ring
      have hden : 0 < (-ζ).re := by simp only [Complex.neg_re]; linarith
      have hrec : Kts / (-ζ).re < ε := by
        by_cases hKts0 : Kts = 0
        · rw [hKts0, zero_div]; exact hε
        · have hKts_pos : 0 < Kts := by
            rcases lt_or_eq_of_le hKtsnn with h | h
            · exact h
            · exact absurd h.symm hKts0
          rw [div_lt_iff₀ hden, Complex.neg_re]
          have hsq : ‖ζ‖ ^ 2 = ζ.re ^ 2 + ζ.im ^ 2 := by
            rw [Complex.sq_norm, Complex.normSq_apply]; ring
          have him : |ζ.im| ≤ M2' := not_lt.mp hbig
          have him2 : ζ.im ^ 2 ≤ M2' ^ 2 := by
            rw [← sq_abs]
            exact pow_le_pow_left₀ (abs_nonneg _) him 2
          have hRlow : Kts / ε + M2' + 2 ≤ max (M₀ + 4 * M2' + 1) (Kts / ε + M2' + 2) :=
            le_max_right _ _
          have hKε : 0 < Kts / ε := div_pos hKts_pos hε
          have h1 : Kts / ε + M2' < ‖ζ‖ :=
            lt_of_lt_of_le (by linarith : Kts / ε + M2' < Kts / ε + M2' + 2)
              (le_of_lt (lt_of_le_of_lt hRlow hR))
          have hsq2 : (Kts / ε) ^ 2 + M2' ^ 2 < ‖ζ‖ ^ 2 := by
            nlinarith [h1, hKε, hM2'pos]
          have hre2 : (Kts / ε) ^ 2 < ζ.re ^ 2 := by nlinarith [hsq, him2, hsq2]
          have habs1 : Kts / ε < |ζ.re| := by
            have h := sq_lt_sq.mp hre2
            rwa [abs_of_nonneg (le_of_lt hKε)] at h
          have hneg : ζ.re < 0 := by linarith
          rw [abs_of_neg hneg] at habs1
          rw [div_lt_iff₀ hε] at habs1
          nlinarith [habs1]
      rw [hdecomp, norm_neg]
      exact lt_of_le_of_lt hremζ hrec
  obtain ⟨ξ₁, hξ₁pos, himg⟩ := Work.Parab.leftCoordData.image_QLeft (Φ := Φ) (L := L)
    (M₀ := M₀) (M₁ := M₁) (a := 1 - a) hM0pos hM1pos
    (fun ζ hζ => by rw [hLdef]; exact Or.inl hζ) hLim_le
    hΦholo (fun ε hε => by
      obtain ⟨R, hR⟩ := hΦasym ε hε
      exact ⟨R, fun ζ hζ hRζ => by simpa only [sub_zero] using hR ζ hζ hRζ⟩)
  exact ⟨⟨Φ, L, M₀, M₁, ξ₁, 1 - a, 0, hM0pos, hM1pos, hξ₁pos, hLopen,
    (fun ζ hζ => by rw [hLdef]; exact Or.inl hζ), hLim_le, hΦholo, hΦabel, hΦinj, hΦasym,
    himg⟩⟩

end

end Work.Parab.leftCoordData
