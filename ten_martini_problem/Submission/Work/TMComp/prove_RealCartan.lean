import Mathlib
import Submission.Work.TMContract.Components
import Submission.Work.TMComp.RealCartanDefs
import Submission.Work.TMComp.RealCartan.rcPot_continuous
import Submission.Work.TMComp.RealCartan.rcPot_harmonic
import Submission.Work.TMComp.RealCartan.rcPot_le
import Submission.Work.TMComp.RealCartan.rcPot_ge
import Submission.Work.TMComp.RealCartan.rcPot_sphere_le
import Submission.Work.TMComp.RealCartan.rcMeanValue
import Submission.Work.TMComp.RealCartan.rcMaxPrincipleOn
import Submission.Work.TMComp.RealCartan.rcExistsDensityPoint
import Submission.Work.TMComp.RealCartan.rcAall_eq_iUnion
import Submission.Work.TMComp.RealCartan.rcAmn_measurable
import Submission.Work.TMComp.RealCartan.rcFrontier
import Submission.Work.TMComp.RealCartan.rcBarrier_const
import Submission.Work.TMComp.RealCartan.rcBclosed
import Submission.Work.TMComp.RealCartan.rcOfRealClosedInterior

/-!
# Component C10: the real-line Cartan lemma (`P_RealCartan`)

This file proves `Work.TMContract.P_RealCartan`, the "Cartan lemma on the real line" which
Avila--Jitomirskaya use (§2.4 of *The Ten Martini Problem*, Ann. of Math. 170 (2009)) in place
of the polar-set properties (1), (3), (4) of their source.

The proof is the barrier (comparison principle) argument described in `TMPlan/ROUTE_LEAD.md`:

* if the good set `A` has positive measure, then one of the closed pieces
  `Amn m n = {x | ∀ k ≥ n, ‖f k x‖ ≤ w k exp (-(s k/(m+1)))}` has positive measure;
* a density point `x₀` of that piece is chosen, and a closed subset
  `B = {x | |x - x₀| ≤ ρ ∧ ∀ k ≥ n, ‖f k x‖ ≤ w k exp (-(s k ε))}` of the piece with
  `volume B ≥ (1 - τ) * 2ρ` is cut out;
* the logarithmic potential `Φ = pot B R = volume B⁻¹ * ∫_B log (R/‖z - t‖)` of `B` is harmonic
  off `B`, continuous, and bounded by `cc R ρ` on the circle `‖z - x₀‖ = R` and by `CC R ρ τ`
  on the disc, while being `≥ log (R/(ρ + r))` on the interval `|x - x₀| ≤ r`;
* the harmonic barrier `W = M - (M + ε) * ((Φ - cc)/(CC - cc))` therefore satisfies
  `W ≥ M` on the circle (where `‖f k‖ ≤ w k exp (M s k)`), `W ≥ -ε` on `B` (where
  `‖f k‖ ≤ w k exp (-s k ε)`) and `W ≤ -ε/2` on `|x - x₀| ≤ r`;
* `ζ ↦ ‖f k ζ‖ exp (-s k W ζ)` satisfies the mean value inequality on the slit disc
  `Ω = ball x₀ R \ B` (locally it is the modulus of the holomorphic function
  `f k * exp (-s k H)`, `H` holomorphic with `Re H = W`), hence the maximum principle gives
  `‖f k ζ‖ ≤ w k exp (s k W ζ)` on `Ω`, and the claim follows with rate `ε/2`.

The ingredients are the lemmas in `Submission/Work/TMComp/RealCartan/`; this file assembles them.
-/

set_option maxHeartbeats 1000000

open MeasureTheory Filter Topology Set
open scoped ENNReal

namespace Work.TMComp

open Work.TMComp.RC
open Work.TMComp.RealCartan

private lemma harmAt_smul {f : ℂ → ℝ} {z : ℂ} {c : ℝ}
    (h : InnerProductSpace.HarmonicAt (c • f) z) :
    InnerProductSpace.HarmonicAt (fun w => c * f w) z := by
  refine (InnerProductSpace.harmonicAt_congr_nhds ?_).mp h
  filter_upwards with w
  simp [Pi.smul_apply, smul_eq_mul]

private lemma exp_shift {s M Wc : ℝ} :
    Real.exp (M * s) * Real.exp (-(s * Wc)) = Real.exp (s * (M - Wc)) := by
  rw [← Real.exp_add]; congr 1; ring

private lemma exp_shift2 {s e Wc : ℝ} :
    Real.exp (-(s * e)) * Real.exp (-(s * Wc)) = Real.exp (-(s * (e + Wc))) := by
  rw [← Real.exp_add]; congr 1; ring

theorem prove_RealCartan : Work.TMContract.P_RealCartan := by
  intro U hU f w s hf hw hs hbound
  by_cases h0 : volume (Aall U f w s) = 0
  · left; exact h0
  · right
    -- ### Step 1: reduce to a closed piece
    have hunion := rcAall_eq_iUnion (U := U) (f := f) (w := w) (s := s) hw hs
    have hpos : 0 < volume (Aall U f w s) := pos_iff_ne_zero.mpr h0
    obtain ⟨m, n, hmn⟩ : ∃ m n : ℕ, 0 < volume (Amn U f w s m n) := by
      by_contra hc
      push_neg at hc
      have hz : ∀ m n : ℕ, volume (Amn U f w s m n) = 0 :=
        fun m n => le_antisymm (hc m n) zero_le
      have hle : volume (Aall U f w s) ≤ ∑' m, ∑' n, volume (Amn U f w s m n) := by
        rw [hunion]
        exact le_trans (measure_iUnion_le _)
          (ENNReal.tsum_le_tsum (fun m => measure_iUnion_le _))
      rw [show (∑' m, ∑' n, volume (Amn U f w s m n)) = 0 by simp [hz]] at hle
      exact h0 (le_antisymm hle zero_le)
    obtain ⟨x₀, hx₀mem, hx₀dens⟩ :=
      rcExistsDensityPoint (rcAmn_measurable hU hf m n) hmn
    have hx₀U : (x₀ : ℂ) ∈ U := hx₀mem.1
    -- ### Step 2: the disc, the a priori bound, the constants
    obtain ⟨R, hR, hRcU⟩ : ∃ R : ℝ, 0 < R ∧ Metric.closedBall (x₀ : ℂ) R ⊆ U := by
      obtain ⟨e, he, heU⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hx₀U)
      refine ⟨e / 2, by positivity, fun z hz => heU ?_⟩
      rw [Metric.mem_ball]
      have h2 := Metric.mem_closedBall.mp hz
      linarith
    obtain ⟨M₀, hM₀⟩ := hbound (Metric.closedBall (x₀ : ℂ) R) hRcU (isCompact_closedBall _ _)
    set M : ℝ := max M₀ 0 with hMdef
    have hMnn : 0 ≤ M := le_max_right _ _
    have hMbd : ∀ k, ∀ z ∈ Metric.closedBall (x₀ : ℂ) R, ‖f k z‖ ≤ w k * Real.exp (M * s k) := by
      intro k z hz
      refine (hM₀ k z hz).trans ?_
      refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (le_of_lt (hw k))
      exact mul_le_mul_of_nonneg_right (le_max_left M₀ 0) (le_of_lt (hs k))
    set ε : ℝ := 1 / ((m : ℝ) + 1) with hεdef
    have hεpos : 0 < ε := by positivity
    set δ : ℝ := (ε / 2) / (M + ε) with hδdef
    have hδpos : 0 < δ := by positivity
    have hδle : δ ≤ 1 / 2 := by
      rw [hδdef, div_le_iff₀ (by positivity : (0:ℝ) < M + ε)]
      nlinarith [hMnn, hεpos]
    set τ : ℝ := δ / 16 with hτdef
    have hτpos : 0 < τ := by positivity
    have hτδ : τ ≤ (ε / 2) / (M + ε) / 16 := by rw [hτdef, hδdef]
    have hτhalf : τ ≤ 1 / 2 := by rw [hτdef]; nlinarith [hδle]
    have hτone : τ ≤ 1 := by linarith
    obtain ⟨ρ₀, hρ₀pos, hρ₀dens⟩ := hx₀dens τ hτpos
    -- ### Step 3: the small radius and the log threshold
    set N₁ : ℝ := (8 * (M + ε) / (7 * (ε / 2))) *
        (1 + (ε / 2) / (M + ε) / 8 + Real.log 2 + (ε / 2) / (M + ε) / 2
          - ((ε / 2) / (M + ε)) * Real.log R) with hN₁def
    set N₂ : ℝ := Real.log (4 / (3 * R)) with hN₂def
    set N : ℝ := max N₁ N₂ with hNdef
    set ρ : ℝ := min (min ρ₀ (R / 4)) (min (1 / 2) (Real.exp (-(N + 1)))) with hρdef
    have hρpos : 0 < ρ := by
      rw [hρdef]
      exact lt_min (lt_min hρ₀pos (by positivity)) (lt_min (by norm_num) (Real.exp_pos _))
    have hρle₀ : ρ ≤ ρ₀ := le_trans (min_le_left _ _) (min_le_left _ _)
    have hρR4 : ρ ≤ R / 4 := le_trans (min_le_left _ _) (min_le_right _ _)
    have hρhalf : ρ ≤ 1 / 2 := le_trans (min_le_right _ _) (min_le_left _ _)
    have hρexp : ρ ≤ Real.exp (-(N + 1)) := le_trans (min_le_right _ _) (min_le_right _ _)
    have hρR : ρ < R := by linarith [hρR4, hR]
    have hlogρ : N ≤ Real.log (1 / ρ) := by
      have hexp : Real.exp (N + 1) ≤ 1 / ρ := by
        have h := one_div_le_one_div_of_le hρpos hρexp
        rwa [Real.exp_neg, inv_eq_one_div, one_div_one_div] at h
      calc N ≤ N + 1 := by linarith
        _ = Real.log (Real.exp (N + 1)) := (Real.log_exp _).symm
        _ ≤ Real.log (1 / ρ) := Real.log_le_log (Real.exp_pos _) hexp
    have hN₁le : N₁ ≤ Real.log (1 / ρ) := le_trans (le_max_left _ _) hlogρ
    have hN₂le : N₂ ≤ Real.log (1 / ρ) := le_trans (le_max_right _ _) hlogρ
    have hlogpos : 0 ≤ Real.log (1 / ρ) := by
      apply Real.log_nonneg
      rw [le_div_iff₀ hρpos]; linarith [hρhalf]
    -- ### Step 4: the "bad" closed set B
    set B : Set ℝ := {x : ℝ | |x - x₀| ≤ ρ ∧ ∀ k ≥ n, ‖f k x‖ ≤ w k * Real.exp (-(s k * ε))}
      with hBdef
    have hBsub : B ⊆ Set.Icc (x₀ - ρ) (x₀ + ρ) := by
      intro x hx
      have h1 := hx.1
      rw [abs_le] at h1
      exact ⟨by linarith [h1.1], by linarith [h1.2]⟩
    have hsubU : ∀ x : ℝ, |x - x₀| ≤ ρ → (x : ℂ) ∈ U := by
      intro x hx
      apply hRcU
      rw [Metric.mem_closedBall, Complex.dist_eq, ← Complex.ofReal_sub]
      rw [Complex.norm_real, Real.norm_eq_abs]
      linarith [hx, hρR4, hR]
    have hBclosed : IsClosed B := rcBclosed hU hf hρpos hsubU
    have hBbdd : Bornology.IsBounded B := (Metric.isBounded_Icc (x₀ - ρ) (x₀ + ρ)).subset hBsub
    have hBvol : (1 - τ) * (2 * ρ) ≤ (volume B).toReal := by
      have hdens := hρ₀dens ρ hρpos hρle₀
      have hsub : Amn U f w s m n ∩ Set.Icc (x₀ - ρ) (x₀ + ρ) ⊆ B := by
        intro x hx
        refine ⟨?_, ?_⟩
        · have h1 := hx.2
          rw [abs_le]
          exact ⟨by linarith [h1.1], by linarith [h1.2]⟩
        · intro k hk
          have h2 := hx.1.2 k hk
          rw [hεdef]
          convert h2 using 3
          ring
      refine hdens.trans (ENNReal.toReal_mono ?_ (measure_mono hsub))
      exact ne_top_of_le_ne_top (by simp) (measure_mono hBsub)
    have hBvolpos : 0 < (volume B).toReal := by
      have h1 : 0 < (1 - τ) * (2 * ρ) := by nlinarith [hτone, hρpos]
      linarith [hBvol]
    -- ### Step 5: the potential and its bounds
    set Φ : ℂ → ℝ := fun z => (volume B).toReal⁻¹ * logPot B R z with hΦdef
    have hΦle : ∀ z : ℂ, Φ z ≤ CC R ρ τ := by
      intro z
      have hle := rcPot_le (R := R) hBsub hρpos hρhalf z
      have hL : 0 ≤ Real.log (1 / ρ) + 1 := by linarith
      have h2 : (2 * ρ) / (volume B).toReal ≤ 1 / (1 - τ) := by
        rw [div_le_div_iff₀ hBvolpos (by linarith : (0:ℝ) < 1 - τ)]
        linarith [hBvol]
      rw [CC]
      change (volume B).toReal⁻¹ * logPot B R z ≤ Real.log R + (1 / (1 - τ)) * (Real.log (1 / ρ) + 1)
      have key : (volume B).toReal⁻¹ * logPot B R z
          ≤ Real.log R + (2 * ρ) / (volume B).toReal * (Real.log (1 / ρ) + 1) := by
        have hBne : (volume B).toReal ≠ 0 := ne_of_gt hBvolpos
        calc (volume B).toReal⁻¹ * logPot B R z
            ≤ (volume B).toReal⁻¹ * ((volume B).toReal * Real.log R
                + 2 * ρ * (Real.log (1 / ρ) + 1)) :=
              mul_le_mul_of_nonneg_left hle (by positivity)
          _ = Real.log R + (2 * ρ) / (volume B).toReal * (Real.log (1 / ρ) + 1) := by
              rw [div_eq_mul_inv, mul_add]
              rw [← mul_assoc, inv_mul_cancel₀ hBne, one_mul]
              ring
      refine key.trans ?_
      have h3 := mul_le_mul_of_nonneg_right h2 hL
      linarith [h3]
    have hΦsphere : ∀ z ∈ Metric.sphere (x₀ : ℂ) R, Φ z ≤ cc R ρ := by
      intro z hz
      have hle := rcPot_sphere_le (R := R) hBsub hρpos hρR hz
      rw [cc]
      change (volume B).toReal⁻¹ * logPot B R z ≤ Real.log (R / (R - ρ))
      rw [inv_mul_le_iff₀ hBvolpos]
      exact hle
    have hΦge : ∀ x : ℝ, |x - x₀| ≤ ρ / 2 → Real.log (R / (ρ + ρ / 2)) ≤ Φ (x : ℂ) := by
      intro x hx
      have hle := rcPot_ge (R := R) hBsub hρpos (by linarith) hR hx
      change Real.log (R / (ρ + ρ / 2)) ≤ (volume B).toReal⁻¹ * logPot B R (x : ℂ)
      rw [le_inv_mul_iff₀ hBvolpos]
      linarith [hle]
    -- ### Step 6: the barrier, its harmonicity and continuity
    set W : ℂ → ℝ := barrier Φ M ε (cc R ρ) (CC R ρ τ) with hWdef
    have hΦcont : Continuous Φ := by
      change Continuous (fun z => (volume B).toReal⁻¹ * logPot B R z)
      exact (rcPot_continuous hBbdd R).const_mul _
    have hWcont : Continuous W := by
      rw [hWdef]
      show Continuous (fun z => M - (M + ε) * ((Φ z - cc R ρ) / (CC R ρ τ - cc R ρ)))
      exact continuous_const.sub (continuous_const.mul ((hΦcont.sub continuous_const).div_const _))
    have hcc_lt_CC : cc R ρ < CC R ρ τ := by
      have h7 : Real.log (1 / (R - ρ)) ≤ Real.log (1 / ρ) := by
        apply Real.log_le_log (by positivity)
        rw [div_le_div_iff₀ (by linarith : (0:ℝ) < R - ρ) hρpos]
        linarith [hρR4, hR]
      have hmain : Real.log (1 / (R - ρ)) < (1 / (1 - τ)) * (Real.log (1 / ρ) + 1) := by
        have h9 : 1 ≤ 1 / (1 - τ) := by rw [le_div_iff₀ (by linarith)]; linarith
        have h10 : Real.log (1 / ρ) + 1 ≤ (1 / (1 - τ)) * (Real.log (1 / ρ) + 1) := by
          nlinarith [hlogpos]
        linarith
      rw [cc, CC, Real.log_div (by linarith : R ≠ 0) (by linarith : R - ρ ≠ 0)]
      have h11 : Real.log (R - ρ) = -Real.log (1 / (R - ρ)) := by
        rw [one_div, Real.log_inv, neg_neg]
      linarith [h11, hmain]
    have hBcclosed : IsClosed (Complex.ofReal '' B) := (rcOfRealClosedInterior hBclosed).1
    have hBcint : interior (Complex.ofReal '' B) = ∅ := (rcOfRealClosedInterior hBclosed).2
    set Ω : Set ℂ := Metric.ball (x₀ : ℂ) R \ (Complex.ofReal '' B) with hΩdef
    have hΩopen : IsOpen Ω := Metric.isOpen_ball.sdiff hBcclosed
    have hΩbdd : Bornology.IsBounded Ω := Metric.isBounded_ball.subset sdiff_subset
    have hBcsub : (Complex.ofReal '' B) ⊆ Metric.ball (x₀ : ℂ) R := by
      rintro z ⟨t, ht, rfl⟩
      rw [Metric.mem_ball, Complex.dist_eq, ← Complex.ofReal_sub]
      rw [Complex.norm_real, Real.norm_eq_abs]
      have h1 : |t - x₀| ≤ ρ := ht.1
      have h2 : t - x₀ ≤ ρ := (abs_le.mp h1).2
      linarith [h2, hρR4, hR]
    have hfront : frontier Ω = Metric.sphere (x₀ : ℂ) R ∪ (Complex.ofReal '' B) :=
      rcFrontier hR hBcclosed hBcsub hBcint
    have hΩsubU : Ω ⊆ U := fun z hz => by
      rw [hΩdef] at hz
      exact hRcU (Metric.ball_subset_closedBall hz.1)
    have hlogharm : InnerProductSpace.HarmonicOnNhd (logPot B R) Ω :=
      fun z hz => rcPot_harmonic hBclosed R hz.2
    have hΦharm : InnerProductSpace.HarmonicOnNhd Φ Ω := by
      intro z hz
      have h := (hlogharm z hz).const_smul (c := (volume B).toReal⁻¹)
      exact harmAt_smul h
    have hWharm : InnerProductSpace.HarmonicOnNhd W Ω := by
      have h1 : InnerProductSpace.HarmonicOnNhd
          (fun z => (Φ z - cc R ρ) / (CC R ρ τ - cc R ρ)) Ω := by
        have hsub := hΦharm.sub (InnerProductSpace.harmonicOnNhd_const (cc R ρ))
        have h := hsub.const_smul (c := (CC R ρ τ - cc R ρ)⁻¹)
        intro z hz
        have h2 := harmAt_smul (h z hz)
        refine (InnerProductSpace.harmonicAt_congr_nhds ?_).mp h2
        filter_upwards with w
        simp only [Pi.sub_apply, div_eq_mul_inv, mul_comm]
      have h2 : InnerProductSpace.HarmonicOnNhd
          (fun z => M - (M + ε) * ((Φ z - cc R ρ) / (CC R ρ τ - cc R ρ))) Ω := by
        have h := h1.const_smul (c := -(M + ε))
        have hneg : InnerProductSpace.HarmonicOnNhd
            (fun z => -((-(M + ε)) * ((Φ z - cc R ρ) / (CC R ρ τ - cc R ρ)))) Ω := h.neg
        have hconst : InnerProductSpace.HarmonicOnNhd (fun _ : ℂ => M) Ω :=
          InnerProductSpace.harmonicOnNhd_const M
        have hh := hconst.sub hneg
        intro z hz
        refine (InnerProductSpace.harmonicAt_congr_nhds ?_).mp (hh z hz)
        filter_upwards with w
        simp only [Pi.sub_apply, Pi.neg_apply]
        ring
      rw [hWdef]
      show InnerProductSpace.HarmonicOnNhd
        (fun z => M - (M + ε) * ((Φ z - cc R ρ) / (CC R ρ τ - cc R ρ))) Ω
      exact h2
    -- ### Step 7: the maximum principle
    set V : ℕ → ℂ → ℝ := fun k z => ‖f k z‖ * Real.exp (-(s k * W z)) with hVdef
    have hclsub : closure Ω ⊆ U := by
      have h1 : closure Ω ⊆ closure (Metric.ball (x₀ : ℂ) R) := closure_mono sdiff_subset
      rw [closure_ball _ (ne_of_gt hR)] at h1
      exact fun z hz => hRcU (h1 hz)
    have hVcont : ∀ k, ContinuousOn (V k) (closure Ω) := by
      intro k
      have hfk : ContinuousOn (fun z => ‖f k z‖) (closure Ω) :=
        ((hf k).continuousOn.norm).mono hclsub
      have hexp : ContinuousOn (fun z => Real.exp (-(s k * W z))) (closure Ω) :=
        Real.continuous_exp.comp_continuousOn (by
          simpa only [neg_mul] using ContinuousOn.const_mul hWcont.continuousOn (-(s k)))
      have hh : ContinuousOn (fun z => ‖f k z‖ * Real.exp (-(s k * W z))) (closure Ω) :=
        (hfk.mul hexp).congr (fun z _ => rfl)
      rw [hVdef]
      exact hh
    have hVmean : ∀ k, ∀ z ∈ Ω, ∀ r : ℝ, 0 < r → Metric.closedBall z r ⊆ Ω →
        V k z ≤ Real.circleAverage (V k) z r := by
      intro k z hz r hr hrU
      by_cases hzf : f k z = 0
      · have hzero : V k z = 0 := by simp [hVdef, hzf]
        rw [hzero]
        refine Real.circleAverage_nonneg_of_nonneg (fun ζ _ => ?_)
        simp only [hVdef]
        positivity
      · have h1 : ‖f k z‖ * Real.exp (-(s k * W z)) ≤
            Real.circleAverage (fun ζ => ‖f k ζ‖ * Real.exp (-(s k * W ζ))) z r :=
          rcMeanValue hΩopen hWharm (((hf k).analyticOnNhd hU).mono hΩsubU) (s k) hz hzf hr hrU
        rw [hVdef]
        exact h1
    have hVbd : ∀ k ≥ n, ∀ ζ ∈ frontier Ω, V k ζ ≤ w k := by
      intro k hk ζ hζ
      rw [hfront] at hζ
      rcases hζ with hζ | hζ
      · -- on the sphere
        have hzdist : dist ζ (x₀ : ℂ) = R := Metric.mem_sphere.mp hζ
        have hzW : M ≤ W ζ := by
          rw [hWdef]
          show M ≤ M - (M + ε) * ((Φ ζ - cc R ρ) / (CC R ρ τ - cc R ρ))
          have h1 : Φ ζ - cc R ρ ≤ 0 := sub_nonpos.mpr (hΦsphere ζ hζ)
          have h2 : 0 < CC R ρ τ - cc R ρ := sub_pos.mpr hcc_lt_CC
          have h3 : (Φ ζ - cc R ρ) / (CC R ρ τ - cc R ρ) ≤ 0 :=
            div_nonpos_of_nonpos_of_nonneg h1 h2.le
          nlinarith [hεpos, h2, h3, hMnn]
        calc V k ζ = ‖f k ζ‖ * Real.exp (-(s k * W ζ)) := rfl
          _ ≤ (w k * Real.exp (M * s k)) * Real.exp (-(s k * W ζ)) :=
              mul_le_mul_of_nonneg_right
                (hMbd k ζ (Metric.mem_closedBall.mpr (le_of_eq hzdist))) (Real.exp_pos _).le
          _ = w k * Real.exp (s k * (M - W ζ)) := by
              rw [mul_assoc, exp_shift]
          _ ≤ w k * 1 := by
              refine mul_le_mul_of_nonneg_left ?_ (le_of_lt (hw k))
              rw [Real.exp_le_one_iff]
              nlinarith [hs k]
          _ = w k := mul_one _
      · -- on B
        rcases hζ with ⟨t, ht, rfl⟩
        have hconstr : ‖f k t‖ ≤ w k * Real.exp (-(s k * ε)) := by
          rw [hBdef] at ht
          exact ht.2 k hk
        have hzX : -ε ≤ W (t : ℂ) := by
          rw [hWdef]
          show -ε ≤ M - (M + ε) * ((Φ (t:ℂ) - cc R ρ) / (CC R ρ τ - cc R ρ))
          have h2 : 0 < CC R ρ τ - cc R ρ := sub_pos.mpr hcc_lt_CC
          have h1 : (Φ (t:ℂ) - cc R ρ) / (CC R ρ τ - cc R ρ) ≤ 1 := by
            rw [div_le_one h2]
            linarith [hΦle (t : ℂ)]
          nlinarith [h1, hεpos, h2, hMnn]
        calc V k (t : ℂ) = ‖f k t‖ * Real.exp (-(s k * W (t:ℂ))) := rfl
          _ ≤ (w k * Real.exp (-(s k * ε))) * Real.exp (-(s k * W (t:ℂ))) :=
              mul_le_mul_of_nonneg_right hconstr (Real.exp_pos _).le
          _ = w k * Real.exp (-(s k * (ε + W (t:ℂ)))) := by
              rw [mul_assoc, exp_shift2]
          _ ≤ w k * 1 := by
              refine mul_le_mul_of_nonneg_left ?_ (le_of_lt (hw k))
              rw [Real.exp_le_one_iff]
              nlinarith [hs k, hzX]
          _ = w k := mul_one _
    have hVle : ∀ k ≥ n, ∀ z ∈ Ω, V k z ≤ w k := by
      intro k hk
      exact rcMaxPrincipleOn hΩopen hΩbdd (hVcont k) (hVmean k) (hVbd k hk)
    -- ### Step 8: conclusion
    refine ⟨x₀ - ρ / 2, x₀ + ρ / 2, by linarith, ?_⟩
    intro x hx
    have hxRn : |x - x₀| < ρ / 2 := by
      rw [Set.mem_Ioo] at hx
      rw [abs_lt]
      exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
    have hxR : |x - x₀| ≤ ρ := by linarith [hxRn, hρpos]
    refine ⟨hsubU x hxR, ε / 2, by positivity, ?_⟩
    rw [Filter.eventually_atTop]
    refine ⟨n, fun k hk => ?_⟩
    by_cases hxB : x ∈ B
    · have hconstr : ‖f k x‖ ≤ w k * Real.exp (-(s k * ε)) := by
        exact hxB.2 k hk
      refine hconstr.trans ?_
      refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (le_of_lt (hw k))
      nlinarith [hs k, hεpos]
    · have hxΩ : (x : ℂ) ∈ Ω := by
        rw [hΩdef, Set.mem_diff]
        refine ⟨?_, ?_⟩
        · rw [Metric.mem_ball, Complex.dist_eq, ← Complex.ofReal_sub]
          rw [Complex.norm_real, Real.norm_eq_abs]
          linarith [hxRn, hρR4, hR]
        · intro hmem
          rcases hmem with ⟨t, ht, htx⟩
          have htx' : t = x := Complex.ofReal_injective htx
          rw [htx'] at ht
          exact hxB ht
      have hVb := hVle k hk (x : ℂ) hxΩ
      have hWx : W x ≤ -(ε / 2) := by
        refine rcBarrier_const hR hρpos hρR4 (by linarith) (by linarith) (by linarith) hMnn hεpos
          hτpos hτδ ?_ (hΦge x (le_of_lt hxRn))
        refine max_le ?_ ?_
        · simpa only [hN₁def] using hN₁le
        · have h1 : Real.log (1 / (R - ρ)) ≤ Real.log (4 / (3 * R)) := by
            apply Real.log_le_log (by positivity)
            have h2 : 3 * R / 4 ≤ R - ρ := by linarith [hρR4, hR]
            have h3 : 0 < 3 * R / 4 := by linarith
            calc 1 / (R - ρ) ≤ 1 / (3 * R / 4) := one_div_le_one_div_of_le h3 h2
              _ = 4 / (3 * R) := by field_simp
          simpa only [hN₂def] using h1.trans hN₂le
      have h2 : V k x ≤ w k := hVb
      change ‖f k x‖ * Real.exp (-(s k * W x)) ≤ w k at h2
      have h3 : ‖f k x‖ ≤ w k * Real.exp (s k * W x) := by
        calc ‖f k x‖ = ‖f k x‖ * Real.exp (-(s k * W x)) * Real.exp (s k * W x) := by
              rw [mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, mul_one]
          _ ≤ w k * Real.exp (s k * W x) :=
              mul_le_mul_of_nonneg_right h2 (Real.exp_pos _).le
      refine h3.trans ?_
      refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (le_of_lt (hw k))
      nlinarith [hs k, hWx]


end Work.TMComp
