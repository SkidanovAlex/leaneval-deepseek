/-
Copyright: the formalization team of the Vinogradov mean value theorem project.
-/
import Submission.Vinogradov.LocalisedDecoupling

/-!
# Corollary 3.7 with a prescribed ball radius (`CurveDecLocR`)

The localised decoupling inequality `CurveDecLoc l D m lam A C` (`BallTent.lean`, proved in
`LocalisedDecoupling.lean`) is stated for **every** ball of radius `R ≥ m^l`.  Its proof uses a
bump `ψ_B` adapted to `B`, whose Fourier support has radius `σ ≤ 1/R`; the hypothesis `hρl` of
`curveDecLoc_of_curveDec` (`2^{l+2} ≤ ρ · lam^l`) is a *worst-case* form of the requirement that
the inradius `ρ(lam/(2m))^l` of the canonical plate dominate `σ ≤ 1/m^l`.

That worst case is too strong for the application to the **reparametrised projected curve** of
GLYZ §3.4: there the plate of a σ-piece has inradius `≈ c_L c^l (σ-plate scale)^l`, and `c = 2^{-m}`
is the (tiny) reparametrisation scale, so `ρ = c_L c^l` and the condition `2^{l+2} ≤ ρ lam^l`
would force the plate enlargement `lam ≳ 2^m` — which is incompatible with the tower, whose
enlargement is bounded by the *fixed* model enlargement (`hΛ₁ : Λ(1+εt)Ctube l ≤ Λ₁`).

The correct requirement is `inradius ≥ 4/R` (with the **actual** ball radius `R`), which for the
projected curve is `c_L(lam/2)^l 2^{k-l+1} ≳ 1` — a fixed condition.  This module provides the
variant

  `CurveDecLocR l D m lam A R₀ C` — the localised inequality for balls of radius `≥ R₀`,

with the correspondingly weakened hypothesis `hρlR : 2^{l+2} ≤ ρ · R₀ · lam^l`, together with
`curveDecLocR_of_curveDec` (the analogue of `curveDecLoc_of_curveDec`).
-/

noncomputable section
open MeasureTheory Complex Classical Filter
open scoped Real BigOperators Topology RealInnerProductSpace ENNReal NNReal

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.style.emptyLine false
set_option linter.unusedVariables false
set_option maxHeartbeats 4000000

namespace Submission.Vinogradov

/-- **The localised decoupling inequality for balls of radius `≥ R₀`** (a strengthening of the
hypothesis of `CurveDecLoc`, which is the case `R₀ = m^l`). -/
def CurveDecLocR (l : ℕ) (D : ℕ → ℝ → E l) (m : ℕ) (lam A R₀ : ℝ) (C : ℝ≥0∞) : Prop :=
  ∀ (f : Fin m → E l → ℂ),
    (∀ j, IsFourierRep l (curvePlate l D (lam / (2 * m)) (pieceCenter m j)) (f j)) →
    ∀ (c : E l) (R : ℝ), R₀ ≤ R →
      ballAvg (plExp l) c R (fun x => ∑ j, f j x)
        ≤ C ^ (plExp l)
          * (∑ j : Fin m,
              (∫⁻ x, (‖f j x‖₊ : ℝ≥0∞) ^ (plExp l) * ballTent l A c R x) ^ (2 / plExp l))
            ^ (plExp l / 2)

lemma CurveDecLocR.mono {l : ℕ} {D : ℕ → ℝ → E l} {m : ℕ} {lam A R₀ : ℝ} {C C' : ℝ≥0∞}
    (h : C ≤ C') (hD : CurveDecLocR l D m lam A R₀ C) : CurveDecLocR l D m lam A R₀ C' :=
  fun f hf c R hR =>
    (hD f hf c R hR).trans (mul_le_mul' (ENNReal.rpow_le_rpow h (plExp_nonneg l)) le_rfl)

lemma isFourierRep_mul_ball_bumpR {l : ℕ} (hl : 1 ≤ l) (D : ℕ → ℝ → E l) {m : ℕ} (hm : 1 ≤ m)
    {lam lam' ρ : ℝ} (hlam : 1 ≤ lam) (hρ : 0 < ρ) {R₀ : ℝ}
    (hρlR : (2 : ℝ) ^ (l + 2) ≤ ρ * (R₀ / (m : ℝ) ^ l) * lam ^ l)
    (hrad : ∀ j : Fin m, Metric.ball (D 0 (pieceCenter m j)) (ρ * (lam / (2 * m)) ^ l)
              ⊆ curvePlate l D (lam / (2 * m)) (pieceCenter m j))
    (hlam' : 2 * lam ≤ lam') {j : Fin m} {σ : ℝ} (hσR : σ * R₀ ≤ 1) (hR : (m : ℝ) ^ l ≤ R₀)
    {ψ : E l → ℂ} (hψ : IsFourierRep l (Metric.closedBall 0 σ) ψ)
    {f : E l → ℂ} (hf : IsFourierRep l (curvePlate l D (lam / (2 * m)) (pieceCenter m j)) f) :
    IsFourierRep l (curvePlate l D (lam' / (2 * m)) (pieceCenter m j))
      (fun x => f x * ψ x) := by
  have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hmpos : (0 : ℝ) < (m : ℝ) := lt_of_lt_of_le zero_lt_one hm1
  have hRpos : (0 : ℝ) < R₀ := lt_of_lt_of_le (pow_pos hmpos l) hR
  have hlampos : 0 < lam := lt_of_lt_of_le zero_lt_one hlam
  have hε' : (1 : ℝ) ≤ lam' / lam - 1 := by
    rw [le_sub_iff_add_le, one_add_one_eq_two]
    exact (le_div_iff₀ hlampos).mpr hlam'
  have hσle : σ ≤ 1 / R₀ := by
    rw [le_div_iff₀ hRpos]; linarith [hσR]
  have hbase : (2 : ℝ) / R₀ ≤ (ρ / 2) * (lam / (2 * m)) ^ l := by
    have h1 : (ρ / 2) * (lam / (2 * m)) ^ l * R₀
        = ρ * (R₀ / (m : ℝ) ^ l) * lam ^ l / 2 ^ (l + 1) := by
      rw [div_pow]
      field_simp
      ring
    rw [div_le_iff₀ hRpos, h1, le_div_iff₀ (by positivity : (0 : ℝ) < 2 ^ (l + 1))]
    have h2 : (2 : ℝ) * 2 ^ (l + 1) = 2 ^ (l + 2) := by ring
    rw [h2]
    exact hρlR
  refine (hf.mul hψ).mono ?_
  rintro z ⟨u, hu, v, hv, rfl⟩
  have hv' : ‖v‖ ≤ σ := by
    rw [Metric.mem_closedBall, dist_eq_norm, sub_zero] at hv
    exact hv
  have hstrict' : ‖v‖ < (lam' / lam - 1) * (ρ / 2 * (lam / (2 * m)) ^ l) := by
    have hstep : (2 : ℝ) / R₀
        ≤ (lam' / lam - 1) * ((ρ / 2) * (lam / (2 * m)) ^ l) := by
      calc (2 : ℝ) / R₀ ≤ 1 * ((ρ / 2) * (lam / (2 * m)) ^ l) := by
            rw [one_mul]; exact hbase
        _ ≤ (lam' / lam - 1) * ((ρ / 2) * (lam / (2 * m)) ^ l) :=
            mul_le_mul_of_nonneg_right hε' (by positivity)
    have h2 : 1 / R₀ < 2 / R₀ := by
      rw [div_lt_div_iff_of_pos_right hRpos]
      norm_num
    linarith [hσle]
  have hprev := curvePlate_add_ball_subset_of (D := D) (δ := lam / (2 * m))
    (t := pieceCenter m j) (ρ := ρ / 2 * (lam / (2 * m)) ^ l) (ε := lam' / lam - 1)
    (by positivity) ?_ hu hstrict'
  · convert hprev using 2
    field_simp
    ring
  · refine (Metric.ball_subset_ball ?_).trans (hrad j)
    have hd : 0 < (lam / (2 * m)) ^ l := by positivity
    nlinarith [hρ.le, hd]


theorem curveDecLocR_of_curveDec {l : ℕ} (hl : 1 ≤ l) (D : ℕ → ℝ → E l) {m : ℕ} (hm : 1 ≤ m)
    {lam lam' ρ A : ℝ} (hlam : 1 ≤ lam) (hρ : 0 < ρ) {R₀ : ℝ} (hR0 : (m : ℝ) ^ l ≤ R₀)
    (hρlR : (2 : ℝ) ^ (l + 2) ≤ ρ * (R₀ / (m : ℝ) ^ l) * lam ^ l)
    (hrad : ∀ j : Fin m, Metric.ball (D 0 (pieceCenter m j)) (ρ * (lam / (2 * m)) ^ l)
              ⊆ curvePlate l D (lam / (2 * m)) (pieceCenter m j))
    (hA : 0 ≤ A) {C : ℝ≥0∞} (hdec : CurveDec l D m lam' C) (hlam' : 2 * lam ≤ lam') :
    ∃ K : ℝ≥0∞, CurveDecLocR l D m lam A R₀ (C * K) := by
  have hp : 0 < plExp l := by
    rw [plExp]
    have hl1 : (1 : ℝ) ≤ l := by exact_mod_cast hl
    nlinarith
  have hpnn : 0 ≤ plExp l := hp.le
  have hpA : 0 ≤ A / plExp l := div_nonneg hA hpnn
  obtain ⟨Cb, hCb, hbump0⟩ :=
    Commons.Analysis.Fourier.exists_ball_bump_uniform l hl (A / plExp l) hpA
  refine ⟨ENNReal.ofReal (2 * Cb), ?_⟩
  intro f hf c R hR
  have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hmpos : (0 : ℝ) < (m : ℝ) := lt_of_lt_of_le zero_lt_one hm1
  have hR1 : (1 : ℝ) ≤ R := le_trans (le_trans (one_le_pow₀ hm1) hR0) hR
  have hRpos : (0 : ℝ) < R := lt_of_lt_of_le zero_lt_one hR1
  obtain ⟨σ, ψ₀, Φ, hσpos, hσR, hΦmeas, hΦint, hΦsupp, hrep, hlow, hdecay⟩ := hbump0 R hR1
  obtain ⟨ψ, hψclass, hψlow, hψdec⟩ :=
    ball_bump_translate (c := c) hR1 hpA hCb.le hσpos hΦmeas hΦint hΦsupp hrep hlow hdecay
  set g : E l → ℂ := fun x => ∑ j, f j x with hg
  set h : E l → ℂ := fun x => ∑ j, f j x * ψ x with hh
  have hgh : ∀ x, h x = g x * ψ x := by
    intro x
    simp only [hh, hg, Finset.sum_mul]
  -- classes of the multiplied pieces
  have hclass : ∀ j : Fin m, IsFourierRep l (curvePlate l D (lam' / (2 * m)) (pieceCenter m j))
      (fun x => f j x * ψ x) := fun j =>
    isFourierRep_mul_ball_bumpR hl D hm hlam hρ hρlR hrad hlam' (j := j)
      (σ := σ) (R₀ := R₀)
      (le_trans (mul_le_mul_of_nonneg_left hR hσpos.le) hσR) hR0 hψclass (hf j)
  -- the decoupling inequality
  have hdec' : lpNorm l (pE l) h
      ≤ C * l2Norm (fun j => lpNorm l (pE l) (fun x => f j x * ψ x)) := by
    have h1 := hdec (fun j => fun x => f j x * ψ x) hclass
    simpa only [hh] using h1
  have hdec2 : (lpNorm l (pE l) h) ^ (plExp l)
      ≤ C ^ (plExp l)
        * (l2Norm (fun j => lpNorm l (pE l) (fun x => f j x * ψ x))) ^ (plExp l) := by
    refine (ENNReal.rpow_le_rpow hdec' hpnn).trans ?_
    rw [ENNReal.mul_rpow_of_nonneg _ _ hpnn]
  -- the localising step
  have hpoint : ∀ x ∈ Metric.ball c R,
      (‖g x‖₊ : ℝ≥0∞) ^ (plExp l) ≤ 2 ^ (plExp l) * (‖h x‖₊ : ℝ≥0∞) ^ (plExp l) := by
    intro x hx
    have hx' : ‖x - c‖ ≤ R := by
      rw [Metric.mem_ball, dist_eq_norm] at hx
      exact hx.le
    have hψ1 : (1 / 2 : ℝ) ≤ ‖ψ x‖ := hψlow x hx'
    have h1 : ‖g x‖ ≤ 2 * ‖h x‖ := by
      have h2 : ‖h x‖ = ‖g x‖ * ‖ψ x‖ := by rw [hgh x, norm_mul]
      have h3 : ‖g x‖ * (1 / 2 : ℝ) ≤ ‖g x‖ * ‖ψ x‖ :=
        mul_le_mul_of_nonneg_left hψ1 (norm_nonneg _)
      nlinarith [norm_nonneg (g x), norm_nonneg (h x)]
    have h2 : (‖g x‖₊ : ℝ≥0∞) ≤ 2 * (‖h x‖₊ : ℝ≥0∞) := by
      have h3 : (‖g x‖₊ : NNReal) ≤ (2 : NNReal) * ‖h x‖₊ := by
        exact_mod_cast h1
      calc (‖g x‖₊ : ℝ≥0∞) = ((‖g x‖₊ : NNReal) : ℝ≥0∞) := rfl
        _ ≤ (((2 : NNReal) * ‖h x‖₊ : NNReal) : ℝ≥0∞) := by exact_mod_cast h3
        _ = 2 * (‖h x‖₊ : ℝ≥0∞) := by rw [ENNReal.coe_mul]; norm_num
    calc (‖g x‖₊ : ℝ≥0∞) ^ (plExp l) ≤ (2 * (‖h x‖₊ : ℝ≥0∞)) ^ (plExp l) :=
          ENNReal.rpow_le_rpow h2 hpnn
      _ = 2 ^ (plExp l) * (‖h x‖₊ : ℝ≥0∞) ^ (plExp l) :=
          ENNReal.mul_rpow_of_nonneg _ _ hpnn
  have hlocal := ballAvg_le_of_two_mul (p := plExp l) hpoint
  have hlp := lintegral_nnnorm_rpow_eq_lpNorm_pow l hl h
  -- the per-piece bound
  have hj : ∀ j : Fin m, (lpNorm l (pE l) (fun x => f j x * ψ x)) ^ (plExp l)
      ≤ ((ENNReal.ofReal Cb) ^ (plExp l) * ENNReal.ofReal (volume (Metric.ball c R)).toReal)
          * tentNorm l A c R (f j) := fun j =>
    lpNorm_mul_le_of_decay hl hCb hRpos (fun x => hψdec x) (f := f j)
  -- assembling
  have hsum2 : (∑ j : Fin m, (lpNorm l (pE l) (fun x => f j x * ψ x)) ^ (2 : ℝ))
      ≤ (((ENNReal.ofReal Cb) ^ (plExp l) * ENNReal.ofReal (volume (Metric.ball c R)).toReal)
          ^ (2 / plExp l)) * ∑ j : Fin m, (tentNorm l A c R (f j)) ^ (2 / plExp l) := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun j _ => ?_
    calc (lpNorm l (pE l) (fun x => f j x * ψ x)) ^ (2 : ℝ)
        = ((lpNorm l (pE l) (fun x => f j x * ψ x)) ^ (plExp l)) ^ (2 / plExp l) := by
          rw [← ENNReal.rpow_mul]
          congr 1
          field_simp
      _ ≤ (((ENNReal.ofReal Cb) ^ (plExp l) * ENNReal.ofReal (volume (Metric.ball c R)).toReal)
            * tentNorm l A c R (f j)) ^ (2 / plExp l) :=
          ENNReal.rpow_le_rpow (hj j) (by positivity)
      _ = ((ENNReal.ofReal Cb) ^ (plExp l) * ENNReal.ofReal (volume (Metric.ball c R)).toReal)
            ^ (2 / plExp l) * (tentNorm l A c R (f j)) ^ (2 / plExp l) :=
          ENNReal.mul_rpow_of_nonneg _ _ (by positivity)
  have hl2 : (l2Norm (fun j => lpNorm l (pE l) (fun x => f j x * ψ x))) ^ (plExp l)
      = (∑ j : Fin m, (lpNorm l (pE l) (fun x => f j x * ψ x)) ^ (2 : ℝ))
          ^ (plExp l / 2) := by
    rw [l2Norm, ← ENNReal.rpow_mul]
    congr 1
    ring
  have hKpow : (((ENNReal.ofReal Cb) ^ (plExp l)
        * ENNReal.ofReal (volume (Metric.ball c R)).toReal) ^ (2 / plExp l))
      ^ (plExp l / 2)
      = (ENNReal.ofReal Cb) ^ (plExp l) * ENNReal.ofReal (volume (Metric.ball c R)).toReal := by
    rw [← ENNReal.rpow_mul]
    rw [show (2 / plExp l) * (plExp l / 2) = 1 by field_simp]
    rw [ENNReal.rpow_one]
  have hBpos : ENNReal.ofReal (volume (Metric.ball c R)).toReal ≠ 0 := by
    rw [ENNReal.ofReal_ne_zero_iff]
    exact ENNReal.toReal_pos (Metric.measure_ball_pos (μ := volume) c hRpos).ne'
      measure_ball_lt_top.ne
  have hBtop : ENNReal.ofReal (volume (Metric.ball c R)).toReal ≠ ⊤ := ENNReal.ofReal_ne_top
  have hcancel : (ENNReal.ofReal (volume (Metric.ball c R)).toReal)⁻¹
        * ((ENNReal.ofReal Cb) ^ (plExp l) * ENNReal.ofReal (volume (Metric.ball c R)).toReal)
      = (ENNReal.ofReal Cb) ^ (plExp l) := by
    rw [mul_comm ((ENNReal.ofReal Cb) ^ (plExp l))
      (ENNReal.ofReal (volume (Metric.ball c R)).toReal),
      ← mul_assoc, ENNReal.inv_mul_cancel hBpos hBtop, one_mul]
  have hconst : 2 ^ (plExp l) * ((ENNReal.ofReal Cb) ^ (plExp l) * C ^ (plExp l))
      ≤ (C * ENNReal.ofReal (2 * Cb)) ^ (plExp l) := by
    have h1 : (C * ENNReal.ofReal (2 * Cb)) ^ (plExp l)
        = C ^ (plExp l) * (ENNReal.ofReal (2 * Cb)) ^ (plExp l) :=
      ENNReal.mul_rpow_of_nonneg _ _ hpnn
    have h2 : (ENNReal.ofReal (2 * Cb)) ^ (plExp l)
        = (ENNReal.ofReal 2) ^ (plExp l) * (ENNReal.ofReal Cb) ^ (plExp l) := by
      rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2),
        ENNReal.mul_rpow_of_nonneg _ _ hpnn]
    have h3 : (ENNReal.ofReal 2 : ℝ≥0∞) = 2 := by norm_num
    rw [h1, h2, h3]
    exact le_of_eq (by ac_rfl)
  calc ballAvg (plExp l) c R g
      ≤ (ENNReal.ofReal (volume (Metric.ball c R)).toReal)⁻¹
          * (2 ^ (plExp l) * ∫⁻ x, (‖h x‖₊ : ℝ≥0∞) ^ (plExp l)) := hlocal
    _ = (ENNReal.ofReal (volume (Metric.ball c R)).toReal)⁻¹
          * (2 ^ (plExp l) * (lpNorm l (pE l) h) ^ (plExp l)) := by rw [hlp]
    _ ≤ (ENNReal.ofReal (volume (Metric.ball c R)).toReal)⁻¹
          * (2 ^ (plExp l) * (C ^ (plExp l)
            * (l2Norm (fun j => lpNorm l (pE l) (fun x => f j x * ψ x))) ^ (plExp l))) :=
        mul_le_mul' le_rfl (mul_le_mul' le_rfl hdec2)
    _ = (ENNReal.ofReal (volume (Metric.ball c R)).toReal)⁻¹
          * (2 ^ (plExp l) * (C ^ (plExp l)
            * (∑ j : Fin m, (lpNorm l (pE l) (fun x => f j x * ψ x)) ^ (2 : ℝ))
              ^ (plExp l / 2))) := by rw [hl2]
    _ ≤ (ENNReal.ofReal (volume (Metric.ball c R)).toReal)⁻¹
          * (2 ^ (plExp l) * (C ^ (plExp l)
            * ((((ENNReal.ofReal Cb) ^ (plExp l)
                * ENNReal.ofReal (volume (Metric.ball c R)).toReal) ^ (2 / plExp l)
                * ∑ j : Fin m, (tentNorm l A c R (f j)) ^ (2 / plExp l)) ^ (plExp l / 2)))) :=
        mul_le_mul' le_rfl (mul_le_mul' le_rfl (mul_le_mul' le_rfl
          (ENNReal.rpow_le_rpow hsum2 (by positivity))))
    _ = (ENNReal.ofReal (volume (Metric.ball c R)).toReal)⁻¹
          * (2 ^ (plExp l) * (C ^ (plExp l)
            * ((ENNReal.ofReal Cb) ^ (plExp l) * ENNReal.ofReal (volume (Metric.ball c R)).toReal
              * (∑ j : Fin m, (tentNorm l A c R (f j)) ^ (2 / plExp l)) ^ (plExp l / 2)))) := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity), hKpow]
    _ = 2 ^ (plExp l) * (C ^ (plExp l) * (ENNReal.ofReal Cb) ^ (plExp l)
          * (∑ j : Fin m, (tentNorm l A c R (f j)) ^ (2 / plExp l)) ^ (plExp l / 2)) := by
        have hc := hcancel
        calc (ENNReal.ofReal (volume (Metric.ball c R)).toReal)⁻¹
              * (2 ^ (plExp l) * (C ^ (plExp l)
                * ((ENNReal.ofReal Cb) ^ (plExp l)
                  * ENNReal.ofReal (volume (Metric.ball c R)).toReal
                  * (∑ j : Fin m, (tentNorm l A c R (f j)) ^ (2 / plExp l)) ^ (plExp l / 2))))
            = 2 ^ (plExp l) * (C ^ (plExp l)
                * (((ENNReal.ofReal (volume (Metric.ball c R)).toReal)⁻¹
                    * ((ENNReal.ofReal Cb) ^ (plExp l)
                      * ENNReal.ofReal (volume (Metric.ball c R)).toReal))
                  * (∑ j : Fin m, (tentNorm l A c R (f j)) ^ (2 / plExp l)) ^ (plExp l / 2))) := by
                ring
          _ = 2 ^ (plExp l) * (C ^ (plExp l) * ((ENNReal.ofReal Cb) ^ (plExp l)
                * (∑ j : Fin m, (tentNorm l A c R (f j)) ^ (2 / plExp l)) ^ (plExp l / 2))) := by
                rw [hc]
          _ = 2 ^ (plExp l) * (C ^ (plExp l) * (ENNReal.ofReal Cb) ^ (plExp l)
                * (∑ j : Fin m, (tentNorm l A c R (f j)) ^ (2 / plExp l)) ^ (plExp l / 2)) := by
                ring
    _ ≤ (C * ENNReal.ofReal (2 * Cb)) ^ (plExp l)
          * (∑ j : Fin m, (tentNorm l A c R (f j)) ^ (2 / plExp l)) ^ (plExp l / 2) := by
        have h1 : 2 ^ (plExp l) * (C ^ (plExp l) * (ENNReal.ofReal Cb) ^ (plExp l))
            ≤ (C * ENNReal.ofReal (2 * Cb)) ^ (plExp l) := by
          have := hconst
          rwa [show 2 ^ (plExp l) * ((ENNReal.ofReal Cb) ^ (plExp l) * C ^ (plExp l))
              = 2 ^ (plExp l) * (C ^ (plExp l) * (ENNReal.ofReal Cb) ^ (plExp l)) from by ring] at this
        calc 2 ^ (plExp l) * (C ^ (plExp l) * (ENNReal.ofReal Cb) ^ (plExp l)
              * (∑ j : Fin m, (tentNorm l A c R (f j)) ^ (2 / plExp l)) ^ (plExp l / 2))
            = (2 ^ (plExp l) * (C ^ (plExp l) * (ENNReal.ofReal Cb) ^ (plExp l)))
              * (∑ j : Fin m, (tentNorm l A c R (f j)) ^ (2 / plExp l)) ^ (plExp l / 2) := by ring
          _ ≤ (C * ENNReal.ofReal (2 * Cb)) ^ (plExp l)
              * (∑ j : Fin m, (tentNorm l A c R (f j)) ^ (2 / plExp l)) ^ (plExp l / 2) :=
              mul_le_mul' h1 le_rfl


end Submission.Vinogradov
