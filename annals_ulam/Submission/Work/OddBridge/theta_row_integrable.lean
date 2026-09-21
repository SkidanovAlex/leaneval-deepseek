import Mathlib
import Submission.Work.OddVolterra.Defs
import Submission.Work.OddVolterra.Assembly
import Submission.Work.OddVolterra.Kernel.Diag
import Submission.Work.OddVolterra.KernelExt.Kden_pos_of_curve
import Submission.Work.OddVolterra.KernelExt.KvecM_contDiffOn_box
import Submission.Work.OddVolterra.KernelExt.KvecM_eq_Kvec
import Submission.Work.OddVolterra.Existence.theta_integrable
import Submission.Work.OddBridge.Defs
import Submission.Work.OddBridge.Kden_radicand_pos_of_curve

/-!
# Interval integrability of the `𝚯`-integrand rows on a `CurveData` curve

The last two rows of the odd-case Volterra kernel `Work.OddVolterra.Theta` are the `u`-derivatives
at `u = s` of the `τ`-average `G2` of the Abel kernel.  This file proves the row integrability
requested by `Work.OddBridge.theta_row_integrable`: for a transition-slope curve given by
`Work.OddVolterra.CurveData` and every slope `s ∈ (0,1)`, the function
`σ ↦ (𝚯(n,h,s,σ,stateOf x y σ))` is interval-integrable on `s..1`.

The argument is the one of `Work.OddVolterra.Existence.theta_integrable`, transported to the
`CurveData` interface:

* `Work.OddBridge.Kden_radicand_pos_of_curve` gives strict positivity of the Abel denominator
  `Kden` on the full square `[s/2,1]²` of slopes, so the *manifest* kernel
  `Work.OddVolterra.KernelExt.KvecM` is `C²` there (`KvecM_contDiffOn_box`);
* the manifest kernel and the paper's kernel `Kvec` agree on the triangle `a ≤ σ`
  (`KvecM_eq_Kvec`), which is all the `τ`-average at `u = s` ever sees;
* the differentiability of the `τ`-average is therefore transferred from the manifest form using
  `Work.OddVolterra.Existence.theta_deriv_parametrization_integrable`, which yields exactly the
  interval-integrability of the `σ ↦ ∂_s G2` rows;
* the first two rows are the derivatives `x'`, `y'`, which are continuous on `(0,∞)`.
-/

open MeasureTheory Set Filter
open scoped Topology ContDiff Interval

namespace Work.OddBridge

noncomputable section

variable {h x y : ℝ → ℝ}

/-! ## Elementary helpers -/

/-- Interval integrability on `s..t` gives integrability on `Ioc s t` when `s ≤ t`. -/
lemma integrableOn_Ioc_of_intervalIntegrable {f : ℝ → ℝ} {s t : ℝ} (hst : s ≤ t)
    (hf : IntervalIntegrable f volume s t) : IntegrableOn f (Set.Ioc s t) volume := by
  rw [← uIoc_of_le hst]
  exact intervalIntegrable_iff.mp hf

/-! ## Positivity of the Abel radicands on a square of slopes -/

/-- **Positivity of the Abel denominator on a square of slopes**, in the form needed by
`KvecM_contDiffOn_box`: `Kden h s' σ (y σ) > 0` and `Kden h s' σ (-(x σ)) > 0` for all slopes
`s', σ` in a square `[a,b] ⊆ (0,1]²`. -/
lemma Kden_pos_box_of_curveData (n : ℕ) (hh : ContDiff ℝ (⊤ : ℕ∞) h)
    (hsupp : Function.support h ⊆ Set.Icc (1 - 2 * Work.OddVolterra.tau)
      (1 - Work.OddVolterra.tau))
    (hdata : Work.OddVolterra.CurveData n h x y) {a b : ℝ} (ha : 0 < a) (hb : b ≤ 1) :
    (∀ s' σ : ℝ, s' ∈ Set.Icc a b → σ ∈ Set.Icc a b →
        0 < Work.OddVolterra.Kden h s' σ (y σ)) ∧
    (∀ s' σ : ℝ, s' ∈ Set.Icc a b → σ ∈ Set.Icc a b →
        0 < Work.OddVolterra.Kden h s' σ (-(x σ))) := by
  have hrad := Kden_radicand_pos_of_curve n hh hsupp hdata
  constructor
  · intro s' σ hs' hσ
    have hs'pos : 0 < s' := lt_of_lt_of_le ha hs'.1
    have hσpos : 0 < σ := lt_of_lt_of_le ha hσ.1
    rw [Work.OddVolterra.Kden_eq_sqrt_krad]
    exact Real.sqrt_pos.mpr (hrad.1 s' σ hs'pos hσpos (le_trans hs'.2 hb) (le_trans hσ.2 hb))
  · intro s' σ hs' hσ
    have hs'pos : 0 < s' := lt_of_lt_of_le ha hs'.1
    have hσpos : 0 < σ := lt_of_lt_of_le ha hσ.1
    rw [Work.OddVolterra.Kden_eq_sqrt_krad]
    exact Real.sqrt_pos.mpr (hrad.2 s' σ hs'pos hσpos (le_trans hs'.2 hb) (le_trans hσ.2 hb))

/-! ## The two `G₂` rows -/

/-- **Interval integrability of the `G₂` rows of `𝚯`.**  For a transition-slope curve and a slope
`s ∈ (0,1)`, the `σ`-derivative at `u = s` of the `i`-th component of the Abel average
`G₂(·,σ,stateOf x y σ)` is interval-integrable on `s..1`. -/
theorem intervalIntegrable_G2_row (n : ℕ) (hn : 1 ≤ n) (hh : ContDiff ℝ (⊤ : ℕ∞) h)
    (hsupp : Function.support h ⊆ Set.Icc (1 - 2 * Work.OddVolterra.tau)
      (1 - Work.OddVolterra.tau))
    (hdata : Work.OddVolterra.CurveData n h x y) {a s : ℝ} (ha : 0 < a)
    (hs : s ∈ Set.Ioo a 1) (i : Fin 2) :
    IntervalIntegrable (fun σ : ℝ => deriv (fun u : ℝ => (Work.OddVolterra.G2 n h u σ
      ((Work.OddVolterra.stateOf x y) σ 0) ((Work.OddVolterra.stateOf x y) σ 1)
      ((Work.OddVolterra.stateOf x y) σ 2) ((Work.OddVolterra.stateOf x y) σ 3)) i) s)
      volume s 1 := by
  have hs0 : 0 < s := lt_trans ha hs.1
  have hs1 : s < 1 := hs.2
  have hs2 : 0 < s / 2 := by linarith
  -- positivity of the Abel denominator on the square `[s/2,1]²`
  obtain ⟨hposy, hposx⟩ := Kden_pos_box_of_curveData n hh hsupp hdata (a := s / 2) (b := 1) hs2 le_rfl
  -- `C¹`-smoothness of the manifest kernel on the square
  have hG : ContDiffOn ℝ 1 (fun p : ℝ × ℝ =>
      (Work.OddVolterra.KernelExt.KvecM n h p.1 p.2 (x p.2) (y p.2)
        (deriv x p.2) (deriv y p.2)) i)
      (Set.Icc (s / 2) 1 ×ˢ Set.Icc (s / 2) 1) := by
    have h2 := Work.OddVolterra.KernelExt.KvecM_contDiffOn_box (n := n) (h := h) (x := x) (y := y)
      (a := s / 2) (b := 1) hh hdata.smooth_x hdata.smooth_y hs2 le_rfl hposy hposx
    exact (contDiffOn_pi.mp (h2.of_le (by norm_num))) i
  -- the parametrisation lemma
  have hint := Work.OddVolterra.Existence.theta_deriv_parametrization_integrable
    (G := fun p : ℝ × ℝ => (Work.OddVolterra.KernelExt.KvecM n h p.1 p.2 (x p.2) (y p.2)
      (deriv x p.2) (deriv y p.2)) i) hG hs0 hs1
  -- replace the manifest kernel by the paper's kernel, on the triangle `a ≤ σ`
  refine hint.congr ?_
  intro σ hσ
  rw [uIoc_of_le (le_of_lt hs1)] at hσ
  have hσpos : 0 < σ := lt_trans hs0 hσ.1
  have hG2eq : (fun u : ℝ => (Work.OddVolterra.G2 n h u σ
        ((Work.OddVolterra.stateOf x y) σ 0) ((Work.OddVolterra.stateOf x y) σ 1)
        ((Work.OddVolterra.stateOf x y) σ 2) ((Work.OddVolterra.stateOf x y) σ 3)) i)
      = fun u : ℝ => ∫ τ in (0 : ℝ)..1,
          (Work.OddVolterra.Kvec n h (u + τ * (σ - u)) σ (x σ) (y σ)
            (deriv x σ) (deriv y σ)) i / Real.sqrt (τ * (1 - τ)) := by
    funext u
    rfl
  have hev : (fun u : ℝ => ∫ τ in (0 : ℝ)..1,
        (Work.OddVolterra.KernelExt.KvecM n h (u + τ * (σ - u)) σ (x σ) (y σ)
          (deriv x σ) (deriv y σ)) i / Real.sqrt (τ * (1 - τ)))
      =ᶠ[𝓝 s] (fun u : ℝ => ∫ τ in (0 : ℝ)..1,
        (Work.OddVolterra.Kvec n h (u + τ * (σ - u)) σ (x σ) (y σ)
          (deriv x σ) (deriv y σ)) i / Real.sqrt (τ * (1 - τ))) := by
    filter_upwards [isOpen_Ioo.mem_nhds (show s ∈ Set.Ioo (s / 2) σ by
      exact ⟨by linarith, hσ.1⟩)] with u hu
    refine intervalIntegral.integral_congr (fun τ hτ => ?_)
    rw [uIcc_of_le zero_le_one] at hτ
    have huσ : u ≤ σ := le_of_lt hu.2
    have hupt : 0 < u + τ * (σ - u) := by
      have hu0 : 0 < u := lt_trans hs2 hu.1
      have h1 : 0 ≤ τ * (σ - u) := mul_nonneg hτ.1 (sub_nonneg.mpr huσ)
      linarith
    have hlept : u + τ * (σ - u) ≤ σ := by
      have h1 : u + τ * (σ - u) = (1 - τ) * u + τ * σ := by ring
      rw [h1]
      have h2 : 0 ≤ 1 - τ := by linarith [hτ.2]
      nlinarith [h2, hτ.1, hτ.2, huσ, le_of_lt hu.1]
    have hlept1 : u + τ * (σ - u) ≤ 1 := le_trans hlept hσ.2
    have hR := Kden_radicand_pos_of_curve n hh hsupp hdata
    have hRy := hR.1 (u + τ * (σ - u)) σ hupt hσpos hlept1 hσ.2
    have hRx := hR.2 (u + τ * (σ - u)) σ hupt hσpos hlept1 hσ.2
    have hEq := Work.OddVolterra.KernelExt.KvecM_eq_Kvec (n := n) (hn := hn) (h := h) hh
      (s := u + τ * (σ - u)) (σ := σ) hlept (x σ) (y σ) (deriv x σ) (deriv y σ) hRy hRx
    simp only [hEq]
  show deriv (fun u : ℝ => ∫ τ in (0 : ℝ)..1,
      (Work.OddVolterra.KernelExt.KvecM n h (u + τ * (σ - u)) σ (x σ) (y σ)
        (deriv x σ) (deriv y σ)) i / Real.sqrt (τ * (1 - τ))) s
    = deriv (fun u : ℝ => (Work.OddVolterra.G2 n h u σ
        ((Work.OddVolterra.stateOf x y) σ 0) ((Work.OddVolterra.stateOf x y) σ 1)
        ((Work.OddVolterra.stateOf x y) σ 2) ((Work.OddVolterra.stateOf x y) σ 3)) i) s
  rw [hG2eq, ← hev.deriv_eq]

/-! ## The target theorem -/

theorem theta_row_integrable (n : ℕ) (hn : 1 ≤ n) {h x y : ℝ → ℝ}
    (hh : ContDiff ℝ (⊤ : ℕ∞) h)
    (hsupp : Function.support h ⊆ Set.Icc (1 - 2 * Work.OddVolterra.tau) (1 - Work.OddVolterra.tau))
    (hdata : Work.OddVolterra.CurveData n h x y) {a : ℝ} (ha : 0 < a) :
    ∀ s ∈ Set.Ioo a 1,
      IntervalIntegrable (fun σ : ℝ => Work.OddVolterra.Theta n h s σ (Work.OddVolterra.stateOf x y σ))
        volume s 1 := by
  intro s hs
  have hs0 : 0 < s := lt_trans ha hs.1
  have hs1 : s < 1 := hs.2
  -- the first two rows: `x'` and `y'`
  have hdx : IntervalIntegrable (fun σ : ℝ => deriv x σ) volume s 1 := by
    refine ContinuousOn.intervalIntegrable ?_
    refine (Work.OddVolterra.KernelExt.contDiffOn_deriv_Ioi hdata.smooth_x).continuousOn.mono ?_
    intro σ hσ
    rw [uIcc_of_le (le_of_lt hs1)] at hσ
    exact lt_of_lt_of_le hs0 hσ.1
  have hdy : IntervalIntegrable (fun σ : ℝ => deriv y σ) volume s 1 := by
    refine ContinuousOn.intervalIntegrable ?_
    refine (Work.OddVolterra.KernelExt.contDiffOn_deriv_Ioi hdata.smooth_y).continuousOn.mono ?_
    intro σ hσ
    rw [uIcc_of_le (le_of_lt hs1)] at hσ
    exact lt_of_lt_of_le hs0 hσ.1
  -- the last two rows
  have hG0 := intervalIntegrable_G2_row n hn hh hsupp hdata ha hs 0
  have hG1 := intervalIntegrable_G2_row n hn hh hsupp hdata ha hs 1
  -- assembly
  rw [intervalIntegrable_iff, uIoc_of_le (le_of_lt hs1)]
  have hF : (fun σ : ℝ => Work.OddVolterra.Theta n h s σ (Work.OddVolterra.stateOf x y σ))
      = fun σ : ℝ => ![ -((Work.OddVolterra.stateOf x y) σ 2), -((Work.OddVolterra.stateOf x y) σ 3),
          -(deriv (fun u : ℝ => (Work.OddVolterra.G2 n h u σ ((Work.OddVolterra.stateOf x y) σ 0)
            ((Work.OddVolterra.stateOf x y) σ 1) ((Work.OddVolterra.stateOf x y) σ 2)
            ((Work.OddVolterra.stateOf x y) σ 3)) 0) s),
          -(deriv (fun u : ℝ => (Work.OddVolterra.G2 n h u σ ((Work.OddVolterra.stateOf x y) σ 0)
            ((Work.OddVolterra.stateOf x y) σ 1) ((Work.OddVolterra.stateOf x y) σ 2)
            ((Work.OddVolterra.stateOf x y) σ 3)) 1) s)] := rfl
  rw [hF]
  show Integrable (fun σ : ℝ => ![ -((Work.OddVolterra.stateOf x y) σ 2),
      -((Work.OddVolterra.stateOf x y) σ 3),
      -(deriv (fun u : ℝ => (Work.OddVolterra.G2 n h u σ ((Work.OddVolterra.stateOf x y) σ 0)
        ((Work.OddVolterra.stateOf x y) σ 1) ((Work.OddVolterra.stateOf x y) σ 2)
        ((Work.OddVolterra.stateOf x y) σ 3)) 0) s),
      -(deriv (fun u : ℝ => (Work.OddVolterra.G2 n h u σ ((Work.OddVolterra.stateOf x y) σ 0)
        ((Work.OddVolterra.stateOf x y) σ 1) ((Work.OddVolterra.stateOf x y) σ 2)
        ((Work.OddVolterra.stateOf x y) σ 3)) 1) s)])
      (volume.restrict (Set.Ioc s 1))
  rw [integrable_pi_iff]
  intro i
  fin_cases i
  · show IntegrableOn (fun σ : ℝ => -deriv x σ) (Set.Ioc s 1) volume
    exact (integrableOn_Ioc_of_intervalIntegrable (le_of_lt hs1) hdx).neg
  · show IntegrableOn (fun σ : ℝ => -deriv y σ) (Set.Ioc s 1) volume
    exact (integrableOn_Ioc_of_intervalIntegrable (le_of_lt hs1) hdy).neg
  · show IntegrableOn (fun σ : ℝ => -deriv (fun u : ℝ => (Work.OddVolterra.G2 n h u σ
        ((Work.OddVolterra.stateOf x y) σ 0) ((Work.OddVolterra.stateOf x y) σ 1)
        ((Work.OddVolterra.stateOf x y) σ 2) ((Work.OddVolterra.stateOf x y) σ 3)) 0) s)
        (Set.Ioc s 1) volume
    exact (integrableOn_Ioc_of_intervalIntegrable (le_of_lt hs1) hG0).neg
  · show IntegrableOn (fun σ : ℝ => -deriv (fun u : ℝ => (Work.OddVolterra.G2 n h u σ
        ((Work.OddVolterra.stateOf x y) σ 0) ((Work.OddVolterra.stateOf x y) σ 1)
        ((Work.OddVolterra.stateOf x y) σ 2) ((Work.OddVolterra.stateOf x y) σ 3)) 1) s)
        (Set.Ioc s 1) volume
    exact (integrableOn_Ioc_of_intervalIntegrable (le_of_lt hs1) hG1).neg

end

end Work.OddBridge
