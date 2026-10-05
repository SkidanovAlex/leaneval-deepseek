import Mathlib
import Submission.Work.RPV.Defs
import Submission.Work.RPV.V
import Submission.Work.RPV.VBasic
import Submission.Work.RPB.Defs
import Submission.Work.RPB.B3.EvenTaylorDefs
import Submission.Work.RPB.B3.EvenTaylorSteps
import Submission.Work.RPB.B3.boundsOnCompactBox
import Submission.Work.RPB.B3.existsRadiusOpen
import Submission.Work.RPB.B5.evenHadamardSplit
import Submission.Work.RPB.B5.SqrtGenDefs
import Submission.Work.RPB.B5.sqrtPowSmooth
import Submission.Work.RPB.B5.SqrtGen.branch_fderiv_pos
import Submission.Work.RPB.B5.SqrtGen.branch_fderiv_neg
import Submission.Work.RPB.B5.halfChordSmooth
import Submission.Work.RPB.B5.chordSurf_rhoChart
import Submission.Work.RPB.B5.hasDerivAt_of_tendsto_slope_sq
import Submission.Work.RPB.B5.exists_eps_neg_of_deriv_pos
import Submission.Work.RPB.B5.regularizedPhaseIntegrand
import Submission.Work.RPB.B5.phaseDeriv_eq
import Submission.Work.RPA3.contDiff_param_intervalIntegral

/-!
# The `ρ`-chart of the chord surface, full statement

Target: `Work.RPB.B5.chordSurf_rhoChart_full`.

The chart is assembled from three `ρ`-charts:
* `S`, the chart of the chord sum `(c τ (t+r) + c τ (t-r))/√2`,
* `P`, the chart of the squared chord datum `(‖c τ (t+r)‖² + ‖c τ (t-r)‖²)/2 - 1`,
* `Â`, a phase chart equal to the chord phase `a` at `ρ = r²`, `2π`-quasiperiodic in `t` (with
  monodromy `+2π`) and `C⁸` on the strip `τ ∈ [0,1]` (global smoothness is impossible: `a` is only
  given on the strip `τ ∈ [0,1]`, so `Â` is built as the sum of a globally smooth chart of the
  `ρ`-chart of the (strictly periodic) phase *increment* `r ↦ a τ t r - a τ t 0` and of a
  `2π`-quasiperiodic lift of the constant `a τ t 0`).

The even `ρ`-chart of an even function is produced by the Hadamard splitting
(`Work.RPB.B5.evenHadamardSplit`) combined with the fact that `ρ ↦ ρ^k • ψ (√|ρ|)` is `C^k`
(the `SqrtGen` development, reproved here from its public branch lemmas).
-/

open RectangularPegProblem
open Manifold Complex Real
open scoped ContDiff
open scoped Topology

set_option autoImplicit false

noncomputable section

namespace Work.RPB.B5

open Work.RPB.B3.EvenTaylor

/-- **The `SqrtGen` induction, from the public branch lemmas.**  For smooth
`ψ : (ℝ × ℝ) × ℝ → E` the level-`n` piecewise function
`GG ψ n z = z.2 ^ n • ψ (z.1, √z.2)` for `z.2 ≥ 0` and `z.2 ^ n • ψ (z.1, √(-z.2))` for `z.2 < 0`
is `C^n`, and `dG ψ n z` is the Fréchet derivative of level `n + 1` at `z`. -/
theorem GG_main (n : ℕ) {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (ψ : (ℝ × ℝ) × ℝ → E) (hψ : ContDiff ℝ ∞ ψ) :
    ContDiff ℝ n (SqrtGen.GG ψ n) ∧
    (∀ z, HasFDerivAt (SqrtGen.GG ψ (n + 1)) (SqrtGen.dG ψ n z) z) := by
  induction n generalizing E with
  | zero =>
    constructor
    · exact SqrtGen.contDiff_GG_zero ψ hψ.continuous
    · intro z
      rcases lt_trichotomy z.2 0 with hlt | heq | hgt
      · refine (SqrtGen.branch_fderiv_neg ψ 0 z hψ hlt).congr_of_eventuallyEq ?_
        have hev : ∀ᶠ w in 𝓝 z, w.2 < 0 :=
          (isOpen_lt (continuous_snd : Continuous fun w : (ℝ × ℝ) × ℝ => w.2)
            continuous_const).mem_nhds hlt
        filter_upwards [hev] with w hw
        simp only [SqrtGen.GG, ite_eq_right (not_le.mpr hw)]
      · have hcont : ContinuousAt (SqrtGen.GG ψ 0) z :=
          (SqrtGen.contDiff_GG_zero ψ hψ.continuous).continuous.continuousAt
        have hb := SqrtGen.hasFDerivAt_proj_smul (SqrtGen.GG ψ 0) z heq hcont
        have hdg : SqrtGen.dG ψ 0 z
            = (ContinuousLinearMap.snd ℝ (ℝ × ℝ) ℝ).smulRight (SqrtGen.GG ψ 0 z) := by
          simp only [SqrtGen.dG, SqrtGen.GG, SqrtGen.ThetaG, heq, le_refl, reduceIte,
            pow_zero, one_smul, zero_smul]
          simp
        rw [show SqrtGen.GG ψ 1 = (fun w : (ℝ × ℝ) × ℝ => w.2 • SqrtGen.GG ψ 0 w) from
          SqrtGen.GG_smul_succ ψ 0, hdg]
        exact hb
      · refine (SqrtGen.branch_fderiv_pos ψ 0 z hψ hgt).congr_of_eventuallyEq ?_
        have hev : ∀ᶠ w in 𝓝 z, 0 ≤ w.2 :=
          Filter.mem_of_superset
            ((isOpen_lt (continuous_const : Continuous fun _ : (ℝ × ℝ) × ℝ => (0 : ℝ))
              (continuous_snd : Continuous fun w : (ℝ × ℝ) × ℝ => w.2)).mem_nhds hgt)
            (fun w (hw : (0 : ℝ) < w.2) => le_of_lt hw)
        filter_upwards [hev] with w hw
        simp only [SqrtGen.GG, ite_eq_left hw]
  | succ n ih =>
    constructor
    · rw [show ((n + 1 : ℕ) : WithTop ℕ∞) = ((n : ℕ) : WithTop ℕ∞) + 1 from by
        rw [Nat.cast_add, Nat.cast_one]]
      rw [contDiff_succ_iff_hasFDerivAt]
      exact ⟨SqrtGen.dG ψ n,
        SqrtGen.contDiff_dG ψ n
          (ih (SqrtGen.pdX ψ) (SqrtGen.contDiff_pdX ψ hψ)).1
          (ih (SqrtGen.ThetaG ψ (n + 1)) (SqrtGen.contDiff_ThetaG ψ hψ (n + 1))).1,
        fun z => (ih ψ hψ).2 z⟩
    · intro z
      exact SqrtGen.hasFDerivAt_GG_succ ψ n z ((ih ψ hψ).2 z)

/-- **The even `ρ`-chart of an even, `2π`-periodic in `t`, smooth function.**
For `F` smooth in `(τ,t,r)`, even in `r` and `2π`-periodic in `t`, and every `k`, there is a
function `G` of `(τ,t,ρ)`, `C^k`, `2π`-periodic in `t`, with `G τ t ρ = F τ t (√ρ)` for `ρ ≥ 0`. -/
theorem evenChart {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (F : ℝ → ℝ → ℝ → E) (k : ℕ)
    (hF : ContDiff ℝ ∞ (fun z : ℝ × (ℝ × ℝ) => F z.1 z.2.1 z.2.2))
    (heven : ∀ τ t r, F τ t (-r) = F τ t r)
    (hper : ∀ τ t r, F τ (t + 2 * Real.pi) r = F τ t r) :
    ∃ G : ℝ → ℝ → ℝ → E,
      ContDiff ℝ k (fun z : ℝ × (ℝ × ℝ) => G z.1 z.2.1 z.2.2) ∧
      (∀ τ t ρ, 0 ≤ ρ → G τ t ρ = F τ t (Real.sqrt ρ)) ∧
      (∀ τ t ρ, G τ (t + 2 * Real.pi) ρ = G τ t ρ) := by
  classical
  set F' : (ℝ × ℝ) × ℝ → E := fun z => F z.1.1 z.1.2 z.2 with hF'def
  have hF' : ContDiff ℝ ∞ F' := by
    have hcomp : F' = (fun z : ℝ × (ℝ × ℝ) => F z.1 z.2.1 z.2.2) ∘
        (fun z : (ℝ × ℝ) × ℝ => (z.1.1, (z.1.2, z.2))) := rfl
    rw [hcomp]
    exact hF.comp (by fun_prop)
  have hF'even : ∀ p r, F' (p, -r) = F' (p, r) := fun p r => heven p.1 p.2 r
  have hF'per : Per F' := fun τ t r => hper τ t r
  have hchi_per : ∀ j : ℕ, Per (chi F' j) := fun j => per_chi F' hF'per j
  have hchi_sm : ∀ j : ℕ, ContDiff ℝ ∞ (chi F' j) := fun j => chi_contDiff F' hF' hF'even j
  refine ⟨fun τ t ρ => (∑ j : Fin k, ρ ^ (j : ℕ) • chi F' (j : ℕ) ((τ, t), 0)) +
      SqrtGen.GG (chi F' k) k ((τ, t), ρ), ?_, ?_, ?_⟩
  · -- smoothness
    have hpoly : ContDiff ℝ ∞ (fun z : ℝ × (ℝ × ℝ) =>
        ∑ j : Fin k, z.2.2 ^ (j : ℕ) • chi F' (j : ℕ) ((z.1, z.2.1), 0)) := by
      refine ContDiff.sum (fun j _ => ?_)
      refine ContDiff.smul ?_ ?_
      · fun_prop
      · exact (hchi_sm (j : ℕ)).comp (by fun_prop)
    have hgg : ContDiff ℝ k (fun z : ℝ × (ℝ × ℝ) =>
        SqrtGen.GG (chi F' k) k ((z.1, z.2.1), z.2.2)) :=
      (GG_main k (chi F' k) (hchi_sm k)).1.comp (by fun_prop)
    exact (hpoly.of_le (by simp)).add hgg
  · -- value property
    intro τ t ρ hρ
    have hdec := chi_decomp F' hF' hF'even k (τ, t) (Real.sqrt ρ)
    have hsq : ∀ i : ℕ, (Real.sqrt ρ) ^ (2 * i) = ρ ^ i := by
      intro i
      rw [pow_mul, Real.sq_sqrt hρ]
    show (∑ j : Fin k, ρ ^ (j : ℕ) • chi F' (j : ℕ) ((τ, t), 0)) +
        SqrtGen.GG (chi F' k) k ((τ, t), ρ) = F τ t (Real.sqrt ρ)
    rw [show SqrtGen.GG (chi F' k) k ((τ, t), ρ)
        = ρ ^ k • chi F' k ((τ, t), Real.sqrt ρ) from by
      simp only [SqrtGen.GG, ite_eq_left hρ]]
    rw [show F τ t (Real.sqrt ρ) = F' ((τ, t), Real.sqrt ρ) from rfl, hdec,
      Fin.sum_univ_eq_sum_range (fun i : ℕ => ρ ^ i • chi F' i ((τ, t), 0))]
    congr 1
    · exact Finset.sum_congr rfl (fun i _ => by rw [hsq i])
    · rw [hsq k]
  · -- periodicity
    intro τ t ρ
    have h1 : ∀ j : ℕ, chi F' j ((τ, t + 2 * Real.pi), 0) = chi F' j ((τ, t), 0) :=
      fun j => hchi_per j τ t 0
    have h2 : ∀ s : ℝ, chi F' k ((τ, t + 2 * Real.pi), s) = chi F' k ((τ, t), s) :=
      fun s => hchi_per k τ t s
    show (∑ j : Fin k, ρ ^ (j : ℕ) • chi F' (j : ℕ) ((τ, t + 2 * Real.pi), 0)) +
        SqrtGen.GG (chi F' k) k ((τ, t + 2 * Real.pi), ρ)
      = (∑ j : Fin k, ρ ^ (j : ℕ) • chi F' (j : ℕ) ((τ, t), 0)) +
        SqrtGen.GG (chi F' k) k ((τ, t), ρ)
    rw [Finset.sum_congr rfl (fun j _ => by rw [h1 j])]
    congr 1
    simp only [SqrtGen.GG]
    split_ifs <;> rw [h2]

/-! ## The chord data is even and `2π`-periodic in `t` -/

theorem chordSumChart_per (c : ℝ → ℝ → ℂ) (hper : ∀ τ t, c τ (t + 2 * Real.pi) = c τ t) :
    ∀ τ t r, chordSumChart c τ (t + 2 * Real.pi) r = chordSumChart c τ t r := by
  intro τ t r
  unfold chordSumChart
  rw [show t + 2 * Real.pi + r = (t + r) + 2 * Real.pi by ring,
    show t + 2 * Real.pi - r = (t - r) + 2 * Real.pi by ring, hper τ (t + r), hper τ (t - r)]

theorem chordModChart_per (c : ℝ → ℝ → ℂ) (hper : ∀ τ t, c τ (t + 2 * Real.pi) = c τ t) :
    ∀ τ t r, chordModChart c τ (t + 2 * Real.pi) r = chordModChart c τ t r := by
  intro τ t r
  unfold chordModChart
  rw [show t + 2 * Real.pi + r = (t + r) + 2 * Real.pi by ring,
    show t + 2 * Real.pi - r = (t - r) + 2 * Real.pi by ring, hper τ (t + r), hper τ (t - r)]

/-! ## The half chord does not vanish for `|r| < π` -/

theorem hc_ne_zero {c : ℝ → ℝ → ℂ} {hc : ℝ → ℝ → ℝ → ℂ}
    (hc_zero : ∀ τ t, hc τ t 0 = deriv (c τ) t)
    (hc_half : ∀ τ t r, r ≠ 0 → hc τ t r = Work.RPB.halfChord c τ t r)
    (hinj : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ t t', c τ t = c τ t' → ∃ m : ℤ, t' = t + 2 * Real.pi * m)
    (himm : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ t, deriv (c τ) t ≠ 0) :
    ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ t r, |r| < Real.pi → hc τ t r ≠ 0 := by
  intro τ hτ t r hr
  rcases eq_or_ne r 0 with hr0 | hr0
  · rw [hr0, hc_zero]
    exact himm τ hτ t
  · rw [hc_half τ t r hr0]
    intro h0
    have h2 : c τ (t + r) = c τ (t - r) := by
      have h1 : c τ (t + r) - c τ (t - r) = 0 := by
        rw [Work.RPB.halfChord, div_eq_zero_iff] at h0
        rcases h0 with h | h
        · exact h
        · exact absurd h (mul_ne_zero (two_ne_zero : (2 : ℂ) ≠ 0)
            (Complex.ofReal_ne_zero.mpr hr0))
      exact sub_eq_zero.mp h1
    obtain ⟨m, hm⟩ := hinj τ hτ (t + r) (t - r) h2
    have hrm : r = -(Real.pi * (m : ℝ)) := by
      have h' : -(2 * r) = 2 * Real.pi * (m : ℝ) := by linarith
      linarith
    have habs : |r| = Real.pi * |(m : ℝ)| := by
      rw [hrm, abs_neg, abs_mul, abs_of_pos Real.pi_pos]
    have hm1 : |(m : ℝ)| < 1 := by
      have h := hr
      rw [habs] at h
      nlinarith [Real.pi_pos]
    have hm0 : m = 0 := by
      have hcast : (((|m| : ℤ)) : ℝ) < 1 := by
        rwa [Int.cast_abs]
      have : (|m| : ℤ) < 1 := by exact_mod_cast hcast
      have := Int.abs_lt_one_iff.mp this
      exact this
    rw [hm0] at hrm
    simp only [Int.cast_zero, mul_zero, neg_zero] at hrm
    exact hr0 hrm

/-! ## `K₀` of the chord surface -/

theorem K0_chordSurf (c : ℝ → ℝ → ℂ) (a : ℝ → ℝ → ℝ → ℝ) {τ t r : ℝ} (hr : r ≠ 0) :
    Work.RPV.K0 (Work.RPB.chordSurf c a τ t r) + 1
      = r ^ 2 * ‖Work.RPB.halfChord c τ t r‖ ^ 2 := by
  have hz : (2 * r : ℂ) ≠ 0 := by
    rw [show (2 * r : ℂ) = ((2 * r : ℝ) : ℂ) by push_cast; ring, Complex.ofReal_ne_zero]
    exact mul_ne_zero two_ne_zero hr
  have h2 : (2 * r : ℂ) * Work.RPB.halfChord c τ t r = c τ (t + r) - c τ (t - r) := by
    rw [Work.RPB.halfChord]
    exact mul_div_cancel₀ _ hz
  rw [Work.RPB.chordSurf, Work.RPV.K0_chordPS, ← h2, sub_add_cancel, norm_mul]
  have h3 : ‖(2 * r : ℂ)‖ = 2 * |r| := by
    rw [show (2 * r : ℂ) = ((2 * r : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
      Real.norm_eq_abs, abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 2)]
  rw [h3]
  have h4 : (2 * |r| * ‖Work.RPB.halfChord c τ t r‖) ^ 2
      = 4 * (r ^ 2 * ‖Work.RPB.halfChord c τ t r‖ ^ 2) := by
    rw [mul_pow, mul_pow, sq_abs]
    ring
  rw [h4]
  ring

/-! ## A uniform lower bound for `‖c'‖²` -/

theorem c_shift_nat (c : ℝ → ℝ → ℂ) (hper : ∀ τ t, c τ (t + 2 * Real.pi) = c τ t)
    (τ : ℝ) (x : ℝ) : ∀ n : ℕ, c τ (x + (n : ℝ) * (2 * Real.pi)) = c τ x := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show ((n + 1 : ℕ) : ℝ) * (2 * Real.pi)
          = (n : ℝ) * (2 * Real.pi) + 2 * Real.pi by push_cast; ring]
    rw [show x + ((n : ℝ) * (2 * Real.pi) + 2 * Real.pi)
          = (x + (n : ℝ) * (2 * Real.pi)) + 2 * Real.pi by ring, hper, ih]

theorem c_shift_neg (c : ℝ → ℝ → ℂ) (hper : ∀ τ t, c τ (t + 2 * Real.pi) = c τ t)
    (τ : ℝ) (x : ℝ) : ∀ n : ℕ, c τ (x - (n : ℝ) * (2 * Real.pi)) = c τ x := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show ((n + 1 : ℕ) : ℝ) * (2 * Real.pi)
          = (n : ℝ) * (2 * Real.pi) + 2 * Real.pi by push_cast; ring]
    rw [show x - ((n : ℝ) * (2 * Real.pi) + 2 * Real.pi)
          = (x - (n : ℝ) * (2 * Real.pi)) - 2 * Real.pi by ring]
    rw [← hper τ ((x - (n : ℝ) * (2 * Real.pi)) - 2 * Real.pi)]
    rw [show (x - (n : ℝ) * (2 * Real.pi)) - 2 * Real.pi + 2 * Real.pi
          = x - (n : ℝ) * (2 * Real.pi) by ring]
    exact ih

theorem c_shift_int (c : ℝ → ℝ → ℂ) (hper : ∀ τ t, c τ (t + 2 * Real.pi) = c τ t)
    (τ : ℝ) (m : ℤ) (x : ℝ) :
    c τ (x + (m : ℝ) * (2 * Real.pi)) = c τ x := by
  obtain ⟨n, hn | hn⟩ := Int.eq_nat_or_neg m
  · rw [hn]
    push_cast
    exact c_shift_nat c hper τ x n
  · rw [hn]
    push_cast
    rw [show x + -(n : ℝ) * (2 * Real.pi) = x - (n : ℝ) * (2 * Real.pi) by ring]
    exact c_shift_neg c hper τ x n

theorem deriv_shift_periodic (c : ℝ → ℝ → ℂ) (hper : ∀ τ t, c τ (t + 2 * Real.pi) = c τ t)
    (τ : ℝ) (m : ℤ) (x : ℝ) :
    deriv (c τ) (x + (m : ℝ) * (2 * Real.pi)) = deriv (c τ) x := by
  have hf : (fun s : ℝ => c τ (x + (m : ℝ) * (2 * Real.pi) + s)) = (fun s : ℝ => c τ (x + s)) := by
    funext s
    rw [show x + (m : ℝ) * (2 * Real.pi) + s = (x + s) + (m : ℝ) * (2 * Real.pi) by ring]
    exact c_shift_int c hper τ m (x + s)
  have h1 : deriv (fun s : ℝ => c τ (x + (m : ℝ) * (2 * Real.pi) + s)) 0
      = deriv (c τ) (x + (m : ℝ) * (2 * Real.pi)) := by
    rw [show (fun s : ℝ => c τ (x + (m : ℝ) * (2 * Real.pi) + s))
        = (fun s : ℝ => c τ (s + (x + (m : ℝ) * (2 * Real.pi)))) from by funext s; ring_nf]
    simpa using deriv_comp_add_const (c τ) (x + (m : ℝ) * (2 * Real.pi)) 0
  have h2 : deriv (fun s : ℝ => c τ (x + s)) 0 = deriv (c τ) x := by
    rw [show (fun s : ℝ => c τ (x + s)) = (fun s : ℝ => c τ (s + x)) from by funext s; ring_nf]
    simpa using deriv_comp_add_const (c τ) x 0
  rw [← h1, hf, h2]

theorem exists_delta_deriv_sq (c : ℝ → ℝ → ℂ)
    (hcs : ContDiff ℝ ∞ (fun z : ℝ × ℝ => c z.1 z.2))
    (hper : ∀ τ t, c τ (t + 2 * Real.pi) = c τ t)
    (himm : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ t, deriv (c τ) t ≠ 0) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ t, δ ≤ ‖deriv (c τ) t‖ ^ 2 := by
  have hcont : Continuous (fun p : ℝ × (ℝ × ℝ) => ‖deriv (c p.1) p.2.1‖ ^ 2) := by
    have h1 : Continuous (fun p : ℝ × (ℝ × ℝ) => Work.RPB.B5.pDeriv c p.1 p.2.1) :=
      (contDiff_pDeriv c hcs).continuous.comp
        ((continuous_fst : Continuous fun p : ℝ × (ℝ × ℝ) => p.1).prodMk
          (continuous_fst.comp (continuous_snd : Continuous fun p : ℝ × (ℝ × ℝ) => p.2)))
    have h2 : (fun p : ℝ × (ℝ × ℝ) => deriv (c p.1) p.2.1)
        = (fun p : ℝ × (ℝ × ℝ) => Work.RPB.B5.pDeriv c p.1 p.2.1) := by
      funext p
      exact (pDeriv_eq_deriv c hcs p.1 p.2.1).symm
    rw [show (fun p : ℝ × (ℝ × ℝ) => ‖deriv (c p.1) p.2.1‖ ^ 2)
        = (fun p : ℝ × (ℝ × ℝ) => ‖Work.RPB.B5.pDeriv c p.1 p.2.1‖ ^ 2) by
      funext p
      exact congrArg (fun f : ℝ × (ℝ × ℝ) → ℂ => ‖f p‖ ^ 2) h2]
    exact (h1.norm).pow 2
  have hpos : ∀ p ∈ Set.Icc (0 : ℝ) 1 ×ˢ (Set.Icc (0 : ℝ) (2 * Real.pi) ×ˢ Set.Icc (-1 : ℝ) 1),
      0 < ‖deriv (c p.1) p.2.1‖ ^ 2 := by
    rintro ⟨τ, t, u⟩ ⟨hτ, ht, hu⟩
    have hne : deriv (c τ) t ≠ 0 := himm τ hτ t
    positivity
  obtain ⟨δ, hδpos, M, hMpos, hbnd⟩ :=
    Work.RPB.B3.boundsOnCompactBox (g := fun p : ℝ × (ℝ × ℝ) => ‖deriv (c p.1) p.2.1‖ ^ 2)
      hcont hpos
  have hδ : ∀ p ∈ Set.Icc (0 : ℝ) 1 ×ˢ (Set.Icc (0 : ℝ) (2 * Real.pi) ×ˢ Set.Icc (-1 : ℝ) 1),
      δ ≤ ‖deriv (c p.1) p.2.1‖ ^ 2 := fun p hp => (hbnd p hp).1
  refine ⟨δ, hδpos, ?_⟩
  intro τ hτ t
  obtain ⟨m, t₀, ht₀, ht⟩ := Work.RPB.B3.existsAngleReduce t
  have hbox : δ ≤ ‖deriv (c τ) t₀‖ ^ 2 :=
    hδ (τ, (t₀, 0)) ⟨hτ, ht₀, by norm_num⟩
  rw [ht, deriv_shift_periodic c hper τ m t₀]
  exact hbox

/-! ## The assembly -/

/-- **The assembly**: from a phase chart `Â` (only required to be `C⁸` on the strip `τ ∈ [0,1]`,
`2π`-quasiperiodic in `t`, and equal to the chord phase at `ρ = r²`) and the uniform sign lemma for
`ρ ↦ K₀ + 1`, build the `ρ`-chart `W` of the chord surface with all four required properties. -/
theorem assembly (CI : Work.RPV.CurveIsotopy) (a : ℝ → ℝ → ℝ → ℝ)
    (Â : ℝ → ℝ → ℝ → ℝ)
    (hA_sm : ContDiffOn ℝ 8 (fun z : ℝ × (ℝ × ℝ) => Â z.1 z.2.1 z.2.2)
        (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ ×ˢ Set.univ))
    (hA_per : ∀ τ t ρ, Â τ (t + 2 * Real.pi) ρ = Â τ t ρ + 2 * Real.pi)
    (hA_val : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ t, ∀ r ∈ Set.Ioc (0 : ℝ) (Real.pi / 2),
      Â τ t (r ^ 2) = a τ t r)
    (heps : ∀ (F : ℝ × (ℝ × ℝ) → ℝ) (δ : ℝ), 0 < δ → ContDiff ℝ 1 F →
      (∀ τ t ρ, F (τ, (t + 2 * Real.pi, ρ)) = F (τ, (t, ρ))) →
      (∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ t, F (τ, (t, 0)) = 0) →
      (∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ t, δ ≤ deriv (fun s : ℝ => F (τ, (t, s))) 0) →
      ∃ ε : ℝ, 0 < ε ∧ ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ t, ∀ ρ ∈ Set.Ioo (-ε) 0,
        F (τ, (t, ρ)) < 0) :
    ∃ ρ₀ : ℝ, Real.pi ^ 2 / 4 < ρ₀ ∧ ∃ W : ℝ → ℝ → ℝ → Work.RPV.PS,
      ContDiffOn ℝ 8 (fun z : ℝ × (ℝ × ℝ) => W z.1 z.2.1 z.2.2)
        (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ ×ˢ Set.Ioo (-ρ₀) ρ₀) ∧
      (∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ t : ℝ, ∀ r ∈ Set.Ioc (0 : ℝ) (Real.pi / 2),
        W τ t (r ^ 2) = Work.RPB.chordSurf CI.c a τ t r) ∧
      (∀ τ t ρ, W τ (t + 2 * Real.pi) ρ = Work.RPV.Tk 1 (W τ t ρ)) ∧
      (∃ ε : ℝ, 0 < ε ∧ ε ≤ ρ₀ ∧
        ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ t : ℝ, ∀ ρ ∈ Set.Ioo (-ε) 0,
          Work.RPV.K0 (W τ t ρ) + 1 < 0) := by
  -- the two even charts of the phase-free pieces
  obtain ⟨S, hS_sm, hS_val, hS_per⟩ :=
    evenChart (chordSumChart CI.c) 8 (chordSumChart_contDiff CI.c CI.smooth)
      (chordSumChart_even CI.c) (chordSumChart_per CI.c CI.per)
  obtain ⟨P, hP_sm, hP_val, hP_per⟩ :=
    evenChart (chordModChart CI.c) 8 (chordModChart_contDiff CI.c CI.smooth)
      (chordModChart_even CI.c) (chordModChart_per CI.c CI.per)
  -- the chart
  let W : ℝ → ℝ → ℝ → Work.RPV.PS := fun τ t ρ =>
    (((Complex.exp (-(Â τ t ρ : ℂ) * Complex.I) * S τ t ρ).im, Â τ t ρ),
     ((Complex.exp (-(Â τ t ρ : ℂ) * Complex.I) * S τ t ρ).re, P τ t ρ))
  have hW_sm : ContDiffOn ℝ 8 (fun z : ℝ × (ℝ × ℝ) => W z.1 z.2.1 z.2.2)
      (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ ×ˢ Set.univ) := by
    have htriple : ContDiffOn ℝ 8 (fun z : ℝ × (ℝ × ℝ) =>
        (Â z.1 z.2.1 z.2.2, S z.1 z.2.1 z.2.2, P z.1 z.2.1 z.2.2))
        (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ ×ˢ Set.univ) :=
      hA_sm.prodMk ((hS_sm.contDiffOn.mono (Set.subset_univ _)).prodMk
        (hP_sm.contDiffOn.mono (Set.subset_univ _)))
    have hpt : ContDiffOn ℝ 8 (fun v : ℝ × (ℂ × ℝ) =>
        (((Complex.exp (-(v.1 : ℂ) * Complex.I) * v.2.1).im, v.1),
         ((Complex.exp (-(v.1 : ℂ) * Complex.I) * v.2.1).re, v.2.2))) Set.univ := by
      have h1 : ContDiff ℝ 8 (fun v : ℝ × (ℂ × ℝ) =>
          Complex.exp (-(v.1 : ℂ) * Complex.I) * v.2.1) :=
        ((Complex.contDiff_exp.comp
          (((Complex.ofRealCLM.contDiff.comp contDiff_fst).neg).mul contDiff_const))).mul
          (contDiff_fst.comp contDiff_snd)
      exact (((Complex.imCLM.contDiff.comp h1).prodMk contDiff_fst).prodMk
        ((Complex.reCLM.contDiff.comp h1).prodMk (contDiff_snd.comp contDiff_snd))).contDiffOn
    have hcomp := hpt.comp htriple (fun z _ => Set.mem_univ _)
    dsimp only [W]
    exact hcomp
  -- the values on the chord annulus
  have hW_val : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ t, ∀ r ∈ Set.Ioc (0 : ℝ) (Real.pi / 2),
      W τ t (r ^ 2) = Work.RPB.chordSurf CI.c a τ t r := by
    intro τ hτ t r hr
    have hr0 : 0 < r := hr.1
    have hsq : Real.sqrt (r ^ 2) = r := Real.sqrt_sq hr0.le
    have hAv : Â τ t (r ^ 2) = a τ t r := hA_val τ hτ t r hr
    simp only [W]
    rw [hS_val τ t (r ^ 2) (by positivity), hP_val τ t (r ^ 2) (by positivity), hAv, hsq]
    unfold Work.RPB.chordSurf Work.RPV.chordPS chordSumChart chordModChart
    rfl
  -- the `2π`-quasiperiodicity
  have hW_per : ∀ τ t ρ, W τ (t + 2 * Real.pi) ρ = Work.RPV.Tk 1 (W τ t ρ) := by
    intro τ t ρ
    have hexp : Complex.exp (-(Â τ (t + 2 * Real.pi) ρ : ℂ) * Complex.I)
        = Complex.exp (-(Â τ t ρ : ℂ) * Complex.I) := by
      rw [hA_per τ t ρ]
      have hsplit : (-((Â τ t ρ + 2 * Real.pi : ℝ)) : ℂ) * Complex.I
          = (-(Â τ t ρ : ℂ) * Complex.I) - (2 * (Real.pi : ℂ) * Complex.I) := by
        push_cast; ring
      rw [hsplit, Complex.exp_sub, Complex.exp_two_pi_mul_I, div_one]
    simp only [W]
    rw [hS_per τ t ρ, hP_per τ t ρ, hexp, hA_per τ t ρ]
    simp only [Work.RPV.Tk, Int.cast_one, mul_one]
  -- `K₀ + 1` of the chart
  have hK0W : ∀ τ t ρ, Work.RPV.K0 (W τ t ρ) + 1 = P τ t ρ - ‖S τ t ρ‖ ^ 2 / 2 + 1 := by
    intro τ t ρ
    have hnorm : ‖Complex.exp (-(Â τ t ρ : ℂ) * Complex.I)‖ = 1 := by
      rw [show -(Â τ t ρ : ℂ) * Complex.I = ((-(Â τ t ρ) : ℝ) : ℂ) * Complex.I from by
        push_cast; ring]
      exact Complex.norm_exp_ofReal_mul_I (-(Â τ t ρ))
    have hsq : (Complex.exp (-(Â τ t ρ : ℂ) * Complex.I) * S τ t ρ).im ^ 2
        + (Complex.exp (-(Â τ t ρ : ℂ) * Complex.I) * S τ t ρ).re ^ 2 = ‖S τ t ρ‖ ^ 2 := by
      have h1 : (Complex.exp (-(Â τ t ρ : ℂ) * Complex.I) * S τ t ρ).im ^ 2
          + (Complex.exp (-(Â τ t ρ : ℂ) * Complex.I) * S τ t ρ).re ^ 2
          = Complex.normSq (Complex.exp (-(Â τ t ρ : ℂ) * Complex.I) * S τ t ρ) := by
        rw [Complex.normSq_apply]; ring
      rw [h1, ← Complex.sq_norm (Complex.exp (-(Â τ t ρ : ℂ) * Complex.I) * S τ t ρ),
        norm_mul, hnorm, one_mul]
    simp only [Work.RPV.K0, W]
    rw [hsq]
  -- the value at `ρ = 0`
  have hQ0 : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ t, Work.RPV.K0 (W τ t 0) + 1 = 0 := by
    intro τ hτ t
    rw [hK0W τ t 0, hS_val τ t 0 le_rfl, hP_val τ t 0 le_rfl, Real.sqrt_zero]
    unfold chordSumChart chordModChart
    simp only [add_zero, sub_zero]
    have hs2 : (Real.sqrt 2 : ℂ) * (Real.sqrt 2 : ℂ) = 2 := by
      rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num : (0:ℝ) ≤ 2)]
      norm_num
    have hne2 : (Real.sqrt 2 : ℂ) ≠ 0 := by
      rw [Complex.ofReal_ne_zero]
      exact ne_of_gt (Real.sqrt_pos.mpr (by norm_num))
    have hsum : (CI.c τ t + CI.c τ t) / (Real.sqrt 2 : ℂ) = (Real.sqrt 2 : ℂ) * CI.c τ t := by
      rw [div_eq_iff hne2]
      calc CI.c τ t + CI.c τ t = 2 * CI.c τ t := by ring
        _ = ((Real.sqrt 2 : ℂ) * (Real.sqrt 2)) * CI.c τ t := by rw [hs2]
        _ = (Real.sqrt 2 : ℂ) * CI.c τ t * (Real.sqrt 2) := by ring
    rw [hsum, norm_mul,
      show ‖(Real.sqrt 2 : ℂ)‖ = Real.sqrt 2 from by
        rw [Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg 2)]]
    have hsq2 : (Real.sqrt 2 * ‖CI.c τ t‖) ^ 2 = 2 * ‖CI.c τ t‖ ^ 2 := by
      rw [mul_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
    rw [hsq2]
    ring
  -- the uniform lower bound on the derivative at `0`
  obtain ⟨δ, hδpos, hδ⟩ := exists_delta_deriv_sq CI.c CI.smooth CI.per CI.imm
  -- the `ρ`-function whose sign is at stake, in globally smooth form
  let F : ℝ × (ℝ × ℝ) → ℝ := fun z => P z.1 z.2.1 z.2.2 + 1 - ‖S z.1 z.2.1 z.2.2‖ ^ 2 / 2
  have hF_eq : ∀ τ t ρ, F (τ, (t, ρ)) = Work.RPV.K0 (W τ t ρ) + 1 := by
    intro τ t ρ
    rw [hK0W τ t ρ]
    dsimp only [F]
    ring
  have hnorm2 : ContDiff ℝ 1 (fun z : ℝ × (ℝ × ℝ) => ‖S z.1 z.2.1 z.2.2‖ ^ 2) := by
    have hS1 : ContDiff ℝ 1 (fun z : ℝ × (ℝ × ℝ) => S z.1 z.2.1 z.2.2) :=
      hS_sm.of_le (by norm_num)
    have h1 : ContDiff ℝ 1 (fun z : ℝ × (ℝ × ℝ) => (S z.1 z.2.1 z.2.2).re) :=
      Complex.reCLM.contDiff.comp hS1
    have h2 : ContDiff ℝ 1 (fun z : ℝ × (ℝ × ℝ) => (S z.1 z.2.1 z.2.2).im) :=
      Complex.imCLM.contDiff.comp hS1
    have h := (h1.mul h1).add (h2.mul h2)
    simpa only [Complex.sq_norm, Complex.normSq_apply] using h
  have hF1 : ContDiff ℝ 1 F := by
    have hP1 : ContDiff ℝ 1 (fun z : ℝ × (ℝ × ℝ) => P z.1 z.2.1 z.2.2) :=
      hP_sm.of_le (by norm_num)
    dsimp only [F]
    exact (hP1.add contDiff_const).sub (hnorm2.div_const 2)
  have hFper : ∀ τ t ρ, F (τ, (t + 2 * Real.pi, ρ)) = F (τ, (t, ρ)) := by
    intro τ t ρ
    dsimp only [F]
    rw [hS_per τ t ρ, hP_per τ t ρ]
  have hF0 : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ t, F (τ, (t, 0)) = 0 := by
    intro τ hτ t
    rw [show F (τ, (t, 0)) = Work.RPV.K0 (W τ t 0) + 1 from hF_eq τ t 0, hQ0 τ hτ t]
  have hFD : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ t,
      δ ≤ deriv (fun s : ℝ => F (τ, (t, s))) 0 := by
    intro τ hτ t
    have hsmall : Set.Iio (Real.pi / 2) ∈ nhdsWithin (0 : ℝ) (Set.Ioi 0) :=
      nhdsWithin_le_nhds (Iio_mem_nhds (by linarith [Real.pi_pos]))
    have hev : (fun r : ℝ => (F (τ, (t, r ^ 2)) - F (τ, (t, 0))) / r ^ 2)
        =ᶠ[nhdsWithin (0 : ℝ) (Set.Ioi 0)] (fun r => ‖Work.RPB.halfChord CI.c τ t r‖ ^ 2) := by
      filter_upwards [self_mem_nhdsWithin, hsmall] with r hr hr2
      have hrpos : 0 < r := hr
      have h1 : F (τ, (t, r ^ 2)) = r ^ 2 * ‖Work.RPB.halfChord CI.c τ t r‖ ^ 2 := by
        rw [hF_eq τ t (r ^ 2), hW_val τ hτ t r ⟨hrpos, le_of_lt hr2⟩]
        exact K0_chordSurf CI.c a (ne_of_gt hrpos)
      rw [h1, hF0 τ hτ t, sub_zero]
      field_simp
    have hlim : Filter.Tendsto (fun r : ℝ => ‖Work.RPB.halfChord CI.c τ t r‖ ^ 2)
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (‖deriv (CI.c τ) t‖ ^ 2)) := by
      have hcont : ContinuousAt (fun r : ℝ => halfChordExt CI.c τ t r) 0 :=
        (((contDiff_halfChordExt CI.c CI.smooth).continuous.continuousAt).comp
          (f := fun r : ℝ => (τ, (t, r))) (x := (0 : ℝ)) (by fun_prop))
      have hlim0 : Filter.Tendsto (fun r : ℝ => halfChordExt CI.c τ t r)
          (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (deriv (CI.c τ) t)) := by
        have h := hcont.tendsto.mono_left (nhdsWithin_le_nhds (a := (0 : ℝ)) (s := Set.Ioi 0))
        rwa [halfChordExt_zero CI.c CI.smooth τ t] at h
      have hev2 : (fun r : ℝ => halfChordExt CI.c τ t r)
          =ᶠ[nhdsWithin (0 : ℝ) (Set.Ioi 0)] (fun r => Work.RPB.halfChord CI.c τ t r) := by
        filter_upwards [self_mem_nhdsWithin] with r hr
        exact halfChordExt_eq CI.c CI.smooth τ t r (ne_of_gt hr)
      exact Filter.Tendsto.congr' hev2 hlim0 |>.norm.pow 2
    have hslope : Filter.Tendsto
        (fun r : ℝ => (F (τ, (t, r ^ 2)) - F (τ, (t, 0))) / r ^ 2)
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (‖deriv (CI.c τ) t‖ ^ 2)) :=
      Filter.Tendsto.congr' hev.symm hlim
    have hdiff : DifferentiableAt ℝ (fun ρ : ℝ => F (τ, (t, ρ))) 0 := by
      have hsm : Differentiable ℝ F := hF1.differentiable_one
      have hslice : DifferentiableAt ℝ (fun ρ : ℝ => (τ, (t, ρ))) 0 :=
        (differentiableAt_const τ).prodMk ((differentiableAt_const t).prodMk differentiableAt_id)
      exact (hsm.differentiableAt (x := (τ, (t, 0)))).comp 0 hslice
    have hHas := hasDerivAt_of_tendsto_slope_sq hdiff hslope
    rw [hHas.deriv]
    exact hδ τ hτ t
  obtain ⟨ε, hεpos, hε⟩ := heps F δ hδpos hF1 hFper hF0 hFD
  refine ⟨9 * Real.pi ^ 2 / 16, by nlinarith [Real.pi_pos], ⟨W, ?_, hW_val, hW_per, ?_⟩⟩
  · exact hW_sm.mono (fun z hz => ⟨hz.1, trivial, trivial⟩)
  · refine ⟨min ε (9 * Real.pi ^ 2 / 16), lt_min hεpos (by positivity), min_le_right _ _, ?_⟩
    intro τ hτ t ρ hρ
    have hlt : F (τ, (t, ρ)) < 0 := hε τ hτ t ρ
      ⟨by linarith [hρ.1, min_le_left ε (9 * Real.pi ^ 2 / 16)], hρ.2⟩
    rwa [hF_eq τ t ρ] at hlt

/-! ## The phase lift: a strip-smooth, `2π`-quasiperiodic phase chart -/

/-- The regularised phase integrand is `2π`-periodic in `t` when `hc` is. -/
theorem regF_per (hc : ℝ → ℝ → ℝ → ℂ)
    (hc_sm : ContDiff ℝ ∞ (fun z : ℝ × (ℝ × ℝ) => hc z.1 z.2.1 z.2.2))
    (hc_per : ∀ τ t s, hc τ (t + 2 * Real.pi) s = hc τ t s) (ρa : ℝ) :
    ∀ τ t s, regF hc ρa τ (t + 2 * Real.pi) s = regF hc ρa τ t s := by
  intro τ t s
  have hpds : pds hc τ (t + 2 * Real.pi) s = pds hc τ t s := by
    rw [pds_eq_deriv hc hc_sm τ (t + 2 * Real.pi) s, pds_eq_deriv hc hc_sm τ t s]
    congr 1
    funext u
    exact hc_per τ t u
  unfold regF regNum regDen
  rw [hpds, hc_per τ t s]

/-- The chord phase `a` is `2π`-quasiperiodic in `t` also at `r = 0` (by continuity). -/
theorem chordPhase_zero_mono (c : ℝ → ℝ → ℂ) (a : ℝ → ℝ → ℝ → ℝ)
    (ha : Work.RPB.IsChordPhase c a) :
    ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ t, a τ (t + 2 * Real.pi) 0 = a τ t 0 + 2 * Real.pi := by
  intro τ hτ t
  have hle : nhdsWithin (0 : ℝ) (Set.Ioi 0) ≤ nhdsWithin (0 : ℝ) (Set.Ioo 0 Real.pi) :=
    nhdsWithin_le_iff.mpr (Ioo_mem_nhdsGT Real.pi_pos)
  have hcont : ∀ b : ℝ, ContinuousWithinAt (fun r : ℝ => a τ b r) (Set.Ioo (0 : ℝ) Real.pi) 0 := by
    intro b
    have hg : ContinuousWithinAt (fun r : ℝ => (τ, (b, r))) (Set.Ioo (0 : ℝ) Real.pi) 0 := by
      fun_prop
    exact (ha.1.continuousOn.continuousWithinAt ⟨hτ, trivial, ⟨le_rfl, Real.pi_pos.le⟩⟩).comp
      (f := fun r : ℝ => (τ, (b, r))) (x := (0 : ℝ)) hg
      (fun r hr => ⟨hτ, trivial, ⟨le_of_lt hr.1, le_of_lt hr.2⟩⟩)
  have hle' : nhdsWithin (0 : ℝ) (Set.Ioo 0 Real.pi) ≤ nhdsWithin (0 : ℝ) (Set.Ioi 0) :=
    nhdsWithin_mono (0 : ℝ) Set.Ioo_subset_Ioi_self
  haveI : (nhdsWithin (0 : ℝ) (Set.Ioo 0 Real.pi)).NeBot := by
    rw [le_antisymm hle' hle]
    exact nhdsWithin_Ioi_neBot (le_refl (0 : ℝ))
  have h1 : Filter.Tendsto (fun r : ℝ => a τ (t + 2 * Real.pi) r)
      (nhdsWithin (0 : ℝ) (Set.Ioo 0 Real.pi)) (nhds (a τ (t + 2 * Real.pi) 0)) :=
    (hcont (t + 2 * Real.pi)).tendsto
  have h2 : Filter.Tendsto (fun r : ℝ => a τ t r + 2 * Real.pi)
      (nhdsWithin (0 : ℝ) (Set.Ioo 0 Real.pi)) (nhds (a τ t 0 + 2 * Real.pi)) :=
    (hcont t).tendsto.add_const (2 * Real.pi)
  have hev : (fun r : ℝ => a τ (t + 2 * Real.pi) r)
      =ᶠ[nhdsWithin (0 : ℝ) (Set.Ioo 0 Real.pi)] (fun r : ℝ => a τ t r + 2 * Real.pi) := by
    filter_upwards [self_mem_nhdsWithin] with r hr
    exact ha.2.2.1 τ hτ t r hr
  exact tendsto_nhds_unique h1 (Filter.Tendsto.congr' hev.symm h2)

/-- **The strip-smooth even phase lift.**  Given the smooth even half-chord `hc` (non-vanishing on
`|r| < π`) and the chord phase `a`, there is a function `Â` of `(τ,t,ρ)`, `C^8` on the strip
`τ ∈ [0,1]`, `2π`-quasiperiodic in `t` (with monodromy `+2π`), reproducing the phase:
`Â τ t (r²) = a τ t r` for `0 < r ≤ π/2`. -/
theorem phaseLiftStrip (c : ℝ → ℝ → ℂ) (a : ℝ → ℝ → ℝ → ℝ) (ha : Work.RPB.IsChordPhase c a)
    (hc : ℝ → ℝ → ℝ → ℂ)
    (hc_sm : ContDiff ℝ ∞ (fun z : ℝ × (ℝ × ℝ) => hc z.1 z.2.1 z.2.2))
    (hc_even : ∀ τ t r, hc τ t (-r) = hc τ t r)
    (hc_per : ∀ τ t r, hc τ (t + 2 * Real.pi) r = hc τ t r)
    (hc_half : ∀ τ t r, r ≠ 0 → hc τ t r = Work.RPB.halfChord c τ t r)
    (hne : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ t r, |r| < Real.pi → hc τ t r ≠ 0) :
    ∃ Â : ℝ → ℝ → ℝ → ℝ,
      ContDiffOn ℝ 8 (fun z : ℝ × (ℝ × ℝ) => Â z.1 z.2.1 z.2.2)
        (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ ×ˢ Set.univ) ∧
      (∀ τ t ρ, Â τ (t + 2 * Real.pi) ρ = Â τ t ρ + 2 * Real.pi) ∧
      (∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ t, ∀ r ∈ Set.Ioc (0 : ℝ) (Real.pi / 2),
        Â τ t (r ^ 2) = a τ t r) := by
  set ρa : ℝ := 3 * Real.pi / 4 with hρadef
  have hρapos : 0 < ρa := by rw [hρadef]; linarith [Real.pi_pos]
  have hρapi : ρa < Real.pi := by rw [hρadef]; linarith [Real.pi_pos]
  -- the regularised integrand
  have hreg_sm : ContDiff ℝ ∞ (fun z : ℝ × (ℝ × ℝ) => regF hc ρa z.1 z.2.1 z.2.2) :=
    regF_contDiff hc ρa hc_sm (fun τ t s =>
      regDen_ne_zero hc Real.pi hne ρa (7 * Real.pi / 8)
        (by rw [hρadef]; linarith [Real.pi_pos]) (by linarith [Real.pi_pos]) τ t s)
  have hreg_odd : ∀ τ t s, regF hc ρa τ t (-s) = -regF hc ρa τ t s :=
    fun τ t s => regF_neg hc hc_sm hc_even ρa τ t s
  have hreg_per : ∀ τ t s, regF hc ρa τ (t + 2 * Real.pi) s = regF hc ρa τ t s :=
    regF_per hc hc_sm hc_per ρa
  -- the primitive of the phase derivative, in `ρ`-free form
  let L : ℝ → ℝ → ℝ → ℝ := fun τ t r => r * ∫ u in (0 : ℝ)..1, regF hc ρa τ t (r * u)
  have hL_sm : ContDiff ℝ ∞ (fun z : ℝ × (ℝ × ℝ) => L z.1 z.2.1 z.2.2) := by
    have hint : ContDiff ℝ ∞ (fun z : ℝ × (ℝ × ℝ) =>
        ∫ u in (0 : ℝ)..1, regF hc ρa z.1 z.2.1 (z.2.2 * u)) := by
      have h1 : ContDiff ℝ ∞ (fun q : (ℝ × (ℝ × ℝ)) × ℝ =>
          regF hc ρa q.1.1 q.1.2.1 (q.1.2.2 * q.2)) := by
        have hf1 : ContDiff ℝ ∞ (fun q : (ℝ × (ℝ × ℝ)) × ℝ => q.1.1) :=
          (contDiff_fst : ContDiff ℝ ∞ (fun q : (ℝ × (ℝ × ℝ)) × ℝ => q.1)).fst
        have hf2 : ContDiff ℝ ∞ (fun q : (ℝ × (ℝ × ℝ)) × ℝ => q.1.2.1) :=
          ((contDiff_fst : ContDiff ℝ ∞ (fun q : (ℝ × (ℝ × ℝ)) × ℝ => q.1)).snd).fst
        have hf3 : ContDiff ℝ ∞ (fun q : (ℝ × (ℝ × ℝ)) × ℝ => q.1.2.2) :=
          ((contDiff_fst : ContDiff ℝ ∞ (fun q : (ℝ × (ℝ × ℝ)) × ℝ => q.1)).snd).snd
        have hs2 : ContDiff ℝ ∞ (fun q : (ℝ × (ℝ × ℝ)) × ℝ => q.2) :=
          (contDiff_snd : ContDiff ℝ ∞ (fun q : (ℝ × (ℝ × ℝ)) × ℝ => q.2))
        exact hreg_sm.comp (hf1.prodMk (hf2.prodMk (hf3.mul hs2)))
      exact Work.RPA3.contDiff_param_intervalIntegral ⊤
        (fun q : ℝ × (ℝ × ℝ) => fun u : ℝ => regF hc ρa q.1 q.2.1 (q.2.2 * u)) h1 0 1
    dsimp only [L]
    exact ((contDiff_snd : ContDiff ℝ ∞ (fun z : ℝ × (ℝ × ℝ) => z.2)).snd).mul hint
  have hL_even : ∀ τ t r, L τ t (-r) = L τ t r := by
    intro τ t r
    dsimp only [L]
    rcases eq_or_ne r 0 with hr | hr
    · rw [hr, neg_zero]
    · have hfun : (fun u : ℝ => regF hc ρa τ t ((-r) * u))
          = (fun u : ℝ => -regF hc ρa τ t (r * u)) := by
        funext u
        rw [show (-r) * u = -(r * u) by ring, hreg_odd]
      rw [hfun, intervalIntegral.integral_neg]
      ring
  have hL_per : ∀ τ t r, L τ (t + 2 * Real.pi) r = L τ t r := by
    intro τ t r
    dsimp only [L]
    rw [show (fun u : ℝ => regF hc ρa τ (t + 2 * Real.pi) (r * u))
        = (fun u : ℝ => regF hc ρa τ t (r * u)) from by
      funext u; exact hreg_per τ t (r * u)]
  -- the identity `L = a - a(·,0)` on the strip
  have hL_eq : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ t, ∀ r, 0 < r → r < ρa →
      L τ t r = a τ t r - a τ t 0 := by
    intro τ hτ t r hr0 hrρ
    have hrpi : r < Real.pi := lt_trans hrρ hρapi
    -- the substitution `r ∫_0^1 f (r u) du = ∫_0^r f`
    have hsub : r * ∫ u in (0 : ℝ)..1, regF hc ρa τ t (r * u)
        = ∫ s in (0 : ℝ)..r, regF hc ρa τ t s := by
      rw [intervalIntegral.integral_comp_mul_left (fun s : ℝ => regF hc ρa τ t s)
        (ne_of_gt hr0), mul_zero, mul_one]
      rw [smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ (ne_of_gt hr0), one_mul]
    -- the fundamental theorem of calculus for the phase
    have hslice : ContDiffOn ℝ 1 (fun s : ℝ => a τ t s) (Set.Icc (0 : ℝ) r) := by
      have hg : ContDiffOn ℝ 1 (fun s : ℝ => (τ, (t, s))) (Set.Icc (0 : ℝ) r) := by
        apply ContDiff.contDiffOn; fun_prop
      have hmaps : Set.MapsTo (fun s : ℝ => (τ, (t, s))) (Set.Icc (0 : ℝ) r)
          (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ ×ˢ Set.Icc (0 : ℝ) Real.pi) :=
        fun s hs => ⟨hτ, trivial, ⟨hs.1, le_of_lt (lt_of_le_of_lt hs.2 hrpi)⟩⟩
      exact (ha.1.of_le (by simp)).comp hg hmaps
    have haeq : ∫ s in (0 : ℝ)..r, deriv (fun s : ℝ => a τ t s) s
        = ∫ s in (0 : ℝ)..r, regF hc ρa τ t s := by
      refine intervalIntegral.integral_congr_ae ?_
      filter_upwards [MeasureTheory.volume.ae_ne (0 : ℝ)] with s hs hsI
      rw [Set.uIoc_of_le (le_of_lt hr0)] at hsI
      have hs0 : 0 < s := hsI.1
      have hsr : s ≤ r := hsI.2
      have hspi : s < Real.pi := lt_of_le_of_lt hsr hrpi
      rw [phaseDeriv_eq c a ha hc hc_sm hc_half hτ ⟨hs0, hspi⟩
        (hne τ hτ t s (by rw [abs_of_pos hs0]; exact hspi)), regF_eq hc hc_sm ρa hτ]
      rw [abs_of_pos hs0]
      exact lt_of_le_of_lt hsr hrρ
    have hftc := intervalIntegral.integral_deriv_of_contDiffOn_Icc hslice (le_of_lt hr0)
    dsimp only [L]
    rw [hsub, ← haeq, hftc]
  -- the even `ρ`-chart of `L`
  obtain ⟨Ĝ, hĜ_sm, hĜ_val, hĜ_per⟩ := evenChart L 8 hL_sm hL_even hL_per
  -- the global, `2π`-quasiperiodic "constant" part of the chart
  let φ : ℝ → ℝ → ℝ := fun τ t => if τ ∈ Set.Icc (0 : ℝ) 1 then a τ t 0 else t
  have hφ_on : ContDiffOn ℝ 8 (fun z : ℝ × (ℝ × ℝ) => φ z.1 z.2.1)
      (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ) := by
    have h1 : ContDiffOn ℝ 8 (fun z : ℝ × (ℝ × ℝ) => a z.1 z.2.1 0)
        (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ) := by
      have hg : ContDiffOn ℝ 8 (fun z : ℝ × (ℝ × ℝ) => (z.1, (z.2.1, (0 : ℝ))))
          (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ) := by
        apply ContDiff.contDiffOn; fun_prop
      have hmaps : Set.MapsTo (fun z : ℝ × (ℝ × ℝ) => (z.1, (z.2.1, (0 : ℝ))))
          (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ)
          (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ ×ˢ Set.Icc (0 : ℝ) Real.pi) :=
        fun z hz => ⟨hz.1, trivial, ⟨le_rfl, Real.pi_pos.le⟩⟩
      exact (ha.1.of_le (by simp)).comp hg hmaps
    refine h1.congr (fun z hz => ?_)
    show (if z.1 ∈ Set.Icc (0 : ℝ) 1 then a z.1 z.2.1 0 else z.2.1) = a z.1 z.2.1 0
    rw [if_pos hz.1]
  have hφ_lift : ContDiffOn ℝ 8 (fun z : ℝ × (ℝ × ℝ) => φ z.1 z.2.1)
      (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ ×ˢ Set.univ) := by
    simpa only [Set.univ_prod_univ] using hφ_on
  have hφ_mono : ∀ τ t, φ τ (t + 2 * Real.pi) = φ τ t + 2 * Real.pi := by
    intro τ t
    by_cases hτ : τ ∈ Set.Icc (0 : ℝ) 1
    · show (if τ ∈ Set.Icc (0 : ℝ) 1 then a τ (t + 2 * Real.pi) 0 else t + 2 * Real.pi)
          = (if τ ∈ Set.Icc (0 : ℝ) 1 then a τ t 0 else t) + 2 * Real.pi
      rw [if_pos hτ, if_pos hτ, chordPhase_zero_mono c a ha τ hτ t]
    · show (if τ ∈ Set.Icc (0 : ℝ) 1 then a τ (t + 2 * Real.pi) 0 else t + 2 * Real.pi)
          = (if τ ∈ Set.Icc (0 : ℝ) 1 then a τ t 0 else t) + 2 * Real.pi
      rw [if_neg hτ, if_neg hτ]
  have hφ_val : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ t, φ τ t = a τ t 0 := by
    intro τ hτ t
    show (if τ ∈ Set.Icc (0 : ℝ) 1 then a τ t 0 else t) = a τ t 0
    rw [if_pos hτ]
  refine ⟨fun τ t ρ => Ĝ τ t ρ + φ τ t, ?_, ?_, ?_⟩
  · -- smoothness on the strip
    have hĜ : ContDiffOn ℝ 8 (fun z : ℝ × (ℝ × ℝ) => Ĝ z.1 z.2.1 z.2.2)
        (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ ×ˢ Set.univ) :=
      hĜ_sm.contDiffOn.mono (Set.subset_univ _)
    exact hĜ.add hφ_lift
  · -- the monodromy
    intro τ t ρ
    show Ĝ τ (t + 2 * Real.pi) ρ + φ τ (t + 2 * Real.pi) = Ĝ τ t ρ + φ τ t + 2 * Real.pi
    rw [hĜ_per τ t ρ, hφ_mono τ t]
    ring
  · -- the value
    intro τ hτ t r hr
    have hr0 : 0 < r := hr.1
    have hrlt : r < ρa := by rw [hρadef]; linarith [hr.2, Real.pi_pos]
    have hsq : Real.sqrt (r ^ 2) = r := Real.sqrt_sq hr0.le
    show Ĝ τ t (r ^ 2) + φ τ t = a τ t r
    rw [hĜ_val τ t (r ^ 2) (by positivity), hsq, hL_eq τ hτ t r hr0 hrlt, hφ_val τ hτ t]
    ring

theorem chordSurf_rhoChart_full (CI : Work.RPV.CurveIsotopy) (a : ℝ → ℝ → ℝ → ℝ)
    (ha : Work.RPB.IsChordPhase CI.c a) :
    ∃ ρ₀ : ℝ, Real.pi ^ 2 / 4 < ρ₀ ∧ ∃ W : ℝ → ℝ → ℝ → Work.RPV.PS,
      ContDiffOn ℝ 8 (fun z : ℝ × (ℝ × ℝ) => W z.1 z.2.1 z.2.2)
        (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ ×ˢ Set.Ioo (-ρ₀) ρ₀) ∧
      (∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ t : ℝ, ∀ r ∈ Set.Ioc (0 : ℝ) (Real.pi / 2),
        W τ t (r ^ 2) = Work.RPB.chordSurf CI.c a τ t r) ∧
      (∀ τ t ρ, W τ (t + 2 * Real.pi) ρ = Work.RPV.Tk 1 (W τ t ρ)) ∧
      (∃ ε : ℝ, 0 < ε ∧ ε ≤ ρ₀ ∧
        ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ t : ℝ, ∀ ρ ∈ Set.Ioo (-ε) 0,
          Work.RPV.K0 (W τ t ρ) + 1 < 0) := by
  obtain ⟨hc, hc_sm, hc_even, hc_per, hc_zero, hc_half⟩ :=
    halfChordSmooth CI.c CI.smooth CI.per
  have hne : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ t r, |r| < Real.pi → hc τ t r ≠ 0 :=
    hc_ne_zero hc_zero hc_half CI.inj CI.imm
  obtain ⟨Â, hA_sm, hA_per, hA_val⟩ :=
    phaseLiftStrip CI.c a ha hc hc_sm hc_even hc_per hc_half hne
  exact assembly CI a Â hA_sm hA_per hA_val
    (fun F δ hδ hF hper h0 hD =>
      Work.RPB.B5.exists_eps_neg_of_deriv_pos F δ hδ hF hper h0 hD)

end Work.RPB.B5
