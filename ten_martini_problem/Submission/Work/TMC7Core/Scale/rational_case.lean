import Mathlib
import Submission.Work.TMC7Core.Defs
import Submission.Work.TMC7Core.Cocycle
import Submission.Work.TMC7Core.Rat
import Submission.Work.TMC7Core.Solutions.lyap_periodic
import Submission.Work.TMC7Core.Solutions.iterC_qpow
import Submission.Work.TMC7Core.LDT
import Submission.Work.TMC7Core.Scale.hasLEBound_Icc
import Submission.Work.TMC7Core.Scale.scale_step_avg
import Submission.Work.TMC7Core.Cocycle.intervalIntegrable_log_frob

/-!
# The rational-frequency case of `prop9_main` (interface)

For rational `α` the Bourgain--Jitomirskaya scale *tower* is not available (the approximant
sequence used for the summable family of errors terminates), and the window/pigeonhole issue
disappears for a different reason.  What is needed instead is the classical **Floquet**
picture of the periodic problem:

* if `α = p/q` then the `q`-step transfer matrix `A_q(x) = iterC (p/q) lam E q x` is
  `1`-periodic in `x` and `iterC (p/q) lam E (q*k) x = (A_q x)^k`
  (`Solutions/iterC_qpow.iterC_qpow`, proved);
* the Lyapunov exponent is the `x`-average of `log (rhoSL (tr A_q (x)))`
  (`Solutions/lyap_periodic.lyap_periodic`, proved);
* hence `lyap ((p:ℝ)/q) lam E > 0` is the statement that the monodromy has
  `rhoSL (tr A_q x) > 1` on a set of positive measure, and for the periodic almost Mathieu
  operator this is equivalent to `E` lying outside the periodic spectrum `Σ(p/q)`, i.e. to the
  cocycle being **uniformly hyperbolic**:
  `∃ ρ > 1, ∀ x, ρ ≤ rhoSL (tr A_q x)`.

Given uniform hyperbolicity, diagonalising `A_q x = U_x diag(ρ_x, ρ_x⁻¹) U_x⁻¹` gives the
*no-superexponential* power bound `log‖(A_q x)^k‖_F ≤ k log ρ_x + log (‖U_x‖_F‖U_x⁻¹‖_F)`, and
`‖U_x‖_F ‖U_x⁻¹‖_F` is bounded on the circle (the eigenprojections of a uniformly hyperbolic
continuous family are continuous, and the circle is compact).  Averaging against the Floquet
formula then gives **exponential decay of the excesses at the multiples of `q`**, which is the
form in which the rational case feeds `prop9_main` (take `N₀ = m q`; the window
`((κ²)⁻¹+1)^{⌈C⌉+2} q` contains such a multiple as soon as `κ` is small, and `m ≈ κ^{-2⌈C⌉-4}`
makes `ρ^{-m}` far smaller than `e^{-cκq/4}` because `log ρ ≈ q · lyap`).

The two statements below are the interface: the first is the Floquet/hyperbolicity input, the
second its quantitative consequence (the excess bound consumed by `prop9_main`).
-/

open MeasureTheory Filter Topology Set
open LeanEval.Analysis.TenMartini

noncomputable section

namespace Work.TMC7Core.Scale

open Work.TMC7Core

/-- Local form of `|x + y| ≤ |x| + |y|`. -/
theorem abs_add_le_real' (x y : ℝ) : |x + y| ≤ |x| + |y| := by
  rw [abs_le]
  constructor
  · linarith [neg_abs_le x, neg_abs_le y]
  · linarith [le_abs_self x, le_abs_self y]

/-- Three-term triangle inequality. -/
theorem abs_le_three' (a b c : ℝ) : |a + b + c| ≤ |a| + |b| + |c| := by
  have h1 := abs_add_le_real' a b
  have h2 := abs_add_le_real' (a + b) c
  linarith [h1, h2]

/-- `HasLEBound` bounds every finite-scale average at energies of `K` from above.
(Self-contained here, so that this module does not depend on `Scale/prop9_final`.) -/
theorem hasLEBound_lyapAvg_le {lam : ℝ} {Kset : Set ℝ} {C₀ : ℝ} (hC₀ : HasLEBound lam Kset C₀)
    {E : ℝ} (hE : E ∈ Kset) (α : ℝ) (N : ℕ) : lyapAvg α lam (E : ℂ) N ≤ C₀ := by
  rw [lyapAvg_eq_integral_uAvg]
  have hint : IntervalIntegrable (fun x : ℝ => uAvg α lam (E : ℂ) N x) volume (0 : ℝ) 1 := by
    rcases Nat.eq_zero_or_pos N with h | h
    · subst h
      have : (fun x : ℝ => uAvg α lam (E : ℂ) 0 x) = fun _ => (0 : ℝ) := by
        funext x; simp [uAvg]
      rw [this]
      exact intervalIntegrable_const
    · have hN : ((N : ℕ) : ℝ) ≠ 0 := by positivity
      have := (Cocycle.intervalIntegrable_log_frob α lam (E : ℂ) N).div_const ((N : ℕ) : ℝ)
      simpa [uAvg, div_eq_inv_mul] using this
  have hmono : (∫ x in (0 : ℝ)..1, uAvg α lam (E : ℂ) N x) ≤ ∫ x in (0 : ℝ)..1, C₀ := by
    refine intervalIntegral.integral_mono_on (by norm_num) hint intervalIntegrable_const ?_
    intro x _
    exact hC₀.2 E hE α N x
  simpa using hmono

/-! ## The endgame arithmetic (structural half)

In `rat_defect_of_rate` the three error terms are

* `K·(1+log(mN₀))/(mN₀)` — the rate term (the only one carrying the unknown constant `K`),
* `4C₀/m` — the middle term, killed by taking the multiplier maximal,
* `(4C₀+1)·e^{-cκq/2}` — the scale-step error.

This lemma disposes of the last two *unconditionally*: in the small-error case
`(12C₀+1000)e^{-cκq/4} ≤ C₀` (i.e. `e^{-cκq/4} < 1/12`) and with the maximal multiplier
`e^{cκq/2} ≤ 2m`, their sum is at most half the target — in fact at most `(C₀+1/12)e^{-cκq/4}`,
against the target `(6C₀+500)e^{-cκq/4}`.  Only the rate term is left, and it is below the other
half of the target exactly when `K` is dominated by `C₀e^{cκq/4}` — the single inequality that
has to be supplied by a lower bound on `q` (or checked directly). -/
theorem rat_endgame_structural (c κ q C₀ m : ℝ)
    (hc : 0 < c) (hc1 : c ≤ 1) (hκ : 0 < κ) (hκ1 : κ ≤ 1 / 100) (hC₀ : 0 < C₀)
    (hq : 1 ≤ q) (hm : 3 ≤ m)
    (hmbig : Real.exp (c * κ * q / 2) ≤ 2 * m)
    (hsmall : (12 * C₀ + 1000) * Real.exp (-(c * κ * q / 4)) ≤ C₀) :
    4 * C₀ / m + (4 * C₀ + 1) * Real.exp (-(c * κ * q / 2))
      ≤ (1 / 2) * ((12 * C₀ + 1000) * Real.exp (-(c * κ * q / 4))) := by
  have hmpos : 0 < m := by linarith
  have hden : 0 < 12 * C₀ + 1000 := by linarith
  have hexp4 : 0 < Real.exp (-(c * κ * q / 4)) := Real.exp_pos _
  -- `e^{-cκq/4} < 1/12`
  have hlt : Real.exp (-(c * κ * q / 4)) < 1 / 12 := by
    have h1 : Real.exp (-(c * κ * q / 4)) ≤ C₀ / (12 * C₀ + 1000) := by
      rw [le_div_iff₀ hden]; linarith [hsmall]
    have h2 : C₀ / (12 * C₀ + 1000) < 1 / 12 := by
      rw [div_lt_div_iff₀ hden (by norm_num : (0 : ℝ) < 12)]
      linarith
    linarith
  -- `e^{-cκq/2} = (e^{-cκq/4})^2 ≤ e^{-cκq/4}/12`
  have hsq : Real.exp (-(c * κ * q / 2)) = Real.exp (-(c * κ * q / 4)) ^ 2 := by
    rw [← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  have hE3 : Real.exp (-(c * κ * q / 2)) ≤ Real.exp (-(c * κ * q / 4)) / 12 := by
    rw [hsq]
    nlinarith [hlt, hexp4]
  -- `1/m ≤ 2 e^{-cκq/2}`
  have hinv : 1 / m ≤ 2 * Real.exp (-(c * κ * q / 2)) := by
    have h1 : 1 ≤ 2 * m * Real.exp (-(c * κ * q / 2)) := by
      have hmul := mul_le_mul_of_nonneg_right hmbig (le_of_lt (Real.exp_pos (-(c * κ * q / 2))))
      have hprod : Real.exp (c * κ * q / 2) * Real.exp (-(c * κ * q / 2)) = 1 := by
        rw [← Real.exp_add, show c * κ * q / 2 + -(c * κ * q / 2) = 0 by ring, Real.exp_zero]
      linarith [hmul, hprod.le, hprod.ge]
    rw [div_le_iff₀ hmpos]
    linarith [h1]
  have h2C₀ : 4 * C₀ / m ≤ 8 * C₀ * (Real.exp (-(c * κ * q / 4)) / 12) := by
    have h := mul_le_mul_of_nonneg_left hinv (by positivity : (0 : ℝ) ≤ 4 * C₀)
    have heq : 4 * C₀ * (2 * Real.exp (-(c * κ * q / 2))) = 8 * C₀ * Real.exp (-(c * κ * q / 2)) := by
      ring
    have h' : 4 * C₀ / m ≤ 8 * C₀ * Real.exp (-(c * κ * q / 2)) := by
      have : 4 * C₀ / m = 4 * C₀ * (1 / m) := by ring
      rw [this]; linarith [h, heq.le, heq.ge]
    have hle : 8 * C₀ * Real.exp (-(c * κ * q / 2))
        ≤ 8 * C₀ * (Real.exp (-(c * κ * q / 4)) / 12) :=
      mul_le_mul_of_nonneg_left hE3 (by positivity)
    linarith [h', hle]
  have h3 : (4 * C₀ + 1) * Real.exp (-(c * κ * q / 2))
      ≤ (4 * C₀ + 1) * (Real.exp (-(c * κ * q / 4)) / 12) :=
    mul_le_mul_of_nonneg_left hE3 (by positivity)
  have htotal : 4 * C₀ / m + (4 * C₀ + 1) * Real.exp (-(c * κ * q / 2))
      ≤ (C₀ + 1 / 12) * Real.exp (-(c * κ * q / 4)) := by
    have hsum : 8 * C₀ * (Real.exp (-(c * κ * q / 4)) / 12)
        + (4 * C₀ + 1) * (Real.exp (-(c * κ * q / 4)) / 12)
        = (C₀ + 1 / 12) * Real.exp (-(c * κ * q / 4)) := by ring
    linarith [h2C₀, h3, hsum.le, hsum.ge]
  have htarget : (C₀ + 1 / 12) * Real.exp (-(c * κ * q / 4))
      ≤ (1 / 2) * ((12 * C₀ + 1000) * Real.exp (-(c * κ * q / 4))) := by
    have : C₀ + 1 / 12 ≤ (1 / 2) * (12 * C₀ + 1000) := by linarith
    nlinarith [mul_le_mul_of_nonneg_right this (le_of_lt hexp4)]
  linarith [htotal, htarget]

/-! ## The assembly wiring (rational case, pointwise)

The following lemma is the whole rational-case assembly: one application of the scale step
(`AvgStep.scale_step_avg`, [BJ] Lemma 6) at the base scale `N₀ = M·q` with the *maximal*
multiplier `m`, plus the delegated polynomial rate evaluated at the huge scale `m·N₀`.

The scale step gives, with `X = lyap + L_{N₀} - 2L_{2N₀}` and `R = L_{mN₀} - lyap`,

  `|X + R - (2/m)(L_{N₀} - L_{2N₀})| ≤ (4C₀+1)·e^{-cκq/2}`,

hence `|X| ≤ R + (4C₀/m) + (4C₀+1)e^{-cκq/2}`.  Since `R` is the excess at the huge scale
`m·N₀` with `m ≈ e^{cκq/2}`, the polynomial rate makes `R` exponentially small, and only the
elementary bound `|L_{N₀} - L_{2N₀}| ≤ 2C₀` is needed for the middle term.  The hypothesis
`hrate` is the polynomial rate of `Scale/rat_excess_decay_of_hyperbolic` instantiated at the
single scale `m·N₀` (which is a multiple of the period since `N₀ = M·q`), and `harith` is the
numerical endgame comparing the three terms with the target. -/
theorem rat_defect_of_rate (lam : ℝ) (Kset : Set ℝ) (c C C₀ : ℝ)
    (hLDT : HasLDTOn lam Kset c C) (hC₀ : HasLEBound lam Kset C₀) (hc1 : c ≤ 1)
    (κ : ℝ) (hκ : 0 < κ) (hκ1 : κ ≤ 1 / 100) (E : ℝ) (hE : E ∈ Kset)
    (a : ℤ) (q : ℕ) (hq : 1 ≤ q) (hcop : Nat.Coprime (Int.natAbs a) q)
    (hqC : C * (κ ^ 2)⁻¹ ≤ (q : ℝ))
    (N₀ : ℕ) (hN₀ : C * (κ ^ 2)⁻¹ * (q : ℝ) ≤ (N₀ : ℝ))
    (hL : 100 * κ < lyapAvg ((a : ℝ) / (q : ℝ)) lam (E : ℂ) N₀)
    (hpair : (9 / 10) * lyapAvg ((a : ℝ) / (q : ℝ)) lam (E : ℂ) N₀
      < lyapAvg ((a : ℝ) / (q : ℝ)) lam (E : ℂ) (2 * N₀))
    (m : ℕ) (hm : 3 ≤ m) (hmq : (m : ℝ) < Real.exp (c * κ * (q : ℝ) / 2))
    (K : ℝ) (hK : 0 ≤ K)
    (hrate : lyapAvg ((a : ℝ) / (q : ℝ)) lam (E : ℂ) (m * N₀)
        - lyap ((a : ℝ) / (q : ℝ)) lam (E : ℂ)
        ≤ K * (1 + Real.log ((m : ℝ) * (N₀ : ℝ))) / ((m : ℝ) * (N₀ : ℝ)))
    (harith : K * (1 + Real.log ((m : ℝ) * (N₀ : ℝ))) / ((m : ℝ) * (N₀ : ℝ))
        + (1 / (m : ℝ)) * (4 * C₀) + (4 * C₀ + 1) * Real.exp (-(c * κ * (q : ℝ) / 2))
        < (12 * C₀ + 1000) * Real.exp (-(c * κ * (q : ℝ) / 4))) :
    |lyap ((a : ℝ) / (q : ℝ)) lam (E : ℂ) + lyapAvg ((a : ℝ) / (q : ℝ)) lam (E : ℂ) N₀
        - 2 * lyapAvg ((a : ℝ) / (q : ℝ)) lam (E : ℂ) (2 * N₀)|
      < (12 * C₀ + 1000) * Real.exp (-(c * κ * (q : ℝ) / 4)) := by
  have hqpos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have hα : |(a : ℝ) / (q : ℝ) - (a : ℝ) / (q : ℝ)| < 1 / ((q : ℝ) ^ 2) := by
    rw [sub_self, abs_zero]
    positivity
  have hstep := AvgStep.scale_step_avg lam Kset c C C₀ hLDT hC₀ hc1 κ hκ hκ1 E hE
    ((a : ℝ) / (q : ℝ)) a q hq hcop hqC hα N₀ hN₀ hL hpair m hm hmq
  -- elementary bounds on the two finite-scale averages
  have hle2 : lyapAvg ((a : ℝ) / (q : ℝ)) lam (E : ℂ) (2 * N₀) ≤ C₀ :=
    hasLEBound_lyapAvg_le hC₀ hE _ (2 * N₀)
  have hge2 : 0 ≤ lyapAvg ((a : ℝ) / (q : ℝ)) lam (E : ℂ) (2 * N₀) := by
    rcases Nat.eq_zero_or_pos (2 * N₀) with h | h
    · rw [h]; simp [lyapAvg]
    · have h' : 2 * N₀ - 1 + 1 = 2 * N₀ := by omega
      simpa [h'] using lyapAvg_nonneg' ((a : ℝ) / (q : ℝ)) lam (E : ℂ) (2 * N₀ - 1)
  have hle1 : lyapAvg ((a : ℝ) / (q : ℝ)) lam (E : ℂ) N₀ ≤ C₀ :=
    hasLEBound_lyapAvg_le hC₀ hE _ N₀
  have hΔ : |lyapAvg ((a : ℝ) / (q : ℝ)) lam (E : ℂ) N₀
      - lyapAvg ((a : ℝ) / (q : ℝ)) lam (E : ℂ) (2 * N₀)| ≤ 2 * C₀ := by
    rw [abs_le]; constructor <;> linarith
  have hmpos : (0 : ℝ) < (m : ℝ) := by
    have : (0 : ℕ) < m := by omega
    exact_mod_cast this
  -- the algebraic identity isolating the defect
  have hkey : lyapAvg ((a : ℝ) / (q : ℝ)) lam (E : ℂ) (m * N₀)
        + (1 - 2 / (m : ℝ)) * lyapAvg ((a : ℝ) / (q : ℝ)) lam (E : ℂ) N₀
        - (2 - 2 / (m : ℝ)) * lyapAvg ((a : ℝ) / (q : ℝ)) lam (E : ℂ) (2 * N₀)
      = (lyap ((a : ℝ) / (q : ℝ)) lam (E : ℂ)
          + lyapAvg ((a : ℝ) / (q : ℝ)) lam (E : ℂ) N₀
          - 2 * lyapAvg ((a : ℝ) / (q : ℝ)) lam (E : ℂ) (2 * N₀))
        + (lyapAvg ((a : ℝ) / (q : ℝ)) lam (E : ℂ) (m * N₀)
            - lyap ((a : ℝ) / (q : ℝ)) lam (E : ℂ))
        - (2 / (m : ℝ)) * (lyapAvg ((a : ℝ) / (q : ℝ)) lam (E : ℂ) N₀
            - lyapAvg ((a : ℝ) / (q : ℝ)) lam (E : ℂ) (2 * N₀)) := by ring
  rw [hkey] at hstep
  set X : ℝ := lyap ((a : ℝ) / (q : ℝ)) lam (E : ℂ)
    + lyapAvg ((a : ℝ) / (q : ℝ)) lam (E : ℂ) N₀
    - 2 * lyapAvg ((a : ℝ) / (q : ℝ)) lam (E : ℂ) (2 * N₀) with hXdef
  set R : ℝ := lyapAvg ((a : ℝ) / (q : ℝ)) lam (E : ℂ) (m * N₀)
    - lyap ((a : ℝ) / (q : ℝ)) lam (E : ℂ) with hRdef
  have hthird : |(2 / (m : ℝ)) * (lyapAvg ((a : ℝ) / (q : ℝ)) lam (E : ℂ) N₀
      - lyapAvg ((a : ℝ) / (q : ℝ)) lam (E : ℂ) (2 * N₀))| ≤ (1 / (m : ℝ)) * (4 * C₀) := by
    have hm2 : (0 : ℝ) ≤ 2 / (m : ℝ) := by positivity
    rw [abs_mul, abs_of_nonneg hm2]
    calc (2 / (m : ℝ)) * |lyapAvg ((a : ℝ) / (q : ℝ)) lam (E : ℂ) N₀
            - lyapAvg ((a : ℝ) / (q : ℝ)) lam (E : ℂ) (2 * N₀)|
        ≤ (2 / (m : ℝ)) * (2 * C₀) := mul_le_mul_of_nonneg_left hΔ hm2
      _ = (1 / (m : ℝ)) * (4 * C₀) := by ring
  -- triangle inequality to isolate `|X|`
  have htri : |X| ≤ (4 * C₀ + 1) * Real.exp (-(c * κ * (q : ℝ) / 2)) + R
      + (1 / (m : ℝ)) * (4 * C₀) := by
    have hC1 : (1 : ℝ) ≤ C := hLDT.2.1
    have hkinv : (1 : ℝ) ≤ (κ ^ 2)⁻¹ := by
      have hκ2 : (0 : ℝ) < κ ^ 2 := by positivity
      rw [one_le_inv₀ hκ2]
      nlinarith [hκ, hκ1]
    have hq1 : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
    have hN₀1 : (1 : ℝ) ≤ (N₀ : ℝ) := by
      have hb : (1 : ℝ) ≤ C * (κ ^ 2)⁻¹ * (q : ℝ) := by
        calc (1 : ℝ) = 1 * 1 * 1 := by ring
          _ ≤ C * (κ ^ 2)⁻¹ * (q : ℝ) := by
              apply mul_le_mul
              · exact mul_le_mul hC1 hkinv (by norm_num) (by positivity)
              · exact hq1
              · norm_num
              · positivity
      linarith [hN₀]
    have hmN : 1 ≤ m * N₀ := by
      have hN₀n : 1 ≤ N₀ := by exact_mod_cast hN₀1
      have hm1 : 1 ≤ m := by omega
      exact le_trans hm1 (Nat.le_mul_of_pos_right m (by omega))
    have hRnn : 0 ≤ R := by
      rw [hRdef]
      exact sub_nonneg.mpr (lyap_le_lyapAvg ((a : ℝ) / (q : ℝ)) lam (E : ℂ) hmN)
    set c₀ : ℝ := (2 / (m : ℝ)) * (lyapAvg ((a : ℝ) / (q : ℝ)) lam (E : ℂ) N₀
      - lyapAvg ((a : ℝ) / (q : ℝ)) lam (E : ℂ) (2 * N₀)) with hc₀def
    have h1 : |X| ≤ |X + R - c₀| + |R| + |c₀| := by
      have htri' := abs_le_three' (X + R - c₀) (-R) c₀
      have hXR : X + R - c₀ + -R + c₀ = X := by ring
      calc |X| = |X + R - c₀ + -R + c₀| := by rw [hXR]
        _ ≤ |X + R - c₀| + |-R| + |c₀| := htri'
        _ = |X + R - c₀| + |R| + |c₀| := by rw [abs_neg]
    have hc₀le : |c₀| ≤ (1 / (m : ℝ)) * (4 * C₀) := by
      rw [hc₀def]
      exact hthird
    have hstep' : |X + R - c₀| ≤ (4 * C₀ + 1) * Real.exp (-(c * κ * (q : ℝ) / 2)) := by
      have hXeq : X = lyap ((a : ℝ) / (q : ℝ)) lam (E : ℂ)
        + lyapAvg ((a : ℝ) / (q : ℝ)) lam (E : ℂ) N₀
        - 2 * lyapAvg ((a : ℝ) / (q : ℝ)) lam (E : ℂ) (2 * N₀) := rfl
      have hReq : R = lyapAvg ((a : ℝ) / (q : ℝ)) lam (E : ℂ) (m * N₀)
        - lyap ((a : ℝ) / (q : ℝ)) lam (E : ℂ) := rfl
      rw [hXeq, hReq] at hstep ⊢
      exact hstep
    have hRabs : |R| = R := abs_of_nonneg hRnn
    linarith [h1, hstep', hRabs, hc₀le]
  -- combine with the rate and the arithmetic hypothesis
  have hfinal : |X| < (12 * C₀ + 1000) * Real.exp (-(c * κ * (q : ℝ) / 4)) := by
    have hRle : R ≤ K * (1 + Real.log ((m : ℝ) * (N₀ : ℝ))) / ((m : ℝ) * (N₀ : ℝ)) := by
      rw [hRdef]; exact hrate
    linarith [htri, hRle, harith]
  rw [hXdef] at hfinal
  exact hfinal

/-! ## The interface (corrected -- two first drafts were REFUTED by review)

**Refutation 1 (uniform hyperbolicity).**  The claim "`lyap (p/q) lam E > 0` implies
`∃ ρ > 1, ∀ x, ρ ≤ rhoSL (tr (iterC (p/q) lam (E:ℂ) q x))`" is **FALSE**.  Counterexample:
`p = 1, q = 1, lam = 1, E = 5/2`.  Then `tr (iterC 1 1 ((5/2):ℂ) 1 x) = 5/2 - 2cos(2πx)`,
which equals `1/2` at `x = 0`, so `rhoSL = 1` there and no uniform `ρ > 1` exists; yet
`lyap ≈ 0.6487 > 0` by `Solutions/lyap_periodic` (the integrand `log (rhoSL (tr A_1))` is
`≥ 0` and strictly positive on a set of positive measure).  The reason is that for rational `α`
the trace ranges over a continuum of *Bloch phases*, so Lyapunov positivity only forces
`|tr A_q(x)| > 2` on a positive-measure set, not for every `x`.

**Refutation 2 (exponential decay of the excess).**  Even under uniform hyperbolicity the excess
is `Θ(1/m)`, not `O(ρ^{-m})`: `log‖A_q(x)^m‖_F = m log ρ_x + log‖P_+(x)‖ + O(ρ_x^{-2m})` and the
middle term is `O(1)`, so `(1/(mq)) ∫ (log‖A_q^m‖ - m log ρ_x)` is `Θ(1/m)` (this is the norm of
the unstable eigenprojection, divided by `mq`).  Counterexample: `p = 0, q = 1, lam = 1, E = 6`,
where `τ(x) = 6 - 2cos(2πx) ∈ [4,8]`, `rhoSL ≥ 2+√3`, so the uniform bound holds for `ρ = 3`,
while numerically `m · excess(m) → 0.0726 ≠ 0`, whence `excess(m) · ρ^m → ∞` for every `ρ > 1`.

## The corrected interface

What *is* available (and what the rational half of `prop9_main` actually needs) is the
**polynomial rate at the multiples of the period**, which is a self-contained consequence of the
Floquet decomposition and does not need any uniform hyperbolicity:

  `∃ K ≥ 0, ∀ m ≥ 1, lyapAvg (p/q) lam E (m*q) - lyap (p/q) lam E ≤ K (1 + log (m q)) / (m q)`.

This is enough for `prop9_main`: at the chosen base scale `N₀ = q · ⌈Cκ⁻²⌉` (which lies in the
window, and carries the pairing) one scale step with the maximal multiplier
`m ≈ e^{cκq/2}` gives `D_{N₀} = -e_{mN₀} + O((4C₀+1)e^{-cκq/2})` (`AvgStep.scale_step_avg`), and
the rate above at the huge scale `mN₀ = m q ⌈Cκ⁻²⌉` makes the excess smaller than
`(12C₀+1000)e^{-cκq/4}` for large `q`, since `e^{cκq/2}` beats any polynomial in `q`.

The statement is delegated as `Scale/rat_excess_decay_of_hyperbolic` (with the fixed conclusion).
-/

end Work.TMC7Core.Scale
