import Submission.Work.TMC14Core.Assembly
import Submission.Work.TMComp.RotBasics.RotLift
import Submission.Work.TMComp.IDSPrufer.rotLift_approx
import Submission.Work.TMComp.RotBasics.PSIter

/-!
# TMC14Core: the `q`-step Prüfer rotation number of the rational approximant

For a rational frequency `α = p/q` the Prüfer cocycle is periodic in the space variable with
period `q` (`pruferIter_periodic_x`, since `q α = p ∈ ℤ`).  Hence the `q`-step map

  `qMap p q lam E x = fun t => pruferIter (p/q) lam E q x t`

is the natural "monodromy" of the cocycle, and the fibre rotation number is the average over
the phase `x` of the rotation number of `qMap`.

This module fixes that vocabulary:

* `qMap p q lam E x`, the `q`-step Prüfer map;
* `qIter p q lam E x m = (qMap …)^[m] 0`, its orbit of `0`;
* `rotQ p q lam E x`, the asymptotic rotation number `lim_m qIter … m / m`;
* `qIter_almostAdditive`, `rotQ_rate`: Fekete almost-additivity (error `1`) and the `1/m`
  convergence rate.
-/

open MeasureTheory Filter Topology Set
open LeanEval.Analysis.TenMartini

noncomputable section

namespace Work.TMC14Core

/-- `q α = p` for `α = p/q`, `q ≠ 0`. -/
theorem q_mul_freq (p : ℤ) (q : ℕ) (hq : 1 ≤ q) :
    ((q : ℕ) : ℝ) * ((p : ℝ) / (q : ℝ)) = (p : ℝ) := by
  have hq0 : ((q : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.one_le_iff_ne_zero.mp hq)
  field_simp

/-- The `q`-step Prüfer map of the frequency `p/q`. -/
def qMap (p : ℤ) (q : ℕ) (lam E x : ℝ) : ℝ → ℝ :=
  fun t => Work.TMContract.pruferIter ((p : ℝ) / (q : ℝ)) lam E q x t

/-- The orbit of `0` under the `q`-step Prüfer map. -/
def qIter (p : ℤ) (q : ℕ) (lam E x : ℝ) (m : ℕ) : ℝ :=
  (qMap p q lam E x)^[m] 0

/-- The rotation number of the `q`-step Prüfer map. -/
def rotQ (p : ℤ) (q : ℕ) (lam E : ℝ) (x : ℝ) : ℝ :=
  Filter.limUnder Filter.atTop (fun m : ℕ => qIter p q lam E x m / (m : ℝ))

theorem qIter_zero (p : ℤ) (q : ℕ) (lam E x : ℝ) : qIter p q lam E x 0 = 0 := by
  simp [qIter]

theorem qIter_succ (p : ℤ) (q : ℕ) (lam E x : ℝ) (m : ℕ) :
    qIter p q lam E x (m + 1) = qMap p q lam E x (qIter p q lam E x m) := by
  simp only [qIter, Function.iterate_succ_apply']

/-- `pruferIter (q*m) x = (qMap)^[m]`: the `q`-step map iterated `m` times is the
`qm`-step Prüfer iteration. -/
theorem pruferIter_q_mul (p : ℤ) (q : ℕ) (lam E x : ℝ) (hq : 1 ≤ q) (m : ℕ) (t : ℝ) :
    Work.TMContract.pruferIter ((p : ℝ) / (q : ℝ)) lam E (q * m) x t
      = (qMap p q lam E x)^[m] t := by
  induction m generalizing t with
  | zero => simp only [Nat.mul_zero, qIter, Function.iterate_zero_apply,
      Work.TMContract.pruferIter]
  | succ m ih =>
    set α : ℝ := (p : ℝ) / (q : ℝ) with hαdef
    have hα : ((q : ℕ) : ℝ) * α = (p : ℝ) := by rw [hαdef]; exact q_mul_freq p q hq
    have hs : x + ((q * m : ℕ) : ℝ) * α = x + (((m : ℤ) * p : ℤ) : ℝ) := by
      rw [show ((q * m : ℕ) : ℝ) * α = (m : ℝ) * (((q : ℕ) : ℝ) * α) by push_cast; ring, hα]
      push_cast; ring
    calc Work.TMContract.pruferIter α lam E (q * (m + 1)) x t
        = Work.TMContract.pruferIter α lam E (q * m + q) x t := by
          rw [show q * (m + 1) = q * m + q by ring]
      _ = Work.TMContract.pruferIter α lam E q (x + ((q * m : ℕ) : ℝ) * α)
            (Work.TMContract.pruferIter α lam E (q * m) x t) :=
          Work.TMComp.RotBasics.pruferIter_cocycle α lam E (q * m) q x t
      _ = Work.TMContract.pruferIter α lam E q (x + (((m : ℤ) * p : ℤ) : ℝ))
            (Work.TMContract.pruferIter α lam E (q * m) x t) := by rw [hs]
      _ = Work.TMContract.pruferIter α lam E q x
            (Work.TMContract.pruferIter α lam E (q * m) x t) :=
          Work.TMComp.RotBasics.pruferIter_periodic_x_int α lam E q ((m : ℤ) * p) x
            (Work.TMContract.pruferIter α lam E (q * m) x t)
      _ = (qMap p q lam E x)^[m + 1] t := by
          rw [Function.iterate_succ_apply']
          simp only [qMap]
          rw [ih]

/-- The displacement bound for the iterated `q`-step map. -/
theorem qMap_iter_disp (p : ℤ) (q : ℕ) (lam E x : ℝ) (hq : 1 ≤ q) (m : ℕ) (s : ℝ) :
    |(qMap p q lam E x)^[m] s - (qMap p q lam E x)^[m] 0 - s| ≤ 1 := by
  have h1 := pruferIter_q_mul p q lam E x hq m s
  have h2 := pruferIter_q_mul p q lam E x hq m 0
  rw [← h1, ← h2]
  exact Work.TMComp.RotBasics.pruferIter_bound ((p : ℝ) / (q : ℝ)) lam E (q * m) x s

/-- The `q`-iterate is almost additive with error `1`. -/
theorem qIter_almostAdditive (p : ℤ) (q : ℕ) (lam E x : ℝ) (hq : 1 ≤ q) (m n : ℕ) :
    |qIter p q lam E x (m + n) - qIter p q lam E x m - qIter p q lam E x n| ≤ 1 := by
  have hsplit : qIter p q lam E x (m + n) = (qMap p q lam E x)^[m] (qIter p q lam E x n) := by
    simp only [qIter, Function.iterate_add_apply]
  rw [hsplit]
  have := qMap_iter_disp p q lam E x hq m (qIter p q lam E x n)
  simpa only [qIter] using this

/-- The `1/m` rate of convergence of `qIter … m / m` to `rotQ`. -/
theorem rotQ_rate (p : ℤ) (q : ℕ) (lam E : ℝ) (x : ℝ) (hq : 1 ≤ q) {m : ℕ} (hm : 1 ≤ m) :
    |rotQ p q lam E x - qIter p q lam E x m / (m : ℝ)| ≤ 1 / (m : ℝ) := by
  have h := Work.TMComp.IDSPrufer.almostAdditive_limUnder_aux
    (fun m => qIter p q lam E x m) 1 (by norm_num) (qIter_zero p q lam E x)
    (fun m n => qIter_almostAdditive p q lam E x hq m n)
  simpa [rotQ] using h m hm

/-- Joint continuity in `(E, t)` of the `n`-step Prüfer iteration at a fixed space point. -/
theorem pruferIter_continuous_Et (α lam : ℝ) (n : ℕ) (x : ℝ) :
    Continuous (fun p : ℝ × ℝ => Work.TMContract.pruferIter α lam p.1 n x p.2) := by
  induction n with
  | zero =>
    have h : (fun p : ℝ × ℝ => Work.TMContract.pruferIter α lam p.1 0 x p.2) = fun p => p.2 := by
      funext p; exact Work.TMComp.RotBasics.pruferIter_zero α lam p.1 x p.2
    rw [h]; exact continuous_snd
  | succ n ih =>
    have hfun : (fun p : ℝ × ℝ => Work.TMContract.pruferIter α lam p.1 (n + 1) x p.2)
        = fun p : ℝ × ℝ =>
            pruferStep (p.1 - 2 * lam * Real.cos (2 * Real.pi * (x + (n : ℝ) * α)))
              (Work.TMContract.pruferIter α lam p.1 n x p.2) := by
      funext p
      exact Work.TMComp.RotBasics.pruferIter_succ α lam p.1 n x p.2
    rw [hfun]
    exact Work.TMComp.RotBasics.pruferStep_continuous.comp
      ((by fun_prop : Continuous (fun p : ℝ × ℝ =>
        p.1 - 2 * lam * Real.cos (2 * Real.pi * (x + (n : ℝ) * α)))).prodMk ih)

/-- Continuity of `m ↦ qIter m` in the energy. -/
theorem qIter_continuous_E (p : ℤ) (q : ℕ) (lam x : ℝ) (m : ℕ) :
    Continuous (fun E : ℝ => qIter p q lam E x m) := by
  induction m with
  | zero =>
    have h : (fun E : ℝ => qIter p q lam E x 0) = fun _ => (0 : ℝ) := by
      funext E; exact qIter_zero p q lam E x
    rw [h]; exact continuous_const
  | succ m ih =>
    have hfun : (fun E : ℝ => qIter p q lam E x (m + 1))
        = fun E : ℝ => qMap p q lam E x (qIter p q lam E x m) := by
      funext E; exact qIter_succ p q lam E x m
    rw [hfun]
    exact (pruferIter_continuous_Et ((p : ℝ) / (q : ℝ)) lam q x).comp
      (Continuous.prodMk continuous_id ih)

end Work.TMC14Core
