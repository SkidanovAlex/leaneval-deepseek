import Mathlib
import Submission.Work.RPCore.Flow.HamFlow

/-!
# C0: `C³` regularity of the two-time Hamiltonian flow in the initial condition

`Phi Hh a b x` is the value at time `b` of the solution of the (clamped) Hamiltonian ODE starting
from `x` at time `a`; equivalently, `Phi Hh a b x = (clampFlow Hh (b - a) (a, x)).2`, where
`clampFlow Hh` is the global flow of the autonomous field `clampedField Hh = (1, X_{H∘ψ})`.

The field `clampedField Hh` is only `C³` (one derivative is lost when passing from the Hamiltonian
to its vector field), so we cannot invoke the `C^∞` joint-smoothness theorem.  Instead we use the
finite-regularity result `contDiff_flow_timeSlice_le`, which gives `C³` dependence on the initial
condition for *uniformly small* times, and extend it to arbitrary times by the semigroup law:
`clampFlow Hh t = (clampFlow Hh (t/k))^[k]` for any `k` with `|t/k| ≤ δ`.  A composition of `C³`
maps is `C³`, whence the time slices of the flow are `C³` for every time.

The main result is `Phi_contDiff`.
-/

open scoped ContDiff

set_option autoImplicit false

noncomputable section

namespace Work.RPCore.Flow

open Work.RPCore

/-- Every time slice of the (clamped) flow of a `CptPerHam` is `C³` in the initial condition.
Small times are handled by `contDiff_flow_timeSlice_le`; arbitrary times follow by writing the
time as a natural multiple of a small one and using the semigroup law. -/
lemma clampFlow_contDiff (Hh : Work.RPV.CptPerHam) (t : ℝ) :
    ContDiff ℝ 3 (clampFlow Hh t) := by
  -- `C³` dependence on the initial condition for uniformly small times
  obtain ⟨δ, hδpos, hδ⟩ := contDiff_flow_timeSlice_le 3 (by norm_num) (clampedField Hh)
      (clampedField_contDiff_three Hh) (clampedData Hh).M (clampedData Hh).K
      (clampedData Hh).hM (clampedData Hh).hK (clampFlow Hh)
      (fun t y => ⟨fun s => clampFlow Hh s y, clampFlow_zero Hh y, clampFlow_curve Hh y, rfl⟩)
  -- an integer `k ≥ 1` with `|t/k| ≤ δ`
  obtain ⟨k, hk⟩ := exists_nat_gt (|t| / δ)
  have hk0 : k ≠ 0 := by
    intro h
    rw [h] at hk
    push_cast at hk
    have : 0 ≤ |t| / δ := div_nonneg (abs_nonneg t) hδpos.le
    linarith
  set s : ℝ := t / (k : ℝ) with hs_def
  have hsδ : |s| ≤ δ := by
    have hk' : |t| < δ * (k : ℝ) := by
      rw [div_lt_iff₀ hδpos] at hk
      rw [mul_comm]
      exact hk
    rw [hs_def, abs_div, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (k : ℝ))]
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < (k : ℝ))]
    exact hk'.le
  -- the semigroup iterate `clampFlow Hh (m * s) = (clampFlow Hh s)^[m]`
  have hiter_lemma : ∀ m : ℕ, clampFlow Hh ((m : ℝ) * s) = (clampFlow Hh s)^[m] := by
    intro m
    induction m with
    | zero =>
        rw [Nat.cast_zero, zero_mul, Function.iterate_zero]
        funext z
        exact clampFlow_zero Hh z
    | succ m ih =>
        have step : clampFlow Hh ((m : ℝ) * s + s)
            = clampFlow Hh ((m : ℝ) * s) ∘ clampFlow Hh s := by
          funext z
          exact clampFlow_add Hh ((m : ℝ) * s) s z
        rw [show ((m + 1 : ℕ) : ℝ) * s = (m : ℝ) * s + s by push_cast; ring]
        rw [step, ih, Function.iterate_succ]
  have hkt : (k : ℝ) * s = t := by
    rw [hs_def, ← mul_div_assoc]
    exact mul_div_cancel_left₀ t (by exact_mod_cast hk0 : (k : ℝ) ≠ 0)
  have hstr : clampFlow Hh t = (clampFlow Hh s)^[k] := by
    rw [← hkt, hiter_lemma k]
  -- `C³` slices are closed under composition, hence under iteration
  have hs : ContDiff ℝ 3 (clampFlow Hh s) := hδ s hsδ
  have hpow : ∀ m : ℕ, ContDiff ℝ 3 ((clampFlow Hh s)^[m]) := by
    intro m
    induction m with
    | zero =>
        simpa using (contDiff_id : ContDiff ℝ 3 (id : ℝ × Work.RPV.PS → ℝ × Work.RPV.PS))
    | succ m ih =>
        rw [Function.iterate_succ]
        exact ih.comp hs
  rw [hstr]
  exact hpow k

theorem Phi_contDiff (Hh : Work.RPV.CptPerHam) (a b : ℝ) :
    ContDiff ℝ 3 (Work.RPCore.Phi Hh a b) := by
  have h1 : ContDiff ℝ 3 (clampFlow Hh (b - a)) := clampFlow_contDiff Hh (b - a)
  have h2 : ContDiff ℝ 3 (fun x : Work.RPV.PS => (a, x)) :=
    (contDiff_const : ContDiff ℝ 3 (fun _ : Work.RPV.PS => a)).prodMk contDiff_id
  have h3 : ContDiff ℝ 3
      ((clampFlow Hh (b - a)) ∘ (fun x : Work.RPV.PS => (a, x))) := h1.comp h2
  exact h3.snd

end Work.RPCore.Flow
