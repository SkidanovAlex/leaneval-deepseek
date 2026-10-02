/-
# The Green function along an orbit: `G_c (T_c^[n] w) = 2^n G_c w`

The Green function of the filled Julia set of the antiholomorphic unicritical family
`T_c(z) = (conj z)^2 + c` satisfies the functional equation

`G_c (T_c w) = 2 G_c w`,

which iterated gives `G_c (T_c^[n] w) = 2^n G_c w`.  This is the potential-theoretic
statement that the escape rate is doubled by each application of the degree two
antipolynomial; it is the basic compatibility of `greenFun` with the dynamics, used
throughout the parameter-ray theory (for instance to transport the potential of the
critical point along the critical orbit).

## Main results

* `Work.ParamRays.greenSeq_bddAbove` : the normalized logarithms `greenSeq c w` are
  bounded above (so the `limsup` defining the Green function is not degenerate).
* `Work.ParamRays.limsup_const_mul_nat` : for `0 ≤ c` and a nonnegative sequence `u`
  bounded above, `limsup_n (c * u n) = c * limsup_n u n`.
* `Work.ParamRays.greenFun_orbit` : `greenFun c (orbit c w n) = 2^n * greenFun c w`.
-/
import Mathlib
import Submission.Work.ParamRays.Basic
import Submission.Work.ParamRays.Green

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Filter
open scoped Real Topology
open LeanEval.ComplexAnalysis (Tantibar)

namespace Work.ParamRays

/-! ## Boundedness of the normalized logarithms -/

/-- The normalized logarithms `greenSeq c w n = 2^{-n} log⁺ ‖T_c^[n] w‖` are bounded
above, uniformly in `n`.

Indeed, with `C = max 1 ‖c‖` and `M = log (2C)` one has the recursion
`log⁺ ‖z_{n+1}‖ ≤ M + 2 log⁺ ‖z_n‖` for the orbit `z_n = T_c^[n] w`: this is clear
when `‖z_n‖ ≤ 1` (where `‖z_{n+1}‖ ≤ ‖z_n‖^2 + ‖c‖ ≤ 1 + C ≤ 2C`), while for `‖z_n‖ ≥ 1`
we have `‖z_n‖^2 + C ≤ 2C ‖z_n‖^2`.  Iterating gives
`log⁺ ‖z_n‖ ≤ 2^n log⁺ ‖w‖ + (2^n - 1) M`, hence `greenSeq c w n ≤ log⁺ ‖w‖ + M`. -/
theorem greenSeq_bddAbove (c w : ℂ) : ∃ B : ℝ, ∀ n : ℕ, greenSeq c w n ≤ B := by
  set C : ℝ := max 1 ‖c‖ with hCdef
  have hC1 : (1 : ℝ) ≤ C := le_max_left _ _
  have hCc : ‖c‖ ≤ C := le_max_right _ _
  have hM0 : 0 ≤ Real.log (2 * C) := Real.log_nonneg (by linarith)
  have key : ∀ n : ℕ, Real.posLog ‖orbit c w n‖ ≤
      (2 : ℝ) ^ n * Real.posLog ‖w‖ + ((2 : ℝ) ^ n - 1) * Real.log (2 * C) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have hstep : Real.posLog ‖orbit c w (n + 1)‖ ≤
          Real.log (2 * C) + 2 * Real.posLog ‖orbit c w n‖ := by
        rw [show orbit c w (n + 1) = Tantibar c (orbit c w n) from orbit_succ c w n]
        have hle : ‖Tantibar c (orbit c w n)‖ ≤ ‖orbit c w n‖ ^ 2 + C := by
          have h := norm_Tantibar_le c (orbit c w n)
          linarith
        rcases lt_or_ge (1 : ℝ) ‖orbit c w n‖ with hx | hx
        · have hz1 : (1 : ℝ) ≤ ‖orbit c w n‖ ^ 2 := by
            nlinarith [hx, norm_nonneg (orbit c w n)]
          have h1 : ‖orbit c w n‖ ^ 2 + C ≤ 2 * C * ‖orbit c w n‖ ^ 2 := by
            nlinarith [hC1, hz1]
          have h2 : Real.posLog ‖Tantibar c (orbit c w n)‖
              ≤ Real.posLog (2 * C * ‖orbit c w n‖ ^ 2) :=
            Real.posLog_le_posLog
              (by linarith [norm_nonneg (Tantibar c (orbit c w n))]) (le_trans hle h1)
          have h3 : Real.posLog (2 * C * ‖orbit c w n‖ ^ 2)
              ≤ Real.posLog (2 * C) + Real.posLog (‖orbit c w n‖ ^ 2) := Real.posLog_mul
          rw [Real.posLog_pow] at h3
          push_cast at h3
          have hM : Real.posLog (2 * C) = Real.log (2 * C) :=
            Real.posLog_eq_log (by rw [abs_of_nonneg (by linarith)]; linarith)
          linarith
        · have h1 : ‖Tantibar c (orbit c w n)‖ ≤ 2 * C := by
            have h2 : ‖orbit c w n‖ ^ 2 ≤ 1 := by nlinarith [hx, norm_nonneg (orbit c w n)]
            linarith
          have h2 : Real.posLog ‖Tantibar c (orbit c w n)‖ ≤ Real.log (2 * C) := by
            refine le_trans (Real.posLog_le_posLog
              (by linarith [norm_nonneg (Tantibar c (orbit c w n))]) h1) ?_
            rw [Real.posLog_eq_log (by rw [abs_of_nonneg (by linarith)]; linarith)]
          have h3 : 0 ≤ Real.posLog ‖orbit c w n‖ := Real.posLog_nonneg
          linarith
      have hpow : (2 : ℝ) ^ (n + 1) = (2 : ℝ) ^ n * 2 := pow_succ 2 n
      have hih := mul_le_mul_of_nonneg_left ih (by norm_num : (0 : ℝ) ≤ 2)
      have harith : 2 * ((2 : ℝ) ^ n * Real.posLog ‖w‖ + ((2 : ℝ) ^ n - 1) * Real.log (2 * C))
          + Real.log (2 * C)
          = (2 : ℝ) ^ (n + 1) * Real.posLog ‖w‖
            + ((2 : ℝ) ^ (n + 1) - 1) * Real.log (2 * C) := by
        rw [hpow]; ring
      linarith
  refine ⟨Real.posLog ‖w‖ + Real.log (2 * C), fun n => ?_⟩
  have h1 : greenSeq c w n ≤ ((2 : ℝ) ^ n)⁻¹ *
      ((2 : ℝ) ^ n * Real.posLog ‖w‖ + ((2 : ℝ) ^ n - 1) * Real.log (2 * C)) := by
    rw [greenSeq]
    exact mul_le_mul_of_nonneg_left (key n) (by positivity)
  have h2 : ((2 : ℝ) ^ n)⁻¹ *
      ((2 : ℝ) ^ n * Real.posLog ‖w‖ + ((2 : ℝ) ^ n - 1) * Real.log (2 * C)) =
      Real.posLog ‖w‖ + (1 - ((2 : ℝ) ^ n)⁻¹) * Real.log (2 * C) := by
    field_simp
  have h3 : 1 - ((2 : ℝ) ^ n)⁻¹ ≤ 1 := by
    have h : ((2 : ℝ) ^ n)⁻¹ ≤ 1 :=
      inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2))
    have h4 : 0 ≤ ((2 : ℝ) ^ n)⁻¹ := by positivity
    linarith
  have h4 : (1 - ((2 : ℝ) ^ n)⁻¹) * Real.log (2 * C) ≤ Real.log (2 * C) :=
    mul_le_of_le_one_left hM0 h3
  linarith

/-! ## A `limsup` scaling lemma -/

/-- For a nonnegative real constant `c` and a nonnegative sequence `u` bounded above,
the `limsup` of `n ↦ c * u n` is `c` times the `limsup` of `u`.

This is proved from the description of the `limsup` as the infimum of the eventual upper
bounds: the set of eventual upper bounds of `c * u` is the image under `x ↦ c * x` of the
set of eventual upper bounds of `u`. -/
theorem limsup_const_mul_nat (c : ℝ) (hc : 0 ≤ c) (u : ℕ → ℝ) (hu0 : ∀ n, 0 ≤ u n)
    (hub : ∃ B : ℝ, ∀ n, u n ≤ B) :
    Filter.limsup (fun n : ℕ => c * u n) Filter.atTop = c * Filter.limsup u Filter.atTop := by
  rcases eq_or_lt_of_le hc with hc0 | hcpos
  · subst hc0
    simp
  rw [Filter.limsup_eq, Filter.limsup_eq]
  set U : Set ℝ := {a | ∀ᶠ n : ℕ in Filter.atTop, u n ≤ a} with hUdef
  set W : Set ℝ := {b | ∀ᶠ n : ℕ in Filter.atTop, c * u n ≤ b} with hWdef
  have hUne : U.Nonempty := by
    obtain ⟨B, hB⟩ := hub
    exact ⟨B, Filter.Eventually.of_forall hB⟩
  have hU0 : ∀ a ∈ U, 0 ≤ a := by
    intro a ha
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp ha
    exact le_trans (hu0 N) (hN N le_rfl)
  have hUup : ∀ {a a' : ℝ}, a ∈ U → a ≤ a' → a' ∈ U := by
    intro a a' ha haa'
    exact ha.mono fun n hn => le_trans hn haa'
  have hW0 : ∀ b ∈ W, 0 ≤ b := by
    intro b hb
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hb
    exact le_trans (mul_nonneg hc (hu0 N)) (hN N le_rfl)
  have hWup : ∀ {b b' : ℝ}, b ∈ W → b ≤ b' → b' ∈ W := by
    intro b b' hb hbb'
    exact hb.mono fun n hn => le_trans hn hbb'
  have hWU : ∀ b : ℝ, b ∈ W ↔ b / c ∈ U := by
    intro b
    constructor
    · intro hb
      refine hb.mono fun n hn => ?_
      rw [le_div_iff₀ hcpos]
      rwa [mul_comm] at hn
    · intro hb
      refine hb.mono fun n hn => ?_
      have h := (le_div_iff₀ hcpos).mp hn
      rwa [mul_comm] at h
  have hWne : W.Nonempty := by
    obtain ⟨a, ha⟩ := hUne
    refine ⟨c * a, ?_⟩
    rw [hWU, mul_div_cancel_left₀ a (ne_of_gt hcpos)]
    exact ha
  have hUmem : ∀ ε : ℝ, 0 < ε → sInf U + ε ∈ U := by
    intro ε hε
    obtain ⟨b, hbU, hb⟩ :=
      (csInf_lt_iff ⟨0, fun a ha => hU0 a ha⟩ hUne).mp (lt_add_of_pos_right _ hε)
    exact hUup hbU (le_of_lt hb)
  have hWmem : ∀ ε : ℝ, 0 < ε → sInf W + ε ∈ W := by
    intro ε hε
    obtain ⟨b, hbW, hb⟩ :=
      (csInf_lt_iff ⟨0, fun b hb => hW0 b hb⟩ hWne).mp (lt_add_of_pos_right _ hε)
    exact hWup hbW (le_of_lt hb)
  refine le_antisymm ?_ ?_
  · refine le_of_forall_pos_le_add fun δ hδ => ?_
    have hmem : c * (sInf U + δ / c) ∈ W := by
      rw [hWU, mul_div_cancel_left₀ _ (ne_of_gt hcpos)]
      exact hUmem (δ / c) (div_pos hδ hcpos)
    have h1 := csInf_le (show BddBelow W from ⟨0, fun b hb => hW0 b hb⟩) hmem
    have h2 : c * (sInf U + δ / c) = c * sInf U + δ := by
      field_simp
    linarith
  · refine le_of_forall_pos_le_add fun δ hδ => ?_
    have hmem : (sInf W + δ) / c ∈ U := (hWU _).mp (hWmem δ hδ)
    have h1 := csInf_le (show BddBelow U from ⟨0, fun a ha => hU0 a ha⟩) hmem
    have h2 : c * ((sInf W + δ) / c) = sInf W + δ := by
      field_simp
    have h3 := mul_le_mul_of_nonneg_left h1 hc
    linarith

/-! ## The orbit formula -/

/-- **The Green function of a point of an orbit** is `2^k` times the Green function of
the point itself. -/
theorem greenFun_orbit_eq (c w : ℂ) (k : ℕ) :
    greenFun c (orbit c w k) = (2 : ℝ) ^ k * greenFun c w := by
  have hseq : ∀ j : ℕ, greenSeq c (orbit c w k) j = (2 : ℝ) ^ k * greenSeq c w (j + k) := by
    intro j
    have horb : orbit c (orbit c w k) j = orbit c w (j + k) := by
      rw [Nat.add_comm j k]
      exact (orbit_add c w k j).symm
    rw [greenSeq, greenSeq, horb, pow_add, mul_inv]
    field_simp
  calc greenFun c (orbit c w k)
      = Filter.limsup (greenSeq c (orbit c w k)) Filter.atTop := rfl
    _ = Filter.limsup (fun j : ℕ => (2 : ℝ) ^ k * greenSeq c w (j + k)) Filter.atTop :=
        Filter.limsup_congr (Filter.Eventually.of_forall hseq)
    _ = (2 : ℝ) ^ k * Filter.limsup (fun j : ℕ => greenSeq c w (j + k)) Filter.atTop := by
        obtain ⟨B, hB⟩ := greenSeq_bddAbove c w
        exact limsup_const_mul_nat ((2 : ℝ) ^ k) (by positivity) (fun j : ℕ => greenSeq c w (j + k))
          (fun j => greenSeq_nonneg c w (j + k)) ⟨B, fun j => hB (j + k)⟩
    _ = (2 : ℝ) ^ k * Filter.limsup (greenSeq c w) Filter.atTop := by
        rw [Filter.limsup_nat_add]
    _ = (2 : ℝ) ^ k * greenFun c w := rfl

theorem greenFun_orbit (c w : ℂ) (n : ℕ) :
    Work.ParamRays.greenFun c (Work.ParamRays.orbit c w n) = (2 : ℝ) ^ n * Work.ParamRays.greenFun c w :=
  greenFun_orbit_eq c w n

end Work.ParamRays
