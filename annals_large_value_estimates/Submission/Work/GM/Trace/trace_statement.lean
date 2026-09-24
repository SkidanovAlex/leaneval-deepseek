import Mathlib
import Submission.GM.Interfaces
import Submission.Work.GM.Trace.Defs
import Submission.Work.GM.Trace.hhat_decay_deriv
import Submission.Work.GM.Trace.hhat_zero_decay
import Submission.Work.GM.Trace.hhat_norm_le_Azero
import Submission.Work.GM.Trace.poisson_hfun
import Submission.Work.GM.Trace.summable_hhat_row
import Submission.Work.GM.Trace.summable_Iterm
import Submission.Work.GM.Trace.summable_Iterm_all
import Submission.Work.GM.Trace.sum_singularValues_pow_eq_trace
import Submission.Work.GM.Trace.trace_two_identity
import Submission.Work.GM.Trace.trace_two_estimate
import Submission.Work.GM.Trace.tsum_split_Iterm
import Submission.Work.GM.Trace.tsum_Iterm_ne_zero_eq_sparts
import Submission.Work.GM.Trace.Iterm_zero_bound
import Submission.Work.GM.Trace.Spart_one_bound
import Submission.Work.GM.Trace.sep_card_le
import Submission.Work.GM.Trace.final_bound
import Submission.Work.GM.Trace.trace_three_identity

/-!
# Guth–Maynard §4 and Proposition 5.1 (area `Work.GM.Trace`)

This file proves `Submission.GM.TraceStatement`, the contract of the `Trace` area: the trace
estimates of GM §4 (Lemmas 4.3–4.5, Proposition 4.6) together with Proposition 5.1 (`‖S₁‖ ≤ 1`).

The proof assembles the lemmas proved by the fleet under `Submission/Work/GM/Trace/`:

* `hhat_decay_deriv`, `hhat_zero_decay`, `hhat_norm_le_Azero`  (GM Lemma 4.3)
* `poisson_hfun`                                               (Poisson summation for `h_t`)
* `sum_singularValues_pow_eq_trace`                            (`Σ σᵢ^{2r} = tr((M M*)^r)`)
* `trace_two_identity`, `trace_two_estimate`                   (GM Lemma 4.4)
* `trace_three_identity`, `Iterm_zero_bound`, `tsum_split_Iterm`,
  `tsum_Iterm_ne_zero_eq_sparts`                               (GM Lemma 4.5 / (5.5))
* `summable_Iterm`, `summable_Iterm_all`, `summable_hhat_row`  (summability)
* `sep_card_le`                                                (`|W| ≤ T + 1`)
* `Spart_one_bound`                                            (GM Proposition 5.1)
* `final_bound`                                                (the numeric assembly, Prop. 4.6)
-/

open Complex Finset
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.GM.Trace

open Submission.GM Submission.LargeValues

/-- The three decay inputs of GM Lemma 4.3, in the form used by the `S₁` bound. -/
private theorem hhat_decay_inputs :
    (∀ j : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ t ξ : ℝ, ξ ≠ 0 →
        ‖hhat t ξ‖ ≤ C * (1 + |t|) ^ j / |ξ| ^ j) ∧
      (∀ j : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, 1 ≤ |t| → ‖hhat t 0‖ ≤ C / |t| ^ j) ∧
      (∀ t ξ : ℝ, ‖hhat t ξ‖ ≤ Azero) :=
  ⟨hhat_decay_deriv, hhat_zero_decay, fun t ξ => hhat_norm_le_Azero t ξ⟩



theorem trace_statement : Submission.GM.TraceStatement := by
  intro ε hε
  obtain ⟨hdec, hzero, hAz⟩ := hhat_decay_inputs
  obtain ⟨N₁, hN₁⟩ := Spart_one_bound ε hε hdec hzero hAz
  obtain ⟨N₂, hN₂⟩ := trace_two_estimate ε hε
  obtain ⟨N₃, hN₃⟩ := Iterm_zero_bound ε hε
  obtain ⟨N₄, hN₄⟩ := final_bound
  refine ⟨16 * Azero + 48, by nlinarith [Azero_nonneg],
    max 1000 (max N₁ (max N₂ (max N₃ N₄))), ?_⟩
  intro N hN W hWmem hWsep
  have hN1 : N₁ ≤ N := by omega
  have hN2 : N₂ ≤ N := by omega
  have hN3 : N₃ ≤ N := by omega
  have hN4 : N₄ ≤ N := by omega
  have hN1p : 1 ≤ N := by omega
  refine ⟨summable_Iterm N hN1p W hdec hAz, hN₁ N hN1 W hWmem hWsep, ?_⟩
  intro b hb V hV hval
  by_cases hW0 : W.card = 0
  · have hz : (W.card : ℝ) = 0 := Nat.cast_eq_zero.mpr hW0
    rw [hz]
    have hCpos : (0 : ℝ) < 16 * Azero + 48 := by nlinarith [Azero_nonneg]
    have hnn : 0 ≤ (16 * Azero + 48) *
        ((N : ℝ) ^ 2 / V ^ 2 + (N : ℝ) / V ^ 2 *
          ‖Spart 1 N W + Spart 2 N W + Spart 3 N W‖ ^ (1 / 3 : ℝ)) := by
      refine mul_nonneg hCpos.le (add_nonneg ?_ ?_)
      · exact div_nonneg (sq_nonneg _) (by positivity)
      · exact mul_nonneg (div_nonneg (Nat.cast_nonneg N) (by positivity))
          (Real.rpow_nonneg (norm_nonneg _) _)
    linarith
  · have hpos : 0 < W.card := Nat.pos_of_ne_zero hW0
    have hW1 : (1 : ℝ) ≤ (W.card : ℝ) := by exact_mod_cast hpos
    refine hN₄ N hN4 W b V hW1 hb hV hval ?_ ?_
    · -- GM Lemma 4.4 with its error term
      have hte := hN₂ N hN2 W hWmem hWsep
      have hb2 : (∑ i : Fin (N + 1),
            (Matrix.toEuclideanLin (MWmat N W)).singularValues i ^ 2)
          = (Matrix.trace (MWmat N W * (MWmat N W).conjTranspose)).re := by
        simpa using sum_singularValues_pow_eq_trace N W (r := 1) le_rfl
      rw [hb2]
      have h1 : |(Matrix.trace (MWmat N W * (MWmat N W).conjTranspose)).re
            - (N : ℝ) * (W.card : ℝ) * Azero|
          = |(Matrix.trace (MWmat N W * (MWmat N W).conjTranspose)
              - (((N : ℝ) * (W.card : ℝ) * Azero : ℝ) : ℂ)).re| := by
        rw [Complex.sub_re, Complex.ofReal_re]
      rw [h1]
      exact (Complex.abs_re_le_norm _).trans hte
    · -- GM Lemma 4.5: the cubic trace bounds `Σ σᵢ⁶`
      have hpoi : ∀ t : ℝ, ∑ n ∈ Finset.Icc N (2 * N), hfun t ((n : ℝ) / (N : ℝ))
          = (N : ℂ) * ∑' m : ℤ, hhat t ((m : ℝ) * (N : ℝ)) :=
        fun t => poisson_hfun hN1p t
      have hsum : ∀ t : ℝ, Summable (fun m : ℤ => hhat t ((m : ℝ) * (N : ℝ))) :=
        fun t => summable_hhat_row N hN1p t hdec
      have hid : Matrix.trace ((MWmat N W * (MWmat N W).conjTranspose) ^ 3)
          = ∑' m : ℤ × ℤ × ℤ, Iterm N W m :=
        trace_three_identity N hN1p W hpoi hsum
      have hsplit := tsum_split_Iterm N W (summable_Iterm_all N hN1p W hdec hAz)
      have hsumk := summable_Iterm N hN1p W hdec hAz
      have hpart := tsum_Iterm_ne_zero_eq_sparts N W (hsumk 1) (hsumk 2) (hsumk 3)
      have hI0 := hN₃ N hN3 W hWmem hWsep
      have hI0re : (Iterm N W 0).re
          ≤ (N : ℝ) ^ 3 * (W.card : ℝ) * Azero ^ 3 + tinyN N := by
        have h := Complex.re_le_norm (Iterm N W 0
          - (((N : ℝ) ^ 3 * (W.card : ℝ) * Azero ^ 3 : ℝ) : ℂ))
        have h' : (Iterm N W 0
            - (((N : ℝ) ^ 3 * (W.card : ℝ) * Azero ^ 3 : ℝ) : ℂ)).re
            = (Iterm N W 0).re - (N : ℝ) ^ 3 * (W.card : ℝ) * Azero ^ 3 := by
          rw [Complex.sub_re, Complex.ofReal_re]
        rw [h'] at h
        linarith
      have hb3 : (∑ i : Fin (N + 1),
            (Matrix.toEuclideanLin (MWmat N W)).singularValues i ^ 6)
          = (Matrix.trace ((MWmat N W * (MWmat N W).conjTranspose) ^ 3)).re := by
        simpa using sum_singularValues_pow_eq_trace N W (r := 3) (by norm_num)
      rw [hb3]
      calc (Matrix.trace ((MWmat N W * (MWmat N W).conjTranspose) ^ 3)).re
          = (∑' m : ℤ × ℤ × ℤ, Iterm N W m).re := by rw [hid]
        _ = (Iterm N W 0 + ∑' m : {m : ℤ × ℤ × ℤ // m ≠ 0}, Iterm N W m).re := by
              rw [hsplit]
        _ = (Iterm N W 0).re
              + (Spart 1 N W + Spart 2 N W + Spart 3 N W).re := by
              rw [hpart]; simp
        _ ≤ (N : ℝ) ^ 3 * (W.card : ℝ) * Azero ^ 3 + tinyN N
              + ‖Spart 1 N W + Spart 2 N W + Spart 3 N W‖ := by
              have hS := Complex.re_le_norm (Spart 1 N W + Spart 2 N W + Spart 3 N W)
              linarith
        _ = (N : ℝ) ^ 3 * (W.card : ℝ) * Azero ^ 3
              + ‖Spart 1 N W + Spart 2 N W + Spart 3 N W‖ + tinyN N := by ring

end Work.GM.Trace
