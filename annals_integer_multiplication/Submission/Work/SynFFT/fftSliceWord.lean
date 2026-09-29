import Mathlib
import Submission.Work.SynFFT.axisStepDefs

/-!
# `Work.SynFFT.SlPre`/`SlPost` form of the slice word (paper Lemma 3.2, Prop. 3.3)

`HasFFT1` (`kit2.lean`) is the slice word in "raw" form: it is stated for an explicit list `ws` of
coefficient vectors together with a target array `u` and an *input* error `e`, and it returns a
list `ws'` approximating `dftN r t sgn u` with error `e + k`.

The axis step (`hasAxis.lean`) needs the same word in a form where the input is an opaque value
`x` (a slice) and where the postcondition talks only about the *values*: this is
`SlPre`/`SlPost` (`axisStepDefs.lean`).  The point of `SlPost` is that it is stated for **every**
`e`-approximation `a` of the slice data `vs`, since the axis step only knows the target array of
the whole flat array, not of the individual slice.

The transfer is the standard error bookkeeping of the paper (`ε` in, `ε` out):

* run the raw word with input error `0` against the *exact* interpolant `u` of the slice data
  (`u q c = fxC p (vs q c)`), which adds only `k` to the error;
* for another target `a` with `ApproxSL p r t vs a e`, `dftN r t sgn` is `1`-Lipschitz in the
  sup norm (`dftNSubLe`, proved in `dftNSubLe.lean`), so `dftN a` differs from `dftN u` by at
  most `e` in the `2^p`-scaled norm, and the triangle inequality gives the total `k + e = e + k`.

The size `vsz y ≤ slL p r t` of the output value is `vsz_of_SlOK` (`axisStepDefs.lean`), which
needs `0 < p`; that follows from `IsPow2 r`, `2 ≤ r` and `2 * r < 2 ^ p`.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace Work.SynFFT

open HvdH

theorem fftSliceWord (h1 : Work.SynFFT.HasFFT1) :
    ∃ (prog : HvdH.Cmd) (K : ℕ), ∀ (main : HvdH.Cmd) (p r t k : ℕ) (sgn : ℤ) (e : ℝ)
      (rest : List HvdH.Val) (x : HvdH.Val),
      HvdH.IsPow2 r → t = 2 ^ k → t ∣ 2 * r → 2 * r < 2 ^ p → (sgn = 1 ∨ sgn = -1) →
      Work.SynFFT.SlPre p r t x →
      HvdH.WordR main prog
        (fun vs => vs = x :: HvdH.Val.int (k : ℤ) :: HvdH.Val.int sgn :: HvdH.Val.int (r : ℤ) ::
          HvdH.Val.int (p : ℤ) :: rest)
        (fun _ out => ∃ y, out = y :: HvdH.Val.int (k : ℤ) :: HvdH.Val.int sgn ::
            HvdH.Val.int (r : ℤ) :: HvdH.Val.int (p : ℤ) :: rest ∧
          Work.SynFFT.SlPost p r t k sgn e x y ∧ HvdH.vsz y ≤ Work.SynFFT.slL p r t)
        (fun _ => K * t * (r + 1) * (p + 1) * (k + 1) + K) := by
  obtain ⟨prog, K, hK⟩ := h1
  refine ⟨prog, K, ?_⟩
  intro main p r t k sgn e rest x hpow ht htdvd hp hsgn hpre
  obtain ⟨vs, hx, hvs_len, hvs_disc⟩ := hpre
  -- `p > 0` (used for the size bound on the output)
  have h2r : 2 ≤ r := by
    obtain ⟨kk, hk1, hkk⟩ := hpow
    rw [hkk]
    calc (2 : ℕ) = 2 ^ 1 := rfl
      _ ≤ 2 ^ kk := pow_le_pow_right₀ (by norm_num) hk1
  have hp0 : 0 < p := by
    by_contra h
    have hpz : p = 0 := Nat.eq_zero_of_not_pos h
    rw [hpz] at hp
    simp at hp
    omega
  have htpos : 0 < t := by rw [ht]; positivity
  -- the exact interpolant of the slice data
  set u : Work.SynFFT.Arr r := fun q c => HvdH.fxC p ((vs.getD q []).getD (c : ℕ) (0, 0)) with hu
  have happ0 : Work.SynFFT.ApproxSL p r t vs u (0 : ℝ) := by
    refine ⟨hvs_len, ?_⟩
    intro q hq c
    simp [hu]
  -- run the raw slice word at input error `0`
  have hkey := hK main p r t k sgn vs u (0 : ℝ) rest hpow ht htdvd hp hsgn hvs_len hvs_disc happ0
  refine Work.SynFFT.MrgKit.WordR_weaken hkey ?_ ?_ ?_
  · -- precondition
    intro ws hws
    rw [hws, hx]
  · -- postcondition: the raw post gives `SlPost` with the outer error `e`
    intro ws out hws hpost
    obtain ⟨ws', hout, hws'_len, hws'_disc, hApp⟩ := hpost
    refine ⟨ofList (Work.SynFFT.cvecs ws'), hout, ?_, ?_⟩
    · refine ⟨vs, ws', hx, rfl, ⟨hvs_len, hvs_disc⟩, ⟨hws'_len, hws'_disc⟩, ?_⟩
      intro a ha
      refine ⟨hws'_len, ?_⟩
      intro q hq c
      -- the word's own error, `≤ k`
      have hAC : (2 : ℝ) ^ p * ‖HvdH.fxC p ((ws'.getD q []).getD (c : ℕ) (0, 0)) -
          Work.SynFFT.dftN r t sgn u q c‖ ≤ (k : ℝ) := by
        have := hApp.2 q hq c
        simpa using this
      -- the error transported from the input, `≤ e`
      have hCB : (2 : ℝ) ^ p * ‖Work.SynFFT.dftN r t sgn u q c -
          Work.SynFFT.dftN r t sgn a q c‖ ≤ e := by
        have hδ : ∀ q' (_ : q' < t) (c' : Fin r), ‖u q' c' - a q' c'‖ ≤ e / (2 : ℝ) ^ p := by
          intro q' hq' c'
          have h := ha.2 q' hq' c'
          rw [hu]
          rw [le_div_iff₀ (by positivity : (0 : ℝ) < (2 : ℝ) ^ p)]
          rw [mul_comm]
          exact h
        have hsub := Work.SynFFT.dftNSubLe r t htpos sgn u a (e / (2 : ℝ) ^ p) hδ q c
        calc (2 : ℝ) ^ p * ‖Work.SynFFT.dftN r t sgn u q c - Work.SynFFT.dftN r t sgn a q c‖
            ≤ (2 : ℝ) ^ p * (e / (2 : ℝ) ^ p) :=
              mul_le_mul_of_nonneg_left hsub (by positivity)
          _ = e := by
              rw [mul_div_assoc', mul_div_cancel_left₀ e (by positivity)]
      have htri : ‖HvdH.fxC p ((ws'.getD q []).getD (c : ℕ) (0, 0)) -
            Work.SynFFT.dftN r t sgn a q c‖ ≤
          ‖HvdH.fxC p ((ws'.getD q []).getD (c : ℕ) (0, 0)) - Work.SynFFT.dftN r t sgn u q c‖ +
          ‖Work.SynFFT.dftN r t sgn u q c - Work.SynFFT.dftN r t sgn a q c‖ := by
        rw [← dist_eq_norm, ← dist_eq_norm, ← dist_eq_norm]
        exact dist_triangle _ _ _
      calc (2 : ℝ) ^ p * ‖HvdH.fxC p ((ws'.getD q []).getD (c : ℕ) (0, 0)) -
              Work.SynFFT.dftN r t sgn a q c‖
          ≤ (2 : ℝ) ^ p * (‖HvdH.fxC p ((ws'.getD q []).getD (c : ℕ) (0, 0)) -
              Work.SynFFT.dftN r t sgn u q c‖ +
              ‖Work.SynFFT.dftN r t sgn u q c - Work.SynFFT.dftN r t sgn a q c‖) :=
            mul_le_mul_of_nonneg_left htri (by positivity)
        _ = (2 : ℝ) ^ p * ‖HvdH.fxC p ((ws'.getD q []).getD (c : ℕ) (0, 0)) -
              Work.SynFFT.dftN r t sgn u q c‖ +
            (2 : ℝ) ^ p * ‖Work.SynFFT.dftN r t sgn u q c - Work.SynFFT.dftN r t sgn a q c‖ := by
            ring
        _ ≤ (k : ℝ) + e := add_le_add hAC hCB
        _ = e + (k : ℝ) := by ring
    · -- the output value is a slice, so its size is bounded by `slL`
      exact Work.SynFFT.vsz_of_SlOK p r t hp0 ws' ⟨hws'_len, hws'_disc⟩
  · -- the cost is unchanged
    intro vs' _
    exact le_rfl

end Work.SynFFT
