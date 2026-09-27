import Mathlib
import Submission.Work.EQ.fan_estimates
import Submission.Work.EQ.germC_facts
import Submission.Work.EQ.eqRelC_candChain
import Submission.Work.EQ.H0_invParam_ge

/-!
# The candidate chain is a chain, given its middle

`CycleDefs.candChain a h f [] b M c u` is the explicit candidate chain whose forward fan word is
`f` (of length `M`), whose forward tail from depth `M` is the principal germ
`germC a h (λ^n u)`, whose `M` steps from index `-M` to index `0` are the backward images along
the sign list `b`, and whose index `-M` is the mirror of the germ at `λ^M (c/u)` (the junction
identity `hjun`); below `-M` it is the mirrored germ of the (empty) unstable word.

This file proves that such a candidate chain is a chain of the equichordal relation as soon as
* the local germ recursion `RegPair a (germC u) (germC (λu))` holds on a disc of radius `ρ`,
* the two germ arguments at the ends of the fan/germ windows are small:
  `λ^M ‖u‖ < ρ` and `λ^M ‖c/u‖ < ρ`,
* the `2M + 1` *middle* pairs `-M-1 ≤ n ≤ M-1` are regular pairs.

The index line is split into three windows: the forward germ window `n ≥ M`, the middle window
`-M-1 ≤ n ≤ M-1` (the hypothesis `hmiddle`), and the far backward (mirrored germ) window
`n ≤ -M-2`.  In the two far windows every germ argument is `λ^k` times `u` (resp. `c/u`) with
`k ≥ M`, hence has modulus `< ρ` by the size hypotheses, so `hreg` applies; the backward window
uses the mirror-swap symmetry `RegPair a P Q ↔ RegPair a (eqMirror Q) (eqMirror P)`
(`H0_invParam_ge_regPair_mirror`).
-/

set_option linter.unusedVariables false

namespace Work.EQ.Ladf

open Work.EQ Filter

noncomputable section

/-! ## The value of the candidate chain in the far windows -/

/-- The forward value of `candChain a h f [] b M c z` in the germ window: for `m ≥ M` the
index-`m` point is the principal germ at `λ^m z`.  (At `m = M` this uses `f.drop M = []`, i.e.
`hf`, together with `fan a h [] = germC a h`.) -/
private theorem candVal_germ {a : ℝ} {h : ℂ → ℂ} {f b : List Bool} {M : ℕ}
    (hf : f.length = M) {c z : ℂ} {m : ℕ} (hm : M ≤ m) :
    (candChain a h f [] b M c z).1 (m : ℤ) =
      germC a h (((eqLam a : ℝ) : ℂ) ^ m * z) := by
  simp only [candChain]
  rw [if_pos (Int.natCast_nonneg m), Int.toNat_natCast, zpow_natCast]
  by_cases hle : m ≤ M
  · rw [if_pos hle, List.drop_eq_nil_of_le (by omega), fan_nil]
  · rw [if_neg hle]

/-- The backward value of `candChain a h f [] b M c z`: for `m ≥ M` the index `-(m)` is the
mirror of the principal germ at `λ^m (c/z)`.  At `m = M` this is the junction identity `hjun`
(the backward fan of `b` over `[-M,0]` meets the mirrored germ). -/
private theorem candVal_neg {a : ℝ} {h : ℂ → ℂ} {f b : List Bool} {M : ℕ}
    (hf : f.length = M) (hb : b.length = M) {c z : ℂ} {m : ℕ} (hm : M ≤ m)
    (hjun : bwdP a b (fan a h f z) =
      eqMirror (germC a h (((eqLam a : ℝ) : ℂ) ^ M * (c / z)))) :
    (candChain a h f [] b M c z).1 (-(m : ℤ)) =
      eqMirror (germC a h (((eqLam a : ℝ) : ℂ) ^ m * (c / z))) := by
  rcases Nat.eq_zero_or_pos m with hm0 | hmpos
  · subst hm0
    have hM0 : M = 0 := by omega
    subst hM0
    obtain rfl : f = [] := List.eq_nil_of_length_eq_zero hf
    obtain rfl : b = [] := List.eq_nil_of_length_eq_zero hb
    simpa [candChain] using hjun
  · have hneg : ¬ ((0 : ℤ) ≤ -(m : ℤ)) := by omega
    simp only [candChain]
    rw [if_neg hneg, neg_neg, Int.toNat_natCast]
    by_cases hle : m ≤ M
    · have hmM : m = M := by omega
      subst hmM
      rw [if_pos hle, List.take_of_length_le (le_of_eq hb), hjun]
    · rw [if_neg hle]
      simp only [List.drop_nil, fan_nil, zpow_natCast]

/-- Size estimate for the far windows: if `λ^M ‖z‖ < ρ` then `‖λ^m z‖ < ρ` for every `m ≥ M`
(here `0 < λ < 1`). -/
private theorem eqLam_pow_mul_norm_lt {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {ρ : ℝ} {M : ℕ}
    {z : ℂ} (hz : (eqLam a) ^ M * ‖z‖ < ρ) {m : ℕ} (hm : M ≤ m) :
    ‖(((eqLam a : ℝ) : ℂ) ^ m * z)‖ < ρ := by
  have hl0 : 0 < eqLam a := eqLam_pos' ha0 ha1
  have hl1 : eqLam a < 1 := eqLam_lt_one' ha0 ha1
  have hnorm : ‖(((eqLam a : ℝ) : ℂ) ^ m)‖ = (eqLam a) ^ m := by
    rw [norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hl0]
  calc ‖(((eqLam a : ℝ) : ℂ) ^ m * z)‖
      = (eqLam a) ^ m * ‖z‖ := by rw [norm_mul, hnorm]
    _ ≤ (eqLam a) ^ M * ‖z‖ :=
        mul_le_mul_of_nonneg_right (pow_le_pow_of_le_one hl0.le hl1.le hm) (norm_nonneg z)
    _ < ρ := hz

/-! ## The main theorem -/

/-- **The candidate chain with a prescribed middle is a chain.** -/
theorem candChain_isChain_of_middle {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {h : ℂ → ℂ} {r : ℝ}
    (hh : IsStableGerm a h r) {f b : List Bool} {M : ℕ} (hf : f.length = M) (hb : b.length = M)
    {c : ℂ} (hc : c ≠ 0) {ρ : ℝ} (hρ : 0 < ρ)
    (hreg : ∀ u : ℂ, ‖u‖ < ρ → RegPair a (germC a h u) (germC a h ((eqLam a : ℂ) * u)))
    {u : ℂ} (hu0 : u ≠ 0) (hcu0 : c / u ≠ 0)
    (hu : (eqLam a) ^ M * ‖u‖ < ρ)
    (hcu : (eqLam a) ^ M * ‖c / u‖ < ρ)
    (hjun : bwdP a b (fan a h f u) = eqMirror (germC a h (((eqLam a : ℝ) : ℂ) ^ M * (c / u))))
    (hmiddle : ∀ n : ℤ, -((M : ℤ)) - 1 ≤ n → n ≤ (M : ℤ) - 1 →
      RegPair a ((candChain a h f [] b M c u).1 n) ((candChain a h f [] b M c u).1 (n+1))) :
    IsChain a h (candChain a h f [] b M c u) := by
  refine ⟨?_, hu0, hcu0, ?_, ?_⟩
  · -- the regular-pair condition in the three windows
    intro n
    by_cases hM : (M : ℤ) ≤ n
    · -- forward germ window: `n = m ≥ M`
      have hn0 : 0 ≤ n := by omega
      obtain ⟨m, rfl⟩ : ∃ m : ℕ, n = (m : ℤ) := ⟨n.toNat, (Int.toNat_of_nonneg hn0).symm⟩
      have hm : M ≤ m := by exact_mod_cast hM
      have h1 : (candChain a h f [] b M c u).1 (m : ℤ) =
          germC a h (((eqLam a : ℝ) : ℂ) ^ m * u) := candVal_germ hf hm
      have h2 : (candChain a h f [] b M c u).1 ((m : ℤ) + 1) =
          germC a h (((eqLam a : ℝ) : ℂ) ^ (m + 1) * u) := by
        rw [show (m : ℤ) + 1 = ((m + 1 : ℕ) : ℤ) by omega]
        exact candVal_germ hf (by omega)
      rw [h1, h2]
      have hnorm : ‖(((eqLam a : ℝ) : ℂ) ^ m * u)‖ < ρ := eqLam_pow_mul_norm_lt ha0 ha1 hu hm
      have hreg' := hreg (((eqLam a : ℝ) : ℂ) ^ m * u) hnorm
      have hw : (eqLam a : ℂ) * ((((eqLam a : ℝ) : ℂ) ^ m) * u)
          = (((eqLam a : ℝ) : ℂ) ^ (m + 1)) * u := by
        rw [pow_succ]; ring
      simpa [hw] using hreg'
    · have hnle : n ≤ (M : ℤ) - 1 := by omega
      by_cases hbwd : n ≤ -((M : ℤ)) - 2
      · -- far backward (mirrored germ) window: `n = -m` with `m ≥ M + 2`
        have hm2 : M + 2 ≤ (-n).toNat :=
          (Int.le_toNat (show (0 : ℤ) ≤ -n by omega)).mpr (by omega)
        obtain ⟨m, rfl⟩ : ∃ m : ℕ, n = -((m : ℤ)) := ⟨(-n).toNat, by
          have htoNat := Int.toNat_of_nonneg (show (0 : ℤ) ≤ -n by omega)
          omega⟩
        have hm1 : M ≤ m - 1 := by omega
        have h1 : (candChain a h f [] b M c u).1 (-(m : ℤ)) =
            eqMirror (germC a h (((eqLam a : ℝ) : ℂ) ^ m * (c / u))) :=
          candVal_neg hf hb (by omega) hjun
        have h2 : (candChain a h f [] b M c u).1 (-(m : ℤ) + 1) =
            eqMirror (germC a h (((eqLam a : ℝ) : ℂ) ^ (m - 1) * (c / u))) := by
          rw [show -(m : ℤ) + 1 = -(((m - 1 : ℕ)) : ℤ) by omega]
          exact candVal_neg hf hb hm1 hjun
        rw [h1, h2]
        refine H0_invParam_ge_regPair_mirror.mpr ?_
        have hnorm : ‖(((eqLam a : ℝ) : ℂ) ^ (m - 1) * (c / u))‖ < ρ :=
          eqLam_pow_mul_norm_lt ha0 ha1 hcu hm1
        have hreg' := hreg (((eqLam a : ℝ) : ℂ) ^ (m - 1) * (c / u)) hnorm
        have hw : (eqLam a : ℂ) * ((((eqLam a : ℝ) : ℂ) ^ (m - 1)) * (c / u))
            = (((eqLam a : ℝ) : ℂ) ^ m) * (c / u) := by
          have hpow : (((eqLam a : ℝ) : ℂ) ^ m)
              = (((eqLam a : ℝ) : ℂ) ^ (m - 1)) * (eqLam a : ℂ) := by
            conv_lhs => rw [show m = (m - 1) + 1 by omega]
            rw [pow_succ]
          rw [hpow]; ring
        simpa [hw] using hreg'
      · -- the prescribed middle window
        exact hmiddle n (by omega) hnle
  · -- forward tail
    filter_upwards [Filter.eventually_ge_atTop M] with m hm
    exact candVal_germ hf hm
  · -- backward tail
    filter_upwards [Filter.eventually_ge_atTop M] with m hm
    have h := candVal_neg hf hb hm hjun
    simpa [ugermC] using h

end

end Work.EQ.Ladf
