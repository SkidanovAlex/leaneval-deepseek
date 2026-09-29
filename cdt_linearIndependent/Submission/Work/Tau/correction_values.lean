import Mathlib
import Submission.Work.Tau.defs

/-!
# The two correction-integral values of the fine-holonomy example

This module evaluates the `correctionFun` halves of the paper's `integrated lcm`
`I_u^v(w)` (Calegari–Dimitrov–Tang, arXiv:2408.15403, §"The cost of an integration")
for the two configurations of the project's Area Tau:

* `∫_{7/4}^{17} correctionFun (7/4) = 7129/5040 = (1/2)·H₉`
* `∫_{2}^{14} correctionFun 2 = 49/40 = (1/2)·H₆`,

where `H_n = Σ_{k≤n} 1/k` is the `n`-th harmonic number.  These are the correction
integrands entering `tauSharpAt eC (7/4)` and `tauSharpAt eA 2` respectively (see
`Submission/Work/Tau/tau_values.lean`).

## The mathematics

For `w ≥ 1` write `B := max 1 w = w` and `m₀ := max 0 (w-1) = w-1`, so that

`correctionFun w t = max (t / ⌊(t + m₀)/B⌋₊ - w) 0`.

The floor `⌊(t + w - 1)/w⌋₊` equals `k : ℕ` exactly on the half-open piece
`A k ≤ t < A (k+1)`, `A k := 1 + (k-1)·w`, and there

`correctionFun w t = max ((t - k·w)/k) 0`.

Since `A k = k·w - (w-1)`, the graph of `correctionFun w` is a sequence of
*spikes*: it vanishes on `[A k, k·w]` and then rises linearly with slope `1/k` on
`[k·w, k·w + 1] = [k·w, A (k+1)]`, dropping back to `0` at the breakpoint
`A (k+1) = k·w + 1`.  Each full spike therefore contributes

`∫_{k·w}^{k·w+1} (t - k·w)/k dt = 1/(2k)`,

and the intermediate zero pieces contribute nothing; the integral accumulates the
harmonic half-sums `(1/2)·Σ_{k=k₀}^{n} 1/k`.  This is formalised as
`integral_spike_unit` (one spike), `integral_spike_accum` (the finite sum), on top of
the two general facts `correctionFun_eq_piece` (the pointwise piecewise description)
and `integral_correctionFun_piece` (the integral over one piece).

For `w = 7/4` the spikes `k = 1, …, 9` fill `[7/4, 67/4]` and `[67/4, 17]` is a tail
of the zero piece `k = 10` (the spike `k = 10` only starts at `17.5 > 17`), giving
`(1/2)·H₉ = 7129/5040`.  For `w = 2` the spikes `k = 1, …, 6` fill `[2, 13]` and the
remaining `[13, 14]` lies in the zero piece `k = 7`, giving `(1/2)·H₆ = 49/40`.
-/

namespace Work.Tau

open MeasureTheory intervalIntegral
open scoped BigOperators

/-- The integral of the linear half of a spike: `∫_a^b (t-c)/k = ((b-c)² - (a-c)²)/(2k)`. -/
lemma integral_corr_linear (c k : ℝ) (hk : k ≠ 0) (a b : ℝ) :
    ∫ t in a..b, (t - c)/k = ((b - c)^2 - (a - c)^2)/(2*k) := by
  rw [intervalIntegral.integral_div]
  rw [intervalIntegral.integral_sub intervalIntegrable_id intervalIntegrable_const,
    integral_id, intervalIntegral.integral_const]
  simp only [smul_eq_mul]
  field_simp
  ring

/-- `∫_a^b max ((t-c)/k) 0 = (max (b-c) 0)²/(2k) - (max (a-c) 0)²/(2k)` for `k > 0`: the
integral of the clipped linear function, with the primitive
`x ↦ (max (x-c) 0)²/(2k)` evaluated at the endpoints. -/
theorem integral_max_div (c : ℝ) {k : ℝ} (hk : 0 < k) (a b : ℝ) (hab : a ≤ b) :
    ∫ t in a..b, max ((t - c)/k) 0
      = (max (b - c) 0)^2/(2*k) - (max (a - c) 0)^2/(2*k) := by
  set g : ℝ → ℝ := fun t => max ((t - c)/k) 0 with hg
  have hcont : Continuous g := by rw [hg]; fun_prop
  have key_lin : ∀ {x y : ℝ}, c ≤ x → x ≤ y →
      ∫ t in x..y, g t = ((y - c)^2 - (x - c)^2)/(2*k) := by
    intro x y hcx hxy
    have hEq : Set.EqOn g (fun t => (t - c)/k) (Set.uIcc x y) := by
      intro t ht
      rw [Set.uIcc_of_le hxy, Set.mem_Icc] at ht
      simp only [hg]
      exact max_eq_left (div_nonneg (by linarith [ht.1]) hk.le)
    rw [intervalIntegral.integral_congr hEq, integral_corr_linear c k (ne_of_gt hk) x y]
  have key_zero : ∀ {x y : ℝ}, y ≤ c → x ≤ y → ∫ t in x..y, g t = 0 := by
    intro x y hyc hxy
    have hEq : Set.EqOn g (fun _ => (0:ℝ)) (Set.uIcc x y) := by
      intro t ht
      rw [Set.uIcc_of_le hxy, Set.mem_Icc] at ht
      simp only [hg]
      exact max_eq_right (div_nonpos_of_nonpos_of_nonneg (by linarith [ht.2]) hk.le)
    rw [intervalIntegral.integral_congr hEq]; simp
  rcases le_or_gt b c with hbc | hbc
  · rw [key_zero hbc hab, max_eq_right (by linarith : b - c ≤ 0),
      max_eq_right (by linarith : a - c ≤ 0)]
    ring
  · rcases le_or_gt c a with hca | hca
    · rw [key_lin hca hab, max_eq_left (by linarith : 0 ≤ b - c),
        max_eq_left (by linarith : 0 ≤ a - c)]
      ring
    · have h1 := key_zero (le_refl c) hca.le
      have h2 := key_lin (le_refl c) hbc.le
      have hadd := integral_add_adjacent_intervals (hcont.intervalIntegrable (μ := volume) a c)
        (hcont.intervalIntegrable (μ := volume) c b)
      rw [h1, zero_add] at hadd
      rw [← hadd, h2, max_eq_left (by linarith : 0 ≤ b - c),
        max_eq_right (by linarith : a - c ≤ 0)]
      ring

/-- **The pointwise piecewise description of `correctionFun`.**  For `w ≥ 1` and `k ≥ 1`, on
the half-open piece `1 + (k-1)·w ≤ t < 1 + k·w` the floor `⌊(t + (w-1))/w⌋₊` equals `k` and
`correctionFun w t = max ((t - k·w)/k) 0`. -/
theorem correctionFun_eq_piece (w : ℝ) (hw : 1 ≤ w) (k : ℕ) (hk : 1 ≤ k) (t : ℝ)
    (h1 : 1 + ((k:ℝ) - 1) * w ≤ t) (h2 : t < 1 + (k:ℝ) * w) :
    Submission.CDT.IntegratedLcm.correctionFun w t
      = max ((t - (k:ℝ) * w) / (k:ℝ)) 0 := by
  have hw1 : max 0 (w - 1) = w - 1 := max_eq_right (by linarith)
  have hw2 : max 1 w = w := max_eq_right hw
  have hkpos : (0:ℝ) < (k:ℝ) := by exact_mod_cast hk
  have hfl : ⌊(t + max 0 (w - 1)) / max 1 w⌋₊ = k := by
    rw [hw1, hw2]
    refine Nat.floor_eq_on_Ico k _ ⟨?_, ?_⟩
    · rw [le_div_iff₀ (by linarith : (0:ℝ) < w)]; linarith
    · rw [div_lt_iff₀ (by linarith : (0:ℝ) < w)]; linarith
  rw [Submission.CDT.IntegratedLcm.correctionFun, hfl]
  congr 1
  rw [sub_div, mul_div_cancel_left₀ w (ne_of_gt hkpos)]

/-- **The integral of `correctionFun` over one piece.**  For `w ≥ 1`, `k ≥ 1` and
`a ≤ b` inside the closed piece `[1 + (k-1)·w, 1 + k·w]`,

`∫_a^b correctionFun w = (max (b - k·w) 0)²/(2k) - (max (a - k·w) 0)²/(2k)`.

(The pointwise identity holds on the half-open piece; the single endpoint `1 + k·w` is a
null set for the interval integral.) -/
theorem integral_correctionFun_piece (w : ℝ) (hw : 1 ≤ w) (k : ℕ) (hk : 1 ≤ k) {a b : ℝ}
    (hab : a ≤ b) (ha : 1 + ((k:ℝ) - 1) * w ≤ a) (hb : b ≤ 1 + (k:ℝ) * w) :
    ∫ t in a..b, Submission.CDT.IntegratedLcm.correctionFun w t
      = (max (b - (k:ℝ)*w) 0)^2/(2*(k:ℝ)) - (max (a - (k:ℝ)*w) 0)^2/(2*(k:ℝ)) := by
  have hkpos : (0:ℝ) < (k:ℝ) := by exact_mod_cast hk
  have hEq : ∀ᵐ t ∂volume, t ∈ Set.uIoc a b →
      Submission.CDT.IntegratedLcm.correctionFun w t = max ((t - (k:ℝ)*w)/(k:ℝ)) 0 := by
    rw [MeasureTheory.ae_iff]
    apply MeasureTheory.measure_mono_null _ (MeasureTheory.measure_singleton (1 + (k:ℝ)*w))
    intro t ht
    simp only [Set.mem_ofPred_eq] at ht
    by_contra hne
    rw [Classical.not_imp] at ht
    obtain ⟨htu, hne'⟩ := ht
    rw [Set.uIoc_of_le hab] at htu
    obtain ⟨hta, htb⟩ := htu
    exact hne' (correctionFun_eq_piece w hw k hk t (le_trans ha (le_of_lt hta))
      (lt_of_le_of_ne (le_trans htb hb) hne))
  rw [intervalIntegral.integral_congr_ae hEq,
    integral_max_div ((k:ℝ)*w) hkpos a b hab]

/-- **One full spike.**  For `w ≥ 1` and `k ≥ 1`,
`∫_{k·w}^{(k+1)·w} correctionFun w = 1/(2k)`: over `[k·w, k·w+1]` the function is the
linear `(t - k·w)/k`, and over `[k·w+1, (k+1)·w]` it vanishes. -/
theorem integral_spike_unit (w : ℝ) (hw : 1 ≤ w) (k : ℕ) (hk : 1 ≤ k) :
    ∫ t in ((k:ℝ)*w)..(((k+1:ℕ):ℝ)*w), Submission.CDT.IntegratedLcm.correctionFun w t
      = 1/(2*(k:ℝ)) := by
  have hk1 : (1:ℕ) ≤ k + 1 := by omega
  have hkw1 : (1:ℝ) ≤ (k:ℝ) := by exact_mod_cast hk
  set g := Submission.CDT.IntegratedLcm.correctionFun w with hg
  have hI1 : IntervalIntegrable g volume ((k:ℝ)*w) ((k:ℝ)*w + 1) :=
    Submission.CDT.FineHolonomy.intervalIntegrable_correctionFun' w _ _
      (by nlinarith [hkw1, hw]) (by linarith)
  have hI2 : IntervalIntegrable g volume ((k:ℝ)*w + 1) (((k+1:ℕ):ℝ)*w) :=
    Submission.CDT.FineHolonomy.intervalIntegrable_correctionFun' w _ _
      (by nlinarith [hkw1, hw]) (by push_cast; nlinarith [hkw1, hw])
  have e1 : ∫ t in ((k:ℝ)*w)..((k:ℝ)*w + 1), g t = 1/(2*(k:ℝ)) := by
    rw [hg, integral_correctionFun_piece w hw k hk (by linarith) (by nlinarith [hkw1, hw])
      (le_of_eq (by ring))]
    rw [show (k:ℝ)*w + 1 - (k:ℝ)*w = 1 by ring, show (k:ℝ)*w - (k:ℝ)*w = 0 by ring]
    norm_num
  have e2 : ∫ t in ((k:ℝ)*w + 1)..(((k+1:ℕ):ℝ)*w), g t = 0 := by
    rw [hg, integral_correctionFun_piece w hw (k+1) hk1 (by push_cast; nlinarith [hkw1, hw])
      (by push_cast; linarith) (by push_cast; linarith)]
    rw [show ((k+1:ℕ):ℝ)*w - ((k+1:ℕ):ℝ)*w = 0 by ring,
      show ((k:ℝ)*w + 1) - ((k+1:ℕ):ℝ)*w = 1 - w by push_cast; ring]
    rw [max_eq_right (by linarith : (1:ℝ) - w ≤ 0), max_eq_right (by norm_num : (0:ℝ) ≤ 0)]
    ring
  have hsplit := integral_add_adjacent_intervals hI1 hI2
  rw [e1, e2, add_zero] at hsplit
  exact hsplit.symm

/-- **The accumulated spikes.**  For `w ≥ 1` and `k₀ ≥ 1`, and every `n`,
`∫_{k₀·w}^{(k₀+n)·w} correctionFun w = Σ_{j<n} 1/(2(k₀+j))`
(the interval contains exactly the full spikes `k₀, …, k₀+n-1`). -/
theorem integral_spike_accum (w : ℝ) (hw : 1 ≤ w) (k₀ : ℕ) (hk₀ : 1 ≤ k₀) :
    ∀ n : ℕ, ∫ t in ((k₀:ℝ)*w)..(((k₀+n:ℕ):ℝ)*w),
        Submission.CDT.IntegratedLcm.correctionFun w t
      = ∑ j ∈ Finset.range n, 1/(2*((k₀+j:ℕ):ℝ)) := by
  have hk₀w : (1:ℝ) ≤ (k₀:ℝ)*w := by
    have : (1:ℝ) ≤ (k₀:ℝ) := by exact_mod_cast hk₀
    nlinarith [this, hw]
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    have hnat : k₀ + (n+1) = (k₀+n) + 1 := by omega
    rw [hnat, Finset.sum_range_succ, ← ih]
    have hsu := integral_spike_unit w hw (k₀+n) (by omega)
    have hI1 : IntervalIntegrable (Submission.CDT.IntegratedLcm.correctionFun w) volume
        ((k₀:ℝ)*w) (((k₀+n:ℕ):ℝ)*w) :=
      Submission.CDT.FineHolonomy.intervalIntegrable_correctionFun' w _ _ hk₀w
        (by push_cast; nlinarith [hk₀w, hw])
    have hI2 : IntervalIntegrable (Submission.CDT.IntegratedLcm.correctionFun w) volume
        (((k₀+n:ℕ):ℝ)*w) ((((k₀+n)+1:ℕ):ℝ)*w) :=
      Submission.CDT.FineHolonomy.intervalIntegrable_correctionFun' w _ _
        (by push_cast; nlinarith [hk₀w, hw]) (by push_cast; nlinarith [hk₀w, hw])
    have hadj := integral_add_adjacent_intervals hI1 hI2
    rw [hsu] at hadj
    linarith [hadj]

/-- The two correction-integral values of the fine-holonomy example:
`∫_{7/4}^{17} correctionFun (7/4) = 7129/5040` and `∫_{2}^{14} correctionFun 2 = 49/40`. -/
theorem correction_values :
    (∫ t in (7 / 4 : ℝ)..17, Submission.CDT.IntegratedLcm.correctionFun (7 / 4) t)
        = 7129 / 5040 ∧
      (∫ t in (2 : ℝ)..14, Submission.CDT.IntegratedLcm.correctionFun 2 t) = 49 / 40 := by
  constructor
  · -- `w = 7/4`: spikes `k = 1, …, 9` fill `[7/4, 67/4]`, the tail `[17, 35/2]` is zero.
    have hacc := integral_spike_accum (7/4) (by norm_num) 1 (by norm_num) 9
    have hzero : ∫ t in (17:ℝ)..(35/2:ℝ),
        Submission.CDT.IntegratedLcm.correctionFun (7/4) t = 0 := by
      rw [integral_correctionFun_piece (7/4) (by norm_num) 10 (by norm_num)
        (by norm_num) (by norm_num) (by norm_num)]
      norm_num
    have hI1 : IntervalIntegrable (Submission.CDT.IntegratedLcm.correctionFun (7/4)) volume
        (7/4) 17 :=
      Submission.CDT.FineHolonomy.intervalIntegrable_correctionFun' (7/4) _ _
        (by norm_num) (by norm_num)
    have hI2 : IntervalIntegrable (Submission.CDT.IntegratedLcm.correctionFun (7/4)) volume
        17 (35/2) :=
      Submission.CDT.FineHolonomy.intervalIntegrable_correctionFun' (7/4) _ _
        (by norm_num) (by norm_num)
    have hadj := intervalIntegral.integral_add_adjacent_intervals hI1 hI2
    rw [hzero, add_zero] at hadj
    rw [hadj]
    rw [show ((1:ℕ):ℝ)*(7/4) = (7/4:ℝ) by norm_num,
        show (((1+9:ℕ):ℝ)*(7/4)) = (35/2:ℝ) by norm_num] at hacc
    rw [hacc]
    norm_num [Finset.sum_range_succ]
  · -- `w = 2`: spikes `k = 1, …, 6` fill `[2, 13]`, the tail `[13, 14]` is zero.
    have hacc := integral_spike_accum (2:ℝ) (by norm_num) 1 (by norm_num) 6
    rw [show ((1:ℕ):ℝ)*2 = (2:ℝ) by norm_num,
        show (((1+6:ℕ):ℝ)*2) = (14:ℝ) by norm_num] at hacc
    rw [hacc]
    norm_num [Finset.sum_range_succ]

end Work.Tau
