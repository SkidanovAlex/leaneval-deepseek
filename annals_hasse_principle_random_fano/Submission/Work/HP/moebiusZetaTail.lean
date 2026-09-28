import Mathlib
import Submission.Work.HP.MMDefs
import Submission.Work.HP.MDEstimates.moebius_zeta_tsum_mul
import Submission.Work.HP.MDEstimates.pSeries_tail_tsum_le

set_option autoImplicit false
noncomputable section

open Finset

namespace Work.HP

/-!
# The Möbius/zeta tail bound `|∑_{ℓ ≤ X} μ(ℓ)/ℓ^s - 1/ζ(s)| ≤ C X^{1-s}`

For real `s > 1` the partial sums of the Dirichlet series of the Möbius function converge to
`1/ζ(s)`, the error being `O(X^{1-s})`.  Since `|μ| ≤ 1`, the whole content is that the tail of
the (absolutely convergent) series is dominated term by term by the tail of the positive `ζ`-series,
together with the classical identity `(∑ μ(n)/n^s)·(∑ 1/n^s) = 1`.

The two analytic inputs are imported from the workspace:

* `Work.HP.MDEstimates.moebius_zeta_tsum_mul` : `(∑' n : ℕ+, μ n / n^s) * (∑' n : ℕ+, 1 / n^s) = 1`,
  obtained there from the complex `LSeries` identity `LSeries 1 · LSeries ↗μ = 1`;
* `Work.HP.MDEstimates.pSeries_tail_tsum_le` : the integral-test bound
  `∑' j, 1/(j+N+1)^s ≤ N^{1-s}/(s-1)`.

The argument in this file is the assembly: rewrite the truncated sum over `Icc 1 ⌊X⌋₊` as a sum over
`range ⌊X⌋₊`, split off the tail of the infinite series, dominate it by the `p`-series tail, and
finally compare `⌊X⌋₊` with `X/2`.
-/

/-- `|(μ n : ℝ)| ≤ 1`. -/
private lemma abs_moebius_cast_le_one (n : ℕ) :
    |(ArithmeticFunction.moebius n : ℝ)| ≤ 1 := by
  rw [← Int.cast_abs]
  exact_mod_cast ArithmeticFunction.abs_moebius_le_one

/-- The term `μ(k+1)/(k+1)^s` of the Möbius Dirichlet series, indexed from `k = 0`. -/
private def mobT (s : ℝ) (k : ℕ) : ℝ :=
  (ArithmeticFunction.moebius (k + 1) : ℝ) / (((k + 1 : ℕ)) : ℝ) ^ s

/-- The term `1/(k+1)^s` of the `ζ`-series, indexed from `k = 0`. -/
private def zetT (s : ℝ) (k : ℕ) : ℝ :=
  1 / (((k + 1 : ℕ)) : ℝ) ^ s

private lemma zetT_summable (s : ℝ) (hs : 1 < s) : Summable (zetT s) := by
  have h : Summable (fun k : ℕ => 1 / |(k : ℝ) + 1| ^ s) :=
    (Real.summable_one_div_nat_add_rpow 1 s).mpr hs
  refine h.congr (fun k => ?_)
  rw [zetT, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (k : ℝ) + 1)]
  push_cast
  ring_nf

private lemma mobT_summable (s : ℝ) (hs : 1 < s) : Summable (mobT s) := by
  refine Summable.of_norm_bounded (g := zetT s) (zetT_summable s hs) (fun k => ?_)
  have hpos : (0 : ℝ) < (((k + 1 : ℕ)) : ℝ) ^ s := Real.rpow_pos_of_pos (by positivity) s
  rw [Real.norm_eq_abs, mobT, zetT, abs_div, abs_of_pos hpos, div_le_div_iff_of_pos_right hpos]
  exact abs_moebius_cast_le_one (k + 1)

private lemma zetT_tsum_pos (s : ℝ) (hs : 1 < s) : 0 < ∑' k : ℕ, zetT s k := by
  refine Summable.tsum_pos (zetT_summable s hs) (fun k => ?_) 0 ?_
  · rw [zetT]; positivity
  · rw [zetT]; norm_num

private lemma zetT_tsum_form (s : ℝ) :
    (∑' k : ℕ, zetT s k) = ∑' k : ℕ, 1 / ((k : ℝ) + 1) ^ s := by
  refine tsum_congr (fun k => ?_)
  rw [zetT]
  push_cast
  ring_nf

/-- The Möbius Dirichlet series evaluated in the `ℕ+`-indexing used by
`moebius_zeta_tsum_mul`. -/
private lemma mobT_tsum_eq (s : ℝ) :
    (∑' k : ℕ, mobT s k)
      = ∑' n : ℕ+, (ArithmeticFunction.moebius (n : ℕ) : ℝ) / ((n : ℕ) : ℝ) ^ s := by
  have h : (∑' k : ℕ, mobT s k)
      = ∑' k : ℕ, (fun n : ℕ => (ArithmeticFunction.moebius n : ℝ) / (n : ℝ) ^ s) (k + 1) := by
    refine tsum_congr (fun k => ?_)
    rw [mobT]
  rw [h]
  exact (tsum_pnat_eq_tsum_succ
    (f := fun n : ℕ => (ArithmeticFunction.moebius n : ℝ) / (n : ℝ) ^ s)).symm

/-- The `ζ`-series evaluated in the `ℕ+`-indexing used by `moebius_zeta_tsum_mul`. -/
private lemma zetT_tsum_eq (s : ℝ) :
    (∑' k : ℕ, zetT s k) = ∑' n : ℕ+, 1 / ((n : ℕ) : ℝ) ^ s := by
  have h : (∑' k : ℕ, zetT s k)
      = ∑' k : ℕ, (fun n : ℕ => 1 / (n : ℝ) ^ s) (k + 1) := by
    refine tsum_congr (fun k => ?_)
    rw [zetT]
  rw [h]
  exact (tsum_pnat_eq_tsum_succ (f := fun n : ℕ => 1 / (n : ℝ) ^ s)).symm

/-- The limit of the Möbius series is `1/ζ(s)`: the Dirichlet convolution identity
`(∑ μ(n)/n^s)(∑ 1/n^s) = 1`, together with the positivity of `∑ 1/n^s`. -/
private lemma mobT_tsum_eq_inv (s : ℝ) (hs : 1 < s) :
    (∑' k : ℕ, mobT s k) = 1 / (∑' k : ℕ, zetT s k) := by
  have hVT : (∑' k : ℕ, mobT s k) * (∑' k : ℕ, zetT s k) = 1 := by
    rw [mobT_tsum_eq, zetT_tsum_eq]
    exact MDEstimates.moebius_zeta_tsum_mul s hs
  rw [eq_div_iff (ne_of_gt (zetT_tsum_pos s hs))]
  exact hVT

/-- The tail of the Möbius series is `O(N^{1-s})`. -/
private lemma mobT_tail (s : ℝ) (hs : 1 < s) (N : ℕ) (hN : 1 ≤ N) :
    |∑' j : ℕ, mobT s (j + N)| ≤ (N : ℝ) ^ (1 - s) / (s - 1) := by
  have hsum : Summable (fun j : ℕ => mobT s (j + N)) :=
    (summable_nat_add_iff N).mpr (mobT_summable s hs)
  have hnorms : Summable (fun j : ℕ => ‖mobT s (j + N)‖) := hsum.norm
  have hupd : Summable (fun j : ℕ => 1 / (((j + N + 1 : ℕ)) : ℝ) ^ s) := by
    have h : Summable (fun n : ℕ => 1 / |(n : ℝ) + (N + 1)| ^ s) :=
      (Real.summable_one_div_nat_add_rpow (N + 1) s).mpr hs
    refine h.congr (fun n => ?_)
    rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ (n : ℝ) + (N + 1))]
    push_cast
    ring_nf
  have hle : ∀ j : ℕ, ‖mobT s (j + N)‖ ≤ 1 / (((j + N + 1 : ℕ)) : ℝ) ^ s := by
    intro j
    have hpos : (0 : ℝ) < (((j + N + 1 : ℕ)) : ℝ) ^ s := Real.rpow_pos_of_pos (by positivity) s
    rw [Real.norm_eq_abs, mobT, abs_div, abs_of_pos hpos, div_le_div_iff_of_pos_right hpos]
    exact abs_moebius_cast_le_one (j + N + 1)
  have h1 : |∑' j : ℕ, mobT s (j + N)| ≤ ∑' j : ℕ, ‖mobT s (j + N)‖ := by
    have := norm_tsum_le_tsum_norm hnorms
    rwa [Real.norm_eq_abs] at this
  have h2 : ∑' j : ℕ, ‖mobT s (j + N)‖ ≤ ∑' j : ℕ, 1 / (((j + N + 1 : ℕ)) : ℝ) ^ s :=
    Summable.tsum_le_tsum hle hnorms hupd
  exact le_trans h1 (le_trans h2 (MDEstimates.pSeries_tail_tsum_le s hs N hN))

/-- The truncated sum over `Icc 1 N` rewritten as a sum over `range N` of the shifted terms. -/
private lemma sum_Icc_eq_sum_range_mobT (s : ℝ) (N : ℕ) :
    (∑ ℓ ∈ Finset.Icc 1 N, (ArithmeticFunction.moebius ℓ : ℝ) / (ℓ : ℝ) ^ s)
      = ∑ i ∈ Finset.range N, mobT s i := by
  rw [← Finset.Ico_succ_right_eq_Icc (1 : ℕ) N, Finset.sum_Ico_eq_sum_range]
  refine Finset.sum_congr ?_ ?_
  · simp
  · intro k _
    rw [mobT]
    push_cast
    ring_nf

theorem moebiusZetaTail (s : ℝ) (hs : 1 < s) :
    ∃ C : ℝ, 0 < C ∧ ∀ X : ℝ, 1 ≤ X →
      |(∑ ℓ ∈ Finset.Icc 1 ⌊X⌋₊, ((ArithmeticFunction.moebius ℓ : ℝ) / (ℓ : ℝ) ^ s)) -
          1 / (∑' k : ℕ, 1 / ((k : ℝ) + 1) ^ s)| ≤ C / X ^ (s - 1) := by
  have hspos : 0 < s - 1 := by linarith
  refine ⟨2 ^ (s - 1) / (s - 1), by positivity, ?_⟩
  intro X hX
  have hXpos : 0 < X := by linarith
  have hN1 : 1 ≤ ⌊X⌋₊ := Nat.le_floor (by simpa using hX)
  have hNpos : (0 : ℝ) < (⌊X⌋₊ : ℝ) := by exact_mod_cast hN1
  -- the limit of the infinite series and its identification with `1/ζ(s)`
  have hM : Summable (mobT s) := mobT_summable s hs
  have hid : (∑' k : ℕ, mobT s k) = 1 / (∑' k : ℕ, zetT s k) := mobT_tsum_eq_inv s hs
  -- split off the tail of the infinite series
  have hsplit := Summable.sum_add_tsum_nat_add (f := mobT s) ⌊X⌋₊ hM
  -- the two remaining estimates
  have htail := mobT_tail s hs ⌊X⌋₊ hN1
  have hfloor : X / 2 ≤ (⌊X⌋₊ : ℝ) := by
    by_cases h2 : (2 : ℝ) ≤ X
    · have h1 : X - 1 < (⌊X⌋₊ : ℝ) := by
        have := Nat.lt_floor_add_one X
        linarith
      linarith
    · have hx2 : X < 2 := not_le.mp h2
      have hge : (1 : ℝ) ≤ (⌊X⌋₊ : ℝ) := by exact_mod_cast hN1
      have : X / 2 < 1 := by linarith
      linarith
  have hfinal : (⌊X⌋₊ : ℝ) ^ (1 - s) / (s - 1) ≤ 2 ^ (s - 1) / (s - 1) / X ^ (s - 1) := by
    have hA : (⌊X⌋₊ : ℝ) ^ (1 - s) ≤ (X / 2) ^ (1 - s) :=
      Real.rpow_le_rpow_of_nonpos (by linarith : (0:ℝ) < X / 2) hfloor (by linarith : 1 - s ≤ 0)
    have hB : (X / 2) ^ (1 - s) = X ^ (1 - s) * 2 ^ (s - 1) := by
      rw [Real.div_rpow (le_of_lt hXpos) (by norm_num) (1 - s), div_eq_mul_inv,
        ← Real.rpow_neg (show (0 : ℝ) ≤ 2 by norm_num) (1 - s),
        show -(1 - s) = s - 1 by ring]
    have hC : X ^ (1 - s) = 1 / X ^ (s - 1) := by
      rw [one_div, ← Real.rpow_neg (le_of_lt hXpos) (s - 1), show -(s - 1) = 1 - s by ring]
    have hD : (⌊X⌋₊ : ℝ) ^ (1 - s) / (s - 1) ≤ (X ^ (1 - s) * 2 ^ (s - 1)) / (s - 1) :=
      div_le_div_of_nonneg_right (hB ▸ hA) (le_of_lt hspos)
    refine le_trans hD (le_of_eq ?_)
    rw [hC]; ring
  rw [sum_Icc_eq_sum_range_mobT, ← zetT_tsum_form, ← hid]
  calc |(∑ i ∈ Finset.range ⌊X⌋₊, mobT s i) - ∑' k : ℕ, mobT s k|
      = |∑' j : ℕ, mobT s (j + ⌊X⌋₊)| := by
        have h : (∑ i ∈ Finset.range ⌊X⌋₊, mobT s i) - (∑' k : ℕ, mobT s k)
            = -(∑' j : ℕ, mobT s (j + ⌊X⌋₊)) := by
          rw [← hsplit]; ring
        rw [h, abs_neg]
    _ ≤ (⌊X⌋₊ : ℝ) ^ (1 - s) / (s - 1) := htail
    _ ≤ 2 ^ (s - 1) / (s - 1) / X ^ (s - 1) := hfinal

end Work.HP
