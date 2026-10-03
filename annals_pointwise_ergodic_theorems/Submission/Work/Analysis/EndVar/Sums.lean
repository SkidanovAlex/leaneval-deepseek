import Submission.Work.Analysis.EndVar.Defs

/-!
# Summability of the §5 error weights along a lacunary sequence

Section 5 of Krause--Mirek--Tao needs the error terms `(Log N)^{-10}` produced by the single-scale
minor arc estimate `improv` to be summable over a lacunary set of scales `D`.  This module
provides that summability: the weights `⟨Log N⟩^{-c}` (`c > 1`) have uniformly bounded partial
sums along a `Λ`-lacunary sequence, with a bound depending only on `Λ` and `c`.

The analytic content is the colleague's `Work.Analysis.SingleScale.lacunary_logb_rpow_summable`
(the `p`-series summability `∑ n^{-c} < ∞` for `c > 1`, transferred to a lacunary sequence through
`a n ≳ Λ^n`).
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace Work.Analysis.EndVar

noncomputable section

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal PNat BigOperators
open PointwiseErgodicTheorems

/-- The §5 error weight `⟨Log N⟩^{-c} = (max 1 (log₂ N))^{-c}` attached to a scale `N`, as a
nonnegative real. -/
def heightWeight (c : ℝ) (N : ℝ≥0) : ℝ≥0 :=
  ⟨(max 1 (Real.logb 2 (N : ℝ))) ^ (-c), Real.rpow_nonneg (le_trans zero_le_one (le_max_left (1 : ℝ) _)) _⟩

lemma coe_heightWeight (c : ℝ) (N : ℝ≥0) :
    ((heightWeight c N : ℝ≥0) : ℝ) = (max 1 (Real.logb 2 (N : ℝ))) ^ (-c) := rfl

/-- **Summability of the §5 error weights.**  For `c > 1`, the partial sums of `⟨Log (a n)⟩^{-c}`
along a `Λ`-lacunary sequence `a` with `a n ≥ 1` are bounded uniformly in the number of terms. -/
theorem sum_heightWeight_le (Λ : ℝ≥0) (hΛ : 1 < Λ) (c : ℝ) (hc : 1 < c) :
    ∃ C : ℝ≥0, ∀ (a : ℕ → ℝ≥0) (K : ℕ), Lacunary Λ a → (∀ n, 1 ≤ a n) →
      ∑ n ∈ Finset.range K, heightWeight c (a n) ≤ C := by
  obtain ⟨C', hC'pos, hC'⟩ := Work.Analysis.SingleScale.lacunary_logb_rpow_summable Λ hΛ c hc
  refine ⟨NNReal.mk C' hC'pos.le, fun a K ha ha1 => ?_⟩
  have hrec : ∀ n, Λ * a n ≤ a (n + 1) := by
    intro n
    have hpos : (0 : ℝ≥0) < a n := lt_of_lt_of_le zero_lt_one (ha1 n)
    exact le_of_lt ((lt_div_iff₀ hpos).mp (ha n))
  have h := hC' a K hrec (ha1 0)
  rw [← NNReal.coe_le_coe]
  calc ((∑ n ∈ Finset.range K, heightWeight c (a n) : ℝ≥0) : ℝ)
      = ∑ n ∈ Finset.range K, ((heightWeight c (a n) : ℝ≥0) : ℝ) := by push_cast; rfl
    _ = ∑ n ∈ Finset.range K, (max 1 (Real.logb 2 (a n : ℝ))) ^ (-c) := by
        exact Finset.sum_congr rfl (fun n _ => coe_heightWeight c (a n))
    _ ≤ C' := h

/-- The same summability with the partial sums taken over `{0, …, K}` (the finite index set of
`VarEstHalfFin`). -/
theorem sum_heightWeight_le_range_succ (Λ : ℝ≥0) (hΛ : 1 < Λ) (c : ℝ) (hc : 1 < c) :
    ∃ C : ℝ≥0, ∀ (a : ℕ → ℝ≥0) (K : ℕ), Lacunary Λ a → (∀ n, 1 ≤ a n) →
      ∑ n ∈ Finset.range (K + 1), heightWeight c (a n) ≤ C := by
  obtain ⟨C, hC⟩ := sum_heightWeight_le Λ hΛ c hc
  exact ⟨C, fun a K ha ha1 => hC a (K + 1) ha ha1⟩

/-- The error weight `⟨Log N⟩^{-c}` is antitone in `N` for `c > 0`. -/
lemma heightWeight_antitone (c : ℝ) (hc : 0 < c) : Antitone (heightWeight c) := by
  intro M N hMN
  rw [← NNReal.coe_le_coe, coe_heightWeight, coe_heightWeight]
  have h2 : (1 : ℝ) < 2 := by norm_num
  have hlog : max 1 (Real.logb 2 (M : ℝ)) ≤ max 1 (Real.logb 2 (N : ℝ)) := by
    rcases eq_or_lt_of_le (NNReal.coe_nonneg M) with hM | hM
    · have hz : Real.logb 2 (M : ℝ) = 0 := by
        rw [← hM]; simp [Real.logb]
      rw [hz]
      simp
    · exact max_le_max le_rfl (Real.logb_le_logb_of_le h2 hM hMN)
  exact (Real.rpow_le_rpow_iff_of_neg
    (lt_of_lt_of_le zero_lt_one (le_max_left (1 : ℝ) _))
    (lt_of_lt_of_le zero_lt_one (le_max_left (1 : ℝ) _))
    (by linarith : -c < 0)).mpr hlog

/-- A `Λ`-lacunary sequence with `a n ≥ 1` grows at least like `Λ ^ n`. -/
lemma pow_le_of_lacunary {Λ : ℝ≥0} (hΛ : 1 < Λ) {a : ℕ → ℝ≥0} (ha : Lacunary Λ a)
    (ha1 : ∀ n, 1 ≤ a n) (n : ℕ) : Λ ^ n ≤ a n := by
  induction n with
  | zero => simpa using ha1 0
  | succ n ih =>
      have hpos : (0 : ℝ≥0) < a n := lt_of_lt_of_le zero_lt_one (ha1 n)
      have hstep : Λ * a n ≤ a (n + 1) := le_of_lt ((lt_div_iff₀ hpos).mp (ha n))
      calc Λ ^ (n + 1) = Λ * Λ ^ n := pow_succ' Λ n
        _ ≤ Λ * a n := mul_le_mul_of_nonneg_left ih bot_le
        _ ≤ a (n + 1) := hstep

/-- The uniform bound on the partial sums of the §5 error weights, packaged as a function of `Λ`
(so that it can be used to build the `C` of `MajorArcApproximation`). -/
noncomputable def weightSumBound (Λ : ℝ≥0) : ℝ≥0 :=
  if h : 1 < Λ then Classical.choose (sum_heightWeight_le Λ h 10 (by norm_num)) else 0

/-- The defining property of `weightSumBound`. -/
lemma sum_heightWeight_le_weightSumBound {Λ : ℝ≥0} (hΛ : 1 < Λ) {a : ℕ → ℝ≥0}
    (ha : Lacunary Λ a) (ha1 : ∀ n, 1 ≤ a n) (K : ℕ) :
    ∑ n ∈ Finset.range K, heightWeight 10 (a n) ≤ weightSumBound Λ := by
  rw [weightSumBound, dif_pos hΛ]
  exact Classical.choose_spec (sum_heightWeight_le Λ hΛ 10 (by norm_num)) a K ha ha1

/-- The partial sums of the weights `⟨log₂ (Λ^n)⟩^{-10}` are bounded, for every `Λ > 1`. -/
theorem exists_sum_heightWeight_pow_le (Λ : ℝ≥0) (hΛ : 1 < Λ) :
    ∃ Cs : ℝ≥0, ∀ K : ℕ, ∑ n ∈ Finset.range K, heightWeight 10 (Λ ^ n) ≤ Cs := by
  have h2 : (0 : ℝ≥0) < 2 := by norm_num
  have hΛ' : 1 < (1 + Λ) / 2 := by
    rw [lt_div_iff₀ h2]; linarith
  have hlt : (1 + Λ) / 2 < Λ := by
    rw [div_lt_iff₀ h2]; linarith
  have hLac : Lacunary ((1 + Λ) / 2) (fun n => Λ ^ n) := by
    intro n
    have hne : (Λ : ℝ≥0) ^ n ≠ 0 := pow_ne_zero n (ne_of_gt (lt_trans zero_lt_one hΛ))
    show (1 + Λ) / 2 < Λ ^ (n + 1) / Λ ^ n
    rw [pow_succ', mul_div_cancel_right₀ _ hne]
    exact hlt
  have h1n : ∀ n, 1 ≤ (fun n => Λ ^ n) n := fun n => one_le_pow₀ hΛ.le
  obtain ⟨Cs, hCs⟩ := sum_heightWeight_le ((1 + Λ) / 2) hΛ' 10 (by norm_num)
  exact ⟨Cs, fun K => hCs (fun n => Λ ^ n) K hLac h1n⟩

/-- The uniform bound on the partial sums of the weights `⟨log₂ (Λ^n)⟩^{-10}`, as a function of
`Λ` (so that it can be used to build the `C` of `MajorArcApproximation`). -/
noncomputable def powWeightBound (Λ : ℝ≥0) : ℝ≥0 :=
  if h : 1 < Λ then Classical.choose (exists_sum_heightWeight_pow_le Λ h) else 0

/-- The defining property of `powWeightBound`. -/
lemma sum_heightWeight_pow_le {Λ : ℝ≥0} (hΛ : 1 < Λ) (K : ℕ) :
    ∑ n ∈ Finset.range K, heightWeight 10 (Λ ^ n) ≤ powWeightBound Λ := by
  rw [powWeightBound, dif_pos hΛ]
  exact Classical.choose_spec (exists_sum_heightWeight_pow_le Λ hΛ) K

/-- The summability of the specific weights `(Log N)^{-10}` used in §5 of the paper. -/
theorem sum_heightWeight_ten_le (Λ : ℝ≥0) (hΛ : 1 < Λ) :
    ∃ C : ℝ≥0, ∀ (a : ℕ → ℝ≥0) (K : ℕ), Lacunary Λ a → (∀ n, 1 ≤ a n) →
      ∑ n ∈ Finset.range (K + 1), heightWeight 10 (a n) ≤ C :=
  sum_heightWeight_le_range_succ Λ hΛ 10 (by norm_num)

end

end Work.Analysis.EndVar
