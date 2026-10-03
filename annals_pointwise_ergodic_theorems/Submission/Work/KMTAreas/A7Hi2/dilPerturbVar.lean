import Mathlib
import Submission.Work.KMTAreas.A7Hi.LowpassDefs
import Submission.Work.Analysis.HardyLittlewood.nbhd_max_defs
import Submission.Work.Analysis.RubioDeFrancia.tsum_inv_one_add_abs_sq_le
import Submission.Work.Analysis.RubioDeFrancia.weight_tsum_le
import Submission.Work.KMTAreas.A7.variationalNorm_le_sqSum
import Submission.Port.Aesm

/-!
# The dilation-perturbation variational estimate

For a Schwartz kernel `K` and a real lacunary family `τ` (`1 ≤ τ n`, `2 * τ n ≤ τ (n+1)`) with
`c n = ⌊τ n⌋`, the family of differences of the `τ n`- and `c n`-dilates of `K`,

`n ↦ (K_{τ n} − K_{c n}) ∗ f`,  `K_t(j) = t⁻¹ K(j/t)`,

has an `r`-variation (`2 < r`) bounded on `ℓᵖ(ℤ)` (`1 < p`) by `C ‖f‖_{ℓᵖ}`, uniformly in `f` and
in the lacunary family.

The two analytic inputs are

* the **pointwise kernel bound** §2: the mean value theorem applied to `t ↦ t⁻¹K(j/t)`, together
  with the Schwartz decay of `K` and of `K' = fderiv K`, gives
  `‖τ⁻¹K(j/τ) − c⁻¹K(j/c)‖ ≤ (2A + 4A') τ⁻² (1 + |j|/τ)⁻²`;
* the **scaled lattice sum** §3: `∑_{j ∈ ℤ} (1 + |j|/τ)⁻² ≤ 3τ` for `τ ≥ 1` (telescoping).

These give, by the radial-kernel/maximal-function comparison (`radial_kernel_tsum_le_maximal`),
a pointwise bound of every member of the family by `O(1/τ n) M_{HL}(‖f‖)`; the variational norm
is bounded by four times the sum of the pointwise norms (§5), the weights sum geometrically
(`τ n ≥ 2^n`), and the interval Hardy–Littlewood maximal function is bounded on `ℓᵖ(ℤ)` (§6).
-/

namespace Work.KMTAreas.A7Hi2

open MeasureTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

/-- `((n.natAbs : ℕ) : ℝ) = |(n : ℝ)|`. -/
private lemma natAbs_cast_real (n : ℤ) : ((n.natAbs : ℕ) : ℝ) = |(n : ℝ)| := by
  rw [Nat.cast_natAbs (α := ℝ), Int.cast_abs]

/-! ## 1. Schwartz decay in the form `C / (1 + |x|)^n` -/

private lemma schwartz_decay_gen {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (K : SchwartzMap ℝ F) (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, ‖K x‖ ≤ C / (1 + |x|) ^ n := by
  obtain ⟨C0, hC0pos, hC0⟩ := K.decay 0 0
  obtain ⟨C1, hC1pos, hC1⟩ := K.decay n 0
  simp only [pow_zero, one_mul, norm_iteratedFDeriv_zero] at hC0 hC1
  refine ⟨2 ^ n * (C0 + C1), by positivity, fun x => ?_⟩
  have hb0 : ‖K x‖ ≤ C0 := hC0 x
  have hb1 : ‖K x‖ * |x| ^ n ≤ C1 := by
    have h := hC1 x
    rw [Real.norm_eq_abs] at h
    linarith [h]
  have hmax : 1 + |x| ≤ 2 * max 1 |x| := by
    rcases max_cases (1 : ℝ) |x| with ⟨he, _⟩ | ⟨he, _⟩
    · rw [he]; linarith [abs_nonneg x]
    · rw [he]; linarith [abs_nonneg x]
  have hmax2 : (max 1 |x|) ^ n ≤ 1 + |x| ^ n := by
    rcases max_cases (1 : ℝ) |x| with ⟨he, _⟩ | ⟨he, _⟩
    · rw [he, one_pow]; linarith [pow_nonneg (abs_nonneg x) n]
    · rw [he]; linarith [pow_nonneg (abs_nonneg x) n]
  have hle : (1 + |x|) ^ n ≤ 2 ^ n * (1 + |x| ^ n) := by
    calc (1 + |x|) ^ n ≤ (2 * max 1 |x|) ^ n := pow_le_pow_left₀ (by positivity) hmax n
      _ = 2 ^ n * (max 1 |x|) ^ n := by rw [mul_pow]
      _ ≤ 2 ^ n * (1 + |x| ^ n) := mul_le_mul_of_nonneg_left hmax2 (by positivity)
  rw [le_div_iff₀ (by positivity : (0 : ℝ) < (1 + |x|) ^ n)]
  calc ‖K x‖ * (1 + |x|) ^ n ≤ ‖K x‖ * (2 ^ n * (1 + |x| ^ n)) :=
        mul_le_mul_of_nonneg_left hle (norm_nonneg _)
    _ = 2 ^ n * (‖K x‖ + ‖K x‖ * |x| ^ n) := by ring
    _ ≤ 2 ^ n * (C0 + C1) :=
        mul_le_mul_of_nonneg_left (add_le_add hb0 hb1) (by positivity)

private lemma schwartz_fderiv_decay (K : SchwartzMap ℝ ℂ) (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, ‖fderiv ℝ (⇑K) x‖ ≤ C / (1 + |x|) ^ n := by
  obtain ⟨C, hCpos, hC⟩ := schwartz_decay_gen (SchwartzMap.fderivCLM ℝ ℝ ℂ K) n
  refine ⟨C, hCpos, fun x => ?_⟩
  have h := hC x
  rwa [SchwartzMap.fderivCLM_apply] at h

/-! ## 2. The pointwise bound on the kernel difference -/

/-- **Pointwise bound on the difference of two dilates of a Schwartz kernel.** -/
private lemma kernel_diff_pointwise {K : SchwartzMap ℝ ℂ} {A A' : ℝ} (hA : 0 < A) (hA' : 0 < A')
    (hdK : ∀ u : ℝ, ‖K u‖ ≤ A / (1 + |u|) ^ 2)
    (hdK' : ∀ u : ℝ, ‖fderiv ℝ (⇑K) u‖ ≤ A' / (1 + |u|) ^ 3)
    {τ c : ℝ} (hτ : 1 ≤ τ) (hc : 1 ≤ c) (hcτ : c ≤ τ) (hτc : τ < c + 1) (j : ℤ) :
    ‖(1 / τ) * K ((j : ℝ) / τ) - (1 / c) * K ((j : ℝ) / c)‖
      ≤ (2 * A + 4 * A') / (τ ^ 2 * (1 + |(j : ℝ)| / τ) ^ 2) := by
  have hτ0 : (0 : ℝ) < τ := lt_of_lt_of_le zero_lt_one hτ
  have hc0 : (0 : ℝ) < c := lt_of_lt_of_le zero_lt_one hc
  have hchalf : τ / 2 < c := by nlinarith
  set u : ℝ := (j : ℝ) / τ with hu
  set v : ℝ := (j : ℝ) / c with hv
  have huj : |u| = |(j : ℝ)| / τ := by rw [hu, abs_div, abs_of_pos hτ0]
  have hKdiff : ‖K u - K v‖ ≤ A' / (1 + |(j : ℝ)| / τ) ^ 3 * |u - v| := by
    have hs : ∀ s ∈ Set.Icc (min u v) (max u v),
        ‖fderiv ℝ (⇑K) s‖ ≤ A' / (1 + |(j : ℝ)| / τ) ^ 3 := by
      intro s hs
      have hsabs : |(j : ℝ)| / τ ≤ |s| := by
        rcases le_total (0 : ℝ) (j : ℝ) with hj | hj
        · have huv : u ≤ v := by
            rw [hu, hv]
            exact div_le_div_of_nonneg_left hj hc0 hcτ
          have hs1 : u ≤ s := by
            have h := hs.1
            rwa [min_eq_left huv] at h
          have hju : |(j : ℝ)| / τ = u := by rw [hu, abs_of_nonneg hj]
          rw [hju]
          exact le_trans hs1 (le_abs_self s)
        · have hvu : v ≤ u := by
            rw [hu, hv, div_le_div_iff₀ hc0 hτ0]
            nlinarith [hj, hcτ]
          have hs2 : s ≤ u := by
            have h := hs.2
            rwa [max_eq_left hvu] at h
          have hju : |(j : ℝ)| / τ = -u := by rw [hu, abs_of_nonpos hj, neg_div]
          rw [hju]
          exact le_trans (neg_le_neg hs2) (neg_le_abs s)
      have hstep : 1 + |(j : ℝ)| / τ ≤ 1 + |s| := by linarith [hsabs]
      have h1 : A' / (1 + |s|) ^ 3 ≤ A' / (1 + |(j : ℝ)| / τ) ^ 3 := by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hstep 3) hA'.le
      exact le_trans (hdK' s) h1
    have hdiff : ∀ s ∈ Set.Icc (min u v) (max u v), DifferentiableAt ℝ (⇑K) s :=
      fun s _ => K.differentiable.differentiableAt
    have hconv : Convex ℝ (Set.Icc (min u v) (max u v)) := convex_Icc _ _
    have hmemu : u ∈ Set.Icc (min u v) (max u v) := ⟨min_le_left _ _, le_max_left _ _⟩
    have hmemv : v ∈ Set.Icc (min u v) (max u v) := ⟨min_le_right _ _, le_max_right _ _⟩
    have hmtv := Convex.norm_image_sub_le_of_norm_fderiv_le hdiff hs hconv hmemu hmemv
    rw [norm_sub_rev]
    refine hmtv.trans (le_of_eq ?_)
    rw [Real.norm_eq_abs, abs_sub_comm]
  have hnum : |c - τ| ≤ 1 := by rw [abs_of_nonpos (by linarith)]; linarith
  have htc : (0 : ℝ) < τ * c := by positivity
  have hterm1 : |1 / τ - 1 / c| ≤ 2 / τ ^ 2 := by
    have heq : 1 / τ - 1 / c = (c - τ) / (τ * c) := by field_simp <;> ring
    rw [heq, abs_div, abs_of_pos htc, div_le_iff₀ htc]
    have hrhs : (2 / τ ^ 2) * (τ * c) = 2 * c / τ := by field_simp <;> ring
    rw [hrhs, le_div_iff₀ hτ0]
    nlinarith [hnum, hchalf, hτ0]
  have hterm2 : |u - v| ≤ 2 * |(j : ℝ)| / τ ^ 2 := by
    have heq : u - v = (j : ℝ) * (c - τ) / (τ * c) := by rw [hu, hv]; field_simp <;> ring
    rw [heq, abs_div, abs_mul, abs_of_pos htc, div_le_iff₀ htc]
    have hrhs : (2 * |(j : ℝ)| / τ ^ 2) * (τ * c) = 2 * |(j : ℝ)| * c / τ := by field_simp <;> ring
    rw [hrhs, le_div_iff₀ hτ0]
    have h6 : |c - τ| * τ ≤ 2 * c := by nlinarith [hnum, hchalf, hτ0]
    calc |(j : ℝ)| * |c - τ| * τ = |(j : ℝ)| * (|c - τ| * τ) := by ring
      _ ≤ |(j : ℝ)| * (2 * c) := mul_le_mul_of_nonneg_left h6 (abs_nonneg _)
      _ = 2 * |(j : ℝ)| * c := by ring
  have hsplit : (1 / τ) * K u - (1 / c) * K v
      = (1 / τ - 1 / c) * K u + (1 / c) * (K u - K v) := by ring
  have hc1 : (0 : ℝ) < 1 / c := by positivity
  have htri : ‖(1 / τ) * K u - (1 / c) * K v‖
      ≤ |1 / τ - 1 / c| * ‖K u‖ + (1 / c) * ‖K u - K v‖ := by
    rw [hsplit]
    have e1 : ‖(1 / τ - 1 / c) * K u‖ = |1 / τ - 1 / c| * ‖K u‖ := by
      rw [norm_mul]
      exact congrArg (· * ‖K u‖) (by
        rw [show (1 / (τ : ℂ) - 1 / (c : ℂ)) = ((1 / τ - 1 / c : ℝ) : ℂ) by push_cast; ring]
        exact RCLike.norm_ofReal _)
    have e2 : ‖(1 / c) * (K u - K v)‖ = |1 / c| * ‖K u - K v‖ := by
      rw [norm_mul]
      exact congrArg (· * ‖K u - K v‖) (by
        rw [show (1 / (c : ℂ)) = ((1 / c : ℝ) : ℂ) by push_cast; ring]
        exact RCLike.norm_ofReal _)
    calc ‖(1 / τ - 1 / c) * K u + (1 / c) * (K u - K v)‖
        ≤ ‖(1 / τ - 1 / c) * K u‖ + ‖(1 / c) * (K u - K v)‖ := norm_add_le _ _
      _ = |1 / τ - 1 / c| * ‖K u‖ + |1 / c| * ‖K u - K v‖ := by rw [e1, e2]
      _ = |1 / τ - 1 / c| * ‖K u‖ + (1 / c) * ‖K u - K v‖ := by
          rw [abs_of_pos hc1]
  have hb1 : |1 / τ - 1 / c| * ‖K u‖ ≤ (2 / τ ^ 2) * (A / (1 + |(j : ℝ)| / τ) ^ 2) := by
    refine mul_le_mul hterm1 ?_ (norm_nonneg _) (by positivity)
    have h := hdK u
    rwa [huj] at h
  have hb2 : (1 / c) * ‖K u - K v‖
      ≤ (1 / c) * ((A' / (1 + |(j : ℝ)| / τ) ^ 3) * (2 * |(j : ℝ)| / τ ^ 2)) :=
    mul_le_mul_of_nonneg_left (hKdiff.trans (mul_le_mul_of_nonneg_left hterm2 (by positivity)))
      (by positivity)
  set W : ℝ := 1 + |(j : ℝ)| / τ with hWdef
  have hWpos : (0 : ℝ) < W := by rw [hWdef]; positivity
  have hfin : (2 / τ ^ 2) * (A / W ^ 2)
      + (1 / c) * ((A' / W ^ 3) * (2 * |(j : ℝ)| / τ ^ 2)) ≤ (2 * A + 4 * A') / (τ ^ 2 * W ^ 2) := by
    have hT1 : (2 / τ ^ 2) * (A / W ^ 2) = 2 * A / (τ ^ 2 * W ^ 2) := by field_simp <;> ring
    have hT2 : (1 / c) * ((A' / W ^ 3) * (2 * |(j : ℝ)| / τ ^ 2)) ≤ 4 * A' / (τ ^ 2 * W ^ 2) := by
      have hL : (1 / c) * ((A' / W ^ 3) * (2 * |(j : ℝ)| / τ ^ 2))
          = 2 * A' * |(j : ℝ)| / (c * W ^ 3 * τ ^ 2) := by field_simp <;> ring
      rw [hL]
      have hw : |(j : ℝ)| / τ ≤ W := by rw [hWdef]; linarith
      have hτ2c : τ ≤ 2 * c := by linarith
      have h7 : |(j : ℝ)| ≤ 2 * c * W := by
        have h8 : |(j : ℝ)| = τ * (|(j : ℝ)| / τ) := by field_simp
        rw [h8]
        exact mul_le_mul hτ2c hw (by positivity) (by positivity)
      have hden : (0 : ℝ) < c * W ^ 3 * τ ^ 2 := by positivity
      have hnum2 : 2 * A' * |(j : ℝ)| ≤ 2 * A' * (2 * c * W) := by nlinarith [h7, hA']
      refine (div_le_div_of_nonneg_right hnum2 hden.le).trans (le_of_eq ?_)
      field_simp <;> ring
    rw [hT1]
    calc 2 * A / (τ ^ 2 * W ^ 2) + (1 / c) * ((A' / W ^ 3) * (2 * |(j : ℝ)| / τ ^ 2))
        ≤ 2 * A / (τ ^ 2 * W ^ 2) + 4 * A' / (τ ^ 2 * W ^ 2) := add_le_add le_rfl hT2
      _ = (2 * A + 4 * A') / (τ ^ 2 * W ^ 2) := by field_simp <;> ring
  calc ‖(1 / τ) * K u - (1 / c) * K v‖
      ≤ |1 / τ - 1 / c| * ‖K u‖ + (1 / c) * ‖K u - K v‖ := htri
    _ ≤ (2 / τ ^ 2) * (A / W ^ 2)
          + (1 / c) * ((A' / W ^ 3) * (2 * |(j : ℝ)| / τ ^ 2)) := add_le_add hb1 hb2
    _ ≤ (2 * A + 4 * A') / (τ ^ 2 * W ^ 2) := hfin

/-! ## 3. The scaled reciprocal-square lattice sum -/

private lemma summable_div_sq_add (τ : ℝ) (hτ : 1 ≤ τ) :
    Summable (fun k : ℕ => 1 / (τ + (k : ℝ)) ^ 2) := by
  have hbase : Summable (fun t : ℤ => 1 / (1 + |(t : ℝ)|) ^ 2) := by
    simpa using (Work.Analysis.RubioDeFrancia.tsum_inv_one_add_abs_sq_le.choose_spec.2 0).1
  have h1 : Summable (fun k : ℕ => 1 / (1 + |((k : ℤ) : ℝ)|) ^ 2) :=
    hbase.comp_injective (fun a b hab => by exact_mod_cast hab)
  have h2 : (fun k : ℕ => 1 / (1 + |((k : ℤ) : ℝ)|) ^ 2)
      = fun k : ℕ => 1 / (1 + (k : ℝ)) ^ 2 := by
    funext k
    rw [Int.cast_natCast, abs_of_nonneg (Nat.cast_nonneg k)]
  rw [h2] at h1
  refine Summable.of_nonneg_of_le (fun k => by positivity) (fun k => ?_) h1
  have hk : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [hτ, hk]

private lemma tsum_div_sq_add_succ_le (τ : ℝ) (hτ : 1 ≤ τ) :
    (∑' k : ℕ, 1 / (τ + ((k + 1 : ℕ) : ℝ)) ^ 2) ≤ 1 / τ := by
  have hτ0 : (0 : ℝ) < τ := lt_of_lt_of_le zero_lt_one hτ
  have hterm : ∀ k : ℕ, 1 / (τ + ((k + 1 : ℕ) : ℝ)) ^ 2
      ≤ 1 / (τ + (k : ℝ)) - 1 / (τ + ((k + 1 : ℕ) : ℝ)) := by
    intro k
    have hcast : ((k + 1 : ℕ) : ℝ) = (k : ℝ) + 1 := by push_cast; ring
    rw [hcast]
    have hA : (0 : ℝ) < τ + (k : ℝ) := by positivity
    have hB : (0 : ℝ) < τ + ((k : ℝ) + 1) := by positivity
    have hsub : 1 / (τ + (k : ℝ)) - 1 / (τ + ((k : ℝ) + 1))
        = 1 / ((τ + (k : ℝ)) * (τ + ((k : ℝ) + 1))) := by field_simp <;> ring
    rw [hsub, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [hA, hB]
  refine Real.tsum_le_of_sum_range_le (fun k => by positivity) (fun K => ?_)
  refine (Finset.sum_le_sum (fun k _ => hterm k)).trans ?_
  have htel : (∑ k ∈ Finset.range K,
      (1 / (τ + (k : ℝ)) - 1 / (τ + ((k + 1 : ℕ) : ℝ)))) ≤ 1 / τ := by
    rw [Finset.sum_range_sub' (fun k : ℕ => 1 / (τ + (k : ℝ))) K]
    simp only [Nat.cast_zero, add_zero]
    have hK : 0 ≤ 1 / (τ + (K : ℝ)) := by positivity
    linarith
  exact htel

private lemma sumInvSqScaled_aux (τ : ℝ) (hτ : 1 ≤ τ) :
    Summable (fun t : ℤ => 1 / (1 + |(t : ℝ)| / τ) ^ 2) ∧
      (∑' t : ℤ, ENNReal.ofReal (1 / (1 + |(t : ℝ)| / τ) ^ 2)) ≤ ENNReal.ofReal (3 * τ) := by
  have hτ0 : (0 : ℝ) < τ := lt_of_lt_of_le zero_lt_one hτ
  set g : ℕ → ℝ := fun k => 1 / (τ + (k : ℝ)) ^ 2 with hg
  have hgs : Summable g := (summable_div_sq_add τ hτ).congr (fun k => by simp only [hg])
  have hG : Summable (fun t : ℤ => g t.natAbs) := by
    have hbase : Summable (fun t : ℤ => 1 / (1 + |(t : ℝ)|) ^ 2) := by
      simpa using (Work.Analysis.RubioDeFrancia.tsum_inv_one_add_abs_sq_le.choose_spec.2 0).1
    refine Summable.of_nonneg_of_le (fun t => by simp only [hg]; positivity) (fun t => ?_) hbase
    simp only [hg]
    rw [natAbs_cast_real t]
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [hτ, abs_nonneg (t : ℝ)]
  have hsum_int : (∑' t : ℤ, g t.natAbs) ≤ 1 / τ ^ 2 + 2 / τ := by
    rw [Work.Analysis.RubioDeFrancia.sum_int_natAbs_even g hgs]
    have hg0 : g 0 = 1 / τ ^ 2 := by simp only [hg, Nat.cast_zero, add_zero]
    rw [hg0]
    have htail : (∑' k : ℕ, g (k + 1)) ≤ 1 / τ := by
      have h2 : (∑' k : ℕ, g (k + 1)) = ∑' k : ℕ, 1 / (τ + ((k + 1 : ℕ) : ℝ)) ^ 2 :=
        tsum_congr (fun k => by simp only [hg])
      rw [h2]
      exact tsum_div_sq_add_succ_le τ hτ
    calc (1 / τ ^ 2 + 2 * ∑' k : ℕ, g (k + 1)) ≤ 1 / τ ^ 2 + 2 * (1 / τ) :=
          add_le_add le_rfl (mul_le_mul_of_nonneg_left htail (by norm_num))
      _ = 1 / τ ^ 2 + 2 / τ := by ring_nf
  have hF : Summable (fun t : ℤ => 1 / (1 + |(t : ℝ)| / τ) ^ 2) := by
    refine (hG.mul_left (τ ^ 2)).congr (fun t => ?_)
    simp only [hg]
    rw [natAbs_cast_real t]
    have h : 1 + |(t : ℝ)| / τ = (τ + |(t : ℝ)|) / τ := by field_simp <;> ring
    rw [h]
    field_simp <;> ring
  have hFeq : (∑' t : ℤ, 1 / (1 + |(t : ℝ)| / τ) ^ 2) = τ ^ 2 * (∑' t : ℤ, g t.natAbs) := by
    rw [← tsum_mul_left]
    refine tsum_congr (fun t => ?_)
    simp only [hg]
    rw [natAbs_cast_real t]
    have h : 1 + |(t : ℝ)| / τ = (τ + |(t : ℝ)|) / τ := by field_simp <;> ring
    rw [h]
    field_simp <;> ring
  have hbound : (∑' t : ℤ, 1 / (1 + |(t : ℝ)| / τ) ^ 2) ≤ 3 * τ := by
    rw [hFeq]
    have hmul := mul_le_mul_of_nonneg_left hsum_int (by positivity : (0 : ℝ) ≤ τ ^ 2)
    calc τ ^ 2 * (∑' t : ℤ, g t.natAbs) ≤ τ ^ 2 * (1 / τ ^ 2 + 2 / τ) := hmul
      _ = 1 + 2 * τ := by field_simp <;> ring
      _ ≤ 3 * τ := by linarith
  refine ⟨hF, ?_⟩
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun t => by positivity) hF]
  exact ENNReal.ofReal_le_ofReal hbound

/-! ## 4. The kernel mass and the maximal bound -/

private lemma kernel_mass_le {C₀ τ : ℝ} (hC₀ : 0 < C₀) (hτ : 1 ≤ τ) :
    (∑' j : ℤ, ENNReal.ofReal (C₀ / (τ ^ 2 * (1 + |(j : ℝ)| / τ) ^ 2)))
      ≤ ENNReal.ofReal (3 * C₀ / τ) := by
  have h1 : ∀ j : ℤ, ENNReal.ofReal (C₀ / (τ ^ 2 * (1 + |(j : ℝ)| / τ) ^ 2))
      ≤ ENNReal.ofReal (C₀ / τ ^ 2) * ENNReal.ofReal (1 / (1 + |(j : ℝ)| / τ) ^ 2) := by
    intro j
    rw [← ENNReal.ofReal_mul (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    have heq : C₀ / (τ ^ 2 * (1 + |(j : ℝ)| / τ) ^ 2)
        = (C₀ / τ ^ 2) * (1 / (1 + |(j : ℝ)| / τ) ^ 2) := by field_simp <;> ring
    exact le_of_eq heq
  calc (∑' j : ℤ, ENNReal.ofReal (C₀ / (τ ^ 2 * (1 + |(j : ℝ)| / τ) ^ 2)))
      ≤ ∑' j : ℤ, ENNReal.ofReal (C₀ / τ ^ 2)
          * ENNReal.ofReal (1 / (1 + |(j : ℝ)| / τ) ^ 2) := ENNReal.tsum_le_tsum h1
    _ = ENNReal.ofReal (C₀ / τ ^ 2)
          * ∑' j : ℤ, ENNReal.ofReal (1 / (1 + |(j : ℝ)| / τ) ^ 2) := ENNReal.tsum_mul_left
    _ ≤ ENNReal.ofReal (C₀ / τ ^ 2) * ENNReal.ofReal (3 * τ) :=
        mul_le_mul_of_nonneg_left (sumInvSqScaled_aux τ hτ).2 bot_le
    _ = ENNReal.ofReal (3 * C₀ / τ) := by
        rw [← ENNReal.ofReal_mul (by positivity)]
        congr 1
        field_simp <;> ring

/-- **The kernel difference convolved against a weight is dominated by the maximal function.** -/
private lemma kernel_conv_max_le {K : SchwartzMap ℝ ℂ} {A A' : ℝ} (hA : 0 < A) (hA' : 0 < A')
    (hdK : ∀ u : ℝ, ‖K u‖ ≤ A / (1 + |u|) ^ 2)
    (hdK' : ∀ u : ℝ, ‖fderiv ℝ (⇑K) u‖ ≤ A' / (1 + |u|) ^ 3)
    {τ c : ℝ} (hτ : 1 ≤ τ) (hc : 1 ≤ c) (hcτ : c ≤ τ) (hτc : τ < c + 1)
    (f : ℤ → ℂ) (x : ℤ) :
    (∑' j : ℤ, ‖(1 / τ) * K ((j : ℝ) / τ) - (1 / c) * K ((j : ℝ) / c)‖ₑ * ‖f (x - j)‖ₑ)
      ≤ ENNReal.ofReal (3 * (2 * A + 4 * A') / τ) *
          Work.Analysis.HardyLittlewood.dMaxENN (fun y => ‖f y‖ₑ) x := by
  set C₀ : ℝ := 2 * A + 4 * A' with hC₀def
  have hC₀ : 0 < C₀ := by rw [hC₀def]; positivity
  have hτ0 : (0 : ℝ) < τ := lt_of_lt_of_le zero_lt_one hτ
  have hbasic : ∀ j : ℤ, ‖(1 / τ) * K ((j : ℝ) / τ) - (1 / c) * K ((j : ℝ) / c)‖
      ≤ C₀ / (τ ^ 2 * (1 + |(j : ℝ)| / τ) ^ 2) := by
    intro j
    rw [hC₀def]
    exact kernel_diff_pointwise hA hA' hdK hdK' hτ hc hcτ hτc j
  set w : ℕ → ℝ≥0∞ := fun k => ENNReal.ofReal (C₀ / (τ ^ 2 * (1 + (k : ℝ) / τ) ^ 2)) with hw
  have hwanti : Antitone w := by
    intro a b hab
    simp only [hw]
    refine ENNReal.ofReal_le_ofReal ?_
    have hab' : (a : ℝ) ≤ (b : ℝ) := by exact_mod_cast hab
    have ha0 : (0 : ℝ) ≤ (a : ℝ) := Nat.cast_nonneg a
    have h1 : (a : ℝ) / τ ≤ (b : ℝ) / τ := div_le_div_of_nonneg_right hab' hτ0.le
    have h2 : (0 : ℝ) < 1 + (a : ℝ) / τ := by positivity
    have h3 : (0 : ℝ) < 1 + (b : ℝ) / τ := by positivity
    have h4 : (1 + (a : ℝ) / τ) ^ 2 ≤ (1 + (b : ℝ) / τ) ^ 2 :=
      pow_le_pow_left₀ h2.le (by linarith) 2
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h4 (sq_nonneg τ)) hC₀.le
  have hle : ∀ j : ℤ, ‖(1 / τ) * K ((j : ℝ) / τ) - (1 / c) * K ((j : ℝ) / c)‖ₑ ≤ w j.natAbs := by
    intro j
    simp only [hw, ← ofReal_norm]
    refine ENNReal.ofReal_le_ofReal ?_
    have h := hbasic j
    rw [← natAbs_cast_real j] at h
    exact h
  have hmass : (∑' t : ℤ, w t.natAbs) ≤ ENNReal.ofReal (3 * C₀ / τ) := by
    have h1 : (∑' t : ℤ, w t.natAbs)
        = ∑' t : ℤ, ENNReal.ofReal (C₀ / (τ ^ 2 * (1 + |(t : ℝ)| / τ) ^ 2)) := by
      refine tsum_congr (fun t => ?_)
      simp only [hw]
      rw [natAbs_cast_real t]
    rw [h1]
    exact kernel_mass_le hC₀ hτ
  calc (∑' j : ℤ, ‖(1 / τ) * K ((j : ℝ) / τ) - (1 / c) * K ((j : ℝ) / c)‖ₑ * ‖f (x - j)‖ₑ)
      ≤ ∑' j : ℤ, w j.natAbs * ‖f (x - j)‖ₑ :=
        ENNReal.tsum_le_tsum (fun j => mul_le_mul_of_nonneg_right (hle j) bot_le)
    _ ≤ (∑' t : ℤ, w t.natAbs) * Work.Analysis.HardyLittlewood.dMaxENN (fun y => ‖f y‖ₑ) x :=
        Commons.Analysis.Hilbert.radial_kernel_tsum_le_maximal w hwanti f x
    _ ≤ ENNReal.ofReal (3 * C₀ / τ) * Work.Analysis.HardyLittlewood.dMaxENN (fun y => ‖f y‖ₑ) x :=
        mul_le_mul_of_nonneg_right hmass bot_le
    _ = ENNReal.ofReal (3 * (2 * A + 4 * A') / τ) *
          Work.Analysis.HardyLittlewood.dMaxENN (fun y => ‖f y‖ₑ) x := by rw [hC₀def]

/-! ## 5. The variational norm is bounded by the sum of the pointwise norms -/

private lemma variationalNorm_le_tsum_enorm {r : NNReal} (hr : 1 ≤ r) (u : ℕ → ℂ) :
    PointwiseErgodicTheorems.variationalNorm r u ≤ 4 * ∑' n : ℕ, ‖u n‖ₑ := by
  have hb : ∀ n : ℕ, ∃ K : ℕ, ∀ k ≥ K, (fun k n => if n = k then u k else 0) k n = 0 := by
    intro n
    refine ⟨n + 1, fun k hk => ?_⟩
    show (if n = k then u k else 0) = 0
    rw [if_neg (fun h => by omega)]
  have hdecomp : u = fun n => ∑' k : ℕ, (if n = k then u k else 0) := by
    funext n
    rw [tsum_eq_single n (fun k hk => if_neg (Ne.symm hk))]
    simp
  calc PointwiseErgodicTheorems.variationalNorm r u
      = PointwiseErgodicTheorems.variationalNorm r
          (fun n => ∑' k : ℕ, (if n = k then u k else 0)) :=
        congrArg (PointwiseErgodicTheorems.variationalNorm r) hdecomp
    _ ≤ ∑' k : ℕ, PointwiseErgodicTheorems.variationalNorm r
          (fun n => if n = k then u k else 0) :=
        Submission.PointwiseErgodicTheorems.variationalNorm_tsum_le hr hb
    _ ≤ ∑' k : ℕ, 4 * ‖u k‖ₑ := ENNReal.tsum_le_tsum
        (fun k => Submission.PointwiseErgodicTheorems.variationalNorm_spike_le hr k (u k))
    _ = 4 * ∑' k : ℕ, ‖u k‖ₑ := ENNReal.tsum_mul_left

/-! ## 6. The interval maximal function on `ℓᵖ` -/

private lemma dMaxENN_eLpNorm_le (p : ℝ) (hp : 1 < p) :
    ∃ C : ℝ, 0 < C ∧ ∀ ψ : ℤ → ENNReal,
      MeasureTheory.eLpNorm (Work.Analysis.HardyLittlewood.dMaxENN ψ) (ENNReal.ofReal p)
          MeasureTheory.Measure.count
        ≤ ENNReal.ofReal C * MeasureTheory.eLpNorm ψ (ENNReal.ofReal p)
            MeasureTheory.Measure.count := by
  obtain ⟨C, hCpos, hC⟩ := Work.Analysis.HardyLittlewood.dMaxENN_lintegral_rpow_le hp
  refine ⟨C, hCpos, fun ψ => ?_⟩
  have hp0 : 0 < p := lt_trans zero_lt_one hp
  have hpne : ENNReal.ofReal p ≠ 0 := ENNReal.ofReal_ne_zero_iff.mpr hp0
  have hptop : ENNReal.ofReal p ≠ ⊤ := ENNReal.ofReal_ne_top
  have h1p : (0 : ℝ) < 1 / p := by positivity
  have hD : MeasureTheory.eLpNorm (Work.Analysis.HardyLittlewood.dMaxENN ψ) (ENNReal.ofReal p)
        MeasureTheory.Measure.count
      = (∫⁻ x : ℤ, Work.Analysis.HardyLittlewood.dMaxENN ψ x ^ p ∂MeasureTheory.Measure.count)
          ^ (1 / p) := by
    rw [MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm_toReal (hf := by pw_aesm) (μ := MeasureTheory.Measure.count)
      (f := Work.Analysis.HardyLittlewood.dMaxENN ψ) hpne hptop]
    simp only [enorm_eq_self, ENNReal.toReal_ofReal hp0.le]
  have hP : MeasureTheory.eLpNorm ψ (ENNReal.ofReal p) MeasureTheory.Measure.count
      = (∫⁻ x : ℤ, ψ x ^ p ∂MeasureTheory.Measure.count) ^ (1 / p) := by
    rw [MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm_toReal (hf := by pw_aesm) (μ := MeasureTheory.Measure.count)
      (f := ψ) hpne hptop]
    simp only [enorm_eq_self, ENNReal.toReal_ofReal hp0.le]
  by_cases hfin : ∀ k : ℤ, ψ k ≠ ⊤
  · rw [hD, hP]
    have h2 := hC ψ hfin
    calc (∫⁻ x : ℤ, Work.Analysis.HardyLittlewood.dMaxENN ψ x ^ p
            ∂MeasureTheory.Measure.count) ^ (1 / p)
        ≤ (ENNReal.ofReal (C ^ p) * ∫⁻ x : ℤ, ψ x ^ p
            ∂MeasureTheory.Measure.count) ^ (1 / p) := ENNReal.rpow_le_rpow h2 (by positivity)
      _ = (ENNReal.ofReal (C ^ p)) ^ (1 / p)
            * (∫⁻ x : ℤ, ψ x ^ p ∂MeasureTheory.Measure.count) ^ (1 / p) :=
          ENNReal.mul_rpow_of_nonneg _ _ (by positivity)
      _ = ENNReal.ofReal C * (∫⁻ x : ℤ, ψ x ^ p ∂MeasureTheory.Measure.count) ^ (1 / p) := by
          have hCpow : (ENNReal.ofReal (C ^ p)) ^ (1 / p) = ENNReal.ofReal C := by
            rw [ENNReal.ofReal_rpow_of_nonneg (by positivity : (0 : ℝ) ≤ C ^ p) h1p.le]
            congr 1
            rw [← Real.rpow_mul hCpos.le, mul_one_div, div_self hp0.ne', Real.rpow_one]
          rw [hCpow]
  · push_neg at hfin
    obtain ⟨k, hk⟩ := hfin
    have hint_top : (∫⁻ x : ℤ, ψ x ^ p ∂MeasureTheory.Measure.count) = ⊤ := by
      rw [eq_top_iff]
      calc ⊤ = ψ k ^ p := by rw [hk]; exact (ENNReal.top_rpow_of_pos hp0).symm
        _ ≤ ∫⁻ x : ℤ, ψ x ^ p ∂MeasureTheory.Measure.count := by
            rw [MeasureTheory.lintegral_count]
            exact ENNReal.le_tsum (f := fun a : ℤ => ψ a ^ p) k
    have hpsi_top : MeasureTheory.eLpNorm ψ (ENNReal.ofReal p) MeasureTheory.Measure.count = ⊤ := by
      rw [hP, hint_top, ENNReal.top_rpow_of_pos h1p]
    rw [hpsi_top, ENNReal.mul_top (ENNReal.ofReal_ne_zero_iff.mpr hCpos)]
    exact le_top

/-! ## 7. The pointwise variational bound and the main theorem -/

private lemma variational_bound {K : SchwartzMap ℝ ℂ} {A A' : ℝ} (hA : 0 < A) (hA' : 0 < A')
    (hdK : ∀ u : ℝ, ‖K u‖ ≤ A / (1 + |u|) ^ 2)
    (hdK' : ∀ u : ℝ, ‖fderiv ℝ (⇑K) u‖ ≤ A' / (1 + |u|) ^ 3)
    (r : NNReal) (hr : 1 ≤ r)
    (τ : ℕ → ℝ) (hτ1 : ∀ n, 1 ≤ τ n) (hτ2 : ∀ n, 2 * τ n ≤ τ (n + 1))
    (c : ℕ → ℕ) (hc1 : ∀ n, 1 ≤ c n)
    (hcτ : ∀ n, ((c n : ℕ) : ℝ) ≤ τ n ∧ τ n < ((c n : ℕ) : ℝ) + 1)
    (f : ℤ → ℂ) (x : ℤ) :
    PointwiseErgodicTheorems.variationalNorm r
        (fun n : ℕ => ∑' j : ℤ, ((1 / τ n) * K ((j : ℝ) / τ n)
          - (1 / ((c n : ℕ) : ℝ)) * K ((j : ℝ) / ((c n : ℕ) : ℝ))) * f (x - j))
      ≤ ENNReal.ofReal (24 * (2 * A + 4 * A')) *
          Work.Analysis.HardyLittlewood.dMaxENN (fun y => ‖f y‖ₑ) x := by
  set C₀ : ℝ := 2 * A + 4 * A' with hC₀def
  have hC₀ : 0 < C₀ := by rw [hC₀def]; positivity
  set G : ℝ≥0∞ := Work.Analysis.HardyLittlewood.dMaxENN (fun y => ‖f y‖ₑ) x with hG
  have hpt : ∀ n : ℕ,
      ‖∑' j : ℤ, ((1 / τ n) * K ((j : ℝ) / τ n)
        - (1 / ((c n : ℕ) : ℝ)) * K ((j : ℝ) / ((c n : ℕ) : ℝ))) * f (x - j)‖ₑ
        ≤ ENNReal.ofReal (3 * C₀ / τ n) * G := by
    intro n
    refine (enorm_tsum_le_tsum_enorm).trans ?_
    simp only [enorm_mul]
    have h := kernel_conv_max_le hA hA' hdK hdK' (hτ1 n) (by exact_mod_cast hc1 n)
      (hcτ n).1 (hcτ n).2 f x
    rw [hG, hC₀def]
    exact h
  have hτge : ∀ n : ℕ, (2 : ℝ) ^ n ≤ τ n := by
    intro n
    induction n with
    | zero => simpa using hτ1 0
    | succ n ih =>
      have h2 := hτ2 n
      calc (2 : ℝ) ^ (n + 1) = 2 * 2 ^ n := by rw [pow_succ]; ring
        _ ≤ 2 * τ n := by linarith
        _ ≤ τ (n + 1) := h2
  have hsum : (∑' n : ℕ, ENNReal.ofReal (3 * C₀ / τ n)) ≤ ENNReal.ofReal (6 * C₀) := by
    have h1 : ∀ n : ℕ, ENNReal.ofReal (3 * C₀ / τ n)
        ≤ ENNReal.ofReal (3 * C₀) * ENNReal.ofReal ((1 / 2 : ℝ) ^ n) := by
      intro n
      have h2n : (1 : ℝ) ≤ ((1 / 2 : ℝ) ^ n) * τ n := by
        have hpos : (0 : ℝ) < (2 : ℝ) ^ n := by positivity
        have h3 : ((1 / 2 : ℝ) ^ n) * τ n = τ n / 2 ^ n := by rw [div_pow, one_pow, one_div]; ring
        rw [h3, le_div_iff₀ hpos]
        simpa using hτge n
      have hleR : 3 * C₀ / τ n ≤ 3 * C₀ * (1 / 2 : ℝ) ^ n := by
        rw [div_le_iff₀ (by linarith [hτ1 n] : (0 : ℝ) < τ n)]
        nlinarith [h2n, hC₀]
      calc ENNReal.ofReal (3 * C₀ / τ n)
          ≤ ENNReal.ofReal (3 * C₀ * (1 / 2 : ℝ) ^ n) := ENNReal.ofReal_le_ofReal hleR
        _ = ENNReal.ofReal (3 * C₀) * ENNReal.ofReal ((1 / 2 : ℝ) ^ n) := by
            rw [ENNReal.ofReal_mul (by positivity)]
    have hgeom : (∑' n : ℕ, ENNReal.ofReal ((1 / 2 : ℝ) ^ n)) = ENNReal.ofReal 2 := by
      rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => by positivity)
        (summable_geometric_of_norm_lt_one (by norm_num : ‖(1 / 2 : ℝ)‖ < 1))]
      congr 1
      rw [(hasSum_geometric_of_norm_lt_one (by norm_num : ‖(1 / 2 : ℝ)‖ < 1)).tsum_eq]
      norm_num
    calc (∑' n : ℕ, ENNReal.ofReal (3 * C₀ / τ n))
        ≤ ∑' n : ℕ, ENNReal.ofReal (3 * C₀) * ENNReal.ofReal ((1 / 2 : ℝ) ^ n) :=
          ENNReal.tsum_le_tsum h1
      _ = ENNReal.ofReal (3 * C₀) * ∑' n : ℕ, ENNReal.ofReal ((1 / 2 : ℝ) ^ n) :=
          ENNReal.tsum_mul_left
      _ = ENNReal.ofReal (3 * C₀) * ENNReal.ofReal 2 := by rw [hgeom]
      _ = ENNReal.ofReal (6 * C₀) := by
          rw [← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 3 * C₀)]
          congr 1
          ring
  have hspike := variationalNorm_le_tsum_enorm (r := r) hr
      (fun n : ℕ => ∑' j : ℤ, ((1 / τ n) * K ((j : ℝ) / τ n)
        - (1 / ((c n : ℕ) : ℝ)) * K ((j : ℝ) / ((c n : ℕ) : ℝ))) * f (x - j))
  refine hspike.trans ?_
  have hkey : (4 : ℝ≥0∞) * ENNReal.ofReal (6 * C₀) = ENNReal.ofReal (24 * (2 * A + 4 * A')) := by
    rw [hC₀def]
    rw [show (4 : ℝ≥0∞) = ENNReal.ofReal 4 from by norm_num,
      ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4)]
    congr 1
    ring
  have hstep : 4 * (∑' n : ℕ, ENNReal.ofReal (3 * C₀ / τ n)) ≤ 4 * ENNReal.ofReal (6 * C₀) :=
    mul_le_mul_of_nonneg_left hsum (by norm_num)
  have hsum2 : 4 * (∑' n : ℕ, ENNReal.ofReal (3 * C₀ / τ n)) * G
      ≤ 4 * ENNReal.ofReal (6 * C₀) * G :=
    mul_le_mul_of_nonneg_right hstep bot_le
  calc 4 * ∑' n : ℕ, ‖∑' j : ℤ, ((1 / τ n) * K ((j : ℝ) / τ n)
        - (1 / ((c n : ℕ) : ℝ)) * K ((j : ℝ) / ((c n : ℕ) : ℝ))) * f (x - j)‖ₑ
      ≤ 4 * ∑' n : ℕ, ENNReal.ofReal (3 * C₀ / τ n) * G :=
        mul_le_mul_of_nonneg_left (ENNReal.tsum_le_tsum hpt) (by norm_num)
    _ = 4 * (∑' n : ℕ, ENNReal.ofReal (3 * C₀ / τ n)) * G := by
        rw [ENNReal.tsum_mul_right]
        ring
    _ ≤ 4 * ENNReal.ofReal (6 * C₀) * G := hsum2
    _ = ENNReal.ofReal (24 * (2 * A + 4 * A')) *
          Work.Analysis.HardyLittlewood.dMaxENN (fun y => ‖f y‖ₑ) x := by
        rw [hkey, hG]

theorem dilPerturbVar (p : ℝ) (hp : 1 < p) (r : NNReal) (hr : 2 < r) (K : SchwartzMap ℝ ℂ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (τ : ℕ → ℝ) (c : ℕ → ℕ) (hτ1 : ∀ n, 1 ≤ τ n)
      (hc1 : ∀ n, 1 ≤ c n) (hcτ : ∀ n, ((c n : ℕ) : ℝ) ≤ τ n ∧ τ n < ((c n : ℕ) : ℝ) + 1)
      (hτ2 : ∀ n, 2 * τ n ≤ τ (n + 1)) (f : ℤ → ℂ),
      MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
          (fun n : ℕ => ∑' j : ℤ, ((1 / τ n) * K ((j : ℝ) / τ n)
            - (1 / ((c n : ℕ) : ℝ)) * K ((j : ℝ) / ((c n : ℕ) : ℝ))) * f (x - j)))
        (ENNReal.ofReal p) MeasureTheory.Measure.count
        ≤ ENNReal.ofReal C * MeasureTheory.eLpNorm f (ENNReal.ofReal p)
            MeasureTheory.Measure.count := by
  obtain ⟨A, hApos, hdK⟩ := schwartz_decay_gen K 2
  obtain ⟨A', hA'pos, hdK'⟩ := schwartz_fderiv_decay K 3
  obtain ⟨Cp, hCppos, hCp⟩ := dMaxENN_eLpNorm_le p hp
  have hr1 : (1 : NNReal) ≤ r := le_trans (by norm_num : (1 : NNReal) ≤ 2) hr.le
  refine ⟨24 * (2 * A + 4 * A') * Cp, by positivity, ?_⟩
  intro τ c hτ1 hc1 hcτ hτ2 f
  have hmono : MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
        (fun n : ℕ => ∑' j : ℤ, ((1 / τ n) * K ((j : ℝ) / τ n)
          - (1 / ((c n : ℕ) : ℝ)) * K ((j : ℝ) / ((c n : ℕ) : ℝ))) * f (x - j)))
        (ENNReal.ofReal p) MeasureTheory.Measure.count
      ≤ MeasureTheory.eLpNorm (fun x : ℤ => ENNReal.ofReal (24 * (2 * A + 4 * A')) *
          Work.Analysis.HardyLittlewood.dMaxENN (fun y => ‖f y‖ₑ) x)
        (ENNReal.ofReal p) MeasureTheory.Measure.count :=
    eLpNorm_mono_enorm (hf := by pw_aesm) (fun x => by
      simpa only [enorm_eq_self] using
        variational_bound hApos hA'pos hdK hdK' r hr1 τ hτ1 hτ2 c hc1 hcτ f x)
  refine hmono.trans ?_
  rw [Commons.Analysis.Convolution.eLpNorm_const_mul_ennreal_of_pos
    (measurable_of_countable (Work.Analysis.HardyLittlewood.dMaxENN (fun y : ℤ => ‖f y‖ₑ))).aemeasurable
    (ENNReal.ofReal (24 * (2 * A + 4 * A'))) (by positivity : (0 : ℝ) < p)]
  have hmax := hCp (fun y : ℤ => ‖f y‖ₑ)
  rw [MeasureTheory.eLpNorm_enorm (hf := by pw_aesm)] at hmax
  calc ENNReal.ofReal (24 * (2 * A + 4 * A')) *
        MeasureTheory.eLpNorm (Work.Analysis.HardyLittlewood.dMaxENN (fun y => ‖f y‖ₑ))
          (ENNReal.ofReal p) MeasureTheory.Measure.count
      ≤ ENNReal.ofReal (24 * (2 * A + 4 * A')) *
        (ENNReal.ofReal Cp * MeasureTheory.eLpNorm f (ENNReal.ofReal p)
          MeasureTheory.Measure.count) := mul_le_mul_of_nonneg_left hmax bot_le
    _ = ENNReal.ofReal (24 * (2 * A + 4 * A') * Cp) *
        MeasureTheory.eLpNorm f (ENNReal.ofReal p) MeasureTheory.Measure.count := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]

end

end Work.KMTAreas.A7Hi2
