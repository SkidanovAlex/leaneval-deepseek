import Mathlib
import Submission.Work.Diff.STE.Torus
import Submission.Work.Diff.STE.conv_l2_sq_le
import Submission.Work.Diff.STE.tsum_mul_sq_le
import Submission.Work.Diff.STE.norm_conv_le
import Submission.Work.Diff.STE.wt_shift_conv_tsum

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Convolution with a moment-bounded kernel is bounded on the weighted `ℓ²` space `CSq s`

Let `b : (ι → ℤ) → ℂ` be a coefficient family all of whose weighted `ℓ¹`-norms are finite,
`Σ_l ⟨l⟩^{2N} ‖b l‖ < ∞` for every `N`, where `⟨l⟩² = wt l = 1 + Σᵢ lᵢ²`.  Then convolution
with `b` is a bounded operator on the weighted `ℓ²` space
`CSq s c = Σ_k ⟨k⟩^{2s} ‖c k‖²`:

  `∃ C ≥ 0, ∀ c, CSq s (conv b c) ≤ C · CSq s c`.

## Proof

Write `u l = ‖b l‖` and `v m = ‖c m‖`.  The two ingredients are

* the triangle inequality `‖conv b c k‖ ≤ Σ_l u l · v (k - l)` (`norm_conv_le`);
* the weighted Cauchy–Schwarz inequality
  `(Σ_l u l · v (k - l))² ≤ (Σ_l u l) · (Σ_l u l · v (k - l)²)` (`tsum_mul_sq_le`),
  applied with the weight `u`;

so that, after the reindexing `l ↦ k - l` of the second factor,

  `⟨k⟩^{2s} ‖conv b c k‖² ≤ (Σ_l u l) · ⟨k⟩^{2s} · Σ_m ‖b (k - m)‖ ‖c m‖²`.

The second factor of the resulting sum is controlled by the weighted Young inequality
`wt_shift_conv_tsum` (`b` plays the role of the `ℓ¹` family, `c` of the `ℓ²` family), which is
exactly the Peetre/submultiplicativity estimate `⟨k⟩ ≤ 2⟨k - m⟩⟨m⟩` — the place where the
polynomial weight of the slowly decaying kernel `b` is absorbed:

  `Σ_k ⟨k⟩^{2s} Σ_m ‖b (k - m)‖ ‖c m‖² ≤ 2^s (Σ_l ⟨l⟩^{2s} ‖b l‖) · CSq s c`.

Summing the pointwise bound and collecting the constants gives
`C = (Σ_l ‖b l‖) · 2^s · (Σ_l ⟨l⟩^{2s} ‖b l‖)`.
-/

noncomputable section

namespace Work.Diff.STE.B3.SymCalcStep1

open scoped BigOperators

theorem conv_CSq_le
    {ι : Type*} [Fintype ι] [DecidableEq ι] (s : ℕ) (b : (ι → ℤ) → ℂ)
    (hb : ∀ N : ℕ, Summable (fun l : ι → ℤ => (Work.Diff.STE.wt l) ^ N * ‖b l‖)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ c : (ι → ℤ) → ℂ,
      Summable (fun k : ι → ℤ => (Work.Diff.STE.wt k) ^ s * ‖c k‖ ^ 2) →
      Work.Diff.STE.CSq s (Work.Diff.STE.conv b c) ≤ C * Work.Diff.STE.CSq s c := by
  classical
  refine ⟨(∑' l : ι → ℤ, ‖b l‖) * 2 ^ s * (∑' l : ι → ℤ, (Work.Diff.STE.wt l) ^ s * ‖b l‖),
    ?_, ?_⟩
  · refine mul_nonneg (mul_nonneg (tsum_nonneg (fun l => norm_nonneg _)) (by positivity)) ?_
    exact tsum_nonneg (fun l =>
      mul_nonneg (pow_nonneg (le_of_lt (Work.Diff.STE.wt_pos l)) s) (norm_nonneg _))
  · intro c hc
    -- `b ∈ ℓ¹`
    have ha0 : Summable (fun l : ι → ℤ => ‖b l‖) := by simpa using hb 0
    -- `c ∈ ℓ²`
    have hc2 : Summable (fun m : ι → ℤ => ‖c m‖ ^ 2) := by
      refine Summable.of_nonneg_of_le (fun m => sq_nonneg _) (fun m => ?_) hc
      have h1 : (1 : ℝ) ≤ (Work.Diff.STE.wt m) ^ s := by
        calc (1 : ℝ) = 1 ^ s := (one_pow s).symm
          _ ≤ (Work.Diff.STE.wt m) ^ s :=
              pow_le_pow_left₀ (by norm_num) (Work.Diff.STE.wt_one_le m) s
      exact le_mul_of_one_le_left (sq_nonneg _) h1
    -- the weighted Young inequality with the roles `a = b` (ℓ¹) and `f = c` (weighted ℓ²)
    have hG := Work.Diff.STE.wt_shift_conv_tsum b c s (hb s) hc
    -- the pointwise bound, for every frequency `k`
    have hpt : ∀ k : ι → ℤ, (Work.Diff.STE.wt k) ^ s * ‖Work.Diff.STE.conv b c k‖ ^ 2
        ≤ (∑' l : ι → ℤ, ‖b l‖)
          * ((Work.Diff.STE.wt k) ^ s
              * ∑' m : ι → ℤ, ‖b (k - m)‖ * ‖c m‖ ^ 2) := by
      intro k
      have hnorm : ‖Work.Diff.STE.conv b c k‖ ≤ ∑' l : ι → ℤ, ‖b l‖ * ‖c (k - l)‖ :=
        Work.Diff.STE.norm_conv_le b c ha0 hc2 k
      have hbdd : ∀ m : ι → ℤ, ‖c m‖ ^ 2 ≤ ∑' m : ι → ℤ, ‖c m‖ ^ 2 :=
        fun m => hc2.le_tsum m (fun j _ => sq_nonneg _)
      have hQl : Summable (fun l : ι → ℤ => ‖b l‖ * ‖c (k - l)‖ ^ 2) :=
        Summable.of_nonneg_of_le (fun l => mul_nonneg (norm_nonneg _) (sq_nonneg _))
          (fun l => mul_le_mul_of_nonneg_left (hbdd (k - l)) (norm_nonneg _)) (ha0.mul_right _)
      have hCS : (∑' l : ι → ℤ, ‖b l‖ * ‖c (k - l)‖) ^ 2
          ≤ (∑' l : ι → ℤ, ‖b l‖) * (∑' l : ι → ℤ, ‖b l‖ * ‖c (k - l)‖ ^ 2) :=
        Work.Diff.STE.tsum_mul_sq_le (fun l : ι → ℤ => ‖b l‖)
          (fun l : ι → ℤ => ‖c (k - l)‖) (fun l => norm_nonneg _)
          (fun l => norm_nonneg _) ha0 hQl
      -- reindex the second Cauchy–Schwarz factor through the involution `l ↦ k - l`
      have hreindex : (∑' l : ι → ℤ, ‖b l‖ * ‖c (k - l)‖ ^ 2)
          = ∑' m : ι → ℤ, ‖b (k - m)‖ * ‖c m‖ ^ 2 := by
        let e : (ι → ℤ) ≃ (ι → ℤ) :=
          { toFun := fun l => k - l
            invFun := fun l => k - l
            left_inv := fun l => sub_sub_self k l
            right_inv := fun l => sub_sub_self k l }
        have h := Equiv.tsum_eq e (fun l : ι → ℤ => ‖b l‖ * ‖c (k - l)‖ ^ 2)
        simpa [e, sub_sub_self] using h.symm
      calc (Work.Diff.STE.wt k) ^ s * ‖Work.Diff.STE.conv b c k‖ ^ 2
          ≤ (Work.Diff.STE.wt k) ^ s * (∑' l : ι → ℤ, ‖b l‖ * ‖c (k - l)‖) ^ 2 :=
            mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hnorm 2)
              (pow_nonneg (le_of_lt (Work.Diff.STE.wt_pos k)) s)
        _ ≤ (Work.Diff.STE.wt k) ^ s
              * ((∑' l : ι → ℤ, ‖b l‖) * (∑' l : ι → ℤ, ‖b l‖ * ‖c (k - l)‖ ^ 2)) :=
            mul_le_mul_of_nonneg_left hCS (pow_nonneg (le_of_lt (Work.Diff.STE.wt_pos k)) s)
        _ = (∑' l : ι → ℤ, ‖b l‖) * ((Work.Diff.STE.wt k) ^ s
              * ∑' m : ι → ℤ, ‖b (k - m)‖ * ‖c m‖ ^ 2) := by
            rw [hreindex]; ring
    have hsumm : Summable (fun k : ι → ℤ =>
        (Work.Diff.STE.wt k) ^ s * ‖Work.Diff.STE.conv b c k‖ ^ 2) :=
      Summable.of_nonneg_of_le
        (fun k => mul_nonneg (pow_nonneg (le_of_lt (Work.Diff.STE.wt_pos k)) s) (sq_nonneg _))
        hpt (hG.1.mul_left _)
    calc Work.Diff.STE.CSq s (Work.Diff.STE.conv b c)
        = ∑' k : ι → ℤ, (Work.Diff.STE.wt k) ^ s * ‖Work.Diff.STE.conv b c k‖ ^ 2 := rfl
      _ ≤ ∑' k : ι → ℤ, (∑' l : ι → ℤ, ‖b l‖)
            * ((Work.Diff.STE.wt k) ^ s * ∑' m : ι → ℤ, ‖b (k - m)‖ * ‖c m‖ ^ 2) :=
          Summable.tsum_le_tsum hpt hsumm (hG.1.mul_left _)
      _ = (∑' l : ι → ℤ, ‖b l‖)
            * ∑' k : ι → ℤ, (Work.Diff.STE.wt k) ^ s
                * ∑' m : ι → ℤ, ‖b (k - m)‖ * ‖c m‖ ^ 2 :=
          Summable.tsum_mul_left _ hG.1
      _ ≤ (∑' l : ι → ℤ, ‖b l‖)
            * (2 ^ s * (∑' l : ι → ℤ, (Work.Diff.STE.wt l) ^ s * ‖b l‖)
                * ∑' m : ι → ℤ, (Work.Diff.STE.wt m) ^ s * ‖c m‖ ^ 2) :=
          mul_le_mul_of_nonneg_left hG.2 (tsum_nonneg fun l => norm_nonneg _)
      _ = ((∑' l : ι → ℤ, ‖b l‖) * 2 ^ s
            * (∑' l : ι → ℤ, (Work.Diff.STE.wt l) ^ s * ‖b l‖)) * Work.Diff.STE.CSq s c := by
          rw [Work.Diff.STE.CSq]; ring

end Work.Diff.STE.B3.SymCalcStep1
