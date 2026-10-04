import Mathlib
import Submission.Work.Diff.STE.Torus
import Submission.Work.Diff.STE.B3.SymCalcStep1.friedrichs_pointwise_nosupp
import Submission.Work.Diff.STE.wt_pow_le
import Submission.Work.Diff.STE.wt_shift_conv_tsum

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The flat multiplier commutator at the Friedrichs cutoff scale, without `ρ 0 = 1`

This is `Work.Diff.STE.B3.SymCalcStep8.flat_multiplier_commutator_no_one`: for a Friedrichs
profile `ρ` that is only assumed to be bounded by `1`, to vanish outside the ball of radius
`√2` (`2 < Σ yᵢ² → ρ y = 0`) and to be Lipschitz with constant `L` — in particular **without**
any normalisation at the origin such as `ρ 0 = 1` — the commutator `[M_a, S_ε]` of the
convolution with a rapidly decaying family `a` and the cutoff `S_ε = trunc ρ ε` gains one
derivative on the weighted `ℓ²` scale, **uniformly in `ε ∈ (0,1]`**:

`CSq (s+1) [M_a, S_ε] c ≤ C · CSq s c`.

The proof is the one of `Work.Diff.STE.B3.SymCalcStep1.flat_multiplier_commutator`: Cauchy–Schwarz
at each frequency, the pointwise weighted estimate `wt (k-l) * (ρ (ε(k-l)) - ρ (ε k))² ≤ 64 (1+L²) wt l`
for the multiplier difference (this is `friedrichs_pointwise_nosupp`, which only needs the support
and Lipschitz hypotheses), and the weighted Young inequality `wt_shift_conv_tsum`.  The origin
normalisation `ρ 0 = 1` is used nowhere, so it is simply dropped here.
-/

namespace Work.Diff.STE.B3.SymCalcStep8

/-! ## Summability helpers -/
/-! ## Summability helpers -/

private lemma wt_neg {ι : Type*} [Fintype ι] (l : ι → ℤ) :
    Work.Diff.STE.wt (-l) = Work.Diff.STE.wt l := by
  unfold Work.Diff.STE.wt
  congr 1
  exact Finset.sum_congr rfl fun i _ => by
    simp only [Pi.neg_apply, Int.cast_neg, neg_sq]

/-- The two-sided form of the slowly varying inequality for `wt`. -/
private lemma wt_sub_le {ι : Type*} [Fintype ι] (k l : ι → ℤ) :
    Work.Diff.STE.wt (k - l) ≤ 2 * (Work.Diff.STE.wt k * Work.Diff.STE.wt l) := by
  have h := wt_le_two_mul (k - l) k
  have hkk : (k - l) - k = -l := by abel
  rw [hkk, wt_neg] at h
  linarith

/-- Cauchy–Schwarz for `tsum` in the form `(Σ F G)² ≤ (Σ F²)(Σ G²)`. -/
private lemma tsum_mul_sq_le' {α : Type*} (F G : α → ℝ) (hF : ∀ l, 0 ≤ F l)
    (hG : ∀ l, 0 ≤ G l) (hFs : Summable (fun l => F l ^ 2))
    (hGs : Summable (fun l => G l ^ 2)) :
    (∑' l, F l * G l) ^ 2 ≤ (∑' l, F l ^ 2) * (∑' l, G l ^ 2) := by
  have hFG : Summable (fun l => F l * G l) := by
    refine Summable.of_nonneg_of_le (fun l => mul_nonneg (hF l) (hG l)) (fun l => ?_)
      (hFs.add hGs)
    nlinarith [hF l, hG l, sq_nonneg (F l - G l)]
  have key : ∀ t : Finset α, (∑ l ∈ t, F l * G l) ^ 2
      ≤ (∑' l, F l ^ 2) * (∑' l, G l ^ 2) := by
    intro t
    have h1 : (∑ l ∈ t, F l * G l) ^ 2
        ≤ (∑ l ∈ t, F l ^ 2) * (∑ l ∈ t, G l ^ 2) :=
      Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul t (fun l _ => sq_nonneg (F l))
        (fun l _ => sq_nonneg (G l)) (fun l _ => le_of_eq (by ring))
    calc (∑ l ∈ t, F l * G l) ^ 2
        ≤ (∑ l ∈ t, F l ^ 2) * (∑ l ∈ t, G l ^ 2) := h1
      _ ≤ (∑' l, F l ^ 2) * (∑' l, G l ^ 2) := by
          refine mul_le_mul (Summable.sum_le_tsum t (fun l _ => sq_nonneg _) hFs)
            (Summable.sum_le_tsum t (fun l _ => sq_nonneg _) hGs)
            (Finset.sum_nonneg (fun l _ => sq_nonneg _)) (tsum_nonneg fun l => sq_nonneg _)
  have hlim : Filter.Tendsto (fun t : Finset α => (∑ l ∈ t, F l * G l) ^ 2) Filter.atTop
      (nhds ((∑' l, F l * G l) ^ 2)) := by
    have hh := hFG.hasSum
    simp only [HasSum, SummationFilter.unconditional_filter] at hh
    exact hh.pow 2
  exact le_of_tendsto' hlim key

/-- Summability is invariant under the reflection `l ↦ k - l`. -/
private lemma summable_sub_le {α : Type*} [AddCommGroup α] {f : α → ℝ} (k : α)
    (hf : Summable f) : Summable (fun l => f (k - l)) := by
  refine hf.comp_injective (i := fun l : α => k - l) ?_
  intro a b hab
  have h0 : k - a = k - b := hab
  have h1 : -(k - a) = -(k - b) := by rw [h0]
  rw [neg_sub, neg_sub, sub_eq_add_neg, sub_eq_add_neg] at h1
  exact add_right_cancel h1

/-- If `u` has all weighted `ℓ¹` norms finite and `v ∈ ℓ²`, then
`l ↦ ‖u l‖ * ⟨k-l⟩ * ‖v (k-l)‖` is summable. -/
private lemma summable_norm_wt_mul {ι : Type*} [Fintype ι] [DecidableEq ι]
    (u v : (ι → ℤ) → ℂ)
    (hu : ∀ N : ℕ, Summable (fun l : ι → ℤ => (Work.Diff.STE.wt l) ^ N * ‖u l‖))
    (hv : Summable (fun m : ι → ℤ => ‖v m‖ ^ 2)) (k : ι → ℤ) :
    Summable (fun l : ι → ℤ => ‖u l‖ * Work.Diff.STE.wt (k - l) * ‖v (k - l)‖) := by
  have hu0 : Summable (fun l : ι → ℤ => ‖u l‖) := by
    refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun l => ?_) (hu 0)
    simp
  have hB : ∀ l, ‖u l‖ ≤ ∑' m, ‖u m‖ := fun l => hu0.le_tsum l (fun j _ => norm_nonneg _)
  have hBnn : (0 : ℝ) ≤ ∑' m, ‖u m‖ := tsum_nonneg fun _ => norm_nonneg _
  have hX : Summable (fun l => ‖u l‖ ^ 2 * Work.Diff.STE.wt (k - l) ^ 2) := by
    refine Summable.of_nonneg_of_le (fun l => mul_nonneg (sq_nonneg _) (sq_nonneg _))
      (fun l => ?_) ((hu 2).mul_right (4 * Work.Diff.STE.wt k ^ 2 * (∑' m, ‖u m‖)))
    have h1 := wt_sub_le k l
    have h2 : Work.Diff.STE.wt (k - l) ^ 2
        ≤ (2 * (Work.Diff.STE.wt k * Work.Diff.STE.wt l)) ^ 2 :=
      pow_le_pow_left₀ (le_of_lt (Work.Diff.STE.wt_pos _)) h1 2
    have h3 : ‖u l‖ ^ 2 ≤ (∑' m, ‖u m‖) * ‖u l‖ := by
      rw [sq]
      exact mul_le_mul_of_nonneg_right (hB l) (norm_nonneg _)
    calc ‖u l‖ ^ 2 * Work.Diff.STE.wt (k - l) ^ 2
        ≤ ‖u l‖ ^ 2 * (2 * (Work.Diff.STE.wt k * Work.Diff.STE.wt l)) ^ 2 :=
          mul_le_mul_of_nonneg_left h2 (sq_nonneg _)
      _ = 4 * Work.Diff.STE.wt k ^ 2 * Work.Diff.STE.wt l ^ 2 * ‖u l‖ ^ 2 := by ring
      _ ≤ 4 * Work.Diff.STE.wt k ^ 2 * Work.Diff.STE.wt l ^ 2
            * ((∑' m, ‖u m‖) * ‖u l‖) :=
          mul_le_mul_of_nonneg_left h3
            (mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _)) (sq_nonneg _))
      _ = (Work.Diff.STE.wt l ^ 2 * ‖u l‖) * (4 * Work.Diff.STE.wt k ^ 2 * (∑' m, ‖u m‖)) :=
          by ring
  have hY : Summable (fun l => ‖v (k - l)‖ ^ 2) := summable_sub_le k hv
  refine Summable.of_nonneg_of_le
    (fun l => mul_nonneg (mul_nonneg (norm_nonneg _) (le_of_lt (Work.Diff.STE.wt_pos _)))
      (norm_nonneg _)) (fun l => ?_) (hX.add hY)
  nlinarith [sq_nonneg (‖u l‖ * Work.Diff.STE.wt (k - l) - ‖v (k - l)‖), norm_nonneg (u l),
    norm_nonneg (v (k - l)), le_of_lt (Work.Diff.STE.wt_pos (k - l))]

/-- The basic commutation identity for a Fourier multiplier `φ` (applied to the
`l`-variable) with the convolution operator `conv a`: writing the multiplier as a
coefficient family, the commutator applied to a family `ψ` produces the family with
the multiplier difference `φ (k-l) - φ k`. -/
private lemma tsum_diff_mul {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a φ ψ : (ι → ℤ) → ℂ) (k : ι → ℤ)
    (h1 : Summable (fun l => a l * (φ (k - l) * ψ (k - l))))
    (h2 : Summable (fun l => a l * ψ (k - l))) :
    (∑' l, a l * (φ (k - l) * ψ (k - l))) - φ k * (∑' l, a l * ψ (k - l))
      = ∑' l, a l * ((φ (k - l) - φ k) * ψ (k - l)) := by
  rw [← tsum_mul_left]
  rw [← Summable.tsum_sub h1 (h2.mul_left (φ k))]
  exact tsum_congr fun l => by ring

private lemma norm_mul_mul (a X b : ℂ) : ‖a * (X * b)‖ = ‖a‖ * (‖X‖ * ‖b‖) := by
  rw [norm_mul, norm_mul]

/-- Summability of `l ↦ u l * (φ (k-l) * v (k-l))` for a bounded multiplier `φ`. -/
private lemma summable_mul_bdd {ι : Type*} [Fintype ι] [DecidableEq ι] (C : ℝ) (hC : 0 ≤ C)
    (φ : (ι → ℤ) → ℂ) (hφ : ∀ m, ‖φ m‖ ≤ C) (u v : (ι → ℤ) → ℂ)
    (hmaj : ∀ k : ι → ℤ,
      Summable (fun l : ι → ℤ => ‖u l‖ * Work.Diff.STE.wt (k - l) * ‖v (k - l)‖))
    (k : ι → ℤ) :
    Summable (fun l : ι → ℤ => u l * (φ (k - l) * v (k - l))) := by
  refine Summable.of_norm_bounded ((hmaj k).mul_left C) (fun l => ?_)
  calc ‖u l * (φ (k - l) * v (k - l))‖ = ‖u l‖ * (‖φ (k - l)‖ * ‖v (k - l)‖) :=
        norm_mul_mul _ _ _
    _ ≤ ‖u l‖ * (C * ‖v (k - l)‖) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right (hφ _) (norm_nonneg _)) (norm_nonneg _)
    _ = C * (‖u l‖ * ‖v (k - l)‖) := by ring
    _ ≤ C * (‖u l‖ * Work.Diff.STE.wt (k - l) * ‖v (k - l)‖) := by
        refine mul_le_mul_of_nonneg_left ?_ hC
        calc ‖u l‖ * ‖v (k - l)‖ = (‖u l‖ * 1) * ‖v (k - l)‖ := by ring
          _ ≤ (‖u l‖ * Work.Diff.STE.wt (k - l)) * ‖v (k - l)‖ :=
              mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_left (wt_one_le _) (norm_nonneg _)) (norm_nonneg _)
          _ = ‖u l‖ * Work.Diff.STE.wt (k - l) * ‖v (k - l)‖ := by ring

/-- The commutation identity underlying the Friedrichs commutator estimate. -/
private lemma comm_eq_tsum {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ρ : (ι → ℝ) → ℝ) (hρb : ∀ y : ι → ℝ, ‖ρ y‖ ≤ 1) (ε : ℝ) (u v : (ι → ℤ) → ℂ)
    (hmaj : ∀ k : ι → ℤ,
      Summable (fun l : ι → ℤ => ‖u l‖ * Work.Diff.STE.wt (k - l) * ‖v (k - l)‖))
    (k : ι → ℤ) :
    Work.Diff.STE.conv u (Work.Diff.STE.trunc ρ ε v) k
        - Work.Diff.STE.trunc ρ ε (Work.Diff.STE.conv u v) k
      = ∑' l, u l * ((((ρ (ε • (fun j => ((k - l) j : ℝ))))
            - ρ (ε • (fun j => (k j : ℝ)))) : ℂ) * v (k - l)) := by
  have hφ : ∀ m : ι → ℤ, ‖((ρ (ε • (fun j => (m j : ℝ))) : ℝ) : ℂ)‖ ≤ 2 := by
    intro m
    rw [Complex.norm_real, Real.norm_eq_abs]
    have h := hρb (ε • (fun j => (m j : ℝ)))
    rw [Real.norm_eq_abs] at h
    linarith
  have h1 : Summable (fun l => u l * ((((ρ (ε • (fun j => ((k - l) j : ℝ))) : ℝ)) : ℂ) * v (k - l))) :=
    summable_mul_bdd 2 (by norm_num) _ hφ u v hmaj k
  have h2 : Summable (fun l => u l * v (k - l)) := by
    refine Summable.of_norm_bounded (hmaj k) (fun l => ?_)
    calc ‖u l * v (k - l)‖ = ‖u l‖ * ‖v (k - l)‖ := norm_mul _ _
      _ ≤ ‖u l‖ * Work.Diff.STE.wt (k - l) * ‖v (k - l)‖ := by
          calc ‖u l‖ * ‖v (k - l)‖ = (‖u l‖ * 1) * ‖v (k - l)‖ := by ring
            _ ≤ (‖u l‖ * Work.Diff.STE.wt (k - l)) * ‖v (k - l)‖ :=
                mul_le_mul_of_nonneg_right
                  (mul_le_mul_of_nonneg_left (wt_one_le _) (norm_nonneg _)) (norm_nonneg _)
            _ = ‖u l‖ * Work.Diff.STE.wt (k - l) * ‖v (k - l)‖ := by ring
  have hdiff := tsum_diff_mul u (fun m => (((ρ (ε • (fun j => (m j : ℝ))) : ℝ)) : ℂ)) v k h1 h2
  simpa [Work.Diff.STE.conv, Work.Diff.STE.trunc, Complex.ofReal_sub] using hdiff

theorem flat_multiplier_commutator_no_one {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ρ : (ι → ℝ) → ℝ)
    (hρb : ∀ y : ι → ℝ, ‖ρ y‖ ≤ 1)
    (hdiam : ∀ y : ι → ℝ, 2 < ∑ i, (y i) ^ 2 → ρ y = 0)
    (L : ℝ) (hL : 0 ≤ L) (hρlip : ∀ y z : ι → ℝ, ‖ρ y - ρ z‖ ≤ L * ‖y - z‖)
    (a : (ι → ℤ) → ℂ)
    (ha : ∀ N : ℕ, Summable (fun k : ι → ℤ => (Work.Diff.STE.wt k) ^ N * ‖a k‖))
    (s : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (ε : ℝ), 0 < ε → ε ≤ 1 → ∀ c : (ι → ℤ) → ℂ,
        Summable (fun k : ι → ℤ => (Work.Diff.STE.wt k) ^ s * ‖c k‖ ^ 2) →
        Work.Diff.STE.CSq (s + 1)
            (fun k => Work.Diff.STE.conv a (Work.Diff.STE.trunc ρ ε c) k
              - Work.Diff.STE.trunc ρ ε (Work.Diff.STE.conv a c) k)
          ≤ C * Work.Diff.STE.CSq s c := by
  classical
  set K : ℝ := 64 * (1 + L ^ 2) with hK
  set A2 : ℝ := ∑' l : ι → ℤ, (Work.Diff.STE.wt l) ^ (2 * s + 2) * ‖a l‖ with hA2
  set As : ℝ := ∑' l : ι → ℤ, (Work.Diff.STE.wt l) ^ s * ‖a l‖ with hAs
  have hKnn : 0 ≤ K := by rw [hK]; positivity
  have hA2nn : 0 ≤ A2 :=
    tsum_nonneg fun l => mul_nonneg (pow_nonneg (le_of_lt (wt_pos l)) _) (norm_nonneg _)
  have hAsnn : 0 ≤ As :=
    tsum_nonneg fun l => mul_nonneg (pow_nonneg (le_of_lt (wt_pos l)) _) (norm_nonneg _)
  refine ⟨2 ^ (3 * s + 1) * K * A2 * As, by positivity, ?_⟩
  intro ε hε hε1 c hc
  have ha0 : Summable (fun l : ι → ℤ => ‖a l‖) := by simpa using ha 0
  have hc2 : Summable (fun m : ι → ℤ => ‖c m‖ ^ 2) := by
    refine Summable.of_nonneg_of_le (fun m => sq_nonneg _) (fun m => ?_) hc
    have h1 : (1 : ℝ) ≤ Work.Diff.STE.wt m ^ s := by
      calc (1 : ℝ) = 1 ^ s := (one_pow s).symm
        _ ≤ Work.Diff.STE.wt m ^ s := pow_le_pow_left₀ (by norm_num) (wt_one_le m) s
    exact le_mul_of_one_le_left (sq_nonneg _) h1
  have hA2sum : Summable (fun l : ι → ℤ => (Work.Diff.STE.wt l) ^ (2 * s + 2) * ‖a l‖) :=
    ha (2 * s + 2)
  have hAssum : Summable (fun l : ι → ℤ => (Work.Diff.STE.wt l) ^ s * ‖a l‖) := ha s
  have hmaj : ∀ k : ι → ℤ,
      Summable (fun l : ι → ℤ => ‖a l‖ * Work.Diff.STE.wt (k - l) * ‖c (k - l)‖) :=
    fun k => summable_norm_wt_mul a c ha hc2 k
  -- the explicit form of the commutator
  have hQeq : ∀ k : ι → ℤ,
      Work.Diff.STE.conv a (Work.Diff.STE.trunc ρ ε c) k
          - Work.Diff.STE.trunc ρ ε (Work.Diff.STE.conv a c) k
        = ∑' l, a l * ((((ρ (ε • (fun j => ((k - l) j : ℝ))))
              - ρ (ε • (fun j => (k j : ℝ)))) : ℂ) * c (k - l)) :=
    fun k => comm_eq_tsum ρ hρb ε a c hmaj k
  -- the norm bound
  have hnorm : ∀ k : ι → ℤ,
      ‖Work.Diff.STE.conv a (Work.Diff.STE.trunc ρ ε c) k
          - Work.Diff.STE.trunc ρ ε (Work.Diff.STE.conv a c) k‖
        ≤ ∑' l, ‖a l‖
            * |ρ (ε • (fun j => ((k - l) j : ℝ))) - ρ (ε • (fun j => (k j : ℝ)))| * ‖c (k - l)‖ := by
    intro k
    rw [hQeq k]
    have hsum : Summable (fun l : ι → ℤ =>
        ‖a l * ((((ρ (ε • (fun j => ((k - l) j : ℝ))))
              - ρ (ε • (fun j => (k j : ℝ)))) : ℂ) * c (k - l))‖) := by
      refine Summable.of_nonneg_of_le (fun l => norm_nonneg _) (fun l => ?_)
        ((hmaj k).mul_left 2)
      rw [norm_mul_mul, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
      have hδb : |ρ (ε • (fun j => ((k - l) j : ℝ))) - ρ (ε • (fun j => (k j : ℝ)))| ≤ 2 := by
        have h1 : |ρ (ε • (fun j => ((k - l) j : ℝ)))| ≤ 1 := by
          have h := hρb (ε • (fun j => ((k - l) j : ℝ)))
          rwa [Real.norm_eq_abs] at h
        have h2 : |ρ (ε • (fun j => (k j : ℝ)))| ≤ 1 := by
          have h := hρb (ε • (fun j => (k j : ℝ)))
          rwa [Real.norm_eq_abs] at h
        have hx := abs_le.mp h1
        have hy := abs_le.mp h2
        exact abs_le.mpr ⟨by linarith [hx.1, hy.2], by linarith [hx.2, hy.1]⟩
      calc ‖a l‖ * (|ρ (ε • (fun j => ((k - l) j : ℝ))) - ρ (ε • (fun j => (k j : ℝ)))| * ‖c (k - l)‖)
          ≤ ‖a l‖ * (2 * ‖c (k - l)‖) :=
            mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_right hδb (norm_nonneg _)) (norm_nonneg _)
        _ = 2 * (‖a l‖ * ‖c (k - l)‖) := by ring
        _ ≤ 2 * (‖a l‖ * Work.Diff.STE.wt (k - l) * ‖c (k - l)‖) := by
            refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
            calc ‖a l‖ * ‖c (k - l)‖ = (‖a l‖ * 1) * ‖c (k - l)‖ := by ring
              _ ≤ (‖a l‖ * Work.Diff.STE.wt (k - l)) * ‖c (k - l)‖ :=
                  mul_le_mul_of_nonneg_right
                    (mul_le_mul_of_nonneg_left (wt_one_le _) (norm_nonneg _)) (norm_nonneg _)
              _ = ‖a l‖ * Work.Diff.STE.wt (k - l) * ‖c (k - l)‖ := by ring
    calc ‖∑' l, a l * ((((ρ (ε • (fun j => ((k - l) j : ℝ))))
            - ρ (ε • (fun j => (k j : ℝ)))) : ℂ) * c (k - l))‖
        ≤ ∑' l, ‖a l * ((((ρ (ε • (fun j => ((k - l) j : ℝ))))
            - ρ (ε • (fun j => (k j : ℝ)))) : ℂ) * c (k - l))‖ :=
          norm_tsum_le_tsum_norm hsum
      _ = ∑' l, ‖a l‖
            * |ρ (ε • (fun j => ((k - l) j : ℝ))) - ρ (ε • (fun j => (k j : ℝ)))| * ‖c (k - l)‖ :=
          tsum_congr fun l => by
            rw [norm_mul_mul, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
            ring
  -- summability of the two Cauchy–Schwarz factors
  have hPsi : ∀ k : ι → ℤ,
      Summable (fun l : ι → ℤ =>
        ‖a l‖ * |ρ (ε • (fun j => ((k - l) j : ℝ))) - ρ (ε • (fun j => (k j : ℝ)))| ^ 2) := by
    intro k
    refine Summable.of_nonneg_of_le (fun l => mul_nonneg (norm_nonneg _) (sq_nonneg _))
      (fun l => ?_) (ha0.mul_left 4)
    have hb : |ρ (ε • (fun j => ((k - l) j : ℝ))) - ρ (ε • (fun j => (k j : ℝ)))| ^ 2 ≤ 4 := by
      have h1 : |ρ (ε • (fun j => ((k - l) j : ℝ)))| ≤ 1 := by
        have h := hρb (ε • (fun j => ((k - l) j : ℝ)))
        rwa [Real.norm_eq_abs] at h
      have h2 : |ρ (ε • (fun j => (k j : ℝ)))| ≤ 1 := by
        have h := hρb (ε • (fun j => (k j : ℝ)))
        rwa [Real.norm_eq_abs] at h
      have hx := abs_le.mp h1
      have hy := abs_le.mp h2
      have hxy : |ρ (ε • (fun j => ((k - l) j : ℝ))) - ρ (ε • (fun j => (k j : ℝ)))| ≤ 2 :=
        abs_le.mpr ⟨by linarith [hx.1, hy.2], by linarith [hx.2, hy.1]⟩
      nlinarith [hxy, abs_nonneg (ρ (ε • (fun j => ((k - l) j : ℝ))) - ρ (ε • (fun j => (k j : ℝ))))]
    calc ‖a l‖ * |ρ (ε • (fun j => ((k - l) j : ℝ))) - ρ (ε • (fun j => (k j : ℝ)))| ^ 2
        ≤ ‖a l‖ * 4 := mul_le_mul_of_nonneg_left hb (norm_nonneg (a l))
      _ = 4 * ‖a l‖ := by ring
  have hGamma : ∀ k : ι → ℤ,
      Summable (fun l : ι → ℤ => ‖a l‖ * ‖c (k - l)‖ ^ 2) := by
    intro k
    have hb : ∀ m : ι → ℤ, ‖c m‖ ^ 2 ≤ ∑' m : ι → ℤ, ‖c m‖ ^ 2 :=
      fun m => hc2.le_tsum m (fun j _ => sq_nonneg _)
    refine Summable.of_nonneg_of_le (fun l => mul_nonneg (norm_nonneg _) (sq_nonneg _))
      (fun l => mul_le_mul_of_nonneg_left (hb (k - l)) (norm_nonneg _)) (ha0.mul_right _)
  -- Cauchy–Schwarz at each frequency
  have hCS : ∀ k : ι → ℤ,
      (∑' l, ‖a l‖
          * |ρ (ε • (fun j => ((k - l) j : ℝ))) - ρ (ε • (fun j => (k j : ℝ)))| * ‖c (k - l)‖) ^ 2
        ≤ (∑' l, ‖a l‖
              * |ρ (ε • (fun j => ((k - l) j : ℝ))) - ρ (ε • (fun j => (k j : ℝ)))| ^ 2)
          * (∑' l, ‖a l‖ * ‖c (k - l)‖ ^ 2) := by
    intro k
    have hFnn : ∀ l : ι → ℤ, 0 ≤ Real.sqrt (‖a l‖)
        * |ρ (ε • (fun j => ((k - l) j : ℝ))) - ρ (ε • (fun j => (k j : ℝ)))| :=
      fun l => mul_nonneg (Real.sqrt_nonneg _) (abs_nonneg _)
    have hGnn : ∀ l : ι → ℤ, 0 ≤ Real.sqrt (‖a l‖) * ‖c (k - l)‖ :=
      fun l => mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)
    have hF2 : Summable (fun l : ι → ℤ => (Real.sqrt (‖a l‖)
        * |ρ (ε • (fun j => ((k - l) j : ℝ))) - ρ (ε • (fun j => (k j : ℝ)))|) ^ 2) := by
      refine (hPsi k).congr fun l => ?_
      rw [mul_pow, Real.sq_sqrt (norm_nonneg _)]
    have hG2 : Summable (fun l : ι → ℤ => (Real.sqrt (‖a l‖) * ‖c (k - l)‖) ^ 2) := by
      refine (hGamma k).congr fun l => ?_
      rw [mul_pow, Real.sq_sqrt (norm_nonneg _)]
    have hmain := tsum_mul_sq_le' (fun l : ι → ℤ => Real.sqrt (‖a l‖)
        * |ρ (ε • (fun j => ((k - l) j : ℝ))) - ρ (ε • (fun j => (k j : ℝ)))|)
      (fun l : ι → ℤ => Real.sqrt (‖a l‖) * ‖c (k - l)‖) hFnn hGnn hF2 hG2
    calc (∑' l, ‖a l‖
            * |ρ (ε • (fun j => ((k - l) j : ℝ))) - ρ (ε • (fun j => (k j : ℝ)))| * ‖c (k - l)‖) ^ 2
        = (∑' l, (Real.sqrt (‖a l‖)
              * |ρ (ε • (fun j => ((k - l) j : ℝ))) - ρ (ε • (fun j => (k j : ℝ)))|)
            * (Real.sqrt (‖a l‖) * ‖c (k - l)‖)) ^ 2 := by
          congr 1
          refine tsum_congr fun l => ?_
          rw [show (Real.sqrt (‖a l‖)
                * |ρ (ε • (fun j => ((k - l) j : ℝ))) - ρ (ε • (fun j => (k j : ℝ)))|)
              * (Real.sqrt (‖a l‖) * ‖c (k - l)‖)
            = (Real.sqrt (‖a l‖) * Real.sqrt (‖a l‖))
              * (|ρ (ε • (fun j => ((k - l) j : ℝ))) - ρ (ε • (fun j => (k j : ℝ)))| * ‖c (k - l)‖)
            from by ring,
            Real.mul_self_sqrt (norm_nonneg _)]
          ring
      _ ≤ (∑' l, (Real.sqrt (‖a l‖)
              * |ρ (ε • (fun j => ((k - l) j : ℝ))) - ρ (ε • (fun j => (k j : ℝ)))|) ^ 2)
          * (∑' l, (Real.sqrt (‖a l‖) * ‖c (k - l)‖) ^ 2) := hmain
      _ = (∑' l, ‖a l‖
              * |ρ (ε • (fun j => ((k - l) j : ℝ))) - ρ (ε • (fun j => (k j : ℝ)))| ^ 2)
          * (∑' l, ‖a l‖ * ‖c (k - l)‖ ^ 2) := by
          congr 1
          · exact tsum_congr fun l => by rw [mul_pow, Real.sq_sqrt (norm_nonneg _)]
          · exact tsum_congr fun l => by rw [mul_pow, Real.sq_sqrt (norm_nonneg _)]
  -- the first Cauchy–Schwarz factor, bounded
  have hPsiBound : ∀ k : ι → ℤ,
      (Work.Diff.STE.wt k) ^ (s + 1)
          * (∑' l, ‖a l‖
              * |ρ (ε • (fun j => ((k - l) j : ℝ))) - ρ (ε • (fun j => (k j : ℝ)))| ^ 2)
        ≤ (2 ^ (2 * s + 1) * K * (Work.Diff.STE.wt k) ^ s) * A2 := by
    intro k
    have hpt : ∀ l : ι → ℤ,
        (Work.Diff.STE.wt k) ^ (s + 1) * (‖a l‖
            * |ρ (ε • (fun j => ((k - l) j : ℝ))) - ρ (ε • (fun j => (k j : ℝ)))| ^ 2)
          ≤ (2 ^ (2 * s + 1) * K * (Work.Diff.STE.wt k) ^ s)
            * ((Work.Diff.STE.wt l) ^ (2 * s + 2) * ‖a l‖) := by
      intro l
      have hD1 : Work.Diff.STE.wt (k - l)
          * |ρ (ε • (fun j => ((k - l) j : ℝ))) - ρ (ε • (fun j => (k j : ℝ)))| ^ 2
            ≤ K * Work.Diff.STE.wt l := by
        have h := Work.Diff.STE.B3.SymCalcStep1.friedrichs_pointwise_nosupp
          ρ hρb hdiam L hL hρlip ε hε hε1 k (k - l)
        rw [sub_sub_self] at h
        rw [hK]
        rw [sq_abs]
        exact h
      have hZnn : (0 : ℝ) ≤ (Work.Diff.STE.wt (k - l)) ^ s :=
        pow_nonneg (le_of_lt (Work.Diff.STE.wt_pos _)) s
      have hp1 := wt_pow_le (s + 1) k l
      have hp2 : (Work.Diff.STE.wt (k - l)) ^ s
          ≤ 2 ^ s * ((Work.Diff.STE.wt k) ^ s * (Work.Diff.STE.wt l) ^ s) := by
        have h := wt_sub_le k l
        calc (Work.Diff.STE.wt (k - l)) ^ s
            ≤ (2 * (Work.Diff.STE.wt k * Work.Diff.STE.wt l)) ^ s :=
              pow_le_pow_left₀ (le_of_lt (Work.Diff.STE.wt_pos _)) h s
          _ = 2 ^ s * ((Work.Diff.STE.wt k) ^ s * (Work.Diff.STE.wt l) ^ s) := by
              rw [mul_pow, mul_pow]
      have h2 : (Work.Diff.STE.wt (k - l)) ^ (s + 1)
          * |ρ (ε • (fun j => ((k - l) j : ℝ))) - ρ (ε • (fun j => (k j : ℝ)))| ^ 2
            ≤ (Work.Diff.STE.wt (k - l)) ^ s * (K * Work.Diff.STE.wt l) := by
        calc (Work.Diff.STE.wt (k - l)) ^ (s + 1)
            * |ρ (ε • (fun j => ((k - l) j : ℝ))) - ρ (ε • (fun j => (k j : ℝ)))| ^ 2
            = (Work.Diff.STE.wt (k - l)) ^ s
              * (Work.Diff.STE.wt (k - l)
                * |ρ (ε • (fun j => ((k - l) j : ℝ))) - ρ (ε • (fun j => (k j : ℝ)))| ^ 2) := by
              ring
          _ ≤ (Work.Diff.STE.wt (k - l)) ^ s * (K * Work.Diff.STE.wt l) :=
              mul_le_mul_of_nonneg_left hD1 hZnn
      have hstep : (Work.Diff.STE.wt k) ^ (s + 1)
          * |ρ (ε • (fun j => ((k - l) j : ℝ))) - ρ (ε • (fun j => (k j : ℝ)))| ^ 2
            ≤ 2 ^ (2 * s + 1) * K * (Work.Diff.STE.wt k) ^ s * (Work.Diff.STE.wt l) ^ (2 * s + 2) := by
        calc (Work.Diff.STE.wt k) ^ (s + 1)
            * |ρ (ε • (fun j => ((k - l) j : ℝ))) - ρ (ε • (fun j => (k j : ℝ)))| ^ 2
            ≤ (2 ^ (s + 1) * ((Work.Diff.STE.wt l) ^ (s + 1)
                * (Work.Diff.STE.wt (k - l)) ^ (s + 1)))
              * |ρ (ε • (fun j => ((k - l) j : ℝ))) - ρ (ε • (fun j => (k j : ℝ)))| ^ 2 :=
              mul_le_mul_of_nonneg_right hp1 (sq_nonneg _)
          _ = 2 ^ (s + 1) * (Work.Diff.STE.wt l) ^ (s + 1)
              * ((Work.Diff.STE.wt (k - l)) ^ (s + 1)
                * |ρ (ε • (fun j => ((k - l) j : ℝ))) - ρ (ε • (fun j => (k j : ℝ)))| ^ 2) := by
              ring
          _ ≤ 2 ^ (s + 1) * (Work.Diff.STE.wt l) ^ (s + 1)
              * ((Work.Diff.STE.wt (k - l)) ^ s * (K * Work.Diff.STE.wt l)) :=
              mul_le_mul_of_nonneg_left h2
                (mul_nonneg (by positivity) (pow_nonneg (le_of_lt (Work.Diff.STE.wt_pos l)) _))
          _ ≤ 2 ^ (s + 1) * (Work.Diff.STE.wt l) ^ (s + 1)
              * ((2 ^ s * ((Work.Diff.STE.wt k) ^ s * (Work.Diff.STE.wt l) ^ s))
                * (K * Work.Diff.STE.wt l)) :=
              mul_le_mul_of_nonneg_left
                (mul_le_mul_of_nonneg_right hp2
                  (mul_nonneg hKnn (le_of_lt (Work.Diff.STE.wt_pos l))))
                (mul_nonneg (by positivity) (pow_nonneg (le_of_lt (Work.Diff.STE.wt_pos l)) _))
          _ = 2 ^ (2 * s + 1) * K * (Work.Diff.STE.wt k) ^ s * (Work.Diff.STE.wt l) ^ (2 * s + 2) := by
              ring
      calc (Work.Diff.STE.wt k) ^ (s + 1) * (‖a l‖
            * |ρ (ε • (fun j => ((k - l) j : ℝ))) - ρ (ε • (fun j => (k j : ℝ)))| ^ 2)
          = ‖a l‖ * ((Work.Diff.STE.wt k) ^ (s + 1)
              * |ρ (ε • (fun j => ((k - l) j : ℝ))) - ρ (ε • (fun j => (k j : ℝ)))| ^ 2) := by
            ring
        _ ≤ ‖a l‖ * (2 ^ (2 * s + 1) * K * (Work.Diff.STE.wt k) ^ s
              * (Work.Diff.STE.wt l) ^ (2 * s + 2)) :=
            mul_le_mul_of_nonneg_left hstep (norm_nonneg _)
        _ = (2 ^ (2 * s + 1) * K * (Work.Diff.STE.wt k) ^ s)
            * ((Work.Diff.STE.wt l) ^ (2 * s + 2) * ‖a l‖) := by ring
    calc (Work.Diff.STE.wt k) ^ (s + 1)
          * (∑' l, ‖a l‖
              * |ρ (ε • (fun j => ((k - l) j : ℝ))) - ρ (ε • (fun j => (k j : ℝ)))| ^ 2)
        = ∑' l, (Work.Diff.STE.wt k) ^ (s + 1) * (‖a l‖
              * |ρ (ε • (fun j => ((k - l) j : ℝ))) - ρ (ε • (fun j => (k j : ℝ)))| ^ 2) := by
          rw [tsum_mul_left]
      _ ≤ ∑' l, (2 ^ (2 * s + 1) * K * (Work.Diff.STE.wt k) ^ s)
            * ((Work.Diff.STE.wt l) ^ (2 * s + 2) * ‖a l‖) :=
          Summable.tsum_le_tsum hpt ((hPsi k).mul_left _) (hA2sum.mul_left _)
      _ = (2 ^ (2 * s + 1) * K * (Work.Diff.STE.wt k) ^ s) * A2 := by
          rw [tsum_mul_left, ← hA2]
  -- the second factor, summed over the frequency
  have hreindex : ∀ k : ι → ℤ,
      (∑' l : ι → ℤ, ‖a l‖ * ‖c (k - l)‖ ^ 2)
        = ∑' m : ι → ℤ, ‖a (k - m)‖ * ‖c m‖ ^ 2 := by
    intro k
    let e : (ι → ℤ) ≃ (ι → ℤ) :=
      { toFun := fun l => k - l
        invFun := fun l => k - l
        left_inv := fun l => sub_sub_self k l
        right_inv := fun l => sub_sub_self k l }
    have h := Equiv.tsum_eq e (fun l : ι → ℤ => ‖a l‖ * ‖c (k - l)‖ ^ 2)
    simpa [e, sub_sub_self] using h.symm
  have hGammasumm : Summable (fun k : ι → ℤ => (Work.Diff.STE.wt k) ^ s
      * (∑' l : ι → ℤ, ‖a l‖ * ‖c (k - l)‖ ^ 2)) := by
    refine ((wt_shift_conv_tsum a c s hAssum hc).1).congr fun k => ?_
    rw [hreindex k]
  have hGammaLe : (∑' k : ι → ℤ, (Work.Diff.STE.wt k) ^ s
      * (∑' l : ι → ℤ, ‖a l‖ * ‖c (k - l)‖ ^ 2)) ≤ 2 ^ s * As * Work.Diff.STE.CSq s c := by
    have h := (wt_shift_conv_tsum a c s hAssum hc).2
    calc (∑' k : ι → ℤ, (Work.Diff.STE.wt k) ^ s
          * (∑' l : ι → ℤ, ‖a l‖ * ‖c (k - l)‖ ^ 2))
        = ∑' k : ι → ℤ, (Work.Diff.STE.wt k) ^ s
            * (∑' m : ι → ℤ, ‖a (k - m)‖ * ‖c m‖ ^ 2) :=
          tsum_congr fun k => by rw [hreindex k]
      _ ≤ 2 ^ s * As * Work.Diff.STE.CSq s c := by
          refine h.trans_eq ?_
          rw [← hAs]
          rfl
  -- the pointwise bound for the commutator, weighted
  have hQbound : ∀ k : ι → ℤ, (Work.Diff.STE.wt k) ^ (s + 1)
        * ‖Work.Diff.STE.conv a (Work.Diff.STE.trunc ρ ε c) k
            - Work.Diff.STE.trunc ρ ε (Work.Diff.STE.conv a c) k‖ ^ 2
      ≤ 2 ^ (2 * s + 1) * K * A2 * ((Work.Diff.STE.wt k) ^ s
          * (∑' l : ι → ℤ, ‖a l‖ * ‖c (k - l)‖ ^ 2)) := by
    intro k
    calc (Work.Diff.STE.wt k) ^ (s + 1)
          * ‖Work.Diff.STE.conv a (Work.Diff.STE.trunc ρ ε c) k
              - Work.Diff.STE.trunc ρ ε (Work.Diff.STE.conv a c) k‖ ^ 2
        ≤ (Work.Diff.STE.wt k) ^ (s + 1)
            * (∑' l, ‖a l‖
              * |ρ (ε • (fun j => ((k - l) j : ℝ))) - ρ (ε • (fun j => (k j : ℝ)))| * ‖c (k - l)‖) ^ 2 :=
          mul_le_mul_of_nonneg_left
            (pow_le_pow_left₀ (norm_nonneg _) (hnorm k) 2)
            (pow_nonneg (le_of_lt (Work.Diff.STE.wt_pos k)) _)
      _ ≤ (Work.Diff.STE.wt k) ^ (s + 1)
            * ((∑' l, ‖a l‖
                * |ρ (ε • (fun j => ((k - l) j : ℝ))) - ρ (ε • (fun j => (k j : ℝ)))| ^ 2)
              * (∑' l, ‖a l‖ * ‖c (k - l)‖ ^ 2)) :=
          mul_le_mul_of_nonneg_left (hCS k) (pow_nonneg (le_of_lt (Work.Diff.STE.wt_pos k)) _)
      _ = ((Work.Diff.STE.wt k) ^ (s + 1)
            * (∑' l, ‖a l‖
              * |ρ (ε • (fun j => ((k - l) j : ℝ))) - ρ (ε • (fun j => (k j : ℝ)))| ^ 2))
          * (∑' l, ‖a l‖ * ‖c (k - l)‖ ^ 2) := by ring
      _ ≤ (2 ^ (2 * s + 1) * K * (Work.Diff.STE.wt k) ^ s * A2)
          * (∑' l, ‖a l‖ * ‖c (k - l)‖ ^ 2) :=
          mul_le_mul_of_nonneg_right (hPsiBound k)
            (tsum_nonneg fun l => mul_nonneg (norm_nonneg _) (sq_nonneg _))
      _ = 2 ^ (2 * s + 1) * K * A2 * ((Work.Diff.STE.wt k) ^ s
          * (∑' l, ‖a l‖ * ‖c (k - l)‖ ^ 2)) := by ring
  have hsumm : Summable (fun k : ι → ℤ => (Work.Diff.STE.wt k) ^ (s + 1)
      * ‖Work.Diff.STE.conv a (Work.Diff.STE.trunc ρ ε c) k
          - Work.Diff.STE.trunc ρ ε (Work.Diff.STE.conv a c) k‖ ^ 2) :=
    Summable.of_nonneg_of_le
      (fun k => mul_nonneg (pow_nonneg (le_of_lt (Work.Diff.STE.wt_pos k)) _) (sq_nonneg _))
      hQbound (hGammasumm.mul_left _)
  calc Work.Diff.STE.CSq (s + 1)
        (fun k => Work.Diff.STE.conv a (Work.Diff.STE.trunc ρ ε c) k
          - Work.Diff.STE.trunc ρ ε (Work.Diff.STE.conv a c) k)
      = ∑' k : ι → ℤ, (Work.Diff.STE.wt k) ^ (s + 1)
          * ‖Work.Diff.STE.conv a (Work.Diff.STE.trunc ρ ε c) k
              - Work.Diff.STE.trunc ρ ε (Work.Diff.STE.conv a c) k‖ ^ 2 := rfl
    _ ≤ ∑' k : ι → ℤ, 2 ^ (2 * s + 1) * K * A2 * ((Work.Diff.STE.wt k) ^ s
          * (∑' l : ι → ℤ, ‖a l‖ * ‖c (k - l)‖ ^ 2)) :=
        Summable.tsum_le_tsum hQbound hsumm (hGammasumm.mul_left _)
    _ = 2 ^ (2 * s + 1) * K * A2 * (∑' k : ι → ℤ, (Work.Diff.STE.wt k) ^ s
          * (∑' l : ι → ℤ, ‖a l‖ * ‖c (k - l)‖ ^ 2)) := by
        rw [tsum_mul_left]
    _ ≤ 2 ^ (2 * s + 1) * K * A2 * (2 ^ s * As * Work.Diff.STE.CSq s c) :=
        mul_le_mul_of_nonneg_left hGammaLe (by positivity)
    _ = (2 ^ (3 * s + 1) * K * A2 * As) * Work.Diff.STE.CSq s c := by ring

end Work.Diff.STE.B3.SymCalcStep8
