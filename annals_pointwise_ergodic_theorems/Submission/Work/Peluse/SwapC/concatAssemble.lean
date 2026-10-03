import Mathlib
import Submission.Work.Peluse.SwapC.concatCore
import Submission.Work.Peluse.Holds.ExpPET.Jensen

/-!
# Assembly lemmas for `Work.Peluse.SwapC.concatStep`

The elementary real-analytic bookkeeping of the concatenation step: the Cauchy–Schwarz inequality in
the base variable, and the "cardinality blindness" of `mCubeSum` in the normalising set.
-/

set_option autoImplicit false

open scoped BigOperators

namespace Work.Peluse.SwapC

noncomputable section

open Work.Peluse

/-- **Cauchy–Schwarz in the base variable** (KKL's step 3).  If `δ·|S| ≤ Re ∑_x f(x)Φ(x)` with
`f` `1`-bounded, vanishing off `S`, then `δ²·|S| ≤ ∑_x ‖Φ x‖²`. -/
theorem cauchySchwarz_base {S T : Finset ℤ} {f Φ : ℤ → ℂ} {δ : ℝ}
    (hf : ∀ x : ℤ, x ∉ S → f x = 0) (hΦ : ∀ x : ℤ, x ∉ T → Φ x = 0) (hST : S ⊆ T)
    (hb : ∀ x : ℤ, ‖f x‖ ≤ 1) (hδ : 0 ≤ δ)
    (h : δ * (S.card : ℝ) ≤ (∑' x : ℤ, f x * Φ x).re) :
    δ ^ 2 * (S.card : ℝ) ≤ ∑' x : ℤ, ‖Φ x‖ ^ 2 := by
  have htsum_f : (∑' x : ℤ, f x * Φ x) = ∑ x ∈ S, f x * Φ x :=
    tsum_eq_sum (s := S) (fun x hx => by rw [hf x hx, zero_mul])
  have htsum_Φ : (∑' x : ℤ, ‖Φ x‖ ^ 2) = ∑ x ∈ T, ‖Φ x‖ ^ 2 :=
    tsum_eq_sum (s := T) (fun x hx => by rw [hΦ x hx, norm_zero]; norm_num)
  have hTnonneg : (0 : ℝ) ≤ ∑ x ∈ T, ‖Φ x‖ ^ 2 :=
    Finset.sum_nonneg fun x _ => sq_nonneg _
  rcases Nat.eq_zero_or_pos S.card with hcard | hcard
  · rw [htsum_Φ]
    have hzero : (S.card : ℝ) = 0 := by rw [hcard]; norm_num
    rw [hzero, mul_zero]
    exact hTnonneg
  · have hSpos : (0 : ℝ) < (S.card : ℝ) := by exact_mod_cast hcard
    have hfsum : ∑ x ∈ S, ‖f x‖ ^ 2 ≤ (S.card : ℝ) := by
      have hterm : ∀ x ∈ S, ‖f x‖ ^ 2 ≤ (1 : ℝ) := fun x _ => by
        have h1 : ‖f x‖ ^ 2 ≤ 1 ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (hb x) 2
        simpa using h1
      calc ∑ x ∈ S, ‖f x‖ ^ 2 ≤ ∑ _x ∈ S, (1 : ℝ) := Finset.sum_le_sum hterm
        _ = (S.card : ℝ) := by simp
    have hΦsum : ∑ x ∈ S, ‖Φ x‖ ^ 2 ≤ ∑ x ∈ T, ‖Φ x‖ ^ 2 :=
      Finset.sum_le_sum_of_subset_of_nonneg hST fun x _ _ => sq_nonneg _
    have hcs : ‖∑ x ∈ S, f x * Φ x‖ ^ 2 ≤ (S.card : ℝ) * (∑ x ∈ T, ‖Φ x‖ ^ 2) := by
      have h1 := Work.Peluse.BoxNorm.cauchySchwarzC S f (fun x => star (Φ x))
      have h2 : (∑ x ∈ S, ‖f x‖ ^ 2) * (∑ x ∈ S, ‖star (Φ x)‖ ^ 2)
          ≤ (S.card : ℝ) * (∑ x ∈ T, ‖Φ x‖ ^ 2) := by
        have h3 : (∑ x ∈ S, ‖star (Φ x)‖ ^ 2) = ∑ x ∈ S, ‖Φ x‖ ^ 2 := by simp
        rw [h3]
        exact mul_le_mul hfsum hΦsum (Finset.sum_nonneg fun x _ => sq_nonneg _) (by positivity)
      have h4 : (∑ x ∈ S, f x * star (star (Φ x))) = ∑ x ∈ S, f x * Φ x := by
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [star_star]
      rw [h4] at h1
      exact le_trans h1 h2
    have hRe : δ * (S.card : ℝ) ≤ ‖∑ x ∈ S, f x * Φ x‖ := by
      calc δ * (S.card : ℝ) ≤ (∑' x : ℤ, f x * Φ x).re := h
        _ = (∑ x ∈ S, f x * Φ x).re := by rw [htsum_f]
        _ ≤ ‖∑ x ∈ S, f x * Φ x‖ := Complex.re_le_norm _
    have hsq : (δ * (S.card : ℝ)) ^ 2 ≤ (‖∑ x ∈ S, f x * Φ x‖) ^ 2 := by
      exact pow_le_pow_left₀ (mul_nonneg hδ (by positivity)) hRe 2
    rw [htsum_Φ]
    have hfinal : (δ * (S.card : ℝ)) ^ 2 ≤ (S.card : ℝ) * (∑ x ∈ T, ‖Φ x‖ ^ 2) :=
      le_trans hsq hcs
    have hmul : (δ * (S.card : ℝ)) ^ 2 = δ ^ 2 * (S.card : ℝ) * (S.card : ℝ) := by ring
    rw [hmul] at hfinal
    rw [mul_comm ((S.card : ℝ)) (∑ x ∈ T, ‖Φ x‖ ^ 2)] at hfinal
    exact le_of_mul_le_mul_right hfinal hSpos

/-- `mCubeSum` sees its normalising set only through its cardinality. -/
lemma mCubeSum_card_congr (d : ℕ) (X : Type) [Fintype X] (ν : Fin d → X → ℤ)
    {S T : Finset ℤ} (h : S.card = T.card) (F : (Fin d → Bool) → ℤ → ℂ) :
    mCubeSum d X ν S F = mCubeSum d X ν T F := by
  simp [mCubeSum, h]

/-- The increment tuple of the `i`-th level-`(s+1)` box along the pair of index tuples `(H, H')`:
the `0`-th entry is the *raw* increment `qH i(a+1) − qH i(a'+1)` (independent of the second
coordinate of `H 0`), the entry `k+1` is the `K`-difference of the `k`-th slot. -/
def incr (s M : ℕ) (qH : ℤ) (q₁ q₂ : Fin s → ℤ)
    (H H' : Fin (s+1) → Fin M × Fin M) : Fin (s+1) → ℤ :=
  fun k => Work.Peluse.LadderP.Swap.pdir ((Fin.cons qH q₁ : Fin (s+1) → ℤ) k)
      ((Fin.cons (0 : ℤ) q₂ : Fin (s+1) → ℤ) k) (H k)
    - Work.Peluse.LadderP.Swap.pdir ((Fin.cons qH q₁ : Fin (s+1) → ℤ) k)
      ((Fin.cons (0 : ℤ) q₂ : Fin (s+1) → ℤ) k) (H' k)

/-- The **gauge** of the concatenation step: the `Rest`-product of the hypothesis, averaged over the
index `i` and over the pair of shift tuples, with the normalising factor of `pboxSum`. -/
def gauge {I : Type} [Fintype I] (s M : ℕ) (qH : I → ℤ) (q₁ q₂ : I → Fin s → ℤ)
    (f : ℤ → ℂ) : ℤ → ℂ :=
  fun y => (((M : ℂ) ^ 4)⁻¹) ^ (s+1) *
    (((Fintype.card I : ℂ))⁻¹ * ∑ i : I, ∑ H : Fin (s+1) → Fin M × Fin M,
      ∑ H' : Fin (s+1) → Fin M × Fin M, Rest (incr s M (qH i) (q₁ i) (q₂ i) H H') f y)

/-- The pair object of the expansion of `‖gauge‖²`: the doubled `Rest`-product of the two indices. -/
def pairObj {I : Type} (s M : ℕ) (qH : I → ℤ) (q₁ q₂ : I → Fin s → ℤ) (f : ℤ → ℂ) (i₀ i₁ : I)
    (H₀ H₀' H₁ H₁' : Fin (s+1) → Fin M × Fin M) : ℂ :=
  ∑' y : ℤ, Rest (incr s M (qH i₀) (q₁ i₀) (q₂ i₀) H₀ H₀') f y *
    star (Rest (incr s M (qH i₁) (q₁ i₁) (q₂ i₁) H₁ H₁') f y)

end

end Work.Peluse.SwapC
