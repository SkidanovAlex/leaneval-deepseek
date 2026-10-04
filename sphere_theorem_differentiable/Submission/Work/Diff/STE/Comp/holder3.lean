import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.STE.Comp

/-- Discrete Hölder inequality for three nonnegative families on `ι → ℤ` (`tsum` version):
if `1/a + 1/b + 1/c = 1` with `a, b, c > 0` and `A^a`, `B^b`, `C^c` are summable, then `A * B * C`
is summable and `∑' A B C ≤ (∑' A^a)^{1/a} (∑' B^b)^{1/b} (∑' C^c)^{1/c}`.

Route: put `a' := (b⁻¹ + c⁻¹)⁻¹`; by `habc` this is the conjugate `(1 - a⁻¹)⁻¹` of `a`, i.e.
`a⁻¹ + a'⁻¹ = 1`, and `Real.HolderTriple.of_pos hb hc` is `b.HolderTriple c a'` definitionally.
1. `Real.Lr_le_Lp_mul_Lq_tsum_of_nonneg` (with `p := b`, `q := c`, `r := a'`) gives
   `(∑' k, (B k * C k) ^ a') ^ (1 / a') ≤ (∑' B^b) ^ (1 / b) * (∑' C^c) ^ (1 / c)` and
   `Real.summable_and_Lr_rpow_le_Lp_mul_Lq_tsum_of_nonneg` (same data) gives
   `Summable (fun k => (B k * C k) ^ a')`.
2. `Real.summable_and_inner_le_Lp_mul_Lq_tsum_of_nonneg` with the conjugate exponents `a`, `a'`
   (the conjugacy `a.HolderConjugate a'` is `⟨by rw [inv_inv, inv_one]; linarith [habc], ha, ha'pos⟩`
   where `ha'pos : 0 < a'`), applied to `A` and `fun k => B k * C k`, needs exactly the summability
   from 1, and gives `Summable (fun k => A k * (B k * C k))` together with
   `∑' k, A k * (B k * C k) ≤ (∑' A^a) ^ (1/a) * (∑' (B * C)^a') ^ (1/a')`.
3. Combine: multiply the inequality of 1 by `(∑' A^a) ^ (1/a)` on the left
   (`mul_le_mul_of_nonneg_left`), then `mul_assoc`, and rewrite `A k * (B k * C k) = A k * B k * C k`. -/
theorem holder3 {ι : Type*} [Fintype ι] [DecidableEq ι] (A B C : (ι → ℤ) → ℝ)
    (hA : ∀ k, 0 ≤ A k) (hB : ∀ k, 0 ≤ B k) (hC : ∀ k, 0 ≤ C k)
    {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (habc : a⁻¹ + b⁻¹ + c⁻¹ = 1)
    (hAs : Summable fun k => A k ^ a) (hBs : Summable fun k => B k ^ b)
    (hCs : Summable fun k => C k ^ c) :
    Summable (fun k => A k * B k * C k) ∧
      ∑' k, A k * B k * C k
        ≤ (∑' k, A k ^ a) ^ (1 / a) * (∑' k, B k ^ b) ^ (1 / b) * (∑' k, C k ^ c) ^ (1 / c) := by
  -- the conjugate exponent `a' = (b⁻¹ + c⁻¹)⁻¹` of `a` is positive and `a⁻¹ + a'⁻¹ = 1`
  have ha'pos : 0 < (b⁻¹ + c⁻¹)⁻¹ := inv_pos.mpr (add_pos (inv_pos.mpr hb) (inv_pos.mpr hc))
  have hBC : ∀ k : ι → ℤ, 0 ≤ B k * C k := fun k => mul_nonneg (hB k) (hC k)
  -- Step 1: Hölder for `B` and `C` with the exponents `(b, c, a')`.
  have hpqr : b.HolderTriple c (b⁻¹ + c⁻¹)⁻¹ := Real.HolderTriple.of_pos hb hc
  have hBCs : Summable fun k => (B k * C k) ^ (b⁻¹ + c⁻¹)⁻¹ :=
    Real.summable_Lr_of_Lp_Lq_of_nonneg (f := B) (g := C) (p := b) (q := c)
      (r := (b⁻¹ + c⁻¹)⁻¹) hpqr hB hC hBs hCs
  have hLr : (∑' k, (B k * C k) ^ (b⁻¹ + c⁻¹)⁻¹) ^ (1 / (b⁻¹ + c⁻¹)⁻¹)
      ≤ (∑' k, B k ^ b) ^ (1 / b) * (∑' k, C k ^ c) ^ (1 / c) :=
    Real.Lr_le_Lp_mul_Lq_tsum_of_nonneg (f := B) (g := C) (p := b) (q := c)
      (r := (b⁻¹ + c⁻¹)⁻¹) hpqr hB hC hBs hCs
  -- Step 2: Hölder for `A` and `B * C` with the conjugate exponents `(a, a')`.
  have hconj : a.HolderConjugate ((b⁻¹ + c⁻¹)⁻¹) :=
    ⟨by rw [inv_inv, inv_one]; linarith [habc], ha, ha'pos⟩
  have h2 := Real.summable_and_inner_le_Lp_mul_Lq_tsum_of_nonneg (f := A)
    (g := fun k => B k * C k) (p := a) (q := (b⁻¹ + c⁻¹)⁻¹) hconj hA hBC hAs hBCs
  -- Step 3: combine the two estimates and reassociate the product.
  have hA_nonneg : 0 ≤ ∑' k, A k ^ a := tsum_nonneg fun k => Real.rpow_nonneg (hA k) a
  have hstep : ∑' k, A k * (B k * C k)
      ≤ (∑' k, A k ^ a) ^ (1 / a)
        * ((∑' k, B k ^ b) ^ (1 / b) * (∑' k, C k ^ c) ^ (1 / c)) :=
    le_trans h2.2 (mul_le_mul_of_nonneg_left hLr (Real.rpow_nonneg hA_nonneg (1 / a)))
  have hAB : (∑' k, A k * B k * C k) = ∑' k, A k * (B k * C k) :=
    tsum_congr fun k => by ring
  refine ⟨?_, ?_⟩
  · exact Summable.congr h2.1 fun k => by ring
  · rw [hAB, mul_assoc]
    exact hstep

end Work.Diff.STE.Comp
