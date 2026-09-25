import Mathlib
import Submission.Work.CR.Flat.Holder
import Submission.Work.CR.Flat.Holder.Bilinear
import Submission.Work.CR.Flat.Holder.hSN_bilinear_le
import Submission.Work.CR.Flat.Holder.holderNorm_mul_le

/-!
# The two-term Leibniz bound for the `C^{k,α}` norm of a product

This file proves `holderNorm_mul_le_two`: for `C^k` functions `f g : X → ℂ` on `Ω` whose
`C^{k,α}` norms are finite, there is a constant `C > 0` with

`‖f * g‖_{k,α} ≤ ‖f‖_{0,α} * ‖g‖_{k,α} + C * (‖f‖_{k,α} * ‖g‖_{k-1,α})`.

The classical Leibniz rule expresses `D^i(f * g)` as a sum over `j ≤ i` of
`binom(i,j) * D^j f * D^{i-j} g`.  Grouping the `j = 0` term separately (`D^0 f = f`, whose
`C^{0,α}` norm controls it) and bounding every remaining term by the full norm of `f` times
the norm of `g` of order at most `i - 1 ≤ k - 1` yields exactly the two-term bound above.

The norm is the one of `Submission/Work/CR/Flat/Holder.lean`, taking values in `ℝ≥0∞`.
-/

noncomputable section

open scoped NNReal ENNReal
open Set

namespace Work.CR.Flat.Holder

section aux

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-! ### Elementary ENNReal inequality -/

/-- The inequality behind the grouping of the Leibniz terms: the part of `(a+b)(c+d)`
coming from `a*c + b*c + a*d` (i.e. everything except the cross term `b*d`). -/
private lemma mul_add_le_mul_add (a b c d : ℝ≥0∞) :
    a * c + (b * c + a * d) ≤ (a + b) * (c + d) := by
  calc a * c + (b * c + a * d) = (a * c + b * c) + a * d := by ac_rfl
    _ ≤ (a * c + b * c) + (a * d + b * d) := by
        gcongr
        exact le_add_right le_rfl
    _ = (a + b) * (c + d) := by rw [mul_add, add_mul, add_mul]

/-- The `0`-th `C^{0,α}` norm is the sum of the sup norm and the Hölder seminorm. -/
lemma holderNorm_zero_eq (α : ℝ) (f : X → ℂ) (Ω : Set X) :
    holderNorm 0 α f Ω = iDN 0 f Ω + hSN 0 α f Ω := by
  have h : holderNorm 0 α f Ω = ∑ i ∈ Finset.range (0 + 1), (iDN i f Ω + hSN i α f Ω) := rfl
  rw [h]
  exact Finset.sum_range_one _

/-- `∑_{j < i} binom(i, j+1) ≤ 2^i`: the sum of the binomial coefficients of order `i`
over the indices `1, …, i`. -/
private lemma sum_choose_succ_le (i : ℕ) :
    (∑ j ∈ Finset.range i, (i.choose (j+1) : ℝ≥0∞)) ≤ (2 : ℝ≥0∞) ^ i := by
  have hcast : (∑ j ∈ Finset.range (i + 1), (i.choose j : ℝ≥0∞)) = (2 : ℝ≥0∞) ^ i := by
    exact_mod_cast Nat.sum_range_choose i
  have himg : (∑ x ∈ (Finset.range i).image (fun j => j+1), (i.choose x : ℝ≥0∞))
      = ∑ j ∈ Finset.range i, (i.choose (j+1) : ℝ≥0∞) :=
    Finset.sum_image (fun a _ b _ h => Nat.succ.inj h)
  have hsub : (Finset.range i).image (fun j => j+1) ⊆ Finset.range (i+1) := by
    intro x hx
    simp only [Finset.mem_image, Finset.mem_range] at hx ⊢
    obtain ⟨y, hy, rfl⟩ := hx
    omega
  calc (∑ j ∈ Finset.range i, (i.choose (j+1) : ℝ≥0∞))
      = ∑ x ∈ (Finset.range i).image (fun j => j+1), (i.choose x : ℝ≥0∞) := himg.symm
    _ ≤ ∑ x ∈ Finset.range (i+1), (i.choose x : ℝ≥0∞) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => bot_le)
    _ = (2 : ℝ≥0∞) ^ i := hcast

/-- The Hölder-seminorm part of the Leibniz bound for a product of `ℂ`-valued functions:
`[D^i (f*g)]_α ≤ ∑_j binom(i,j) ([D^j f]_α ‖D^{i-j} g‖_∞ + ‖D^j f‖_∞ [D^{i-j} g]_α)`. -/
lemma hSN_mul_le {i : ℕ} {α : ℝ} {f g : X → ℂ} {Ω : Set X}
    (hf : ContDiffOn ℝ i f Ω) (hg : ContDiffOn ℝ i g Ω) (hΩ : UniqueDiffOn ℝ Ω) :
    hSN i α (fun x => f x * g x) Ω
      ≤ ∑ j ∈ Finset.range (i + 1), (i.choose j : ℝ≥0∞) *
          (hSN j α f Ω * iDN (i - j) g Ω + iDN j f Ω * hSN (i - j) α g Ω) := by
  let e : ℂ ≃ₗᵢ[ℝ] ULift ℂ := (LinearIsometryEquiv.ulift ℝ ℂ).symm
  let F : X → ULift ℂ := fun x => e (f x)
  let G : X → ULift ℂ := fun x => e (g x)
  have hb := hSN_bilinear_le (E := ULift ℂ) (F := ULift ℂ) (G := ULift ℂ)
      (B := ContinuousLinearMap.mul ℝ (ULift ℂ)) i α (f := F) (g := G) (Ω := Ω)
      (contDiffOn_comp_lie e hf) (contDiffOn_comp_lie e hg) hΩ
  have hbL : hSN i α (fun x => (ContinuousLinearMap.mul ℝ (ULift ℂ) (F x)) (G x)) Ω
      = hSN i α (fun x => f x * g x) Ω := by
    rw [show (fun x => (ContinuousLinearMap.mul ℝ (ULift ℂ) (F x)) (G x))
          = (fun x => F x * G x) from rfl]
    rw [show (fun x => F x * G x) = fun x => e (f x * g x) from rfl]
    exact hSN_comp_lie e (fun x => f x * g x) i α Ω hΩ
  rw [hbL] at hb
  have hbR : (∑ j ∈ Finset.range (i + 1), (i.choose j : ℝ≥0∞) *
        (hSN j α F Ω * iDN (i - j) G Ω + iDN j F Ω * hSN (i - j) α G Ω))
      = ∑ j ∈ Finset.range (i + 1), (i.choose j : ℝ≥0∞) *
        (hSN j α f Ω * iDN (i - j) g Ω + iDN j f Ω * hSN (i - j) α g Ω) := by
    apply Finset.sum_congr rfl
    intro j hj
    rw [hSN_comp_lie e f j α Ω hΩ, iDN_comp_lie e g (i - j) Ω hΩ, iDN_comp_lie e f j Ω hΩ,
        hSN_comp_lie e g (i - j) α Ω hΩ]
  refine hb.trans ?_
  rw [hbR]
  calc ENNReal.ofReal ‖ContinuousLinearMap.mul ℝ (ULift ℂ)‖ *
        ∑ j ∈ Finset.range (i + 1), (i.choose j : ℝ≥0∞) *
          (hSN j α f Ω * iDN (i - j) g Ω + iDN j f Ω * hSN (i - j) α g Ω)
      ≤ 1 * ∑ j ∈ Finset.range (i + 1), (i.choose j : ℝ≥0∞) *
          (hSN j α f Ω * iDN (i - j) g Ω + iDN j f Ω * hSN (i - j) α g Ω) := by
        gcongr
        exact ENNReal.ofReal_le_one.mpr (ContinuousLinearMap.opNorm_mul_le ℝ (ULift ℂ))
    _ = _ := one_mul _

/-- The full Leibniz bound for the order-`i` part of the `C^{i,α}` norm of a product,
phrased directly through the sums of the sup norm and the Hölder seminorm. -/
lemma iDN_add_hSN_mul_le {i : ℕ} {α : ℝ} {f g : X → ℂ} {Ω : Set X}
    (hf : ContDiffOn ℝ i f Ω) (hg : ContDiffOn ℝ i g Ω) (hΩ : UniqueDiffOn ℝ Ω) :
    iDN i (fun x => f x * g x) Ω + hSN i α (fun x => f x * g x) Ω
      ≤ ∑ j ∈ Finset.range (i + 1), (i.choose j : ℝ≥0∞) *
          ((iDN j f Ω + hSN j α f Ω) * (iDN (i - j) g Ω + hSN (i - j) α g Ω)) := by
  refine (add_le_add (iDN_mul_le hf hg hΩ) (hSN_mul_le hf hg hΩ)).trans ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun j hj => ?_
  rw [← mul_add]
  exact mul_le_mul_right (mul_add_le_mul_add _ _ _ _) _

/-- An order-`i` summand of `holderNorm k` is bounded by `holderNorm k`. -/
lemma iDN_add_hSN_le_holderNorm (k : ℕ) (α : ℝ) (h : X → ℂ) (Ω : Set X) {i : ℕ}
    (hi : i ≤ k) : iDN i h Ω + hSN i α h Ω ≤ holderNorm k α h Ω := by
  have hsingle := Finset.single_le_sum (f := fun l => iDN l h Ω + hSN l α h Ω)
    (fun _ _ => bot_le) (Finset.mem_range.mpr (Nat.lt_succ_of_le hi))
  simpa [holderNorm] using hsingle

/-- The two-term bound at a single order: the order-`i` part of the `C^{i,α}` norm of the
product is bounded by (the `C^{0,α}` norm of `f`) times (the order-`i` part of `g`) plus
`2^i` times the product of the `C^{k,α}` norm of `f` and the `C^{k-1,α}` norm of `g`. -/
lemma iDN_add_hSN_mul_le_two {i k : ℕ} {α : ℝ} {f g : X → ℂ} {Ω : Set X}
    (hi : i ≤ k) (hf : ContDiffOn ℝ k f Ω) (hg : ContDiffOn ℝ k g Ω) (hΩ : UniqueDiffOn ℝ Ω) :
    iDN i (fun x => f x * g x) Ω + hSN i α (fun x => f x * g x) Ω
      ≤ (iDN 0 f Ω + hSN 0 α f Ω) * (iDN i g Ω + hSN i α g Ω)
        + (2 : ℝ≥0∞) ^ i * (holderNorm k α f Ω * holderNorm (k-1) α g Ω) := by
  have hik : ContDiffOn ℝ i f Ω := hf.of_le (by exact_mod_cast hi)
  have hig : ContDiffOn ℝ i g Ω := hg.of_le (by exact_mod_cast hi)
  have hsplit : (∑ j ∈ Finset.range (i + 1), (i.choose j : ℝ≥0∞) *
        ((iDN j f Ω + hSN j α f Ω) * (iDN (i - j) g Ω + hSN (i - j) α g Ω)))
      = ((iDN 0 f Ω + hSN 0 α f Ω) * (iDN i g Ω + hSN i α g Ω))
        + ∑ j ∈ Finset.range i, (i.choose (j+1) : ℝ≥0∞) *
          ((iDN (j+1) f Ω + hSN (j+1) α f Ω)
            * (iDN (i - (j+1)) g Ω + hSN (i - (j+1)) α g Ω)) := by
    rw [Finset.sum_range_succ']
    simp only [Nat.choose_zero_right, Nat.cast_one, one_mul, Nat.sub_zero]
    ac_rfl
  refine (iDN_add_hSN_mul_le hik hig hΩ).trans ?_
  rw [hsplit]
  refine add_le_add le_rfl ?_
  calc ∑ j ∈ Finset.range i, (i.choose (j+1) : ℝ≥0∞) *
        ((iDN (j+1) f Ω + hSN (j+1) α f Ω)
          * (iDN (i - (j+1)) g Ω + hSN (i - (j+1)) α g Ω))
      ≤ ∑ j ∈ Finset.range i, (i.choose (j+1) : ℝ≥0∞) *
          (holderNorm k α f Ω * holderNorm (k-1) α g Ω) := by
        refine Finset.sum_le_sum fun j hj => ?_
        have hj1 : j + 1 ≤ k := by have := Finset.mem_range.mp hj; omega
        have hij1 : i - (j+1) ≤ k - 1 := by have := Finset.mem_range.mp hj; omega
        refine mul_le_mul_right ?_ _
        gcongr
        · exact iDN_add_hSN_le_holderNorm k α f Ω hj1
        · exact iDN_add_hSN_le_holderNorm (k-1) α g Ω hij1
    _ = (∑ j ∈ Finset.range i, (i.choose (j+1) : ℝ≥0∞)) *
          (holderNorm k α f Ω * holderNorm (k-1) α g Ω) := by rw [Finset.sum_mul]
    _ ≤ (2 : ℝ≥0∞) ^ i * (holderNorm k α f Ω * holderNorm (k-1) α g Ω) :=
        mul_le_mul_left (sum_choose_succ_le i) _

/-- The sum of the powers of two up to `k` is bounded by `(k+1) * 2^{k+1}`. -/
lemma sum_pow_two_le (k : ℕ) :
    (∑ i ∈ Finset.range (k + 1), (2 : ℝ≥0∞) ^ i) ≤ ((k : ℝ≥0∞) + 1) * 2 ^ (k + 1) := by
  calc (∑ i ∈ Finset.range (k + 1), (2 : ℝ≥0∞) ^ i)
      ≤ ∑ i ∈ Finset.range (k + 1), 2 ^ (k + 1) :=
        Finset.sum_le_sum fun i hi =>
          pow_le_pow_right₀ (by norm_num) (by have := Finset.mem_range.mp hi; omega)
    _ = (k + 1) • (2 ^ (k + 1) : ℝ≥0∞) := by rw [Finset.sum_const, Finset.card_range]
    _ = ((k : ℝ≥0∞) + 1) * 2 ^ (k + 1) := by
        rw [nsmul_eq_mul, Nat.cast_add, Nat.cast_one]

/-- The real constant `(k+1) * 2^{k+1}` maps to the `ℝ≥0∞`-constant `(k+1) * 2^{k+1}`. -/
lemma ofReal_const_eq (k : ℕ) :
    ENNReal.ofReal (((k : ℝ) + 1) * (2 : ℝ) ^ (k + 1))
      = ((k : ℝ≥0∞) + 1) * (2 : ℝ≥0∞) ^ (k + 1) := by
  rw [ENNReal.ofReal_mul (by positivity)]
  congr 1 <;> simp [ENNReal.ofReal_add, ENNReal.ofReal_pow]

end aux

/-- **Two-term Leibniz bound for the `C^{k,α}` norm of a product.**  The `C^{k,α}` norm of
`x ↦ f x * g x` is bounded by `‖f‖_{0,α} ‖g‖_{k,α} + C ‖f‖_{k,α} ‖g‖_{k-1,α}` for some
constant `C > 0`; one may take `C = (k+1) * 2^{k+1}`. -/
theorem holderNorm_mul_le_two {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {k : ℕ} {α : ℝ} {f g : X → ℂ} {Ω : Set X}
    (hf : ContDiffOn ℝ (k : ℕ∞) f Ω) (hg : ContDiffOn ℝ (k : ℕ∞) g Ω)
    (hΩ : UniqueDiffOn ℝ Ω)
    (hf' : Work.CR.Flat.holderNorm k α f Ω ≠ ⊤) (hg' : Work.CR.Flat.holderNorm k α g Ω ≠ ⊤) :
    ∃ C : ℝ, 0 < C ∧
      Work.CR.Flat.holderNorm k α (fun x => f x * g x) Ω
        ≤ Work.CR.Flat.holderNorm 0 α f Ω * Work.CR.Flat.holderNorm k α g Ω
          + ENNReal.ofReal C * (Work.CR.Flat.holderNorm k α f Ω
              * Work.CR.Flat.holderNorm (k - 1) α g Ω) := by
  refine ⟨((k : ℝ) + 1) * (2 : ℝ) ^ (k + 1), by positivity, ?_⟩
  have h0f : holderNorm 0 α f Ω = iDN 0 f Ω + hSN 0 α f Ω := holderNorm_zero_eq α f Ω
  have hkg : holderNorm k α g Ω = ∑ i ∈ Finset.range (k + 1), (iDN i g Ω + hSN i α g Ω) := rfl
  have hsum2 : (∑ i ∈ Finset.range (k + 1), (2 : ℝ≥0∞) ^ i)
      ≤ ENNReal.ofReal (((k : ℝ) + 1) * (2 : ℝ) ^ (k + 1)) := by
    rw [ofReal_const_eq]
    exact sum_pow_two_le k
  rw [show holderNorm k α (fun x => f x * g x) Ω
      = ∑ i ∈ Finset.range (k + 1),
          (iDN i (fun x => f x * g x) Ω + hSN i α (fun x => f x * g x) Ω) from rfl]
  refine (Finset.sum_le_sum fun i hi =>
      iDN_add_hSN_mul_le_two (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)) hf hg hΩ).trans ?_
  rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.mul_sum, ← h0f, ← hkg]
  exact add_le_add le_rfl (mul_le_mul_left hsum2 _)

end Work.CR.Flat.Holder
