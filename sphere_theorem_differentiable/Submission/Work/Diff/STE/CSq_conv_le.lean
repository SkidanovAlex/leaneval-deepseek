import Mathlib
import Submission.Work.Diff.STE.Torus
import Submission.Work.Diff.STE.wt_pow_le
import Submission.Work.Diff.STE.l1_le_sqrt_CSq
import Submission.Work.Diff.STE.conv_l2_sq_le
import Submission.Work.Diff.STE.norm_conv_le
import Submission.Work.Diff.STE.tsum_mul_sq_le
import Submission.Work.Diff.STE.summable_translate_conv
import Submission.Work.Diff.STE.summable_wt_zpow
import Submission.Work.Diff.STE.summable_norm_of_CSq

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# `Hˢ` is a convolution algebra on the Fourier lattice `ℤ^ι` (Layer A, estimate A6)

For `card ι < 2 s` the weighted `ℓ²` space of coefficient families
`CSq s c = Σ_k ⟨k⟩^{2s} ‖c k‖²` is closed under convolution
`(c ∗ d) k = Σ_l c l · d (k - l)`, with
`∃ C, CSq s (c ∗ d) ≤ C · CSq s c · CSq s d`
(and the convolution again has finite `CSq`).  This is estimate A6 of the short-time-existence
design (`REFS/NOTES_LEAD_P1_STE.md`): for `s > card ι / 2` the Sobolev space `Hˢ` is a Banach
algebra.

## Proof

The key point is that `ℓ¹(ℤ^ι) ⊇ Hˢ` for `card ι < 2 s` (`Work.Diff.STE.l1_le_sqrt_CSq`), so we
may use Young's inequality `ℓ¹ ∗ ℓ² ⊆ ℓ²` (`Work.Diff.STE.young_l1_l2`).  Concretely, with
`A k = ‖c k‖`, `E k = ‖d k‖` and `W k = ⟨k⟩^s = √(wt k)^s`, the pointwise Peetre-type bound

  `W k ≤ 2^{2s} (W l + W (k - l))`,   i.e.  `√(wt k) ≤ 2 (√(wt l) + √(wt (k-l)))`,

gives, after multiplying by `A l * E (k-l)` and summing over `l`,

  `W k · (A ∗ E)(k) ≤ 2^{2s} ((F ∗ E)(k) + (A ∗ G)(k))`,   `F = W·A`, `G = W·E`,

and both terms on the right are `ℓ²`-convolutions with one `ℓ¹` factor.  Summing the squares yields
the result with `C = 2^{4s+2} C₁²`, where `C₁` is the constant of `l1_le_sqrt_CSq`.
-/

noncomputable section

open scoped BigOperators

namespace Work.Diff.STE

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ## Elementary power inequalities -/

/-- `(x + y)^s ≤ 2^s (x^s + y^s)` for `x, y ≥ 0`. -/
private lemma add_pow_le_two (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (s : ℕ) :
    (x + y) ^ s ≤ 2 ^ s * (x ^ s + y ^ s) := by
  have hmax : (max x y) ^ s ≤ x ^ s + y ^ s := by
    rcases le_total x y with h | h
    · rw [max_eq_right h]; exact le_add_of_nonneg_left (pow_nonneg hx s)
    · rw [max_eq_left h]; exact le_add_of_nonneg_right (pow_nonneg hy s)
  have hle : x + y ≤ 2 * max x y := by
    have h1 : x ≤ max x y := le_max_left _ _
    have h2 : y ≤ max x y := le_max_right _ _
    linarith
  calc (x + y) ^ s ≤ (2 * max x y) ^ s := pow_le_pow_left₀ (by positivity) hle s
    _ = 2 ^ s * (max x y) ^ s := by rw [mul_pow]
    _ ≤ 2 ^ s * (x ^ s + y ^ s) := mul_le_mul_of_nonneg_left hmax (by positivity)

/-- `((2 : ℝ)^n)^2 = 2^{2n}`. -/
private lemma sq_two_pow (n : ℕ) : ((2 : ℝ) ^ n) ^ 2 = 2 ^ (2 * n) := by
  rw [← pow_mul, Nat.mul_comm]

/-- `(√(wt k)^s)^2 = (wt k)^s`. -/
private lemma sqrt_wt_pow_sq (s : ℕ) (k : ι → ℤ) :
    (Real.sqrt (wt k) ^ s) ^ 2 = (wt k) ^ s := by
  rw [← pow_mul, Nat.mul_comm, pow_mul, Real.sq_sqrt (le_of_lt (wt_pos k))]

/-! ## The Peetre-type weight inequality -/

/-- `wt k ≤ 2 (wt l + wt (k - l))`: the additive triangle inequality for the weight
`⟨k⟩² = 1 + Σ kᵢ²`, as opposed to the multiplicative `wt_le_two_mul`. -/
private lemma wt_le_two_add (k l : ι → ℤ) : wt k ≤ 2 * (wt l + wt (k - l)) := by
  have hcoord : ∀ i : ι,
      ((k i : ℤ) : ℝ) ^ 2 ≤ 2 * ((l i : ℝ) ^ 2 + (((k - l) i : ℤ) : ℝ) ^ 2) := by
    intro i
    have hkl : ((k - l) i : ℤ) = k i - l i := Pi.sub_apply k l i
    have hcast : (k i : ℝ) = (l i : ℝ) + (((k - l) i : ℤ) : ℝ) := by
      rw [hkl]; push_cast; ring
    rw [hcast]
    nlinarith [sq_nonneg ((l i : ℝ) - (((k - l) i : ℤ) : ℝ))]
  have hsum : ∑ i, ((k i : ℤ) : ℝ) ^ 2
      ≤ 2 * (∑ i, ((l i : ℤ) : ℝ) ^ 2) + 2 * (∑ i, (((k - l) i : ℤ) : ℝ) ^ 2) := by
    calc ∑ i, ((k i : ℤ) : ℝ) ^ 2
        ≤ ∑ i, (2 * ((l i : ℝ) ^ 2 + (((k - l) i : ℤ) : ℝ) ^ 2)) :=
          Finset.sum_le_sum fun i _ => hcoord i
      _ = ∑ i, (2 * ((l i : ℤ) : ℝ) ^ 2 + 2 * (((k - l) i : ℤ) : ℝ) ^ 2) :=
          Finset.sum_congr rfl fun i _ => by ring
      _ = (∑ i, 2 * ((l i : ℤ) : ℝ) ^ 2) + ∑ i, 2 * (((k - l) i : ℤ) : ℝ) ^ 2 :=
          Finset.sum_add_distrib
      _ = 2 * (∑ i, ((l i : ℤ) : ℝ) ^ 2) + 2 * (∑ i, (((k - l) i : ℤ) : ℝ) ^ 2) := by
          rw [Finset.mul_sum, Finset.mul_sum]
  simp only [wt]
  linarith

/-- The Peetre-type inequality `√(wt k) ≤ 2 (√(wt l) + √(wt (k-l)))`. -/
private lemma sqrt_wt_le (k l : ι → ℤ) :
    Real.sqrt (wt k) ≤ 2 * (Real.sqrt (wt l) + Real.sqrt (wt (k - l))) := by
  have hsq : (Real.sqrt (wt k)) ^ 2 ≤ (2 * (Real.sqrt (wt l) + Real.sqrt (wt (k - l)))) ^ 2 := by
    rw [Real.sq_sqrt (le_of_lt (wt_pos k)), mul_pow, add_sq]
    have h2 : wt k ≤ 2 * (wt l + wt (k - l)) := wt_le_two_add k l
    rw [Real.sq_sqrt (le_of_lt (wt_pos l)), Real.sq_sqrt (le_of_lt (wt_pos (k - l)))] at *
    nlinarith [sq_nonneg (Real.sqrt (wt l)), sq_nonneg (Real.sqrt (wt (k - l))),
      mul_nonneg (Real.sqrt_nonneg (wt l)) (Real.sqrt_nonneg (wt (k - l))),
      le_of_lt (wt_pos l), le_of_lt (wt_pos (k - l)), h2]
  have := Real.sqrt_le_sqrt hsq
  rw [Real.sqrt_sq_eq_abs, Real.sqrt_sq_eq_abs] at this
  rwa [abs_of_nonneg (Real.sqrt_nonneg _), abs_of_nonneg (by positivity)] at this

/-- `(√(wt k))^s ≤ 2^{2s} ((√(wt l))^s + (√(wt (k - l)))^s)`. -/
private lemma wt_sqrt_pow_le_aux (s : ℕ) (k l : ι → ℤ) :
    (Real.sqrt (wt k)) ^ s
      ≤ 2 ^ (2 * s) * ((Real.sqrt (wt l)) ^ s + (Real.sqrt (wt (k - l))) ^ s) := by
  calc (Real.sqrt (wt k)) ^ s
      ≤ (2 * (Real.sqrt (wt l) + Real.sqrt (wt (k - l)))) ^ s :=
        pow_le_pow_left₀ (Real.sqrt_nonneg _) (sqrt_wt_le k l) s
    _ = 2 ^ s * (Real.sqrt (wt l) + Real.sqrt (wt (k - l))) ^ s := by rw [mul_pow]
    _ ≤ 2 ^ s * (2 ^ s * ((Real.sqrt (wt l)) ^ s + (Real.sqrt (wt (k - l))) ^ s)) :=
        mul_le_mul_of_nonneg_left
          (add_pow_le_two _ _ (Real.sqrt_nonneg _) (Real.sqrt_nonneg _) s) (by positivity)
    _ = 2 ^ (2 * s) * ((Real.sqrt (wt l)) ^ s + (Real.sqrt (wt (k - l))) ^ s) := by
        rw [← mul_assoc, ← pow_add]; congr 2; omega

/-! ## Young's inequality `ℓ¹ ∗ ℓ² ⊆ ℓ²` for nonnegative families -/

/-- **Young's inequality** for nonnegative real families on `ℤ^ι`: `‖a ∗ b‖₂ ≤ ‖a‖₁ ‖b‖₂`. -/
private lemma young_l1_l2_aux (a b : (ι → ℤ) → ℝ)
    (ha : ∀ k, 0 ≤ a k) (hb : ∀ k, 0 ≤ b k)
    (ha' : Summable a) (hb' : Summable fun k => b k ^ 2) :
    Summable (fun k : ι → ℤ => (∑' l : ι → ℤ, a l * b (k - l)) ^ 2) ∧
      (∑' k : ι → ℤ, (∑' l : ι → ℤ, a l * b (k - l)) ^ 2)
        ≤ (∑' k : ι → ℤ, a k) ^ 2 * (∑' k : ι → ℤ, b k ^ 2) := by
  have hbdd : ∀ m, b m ^ 2 ≤ ∑' j, b j ^ 2 := fun m =>
    hb'.le_tsum m (fun j _ => sq_nonneg _)
  have hQl : ∀ k, Summable fun l => a l * b (k - l) ^ 2 := fun k =>
    Summable.of_nonneg_of_le (fun l => mul_nonneg (ha l) (sq_nonneg _))
      (fun l => mul_le_mul_of_nonneg_left (hbdd (k - l)) (ha l)) (ha'.mul_right _)
  have hkey : ∀ k, (∑' l, a l * b (k - l)) ^ 2
      ≤ (∑' m, a m) * (∑' l, a l * b (k - l) ^ 2) := fun k =>
    tsum_mul_sq_le a (fun l => b (k - l)) ha (fun l => hb (k - l)) ha' (hQl k)
  have hconv := summable_translate_conv a b ha hb ha' hb'
  have hmain : Summable (fun k => (∑' l, a l * b (k - l)) ^ 2) :=
    Summable.of_nonneg_of_le (fun k => sq_nonneg _) hkey (hconv.1.mul_left _)
  refine ⟨hmain, ?_⟩
  calc (∑' k, (∑' l, a l * b (k - l)) ^ 2)
      ≤ ∑' k, (∑' m, a m) * (∑' l, a l * b (k - l) ^ 2) :=
        Summable.tsum_le_tsum hkey hmain (hconv.1.mul_left _)
    _ = (∑' m, a m) * (∑' k, ∑' l, a l * b (k - l) ^ 2) :=
        Summable.tsum_mul_left _ hconv.1
    _ = (∑' m, a m) * ((∑' m, a m) * (∑' m, b m ^ 2)) := by rw [hconv.2]
    _ = (∑' m, a m) ^ 2 * (∑' m, b m ^ 2) := by ring

/-- Convolution is commutative (by the reindexing `l ↦ k - l`). -/
private lemma tsum_conv_swap (u v : (ι → ℤ) → ℝ) (k : ι → ℤ) :
    (∑' l : ι → ℤ, u l * v (k - l)) = ∑' l : ι → ℤ, u (k - l) * v l := by
  rw [← Equiv.tsum_eq (Equiv.subLeft k) (fun l => u l * v (k - l))]
  refine tsum_congr fun l => ?_
  rw [Equiv.subLeft_apply]
  have : k - (k - l) = l := by abel
  rw [this]

/-- **Young's inequality, reversed**: the `ℓ¹` factor may sit on the *right* of the convolution. -/
private lemma young_l1_l2_rev (a b : (ι → ℤ) → ℝ)
    (ha : ∀ k, 0 ≤ a k) (hb : ∀ k, 0 ≤ b k)
    (ha' : Summable a) (hb' : Summable fun k => b k ^ 2) :
    Summable (fun k : ι → ℤ => (∑' l : ι → ℤ, b l * a (k - l)) ^ 2) ∧
      (∑' k : ι → ℤ, (∑' l : ι → ℤ, b l * a (k - l)) ^ 2)
        ≤ (∑' k : ι → ℤ, a k) ^ 2 * (∑' k : ι → ℤ, b k ^ 2) := by
  have hswap : ∀ k, (∑' l, b l * a (k - l)) = ∑' l, a l * b (k - l) := by
    intro k
    rw [tsum_conv_swap b a k]
    exact tsum_congr fun l => by ring
  obtain ⟨h1, h2⟩ := young_l1_l2_aux a b ha hb ha' hb'
  refine ⟨h1.congr (fun k => by rw [hswap k]), ?_⟩
  simp only [hswap]
  exact h2

/-! ## The main convolution bound -/

/-- The heart of estimate A6.  For nonnegative `A, E : ℤ^ι → ℝ` with `A, E ∈ ℓ¹` and the weighted
families `⟨k⟩^s A k`, `⟨k⟩^s E k` in `ℓ²`,

  `Σ_k ⟨k⟩^{2s} ((A ∗ E) k)² ≤ 2^{4s+1} (‖E‖₁² ‖⟨·⟩^s A‖₂² + ‖A‖₁² ‖⟨·⟩^s E‖₂²)`. -/
private lemma conv_bound_aux (s : ℕ) (A E : (ι → ℤ) → ℝ)
    (hA_nn : ∀ k, 0 ≤ A k) (hE_nn : ∀ k, 0 ≤ E k)
    (hA : Summable A) (hE : Summable E)
    (hF2 : Summable fun k => (Real.sqrt (wt k) ^ s * A k) ^ 2)
    (hG2 : Summable fun k => (Real.sqrt (wt k) ^ s * E k) ^ 2) :
    Summable (fun k : ι → ℤ => (wt k) ^ s * (∑' l : ι → ℤ, A l * E (k - l)) ^ 2) ∧
      (∑' k : ι → ℤ, (wt k) ^ s * (∑' l : ι → ℤ, A l * E (k - l)) ^ 2)
        ≤ 2 ^ (4 * s + 1) *
          ((∑' k, E k) ^ 2 * (∑' k, (Real.sqrt (wt k) ^ s * A k) ^ 2)
            + (∑' k, A k) ^ 2 * (∑' k, (Real.sqrt (wt k) ^ s * E k) ^ 2)) := by
  -- name the weighted families
  set F : (ι → ℤ) → ℝ := fun k => Real.sqrt (wt k) ^ s * A k with hF
  set G : (ι → ℤ) → ℝ := fun k => Real.sqrt (wt k) ^ s * E k with hG
  have hF2' : Summable fun k => F k ^ 2 := hF2.congr (fun k => by rw [hF])
  have hG2' : Summable fun k => G k ^ 2 := hG2.congr (fun k => by rw [hG])
  have hF_nn : ∀ k, 0 ≤ F k := fun k => by
    rw [hF]; exact mul_nonneg (pow_nonneg (Real.sqrt_nonneg _) _) (hA_nn k)
  have hG_nn : ∀ k, 0 ≤ G k := fun k => by
    rw [hG]; exact mul_nonneg (pow_nonneg (Real.sqrt_nonneg _) _) (hE_nn k)
  -- boundedness
  have hE_bdd : ∀ k, E k ≤ ∑' j, E j := fun k => hE.le_tsum k (fun j _ => hE_nn j)
  have hF_bdd : ∀ k, F k ≤ Real.sqrt (∑' j, F j ^ 2) := fun k =>
    Real.le_sqrt_of_sq_le (hF2'.le_tsum k (fun j _ => sq_nonneg _))
  have hG_bdd : ∀ k, G k ≤ Real.sqrt (∑' j, G j ^ 2) := fun k =>
    Real.le_sqrt_of_sq_le (hG2'.le_tsum k (fun j _ => sq_nonneg _))
  have hEshift : ∀ k, Summable (fun l : ι → ℤ => E (k - l)) := fun k =>
    Summable.comp_injective hE (sub_right_injective (b := k))
  -- the three elementary pointwise sums
  have hAE : ∀ k, Summable (fun l => A l * E (k - l)) := fun k =>
    Summable.of_nonneg_of_le (fun l => mul_nonneg (hA_nn l) (hE_nn (k - l)))
      (fun l => mul_le_mul_of_nonneg_left (hE_bdd (k - l)) (hA_nn l)) (hA.mul_right _)
  have hFE : ∀ k, Summable (fun l => F l * E (k - l)) := fun k =>
    Summable.of_nonneg_of_le (fun l => mul_nonneg (hF_nn l) (hE_nn (k - l)))
      (fun l => mul_le_mul_of_nonneg_right (hF_bdd l) (hE_nn (k - l)))
      ((hEshift k).mul_left (Real.sqrt (∑' j, F j ^ 2)))
  have hAG : ∀ k, Summable (fun l => A l * G (k - l)) := fun k =>
    Summable.of_nonneg_of_le (fun l => mul_nonneg (hA_nn l) (hG_nn (k - l)))
      (fun l => mul_le_mul_of_nonneg_left (hG_bdd (k - l)) (hA_nn l)) (hA.mul_right _)
  -- the weighted summand identifies with `F l * E (k-l) + A l * G (k-l)`
  have hsummand : ∀ k, (fun l => (Real.sqrt (wt l) ^ s + Real.sqrt (wt (k - l)) ^ s)
        * (A l * E (k - l)))
      = fun l => F l * E (k - l) + A l * G (k - l) := by
    intro k; funext l
    rw [hF, hG]; ring
  have hWsum : ∀ k, Summable (fun l => (Real.sqrt (wt l) ^ s + Real.sqrt (wt (k - l)) ^ s)
      * (A l * E (k - l))) := by
    intro k
    rw [hsummand k]
    exact (hFE k).add (hAG k)
  -- the pointwise key estimate
  have hkey : ∀ k, Real.sqrt (wt k) ^ s * (∑' l, A l * E (k - l))
      ≤ 2 ^ (2 * s) * ((∑' l, F l * E (k - l)) + (∑' l, A l * G (k - l))) := by
    intro k
    have h1 : (∑' l, (Real.sqrt (wt l) ^ s + Real.sqrt (wt (k - l)) ^ s) * (A l * E (k - l)))
        = (∑' l, F l * E (k - l)) + (∑' l, A l * G (k - l)) := by
      rw [hsummand k, Summable.tsum_add (hFE k) (hAG k)]
    calc Real.sqrt (wt k) ^ s * (∑' l, A l * E (k - l))
        = ∑' l, Real.sqrt (wt k) ^ s * (A l * E (k - l)) :=
          (Summable.tsum_mul_left (Real.sqrt (wt k) ^ s) (hAE k)).symm
      _ ≤ ∑' l, 2 ^ (2 * s)
            * ((Real.sqrt (wt l) ^ s + Real.sqrt (wt (k - l)) ^ s) * (A l * E (k - l))) :=
          Summable.tsum_le_tsum
            (fun l => (mul_le_mul_of_nonneg_right (wt_sqrt_pow_le_aux s k l)
              (mul_nonneg (hA_nn l) (hE_nn (k - l)))).trans (le_of_eq (by ring)))
            ((hAE k).mul_left _) ((hWsum k).mul_left _)
      _ = 2 ^ (2 * s) * ((∑' l, F l * E (k - l)) + (∑' l, A l * G (k - l))) := by
          rw [Summable.tsum_mul_left (2 ^ (2 * s)) (hWsum k), h1]
  -- the pointwise squared estimate
  have hpt : ∀ k, (wt k) ^ s * (∑' l, A l * E (k - l)) ^ 2
      ≤ 2 ^ (4 * s + 1) * ((∑' l, F l * E (k - l)) ^ 2 + (∑' l, A l * G (k - l)) ^ 2) := by
    intro k
    have hAEnn : 0 ≤ ∑' l, A l * E (k - l) :=
      tsum_nonneg (fun l => mul_nonneg (hA_nn l) (hE_nn (k - l)))
    have hXY : ((∑' l, F l * E (k - l)) + (∑' l, A l * G (k - l))) ^ 2
        ≤ 2 * ((∑' l, F l * E (k - l)) ^ 2 + (∑' l, A l * G (k - l)) ^ 2) := by
      nlinarith [sq_nonneg ((∑' l, F l * E (k - l)) - (∑' l, A l * G (k - l)))]
    have hstep : (Real.sqrt (wt k) ^ s * (∑' l, A l * E (k - l))) ^ 2
        ≤ (2 ^ (2 * s) * ((∑' l, F l * E (k - l)) + (∑' l, A l * G (k - l)))) ^ 2 :=
      pow_le_pow_left₀ (mul_nonneg (pow_nonneg (Real.sqrt_nonneg _) s) hAEnn) (hkey k) 2
    rw [← sqrt_wt_pow_sq s k]
    calc (Real.sqrt (wt k) ^ s) ^ 2 * (∑' l, A l * E (k - l)) ^ 2
        = (Real.sqrt (wt k) ^ s * (∑' l, A l * E (k - l))) ^ 2 := by rw [mul_pow]
      _ ≤ (2 ^ (2 * s) * ((∑' l, F l * E (k - l)) + (∑' l, A l * G (k - l)))) ^ 2 := hstep
      _ = 2 ^ (4 * s) * ((∑' l, F l * E (k - l)) + (∑' l, A l * G (k - l))) ^ 2 := by
          rw [mul_pow, sq_two_pow, show 2 * (2 * s) = 4 * s by omega]
      _ ≤ 2 ^ (4 * s) * (2 * ((∑' l, F l * E (k - l)) ^ 2
            + (∑' l, A l * G (k - l)) ^ 2)) :=
          mul_le_mul_of_nonneg_left hXY (by positivity)
      _ = 2 ^ (4 * s + 1) * ((∑' l, F l * E (k - l)) ^ 2 + (∑' l, A l * G (k - l)) ^ 2) := by
          rw [pow_succ]; ring
  -- the two `ℓ²` families are summable by Young
  have hFE2 : Summable fun k => (∑' l, F l * E (k - l)) ^ 2 :=
    (young_l1_l2_rev E F hE_nn hF_nn hE hF2').1
  have hAG2 : Summable fun k => (∑' l, A l * G (k - l)) ^ 2 :=
    (young_l1_l2_aux A G hA_nn hG_nn hA hG2').1
  have hmajor : Summable fun k => 2 ^ (4 * s + 1)
      * ((∑' l, F l * E (k - l)) ^ 2 + (∑' l, A l * G (k - l)) ^ 2) :=
    (hFE2.add hAG2).mul_left _
  have hsumm : Summable fun k => (wt k) ^ s * (∑' l, A l * E (k - l)) ^ 2 :=
    Summable.of_nonneg_of_le
      (fun k => mul_nonneg (pow_nonneg (le_of_lt (wt_pos k)) s) (sq_nonneg _)) hpt hmajor
  refine ⟨hsumm, ?_⟩
  have hE2eq : (∑' k, F k ^ 2) = ∑' k, (Real.sqrt (wt k) ^ s * A k) ^ 2 :=
    tsum_congr (fun k => by rw [hF])
  have hG2eq : (∑' k, G k ^ 2) = ∑' k, (Real.sqrt (wt k) ^ s * E k) ^ 2 :=
    tsum_congr (fun k => by rw [hG])
  calc (∑' k, (wt k) ^ s * (∑' l, A l * E (k - l)) ^ 2)
      ≤ ∑' k, 2 ^ (4 * s + 1)
          * ((∑' l, F l * E (k - l)) ^ 2 + (∑' l, A l * G (k - l)) ^ 2) :=
        Summable.tsum_le_tsum hpt hsumm hmajor
    _ = 2 ^ (4 * s + 1) * ((∑' k, (∑' l, F l * E (k - l)) ^ 2)
          + (∑' k, (∑' l, A l * G (k - l)) ^ 2)) := by
        rw [Summable.tsum_mul_left (2 ^ (4 * s + 1)) (hFE2.add hAG2),
          Summable.tsum_add hFE2 hAG2]
    _ ≤ 2 ^ (4 * s + 1) * ((∑' k, E k) ^ 2 * (∑' k, F k ^ 2)
          + (∑' k, A k) ^ 2 * (∑' k, G k ^ 2)) := by
        refine mul_le_mul_of_nonneg_left (add_le_add ?_ ?_) (by positivity)
        · exact (young_l1_l2_rev E F hE_nn hF_nn hE hF2').2
        · exact (young_l1_l2_aux A G hA_nn hG_nn hA hG2').2
    _ = 2 ^ (4 * s + 1) * ((∑' k, E k) ^ 2 * (∑' k, (Real.sqrt (wt k) ^ s * A k) ^ 2)
          + (∑' k, A k) ^ 2 * (∑' k, (Real.sqrt (wt k) ^ s * E k) ^ 2)) := by
        rw [hE2eq, hG2eq]

/-- **Estimate A6** (`Hˢ` is a convolution algebra).  For `card ι < 2 s` the convolution of two
coefficient families with summable weighted `ℓ²`-norm again has summable weighted `ℓ²`-norm, and
`CSq s (conv c d) ≤ C · CSq s c · CSq s d`. -/
theorem CSq_conv_le {ι : Type*} [Fintype ι] [DecidableEq ι] (s : ℕ) (hs : Fintype.card ι < 2 * s) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ c d : (ι → ℤ) → ℂ,
      Summable (fun k : ι → ℤ => (Work.Diff.STE.wt k) ^ s * ‖c k‖ ^ 2) →
      Summable (fun k : ι → ℤ => (Work.Diff.STE.wt k) ^ s * ‖d k‖ ^ 2) →
      Summable (fun k : ι → ℤ => (Work.Diff.STE.wt k) ^ s * ‖Work.Diff.STE.conv c d k‖ ^ 2) ∧
      Work.Diff.STE.CSq s (Work.Diff.STE.conv c d)
        ≤ C * Work.Diff.STE.CSq s c * Work.Diff.STE.CSq s d := by
  obtain ⟨C₁, hC₁nn, hC₁⟩ := l1_le_sqrt_CSq (ι := ι) s hs
  refine ⟨2 ^ (4 * s + 1) * 2 * C₁ ^ 2, by positivity, ?_⟩
  intro c d hc hd
  -- `‖c‖, ‖d‖ ∈ ℓ¹` and `‖d‖ ∈ ℓ²`
  have ha : Summable (fun k => ‖c k‖) := summable_norm_of_CSq s hs c hc
  have he : Summable (fun k => ‖d k‖) := summable_norm_of_CSq s hs d hd
  have hd2 : Summable (fun k => ‖d k‖ ^ 2) :=
    Summable.of_nonneg_of_le (fun k => sq_nonneg _)
      (fun k => by
        have h1 : (1 : ℝ) ≤ (wt k) ^ s := one_le_pow₀ (wt_one_le k)
        calc ‖d k‖ ^ 2 = 1 * ‖d k‖ ^ 2 := by rw [one_mul]
          _ ≤ (wt k) ^ s * ‖d k‖ ^ 2 := mul_le_mul_of_nonneg_right h1 (sq_nonneg _))
      hd
  -- the weighted families are `ℓ²`
  have hF2 : Summable fun k => (Real.sqrt (wt k) ^ s * ‖c k‖) ^ 2 :=
    hc.congr (fun k => by rw [mul_pow, sqrt_wt_pow_sq])
  have hG2 : Summable fun k => (Real.sqrt (wt k) ^ s * ‖d k‖) ^ 2 :=
    hd.congr (fun k => by rw [mul_pow, sqrt_wt_pow_sq])
  -- apply the abstract bound
  obtain ⟨hsumm, hle⟩ := conv_bound_aux s (fun k => ‖c k‖) (fun k => ‖d k‖)
    (fun k => norm_nonneg _) (fun k => norm_nonneg _) ha he hF2 hG2
  -- make the `CSq`-norms appear
  have hsumc : (∑' k, (Real.sqrt (wt k) ^ s * ‖c k‖) ^ 2) = CSq s c :=
    tsum_congr (fun k => by rw [mul_pow, sqrt_wt_pow_sq])
  have hsumd : (∑' k, (Real.sqrt (wt k) ^ s * ‖d k‖) ^ 2) = CSq s d :=
    tsum_congr (fun k => by rw [mul_pow, sqrt_wt_pow_sq])
  rw [hsumc, hsumd] at hle
  -- summability of the target family, by comparison with the pointwise triangle bound
  have hsumm_conv : Summable fun k => (wt k) ^ s * ‖conv c d k‖ ^ 2 := by
    refine Summable.of_nonneg_of_le
      (fun k => mul_nonneg (pow_nonneg (le_of_lt (wt_pos k)) s) (sq_nonneg _)) (fun k => ?_) hsumm
    exact mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (norm_nonneg _) (norm_conv_le c d ha hd2 k) 2)
      (pow_nonneg (le_of_lt (wt_pos k)) s)
  refine ⟨hsumm_conv, ?_⟩
  -- the constant bookkeeping
  have hCsqc_nn : 0 ≤ CSq s c :=
    tsum_nonneg (fun k => mul_nonneg (pow_nonneg (le_of_lt (wt_pos k)) s) (sq_nonneg _))
  have hCsqd_nn : 0 ≤ CSq s d :=
    tsum_nonneg (fun k => mul_nonneg (pow_nonneg (le_of_lt (wt_pos k)) s) (sq_nonneg _))
  have hsqc : (∑' k, ‖c k‖) ^ 2 ≤ C₁ ^ 2 * CSq s c := by
    have h1 : (∑' k, ‖c k‖) ^ 2 ≤ (C₁ * Real.sqrt (CSq s c)) ^ 2 :=
      pow_le_pow_left₀ (tsum_nonneg (fun k => norm_nonneg _)) (hC₁ c hc) 2
    rwa [mul_pow, Real.sq_sqrt hCsqc_nn] at h1
  have hsqd : (∑' k, ‖d k‖) ^ 2 ≤ C₁ ^ 2 * CSq s d := by
    have h1 : (∑' k, ‖d k‖) ^ 2 ≤ (C₁ * Real.sqrt (CSq s d)) ^ 2 :=
      pow_le_pow_left₀ (tsum_nonneg (fun k => norm_nonneg _)) (hC₁ d hd) 2
    rwa [mul_pow, Real.sq_sqrt hCsqd_nn] at h1
  have htri : CSq s (conv c d)
      ≤ 2 ^ (4 * s + 1) * ((∑' k, ‖d k‖) ^ 2 * CSq s c + (∑' k, ‖c k‖) ^ 2 * CSq s d) := by
    rw [CSq]
    calc (∑' k, (wt k) ^ s * ‖conv c d k‖ ^ 2)
        ≤ ∑' k, (wt k) ^ s * (∑' l, ‖c l‖ * ‖d (k - l)‖) ^ 2 :=
          Summable.tsum_le_tsum
            (fun k => mul_le_mul_of_nonneg_left
              (pow_le_pow_left₀ (norm_nonneg _) (norm_conv_le c d ha hd2 k) 2)
              (pow_nonneg (le_of_lt (wt_pos k)) s)) hsumm_conv hsumm
      _ ≤ 2 ^ (4 * s + 1) * ((∑' k, ‖d k‖) ^ 2 * CSq s c + (∑' k, ‖c k‖) ^ 2 * CSq s d) := hle
  calc CSq s (conv c d)
      ≤ 2 ^ (4 * s + 1) * ((∑' k, ‖d k‖) ^ 2 * CSq s c + (∑' k, ‖c k‖) ^ 2 * CSq s d) := htri
    _ ≤ 2 ^ (4 * s + 1) * (C₁ ^ 2 * CSq s d * CSq s c + C₁ ^ 2 * CSq s c * CSq s d) := by
        refine mul_le_mul_of_nonneg_left (add_le_add ?_ ?_) (by positivity)
        · exact mul_le_mul_of_nonneg_right hsqd hCsqc_nn
        · exact mul_le_mul_of_nonneg_right hsqc hCsqd_nn
    _ = (2 ^ (4 * s + 1) * 2 * C₁ ^ 2) * CSq s c * CSq s d := by ring

end Work.Diff.STE
