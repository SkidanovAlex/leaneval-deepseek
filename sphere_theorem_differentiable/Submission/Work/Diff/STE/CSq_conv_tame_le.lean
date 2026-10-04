import Mathlib
import Submission.Work.Diff.STE.Torus
import Submission.Work.Diff.STE.wt_sqrt_pow_le
import Submission.Work.Diff.STE.norm_conv_le
import Submission.Work.Diff.STE.l1_l2sq_conv_le

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# A *tame* (dimension-free) convolution estimate for the weighted `ℓ²` norm `CSq`

For coefficient families `c d : (ι → ℤ) → ℂ` on the dual lattice `ℤ^ι` and the weight
`wt k = ⟨k⟩² = 1 + Σᵢ kᵢ²`, this file proves that convolution
`(c ∗ d) k = Σ_l c l · d (k - l)` is controlled in the weighted `ℓ²` norm
`CSq s c = Σ_k ⟨k⟩^{2s} ‖c k‖²` by the `ℓ¹` norms and the two weighted `ℓ²` norms:

  `CSq s (c ∗ d) ≤ C · (‖c‖₁² · CSq s d + CSq s c · ‖d‖₁²)`,  `‖c‖₁ = l1 c = Σ_k ‖c k‖`.

Unlike the companion estimate `CSq_conv_le` (`Hˢ` is a convolution algebra for `card ι < 2 s`),
**no hypothesis on `card ι` appears here**: the two terms on the right are exactly the two ways of
distributing the `ℓ¹` norm and the weighted `ℓ²` norm between the two factors.  This is the "tame"
form of the estimate, valid in every dimension, which is why it is the one needed by the
short-time-existence argument.

## Proof

Write `u k = ‖c k‖`, `v k = ‖d k‖` and `W k = ⟨k⟩^s = (√(wt k))^s`.  The pointwise Peetre bound
`W k ≤ 2^{2s} (W l + W (k - l))` (`Work.Diff.STE.wt_sqrt_pow_le`) gives, after multiplying by
`u l · v (k - l) ≥ 0` and summing over `l`,

  `W k · (u ∗ v)(k) ≤ 2^{2s} ((W·u) ∗ v (k) + u ∗ (W·v)(k))`,

and both terms on the right are convolutions with one `ℓ¹` and one `ℓ²` factor
(`W·u` and `W·v` are in `ℓ²`, with sums `CSq s c` resp. `CSq s d`).  Young's inequality
`ℓ¹ ∗ ℓ² ⊆ ℓ²` for nonnegative real families on `ℤ^ι` bounds the `ℓ²`-norm² of each term, and
squaring the pointwise bound using `(x + y)² ≤ 2 (x² + y²)` turns this into

  `Σ_k ⟨k⟩^{2s} ((u ∗ v) k)² ≤ 2^{4s+1} (‖v‖₁² · CSq s c + ‖u‖₁² · CSq s d)`.

Since `‖conv c d k‖ ≤ (u ∗ v) k` (`Work.Diff.STE.norm_conv_le`), the same bound holds for
`CSq s (conv c d)`.

The Young inequality used below is the local lemma `young_l1_l2_local`; the public development
proves the same statement as `Work.Diff.STE.l1_l2sq_conv_le` / `Work.Diff.STE.young_l1_l2`.
-/

noncomputable section

open scoped BigOperators

namespace Work.Diff.STE

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ## Elementary helpers -/

/-- `((2 : ℝ)^n)^2 = 2^(2n)`. -/
private lemma sq_two_pow (n : ℕ) : ((2 : ℝ) ^ n) ^ 2 = 2 ^ (2 * n) := by
  rw [← pow_mul, Nat.mul_comm]

/-- `(√(wt k)^s)^2 = (wt k)^s`. -/
private lemma sqrt_wt_pow_sq (s : ℕ) (k : ι → ℤ) :
    ((Real.sqrt (wt k)) ^ s) ^ 2 = (wt k) ^ s := by
  rw [← pow_mul, Nat.mul_comm, pow_mul, Real.sq_sqrt (le_of_lt (wt_pos k))]

/-- Convolution is commutative (reindexing by `l ↦ k - l`). -/
private lemma tsum_conv_swap (u v : (ι → ℤ) → ℝ) (k : ι → ℤ) :
    (∑' l : ι → ℤ, u l * v (k - l)) = ∑' l : ι → ℤ, u (k - l) * v l := by
  rw [← Equiv.tsum_eq (Equiv.subLeft k) (fun l => u l * v (k - l))]
  refine tsum_congr fun l => ?_
  rw [Equiv.subLeft_apply]
  have : k - (k - l) = l := by abel
  rw [this]

/-- The two factors of a convolution may be interchanged (commutativity of multiplication
combined with the reindexing `l ↦ k - l`). -/
private lemma tsum_conv_comm (u v : (ι → ℤ) → ℝ) (k : ι → ℤ) :
    (∑' l : ι → ℤ, u l * v (k - l)) = ∑' l : ι → ℤ, v l * u (k - l) :=
  (tsum_congr fun l => mul_comm _ _).trans (tsum_conv_swap v u k).symm

/-- **Young's inequality** `ℓ¹ ∗ ℓ² ⊆ ℓ²` for nonnegative real families on `ℤ^ι`:
`‖a ∗ b‖₂² ≤ ‖a‖₁² ‖b‖₂²`.  This is the public lemma `Work.Diff.STE.l1_l2sq_conv_le`,
recalled here under a local name for readability of the argument below. -/
private lemma young_l1_l2_local (a b : (ι → ℤ) → ℝ)
    (ha : ∀ k, 0 ≤ a k) (hb : ∀ k, 0 ≤ b k)
    (ha' : Summable a) (hb' : Summable fun k => b k ^ 2) :
    Summable (fun k : ι → ℤ => (∑' l : ι → ℤ, a l * b (k - l)) ^ 2) ∧
      (∑' k : ι → ℤ, (∑' l : ι → ℤ, a l * b (k - l)) ^ 2)
        ≤ (∑' k : ι → ℤ, a k) ^ 2 * (∑' k : ι → ℤ, b k ^ 2) :=
  l1_l2sq_conv_le a b ha hb ha' hb'

/-! ## The heart: the weighted convolution bound -/

/-- For nonnegative real families `A, E : ℤ^ι → ℝ` with `A, E ∈ ℓ¹` and such that the weighted
families `(√(wt ·))^s A` and `(√(wt ·))^s E` are in `ℓ²`,

  `Σ_k (wt k)^s ((A ∗ E) k)²
     ≤ 2^{4s+1} (‖E‖₁² · Σ_k ((√(wt k))^s A k)² + ‖A‖₁² · Σ_k ((√(wt k))^s E k)²)`.

This is the analytic core of `CSq_conv_tame_le`: the Peetre splitting of the weight into an
`A`-part and an `E`-part, followed by Young's inequality on each of the two pieces. -/
private lemma conv_weighted_bound (s : ℕ) (A E : (ι → ℤ) → ℝ)
    (hA_nn : ∀ k, 0 ≤ A k) (hE_nn : ∀ k, 0 ≤ E k)
    (hA : Summable A) (hE : Summable E)
    (hF2 : Summable fun k => (Real.sqrt (wt k) ^ s * A k) ^ 2)
    (hG2 : Summable fun k => (Real.sqrt (wt k) ^ s * E k) ^ 2) :
    Summable (fun k : ι → ℤ => (wt k) ^ s * (∑' l : ι → ℤ, A l * E (k - l)) ^ 2) ∧
      (∑' k : ι → ℤ, (wt k) ^ s * (∑' l : ι → ℤ, A l * E (k - l)) ^ 2)
        ≤ 2 ^ (4 * s + 1) *
          ((∑' k, E k) ^ 2 * (∑' k, (Real.sqrt (wt k) ^ s * A k) ^ 2)
            + (∑' k, A k) ^ 2 * (∑' k, (Real.sqrt (wt k) ^ s * E k) ^ 2)) := by
  set F : (ι → ℤ) → ℝ := fun k => Real.sqrt (wt k) ^ s * A k with hF
  set G : (ι → ℤ) → ℝ := fun k => Real.sqrt (wt k) ^ s * E k with hG
  have hF2' : Summable fun k => F k ^ 2 := hF2.congr (fun k => by rw [hF])
  have hG2' : Summable fun k => G k ^ 2 := hG2.congr (fun k => by rw [hG])
  have hF_nn : ∀ k, 0 ≤ F k := fun k => by
    rw [hF]; exact mul_nonneg (pow_nonneg (Real.sqrt_nonneg _) _) (hA_nn k)
  have hG_nn : ∀ k, 0 ≤ G k := fun k => by
    rw [hG]; exact mul_nonneg (pow_nonneg (Real.sqrt_nonneg _) _) (hE_nn k)
  -- boundedness of the two ingredients that occur as weights
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
  -- the weighted summand identifies with `F l * E (k - l) + A l * G (k - l)`
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
  -- the pointwise key estimate (Peetre splitting)
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
            (fun l => (mul_le_mul_of_nonneg_right (wt_sqrt_pow_le s k l)
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
  -- the two `ℓ²` families are summable by Young, with the announced bounds
  have hFE2 : Summable fun k => (∑' l, F l * E (k - l)) ^ 2 := by
    have hswap : ∀ k, (∑' l, F l * E (k - l)) = ∑' l, E l * F (k - l) := fun k =>
      tsum_conv_comm F E k
    refine ((young_l1_l2_local E F hE_nn hF_nn hE hF2').1).congr (fun k => ?_)
    rw [hswap k]
  have hAG2 : Summable fun k => (∑' l, A l * G (k - l)) ^ 2 :=
    (young_l1_l2_local A G hA_nn hG_nn hA hG2').1
  have hFE2bound : (∑' k, (∑' l, F l * E (k - l)) ^ 2)
      ≤ (∑' k, E k) ^ 2 * (∑' k, F k ^ 2) := by
    have hswap : ∀ k, (∑' l, F l * E (k - l)) ^ 2 = (∑' l, E l * F (k - l)) ^ 2 :=
      fun k => by rw [tsum_conv_comm F E k]
    rw [tsum_congr hswap]
    exact (young_l1_l2_local E F hE_nn hF_nn hE hF2').2
  have hAG2bound : (∑' k, (∑' l, A l * G (k - l)) ^ 2)
      ≤ (∑' k, A k) ^ 2 * (∑' k, G k ^ 2) :=
    (young_l1_l2_local A G hA_nn hG_nn hA hG2').2
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
        refine mul_le_mul_of_nonneg_left (add_le_add hFE2bound hAG2bound) (by positivity)
    _ = 2 ^ (4 * s + 1) * ((∑' k, E k) ^ 2 * (∑' k, (Real.sqrt (wt k) ^ s * A k) ^ 2)
          + (∑' k, A k) ^ 2 * (∑' k, (Real.sqrt (wt k) ^ s * E k) ^ 2)) := by
        rw [hE2eq, hG2eq]

/-! ## The target estimate -/

theorem CSq_conv_tame_le {ι : Type*} [Fintype ι] [DecidableEq ι] (s : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ c d : (ι → ℤ) → ℂ,
      Summable (fun k : ι → ℤ => ‖c k‖) → Summable (fun k : ι → ℤ => ‖d k‖) →
      Summable (fun k : ι → ℤ => (Work.Diff.STE.wt k) ^ s * ‖c k‖ ^ 2) →
      Summable (fun k : ι → ℤ => (Work.Diff.STE.wt k) ^ s * ‖d k‖ ^ 2) →
      Summable (fun k : ι → ℤ => (Work.Diff.STE.wt k) ^ s * ‖Work.Diff.STE.conv c d k‖ ^ 2) ∧
      Work.Diff.STE.CSq s (Work.Diff.STE.conv c d)
        ≤ C * ((Work.Diff.STE.l1 c) ^ 2 * Work.Diff.STE.CSq s d
              + Work.Diff.STE.CSq s c * (Work.Diff.STE.l1 d) ^ 2) := by
  classical
  refine ⟨2 ^ (4 * s + 1), by positivity, ?_⟩
  intro c d hc hd hcs hds
  set u : (ι → ℤ) → ℝ := fun k => ‖c k‖ with hu
  set v : (ι → ℤ) → ℝ := fun k => ‖d k‖ with hv
  have hu_nn : ∀ k, 0 ≤ u k := fun k => norm_nonneg _
  have hv_nn : ∀ k, 0 ≤ v k := fun k => norm_nonneg _
  have hu_sum : Summable u := by rw [hu]; exact hc
  have hv_sum : Summable v := by rw [hv]; exact hd
  have hv2 : Summable (fun k => v k ^ 2) := by
    refine Summable.of_nonneg_of_le (fun k => sq_nonneg _)
      (fun k => ?_) (hv_sum.mul_left (∑' j, v j))
    have hbd := hv_sum.le_tsum k (fun j _ => hv_nn j)
    nlinarith [hv_nn k]
  -- the two weighted `ℓ²` summabilities
  have hF2 : Summable (fun k => (Real.sqrt (wt k) ^ s * u k) ^ 2) := by
    refine hcs.congr (fun k => ?_)
    rw [hu, mul_pow, sqrt_wt_pow_sq]
  have hG2 : Summable (fun k => (Real.sqrt (wt k) ^ s * v k) ^ 2) := by
    refine hds.congr (fun k => ?_)
    rw [hv, mul_pow, sqrt_wt_pow_sq]
  obtain ⟨hbound_sum, hbound⟩ :=
    conv_weighted_bound s u v hu_nn hv_nn hu_sum hv_sum hF2 hG2
  -- the triangle inequality for the convolution of the absolute values
  have hnorm : ∀ k : ι → ℤ, ‖conv c d k‖ ≤ ∑' l, u l * v (k - l) := fun k => by
    simpa only [hu, hv] using norm_conv_le c d hc hv2 k
  have hconv_sum : Summable (fun k : ι → ℤ => (wt k) ^ s * ‖conv c d k‖ ^ 2) :=
    Summable.of_nonneg_of_le
      (fun k => mul_nonneg (pow_nonneg (le_of_lt (wt_pos k)) s) (sq_nonneg _))
      (fun k => mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (hnorm k) 2)
        (pow_nonneg (le_of_lt (wt_pos k)) s)) hbound_sum
  refine ⟨hconv_sum, ?_⟩
  have hSumU : (∑' k, u k) = l1 c := by rw [hu]; rfl
  have hSumV : (∑' k, v k) = l1 d := by rw [hv]; rfl
  have hCSqc : (∑' k, (Real.sqrt (wt k) ^ s * u k) ^ 2) = CSq s c := by
    rw [hu, CSq]
    exact tsum_congr fun k => by rw [mul_pow, sqrt_wt_pow_sq]
  have hCSqd : (∑' k, (Real.sqrt (wt k) ^ s * v k) ^ 2) = CSq s d := by
    rw [hv, CSq]
    exact tsum_congr fun k => by rw [mul_pow, sqrt_wt_pow_sq]
  have hstep1 : CSq s (conv c d) ≤ ∑' k, (wt k) ^ s * (∑' l, u l * v (k - l)) ^ 2 := by
    rw [CSq]
    exact Summable.tsum_le_tsum
      (fun k => mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (hnorm k) 2)
        (pow_nonneg (le_of_lt (wt_pos k)) s)) hconv_sum hbound_sum
  calc CSq s (conv c d)
      ≤ ∑' k, (wt k) ^ s * (∑' l, u l * v (k - l)) ^ 2 := hstep1
    _ ≤ 2 ^ (4 * s + 1) * ((∑' k, v k) ^ 2 * (∑' k, (Real.sqrt (wt k) ^ s * u k) ^ 2)
          + (∑' k, u k) ^ 2 * (∑' k, (Real.sqrt (wt k) ^ s * v k) ^ 2)) := hbound
    _ = 2 ^ (4 * s + 1) * ((l1 d) ^ 2 * CSq s c + (l1 c) ^ 2 * CSq s d) := by
        rw [hSumU, hSumV, hCSqc, hCSqd]
    _ = 2 ^ (4 * s + 1) * ((l1 c) ^ 2 * CSq s d + CSq s c * (l1 d) ^ 2) := by ring

end Work.Diff.STE
