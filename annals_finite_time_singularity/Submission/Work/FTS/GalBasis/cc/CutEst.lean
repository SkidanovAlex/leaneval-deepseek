import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.GalBasis.cc.CutDefs
import Submission.Work.FTS.GalBasis.cc.SlotDefs
import Submission.Work.FTS.GalBasis.cc.ShrinkDefs
import Submission.Work.FTS.GalBasis.cc.CutSpec
import Submission.Work.FTS.EllipticEst.SmoothOpenAdd
import Submission.Work.FTS.OpenPkg.ProdOpen.leibniz_open_mixed
import Submission.Work.FTS.GalLimit.Closure.phi_HQo
import Submission.Work.FTS.Nonlinear.N4Fields.angmul_field_smooth
import Submission.Work.FTS.EllipticEst.EllHyp_certificates
import Submission.Work.FTS.EllipticEst.HkNorm_add_le
import Submission.Work.Spaces.HkSq_terms

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.GalBasis.cc

open Work.FTS.Galerkin (Fn)

attribute [local instance] Classical.propDecidable
set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

/-! ## Two elementary arithmetic lemmas -/

/-- `a²·b² ≤ K²·(c·H)` from `a² ≤ K²c`, `b² ≤ H`, `0 ≤ c`. -/
private lemma mul_sq_le {a b c H K : ℝ} (ha : a ^ 2 ≤ K ^ 2 * c) (hb : b ^ 2 ≤ H)
    (hc : 0 ≤ c) : a ^ 2 * b ^ 2 ≤ K ^ 2 * (c * H) := by
  calc a ^ 2 * b ^ 2 ≤ (K ^ 2 * c) * H :=
        mul_le_mul ha hb (sq_nonneg b) (mul_nonneg (sq_nonneg K) hc)
    _ = K ^ 2 * (c * H) := by ring

/-- `K²·A ≤ (K²+1)·(A+B)` for nonnegative `A`, `B`. -/
private lemma sq_mul_le_succ_mul_add {K A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hK : 0 ≤ K) :
    K ^ 2 * A ≤ (K ^ 2 + 1) * (A + B) := by
  have h1 : K ^ 2 * A ≤ (K ^ 2 + 1) * A :=
    mul_le_mul_of_nonneg_right (by linarith) hA
  have h2 : (K ^ 2 + 1) * A ≤ (K ^ 2 + 1) * (A + B) :=
    mul_le_mul_of_nonneg_left (le_add_of_nonneg_right hB) (by positivity)
  linarith

/-! ## The localised product bound

The Leibniz expansion `mulSlotRHS` of the `ℋ⁴`-integrand of `χ · f` is dominated by two explicit
localised quantities: the `ℋ⁴`-mass of `f` carried by the region `U` where the mixed derivatives
of `χ` can be non-zero, and the *wrong-weight* slots `D_z^b f · Wt α` (i.e. the `γ`-weighted
`D_z`-slots) carried by the angular layer `L` — the terms of the expansion in which every
`θ`-derivative falls on the multiplier. -/

theorem mulSlotRHS_le_localized {α : ℝ} {χ f : Fn} {K : ℝ} {U : Set (ℝ × ℝ)} {L : Set ℝ}
    (hK : 0 ≤ K)
    (hU : ∀ j i : ℕ, j + i ≤ 4 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Work.Spaces.mixed j i χ z θ ≠ 0 → (z, θ) ∈ U)
    (hL : ∀ j i : ℕ, 1 ≤ i → j + i ≤ 4 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Work.Spaces.mixed j i χ z θ ≠ 0 → θ ∈ L)
    (hbound : ∀ j i : ℕ, j + i ≤ 4 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      |Work.Spaces.mixed j i χ z θ| ≤ K)
    {z θ : ℝ} (hz : 0 < z) (hθ : 0 < θ) (hθ2 : θ < Real.pi / 2) :
    mulSlotRHS α χ f z θ ≤ 650 * (K ^ 2 + 1) *
      ((if (z, θ) ∈ U then (1 : ℝ) else 0) * Work.Spaces.HkIntegrand α 4 f z θ
        + (if θ ∈ L then (1 : ℝ) else 0) *
          ∑ b ∈ Finset.range 5, (zslotW α b f z θ) ^ 2) := by
  set A : ℝ := (if (z, θ) ∈ U then (1 : ℝ) else 0) * Work.Spaces.HkIntegrand α 4 f z θ
    with hAdef
  set B : ℝ := (if θ ∈ L then (1 : ℝ) else 0) *
    ∑ b ∈ Finset.range 5, (zslotW α b f z θ) ^ 2 with hBdef
  have hHnn : 0 ≤ Work.Spaces.HkIntegrand α 4 f z θ := Work.Spaces.HkIntegrand_nonneg α 4 f z θ
  have hcUnn : 0 ≤ (if (z, θ) ∈ U then (1 : ℝ) else 0) := by split_ifs <;> norm_num
  have hcLnn : 0 ≤ (if θ ∈ L then (1 : ℝ) else 0) := by split_ifs <;> norm_num
  have hSnn : 0 ≤ ∑ b ∈ Finset.range 5, (zslotW α b f z θ) ^ 2 :=
    Finset.sum_nonneg fun b _ => sq_nonneg _
  have hAnn : 0 ≤ A := by
    rw [hAdef]; exact mul_nonneg hcUnn hHnn
  have hBnn : 0 ≤ B := by
    rw [hBdef]; exact mul_nonneg hcLnn hSnn
  -- master bounds for the powers of the multiplier's mixed derivatives
  have hmulU : ∀ j i : ℕ, j + i ≤ 4 →
      (Work.Spaces.mixed j i χ z θ) ^ 2 ≤ K ^ 2 * (if (z, θ) ∈ U then (1 : ℝ) else 0) := by
    intro j i hji
    by_cases hzero : Work.Spaces.mixed j i χ z θ = 0
    · rw [hzero, show (0 : ℝ) ^ 2 = 0 by norm_num]
      exact mul_nonneg (sq_nonneg K) hcUnn
    · rw [if_pos (hU j i hji z θ hz hθ hθ2 hzero), mul_one]
      have hb := hbound j i hji z θ hz hθ hθ2
      have hK2 : K ^ 2 = |K| ^ 2 := (sq_abs K).symm
      rw [hK2, ← sq_abs (Work.Spaces.mixed j i χ z θ)]
      exact pow_le_pow_left₀ (abs_nonneg _) (by simpa only [abs_of_nonneg hK] using hb) 2
  have hmulL : ∀ j i : ℕ, 1 ≤ i → j + i ≤ 4 →
      (Work.Spaces.mixed j i χ z θ) ^ 2 ≤ K ^ 2 * (if θ ∈ L then (1 : ℝ) else 0) := by
    intro j i hi hji
    by_cases hzero : Work.Spaces.mixed j i χ z θ = 0
    · rw [hzero, show (0 : ℝ) ^ 2 = 0 by norm_num]
      exact mul_nonneg (sq_nonneg K) hcLnn
    · rw [if_pos (hL j i hi hji z θ hz hθ hθ2 hzero), mul_one]
      have hb := hbound j i hji z θ hz hθ hθ2
      have hK2 : K ^ 2 = |K| ^ 2 := (sq_abs K).symm
      rw [hK2, ← sq_abs (Work.Spaces.mixed j i χ z θ)]
      exact pow_le_pow_left₀ (abs_nonneg _) (by simpa only [abs_of_nonneg hK] using hb) 2
  -- the `D_z`-family terms
  have hS1 : ∀ j ∈ Finset.range 5, ∀ s ∈ Finset.range 5,
      (if s ≤ j then (Work.Spaces.mixed s 0 χ z θ) ^ 2 * (zslot (j - s) f z θ) ^ 2 else 0)
        ≤ (K ^ 2 + 1) * (A + B) := by
    intro j hj s hs
    by_cases hsle : s ≤ j
    · rw [if_pos hsle]
      have hjs : j - s ≤ 4 :=
        le_trans (Nat.sub_le j s) (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj))
      have hslot : (zslot (j - s) f z θ) ^ 2 ≤ Work.Spaces.HkIntegrand α 4 f z θ := by
        simpa only [zslot, pw] using Work.Spaces.sq_le_HkIntegrand_z α 4 f z θ (j - s) hjs
      have hs4 : s + 0 ≤ 4 := by
        have : s ≤ 4 := Nat.lt_succ_iff.mp (Finset.mem_range.mp hs); omega
      have hstep := mul_sq_le (hmulU s 0 hs4) hslot hcUnn
      refine le_trans hstep ?_
      rw [hAdef]
      exact sq_mul_le_succ_mul_add (mul_nonneg hcUnn hHnn) hBnn hK
    · rw [if_neg hsle]
      exact mul_nonneg (by positivity) (add_nonneg hAnn hBnn)
  -- the mixed terms
  have hS2 : ∀ i ∈ Finset.range 5, ∀ j ∈ Finset.range 5, ∀ a ∈ Finset.range 5,
      ∀ b ∈ Finset.range 5,
      (if 1 ≤ i ∧ i + j ≤ 4 ∧ a ≤ i ∧ b ≤ j then
        (Work.Spaces.mixed b a χ z θ) ^ 2 *
          (if 1 ≤ i - a then (mslot α (j - b) (i - a) f z θ) ^ 2
            else (zslotW α (j - b) f z θ) ^ 2)
        else 0) ≤ (K ^ 2 + 1) * (A + B) := by
    intro i hi j hj a ha b hb
    by_cases hg : 1 ≤ i ∧ i + j ≤ 4 ∧ a ≤ i ∧ b ≤ j
    · rw [if_pos hg]
      obtain ⟨hi1, hij, hai, hbj⟩ := hg
      have hsub : (i - a) + (j - b) ≤ 4 := by omega
      by_cases hia : 1 ≤ i - a
      · rw [if_pos hia]
        have hslot : (mslot α (j - b) (i - a) f z θ) ^ 2
            ≤ Work.Spaces.HkIntegrand α 4 f z θ := by
          simpa only [mslot] using
            Work.Spaces.sq_le_HkIntegrand_mixed α 4 f z θ (i - a) (j - b) hia hsub
        have hstep := mul_sq_le (hmulU b a (by omega)) hslot hcUnn
        refine le_trans hstep ?_
        rw [hAdef]
        exact sq_mul_le_succ_mul_add (mul_nonneg hcUnn hHnn) hBnn hK
      · rw [if_neg hia]
        have hi1a : 1 ≤ a := by omega
        have hslot : (zslotW α (j - b) f z θ) ^ 2
            ≤ ∑ b' ∈ Finset.range 5, (zslotW α b' f z θ) ^ 2 := by
          refine Finset.single_le_sum (f := fun b' => (zslotW α b' f z θ) ^ 2)
            (fun b' _ => sq_nonneg _) ?_
          exact Finset.mem_range.mpr (by omega)
        have hstep := mul_sq_le (hmulL b a hi1a (by omega)) hslot hcLnn
        refine le_trans hstep ?_
        rw [hBdef]
        exact le_trans (sq_mul_le_succ_mul_add (mul_nonneg hcLnn hSnn) hAnn hK)
          (le_of_eq (by ring))
    · rw [if_neg hg]
      exact mul_nonneg (by positivity) (add_nonneg hAnn hBnn)
  have hS1sum : (∑ j ∈ Finset.range 5, ∑ s ∈ Finset.range 5,
      (if s ≤ j then (Work.Spaces.mixed s 0 χ z θ) ^ 2 * (zslot (j - s) f z θ) ^ 2 else 0))
      ≤ 25 * ((K ^ 2 + 1) * (A + B)) := by
    refine le_trans (Finset.sum_le_sum fun j hj => Finset.sum_le_sum fun s hs =>
      hS1 j hj s hs) (le_of_eq ?_)
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_ofNat]
    ring
  have hS2sum : (∑ i ∈ Finset.range 5, ∑ j ∈ Finset.range 5, ∑ a ∈ Finset.range 5,
      ∑ b ∈ Finset.range 5,
      (if 1 ≤ i ∧ i + j ≤ 4 ∧ a ≤ i ∧ b ≤ j then
        (Work.Spaces.mixed b a χ z θ) ^ 2 *
          (if 1 ≤ i - a then (mslot α (j - b) (i - a) f z θ) ^ 2
            else (zslotW α (j - b) f z θ) ^ 2)
        else 0)) ≤ 625 * ((K ^ 2 + 1) * (A + B)) := by
    refine le_trans (Finset.sum_le_sum fun i hi => Finset.sum_le_sum fun j hj =>
      Finset.sum_le_sum fun a ha => Finset.sum_le_sum fun b hb => hS2 i hi j hj a ha b hb) (le_of_eq ?_)
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_ofNat]
    ring
  have hmain : mulSlotRHS α χ f z θ
      ≤ 25 * ((K ^ 2 + 1) * (A + B)) + 625 * ((K ^ 2 + 1) * (A + B)) := by
    rw [mulSlotRHS]
    exact add_le_add hS1sum hS2sum
  refine le_trans hmain (le_of_eq ?_)
  rw [hAdef, hBdef]
  ring

end Work.FTS.GalBasis.cc
