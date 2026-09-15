import Submission.Work.KvnDual
import Submission.Work.KvnEnergy
import Submission.Work.KvnPart

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-!
# The correlation lower bound of the Green–Tao §7 iterative step

Green–Tao Proposition 8.2 (= Proposition 7.2 of the published paper) derives the *energy
increment* from the non-Gowers-uniformity hypothesis `‖F_{K+1}‖_{U^{k-1}} > ε^{1/2^k}`.
The key estimate is

`|⟨(1 - 1_Ω)(f - 𝔼(f|B_K)), 𝒟F_{K+1}⟩| ≥ |G|·‖F_{K+1}‖^{2^d} - O(η) - O(ε)`

(Gowers–anti-uniformity, Lemma 7.3), together with the observation that `𝒟F_{K+1}` may be
replaced by its conditional expectation on `B_{K+1}` at a cost of `O(ε)`, because `B_{K+1}`
contains the level sets of `𝒟F_{K+1}` at resolution `ε`.

This file proves that lower bound in the abstract σ-algebra language.
-/

open Finset
open scoped BigOperators

namespace GTTrans

open Commons.Combinatorics.Transference
open FinSigma

/-- `|a| - |b| ≤ |a + b|` (the reverse triangle inequality in additive form). -/
lemma abs_sub_abs_le_abs_add (a b : ℝ) : |a| - |b| ≤ |a + b| := by
  have h := abs_add_le (a + b) (-b)
  rw [add_neg_cancel_right, abs_neg] at h
  linarith

/-- **Green–Tao Lemma 7.3, lower bound on the dual pairing after conditional expectation.**

Let `F` vanish on the exceptional set `Ω` and agree with the residual `f - 𝔼(f|P)` outside
`Ω' ⊇ Ω`; let `Q` be a partition refining the level sets of `Φ = 𝒟F` at resolution `ε`
(`hQcl`), and suppose `|Φ| ≤ M`.  Then

`N·γ - M·∑_{Ω'}|F| - ε·∑|F| ≤ |∑_{x ∉ Ω'}(f(x) - 𝔼(f|P)(x)) · 𝔼(Φ|Q)(x)|`

whenever `γ ≤ ‖F‖_{U^d}^{2^d}`. -/
theorem dual_corr_lower {p : ℕ} [Fact p.Prime] {d : ℕ} (hd : 1 ≤ d)
    (P Q : ZMod p → Finset (ZMod p)) (hQmem : ∀ x, x ∈ Q x)
    (Ω Ω' : Finset (ZMod p)) (hΩsub : Ω ⊆ Ω') (hΩ' : ∀ x ∈ Ω', Q x ⊆ Ω')
    (F f : ZMod p → ℝ) (hFx0 : ∀ x ∈ Ω, F x = 0)
    (hFxe : ∀ x, x ∉ Ω' → F x = f x - cE P f x)
    {M ε γ : ℝ} (hM : 0 ≤ M) (hε : 0 < ε)
    (hMb : ∀ x, |davg d F x| ≤ M)
    (hQcl : ∀ x y : ZMod p, y ∈ Q x → |davg d F y - davg d F x| ≤ ε)
    (hU : γ ≤ Unorm d F ^ (2 ^ d)) :
    (Fintype.card (ZMod p) : ℝ) * γ
      - M * (∑ y ∈ Ω', |F y|)
      - ε * (∑ y, |F y|)
      ≤ |∑ x ∈ Finset.univ \ Ω', (f x - cE P f x) * cE Q (davg d F) x| := by
  classical
  set Φ : ZMod p → ℝ := davg d F with hΦdef
  set hfun : ZMod p → ℝ := cE Q Φ with hhdef
  -- (0) `h` is close to `Φ`
  have hclose : ∀ x, x ∉ Ω' → |hfun x - Φ x| ≤ ε := by
    intro x _
    have hc := cE_abs_sub_le_of_bound (part := Q) hQmem Φ x ε (fun y hy => hQcl x y hy)
    simpa only [hhdef] using hc
  -- (1) the unweighted pairing equals `N·‖F‖^{2^d}`
  have huniv : ∑ x, F x * Φ x
      = (Fintype.card (ZMod p) : ℝ) * Unorm d F ^ (2 ^ d) := by
    rw [hΦdef]; exact dual_inner_unorm hd F
  -- (2) split off the exceptional set
  have hsplit : ∑ x ∈ Finset.univ \ Ω', F x * Φ x
      = (∑ x, F x * Φ x) - ∑ x ∈ Ω', F x * Φ x := by
    have h := Finset.sum_sdiff (f := fun x => F x * Φ x) (Finset.subset_univ Ω')
    linarith
  have hA : (Fintype.card (ZMod p) : ℝ) * γ - M * (∑ y ∈ Ω', |F y|)
      ≤ |∑ x ∈ Finset.univ \ Ω', F x * Φ x| := by
    have h2 : |∑ x ∈ Ω', F x * Φ x| ≤ M * ∑ x ∈ Ω', |F x| := by
      calc |∑ x ∈ Ω', F x * Φ x| ≤ ∑ x ∈ Ω', |F x * Φ x| := Finset.abs_sum_le_sum_abs _ _
        _ = ∑ x ∈ Ω', |F x| * |Φ x| := by simp_rw [abs_mul]
        _ ≤ ∑ x ∈ Ω', |F x| * M := by
            apply Finset.sum_le_sum
            intro x _
            exact mul_le_mul_of_nonneg_left (hMb x) (abs_nonneg _)
        _ = M * ∑ x ∈ Ω', |F x| := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro x _
            ring
    have h4 : (Fintype.card (ZMod p) : ℝ) * γ
        ≤ (Fintype.card (ZMod p) : ℝ) * Unorm d F ^ (2 ^ d) :=
      mul_le_mul_of_nonneg_left hU (by positivity)
    have h2' : ∑ x ∈ Ω', F x * Φ x ≤ M * ∑ x ∈ Ω', |F x| := (abs_le.mp h2).2
    have h4' : (Fintype.card (ZMod p) : ℝ) * γ ≤ ∑ x, F x * Φ x := by
      rw [huniv]; exact h4
    have h6 : (Fintype.card (ZMod p) : ℝ) * γ - M * ∑ x ∈ Ω', |F x|
        ≤ ∑ x ∈ Finset.univ \ Ω', F x * Φ x := by
      rw [hsplit]
      nlinarith [h2', h4']
    exact le_trans h6 (le_abs_self _)
  -- (3) replacing `Φ` by `h`
  have hB : |∑ x ∈ Finset.univ \ Ω', F x * (hfun x - Φ x)| ≤ ε * ∑ x, |F x| := by
    calc |∑ x ∈ Finset.univ \ Ω', F x * (hfun x - Φ x)|
        ≤ ∑ x ∈ Finset.univ \ Ω', |F x * (hfun x - Φ x)| := Finset.abs_sum_le_sum_abs _ _
      _ = ∑ x ∈ Finset.univ \ Ω', |F x| * |hfun x - Φ x| := by simp_rw [abs_mul]
      _ ≤ ∑ x ∈ Finset.univ \ Ω', |F x| * ε := by
          apply Finset.sum_le_sum
          intro x hx
          rw [Finset.mem_sdiff] at hx
          exact mul_le_mul_of_nonneg_left (hclose x hx.2) (abs_nonneg _)
      _ = ε * ∑ x ∈ Finset.univ \ Ω', |F x| := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro x _
          ring
      _ ≤ ε * ∑ x, |F x| := by
          apply mul_le_mul_of_nonneg_left _ hε.le
          exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.sdiff_subset)
            (fun x _ _ => abs_nonneg _)
  -- (4) combine
  have hsum_eq : ∑ x ∈ Finset.univ \ Ω', (f x - cE P f x) * hfun x
      = ∑ x ∈ Finset.univ \ Ω', F x * hfun x := by
    apply Finset.sum_congr rfl
    intro x hx
    rw [Finset.mem_sdiff] at hx
    rw [hFxe x hx.2]
  have hdecomp : ∑ x ∈ Finset.univ \ Ω', F x * hfun x
      = ∑ x ∈ Finset.univ \ Ω', F x * Φ x
        + ∑ x ∈ Finset.univ \ Ω', F x * (hfun x - Φ x) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro x _
    ring
  rw [hsum_eq, hdecomp]
  have htri : |∑ x ∈ Finset.univ \ Ω', F x * Φ x|
      - |∑ x ∈ Finset.univ \ Ω', F x * (hfun x - Φ x)|
      ≤ |∑ x ∈ Finset.univ \ Ω', F x * Φ x
          + ∑ x ∈ Finset.univ \ Ω', F x * (hfun x - Φ x)| :=
    abs_sub_abs_le_abs_add _ _
  linarith [htri, hA, hB]

end GTTrans
