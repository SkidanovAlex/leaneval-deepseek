import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.OpenPkg.Defs
import Submission.Work.FTS.OpenPkg.WDp_le_of_pointwise
import Submission.Work.FTS.OpenPkg.WtohWin.Assembly
import Submission.Work.FTS.StrongGlobal.Global
import Submission.Work.H2.WPQ.m_term_le_smoothQuad

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.OpenPkg

open Work.FTS.Nonlin
open Work.FTS.VocabO
open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option linter.unusedVariables false

/-- **Multiplication by a `z`-profile in the `D`-sup norm.** -/
theorem wrad_field :
    ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ), 0 < α → α ≤ 1 → ∀ (φ : ℝ → ℝ) (h : Fn),
      Work.FTS.EllipticEst.SmoothOpen (fun z _ => φ z) → Work.FTS.EllipticEst.SmoothOpen h →
      WDMem 4 (fun z _ => φ z) → WDMem 4 h →
      WDMem 4 (fun z θ => φ z * h z θ) ∧
      WDp 4 (fun z θ => φ z * h z θ) ≤ C * WDp 4 (fun z _ => φ z) * WDp 4 h := by
  refine ⟨400, by norm_num, ?_⟩
  intro α hα hα1 φ h hφ hh hφm hm
  have hΦnn : 0 ≤ WDp 4 (fun z _ => φ z) := WDp_nonneg 4 _
  have hhnn : 0 ≤ WDp 4 h := WDp_nonneg 4 h
  have hMnn : 0 ≤ 16 * (WDp 4 (fun z _ => φ z) * WDp 4 h) :=
    mul_nonneg (by norm_num) (mul_nonneg hΦnn hhnn)
  have hbound : ∀ b j : ℕ, b + j ≤ 4 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 →
      |Work.Spaces.mixed b j (fun z θ => φ z * h z θ) z θ|
        ≤ 16 * (WDp 4 (fun z _ => φ z) * WDp 4 h) := by
    intro b j hbj z θ hz hθ0 hθ1
    have hLeib : Work.Spaces.mixed b j (fun z θ => φ z * h z θ) z θ
        = ∑ a ∈ Finset.range (j + 1), ∑ c ∈ Finset.range (b + 1),
            ((j.choose a : ℝ) * (b.choose c : ℝ))
              * (Work.Spaces.mixed c a (fun z _ => φ z) z θ
                * Work.Spaces.mixed (b - c) (j - a) h z θ) :=
      ProdOpen.leibniz_open_mixed b j (fun z _ => φ z) h hφ hh z θ hz hθ0 hθ1
    rw [hLeib]
    refine le_trans (Finset.abs_sum_le_sum_abs
      (fun a => ∑ c ∈ Finset.range (b + 1), (j.choose a : ℝ) * (b.choose c : ℝ)
        * (Work.Spaces.mixed c a (fun z _ => φ z) z θ
          * Work.Spaces.mixed (b - c) (j - a) h z θ)) (Finset.range (j + 1))) ?_
    have hstep : ∀ a ∈ Finset.range (j + 1),
        |∑ c ∈ Finset.range (b + 1), (j.choose a : ℝ) * (b.choose c : ℝ)
            * (Work.Spaces.mixed c a (fun z _ => φ z) z θ
              * Work.Spaces.mixed (b - c) (j - a) h z θ)|
          ≤ ∑ c ∈ Finset.range (b + 1), (j.choose a : ℝ) * (b.choose c : ℝ)
              * (WDp 4 (fun z _ => φ z) * WDp 4 h) := by
      intro a ha
      refine le_trans (Finset.abs_sum_le_sum_abs
        (fun c => (j.choose a : ℝ) * (b.choose c : ℝ)
          * (Work.Spaces.mixed c a (fun z _ => φ z) z θ
            * Work.Spaces.mixed (b - c) (j - a) h z θ)) (Finset.range (b + 1))) ?_
      refine Finset.sum_le_sum fun c hc => ?_
      have haj : a ≤ j := Nat.le_of_lt_succ (Finset.mem_range.mp ha)
      have hcb : c ≤ b := Nat.le_of_lt_succ (Finset.mem_range.mp hc)
      have hcn : (0 : ℝ) ≤ (b.choose c : ℝ) := Nat.cast_nonneg _
      have han : (0 : ℝ) ≤ (j.choose a : ℝ) := Nat.cast_nonneg _
      have h1 : |Work.Spaces.mixed c a (fun z _ => φ z) z θ| ≤ WDp 4 (fun z _ => φ z) := by
        rcases Nat.eq_zero_or_pos a with ha0 | hapos
        · subst ha0
          exact mixed_le_WDp hφm (b := c) (j := 0) (z := z) (θ := θ) (by omega) hz hθ0 hθ1
        · have hzero : Work.Spaces.mixed c a (fun z _ => φ z) z θ = 0 := by
            have hD := DthIter_const_theta φ a hapos
            simp only [Work.Spaces.mixed]
            rw [hD, DzIter_zero_fun]
          rw [hzero, abs_zero]
          exact hΦnn
      have h2 : |Work.Spaces.mixed (b - c) (j - a) h z θ| ≤ WDp 4 h :=
        mixed_le_WDp hm (by omega) hz hθ0 hθ1
      rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg han, abs_of_nonneg hcn]
      have hmain : |Work.Spaces.mixed c a (fun z _ => φ z) z θ|
            * |Work.Spaces.mixed (b - c) (j - a) h z θ|
          ≤ WDp 4 (fun z _ => φ z) * WDp 4 h :=
        mul_le_mul h1 h2 (abs_nonneg _) hΦnn
      calc (j.choose a : ℝ) * (b.choose c : ℝ)
            * (|Work.Spaces.mixed c a (fun z _ => φ z) z θ|
              * |Work.Spaces.mixed (b - c) (j - a) h z θ|)
          = (j.choose a : ℝ) * ((b.choose c : ℝ)
              * (|Work.Spaces.mixed c a (fun z _ => φ z) z θ|
                * |Work.Spaces.mixed (b - c) (j - a) h z θ|)) := by ring
        _ ≤ (j.choose a : ℝ) * ((b.choose c : ℝ)
              * (WDp 4 (fun z _ => φ z) * WDp 4 h)) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hmain hcn) han
        _ = (j.choose a : ℝ) * (b.choose c : ℝ)
              * (WDp 4 (fun z _ => φ z) * WDp 4 h) := by ring
    refine le_trans (Finset.sum_le_sum hstep) ?_
    have hswap : ((∑ a ∈ Finset.range (j + 1), (j.choose a : ℝ))
            * (∑ c ∈ Finset.range (b + 1), (b.choose c : ℝ)))
          * (WDp 4 (fun z _ => φ z) * WDp 4 h)
        = ∑ a ∈ Finset.range (j + 1), ∑ c ∈ Finset.range (b + 1),
            (j.choose a : ℝ) * (b.choose c : ℝ) * (WDp 4 (fun z _ => φ z) * WDp 4 h) := by
      rw [Finset.sum_mul_sum]
      simp only [Finset.sum_mul]
    rw [← hswap]
    have hchoose_j : (∑ a ∈ Finset.range (j + 1), (j.choose a : ℝ)) = 2 ^ j := by
      exact_mod_cast Nat.sum_range_choose j
    have hchoose_b : (∑ c ∈ Finset.range (b + 1), (b.choose c : ℝ)) = 2 ^ b := by
      exact_mod_cast Nat.sum_range_choose b
    rw [hchoose_j, hchoose_b, ← pow_add]
    have hpow : (2 : ℝ) ^ (j + b) ≤ 16 := by
      have hjb : j + b ≤ 4 := by omega
      calc (2 : ℝ) ^ (j + b) ≤ 2 ^ 4 := pow_le_pow_right₀ (by norm_num) hjb
        _ = 16 := by norm_num
    nlinarith [hΦnn, hhnn, hpow, mul_nonneg hΦnn hhnn]
  constructor
  · intro b j hbj
    exact ⟨16 * (WDp 4 (fun z _ => φ z) * WDp 4 h),
      fun z θ hz hθ0 hθ1 => hbound b j hbj z θ hz hθ0 hθ1⟩
  · refine le_trans (WDp_le_of_pointwise (α := α) hMnn
      (fun b j hbj z θ hz hθ0 hθ1 => hbound b j hbj z θ hz hθ0 hθ1)) ?_
    nlinarith [hΦnn, hhnn, mul_nonneg hΦnn hhnn]

end Work.FTS.OpenPkg
