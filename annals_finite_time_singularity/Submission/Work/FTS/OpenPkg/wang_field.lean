/-
# `OpenPkg/wang_field` — multiplication by a function of `θ` alone, in the `D`-sup norms

This is the `wang` field of `Work.FTS.OpenPkg.N4Norm'` for the `D`-sup norms `WDp 4`/`WDMem 4`:
the open-quadrant Leibniz rule `Work.FTS.OpenPkg.ProdOpen.leibniz_open_mixed` collapses for a
factor which is constant in `z` (all terms with at least one radial derivative on that factor
vanish), and the remaining single sum is bounded by the hypotheses on the profile
`|a θ| ≤ Ca`, `|D_θ^i a| ≤ Ca·sin(2θ)` — the two hypotheses that exclude the spike families which
refute the un-hypothesised form (see `NOTES_wang_field_false.md` upstream).

The migrated analogue of `Work.FTS.Nonlinear.N4Fields.wang_field_smoothInt`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.OpenPkg.Defs
import Submission.Work.FTS.OpenPkg.Basic
import Submission.Work.FTS.OpenPkg.MulHelpers
import Submission.Work.FTS.OpenPkg.WDp_le_of_pointwise
import Submission.Work.FTS.OpenPkg.ProdOpen.leibniz_open_mixed

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

/-- The iterated angular operator applied to a function which is constant in `z` does not depend
on `z` (the derivatives are taken of literally the same angular function). -/
theorem DthIter_const_z_eq (a : ℝ → ℝ) :
    ∀ (i : ℕ) (z z' θ : ℝ),
      Work.Spaces.DthIter i (fun _ θ' => a θ') z θ
        = Work.Spaces.DthIter i (fun _ θ' => a θ') z' θ := by
  intro i
  induction i with
  | zero => intro z z' θ; rfl
  | succ i ih =>
    intro z z' θ
    change Work.Spaces.Dth (Work.Spaces.DthIter i (fun _ θ' => a θ')) z θ
      = Work.Spaces.Dth (Work.Spaces.DthIter i (fun _ θ' => a θ')) z' θ
    rw [show Work.Spaces.Dth (Work.Spaces.DthIter i (fun _ θ' => a θ')) z θ
        = Real.sin (2 * θ) * deriv (fun θ' =>
            Work.Spaces.DthIter i (fun _ θ'' => a θ'') z θ') θ from rfl,
      show Work.Spaces.Dth (Work.Spaces.DthIter i (fun _ θ' => a θ')) z' θ
        = Real.sin (2 * θ) * deriv (fun θ' =>
            Work.Spaces.DthIter i (fun _ θ'' => a θ'') z' θ') θ from rfl]
    have hfun : (fun θ' => Work.Spaces.DthIter i (fun _ θ'' => a θ'') z θ')
        = fun θ' => Work.Spaces.DthIter i (fun _ θ'' => a θ'') z' θ' := by
      funext θ'
      exact ih z z' θ'
    rw [hfun]

/-- **Multiplication by an angular profile in the `D`-sup norm.** -/
theorem wang_field :
    ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ), 0 < α → α ≤ 1 →
      ∀ (a : ℝ → ℝ) (h : Fn) (Ca : ℝ),
      Work.FTS.EllipticEst.SmoothOpen (fun _ (θ : ℝ) => a θ) →
      Work.FTS.EllipticEst.SmoothOpen h →
      (∀ θ ∈ Work.Spaces.Iθ, |a θ| ≤ Ca) →
      (∀ i : ℕ, 1 ≤ i → i ≤ 4 → ∀ θ ∈ Work.Spaces.Iθ,
        |Work.Spaces.DthIter i (fun _ (θ' : ℝ) => a θ') 0 θ| ≤ Ca * Real.sin (2 * θ)) →
      WDMem 4 h →
      WDMem 4 (fun z θ => a θ * h z θ) ∧
      WDp 4 (fun z θ => a θ * h z θ) ≤ C * Ca * WDp 4 h := by
  refine ⟨400, by norm_num, ?_⟩
  intro α hα hα1 a h Ca hasm hhsm hab hdab hm
  have hCa : 0 ≤ Ca := by
    have h0 : (0 : ℝ) ∈ Work.Spaces.Iθ := by
      rw [Work.Spaces.Iθ]; exact ⟨le_rfl, by linarith [Real.pi_pos]⟩
    exact le_trans (abs_nonneg _) (hab 0 h0)
  have hhnn : 0 ≤ WDp 4 h := WDp_nonneg 4 h
  have hMnn : 0 ≤ 16 * (Ca * WDp 4 h) := mul_nonneg (by norm_num) (mul_nonneg hCa hhnn)
  have hbound : ∀ b j : ℕ, b + j ≤ 4 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 →
      |Work.Spaces.mixed b j (fun z θ => a θ * h z θ) z θ| ≤ 16 * (Ca * WDp 4 h) := by
    intro b j hbj z θ hz hθ0 hθ1
    have hLeib : Work.Spaces.mixed b j (fun z θ => a θ * h z θ) z θ
        = ∑ u ∈ Finset.range (j + 1), ∑ c ∈ Finset.range (b + 1),
            ((j.choose u : ℝ) * (b.choose c : ℝ))
              * (Work.Spaces.mixed c u (fun _ θ' => a θ') z θ
                * Work.Spaces.mixed (b - c) (j - u) h z θ) :=
      ProdOpen.leibniz_open_mixed b j (fun _ θ' => a θ') h hasm hhsm z θ hz hθ0 hθ1
    rw [hLeib]
    refine le_trans (Finset.abs_sum_le_sum_abs
      (fun u => ∑ c ∈ Finset.range (b + 1), (j.choose u : ℝ) * (b.choose c : ℝ)
        * (Work.Spaces.mixed c u (fun _ θ' => a θ') z θ
          * Work.Spaces.mixed (b - c) (j - u) h z θ)) (Finset.range (j + 1))) ?_
    have hstep : ∀ u ∈ Finset.range (j + 1),
        |∑ c ∈ Finset.range (b + 1), (j.choose u : ℝ) * (b.choose c : ℝ)
            * (Work.Spaces.mixed c u (fun _ θ' => a θ') z θ
              * Work.Spaces.mixed (b - c) (j - u) h z θ)|
          ≤ ∑ c ∈ Finset.range (b + 1), (j.choose u : ℝ) * (b.choose c : ℝ)
              * (Ca * WDp 4 h) := by
      intro u hu
      refine le_trans (Finset.abs_sum_le_sum_abs
        (fun c => (j.choose u : ℝ) * (b.choose c : ℝ)
          * (Work.Spaces.mixed c u (fun _ θ' => a θ') z θ
            * Work.Spaces.mixed (b - c) (j - u) h z θ)) (Finset.range (b + 1))) ?_
      refine Finset.sum_le_sum fun c hc => ?_
      have huj : u ≤ j := Nat.le_of_lt_succ (Finset.mem_range.mp hu)
      have hcb : c ≤ b := Nat.le_of_lt_succ (Finset.mem_range.mp hc)
      have hcn : (0 : ℝ) ≤ (b.choose c : ℝ) := Nat.cast_nonneg _
      have hun : (0 : ℝ) ≤ (j.choose u : ℝ) := Nat.cast_nonneg _
      have h1 : |Work.Spaces.mixed c u (fun _ θ' => a θ') z θ| ≤ Ca := by
        rcases Nat.eq_zero_or_pos c with hc0 | hcpos
        · subst hc0
          simp only [Work.Spaces.mixed, Work.Spaces.DzIter_zero]
          rcases Nat.eq_zero_or_pos u with hu0 | hupos
          · subst hu0
            exact hab θ ⟨le_of_lt hθ0, le_of_lt hθ1⟩
          · have hz0 : Work.Spaces.DthIter u (fun _ θ' => a θ') z θ
                = Work.Spaces.DthIter u (fun _ θ' => a θ') 0 θ :=
              DthIter_const_z_eq a u z 0 θ
            rw [hz0]
            refine le_trans (hdab u hupos (by omega) θ ⟨le_of_lt hθ0, le_of_lt hθ1⟩) ?_
            have hsin1 : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
            nlinarith [hCa, hsin1]
        · have hzero : Work.Spaces.mixed c u (fun _ θ' => a θ') z θ = 0 := by
            have hD := DzIter_eq_zero_of_z_const
              (F := Work.Spaces.DthIter u (fun _ θ' => a θ'))
              (fun z θ => DthIter_const_z_eq a u z 0 θ) c hcpos
            simp only [Work.Spaces.mixed]
            rw [hD]
          rw [hzero, abs_zero]
          exact hCa
      have h2 : |Work.Spaces.mixed (b - c) (j - u) h z θ| ≤ WDp 4 h :=
        mixed_le_WDp hm (by omega) hz hθ0 hθ1
      rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg hun, abs_of_nonneg hcn]
      calc (j.choose u : ℝ) * (b.choose c : ℝ)
            * (|Work.Spaces.mixed c u (fun _ θ' => a θ') z θ|
              * |Work.Spaces.mixed (b - c) (j - u) h z θ|)
          = (j.choose u : ℝ) * ((b.choose c : ℝ)
              * (|Work.Spaces.mixed c u (fun _ θ' => a θ') z θ|
                * |Work.Spaces.mixed (b - c) (j - u) h z θ|)) := by ring
        _ ≤ (j.choose u : ℝ) * ((b.choose c : ℝ) * (Ca * WDp 4 h)) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
              (mul_le_mul h1 h2 (abs_nonneg _) hCa) hcn) hun
        _ = (j.choose u : ℝ) * (b.choose c : ℝ) * (Ca * WDp 4 h) := by ring
    refine le_trans (Finset.sum_le_sum hstep) ?_
    have hswap : ((∑ u ∈ Finset.range (j + 1), (j.choose u : ℝ))
            * (∑ c ∈ Finset.range (b + 1), (b.choose c : ℝ)))
          * (Ca * WDp 4 h)
        = ∑ u ∈ Finset.range (j + 1), ∑ c ∈ Finset.range (b + 1),
            (j.choose u : ℝ) * (b.choose c : ℝ) * (Ca * WDp 4 h) := by
      rw [Finset.sum_mul_sum]
      simp only [Finset.sum_mul]
    rw [← hswap]
    have hchoose_j : (∑ u ∈ Finset.range (j + 1), (j.choose u : ℝ)) = 2 ^ j := by
      exact_mod_cast Nat.sum_range_choose j
    have hchoose_b : (∑ c ∈ Finset.range (b + 1), (b.choose c : ℝ)) = 2 ^ b := by
      exact_mod_cast Nat.sum_range_choose b
    rw [hchoose_j, hchoose_b, ← pow_add]
    have hpow : (2 : ℝ) ^ (j + b) ≤ 16 := by
      have hjb : j + b ≤ 4 := by omega
      calc (2 : ℝ) ^ (j + b) ≤ 2 ^ 4 := pow_le_pow_right₀ (by norm_num) hjb
        _ = 16 := by norm_num
    nlinarith [hCa, hhnn, hpow, mul_nonneg hCa hhnn]
  constructor
  · intro b j hbj
    exact ⟨16 * (Ca * WDp 4 h),
      fun z θ hz hθ0 hθ1 => hbound b j hbj z θ hz hθ0 hθ1⟩
  · refine le_trans (WDp_le_of_pointwise (α := α) hMnn
      (fun b j hbj z θ hz hθ0 hθ1 => hbound b j hbj z θ hz hθ0 hθ1)) ?_
    nlinarith [hCa, hhnn, mul_nonneg hCa hhnn]

end Work.FTS.OpenPkg
