import Mathlib
import Submission.Work.EQ.DefsCore
import Submission.Work.EQ.FanTri.BranchCompDefs
import Submission.Work.EQ.FanTri.analytic_invBranch
import Submission.Work.EQ.FanTri.analytic_lipschitz_ball
import Submission.Work.EQ.FanTri.branchComp_axis
import Submission.Work.EQ.FanSep.axis_walk
import Submission.Work.EQ.FanSep.germ_lip
import Submission.Work.EQ.walk_bounds

namespace Work.EQ.FanTri

open Complex Filter _root_.Topology
open scoped Topology

noncomputable section

/-- The point `A₁ = (-1/2, 0)`, in the exact literal form used by `branchComp_lipschitz`. -/
def A1c : ℂ × ℂ := (((-1 / 2 : ℝ) : ℂ), (0 : ℂ))

/-- The radicand of `invBranch` at an axis point `Q = ((x:ℂ), 0)` is the real number
`(x + a/2)²`; it has positive real part as soon as `x ≠ -a/2`. -/
lemma radicand_axis (a x : ℝ) :
    (((((x : ℂ), (0 : ℂ)) : ℂ × ℂ).1 + ((a / 2 : ℝ) : ℂ)) ^ 2
      + (((x : ℂ), (0 : ℂ)) : ℂ × ℂ).2 ^ 2) = (((x + a / 2) ^ 2 : ℝ) : ℂ) := by
  have h1 : (((x : ℂ), (0 : ℂ)) : ℂ × ℂ).1 + ((a / 2 : ℝ) : ℂ) = ((x + a / 2 : ℝ) : ℂ) := by
    push_cast; ring
  rw [h1, show (((x : ℂ), (0 : ℂ)) : ℂ × ℂ).2 ^ 2 = (0 : ℂ) by simp]
  rw [add_zero]
  exact (Complex.ofReal_pow (x + a / 2) 2).symm

/-- **The inverse branch is Lipschitz on a ball around an axis point.**  For `x + a/2 ≠ 0` the
radicand at `Q = ((x:ℂ),0)` has positive real part, so `invBranch a s` is analytic (hence
Lipschitz) there. -/
theorem invBranch_lipschitz_axis {a : ℝ} (s : Bool) {x : ℝ} (hx : x + a / 2 ≠ 0) :
    ∃ ρ C : ℝ, 0 < ρ ∧ 0 ≤ C ∧ ∀ p q : ℂ × ℂ,
      ‖p - (((x : ℂ), (0 : ℂ)))‖ ≤ ρ → ‖q - (((x : ℂ), (0 : ℂ)))‖ ≤ ρ →
      ‖invBranch a s p - invBranch a s q‖ ≤ C * ‖p - q‖ := by
  have hpos : 0 < (((((x : ℂ), (0 : ℂ)) : ℂ × ℂ).1 + ((a / 2 : ℝ) : ℂ)) ^ 2
      + (((x : ℂ), (0 : ℂ)) : ℂ × ℂ).2 ^ 2).re := by
    rw [radicand_axis a x, Complex.ofReal_re]
    exact sq_pos_of_ne_zero hx
  obtain ⟨ρ, C, hρ, hC, hb⟩ :=
    analytic_lipschitz_ball (f := invBranch a s) (z := (((x : ℂ), (0 : ℂ)) : ℂ × ℂ))
      (analytic_invBranch (a := a) (s := s) (Q := ((x : ℂ), (0 : ℂ))) hpos)
  exact ⟨ρ, C, hρ, hC, hb⟩

/-- **A finite composition of inverse branches is Lipschitz near `A₁ = (-1/2,0)`.**  For every
word `w` the composition `Work.EQ.FanTri.branchComp a w` is holomorphic on a ball around `A₁`
(each `invBranch a s` is holomorphic where the radicand has positive real part, and the image of
`A₁` under the composition is an axis point where this holds), hence Lipschitz there. -/
theorem branchComp_lipschitz {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (w : List Bool) :
    ∃ ρ C : ℝ, 0 < ρ ∧ 0 ≤ C ∧ ∀ x y : ℂ × ℂ,
      ‖x - (((-1 / 2 : ℝ) : ℂ), (0 : ℂ))‖ ≤ ρ →
      ‖y - (((-1 / 2 : ℝ) : ℂ), (0 : ℂ))‖ ≤ ρ →
      ‖Work.EQ.FanTri.branchComp a w x - Work.EQ.FanTri.branchComp a w y‖ ≤ C * ‖x - y‖ := by
  have haux : ∀ w : List Bool, ∃ ρ C : ℝ, 0 < ρ ∧ 0 ≤ C ∧ ∀ x y : ℂ × ℂ,
      ‖x - A1c‖ ≤ ρ → ‖y - A1c‖ ≤ ρ →
      ‖branchComp a w x - branchComp a w y‖ ≤ C * ‖x - y‖ := by
    intro w
    induction w with
    | nil =>
        refine ⟨1, 1, one_pos, zero_le_one, ?_⟩
        intro x y _ _
        rw [branchComp_apply_nil]
        simp
    | cons c w' ih =>
        obtain ⟨ρ', C', hρ', hC', hlip'⟩ := ih
        obtain ⟨k, hk, hkne⟩ := branchComp_axis (a := a) ha0 ha1 w'
        obtain ⟨ρ'', C'', hρ'', hC'', hlip''⟩ := invBranch_lipschitz_axis (a := a) c hkne
        refine ⟨min ρ' (ρ'' / (C' + 1)), C'' * C', lt_min hρ' (div_pos hρ'' (by linarith)),
          mul_nonneg hC'' hC', ?_⟩
        intro x y hx hy
        have hx' : ‖x - A1c‖ ≤ ρ' := le_trans hx (min_le_left _ _)
        have hy' : ‖y - A1c‖ ≤ ρ' := le_trans hy (min_le_left _ _)
        have hxs : ‖x - A1c‖ ≤ ρ'' / (C' + 1) := le_trans hx (min_le_right _ _)
        have hys : ‖y - A1c‖ ≤ ρ'' / (C' + 1) := le_trans hy (min_le_right _ _)
        have hA : ‖A1c - A1c‖ ≤ ρ' := by rw [sub_self, norm_zero]; exact hρ'.le
        -- the centre `branchComp a w' A1c` is the axis point with index `k`
        have hcenter : ‖branchComp a w' x
            - ((((-1 / 2 + 2 * (k : ℝ) : ℝ) : ℂ)), (0 : ℂ))‖ ≤ ρ'' := by
          rw [← hk]
          calc ‖branchComp a w' x - branchComp a w' A1c‖ ≤ C' * ‖x - A1c‖ := hlip' x A1c hx' hA
            _ ≤ C' * (ρ'' / (C' + 1)) := mul_le_mul_of_nonneg_left hxs hC'
            _ ≤ ρ'' := by
                have h1 : C' / (C' + 1) ≤ 1 := by
                  rw [div_le_one (by linarith)]; linarith
                calc C' * (ρ'' / (C' + 1)) = (C' / (C' + 1)) * ρ'' := by ring
                  _ ≤ 1 * ρ'' := mul_le_mul_of_nonneg_right h1 hρ''.le
                  _ = ρ'' := by ring
        have hcentery : ‖branchComp a w' y
            - ((((-1 / 2 + 2 * (k : ℝ) : ℝ) : ℂ)), (0 : ℂ))‖ ≤ ρ'' := by
          rw [← hk]
          calc ‖branchComp a w' y - branchComp a w' A1c‖ ≤ C' * ‖y - A1c‖ := hlip' y A1c hy' hA
            _ ≤ C' * (ρ'' / (C' + 1)) := mul_le_mul_of_nonneg_left hys hC'
            _ ≤ ρ'' := by
                have h1 : C' / (C' + 1) ≤ 1 := by
                  rw [div_le_one (by linarith)]; linarith
                calc C' * (ρ'' / (C' + 1)) = (C' / (C' + 1)) * ρ'' := by ring
                  _ ≤ 1 * ρ'' := mul_le_mul_of_nonneg_right h1 hρ''.le
                  _ = ρ'' := by ring
        have hstep := hlip'' (branchComp a w' x) (branchComp a w' y) hcenter hcentery
        rw [branchComp_cons, branchComp_cons]
        calc ‖invBranch a c (branchComp a w' x) - invBranch a c (branchComp a w' y)‖
            ≤ C'' * ‖branchComp a w' x - branchComp a w' y‖ := hstep
          _ ≤ C'' * (C' * ‖x - y‖) := mul_le_mul_of_nonneg_left (hlip' x y hx' hy') hC''
          _ = (C'' * C') * ‖x - y‖ := by ring
  exact haux w

end

end Work.EQ.FanTri
