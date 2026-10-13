import Mathlib
import Submission.Work.WilG4c.StepLipDefs
import Submission.Work.WilG4c.StepLipPieces
import Submission.Work.WilG4c.FLemAPI
import Submission.Work.WilG4c.ExactChartDeriv
import Submission.Work.WilG4c.YPullback

set_option autoImplicit false
noncomputable section
open Classical

namespace Work.WilG4c

open WilkiesDesign WilkiesDesign.CG

/-- Patching a family by a constant `c ∈ (0,1)` outside a parameter set preserves `YBound`
and `LipOnCube` (the `ValuesIn01` clause of `iteFamPYLipOn` is not needed here). -/
theorem iteFam_ybound_lip {p n k : ℕ} (Λ : Set (Fin p → ℝ))
    (F G : Work.WilkG4c.Family k p (n + 1)) (c : ℝ) (hc : c ∈ Set.Ioo (0 : ℝ) 1)
    (r : ℕ) (C : ℝ) (hC : 0 ≤ C)
    (hPY : ∀ i l, l ∈ Λ → ∀ x ∈ Work.WilkG4c.I, ∀ m, m ≤ r →
      ∀ y ∈ WilkiesDesign.openCube n,
      ‖iteratedFDeriv ℝ m (Work.WilkG4c.slice (F i l) x) y‖ ≤ 1)
    (hLip : ∀ i l, l ∈ Λ → ∀ z ∈ WilkiesDesign.openCube (n + 1),
      ∀ z' ∈ WilkiesDesign.openCube (n + 1), |F i l z - F i l z'| ≤ C * dist z z')
    (hG : ∀ i l t, l ∈ Λ → G i l t = F i l t)
    (hGc : ∀ i l t, l ∉ Λ → G i l t = c) :
    Work.WilkG4c.YBound G r ∧ Work.WilkG4c.LipOnCube G C := by
  have hc0 : (0 : ℝ) < c := hc.1
  refine ⟨?_, ?_⟩
  · intro i l x hx m hm y hy
    by_cases hl : l ∈ Λ
    · rw [show G i l = F i l from funext fun t => hG i l t hl]
      exact hPY i l hl x hx m hm y hy
    · rw [show Work.WilkG4c.slice (G i l) x = fun _ : Fin n → ℝ => c from
        funext fun y' => by
          simp only [Work.WilkG4c.slice_apply]
          exact hGc i l (Work.WilkG4c.pt x y') hl]
      cases m with
      | zero =>
          rw [norm_iteratedFDeriv_zero]
          show ‖c‖ ≤ 1
          rw [Real.norm_eq_abs, abs_of_pos hc0]
          linarith [hc.2]
      | succ m' =>
          rw [iteratedFDeriv_succ_const]
          simp
  · intro i l z z' hz hz'
    by_cases hl : l ∈ Λ
    · rw [show G i l = F i l from funext fun t => hG i l t hl]
      exact hLip i l hl z hz z' hz'
    · rw [hGc i l z hl, hGc i l z' hl, sub_self, abs_zero]
      exact mul_nonneg hC dist_nonneg

/-- Chain-rule bound: if the composite `f ∘ g` has derivative bounded by `K` at `x`, and both
`f` at `g x` and `g` at `x` are differentiable, then `|f'(g x)| * |g'(x)| ≤ K`. -/
theorem deriv_mul_le_of_comp {f g : ℝ → ℝ} {x K : ℝ}
    (hf : DifferentiableAt ℝ f (g x)) (hg : DifferentiableAt ℝ g x)
    (h : |deriv (f ∘ g) x| ≤ K) : |deriv f (g x)| * |deriv g x| ≤ K := by
  have h1 : deriv (f ∘ g) x = deriv f (g x) * deriv g x := by
    rw [deriv_comp]
    · exact hf
    · exact hg
  rw [h1, abs_mul] at h
  exact h

end Work.WilG4c

namespace Work.WilG4c

open WilkiesDesign WilkiesDesign.CG

/-! ## TEMPORARY stubs (removed once the delegated modules land) -/

end Work.WilG4c
