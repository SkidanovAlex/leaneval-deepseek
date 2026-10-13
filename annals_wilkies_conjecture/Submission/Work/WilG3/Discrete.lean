/-
  WilG3 — the discrete `C^r` lemma of Binyamini–Novikov–Zak (arXiv 2202.05305, Lemma 5.4),
  proved as `G3_discrete_Cr_proved` for the frozen statement `WilkieDesign.CG.G3_discrete_Cr`
  in `Submission/Work/Wilkies/CG/Spec.lean`.

  Assembly: `Work.WilG3.DiscreteCrCore` is the abstract induction (a tower of functions with
  constant-signed derivatives), and `Work.WilG3.WithinTowerHasDerivAt` identifies the tower of
  within-derivatives of a `C^(r+1)` function on `(0,1)` with such a tower.
-/
import Submission.Work.WilG3.Defs
import Submission.Work.WilG3.DiscreteCrCore
import Submission.Work.WilG3.WithinTowerHasDerivAt

set_option autoImplicit false
noncomputable section
open Classical
namespace WilkiesDesign.CG

open WilkiesDesign

/-- **G3a: BNZ Lemma 5.4 (discrete C^r).** -/
theorem G3_discrete_Cr_proved (r : ℕ) (f : ℝ → ℝ)
    (hf : ContDiffOn ℝ (r + 1) f (Set.Ioo 0 1))
    (hI : ∀ x ∈ Set.Ioo (0 : ℝ) 1, f x ∈ Set.Ioo (0 : ℝ) 1)
    (hsign : ∀ j ≤ r + 1,
      (∀ x ∈ Set.Ioo (0 : ℝ) 1, 0 ≤ iteratedDerivWithin j f (Set.Ioo 0 1) x) ∨
      (∀ x ∈ Set.Ioo (0 : ℝ) 1, iteratedDerivWithin j f (Set.Ioo 0 1) x ≤ 0))
    (M : ℝ) (hM : 1 < M) :
    ∀ j ≤ r, ∀ x ∈ Set.Ioo (0 : ℝ) 1, (j : ℝ) / M < x → x < 1 - j / M →
      |iteratedDerivWithin j f (Set.Ioo 0 1) x| < M ^ j := by
  refine Work.WilG3.DiscreteCrCore r M hM
    (fun j x => iteratedDerivWithin j f (Set.Ioo (0 : ℝ) 1) x) ?_ hsign ?_
  · intro j hj y hy
    exact Work.WilG3.WithinTowerHasDerivAt r j f hf hj y hy
  · intro y hy
    have h := hI y hy
    rw [iteratedDerivWithin_zero, abs_of_pos h.1]
    exact h.2

end WilkiesDesign.CG

namespace Work.WilG3

/-- Alias of `WilkieDesign.CG.G3_discrete_Cr_proved`, for callers working in `Work.WilG3`. -/
theorem G3_discrete_Cr_proved (r : ℕ) (f : ℝ → ℝ)
    (hf : ContDiffOn ℝ (r + 1) f (Set.Ioo 0 1))
    (hI : ∀ x ∈ Set.Ioo (0 : ℝ) 1, f x ∈ Set.Ioo (0 : ℝ) 1)
    (hsign : ∀ j ≤ r + 1,
      (∀ x ∈ Set.Ioo (0 : ℝ) 1, 0 ≤ iteratedDerivWithin j f (Set.Ioo 0 1) x) ∨
      (∀ x ∈ Set.Ioo (0 : ℝ) 1, iteratedDerivWithin j f (Set.Ioo 0 1) x ≤ 0))
    (M : ℝ) (hM : 1 < M) :
    ∀ j ≤ r, ∀ x ∈ Set.Ioo (0 : ℝ) 1, (j : ℝ) / M < x → x < 1 - j / M →
      |iteratedDerivWithin j f (Set.Ioo 0 1) x| < M ^ j :=
  WilkiesDesign.CG.G3_discrete_Cr_proved r f hf hI hsign M hM

end Work.WilG3
