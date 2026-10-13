import Mathlib
import Submission.Work.WilG4a.f1affine1_defs
import Submission.Work.WilG4a.affine_reparam_bound

namespace Work.WilG4a

lemma affine_comp_sameSign {n j : ℕ} {f : ℝ → ℝ} {c d : ℝ} (hcd : c < d) (h : ContDiffOn ℝ n f (Set.Ioo c d)) (hj : j ≤ n) (hsign : SameSignOn j f (Set.Ioo c d)) : SameSignOn j (fun x : ℝ => f (c + (d - c) * x)) I := by
  have hpos : 0 < d - c := sub_pos.mpr hcd
  -- The affine map sends `I = (0,1)` strictly into `(c,d)`.
  have hmem : ∀ x ∈ I, c + (d - c) * x ∈ Set.Ioo c d := by
    intro x hx
    exact ⟨by nlinarith [hx.1, hpos], by nlinarith [hx.2, hpos]⟩
  -- The chain rule for the `j`-th iterated derivative.
  have hcomp : ∀ x ∈ I, iteratedDeriv j (fun x : ℝ => f (c + (d - c) * x)) x
      = (d - c) ^ j * iteratedDeriv j f (c + (d - c) * x) := by
    intro x hx
    have hxI := hmem x hx
    have hcda : ContDiffAt ℝ n f (c + (d - c) * x) :=
      h.contDiffAt (isOpen_Ioo.mem_nhds hxI)
    exact iteratedDeriv_comp_affine c (d - c) j f x (hcda.of_le (by exact_mod_cast hj))
  rcases hsign with hnn | hnp
  · left
    intro x hx
    rw [hcomp x hx]
    exact mul_nonneg (pow_nonneg hpos.le j) (hnn _ (hmem x hx))
  · right
    intro x hx
    rw [hcomp x hx]
    exact mul_nonpos_of_nonneg_of_nonpos (pow_nonneg hpos.le j) (hnp _ (hmem x hx))

end Work.WilG4a
