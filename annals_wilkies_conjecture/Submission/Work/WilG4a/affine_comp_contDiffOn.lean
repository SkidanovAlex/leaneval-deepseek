import Mathlib
import Submission.Work.WilG4a.f1affine1_defs

namespace Work.WilG4a

/-- The affine reparametrisation `x ↦ c + (d - c) * x` maps the open unit interval `I = (0,1)`
into the open interval `(c,d)` when `c < d`, hence precomposition with it preserves
`C^n`-regularity on `I`. -/
lemma affine_comp_contDiffOn {n : ℕ} {f : ℝ → ℝ} {c d : ℝ} (hcd : c < d) (h : ContDiffOn ℝ n f (Set.Ioo c d)) : ContDiffOn ℝ n (fun x : ℝ => f (c + (d - c) * x)) I := by
  have hφ : ContDiffOn ℝ n (fun x : ℝ => c + (d - c) * x) (Set.Ioo 0 1) := by
    fun_prop
  have hmap : Set.MapsTo (fun x : ℝ => c + (d - c) * x) (Set.Ioo 0 1) (Set.Ioo c d) := by
    intro x hx
    simp only [Set.mem_Ioo] at hx ⊢
    exact ⟨by nlinarith, by nlinarith⟩
  exact h.comp hφ hmap

end Work.WilG4a
