import Mathlib

namespace Work.WilG4a

theorem continuousOn_iteratedDeriv {j : ℕ} {f : ℝ → ℝ} {s : Set ℝ} (hs : IsOpen s)
    (hf : ∀ x ∈ s, ContDiffAt ℝ (j + 1) f x) : ContinuousOn (iteratedDeriv j f) s := by
  -- Pointwise `C^{j+1}` on the open set `s` gives `ContDiffOn ℝ (j+1) f s`.
  have hc : ContDiffOn ℝ (j + 1) f s := hs.contDiffOn_iff.mpr fun a ha => hf a ha
  -- Hence the `j`-th derivative within `s` is `C^1`, in particular continuous on `s`.
  have h1 : ContDiffOn ℝ 1 (iteratedDerivWithin j f s) s :=
    ((contDiffOn_nat_succ_iff_contDiffOn_one_iteratedDerivWithin (𝕜 := ℝ) (f := f)
      (s := s) (n := j) hs.uniqueDiffOn).mp hc).2
  -- On an open set the derivative within `s` coincides with the honest iterated derivative.
  exact h1.continuousOn.congr fun x hx =>
    (iteratedDerivWithin_of_isOpen (n := j) hs hx).symm

end Work.WilG4a
