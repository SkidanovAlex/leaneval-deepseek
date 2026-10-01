import Mathlib

namespace Work.LinnikAreas.FarRepel

/-- If a sequence of complex functions converging locally uniformly on an open set `U` is
eventually differentiable on `U`, then so are all its iterated derivatives, and the `k`-th
derivatives converge locally uniformly to the `k`-th derivative of the limit.  (Iterate
`TendstoLocallyUniformlyOn.deriv`, using that on an open set in `ℂ` differentiability is
stable under `deriv`.) -/
theorem tendstoLocallyUniformlyOnIterateDeriv {U : Set ℂ} (hU : IsOpen U)
    {F : ℕ → ℂ → ℂ} {f : ℂ → ℂ} (hF : ∀ᶠ n in Filter.atTop, DifferentiableOn ℂ (F n) U)
    (h : TendstoLocallyUniformlyOn F f Filter.atTop U) (k : ℕ) :
    TendstoLocallyUniformlyOn (fun n => deriv^[k] (F n)) (deriv^[k] f) Filter.atTop U := by
  -- On an open set in `ℂ`, differentiability is stable under taking derivatives, hence the
  -- `k`-th iterated derivatives of the `F n` are eventually differentiable on `U`.
  have hFk : ∀ k, ∀ᶠ n in Filter.atTop, DifferentiableOn ℂ (deriv^[k] (F n)) U := by
    intro k
    induction k with
    | zero => simpa using hF
    | succ k ih =>
      filter_upwards [ih] with n hn
      simpa only [Function.iterate_succ', Function.comp_apply] using hn.deriv hU
  -- Iterate `TendstoLocallyUniformlyOn.deriv` on `k`.
  induction k with
  | zero => simpa using h
  | succ k ih =>
    have hd := ih.deriv (hFk k) hU
    simpa only [Function.iterate_succ', Function.comp_apply, Function.comp_def] using hd

end Work.LinnikAreas.FarRepel
