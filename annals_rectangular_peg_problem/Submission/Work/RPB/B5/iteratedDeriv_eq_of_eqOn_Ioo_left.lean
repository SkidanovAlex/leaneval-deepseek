import Mathlib

namespace Work.RPB.B5

open scoped Topology

/-- If two functions are `C^n` at `x₀` and agree on an open interval `(x₀ - δ, x₀)` to the left of
`x₀`, then their `k`-th iterated derivatives at `x₀` agree for every `k ≤ n`. -/
theorem iteratedDeriv_eq_of_eqOn_Ioo_left {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f g : ℝ → E} {x₀ δ : ℝ} (hδ : 0 < δ) {n : ℕ} (hf : ContDiffAt ℝ n f x₀)
    (hg : ContDiffAt ℝ n g x₀) (h : ∀ x ∈ Set.Ioo (x₀ - δ) x₀, f x = g x) {k : ℕ}
    (hk : k ≤ n) : iteratedDeriv k f x₀ = iteratedDeriv k g x₀ := by
  -- Prove the general statement by induction on `k`, allowing the functions and `n` to vary so
  -- that the induction hypothesis can be applied to `deriv f` and `deriv g`.
  have main : ∀ k : ℕ, ∀ (n : ℕ) (f g : ℝ → E), ContDiffAt ℝ n f x₀ → ContDiffAt ℝ n g x₀ →
      (∀ x ∈ Set.Ioo (x₀ - δ) x₀, f x = g x) → k ≤ n →
      iteratedDeriv k f x₀ = iteratedDeriv k g x₀ := by
    intro k
    induction k with
    | zero =>
      -- `iteratedDeriv 0 = id`, so this is the statement `f x₀ = g x₀`, which follows from
      -- continuity at `x₀` and agreement on the left-neighbourhood `(x₀ - δ, x₀)`.
      intro n f g hf hg h hk
      simp only [iteratedDeriv_zero]
      have hmem : Set.Ioo (x₀ - δ) x₀ ∈ 𝓝[Set.Iio x₀] x₀ := Ioo_mem_nhdsLT (by linarith)
      have hev : f =ᶠ[𝓝[Set.Iio x₀] x₀] g :=
        Filter.eventually_of_mem hmem (fun x hx => h x hx)
      have h1 : Filter.Tendsto f (𝓝[Set.Iio x₀] x₀) (𝓝 (f x₀)) :=
        hf.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
      have h2 : Filter.Tendsto g (𝓝[Set.Iio x₀] x₀) (𝓝 (g x₀)) :=
        hg.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
      exact tendsto_nhds_unique (Filter.Tendsto.congr' hev h1) h2
    | succ k ih =>
      -- `iteratedDeriv (k+1) = iteratedDeriv k ∘ deriv`, and `deriv f = deriv g` on the open
      -- interval (being a neighbourhood of each of its points), so we apply the induction
      -- hypothesis to `deriv f`, `deriv g` with `n = k`.
      intro n f g hf hg h hk
      rw [iteratedDeriv_succ', iteratedDeriv_succ']
      have hderiv : ∀ x ∈ Set.Ioo (x₀ - δ) x₀, deriv f x = deriv g x := by
        intro x hx
        exact Filter.EventuallyEq.deriv_eq
          (Filter.eventually_of_mem (isOpen_Ioo.mem_nhds hx) (fun y hy => h y hy))
      exact ih k (deriv f) (deriv g) (hf.derivWithin (by exact_mod_cast hk))
        (hg.derivWithin (by exact_mod_cast hk)) hderiv le_rfl
  exact main k n f g hf hg h hk

end Work.RPB.B5
