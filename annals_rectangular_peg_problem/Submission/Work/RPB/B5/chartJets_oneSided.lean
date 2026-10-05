import Mathlib

open scoped Topology

-- `haveI` is genuinely needed below (`NeBot` is used as a typeclass instance).
set_option linter.style.haveILetI false

namespace Work.RPB.B5

theorem chartJets_oneSided {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f g : ℝ → E} {x₀ δ : ℝ} (hδ : 0 < δ) {n : ℕ}
    (hf : ContDiffAt ℝ n f x₀) (hg : ContDiffAt ℝ n g x₀)
    (h : ∀ x ∈ Set.Ioo (x₀ - δ) x₀, f x = g x) {k : ℕ} (hk : k ≤ n) :
    iteratedDeriv k f x₀ = iteratedDeriv k g x₀ := by
  -- If two `C^n` functions agree on a one-sided neighbourhood `(x₀-δ, x₀)` of `x₀`,
  -- then all their iterated derivatives of order `≤ n` agree at `x₀`.
  have key : ∀ k, ∀ {n : ℕ}, k ≤ n → ∀ {u v : ℝ → E},
      ContDiffAt ℝ n u x₀ → ContDiffAt ℝ n v x₀ →
      (∀ x ∈ Set.Ioo (x₀ - δ) x₀, u x = v x) →
      iteratedDeriv k u x₀ = iteratedDeriv k v x₀ := by
    intro k
    induction k with
    | zero =>
      -- Order 0: only continuity is used, and the common left limit forces `u x₀ = v x₀`.
      intro n _ u v hu hv huv
      simp only [iteratedDeriv_zero]
      haveI : (𝓝[Set.Iio x₀] x₀).NeBot := nhdsLT_neBot x₀
      have hmem : Set.Ioo (x₀ - δ) x₀ ∈ 𝓝[Set.Iio x₀] x₀ := by
        rw [mem_nhdsWithin_iff_exists_mem_nhds_inter]
        refine ⟨Set.Ioo (x₀ - δ) (x₀ + 1), Ioo_mem_nhds (by linarith) (by linarith), ?_⟩
        rintro x ⟨h1, h2⟩
        exact ⟨h1.1, h2⟩
      have hEq : (fun x => u x - v x) =ᶠ[𝓝[Set.Iio x₀] x₀] (fun _ => (0 : E)) := by
        filter_upwards [hmem] with x hx
        rw [huv x hx]; simp
      have h1 : Filter.Tendsto (fun x => u x - v x) (𝓝[Set.Iio x₀] x₀)
          (𝓝 ((fun x => u x - v x) x₀)) :=
        (hu.continuousAt.sub hv.continuousAt).continuousWithinAt
      have h2 : Filter.Tendsto (fun x => u x - v x) (𝓝[Set.Iio x₀] x₀) (𝓝 (0 : E)) :=
        Filter.Tendsto.congr' hEq.symm tendsto_const_nhds
      exact sub_eq_zero.mp (tendsto_nhds_unique h1 h2)
    | succ k ih =>
      -- Order `k+1`: pass to the derivatives, which still agree on the same interval
      -- and are `C^(n-1)` at `x₀`, and apply the induction hypothesis.
      intro n hk u v hu hv huv
      rw [iteratedDeriv_succ', iteratedDeriv_succ']
      have hderiv : ∀ x ∈ Set.Ioo (x₀ - δ) x₀, deriv u x = deriv v x := by
        intro x hx
        have heq : u =ᶠ[𝓝 x] v := by
          filter_upwards [isOpen_Ioo.mem_nhds hx] with y hy
          exact huv y hy
        exact Filter.EventuallyEq.deriv_eq heq
      have hn1 : 1 ≤ n := by omega
      have hle : (((n - 1 : ℕ) : WithTop ℕ∞) + 1) ≤ ((n : ℕ) : WithTop ℕ∞) := by
        rw [← Nat.sub_add_cancel hn1]; simp
      have hcu : ContDiffAt ℝ (n - 1) (deriv u) x₀ := ContDiffAt.derivWithin hu hle
      have hcv : ContDiffAt ℝ (n - 1) (deriv v) x₀ := ContDiffAt.derivWithin hv hle
      have hk' : k ≤ n - 1 := by omega
      exact ih hk' hcu hcv hderiv
  exact key k hk hf hg h

end Work.RPB.B5
