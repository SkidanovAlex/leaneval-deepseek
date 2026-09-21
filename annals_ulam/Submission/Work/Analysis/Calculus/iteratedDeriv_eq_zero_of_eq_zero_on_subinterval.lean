import Mathlib
import Submission.Commons.Analysis.Calculus.eqOn_of_hasDerivAt_eq_zero_Icc

namespace Commons.Analysis.Calculus

open Set Filter
open scoped Topology ContDiff

/-- If the `k`-th iterated derivative of a smooth function vanishes on an
interval and the function vanishes on a terminal subinterval with nonempty
interior, then it vanishes on the whole interval.  The assumption `c < b` is
needed: when `c = b`, the terminal condition is only a pointwise value and
does not determine the function. -/
lemma iteratedDeriv_zero_of_zero_nhds {k : ℕ} {f : ℝ → ℝ} {x : ℝ}
    (h : f =ᶠ[𝓝 x] (fun _ : ℝ => (0 : ℝ))) : iteratedDeriv k f x = 0 := by
  have hiter := Filter.EventuallyEq.iteratedDeriv_eq (𝕜 := ℝ) (n := k) (f := f)
    (g := fun _ : ℝ => (0 : ℝ)) (x := x) h
  simpa using hiter

lemma iteratedDeriv_eq_zero_of_eq_zero_on_subinterval {k : ℕ} {a b c : ℝ} {f : ℝ → ℝ}
    (hab : a ≤ b) (hcb : c < b) (hac : a ≤ c)
    (hf : ContDiffOn ℝ (⊤ : ℕ∞) f Set.univ)
    (hderiv : ∀ s ∈ Set.Icc a b, iteratedDeriv k f s = 0)
    (hzero : ∀ s ∈ Set.Icc c b, f s = 0) :
    ∀ s ∈ Set.Icc a b, f s = 0 := by
  induction k with
  | zero =>
      intro s hs
      simpa [iteratedDeriv_zero] using hderiv s hs
  | succ k ih =>
      have hf_global : ContDiff ℝ (⊤ : ℕ∞) f := contDiffOn_univ.mp hf
      let g : ℝ → ℝ := iteratedDeriv k f
      have hg_diff : ∀ x ∈ Set.Icc a b, HasDerivAt g 0 x := by
        intro x hx
        have hx_deriv : deriv g x = 0 := by
          have h := hderiv x hx
          simpa [g, iteratedDeriv_succ] using h
        have hd : HasDerivAt g (deriv g x) x := by
          have hdiff : Differentiable ℝ g := by
            exact (hf_global.differentiable_iteratedDeriv k (by
              exact_mod_cast (ENat.natCast_lt_top (n := k))))
          exact hdiff.differentiableAt.hasDerivAt
        simpa [hx_deriv] using hd
      have hconst : ∀ x ∈ Set.Icc a b, g x = g a :=
        eqOn_of_hasDerivAt_eq_zero_Icc (f := g) hab hg_diff
      have hg_a : g a = 0 := by
        let d : ℝ := (c + b) / 2
        have hcd : c < d := by dsimp [d]; linarith
        have hdb : d < b := by dsimp [d]; linarith
        have had : a ≤ d := le_trans hac (le_of_lt hcd)
        have hd_in : d ∈ Set.Icc a b := ⟨had, le_of_lt hdb⟩
        have h_eventually : f =ᶠ[𝓝 d] (fun _ : ℝ => (0 : ℝ)) := by
          have hIoo : Set.Ioo c b ∈ 𝓝 d := Ioo_mem_nhds hcd hdb
          filter_upwards [hIoo] with t ht
          exact hzero t ⟨le_of_lt ht.1, le_of_lt ht.2⟩
        have hd_deriv : g d = 0 := by
          have := iteratedDeriv_zero_of_zero_nhds (k := k) (f := f) (x := d) h_eventually
          simpa [g] using this
        have hconst_d := hconst d hd_in
        rw [← hconst_d]
        exact hd_deriv
      have hg_all : ∀ x ∈ Set.Icc a b, g x = 0 := by
        intro x hx
        rw [hconst x hx, hg_a]
      exact ih hg_all

end Commons.Analysis.Calculus
