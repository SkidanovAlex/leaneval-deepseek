import Mathlib

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.Coercivity

open scoped NNReal ENNReal Topology
open MeasureTheory Set Filter

/-- **Uniform geometric bound from a local one.**

If a family `a : ℕ → ℝ → ℝ` admits, at every point `θ` of a compact set `I`, a
neighbourhood `(θ - ε, θ + ε)` together with constants `C, s > 0` such that
`|a k θ'| ≤ C / s ^ k` for *all* `k` and all `θ'` in that neighbourhood, then the
same geometric bound holds uniformly on all of `I` (with constants obtained from a
finite subcover: the minimum of the `s`'s and the maximum of the `C`'s). -/
theorem uniform_geometric_bound_of_local {I : Set ℝ} (hI : IsCompact I) {a : ℕ → ℝ → ℝ}
    (hloc : ∀ θ ∈ I, ∃ ε > 0, ∃ C > 0, ∃ s > 0,
      ∀ k, ∀ θ' ∈ Set.Ioo (θ - ε) (θ + ε), |a k θ'| ≤ C / s ^ k) :
    ∃ C > 0, ∃ s > 0, ∀ k, ∀ θ ∈ I, |a k θ| ≤ C / s ^ k := by
  classical
  by_cases hne : I.Nonempty
  · -- Extract, by choice, the local neighbourhood and constants at each `θ ∈ I`.
    choose ε hεpos C hCpos s hs hb using fun (θ : I) => hloc θ θ.2
    -- These neighbourhoods cover `I`.
    have hcover : I ⊆ ⋃ i : I, Set.Ioo ((i : ℝ) - ε i) ((i : ℝ) + ε i) := by
      intro x hx
      exact Set.mem_iUnion.mpr
        ⟨⟨x, hx⟩, ⟨by linarith [hεpos ⟨x, hx⟩], by linarith [hεpos ⟨x, hx⟩]⟩⟩
    -- Compactness yields a finite subcover.
    obtain ⟨t, ht⟩ := hI.elim_finite_subcover
      (fun i : I => Set.Ioo ((i : ℝ) - ε i) ((i : ℝ) + ε i)) (fun _ => isOpen_Ioo) hcover
    -- The index finset of the subcover is nonempty because `I` is.
    have htne : t.Nonempty := by
      obtain ⟨x, hx⟩ := hne
      have hxmem := ht hx
      simp only [Set.mem_iUnion, exists_prop] at hxmem
      obtain ⟨i, hi, _⟩ := hxmem
      exact ⟨i, hi⟩
    -- Pick the indices achieving the minimal rate and the maximal constant.
    obtain ⟨i₀, _, hi₀min⟩ := Finset.exists_min_image t s htne
    obtain ⟨i₁, _, hi₁max⟩ := Finset.exists_max_image t C htne
    refine ⟨C i₁, hCpos i₁, s i₀, hs i₀, fun k θ hθ => ?_⟩
    -- `θ` lies in one of the (finitely many) chosen neighbourhoods.
    have hmem := ht hθ
    simp only [Set.mem_iUnion, exists_prop] at hmem
    obtain ⟨i, hit, hθi⟩ := hmem
    calc |a k θ| ≤ C i / (s i) ^ k := hb i k θ hθi
      _ ≤ C i₁ / (s i₀) ^ k := by
          have hCi : C i ≤ C i₁ := hi₁max i hit
          have hsi : s i₀ ≤ s i := hi₀min i hit
          have hs0 : 0 < s i₀ := hs i₀
          have hpi : (s i₀) ^ k ≤ (s i) ^ k := by gcongr
          gcongr
          exact le_of_lt (hCpos i₁)
  · -- `I` is empty: the conclusion holds vacuously.
    exact ⟨1, one_pos, 1, one_pos, fun _ θ hθ => absurd ⟨θ, hθ⟩ hne⟩

end Work.Coercivity
