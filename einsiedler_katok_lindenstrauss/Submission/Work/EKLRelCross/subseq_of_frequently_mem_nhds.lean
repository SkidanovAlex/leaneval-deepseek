import Mathlib

/-!
# Extracting a convergent subsequence contained in `A`

If a sequence `u : ℕ → X` in a first-countable topological space visits `A ∩ s`
infinitely often for every neighbourhood `s` of `x`, then there is a strictly
monotone `φ` such that `u ∘ φ` stays inside `A` and converges to `x`.

The argument is a standard diagonal extraction: take an antitone basis
`V : ℕ → Set X` of `𝓝 x` (`Filter.exists_antitone_basis`, available because
`𝓝 x` is countably generated in a first-countable space), use the hypothesis on
each `V n` to find indices, and extract them simultaneously with
`extraction_forall_of_frequently`. The resulting subsequence satisfies
`u (φ n) ∈ V n`, so the basis property gives convergence to `x`
(`HasAntitoneBasis.tendsto`).
-/

namespace Work.EKLRelCross

theorem subseq_of_frequently_mem_nhds {X : Type*} [TopologicalSpace X] [FirstCountableTopology X]
    (u : ℕ → X) (x : X) (A : Set X)
    (h : ∀ s ∈ nhds x, ∃ᶠ n in Filter.atTop, u n ∈ A ∩ s) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ (∀ k, u (φ k) ∈ A) ∧
      Filter.Tendsto (fun k => u (φ k)) Filter.atTop (nhds x) := by
  -- An antitone (decreasing) neighbourhood basis at `x`.
  obtain ⟨V, hV⟩ := Filter.exists_antitone_basis (nhds x)
  -- Every basis element is a neighbourhood of `x`, so `u` frequently visits `A ∩ V n`.
  have hVfreq : ∀ n, ∃ᶠ k in Filter.atTop, u k ∈ A ∩ V n :=
    fun n => h (V n) (hV.mem n)
  -- Extract, simultaneously for all `n`, an index `φ n` with `u (φ n) ∈ A ∩ V n`.
  obtain ⟨φ, hφmono, hφmem⟩ := Filter.extraction_forall_of_frequently hVfreq
  exact ⟨φ, hφmono, fun k => (hφmem k).1, hV.tendsto (fun k => (hφmem k).2)⟩

end Work.EKLRelCross
