import Mathlib
import Submission.Work.Normal.Basic
import Submission.Work.Normal.escapeRadius
import Submission.Work.Normal.FilledJulia
import Submission.Work.Normal.Frontier

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# Elementary properties of the Julia set of a polynomial map

Using `JuliaSet f = frontier (FilledJuliaSet f)` and the invariances of `K`, `K°` and `Kᶜ` from
`FilledJulia.lean`, we obtain the standard structural facts about the Julia set of a polynomial map
`f` of degree `d ≥ 2`:

* `f` is continuous, and `JuliaSet f` is closed (`Basic`) and nonempty;
* `JuliaSet f` is completely invariant: `f '' JuliaSet f ⊆ JuliaSet f` and
  `f ⁻¹' JuliaSet f ⊆ JuliaSet f`, hence also for iterates of `f`.
-/

namespace Work.Normal

open Set Filter Topology Function
open scoped Topology Polynomial

/-- The filled Julia set of a polynomial map of degree at least two is closed. -/
theorem isClosed_filledJuliaSet {d : ℕ} {f : ℂ → ℂ} (hd : 2 ≤ d)
    (hf : IsPolynomialMapOfDegree d f) : IsClosed (FilledJuliaSet f) := by
  obtain ⟨R, -, -, -, -, hcl, -, -⟩ := escapeRadius hd hf
  exact hcl

/-- The filled Julia set of a polynomial map of degree at least two is not all of `ℂ`. -/
theorem filledJuliaSet_ne_univ {d : ℕ} {f : ℂ → ℂ} (hd : 2 ≤ d)
    (hf : IsPolynomialMapOfDegree d f) : FilledJuliaSet f ≠ Set.univ := by
  obtain ⟨R, hR2, -, hKeq, -, -, -, -⟩ := escapeRadius hd hf
  intro h
  have hmem : ((R + 1 : ℝ) : ℂ) ∈ FilledJuliaSet f := by rw [h]; trivial
  rw [hKeq] at hmem
  have hnorm : ∀ x : ℝ, 0 ≤ x → ‖((x : ℝ) : ℂ)‖ = x := by
    intro x hx
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hx]
  have h0 := hmem 0
  rw [Function.iterate_zero_apply, hnorm (R + 1) (by linarith)] at h0
  linarith

/-- The Julia set of a polynomial map of degree at least two is nonempty. -/
theorem juliaSet_nonempty {d : ℕ} {f : ℂ → ℂ} (hd : 2 ≤ d)
    (hf : IsPolynomialMapOfDegree d f) : (JuliaSet f).Nonempty := by
  obtain ⟨R, hR2, -, hKeq, -, hKcl, -, hKne⟩ := escapeRadius hd hf
  rw [juliaSet_eq_frontier hd hf]
  by_contra h
  rw [not_nonempty_iff_eq_empty] at h
  have hclopen : IsClopen (FilledJuliaSet f) := isClopen_iff_frontier_eq_empty.mpr h
  rcases (isPreconnected_univ (α := ℂ)).subset_or_subset (u := FilledJuliaSet f)
      (v := (FilledJuliaSet f)ᶜ) hclopen.isOpen hclopen.compl.isOpen
      disjoint_compl_right (by simp) with hsub | hsub
  · exact filledJuliaSet_ne_univ hd hf (eq_univ_of_univ_subset hsub)
  · refine hKne.ne_empty (Subset.antisymm ?_ (empty_subset _))
    intro z hz
    exact hsub (mem_univ z) hz

/-- The Julia set of a polynomial map of degree at least two is forward invariant. -/
theorem mapsTo_juliaSet {d : ℕ} {f : ℂ → ℂ} (hd : 2 ≤ d)
    (hf : IsPolynomialMapOfDegree d f) : MapsTo f (JuliaSet f) (JuliaSet f) := by
  obtain ⟨-, -, -, -, -, hKcl, -, -⟩ := escapeRadius hd hf
  have hcont := continuous_of_isPolynomialMapOfDegree hf
  intro x hx
  rw [juliaSet_eq_frontier hd hf] at hx ⊢
  have hxK : x ∈ FilledJuliaSet f := by
    rw [← hKcl.closure_eq]
    exact frontier_subset_closure hx
  have hxcl : x ∈ closure (FilledJuliaSet f)ᶜ := by
    rw [frontier_eq_closure_inter_closure] at hx
    exact hx.2
  rw [frontier_eq_closure_inter_closure]
  refine ⟨?_, ?_⟩
  · rw [hKcl.closure_eq]
    exact mapsTo_filledJuliaSet f hxK
  · rw [mem_closure_iff_nhds] at hxcl ⊢
    intro W hW
    obtain ⟨y, hyV, hyK⟩ := hxcl (f ⁻¹' W) (hcont.continuousAt.preimage_mem_nhds hW)
    refine ⟨f y, hyV, fun hmem => hyK (preimage_filledJuliaSet_subset f hmem)⟩

/-- The Julia set of a polynomial map of degree at least two is backward invariant. -/
theorem preimage_juliaSet_subset {d : ℕ} {f : ℂ → ℂ} (hd : 2 ≤ d)
    (hf : IsPolynomialMapOfDegree d f) : f ⁻¹' (JuliaSet f) ⊆ JuliaSet f := by
  obtain ⟨-, -, -, -, -, hKcl, -, -⟩ := escapeRadius hd hf
  intro x hx
  rw [juliaSet_eq_frontier hd hf] at hx ⊢
  have hfxK : f x ∈ FilledJuliaSet f := by
    rw [← hKcl.closure_eq]
    exact frontier_subset_closure hx
  have hxK : x ∈ FilledJuliaSet f := preimage_filledJuliaSet_subset f hfxK
  rw [mem_frontier_iff_notMem_interior hxK]
  exact fun hxint => (mem_frontier_iff_notMem_interior hfxK).1 hx
    (mapsTo_interior_filledJuliaSet (by omega : 1 ≤ d) hf hxint)

/-- Preimages of the Julia set under an iterate are still in the Julia set. -/
theorem preimage_iterate_juliaSet_subset {d : ℕ} {f : ℂ → ℂ} (hd : 2 ≤ d)
    (hf : IsPolynomialMapOfDegree d f) (n : ℕ) :
    (f^[n]) ⁻¹' (JuliaSet f) ⊆ JuliaSet f := by
  induction n with
  | zero => exact Subset.rfl
  | succ n ih =>
    intro x hx
    simp only [mem_preimage, Function.iterate_succ_apply'] at hx
    exact ih (preimage_juliaSet_subset hd hf hx)

end Work.Normal
