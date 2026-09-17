import Mathlib.Algebra.Lie.Killing

/-!
# A Killing Lie algebra is finite-dimensional

Mathlib's `LieAlgebra.IsKilling R L` is defined (for an arbitrary, not necessarily
finite-dimensional, Lie algebra `L`) by requiring the "Killing orthogonal complement of `⊤`"
to be `⊥`.  Since `LinearMap.trace` is defined to be *zero* on a module admitting no finite
basis, an infinite-dimensional Lie algebra over a field has *identically vanishing* Killing
form; then the Killing complement of `⊤` is `⊤` itself, which can only be `⊥` if `L` is a
subsingleton.

Consequently, over a field, a nontrivial Lie algebra with non-singular Killing form is
necessarily finite-dimensional.  This is the missing implication needed whenever
`LieAlgebra.IsKilling` is used to obtain the finite-dimensional theory
(`IsKilling.instSemisimple`, Cartan subalgebras, root space decompositions, ...).

## Main result

* `Commons.Algebra.Lie.Killing.moduleFinite`: `IsKilling K L` and `Nontrivial L` imply
  `Module.Finite K L`.
-/

namespace Commons.Algebra.Lie.Killing

open LieAlgebra

/-- **A nontrivial Lie algebra over a field with non-singular Killing form is
finite-dimensional.**

If `L` admitted no finite basis then `LinearMap.trace K L` would be the zero map, hence
`killingForm K L = 0`, hence `LinearMap.ker (killingForm K L) = ⊤`; the `IsKilling` hypothesis
says this kernel is `⊥`, forcing `L` to be a subsingleton, contradicting `Nontrivial L`. -/
theorem moduleFinite {K L : Type*} [Field K] [LieRing L] [LieAlgebra K L]
    [LieAlgebra.IsKilling K L] [Nontrivial L] : Module.Finite K L := by
  by_contra h
  -- If `L` is not finitely generated, it admits no finite basis.
  have hH : ¬ ∃ s : Finset L, Nonempty (Module.Basis s K L) := by
    rintro ⟨s, ⟨b⟩⟩
    exact h (Module.Finite.of_basis b)
  -- Hence the trace on `L` vanishes identically.
  have htrace : ∀ f : L →ₗ[K] L, LinearMap.trace K L f = 0 := by
    intro f
    rw [LinearMap.trace, dif_neg hH, LinearMap.zero_apply]
  -- So does the Killing form.
  have hform : killingForm K L = 0 := by
    ext x y
    rw [killingForm_apply_apply, htrace]
    rfl
  have hker : LinearMap.ker (killingForm K L) = ⊤ := by
    rw [hform, LinearMap.ker_zero]
  -- But `IsKilling` says the kernel of the Killing form is trivial.
  have hbot : LinearMap.ker (killingForm K L) = ⊥ :=
    LieAlgebra.IsKilling.ker_killingForm_eq_bot K L
  rw [hker] at hbot
  -- Hence every element of `L` is `0`, contradicting nontriviality.
  obtain ⟨x, y, hxy⟩ := exists_pair_ne L
  have hx : x = 0 := by
    have : x ∈ (⊥ : Submodule K L) := hbot ▸ Submodule.mem_top
    simpa using this
  have hy : y = 0 := by
    have : y ∈ (⊥ : Submodule K L) := hbot ▸ Submodule.mem_top
    simpa using this
  exact hxy (hx.trans hy.symm)

end Commons.Algebra.Lie.Killing