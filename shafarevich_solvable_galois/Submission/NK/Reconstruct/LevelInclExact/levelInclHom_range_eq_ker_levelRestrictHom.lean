import Mathlib.NumberTheory.NumberField.Basic
import Submission.NK.Reconstruct.baseChange
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Exactness of the inclusion of level Galois groups

For two finite Galois levels `L ⊆ M` of `K'/K` (`NK.Reconstruct.FrobLevel`), the two group
homomorphisms of `NK.Reconstruct.baseChange` and `NK.Reconstruct.GammaObject`,

* `levelInclHom L M h : Gal(M/L) →* Gal(M/K)` — restriction of scalars along `K ⊆ L` (the
  "forget the `L`-structure of `M`" map), and
* `levelRestrictHom L M h : Gal(M/K) →* Gal(L/K)` — the transition map of the projective system,

fit into the exact sequence of Galois theory

  `1 → Gal(M/L) → Gal(M/K) → Gal(L/K) → 1`,

because `L/K` is normal (`M` being a finite level, `M/K` is Galois and `L/K` normal, so
restriction `Gal(M/K) → Gal(L/K)` is onto with kernel the automorphisms of `M` fixing `L`).

This file proves the exactness statement at the group level, i.e. that the range of the level
inclusion is the kernel of the level restriction:

* `levelInclHom_range_le_levelRestrictHom_ker` — every automorphism of `M` fixing `L` restricts to
  the identity of `L` (evaluated on an element `y ∈ L`, both sides are `σ y` in the ambient field);
* `levelRestrictHom_ker_le_levelInclHom_range` — conversely, an automorphism of `M/K` restricting
  to the identity of `L` fixes `L` pointwise, hence is `L`-linear, hence lies in the image of the
  inclusion;
* `levelInclHom_range_eq_ker_levelRestrictHom` — the resulting equality
  `range (levelInclHom L M h) = ker (levelRestrictHom L M h)`.

The two `apply_coe` lemmas `levelInclHom_apply_coe` and `levelRestrictHom_apply_coe` (the latter in
`Submission/Work/Reconstruct/ellRestrict_comp.lean`) are what make both computations purely
elementwise: neither map moves the underlying element of the ambient field `K'`.

## References

J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, Ch. X §10.3;
S. Shimizu, *On the Neukirch–Uchida theorem for small sets of primes*, arXiv:2009.10431, §4.
-/

set_option linter.unusedSectionVars false

namespace NK.Reconstruct.LevelInclExact

/-- **The inclusion lands in the kernel of the restriction**: an automorphism `g` of `M` fixing `L`
restricts to the identity of `L`.  For `y ∈ L` the value of
`levelRestrictHom L M h (levelInclHom L M h g)` at `y` is, in the ambient field `K'`, both the value
of `g` at `y` and `y` itself, because `g` is `L`-linear. -/
theorem levelInclHom_range_le_levelRestrictHom_ker {K : Type*} [Field K] [NumberField K]
    {K' : Type*} [Field K'] [Algebra K K'] [IsGalois K K'] (L M : FrobLevel K K')
    (h : L.L ≤ M.L) : (levelInclHom L M h).range ≤ (levelRestrictHom L M h).ker := by
  rintro σ ⟨g, rfl⟩
  rw [MonoidHom.mem_ker]
  ext y
  rw [AlgEquiv.one_apply, levelRestrictHom_apply_coe, levelInclHom_apply_coe]
  exact congrArg Subtype.val (g.commutes y)

/-- **The kernel of the restriction is contained in the inclusion**: if an automorphism `σ` of `M/K`
restricts to the identity of `L`, then `σ` fixes `L` pointwise, hence is `L`-linear; the same
underlying automorphism of `M`, regarded as an `L`-algebra automorphism, is a preimage of `σ`. -/
theorem levelRestrictHom_ker_le_levelInclHom_range {K : Type*} [Field K] [NumberField K]
    {K' : Type*} [Field K'] [Algebra K K'] [IsGalois K K'] (L M : FrobLevel K K')
    (h : L.L ≤ M.L) : (levelRestrictHom L M h).ker ≤ (levelInclHom L M h).range := by
  intro σ hσ
  rw [MonoidHom.mem_ker] at hσ
  -- `σ` fixes `L` pointwise, read in `M`.
  have hfix : ∀ y : ↥L.L, (σ ⟨(y : K'), h y.2⟩ : ↥M.L) = ⟨(y : K'), h y.2⟩ := by
    intro y
    apply Subtype.ext
    have hy := congrArg (fun τ : Gal(↥L.L/K) => ((τ y : ↥L.L) : K')) hσ
    simpa [levelRestrictHom_apply_coe] using hy
  refine ⟨{ σ with commutes' := fun a => hfix a }, ?_⟩
  ext x
  rfl

/-- **Exactness of the Galois-theoretic pair `Gal(M/L) → Gal(M/K) → Gal(L/K)`**: the range of the
level inclusion is the kernel of the level restriction. -/
theorem levelInclHom_range_eq_ker_levelRestrictHom {K : Type*} [Field K] [NumberField K]
    {K' : Type*} [Field K'] [Algebra K K'] [IsGalois K K'] (L M : FrobLevel K K')
    (h : L.L ≤ M.L) : (levelInclHom L M h).range = (levelRestrictHom L M h).ker :=
  le_antisymm (levelInclHom_range_le_levelRestrictHom_ker L M h)
    (levelRestrictHom_ker_le_levelInclHom_range L M h)

end NK.Reconstruct.LevelInclExact
