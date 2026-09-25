import Mathlib
import Submission.Work.TameArithmetic.Defs
import Submission.Work.ClassFieldTower.ProTwoDefs

/-!
# `Work.TameArithmetic.residuallyFiniteTwoGroup_galoisGroup_tame`

`Gamma = Gal(K/Q)` for a maximal tame pro-`2` extension `K` of `Q` (`IsMaximalTamePro2 K`) is
*residually a finite `2`-group*: every nontrivial element survives in a quotient which is a
finite `2`-group.  This is the `ResiduallyFiniteTwoGroup` hypothesis of the Golod--Shafarevich
interface `Work.ClassFieldTower.ProTwoPresentationData` (`ProTwoDefs.lean`): it is what turns
`Finite G` into `IsPGroup 2 G` (so that the finite `p`-group Golod--Shafarevich inequality of
Chapter B applies) and `Infinite G` into finite `2`-quotients of unbounded order (the levels of
the Martinet tower).

## The argument

Only two of the three components of the interface `IsMaximalTamePro2` are used, and of
`TameSubClause` only its first conjunct:

* `Algebra.IsAlgebraic Q K` -- `K` is the union of its finite dimensional subextensions;
* the *pro-`2` clause* of `TameSubClause K` -- every finite Galois `L/Q` admitting an embedding
  `L -> Q K` has pro-`2` Galois group (which for `Q` is even automatic, since a finite Galois
  extension of `Q` whose Galois group is pro-`2` is nothing but a `2`-power degree extension).

Given `sigma ≠ 1` in `Gamma`, pick `x` with `sigma x ≠ x`.  Since `K/Q` is algebraic, `x` is
integral over `Q`, so `E = Q⟮x⟯` is finite dimensional over `Q`; the normal closure
`L = normalClosure Q E K` of `E` inside `K` is then finite dimensional and Galois over `Q`, and
`x ∈ L`.  Hence `Gal(L/Q)` is a finite `2`-group by the pro-`2` clause, and the restriction map

`phi : Gamma ->* Gal(L/Q)`,

whose kernel is a normal subgroup `N` of finite index in `Gamma`, does not kill `sigma` because
`sigma` moves `x ∈ L`.  Finally `Gamma ⧸ N ≃* phi.range ≤ Gal(L/Q)` is a subgroup of a finite
`2`-group, hence is itself a finite `2`-group.  This separates `sigma` from `1`.

Note what is *not* used: neither the universal property `TameUnivClause` (so the lemma does not
need `K` to be maximal), nor the tameness (`S`-supported different, unramified at the infinite
places) half of `TameSubClause`, nor the relation count.  The statement is the general fact
"the Galois group of an algebraic Galois extension, all of whose finite Galois subextensions are
pro-`2`, is residually a finite `2`-group".

## The formalisation

The heart is the helper `residuallyFiniteTwoGroup_galoisGroup_of_proP`, stated over a *variable*
base field `F` with an abstract pro-`2` hypothesis on all finite Galois subextensions.  This is
deliberate: over `Q` the type `IntermediateField Q K` carries two competing `Q`-algebra
structures (`IntermediateField.algebra'` and the generic `DivisionRing.toRatAlgebra`), which are
only propositionally and not definitionally equal, and which make statements such as
`IsGalois Q ↥L`, `NumberField ↥L` or `AlgEquiv.restrictNormalHom ↥L` fail to elaborate when the
two are mixed.  Over a variable base only `algebra'` is available.  The universe of the abstract
type in the hypothesis is tied to the universe of `K` (both `Type u`), so that the subfield
`↥L`, which lives in the same universe as `K`, can be fed to the hypothesis directly.

The reduction of the target from the helper is then the one-liner turning `TameSubClause K` into
that hypothesis (the `NumberField` instance required by `TameSubClause` is obtained from
`NumberField.of_module_finite`).
-/

set_option autoImplicit false
set_option linter.style.haveILetI false

open scoped Classical

namespace Work.TameArithmetic

universe u

/-- **`Gal(K/F)` is residually a finite `2`-group, given that every finite Galois
subextension of `K/F` has pro-`2` Galois group.**

For a (possibly infinite) algebraic Galois extension `K/F`: if every finite dimensional Galois
`L/F` admitting an `F`-embedding `φ : L →ₐ[F] K` has `IsPGroup 2 (L ≃ₐ[F] L)`, then every
`σ ≠ 1` in `Gal(K/F)` has nontrivial image in a quotient of `Gal(K/F)` which is a finite
`2`-group.

Proof: pick `x` with `σ x ≠ x`; the normal closure `L` of `F⟮x⟯` inside `K` is finite dimensional
and Galois over `F` and contains `x`, so by hypothesis `Gal(L/F)` is a `2`-group; the restriction
map `φ : Gal(K/F) →* Gal(L/F)` has finite image and does not kill `σ`, and its kernel has finite
index with quotient `≃* φ.range ≤ Gal(L/F)`, a finite `2`-group.

The base field is a variable on purpose (see the module docstring): over `F = ℚ` the
`IntermediateField` type carries two non-definitionally-equal `ℚ`-algebra structures. -/
theorem residuallyFiniteTwoGroup_galoisGroup_of_proP {F K : Type u} [Field F] [Field K]
    [Algebra F K] [IsGalois F K] (halb : Algebra.IsAlgebraic F K)
    (hpro : ∀ (L : Type u) [Field L] [Algebra F L] [FiniteDimensional F L] [IsGalois F L]
      (φ : L →ₐ[F] K), Function.Injective φ → IsPGroup 2 (L ≃ₐ[F] L)) :
    Work.ClassFieldTower.ResiduallyFiniteTwoGroup (K ≃ₐ[F] K) := by
  classical
  intro σ hσ
  -- `σ ≠ 1` gives a point moved by `σ`
  have hne : ∃ x : K, σ x ≠ x := by
    by_contra h
    exact hσ (AlgEquiv.ext fun x => by by_contra hx; exact h ⟨x, hx⟩)
  obtain ⟨x, hx⟩ := hne
  -- `E = F⟮x⟯` is finite dimensional over `F`, since `x` is algebraic (hence integral) over `F`
  let E : IntermediateField F K := IntermediateField.adjoin F ({x} : Set K)
  haveI hfdE : FiniteDimensional F E :=
    IntermediateField.finiteDimensional_adjoin
      (fun z _ => IsAlgebraic.isIntegral (halb.isAlgebraic z))
  -- the normal closure `L` of `E` inside `K` is finite dimensional and Galois over `F`
  let L : IntermediateField F K := IntermediateField.normalClosure F E K
  haveI hfdL : FiniteDimensional F L := normalClosure.is_finiteDimensional F E K
  haveI hgalL : IsGalois F L := IsGalois.normalClosure F E K
  haveI hnormL : Normal F L := inferInstance
  -- `Gal(L/F)` is a `2`-group, by the pro-`2` hypothesis applied to the inclusion `L → K`
  have hpgL : IsPGroup 2 (↥L ≃ₐ[F] ↥L) :=
    hpro ↥L (IntermediateField.val L) (fun a b h => Subtype.ext h)
  -- the restriction map to the finite `2`-group `Gal(L/F)`
  let φ : (K ≃ₐ[F] K) →* (↥L ≃ₐ[F] ↥L) :=
    AlgEquiv.restrictNormalHom (F := F) (K₁ := K) ↥L
  -- `σ` does not act trivially on `L`, since `x ∈ L` and `σ x ≠ x`
  have hφσ : φ σ ≠ 1 := by
    intro h
    have hxmem : x ∈ L :=
      (IntermediateField.subset_adjoin F ({x} : Set K)).trans
        (IntermediateField.le_normalClosure E) (by simp)
    have h1 : (φ σ) ⟨x, hxmem⟩ = (1 : ↥L ≃ₐ[F] ↥L) ⟨x, hxmem⟩ := by rw [h]
    have h2 : (↑((φ σ) ⟨x, hxmem⟩) : K) = (↑(⟨x, hxmem⟩ : ↥L) : K) := by rw [h1]; rfl
    rw [AlgEquiv.restrictNormalHom_apply L σ ⟨x, hxmem⟩] at h2
    exact hx h2
  haveI : Finite (↥L ≃ₐ[F] ↥L) := Finite.of_fintype _
  -- the kernel of the restriction is a normal subgroup of finite index with `2`-group quotient
  let N : Subgroup (K ≃ₐ[F] K) := φ.ker
  have hN : N.Normal := MonoidHom.normal_ker φ
  haveI : N.Normal := hN
  refine ⟨N, hN, ?_, ?_, ?_⟩
  · -- `Gal(K/F) ⧸ N ≃* φ.range`, a subgroup of the finite group `Gal(L/F)`
    exact Finite.of_equiv φ.range (QuotientGroup.quotientKerEquivRange φ).symm.toEquiv
  · -- a subgroup of a finite (hence here `2`-)group is a `2`-group
    have hpgrange : IsPGroup 2 ↥(φ.range) :=
      hpgL.of_injective (Subgroup.subtype φ.range) Subtype.coe_injective
    exact hpgrange.of_equiv (QuotientGroup.quotientKerEquivRange φ).symm
  · -- `σ ∉ N`, i.e. `σ` survives in `Gal(K/F) ⧸ N`
    intro h
    have hmem : σ ∈ N :=
      (QuotientGroup.eq_one_iff (N := N) σ).mp (by simpa [QuotientGroup.mk'_apply] using h)
    exact hφσ hmem

/-- **`Γ = Gal(K/ℚ)` is residually a finite `2`-group** for a maximal tame pro-`2` extension `K`
of `ℚ` (`IsMaximalTamePro2 K`): every `σ ≠ 1` survives in a quotient of `Γ` which is a finite
`2`-group.

This is `ResiduallyFiniteTwoGroup (K ≃ₐ[ℚ] K)` (`Work.ClassFieldTower.ProTwoDefs`), one of the
hypotheses of the Golod--Shafarevich interface of the tame route.

Only `Algebra.IsAlgebraic ℚ K` and the pro-`2` clause of `TameSubClause K` are used: the finite
Galois subextensions `L ⊆ K` have pro-`2` Galois group, so the restriction maps
`Γ →* Gal(L/ℚ)` exhibit arbitrarily fine finite `2`-group quotients; the maximality of `K`
(its universal property) and the tameness of the subextensions are not needed here. -/
theorem residuallyFiniteTwoGroup_galoisGroup_tame {K : Type} [Field K] [Algebra ℚ K] [IsGalois ℚ K]
    (hmax : Work.TameArithmetic.IsMaximalTamePro2 K) :
    Work.ClassFieldTower.ResiduallyFiniteTwoGroup (K ≃ₐ[ℚ] K) := by
  have halb : Algebra.IsAlgebraic ℚ K := hmax.1
  have hsub : Work.TameArithmetic.TameSubClause K := hmax.2.2
  exact residuallyFiniteTwoGroup_galoisGroup_of_proP halb (fun L _ _ _ _ φ hφ => by
    haveI : NumberField L := NumberField.of_module_finite ℚ L
    exact (hsub L φ hφ).1)

end Work.TameArithmetic
