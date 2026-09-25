import Mathlib
import Submission.Work.TameArithmetic.Defs

/-!
# `Work.TameArithmetic.residuallyFinite_presentedGroup`

The abstract group `presentedGroup P = FreeGroup (Fin 5) ⧸ ⟪rel⟫` presented by a pro-`2`
presentation `P` of `Γ = Gal(K/ℚ)` is **residually finite**.

## The argument

`P.ker_eq` says that the kernel of the presentation map
`FreeGroup.lift P.gen : FreeGroup (Fin 5) →* (K ≃ₐ[ℚ] K)` is *exactly* the normal closure of the
relator set `P.rel`.  Hence `FreeGroup.lift P.gen` descends to an injective homomorphism

`ψ : presentedGroup P →* (K ≃ₐ[ℚ] K)`

(`QuotientGroup.lift` + `QuotientGroup.injective_lift_iff`).  The second input is that the Galois
group of an algebraic Galois extension is residually finite:

`Γ = Gal(K/ℚ)` is the inverse limit of the finite groups `Gal(L/ℚ)` for the finite Galois
subextensions `L ⊆ K` (this is where `Algebra.IsAlgebraic ℚ K` is used: `K` is the union of its
finite Galois subextensions), so for `σ ≠ 1` there is such an `L` with `σ|_L ≠ 1`, and the kernel
of the restriction map `Γ →* Gal(L/ℚ)` is a finite-index normal subgroup not containing `σ`.

Explicitly, `x` with `σ x ≠ x` is algebraic, `E = ℚ⟮x⟯` is finite dimensional over `ℚ`, its
normal closure `L` inside `K` is finite dimensional and Galois over `ℚ`, and the restriction map
`AlgEquiv.restrictNormalHom ↥L : Γ →* (↥L ≃ₐ[ℚ] ↥L)` has finite image and does not kill `σ`
because `x ∈ L`.

Since `ψ` is injective and `Γ` is residually finite, so is `presentedGroup P`: separating
`ψ g` from `1` by a finite quotient of `Γ` and pulling back along `ψ` separates `g` from `1`
in `presentedGroup P`.

Nothing here uses the relation count `P.rel_card ≤ 6` or the density of the generators: the
statement holds for *every* pro-`2` presentation `P` of `Gal(K/ℚ)` over an algebraic Galois
extension `K/ℚ`.

## Main results

* `exists_finiteIndexNormalSubgroup_notMem_algEquiv` -- separation in `Gal(K/F)` for an
  algebraic Galois extension `K/F` (stated over a variable base field `F`, which avoids the
  `IntermediateField.algebra'` / `DivisionRing.toRatAlgebra` instance ambiguity over `ℚ`);
* `residuallyFinite_presentedGroup` -- the target.
-/

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

namespace Work.TameArithmetic

/-- **Separation of points of a Galois group of an algebraic Galois extension.**

For a field extension `K/F` which is algebraic and Galois, every nontrivial element `σ` of
`Gal(K/F)` survives in a finite quotient: there is a finite-index normal subgroup of `Gal(K/F)`
not containing `σ`.

Proof: pick `x` with `σ x ≠ x`.  Since `K/F` is algebraic, `x` is integral over `F`, so
`E = F⟮x⟯` is finite dimensional over `F`, and its normal closure `L` inside `K` is finite
dimensional and Galois over `F`.  The restriction map `AlgEquiv.restrictNormalHom ↥L` has finite
image and its kernel does not contain `σ`, because `x ∈ L` and `σ x ≠ x` force `σ|_L ≠ 1`.

The lemma is stated over a variable base field `F` on purpose: over `F = ℚ` the algebra structure
on an `IntermediateField ↥L` is ambiguous between `IntermediateField.algebra'` and
`DivisionRing.toRatAlgebra`, whereas over a variable `F` only the former is available. -/
theorem exists_finiteIndexNormalSubgroup_notMem_algEquiv {F K : Type*} [Field F] [Field K]
    [Algebra F K] [IsGalois F K] (halb : Algebra.IsAlgebraic F K)
    (σ : K ≃ₐ[F] K) (hσ : σ ≠ 1) :
    ∃ N : FiniteIndexNormalSubgroup (K ≃ₐ[F] K), σ ∉ N := by
  classical
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
  -- the restriction map to the finite group `Gal(L/F)`
  let φ : (K ≃ₐ[F] K) →* (↥L ≃ₐ[F] ↥L) :=
    AlgEquiv.restrictNormalHom (F := F) (K₁ := K) ↥L
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
  haveI : Finite ↥φ.range := Finite.of_injective (Subgroup.subtype φ.range) Subtype.coe_injective
  exact ⟨FiniteIndexNormalSubgroup.ofSubgroup φ.ker, fun hmem => hφσ hmem⟩

/-- **The group presented by a pro-`2` presentation of `Gal(K/ℚ)` is residually finite.**

The presentation map `FreeGroup.lift P.gen` has kernel `⟪P.rel⟫` (`P.ker_eq`), so it descends to
an injective homomorphism `ψ : presentedGroup P →* Gal(K/ℚ)`.  Since `K/ℚ` is algebraic and
Galois, `Gal(K/ℚ)` is residually finite
(`exists_finiteIndexNormalSubgroup_notMem_algEquiv`), and the property passes to the subgroup
`presentedGroup P` along the injective `ψ`. -/
theorem residuallyFinite_presentedGroup {K : Type} [Field K] [Algebra ℚ K] [IsGalois ℚ K]
    (halb : Algebra.IsAlgebraic ℚ K) (P : Work.TameArithmetic.TamePro2Presentation K) :
    Group.ResiduallyFinite (Work.TameArithmetic.presentedGroup P) := by
  classical
  rw [Group.residuallyFinite_iff_exists_finiteIndex]
  intro g hg
  -- the presentation map `FreeGroup.lift P.gen` kills the relators, so it descends to
  -- `ψ : presentedGroup P →* Gal(K/ℚ)`, and `P.ker_eq` makes `ψ` injective
  have hle : Subgroup.normalClosure (P.rel : Set (FreeGroup (Fin 5))) ≤
      MonoidHom.ker (FreeGroup.lift P.gen) := by rw [P.ker_eq]
  let ψ : presentedGroup P →* (K ≃ₐ[ℚ] K) :=
    QuotientGroup.lift (Subgroup.normalClosure (P.rel : Set (FreeGroup (Fin 5))))
      (FreeGroup.lift P.gen) hle
  have hψ : Function.Injective ψ := by
    show Function.Injective
      (QuotientGroup.lift (Subgroup.normalClosure (P.rel : Set (FreeGroup (Fin 5))))
        (FreeGroup.lift P.gen) hle)
    rw [QuotientGroup.injective_lift_iff]
    exact P.ker_eq.symm
  have hψg : ψ g ≠ 1 := fun h1 => hg (hψ (by rw [h1, map_one]))
  -- separate `ψ g` from `1` by a finite quotient of `Gal(K/ℚ)`
  obtain ⟨N, hN⟩ := exists_finiteIndexNormalSubgroup_notMem_algEquiv (F := ℚ) halb (ψ g) hψg
  -- pull that quotient back to `presentedGroup P`
  let f : presentedGroup P →* ((K ≃ₐ[ℚ] K) ⧸ N.toSubgroup) :=
    (QuotientGroup.mk' N.toSubgroup).comp ψ
  haveI : Finite ↥f.range := Finite.of_injective (Subgroup.subtype f.range) Subtype.coe_injective
  refine ⟨f.ker, Subgroup.finiteIndex_ker f, fun hmem => ?_⟩
  have hmk : (QuotientGroup.mk' N.toSubgroup) (ψ g) = 1 := MonoidHom.mem_ker.mp hmem
  exact hN ((QuotientGroup.eq_one_iff (ψ g)).mp (by simpa [QuotientGroup.mk'_apply] using hmk))

end Work.TameArithmetic
