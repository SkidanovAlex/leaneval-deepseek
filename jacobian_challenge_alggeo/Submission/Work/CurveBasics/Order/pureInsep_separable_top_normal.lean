import Mathlib
import Submission.Work.CurveBasics.Basic

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.CurveBasics.Order

open IntermediateField Module Polynomial

/-- The fixed field of the full group of `K`-automorphisms of a finite normal extension `L / K`
is contained in the relative perfect closure `perfectClosure K L`; equivalently, every element of
`L` fixed by all `K`-automorphisms is purely inseparable over `K`.

The proof uses that, `L / K` being normal, the images of `x` under the `K`-algebra endomorphisms
of `L` are exactly the roots in `L` of `minpoly K x`
(`Algebra.IsAlgebraic.range_eval_eq_rootSet_minpoly_of_splits`).  If all of those endomorphisms
fix `x`, then `minpoly K x` has the single root `x`, hence separable degree one, which is exactly
the criterion for being in the relative perfect closure
(`mem_perfectClosure_iff_natSepDegree_eq_one`). -/
theorem fixedField_le_perfectClosure {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [Normal K L] :
    IntermediateField.fixedField (⊤ : Subgroup Gal(L/K)) ≤ perfectClosure K L := by
  classical
  intro x hx
  rw [mem_perfectClosure_iff_natSepDegree_eq_one]
  have hfix : ∀ ψ : L →ₐ[K] L, ψ x = x := by
    intro ψ
    have hmem := (IntermediateField.mem_fixedField_iff (⊤ : Subgroup Gal(L/K)) x).mp hx
    have := hmem ((algEquivEquivAlgHom K L).symm ψ) (Subgroup.mem_top _)
    simpa using this
  have hrange : Set.range (fun ψ : L →ₐ[K] L => ψ x) = (minpoly K x).rootSet L :=
    Algebra.IsAlgebraic.range_eval_eq_rootSet_minpoly_of_splits (F := K) (K := L) L
      (fun y => Normal.splits' y) x
  have hsing : Set.range (fun ψ : L →ₐ[K] L => ψ x) = ({x} : Set L) := by
    ext y
    constructor
    · rintro ⟨ψ, rfl⟩
      simpa using (hfix ψ)
    · intro hy
      exact ⟨IsScalarTower.toAlgHom K L L, by simpa using (Set.mem_singleton_iff.mp hy).symm⟩
  have hroot : (minpoly K x).rootSet L = ({x} : Set L) := hrange ▸ hsing
  rw [Polynomial.natSepDegree_eq_of_splits (minpoly K x) (Normal.splits' x)]
  have hfin : ((minpoly K x).aroots L).toFinset = ({x} : Finset L) := by
    apply Finset.coe_injective
    rw [← Polynomial.rootSet_def, hroot]
    simp
  rw [hfin]
  simp

/-- If `L / K` is a finite **normal** extension, then `L` is separable over the relative perfect
closure `perfectClosure K L` (equivalently, `L` is separable over the fixed field of `Gal(L/K)`).

The proof compares two ways of counting degrees.  On the one hand
`finSepDegree K L = Nat.card Gal(L/K)` (`Normal.algHomEquivAut`), and on the other hand
`finSepDegree K (perfectClosure K L) = 1` because `perfectClosure K L / K` is purely inseparable,
so the tower law for the separable degree gives
`finSepDegree (perfectClosure K L) L = Nat.card Gal(L/K)`.  Meanwhile
`finrank (perfectClosure K L) L ≤ finrank F L = Nat.card Gal(L/K)` for
`F = fixedField ⊤`, using `fixedField_le_perfectClosure`.  Hence the separable degree and the
degree of `L` over `perfectClosure K L` agree, which is precisely separability
(`Field.finSepDegree_eq_finrank_iff`). -/
theorem isSeparable_perfectClosure_of_normal {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [Normal K L] :
    Algebra.IsSeparable ↥(perfectClosure K L) L := by
  classical
  have h1 : finrank ↥(perfectClosure K L) L ≤ Nat.card Gal(L/K) := by
    have h := IntermediateField.finrank_le_of_le_left
      (F := IntermediateField.fixedField (⊤ : Subgroup Gal(L/K)))
      (E := perfectClosure K L) (L := L) fixedField_le_perfectClosure
    rw [IntermediateField.finrank_fixedField_eq_card] at h
    exact h.trans (le_of_eq (Nat.card_congr Subgroup.topEquiv.toEquiv))
  have h3 : Field.finSepDegree ↥(perfectClosure K L) L = Nat.card Gal(L/K) := by
    have hsep : Field.finSepDegree K ↥(perfectClosure K L) *
        Field.finSepDegree ↥(perfectClosure K L) L = Field.finSepDegree K L :=
      Field.finSepDegree_mul_finSepDegree_of_isAlgebraic K ↥(perfectClosure K L) L
    have hN : Field.finSepDegree K ↥(perfectClosure K L) = 1 :=
      IsPurelyInseparable.finSepDegree_eq_one K ↥(perfectClosure K L)
    have hKL : Field.finSepDegree K L = Nat.card Gal(L/K) :=
      Nat.card_congr (Normal.algHomEquivAut K (AlgebraicClosure L) L)
    rw [hN, one_mul, hKL] at hsep
    exact hsep
  have hle : Field.finSepDegree ↥(perfectClosure K L) L ≤ finrank ↥(perfectClosure K L) L :=
    Field.finSepDegree_le_finrank _ _
  exact (Field.finSepDegree_eq_finrank_iff _ _).mp (le_antisymm hle (h1.trans h3.ge))

/-- **The general form.** If `L / K` is a finite **normal** extension of fields, then there is an
intermediate field `N` with `N / K` purely inseparable and `L / N` separable; namely the relative
perfect closure `N = perfectClosure K L`. -/
theorem exists_isPurelyInseparable_isSeparable_of_normal {K L : Type*} [Field K] [Field L]
    [Algebra K L] [FiniteDimensional K L] [Normal K L] :
    ∃ N : IntermediateField K L, IsPurelyInseparable K ↥N ∧ Algebra.IsSeparable ↥N L :=
  ⟨perfectClosure K L, inferInstance, isSeparable_perfectClosure_of_normal⟩

open Work.CurveBasics in
/-- If `L / k(x)` is a finite **normal** extension (`x` transcendental), then there is an
intermediate field `k(x) ⊆ N ⊆ L` such that `N/k(x)` is purely inseparable and `L/N` is separable.
(Namely `N = perfectClosure k(x) L`, the largest purely inseparable subextension; normality of
`L/k(x)` is what makes `L/N` separable.) -/
theorem pureInsep_separable_top_normal {k L : Type*} [Field k] [Field L] [Algebra k L]
    (x : L) (hx : Transcendental k x)
    [FiniteDimensional ↥(IntermediateField.adjoin k ({x} : Set L)) L]
    [Normal ↥(IntermediateField.adjoin k ({x} : Set L)) L] :
    ∃ N : IntermediateField ↥(IntermediateField.adjoin k ({x} : Set L)) L,
      IsPurelyInseparable ↥(IntermediateField.adjoin k ({x} : Set L)) ↥N ∧
        Algebra.IsSeparable ↥N L := by
  have _ := hx
  exact exists_isPurelyInseparable_isSeparable_of_normal

end Work.CurveBasics.Order
