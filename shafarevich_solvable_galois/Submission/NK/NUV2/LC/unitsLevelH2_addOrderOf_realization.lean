import Mathlib
import Submission.NK.NUV2.Wall
import Submission.NK.NUV2.ABHN.unitsLevelH2_card
import Submission.NK.HassePrinciple.MuColimit
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The local fundamental class at the level of `UnitsLevelH2`, in the `NK.NUV2.Wall` world

The target of this file is

`NK.NUV2.LC.unitsLevelH2_addOrderOf_realization`:
`∃ x : H²(Gal(M/K_𝔮), Mˣ), addOrderOf x = [M : K_𝔮]`

for `K` a number field, `𝔮` a finite place of `K` and `M` a finite Galois intermediate field of the
separable closure of the `𝔮`-adic completion `K_𝔮` of `K`, where `H²(Gal(M/K_𝔮), Mˣ)` is the level
cohomology `NK.HassePrinciple.UnitsLevelH2 ⊤ M` (with coefficients in `CoeffInt = ULift ℤ`).

The statement is `NK.NUV2.ABHN.unitsLevelH2_addOrderOf` and is proved there, but that module
imports `Submission.Commons.NumberTheory.NumberField.Completion.exists_addOrderOf_eq_finrank_groupCohomology_two_units`,
which defines `Commons.NumberTheory.NumberField.Completion.adicIntegersUnitsRep` and therefore cannot
be imported together with `Submission.NK.NUV2.Wall` (whose import closure contains the older
`Submission.NK.NumberTheory.NumberField.Completion.H2_units_ringOfIntegers_unramified`, which
defines the same constants).  Since the statement mentions `NK.NUV2.KCAll`, which lives in
`Submission/Work/NUV2/Wall.lean`, the proof below re-derives the two ingredients from material that
lives in the `Wall` closure:

* **the level dictionary, additively**: for `V = ⊤` the level group `LevelGroup ⊤ M` is the full
  Galois group `Gal(↥M/K_𝔮)`, so `UnitsLevelH2 ⊤ M = H²(Gal(↥M/K_𝔮), ↥Mˣ)` as additive groups
  (`nonempty_addEquiv_unitsLevelH2_top`);
* **the coefficient-ring transfer, additively** (`CoeffInt → ℤ`), via the ring-agnostic description
  of `H²` by cocycles and coboundaries (`nonempty_addEquiv_groupCohomology_two_coeffTransfer`);
* **the local fundamental class at an arbitrary `p`-adic base**
  (`exists_addOrderOf_eq_finrank_groupCohomology_two_units_local`), obtained from the number-field
  form `exists_addOrderOf_eq_finrank_groupCohomology_two_units_adicCompletion` by realising the
  local extension as a completion of number fields (`exists_galois_adicCompletion_of_finiteDimensional`)
  and transporting along `AddEquiv`s.
-/

open CategoryTheory
open NK.BrauerHasse

namespace NK.NUV2.LC

/-! ## Restriction along a group isomorphism, additively -/

/-- Group cohomology is invariant under restricting a representation along a group isomorphism, as
an additive equivalence: the underlying module does not change, only the action is transported. -/
theorem nonempty_addEquiv_groupCohomology_res_mulEquiv {k G G' : Type} [CommRing k] [Group G]
    [Group G'] (A : Rep k G') (e : G ≃* G') (n : ℕ) :
    Nonempty (groupCohomology (Rep.res e.toMonoidHom A) n ≃+ groupCohomology A n) := by
  refine ⟨(groupCohomology.mapIso (G := G) (H := G') (A := A) (B := Rep.res e.toMonoidHom A) e
    (LinearEquiv.refl k A.V) ?_ n).toLinearEquiv.toAddEquiv⟩
  intro g
  rfl

/-! ## The coefficient-ring transfer, additively -/

/-- **The coefficient-ring transfer for `H²`, additively.**  If `V` carries both a `k`-module and a
`k'`-module structure compatible with the same `G`-action, then the second cohomology groups of the
associated representations are additively isomorphic. -/
theorem nonempty_addEquiv_groupCohomology_two_coeffTransfer {k k' G V : Type} [CommRing k]
    [CommRing k'] [Group G] [AddCommGroup V] [Module k V] [Module k' V] [DistribMulAction G V]
    [SMulCommClass G k V] [SMulCommClass G k' V] :
    Nonempty (groupCohomology (Rep.ofDistribMulAction k G V) 2 ≃+
      groupCohomology (Rep.ofDistribMulAction k' G V) 2) := by
  classical
  have hsurj : Function.Surjective (⇑(groupCohomology.H2π (Rep.ofDistribMulAction k G V))) :=
    (ModuleCat.epi_iff_surjective _).mp inferInstance
  have hsurj' : Function.Surjective (⇑(groupCohomology.H2π (Rep.ofDistribMulAction k' G V))) :=
    (ModuleCat.epi_iff_surjective _).mp inferInstance
  let cast₁ : ↥(groupCohomology.cocycles₂ (Rep.ofDistribMulAction k G V)) →
      ↥(groupCohomology.cocycles₂ (Rep.ofDistribMulAction k' G V)) := fun z => z
  let cast₂ : ↥(groupCohomology.cocycles₂ (Rep.ofDistribMulAction k' G V)) →
      ↥(groupCohomology.cocycles₂ (Rep.ofDistribMulAction k G V)) := fun z => z
  have cast₁_add : ∀ x y, cast₁ (x + y) = cast₁ x + cast₁ y := fun x y => rfl
  have cast₂_add : ∀ x y, cast₂ (x + y) = cast₂ x + cast₂ y := fun x y => rfl
  have wd : ∀ x x' : ↥(groupCohomology.cocycles₂ (Rep.ofDistribMulAction k G V)),
      (⇑(groupCohomology.H2π (Rep.ofDistribMulAction k G V))) x =
        (⇑(groupCohomology.H2π (Rep.ofDistribMulAction k G V))) x' →
      (⇑(groupCohomology.H2π (Rep.ofDistribMulAction k' G V))) (cast₁ x) =
        (⇑(groupCohomology.H2π (Rep.ofDistribMulAction k' G V))) (cast₁ x') := by
    intro x x' h
    have hsub : (⇑(groupCohomology.H2π (Rep.ofDistribMulAction k G V))) (x - x') = 0 := by
      rw [map_sub, h, sub_self]
    have h1 : ⇑(x - x') ∈ groupCohomology.coboundaries₂ (Rep.ofDistribMulAction k G V) :=
      (groupCohomology.H2π_eq_zero_iff (x - x')).mp hsub
    have h2 : ⇑(cast₁ (x - x')) ∈
        groupCohomology.coboundaries₂ (Rep.ofDistribMulAction k' G V) := h1
    have h3 : (⇑(groupCohomology.H2π (Rep.ofDistribMulAction k' G V))) (cast₁ (x - x')) = 0 :=
      (groupCohomology.H2π_eq_zero_iff (cast₁ (x - x'))).mpr h2
    have h4 : (⇑(groupCohomology.H2π (Rep.ofDistribMulAction k' G V))) (cast₁ x) -
        (⇑(groupCohomology.H2π (Rep.ofDistribMulAction k' G V))) (cast₁ x') = 0 := by
      rw [← map_sub]
      exact h3
    exact sub_eq_zero.mp h4
  have wd' : ∀ x x' : ↥(groupCohomology.cocycles₂ (Rep.ofDistribMulAction k' G V)),
      (⇑(groupCohomology.H2π (Rep.ofDistribMulAction k' G V))) x =
        (⇑(groupCohomology.H2π (Rep.ofDistribMulAction k' G V))) x' →
      (⇑(groupCohomology.H2π (Rep.ofDistribMulAction k G V))) (cast₂ x) =
        (⇑(groupCohomology.H2π (Rep.ofDistribMulAction k G V))) (cast₂ x') := by
    intro x x' h
    have hsub : (⇑(groupCohomology.H2π (Rep.ofDistribMulAction k' G V))) (x - x') = 0 := by
      rw [map_sub, h, sub_self]
    have h1 : ⇑(x - x') ∈ groupCohomology.coboundaries₂ (Rep.ofDistribMulAction k' G V) :=
      (groupCohomology.H2π_eq_zero_iff (x - x')).mp hsub
    have h2 : ⇑(cast₂ (x - x')) ∈
        groupCohomology.coboundaries₂ (Rep.ofDistribMulAction k G V) := h1
    have h3 : (⇑(groupCohomology.H2π (Rep.ofDistribMulAction k G V))) (cast₂ (x - x')) = 0 :=
      (groupCohomology.H2π_eq_zero_iff (cast₂ (x - x'))).mpr h2
    have h4 : (⇑(groupCohomology.H2π (Rep.ofDistribMulAction k G V))) (cast₂ x) -
        (⇑(groupCohomology.H2π (Rep.ofDistribMulAction k G V))) (cast₂ x') = 0 := by
      rw [← map_sub]
      exact h3
    exact sub_eq_zero.mp h4
  have hcomp : ∀ z, cast₂ (cast₁ z) = z := fun z => rfl
  have hcomp' : ∀ z, cast₁ (cast₂ z) = z := fun z => rfl
  let F : groupCohomology (Rep.ofDistribMulAction k G V) 2 →
      groupCohomology (Rep.ofDistribMulAction k' G V) 2 :=
    fun y => (groupCohomology.H2π (Rep.ofDistribMulAction k' G V))
      (cast₁ (Function.surjInv hsurj y))
  let F' : groupCohomology (Rep.ofDistribMulAction k' G V) 2 →
      groupCohomology (Rep.ofDistribMulAction k G V) 2 :=
    fun y => (groupCohomology.H2π (Rep.ofDistribMulAction k G V))
      (cast₂ (Function.surjInv hsurj' y))
  have F_add : ∀ y1 y2, F (y1 + y2) = F y1 + F y2 := by
    intro y1 y2
    show (⇑(groupCohomology.H2π (Rep.ofDistribMulAction k' G V)))
        (cast₁ (Function.surjInv hsurj (y1 + y2))) =
      (⇑(groupCohomology.H2π (Rep.ofDistribMulAction k' G V)))
          (cast₁ (Function.surjInv hsurj y1)) +
        (⇑(groupCohomology.H2π (Rep.ofDistribMulAction k' G V)))
          (cast₁ (Function.surjInv hsurj y2))
    have key := wd (Function.surjInv hsurj (y1 + y2))
      (Function.surjInv hsurj y1 + Function.surjInv hsurj y2) (by
        rw [map_add, Function.surjInv_eq hsurj y1, Function.surjInv_eq hsurj y2,
          Function.surjInv_eq hsurj (y1 + y2)])
    rw [key, cast₁_add, map_add]
  have F'_add : ∀ y1 y2, F' (y1 + y2) = F' y1 + F' y2 := by
    intro y1 y2
    show (⇑(groupCohomology.H2π (Rep.ofDistribMulAction k G V)))
        (cast₂ (Function.surjInv hsurj' (y1 + y2))) =
      (⇑(groupCohomology.H2π (Rep.ofDistribMulAction k G V)))
          (cast₂ (Function.surjInv hsurj' y1)) +
        (⇑(groupCohomology.H2π (Rep.ofDistribMulAction k G V)))
          (cast₂ (Function.surjInv hsurj' y2))
    have key := wd' (Function.surjInv hsurj' (y1 + y2))
      (Function.surjInv hsurj' y1 + Function.surjInv hsurj' y2) (by
        rw [map_add, Function.surjInv_eq hsurj' y1, Function.surjInv_eq hsurj' y2,
          Function.surjInv_eq hsurj' (y1 + y2)])
    rw [key, cast₂_add, map_add]
  have F_left : Function.LeftInverse F' F := by
    intro y
    show (⇑(groupCohomology.H2π (Rep.ofDistribMulAction k G V)))
        (cast₂ (Function.surjInv hsurj' (F y))) = y
    have hx := Function.surjInv_eq hsurj' (F y)
    have h := wd' (Function.surjInv hsurj' (F y)) (cast₁ (Function.surjInv hsurj y)) hx
    rw [h, hcomp, Function.surjInv_eq hsurj y]
  have F_right : Function.RightInverse F' F := by
    intro y
    show (⇑(groupCohomology.H2π (Rep.ofDistribMulAction k' G V)))
        (cast₁ (Function.surjInv hsurj (F' y))) = y
    have hx := Function.surjInv_eq hsurj (F' y)
    have h := wd (Function.surjInv hsurj (F' y)) (cast₂ (Function.surjInv hsurj' y)) hx
    rw [h, hcomp', Function.surjInv_eq hsurj' y]
  exact ⟨{ toFun := F, invFun := F', left_inv := F_left, right_inv := F_right, map_add' := F_add }⟩

/-! ## The level dictionary at the top level, additively -/

open NK.HassePrinciple in
/-- **The level dictionary at the top level, additively**: `UnitsLevelH2 ⊤ L` is, up to the change
of coefficient ring `CoeffInt → ℤ`, the second cohomology `H²(Gal(↥L/K), ↥Lˣ)`. -/
theorem nonempty_addEquiv_unitsLevelH2_top {K K' : Type} [Field K] [Field K'] [Algebra K K']
    [IsSepClosure K K'] (L : FiniteGaloisIntermediateField K K') :
    Nonempty (UnitsLevelH2 (K := K) (K' := K') (⊤ : Subgroup Gal(K'/K)) L ≃+
      groupCohomology (Rep.ofAlgebraAutOnUnits K ↥L) 2) := by
  have hres : Nonempty (groupCohomology
      (Rep.res (levelGroupRestrictHom (⊤ : Subgroup Gal(K'/K)) L) (unitsRep K ↥L)) 2 ≃+
      groupCohomology (unitsRep K ↥L) 2) := by
    let e : LevelGroup (⊤ : Subgroup Gal(K'/K)) L ≃* (↥L ≃ₐ[K] ↥L) :=
      MulEquiv.ofBijective (levelGroupRestrictHom (⊤ : Subgroup Gal(K'/K)) L)
        ⟨NK.NUV2.ABHN.levelGroupRestrictHom_top_injective L,
          NK.NUV2.ABHN.levelGroupRestrictHom_top_surjective L⟩
    have he : e.toMonoidHom = levelGroupRestrictHom (⊤ : Subgroup Gal(K'/K)) L :=
      MonoidHom.ext fun _ => rfl
    have h : Nonempty (groupCohomology (Rep.res e.toMonoidHom (unitsRep K ↥L)) 2 ≃+
        groupCohomology (unitsRep K ↥L) 2) :=
      nonempty_addEquiv_groupCohomology_res_mulEquiv (unitsRep K ↥L) e 2
    exact he ▸ h
  have hcoeff : Nonempty (groupCohomology (unitsRep K ↥L) 2 ≃+
      groupCohomology (Rep.ofAlgebraAutOnUnits K ↥L) 2) :=
    nonempty_addEquiv_groupCohomology_two_coeffTransfer (k := CoeffInt) (k' := ℤ)
      (G := ↥L ≃ₐ[K] ↥L) (V := Additive (↥L)ˣ)
  obtain ⟨e₁⟩ := hres
  obtain ⟨e₂⟩ := hcoeff
  exact ⟨e₁.trans e₂⟩

/-! ## The local fundamental class at an arbitrary `p`-adic base -/

/-- **The fundamental class at an arbitrary `p`-adic base** (Milne, *CFT*, III.2): for `F` a finite
extension of `Q.adicCompletion K` (`K` a number field, `Q` a finite place) and `E / F` finite
Galois, there is `α ∈ H²(Gal(E/F), Eˣ)` of order `[E : F]`.

Obtained from the published number-field form
`exists_addOrderOf_eq_finrank_groupCohomology_two_units_adicCompletion` by realising `F` and then
`E` as completions of number fields (`exists_algEquiv_adicCompletion_of_finiteDimensional`,
`exists_galois_adicCompletion_of_finiteDimensional`) and transporting along the `AddEquiv`s
`addEquiv_groupCohomology_two_units_baseRingEquiv`, `addEquiv_groupCohomology_two_units_topAlgEquiv`. -/
theorem exists_addOrderOf_eq_finrank_groupCohomology_two_units_local
    {K : Type} [Field K] [NumberField K]
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    {F E : Type} [Field F] [Field E]
    [Algebra (Q.adicCompletion K) F] [Algebra F E] [Algebra (Q.adicCompletion K) E]
    [IsScalarTower (Q.adicCompletion K) F E]
    [FiniteDimensional (Q.adicCompletion K) F] [FiniteDimensional F E]
    [FiniteDimensional (Q.adicCompletion K) E] [IsGalois F E] :
    ∃ α : groupCohomology (Rep.ofAlgebraAutOnUnits F E) 2,
      addOrderOf α = Module.finrank F E := by
  obtain ⟨L : Type, hLf, hLn, hLa, q, hq, ⟨e⟩⟩ :=
    Commons.NumberTheory.NumberField.Completion.exists_algEquiv_adicCompletion_of_finiteDimensional
      (Q := Q) (B := F)
  letI : Field L := hLf
  letI : NumberField L := hLn
  letI : Algebra (Q.adicCompletion K) (q.adicCompletion L) :=
    RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap Q q hq)
  letI : Algebra (q.adicCompletion L) E := ((algebraMap F E).comp e.symm.toRingHom).toAlgebra
  have hhe : (algebraMap (q.adicCompletion L) E).comp e.toRingHom = algebraMap F E := by
    ext x
    show algebraMap (q.adicCompletion L) E (e x) = algebraMap F E x
    rw [show algebraMap (q.adicCompletion L) E = (algebraMap F E).comp e.symm.toRingHom from rfl]
    simp [RingHom.comp_apply]
  haveI : FiniteDimensional (q.adicCompletion L) E :=
    Commons.NumberTheory.NumberField.Completion.finiteDimensional_transport e.toRingEquiv hhe
  haveI : IsGalois (q.adicCompletion L) E :=
    Commons.NumberTheory.NumberField.Completion.isGalois_transport e.toRingEquiv hhe
  obtain ⟨L' : Type, hL'f, hL'n, hL'a, q', hq', hgal', ⟨e'⟩⟩ :=
    Commons.NumberTheory.NumberField.Completion.exists_galois_adicCompletion_of_finiteDimensional
      (Q := q) (B := E)
  letI : Field L' := hL'f
  letI : NumberField L' := hL'n
  letI : Algebra L L' := hL'a
  letI : Algebra (q.adicCompletion L) (q'.adicCompletion L') :=
    RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap q q' hq')
  haveI : FiniteDimensional L L' := Module.Finite.of_restrictScalars_finite ℚ L L'
  haveI : IsGalois L L' := hgal'
  obtain ⟨α', hα'⟩ :=
    Commons.NumberTheory.NumberField.Completion.exists_addOrderOf_eq_finrank_groupCohomology_two_units_adicCompletion
      (L := L) (L' := L') q q' hq'
  obtain ⟨h₂⟩ :=
    Commons.NumberTheory.NumberField.Completion.addEquiv_groupCohomology_two_units_topAlgEquiv
      (F := q.adicCompletion L) e'
  obtain ⟨h₁⟩ :=
    Commons.NumberTheory.NumberField.Completion.addEquiv_groupCohomology_two_units_baseRingEquiv
      (M := F) (M' := q.adicCompletion L) (E := E) e.toRingEquiv hhe
  refine ⟨h₁.symm (h₂.symm α'), ?_⟩
  rw [AddEquiv.addOrderOf_eq, AddEquiv.addOrderOf_eq, hα',
    ← Commons.NumberTheory.NumberField.Completion.finrank_eq_of_algebraMap_eq
      (E := E) e.toRingEquiv hhe,
    (AlgEquiv.toLinearEquiv e').finrank_eq]

/-! ## The target -/

theorem unitsLevelH2_addOrderOf_realization (hKC : NK.NUV2.KCAll) (K : Type) [Field K] [NumberField K] (𝔮 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) (M : FiniteGaloisIntermediateField (𝔮.adicCompletion K) (SeparableClosure (𝔮.adicCompletion K))) : ∃ x : NK.HassePrinciple.UnitsLevelH2 (K := 𝔮.adicCompletion K) (K' := SeparableClosure (𝔮.adicCompletion K)) ⊤ M, addOrderOf x = Module.finrank (𝔮.adicCompletion K) ↥M := by
  obtain ⟨α, hα⟩ :=
    exists_addOrderOf_eq_finrank_groupCohomology_two_units_local (K := K) (Q := 𝔮)
      (F := 𝔮.adicCompletion K) (E := ↥M)
  obtain ⟨e⟩ :=
    nonempty_addEquiv_unitsLevelH2_top (K := 𝔮.adicCompletion K)
      (K' := SeparableClosure (𝔮.adicCompletion K)) M
  exact ⟨e.symm α, by rw [AddEquiv.addOrderOf_eq, hα]⟩

end NK.NUV2.LC
