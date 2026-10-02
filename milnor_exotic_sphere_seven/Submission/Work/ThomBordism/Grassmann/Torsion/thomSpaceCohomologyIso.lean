import Mathlib
import Submission.Work.ThomBordism.Grassmann.Torsion.ThomSpaceCohomologyCompare
import Submission.Work.ThomBordism.Grassmann.Torsion.contractibleFar

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option linter.style.haveILetI false
set_option linter.unusedSimpArgs false

/-!
# `Hⁿ(Th γ; ℤ) ≅ Hⁿ(E, E∖0; ℤ)` in every degree `n ≥ 1`

The Thom space of the tautological bundle is the one-point compactification `T = OnePoint E`,
`E = (tautologicalBundle k m).TotalSpace`.  For `n ≥ 1` its cohomology is the relative cohomology of
the Thom pair `(E, E∖0)`:

  `Hⁿ(T; ℤ) ≅ Hⁿ(E, E∖0; ℤ) = OpenThom γ n`.

The chain of isomorphisms (the route of the project lead, `Grassmann/README.md` §4ter) is

1. `Hⁿ(T) ≅ Hⁿ(T, {∞})`: the long exact sequence of the pair `(T, {∞})`, where the connecting map
   `H^{n-1}({∞}) → Hⁿ(T, {∞})` vanishes.  For `n ≥ 2` this is the vanishing `H^{n-1}({∞}) = 0` of a
   contractible space; for `n = 1` it is the surjectivity of `H⁰(T) → H⁰({∞})`, which holds for
   *every* nonempty space — the constant map `T → {∞}` is a section of `{∞} ↪ T`, so it is a
   split epimorphism of cohomology groups (`restrCoh_singleton_zero_surjective`).  This is the step
   that the degree-`(k+8)` comparison `thomSpaceCohomologyCompare` could not do at `n = 1`.
2. `Hⁿ(T, {∞}) ≅ Hⁿ(T, far 1)`: the pairs `(T, {∞})` and `(T, far 1)` have the same relative
   cohomology, because `far 1` deformation retracts onto `{∞}` along the radial push `pushF`
   (`subsingleton_relCoh_far_singleton`: an explicit homotopy equivalence of pairs with
   `(far 1, {∞}) ≃ ({∞}, {∞})`, whose relative cohomology vanishes in every degree).
3. the chain of `thomSpaceCohomologyCompare` from `Hⁿ(T, far 1)` to `OpenThom γ n`: excision for the
   open cover `near 2 ∪ far 1 = T` (which requires only openness and the covering relation), the
   homeomorphism `near 2 ≅ {fibN < 2}`, the shrinking of the annulus and the radial retraction of
   the total space onto the disc — every one of these is available in arbitrary degree, so only
   steps 1 and 2 had to be handled here.
-/

namespace Work.ThomBordism.Grassmann.Torsion

open CategoryTheory
open Work.ThomBordism.Grassmann

noncomputable section

/-! ## The flip of the unit interval -/

/-- The homotopy parameter flip `t ↦ 1 - t` on the unit interval, used to run the radial push
`pushF` backwards (from the collapsed end `∞` to the identity). -/
def flipI (t : unitInterval) : unitInterval :=
  ⟨1 - (t : ℝ), sub_nonneg.mpr t.2.2, by linarith [t.2.1]⟩

@[simp] theorem flipI_zero : flipI 0 = 1 := by ext; simp [flipI]

@[simp] theorem flipI_one : flipI 1 = 0 := by ext; simp [flipI]

theorem continuous_flipI : Continuous flipI :=
  Continuous.subtype_mk (f := fun t : unitInterval => 1 - (t : ℝ))
    (continuous_const.sub continuous_subtype_val)
    (fun t => ⟨sub_nonneg.mpr t.2.2, by linarith [t.2.1]⟩)

/-! ## The pair `(T, {∞})`: the long exact sequence when only `H⁰` is non-trivial -/

/-- **The forgetful map `H^{m+1}(X,A) → H^{m+1}(X)` is bijective** as soon as the connecting map
`H^m(A) → H^{m+1}(X,A)` vanishes and `H^{m+1}(A) = 0`.  This is the form of the pair long exact
sequence that is stable under taking `m = 0`: at `m = 0` the vanishing of `H⁰(A)` (which is false for
a nonempty `A`) is replaced by the vanishing of the connecting map. -/
theorem relToAbs_bijective_of_pairδC_eq_zero {X : Type} [TopologicalSpace X] (A : Set X) (m : ℕ)
    (hδ : Work.Thom.pairδC A m = 0)
    (hA : Subsingleton (Work.Thom.Coh ℤ (m + 1) A)) :
    Function.Bijective (Work.Thom.relToAbs ℤ A (m + 1)).hom := by
  haveI := hA
  have hmono : CategoryTheory.Mono (Work.Thom.relToAbs ℤ A (m + 1)) := by
    have hf : (ShortComplex.mk (Work.Thom.pairδC A m) (Work.Thom.relToAbs ℤ A (m + 1))
        (Work.Thom.pairδC_comp_relToAbs A m)).f = 0 := hδ
    exact (CategoryTheory.ShortComplex.exact_iff_mono _ hf).mp (Work.Thom.pairExact₁ A m)
  have hepi : CategoryTheory.Epi (Work.Thom.relToAbs ℤ A (m + 1)) := by
    have hg : (ShortComplex.mk (Work.Thom.relToAbs ℤ A (m + 1)) (Work.Thom.restrCoh A ℤ (m + 1))
        (Work.Thom.relToAbs_comp_CohMap_subtype ℤ A (m + 1))).g = 0 :=
      (ModuleCat.isZero_of_subsingleton (Work.Thom.Coh ℤ (m + 1) ↑A)).eq_of_tgt _ 0
    exact (CategoryTheory.ShortComplex.exact_iff_epi _ hg).mp (Work.Thom.pairExact₂ A (m + 1))
  exact ⟨(ModuleCat.mono_iff_injective _).mp hmono, (ModuleCat.epi_iff_surjective _).mp hepi⟩

/-- **The connecting map `H^m(A) → H^{m+1}(X,A)` vanishes when the restriction is surjective**: the
composite `H^m(X) → H^m(A) → H^{m+1}(X,A)` is zero, and a surjection is cancellable. -/
theorem pairδC_eq_zero_of_restrCoh_surjective {X : Type} [TopologicalSpace X] (A : Set X) (m : ℕ)
    (h : Function.Surjective (Work.Thom.restrCoh A ℤ m).hom) :
    Work.Thom.pairδC A m = 0 := by
  haveI : CategoryTheory.Epi (Work.Thom.restrCoh A ℤ m) :=
    (ModuleCat.epi_iff_surjective _).mpr h
  have hcomp : Work.Thom.restrCoh A ℤ m ≫ Work.Thom.pairδC A m
      = Work.Thom.restrCoh A ℤ m ≫ 0 := by
    rw [Work.Thom.restrCoh_comp_pairδC A m]
    simp
  exact (CategoryTheory.cancel_epi (Work.Thom.restrCoh A ℤ m)).mp hcomp

/-- **The restriction `H⁰(X) → H⁰({x₀})` to a point is surjective**, for every topological space
`X` and every `x₀ : X`.  This needs no connectedness of `X`: the constant map `X → {x₀}` is a
section of the inclusion `{x₀} ↪ X`, so by functoriality of `H⁰` the restriction is split
surjective. -/
theorem restrCoh_singleton_zero_surjective {X : Type} [TopologicalSpace X] (x₀ : X) :
    Function.Surjective (Work.Thom.restrCoh ({x₀} : Set X) ℤ 0).hom := by
  let c : C(X, ↥({x₀} : Set X)) := ContinuousMap.const X ⟨x₀, rfl⟩
  have hcomp : c.comp (Work.Thom.subtypeMap ({x₀} : Set X))
      = ContinuousMap.id ↥({x₀} : Set X) := by
    ext y
    change x₀ = (y : X)
    simpa using y.2.symm
  have h1 : Work.Thom.CohMap (c.comp (Work.Thom.subtypeMap ({x₀} : Set X))) ℤ 0
      = Work.Thom.CohMap c ℤ 0 ≫ Work.Thom.CohMap (Work.Thom.subtypeMap ({x₀} : Set X)) ℤ 0 :=
    Work.Thom.CohMap_comp _ _ ℤ 0
  rw [hcomp, Work.Thom.CohMap_id] at h1
  have h2 : LinearMap.id = (Work.Thom.CohMap (Work.Thom.subtypeMap ({x₀} : Set X)) ℤ 0).hom.comp
      (Work.Thom.CohMap c ℤ 0).hom := by
    have hh := congrArg ModuleCat.Hom.hom h1
    simpa [ModuleCat.hom_comp, ModuleCat.hom_id] using hh
  intro y
  refine ⟨(Work.Thom.CohMap c ℤ 0).hom y, ?_⟩
  have hh := LinearMap.congr_fun h2 y
  simpa using hh.symm

/-- **The connecting map of the pair `(X, {x₀})` vanishes in every degree**: for `j = 0` this is
`restrCoh_singleton_zero_surjective`, and for `j ≥ 1` the target `H^j({x₀})` of the restriction is
zero, so the restriction is trivially surjective. -/
theorem pairδC_singleton_eq_zero {X : Type} [TopologicalSpace X] (x₀ : X) (j : ℕ) :
    Work.Thom.pairδC ({x₀} : Set X) j = 0 := by
  rcases Nat.eq_zero_or_pos j with h0 | hpos
  · subst h0
    exact pairδC_eq_zero_of_restrCoh_surjective _ 0 (restrCoh_singleton_zero_surjective x₀)
  · haveI : ContractibleSpace ↥({x₀} : Set X) := inferInstance
    haveI : Subsingleton (Work.Thom.Coh ℤ j ↥({x₀} : Set X)) := by
      rw [show j = (j - 1) + 1 from (Nat.sub_add_cancel hpos).symm]
      exact subsingleton_cohomology_of_contractible (X := TopCat.of ↥({x₀} : Set X)) (j - 1)
    exact pairδC_eq_zero_of_restrCoh_surjective _ j (fun _ => ⟨0, Subsingleton.elim _ _⟩)

/-! ## The pair `(far 1, {∞})` is acyclic -/

/-- **The pair `(far 1, {∞})` has vanishing relative cohomology in every degree.**  The radial push
`pushF` restricts to a deformation of `far 1` onto `{∞}`, so `(far 1, {∞})` is homotopy equivalent,
as a pair, to `({∞}, {∞})`, whose relative cohomology vanishes.  Note that no connectivity of
`far 1` is used: the homotopy is exhibited explicitly, so the statement covers degree `0` too. -/
theorem subsingleton_relCoh_far_singleton (k m j : ℕ) :
    Subsingleton (Work.Thom.RelCoh ℤ j ↥(far k m 1)
      ((Subtype.val : ↥(far k m 1) → TP k m) ⁻¹' ({OnePoint.infty} : Set (TP k m)))) := by
  let Y := ↥({OnePoint.infty} : Set (TP k m))
  haveI : Subsingleton Y := ⟨fun a b => Subtype.ext (a.2.trans b.2.symm)⟩
  let g : C(Y, ↥(far k m 1)) :=
    ⟨fun _ => ⟨OnePoint.infty, infty_mem_far k m 1⟩, continuous_const⟩
  let f : C(↥(far k m 1), Y) := ContinuousMap.const _ ⟨OnePoint.infty, rfl⟩
  have hf : ∀ x ∈ ((Subtype.val : ↥(far k m 1) → TP k m) ⁻¹' ({OnePoint.infty} : Set (TP k m))),
      f x ∈ (Set.univ : Set Y) := fun _ _ => trivial
  have hg : ∀ y ∈ (Set.univ : Set Y),
      g y ∈ ((Subtype.val : ↥(far k m 1) → TP k m) ⁻¹' ({OnePoint.infty} : Set (TP k m))) := by
    intro y _
    show (OnePoint.infty : TP k m) ∈ ({OnePoint.infty} : Set (TP k m))
    exact rfl
  have hcont : Continuous fun q : ↥unitInterval × ↥(far k m 1) =>
      pushF k m (flipI q.1) (q.2 : TP k m) :=
    (continuous_pushF_far k m).comp
      (continuous_snd.prodMk (continuous_flipI.comp continuous_fst))
  let Φ : C(↥unitInterval × ↥(far k m 1), ↥(far k m 1)) :=
    ⟨fun q => ⟨pushF k m (flipI q.1) (q.2 : TP k m),
        mem_far_pushF k m q.2.2 (flipI q.1)⟩,
      Continuous.subtype_mk hcont (fun q => mem_far_pushF k m q.2.2 (flipI q.1))⟩
  let P : (g.comp f).Homotopy (ContinuousMap.id ↥(far k m 1)) :=
    { toContinuousMap := Φ
      map_zero_left := fun x => Subtype.ext (by
        show pushF k m (flipI 0) (x : TP k m) = OnePoint.infty
        rw [flipI_zero]; exact pushF_one k m (x : TP k m))
      map_one_left := fun x => Subtype.ext (by
        show pushF k m (flipI 1) (x : TP k m) = (x : TP k m)
        rw [flipI_one]; exact pushF_zero k m (x : TP k m)) }
  let Q : (f.comp g).Homotopy (ContinuousMap.id Y) :=
    { toContinuousMap := ⟨fun q => q.2, continuous_snd⟩
      map_zero_left := fun _ => Subsingleton.elim _ _
      map_one_left := fun _ => rfl }
  have hP : ∀ t x, x ∈ ((Subtype.val : ↥(far k m 1) → TP k m) ⁻¹'
      ({OnePoint.infty} : Set (TP k m))) →
      P (t, x) ∈ ((Subtype.val : ↥(far k m 1) → TP k m) ⁻¹' ({OnePoint.infty} : Set (TP k m))) := by
    intro t x hx
    show pushF k m (flipI t) (x : TP k m) ∈ ({OnePoint.infty} : Set (TP k m))
    rw [hx, pushF_infty]
    rfl
  have hQ : ∀ t y, y ∈ (Set.univ : Set Y) → Q (t, y) ∈ Set.univ := fun _ _ _ => trivial
  have hbij := relCohMap_pairHomotopy
    ((Subtype.val : ↥(far k m 1) → TP k m) ⁻¹' ({OnePoint.infty} : Set (TP k m)))
    (Set.univ : Set Y) f g hf hg P hP Q hQ j
  haveI : Subsingleton (Work.Thom.RelCoh ℤ j Y Set.univ) :=
    Work.Cohomology.relCohomology_univ_vanishing (TopCat.of Y) j
  refine ⟨fun a b => ?_⟩
  have e : (Work.Thom.RelCoh ℤ j Y Set.univ) ≃ₗ[ℤ]
      (Work.Thom.RelCoh ℤ j ↥(far k m 1) ((Subtype.val : ↥(far k m 1) → TP k m) ⁻¹'
        ({OnePoint.infty} : Set (TP k m)))) :=
    LinearEquiv.ofBijective _ hbij
  have h1 : e.symm a = e.symm b := Subsingleton.elim _ _
  have h2 := congrArg e h1
  simpa using h2

/-! ## The comparison in degree `j + 1` -/

/-- **The comparison in every positive degree**: `H^{j+1}(Th γ) ≅ H^{j+1}(E, E∖0)`.  The degree is
written as `j + 1` because every step of the geometric chain (excision, the homeomorphism onto the
disc, the annulus shrinking, the radial retraction) is naturally stated with the relative degree
one lower. -/
theorem thomSpaceCohomologyIso_aux (k m j : ℕ) :
    Nonempty (Work.Thom.Coh ℤ (j + 1) (TautologicalThomSpace k m) ≃ₗ[ℤ]
      Work.Thom.OpenThom (tautologicalBundle k m) (j + 1)) := by
  -- the vanishing of `H^{j+1}({∞})`, the point being contractible
  have hA : Subsingleton (Work.Thom.Coh ℤ (j + 1) ↥({OnePoint.infty} : Set (TP k m))) := by
    haveI : ContractibleSpace ↥({OnePoint.infty} : Set (TP k m)) := inferInstance
    exact subsingleton_cohomology_of_contractible
      (X := TopCat.of ↥({OnePoint.infty} : Set (TP k m))) j
  -- step 1: `H^{j+1}(T) ≅ H^{j+1}(T, {∞})`
  have e1 := LinearEquiv.ofBijective
    (Work.Thom.relToAbs ℤ ({OnePoint.infty} : Set (TP k m)) (j + 1)).hom
    (relToAbs_bijective_of_pairδC_eq_zero ({OnePoint.infty} : Set (TP k m)) j
      (pairδC_singleton_eq_zero (OnePoint.infty : TP k m) j) hA)
  -- step 2: `H^{j+1}(T, {∞}) ≅ H^{j+1}(T, far 1)`
  obtain ⟨e2⟩ := relCohomology_iso_of_tripleVanishing (TopCat.of (TautologicalThomSpace k m))
    ({OnePoint.infty} : Set (TP k m)) (far k m 1)
    (fun x hx => by obtain rfl : x = OnePoint.infty := hx; exact infty_mem_far k m 1)
    (fun j' => subsingleton_relCoh_far_singleton k m j') j
  -- step 3: excision for the open cover `near 2 ∪ far 1 = T`
  obtain ⟨e3⟩ := relCohomology_iso_of_open_cover (TopCat.of (TautologicalThomSpace k m))
    (near k m 2) (far k m 1) (isOpen_near k m 2) (isOpen_far_one k m)
    (near_union_far k m (by norm_num)) (j + 1)
  -- step 4: the homeomorphism of pairs induced by `OnePoint.some`
  have he : ∀ x : ↥(discSet k m),
      x ∈ {x : ↥(discSet k m) | 1 < fibN k m x.val} ↔
        homeoNear k m 2 x ∈ {y : ↥(near k m 2) | (y : TP k m) ∈ far k m 1} := by
    intro x
    simp [homeoNear_apply_coe, some_mem_far_iff]
  have e4 := LinearEquiv.ofBijective
    (Work.Thom.relCohMap (homeoNear k m 2)
      {x : ↥(discSet k m) | 1 < fibN k m x.val}
      {y : ↥(near k m 2) | (y : TP k m) ∈ far k m 1} (fun x hx => (he x).mp hx) ℤ (j + 1)).hom
    (Work.Thom.bijective_relCohMap_of_homeomorphA
      {x : ↥(discSet k m) | 1 < fibN k m x.val}
      {y : ↥(near k m 2) | (y : TP k m) ∈ far k m 1} (homeoNear k m 2) he ℤ (j + 1))
  -- step 5: the annulus is replaced by the punctured disc
  obtain ⟨e5⟩ := discPairIso k m j
  -- step 6: the radial retraction of the total space onto the disc
  obtain ⟨e6⟩ := puncturedDiscPairIso k m (j + 1)
  exact ⟨(e1.symm.trans e2.symm).trans (e3.toLinearEquiv.trans (e4.trans (e5.trans e6)))⟩

/-- **The cohomology of the Thom space is the relative cohomology of the Thom pair**: for
`T = OnePoint (TotalSpace γ)`, `H^n(T; ℤ) ≅ H^n(E, E∖0; ℤ) = OpenThom γ n` for `n ≥ 1`.

Route (the project lead's, `Grassmann/README.md` §4ter): `H^n(T) ≅ H^n(T, {∞}) ≅ H^n(T, T∖G) ≅
H^n(E, E∖0)`, where the middle isomorphism is the deformation retraction of `T∖G = (E∖0) ∪ {∞}`
onto `{∞}` by the fibrewise scaling `v ↦ v/t` (`t ↘ 0`), continuous at `∞` because `G` is compact,
and the last is excision of the closed `{∞}` inside the open `T∖G`.

For `n ≥ 2` the already-proved `Work.ThomBordism.Grassmann.Torsion.thomSpaceCohomologyCompare`
(in degree `k+8`) shows the pattern; it uses
`Work.ThomBordism.Grassmann.relCoh_equiv_cohomology_of_subsingleton`, which needs the vanishing of
`H^{n-1}` and `H^n` of `far k m 1` — available for `n ≥ 2` from `Torsion.contractibleFar` and
`Work.Cohomology.subsingleton_cohomology_of_contractible`, but **not** at `n = 1`, where
`H^0` of the contractible `far 1` is `ℤ ≠ 0`; the case `n = 1` needs the pair LES (or the
surjectivity of `H^0(T) → H^0(far 1)`) instead. -/
theorem thomSpaceCohomologyIso (k m n : ℕ) (hn : 1 ≤ n) :
    Nonempty ((Work.Thom.Coh ℤ n (Work.ThomBordism.Grassmann.TautologicalThomSpace k m)) ≃ₗ[ℤ]
      (Work.Thom.OpenThom (Work.ThomBordism.Grassmann.tautologicalBundle k m) n)) := by
  rw [show n = n - 1 + 1 from (Nat.sub_add_cancel hn).symm]
  exact thomSpaceCohomologyIso_aux k m (n - 1)

end

end Work.ThomBordism.Grassmann.Torsion
