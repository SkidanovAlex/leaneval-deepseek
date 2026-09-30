/-
# Namespace mirror of `Work.SpecLin.Alt.sectionPrime_le_iff_ptPlace_eq_alt`

This file is an exact copy of `Submission/Work/SpecLin/Alt/sectionPrime_le_iff_ptPlace_eq_alt.lean` (module `Work.SpecLin.Alt.sectionPrime_le_iff_ptPlace_eq_alt`), changed in exactly three ways:

* a `namespace Up` / `end Up` pair is inserted immediately inside the file's own namespace, so
  that every declaration `Work.SpecLin.<Area>.<x>` of the original appears here as
  `Work.SpecLin.<Area>.Up.<x>` (this avoids a name clash with the original, which cannot be
  removed: the original is part of the shared library);
* references to declarations *of the mirrored modules* are rewritten accordingly (full and
  area-relative forms), and imports of those modules point at their mirrors;
* an import of `Core/linEquiv_of_sections_of_chart.lean` (the module that *states* the
  affine-chart theorem) is replaced by an import of the upstream vocabulary module
  `Core/chartVocab.lean`, which declares the same chart algebra under the same names.

The point of the mirror is to break the import cycle
`vocabulary -> statement -> ... -> proof modules -> vocabulary`: the proof modules used to take
their vocabulary from the module that states the theorem, and this made a proof of that theorem
unreachable.  The mathematics is unchanged: the mirror is a verbatim copy of verified code.

The statements of the mirrored theorems mention only names that are *upstream* of the mirror, so
`Work.SpecLin.Core.Up.chartSpecialisation` (module
`Submission.Work.SpecLin.Up.Core.chartSpecialisation`) has literally the statement of
`Work.SpecLin.Core.linEquiv_of_sections_of_chart`, which is proved from it.
-/
import Mathlib
import Submission.Work.SpecLin.Alt.chartDictionary
import Submission.Work.SpecLin.Up.Alt.chartTensorMap_isFractionRing
import Submission.Work.SpecLin.Core.sectionPrime_genFibre_eq_ker
import Submission.Work.SpecLin.Up.Core.ordChart
import Submission.Work.SpecLin.Up.Core.linEquiv_of_sections
import Submission.Work.SpecLin.Up.Core.mem_primeIdealOf_ptToPoint_iff
import Submission.Work.SpecLin.Up.Alt.pointDict_prime
import Submission.Work.SpecLin.Alt.exists_mul_eq_iff_of_isLocalization
import Submission.Work.SpecLin.Alt.exists_mul_eq_iff_ordAt_of_primeIdealOf
import Submission.Work.SpecLin.Alt.mem_range_algebraMap_iff_exists_mul_eq
import Submission.Work.SpecLin.Up.Alt.isLocalization_chartTensorSectionsMap
import Submission.Work.SpecLin.Up.Alt.chartTensorPointSetup
import Submission.Work.CurveBasics.Place.mem_valuationSubring_iff
import Submission.Work.CurveBasics.Place.place_eq_of_valuationSubring_eq
import Submission.Work.CurveBasics.Curve.BCSquare.SectionsTensor
import Submission.Work.CurveBasics.BaseChange.isAffineOpen_bcOpens

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


namespace Work.SpecLin.Alt
namespace Up

universe u

open CategoryTheory Limits AlgebraicGeometry
open scoped TensorProduct


set_option linter.style.haveILetI false

variable {K : Type u} [Field K] {C : Work.CurveBasics.Curve K}

/-- **The evaluation at the point of the generic fibre of a section.**

For an affine chart `W ⊆ C`, an `R`-point `s` of `C` landing in `W` and `F = Frac R`, there is a
ring homomorphism `γ : Γ(C_F, W_F) → F` which is the evaluation of sections of the chart `W_F` at
the point `ptToPoint s^F ∈ W_F` of the generic fibre.  It is characterised by

* `Spec.map γ ≫ hU.fromSpec = ptLeft s^F` (it is the pullback along the section),
* `γ (appLE a) = ψ a` where `ψ = (algebraMap R F) ∘ rgMap` is the generic fibre of the section,
* `γ (c · 1) = c` for constants `c ∈ F`. -/
lemma sectionEval_data (R : Type u) [CommRing R] [IsDomain R] [ValuationRing R] [Algebra K R]
    (W : C.left.Opens) (hW : AlgebraicGeometry.IsAffineOpen W) [Nonempty W]
    (s : Work.SpecLin.CurvePt C R)
    (hs : Set.range (s.left.base) ⊆ (W : Set C.left)) :
    ∃ γ : Γ((C.baseChange (FractionRing R)).left, C.bcOpens (FractionRing R) W) →+* FractionRing R,
      (Spec.map (CommRingCat.ofHom γ)
          ≫ (Work.CurveBasics.BaseChange.isAffineOpen_bcOpens (FractionRing R) W hW).fromSpec
        = Work.SpecLin.ptLeft (Work.SpecLin.RPt.map
            (IsScalarTower.toAlgHom K R (FractionRing R)) s))
      ∧ (∀ a : Γ(C.left, W),
          γ (((C.baseChangeFst (FractionRing R)).appLE W
              (C.bcOpens (FractionRing R) W) le_rfl).hom a)
            = (IsScalarTower.toAlgHom K R (FractionRing R))
                (Work.SpecLin.Core.Up.rgMap R W hW s hs a))
      ∧ (∀ c : FractionRing R, γ (algebraMap (FractionRing R)
              Γ((C.baseChange (FractionRing R)).left, C.bcOpens (FractionRing R) W) c) = c) := by
  let F := FractionRing R
  let p : Work.SpecLin.CurveFPt C F := Work.SpecLin.RPt.map (IsScalarTower.toAlgHom K R F) s
  let hU : IsAffineOpen (C.bcOpens F W) := Work.CurveBasics.BaseChange.isAffineOpen_bcOpens F W hW
  have hmem : Work.SpecLin.ptToPoint p ∈ C.bcOpens F W := Work.SpecLin.Alt.ptToPoint_genPt_mem R W s hs
  have hrange : Set.range (Work.SpecLin.ptLeft p).base ⊆ Set.range hU.fromSpec.base := by
    rw [IsAffineOpen.range_fromSpec, Work.SpecLin.Points.range_ptLeft]
    exact Set.singleton_subset_iff.mpr hmem
  let γ₀ : Γ((C.baseChange F).left, C.bcOpens F W) →+* F :=
    (Spec.preimage (IsOpenImmersion.lift hU.fromSpec (Work.SpecLin.ptLeft p) hrange)).hom
  have hfac : Spec.map (CommRingCat.ofHom γ₀) ≫ hU.fromSpec = Work.SpecLin.ptLeft p := by
    rw [CommRingCat.ofHom_hom, Spec.map_preimage]
    exact IsOpenImmersion.lift_fac _ _ _
  have hval_get : γ₀.comp (((C.baseChangeFst F).appLE W (C.bcOpens F W) le_rfl).hom)
      = ((IsScalarTower.toAlgHom K R F).comp (Work.SpecLin.Core.Up.rgMap R W hW s hs)).toRingHom := by
    have hM : Spec.map ((C.baseChangeFst F).appLE W (C.bcOpens F W) le_rfl) ≫ hW.fromSpec
        = hU.fromSpec ≫ C.baseChangeFst F :=
      IsAffineOpen.SpecMap_appLE_fromSpec _ hW hU le_rfl
    have e1 : Spec.map (CommRingCat.ofHom (γ₀.comp
          (((C.baseChangeFst F).appLE W (C.bcOpens F W) le_rfl).hom)))
        = Spec.map (CommRingCat.ofHom γ₀)
          ≫ Spec.map ((C.baseChangeFst F).appLE W (C.bcOpens F W) le_rfl) := by
      rw [show CommRingCat.ofHom (γ₀.comp (((C.baseChangeFst F).appLE W (C.bcOpens F W) le_rfl).hom))
          = (C.baseChangeFst F).appLE W (C.bcOpens F W) le_rfl ≫ CommRingCat.ofHom γ₀ from rfl]
      exact Spec.map_comp _ _
    have hkey : Spec.map (CommRingCat.ofHom (γ₀.comp
          (((C.baseChangeFst F).appLE W (C.bcOpens F W) le_rfl).hom))) ≫ hW.fromSpec
        = Spec.map (CommRingCat.ofHom
            (((IsScalarTower.toAlgHom K R F).comp (Work.SpecLin.Core.Up.rgMap R W hW s hs)).toRingHom))
          ≫ hW.fromSpec := by
      rw [e1, Category.assoc, hM, ← Category.assoc, hfac, Work.SpecLin.ptLeft_fst]
      show Over.Hom.left (Work.SpecLin.RPt.map (IsScalarTower.toAlgHom K R F) s)
        = Over.Hom.left (Work.SpecLin.specOfMap ((IsScalarTower.toAlgHom K R F).comp
            (Work.SpecLin.Core.Up.rgMap R W hW s hs))) ≫ hW.fromSpec
      exact Work.SpecLin.Core.Up.genPtMap_fac R W hW s hs
    have hmain := (cancel_mono hW.fromSpec).mp hkey
    exact congrArg CommRingCat.Hom.hom (Spec.map_injective hmain)
  have hconst : γ₀.comp (algebraMap F Γ((C.baseChange F).left, C.bcOpens F W)) = RingHom.id F := by
    have hstruct : Spec.map (CommRingCat.ofHom (algebraMap F
        Γ((C.baseChange F).left, C.bcOpens F W)))
        = hU.fromSpec ≫ (C.baseChange F).hom :=
      Work.CurveBasics.Curve.specMap_algebraMap_sections (C.baseChange F) hU
    have h1 : Spec.map (CommRingCat.ofHom γ₀)
          ≫ Spec.map (CommRingCat.ofHom (algebraMap F Γ((C.baseChange F).left, C.bcOpens F W)))
        = 𝟙 (Spec (CommRingCat.of F)) := by
      rw [hstruct, ← Category.assoc, hfac]
      exact Work.SpecLin.Points.ptLeft_comp_hom p
    have e2 : Spec.map (CommRingCat.ofHom (γ₀.comp (algebraMap F
          Γ((C.baseChange F).left, C.bcOpens F W))))
        = Spec.map (CommRingCat.ofHom γ₀)
          ≫ Spec.map (CommRingCat.ofHom (algebraMap F Γ((C.baseChange F).left, C.bcOpens F W))) := by
      rw [show CommRingCat.ofHom (γ₀.comp (algebraMap F Γ((C.baseChange F).left, C.bcOpens F W)))
          = CommRingCat.ofHom (algebraMap F Γ((C.baseChange F).left, C.bcOpens F W))
            ≫ CommRingCat.ofHom γ₀ from rfl]
      exact Spec.map_comp _ _
    have hmain : CommRingCat.ofHom (γ₀.comp (algebraMap F Γ((C.baseChange F).left, C.bcOpens F W)))
        = CommRingCat.ofHom (RingHom.id F) := by
      apply Spec.map_injective
      rw [e2, h1]
      exact (Spec.map_id _).symm
    exact congrArg CommRingCat.Hom.hom hmain
  exact ⟨γ₀, hfac, fun a => congrArg (fun f : Γ(C.left, W) →+* F => f a) hval_get,
    fun c => congrArg (fun f : F →+* F => f c) hconst⟩

/-- **The graph equation of the section vanishes at the section's generic-fibre point.**

The generators `a ⊗ 1 - 1 ⊗ (rgMap a)` of the section prime, pushed into the coordinate ring
`Γ(C_F, W_F)` of the generic fibre chart, lie in the prime of the point `ptToPoint s^F`. -/
theorem sectionsMap_generator_mem (R : Type u) [CommRing R] [IsDomain R] [ValuationRing R]
    [Algebra K R] (W : C.left.Opens) (hW : AlgebraicGeometry.IsAffineOpen W) [Nonempty W]
    (s : Work.SpecLin.CurvePt C R)
    (hs : Set.range (s.left.base) ⊆ (W : Set C.left))
    (a : Γ(C.left, W)) :
    Work.SpecLin.Alt.Up.chartTensorSectionsMap R W hW
        (a ⊗ₜ[K] (1 : R) - (1 : Γ(C.left, W)) ⊗ₜ[K] (Work.SpecLin.Core.Up.rgMap R W hW s hs a))
      ∈ ((Work.CurveBasics.BaseChange.isAffineOpen_bcOpens (FractionRing R) W hW).primeIdealOf
          ⟨Work.SpecLin.ptToPoint (Work.SpecLin.RPt.map
              (IsScalarTower.toAlgHom K R (FractionRing R)) s),
            Work.SpecLin.Alt.ptToPoint_genPt_mem R W s hs⟩).asIdeal := by
  obtain ⟨γ, hfac, hval, hconst⟩ := Work.SpecLin.Alt.Up.sectionEval_data R W hW s hs
  have hP : Work.SpecLin.ptToPoint (Work.SpecLin.RPt.map
        (IsScalarTower.toAlgHom K R (FractionRing R)) s)
      = (Work.CurveBasics.BaseChange.isAffineOpen_bcOpens (FractionRing R) W hW).fromSpec
          (Spec.map (CommRingCat.ofHom γ) (IsLocalRing.closedPoint (FractionRing R))) := by
    show (Work.SpecLin.ptLeft (Work.SpecLin.RPt.map
        (IsScalarTower.toAlgHom K R (FractionRing R)) s))
        (IsLocalRing.closedPoint (FractionRing R)) = _
    rw [← hfac]
    rfl
  have hmPker : ((Work.CurveBasics.BaseChange.isAffineOpen_bcOpens (FractionRing R) W hW).primeIdealOf
        ⟨Work.SpecLin.ptToPoint (Work.SpecLin.RPt.map
            (IsScalarTower.toAlgHom K R (FractionRing R)) s),
          Work.SpecLin.Alt.ptToPoint_genPt_mem R W s hs⟩).asIdeal = RingHom.ker γ := by
    rw [Work.SpecLin.Core.Up.primeIdealOf_eq_of_fromSpec_eq _
      γ _ (Work.SpecLin.Alt.ptToPoint_genPt_mem R W s hs) hP]
    rw [PrimeSpectrum.comap_asIdeal, Work.SpecLin.Core.Up.closedPoint_asIdeal_eq_bot (FractionRing R),
      (RingHom.ker_eq_comap_bot γ).symm]
  rw [hmPker, RingHom.mem_ker]
  have h1 : Work.SpecLin.Alt.Up.chartTensorSectionsMap R W hW (a ⊗ₜ[K] (1 : R))
      = ((C.baseChangeFst (FractionRing R)).appLE W
          (C.bcOpens (FractionRing R) W) le_rfl).hom a := by
    rw [Work.SpecLin.Alt.Up.chartTensorSectionsMap_tmul_one, Scheme.Hom.app_eq_appLE]
    rfl
  have h2 : Work.SpecLin.Alt.Up.chartTensorSectionsMap R W hW
        ((1 : Γ(C.left, W)) ⊗ₜ[K] (Work.SpecLin.Core.Up.rgMap R W hW s hs a))
      = algebraMap (FractionRing R) Γ((C.baseChange (FractionRing R)).left,
          C.bcOpens (FractionRing R) W)
          ((IsScalarTower.toAlgHom K R (FractionRing R)) (Work.SpecLin.Core.Up.rgMap R W hW s hs a)) := by
    show (Work.CurveBasics.Curve.BCSquare.sectionsLift
        (Work.CurveBasics.Curve.bcSquare C (FractionRing R)) W hW)
        ((Algebra.TensorProduct.map (AlgHom.id K Γ(C.left, W))
          (IsScalarTower.toAlgHom K R (FractionRing R)))
            ((1 : Γ(C.left, W)) ⊗ₜ[K] (Work.SpecLin.Core.Up.rgMap R W hW s hs a))) = _
    rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
    exact Work.CurveBasics.Curve.BCSquare.sectionsLift_one_tmul _ W hW _
  rw [map_sub, h1, h2, map_sub, sub_eq_zero]
  exact (hval a).trans (hconst _).symm


/-- **The section prime is spanned by the graph equations** `a ⊗ 1 - 1 ⊗ φ a`. -/
theorem sectionPrime_eq_span (R : Type u) [CommRing R] [IsDomain R] [ValuationRing R]
    [Algebra K R] (W : C.left.Opens) (φ : Γ(C.left, W) →ₐ[K] R) :
    Work.SpecLin.Core.sectionPrime (K:=K) (C:=C) R W φ
      = Ideal.span (Set.range (fun a : Γ(C.left, W) =>
          a ⊗ₜ[K] (1 : R) - (1 : Γ(C.left, W)) ⊗ₜ[K] (φ a))) := by
  classical
  apply le_antisymm
  · intro b hb
    have hb' : Work.SpecLin.Core.evChart (K:=K) (C:=C) R W φ b = 0 := RingHom.mem_ker.mp hb
    have hmain : ∀ b : Γ(C.left, W) ⊗[K] R,
        b - Algebra.TensorProduct.includeRight (R := K) (A := Γ(C.left, W)) (B := R)
            (Work.SpecLin.Core.evChart (K:=K) (C:=C) R W φ b)
          ∈ Ideal.span (Set.range (fun a : Γ(C.left, W) =>
              a ⊗ₜ[K] (1 : R) - (1 : Γ(C.left, W)) ⊗ₜ[K] (φ a))) := by
      intro b
      induction b using TensorProduct.inductionOn with
      | tmul a r =>
        have h : (a ⊗ₜ[K] (1 : R) - (1 : Γ(C.left, W)) ⊗ₜ[K] (φ a)) * (1 ⊗ₜ[K] r)
            = a ⊗ₜ[K] r - Algebra.TensorProduct.includeRight (R := K) (A := Γ(C.left, W))
                (B := R) (Work.SpecLin.Core.evChart (K:=K) (C:=C) R W φ (a ⊗ₜ[K] r)) := by
          rw [Work.SpecLin.Core.evChart_tmul, Algebra.TensorProduct.includeRight_apply,
            sub_mul, Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul,
            mul_one, one_mul, one_mul]
        rw [← h]
        exact Ideal.mul_mem_right (1 ⊗ₜ[K] r) (Ideal.span _)
          (Ideal.subset_span (Set.mem_range_self a))
      | add x y hx hy =>
        have h : x + y - Algebra.TensorProduct.includeRight (R := K) (A := Γ(C.left, W)) (B := R)
            (Work.SpecLin.Core.evChart (K:=K) (C:=C) R W φ (x + y))
            = (x - Algebra.TensorProduct.includeRight (R := K) (A := Γ(C.left, W)) (B := R)
                  (Work.SpecLin.Core.evChart (K:=K) (C:=C) R W φ x))
              + (y - Algebra.TensorProduct.includeRight (R := K) (A := Γ(C.left, W)) (B := R)
                  (Work.SpecLin.Core.evChart (K:=K) (C:=C) R W φ y)) := by
          rw [map_add, map_add]
          abel
        rw [h]
        exact Ideal.add_mem _ hx hy
    have h2 := hmain b
    rw [hb', map_zero, sub_zero] at h2
    exact h2
  · rw [Ideal.span_le]
    rintro b ⟨a, rfl⟩
    show Work.SpecLin.Core.evChart (K:=K) (C:=C) R W φ
      (a ⊗ₜ[K] (1 : R) - (1 : Γ(C.left, W)) ⊗ₜ[K] (φ a)) = 0
    rw [map_sub, Work.SpecLin.Core.evChart_tmul, Work.SpecLin.Core.evChart_tmul]
    simp

/-- **Transport of the "fraction" condition along a ring isomorphism.**

If `e : R ≃+* S` and the maps `i : R →+* L`, `j : S →+* L` satisfy `i = j.comp e`, then the sets
of fractions `a/b` with denominator outside a prime `m` of `S` correspond under `e`. -/
lemma fracSet_ringEquiv {R S L : Type*} [CommRing R] [CommRing S] [CommRing L]
    (e : R ≃+* S) (i : R →+* L) (j : S →+* L) (hij : ∀ r : R, i r = j (e r))
    (m : Ideal S) (x : L) :
    (∃ a b : R, b ∉ Ideal.comap (e : R →+* S) m ∧ x * i b = i a) ↔
      (∃ a b : S, b ∉ m ∧ x * j b = j a) := by
  constructor
  · rintro ⟨a, b, hb, hx⟩
    exact ⟨e a, e b, fun h => hb (Ideal.mem_comap.mpr h),
      by rw [← hij a, ← hij b]; exact hx⟩
  · rintro ⟨a, b, hb, hx⟩
    obtain ⟨a', rfl⟩ := e.surjective a
    obtain ⟨b', rfl⟩ := e.surjective b
    exact ⟨a', b', fun h => hb (Ideal.mem_comap.mp h),
      by rw [hij a', hij b']; exact hx⟩
/-- **The generic-fibre dictionary of the affine chart.**

For an affine chart `W ⊆ C` containing the image of an `R`-point `s`, a prime `p` of the relative
chart `B = Γ(C,W) ⊗_K R` which misses all the nonzero scalars of `R` (so that `p` lies over the
generic point of `Spec R`, i.e. defines a point of `W_F`), and a place `Q` of `C_F` whose point
lies in `W_F` and whose valuation subring is the localisation at `p` (encoded by `hQ`), the
section prime `I_m` of `s` is contained in `p` if and only if the generic fibre `s^F` of `s` has
place `Q`. -/
theorem sectionPrime_le_iff_ptPlace_eq_alt {K : Type _} [Field K] {C : Work.CurveBasics.Curve K}
    (R : Type _) [CommRing R] [IsDomain R] [ValuationRing R] [Algebra K R]
    (W : C.left.Opens) (hW : AlgebraicGeometry.IsAffineOpen W) [Nonempty W]
    (s : Work.SpecLin.CurvePt C R)
    (hs : Set.range (s.left.base) ⊆ (W : Set C.left))
    (p : Ideal (Work.SpecLin.Core.chartTensor (K := K) (C := C) R W)) (hp : p.IsPrime)
    (hmiss : ∀ r : R, r ≠ 0 →
      (Algebra.TensorProduct.includeRight (R := K)
        (A := C.left.presheaf.obj (Opposite.op W)) (B := R)) r ∉ p)
    (Q : (C.baseChange (FractionRing R)).Place)
    (hQmem : Q.point ∈ C.bcOpens (FractionRing R) W)
    (hQ : ∀ x : (C.baseChange (FractionRing R)).functionField,
      (∃ a b : Work.SpecLin.Core.chartTensor (K := K) (C := C) R W,
          b ∉ p ∧ x * Work.SpecLin.Alt.Up.chartTensorMap R W hW b
            = Work.SpecLin.Alt.Up.chartTensorMap R W hW a)
        ↔ 0 ≤ (C.baseChange (FractionRing R)).ordAt x Q) :
    Work.SpecLin.Core.sectionPrime R W (Work.SpecLin.Core.Up.rgMap R W hW s hs) ≤ p
      ↔ Work.SpecLin.ptPlace (Work.SpecLin.RPt.map
          (IsScalarTower.toAlgHom K R (FractionRing R)) s) = Q := by
  classical
  let F := FractionRing R
  let A := Γ(C.left, W)
  let B := A ⊗[K] R
  let G := A ⊗[K] F
  let SC := Γ((C.baseChange F).left, C.bcOpens F W)
  let L := (C.baseChange F).functionField
  let φ : A →ₐ[K] R := Work.SpecLin.Core.Up.rgMap R W hW s hs
  let tMap : B →+* G :=
    (Algebra.TensorProduct.map (AlgHom.id K A) (IsScalarTower.toAlgHom K R F)).toRingHom
  let SMap : B →+* SC := Work.SpecLin.Alt.Up.chartTensorSectionsMap R W hW
  let ι : G →+* SC :=
    Work.CurveBasics.Curve.BCSquare.sectionsLift (Work.CurveBasics.Curve.bcSquare C F) W hW
  let evF : G →ₐ[K] F := Algebra.TensorProduct.lift ((IsScalarTower.toAlgHom K R F).comp φ)
    (AlgHom.id K F) (fun _ _ => Commute.all _ _)
  let evRH : G →+* F := evF.toRingHom
  let Q₀ : (C.baseChange F).Place :=
    Work.SpecLin.ptPlace (Work.SpecLin.RPt.map (IsScalarTower.toAlgHom K R F) s)
  let mP : Ideal SC := ((Work.CurveBasics.BaseChange.isAffineOpen_bcOpens F W hW).primeIdealOf
      ⟨Q₀.point, Work.SpecLin.Alt.ptToPoint_genPt_mem R W s hs⟩).asIdeal
  let 𝔪 : Ideal G := Ideal.comap ι mP
  let p' : Ideal G := Ideal.map tMap p
  let M : Submonoid B := (nonZeroDivisors R).map
    (Algebra.TensorProduct.includeRight (R := K) (A := A) (B := R))
  -- ## Set-up: instances
  haveI hAdom : IsDomain A := Function.Injective.isDomain (C.left.germToFunctionField W).hom
    (Scheme.germToFunctionField_injective C.left W)
  have hsections : SMap = ι.comp tMap := rfl
  letI : Algebra B G := tMap.toAlgebra
  letI : Algebra B L := (Work.SpecLin.Alt.Up.chartTensorMap R W hW).toAlgebra
  letI : Algebra G L := ((algebraMap SC L).comp ι).toAlgebra
  have hSTBGL : IsScalarTower B G L := IsScalarTower.of_algebraMap_eq (fun b => rfl)
  have halgBG : (algebraMap B G) = tMap := rfl
  have halgBL : (algebraMap B L) = Work.SpecLin.Alt.Up.chartTensorMap R W hW := rfl
  have halgGL : (algebraMap G L) = (algebraMap SC L).comp ι := rfl
  haveI hIsLoc : IsLocalization M G := by
    haveI hSTAG : IsScalarTower A B G := IsScalarTower.of_algebraMap_eq (fun a => by
      rw [show algebraMap A B a = a ⊗ₜ[K] (1 : R) from rfl]
      show a ⊗ₜ[K] (1 : F) = (Algebra.TensorProduct.map (AlgHom.id K A)
        (IsScalarTower.toAlgHom K R F)) (a ⊗ₜ[K] (1 : R))
      rw [Algebra.TensorProduct.map_tmul]; simp)
    have hH : (algebraMap B G).comp
        (Algebra.TensorProduct.includeRight (R := K) (A := A) (B := R)).toRingHom
        = (Algebra.TensorProduct.includeRight (R := K) (A := A) (B := F)).toRingHom.comp
            (algebraMap R F) := by
      ext r
      show (Algebra.TensorProduct.map (AlgHom.id K A) (IsScalarTower.toAlgHom K R F))
          ((1 : A) ⊗ₜ[K] r) = (1 : A) ⊗ₜ[K] algebraMap R F r
      rw [Algebra.TensorProduct.map_tmul]; simp
    exact IsLocalization.tensorProduct_tensorProduct_right (R := K) (S := A) (A := R)
      (M := nonZeroDivisors R) (B := F) hH
  have hdisj : Disjoint (M : Set B) (p : Set B) := by
    rw [Set.disjoint_left]
    intro x hx hxp
    obtain ⟨m, hm, rfl⟩ := Submonoid.mem_map.mp hx
    exact hmiss m (mem_nonZeroDivisors_iff_ne_zero.mp hm) hxp
  have hunder : Ideal.comap tMap p' = p := by
    haveI : p.IsPrime := hp
    have h := IsLocalization.under_map_of_isPrime_disjoint M G hp hdisj
    change Ideal.comap (algebraMap B G) (Ideal.map (algebraMap B G) p) = p at h
    rwa [halgBG] at h
  have hp'ne : p' ≠ ⊤ := by
    intro h
    have : p = ⊤ := by
      rw [← hunder, h]
      exact Ideal.comap_top
    exact hp.ne_top this
  -- ## (1) the section graph meets the generic fibre at the section's point
  have hD1c : Ideal.map tMap (Work.SpecLin.Core.sectionPrime R W φ) = RingHom.ker evRH := by
    have h := Work.SpecLin.Core.sectionPrime_genFibre_eq_ker (K := K) (A := A) (R := R) φ
    exact h
  have hger : Work.SpecLin.Core.sectionPrime R W φ ≤ Ideal.comap SMap mP := by
    rw [sectionPrime_eq_span, Ideal.span_le]
    rintro b ⟨a, rfl⟩
    exact sectionsMap_generator_mem R W hW s hs a
  have hker𝔪 : RingHom.ker evRH ≤ 𝔪 := by
    rw [← hD1c]
    refine Ideal.map_le_iff_le_comap.mpr ?_
    rw [show 𝔪 = Ideal.comap ι mP from rfl, Ideal.comap_comap tMap ι]
    exact hger
  have hmax : (RingHom.ker evRH).IsMaximal := by
    refine RingHom.ker_isMaximal_of_surjective evRH ?_
    intro c
    refine ⟨(1 : A) ⊗ₜ[K] c, ?_⟩
    change (Algebra.TensorProduct.lift ((IsScalarTower.toAlgHom K R F).comp φ)
      (AlgHom.id K F) (fun _ _ => Commute.all _ _)) ((1 : A) ⊗ₜ[K] c) = c
    rw [Algebra.TensorProduct.lift_tmul]
    simp
  have hmPprime : mP.IsPrime := PrimeSpectrum.isPrime _
  have h𝔪ne : 𝔪 ≠ ⊤ := (hmPprime.comap ι).ne_top
  have hker_eq : RingHom.ker evRH = 𝔪 := hmax.eq_of_le h𝔪ne hker𝔪
  -- ## (2) the left-hand side is `ker evF ≤ p'`
  have hLHS : Work.SpecLin.Core.sectionPrime R W φ ≤ p ↔ RingHom.ker evRH ≤ p' := by
    rw [← hD1c]
    constructor
    · exact Ideal.map_mono
    · intro h
      have h2 : Work.SpecLin.Core.sectionPrime R W φ ≤ Ideal.comap tMap p' :=
        Ideal.map_le_iff_le_comap.mp h
      rwa [hunder] at h2
  -- ## (3) fraction sets at the two points
  have hιbij : Function.Bijective ι :=
    Work.SpecLin.Alt.Up.sectionsLift_bijective (Work.CurveBasics.Curve.bcSquare C F) W hW
  let eι : G ≃+* SC := RingEquiv.ofBijective ι hιbij
  have hfrac_ι : ∀ x : L,
      (∃ a b : G, b ∉ 𝔪 ∧ x * algebraMap G L b = algebraMap G L a)
        ↔ (∃ a b : SC, b ∉ mP ∧ x * algebraMap SC L b = algebraMap SC L a) := by
    intro x
    exact fracSet_ringEquiv eι (algebraMap G L) (algebraMap SC L) (fun r => rfl) mP x
  have hfrac_ord : ∀ x : L,
      (∃ a b : SC, b ∉ mP ∧ x * algebraMap SC L b = algebraMap SC L a)
        ↔ 0 ≤ (C.baseChange F).ordAt x Q₀ := by
    intro x
    exact Work.SpecLin.Alt.exists_mul_eq_iff_ordAt_of_primeIdealOf
      (C := C.baseChange F) (C.bcOpens F W)
      (Work.CurveBasics.BaseChange.isAffineOpen_bcOpens F W hW) Q₀
      (Work.SpecLin.Alt.ptToPoint_genPt_mem R W s hs) x
  have hfrac𝔪 : ∀ x : L,
      (∃ a b : G, b ∉ 𝔪 ∧ x * algebraMap G L b = algebraMap G L a)
        ↔ 0 ≤ (C.baseChange F).ordAt x Q₀ := fun x => (hfrac_ι x).trans (hfrac_ord x)
  have hfrac_p : ∀ x : L,
      (∃ a b : B, b ∉ p ∧ x * algebraMap B L b = algebraMap B L a)
        ↔ (∃ a b : G, b ∉ p' ∧ x * algebraMap G L b = algebraMap G L a) := by
    intro x
    exact Work.SpecLin.Alt.exists_mul_eq_iff_of_isLocalization (R := B) (S := G) (K := L)
      M p hdisj x
  have hfracp' : ∀ x : L,
      (∃ a b : G, b ∉ p' ∧ x * algebraMap G L b = algebraMap G L a)
        ↔ 0 ≤ (C.baseChange F).ordAt x Q := fun x => (hfrac_p x).symm.trans (hQ x)
  -- ## (4) equality of the two primes is equality of the two points
  have h𝔪p' : 𝔪 = p'
      ↔ ∀ x : L, (0 ≤ (C.baseChange F).ordAt x Q₀ ↔ 0 ≤ (C.baseChange F).ordAt x Q) := by
    have hinjG : Function.Injective (algebraMap G L) := by
      rw [halgGL]
      exact (Scheme.germToFunctionField_injective (C.baseChange F).left
        (C.bcOpens F W)).comp hιbij.1
    constructor
    · intro h x
      rw [← hfrac𝔪 x, ← hfracp' x, h]
    · intro h
      refine Work.SpecLin.Alt.Up.prime_eq_of_forall_exists_mul_eq (algebraMap G L) hinjG 𝔪 p'
        (fun x => ?_)
      rw [hfrac𝔪 x, h x, ← hfracp' x]
  have hplace : (∀ x : L, (0 ≤ (C.baseChange F).ordAt x Q₀
        ↔ 0 ≤ (C.baseChange F).ordAt x Q)) ↔ Q₀ = Q := by
    constructor
    · intro h
      refine Work.CurveBasics.Place.place_eq_of_valuationSubring_eq (C.baseChange F) ?_
      ext x
      rw [Work.CurveBasics.Place.mem_valuationSubring_iff,
        Work.CurveBasics.Place.mem_valuationSubring_iff]
      exact h x
    · intro h x
      rw [h]
  have hplaceP : Q₀ = Q ↔ Work.SpecLin.ptPlace (Work.SpecLin.RPt.map
      (IsScalarTower.toAlgHom K R (FractionRing R)) s) = Q := Iff.rfl
  -- ## (5) assembly
  have key : (RingHom.ker evRH ≤ p') ↔ 𝔪 = p' := by
    have hmax𝔪 : 𝔪.IsMaximal := hker_eq ▸ hmax
    constructor
    · intro h
      rw [hker_eq] at h
      exact hmax𝔪.eq_of_le hp'ne h
    · intro h
      rw [hker_eq, h]
  exact hLHS.trans (key.trans (h𝔪p'.trans (hplace.trans hplaceP)))


end Up
end Work.SpecLin.Alt

