import Mathlib
import Submission.QuotientLattice
import Submission.Commons.LinearAlgebra.Independence.discrete_basis_values_linIndep
import Submission.Uncrossing
import Submission.StableLattices

open Module Real InnerProductSpace Submission.Uncrossing
open scoped Real
set_option autoImplicit false
set_option maxHeartbeats 600000

/-!
# Isometric identification of a lattice's real span with the standard space of its rank

The boundary case of `gamma_stable_of_two_le` (paper Prop 7.2) applies the induction
hypothesis to the rank-`d` stable sublattice `ℒ'` and its stable quotient — but those live
in proper subspaces of the ambient `E`.  The bridge is an *isometric* identification of
`realSpan ℒ` (the `ℝ`-span of a discrete `ℤ`-lattice of rank `d`) with the standard
`d`-dimensional space `EuclideanSpace ℝ (Fin d)`; through it the lattice, its Voronoi cell,
its determinant, its stability and its Gaussian masses are transported to the full-rank
situation that `gamma_stable` speaks about.

This module provides the arrow and the transported objects:

* `realSpan_finrank` — `finrank ℝ (realSpan ℒ) = finrank ℤ ℒ`;
* `realSpanIso ℒ` — a `LinearIsometryEquiv` `realSpan ℒ ≃ₗᵢ EuclideanSpace ℝ (Fin (finrank ℤ ℒ))`;
* `basisValuesW`, `transValues` — the ℤ-basis values of `ℒ` (in `realSpan ℒ`) and their
  image in the standard space;
* `span_basis_discrete` — the mathlib discreteness instance for the ℤ-span of an ambient
  `ℝ`-basis (used to make the transported lattice discrete).

(The remaining transport lemmas — discreteness/full-rank of `transLattice`, determinant and
stability preservation, Voronoi-cell and Gaussian-mass transport — are built on top of these
in follow-up sessions; see `Submission/Blueprint.lean`.)
-/

namespace Submission.Transport

variable {m : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin m)
local notation "W" => Submission.QuotientLattice.realSpan

/-- The `ℝ`-dimension of the real span of a discrete lattice equals its `ℤ`-rank. -/
lemma realSpan_finrank (ℒ : Submodule ℤ E) [DiscreteTopology ℒ] :
    Module.finrank ℝ (W ℒ) = Module.finrank ℤ ℒ := by
  classical
  let b : Module.Basis (Fin (Module.finrank ℤ ℒ)) ℤ ℒ := Module.finBasis ℤ ℒ
  let v : Fin (Module.finrank ℤ ℒ) → E := fun i => ((b i : ℒ) : E)
  have hspanZ : Submodule.span ℤ (Set.range v) = ℒ := by
    dsimp [v]
    calc
      Submodule.span ℤ (Set.range (fun i => ((b i : ℒ) : E))) =
          Submodule.span ℤ (ℒ.subtype '' Set.range b) := by
        congr 1
        ext x
        constructor
        · rintro ⟨i, rfl⟩
          exact ⟨b i, ⟨i, rfl⟩, rfl⟩
        · rintro ⟨y, ⟨i, rfl⟩, hx⟩
          refine ⟨i, ?_⟩
          simpa using hx
      _ = Submodule.map ℒ.subtype (Submodule.span ℤ (Set.range b)) := by rw [Submodule.map_span]
      _ = Submodule.map ℒ.subtype ⊤ := by rw [b.span_eq]
      _ = ℒ := by rw [Submodule.map_top, Submodule.range_subtype]
  have hdisc : DiscreteTopology (Submodule.span ℤ (Set.range v)) := by
    rw [hspanZ]
    infer_instance
  have hfr : Module.finrank ℝ (Submodule.span ℝ (Set.range v)) = Module.finrank ℤ ℒ := by
    have hset := Real.finrank_eq_int_finrank_of_discrete (s := Set.range v) hdisc
    rw [Set.finrank, Set.finrank] at hset
    rw [hspanZ] at hset
    exact hset
  have hspanℝ : Submodule.span ℝ ((ℒ : Submodule ℤ E) : Set E) = Submodule.span ℝ (Set.range v) := by
    calc
      Submodule.span ℝ ((ℒ : Submodule ℤ E) : Set E)
          = Submodule.span ℝ ((Submodule.span ℤ (Set.range v) : Submodule ℤ E) : Set E) := by
            congr 1
            exact congrArg (fun S : Submodule ℤ E => (S : Set E)) hspanZ.symm
      _ = Submodule.span ℝ (Set.range v) := by rw [Submodule.span_span_of_tower]
  dsimp [Submission.QuotientLattice.realSpan]
  change Module.finrank ℝ ↥(Submodule.span ℝ (ℒ : Set E)) = Module.finrank ℤ ℒ
  have hfinℝ : Module.finrank ℝ ↥(Submodule.span ℝ (ℒ : Set E)) =
      Module.finrank ℝ ↥(Submodule.span ℝ (Set.range v)) := by
    exact LinearEquiv.finrank_eq
      (LinearEquiv.ofEq (Submodule.span ℝ (ℒ : Set E)) (Submodule.span ℝ (Set.range v)) hspanℝ)
  rw [hfinℝ, hfr]

/-- The canonical isometry from the real span of `ℒ` onto the standard space of rank
`finrank ℤ ℒ` (built from `stdOrthonormalBasis`). -/
noncomputable def realSpanIso (ℒ : Submodule ℤ E) [DiscreteTopology ℒ] :
    W ℒ ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℤ ℒ)) := by
  classical
  let W' : Submodule ℝ E := W ℒ
  let E' : Type := EuclideanSpace ℝ (Fin (Module.finrank ℤ ℒ))
  have hfr : Module.finrank ℝ W' = Module.finrank ℤ ℒ := by
    dsimp [W']
    exact realSpan_finrank ℒ
  have hE : Module.finrank ℝ E' = Module.finrank ℤ ℒ := by
    dsimp [E']
    simp
  let b : OrthonormalBasis (Fin (Module.finrank ℝ W')) ℝ W' := stdOrthonormalBasis ℝ W'
  let b' : OrthonormalBasis (Fin (Module.finrank ℝ E')) ℝ E' := stdOrthonormalBasis ℝ E'
  have hIdx : Fin (Module.finrank ℝ W') ≃ Fin (Module.finrank ℝ E') :=
    finCongr (hfr.trans hE.symm)
  exact OrthonormalBasis.equiv b b' hIdx

/-- The `ℤ`-basis values of a discrete lattice, viewed inside its real span. -/
noncomputable def basisValuesW (ℒ : Submodule ℤ E) [DiscreteTopology ℒ] :
    Fin (Module.finrank ℤ ℒ) → W ℒ := fun i =>
  ⟨((Module.finBasis ℤ ℒ i : ℒ) : E),
    Submission.QuotientLattice.mem_realSpan (ℒ := ℒ) (x := ((Module.finBasis ℤ ℒ i : ℒ) : E))
      (Module.finBasis ℤ ℒ i).2⟩

/-- The `ℤ`-basis values of `ℒ`, transported by `realSpanIso` into the standard space of
rank `finrank ℤ ℒ`. -/
noncomputable def transValues (ℒ : Submodule ℤ E) [DiscreteTopology ℒ] :
    Fin (Module.finrank ℤ ℒ) → EuclideanSpace ℝ (Fin (Module.finrank ℤ ℒ)) :=
  fun i => realSpanIso ℒ (basisValuesW ℒ i)

/-- The transported lattice: the `ℤ`-span of `transValues` in the standard space. -/
noncomputable def transLattice (ℒ : Submodule ℤ E) [DiscreteTopology ℒ] :
    Submodule ℤ (EuclideanSpace ℝ (Fin (Module.finrank ℤ ℒ))) :=
  Submodule.span ℤ (Set.range (transValues ℒ))

/-- The `ℤ`-span of an ambient `ℝ`-basis is discrete (mathlib instance). -/
lemma span_basis_discrete {r : ℕ} (β : Module.Basis (Fin r) ℝ (EuclideanSpace ℝ (Fin r))) :
    DiscreteTopology (Submodule.span ℤ
      (Set.range (fun j : Fin r => (β j : EuclideanSpace ℝ (Fin r))))) := by
  infer_instance


/-- ℝ-independence of the ambient basis values of a discrete lattice. -/
lemma ambient_basis_values_linIndep (ℒ : Submodule ℤ E) [DiscreteTopology ℒ] :
    LinearIndependent ℝ (fun i : Fin (Module.finrank ℤ ℒ) => ((Module.finBasis ℤ ℒ i : ℒ) : E)) := by
  exact Commons.LinearAlgebra.Independence.discrete_basis_values_linIndep
    (ℒ := ℒ) (b := Module.finBasis ℤ ℒ)

/-- ℝ-independence of the basis values inside the real span. -/
lemma basisValuesW_linIndep_R (ℒ : Submodule ℤ E) [DiscreteTopology ℒ] :
    LinearIndependent ℝ (basisValuesW ℒ) := by
  have hliE := ambient_basis_values_linIndep ℒ
  have hcomp : (fun i : Fin (Module.finrank ℤ ℒ) =>
      ((Submission.QuotientLattice.realSpan ℒ).subtype) (basisValuesW ℒ i)) =
      (fun i : Fin (Module.finrank ℤ ℒ) => ((Module.finBasis ℤ ℒ i : ℒ) : E)) := by
    funext i
    simp [basisValuesW]
  have hfv : LinearIndependent ℝ (fun i : Fin (Module.finrank ℤ ℒ) =>
      ((Submission.QuotientLattice.realSpan ℒ).subtype) (basisValuesW ℒ i)) :=
    hcomp.symm ▸ hliE
  exact LinearIndependent.of_comp ((Submission.QuotientLattice.realSpan ℒ).subtype) hfv

/-- ℝ-independence of the transported values (in the standard space). -/
lemma transValues_linIndep_R (ℒ : Submodule ℤ E) [DiscreteTopology ℒ] :
    LinearIndependent ℝ (transValues ℒ) := by
  have hliW := basisValuesW_linIndep_R ℒ
  let f : Submission.QuotientLattice.realSpan ℒ →ₗ[ℝ]
      EuclideanSpace ℝ (Fin (Module.finrank ℤ ℒ)) := (realSpanIso ℒ).toLinearEquiv.toLinearMap
  have hker : f.ker = ⊥ := by
    dsimp [f]
    exact LinearMap.ker_eq_bot.mpr (realSpanIso ℒ).injective
  have hlv : LinearIndependent ℝ (fun i : Fin (Module.finrank ℤ ℒ) => f (basisValuesW ℒ i)) :=
    hliW.map' f hker
  have hfun : transValues ℒ = (fun i : Fin (Module.finrank ℤ ℒ) => f (basisValuesW ℒ i)) := by
    funext i
    simp [f, transValues]
  exact hfun.symm ▸ hlv

/-- ℤ-independence of the transported values. -/
lemma transValues_linIndep_Z (ℒ : Submodule ℤ E) [DiscreteTopology ℒ] :
    LinearIndependent ℤ (transValues ℒ) := by
  exact LinearIndependent.restrict_scalars' ℤ (transValues_linIndep_R ℒ)

/-- The ambient basis values span the real span (as a submodule of `E`). -/
lemma span_carrier_eq_realSpan (ℒ : Submodule ℤ E) [DiscreteTopology ℒ] :
    Submodule.span ℝ (Set.range (fun i : Fin (Module.finrank ℤ ℒ) =>
      ((Module.finBasis ℤ ℒ i : ℒ) : E))) = Submission.QuotientLattice.realSpan ℒ := by
  classical
  haveI : Module.Free ℤ ℒ := instModuleFree_of_discrete_submodule ℒ
  haveI : Module.Finite ℤ ℒ := instModuleFinite_of_discrete_submodule ℒ
  exact (Submission.QuotientLattice.realSpan_eq_span_basis (ℒ := ℒ)).symm

/-- The in-span basis values span the whole real span. -/
lemma basisValuesW_span_top (ℒ : Submodule ℤ E) [DiscreteTopology ℒ] :
    Submodule.span ℝ (Set.range (basisValuesW ℒ)) = ⊤ := by
  classical
  have hspanE := span_carrier_eq_realSpan ℒ
  apply le_antisymm
  · intro x hx
    trivial
  · intro x hx
    have hmemE : (x : E) ∈ (Submodule.span ℝ (Set.range
        (fun i : Fin (Module.finrank ℤ ℒ) => ((Module.finBasis ℤ ℒ i : ℒ) : E)))) := by
      rw [hspanE]
      exact x.2
    rcases (Submodule.mem_span_range_iff_exists_fun (R := ℝ)
        (v := fun i : Fin (Module.finrank ℤ ℒ) => ((Module.finBasis ℤ ℒ i : ℒ) : E))
        (x := (x : E))).mp hmemE with ⟨c, hc⟩
    have hx' : (∑ i : Fin (Module.finrank ℤ ℒ), c i • (basisValuesW ℒ i)) = x := by
      apply Subtype.ext
      calc
        (((∑ i, c i • (basisValuesW ℒ i)) : (Submission.QuotientLattice.realSpan ℒ)) : E)
            = ∑ i, c i • ((basisValuesW ℒ i : Submission.QuotientLattice.realSpan ℒ) : E) := by
              simp
        _ = (x : E) := by
          simpa [basisValuesW] using hc
    exact (Submodule.mem_span_range_iff_exists_fun (R := ℝ) (v := basisValuesW ℒ) (x := x)).2 ⟨c, hx'⟩

/-- The transported values span the standard space. -/
lemma transValues_span_top (ℒ : Submodule ℤ E) [DiscreteTopology ℒ] :
    Submodule.span ℝ (Set.range (transValues ℒ)) = ⊤ := by
  classical
  have hspanW : Submodule.span ℝ (Set.range (basisValuesW ℒ)) = ⊤ := basisValuesW_span_top ℒ
  let f : Submission.QuotientLattice.realSpan ℒ →ₗ[ℝ]
      EuclideanSpace ℝ (Fin (Module.finrank ℤ ℒ)) := (realSpanIso ℒ).toLinearEquiv.toLinearMap
  have hfun : transValues ℒ = fun i : Fin (Module.finrank ℤ ℒ) => f (basisValuesW ℒ i) := by
    funext i
    simp [f, transValues]
  calc
    Submodule.span ℝ (Set.range (transValues ℒ))
        = Submodule.span ℝ (f '' Set.range (basisValuesW ℒ)) := by
          rw [hfun]
          congr 1
          ext y
          constructor
          · rintro ⟨i, rfl⟩
            exact ⟨basisValuesW ℒ i, ⟨i, rfl⟩, rfl⟩
          · rintro ⟨x, ⟨i, hx⟩, rfl⟩
            refine ⟨i, ?_⟩
            simpa [hx]
    _ = (Submodule.span ℝ (Set.range (basisValuesW ℒ))).map f := by rw [Submodule.map_span]
    _ = ⊤ := by
      rw [hspanW, Submodule.map_top]
      rw [LinearMap.range_eq_top]
      intro y
      refine ⟨(realSpanIso ℒ).symm y, ?_⟩
      dsimp [f]
      simp

/-- **The transported lattice is discrete.** (It is the ℤ-span of the `transValues`, which
form an ambient `ℝ`-basis, so the mathlib discreteness instance applies.) -/
lemma transLattice_discrete (ℒ : Submodule ℤ E) [DiscreteTopology ℒ] :
    DiscreteTopology (transLattice ℒ) := by
  classical
  have hli := transValues_linIndep_R ℒ
  have hspan : Submodule.span ℝ (Set.range (transValues ℒ)) = ⊤ := transValues_span_top ℒ
  let βℝ : Module.Basis (Fin (Module.finrank ℤ ℒ)) ℝ
      (EuclideanSpace ℝ (Fin (Module.finrank ℤ ℒ))) :=
    Module.Basis.mk hli (le_of_eq hspan.symm)
  have hβval : ∀ j, (βℝ j : EuclideanSpace ℝ (Fin (Module.finrank ℤ ℒ))) = transValues ℒ j := by
    intro j
    simp [βℝ]
  have hI : DiscreteTopology (Submodule.span ℤ (Set.range
      (fun j : Fin (Module.finrank ℤ ℒ) => (βℝ j : EuclideanSpace ℝ (Fin (Module.finrank ℤ ℒ)))))) :=
    span_basis_discrete βℝ
  have hcar : ((transLattice ℒ : Submodule ℤ (EuclideanSpace ℝ (Fin (Module.finrank ℤ ℒ)))) :
        Set (EuclideanSpace ℝ (Fin (Module.finrank ℤ ℒ)))) =
      ((Submodule.span ℤ (Set.range (fun j : Fin (Module.finrank ℤ ℒ) =>
          (βℝ j : EuclideanSpace ℝ (Fin (Module.finrank ℤ ℒ))))) :
        Submodule ℤ (EuclideanSpace ℝ (Fin (Module.finrank ℤ ℒ)))) :
        Set (EuclideanSpace ℝ (Fin (Module.finrank ℤ ℒ)))) := by
    dsimp [transLattice]
    congr 1
    ext x
    simp [hβval]
  change DiscreteTopology (↥((transLattice ℒ : Submodule ℤ (EuclideanSpace ℝ (Fin (Module.finrank ℤ ℒ)))) :
      Set (EuclideanSpace ℝ (Fin (Module.finrank ℤ ℒ)))))
  rw [discreteTopology_subtype_iff']
  rw [hcar]
  change DiscreteTopology (↥((Submodule.span ℤ (Set.range (fun j : Fin (Module.finrank ℤ ℒ) =>
      (βℝ j : EuclideanSpace ℝ (Fin (Module.finrank ℤ ℒ))))) :
        Submodule ℤ (EuclideanSpace ℝ (Fin (Module.finrank ℤ ℒ)))) :
      Set (EuclideanSpace ℝ (Fin (Module.finrank ℤ ℒ))))) at hI
  rw [discreteTopology_subtype_iff'] at hI
  exact hI


/-- Inner product of two elements of a submodule equals the inner product of their carriers. -/
lemma inner_of_submodule {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    (S : Submodule ℝ X) (a b : S) : ⟪a, b⟫_ℝ = ⟪(a : X), (b : X)⟫_ℝ := by
  rfl

/-- Gram matrix of the transported values equals the Gram matrix of the original ambient
basis values (the isometry preserves inner products). -/
lemma gram_transValues_eq (ℒ : Submodule ℤ E) [DiscreteTopology ℒ] :
    Matrix.gram ℝ (fun i : Fin (Module.finrank ℤ ℒ) =>
        (transValues ℒ i : EuclideanSpace ℝ (Fin (Module.finrank ℤ ℒ)))) =
      Matrix.gram ℝ (fun i : Fin (Module.finrank ℤ ℒ) => ((Module.finBasis ℤ ℒ i : ℒ) : E)) := by
  classical
  ext i j
  dsimp [Matrix.gram]
  have h1 : ⟪transValues ℒ i, transValues ℒ j⟫_ℝ =
      ⟪basisValuesW ℒ i, basisValuesW ℒ j⟫_ℝ := by
    simpa [transValues] using
      ((realSpanIso ℒ).inner_map_map (basisValuesW ℒ i) (basisValuesW ℒ j))
  have h2 : ⟪basisValuesW ℒ i, basisValuesW ℒ j⟫_ℝ =
      ⟪((basisValuesW ℒ i : Submission.QuotientLattice.realSpan ℒ) : E),
        ((basisValuesW ℒ j : Submission.QuotientLattice.realSpan ℒ) : E)⟫_ℝ := by
    exact (inner_of_submodule (Submission.QuotientLattice.realSpan ℒ) (basisValuesW ℒ i) (basisValuesW ℒ j)).symm
  calc
    ⟪transValues ℒ i, transValues ℒ j⟫_ℝ = ⟪basisValuesW ℒ i, basisValuesW ℒ j⟫_ℝ := h1
    _ = ⟪((basisValuesW ℒ i : Submission.QuotientLattice.realSpan ℒ) : E),
          ((basisValuesW ℒ j : Submission.QuotientLattice.realSpan ℒ) : E)⟫_ℝ := h2
    _ = ⟪((Module.finBasis ℤ ℒ i : ℒ) : E), ((Module.finBasis ℤ ℒ j : ℒ) : E)⟫_ℝ := by
        simp [basisValuesW]

/-- A ℤ-basis of the transported lattice whose values are exactly the transported values. -/
lemma transBasis_exists (ℒ : Submodule ℤ E) [DiscreteTopology ℒ] :
    ∃ β : Module.Basis (Fin (Module.finrank ℤ ℒ)) ℤ (transLattice ℒ),
      ∀ j : Fin (Module.finrank ℤ ℒ),
        ((β j : transLattice ℒ) : EuclideanSpace ℝ (Fin (Module.finrank ℤ ℒ))) = transValues ℒ j := by
  classical
  have hspan : transLattice ℒ ≤ Submodule.span ℤ (Set.range (transValues ℒ)) := by
    dsimp [transLattice]
    exact le_rfl
  have hmem : ∀ j : Fin (Module.finrank ℤ ℒ),
      transValues ℒ j ∈ transLattice ℒ := by
    intro j
    exact Submodule.subset_span (by exact ⟨j, rfl⟩)
  exact basis_of_ambient (M := transLattice ℒ) (w := transValues ℒ) hspan hmem
    (transValues_linIndep_Z ℒ)

/-- **Determinant is preserved by the transport**: `det (transLattice ℒ) = det ℒ`.
(The discreteness of `transLattice ℒ` is `transLattice_discrete ℒ`; pass it as the second
instance argument.) -/
lemma det_transported (ℒ : Submodule ℤ E) [DiscreteTopology ℒ]
    [DiscreteTopology (transLattice ℒ)] :
    ReverseMinkowski.determinant (transLattice ℒ) = ReverseMinkowski.determinant ℒ := by
  classical
  haveI : Module.Free ℤ ℒ := instModuleFree_of_discrete_submodule ℒ
  haveI : Module.Finite ℤ ℒ := instModuleFinite_of_discrete_submodule ℒ
  haveI : Module.Free ℤ (transLattice ℒ) := instModuleFree_of_discrete_submodule (transLattice ℒ)
  haveI : Module.Finite ℤ (transLattice ℒ) := instModuleFinite_of_discrete_submodule (transLattice ℒ)
  rcases transBasis_exists ℒ with ⟨β, hβval⟩
  have hdetT : ReverseMinkowski.determinant (transLattice ℒ) =
      Real.sqrt ((Matrix.gram ℝ (fun j : Fin (Module.finrank ℤ ℒ) =>
        (transValues ℒ j : EuclideanSpace ℝ (Fin (Module.finrank ℤ ℒ))))).det) := by
    have h0 := det_eq_sqrt_gram_any_basis (L := transLattice ℒ) β
    rw [h0]
    congr 1
    congr 1
    ext a b
    simp [Matrix.gram, hβval]
  have hdetL : ReverseMinkowski.determinant ℒ =
      Real.sqrt ((Matrix.gram ℝ (fun i : Fin (Module.finrank ℤ ℒ) =>
        ((Module.finBasis ℤ ℒ i : ℒ) : E))).det) := by
    exact det_eq_sqrt_gram_any_basis (L := ℒ) (Module.finBasis ℤ ℒ)
  rw [hdetT, hdetL, gram_transValues_eq]


/-- The canonical ℤ-basis of the transported lattice (values equal to `transValues`). -/
noncomputable def transBasis (ℒ : Submodule ℤ E) [DiscreteTopology ℒ] :
    Module.Basis (Fin (Module.finrank ℤ ℒ)) ℤ (transLattice ℒ) :=
  Classical.choose (transBasis_exists ℒ)

lemma transBasis_val (ℒ : Submodule ℤ E) [DiscreteTopology ℒ]
    (j : Fin (Module.finrank ℤ ℒ)) :
    ((transBasis ℒ j : transLattice ℒ) : EuclideanSpace ℝ (Fin (Module.finrank ℤ ℒ))) =
      transValues ℒ j :=
  (Classical.choose_spec (transBasis_exists ℒ)) j

/-- The transported lattice is full-rank in the standard space (so `gamma_stable` can be
invoked at the rank `finrank ℤ ℒ` on `transLattice ℒ`). -/
lemma finrank_transLattice (ℒ : Submodule ℤ E) [DiscreteTopology ℒ] :
    Module.finrank ℤ (transLattice ℒ) = Module.finrank ℤ ℒ := by
  classical
  simpa using (Module.finrank_eq_card_basis (transBasis ℒ))

/-- The ℤ-module equivalence between the lattice and its transport, along `realSpanIso`
(it maps the canonical ℤ-basis values to the transported values).  Through this equivalence
every submodule of `transLattice ℒ` corresponds to a submodule of `ℒ`, with equal
determinants (Gram invariance under the isometry) — the correspondence underlying
`Stable ℒ ↔ Stable (transLattice ℒ)`. -/
noncomputable def latticeEquiv (ℒ : Submodule ℤ E) [DiscreteTopology ℒ] :
    ℒ ≃ₗ[ℤ] transLattice ℒ :=
  (Module.finBasis ℤ ℒ).equiv (transBasis ℒ) (Equiv.refl (Fin (Module.finrank ℤ ℒ)))

lemma latticeEquiv_basis (ℒ : Submodule ℤ E) [DiscreteTopology ℒ]
    (i : Fin (Module.finrank ℤ ℒ)) :
    latticeEquiv ℒ (Module.finBasis ℤ ℒ i) = transBasis ℒ i := by
  exact (Module.Basis.equiv_apply (Module.finBasis ℤ ℒ) i (transBasis ℒ)
    (Equiv.refl (Fin (Module.finrank ℤ ℒ))))


/-- Carrier-level description of `latticeEquiv`: transporting an element and reading its
carrier in the standard space is the same as applying `realSpanIso` to its carrier (viewed
inside the real span). -/
lemma latticeEquiv_coe (ℒ : Submodule ℤ E) [DiscreteTopology ℒ] (x : ℒ) :
    ((latticeEquiv ℒ x : transLattice ℒ) : EuclideanSpace ℝ (Fin (Module.finrank ℤ ℒ))) =
      realSpanIso ℒ ⟨(x : E),
        Submission.QuotientLattice.mem_realSpan (ℒ := ℒ) (x := (x : E)) x.2⟩ := by
  classical
  let b : Module.Basis (Fin (Module.finrank ℤ ℒ)) ℤ ℒ := Module.finBasis ℤ ℒ
  let c : Fin (Module.finrank ℤ ℒ) → ℤ := b.repr x
  have hx : x = ∑ i, c i • (b i) := by
    simpa [c] using (b.sum_repr x).symm
  have hcar : (x : E) = ∑ i, c i • ((b i : ℒ) : E) := by
    have hc := congrArg (fun z : ℒ => (z : E)) hx
    change (ℒ.subtype) x = (ℒ.subtype) (∑ i, c i • (b i)) at hc
    rw [map_sum] at hc
    simp at hc
    simpa using hc
  have hlin : ((latticeEquiv ℒ x : transLattice ℒ) : EuclideanSpace ℝ (Fin (Module.finrank ℤ ℒ))) =
      ∑ i, c i • ((latticeEquiv ℒ (b i) : transLattice ℒ) : EuclideanSpace ℝ (Fin (Module.finrank ℤ ℒ))) := by
    rw [hx]
    have h1 : latticeEquiv ℒ (∑ i, c i • (b i)) = ∑ i, c i • (latticeEquiv ℒ (b i)) := by
      change ((latticeEquiv ℒ).toLinearMap) (∑ i, c i • (b i)) =
          ∑ i, c i • ((latticeEquiv ℒ).toLinearMap) (b i)
      rw [map_sum]
      simp
    have hc1 := congrArg (fun z : transLattice ℒ =>
      ((z : transLattice ℒ) : EuclideanSpace ℝ (Fin (Module.finrank ℤ ℒ)))) h1
    have hc2 : (((∑ i, c i • (latticeEquiv ℒ (b i))) : transLattice ℒ) :
          EuclideanSpace ℝ (Fin (Module.finrank ℤ ℒ))) =
        ∑ i, c i • ((latticeEquiv ℒ (b i) : transLattice ℒ) : EuclideanSpace ℝ (Fin (Module.finrank ℤ ℒ))) := by
      change (transLattice ℒ).subtype (∑ i, c i • (latticeEquiv ℒ (b i))) =
          ∑ i, c i • ((transLattice ℒ).subtype) (latticeEquiv ℒ (b i))
      rw [map_sum]
      simp
    exact hc1.trans hc2
  have hw : (⟨(x : E),
        Submission.QuotientLattice.mem_realSpan (ℒ := ℒ) (x := (x : E)) x.2⟩ :
        Submission.QuotientLattice.realSpan ℒ) =
      ∑ i, c i • (basisValuesW ℒ i) := by
    apply Subtype.ext
    calc
      ((⟨(x : E),
          Submission.QuotientLattice.mem_realSpan (ℒ := ℒ) (x := (x : E)) x.2⟩ :
          Submission.QuotientLattice.realSpan ℒ) : E)
          = (x : E) := rfl
      _ = ∑ i, c i • ((b i : ℒ) : E) := hcar
      _ = ∑ i, c i • ((basisValuesW ℒ i : Submission.QuotientLattice.realSpan ℒ) : E) := by
          simp [basisValuesW, b]
      _ = ((∑ i, c i • (basisValuesW ℒ i) : Submission.QuotientLattice.realSpan ℒ) : E) := by
          change ∑ i, c i • (((basisValuesW ℒ i : Submission.QuotientLattice.realSpan ℒ) : E)) =
              ((Submission.QuotientLattice.realSpan ℒ).subtype)
                (∑ i, c i • (basisValuesW ℒ i))
          rw [map_sum]
          simp [basisValuesW, b]
  have hrhs : realSpanIso ℒ ⟨(x : E),
        Submission.QuotientLattice.mem_realSpan (ℒ := ℒ) (x := (x : E)) x.2⟩ =
      ∑ i, c i • transValues ℒ i := by
    calc
      realSpanIso ℒ ⟨(x : E),
          Submission.QuotientLattice.mem_realSpan (ℒ := ℒ) (x := (x : E)) x.2⟩
          = realSpanIso ℒ (∑ i, c i • (basisValuesW ℒ i)) := by rw [hw]
      _ = ∑ i, c i • (realSpanIso ℒ (basisValuesW ℒ i)) := by
          change ((realSpanIso ℒ).toLinearEquiv.toLinearMap)
              (∑ i, c i • (basisValuesW ℒ i)) =
            ∑ i, c i • ((realSpanIso ℒ).toLinearEquiv.toLinearMap) (basisValuesW ℒ i)
          rw [map_sum]
          simp
      _ = ∑ i, c i • transValues ℒ i := by
          simp [transValues]
  calc
    ((latticeEquiv ℒ x : transLattice ℒ) : EuclideanSpace ℝ (Fin (Module.finrank ℤ ℒ)))
        = ∑ i, c i • ((latticeEquiv ℒ (b i) : transLattice ℒ) : EuclideanSpace ℝ (Fin (Module.finrank ℤ ℒ))) := hlin
    _ = ∑ i, c i • transValues ℒ i := by
        simp [latticeEquiv_basis, transBasis_val, b]
    _ = realSpanIso ℒ ⟨(x : E),
        Submission.QuotientLattice.mem_realSpan (ℒ := ℒ) (x := (x : E)) x.2⟩ := hrhs.symm



/-- Embedding of the standard space back into the ambient `E`: the inverse isometry followed
by the inclusion of the real span.  Through it every `N ≤ transLattice ℒ` corresponds to a
sublattice `toSpanMap '' N ≤ ℒ` with the same Gram matrices (hence the same determinant). -/
noncomputable def toSpanMap (ℒ : Submodule ℤ E) [DiscreteTopology ℒ] :
    EuclideanSpace ℝ (Fin (Module.finrank ℤ ℒ)) →ₗ[ℝ] E :=
  (Submission.QuotientLattice.realSpan ℒ).subtype.comp
    ((realSpanIso ℒ).symm).toLinearEquiv.toLinearMap

/-- `toSpanMap` preserves inner products (an isometric embedding). -/
lemma toSpanMap_inner (ℒ : Submodule ℤ E) [DiscreteTopology ℒ]
    (a b : EuclideanSpace ℝ (Fin (Module.finrank ℤ ℒ))) :
    ⟪toSpanMap ℒ a, toSpanMap ℒ b⟫_ℝ =
      ⟪a, b⟫_ℝ := by
  calc
    ⟪toSpanMap ℒ a, toSpanMap ℒ b⟫_ℝ
        = ⟪((realSpanIso ℒ).symm a : Submission.QuotientLattice.realSpan ℒ),
            ((realSpanIso ℒ).symm b : Submission.QuotientLattice.realSpan ℒ)⟫_ℝ := by
            exact (inner_of_submodule (Submission.QuotientLattice.realSpan ℒ)
                ((realSpanIso ℒ).symm a) ((realSpanIso ℒ).symm b)).symm
    _ = ⟪a, b⟫_ℝ := by
        simpa using (((realSpanIso ℒ).symm).inner_map_map a b)

/-- `toSpanMap` sends the transported values back to the original in-span basis values. -/
lemma toSpanMap_transValues (ℒ : Submodule ℤ E) [DiscreteTopology ℒ]
    (i : Fin (Module.finrank ℤ ℒ)) :
    toSpanMap ℒ (transValues ℒ i) =
      ((basisValuesW ℒ i : Submission.QuotientLattice.realSpan ℒ) : E) := by
  simp [toSpanMap, transValues]

/-- `toSpanMap` is injective. -/
lemma toSpanMap_injective (ℒ : Submodule ℤ E) [DiscreteTopology ℒ] :
    Function.Injective (toSpanMap ℒ) := by
  change Function.Injective ((Submission.QuotientLattice.realSpan ℒ).subtype ∘
    (realSpanIso ℒ).symm)
  exact Function.Injective.comp
    (by intro x y h; exact Subtype.ext h)
    ((realSpanIso ℒ).symm).injective



/-- A `ℤ`-submodule with a uniform positive gap below all nonzero vector norms is discrete. -/
lemma discrete_of_norm_gap {X : Type*} [NormedAddCommGroup X] (G : Submodule ℤ X)
    (h : ∃ ε > 0, ∀ g : G, g ≠ 0 → ε ≤ ‖(g : X)‖) : DiscreteTopology G := by
  change DiscreteTopology (↥(G : Set X))
  rw [discreteTopology_subtype_iff']
  rcases h with ⟨ε, hε, hg⟩
  intro y hy
  refine ⟨Metric.ball y ε, Metric.isOpen_ball, ?_⟩
  ext x
  constructor
  · intro hxmem
    rcases hxmem with ⟨hxball, hxG⟩
    by_contra hxne
    have hzG : x - y ∈ G := Submodule.sub_mem G hxG hy
    have hz : (⟨x - y, hzG⟩ : G) ≠ 0 := by
      intro hz0
      apply hxne
      exact sub_eq_zero.mp (congrArg (fun z : G => (z : X)) hz0)
    have hgap := hg ⟨x - y, hzG⟩ hz
    have hnorm : ‖x - y‖ < ε := by
      simpa [dist_eq_norm] using (Metric.mem_ball.mp hxball)
    linarith
  · intro hx
    rw [hx]
    exact ⟨Metric.mem_ball_self hε, hy⟩

/-- A discrete `ℤ`-submodule has a uniform positive gap below all nonzero vector norms
(`0` is isolated). -/
lemma norm_gap_of_discrete {X : Type*} [NormedAddCommGroup X] (G : Submodule ℤ X)
    [DiscreteTopology G] : ∃ ε > 0, ∀ g : G, g ≠ 0 → ε ≤ ‖(g : X)‖ := by
  classical
  have hI : DiscreteTopology (↥(G : Set X)) := by
    change DiscreteTopology G
    infer_instance
  rcases (discreteTopology_subtype_iff'.1 hI) (0 : X) (by simp : (0 : X) ∈ (G : Set X))
    with ⟨U, hUo, hU⟩
  have h0U : (0 : X) ∈ U := by
    have : (0 : X) ∈ U ∩ (G : Set X) := by
      rw [hU]
      simp
    exact this.1
  rcases (Metric.isOpen_iff.mp hUo) (0 : X) h0U with ⟨ε, hε, hball⟩
  refine ⟨ε, hε, ?_⟩
  intro g hg0
  by_contra hlt
  have hmem : (g : X) ∈ Metric.ball (0 : X) ε := by
    rw [Metric.mem_ball, dist_zero_right]
    exact lt_of_not_ge hlt
  have hgU : (g : X) ∈ U := hball hmem
  have : (g : X) ∈ U ∩ (G : Set X) := ⟨hgU, g.2⟩
  have hzero : (g : X) = 0 := by
    rwa [hU] at this
  apply hg0
  exact Subtype.ext hzero



/-- `toSpanMap` sends elements of the transported lattice back into the original lattice. -/
lemma toSpanMap_mem_lattice (ℒ : Submodule ℤ E) [DiscreteTopology ℒ]
    {y : EuclideanSpace ℝ (Fin (Module.finrank ℤ ℒ))} (hy : y ∈ transLattice ℒ) :
    toSpanMap ℒ y ∈ ℒ := by
  classical
  rcases (Submodule.mem_span_range_iff_exists_fun (R := ℤ)
      (v := transValues ℒ) (x := y)).mp hy with ⟨c, hc⟩
  have hF : toSpanMap ℒ y =
      ∑ i : Fin (Module.finrank ℤ ℒ), c i • (toSpanMap ℒ (transValues ℒ i)) := by
    rw [← hc]
    rw [map_sum]
    refine Finset.sum_congr rfl ?_
    intro i hi
    exact map_zsmul (toSpanMap ℒ) (c i) (transValues ℒ i)
  have hterm : ∀ i : Fin (Module.finrank ℤ ℒ),
      c i • (toSpanMap ℒ (transValues ℒ i)) ∈ ℒ := by
    intro i
    have hval : toSpanMap ℒ (transValues ℒ i) =
        ((basisValuesW ℒ i : Submission.QuotientLattice.realSpan ℒ) : E) :=
      toSpanMap_transValues ℒ i
    have hm : ((basisValuesW ℒ i : Submission.QuotientLattice.realSpan ℒ) : E) ∈ ℒ := by
      simp [basisValuesW]
    rw [hval]
    exact Submodule.smul_mem ℒ (c i) hm
  have hsum : (∑ i : Fin (Module.finrank ℤ ℒ), c i • (toSpanMap ℒ (transValues ℒ i))) ∈ ℒ := by
    exact Submodule.sum_mem ℒ (by intro i hi; exact hterm i)
  rwa [hF]

/-- Pullback of an ambient sublattice `N ≤ transLattice ℒ` to a sublattice of the original
`ℒ`, through `toSpanMap` (on the ℤ-basis values of `N`). -/
noncomputable def pullback (ℒ : Submodule ℤ E) [DiscreteTopology ℒ]
    (N : Submodule ℤ (EuclideanSpace ℝ (Fin (Module.finrank ℤ ℒ)))) [DiscreteTopology N] :
    Submodule ℤ E :=
  Submodule.span ℤ (Set.range (fun j : Fin (Module.finrank ℤ N) =>
    toSpanMap ℒ (((Module.finBasis ℤ N j : N) : EuclideanSpace ℝ (Fin (Module.finrank ℤ ℒ))))))

/-- The pullback of a sublattice of the transport is a sublattice of the original lattice
(`M ≤ ℒ` for `M := pullback ℒ N`). -/
lemma pullback_le_lattice (ℒ : Submodule ℤ E) [DiscreteTopology ℒ]
    (N : Submodule ℤ (EuclideanSpace ℝ (Fin (Module.finrank ℤ ℒ)))) [DiscreteTopology N]
    (hN : N ≤ transLattice ℒ) : pullback ℒ N ≤ ℒ := by
  classical
  refine Submodule.span_le.mpr ?_
  intro y hy
  rcases hy with ⟨j, hjy⟩
  subst y
  exact toSpanMap_mem_lattice ℒ (hN (Module.finBasis ℤ N j).2)



/-- The ambient values of the canonical ℤ-basis of a discrete lattice span the lattice
(as an ambient submodule of the space). -/
lemma finBasis_span_ambient {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [FiniteDimensional ℝ X] (N : Submodule ℤ X) [DiscreteTopology N] :
    Submodule.span ℤ (Set.range (fun j : Fin (Module.finrank ℤ N) =>
      ((Module.finBasis ℤ N j : N) : X))) = N := by
  classical
  apply le_antisymm
  · refine Submodule.span_le.mpr ?_
    intro y hy
    rcases hy with ⟨j, hjy⟩
    rw [← hjy]
    exact (Module.finBasis ℤ N j).2
  · intro x hx
    let xN : N := ⟨x, hx⟩
    let β : Module.Basis (Fin (Module.finrank ℤ N)) ℤ (↥N) := Module.finBasis ℤ N
    have hxN : xN = ∑ i, (β.repr xN) i • (β i) := (β.sum_repr xN).symm
    have hc : x = ∑ i, (β.repr xN) i • (((Module.finBasis ℤ N i : N) : X)) := by
      have h0 := congrArg (fun z : ↥N => (z : X)) hxN
      change (N.subtype) xN = (N.subtype) (∑ i, (β.repr xN) i • (β i)) at h0
      rw [map_sum] at h0
      simp at h0
      simpa [xN, β] using h0
    exact (Submodule.mem_span_range_iff_exists_fun (R := ℤ)
      (v := fun i : Fin (Module.finrank ℤ N) => (((Module.finBasis ℤ N i : N) : X)))
      (x := x)).2 ⟨β.repr xN, hc.symm⟩



/-- `pullback` equals the image of `N` under the `ℤ`-restricted `toSpanMap`. -/
lemma pullback_eq_map (ℒ : Submodule ℤ E) [DiscreteTopology ℒ]
    (N : Submodule ℤ (EuclideanSpace ℝ (Fin (Module.finrank ℤ ℒ)))) [DiscreteTopology N] :
    pullback ℒ N = Submodule.map ((toSpanMap ℒ).restrictScalars ℤ) N := by
  classical
  let wN : Fin (Module.finrank ℤ N) → EuclideanSpace ℝ (Fin (Module.finrank ℤ ℒ)) :=
    fun j => (((Module.finBasis ℤ N j : N) : EuclideanSpace ℝ (Fin (Module.finrank ℤ ℒ))))
  calc
    pullback ℒ N = Submodule.span ℤ (Set.range (fun j : Fin (Module.finrank ℤ N) =>
        toSpanMap ℒ (wN j))) := rfl
    _ = Submodule.span ℤ (((toSpanMap ℒ).restrictScalars ℤ) '' Set.range wN) := by
          congr 1
          ext y
          simp
    _ = Submodule.map ((toSpanMap ℒ).restrictScalars ℤ)
          (Submodule.span ℤ (Set.range wN)) := by
          rw [← Submodule.map_span]
    _ = Submodule.map ((toSpanMap ℒ).restrictScalars ℤ) N := by
          rw [finBasis_span_ambient (X := EuclideanSpace ℝ (Fin (Module.finrank ℤ ℒ))) N]

/-- Membership in the pullback = membership in the image of `N` under the `ℤ`-restricted
`toSpanMap`. -/
lemma mem_pullback_iff (ℒ : Submodule ℤ E) [DiscreteTopology ℒ]
    (N : Submodule ℤ (EuclideanSpace ℝ (Fin (Module.finrank ℤ ℒ)))) [DiscreteTopology N]
    (x : E) :
    x ∈ pullback ℒ N ↔
      ∃ y : EuclideanSpace ℝ (Fin (Module.finrank ℤ ℒ)),
        y ∈ (N : Set (EuclideanSpace ℝ (Fin (Module.finrank ℤ ℒ)))) ∧
          (toSpanMap ℒ).restrictScalars ℤ y = x := by
  calc
    x ∈ pullback ℒ N
        ↔ x ∈ Submodule.map ((toSpanMap ℒ).restrictScalars ℤ) N :=
          Iff.of_eq (congrArg (fun S : Submodule ℤ E => x ∈ S) (pullback_eq_map ℒ N))
    _ ↔ ∃ y : EuclideanSpace ℝ (Fin (Module.finrank ℤ ℒ)),
        y ∈ (N : Set (EuclideanSpace ℝ (Fin (Module.finrank ℤ ℒ)))) ∧
          (toSpanMap ℒ).restrictScalars ℤ y = x :=
          Submodule.mem_map

/-- The pullback of a discrete sublattice of the transport is discrete (norm gap transfers
through the isometric embedding `toSpanMap`). -/
lemma pullback_discrete (ℒ : Submodule ℤ E) [DiscreteTopology ℒ]
    (N : Submodule ℤ (EuclideanSpace ℝ (Fin (Module.finrank ℤ ℒ)))) [DiscreteTopology N]
    (_hN : N ≤ transLattice ℒ) : DiscreteTopology (pullback ℒ N) := by
  classical
  rcases norm_gap_of_discrete N with ⟨ε, hε, hg⟩
  apply discrete_of_norm_gap
  refine ⟨ε, hε, ?_⟩
  intro m hm0
  have hm : (m : E) ∈ pullback ℒ N := m.2
  rcases (mem_pullback_iff ℒ N (m : E)).1 hm with ⟨y, hyN, hfy⟩
  have hne0 : y ≠ 0 := by
    intro hy0
    apply hm0
    apply Subtype.ext
    calc
      (m : E) = (toSpanMap ℒ).restrictScalars ℤ y := hfy.symm
      _ = (toSpanMap ℒ).restrictScalars ℤ 0 := by rw [hy0]
      _ = 0 := by simp
  have hsub0 : (⟨y, hyN⟩ : N) ≠ 0 := by
    intro hz0
    apply hne0
    exact congrArg (fun z : N => (z : EuclideanSpace ℝ (Fin (Module.finrank ℤ ℒ)))) hz0
  have hgapN : ε ≤ ‖y‖ := by
    simpa using (hg ⟨y, hyN⟩ hsub0)
  have hcar : toSpanMap ℒ y = (m : E) := by simpa using hfy
  have hnorm : ‖(m : E)‖ = ‖y‖ := by
    calc
      ‖(m : E)‖ = ‖toSpanMap ℒ y‖ := by rw [hcar]
      _ = ‖(realSpanIso ℒ).symm y‖ := by rfl
      _ = ‖y‖ := (realSpanIso ℒ).symm.norm_map y
  calc
    ε ≤ ‖y‖ := hgapN
    _ = ‖(m : E)‖ := hnorm.symm



/-- **Determinant is preserved by the pullback**: `det (pullback ℒ N) = det N` for every
sublattice `N ≤ transLattice ℒ`.  (Gram matrices of the two ℤ-bases agree by
`toSpanMap_inner`; both determinants are expressed through `det_eq_sqrt_gram_any_basis`.) -/
lemma det_pullback (ℒ : Submodule ℤ E) [DiscreteTopology ℒ]
    (N : Submodule ℤ (EuclideanSpace ℝ (Fin (Module.finrank ℤ ℒ)))) [DiscreteTopology N]
    (hN : N ≤ transLattice ℒ) [DiscreteTopology (pullback ℒ N)] :
    ReverseMinkowski.determinant (pullback ℒ N) = ReverseMinkowski.determinant N := by
  classical
  haveI : Module.Free ℤ ℒ := instModuleFree_of_discrete_submodule ℒ
  haveI : Module.Finite ℤ ℒ := instModuleFinite_of_discrete_submodule ℒ
  haveI : Module.Free ℤ N := instModuleFree_of_discrete_submodule N
  haveI : Module.Finite ℤ N := instModuleFinite_of_discrete_submodule N
  haveI : Module.Free ℤ (pullback ℒ N) := instModuleFree_of_discrete_submodule (pullback ℒ N)
  haveI : Module.Finite ℤ (pullback ℒ N) := instModuleFinite_of_discrete_submodule (pullback ℒ N)
  let wN : Fin (Module.finrank ℤ N) → EuclideanSpace ℝ (Fin (Module.finrank ℤ ℒ)) :=
    fun j => (((Module.finBasis ℤ N j : N) : EuclideanSpace ℝ (Fin (Module.finrank ℤ ℒ))))
  let v : Fin (Module.finrank ℤ N) → E := fun j => toSpanMap ℒ (wN j)
  have hli_wN : LinearIndependent ℤ wN := by
    let βN : Module.Basis (Fin (Module.finrank ℤ N)) ℤ (↥N) := Module.finBasis ℤ N
    have hb0 : LinearIndependent ℤ (fun j : Fin (Module.finrank ℤ N) =>
        ((βN j : ↥N) : EuclideanSpace ℝ (Fin (Module.finrank ℤ ℒ)))) := by
      exact βN.linearIndependent.map' (N.subtype) (by
        rw [LinearMap.ker_eq_bot]
        intro x y h
        exact Subtype.ext h)
    simpa [wN, βN] using hb0
  have hli_v : LinearIndependent ℤ v := by
    have hf : Function.Injective ((toSpanMap ℒ).restrictScalars ℤ) := by
      change Function.Injective (toSpanMap ℒ)
      exact toSpanMap_injective ℒ
    have hli0 : LinearIndependent ℤ (fun j : Fin (Module.finrank ℤ N) =>
        ((toSpanMap ℒ).restrictScalars ℤ) (wN j)) :=
      hli_wN.map' ((toSpanMap ℒ).restrictScalars ℤ) (by rw [LinearMap.ker_eq_bot]; exact hf)
    simpa [v] using hli0
  have hspan : pullback ℒ N ≤ Submodule.span ℤ (Set.range v) := by
    dsimp [pullback, v]
    exact le_rfl
  have hmem : ∀ j : Fin (Module.finrank ℤ N), v j ∈ pullback ℒ N := by
    intro j
    exact Submodule.subset_span (by exact ⟨j, rfl⟩)
  rcases (basis_of_ambient (M := pullback ℒ N) (w := v) hspan hmem hli_v) with ⟨βM, hβMval⟩
  have hgram_eq : Matrix.gram ℝ v = Matrix.gram ℝ wN := by
    ext a b
    simp only [Matrix.gram]
    exact toSpanMap_inner ℒ (wN a) (wN b)
  have hgramM : Matrix.gram ℝ (fun j : Fin (Module.finrank ℤ N) =>
        ((βM j : pullback ℒ N) : E)) = Matrix.gram ℝ v := by
    ext a b
    simp [Matrix.gram, hβMval]
  have hgramN : Matrix.gram ℝ (fun j : Fin (Module.finrank ℤ N) =>
        (((Module.finBasis ℤ N j : N) : EuclideanSpace ℝ (Fin (Module.finrank ℤ ℒ))))) =
      Matrix.gram ℝ wN := by
    simp [wN]
  have hdetM : ReverseMinkowski.determinant (pullback ℒ N) =
      Real.sqrt ((Matrix.gram ℝ v).det) := by
    have h0 := det_eq_sqrt_gram_any_basis (L := pullback ℒ N) βM
    rw [h0, hgramM]
  have hdetN : ReverseMinkowski.determinant N =
      Real.sqrt ((Matrix.gram ℝ wN).det) := by
    have h0 := det_eq_sqrt_gram_any_basis (L := N) (Module.finBasis ℤ N)
    rw [h0, hgramN]
  rw [hdetM, hdetN, hgram_eq]



/-- **Stability transports to the transported lattice**: `Stable ℒ → Stable (transLattice ℒ)`.
Every sublattice `N ≤ transLattice ℒ` pulls back to `pullback ℒ N ≤ ℒ` with the same
determinant (`pullback_le_lattice` + `det_pullback`), so `Stable ℒ`'s subdeterminant clause
applies; the determinant of the transport is `1` by `det_transported`.  (This is the direction
the boundary case of `gamma_stable_of_two_le` needs: the transported rank-`d` stable sublattice
satisfies `Stable` so the induction hypothesis applies at rank `d`.) -/
lemma stable_of_stable_transported (ℒ : Submodule ℤ E) [DiscreteTopology ℒ]
    [DiscreteTopology (transLattice ℒ)]
    (hSt : Submission.StableLattices.Stable ℒ) :
    Submission.StableLattices.Stable (transLattice ℒ) := by
  constructor
  · rw [det_transported ℒ]
    exact Submission.StableLattices.det_eq_one_of_stable hSt
  · intro N hNle _hDTN
    haveI dtP : DiscreteTopology (pullback ℒ N) := pullback_discrete ℒ N hNle
    have hdet : ReverseMinkowski.determinant N =
        ReverseMinkowski.determinant (pullback ℒ N) :=
      (det_pullback ℒ N hNle).symm
    rw [hdet]
    exact hSt.2 (pullback ℒ N) (pullback_le_lattice ℒ N hNle)



/-- Pushforward of an ambient sublattice `M ≤ ℒ` to a sublattice of `transLattice ℒ`
(through `realSpanIso`, applied to the carriers of the canonical ℤ-basis of `M`). -/
noncomputable def pushforward (ℒ : Submodule ℤ E) [DiscreteTopology ℒ]
    (M : Submodule ℤ E) [DiscreteTopology M] (hMle : M ≤ ℒ) :
    Submodule ℤ (EuclideanSpace ℝ (Fin (Module.finrank ℤ ℒ))) :=
  Submodule.span ℤ (Set.range (fun i : Fin (Module.finrank ℤ M) =>
    realSpanIso ℒ ⟨(((Module.finBasis ℤ M i : M) : E)),
      Submission.QuotientLattice.mem_realSpan (ℒ := ℒ)
        (x := (((Module.finBasis ℤ M i : M) : E))) (hMle (Module.finBasis ℤ M i).2)⟩))

/-- The pushforward of a sublattice of `ℒ` is a sublattice of the transport. -/
lemma pushforward_le_transLattice (ℒ : Submodule ℤ E) [DiscreteTopology ℒ]
    (M : Submodule ℤ E) [DiscreteTopology M] (hMle : M ≤ ℒ) :
    pushforward ℒ M hMle ≤ transLattice ℒ := by
  classical
  refine Submodule.span_le.mpr ?_
  intro y hy
  rcases hy with ⟨i, hiy⟩
  subst y
  let x' : ℒ := ⟨((Module.finBasis ℤ M i : M) : E), hMle (Module.finBasis ℤ M i).2⟩
  have hcoe := latticeEquiv_coe ℒ x'
  change realSpanIso ℒ ⟨(((Module.finBasis ℤ M i : M) : E)),
      Submission.QuotientLattice.mem_realSpan (ℒ := ℒ)
        (x := (((Module.finBasis ℤ M i : M) : E))) (hMle (Module.finBasis ℤ M i).2)⟩
      ∈ (transLattice ℒ : Set (EuclideanSpace ℝ (Fin (Module.finrank ℤ ℒ))))
  rw [show (⟨(((Module.finBasis ℤ M i : M) : E)),
        Submission.QuotientLattice.mem_realSpan (ℒ := ℒ)
          (x := (((Module.finBasis ℤ M i : M) : E))) (hMle (Module.finBasis ℤ M i).2)⟩ :
        Submission.QuotientLattice.realSpan ℒ) =
        ⟨(x' : E), Submission.QuotientLattice.mem_realSpan (ℒ := ℒ) (x := (x' : E)) x'.2⟩ by
      apply Subtype.ext
      rfl]
  rw [← hcoe]
  exact (latticeEquiv ℒ x').2



/-- Membership in the pushforward: it consists exactly of the isometry-images of the
elements of `M`. -/
lemma mem_pushforward_iff (ℒ : Submodule ℤ E) [DiscreteTopology ℒ]
    (M : Submodule ℤ E) [DiscreteTopology M] (hMle : M ≤ ℒ)
    (x : EuclideanSpace ℝ (Fin (Module.finrank ℤ ℒ))) :
    x ∈ pushforward ℒ M hMle ↔
      ∃ m : M, realSpanIso ℒ ⟨((m : M) : E),
        Submission.QuotientLattice.mem_realSpan (ℒ := ℒ) (x := (((m : M) : E))) (hMle m.2)⟩ = x := by
  classical
  let b : Module.Basis (Fin (Module.finrank ℤ M)) ℤ (↥M) := Module.finBasis ℤ M
  let gen : Fin (Module.finrank ℤ M) →
      Submission.QuotientLattice.realSpan ℒ := fun i =>
    ⟨((Module.finBasis ℤ M i : M) : E),
      Submission.QuotientLattice.mem_realSpan (ℒ := ℒ)
        (x := (((Module.finBasis ℤ M i : M) : E))) (hMle (Module.finBasis ℤ M i).2)⟩
  have hpf : pushforward ℒ M hMle = Submodule.span ℤ
      (Set.range (fun i : Fin (Module.finrank ℤ M) => realSpanIso ℒ (gen i))) := by
    dsimp [pushforward, gen]
  rw [hpf]
  constructor
  · intro hx
    rcases (Submodule.mem_span_range_iff_exists_fun (R := ℤ)
        (v := fun i : Fin (Module.finrank ℤ M) => realSpanIso ℒ (gen i))
        (x := x)).1 hx with ⟨c, hxeq⟩
    let sE : E := ∑ i, c i • ((Module.finBasis ℤ M i : M) : E)
    have hsE : sE ∈ M := by
      dsimp [sE]
      exact Submodule.sum_mem M (by intro i hi; exact Submodule.smul_mem M (c i) (Module.finBasis ℤ M i).2)
    have hzsum : (⟨sE, Submission.QuotientLattice.mem_realSpan (ℒ := ℒ) (x := sE) (hMle hsE)⟩ :
          Submission.QuotientLattice.realSpan ℒ) = ∑ i, c i • (gen i) := by
      apply Subtype.ext
      calc
        ((⟨sE, Submission.QuotientLattice.mem_realSpan (ℒ := ℒ) (x := sE) (hMle hsE)⟩ :
              Submission.QuotientLattice.realSpan ℒ) : E) = sE := rfl
        _ = (((∑ i, c i • (gen i)) : Submission.QuotientLattice.realSpan ℒ) : E) := by
            change ∑ i, c i • (((gen i : Submission.QuotientLattice.realSpan ℒ) : E)) =
                ((Submission.QuotientLattice.realSpan ℒ).subtype)
                  (∑ i, c i • (gen i))
            rw [map_sum]
            simp [gen]
    have hφ : realSpanIso ℒ ⟨sE, Submission.QuotientLattice.mem_realSpan (ℒ := ℒ) (x := sE) (hMle hsE)⟩ = x := by
      calc
        realSpanIso ℒ ⟨sE, Submission.QuotientLattice.mem_realSpan (ℒ := ℒ) (x := sE) (hMle hsE)⟩
            = realSpanIso ℒ (∑ i, c i • (gen i)) := by rw [hzsum]
        _ = ∑ i, c i • (realSpanIso ℒ (gen i)) := by
            change ((realSpanIso ℒ).toLinearEquiv.toLinearMap)
                (∑ i, c i • (gen i)) =
              ∑ i, c i • ((realSpanIso ℒ).toLinearEquiv.toLinearMap) (gen i)
            rw [map_sum]
            simp
        _ = x := hxeq
    exact ⟨⟨sE, hsE⟩, hφ⟩
  · intro hmm
    rcases hmm with ⟨m, hmφ⟩
    let c : Fin (Module.finrank ℤ M) → ℤ := b.repr m
    have hm : m = ∑ i, c i • (b i) := by
      simpa [c] using (b.sum_repr m).symm
    have hcar : (m : E) = ∑ i, c i • ((Module.finBasis ℤ M i : M) : E) := by
      have h0 := congrArg (fun z : ↥M => (z : E)) hm
      change (M.subtype) m = (M.subtype) (∑ i, c i • (b i)) at h0
      rw [map_sum] at h0
      simp at h0
      simpa [b] using h0
    have hzsum : (⟨((m : M) : E),
          Submission.QuotientLattice.mem_realSpan (ℒ := ℒ) (x := ((m : M) : E)) (hMle m.2)⟩ :
          Submission.QuotientLattice.realSpan ℒ) = ∑ i, c i • (gen i) := by
      apply Subtype.ext
      calc
        ((⟨((m : M) : E), Submission.QuotientLattice.mem_realSpan (ℒ := ℒ)
              (x := ((m : M) : E)) (hMle m.2)⟩ : Submission.QuotientLattice.realSpan ℒ) : E)
            = (m : E) := rfl
        _ = ∑ i, c i • ((Module.finBasis ℤ M i : M) : E) := hcar
        _ = (((∑ i, c i • (gen i)) : Submission.QuotientLattice.realSpan ℒ) : E) := by
            change ∑ i, c i • (((gen i : Submission.QuotientLattice.realSpan ℒ) : E)) =
                ((Submission.QuotientLattice.realSpan ℒ).subtype)
                  (∑ i, c i • (gen i))
            rw [map_sum]
            simp [gen]
    have hφ' : realSpanIso ℒ ⟨((m : M) : E),
          Submission.QuotientLattice.mem_realSpan (ℒ := ℒ) (x := ((m : M) : E)) (hMle m.2)⟩ =
        ∑ i, c i • (realSpanIso ℒ (gen i)) := by
      calc
        realSpanIso ℒ ⟨((m : M) : E), Submission.QuotientLattice.mem_realSpan (ℒ := ℒ)
              (x := ((m : M) : E)) (hMle m.2)⟩
            = realSpanIso ℒ (∑ i, c i • (gen i)) := by rw [hzsum]
        _ = ∑ i, c i • (realSpanIso ℒ (gen i)) := by
            change ((realSpanIso ℒ).toLinearEquiv.toLinearMap)
                (∑ i, c i • (gen i)) =
              ∑ i, c i • ((realSpanIso ℒ).toLinearEquiv.toLinearMap) (gen i)
            rw [map_sum]
            simp
    have hmem : ∑ i, c i • (realSpanIso ℒ (gen i)) ∈ (Submodule.span ℤ
        (Set.range (fun i : Fin (Module.finrank ℤ M) => realSpanIso ℒ (gen i)))) := by
      exact (Submodule.mem_span_range_iff_exists_fun (R := ℤ)
        (v := fun i : Fin (Module.finrank ℤ M) => realSpanIso ℒ (gen i))
        (x := ∑ i, c i • (realSpanIso ℒ (gen i)))).2 ⟨c, rfl⟩
    rw [← hmφ, hφ']
    exact hmem



/-- The pushforward of a discrete sublattice of `ℒ` is discrete (norm gap transfers through
the isometry `realSpanIso`). -/
lemma pushforward_discrete (ℒ : Submodule ℤ E) [DiscreteTopology ℒ]
    (M : Submodule ℤ E) [DiscreteTopology M] (hMle : M ≤ ℒ) :
    DiscreteTopology (pushforward ℒ M hMle) := by
  classical
  rcases norm_gap_of_discrete M with ⟨ε, hε, hg⟩
  apply discrete_of_norm_gap
  refine ⟨ε, hε, ?_⟩
  intro p hp0
  have hp : (p : EuclideanSpace ℝ (Fin (Module.finrank ℤ ℒ))) ∈ pushforward ℒ M hMle := p.2
  rcases (mem_pushforward_iff ℒ M hMle
      (p : EuclideanSpace ℝ (Fin (Module.finrank ℤ ℒ)))).1 hp with ⟨m, hmp⟩
  have hm0' : m ≠ 0 := by
    intro hm0
    apply hp0
    apply Subtype.ext
    have hz0 : (⟨((m : M) : E),
          Submission.QuotientLattice.mem_realSpan (ℒ := ℒ) (x := (((m : M) : E))) (hMle m.2)⟩ :
          Submission.QuotientLattice.realSpan ℒ) = 0 := by
      apply Subtype.ext
      exact congrArg (fun z : ↥M => (z : E)) hm0
    calc
      (p : EuclideanSpace ℝ (Fin (Module.finrank ℤ ℒ))) =
          realSpanIso ℒ ⟨((m : M) : E),
            Submission.QuotientLattice.mem_realSpan (ℒ := ℒ) (x := (((m : M) : E))) (hMle m.2)⟩ :=
            hmp.symm
      _ = 0 := by rw [hz0]; simp
  have hgapM : ε ≤ ‖((m : M) : E)‖ := hg m hm0'
  have hnorm : ‖(p : EuclideanSpace ℝ (Fin (Module.finrank ℤ ℒ)))‖ = ‖((m : M) : E)‖ := by
    calc
      ‖(p : EuclideanSpace ℝ (Fin (Module.finrank ℤ ℒ)))‖
          = ‖realSpanIso ℒ ⟨((m : M) : E),
              Submission.QuotientLattice.mem_realSpan (ℒ := ℒ) (x := (((m : M) : E))) (hMle m.2)⟩‖ := by rw [hmp]
      _ = ‖(⟨((m : M) : E),
              Submission.QuotientLattice.mem_realSpan (ℒ := ℒ) (x := (((m : M) : E))) (hMle m.2)⟩ :
              Submission.QuotientLattice.realSpan ℒ)‖ :=
          (realSpanIso ℒ).norm_map _
      _ = ‖((m : M) : E)‖ := by rfl
  calc
    ε ≤ ‖((m : M) : E)‖ := hgapM
    _ = ‖(p : EuclideanSpace ℝ (Fin (Module.finrank ℤ ℒ)))‖ := hnorm.symm



/-- **Determinant is preserved by the pushforward** (reverse direction).  The independence of
the transported family is proved through φ⁻¹ and carriers (avoiding `of_comp` over the real
span, which blows up typeclass synthesis); the Gram matrices agree by the isometry. -/
lemma det_pushforward (ℒ : Submodule ℤ E) [DiscreteTopology ℒ]
    (M : Submodule ℤ E) [DiscreteTopology M] (hMle : M ≤ ℒ)
    [DiscreteTopology (pushforward ℒ M hMle)] :
    ReverseMinkowski.determinant (pushforward ℒ M hMle) = ReverseMinkowski.determinant M := by
  classical
  haveI : Module.Free ℤ ℒ := instModuleFree_of_discrete_submodule ℒ
  haveI : Module.Finite ℤ ℒ := instModuleFinite_of_discrete_submodule ℒ
  haveI : Module.Free ℤ M := instModuleFree_of_discrete_submodule M
  haveI : Module.Finite ℤ M := instModuleFinite_of_discrete_submodule M
  haveI : Module.Free ℤ (pushforward ℒ M hMle) := instModuleFree_of_discrete_submodule (pushforward ℒ M hMle)
  haveI : Module.Finite ℤ (pushforward ℒ M hMle) := instModuleFinite_of_discrete_submodule (pushforward ℒ M hMle)
  let bM : Module.Basis (Fin (Module.finrank ℤ M)) ℤ (↥M) := Module.finBasis ℤ M
  let wM : Fin (Module.finrank ℤ M) → E := fun i => ((bM i : ↥M) : E)
  let z : Fin (Module.finrank ℤ M) →
      Submission.QuotientLattice.realSpan ℒ := fun i =>
    ⟨wM i, Submission.QuotientLattice.mem_realSpan (ℒ := ℒ) (x := wM i) (hMle (bM i).2)⟩
  let v : Fin (Module.finrank ℤ M) → EuclideanSpace ℝ (Fin (Module.finrank ℤ ℒ)) :=
    fun i => realSpanIso ℒ (z i)
  have hli_wM : LinearIndependent ℤ wM := by
    have hb0 : LinearIndependent ℤ (fun i : Fin (Module.finrank ℤ M) => ((bM i : ↥M) : E)) := by
      exact bM.linearIndependent.map' (M.subtype) (by
        rw [LinearMap.ker_eq_bot]
        intro x y h
        exact Subtype.ext h)
    simpa [wM, bM] using hb0
  have hli_v : LinearIndependent ℤ v := by
    rw [Fintype.linearIndependent_iff]
    intro c hsum
    have hsym : (realSpanIso ℒ).symm (∑ i, c i • v i) = 0 := by
      simpa using congrArg ((realSpanIso ℒ).symm) hsum
    have hlin : (realSpanIso ℒ).symm (∑ i : Fin (Module.finrank ℤ M), c i • v i) =
        ∑ i : Fin (Module.finrank ℤ M), c i • z i := by
      rw [map_sum]
      refine Finset.sum_congr rfl ?_
      intro i hi
      have hzv : (realSpanIso ℒ).symm (v i) = z i := by
        change (realSpanIso ℒ).symm (realSpanIso ℒ (z i)) = z i
        exact (realSpanIso ℒ).symm_apply_apply (z i)
      calc
        (realSpanIso ℒ).symm (c i • v i) = c i • (realSpanIso ℒ).symm (v i) := by
            exact map_zsmul ((realSpanIso ℒ).symm) (c i) (v i)
        _ = c i • z i := by rw [hzv]
    have h0 : (∑ i : Fin (Module.finrank ℤ M), c i • z i) = 0 := by
      rwa [hlin] at hsym
    have hcar0 : (∑ i : Fin (Module.finrank ℤ M), c i • wM i) = 0 := by
      have hc0 := congrArg (fun w : ↥(Submission.QuotientLattice.realSpan ℒ) => (w : E)) h0
      change ((Submission.QuotientLattice.realSpan ℒ).subtype) (∑ i, c i • z i) = (0 : E) at hc0
      rw [map_sum] at hc0
      simp at hc0
      simpa [z, wM] using hc0
    exact (Fintype.linearIndependent_iff.mp hli_wM) c hcar0
  have hspan : pushforward ℒ M hMle ≤ Submodule.span ℤ (Set.range v) := by
    refine Submodule.span_le.mpr ?_
    intro y hy
    rcases hy with ⟨i, hiy⟩
    subst y
    have hzi : (⟨(((Module.finBasis ℤ M i : M) : E)),
          Submission.QuotientLattice.mem_realSpan (ℒ := ℒ)
            (x := (((Module.finBasis ℤ M i : M) : E))) (hMle (Module.finBasis ℤ M i).2)⟩ :
          Submission.QuotientLattice.realSpan ℒ) = z i := by
      apply Subtype.ext
      simp [z, wM, bM]
    have hvi : realSpanIso ℒ ⟨(((Module.finBasis ℤ M i : M) : E)),
          Submission.QuotientLattice.mem_realSpan (ℒ := ℒ)
            (x := (((Module.finBasis ℤ M i : M) : E))) (hMle (Module.finBasis ℤ M i).2)⟩ = v i := by
      rw [hzi]
    exact Submodule.subset_span (by exact ⟨i, hvi.symm⟩)
  have hmem : ∀ i : Fin (Module.finrank ℤ M), v i ∈ pushforward ℒ M hMle := by
    intro i
    exact Submodule.subset_span (by exact ⟨i, rfl⟩)
  rcases (basis_of_ambient (M := pushforward ℒ M hMle) (w := v) hspan hmem hli_v) with ⟨βP, hβPval⟩
  have hgram_eq : Matrix.gram ℝ v = Matrix.gram ℝ wM := by
    ext a b
    simp only [Matrix.gram]
    calc
      ⟪v a, v b⟫_ℝ = ⟪realSpanIso ℒ (z a), realSpanIso ℒ (z b)⟫_ℝ := by simp [v]
      _ = ⟪z a, z b⟫_ℝ := by exact (realSpanIso ℒ).inner_map_map (z a) (z b)
      _ = ⟪((z a : Submission.QuotientLattice.realSpan ℒ) : E),
            ((z b : Submission.QuotientLattice.realSpan ℒ) : E)⟫_ℝ := by
          exact inner_of_submodule (Submission.QuotientLattice.realSpan ℒ) (z a) (z b)
      _ = ⟪wM a, wM b⟫_ℝ := by simp [wM, z]
  have hgramP : Matrix.gram ℝ (fun i : Fin (Module.finrank ℤ M) =>
        ((βP i : pushforward ℒ M hMle) : EuclideanSpace ℝ (Fin (Module.finrank ℤ ℒ)))) =
      Matrix.gram ℝ v := by
    ext a b
    simp [Matrix.gram, hβPval]
  have hgramM : Matrix.gram ℝ (fun i : Fin (Module.finrank ℤ M) =>
        (((Module.finBasis ℤ M i : M) : E))) = Matrix.gram ℝ wM := by
    simp [wM, bM]
  have hdetP : ReverseMinkowski.determinant (pushforward ℒ M hMle) =
      Real.sqrt ((Matrix.gram ℝ v).det) := by
    have h0 := det_eq_sqrt_gram_any_basis (L := pushforward ℒ M hMle) βP
    rw [h0, hgramP]
  have hdetM : ReverseMinkowski.determinant M =
      Real.sqrt ((Matrix.gram ℝ wM).det) := by
    have h0 := det_eq_sqrt_gram_any_basis (L := M) (Module.finBasis ℤ M)
    rw [h0, hgramM]
  rw [hdetP, hdetM, hgram_eq]

/-- **Stability transports back from the transported lattice** (reverse direction). -/
lemma stable_transported_of_stable (ℒ : Submodule ℤ E) [DiscreteTopology ℒ]
    [DiscreteTopology (transLattice ℒ)]
    (hSt : Submission.StableLattices.Stable (transLattice ℒ)) :
    Submission.StableLattices.Stable ℒ := by
  constructor
  · rw [← det_transported ℒ]
    exact Submission.StableLattices.det_eq_one_of_stable hSt
  · intro M hMle _hDTM
    haveI dtF : DiscreteTopology (pushforward ℒ M hMle) := pushforward_discrete ℒ M hMle
    have hdet : ReverseMinkowski.determinant M =
        ReverseMinkowski.determinant (pushforward ℒ M hMle) :=
      (det_pushforward ℒ M hMle).symm
    rw [hdet]
    exact hSt.2 (pushforward ℒ M hMle) (pushforward_le_transLattice ℒ M hMle)

/-- **Stability is preserved by the transport, in both directions.** -/
lemma stable_transported_iff (ℒ : Submodule ℤ E) [DiscreteTopology ℒ]
    [DiscreteTopology (transLattice ℒ)] :
    Submission.StableLattices.Stable (transLattice ℒ) ↔
      Submission.StableLattices.Stable ℒ := by
  exact ⟨stable_transported_of_stable ℒ, stable_of_stable_transported ℒ⟩


end Submission.Transport
