import Mathlib
import ChallengeDeps
import Submission.QuotientLattice
import Submission.DetQuot
import Submission.Commons.Lattice.Module.basis_extension_pure_rank
import Submission.Commons.LinearAlgebra.Independence.discrete_basis_values_linIndep
import Submission.Commons.LinearAlgebra.Projection.linearIndependent_proj_complement
import Submission.Commons.Analysis.InnerProductSpace.gram_det_shear_orthogonal

open Module MeasureTheory Metric
open Submission.QuotientLattice
open scoped Real BigOperators InnerProductSpace RealInnerProductSpace ENNReal NNReal Pointwise
set_option autoImplicit false
set_option linter.style.haveILetI false

/-!
# Rank-generic sublattice theory (paper §2.5)

A "rank-generic" lattice is a discrete `ℤ`-submodule `ℒ ≤ E` of the ambient
`E = EuclideanSpace ℝ (Fin nA)` of *arbitrary* `ℤ`-rank `m ≤ nA` (no full-rank /
`IsZLattice` hypothesis).  All previous machinery (`Submission/QuotientLattice.lean`,
`Submission/DetQuot.lean`) was built for full-rank lattices whose ℤ-basis is indexed by
`Fin nA` (ambient dimension = lattice rank).  This module re-does the adapted-basis
quotient chain and the quotient determinant identity in the rank-generic setting, with a
ℤ-basis `e : Basis (Fin m) ℤ ℒ` of arbitrary length `m`.

The main deliverable is `determinant_quot_generic`:

    det (quotLattice ℒ S) = det ℒ / det ℒ'        (ℒ' ≤ ℒ primitive, S = spanℝ ℒ')

with no full-rank hypothesis on `ℒ`.  This is the key enabler for the stable-lattice
programme of paper §2.5/§2.6 (Stuhler uncrossing Lemma 2.4, canonical filtration
quotients `αᵢ (Lᵢ/Lᵢ₋₁)`, direct-sum-stable, boundary characterization), where
intermediate-rank sublattices `ℒ' ⊆ ℒ` appear.
-/


namespace Submission.SubLattice

variable {nA m : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin nA)

noncomputable section

/-- The inclusion-based ℤ-linear equivalence `ℒ' ≃ₗ comap ℒ.subtype ℒ'` with `rfl`-level
coercions to the ambient space. -/
noncomputable def comapEquiv {ℒ' ℒ : Submodule ℤ E} (hle : ℒ' ≤ ℒ) :
    ℒ' ≃ₗ[ℤ] (ℒ'.comap (ℒ.subtype)) where
  toFun := fun y => ⟨⟨(y : E), hle y.2⟩, by
    rw [Submodule.mem_comap]
    exact y.2⟩
  invFun := fun z => ⟨((z.1 : ↥ℒ) : E), by
    simpa [Submodule.subtype_apply] using (Submodule.mem_comap.mp z.2)⟩
  left_inv := by
    intro y
    apply Subtype.ext
    rfl
  right_inv := by
    intro z
    apply Subtype.ext
    rfl
  map_add' := by intro x y; ext <;> rfl
  map_smul' := by intro a x; ext <;> rfl

lemma comapEquiv_val {ℒ' ℒ : Submodule ℤ E} (hle : ℒ' ≤ ℒ) (y : ℒ') :
    (((comapEquiv (ℒ' := ℒ') (ℒ := ℒ) hle y : ℒ'.comap (ℒ.subtype)) : ℒ) : E) = (y : E) := by
  rfl

/-- Purity of the comap `ℒ'.comap ℒ.subtype` in `ℒ`, from ambient primitivity. -/
lemma comap_pure {ℒ' ℒ : Submodule ℤ E} (hp : Primitive ℒ' ℒ)
    (x : ℒ) (a : ℤ) (ha : a ≠ 0)
    (hax : a • x ∈ ℒ'.comap (ℒ.subtype)) : x ∈ ℒ'.comap (ℒ.subtype) := by
  rw [Submodule.mem_comap] at hax ⊢
  apply (hp (x : E)).mpr
  constructor
  · exact x.2
  · have hmemS : (a : ℤ) • (x : E) ∈ realSpan (ℒ := ℒ') := by
      exact mem_realSpan (ℒ := ℒ') hax
    have hxeq : (x : E) = ((a : ℝ)⁻¹ • ((a : ℤ) • (x : E))) := by
      rw [← Int.cast_smul_eq_zsmul ℝ a (x : E)]
      simp [ha]
    rw [hxeq]
    exact Submodule.smul_mem _ ((a : ℝ)⁻¹) hmemS

/-- Adapted basis of ℒ (of any rank `m = finrank ℤ ℒ`), whose first `d = finrank ℤ ℒ'`
values are the canonical basis values of `ℒ'`. -/
lemma adapted_basis {ℒ' ℒ : Submodule ℤ E} [DiscreteTopology ℒ] [DiscreteTopology ℒ']
    (hp : Primitive ℒ' ℒ) :
    ∃ (hd : Module.finrank ℤ ℒ' ≤ Module.finrank ℤ ℒ)
      (e : Module.Basis (Fin (Module.finrank ℤ ℒ)) ℤ ℒ),
      ∀ i : Fin (Module.finrank ℤ ℒ'),
        ((e (Fin.castLE hd i) : ℒ) : E) = ((Module.finBasis ℤ ℒ' i : ℒ') : E) := by
  classical
  haveI : Module.Free ℤ ℒ := instModuleFree_of_discrete_submodule ℒ
  haveI : Module.Finite ℤ ℒ := instModuleFinite_of_discrete_submodule ℒ
  haveI : Module.Free ℤ ℒ' := instModuleFree_of_discrete_submodule ℒ'
  haveI : Module.Finite ℤ ℒ' := instModuleFinite_of_discrete_submodule ℒ'
  let m := Module.finrank ℤ ℒ
  let d := Module.finrank ℤ ℒ'
  let hle : ℒ' ≤ ℒ := Primitive.le hp
  let hd : d ≤ m := by
    dsimp [d, m]
    exact finrank_le_of_le (ℒ' := ℒ') (ℒ := ℒ) hle
  let N : Submodule ℤ ℒ := ℒ'.comap (ℒ.subtype)
  let bM : Module.Basis (Fin m) ℤ ℒ := Module.finBasis ℤ ℒ
  let bN : Module.Basis (Fin d) ℤ N :=
    (Module.finBasis ℤ ℒ').map (comapEquiv (ℒ' := ℒ') (ℒ := ℒ) hle)
  have hpure : ∀ x : ℒ, (∃ a : ℤ, a ≠ 0 ∧ a • x ∈ N) → x ∈ N := by
    intro x hx
    rcases hx with ⟨a, ha, hax⟩
    exact comap_pure (ℒ' := ℒ') (ℒ := ℒ) hp x a ha hax
  rcases (Commons.Lattice.Module.basis_extension_pure_rank (hd := hd) (M := ℒ) (N := N)
    (bM := bM) (bN := bN) (hpure := hpure)) with ⟨e, he⟩
  refine ⟨hd, e, ?_⟩
  intro i
  have he0 := he i
  have hval : ((((bN i : N) : ℒ) : E)) = ((Module.finBasis ℤ ℒ' i : ℒ') : E) := by
    dsimp [bN, N]
    change ((((comapEquiv (ℒ' := ℒ') (ℒ := ℒ) hle (Module.finBasis ℤ ℒ' i)) : N) : ℒ) : E) =
      ((Module.finBasis ℤ ℒ' i : ℒ') : E)
    exact comapEquiv_val (ℒ' := ℒ') (ℒ := ℒ) hle (Module.finBasis ℤ ℒ' i)
  calc
    ((e (Fin.castLE hd i) : ℒ) : E) = ((((bN i : N) : ℒ)) : E) := by rw [he0]
    _ = ((Module.finBasis ℤ ℒ' i : ℒ') : E) := hval

/-- The values of a ℤ-basis of a discrete lattice are ℝ-linearly independent in the
ambient space. -/
lemma basis_values_linIndep {ℒ : Submodule ℤ E} [DiscreteTopology ℒ]
    {m : ℕ} (e : Module.Basis (Fin m) ℤ ℒ) :
    LinearIndependent ℝ (fun k : Fin m => ((e k : ℒ) : E)) := by
  exact Commons.LinearAlgebra.Independence.discrete_basis_values_linIndep (ℒ := ℒ) (m := m) e

/-- The quotient lattice is generated by the projections of all basis values (rank-generic). -/
lemma quotLattice_eq_span_proj {ℒ : Submodule ℤ E}
    (b : Module.Basis (Fin m) ℤ ℒ) (S : Submodule ℝ E) :
    quotLattice ℒ S = Submodule.span ℤ
      (Set.range (fun j : Fin m => Sᗮ.starProjection ((b j : ℒ) : E))) := by
  classical
  let p : E →ₗ[ℤ] E := (Sᗮ.starProjection : E →ₗ[ℝ] E).restrictScalars ℤ
  apply le_antisymm
  · intro z hz
    rw [mem_quotLattice] at hz
    rcases hz with ⟨y, hy, hzy⟩
    have hy' : (y : E) = ∑ j : Fin m, (b.repr ⟨y, hy⟩ j : ℤ) • ((b j : ℒ) : E) := by
      simpa using (ambient_basis_expand (ℒ := ℒ) (b := b) ⟨y, hy⟩)
    rw [← hzy]
    change p (y : E) ∈ Submodule.span ℤ
      (Set.range (fun j : Fin m => Sᗮ.starProjection ((b j : ℒ) : E)))
    rw [hy']
    rw [map_sum]
    apply Submodule.sum_mem
    intro j hj
    rw [map_smul p (b.repr ⟨y, hy⟩ j : ℤ) ((b j : ℒ) : E)]
    apply Submodule.smul_mem
    apply Submodule.subset_span
    exact ⟨j, rfl⟩
  · rw [Submodule.span_le]
    intro z hz
    rcases hz with ⟨j, hz⟩
    rw [← hz]
    exact Submodule.mem_map.mpr ⟨(b j : ℒ), (b j : ℒ).2, rfl⟩

/-- When the projections of the first d basis vectors vanish, the quotient lattice is
generated by the projected tail (rank-generic). -/
lemma quotLattice_eq_span_tail {ℒ : Submodule ℤ E} {d : ℕ} (hd : d ≤ m)
    (b : Module.Basis (Fin m) ℤ ℒ) (S : Submodule ℝ E)
    (hzero : ∀ i : Fin d, Sᗮ.starProjection ((b (Fin.castLE hd i) : ℒ) : E) = 0) :
    quotLattice ℒ S = Submodule.span ℤ
      (Set.range (fun j : Fin (m - d) => Sᗮ.starProjection ((b (tailEmb (n := m) hd j) : ℒ) : E))) := by
  classical
  have hspan := quotLattice_eq_span_proj (ℒ := ℒ) b S
  rw [hspan]
  apply le_antisymm
  · rw [Submodule.span_le]
    intro z hz
    rcases hz with ⟨k, hz⟩
    rw [← hz]
    by_cases hk : k.val < d
    · have hk' : k = Fin.castLE hd ⟨k.val, hk⟩ := by
        apply Fin.ext
        rfl
      have hz0 : Sᗮ.starProjection ((b k : ℒ) : E) = 0 := by
        rw [hk']
        exact hzero ⟨k.val, hk⟩
      change Sᗮ.starProjection ((b k : ℒ) : E) ∈
        Submodule.span ℤ (Set.range (fun j : Fin (m - d) => Sᗮ.starProjection ((b (tailEmb (n := m) hd j) : ℒ) : E)))
      rw [hz0]
      apply Submodule.zero_mem
    · let k' : Fin (m - d) := ⟨k.val - d, by omega⟩
      have hdval : d ≤ k.val := le_of_not_gt hk
      have hkt : k = tailEmb (n := m) hd k' := by
        apply Fin.ext
        dsimp [tailEmb]
        dsimp [k']
        omega
      change Sᗮ.starProjection ((b k : ℒ) : E) ∈
        Submodule.span ℤ (Set.range (fun j : Fin (m - d) => Sᗮ.starProjection ((b (tailEmb (n := m) hd j) : ℒ) : E)))
      rw [hkt]
      apply Submodule.subset_span
      exact ⟨k', rfl⟩
  · rw [Submodule.span_le]
    intro z hz
    rcases hz with ⟨j, hz⟩
    rw [← hz]
    apply Submodule.subset_span
    exact ⟨tailEmb (n := m) hd j, rfl⟩

/-- Adapted basis + tail-spanning of the quotient lattice, rank-generic version. -/
lemma adapted_span_tail {ℒ' ℒ : Submodule ℤ E} [DiscreteTopology ℒ] [DiscreteTopology ℒ']
    (S : Submodule ℝ E) (hS : S = realSpan ℒ') (hp : Primitive ℒ' ℒ)
    (hd : Module.finrank ℤ ℒ' ≤ m) (e : Module.Basis (Fin m) ℤ ℒ)
    (he : ∀ i : Fin (Module.finrank ℤ ℒ'),
      ((e (Fin.castLE hd i) : ℒ) : E) = ((Module.finBasis ℤ ℒ' i : ℒ') : E)) :
    quotLattice ℒ S = Submodule.span ℤ
      (Set.range (fun j : Fin (m - Module.finrank ℤ ℒ') =>
        Sᗮ.starProjection (((e (tailEmb (n := m) hd j) : ℒ)) : E))) := by
  classical
  have hzero : ∀ i : Fin (Module.finrank ℤ ℒ'),
      Sᗮ.starProjection (((e (Fin.castLE hd i) : ℒ)) : E) = 0 := by
    intro i
    have hval : ((e (Fin.castLE hd i) : ℒ) : E) = ((Module.finBasis ℤ ℒ' i : ℒ') : E) := he i
    have hxS : ((e (Fin.castLE hd i) : ℒ) : E) ∈ S := by
      rw [hval]
      rw [hS]
      exact mem_realSpan (ℒ := ℒ') (Module.finBasis ℤ ℒ' i).2
    exact starProjection_orthogonal_eq_zero_of_mem S hxS
  exact quotLattice_eq_span_tail (m := m) hd e S hzero

/-- The projected tail of an adapted basis is ℤ-linearly independent, rank-generic. -/
lemma tail_values_linIndep_Z {ℒ' ℒ : Submodule ℤ E} [DiscreteTopology ℒ] [DiscreteTopology ℒ']
    (S : Submodule ℝ E) (hS : S = realSpan ℒ') (hp : Primitive ℒ' ℒ)
    (hd : Module.finrank ℤ ℒ' ≤ m) (e : Module.Basis (Fin m) ℤ ℒ)
    (he : ∀ i : Fin (Module.finrank ℤ ℒ'),
      ((e (Fin.castLE hd i) : ℒ) : E) = ((Module.finBasis ℤ ℒ' i : ℒ') : E)) :
    LinearIndependent ℤ (fun j : Fin (m - Module.finrank ℤ ℒ') =>
      Sᗮ.starProjection (((e (tailEmb (n := m) hd j) : ℒ)) : E)) := by
  classical
  haveI : Module.Free ℤ ℒ := instModuleFree_of_discrete_submodule ℒ
  haveI : Module.Finite ℤ ℒ := instModuleFinite_of_discrete_submodule ℒ
  haveI : Module.Free ℤ ℒ' := instModuleFree_of_discrete_submodule ℒ'
  haveI : Module.Finite ℤ ℒ' := instModuleFinite_of_discrete_submodule ℒ'
  have hS' : S = Submodule.span ℝ (Set.range
      (fun i : Fin (Module.finrank ℤ ℒ') => ((e (Fin.castLE hd i) : ℒ) : E))) := by
    rw [hS]
    have hb : realSpan ℒ' = Submodule.span ℝ (Set.range
        (fun i : Fin (Module.finrank ℤ ℒ') => ((Module.finBasis ℤ ℒ' i : ℒ') : E))) :=
      realSpan_eq_span_basis (ℒ := ℒ')
    rw [hb]
    congr 1
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      refine ⟨i, he i⟩
    · rintro ⟨i, rfl⟩
      refine ⟨i, (he i).symm⟩
  have hf : LinearIndependent ℝ (Sum.elim
      (fun i : Fin (Module.finrank ℤ ℒ') => ((e (Fin.castLE hd i) : ℒ) : E))
      (fun j : Fin (m - Module.finrank ℤ ℒ') => ((e (tailEmb (n := m) hd j) : ℒ) : E))) := by
    have hfeq : Sum.elim
        (fun i : Fin (Module.finrank ℤ ℒ') => ((e (Fin.castLE hd i) : ℒ) : E))
        (fun j : Fin (m - Module.finrank ℤ ℒ') => ((e (tailEmb (n := m) hd j) : ℒ) : E)) =
        (fun x : Fin (Module.finrank ℤ ℒ') ⊕ Fin (m - Module.finrank ℤ ℒ') =>
          ((e (finSplitMap (n := m) hd x) : ℒ) : E)) := by
      funext x
      cases x with
      | inl i => rfl
      | inr j => rfl
    rw [hfeq]
    exact (basis_values_linIndep (ℒ := ℒ) e).comp (finSplitMap (n := m) hd)
      (finSplitMap_injective (n := m) hd)
  have hc := Commons.LinearAlgebra.Projection.linearIndependent_proj_complement (n := nA)
    (d := Module.finrank ℤ ℒ') (r := m - Module.finrank ℤ ℒ')
    (u := fun i : Fin (Module.finrank ℤ ℒ') => ((e (Fin.castLE hd i) : ℒ) : E))
    (v := fun j : Fin (m - Module.finrank ℤ ℒ') => ((e (tailEmb (n := m) hd j) : ℒ) : E))
    S hS' hf
  have hprojR : LinearIndependent ℝ (fun j : Fin (m - Module.finrank ℤ ℒ') =>
      Sᗮ.starProjection (((e (tailEmb (n := m) hd j) : ℒ)) : E)) := by
    simpa using hc
  exact hprojR.restrict_scalars' ℤ

/-- Basis of the quotient lattice from an adapted basis of ℒ, rank-generic. -/
lemma quotBasis_of_adapted {ℒ' ℒ : Submodule ℤ E} [DiscreteTopology ℒ] [DiscreteTopology ℒ']
    (S : Submodule ℝ E) (hS : S = realSpan ℒ') (hp : Primitive ℒ' ℒ)
    (hd : Module.finrank ℤ ℒ' ≤ m) (e : Module.Basis (Fin m) ℤ ℒ)
    (he : ∀ i : Fin (Module.finrank ℤ ℒ'),
      ((e (Fin.castLE hd i) : ℒ) : E) = ((Module.finBasis ℤ ℒ' i : ℒ') : E)) :
    ∃ β : Module.Basis (Fin (m - Module.finrank ℤ ℒ')) ℤ (quotLattice ℒ S),
      ∀ j : Fin (m - Module.finrank ℤ ℒ'),
        ((β j : quotLattice ℒ S) : E) =
          Sᗮ.starProjection (((e (tailEmb (n := m) hd j) : ℒ)) : E) := by
  classical
  let P : Submodule ℤ E := quotLattice ℒ S
  let w' : Fin (m - Module.finrank ℤ ℒ') → P := fun j =>
    ⟨Sᗮ.starProjection (((e (tailEmb (n := m) hd j) : ℒ)) : E), by
      rw [mem_quotLattice]
      exact ⟨(e (tailEmb (n := m) hd j) : ℒ), (e (tailEmb (n := m) hd j) : ℒ).2, rfl⟩⟩
  have hvals : (fun j : Fin (m - Module.finrank ℤ ℒ') => ((w' j : P) : E)) =
      (fun j : Fin (m - Module.finrank ℤ ℒ') =>
        Sᗮ.starProjection (((e (tailEmb (n := m) hd j) : ℒ)) : E)) := by
    funext j
    rfl
  have hspanQ : Submodule.span ℤ (Set.range (fun j : Fin (m - Module.finrank ℤ ℒ') => ((w' j : P) : E))) = P := by
    rw [hvals]
    dsimp [P]
    exact (adapted_span_tail (ℒ' := ℒ') (ℒ := ℒ) S hS hp hd e he).symm
  have hspanInt : ⊤ ≤ Submodule.span ℤ (Set.range w') := by
    intro z hz
    have hzQ : (z : E) ∈ (P : Set E) := z.2
    have hzspanE : (z : E) ∈ (Submodule.span ℤ (Set.range
        (fun j : Fin (m - Module.finrank ℤ ℒ') => ((w' j : P) : E))) : Set E) := by
      simpa [hspanQ] using hzQ
    rcases (Submodule.mem_span_range_iff_exists_fun (R := ℤ)
        (v := fun j : Fin (m - Module.finrank ℤ ℒ') => ((w' j : P) : E)) (x := (z : E))).mp hzspanE with ⟨c, hc⟩
    have hzP : (∑ j : Fin (m - Module.finrank ℤ ℒ'), c j • (w' j : P)) = z := by
      apply Subtype.ext
      calc
        (((∑ j : Fin (m - Module.finrank ℤ ℒ'), c j • (w' j : P)) : P) : E)
            = (P.subtype : P →ₗ[ℤ] E) (∑ j : Fin (m - Module.finrank ℤ ℒ'), c j • (w' j : P)) := rfl
        _ = ∑ j : Fin (m - Module.finrank ℤ ℒ'), c j • ((w' j : P) : E) := by
            rw [map_sum]
            simp
        _ = (z : E) := hc
    exact (Submodule.mem_span_range_iff_exists_fun (R := ℤ) (v := w') (x := z)).2 ⟨c, hzP⟩
  have hliQ : LinearIndependent ℤ w' := by
    apply Commons.LinearAlgebra.Independence.linearIndependent_of_ambient (P := P) (v := w')
    rw [hvals]
    exact tail_values_linIndep_Z (ℒ' := ℒ') (ℒ := ℒ) S hS hp hd e he
  let β : Module.Basis (Fin (m - Module.finrank ℤ ℒ')) ℤ P := Module.Basis.mk hliQ hspanInt
  refine ⟨β, ?_⟩
  intro j
  have hb : (β j : P) = w' j := by
    simp [β, w']
  rw [hb]

/-- Adapted basis of ℒ together with a basis of the quotient lattice, rank-generic. -/
lemma exists_adapted_quotBasis {ℒ' ℒ : Submodule ℤ E} [DiscreteTopology ℒ] [DiscreteTopology ℒ']
    (S : Submodule ℝ E) (hS : S = realSpan ℒ') (hp : Primitive ℒ' ℒ) :
    ∃ (hd : Module.finrank ℤ ℒ' ≤ Module.finrank ℤ ℒ)
      (e : Module.Basis (Fin (Module.finrank ℤ ℒ)) ℤ ℒ)
      (β : Module.Basis (Fin (Module.finrank ℤ ℒ - Module.finrank ℤ ℒ')) ℤ (quotLattice ℒ S)),
      (∀ i : Fin (Module.finrank ℤ ℒ'),
        ((e (Fin.castLE hd i) : ℒ) : E) = ((Module.finBasis ℤ ℒ' i : ℒ') : E)) ∧
      (∀ j : Fin (Module.finrank ℤ ℒ - Module.finrank ℤ ℒ'),
        ((β j : quotLattice ℒ S) : E) =
          Sᗮ.starProjection (((e (tailEmb (n := Module.finrank ℤ ℒ) hd j) : ℒ)) : E)) := by
  classical
  haveI : Module.Free ℤ ℒ := instModuleFree_of_discrete_submodule ℒ
  haveI : Module.Finite ℤ ℒ := instModuleFinite_of_discrete_submodule ℒ
  haveI : Module.Free ℤ ℒ' := instModuleFree_of_discrete_submodule ℒ'
  haveI : Module.Finite ℤ ℒ' := instModuleFinite_of_discrete_submodule ℒ'
  rcases (adapted_basis (ℒ' := ℒ') (ℒ := ℒ) hp) with ⟨hd, e, he⟩
  let m := Module.finrank ℤ ℒ
  rcases (quotBasis_of_adapted (ℒ' := ℒ') (ℒ := ℒ) S hS hp (m := m) hd e he) with ⟨β, hβval⟩
  refine ⟨hd, e, β, ?_⟩
  constructor
  · intro i
    exact he i
  · exact hβval

/-- The real span `S` equals the real span of the first-d adapted values, rank-generic. -/
lemma head_span_eq {ℒ' ℒ : Submodule ℤ E} [DiscreteTopology ℒ] [DiscreteTopology ℒ']
    (S : Submodule ℝ E) (hS : S = realSpan ℒ')
    (hd : Module.finrank ℤ ℒ' ≤ m) (e : Module.Basis (Fin m) ℤ ℒ)
    (he : ∀ i : Fin (Module.finrank ℤ ℒ'),
      ((e (Fin.castLE hd i) : ℒ) : E) = ((Module.finBasis ℤ ℒ' i : ℒ') : E)) :
    S = Submodule.span ℝ (Set.range
      (fun i : Fin (Module.finrank ℤ ℒ') => ((e (Fin.castLE hd i) : ℒ) : E))) := by
  classical
  haveI : Module.Free ℤ ℒ' := instModuleFree_of_discrete_submodule ℒ'
  haveI : Module.Finite ℤ ℒ' := instModuleFinite_of_discrete_submodule ℒ'
  rw [hS]
  have hb : realSpan ℒ' = Submodule.span ℝ (Set.range
      (fun i : Fin (Module.finrank ℤ ℒ') => ((Module.finBasis ℤ ℒ' i : ℒ') : E))) :=
    realSpan_eq_span_basis (ℒ := ℒ')
  rw [hb]
  congr 1
  ext x
  constructor
  · rintro ⟨i, rfl⟩
    refine ⟨i, he i⟩
  · rintro ⟨i, rfl⟩
    refine ⟨i, (he i).symm⟩

/-- determinant of the Gram matrix of a basis family equals that of its (head, tail) split. -/
lemma gram_det_head_tail {ℒ : Submodule ℤ E} (e : Module.Basis (Fin m) ℤ ℒ) {d : ℕ}
    (hd : d ≤ m) :
    let u : Fin d → E := fun i => ((e (Fin.castLE hd i) : ℒ) : E)
    let x : Fin (m - d) → E := fun j => ((e (tailEmb (n := m) hd j) : ℒ) : E)
    (Matrix.gram ℝ (fun k : Fin m => ((e k : ℒ) : E))).det =
      (Matrix.gram ℝ (Sum.elim u x)).det := by
  classical
  intro u x
  let φ : Fin m ≃ (Fin d ⊕ Fin (m - d)) := (Commons.Lattice.Module.BasisExtensionPure.blockEquiv hd).symm
  have hq : ∀ q : Fin d ⊕ Fin (m - d), Sum.elim u x q =
      ((e (Commons.Lattice.Module.BasisExtensionPure.blockEquiv hd q) : ℒ) : E) := by
    intro q
    cases q with
    | inl i => rfl
    | inr j => rfl
  have hpoint : (fun k : Fin m => ((e k : ℒ) : E)) = Sum.elim u x ∘ φ := by
    funext k
    have hqk : Sum.elim u x (φ k) = ((e ((Commons.Lattice.Module.BasisExtensionPure.blockEquiv hd) (φ k)) : ℒ) : E) :=
      hq (φ k)
    have hidx : ((Commons.Lattice.Module.BasisExtensionPure.blockEquiv hd) (φ k) : Fin m) = k := by
      dsimp [φ]
      exact ((Commons.Lattice.Module.BasisExtensionPure.blockEquiv hd).right_inv k)
    calc
      ((e k : ℒ) : E) = ((e ((Commons.Lattice.Module.BasisExtensionPure.blockEquiv hd) (φ k)) : ℒ) : E) := by rw [hidx]
      _ = Sum.elim u x (φ k) := hqk.symm
  calc
    (Matrix.gram ℝ (fun k : Fin m => ((e k : ℒ) : E))).det
        = (Matrix.gram ℝ (Sum.elim u x ∘ φ)).det := by rw [hpoint]
    _ = (Matrix.gram ℝ (Sum.elim u x)).det := by
        change (Matrix.gram ℝ (Sum.elim u x ∘ φ)).det = (Matrix.gram ℝ (Sum.elim u x)).det
        have hg : Matrix.gram ℝ (Sum.elim u x ∘ φ) = (Matrix.gram ℝ (Sum.elim u x)).submatrix φ φ := by
          ext k l
          simp [Matrix.gram]
        rw [hg]
        simp

 
/-- **Rank-generic quotient determinant identity**: for `ℒ' ≤ ℒ` ambient-primitive with
`S = spanℝ ℒ'`, `det (quotLattice ℒ S) = det ℒ / det ℒ'`. No full-rank hypothesis on `ℒ`. -/
theorem determinant_quot_generic {ℒ' ℒ : Submodule ℤ E} [DiscreteTopology ℒ] [DiscreteTopology ℒ']
    (S : Submodule ℝ E) (hS : S = realSpan ℒ') (hp : Primitive ℒ' ℒ)
    [DiscreteTopology (quotLattice ℒ S)] :
    ReverseMinkowski.determinant (quotLattice ℒ S) =
      ReverseMinkowski.determinant ℒ / ReverseMinkowski.determinant ℒ' := by
  classical
  haveI : Module.Free ℤ ℒ := instModuleFree_of_discrete_submodule ℒ
  haveI : Module.Finite ℤ ℒ := instModuleFinite_of_discrete_submodule ℒ
  haveI : Module.Free ℤ ℒ' := instModuleFree_of_discrete_submodule ℒ'
  haveI : Module.Finite ℤ ℒ' := instModuleFinite_of_discrete_submodule ℒ'
  rcases exists_adapted_quotBasis (ℒ' := ℒ') (ℒ := ℒ) S hS hp with ⟨hd, e, β, he, hβval⟩
  haveI : Module.Free ℤ (quotLattice ℒ S) := Module.Free.of_basis β
  haveI : Module.Finite ℤ (quotLattice ℒ S) := Module.Finite.of_basis β
  let m := Module.finrank ℤ ℒ
  let d := Module.finrank ℤ ℒ'
  let u : Fin d → E := fun i => ((e (Fin.castLE hd i) : ℒ) : E)
  let x : Fin (m - d) → E := fun j => ((e (tailEmb (n := m) hd j) : ℒ) : E)
  let w : Fin (m - d) → E := fun j => Sᗮ.starProjection (((e (tailEmb (n := m) hd j) : ℒ)) : E)
  let DL : ℝ := (Matrix.gram ℝ (fun k : Fin m => ((e k : ℒ) : E))).det
  let Du : ℝ := (Matrix.gram ℝ u).det
  let Dw : ℝ := (Matrix.gram ℝ w).det
  have hS' : S = Submodule.span ℝ (Set.range u) := by
    dsimp [u]
    exact head_span_eq (ℒ' := ℒ') (ℒ := ℒ) S hS hd e he
  have hxw : ∀ j : Fin (m - d), x j - w j ∈ S := by
    intro j
    have hwj : w j = x j - S.starProjection (x j) := by
      dsimp [w, x]
      exact proj_orth_comp S ((e (tailEmb (n := m) hd j) : ℒ) : E)
    rw [hwj]
    have hxy : x j - (x j - S.starProjection (x j)) = S.starProjection (x j) := by abel
    rw [hxy]
    exact Submodule.starProjection_apply_mem S (x j)
  have hw : ∀ j : Fin (m - d), w j ∈ Sᗮ := by
    intro j
    exact Submodule.starProjection_apply_mem Sᗮ ((e (tailEmb (n := m) hd j) : ℒ) : E)
  have hshear := Commons.Analysis.InnerProductSpace.gram_det_shear_orthogonal (N := nA)
    (d := d) (r := m - d) u x w S hS' hxw hw
  have hmain : DL = Du * Dw := by
    dsimp [DL, Du, Dw]
    rw [gram_det_head_tail (ℒ := ℒ) e hd]
    exact hshear
  -- square roots
  have hDu0 : 0 ≤ Du := by
    dsimp [Du]
    exact (Matrix.posSemidef_gram ℝ u).det_nonneg
  have hDw0 : 0 ≤ Dw := by
    dsimp [Dw]
    exact (Matrix.posSemidef_gram ℝ w).det_nonneg
  have hsqrt : √(Du * Dw) = √Du * √Dw := by
    rw [Real.sqrt_mul hDu0]
  -- bridge ℒ
  have hgL : (Matrix.gram ℝ (fun i : Fin (Module.finrank ℤ ℒ) => ((e i : ℒ) : E))).det = DL := by
    dsimp [DL]
  have hL0 := Submission.DetQuot.determinant_eq_sqrt_gram (ℒ := ℒ) e
  have hL0g : ReverseMinkowski.determinant ℒ = √(Matrix.gram ℝ
      (fun i : Fin (Module.finrank ℤ ℒ) => ((e i : ℒ) : E))).det := by
    simpa [Matrix.gram] using hL0
  have hL : ReverseMinkowski.determinant ℒ = √DL := by
    rw [hgL] at hL0g
    exact hL0g
  -- bridge ℒ'
  have hL'0 := Submission.DetQuot.determinant_eq_sqrt_gram (ℒ := ℒ') (Module.finBasis ℤ ℒ')
  have hL'0g : ReverseMinkowski.determinant ℒ' = √(Matrix.gram ℝ
      (fun i : Fin (Module.finrank ℤ ℒ') => ((Module.finBasis ℤ ℒ' i : ℒ') : E))).det := by
    simpa [Matrix.gram] using hL'0
  have hgU : (Matrix.gram ℝ (fun i : Fin (Module.finrank ℤ ℒ') => ((Module.finBasis ℤ ℒ' i : ℒ') : E))).det = Du := by
    dsimp [Du, u]
    congr 1
    ext i j
    simp [he i, he j]
  have hL' : ReverseMinkowski.determinant ℒ' = √Du := by
    rw [hgU] at hL'0g
    exact hL'0g
  -- bridge Q
  have hfinQ : Module.finrank ℤ (quotLattice ℒ S) = m - d := by
    dsimp [m, d]
    simpa using (Module.finrank_eq_card_basis β)
  let equivQ : Fin (m - d) ≃ Fin (Module.finrank ℤ (quotLattice ℒ S)) :=
    (finCongr hfinQ).symm
  let β'' : Module.Basis (Fin (Module.finrank ℤ (quotLattice ℒ S))) ℤ (quotLattice ℒ S) :=
    β.reindex equivQ
  have hgQ : (Matrix.gram ℝ (fun i : Fin (Module.finrank ℤ (quotLattice ℒ S)) => ((β'' i : quotLattice ℒ S) : E))).det = Dw := by
    dsimp [Dw]
    let vq : Fin (m - d) → E := fun j => ((β j : quotLattice ℒ S) : E)
    have hfam : (fun i : Fin (Module.finrank ℤ (quotLattice ℒ S)) => ((β'' i : quotLattice ℒ S) : E)) = vq ∘ equivQ.symm := by
      funext i
      dsimp [β'', equivQ, vq]
      simp [Module.Basis.reindex_apply]
    have hvq : vq = w := by
      dsimp [vq, w]
      funext j
      exact hβval j
    calc
      (Matrix.gram ℝ (fun i : Fin (Module.finrank ℤ (quotLattice ℒ S)) => ((β'' i : quotLattice ℒ S) : E))).det
          = (Matrix.gram ℝ (vq ∘ equivQ.symm)).det := by rw [hfam]
      _ = (Matrix.gram ℝ vq).det := by
          have hg : Matrix.gram ℝ (vq ∘ equivQ.symm) = (Matrix.gram ℝ vq).submatrix equivQ.symm equivQ.symm := by
            ext a b
            simp [Matrix.gram]
          rw [hg]
          simp
      _ = (Matrix.gram ℝ w).det := by rw [hvq]
  have hQ0 := Submission.DetQuot.determinant_eq_sqrt_gram (ℒ := quotLattice ℒ S) β''
  have hQ0g : ReverseMinkowski.determinant (quotLattice ℒ S) = √(Matrix.gram ℝ
      (fun i : Fin (Module.finrank ℤ (quotLattice ℒ S)) => ((β'' i : quotLattice ℒ S) : E))).det := by
    simpa [Matrix.gram] using hQ0
  have hQ : ReverseMinkowski.determinant (quotLattice ℒ S) = √Dw := by
    rw [hgQ] at hQ0g
    exact hQ0g
  -- determinant product
  have hprod : ReverseMinkowski.determinant ℒ =
      ReverseMinkowski.determinant ℒ' * ReverseMinkowski.determinant (quotLattice ℒ S) := by
    calc
      ReverseMinkowski.determinant ℒ = √DL := hL
      _ = √(Du * Dw) := by rw [hmain]
      _ = √Du * √Dw := hsqrt
      _ = ReverseMinkowski.determinant ℒ' * ReverseMinkowski.determinant (quotLattice ℒ S) := by
          rw [← hL', ← hQ]
  -- divide
  have hL'pos : 0 < ReverseMinkowski.determinant ℒ' := by
    rw [hL']
    have hDu_pos : 0 < Du := by
      dsimp [Du]
      have hli : LinearIndependent ℝ u := by
        dsimp [u]
        have hli0 := basis_values_linIndep (ℒ := ℒ) e
        exact hli0.comp (Fin.castLE hd) (by
          intro a b hab
          apply Fin.ext
          simpa using congrArg Fin.val hab)
      have hdetnz : (Matrix.gram ℝ u).det ≠ 0 := by
        exact (Matrix.det_gram_ne_zero_iff_linearIndependent (𝕜 := ℝ)).2 hli
      have hge : 0 ≤ (Matrix.gram ℝ u).det := (Matrix.posSemidef_gram ℝ u).det_nonneg
      exact lt_of_le_of_ne hge (Ne.symm hdetnz)
    exact Real.sqrt_pos.2 hDu_pos
  have hL'neq : ReverseMinkowski.determinant ℒ' ≠ 0 := ne_of_gt hL'pos
  have hprod' : ReverseMinkowski.determinant ℒ = ReverseMinkowski.determinant ℒ' * √Dw := by
    rw [hQ] at hprod
    exact hprod
  calc
    ReverseMinkowski.determinant (quotLattice ℒ S) = √Dw := hQ
    _ = (ReverseMinkowski.determinant ℒ' * √Dw) / ReverseMinkowski.determinant ℒ' := by
        field_simp [hL'neq]
    _ = ReverseMinkowski.determinant ℒ / ReverseMinkowski.determinant ℒ' := by
        rw [← hprod']

end
end Submission.SubLattice
