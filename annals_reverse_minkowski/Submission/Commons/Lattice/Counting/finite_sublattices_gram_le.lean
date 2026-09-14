import Mathlib
import Submission.Commons.Lattice.Discrete.discreteTopology_of_le
import Submission.Commons.Lattice.Determinant.gram_det_independent
import Submission.Commons.LinearAlgebra.Independence.discrete_basis_values_linIndep
import Submission.Commons.LinearAlgebra.Matrix.det_mono_posSemidef_sub
import Submission.Commons.LinearAlgebra.Matrix.posDef_lower_bound_quadratic
import Submission.Commons.LinearAlgebra.GramMatrix.gram_of_linComb
import Submission.Commons.GroupTheory.Hopfian.finite_addSubgroups_of_index_le
import Submission.Commons.LinearAlgebra.Matrix.det_posDef_mulVec_lower
import Submission.Commons.LinearAlgebra.Module.comap_linearEquiv_of_subset_range
import Submission.Commons.Lattice.Counting.finite_sublattices_int

set_option autoImplicit false
set_option linter.style.haveILetI false

noncomputable section
open Module
open scoped BigOperators

/-!FinitelymanysublatticeswithboundedGramdeterminant.Thisfileproves
the finiteness statement `finite_sublattices_gram_le` used in the
reverse-Minkowski development.  Everything below is local to this file and
imports only Mathlib and previously-proven commons lemmas; the actual
counting core `Commons.Lattice.Counting.finite_sublattices_int` (a fleet
lemma over the coordinate lattice `(Fin n → ℤ)`) provides the pure
integer-lattice finiteness. -/
namespace Commons.Lattice.Counting

abbrev Eu (n : ℕ) := EuclideanSpace ℝ (Fin n)

/-- basis of the full-rank lattice indexed by `Fin n`. -/
def basisLattice {n : ℕ} (L : Submodule ℤ (Eu n)) [DiscreteTopology L] [IsZLattice ℝ L] :
    Module.Basis (Fin n) ℤ L := by
  classical
  have hfin : Module.finrank ℤ L = n := by
    calc Module.finrank ℤ L = Module.finrank ℝ (Eu n) := ZLattice.rank ℝ L
         _ = n := by simpa using Module.finrank_eq_card_basis (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
  exact (Module.finBasis ℤ L).reindex (finCongr hfin)

lemma basisLattice_linIndep {n : ℕ} (L : Submodule ℤ (Eu n)) [DiscreteTopology L] [IsZLattice ℝ L] :
    LinearIndependent ℝ (fun i : Fin n => ((basisLattice L i : L) : Eu n)) := by
  classical
  exact Commons.LinearAlgebra.Independence.discrete_basis_values_linIndep (ℒ := L) (b := basisLattice L)

lemma basisLattice_gram_posDef {n : ℕ} (L : Submodule ℤ (Eu n)) [DiscreteTopology L] [IsZLattice ℝ L] :
    (Matrix.gram ℝ (fun i : Fin n => ((basisLattice L i : L) : Eu n))).PosDef := by
  rw [Matrix.posDef_gram_iff_linearIndependent]
  exact basisLattice_linIndep L

/-- Gram matrix of the fixed ℤ-basis of `L`. -/
abbrev gramBasis {n : ℕ} (L : Submodule ℤ (Eu n)) [DiscreteTopology L] [IsZLattice ℝ L] :
    Matrix (Fin n) (Fin n) ℝ :=
  Matrix.gram ℝ (fun i : Fin n => ((basisLattice L i : L) : Eu n))

def coordEquiv {n : ℕ} (L : Submodule ℤ (Eu n)) [DiscreteTopology L] [IsZLattice ℝ L] :
    L ≃ₗ[ℤ] (Fin n → ℤ) :=
  (basisLattice L).equivFun

/-- ℤ-linear evaluation of coordinate functions against the lattice basis (as elements of E). -/
def evalZ {n : ℕ} (L : Submodule ℤ (Eu n)) [DiscreteTopology L] [IsZLattice ℝ L] :
    (Fin n → ℤ) →ₗ[ℤ] Eu n :=
  (Submodule.subtype L).comp (coordEquiv L).symm.toLinearMap

lemma evalZ_injective {n : ℕ} (L : Submodule ℤ (Eu n)) [DiscreteTopology L] [IsZLattice ℝ L] :
    Function.Injective (evalZ L) := by
  intro x y hxy
  have h : (coordEquiv L).symm x = (coordEquiv L).symm y :=
    (Submodule.injective_subtype L) hxy
  exact (coordEquiv L).symm.injective h

lemma range_evalZ {n : ℕ} (L : Submodule ℤ (Eu n)) [DiscreteTopology L] [IsZLattice ℝ L] :
    LinearMap.range (evalZ L) = L := by
  ext y
  constructor
  · intro hy
    rcases (LinearMap.mem_range.mp hy) with ⟨x, hx⟩
    rw [← hx]
    exact Submodule.coe_mem (x := (coordEquiv L).symm x)
  · intro hy
    rw [LinearMap.mem_range]
    refine ⟨(coordEquiv L) ⟨y, hy⟩, ?_⟩
    simp [evalZ]

/-- coordinate map of a submodule `M ≤ L`: preimage under `evalZ`. -/
def coordSub {n : ℕ} (L : Submodule ℤ (Eu n)) [DiscreteTopology L] [IsZLattice ℝ L]
    (M : Submodule ℤ (Eu n)) : Submodule ℤ (Fin n → ℤ) :=
  M.comap (evalZ L)

/-- the image of `coordSub` under `evalZ` recovers `M` (for `M ≤ L`). -/
lemma map_coordSub {n : ℕ} (L : Submodule ℤ (Eu n)) [DiscreteTopology L] [IsZLattice ℝ L]
    (M : Submodule ℤ (Eu n)) (hM : M ≤ L) :
    Submodule.map (evalZ L) (coordSub L M) = M := by
  unfold coordSub
  rw [Submodule.map_comap_eq, range_evalZ]
  exact le_antisymm (by intro y hy; exact hy.2) (by intro y hy; exact ⟨hM hy, hy⟩)

/-- injectivity of `M ↦ coordSub L M` on submodules `≤ L`. -/
lemma coordSub_inj {n : ℕ} (L : Submodule ℤ (Eu n)) [DiscreteTopology L] [IsZLattice ℝ L]
    {M N : Submodule ℤ (Eu n)} (hM : M ≤ L) (hN : N ≤ L) :
    coordSub L M = coordSub L N → M = N := by
  intro h
  calc
    M = Submodule.map (evalZ L) (coordSub L M) := (map_coordSub L M hM).symm
    _ = Submodule.map (evalZ L) (coordSub L N) := by rw [h]
    _ = N := map_coordSub L N hN

/-- rank preservation: `finrank (coordSub L M) = finrank M` for `M ≤ L`. -/
lemma finrank_coordSub {n : ℕ} (L : Submodule ℤ (Eu n)) [DiscreteTopology L] [IsZLattice ℝ L]
    (M : Submodule ℤ (Eu n)) (hM : M ≤ L) :
    Module.finrank ℤ (coordSub L M) = Module.finrank ℤ M := by
  classical
  rcases Commons.LinearAlgebra.Module.comap_linearEquiv_of_subset_range
      (A := (Fin n → ℤ)) (B := Eu n) (f := evalZ L) (evalZ_injective L) M
      (by simpa [range_evalZ L] using hM) with ⟨e⟩
  exact LinearEquiv.finrank_eq e

end Commons.Lattice.Counting

namespace Commons.Lattice.Counting

/-- real-linear evaluation (definitionally convenient for Gram computations). -/
def evalReal {n : ℕ} (L : Submodule ℤ (Eu n)) [DiscreteTopology L] [IsZLattice ℝ L]
    (x : Fin n → ℤ) : Eu n :=
  ∑ i : Fin n, ((x i : ℤ) : ℝ) • ((basisLattice L i : L) : Eu n)

lemma evalZ_eq_evalReal {n : ℕ} (L : Submodule ℤ (Eu n)) [DiscreteTopology L] [IsZLattice ℝ L]
    (x : Fin n → ℤ) : evalZ L x = evalReal L x := by
  classical
  have h : (coordEquiv L).symm x = ∑ i : Fin n, (x i : ℤ) • (basisLattice L i) := by
    exact Module.Basis.equivFun_symm_apply (basisLattice L) x
  calc
    evalZ L x = (Submodule.subtype L) ((coordEquiv L).symm x) := rfl
    _ = (Submodule.subtype L) (∑ i : Fin n, (x i : ℤ) • (basisLattice L i)) := by rw [h]
    _ = ∑ i : Fin n, (Submodule.subtype L) ((x i : ℤ) • (basisLattice L i)) := by rw [map_sum]
    _ = ∑ i : Fin n, ((x i : ℤ) : ℝ) • ((Submodule.subtype L) (basisLattice L i)) := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [map_smul]
          simpa using (Int.cast_smul_eq_zsmul ℝ (x i) (((basisLattice L i : L) : Eu n))).symm
    _ = evalReal L x := rfl

/-- the `L`-element with E-value `v`, for `v ∈ L`. -/
def inL {n : ℕ} (L : Submodule ℤ (Eu n)) [DiscreteTopology L] [IsZLattice ℝ L]
    (v : Eu n) (hv : v ∈ L) : L := ⟨v, hv⟩

/-- coordinates of a vector `w ∈ L` in the fixed basis. -/
def coordsOf {n : ℕ} (L : Submodule ℤ (Eu n)) [DiscreteTopology L] [IsZLattice ℝ L]
    (v : Eu n) (hv : v ∈ L) : Fin n → ℤ := coordEquiv L (inL L v hv)

lemma evalZ_coordsOf {n : ℕ} (L : Submodule ℤ (Eu n)) [DiscreteTopology L] [IsZLattice ℝ L]
    (v : Eu n) (hv : v ∈ L) : evalZ L (coordsOf L v hv) = v := by
  dsimp [coordsOf, inL]
  simp [evalZ]

/-- Gram matrix of vectors of `L` expressed via the basis Gram matrix. -/
lemma gram_of_Lvectors {n r : ℕ} (L : Submodule ℤ (Eu n)) [DiscreteTopology L] [IsZLattice ℝ L]
    (w : Fin r → Eu n) (hw : ∀ j : Fin r, w j ∈ L) :
    Matrix.gram ℝ w =
      (Matrix.of (fun i : Fin n => fun j : Fin r => (((coordsOf L (w j) (hw j)) i : ℤ) : ℝ))).transpose *
        gramBasis L *
        Matrix.of (fun i : Fin n => fun j : Fin r => (((coordsOf L (w j) (hw j)) i : ℤ) : ℝ)) := by
  classical
  let C : Matrix (Fin n) (Fin r) ℝ :=
    Matrix.of (fun i : Fin n => fun j : Fin r => (((coordsOf L (w j) (hw j)) i : ℤ) : ℝ))
  have hvec : ∀ j : Fin r, w j = ∑ i : Fin n, C i j • ((basisLattice L i : L) : Eu n) := by
    intro j
    have h1 : evalZ L (coordsOf L (w j) (hw j)) = w j := evalZ_coordsOf L (w j) (hw j)
    rw [← h1]
    rw [evalZ_eq_evalReal]
    rfl
  calc
    Matrix.gram ℝ w = Matrix.gram ℝ (fun j : Fin r => ∑ i : Fin n, C i j • ((basisLattice L i : L) : Eu n)) := by
          congr 1
          funext j
          rw [hvec j]
    _ = C.transpose * Matrix.gram ℝ (fun i : Fin n => ((basisLattice L i : L) : Eu n)) * C := by
          exact Commons.LinearAlgebra.GramMatrix.gram_of_linComb
            (b := fun i : Fin n => ((basisLattice L i : L) : Eu n)) (C := C)
    _ = C.transpose * gramBasis L * C := rfl

end Commons.Lattice.Counting

namespace Commons.Lattice.Counting

/-- coordinates of `w j` belong to the coordinate submodule of `M`. -/
lemma coord_mem_coordSub {n r : ℕ} (L : Submodule ℤ (Eu n)) [DiscreteTopology L] [IsZLattice ℝ L]
    {M : Submodule ℤ (Eu n)} (hMle : M ≤ L) {w : Fin r → Eu n} (hw : ∀ j : Fin r, w j ∈ M) :
    ∀ j : Fin r, coordsOf L (w j) (hMle (hw j)) ∈ coordSub L M := by
  intro j
  rw [coordSub, Submodule.mem_comap]
  have h : evalZ L (coordsOf L (w j) (hMle (hw j))) = w j := evalZ_coordsOf L (w j) (hMle (hw j))
  simpa [h] using hw j

/-- if `M = span(w)`, the coordinate submodule is spanned by the coordinates of `w`. -/
lemma span_coordSub {n r : ℕ} (L : Submodule ℤ (Eu n)) [DiscreteTopology L] [IsZLattice ℝ L]
    {M : Submodule ℤ (Eu n)} (hMle : M ≤ L) {w : Fin r → Eu n} (hw : ∀ j : Fin r, w j ∈ M)
    (hspan : M ≤ Submodule.span ℤ (Set.range w)) :
    coordSub L M ≤
      Submodule.span ℤ (Set.range (fun j : Fin r => coordsOf L (w j) (hMle (hw j)))) := by
  classical
  intro x hx
  -- x ∈ coordSub L M  ⇒ evalZ x ∈ M = span(range w)
  have hxev : evalZ L x ∈ M := (Submodule.mem_comap.mp hx)
  have hxspan : evalZ L x ∈ Submodule.span ℤ (Set.range w) := hspan hxev
  rcases (Submodule.mem_span_range_iff_exists_fun (R := ℤ) (v := w) (x := evalZ L x)).mp hxspan with ⟨c, hc⟩
  -- evalZ x = ∑ c j • w j = evalZ (∑ c j • coordsOf (w j))
  have hsum : evalZ L (∑ j : Fin r, (c j : ℤ) • coordsOf L (w j) (hMle (hw j))) = evalZ L x := by
    calc
      evalZ L (∑ j : Fin r, (c j : ℤ) • coordsOf L (w j) (hMle (hw j)))
          = ∑ j : Fin r, (c j : ℤ) • evalZ L (coordsOf L (w j) (hMle (hw j))) := by
              rw [map_sum]
              simp_rw [map_smul]
      _ = ∑ j : Fin r, (c j : ℤ) • w j := by
              apply Finset.sum_congr rfl
              intro j hj
              rw [evalZ_coordsOf]
      _ = evalZ L x := hc
  have hxeq : (∑ j : Fin r, (c j : ℤ) • coordsOf L (w j) (hMle (hw j))) = x := (evalZ_injective L) hsum
  exact (Submodule.mem_span_range_iff_exists_fun (R := ℤ)
    (v := fun j : Fin r => coordsOf L (w j) (hMle (hw j))) (x := x)).2 ⟨c, hxeq⟩

end Commons.Lattice.Counting

namespace Commons.Lattice.Counting

open Matrix

/-- determinant transfer: bound the integer Gram determinant from the ambient Gram bound. -/
lemma intGram_det_le_of_gram_le {n r : ℕ} (L : Submodule ℤ (Eu n)) [DiscreteTopology L] [IsZLattice ℝ L]
    {M : Submodule ℤ (Eu n)} (hMle : M ≤ L) {w : Fin r → Eu n} (hw : ∀ j : Fin r, w j ∈ M)
    {X c : ℝ} (hX : 0 ≤ X) (hcpos : 0 < c)
    (hc : ∀ {r' : ℕ} (A : Matrix (Fin n) (Fin r') ℝ),
      c ^ r' * (A.transpose * A).det ≤ (A.transpose * gramBasis L * A).det)
    (hgram : (Matrix.gram ℝ w).det ≤ X) :
    let A : Matrix (Fin n) (Fin r) ℤ := Matrix.of (fun i : Fin n => fun j : Fin r => coordsOf L (w j) (hMle (hw j)) i)
    ((A.map (fun z : ℤ => (z : ℝ))).transpose * (A.map (fun z : ℤ => (z : ℝ)))).det ≤ X / c ^ r := by
  classical
  let A : Matrix (Fin n) (Fin r) ℤ := Matrix.of (fun i : Fin n => fun j : Fin r => coordsOf L (w j) (hMle (hw j)) i)
  let Ar : Matrix (Fin n) (Fin r) ℝ := A.map (fun z : ℤ => (z : ℝ))
  have hA : Matrix.of (fun i : Fin n => fun j : Fin r => (((coordsOf L (w j) (hMle (hw j))) i : ℤ) : ℝ)) = Ar := rfl
  have hgm : (Matrix.gram ℝ w).det = (Ar.transpose * gramBasis L * Ar).det := by
    rw [gram_of_Lvectors L w (fun j => hMle (hw j))]
    congr 1
  have hbound : c ^ r * (Ar.transpose * Ar).det ≤ X := by
    calc
      c ^ r * (Ar.transpose * Ar).det ≤ (Ar.transpose * gramBasis L * Ar).det := hc Ar
      _ = (Matrix.gram ℝ w).det := hgm.symm
      _ ≤ X := hgram
  have hpos : 0 < c ^ r := pow_pos hcpos r
  have hmain : (Ar.transpose * Ar).det ≤ X / c ^ r := by
    rw [mul_comm] at hbound
    exact (le_div_iff₀ hpos).mpr hbound
  simpa [A, Ar] using hmain

end Commons.Lattice.Counting

namespace Commons.Lattice.Counting

open Matrix

/-- membership of the coordinate submodule in the target set. -/
lemma coordSub_mem_targetSet {n r : ℕ} (L : Submodule ℤ (Eu n)) [DiscreteTopology L] [IsZLattice ℝ L]
    (c : ℝ) (hcpos : 0 < c)
    (hc : ∀ {r' : ℕ} (A : Matrix (Fin n) (Fin r') ℝ),
      c ^ r' * (A.transpose * A).det ≤ (A.transpose * gramBasis L * A).det)
    {X : ℝ} (hX : 0 ≤ X) {M : Submodule ℤ (Eu n)} (hMle : M ≤ L)
    (hr : Module.finrank ℤ M = r) {w : Fin r → Eu n}
    (hw : ∀ j : Fin r, w j ∈ M)
    (hspan : ∀ ⦃x⦄, x ∈ M → x ∈ Submodule.span ℤ (Set.range w))
    (hgram : (Matrix.gram ℝ w).det ≤ X) :
    coordSub L M ∈ {N : Submodule ℤ (Fin n → ℤ) | Module.finrank ℤ N = r ∧
      (∃ A : Matrix (Fin n) (Fin r) ℤ,
        (∀ j : Fin r, (fun i => A i j) ∈ N) ∧
        (∀ ⦃x⦄, x ∈ N → x ∈ Submodule.span ℤ (Set.range (fun j : Fin r => (fun i => A i j)))) ∧
        (((A.map (fun z : ℤ => (z : ℝ))).transpose *
            (A.map (fun z : ℤ => (z : ℝ)))).det ≤ X / c ^ r))} := by
  classical
  let N : Submodule ℤ (Fin n → ℤ) := coordSub L M
  have hrN : Module.finrank ℤ N = r := by
    dsimp [N]
    calc Module.finrank ℤ (coordSub L M) = Module.finrank ℤ M := finrank_coordSub L M hMle
         _ = r := hr
  have h1 : ∀ j : Fin r, coordsOf L (w j) (hMle (hw j)) ∈ N := by
    intro j
    dsimp [N]
    exact coord_mem_coordSub L hMle hw j
  have h2 : ∀ ⦃x⦄, x ∈ N →
      x ∈ Submodule.span ℤ (Set.range (fun j : Fin r => coordsOf L (w j) (hMle (hw j)))) := by
    intro x hx
    dsimp [N] at hx
    exact span_coordSub L hMle hw hspan hx
  refine ⟨hrN, ?_⟩
  refine ⟨Matrix.of (fun i : Fin n => fun j : Fin r => coordsOf L (w j) (hMle (hw j)) i), ?_, ?_, ?_⟩
  · intro j
    simpa using (h1 j)
  · intro x hx
    simpa using (h2 hx)
  · simpa using (intGram_det_le_of_gram_le L hMle hw hX hcpos hc hgram)

/-- Main theorem. -/
theorem finite_sublattices_gram_le
    {n r : ℕ} (L : Submodule ℤ (EuclideanSpace ℝ (Fin n)))
    [DiscreteTopology L] [IsZLattice ℝ L] (X : ℝ) :
    {M : Submodule ℤ (EuclideanSpace ℝ (Fin n)) | M ≤ L ∧
      Module.finrank ℤ M = r ∧
      (∃ w : Fin r → EuclideanSpace ℝ (Fin n),
        (∀ i : Fin r, w i ∈ M) ∧
        (∀ ⦃x⦄, x ∈ M → x ∈ Submodule.span ℤ (Set.range w)) ∧
        (Matrix.gram ℝ w).det ≤ X)}.Finite := by
  classical
  let E := EuclideanSpace ℝ (Fin n)
  let s : Set (Submodule ℤ E) := {M | M ≤ L ∧ Module.finrank ℤ M = r ∧
      (∃ w : Fin r → E,
        (∀ i : Fin r, w i ∈ M) ∧
        (∀ ⦃x⦄, x ∈ M → x ∈ Submodule.span ℤ (Set.range w)) ∧
        (Matrix.gram ℝ w).det ≤ X)}
  by_cases hXneg : X < 0
  · -- empty: Gram determinants are nonnegative
    have hnonneg : ∀ (w : Fin r → E), 0 ≤ (Matrix.gram ℝ w).det := by
      intro w
      exact (Matrix.posSemidef_gram (𝕜 := ℝ) (E := E) w).det_nonneg
    have hsub : s ⊆ (∅ : Set (Submodule ℤ E)) := by
      intro M hM
      rcases hM with ⟨hMle, hr, hw⟩
      rcases hw with ⟨w, hwmem, hwspan, hgram⟩
      have h : (Matrix.gram ℝ w).det ≤ X := hgram
      have hlt : X < 0 := hXneg
      exact False.elim ((not_le_of_gt hlt) (le_trans (hnonneg w) hgram))
    exact (Set.finite_empty.subset hsub)
  · have hX : 0 ≤ X := le_of_not_gt hXneg
    rcases (Commons.LinearAlgebra.Matrix.det_posDef_mulVec_lower (G := gramBasis L)
        (basisLattice_gram_posDef L)) with ⟨c, hcpos, hc⟩
    let target : Set (Submodule ℤ (Fin n → ℤ)) := {N | Module.finrank ℤ N = r ∧
      (∃ A : Matrix (Fin n) (Fin r) ℤ,
        (∀ j : Fin r, (fun i => A i j) ∈ N) ∧
        (∀ ⦃x⦄, x ∈ N → x ∈ Submodule.span ℤ (Set.range (fun j : Fin r => (fun i => A i j)))) ∧
        (((A.map (fun z : ℤ => (z : ℝ))).transpose *
            (A.map (fun z : ℤ => (z : ℝ)))).det ≤ X / c ^ r))}
    have htargetFin : target.Finite := by
      dsimp [target]
      exact finite_sublattices_int (n := n) (r := r) (B := X / c ^ r)
    -- s ⊆ {M | M ≤ L ∧ coordSub L M ∈ target}
    let big : Set (Submodule ℤ E) := {M | M ≤ L ∧ coordSub L M ∈ target}
    have hsSub : s ⊆ big := by
      intro M hM
      rcases hM with ⟨hMle, hr, hw⟩
      rcases hw with ⟨w, hwmem, hwspan, hgram⟩
      exact ⟨hMle, coordSub_mem_targetSet L c hcpos hc hX hMle hr hwmem hwspan hgram⟩
    -- big is finite
    have hbigFin : big.Finite := by
      let SBig := {M : Submodule ℤ E // M ≤ L ∧ coordSub L M ∈ target}
      let F : SBig → {N : Submodule ℤ (Fin n → ℤ) // N ∈ target} :=
        fun M => ⟨coordSub L M.1, M.2.2⟩
      have hFinF : Function.Injective F := by
        intro A B h
        apply Subtype.ext
        exact coordSub_inj L A.2.1 B.2.1 (by simpa [F] using congrArg (fun q => q.1) h)
      haveI : Finite {N : Submodule ℤ (Fin n → ℤ) // N ∈ target} := htargetFin.to_subtype
      haveI : Finite SBig := Finite.of_injective F hFinF
      dsimp [big]
      exact Set.finite_coe_iff.mpr (inferInstance : Finite {M : Submodule ℤ E // M ≤ L ∧ coordSub L M ∈ target})
    exact hbigFin.subset hsSub

end Commons.Lattice.Counting
