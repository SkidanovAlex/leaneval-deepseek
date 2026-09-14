import Mathlib
import ChallengeDeps
import Submission.QuotientLattice
import Submission.SubLattice
import Submission.Commons.Lattice.Discrete.discreteTopology_of_le
import Submission.Commons.Lattice.Discrete.discreteTopology_quotLattice
import Submission.Commons.Lattice.Finrank.finrank_sup_add_finrank_inf_eq_of_discrete
import Submission.Commons.LinearAlgebra.Matrix.det_mono_posSemidef_sub
import Submission.Commons.Analysis.InnerProductSpace.gram_sub_gram_of_contraction
import Submission.Commons.LinearAlgebra.Independence.linearIndependent_of_ambient
import Submission.Commons.LinearAlgebra.Matrix.det_mono_posSemidef_sub
import Submission.Commons.Analysis.InnerProductSpace.gram_sub_gram_of_contraction

open Module MeasureTheory Metric
open Submission.QuotientLattice
open scoped Real BigOperators InnerProductSpace RealInnerProductSpace
set_option autoImplicit false
set_option linter.style.haveILetI false

/-!
# Stuhler uncrossing (paper Lemma 2.4) and rank-modularity of sublattices

Everything here is for lattices `L₁, L₂ ≤ L ≤ E` (ambient `E = EuclideanSpace ℝ (Fin nA)`,
`L` discrete — any rank).  For two primitive sublattices of `L`:

    rank(L₁) + rank(L₂) = rank(L₁∩L₂) + rank(L₁+L₂)
    det(L₁+L₂) · det(L₁∩L₂) ≤ det(L₁) · det(L₂)

The determinant inequality follows the paper: reduce to the case `M₁ ∩ M₂ = {0}` and use
`det(M₁+M₂) = det(M₁) · det(π_{span M₁}⊥ M₂) ≤ det(M₁) · det(M₂)` where the projection is
a contraction (Gram-monotonicity of the determinant under contractions).
-/

namespace Submission.Uncrossing

variable {nA : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin nA)

noncomputable section

/-- The Gram determinant of the canonical basis values is positive (equivalently det > 0). -/
lemma det_gram_finBasis_pos {L : Submodule ℤ E} [DiscreteTopology L] :
    0 < (Matrix.gram ℝ (fun i : Fin (Module.finrank ℤ L) => ((Module.finBasis ℤ L i : L) : E))).det := by
  classical
  haveI : Module.Free ℤ L := instModuleFree_of_discrete_submodule L
  haveI : Module.Finite ℤ L := instModuleFinite_of_discrete_submodule L
  let v : Fin (Module.finrank ℤ L) → E := fun i => ((Module.finBasis ℤ L i : L) : E)
  have hli : LinearIndependent ℝ v := by
    exact Commons.LinearAlgebra.Independence.discrete_basis_values_linIndep (ℒ := L) (Module.finBasis ℤ L)
  have hdetnz : (Matrix.gram ℝ v).det ≠ 0 := by
    exact (Matrix.det_gram_ne_zero_iff_linearIndependent (𝕜 := ℝ)).2 hli
  have hge : 0 ≤ (Matrix.gram ℝ v).det := (Matrix.posSemidef_gram ℝ v).det_nonneg
  exact lt_of_le_of_ne hge (Ne.symm hdetnz)

/-- Determinants of (discrete) lattices are strictly positive (incl. the zero lattice). -/
lemma det_pos {L : Submodule ℤ E} [DiscreteTopology L] : 0 < ReverseMinkowski.determinant L := by
  classical
  haveI : Module.Free ℤ L := instModuleFree_of_discrete_submodule L
  haveI : Module.Finite ℤ L := instModuleFinite_of_discrete_submodule L
  have h0 := Submission.DetQuot.determinant_eq_sqrt_gram (ℒ := L) (Module.finBasis ℤ L)
  rw [h0]
  have hb := det_gram_finBasis_pos (L := L)
  simpa [Matrix.gram] using (Real.sqrt_pos.2 hb)

/-- `realSpan` is monotone. -/
lemma realSpan_mono {L₁ L₂ : Submodule ℤ E} (hle : L₁ ≤ L₂) : realSpan L₁ ≤ realSpan L₂ := by
  rw [realSpan, realSpan]
  exact Submodule.span_mono hle

/-- Intersection of two sublattices of a common ambient is primitive in the first. -/
lemma inter_primitive_left {L₁ L₂ L : Submodule ℤ E} (hp₂ : Primitive L₂ L) (h₁ : L₁ ≤ L) :
    Primitive (L₁ ⊓ L₂) L₁ := by
  intro x
  constructor
  · intro hx
    exact ⟨hx.1, mem_realSpan (ℒ := L₁ ⊓ L₂) hx⟩
  · intro hx
    have hxS2 : x ∈ realSpan L₂ := realSpan_mono (L₁ := L₁ ⊓ L₂) (L₂ := L₂)
        (by intro y hy; exact hy.2) hx.2
    exact ⟨hx.1, (hp₂ x).mpr ⟨h₁ hx.1, hxS2⟩⟩

/-- Intersection of two sublattices of a common ambient is primitive in the second. -/
lemma inter_primitive_right {L₁ L₂ L : Submodule ℤ E} (hp₁ : Primitive L₁ L) (h₂ : L₂ ≤ L) :
    Primitive (L₁ ⊓ L₂) L₂ := by
  intro x
  constructor
  · intro hx
    exact ⟨hx.2, mem_realSpan (ℒ := L₁ ⊓ L₂) hx⟩
  · intro hx
    have hxS1 : x ∈ realSpan L₁ := realSpan_mono (L₁ := L₁ ⊓ L₂) (L₂ := L₁)
        (by intro y hy; exact hy.1) hx.2
    exact ⟨(hp₁ x).mpr ⟨h₂ hx.1, hxS1⟩, hx.1⟩

/-- The intersection of two primitive sublattices is primitive in their sum. -/
lemma primitive_inter_sup {L₁ L₂ L : Submodule ℤ E} (hp₁ : Primitive L₁ L) (hp₂ : Primitive L₂ L) :
    Primitive (L₁ ⊓ L₂) (L₁ ⊔ L₂) := by
  intro x
  constructor
  · intro hx
    exact ⟨(le_sup_left : L₁ ≤ L₁ ⊔ L₂) hx.1, mem_realSpan (ℒ := L₁ ⊓ L₂) hx⟩
  · intro hx
    rcases (Submodule.mem_sup.mp hx.1) with ⟨m₁, hm₁, m₂, hm₂, hxeq⟩
    have hspan₂ : realSpan (L₁ ⊓ L₂) ≤ realSpan L₂ := realSpan_mono (L₁ := L₁ ⊓ L₂) (L₂ := L₂)
      (by intro y hy; exact hy.2)
    have hspan₁ : realSpan (L₁ ⊓ L₂) ≤ realSpan L₁ := realSpan_mono (L₁ := L₁ ⊓ L₂) (L₂ := L₁)
      (by intro y hy; exact hy.1)
    have hm₁V₂ : m₁ ∈ realSpan L₂ := by
      have hxV₂ : x ∈ realSpan L₂ := hspan₂ hx.2
      have hm₂S₂ : m₂ ∈ realSpan L₂ := mem_realSpan (ℒ := L₂) hm₂
      have hsub : x - m₂ ∈ realSpan L₂ := Submodule.sub_mem (realSpan L₂) hxV₂ hm₂S₂
      have hxmeq : x - m₂ = m₁ := by rw [← hxeq]; abel
      simpa [hxmeq] using hsub
    have hm₁L₂ : m₁ ∈ L₂ := (hp₂ m₁).mpr ⟨(Primitive.le hp₁) hm₁, hm₁V₂⟩
    have hm₂V₁ : m₂ ∈ realSpan L₁ := by
      have hxV₁ : x ∈ realSpan L₁ := hspan₁ hx.2
      have hm₁S₁ : m₁ ∈ realSpan L₁ := mem_realSpan (ℒ := L₁) hm₁
      have hsub : x - m₁ ∈ realSpan L₁ := Submodule.sub_mem (realSpan L₁) hxV₁ hm₁S₁
      have hxmeq : x - m₁ = m₂ := by rw [← hxeq]; abel
      simpa [hxmeq] using hsub
    have hm₂L₁ : m₂ ∈ L₁ := (hp₁ m₂).mpr ⟨(Primitive.le hp₂) hm₂, hm₂V₁⟩
    have hsum : m₁ + m₂ ∈ L₁ ⊓ L₂ := Submodule.add_mem (L₁ ⊓ L₂) ⟨hm₁, hm₁L₂⟩ ⟨hm₂L₁, hm₂⟩
    exact hxeq ▸ hsum


/-- **Rank-modularity (Lemma 2.4, rank part)**: for `L₁, L₂ ≤ L` (any ranks),
`rank(L₁+L₂) + rank(L₁∩L₂) = rank(L₁) + rank(L₂)`. -/
theorem uncrossing_rank {L L₁ L₂ : Submodule ℤ E} [DiscreteTopology L] (h₁ : L₁ ≤ L) (h₂ : L₂ ≤ L) :
    Module.finrank ℤ ↥(L₁ ⊔ L₂) + Module.finrank ℤ ↥(L₁ ⊓ L₂) =
      Module.finrank ℤ ↥L₁ + Module.finrank ℤ ↥L₂ := by
  exact Commons.Lattice.Finrank.finrank_sup_add_finrank_inf_eq_of_discrete (L₀ := L) (L₁ := L₁)
    (L₂ := L₂) h₁ h₂

/-- `realSpan` distributes over the sum of two sublattices. -/
lemma realSpan_sup {L₁ L₂ : Submodule ℤ E} :
    realSpan (L₁ ⊔ L₂) = realSpan L₁ ⊔ realSpan L₂ := by
  classical
  unfold realSpan
  apply le_antisymm
  · rw [Submodule.span_le]
    intro x hx
    rcases (Submodule.mem_sup.mp hx) with ⟨a, ha, b, hb, hab⟩
    have ha' : a ∈ Submodule.span ℝ (L₁ : Set E) := Submodule.subset_span ha
    have hb' : b ∈ Submodule.span ℝ (L₂ : Set E) := Submodule.subset_span hb
    have hlt : Submodule.span ℝ (L₁ : Set E) ≤
        Submodule.span ℝ (L₁ : Set E) ⊔ Submodule.span ℝ (L₂ : Set E) := le_sup_left
    have hrt : Submodule.span ℝ (L₂ : Set E) ≤
        Submodule.span ℝ (L₁ : Set E) ⊔ Submodule.span ℝ (L₂ : Set E) := le_sup_right
    rw [← hab]
    exact Submodule.add_mem (Submodule.span ℝ (L₁ : Set E) ⊔ Submodule.span ℝ (L₂ : Set E))
      (hlt ha') (hrt hb')
  · rw [sup_le_iff]
    constructor
    · rw [Submodule.span_le]
      intro x hx
      exact Submodule.subset_span ((le_sup_left : L₁ ≤ L₁ ⊔ L₂) hx)
    · rw [Submodule.span_le]
      intro x hx
      exact Submodule.subset_span ((le_sup_right : L₂ ≤ L₁ ⊔ L₂) hx)

/-- For `L₁, L₂` sublattices of a discrete ambient: `span(L₁) ∩ span(L₂) = span(L₁∩L₂)`. -/
lemma span_inter_eq_span_inf {L L₁ L₂ : Submodule ℤ E} [DiscreteTopology L]
    (h₁ : L₁ ≤ L) (h₂ : L₂ ≤ L) :
    realSpan L₁ ⊓ realSpan L₂ = realSpan (L₁ ⊓ L₂) := by
  classical
  haveI : DiscreteTopology L₁ := Commons.Lattice.Discrete.discreteTopology_of_le (n := nA) h₁
  haveI : DiscreteTopology L₂ := Commons.Lattice.Discrete.discreteTopology_of_le (n := nA) h₂
  haveI : DiscreteTopology ↥(L₁ ⊔ L₂) := Commons.Lattice.Discrete.discreteTopology_of_le (n := nA)
    (ℒ := L) (ℒ' := L₁ ⊔ L₂) (sup_le h₁ h₂)
  haveI : DiscreteTopology ↥(L₁ ⊓ L₂) := Commons.Lattice.Discrete.discreteTopology_of_le (n := nA)
    (ℒ := L₁) (ℒ' := L₁ ⊓ L₂) inf_le_left
  apply Eq.symm
  apply Submodule.eq_of_le_of_finrank_eq (K := ℝ) (V := E)
    (S₁ := realSpan (L₁ ⊓ L₂)) (S₂ := realSpan L₁ ⊓ realSpan L₂)
  · exact le_inf (realSpan_mono (L₁ := L₁ ⊓ L₂) (L₂ := L₁) inf_le_left)
      (realSpan_mono (L₁ := L₁ ⊓ L₂) (L₂ := L₂) inf_le_right)
  · -- finrank ℝ (span(I)) = finrank ℝ (span L₁ ∩ span L₂)
    have hf₁ : Module.finrank ℝ ↥(realSpan L₁) = Module.finrank ℤ ↥L₁ := by
      change Module.finrank ℝ ↥(Submodule.span ℝ (L₁ : Set E)) = Module.finrank ℤ ↥L₁
      exact Commons.Lattice.Discrete.finrank_span_eq_finrank (n := nA) L₁
    have hf₂ : Module.finrank ℝ ↥(realSpan L₂) = Module.finrank ℤ ↥L₂ := by
      change Module.finrank ℝ ↥(Submodule.span ℝ (L₂ : Set E)) = Module.finrank ℤ ↥L₂
      exact Commons.Lattice.Discrete.finrank_span_eq_finrank (n := nA) L₂
    have hfI : Module.finrank ℝ ↥(realSpan (L₁ ⊓ L₂)) = Module.finrank ℤ ↥(L₁ ⊓ L₂) := by
      change Module.finrank ℝ ↥(Submodule.span ℝ ((L₁ ⊓ L₂ : Submodule ℤ E) : Set E)) =
        Module.finrank ℤ ↥(L₁ ⊓ L₂)
      exact Commons.Lattice.Discrete.finrank_span_eq_finrank (n := nA) (L₁ ⊓ L₂)
    have hfSup : Module.finrank ℝ ↥(realSpan (L₁ ⊔ L₂)) = Module.finrank ℤ ↥(L₁ ⊔ L₂) := by
      change Module.finrank ℝ ↥(Submodule.span ℝ ((L₁ ⊔ L₂ : Submodule ℤ E) : Set E)) =
        Module.finrank ℤ ↥(L₁ ⊔ L₂)
      exact Commons.Lattice.Discrete.finrank_span_eq_finrank (n := nA) (L₁ ⊔ L₂)
    have hdim := Submodule.finrank_sup_add_finrank_inf_eq (K := ℝ) (V := E)
      (s := realSpan L₁) (t := realSpan L₂)
    have hsupEq : realSpan L₁ ⊔ realSpan L₂ = realSpan (L₁ ⊔ L₂) := realSpan_sup.symm
    have hrk := uncrossing_rank (L := L) h₁ h₂
    have h1 : Module.finrank ℝ ↥(realSpan L₁ ⊔ realSpan L₂) = Module.finrank ℤ ↥(L₁ ⊔ L₂) := by
      rw [hsupEq]
      exact hfSup
    -- hdim : finrank(U₁⊔U₂) + finrank(U₁⊓U₂) = finrank U₁ + finrank U₂
    -- goal: finrank (realSpan L₁ ⊓ realSpan L₂) = finrank ℤ (L₁ ⊓ L₂)
    have hgoal : Module.finrank ℝ ↥(realSpan L₁ ⊓ realSpan L₂) = Module.finrank ℤ ↥(L₁ ⊓ L₂) := by
      nlinarith [hdim, hf₁, hf₂, h1, hrk, hfI]
    -- target: finrank S₁ = finrank S₂ where S₂ := realSpanL₁ ⊓ realSpanL₂ : need finrank ↥S₂ = hgoal's LHS
    change Module.finrank ℝ ↥(realSpan (L₁ ⊓ L₂)) = Module.finrank ℝ ↥(realSpan L₁ ⊓ realSpan L₂)
    rw [hfI, hgoal]



/-- The ambient ℤ-linear projection onto the orthogonal complement of `S`. -/
def projMap (S : Submodule ℝ E) : E →ₗ[ℤ] E :=
  (Sᗮ.starProjection : E →ₗ[ℝ] E).restrictScalars ℤ

lemma projMap_apply (S : Submodule ℝ E) (x : E) : projMap S x = Sᗮ.starProjection x := rfl

/-- The value family of a mapped basis is ℤ-independent, given injectivity on `M`. -/
lemma map_values_linIndep {M : Submodule ℤ E} {r : ℕ} (f : E →ₗ[ℤ] E)
    (hf : ∀ m : M, f (m : E) = 0 → m = 0) (b : Module.Basis (Fin r) ℤ M) :
    LinearIndependent ℤ (fun j : Fin r => f ((b j : M) : E)) := by
  rw [Fintype.linearIndependent_iff]
  intro c hc
  let sE : E := ∑ j : Fin r, c j • ((b j : M) : E)
  have hsE_mem : sE ∈ M := by
    dsimp [sE]
    exact Submodule.sum_mem (M) (by intro j hj; exact Submodule.smul_mem (M) (c j) ((b j : M).2))
  have hs0 : f sE = 0 := by
    dsimp [sE]
    calc
      f (∑ j : Fin r, c j • ((b j : M) : E)) = ∑ j : Fin r, c j • f ((b j : M) : E) := by
        rw [map_sum]
        simp
      _ = 0 := by simpa using hc
  have hm : (⟨sE, hsE_mem⟩ : M) = 0 := hf ⟨sE, hsE_mem⟩ hs0
  have hsE0 : sE = 0 := by simpa using congrArg (fun m : M => (m : E)) hm
  have hbval : LinearIndependent ℤ (fun j : Fin r => ((b j : M) : E)) := by
    exact (b.linearIndependent).map' (M.subtype) (by simp)
  rw [Fintype.linearIndependent_iff] at hbval
  exact hbval c hsE0

/-- A ℤ-basis of `M` from ambient values: independent family in `E`, inside `M`, spanning `M`. -/
lemma basis_of_ambient {M : Submodule ℤ E} {r : ℕ} (w : Fin r → E)
    (hspan : M ≤ Submodule.span ℤ (Set.range w))
    (hmem : ∀ j : Fin r, w j ∈ M)
    (hind : LinearIndependent ℤ w) :
    ∃ β : Module.Basis (Fin r) ℤ M, ∀ j : Fin r, ((β j : M) : E) = w j := by
  classical
  let w' : Fin r → M := fun j => ⟨w j, hmem j⟩
  have hvals : (fun j : Fin r => ((w' j : M) : E)) = w := by
    funext j
    rfl
  have hli : LinearIndependent ℤ w' := by
    apply Commons.LinearAlgebra.Independence.linearIndependent_of_ambient (P := M) (v := w')
    simpa [hvals] using hind
  have hspanInt : ⊤ ≤ Submodule.span ℤ (Set.range w') := by
    intro z hz
    have hzval : (z : E) ∈ (Submodule.span ℤ (Set.range w) : Set E) := hspan z.2
    have hzspan : (z : E) ∈ (Submodule.span ℤ (Set.range (fun j : Fin r => ((w' j : M) : E))) : Set E) := by
      simpa [hvals] using hzval
    rcases (Submodule.mem_span_range_iff_exists_fun (R := ℤ)
        (v := fun j : Fin r => ((w' j : M) : E)) (x := (z : E))).mp hzspan with ⟨c, hc⟩
    have hz' : (∑ j : Fin r, c j • (w' j : M)) = z := by
      apply Subtype.ext
      calc
        (((∑ j : Fin r, c j • (w' j : M)) : M) : E)
            = (M.subtype : M →ₗ[ℤ] E) (∑ j : Fin r, c j • (w' j : M)) := rfl
        _ = ∑ j : Fin r, c j • ((w' j : M) : E) := by
            rw [map_sum]
            simp
        _ = (z : E) := hc
    exact (Submodule.mem_span_range_iff_exists_fun (R := ℤ) (v := w') (x := z)).2 ⟨c, hz'⟩
  let β : Module.Basis (Fin r) ℤ M := Module.Basis.mk hli hspanInt
  refine ⟨β, ?_⟩
  intro j
  have hb : (β j : M) = w' j := by simp [β, w']
  simpa [w'] using congrArg (fun z : M => (z : E)) hb

/-- Determinant expressed through ANY basis (index `Fin r`) of the lattice. -/
lemma det_eq_sqrt_gram_any_basis {L : Submodule ℤ E} [DiscreteTopology L]
    [Module.Free ℤ L] [Module.Finite ℤ L] {r : ℕ} (β : Module.Basis (Fin r) ℤ L) :
    ReverseMinkowski.determinant L =
      √((Matrix.gram ℝ (fun j : Fin r => ((β j : L) : E))).det) := by
  classical
  have hfin : Module.finrank ℤ L = r := by
    simpa using (Module.finrank_eq_card_basis β)
  let β' : Module.Basis (Fin (Module.finrank ℤ L)) ℤ L := β.reindex (finCongr hfin).symm
  have h0 := Submission.DetQuot.determinant_eq_sqrt_gram (ℒ := L) β'
  have hfam : (fun i : Fin (Module.finrank ℤ L) => ((β' i : L) : E)) =
      (fun j : Fin r => ((β j : L) : E)) ∘ (finCongr hfin) := by
    funext i
    dsimp [β']
    rw [Module.Basis.reindex_apply]
    rfl
  calc
    ReverseMinkowski.determinant L =
        √((Matrix.gram ℝ (fun i : Fin (Module.finrank ℤ L) => ((β' i : L) : E))).det) := by
          simpa [Matrix.gram] using h0
    _ = √((Matrix.gram ℝ (fun j : Fin r => ((β j : L) : E))).det) := by
        congr 1
        have hg : Matrix.gram ℝ (fun i : Fin (Module.finrank ℤ L) => ((β' i : L) : E)) =
            (Matrix.gram ℝ (fun j : Fin r => ((β j : L) : E))).submatrix (finCongr hfin) (finCongr hfin) := by
          rw [hfam]
          ext a b
          simp [Matrix.gram]
        rw [hg]
        simp

/-- Determinant of a sublattice `N` all of whose elements lie in the ℤ-span of the
projection of a basis of `L` is ≤ det L (projection is a contraction, injective on `L`). -/
lemma det_proj_le {L : Submodule ℤ E} (S : Submodule ℝ E) {N : Submodule ℤ E}
    [DiscreteTopology L] [DiscreteTopology N] {r : ℕ} (v : Module.Basis (Fin r) ℤ L)
    (hspanN : N ≤ Submodule.span ℤ (Set.range (fun j : Fin r => (projMap S) ((v j : L) : E))))
    (hNmem : ∀ j : Fin r, (projMap S) ((v j : L) : E) ∈ N)
    (hfinj : ∀ m : L, (projMap S) (m : E) = 0 → m = 0) :
    ReverseMinkowski.determinant N ≤ ReverseMinkowski.determinant L := by
  classical
  haveI : Module.Free ℤ L := instModuleFree_of_discrete_submodule L
  haveI : Module.Finite ℤ L := instModuleFinite_of_discrete_submodule L
  let w : Fin r → E := fun j => (projMap S) ((v j : L) : E)
  have hmem : ∀ j : Fin r, w j ∈ N := hNmem
  have hspan : N ≤ Submodule.span ℤ (Set.range w) := by
    simpa [w] using hspanN
  have hind : LinearIndependent ℤ w := by
    exact map_values_linIndep (M := L) (f := projMap S) hfinj v
  rcases (basis_of_ambient (M := N) (w := w) hspan hmem hind) with ⟨β, hβval⟩
  haveI : Module.Free ℤ N := Module.Free.of_basis β
  haveI : Module.Finite ℤ N := Module.Finite.of_basis β
  have hgβ : (Matrix.gram ℝ (fun j : Fin r => ((β j : N) : E))) = Matrix.gram ℝ w := by
    ext a b
    simp [Matrix.gram, hβval]
  have hdetN : ReverseMinkowski.determinant N =
      √((Matrix.gram ℝ w).det) := by
    rw [det_eq_sqrt_gram_any_basis (L := N) β, hgβ]
  have hdetL : ReverseMinkowski.determinant L =
      √((Matrix.gram ℝ (fun j : Fin r => ((v j : L) : E))).det) := by
    rw [det_eq_sqrt_gram_any_basis (L := L) v]
  let T : E →ₗ[ℝ] E := Sᗮ.starProjection
  have hT : ∀ x : E, ‖T x‖ ≤ ‖x‖ := by
    intro x
    dsimp [T]
    exact norm_starProjection_le Sᗮ x
  have hcg := Commons.Analysis.InnerProductSpace.gram_sub_gram_of_contraction
    (n := nA) (m := r) (v := fun j : Fin r => ((v j : L) : E)) (T := T) hT
  have hwT : (fun j : Fin r => T ((v j : L) : E)) = w := by
    funext j
    dsimp [w, T]
    rfl
  have hPSD : ((Matrix.gram ℝ (fun j : Fin r => ((v j : L) : E))) -
      (Matrix.gram ℝ w)).PosSemidef := by
    simpa [hwT] using hcg
  have hgL0 : 0 ≤ (Matrix.gram ℝ (fun j : Fin r => ((v j : L) : E))).det :=
    (Matrix.posSemidef_gram ℝ (fun j : Fin r => ((v j : L) : E))).det_nonneg
  have hgN0 : 0 ≤ (Matrix.gram ℝ w).det := (Matrix.posSemidef_gram ℝ w).det_nonneg
  have hdetle : (Matrix.gram ℝ w).det ≤ (Matrix.gram ℝ (fun j : Fin r => ((v j : L) : E))).det := by
    exact Commons.LinearAlgebra.Matrix.det_mono_posSemidef_sub
      (A := Matrix.gram ℝ w)
      (B := Matrix.gram ℝ (fun j : Fin r => ((v j : L) : E)))
      (Matrix.posSemidef_gram ℝ w) hPSD
  calc
    ReverseMinkowski.determinant N = √((Matrix.gram ℝ w).det) := hdetN
    _ ≤ √((Matrix.gram ℝ (fun j : Fin r => ((v j : L) : E))).det) := by
        apply le_of_sq_le_sq
        · rw [Real.sq_sqrt hgN0, Real.sq_sqrt hgL0]
          exact hdetle
        · exact Real.sqrt_nonneg _
    _ = ReverseMinkowski.determinant L := by rw [hdetL]


lemma map_proj_bot_of_subset {M : Submodule ℤ E} (S : Submodule ℝ E)
    (h : M ≤ S.restrictScalars ℤ) : M.map (projMap S) = ⊥ := by
  apply le_bot_iff.mp
  intro x hx
  rcases (Submodule.mem_map.mp hx) with ⟨m, hm, hxeq⟩
  have hf0 : (projMap S) (m : E) = 0 := by
    have hmS : (m : E) ∈ S := h hm
    simpa [projMap] using (starProjection_orthogonal_eq_zero_of_mem S hmS)
  rw [← hxeq]
  simpa using hf0

/-- **Reduced uncrossing**: if `M₁ ∩ M₂ = {0}` and `M₁` is primitive in `M₁+M₂`, then
`det(M₁+M₂) ≤ det M₁ · det M₂`. -/
lemma det_sup_le_mul_of_primitive {M₁ M₂ : Submodule ℤ E} [DiscreteTopology M₁]
    [DiscreteTopology M₂] [DiscreteTopology ↥(M₁ ⊔ M₂)]
    (hprim : Primitive M₁ (M₁ ⊔ M₂)) (hdisj : M₁ ⊓ M₂ = ⊥) :
    ReverseMinkowski.determinant (M₁ ⊔ M₂) ≤ ReverseMinkowski.determinant M₁ *
      ReverseMinkowski.determinant M₂ := by
  classical
  haveI : Module.Free ℤ M₁ := instModuleFree_of_discrete_submodule M₁
  haveI : Module.Finite ℤ M₁ := instModuleFinite_of_discrete_submodule M₁
  haveI : Module.Free ℤ M₂ := instModuleFree_of_discrete_submodule M₂
  haveI : Module.Finite ℤ M₂ := instModuleFinite_of_discrete_submodule M₂
  let S₁ : Submodule ℝ E := realSpan M₁
  haveI : DiscreteTopology ↥(quotLattice (M₁ ⊔ M₂) S₁) :=
    discrete_quotLattice (ℒ' := M₁) (ℒ := M₁ ⊔ M₂) S₁ (by rfl) hprim
  have hq : ReverseMinkowski.determinant (quotLattice (M₁ ⊔ M₂) S₁) =
      ReverseMinkowski.determinant (M₁ ⊔ M₂) / ReverseMinkowski.determinant M₁ := by
    exact Submission.SubLattice.determinant_quot_generic (nA := nA) (ℒ' := M₁)
      (ℒ := M₁ ⊔ M₂) S₁ (by rfl) hprim
  have hpos1 : ReverseMinkowski.determinant M₁ ≠ 0 := ne_of_gt (det_pos (L := M₁))
  have hM₁₀ : M₁.map (projMap S₁) = ⊥ := by
    apply map_proj_bot_of_subset (M := M₁) (S := S₁)
    intro m hm
    dsimp [S₁]
    exact mem_realSpan (ℒ := M₁) hm
  have hQeq : quotLattice (M₁ ⊔ M₂) S₁ = M₂.map (projMap S₁) := by
    dsimp [quotLattice]
    calc
      (M₁ ⊔ M₂).map ((S₁ᗮ.starProjection : E →ₗ[ℝ] E).restrictScalars ℤ) =
          M₁.map ((S₁ᗮ.starProjection : E →ₗ[ℝ] E).restrictScalars ℤ) ⊔
          M₂.map ((S₁ᗮ.starProjection : E →ₗ[ℝ] E).restrictScalars ℤ) := by
            rw [Submodule.map_sup]
      _ = M₂.map ((S₁ᗮ.starProjection : E →ₗ[ℝ] E).restrictScalars ℤ) := by
            have h₁₀ : M₁.map ((S₁ᗮ.starProjection : E →ₗ[ℝ] E).restrictScalars ℤ) = ⊥ := by
              exact hM₁₀
            rw [h₁₀]
            simp
      _ = M₂.map (projMap S₁) := rfl
  have hfinj : ∀ m : M₂, (projMap S₁) (m : E) = 0 → m = 0 := by
    intro m hm
    have hmS : (m : E) ∈ S₁ := by
      have horth : S₁ᗮ.starProjection (m : E) = 0 := by simpa [projMap] using hm
      have hsub : (m : E) - S₁.starProjection (m : E) = 0 := by
        rw [← proj_orth_comp S₁ (m : E)]
        exact horth
      have hEq : (m : E) = S₁.starProjection (m : E) := sub_eq_zero.mp hsub
      rw [hEq]
      exact Submodule.starProjection_apply_mem S₁ (m : E)
    have hmM₁ : (m : E) ∈ M₁ := (hprim (m : E)).mpr
      ⟨(le_sup_right : M₂ ≤ M₁ ⊔ M₂) m.2, hmS⟩
    have hmemI : (m : E) ∈ M₁ ⊓ M₂ := ⟨hmM₁, m.2⟩
    have hz : (m : E) = 0 := by
      have : (m : E) ∈ (⊥ : Submodule ℤ E) := by
        rw [← hdisj]
        exact hmemI
      simpa using this
    apply Subtype.ext
    exact hz
  let r : ℕ := Module.finrank ℤ M₂
  let v : Module.Basis (Fin r) ℤ M₂ := Module.finBasis ℤ M₂
  -- each projected basis value lies in the quotient lattice
  have hNmem : ∀ j : Fin r, (projMap S₁) ((v j : M₂) : E) ∈ quotLattice (M₁ ⊔ M₂) S₁ := by
    intro j
    rw [mem_quotLattice]
    exact ⟨(v j : M₂), (le_sup_right : M₂ ≤ M₁ ⊔ M₂) (v j : M₂).2, rfl⟩
  -- the quotient lattice is spanned by the projected basis values
  have hQeqset : quotLattice (M₁ ⊔ M₂) S₁ ≤ M₂.map (projMap S₁) := by
    rw [hQeq]
  have hspanQ : quotLattice (M₁ ⊔ M₂) S₁ ≤ Submodule.span ℤ
      (Set.range (fun j : Fin r => (projMap S₁) ((v j : M₂) : E))) := by
    intro x hx
    have hxmap : x ∈ M₂.map (projMap S₁) := hQeqset hx
    rcases (Submodule.mem_map.mp hxmap) with ⟨m, hm, hxeq⟩
    let e : M₂ := ⟨m, hm⟩
    let c : Fin r → ℤ := fun j => (v.repr e j : ℤ)
    have hmexp : (e : E) = ∑ j : Fin r, c j • ((v j : M₂) : E) := by
      dsimp [e, c]
      simpa using (ambient_basis_expand (ℒ := M₂) (b := v) ⟨m, hm⟩)
    have hxw : x = ∑ j : Fin r, c j • (projMap S₁) ((v j : M₂) : E) := by
      calc
        x = (projMap S₁) (e : E) := by
          rw [← hxeq]
        _ = (projMap S₁) (∑ j : Fin r, c j • ((v j : M₂) : E)) := by rw [hmexp]
        _ = ∑ j : Fin r, c j • (projMap S₁) ((v j : M₂) : E) := by
          rw [map_sum]
          simp
    exact (Submodule.mem_span_range_iff_exists_fun (R := ℤ)
      (v := fun j : Fin r => (projMap S₁) ((v j : M₂) : E)) (x := x)).2 ⟨c, hxw.symm⟩
  have hdetQ : ReverseMinkowski.determinant (quotLattice (M₁ ⊔ M₂) S₁) ≤
      ReverseMinkowski.determinant M₂ := by
    exact det_proj_le (L := M₂) S₁ v hspanQ hNmem hfinj
  have hdetS : ReverseMinkowski.determinant (M₁ ⊔ M₂) = ReverseMinkowski.determinant (quotLattice (M₁ ⊔ M₂) S₁) *
      ReverseMinkowski.determinant M₁ := by
    calc
      ReverseMinkowski.determinant (M₁ ⊔ M₂) =
          (ReverseMinkowski.determinant (M₁ ⊔ M₂) / ReverseMinkowski.determinant M₁) *
            ReverseMinkowski.determinant M₁ := by
              field_simp [hpos1]
      _ = ReverseMinkowski.determinant (quotLattice (M₁ ⊔ M₂) S₁) *
          ReverseMinkowski.determinant M₁ := by rw [← hq]
  calc
    ReverseMinkowski.determinant (M₁ ⊔ M₂) =
        ReverseMinkowski.determinant (quotLattice (M₁ ⊔ M₂) S₁) *
          ReverseMinkowski.determinant M₁ := hdetS
    _ ≤ ReverseMinkowski.determinant M₂ * ReverseMinkowski.determinant M₁ := by
        exact mul_le_mul_of_nonneg_right hdetQ (le_of_lt (det_pos (L := M₁)))
    _ = ReverseMinkowski.determinant M₁ * ReverseMinkowski.determinant M₂ := by ring


/-- Determinants of equal lattices coincide. -/
lemma det_eq_of_eq {L₁ L₂ : Submodule ℤ E} [DiscreteTopology L₁] [DiscreteTopology L₂]
    (h : L₁ = L₂) : ReverseMinkowski.determinant L₁ = ReverseMinkowski.determinant L₂ := by
  classical
  haveI : Module.Free ℤ L₁ := instModuleFree_of_discrete_submodule L₁
  haveI : Module.Finite ℤ L₁ := instModuleFinite_of_discrete_submodule L₁
  haveI : Module.Free ℤ L₂ := instModuleFree_of_discrete_submodule L₂
  haveI : Module.Finite ℤ L₂ := instModuleFinite_of_discrete_submodule L₂
  let v : Module.Basis (Fin (Module.finrank ℤ L₁)) ℤ L₁ := Module.finBasis ℤ L₁
  let w : Fin (Module.finrank ℤ L₁) → E := fun j => ((v j : L₁) : E)
  have hmem : ∀ j : Fin (Module.finrank ℤ L₁), w j ∈ L₂ := by
    intro j
    dsimp [w]
    rw [← h]
    exact (v j : L₁).2
  have hspan : L₂ ≤ Submodule.span ℤ (Set.range w) := by
    intro x hx
    have hx1 : x ∈ L₁ := by rw [h]; exact hx
    let e : L₁ := ⟨x, hx1⟩
    let c : Fin (Module.finrank ℤ L₁) → ℤ := fun j => (v.repr e j : ℤ)
    have hmexp : (e : E) = ∑ j : Fin (Module.finrank ℤ L₁), c j • ((v j : L₁) : E) := by
      dsimp [e, c]
      simpa using (ambient_basis_expand (ℒ := L₁) (b := v) ⟨x, hx1⟩)
    have hxw : x = ∑ j : Fin (Module.finrank ℤ L₁), c j • w j := by
      calc
        x = (e : E) := rfl
        _ = ∑ j : Fin (Module.finrank ℤ L₁), c j • ((v j : L₁) : E) := hmexp
        _ = ∑ j : Fin (Module.finrank ℤ L₁), c j • w j := by
          apply Finset.sum_congr rfl
          intro j hj
          dsimp [w]
    exact (Submodule.mem_span_range_iff_exists_fun (R := ℤ) (v := w) (x := x)).2 ⟨c, hxw.symm⟩
  have hind : LinearIndependent ℤ w := by
    dsimp [w]
    exact (v.linearIndependent).map' L₁.subtype (by simp)
  rcases (basis_of_ambient (M := L₂) (w := w) hspan hmem hind) with ⟨β, hβval⟩
  have hgram : (Matrix.gram ℝ (fun j : Fin (Module.finrank ℤ L₁) => ((β j : L₂) : E))) =
      Matrix.gram ℝ w := by
    ext a b
    simp [Matrix.gram, hβval]
  have hdet2 : ReverseMinkowski.determinant L₂ =
      √((Matrix.gram ℝ w).det) := by
    rw [det_eq_sqrt_gram_any_basis (L := L₂) β, hgram]
  have hdet1 : ReverseMinkowski.determinant L₁ =
      √((Matrix.gram ℝ w).det) := by
    rw [det_eq_sqrt_gram_any_basis (L := L₁) v]
  rw [hdet1, hdet2]


/-- The real span of the projected lattice equals the projection of the real span. -/
lemma realSpan_map_proj {L : Submodule ℤ E} (S : Submodule ℝ E) :
    realSpan (L.map (projMap S)) = (realSpan L).map (Sᗮ.starProjection : E →ₗ[ℝ] E) := by
  classical
  unfold realSpan
  let p : E →ₗ[ℝ] E := Sᗮ.starProjection
  have hset : ((L.map (projMap S)) : Set E) = p '' (L : Set E) := by
    ext x
    constructor
    · intro hx
      rcases (Submodule.mem_map.mp hx) with ⟨m, hm, hxeq⟩
      exact ⟨m, hm, by simpa [p, projMap] using hxeq⟩
    · rintro ⟨m, hm, hxeq⟩
      exact Submodule.mem_map.mpr ⟨m, hm, by simpa [p, projMap] using hxeq⟩
  calc
    Submodule.span ℝ ((L.map (projMap S)) : Set E) = Submodule.span ℝ (p '' (L : Set E)) := by
      rw [hset]
    _ = Submodule.map p (Submodule.span ℝ (L : Set E)) := by
      rw [Submodule.map_span]
    _ = (realSpan L).map p := by rfl

/-- Membership in the real span of the projected lattice. -/
lemma mem_realSpan_map_proj {L : Submodule ℤ E} (S : Submodule ℝ E) {x : E} :
    x ∈ realSpan (L.map (projMap S)) ↔ ∃ y ∈ realSpan L, (projMap S) y = x := by
  rw [realSpan_map_proj]
  constructor
  · intro hx
    rcases (Submodule.mem_map.mp hx) with ⟨y, hy, hxeq⟩
    exact ⟨y, hy, by simpa [projMap] using hxeq⟩
  · rintro ⟨y, hy, hxeq⟩
    exact Submodule.mem_map.mpr ⟨y, hy, by simpa [projMap] using hxeq⟩


/-- **Stuhler uncrossing (Lemma 2.4, determinant part)**. -/
theorem uncrossing_det {L L₁ L₂ : Submodule ℤ E} [DiscreteTopology L]
    [DiscreteTopology L₁] [DiscreteTopology L₂]
    [DiscreteTopology ↥(L₁ ⊔ L₂)] [DiscreteTopology ↥(L₁ ⊓ L₂)]
    (h₁ : L₁ ≤ L) (h₂ : L₂ ≤ L) (hp₁ : Primitive L₁ L) (hp₂ : Primitive L₂ L) :
    ReverseMinkowski.determinant (L₁ ⊔ L₂) * ReverseMinkowski.determinant (L₁ ⊓ L₂) ≤
      ReverseMinkowski.determinant L₁ * ReverseMinkowski.determinant L₂ := by
  classical
  haveI : Module.Free ℤ L₁ := instModuleFree_of_discrete_submodule L₁
  haveI : Module.Finite ℤ L₁ := instModuleFinite_of_discrete_submodule L₁
  haveI : Module.Free ℤ L₂ := instModuleFree_of_discrete_submodule L₂
  haveI : Module.Finite ℤ L₂ := instModuleFinite_of_discrete_submodule L₂
  haveI : Module.Free ℤ ↥(L₁ ⊔ L₂) := instModuleFree_of_discrete_submodule (L₁ ⊔ L₂)
  haveI : Module.Finite ℤ ↥(L₁ ⊔ L₂) := instModuleFinite_of_discrete_submodule (L₁ ⊔ L₂)
  haveI : Module.Free ℤ ↥(L₁ ⊓ L₂) := instModuleFree_of_discrete_submodule (L₁ ⊓ L₂)
  haveI : Module.Finite ℤ ↥(L₁ ⊓ L₂) := instModuleFinite_of_discrete_submodule (L₁ ⊓ L₂)
  let I : Submodule ℤ E := L₁ ⊓ L₂
  let S : Submodule ℝ E := realSpan I
  have hpI₁ : Primitive I L₁ := by
    dsimp [I]
    exact inter_primitive_left (L₁ := L₁) (L₂ := L₂) (L := L) hp₂ h₁
  have hpI₂ : Primitive I L₂ := by
    dsimp [I]
    exact inter_primitive_right (L₁ := L₁) (L₂ := L₂) (L := L) hp₁ h₂
  have hpISum : Primitive I (L₁ ⊔ L₂) := by
    dsimp [I]
    exact primitive_inter_sup (L₁ := L₁) (L₂ := L₂) (L := L) hp₁ hp₂
  haveI : DiscreteTopology ↥(quotLattice (L₁ ⊔ L₂) S) :=
    discrete_quotLattice (ℒ' := I) (ℒ := L₁ ⊔ L₂) S (by rfl) hpISum
  haveI : DiscreteTopology ↥(quotLattice L₁ S) :=
    discrete_quotLattice (ℒ' := I) (ℒ := L₁) S (by rfl) hpI₁
  haveI : DiscreteTopology ↥(quotLattice L₂ S) :=
    discrete_quotLattice (ℒ' := I) (ℒ := L₂) S (by rfl) hpI₂
  -- det-quot applications
  have hqQ : ReverseMinkowski.determinant (quotLattice (L₁ ⊔ L₂) S) =
      ReverseMinkowski.determinant (L₁ ⊔ L₂) / ReverseMinkowski.determinant I := by
    exact Submission.SubLattice.determinant_quot_generic (nA := nA) (ℒ' := I)
      (ℒ := L₁ ⊔ L₂) S (by rfl) hpISum
  have hq₁ : ReverseMinkowski.determinant (quotLattice L₁ S) =
      ReverseMinkowski.determinant L₁ / ReverseMinkowski.determinant I := by
    exact Submission.SubLattice.determinant_quot_generic (nA := nA) (ℒ' := I)
      (ℒ := L₁) S (by rfl) hpI₁
  have hq₂ : ReverseMinkowski.determinant (quotLattice L₂ S) =
      ReverseMinkowski.determinant L₂ / ReverseMinkowski.determinant I := by
    exact Submission.SubLattice.determinant_quot_generic (nA := nA) (ℒ' := I)
      (ℒ := L₂) S (by rfl) hpI₂
  -- Q := quotLattice Σ S equals Q₁ ⊔ Q₂
  have hQsum : quotLattice (L₁ ⊔ L₂) S = quotLattice L₁ S ⊔ quotLattice L₂ S := by
    dsimp [quotLattice]
    rw [Submodule.map_sup]
  -- discreteness of Q₁ ⊔ Q₂ (instance)
  haveI : DiscreteTopology ↥(quotLattice L₁ S ⊔ quotLattice L₂ S) := by
    rw [← hQsum]
    infer_instance
  -- hdisjQ : Q₁ ∩ Q₂ = ⊥
  have hdisjQ : quotLattice L₁ S ⊓ quotLattice L₂ S = ⊥ := by
    apply le_antisymm
    · intro x hx
      rcases (Submodule.mem_inf.mp hx) with ⟨hxQ₁, hxQ₂⟩
      change x ∈ L₁.map (projMap S) at hxQ₁
      change x ∈ L₂.map (projMap S) at hxQ₂
      rcases (Submodule.mem_map.mp hxQ₁) with ⟨a, ha, hxeq₁⟩
      rcases (Submodule.mem_map.mp hxQ₂) with ⟨b, hb, hxeq₂⟩
      -- π a = x = π b; a ∈ L₁, b ∈ L₂
      have hπa : (projMap S) a = x := hxeq₁
      have hπb : (projMap S) b = x := hxeq₂
      have hab0 : (projMap S) (a - b) = 0 := by
        rw [map_sub, hπa, hπb]
        simp
      have habS : a - b ∈ S := by
        have : Sᗮ.starProjection (a - b) = 0 := by simpa [projMap] using hab0
        exact Commons.Lattice.Discrete.mem_of_proj_orth_eq_zero (n := nA) S this
      have hbV₁ : b ∈ realSpan L₁ := by
        have haV₁ : a ∈ realSpan L₁ := mem_realSpan (ℒ := L₁) ha
        have habV₁ : a - b ∈ realSpan L₁ := by
          exact (realSpan_mono (L₁ := I) (L₂ := L₁) inf_le_left : realSpan I ≤ realSpan L₁)
            (by simpa [I] using habS)
        have hb' : b = a - (a - b) := by abel
        rw [hb']
        exact Submodule.sub_mem (realSpan L₁) haV₁ habV₁
      have hbL₁ : b ∈ L₁ := (hp₁ b).mpr ⟨h₂ hb, hbV₁⟩
      have hbI : b ∈ I := by
        dsimp [I]
        exact ⟨hbL₁, hb⟩
      have hx0 : x = 0 := by
        rw [← hxeq₂]
        have hbS : b ∈ S := by
          dsimp [S]
          exact mem_realSpan (ℒ := I) hbI
        simpa [projMap] using (starProjection_orthogonal_eq_zero_of_mem S hbS)
      simpa [hx0]
    · intro x hx
      have hx0 : x = 0 := by simpa using hx
      simp [hx0]
  -- hprimQ : Primitive Q₁ (Q₁ ⊔ Q₂)
  have hprimQ : Primitive (quotLattice L₁ S) (quotLattice L₁ S ⊔ quotLattice L₂ S) := by
    intro x
    constructor
    · intro hxQ₁
      exact ⟨(le_sup_left : quotLattice L₁ S ≤ quotLattice L₁ S ⊔ quotLattice L₂ S) hxQ₁,
        mem_realSpan (ℒ := quotLattice L₁ S) hxQ₁⟩
    · intro hx
      rcases hx with ⟨hxsum, hxspan⟩
      have hxQ : x ∈ quotLattice (L₁ ⊔ L₂) S := by
        rw [hQsum]
        exact hxsum
      change x ∈ (L₁ ⊔ L₂).map (projMap S) at hxQ
      rcases (Submodule.mem_map.mp hxQ) with ⟨m, hmSg, hxeqQ⟩
      have hxspan' : x ∈ realSpan (L₁.map (projMap S)) := by
        change x ∈ realSpan (quotLattice L₁ S)
        exact hxspan
      rcases (mem_realSpan_map_proj (L := L₁) S).mp hxspan' with ⟨y, hyV₁, hxeqπ⟩
      have hm_yS : m - y ∈ S := by
        have hπ : (projMap S) (m - y) = 0 := by
          rw [map_sub]
          have h1 : (projMap S) m = x := hxeqQ
          have h2 : (projMap S) y = x := hxeqπ
          rw [h1, h2]
          simp
        have : Sᗮ.starProjection (m - y) = 0 := by simpa [projMap] using hπ
        exact Commons.Lattice.Discrete.mem_of_proj_orth_eq_zero (n := nA) S this
      have hmV₁ : m ∈ realSpan L₁ := by
        have hleS : S ≤ realSpan L₁ := by
          dsimp [S]
          exact realSpan_mono (L₁ := I) (L₂ := L₁) inf_le_left
        have hy_m : y + (m - y) = m := by abel
        rw [← hy_m]
        exact Submodule.add_mem (realSpan L₁) hyV₁ (hleS hm_yS)
      rcases (Submodule.mem_sup.mp hmSg) with ⟨m₁, hm₁, m₂, hm₂, hmsum⟩
      have hm₂V₁ : m₂ ∈ realSpan L₁ := by
        have hm₁V₁ : m₁ ∈ realSpan L₁ := mem_realSpan (ℒ := L₁) hm₁
        have hm₂' : m - m₁ = m₂ := by rw [← hmsum]; abel
        rw [← hm₂']
        exact Submodule.sub_mem (realSpan L₁) hmV₁ hm₁V₁
      have hm₂L₁ : m₂ ∈ L₁ := (hp₁ m₂).mpr ⟨h₂ hm₂, hm₂V₁⟩
      have hm₂S : m₂ ∈ S := by
        dsimp [S]
        exact mem_realSpan (ℒ := I) ⟨hm₂L₁, hm₂⟩
      have hxeq : x = (projMap S) m₁ := by
        calc
          x = (projMap S) m := hxeqQ.symm
          _ = (projMap S) (m₁ + m₂) := by rw [← hmsum]
          _ = (projMap S) m₁ + (projMap S) m₂ := by rw [map_add]
          _ = (projMap S) m₁ := by
            have hπm₂ : (projMap S) m₂ = 0 := by
              simpa [projMap] using (starProjection_orthogonal_eq_zero_of_mem S hm₂S)
            rw [hπm₂]
            simp
      change x ∈ L₁.map (projMap S)
      exact Submodule.mem_map.mpr ⟨m₁, hm₁, hxeq.symm⟩
  -- reduced inequality on the quotients
  have hred : ReverseMinkowski.determinant (quotLattice L₁ S ⊔ quotLattice L₂ S) ≤
      ReverseMinkowski.determinant (quotLattice L₁ S) *
        ReverseMinkowski.determinant (quotLattice L₂ S) := by
    exact det_sup_le_mul_of_primitive (M₁ := quotLattice L₁ S) (M₂ := quotLattice L₂ S)
      hprimQ hdisjQ
  have hdeteq : ReverseMinkowski.determinant (quotLattice (L₁ ⊔ L₂) S) =
      ReverseMinkowski.determinant (quotLattice L₁ S ⊔ quotLattice L₂ S) := by
    exact det_eq_of_eq (L₁ := quotLattice (L₁ ⊔ L₂) S) (L₂ := quotLattice L₁ S ⊔ quotLattice L₂ S)
      hQsum
  have hQle : ReverseMinkowski.determinant (quotLattice (L₁ ⊔ L₂) S) ≤
      ReverseMinkowski.determinant (quotLattice L₁ S) *
        ReverseMinkowski.determinant (quotLattice L₂ S) := by
    rw [hdeteq]
    exact hred
  have hposI : 0 < ReverseMinkowski.determinant I := det_pos (L := I)
  have hIne : ReverseMinkowski.determinant I ≠ 0 := ne_of_gt hposI
  have hL₁' : ReverseMinkowski.determinant L₁ = ReverseMinkowski.determinant I *
      ReverseMinkowski.determinant (quotLattice L₁ S) := by
    calc
      ReverseMinkowski.determinant L₁ = (ReverseMinkowski.determinant L₁ /
          ReverseMinkowski.determinant I) * ReverseMinkowski.determinant I := by
            field_simp [hIne]
      _ = ReverseMinkowski.determinant (quotLattice L₁ S) * ReverseMinkowski.determinant I := by
            rw [← hq₁]
      _ = ReverseMinkowski.determinant I * ReverseMinkowski.determinant (quotLattice L₁ S) := by ring
  have hL₂' : ReverseMinkowski.determinant L₂ = ReverseMinkowski.determinant I *
      ReverseMinkowski.determinant (quotLattice L₂ S) := by
    calc
      ReverseMinkowski.determinant L₂ = (ReverseMinkowski.determinant L₂ /
          ReverseMinkowski.determinant I) * ReverseMinkowski.determinant I := by
            field_simp [hIne]
      _ = ReverseMinkowski.determinant (quotLattice L₂ S) * ReverseMinkowski.determinant I := by
            rw [← hq₂]
      _ = ReverseMinkowski.determinant I * ReverseMinkowski.determinant (quotLattice L₂ S) := by ring
  have hS' : ReverseMinkowski.determinant (L₁ ⊔ L₂) = ReverseMinkowski.determinant I *
      ReverseMinkowski.determinant (quotLattice (L₁ ⊔ L₂) S) := by
    calc
      ReverseMinkowski.determinant (L₁ ⊔ L₂) = (ReverseMinkowski.determinant (L₁ ⊔ L₂) /
          ReverseMinkowski.determinant I) * ReverseMinkowski.determinant I := by
            field_simp [hIne]
      _ = ReverseMinkowski.determinant (quotLattice (L₁ ⊔ L₂) S) * ReverseMinkowski.determinant I := by
            rw [← hqQ]
      _ = ReverseMinkowski.determinant I * ReverseMinkowski.determinant (quotLattice (L₁ ⊔ L₂) S) := by ring
  calc
    ReverseMinkowski.determinant (L₁ ⊔ L₂) * ReverseMinkowski.determinant I
        = (ReverseMinkowski.determinant I * ReverseMinkowski.determinant (quotLattice (L₁ ⊔ L₂) S)) *
            ReverseMinkowski.determinant I := by rw [hS']
    _ = ReverseMinkowski.determinant (quotLattice (L₁ ⊔ L₂) S) *
        (ReverseMinkowski.determinant I * ReverseMinkowski.determinant I) := by ring
    _ ≤ (ReverseMinkowski.determinant (quotLattice L₁ S) *
          ReverseMinkowski.determinant (quotLattice L₂ S)) *
        (ReverseMinkowski.determinant I * ReverseMinkowski.determinant I) := by
          exact mul_le_mul_of_nonneg_right hQle
            (mul_nonneg (le_of_lt hposI) (le_of_lt hposI))
    _ = (ReverseMinkowski.determinant I * ReverseMinkowski.determinant (quotLattice L₁ S)) *
        (ReverseMinkowski.determinant I * ReverseMinkowski.determinant (quotLattice L₂ S)) := by ring
    _ = ReverseMinkowski.determinant L₁ * ReverseMinkowski.determinant L₂ := by
          rw [← hL₁', ← hL₂']

end
end Submission.Uncrossing
