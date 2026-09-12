import Mathlib
import Submission.Work.Lattice.IntSubgroupCovol
import Submission.GeometryOfNumbers.FlowLattice
import Submission.Commons.Analysis.InnerProductSpace.intCoords_linearIndependent_real

/-!
# P1-general (a, flow form): every subgroup of the flow lattice is a family ℤ-span

Milestone (a) step 1: the subgroup ↔ family representation lemma for the **flow lattice**
`Λ = flowLattice a b ℓ` (the `ℤ`-span of the flowed standard basis `{f ((B d) i)}`,
`f = scaleMap (twoScale a b ℓ)`, `a b ≠ 0`).  For any discrete subgroup `W ≤ Λ`,
`W ≠ ⊥`, there is an `ℝ`-independent member family `cW : Fin n → Λ` of size `0 < n`
whose `ℤ`-span is exactly `W` (its `ℤ`-basis, coerced to the ambient space):

    `exists_basis_of_le_flowLattice`

The genuinely new ingredient over `IntSubgroupCovol.exists_basis_of_le_intLattice` is the
**ℤ-independence ⟹ ℝ-independence transfer for the flow lattice**: a `ℤ`-linearly
independent family of members of `Λ = f(ℤᵈ)` is `ℝ`-linearly independent, since pulling
back along the injective flow map `f` gives a `ℤ`-independent family of integer points
(fleet `intCoords_linearIndependent_real` applies: integer coordinates + ℤ-independence
⟹ ℝ-independence), and `ℝ`-independence is preserved by the injective linear map `f`.

All declarations are Mathlib + Submission (GraysonLattice/FlowLattice/Commons) only.
-/

noncomputable section

open Set Module Real LinearSubspaces
open scoped BigOperators
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1200000

namespace Submission.GraysonLattice

open Submission.GraysonData
open Submission.FlowLattice
open Submission.DiagonalFlow
open Submission.ExteriorCoordinates

/-- **ℤ-LI ⟹ ℝ-LI for members of the flow lattice**: a `ℤ`-linearly independent ambient
family of members of `flowLattice a b ℓ` (invertible flow) is `ℝ`-linearly independent.
Proof: write each member as `f z` with `z` an integer point (the flow lattice is the image
of `ℤᵈ` under the injective flow), transfer the `ℤ`-independence to the integer
preimage family `z`, apply the integer-coordinate ℝ-independence lemma
(`Commons.intCoords_linearIndependent_real`), and transfer back along the injective real
linear map `f`. -/
lemma linearIndependent_real_of_mem_flowLattice {d : ℕ} {a b : ℝ} (ℓ : ℕ)
    (ha : a ≠ 0) (hb : b ≠ 0) {n : ℕ} (u : Fin n → E d)
    (huℤ : ∀ r : Fin n, u r ∈ Submission.FlowLattice.flowLattice (d := d) a b ℓ)
    (hli : LinearIndependent ℤ u) : LinearIndependent ℝ u := by
  classical
  let f : E d →ₗ[ℤ] E d := (scaleMap (twoScale a b ℓ)).restrictScalars ℤ
  -- each member has an integer-coordinate preimage
  have hwmem : ∀ r : Fin n, ∃ z : E d, z ∈ intPoints (d := d) ∧ f z = u r := by
    intro r
    have hmem : u r ∈ Submission.FlowLattice.flowLattice (d := d) a b ℓ := huℤ r
    rw [flowLattice_eq_map (d := d) a b ℓ] at hmem
    exact (Submodule.mem_map).mp hmem
  let z : Fin n → E d := fun r => Classical.choose (hwmem r)
  have hzf : ∀ r : Fin n, f (z r) = u r := by
    intro r
    exact (Classical.choose_spec (hwmem r)).2
  have hzflow : ∀ r : Fin n, (scaleMap (twoScale a b ℓ)) (z r) = u r := by
    intro r
    exact hzf r
  -- ℤ-independence of the preimages
  have hzli : LinearIndependent ℤ z := by
    rw [Fintype.linearIndependent_iff]
    intro c hc j
    have hsum0 : (∑ i : Fin n, c i • u i) = 0 := by
      calc
        (∑ i : Fin n, c i • u i) = ∑ i : Fin n, c i • f (z i) := by
              apply Finset.sum_congr rfl
              intro i hi
              rw [← hzf i]
        _ = f (∑ i : Fin n, c i • z i) := by
              symm
              rw [map_sum]
              apply Finset.sum_congr rfl
              intro i hi
              rw [map_smul]
        _ = 0 := by
              rw [hc]
              simp
    exact (Fintype.linearIndependent_iff.mp hli) c hsum0 j
  -- ℝ-independence of the preimages (integer coordinates + ℤ-LI)
  have hzspan : ∀ r : Fin n, z r ∈ Submodule.span ℤ
      (Set.range (EuclideanSpace.basisFun (Fin d) ℝ)) := by
    intro r
    have hzI : z r ∈ intPoints (d := d) := (Classical.choose_spec (hwmem r)).1
    simpa [intPoints] using hzI
  have hzliℝ : LinearIndependent ℝ z :=
    Commons.Analysis.InnerProductSpace.intCoords_linearIndependent_real (u := z) hzspan hzli
  -- transfer back along the injective real linear map
  have hlinℝ : LinearIndependent ℝ (fun r : Fin n =>
      (scaleMap (twoScale a b ℓ)) (z r)) := by
    exact linearIndependent_comp_injective (f := scaleMap (twoScale a b ℓ))
      (by
        intro x y hxy
        apply (scaleMapEquiv (d := d) a b ℓ ha hb).injective
        exact hxy) z hzliℝ
  have hzeq : (fun r : Fin n => (scaleMap (twoScale a b ℓ)) (z r)) = u := by
    funext r
    exact hzflow r
  simpa [hzeq] using hlinℝ

/-- **Flow-lattice basis representation**: for `W ≤ flowLattice a b ℓ` (`W ≠ ⊥`,
invertible flow), there is an `ℝ`-independent member family `cW : Fin n → Λ` of size
`0 < n` with `W = span ℤ (range cW)` — the coerced `ℤ`-basis of `W` extracted by the PID
structure of the flow lattice (`Submodule.basisOfPidOfLESpan` over the flowed standard
basis). -/
lemma exists_basis_of_le_flowLattice {d : ℕ} {a b : ℝ} (ℓ : ℕ) (ha : a ≠ 0) (hb : b ≠ 0)
    (W : Submodule ℤ (E d)) (hWle : W ≤ Submission.FlowLattice.flowLattice (d := d) a b ℓ)
    (hW0 : W ≠ ⊥) :
    ∃ n : ℕ, 0 < n ∧ ∃ cW : Fin n → E d,
      LinearIndependent ℝ cW ∧
      (∀ r : Fin n, cW r ∈ Submission.FlowLattice.flowLattice (d := d) a b ℓ) ∧
      W = Submodule.span ℤ (Set.range cW) := by
  classical
  let fb : Fin d → E d := fun i => (scaleMap (twoScale a b ℓ)) ((B d) i)
  have hLI : LinearIndependent ℤ fb := by
    dsimp [fb]
    exact Submission.FlowLattice.linearIndependent_flow_basis (d := d) a b ℓ ha hb
  have hle : W ≤ Submodule.span ℤ (Set.range fb) := by
    dsimp [fb]
    simpa [Submission.FlowLattice.flowLattice] using hWle
  obtain ⟨n, bW⟩ := Submodule.basisOfPidOfLESpan (R := ℤ) (b := fb) hLI hle
  have hn0 : 0 < n := by
    by_contra hn
    have hnz : n = 0 := by omega
    subst n
    rw [Submodule.ne_bot_iff] at hW0
    obtain ⟨y, hyW, hy0⟩ := hW0
    let yW : W := ⟨y, hyW⟩
    have hspan : Submodule.span ℤ (Set.range (fun i : Fin 0 => bW i)) = ⊤ := bW.span_eq
    have hmem : yW ∈ Submodule.span ℤ (Set.range (fun i : Fin 0 => bW i)) := by
      rw [hspan]
      trivial
    have hybot : yW ∈ (⊥ : Submodule ℤ W) := by
      simpa using hmem
    have hyW0 : yW = 0 := (Submodule.mem_bot (R := ℤ)).mp hybot
    apply hy0
    exact congrArg (fun z : W => z.val) hyW0
  let cW : Fin n → E d := fun i => ((bW i : W) : E d)
  have hW_eq : W = Submodule.span ℤ (Set.range cW) := by
    apply le_antisymm
    · intro x hx
      let xW : W := ⟨x, hx⟩
      have hmem : xW ∈ Submodule.span ℤ (Set.range bW) := by
        rw [bW.span_eq]
        trivial
      rw [Submodule.mem_span_range_iff_exists_fun (α := Fin n) (R := ℤ) (v := bW)] at hmem
      rcases hmem with ⟨c, hc⟩
      have hcE : (∑ i : Fin n, c i • cW i) = x := by
        have hm := congrArg (fun z : W => (z : E d)) hc
        simpa [cW] using hm
      rw [← hcE]
      exact Submodule.sum_mem _ (fun i hi => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩))
    · rw [Submodule.span_le]
      rintro y ⟨i, rfl⟩
      exact (bW i : W).2
  have hzli : LinearIndependent ℤ cW := by
    have hliW : LinearIndependent ℤ (fun i : Fin n => (bW i : W)) := bW.linearIndependent
    exact hliW.map' (W.subtype.restrictScalars ℤ) (Submodule.ker_subtype W)
  refine ⟨n, hn0, cW, ?_, ?_, hW_eq⟩
  · exact linearIndependent_real_of_mem_flowLattice (ℓ := ℓ) ha hb cW (by
      intro r
      have hm : cW r ∈ Submission.FlowLattice.flowLattice (d := d) a b ℓ := by
        simpa [cW] using (hWle ((bW r : W).2))
      exact hm) hzli
  · intro r
    exact hWle ((bW r : W).2)

/-- The **size/rank identity**: an `ℝ`-independent `n`-member ambient family spans a
subgroup whose real dimension is `n`. -/
lemma subDim_span_range_of_linearIndependent {d n : ℕ} (u : Fin n → E d)
    (hli : LinearIndependent ℝ u) :
    subDim (Submodule.span ℤ (Set.range u)) = n := by
  have hRS : realSpan (Submodule.span ℤ (Set.range u)) =
      Submodule.span ℝ (Set.range u) := by
    dsimp [realSpan]
    rw [Submodule.span_span_of_tower (R := ℤ) (S := ℝ) (M := E d) (s := Set.range u)]
  dsimp [subDim]
  rw [hRS]
  simpa using (finrank_span_eq_card (R := ℝ) hli)


/-- Reindexing a family by a bijection does not change its `ℤ`-span. -/
lemma span_int_range_comp_bijective {d : ℕ} {n m : ℕ} (u : Fin n → E d) (e : Fin n ≃ Fin m) :
    Submodule.span ℤ (Set.range (fun r : Fin m => u (e.symm r))) =
      Submodule.span ℤ (Set.range u) := by
  apply congrArg (fun s : Set (E d) => Submodule.span ℤ s)
  ext x
  constructor
  · rintro ⟨r, rfl⟩
    exact ⟨e.symm r, rfl⟩
  · rintro ⟨s, rfl⟩
    refine ⟨e s, ?_⟩
    simp

/-- **Flow-lattice basis representation at the exact rank**: for `W ≤ flowLattice a b ℓ`
(invertible flow), `W ≠ ⊥`, the `ℤ`-basis of `W` can be presented as an `ℝ`-independent
member family indexed by `Fin (subDim W)` whose `ℤ`-span is `W`. -/
lemma exists_basis_family_of_le_flowLattice {d : ℕ} {a b : ℝ} (ℓ : ℕ) (ha : a ≠ 0)
    (hb : b ≠ 0) (W : Submodule ℤ (E d))
    (hWle : W ≤ Submission.FlowLattice.flowLattice (d := d) a b ℓ) (hW0 : W ≠ ⊥) :
    ∃ cW : Fin (subDim W) → E d,
      LinearIndependent ℝ cW ∧
      (∀ r : Fin (subDim W), cW r ∈ Submission.FlowLattice.flowLattice (d := d) a b ℓ) ∧
      W = Submodule.span ℤ (Set.range cW) := by
  classical
  rcases exists_basis_of_le_flowLattice (ℓ := ℓ) ha hb W hWle hW0 with ⟨n, hn0, cW0, hli, hmem, hW_eq⟩
  have hsub : subDim W = n := by
    rw [hW_eq]
    exact subDim_span_range_of_linearIndependent cW0 hli
  let e : Fin n ≃ Fin (subDim W) :=
    ((Fin.castOrderIso (n := subDim W) (m := n) hsub).toEquiv).symm
  let cW : Fin (subDim W) → E d := fun r => cW0 (e.symm r)
  refine ⟨cW, ?_, ?_, ?_⟩
  · have hli' : LinearIndependent ℝ (fun r : Fin (subDim W) => cW0 (e.symm r)) :=
      hli.comp e.symm e.symm.injective
    simpa [cW] using hli'
  · intro r
    simpa [cW] using hmem (e.symm r)
  · have hspan0 : Submodule.span ℤ (Set.range cW) = Submodule.span ℤ (Set.range cW0) := by
      dsimp [cW]
      exact span_int_range_comp_bijective (u := cW0) (e := e)
    calc
      W = Submodule.span ℤ (Set.range cW0) := hW_eq
      _ = Submodule.span ℤ (Set.range cW) := hspan0.symm

end Submission.GraysonLattice

end
