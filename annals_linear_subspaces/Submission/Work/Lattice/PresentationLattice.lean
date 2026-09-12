import Mathlib
import Submission.Work.Lattice.GraysonLattice
import Submission.Work.Lattice.FlowSubgroupBasis
import Submission.Commons.Analysis.InnerProductSpace.intCoords_linearIndependent_real

/-!
# P2/P3-general (b), step: presentation lemma for subgroups of an arbitrary lattice

Every discrete subgroup `W` of a full-rank lattice `Λ ≤ ℝᵈ`
(`[DiscreteTopology Λ] [IsZLattice ℝ Λ]`, `finrank ℤ Λ = d`) is the `ℤ`-span of an
`ℝ`-independent member family of size exactly `subDim W` — its `ℤ`-basis coerced to the
ambient space:

    `exists_basis_family_of_le_lattice` :  ∃ u : Fin (subDim W) → E d,
        LinearIndependent ℝ u ∧ (∀ r, u r ∈ Λ) ∧ W = span ℤ (range u)

This generalises `Submission.FlowSubgroupBasis` (the flow lattice) to an arbitrary
lattice.  The construction: a `ℤ`-basis of `Λ` (`Module.Free.chooseBasis`, reindexed to
`Fin d` via `hΛfin`) is at the same time an `ℝ`-basis of the ambient `ℝᵈ` (its real span
is all of `ℝᵈ` by `IsZLattice.span_top`, and a spanning family of `finrank`-many vectors
is linearly independent), so the basis-coordinate linear equivalence `B` sends `Λ` onto
the integer lattice `ℤᵈ`.  The PID basis extraction
`Submodule.basisOfPidOfLESpan` over the ambient `ℤ`-basis gives a `ℤ`-basis of `W`
(coerced family `cW`); its `ℝ`-independence follows from `ℤ`-independence plus membership
in `Λ` by pulling back along `B` to integer points
(`Commons.intCoords_linearIndependent_real`), exactly as in the flow case.

All declarations are Mathlib + Submission (GraysonLattice/FlowSubgroupBasis) + Commons.
-/

noncomputable section

open Set Module Real LinearSubspaces
open scoped BigOperators
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySimpa false
set_option maxHeartbeats 1200000

namespace Submission.GraysonLattice

open Submission.GraysonData

/-- A `ℤ`-basis of the full-rank lattice `Λ ≤ ℝᵈ`, indexed by `Fin d` (reindexed from
`Module.Free.chooseBasis`). -/
noncomputable def latticeZBasis {d : ℕ} (Λ : Submodule ℤ (E d)) [DiscreteTopology Λ]
    [IsZLattice ℝ Λ] (hΛfin : Module.finrank ℤ Λ = d) : Basis (Fin d) ℤ Λ :=
  (Module.Free.chooseBasis ℤ Λ).reindex (Fintype.equivFinOfCardEq (by
    rw [← Module.finrank_eq_card_basis (Module.Free.chooseBasis ℤ Λ), hΛfin]))

/-- The ambient coercion of the `ℤ`-basis of `Λ`. -/
abbrev latticeZBasisE {d : ℕ} (Λ : Submodule ℤ (E d)) [DiscreteTopology Λ]
    [IsZLattice ℝ Λ] (hΛfin : Module.finrank ℤ Λ = d) : Fin d → E d :=
  fun i => ((latticeZBasis (d := d) Λ hΛfin i : Λ) : E d)

/-- The ambient `ℤ`-basis vectors lie in `Λ`. -/
lemma latticeZBasisE_mem {d : ℕ} (Λ : Submodule ℤ (E d)) [DiscreteTopology Λ]
    [IsZLattice ℝ Λ] (hΛfin : Module.finrank ℤ Λ = d) (i : Fin d) :
    latticeZBasisE Λ hΛfin i ∈ (Λ : Set (E d)) := by
  dsimp [latticeZBasisE]
  exact (latticeZBasis Λ hΛfin i : Λ).2

/-- The ambient `ℤ`-basis is `ℤ`-linearly independent. -/
lemma latticeZBasisE_linearIndependent_ℤ {d : ℕ} (Λ : Submodule ℤ (E d)) [DiscreteTopology Λ]
    [IsZLattice ℝ Λ] (hΛfin : Module.finrank ℤ Λ = d) :
    LinearIndependent ℤ (latticeZBasisE (d := d) Λ hΛfin) := by
  classical
  have hliΛ : LinearIndependent ℤ (fun i : Fin d => (latticeZBasis Λ hΛfin i : Λ)) :=
    (latticeZBasis Λ hΛfin).linearIndependent
  have hmap : LinearIndependent ℤ (fun i : Fin d =>
      ((latticeZBasis Λ hΛfin i : Λ) : E d)) :=
    hliΛ.map' (Λ.subtype.restrictScalars ℤ) (Submodule.ker_subtype Λ)
  simpa [latticeZBasisE] using hmap

/-- The `ℤ`-span of the ambient `ℤ`-basis is the whole lattice `Λ`. -/
lemma span_latticeZBasisE {d : ℕ} (Λ : Submodule ℤ (E d)) [DiscreteTopology Λ]
    [IsZLattice ℝ Λ] (hΛfin : Module.finrank ℤ Λ = d) :
    Submodule.span ℤ (Set.range (latticeZBasisE (d := d) Λ hΛfin)) = Λ := by
  classical
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro x ⟨i, rfl⟩
    exact latticeZBasisE_mem Λ hΛfin i
  · intro x hx
    -- x ∈ Λ = the ℤ-span of the basis (inside Λ); lift to ambient
    let xΛ : Λ := ⟨x, hx⟩
    have hmem : xΛ ∈ Submodule.span ℤ (Set.range (latticeZBasis Λ hΛfin)) := by
      rw [(latticeZBasis Λ hΛfin).span_eq]
      trivial
    rw [Submodule.mem_span_range_iff_exists_fun (R := ℤ) (v := latticeZBasis Λ hΛfin)] at hmem
    rcases hmem with ⟨c, hc⟩
    have hxE : (∑ i : Fin d, c i • latticeZBasisE Λ hΛfin i) = x := by
      have hm := congrArg (fun z : Λ => (z : E d)) hc
      simpa [latticeZBasisE] using hm
    rw [← hxE]
    exact Submodule.sum_mem _ (fun i hi => Submodule.smul_mem _ _
      (Submodule.subset_span ⟨i, rfl⟩))

/-- The real span of the ambient `ℤ`-basis is the whole space (full-rankness). -/
lemma latticeZBasisE_spanReal_top {d : ℕ} (Λ : Submodule ℤ (E d)) [DiscreteTopology Λ]
    [IsZLattice ℝ Λ] (hΛfin : Module.finrank ℤ Λ = d) :
    Submodule.span ℝ (Set.range (latticeZBasisE (d := d) Λ hΛfin)) = ⊤ := by
  classical
  have htop : Submodule.span ℝ (Λ : Set (E d)) = ⊤ := by
    exact (inferInstance : IsZLattice ℝ Λ).span_top
  have hset : (Submodule.span ℤ (Set.range (latticeZBasisE (d := d) Λ hΛfin)) : Set (E d)) =
      (Λ : Set (E d)) := by
    exact congrArg (fun S : Submodule ℤ (E d) => (S : Set (E d)))
      (span_latticeZBasisE (d := d) Λ hΛfin)
  have htw : Submodule.span ℝ ((Submodule.span ℤ (Set.range (latticeZBasisE (d := d) Λ hΛfin))) :
        Set (E d)) =
      Submodule.span ℝ (Set.range (latticeZBasisE (d := d) Λ hΛfin)) :=
    Submodule.span_span_of_tower (R := ℤ) (S := ℝ) (M := E d)
      (s := Set.range (latticeZBasisE (d := d) Λ hΛfin))
  calc
    Submodule.span ℝ (Set.range (latticeZBasisE (d := d) Λ hΛfin))
        = Submodule.span ℝ ((Submodule.span ℤ (Set.range (latticeZBasisE (d := d) Λ hΛfin))) : Set (E d)) := htw.symm
    _ = Submodule.span ℝ (Λ : Set (E d)) := by rw [hset]
    _ = ⊤ := htop

/-- The ambient `ℤ`-basis of a full-rank lattice is an `ℝ`-basis of the ambient space. -/
lemma latticeZBasisE_linearIndependent_real {d : ℕ} (Λ : Submodule ℤ (E d))
    [DiscreteTopology Λ] [IsZLattice ℝ Λ] (hΛfin : Module.finrank ℤ Λ = d) :
    LinearIndependent ℝ (latticeZBasisE (d := d) Λ hΛfin) := by
  classical
  have hsp : ⊤ ≤ Submodule.span ℝ (Set.range (latticeZBasisE (d := d) Λ hΛfin)) := by
    rw [latticeZBasisE_spanReal_top Λ hΛfin]
  have hfinE : Module.finrank ℝ (E d) = d := by
    have hb := (EuclideanSpace.basisFun (Fin d) ℝ).toBasis
    simpa using (hb.finrank_eq (Fin d))
  exact linearIndependent_of_top_le_span_of_card_eq_finrank (R := ℝ) (M := E d)
    (b := latticeZBasisE (d := d) Λ hΛfin) hsp (by simp [hfinE])



/-- **Members of a full-rank lattice, `ℤ`-LI ⟹ `ℝ`-LI**: a `ℤ`-linearly independent
ambient family of members of `Λ` is `ℝ`-linearly independent.  Proof: the ambient
`ℤ`-basis of `Λ` is an `ℝ`-basis, so the basis-coordinate equivalence `T₀` sends `Λ`
onto the integer lattice `ℤᵈ`; pull the family back along `T₀` to an integer-coordinate
family (ℤ-LI by injectivity of `T₀`; `ℝ`-LI by the Commons integer-coordinate lemma),
and transfer back along the injective `ℝ`-linear map `T₀`. -/
lemma linearIndependent_real_of_mem_lattice {d n : ℕ} (Λ : Submodule ℤ (E d))
    [DiscreteTopology Λ] [IsZLattice ℝ Λ] (hΛfin : Module.finrank ℤ Λ = d)
    (u : Fin n → E d) (huΛ : ∀ r : Fin n, u r ∈ (Λ : Set (E d)))
    (hli : LinearIndependent ℤ u) : LinearIndependent ℝ u := by
  classical
  let std : Fin d → E d := fun i => (EuclideanSpace.basisFun (Fin d) ℝ i : E d)
  let bE : Fin d → E d := latticeZBasisE (d := d) Λ hΛfin
  let bR : Basis (Fin d) ℝ (E d) := Module.Basis.mk
    (latticeZBasisE_linearIndependent_real (d := d) Λ hΛfin) (by
      rw [latticeZBasisE_spanReal_top Λ hΛfin])
  have hbR : (fun i : Fin d => (bR i : E d)) = bE := by
    dsimp [bE, bR]
    exact Module.Basis.coe_mk (latticeZBasisE_linearIndependent_real (d := d) Λ hΛfin)
      (by rw [latticeZBasisE_spanReal_top Λ hΛfin])
  let T₀ : E d ≃ₗ[ℝ] E d := (EuclideanSpace.basisFun (Fin d) ℝ).toBasis.equiv bR (Equiv.refl (Fin d))
  have hT : ∀ i : Fin d, T₀ (std i) = bE i := by
    intro i
    have h := Module.Basis.equiv_apply (EuclideanSpace.basisFun (Fin d) ℝ).toBasis i bR
      (Equiv.refl (Fin d))
    simpa [T₀, hbR, std] using h
  let f : E d →ₗ[ℤ] E d := (T₀ : E d →ₗ[ℝ] E d).restrictScalars ℤ
  -- the image of the standard integer lattice is the ℤ-span of the lattice basis
  have himgset : f '' (Set.range std) = Set.range bE := by
    ext x
    constructor
    · rintro ⟨y, ⟨j, rfl⟩, hy⟩
      refine ⟨j, ?_⟩
      exact (show f (std j) = bE j from by simpa [f] using (hT j)).symm.trans hy
    · rintro ⟨j, rfl⟩
      refine ⟨std j, ⟨j, rfl⟩, ?_⟩
      simpa [f] using (hT j)
  have hΛim : (Submodule.span ℤ (Set.range std)).map f = Submodule.span ℤ (Set.range bE) := by
    dsimp [f]
    rw [Submodule.map_span]
    rw [himgset]
  -- each member has an integer-coordinate preimage
  have hwmem : ∀ r : Fin n, ∃ z : E d,
      z ∈ Submodule.span ℤ (Set.range std) ∧ f z = u r := by
    intro r
    have hu : u r ∈ Submodule.span ℤ (Set.range bE) := by
      change u r ∈ Submodule.span ℤ (Set.range (latticeZBasisE (d := d) Λ hΛfin))
      rw [span_latticeZBasisE (d := d) Λ hΛfin]
      exact huΛ r
    have hmem' : u r ∈ (Submodule.span ℤ (Set.range std)).map f := by
      rw [← hΛim] at hu
      exact hu
    exact (Submodule.mem_map).mp hmem'
  let z : Fin n → E d := fun r => Classical.choose (hwmem r)
  have hzmem : ∀ r : Fin n, z r ∈ Submodule.span ℤ (Set.range std) := by
    intro r
    exact (Classical.choose_spec (hwmem r)).1
  have hzf : ∀ r : Fin n, f (z r) = u r := by
    intro r
    exact (Classical.choose_spec (hwmem r)).2
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
    change z r ∈ Submodule.span ℤ (Set.range (fun j : Fin d => (EuclideanSpace.basisFun (Fin d) ℝ j : E d)))
    simpa [std] using hzmem r
  have hzliℝ : LinearIndependent ℝ z :=
    Commons.Analysis.InnerProductSpace.intCoords_linearIndependent_real (u := z) hzspan hzli
  -- transfer back along the injective real linear map T₀
  have hlinℝ : LinearIndependent ℝ (fun r : Fin n => T₀ (z r)) := by
    exact linearIndependent_comp_injective (f := (T₀ : E d →ₗ[ℝ] E d)) T₀.injective z hzliℝ
  have hzeq : (fun r : Fin n => T₀ (z r)) = u := by
    funext r
    have h := hzf r
    simpa [f] using h
  simpa [hzeq] using hlinℝ

/-- **Lattice-subgroup basis representation**: for a full-rank lattice `Λ` and a subgroup
`W ≤ Λ` (`W ≠ ⊥`), there is an `ℝ`-independent member family `cW : Fin n → Λ` of size
`0 < n` with `W = span ℤ (range cW)` — the coerced `ℤ`-basis of `W` extracted by the PID
structure of `Λ` (`Submodule.basisOfPidOfLESpan` over the ambient `ℤ`-basis of `Λ`). -/
lemma exists_basis_of_le_lattice {d : ℕ} (Λ : Submodule ℤ (E d)) [DiscreteTopology Λ]
    [IsZLattice ℝ Λ] (hΛfin : Module.finrank ℤ Λ = d) (W : Submodule ℤ (E d))
    (hWle : W ≤ Λ) (hW0 : W ≠ ⊥) :
    ∃ n : ℕ, 0 < n ∧ ∃ cW : Fin n → E d,
      LinearIndependent ℝ cW ∧
      (∀ r : Fin n, cW r ∈ (Λ : Set (E d))) ∧
      W = Submodule.span ℤ (Set.range cW) := by
  classical
  let bE : Fin d → E d := latticeZBasisE (d := d) Λ hΛfin
  have hLI : LinearIndependent ℤ bE := by
    dsimp [bE]
    exact latticeZBasisE_linearIndependent_ℤ (d := d) Λ hΛfin
  have hle : W ≤ Submodule.span ℤ (Set.range bE) := by
    dsimp [bE]
    rw [span_latticeZBasisE (d := d) Λ hΛfin]
    exact hWle
  obtain ⟨n, bW⟩ := Submodule.basisOfPidOfLESpan (R := ℤ) (b := bE) hLI hle
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
  · -- ℝ-independence: membership in Λ + ℤ-independence (transfer lemma)
    exact linearIndependent_real_of_mem_lattice (d := d) Λ hΛfin cW (by
      intro r
      exact hWle ((bW r : W).2)) hzli
  · intro r
    exact hWle ((bW r : W).2)

/-- **Presentation lemma**: every discrete subgroup `W` of a full-rank lattice `Λ ≤ ℝᵈ`
(`W ≠ ⊥`) is the `ℤ`-span of an `ℝ`-independent member family of size exactly
`subDim W`. -/
lemma exists_basis_family_of_le_lattice {d : ℕ} (Λ : Submodule ℤ (E d)) [DiscreteTopology Λ]
    [IsZLattice ℝ Λ] (hΛfin : Module.finrank ℤ Λ = d) (W : Submodule ℤ (E d))
    (hWle : W ≤ Λ) (hW0 : W ≠ ⊥) :
    ∃ cW : Fin (subDim W) → E d,
      LinearIndependent ℝ cW ∧
      (∀ r : Fin (subDim W), cW r ∈ (Λ : Set (E d))) ∧
      W = Submodule.span ℤ (Set.range cW) := by
  classical
  rcases exists_basis_of_le_lattice (d := d) Λ hΛfin W hWle hW0 with ⟨n, hn0, cW0, hli, hmem, hW_eq⟩
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
