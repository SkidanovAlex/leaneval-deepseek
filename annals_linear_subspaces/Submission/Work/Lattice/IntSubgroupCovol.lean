import Mathlib
import Submission.Work.Lattice.IsometryLatticeBounded
import Submission.Work.Lattice.LatticeDataEndpoints
import Submission.Commons.Analysis.InnerProductSpace.intCoords_linearIndependent_real

/-!
# P1-general (a), completion: every subgroup of `ℤᵈ` has covolume ≥ 1

This module closes the sub-task recorded in the ROADMAP (session 92 continued §8) for the
base lattice `ℤᵈ`:

    `∀ W ≤ stdIntLattice d :  1 ≤ latticeCovol W`

**Key observation** (removes the rank-identity sub-task): it is unnecessary to know that
the `ℤ`-rank `n` of `W` equals `subDim W = j`.  For an arbitrary subgroup `W ≤ ℤᵈ`, the PID
basis extraction `Submodule.basisOfPidOfLESpan` yields a `ℤ`-basis `bW : Basis (Fin n) ℤ W`
for *some* `n`; writing `cW : Fin n → ℝᵈ` for its coercion, one has `W = span ℤ (range cW)`
and `latticeCovol W = ‖ιMulti ℝ n cW‖` (covol-wedge bridge); the `cW` lie in `ℤᵈ` and are
`ℤ`-independent, hence `ℝ`-independent (fleet L75
`Commons.Analysis.InnerProductSpace.intCoords_linearIndependent_real`), so the integer-wedge
lower bound (`intWedge_norm_ge_one`, via `intCoords_span_covol_ge_one`) gives
`1 ≤ latticeCovol W`.  The `BddBelow` corollary for the per-rank data of `ℤᵈ` (and, by
isometry transport, of every §3-route lattice `g(ℤᵈ)`) is recorded in the companion module
`Submission.Work.Lattice.LatticePolygon` (see `bddBelow_rankDataSet_stdIntLattice`).

All declarations are Mathlib + Submission.GraysonLattice/IsometryLatticeBounded + Commons.
-/

noncomputable section

open Set Module Real
open scoped BigOperators RealInnerProductSpace
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1200000

namespace Submission.GraysonLattice

open Submission.GraysonData

/-- An `ℝ`-linearly independent family in a real normed space is `ℤ`-linearly independent:
integer relations are real relations. -/
lemma li_int_of_li_real {d : ℕ} {ι : Type*} [Fintype ι] (f : ι → E d)
    (h : LinearIndependent ℝ f) : LinearIndependent ℤ f := by
  exact LinearIndependent.restrict_scalars (R := ℤ) (K := ℝ) (M := E d) (v := f)
    (by
      intro a b hab
      have hab' : (a : ℝ) = (b : ℝ) := by simpa [zsmul_eq_mul] using hab
      exact_mod_cast hab') h

/-- The standard coordinate family of `ℝᵈ` is `ℤ`-independent (it is `ℝ`-independent). -/
lemma stdVec_linearIndependent_ℤ {d : ℕ} : LinearIndependent ℤ (fun t : Fin d => stdVec d t) := by
  have hliℝ : LinearIndependent ℝ (fun t : Fin d => EuclideanSpace.basisFun (Fin d) ℝ t) :=
    (EuclideanSpace.basisFun (Fin d) ℝ).toBasis.linearIndependent
  simpa [stdVec] using
    (li_int_of_li_real (fun t : Fin d => EuclideanSpace.basisFun (Fin d) ℝ t) hliℝ)

/-- `stdIntLattice d` equals the `ℤ`-span of the standard `OrthonormalBasis` vectors (the
`basisFun` family of the Commons integer-coordinate lemmas). -/
lemma stdIntLattice_eq_span_basisFun {d : ℕ} :
    stdIntLattice d = Submodule.span ℤ (Set.range (EuclideanSpace.basisFun (Fin d) ℝ)) := by
  dsimp [stdIntLattice, stdVec]

/-- The `ℤ`-basis of a subgroup `W ≤ ℤᵈ`, as an `ℝ`-independent ambient family with integer
coordinates, spanning `W`. -/
lemma exists_basis_of_le_intLattice {d : ℕ} (W : Submodule ℤ (E d)) (hWle : W ≤ stdIntLattice d)
    (hW0 : W ≠ ⊥) :
    ∃ n : ℕ, 0 < n ∧ ∃ cW : Fin n → E d,
      LinearIndependent ℝ cW ∧
      (∀ r : Fin n, cW r ∈ stdIntLattice d) ∧
      W = Submodule.span ℤ (Set.range cW) := by
  classical
  have hLI : LinearIndependent ℤ (fun t : Fin d => stdVec d t) := stdVec_linearIndependent_ℤ (d := d)
  have hle : W ≤ Submodule.span ℤ (Set.range (fun t : Fin d => stdVec d t)) := by
    simpa [stdIntLattice] using hWle
  obtain ⟨n, bW⟩ := Submodule.basisOfPidOfLESpan (R := ℤ) (b := fun t : Fin d => stdVec d t) hLI hle
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
  -- W = ℤ-span of the coerced basis
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
  · -- ℝ-independence: membership in ℤᵈ + ℤ-independence (fleet L75)
    exact Commons.Analysis.InnerProductSpace.intCoords_linearIndependent_real
      (u := cW)
      (by
        intro r
        have hm : cW r ∈ stdIntLattice d := by
          simpa [cW] using (hWle ((bW r : W).2))
        rwa [stdIntLattice_eq_span_basisFun] at hm)
      hzli
  · intro r
    exact hWle ((bW r : W).2)

/-- **Every subgroup of the integer lattice has covolume ≥ 1**: for `W ≤ ℤᵈ`,
`latticeCovol W ≥ 1` (equivalently, its log-covolume is `≥ 0`). -/
theorem subgroup_covol_ge_one_of_le_intLattice {d : ℕ} (W : Submodule ℤ (E d))
    (hWle : W ≤ stdIntLattice d) :
    (1 : ℝ) ≤ latticeCovol W := by
  by_cases hW0 : W = ⊥
  · subst W
    rw [latticeCovol_bot]
  · rcases exists_basis_of_le_intLattice W hWle hW0 with ⟨n, hn0, cW, hliℝ, hmem, hW_eq⟩
    have hcov : latticeCovol W = ‖exteriorPower.ιMulti ℝ n cW‖ := by
      rw [hW_eq]
      exact latticeCovol_span (d := d) (r := n) hn0 cW hliℝ
    have huz : ∀ r : Fin n, ∀ t : Fin d, ∃ z : ℤ, cW r t = z := by
      intro r t
      exact coord_mem_stdIntLattice (hmem r) t
    have hw : (1 : ℝ) ≤ ‖exteriorPower.ιMulti ℝ n cW‖ :=
      intCoords_ιMulti_norm_ge_one (d := d) (j := n) (by omega) cW huz hliℝ
    rwa [hcov]

/-- **Log form**: every subgroup of the integer lattice has `0 ≤ log covol(W)`. -/
theorem logCovol_nonneg_of_le_intLattice {d : ℕ} (W : Submodule ℤ (E d))
    (hWle : W ≤ stdIntLattice d) :
    (0 : ℝ) ≤ Real.log (latticeCovol W) := by
  have hge : (1 : ℝ) ≤ latticeCovol W := subgroup_covol_ge_one_of_le_intLattice W hWle
  have hpos : 0 < latticeCovol W := lt_of_lt_of_le zero_lt_one hge
  calc
    (0 : ℝ) = Real.log 1 := by simp
    _ ≤ Real.log (latticeCovol W) := Real.log_le_log (by norm_num) hge

end Submission.GraysonLattice

end
