import Mathlib
import Submission.Work.Whitney.cruxDefs
import Submission.Work.Gen.splitCruxConstant_eq_one
import Submission.Work.Gen.lineSumCore_top_chern
import Submission.Work.Kunneth.kunnethCP
import Submission.Work.LerayHirsch.FibreRestrict

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option linter.style.haveILetI false

/-!
# A model on which the crux `c_{N-1}(lineSumCore N M) = eSym N M (N-1)` holds non-trivially

The lemma `Work.Gen.splitCruxConstant_eq_one` proves that the universal constant of the split crux
is `1` by testing on the model

`B = ℂP^{N-1}`,   `M = (ℓ, ℓ, …, ℓ, ε)`   (`N-1` copies of the tautological line bundle plus one
trivial one),

where the crux is provable because of the *trivial* summand: both sides collapse to `ζ^{N-1}`
(`Work.Gen.splitCrux_chernClass_lineSumCore_snoc_trivial` +
`Work.Gen.splitCrux_chernClass_lineSumCore_const` for the left-hand side, and the `eSym` analogues
for the right-hand side).

This module *repackages that model* as the existence statement `Work.Whitney.cruxModelPins`: the
model is a compact path-connected paracompact Hausdorff space, the class `ζ^{N-1}` is a *non-torsion*
class (`Work.Kunneth.smul_zetaPow_injective`), and `H⁰(B;ℤ) = ℤ⟨1⟩`
(`Work.Cohomology.exists_smul_oneH`).

The only new topological inputs are that `ProjSpace (trivCore (m+1))` is compact (it is
homeomorphic to `ℙ ℂ (ℂ^{m+1})`, which is a quotient of the unit sphere) and path connected (it is a
quotient of the punctured space `ℂ^{m+1}∖0`, which is a continuous image of the path connected
punctured Euclidean space).
-/

namespace Work.Whitney

open scoped LinearAlgebra.Projectivization

theorem cruxModelPins (N : ℕ) (hN : 2 ≤ N) :
    ∃ (B₀ : Type) (_ : TopologicalSpace B₀) (_ : ParacompactSpace B₀) (_ : T2Space B₀)
      (_ : CompactSpace B₀) (_ : PathConnectedSpace B₀)
      (ι₀ : Type) (_ : Fintype ι₀)
      (M₀ : Fin N → VectorBundleCore ℂ B₀ (EuclideanSpace ℂ (Fin 1)) ι₀),
      Work.Thom.chernClass N (N - 1) (Work.LerayHirsch.lineSumCore N M₀)
          = Work.Gen.eSym N M₀ (N - 1)
      ∧ (∀ k : ℤ, k • Work.Gen.eSym N M₀ (N - 1) = 0 → k = 0)
      ∧ (∀ x : Work.Thom.Coh ℤ 0 B₀, ∃ k : ℤ,
            x = k • Work.Cohomology.oneH ℤ (Work.Whitney.ssB B₀)) := by
  obtain ⟨m, rfl⟩ : ∃ m, N = m + 1 := ⟨N - 1, (Nat.succ_pred_eq_of_pos (by omega)).symm⟩
  -- the model base: `ℂP^m = P(ε^{m+1})`
  let Z : VectorBundleCore ℂ PUnit (EuclideanSpace ℂ (Fin (m+1))) PUnit :=
    Work.LerayHirsch.trivCore (m+1)
  let B : Type := Work.LerayHirsch.ProjSpace Z
  let ι : Type := PUnit × Fin (m+1)
  haveI hpar : ParacompactSpace B := Work.LerayHirsch.paracompactSpace_projSpace Z
  haveI ht2 : T2Space B := Work.LerayHirsch.t2Space_projSpace Z
  -- compactness and path connectedness of the model base
  haveI hcompProj : CompactSpace (ℙ ℂ (EuclideanSpace ℂ (Fin (m+1)))) :=
    Work.LerayHirsch.compactSpace_modelProjectivization (m+1)
  have hrank : 1 < Module.rank ℝ (EuclideanSpace ℂ (Fin (m+1))) := by
    rw [← Module.finrank_eq_rank]
    have h : Module.finrank ℝ (EuclideanSpace ℂ (Fin (m+1))) = 2 * (m+1) := by
      have h2 := ((WithLp.linearEquiv 2 ℂ (Fin (m+1) → ℂ)).restrictScalars ℝ).finrank_eq
      rw [h2]
      exact Work.Projective.finrank_real_fin_complex (m+1)
    rw [h, ← Nat.cast_one, Nat.cast_lt]
    omega
  haveI hpcE : PathConnectedSpace {v : EuclideanSpace ℂ (Fin (m+1)) // v ≠ 0} :=
    (isPathConnected_iff_pathConnectedSpace (F := ({0} : Set (EuclideanSpace ℂ (Fin (m+1))))ᶜ)).mp
      (by simpa using isPathConnected_compl_singleton_of_one_lt_rank hrank 0)
  haveI hpcProj : PathConnectedSpace (ℙ ℂ (EuclideanSpace ℂ (Fin (m+1)))) :=
    (Work.LerayHirsch.surjective_mkP (m+1)).pathConnectedSpace
      (Work.LerayHirsch.continuous_mkP (m+1))
  obtain ⟨e⟩ := Work.LerayHirsch.nonempty_homeo_projSpace_trivial (m+1) PUnit
  haveI hcompB : CompactSpace B := e.symm.compactSpace
  haveI hpcB : PathConnectedSpace B := e.symm.surjective.pathConnectedSpace e.symm.continuous
  -- the model family: `N-1` copies of the tautological line bundle and one trivial bundle
  let L : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin 1)) ι := Work.LerayHirsch.tautLine Z
  let M : Fin (m+1) → VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin 1)) ι :=
    Fin.snoc (α := fun _ : Fin (m+1) =>
        VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin 1)) ι)
      (fun _ : Fin m => L) (trivialVectorBundleCore ℂ B (EuclideanSpace ℂ (Fin 1)) ι)
  -- both sides of the crux for the model compute to `ζ^m`
  have hzeta : Work.Kunneth.pow2 (Work.Thom.chernClass 1 1 L) m
      = Work.LerayHirsch.zetaPow Z m := by
    have hc : Work.Thom.chernClass 1 1 L = Work.LerayHirsch.zeta Z := by
      rw [Work.LerayHirsch.zeta_def, Work.Thom.cohTransport_rfl]
    rw [hc, Work.Kunneth.pow2_zeta]
  have hLHS : Work.Thom.chernClass (m + 1) ((m + 1) - 1)
      (Work.LerayHirsch.lineSumCore (m + 1) M) = Work.LerayHirsch.zetaPow Z m :=
    (Work.Gen.splitCrux_chernClass_lineSumCore_snoc_trivial (f := fun _ : Fin m => L)
        ((m + 1) - 1)).trans
      ((Work.Gen.splitCrux_chernClass_lineSumCore_const L m).trans hzeta)
  have hRHS : Work.Gen.eSym (m + 1) M ((m + 1) - 1) = Work.LerayHirsch.zetaPow Z m :=
    (Work.Gen.splitCrux_eSym_snoc_trivial (f := fun _ : Fin m => L) ((m + 1) - 1)).trans
      ((Work.Gen.splitCrux_eSym_const L m).trans hzeta)
  refine ⟨B, inferInstance, hpar, ht2, hcompB, hpcB, ι, inferInstance, M, ?_, ?_, ?_⟩
  · -- the crux holds for the model
    exact hLHS.trans hRHS.symm
  · -- `ζ^m` is not a torsion class
    intro k hk
    rw [hRHS] at hk
    exact Work.Kunneth.smul_zetaPow_injective m m le_rfl k 0 (by simpa using hk)
  · -- `H⁰` of the model base is generated by the unit class
    intro x
    exact Work.Cohomology.exists_smul_oneH (TopCat.of B) x

end Work.Whitney
