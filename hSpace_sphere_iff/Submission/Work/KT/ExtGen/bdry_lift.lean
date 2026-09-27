import Mathlib
import Submission.Work.KT.ExtGen.Triple
import Submission.Work.KT.ExtGen.TripleBdry
import Submission.Work.KT.ExtGen.bdry_aux
import Submission.Work.KT.ExtGen.bdryRestZ_eq
import Submission.Work.KT.ExtGen.bdryRestW_eq
import Submission.Work.KT.ExtGen.bdryRestV_eq
import Submission.Work.KT.ExtGen.bdryCornerW_eq_V
import Submission.Work.KT.ExtGen.bdryCornerZ_eq_V

namespace Work.KT.ExtGen

noncomputable section

set_option maxHeartbeats 10000000
set_option synthInstance.maxHeartbeats 800000

/-- With `k = 0`, the reindexed block matrix `fromBlocks u 0 0 1` is `u` again. -/
lemma reindex_fromBlocks_zero {A : Type} [CommRing A] (n : ℕ) (u : Matrix (Fin n) (Fin n) A) :
    Matrix.reindex (finSumFinEquiv (m := n) (n := 0)) (finSumFinEquiv (m := n) (n := 0))
      (Matrix.fromBlocks u (0 : Matrix (Fin n) (Fin 0) A) (0 : Matrix (Fin 0) (Fin n) A)
        (1 : Matrix (Fin 0) (Fin 0) A)) = u := by
  ext i j
  have h1 : (finSumFinEquiv (m := n) (n := 0)).symm i = Sum.inl i := by
    rw [Equiv.symm_apply_eq, finSumFinEquiv_apply_left]
    exact Fin.ext rfl
  have h2 : (finSumFinEquiv (m := n) (n := 0)).symm j = Sum.inl j := by
    rw [Equiv.symm_apply_eq, finSumFinEquiv_apply_left]
    exact Fin.ext rfl
  rw [Matrix.reindex_apply, Matrix.submatrix_apply, h1, h2]
  simp [Matrix.fromBlocks]

/-- Invertible matrices over `bdryAlg` (the fibre product of the three chart algebras
`prodAlg W Z`, `prodAlg V Z`, `prodAlg V W` over their pairwise common `Kpair` restrictions, see
`Submission.Work.KT.ExtGen.TripleBdry`) lift along `bdryProj : tripleAlg V W Z →ₐ[ℂ] bdryAlg` to
invertible matrices over `tripleAlg V W Z`, in fact with `k = 0`.  Writing `u = (u₁,u₂,u₃)` for the
three components, the lift is
`V(v,w,z) = u₁(w,z)·u₁₂(z)⁻¹·u₂(v,z)·u₂₃(v)⁻¹·u₀·u₁₃(w)⁻¹·u₃(v,w)`,
with `u₁₂ ∈ Mₙ(Kpair Z)`, `u₁₃ ∈ Mₙ(Kpair W)`, `u₂₃ ∈ Mₙ(Kpair V)` the pairwise restrictions and
`u₀` their common corner value (`augPair V v₀ u₂₃`). -/
theorem bdry_lift (V W Z : Type) [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z]
    (v0 : Ball V) (hv0 : v0 ∈ bdry V) (w0 : Ball W) (hw0 : w0 ∈ bdry W)
    (z0 : Ball Z) (hz0 : z0 ∈ bdry Z)
    (n : ℕ) (u : Matrix (Fin n) (Fin n) (bdryAlg V W Z v0 hv0 w0 hw0 z0 hz0)) (hu : IsUnit u) :
    ∃ (k : ℕ) (v : Matrix (Fin (n + k)) (Fin (n + k)) (tripleAlg V W Z)), IsUnit v ∧
      v.map (bdryProj V W Z v0 hv0 w0 hw0 z0 hz0)
        = Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks u 0 0 1) := by
  -- the fibre-product conditions
  have hRZ : bdryRestZ V W Z v0 hv0 w0 hw0 z0 hz0
      = (sliceW V Z v0 hv0).comp (bdrySnd V W Z v0 hv0 w0 hw0 z0 hz0) :=
    bdryRestZ_eq V W Z v0 hv0 w0 hw0 z0 hz0
  have hRW : bdryRestW V W Z v0 hv0 w0 hw0 z0 hz0
      = (sliceW V W v0 hv0).comp (bdryTrd V W Z v0 hv0 w0 hw0 z0 hz0) :=
    bdryRestW_eq V W Z v0 hv0 w0 hw0 z0 hz0
  have hRV : bdryRestV V W Z v0 hv0 w0 hw0 z0 hz0
      = (sliceV V W w0 hw0).comp (bdryTrd V W Z v0 hv0 w0 hw0 z0 hz0) :=
    bdryRestV_eq V W Z v0 hv0 w0 hw0 z0 hz0
  have hCW : bdryCornerW V W Z v0 hv0 w0 hw0 z0 hz0
      = bdryCornerV V W Z v0 hv0 w0 hw0 z0 hz0 :=
    bdryCornerW_eq_V V W Z v0 hv0 w0 hw0 z0 hz0
  have hCZ : bdryCornerZ V W Z v0 hv0 w0 hw0 z0 hz0
      = bdryCornerV V W Z v0 hv0 w0 hw0 z0 hz0 :=
    bdryCornerZ_eq_V V W Z v0 hv0 w0 hw0 z0 hz0
  -- the unit of `u`, its inverse, the three slices of `bdryProj` and the three charts
  let U : (Matrix (Fin n) (Fin n) (bdryAlg V W Z v0 hv0 w0 hw0 z0 hz0))ˣ := hu.unit
  let Ui : (Matrix (Fin n) (Fin n) (bdryAlg V W Z v0 hv0 w0 hw0 z0 hz0))ˣ := U⁻¹
  have hU : (↑U : Matrix (Fin n) (Fin n) (bdryAlg V W Z v0 hv0 w0 hw0 z0 hz0)) = u := hu.unit_spec
  set BF : bdryAlg V W Z v0 hv0 w0 hw0 z0 hz0 →ₐ[ℂ] prodAlg W Z :=
    bdryFst V W Z v0 hv0 w0 hw0 z0 hz0 with hBF
  set BS : bdryAlg V W Z v0 hv0 w0 hw0 z0 hz0 →ₐ[ℂ] prodAlg V Z :=
    bdrySnd V W Z v0 hv0 w0 hw0 z0 hz0 with hBS
  set BT : bdryAlg V W Z v0 hv0 w0 hw0 z0 hz0 →ₐ[ℂ] prodAlg V W :=
    bdryTrd V W Z v0 hv0 w0 hw0 z0 hz0 with hBT
  -- the seven chart homomorphisms `bdryAlg → tripleAlg` carrying the seven factors
  set ψ1 : bdryAlg V W Z v0 hv0 w0 hw0 z0 hz0 →ₐ[ℂ] tripleAlg V W Z :=
    (tripleInclWZ V W Z).comp BF with hψ1
  set ψ2 : bdryAlg V W Z v0 hv0 w0 hw0 z0 hz0 →ₐ[ℂ] tripleAlg V W Z :=
    (triplePullZ V W Z).comp (bdryRestZ V W Z v0 hv0 w0 hw0 z0 hz0) with hψ2
  set ψ3 : bdryAlg V W Z v0 hv0 w0 hw0 z0 hz0 →ₐ[ℂ] tripleAlg V W Z :=
    (pullProjVZ V W Z).comp BS with hψ3
  set ψ4 : bdryAlg V W Z v0 hv0 w0 hw0 z0 hz0 →ₐ[ℂ] tripleAlg V W Z :=
    (triplePullV V W Z).comp (bdryRestV V W Z v0 hv0 w0 hw0 z0 hz0) with hψ4
  set ψ5 : bdryAlg V W Z v0 hv0 w0 hw0 z0 hz0 →ₐ[ℂ] tripleAlg V W Z :=
    (Algebra.ofId ℂ (tripleAlg V W Z)).comp (bdryCornerV V W Z v0 hv0 w0 hw0 z0 hz0) with hψ5
  set ψ6 : bdryAlg V W Z v0 hv0 w0 hw0 z0 hz0 →ₐ[ℂ] tripleAlg V W Z :=
    (triplePullW V W Z).comp (bdryRestW V W Z v0 hv0 w0 hw0 z0 hz0) with hψ6
  set ψ7 : bdryAlg V W Z v0 hv0 w0 hw0 z0 hz0 →ₐ[ℂ] tripleAlg V W Z :=
    (tripleInclPW V W Z).comp BT with hψ7
  -- the seven factors, as matrix units over `tripleAlg`
  let UA1 : (Matrix (Fin n) (Fin n) (tripleAlg V W Z))ˣ := matUnitMap ψ1 U
  let UA2 : (Matrix (Fin n) (Fin n) (tripleAlg V W Z))ˣ := matUnitMap ψ2 Ui
  let UA3 : (Matrix (Fin n) (Fin n) (tripleAlg V W Z))ˣ := matUnitMap ψ3 U
  let UA4 : (Matrix (Fin n) (Fin n) (tripleAlg V W Z))ˣ := matUnitMap ψ4 Ui
  let UA5 : (Matrix (Fin n) (Fin n) (tripleAlg V W Z))ˣ := matUnitMap ψ5 U
  let UA6 : (Matrix (Fin n) (Fin n) (tripleAlg V W Z))ˣ := matUnitMap ψ6 Ui
  let UA7 : (Matrix (Fin n) (Fin n) (tripleAlg V W Z))ˣ := matUnitMap ψ7 U
  let VU : (Matrix (Fin n) (Fin n) (tripleAlg V W Z))ˣ := UA1 * UA2 * UA3 * UA4 * UA5 * UA6 * UA7
  let Vt : Matrix (Fin n) (Fin n) (tripleAlg V W Z) := ↑VU
  have hVunit : IsUnit Vt := ⟨VU, rfl⟩
  have hVt : Vt = ↑VU := rfl
  -- the images of the seven chart homs under the `v₀`-slice
  set χV : bdryAlg V W Z v0 hv0 w0 hw0 z0 hz0 →ₐ[ℂ] prodAlg W Z :=
    (pullSnd W Z).comp (bdryRestZ V W Z v0 hv0 w0 hw0 z0 hz0) with hχV
  set ρV : bdryAlg V W Z v0 hv0 w0 hw0 z0 hz0 →ₐ[ℂ] prodAlg W Z :=
    (Algebra.ofId ℂ (prodAlg W Z)).comp (bdryCornerV V W Z v0 hv0 w0 hw0 z0 hz0) with hρV
  set ϑV : bdryAlg V W Z v0 hv0 w0 hw0 z0 hz0 →ₐ[ℂ] prodAlg W Z :=
    (pullFst W Z).comp (bdryRestW V W Z v0 hv0 w0 hw0 z0 hz0) with hϑV
  have e1 : (sliceV0 V W Z v0 hv0).comp ψ1 = BF := by
    rw [hBF, hψ1, ← AlgHom.comp_assoc, sliceV0_comp_tripleInclWZ, AlgHom.id_comp]
  have e2 : (sliceV0 V W Z v0 hv0).comp ψ2 = χV := by
    rw [hχV, hψ2, ← AlgHom.comp_assoc, sliceV0_comp_triplePullZ]
  have e3 : (sliceV0 V W Z v0 hv0).comp ψ3 = χV := by
    rw [hχV, hψ3, ← AlgHom.comp_assoc, sliceV0_comp_pullProjVZ, AlgHom.comp_assoc, ← hRZ]
  have e4 : (sliceV0 V W Z v0 hv0).comp ψ4 = ρV := by
    rw [hρV, hψ4, ← AlgHom.comp_assoc, sliceV0_comp_triplePullV, AlgHom.comp_assoc]
    rfl
  have e5 : (sliceV0 V W Z v0 hv0).comp ψ5 = ρV := by
    rw [hρV, hψ5, ← AlgHom.comp_assoc, sliceV0_comp_algebraMap]
  have e6 : (sliceV0 V W Z v0 hv0).comp ψ6 = ϑV := by
    rw [hϑV, hψ6, ← AlgHom.comp_assoc, sliceV0_comp_triplePullW]
  have e7 : (sliceV0 V W Z v0 hv0).comp ψ7 = ϑV := by
    rw [hϑV, hψ7, ← AlgHom.comp_assoc, sliceV0_comp_tripleInclPW, AlgHom.comp_assoc, ← hRW]
  -- the lift restricts to `u₁` on the `v₀`-slice
  have keyV : Vt.map ⇑(sliceV0 V W Z v0 hv0) = u.map ⇑BF := by
    have t1 : matUnitMap (sliceV0 V W Z v0 hv0) UA1 = matUnitMap BF U := by
      rw [show UA1 = matUnitMap ψ1 U from rfl, matUnitMap_comp, e1]
    have t2 : matUnitMap (sliceV0 V W Z v0 hv0) UA2 = (matUnitMap χV U)⁻¹ := by
      rw [show UA2 = matUnitMap ψ2 Ui from rfl, show Ui = U⁻¹ from rfl, matUnitMap_comp, e2,
        map_inv]
    have t3 : matUnitMap (sliceV0 V W Z v0 hv0) UA3 = matUnitMap χV U := by
      rw [show UA3 = matUnitMap ψ3 U from rfl, matUnitMap_comp, e3]
    have t4 : matUnitMap (sliceV0 V W Z v0 hv0) UA4 = (matUnitMap ρV U)⁻¹ := by
      rw [show UA4 = matUnitMap ψ4 Ui from rfl, show Ui = U⁻¹ from rfl, matUnitMap_comp, e4,
        map_inv]
    have t5 : matUnitMap (sliceV0 V W Z v0 hv0) UA5 = matUnitMap ρV U := by
      rw [show UA5 = matUnitMap ψ5 U from rfl, matUnitMap_comp, e5]
    have t6 : matUnitMap (sliceV0 V W Z v0 hv0) UA6 = (matUnitMap ϑV U)⁻¹ := by
      rw [show UA6 = matUnitMap ψ6 Ui from rfl, show Ui = U⁻¹ from rfl, matUnitMap_comp, e6,
        map_inv]
    have t7 : matUnitMap (sliceV0 V W Z v0 hv0) UA7 = matUnitMap ϑV U := by
      rw [show UA7 = matUnitMap ψ7 U from rfl, matUnitMap_comp, e7]
    have hkey : matUnitMap (sliceV0 V W Z v0 hv0) VU = matUnitMap BF U := by
      rw [show VU = UA1 * UA2 * UA3 * UA4 * UA5 * UA6 * UA7 from rfl]
      simp only [map_mul]
      rw [t1, t2, t3, t4, t5, t6, t7]
      exact mul_tele_a (inv_mul_cancel (matUnitMap χV U)) (inv_mul_cancel (matUnitMap ρV U))
        (inv_mul_cancel (matUnitMap ϑV U))
    have h1 : Vt.map ⇑(sliceV0 V W Z v0 hv0)
        = ↑(matUnitMap (sliceV0 V W Z v0 hv0) VU) := rfl
    rw [h1, hkey, matUnitMap_apply]
    exact congrArg (fun M => M.map ⇑BF) hU
  -- the images of the seven chart homs under the `w₀`-slice
  set χW : bdryAlg V W Z v0 hv0 w0 hw0 z0 hz0 →ₐ[ℂ] prodAlg V Z :=
    (pullSnd V Z).comp (bdryRestZ V W Z v0 hv0 w0 hw0 z0 hz0) with hχW
  set ρW : bdryAlg V W Z v0 hv0 w0 hw0 z0 hz0 →ₐ[ℂ] prodAlg V Z :=
    (pullFst V Z).comp (bdryRestV V W Z v0 hv0 w0 hw0 z0 hz0) with hρW
  set ςW : bdryAlg V W Z v0 hv0 w0 hw0 z0 hz0 →ₐ[ℂ] prodAlg V Z :=
    (Algebra.ofId ℂ (prodAlg V Z)).comp (bdryCornerV V W Z v0 hv0 w0 hw0 z0 hz0) with hςW
  have f1 : (sliceW0 V W Z w0 hw0).comp ψ1 = χW := by
    rw [hχW, hψ1, ← AlgHom.comp_assoc, sliceW0_comp_tripleInclWZ, AlgHom.comp_assoc]
    rfl
  have f2 : (sliceW0 V W Z w0 hw0).comp ψ2 = χW := by
    rw [hχW, hψ2, ← AlgHom.comp_assoc, sliceW0_comp_triplePullZ]
  have f3 : (sliceW0 V W Z w0 hw0).comp ψ3 = BS := by
    rw [hBS, hψ3, ← AlgHom.comp_assoc, sliceW0_comp_pullProjVZ, AlgHom.id_comp]
  have f4 : (sliceW0 V W Z w0 hw0).comp ψ4 = ρW := by
    rw [hρW, hψ4, ← AlgHom.comp_assoc, sliceW0_comp_triplePullV]
  have f5 : (sliceW0 V W Z w0 hw0).comp ψ5 = ςW := by
    rw [hςW, hψ5, ← AlgHom.comp_assoc, sliceW0_comp_algebraMap]
  have f6 : (sliceW0 V W Z w0 hw0).comp ψ6
      = (Algebra.ofId ℂ (prodAlg V Z)).comp (bdryCornerW V W Z v0 hv0 w0 hw0 z0 hz0) := by
    rw [hψ6, ← AlgHom.comp_assoc, sliceW0_comp_triplePullW, AlgHom.comp_assoc]
    rfl
  have f7 : (sliceW0 V W Z w0 hw0).comp ψ7 = ρW := by
    rw [hρW, hψ7, ← AlgHom.comp_assoc, sliceW0_comp_tripleInclPW, AlgHom.comp_assoc, ← hRV]
  -- the lift restricts to `u₂` on the `w₀`-slice
  have keyW : Vt.map ⇑(sliceW0 V W Z w0 hw0) = u.map ⇑BS := by
    have t1 : matUnitMap (sliceW0 V W Z w0 hw0) UA1 = matUnitMap χW U := by
      rw [show UA1 = matUnitMap ψ1 U from rfl, matUnitMap_comp, f1]
    have t2 : matUnitMap (sliceW0 V W Z w0 hw0) UA2 = (matUnitMap χW U)⁻¹ := by
      rw [show UA2 = matUnitMap ψ2 Ui from rfl, show Ui = U⁻¹ from rfl, matUnitMap_comp, f2,
        map_inv]
    have t3 : matUnitMap (sliceW0 V W Z w0 hw0) UA3 = matUnitMap BS U := by
      rw [show UA3 = matUnitMap ψ3 U from rfl, matUnitMap_comp, f3]
    have t4 : matUnitMap (sliceW0 V W Z w0 hw0) UA4 = (matUnitMap ρW U)⁻¹ := by
      rw [show UA4 = matUnitMap ψ4 Ui from rfl, show Ui = U⁻¹ from rfl, matUnitMap_comp, f4,
        map_inv]
    have t5 : matUnitMap (sliceW0 V W Z w0 hw0) UA5 = matUnitMap ςW U := by
      rw [show UA5 = matUnitMap ψ5 U from rfl, matUnitMap_comp, f5]
    have t6 : matUnitMap (sliceW0 V W Z w0 hw0) UA6 = (matUnitMap ςW U)⁻¹ := by
      rw [show UA6 = matUnitMap ψ6 Ui from rfl, show Ui = U⁻¹ from rfl, matUnitMap_comp, f6,
        hCW, map_inv]
    have t7 : matUnitMap (sliceW0 V W Z w0 hw0) UA7 = matUnitMap ρW U := by
      rw [show UA7 = matUnitMap ψ7 U from rfl, matUnitMap_comp, f7]
    have hkey : matUnitMap (sliceW0 V W Z w0 hw0) VU = matUnitMap BS U := by
      rw [show VU = UA1 * UA2 * UA3 * UA4 * UA5 * UA6 * UA7 from rfl]
      simp only [map_mul]
      rw [t1, t2, t3, t4, t5, t6, t7]
      exact mul_tele_b (mul_inv_cancel (matUnitMap χW U)) (mul_inv_cancel (matUnitMap ςW U))
        (inv_mul_cancel (matUnitMap ρW U))
    have h1 : Vt.map ⇑(sliceW0 V W Z w0 hw0)
        = ↑(matUnitMap (sliceW0 V W Z w0 hw0) VU) := rfl
    rw [h1, hkey, matUnitMap_apply]
    exact congrArg (fun M => M.map ⇑BS) hU
  -- the images of the seven chart homs under the `z₀`-slice
  set ϑZ : bdryAlg V W Z v0 hv0 w0 hw0 z0 hz0 →ₐ[ℂ] prodAlg V W :=
    (pullSnd V W).comp (bdryRestW V W Z v0 hv0 w0 hw0 z0 hz0) with hϑZ
  set ρZ : bdryAlg V W Z v0 hv0 w0 hw0 z0 hz0 →ₐ[ℂ] prodAlg V W :=
    (pullFst V W).comp (bdryRestV V W Z v0 hv0 w0 hw0 z0 hz0) with hρZ
  set ςV : bdryAlg V W Z v0 hv0 w0 hw0 z0 hz0 →ₐ[ℂ] prodAlg V W :=
    (Algebra.ofId ℂ (prodAlg V W)).comp (bdryCornerV V W Z v0 hv0 w0 hw0 z0 hz0) with hςV
  have g1 : (sliceZ0 V W Z z0 hz0).comp ψ1 = ϑZ := by
    rw [hϑZ, hψ1, ← AlgHom.comp_assoc, sliceZ0_comp_tripleInclWZ, AlgHom.comp_assoc]
    rfl
  have g2 : (sliceZ0 V W Z z0 hz0).comp ψ2
      = (Algebra.ofId ℂ (prodAlg V W)).comp (bdryCornerZ V W Z v0 hv0 w0 hw0 z0 hz0) := by
    rw [hψ2, ← AlgHom.comp_assoc, sliceZ0_comp_triplePullZ, AlgHom.comp_assoc]
    rfl
  have g3 : (sliceZ0 V W Z z0 hz0).comp ψ3 = ρZ := by
    rw [hρZ, hψ3, ← AlgHom.comp_assoc, sliceZ0_comp_pullProjVZ, AlgHom.comp_assoc]
    rfl
  have g4 : (sliceZ0 V W Z z0 hz0).comp ψ4 = ρZ := by
    rw [hρZ, hψ4, ← AlgHom.comp_assoc, sliceZ0_comp_triplePullV]
  have g5 : (sliceZ0 V W Z z0 hz0).comp ψ5 = ςV := by
    rw [hςV, hψ5, ← AlgHom.comp_assoc, sliceZ0_comp_algebraMap]
  have g6 : (sliceZ0 V W Z z0 hz0).comp ψ6 = ϑZ := by
    rw [hϑZ, hψ6, ← AlgHom.comp_assoc, sliceZ0_comp_triplePullW]
  have g7 : (sliceZ0 V W Z z0 hz0).comp ψ7 = BT := by
    rw [hBT, hψ7, ← AlgHom.comp_assoc, sliceZ0_comp_tripleInclPW, AlgHom.id_comp]
  -- the lift restricts to `u₃` on the `z₀`-slice
  have keyZ : Vt.map ⇑(sliceZ0 V W Z z0 hz0) = u.map ⇑BT := by
    have t1 : matUnitMap (sliceZ0 V W Z z0 hz0) UA1 = matUnitMap ϑZ U := by
      rw [show UA1 = matUnitMap ψ1 U from rfl, matUnitMap_comp, g1]
    have t2 : matUnitMap (sliceZ0 V W Z z0 hz0) UA2 = (matUnitMap ςV U)⁻¹ := by
      rw [show UA2 = matUnitMap ψ2 Ui from rfl, show Ui = U⁻¹ from rfl, matUnitMap_comp, g2,
        hCZ, map_inv]
    have t3 : matUnitMap (sliceZ0 V W Z z0 hz0) UA3 = matUnitMap ρZ U := by
      rw [show UA3 = matUnitMap ψ3 U from rfl, matUnitMap_comp, g3]
    have t4 : matUnitMap (sliceZ0 V W Z z0 hz0) UA4 = (matUnitMap ρZ U)⁻¹ := by
      rw [show UA4 = matUnitMap ψ4 Ui from rfl, show Ui = U⁻¹ from rfl, matUnitMap_comp, g4,
        map_inv]
    have t5 : matUnitMap (sliceZ0 V W Z z0 hz0) UA5 = matUnitMap ςV U := by
      rw [show UA5 = matUnitMap ψ5 U from rfl, matUnitMap_comp, g5]
    have t6 : matUnitMap (sliceZ0 V W Z z0 hz0) UA6 = (matUnitMap ϑZ U)⁻¹ := by
      rw [show UA6 = matUnitMap ψ6 Ui from rfl, show Ui = U⁻¹ from rfl, matUnitMap_comp, g6,
        map_inv]
    have t7 : matUnitMap (sliceZ0 V W Z z0 hz0) UA7 = matUnitMap BT U := by
      rw [show UA7 = matUnitMap ψ7 U from rfl, matUnitMap_comp, g7]
    have hkey : matUnitMap (sliceZ0 V W Z z0 hz0) VU = matUnitMap BT U := by
      rw [show VU = UA1 * UA2 * UA3 * UA4 * UA5 * UA6 * UA7 from rfl]
      simp only [map_mul]
      rw [t1, t2, t3, t4, t5, t6, t7]
      exact mul_tele_c (mul_inv_cancel (matUnitMap ρZ U)) (inv_mul_cancel (matUnitMap ςV U))
        (mul_inv_cancel (matUnitMap ϑZ U))
    have h1 : Vt.map ⇑(sliceZ0 V W Z z0 hz0)
        = ↑(matUnitMap (sliceZ0 V W Z z0 hz0) VU) := rfl
    rw [h1, hkey, matUnitMap_apply]
    exact congrArg (fun M => M.map ⇑BT) hU
  -- assemble: the three slices of the lift are the three components of `u`
  have hmain : Vt.map ⇑(bdryProj V W Z v0 hv0 w0 hw0 z0 hz0) = u := by
    apply Matrix.ext
    intro i j
    apply Subtype.ext
    apply Prod.ext
    · exact congrArg (fun M : Matrix (Fin n) (Fin n) (prodAlg W Z) => M i j) keyV
    · apply Prod.ext
      · exact congrArg (fun M : Matrix (Fin n) (Fin n) (prodAlg V Z) => M i j) keyW
      · exact congrArg (fun M : Matrix (Fin n) (Fin n) (prodAlg V W) => M i j) keyZ
  refine ⟨0, Vt, hVunit, ?_⟩
  rw [hmain]
  exact (reindex_fromBlocks_zero n u).symm

end

end Work.KT.ExtGen
