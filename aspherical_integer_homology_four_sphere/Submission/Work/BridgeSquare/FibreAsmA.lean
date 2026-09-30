/-
# `BridgeSquare/FibreAsmA.lean` — the numeric facts of the `A`-case assembly

The assembly of `fibreLoopIdentA` out of the per-cell identities (`cellChiA`), the loop identity
(`singA_eq_cChain`) and the chart-chain algebra of `ChartAlgA.lean` uses only the following numeric
input (a finite computation on the generated tables):

* the expansion of the cellular fibre loop in the basis of the unit cells, with the coefficients
  `edgeSign v 0 k` (`fibreLoop_expand`), and
* the fact that the coefficient `edgeSign v 0 k • (-(qInc (edgeFace v 0 k) (edgeW0Face v 0 k)))`
  of the *geometric* unit edge in `Ψ_M (fibreLoopVec v 0)` is a constant `±1`, independent of `k`
  (`sign_const`), with the value `-1` for the first four cusps and `+1` for the fifth
  (`edgeSign_coeff`), the dummy cells `k ≥ fibreLen v 0` contributing `0`.
-/
import Mathlib
import Submission.Work.BridgeSquare.FibreGeomDataA
import Submission.Work.BridgeSquare.ChartAlgA

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency.types false

open Work.BridgeSquare Work.MbarHomology

namespace Work.BridgeSquare

noncomputable section

/-- The constant sign of the `A`-case: `-1` for the first four cusps, `+1` for the fifth. -/
def sgnA (v : Fin 5) : ℤ := if (v : ℕ) = 4 then 1 else -1

theorem sgnA_spec (v : Fin 5) : sgnA v = 1 ∨ sgnA v = -1 := by
  unfold sgnA; split <;> simp

/-- **The expansion of the cellular fibre loop** in the basis of the unit cells. -/
theorem fibreLoop_expand_point (v : Fin 5) (i : Fin 168) :
    fibreLoopVec v 0 i
      = (∑ k : Fin 4, (edgeSign v 0 k) • (Pi.single (edgeCell v 0 k) (1 : ℤ) :
          Fin (Work.HomologyIso.Gen.mbarDim 1) → ℤ)) i := by
  fin_cases v <;> fin_cases i <;> decide

theorem fibreLoop_expand (v : Fin 5) :
    fibreLoopVec v 0
      = ∑ k : Fin 4, (edgeSign v 0 k) • (Pi.single (edgeCell v 0 k) (1 : ℤ) :
          Fin (Work.HomologyIso.Gen.mbarDim 1) → ℤ) := by
  funext i
  exact fibreLoop_expand_point v i

/-- **The coefficient of the geometric unit edge in `Ψ_M` of the fibre loop**, uniformly: the
coefficient on the `k`-th unit edge is `sgnA v` when the edge exists and `0` for the dummy cells. -/
theorem edgeSign_coeff (v : Fin 5) (k : Fin 4) :
    edgeSign v 0 k * (-(qInc (edgeFace v 0 k) (edgeW0Face v 0 k)))
      = if (k : ℕ) < fibreLen v 0 then sgnA v else 0 := by
  fin_cases v <;> fin_cases k <;> decide

/-- The coefficient of the geometric unit edge is the constant `sgnA v`. -/
theorem sign_const (v : Fin 5) (k : Fin 4) (hk : (k : ℕ) < fibreLen v 0) :
    edgeSign v 0 k * (-(qInc (edgeFace v 0 k) (edgeW0Face v 0 k))) = sgnA v := by
  rw [edgeSign_coeff, if_pos hk]

/-- The dummy cells have coefficient zero. -/
theorem edgeSign_coeff_zero (v : Fin 5) (k : Fin 4) (hk : ¬ (k : ℕ) < fibreLen v 0) :
    edgeSign v 0 k * (-(qInc (edgeFace v 0 k) (edgeW0Face v 0 k))) = 0 := by
  rw [edgeSign_coeff, if_neg hk]

/-- `λ₂` is a lattice period of the ceiling map. -/
theorem lam2V_eq_kv (v : Fin 5) : lam2V v = Work.Cusp.kv v 1 := by
  apply PiLp.ext
  intro i
  fin_cases i <;>
    simp [lam2V, Work.Cusp.kv]

theorem lam2V_mem_lattice (v : Fin 5) : lam2V v ∈ Work.Cusp.lattice v := by
  rw [lam2V_eq_kv]
  exact AddSubgroup.subset_closure ⟨1, rfl⟩

end

end Work.BridgeSquare
