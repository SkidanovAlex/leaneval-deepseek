import Mathlib
import Submission.Work.MotT.KleinParamData
import Submission.Work.Reflect.PolyId

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.MotT.kpData_spans_good`: the parametric Klein datum `(u,1)` generates `L(5·O)`

The requested lemma is the `spans` field of `Work.MotV.KleinData.Good` for the parametric Klein
datum `kpData K u` of `Submission/Work/MotT/KleinParamData.lean`: the basis
`1, x, y, x², xy` of `L(5·O)` is a `K`-linear combination of the five Klein coordinates
`κ_i = Σ_m coord_i m · b_m`.

Equivalently, the coordinate matrix `M = kpCoord K u` is invertible over `K`.  We prove this by
computing its determinant:

`det (kpCoord K u) = -5⁵⁹ · u¹⁰³ · (kpDelta K u)⁵`,

a (rational) identity obtained by expanding the `5 × 5` determinant with `Matrix.det_succ_row_zero`
and verifying the resulting polynomial identity with `ring`.  The right-hand side is nonzero as
soon as `ringChar K ≠ 5`, `u ≠ 0` and `kpDelta K u ≠ 0` (the extra hypothesis `kpW K u ≠ 0` is
needed to clear the denominators `u ^ ·` and `kpW K u ^ ·` appearing in the entries).  Then
`N = (det M)⁻¹ • M.adjugate` satisfies `N * M = 1`, which inverts the relation
`κ_i = Σ_m M i m · b_m` and yields the claim.

The determinant identity is false without `kpW K u ≠ 0`: see
`Submission/Work/MotT/kpData_spans_refutation.lean`.
-/

set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option linter.style.haveILetI false

open WeierstrassCurve WeierstrassCurve.Affine

namespace Work.MotT

noncomputable section

/-- The coordinate matrix `kpCoord K u` written as a matrix literal (`kpMatLit K u` is
definitionally equal to `kpCoord K u`, but is *syntactically* a `Matrix`, which is what the
determinant API of Mathlib needs in order to expand it entry by entry). -/
def kpMatLit (K : Type) [Field K] (u : K) : Matrix (Fin 5) (Fin 5) K :=
  !![ -390625 * u ^ 17 * kpDelta K u ^ 3 / kpW K u ^ 2,
       48828125 * u ^ 21 * (4 * u ^ 5 + 3) * kpDelta K u / kpW K u,
       0,
       6103515625 * u ^ 25,
       0;
     78125 * u ^ 15 * (3 * u ^ 5 + 1) * kpDelta K u ^ 3 / kpW K u ^ 2,
       19531250 * u ^ 19 * kpDelta K u ^ 2 / kpW K u,
       -48828125 * u ^ 21 * (3 * u ^ 5 - 4) * kpDelta K u / kpW K u,
       -1220703125 * u ^ 23 * (u ^ 5 + 2),
       6103515625 * u ^ 25;
     390625 * u ^ 19 * kpDelta K u ^ 3 / kpW K u ^ 2,
       -9765625 * u ^ 18 * (6 * u ^ 10 + 24 * u ^ 5 - 1) * kpDelta K u / kpW K u,
       48828125 * u ^ 20 * (7 * u ^ 5 - 1) * kpDelta K u / kpW K u,
       -1220703125 * u ^ 22 * (3 * u ^ 5 + 1),
       6103515625 * u ^ 24;
     -78125 * u ^ 14 * kpDelta K u ^ 3 / kpW K u,
       9765625 * u ^ 18 * (7 * u ^ 5 - 1) * kpDelta K u,
       -48828125 * u ^ 20 * (7 * u ^ 5 - 1) * kpDelta K u / kpW K u,
       0,
       -6103515625 * u ^ 24;
     234375 * u ^ 15 * kpDelta K u ^ 3 / kpW K u,
       -9765625 * u ^ 19 * (4 * u ^ 5 + 3) * kpDelta K u,
       48828125 * u ^ 21 * (3 * u ^ 5 - 4) * kpDelta K u / kpW K u,
       1220703125 * u ^ 23 * kpW K u,
       -6103515625 * u ^ 25]

theorem kpMatLit_eq_kpCoord (K : Type) [Field K] (u : K) :
    kpMatLit K u = (kpCoord K u : Matrix (Fin 5) (Fin 5) K) := rfl

/-- **The determinant of the coordinate matrix.**  `det (kpCoord K u) = -5⁵⁹ u¹⁰³ Δ⁵`.

The hypotheses `u ≠ 0` and `kpW K u ≠ 0` are exactly the nonvanishing of the denominators appearing
in the entries of `kpCoord K u`; `ringChar K ≠ 5` makes the numeric factors invertible. -/
theorem kpMatLit_det (K : Type) [Field K] (u : K) (hk : ringChar K ≠ 5) (hu : u ≠ 0)
    (hw : kpW K u ≠ 0) :
    (kpMatLit K u).det = -(5 : K) ^ 59 * u ^ 103 * (kpDelta K u) ^ 5 := by
  have h5 : (5 : K) ≠ 0 := by
    haveI := ringChar.charP K
    exact CharP.cast_ne_zero_of_ne_of_prime (R := K) Nat.prime_five hk
  simp [kpMatLit, Matrix.det_succ_row_zero, Fin.sum_univ_succ]
  simp only [Fin.succAbove]
  norm_num
  field_simp
  simp only [kpDelta, kpW]
  first | refl_ring1 | ring

/-- The determinant is nonzero under the hypotheses of `kpData_spans_good`. -/
theorem kpCoord_det_ne_zero (K : Type) [Field K] (hk : ringChar K ≠ 5) (u : K) (hu : u ≠ 0)
    (hw : kpW K u ≠ 0) (hΔ : kpDelta K u ≠ 0) :
    Matrix.det (kpCoord K u : Matrix (Fin 5) (Fin 5) K) ≠ 0 := by
  have h5 : (5 : K) ≠ 0 := by
    haveI := ringChar.charP K
    exact CharP.cast_ne_zero_of_ne_of_prime (R := K) Nat.prime_five hk
  rw [← kpMatLit_eq_kpCoord K u, kpMatLit_det K u hk hu hw]
  exact mul_ne_zero (mul_ne_zero (neg_ne_zero.mpr (pow_ne_zero 59 h5)) (pow_ne_zero 103 hu))
    (pow_ne_zero 5 hΔ)

theorem kpData_spans_good (K : Type) [Field K] (hk : ringChar K ≠ 5) (u : K) (hu : u ≠ 0)
    (hw : Work.MotT.kpW K u ≠ 0) (hΔ : Work.MotT.kpDelta K u ≠ 0) :
    ∃ e : Fin 5 → Fin 5 → K, ∀ (L : Type) [Field L] [Algebra K L] (m : Fin 5),
      Work.MotV.kleinBas (Work.MotT.kpData K u) L m =
        ∑ i, algebraMap L (WeierstrassCurve.Affine.FunctionField ((Work.MotT.kpData K u).E.baseChange L))
          (algebraMap K L (e m i)) * Work.MotV.kleinCoord (Work.MotT.kpData K u) L i := by
  let M : Matrix (Fin 5) (Fin 5) K := kpCoord K u
  have hMdet : M.det ≠ 0 := by
    have h := kpCoord_det_ne_zero K hk u hu hw hΔ
    simpa only [M] using h
  -- the inverse of the coordinate matrix: `N * M = 1`
  let N : Matrix (Fin 5) (Fin 5) K := (M.det)⁻¹ • M.adjugate
  have hNM : N * M = 1 := by
    show ((M.det)⁻¹ • M.adjugate) * M = 1
    rw [Matrix.smul_mul, Matrix.adjugate_mul, smul_smul, inv_mul_cancel₀ hMdet, one_smul]
  refine ⟨fun m i => N m i, ?_⟩
  intro L _ _ m
  let F := WeierstrassCurve.Affine.FunctionField ((kpData K u).E.baseChange L)
  let φ : K →+* F := (algebraMap L F).comp (algebraMap K L)
  let b : Fin 5 → F := Work.MotV.kleinBas (kpData K u) L
  let c : Fin 5 → F := Work.MotV.kleinCoord (kpData K u) L
  -- the Klein coordinates in the basis `1, x, y, x², xy`
  have hc : c = Matrix.mulVec (M.map φ) b := by
    funext i
    simp only [c, b, φ, Matrix.mulVec, Matrix.map, M]
    rw [Work.MotV.kleinCoord_eq_sum (kpData K u) L i, kpData_coord]
    refine Finset.sum_congr rfl fun j _ => rfl
  -- invert the linear system
  have hb : b = Matrix.mulVec (N.map φ) c := by
    rw [hc, Matrix.mulVec_mulVec, ← Matrix.map_mul, hNM]
    have hone : ((1 : Matrix (Fin 5) (Fin 5) K).map (φ : K → F)) = 1 := by
      ext i j
      by_cases hij : i = j <;> simp [Matrix.map_apply, Matrix.one_apply, hij]
    rw [hone, Matrix.one_mulVec]
  have hbm : b m = Matrix.mulVec (N.map φ) c m := congrFun hb m
  simp only [b, c, φ, Matrix.mulVec, Matrix.map_apply] at hbm ⊢
  exact hbm

end

end Work.MotT
