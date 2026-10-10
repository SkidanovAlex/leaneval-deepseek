import Mathlib
import Submission.Work.MotT.KleinParamData
import Submission.Work.MotT.kpData_spans_good
import Submission.Work.MotT.kpData_klein_eq
import Submission.Work.MotC2.Translation
import Submission.Work.MotT.kpE_point_on_curve
import Submission.Work.MotK.T_diag_of_kleinEq_spans
import Submission.Work.Reflect.PolyId

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option maxRecDepth 200000
set_option maxHeartbeats 20000000
set_option linter.unusedSectionVars false

open WeierstrassCurve WeierstrassCurve.Affine

namespace Work.MotT
noncomputable section

/-- `5 ≠ 0` in a field of `ringChar ≠ 5`. -/
lemma five_ne_zero (K : Type) [Field K] (hk : ringChar K ≠ 5) : (5 : K) ≠ 0 := by
  intro h
  have hdvd : ringChar K ∣ 5 := ringChar.dvd h
  rcases (Nat.Prime.eq_one_or_self_of_dvd (by norm_num : Nat.Prime 5) _ hdvd) with h1 | h5
  · exact CharP.ringChar_ne_one h1
  · exact hk h5

/-- the discriminant of `kpE K u`. -/
theorem kpE_Δ (K : Type) [Field K] (u : K) (hu : u ≠ 0) (hw : kpW K u ≠ 0)
    (h5 : (5 : K) ≠ 0) :
    (kpE K u).Δ = (kpDelta K u) ^ 5 / ((5 : K) ^ 12 * u ^ 19) := by
  have h125 : (125 : K) ≠ 0 := by
    have : (125 : K) = (5 : K) ^ 3 := by norm_num
    rw [this]; exact pow_ne_zero 3 h5
  have h625 : (625 : K) ≠ 0 := by
    have : (625 : K) = (5 : K) ^ 4 := by norm_num
    rw [this]; exact pow_ne_zero 4 h5
  have h15625 : (15625 : K) ≠ 0 := by
    have : (15625 : K) = (5 : K) ^ 6 := by norm_num
    rw [this]; exact pow_ne_zero 6 h5
  have h390625 : (390625 : K) ≠ 0 := by
    have : (390625 : K) = (5 : K) ^ 8 := by norm_num
    rw [this]; exact pow_ne_zero 8 h5
  have h1953125 : (1953125 : K) ≠ 0 := by
    have : (1953125 : K) = (5 : K) ^ 9 := by norm_num
    rw [this]; exact pow_ne_zero 9 h5
  rw [eq_div_iff (by exact mul_ne_zero (pow_ne_zero 12 h5) (pow_ne_zero 19 hu))]
  simp only [kpE, kpA1, kpA2, kpA3, kpA4, kpA6]
  simp only [WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆,
    WeierstrassCurve.b₈]
  field_simp
  rw [kpDelta, kpW]
  ring_nf

/-- `κ_0` of the parametric model, as a polynomial in `x`. -/
lemma kpData_kleinCoord_zero (K : Type) [Field K] (u : K) (L : Type) [Field L] [Algebra K L] :
    Work.MotV.kleinCoord (kpData K u) L 0 =
      Polynomial.aeval (Work.MotV.genX ((kpData K u).E.baseChange L))
        (Polynomial.C (algebraMap L (WeierstrassCurve.Affine.FunctionField ((kpData K u).E.baseChange L))
            (algebraMap K L (kpCoord K u 0 0))) +
         Polynomial.C (algebraMap L (WeierstrassCurve.Affine.FunctionField ((kpData K u).E.baseChange L))
            (algebraMap K L (kpCoord K u 0 1))) * Polynomial.X +
         Polynomial.C (algebraMap L (WeierstrassCurve.Affine.FunctionField ((kpData K u).E.baseChange L))
            (algebraMap K L (kpCoord K u 0 3))) * Polynomial.X^2) := by
  simp only [Work.MotV.kleinCoord, kpData_coord, kpCoord, Work.MotV.kleinBas]
  simp only [Fin.sum_univ_five, Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.head_fin_const,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
    Matrix.head_cons, Matrix.tail_cons, Matrix.empty_val']
  simp only [map_add, map_mul, map_pow, Polynomial.aeval_X, Polynomial.aeval_C]
  push_cast
  simp only [← IsScalarTower.algebraMap_apply]
  first | refl_ring1 | ring


/-- **The linear-algebra core of the scaling route.**  Let `C` be the coordinate matrix
(`κ_i = ∑_m C i m * bas_m`) and let `Γ` be the change-of-basis matrix of the scaling
`κ ↦ diag(ζ)κ`; both hypotheses are *linear* in `Γ`:

* `hCΓ : ∀ i k, ∑ m, C i m * Γ m k = ζ ^ i * C i k`  (i.e. `C * Γ = diag ζ * C`), and
* `hbas : ∀ m, ∑ k, Γ m k * bas k = <the Veronese vector of the transformed point>`.

The second hypothesis is the substantive one (it says the transformed `bas`-vector is again a
Veronese vector, i.e. the transformed point exists); granted it, the eigen-relation is a pure
double-sum rearrangement.  This lemma isolates that rearrangement so that the remaining
content (the existence of the transformed point) can be attacked separately. -/
lemma eigen_of_matrix {F : Type} [Field F] (z : F) (C Γ : Fin 5 → Fin 5 → F) (bas : Fin 5 → F)
    (hCΓ : ∀ i k, ∑ m, C i m * Γ m k = z ^ (i : ℕ) * C i k) (i : Fin 5) :
    ∑ m, C i m * (∑ k, Γ m k * bas k) = z ^ (i : ℕ) * ∑ m, C i m * bas m := by
  calc ∑ m, C i m * (∑ k, Γ m k * bas k)
      = ∑ m, ∑ k, C i m * Γ m k * bas k := by
        exact Finset.sum_congr rfl fun m _ => by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun k _ => by ring
    _ = ∑ k, ∑ m, C i m * Γ m k * bas k := Finset.sum_comm
    _ = ∑ k, (∑ m, C i m * Γ m k) * bas k := by
        exact Finset.sum_congr rfl fun k _ => by rw [Finset.sum_mul]
    _ = ∑ k, (z ^ (i : ℕ) * C i k) * bas k := by
        exact Finset.sum_congr rfl fun k _ => by rw [hCΓ i k]
    _ = z ^ (i : ℕ) * ∑ k, C i k * bas k := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun k _ => by ring

/-- **(I″) instance, first half.**  The polynomial `Q = (Σ_i E 1 i • X_i)^2 − Σ_i E 3 i • X_i`
evaluates to `x^2 − x^2 = 0` at the Klein coordinates `κ_i` — this uses only the `spans` relation
`Σ_i E m i • κ_i = bas_m`.  Hence, by the kernel-preservation input (I″), it evaluates to `0` at
the scaled coordinate vector `k'` as well, i.e. `ssx^2 = Σ_i E 3 i • k'_i`. -/
lemma kp_veronese3 (K : Type) [Field K] (u : K) (L : Type) [Field L] [Algebra K L]
    (k' : Fin 5 → WeierstrassCurve.Affine.FunctionField ((kpData K u).E.baseChange L))
    (E : Matrix (Fin 5) (Fin 5) L)
    (hκ : ∀ F : MvPolynomial (Fin 5) L,
      MvPolynomial.aeval (fun i => Work.MotV.kleinCoord (kpData K u) L i) F = 0 →
      MvPolynomial.aeval k' F = 0)
    (hbas : ∀ m : Fin 5,
      ∑ i, algebraMap L (WeierstrassCurve.Affine.FunctionField ((kpData K u).E.baseChange L))
          (E m i) * Work.MotV.kleinCoord (kpData K u) L i
        = Work.MotV.kleinBas (kpData K u) L m) :
    (∑ i, algebraMap L (WeierstrassCurve.Affine.FunctionField ((kpData K u).E.baseChange L))
        (E 1 i) * k' i) ^ 2
      = ∑ i, algebraMap L (WeierstrassCurve.Affine.FunctionField ((kpData K u).E.baseChange L))
        (E 3 i) * k' i := by
  have hQ : MvPolynomial.aeval (fun i => Work.MotV.kleinCoord (kpData K u) L i)
      ((∑ i, MvPolynomial.C (E 1 i) * MvPolynomial.X i) ^ 2 -
        ∑ i, MvPolynomial.C (E 3 i) * MvPolynomial.X i) = 0 := by
    simp only [map_sub, map_pow, map_sum, map_mul, MvPolynomial.aeval_X, MvPolynomial.aeval_C]
    rw [hbas 1, hbas 3]
    simp only [Work.MotV.kleinBas, Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.head_cons,
      Matrix.tail_cons, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
      Matrix.cons_val_four, Matrix.head_fin_const, Matrix.empty_val']
    first | refl_ring1 | ring
  have hQ' := hκ _ hQ
  simp only [map_sub, map_pow, map_sum, map_mul, MvPolynomial.aeval_X, MvPolynomial.aeval_C]
    at hQ'
  exact sub_eq_zero.mp hQ'

/-- **(I″) instance, second half.**  The same argument applied to
`(Σ_i E 1 i • X_i)(Σ_i E 2 i • X_i) − Σ_i E 4 i • X_i`, which evaluates to `xy − xy = 0` at the
Klein coordinates, gives `ssx · ssy = Σ_i E 4 i • k'_i`. -/
lemma kp_veronese4 (K : Type) [Field K] (u : K) (L : Type) [Field L] [Algebra K L]
    (k' : Fin 5 → WeierstrassCurve.Affine.FunctionField ((kpData K u).E.baseChange L))
    (E : Matrix (Fin 5) (Fin 5) L)
    (hκ : ∀ F : MvPolynomial (Fin 5) L,
      MvPolynomial.aeval (fun i => Work.MotV.kleinCoord (kpData K u) L i) F = 0 →
      MvPolynomial.aeval k' F = 0)
    (hbas : ∀ m : Fin 5,
      ∑ i, algebraMap L (WeierstrassCurve.Affine.FunctionField ((kpData K u).E.baseChange L))
          (E m i) * Work.MotV.kleinCoord (kpData K u) L i
        = Work.MotV.kleinBas (kpData K u) L m) :
    (∑ i, algebraMap L (WeierstrassCurve.Affine.FunctionField ((kpData K u).E.baseChange L))
        (E 1 i) * k' i) *
      (∑ i, algebraMap L (WeierstrassCurve.Affine.FunctionField ((kpData K u).E.baseChange L))
        (E 2 i) * k' i)
      = ∑ i, algebraMap L (WeierstrassCurve.Affine.FunctionField ((kpData K u).E.baseChange L))
        (E 4 i) * k' i := by
  have hQ : MvPolynomial.aeval (fun i => Work.MotV.kleinCoord (kpData K u) L i)
      ((∑ i, MvPolynomial.C (E 1 i) * MvPolynomial.X i) *
          (∑ i, MvPolynomial.C (E 2 i) * MvPolynomial.X i) -
        ∑ i, MvPolynomial.C (E 4 i) * MvPolynomial.X i) = 0 := by
    simp only [map_sub, map_mul, map_sum, MvPolynomial.aeval_X, MvPolynomial.aeval_C]
    rw [hbas 1, hbas 2, hbas 4]
    simp only [Work.MotV.kleinBas, Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.head_cons,
      Matrix.tail_cons, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
      Matrix.cons_val_four, Matrix.head_fin_const, Matrix.empty_val']
    first | refl_ring1 | ring
  have hQ' := hκ _ hQ
  simp only [map_sub, map_mul, map_sum, MvPolynomial.aeval_X, MvPolynomial.aeval_C] at hQ'
  exact sub_eq_zero.mp hQ'

/-- The `MotV` and `MotC2` function-field coordinates agree (needed to quote the Weierstrass
relation, which lives in `MotC2`). -/
lemma kp_MotV_genX_eq (L : Type) [Field L] (E : WeierstrassCurve L) :
    Work.MotV.genX E = Work.MotC2.genX E := by
  rw [Work.MotV.genX, Work.MotC2.genX, Work.MotC2.coordX_eq_mk]

lemma kp_MotV_genY_eq (L : Type) [Field L] (E : WeierstrassCurve L) :
    Work.MotV.genY E = Work.MotC2.genY E := by
  rw [Work.MotV.genY, Work.MotC2.genY, Work.MotC2.coordY_eq_mk]

/-- **(I″) instance, third: the transformed point is on the curve.**  The polynomial obtained by
substituting `x := Σ_i E 1 i • X_i`, `y := Σ_i E 2 i • X_i` into the Weierstrass relation
evaluates to `0` at the Klein coordinates `κ_i` (that *is* the Weierstrass relation in `FF`,
`Work.MotC2.genY_sq_relation`), hence by (I″) it evaluates to `0` at `k'`: the point `(ssx, ssy)`
lies on `E`. -/
lemma kp_curve (K : Type) [Field K] (u : K) (L : Type) [Field L] [Algebra K L]
    (k' : Fin 5 → WeierstrassCurve.Affine.FunctionField ((kpData K u).E.baseChange L))
    (E : Matrix (Fin 5) (Fin 5) L)
    (hκ : ∀ F : MvPolynomial (Fin 5) L,
      MvPolynomial.aeval (fun i => Work.MotV.kleinCoord (kpData K u) L i) F = 0 →
      MvPolynomial.aeval k' F = 0)
    (hbas : ∀ m : Fin 5,
      ∑ i, algebraMap L (WeierstrassCurve.Affine.FunctionField ((kpData K u).E.baseChange L))
          (E m i) * Work.MotV.kleinCoord (kpData K u) L i
        = Work.MotV.kleinBas (kpData K u) L m) :
    (∑ i, algebraMap L (WeierstrassCurve.Affine.FunctionField ((kpData K u).E.baseChange L))
        (E 2 i) * k' i) ^ 2
      + algebraMap L (WeierstrassCurve.Affine.FunctionField ((kpData K u).E.baseChange L))
          (((kpData K u).E.baseChange L).a₁)
          * (∑ i, algebraMap L (WeierstrassCurve.Affine.FunctionField ((kpData K u).E.baseChange L))
              (E 1 i) * k' i)
          * (∑ i, algebraMap L (WeierstrassCurve.Affine.FunctionField ((kpData K u).E.baseChange L))
              (E 2 i) * k' i)
      + algebraMap L (WeierstrassCurve.Affine.FunctionField ((kpData K u).E.baseChange L))
          (((kpData K u).E.baseChange L).a₃)
          * (∑ i, algebraMap L (WeierstrassCurve.Affine.FunctionField ((kpData K u).E.baseChange L))
              (E 2 i) * k' i)
      = (∑ i, algebraMap L (WeierstrassCurve.Affine.FunctionField ((kpData K u).E.baseChange L))
          (E 1 i) * k' i) ^ 3
      + algebraMap L (WeierstrassCurve.Affine.FunctionField ((kpData K u).E.baseChange L))
          (((kpData K u).E.baseChange L).a₂)
          * (∑ i, algebraMap L (WeierstrassCurve.Affine.FunctionField ((kpData K u).E.baseChange L))
              (E 1 i) * k' i) ^ 2
      + algebraMap L (WeierstrassCurve.Affine.FunctionField ((kpData K u).E.baseChange L))
          (((kpData K u).E.baseChange L).a₄)
          * (∑ i, algebraMap L (WeierstrassCurve.Affine.FunctionField ((kpData K u).E.baseChange L))
              (E 1 i) * k' i)
      + algebraMap L (WeierstrassCurve.Affine.FunctionField ((kpData K u).E.baseChange L))
          (((kpData K u).E.baseChange L).a₆) := by
  have hQ : MvPolynomial.aeval (fun i => Work.MotV.kleinCoord (kpData K u) L i)
      ((∑ i, MvPolynomial.C (E 2 i) * MvPolynomial.X i) ^ 2
        + MvPolynomial.C (((kpData K u).E.baseChange L).a₁)
            * (∑ i, MvPolynomial.C (E 1 i) * MvPolynomial.X i)
            * (∑ i, MvPolynomial.C (E 2 i) * MvPolynomial.X i)
        + MvPolynomial.C (((kpData K u).E.baseChange L).a₃)
            * (∑ i, MvPolynomial.C (E 2 i) * MvPolynomial.X i)
        - (∑ i, MvPolynomial.C (E 1 i) * MvPolynomial.X i) ^ 3
        - MvPolynomial.C (((kpData K u).E.baseChange L).a₂)
            * (∑ i, MvPolynomial.C (E 1 i) * MvPolynomial.X i) ^ 2
        - MvPolynomial.C (((kpData K u).E.baseChange L).a₄)
            * (∑ i, MvPolynomial.C (E 1 i) * MvPolynomial.X i)
        - MvPolynomial.C (((kpData K u).E.baseChange L).a₆)) = 0 := by
    simp only [map_sub, map_add, map_mul, map_pow, map_sum, MvPolynomial.aeval_X,
      MvPolynomial.aeval_C]
    rw [hbas 1, hbas 2]
    simp only [Work.MotV.kleinBas, Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.head_cons,
      Matrix.tail_cons, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
      Matrix.cons_val_four, Matrix.head_fin_const, Matrix.empty_val']
    rw [kp_MotV_genX_eq, kp_MotV_genY_eq]
    linear_combination (norm := first | refl_ring1 | ring1) Work.MotC2.genY_sq_relation ((kpData K u).E.baseChange L)
  have hQ' := hκ _ hQ
  simp only [map_sub, map_add, map_mul, map_pow, map_sum, MvPolynomial.aeval_X,
    MvPolynomial.aeval_C] at hQ'
  linear_combination (norm := first | refl_ring1 | ring1) hQ'

/-- **`kpData_T_diag`** -/
theorem kpData_T_diag (K : Type) [Field K] (hk : ringChar K ≠ 5) (u : K) (hu : u ≠ 0)
    (hw : Work.MotT.kpW K u ≠ 0) (hΔ : Work.MotT.kpDelta K u ≠ 0) :
    ∀ (L : Type) [Field L] [Algebra K L] (ζ : L), IsPrimitiveRoot ζ 5 →
      ∃ σ : WeierstrassCurve.Affine.FunctionField ((Work.MotT.kpData K u).E.baseChange L) ≃ₐ[L]
          WeierstrassCurve.Affine.FunctionField ((Work.MotT.kpData K u).E.baseChange L),
        ∀ i, σ (Work.MotV.kleinCoord (Work.MotT.kpData K u) L i /
              Work.MotV.kleinCoord (Work.MotT.kpData K u) L 0) =
          algebraMap L (WeierstrassCurve.Affine.FunctionField ((Work.MotT.kpData K u).E.baseChange L)) ζ ^ (i : ℕ) *
            (Work.MotV.kleinCoord (Work.MotT.kpData K u) L i /
              Work.MotV.kleinCoord (Work.MotT.kpData K u) L 0) :=
  Work.MotK.T_diag_of_kleinEq_spans (Work.MotT.kpData K u)
    (by show u * 1 ≠ 0; simpa using hu)
    (kpData_klein_eq K hk u hu hw hΔ)
    (kpData_spans_good K hk u hu hw hΔ)

end
end Work.MotT
