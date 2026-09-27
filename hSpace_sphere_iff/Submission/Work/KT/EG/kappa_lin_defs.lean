import Mathlib
import Submission.Work.KT.Defs
import Submission.Work.KT.Fund.Kappa
import Submission.Work.KT.Fund.isUnit_matrix_forall

/-!
# `Work.KT.EG.kappa_lin_defs` — matrices for the linear clutching reduction

The linear clutching reduction (`Work.KT.EG.kappa_lin`, Hatcher VBKT Prop. 2.7) computes the
clutched class of the linear unit `z·1 + pullMat b` over `C(X × S¹, ℂ)` by writing it as a product
`v·w` of two commuting units which are *block diagonal* with respect to a spectral projection `E`
of `b`:

  `v = z E + E b + (1-E)`,  `w = E + z (1-E) + (1-E) b`,  `v·w = z·1 + b`.

Both `v` and `w` are deformed, through homotopies consisting of units, to the standard forms
`z E + (1-E)` and `E + (1-E) b`; the latter is a constant (in `z`) unit, and the former is the
Bott unit of the idempotent `E`.

This module collects the matrices involved (over the circle `X × S¹` and over the cylinder
`(X × I) × S¹` in which the homotopies live), so that the lemmas about them can be stated and
proved separately.
-/

namespace Work.KT.EG

open Matrix

noncomputable section

variable (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X]

/-! ## The cylinder `(X × I) × S¹` -/

/-- The projection `(X × I) × S¹ → X`, dropping both the interval and the circle coordinate. -/
def projCylX : C((X × unitInterval) × Sph ℂ, X) where
  toFun q := q.1.1
  continuous_toFun := by fun_prop

@[simp] lemma projCylX_apply (q : (X × unitInterval) × Sph ℂ) : projCylX X q = q.1.1 := rfl

/-- The coordinate `z` on `(X × I) × S¹`, as a continuous function. -/
def zCyl : C((X × unitInterval) × Sph ℂ, ℂ) :=
  (Work.KT.zUnit (X × unitInterval) : C((X × unitInterval) × Sph ℂ, ℂ))

/-- The coordinate `t` on `(X × I) × S¹`, as a complex-valued continuous function. -/
def tCyl : C((X × unitInterval) × Sph ℂ, ℂ) where
  toFun q := ((q.1.2 : unitInterval) : ℂ)
  continuous_toFun := by fun_prop

@[simp] lemma tCyl_apply (q : (X × unitInterval) × Sph ℂ) :
    tCyl X q = ((q.1.2 : unitInterval) : ℂ) := rfl

/-- Pull back a matrix over `C(X, ℂ)` to the cylinder `(X × I) × S¹`. -/
def pullBig {n : ℕ} (M : Matrix (Fin n) (Fin n) C(X, ℂ)) :
    Matrix (Fin n) (Fin n) C((X × unitInterval) × Sph ℂ, ℂ) :=
  M.map (fun f => f.comp (projCylX X))

@[simp] lemma pullBig_apply {n : ℕ} (M : Matrix (Fin n) (Fin n) C(X, ℂ)) (i j : Fin n)
    (q : (X × unitInterval) × Sph ℂ) : pullBig X M i j q = M i j q.1.1 := rfl

lemma pullBig_add {n : ℕ} (M N : Matrix (Fin n) (Fin n) C(X, ℂ)) :
    pullBig X (M + N) = pullBig X M + pullBig X N := by
  refine Matrix.ext fun i j => ContinuousMap.ext fun q => ?_
  simp only [pullBig_apply, Matrix.add_apply, ContinuousMap.add_apply]

/-! ## The two matrices of the factorisation, over the circle -/

/-- `v = z E + E b + (1 - E)`, over `C(X × S¹, ℂ)`. -/
def Vcirc {n : ℕ} (b E : Matrix (Fin n) (Fin n) C(X, ℂ)) :
    Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ) :=
  (Work.KT.zUnit X : C(X × Sph ℂ, ℂ)) • Work.KT.Fund.pullMat X E
    + Work.KT.Fund.pullMat X (E * b) + Work.KT.Fund.pullMat X (1 - E)

/-- `v₀ = z E + (1 - E)`, over `C(X × S¹, ℂ)`. -/
def Vcirc0 {n : ℕ} (E : Matrix (Fin n) (Fin n) C(X, ℂ)) :
    Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ) :=
  (Work.KT.zUnit X : C(X × Sph ℂ, ℂ)) • Work.KT.Fund.pullMat X E
    + Work.KT.Fund.pullMat X (1 - E)

/-- `w = E + z (1 - E) + (1-E) b`, over `C(X × S¹, ℂ)`. -/
def Wcirc {n : ℕ} (b E : Matrix (Fin n) (Fin n) C(X, ℂ)) :
    Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ) :=
  Work.KT.Fund.pullMat X E
    + (Work.KT.zUnit X : C(X × Sph ℂ, ℂ)) • Work.KT.Fund.pullMat X (1 - E)
    + Work.KT.Fund.pullMat X ((1 - E) * b)

/-- `w₀ = E + (1-E) b`, the constant (in `z`) form of `w`, over `C(X × S¹, ℂ)`. -/
def Wcirc0 {n : ℕ} (b E : Matrix (Fin n) (Fin n) C(X, ℂ)) :
    Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ) :=
  Work.KT.Fund.pullMat X E + Work.KT.Fund.pullMat X ((1 - E) * b)

/-! ## The two homotopy matrices, over the cylinder -/

/-- The homotopy `z E + t (E b) + (1 - E)` from `v` (`t = 1`) to `v₀` (`t = 0`). -/
def VinBig {n : ℕ} (b E : Matrix (Fin n) (Fin n) C(X, ℂ)) :
    Matrix (Fin n) (Fin n) C((X × unitInterval) × Sph ℂ, ℂ) :=
  zCyl X • pullBig X E + tCyl X • pullBig X (E * b) + pullBig X (1 - E)

/-- The homotopy `E + t z (1 - E) + (1-E) b` from `w` (`t = 1`) to `w₀` (`t = 0`). -/
def WoutBig {n : ℕ} (b E : Matrix (Fin n) (Fin n) C(X, ℂ)) :
    Matrix (Fin n) (Fin n) C((X × unitInterval) × Sph ℂ, ℂ) :=
  pullBig X E + (tCyl X * zCyl X) • pullBig X (1 - E) + pullBig X ((1 - E) * b)

end

end Work.KT.EG
