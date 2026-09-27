import Mathlib
import Submission.Work.KT.Fund.Kappa
import Submission.Work.KT.Fund.kl_defs

/-!
# `Work.KT.Fund.kl_alg` — the algebraic core of the linear clutching splitting

Hatcher's linear splitting (`kappa_lin`, and Hatcher *Vector Bundles and K-Theory*, Prop. 2.7): a
clutching function `z • 1 + b` with `b` commuting with an idempotent `E` factors as

  `z • 1 + b = klV * klW`,  `klV = z • E + E b + (1 - E)`,  `klW = E + z • (1 - E) + (1 - E) b`,

and the two factors commute.  This file proves that identity.

The proof is a computation in the centralizer of the idempotent `E` and is isolated in the
namespace `Work.KT.Fund.KL`, where all the identities are stated for matrices over an arbitrary
commutative ring; the second half of the file instantiates them for `R = C(X × S¹, ℂ)`, `E` the
pull-back of an idempotent of `C(X, ℂ)` and `b` the pull-back of a matrix commuting with it.
-/

namespace Work.KT.Fund

open Matrix

noncomputable section

/-! ## The abstract computation in the centralizer of an idempotent -/

namespace KL

variable {R : Type} [CommRing R] {n : ℕ}

lemma h1E (E : Matrix (Fin n) (Fin n) R) (hE : E * E = E) : E * (1 - E) = 0 := by
  rw [Matrix.mul_sub, Matrix.mul_one, hE, sub_self]

lemma hE1 (E : Matrix (Fin n) (Fin n) R) (hE : E * E = E) : (1 - E) * E = 0 := by
  rw [Matrix.sub_mul, Matrix.one_mul, hE, sub_self]

lemma h1E1 (E : Matrix (Fin n) (Fin n) R) (hE : E * E = E) : (1 - E) * (1 - E) = 1 - E := by
  rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_sub, Matrix.mul_one, hE, sub_self, sub_zero]

/-- A matrix commuting with the idempotent `E` also commutes with `1 - E`. -/
lemma hc1 (A E : Matrix (Fin n) (Fin n) R) (h : E * A = A * E) : A * (1 - E) = (1 - E) * A := by
  rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.one_mul, h]

lemma rE (A E : Matrix (Fin n) (Fin n) R) (hE : E * E = E) (h : E * A = A * E) :
    E * A * E = E * A := by
  rw [Matrix.mul_assoc, ← h, ← Matrix.mul_assoc, hE]

lemma r1 (A E : Matrix (Fin n) (Fin n) R) (hE : E * E = E) (h : E * A = A * E) :
    E * A * (1 - E) = 0 := by
  rw [h, Matrix.mul_assoc, h1E E hE, Matrix.mul_zero]

lemma r2 (A E : Matrix (Fin n) (Fin n) R) (hE : E * E = E) (h : E * A = A * E) :
    (1 - E) * A * E = 0 := by
  rw [Matrix.mul_assoc, ← h, ← Matrix.mul_assoc, hE1 E hE, Matrix.zero_mul]

lemma r3 (A E : Matrix (Fin n) (Fin n) R) (hE : E * E = E) (h : E * A = A * E) :
    (1 - E) * A * (1 - E) = (1 - E) * A := by
  rw [Matrix.mul_assoc, hc1 A E h, ← Matrix.mul_assoc, h1E1 E hE]

lemma rsum (A E : Matrix (Fin n) (Fin n) R) : E * A + (1 - E) * A = A := by
  rw [← Matrix.add_mul, add_sub_cancel, Matrix.one_mul]

lemma t1 (A E : Matrix (Fin n) (Fin n) R) (hE : E * E = E) (h : E * A = A * E) :
    E * A * ((1 - E) * A * (1 - E)) = 0 := by
  rw [← Matrix.mul_assoc (E * A) ((1 - E) * A) (1 - E),
    ← Matrix.mul_assoc (E * A) (1 - E) A, r1 A E hE h, Matrix.zero_mul, Matrix.zero_mul]

lemma t2 (A E : Matrix (Fin n) (Fin n) R) (hE : E * E = E) (h : E * A = A * E) :
    (1 - E) * ((1 - E) * A * (1 - E)) = (1 - E) * A := by
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, h1E1 E hE, r3 A E hE h]

lemma t5 (A E : Matrix (Fin n) (Fin n) R) (hE : E * E = E) : E * (E * A) = E * A := by
  rw [← Matrix.mul_assoc, hE]

lemma t3 (A E : Matrix (Fin n) (Fin n) R) (hE : E * E = E) (h : E * A = A * E) :
    ((1 - E) * A * (1 - E)) * (E * A) = 0 := by
  rw [Matrix.mul_assoc, ← Matrix.mul_assoc (1 - E) E A, hE1 E hE, Matrix.zero_mul,
    Matrix.mul_zero]

lemma t4 (A E : Matrix (Fin n) (Fin n) R) (hE : E * E = E) (h : E * A = A * E) :
    ((1 - E) * A * (1 - E)) * (1 - E) = (1 - E) * A := by
  rw [Matrix.mul_assoc, h1E1 E hE, r3 A E hE h]

/-- Decomposition of a matrix commuting with an idempotent into the two compressed blocks. -/
lemma comp_E (A E : Matrix (Fin n) (Fin n) R) (hE : E * E = E) (h : E * A = A * E) :
    A = E * A + (1 - E) * A * (1 - E) := by
  calc A = (E + (1 - E)) * A * (E + (1 - E)) := by
        rw [add_sub_cancel, Matrix.one_mul, Matrix.mul_one]
    _ = ((E + (1 - E)) * A) * E + ((E + (1 - E)) * A) * (1 - E) := by rw [Matrix.mul_add]
    _ = (E * A + (1 - E) * A) * E + (E * A + (1 - E) * A) * (1 - E) := by
        simp only [Matrix.add_mul]
    _ = (E * A * E + (1 - E) * A * E) + (E * A * (1 - E) + (1 - E) * A * (1 - E)) := by
        simp only [Matrix.add_mul]
    _ = (E * A + 0) + (0 + (1 - E) * A * (1 - E)) := by
        simp only [rE A E hE h, r2 A E hE h, r1 A E hE h]
    _ = E * A + (1 - E) * A * (1 - E) := by abel

/-- **The linear factorisation, first order.** -/
lemma mul_comp (A E : Matrix (Fin n) (Fin n) R) (hE : E * E = E) (h : E * A = A * E) :
    (E * A + (1 - E)) * (E + (1 - E) * A * (1 - E)) = A := by
  have step : (E * A + (1 - E)) * (E + (1 - E) * A * (1 - E))
      = (E * A + 0) + (0 + (1 - E) * A) := by
    simp only [Matrix.mul_add, Matrix.add_mul, rE A E hE h, hE1 E hE, t1 A E hE h,
      t2 A E hE h]
  rw [step]
  have e2 : (E * A + 0) + (0 + (1 - E) * A) = E * A + (1 - E) * A := by abel
  rw [e2, rsum A E]

/-- **The linear factorisation, second order.** -/
lemma mul_comp' (A E : Matrix (Fin n) (Fin n) R) (hE : E * E = E) (h : E * A = A * E) :
    (E + (1 - E) * A * (1 - E)) * (E * A + (1 - E)) = A := by
  have step : (E + (1 - E) * A * (1 - E)) * (E * A + (1 - E))
      = (E * A + 0) + (0 + (1 - E) * A) := by
    simp only [Matrix.add_mul, Matrix.mul_add, t5 A E hE, h1E E hE, t3 A E hE h, t4 A E hE h]
  rw [step]
  have e2 : (E * A + 0) + (0 + (1 - E) * A) = E * A + (1 - E) * A := by abel
  rw [e2, rsum A E]

end KL

/-! ## The pull-back calculus for `C(X, ℂ) → C(X × S¹, ℂ)` -/

variable (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X]

lemma klP_mul {n : ℕ} (A B : Matrix (Fin n) (Fin n) C(X, ℂ)) :
    klP X (A * B) = klP X A * klP X B := by
  simp only [klP, pullMat]
  exact (Work.KT.Matrix.map_mul'
    ((Work.KT.pullAlg (ContinuousMap.fst : C(X × Sph ℂ, X))).toRingHom) A B).symm

lemma klP_one {n : ℕ} : klP X (1 : Matrix (Fin n) (Fin n) C(X, ℂ)) = 1 := by
  simp only [klP, pullMat]
  refine Matrix.map_one (fun f : C(X, ℂ) => f.comp (ContinuousMap.fst : C(X × Sph ℂ, X))) ?_ ?_ <;>
    · ext p
      rfl

lemma klP_sub {n : ℕ} (A B : Matrix (Fin n) (Fin n) C(X, ℂ)) :
    klP X (A - B) = klP X A - klP X B := by
  simp only [klP, pullMat]
  rw [Matrix.map_sub]
  intro a b; rfl

lemma klP_add {n : ℕ} (A B : Matrix (Fin n) (Fin n) C(X, ℂ)) :
    klP X (A + B) = klP X A + klP X B := by
  simp only [klP, pullMat]
  rw [Matrix.map_add]
  intro a b; rfl

/-- The scalar matrix `z • 1` is central. -/
lemma smul_one_mul {n : ℕ} (M : Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ)) :
    (klz X • (1 : Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ))) * M
      = M * (klz X • (1 : Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ))) := by
  rw [Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul, Matrix.mul_one]

/-- The idempotence of the pull-back of `E`. -/
lemma klP_isIdem {n : ℕ} (E : Matrix (Fin n) (Fin n) C(X, ℂ)) (hE : E * E = E) :
    klP X E * klP X E = klP X E := by
  rw [← klP_mul, hE]

/-- `klP E` commutes with the pulled-back clutching function. -/
lemma klP_comm {n : ℕ} (b E : Matrix (Fin n) (Fin n) C(X, ℂ)) (hc : E * b = b * E) :
    klP X E * (klz X • 1 + klP X b) = (klz X • 1 + klP X b) * klP X E := by
  rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul,
    Matrix.one_mul, ← klP_mul, ← klP_mul, hc]

/-- `klP E` commutes with the pull-back of `b`. -/
lemma klP_comm_b {n : ℕ} (b E : Matrix (Fin n) (Fin n) C(X, ℂ)) (hc : E * b = b * E) :
    klP X E * klP X b = klP X b * klP X E := by
  rw [← klP_mul, ← klP_mul, hc]

/-- `klV` is the compression of the clutching function to the range of `E`. -/
lemma klV_eq {n : ℕ} (b E : Matrix (Fin n) (Fin n) C(X, ℂ)) :
    klV X n b E = klP X E * (klz X • 1 + klP X b) + (1 - klP X E) := by
  simp only [klV, klP_mul, Matrix.mul_add, Matrix.mul_smul, Matrix.mul_one]

/-- The `E`-compression of `(1 - E) * (z • 1 + b) * (1 - E)`: the second compression only sees
the "outside" part of `b`, and the scalar `z` survives. -/
lemma klW_block {n : ℕ} (b E : Matrix (Fin n) (Fin n) C(X, ℂ)) (hE : E * E = E)
    (hc : E * b = b * E) :
    (1 - klP X E) * (klz X • 1 + klP X b) * (1 - klP X E)
      = klz X • (1 - klP X E) + (1 - klP X E) * klP X b := by
  have h1 : (1 - klP X E) * (klz X • 1 + klP X b)
      = klz X • (1 - klP X E) + (1 - klP X E) * klP X b := by
    rw [Matrix.mul_add, Matrix.mul_smul, Matrix.mul_one]
  rw [h1, Matrix.add_mul, Matrix.smul_mul, KL.h1E1 (klP X E) (klP_isIdem X E hE),
    KL.r3 (klP X b) (klP X E) (klP_isIdem X E hE) (klP_comm_b X b E hc)]

/-- `klW` is the complementary compression of the clutching function, plus `E`. -/
lemma klW_eq {n : ℕ} (b E : Matrix (Fin n) (Fin n) C(X, ℂ)) (hE : E * E = E) (hc : E * b = b * E) :
    klW X n b E = klP X E + (1 - klP X E) * (klz X • 1 + klP X b) * (1 - klP X E) := by
  have h1 : klW X n b E
      = klP X E + (klz X • (1 - klP X E) + (1 - klP X E) * klP X b) := by
    simp only [klW, klP_mul, klP_sub, klP_one]
    abel
  rw [h1, klW_block X b E hE hc]

/-- The Bott unit in the form in which `kappa_bottKL` consumes it. -/
lemma klV0_eq {n : ℕ} (E : Matrix (Fin n) (Fin n) C(X, ℂ)) :
    klV0 X n E = pullMat X (1 - E) + (zUnit X : C(X × Sph ℂ, ℂ)) • pullMat X E := by
  show klz X • klP X E + (1 - klP X E)
    = pullMat X (1 - E) + (zUnit X : C(X × Sph ℂ, ℂ)) • pullMat X E
  rw [show pullMat X (1 - E) + (zUnit X : C(X × Sph ℂ, ℂ)) • pullMat X E
      = klP X (1 - E) + klz X • klP X E from rfl, klP_sub, klP_one]
  abel

/-- **The linear splitting of the clutching function `z • 1 + pullMat b`.** -/
theorem kl_factor {n : ℕ} (b E : Matrix (Fin n) (Fin n) C(X, ℂ)) (hE : E * E = E)
    (hc : E * b = b * E) :
    klV X n b E * klW X n b E
      = klz X • (1 : Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ)) + klP X b := by
  rw [klV_eq X b E, klW_eq X b E hE hc,
    KL.mul_comp (klz X • 1 + klP X b) (klP X E) (klP_isIdem X E hE) (klP_comm X b E hc)]

/-- The two factors commute (so `kappa_mul_comm` applies). -/
theorem kl_factor_comm {n : ℕ} (b E : Matrix (Fin n) (Fin n) C(X, ℂ)) (hE : E * E = E)
    (hc : E * b = b * E) :
    klV X n b E * klW X n b E = klW X n b E * klV X n b E := by
  rw [klV_eq X b E, klW_eq X b E hE hc,
    KL.mul_comp (klz X • 1 + klP X b) (klP X E) (klP_isIdem X E hE) (klP_comm X b E hc),
    KL.mul_comp' (klz X • 1 + klP X b) (klP X E) (klP_isIdem X E hE) (klP_comm X b E hc)]

end

end Work.KT.Fund
