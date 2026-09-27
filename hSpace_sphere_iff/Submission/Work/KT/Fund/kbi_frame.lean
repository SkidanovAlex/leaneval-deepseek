import Mathlib
import Submission.Work.KT.Fund.kbi_defs

/-!
# `Work.KT.Fund.kbi_frame`

The frame identities for the K-theoretic Bott construction of `Work.KT.Fund.kappa_bott`.

`SA1p`, `TB1p` (resp. `SA2p`, `TB2p`) are a retraction and a frame of the target module over the
first (resp. second) disc: `SA_i * TB_i = 1`, and the idempotent `TB_i * SA_i` is the disc image
`W_i` of the target idempotent.  All four identities are proved by rewriting into a `2 × 2` block
calculus (`KBIFrameBlk.stk`, `KBIFrameBlk.ustk`, `KBIFrameBlk.blk`) and reducing to the elementary algebra of the
scalar matrix `Pd` and its complement `Qd = 1 - Pd` supplied by `Work.KT.Fund.KBI`.

This file is sorry-free.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace Work.KT.Fund

open scoped Kronecker

/-! ## A `2 × 2` block calculus for `Fin m × Fin 2`-indexed matrices -/

namespace KBIFrameBlk

variable {R : Type*} [CommRing R] {m : ℕ}

/-- The vertical stack of two `m × m` blocks. -/
def stk (A B : Matrix (Fin m) (Fin m) R) : Matrix (Fin m × Fin 2) (Fin m) R :=
  Matrix.of fun a j => if a.2 = 0 then A a.1 j else B a.1 j

/-- The horizontal stack of two `m × m` blocks. -/
def ustk (A B : Matrix (Fin m) (Fin m) R) : Matrix (Fin m) (Fin m × Fin 2) R :=
  Matrix.of fun i a => if a.2 = 0 then A i a.1 else B i a.1

/-- The `2 × 2` block matrix with blocks `A B C D`. -/
def blk (A B C D : Matrix (Fin m) (Fin m) R) : Matrix (Fin m × Fin 2) (Fin m × Fin 2) R :=
  Matrix.of fun a b => if a.2 = 0 then (if b.2 = 0 then A a.1 b.1 else B a.1 b.1)
                              else (if b.2 = 0 then C a.1 b.1 else D a.1 b.1)

lemma ustk_mul_stk (A B C D : Matrix (Fin m) (Fin m) R) :
    ustk A B * stk C D = A * C + B * D := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.add_apply, ustk, stk, Matrix.of_apply]
  rw [Fintype.sum_prod_type]
  simp [Fin.sum_univ_two, Finset.sum_add_distrib]

lemma stk_mul_ustk (A B C D : Matrix (Fin m) (Fin m) R) :
    stk C D * ustk A B = blk (C * A) (C * B) (D * A) (D * B) := by
  ext a b
  simp only [Matrix.mul_apply, stk, ustk, blk, Matrix.of_apply]
  rcases a with ⟨ai, ae⟩
  rcases b with ⟨bi, be⟩
  fin_cases ae <;> fin_cases be <;> simp

lemma blk_congr {A A' B B' C C' D D' : Matrix (Fin m) (Fin m) R}
    (hA : A = A') (hB : B = B') (hC : C = C') (hD : D = D') :
    blk A B C D = blk A' B' C' D' := by rw [hA, hB, hC, hD]

end KBIFrameBlk

/-! ## The KBI-specific algebra -/

namespace KBIFrameAux

open Work.KT.Fund.KBI

variable (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X]
variable (m : ℕ) (P : Matrix (Fin m) (Fin m) C(X, ℂ))

lemma D0D1 (M N : Matrix (Fin m) (Fin m) (kdD X)) :
    D0 X m * M + D1 X m * N = KBIFrameBlk.stk M N := by
  ext a j
  rcases a with ⟨ai, ae⟩
  fin_cases ae <;> simp [Matrix.mul_apply, KBIFrameBlk.stk]

lemma D0_add_D1_mul (N : Matrix (Fin m) (Fin m) (kdD X)) :
    D0 X m + D1 X m * N = KBIFrameBlk.stk (1 : Matrix (Fin m) (Fin m) (kdD X)) N := by
  ext a j
  rcases a with ⟨ai, ae⟩
  fin_cases ae <;> simp [Matrix.mul_apply, Matrix.one_apply, KBIFrameBlk.stk]

lemma R0R1 (M N : Matrix (Fin m) (Fin m) (kdD X)) :
    M * R0 X m + N * R1 X m = KBIFrameBlk.ustk M N := by
  ext i a
  rcases a with ⟨ai, ae⟩
  fin_cases ae <;> simp [Matrix.mul_apply, KBIFrameBlk.ustk]

/-! ### The `sm` calculus (`sm a` is the entrywise product `a • Pd`) -/

lemma sm_mul_sm (hP : P * P = P) (a b : kdD X) :
    sm X m P a * sm X m P b = sm X m P (a * b) := by
  apply Matrix.ext; intro i j
  simp only [Matrix.mul_apply, sm, Matrix.of_apply]
  have key : ∀ k : Fin m, a * Pd X m P i k * (b * Pd X m P k j)
      = a * b * (Pd X m P i k * Pd X m P k j) := fun k => by ring
  rw [Finset.sum_congr rfl (fun k _ => key k)]
  rw [← Finset.mul_sum]
  congr 1
  rw [← Matrix.mul_apply, Pd_sq X m P hP]

lemma sm_mul_Pd (hP : P * P = P) (a : kdD X) : sm X m P a * Pd X m P = sm X m P a := by
  rw [← sm_one X m P hP, sm_mul_sm X m P hP a 1, mul_one]

lemma Pd_mul_sm (hP : P * P = P) (a : kdD X) : Pd X m P * sm X m P a = sm X m P a := by
  rw [← sm_one X m P hP, sm_mul_sm X m P hP 1 a, one_mul]

lemma Pd_mul_Qd (hP : P * P = P) : Pd X m P * Qd X m P = 0 := by
  rw [Qd, Matrix.mul_sub, Matrix.mul_one, Pd_sq X m P hP, sub_self]

lemma Qd_mul_Pd (hP : P * P = P) : Qd X m P * Pd X m P = 0 := by
  rw [Qd, Matrix.sub_mul, Matrix.one_mul, Pd_sq X m P hP, sub_self]

lemma Qd_mul_Qd (hP : P * P = P) : Qd X m P * Qd X m P = Qd X m P := by
  rw [Qd, Matrix.mul_sub, Matrix.mul_one, Matrix.sub_mul, Matrix.one_mul,
    Pd_sq X m P hP, sub_self, sub_zero]

lemma sm_mul_Qd (hP : P * P = P) (a : kdD X) : sm X m P a * Qd X m P = 0 := by
  rw [Qd, Matrix.mul_sub, Matrix.mul_one, sm_mul_Pd X m P hP a, sub_self]

lemma Qd_mul_sm (hP : P * P = P) (a : kdD X) : Qd X m P * sm X m P a = 0 := by
  rw [Qd, Matrix.sub_mul, Matrix.one_mul, Pd_mul_sm X m P hP a, sub_self]

/-! ### The frames, retractions and disc images as blocks -/

lemma TB1p_eq :
    TB1p X m P = KBIFrameBlk.stk (1 : Matrix (Fin m) (Fin m) (kdD X)) (sm X m P (zc X)) := by
  rw [TB1p]
  exact D0_add_D1_mul X m (sm X m P (zc X))

lemma TB2p_eq : TB2p X m P = KBIFrameBlk.stk (Qd X m P + sm X m P (zcb X)) (Pd X m P) := by
  rw [TB2p]
  exact D0D1 X m (Qd X m P + sm X m P (zcb X)) (Pd X m P)

lemma SA1p_eq :
    SA1p X m P = KBIFrameBlk.ustk (Qd X m P + sm X m P (zcn X)) (sm X m P (zcn X * zcb X)) := by
  rw [SA1p]
  exact R0R1 X m (Qd X m P + sm X m P (zcn X)) (sm X m P (zcn X * zcb X))

lemma SA2p_eq :
    SA2p X m P = KBIFrameBlk.ustk (Qd X m P + sm X m P (zcn X * zc X)) (sm X m P (zcn X)) := by
  rw [SA2p]
  exact R0R1 X m (Qd X m P + sm X m P (zcn X * zc X)) (sm X m P (zcn X))

lemma W1p_eq_blk : W1p X m P =
    KBIFrameBlk.blk (sm X m P (zcn X) + Qd X m P) (sm X m P (zcn X * zcb X))
      (sm X m P (zcn X * zc X)) (sm X m P (zcn X * zc X * zcb X)) := by
  apply Matrix.ext; intro a b
  rcases a with ⟨ai, ae⟩
  rcases b with ⟨bi, be⟩
  fin_cases ae <;> fin_cases be <;>
    simp [W1p, KBIFrameBlk.blk, sm, Qd, Matrix.kroneckerMap_apply, h1m, E00, Matrix.of_apply] <;> ring

lemma W2p_eq_blk : W2p X m P =
    KBIFrameBlk.blk (sm X m P (zcn X * zc X * zcb X) + Qd X m P) (sm X m P (zcn X * zcb X))
      (sm X m P (zcn X * zc X)) (sm X m P (zcn X)) := by
  apply Matrix.ext; intro a b
  rcases a with ⟨ai, ae⟩
  rcases b with ⟨bi, be⟩
  fin_cases ae <;> fin_cases be <;>
    simp [W2p, KBIFrameBlk.blk, sm, Qd, Matrix.kroneckerMap_apply, h2m, E00, Matrix.of_apply] <;> ring

/-! ### Boundary scalar identities -/

lemma zcn_add_zcb : zcn X + zcn X * zcb X * zc X = 1 := by
  calc zcn X + zcn X * zcb X * zc X = zcn X * (1 + zc X * zcb X) := by ring
    _ = 1 := zcn_mul_one_add X

lemma zcn_add_zcb' : zcn X * zc X * zcb X + zcn X = 1 := by
  calc zcn X * zc X * zcb X + zcn X = zcn X * (1 + zc X * zcb X) := by ring
    _ = 1 := zcn_mul_one_add X

/-! ### The four frame identities -/

lemma SA1p_mul_TB1p (hP : P * P = P) : SA1p X m P * TB1p X m P = 1 := by
  rw [SA1p_eq, TB1p_eq, KBIFrameBlk.ustk_mul_stk, Matrix.mul_one,
      sm_mul_sm X m P hP (zcn X * zcb X) (zc X),
      add_assoc, ← sm_add X m P (zcn X) (zcn X * zcb X * zc X), zcn_add_zcb X,
      sm_one X m P hP, add_comm (Qd X m P) (Pd X m P), Pd_add_Qd X m P]

lemma SA2p_mul_TB2p (hP : P * P = P) : SA2p X m P * TB2p X m P = 1 := by
  rw [SA2p_eq, TB2p_eq, KBIFrameBlk.ustk_mul_stk, Matrix.mul_add, Matrix.add_mul, Matrix.add_mul,
      Qd_mul_Qd X m P hP, sm_mul_Qd X m P hP, Qd_mul_sm X m P hP,
      sm_mul_sm X m P hP (zcn X * zc X) (zcb X), sm_mul_Pd X m P hP,
      add_zero, zero_add, add_assoc,
      ← sm_add X m P (zcn X * zc X * zcb X) (zcn X), zcn_add_zcb' X, sm_one X m P hP,
      add_comm (Qd X m P) (Pd X m P), Pd_add_Qd X m P]

lemma TB1p_mul_SA1p (hP : P * P = P) : TB1p X m P * SA1p X m P = W1p X m P := by
  rw [TB1p_eq, SA1p_eq, KBIFrameBlk.stk_mul_ustk, W1p_eq_blk]
  refine KBIFrameBlk.blk_congr ?_ ?_ ?_ ?_
  · rw [one_mul, add_comm (Qd X m P) (sm X m P (zcn X))]
  · rw [one_mul]
  · rw [Matrix.mul_add, sm_mul_Qd X m P hP, zero_add, sm_mul_sm X m P hP, mul_comm (zc X) (zcn X)]
  · rw [sm_mul_sm X m P hP, show zc X * (zcn X * zcb X) = zcn X * zc X * zcb X from by ring]

lemma TB2p_mul_SA2p (hP : P * P = P) : TB2p X m P * SA2p X m P = W2p X m P := by
  rw [TB2p_eq, SA2p_eq, KBIFrameBlk.stk_mul_ustk, W2p_eq_blk]
  refine KBIFrameBlk.blk_congr ?_ ?_ ?_ ?_
  · rw [Matrix.add_mul, Matrix.mul_add, Matrix.mul_add, Qd_mul_Qd X m P hP, Qd_mul_sm X m P hP,
        sm_mul_Qd X m P hP, sm_mul_sm X m P hP, add_zero, zero_add,
        show zcb X * (zcn X * zc X) = zcn X * zc X * zcb X from by ring,
        add_comm (Qd X m P) (sm X m P (zcn X * zc X * zcb X))]
  · rw [Matrix.add_mul, Qd_mul_sm X m P hP, zero_add, sm_mul_sm X m P hP,
        show zcb X * zcn X = zcn X * zcb X from by ring]
  · rw [Matrix.mul_add, Pd_mul_Qd X m P hP, zero_add, Pd_mul_sm X m P hP]
  · rw [Pd_mul_sm X m P hP]

end KBIFrameAux

theorem kbi_frame (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X]
    (n : ℕ) (P : Matrix (Fin n) (Fin n) C(X, ℂ)) (hP : P * P = P) :
    Work.KT.Fund.KBI.SA1p X n P * Work.KT.Fund.KBI.TB1p X n P = 1 ∧
      Work.KT.Fund.KBI.SA2p X n P * Work.KT.Fund.KBI.TB2p X n P = 1 ∧
      Work.KT.Fund.KBI.TB1p X n P * Work.KT.Fund.KBI.SA1p X n P = Work.KT.Fund.KBI.W1p X n P ∧
      Work.KT.Fund.KBI.TB2p X n P * Work.KT.Fund.KBI.SA2p X n P = Work.KT.Fund.KBI.W2p X n P :=
  ⟨KBIFrameAux.SA1p_mul_TB1p X n P hP, KBIFrameAux.SA2p_mul_TB2p X n P hP,
    KBIFrameAux.TB1p_mul_SA1p X n P hP, KBIFrameAux.TB2p_mul_SA2p X n P hP⟩

end Work.KT.Fund
