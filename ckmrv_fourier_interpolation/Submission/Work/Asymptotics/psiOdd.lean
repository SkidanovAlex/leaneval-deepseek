import Mathlib
import Submission.Work.FreeProduct.shiftedDefs
import Submission.Work.FreeProduct.Bridge
import Submission.Work.Residues.Basic
import Submission.Work.Kernels.GroupAlgebra
import Submission.Work.Residues.XiTransfer
import Submission.Work.Modular.presentedGroup_equiv_PSL

namespace Work.Asymptotics

open Work.Kernels
open Work.FreeProduct (RR X Y Y2 TT Tnu x y y2)
open Work.Modular.PresGroup (Cyc C2 C3 FP gC2 gC3 ofFree)
open scoped MonoidAlgebra MatrixGroups

noncomputable section

/-! ## The idempotents `e₊ = 2⁻¹(1 + z)` and `e₋ = 2⁻¹(1 - z)` -/

/-- The idempotent `e₊ = 2⁻¹(1 + z)` of the even part `R e₊`. -/
def ePlus : R := (2⁻¹ : ℂ) • (1 + Work.Residues.Rneg)

/-- The idempotent `e₋ = 2⁻¹(1 - z)`; `R e₋` is the odd part of `R = ℂ[SL(2,ℤ)]`. -/
def eMinus : R := (2⁻¹ : ℂ) • (1 - Work.Residues.Rneg)

/-- `(c • x) * (d • y) = (c * d) • (x * y)` in a `ℂ`-algebra. -/
lemma smul_mul_smul (c d : ℂ) (x y : R) : (c • x) * (d • y) = (c * d) • (x * y) := by
  rw [Algebra.smul_mul_assoc, Algebra.mul_smul_comm, smul_smul]

lemma ePlus_add_eMinus : ePlus + eMinus = (1 : R) := by
  rw [ePlus, eMinus, ← smul_add]
  have h : (1 + Work.Residues.Rneg) + (1 - Work.Residues.Rneg) = (2 : ℂ) • (1 : R) := by
    module
  rw [h, smul_smul]
  norm_num

lemma eMinus_sq : eMinus * eMinus = eMinus := by
  rw [eMinus, smul_mul_smul]
  have h : (1 - Work.Residues.Rneg) * (1 - Work.Residues.Rneg)
      = (2 : ℂ) • (1 - Work.Residues.Rneg) := by
    have h1 : (1 - Work.Residues.Rneg) * (1 - Work.Residues.Rneg)
        = 1 - Work.Residues.Rneg - Work.Residues.Rneg
          + Work.Residues.Rneg * Work.Residues.Rneg := by noncomm_ring
    rw [h1, Work.Residues.Rneg_mul_Rneg]
    module
  rw [h, smul_smul]
  norm_num

lemma ePlus_sq : ePlus * ePlus = ePlus := by
  rw [ePlus, smul_mul_smul]
  have h : (1 + Work.Residues.Rneg) * (1 + Work.Residues.Rneg)
      = (2 : ℂ) • (1 + Work.Residues.Rneg) := by
    have h1 : (1 + Work.Residues.Rneg) * (1 + Work.Residues.Rneg)
        = 1 + Work.Residues.Rneg + Work.Residues.Rneg
          + Work.Residues.Rneg * Work.Residues.Rneg := by noncomm_ring
    rw [h1, Work.Residues.Rneg_mul_Rneg]
    module
  rw [h, smul_smul]
  norm_num

lemma eMinus_mul_ePlus : eMinus * ePlus = 0 := by
  rw [eMinus, ePlus, smul_mul_smul]
  have h : (1 - Work.Residues.Rneg) * (1 + Work.Residues.Rneg) = 0 := by
    have h1 : (1 - Work.Residues.Rneg) * (1 + Work.Residues.Rneg)
        = 1 - Work.Residues.Rneg * Work.Residues.Rneg := by noncomm_ring
    rw [h1, Work.Residues.Rneg_mul_Rneg, sub_self]
  rw [h, smul_zero]

lemma ePlus_mul_eMinus : ePlus * eMinus = 0 := by
  rw [ePlus, eMinus, smul_mul_smul]
  have h : (1 + Work.Residues.Rneg) * (1 - Work.Residues.Rneg) = 0 := by
    have h1 : (1 + Work.Residues.Rneg) * (1 - Work.Residues.Rneg)
        = 1 - Work.Residues.Rneg * Work.Residues.Rneg := by noncomm_ring
    rw [h1, Work.Residues.Rneg_mul_Rneg, sub_self]
  rw [h, smul_zero]

lemma one_sub_Rneg_mul_Rneg :
    (1 - Work.Residues.Rneg) * Work.Residues.Rneg = -(1 - Work.Residues.Rneg) := by
  have h2 : (1 - Work.Residues.Rneg) * Work.Residues.Rneg
      = Work.Residues.Rneg - Work.Residues.Rneg * Work.Residues.Rneg := by noncomm_ring
  rw [h2, Work.Residues.Rneg_mul_Rneg]
  abel

lemma eMinus_mul_Rneg : eMinus * Work.Residues.Rneg = -eMinus := by
  rw [eMinus, Algebra.smul_mul_assoc, one_sub_Rneg_mul_Rneg, smul_neg]

lemma Rneg_mul_eMinus : Work.Residues.Rneg * eMinus = -eMinus := by
  rw [eMinus, Algebra.mul_smul_comm, Work.Residues.Rneg_comm,
    one_sub_Rneg_mul_Rneg, smul_neg]

lemma eMinus_comm (r : R) : eMinus * r = r * eMinus := by
  rw [eMinus, Algebra.smul_mul_assoc, Algebra.mul_smul_comm]
  congr 1
  simp only [sub_mul, mul_sub, one_mul, mul_one, Work.Residues.Rneg_comm]

lemma ePlus_comm (r : R) : ePlus * r = r * ePlus := by
  rw [ePlus, Algebra.smul_mul_assoc, Algebra.mul_smul_comm]
  congr 1
  simp only [add_mul, mul_add, one_mul, mul_one, Work.Residues.Rneg_comm]

lemma eMinus_add_ePlus : eMinus + ePlus = (1 : R) := by
  rw [add_comm, ePlus_add_eMinus]

/-- The odd part `{A | A z = -A}` is the image of `e₋`. -/
lemma mul_Rneg_eq_neg_iff (A : R) : A * Work.Residues.Rneg = -A ↔ A = A * eMinus := by
  constructor
  · intro h
    have h1 : A * eMinus = A := by
      rw [eMinus, Algebra.mul_smul_comm, mul_sub, mul_one, h]
      rw [show (A - -A : R) = (2 : ℂ) • A by module]
      rw [smul_smul]
      norm_num
    exact h1.symm
  · intro h
    rw [h, mul_assoc, eMinus_mul_Rneg, mul_neg, ← h]

/-! ## The units `u = i·(S e₋) + e₊` and `v = -(ST e₋) + e₊` of `R` -/

/-- Sandwich: `(x e₋)(y e₋) = (x y) e₋`. -/
lemma mul_eMinus_mul (x y : R) : (x * eMinus) * (y * eMinus) = (x * y) * eMinus := by
  calc (x * eMinus) * (y * eMinus)
      = x * (eMinus * (y * eMinus)) := by rw [mul_assoc]
    _ = x * ((eMinus * y) * eMinus) := by rw [← mul_assoc eMinus y eMinus]
    _ = x * ((y * eMinus) * eMinus) := by rw [eMinus_comm y]
    _ = x * (y * (eMinus * eMinus)) := by rw [mul_assoc y eMinus eMinus]
    _ = x * (y * eMinus) := by rw [eMinus_sq]
    _ = (x * y) * eMinus := by rw [← mul_assoc x y eMinus]

/-- `(x e₋)^(n+1) = x^(n+1) e₋`. -/
lemma mul_eMinus_pow (x : R) (n : ℕ) : (x * eMinus) ^ (n + 1) = x ^ (n + 1) * eMinus := by
  induction n with
  | zero => rw [Nat.zero_add, pow_one, pow_one]
  | succ n ih =>
    rw [show n + 1 + 1 = (n + 1) + 1 from rfl, pow_succ, ih, mul_eMinus_mul, ← pow_succ]

/-- `(c • (x e₋))² = (c·c) • ((x·x) e₋)`. -/
lemma smul_eMinus_sq (c : ℂ) (x : R) :
    (c • (x * eMinus)) * (c • (x * eMinus)) = (c * c) • ((x * x) * eMinus) := by
  rw [smul_mul_smul, mul_eMinus_mul]

/-- `(c • (x e₋))³ = (c·c·c) • ((x·x·x) e₋)`. -/
lemma smul_eMinus_cube (c : ℂ) (x : R) :
    (c • (x * eMinus)) * (c • (x * eMinus)) * (c • (x * eMinus))
      = (c * c * c) • ((x * x * x) * eMinus) := by
  rw [smul_eMinus_sq, smul_mul_smul, mul_eMinus_mul]

lemma mul_self_self (a : R) : a * a * a = a ^ 3 := by
  rw [pow_succ, pow_two]

/-- `(a + p)² = a² + p` for a central idempotent `p` with `a p = p a = 0`. -/
lemma sq_of_add_idem {p a : R} (hp : p * p = p) (h : a * p = 0) (h' : p * a = 0) :
    (a + p) * (a + p) = a * a + p := by
  rw [add_mul, mul_add, mul_add, h, h', hp]
  abel

lemma mul_mul_eq_zero {a p : R} (h : a * p = 0) : (a * a) * p = 0 := by
  rw [mul_assoc, h, mul_zero]

/-- `(a + p)³ = a³ + p` for a central idempotent `p` with `a p = p a = 0`. -/
lemma cube_of_add_idem {p a : R} (hp : p * p = p) (h : a * p = 0) (h' : p * a = 0) :
    (a + p) * (a + p) * (a + p) = a * a * a + p := by
  rw [sq_of_add_idem hp h h', add_mul, mul_add, mul_add, mul_mul_eq_zero h, h', hp]
  abel

/-- `(ST)³ = z` in `R`. -/
lemma R_S_mul_R_T_cube : (R_S * R_T) ^ 3 = Work.Residues.Rneg := by
  have h : (ModularGroup.S * ModularGroup.T : SL(2,ℤ)) ^ 3 = -1 := by decide
  rw [show (R_S * R_T : R) = MonoidAlgebra.of ℂ (SL(2,ℤ)) (ModularGroup.S * ModularGroup.T)
      from by rw [R_S, R_T, map_mul]; rfl,
    ← map_pow, h, Work.Residues.Rneg_eq_of]

/-- The element `u = i·(S e₋) + e₊` of `R`; it is an involution. -/
def uu : R := Complex.I • (R_S * eMinus) + ePlus

/-- The element `v = -(ST e₋) + e₊` of `R`; it has order three. -/
def vv : R := (-1 : ℂ) • ((R_S * R_T) * eMinus) + ePlus

lemma smul_eMinus_mul_ePlus (c : ℂ) (x : R) : (c • (x * eMinus)) * ePlus = 0 := by
  rw [Algebra.smul_mul_assoc, mul_assoc, eMinus_mul_ePlus, mul_zero, smul_zero]

lemma ePlus_mul_smul_eMinus (c : ℂ) (x : R) : ePlus * (c • (x * eMinus)) = 0 := by
  rw [Algebra.mul_smul_comm, ← mul_assoc, ePlus_comm x, mul_assoc, ePlus_mul_eMinus,
    mul_zero, smul_zero]

lemma I_mul_I' : (Complex.I * Complex.I : ℂ) = -1 := Complex.I_mul_I

lemma uu_mul_uu : uu * uu = 1 := by
  rw [uu, sq_of_add_idem ePlus_sq (smul_eMinus_mul_ePlus Complex.I R_S)
    (ePlus_mul_smul_eMinus Complex.I R_S), smul_eMinus_sq, I_mul_I']
  rw [show (R_S * R_S : R) = Work.Residues.Rneg from Work.Residues.R_S_mul_R_S_eq]
  rw [show (-1 : ℂ) • (Work.Residues.Rneg * eMinus) = eMinus by
    rw [Rneg_mul_eMinus, neg_smul, one_smul, neg_neg]]
  rw [eMinus_add_ePlus]

lemma vv_cube : vv ^ 3 = 1 := by
  have ha : ((-1 : ℂ) • ((R_S * R_T) * eMinus)) * ((-1 : ℂ) • ((R_S * R_T) * eMinus))
      * ((-1 : ℂ) • ((R_S * R_T) * eMinus)) = eMinus := by
    rw [smul_eMinus_cube]
    rw [show ((-1 : ℂ) * -1 * -1) = -1 by norm_num, neg_smul, one_smul,
      show (R_S * R_T) * (R_S * R_T) * (R_S * R_T) = (R_S * R_T) ^ 3 by
        rw [mul_self_self],
      R_S_mul_R_T_cube, Rneg_mul_eMinus, neg_neg]
  rw [show vv ^ 3 = vv * vv * vv by rw [pow_succ, pow_succ, pow_one], vv]
  rw [cube_of_add_idem ePlus_sq (smul_eMinus_mul_ePlus (-1) (R_S * R_T))
    (ePlus_mul_smul_eMinus (-1) (R_S * R_T))]
  rw [ha, eMinus_add_ePlus]

/-! ## The algebra homomorphism `psi : ℂ[ℤ/2 ∗ ℤ/3] → R` with `X ↦ u`, `Y ↦ v` -/

/-- The homomorphism `ℤ/n →* M` sending the generator to `g`, for `g ^ n = 1`. -/
def cycHom {M : Type*} [Monoid M] (n : ℕ) [NeZero n] (g : M) (hg : g ^ n = 1) :
    Multiplicative (ZMod n) →* M where
  toFun x := g ^ x.toAdd.val
  map_one' := by simp
  map_mul' x y := by
    show g ^ (x * y).toAdd.val = g ^ x.toAdd.val * g ^ y.toAdd.val
    rw [toAdd_mul, ZMod.val_add, ← pow_eq_pow_mod _ hg, pow_add]

/-- The monoid homomorphism `FP →* R` with `x ↦ u` and `y ↦ v`. -/
def phiFP : FP →* R :=
  Monoid.CoprodI.lift fun b : Bool =>
    match b with
    | false => cycHom 2 uu (by rw [pow_two]; exact uu_mul_uu)
    | true => cycHom 3 vv vv_cube

/-- The algebra homomorphism `ℂ[ℤ/2 ∗ ℤ/3] →ₐ[ℂ] R` with `X ↦ u` and `Y ↦ v`. -/
def psi : RR →ₐ[ℂ] R := MonoidAlgebra.lift ℂ R FP phiFP

/-- The odd component `a ↦ psi a · e₋`, an algebra homomorphism onto `R e₋`. -/
def psiM (a : RR) : R := psi a * eMinus

lemma psi_X : psi X = uu := by
  rw [X, Work.FreeProduct.x, gC2]
  simp only [psi, phiFP, MonoidAlgebra.lift_of, Monoid.CoprodI.lift_of]
  change uu ^ (Multiplicative.ofAdd 1 : C2).toAdd.val = uu
  rw [show (Multiplicative.ofAdd 1 : C2).toAdd.val = 1 from rfl, pow_one]

lemma psi_Y : psi Y = vv := by
  rw [Y, Work.FreeProduct.y, gC3]
  simp only [psi, phiFP, MonoidAlgebra.lift_of, Monoid.CoprodI.lift_of]
  change vv ^ (Multiplicative.ofAdd 1 : C3).toAdd.val = vv
  rw [show (Multiplicative.ofAdd 1 : C3).toAdd.val = 1 from rfl, pow_one]

lemma psi_TT : psi TT = uu * vv := by
  rw [show TT = X * Y from Work.FreeProduct.X_mul_Y.symm, map_mul, psi_X, psi_Y]

lemma psiM_mul (a b : RR) : psiM (a * b) = psiM a * psiM b := by
  rw [psiM, psiM, psiM, map_mul]
  exact (mul_eMinus_mul (psi a) (psi b)).symm

lemma psiM_add (a b : RR) : psiM (a + b) = psiM a + psiM b := by
  rw [psiM, psiM, psiM, map_add, add_mul]

lemma psiM_smul (c : ℂ) (a : RR) : psiM (c • a) = c • psiM a := by
  rw [psiM, psiM, map_smul, Algebra.smul_mul_assoc]

lemma psiM_one : psiM (1 : RR) = eMinus := by
  rw [psiM, map_one, one_mul]

lemma psiM_X : psiM X = Complex.I • (R_S * eMinus) := by
  rw [psiM, psi_X, uu, add_mul, Algebra.smul_mul_assoc, mul_assoc, eMinus_sq,
    ePlus_mul_eMinus, add_zero]

lemma psiM_Y : psiM Y = -((R_S * R_T) * eMinus) := by
  rw [psiM, psi_Y, vv, add_mul, Algebra.smul_mul_assoc, mul_assoc, eMinus_sq,
    ePlus_mul_eMinus, add_zero, neg_smul, one_smul]

lemma psiM_TT : psiM TT = Complex.I • (R_T * eMinus) := by
  have h : (Complex.I • (R_S * eMinus)) * ((-1 : ℂ) • ((R_S * R_T) * eMinus))
      = Complex.I • (R_T * eMinus) := by
    calc (Complex.I • (R_S * eMinus)) * ((-1 : ℂ) • ((R_S * R_T) * eMinus))
        = (Complex.I * -1) • ((R_S * eMinus) * ((R_S * R_T) * eMinus)) := by
          rw [smul_mul_smul]
      _ = (Complex.I * -1) • ((R_S * (R_S * R_T)) * eMinus) := by rw [mul_eMinus_mul]
      _ = Complex.I • (R_T * eMinus) := by
          rw [show Complex.I * -1 = -Complex.I by ring, neg_smul]
          rw [show ((R_S * (R_S * R_T)) * eMinus) = -(R_T * eMinus) by
            rw [← mul_assoc R_S R_S R_T, Work.Residues.R_S_mul_R_S_eq,
              Work.Residues.Rneg_comm R_T, mul_assoc, Rneg_mul_eMinus, mul_neg]]
          rw [smul_neg, neg_neg]
  rw [show TT = X * Y from Work.FreeProduct.X_mul_Y.symm, psiM_mul, psiM_X, psiM_Y,
    show -(R_S * R_T * eMinus) = (-1 : ℂ) • (R_S * R_T * eMinus) by
      rw [neg_smul, one_smul], h]

/-! ## The values of `psiM` on the letters `x`, `y`, `y²` -/

lemma of_of_C2 (m : C2) (hm : m ≠ 1) :
    Monoid.CoprodI.of (i := false) m = x := by
  have hx1 : m = Multiplicative.ofAdd 1 := by revert m hm; decide
  rw [hx1]; rfl

lemma of_of_C3 (m : C3) (hm : m ≠ 1) :
    Monoid.CoprodI.of (i := true) m = y ∨ Monoid.CoprodI.of (i := true) m = y2 := by
  have hx1 : m = Multiplicative.ofAdd 1 ∨ m = Multiplicative.ofAdd 2 := by revert m hm; decide
  rcases hx1 with h | h
  · left; rw [h]; rfl
  · right
    rw [h, Work.Modular.PresGroup.of_as_pow_C3]
    rw [show (Multiplicative.ofAdd 2 : C3).toAdd.val = 2 from rfl, pow_two]
    rfl

lemma ofFree_x : ofFree x = Work.Modular.genS := by
  rw [Work.FreeProduct.x]; exact Work.Modular.PresGroup.ofFree_gC2

lemma ofFree_y : ofFree y = Work.Modular.genS * Work.Modular.genT := by
  rw [Work.FreeProduct.y]; exact Work.Modular.PresGroup.ofFree_gC3

lemma ofFree_y2 : ofFree y2 = (Work.Modular.genS * Work.Modular.genT) ^ 2 := by
  rw [show y2 = y ^ 2 from rfl, map_pow, ofFree_y]

lemma psiM_of_x :
    psiM (MonoidAlgebra.of ℂ FP x) = Complex.I • (MonoidAlgebra.single ModularGroup.S 1 * eMinus) := by
  rw [show MonoidAlgebra.of ℂ FP x = X from rfl, psiM_X]

lemma psiM_of_y :
    psiM (MonoidAlgebra.of ℂ FP y)
      = (-1 : ℂ) • (MonoidAlgebra.single (ModularGroup.S * ModularGroup.T) 1 * eMinus) := by
  rw [show MonoidAlgebra.of ℂ FP y = Y from rfl, psiM_Y]
  rw [show (R_S * R_T : R) = MonoidAlgebra.single (ModularGroup.S * ModularGroup.T) 1 from by
    rw [R_S, R_T, MonoidAlgebra.single_mul_single, mul_one], neg_smul, one_smul]

lemma psiM_of_y2 :
    psiM (MonoidAlgebra.of ℂ FP y2)
      = (1 : ℂ) • (MonoidAlgebra.single ((ModularGroup.S * ModularGroup.T) ^ 2) 1 * eMinus) := by
  have h : MonoidAlgebra.of ℂ FP y2 = MonoidAlgebra.of ℂ FP y * MonoidAlgebra.of ℂ FP y := by
    rw [show y2 = y ^ 2 from rfl, pow_two, map_mul]
  rw [h, psiM_mul, psiM_of_y]
  rw [smul_mul_smul, show (-1 : ℂ) * -1 = 1 by norm_num]
  congr 1
  rw [mul_eMinus_mul, MonoidAlgebra.single_mul_single, mul_one, ← pow_two]


end
end Work.Asymptotics
