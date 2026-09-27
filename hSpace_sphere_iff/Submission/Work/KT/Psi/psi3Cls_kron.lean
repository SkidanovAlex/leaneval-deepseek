import Mathlib
import Submission.Work.KT.Defs
import Submission.Work.KT.Basic
import Submission.Work.KT.Psi.Basic
import Submission.Work.KT.Psi.cubeAux
import Submission.Work.KT.Psi.k3Aux
import Submission.Work.KT.Psi.cubeMvNAux
import Submission.Work.KT.Psi.kron3_mul
import Submission.Work.KT.Psi.OrbitBasic

import Submission.Work.KT.Psi.cubePart_idem
import Submission.Work.KT.Psi.cubePart_conj
import Submission.Work.KT.Psi.ClsM
import Submission.Work.KT.Psi.clsM_idem_add
import Submission.Work.KT.Psi.psi3sum_Setup
import Submission.Work.KT.K0Prod.mulCls_add
import Submission.Work.KT.K0Prod.mulCls_mvN
import Submission.Work.KT.k0_basic
open Matrix Finset
namespace Work.KT.Psi
noncomputable section

section Abs
variable {S : Type} [Ring S] [Algebra ℂ S]

theorem thirdProj_sum (W : S) :
    (1 + W + W*W) + (1 + (omega^2:ℂ) • W + (omega:ℂ) • (W*W))
      + (1 + (omega:ℂ) • W + (omega^2:ℂ) • (W*W)) = (3:S) := by
  have ha : (1:S) + algebraMap ℂ S omega + (algebraMap ℂ S omega)^2 = 0 := by
    have h : algebraMap ℂ S ((1:ℂ) + omega + omega^2) = 0 := by
      rw [K3.one_add_omega_add_omega_sq, map_zero]
    simpa only [map_add, map_one, map_pow] using h
  have hA : (algebraMap ℂ S omega)^2 = -1 - algebraMap ℂ S omega := by
    have h := ha
    rw [show (1:S) + algebraMap ℂ S omega + (algebraMap ℂ S omega)^2
        = (algebraMap ℂ S omega)^2 + (1 + algebraMap ℂ S omega) from by abel] at h
    have hh := eq_neg_of_add_eq_zero_left h
    rw [hh]; abel
  rw [Algebra.smul_def, Algebra.smul_def, Algebra.smul_def, Algebra.smul_def]
  simp only [map_pow]
  rw [hA]
  noncomm_ring; norm_num

end Abs

variable {A : Type} [Ring A] [Algebra ℂ A]

theorem PM_eq_orbitSpec {ι : Type} [Fintype ι] [DecidableEq ι] (u : Matrix ι ι A) (lam : ℂ) :
    K3.PM u lam = orbitSpec lam u 3 := by
  have hq2 : qg lam u ^ 2 = (lam⁻¹)^2 • (u*u) := by
    rw [qg_pow lam u 2, show (u : Matrix ι ι A)^2 = u*u from pow_two u]
  have hsum : (∑ j ∈ Finset.range 3, qg lam u ^ j) = 1 + lam⁻¹ • u + (lam⁻¹)^2 • (u*u) := by
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one,
      pow_zero, pow_one, hq2]
    simp only [qg]
  rw [K3.PM, orbitSpec, geoSum, hsum, show (((3:ℕ):ℂ)⁻¹) = (1/3:ℂ) by norm_num]

theorem pmSum {ι : Type} [Fintype ι] [DecidableEq ι] (u : Matrix ι ι A) (hu : u*u*u = 1) :
    K3.PM u 1 + K3.PM u omega + K3.PM u (omega^2) = 1 := by
  have h1 : K3.PM u 1 = (1/3:ℂ) • (1 + u + u*u) := by rw [K3.PM]; simp
  have h2 : K3.PM u omega = (1/3:ℂ) • (1 + (omega^2:ℂ)•u + (omega:ℂ)•(u*u)) := by
    rw [K3.PM, Work.KT.omega_inv_sq, Work.KT.omega_inv]
  have h3 : K3.PM u (omega^2) = (1/3:ℂ) • (1 + (omega:ℂ)•u + (omega^2:ℂ)•(u*u)) := by
    rw [K3.PM, K3.omega2_inv_sq, K3.omega2_inv]
  have hnum : (3 : Matrix ι ι A) = (3:ℂ) • (1 : Matrix ι ι A) := by
    rw [Algebra.smul_def, mul_one]
    exact (map_ofNat (algebraMap ℂ (Matrix ι ι A)) 3).symm
  rw [h1, h2, h3, ← smul_add, ← smul_add, thirdProj_sum u, hnum, smul_smul,
    show (1/3:ℂ) * 3 = 1 by norm_num, one_smul]

theorem pm_eigen_left {ι : Type} [Fintype ι] [DecidableEq ι] (u : Matrix ι ι A) (lam : ℂ)
    (hu : u*u*u = 1) (hlam : lam^3 = 1) : u * K3.PM u lam = lam • K3.PM u lam := by
  rw [PM_eq_orbitSpec]
  have hw : u^3 = 1 := by rw [show (3:ℕ) = 2+1 from rfl, pow_succ, pow_two]; exact hu
  rw [g_mul_orbitSpec (by norm_num : 0 < 3) hlam (qg_pow_eq_one hw hlam), Algebra.smul_def]

theorem pm_eigen_right {ι : Type} [Fintype ι] [DecidableEq ι] (u : Matrix ι ι A) (lam : ℂ)
    (hu : u*u*u = 1) (hlam : lam^3 = 1) : K3.PM u lam * u = lam • K3.PM u lam := by
  rw [PM_eq_orbitSpec]
  have hw : u^3 = 1 := by rw [show (3:ℕ) = 2+1 from rfl, pow_succ, pow_two]; exact hu
  rw [orbitSpec_mul_g (by norm_num : 0 < 3) hlam (qg_pow_eq_one hw hlam), Algebra.smul_def]

theorem pmOrth {ι : Type} [Fintype ι] [DecidableEq ι]
    (u : Matrix ι ι A) (lam1 lam2 : ℂ) (hu : u*u*u = 1)
    (h1 : lam1^3 = 1) (h2 : lam2^3 = 1) (hne : lam1 ≠ lam2) :
    K3.PM u lam1 * K3.PM u lam2 = 0 := by
  have hl1 := pm_eigen_left u lam1 hu h1
  have hl2 := pm_eigen_left u lam2 hu h2
  have hr1 := pm_eigen_right u lam1 hu h1
  have hA : lam1 • (K3.PM u lam1 * K3.PM u lam2) = u * (K3.PM u lam1 * K3.PM u lam2) := by
    rw [← Matrix.smul_mul, ← hl1, Matrix.mul_assoc]
  have hB : lam2 • (K3.PM u lam1 * K3.PM u lam2) = u * (K3.PM u lam1 * K3.PM u lam2) := by
    rw [← Matrix.mul_smul, ← hl2, ← Matrix.mul_assoc, hr1, ← hA, Matrix.smul_mul]
  have key : lam1 • (K3.PM u lam1 * K3.PM u lam2) = lam2 • (K3.PM u lam1 * K3.PM u lam2) :=
    hA.trans hB.symm
  have h2' : (lam1 - lam2) • (K3.PM u lam1 * K3.PM u lam2) = 0 := by
    rw [sub_smul, key, sub_self]
  have hne' : (lam1 - lam2 : ℂ) ≠ 0 := sub_ne_zero.mpr hne
  have h4 := congrArg (fun x => (lam1 - lam2)⁻¹ • x) h2'
  rw [smul_zero, smul_smul, inv_mul_cancel₀ hne', one_smul] at h4
  exact h4


variable {A : Type} [Ring A] [Algebra ℂ A]
variable {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

abbrev kronMap (X : Matrix ι ι A) (Y : Matrix κ κ A) : Matrix (ι × κ) (ι × κ) A :=
  Matrix.kroneckerMap (· * ·) X Y

lemma kronMap_add_l (X X' : Matrix ι ι A) (Y : Matrix κ κ A) :
    kronMap (X + X') Y = kronMap X Y + kronMap X' Y :=
  Matrix.kroneckerMap_add_left _ (fun a₁ a₂ b => add_mul a₁ a₂ b) X X' Y

lemma kronMap_add_r (X : Matrix ι ι A) (Y Y' : Matrix κ κ A) :
    kronMap X (Y + Y') = kronMap X Y + kronMap X Y' :=
  Matrix.kroneckerMap_add_right _ (fun a b₁ b₂ => mul_add a b₁ b₂) X Y Y'

lemma kronMap_add_r3 (X : Matrix ι ι A) (Y1 Y2 Y3 : Matrix κ κ A) :
    kronMap X (Y1 + Y2 + Y3) = kronMap X Y1 + kronMap X Y2 + kronMap X Y3 := by
  rw [kronMap_add_r, kronMap_add_r]

lemma kronMap_smul_l (c : ℂ) (X : Matrix ι ι A) (Y : Matrix κ κ A) :
    kronMap (c • X) Y = c • kronMap X Y :=
  Matrix.kroneckerMap_smul_left _ c (fun a b => by
    rw [Algebra.smul_def, Algebra.smul_def, mul_assoc]) X Y

lemma kronMap_smul_r (c : ℂ) (X : Matrix ι ι A) (Y : Matrix κ κ A) :
    kronMap X (c • Y) = c • kronMap X Y :=
  Matrix.kroneckerMap_smul_right _ c (fun a b => by
    rw [Algebra.smul_def, Algebra.smul_def, ← mul_assoc, ← Algebra.commutes c a, mul_assoc]) X Y

lemma kronMap_mul (hA : ∀ x y : A, x * y = y * x) (X X' : Matrix ι ι A) (Y Y' : Matrix κ κ A) :
    kronMap X Y * kronMap X' Y' = kronMap (X * X') (Y * Y') := by
  letI : CommRing A := { ‹Ring A› with mul_comm := hA }
  exact (Matrix.mul_kronecker_mul X X' Y Y').symm

lemma kronMap_one : kronMap (1 : Matrix ι ι A) (1 : Matrix κ κ A) = 1 := by
  ext ⟨i₁, i₂⟩ ⟨j₁, j₂⟩
  simp only [kronMap, Matrix.kroneckerMap_apply, Matrix.one_apply]
  by_cases h : i₁ = j₁ <;> by_cases h2 : i₂ = j₂ <;> simp [h, h2, Prod.ext_iff]

def E1 (u : Matrix ι ι A) (v : Matrix κ κ A) : Matrix (ι × κ) (ι × κ) A :=
  kronMap (K3.PM u 1) (K3.PM v 1) + kronMap (K3.PM u omega) (K3.PM v (omega^2)) +
    kronMap (K3.PM u (omega^2)) (K3.PM v omega)

def Ew (u : Matrix ι ι A) (v : Matrix κ κ A) : Matrix (ι × κ) (ι × κ) A :=
  kronMap (K3.PM u 1) (K3.PM v omega) + kronMap (K3.PM u omega) (K3.PM v 1) +
    kronMap (K3.PM u (omega^2)) (K3.PM v (omega^2))

def Ew2 (u : Matrix ι ι A) (v : Matrix κ κ A) : Matrix (ι × κ) (ι × κ) A :=
  kronMap (K3.PM u 1) (K3.PM v (omega^2)) + kronMap (K3.PM u omega) (K3.PM v omega) +
    kronMap (K3.PM u (omega^2)) (K3.PM v 1)

lemma kronMap_pm_mul {u : Matrix ι ι A} {v : Matrix κ κ A}
    (hA : ∀ x y : A, x * y = y * x) (hu : u*u*u = 1) (hv : v*v*v = 1)
    (α β : ℂ) (ha : α^3 = 1) (hb : β^3 = 1) :
    kronMap u v * kronMap (K3.PM u α) (K3.PM v β)
      = (α * β) • kronMap (K3.PM u α) (K3.PM v β) := by
  rw [kronMap_mul hA, pm_eigen_left u α hu ha, pm_eigen_left v β hv hb,
    kronMap_smul_l, kronMap_smul_r, smul_smul]

lemma wE1 {u : Matrix ι ι A} {v : Matrix κ κ A}
    (hA : ∀ x y : A, x * y = y * x) (hu : u*u*u = 1) (hv : v*v*v = 1) :
    kronMap u v * E1 u v = (1:ℂ) • E1 u v := by
  have h1 := kronMap_pm_mul hA hu hv (1:ℂ) 1 (by norm_num) (by norm_num)
  have h2 := kronMap_pm_mul hA hu hv omega (omega^2) Work.KT.omega_pow_three omega_sq_pow_three
  have h3 := kronMap_pm_mul hA hu hv (omega^2) omega omega_sq_pow_three Work.KT.omega_pow_three
  rw [E1, mul_add, mul_add, h1, h2, h3,
    show (1:ℂ) * 1 = (1:ℂ) by norm_num,
    show omega * omega^2 = (1:ℂ) by rw [Work.KT.omega_mul_sq],
    show omega^2 * omega = (1:ℂ) by rw [mul_comm, Work.KT.omega_mul_sq],
    ← smul_add, ← smul_add]

lemma wEw {u : Matrix ι ι A} {v : Matrix κ κ A}
    (hA : ∀ x y : A, x * y = y * x) (hu : u*u*u = 1) (hv : v*v*v = 1) :
    kronMap u v * Ew u v = omega • Ew u v := by
  have h1 := kronMap_pm_mul hA hu hv (1:ℂ) omega (by norm_num) Work.KT.omega_pow_three
  have h2 := kronMap_pm_mul hA hu hv omega 1 Work.KT.omega_pow_three (by norm_num)
  have h3 := kronMap_pm_mul hA hu hv (omega^2) (omega^2) omega_sq_pow_three omega_sq_pow_three
  rw [Ew, mul_add, mul_add, h1, h2, h3,
    show (1:ℂ) * omega = omega by rw [one_mul],
    show omega * 1 = omega by rw [mul_one],
    show omega^2 * omega^2 = omega by rw [← pow_two, ← pow_mul, K3.omega_pow_four],
    ← smul_add, ← smul_add]

lemma wEw2 {u : Matrix ι ι A} {v : Matrix κ κ A}
    (hA : ∀ x y : A, x * y = y * x) (hu : u*u*u = 1) (hv : v*v*v = 1) :
    kronMap u v * Ew2 u v = (omega^2) • Ew2 u v := by
  have h1 := kronMap_pm_mul hA hu hv (1:ℂ) (omega^2) (by norm_num) omega_sq_pow_three
  have h2 := kronMap_pm_mul hA hu hv omega omega Work.KT.omega_pow_three Work.KT.omega_pow_three
  have h3 := kronMap_pm_mul hA hu hv (omega^2) 1 omega_sq_pow_three (by norm_num)
  rw [Ew2, mul_add, mul_add, h1, h2, h3,
    show (1:ℂ) * omega^2 = omega^2 by rw [one_mul],
    show omega * omega = omega^2 by rw [← pow_two],
    show omega^2 * 1 = omega^2 by rw [mul_one],
    ← smul_add, ← smul_add]

lemma Esum {u : Matrix ι ι A} {v : Matrix κ κ A}
    (hA : ∀ x y : A, x * y = y * x) (hu : u*u*u = 1) (hv : v*v*v = 1) :
    E1 u v + Ew u v + Ew2 u v = 1 := by
  have h1 : K3.PM v 1 + K3.PM v omega + K3.PM v (omega^2) = 1 := pmSum v hv
  have h2 : K3.PM u 1 + K3.PM u omega + K3.PM u (omega^2) = 1 := pmSum u hu
  have key : E1 u v + Ew u v + Ew2 u v =
      kronMap (K3.PM u 1) (K3.PM v 1 + K3.PM v omega + K3.PM v (omega^2)) +
      kronMap (K3.PM u omega) (K3.PM v 1 + K3.PM v omega + K3.PM v (omega^2)) +
      kronMap (K3.PM u (omega^2)) (K3.PM v 1 + K3.PM v omega + K3.PM v (omega^2)) := by
    rw [E1, Ew, Ew2, kronMap_add_r3, kronMap_add_r3, kronMap_add_r3]
    abel
  rw [key, h1, ← kronMap_add_l, ← kronMap_add_l, h2, kronMap_one]


/-! ## Distinctness of the cube roots of unity -/

lemma omega_ne_one : omega ≠ 1 := K3.omega_primRoot.ne_one (by norm_num)
lemma one_ne_omega : (1:ℂ) ≠ omega := omega_ne_one.symm
lemma omega_sq_ne_one : omega^2 ≠ (1:ℂ) := by
  intro h
  have h2 : (omega - 1) * (omega + 1) = 0 := by linear_combination h
  rcases mul_eq_zero.mp h2 with h3 | h3
  · exact omega_ne_one (sub_eq_zero.mp h3)
  · have h4 : omega = -1 := by linear_combination h3
    have h5 : omega^3 = (1:ℂ) := Work.KT.omega_pow_three
    rw [h4] at h5
    norm_num at h5
lemma one_ne_omega_sq : (1:ℂ) ≠ omega^2 := omega_sq_ne_one.symm
lemma omega_ne_omega_sq : omega ≠ omega^2 := by
  intro heq
  have h2 : omega⁻¹ * omega = omega⁻¹ * omega^2 := congrArg (fun x => omega⁻¹ * x) heq
  rw [inv_mul_cancel₀ omega_ne_zero, pow_two, ← mul_assoc, inv_mul_cancel₀ omega_ne_zero,
    one_mul] at h2
  exact omega_ne_one h2.symm
lemma omega_sq_ne_omega : omega^2 ≠ omega := omega_ne_omega_sq.symm

/-! ## Orthogonality and the identification of `PM W λ` with `E λ` -/

lemma mul_eq_zero_of_orth {W F : Matrix (ι × κ) (ι × κ) A} {a b : ℂ}
    (hWO : W * K3.PM W a = a • K3.PM W a) (hOW : K3.PM W a * W = a • K3.PM W a)
    (hWF : W * F = b • F) (hne : a ≠ b) : K3.PM W a * F = 0 := by
  have e1 : W * (K3.PM W a * F) = a • (K3.PM W a * F) := by
    rw [← Matrix.mul_assoc, hWO, Matrix.smul_mul]
  have e2 : W * (K3.PM W a * F) = b • (K3.PM W a * F) := by
    rw [← Matrix.mul_assoc, hWO, ← hOW, Matrix.mul_assoc, hWF, Matrix.mul_smul]
  have hkey : a • (K3.PM W a * F) = b • (K3.PM W a * F) := e1.symm.trans e2
  have h2 : (a - b) • (K3.PM W a * F) = 0 := by rw [sub_smul, hkey, sub_self]
  have hne' : (a - b : ℂ) ≠ 0 := sub_ne_zero.mpr hne
  have h4 := congrArg (fun x => (a - b)⁻¹ • x) h2
  rw [smul_zero, smul_smul, inv_mul_cancel₀ hne', one_smul] at h4
  exact h4

lemma PM_mul_of_wE {W F : Matrix (ι × κ) (ι × κ) A} {a : ℂ}
    (ha : a^3 = 1) (hWF : W * F = a • F) : K3.PM W a * F = F := by
  have hne : a ≠ 0 := fun hc => by
    rw [hc, zero_pow (by norm_num : (3:ℕ) ≠ 0)] at ha; exact zero_ne_one ha
  have hW2 : W * (W * F) = (a*a) • F := by rw [hWF, Matrix.mul_smul, hWF, smul_smul]
  have h1 : a⁻¹ * a = (1:ℂ) := inv_mul_cancel₀ hne
  have h2 : (a⁻¹)^2 * (a*a) = (1:ℂ) := by
    rw [pow_two, ← _root_.mul_inv_rev, inv_mul_cancel₀ (mul_ne_zero hne hne)]
  have hF3 : F + F + F = (3:ℂ) • F := by
    rw [show (3:ℂ) = 1 + 1 + 1 by norm_num, add_smul, add_smul]; simp only [one_smul]
  rw [K3.PM, Matrix.smul_mul, Matrix.add_mul, Matrix.add_mul, Matrix.one_mul, Matrix.smul_mul,
    Matrix.smul_mul, hWF, Matrix.mul_assoc, hW2, smul_smul, smul_smul, h1, h2]
  simp only [one_smul]
  rw [hF3, smul_smul, show (1/3:ℂ) * 3 = 1 by norm_num, one_smul]

lemma PM_mul_E1 {u : Matrix ι ι A} {v : Matrix κ κ A}
    (hA : ∀ x y : A, x * y = y * x) (hu : u*u*u = 1) (hv : v*v*v = 1) :
    K3.PM (kronMap u v) 1 * E1 u v = E1 u v :=
  PM_mul_of_wE (by norm_num) (wE1 hA hu hv)

lemma PM_mul_Ew {u : Matrix ι ι A} {v : Matrix κ κ A}
    (hA : ∀ x y : A, x * y = y * x) (hu : u*u*u = 1) (hv : v*v*v = 1) :
    K3.PM (kronMap u v) omega * Ew u v = Ew u v :=
  PM_mul_of_wE Work.KT.omega_pow_three (wEw hA hu hv)

lemma PM_mul_Ew2 {u : Matrix ι ι A} {v : Matrix κ κ A}
    (hA : ∀ x y : A, x * y = y * x) (hu : u*u*u = 1) (hv : v*v*v = 1) :
    K3.PM (kronMap u v) (omega^2) * Ew2 u v = Ew2 u v :=
  PM_mul_of_wE omega_sq_pow_three (wEw2 hA hu hv)

lemma kronMap_cube {u : Matrix ι ι A} {v : Matrix κ κ A}
    (hA : ∀ x y : A, x * y = y * x) (hu : u*u*u = 1) (hv : v*v*v = 1) :
    kronMap u v * kronMap u v * kronMap u v = 1 := by
  rw [kronMap_mul hA, kronMap_mul hA, hu, hv, kronMap_one]

lemma PM_kron_one {u : Matrix ι ι A} {v : Matrix κ κ A}
    (hA : ∀ x y : A, x * y = y * x) (hu : u*u*u = 1) (hv : v*v*v = 1) :
    K3.PM (kronMap u v) 1 = E1 u v := by
  have hW : kronMap u v * kronMap u v * kronMap u v = 1 := kronMap_cube hA hu hv
  have h1 := PM_mul_E1 (A := A) hA hu hv
  have hzw : K3.PM (kronMap u v) 1 * Ew u v = 0 :=
    mul_eq_zero_of_orth (pm_eigen_left _ 1 hW (by norm_num)) (pm_eigen_right _ 1 hW (by norm_num))
      (wEw hA hu hv) one_ne_omega
  have hzw2 : K3.PM (kronMap u v) 1 * Ew2 u v = 0 :=
    mul_eq_zero_of_orth (pm_eigen_left _ 1 hW (by norm_num)) (pm_eigen_right _ 1 hW (by norm_num))
      (wEw2 hA hu hv) one_ne_omega_sq
  have hEsum := Esum (A := A) hA hu hv
  calc K3.PM (kronMap u v) 1
      = K3.PM (kronMap u v) 1 * 1 := (mul_one _).symm
    _ = K3.PM (kronMap u v) 1 * (E1 u v + Ew u v + Ew2 u v) := by rw [hEsum]
    _ = K3.PM (kronMap u v) 1 * E1 u v + K3.PM (kronMap u v) 1 * Ew u v
          + K3.PM (kronMap u v) 1 * Ew2 u v := by rw [mul_add, mul_add]
    _ = E1 u v := by rw [h1, hzw, hzw2, add_zero, add_zero]

lemma PM_kron_omega {u : Matrix ι ι A} {v : Matrix κ κ A}
    (hA : ∀ x y : A, x * y = y * x) (hu : u*u*u = 1) (hv : v*v*v = 1) :
    K3.PM (kronMap u v) omega = Ew u v := by
  have hW : kronMap u v * kronMap u v * kronMap u v = 1 := kronMap_cube hA hu hv
  have h1 := PM_mul_Ew (A := A) hA hu hv
  have hz1 : K3.PM (kronMap u v) omega * E1 u v = 0 :=
    mul_eq_zero_of_orth (pm_eigen_left _ omega hW Work.KT.omega_pow_three)
      (pm_eigen_right _ omega hW Work.KT.omega_pow_three) (wE1 hA hu hv) omega_ne_one
  have hz2 : K3.PM (kronMap u v) omega * Ew2 u v = 0 :=
    mul_eq_zero_of_orth (pm_eigen_left _ omega hW Work.KT.omega_pow_three)
      (pm_eigen_right _ omega hW Work.KT.omega_pow_three) (wEw2 hA hu hv) omega_ne_omega_sq
  have hEsum := Esum (A := A) hA hu hv
  calc K3.PM (kronMap u v) omega
      = K3.PM (kronMap u v) omega * 1 := (mul_one _).symm
    _ = K3.PM (kronMap u v) omega * (E1 u v + Ew u v + Ew2 u v) := by rw [hEsum]
    _ = K3.PM (kronMap u v) omega * E1 u v + K3.PM (kronMap u v) omega * Ew u v
          + K3.PM (kronMap u v) omega * Ew2 u v := by rw [mul_add, mul_add]
    _ = Ew u v := by rw [hz1, h1, hz2, zero_add, add_zero]


/-! ## The shuffle `SH` commutes with the triple tensor power -/

omit [Algebra ℂ A] in
private theorem hdiv {m : ℕ} (f : Fin m) (c : ℕ) : (f.val + m * c) / m = c := by
  have hm : 0 < m := f.pos
  rw [Nat.add_mul_div_left f.val c hm, Nat.div_eq_of_lt f.isLt, Nat.zero_add]

omit [Algebra ℂ A] in
private theorem hmod {m : ℕ} (f : Fin m) : f.val % m = f.val :=
  Nat.mod_eq_of_lt f.isLt

omit [Algebra ℂ A] in
theorem sh_conj (n m : ℕ) :
    (K3.SH n m).symm.trans ((cycPermP (n*m)).trans (K3.SH n m)) =
      Equiv.prodCongr (cycPermP n) (cycPermP m) := by
  apply Equiv.ext
  intro x
  obtain ⟨⟨⟨a,b⟩,c⟩,⟨⟨d,e⟩,f⟩⟩ := x
  apply Prod.ext
  · apply Prod.ext
    · apply Prod.ext
      · apply Fin.ext; simp [K3.SH, cycPermP, finProdFinEquiv]; exact hdiv f c
      · apply Fin.ext; simp [K3.SH, cycPermP, finProdFinEquiv]; exact hdiv d a
    · apply Fin.ext; simp [K3.SH, cycPermP, finProdFinEquiv]; exact hdiv e b
  · apply Prod.ext
    · apply Prod.ext
      · apply Fin.ext; simp [K3.SH, cycPermP, finProdFinEquiv]; exact hmod f
      · apply Fin.ext; simp [K3.SH, cycPermP, finProdFinEquiv]; exact hmod d
    · apply Fin.ext; simp [K3.SH, cycPermP, finProdFinEquiv]; exact hmod e

theorem k3ShufCyc {n m : ℕ} :
    Matrix.reindex (K3.SH n m) (K3.SH n m)
        (Equiv.Perm.permMatrix A (cycPermP (n * m))) =
      Matrix.kroneckerMap (· * ·) (Equiv.Perm.permMatrix A (cycPermP n))
        (Equiv.Perm.permMatrix A (cycPermP m)) := by
  rw [Work.KT.reindex_permMatrix, sh_conj, K3.kroneckerMap_permMatrix]

theorem k3ShufTZ (hA : ∀ x y : A, x * y = y * x) {n m : ℕ}
    (M : Matrix (Fin n) (Fin n) A) (N : Matrix (Fin m) (Fin m) A) :
    Matrix.reindex (K3.SH n m) (K3.SH n m) (K3.TZ (kronMatR M N)) =
      Matrix.kroneckerMap (· * ·) (K3.TZ M) (K3.TZ N) := by
  letI : CommRing A := { ‹Ring A› with mul_comm := hA }
  ext ⟨⟨⟨a1,b1⟩,c1⟩,⟨⟨d1,e1⟩,f1⟩⟩ ⟨⟨⟨a2,b2⟩,c2⟩,⟨⟨d2,e2⟩,f2⟩⟩
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, K3.TZ_apply, K3.SH_symm_apply,
    kronMatR_apply, Matrix.kroneckerMap_apply]
  ring

/-! ## `TZ` commutes with `PM` of the cyclic permutation matrix -/

theorem tzPMcomm (hA : ∀ x y : A, x * y = y * x) {n : ℕ}
    (G : Matrix (Fin n) (Fin n) A) (lam : ℂ) :
    K3.TZ G * K3.PM (Equiv.Perm.permMatrix A (cycPermP n)) lam =
      K3.PM (Equiv.Perm.permMatrix A (cycPermP n)) lam * K3.TZ G := by
  have hC : K3.TZ G * Equiv.Perm.permMatrix A (cycPermP n) =
      Equiv.Perm.permMatrix A (cycPermP n) * K3.TZ G :=
    kron3_mul_permMatrix_cyc hA G
  have hC2 : K3.TZ G *
        (Equiv.Perm.permMatrix A (cycPermP n) * Equiv.Perm.permMatrix A (cycPermP n)) =
      (Equiv.Perm.permMatrix A (cycPermP n) * Equiv.Perm.permMatrix A (cycPermP n)) * K3.TZ G := by
    rw [← Matrix.mul_assoc, hC, Matrix.mul_assoc, hC, ← Matrix.mul_assoc]
  simp only [K3.PM]
  rw [Matrix.mul_smul, Matrix.smul_mul]
  congr 1
  rw [mul_add, mul_add, mul_one, Matrix.mul_smul, Matrix.mul_smul, add_mul, add_mul, one_mul,
    Matrix.smul_mul, Matrix.smul_mul, hC, hC2]

/-! ## Orthogonality and idempotency of `cubePartP` -/

theorem cubePartP_orth (hA : ∀ x y : A, x * y = y * x) (alpha beta : ℂ)
    (ha : alpha^3 = 1) (hb : beta^3 = 1) (hne : alpha ≠ beta) {p : Mat A} (hp : p.IsIdem) :
    cubePartP alpha p * cubePartP beta p = 0 := by
  calc cubePartP alpha p * cubePartP beta p
      = (K3.TZ p.2 * K3.PM (Equiv.Perm.permMatrix A (cycPermP p.1)) alpha) *
          (K3.TZ p.2 * K3.PM (Equiv.Perm.permMatrix A (cycPermP p.1)) beta) := by
        rw [K3.cubePartP_eq, K3.cubePartP_eq]
    _ = K3.TZ p.2 * (K3.PM (Equiv.Perm.permMatrix A (cycPermP p.1)) alpha * K3.TZ p.2) *
          K3.PM (Equiv.Perm.permMatrix A (cycPermP p.1)) beta := by noncomm_ring
    _ = K3.TZ p.2 * (K3.TZ p.2 * K3.PM (Equiv.Perm.permMatrix A (cycPermP p.1)) alpha) *
          K3.PM (Equiv.Perm.permMatrix A (cycPermP p.1)) beta := by
        rw [tzPMcomm hA p.2 alpha]
    _ = (K3.TZ p.2 * K3.TZ p.2) *
          (K3.PM (Equiv.Perm.permMatrix A (cycPermP p.1)) alpha *
            K3.PM (Equiv.Perm.permMatrix A (cycPermP p.1)) beta) := by noncomm_ring
    _ = 0 := by
        rw [pmOrth _ alpha beta (K3.permMatrix_cycPermP_cube p.1) ha hb hne, Matrix.mul_zero]

lemma kronMap_zero_l (Y : Matrix κ κ A) : kronMap (0 : Matrix ι ι A) Y = 0 := by
  ext i j; simp [kronMap, Matrix.kroneckerMap_apply]

lemma kronMap_zero_r (X : Matrix ι ι A) : kronMap X (0 : Matrix κ κ A) = 0 := by
  ext i j; simp [kronMap, Matrix.kroneckerMap_apply]

/-! ## The tensor decomposition of `cubePartP` -/

theorem cubePartP_decomp_one (hA : ∀ x y : A, x * y = y * x) {p q : Mat A} :
    Matrix.reindex (K3.SH p.1 q.1) (K3.SH p.1 q.1)
        (cubePartP 1 (⟨p.1 * q.1, kronMatR p.2 q.2⟩ : Mat A)) =
      kronMap (cubePartP 1 p) (cubePartP 1 q) +
      kronMap (cubePartP omega p) (cubePartP (omega^2) q) +
      kronMap (cubePartP (omega^2) p) (cubePartP omega q) := by
  rw [K3.cubePartP_eq, Work.KT.reindex_mul', k3ShufTZ hA, K3.reindex_PM, k3ShufCyc,
    PM_kron_one hA (K3.permMatrix_cycPermP_cube p.1) (K3.permMatrix_cycPermP_cube q.1),
    E1, mul_add, mul_add, kronMap_mul hA, kronMap_mul hA, kronMap_mul hA,
    ← K3.cubePartP_eq, ← K3.cubePartP_eq, ← K3.cubePartP_eq, ← K3.cubePartP_eq,
    ← K3.cubePartP_eq, ← K3.cubePartP_eq]

theorem cubePartP_decomp_omega (hA : ∀ x y : A, x * y = y * x) {p q : Mat A} :
    Matrix.reindex (K3.SH p.1 q.1) (K3.SH p.1 q.1)
        (cubePartP omega (⟨p.1 * q.1, kronMatR p.2 q.2⟩ : Mat A)) =
      kronMap (cubePartP 1 p) (cubePartP omega q) +
      kronMap (cubePartP omega p) (cubePartP 1 q) +
      kronMap (cubePartP (omega^2) p) (cubePartP (omega^2) q) := by
  rw [K3.cubePartP_eq, Work.KT.reindex_mul', k3ShufTZ hA, K3.reindex_PM, k3ShufCyc,
    PM_kron_omega hA (K3.permMatrix_cycPermP_cube p.1) (K3.permMatrix_cycPermP_cube q.1),
    Ew, mul_add, mul_add, kronMap_mul hA, kronMap_mul hA, kronMap_mul hA,
    ← K3.cubePartP_eq, ← K3.cubePartP_eq, ← K3.cubePartP_eq, ← K3.cubePartP_eq,
    ← K3.cubePartP_eq, ← K3.cubePartP_eq]


/-! ## `K₀`-level consequences -/

lemma clsM_reindex_kron3 {ι κ : Type} [Fintype ι] [Fintype κ] (g : ι ≃ κ) (M : Matrix ι ι A) :
    clsM κ (Matrix.reindex g g M) = clsM ι M := by
  unfold clsM
  exact (cls_ofIdx_irrel (Matrix.reindex g g M) (Fintype.equivFin κ)
      (g.symm.trans (Fintype.equivFin ι))).trans
    (clsE_reindex M (Fintype.card ι) (Fintype.equivFin ι) g)

lemma mulCls_congr_left (hA : ∀ x y : A, x * y = y * x) {p p' q : Mat A}
    (h : Work.KT.cls p = Work.KT.cls p') : mulCls p q = mulCls p' q := by
  rw [← Work.KT.k0Mul_cls A hA p q, ← Work.KT.k0Mul_cls A hA p' q, h]

lemma mulCls_congr_right (hA : ∀ x y : A, x * y = y * x) {p q q' : Mat A}
    (h : Work.KT.cls q = Work.KT.cls q') : mulCls p q = mulCls p q' := by
  rw [← Work.KT.k0Mul_cls A hA p q, ← Work.KT.k0Mul_cls A hA p q', h]

lemma clsM_kronMap_cubePart (hA : ∀ x y : A, x * y = y * x) {p q : Mat A}
    (hp : p.IsIdem) (hq : q.IsIdem) {α β : ℂ} (hα : α^3 = 1) (hβ : β^3 = 1) :
    clsM (K3.I3 p.1 × K3.I3 q.1) (kronMap (cubePartP α p) (cubePartP β q)) =
      mulCls (cubePart α p) (cubePart β q) := by
  rw [Work.KT.mulCls_of_idem (cubePart_idem hA α hα hp) (cubePart_idem hA β hβ hq),
    cubePart_eq α p, cubePart_eq β q, K3.cls_kron_of_reindex]
  exact cls_ofIdx_irrel (kronMap (cubePartP α p) (cubePartP β q))
    (Fintype.equivFin (K3.I3 p.1 × K3.I3 q.1))
    (((cycIdx p.1).symm.prodCongr (cycIdx q.1).symm).trans finProdFinEquiv)

lemma kronMap_mul_zero_l (hA : ∀ x y : A, x * y = y * x) {P P' : Matrix ι ι A}
    {Q Q' : Matrix κ κ A} (h : P * P' = 0) : kronMap P Q * kronMap P' Q' = 0 := by
  rw [kronMap_mul hA, h, kronMap_zero_l]

lemma kronMap_mul_zero_r (hA : ∀ x y : A, x * y = y * x) {P P' : Matrix ι ι A}
    {Q Q' : Matrix κ κ A} (h : Q * Q' = 0) : kronMap P Q * kronMap P' Q' = 0 := by
  rw [kronMap_mul hA, h, kronMap_zero_r]

lemma kronMap_idem (hA : ∀ x y : A, x * y = y * x) {P : Matrix ι ι A} {Q : Matrix κ κ A}
    (hP : P * P = P) (hQ : Q * Q = Q) : kronMap P Q * kronMap P Q = kronMap P Q := by
  rw [kronMap_mul hA, hP, hQ]

lemma cls_cubePart_kron_one (hA : ∀ x y : A, x * y = y * x) {p q : Mat A}
    (hp : p.IsIdem) (hq : q.IsIdem) :
    Work.KT.cls (cubePart 1 (p.kron q)) =
      mulCls (cubePart 1 p) (cubePart 1 q) + mulCls (cubePart omega p) (cubePart (omega^2) q) +
        mulCls (cubePart (omega^2) p) (cubePart omega q) := by
  have hP1 := cubePartP_idem hA 1 (by norm_num) hp
  have hPw := cubePartP_idem hA omega Work.KT.omega_pow_three hp
  have hP2 := cubePartP_idem hA (omega^2) omega_sq_pow_three hp
  have hQ1 := cubePartP_idem hA 1 (by norm_num) hq
  have hQw := cubePartP_idem hA omega Work.KT.omega_pow_three hq
  have hQ2 := cubePartP_idem hA (omega^2) omega_sq_pow_three hq
  have oP1w : cubePartP 1 p * cubePartP omega p = 0 :=
    cubePartP_orth hA 1 omega (by norm_num) Work.KT.omega_pow_three one_ne_omega hp
  have oP12 : cubePartP 1 p * cubePartP (omega^2) p = 0 :=
    cubePartP_orth hA 1 (omega^2) (by norm_num) omega_sq_pow_three one_ne_omega_sq hp
  have oP2w : cubePartP (omega^2) p * cubePartP omega p = 0 :=
    cubePartP_orth hA (omega^2) omega omega_sq_pow_three Work.KT.omega_pow_three
      omega_sq_ne_omega hp
  have oQ2w : cubePartP (omega^2) q * cubePartP omega q = 0 :=
    cubePartP_orth hA (omega^2) omega omega_sq_pow_three Work.KT.omega_pow_three
      omega_sq_ne_omega hq
  have hA1 : kronMap (cubePartP 1 p) (cubePartP 1 q) *
      kronMap (cubePartP 1 p) (cubePartP 1 q) = kronMap (cubePartP 1 p) (cubePartP 1 q) :=
    kronMap_idem hA hP1 hQ1
  have hA2 : kronMap (cubePartP omega p) (cubePartP (omega^2) q) *
      kronMap (cubePartP omega p) (cubePartP (omega^2) q) =
        kronMap (cubePartP omega p) (cubePartP (omega^2) q) :=
    kronMap_idem hA hPw hQ2
  have hA3 : kronMap (cubePartP (omega^2) p) (cubePartP omega q) *
      kronMap (cubePartP (omega^2) p) (cubePartP omega q) =
        kronMap (cubePartP (omega^2) p) (cubePartP omega q) :=
    kronMap_idem hA hP2 hQw
  have h12 : kronMap (cubePartP 1 p) (cubePartP 1 q) *
      kronMap (cubePartP omega p) (cubePartP (omega^2) q) = 0 :=
    kronMap_mul_zero_l hA oP1w
  have h21 : kronMap (cubePartP omega p) (cubePartP (omega^2) q) *
      kronMap (cubePartP 1 p) (cubePartP 1 q) = 0 :=
    kronMap_mul_zero_l hA (cubePartP_orth hA omega 1 Work.KT.omega_pow_three (by norm_num)
      omega_ne_one hp)
  have h13 : kronMap (cubePartP 1 p) (cubePartP 1 q) *
      kronMap (cubePartP (omega^2) p) (cubePartP omega q) = 0 :=
    kronMap_mul_zero_l hA oP12
  have h23 : kronMap (cubePartP omega p) (cubePartP (omega^2) q) *
      kronMap (cubePartP (omega^2) p) (cubePartP omega q) = 0 :=
    kronMap_mul_zero_l hA (cubePartP_orth hA omega (omega^2) Work.KT.omega_pow_three
      omega_sq_pow_three omega_ne_omega_sq hp)
  have h31 : kronMap (cubePartP (omega^2) p) (cubePartP omega q) *
      kronMap (cubePartP 1 p) (cubePartP 1 q) = 0 :=
    kronMap_mul_zero_l hA (cubePartP_orth hA (omega^2) 1 omega_sq_pow_three (by norm_num)
      omega_sq_ne_one hp)
  have h32 : kronMap (cubePartP (omega^2) p) (cubePartP omega q) *
      kronMap (cubePartP omega p) (cubePartP (omega^2) q) = 0 :=
    kronMap_mul_zero_l hA oP2w
  have hE : (kronMap (cubePartP 1 p) (cubePartP 1 q) +
      kronMap (cubePartP omega p) (cubePartP (omega^2) q)) *
      (kronMap (cubePartP 1 p) (cubePartP 1 q) +
        kronMap (cubePartP omega p) (cubePartP (omega^2) q)) =
      kronMap (cubePartP 1 p) (cubePartP 1 q) +
        kronMap (cubePartP omega p) (cubePartP (omega^2) q) := by
    rw [add_mul, mul_add, mul_add, hA1, h21, h12, hA2]; abel
  have hE3 : (kronMap (cubePartP 1 p) (cubePartP 1 q) +
      kronMap (cubePartP omega p) (cubePartP (omega^2) q)) *
      kronMap (cubePartP (omega^2) p) (cubePartP omega q) = 0 := by
    rw [add_mul, h13, h23, add_zero]
  have h3E : kronMap (cubePartP (omega^2) p) (cubePartP omega q) *
      (kronMap (cubePartP 1 p) (cubePartP 1 q) +
        kronMap (cubePartP omega p) (cubePartP (omega^2) q)) = 0 := by
    rw [mul_add, h31, h32, add_zero]
  have hK : p.kron q = (⟨p.1 * q.1, kronMatR p.2 q.2⟩ : Mat A) := rfl
  rw [hK, ← clsM_I3_cubePartP 1 (⟨p.1 * q.1, kronMatR p.2 q.2⟩ : Mat A),
    ← clsM_reindex_kron3 (K3.SH p.1 q.1), cubePartP_decomp_one hA]
  rw [clsM_idem_add _ _ hE hA3 hE3 h3E, clsM_idem_add _ _ hA1 hA2 h12 h21]
  rw [clsM_kronMap_cubePart hA hp hq (by norm_num) (by norm_num),
    clsM_kronMap_cubePart hA hp hq Work.KT.omega_pow_three omega_sq_pow_three,
    clsM_kronMap_cubePart hA hp hq omega_sq_pow_three Work.KT.omega_pow_three]

lemma cls_cubePart_kron_omega (hA : ∀ x y : A, x * y = y * x) {p q : Mat A}
    (hp : p.IsIdem) (hq : q.IsIdem) :
    Work.KT.cls (cubePart omega (p.kron q)) =
      mulCls (cubePart 1 p) (cubePart omega q) + mulCls (cubePart omega p) (cubePart 1 q) +
        mulCls (cubePart (omega^2) p) (cubePart (omega^2) q) := by
  have hP1 := cubePartP_idem hA 1 (by norm_num) hp
  have hPw := cubePartP_idem hA omega Work.KT.omega_pow_three hp
  have hP2 := cubePartP_idem hA (omega^2) omega_sq_pow_three hp
  have hQ1 := cubePartP_idem hA 1 (by norm_num) hq
  have hQw := cubePartP_idem hA omega Work.KT.omega_pow_three hq
  have hQ2 := cubePartP_idem hA (omega^2) omega_sq_pow_three hq
  have oP1w : cubePartP 1 p * cubePartP omega p = 0 :=
    cubePartP_orth hA 1 omega (by norm_num) Work.KT.omega_pow_three one_ne_omega hp
  have oPw1 : cubePartP omega p * cubePartP 1 p = 0 :=
    cubePartP_orth hA omega 1 Work.KT.omega_pow_three (by norm_num) omega_ne_one hp
  have oP12 : cubePartP 1 p * cubePartP (omega^2) p = 0 :=
    cubePartP_orth hA 1 (omega^2) (by norm_num) omega_sq_pow_three one_ne_omega_sq hp
  have oP21 : cubePartP (omega^2) p * cubePartP 1 p = 0 :=
    cubePartP_orth hA (omega^2) 1 omega_sq_pow_three (by norm_num) omega_sq_ne_one hp
  have oPw2 : cubePartP omega p * cubePartP (omega^2) p = 0 :=
    cubePartP_orth hA omega (omega^2) Work.KT.omega_pow_three omega_sq_pow_three
      omega_ne_omega_sq hp
  have oP2w : cubePartP (omega^2) p * cubePartP omega p = 0 :=
    cubePartP_orth hA (omega^2) omega omega_sq_pow_three Work.KT.omega_pow_three
      omega_sq_ne_omega hp
  have hB1 : kronMap (cubePartP 1 p) (cubePartP omega q) *
      kronMap (cubePartP 1 p) (cubePartP omega q) = kronMap (cubePartP 1 p) (cubePartP omega q) :=
    kronMap_idem hA hP1 hQw
  have hB2 : kronMap (cubePartP omega p) (cubePartP 1 q) *
      kronMap (cubePartP omega p) (cubePartP 1 q) = kronMap (cubePartP omega p) (cubePartP 1 q) :=
    kronMap_idem hA hPw hQ1
  have hB3 : kronMap (cubePartP (omega^2) p) (cubePartP (omega^2) q) *
      kronMap (cubePartP (omega^2) p) (cubePartP (omega^2) q) =
        kronMap (cubePartP (omega^2) p) (cubePartP (omega^2) q) :=
    kronMap_idem hA hP2 hQ2
  have h12 : kronMap (cubePartP 1 p) (cubePartP omega q) *
      kronMap (cubePartP omega p) (cubePartP 1 q) = 0 := kronMap_mul_zero_l hA oP1w
  have h21 : kronMap (cubePartP omega p) (cubePartP 1 q) *
      kronMap (cubePartP 1 p) (cubePartP omega q) = 0 := kronMap_mul_zero_l hA oPw1
  have h13 : kronMap (cubePartP 1 p) (cubePartP omega q) *
      kronMap (cubePartP (omega^2) p) (cubePartP (omega^2) q) = 0 :=
    kronMap_mul_zero_l hA oP12
  have h23 : kronMap (cubePartP omega p) (cubePartP 1 q) *
      kronMap (cubePartP (omega^2) p) (cubePartP (omega^2) q) = 0 :=
    kronMap_mul_zero_l hA oPw2
  have h31 : kronMap (cubePartP (omega^2) p) (cubePartP (omega^2) q) *
      kronMap (cubePartP 1 p) (cubePartP omega q) = 0 := kronMap_mul_zero_l hA oP21
  have h32 : kronMap (cubePartP (omega^2) p) (cubePartP (omega^2) q) *
      kronMap (cubePartP omega p) (cubePartP 1 q) = 0 := kronMap_mul_zero_l hA oP2w
  have hE : (kronMap (cubePartP 1 p) (cubePartP omega q) +
      kronMap (cubePartP omega p) (cubePartP 1 q)) *
      (kronMap (cubePartP 1 p) (cubePartP omega q) +
        kronMap (cubePartP omega p) (cubePartP 1 q)) =
      kronMap (cubePartP 1 p) (cubePartP omega q) +
        kronMap (cubePartP omega p) (cubePartP 1 q) := by
    rw [add_mul, mul_add, mul_add, hB1, h21, h12, hB2]; abel
  have hE3 : (kronMap (cubePartP 1 p) (cubePartP omega q) +
      kronMap (cubePartP omega p) (cubePartP 1 q)) *
      kronMap (cubePartP (omega^2) p) (cubePartP (omega^2) q) = 0 := by
    rw [add_mul, h13, h23, add_zero]
  have h3E : kronMap (cubePartP (omega^2) p) (cubePartP (omega^2) q) *
      (kronMap (cubePartP 1 p) (cubePartP omega q) +
        kronMap (cubePartP omega p) (cubePartP 1 q)) = 0 := by
    rw [mul_add, h31, h32, add_zero]
  have hK : p.kron q = (⟨p.1 * q.1, kronMatR p.2 q.2⟩ : Mat A) := rfl
  rw [hK, ← clsM_I3_cubePartP omega (⟨p.1 * q.1, kronMatR p.2 q.2⟩ : Mat A),
    ← clsM_reindex_kron3 (K3.SH p.1 q.1), cubePartP_decomp_omega hA]
  rw [clsM_idem_add _ _ hE hB3 hE3 h3E, clsM_idem_add _ _ hB1 hB2 h12 h21]
  rw [clsM_kronMap_cubePart hA hp hq (by norm_num) Work.KT.omega_pow_three,
    clsM_kronMap_cubePart hA hp hq Work.KT.omega_pow_three (by norm_num),
    clsM_kronMap_cubePart hA hp hq omega_sq_pow_three omega_sq_pow_three]


/-! ## The main theorem -/

set_option maxHeartbeats 800000 in
theorem psi3Cls_kron {A : Type} [Ring A] [Algebra ℂ A] (hA : ∀ x y : A, x * y = y * x)
    {p q : Mat A} (hp : p.IsIdem) (hq : q.IsIdem) :
    psi3Cls (p.kron q) =
      mulCls (cubePart 1 p) (cubePart 1 q) - mulCls (cubePart 1 p) (cubePart omega q) -
        mulCls (cubePart omega p) (cubePart 1 q) + mulCls (cubePart omega p) (cubePart omega q) := by
  have hpq : (p.kron q).IsIdem := Work.KT.Mat.kron_idem hA hp hq
  have e1 : mulCls (cubePart omega p) (cubePart (omega^2) q) =
      mulCls (cubePart omega p) (cubePart omega q) :=
    mulCls_congr_right hA (cubePart_conj hA hq).symm
  have e2 : mulCls (cubePart (omega^2) p) (cubePart omega q) =
      mulCls (cubePart omega p) (cubePart omega q) :=
    mulCls_congr_left hA (cubePart_conj hA hp).symm
  have e3 : mulCls (cubePart (omega^2) p) (cubePart (omega^2) q) =
      mulCls (cubePart omega p) (cubePart omega q) :=
    (mulCls_congr_left hA (cubePart_conj hA hp).symm).trans
      (mulCls_congr_right hA (cubePart_conj hA hq).symm)
  simp only [psi3Cls, if_pos hpq]
  rw [cls_cubePart_kron_one hA hp hq, cls_cubePart_kron_omega hA hp hq, e1, e2, e3]
  abel


end
end Work.KT.Psi
