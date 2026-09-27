import Mathlib
import Submission.Work.KT.Defs
import Submission.Work.KT.PsiC.BFrame

/-!
# `Work.PsiC.cycProj_diag`

The diagonal decomposition of the three-term spectral projector of a product of two
commuting order-three matrices:

`cycProj (cB n) (λ²) = P_λ Q_λ + P_{λω} Q_{λω²} + P_{λω²} Q_{λω}`

with `cB = uB · vB`, `P_• = cycProj (uB n) •` and `Q_• = cycProj (vB n) •`.

The proof is the general matrix statement `orbSpec_UV_decomp` (spectral projectors of the
product of two commuting order-three elements), specialised to `U = uB`, `V = vB`.
-/

namespace Work.PsiC

open Matrix
open Work.KT.Psi

noncomputable section

variable {A : Type} [Ring A] [Algebra ℂ A]
variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-! ## Elementary spectral-projector lemmas for an order-three matrix -/

/-- A cube root of unity in `ℂ` is nonzero. -/
theorem ne_zero_of_pow3 (x : ℂ) (h : x ^ 3 = 1) : x ≠ 0 := by
  intro hc
  rw [hc] at h
  norm_num at h

/-- `X ^ 3 = 1` from the left-associated product form. -/
theorem eq_cube_of_mul3 (X : Matrix ι ι A) (h : X * X * X = 1) : X ^ 3 = 1 := by
  rw [pow_three, ← mul_assoc]; exact h

/-- The left eigenrelation of the spectral projector. -/
theorem orbSpec_g_mul (X : Matrix ι ι A) (lam : ℂ) (hX : X * X * X = 1) (hlam : lam ^ 3 = 1) :
    X * orbitSpec lam X 3 = lam • orbitSpec lam X 3 := by
  rw [Work.KT.Psi.g_mul_orbitSpec (by norm_num) hlam
    (Work.KT.Psi.qg_pow_eq_one (eq_cube_of_mul3 X hX) hlam), Algebra.smul_def]

/-- The right eigenrelation of the spectral projector. -/
theorem orbSpec_mul_g (X : Matrix ι ι A) (lam : ℂ) (hX : X * X * X = 1) (hlam : lam ^ 3 = 1) :
    orbitSpec lam X 3 * X = lam • orbitSpec lam X 3 := by
  rw [Work.KT.Psi.orbitSpec_mul_g (by norm_num) hlam
    (Work.KT.Psi.qg_pow_eq_one (eq_cube_of_mul3 X hX) hlam), Algebra.smul_def]

/-- If `W` acts on `F` by the scalar `a` of order three, the spectral projector of `W` at `a`
fixes `F`. -/
theorem orbSpec_mul_of_eigen (W F : Matrix ι ι A) (a : ℂ) (ha : a ^ 3 = 1)
    (hWF : W * F = a • F) : orbitSpec a W 3 * F = F := by
  have hne : a ≠ 0 := by
    intro hc
    rw [hc] at ha
    norm_num at ha
  have hWF2 : W * (W * F) = (a*a) • F := by rw [hWF, Matrix.mul_smul, hWF, smul_smul]
  have hWa : W^2 * F = (a*a) • F := by rw [pow_two, Matrix.mul_assoc]; exact hWF2
  have h1 : a⁻¹ * a = (1:ℂ) := inv_mul_cancel₀ hne
  have h2 : (a⁻¹)^2 * (a*a) = (1:ℂ) := by rw [pow_two]; field_simp
  have hF3 : F + F + F = (3:ℂ) • F := by
    rw [show (3:ℂ) = 1 + 1 + 1 by norm_num, add_smul, add_smul]; simp
  rw [Work.KT.PsiC.orbitSpec_three a W, smul_mul, Matrix.add_mul, Matrix.add_mul, Matrix.one_mul,
    smul_mul, smul_mul, hWF, hWa, smul_smul, smul_smul, h1, h2]
  simp only [one_smul]
  rw [hF3, smul_smul, show (3:ℂ)⁻¹ * 3 = 1 by norm_num, one_smul]

/-- Orthogonality: if `F` is an eigenvector of `W` with eigenvalue `b ≠ a`, then the `a`-spectral
projector of `W` kills it. -/
theorem orbSpec_mul_eq_zero (W F : Matrix ι ι A) (a b : ℂ)
    (hWO : W * orbitSpec a W 3 = a • orbitSpec a W 3)
    (hOW : orbitSpec a W 3 * W = a • orbitSpec a W 3)
    (hWF : W * F = b • F) (hne : a ≠ b) :
    orbitSpec a W 3 * F = 0 := by
  have e1 : W * (orbitSpec a W 3 * F) = a • (orbitSpec a W 3 * F) := by
    rw [← Matrix.mul_assoc, hWO, Matrix.smul_mul]
  have e2 : W * (orbitSpec a W 3 * F) = b • (orbitSpec a W 3 * F) := by
    rw [← Matrix.mul_assoc, hWO, ← hOW, Matrix.mul_assoc, hWF, Matrix.mul_smul]
  have hkey : a • (orbitSpec a W 3 * F) = b • (orbitSpec a W 3 * F) := e1.symm.trans e2
  have h2 : (a - b) • (orbitSpec a W 3 * F) = 0 := by rw [sub_smul, hkey, sub_self]
  have hne' : (a - b : ℂ) ≠ 0 := sub_ne_zero.mpr hne
  have h4 := congrArg (fun x => (a - b)⁻¹ • x) h2
  rw [smul_zero, smul_smul, inv_mul_cancel₀ hne', one_smul] at h4
  exact h4

/-- The three spectral projectors onto the cube-root eigenvalues sum to `1`. -/
theorem orbSpec_sum (X : Matrix ι ι A) (a : ℂ) :
    orbitSpec a X 3 + orbitSpec (a * Work.KT.omega) X 3 +
      orbitSpec (a * Work.KT.omega ^ 2) X 3 = 1 := by
  have hcoef1 : a⁻¹ + (a * Work.KT.omega)⁻¹ + (a * Work.KT.omega ^ 2)⁻¹ = 0 := by
    rw [_root_.mul_inv_rev, _root_.mul_inv_rev]
    linear_combination a⁻¹ * Work.KT.Psi.K3.sum_inv
  have hcoef2 : (a⁻¹)^2 + ((a * Work.KT.omega)⁻¹)^2 + ((a * Work.KT.omega ^ 2)⁻¹)^2 = 0 := by
    rw [_root_.mul_inv_rev, _root_.mul_inv_rev]
    linear_combination (a⁻¹)^2 * Work.KT.Psi.K3.sum_inv_sq
  rw [Work.KT.PsiC.orbitSpec_three a X, Work.KT.PsiC.orbitSpec_three (a * Work.KT.omega) X,
    Work.KT.PsiC.orbitSpec_three (a * Work.KT.omega ^ 2) X]
  rw [← smul_add, ← smul_add]
  have hABC : (1 + a⁻¹ • X + (a⁻¹)^2 • X^2)
      + (1 + (a*Work.KT.omega)⁻¹ • X + ((a*Work.KT.omega)⁻¹)^2 • X^2)
      + (1 + (a*Work.KT.omega^2)⁻¹ • X + ((a*Work.KT.omega^2)⁻¹)^2 • X^2) = 3 := by
    have e : (1 + a⁻¹ • X + (a⁻¹)^2 • X^2)
        + (1 + (a*Work.KT.omega)⁻¹ • X + ((a*Work.KT.omega)⁻¹)^2 • X^2)
        + (1 + (a*Work.KT.omega^2)⁻¹ • X + ((a*Work.KT.omega^2)⁻¹)^2 • X^2)
        = (1 + 1 + 1) + (a⁻¹ • X + (a*Work.KT.omega)⁻¹ • X + (a*Work.KT.omega^2)⁻¹ • X)
        + ((a⁻¹)^2 • X^2 + ((a*Work.KT.omega)⁻¹)^2 • X^2
            + ((a*Work.KT.omega^2)⁻¹)^2 • X^2) := by abel
    rw [e, ← add_smul, ← add_smul, ← add_smul, ← add_smul, hcoef1, hcoef2, zero_smul, zero_smul,
      add_zero, add_zero]
    norm_num
  rw [hABC, Algebra.smul_def,
    show (3 : Matrix ι ι A) = algebraMap ℂ (Matrix ι ι A) (3:ℂ) from
      (map_ofNat (algebraMap ℂ (Matrix ι ι A)) 3).symm, ← map_mul,
    show (3:ℂ)⁻¹ * 3 = 1 by norm_num, map_one]

/-- If `U V = V U`, `U³ = 1`, `V³ = 1`, then `U·V` acts on `P_μ(U) Q_ν(V)` by `μν`. -/
theorem prod_UV_eigen (U V : Matrix ι ι A) (hU : U * U * U = 1) (hV : V * V * V = 1)
    (hUV : U * V = V * U) (mu nu : ℂ) (hmu : mu ^ 3 = 1) (hnu : nu ^ 3 = 1) :
    (U*V) * (orbitSpec mu U 3 * orbitSpec nu V 3) =
      (mu*nu) • (orbitSpec mu U 3 * orbitSpec nu V 3) := by
  have hUP : U * orbitSpec mu U 3 = mu • orbitSpec mu U 3 := orbSpec_g_mul U mu hU hmu
  have hVQ : V * orbitSpec nu V 3 = nu • orbitSpec nu V 3 := orbSpec_g_mul V nu hV hnu
  have hVP : V * orbitSpec mu U 3 = orbitSpec mu U 3 * V :=
    (Work.KT.Psi.orbitSpec_comm_of hUV).symm
  calc (U*V) * (orbitSpec mu U 3 * orbitSpec nu V 3)
      = U * (V * (orbitSpec mu U 3 * orbitSpec nu V 3)) :=
          mul_assoc U V (orbitSpec mu U 3 * orbitSpec nu V 3)
    _ = U * ((V * orbitSpec mu U 3) * orbitSpec nu V 3) :=
          by rw [← mul_assoc V (orbitSpec mu U 3) (orbitSpec nu V 3)]
    _ = U * ((orbitSpec mu U 3 * V) * orbitSpec nu V 3) := by rw [hVP]
    _ = U * (orbitSpec mu U 3 * (V * orbitSpec nu V 3)) :=
          by rw [mul_assoc (orbitSpec mu U 3) V (orbitSpec nu V 3)]
    _ = U * (orbitSpec mu U 3 * (nu • orbitSpec nu V 3)) := by rw [hVQ]
    _ = U * (nu • (orbitSpec mu U 3 * orbitSpec nu V 3)) := by rw [Matrix.mul_smul]
    _ = nu • (U * (orbitSpec mu U 3 * orbitSpec nu V 3)) := by rw [Matrix.mul_smul]
    _ = nu • ((U * orbitSpec mu U 3) * orbitSpec nu V 3) :=
          by rw [← mul_assoc U (orbitSpec mu U 3) (orbitSpec nu V 3)]
    _ = nu • ((mu • orbitSpec mu U 3) * orbitSpec nu V 3) := by rw [hUP]
    _ = nu • (mu • (orbitSpec mu U 3 * orbitSpec nu V 3)) := by rw [smul_mul]
    _ = (nu * mu) • (orbitSpec mu U 3 * orbitSpec nu V 3) := by rw [smul_smul]
    _ = (mu * nu) • (orbitSpec mu U 3 * orbitSpec nu V 3) := by rw [mul_comm]

theorem cube_of_comm (U V : Matrix ι ι A) (hUV : U * V = V * U) (hU : U * U * U = 1)
    (hV : V * V * V = 1) : (U*V) * (U*V) * (U*V) = 1 := by
  rw [show (U*V)*(U*V)*(U*V) = (U*V)^3 from by noncomm_ring,
      (show Commute U V from hUV).mul_pow 3]
  rw [show U^3 = 1 from by rw [pow_three, ← mul_assoc]; exact hU,
      show V^3 = 1 from by rw [pow_three, ← mul_assoc]; exact hV, one_mul]

/-- **Diagonal decomposition of the spectral projector of a product.** -/
theorem orbSpec_UV_decomp (U V : Matrix ι ι A) (hU : U * U * U = 1) (hV : V * V * V = 1)
    (hUV : U * V = V * U) (a b : ℂ) (ha : a ^ 3 = 1) (hb : b ^ 3 = 1) :
    orbitSpec (a*b) (U*V) 3 =
      orbitSpec a U 3 * orbitSpec b V 3 +
        (orbitSpec (a*Work.KT.omega) U 3 * orbitSpec (b*Work.KT.omega^2) V 3 +
         orbitSpec (a*Work.KT.omega^2) U 3 * orbitSpec (b*Work.KT.omega) V 3) := by
  set A1 := orbitSpec a U 3 with hA1
  set A2 := orbitSpec (a*Work.KT.omega) U 3 with hA2
  set A3 := orbitSpec (a*Work.KT.omega^2) U 3 with hA3
  set B1 := orbitSpec b V 3 with hB1
  set B2 := orbitSpec (b*Work.KT.omega) V 3 with hB2
  set B3 := orbitSpec (b*Work.KT.omega^2) V 3 with hB3
  set P := orbitSpec (a*b) (U*V) 3 with hP
  set G1 := A1 * B1 + (A2 * B3 + A3 * B2) with hG1
  set G2 := A1 * B2 + (A2 * B1 + A3 * B3) with hG2
  set G3 := A1 * B3 + (A2 * B2 + A3 * B1) with hG3
  have hsumU : A1 + A2 + A3 = 1 := by rw [hA1, hA2, hA3]; exact orbSpec_sum U a
  have hsumV : B1 + B2 + B3 = 1 := by rw [hB1, hB2, hB3]; exact orbSpec_sum V b
  have hab3 : (a*b) ^ 3 = 1 := by rw [mul_pow, ha, hb, one_mul]
  have hW3 : (U*V) * (U*V) * (U*V) = 1 := cube_of_comm U V hUV hU hV
  have hcaw : (a*Work.KT.omega) ^ 3 = 1 := by
    rw [mul_pow, ha, Work.KT.omega_pow_three, one_mul]
  have hcaw2 : (a*Work.KT.omega^2) ^ 3 = 1 := by
    rw [mul_pow, ha, show (Work.KT.omega^2)^3 = 1 from by
      rw [← pow_mul, show (2:ℕ)*3 = 3*2 from by norm_num, pow_mul, Work.KT.omega_pow_three,
        one_pow], one_mul]
  have hcbw : (b*Work.KT.omega) ^ 3 = 1 := by
    rw [mul_pow, hb, Work.KT.omega_pow_three, one_mul]
  have hcbw2 : (b*Work.KT.omega^2) ^ 3 = 1 := by
    rw [mul_pow, hb, show (Work.KT.omega^2)^3 = 1 from by
      rw [← pow_mul, show (2:ℕ)*3 = 3*2 from by norm_num, pow_mul, Work.KT.omega_pow_three,
        one_pow], one_mul]
  have e23 : (a*Work.KT.omega) * (b*Work.KT.omega^2) = a*b := by
    rw [show (a*Work.KT.omega)*(b*Work.KT.omega^2) = a*b*Work.KT.omega^3 from by ring,
      Work.KT.omega_pow_three, mul_one]
  have e32 : (a*Work.KT.omega^2) * (b*Work.KT.omega) = a*b := by
    rw [show (a*Work.KT.omega^2)*(b*Work.KT.omega) = a*b*Work.KT.omega^3 from by ring,
      Work.KT.omega_pow_three, mul_one]
  have hab_ne : a*b ≠ 0 := mul_ne_zero (ne_zero_of_pow3 a ha) (ne_zero_of_pow3 b hb)
  have homega_ne_one : Work.KT.omega ≠ 1 := Work.KT.Psi.K3.omega_primRoot.ne_one (by norm_num)
  have homega2_ne_one : Work.KT.omega ^ 2 ≠ 1 := by
    intro h
    refine homega_ne_one ?_
    calc Work.KT.omega = Work.KT.omega * 1 := (mul_one _).symm
      _ = Work.KT.omega * Work.KT.omega^2 := by rw [h]
      _ = Work.KT.omega^3 := by ring
      _ = 1 := Work.KT.omega_pow_three
  have hne_of : ∀ c : ℂ, c ≠ 1 → (a*b)*c ≠ a*b := fun c hc h =>
    hc (mul_left_cancel₀ hab_ne (h.trans (mul_one _).symm))
  have hPos : ∀ mu nu : ℂ, mu^3 = 1 → nu^3 = 1 → mu*nu = a*b →
      P * (orbitSpec mu U 3 * orbitSpec nu V 3) = orbitSpec mu U 3 * orbitSpec nu V 3 := by
    intro mu nu hmu hnu he
    have hWF : (U*V) * (orbitSpec mu U 3 * orbitSpec nu V 3) =
        (a*b) • (orbitSpec mu U 3 * orbitSpec nu V 3) := by
      rw [prod_UV_eigen U V hU hV hUV mu nu hmu hnu, he]
    have h := orbSpec_mul_of_eigen (U*V) (orbitSpec mu U 3 * orbitSpec nu V 3) (a*b) hab3 hWF
    rw [← hP] at h; exact h
  have hZero : ∀ mu nu : ℂ, mu^3 = 1 → nu^3 = 1 → mu*nu ≠ a*b →
      P * (orbitSpec mu U 3 * orbitSpec nu V 3) = 0 := by
    intro mu nu hmu hnu he
    have hWF : (U*V) * (orbitSpec mu U 3 * orbitSpec nu V 3) =
        (mu*nu) • (orbitSpec mu U 3 * orbitSpec nu V 3) :=
      prod_UV_eigen U V hU hV hUV mu nu hmu hnu
    have hWO : (U*V) * orbitSpec (a*b) (U*V) 3 = (a*b) • orbitSpec (a*b) (U*V) 3 :=
      orbSpec_g_mul (U*V) (a*b) hW3 hab3
    have hOW : orbitSpec (a*b) (U*V) 3 * (U*V) = (a*b) • orbitSpec (a*b) (U*V) 3 :=
      orbSpec_mul_g (U*V) (a*b) hW3 hab3
    have h := orbSpec_mul_eq_zero (U*V) (orbitSpec mu U 3 * orbitSpec nu V 3) (a*b) (mu*nu)
      hWO hOW hWF (Ne.symm he)
    rw [← hP] at h; exact h
  have hne12 : a*(b*Work.KT.omega) ≠ a*b := by
    rw [show a*(b*Work.KT.omega) = (a*b)*Work.KT.omega from by ring]
    exact hne_of Work.KT.omega homega_ne_one
  have hne21 : (a*Work.KT.omega)*b ≠ a*b := by
    rw [show (a*Work.KT.omega)*b = (a*b)*Work.KT.omega from by ring]
    exact hne_of Work.KT.omega homega_ne_one
  have hne33 : (a*Work.KT.omega^2)*(b*Work.KT.omega^2) ≠ a*b := by
    rw [show (a*Work.KT.omega^2)*(b*Work.KT.omega^2) = (a*b)*Work.KT.omega^4 from by ring,
      Work.KT.Psi.K3.omega_pow_four]
    exact hne_of Work.KT.omega homega_ne_one
  have hne13 : a*(b*Work.KT.omega^2) ≠ a*b := by
    rw [show a*(b*Work.KT.omega^2) = (a*b)*Work.KT.omega^2 from by ring]
    exact hne_of (Work.KT.omega^2) homega2_ne_one
  have hne22 : (a*Work.KT.omega)*(b*Work.KT.omega) ≠ a*b := by
    rw [show (a*Work.KT.omega)*(b*Work.KT.omega) = (a*b)*Work.KT.omega^2 from by ring]
    exact hne_of (Work.KT.omega^2) homega2_ne_one
  have hne31 : (a*Work.KT.omega^2)*b ≠ a*b := by
    rw [show (a*Work.KT.omega^2)*b = (a*b)*Work.KT.omega^2 from by ring]
    exact hne_of (Work.KT.omega^2) homega2_ne_one
  have hP1 : P * G1 = G1 := by
    rw [hG1, mul_add, mul_add]
    rw [show P * (A1*B1) = A1*B1 from by rw [hA1, hB1]; exact hPos a b ha hb rfl,
      show P * (A2*B3) = A2*B3 from by rw [hA2, hB3]; exact hPos _ _ hcaw hcbw2 e23,
      show P * (A3*B2) = A3*B2 from by rw [hA3, hB2]; exact hPos _ _ hcaw2 hcbw e32]
  have hP2 : P * G2 = 0 := by
    rw [hG2, mul_add, mul_add]
    rw [show P * (A1*B2) = 0 from by rw [hA1, hB2]; exact hZero _ _ ha hcbw hne12,
      show P * (A2*B1) = 0 from by rw [hA2, hB1]; exact hZero _ _ hcaw hb hne21,
      show P * (A3*B3) = 0 from by rw [hA3, hB3]; exact hZero _ _ hcaw2 hcbw2 hne33]
    simp
  have hP3 : P * G3 = 0 := by
    rw [hG3, mul_add, mul_add]
    rw [show P * (A1*B3) = 0 from by rw [hA1, hB3]; exact hZero _ _ ha hcbw2 hne13,
      show P * (A2*B2) = 0 from by rw [hA2, hB2]; exact hZero _ _ hcaw hcbw hne22,
      show P * (A3*B1) = 0 from by rw [hA3, hB1]; exact hZero _ _ hcaw2 hb hne31]
    simp
  have hGsum : (A1+A2+A3)*(B1+B2+B3) = G1 + G2 + G3 := by
    rw [hG1, hG2, hG3]; noncomm_ring
  calc P = P * 1 := (mul_one P).symm
    _ = P * ((A1+A2+A3)*(B1+B2+B3)) := by rw [hsumU, hsumV, one_mul]
    _ = P * (G1 + G2 + G3) := by rw [hGsum]
    _ = P*G1 + P*G2 + P*G3 := by rw [mul_add, mul_add]
    _ = G1 := by rw [hP1, hP2, hP3, add_zero, add_zero]

end

/-! ## The permutation facts for `uB`, `vB`, `cB` -/

/-- Conjugation of a permutation by an index equivalence. -/
def conjP {α β : Type} (e : α ≃ β) (σ : Equiv.Perm α) : Equiv.Perm β :=
  e.symm.trans (σ.trans e)

theorem conjP_mul {α β : Type} (e : α ≃ β) (σ τ : Equiv.Perm α) :
    conjP e σ * conjP e τ = conjP e (σ * τ) := by
  apply Equiv.ext
  intro x
  simp only [conjP, Equiv.Perm.mul_apply, Equiv.trans_apply, Equiv.symm_apply_apply]

theorem conjP_one {α β : Type} (e : α ≃ β) : conjP e 1 = 1 := by
  apply Equiv.ext
  intro x
  simp only [conjP, Equiv.Perm.one_apply, Equiv.trans_apply, Equiv.apply_symm_apply]

theorem uB_eq_conjP (n : ℕ) :
    Work.KT.PsiC.uB n = conjP (Work.KT.PsiC.Phi n) (Work.KT.PsiC.c1A n) := rfl

theorem vB_eq_conjP (n : ℕ) :
    Work.KT.PsiC.vB n = conjP (Work.KT.PsiC.Phi n) (Work.KT.PsiC.c2A n) := rfl

theorem uB_cube (n : ℕ) :
    Work.KT.PsiC.uB n * Work.KT.PsiC.uB n * Work.KT.PsiC.uB n = 1 := by
  rw [uB_eq_conjP n, conjP_mul, conjP_mul,
    show Work.KT.PsiC.c1A n * Work.KT.PsiC.c1A n * Work.KT.PsiC.c1A n = 1 from
      Work.KT.PsiC.c1A_cube n, conjP_one]

theorem vB_cube (n : ℕ) :
    Work.KT.PsiC.vB n * Work.KT.PsiC.vB n * Work.KT.PsiC.vB n = 1 := by
  rw [vB_eq_conjP n, conjP_mul, conjP_mul,
    show Work.KT.PsiC.c2A n * Work.KT.PsiC.c2A n * Work.KT.PsiC.c2A n = 1 from
      Work.KT.PsiC.c2A_cube n, conjP_one]

theorem uB_mul_vB (n : ℕ) : Work.KT.PsiC.uB n * Work.KT.PsiC.vB n = Work.KT.PsiC.cB n := by
  rw [uB_eq_conjP n, vB_eq_conjP n, conjP_mul, ← Work.KT.PsiC.tA_eq n]
  exact Work.KT.PsiC.Phi_conj_tA n

theorem vB_mul_uB (n : ℕ) : Work.KT.PsiC.vB n * Work.KT.PsiC.uB n = Work.KT.PsiC.cB n := by
  rw [vB_eq_conjP n, uB_eq_conjP n, conjP_mul, ← Work.KT.PsiC.c1A_comm_c2A n,
    ← Work.KT.PsiC.tA_eq n]
  exact Work.KT.PsiC.Phi_conj_tA n

theorem uB_mul_vB_comm (n : ℕ) :
    Work.KT.PsiC.uB n * Work.KT.PsiC.vB n = Work.KT.PsiC.vB n * Work.KT.PsiC.uB n :=
  (uB_mul_vB n).trans (vB_mul_uB n).symm

/-! ## The diagonalisation of `cycProj (cB n) (λ²)` -/

theorem cycProj_diag (A : Type) [Ring A] [Algebra ℂ A] (n : ℕ) (lam : ℂ)
    (hlam : lam ^ 3 = 1) :
    (Work.KT.PsiC.cycProj (Work.KT.PsiC.cB n) (lam ^ 2) :
        Matrix (Work.KT.PsiC.IB n) (Work.KT.PsiC.IB n) A) =
      Work.KT.PsiC.cycProj (Work.KT.PsiC.uB n) lam * Work.KT.PsiC.cycProj (Work.KT.PsiC.vB n) lam +
        (Work.KT.PsiC.cycProj (Work.KT.PsiC.uB n) (lam * Work.KT.omega) * Work.KT.PsiC.cycProj (Work.KT.PsiC.vB n) (lam * Work.KT.omega ^ 2) +
          Work.KT.PsiC.cycProj (Work.KT.PsiC.uB n) (lam * Work.KT.omega ^ 2) * Work.KT.PsiC.cycProj (Work.KT.PsiC.vB n) (lam * Work.KT.omega)) := by
  have hU3 : (Work.KT.PsiC.uB n).permMatrix A * (Work.KT.PsiC.uB n).permMatrix A *
      (Work.KT.PsiC.uB n).permMatrix A = 1 := by
    rw [show (Work.KT.PsiC.uB n).permMatrix A * (Work.KT.PsiC.uB n).permMatrix A *
        (Work.KT.PsiC.uB n).permMatrix A = ((Work.KT.PsiC.uB n).permMatrix A)^3 from
          by noncomm_ring]
    exact Work.KT.PsiC.permMatrix_cube (A:=A) (Work.KT.PsiC.uB n) (uB_cube n)
  have hV3 : (Work.KT.PsiC.vB n).permMatrix A * (Work.KT.PsiC.vB n).permMatrix A *
      (Work.KT.PsiC.vB n).permMatrix A = 1 := by
    rw [show (Work.KT.PsiC.vB n).permMatrix A * (Work.KT.PsiC.vB n).permMatrix A *
        (Work.KT.PsiC.vB n).permMatrix A = ((Work.KT.PsiC.vB n).permMatrix A)^3 from
          by noncomm_ring]
    exact Work.KT.PsiC.permMatrix_cube (A:=A) (Work.KT.PsiC.vB n) (vB_cube n)
  have hUV : (Work.KT.PsiC.uB n).permMatrix A * (Work.KT.PsiC.vB n).permMatrix A =
      (Work.KT.PsiC.vB n).permMatrix A * (Work.KT.PsiC.uB n).permMatrix A := by
    rw [← Matrix.permMatrix_mul (Work.KT.PsiC.vB n) (Work.KT.PsiC.uB n),
        ← Matrix.permMatrix_mul (Work.KT.PsiC.uB n) (Work.KT.PsiC.vB n), uB_mul_vB_comm n]
  have hcB : (Work.KT.PsiC.cB n).permMatrix A =
      (Work.KT.PsiC.uB n).permMatrix A * (Work.KT.PsiC.vB n).permMatrix A := by
    rw [(uB_mul_vB n).symm, Matrix.permMatrix_mul,
        ← Matrix.permMatrix_mul (Work.KT.PsiC.uB n) (Work.KT.PsiC.vB n),
        ← Matrix.permMatrix_mul (Work.KT.PsiC.vB n) (Work.KT.PsiC.uB n),
        ← uB_mul_vB_comm n]
  have hdec := orbSpec_UV_decomp (A := A) (ι := Work.KT.PsiC.IB n)
    ((Work.KT.PsiC.uB n).permMatrix A) ((Work.KT.PsiC.vB n).permMatrix A)
    hU3 hV3 hUV lam lam hlam hlam
  rw [Work.KT.PsiC.cycProj_eq_orbitSpec (Work.KT.PsiC.cB n) (lam^2),
      Work.KT.PsiC.cycProj_eq_orbitSpec (Work.KT.PsiC.uB n) lam,
      Work.KT.PsiC.cycProj_eq_orbitSpec (Work.KT.PsiC.vB n) lam,
      Work.KT.PsiC.cycProj_eq_orbitSpec (Work.KT.PsiC.uB n) (lam*Work.KT.omega),
      Work.KT.PsiC.cycProj_eq_orbitSpec (Work.KT.PsiC.vB n) (lam*Work.KT.omega^2),
      Work.KT.PsiC.cycProj_eq_orbitSpec (Work.KT.PsiC.uB n) (lam*Work.KT.omega^2),
      Work.KT.PsiC.cycProj_eq_orbitSpec (Work.KT.PsiC.vB n) (lam*Work.KT.omega),
      hcB, pow_two lam]
  exact hdec


end Work.PsiC
