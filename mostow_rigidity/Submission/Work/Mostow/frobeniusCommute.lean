import Mathlib
import Submission.Mostow.HLDefs
import Submission.Work.Mostow.StabLift
import Submission.Work.Mostow.norm_gap
import Submission.Work.Mostow.commutatorNormLe
import Submission.Work.Mostow.Margulis.engel_frobenius_orthogonal
import Submission.Work.Mostow.near1OfNearIdAtBall
import Submission.Work.Mostow.BoostTransitive
import Submission.Work.Mostow.margulisPair
import Submission.Work.Mostow.mat_toEuclideanCLM_norm_le

/-! Frobenius commute helpers (finite-order eigenspace projectors). -/

namespace Work.Mostow

noncomputable section

open Submission.Mostow LeanEval.Geometry.MostowRigidity MeasureTheory
open scoped _root_.Matrix _root_.Matrix.Norms.Operator commutatorElement

variable {n : ℕ}

lemma sum_pow_succ_eq (X : Matrix (Fin n) (Fin n) ℂ) (m : ℕ) (hXm : X ^ m = 1) :
    (∑ k ∈ Finset.range m, X ^ (k+1)) = ∑ k ∈ Finset.range m, X ^ k := by
  have hmain : (∑ k ∈ Finset.range m, X ^ (k+1)) + 1
      = (∑ k ∈ Finset.range m, X ^ k) + X ^ m := by
    have h1 := Finset.sum_range_succ' (M := Matrix (Fin n) (Fin n) ℂ) (fun k => X ^ k) m
    have h2 := Finset.sum_range_succ (M := Matrix (Fin n) (Fin n) ℂ) (fun k => X ^ k) m
    rw [h1] at h2; simpa using h2
  rw [hXm] at hmain; exact add_right_cancel hmain

lemma sum_pow_mul_eq (X : Matrix (Fin n) (Fin n) ℂ) (m : ℕ) (hXm : X ^ m = 1) :
    (∑ k ∈ Finset.range m, X ^ k) * X = ∑ k ∈ Finset.range m, X ^ k := by
  rw [Finset.sum_mul]; simp only [← pow_succ]; exact sum_pow_succ_eq X m hXm

lemma inv_self_eq (Y : Matrix (Fin n) (Fin n) ℂ) (m : ℕ) (hm : 0 < m) (hYm : Y^m = 1) :
    Y⁻¹ = Y^(m-1) := by
  apply Matrix.inv_eq_right_inv
  rw [← pow_succ', Nat.sub_add_cancel (by omega : 1 ≤ m), hYm]

lemma mul_inv_self_eq (Y : Matrix (Fin n) (Fin n) ℂ) (m : ℕ) (hm : 0 < m) (hYm : Y^m = 1) :
    Y * Y⁻¹ = 1 := by
  rw [inv_self_eq Y m hm hYm, ← pow_succ', Nat.sub_add_cancel (by omega : 1 ≤ m), hYm]

lemma inv_pow_eq' (Y : Matrix (Fin n) (Fin n) ℂ) (m : ℕ) (hm : 0 < m) (hYm : Y^m = 1) (k : ℕ) :
    (Y⁻¹)^k = (Y^k)⁻¹ := by
  have harith : k + (m-1)*k = m*k := by
    calc k + (m-1)*k = (m-1)*k + k := by omega
      _ = ((m-1)+1)*k := by rw [Nat.add_mul, one_mul]
      _ = m*k := by rw [Nat.sub_add_cancel (by omega : 1 ≤ m)]
  have h : Y^k * (Y⁻¹)^k = 1 := by
    rw [inv_self_eq Y m hm hYm, ← pow_mul, ← pow_add, harith, pow_mul, hYm, one_pow]
  exact (Matrix.inv_eq_right_inv h).symm

lemma sum_inv_pow_eq (Y : Matrix (Fin n) (Fin n) ℂ) (m : ℕ) (hm : 0 < m) (hYm : Y^m = 1) :
    (∑ k ∈ Finset.range m, (Y⁻¹)^k) = ∑ k ∈ Finset.range m, Y^k := by
  have h1 : (∑ k ∈ Finset.range m, (Y⁻¹)^k) = ∑ k ∈ Finset.range m, Y^(m-k) := by
    refine Finset.sum_congr rfl fun k hk => ?_
    have hk' : k ≤ m := le_of_lt (Finset.mem_range.mp hk)
    rw [inv_pow_eq' Y m hm hYm k, show (Y^k)⁻¹ = Y^(m-k) from by
      apply Matrix.inv_eq_right_inv; rw [← pow_add, Nat.add_sub_of_le hk', hYm]]
  have h2 : (∑ k ∈ Finset.range m, Y^(m-k)) = ∑ k ∈ Finset.range m, Y^(k+1) := by
    have h3 : (∑ k ∈ Finset.range m, Y^(m-k)) = ∑ k ∈ Finset.range m, Y^((m-1-k)+1) :=
      Finset.sum_congr rfl fun k hk => by
        rw [show m - 1 - k + 1 = m - k from by have := Finset.mem_range.mp hk; omega]
    rw [h3]; exact Finset.sum_range_reflect (fun j => Y^(j+1)) m
  rw [h1, h2, sum_pow_succ_eq Y m hYm]

lemma commute_pow {X C : Matrix (Fin n) (Fin n) ℂ} (h : C * X = X * C) (k : ℕ) :
    C * X^k = X^k * C := by
  induction k with
  | zero => rw [pow_zero, mul_one, one_mul]
  | succ k ih => rw [pow_succ, ← mul_assoc, ih, mul_assoc, h, ← mul_assoc]

def eigProj (A : Matrix (Fin n) (Fin n) ℂ) (m : ℕ) (lam : ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  (m : ℂ)⁻¹ • ∑ k ∈ Finset.range m, (lam⁻¹ • A) ^ k

lemma eigProj_mul_X (A : Matrix (Fin n) (Fin n) ℂ) (m : ℕ) (lam : ℂ)
    (hXm : (lam⁻¹ • A) ^ m = 1) :
    eigProj A m lam * (lam⁻¹ • A) = eigProj A m lam := by
  unfold eigProj; rw [Matrix.smul_mul, sum_pow_mul_eq _ m hXm]

lemma eigProj_comm (A : Matrix (Fin n) (Fin n) ℂ) (m : ℕ) (lam : ℂ)
    {C : Matrix (Fin n) (Fin n) ℂ} (hCA : C * A = A * C) :
    C * eigProj A m lam = eigProj A m lam * C := by
  have hCX : C * (lam⁻¹ • A) = (lam⁻¹ • A) * C := by
    rw [Matrix.mul_smul, Matrix.smul_mul, hCA]
  have hCS : C * (∑ k ∈ Finset.range m, (lam⁻¹ • A)^k)
      = (∑ k ∈ Finset.range m, (lam⁻¹ • A)^k) * C := by
    rw [Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun k _ => commute_pow hCX k
  unfold eigProj
  rw [Matrix.mul_smul, Matrix.smul_mul, hCS]

lemma eigProj_mul_A (A : Matrix (Fin n) (Fin n) ℂ) (m : ℕ) (lam : ℂ) (hlam : lam ≠ 0)
    (hXm : (lam⁻¹ • A) ^ m = 1) :
    eigProj A m lam * A = lam • eigProj A m lam := by
  have hA : lam • (lam⁻¹ • A) = A := by rw [smul_smul, mul_inv_cancel₀ hlam, one_smul]
  calc eigProj A m lam * A
      = eigProj A m lam * (lam • (lam⁻¹ • A)) := by rw [hA]
    _ = lam • (eigProj A m lam * (lam⁻¹ • A)) := by rw [Matrix.mul_smul]
    _ = lam • eigProj A m lam := by rw [eigProj_mul_X _ _ _ hXm]

lemma eigProj_star (A : Matrix (Fin n) (Fin n) ℂ) (m : ℕ) (hm : 0 < m) (lam : ℂ)
    (hAh : Aᴴ = A⁻¹) (hAmul : A * A⁻¹ = 1) (hlam : lam * star lam = 1) (hlam0 : lam ≠ 0)
    (hXm : (lam⁻¹ • A) ^ m = 1) :
    (eigProj A m lam)ᴴ = eigProj A m lam := by
  have hXh : (lam⁻¹ • A)ᴴ = (lam⁻¹ • A)⁻¹ := by
    rw [Matrix.conjTranspose_smul, hAh]
    rw [show star lam⁻¹ = lam from by rw [star_inv₀, inv_eq_of_mul_eq_one_left hlam]]
    exact (Matrix.inv_eq_right_inv (by
      rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, inv_mul_cancel₀ hlam0, one_smul,
        hAmul])).symm
  have hst : star ((m : ℂ)⁻¹) = (m : ℂ)⁻¹ := by rw [star_inv₀]; simp
  unfold eigProj
  rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_sum, hst]
  congr 1
  rw [show (∑ k ∈ Finset.range m, ((lam⁻¹ • A) ^ k)ᴴ)
      = ∑ k ∈ Finset.range m, ((lam⁻¹ • A)⁻¹) ^ k from
    Finset.sum_congr rfl fun k _ => by rw [Matrix.conjTranspose_pow, hXh]]
  exact sum_inv_pow_eq _ m hm hXm

lemma eigProj_mulVec_eigen (A : Matrix (Fin n) (Fin n) ℂ) (m : ℕ) (hm : 0 < m) (lam : ℂ)
    (hlam : lam ≠ 0) (hXm : (lam⁻¹ • A) ^ m = 1) {v : Fin n → ℂ} (hv : A *ᵥ v = lam • v) :
    eigProj A m lam *ᵥ v = v := by
  have hXv : (lam⁻¹ • A) *ᵥ v = v := by
    rw [Matrix.smul_mulVec, hv, smul_smul, inv_mul_cancel₀ hlam, one_smul]
  have hXkv : ∀ k, ((lam⁻¹ • A)^k) *ᵥ v = v := by
    intro k; induction k with
    | zero => rw [pow_zero, Matrix.one_mulVec]
    | succ k ih => rw [pow_succ, ← Matrix.mulVec_mulVec, hXv, ih]
  unfold eigProj
  rw [Matrix.smul_mulVec, Matrix.sum_mulVec]
  simp only [hXkv]
  rw [Finset.sum_const, Finset.card_range, ← Nat.cast_smul_eq_nsmul ℂ m v,
    inv_smul_smul₀ (by exact_mod_cast hm.ne')]

-- per-lambda argument: ker(A - lam) ⊆ ker(C - 1)
lemma perLam {n : ℕ} (A B C : Matrix (Fin n) (Fin n) ℂ) (m : ℕ) (hm : 0 < m)
    (hAh : Aᴴ = A⁻¹) (hAmul : A * A⁻¹ = 1) (hAm : A ^ m = 1)
    (hAC : C * A = A * C) (hrel : A * B = C * B * A)
    (hpos : ∀ x : Fin n → ℂ, x ≠ 0 → 0 < (star x ⬝ᵥ (B *ᵥ x)).re)
    (lam : ℂ) (hlam0 : lam ≠ 0) (hlamu : lam * star lam = 1) (hlamm : lam ^ m = 1) :
    ∀ x : Fin n → ℂ, A *ᵥ x = lam • x → C *ᵥ x = x := by
  have hXm : (lam⁻¹ • A) ^ m = 1 := by
    rw [smul_pow, hAm, inv_pow, hlamm, inv_one]; simp
  have hstar := eigProj_star A m hm lam hAh hAmul hlamu hlam0 hXm
  have hmulA := eigProj_mul_A A m lam hlam0 hXm
  have hcomm : C * eigProj A m lam = eigProj A m lam * C := eigProj_comm A m lam hAC
  have hcommA : A * eigProj A m lam = eigProj A m lam * A :=
    eigProj_comm A m lam (show A * A = A * A from rfl)
  have hkey : lam • (eigProj A m lam * B) = C * (eigProj A m lam * B) * A := by
    have hRHS : C * (eigProj A m lam * B) * A = (C * eigProj A m lam) * (B * A) := by
      noncomm_ring
    rw [hRHS, hcomm]
    have h2 : (eigProj A m lam * C) * (B * A) = eigProj A m lam * (A * B) := by
      rw [show (eigProj A m lam * C) * (B * A) = eigProj A m lam * (C * B * A) from by noncomm_ring,
        ← hrel]
    rw [h2]
    have h4 : eigProj A m lam * (A * B) = (eigProj A m lam * A) * B := by noncomm_ring
    rw [h4, hmulA]
    exact (Matrix.smul_mul _ _ _).symm
  have hAV : ∀ x : Fin n → ℂ, A *ᵥ (eigProj A m lam *ᵥ x) = lam • (eigProj A m lam *ᵥ x) := by
    intro x
    rw [Matrix.mulVec_mulVec, hcommA, hmulA, Matrix.smul_mulVec]
  set V : Submodule ℂ (Fin n → ℂ) := LinearMap.ker (Matrix.toLin' (A - lam • 1)) with hV
  have hmemV : ∀ x : Fin n → ℂ, x ∈ V ↔ A *ᵥ x = lam • x := by
    intro x
    rw [hV, LinearMap.mem_ker, Matrix.toLin'_apply, Matrix.sub_mulVec]
    rw [Matrix.smul_mulVec, Matrix.one_mulVec, sub_eq_zero, eq_comm]
  have hmapV : ∀ x ∈ V, Matrix.toLin' (eigProj A m lam * B) x ∈ V := by
    intro x hx
    rw [hmemV] at hx ⊢
    rw [Matrix.toLin'_apply]
    have hsplit : (eigProj A m lam * B) *ᵥ x = eigProj A m lam *ᵥ (B *ᵥ x) := by
      rw [Matrix.mulVec_mulVec]
    rw [hsplit, hAV]
  have hinj : Function.Injective ((Matrix.toLin' (eigProj A m lam * B)).restrict hmapV) := by
    intro x y hxy
    have hval : Matrix.toLin' (eigProj A m lam * B) (x : Fin n → ℂ)
        = Matrix.toLin' (eigProj A m lam * B) (y : Fin n → ℂ) := by
      have h := congrArg Subtype.val hxy
      rwa [LinearMap.restrict_apply, LinearMap.restrict_apply] at h
    have h2 : (eigProj A m lam * B) *ᵥ ((x : Fin n → ℂ) - (y : Fin n → ℂ)) = 0 := by
      rw [Matrix.toLin'_apply, Matrix.toLin'_apply] at hval
      rw [Matrix.mulVec_sub, hval, sub_self]
    have hxV : A *ᵥ ((x : Fin n → ℂ) - (y : Fin n → ℂ))
        = lam • ((x : Fin n → ℂ) - (y : Fin n → ℂ)) := by
      have hx2 : A *ᵥ (x : Fin n → ℂ) = lam • (x : Fin n → ℂ) := (hmemV (x : Fin n → ℂ)).mp x.2
      have hy2 : A *ᵥ (y : Fin n → ℂ) = lam • (y : Fin n → ℂ) := (hmemV (y : Fin n → ℂ)).mp y.2
      rw [Matrix.mulVec_sub, hx2, hy2, smul_sub]
    have hz0 : (x : Fin n → ℂ) - (y : Fin n → ℂ) = 0 := by
      by_contra hz
      have hdot : (star ((x : Fin n → ℂ) - (y : Fin n → ℂ)) ⬝ᵥ
          (B *ᵥ ((x : Fin n → ℂ) - (y : Fin n → ℂ)))).re = 0 := by
        have h1 : (star ((x : Fin n → ℂ) - (y : Fin n → ℂ)) ⬝ᵥ
            ((eigProj A m lam * B) *ᵥ ((x : Fin n → ℂ) - (y : Fin n → ℂ)))).re = 0 := by
          rw [h2]; simp
        have hsplit : (eigProj A m lam * B) *ᵥ ((x : Fin n → ℂ) - (y : Fin n → ℂ))
            = eigProj A m lam *ᵥ (B *ᵥ ((x : Fin n → ℂ) - (y : Fin n → ℂ))) := by
          rw [Matrix.mulVec_mulVec]
        have hPi : star ((x : Fin n → ℂ) - (y : Fin n → ℂ)) ᵥ* eigProj A m lam
            = star ((x : Fin n → ℂ) - (y : Fin n → ℂ)) := by
          rw [← hstar, ← Matrix.star_mulVec, eigProj_mulVec_eigen A m hm lam hlam0 hXm hxV]
        rw [hsplit, Matrix.dotProduct_mulVec, hPi] at h1
        exact h1
      exact absurd (hpos _ hz) (not_lt.mpr (le_of_eq hdot))
    exact Subtype.ext (sub_eq_zero.mp hz0)
  have hsurj := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank rfl).mp hinj
  intro x hx
  have hxV : x ∈ V := (hmemV x).mpr hx
  obtain ⟨z, hz⟩ := hsurj ⟨x, hxV⟩
  have hzx : (eigProj A m lam * B) *ᵥ (z : Fin n → ℂ) = x := by
    have h := congrArg Subtype.val hz
    simpa only [LinearMap.restrict_apply, Matrix.toLin'_apply, Subtype.coe_mk, SetLike.coe_eq_coe]
      using h
  have hCz : C *ᵥ ((eigProj A m lam * B) *ᵥ (z : Fin n → ℂ))
      = (eigProj A m lam * B) *ᵥ (z : Fin n → ℂ) := by
    have h := congrArg (fun M => M *ᵥ (z : Fin n → ℂ)) hkey
    rw [Matrix.smul_mulVec] at h
    have hexp : (C * (eigProj A m lam * B) * A) *ᵥ (z : Fin n → ℂ)
        = C *ᵥ ((eigProj A m lam * B) *ᵥ (A *ᵥ (z : Fin n → ℂ))) := by
      have hmat : C * (eigProj A m lam * B) * A = C * ((eigProj A m lam * B) * A) := by
        rw [mul_assoc]
      rw [hmat, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    rw [hexp] at h
    have hzmem : A *ᵥ (z : Fin n → ℂ) = lam • (z : Fin n → ℂ) := (hmemV (z : Fin n → ℂ)).mp z.2
    rw [hzmem, Matrix.mulVec_smul, Matrix.mulVec_smul] at h
    exact (smul_right_injective (Fin n → ℂ) hlam0 h).symm
  rw [hzx] at hCz
  exact hCz


lemma star_mul_self_eq_one {x : ℂ} {m : ℕ} (hm : 0 < m) (hx : x ^ m = 1) : x * star x = 1 := by
  have h1 : ‖x‖ ^ m = 1 := by rw [← norm_pow, hx, norm_one]
  have h2 : ‖x‖ = 1 := by
    have h3 : (0:ℝ) ≤ ‖x‖ := norm_nonneg x
    calc ‖x‖ = (‖x‖ ^ (m:ℝ)) ^ ((m:ℝ)⁻¹) := by
          rw [← Real.rpow_mul h3, mul_inv_cancel₀ (by positivity : (m:ℝ) ≠ 0), Real.rpow_one]
      _ = (1:ℝ) ^ ((m:ℝ)⁻¹) := by rw [Real.rpow_natCast, h1]
      _ = 1 := Real.one_rpow _
  rw [show x * star x = (Complex.normSq x : ℂ) from Complex.mul_conj x,
    Complex.normSq_eq_norm_sq, h2]; norm_num

theorem frobenius_crux {n : ℕ} (A B C : Matrix (Fin n) (Fin n) ℂ) (m : ℕ) (hm : 0 < m)
    (hAh : Aᴴ = A⁻¹) (hAmul : A * A⁻¹ = 1) (hAm : A ^ m = 1)
    (hAC : C * A = A * C) (hrel : A * B = C * B * A)
    (hpos : ∀ x : Fin n → ℂ, x ≠ 0 → 0 < (star x ⬝ᵥ (B *ᵥ x)).re) :
    C = 1 := by
  set zeta := Complex.exp (2 * Real.pi * Complex.I / (m : ℂ)) with hzeta
  have hzprim : IsPrimitiveRoot zeta m := Complex.isPrimitiveRoot_exp m (by omega)
  have hz0 : zeta ≠ 0 := Complex.exp_ne_zero _
  have hkill : ∀ j : ℕ, C * eigProj A m (zeta^j) = eigProj A m (zeta^j) := by
    intro j
    have hzj0 : (zeta^j) ≠ 0 := pow_ne_zero j hz0
    have hzjm : (zeta^j)^m = 1 := by
      rw [← pow_mul, mul_comm, pow_mul, hzprim.pow_eq_one, one_pow]
    have hzju : (zeta^j) * star (zeta^j) = 1 := star_mul_self_eq_one hm hzjm
    have hXm : ((zeta^j)⁻¹ • A)^m = 1 := by rw [smul_pow, hAm, inv_pow, hzjm, inv_one]; simp
    refine Matrix.toLin'.injective (LinearMap.ext fun x => ?_)
    rw [Matrix.toLin'_apply, Matrix.toLin'_apply, ← Matrix.mulVec_mulVec]
    have hy : A *ᵥ (eigProj A m (zeta^j) *ᵥ x) = (zeta^j) • (eigProj A m (zeta^j) *ᵥ x) := by
      rw [Matrix.mulVec_mulVec, eigProj_comm A m (zeta^j) (show A * A = A * A from rfl),
        eigProj_mul_A A m (zeta^j) hzj0 hXm, Matrix.smul_mulVec]
    exact perLam A B C m hm hAh hAmul hAm hAC hrel hpos (zeta^j) hzj0 hzju hzjm _ hy
  have hsum : (∑ j ∈ Finset.range m, eigProj A m (zeta^j)) = 1 := by
    have hstep : ∀ j : ℕ, eigProj A m (zeta^j)
        = (m:ℂ)⁻¹ • ∑ k ∈ Finset.range m, (zeta⁻¹)^(j*k) • A^k := by
      intro j
      rw [eigProj]
      congr 1
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [smul_pow, inv_pow, ← pow_mul, inv_pow]
    simp only [hstep]
    rw [← Finset.smul_sum, Finset.sum_comm]
    rw [show (∑ k ∈ Finset.range m, ∑ j ∈ Finset.range m, (zeta⁻¹)^(j*k) • A^k)
        = ∑ k ∈ Finset.range m, (∑ j ∈ Finset.range m, (zeta⁻¹)^(j*k)) • A^k from by
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [← Finset.sum_smul]]
    have hchar : ∀ k : ℕ, (∑ j ∈ Finset.range m, (zeta⁻¹)^(j*k)) = if m ∣ k then (m:ℂ) else 0 := by
      intro k
      rw [show (∑ j ∈ Finset.range m, (zeta⁻¹)^(j*k)) = ∑ j ∈ Finset.range m, ((zeta⁻¹)^k)^j from by
        refine Finset.sum_congr rfl fun j _ => ?_; rw [← pow_mul, mul_comm]]
      by_cases hk : (zeta⁻¹)^k = 1
      · have hdvd : m ∣ k := (hzprim.pow_eq_one_iff_dvd k).mp (by rw [inv_pow, inv_eq_one] at hk; exact hk)
        rw [if_pos hdvd,
          Finset.sum_congr rfl (fun j _ => by rw [show ((zeta⁻¹)^k)^j = 1 from by rw [hk, one_pow]])]
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
      · rw [if_neg]
        · rw [geom_sum_eq hk m, show ((zeta⁻¹)^k)^m = 1 from by
            rw [← pow_mul, inv_pow, mul_comm, pow_mul, hzprim.pow_eq_one, one_pow, inv_one],
            sub_self, zero_div]
        · intro hdvd
          have : zeta ^ k = 1 := (IsPrimitiveRoot.pow_eq_one_iff_dvd hzprim k).mpr hdvd
          rw [inv_pow, this, inv_one] at hk
          exact hk rfl
    rw [Finset.sum_eq_single 0]
    · rw [hchar 0, if_pos (dvd_zero m), smul_smul,
        inv_mul_cancel₀ (by exact_mod_cast hm.ne'), one_smul, pow_zero]
    · intro k hk hk0
      have hklt : k < m := Finset.mem_range.mp hk
      rw [hchar k, if_neg (by
        intro hdvd
        rw [Nat.dvd_iff_mod_eq_zero, Nat.mod_eq_of_lt hklt] at hdvd
        exact hk0 hdvd)]
      rw [zero_smul]
    · intro h0; exact absurd (Finset.mem_range.mpr hm) h0
  calc C = C * 1 := (mul_one C).symm
    _ = C * (∑ j ∈ Finset.range m, eigProj A m (zeta^j)) := by rw [hsum]
    _ = ∑ j ∈ Finset.range m, C * eigProj A m (zeta^j) := by rw [Finset.mul_sum]
    _ = ∑ j ∈ Finset.range m, eigProj A m (zeta^j) := by simp only [hkill]
    _ = 1 := hsum


/-! ## Bridge: the differential of the action as a real matrix -/

/-- The matrix (in the standard basis) of the differential at `0` of the action of `g`. -/
noncomputable def Dmat (g : PO n 1) : Matrix (Fin n) (Fin n) ℝ :=
  (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin n)).symm (fderiv ℝ (fun u : E n => g • u) 0)

lemma Dmat_toCLM (g : PO n 1) :
    (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin n)).toRingEquiv (Dmat g)
      = fderiv ℝ (fun u : E n => g • u) 0 := by
  rw [Dmat]; exact StarAlgEquiv.apply_symm_apply _ _

lemma Dmat_diff (hI : HypIsometryProp n) (g : PO n 1) :
    DifferentiableAt ℝ (fun u : E n => g • u) 0 :=
  (ContDiff.differentiable_one (hI.2.2.2.2.2.2.2.2.1 g)).differentiableAt

lemma Dmat_mul (hA : POActionProp n) (hI : HypIsometryProp n) {g h : PO n 1}
    (hh : h • (0 : E n) = 0) : Dmat (g * h) = Dmat g * Dmat h := by
  apply (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin n)).injective
  rw [Dmat_toCLM, map_mul, Dmat_toCLM, Dmat_toCLM]
  have hmul : (fun u : E n => (g * h) • u) = (fun u => g • u) ∘ (fun u => h • u) :=
    funext fun u => hA.2.2.2.2.1 g h u
  rw [hmul]
  rw [fderiv_comp (x := (0 : E n)) (f := fun u : E n => h • u) (g := fun u : E n => g • u)
    (by rw [hh]; exact Dmat_diff hI g) (Dmat_diff hI h)]
  rw [hh]
  rfl


/-! ## The lift of an element fixing the origin is Euclidean-orthogonal -/

lemma mink_etime_right_frobeniusCommute {n : ℕ} (y : Fin n ⊕ Fin 1 → ℝ) :
    Hyper.mink y (Hyper.etime n) = - y (Sum.inr 0) := by
  rw [Hyper.mink_apply]
  have h1 : (∑ i : Fin n, y (Sum.inl i) * Hyper.etime n (Sum.inl i)) = 0 :=
    Finset.sum_eq_zero fun i _ => by simp [Hyper.etime, Pi.single_apply]
  have h2 : Hyper.etime n (Sum.inr 0) = 1 := by simp [Hyper.etime, Pi.single_apply]
  rw [h1, h2, mul_one]; ring

lemma LambdaMat_fixZero_mink {n : ℕ} (hA : POActionProp n) {g : PO n 1}
    (hg : g • (0 : E n) = 0) (x y : Fin n ⊕ Fin 1 → ℝ) :
    Hyper.mink (LambdaMat g *ᵥ x) (LambdaMat g *ᵥ y) = Hyper.mink x y :=
  Hyper.mink_mulVec (LambdaMat g) (LambdaMat_isJOrth g) x y

/-- If `g` fixes the origin, `Λ g` preserves the last coordinate. -/
lemma LambdaMat_fixZero_row {n : ℕ} (hA : POActionProp n) {g : PO n 1}
    (hg : g • (0 : E n) = 0) (x : Fin n ⊕ Fin 1 → ℝ) :
    (LambdaMat g *ᵥ x) (Sum.inr 0) = x (Sum.inr 0) := by
  have hfix : LambdaMat g *ᵥ Hyper.etime n = Hyper.etime n := by
    rw [← Hyper.hlift_zero, ← hlift_LambdaMat hA g (0 : E n), hg]
  have h1 := LambdaMat_fixZero_mink hA hg x (Hyper.etime n)
  rw [hfix, mink_etime_right_frobeniusCommute, mink_etime_right_frobeniusCommute] at h1
  linarith

lemma LambdaMat_fixZero_vecRow {n : ℕ} (hA : POActionProp n) {g : PO n 1}
    (hg : g • (0 : E n) = 0) :
    (LambdaMat g)ᵀ *ᵥ Hyper.etime n = Hyper.etime n := by
  funext i
  rw [Matrix.mulVec_apply_eq_sum]
  have h1 : ∀ a : Fin n ⊕ Fin 1,
      (LambdaMat g)ᵀ i a * Hyper.etime n a
        = (LambdaMat g *ᵥ (Pi.single i (1:ℝ))) a * Hyper.etime n a := by
    intro a
    rw [Matrix.transpose_apply, Matrix.mulVec_single_one, Matrix.col_apply]
  rw [Finset.sum_congr rfl (fun a _ => h1 a)]
  have hdot : (∑ a : Fin n ⊕ Fin 1,
        (LambdaMat g *ᵥ (Pi.single i (1:ℝ))) a * Hyper.etime n a)
      = (LambdaMat g *ᵥ (Pi.single i (1:ℝ))) (Sum.inr 0) := by
    rw [Finset.sum_eq_single (Sum.inr 0)]
    · rw [Hyper.etime, Pi.single_eq_same, mul_one]
    · intro b _ hb
      simp [Hyper.etime, Pi.single_apply, hb]
    · intro h; exact absurd (Finset.mem_univ _) h
  rw [hdot]
  have hei : Hyper.etime n i = (Pi.single i (1:ℝ) : Fin n ⊕ Fin 1 → ℝ) (Sum.inr 0) := by
    simp [Hyper.etime, Pi.single_apply, eq_comm]
  rw [hei, ← LambdaMat_fixZero_row hA hg (Pi.single i (1:ℝ))]

lemma LambdaMat_fixZero_orth {n : ℕ} (hA : POActionProp n) {g : PO n 1}
    (hg : g • (0 : E n) = 0) : (LambdaMat g)ᵀ * LambdaMat g = 1 := by
  set e : Fin n ⊕ Fin 1 → ℝ := Hyper.etime n with he
  set E : Matrix (Fin n ⊕ Fin 1) (Fin n ⊕ Fin 1) ℝ := Matrix.of (fun i j => e i * e j) with hE
  have hrow : (LambdaMat g)ᵀ *ᵥ e = e := LambdaMat_fixZero_vecRow hA hg
  have hentry : ∀ i j : Fin n ⊕ Fin 1,
      (pmOneMat (p := Fin n) (q := Fin 1) (α := ℝ) : Matrix _ _ ℝ) i j
        + 2 * (e i * e j) = (if i = j then (1:ℝ) else 0) := by
    intro i j
    rcases i with a | a <;> rcases j with b | b
    · rw [pmOneMat, Matrix.fromBlocks_apply₁₁, Matrix.one_apply, he, Hyper.etime,
        Pi.single_apply, Pi.single_apply]
      by_cases h : a = b <;> simp [h, Sum.inl_injective.eq_iff]
    · rw [pmOneMat, Matrix.fromBlocks_apply₁₂, he, Hyper.etime, Pi.single_apply]
      simp [Sum.inl_ne_inr]
    · rw [pmOneMat, Matrix.fromBlocks_apply₂₁, he, Hyper.etime, Pi.single_apply]
      simp [Sum.inr_ne_inl]
    · fin_cases a; fin_cases b
      simp [pmOneMat, he, Hyper.etime]
      norm_num
  have hsum : (pmOneMat (p := Fin n) (q := Fin 1) (α := ℝ)) + (2:ℝ) • E = 1 := by
    ext i j
    rw [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Matrix.one_apply, hE,
      Matrix.of_apply]
    exact hentry i j
  have hEEL : (LambdaMat g)ᵀ * E * LambdaMat g = E := by
    ext i j
    rw [Matrix.mul_apply, hE, Matrix.of_apply]
    have hstep : ∀ k : Fin n ⊕ Fin 1,
        ((LambdaMat g)ᵀ * E) i k * LambdaMat g k j
          = (∑ a : Fin n ⊕ Fin 1, (LambdaMat g)ᵀ i a * e a) * (e k * LambdaMat g k j) := by
      intro k
      rw [Matrix.mul_apply, Finset.sum_mul, Finset.sum_mul]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [hE, Matrix.of_apply]; ring
    rw [Finset.sum_congr rfl (fun k _ => hstep k)]
    rw [← Finset.mul_sum]
    have h2 : (∑ a : Fin n ⊕ Fin 1, (LambdaMat g)ᵀ i a * e a) = e i := by
      have h := congrFun hrow i
      rwa [Matrix.mulVec_apply_eq_sum] at h
    have h3 : (∑ k : Fin n ⊕ Fin 1, e k * LambdaMat g k j) = e j := by
      have h := congrFun hrow j
      rw [Matrix.mulVec_apply_eq_sum] at h
      rw [← h]
      exact Finset.sum_congr rfl fun k _ => by rw [Matrix.transpose_apply]; ring
    rw [h2, h3]
  have hJL : (LambdaMat g)ᵀ * (pmOneMat (p := Fin n) (q := Fin 1) (α := ℝ)) * LambdaMat g
      = pmOneMat (p := Fin n) (q := Fin 1) (α := ℝ) := LambdaMat_isJOrth g
  calc (LambdaMat g)ᵀ * LambdaMat g
      = (LambdaMat g)ᵀ * (1 : Matrix (Fin n ⊕ Fin 1) (Fin n ⊕ Fin 1) ℝ) * LambdaMat g := by
        rw [mul_one]
    _ = (LambdaMat g)ᵀ * (pmOneMat (p := Fin n) (q := Fin 1) (α := ℝ) + (2:ℝ) • E)
          * LambdaMat g := by rw [hsum]
    _ = (LambdaMat g)ᵀ * (pmOneMat (p := Fin n) (q := Fin 1) (α := ℝ)) * LambdaMat g
          + (2:ℝ) • ((LambdaMat g)ᵀ * E * LambdaMat g) := by
        rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul]
    _ = pmOneMat (p := Fin n) (q := Fin 1) (α := ℝ) + (2:ℝ) • E := by rw [hJL, hEEL]
    _ = 1 := hsum


/-! ## The Euclidean isometry attached to an orthogonal matrix -/

lemma clo_norm {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι ℝ) (hM : Matrix.transpose M * M = 1) (x : EuclideanSpace ℝ ι) :
    ‖(Matrix.toEuclideanCLM (𝕜 := ℝ) (n := ι) M) x‖ = ‖x‖ := by
  have h1 : ‖(Matrix.toEuclideanCLM (𝕜 := ℝ) (n := ι) M) x‖ ^ 2
      = ∑ i, ((Matrix.toEuclideanCLM (𝕜 := ℝ) (n := ι) M) x) i
          * ((Matrix.toEuclideanCLM (𝕜 := ℝ) (n := ι) M) x) i := by
    rw [← real_inner_self_eq_norm_sq, EuclideanSpace.inner_eq_star_dotProduct]
    simp only [dotProduct, star_trivial]
  have h2 : ‖x‖ ^ 2 = ∑ i, x i * x i := by
    rw [← real_inner_self_eq_norm_sq, EuclideanSpace.inner_eq_star_dotProduct]
    simp only [dotProduct, star_trivial]
  have hTx : ∀ i, ((Matrix.toEuclideanCLM (𝕜 := ℝ) (n := ι) M) x) i
      = (M *ᵥ (fun i => x i)) i := by
    intro i
    rw [Matrix.ofLp_toEuclideanCLM]
  have hsq : ‖(Matrix.toEuclideanCLM (𝕜 := ℝ) (n := ι) M) x‖ ^ 2 = ‖x‖ ^ 2 := by
    rw [h1, h2]
    simp only [hTx]
    have hdot : (M *ᵥ (fun i => x i)) ⬝ᵥ (M *ᵥ (fun i => x i))
        = (fun i => x i) ⬝ᵥ (fun i => x i) := by
      rw [Matrix.dotProduct_mulVec, Matrix.vecMul_mulVec, hM, Matrix.vecMul_one]
    rw [show (∑ i, (M *ᵥ (fun i => x i)) i * (M *ᵥ (fun i => x i)) i)
        = (M *ᵥ (fun i => x i)) ⬝ᵥ (M *ᵥ (fun i => x i)) from rfl, hdot]
    rfl
  nlinarith [hsq, norm_nonneg ((Matrix.toEuclideanCLM (𝕜 := ℝ) (n := ι) M) x), norm_nonneg x]

lemma clo_isometry {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι ℝ) (hM : Matrix.transpose M * M = 1) :
    Isometry (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := ι) M) := by
  intro x y
  rw [edist_dist, edist_dist, dist_eq_norm, dist_eq_norm, ← map_sub, clo_norm M hM (x - y)]

/-- The Euclidean isometry of `EuclideanSpace ℝ ι` given by an orthogonal real matrix. -/
noncomputable def matIsom {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι ℝ) (hM : Matrix.transpose M * M = 1) :
    EuclideanSpace ℝ ι ≃ₗᵢ[ℝ] EuclideanSpace ℝ ι :=
  LinearIsometryEquiv.ofSurjective
    (LinearMap.toLinearIsometry (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := ι) M).toLinearMap
      (clo_isometry M hM))
    (by
      have hinj : Function.Injective (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := ι) M) := by
        intro x y hxy
        have h := clo_norm M hM (x - y)
        rw [map_sub, hxy, sub_self, norm_zero] at h
        exact sub_eq_zero.mp (norm_eq_zero.mp h.symm)
      exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank rfl).mp hinj)

lemma matIsom_apply {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι ℝ) (hM : Matrix.transpose M * M = 1) (x : EuclideanSpace ℝ ι) :
    matIsom M hM x = (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := ι) M) x := rfl

lemma matIsom_coe {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι ℝ) (hM : Matrix.transpose M * M = 1) :
    (matIsom M hM : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι)
      = Matrix.toEuclideanCLM (𝕜 := ℝ) (n := ι) M :=
  ContinuousLinearMap.ext fun x => matIsom_apply M hM x

lemma matIsom_mul {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M N : Matrix ι ι ℝ) (hM : Matrix.transpose M * M = 1)
    (hN : Matrix.transpose N * N = 1) (hMN : Matrix.transpose (M * N) * (M * N) = 1) :
    matIsom (M * N) hMN = matIsom M hM * matIsom N hN := by
  refine LinearIsometryEquiv.ext fun x => ?_
  rw [LinearIsometryEquiv.mul_def, LinearIsometryEquiv.trans_apply,
    matIsom_apply, matIsom_apply, matIsom_apply, map_mul]
  rfl

lemma matIsom_one {ι : Type*} [Fintype ι] [DecidableEq ι]
    (h1 : Matrix.transpose (1 : Matrix ι ι ℝ) * 1 = 1) :
    matIsom (1 : Matrix ι ι ℝ) h1 = 1 := by
  refine LinearIsometryEquiv.ext fun x => ?_
  rw [matIsom_apply, map_one]
  rfl

lemma matIsom_injective {ι : Type*} [Fintype ι] [DecidableEq ι]
    {M N : Matrix ι ι ℝ} {hM : Matrix.transpose M * M = 1}
    {hN : Matrix.transpose N * N = 1} (h : matIsom M hM = matIsom N hN) : M = N := by
  have h2 : (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := ι) M)
      = Matrix.toEuclideanCLM (𝕜 := ℝ) (n := ι) N := by
    rw [← matIsom_coe M hM, ← matIsom_coe N hN, h]
  exact (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := ι)).injective h2


/-! ## Norm control: entrywise closeness to the operator norm -/

lemma dE_eq_one_matrix {n : ℕ} (i j : Fin n ⊕ Fin 1) :
    dE n i j = (1 : Matrix (Fin n ⊕ Fin 1) (Fin n ⊕ Fin 1) ℝ) i j := by
  rw [← mat_one_entry (n := n) i j, mat_one_coe]

lemma clm_norm_le_of_entry {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (q : ℝ) (hq : 0 ≤ q) (hAq : ∀ i j, |A i j| ≤ q) :
    ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (n := ι) A‖ ≤ (Fintype.card ι : ℝ) * q := by
  have hA2 : ∀ i j, (A i j) ^ 2 ≤ q ^ 2 := by
    intro i j
    have h1 : |A i j| ≤ |q| := by rw [abs_of_nonneg hq]; exact hAq i j
    exact (sq_le_sq).mpr h1
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) ?_
  intro x
  set v : ι → ℝ := x.ofLp
  have hxnorm : ‖x‖ ^ 2 = ∑ j, (v j) ^ 2 := by rw [EuclideanSpace.real_norm_sq_eq]
  have hterm : ∀ i, ((A *ᵥ v) i) ^ 2 ≤ ((Fintype.card ι : ℝ) * q ^ 2) * (∑ j, (v j) ^ 2) := by
    intro i
    have h1 : ((A *ᵥ v) i) ^ 2 = (∑ j, A i j * v j) ^ 2 := by
      rw [Matrix.mulVec_apply_eq_sum]
    rw [h1]
    calc (∑ j, A i j * v j) ^ 2
        ≤ (∑ j, (A i j) ^ 2) * (∑ j, (v j) ^ 2) := Finset.sum_mul_sq_le_sq_mul_sq _ _ _
      _ ≤ ((Fintype.card ι : ℝ) * q ^ 2) * (∑ j, (v j) ^ 2) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          calc (∑ j, (A i j) ^ 2) ≤ ∑ j, q ^ 2 := Finset.sum_le_sum (fun j _ => hA2 i j)
            _ = (Fintype.card ι : ℝ) * q ^ 2 := by
                rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have key : ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (n := ι) A x‖ ^ 2
      ≤ (((Fintype.card ι : ℝ) * q) * ‖x‖) ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    have hof : ∀ i, (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := ι) A x).ofLp i = (A *ᵥ v) i := by
      intro i
      rw [Matrix.ofLp_toEuclideanCLM]
    simp only [hof]
    calc (∑ i, ((A *ᵥ v) i) ^ 2)
        ≤ ∑ i, ((Fintype.card ι : ℝ) * q ^ 2) * (∑ j, (v j) ^ 2) :=
          Finset.sum_le_sum (fun i _ => hterm i)
      _ = (((Fintype.card ι : ℝ) * q) * ‖x‖) ^ 2 := by
          rw [← hxnorm, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
          ring
  have hle := (sq_le_sq.mp key)
  rwa [abs_of_nonneg (norm_nonneg _), abs_of_nonneg (by positivity)] at hle

/-- `NearIdAt g 0 η` makes the lift of `g` `O(η)`-close to the identity in operator norm. -/
lemma nearIdAt_lift_close (n : ℕ) (hA : POActionProp n) (hI : HypIsometryProp n) :
    ∃ C : ℝ, 0 < C ∧ ∀ (g : PO n 1) (η : ℝ), 0 < η → η ≤ 1 → NearIdAt g (0 : E n) η →
      ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin n ⊕ Fin 1) (LambdaMat g - 1)‖ ≤ C * η := by
  obtain ⟨C1, hC1pos, hC1⟩ := near1OfNearIdAtBall n hA hI
  refine ⟨(Fintype.card (Fin n ⊕ Fin 1) : ℝ) * C1, by positivity, ?_⟩
  intro g η hη hη1 hnear
  have hq : ∀ i j : Fin n ⊕ Fin 1, |(LambdaMat g - 1) i j| ≤ C1 * η := by
    intro i j
    have h := hC1 η hη hη1 g hnear i j
    rw [mat_ToO] at h
    simpa [Matrix.sub_apply, dE_eq_one_matrix] using h
  have hqpos : 0 ≤ C1 * η := by positivity
  calc ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin n ⊕ Fin 1) (LambdaMat g - 1)‖
      ≤ (Fintype.card (Fin n ⊕ Fin 1) : ℝ) * (C1 * η) := clm_norm_le_of_entry _ _ hqpos hq
    _ = ((Fintype.card (Fin n ⊕ Fin 1) : ℝ) * C1) * η := by ring

/-- Contraction of the multiplicative commutator in a normed ring, copied for the operator-norm
setting used by `engel_frobenius_orthogonal`. -/
lemma commutator_contraction_ring {R : Type*} [NormedRing R] [NormOneClass R]
    (A B A' B' : R) (hAA' : A * A' = 1) (hBB' : B * B' = 1)
    (hAn : ‖A - 1‖ ≤ 1 / 4) (hBn : ‖B - 1‖ ≤ 1 / 4) :
    ‖A * B * A' * B' - 1‖ ≤ 4 * ‖A - 1‖ * ‖B - 1‖ := by
  have hA'norm : ‖A'‖ ≤ 4 / 3 := by
    have h1 : A' = 1 - (A - 1) * A' := by
      have h3 : (1 + (A - 1)) * A' = 1 := by
        rw [show (1 + (A - 1)) = A from by abel]; exact hAA'
      rw [add_mul, one_mul] at h3
      exact eq_sub_iff_add_eq.mpr h3
    have h2 : ‖A'‖ ≤ 1 + ‖A - 1‖ * ‖A'‖ := by
      calc ‖A'‖ = ‖1 - (A - 1) * A'‖ := by conv_lhs => rw [h1]
        _ ≤ ‖(1 : R)‖ + ‖(A - 1) * A'‖ := norm_sub_le _ _
        _ = 1 + ‖(A - 1) * A'‖ := by rw [norm_one]
        _ ≤ 1 + ‖A - 1‖ * ‖A'‖ := by gcongr; exact norm_mul_le _ _
    nlinarith [h2, hAn, norm_nonneg A']
  have hB'norm : ‖B'‖ ≤ 4 / 3 := by
    have h1 : B' = 1 - (B - 1) * B' := by
      have h3 : (1 + (B - 1)) * B' = 1 := by
        rw [show (1 + (B - 1)) = B from by abel]; exact hBB'
      rw [add_mul, one_mul] at h3
      exact eq_sub_iff_add_eq.mpr h3
    have h2 : ‖B'‖ ≤ 1 + ‖B - 1‖ * ‖B'‖ := by
      calc ‖B'‖ = ‖1 - (B - 1) * B'‖ := by conv_lhs => rw [h1]
        _ ≤ ‖(1 : R)‖ + ‖(B - 1) * B'‖ := norm_sub_le _ _
        _ = 1 + ‖(B - 1) * B'‖ := by rw [norm_one]
        _ ≤ 1 + ‖B - 1‖ * ‖B'‖ := by gcongr; exact norm_mul_le _ _
    nlinarith [h2, hBn, norm_nonneg B']
  have hAB : ‖A * B - B * A‖ ≤ 2 * ‖A - 1‖ * ‖B - 1‖ := by
    have he : A * B - B * A = (A - 1) * (B - 1) - (B - 1) * (A - 1) := by
      rw [sub_mul, mul_sub, one_mul, mul_one, sub_mul, mul_sub, one_mul, mul_one]; abel
    rw [he]
    calc ‖(A - 1) * (B - 1) - (B - 1) * (A - 1)‖
        ≤ ‖(A - 1) * (B - 1)‖ + ‖(B - 1) * (A - 1)‖ := norm_sub_le _ _
      _ ≤ ‖A - 1‖ * ‖B - 1‖ + ‖B - 1‖ * ‖A - 1‖ := by
          gcongr <;> exact norm_mul_le _ _
      _ = 2 * ‖A - 1‖ * ‖B - 1‖ := by ring
  have hdec : A * B * A' * B' - 1 = (A * B - B * A) * (A' * B') := by
    have hBA : (B * A) * (A' * B') = 1 := by
      rw [mul_assoc, ← mul_assoc A A' B', hAA', one_mul, hBB']
    rw [sub_mul, hBA]
    rw [mul_assoc]
  have hA'mul : ‖A' * B'‖ ≤ 16 / 9 := by
    calc ‖A' * B'‖ ≤ ‖A'‖ * ‖B'‖ := norm_mul_le _ _
      _ ≤ (4 / 3) * (4 / 3) := by gcongr
      _ = 16 / 9 := by norm_num
  rw [hdec]
  calc ‖(A * B - B * A) * (A' * B')‖
      ≤ ‖A * B - B * A‖ * ‖A' * B'‖ := norm_mul_le _ _
    _ ≤ (2 * ‖A - 1‖ * ‖B - 1‖) * (16 / 9) := by
        refine mul_le_mul hAB hA'mul (norm_nonneg _) ?_
        positivity
    _ ≤ 4 * ‖A - 1‖ * ‖B - 1‖ := by
        nlinarith [norm_nonneg (A - 1), norm_nonneg (B - 1),
          mul_nonneg (norm_nonneg (A - 1)) (norm_nonneg (B - 1))]


/-! ## The lift as a continuous linear map and the isometry it defines -/

noncomputable def Lmat {n : ℕ} (g : PO n 1) :
    EuclideanSpace ℝ (Fin n ⊕ Fin 1) →L[ℝ] EuclideanSpace ℝ (Fin n ⊕ Fin 1) :=
  Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin n ⊕ Fin 1) (LambdaMat g)

lemma Lmat_mul {n : ℕ} (hA : POActionProp n) (g h : PO n 1) :
    Lmat (g * h) = Lmat g * Lmat h := by
  simp only [Lmat]
  rw [LambdaMat_mul hA g h, map_mul]

lemma Lmat_sub_one {n : ℕ} (g : PO n 1) :
    Lmat g - 1 = Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin n ⊕ Fin 1) (LambdaMat g - 1) := by
  rw [Lmat, map_sub, map_one]

lemma smul_zero_mul {n : ℕ} (hA : POActionProp n) {g h : PO n 1}
    (hg : g • (0 : E n) = 0) (hh : h • (0 : E n) = 0) : (g * h) • (0 : E n) = 0 := by
  rw [hA.2.2.2.2.1, hh, hg]

lemma smul_zero_inv {n : ℕ} (hA : POActionProp n) {g : PO n 1} (hg : g • (0 : E n) = 0) :
    g⁻¹ • (0 : E n) = 0 := by
  have h1 : g⁻¹ • (g • (0 : E n)) = (g⁻¹ * g) • (0 : E n) :=
    (hA.2.2.2.2.1 g⁻¹ g (0 : E n)).symm
  rw [hg, inv_mul_cancel, hA.2.2.2.1] at h1
  exact h1

noncomputable def Iso {n : ℕ} (hA : POActionProp n) (g : PO n 1) (hg : g • (0 : E n) = 0) :
    EuclideanSpace ℝ (Fin n ⊕ Fin 1) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n ⊕ Fin 1) :=
  matIsom (LambdaMat g) (LambdaMat_fixZero_orth hA hg)

lemma Iso_coe {n : ℕ} (hA : POActionProp n) {g : PO n 1} (hg : g • (0 : E n) = 0) :
    (Iso hA g hg : EuclideanSpace ℝ (Fin n ⊕ Fin 1) →L[ℝ]
        EuclideanSpace ℝ (Fin n ⊕ Fin 1)) = Lmat g :=
  matIsom_coe _ _

lemma Iso_apply {n : ℕ} (hA : POActionProp n) {g : PO n 1} (hg : g • (0 : E n) = 0)
    (x : EuclideanSpace ℝ (Fin n ⊕ Fin 1)) : Iso hA g hg x = Lmat g x :=
  matIsom_apply _ _ x

lemma Iso_mul {n : ℕ} (hA : POActionProp n) {g h : PO n 1} (hg : g • (0 : E n) = 0)
    (hh : h • (0 : E n) = 0) :
    Iso hA (g * h) (smul_zero_mul hA hg hh) = Iso hA g hg * Iso hA h hh := by
  refine LinearIsometryEquiv.ext fun x => ?_
  rw [LinearIsometryEquiv.mul_def, LinearIsometryEquiv.trans_apply,
    Iso_apply, Iso_apply, Iso_apply]
  simp only [Lmat]
  rw [LambdaMat_mul hA g h, map_mul]
  rfl

lemma Iso_one {n : ℕ} (hA : POActionProp n) : Iso hA 1 (hA.2.2.2.1 (0 : E n)) = 1 := by
  refine LinearIsometryEquiv.ext fun x => ?_
  rw [Iso_apply]
  simp only [Lmat, LambdaMat_one hA, map_one]
  rfl

lemma Iso_mul_inv {n : ℕ} (hA : POActionProp n) {g : PO n 1} (hg : g • (0 : E n) = 0) :
    Iso hA g hg * Iso hA g⁻¹ (smul_zero_inv hA hg) = 1 := by
  refine LinearIsometryEquiv.ext fun x => ?_
  rw [LinearIsometryEquiv.mul_def, LinearIsometryEquiv.trans_apply,
    Iso_apply, Iso_apply]
  simp only [Lmat]
  rw [← ContinuousLinearMap.mul_apply, ← map_mul, ← LambdaMat_mul hA g g⁻¹, mul_inv_cancel,
    LambdaMat_one hA, map_one]
  rfl

lemma Iso_inv {n : ℕ} (hA : POActionProp n) {g : PO n 1} (hg : g • (0 : E n) = 0) :
    (Iso hA g hg)⁻¹ = Iso hA g⁻¹ (smul_zero_inv hA hg) :=
  inv_eq_of_mul_eq_one_right (Iso_mul_inv hA hg)

lemma Iso_commutator {n : ℕ} (hA : POActionProp n) {g h : PO n 1}
    (hg : g • (0 : E n) = 0) (hh : h • (0 : E n) = 0) :
    Iso hA g hg * Iso hA h hh * (Iso hA g hg)⁻¹ * (Iso hA h hh)⁻¹
      = Iso hA (g * h * g⁻¹ * h⁻¹)
          (smul_zero_mul hA (smul_zero_mul hA (smul_zero_mul hA hg hh) (smul_zero_inv hA hg))
            (smul_zero_inv hA hh)) := by
  rw [Iso_inv hA hg, Iso_inv hA hh]
  rw [← Iso_mul hA hg hh]
  rw [← Iso_mul hA (smul_zero_mul hA hg hh) (smul_zero_inv hA hg)]
  rw [← Iso_mul hA (smul_zero_mul hA (smul_zero_mul hA hg hh) (smul_zero_inv hA hg))
    (smul_zero_inv hA hh)]

lemma Iso_close {n : ℕ} (hA : POActionProp n) (hI : HypIsometryProp n) :
    ∃ C : ℝ, 0 < C ∧ ∀ (g : PO n 1) (η : ℝ), 0 < η → η ≤ 1 → NearIdAt g (0 : E n) η →
      ∀ (hg : g • (0 : E n) = 0),
      ‖(Iso hA g hg :
        EuclideanSpace ℝ (Fin n ⊕ Fin 1) →L[ℝ] EuclideanSpace ℝ (Fin n ⊕ Fin 1)) - 1‖
        ≤ C * η := by
  obtain ⟨C1, hC1pos, hC1⟩ := nearIdAt_lift_close n hA hI
  refine ⟨C1, hC1pos, ?_⟩
  intro g η hη hη1 hnear hg
  rw [Iso_coe, Lmat_sub_one]
  exact hC1 g η hη hη1 hnear

def seqG {G : Type*} [Group G] (a b : G) : ℕ → G
  | 0 => b
  | (k + 1) => a * seqG a b k * a⁻¹ * (seqG a b k)⁻¹

@[simp] lemma seqG_zero {G : Type*} [Group G] (a b : G) : seqG a b 0 = b := rfl

@[simp] lemma seqG_succ {G : Type*} [Group G] (a b : G) (k : ℕ) :
    seqG a b (k + 1) = a * seqG a b k * a⁻¹ * (seqG a b k)⁻¹ := rfl

lemma seqG_eq_comm {G : Type*} [Group G] (a b : G) (k : ℕ) :
    seqG a b (k + 1) = ⁅a, seqG a b k⁆ := by
  rw [seqG_succ]; rfl


lemma seqG_mem {n : ℕ} {H : Subgroup (PO n 1)} {a c : PO n 1} (ha : a ∈ H) (hc : c ∈ H)
    (k : ℕ) : seqG a c k ∈ H := by
  induction k with
  | zero => exact hc
  | succ k ih =>
    rw [seqG_succ]
    exact H.mul_mem (H.mul_mem (H.mul_mem ha ih) (H.inv_mem ha)) (H.inv_mem ih)

lemma seqG_fix {n : ℕ} (hA : POActionProp n) {a c : PO n 1}
    (ha : a • (0 : E n) = 0) (hc : c • (0 : E n) = 0) (k : ℕ) :
    seqG a c k • (0 : E n) = 0 := by
  induction k with
  | zero => exact hc
  | succ k ih =>
    rw [seqG_succ]
    exact smul_zero_mul hA (smul_zero_mul hA (smul_zero_mul hA ha ih) (smul_zero_inv hA ha))
      (smul_zero_inv hA ih)

lemma commute_of_commutator_eq_one {G : Type*} [Group G] {a b : G} (h : ⁅a, b⁆ = 1) :
    a * b = b * a := by
  have h' : a * b * a⁻¹ * b⁻¹ = 1 := by
    rw [← commutatorElement_def]; exact h
  have h2 : a * b * a⁻¹ = b := by
    have h3 : a * b * a⁻¹ * b⁻¹ * b = 1 * b := congrArg (fun x => x * b) h'
    rw [mul_assoc (a * b * a⁻¹) b⁻¹ b, inv_mul_cancel, mul_one, one_mul] at h3
    exact h3
  have h4 : a * b * a⁻¹ * a = b * a := congrArg (fun x => x * a) h2
  rw [mul_assoc (a * b) a⁻¹ a, inv_mul_cancel, mul_one] at h4
  exact h4

lemma LambdaMat_inv' {n : ℕ} (hA : POActionProp n) (g : PO n 1) :
    LambdaMat g⁻¹ = (LambdaMat g)⁻¹ :=
  (Matrix.inv_eq_right_inv (by rw [← LambdaMat_mul hA, mul_inv_cancel, LambdaMat_one hA])).symm

lemma Iso_congr {n : ℕ} (hA : POActionProp n) {g g' : PO n 1}
    (hg : g • (0 : E n) = 0) (hg' : g' • (0 : E n) = 0) (h : g = g') :
    Iso hA g hg = Iso hA g' hg' := by
  subst h; rfl

lemma nearIdAt_conj_at_zero {n : ℕ} (hA : POActionProp n) (hI : HypIsometryProp n)
    {B : PO n 1} {p : E n} (hB : B • p = 0) (η : ℝ) (γ : PO n 1) :
    NearIdAt (B * γ * B⁻¹) (0 : E n) η ↔ NearIdAt γ p η := by
  have hone : ∀ u : E n, (1 : PO n 1) • u = u := hA.2.2.2.1
  have hmul : ∀ (g h : PO n 1) (u : E n), (g * h) • u = g • (h • u) := hA.2.2.2.2.1
  have hisom : ∀ (g : PO n 1) (u v : E n), hdist (g • u) (g • v) = hdist u v :=
    hI.2.2.2.2.2.2.1
  have hBinv : B⁻¹ • (0 : E n) = p := by
    have h := congrArg (fun x : E n => B⁻¹ • x) hB
    rw [← hmul B⁻¹ B p, inv_mul_cancel, hone] at h
    exact h.symm
  constructor
  · intro h u hu
    have hpre : hdist (0 : E n) (B • u) ≤ 1 := by
      rw [← hisom B⁻¹ 0 (B • u), hBinv, ← hmul B⁻¹ B u, inv_mul_cancel, hone]
      exact hu
    have h1 := h (B • u) hpre
    rw [← hisom B⁻¹ (B • u) ((B * γ * B⁻¹) • (B • u))] at h1
    have e1 : B⁻¹ • (B • u) = u := by rw [← hmul B⁻¹ B u, inv_mul_cancel, hone]
    have e2 : B⁻¹ • ((B * γ * B⁻¹) • (B • u)) = γ • u := by
      rw [hmul (B * γ) B⁻¹ (B • u), hmul B γ (B⁻¹ • (B • u)),
        ← hmul B⁻¹ B (γ • (B⁻¹ • (B • u))), inv_mul_cancel, hone,
        ← hmul B⁻¹ B u, inv_mul_cancel, hone]
    rw [e1, e2] at h1
    exact h1
  · intro h v hv
    have hpre : hdist p (B⁻¹ • v) ≤ 1 := by
      rw [← hisom B p (B⁻¹ • v), hB, ← hmul B B⁻¹ v, mul_inv_cancel, hone]
      exact hv
    have h1 := h (B⁻¹ • v) hpre
    rw [← hisom B (B⁻¹ • v) (γ • (B⁻¹ • v))] at h1
    have e1 : B • (B⁻¹ • v) = v := by rw [← hmul B B⁻¹ v, mul_inv_cancel, hone]
    have e2 : B • (γ • (B⁻¹ • v)) = (B * γ * B⁻¹) • v := by
      rw [hmul (B * γ) B⁻¹ v, hmul B γ (B⁻¹ • v)]
    rw [e1, e2] at h1
    exact h1

theorem frobeniusAtOrigin (n : ℕ) (hA : POActionProp n) (hI : HypIsometryProp n) :
    ∃ θ : ℝ, 0 < θ ∧ ∀ (H : Subgroup (PO n 1)), Finite H →
      (∀ h ∈ H, h • (0 : E n) = 0) →
      ∀ a ∈ H, ∀ c ∈ H, NearIdAt a (0 : E n) θ → NearIdAt c (0 : E n) θ → a * c = c * a := by
  classical
  obtain ⟨C, hCpos, hC⟩ := Iso_close hA hI
  refine ⟨min 1 (1 / (8 * C)), lt_min one_pos (by positivity), ?_⟩
  intro H hH hfix a ha c hc haNear hcNear
  set θ : ℝ := min 1 (1 / (8 * C)) with hθdef
  have hθpos : 0 < θ := by rw [hθdef]; positivity
  have hθ1 : θ ≤ 1 := by rw [hθdef]; exact min_le_left _ _
  have hCθ : C * θ ≤ 1 / 8 := by
    have h1 : θ ≤ 1 / (8 * C) := by rw [hθdef]; exact min_le_right _ _
    calc C * θ ≤ C * (1 / (8 * C)) := mul_le_mul_of_nonneg_left h1 (le_of_lt hCpos)
      _ = 1 / 8 := by field_simp
  have hafix : a • (0 : E n) = 0 := hfix a ha
  have hcfix : c • (0 : E n) = 0 := hfix c hc
  have hclose : ∀ (g : PO n 1) (hg : g ∈ H), NearIdAt g (0 : E n) θ → ‖Lmat g - 1‖ ≤ C * θ := by
    intro g hg hn
    have h := hC g θ hθpos hθ1 hn (hfix g hg)
    rwa [Iso_coe] at h
  have hseqAll : ∀ k : ℕ, ‖Lmat (seqG a c k) - 1‖ ≤ (1 / 2 : ℝ) ^ k * (C * θ) := by
    intro k
    induction k with
    | zero => simpa using hclose c hc hcNear
    | succ k ih =>
      have hAk : ‖Lmat a - 1‖ ≤ C * θ := hclose a ha haNear
      have hcontr := commutator_contraction_ring (Lmat a) (Lmat (seqG a c k))
        (Lmat a⁻¹) (Lmat (seqG a c k)⁻¹)
        (by rw [← Lmat_mul hA, mul_inv_cancel, Lmat, LambdaMat_one hA, map_one])
        (by rw [← Lmat_mul hA, mul_inv_cancel, Lmat, LambdaMat_one hA, map_one])
        (le_trans hAk (by linarith [hCθ]))
        (le_trans ih (by
          calc (1 / 2 : ℝ) ^ k * (C * θ) ≤ 1 * (C * θ) := mul_le_mul_of_nonneg_right
                (pow_le_one₀ (by norm_num) (by norm_num)) (by positivity)
            _ = C * θ := one_mul _
            _ ≤ 1 / 4 := by linarith [hCθ]))
      rw [seqG_succ]
      have hexp : Lmat (a * seqG a c k * a⁻¹ * (seqG a c k)⁻¹)
          = Lmat a * Lmat (seqG a c k) * Lmat a⁻¹ * Lmat (seqG a c k)⁻¹ := by
        simp only [Lmat_mul hA]
      rw [hexp]
      refine le_trans hcontr ?_
      calc 4 * ‖Lmat a - 1‖ * ‖Lmat (seqG a c k) - 1‖
          ≤ 4 * (C * θ) * ((1 / 2 : ℝ) ^ k * (C * θ)) := by gcongr
        _ ≤ (1 / 2 : ℝ) ^ (k + 1) * (C * θ) := by
            have h1 : 4 * (C * θ) ≤ 1 / 2 := by linarith [hCθ, mul_pos hCpos hθpos]
            have h2 : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ k * (C * θ) := by positivity
            calc 4 * (C * θ) * ((1 / 2 : ℝ) ^ k * (C * θ))
                = (4 * (C * θ)) * ((1 / 2 : ℝ) ^ k * (C * θ)) := by ring
              _ ≤ (1 / 2) * ((1 / 2 : ℝ) ^ k * (C * θ)) :=
                  mul_le_mul_of_nonneg_right h1 h2
              _ = (1 / 2 : ℝ) ^ (k + 1) * (C * θ) := by ring
  have hterm : ∃ N : ℕ, seqG a c N = 1 := by
    by_cases htriv : ∀ h ∈ H, h = 1
    · refine ⟨1, ?_⟩
      rw [seqG_succ, seqG_zero, htriv a ha, htriv c hc]; group
    · push_neg at htriv
      obtain ⟨h0, hh0, hh0ne⟩ := htriv
      haveI : Fintype H := Fintype.ofFinite H
      set S : Finset H := Finset.univ.filter (fun h => h ≠ 1) with hS
      have hSne : S.Nonempty := ⟨⟨h0, hh0⟩, by simp [hS, hh0ne]⟩
      set m : ℝ := S.inf' hSne (fun h => ‖Lmat (h : PO n 1) - 1‖) with hm
      have hmpos : 0 < m := by
        rw [hm, Finset.lt_inf'_iff]
        intro h hh
        have hne : (h : PO n 1) ≠ 1 := fun hh1 => (Finset.mem_filter.mp hh).2 (Subtype.ext hh1)
        have hΛ : LambdaMat (h : PO n 1) - 1 ≠ 0 := fun hz =>
          hne (eq_one_of_LambdaMat_eq_one hA (sub_eq_zero.mp hz))
        have hne' : Lmat (h : PO n 1) - 1 ≠ 0 := by
          intro hz
          have hz2 : (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin n ⊕ Fin 1))
              (LambdaMat (h : PO n 1) - 1)
              = (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin n ⊕ Fin 1)) 0 := by
            rw [map_zero, ← Lmat_sub_one]; exact hz
          exact hΛ ((Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin n ⊕ Fin 1)).injective hz2)
        exact norm_pos_iff.mpr hne'
      obtain ⟨N, hN⟩ : ∃ N : ℕ, (1 / 2 : ℝ) ^ N * (C * θ) < m := by
        obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one
          (show 0 < m / (C * θ) by positivity) (by norm_num : (1 / 2 : ℝ) < 1)
        refine ⟨N, ?_⟩
        have h := mul_lt_mul_of_pos_right hN (by positivity : (0:ℝ) < C * θ)
        rwa [div_mul_cancel₀ m (by positivity : C * θ ≠ 0)] at h
      have hgap : ∀ (h : H), h ≠ 1 → m ≤ ‖Lmat (h : PO n 1) - 1‖ := by
        intro h hh
        rw [hm]
        refine Finset.inf'_le (s := S) (fun h : H => ‖Lmat (h : PO n 1) - 1‖) ?_
        rw [hS]
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hh⟩
      refine ⟨N, ?_⟩
      by_contra hne
      have hmem : seqG a c N ∈ H := seqG_mem ha hc N
      have hle := hgap ⟨seqG a c N, hmem⟩ (fun hh => hne (Subtype.ext_iff.mp hh))
      have h2 := hseqAll N
      linarith [hN, hle, h2]
  -- descent: `seqG a c (j+1) = 1 → seqG a c j = 1` for `j ≥ 1`
  have hstep : ∀ j : ℕ, 1 ≤ j → seqG a c (j + 1) = 1 → seqG a c j = 1 := by
    intro j hj hj1
    set B : PO n 1 := seqG a c (j - 1) with hB
    have hBmem : B ∈ H := seqG_mem ha hc (j - 1)
    have hBfix : B • (0 : E n) = 0 := hfix B hBmem
    have hseqB : ‖Lmat B - 1‖ ≤ C * θ := by
      have := hseqAll (j - 1)
      rw [← hB] at this
      calc ‖Lmat B - 1‖ ≤ (1 / 2 : ℝ) ^ (j - 1) * (C * θ) := this
        _ ≤ 1 * (C * θ) := mul_le_mul_of_nonneg_right
            (pow_le_one₀ (by norm_num) (by norm_num)) (by positivity)
        _ = C * θ := one_mul _
    have hBeq : seqG a c j = ⁅a, B⁆ := by
      have h2 := seqG_eq_comm a c (j - 1)
      rw [show j - 1 + 1 = j from by omega] at h2
      rw [← hB] at h2
      exact h2
    -- `a` commutes with `⁅a, B⁆`
    have hcomm : a * ⁅a, B⁆ = ⁅a, B⁆ * a := by
      have h1 : ⁅a, seqG a c j⁆ = 1 := by
        have h2 := seqG_eq_comm a c j
        rw [hj1] at h2
        exact h2.symm
      have h3 := commute_of_commutator_eq_one h1
      rw [← hBeq]
      exact h3
    have hAc : ‖(Iso hA a hafix : EuclideanSpace ℝ (Fin n ⊕ Fin 1) →L[ℝ]
        EuclideanSpace ℝ (Fin n ⊕ Fin 1)) - 1‖ ≤ 1 / 2 := by
      rw [Iso_coe]
      exact le_trans (hclose a ha haNear) (by linarith [hCθ])
    have hBc : ‖(Iso hA B hBfix : EuclideanSpace ℝ (Fin n ⊕ Fin 1) →L[ℝ]
        EuclideanSpace ℝ (Fin n ⊕ Fin 1)) - 1‖ ≤ 1 / 2 := by
      rw [Iso_coe]
      exact le_trans hseqB (by linarith [hCθ])
    have heq1 : a * B * a⁻¹ * B⁻¹ = seqG a c j := by
      have h2 := seqG_eq_comm a c (j - 1)
      rw [show j - 1 + 1 = j from by omega] at h2
      rw [← hB, commutatorElement_def] at h2
      exact h2.symm
    have hhyp : Iso hA a hafix *
        (Iso hA a hafix * Iso hA B hBfix * (Iso hA a hafix)⁻¹ * (Iso hA B hBfix)⁻¹)
        = (Iso hA a hafix * Iso hA B hBfix * (Iso hA a hafix)⁻¹ * (Iso hA B hBfix)⁻¹)
          * Iso hA a hafix := by
      rw [Iso_commutator hA hafix hBfix]
      have hseqfix : seqG a c j • (0 : E n) = 0 := seqG_fix hA hafix hcfix j
      have hcomfix : (a * B * a⁻¹ * B⁻¹) • (0 : E n) = 0 :=
        smul_zero_mul hA (smul_zero_mul hA (smul_zero_mul hA hafix hBfix) (smul_zero_inv hA hafix))
          (smul_zero_inv hA hBfix)
      rw [Iso_congr hA hcomfix hseqfix heq1]
      rw [← Iso_mul hA hafix hseqfix, ← Iso_mul hA hseqfix hafix]
      exact Iso_congr hA _ _ (by rw [hBeq]; exact hcomm)
    have hef := Margulis.engel_frobenius_orthogonal (Iso hA a hafix) (Iso hA B hBfix) hAc hBc hhyp
    -- extract `seqG a c j = 1`
    have h5 : LambdaMat (a * B) = LambdaMat (B * a) := by
      have h6 : Iso hA (a * B) (smul_zero_mul hA hafix hBfix) = Iso hA (B * a) (smul_zero_mul hA hBfix hafix) := by
        rw [Iso_mul hA hafix hBfix, Iso_mul hA hBfix hafix]
        exact hef
      exact matIsom_injective h6
    have h7 : LambdaMat a * LambdaMat B = LambdaMat B * LambdaMat a := by
      simpa only [LambdaMat_mul hA] using h5
    have h8 : LambdaMat ⁅a, B⁆ = 1 := by
      rw [commutatorElement_def]
      have h9 : LambdaMat (a * B * a⁻¹ * B⁻¹)
          = LambdaMat a * LambdaMat B * LambdaMat a⁻¹ * LambdaMat B⁻¹ := by
        simp only [LambdaMat_mul hA]
      rw [h9, h7, mul_assoc (LambdaMat B) (LambdaMat a) (LambdaMat a⁻¹),
        LambdaMat_inv hA a, mul_one, LambdaMat_inv hA B]
    rw [← hBeq] at h8
    exact eq_one_of_LambdaMat_eq_one hA h8
  -- descend to `seqG a c 1 = 1`
  obtain ⟨N, hN⟩ := hterm
  have hfinal : seqG a c 1 = 1 := by
    have hgen : ∀ j : ℕ, seqG a c j = 1 → seqG a c 1 = 1 := by
      intro j
      induction j with
      | zero =>
        intro h0
        have hc1 : c = 1 := h0
        rw [seqG_succ, seqG_zero, hc1]; simp
      | succ k ih =>
        intro hk1
        rcases Nat.eq_zero_or_pos k with hk | hk
        · subst hk; exact hk1
        · exact ih (hstep k hk hk1)
    exact hgen N hN
  have h1 : seqG a c 1 = ⁅a, c⁆ := seqG_eq_comm a c 0
  have h2 : ⁅a, c⁆ = 1 := by rw [← h1]; exact hfinal
  exact commute_of_commutator_eq_one h2

theorem frobeniusCommute (n : ℕ) (hn : 2 ≤ n) (hA : POActionProp n) (hI : HypIsometryProp n) :
    ∃ θ : ℝ, 0 < θ ∧ ∀ (H : Subgroup (PO n 1)), Finite H → ∀ (p : E n), (∀ h ∈ H, h • p = p) →
      ∀ a ∈ H, ∀ c ∈ H, NearIdAt a p θ → NearIdAt c p θ → a * c = c * a := by
  obtain ⟨θ, hθpos, hθ⟩ := frobeniusAtOrigin n hA hI
  refine ⟨θ, hθpos, ?_⟩
  intro H hH p hfix a ha c hc haNear hcNear
  rcases eq_or_ne p (0 : E n) with hp | hp
  · subst hp
    exact hθ H hH hfix a ha c hc haNear hcNear
  obtain ⟨B, hB⟩ := (BoostTransitive n hA).2 p 0
  have hBinv : B⁻¹ • (0 : E n) = p := by
    have h := congrArg (fun y : E n => B⁻¹ • y) hB
    rw [← hA.2.2.2.2.1 B⁻¹ B p, inv_mul_cancel, hA.2.2.2.1] at h
    exact h.symm
  set a' : PO n 1 := B * a * B⁻¹ with ha'
  set c' : PO n 1 := B * c * B⁻¹ with hc'
  set H' : Subgroup (PO n 1) := H.map (MulAut.conj B) with hH'def
  have hH'fin : Finite ↥H' := by
    have hHset : (H : Set (PO n 1)).Finite := Set.finite_coe_iff.mpr hH
    refine Set.finite_coe_iff.mp ?_
    rw [hH'def, Subgroup.coe_map]
    exact hHset.image _
  have ha'mem : a' ∈ H' := by
    rw [ha', hH'def]
    exact Subgroup.mem_map_of_mem _ ha
  have hc'mem : c' ∈ H' := by
    rw [hc', hH'def]
    exact Subgroup.mem_map_of_mem _ hc
  have hfix' : ∀ h ∈ H', h • (0 : E n) = 0 := by
    intro h hh
    rw [hH'def] at hh
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hh
    change (B * x * B⁻¹) • (0 : E n) = 0
    rw [hA.2.2.2.2.1, hA.2.2.2.2.1, hBinv, hfix x hx, hB]
  have haNear' : NearIdAt a' (0 : E n) θ := by
    rw [ha']
    exact (nearIdAt_conj_at_zero hA hI hB θ a).mpr haNear
  have hcNear' : NearIdAt c' (0 : E n) θ := by
    rw [hc']
    exact (nearIdAt_conj_at_zero hA hI hB θ c).mpr hcNear
  have heq := hθ H' hH'fin hfix' a' ha'mem c' hc'mem haNear' hcNear'
  have h3 : B * (a * c) * B⁻¹ = B * (c * a) * B⁻¹ := by
    have h := heq
    rw [ha', hc'] at h
    have e1 : (B * a * B⁻¹) * (B * c * B⁻¹) = B * (a * c) * B⁻¹ := by group
    have e2 : (B * c * B⁻¹) * (B * a * B⁻¹) = B * (c * a) * B⁻¹ := by group
    rwa [e1, e2] at h
  have h4 : B * (a * c) = B * (c * a) := mul_right_cancel h3
  exact mul_left_cancel h4

end

end Work.Mostow
