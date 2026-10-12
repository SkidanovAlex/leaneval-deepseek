import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseFixB1S.boxMtBoundScalarB1
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option maxHeartbeats 4000000

namespace Work.BoseFixB1S

lemma two_mul_sqrt_mul_le {X Y : ℝ} (hX : 0 ≤ X) (hY : 0 ≤ Y) :
    2 * Real.sqrt (X * Y) ≤ X + Y := by
  have h : Real.sqrt (X * Y) ≤ (X + Y) / 2 := by
    rw [Real.sqrt_le_iff]
    refine ⟨by linarith, ?_⟩
    nlinarith [sq_nonneg (X - Y)]
  linarith

lemma sqrt_add_le' {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    Real.sqrt (x + y) ≤ Real.sqrt x + Real.sqrt y := by
  rw [Real.sqrt_le_iff]
  refine ⟨by positivity, ?_⟩
  have h1 : Real.sqrt x ^ 2 = x := Real.sq_sqrt hx
  have h2 : Real.sqrt y ^ 2 = y := Real.sq_sqrt hy
  nlinarith [mul_nonneg (Real.sqrt_nonneg x) (Real.sqrt_nonneg y)]

lemma ledgerCase1B1 {c S Var nq K0 α Mb C : ℝ}
    (hc : 1 ≤ c) (hK0 : 0 ≤ K0) (hα : 0 ≤ α) (hS : 0 ≤ S) (hVar : 0 ≤ Var) (hnq : 0 ≤ nq)
    (hMb1 : Mb ≤ Var + (S + 1 - c) ^ 2) (hcase : 3 * S ≤ 4 * c)
    (hC : 2048 * K0 ≤ C) :
    8 * K0 * (S + 1 + c) * nq + (α / 4) * Mb + 8 * Real.sqrt (K0 * α * nq * Mb)
      + 4 * Real.sqrt (K0 * α * nq * S) + c * K0 * nq
      ≤ (α / 4) * (S + 1 - c) ^ 2 + α * c + (α / 2) * Var + C * (S + c) * nq := by
  have hc0 : 0 ≤ c := by linarith
  have hcpos : 0 < c := by linarith
  have hK0nq : 0 ≤ K0 * nq := mul_nonneg hK0 hnq
  have hsMb : Real.sqrt (K0 * α * nq * Mb)
      ≤ Real.sqrt (K0 * α * nq) * (Real.sqrt Var + (c + 1)) := by
    have hle : K0 * α * nq * Mb ≤ K0 * α * nq * (Var + (S + 1 - c) ^ 2) :=
      mul_le_mul_of_nonneg_left hMb1 (by positivity)
    have h1 : Real.sqrt (K0 * α * nq * Mb)
        ≤ Real.sqrt (K0 * α * nq * (Var + (S + 1 - c) ^ 2)) := Real.sqrt_le_sqrt hle
    have h2 : Real.sqrt (K0 * α * nq * (Var + (S + 1 - c) ^ 2))
        = Real.sqrt (K0 * α * nq) * Real.sqrt (Var + (S + 1 - c) ^ 2) :=
      Real.sqrt_mul (by positivity : (0:ℝ) ≤ K0 * α * nq) _
    have h3 : Real.sqrt (Var + (S + 1 - c) ^ 2) ≤ Real.sqrt Var + (c + 1) := by
      have h4 := sqrt_add_le' hVar (sq_nonneg (S + 1 - c))
      rw [Real.sqrt_sq_eq_abs] at h4
      have hA : |S + 1 - c| ≤ c + 1 := by rw [abs_le]; constructor <;> linarith
      linarith
    have h5 : Real.sqrt (K0 * α * nq) * Real.sqrt (Var + (S + 1 - c) ^ 2)
        ≤ Real.sqrt (K0 * α * nq) * (Real.sqrt Var + (c + 1)) :=
      mul_le_mul_of_nonneg_left h3 (Real.sqrt_nonneg _)
    linarith [h1, h2, h5]
  have ham1 : 8 * (Real.sqrt (K0 * α * nq) * Real.sqrt Var) ≤ α * Var / 4 + 64 * K0 * nq := by
    have hX : (0:ℝ) ≤ α * Var / 4 := by positivity
    have hY : (0:ℝ) ≤ 64 * (K0 * nq) := by positivity
    have h := two_mul_sqrt_mul_le hX hY
    have hid : (4 * (Real.sqrt (K0 * α * nq) * Real.sqrt Var)) ^ 2
        = (α * Var / 4) * (64 * (K0 * nq)) := by
      rw [mul_pow, mul_pow, Real.sq_sqrt (by positivity : (0:ℝ) ≤ K0 * α * nq), Real.sq_sqrt hVar]
      ring
    rw [← hid, Real.sqrt_sq (by positivity)] at h
    linarith
  have ham2 : 8 * (c + 1) * Real.sqrt (K0 * α * nq)
      ≤ α * c / 2 + 32 * (c + 1) ^ 2 * (K0 * nq) / c := by
    have hX : (0:ℝ) ≤ α * c / 2 := by positivity
    have hY : (0:ℝ) ≤ 32 * (c + 1) ^ 2 * (K0 * nq) / c := by positivity
    have h := two_mul_sqrt_mul_le hX hY
    have hid : (4 * ((c + 1) * Real.sqrt (K0 * α * nq))) ^ 2
        = (α * c / 2) * (32 * (c + 1) ^ 2 * (K0 * nq) / c) := by
      rw [mul_pow, mul_pow, Real.sq_sqrt (by positivity : (0:ℝ) ≤ K0 * α * nq)]
      field_simp
      ring
    rw [← hid, Real.sqrt_sq (by positivity)] at h
    linarith
  have ham3 : 4 * Real.sqrt (K0 * α * nq * S) ≤ α * c / 2 + 8 * S * (K0 * nq) / c := by
    have hX : (0:ℝ) ≤ α * c / 2 := by positivity
    have hY : (0:ℝ) ≤ 8 * S * (K0 * nq) / c := by positivity
    have h := two_mul_sqrt_mul_le hX hY
    have hid : (2 * (Real.sqrt (K0 * α * nq) * Real.sqrt S)) ^ 2
        = (α * c / 2) * (8 * S * (K0 * nq) / c) := by
      rw [mul_pow, mul_pow, Real.sq_sqrt (by positivity : (0:ℝ) ≤ K0 * α * nq), Real.sq_sqrt hS]
      field_simp
      ring
    have hsplit : Real.sqrt (K0 * α * nq * S) = Real.sqrt (K0 * α * nq) * Real.sqrt S :=
      Real.sqrt_mul (by positivity : (0:ℝ) ≤ K0 * α * nq) S
    rw [hsplit]
    rw [← hid, Real.sqrt_sq (by positivity)] at h
    linarith
  have hMb1' : (α / 4) * Mb ≤ (α / 4) * (Var + (S + 1 - c) ^ 2) :=
    mul_le_mul_of_nonneg_left hMb1 (by positivity)
  have hchg : K0 * nq * (8 * (S + 1 + c) + 64 + 32 * (c + 1) ^ 2 / c + 8 * S / c + c)
      ≤ C * (S + c) * nq := by
    have hb : 8 * (S + 1 + c) + 64 + 32 * (c + 1) ^ 2 / c + 8 * S / c + c ≤ 2048 * (S + c) := by
      have h1 : 32 * (c + 1) ^ 2 / c ≤ 32 * c + 96 := by
        rw [div_le_iff₀ hcpos]; nlinarith [hc, hc0]
      have h2 : 8 * S / c ≤ 8 * S := by
        rw [div_le_iff₀ hcpos]; nlinarith [hS, hc]
      linarith
    have h3 : K0 * nq * (8 * (S + 1 + c) + 64 + 32 * (c + 1) ^ 2 / c + 8 * S / c + c)
        ≤ K0 * nq * (2048 * (S + c)) := mul_le_mul_of_nonneg_left hb hK0nq
    have h4 : K0 * nq * (2048 * (S + c)) ≤ C * (S + c) * nq := by
      have hScn : 0 ≤ (S + c) * nq := mul_nonneg (by linarith) hnq
      have e1 : K0 * nq * (2048 * (S + c)) = (2048 * K0) * ((S + c) * nq) := by ring
      have e2 : C * (S + c) * nq = C * ((S + c) * nq) := by ring
      rw [e1, e2]
      exact mul_le_mul_of_nonneg_right hC hScn
    linarith [h3, h4]
  have h8 : 8 * Real.sqrt (K0 * α * nq * Mb)
      ≤ 8 * (Real.sqrt (K0 * α * nq) * Real.sqrt Var) + 8 * ((c + 1) * Real.sqrt (K0 * α * nq)) := by
    linarith [hsMb]
  ring_nf at h8 ham1 ham2 ham3 hMb1' hchg ⊢
  linarith [h8, ham1, ham2, ham3, hMb1', hchg]

lemma ledgerCase2B1 {c S Var nq K0 α Mb C : ℝ}
    (hc : 1 ≤ c) (hK0 : 0 ≤ K0) (hα : 0 ≤ α) (hS : 0 ≤ S) (hVar : 0 ≤ Var) (hnq : 0 ≤ nq)
    (hMb2 : Mb ≤ Var + (S - c - 1) ^ 2 + S) (hcase : 4 * c ≤ 3 * S)
    (hC : 2048 * K0 ≤ C) :
    8 * K0 * (S + 1 + c) * nq + (α / 4) * Mb + 8 * Real.sqrt (K0 * α * nq * Mb)
      + 4 * Real.sqrt (K0 * α * nq * S) + c * K0 * nq
      ≤ (α / 4) * (S + 1 - c) ^ 2 + α * c + (α / 2) * Var + C * (S + c) * nq := by
  have hc0 : 0 ≤ c := by linarith
  have hK0nq : 0 ≤ K0 * nq := mul_nonneg hK0 hnq
  have hsplit : Real.sqrt (K0 * α * nq * S) = Real.sqrt (K0 * α * nq) * Real.sqrt S :=
    Real.sqrt_mul (by positivity : (0:ℝ) ≤ K0 * α * nq) S
  have hsMb : Real.sqrt (K0 * α * nq * Mb)
      ≤ Real.sqrt (K0 * α * nq) * (Real.sqrt Var + 3 * S / 2 + Real.sqrt S) := by
    have hle : K0 * α * nq * Mb ≤ K0 * α * nq * (Var + (S - c - 1) ^ 2 + S) :=
      mul_le_mul_of_nonneg_left hMb2 (by positivity)
    have h1 : Real.sqrt (K0 * α * nq * Mb)
        ≤ Real.sqrt (K0 * α * nq * (Var + (S - c - 1) ^ 2 + S)) := Real.sqrt_le_sqrt hle
    have h2 : Real.sqrt (K0 * α * nq * (Var + (S - c - 1) ^ 2 + S))
        = Real.sqrt (K0 * α * nq) * Real.sqrt (Var + (S - c - 1) ^ 2 + S) :=
      Real.sqrt_mul (by positivity : (0:ℝ) ≤ K0 * α * nq) _
    have hA : |S - c - 1| ≤ 3 * S / 2 := by
      rw [abs_le]; constructor <;> linarith
    have h3 : Real.sqrt (Var + (S - c - 1) ^ 2 + S)
        ≤ Real.sqrt Var + 3 * S / 2 + Real.sqrt S := by
      have h4 : Real.sqrt (Var + (S - c - 1) ^ 2 + S)
          ≤ Real.sqrt (Var + (S - c - 1) ^ 2) + Real.sqrt S := by
        have := sqrt_add_le' (by positivity : (0:ℝ) ≤ Var + (S - c - 1) ^ 2) hS
        rwa [show Var + (S - c - 1) ^ 2 + S = (Var + (S - c - 1) ^ 2) + S from by ring] at this
      have h5 : Real.sqrt (Var + (S - c - 1) ^ 2) ≤ Real.sqrt Var + |S - c - 1| := by
        have := sqrt_add_le' hVar (sq_nonneg (S - c - 1))
        rwa [Real.sqrt_sq_eq_abs] at this
      linarith
    have h6 : Real.sqrt (K0 * α * nq) * Real.sqrt (Var + (S - c - 1) ^ 2 + S)
        ≤ Real.sqrt (K0 * α * nq) * (Real.sqrt Var + 3 * S / 2 + Real.sqrt S) :=
      mul_le_mul_of_nonneg_left h3 (Real.sqrt_nonneg _)
    linarith [h1, h2, h6]
  have ham1 : 8 * (Real.sqrt (K0 * α * nq) * Real.sqrt Var) ≤ α * Var / 4 + 64 * K0 * nq := by
    have hX : (0:ℝ) ≤ α * Var / 4 := by positivity
    have hY : (0:ℝ) ≤ 64 * (K0 * nq) := by positivity
    have h := two_mul_sqrt_mul_le hX hY
    have hid : (4 * (Real.sqrt (K0 * α * nq) * Real.sqrt Var)) ^ 2
        = (α * Var / 4) * (64 * (K0 * nq)) := by
      rw [mul_pow, mul_pow, Real.sq_sqrt (by positivity : (0:ℝ) ≤ K0 * α * nq), Real.sq_sqrt hVar]
      ring
    rw [← hid, Real.sqrt_sq (by positivity)] at h
    linarith
  have ham2 : 12 * S * Real.sqrt (K0 * α * nq) ≤ 3 * α * S / 8 + 96 * S * (K0 * nq) := by
    have hX : (0:ℝ) ≤ 3 * α * S / 8 := by positivity
    have hY : (0:ℝ) ≤ 96 * S * (K0 * nq) := by positivity
    have h := two_mul_sqrt_mul_le hX hY
    have hid : (6 * S * Real.sqrt (K0 * α * nq)) ^ 2
        = (3 * α * S / 8) * (96 * S * (K0 * nq)) := by
      rw [mul_pow, mul_pow, Real.sq_sqrt (by positivity : (0:ℝ) ≤ K0 * α * nq)]
      ring
    rw [← hid, Real.sqrt_sq (by positivity)] at h
    linarith
  have ham3 : 12 * Real.sqrt (K0 * α * nq * S) ≤ 3 * α * S / 8 + 96 * K0 * nq := by
    have hX : (0:ℝ) ≤ 3 * α * S / 8 := by positivity
    have hY : (0:ℝ) ≤ 96 * (K0 * nq) := by positivity
    have h := two_mul_sqrt_mul_le hX hY
    have hid : (6 * (Real.sqrt (K0 * α * nq) * Real.sqrt S)) ^ 2
        = (3 * α * S / 8) * (96 * (K0 * nq)) := by
      rw [mul_pow, mul_pow, Real.sq_sqrt (by positivity : (0:ℝ) ≤ K0 * α * nq), Real.sq_sqrt hS]
      ring
    rw [← hid, Real.sqrt_sq (by positivity)] at h
    rw [hsplit]
    linarith
  have hMb2' : (α / 4) * Mb ≤ (α / 4) * (Var + (S - c - 1) ^ 2 + S) :=
    mul_le_mul_of_nonneg_left hMb2 (by positivity)
  have hchg : K0 * nq * (8 * (S + 1 + c) + 64 + 96 * S + 96 + c) ≤ C * (S + c) * nq := by
    have hb : 8 * (S + 1 + c) + 64 + 96 * S + 96 + c ≤ 2048 * (S + c) := by
      nlinarith [hc, hS]
    have h3 : K0 * nq * (8 * (S + 1 + c) + 64 + 96 * S + 96 + c) ≤ K0 * nq * (2048 * (S + c)) :=
      mul_le_mul_of_nonneg_left hb hK0nq
    have h4 : K0 * nq * (2048 * (S + c)) ≤ C * (S + c) * nq := by
      have hScn : 0 ≤ (S + c) * nq := mul_nonneg (by linarith) hnq
      have e1 : K0 * nq * (2048 * (S + c)) = (2048 * K0) * ((S + c) * nq) := by ring
      have e2 : C * (S + c) * nq = C * ((S + c) * nq) := by ring
      rw [e1, e2]
      exact mul_le_mul_of_nonneg_right hC hScn
    linarith [h3, h4]
  have h8 : 8 * Real.sqrt (K0 * α * nq * Mb) + 4 * Real.sqrt (K0 * α * nq * S)
      ≤ 8 * (Real.sqrt (K0 * α * nq) * Real.sqrt Var) + 12 * S * Real.sqrt (K0 * α * nq)
        + 12 * (Real.sqrt (K0 * α * nq) * Real.sqrt S) := by
    rw [hsplit]
    linarith [hsMb]
  ring_nf at h8 ham1 ham2 ham3 hMb2' hchg ⊢
  linarith [h8, ham1, ham2, ham3, hMb2', hchg]

theorem ledgerCoreB1 {c S Var nq K0 α C Mb : ℝ}
    (hc : 1 ≤ c) (hK0 : 0 ≤ K0) (hα : 0 ≤ α) (hS : 0 ≤ S) (hVar : 0 ≤ Var) (hnq : 0 ≤ nq)
    (hMb0 : 0 ≤ Mb)
    (hMb1 : Mb ≤ Var + (S + 1 - c) ^ 2)
    (hMb2 : Mb ≤ Var + (S - c - 1) ^ 2 + S)
    (hMb3 : Mb ≤ 4 * Var + 4 * S ^ 2 + 2 * c * S)
    (hC : 2048 * K0 ≤ C) :
    8 * K0 * (S + 1 + c) * nq + (α / 4) * Mb + 8 * Real.sqrt (K0 * α * nq * Mb)
      + 4 * Real.sqrt (K0 * α * nq * S) + c * K0 * nq
      ≤ (α / 4) * (S + 1 - c) ^ 2 + α * c + (α / 2) * Var + C * (S + c) * nq := by
  by_cases h : 3 * S ≤ 4 * c
  · exact ledgerCase1B1 hc hK0 hα hS hVar hnq hMb1 h hC
  · exact ledgerCase2B1 hc hK0 hα hS hVar hnq hMb2 (by linarith) hC

theorem boxJointLedgerB1
    {a V μ S Pc Var nq Q P Qm Mt Cosc Cf M1 M2 K K0 C α : ℝ}
    (ha : 0 < a) (hV : 0 < V) (hμ : 0 < μ) (hK : 0 ≤ K) (hK0 : 0 ≤ K0) (hK0K : K0 ≤ K)
    (hC : 2048 * K ≤ C) (hc1 : 1 ≤ μ * V)
    (hCf0 : 0 ≤ Cf) (hCfK : Cf ≤ K0 * a)
    (hM1 : 0 ≤ M1) (hM2 : M1 ≤ M2) (hαeq : M1 = α * a * V) (hα0 : 0 ≤ α)
    (hS : 0 ≤ S) (hPc : 0 ≤ Pc) (hVar : Var = Pc - (S ^ 2 - S)) (hcS2 : S ^ 2 - S ≤ Pc)
    (hnq : 0 ≤ nq) (hMt0 : 0 ≤ Mt)
    (hQ0 : 0 ≤ Q) (hQ : Q ≤ Cf * nq)
    (hP : P ^ 2 ≤ Q * (M1 / V) * S)
    (hQm : Qm ≤ 2 * Cf * (S * nq + (1 + μ * V) * nq))
    (hMt1 : Mt ≤ Var + (S + 1 - μ * V) ^ 2)
    (hMt2 : Mt ≤ Var + (S - μ * V - 1) ^ 2 + S)
    (hMt3 : Mt ≤ 4 * Var + 4 * S ^ 2 + 2 * (μ * V) * S)
    (hCosc : Cosc ^ 2 ≤ Cf * (M1 / V)) (hCosc0 : 0 ≤ Cosc) :
    -(4 / V) * Qm - (M1 / (4 * V ^ 2)) * Mt - (8 * Cosc / V) * Real.sqrt (nq * Mt) - (4 / V) * |P|
      + M1 * ((1 / 4) * (S / V - μ) ^ 2 + (S / V + μ) / (2 * V) + 1 / (4 * V ^ 2))
      + ((1 / 2) * (M2 / V ^ 2) * Pc - (1 / 2) * (M1 / V ^ 2) * (S ^ 2 - S))
      + C * a * (μ + S / V) * nq
      - μ * Q ≥ 0 := by
  have hVpos : (0:ℝ) < V := hV
  have hVar0 : 0 ≤ Var := by rw [hVar]; linarith
  have hC' : 2048 * K0 ≤ C := by linarith
  have hM1V : M1 / V = α * a := by rw [hαeq]; field_simp
  set Mb := min (Var + (S + 1 - μ * V) ^ 2)
      (min (Var + (S - μ * V - 1) ^ 2 + S) (4 * Var + 4 * S ^ 2 + 2 * (μ * V) * S)) with hMbdef
  have hMb1 : Mb ≤ Var + (S + 1 - μ * V) ^ 2 := by rw [hMbdef]; exact min_le_left _ _
  have hMb2 : Mb ≤ Var + (S - μ * V - 1) ^ 2 + S := by
    rw [hMbdef]; exact le_trans (min_le_right _ _) (min_le_left _ _)
  have hMb3 : Mb ≤ 4 * Var + 4 * S ^ 2 + 2 * (μ * V) * S := by
    rw [hMbdef]; exact le_trans (min_le_right _ _) (min_le_right _ _)
  have hMb0 : 0 ≤ Mb := by
    rw [hMbdef]
    exact le_min (by positivity) (le_min (by positivity) (by positivity))
  have hMble : Mt ≤ Mb := by
    rw [hMbdef]; exact le_min hMt1 (le_min hMt2 hMt3)
  have hcore := ledgerCoreB1 (c := μ * V) (S := S) (Var := Var) (nq := nq) (K0 := K0) (α := α)
    (C := C) (Mb := Mb) hc1 hK0 hα0 hS hVar0 hnq hMb0 hMb1 hMb2 hMb3 hC'
  -- individual bounds
  have hb_Qm : 4 * V * Qm ≤ 8 * K0 * a * V * (S + 1 + μ * V) * nq := by
    have h1 : Qm ≤ 2 * Cf * (S + 1 + μ * V) * nq := by nlinarith [hQm]
    have h2 : 4 * V * Qm ≤ 4 * V * (2 * Cf * (S + 1 + μ * V) * nq) :=
      mul_le_mul_of_nonneg_left h1 (by positivity)
    have h3 : 4 * V * (2 * Cf * (S + 1 + μ * V) * nq) ≤ 8 * K0 * a * V * (S + 1 + μ * V) * nq := by
      have h4 : Cf * (S + 1 + μ * V) * nq ≤ K0 * a * (S + 1 + μ * V) * nq := by
        have h5 : 0 ≤ (S + 1 + μ * V) * nq := by positivity
        nlinarith [hCfK, h5]
      nlinarith [h4, hV]
    linarith [h2, h3]
  have hb_Mt : (M1 / 4) * Mt ≤ (α * a * V / 4) * Mb := by
    rw [hαeq]
    exact mul_le_mul_of_nonneg_left hMble (by positivity)
  have hb_Cosc : 8 * V * Cosc * Real.sqrt (nq * Mt) ≤ 8 * a * V * Real.sqrt (K0 * α * nq * Mb) := by
    have hCosc1 : Cosc ≤ Real.sqrt (Cf * (M1 / V)) := by
      rw [← Real.sqrt_sq hCosc0]
      exact Real.sqrt_le_sqrt hCosc
    have hCosc2 : Real.sqrt (Cf * (M1 / V)) ≤ a * Real.sqrt (K0 * α) := by
      have hle : Cf * (M1 / V) ≤ a ^ 2 * (K0 * α) := by rw [hM1V]; nlinarith [hCfK, hα0, ha]
      have h2 := Real.sqrt_le_sqrt hle
      have h3 : Real.sqrt (a ^ 2 * (K0 * α)) = a * Real.sqrt (K0 * α) := by
        rw [Real.sqrt_mul (sq_nonneg a), Real.sqrt_sq (le_of_lt ha)]
      linarith [h2, h3]
    have hMt1' : Real.sqrt (nq * Mt) ≤ Real.sqrt (nq * Mb) :=
      Real.sqrt_le_sqrt (by nlinarith [hnq, hMble])
    have hstep : Cosc * Real.sqrt (nq * Mt) ≤ a * Real.sqrt (K0 * α * nq * Mb) := by
      have h4 : Cosc * Real.sqrt (nq * Mt) ≤ (a * Real.sqrt (K0 * α)) * Real.sqrt (nq * Mb) :=
        mul_le_mul (le_trans hCosc1 hCosc2) hMt1' (Real.sqrt_nonneg _) (by positivity)
      have h5 : (a * Real.sqrt (K0 * α)) * Real.sqrt (nq * Mb) = a * Real.sqrt (K0 * α * nq * Mb) := by
        rw [show K0 * α * nq * Mb = (K0 * α) * (nq * Mb) by ring,
          Real.sqrt_mul (by positivity : (0:ℝ) ≤ K0 * α) (nq * Mb)]
        ring
      linarith [h4, h5]
    nlinarith [hstep, hV]
  have hb_P : 4 * V * |P| ≤ 4 * a * V * Real.sqrt (K0 * α * nq * S) := by
    have hP2 : P ^ 2 ≤ a ^ 2 * (K0 * α * nq * S) := by
      have hQ2 : Q * (M1 / V) * S ≤ (Cf * nq) * (α * a * S) := by
        rw [hM1V]
        have hσ : 0 ≤ α * a * S := by positivity
        calc Q * (α * a) * S = Q * (α * a * S) := by ring
          _ ≤ (Cf * nq) * (α * a * S) := mul_le_mul_of_nonneg_right hQ hσ
      have h5 : (Cf * nq) * (α * a * S) ≤ (K0 * a * nq) * (α * a * S) := by
        have hσ : 0 ≤ nq * (α * a * S) := by positivity
        calc (Cf * nq) * (α * a * S) = Cf * (nq * (α * a * S)) := by ring
          _ ≤ (K0 * a) * (nq * (α * a * S)) := mul_le_mul_of_nonneg_right hCfK hσ
          _ = (K0 * a * nq) * (α * a * S) := by ring
      have h6 : (K0 * a * nq) * (α * a * S) = a ^ 2 * (K0 * α * nq * S) := by ring
      linarith [hP, hQ2, h5, h6]
    have h7 : |P| ≤ a * Real.sqrt (K0 * α * nq * S) := by
      have h8 : |P| = Real.sqrt (P ^ 2) := (Real.sqrt_sq_eq_abs P).symm
      rw [h8]
      have h9 : Real.sqrt (P ^ 2) ≤ Real.sqrt (a ^ 2 * (K0 * α * nq * S)) := Real.sqrt_le_sqrt hP2
      have h10 : Real.sqrt (a ^ 2 * (K0 * α * nq * S)) = a * Real.sqrt (K0 * α * nq * S) := by
        rw [Real.sqrt_mul (sq_nonneg a), Real.sqrt_sq (le_of_lt ha)]
      linarith [h9, h10]
    nlinarith [h7, hV]
  have hb_Q : μ * V ^ 2 * Q ≤ a * V * (μ * V) * K0 * nq := by
    have h1 : Q ≤ K0 * a * nq := by nlinarith [hQ, hCfK, hnq, hCf0]
    have h2 := mul_le_mul_of_nonneg_left h1 (by positivity : (0:ℝ) ≤ μ * V ^ 2)
    have he : μ * V ^ 2 * (K0 * a * nq) = a * V * (μ * V) * K0 * nq := by ring
    linarith [h2, he]
  have hb_G1 : M1 * V ^ 2 * ((1 / 4) * (S / V - μ) ^ 2 + (S / V + μ) / (2 * V) + 1 / (4 * V ^ 2))
      = a * V * ((α / 4) * (S + 1 - μ * V) ^ 2 + α * (μ * V)) := by
    rw [hαeq]
    field_simp
    ring
  have hb_pcb : a * V * ((α / 2) * Var) ≤ (1 / 2) * M2 * Pc - (1 / 2) * M1 * (S ^ 2 - S) := by
    have hM2' : α * a * V ≤ M2 := by linarith [hM2, hαeq]
    rw [hVar, hαeq]
    nlinarith [hM2', hPc]
  have hb_C : C * a * V * (S + μ * V) * nq = a * V * (C * (S + μ * V) * nq) := by ring
  have hD : 0 ≤ (α / 4) * (S + 1 - μ * V) ^ 2 + α * (μ * V) + (α / 2) * Var + C * (S + μ * V) * nq
      - (8 * K0 * (S + 1 + μ * V) * nq + (α / 4) * Mb + 8 * Real.sqrt (K0 * α * nq * Mb)
        + 4 * Real.sqrt (K0 * α * nq * S) + (μ * V) * K0 * nq) := by linarith [hcore]
  suffices h : 0 ≤ ( -4 * V * Qm - (M1 / 4) * Mt - 8 * V * Cosc * Real.sqrt (nq * Mt) - 4 * V * |P|
      + M1 * V ^ 2 * ((1 / 4) * (S / V - μ) ^ 2 + (S / V + μ) / (2 * V) + 1 / (4 * V ^ 2))
      + ((1 / 2) * M2 * Pc - (1 / 2) * M1 * (S ^ 2 - S))
      + C * a * V * (S + μ * V) * nq
      - μ * V ^ 2 * Q) by
    have hscale : ( -4 * V * Qm - (M1 / 4) * Mt - 8 * V * Cosc * Real.sqrt (nq * Mt) - 4 * V * |P|
        + M1 * V ^ 2 * ((1 / 4) * (S / V - μ) ^ 2 + (S / V + μ) / (2 * V) + 1 / (4 * V ^ 2))
        + ((1 / 2) * M2 * Pc - (1 / 2) * M1 * (S ^ 2 - S))
        + C * a * V * (S + μ * V) * nq
        - μ * V ^ 2 * Q) = V ^ 2 * (-(4 / V) * Qm - (M1 / (4 * V ^ 2)) * Mt
        - (8 * Cosc / V) * Real.sqrt (nq * Mt) - (4 / V) * |P|
        + M1 * ((1 / 4) * (S / V - μ) ^ 2 + (S / V + μ) / (2 * V) + 1 / (4 * V ^ 2))
        + ((1 / 2) * (M2 / V ^ 2) * Pc - (1 / 2) * (M1 / V ^ 2) * (S ^ 2 - S))
        + C * a * (μ + S / V) * nq - μ * Q) := by
      field_simp
      ring
    rw [hscale] at h
    have hV2 : (0:ℝ) < V ^ 2 := by positivity
    exact (mul_nonneg_iff_of_pos_left hV2).mp h
  rw [hb_G1, hb_C]
  have h1 : 0 ≤ a * V * ((α / 4) * (S + 1 - μ * V) ^ 2 + α * (μ * V) + (α / 2) * Var
      + C * (S + μ * V) * nq
      - (8 * K0 * (S + 1 + μ * V) * nq + (α / 4) * Mb + 8 * Real.sqrt (K0 * α * nq * Mb)
        + 4 * Real.sqrt (K0 * α * nq * S) + (μ * V) * K0 * nq)) := mul_nonneg (by positivity) hD
  ring_nf at hb_Qm hb_Mt hb_Cosc hb_P hb_pcb hb_Q h1 ⊢
  linarith [hb_Qm, hb_Mt, hb_Cosc, hb_P, hb_pcb, hb_Q, h1]

end Work.BoseFixB1S
