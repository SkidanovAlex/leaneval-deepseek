import Mathlib
import Submission.Work.MotK.TGen.ZElim2Defs
import Submission.Work.MotK.TGen.ZElim2AuxB1.fin1_shape_le_one
import Submission.Work.MotK.TGen.ZElim2AuxB2.fin1_shape_le_two
import Submission.Work.MotK.TGen.ZElim2AuxC.finSucc_g0p
import Submission.Work.MotK.TGen.ZElim2AuxE.totalDegree_g0p
import Submission.Work.MotK.TGen.ZElim2AuxF.eq_C23_of_mul
import Submission.Work.MotK.TGen.ZElim2AuxG.line_factor
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace Work.MotK.TGen

open MvPolynomial

namespace ZElim2StructAux


-- ===== my helpers =====

theorem finSuccEquiv_C' {L : Type} [Field L] (r : L) :
    MvPolynomial.finSuccEquiv L 1 (MvPolynomial.C r) = Polynomial.C (MvPolynomial.C r) := by
  rw [← MvPolynomial.algebraMap_eq L (Fin 2), AlgEquiv.commutes, Polynomial.algebraMap_apply]
  rfl

noncomputable def q1R {L : Type} [CommSemiring L] (u1 u0 : L) : MvPolynomial (Fin 1) L :=
  MvPolynomial.C u1 * MvPolynomial.X 0 + MvPolynomial.C u0

noncomputable def q0R {L : Type} [CommSemiring L] (v2 v1 v0 : L) : MvPolynomial (Fin 1) L :=
  MvPolynomial.C v2 * (MvPolynomial.X 0)^2 + MvPolynomial.C v1 * MvPolynomial.X 0 + MvPolynomial.C v0

theorem finSucc_q1p {L : Type} [Field L] (u1 u0 : L) :
    MvPolynomial.finSuccEquiv L 1 (q1p u1 u0) = Polynomial.C (q1R u1 u0) := by
  rw [q1p, q1R]
  simp only [map_add, map_mul, finSuccEquiv_C']
  rw [show (1 : Fin 2) = Fin.succ (0 : Fin 1) from rfl, MvPolynomial.finSuccEquiv_X_succ]

theorem finSucc_q0p {L : Type} [Field L] (v2 v1 v0 : L) :
    MvPolynomial.finSuccEquiv L 1 (q0p v2 v1 v0) = Polynomial.C (q0R v2 v1 v0) := by
  rw [q0p, q0R]
  simp only [map_add, map_mul, map_pow, finSuccEquiv_C']
  rw [show (1 : Fin 2) = Fin.succ (0 : Fin 1) from rfl, MvPolynomial.finSuccEquiv_X_succ]

theorem F2_quad {L : Type} [Field L] (c u1 u0 v2 v1 v0 : L) :
    MvPolynomial.finSuccEquiv L 1
        (MvPolynomial.C c * (MvPolynomial.X 0)^2 + q1p u1 u0 * MvPolynomial.X 0
          + q0p v2 v1 v0)
      = Polynomial.C (MvPolynomial.C c) * Polynomial.X^2 + Polynomial.C (q1R u1 u0) * Polynomial.X^1
        + Polynomial.C (q0R v2 v1 v0) := by
  rw [map_add, map_add, map_mul, map_mul, map_pow, finSuccEquiv_C',
      MvPolynomial.finSuccEquiv_X_zero, finSucc_q1p, finSucc_q0p]
  first | refl_ring1 | ring

theorem q1p_scale {L : Type} [Field L] (c u1 u0 : L) (hc : c ≠ 0) :
    q1p (u1 * c⁻¹) (u0 * c⁻¹) * MvPolynomial.C c = q1p u1 u0 := by
  have h1 : (MvPolynomial.C (u1 * c⁻¹) : MvPolynomial (Fin 2) L) * MvPolynomial.C c
      = MvPolynomial.C u1 := by
    rw [← map_mul]; congr 1; rw [mul_assoc, inv_mul_cancel₀ hc, mul_one]
  have h2 : (MvPolynomial.C (u0 * c⁻¹) : MvPolynomial (Fin 2) L) * MvPolynomial.C c
      = MvPolynomial.C u0 := by
    rw [← map_mul]; congr 1; rw [mul_assoc, inv_mul_cancel₀ hc, mul_one]
  rw [q1p, q1p, ← h1, ← h2]
  first | refl_ring1 | ring

theorem q0p_scale {L : Type} [Field L] (c v2 v1 v0 : L) (hc : c ≠ 0) :
    q0p (v2 * c⁻¹) (v1 * c⁻¹) (v0 * c⁻¹) * MvPolynomial.C c = q0p v2 v1 v0 := by
  have h2 : (MvPolynomial.C (v2 * c⁻¹) : MvPolynomial (Fin 2) L) * MvPolynomial.C c
      = MvPolynomial.C v2 := by
    rw [← map_mul]; congr 1; rw [mul_assoc, inv_mul_cancel₀ hc, mul_one]
  have h1 : (MvPolynomial.C (v1 * c⁻¹) : MvPolynomial (Fin 2) L) * MvPolynomial.C c
      = MvPolynomial.C v1 := by
    rw [← map_mul]; congr 1; rw [mul_assoc, inv_mul_cancel₀ hc, mul_one]
  have h0 : (MvPolynomial.C (v0 * c⁻¹) : MvPolynomial (Fin 2) L) * MvPolynomial.C c
      = MvPolynomial.C v0 := by
    rw [← map_mul]; congr 1; rw [mul_assoc, inv_mul_cancel₀ hc, mul_one]
  rw [q0p, q0p, ← h2, ← h1, ← h0]
  first | refl_ring1 | ring

theorem Q23_scale {L : Type} [Field L] (c u1 u0 v2 v1 v0 : L) (hc : c ≠ 0) :
    Q23 (u1 * c⁻¹) (u0 * c⁻¹) (v2 * c⁻¹) (v1 * c⁻¹) (v0 * c⁻¹) * MvPolynomial.C c
      = MvPolynomial.C c * (MvPolynomial.X 0)^2 + q1p u1 u0 * MvPolynomial.X 0 + q0p v2 v1 v0 := by
  have hq1 := q1p_scale c u1 u0 hc
  have hq0 := q0p_scale c v2 v1 v0 hc
  rw [Q23, ← hq1, ← hq0]
  first | refl_ring1 | ring

theorem eq_coeff_shape {M : Type} [Semiring M] (P : Polynomial M) (h : P.natDegree ≤ 2) :
    P = Polynomial.C (P.coeff 2) * Polynomial.X^2 + Polynomial.C (P.coeff 1) * Polynomial.X^1
      + Polynomial.C (P.coeff 0) := by
  ext n
  rw [Polynomial.coeff_add, Polynomial.coeff_add, Polynomial.coeff_C_mul_X_pow,
    Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_C]
  rcases lt_or_ge n 3 with hn | hn
  · interval_cases n <;> simp
  · have h0 : P.coeff n = 0 := Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
    have h1 : ¬ (n = 2) := by omega
    have h2 : ¬ (n = 1) := by omega
    have h3 : ¬ (n = 0) := by omega
    simp [h0, h1, h2, h3]

theorem eq_coeff_shape1 {M : Type} [Semiring M] (P : Polynomial M) (h : P.natDegree ≤ 1) :
    P = Polynomial.C (P.coeff 1) * Polynomial.X^1 + Polynomial.C (P.coeff 0) := by
  have h2 := eq_coeff_shape P (by omega : P.natDegree ≤ 2)
  have hc2 : P.coeff 2 = 0 := Polynomial.coeff_eq_zero_of_natDegree_lt (by omega : P.natDegree < 2)
  conv_lhs => rw [h2]
  rw [hc2]
  simp

theorem one_le_totalDegree_of_not_isUnit {L : Type} [Field L] {p : MvPolynomial (Fin 2) L}
    (hp : p ≠ 0) (h : ¬ IsUnit p) : 1 ≤ p.totalDegree := by
  by_contra hc
  have h0 : p.totalDegree = 0 := by omega
  have hpC : p = MvPolynomial.C (p.coeff 0) := (MvPolynomial.totalDegree_eq_zero_iff_eq_C).mp h0
  have hc0 : p.coeff 0 ≠ 0 := by
    intro hz; exact hp (by rw [hpC, hz, map_zero])
  exact h (hpC ▸ IsUnit.map MvPolynomial.C (isUnit_iff_ne_zero.mpr hc0))

theorem coeff5_finSucc_g0p {L : Type} [Field L] (r : L) :
    (MvPolynomial.finSuccEquiv L 1 (g0p r)).coeff 5 = MvPolynomial.C (r^7) := by
  rw [Work.MotK.TGen.ZElim2AuxC.finSucc_g0p]
  rw [Polynomial.coeff_add, Polynomial.coeff_add, Polynomial.coeff_add,
    Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_C_mul_X_pow,
    Polynomial.coeff_C]
  norm_num

theorem degreeOf_g0p {L : Type} [Field L] (r : L) (hr : r ≠ 0) : (g0p r).degreeOf 0 = 5 := by
  have htot := Work.MotK.TGen.ZElim2AuxE.totalDegree_g0p r hr
  apply le_antisymm
  · calc (g0p r).degreeOf 0 ≤ (g0p r).totalDegree := MvPolynomial.degreeOf_le_totalDegree _ _
      _ = 5 := htot
  · have hcoe := coeff5_finSucc_g0p (L := L) r
    have h1 : ((MvPolynomial.finSuccEquiv L 1 (g0p r)).coeff 5).coeff (0 : Fin 1 →₀ ℕ)
        = (g0p r).coeff (Finsupp.cons 5 (0 : Fin 1 →₀ ℕ)) :=
      MvPolynomial.finSuccEquiv_coeff_coeff (R := L) (n := 1) (0 : Fin 1 →₀ ℕ) (g0p r) 5
    have h2 : Finsupp.cons 5 (0 : Fin 1 →₀ ℕ) = Finsupp.single (0 : Fin 2) 5 := by
      ext j
      refine Fin.cases ?_ ?_ j
      · simp [Finsupp.cons_zero]
      · intro i
        rw [Finsupp.cons_succ]
        simp
    have hc : (g0p r).coeff (Finsupp.single (0 : Fin 2) 5) = r^7 := by
      rw [← h2, ← h1, hcoe, MvPolynomial.coeff_C]
      simp
    have hmem : Finsupp.single (0 : Fin 2) 5 ∈ (g0p r).support := by
      rw [MvPolynomial.mem_support_iff, hc]
      exact pow_ne_zero 7 hr
    have := (MvPolynomial.degreeOf_le_iff.mp (le_refl ((g0p r).degreeOf 0)))
      (Finsupp.single (0 : Fin 2) 5) hmem
    simpa using this

theorem ZElim2StructKey {L : Type} [Field L] (r : L) (hr : r ≠ 0)
    (a b : MvPolynomial (Fin 2) L) (hab : g0p r = a * b) (ha : ¬ IsUnit a) (hb : ¬ IsUnit b)
    (hle : a.degreeOf 0 ≤ b.degreeOf 0) :
    (∃ u1 u0 v2 v1 v0 : L, Q23 u1 u0 v2 v1 v0 * C23 r u1 u0 v2 v1 v0 = g0p r)
    ∨ (∃ η τ : L, η ^ 5 = 1 ∧ ∃ q : MvPolynomial (Fin 2) L,
        (MvPolynomial.C r * MvPolynomial.X 0 - MvPolynomial.C η * MvPolynomial.X 1
            + MvPolynomial.C τ) * q = g0p r) := by
  have hG_ne : g0p r ≠ 0 := by
    intro h
    have h5 := Work.MotK.TGen.ZElim2AuxE.totalDegree_g0p r hr
    rw [h] at h5
    simp at h5
  have ha0 : a ≠ 0 := fun h => hG_ne (by rw [hab, h, zero_mul])
  have hb0 : b ≠ 0 := fun h => hG_ne (by rw [hab, h, mul_zero])
  have htot : a.totalDegree + b.totalDegree = 5 := by
    have h := MvPolynomial.totalDegree_mul_of_isDomain ha0 hb0
    rw [← hab, Work.MotK.TGen.ZElim2AuxE.totalDegree_g0p r hr] at h
    exact h.symm
  have hdeg : a.degreeOf 0 + b.degreeOf 0 = 5 := by
    have h := MvPolynomial.degreeOf_mul_eq (n := (0 : Fin 2)) ha0 hb0
    rw [← hab, degreeOf_g0p r hr] at h
    exact h.symm
  have hta : 1 ≤ a.totalDegree := one_le_totalDegree_of_not_isUnit ha0 ha
  have hda : a.degreeOf 0 ≠ 0 := by
    intro h0
    have hdb : b.degreeOf 0 = 5 := by omega
    have h5 : 5 ≤ b.totalDegree := by
      calc (5 : ℕ) = b.degreeOf 0 := hdb.symm
        _ ≤ b.totalDegree := MvPolynomial.degreeOf_le_totalDegree b 0
    omega
  have hta' : a.totalDegree = a.degreeOf 0 := by
    have h1 := MvPolynomial.degreeOf_le_totalDegree a 0
    have h2 := MvPolynomial.degreeOf_le_totalDegree b 0
    omega
  have hcase : a.degreeOf 0 = 1 ∨ a.degreeOf 0 = 2 := by omega
  rcases hcase with hd1 | hd2
  · -- ============ line case ============
    set P := MvPolynomial.finSuccEquiv L 1 a with hP
    have hPnat : P.natDegree = 1 := by rw [hP, MvPolynomial.natDegree_finSuccEquiv, hd1]
    have hPne : P ≠ 0 := by
      intro h
      rw [h] at hPnat
      rw [Polynomial.natDegree_zero] at hPnat
      omega
    have hPshape : P = Polynomial.C (P.coeff 1) * Polynomial.X^1 + Polynomial.C (P.coeff 0) :=
      eq_coeff_shape1 P (by rw [hPnat])
    have hc1ne : P.coeff 1 ≠ 0 := by
      intro hz
      have hle1 : P.natDegree ≤ 0 := by
        rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
        intro N hN
        rcases Nat.lt_or_ge 1 N with h | h
        · exact Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [hPnat]; omega)
        · have hN1 : N = 1 := by omega
          rw [hN1]; exact hz
      omega
    have hc1td : (P.coeff 1).totalDegree ≤ 0 := by
      have h := MvPolynomial.totalDegree_coeff_finSuccEquiv_add_le a 1 (by rwa [hP] at hc1ne)
      rw [← hP] at h
      rw [hta', hd1] at h
      omega
    have hc0td : (P.coeff 0).totalDegree ≤ 1 := by
      by_cases hz : P.coeff 0 = 0
      · rw [hz]; simp
      · have h := MvPolynomial.totalDegree_coeff_finSuccEquiv_add_le a 0 (by rwa [hP] at hz)
        rw [← hP] at h
        rw [hta', hd1] at h
        omega
    obtain ⟨c, hc1⟩ : ∃ c : L, P.coeff 1 = MvPolynomial.C c :=
      ⟨_, (MvPolynomial.totalDegree_eq_zero_iff_eq_C).mp (by omega)⟩
    have hcne : c ≠ 0 := by
      intro h; exact hc1ne (by rw [hc1, h, map_zero])
    obtain ⟨d, e, hc0⟩ :
        ∃ d e : L, P.coeff 0 = MvPolynomial.C d * MvPolynomial.X 0 + MvPolynomial.C e :=
      Work.MotK.TGen.ZElim2AuxB1.fin1_shape_le_one (P.coeff 0) hc0td
    have hFa : MvPolynomial.finSuccEquiv L 1 a
        = Polynomial.C (MvPolynomial.C c) * Polynomial.X^1
          + Polynomial.C (MvPolynomial.C d * MvPolynomial.X 0 + MvPolynomial.C e) := by
      rw [← hP, hPshape, hc1, hc0]
    have hline : MvPolynomial.finSuccEquiv L 1
        (MvPolynomial.C c * MvPolynomial.X 0 + MvPolynomial.C d * MvPolynomial.X 1
          + MvPolynomial.C e)
        = Polynomial.C (MvPolynomial.C c) * Polynomial.X^1
          + Polynomial.C (MvPolynomial.C d * MvPolynomial.X 0 + MvPolynomial.C e) := by
      simp only [map_add, map_mul, map_pow, finSuccEquiv_C', MvPolynomial.finSuccEquiv_X_zero]
      rw [show (1 : Fin 2) = Fin.succ (0 : Fin 1) from rfl, MvPolynomial.finSuccEquiv_X_succ]
      first | refl_ring1 | ring
    have ha_line : a = MvPolynomial.C c * MvPolynomial.X 0 + MvPolynomial.C d * MvPolynomial.X 1
        + MvPolynomial.C e := by
      apply (MvPolynomial.finSuccEquiv L 1).injective
      rw [hFa, hline]
    have hfd := Work.MotK.TGen.ZElim2AuxG.line_factor r c d e hr hcne b (by rw [← ha_line, ← hab])
    refine Or.inr ⟨-((r * c⁻¹) * d), (r * c⁻¹) * e, ?_, MvPolynomial.C (c * r⁻¹) * b, ?_⟩
    · have hx : ((r * d) * c⁻¹)^5 = (r * d)^5 * (c^5)⁻¹ := by
        rw [mul_pow, inv_pow]
      have hη : (-((r * c⁻¹) * d))^5 = 1 := by
        rw [show (r * c⁻¹) * d = (r * d) * c⁻¹ by ring,
          show (-((r * d) * c⁻¹))^5 = -(((r * d) * c⁻¹)^5) by ring, hx, hfd]
        rw [neg_mul, neg_neg, mul_inv_cancel₀ (pow_ne_zero 5 hcne)]
      exact hη
    · have hrsc : r * c⁻¹ * c = r := by field_simp
      have hneg : (-MvPolynomial.C (-((r * c⁻¹) * d)) : MvPolynomial (Fin 2) L)
          = MvPolynomial.C ((r * c⁻¹) * d) := by
        rw [MvPolynomial.C_neg, neg_neg]
      have hls : (MvPolynomial.C (r * c⁻¹) * (MvPolynomial.C c * MvPolynomial.X 0
            + MvPolynomial.C d * MvPolynomial.X 1 + MvPolynomial.C e) : MvPolynomial (Fin 2) L)
          = MvPolynomial.C ((r * c⁻¹) * c) * MvPolynomial.X 0
            + MvPolynomial.C ((r * c⁻¹) * d) * MvPolynomial.X 1
            + MvPolynomial.C ((r * c⁻¹) * e) := by
        rw [mul_add, mul_add, ← mul_assoc, ← mul_assoc, ← map_mul, ← map_mul, ← map_mul]
      have hadd : (MvPolynomial.C r * MvPolynomial.X 0
            + MvPolynomial.C ((r * c⁻¹) * d) * MvPolynomial.X 1
            + MvPolynomial.C ((r * c⁻¹) * e) : MvPolynomial (Fin 2) L)
          = MvPolynomial.C (r * c⁻¹) * (MvPolynomial.C c * MvPolynomial.X 0
            + MvPolynomial.C d * MvPolynomial.X 1 + MvPolynomial.C e) := by
        rw [hls, hrsc]
      have hsubst : (MvPolynomial.C r * MvPolynomial.X 0
            - MvPolynomial.C (-((r * c⁻¹) * d)) * MvPolynomial.X 1
            + MvPolynomial.C ((r * c⁻¹) * e) : MvPolynomial (Fin 2) L)
          = MvPolynomial.C r * MvPolynomial.X 0
            + MvPolynomial.C ((r * c⁻¹) * d) * MvPolynomial.X 1
            + MvPolynomial.C ((r * c⁻¹) * e) := by
        rw [sub_eq_add_neg, ← neg_mul]
        conv_lhs => rw [hneg]
      have hsr : (r * c⁻¹) * (c * r⁻¹) = 1 := by field_simp
      have hCt : (MvPolynomial.C (r * c⁻¹) : MvPolynomial (Fin 2) L) * MvPolynomial.C (c * r⁻¹) = 1 := by
        rw [← map_mul, hsr, map_one]
      calc (MvPolynomial.C r * MvPolynomial.X 0 - MvPolynomial.C (-((r * c⁻¹) * d)) * MvPolynomial.X 1
              + MvPolynomial.C ((r * c⁻¹) * e)) * (MvPolynomial.C (c * r⁻¹) * b)
          = (MvPolynomial.C r * MvPolynomial.X 0 + MvPolynomial.C ((r * c⁻¹) * d) * MvPolynomial.X 1
              + MvPolynomial.C ((r * c⁻¹) * e)) * (MvPolynomial.C (c * r⁻¹) * b) :=
            congrArg (fun z : MvPolynomial (Fin 2) L => z * (MvPolynomial.C (c * r⁻¹) * b)) hsubst
        _ = (MvPolynomial.C (r * c⁻¹) * (MvPolynomial.C c * MvPolynomial.X 0
              + MvPolynomial.C d * MvPolynomial.X 1 + MvPolynomial.C e))
              * (MvPolynomial.C (c * r⁻¹) * b) :=
            congrArg (fun z : MvPolynomial (Fin 2) L => z * (MvPolynomial.C (c * r⁻¹) * b)) hadd
        _ = (MvPolynomial.C (r * c⁻¹) * MvPolynomial.C (c * r⁻¹))
              * ((MvPolynomial.C c * MvPolynomial.X 0 + MvPolynomial.C d * MvPolynomial.X 1
                  + MvPolynomial.C e) * b) := by ring
        _ = 1 * ((MvPolynomial.C c * MvPolynomial.X 0 + MvPolynomial.C d * MvPolynomial.X 1
                  + MvPolynomial.C e) * b) :=
            congrArg (fun z : MvPolynomial (Fin 2) L => z * ((MvPolynomial.C c * MvPolynomial.X 0 + MvPolynomial.C d * MvPolynomial.X 1
                  + MvPolynomial.C e) * b)) hCt
        _ = (MvPolynomial.C c * MvPolynomial.X 0 + MvPolynomial.C d * MvPolynomial.X 1
                  + MvPolynomial.C e) * b := by rw [one_mul]
        _ = a * b := congrArg (fun z : MvPolynomial (Fin 2) L => z * b) ha_line.symm
        _ = g0p r := hab.symm
  · -- ============ quadratic case ============
    set P := MvPolynomial.finSuccEquiv L 1 a with hP
    have hPnat : P.natDegree = 2 := by rw [hP, MvPolynomial.natDegree_finSuccEquiv, hd2]
    have hPne : P ≠ 0 := by
      intro h
      rw [h] at hPnat
      rw [Polynomial.natDegree_zero] at hPnat
      omega
    have hPshape : P = Polynomial.C (P.coeff 2) * Polynomial.X^2 + Polynomial.C (P.coeff 1) * Polynomial.X^1
        + Polynomial.C (P.coeff 0) := eq_coeff_shape P (by rw [hPnat])
    have hc2ne : P.coeff 2 ≠ 0 := by
      intro hz
      have hle1 : P.natDegree ≤ 1 := by
        rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
        intro N hN
        rcases Nat.lt_or_ge 3 N with h | h
        · exact Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [hPnat]; omega)
        · interval_cases N
          · exact hz
          · exact Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [hPnat]; omega)
      omega
    have hGam_td : (P.coeff 2).totalDegree ≤ 0 := by
      have h := MvPolynomial.totalDegree_coeff_finSuccEquiv_add_le a 2 (by rwa [hP] at hc2ne)
      rw [← hP] at h
      rw [hta', hd2] at h
      omega
    have hA_td : (P.coeff 1).totalDegree ≤ 1 := by
      by_cases hz : P.coeff 1 = 0
      · rw [hz]; simp
      · have h := MvPolynomial.totalDegree_coeff_finSuccEquiv_add_le a 1 (by rwa [hP] at hz)
        rw [← hP] at h
        rw [hta', hd2] at h
        omega
    have hE_td : (P.coeff 0).totalDegree ≤ 2 := by
      by_cases hz : P.coeff 0 = 0
      · rw [hz]; simp
      · have h := MvPolynomial.totalDegree_coeff_finSuccEquiv_add_le a 0 (by rwa [hP] at hz)
        rw [← hP] at h
        rw [hta', hd2] at h
        omega
    obtain ⟨c₀, hc₀⟩ : ∃ c₀ : L, P.coeff 2 = MvPolynomial.C c₀ :=
      ⟨_, (MvPolynomial.totalDegree_eq_zero_iff_eq_C).mp (by omega)⟩
    have hc₀ne : c₀ ≠ 0 := by
      intro h; exact hc2ne (by rw [hc₀, h, map_zero])
    obtain ⟨u1, u0, hu⟩ := Work.MotK.TGen.ZElim2AuxB1.fin1_shape_le_one (P.coeff 1) hA_td
    obtain ⟨v2, v1, v0, hv⟩ := Work.MotK.TGen.ZElim2AuxB2.fin1_shape_le_two (P.coeff 0) hE_td
    have hPexpl : P = Polynomial.C (MvPolynomial.C c₀) * Polynomial.X^2
        + Polynomial.C (q1R u1 u0) * Polynomial.X^1 + Polynomial.C (q0R v2 v1 v0) := by
      conv_lhs => rw [hPshape]
      rw [hc₀, hu, hv, q1R, q0R]
    have ha_quad : a = MvPolynomial.C c₀ * (MvPolynomial.X 0)^2 + q1p u1 u0 * MvPolynomial.X 0
        + q0p v2 v1 v0 := by
      apply (MvPolynomial.finSuccEquiv L 1).injective
      rw [F2_quad, ← hP, hPexpl]
    have hMQ : Q23 (u1 * c₀⁻¹) (u0 * c₀⁻¹) (v2 * c₀⁻¹) (v1 * c₀⁻¹) (v0 * c₀⁻¹)
        * MvPolynomial.C c₀ = a := by
      rw [Q23_scale c₀ u1 u0 v2 v1 v0 hc₀ne, ← ha_quad]
    refine Or.inl ⟨u1 * c₀⁻¹, u0 * c₀⁻¹, v2 * c₀⁻¹, v1 * c₀⁻¹, v0 * c₀⁻¹, ?_⟩
    have hS : Q23 (u1 * c₀⁻¹) (u0 * c₀⁻¹) (v2 * c₀⁻¹) (v1 * c₀⁻¹) (v0 * c₀⁻¹)
        * (MvPolynomial.C c₀ * b) = g0p r := by
      rw [← mul_assoc, hMQ, ← hab]
    have hC23 := Work.MotK.TGen.ZElim2AuxF.eq_C23_of_mul r (u1 * c₀⁻¹) (u0 * c₀⁻¹) (v2 * c₀⁻¹) (v1 * c₀⁻¹) (v0 * c₀⁻¹) hr
      (MvPolynomial.C c₀ * b) hS
    rw [← hC23]
    exact hS

end ZElim2StructAux

open ZElim2StructAux

theorem ZElim2Struct (L : Type) [Field L] (h5 : (5 : L) ≠ 0) (r : L) (hr : r ≠ 0)
    (hred : ¬ Irreducible (Work.MotK.TGen.g0p r)) :
    (∃ u1 u0 v2 v1 v0 : L, Work.MotK.TGen.Q23 u1 u0 v2 v1 v0
        * Work.MotK.TGen.C23 r u1 u0 v2 v1 v0 = Work.MotK.TGen.g0p r)
    ∨ (∃ η τ : L, η ^ 5 = 1 ∧ ∃ q : MvPolynomial (Fin 2) L,
        (MvPolynomial.C r * MvPolynomial.X 0 - MvPolynomial.C η * MvPolynomial.X 1
            + MvPolynomial.C τ) * q = Work.MotK.TGen.g0p r) := by
  have hG_ne : g0p r ≠ 0 := by
    intro h
    have h5' := Work.MotK.TGen.ZElim2AuxE.totalDegree_g0p r hr
    rw [h] at h5'
    simp at h5'
  have hG_unit : ¬ IsUnit (g0p r) := by
    intro hu
    have hdvd : g0p r ∣ 1 := isUnit_iff_dvd_one.mp hu
    have h2 := MvPolynomial.totalDegree_le_of_dvd_of_isDomain hdvd
      (one_ne_zero (α := MvPolynomial (Fin 2) L))
    rw [Work.MotK.TGen.ZElim2AuxE.totalDegree_g0p r hr] at h2
    simp at h2
  rw [irreducible_iff] at hred
  push_neg at hred
  have hred' : ∃ a b, g0p r = a * b ∧ ¬IsUnit a ∧ ¬IsUnit b := hred hG_unit
  obtain ⟨a, b, hab, ha, hb⟩ := hred'
  rcases le_total (a.degreeOf 0) (b.degreeOf 0) with hle | hle
  · exact ZElim2StructKey r hr a b hab ha hb hle
  · exact ZElim2StructKey r hr b a (by rw [hab, mul_comm]) hb ha hle

end Work.MotK.TGen
