import Mathlib
import Submission.Work.L2F.Props.OddSubDefs
import Submission.Work.L2F.Props.oddsub.eq_or_trace_sub_of_commute
import Submission.Work.L2F.Involution.mem_normalizer_zpowers
import Submission.Work.L2F.Torus.conj_eq_inv_of_mem_cent

namespace Work.L2F.Props.oddsub

open scoped MatrixGroups
open Matrix

/-- In `SL(2,F)` the centre is `{1, -1}`, in every characteristic. -/
theorem eq_one_or_negOne_of_mem_center (F : Type*) [Field F]
    (x : Matrix.SpecialLinearGroup (Fin 2) F)
    (hx : x ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F)) :
    x = 1 ∨ x = Work.L2F.negOne F := by
  rw [Matrix.SpecialLinearGroup.mem_center_iff] at hx
  obtain ⟨r, hr, hrm⟩ := hx
  have hr2 : r ^ 2 = 1 := by
    have := hr
    rwa [Fintype.card_fin] at this
  have hfac : (r - 1) * (r + 1) = 0 := by
    have h : (r - 1) * (r + 1) = r ^ 2 - 1 := by ring
    rw [h, hr2]; ring
  rcases mul_eq_zero.mp hfac with h | h
  · left
    have hr1 : r = 1 := sub_eq_zero.mp h
    apply Subtype.ext
    rw [← hrm, hr1]
    simp
  · right
    have hr1 : r = -1 := add_eq_zero_iff_eq_neg.mp h
    apply Subtype.ext
    rw [← hrm, hr1, Matrix.scalar_apply]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Work.L2F.negOne, Matrix.diagonal_neg]

theorem conj_eq_self_of_mem_zpowers (F : Type*) [Field F]
    (K : Subgroup (Matrix.ProjGenLinGroup (Fin 2) F)) (hodd : Odd (Nat.card K))
    (hK : K ≤ Matrix.SpecialLinearGroup.toPGL.range)
    (x y : Matrix.ProjGenLinGroup (Fin 2) F) (hxK : x ∈ K) (hyK : y ∈ K) (hx1 : x ≠ 1)
    (hsemi : ∃ g : Matrix.SpecialLinearGroup (Fin 2) F,
        Matrix.SpecialLinearGroup.toPGL g = x ∧
          Work.L2F.Props.SemisimpleSL (g : Matrix (Fin 2) (Fin 2) F))
    (hyx : y * x * y⁻¹ ∈ Subgroup.zpowers x) :
    y * x * y⁻¹ = x := by
  classical
  obtain ⟨g, hgx, hgsemi⟩ := hsemi
  obtain ⟨s, hs⟩ := MonoidHom.mem_range.mp (hK hyK)
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hyx
  set u : Matrix.SpecialLinearGroup (Fin 2) F := s * g * s⁻¹ with hu
  have hu_pgl : Matrix.SpecialLinearGroup.toPGL u = x ^ n := by
    rw [hu, map_mul, map_mul, map_inv, hs, hgx, ← hn]
  -- `u * (g^n)⁻¹` lies in the kernel of `toPGL`, hence is `1` or `-1`
  have hcenter : u * (g ^ n)⁻¹ ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F) := by
    rw [← Matrix.SpecialLinearGroup.toPGL_ker, MonoidHom.mem_ker]
    rw [map_mul, map_inv, map_zpow, hu_pgl, hgx]
    simp
  have hcs : u = g ^ n ∨ u = Work.L2F.negOne F * g ^ n := by
    rcases eq_one_or_negOne_of_mem_center F (u * (g ^ n)⁻¹) hcenter with h | h
    · left
      have := congrArg (fun w => w * g ^ n) h
      simpa using this
    · right
      have := congrArg (fun w => w * g ^ n) h
      simpa using this
  -- `u` commutes with `g`
  have hgn_comm : g ^ n * g = g * g ^ n := (Commute.refl g).zpow_left n
  have hu_comm : u * g = g * u := by
    rcases hcs with h | h
    · rw [h, hgn_comm]
    · rw [h]
      calc Work.L2F.negOne F * g ^ n * g
          = Work.L2F.negOne F * (g ^ n * g) := by rw [mul_assoc]
        _ = Work.L2F.negOne F * (g * g ^ n) := by rw [hgn_comm]
        _ = (Work.L2F.negOne F * g) * g ^ n := by rw [mul_assoc]
        _ = (g * Work.L2F.negOne F) * g ^ n := by rw [Work.L2F.Involution.negOne_mul_comm]
        _ = g * (Work.L2F.negOne F * g ^ n) := by rw [mul_assoc]
  have hmat_comm : (u : Matrix (Fin 2) (Fin 2) F) * (g : Matrix (Fin 2) (Fin 2) F)
      = (g : Matrix (Fin 2) (Fin 2) F) * (u : Matrix (Fin 2) (Fin 2) F) := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, ← Matrix.SpecialLinearGroup.coe_mul, hu_comm]
  have htr : (u : Matrix (Fin 2) (Fin 2) F).trace = (g : Matrix (Fin 2) (Fin 2) F).trace := by
    have hcoe : (u : Matrix (Fin 2) (Fin 2) F)
        = (s : Matrix (Fin 2) (Fin 2) F) * (g : Matrix (Fin 2) (Fin 2) F)
          * ((s⁻¹ : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) := by
      rw [hu, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
    have hmul : ((s⁻¹ : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)
        * (s : Matrix (Fin 2) (Fin 2) F) = 1 := by
      rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel]
      exact Matrix.SpecialLinearGroup.coe_one
    rw [hcoe, mul_assoc, Matrix.trace_mul_comm, mul_assoc, hmul, mul_one]
  have hdet : (u : Matrix (Fin 2) (Fin 2) F).det = (g : Matrix (Fin 2) (Fin 2) F).det := by
    rw [Matrix.SpecialLinearGroup.det_coe, Matrix.SpecialLinearGroup.det_coe]
  obtain hEq | hEq :=
    Work.L2F.Props.oddsub.eq_or_trace_sub_of_commute F (g : Matrix (Fin 2) (Fin 2) F)
      (u : Matrix (Fin 2) (Fin 2) F) (Matrix.SpecialLinearGroup.det_coe g) hgsemi hmat_comm htr
      hdet
  · -- first case: `u = g`, hence `y * x * y⁻¹ = x`
    have hu_eq : u = g := Subtype.ext hEq
    rw [← hn, ← hu_pgl, hu_eq, hgx]
  · -- second case: `u = g⁻¹`, so `y * x * y⁻¹ = x⁻¹`, contradicting odd order
    exfalso
    have hginv : ((g⁻¹ : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)
        = (g : Matrix (Fin 2) (Fin 2) F).trace • (1 : Matrix (Fin 2) (Fin 2) F)
          - (g : Matrix (Fin 2) (Fin 2) F) := by
      rw [Work.L2F.Torus.coe_inv_sl F]
      refine Matrix.inv_eq_right_inv ?_
      have hCH := Work.L2F.Mat2.sq_eq_trace_smul_sub_det F (g : Matrix (Fin 2) (Fin 2) F)
      rw [Matrix.SpecialLinearGroup.det_coe g] at hCH
      rw [Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_one, hCH]
      module
    have hu_eq : u = g⁻¹ := by
      apply Subtype.ext
      rw [hEq, hginv]
    have hhyx : y * x * y⁻¹ = x⁻¹ := by
      rw [← hn, ← hu_pgl, hu_eq, map_inv, hgx]
    -- the orders of `x` and `y` are odd
    have hx_ord_odd : Odd (orderOf x) :=
      Odd.of_dvd_nat hodd (Subgroup.orderOf_dvd_natCard K hxK)
    have hy_ord_odd : Odd (orderOf y) :=
      Odd.of_dvd_nat hodd (Subgroup.orderOf_dvd_natCard K hyK)
    -- `y * x = x⁻¹ * y` and `y * x⁻¹ = x * y`
    have hyx1 : y * x = x⁻¹ * y := by rw [← hhyx]; group
    have hyx2 : y * x⁻¹ = x * y := by
      have h : y * x⁻¹ * y⁻¹ = x := by
        rw [show y * x⁻¹ * y⁻¹ = (y * x * y⁻¹)⁻¹ from by group, hhyx]
        simp
      have h2 := congrArg (fun w => w * y) h
      simpa using h2
    have hcomm2eq : y ^ 2 * x = x * y ^ 2 := by
      rw [pow_two]
      calc y * y * x = y * (y * x) := by group
        _ = y * (x⁻¹ * y) := by rw [hyx1]
        _ = (y * x⁻¹) * y := by group
        _ = (x * y) * y := by rw [hyx2]
        _ = x * (y * y) := by group
    have hcomm2 : Commute (y ^ 2) x := hcomm2eq
    obtain ⟨m, hm⟩ := hy_ord_odd
    have hk : y ^ (orderOf y - 1) = (y ^ 2) ^ m := by
      have h' : orderOf y - 1 = 2 * m := by omega
      rw [h', pow_mul]
    have hRHS : y ^ orderOf y * x * (y ^ orderOf y)⁻¹ = x⁻¹ := by
      have hsplit : y ^ orderOf y = y ^ (orderOf y - 1) * y := by
        conv_lhs => rw [show orderOf y = orderOf y - 1 + 1 from
          (Nat.succ_pred_eq_of_pos (by omega : 0 < orderOf y)).symm]
        rw [pow_succ]
      calc y ^ orderOf y * x * (y ^ orderOf y)⁻¹
          = y ^ (orderOf y - 1) * (y * x * y⁻¹) * (y ^ (orderOf y - 1))⁻¹ := by
            rw [hsplit]; group
        _ = y ^ (orderOf y - 1) * x⁻¹ * (y ^ (orderOf y - 1))⁻¹ := by rw [hhyx]
        _ = x⁻¹ := by
            rw [hk, ((hcomm2.pow_left m).inv_right)]
            group
    have hLHS : y ^ orderOf y * x * (y ^ orderOf y)⁻¹ = x := by
      rw [pow_orderOf_eq_one]; group
    have hxx : x = x⁻¹ := hLHS.symm.trans hRHS
    have hx2 : x ^ 2 = 1 := by
      rw [pow_two]
      nth_rewrite 2 [hxx]
      exact mul_inv_cancel x
    have hxord1 : orderOf x = 1 := by
      rcases (Nat.dvd_prime Nat.prime_two).mp (orderOf_dvd_iff_pow_eq_one.mpr hx2) with h | h
      · exact h
      · exfalso
        obtain ⟨k, hk'⟩ := hx_ord_odd
        rw [h] at hk'
        omega
    exact hx1 (orderOf_eq_one_iff.mp hxord1)

end Work.L2F.Props.oddsub
