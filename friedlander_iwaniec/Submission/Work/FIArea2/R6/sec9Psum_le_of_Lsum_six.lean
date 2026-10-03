import Mathlib
import Submission.Work.FIArea2.R6.SixDefs
import Submission.Work.FIArea2.R6.Aggregate6
import Submission.Work.FIArea2.R6.Aggregate6_c
import Submission.Work.FIArea2.R6.sec9Psum06_eq_tsum
import Submission.Work.FIArea2.R6.summable_sec9Uwt_Usumming
import Submission.Work.FIArea2.R6.log_absorb6

set_option maxHeartbeats 2000000

namespace Work.FIArea2.R6

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-- **The §9 aggregate with the sector-scale threshold, plugged into the averaged `h`-sum.**

From the per-frequency (9.5) bound `sec9Zsum6 ≤ CZ·ϑ⁻¹(log N+2)^{KZ}·sec9Usumming` and the averaged
`h`-sum hypothesis `hL`, the coefficient-free pair sum `sec9Psum06` satisfies

  `sec9Psum06 Pa ≤ CZ·CL·ϑ⁻¹·(log N+2)^{KZ}·((H²+1)(2R+1)²)·(log(H+R+2))^{KL}`,

`H = Hscale M N`, `R = radN.toNat`.  The proof is the adaptation of `sec9Psum0_le_of_Lsum`
(`Aggregate6.lean`) to the sector-scale objects of `SixDefs.lean`; the only change of arithmetic is
that `ϑ^{-1/2}` is replaced by `ϑ⁻¹` (which is never used except for positivity here). -/
theorem sec9Psum06_le_of_Zbound
    (CZ : ℝ) (hCZ : 0 < CZ) (KZ : ℕ)
    (hZ : ∀ (Pa : Work.FITop.Params) (h1 h2 : ℤ), h1 ≠ 0 ∨ h2 ≠ 0 →
      sec9Zsum6 Pa h1 h2
        ≤ CZ * Pa.ϑ⁻¹ * (Real.log Pa.N + 2) ^ KZ * sec9Usumming Pa h1 h2)
    (CL : ℝ) (hCL : 0 < CL) (KL : ℕ)
    (hL : ∀ (H : ℝ) (hH : 1 ≤ H) (R : ℕ) (hR : 1 ≤ R),
      (∑' h : ℤ × ℤ, (1 + (h.1 : ℝ) ^ 2 / H ^ 2)⁻¹ * (1 + (h.2 : ℝ) ^ 2 / H ^ 2)⁻¹
        * (∑ u1 ∈ Finset.Icc (-(R : ℤ)) (R : ℤ), ∑ u2 ∈ Finset.Icc (-(R : ℤ)) (R : ℤ),
            (Nat.gcd u1.natAbs u2.natAbs : ℝ)
              * (((u1 * h.1 ^ 2 - u2 * h.2 ^ 2).natAbs.divisors.card : ℝ) ^ 4)))
      ≤ CL * (H ^ 2 + 1) * ((((2 * R + 1 : ℕ)) : ℝ) ^ 2) * (Real.log (H + R + 2)) ^ KL) :
    ∀ (Pa : Work.FITop.Params),
      sec9Psum06 Pa
        ≤ CZ * CL * Pa.ϑ⁻¹ * (Real.log Pa.N + 2) ^ KZ
            * ((Work.FIPlan.Hscale Pa.M Pa.N ^ 2 + 1)
                * (2 * (((Work.FITop.radN Pa).toNat : ℕ) : ℝ) + 1) ^ 2)
            * (Real.log (Work.FIPlan.Hscale Pa.M Pa.N
                + (((Work.FITop.radN Pa).toNat : ℕ) : ℝ) + 2)) ^ KL := by
  intro Pa
  have hH1 : 1 ≤ Work.FIPlan.Hscale Pa.M Pa.N := Hscale_ge_one Pa
  have hRadN : (((Work.FITop.radN Pa).toNat : ℕ) : ℤ) = Work.FITop.radN Pa :=
    Int.toNat_of_nonneg (Work.FIArea2.Count.radN_nonneg Pa)
  have hR1 : 1 ≤ (Work.FITop.radN Pa).toNat := by
    have h2 : (2 : ℤ) ≤ Work.FITop.radN Pa := by
      unfold Work.FITop.radN
      have h3 : (2 : ℝ) ≤ Real.sqrt (4 * Pa.N) := by
        rw [show (4 : ℝ) * Pa.N = (2 : ℝ) ^ 2 * Pa.N by ring, Real.sqrt_mul (by positivity),
          Real.sqrt_sq (by norm_num)]
        have h4 : (1 : ℝ) ≤ Real.sqrt Pa.N := Real.one_le_sqrt.mpr Pa.hN1
        nlinarith
      have h5 := Nat.le_ceil (Real.sqrt (4 * Pa.N))
      exact_mod_cast le_trans h3 h5
    omega
  have hlogN0 : (0 : ℝ) ≤ Real.log Pa.N := Real.log_nonneg Pa.hN1
  have hlogKZ : (0 : ℝ) ≤ (Real.log Pa.N + 2) ^ KZ := pow_nonneg (by linarith) KZ
  have hUsumm : Summable (fun h : ℤ × ℤ => sec9Uwt Pa h.1 h.2 * sec9Usumming Pa h.1 h.2) :=
    summable_sec9Uwt_Usumming Pa
  have hGsumm : Summable (fun h : ℤ × ℤ =>
      CZ * Pa.ϑ⁻¹ * (Real.log Pa.N + 2) ^ KZ
        * (sec9Uwt Pa h.1 h.2 * sec9Usumming Pa h.1 h.2)) := hUsumm.mul_left _
  have hZb : ∀ h : ℤ × ℤ, h ≠ (0, 0) →
      sec9Zsum6 Pa h.1 h.2
        ≤ CZ * Pa.ϑ⁻¹ * (Real.log Pa.N + 2) ^ KZ * sec9Usumming Pa h.1 h.2 := by
    intro h hh
    refine hZ Pa h.1 h.2 ?_
    by_contra hc
    push_neg at hc
    exact hh (Prod.ext hc.1 hc.2)
  have hpoint : ∀ h : ℤ × ℤ,
      (if h = (0, 0) then 0 else sec9Uwt Pa h.1 h.2) * sec9Zsum6 Pa h.1 h.2
        ≤ CZ * Pa.ϑ⁻¹ * (Real.log Pa.N + 2) ^ KZ
            * (sec9Uwt Pa h.1 h.2 * sec9Usumming Pa h.1 h.2) := by
    intro h
    by_cases hh : h = (0, 0)
    · rw [if_pos hh, zero_mul]
      exact mul_nonneg (mul_nonneg (mul_nonneg hCZ.le (inv_nonneg.mpr Pa.hϑ0.le)) hlogKZ)
        (mul_nonneg (sec9Uwt_nonneg Pa _ _) (sec9Usumming_nonneg Pa _ _))
    · rw [if_neg hh]
      calc sec9Uwt Pa h.1 h.2 * sec9Zsum6 Pa h.1 h.2
          ≤ sec9Uwt Pa h.1 h.2
              * (CZ * Pa.ϑ⁻¹ * (Real.log Pa.N + 2) ^ KZ * sec9Usumming Pa h.1 h.2) :=
            mul_le_mul_of_nonneg_left (hZb h hh) (sec9Uwt_nonneg Pa _ _)
        _ = CZ * Pa.ϑ⁻¹ * (Real.log Pa.N + 2) ^ KZ
              * (sec9Uwt Pa h.1 h.2 * sec9Usumming Pa h.1 h.2) := by ring
  have hFsumm : Summable (fun h : ℤ × ℤ =>
      (if h = (0, 0) then 0 else sec9Uwt Pa h.1 h.2) * sec9Zsum6 Pa h.1 h.2) :=
    Summable.of_nonneg_of_le (fun h => by
      refine mul_nonneg ?_ (sec9Zsum6_nonneg Pa _ _)
      by_cases hh : h = (0, 0)
      · rw [if_pos hh]
      · rw [if_neg hh]; exact sec9Uwt_nonneg Pa _ _) hpoint hGsumm
  have htsum_le := Summable.tsum_le_tsum hpoint hFsumm hGsumm
  have hLs := hL (Work.FIPlan.Hscale Pa.M Pa.N) hH1 ((Work.FITop.radN Pa).toNat) hR1
  have hLin : (∑' h : ℤ × ℤ, sec9Uwt Pa h.1 h.2 * sec9Usumming Pa h.1 h.2)
      ≤ CL * (Work.FIPlan.Hscale Pa.M Pa.N ^ 2 + 1)
          * (((2 * (Work.FITop.radN Pa).toNat + 1 : ℕ) : ℝ) ^ 2)
          * (Real.log (Work.FIPlan.Hscale Pa.M Pa.N
              + (((Work.FITop.radN Pa).toNat : ℕ) : ℝ) + 2)) ^ KL := by
    refine le_trans (le_of_eq (tsum_congr fun h => ?_)) hLs
    rw [sec9Uwt, sec9Usumming, ← hRadN, Int.toNat_natCast]
  have hgeom : (0 : ℝ) ≤ CZ * Pa.ϑ⁻¹ * (Real.log Pa.N + 2) ^ KZ :=
    mul_nonneg (mul_nonneg hCZ.le (inv_nonneg.mpr Pa.hϑ0.le)) hlogKZ
  rw [sec9Psum06_eq_tsum Pa]
  calc (∑' h : ℤ × ℤ,
          (if h = (0, 0) then 0 else sec9Uwt Pa h.1 h.2) * sec9Zsum6 Pa h.1 h.2)
      ≤ (∑' h : ℤ × ℤ, CZ * Pa.ϑ⁻¹ * (Real.log Pa.N + 2) ^ KZ
          * (sec9Uwt Pa h.1 h.2 * sec9Usumming Pa h.1 h.2)) := htsum_le
    _ = CZ * Pa.ϑ⁻¹ * (Real.log Pa.N + 2) ^ KZ
          * (∑' h : ℤ × ℤ, sec9Uwt Pa h.1 h.2 * sec9Usumming Pa h.1 h.2) := tsum_mul_left
    _ ≤ CZ * Pa.ϑ⁻¹ * (Real.log Pa.N + 2) ^ KZ
          * (CL * (Work.FIPlan.Hscale Pa.M Pa.N ^ 2 + 1)
              * (((2 * (Work.FITop.radN Pa).toNat + 1 : ℕ) : ℝ) ^ 2)
              * (Real.log (Work.FIPlan.Hscale Pa.M Pa.N
                  + (((Work.FITop.radN Pa).toNat : ℕ) : ℝ) + 2)) ^ KL) :=
        mul_le_mul_of_nonneg_left hLin hgeom
    _ = CZ * CL * Pa.ϑ⁻¹ * (Real.log Pa.N + 2) ^ KZ
          * ((Work.FIPlan.Hscale Pa.M Pa.N ^ 2 + 1)
              * (2 * (((Work.FITop.radN Pa).toNat : ℕ) : ℝ) + 1) ^ 2)
          * (Real.log (Work.FIPlan.Hscale Pa.M Pa.N
              + (((Work.FITop.radN Pa).toNat : ℕ) : ℝ) + 2)) ^ KL := by
        have hc : (((2 * (Work.FITop.radN Pa).toNat + 1 : ℕ) : ℝ))
            = 2 * (((Work.FITop.radN Pa).toNat : ℕ) : ℝ) + 1 := by push_cast; ring
        rw [hc]; ring

theorem sec9Psum_le_of_Lsum_six
    (CZ : ℝ) (hCZ : 0 < CZ) (KZ : ℕ)
    (hZ : ∀ (Pa : Work.FITop.Params) (h1 h2 : ℤ), h1 ≠ 0 ∨ h2 ≠ 0 →
      Work.FIArea2.R6.sec9Zsum6 Pa h1 h2
        ≤ CZ * Pa.ϑ⁻¹ * (Real.log Pa.N + 2) ^ KZ * Work.FIArea2.sec9Usumming Pa h1 h2)
    (CL : ℝ) (hCL : 0 < CL) (KL : ℕ)
    (hL : ∀ (H : ℝ) (hH : 1 ≤ H) (R : ℕ) (hR : 1 ≤ R),
      (∑' h : ℤ × ℤ, (1 + (h.1 : ℝ) ^ 2 / H ^ 2)⁻¹ * (1 + (h.2 : ℝ) ^ 2 / H ^ 2)⁻¹
        * (∑ u1 ∈ Finset.Icc (-(R : ℤ)) (R : ℤ), ∑ u2 ∈ Finset.Icc (-(R : ℤ)) (R : ℤ),
            (Nat.gcd u1.natAbs u2.natAbs : ℝ)
              * (((u1 * h.1 ^ 2 - u2 * h.2 ^ 2).natAbs.divisors.card : ℝ) ^ 4)))
      ≤ CL * (H ^ 2 + 1) * ((((2 * R + 1 : ℕ)) : ℝ) ^ 2) * (Real.log (H + R + 2)) ^ KL) :
    ∃ C : ℝ, 0 < C ∧ ∀ (Pa : Work.FITop.Params) (β : GaussianInt → ℂ),
      (∀ z : GaussianInt, ‖β z‖ ≤ Pa.τ) →
      Work.FIArea2.R6.sec9Psum6 Pa β
        ≤ C * (CZ * CL) * Pa.ϑ⁻¹ * Pa.τ ^ (2 : ℕ)
            * ((Work.FIPlan.Hscale Pa.M Pa.N ^ 2 + 1)
                * (2 * (((Work.FITop.radN Pa).toNat : ℕ) : ℝ) + 1) ^ 2)
            * (Real.log (Work.FIPlan.Hscale Pa.M Pa.N
                + (((Work.FITop.radN Pa).toNat : ℕ) : ℝ) + 2)) ^ (KZ + KL + 4) := by
  have hAgg := sec9Psum06_le_of_Zbound CZ hCZ KZ hZ CL hCL KL hL
  refine ⟨4 ^ KZ, pow_pos (by norm_num : (0 : ℝ) < 4) KZ, fun Pa β hβ => ?_⟩
  have hb := sec9Psum6_le_of_beta_bound Pa β hβ
  have hlog := log_absorb6 Pa KZ KL
  have hτ2 : (0 : ℝ) ≤ Pa.τ ^ (2 : ℕ) := sq_nonneg _
  have hnonneg : (0 : ℝ) ≤ CZ * CL * Pa.ϑ⁻¹ * Pa.τ ^ (2 : ℕ)
      * ((Work.FIPlan.Hscale Pa.M Pa.N ^ 2 + 1)
          * (2 * (((Work.FITop.radN Pa).toNat : ℕ) : ℝ) + 1) ^ 2) := by
    refine mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hCZ.le hCL.le)
      (inv_nonneg.mpr Pa.hϑ0.le)) hτ2) ?_
    exact mul_nonneg (by positivity) (by positivity)
  calc sec9Psum6 Pa β
      ≤ Pa.τ ^ (2 : ℕ) * sec9Psum06 Pa := hb
    _ ≤ Pa.τ ^ (2 : ℕ) * (CZ * CL * Pa.ϑ⁻¹ * (Real.log Pa.N + 2) ^ KZ
          * ((Work.FIPlan.Hscale Pa.M Pa.N ^ 2 + 1)
              * (2 * (((Work.FITop.radN Pa).toNat : ℕ) : ℝ) + 1) ^ 2)
          * (Real.log (Work.FIPlan.Hscale Pa.M Pa.N
              + (((Work.FITop.radN Pa).toNat : ℕ) : ℝ) + 2)) ^ KL) :=
        mul_le_mul_of_nonneg_left (hAgg Pa) hτ2
    _ = CZ * CL * Pa.ϑ⁻¹ * Pa.τ ^ (2 : ℕ)
          * ((Work.FIPlan.Hscale Pa.M Pa.N ^ 2 + 1)
              * (2 * (((Work.FITop.radN Pa).toNat : ℕ) : ℝ) + 1) ^ 2)
          * ((Real.log Pa.N + 2) ^ KZ
              * (Real.log (Work.FIPlan.Hscale Pa.M Pa.N
                  + (((Work.FITop.radN Pa).toNat : ℕ) : ℝ) + 2)) ^ KL) := by ring
    _ ≤ CZ * CL * Pa.ϑ⁻¹ * Pa.τ ^ (2 : ℕ)
          * ((Work.FIPlan.Hscale Pa.M Pa.N ^ 2 + 1)
              * (2 * (((Work.FITop.radN Pa).toNat : ℕ) : ℝ) + 1) ^ 2)
          * (4 ^ KZ * (Real.log (Work.FIPlan.Hscale Pa.M Pa.N
              + (((Work.FITop.radN Pa).toNat : ℕ) : ℝ) + 2)) ^ (KZ + KL + 4)) :=
        mul_le_mul_of_nonneg_left hlog hnonneg
    _ = 4 ^ KZ * (CZ * CL) * Pa.ϑ⁻¹ * Pa.τ ^ (2 : ℕ)
          * ((Work.FIPlan.Hscale Pa.M Pa.N ^ 2 + 1)
              * (2 * (((Work.FITop.radN Pa).toNat : ℕ) : ℝ) + 1) ^ 2)
          * (Real.log (Work.FIPlan.Hscale Pa.M Pa.N
              + (((Work.FITop.radN Pa).toNat : ℕ) : ℝ) + 2)) ^ (KZ + KL + 4) := by ring

end

end Work.FIArea2.R6
