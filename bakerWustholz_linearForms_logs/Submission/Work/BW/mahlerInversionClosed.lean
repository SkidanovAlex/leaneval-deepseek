import Mathlib
import Submission.Work.BW.roots_facts
import Submission.Work.BW.pow_sum_roots_int
import Submission.Work.BW.inv_pow_sum_roots_int
import Submission.Work.BW.multiset_eq_of_powSum_eq
import Submission.Work.BW.roots_map_conj_eq
import Submission.Work.BW.nonreciprocal_measure_gt

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

open Polynomial

/-- Evaluation identity for the reverse polynomial: for `p : ℚ[X]` with nonzero constant
coefficient and `x : ℂ`, `x ≠ 0`, one has `(reverse p)(x) = x ^ p.natDegree * p(x⁻¹)`. -/
private lemma aeval_reverse_eq (p : Polynomial ℚ) {x : ℂ} (hx : x ≠ 0)
    (hp0 : p.coeff 0 ≠ 0) :
    (aeval x) (reverse p) = x ^ p.natDegree * (aeval x⁻¹) p := by
  letI : Invertible x := invertibleOfNonzero hx
  have hnd : (reverse p).natDegree = p.natDegree := by
    rw [reverse_natDegree, natTrailingDegree_eq_zero.mpr (Or.inr hp0), tsub_zero]
  have hrefl : reflect ((reverse p).natDegree) (reverse p) = p := by
    rw [hnd]
    show reflect p.natDegree (reflect p.natDegree p) = p
    exact reflect_reflect
  have hkey := eval₂_reflect_mul_pow (algebraMap ℚ ℂ) x ((reverse p).natDegree) (reverse p) le_rfl
  rw [hrefl, hnd, invOf_eq_inv x] at hkey
  rw [aeval_def, aeval_def, ← hkey]
  ring

theorem mahlerInversionClosed (P : Polynomial ℤ) (hP : P.Monic) (hirr : Irreducible P)
    (hdeg : 1 < P.natDegree)
    (hM : (P.map (Int.castRingHom ℂ)).mahlerMeasure ≤
      1 + 1 / (52 * (P.natDegree : ℝ) * Real.log (6 * (P.natDegree : ℝ))))
    {z : ℂ} (hz : (P.map (Int.castRingHom ℂ)).IsRoot z) :
    (P.map (Int.castRingHom ℂ)).IsRoot z⁻¹ := by
  obtain ⟨hroot_ne, -, -, hc0⟩ := roots_facts P hP hirr hdeg
  set Q : Polynomial ℂ := P.map (Int.castRingHom ℂ) with hQ
  have hQne : Q ≠ 0 := by rw [hQ]; exact (hP.map _).ne_zero
  -- #### Step 1: under the small-measure hypothesis two roots are mutual inverses.
  have hpair : ∃ a b : ℂ, a ∈ Q.roots ∧ b ∈ Q.roots ∧ a * b = 1 := by
    by_contra hcon
    have hnrec : ∀ a ∈ (P.map (Int.castRingHom ℂ)).roots,
        ∀ b ∈ (P.map (Int.castRingHom ℂ)).roots, a * b ≠ 1 := by
      intro a ha b hb h
      exact hcon ⟨a, b, by rwa [← hQ] at ha, by rwa [← hQ] at hb, h⟩
    have hgt := nonreciprocal_measure_gt P hP hirr hdeg hnrec
    linarith
  obtain ⟨a, b, ha, hb, hab⟩ := hpair
  have ha0 : a ≠ 0 := by rintro rfl; simp at hab
  have hb0 : b ≠ 0 := by rintro rfl; simp at hab
  have hba : b = a⁻¹ := eq_inv_of_mul_eq_one_right hab
  have hz0 : z ≠ 0 := by
    have hzmem : z ∈ Q.roots := (mem_roots hQne).mpr hz
    rw [hQ] at hzmem
    exact hroot_ne z hzmem
  -- #### Step 2: pass to `ℚ` and use `minpoly` + the reverse polynomial.
  set p : Polynomial ℚ := P.map (Int.castRingHom ℚ) with hp
  have hpmonic : p.Monic := by rw [hp]; exact hP.map _
  have hpirr : Irreducible p := by
    rw [hp]
    exact (Polynomial.IsPrimitive.Int.irreducible_iff_irreducible_map_cast hP.isPrimitive).mp hirr
  have hpcoeff0 : p.coeff 0 ≠ 0 := by
    rw [hp, coeff_map]
    exact Int.cast_ne_zero.mpr hc0
  have hcomp : (algebraMap ℚ ℂ).comp (Int.castRingHom ℚ) = Int.castRingHom ℂ := by
    ext n; simp
  have hQp : Q = p.map (algebraMap ℚ ℂ) := by
    rw [hQ, hp, Polynomial.map_map, hcomp]
  -- `a` and `b = a⁻¹` are roots of `p`.
  have ha_aeval : (aeval a) p = 0 := by
    have hroot : (p.map (algebraMap ℚ ℂ)).IsRoot a := by
      rw [← hQp]; exact (mem_roots hQne).mp ha
    rw [IsRoot.def] at hroot
    rwa [← eval₂_eq_eval_map, ← aeval_def] at hroot
  have hb_aeval : (aeval b) p = 0 := by
    have hroot : (p.map (algebraMap ℚ ℂ)).IsRoot b := by
      rw [← hQp]; exact (mem_roots hQne).mp hb
    rw [IsRoot.def] at hroot
    rwa [← eval₂_eq_eval_map, ← aeval_def] at hroot
  have ha_inv_aeval : (aeval a⁻¹) p = 0 := by
    rwa [hba] at hb_aeval
  have hmin : minpoly ℚ a = p :=
    (minpoly.eq_of_irreducible_of_monic hpirr ha_aeval hpmonic).symm
  -- the reverse polynomial vanishes at `a`
  have hrev : (aeval a) (reverse p) = 0 := by
    have h := aeval_reverse_eq p ha0 hpcoeff0
    rw [ha_inv_aeval, mul_zero] at h
    exact h
  have hdvdp : p ∣ reverse p := by
    have h := minpoly.dvd ℚ a hrev
    rwa [hmin] at h
  obtain ⟨c, hc⟩ : ∃ c : ℚ, reverse p = p * C c :=
    ⟨(reverse p).leadingCoeff,
      eq_mul_leadingCoeff_of_monic_of_dvd_of_natDegree_le hpmonic hdvdp (reverse_natDegree_le p)⟩
  -- the reverse polynomial also vanishes at `z`
  have hz_aeval : (aeval z) p = 0 := by
    have hroot : (p.map (algebraMap ℚ ℂ)).IsRoot z := by
      rw [← hQp]; exact hz
    rw [IsRoot.def] at hroot
    rwa [← eval₂_eq_eval_map, ← aeval_def] at hroot
  have hzrev : (aeval z) (reverse p) = 0 := by
    rw [hc, map_mul, hz_aeval, zero_mul]
  -- #### Step 3: conclude `z⁻¹` is a root.
  have hgoal : (aeval z⁻¹) p = 0 := by
    have h := aeval_reverse_eq p hz0 hpcoeff0
    rw [hzrev] at h
    exact (mul_eq_zero.mp h.symm).resolve_left (pow_ne_zero _ hz0)
  rw [hQp, IsRoot.def, ← eval₂_eq_eval_map, ← aeval_def]
  exact hgoal

end Work.BW
