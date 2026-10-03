import Mathlib
import Submission.Work.FIArea5.S16Hecke.GaussFourier
import Submission.Work.FIArea5.S16Hecke.GaussChi

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.FIArea6Hecke.R

open Finset
open scoped BigOperators
open Work.FIArea5.S16Hecke
open Work.FIArea5.S16Hecke.GaussBasic

/-- The value of `χ` at the residue class of a Gaussian integer is its value at the Gaussian
integer itself, for a character modulo `4d`. -/
lemma chiR_gOfZI (d : ℕ) [NeZero (4 * d)] {chi : GaussianInt → ℂ}
    (hchi : Work.FITop3.IsCharMod4d d chi) (z : GaussianInt) :
    chiR d chi (gOfZI d z) = chi z :=
  chi_eq_of_gOfZI_eq hchi (gOfZI_zOfG (gOfZI d z))

/-- A Gaussian integer that is a unit modulo `4d` gives a unit of the Gaussian residue ring. -/
lemma isUnitR_gOfZI_of_isUnitMod4d (d : ℕ) [NeZero (4 * d)] {z : GaussianInt}
    (hz : IsUnitMod4d d z) : IsUnitR d (gOfZI d z) := by
  obtain ⟨w, hw⟩ := hz
  refine ⟨gOfZI d w, ?_⟩
  calc gmul d (gOfZI d z) (gOfZI d w) = gOfZI d (z * w) := (gOfZI_mul z w).symm
    _ = gOfZI d (1 : GaussianInt) := gOfZI_eq_of_dvd hw
    _ = gone d := gOfZI_one

/-- The sum of the periodic weight `FR d χ` over the residue ring vanishes as soon as `χ` is
non-trivial on the units: multiplying the summation variable by a unit `u` with `χ(u) ≠ 1`
permutes the ring and multiplies the sum by `χ(u)`. -/
lemma sum_FR_eq_zero_of_nontrivial {d : ℕ} [NeZero (4 * d)] {chi : GaussianInt → ℂ}
    (hchi : Work.FITop3.IsCharMod4d d chi)
    (hnontriv : ∃ u : ZMod (4 * d) × ZMod (4 * d),
      IsUnitR d u ∧ chiR d chi u ≠ 1) :
    (∑ x, FR d chi x) = 0 := by
  obtain ⟨u, hu, hune⟩ := hnontriv
  obtain ⟨u', hu'⟩ := hu
  have huu : IsUnitR d u := ⟨u', hu'⟩
  have hu'' : gmul d u' u = gone d := by rw [gmul_comm]; exact hu'
  let e : (ZMod (4 * d) × ZMod (4 * d)) ≃ (ZMod (4 * d) × ZMod (4 * d)) :=
    { toFun := fun x => gmul d x u
      invFun := fun x => gmul d x u'
      left_inv := fun x => by
        show gmul d (gmul d x u) u' = x
        rw [gmul_assoc, hu', gmul_gone_right]
      right_inv := fun x => by
        show gmul d (gmul d x u') u = x
        rw [gmul_assoc, hu'', gmul_gone_right] }
  have hshift : (∑ x, FR d chi (gmul d x u)) = ∑ x, FR d chi x :=
    Equiv.sum_comp e (FR d chi)
  have hS : (∑ x, FR d chi x) = (∑ x, FR d chi x) * chiR d chi u := by
    calc (∑ x, FR d chi x) = ∑ x, FR d chi (gmul d x u) := hshift.symm
      _ = (∑ x, FR d chi x) * chiR d chi u := by
            rw [Finset.sum_mul]
            exact Finset.sum_congr rfl (fun x _ => FR_mul_unit hchi huu x)
  have h1 : (∑ x, FR d chi x) * (1 - chiR d chi u) = 0 := by
    rw [mul_sub, mul_one]
    exact sub_eq_zero.mpr hS
  have h2 : (1 - chiR d chi u) ≠ 0 := sub_ne_zero.mpr (Ne.symm hune)
  exact (mul_eq_zero.mp h1).resolve_right h2

theorem gaussSum_zero_of_nontrivial {d : ℕ} (hd : 1 ≤ d) {chi : GaussianInt → ℂ}
    (hchi : Work.FIArea5.S16Hecke.IsCharMod4dStrict d chi)
    (hnontriv : ∃ z : GaussianInt, Work.FIPlan.IsPrimary z ∧
      Work.FIArea5.S16Hecke.IsUnitMod4d d z ∧ chi z ≠ 1) :
    Work.FIArea5.S16Hecke.gaussSum d chi 0 = 0 := by
  haveI : NeZero (4 * d) := ⟨by omega⟩
  obtain ⟨z, -, hzunit, hzchi⟩ := hnontriv
  have hchiC : Work.FITop3.IsCharMod4d d chi := hchi.1
  have hu : IsUnitR d (gOfZI d z) := isUnitR_gOfZI_of_isUnitMod4d d hzunit
  have hune : chiR d chi (gOfZI d z) ≠ 1 := by
    rw [chiR_gOfZI d hchiC z]
    exact hzchi
  have hsum : (∑ x, FR d chi x) = 0 :=
    sum_FR_eq_zero_of_nontrivial hchiC ⟨gOfZI d z, hu, hune⟩
  have hFhat : Fhat d chi (gOfZI d 0) = ∑ x, FR d chi x := by
    rw [gOfZI_zero, Fhat]
    exact Finset.sum_congr rfl (fun x _ => by simp [pairG])
  rw [gaussSum_eq_Fhat (d := d) chi (0 : GaussianInt), hFhat, hsum]

end Work.FIArea6Hecke.R
