import Mathlib
import Submission.Work.FIArea7.FIsymbols
import Submission.Work.FIArea7.JacTools
import Submission.Work.FIArea7.star_identity

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
namespace Work.FIArea7
open Finset
attribute [local instance] Classical.propDecidable
noncomputable section

lemma stepP2 {u v₁ r₁ s v' : ℤ} (α : ℕ) (ρ m : ℤ)
    (hu : Odd u) (hr₁ : Odd r₁) (hs : Even s) (hρ : 0 < ρ) (hρodd : Odd ρ)
    (hα : v₁ = 2 ^ α * v') (hv₁ : Even v₁) (hv₁0 : v₁ ≠ 0) (hv' : Odd v')
    (hm : m = u * r₁ - v₁ * s)
    (hcu : IsCoprime u v₁) (hcr : IsCoprime v₁ r₁) (hr₁s : IsCoprime r₁ s) :
    jacobiSym (v₁ * r₁) m.natAbs
      = (MultEps (⟨u, ρ * v₁⟩ : GaussianInt) ⟨ρ * r₁, s⟩ : ℤ)
        * ((Int.negOnePow (((u - 1) * (ρ * r₁ - 1) - (ρ * v₁) * s) / 4
            - (u - 1) / 2 * ((ρ - 1) / 2)) : ℤˣ) : ℤ)
        * jacobiSym v₁ u.natAbs * jacobiSym s r₁.natAbs := by
  have hm_odd : Odd m := by
    rw [hm]
    exact (hu.mul hr₁).sub_even (hs.mul_left v₁)
  have hv'dvd : v' ∣ v₁ := ⟨(2 : ℤ) ^ α, by rw [hα]; ring⟩
  have hu_v' : IsCoprime u v' := by
    rw [Int.isCoprime_iff_gcd_eq_one] at hcu ⊢
    exact Nat.eq_one_of_dvd_one (hcu ▸ Int.gcd_dvd_gcd_of_dvd_right u hv'dvd)
  have hv'_r₁ : IsCoprime v' r₁ := by
    rw [Int.isCoprime_iff_gcd_eq_one] at hcr ⊢
    refine Nat.eq_one_of_dvd_one ?_
    have h := Int.gcd_dvd_gcd_of_dvd_left r₁ hv'dvd
    rw [hcr] at h
    simpa using h
  have hv'_m : IsCoprime v' m := by
    rw [Int.isCoprime_iff_gcd_eq_one]
    have h1 : v'.gcd m = v'.gcd (u * r₁) := by
      rw [hm, show u * r₁ - v₁ * s = u * r₁ + (-(2 ^ α * s)) * v' by rw [hα]; ring,
        Int.gcd_add_mul_right_right]
    rw [h1, ← Int.isCoprime_iff_gcd_eq_one]
    exact hu_v'.symm.mul_right hv'_r₁
  have hr₁_m : IsCoprime r₁ m := by
    rw [Int.isCoprime_iff_gcd_eq_one]
    have h1 : r₁.gcd m = r₁.gcd (v₁ * s) := by
      rw [hm, show u * r₁ - v₁ * s = -(v₁ * s) + u * r₁ by ring, Int.gcd_add_mul_right_right,
        Int.gcd_eq_natAbs, Int.gcd_eq_natAbs, Int.natAbs_neg]
    rw [h1, ← Int.isCoprime_iff_gcd_eq_one]
    exact hcr.symm.mul_right hr₁s
  have hpeel_m : jacobiSym v₁ m.natAbs
      = (ZMod.χ₈ (m : ZMod 8) : ℤ) ^ α * jacobiSym v' m.natAbs := by
    rw [hα, jacobiSym_two_pow_mul m.natAbs hm_odd.natAbs v' α, chi8_natAbs]
  have hpeel_r : jacobiSym v₁ r₁.natAbs
      = (ZMod.χ₈ (r₁ : ZMod 8) : ℤ) ^ α * jacobiSym v' r₁.natAbs := by
    rw [hα, jacobiSym_two_pow_mul r₁.natAbs hr₁.natAbs v' α, chi8_natAbs]
  have hpeel_u : jacobiSym v₁ u.natAbs
      = (ZMod.χ₈ (u : ZMod 8) : ℤ) ^ α * jacobiSym v' u.natAbs := by
    rw [hα, jacobiSym_two_pow_mul u.natAbs hu.natAbs v' α, chi8_natAbs]
  have hrec_vm : jacobiSym v' m.natAbs
      = ((Int.negOnePow (((v' - 1) / 2) * ((m - 1) / 2)) : ℤˣ) : ℤ) * HilbertInf v' m
        * jacobiSym m v'.natAbs := jac_recip hv' hm_odd hv'_m
  have hrec_r₁m : jacobiSym r₁ m.natAbs
      = ((Int.negOnePow (((r₁ - 1) / 2) * ((m - 1) / 2)) : ℤˣ) : ℤ) * HilbertInf r₁ m
        * jacobiSym m r₁.natAbs := jac_recip hr₁ hm_odd hr₁_m
  have hm_v' : jacobiSym m v'.natAbs
      = jacobiSym u v'.natAbs * jacobiSym r₁ v'.natAbs := by
    have hdvd : v' ∣ m - u * r₁ := by
      have : m - u * r₁ = -(2 ^ α * s) * v' := by rw [hm, hα]; ring
      rw [this]; exact dvd_mul_left v' _
    have hmod : m % v'.natAbs = (u * r₁) % v'.natAbs :=
      Int.emod_eq_emod_iff_emod_sub_eq_zero.mpr
        (Int.emod_eq_zero_of_dvd (Int.natAbs_dvd.mpr hdvd))
    rw [jacobiSym.mod_left m v'.natAbs, hmod, ← jacobiSym.mod_left (u * r₁) v'.natAbs,
      jacobiSym.mul_left]
  have hm_r₁ : jacobiSym m r₁.natAbs
      = jacobiSym (-1) r₁.natAbs * jacobiSym v₁ r₁.natAbs * jacobiSym s r₁.natAbs := by
    have hdvd : (r₁.natAbs : ℤ) ∣ m - (-(v₁ * s)) := by
      have h1 : (r₁.natAbs : ℤ) ∣ r₁ := (Int.natAbs_dvd).mpr (dvd_refl r₁)
      have h2 : m - (-(v₁ * s)) = u * r₁ := by rw [hm]; ring
      rw [h2]; exact dvd_mul_of_dvd_right h1 u
    have hmod : m % (r₁.natAbs : ℤ) = (-(v₁ * s)) % (r₁.natAbs : ℤ) :=
      Int.emod_eq_emod_iff_emod_sub_eq_zero.mpr
        (by simpa only [sub_neg_eq_add] using Int.emod_eq_zero_of_dvd hdvd)
    rw [jacobiSym.mod_left m r₁.natAbs, hmod, ← jacobiSym.mod_left (-(v₁ * s)) r₁.natAbs,
      show -(v₁ * s) = (-1) * (v₁ * s) by ring, jacobiSym.mul_left, jacobiSym.mul_left]
    ring
  have hneg : jacobiSym (-1) r₁.natAbs
      = ((Int.negOnePow (((r₁.natAbs : ℤ) - 1) / 2) : ℤˣ) : ℤ) :=
    jacobiSym_neg_one_eq r₁.natAbs hr₁.natAbs
  have hpair_u : jacobiSym u v'.natAbs * jacobiSym v' u.natAbs
      = ((Int.negOnePow (((u - 1) / 2) * ((v' - 1) / 2)) : ℤˣ) : ℤ) * HilbertInf u v' := by
    have h : jacobiSym u v'.natAbs
        = ((Int.negOnePow (((u - 1) / 2) * ((v' - 1) / 2)) : ℤˣ) : ℤ) * HilbertInf u v'
          * jacobiSym v' u.natAbs := jac_recip hu hv' hu_v'
    have hsq : jacobiSym v' u.natAbs * jacobiSym v' u.natAbs = 1 := by
      have hg : v'.gcd (u.natAbs : ℤ) = 1 := by
        rw [Int.gcd_eq_natAbs, Int.natAbs_natCast, ← Int.gcd_eq_natAbs]
        exact Int.isCoprime_iff_gcd_eq_one.mp hu_v'.symm
      have h' := jacobiSym.sq_one hg
      rwa [pow_two] at h'
    rw [h, mul_assoc, hsq, mul_one]
  have hpair_r : jacobiSym v' r₁.natAbs * jacobiSym r₁ v'.natAbs
      = ((Int.negOnePow (((v' - 1) / 2) * ((r₁ - 1) / 2)) : ℤˣ) : ℤ) * HilbertInf v' r₁ := by
    have h : jacobiSym v' r₁.natAbs
        = ((Int.negOnePow (((v' - 1) / 2) * ((r₁ - 1) / 2)) : ℤˣ) : ℤ) * HilbertInf v' r₁
          * jacobiSym r₁ v'.natAbs := jac_recip hv' hr₁ hv'_r₁
    have hsq : jacobiSym r₁ v'.natAbs * jacobiSym r₁ v'.natAbs = 1 := by
      have hg : r₁.gcd (v'.natAbs : ℤ) = 1 := by
        rw [Int.gcd_eq_natAbs, Int.natAbs_natCast, ← Int.gcd_eq_natAbs]
        exact Int.isCoprime_iff_gcd_eq_one.mp hv'_r₁.symm
      have h' := jacobiSym.sq_one hg
      rwa [pow_two] at h'
    rw [h, mul_assoc, hsq, mul_one]
  have hF : Even (((m - 1) / 2) + ((u - 1) / 2) + ((r₁ - 1) / 2)) := by
    have hmur : (m * u * r₁) % 4 = 1 := by
      obtain ⟨k, hk⟩ := hu.mul hr₁
      obtain ⟨a, ha⟩ := hv₁
      obtain ⟨b, hb⟩ := hs
      have hv₁s : v₁ * s = 4 * (a * b) := by rw [ha, hb]; ring
      have h1 : m * u * r₁ = (u * r₁) * (u * r₁) - u * r₁ * (v₁ * s) := by rw [hm]; ring
      rw [h1, hv₁s]
      have h2 : (u * r₁ * (4 * (a * b))) % 4 = 0 := by
        rw [show u * r₁ * (4 * (a * b)) = 4 * (u * r₁ * (a * b)) by ring]
        exact Int.emod_eq_zero_of_dvd (dvd_mul_right 4 _)
      have h3 : ((u * r₁) * (u * r₁)) % 4 = 1 := by
        rw [hk]
        rw [show (2 * k + 1) * (2 * k + 1) = 4 * (k * k + k) + 1 by ring,
          Int.add_emod, Int.emod_eq_zero_of_dvd (dvd_mul_right 4 _), zero_add]
        norm_num
      rw [Int.sub_emod, h3, h2, sub_zero]
      norm_num
    have hkey : ((Int.negOnePow (((m - 1) / 2) + ((u - 1) / 2) + ((r₁ - 1) / 2)) : ℤˣ) : ℤ)
        = 1 := by
      rw [Int.negOnePow_add, Int.negOnePow_add, Units.val_mul, Units.val_mul,
        ← chi4_int_eq_negOnePow hm_odd, ← chi4_int_eq_negOnePow hu,
        ← chi4_int_eq_negOnePow hr₁, ← map_mul, ← map_mul]
      rw [show (↑m * ↑u * ↑r₁ : ZMod 4) = ((m * u * r₁ : ℤ) : ZMod 4) by push_cast; ring,
        ZMod.χ₄_int_mod_four, hmur]
      rfl
    exact (Int.negOnePow_eq_one_iff _).mp (Units.ext (hkey.trans Units.val_one.symm))
  have hN₃u : (Int.negOnePow (((v' - 1) / 2) * ((m - 1) / 2)) : ℤˣ)
      * (Int.negOnePow (((u - 1) / 2) * ((v' - 1) / 2)) : ℤˣ)
      * (Int.negOnePow (((v' - 1) / 2) * ((r₁ - 1) / 2)) : ℤˣ) = 1 := by
    rw [← Int.negOnePow_add, ← Int.negOnePow_add, Int.negOnePow_eq_one_iff]
    have he : ((v' - 1) / 2) * ((m - 1) / 2) + ((u - 1) / 2) * ((v' - 1) / 2)
        + ((v' - 1) / 2) * ((r₁ - 1) / 2)
        = ((v' - 1) / 2) * (((m - 1) / 2) + ((u - 1) / 2) + ((r₁ - 1) / 2)) := by ring
    rw [he]
    exact hF.mul_left _
  have hN₃ : ((Int.negOnePow (((v' - 1) / 2) * ((m - 1) / 2)) : ℤˣ) : ℤ)
      * ((Int.negOnePow (((u - 1) / 2) * ((v' - 1) / 2)) : ℤˣ) : ℤ)
      * ((Int.negOnePow (((v' - 1) / 2) * ((r₁ - 1) / 2)) : ℤˣ) : ℤ) = 1 := by
    rw [← Units.val_mul, ← Units.val_mul, show
      (Int.negOnePow (((v' - 1) / 2) * ((m - 1) / 2)) : ℤˣ)
        * (Int.negOnePow (((u - 1) / 2) * ((v' - 1) / 2)) : ℤˣ)
        * (Int.negOnePow (((v' - 1) / 2) * ((r₁ - 1) / 2)) : ℤˣ)
      = (Int.negOnePow (((v' - 1) / 2) * ((m - 1) / 2)) : ℤˣ)
        * (Int.negOnePow (((u - 1) / 2) * ((v' - 1) / 2)) : ℤˣ)
        * (Int.negOnePow (((v' - 1) / 2) * ((r₁ - 1) / 2)) : ℤˣ) from rfl,
      hN₃u, Units.val_one]
  -- assemble
  rw [jacobiSym.mul_left, hpeel_m, hrec_vm, hrec_r₁m, hm_v', hm_r₁, hneg, hpeel_r]
  rw [show (MultEps (⟨u, ρ * v₁⟩ : GaussianInt) ⟨ρ * r₁, s⟩ : ℤ)
      * ((Int.negOnePow (((u - 1) * (ρ * r₁ - 1) - (ρ * v₁) * s) / 4
          - (u - 1) / 2 * ((ρ - 1) / 2)) : ℤˣ) : ℤ)
      * jacobiSym v₁ u.natAbs * jacobiSym s r₁.natAbs
      = (MultEps (⟨u, ρ * v₁⟩ : GaussianInt) ⟨ρ * r₁, s⟩ : ℤ)
        * ((Int.negOnePow (((u - 1) * (ρ * r₁ - 1) - (ρ * v₁) * s) / 4
            - (u - 1) / 2 * ((ρ - 1) / 2)) : ℤˣ) : ℤ)
        * ((ZMod.χ₈ (u : ZMod 8) : ℤ) ^ α * jacobiSym v' u.natAbs)
        * jacobiSym s r₁.natAbs from by rw [hpeel_u]]
  have hsq_u : jacobiSym v' u.natAbs * jacobiSym v' u.natAbs = 1 := by
    have hg : v'.gcd (u.natAbs : ℤ) = 1 := by
      rw [Int.gcd_eq_natAbs, Int.natAbs_natCast, ← Int.gcd_eq_natAbs]
      exact Int.isCoprime_iff_gcd_eq_one.mp hu_v'.symm
    have h' := jacobiSym.sq_one hg
    rwa [pow_two] at h'
  have hsq_r : jacobiSym r₁ v'.natAbs * jacobiSym r₁ v'.natAbs = 1 := by
    have hg : r₁.gcd (v'.natAbs : ℤ) = 1 := by
      rw [Int.gcd_eq_natAbs, Int.natAbs_natCast, ← Int.gcd_eq_natAbs]
      exact Int.isCoprime_iff_gcd_eq_one.mp hv'_r₁.symm
    have h' := jacobiSym.sq_one hg
    rwa [pow_two] at h'
  have ha : jacobiSym u v'.natAbs
      = ((Int.negOnePow (((u - 1) / 2) * ((v' - 1) / 2)) : ℤˣ) : ℤ) * HilbertInf u v'
        * jacobiSym v' u.natAbs := by
    calc jacobiSym u v'.natAbs = jacobiSym u v'.natAbs * 1 := by ring
      _ = jacobiSym u v'.natAbs * (jacobiSym v' u.natAbs * jacobiSym v' u.natAbs) := by
            rw [hsq_u]
      _ = (jacobiSym u v'.natAbs * jacobiSym v' u.natAbs) * jacobiSym v' u.natAbs := by ring
      _ = (((Int.negOnePow (((u - 1) / 2) * ((v' - 1) / 2)) : ℤˣ) : ℤ) * HilbertInf u v') *
            jacobiSym v' u.natAbs := by rw [hpair_u]
      _ = _ := by ring
  have hb : jacobiSym v' r₁.natAbs
      = ((Int.negOnePow (((v' - 1) / 2) * ((r₁ - 1) / 2)) : ℤˣ) : ℤ) * HilbertInf v' r₁
        * jacobiSym r₁ v'.natAbs := by
    calc jacobiSym v' r₁.natAbs = jacobiSym v' r₁.natAbs * 1 := by ring
      _ = jacobiSym v' r₁.natAbs * (jacobiSym r₁ v'.natAbs * jacobiSym r₁ v'.natAbs) := by
            rw [hsq_r]
      _ = (jacobiSym v' r₁.natAbs * jacobiSym r₁ v'.natAbs) * jacobiSym r₁ v'.natAbs := by ring
      _ = (((Int.negOnePow (((v' - 1) / 2) * ((r₁ - 1) / 2)) : ℤˣ) : ℤ) * HilbertInf v' r₁) *
            jacobiSym r₁ v'.natAbs := by rw [hpair_r]
      _ = _ := by ring
  have hchi : (ZMod.χ₈ ((m * r₁ * u : ℤ) : ZMod 8) : ℤ) ^ α
      = (ZMod.χ₈ (m : ZMod 8) : ℤ) ^ α * (ZMod.χ₈ (r₁ : ZMod 8) : ℤ) ^ α
        * (ZMod.χ₈ (u : ZMod 8) : ℤ) ^ α := by
    rw [show (((m * r₁ * u : ℤ)) : ZMod 8)
        = ((m : ZMod 8) * (r₁ : ZMod 8) * (u : ZMod 8)) by push_cast; ring,
      map_mul, map_mul, mul_pow, mul_pow]
  have hNsum : ((Int.negOnePow ((r₁ - 1) / 2 * ((m - 1) / 2) + ((r₁.natAbs : ℤ) - 1) / 2)
      : ℤˣ) : ℤ)
      = ((Int.negOnePow ((r₁ - 1) / 2 * ((m - 1) / 2)) : ℤˣ) : ℤ)
        * ((Int.negOnePow (((r₁.natAbs : ℤ) - 1) / 2) : ℤˣ) : ℤ) := by
    rw [Int.negOnePow_add, Units.val_mul]
  rw [← star_identity u v₁ r₁ s v' α ρ m hu hv₁ hv₁0 hα hv' hr₁ hs hρ hρodd hm hcu hcr,
    ha, hb, hchi, hNsum]
  ring_nf
  rw [show jacobiSym r₁ v'.natAbs ^ 2 = 1 by rw [pow_two]; exact hsq_r]
  rw [show (ZMod.χ₈ (u : ZMod 8) : ℤ) ^ (α * 2) = 1 by
      have hu2 : u % 2 = 1 := Int.odd_iff.mp hu
      rw [mul_comm α 2, pow_mul, show (ZMod.χ₈ (u : ZMod 8) : ℤ) ^ 2 = 1 by
        rw [ZMod.χ₈_int_eq_if_mod_eight, if_neg (by omega)]
        split_ifs <;> norm_num, one_pow]]
  have hN₃n : ((Int.negOnePow (((-1 + v') / 2) * ((-1 + m) / 2)) : ℤˣ) : ℤ)
      * ((Int.negOnePow (((-1 + v') / 2) * ((-1 + u) / 2)) : ℤˣ) : ℤ)
      * ((Int.negOnePow (((-1 + v') / 2) * ((-1 + r₁) / 2)) : ℤˣ) : ℤ) = 1 := by
    convert hN₃ using 2 <;> ring
  simp only [mul_one, one_mul]
  ring_nf at hN₃n
  set χm := ZMod.χ₈ (m : ZMod 8) ^ α with hχm
  set χr := ZMod.χ₈ (r₁ : ZMod 8) ^ α with hχr
  set H3 := HilbertInf v' m with hH3
  set H4 := HilbertInf u v' with hH4
  set H2 := HilbertInf r₁ m with hH2
  set H5 := HilbertInf v' r₁ with hH5
  set Ju := jacobiSym v' u.natAbs with hJu
  set Js := jacobiSym s r₁.natAbs with hJs
  set N2 := ((Int.negOnePow ((-1 + m) / 2 * ((-1 + r₁) / 2)) : ℤˣ) : ℤ) with hN2
  set Nn := ((Int.negOnePow ((-1 + (r₁.natAbs : ℤ)) / 2) : ℤˣ) : ℤ) with hNn
  set N3 := ((Int.negOnePow ((-1 + v') / 2 * ((-1 + m) / 2)) : ℤˣ) : ℤ) with hN3
  set N4 := ((Int.negOnePow ((-1 + v') / 2 * ((-1 + u) / 2)) : ℤˣ) : ℤ) with hN4
  set N5 := ((Int.negOnePow ((-1 + v') / 2 * ((-1 + r₁) / 2)) : ℤˣ) : ℤ) with hN5
  rw [show χm * N3 * H3 * N4 * H4 * Ju * N2 * H2 * Nn * χr * N5 * H5 * Js
      = χm * H3 * H4 * Ju * N2 * H2 * Nn * χr * H5 * Js * (N3 * N4 * N5) by ring]
  rw [hN₃n, mul_one]

end
end Work.FIArea7
