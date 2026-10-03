import Mathlib
import Submission.Work.FIArea7.FIsymbols
import Submission.Work.FIArea7.JacTools
import Submission.Work.FIArea7.star_identity
import Submission.Work.FIArea7.chain2

set_option autoImplicit false
namespace Work.FIArea7
open Finset
attribute [local instance] Classical.propDecidable
noncomputable section

/-- The core integer identity (20.4): `(b/|a|) = ε (-1)^{ν'} (v/|u|)(s/|r|)(a/q)`. -/
lemma jksym_core {u v r s : ℤ} (hu : Odd u) (hv : Even v) (hr : Odd r) (hs : Even s)
    (huv : IsCoprime u v) (hrs : IsCoprime r s) (hv0 : v ≠ 0) :
    jacobiSym (u * s + v * r) (u * r - v * s).natAbs
      = (MultEps ({ re := u, im := v } : GaussianInt) ({ re := r, im := s } : GaussianInt))
        * ((Int.negOnePow (((u - 1) * (r - 1) - v * s) / 4) : ℤˣ) : ℤ)
        * jacobiSym v u.natAbs * jacobiSym s r.natAbs
        * jacobiSym (u * r - v * s) (u ^ 2 + v ^ 2).natAbs := by
  have hr0 : r ≠ 0 := by rintro rfl; obtain ⟨k, hk⟩ := hr; omega
  set ρ : ℕ := Int.gcd v r with hρdef
  have hρpos : 0 < ρ := by
    rw [hρdef, Int.gcd_eq_natAbs]
    refine Nat.gcd_pos_of_pos_right _ ?_
    simpa [Int.natAbs_pos] using hr0
  have hρdv : (ρ : ℤ) ∣ v := by rw [hρdef]; exact Int.gcd_dvd_left v r
  have hρdr : (ρ : ℤ) ∣ r := by rw [hρdef]; exact Int.gcd_dvd_right v r
  have hρodd : Odd ρ := by
    have h1 : ρ ∣ r.natAbs := by
      simpa using (Int.natAbs_dvd_natAbs (a := (ρ : ℤ)) (b := r)).mpr hρdr
    exact Odd.of_dvd_nat hr.natAbs h1
  have hρoddZ : Odd ((ρ : ℤ)) := by
    obtain ⟨k, hk⟩ := hρodd
    exact ⟨k, by exact_mod_cast hk⟩
  set v₁ : ℤ := v / (ρ : ℤ) with hv₁def
  set r₁ : ℤ := r / (ρ : ℤ) with hr₁def
  have hvv₁ : v = ρ * v₁ := by
    rw [hv₁def]
    exact (Int.ediv_mul_cancel hρdv).symm.trans (by ring)
  have hrr₁ : r = ρ * r₁ := by
    rw [hr₁def]
    exact (Int.ediv_mul_cancel hρdr).symm.trans (by ring)
  have hv₁0 : v₁ ≠ 0 := by
    intro h; rw [h, mul_zero] at hvv₁; exact hv0 hvv₁
  have hv₁ : Even v₁ := by
    obtain ⟨k, hk⟩ := hv
    obtain ⟨l, hl⟩ := hρoddZ
    refine ⟨k - l * v₁, ?_⟩
    rw [hk] at hvv₁
    rw [hl] at hvv₁
    nlinarith [hvv₁]
  have hr₁ : Odd r₁ := by
    obtain ⟨k, hk⟩ := hr
    obtain ⟨l, hl⟩ := hρoddZ
    refine ⟨k - l * r₁, ?_⟩
    rw [hk] at hrr₁
    rw [hl] at hrr₁
    nlinarith [hrr₁]
  have hcuρ : IsCoprime u (ρ : ℤ) := by
    have h : IsCoprime u (ρ * v₁) := by rw [← hvv₁]; exact huv
    exact IsCoprime.of_mul_right_left h
  have hcv₁ : IsCoprime u v₁ := by
    have h : IsCoprime u (ρ * v₁) := by rw [← hvv₁]; exact huv
    exact IsCoprime.of_mul_right_right h
  have hcsρ : IsCoprime s (ρ : ℤ) := by
    have h : IsCoprime (ρ * r₁) s := by rw [← hrr₁]; exact hrs
    exact (IsCoprime.of_mul_left_left h).symm
  have hcsr₁ : IsCoprime s r₁ := by
    have h : IsCoprime (ρ * r₁) s := by rw [← hrr₁]; exact hrs
    exact (IsCoprime.of_mul_left_right h).symm
  have hv₁r₁ : IsCoprime v₁ r₁ := by
    rw [Int.isCoprime_iff_gcd_eq_one] at ⊢
    have h := Int.gcd_div_gcd_div_gcd (i := v) (j := r) (by rw [← hρdef]; exact hρpos)
    rw [← hρdef] at h
    rwa [← hv₁def, ← hr₁def] at h
  set a : ℤ := u * r - v * s with hadef
  set b : ℤ := u * s + v * r with hbdef
  set q : ℤ := u ^ 2 + v ^ 2 with hqdef
  set m : ℤ := u * r₁ - v₁ * s with hmdef
  have ha : a = ρ * m := by rw [hadef, hmdef, hvv₁, hrr₁]; ring
  have hqpos : q = u ^ 2 + v ^ 2 := hqdef
  have hqmod : q % 4 = 1 := by
    obtain ⟨k, hk⟩ := hu
    obtain ⟨l, hl⟩ := hv
    rw [hqdef, hk, hl]
    rw [show (2 * k + 1) ^ 2 + (l + l) ^ 2 = 4 * (k * k + k + l * l) + 1 by ring]
    rw [Int.add_emod, Int.emod_eq_zero_of_dvd (dvd_mul_right 4 _), zero_add]
    norm_num
  obtain ⟨α, v', hα, hv'⟩ := exists_two_pow_mul_odd v₁ hv₁0
  have hm0 : m ≠ 0 := by
    intro h
    have hur : u * r₁ = v₁ * s := by rw [hmdef] at h; linarith
    have hr₁dvd : r₁ ∣ s := IsCoprime.dvd_of_dvd_mul_left hv₁r₁.symm ⟨u, by rw [← hur]; ring⟩
    have hunit : r₁ ∣ (1 : ℤ) := IsCoprime.dvd_of_dvd_mul_left hcsr₁.symm (by simpa using hr₁dvd)
    have hodd_ev : Even u := by
      rcases Int.isUnit_iff.mp (isUnit_of_dvd_one hunit) with h1 | h1
      · rw [h1, mul_one] at hur; rw [hur]; exact hs.mul_left v₁
      · rw [h1, mul_neg_one] at hur
        have : u = -(v₁ * s) := by linarith [hur]
        rw [this]; exact (hs.mul_left v₁).neg
    obtain ⟨l, hl⟩ := hu
    obtain ⟨k, hk⟩ := hodd_ev
    omega
  have hmne : NeZero m.natAbs := ⟨by simpa [Int.natAbs_pos] using hm0⟩
  have hr₁ne : NeZero r₁.natAbs := ⟨by
    intro h
    have h0 : r₁ = 0 := Int.natAbs_eq_zero.mp h
    rw [h0] at hr₁
    obtain ⟨k, hk⟩ := hr₁
    omega⟩
  have hρne : NeZero ρ := ⟨by omega⟩
  -- coprimalities for the chain
  have hcsρ' : IsCoprime s (ρ : ℤ) := hcsρ
  -- (P1)
  have hbρ : jacobiSym b ρ = jacobiSym (u * s) ρ := by
    refine jacobiSym.mod_left' ?_
    rw [Int.emod_eq_emod_iff_emod_sub_eq_zero]
    refine Int.emod_eq_zero_of_dvd ?_
    have : b - u * s = ρ * (ρ * v₁ * r₁) := by rw [hbdef, hvv₁, hrr₁]; ring
    rw [this]
    exact dvd_mul_right (ρ : ℤ) (ρ * v₁ * r₁)
  have hbm : jacobiSym b m.natAbs
      = jacobiSym (v₁ * r₁) m.natAbs * jacobiSym q m.natAbs := by
    have hfac : v₁ * r₁ * q - v₁ ^ 2 * b = v₁ * u * m := by
      rw [hqdef, hbdef, hmdef, hvv₁, hrr₁]; ring
    have hmod : (v₁ * r₁ * q) % m.natAbs = (v₁ ^ 2 * b) % m.natAbs := by
      rw [Int.emod_eq_emod_iff_emod_sub_eq_zero]
      refine Int.emod_eq_zero_of_dvd ?_
      rw [hfac]
      exact dvd_mul_of_dvd_right ((Int.natAbs_dvd).mpr (dvd_refl m)) (v₁ * u)
    have hsq : jacobiSym v₁ m.natAbs ^ 2 = 1 := by
      have hg : v₁.gcd (m.natAbs : ℤ) = 1 := by
        have hmv : m = u * r₁ + (-s) * v₁ := by rw [hmdef]; ring
        have h2 : v₁.gcd m = v₁.gcd (u * r₁) := by rw [hmv, Int.gcd_add_mul_right_right]
        rw [Int.gcd_eq_natAbs, Int.natAbs_natCast, ← Int.gcd_eq_natAbs, h2,
          ← Int.isCoprime_iff_gcd_eq_one]
        exact hcv₁.symm.mul_right hv₁r₁
      exact jacobiSym.sq_one hg
    rw [(calc jacobiSym (v₁ * r₁) m.natAbs * jacobiSym q m.natAbs
        = jacobiSym (v₁ * r₁ * q) m.natAbs := (jacobiSym.mul_left _ _ _).symm
      _ = jacobiSym (v₁ ^ 2 * b) m.natAbs := jacobiSym.mod_left' hmod
      _ = jacobiSym v₁ m.natAbs ^ 2 * jacobiSym b m.natAbs := by
            rw [jacobiSym.mul_left, jacobiSym.pow_left]
      _ = 1 * jacobiSym b m.natAbs := by rw [hsq]
      _ = jacobiSym b m.natAbs := one_mul _).symm]
  have hqm : jacobiSym q m.natAbs = jacobiSym q a.natAbs := by
    have hρa : a.natAbs = ρ * m.natAbs := by
      rw [ha, Int.natAbs_mul, Int.natAbs_natCast]
    have hqρ : jacobiSym q ρ = 1 := by
      have hmod : q % ρ = (u ^ 2) % ρ := by
        rw [Int.emod_eq_emod_iff_emod_sub_eq_zero]
        refine Int.emod_eq_zero_of_dvd ?_
        have h1 : q - u ^ 2 = v * v := by rw [hqdef]; ring
        rw [h1]
        obtain ⟨k, hk⟩ := hρdv
        exact ⟨k * v, by rw [hk]; ring⟩
      rw [jacobiSym.mod_left q ρ, hmod, ← jacobiSym.mod_left (u ^ 2) ρ, jacobiSym.pow_left]
      have hg : u.gcd (ρ : ℤ) = 1 := Int.isCoprime_iff_gcd_eq_one.mp hcuρ
      exact jacobiSym.sq_one (by simpa [Int.gcd_eq_natAbs] using hg)
    rw [hρa, jacobiSym.mul_right, hqρ, one_mul]
  have hP1 : jacobiSym b a.natAbs
      = jacobiSym (u * s) ρ * jacobiSym (v₁ * r₁) m.natAbs * jacobiSym q a.natAbs := by
    conv_lhs => rw [show a.natAbs = ρ * m.natAbs by rw [ha, Int.natAbs_mul, Int.natAbs_natCast]]
    rw [jacobiSym.mul_right, hbρ, hbm, hqm]
    ring
  -- Step 0: reciprocity turns `(q/|a|)` into `(a/|q|)` since `q ≡ 1 mod 4`
  have hS0 : jacobiSym q a.natAbs = jacobiSym a q.natAbs := by
    have hao : Odd a := by
      rw [hadef]
      exact (hu.mul hr).sub_even (hs.mul_left v)
    have hqo : Odd q := by
      rw [hqdef]
      exact hu.pow.add_even (by rw [pow_two]; exact hv.mul_left v)
    have hqpos : 0 < q := by rw [hqdef]; positivity
    by_cases hc : IsCoprime a q
    · have hrec := jac_recip hqo hao hc.symm
      rw [hrec]
      have hH : HilbertInf q a = 1 := by unfold HilbertInf; rw [if_neg]; omega
      rw [hH, mul_one]
      have hEp : ((Int.negOnePow ((q - 1) / 2 * ((a - 1) / 2)) : ℤˣ) : ℤ) = 1 := by
        have h1 : (Int.negOnePow ((q - 1) / 2 * ((a - 1) / 2)) : ℤˣ) = 1 :=
          (Int.negOnePow_eq_one_iff _).mpr (by
            rw [Int.even_iff]
            have hq1 : (q - 1) / 2 % 2 = 0 := by omega
            rw [Int.mul_emod, hq1, zero_mul, Int.zero_emod])
        rw [h1, Units.val_one]
      rw [hEp, one_mul]
    · have h0 : jacobiSym a q.natAbs = 0 := by
        rw [jacobiSym.eq_zero_iff]
        refine ⟨(Int.natAbs_pos.mpr hqpos.ne').ne', ?_⟩
        rw [Int.gcd_eq_natAbs, Int.natAbs_natCast]
        rw [Int.isCoprime_iff_gcd_eq_one] at hc
        exact hc
      have h0' : jacobiSym q a.natAbs = 0 := by
        rw [jacobiSym.eq_zero_iff]
        have ha0 : a ≠ 0 := by rw [ha]; exact mul_ne_zero (by omega) hm0
        refine ⟨(Int.natAbs_pos.mpr ha0).ne', ?_⟩
        rw [Int.gcd_eq_natAbs, Int.natAbs_natCast]
        rw [Int.isCoprime_iff_gcd_eq_one] at hc
        rwa [Nat.gcd_comm]
      rw [h0, h0']
  -- (P3): `(us/ρ)(v₁/|u|)(s/|r₁|) = (-1)^e (v/|u|)(s/|r|)`
  have hP3 : jacobiSym (u * s) ρ * jacobiSym v₁ u.natAbs * jacobiSym s r₁.natAbs
      = ((Int.negOnePow (((u - 1) / 2) * (((ρ : ℤ) - 1) / 2)) : ℤˣ) : ℤ)
        * jacobiSym v u.natAbs * jacobiSym s r.natAbs := by
    have hrec := jac_recip hu hρoddZ hcuρ
    have hH : HilbertInf u (ρ : ℤ) = 1 := by unfold HilbertInf; rw [if_neg]; omega
    rw [hH, mul_one] at hrec
    rw [show ((ρ : ℤ)).natAbs = ρ from Int.natAbs_natCast ρ] at hrec
    have hsq1 : jacobiSym (ρ : ℤ) u.natAbs ^ 2 = 1 := by
      refine jacobiSym.sq_one ?_
      rw [Int.gcd_eq_natAbs, Int.natAbs_natCast, Int.natAbs_natCast, Nat.gcd_comm]
      have h2 : Int.gcd u (ρ : ℤ) = 1 := Int.isCoprime_iff_gcd_eq_one.mp hcuρ
      rwa [Int.gcd_eq_natAbs, Int.natAbs_natCast] at h2
    have hsq2 : jacobiSym s ρ ^ 2 = 1 :=
      jacobiSym.sq_one (Int.isCoprime_iff_gcd_eq_one.mp hcsρ)
    have hkey : jacobiSym (u * s) ρ
        = ((Int.negOnePow (((u - 1) / 2) * (((ρ : ℤ) - 1) / 2)) : ℤˣ) : ℤ)
          * jacobiSym (ρ : ℤ) u.natAbs * jacobiSym s ρ := by
      rw [jacobiSym.mul_left, hrec]
    have hv' : jacobiSym v u.natAbs = jacobiSym (ρ : ℤ) u.natAbs * jacobiSym v₁ u.natAbs := by
      rw [hvv₁, jacobiSym.mul_left]
    have hr' : jacobiSym s r.natAbs = jacobiSym s ρ * jacobiSym s r₁.natAbs := by
      rw [hrr₁, Int.natAbs_mul, Int.natAbs_natCast, jacobiSym.mul_right]
    rw [hkey, hv', hr']
    ring_nf
  -- assembly
  rw [hP1, hS0, hvv₁, hrr₁]
  rw [stepP2 α (ρ : ℤ) m hu hr₁ hs (by exact_mod_cast hρpos) hρoddZ hα hv₁ hv₁0 hv' hmdef
    hcv₁ hv₁r₁ hcsr₁.symm]
  rw [← hvv₁, ← hrr₁]
  set ε := MultEps ({ re := u, im := v } : GaussianInt) ({ re := r, im := s } : GaussianInt) with hε
  set Nθ := ((Int.negOnePow (((u - 1) * (r - 1) - v * s) / 4
      - (u - 1) / 2 * (((ρ : ℤ) - 1) / 2)) : ℤˣ) : ℤ) with hNθ
  set Nν := ((Int.negOnePow (((u - 1) * (r - 1) - v * s) / 4) : ℤˣ) : ℤ) with hNν
  set Ne := ((Int.negOnePow (((u - 1) / 2) * (((ρ : ℤ) - 1) / 2)) : ℤˣ) : ℤ) with hNe
  set J₁ := jacobiSym (u * s) ρ with hJ₁
  set J₂ := jacobiSym v₁ u.natAbs with hJ₂
  set J₃ := jacobiSym s r₁.natAbs with hJ₃
  set Jv := jacobiSym v u.natAbs with hJv
  set Js := jacobiSym s r.natAbs with hJs
  set Ja := jacobiSym a q.natAbs with hJa
  rw [show J₁ * (ε * Nθ * J₂ * J₃) * Ja = (J₁ * J₂ * J₃) * (ε * Nθ) * Ja by ring]
  rw [hP3]
  rw [show (Ne * Jv * Js) * (ε * Nθ) * Ja = ε * (Nθ * Ne) * Jv * Js * Ja by ring]
  rw [show Nθ * Ne = Nν from by
    rw [hNθ, hNe, ← Units.val_mul, ← Int.negOnePow_add, hNν,
      show (((u - 1) * (r - 1) - v * s) / 4 - (u - 1) / 2 * (((ρ : ℤ) - 1) / 2))
          + (u - 1) / 2 * (((ρ : ℤ) - 1) / 2)
        = ((u - 1) * (r - 1) - v * s) / 4 from by ring]]

