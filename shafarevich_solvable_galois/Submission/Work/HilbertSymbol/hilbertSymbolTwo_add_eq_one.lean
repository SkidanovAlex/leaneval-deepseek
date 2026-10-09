import Mathlib
import Submission.Work.HilbertSymbol.Places
import Submission.Work.HilbertSymbol.Symbol
import Submission.Work.HilbertSymbol.padicVal_eq_zero_iff
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

noncomputable section

open scoped Classical

namespace Work.HilbertSymbol

/-!
# The `2`-adic Hilbert symbol of `a` and `b` with `a + b = 1`

We prove `(a,b)_2 = 1` whenever `a + b = 1` in `ℚ`, where `(·,·)_2` is the explicit `2`-adic
Hilbert symbol of `Submission.Work.HilbertSymbol.Basic`:

`(a,b)_2 = signOf (ε(u) ε(v) + α ω(v) + β ω(u))`, with `u = unitPart 2 a`, `v = unitPart 2 b`,
`α = v₂(a)`, `β = v₂(b)`, `ε = epsZ` and `ω = omegaZ`.

The proof works with the residue classes of `u` and `v` modulo `8` (where `ε` and `ω` live) and the
relation `2^α (u : ℚ₂) + 2^β (v : ℚ₂) = 1`, which is the image in `ℚ₂` of `a + b = 1`.  Writing
`X`, `Y` for the reductions of `u`, `v` modulo `8`, the possible relations between `X` and `Y` are
`X + 2Y = 1`, `X + 4Y = 1`, `X = 1` (when `α = 0 < β`), the symmetric ones (when `β = 0 < α`), and
`X + Y = 2^τ` (when `α = β = -τ < 0`).  Each of these forces the exponent
`ε(u)ε(v) + α ω(v) + β ω(u)` to vanish, by a finite check on `(ZMod 8)^×`.
-/

/-! ## The reduction map modulo `8` -/

/-- The `2`-adic unit `u`, reduced modulo `8` (as a unit of `ZMod 8`). -/
def toZ8u (u : ℤ_[2]ˣ) : (ZMod (2 ^ 3))ˣ := Units.map (PadicInt.toZModPow 3).toMonoidHom u

/-- The underlying element of `ZMod 8` of `toZ8u u`. -/
theorem toZ8u_coe (u : ℤ_[2]ˣ) :
    (toZ8u u : ZMod (2 ^ 3)) = PadicInt.toZModPow 3 (u : ℤ_[2]) := rfl

/-- `ε`, as a function of the residue class modulo `8`. -/
def epsOf (X : ZMod (2 ^ 3)) : ZMod 2 := ((X.val / 2 : ℕ) : ZMod 2)

/-- `ω`, as a function of the residue class modulo `8`. -/
def omgOf (X : ZMod (2 ^ 3)) : ZMod 2 :=
  if X.val = 1 ∨ X.val = 7 then 0 else 1

/-- Compatibility of the reductions modulo `4` and modulo `8`. -/
theorem toZModPow_compat (x : ℤ_[2]) :
    PadicInt.toZModPow 2 x = ZMod.cast (PadicInt.toZModPow 3 x) := by
  have h3 : x - ((x.appr 3 : ℕ) : ℤ_[2]) ∈ Ideal.span {(((2 : ℕ) : ℤ_[2])) ^ 3} :=
    PadicInt.appr_spec 3 x
  have h2 : x - ((x.appr 2 : ℕ) : ℤ_[2]) ∈ Ideal.span {(((2 : ℕ) : ℤ_[2])) ^ 2} :=
    PadicInt.appr_spec 2 x
  have hmono : Ideal.span {(((2 : ℕ) : ℤ_[2])) ^ 3} ≤ Ideal.span {(((2 : ℕ) : ℤ_[2])) ^ 2} := by
    rw [Ideal.span_singleton_le_span_singleton]
    exact pow_dvd_pow _ (by norm_num : 2 ≤ 3)
  have h3' := hmono h3
  have hdiff : ((x.appr 3 : ℕ) : ℤ_[2]) - ((x.appr 2 : ℕ) : ℤ_[2])
      ∈ Ideal.span {(((2 : ℕ) : ℤ_[2])) ^ 2} := by
    have : ((x.appr 3 : ℕ) : ℤ_[2]) - ((x.appr 2 : ℕ) : ℤ_[2])
        = (x - ((x.appr 2 : ℕ) : ℤ_[2])) - (x - ((x.appr 3 : ℕ) : ℤ_[2])) := by ring
    rw [this]
    exact Submodule.sub_mem _ h2 h3'
  have hker : ((x.appr 3 : ℕ) : ℤ_[2]) - ((x.appr 2 : ℕ) : ℤ_[2])
      ∈ RingHom.ker (PadicInt.toZModPow 2) := by
    rw [PadicInt.ker_toZModPow]; exact hdiff
  have hzero :
      PadicInt.toZModPow 2 (((x.appr 3 : ℕ) : ℤ_[2]) - ((x.appr 2 : ℕ) : ℤ_[2])) = 0 := hker
  rw [map_sub, map_natCast, map_natCast] at hzero
  have heq : ((x.appr 2 : ℕ) : ZMod (2 ^ 2)) = ((x.appr 3 : ℕ) : ZMod (2 ^ 2)) :=
    (sub_eq_zero.mp hzero).symm
  rw [show PadicInt.toZModPow 2 x = ((x.appr 2 : ℕ) : ZMod (2 ^ 2)) from rfl,
      show PadicInt.toZModPow 3 x = ((x.appr 3 : ℕ) : ZMod (2 ^ 3)) from rfl,
      ZMod.cast_natCast (R := ZMod (2 ^ 2)) (by norm_num : 2 ^ 2 ∣ 2 ^ 3)]
  exact heq

/-- Arithmetic core of the compatibility: `(r % 4) / 2` and `r / 2` agree modulo `2`. -/
theorem nat_div_mod_two (r : ℕ) :
    (((r % 4) / 2 : ℕ) : ZMod 2) = ((r / 2 : ℕ) : ZMod 2) := by
  rw [ZMod.natCast_eq_natCast_iff']; omega

/-- `epsZ` only depends on the residue class of the unit modulo `8`. -/
theorem epsZ_eq_epsOf (u : ℤ_[2]ˣ) : epsZ u = epsOf (toZ8u u : ZMod (2 ^ 3)) := by
  rw [epsZ]
  have hcast : PadicInt.toZModPow 2 (u : ℤ_[2]) = ZMod.cast (toZ8u u : ZMod (2 ^ 3)) :=
    toZModPow_compat (u : ℤ_[2])
  rw [hcast, ZMod.cast_eq_val, ZMod.val_natCast]
  exact nat_div_mod_two _

/-- `omegaZ` only depends on the residue class of the unit modulo `8`. -/
theorem omegaZ_eq_omgOf (u : ℤ_[2]ˣ) : omegaZ u = omgOf (toZ8u u : ZMod (2 ^ 3)) := rfl

/-! ## Finite checks on `(ZMod 8)^×` -/

theorem check_beta_one : ∀ X Y : (ZMod (2 ^ 3))ˣ,
    (X : ZMod (2 ^ 3)) + 2 * (Y : ZMod (2 ^ 3)) = 1 →
      epsOf (X : ZMod (2 ^ 3)) * epsOf (Y : ZMod (2 ^ 3)) + omgOf (X : ZMod (2 ^ 3)) = 0 := by
  decide

theorem check_beta_two : ∀ X Y : (ZMod (2 ^ 3))ˣ,
    (X : ZMod (2 ^ 3)) + 4 * (Y : ZMod (2 ^ 3)) = 1 →
      epsOf (X : ZMod (2 ^ 3)) * epsOf (Y : ZMod (2 ^ 3)) = 0 := by
  decide

theorem check_alpha_one : ∀ X Y : (ZMod (2 ^ 3))ˣ,
    2 * (X : ZMod (2 ^ 3)) + (Y : ZMod (2 ^ 3)) = 1 →
      epsOf (X : ZMod (2 ^ 3)) * epsOf (Y : ZMod (2 ^ 3)) + omgOf (Y : ZMod (2 ^ 3)) = 0 := by
  decide

theorem check_alpha_two : ∀ X Y : (ZMod (2 ^ 3))ˣ,
    4 * (X : ZMod (2 ^ 3)) + (Y : ZMod (2 ^ 3)) = 1 →
      epsOf (X : ZMod (2 ^ 3)) * epsOf (Y : ZMod (2 ^ 3)) = 0 := by
  decide

theorem check_tau_one : ∀ X Y : (ZMod (2 ^ 3))ˣ,
    (X : ZMod (2 ^ 3)) + (Y : ZMod (2 ^ 3)) = 2 →
      epsOf (X : ZMod (2 ^ 3)) * epsOf (Y : ZMod (2 ^ 3))
        + omgOf (X : ZMod (2 ^ 3)) + omgOf (Y : ZMod (2 ^ 3)) = 0 := by
  decide

theorem check_tau_two : ∀ X Y : (ZMod (2 ^ 3))ˣ,
    (X : ZMod (2 ^ 3)) + (Y : ZMod (2 ^ 3)) = 4 →
      epsOf (X : ZMod (2 ^ 3)) * epsOf (Y : ZMod (2 ^ 3)) = 0 := by
  decide

theorem check_tau_big_eps : ∀ X Y : (ZMod (2 ^ 3))ˣ,
    (X : ZMod (2 ^ 3)) + (Y : ZMod (2 ^ 3)) = 0 →
      epsOf (X : ZMod (2 ^ 3)) * epsOf (Y : ZMod (2 ^ 3)) = 0 := by
  decide

theorem check_tau_big_omg : ∀ X Y : (ZMod (2 ^ 3))ˣ,
    (X : ZMod (2 ^ 3)) + (Y : ZMod (2 ^ 3)) = 0 →
      omgOf (X : ZMod (2 ^ 3)) + omgOf (Y : ZMod (2 ^ 3)) = 0 := by
  decide

theorem pow_two_zmod_eight_zero (m : ℕ) (hm : 3 ≤ m) : (2 : ZMod (2 ^ 3)) ^ m = 0 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hm
  rw [pow_add]
  rw [show (2 : ZMod (2 ^ 3)) ^ 3 = 0 from by decide, zero_mul]

/-! ## The trichotomy of the `2`-adic valuations of `a` and `b` -/

theorem padicValInt_two_ge_one {z : ℤ} (hz : z ≠ 0) (h : (2 : ℤ) ∣ z) :
    1 ≤ padicValInt 2 z := by
  rw [padicValInt]
  have h1 : z.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hz
  have h2 : 2 ∣ z.natAbs := by
    have hz' : (2 : ℤ) ∣ (z.natAbs : ℤ) := by rwa [Int.dvd_natAbs]
    exact_mod_cast hz'
  by_contra hlt
  have h0 : padicValNat 2 z.natAbs = 0 := by omega
  rcases (padicValNat.eq_zero_iff.mp h0) with h' | h' | h'
  · exact absurd h' (by norm_num)
  · exact h1 h'
  · exact h' h2

/-- The identity `1 + q = (q.den + q.num) / q.den` for a rational `q`. -/
theorem one_add_rat_unit (q : ℚˣ) :
    (1 : ℚ) + (q : ℚ)
      = ((((q : ℚ).den : ℤ) + (q : ℚ).num : ℤ) : ℚ) / (((q : ℚ).den : ℤ) : ℚ) := by
  have hm : (q : ℚ) * ((q : ℚ).den : ℚ) = ((q : ℚ).num : ℚ) := Rat.mul_den_eq_num (q : ℚ)
  have hd : (((q : ℚ).den : ℤ) : ℚ) ≠ 0 := by exact_mod_cast (q : ℚ).den_nz
  rw [eq_div_iff hd]
  push_cast
  rw [add_mul, one_mul, hm]

/-- For a nonzero rational `q` with `v₂(q) = 0`, the valuation of `1 + q` is
`v₂(q.den + q.num) - v₂(q.den)`, provided `1 + q ≠ 0`. -/
theorem padicValRat_one_add_unit (q : ℚˣ) (hq : (1 : ℚ) + (q : ℚ) ≠ 0) :
    padicValRat 2 (1 + (q : ℚ))
      = (padicValInt 2 (((q : ℚ).den : ℤ) + (q : ℚ).num) : ℤ)
        - (padicValNat 2 (q : ℚ).den : ℤ) := by
  have hnum_ne : ((((q : ℚ).den : ℤ) + (q : ℚ).num : ℤ) : ℚ) ≠ 0 := by
    intro h0
    exact hq (by rw [one_add_rat_unit q, h0]; simp)
  have hd : (((q : ℚ).den : ℤ) : ℚ) ≠ 0 := by exact_mod_cast (q : ℚ).den_nz
  rw [one_add_rat_unit q, padicValRat.div hnum_ne hd]
  simp only [Int.cast_natCast, padicValRat.of_int, padicValRat.of_nat]

/-- If `a + b = 1` then either `v₂(a) = 0 < v₂(b)`, or `v₂(b) = 0 < v₂(a)`, or
`v₂(a) = v₂(b) < 0`. -/
theorem padicVal_two_trichotomy {a b : ℚˣ} (h : (a : ℚ) + (b : ℚ) = 1) :
    (padicVal 2 a = 0 ∧ 0 < padicVal 2 b) ∨
    (padicVal 2 b = 0 ∧ 0 < padicVal 2 a) ∨
    (padicVal 2 a = padicVal 2 b ∧ padicVal 2 a < 0) := by
  by_cases hne : padicVal 2 a = padicVal 2 b
  · -- equal valuations: they are negative
    right; right
    refine ⟨hne, ?_⟩
    have hq0 : (b : ℚ) / (a : ℚ) ≠ 0 := div_ne_zero b.ne_zero a.ne_zero
    set q : ℚˣ := ratUnit ((b : ℚ) / (a : ℚ)) hq0 with hqdef
    have hqval : padicVal 2 q = 0 := by
      have hval : padicValRat 2 (q : ℚ) = 0 := by
        rw [ratUnit_coe, padicValRat.div b.ne_zero a.ne_zero]
        have hne' : padicValRat 2 (a : ℚ) = padicValRat 2 (b : ℚ) := by
          simpa only [padicVal] using hne
        linarith
      simpa only [padicVal] using hval
    have hqnd := (padicVal_eq_zero_iff (p := 2) q).mp hqval
    have hone : (1 : ℚ) + (q : ℚ) = (a : ℚ)⁻¹ := by
      rw [ratUnit_coe]
      field_simp
      linarith
    have hone_ne : (1 : ℚ) + (q : ℚ) ≠ 0 := by rw [hone]; exact inv_ne_zero a.ne_zero
    have hval1 : padicValRat 2 (1 + (q : ℚ)) = -padicVal 2 a := by
      rw [hone, padicValRat.inv]
      simp only [padicVal]
    have hodd_num : Odd (q : ℚ).num :=
      Int.not_even_iff_odd.mp fun he => hqnd.1 (even_iff_two_dvd.mp he)
    have hden_ndvd_int : ¬ (2 : ℤ) ∣ ((q : ℚ).den : ℤ) := by
      intro hd; exact hqnd.2 (by exact_mod_cast hd)
    have hodd_den : Odd (((q : ℚ).den : ℤ)) :=
      Int.not_even_iff_odd.mp fun he => hden_ndvd_int (even_iff_two_dvd.mp he)
    have hnum_ne : (((q : ℚ).den : ℤ) + (q : ℚ).num) ≠ 0 := by
      intro h0
      refine hone_ne ?_
      rw [one_add_rat_unit q, h0]; simp
    have hnum_ge : 1 ≤ padicValInt 2 (((q : ℚ).den : ℤ) + (q : ℚ).num) :=
      padicValInt_two_ge_one hnum_ne
        (even_iff_two_dvd.mp (Odd.add_odd hodd_den hodd_num))
    have hval2 := padicValRat_one_add_unit q hone_ne
    have hden_zero : (padicValNat 2 (q : ℚ).den : ℤ) = 0 := by
      rw [padicValNat.eq_zero_of_not_dvd hqnd.2]; simp
    have hneg : 1 ≤ -padicVal 2 a := by
      rw [← hval1, hval2, hden_zero]; simpa using hnum_ge
    linarith
  · -- unequal valuations: use additivity of `v₂`
    have hmin := padicValRat.add_eq_min (p := 2) (q := (a : ℚ)) (r := (b : ℚ))
      (by rw [h]; norm_num) a.ne_zero b.ne_zero (by simpa only [padicVal] using hne)
    rw [h, padicValRat.one] at hmin
    change (0 : ℤ) = min (padicVal 2 a) (padicVal 2 b) at hmin
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · left
      have hmin' : min (padicVal 2 a) (padicVal 2 b) = padicVal 2 a := min_eq_left hlt.le
      rw [hmin'] at hmin
      exact ⟨hmin.symm, by omega⟩
    · right; left
      have hmin' : min (padicVal 2 a) (padicVal 2 b) = padicVal 2 b := min_eq_right hgt.le
      rw [hmin'] at hmin
      exact ⟨hmin.symm, by omega⟩

/-! ## The main theorem -/

theorem hilbertSymbolTwo_add_eq_one {a b : ℚˣ} (h : (a : ℚ) + (b : ℚ) = 1) :
    hilbertSymbolTwo a b = 1 := by
  have htwo : (2 : ℚ_[2]) ≠ 0 := by norm_num
  -- the image in `ℚ₂` of the relation `a + b = 1`
  have hrel : (2 : ℚ_[2]) ^ (padicVal 2 a) * ((unitPart 2 a : ℤ_[2]) : ℚ_[2])
      + (2 : ℚ_[2]) ^ (padicVal 2 b) * ((unitPart 2 b : ℤ_[2]) : ℚ_[2]) = 1 := by
    have ha : (2 : ℚ_[2]) ^ (padicVal 2 a) * ((unitPart 2 a : ℤ_[2]) : ℚ_[2])
        = (a : ℚ_[2]) := by
      rw [unitPart_coe, unitVal]
      simp only [Nat.cast_ofNat]
      rw [← mul_assoc, ← zpow_add₀ htwo, add_neg_cancel, zpow_zero, one_mul]
    have hb : (2 : ℚ_[2]) ^ (padicVal 2 b) * ((unitPart 2 b : ℤ_[2]) : ℚ_[2])
        = (b : ℚ_[2]) := by
      rw [unitPart_coe, unitVal]
      simp only [Nat.cast_ofNat]
      rw [← mul_assoc, ← zpow_add₀ htwo, add_neg_cancel, zpow_zero, one_mul]
    rw [ha, hb, ← Rat.cast_add, h, Rat.cast_one]
  rcases padicVal_two_trichotomy h with ⟨hα, hβ⟩ | ⟨hβ, hα⟩ | ⟨heq, hlt⟩
  · -- case `α = 0 < β`
    obtain ⟨m, hm⟩ : ∃ m : ℕ, (m : ℤ) = padicVal 2 b :=
      ⟨(padicVal 2 b).toNat, Int.toNat_of_nonneg hβ.le⟩
    have hm1 : 1 ≤ m := by
      have : (0 : ℤ) < (m : ℤ) := by rw [hm]; exact hβ
      omega
    have hrelI : ((unitPart 2 a : ℤ_[2]) : ℚ_[2])
        + (2 : ℚ_[2]) ^ m * ((unitPart 2 b : ℤ_[2]) : ℚ_[2]) = 1 := by
      have hh := hrel
      rw [hα, ← hm] at hh
      simpa using hh
    have hzI : (unitPart 2 a : ℤ_[2]) + (2 : ℤ_[2]) ^ m * (unitPart 2 b : ℤ_[2]) = 1 := by
      apply PadicInt.ext; push_cast; exact hrelI
    have hZI : (toZ8u (unitPart 2 a) : ZMod (2 ^ 3))
        + (2 : ZMod (2 ^ 3)) ^ m * (toZ8u (unitPart 2 b) : ZMod (2 ^ 3)) = 1 := by
      have hh := congrArg (PadicInt.toZModPow 3) hzI
      simp only [map_add, map_mul, map_pow, map_one, map_ofNat] at hh
      rw [toZ8u_coe, toZ8u_coe]
      exact hh
    have hcoef : (padicVal 2 b : ZMod 2) = (m : ZMod 2) := by rw [← hm]; simp
    have hexp : epsZ (unitPart 2 a) * epsZ (unitPart 2 b)
        + (padicVal 2 a : ZMod 2) * omegaZ (unitPart 2 b)
        + (padicVal 2 b : ZMod 2) * omegaZ (unitPart 2 a) = 0 := by
      rw [epsZ_eq_epsOf, epsZ_eq_epsOf, omegaZ_eq_omgOf, omegaZ_eq_omgOf, hα, hcoef]
      simp only [Int.cast_zero, zero_mul, add_zero]
      rcases Nat.eq_or_lt_of_le hm1 with h1 | h1
      · have hm1' : m = 1 := h1.symm
        subst hm1'
        have hrel1 : (toZ8u (unitPart 2 a) : ZMod (2 ^ 3))
            + 2 * (toZ8u (unitPart 2 b) : ZMod (2 ^ 3)) = 1 := by simpa using hZI
        simpa using check_beta_one _ _ hrel1
      · rcases Nat.eq_or_lt_of_le (by omega : 2 ≤ m) with h2 | h2
        · have hm2' : m = 2 := h2.symm
          subst hm2'
          have hrel2 : (toZ8u (unitPart 2 a) : ZMod (2 ^ 3))
              + 4 * (toZ8u (unitPart 2 b) : ZMod (2 ^ 3)) = 1 := by
            have hh := hZI
            rw [show (2 : ZMod (2 ^ 3)) ^ 2 = 4 from by decide] at hh
            exact hh
          have hchk := check_beta_two _ _ hrel2
          have h2z : ((2 : ℕ) : ZMod 2) = 0 := by decide
          simpa only [h2z, zero_mul, add_zero] using hchk
        · have hm3 : 3 ≤ m := by omega
          have hX1 : (toZ8u (unitPart 2 a) : ZMod (2 ^ 3)) = 1 := by
            have hh := hZI
            rw [pow_two_zmod_eight_zero m hm3, zero_mul, add_zero] at hh
            exact hh
          have he : epsOf (1 : ZMod (2 ^ 3)) = 0 := by decide
          have ho : omgOf (1 : ZMod (2 ^ 3)) = 0 := by decide
          rw [hX1, he, ho]; simp
    rw [hilbertSymbolTwo, hexp, signOf_zero]
  · -- case `β = 0 < α`
    obtain ⟨m, hm⟩ : ∃ m : ℕ, (m : ℤ) = padicVal 2 a :=
      ⟨(padicVal 2 a).toNat, Int.toNat_of_nonneg hα.le⟩
    have hm1 : 1 ≤ m := by
      have : (0 : ℤ) < (m : ℤ) := by rw [hm]; exact hα
      omega
    have hrelII : (2 : ℚ_[2]) ^ m * ((unitPart 2 a : ℤ_[2]) : ℚ_[2])
        + ((unitPart 2 b : ℤ_[2]) : ℚ_[2]) = 1 := by
      have hh := hrel
      rw [hβ, ← hm] at hh
      simpa using hh
    have hzII : (2 : ℤ_[2]) ^ m * (unitPart 2 a : ℤ_[2]) + (unitPart 2 b : ℤ_[2]) = 1 := by
      apply PadicInt.ext; push_cast; exact hrelII
    have hZII : (2 : ZMod (2 ^ 3)) ^ m * (toZ8u (unitPart 2 a) : ZMod (2 ^ 3))
        + (toZ8u (unitPart 2 b) : ZMod (2 ^ 3)) = 1 := by
      have hh := congrArg (PadicInt.toZModPow 3) hzII
      simp only [map_add, map_mul, map_pow, map_one, map_ofNat] at hh
      rw [toZ8u_coe, toZ8u_coe]
      exact hh
    have hcoef : (padicVal 2 a : ZMod 2) = (m : ZMod 2) := by rw [← hm]; simp
    have hexp : epsZ (unitPart 2 a) * epsZ (unitPart 2 b)
        + (padicVal 2 a : ZMod 2) * omegaZ (unitPart 2 b)
        + (padicVal 2 b : ZMod 2) * omegaZ (unitPart 2 a) = 0 := by
      rw [epsZ_eq_epsOf, epsZ_eq_epsOf, omegaZ_eq_omgOf, omegaZ_eq_omgOf, hβ, hcoef]
      simp only [Int.cast_zero, zero_mul, add_zero]
      rcases Nat.eq_or_lt_of_le hm1 with h1 | h1
      · have hm1' : m = 1 := h1.symm
        subst hm1'
        have hrel1 : 2 * (toZ8u (unitPart 2 a) : ZMod (2 ^ 3))
            + (toZ8u (unitPart 2 b) : ZMod (2 ^ 3)) = 1 := by simpa using hZII
        simpa using check_alpha_one _ _ hrel1
      · rcases Nat.eq_or_lt_of_le (by omega : 2 ≤ m) with h2 | h2
        · have hm2' : m = 2 := h2.symm
          subst hm2'
          have hrel2 : 4 * (toZ8u (unitPart 2 a) : ZMod (2 ^ 3))
              + (toZ8u (unitPart 2 b) : ZMod (2 ^ 3)) = 1 := by
            have hh := hZII
            rw [show (2 : ZMod (2 ^ 3)) ^ 2 = 4 from by decide] at hh
            exact hh
          have hchk := check_alpha_two _ _ hrel2
          have h2z : ((2 : ℕ) : ZMod 2) = 0 := by decide
          simpa only [h2z, zero_mul, add_zero] using hchk
        · have hm3 : 3 ≤ m := by omega
          have hY1 : (toZ8u (unitPart 2 b) : ZMod (2 ^ 3)) = 1 := by
            have hh := hZII
            rw [pow_two_zmod_eight_zero m hm3, zero_mul, zero_add] at hh
            exact hh
          have he : epsOf (1 : ZMod (2 ^ 3)) = 0 := by decide
          have ho : omgOf (1 : ZMod (2 ^ 3)) = 0 := by decide
          rw [hY1, he, ho]; simp
    rw [hilbertSymbolTwo, hexp, signOf_zero]
  · -- case `α = β = -τ < 0`
    obtain ⟨τ, hτ⟩ : ∃ τ : ℕ, (τ : ℤ) = -(padicVal 2 a) :=
      ⟨(-(padicVal 2 a)).toNat, Int.toNat_of_nonneg (by omega)⟩
    have hτ1 : 1 ≤ τ := by
      have : (0 : ℤ) < (τ : ℤ) := by rw [hτ]; omega
      omega
    have hrelIII : ((unitPart 2 a : ℤ_[2]) : ℚ_[2]) + ((unitPart 2 b : ℤ_[2]) : ℚ_[2])
        = (2 : ℚ_[2]) ^ τ := by
      have hh := hrel
      rw [← heq] at hh
      rw [← mul_add] at hh
      have hh' := congrArg (fun t => (2 : ℚ_[2]) ^ (-(padicVal 2 a)) * t) hh
      rw [← mul_assoc, ← zpow_add₀ htwo, neg_add_cancel, zpow_zero, one_mul, mul_one] at hh'
      rw [← hτ] at hh'
      simpa only [zpow_natCast] using hh'
    have hzIII : (unitPart 2 a : ℤ_[2]) + (unitPart 2 b : ℤ_[2]) = (2 : ℤ_[2]) ^ τ := by
      apply PadicInt.ext; push_cast; exact hrelIII
    have hZIII : (toZ8u (unitPart 2 a) : ZMod (2 ^ 3))
        + (toZ8u (unitPart 2 b) : ZMod (2 ^ 3)) = (2 : ZMod (2 ^ 3)) ^ τ := by
      have hh := congrArg (PadicInt.toZModPow 3) hzIII
      simp only [map_add, map_pow, map_ofNat] at hh
      rw [toZ8u_coe, toZ8u_coe]
      exact hh
    have hcoef : (padicVal 2 a : ZMod 2) = (τ : ZMod 2) := by
      have k : ((τ : ℤ) : ZMod 2) = ((-(padicVal 2 a) : ℤ) : ZMod 2) := by rw [hτ]
      rw [Int.cast_natCast, Int.cast_neg] at k
      rw [k]
      exact (CharTwo.neg_eq (padicVal 2 a : ZMod 2)).symm
    have hcoefb : (padicVal 2 b : ZMod 2) = (τ : ZMod 2) := by
      rw [← heq]; exact hcoef
    have hexp : epsZ (unitPart 2 a) * epsZ (unitPart 2 b)
        + (padicVal 2 a : ZMod 2) * omegaZ (unitPart 2 b)
        + (padicVal 2 b : ZMod 2) * omegaZ (unitPart 2 a) = 0 := by
      rw [epsZ_eq_epsOf, epsZ_eq_epsOf, omegaZ_eq_omgOf, omegaZ_eq_omgOf, hcoef, hcoefb]
      rcases Nat.eq_or_lt_of_le hτ1 with h1 | h1
      · have hτ1' : τ = 1 := h1.symm
        subst hτ1'
        have hrel1 : (toZ8u (unitPart 2 a) : ZMod (2 ^ 3))
            + (toZ8u (unitPart 2 b) : ZMod (2 ^ 3)) = 2 := by simpa using hZIII
        have hchk := check_tau_one _ _ hrel1
        simpa [add_assoc, add_comm, add_left_comm] using hchk
      · rcases Nat.eq_or_lt_of_le (by omega : 2 ≤ τ) with h2 | h2
        · have hτ2' : τ = 2 := h2.symm
          subst hτ2'
          have hrel2 : (toZ8u (unitPart 2 a) : ZMod (2 ^ 3))
              + (toZ8u (unitPart 2 b) : ZMod (2 ^ 3)) = 4 := by
            have hh := hZIII
            rw [show (2 : ZMod (2 ^ 3)) ^ 2 = 4 from by decide] at hh
            exact hh
          have hchk := check_tau_two _ _ hrel2
          have h2z : ((2 : ℕ) : ZMod 2) = 0 := by decide
          simpa only [h2z, zero_mul, add_zero] using hchk
        · have hτ3 : 3 ≤ τ := by omega
          have hrel0 : (toZ8u (unitPart 2 a) : ZMod (2 ^ 3))
              + (toZ8u (unitPart 2 b) : ZMod (2 ^ 3)) = 0 := by
            have hh := hZIII
            rw [pow_two_zmod_eight_zero τ hτ3] at hh
            exact hh
          have he := check_tau_big_eps _ _ hrel0
          have ho := check_tau_big_omg _ _ hrel0
          have hsum : omgOf (toZ8u (unitPart 2 b) : ZMod (2 ^ 3))
              + omgOf (toZ8u (unitPart 2 a) : ZMod (2 ^ 3)) = 0 := by
            rw [add_comm]; exact ho
          rw [he, zero_add, ← mul_add, hsum, mul_zero]
    rw [hilbertSymbolTwo, hexp, signOf_zero]

end Work.HilbertSymbol
