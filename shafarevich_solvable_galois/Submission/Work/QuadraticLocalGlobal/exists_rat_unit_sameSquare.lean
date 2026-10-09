import Mathlib
import Submission.Work.QuadraticLocalGlobal.Defs
import Submission.Work.QuadraticLocalGlobal.isSquare_padic_iff
import Submission.Work.QuadraticLocalGlobal.isSquare_padic_two_iff
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.QuadraticLocalGlobal

open Work.HilbertSymbol

/-- If `c = p ^ v * u` with `u : ℤ_[p]ˣ` a unit and `u * n = zw ^ 2` for some `n : ℕ` and
`zw : ℤ_[p]`, then the rational number `y = p ^ v * n` is a rational unit with
`SameSquare y c`. -/
private theorem exists_rat_unit_sameSquare_of_mul_sq {p : ℕ} [Fact p.Prime] (c : ℚ_[p]) (hc : c ≠ 0)
    (u : ℤ_[p]ˣ) (v : ℤ) (hcu : c = (p : ℚ_[p]) ^ v * (u : ℚ_[p]))
    {n : ℕ} (hn0 : n ≠ 0) (zw : ℤ_[p])
    (hzw : (u : ℤ_[p]) * (n : ℤ_[p]) = zw * zw) :
    ∃ y : ℚˣ, SameSquare ((y : ℚ_[p])) c := by
  have hn : (n : ℚ_[p]) ≠ 0 := by exact_mod_cast hn0
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have hneq : (p : ℚ) ^ v * (n : ℚ) ≠ 0 :=
    mul_ne_zero (zpow_ne_zero v hp0) (by exact_mod_cast hn0)
  refine ⟨ratUnit ((p : ℚ) ^ v * (n : ℚ)) hneq, ?_⟩
  have hy : (((ratUnit ((p : ℚ) ^ v * (n : ℚ)) hneq : ℚˣ)) : ℚ_[p]) =
      (p : ℚ_[p]) ^ v * (n : ℚ_[p]) := by
    change (((p : ℚ) ^ v * (n : ℚ) : ℚ) : ℚ_[p]) = _
    push_cast
    ring
  have hzwQ : (zw : ℚ_[p]) * (zw : ℚ_[p]) = (u : ℚ_[p]) * (n : ℚ_[p]) := by
    have h2 := congrArg (fun z : ℤ_[p] => (z : ℚ_[p])) hzw.symm
    push_cast at h2
    exact h2
  have hzsq : ((zw : ℚ_[p]) / (n : ℚ_[p])) ^ 2 = (u : ℚ_[p]) / (n : ℚ_[p]) := by
    rw [sq, div_mul_div_comm, hzwQ]
    field_simp
  refine ⟨(zw : ℚ_[p]) / (n : ℚ_[p]), ?_⟩
  rw [hy, hcu, hzsq]
  field_simp

theorem exists_rat_unit_sameSquare {p : ℕ} [Fact p.Prime] (c : ℚ_[p]) (hc : c ≠ 0) : ∃ y : ℚˣ, Work.QuadraticLocalGlobal.SameSquare ((y : ℚ_[p])) c := by
  by_cases hp2 : p = 2
  · subst hp2
    haveI : Fact (1 < 2 ^ 3) := ⟨by norm_num⟩
    set u : ℤ_[2]ˣ := padicUnitOf 2 c hc with hu
    have hcu : c = (2 : ℚ_[2]) ^ c.valuation * (u : ℚ_[2]) := by
      rw [hu]; exact padic_eq_pow_valuation_mul_unit c hc
    let f : ℤ_[2] →* ZMod (2 ^ 3) := (PadicInt.toZModPow (p := 2) 3)
    set n : ℕ := ((((Units.map f u)⁻¹ : (ZMod (2 ^ 3))ˣ) : ZMod (2 ^ 3))).val with hn
    have hnu : (n : ZMod (2 ^ 3)) =
        (((Units.map f u)⁻¹ : (ZMod (2 ^ 3))ˣ) : ZMod (2 ^ 3)) := by
      rw [hn]; exact ZMod.natCast_zmod_val _
    have hnunit : IsUnit ((n : ℕ) : ZMod (2 ^ 3)) := by
      rw [hnu]; exact Units.isUnit _
    have hcop8 : n.Coprime (2 ^ 3) := (ZMod.isUnit_iff_coprime n (2 ^ 3)).mp hnunit
    have hcop2 : (2 : ℕ).Coprime n := (hcop8.coprime_dvd_right (by norm_num : 2 ∣ 2 ^ 3)).symm
    have hn0 : n ≠ 0 := by
      intro h; rw [h] at hcop2; exact absurd hcop2 (by norm_num)
    have hunitZ : IsUnit ((n : ℕ) : ℤ_[2]) :=
      (PadicInt.isUnit_iff).mpr ((PadicInt.norm_natCast_eq_one_iff).mpr hcop2)
    set nn : ℤ_[2]ˣ := hunitZ.unit with hnn
    have hnn_coe : (nn : ℤ_[2]) = (n : ℤ_[2]) := by rw [hnn]; exact hunitZ.unit_spec
    set W : ℤ_[2]ˣ := u * nn with hW
    have hWcoe : (W : ℤ_[2]) = (u : ℤ_[2]) * (n : ℤ_[2]) := by
      rw [hW, Units.val_mul, hnn_coe]
    have hW1 : PadicInt.toZModPow 3 (W : ℤ_[2]) = 1 := by
      have h1 : PadicInt.toZModPow 3 (W : ℤ_[2]) = f (u : ℤ_[2]) * (n : ZMod (2 ^ 3)) := by
        rw [hWcoe, map_mul, map_natCast]; rfl
      have hb : f (u : ℤ_[2]) *
          (((Units.map f u)⁻¹ : (ZMod (2 ^ 3))ˣ) : ZMod (2 ^ 3)) = 1 := by
        rw [← Units.coe_map f u]
        exact Units.mul_inv (Units.map f u)
      rw [h1, hnu, hb]
    have hIsSq : IsSquare (W : ℤ_[2]) := (isSquare_padicInt_two_unit_iff W).mpr hW1
    obtain ⟨zw, hzw⟩ := hIsSq
    exact exists_rat_unit_sameSquare_of_mul_sq c hc u c.valuation hcu hn0 zw
      (by rw [← hWcoe]; exact hzw)
  · haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
    set u : ℤ_[p]ˣ := padicUnitOf p c hc with hu
    have hcu : c = (p : ℚ_[p]) ^ c.valuation * (u : ℚ_[p]) := by
      rw [hu]; exact padic_eq_pow_valuation_mul_unit c hc
    set n : ℕ := (PadicInt.toZMod (u : ℤ_[p])).val with hn
    have hnu : (n : ZMod p) = PadicInt.toZMod (u : ℤ_[p]) := by
      rw [hn]; exact ZMod.natCast_zmod_val _
    have hu_ne : PadicInt.toZMod (u : ℤ_[p]) ≠ 0 :=
      (IsUnit.map (PadicInt.toZMod) u.isUnit).ne_zero
    have hn0 : n ≠ 0 := by
      intro h; apply hu_ne; rw [← hnu, h]; simp
    have hnunit : IsUnit ((n : ℕ) : ZMod p) := by
      rw [hnu]; exact IsUnit.map (PadicInt.toZMod) u.isUnit
    have hcop' : n.Coprime p := (ZMod.isUnit_iff_coprime n p).mp hnunit
    have hcop : p.Coprime n := hcop'.symm
    have hunitZ : IsUnit ((n : ℕ) : ℤ_[p]) :=
      (PadicInt.isUnit_iff).mpr ((PadicInt.norm_natCast_eq_one_iff).mpr hcop)
    set nn : ℤ_[p]ˣ := hunitZ.unit with hnn
    have hnn_coe : (nn : ℤ_[p]) = (n : ℤ_[p]) := by rw [hnn]; exact hunitZ.unit_spec
    set W : ℤ_[p]ˣ := u * nn with hW
    have hWcoe : (W : ℤ_[p]) = (u : ℤ_[p]) * (n : ℤ_[p]) := by
      rw [hW, Units.val_mul, hnn_coe]
    have hWnorm : ‖(W : ℤ_[p])‖ = 1 := PadicInt.norm_units W
    have hWsq : IsSquare (PadicInt.toZMod (W : ℤ_[p])) := by
      have h1 : PadicInt.toZMod (W : ℤ_[p]) =
          PadicInt.toZMod (u : ℤ_[p]) * PadicInt.toZMod (u : ℤ_[p]) := by
        rw [hWcoe, map_mul, map_natCast, hnu]
      rw [h1]; exact ⟨_, rfl⟩
    have hIsSq : IsSquare (W : ℤ_[p]) := (isSquare_padicInt_of_norm_one hp2 hWnorm).mpr hWsq
    obtain ⟨zw, hzw⟩ := hIsSq
    exact exists_rat_unit_sameSquare_of_mul_sq c hc u c.valuation hcu hn0 zw
      (by rw [← hWcoe]; exact hzw)

end Work.QuadraticLocalGlobal
