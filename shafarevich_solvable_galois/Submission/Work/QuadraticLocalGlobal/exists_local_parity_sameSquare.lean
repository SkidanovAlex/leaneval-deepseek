import Mathlib.RingTheory.Henselian
import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Submission.Work.QuadraticLocalGlobal.GrunwaldPrelim
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

noncomputable section

open scoped Classical

namespace Work.QuadraticLocalGlobal

open Work.HilbertSymbol

/-- Odd residue characteristic: every unit `u` of `ℤ_[p]` becomes a square after multiplying by
a suitable positive integer `n` coprime to `p`; explicitly `n` is the representative in
`{0, …, p-1}` of the residue class of `u` in `ZMod p`.  The reduction of `u * n` mod `p` is the
square of the reduction of `u`, so Hensel's lemma (`isSquare_padicInt_of_norm_one`) applies. -/
private theorem exists_nat_coprime_mul_isSquare_odd {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (u : ℤ_[p]ˣ) : ∃ n : ℕ, n ≠ 0 ∧ n.Coprime p ∧ IsSquare ((u : ℤ_[p]) * (n : ℤ_[p])) := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  set n : ℕ := (PadicInt.toZMod (p := p) (u : ℤ_[p])).val with hn
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
  exact ⟨n, hn0, hcop', by rw [← hWcoe]; exact ⟨zw, hzw⟩⟩

/-- Residue characteristic `2`: every unit `u` of `ℤ_[2]` becomes a square after multiplying by a
suitable odd positive integer `n`; explicitly `n` represents the inverse in `(ZMod 8)ˣ` of the
residue class of `u`, so that `u * n ≡ 1 (mod 8)` and Hensel's lemma in the form
`isSquare_padicInt_two_unit_iff` applies. -/
private theorem exists_nat_coprime_mul_isSquare_two (u : ℤ_[2]ˣ) :
    ∃ n : ℕ, n ≠ 0 ∧ n.Coprime 2 ∧ IsSquare ((u : ℤ_[2]) * (n : ℤ_[2])) := by
  haveI : Fact (1 < 2 ^ 3) := ⟨by norm_num⟩
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
  exact ⟨n, hn0, hcop2.symm, by rw [← hWcoe]; exact ⟨zw, hzw⟩⟩

/-- Local reduction of an arbitrary nonzero `p`-adic number to the normal form `p ^ e * n` with
`e ≤ 1` and `n` a positive integer coprime to `p`.

Write `c = p ^ V * u` with `u = padicUnitOf p c hc` and `V = c.valuation`.  Then
`e := (if Even V then 0 else 1)`, and `n` is any positive integer whose residue mod `p`
(resp. mod `8` when `p = 2`) represents the square class of `u`: `n := (PadicInt.toZMod u).val`
for odd `p` and `n := ((PadicInt.toZModPow 3 u)⁻¹).val` for `p = 2`.  Then `u * n` is a square in
`ℤ_[p]` (Hensel: `isSquare_padicInt_of_norm_one` / `isSquare_padicInt_two_unit_iff`), and
`c / (p ^ e * n) = p ^ (V - e) * (u / n)` is a product of two squares. -/
theorem exists_local_parity_sameSquare {p : ℕ} [Fact p.Prime] (c : (ℚ_[p])ˣ) :
    ∃ (e : ℕ) (n : ℕ), e ≤ 1 ∧ n ≠ 0 ∧ n.Coprime p ∧
      Work.QuadraticLocalGlobal.SameSquare ((p : ℚ_[p]) ^ e * (n : ℚ_[p]))
        ((c : (ℚ_[p])ˣ) : ℚ_[p]) := by
  set x : ℚ_[p] := ((c : (ℚ_[p])ˣ) : ℚ_[p]) with hxdef
  have hx : x ≠ 0 := by rw [hxdef]; exact Units.ne_zero c
  set V : ℤ := x.valuation with hV
  set u : ℤ_[p]ˣ := padicUnitOf p x hx with hu
  have hxu : x = (p : ℚ_[p]) ^ V * (u : ℚ_[p]) := by
    rw [hu, hV]; exact padic_eq_pow_valuation_mul_unit x hx
  set e : ℕ := if Even V then 0 else 1 with he
  have he1 : e ≤ 1 := by rw [he]; split <;> omega
  have hEeven : Even (V - (e : ℤ)) := by
    rw [he]
    by_cases hV' : Even V
    · simp [hV']
    · simp [hV']
      exact Int.not_even_iff_odd.mp hV'
  obtain ⟨m, hm⟩ := hEeven
  obtain ⟨n, zw, hn0, hncop, hzw⟩ : ∃ (n : ℕ) (zw : ℤ_[p]), n ≠ 0 ∧ n.Coprime p ∧
      (u : ℤ_[p]) * (n : ℤ_[p]) = zw * zw := by
    by_cases hp2 : p = 2
    · subst hp2
      obtain ⟨n, hn0, hnc, hisq⟩ := exists_nat_coprime_mul_isSquare_two u
      obtain ⟨zw, hzw⟩ := hisq
      exact ⟨n, zw, hn0, hnc, hzw⟩
    · obtain ⟨n, hn0, hnc, hisq⟩ := exists_nat_coprime_mul_isSquare_odd hp2 u
      obtain ⟨zw, hzw⟩ := hisq
      exact ⟨n, zw, hn0, hnc, hzw⟩
  refine ⟨e, n, he1, hn0, hncop, ?_⟩
  have hP : (p : ℚ_[p]) ≠ 0 := p_cast_ne_zero p
  have hN : ((n : ℕ) : ℚ_[p]) ≠ 0 := by exact_mod_cast hn0
  have hPe : (p : ℚ_[p]) ^ e = (p : ℚ_[p]) ^ ((e : ℤ)) := (zpow_natCast _ e).symm
  have hzwq : (zw : ℚ_[p]) * (zw : ℚ_[p]) = (u : ℚ_[p]) * ((n : ℕ) : ℚ_[p]) := by
    have h := congrArg (fun w : ℤ_[p] => (w : ℚ_[p])) hzw.symm
    push_cast at h ⊢
    exact h
  refine ⟨(p : ℚ_[p]) ^ m * (zw : ℚ_[p]) / ((n : ℕ) : ℚ_[p]), ?_⟩
  rw [hPe]
  have hmain : ((p : ℚ_[p]) ^ m * (zw : ℚ_[p]) / ((n : ℕ) : ℚ_[p])) ^ 2 *
      ((p : ℚ_[p]) ^ ((e : ℤ)) * ((n : ℕ) : ℚ_[p])) = (p : ℚ_[p]) ^ V * (u : ℚ_[p]) := by
    have hsqm : ((p : ℚ_[p]) ^ m) * ((p : ℚ_[p]) ^ m) =
        (p : ℚ_[p]) ^ (V - (e : ℤ)) := by
      rw [← zpow_add₀ hP m m, ← hm]
    have step1 : ((p : ℚ_[p]) ^ m * (zw : ℚ_[p]) / ((n : ℕ) : ℚ_[p])) ^ 2 *
        ((p : ℚ_[p]) ^ ((e : ℤ)) * ((n : ℕ) : ℚ_[p])) =
        ((p : ℚ_[p]) ^ m) * ((p : ℚ_[p]) ^ m) * ((zw : ℚ_[p]) * (zw : ℚ_[p])) /
          (((n : ℕ) : ℚ_[p]) * ((n : ℕ) : ℚ_[p])) *
            ((p : ℚ_[p]) ^ ((e : ℤ)) * ((n : ℕ) : ℚ_[p])) := by
      field_simp
    rw [step1, hsqm, hzwq]
    field_simp
    rw [← zpow_add₀ hP (V - (e : ℤ)) (e : ℤ), show V - (e : ℤ) + (e : ℤ) = V by ring]
  exact hmain.trans hxu.symm

end Work.QuadraticLocalGlobal
