import Mathlib.GroupTheory.Nilpotent
import Mathlib.NumberTheory.Padics.Hensel
import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.Algebra.Order.Ring.Star
import Submission.Work.QuadraticLocalGlobal.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.QuadraticLocalGlobal

open Work.HilbertSymbol

/-- Every nonzero `p`-adic number is `p ^ valuation` times its unit part. -/
theorem padic_eq_pow_valuation_mul_unit {p : ℕ} [Fact p.Prime] (x : ℚ_[p]) (hx : x ≠ 0) :
    x = (p : ℚ_[p]) ^ x.valuation * ((padicUnitOf p x hx : ℤ_[p]) : ℚ_[p]) := by
  rw [padicUnitOf_coe, ← mul_assoc, ← zpow_add₀ (p_cast_ne_zero p), add_neg_cancel, zpow_zero,
    one_mul]

/-- **Hensel's lemma for square roots of units.** For an odd prime `p`, a `p`-adic integer
of norm `1` is a square if and only if its residue class in `ZMod p` is a square. -/
theorem isSquare_padicInt_of_norm_one {p : ℕ} [Fact p.Prime] (hp : p ≠ 2) {u : ℤ_[p]}
    (hu : ‖u‖ = 1) : IsSquare u ↔ IsSquare (PadicInt.toZMod u) := by
  constructor
  · intro h
    exact IsSquare.map PadicInt.toZMod h
  · intro h
    obtain ⟨ā, hā⟩ := h
    -- lift the residue class of a square root of `toZMod u` to `ℤ_[p]`
    let a₀ : ℤ_[p] := (ā.val : ℤ_[p])
    have hā0 : PadicInt.toZMod a₀ = ā := by
      apply ZMod.val_injective p
      show (PadicInt.toZMod a₀).val = ā.val
      rw [PadicInt.val_toZMod_eq_zmodRepr]
      show ((ā.val : ℕ) : ℤ_[p]).zmodRepr = ā.val
      rw [PadicInt.zmodRepr_natCast, Nat.mod_eq_of_lt (ZMod.val_lt ā)]
    -- `toZMod u ≠ 0` because `u` is a unit
    have huz : PadicInt.toZMod u ≠ 0 := by
      intro hz
      have hmem : u ∈ IsLocalRing.maximalIdeal ℤ_[p] := by
        rw [← PadicInt.ker_toZMod, RingHom.mem_ker]; exact hz
      exact ((IsLocalRing.notMem_maximalIdeal).mpr ((PadicInt.isUnit_iff).mpr hu)) hmem
    have hāne : ā ≠ 0 := by
      rintro rfl
      simp only [mul_zero] at hā
      exact huz hā
    -- `2 ≠ 0` in `ZMod p` since `p` is odd
    have h2ne : (2 : ZMod p) ≠ 0 := by
      intro h2
      have hdvd : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp h2
      have h2le : p ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd
      have hp2le : 2 ≤ p := (Fact.out : p.Prime).two_le
      omega
    -- `a₀ ^ 2 - u` lies in the maximal ideal
    have hker : a₀ ^ 2 - u ∈ IsLocalRing.maximalIdeal ℤ_[p] := by
      rw [← PadicInt.ker_toZMod, RingHom.mem_ker, map_sub, map_pow, hā0, hā]
      ring
    have hlt : ‖a₀ ^ 2 - u‖ < 1 := by
      rw [← PadicInt.mem_nonunits, ← IsLocalRing.mem_maximalIdeal]
      exact hker
    -- and `2 * a₀` is a unit, so `‖2 * a₀‖ = 1`
    have h2a : (2 : ℤ_[p]) * a₀ ∉ IsLocalRing.maximalIdeal ℤ_[p] := by
      rw [← PadicInt.ker_toZMod, RingHom.mem_ker, map_mul, hā0, map_ofNat]
      exact mul_ne_zero h2ne hāne
    have h2a1 : ‖(2 : ℤ_[p]) * a₀‖ = 1 :=
      (PadicInt.isUnit_iff).mp ((IsLocalRing.notMem_maximalIdeal).mp h2a)
    have hpoly : (Polynomial.aeval a₀) (Polynomial.X ^ 2 - Polynomial.C u) = a₀ ^ 2 - u := by
      simp
    have hd : (Polynomial.aeval a₀) (Polynomial.derivative (Polynomial.X ^ 2 - Polynomial.C u)) =
        2 * a₀ := by
      rw [Polynomial.derivative_sub, Polynomial.derivative_X_pow, Polynomial.derivative_C]
      simp
    have h2a1sq : ‖(2 : ℤ_[p]) * a₀‖ ^ 2 = 1 := by rw [h2a1]; norm_num
    have hHens : ‖(Polynomial.aeval a₀) (Polynomial.X ^ 2 - Polynomial.C u)‖ <
        ‖(Polynomial.aeval a₀) (Polynomial.derivative (Polynomial.X ^ 2 - Polynomial.C u))‖ ^ 2 := by
      rw [hpoly, hd, h2a1sq]; exact hlt
    obtain ⟨z, hz, -, -, -⟩ := hensels_lemma hHens
    have hz' : z ^ 2 = u := by
      have : z ^ 2 - u = 0 := by simpa using hz
      exact sub_eq_zero.mp this
    exact ⟨z, by rw [← hz', sq]⟩

/-- **Squares in `ℚ_[p]` for odd `p`.** A nonzero `p`-adic number is a square if and only if
its valuation is even and the residue class of its unit part is a square in `ZMod p`. -/
theorem isSquare_padic_iff {p : ℕ} [Fact p.Prime] (hp : p ≠ 2) {x : ℚ_[p]} (hx : x ≠ 0) :
    IsSquare x ↔ Even (x.valuation) ∧ IsSquare (PadicInt.toZMod (p := p) (Work.QuadraticLocalGlobal.padicUnitOf p x hx : ℤ_[p])) := by
  constructor
  · rintro ⟨y, hy⟩
    have hy0 : y ≠ 0 := by rintro rfl; rw [mul_zero] at hy; exact hx hy
    have hval : x.valuation = y.valuation + y.valuation := by
      rw [hy, Padic.valuation_mul hy0 hy0]
    refine ⟨⟨y.valuation, hval⟩, ?_⟩
    -- the unit part of `x` is the square of the unit part of `y`
    have hcoe : ((padicUnitOf p x hx : ℤ_[p]) : ℚ_[p]) =
        ((padicUnitOf p y hy0 : ℤ_[p]) : ℚ_[p]) * ((padicUnitOf p y hy0 : ℤ_[p]) : ℚ_[p]) := by
      rw [padicUnitOf_coe, padicUnitOf_coe, hval, hy, neg_add, zpow_add₀ (p_cast_ne_zero p)]
      ring
    have hmul : (padicUnitOf p x hx : ℤ_[p]) =
        (padicUnitOf p y hy0 : ℤ_[p]) * (padicUnitOf p y hy0 : ℤ_[p]) :=
      PadicInt.ext (by rw [PadicInt.coe_mul]; exact hcoe)
    exact ⟨PadicInt.toZMod (padicUnitOf p y hy0 : ℤ_[p]), by rw [hmul, map_mul]⟩
  · rintro ⟨hv, hs⟩
    obtain ⟨k, hk⟩ := hv
    have hu : IsSquare ((padicUnitOf p x hx : ℤ_[p])) :=
      (isSquare_padicInt_of_norm_one hp (PadicInt.norm_units _)).mpr hs
    obtain ⟨z, hz⟩ := hu
    refine ⟨(p : ℚ_[p]) ^ k * (z : ℚ_[p]), ?_⟩
    rw [padic_eq_pow_valuation_mul_unit (p := p) x hx, hk, zpow_add₀ (p_cast_ne_zero p),
      show (((padicUnitOf p x hx : ℤ_[p])) : ℚ_[p]) = (z : ℚ_[p]) * (z : ℚ_[p]) by
        rw [hz, PadicInt.coe_mul]]
    ring

end Work.QuadraticLocalGlobal
