import Mathlib
import Submission.Work.HilbertSymbol.Basic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.HilbertSymbol

/-- If `a : ℚˣ` is a `p`-adic unit (`v_p a = 0`) with `a ≡ 1 (mod p)` (i.e. `v_p (a - 1) > 0`),
then the Legendre symbol of its `p`-adic unit part is `1`. -/
theorem legendreOf_eq_one_of_padicVal_eq_zero_of_sub_one_pos {p : ℕ} [Fact p.Prime] (a : ℚˣ)
    (ha : padicVal p a = 0) (h : 0 < padicValRat p ((a : ℚ) - 1)) : legendreOf p a = 1 := by
  -- `a - 1 ≠ 0`, since otherwise its valuation would vanish.
  have hne : (a : ℚ) - 1 ≠ 0 := by
    intro h0
    rw [h0, padicValRat.zero] at h
    exact lt_irrefl 0 h
  set x : ℤ_[p] := (unitPart p a : ℤ_[p]) with hxdef
  -- `x` has the same image in `ℚ_[p]` as `a`.
  have hxcoe : (x : ℚ_[p]) = (a : ℚ_[p]) := unitPart_of_padicVal_eq_zero ha
  have hsub : ((x - 1 : ℤ_[p]) : ℚ_[p]) = (((a : ℚ) - 1 : ℚ) : ℚ_[p]) := by
    rw [PadicInt.coe_sub, hxcoe, PadicInt.coe_one]
    norm_cast
  have hx0 : (x - 1) ≠ 0 := by
    rw [← PadicInt.coe_ne_zero, hsub]
    exact Rat.cast_ne_zero.mpr hne
  -- its valuation is that of `a - 1`, hence positive.
  have hv : ((x - 1).valuation : ℤ) = padicValRat p ((a : ℚ) - 1) := by
    rw [← PadicInt.valuation_coe (x - 1), hsub]
    exact Padic.valuation_ratCast _
  have hpos : (1 : ℕ) ≤ (x - 1).valuation := by
    have : (0 : ℤ) < ((x - 1).valuation : ℤ) := by rw [hv]; exact h
    omega
  have hmem : (x - 1) ∈ Ideal.span {(p : ℤ_[p])} := by
    have := (PadicInt.mem_span_pow_iff_le_valuation (x - 1) hx0 1).mpr hpos
    simpa using this
  -- therefore `x` reduces to `1` modulo `p`.
  have htoZ : PadicInt.toZMod (p := p) x = 1 := by
    have hker : PadicInt.toZMod (p := p) (x - 1) = 0 := by
      rw [← RingHom.mem_ker, PadicInt.ker_toZMod, PadicInt.maximalIdeal_eq_span_p]
      exact hmem
    rw [map_sub, map_one] at hker
    exact sub_eq_zero.mp hker
  rw [legendreOf, legendreUnit, quadCharUnit]
  rw [show ((Units.map (PadicInt.toZMod (p := p)) (unitPart p a) : (ZMod p)ˣ) : ZMod p)
        = PadicInt.toZMod (p := p) x from by rw [Units.coe_map]; rfl]
  rw [htoZ, MulChar.map_one]
  exact intUnitOf_one

end Work.HilbertSymbol
