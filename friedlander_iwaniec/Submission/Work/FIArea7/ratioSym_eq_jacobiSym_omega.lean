import Mathlib
import Submission.Work.FIArea7.ReSymbolTwist
import Submission.Work.FIArea7.FIsymbols

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.FIArea7

/-- ***FI* (17.9) arithmetic core at the round-6 ratio symbol: the symbol of a modulus
`e ∣ q` on a pair that is congruent modulo `q` is the symbol of the *class*.**

Let `q, e : ℕ` with `e ∣ q`, `z₁, z₂ : ℤ[i]` and `ω₀ : ZMod q` a *unit* such that `ω₀` is the
unique class with `z₁ ≡ ω₀ z₂ (mod q)` (componentwise, in `ZMod q`), and `(|z₂|², q) = 1`.  Then
the ratio symbol of the small modulus `e` is the Jacobi symbol of the class:

  `ratioSym z₁ z₂ e = (ω₀ | e)`,   i.e.  `(z₂/z₁ | e) = (ω₀|e)`.

This is what makes (17.9) run: after `WBcutExpanded6` has been rewritten into the `ω`-form by
the congruence detection `dvd_delta_iff_exists_omega` / `existsUnique_omega_of_dvd_delta`, the
only symbol left on the `e ≤ X` side is `(ω|e)` — the character of (17.10).

Mathematically: `e ∣ q` and `z₁ ≡ ω₀ z₂ (mod q)` give `z₁ ≡ ω₀ z₂ (mod e)`, hence both
`Re(z̄₁z₂) ≡ ω₀|z₂|²` and `|z₁|² ≡ ω₀²|z₂|² (mod e)`, so the rational residue `z₂/z₁` is
`ω₀⁻¹ (mod e)`; and `(ω₀⁻¹|e) = (ω₀|e)` because both are `±1` (`hunit` makes `ω₀` a unit modulo
`e` as well, and `hc` makes `|z₂|²` one). -/
theorem ratioSym_eq_jacobiSym_omega {q : ℕ} [NeZero q] {e : ℕ} [NeZero e] (he : e ∣ q)
    {z1 z2 : GaussianInt} {ω₀ : ZMod q}
    (hunit : IsUnit ω₀)
    (huniq : ∀ ω : ZMod q, (((z1.re : ZMod q) = ω * (z2.re : ZMod q)) ∧
        ((z1.im : ZMod q) = ω * (z2.im : ZMod q))) ↔ ω = ω₀)
    (hc : Nat.Coprime (Work.FIPlan.gnorm z2) q) :
    Work.FIArea7.ratioSym z1 z2 e = jacobiSym (ω₀.val : ℤ) e := by
  -- the class `ω₀` realises the congruence, by definition
  obtain ⟨hReq, hImq⟩ := (huniq ω₀).mpr rfl
  -- `ω₀` is `((ω₀.val : ℕ))`; its representative modulo `e` is `ω`
  have hωq : ((ω₀.val : ℕ) : ZMod q) = ω₀ := by rw [ZMod.natCast_val, ZMod.cast_id]
  let ω : ZMod e := ((ω₀.val : ℤ) : ZMod e)
  have hphi : ZMod.castHom he (ZMod e) ω₀ = ω := by
    conv_lhs => rw [← hωq]
    rw [ZMod.castHom_apply, ZMod.cast_natCast he]
    exact (Int.cast_natCast (R := ZMod e) ω₀.val).symm
  have hωu : IsUnit ω :=
    hphi ▸ IsUnit.map (ZMod.castHom he (ZMod e)) hunit
  -- reduce the two component congruences modulo `e`
  have hRee : (z1.re : ZMod e) = ω * (z2.re : ZMod e) := by
    have h := congrArg (ZMod.castHom he (ZMod e)) hReq
    rw [map_mul, hphi] at h
    simpa using h
  have hIme : (z1.im : ZMod e) = ω * (z2.im : ZMod e) := by
    have h := congrArg (ZMod.castHom he (ZMod e)) hImq
    rw [map_mul, hphi] at h
    simpa using h
  -- the two norms, in `ZMod e`
  have hG2eq : (((Work.FIPlan.gnorm z2 : ℕ)) : ZMod e)
      = (z2.re : ZMod e) ^ 2 + (z2.im : ZMod e) ^ 2 := by
    rw [← Int.cast_natCast, Work.FIArea7.norm_eq]
    push_cast
    ring
  have hG1eq : (((Work.FIPlan.gnorm z1 : ℕ)) : ZMod e)
      = (z1.re : ZMod e) ^ 2 + (z1.im : ZMod e) ^ 2 := by
    rw [← Int.cast_natCast, Work.FIArea7.norm_eq]
    push_cast
    ring
  -- `Re(z̄₁z₂)` in `ZMod e`
  have hRec : ((star z1 * z2).re : ZMod e)
      = (z1.re : ZMod e) * (z2.re : ZMod e) + (z1.im : ZMod e) * (z2.im : ZMod e) := by
    rw [re_star_mul_coords]
    push_cast
    ring
  have hRecω : ((star z1 * z2).re : ZMod e) = ω * (((Work.FIPlan.gnorm z2 : ℕ)) : ZMod e) := by
    rw [hRec, hRee, hIme, hG2eq]
    ring
  have hG1ω : (((Work.FIPlan.gnorm z1 : ℕ)) : ZMod e)
      = ω ^ 2 * (((Work.FIPlan.gnorm z2 : ℕ)) : ZMod e) := by
    rw [hG1eq, hRee, hIme, hG2eq]
    ring
  -- `|z₂|²` is a unit modulo `e`
  have hcop_e : Nat.Coprime (Work.FIPlan.gnorm z2) e := hc.coprime_dvd_right he
  have hG2u : IsUnit (((Work.FIPlan.gnorm z2 : ℕ)) : ZMod e) :=
    (ZMod.isUnit_iff_coprime (Work.FIPlan.gnorm z2) e).mpr hcop_e
  -- the actual ratio symbol is the inverse of `ω`
  unfold ratioSym
  set X : ZMod e :=
    ((star z1 * z2).re : ZMod e) * (((Work.FIPlan.gnorm z1 : ℕ)) : ZMod e)⁻¹ with hXdef
  have hXω : X * ω = 1 := by
    rw [hXdef, hRecω, hG1ω]
    rw [show (ω * (((Work.FIPlan.gnorm z2 : ℕ)) : ZMod e))
            * (ω ^ 2 * (((Work.FIPlan.gnorm z2 : ℕ)) : ZMod e))⁻¹ * ω
          = (ω ^ 2 * (((Work.FIPlan.gnorm z2 : ℕ)) : ZMod e))
            * (ω ^ 2 * (((Work.FIPlan.gnorm z2 : ℕ)) : ZMod e))⁻¹ by ring]
    exact ZMod.mul_inv_of_unit _ ((hωu.pow 2).mul hG2u)
  have hX : X = ω⁻¹ := by
    calc X = X * 1 := (mul_one X).symm
      _ = X * (ω * ω⁻¹) := by rw [ZMod.mul_inv_of_unit ω hωu]
      _ = (X * ω) * ω⁻¹ := by ring
      _ = 1 * ω⁻¹ := by rw [hXω]
      _ = ω⁻¹ := one_mul _
  have hXval : ((X.val : ℤ) : ZMod e) = X := by
    push_cast
    rw [ZMod.natCast_val]
    simp
  have hprod : ((X.val : ℤ) : ZMod e) * ((ω₀.val : ℤ) : ZMod e) = 1 := by
    rw [hXval]
    exact hXω
  have hcast : (((X.val : ℤ) * (ω₀.val : ℤ) : ℤ) : ZMod e) = ((1 : ℤ) : ZMod e) := by
    rw [Int.cast_mul, Int.cast_one]
    exact hprod
  have hmod : ((X.val : ℤ) * (ω₀.val : ℤ)) % (e : ℤ) = (1 : ℤ) % (e : ℤ) :=
    (ZMod.intCast_eq_intCast_iff' ((X.val : ℤ) * (ω₀.val : ℤ)) 1 e).mp hcast
  have hone : jacobiSym ((X.val : ℤ)) e * jacobiSym ((ω₀.val : ℤ)) e = 1 := by
    rw [← jacobiSym.mul_left, jacobiSym.mod_left' hmod, jacobiSym.one_left]
  have hgX : (X.val : ℤ).gcd (e : ℤ) = 1 := by
    by_contra h
    have h0 : jacobiSym ((X.val : ℤ)) e = 0 := jacobiSym.eq_zero_iff_not_coprime.mpr h
    rw [h0, zero_mul] at hone
    exact one_ne_zero hone.symm
  have hgω : (ω₀.val : ℤ).gcd (e : ℤ) = 1 := by
    by_contra h
    have h0 : jacobiSym ((ω₀.val : ℤ)) e = 0 := jacobiSym.eq_zero_iff_not_coprime.mpr h
    rw [h0, mul_zero] at hone
    exact one_ne_zero hone.symm
  rcases jacobiSym.eq_one_or_neg_one hgX with h1 | h1 <;>
    rcases jacobiSym.eq_one_or_neg_one hgω with h2 | h2
  · simp only [h1, h2]
  · exfalso
    rw [h1, h2] at hone
    norm_num at hone
  · exfalso
    rw [h1, h2] at hone
    norm_num at hone
  · simp only [h1, h2]

end Work.FIArea7
