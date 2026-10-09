import Mathlib
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option linter.style.haveILetI false

/-!
# Fixed points of an involution of a finite field are squares

Let `F` be a finite field and `σ` an involutive (`σ² = 1`) nontrivial ring automorphism of `F`.
If `x` is fixed by `σ`, then `x` is a square in `F`.

The mathematical content: in characteristic `2` every element of a finite field is a square
(the Frobenius `y ↦ y²` is a bijection).  In odd characteristic the fixed field `F^σ` is a
subfield over which `F` has degree `2` (the anti-invariant element `t = a - σ a` together with
`1` spans `F`); hence `|F| = |F^σ|²`.  For `x ∈ F^σ` nonzero, Fermat in `F^σ` gives
`x ^ (|F^σ| - 1) = 1`, so `x ^ (|F| / 2) = (x ^ (|F^σ| - 1)) ^ ((|F^σ| + 1) / 2) = 1`, and
Euler's criterion (`FiniteField.isSquare_iff`) finishes.
-/

namespace Work.SSGRoute.NodeS37

open scoped Classical

/-- The fixed field of a ring automorphism `σ`, as a `Subfield`. -/
def fixedSubfield {F : Type*} [Field F] (σ : F ≃+* F) : Subfield F :=
  (σ : F →+* F).eqLocusField (RingHom.id F)

@[simp]
theorem mem_fixedSubfield {F : Type*} [Field F] (σ : F ≃+* F) (y : F) :
    y ∈ fixedSubfield σ ↔ σ y = y := by
  rw [fixedSubfield, RingHom.mem_eqLocusField]
  simp

/-- **Cardinality of the fixed field.** For a finite field `F` of odd characteristic and a
nontrivial involution `σ` of `F`, the fixed field has cardinality the square root of `|F|`. -/
theorem card_fixedSubfield_sq {F : Type*} [Field F] [Finite F] (σ : F ≃+* F)
    (hσ : Function.Involutive σ) (hchar : ringChar F ≠ 2) (hσ1 : σ ≠ 1) :
    Nat.card F = (Nat.card ↥(fixedSubfield σ)) ^ 2 := by
  classical
  -- a moved point and the anti-invariant element `t = a - σ a`
  obtain ⟨a, ha⟩ := DFunLike.ne_iff.mp hσ1
  have hat : σ a ≠ a := by simpa using ha
  set t : F := a - σ a with ht
  have ht_ne : t ≠ 0 := by
    rw [ht, sub_ne_zero]
    exact fun h => hat h.symm
  have hσt : σ t = -t := by
    rw [ht, map_sub, hσ a]
    ring
  have ht_notmem : t ∉ fixedSubfield σ := by
    intro hmemt
    have hfix : σ t = t := (mem_fixedSubfield σ t).mp hmemt
    rw [hσt] at hfix
    exact ht_ne ((Ring.eq_self_iff_eq_zero_of_char_ne_two hchar).mp hfix)
  have htwo : (2 : F) ≠ 0 := Ring.two_ne_zero hchar
  have hσ2 : σ (2 : F) = 2 := map_ofNat σ 2
  -- `σ` commutes with inversion
  have hσinv : ∀ z : F, σ z⁻¹ = (σ z)⁻¹ := by
    intro z
    by_cases hz : z = 0
    · subst hz; simp
    · have hσz : σ z ≠ 0 := by
        intro h
        apply hz
        have := congrArg σ.symm h
        simpa using this
      have h1 : σ z⁻¹ * σ z = 1 := by rw [← map_mul, inv_mul_cancel₀ hz, map_one]
      have h2 : (σ z)⁻¹ * σ z = 1 := inv_mul_cancel₀ hσz
      exact mul_right_cancel₀ hσz (by rw [h1, h2])
  have hfixc : ∀ c : ↥(fixedSubfield σ), σ (c : F) = (c : F) := fun c =>
    (mem_fixedSubfield σ (c : F)).mp c.2
  -- the explicit `F^σ`-linear coordinate map
  let φ : ↥(fixedSubfield σ) × ↥(fixedSubfield σ) → F :=
    fun p => (p.1 : F) + (p.2 : F) * t
  have hφ : Function.Bijective φ := by
    refine ⟨?_, ?_⟩
    · rintro ⟨c1, e1⟩ ⟨c2, e2⟩ h
      change (c1 : F) + (e1 : F) * t = (c2 : F) + (e2 : F) * t at h
      have h' : (c1 : F) - (e1 : F) * t = (c2 : F) - (e2 : F) * t := by
        have hc := congrArg σ h
        simp only [map_add, map_mul, hfixc c1, hfixc e1, hfixc c2, hfixc e2, hσt] at hc
        linear_combination hc
      have hcc : (c1 : F) = (c2 : F) := by
        have h2 : (2 : F) * (c1 : F) = 2 * (c2 : F) := by linear_combination h + h'
        exact mul_left_cancel₀ htwo h2
      have hee : (e1 : F) = (e2 : F) := by
        have h2 : (2 : F) * ((e1 : F) * t) = 2 * ((e2 : F) * t) := by
          linear_combination h - h'
        exact mul_right_cancel₀ ht_ne (mul_left_cancel₀ htwo h2)
      exact Prod.ext (Subtype.ext hcc) (Subtype.ext hee)
    · intro y
      refine ⟨(⟨(y + σ y) / 2, ?_⟩, ⟨(y - σ y) / (2 * t), ?_⟩), ?_⟩
      · rw [mem_fixedSubfield]
        rw [div_eq_mul_inv, map_mul, map_add, hσ y, hσinv, hσ2]
        ring
      · rw [mem_fixedSubfield]
        rw [div_eq_mul_inv, map_mul, map_sub, hσ y, hσinv, map_mul, hσt, hσ2]
        rw [show (2 : F) * -t = -(2 * t) by ring, inv_neg]
        ring
      · change (y + σ y) / 2 + ((y - σ y) / (2 * t)) * t = y
        have h2t : (2 : F) * t ≠ 0 := mul_ne_zero htwo ht_ne
        field_simp
        ring
  have hcard1 : Nat.card (↥(fixedSubfield σ) × ↥(fixedSubfield σ)) = Nat.card F :=
    Nat.card_congr (Equiv.ofBijective φ hφ)
  rw [Nat.card_prod] at hcard1
  rw [← hcard1]
  ring

/-- **Every element of a finite field fixed by a nontrivial involution is a square.** -/
theorem isSquare_of_fixed_of_involution {F : Type*} [Field F] [Finite F]
    (σ : F ≃+* F) (hσ : Function.Involutive σ) (hσ1 : σ ≠ 1) {x : F} (hx : σ x = x) :
    IsSquare x := by
  classical
  by_cases hchar : ringChar F = 2
  · haveI : CharP F 2 := hchar ▸ (inferInstance : CharP F (ringChar F))
    exact isSquare_of_charTwo' x
  · rcases eq_or_ne x 0 with rfl | hxne
    · exact ⟨0, by simp⟩
    have hxmem : x ∈ fixedSubfield σ := (mem_fixedSubfield σ x).mpr hx
    haveI : Fintype F := Fintype.ofFinite F
    haveI : Fintype ↥(fixedSubfield σ) := Fintype.ofFinite _
    have hcard := card_fixedSubfield_sq σ hσ hchar hσ1
    simp only [Nat.card_eq_fintype_card] at hcard
    -- parity: `|F|` and `|F^σ|` are odd
    have hoddF : Odd (Fintype.card F) :=
      Nat.odd_iff.mpr (FiniteField.odd_card_of_char_ne_two hchar)
    have hodd0 : Odd (Fintype.card ↥(fixedSubfield σ)) := by
      have h := hoddF
      rw [hcard, pow_two] at h
      exact (Nat.odd_mul.mp h).1
    -- Fermat in the fixed field, transported to `F`
    have hFermat : x ^ (Fintype.card ↥(fixedSubfield σ) - 1) = 1 := by
      have hne : (⟨x, hxmem⟩ : ↥(fixedSubfield σ)) ≠ 0 := by
        intro h
        exact hxne (by simpa using congrArg (fun z : ↥(fixedSubfield σ) => (z : F)) h)
      have h := FiniteField.pow_card_sub_one_eq_one (⟨x, hxmem⟩ : ↥(fixedSubfield σ)) hne
      have h2 : Subfield.subtype (fixedSubfield σ)
          ((⟨x, hxmem⟩ : ↥(fixedSubfield σ)) ^ (Fintype.card ↥(fixedSubfield σ) - 1)) = 1 := by
        rw [h]; simp
      rw [map_pow] at h2
      simpa using h2
    -- the exponent relation `|F| / 2 = (|F^σ| - 1) * ((|F^σ| + 1) / 2)`
    have hexp : Fintype.card F / 2 = (Fintype.card ↥(fixedSubfield σ) - 1) *
        ((Fintype.card ↥(fixedSubfield σ) + 1) / 2) := by
      obtain ⟨k, hk⟩ := hodd0
      have hq : Fintype.card F = (2 * k + 1) * (2 * k + 1) := by
        rw [hcard, hk, pow_two]
      have hL : (2 * k + 1) * (2 * k + 1) / 2 = 2 * k * k + 2 * k := by
        have hh : (2 * k + 1) * (2 * k + 1) = 2 * (2 * k * k + 2 * k) + 1 := by ring
        rw [hh]; omega
      have hR : (2 * k + 1 - 1) * ((2 * k + 1 + 1) / 2) = 2 * k * k + 2 * k := by
        have h1 : 2 * k + 1 - 1 = 2 * k := by omega
        have h2 : (2 * k + 1 + 1) / 2 = k + 1 := by omega
        rw [h1, h2]; ring
      rw [hq, hk, hL, hR]
    rw [FiniteField.isSquare_iff hchar hxne, hexp, pow_mul, hFermat, one_pow]

end Work.SSGRoute.NodeS37
