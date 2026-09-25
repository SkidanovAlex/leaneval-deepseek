import Mathlib
import Submission.Work.CFT.Kummer.Defs

/-!
# `δ_{K,p} = 1` iff `p` divides the number of roots of unity in `K`

For a number field `K` and a prime `p`, the indicator `deltaK K p` is `1` exactly when `K`
contains a primitive `p`-th root of unity.  Such a root of unity is an algebraic integer whose
inverse is again integral, hence a torsion unit of `𝓞 K` of order `p`, so `p` divides the order
`NumberField.Units.torsionOrder K = #(𝓞 K)^{×}_{tors}` of the torsion subgroup of the units.
Conversely, since the torsion subgroup of the units of a number field is finite, Cauchy's
theorem gives an element of order `p` as soon as `p` divides its order, and such an element is a
primitive `p`-th root of unity.

These two directions together are the content of the theorem below.
-/

open NumberField

namespace Work.CFT.Kummer

/-- For a number field `K` and a prime `p`, `K` contains a primitive `p`-th root of unity if and
only if `p` divides the order of the torsion subgroup of `Kˣ`, i.e. the number of roots of unity
in `K`. -/
theorem deltaK_eq_one_iff_dvd_torsionOrder (K : Type*) [Field K] [NumberField K] (p : ℕ)
    (hp : p.Prime) :
    Work.CFT.Kummer.deltaK K p = 1 ↔ p ∣ NumberField.Units.torsionOrder K := by
  rw [deltaK_eq_one_iff]
  simp only [IsPrimitiveRoot.iff_orderOf]
  -- the coercion `(𝓞 K)ˣ → Kˣ` is injective, hence preserves orders of elements
  have hinj : Function.Injective (Units.map (algebraMap (𝓞 K) K).toMonoidHom) :=
    Units.map_injective NumberField.RingOfIntegers.coe_injective
  constructor
  · -- a primitive `p`-th root of unity is a torsion unit of `𝓞 K` of order `p`
    rintro ⟨ζ, hζ⟩
    have hp0 : 0 < p := hp.pos
    have hprim : IsPrimitiveRoot ζ p := IsPrimitiveRoot.iff_orderOf.mpr hζ
    -- `ζ` and `ζ⁻¹` are integral over `ℤ`, so `ζ` is a unit of `𝓞 K`
    have hint : IsIntegral ℤ (ζ : K) := (IsPrimitiveRoot.coe_units_iff.mpr hprim).isIntegral hp0
    have hprim' : IsPrimitiveRoot (ζ⁻¹ : Kˣ) p :=
      IsPrimitiveRoot.iff_orderOf.mpr (by rw [orderOf_inv, hζ])
    have hint' : IsIntegral ℤ ((ζ⁻¹ : Kˣ) : K) :=
      (IsPrimitiveRoot.coe_units_iff.mpr hprim').isIntegral hp0
    let u : (𝓞 K)ˣ := Units.mk ⟨(ζ : K), hint⟩ ⟨((ζ⁻¹ : Kˣ) : K), hint'⟩
      (by apply Subtype.ext; show (ζ : K) * ((ζ⁻¹ : Kˣ) : K) = (1 : K)
          rw [Units.val_inv_eq_inv_val]; exact mul_inv_cancel₀ (Units.ne_zero ζ))
      (by apply Subtype.ext; show ((ζ⁻¹ : Kˣ) : K) * (ζ : K) = (1 : K)
          rw [Units.val_inv_eq_inv_val]; exact inv_mul_cancel₀ (Units.ne_zero ζ))
    have hu : Units.map (algebraMap (𝓞 K) K).toMonoidHom u = ζ := by
      apply Units.ext
      rfl
    have hordu : orderOf u = p := by
      have h := orderOf_injective (Units.map (algebraMap (𝓞 K) K).toMonoidHom) hinj u
      rw [hu, hζ] at h
      exact h.symm
    -- `u` lies in the torsion subgroup and has order `p`, so `p` divides its order
    have hmem : u ∈ NumberField.Units.torsion K := by
      change u ∈ CommGroup.torsion (𝓞 K)ˣ
      rw [CommGroup.mem_torsion]
      exact isOfFinOrder_iff_pow_eq_one.mpr ⟨p, hp0, by rw [← hordu]; exact pow_orderOf_eq_one u⟩
    have hdvd : p ∣ Nat.card (NumberField.Units.torsion K) := by
      have h := orderOf_dvd_natCard (⟨u, hmem⟩ : NumberField.Units.torsion K)
      rw [Subgroup.orderOf_mk, hordu] at h
      exact h
    exact hdvd
  · -- an element of order `p` in the torsion subgroup is a primitive `p`-th root of unity
    intro hdvd
    obtain ⟨x, hx⟩ := @exists_prime_orderOf_dvd_card' (NumberField.Units.torsion K) _ _ p ⟨hp⟩ hdvd
    refine ⟨Units.map (algebraMap (𝓞 K) K).toMonoidHom (x : (𝓞 K)ˣ), ?_⟩
    have h1 : orderOf ((x : (𝓞 K)ˣ)) = p := (Subgroup.orderOf_coe x).trans hx
    have h := orderOf_injective (Units.map (algebraMap (𝓞 K) K).toMonoidHom) hinj (x : (𝓞 K)ˣ)
    rw [h1] at h
    exact h

end Work.CFT.Kummer
