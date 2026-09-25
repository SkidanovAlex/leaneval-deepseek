import Mathlib
import Submission.NK.GlobalCFT.Place

/-!
# Correcting a coboundary in the local unit group

Let `L` be a number field, `q` a finite place of `L` and `K = L_q` the corresponding completed
local field, with a fixed uniformizer `π` (`v π = exp (-1)`).  Suppose a finite group `H` acts on
`K` by ring automorphisms `φ g` fixing `π`, and let `f g = φ g (β₀) / β₀` be a coboundary in
`Kˣ` whose values happen to lie in the subgroup `𝒪_qˣ` of local units.

The point of this file is that then the *same* cocycle is a coboundary with a **local unit**
`β`: the unit part `β₀ · π ^ m` of `β₀` (with `m = log (v β₀)`) is again fixed up to the
coboundary `f`, because `π` (hence every power of it) is fixed by the action.

In particular the hypothesis `f g ∈ 𝒪_qˣ` is in fact unnecessary for the conclusion; the
statement is recorded with it because that is the form in which it is consumed.
-/

namespace NK.HassePrinciple

open NK.GlobalCFT

/-- **The unit part of an element of a completed local field.**  For any `β₀` in `Kˣ`, some
integral power `β₀ * π ^ m` of `β₀` by the uniformizer `π` is a local unit, i.e. has valuation
`1`.  Indeed `v (β₀ * π ^ m) = exp (m + m • (-1)) = 1` for `m = log (v β₀)`. -/
theorem exists_zpow_mul_uniformizer_mem_localUnits {L : Type} [Field L] [NumberField L]
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
    (π : (q.adicCompletion L)ˣ)
    (hπ : Valued.v (R := q.adicCompletion L) (Γ₀ := WithZero (Multiplicative ℤ))
        (π : q.adicCompletion L) = WithZero.exp (-1))
    (β₀ : (q.adicCompletion L)ˣ) :
    ∃ m : ℤ, β₀ * π ^ m ∈ Place.localUnits L (Place.ofFinite q) := by
  set m : ℤ := WithZero.log (Valued.v ((β₀ : q.adicCompletion L))) with hm
  have hvβ : Valued.v ((β₀ : q.adicCompletion L)) ≠ 0 :=
    (Valuation.ne_zero_iff Valued.v).mpr (Units.ne_zero β₀)
  have hlog : Valued.v ((β₀ : q.adicCompletion L)) = WithZero.exp m :=
    (WithZero.exp_log hvβ).symm
  refine ⟨m, ?_⟩
  rw [Place.mem_localUnits_ofFinite_iff_valued_eq_one]
  have hcoe : ((β₀ * π ^ m : (q.adicCompletion L)ˣ) : q.adicCompletion L)
      = (β₀ : q.adicCompletion L) * (π : q.adicCompletion L) ^ m := by
    rw [Units.val_mul, Units.val_zpow_eq_zpow_val]
  rw [hcoe, map_mul, hlog, map_zpow₀, hπ, ← WithZero.exp_zsmul, ← WithZero.exp_add,
    show m + m • (-1 : ℤ) = 0 by ring, WithZero.exp_zero]

theorem exists_mem_localUnits_div_of_forall_eq_div {L : Type} [Field L] [NumberField L]
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
    {H : Type} [Group H] [Fintype H]
    (φ : H →* ((q.adicCompletion L) ≃+* (q.adicCompletion L)))
    (π : (q.adicCompletion L)ˣ)
    (hπ : Valued.v (R := q.adicCompletion L) (Γ₀ := WithZero (Multiplicative ℤ)) (π : q.adicCompletion L)
      = WithZero.exp (-1))
    (hπfix : ∀ g : H, φ g π = π)
    (f : H → (q.adicCompletion L)ˣ)
    (hfunits : ∀ g : H, f g ∈ NK.GlobalCFT.Place.localUnits L (NK.GlobalCFT.Place.ofFinite q))
    (β₀ : (q.adicCompletion L)ˣ) (hβ₀ : ∀ g : H, f g = Units.map (φ g).toMonoidHom β₀ / β₀) :
    ∃ β : (q.adicCompletion L)ˣ, β ∈ NK.GlobalCFT.Place.localUnits L (NK.GlobalCFT.Place.ofFinite q) ∧
      ∀ g : H, f g = Units.map (φ g).toMonoidHom β / β := by
  obtain ⟨m, hm⟩ := exists_zpow_mul_uniformizer_mem_localUnits q π hπ β₀
  refine ⟨β₀ * π ^ m, hm, ?_⟩
  intro g
  rw [hβ₀ g]
  -- the action fixes `π ^ m`, hence the ratio `β₀ * π ^ m / β₀` is fixed too
  have hmapπ : Units.map (φ g).toMonoidHom π = π := by
    apply Units.ext
    rw [Units.coe_map]
    exact hπfix g
  have hfix : Units.map (φ g).toMonoidHom (π ^ m) = π ^ m := by
    rw [map_zpow, hmapπ]
  rw [map_mul, hfix]
  exact (mul_div_mul_right_eq_div _ _ _).symm

end NK.HassePrinciple
