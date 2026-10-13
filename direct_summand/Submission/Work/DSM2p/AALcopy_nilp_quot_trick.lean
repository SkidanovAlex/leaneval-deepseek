-- Redirected copy of `Submission.Work.DSM2p.nilp_quot_trick` (imports re-pointed to the `AALvaln` vocabulary layer so that
-- `area_AAL_proved.lean` can import the result without an import cycle).  The original
-- file is untouched; this copy is generated mechanically.
import Mathlib
import Submission.Work.DSM2p.AALvaln
import Submission.Work.DSM2p.exists_valuationSubring_fractionRing_quotient
import Submission.Work.DSM2p.valex_iInf_span_pow
import Submission.Work.DSM2p.continuous_of_iInf_span_pow_eq_bot

namespace Work.DSM2p

universe u

open scoped Classical

/-!
# `Work.DSM2p.nilp_quot_trick`

Given a commutative ring `D`, a field `K`, a valuation subring `V ⊆ K`, a ring homomorphism
`f : D →+* V` and an element `x₀ : D` whose image `a = f x₀ ∈ V` is nonzero and a non-unit, we
produce a valuation `v` on `D` with

* `v d ≤ 1` for all `d : D`;
* `v x₀ < 1` and `v x₀ ≠ 0`;
* `IsContinuousValuation x₀ v`, i.e. the values of the powers of `x₀` become smaller than any
  prescribed nonzero element of the value group.

## The construction

`a ∈ V` is nonzero and not a unit, so by `valex_iInf_span_pow` the ideal
`I = ⋂ₙ (aⁿ) ⊆ V` is prime and misses `a`.  Quotienting by `I` and passing to the fraction ring
gives a new valuation subring `W` of `Kbar = Frac(V ⧸ I)` (this is
`exists_valuationSubring_fractionRing_quotient`): a coarsening of the valuation of `V` in which the
image `wbar` of `a` is a nonzero non-unit.  The decisive point is that in `V ⧸ I` the `a`-adic
intersection is zero (`hspans` below), whence the powers of `v wbar` escape below every nonzero
value (`continuous_of_iInf_span_pow_eq_bot`): this is exactly the continuity required.  Since
`V ⊆ W` in the appropriate sense (`W` is the image of `V ⧸ I`), the pulled-back valuation is `≤ 1`
on `D`.
-/

/-- **The nilpotent-quotient trick.**  A nonzero non-unit of a valuation ring can be made
"arbitrarily small" for a continuous valuation of any ring mapping into it. -/
theorem nilp_quot_trick {D : Type*} [CommRing D] {K : Type u} [Field K] (V : ValuationSubring K)
    (f : D →+* V) {x₀ : D} (ht0 : (f x₀ : V) ≠ 0) (ht1 : ¬ IsUnit (f x₀)) :
    ∃ (Γ₀ : Type u) (_ : LinearOrderedCommGroupWithZero Γ₀) (v : Valuation D Γ₀),
      (∀ d : D, v d ≤ 1) ∧ v x₀ < 1 ∧ v x₀ ≠ 0 ∧ IsContinuousValuation x₀ v := by
  -- the element `a = f x₀ ∈ V` is nonzero and a non-unit
  set a : V := f x₀ with ha_def
  have ha0 : a ≠ 0 := by simpa [ha_def] using ht0
  have ha1 : ¬ IsUnit a := by simpa [ha_def] using ht1
  -- the `a`-adic intersection
  let I : Ideal V := ⨅ n : ℕ, Ideal.span {a ^ n}
  obtain ⟨hIprime, haI⟩ := valex_iInf_span_pow V a ha0 ha1
  haveI : I.IsPrime := hIprime
  -- the quotient valuation subring `W` of `Kbar = Frac (V ⧸ I)`
  obtain ⟨W, hW⟩ := exists_valuationSubring_fractionRing_quotient V I
  let Kbar : Type u := FractionRing (V ⧸ I)
  let abar : V ⧸ I := Ideal.Quotient.mk I a
  have habar0 : abar ≠ 0 := by
    change Ideal.Quotient.mk I a ≠ 0
    rw [Ne, Ideal.Quotient.eq_zero_iff_mem]
    exact haI
  let wbar : W := ⟨algebraMap (V ⧸ I) Kbar abar, by
    show algebraMap (V ⧸ I) Kbar abar ∈ W.toSubring
    rw [hW]; exact ⟨abar, rfl⟩⟩
  -- `wbar` is a non-unit of `W`, hence has value `< 1`
  have hwbar_lt : W.valuation (wbar : Kbar) < 1 := by
    rw [← ValuationSubring.valuation_lt_one_iff W wbar]
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    obtain ⟨y, hy⟩ := hu.exists_right_inv
    have hy_range : (y : Kbar) ∈ (algebraMap (V ⧸ I) Kbar).range := hW ▸ y.2
    obtain ⟨z, hz⟩ := hy_range
    have h1 : Ideal.Quotient.mk I a * z = 1 := by
      apply IsFractionRing.injective (V ⧸ I) Kbar
      rw [map_one, map_mul]
      have h3 := congrArg (ValuationSubring.subtype W) hy
      simp only [map_mul, map_one, ValuationSubring.coe_subtype] at h3
      rw [← hz] at h3
      rw [show (↑wbar : Kbar) = algebraMap (V ⧸ I) Kbar (Ideal.Quotient.mk I a) from rfl] at h3
      exact h3
    have h2 : IsUnit (Ideal.Quotient.mk I a) := isUnit_iff_exists_inv.mpr ⟨z, h1⟩
    obtain ⟨v, hv⟩ := isUnit_iff_exists_inv.mp h2
    obtain ⟨vu, hvu⟩ := Ideal.Quotient.mk_surjective v
    have hv' : Ideal.Quotient.mk I a * Ideal.Quotient.mk I vu = 1 := by
      rw [hvu]; exact hv
    have h3 : a * vu - 1 ∈ I := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_one, map_mul, hv', sub_self]
    have h4 : a * vu - 1 ∈ Ideal.span {a ^ 2} :=
      (iInf_le (fun n : ℕ => Ideal.span {a ^ n}) 2) h3
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 h4
    exact ha1 (isUnit_iff_exists_inv.mpr ⟨vu - c * a, by
      have h5 : a * (vu - c * a) = a * vu - c * a ^ 2 := by ring
      rw [h5, hc]
      ring⟩)
  -- the `a`-adic intersection vanishes in the quotient
  have hspans : (⨅ n : ℕ, Ideal.span {abar ^ n}) = ⊥ := by
    rw [eq_bot_iff]
    intro y hy
    rw [Ideal.mem_bot]
    obtain ⟨y₀, rfl⟩ := Ideal.Quotient.mk_surjective y
    refine Ideal.Quotient.eq_zero_iff_mem.mpr ?_
    have hmem : y₀ ∈ ⨅ n : ℕ, Ideal.span {a ^ n} := by
      rw [Ideal.mem_iInf]
      intro n
      have h1 : (Ideal.Quotient.mk I y₀) ∈ Ideal.span {(Ideal.Quotient.mk I a) ^ n} :=
        Ideal.mem_iInf.mp hy n
      rw [show (Ideal.Quotient.mk I a) ^ n = Ideal.Quotient.mk I (a ^ n) from
          (map_pow _ _ _).symm, ← Set.image_singleton, ← Ideal.map_span] at h1
      obtain ⟨z, hz, hz1⟩ := (Ideal.mem_map_iff_of_surjective (Ideal.Quotient.mk I)
        Ideal.Quotient.mk_surjective).mp h1
      have h2 : z - y₀ ∈ I := by
        rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, hz1, sub_self]
      have h3 : z - y₀ ∈ Ideal.span {a ^ n} :=
        (iInf_le (fun k : ℕ => Ideal.span {a ^ k}) n) h2
      have h4 : y₀ = z - (z - y₀) := by ring
      rw [h4]
      exact Ideal.sub_mem _ hz h3
    exact hmem
  -- continuity of the powers of the value of `wbar`
  have hcont : ∀ γ : W.ValueGroup, γ ≠ 0 →
      ∃ n : ℕ, W.valuation (wbar : Kbar) ^ n < γ := by
    have hlt : W.valuation (algebraMap (V ⧸ I) Kbar abar) < 1 := by simpa using hwbar_lt
    have h := continuous_of_iInf_span_pow_eq_bot W hW abar hspans hlt
    simpa using h
  -- the pulled back valuation on `D`
  let φ : D →+* Kbar := (algebraMap (V ⧸ I) Kbar).comp ((Ideal.Quotient.mk I).comp f)
  let v : Valuation D W.ValueGroup := (W.valuation).comap φ
  have hφx : φ x₀ = algebraMap (V ⧸ I) Kbar abar := rfl
  have hv_ball : ∀ d : D, v d ≤ 1 := by
    intro d
    have hd : φ d ∈ W.toSubring := by
      rw [hW]
      exact ⟨Ideal.Quotient.mk I (f d), rfl⟩
    show W.valuation (φ d) ≤ 1
    exact W.valuation_le_one ⟨φ d, hd⟩
  have hv_lt : v x₀ < 1 := by
    show W.valuation (φ x₀) < 1
    rw [hφx]
    simpa using hwbar_lt
  have hv_ne : v x₀ ≠ 0 := by
    show W.valuation (φ x₀) ≠ 0
    rw [hφx]
    intro h0
    have hz : algebraMap (V ⧸ I) Kbar abar = 0 := by
      by_contra hne
      have h1 : W.valuation (algebraMap (V ⧸ I) Kbar abar) *
          W.valuation (algebraMap (V ⧸ I) Kbar abar)⁻¹ = 1 := by
        rw [← map_mul, mul_inv_cancel₀ hne, map_one]
      rw [h0, zero_mul] at h1
      exact one_ne_zero h1.symm
    exact habar0 (IsFractionRing.injective (V ⧸ I) Kbar (by rw [hz, map_zero]))
  have hv_cont : IsContinuousValuation x₀ v := by
    intro γ hγ
    show ∃ n : ℕ, W.valuation (φ x₀) ^ n < γ
    rw [hφx]
    exact hcont γ hγ
  exact ⟨W.ValueGroup, inferInstance, v, hv_ball, hv_lt, hv_ne, hv_cont⟩

end Work.DSM2p
