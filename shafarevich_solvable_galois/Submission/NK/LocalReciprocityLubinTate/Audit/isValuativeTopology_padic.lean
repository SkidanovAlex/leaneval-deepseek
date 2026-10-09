/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `ℚ_[p]` carries its valuative topology

Mathlib registers the `ValuativeRel` on `ℚ_[p]` (from `Padic.mulValuation`, the multiplicative
`p`-adic valuation), but not the matching `IsValuativeTopology` instance: the `TODO` at the end of
the module docstring of `Mathlib/NumberTheory/Padics/HeightOneSpectrum.lean` records this gap, and
`Mathlib.NumberTheory.LocalField.Basic` therefore provides no `IsNonarchimedeanLocalField ℚ_[p]`
(hence no `LocallyCompactSpace`, no `IsDiscreteValuationRing 𝒪[K]`, ...).

This file fills the gap.  The content is the classical correspondence between the `p`-adic norm and
the `p`-adic valuation: for `x y : ℚ_[p]`,
`Padic.mulValuation x < Padic.mulValuation y ↔ ‖x‖ < ‖y‖`, so that the valuative balls
`{z | mulValuation.restrict z < γ}` (`γ` a unit of the value group) are exactly the open metric
balls around `0`; the two neighbourhood bases agree and the topology induced by the valuative
relation is the `p`-adic (metric) topology.

## Main result

* `NK.LocalReciprocityLubinTate.Audit.isValuativeTopology_padic` : `IsValuativeTopology ℚ_[p]`.
-/

open scoped Classical
open ValuativeRel MonoidWithZeroHom ValueGroup₀ Valuation WithZero Filter
open scoped Topology

namespace NK.LocalReciprocityLubinTate.Audit

variable {p : ℕ} [Fact p.Prime]

/-- The multiplicative `p`-adic valuation of `p ^ n`, for integral `n`. -/
lemma padicMulValuation_zpow (p : ℕ) [Fact p.Prime] (n : ℤ) :
    Padic.mulValuation (p := p) ((p : ℚ_[p]) ^ n) = WithZero.exp (-n) := by
  have hp : (p : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
  have hx : (p : ℚ_[p]) ^ n ≠ 0 := zpow_ne_zero n hp
  rw [show Padic.mulValuation (p := p) ((p : ℚ_[p]) ^ n) =
      (if ((p : ℚ_[p]) ^ n) = 0 then 0 else WithZero.exp (-((p : ℚ_[p]) ^ n).valuation)) from rfl]
  rw [if_neg hx, Padic.valuation_zpow, Padic.valuation_p, mul_one]

/-- The multiplicative `p`-adic valuation on `ℚ_[p]` is surjective onto `ℤᵐ⁰`. -/
lemma padicMulValuation_surjective (p : ℕ) [Fact p.Prime] (γ : ℤᵐ⁰) :
    ∃ x : ℚ_[p], Padic.mulValuation (p := p) x = γ := by
  by_cases hγ : γ = 0
  · exact ⟨0, by simp [hγ]⟩
  · refine ⟨(p : ℚ_[p]) ^ (-(γ.log)), ?_⟩
    rw [padicMulValuation_zpow p (-(γ.log))]
    simp [WithZero.exp_log hγ]

/-- **The `p`-adic norm is the `p`-adic valuation**: the order induced by `Padic.mulValuation`
coincides with the order induced by the norm `‖·‖`. -/
lemma padicMulValuation_lt_iff_norm_lt (p : ℕ) [Fact p.Prime] (x y : ℚ_[p]) :
    Padic.mulValuation (p := p) x < Padic.mulValuation (p := p) y ↔ ‖x‖ < ‖y‖ := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  by_cases hx : x = 0
  · subst hx
    by_cases hy : y = 0
    · simp [hy]
    · rw [map_zero, show Padic.mulValuation (p := p) y = WithZero.exp (-y.valuation) from by
          simp [Padic.mulValuation, hy]]
      simp [norm_pos_iff, hy]
  · by_cases hy : y = 0
    · subst hy
      rw [map_zero, show Padic.mulValuation (p := p) x = WithZero.exp (-x.valuation) from by
          simp [Padic.mulValuation, hx]]
      simp
    · rw [show Padic.mulValuation (p := p) x = WithZero.exp (-x.valuation) from by
            simp [Padic.mulValuation, hx],
          show Padic.mulValuation (p := p) y = WithZero.exp (-y.valuation) from by
            simp [Padic.mulValuation, hy],
          WithZero.exp_lt_exp, neg_lt_neg_iff,
          Padic.norm_eq_zpow_neg_valuation hx, Padic.norm_eq_zpow_neg_valuation hy,
          zpow_lt_zpow_iff_right₀ hp1, neg_lt_neg_iff]

/-- The unit of the value group of `Padic.mulValuation` attached to a nonzero element `r`: the
class of the value `Padic.mulValuation r`. -/
noncomputable def padicRestrictUnit (p : ℕ) [Fact p.Prime] (r : ℚ_[p]) (hr : r ≠ 0) :
    (ValueGroup₀ ((Padic.mulValuation (p := p) : ℚ_[p] →*₀ ℤᵐ⁰)))ˣ :=
  Units.mk0 (Padic.mulValuation.restrict r) (by
    simp only [ne_eq, Valuation.zero_iff]
    exact hr)

lemma padicRestrictUnit_coe (p : ℕ) [Fact p.Prime] (r : ℚ_[p]) (hr : r ≠ 0) :
    ((padicRestrictUnit p r hr : (ValueGroup₀ ((Padic.mulValuation (p := p) : ℚ_[p] →*₀ ℤᵐ⁰)))ˣ) :
      ValueGroup₀ ((Padic.mulValuation (p := p) : ℚ_[p] →*₀ ℤᵐ⁰))) = Padic.mulValuation.restrict r :=
  Units.val_mk0 _

/-- The valuative ball of the unit attached to `r` is the open metric ball of radius `‖r‖`. -/
lemma padicRestrictUnit_ball (p : ℕ) [Fact p.Prime] (r : ℚ_[p]) (hr : r ≠ 0) :
    {z : ℚ_[p] | Padic.mulValuation.restrict z < (padicRestrictUnit p r hr).1}
      = {z : ℚ_[p] | ‖z‖ < ‖r‖} := by
  ext z
  simp only [Set.mem_ofPred_eq, padicRestrictUnit_coe, Valuation.restrict_lt_iff,
    padicMulValuation_lt_iff_norm_lt]

/-- Every valuative ball around `0` is a neighbourhood of `0`. -/
lemma mem_nhds_zero_of_padicRestrict_ball (p : ℕ) [Fact p.Prime] (s : Set ℚ_[p])
    (γ : (ValueGroup₀ ((Padic.mulValuation (p := p) : ℚ_[p] →*₀ ℤᵐ⁰)))ˣ)
    (hγ : {z : ℚ_[p] | Padic.mulValuation.restrict z < (γ : ValueGroup₀ _)} ⊆ s) :
    s ∈ 𝓝 (0 : ℚ_[p]) := by
  obtain ⟨x₀, hx₀⟩ := padicMulValuation_surjective p (MonoidWithZeroHom.ValueGroup₀.embedding γ.1)
  have he : (MonoidWithZeroHom.ValueGroup₀.embedding γ.1 : ℤᵐ⁰) =
      MonoidWithZeroHom.ValueGroup₀.embedding (Padic.mulValuation.restrict x₀) := by
    rw [embedding_restrict, hx₀]
  have hγeq : (γ.1 : ValueGroup₀ ((Padic.mulValuation (p := p) : ℚ_[p] →*₀ ℤᵐ⁰))) =
      Padic.mulValuation.restrict x₀ := MonoidWithZeroHom.ValueGroup₀.embedding_injective he
  have hx₀ne : x₀ ≠ 0 := by
    intro h
    rw [h, map_zero] at hγeq
    exact Units.ne_zero γ hγeq
  have hset : {z : ℚ_[p] | ‖z‖ < ‖x₀‖} ∈ 𝓝 (0 : ℚ_[p]) := by
    have hb := Metric.ball_mem_nhds (0 : ℚ_[p]) (norm_pos_iff.mpr hx₀ne)
    simpa [Metric.ball, dist_zero_right] using hb
  have hEq : {z : ℚ_[p] | Padic.mulValuation.restrict z < (γ : ValueGroup₀ _)} =
      {z : ℚ_[p] | ‖z‖ < ‖x₀‖} := by
    ext z
    simp only [Set.mem_ofPred_eq, hγeq, Valuation.restrict_lt_iff,
      padicMulValuation_lt_iff_norm_lt]
  rw [hEq] at hγ
  exact mem_of_superset hset hγ

/-- Every neighbourhood of `0` contains a valuative ball around `0`. -/
lemma exists_padicRestrict_ball_subset (p : ℕ) [Fact p.Prime] {s : Set ℚ_[p]}
    (hs : s ∈ 𝓝 (0 : ℚ_[p])) :
    ∃ γ : (ValueGroup₀ ((Padic.mulValuation (p := p) : ℚ_[p] →*₀ ℤᵐ⁰)))ˣ,
      {z : ℚ_[p] | Padic.mulValuation.restrict z < (γ : ValueGroup₀ _)} ⊆ s := by
  rw [Metric.mem_nhds_iff] at hs
  obtain ⟨ε, hε, hball⟩ := hs
  have hp1 : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (ε⁻¹) hp1
  have hle : (p : ℝ) ^ (-(n : ℤ)) ≤ ε := by
    rw [zpow_neg]
    have hpnn : (0 : ℝ) < (p : ℝ) ^ (n : ℤ) :=
      zpow_pos (by exact_mod_cast (Fact.out : p.Prime).pos) _
    have h1 : 1 < (p : ℝ) ^ (n : ℤ) * ε :=
      (inv_lt_iff_one_lt_mul₀ hε).mp (by simpa using hn)
    exact (inv_le_iff_one_le_mul₀ hpnn).mpr (by linarith)
  have hpne : (p : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
  have hx₀ : (p : ℚ_[p]) ^ (n : ℤ) ≠ 0 := zpow_ne_zero _ hpne
  have hnorm : ‖(p : ℚ_[p]) ^ (n : ℤ)‖ = (p : ℝ) ^ (-(n : ℤ)) := Padic.norm_p_zpow (n : ℤ)
  refine ⟨padicRestrictUnit p ((p : ℚ_[p]) ^ (n : ℤ)) hx₀, fun z hz => hball ?_⟩
  have hz' : ‖z‖ < ‖(p : ℚ_[p]) ^ (n : ℤ)‖ := by
    have hb := padicRestrictUnit_ball p ((p : ℚ_[p]) ^ (n : ℤ)) hx₀
    rw [hb] at hz
    exact hz
  rw [hnorm] at hz'
  simpa [Metric.ball, dist_zero_right] using lt_of_lt_of_le hz' hle

/-- **Mathlib gap filled**: the `p`-adic numbers `ℚ_[p]` carry the topology induced by the
`p`-adic valuation, i.e. the valuative topology of the `ValuativeRel` instance
`Padic.instValuativeRel` is the `p`-adic (metric) topology. -/
theorem isValuativeTopology_padic (p : ℕ) [Fact p.Prime] : IsValuativeTopology ℚ_[p] := by
  refine IsValuativeTopology.of_mem_nhds_zero_iff_vle (Padic.mulValuation (p := p)) fun {s} => ?_
  exact ⟨exists_padicRestrict_ball_subset p,
    fun ⟨γ, hγ⟩ => mem_nhds_zero_of_padicRestrict_ball p s γ hγ⟩

end NK.LocalReciprocityLubinTate.Audit
