import Mathlib
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The polar-part descent without `σ`-stability of the valuation

`Work.MotV5.exists_polarApprox_of_unramified` proves the polar-part descent

`∃ u : F, V (algebraMap F L u - W) ≤ 1`

for `L = F⟮W⟯` with `W⁵ - W = g`, `σ` of order `5` generating `Gal(L/F)`, `σ W = W + 1`, and a
valuation `V` of `L` extending `v`, with value-group equality `Γ(V) = Γ(v)`, well-foundedness of
the values `> 1`, and the residue lifting `hresidue`.

**The hypothesis `hσV` (`σ` preserves `V`) of that statement is never used in its proof**: the
descent only uses `σ a = a - 1` for `a = ι u - W` (which comes from `hσW` and `hσF`) and the
consequent identity `σ x - x = -1/q` for `x = a/q`, `q = ι π` with `π ∈ F`.  This file records the
strengthened form of the lemma with `hσV` dropped, which is what the local theory of the twist field
actually supplies: at a place of `L` whose centre on the twist surface is a *closed point* of the
pole locus, the twisted action permutes the prolongations cyclically, so no prolongation is
`σ`-stable, yet the descent still applies.
-/

set_option autoImplicit false

namespace Work.MotV5

/-- **Polar-part descent, without any stability assumption on `V`.**  Same statement as
`Work.MotV5.exists_polarApprox_of_unramified` with the hypothesis `hσV` removed (it is unused in
that proof). -/
theorem exists_polarApprox_of_unramified' {F L Γ₀ Γ₁ : Type*} [Field F] [Field L] [Algebra F L]
    [CharP F 5] [LinearOrderedCommGroupWithZero Γ₀] [LinearOrderedCommGroupWithZero Γ₁]
    (v : Valuation F Γ₀) (V : Valuation L Γ₁) (σ : L ≃+* L) {W : L} {g : F}
    (hW : W ^ 5 - W = algebraMap F L g)
    (hσW : σ W = W + 1)
    (hσF : ∀ x : F, σ (algebraMap F L x) = algebraMap F L x)
    (hfv : ∀ x : F, V (algebraMap F L x) ≤ 1 ↔ v x ≤ 1)
    (hΓ : ∀ x : L, x ≠ 0 → ∃ y : F, y ≠ 0 ∧ V (algebraMap F L y) = V x)
    (hwf : WellFounded (fun a b : Γ₁ => 1 < a ∧ a < b))
    (hresidue : ∀ x : L, V x ≤ 1 → V (σ x - x) < 1 →
      ∃ y : F, V (algebraMap F L y - x) < 1) :
    ∃ u : F, V (algebraMap F L u - W) ≤ 1 := by
  by_contra h
  simp only [not_exists, not_le] at h
  have descent : ∀ u : F, ∃ u' : F,
      V (algebraMap F L u' - W) < V (algebraMap F L u - W) := by
    intro u
    set a : L := algebraMap F L u - W with ha
    have hault : 1 < V a := by rw [ha]; exact h u
    have hane : a ≠ 0 := by
      intro h0
      have hz : V a = 0 := by rw [h0, Valuation.map_zero]
      rw [hz] at hault
      exact lt_asymm zero_lt_one hault
    obtain ⟨π, hπne, hπV⟩ := hΓ a hane
    set q : L := algebraMap F L π with hq
    have hqne : q ≠ 0 := by
      rw [hq]
      exact fun h0 => hπne ((RingHom.injective (algebraMap F L)) (by simpa using h0))
    set x : L := a / q with hx
    have hqx : q * x = a := by
      rw [hx]
      exact mul_div_cancel₀ a hqne
    have hxle : V x ≤ 1 := by
      have hone : V x = 1 := by
        rw [hx, Valuation.map_div, hq, hπV]
        exact div_self (ne_of_gt (lt_trans zero_lt_one hault))
      exact le_of_eq hone
    have hσa : σ a = a - 1 := by
      rw [ha]
      simp only [map_sub, hσF u, hσW]
      first | refl_ring1 | ring
    have hσx : σ x = (a - 1) * q⁻¹ := by
      rw [hx, div_eq_mul_inv, map_mul, map_inv₀, hσa, hq, hσF π]
    have hsub : σ x - x = -(1 / q) := by
      rw [hσx, hx, div_eq_mul_inv, div_eq_mul_inv]
      field_simp
      first | refl_ring1 | ring
    have hdiff : V (σ x - x) < 1 := by
      rw [hsub, Valuation.map_neg, Valuation.map_div, Valuation.map_one, hq, hπV, one_div]
      exact inv_lt_one_iff₀.mpr (Or.inr hault)
    obtain ⟨y, hy⟩ := hresidue x hxle hdiff
    refine ⟨u - π * y, ?_⟩
    have hyV : V (x - algebraMap F L y) < 1 := by
      have hneg : x - algebraMap F L y = -(algebraMap F L y - x) := by ring
      rw [hneg, Valuation.map_neg]
      exact hy
    have hkey : algebraMap F L (u - π * y) - W = q * (x - algebraMap F L y) := by
      have hL : algebraMap F L (u - π * y) - W = a - q * algebraMap F L y := by
        rw [map_sub, map_mul, ← hq, ha]
        first | refl_ring1 | ring
      have hR : q * (x - algebraMap F L y) = a - q * algebraMap F L y := by
        rw [mul_sub, hqx]
      rw [hL, hR]
    rw [hkey, Valuation.map_mul, hq, hπV, ha]
    exact mul_lt_of_lt_one_right (lt_trans zero_lt_one hault) hyV
  obtain ⟨m, hmS, hmin⟩ := hwf.has_min (Set.range fun u : F => V (algebraMap F L u - W))
      ⟨V (algebraMap F L (0:F) - W), ⟨0, rfl⟩⟩
  obtain ⟨u₀, hu₀⟩ := hmS
  obtain ⟨u₁, hlt⟩ := descent u₀
  exact hmin _ ⟨u₁, rfl⟩ ⟨h u₁, lt_of_lt_of_eq hlt hu₀⟩

end Work.MotV5
