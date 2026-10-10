import Mathlib
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.MotV5

/-- **Polar-part descent for an unramified Artin–Schreier extension** (the crux of
`Work.MotV5.RigAS.bridge_twist` in the case `e = 1`).

`F ⊆ L` fields of characteristic `5`, `W ∈ L` with `W⁵ - W = ι g`, `σ` a ring automorphism of `L`
fixing `F` and sending `W` to `W + 1`, `V` a valuation of `L` restricting to (the valuation ring
of) `v` and preserved by `σ`.  Hypotheses: every value of `V` on `L` is a value of `v` on `F`
(exactly `e = 1`; mere cofinality is *not* enough), the values strictly above `1` are
well-founded (no infinite descending chains; true for value groups embeddable in `(ℚ,+)`), and
residue classes of `V`-integral elements fixed by `σ` are lifted by elements of `F`.

Proof route (polar-part descent): given `u ∈ F`, let `m` be the order of the pole of `W_u := W - u`
at `V`.  Then `x := W_u π^m ∈ O_V` for a uniformiser `π` of `F`, and `σ x - x = (σ W - W) π^m =
π^m ∈ 𝔪_V`, so the residue hypothesis applies to `x` and produces `y ∈ F` with
`V (ι y - W_u π^m) < 1`; then `u + π^{-m} y ∈ F` has strictly higher order.  Well-foundedness of
the orders above `0` gives `u ∈ F` with `V (W - u) ≤ 1`. -/
theorem exists_polarApprox_of_unramified {F L Γ₀ Γ₁ : Type*} [Field F] [Field L] [Algebra F L]
    [CharP F 5] [LinearOrderedCommGroupWithZero Γ₀] [LinearOrderedCommGroupWithZero Γ₁]
    (v : Valuation F Γ₀) (V : Valuation L Γ₁) (σ : L ≃+* L) {W : L} {g : F}
    (hW : W ^ 5 - W = algebraMap F L g)
    (hσW : σ W = W + 1)
    (hσF : ∀ x : F, σ (algebraMap F L x) = algebraMap F L x)
    (hσV : ∀ x : L, V (σ x) = V x)
    (hfv : ∀ x : F, V (algebraMap F L x) ≤ 1 ↔ v x ≤ 1)
    (hΓ : ∀ x : L, x ≠ 0 → ∃ y : F, y ≠ 0 ∧ V (algebraMap F L y) = V x)
    (hwf : WellFounded (fun a b : Γ₁ => 1 < a ∧ a < b))
    (hresidue : ∀ x : L, V x ≤ 1 → V (σ x - x) < 1 →
      ∃ y : F, V (algebraMap F L y - x) < 1) :
    ∃ u : F, V (algebraMap F L u - W) ≤ 1 := by
  -- Assume the contrary: every translate of `W` by an element of `F` still has a pole.
  by_contra h
  simp only [not_exists, not_le] at h
  -- `h : ∀ u : F, 1 < V (ι u - W)`.
  -- Descent step: from a translate `ι u - W` with a pole one produces a translate with a
  -- strictly *smaller* pole.  Let `a := ι u - W`, `γ := V a > 1`, and pick `π ∈ F`, `π ≠ 0`,
  -- with `V (ι π) = γ` (here `hΓ` is used).  Put `x := a / ι π`; then `V x = 1` and
  -- `σ x - x = -1/ι π` has value `γ⁻¹ < 1`, so the residue hypothesis gives `y ∈ F` with
  -- `V (ι y - x) < 1`.  Then `u' := u - π y` has `ι u' - W = ι π · (x - ι y)`, of value `γ·δ`
  -- with `δ < 1`, whence `V (ι u' - W) < γ`.
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
  -- Well-foundedness of the values `> 1` forbids an infinite descent.
  obtain ⟨m, hmS, hmin⟩ := hwf.has_min (Set.range fun u : F => V (algebraMap F L u - W))
      ⟨V (algebraMap F L (0:F) - W), ⟨0, rfl⟩⟩
  obtain ⟨u₀, hu₀⟩ := hmS
  obtain ⟨u₁, hlt⟩ := descent u₀
  exact hmin _ ⟨u₁, rfl⟩ ⟨h u₁, lt_of_lt_of_eq hlt hu₀⟩

end Work.MotV5
