import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Normed.Group.AddTorsor
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.Construction.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The cubic barrier lemma of the modulation chapter

This file proves the ODE-comparison ("barrier") estimate that bounds a continuously
differentiable function `φ` on `[0,∞)` from above by `y1`, given that on the right of the
origin its derivative is dominated by the cubic

`y ↦ -2 c y + C (α² + √α · y + α^{-3/2} y² + α^{-5/2} y³)`

which is *negative at* `y1`.  The point is that no sign hypothesis is needed away from `y1`:
if `φ` were to leave the region `(-∞, y1]` for the first time at a time `t`, then at that
instant `φ t = y1`, so the differential inequality forces `φ' t ≤ f (y1) < 0`, hence `φ`
strictly decreases just to the right of `t`, contradicting maximality of the crossing time.

The two auxiliary lemmas isolate the two real-analysis ingredients:

* `barrier_exists_right_lt_of_hasDerivAt_neg` — a strictly negative derivative at a point
  makes the function strictly decrease immediately to the right of it;
* `barrier_sSup_crossing_eq_y1` — the last time `φ ≤ y1` before a moment at which `φ > y1`
  is a genuine crossing point `φ t = y1`, lying strictly inside `(0, τ₀)`.
-/

open Set Filter Topology

namespace Work.Construction

/-- Local one-sided descent: if `f` has a strictly negative derivative at `x`, then `f`
strictly decreases just to the right of `x`. -/
lemma barrier_exists_right_lt_of_hasDerivAt_neg {f : ℝ → ℝ} {f' x : ℝ}
    (h : HasDerivAt f f' x) (hf' : f' < 0) :
    ∃ δ > 0, ∀ y, x < y → y < x + δ → f y < f x := by
  have hw : HasDerivWithinAt f f' (Set.Ioi x) x := h.hasDerivWithinAt
  have hmem : x ∉ Set.Ioi x := by simp
  have hev : ∀ᶠ z in 𝓝[>] x, slope f x z < 0 := hw.limsup_slope_le' hmem hf'
  rw [(nhdsGT_basis x).eventually_iff] at hev
  obtain ⟨ε, hε, hε'⟩ := hev
  refine ⟨ε - x, sub_pos.mpr hε, ?_⟩
  intro y hyx hyδ
  have hyε : y ∈ Set.Ioo x ε := ⟨hyx, by linarith⟩
  have hd := hε' hyε
  rw [slope_def_field] at hd
  have hyx0 : 0 < y - x := sub_pos.mpr hyx
  have hkey := div_mul_cancel₀ (f y - f x) (ne_of_gt hyx0)
  have : f y - f x < 0 := by nlinarith [hd, hyx0, hkey]
  linarith

/-- First-crossing point.  Let `φ` be continuous on `[0,∞)` with `φ 0 < y1 < φ τ₀` for some
`τ₀ ≥ 0`.  Then the largest time `t ≤ τ₀` at which `φ t ≤ y1` satisfies `0 < t < τ₀` and
`φ t = y1`. -/
lemma barrier_sSup_crossing_eq_y1 {φ : ℝ → ℝ} {y1 τ₀ : ℝ}
    (hcont : ContinuousOn φ (Set.Ici 0)) (hτ₀ : 0 ≤ τ₀) (h0 : φ 0 < y1) (hgt : y1 < φ τ₀) :
    0 < sSup (Set.Icc 0 τ₀ ∩ φ ⁻¹' Set.Iic y1) ∧
      sSup (Set.Icc 0 τ₀ ∩ φ ⁻¹' Set.Iic y1) < τ₀ ∧
      φ (sSup (Set.Icc 0 τ₀ ∩ φ ⁻¹' Set.Iic y1)) = y1 := by
  set S := Set.Icc 0 τ₀ ∩ φ ⁻¹' Set.Iic y1 with hS
  have hSne : S.Nonempty := ⟨0, by refine ⟨⟨le_refl 0, hτ₀⟩, ?_⟩; exact le_of_lt h0⟩
  have hSbdd : BddAbove S := ⟨τ₀, fun x hx => hx.1.2⟩
  have hScl : IsClosed S := by
    have h1 : IsClosed (Set.Icc (0:ℝ) τ₀) := isClosed_Icc
    have h2 : IsClosed (Set.Ici (0:ℝ) ∩ φ ⁻¹' Set.Iic y1) :=
      hcont.preimage_isClosed_of_isClosed isClosed_Ici isClosed_Iic
    have hEq : S = Set.Icc 0 τ₀ ∩ (Set.Ici 0 ∩ φ ⁻¹' Set.Iic y1) := by
      rw [hS]; ext x; constructor
      · rintro ⟨hx1, hx2⟩; exact ⟨hx1, hx1.1, hx2⟩
      · rintro ⟨hx1, _, hx2⟩; exact ⟨hx1, hx2⟩
    rw [hEq]; exact h1.inter h2
  have htmem : sSup S ∈ S := hScl.csSup_mem hSne hSbdd
  have ht0 : 0 ≤ sSup S := htmem.1.1
  have htle : sSup S ≤ τ₀ := htmem.1.2
  have htlt : sSup S < τ₀ := by
    rcases lt_or_eq_of_le htle with h | h
    · exact h
    · exfalso
      have : τ₀ ∈ S := h ▸ htmem
      exact absurd this.2 (not_le.mpr hgt)
  have htφ : φ (sSup S) = y1 := by
    refine le_antisymm htmem.2 ?_
    by_contra hlt
    have hlt' : φ (sSup S) < y1 := not_le.mp hlt
    have hmemIci : sSup S ∈ Set.Ici (0:ℝ) := ht0
    have hev : ∀ᶠ z in 𝓝[Set.Ici (0:ℝ)] (sSup S), φ z < y1 :=
      (hcont.continuousWithinAt hmemIci).preimage_mem_nhdsWithin (isOpen_Iio.mem_nhds hlt')
    have hsub : Set.Ioi (sSup S) ⊆ Set.Ici (0:ℝ) := fun z hz => le_trans ht0 (le_of_lt hz)
    have hev2 : ∀ᶠ z in 𝓝[>] (sSup S), φ z < y1 := hev.filter_mono (nhdsWithin_mono _ hsub)
    rw [(nhdsGT_basis (sSup S)).eventually_iff] at hev2
    obtain ⟨ε, hε, hε'⟩ := hev2
    set z := sSup S + min (ε - sSup S) (τ₀ - sSup S) / 2 with hz
    have hzgt : sSup S < z := by rw [hz]; have := lt_min (sub_pos.mpr hε) (sub_pos.mpr htlt); linarith
    have hzltε : z < ε := by
      rw [hz]; have := min_le_left (ε - sSup S) (τ₀ - sSup S); linarith
    have hzltτ : z < τ₀ := by
      rw [hz]; have := min_le_right (ε - sSup S) (τ₀ - sSup S); linarith
    have hzS : z ∈ S := by
      refine ⟨⟨le_of_lt (lt_of_le_of_lt ht0 hzgt), le_of_lt hzltτ⟩, ?_⟩
      exact le_of_lt (hε' ⟨hzgt, hzltε⟩)
    have hle := le_csSup hSbdd hzS
    linarith
  have htpos : 0 < sSup S := by
    rcases lt_or_eq_of_le ht0 with h | h
    · exact h
    · exfalso
      have : φ 0 = y1 := by rw [h]; exact htφ
      linarith
  exact ⟨htpos, htlt, htφ⟩

/-- **Cubic barrier.**  Let `φ` be continuous on `[0,∞)` and differentiable on `(0,∞)`, with
`φ 0 ≤ 0` and, for `τ > 0`,

`φ' τ ≤ -2 c φ τ + C (α² + √α · φ τ + α^{-3/2} (φ τ)² + α^{-5/2} (φ τ)³)`.

If the right-hand side is negative at `y1 > 0`, then `φ τ ≤ y1` for all `τ ≥ 0`. -/
theorem le_of_deriv_le_of_cubic {φ : ℝ → ℝ} {α c C y1 : ℝ} (hα : 0 < α) (hc : 0 < c) (hC : 0 < C)
    (hy1 : 0 < y1)
    (hF : -2 * c * y1 + C * (α ^ 2 + Real.sqrt α * y1 + α ^ (-(3 / 2 : ℝ)) * y1 ^ 2
        + α ^ (-(5 / 2 : ℝ)) * y1 ^ 3) < 0)
    (hcont : ContinuousOn φ (Set.Ici 0))
    (hdiff : ∀ τ, 0 < τ → HasDerivAt φ (deriv φ τ) τ)
    (h0 : φ 0 ≤ 0)
    (hline : ∀ τ, 0 < τ → deriv φ τ ≤ -2 * c * φ τ
      + C * (α ^ 2 + Real.sqrt α * φ τ + α ^ (-(3 / 2 : ℝ)) * φ τ ^ 2
        + α ^ (-(5 / 2 : ℝ)) * φ τ ^ 3)) :
    ∀ τ, 0 ≤ τ → φ τ ≤ y1 := by
  by_contra hcon
  rw [not_forall] at hcon
  obtain ⟨τ₀, hτ₀⟩ := hcon
  rw [not_imp, not_le] at hτ₀
  obtain ⟨hτ₀0, hτ₀⟩ := hτ₀
  have h0' : φ 0 < y1 := lt_of_le_of_lt h0 hy1
  set S : Set ℝ := Set.Icc 0 τ₀ ∩ φ ⁻¹' Set.Iic y1 with hS
  obtain ⟨htpos, htlt, htφ⟩ := barrier_sSup_crossing_eq_y1 hcont hτ₀0 h0' hτ₀
  have hSbdd : BddAbove S := ⟨τ₀, fun x hx => hx.1.2⟩
  have hline_t : deriv φ (sSup S) ≤ -2 * c * φ (sSup S) + C * (α ^ 2 + Real.sqrt α * φ (sSup S)
      + α ^ (-(3 / 2 : ℝ)) * φ (sSup S) ^ 2 + α ^ (-(5 / 2 : ℝ)) * φ (sSup S) ^ 3) :=
    hline (sSup S) htpos
  rw [htφ] at hline_t
  have hderiv_neg : deriv φ (sSup S) < 0 := by linarith [hline_t, hF]
  obtain ⟨δ, hδpos, hδ⟩ := barrier_exists_right_lt_of_hasDerivAt_neg (hdiff (sSup S) htpos) hderiv_neg
  set z : ℝ := sSup S + min δ (τ₀ - sSup S) / 2 with hz
  have hzgt : sSup S < z := by rw [hz]; have := lt_min hδpos (sub_pos.mpr htlt); linarith
  have hzltτ : z < τ₀ := by rw [hz]; have := min_le_right δ (τ₀ - sSup S); linarith
  have hzltδ : z < sSup S + δ := by rw [hz]; have := min_le_left δ (τ₀ - sSup S); linarith
  have hzS : z ∈ S := by
    refine ⟨⟨le_of_lt (lt_trans htpos hzgt), le_of_lt hzltτ⟩, ?_⟩
    have h1 := hδ z hzgt hzltδ
    rw [htφ] at h1
    exact le_of_lt h1
  have hle := le_csSup hSbdd hzS
  linarith

end Work.Construction
