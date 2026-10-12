import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Submission.Work.SmallBoxSliding.Indicator
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The `u`-support of the sliding cutoff `χ_{B(u)}`

This file records the elementary (and essential) geometric fact behind the
`u`-marginal integrability statements of `Work.BoseFixB1S.corrMarginal`:

    `χ_{B(u)}(z) = χ(z/ℓ)·χ(z/(ℓd) − u)` can only be non-zero when the sliding
    centre `u` lies in the *fixed* centred cube `acube ((1+d)/d)`.

Indeed, if `χ_{B(u)}(z) ≠ 0` then `z ∈ acube ℓ` and `z − (ℓd)•u ∈ acube(ℓd)`
(`Submission.BoseGases.chiB_support_mem`), so coordinatewise
`|z_m| ≤ ℓ/2` and `|z_m − ℓd u_m| ≤ ℓd/2`, whence
`ℓd|u_m| ≤ |z_m| + |z_m − ℓd u_m| ≤ ℓ(1+d)/2`, i.e. `|u_m| ≤ (1+d)/(2d)`.

Consequently every `u`-family of states cut off by `χ_{B(u)}` (such as
`u ↦ χ_{B(u)}·w`) is **supported in the fixed cube** `acube ((1+d)/d)` of
finite Lebesgue measure — which is what makes the `u`-marginal integrals
finite (and the `u`-decay of the cutoff kinetic word `u ↦ bsW …` automatic).
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators ENNReal

namespace Work.BoseFixB1S

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

open Submission.BoseGases

set_option autoImplicit false
set_option linter.unusedVariables false

/-- **Geometric core.**  If `χ_{B(u)}` does not vanish at the point `z`, then
the sliding centre `u` lies in the fixed cube `acube ((1+d)/d)`. -/
theorem chiB_ne_zero_mem_acube_u {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d) {u z : ℝ³}
    (h : chiB ℓ d u z ≠ 0) : u ∈ acube ((1 + d) / d) := by
  have hmem := chiB_support_mem hℓ hd u z h
  rw [mem_dlBox_iff] at hmem
  obtain ⟨hz, hzu⟩ := hmem
  rw [mem_acube_iff] at hz hzu ⊢
  have hld : 0 < ℓ * d := mul_pos hℓ hd
  intro m
  have hzm := hz m
  have hzum := hzu m
  simp only [Set.mem_Icc] at hzm hzum
  have h2 : |z m - ℓ * d * u m| ≤ ℓ * d / 2 := by
    have he : (z - (ℓ * d) • u) m = z m - ℓ * d * u m := by
      simp [PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]
    rw [he] at hzum
    exact abs_le.mpr ⟨by linarith [hzum.1], by linarith [hzum.2]⟩
  have h1 : |z m| ≤ ℓ / 2 := abs_le.mpr ⟨by linarith [hzm.1], by linarith [hzm.2]⟩
  have h4 : ℓ * d * |u m| ≤ ℓ * (1 + d) / 2 := by
    have hrew : ℓ * d * |u m| = |ℓ * d * u m| := by
      rw [abs_mul, abs_of_pos hld, mul_comm]
    rw [hrew]
    have htri : |ℓ * d * u m| - |z m| ≤ |ℓ * d * u m - z m| :=
      le_trans (le_abs_self _) (abs_abs_sub_abs_le_abs_sub (ℓ * d * u m) (z m))
    have h2' : |ℓ * d * u m - z m| ≤ ℓ * d / 2 := by rw [abs_sub_comm]; exact h2
    linarith
  have hkey : |u m| ≤ (1 + d) / (2 * d) := by
    have hstep : |u m| ≤ (ℓ * (1 + d) / 2) / (ℓ * d) := by
      rw [le_div_iff₀ hld]; linarith
    have hrew : (ℓ * (1 + d) / 2) / (ℓ * d) = (1 + d) / (2 * d) := by
      field_simp
    rwa [hrew] at hstep
  have hb : ((1 + d) / d) / 2 = (1 + d) / (2 * d) := by ring
  rw [Set.mem_Icc]
  constructor
  · have hneg : -((1 + d) / d) / 2 = -((1 + d) / (2 * d)) := by
      rw [neg_div, hb]
    rw [hneg]; linarith [neg_abs_le (u m)]
  · rw [hb]; linarith [le_abs_self (u m)]

/-- **The `u`-support lemma.**  Outside the fixed cube `acube ((1+d)/d)` the
sliding cutoff `χ_{B(u)}` vanishes identically. -/
theorem chiB_eq_zero_of_not_mem_acube_u {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d)
    {u : ℝ³} (hu : u ∉ acube ((1 + d) / d)) : ∀ z : ℝ³, chiB ℓ d u z = 0 := by
  intro z
  by_contra h
  exact hu (chiB_ne_zero_mem_acube_u hℓ hd h)

/-- The cut state `z ↦ χ_{B(u)}(z)·(g z − ρ u)` vanishes identically for `u`
outside the fixed cube `acube ((1+d)/d)` — the form in which the support lemma is
used by the `u`-marginal integrability statements. -/
theorem chiB_mul_eq_zero_of_not_mem_acube_u {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d)
    {u : ℝ³} (hu : u ∉ acube ((1 + d) / d)) (g : ℝ³ → ℝ) (ρ : ℝ) :
    (fun z : ℝ³ => chiB ℓ d u z * (g z - ρ)) = 0 := by
  funext z
  rw [chiB_eq_zero_of_not_mem_acube_u hℓ hd hu z]
  simp

end Work.BoseFixB1S
