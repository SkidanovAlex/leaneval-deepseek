import Mathlib
import ChallengeDeps
import Submission.Work.Dani.Part2
import Submission.GeometryOfNumbers.RationalSpan
import Submission.Work.ModelStar.ModelStarHeight
import Submission.Commons.Analysis.Real.exp_mul_le_of_exp_neg_mul_ge

/-!
# From the flow production (Prop 5) to the rational-plane Dirichlet property

`Submission.ConeFromPlane.coneObligation_of_dirichlet_property` reduces the §3 cone obligation to
the *rational-plane Dirichlet property*: for every `ε ∈ (0,1]` there is a rational `k`-plane `v`
with `d(v,W) ≤ ε/2` and `H(v) ≤ C ε^{−k(d−ℓ)/d}`.

This file supplies the second piece of plumbing: the flow production of the paper's §3 (at a
*critical* time `t` with `e^{−t·rate} ∈ [δ/2, δ]`, a `c₀`-dominated family in `a_t g ℤᵈ` whose
flowed wedge is bounded by `C₀`) implies that Dirichlet property, via Prop 1 part 2
(`DaniPart2.prop1_part2`) and the chase `e^{tk/ℓ} = (e^{t·rate})^{k(d−ℓ)/d}`.

Module `Submission.Work.Dani.FlowToDirichlet`, namespace `Submission.FlowToDirichlet`.
-/

noncomputable section

open LinearSubspaces Module Real
open scoped BigOperators

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false

namespace Submission.FlowToDirichlet

variable {d : ℕ}
local notation "ℝᵈ" => EuclideanSpace ℝ (Fin d)
local notation "ℤᵈ" => intPoints

/-- The exponent identity `k/ℓ = (k(d−ℓ)/d)·(1/ℓ + 1/(d−ℓ))`. -/
theorem div_eq_mul_rate {l k : ℕ} (hl0 : 0 < l) (hld : l < d) :
    (k : ℝ) / (l : ℝ) =
      ((k : ℝ) * ((d - l : ℕ) : ℝ) / (d : ℝ)) * Submission.DaniEndgame.rate d l := by
  have hlR : (0 : ℝ) < (l : ℝ) := by exact_mod_cast hl0
  have hdlR : (0 : ℝ) < (d : ℝ) - (l : ℝ) := by
    have hlt : (l : ℝ) < (d : ℝ) := by exact_mod_cast hld
    linarith
  have hdR : (0 : ℝ) < (d : ℝ) := by linarith
  have hcast : ((d - l : ℕ) : ℝ) = (d : ℝ) - (l : ℝ) := Nat.cast_sub (le_of_lt hld)
  rw [Submission.DaniEndgame.rate, hcast]
  field_simp
  ring

/-- **The Dirichlet property from the flow production.**  The hypothesis is the paper's §3
production at a *critical* time: for every `ε ∈ (0,1]` there is `t ≥ 0` with
`e^{−t·rate} ≤ c₀ε/2`, a `c₀`-dominated integer family in the flowed lattice `a_t g ℤᵈ` whose
flowed wedge is bounded by `C₀`, and the companion bound `e^{tk/ℓ} ≤ C₁ε^{−k(d−ℓ)/d}` (which is
the content of `Commons.Analysis.Real.exp_mul_le_of_exp_neg_mul_ge`). -/
theorem dirichlet_property_of_flow_family {l k : ℕ} (hk1 : 1 ≤ k) (hkl : k ≤ l) (hld : l < d)
    (W : Submodule ℝ ℝᵈ) (_hW : Module.finrank ℝ W = l)
    (g : ℝᵈ ≃ₗᵢ[ℝ] ℝᵈ)
    (hg : Submodule.map (g : ℝᵈ →ₗ[ℝ] ℝᵈ) W = Submission.WedgeBlocks.modelX (d := d) l)
    {c₀ C₀ C₁ : ℝ} (hc₀ : 0 < c₀) (hC₀ : 0 < C₀) (_hC₁ : 0 < C₁)
    (hprod : ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∃ t : ℝ, 0 ≤ t ∧
      Real.exp (-(t * Submission.DaniEndgame.rate d l)) ≤ c₀ * ε / 2 ∧
      ∃ m : Fin k → ℝᵈ, (∀ i, m i ∈ ℤᵈ) ∧ LinearIndependent ℝ m ∧
        Submission.DaniEndgame.Dominates d l k t c₀
          (exteriorPower.map k (g : ℝᵈ →ₗ[ℝ] ℝᵈ) (exteriorPower.ιMulti ℝ k m)) ∧
        ‖Submission.DaniEndgame.eFlowK d l k t
          (exteriorPower.map k (g : ℝᵈ →ₗ[ℝ] ℝᵈ) (exteriorPower.ιMulti ℝ k m))‖ ≤ C₀ ∧
        Real.exp (t * (k : ℝ) / (l : ℝ)) ≤ C₁ * ε ^
          (-((k : ℝ) * ((d - l : ℕ) : ℝ)) / (d : ℝ))) :
    ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∃ v : Submodule ℝ ℝᵈ, ∃ hv : IsRational v,
      Module.finrank ℝ v = k ∧ distSubspaces v W ≤ ε / 2 ∧
      height v hv ≤ ((k : ℝ) + 1) * c₀⁻¹ * C₀ * C₁ *
        ε ^ (-((k : ℝ) * ((d - l : ℕ) : ℝ)) / (d : ℝ)) := by
  classical
  have hl0 : 0 < l := lt_of_lt_of_le (Nat.one_le_iff_ne_zero.mpr (by omega)) hkl
  have hk0 : 0 < k := hk1
  intro ε hε hε1
  obtain ⟨t, ht0, htbound, m, hmem, hLI, hdom, hnorm, hexp⟩ := hprod ε hε hε1
  refine ⟨Submodule.span ℝ (Set.range m),
    Submission.RationalSpan.isRational_span_of_mem_intPoints m hmem,
    Submission.PlaneFinrank.finrank_span_range m hLI, ?_, ?_⟩
  · have h1 := (Submission.DaniPart2.prop1_part2 (d := d) hk0 hkl hld g W hg m hmem hLI ht0 hc₀
      hdom).1
    have h2 : c₀⁻¹ * Real.exp (-(t * Submission.DaniEndgame.rate d l)) ≤ c₀⁻¹ * (c₀ * ε / 2) :=
      mul_le_mul_of_nonneg_left htbound (inv_nonneg.mpr hc₀.le)
    calc distSubspaces (Submodule.span ℝ (Set.range m)) W
        ≤ c₀⁻¹ * Real.exp (-(t * Submission.DaniEndgame.rate d l)) := h1
      _ ≤ c₀⁻¹ * (c₀ * ε / 2) := h2
      _ = ε / 2 := by field_simp
  · obtain ⟨-, h2⟩ := Submission.DaniPart2.prop1_part2 (d := d) hk0 hkl hld g W hg m hmem hLI ht0
      hc₀ hdom
    refine le_trans (h2 _) ?_
    have hpos : 0 ≤ ε ^ (-((k : ℝ) * ((d - l : ℕ) : ℝ)) / (d : ℝ)) :=
      Real.rpow_nonneg hε.le _
    calc ((k : ℝ) + 1) * c₀⁻¹ * Real.exp (t * (k : ℝ) / (l : ℝ)) *
            ‖(Submission.DaniEndgame.eFlowK d l k t)
              ((exteriorPower.map k (g : ℝᵈ →ₗ[ℝ] ℝᵈ)) (exteriorPower.ιMulti ℝ k m))‖
        ≤ ((k : ℝ) + 1) * c₀⁻¹ * Real.exp (t * (k : ℝ) / (l : ℝ)) * C₀ :=
          mul_le_mul_of_nonneg_left hnorm (by positivity)
      _ ≤ ((k : ℝ) + 1) * c₀⁻¹ * (C₁ * ε ^ (-((k : ℝ) * ((d - l : ℕ) : ℝ)) / (d : ℝ))) * C₀ :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hexp (by positivity)) hC₀.le
      _ = ((k : ℝ) + 1) * c₀⁻¹ * C₀ * C₁ *
            ε ^ (-((k : ℝ) * ((d - l : ℕ) : ℝ)) / (d : ℝ)) := by ring

/-- **The Dirichlet property from the critical-window form of the production.**  This is the
natural form of the §3 input: for every `ε ∈ (0,1]` there is a time `t ≥ 0` whose escape factor
lies in the critical window `[c₀ε/4, c₀ε/2]` and carries a `c₀`-dominated family with bounded
flowed wedge; the companion bound `e^{tk/ℓ} ≤ (4/c₀)^{k(d−ℓ)/d}ε^{−k(d−ℓ)/d}` is then automatic
(`Commons.Analysis.Real.exp_mul_le_of_exp_neg_mul_ge`). -/
theorem dirichlet_property_of_critical_window {l k : ℕ} (hk1 : 1 ≤ k) (hkl : k ≤ l) (hld : l < d)
    (W : Submodule ℝ ℝᵈ) (_hW : Module.finrank ℝ W = l)
    (g : ℝᵈ ≃ₗᵢ[ℝ] ℝᵈ)
    (hg : Submodule.map (g : ℝᵈ →ₗ[ℝ] ℝᵈ) W = Submission.WedgeBlocks.modelX (d := d) l)
    {c₀ C₀ : ℝ} (hc₀ : 0 < c₀) (hC₀ : 0 < C₀)
    (hprod : ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∃ t : ℝ, 0 ≤ t ∧
      c₀ * ε / 4 ≤ Real.exp (-(t * Submission.DaniEndgame.rate d l)) ∧
      Real.exp (-(t * Submission.DaniEndgame.rate d l)) ≤ c₀ * ε / 2 ∧
      ∃ m : Fin k → ℝᵈ, (∀ i, m i ∈ ℤᵈ) ∧ LinearIndependent ℝ m ∧
        Submission.DaniEndgame.Dominates d l k t c₀
          (exteriorPower.map k (g : ℝᵈ →ₗ[ℝ] ℝᵈ) (exteriorPower.ιMulti ℝ k m)) ∧
        ‖Submission.DaniEndgame.eFlowK d l k t
          (exteriorPower.map k (g : ℝᵈ →ₗ[ℝ] ℝᵈ) (exteriorPower.ιMulti ℝ k m))‖ ≤ C₀) :
    ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∃ v : Submodule ℝ ℝᵈ, ∃ hv : IsRational v,
      Module.finrank ℝ v = k ∧ distSubspaces v W ≤ ε / 2 ∧
      height v hv ≤ ((k : ℝ) + 1) * c₀⁻¹ * C₀ * (4 / c₀) ^
        ((k : ℝ) * ((d - l : ℕ) : ℝ) / (d : ℝ)) *
        ε ^ (-((k : ℝ) * ((d - l : ℕ) : ℝ)) / (d : ℝ)) := by
  have hl0 : 0 < l := lt_of_lt_of_le (Nat.one_le_iff_ne_zero.mpr (by omega)) hkl
  have hk0 : 0 < k := hk1
  have hα : 0 < (k : ℝ) * ((d - l : ℕ) : ℝ) / (d : ℝ) := by
    have h1 : 0 < (k : ℝ) := by exact_mod_cast hk0
    have h2 : 0 < ((d - l : ℕ) : ℝ) := by
      have : 0 < d - l := Nat.sub_pos_of_lt hld
      exact_mod_cast this
    have h3 : (0 : ℝ) < (d : ℝ) := by
      have : 0 < d := lt_of_lt_of_le hl0 (le_of_lt hld)
      exact_mod_cast this
    positivity
  have hrate : 0 < Submission.DaniEndgame.rate d l := by
    rw [Submission.DaniEndgame.rate]
    have hlR : (0 : ℝ) < (l : ℝ) := by exact_mod_cast hl0
    have h1 : 0 < 1 / (l : ℝ) := by positivity
    have h2 : 0 < 1 / (((d - l : ℕ)) : ℝ) := by
      have hlt : 0 < d - l := Nat.sub_pos_of_lt hld
      positivity
    exact add_pos h1 h2
  refine dirichlet_property_of_flow_family (d := d) hk1 hkl hld W _hW g hg hc₀ hC₀
    (by positivity : (0:ℝ) < (4 / c₀) ^ ((k : ℝ) * ((d - l : ℕ) : ℝ) / (d : ℝ)))
    (fun ε hε hε1 => ?_)
  obtain ⟨t, ht0, htlow, hthigh, m, hmem, hLI, hdom, hnorm⟩ := hprod ε hε hε1
  refine ⟨t, ht0, hthigh, m, hmem, hLI, hdom, hnorm, ?_⟩
  have hexp : Real.exp (t * (k : ℝ) / (l : ℝ)) =
      Real.exp (t * Submission.DaniEndgame.rate d l *
        ((k : ℝ) * ((d - l : ℕ) : ℝ) / (d : ℝ))) := by
    rw [show t * (k : ℝ) / (l : ℝ) = t * ((k : ℝ) / (l : ℝ)) by ring,
      div_eq_mul_rate hl0 hld]
    ring
  rw [hexp]
  have hwin : c₀ / 4 * ε ≤ Real.exp (-(t * Submission.DaniEndgame.rate d l)) := by
    have h := htlow
    rwa [show c₀ / 4 * ε = c₀ * ε / 4 by ring]
  have hmain := Commons.Analysis.Real.exp_mul_le_of_exp_neg_mul_ge hrate hα (by positivity) hε hwin
  have h1 : (1 / (c₀ / 4) : ℝ) = 4 / c₀ := by ring
  have h2 : -((k : ℝ) * ((d - l : ℕ) : ℝ) / (d : ℝ)) =
      -((k : ℝ) * ((d - l : ℕ) : ℝ)) / (d : ℝ) := by rw [neg_div]
  rwa [h1, h2] at hmain

end Submission.FlowToDirichlet

end
