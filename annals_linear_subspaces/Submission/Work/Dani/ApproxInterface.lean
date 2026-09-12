import Mathlib
import ChallengeDeps
import Submission.Helpers
import Submission.Work.Dani.Part2
import Submission.Work.Dani.OrthoRep
import Submission.Work.Dani.Conjunct2
import Submission.Work.Interface.Theorem9ToConjunct1
import Submission.Commons.Analysis.ENNReal.natCast_div_natCast_sub_mul_ofReal

/-!
# The sharp interface: flow approximants at *arbitrarily large* times ⟹ conjunct 1

This module replaces the "critical-window" interface of `Submission.FlowToDirichlet` by the
**weaker and correct** hypothesis that the flow production is available at *arbitrarily large*
times.  The window form asks for a good time in the (fixed-width) window
`e^{−t·rate} ∈ [c₀ε/4, c₀ε/2]` for every `ε ∈ (0,1]`, i.e. *bounded gaps* of the good-time set,
which the energy argument does **not** give (and which is very likely false); whereas the paper's
Theorem 9 only uses one good time at each (arbitrarily large) scale.

The abstract content is a short chase.  Suppose that for arbitrarily large `t` there is a rational
`k`-plane `v` with

  `d(v,W) ≤ c₁ · e^{−t·rate}`  and  `H(v) ≤ c₂ · e^{t·k/ℓ}`   (`rate = 1/ℓ + 1/(d−ℓ)`).

Then for every `β < d/(k(d−ℓ))` and every `c > 0` one of these approximants satisfies
`d(v,W) < c·H(v)^{−β}`: assuming `d(v,W) ≥ c·H(v)^{−β}` for all rational `k`-planes forces
`c ≤ d·H^β ≤ c₁c₂^β·e^{t·(kβ/ℓ − rate)}`, whose right-hand side tends to `0` because
`kβ/ℓ < rate` for `β < d/(k(d−ℓ))`.  Hence `β_k(W) ≥ d/(k(d−ℓ))`, the first conjunct of the
challenge.

Module `Submission.Work.Dani.ApproxInterface`, namespace `Submission.ApproxInterface`.
-/

noncomputable section

open LinearSubspaces ENNReal Real Module exteriorPower InnerProductGeometry
open scoped LinearAlgebra.Projectivization

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option linter.unusedSectionVars false

namespace Submission.ApproxInterface

variable {d : ℕ}
local notation "ℝᵈ" => EuclideanSpace ℝ (Fin d)
local notation "ℤᵈ" => intPoints

/-- The flow rate `1/ℓ + 1/(d−ℓ)` as a single fraction: `rate = d / (ℓ(d−ℓ))`. -/
lemma rate_eq {l : ℕ} (hl0 : 0 < l) (hld : l < d) :
    Submission.DaniEndgame.rate d l = (d : ℝ) / ((l : ℝ) * ((d : ℝ) - (l : ℝ))) := by
  rw [Submission.DaniEndgame.rate, Nat.cast_sub (le_of_lt hld)]
  have hlR : (0 : ℝ) < (l : ℝ) := by exact_mod_cast hl0
  have hdR : (0 : ℝ) < (d : ℝ) - (l : ℝ) := by
    have : (l : ℝ) < (d : ℝ) := by exact_mod_cast hld
    linarith
  field_simp
  ring

/-- The key comparison `kβ/ℓ < rate` for `β < d/(k(d−ℓ))`. -/
lemma mul_div_lt_rate {l k : ℕ} (hl0 : 0 < l) (hld : l < d) {β : ℝ} (_hβ0 : 0 < β)
    (hk : 1 ≤ k) (hβ : β < (d : ℝ) / ((k : ℝ) * ((d : ℝ) - (l : ℝ)))) :
    (k : ℝ) * β / (l : ℝ) < Submission.DaniEndgame.rate d l := by
  have hlR : (0 : ℝ) < (l : ℝ) := by exact_mod_cast hl0
  have hdlR : (0 : ℝ) < (d : ℝ) - (l : ℝ) := by
    have : (l : ℝ) < (d : ℝ) := by exact_mod_cast hld
    linarith
  have hkR : (0 : ℝ) < (k : ℝ) := by exact_mod_cast (lt_of_lt_of_le zero_lt_one hk)
  have hkβ : (k : ℝ) * β < (d : ℝ) / ((d : ℝ) - (l : ℝ)) := by
    have hden : (0 : ℝ) < (k : ℝ) * ((d : ℝ) - (l : ℝ)) := mul_pos hkR hdlR
    have h1 : β * ((k : ℝ) * ((d : ℝ) - (l : ℝ))) < (d : ℝ) := (lt_div_iff₀ hden).mp hβ
    rw [lt_div_iff₀ hdlR]
    nlinarith [h1]
  have h5 : ((k : ℝ) * β) * ((d : ℝ) - (l : ℝ)) < (d : ℝ) := (lt_div_iff₀ hdlR).mp hkβ
  have h6 := mul_lt_mul_of_pos_left h5 hlR
  rw [rate_eq hl0 hld, div_lt_div_iff₀ hlR (mul_pos hlR hdlR)]
  nlinarith [h6]

/-- **The abstract interface.**  Approximants of Dirichlet quality at arbitrarily large times give
the first conjunct's lower bound at the plane `W`. -/
theorem diophantineExponent_ge_of_approx {l k : ℕ} (hl0 : 0 < l) (hld : l < d) (hk1 : 1 ≤ k)
    (W : Submodule ℝ ℝᵈ) (_hW : Module.finrank ℝ W = l)
    {c1 c2 : ℝ} (hc1 : 0 < c1) (hc2 : 0 < c2)
    (h : ∀ T : ℝ, ∃ t : ℝ, T ≤ t ∧ ∃ v : Submodule ℝ ℝᵈ, ∃ hv : IsRational v,
      Module.finrank ℝ v = k ∧
      LinearSubspaces.distSubspaces v W ≤ c1 * Real.exp (-(t * Submission.DaniEndgame.rate d l)) ∧
      LinearSubspaces.height v hv ≤ c2 * Real.exp (t * (k : ℝ) / (l : ℝ))) :
    diophantineExponent k W ≥ (d : ℝ≥0∞) / (k * (d - l)) := by
  refine Submission.Helpers.diophantineExponent_ge_of_forall_mem k W ((d : ℝ≥0∞) / (k * (d - l)))
    ?_
  intro β hβ0 hcond
  obtain ⟨c0, hc0, hcondAll⟩ := hcond
  have hDle : (d : ℝ) / ((k : ℝ) * ((d : ℝ) - (l : ℝ))) ≤ β := by
    by_contra hb
    have hβD : β < (d : ℝ) / ((k : ℝ) * ((d : ℝ) - (l : ℝ))) := lt_of_not_ge hb
    have hrpos : 0 < Submission.DaniEndgame.rate d l - (k : ℝ) * β / (l : ℝ) := by
      linarith [mul_div_lt_rate hl0 hld hβ0 hk1 hβD]
    set r : ℝ := Submission.DaniEndgame.rate d l - (k : ℝ) * β / (l : ℝ) with hrdef
    have hr : 0 < r := hrpos
    set T : ℝ := max 0 (Real.log (c1 * c2 ^ β / c0) / r + 1) with hTdef
    obtain ⟨t, htT, v, hv, hvk, hdist, hheight⟩ := h T
    have hHpos : 0 < height v hv := Submission.height_pos v hv
    -- the defining lower bound, written as `c₀ ≤ d(v,W)·H^β`
    have hle1 : c0 ≤ distSubspaces v W * height v hv ^ β := by
      have h2 := hcondAll v hvk hv
      have h4 : height v hv ^ (-β) * height v hv ^ β = 1 := by
        rw [← Real.rpow_add hHpos (-β) β, show -β + β = 0 by ring, Real.rpow_zero]
      calc c0 = c0 * 1 := (mul_one c0).symm
        _ = c0 * (height v hv ^ (-β) * height v hv ^ β) := by rw [h4]
        _ = (c0 * height v hv ^ (-β)) * height v hv ^ β := by ring
        _ ≤ distSubspaces v W * height v hv ^ β :=
            mul_le_mul_of_nonneg_right h2 (Real.rpow_nonneg hHpos.le β)
    -- the Dirichlet-quality upper bound along the approximants
    have hupper : distSubspaces v W * height v hv ^ β ≤ c1 * c2 ^ β * Real.exp (-(t * r)) := by
      have hstep : distSubspaces v W * height v hv ^ β ≤
          (c1 * Real.exp (-(t * Submission.DaniEndgame.rate d l))) *
            (c2 * Real.exp (t * (k : ℝ) / (l : ℝ))) ^ β :=
        mul_le_mul hdist (Real.rpow_le_rpow hHpos.le hheight hβ0.le)
          (Real.rpow_nonneg hHpos.le β)
          (le_of_lt (mul_pos hc1 (Real.exp_pos _)))
      refine hstep.trans (le_of_eq ?_)
      set B : ℝ := (t * (k : ℝ) / (l : ℝ)) * β with hB
      have h1 : (c2 * Real.exp (t * (k : ℝ) / (l : ℝ))) ^ β = c2 ^ β * Real.exp B := by
        rw [Real.mul_rpow hc2.le (Real.exp_nonneg _), Real.rpow_def_of_pos (Real.exp_pos _) β,
          Real.log_exp, hB]
      have h2 : Real.exp (-(t * Submission.DaniEndgame.rate d l)) * Real.exp B =
          Real.exp (-(t * r)) := by
        rw [← Real.exp_add, hB, hrdef]
        congr 1
        ring_nf
      rw [h1]
      calc c1 * Real.exp (-(t * Submission.DaniEndgame.rate d l)) * (c2 ^ β * Real.exp B)
          = c1 * c2 ^ β *
              (Real.exp (-(t * Submission.DaniEndgame.rate d l)) * Real.exp B) := by ring
        _ = c1 * c2 ^ β * Real.exp (-(t * r)) := by rw [h2]
    -- at the chosen time the exponential term is already below `c₀`
    have hlogpos : 0 < c1 * c2 ^ β / c0 := by positivity
    have hTbig : Real.log (c1 * c2 ^ β / c0) < T * r := by
      have h1 : Real.log (c1 * c2 ^ β / c0) / r + 1 ≤ T := le_max_right _ _
      have h2 : (Real.log (c1 * c2 ^ β / c0) / r + 1) * r ≤ T * r :=
        mul_le_mul_of_nonneg_right h1 hr.le
      rw [add_mul, div_mul_cancel₀ _ hr.ne', one_mul] at h2
      linarith
    have hexp : Real.exp (-(t * r)) ≤ Real.exp (-(T * r)) :=
      Real.exp_le_exp.mpr (by nlinarith [htT, hr])
    have hTbound : c1 * c2 ^ β * Real.exp (-(T * r)) < c0 := by
      have h3 : Real.exp (-(T * r)) < c0 / (c1 * c2 ^ β) := by
        have h4 : Real.exp (-(T * r)) < Real.exp (-(Real.log (c1 * c2 ^ β / c0))) := by
          rw [Real.exp_lt_exp]
          linarith [hTbig]
        have h5 : Real.exp (Real.log (c1 * c2 ^ β / c0)) = c1 * c2 ^ β / c0 := Real.exp_log hlogpos
        rw [Real.exp_neg, Real.exp_neg, h5, inv_div] at h4
        simpa [Real.exp_neg] using h4
      have h5 : c1 * c2 ^ β * Real.exp (-(T * r)) < c1 * c2 ^ β * (c0 / (c1 * c2 ^ β)) :=
        mul_lt_mul_of_pos_left h3 (by positivity)
      have h6 : c1 * c2 ^ β * (c0 / (c1 * c2 ^ β)) = c0 := by
        field_simp
      rwa [h6] at h5
    have hexp2 : c1 * c2 ^ β * Real.exp (-(t * r)) ≤ c1 * c2 ^ β * Real.exp (-(T * r)) :=
      mul_le_mul_of_nonneg_left hexp (by positivity)
    linarith [hle1, hupper, hexp2, hTbound]
  have hfrac : (d : ℝ≥0∞) / (k * (d - l)) =
      ENNReal.ofReal ((d : ℝ) / ((k : ℝ) * ((d : ℝ) - (l : ℝ)))) := by
    simpa using
      (Commons.Analysis.ENNReal.natCast_div_natCast_sub_mul_ofReal (d := d) (l := l) (k := k)
        (hld := hld) (hk := hk1))
  rw [hfrac]
  exact ENNReal.ofReal_le_ofReal hDle


/-- **The flow-production interface.**  This is the shape in which the paper's §3 machinery
(Prop 5 + time selection) delivers its output: for every `ℓ`-plane `W` and every `T` there is a
time `t ≥ T` and an independent integer family `m` whose *flowed* wedge at `t` is dominated by its
`L`-block with constant `c₀` and bounded by `C₀`.  We prove that this implies the first conjunct of
the challenge, via `diophantineExponent_ge_of_approx` and Prop 1 part 2
(`Submission.DaniPart2.exists_dominated_pair`).

Note the quantifier over `T`: only *arbitrarily large* times are required — no window, hence no
bounded-gap statement about the good-time set. -/
theorem conjunct1_of_flow_production {l k : ℕ} (_hd : 2 ≤ d) (hl0 : 0 < l) (hld : l < d)
    (hk1 : 1 ≤ k) (hkl : k ≤ l) {c₀ C₀ : ℝ} (hc₀ : 0 < c₀) (hC₀ : 0 < C₀)
    (hprod : ∀ W : Submodule ℝ ℝᵈ, ∀ (hW : Module.finrank ℝ W = l), ∀ T : ℝ,
      ∃ t : ℝ, T ≤ t ∧ ∃ m : Fin k → ℝᵈ, (∀ i, m i ∈ ℤᵈ) ∧ LinearIndependent ℝ m ∧
        Submission.DaniEndgame.Dominates d l k t c₀
          (exteriorPower.map k
            (Submission.DaniOrthoRep.orthRep (le_of_lt hld) W hW : ℝᵈ →ₗ[ℝ] ℝᵈ)
            (exteriorPower.ιMulti ℝ k m)) ∧
        ‖Submission.DaniEndgame.eFlowK d l k t
          (exteriorPower.map k
            (Submission.DaniOrthoRep.orthRep (le_of_lt hld) W hW : ℝᵈ →ₗ[ℝ] ℝᵈ)
            (exteriorPower.ιMulti ℝ k m))‖ ≤ C₀) :
    ∀ x : Submodule ℝ ℝᵈ, Module.finrank ℝ x = l →
      diophantineExponent k x ≥ (d : ℝ≥0∞) / (k * (d - l)) := by
  intro x hx
  have hk0 : 0 < k := hk1
  refine diophantineExponent_ge_of_approx (d := d) hl0 hld hk1 x hx
    (c1 := c₀⁻¹) (c2 := ((k : ℝ) + 1) * c₀⁻¹ * C₀) (inv_pos.mpr hc₀) (by positivity) ?_
  intro T
  obtain ⟨t, htT, m, hmem, hLI, hdom, hbound⟩ := hprod x hx (max T 0)
  have ht0 : 0 ≤ t := le_trans (le_max_right T 0) htT
  obtain ⟨hV, hdist, hheight⟩ := Submission.DaniPart2.exists_dominated_pair (d := d) (ℓ := l)
    (k := k) hk0 hkl hld x hx m hmem hLI ht0 hc₀ hdom
  refine ⟨t, le_trans (le_max_left T 0) htT, Submodule.span ℝ (Set.range m), hV,
    Submission.PlaneFinrank.finrank_span_range (d := d) m hLI, ?_, ?_⟩
  · exact hdist
  · calc LinearSubspaces.height (Submodule.span ℝ (Set.range m)) hV
        ≤ ((k : ℝ) + 1) * c₀⁻¹ * Real.exp (t * (k : ℝ) / (l : ℝ)) *
            ‖Submission.DaniEndgame.eFlowK d l k t
              (exteriorPower.map k
                (Submission.DaniOrthoRep.orthRep (le_of_lt hld) x hx : ℝᵈ →ₗ[ℝ] ℝᵈ)
                (exteriorPower.ιMulti ℝ k m))‖ := hheight
      _ ≤ ((k : ℝ) + 1) * c₀⁻¹ * Real.exp (t * (k : ℝ) / (l : ℝ)) * C₀ :=
          mul_le_mul_of_nonneg_left hbound (by positivity)
      _ = ((k : ℝ) + 1) * c₀⁻¹ * C₀ * Real.exp (t * (k : ℝ) / (l : ℝ)) := by ring

/-- **The challenge theorem from the flow production.**  Packaging the first conjunct
(`conjunct1_of_flow_production`) with the already-proven reduction of the second conjunct to the
first (`Submission.Conjunct2.conjunct2_of_conjunct1`): the single remaining input of
`Submission.theorem_1` is the §3 flow production at arbitrarily large times. -/
theorem theorem_1_of_flow_production {l k : ℕ} (hd : 2 ≤ d) (hl0 : 0 < l) (hld : l < d)
    (hk1 : 1 ≤ k) (hkl : k ≤ l) {c₀ C₀ : ℝ} (hc₀ : 0 < c₀) (hC₀ : 0 < C₀)
    (hprod : ∀ W : Submodule ℝ ℝᵈ, ∀ (hW : Module.finrank ℝ W = l), ∀ T : ℝ,
      ∃ t : ℝ, T ≤ t ∧ ∃ m : Fin k → ℝᵈ, (∀ i, m i ∈ ℤᵈ) ∧ LinearIndependent ℝ m ∧
        Submission.DaniEndgame.Dominates d l k t c₀
          (exteriorPower.map k
            (Submission.DaniOrthoRep.orthRep (le_of_lt hld) W hW : ℝᵈ →ₗ[ℝ] ℝᵈ)
            (exteriorPower.ιMulti ℝ k m)) ∧
        ‖Submission.DaniEndgame.eFlowK d l k t
          (exteriorPower.map k
            (Submission.DaniOrthoRep.orthRep (le_of_lt hld) W hW : ℝᵈ →ₗ[ℝ] ℝᵈ)
            (exteriorPower.ιMulti ℝ k m))‖ ≤ C₀) :
    (∀ x : Submodule ℝ ℝᵈ, Module.finrank ℝ x = l →
        diophantineExponent k x ≥ (d : ℝ≥0∞) / (k * (d - l))) ∧
      ∃ x : Submodule ℝ ℝᵈ, Module.finrank ℝ x = l ∧
        diophantineExponent k x = (d : ℝ≥0∞) / (k * (d - l)) :=
  ⟨conjunct1_of_flow_production hd hl0 hld hk1 hkl hc₀ hC₀ hprod,
   Submission.Conjunct2.conjunct2_of_conjunct1 hk1 hkl hld
     (conjunct1_of_flow_production hd hl0 hld hk1 hkl hc₀ hC₀ hprod)⟩

end Submission.ApproxInterface

end
