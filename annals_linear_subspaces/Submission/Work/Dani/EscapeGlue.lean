import Mathlib
import ChallengeDeps
import Submission.Helpers
import Submission.Bridge.Challenge
import Submission.Bridge.ChallengeIsometry
import Submission.GeometryOfNumbers.Heights
import Submission.Commons.Analysis.InnerProductSpace.norm_iMulti_ge_one_of_mem_intPoints
import Submission.Commons.Analysis.ENNReal.natCast_div_natCast_sub_mul_ofReal
import Submission.GeometryOfNumbers.ModelProp1Part1
import Submission.GeometryOfNumbers.WedgeHigherBlocks
import Submission.GeometryOfNumbers.WedgeLemma1a
import Submission.GeometryOfNumbers.WedgeBlocks
import Submission.GeometryOfNumbers.DiagonalFlow
import Submission.GeometryOfNumbers.ProjectionDistance
import Submission.GeometryOfNumbers.ImageLatticeCovolume
import Submission.Work.Dani.OrthoRep
import Submission.Commons.Lattice.Minkowski.wedge_norm_ge_prod_successiveMinimum
import Submission.Commons.Lattice.SuccessiveMinima.Basic
import Submission.Commons.Analysis.InnerProductSpace.intCoords_linearIndependent_real
import Submission.Commons.Analysis.InnerProductSpace.intWedge_norm_ge_one
import Submission.Commons.Analysis.InnerProductSpace.norm_iMulti_comp_isometry
import Submission.Commons.Lattice.Minkowski.wedge_norm_ge_pow_of_successiveMinimum_le
import Submission.Commons.Lattice.Minkowski.wedge_norm_ge_pow_uniform
import Submission.GeometryOfNumbers.Heights
import Submission.Commons.Analysis.InnerProductSpace.norm_iMulti_ge_one_of_mem_intPoints
import Submission.Commons.Analysis.ENNReal.natCast_div_natCast_sub_mul_ofReal

/-!
# The escape glue for conjunct 2 (de Saxcé, Corollary 1, the `β_k(x) ≤ d/(k(d−ℓ))` direction)

Conjunct 2 of the challenge (`∃ x, β_k(x) = d/(k(d−ℓ))`) needs, for an explicit witness `x`
of dimension `ℓ`, the two halves

* `β_k(x) ≥ d/(k(d−ℓ))` — this is conjunct 1 (Theorem 9, the §3 body of work), and
* `β_k(x) ≤ d/(k(d−ℓ))` — **the escape direction**, formalised here.

The escape direction is the contrapositive of de Saxcé's Proposition 1 part 1: a rational
`k`-plane `v` that is *better* than critical (`d(v,x) < c·H(v)^{−β}` with
`β > d/(k(d−ℓ))`) produces, at the critical time `t = log(1/d(v,x))/S`
(`S = 1/ℓ + 1/(d−ℓ)`), a *small* element `⋀^k(a_t s_x m)` of the flowed lattice
`a_t s_x ℤᵈ`; the "slow escape" hypothesis (no exponentially small independent wedge of the
flowed lattice, `λ₁(a_t s_x ℤᵈ) ≥ e^{−εt}`) forbids this.  The Mahler-type lower bound
`C·∏ᵢλᵢ(L) ≤ ‖w₁ ∧ … ∧ w_k‖` (commons
`Commons.Lattice.Minkowski.wedge_norm_ge_prod_successiveMinimum`) converts `λ₁ ≥ e^{−εt}`
into the wedge bound.

Module `Submission.Work.Dani.EscapeGlue`, namespace `Submission.EscapeGlue`.
-/

noncomputable section

open LinearSubspaces ENNReal Real Module exteriorPower InnerProductGeometry
open scoped LinearAlgebra.Projectivization ENNReal

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedSectionVars false

namespace Submission.EscapeGlue

variable {d : ℕ}
local notation "ℝᵈ" => EuclideanSpace ℝ (Fin d)
local notation "ℤᵈ" => intPoints

/-- The flow rate `S = 1/ℓ + 1/(d−ℓ)`: the exponential rate of the distance
`d(v, x) ≍ e^{−tS}` along the diagonal flow. -/
def rateS (d l : ℕ) : ℝ := 1 / (l : ℝ) + 1 / ((d : ℝ) - (l : ℝ))

/-- The critical exponent `α = k(d−ℓ)/d`. -/
def alpha (d k l : ℕ) : ℝ := (k : ℝ) * ((d : ℝ) - (l : ℝ)) / (d : ℝ)

theorem alpha_pos {d k l : ℕ} (hk : 1 ≤ k) (hl0 : 0 < l) (hld : l < d) :
    0 < alpha d k l := by
  have hd : (0 : ℝ) < d := by
    have : 0 < d := lt_of_lt_of_le hl0 (le_of_lt hld)
    exact_mod_cast this
  have hl : (0 : ℝ) < l := by exact_mod_cast hl0
  have hdl : (0 : ℝ) < (d : ℝ) - (l : ℝ) := by
    have : (l : ℝ) < (d : ℝ) := by exact_mod_cast hld
    linarith
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  dsimp [alpha]
  positivity

/-- **Dual interface for `diophantineExponent`**: if the defining separation property holds
for every exponent `β > a`, then `β_k(x) ≤ a`.  (The companion of
`Submission.Helpers.diophantineExponent_ge_of_forall_mem`.) -/
theorem diophantineExponent_le_of_forall_gt (k : ℕ) (x : Submodule ℝ ℝᵈ) {a : ℝ} (ha : 0 ≤ a)
    (h : ∀ β : ℝ, a < β → ∃ c : ℝ, 0 < c ∧ ∀ v : Submodule ℝ ℝᵈ, Module.finrank ℝ v = k →
      (hv : IsRational v) → LinearSubspaces.distSubspaces v x ≥ c * LinearSubspaces.height v hv ^ (-β)) :
    LinearSubspaces.diophantineExponent k x ≤ ENNReal.ofReal a := by
  classical
  set S : Set ℝ := {β : ℝ | β > 0 ∧ ∃ c : ℝ, 0 < c ∧ ∀ v : Submodule ℝ ℝᵈ,
    Module.finrank ℝ v = k → (hv : IsRational v) →
      LinearSubspaces.distSubspaces v x ≥ c * LinearSubspaces.height v hv ^ (-β)} with hS
  have hmem : ∀ β : ℝ, a < β → ENNReal.ofReal β ∈ ENNReal.ofReal '' S := by
    intro β hβ
    refine ⟨β, ⟨lt_of_le_of_lt ha hβ, ?_⟩, rfl⟩
    exact h β hβ
  have hbdd : BddBelow (ENNReal.ofReal '' S) := ⟨0, by rintro _ ⟨β, _, rfl⟩; exact bot_le⟩
  have hne : (ENNReal.ofReal '' S).Nonempty := ⟨_, hmem (a + 1) (by linarith)⟩
  rw [LinearSubspaces.diophantineExponent, hS.symm]
  refine (csInf_le_iff hbdd hne).mpr ?_
  intro b hb
  -- `b` is a lower bound for `ofReal '' S`, hence `b ≤ ofReal β` for every `β > a`
  have hle : ∀ β : ℝ, a < β → b ≤ ENNReal.ofReal β := fun β hβ => hb (hmem β hβ)
  have hbtop : b ≠ ⊤ := by
    have := hle (a + 1) (by linarith)
    exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top this
  refine (ENNReal.le_ofReal_iff_toReal_le hbtop ha).mpr ?_
  by_contra hlt
  have hlt' : a < b.toReal := lt_of_not_ge hlt
  -- `β := (a + b.toReal)/2` lies above `a`, so `b ≤ ofReal β`, forcing `b.toReal ≤ β`
  have hβ : a < (a + b.toReal) / 2 := by linarith
  have hhalf : b.toReal ≤ (a + b.toReal) / 2 :=
    ENNReal.toReal_le_of_le_ofReal (by linarith [hβ, hlt']) (hle ((a + b.toReal) / 2) hβ)
  linarith

/-- **The critical rpow chase.**  If `C₂ ≤ C₁·δᵖ·H` with `0 < p`, `0 < δ ≤ 1`, `1 ≤ H`,
then `(C₂/C₁)^{1/p}·H^{−1/p} ≤ δ`.  This is the algebraic core of the escape direction: the
flowed wedge is bounded above by `C₁·e^{−tk/ℓ}H(v)` (Prop 1 part 1) and below by
`C₂·e^{−kεt}` (Mahler + slow escape); at the critical time the two combine into the
"no better-than-critical approximations" inequality. -/
theorem chase {δ H C1 C2 p : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (hH : 1 ≤ H)
    (hC1 : 0 < C1) (hC2 : 0 < C2) (hp : 0 < p)
    (h : C2 ≤ C1 * δ ^ p * H) :
    (C2 / C1) ^ (1 / p) * H ^ (-(1 / p)) ≤ δ := by
  have hC1H : (0 : ℝ) < C1 * H := by positivity
  -- `C₂ / (C₁·H) ≤ δᵖ`
  have hdiv : C2 / (C1 * H) ≤ δ ^ p := by
    rw [div_le_iff₀ hC1H]
    nlinarith [h]
  -- monotonicity of `x ↦ x^{1/p}`
  have hstep : (C2 / (C1 * H)) ^ (1 / p) ≤ (δ ^ p) ^ (1 / p) :=
    Real.rpow_le_rpow (by positivity) hdiv (by positivity)
  have hpow : (δ ^ p) ^ (1 / p) = δ := by
    rw [← Real.rpow_mul (le_of_lt hδ0), mul_one_div_cancel (ne_of_gt hp), Real.rpow_one]
  -- identify `(C₂/(C₁H))^{1/p}` with the stated product
  have hid : (C2 / (C1 * H)) ^ (1 / p) = (C2 / C1) ^ (1 / p) * H ^ (-(1 / p)) := by
    have hHpos : (0 : ℝ) < H := lt_of_lt_of_le one_pos hH
    rw [Real.div_rpow (le_of_lt hC2) (le_of_lt hC1H),
        Real.mul_rpow (le_of_lt hC1) hHpos.le,
        Real.div_rpow (le_of_lt hC2) (le_of_lt hC1),
        Real.rpow_neg hHpos.le]
    field_simp
  rw [hid] at hstep
  rwa [hpow] at hstep

/-- The exponential-to-`rpow` conversion used at the critical time `t = log(1/δ)/S`. -/
theorem exp_neg_log_div_eq_rpow {δ S R : ℝ} (hδ0 : 0 < δ) (hS : 0 < S) :
    Real.exp (-(Real.log (1 / δ) / S * R)) = δ ^ (R / S) := by
  have hlog : Real.log (1 / δ) = -Real.log δ := by rw [one_div, Real.log_inv]
  rw [Real.rpow_def_of_pos hδ0, hlog]
  congr 1
  field_simp

/-- **Escape bound from the two flow estimates.**  With `δ` the distance, `H` the height,
`ε > 0` the escape parameter, `Φ` the norm of the flowed wedge evaluated at the critical time
`t = log(1/δ)/S` (`S = rateS d l`): if `Φ ≤ C₁·e^{−tk/ℓ}·H` and `C₂·e^{−tkε} ≤ Φ`, then
`δ ≥ c·H^{−β}` for the exponent `β = 1/(α − kε/S)`, `α = alpha d k l`. -/
theorem escape_bound_of_flow_bounds {l k : ℕ} (hk : 1 ≤ k) (hl0 : 0 < l) (hld : l < d)
    {δ H C1 C2 ε Φ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (hH : 1 ≤ H)
    (hC1 : 0 < C1) (hC2 : 0 < C2) (hε : 0 ≤ ε)
    (hp : 0 < alpha d k l - (k : ℝ) * ε / rateS d l)
    (hup : Φ ≤ C1 * Real.exp (-(Real.log (1 / δ) / rateS d l * ((k : ℝ) / (l : ℝ)))) * H)
    (hlo : C2 * Real.exp (-(Real.log (1 / δ) / rateS d l * ((k : ℝ) * ε))) ≤ Φ) :
    (C2 / C1) ^ (1 / (alpha d k l - (k : ℝ) * ε / rateS d l)) *
        H ^ (-(1 / (alpha d k l - (k : ℝ) * ε / rateS d l))) ≤ δ := by
  classical
  have hS : 0 < rateS d l := by
    have hl : (0 : ℝ) < l := by exact_mod_cast hl0
    have hdl : (0 : ℝ) < (d : ℝ) - (l : ℝ) := by
      have : (l : ℝ) < (d : ℝ) := by exact_mod_cast hld
      linarith
    dsimp [rateS]
    positivity
  -- the identity `α = (k/ℓ)/S`
  have hα : alpha d k l = (k : ℝ) / (l : ℝ) / rateS d l := by
    have hl : (l : ℝ) ≠ 0 := by positivity
    have hdl : (d : ℝ) - (l : ℝ) ≠ 0 := by
      have : (l : ℝ) < (d : ℝ) := by exact_mod_cast hld
      linarith
    have hd : (d : ℝ) ≠ 0 := by
      have : (0 : ℝ) < (d : ℝ) := by
        have : 0 < d := lt_of_lt_of_le hl0 (le_of_lt hld)
        exact_mod_cast this
      exact ne_of_gt this
    dsimp [alpha, rateS]
    field_simp
    rw [sub_add_cancel, div_self hd]
  -- convert the two exponentials to powers of `δ`
  rw [exp_neg_log_div_eq_rpow (δ := δ) (S := rateS d l) (R := (k : ℝ) / (l : ℝ)) hδ0 hS] at hup
  rw [exp_neg_log_div_eq_rpow (δ := δ) (S := rateS d l) (R := (k : ℝ) * ε) hδ0 hS] at hlo
  rw [← hα] at hup
  have hYpos : (0 : ℝ) < δ ^ ((k : ℝ) * ε / rateS d l) := Real.rpow_pos_of_pos hδ0 _
  have hppos : 0 < (k : ℝ) / (l : ℝ) / rateS d l - (k : ℝ) * ε / rateS d l := by
    rw [← hα]; exact hp
  have hcomb : C2 ≤ C1 * δ ^ ((k : ℝ) / (l : ℝ) / rateS d l - (k : ℝ) * ε / rateS d l) * H := by
    have h2 : C2 * δ ^ ((k : ℝ) * ε / rateS d l) ≤ C1 * δ ^ (alpha d k l) * H :=
      le_trans hlo hup
    have h3 : C2 ≤ (C1 * δ ^ (alpha d k l) * H) / δ ^ ((k : ℝ) * ε / rateS d l) :=
      (le_div_iff₀ hYpos).mpr h2
    refine h3.trans_eq ?_
    rw [show (C1 * δ ^ (alpha d k l) * H) / δ ^ ((k : ℝ) * ε / rateS d l)
        = C1 * (δ ^ (alpha d k l) / δ ^ ((k : ℝ) * ε / rateS d l)) * H by ring,
      ← Real.rpow_sub hδ0]
    rw [hα]
  have hchase := chase hδ0 hδ1 hH hC1 hC2 hppos hcomb
  rw [hα]
  exact hchase

/-- **Prop 1 part 1 in the form used by the escape glue**: for a `k`-plane (given by an
independent family `u`) that is `δ`-close to the model plane `x₀` (`δ ≤ 1/2`), at the time `t`
whose flow factor is `e^{−tS} = 2√k·δ` the flowed integer wedge is bounded by
`(k+1)·2^k·e^{−tk/ℓ}·‖⋀u‖`. -/
theorem model_wedge_flow_upper {k l : ℕ} (hk : 0 < k) (hkl : k ≤ l) (hld : l < d)
    {δ : ℝ} (hδ0 : 0 < δ) (hδ12 : δ ≤ 1 / 2)
    (u : Fin k → ℝᵈ) (hu : LinearIndependent ℝ u)
    (hbot : (Submodule.span ℝ (Set.range u)) ⊓
      (Submission.WedgeBlocks.modelX (d := d) l)ᗮ = ⊥)
    (hdist : Submission.ProjectionDistance.planeResidual (Submodule.span ℝ (Set.range u))
      (Submission.WedgeBlocks.modelX (d := d) l) = δ)
    (t : ℝ) (ht : Real.exp (-(t * rateS d l)) = 2 * Real.sqrt (k : ℝ) * δ) :
    ‖exteriorPower.map k (Submission.DiagonalFlow.scaleMap
        (Submission.DiagonalFlow.twoScale (Real.exp (-t / (l : ℝ)))
          (Real.exp (t / ((d : ℝ) - (l : ℝ)))) l)) (exteriorPower.ιMulti ℝ k u)‖ ≤
      ((k : ℝ) + 1) * (2 : ℝ) ^ k * Real.exp (-(t * ((k : ℝ) / (l : ℝ)))) *
        ‖exteriorPower.ιMulti ℝ k u‖ := by
  classical
  have hl : (0 : ℝ) < l := by
    have : 0 < l := lt_of_lt_of_le hk hkl
    exact_mod_cast this
  have hdl : (0 : ℝ) < (d : ℝ) - (l : ℝ) := by
    have : (l : ℝ) < (d : ℝ) := by exact_mod_cast hld
    linarith
  have hS : 0 < rateS d l := by dsimp [rateS]; positivity
  have ha : (0 : ℝ) < Real.exp (-t / (l : ℝ)) := Real.exp_pos _
  have hb : (0 : ℝ) ≤ Real.exp (t / ((d : ℝ) - (l : ℝ))) := (Real.exp_pos _).le
  -- the cone hypothesis, from the smallness of `δ`
  have hδexp : (2 : ℝ) * Real.sqrt (k : ℝ) * δ ≤
      Real.exp (-t * ((1 : ℝ) / (l : ℝ) + 1 / ((d : ℝ) - (l : ℝ)))) := by
    rw [← ht]
    have : -t * ((1 : ℝ) / (l : ℝ) + 1 / ((d : ℝ) - (l : ℝ))) =
        -(t * rateS d l) := by dsimp [rateS]; ring
    rw [this]
  have hcone := Submission.ModelProp1Part1.blockRatio_small_of_distSmall (d := d) (k := k)
    (ℓ := l) hk u hu hbot (by rw [hdist]; exact hδ12) t (by rw [hdist]; exact hδexp)
  have hX : 0 < ‖Submission.ExteriorCoordinates.blockElem (d := d) (k := k) (ℓ := l)
      (exteriorPower.ιMulti ℝ k u) 0‖ :=
    Submission.WedgeLemma1a.blockElem_zero_ne_zero_of_transverse (d := d) (k := k) l hk u hu hbot
  have hflow := Submission.WedgeBlocks.pureTensor_flow_le (d := d) (k := k) l hk
    (Real.exp (-t / (l : ℝ))) (Real.exp (t / ((d : ℝ) - (l : ℝ)))) ha hb u hu hbot hX hcone
  -- replace `a^k` and `‖w₀‖ ≤ ‖w‖`
  have hpow : (Real.exp (-t / (l : ℝ))) ^ k = Real.exp (-(t * ((k : ℝ) / (l : ℝ)))) := by
    rw [← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  have hle0 : ‖Submission.ExteriorCoordinates.blockElem (d := d) (k := k) (ℓ := l)
      (exteriorPower.ιMulti ℝ k u) 0‖ ≤ ‖exteriorPower.ιMulti ℝ k u‖ :=
    Submission.DiagonalFlow.norm_blockElem_le_norm (d := d) (k := k) (ℓ := l)
      (exteriorPower.ιMulti ℝ k u) (by omega)
  calc ‖exteriorPower.map k (Submission.DiagonalFlow.scaleMap
        (Submission.DiagonalFlow.twoScale (Real.exp (-t / (l : ℝ)))
          (Real.exp (t / ((d : ℝ) - (l : ℝ)))) l)) (exteriorPower.ιMulti ℝ k u)‖
      ≤ ((k : ℝ) + 1) * (2 : ℝ) ^ k * (Real.exp (-t / (l : ℝ))) ^ k *
          ‖Submission.ExteriorCoordinates.blockElem (d := d) (k := k) (ℓ := l)
            (exteriorPower.ιMulti ℝ k u) 0‖ := hflow
    _ ≤ ((k : ℝ) + 1) * (2 : ℝ) ^ k * (Real.exp (-t / (l : ℝ))) ^ k *
          ‖exteriorPower.ιMulti ℝ k u‖ := by
          have hnn : (0 : ℝ) ≤ ((k : ℝ) + 1) * (2 : ℝ) ^ k *
              (Real.exp (-t / (l : ℝ))) ^ k := by positivity
          exact mul_le_mul_of_nonneg_left hle0 hnn
    _ = ((k : ℝ) + 1) * (2 : ℝ) ^ k * Real.exp (-(t * ((k : ℝ) / (l : ℝ)))) *
          ‖exteriorPower.ιMulti ℝ k u‖ := by rw [hpow]



/-- The full flow map of Section 3: `a_t ∘ s`, where `s` is an isometry and `a_t` is the
exponential two-scale diagonal flow (contracting `ℓ` directions by `e^{−t/ℓ}`, expanding the
remaining `d−ℓ` by `e^{t/(d−ℓ)}`). -/
noncomputable def flowMap (l : ℕ) (s : ℝᵈ ≃ₗᵢ[ℝ] ℝᵈ) (t : ℝ) : ℝᵈ ≃ₗ[ℝ] ℝᵈ :=
  s.toLinearEquiv.trans (Submission.FlowLattice.scaleMapEquiv (d := d)
    (Real.exp (-t / (l : ℝ))) (Real.exp (t / ((d : ℝ) - (l : ℝ)))) l
    (ne_of_gt (Real.exp_pos _)) (ne_of_gt (Real.exp_pos _)))

/-- Computation rule of `flowMap`: it is the diagonal two-scale map applied to `s y`. -/
lemma flowMap_apply (l : ℕ) (s : ℝᵈ ≃ₗᵢ[ℝ] ℝᵈ) (t : ℝ) (y : ℝᵈ) :
    flowMap (d := d) l s t y = Submission.DiagonalFlow.scaleMap
      (Submission.DiagonalFlow.twoScale (Real.exp (-t / (l : ℝ)))
        (Real.exp (t / ((d : ℝ) - (l : ℝ)))) l) (s y) := rfl

open Submission.ProjectionDistance in
lemma intPoints_coord_int (n : ℝᵈ) (hn : n ∈ intPoints (d := d)) (t : Fin d) :
    ∃ z : ℤ, n t = z := by
  classical
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun (R := ℤ) (M := ℝᵈ)
    (v := fun i : Fin d => ((EuclideanSpace.basisFun (Fin d) ℝ) i : ℝᵈ)) (x := n)).mp hn
  refine ⟨c t, ?_⟩
  rw [← hc, WithLp.ofLp_sum, Finset.sum_apply]
  rw [Finset.sum_eq_single t]
  · rw [WithLp.ofLp_smul, Pi.smul_apply, EuclideanSpace.basisFun_apply, PiLp.single_apply]
    simp [zsmul_eq_mul]
  · intro i _ hi
    rw [WithLp.ofLp_smul, Pi.smul_apply, EuclideanSpace.basisFun_apply, PiLp.single_apply,
      if_neg (Ne.symm hi)]
    simp
  · intro h; exact absurd (Finset.mem_univ t) h


open Submission.ProjectionDistance in
lemma bddAbove_residualSet {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (V x : Submodule ℝ E) :
    BddAbove {r : ℝ | ∃ v : E, v ∈ V ∧ ‖v‖ = 1 ∧
      ‖v - ((x.orthogonalProjectionOnto v) : E)‖ = r} := by
  refine ⟨1, ?_⟩
  rintro r ⟨v, hvV, hv1, rfl⟩
  have hsub : ((x.orthogonalProjectionOnto v) : E) = x.starProjection v := by
    rw [Submodule.starProjection_apply]
  rw [hsub]
  have horth : v - x.starProjection v = xᗮ.starProjection v := by
    have h := congrFun (congrArg DFunLike.coe (Submodule.starProjection_orthogonal (𝕜 := ℝ) x)) v
    simp only [sub_apply, ContinuousLinearMap.id_apply] at h
    rw [h]
  rw [horth]
  calc ‖xᗮ.starProjection v‖ ≤ ‖v‖ := Submodule.norm_starProjection_apply_le xᗮ v
    _ = 1 := hv1

open Submission.ProjectionDistance in
lemma one_le_planeResidual_of_meet_ne_bot {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] (V x : Submodule ℝ E)
    (h : V ⊓ xᗮ ≠ ⊥) : 1 ≤ planeResidual V x := by
  obtain ⟨w, hwmem, hwne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h
  rw [Submodule.mem_inf] at hwmem
  obtain ⟨hwV, hwx⟩ := hwmem
  have hwn : ‖w‖ ≠ 0 := norm_ne_zero_iff.mpr hwne
  refine le_csSup (bddAbove_residualSet V x) ?_
  refine ⟨(‖w‖⁻¹) • w, Submodule.smul_mem _ _ hwV, ?_, ?_⟩
  · rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_nonneg (norm_nonneg w), inv_mul_cancel₀ hwn]
  · have hproj : x.orthogonalProjectionOnto ((‖w‖⁻¹) • w) = 0 :=
      Submodule.orthogonalProjectionOnto_apply_of_mem_orthogonal (Submodule.smul_mem _ _ hwx)
    simp only [hproj, Submodule.coe_zero, sub_zero]
    rw [norm_smul, Real.norm_eq_abs, abs_inv,
      abs_of_nonneg (norm_nonneg w), inv_mul_cancel₀ hwn]

/-- The universal lattice constant `vol(B_k)` (the volume of the unit ball of `ℝᵏ`) divided
by `2^{2k}`: the *uniform* Mahler lower-bound constant of
`Commons.Lattice.Minkowski.wedge_norm_ge_pow_uniform`. -/
noncomputable def ballConst (k : ℕ) : ℝ :=
  Real.sqrt Real.pi ^ k / Real.Gamma ((k : ℝ) / 2 + 1) / (2 : ℝ) ^ (2 * k)

/-- **The uniform escape constant** of the glue estimate: for a `k`-plane, a distance `δ`
whose flowed wedge is `c`-dominated (and whose flowed lattice has first minimum `≥ c`),
`δ ≥ glueConst · H^{−1/α}`.  It is independent of the plane, of the family and of the time. -/
noncomputable def glueConst (d k l : ℕ) (c : ℝ) : ℝ :=
  (2 * Real.sqrt (k : ℝ))⁻¹ *
    min ((ballConst k * c ^ k / (((k : ℝ) + 1) * (2 : ℝ) ^ k)) ^ (1 / alpha d k l)) 1

theorem ballConst_pos (k : ℕ) : 0 < ballConst k := by
  have h1 : (0:ℝ) < Real.sqrt Real.pi ^ k := pow_pos (Real.sqrt_pos.mpr Real.pi_pos) k
  have h2 : 0 < Real.Gamma ((k:ℝ)/2+1) := Real.Gamma_pos_of_pos (by positivity)
  have h3 : 0 < (2:ℝ)^(2*k) := pow_pos (by norm_num) _
  rw [ballConst]
  exact div_pos (div_pos h1 h2) h3

theorem glueConst_pos {d k l : ℕ} (hk : 1 ≤ k) {c : ℝ} (hc : 0 < c) :
    0 < glueConst d k l c := by
  have hk0 : 0 < k := hk
  rw [glueConst]
  have hbase : (0:ℝ) < ballConst k * c ^ k / (((k : ℝ) + 1) * (2 : ℝ) ^ k) :=
    div_pos (mul_pos (ballConst_pos k) (pow_pos hc k)) (by positivity)
  have hm : 0 < min ((ballConst k * c ^ k / (((k : ℝ) + 1) * (2 : ℝ) ^ k)) ^ (1 / alpha d k l))
      (1 : ℝ) :=
    lt_min (Real.rpow_pos_of_pos hbase (1 / alpha d k l)) one_pos
  exact mul_pos (inv_pos.mpr (by positivity)) hm

theorem glueConst_le_inv {d k l : ℕ} {c : ℝ} :
    glueConst d k l c ≤ (2 * Real.sqrt (k : ℝ))⁻¹ := by
  have hnn : (0:ℝ) ≤ (2 * Real.sqrt (k:ℝ))⁻¹ := inv_nonneg.mpr (by positivity)
  rw [glueConst]
  simpa using mul_le_mul_of_nonneg_left (min_le_right
    ((ballConst k * c ^ k / (((k : ℝ) + 1) * (2 : ℝ) ^ k)) ^ (1 / alpha d k l)) (1:ℝ)) hnn

theorem glueConst_nonneg {d k l : ℕ} {c : ℝ} (hc : 0 < c) : 0 ≤ glueConst d k l c := by
  have hnn : (0:ℝ) ≤ (2 * Real.sqrt (k:ℝ))⁻¹ := inv_nonneg.mpr (by positivity)
  have hbase : (0:ℝ) ≤ ballConst k * c ^ k / (((k : ℝ) + 1) * (2 : ℝ) ^ k) :=
    le_of_lt (div_pos (mul_pos (ballConst_pos k) (pow_pos hc k)) (by positivity))
  have hA : (0:ℝ) ≤ (ballConst k * c ^ k / (((k : ℝ) + 1) * (2 : ℝ) ^ k)) ^ (1 / alpha d k l) :=
    Real.rpow_nonneg hbase _
  rw [glueConst]
  exact mul_nonneg hnn (le_min hA zero_le_one)

theorem glue_family {l k : ℕ} (hk : 1 ≤ k) (hkl : k ≤ l) (hld : l < d)
    (x : Submodule ℝ ℝᵈ) (hx : Module.finrank ℝ x = l)
    (s : ℝᵈ ≃ₗᵢ[ℝ] ℝᵈ) (hs : Submodule.map (s : ℝᵈ →ₗ[ℝ] ℝᵈ) x
      = Submission.WedgeBlocks.modelX (d := d) l)
    {c : ℝ} (hc : 0 < c)
    (hslow : ∀ t : ℝ, c ≤ Commons.Lattice.SuccessiveMinima.successiveMinimum
       (Submission.ImageLattice.imageSpan (flowMap (d := d) l s t)) 1)
    (m : Fin k → ℝᵈ) (hmem : ∀ i, m i ∈ intPoints (d := d)) (hmLI : LinearIndependent ℝ m)
    (hδpos : 0 < LinearSubspaces.distSubspaces (Submodule.span ℝ (Set.range m)) x) :
    LinearSubspaces.distSubspaces (Submodule.span ℝ (Set.range m)) x ≥
      glueConst d k l c * ‖exteriorPower.ιMulti ℝ k m‖ ^ (-(1 / alpha d k l)) := by
  classical
  have hk0 : 0 < k := hk
  have hl0 : 0 < l := lt_of_lt_of_le hk0 hkl
  have hdl : (0 : ℝ) < (d : ℝ) - (l : ℝ) := by
    have : (l : ℝ) < (d : ℝ) := by exact_mod_cast hld
    linarith
  have hS : 0 < rateS d l := by
    have hlne : (0:ℝ) < (l:ℝ) := by exact_mod_cast hl0
    dsimp [rateS]; positivity
  have hα : 0 < alpha d k l := alpha_pos hk hl0 hld
  set V : Submodule ℝ ℝᵈ := Submodule.span ℝ (Set.range m) with hVdef
  set δ : ℝ := LinearSubspaces.distSubspaces V x with hδdef
  have hVfr : Module.finrank ℝ V = k := by
    rw [hVdef]; exact Submission.PlaneFinrank.finrank_span_range m hmLI
  have hVne : V ≠ ⊥ := by
    rw [hVdef]; exact Submission.PlaneFinrank.span_range_ne_bot hk0 m hmLI
  have hxne : x ≠ ⊥ := by
    intro h; rw [h] at hx; simp at hx; omega
  have hδbridge : δ = Submission.ProjectionDistance.planeResidual V x := by
    rw [hδdef]
    exact Submission.Bridge.distSubspaces_eq_planeResidual_of_le V x (by rw [hVfr, hx]; exact hkl)
      hVne hxne
  have hH1 : (1:ℝ) ≤ ‖exteriorPower.ιMulti ℝ k m‖ := by
    refine Commons.Analysis.InnerProductSpace.intWedge_norm_ge_one hk m ?_ hmLI
    intro r t
    exact intPoints_coord_int (m r) (hmem r) t
  by_cases hsmall : δ ≤ 1 / (2 * Real.sqrt (k : ℝ))
  · -- SMALL CASE
    have hsqrtk_pos : 0 < Real.sqrt (k:ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hk0)
    have hsqrtk1 : (1:ℝ) ≤ Real.sqrt (k:ℝ) := Real.one_le_sqrt.mpr (by exact_mod_cast hk)
    have hδ12 : δ ≤ 1/2 := by
      refine le_trans hsmall ?_
      rw [div_le_div_iff₀ (by positivity) (by norm_num : (0:ℝ) < 2)]
      linarith
    set X : ℝ := 2 * Real.sqrt (k:ℝ) * δ with hXdef
    have hXpos : 0 < X := by rw [hXdef]; positivity
    set t : ℝ := Real.log (1/X) / rateS d l with htdef
    have htS : t * rateS d l = Real.log (1/X) := by
      rw [htdef, div_mul_cancel₀ _ (ne_of_gt hS)]
    have htexp : Real.exp (-(t * rateS d l)) = X := by
      rw [htS, Real.exp_neg, Real.exp_log (by positivity), one_div, inv_inv]
    -- the upper bound
    set u : Fin k → ℝᵈ := fun i => s (m i) with hudef
    have hu : LinearIndependent ℝ u := by
      rw [hudef]
      have := hmLI.map' (s : ℝᵈ →ₗ[ℝ] ℝᵈ) (by rw [LinearMap.ker_eq_bot]; exact s.injective)
      simpa [Function.comp_def] using this
    have hrange : Set.range u = ((s : ℝᵈ →ₗ[ℝ] ℝᵈ) : ℝᵈ → ℝᵈ) '' Set.range m := by
      rw [hudef,
        show (fun i => s (m i)) = ((s : ℝᵈ →ₗ[ℝ] ℝᵈ) : ℝᵈ → ℝᵈ) ∘ m from rfl, Set.range_comp]
    have hspan_u : Submodule.span ℝ (Set.range u) = V.map (s : ℝᵈ →ₗ[ℝ] ℝᵈ) := by
      rw [hVdef, Submodule.map_span, ← hrange]
    have hdist_u : Submission.ProjectionDistance.planeResidual
        (Submodule.span ℝ (Set.range u)) (Submission.WedgeBlocks.modelX (d := d) l) = δ := by
      rw [hspan_u, hδbridge, ← hs]
      exact Submission.Bridge.Isometry.planeResidual_map_map V x s
    have hbot : (Submodule.span ℝ (Set.range u)) ⊓
        (Submission.WedgeBlocks.modelX (d := d) l)ᗮ = ⊥ := by
      by_contra hne
      have h1 := one_le_planeResidual_of_meet_ne_bot
        (Submodule.span ℝ (Set.range u)) (Submission.WedgeBlocks.modelX (d := d) l) hne
      rw [hdist_u] at h1
      linarith
    have hup := model_wedge_flow_upper (d := d) (k := k) (l := l) hk0 hkl hld
      hδpos hδ12 u hu hbot hdist_u t (by rw [htexp, hXdef])
    -- rewrite the upper bound
    have hmap : exteriorPower.ιMulti ℝ k (fun i => flowMap (d := d) l s t (m i)) =
        exteriorPower.map k (Submission.DiagonalFlow.scaleMap
          (Submission.DiagonalFlow.twoScale (Real.exp (-t / (l : ℝ)))
            (Real.exp (t / ((d : ℝ) - (l : ℝ)))) l)) (exteriorPower.ιMulti ℝ k u) := by
      rw [exteriorPower.map_apply_ιMulti]
      congr 1
    have hnormu : ‖exteriorPower.ιMulti ℝ k u‖ = ‖exteriorPower.ιMulti ℝ k m‖ := by
      rw [hudef]
      exact Commons.Analysis.InnerProductSpace.norm_iMulti_comp_isometry s m
    -- the lower bound
    set g : ℝᵈ ≃ₗ[ℝ] ℝᵈ := flowMap (d := d) l s t with hgdef
    set Λ : Submodule ℤ ℝᵈ := Submission.ImageLattice.imageSpan g with hΛdef
    have hgmem : ∀ i, g (m i) ∈ Λ := by
      intro i
      rw [hΛdef]
      rw [Submission.ImageLattice.imageSpan_eq_map]
      exact Submodule.mem_map.mpr ⟨m i, hmem i, rfl⟩
    set w : Fin k → Λ := fun i => ⟨g (m i), hgmem i⟩ with hwdef
    have hwLI : LinearIndependent ℤ w := by
      apply LinearIndependent.of_comp (Submodule.subtype Λ)
      have hcomp : (Submodule.subtype Λ) ∘ w = (fun i => g (m i)) := by
        funext i; rfl
      rw [hcomp]
      have h1 : LinearIndependent ℤ (fun i => g (m i)) := by
        have h2 : LinearIndependent ℝ (fun i => g (m i)) := by
          have := hmLI.map' (g : ℝᵈ →ₗ[ℝ] ℝᵈ) (by rw [LinearMap.ker_eq_bot]; exact g.injective)
          simpa [Function.comp_def] using this
        exact h2.restrict_scalars' ℤ
      exact h1
    have hlow := Commons.Lattice.Minkowski.wedge_norm_ge_pow_uniform (E := ℝᵈ) Λ (le_of_lt hc)
      (hslow t) w hwLI
    -- hlow : (ballConst k) * c^k ≤ ‖ιMulti ℝ k (fun i => (w i : ℝᵈ))‖
    have hwval : (fun i => (w i : ℝᵈ)) = (fun i => flowMap (d := d) l s t (m i)) := by
      funext i; rw [hwdef]
    rw [hwval] at hlow
    -- combine: C2 * c^k ≤ Φ ≤ C1 * X^α * H
    have hαeq : alpha d k l = ((k:ℝ)/(l:ℝ)) / rateS d l := by
      have hlne : (l:ℝ) ≠ 0 := ne_of_gt (by exact_mod_cast hl0)
      have hdlne : (d:ℝ) - (l:ℝ) ≠ 0 := ne_of_gt hdl
      have hdne : (d:ℝ) ≠ 0 := by
        have : (0:ℝ) < (d:ℝ) := by
          have : 0 < d := lt_of_lt_of_le hl0 (le_of_lt hld); exact_mod_cast this
        exact ne_of_gt this
      dsimp [alpha, rateS]; field_simp; ring
    have hXα : Real.exp (-(t * ((k:ℝ) / (l:ℝ)))) = X ^ (alpha d k l) := by
      have h1 : t * ((k:ℝ)/(l:ℝ)) = Real.log (1/X) * alpha d k l := by
        have h3 : t * ((k:ℝ)/(l:ℝ)) = (t * rateS d l) * (((k:ℝ)/(l:ℝ)) / rateS d l) := by
          field_simp
        rw [h3, htS, ← hαeq]
      have h2 : -(t * ((k:ℝ)/(l:ℝ))) = Real.log X * alpha d k l := by
        rw [h1, one_div, Real.log_inv]; ring
      rw [Real.rpow_def_of_pos hXpos, h2]
    have hC1pos : (0:ℝ) < ((k:ℝ) + 1) * (2:ℝ)^k := by positivity
    have hmain : ballConst k * c^k ≤ ((k:ℝ)+1) * (2:ℝ)^k * X ^ (alpha d k l) *
        ‖exteriorPower.ιMulti ℝ k m‖ := by
      calc ballConst k * c^k
          ≤ ‖exteriorPower.ιMulti ℝ k (fun i => flowMap (d:=d) l s t (m i))‖ := hlow
        _ = ‖exteriorPower.map k (Submission.DiagonalFlow.scaleMap
              (Submission.DiagonalFlow.twoScale (Real.exp (-t / (l : ℝ)))
                (Real.exp (t / ((d : ℝ) - (l : ℝ)))) l)) (exteriorPower.ιMulti ℝ k u)‖ := by
              rw [hmap]
        _ ≤ ((k:ℝ)+1) * (2:ℝ)^k * Real.exp (-(t * ((k:ℝ)/(l:ℝ)))) *
              ‖exteriorPower.ιMulti ℝ k u‖ := hup
        _ = ((k:ℝ)+1) * (2:ℝ)^k * X ^ (alpha d k l) * ‖exteriorPower.ιMulti ℝ k m‖ := by
              rw [hXα, hnormu]
    have hX1 : X ≤ 1 := by
      rw [hXdef]
      have hk2 : (0:ℝ) < 2 * Real.sqrt (k:ℝ) := by positivity
      have hle := (le_div_iff₀ hk2).mp hsmall
      linarith [hle]
    have hchase := Submission.EscapeGlue.chase (δ := X) (H := ‖exteriorPower.ιMulti ℝ k m‖)
      (C1 := ((k:ℝ)+1) * (2:ℝ)^k) (C2 := ballConst k * c^k) (p := alpha d k l)
      hXpos hX1 hH1 hC1pos (mul_pos (ballConst_pos k) (pow_pos hc k)) hα hmain
    have hXeq : X = 2 * Real.sqrt (k:ℝ) * δ := hXdef
    rw [hXeq] at hchase
    have hstep : (2 * Real.sqrt (k:ℝ))⁻¹ *
        ((ballConst k * c^k / (((k:ℝ)+1) * (2:ℝ)^k)) ^ (1/alpha d k l)
          * ‖exteriorPower.ιMulti ℝ k m‖ ^ (-(1/alpha d k l)))
        ≤ δ := by
      have h0 : (2 * Real.sqrt (k:ℝ))⁻¹ *
          ((ballConst k * c^k / (((k:ℝ)+1) * (2:ℝ)^k)) ^ (1/alpha d k l)
            * ‖exteriorPower.ιMulti ℝ k m‖ ^ (-(1/alpha d k l)))
          ≤ (2 * Real.sqrt (k:ℝ))⁻¹ * (2 * Real.sqrt (k:ℝ) * δ) :=
        mul_le_mul_of_nonneg_left hchase (by positivity)
      rw [inv_mul_cancel_left₀ (ne_of_gt (by positivity : (0:ℝ) < 2 * Real.sqrt (k:ℝ)))] at h0
      exact h0
    have hgluele : glueConst d k l c * ‖exteriorPower.ιMulti ℝ k m‖ ^ (-(1/alpha d k l)) ≤
        (2 * Real.sqrt (k:ℝ))⁻¹ *
          ((ballConst k * c^k / (((k:ℝ)+1) * (2:ℝ)^k)) ^ (1/alpha d k l)
            * ‖exteriorPower.ιMulti ℝ k m‖ ^ (-(1/alpha d k l))) := by
      rw [glueConst]
      have hHnn : (0:ℝ) ≤ ‖exteriorPower.ιMulti ℝ k m‖ ^ (-(1/alpha d k l)) :=
        Real.rpow_nonneg (norm_nonneg _) _
      have hm : min ((ballConst k * c^k / (((k:ℝ)+1) * (2:ℝ)^k)) ^ (1/alpha d k l)) 1 ≤
          (ballConst k * c^k / (((k:ℝ)+1) * (2:ℝ)^k)) ^ (1/alpha d k l) := min_le_left _ _
      calc (2 * Real.sqrt (k:ℝ))⁻¹ *
              min ((ballConst k * c^k / (((k:ℝ)+1) * (2:ℝ)^k)) ^ (1/alpha d k l)) 1 *
              ‖exteriorPower.ιMulti ℝ k m‖ ^ (-(1/alpha d k l))
          = (2 * Real.sqrt (k:ℝ))⁻¹ *
              (min ((ballConst k * c^k / (((k:ℝ)+1) * (2:ℝ)^k)) ^ (1/alpha d k l)) 1 *
              ‖exteriorPower.ιMulti ℝ k m‖ ^ (-(1/alpha d k l))) := by ring
        _ ≤ (2 * Real.sqrt (k:ℝ))⁻¹ *
              (((ballConst k * c^k / (((k:ℝ)+1) * (2:ℝ)^k)) ^ (1/alpha d k l)) *
              ‖exteriorPower.ιMulti ℝ k m‖ ^ (-(1/alpha d k l))) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hm hHnn) (by positivity)
    exact hgluele.trans hstep
  · -- LARGE CASE
    push Not at hsmall
    have hHinv : ‖exteriorPower.ιMulti ℝ k m‖ ^ (-(1/alpha d k l)) ≤ 1 := by
      have hpos : (0:ℝ) < ‖exteriorPower.ιMulti ℝ k m‖ := lt_of_lt_of_le one_pos hH1
      rw [Real.rpow_neg hpos.le]
      rw [inv_le_one₀ (Real.rpow_pos_of_pos hpos _)]
      exact Real.one_le_rpow hH1 (by positivity)
    calc glueConst d k l c * ‖exteriorPower.ιMulti ℝ k m‖ ^ (-(1/alpha d k l))
        ≤ glueConst d k l c * 1 := mul_le_mul_of_nonneg_left hHinv (glueConst_nonneg (k := k) (d := d) (l := l) hc)
      _ ≤ (2 * Real.sqrt (k:ℝ))⁻¹ * 1 := by
          exact mul_le_mul_of_nonneg_right (glueConst_le_inv (d := d) (k := k) (l := l) (c := c))
            zero_le_one
      _ = 1 / (2 * Real.sqrt (k:ℝ)) := by ring
      _ ≤ δ := le_of_lt hsmall


open Submission.Heights in
/-- The integer lattice of a rational subspace is contained in `ℤᵈ`. -/
lemma imageLattice_le_intPoints (V : Submodule ℝ ℝᵈ) :
    Submission.Heights.imageLattice V ≤ ℤᵈ := by
  intro x hx
  rw [Submission.Heights.imageLattice] at hx
  rcases Submodule.mem_map.mp hx with ⟨y, hy, rfl⟩
  exact hy

open Submission.Heights in
/-- The chosen-basis family of a rational subspace spans it over `ℝ`. -/
lemma span_range_cbFamily (V : Submodule ℝ ℝᵈ) (hV : IsRational V) :
    Submodule.span ℝ (Set.range (cbFamily V hV)) = V := by
  have hfam : cbFamily V hV = (fun i => ((chosenBasis V hV i : V) : ℝᵈ)) := rfl
  rw [hfam]
  have h1 : Submodule.span ℝ (Set.range (fun i => ((chosenBasis V hV i : V) : ℝᵈ)))
      = Submodule.map (V.subtype.restrictScalars ℝ)
          (Submodule.span ℝ (Set.range (chosenBasis V hV))) := by
    rw [Submodule.map_span]
    congr 1
    ext y
    simp only [Set.mem_image, Set.mem_range]
    constructor
    · rintro ⟨i, rfl⟩; exact ⟨chosenBasis V hV i, ⟨i, rfl⟩, rfl⟩
    · rintro ⟨z, ⟨i, rfl⟩, rfl⟩; exact ⟨i, rfl⟩
  rw [h1, (chosenBasis V hV).span_eq, Submodule.map_top]
  exact Submodule.range_subtype V

/-- Reindexing `ιMulti` along an equality of index types preserves its norm. -/
lemma norm_iMulti_cast {n k : ℕ} (h : n = k) (v : Fin n → ℝᵈ) :
    ‖exteriorPower.ιMulti ℝ k (fun i => v (Fin.cast h.symm i))‖ =
      ‖exteriorPower.ιMulti ℝ n v‖ := by
  subst h
  rfl

theorem glue_rational {l k : ℕ} (hk : 1 ≤ k) (hkl : k ≤ l) (hld : l < d)
    (x : Submodule ℝ ℝᵈ) (hx : Module.finrank ℝ x = l)
    (s : ℝᵈ ≃ₗᵢ[ℝ] ℝᵈ) (hs : Submodule.map (s : ℝᵈ →ₗ[ℝ] ℝᵈ) x
      = Submission.WedgeBlocks.modelX (d := d) l)
    {c : ℝ} (hc : 0 < c)
    (hslow : ∀ t : ℝ, c ≤ Commons.Lattice.SuccessiveMinima.successiveMinimum
       (Submission.ImageLattice.imageSpan (flowMap (d := d) l s t)) 1)
    (v : Submodule ℝ ℝᵈ) (hv : IsRational v) (hvk : Module.finrank ℝ v = k)
    (hδpos : 0 < LinearSubspaces.distSubspaces v x) :
    LinearSubspaces.distSubspaces v x ≥
      glueConst d k l c * LinearSubspaces.height v hv ^ (-(1 / alpha d k l)) := by
  classical
  set m : Fin k → ℝᵈ := fun i => Submission.Heights.cbFamily v hv (Fin.cast hvk.symm i) with hmdef
  have hmem : ∀ i, m i ∈ ℤᵈ := by
    intro i
    refine imageLattice_le_intPoints v ?_
    rw [← Submission.Heights.chosenBasis_span_lattice v hv]
    exact Submodule.subset_span ⟨Fin.cast hvk.symm i, rfl⟩
  have hmLI : LinearIndependent ℝ m := by
    have hZ : LinearIndependent ℤ m := by
      have h1 : LinearIndependent ℤ (Submission.Heights.cbFamily v hv) :=
        Submission.Heights.chosenBasis_linearIndependent v hv
      have h2 := h1.comp (Fin.cast hvk.symm) (Fin.cast_injective hvk.symm)
      simpa [hmdef, Function.comp_def] using h2
    exact Commons.Analysis.InnerProductSpace.intCoords_linearIndependent_real hmem hZ
  have hspan : Submodule.span ℝ (Set.range m) = v := by
    have hrange : Set.range m = Set.range (Submission.Heights.cbFamily v hv) := by
      rw [hmdef, show (fun i : Fin k => Submission.Heights.cbFamily v hv (Fin.cast hvk.symm i))
          = Submission.Heights.cbFamily v hv ∘ (Fin.cast hvk.symm) from rfl, Set.range_comp]
      have hsurj : Function.Surjective (Fin.cast hvk.symm) :=
        fun j => ⟨Fin.cast hvk j, Fin.ext (by simp only [Fin.val_cast])⟩
      rw [Set.range_eq_univ.mpr hsurj, Set.image_univ]
    rw [hrange]
    exact span_range_cbFamily v hv
  have hnorm : ‖exteriorPower.ιMulti ℝ k m‖ =
      ‖exteriorPower.ιMulti ℝ (Module.finrank ℝ v) (Submission.Heights.cbFamily v hv)‖ := by
    rw [← norm_iMulti_cast hvk (Submission.Heights.cbFamily v hv), hmdef]
  have hheight : LinearSubspaces.height v hv =
      ‖exteriorPower.ιMulti ℝ k m‖ := by
    rw [hnorm]
    rfl
  have hδ : 0 < LinearSubspaces.distSubspaces (Submodule.span ℝ (Set.range m)) x := by
    rw [hspan]; exact hδpos
  have h := glue_family (d := d) (l := l) (k := k) hk hkl hld x hx s hs
    hc hslow m hmem hmLI hδ
  rw [hspan, ← hheight] at h
  exact h


open Submission.Heights in
/-- The height of a nonzero rational subspace is at least `1`. -/
lemma height_ge_one (v : Submodule ℝ ℝᵈ) (hv : IsRational v) :
    (1:ℝ) ≤ LinearSubspaces.height v hv := by
  have hmem : ∀ i : Fin (Module.finrank ℝ v), Submission.Heights.cbFamily v hv i ∈
      Submodule.span ℤ (Set.range (EuclideanSpace.basisFun (Fin d) ℝ)) := by
    intro i
    have h1 : Submission.Heights.cbFamily v hv i ∈ Submission.Heights.imageLattice v := by
      rw [← Submission.Heights.chosenBasis_span_lattice v hv]
      exact Submodule.subset_span ⟨i, rfl⟩
    have h2 := Submission.EscapeGlue.imageLattice_le_intPoints (d := d) v h1
    simpa only [LinearSubspaces.intPoints, OrthonormalBasis.coe_toBasis] using h2
  have hli : LinearIndependent ℤ (Submission.Heights.cbFamily v hv) :=
    Submission.Heights.chosenBasis_linearIndependent v hv
  have := Commons.Analysis.InnerProductSpace.norm_iMulti_ge_one_of_mem_intPoints
    (Submission.Heights.cbFamily v hv) hmem hli
  exact this

theorem conjunct2_upper {l k : ℕ} (hk : 1 ≤ k) (hkl : k ≤ l) (hld : l < d)
    (x : Submodule ℝ ℝᵈ) (hx : Module.finrank ℝ x = l)
    (s : ℝᵈ ≃ₗᵢ[ℝ] ℝᵈ) (hs : Submodule.map (s : ℝᵈ →ₗ[ℝ] ℝᵈ) x
      = Submission.WedgeBlocks.modelX (d := d) l)
    {c : ℝ} (hc : 0 < c)
    (hslow : ∀ t : ℝ, c ≤ Commons.Lattice.SuccessiveMinima.successiveMinimum
       (Submission.ImageLattice.imageSpan (flowMap (d := d) l s t)) 1)
    (hδ : ∀ v : Submodule ℝ ℝᵈ, IsRational v → Module.finrank ℝ v = k →
      0 < LinearSubspaces.distSubspaces v x) :
    LinearSubspaces.diophantineExponent k x ≤
      ENNReal.ofReal (1 / alpha d k l) := by
  have hl0 : 0 < l := lt_of_lt_of_le hk hkl
  refine diophantineExponent_le_of_forall_gt k x
    (le_of_lt (div_pos one_pos (alpha_pos hk hl0 hld))) ?_
  intro β hβ
  refine ⟨glueConst d k l c,
    glueConst_pos (d := d) (l := l) hk hc, ?_⟩
  intro v hvk hv
  have h1 := glue_rational (d := d) hk hkl hld x hx s hs hc hslow v hv hvk
    (hδ v hv hvk)
  have hH : (1:ℝ) ≤ LinearSubspaces.height v hv := height_ge_one v hv
  have h2 : LinearSubspaces.height v hv ^ (-β) ≤
      LinearSubspaces.height v hv ^ (-(1 / alpha d k l)) :=
    Real.rpow_le_rpow_of_exponent_le hH (by linarith)
  calc glueConst d k l c * LinearSubspaces.height v hv ^ (-β)
      ≤ glueConst d k l c *
          LinearSubspaces.height v hv ^ (-(1 / alpha d k l)) :=
        mul_le_mul_of_nonneg_left h2 (glueConst_nonneg (d := d) (l := l) hc)
    _ ≤ LinearSubspaces.distSubspaces v x := h1

/-- **Conjunct 2 from a witness.**  If conjunct 1 holds (the uniform lower bound) and there is an
`ℓ`-plane `x` with a slow-escape orthogonal representative and all its rational `k`-planes at
positive distance, then `diophantineExponent k x` equals the critical exponent. -/
theorem conjunct2_of_witness {l k : ℕ} (hk : 1 ≤ k) (hkl : k ≤ l) (hld : l < d)
    (h1 : ∀ x : Submodule ℝ ℝᵈ, Module.finrank ℝ x = l →
      LinearSubspaces.diophantineExponent k x ≥ (d : ℝ≥0∞) / (k * (d - l)))
    (hW : ∃ x : Submodule ℝ ℝᵈ, Module.finrank ℝ x = l ∧
      ∃ s : ℝᵈ ≃ₗᵢ[ℝ] ℝᵈ, Submodule.map (s : ℝᵈ →ₗ[ℝ] ℝᵈ) x
          = Submission.WedgeBlocks.modelX (d := d) l ∧
      ∃ c : ℝ, 0 < c ∧ (∀ t : ℝ, c ≤ Commons.Lattice.SuccessiveMinima.successiveMinimum
          (Submission.ImageLattice.imageSpan (flowMap (d := d) l s t)) 1) ∧
      (∀ v : Submodule ℝ ℝᵈ, IsRational v → Module.finrank ℝ v = k →
        0 < LinearSubspaces.distSubspaces v x)) :
    ∃ x : Submodule ℝ ℝᵈ, Module.finrank ℝ x = l ∧
      LinearSubspaces.diophantineExponent k x = (d : ℝ≥0∞) / (k * (d - l)) := by
  obtain ⟨x, hx, s, hs, c, hc, hslow, hδ⟩ := hW
  refine ⟨x, hx, le_antisymm ?_ (h1 x hx)⟩
  have hl0 : 0 < l := lt_of_lt_of_le hk hkl
  have hαval : (1 / alpha d k l) = (d : ℝ) / ((k : ℝ) * ((d : ℝ) - (l : ℝ))) := by
    have hdl : (0:ℝ) < (d:ℝ) - (l:ℝ) := by
      have : (l:ℝ) < (d:ℝ) := by exact_mod_cast hld
      linarith
    have hd : (d:ℝ) ≠ 0 := by
      have : (0:ℝ) < (d:ℝ) := by
        have : 0 < d := lt_of_lt_of_le hl0 (le_of_lt hld); exact_mod_cast this
      exact ne_of_gt this
    have hkne : (k:ℝ) ≠ 0 := ne_of_gt (by exact_mod_cast hk)
    rw [alpha]
    field_simp
  have h := conjunct2_upper (d := d) hk hkl hld x hx s hs hc hslow hδ
  rw [hαval] at h
  rw [← Commons.Analysis.ENNReal.natCast_div_natCast_sub_mul_ofReal (d := d) (l := l) (k := k)
    (hld := hld) (hk := hk)] at h
  exact h


/-- If the projection residual of a subspace is `≤ 0` then the subspace is contained in the
target: every unit vector of `V` is at residual `≤ 0`, hence (residuals being norms) at
residual `0`, hence lies in `x`. -/
lemma le_of_planeResidual_le_zero {V x : Submodule ℝ ℝᵈ}
    (h : Submission.ProjectionDistance.planeResidual V x ≤ 0) : V ≤ x := by
  intro u hu
  by_cases hu0 : u = 0
  · subst hu0; exact Submodule.zero_mem x
  have hun : ‖u‖ ≠ 0 := (norm_pos_iff.mpr hu0).ne'
  set ũ : ℝᵈ := (‖u‖⁻¹) • u with hũ
  have hũV : ũ ∈ V := Submodule.smul_mem _ _ hu
  have hũ1 : ‖ũ‖ = 1 := by
    rw [hũ, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_nonneg (norm_nonneg u),
      inv_mul_cancel₀ hun]
  have hle : ‖ũ - ((x.orthogonalProjectionOnto ũ) : ℝᵈ)‖ ≤
      Submission.ProjectionDistance.planeResidual V x :=
    le_csSup (bddAbove_residualSet V x)
      ⟨ũ, hũV, hũ1, rfl⟩
  have hzero : ‖ũ - ((x.orthogonalProjectionOnto ũ) : ℝᵈ)‖ = 0 :=
    le_antisymm (le_trans hle h) (norm_nonneg _)
  have hsub : ũ - ((x.orthogonalProjectionOnto ũ) : ℝᵈ) = 0 := norm_eq_zero.mp hzero
  have hũx : ũ ∈ x := by
    have hfix : ((x.orthogonalProjectionOnto ũ) : ℝᵈ) = ũ := by
      rw [sub_eq_zero] at hsub; exact hsub.symm
    rw [← hfix]; exact (x.orthogonalProjectionOnto ũ).2
  have hueq : u = ‖u‖ • ũ := by
    rw [hũ, smul_smul, mul_inv_cancel₀ hun, one_smul]
  rw [hueq]
  exact Submodule.smul_mem _ _ hũx

/-- If a subspace `x` contains no nonzero integer vector, then every subspace `v` which contains
one is at positive distance from `x`. -/
theorem dist_pos_of_intPoints_sep {x v : Submodule ℝ ℝᵈ}
    (hx : ∀ n : ℝᵈ, n ∈ ℤᵈ → n ∈ x → n = 0)
    (hvnz : ∃ n : ℝᵈ, n ∈ v ∧ n ∈ ℤᵈ ∧ n ≠ 0)
    (hkl : Module.finrank ℝ v ≤ Module.finrank ℝ x) (hvn : v ≠ ⊥) (hxn : x ≠ ⊥) :
    0 < LinearSubspaces.distSubspaces v x := by
  rw [Submission.Bridge.distSubspaces_eq_planeResidual_of_le v x hkl hvn hxn]
  by_contra hcon
  have hvx : v ≤ x := le_of_planeResidual_le_zero (le_of_not_gt hcon)
  obtain ⟨n, hnv, hnZ, hn0⟩ := hvnz
  exact hn0 (hx n hnZ (hvx hnv))

end Submission.EscapeGlue

end
