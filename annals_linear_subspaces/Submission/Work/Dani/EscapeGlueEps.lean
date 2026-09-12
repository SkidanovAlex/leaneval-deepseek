import Mathlib
import ChallengeDeps
import Submission.Work.Dani.EscapeGlue
import Submission.GeometryOfNumbers.FlowSpanSxLower

/-!
# The `ε`-version of the escape glue (de Saxcé, Corollary 1: `β_k(x) ≤ d/(k(d−ℓ))`)

`Submission.EscapeGlue` proves the escape direction of conjunct 2 under the **uniform** slow
escape hypothesis `∀ t, c ≤ λ₁(a_t s_x ℤᵈ)`.  That hypothesis is far too strong: it fails for
almost every `x` (for `d = 2`, `ℓ = 1` it says that the slope is badly approximable).  The
correct hypothesis, matching the paper's Corollary 1, is the **zero escape rate**
`(1/t)·log λ₁(a_t s_x ℤᵈ) → 0`, i.e. for every `ε > 0` and all large `t`,
`e^{−εt} ≤ λ₁(a_t s_x ℤᵈ)`.

This file redoes the glue with that weaker hypothesis.  The only change in the arithmetic is
that the Mahler lower bound now reads `ballConst k · (c·e^{−εt})^k ≤ Φ`, i.e. the flowed wedge
acquires the factor `e^{−kεt} = X^{kε/S}`; the resulting exponent is
`1/(α − kε/S) = 1/(α(1 − εℓ))`, which tends to `1/α = d/(k(d−ℓ))` as `ε → 0`.

Module `Submission.Work.Dani.EscapeGlueEps`, namespace `Submission.EscapeGlueEps`.
-/

noncomputable section

open LinearSubspaces ENNReal Real Module exteriorPower InnerProductGeometry
open scoped LinearAlgebra.Projectivization ENNReal

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedSectionVars false

namespace Submission.EscapeGlueEps

variable {d : ℕ}
local notation "ℝᵈ" => EuclideanSpace ℝ (Fin d)
local notation "ℤᵈ" => intPoints

/-- The escape exponent `p = α − kε/S` at escape rate `ε`; the glue produces the exponent
`1/p` in `d(v,x) ≳ H(v)^{−1/p}`.  With `ε = 0` this is `α = k(d−ℓ)/d`. -/
def escapeExp (d k l : ℕ) (ε : ℝ) : ℝ :=
  Submission.EscapeGlue.alpha d k l - (k : ℝ) * ε / Submission.EscapeGlue.rateS d l

/-- `p = α(1 − εℓ)`. -/
theorem escapeExp_eq {l k : ℕ} (hl0 : 0 < l) (hld : l < d) (ε : ℝ) :
    escapeExp d k l ε = Submission.EscapeGlue.alpha d k l * (1 - ε * (l : ℝ)) := by
  have hl : (l : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hl0)
  have hdl : ((d : ℝ) - (l : ℝ)) ≠ 0 := by
    have : (l : ℝ) < (d : ℝ) := by exact_mod_cast hld
    linarith
  rw [escapeExp, Submission.EscapeGlue.alpha, Submission.EscapeGlue.rateS]
  field_simp
  ring

theorem escapeExp_pos {l k : ℕ} (hk : 1 ≤ k) (hl0 : 0 < l) (hld : l < d) {ε : ℝ}
    (hεl : ε * (l : ℝ) < 1) : 0 < escapeExp d k l ε := by
  rw [escapeExp_eq (d := d) hl0 hld]
  have hα : 0 < Submission.EscapeGlue.alpha d k l :=
    Submission.EscapeGlue.alpha_pos hk hl0 hld
  have h1 : (0 : ℝ) < 1 - ε * (l : ℝ) := by linarith
  exact mul_pos hα h1

/-- The uniform escape constant of the `ε`-glue. -/
noncomputable def glueConstEps (d k l : ℕ) (ε c : ℝ) : ℝ :=
  (2 * Real.sqrt (k : ℝ))⁻¹ *
    min ((Submission.EscapeGlue.ballConst k * c ^ k / (((k : ℝ) + 1) * (2 : ℝ) ^ k)) ^
      (1 / escapeExp d k l ε)) 1

theorem glueConstEps_pos {d k l : ℕ} {ε c : ℝ} (hk : 1 ≤ k) (_hp : 0 < escapeExp d k l ε)
    (hc : 0 < c) :
    0 < glueConstEps d k l ε c := by
  have hbase : (0 : ℝ) < Submission.EscapeGlue.ballConst k * c ^ k /
      (((k : ℝ) + 1) * (2 : ℝ) ^ k) :=
    div_pos (mul_pos (Submission.EscapeGlue.ballConst_pos k) (pow_pos hc k)) (by positivity)
  have hm : 0 < min ((Submission.EscapeGlue.ballConst k * c ^ k /
      (((k : ℝ) + 1) * (2 : ℝ) ^ k)) ^ (1 / escapeExp d k l ε)) (1 : ℝ) :=
    lt_min (Real.rpow_pos_of_pos hbase (1 / escapeExp d k l ε)) one_pos
  rw [glueConstEps]
  exact mul_pos (inv_pos.mpr (by positivity)) hm

theorem glueConstEps_le_inv {d k l : ℕ} {ε c : ℝ} :
    glueConstEps d k l ε c ≤ (2 * Real.sqrt (k : ℝ))⁻¹ := by
  have hnn : (0 : ℝ) ≤ (2 * Real.sqrt (k : ℝ))⁻¹ := inv_nonneg.mpr (by positivity)
  rw [glueConstEps]
  simpa using mul_le_mul_of_nonneg_left (min_le_right
    ((Submission.EscapeGlue.ballConst k * c ^ k /
      (((k : ℝ) + 1) * (2 : ℝ) ^ k)) ^ (1 / escapeExp d k l ε)) (1 : ℝ)) hnn

theorem glueConstEps_nonneg {d k l : ℕ} {ε c : ℝ} (hc : 0 < c) :
    0 ≤ glueConstEps d k l ε c := by
  have hnn : (0 : ℝ) ≤ (2 * Real.sqrt (k : ℝ))⁻¹ := inv_nonneg.mpr (by positivity)
  have hbase : (0 : ℝ) ≤ Submission.EscapeGlue.ballConst k * c ^ k /
      (((k : ℝ) + 1) * (2 : ℝ) ^ k) :=
    le_of_lt (div_pos (mul_pos (Submission.EscapeGlue.ballConst_pos k) (pow_pos hc k))
      (by positivity))
  have hA : (0 : ℝ) ≤ (Submission.EscapeGlue.ballConst k * c ^ k /
      (((k : ℝ) + 1) * (2 : ℝ) ^ k)) ^ (1 / escapeExp d k l ε) := Real.rpow_nonneg hbase _
  rw [glueConstEps]
  exact mul_nonneg hnn (le_min hA zero_le_one)

/-- **The `ε`-escape glue**: with the *rate* hypothesis `c·e^{−εt} ≤ λ₁(a_t s_x ℤᵈ)` for every
`t ≥ 0`, a rational `k`-plane at distance `δ` from `x` satisfies
`δ ≥ glueConstEps · H^{−1/p}`, `p = α(1 − εℓ)`. -/
theorem glue_family_eps {l k : ℕ} (hk : 1 ≤ k) (hkl : k ≤ l) (hld : l < d)
    (x : Submodule ℝ ℝᵈ) (hx : Module.finrank ℝ x = l)
    (s : ℝᵈ ≃ₗᵢ[ℝ] ℝᵈ) (hs : Submodule.map (s : ℝᵈ →ₗ[ℝ] ℝᵈ) x
      = Submission.WedgeBlocks.modelX (d := d) l)
    {ε c : ℝ} (_hε : 0 ≤ ε) (hεl : ε * (l : ℝ) < 1) (hc : 0 < c)
    (hslow : ∀ t : ℝ, 0 ≤ t → c * Real.exp (-(ε * t)) ≤
       Commons.Lattice.SuccessiveMinima.successiveMinimum
       (Submission.ImageLattice.imageSpan (Submission.EscapeGlue.flowMap (d := d) l s t)) 1)
    (m : Fin k → ℝᵈ) (hmem : ∀ i, m i ∈ intPoints (d := d)) (hmLI : LinearIndependent ℝ m)
    (hδpos : 0 < LinearSubspaces.distSubspaces (Submodule.span ℝ (Set.range m)) x) :
    LinearSubspaces.distSubspaces (Submodule.span ℝ (Set.range m)) x ≥
      glueConstEps d k l ε c * ‖exteriorPower.ιMulti ℝ k m‖ ^
        (-(1 / escapeExp d k l ε)) := by
  classical
  have hk0 : 0 < k := hk
  have hl0 : 0 < l := lt_of_lt_of_le hk0 hkl
  have hdl : (0 : ℝ) < (d : ℝ) - (l : ℝ) := by
    have : (l : ℝ) < (d : ℝ) := by exact_mod_cast hld
    linarith
  have hS : 0 < Submission.EscapeGlue.rateS d l := by
    have hlne : (0 : ℝ) < (l : ℝ) := by exact_mod_cast hl0
    dsimp [Submission.EscapeGlue.rateS]; positivity
  have hp : 0 < escapeExp d k l ε := escapeExp_pos hk hl0 hld hεl
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
  have hH1 : (1 : ℝ) ≤ ‖exteriorPower.ιMulti ℝ k m‖ := by
    refine Commons.Analysis.InnerProductSpace.intWedge_norm_ge_one hk m ?_ hmLI
    intro r t
    exact Submission.EscapeGlue.intPoints_coord_int (m r) (hmem r) t
  by_cases hsmall : δ ≤ 1 / (2 * Real.sqrt (k : ℝ))
  · -- SMALL CASE
    have hsqrtk_pos : 0 < Real.sqrt (k : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hk0)
    have hsqrtk1 : (1 : ℝ) ≤ Real.sqrt (k : ℝ) := Real.one_le_sqrt.mpr (by exact_mod_cast hk)
    have hδ12 : δ ≤ 1 / 2 := by
      refine le_trans hsmall ?_
      rw [div_le_div_iff₀ (by positivity) (by norm_num : (0 : ℝ) < 2)]
      linarith
    set X : ℝ := 2 * Real.sqrt (k : ℝ) * δ with hXdef
    have hXpos : 0 < X := by rw [hXdef]; positivity
    set t : ℝ := Real.log (1 / X) / Submission.EscapeGlue.rateS d l with htdef
    have htS : t * Submission.EscapeGlue.rateS d l = Real.log (1 / X) := by
      rw [htdef, div_mul_cancel₀ _ (ne_of_gt hS)]
    have htexp : Real.exp (-(t * Submission.EscapeGlue.rateS d l)) = X := by
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
      have h1 := Submission.EscapeGlue.one_le_planeResidual_of_meet_ne_bot
        (Submodule.span ℝ (Set.range u)) (Submission.WedgeBlocks.modelX (d := d) l) hne
      rw [hdist_u] at h1
      linarith
    have hup := Submission.EscapeGlue.model_wedge_flow_upper (d := d) (k := k) (l := l) hk0 hkl
      hld hδpos hδ12 u hu hbot hdist_u t (by rw [htexp, hXdef])
    -- rewrite the upper bound
    have hmap : exteriorPower.ιMulti ℝ k (fun i => Submission.EscapeGlue.flowMap (d := d) l s t
          (m i)) =
        exteriorPower.map k (Submission.DiagonalFlow.scaleMap
          (Submission.DiagonalFlow.twoScale (Real.exp (-t / (l : ℝ)))
            (Real.exp (t / ((d : ℝ) - (l : ℝ)))) l)) (exteriorPower.ιMulti ℝ k u) := by
      rw [exteriorPower.map_apply_ιMulti]
      congr 1
    have hnormu : ‖exteriorPower.ιMulti ℝ k u‖ = ‖exteriorPower.ιMulti ℝ k m‖ := by
      rw [hudef]
      exact Commons.Analysis.InnerProductSpace.norm_iMulti_comp_isometry s m
    -- the lower bound
    set g : ℝᵈ ≃ₗ[ℝ] ℝᵈ := Submission.EscapeGlue.flowMap (d := d) l s t with hgdef
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
    -- the time is nonnegative
    have hX1 : X ≤ 1 := by
      rw [hXdef]
      have hk2 : (0 : ℝ) < 2 * Real.sqrt (k : ℝ) := by positivity
      have hle := (le_div_iff₀ hk2).mp hsmall
      linarith [hle]
    have hlog_nonneg : (0 : ℝ) ≤ Real.log (1 / X) := by
      refine Real.log_nonneg ?_
      rw [le_div_iff₀ hXpos, one_mul]
      exact hX1
    have ht0 : 0 ≤ t := by
      rw [htdef]
      exact div_nonneg hlog_nonneg (le_of_lt hS)
    have hlow0 := Commons.Lattice.Minkowski.wedge_norm_ge_pow_uniform (E := ℝᵈ) Λ
      (le_of_lt (mul_pos hc (Real.exp_pos _))) (hslow t ht0) w hwLI
    have hlow : Submission.EscapeGlue.ballConst k * (c * Real.exp (-(ε * t))) ^ k ≤
        ‖exteriorPower.ιMulti ℝ k (fun i =>
          Submission.EscapeGlue.flowMap (d := d) l s t (m i))‖ := by
      simpa [Submission.EscapeGlue.ballConst] using hlow0
    have hwval : (fun i => (w i : ℝᵈ)) =
        (fun i => Submission.EscapeGlue.flowMap (d := d) l s t (m i)) := by
      funext i; rw [hwdef]
    rw [hwval] at hlow
    -- exponential identities
    have hpk : Real.exp (-(ε * t)) ^ k = Real.exp (-(t * ((k : ℝ) * ε))) := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    have hYeq : Real.exp (-(t * ((k : ℝ) * ε))) =
        X ^ ((k : ℝ) * ε / Submission.EscapeGlue.rateS d l) := by
      rw [← Submission.EscapeGlue.exp_neg_log_div_eq_rpow (δ := X) (S := Submission.EscapeGlue.rateS d l)
        (R := (k : ℝ) * ε) hXpos hS]
    have hαeq : Submission.EscapeGlue.alpha d k l =
        ((k : ℝ) / (l : ℝ)) / Submission.EscapeGlue.rateS d l := by
      have hlne : (l : ℝ) ≠ 0 := ne_of_gt (by exact_mod_cast hl0)
      have hdlne : (d : ℝ) - (l : ℝ) ≠ 0 := ne_of_gt hdl
      have hdne : (d : ℝ) ≠ 0 := by
        have : (0 : ℝ) < (d : ℝ) := by
          have : 0 < d := lt_of_lt_of_le hl0 (le_of_lt hld); exact_mod_cast this
        exact ne_of_gt this
      dsimp [Submission.EscapeGlue.alpha, Submission.EscapeGlue.rateS]
      field_simp
      ring
    have hXα : Real.exp (-(t * ((k : ℝ) / (l : ℝ)))) =
        X ^ (Submission.EscapeGlue.alpha d k l) := by
      have h1 : t * ((k : ℝ) / (l : ℝ)) = Real.log (1 / X) * Submission.EscapeGlue.alpha d k l := by
        have h3 : t * ((k : ℝ) / (l : ℝ)) = (t * Submission.EscapeGlue.rateS d l) *
            (((k : ℝ) / (l : ℝ)) / Submission.EscapeGlue.rateS d l) := by
          field_simp
        rw [h3, htS, ← hαeq]
      have h2 : -(t * ((k : ℝ) / (l : ℝ))) = Real.log X * Submission.EscapeGlue.alpha d k l := by
        rw [h1, one_div, Real.log_inv]; ring
      rw [Real.rpow_def_of_pos hXpos, h2]
    have hC1pos : (0 : ℝ) < ((k : ℝ) + 1) * (2 : ℝ) ^ k := by positivity
    have hmain : Submission.EscapeGlue.ballConst k * c ^ k *
          X ^ ((k : ℝ) * ε / Submission.EscapeGlue.rateS d l) ≤
        ((k : ℝ) + 1) * (2 : ℝ) ^ k * X ^ (Submission.EscapeGlue.alpha d k l) *
          ‖exteriorPower.ιMulti ℝ k m‖ := by
      have h1 : Submission.EscapeGlue.ballConst k * c ^ k *
            Real.exp (-(t * ((k : ℝ) * ε))) ≤
          ((k : ℝ) + 1) * (2 : ℝ) ^ k * X ^ (Submission.EscapeGlue.alpha d k l) *
            ‖exteriorPower.ιMulti ℝ k m‖ := by
        have hA : Submission.EscapeGlue.ballConst k * c ^ k *
              Real.exp (-(t * ((k : ℝ) * ε))) =
            Submission.EscapeGlue.ballConst k * (c * Real.exp (-(ε * t))) ^ k := by
          rw [mul_pow, hpk]; ring
        rw [hA]
        calc Submission.EscapeGlue.ballConst k * (c * Real.exp (-(ε * t))) ^ k
            ≤ ‖exteriorPower.ιMulti ℝ k (fun i =>
                Submission.EscapeGlue.flowMap (d := d) l s t (m i))‖ := hlow
          _ = ‖exteriorPower.map k (Submission.DiagonalFlow.scaleMap
                (Submission.DiagonalFlow.twoScale (Real.exp (-t / (l : ℝ)))
                  (Real.exp (t / ((d : ℝ) - (l : ℝ)))) l)) (exteriorPower.ιMulti ℝ k u)‖ := by
                rw [hmap]
          _ ≤ ((k : ℝ) + 1) * (2 : ℝ) ^ k * Real.exp (-(t * ((k : ℝ) / (l : ℝ)))) *
                ‖exteriorPower.ιMulti ℝ k u‖ := hup
          _ = ((k : ℝ) + 1) * (2 : ℝ) ^ k * X ^ (Submission.EscapeGlue.alpha d k l) *
                ‖exteriorPower.ιMulti ℝ k m‖ := by
                rw [hXα, hnormu]
      rwa [hYeq] at h1
    have hchase := Submission.EscapeGlue.chase (δ := X) (H := ‖exteriorPower.ιMulti ℝ k m‖)
      (C1 := ((k : ℝ) + 1) * (2 : ℝ) ^ k)
      (C2 := Submission.EscapeGlue.ballConst k * c ^ k)
      (p := escapeExp d k l ε)
      hXpos hX1 hH1 hC1pos
      (mul_pos (Submission.EscapeGlue.ballConst_pos k) (pow_pos hc k)) hp ?_
    · have hXeq : X = 2 * Real.sqrt (k : ℝ) * δ := hXdef
      rw [hXeq] at hchase
      have hstep : (2 * Real.sqrt (k : ℝ))⁻¹ *
          ((Submission.EscapeGlue.ballConst k * c ^ k / (((k : ℝ) + 1) * (2 : ℝ) ^ k)) ^
            (1 / escapeExp d k l ε) *
            ‖exteriorPower.ιMulti ℝ k m‖ ^ (-(1 / escapeExp d k l ε)))
          ≤ δ := by
        have h0 : (2 * Real.sqrt (k : ℝ))⁻¹ *
            ((Submission.EscapeGlue.ballConst k * c ^ k / (((k : ℝ) + 1) * (2 : ℝ) ^ k)) ^
              (1 / escapeExp d k l ε) *
              ‖exteriorPower.ιMulti ℝ k m‖ ^ (-(1 / escapeExp d k l ε)))
            ≤ (2 * Real.sqrt (k : ℝ))⁻¹ * (2 * Real.sqrt (k : ℝ) * δ) :=
          mul_le_mul_of_nonneg_left hchase (by positivity)
        rw [inv_mul_cancel_left₀ (ne_of_gt (by positivity : (0 : ℝ) < 2 * Real.sqrt (k : ℝ)))] at h0
        exact h0
      have hgluele : glueConstEps d k l ε c *
          ‖exteriorPower.ιMulti ℝ k m‖ ^ (-(1 / escapeExp d k l ε)) ≤
          (2 * Real.sqrt (k : ℝ))⁻¹ *
            ((Submission.EscapeGlue.ballConst k * c ^ k / (((k : ℝ) + 1) * (2 : ℝ) ^ k)) ^
              (1 / escapeExp d k l ε) *
              ‖exteriorPower.ιMulti ℝ k m‖ ^ (-(1 / escapeExp d k l ε))) := by
        rw [glueConstEps]
        have hHnn : (0 : ℝ) ≤ ‖exteriorPower.ιMulti ℝ k m‖ ^ (-(1 / escapeExp d k l ε)) :=
          Real.rpow_nonneg (norm_nonneg _) _
        have hm : min ((Submission.EscapeGlue.ballConst k * c ^ k /
            (((k : ℝ) + 1) * (2 : ℝ) ^ k)) ^ (1 / escapeExp d k l ε)) 1 ≤
            (Submission.EscapeGlue.ballConst k * c ^ k /
              (((k : ℝ) + 1) * (2 : ℝ) ^ k)) ^ (1 / escapeExp d k l ε) := min_le_left _ _
        calc (2 * Real.sqrt (k : ℝ))⁻¹ *
                min ((Submission.EscapeGlue.ballConst k * c ^ k /
                  (((k : ℝ) + 1) * (2 : ℝ) ^ k)) ^ (1 / escapeExp d k l ε)) 1 *
                ‖exteriorPower.ιMulti ℝ k m‖ ^ (-(1 / escapeExp d k l ε))
            = (2 * Real.sqrt (k : ℝ))⁻¹ *
                (min ((Submission.EscapeGlue.ballConst k * c ^ k /
                  (((k : ℝ) + 1) * (2 : ℝ) ^ k)) ^ (1 / escapeExp d k l ε)) 1 *
                ‖exteriorPower.ιMulti ℝ k m‖ ^ (-(1 / escapeExp d k l ε))) := by ring
          _ ≤ (2 * Real.sqrt (k : ℝ))⁻¹ *
                (((Submission.EscapeGlue.ballConst k * c ^ k /
                  (((k : ℝ) + 1) * (2 : ℝ) ^ k)) ^ (1 / escapeExp d k l ε)) *
                ‖exteriorPower.ιMulti ℝ k m‖ ^ (-(1 / escapeExp d k l ε))) :=
              mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hm hHnn) (by positivity)
      exact hgluele.trans hstep
    · -- the input of the chase
      have hYpos : 0 < X ^ ((k : ℝ) * ε / Submission.EscapeGlue.rateS d l) :=
        Real.rpow_pos_of_pos hXpos _
      have h2 : Submission.EscapeGlue.ballConst k * c ^ k ≤
          ((k : ℝ) + 1) * (2 : ℝ) ^ k * X ^ (Submission.EscapeGlue.alpha d k l) *
            ‖exteriorPower.ιMulti ℝ k m‖ /
            X ^ ((k : ℝ) * ε / Submission.EscapeGlue.rateS d l) :=
        (le_div_iff₀ hYpos).mpr hmain
      refine h2.trans_eq ?_
      have h3 : X ^ (Submission.EscapeGlue.alpha d k l) /
          X ^ ((k : ℝ) * ε / Submission.EscapeGlue.rateS d l) = X ^ (escapeExp d k l ε) := by
        rw [escapeExp, Real.rpow_sub hXpos]
      calc ((k : ℝ) + 1) * (2 : ℝ) ^ k * X ^ (Submission.EscapeGlue.alpha d k l) *
              ‖exteriorPower.ιMulti ℝ k m‖ /
              X ^ ((k : ℝ) * ε / Submission.EscapeGlue.rateS d l)
          = ((k : ℝ) + 1) * (2 : ℝ) ^ k *
              (X ^ (Submission.EscapeGlue.alpha d k l) /
                X ^ ((k : ℝ) * ε / Submission.EscapeGlue.rateS d l)) *
              ‖exteriorPower.ιMulti ℝ k m‖ := by ring
        _ = ((k : ℝ) + 1) * (2 : ℝ) ^ k * X ^ (escapeExp d k l ε) *
              ‖exteriorPower.ιMulti ℝ k m‖ := by rw [h3]
  · -- LARGE CASE
    push Not at hsmall
    have hHinv : ‖exteriorPower.ιMulti ℝ k m‖ ^ (-(1 / escapeExp d k l ε)) ≤ 1 := by
      have hpos : (0 : ℝ) < ‖exteriorPower.ιMulti ℝ k m‖ := lt_of_lt_of_le one_pos hH1
      rw [Real.rpow_neg hpos.le]
      rw [inv_le_one₀ (Real.rpow_pos_of_pos hpos _)]
      exact Real.one_le_rpow hH1 (le_of_lt (one_div_pos.mpr hp))
    calc glueConstEps d k l ε c * ‖exteriorPower.ιMulti ℝ k m‖ ^ (-(1 / escapeExp d k l ε))
        ≤ glueConstEps d k l ε c * 1 :=
          mul_le_mul_of_nonneg_left hHinv (glueConstEps_nonneg (d := d) (k := k) (l := l) (ε := ε) hc)
      _ ≤ (2 * Real.sqrt (k : ℝ))⁻¹ * 1 := by
          exact mul_le_mul_of_nonneg_right (glueConstEps_le_inv (d := d) (k := k) (l := l) (ε := ε)
            (c := c)) zero_le_one
      _ = 1 / (2 * Real.sqrt (k : ℝ)) := by ring
      _ ≤ δ := le_of_lt hsmall

/-- **Rational-plane form** of the `ε`-glue (the form in which conjunct 2 consumes it). -/
theorem glue_rational_eps {l k : ℕ} (hk : 1 ≤ k) (hkl : k ≤ l) (hld : l < d)
    (x : Submodule ℝ ℝᵈ) (hx : Module.finrank ℝ x = l)
    (s : ℝᵈ ≃ₗᵢ[ℝ] ℝᵈ) (hs : Submodule.map (s : ℝᵈ →ₗ[ℝ] ℝᵈ) x
      = Submission.WedgeBlocks.modelX (d := d) l)
    {ε c : ℝ} (hε : 0 ≤ ε) (hεl : ε * (l : ℝ) < 1) (hc : 0 < c)
    (hslow : ∀ t : ℝ, 0 ≤ t → c * Real.exp (-(ε * t)) ≤
       Commons.Lattice.SuccessiveMinima.successiveMinimum
       (Submission.ImageLattice.imageSpan (Submission.EscapeGlue.flowMap (d := d) l s t)) 1)
    (v : Submodule ℝ ℝᵈ) (hv : IsRational v) (hvk : Module.finrank ℝ v = k)
    (hδpos : 0 < LinearSubspaces.distSubspaces v x) :
    LinearSubspaces.distSubspaces v x ≥
      glueConstEps d k l ε c * LinearSubspaces.height v hv ^ (-(1 / escapeExp d k l ε)) := by
  classical
  set m : Fin k → ℝᵈ := fun i => Submission.Heights.cbFamily v hv (Fin.cast hvk.symm i) with hmdef
  have hmem : ∀ i, m i ∈ ℤᵈ := by
    intro i
    refine Submission.EscapeGlue.imageLattice_le_intPoints v ?_
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
    exact Submission.EscapeGlue.span_range_cbFamily v hv
  have hnorm : ‖exteriorPower.ιMulti ℝ k m‖ =
      ‖exteriorPower.ιMulti ℝ (Module.finrank ℝ v) (Submission.Heights.cbFamily v hv)‖ := by
    rw [← Submission.EscapeGlue.norm_iMulti_cast hvk (Submission.Heights.cbFamily v hv), hmdef]
  have hheight : LinearSubspaces.height v hv = ‖exteriorPower.ιMulti ℝ k m‖ := by
    rw [hnorm]; rfl
  have hδ : 0 < LinearSubspaces.distSubspaces (Submodule.span ℝ (Set.range m)) x := by
    rw [hspan]; exact hδpos
  have h := glue_family_eps (d := d) (l := l) (k := k) hk hkl hld x hx s hs
    hε hεl hc hslow m hmem hmLI hδ
  rw [hspan, ← hheight] at h
  exact h

/-- **`β_k(x) ≤ 1/(α(1−εℓ))` from a rate-`ε` escape hypothesis.** -/
theorem conjunct2_upper_eps {l k : ℕ} (hk : 1 ≤ k) (hkl : k ≤ l) (hld : l < d)
    (x : Submodule ℝ ℝᵈ) (hx : Module.finrank ℝ x = l)
    (s : ℝᵈ ≃ₗᵢ[ℝ] ℝᵈ) (hs : Submodule.map (s : ℝᵈ →ₗ[ℝ] ℝᵈ) x
      = Submission.WedgeBlocks.modelX (d := d) l)
    {ε c : ℝ} (hε : 0 ≤ ε) (hεl : ε * (l : ℝ) < 1) (hc : 0 < c)
    (hslow : ∀ t : ℝ, 0 ≤ t → c * Real.exp (-(ε * t)) ≤
       Commons.Lattice.SuccessiveMinima.successiveMinimum
       (Submission.ImageLattice.imageSpan (Submission.EscapeGlue.flowMap (d := d) l s t)) 1)
    (hδ : ∀ v : Submodule ℝ ℝᵈ, IsRational v → Module.finrank ℝ v = k →
      0 < LinearSubspaces.distSubspaces v x) :
    LinearSubspaces.diophantineExponent k x ≤ ENNReal.ofReal (1 / escapeExp d k l ε) := by
  have hl0 : 0 < l := lt_of_lt_of_le (Nat.one_le_iff_ne_zero.mpr (by omega)) hkl
  have hp : 0 < escapeExp d k l ε := escapeExp_pos hk hl0 hld hεl
  refine Submission.EscapeGlue.diophantineExponent_le_of_forall_gt k x
    (le_of_lt (div_pos one_pos hp)) ?_
  intro β hβ
  refine ⟨glueConstEps d k l ε c,
    glueConstEps_pos hk hp hc, ?_⟩
  intro v hvk hv
  have h1 := glue_rational_eps (d := d) hk hkl hld x hx s hs hε hεl hc hslow v hv hvk
    (hδ v hv hvk)
  have hH : (1 : ℝ) ≤ LinearSubspaces.height v hv := Submission.EscapeGlue.height_ge_one v hv
  have h2 : LinearSubspaces.height v hv ^ (-β) ≤
      LinearSubspaces.height v hv ^ (-(1 / escapeExp d k l ε)) :=
    Real.rpow_le_rpow_of_exponent_le hH (by linarith : -β ≤ -(1 / escapeExp d k l ε))
  calc glueConstEps d k l ε c * LinearSubspaces.height v hv ^ (-β)
      ≤ glueConstEps d k l ε c *
          LinearSubspaces.height v hv ^ (-(1 / escapeExp d k l ε)) :=
        mul_le_mul_of_nonneg_left h2 (glueConstEps_nonneg (d := d) (k := k) (l := l) (ε := ε) hc)
    _ ≤ LinearSubspaces.distSubspaces v x := h1

/-- **The initial segment bound**: for `0 ≤ t ≤ T` the first minimum of the flowed lattice is at
least `e^{−T/ℓ}` (the flow shrinks norms by at most `e^{t/ℓ}` and `s` is an isometry, so the
first minimum never drops below `1` up to the flow factor). -/
theorem flowMap_successiveMinimum_ge {l : ℕ} (hl0 : 0 < l) (hld : l < d)
    (s : ℝᵈ ≃ₗᵢ[ℝ] ℝᵈ) {t T : ℝ} (ht0 : 0 ≤ t) (htT : t ≤ T) :
    Real.exp (-(T / (l : ℝ))) ≤
      Commons.Lattice.SuccessiveMinima.successiveMinimum
        (Submission.ImageLattice.imageSpan (Submission.EscapeGlue.flowMap (d := d) l s t)) 1 := by
  have h1 : Real.exp (-t / (l : ℝ)) / 1 ≤
      Commons.Lattice.SuccessiveMinima.successiveMinimum
        (Submission.ImageLattice.flowSpan_sx (d := d) (Real.exp (-t / (l : ℝ)))
          (Real.exp (t / ((d : ℝ) - (l : ℝ)))) l (ne_of_gt (Real.exp_pos _))
          (ne_of_gt (Real.exp_pos _)) s.toLinearEquiv) 1 :=
    Submission.FlowSpanSxLower.successiveMinimum_ge_exp_of_flowSpan_sx (d := d) hl0 hld ht0
      (sx := s.toLinearEquiv) (M := 1) zero_le_one (fun y => by
        have h := (s.symm : ℝᵈ ≃ₗᵢ[ℝ] ℝᵈ).norm_map y
        simp)
  rw [div_one] at h1
  have hl : (0 : ℝ) < (l : ℝ) := by exact_mod_cast hl0
  have he : Real.exp (-(T / (l : ℝ))) ≤ Real.exp (-t / (l : ℝ)) :=
    Real.exp_le_exp.mpr (by rw [neg_div]; exact neg_le_neg (div_le_div_of_nonneg_right htT hl.le))
  exact le_trans he h1

/-- From the eventual rate-`ε` bound (`∀ t ≥ T, e^{−εt} ≤ λ₁`) one gets the all-`t ≥ 0` bound
with a positive constant. -/
theorem slow_of_eventual {l : ℕ} (hl0 : 0 < l) (hld : l < d) (s : ℝᵈ ≃ₗᵢ[ℝ] ℝᵈ)
    {ε : ℝ} (hε : 0 < ε)
    (h : ∃ T : ℝ, ∀ t : ℝ, T ≤ t →
      Real.exp (-(ε * t)) ≤ Commons.Lattice.SuccessiveMinima.successiveMinimum
        (Submission.ImageLattice.imageSpan (Submission.EscapeGlue.flowMap (d := d) l s t)) 1) :
    ∃ c : ℝ, 0 < c ∧ ∀ t : ℝ, 0 ≤ t → c * Real.exp (-(ε * t)) ≤
      Commons.Lattice.SuccessiveMinima.successiveMinimum
        (Submission.ImageLattice.imageSpan (Submission.EscapeGlue.flowMap (d := d) l s t)) 1 := by
  obtain ⟨T₀, hT⟩ := h
  set T : ℝ := max T₀ 0 with hTdef
  refine ⟨min (Real.exp (-(T / (l : ℝ)))) 1, lt_min (Real.exp_pos _) one_pos, fun t ht0 => ?_⟩
  by_cases htT : t ≤ T
  · have h1 := flowMap_successiveMinimum_ge (d := d) hl0 hld s ht0 htT
    have he : Real.exp (-(ε * t)) ≤ 1 := by
      rw [← Real.exp_zero]
      exact Real.exp_le_exp.mpr (by nlinarith [hε, ht0])
    calc min (Real.exp (-(T / (l : ℝ)))) 1 * Real.exp (-(ε * t))
        ≤ Real.exp (-(T / (l : ℝ))) * 1 :=
          mul_le_mul (min_le_left _ _) he (Real.exp_pos _).le (Real.exp_pos _).le
      _ = Real.exp (-(T / (l : ℝ))) := mul_one _
      _ ≤ _ := h1
  · have hle : T ≤ t := le_of_lt (lt_of_not_ge htT)
    have h2 := hT t (le_trans (le_max_left T₀ 0) hle)
    calc min (Real.exp (-(T / (l : ℝ)))) 1 * Real.exp (-(ε * t))
        ≤ 1 * Real.exp (-(ε * t)) :=
          mul_le_mul_of_nonneg_right (min_le_right _ _) (Real.exp_pos _).le
      _ = Real.exp (-(ε * t)) := one_mul _
      _ ≤ _ := h2

/-- **ENNReal limit helper**: pointwise control from above by `ofReal r` for all `r > a`
gives the bound by `ofReal a`. -/
theorem le_ofReal_of_forall_gt {b : ENNReal} {a : ℝ} (ha : 0 ≤ a)
    (h : ∀ r : ℝ, a < r → b ≤ ENNReal.ofReal r) : b ≤ ENNReal.ofReal a := by
  obtain ⟨r0, hr0⟩ : ∃ r : ℝ, a < r := ⟨a + 1, by linarith⟩
  have hb : b ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top (h r0 hr0)
  refine (ENNReal.le_ofReal_iff_toReal_le hb ha).mpr ?_
  by_contra hlt
  have hlt' : a < b.toReal := lt_of_not_ge hlt
  have h2 : b.toReal ≤ (a + b.toReal) / 2 :=
    ENNReal.toReal_le_of_le_ofReal (by linarith) (h ((a + b.toReal) / 2) (by linarith))
  linarith

/-- **Conjunct 2 from an `ε`-rate witness.**  If conjunct 1 holds and there is an `ℓ`-plane `x`
with all its rational `k`-planes at positive distance and with **zero escape rate**
(`∃T ∀t ≥ T, e^{−εt} ≤ λ₁(a_t s_x ℤᵈ)` for every `ε > 0`), then `β_k(x)` equals the critical
exponent. -/
theorem conjunct2_of_witness_eps {l k : ℕ} (hk : 1 ≤ k) (hkl : k ≤ l) (hld : l < d)
    (h1 : ∀ x : Submodule ℝ ℝᵈ, Module.finrank ℝ x = l →
      LinearSubspaces.diophantineExponent k x ≥ (d : ℝ≥0∞) / (k * (d - l)))
    (hW : ∃ x : Submodule ℝ ℝᵈ, Module.finrank ℝ x = l ∧
      ∃ s : ℝᵈ ≃ₗᵢ[ℝ] ℝᵈ, Submodule.map (s : ℝᵈ →ₗ[ℝ] ℝᵈ) x
          = Submission.WedgeBlocks.modelX (d := d) l ∧
      (∀ v : Submodule ℝ ℝᵈ, IsRational v → Module.finrank ℝ v = k →
        0 < LinearSubspaces.distSubspaces v x) ∧
      (∀ ε : ℝ, 0 < ε → ∃ T : ℝ, ∀ t : ℝ, T ≤ t →
        Real.exp (-(ε * t)) ≤ Commons.Lattice.SuccessiveMinima.successiveMinimum
          (Submission.ImageLattice.imageSpan (Submission.EscapeGlue.flowMap (d := d) l s t)) 1)) :
    ∃ x : Submodule ℝ ℝᵈ, Module.finrank ℝ x = l ∧
      LinearSubspaces.diophantineExponent k x = (d : ℝ≥0∞) / (k * (d - l)) := by
  obtain ⟨x, hx, s, hs, hδ, hesc⟩ := hW
  have hl0 : 0 < l := lt_of_lt_of_le (Nat.one_le_iff_ne_zero.mpr (by omega)) hkl
  have hα : 0 < Submission.EscapeGlue.alpha d k l :=
    Submission.EscapeGlue.alpha_pos hk hl0 hld
  have hlR : (0 : ℝ) < (l : ℝ) := by exact_mod_cast hl0
  have hαpos : (0 : ℝ) < Submission.EscapeGlue.alpha d k l := hα
  -- the upper bound, at every exponent `r > 1/α`
  have hupper : LinearSubspaces.diophantineExponent k x ≤
      ENNReal.ofReal (1 / Submission.EscapeGlue.alpha d k l) := by
    refine le_ofReal_of_forall_gt (le_of_lt (div_pos one_pos hα)) ?_
    intro r hr
    -- choose the escape rate `ε`
    set ε : ℝ := (1 - 1 / (r * Submission.EscapeGlue.alpha d k l)) / (2 * (l : ℝ)) with hεdef
    have hαr : 1 < r * Submission.EscapeGlue.alpha d k l := by
      rw [div_lt_iff₀ hα] at hr
      linarith
    have hrα : 0 < r * Submission.EscapeGlue.alpha d k l := by linarith
    have hrpos : 0 < r := lt_trans (div_pos one_pos hα) hr
    have hnum : 0 < 1 - 1 / (r * Submission.EscapeGlue.alpha d k l) := by
      have hlt : 1 / (r * Submission.EscapeGlue.alpha d k l) < 1 := by
        rw [div_lt_one hrα]
        linarith
      linarith
    have hεpos : 0 < ε := by rw [hεdef]; positivity
    have hmul : ε * (l : ℝ) = (1 - 1 / (r * Submission.EscapeGlue.alpha d k l)) / 2 := by
      rw [hεdef]
      field_simp
    have hεl : ε * (l : ℝ) < 1 := by
      have hq : 0 < 1 / (r * Submission.EscapeGlue.alpha d k l) := by positivity
      rw [hmul]; linarith
    obtain ⟨c, hc, hslow⟩ := slow_of_eventual (d := d) hl0 hld s hεpos (hesc ε hεpos)
    have hup := conjunct2_upper_eps (d := d) hk hkl hld x hx s hs (le_of_lt hεpos) hεl hc hslow hδ
    -- `1/escapeExp ≤ r`
    have hexp_le : 1 / escapeExp d k l ε ≤ r := by
      have hfac : (0 : ℝ) < 1 - ε * (l : ℝ) := by
        have hq : 0 < 1 / (r * Submission.EscapeGlue.alpha d k l) := by positivity
        rw [hmul]; linarith
      rw [escapeExp_eq (d := d) hl0 hld, div_le_iff₀ (mul_pos hαpos hfac)]
      have hid : r * (Submission.EscapeGlue.alpha d k l * (1 - ε * (l : ℝ))) =
          (r * Submission.EscapeGlue.alpha d k l + 1) / 2 := by
        rw [hmul]
        field_simp
        ring
      rw [hid]
      linarith
    exact le_trans hup (ENNReal.ofReal_le_ofReal hexp_le)
  refine ⟨x, hx, le_antisymm ?_ (h1 x hx)⟩
  have hαval : (1 / Submission.EscapeGlue.alpha d k l) =
      (d : ℝ) / ((k : ℝ) * ((d : ℝ) - (l : ℝ))) := by
    have hdl : (0 : ℝ) < (d : ℝ) - (l : ℝ) := by
      have : (l : ℝ) < (d : ℝ) := by exact_mod_cast hld
      linarith
    have hd : (d : ℝ) ≠ 0 := by
      have : (0 : ℝ) < (d : ℝ) := by
        have : 0 < d := lt_of_lt_of_le hl0 (le_of_lt hld); exact_mod_cast this
      exact ne_of_gt this
    have hkne : (k : ℝ) ≠ 0 := ne_of_gt (by exact_mod_cast hk)
    rw [Submission.EscapeGlue.alpha]
    field_simp
  rw [hαval] at hupper
  rw [← Commons.Analysis.ENNReal.natCast_div_natCast_sub_mul_ofReal (d := d) (l := l) (k := k)
    (hld := hld) (hk := hk)] at hupper
  exact hupper

end Submission.EscapeGlueEps

end
