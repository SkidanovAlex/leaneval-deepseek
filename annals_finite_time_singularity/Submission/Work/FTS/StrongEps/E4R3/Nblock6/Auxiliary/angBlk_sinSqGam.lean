/-
# Buildable copy of `Work.FTS.StrongEps.E4R3.Nblock6.aux.angBlk_sinSqGam`

The assigned file lives at
`Submission/Work/FTS/StrongEps/E4R3/Nblock6/aux/angBlk_sinSqGam.lean`, whose module name
`Submission.Work.FTS.StrongEps.E4R3.Nblock6.aux.angBlk_sinSqGam` contains the component `aux`,
a file name reserved on some operating systems (`CON`, `PRN`, **`AUX`**, `NUL`, …).  Lean 4.34
rejects such module names in `Lean.checkModuleNamePortability`, *before* elaboration, so that
module can never be built from sources and nothing can `import` it
(`lake build Submission.Work.FTS.StrongEps.E4R3.Nblock6.aux.angBlk_sinSqGam` fails with
`'aux' is a reserved file name on some operating systems`).

This file is the rehomed copy: it lives under `Nblock6/Auxiliary/`, so its module name is
portable and it can be built and imported, while declaring **the same** theorem name
`Work.FTS.StrongEps.E4R3.Nblock6.aux.angBlk_sinSqGam` (the namespace is unchanged).  Import
this module, not the `aux/` one.  The mathematical content is identical to the assigned file
(the same imports and the same body; only this header differs).  The consumer
`Work.FTS.StrongEps.E4R3.Nblock6.N_b6_five` must be re-pointed at this module.

# `angBlk_sinSqGam` — the uniform angular integral bound for the profile `-sin²θ·Γ(α,·)/c(α)`

The consumer `Work.FTS.StrongEps.E4R3.Nblock6.N_b6_five` needs, uniformly in `α ∈ (0,1]`, the
integrability and a bound of the angular block

`AngBlk α C`,   `C θ = -sin²θ·Γ(α,θ)/c(α)`,

where `AngBlk α C θ = (C θ)² sin(2θ)^{-η} + ∑_{1 ≤ i ≤ 6} (D_θ^i C θ)² sin(2θ)^{-γ(α)}`,
`D_θ = sin(2θ)∂_θ`, `η = 99/100`, `γ(α) = 1 + α/10`.

## Route

`C = -(1/c(α))·G` with the *unnormalised* profile `G θ = sin²θ·Γ(α,θ)`; `AngBlk` is quadratic
in its argument (`D_θ` is linear and `D_θ(c·f) = c·D_θ f`), so

`AngBlk α C θ = c(α)^{-2}·AngBlk α G θ`,

and `1/10 ≤ c(α) ≤ 10` (`Spaces.c_bounds`) reduces the task to a uniform bound of
`∫_{Iθ} AngBlk α G`.  Every term is bounded pointwise by the *integrable* majorant

`sin(2θ)^{2α/3-η} + 14·(α·10⁵)²·sin(2θ)^{2α/3-γ(α)} + T`   (`T` a constant):

* `i = 0`: `G² sin(2θ)^{-η} = sin⁴θ·Γ²·sin(2θ)^{-η} ≤ Γ² sin(2θ)^{-η} ≤ sin(2θ)^{2α/3-η}`
  (using `Γ² ≤ sin(2θ)^{2α/3}`, `Coercivity.Gam_sq_le_sin_two`), whose integral over `Iθ` is
  `≤ 400` since `2α/3 - η = -(η - 2α/3)` with `η - 2α/3 ∈ (0,1)`;
* `i ≥ 1`: the local Leibniz rule (`Auxiliary.dthU_iter_mul_Ioo`) together with the two factor
  bounds `|D_θ^r sin²| ≤ K_r·sin(2θ)²` (`fkSinPow`) and `|D_θ^j Γ| ≤ α·10⁵·Γ`
  (`Spaces.dthU_iter_Gam_abs_bound`, the *crucial* factor `α`) gives
  `|D_θ^i G| ≤ Γ·(α·10⁵ + B_i·sin(2θ)²)`, whence
  `(D_θ^i G)² sin(2θ)^{-γ} ≤ 2(α·10⁵)²sin(2θ)^{2α/3-γ} + 2B_i² sin(2θ)^{3+17α/30}`
  `≤ 2(α·10⁵)²sin(2θ)^{2α/3-γ} + 2B_i²`, and `∫ sin(2θ)^{2α/3-γ} ≤ 120/(17α)` — the dangerous
  `1/α` is cancelled by the `α²` coming from the factor `α` on the `Γ`-derivatives.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.StrongEps.E4R3.Apriori4Proofs.blocks.N0Aux.N04aN05a_Defs
import Submission.Work.FTS.LocData6.DthIter_Gam_abs_le6
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux.fkSinPow
import Submission.Work.Coercivity.gamDth_l2_bound
import Submission.Work.Coercivity.integral_sin_two_neg_rpow_le
import Submission.Work.Spaces.c_bounds
import Submission.Work.Spaces.Gamma_WlInf
import Submission.Work.FTS.StrongEps.E4R3.Nblock6.Auxiliary.dthU_iter_mul_Ioo
import Submission.Work.FTS.StrongEps.E4R3.Nblock6.Auxiliary.dthU_iter_Gfun_bound
import Submission.Work.FTS.StrongEps.E4R3.Nblock6.Auxiliary.sin_two_rpow_block_integrals

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology ContDiff
open MeasureTheory Set Filter
open Work.FTS.StrongEps.E4R3.Apriori4Proofs.blocks.N0Aux (AngBlk)

namespace Work.FTS.StrongEps.E4R3.Nblock6.aux

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-! ## Elementary angular facts -/

lemma sin_two_nonneg_Iθ {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ Real.sin (2 * θ) :=
  Real.sin_nonneg_of_mem_Icc ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩

lemma sin_two_le_one' (θ : ℝ) : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _

lemma volume_real_Iθ : MeasureTheory.volume.real Work.Spaces.Iθ = Real.pi / 2 := by
  rw [MeasureTheory.measureReal_def, Work.Spaces.Iθ, Real.volume_Icc,
    ENNReal.toReal_ofReal (by linarith [Real.pi_pos])]
  ring

lemma volume_Iθ_ne_top : MeasureTheory.volume Work.Spaces.Iθ ≠ ⊤ := by
  rw [Work.Spaces.Iθ, Real.volume_Icc]
  exact ENNReal.ofReal_ne_top

/-! ## The profile `sin²θ·Γ` and the `C^∞`-regularity of its `D_θ`-jets on `(0,π/2)` -/

/-- The unnormalised profile `θ ↦ sin²θ·Γ(α,θ)`. -/
abbrev sinSqGam (α : ℝ) : ℝ → ℝ := fun θ => Real.sin θ ^ 2 * Work.Spaces.Gam α θ

/-- `Γ(α,·) = (sinθ·cos²θ)^{α/3}` is `C^∞` (at the honest smooth order `∞`) on the open
angular interval `(0,π/2)`, where its base is strictly positive. -/
lemma gam_contDiffOn_Ioo (α : ℝ) :
    ContDiffOn ℝ ∞ (fun θ : ℝ => Work.Spaces.Gam α θ) (Set.Ioo 0 (Real.pi / 2)) := by
  show ContDiffOn ℝ ∞ (fun θ : ℝ => (Real.sin θ * Real.cos θ ^ 2) ^ (α / 3))
    (Set.Ioo 0 (Real.pi / 2))
  have hbase : ContDiffOn ℝ ∞ (fun θ : ℝ => Real.sin θ * Real.cos θ ^ 2)
      (Set.Ioo 0 (Real.pi / 2)) :=
    ((Real.contDiff_sin (n := ∞)).contDiffOn).mul
      (((Real.contDiff_cos (n := ∞)).contDiffOn).pow 2)
  refine hbase.rpow_const_of_ne (fun θ hθ => ?_)
  have h1 : 0 < Real.sin θ :=
    Real.sin_pos_of_pos_of_lt_pi hθ.1 (by linarith [hθ.2, Real.pi_pos])
  have h2 : 0 < Real.cos θ :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, Real.pi_pos],
      by linarith [hθ.2, Real.pi_pos]⟩
  positivity

lemma sinSqGam_contDiffOn_Ioo (α : ℝ) :
    ContDiffOn ℝ ∞ (sinSqGam α) (Set.Ioo 0 (Real.pi / 2)) :=
  (((Real.contDiff_sin (n := ∞)).pow 2).contDiffOn).mul (gam_contDiffOn_Ioo α)

/-- `D_θ` preserves `C^∞`-regularity of a one-variable function on the open angular
interval. -/
lemma dthU_iter_contDiffOn_Ioo {f : ℝ → ℝ}
    (hf : ContDiffOn ℝ ∞ f (Set.Ioo 0 (Real.pi / 2))) (i : ℕ) :
    ContDiffOn ℝ ∞ (Work.Spaces.dthU^[i] f) (Set.Ioo 0 (Real.pi / 2)) := by
  induction i with
  | zero => simpa using hf
  | succ i ih =>
      rw [Function.iterate_succ_apply']
      have hsin : ContDiffOn ℝ ∞ (fun θ : ℝ => Real.sin (2 * θ))
          (Set.Ioo 0 (Real.pi / 2)) := by
        fun_prop
      exact hsin.mul (ih.deriv_of_isOpen isOpen_Ioo (by simp))

/-! ## `AngBlk` under a constant multiple -/

/-- `AngBlk` is quadratic in its profile argument. -/
lemma AngBlk_const_mul (α a : ℝ) (f : ℝ → ℝ) (θ : ℝ) :
    AngBlk α (fun θ => a * f θ) θ = a ^ 2 * AngBlk α f θ := by
  simp only [AngBlk, Work.Spaces.dthU_iter_const_mul]
  rw [mul_add, Finset.mul_sum]
  congr 1
  · ring
  · refine Finset.sum_congr rfl fun i _ => ?_
    by_cases h : 1 ≤ i
    · simp only [h, if_true]; ring
    · simp only [h, if_false]; ring

/-! ## The pointwise bound -/

/-- **The pointwise bound.**  For `α ∈ (0,1]`, `θ ∈ Iθ` and any `B` witnessing the jet bound,
`AngBlk α (sin²·Γ)` is dominated by an explicit integrable majorant. -/
lemma angBlk_le_majorant {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {B : ℕ → ℝ}
    (hBnn : ∀ i, 0 ≤ B i)
    (hB : ∀ i : ℕ, 1 ≤ i → i ≤ 6 → ∀ θ ∈ Work.Spaces.Iθ,
      |Work.Spaces.dthU^[i] (sinSqGam α) θ|
        ≤ Work.Spaces.Gam α θ * (α * 100000 + B i * (Real.sin (2 * θ)) ^ 2))
    (T : ℝ) (hT : T = ∑ i ∈ Finset.range 7, 2 * (B i) ^ 2)
    {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    AngBlk α (sinSqGam α) θ
      ≤ (Real.sin (2 * θ)) ^ (2 * α / 3 - Work.Spaces.eta)
        + 14 * (α * 100000) ^ 2 * (Real.sin (2 * θ)) ^ (2 * α / 3 - Work.Spaces.gam α)
        + T := by
  set s : ℝ := Real.sin (2 * θ) with hs
  have hs0 : 0 ≤ s := by rw [hs]; exact sin_two_nonneg_Iθ hθ
  have hs1 : s ≤ 1 := by rw [hs]; exact Real.sin_le_one _
  have hGnn : 0 ≤ Work.Spaces.Gam α θ := (Work.Spaces.Gam_bounds α θ hα hθ).1
  have hG2 : (Work.Spaces.Gam α θ) ^ 2 ≤ s ^ (2 * α / 3) := by
    rw [hs]; exact Work.Coercivity.Gam_sq_le_sin_two α hα θ hθ
  have hweta : 0 ≤ s ^ (-(Work.Spaces.eta)) := Real.rpow_nonneg hs0 _
  have hwgam : 0 ≤ s ^ (-(Work.Spaces.gam α)) := Real.rpow_nonneg hs0 _
  have hne1 : 2 * α / 3 + -(Work.Spaces.eta) ≠ 0 := by
    have hlt : 2 * α / 3 < Work.Spaces.eta := by
      rw [Work.Spaces.eta]; nlinarith [hα1]
    intro h; linarith
  have hne2 : 2 * α / 3 + -(Work.Spaces.gam α) ≠ 0 := by
    have hlt : 2 * α / 3 < Work.Spaces.gam α := by
      rw [Work.Spaces.gam]; nlinarith [hα]
    intro h; linarith
  have hexp3 : 0 < 4 + (2 * α / 3 - Work.Spaces.gam α) := by
    rw [Work.Spaces.gam]; nlinarith [hα, hα1]
  have hne3 : 4 + (2 * α / 3 + -(Work.Spaces.gam α)) ≠ 0 := by
    intro h; linarith [hexp3]
  -- the two exponent identities
  have hcol1 : s ^ (2 * α / 3) * s ^ (-(Work.Spaces.eta))
      = s ^ (2 * α / 3 + -(Work.Spaces.eta)) := (Real.rpow_add' hs0 hne1).symm
  have hcol2 : s ^ (2 * α / 3) * s ^ (-(Work.Spaces.gam α))
      = s ^ (2 * α / 3 + -(Work.Spaces.gam α)) := (Real.rpow_add' hs0 hne2).symm
  -- the `i = 0` block
  have h0 : (sinSqGam α θ) ^ 2 * s ^ (-(Work.Spaces.eta))
      ≤ s ^ (2 * α / 3 - Work.Spaces.eta) := by
    have hsin2 : Real.sin θ ^ 2 ≤ 1 := by
      have h := Real.abs_sin_le_one θ
      nlinarith [abs_nonneg (Real.sin θ), sq_abs (Real.sin θ), h]
    have hsin4 : Real.sin θ ^ 4 ≤ 1 := by
      nlinarith [hsin2, sq_nonneg (Real.sin θ ^ 2)]
    have hsq : (sinSqGam α θ) ^ 2 = Real.sin θ ^ 4 * (Work.Spaces.Gam α θ) ^ 2 := by
      simp only [sinSqGam]; ring
    calc (sinSqGam α θ) ^ 2 * s ^ (-(Work.Spaces.eta))
        = Real.sin θ ^ 4 * ((Work.Spaces.Gam α θ) ^ 2 * s ^ (-(Work.Spaces.eta))) := by
          rw [hsq]; ring
      _ ≤ 1 * ((Work.Spaces.Gam α θ) ^ 2 * s ^ (-(Work.Spaces.eta))) :=
          mul_le_mul_of_nonneg_right hsin4 (mul_nonneg (sq_nonneg _) hweta)
      _ = (Work.Spaces.Gam α θ) ^ 2 * s ^ (-(Work.Spaces.eta)) := by ring
      _ ≤ s ^ (2 * α / 3) * s ^ (-(Work.Spaces.eta)) :=
          mul_le_mul_of_nonneg_right hG2 hweta
      _ = s ^ (2 * α / 3 - Work.Spaces.eta) := hcol1
  -- the two key blocks for the `i ≥ 1` terms
  have hkey1 : (Work.Spaces.Gam α θ) ^ 2 * s ^ (-(Work.Spaces.gam α))
      ≤ s ^ (2 * α / 3 - Work.Spaces.gam α) :=
    calc (Work.Spaces.Gam α θ) ^ 2 * s ^ (-(Work.Spaces.gam α))
        ≤ s ^ (2 * α / 3) * s ^ (-(Work.Spaces.gam α)) :=
          mul_le_mul_of_nonneg_right hG2 hwgam
      _ = s ^ (2 * α / 3 - Work.Spaces.gam α) := hcol2
  have hkey2 : s ^ 4 * ((Work.Spaces.Gam α θ) ^ 2 * s ^ (-(Work.Spaces.gam α))) ≤ 1 := by
    have h4 : s ^ 4 = s ^ (4 : ℝ) := (Real.rpow_natCast s 4).symm
    have hcol4 : s ^ (4 : ℝ) * s ^ (2 * α / 3 + -(Work.Spaces.gam α))
        = s ^ (4 + (2 * α / 3 + -(Work.Spaces.gam α))) := (Real.rpow_add' hs0 hne3).symm
    calc s ^ 4 * ((Work.Spaces.Gam α θ) ^ 2 * s ^ (-(Work.Spaces.gam α)))
        ≤ s ^ 4 * s ^ (2 * α / 3 - Work.Spaces.gam α) :=
          mul_le_mul_of_nonneg_left hkey1 (pow_nonneg hs0 4)
      _ = s ^ (4 : ℝ) * s ^ (2 * α / 3 - Work.Spaces.gam α) := by rw [h4]
      _ = s ^ (4 + (2 * α / 3 - Work.Spaces.gam α)) := hcol4
      _ ≤ 1 := Real.rpow_le_one hs0 hs1 hexp3.le
  -- the per-`i` term bound
  have hterm : ∀ i : ℕ, 1 ≤ i → i ≤ 6 →
      (Work.Spaces.dthU^[i] (sinSqGam α) θ) ^ 2 * s ^ (-(Work.Spaces.gam α))
        ≤ 2 * (α * 100000) ^ 2 * s ^ (2 * α / 3 - Work.Spaces.gam α) + 2 * (B i) ^ 2 := by
    intro i hi1 hi6
    have hb := hB i hi1 hi6 θ hθ
    simp only [← hs] at hb
    have hsq : (Work.Spaces.dthU^[i] (sinSqGam α) θ) ^ 2
        ≤ (Work.Spaces.Gam α θ * (α * 100000 + B i * s ^ 2)) ^ 2 := by
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) hb 2
    have hxy : (α * 100000 + B i * s ^ 2) ^ 2
        ≤ 2 * ((α * 100000) ^ 2 + (B i * s ^ 2) ^ 2) := by
      nlinarith [sq_nonneg (α * 100000 - B i * s ^ 2)]
    have hstep : (Work.Spaces.Gam α θ * (α * 100000 + B i * s ^ 2)) ^ 2
        ≤ 2 * ((Work.Spaces.Gam α θ) ^ 2 * (α * 100000) ^ 2
            + (Work.Spaces.Gam α θ) ^ 2 * (B i) ^ 2 * s ^ 4) := by
      rw [show (Work.Spaces.Gam α θ * (α * 100000 + B i * s ^ 2)) ^ 2
            = (Work.Spaces.Gam α θ) ^ 2 * (α * 100000 + B i * s ^ 2) ^ 2 by ring]
      calc (Work.Spaces.Gam α θ) ^ 2 * (α * 100000 + B i * s ^ 2) ^ 2
          ≤ (Work.Spaces.Gam α θ) ^ 2 * (2 * ((α * 100000) ^ 2 + (B i * s ^ 2) ^ 2)) :=
            mul_le_mul_of_nonneg_left hxy (sq_nonneg _)
        _ = 2 * ((Work.Spaces.Gam α θ) ^ 2 * (α * 100000) ^ 2
              + (Work.Spaces.Gam α θ) ^ 2 * (B i) ^ 2 * s ^ 4) := by ring
    calc (Work.Spaces.dthU^[i] (sinSqGam α) θ) ^ 2 * s ^ (-(Work.Spaces.gam α))
        ≤ (Work.Spaces.Gam α θ * (α * 100000 + B i * s ^ 2)) ^ 2
            * s ^ (-(Work.Spaces.gam α)) := mul_le_mul_of_nonneg_right hsq hwgam
      _ ≤ (2 * ((Work.Spaces.Gam α θ) ^ 2 * (α * 100000) ^ 2
              + (Work.Spaces.Gam α θ) ^ 2 * (B i) ^ 2 * s ^ 4))
            * s ^ (-(Work.Spaces.gam α)) := mul_le_mul_of_nonneg_right hstep hwgam
      _ = 2 * ((α * 100000) ^ 2 * ((Work.Spaces.Gam α θ) ^ 2 * s ^ (-(Work.Spaces.gam α)))
            + (B i) ^ 2 * (s ^ 4 * ((Work.Spaces.Gam α θ) ^ 2
                * s ^ (-(Work.Spaces.gam α))))) := by ring
      _ ≤ 2 * ((α * 100000) ^ 2 * s ^ (2 * α / 3 - Work.Spaces.gam α) + (B i) ^ 2 * 1) := by
          refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
          exact add_le_add (mul_le_mul_of_nonneg_left hkey1 (sq_nonneg _))
            (mul_le_mul_of_nonneg_left hkey2 (sq_nonneg _))
      _ = 2 * (α * 100000) ^ 2 * s ^ (2 * α / 3 - Work.Spaces.gam α) + 2 * (B i) ^ 2 := by
          ring
  -- the sum of the `i ≥ 1` terms
  have hsum : (∑ i ∈ Finset.range 7,
        (if 1 ≤ i then (Work.Spaces.dthU^[i] (sinSqGam α) θ) ^ 2
          * s ^ (-(Work.Spaces.gam α)) else 0))
      ≤ 14 * (α * 100000) ^ 2 * s ^ (2 * α / 3 - Work.Spaces.gam α) + T := by
    have hstep1 : (∑ i ∈ Finset.range 7,
          (if 1 ≤ i then (Work.Spaces.dthU^[i] (sinSqGam α) θ) ^ 2
            * s ^ (-(Work.Spaces.gam α)) else 0))
        ≤ ∑ i ∈ Finset.range 7,
            (if 1 ≤ i then 2 * (α * 100000) ^ 2 * s ^ (2 * α / 3 - Work.Spaces.gam α)
              + 2 * (B i) ^ 2 else 0) := by
      refine Finset.sum_le_sum fun i hi => ?_
      by_cases h1 : 1 ≤ i
      · have hi6 : i ≤ 6 := by have := Finset.mem_range.mp hi; omega
        rw [if_pos h1, if_pos h1]
        exact hterm i h1 hi6
      · rw [if_neg h1, if_neg h1]
    have hstep2 : (∑ i ∈ Finset.range 7,
            (if 1 ≤ i then 2 * (α * 100000) ^ 2 * s ^ (2 * α / 3 - Work.Spaces.gam α)
              + 2 * (B i) ^ 2 else 0))
        ≤ ∑ i ∈ Finset.range 7,
            (2 * (α * 100000) ^ 2 * s ^ (2 * α / 3 - Work.Spaces.gam α) + 2 * (B i) ^ 2) := by
      refine Finset.sum_le_sum fun i _ => ?_
      by_cases h1 : 1 ≤ i
      · rw [if_pos h1]
      · rw [if_neg h1]
        exact add_nonneg (mul_nonneg (by positivity) (Real.rpow_nonneg hs0 _)) (by positivity)
    have hstep3 : (∑ i ∈ Finset.range 7,
            (2 * (α * 100000) ^ 2 * s ^ (2 * α / 3 - Work.Spaces.gam α) + 2 * (B i) ^ 2))
        = 14 * (α * 100000) ^ 2 * s ^ (2 * α / 3 - Work.Spaces.gam α) + T := by
      rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul, ← hT]
      ring
    linarith [hstep1, hstep2, hstep3.le, hstep3.ge]
  -- assemble
  have hgoal : AngBlk α (sinSqGam α) θ
      = (sinSqGam α θ) ^ 2 * s ^ (-(Work.Spaces.eta))
        + ∑ i ∈ Finset.range 7, (if 1 ≤ i then
            (Work.Spaces.dthU^[i] (sinSqGam α) θ) ^ 2 * s ^ (-(Work.Spaces.gam α)) else 0) := by
    simp only [AngBlk, ← hs]
  rw [hgoal]
  linarith [h0, hsum]

/-! ## The core uniform bound for the unnormalised profile -/

theorem angBlk_sinSqGam_bound : ∃ Bang0 : ℝ, 0 < Bang0 ∧ ∀ α ∈ Set.Ioc (0 : ℝ) 1,
    MeasureTheory.IntegrableOn (fun θ => AngBlk α (sinSqGam α) θ) Work.Spaces.Iθ ∧
    (∫ θ in Work.Spaces.Iθ, AngBlk α (sinSqGam α) θ) ≤ Bang0 := by
  -- the jet bound (local Leibniz + the two factor bounds)
  obtain ⟨B, hBnn, hB⟩ : ∃ B : ℕ → ℝ, (∀ i, 0 ≤ B i) ∧
      ∀ α ∈ Set.Ioc (0 : ℝ) 1, ∀ i : ℕ, 1 ≤ i → i ≤ 6 → ∀ θ ∈ Work.Spaces.Iθ,
        |Work.Spaces.dthU^[i] (sinSqGam α) θ|
          ≤ Work.Spaces.Gam α θ * (α * 100000 + B i * (Real.sin (2 * θ)) ^ 2) := by
    refine Work.FTS.StrongEps.E4R3.Nblock6.Auxiliary.dthU_iter_Gfun_bound ?_
    intro β hβmem j hj6
    exact Work.FTS.StrongEps.E4R3.Nblock6.Auxiliary.dthU_iter_mul_Ioo j
      (fun θ => Real.sin θ ^ 2) (fun θ => Work.Spaces.Gam β θ)
      (fun k _ => (dthU_iter_contDiffOn_Ioo
        (((Real.contDiff_sin (n := ∞)).pow 2).contDiffOn) k).differentiableOn (by simp))
      (fun k _ => (dthU_iter_contDiffOn_Ioo (gam_contDiffOn_Ioo β) k).differentiableOn
        (by simp))
  -- the two `sin(2θ)`-block integrals
  have hIntBlock : ∀ α ∈ Set.Ioc (0 : ℝ) 1,
      MeasureTheory.IntegrableOn
          (fun θ : ℝ => (Real.sin (2 * θ)) ^ (2 * α / 3 - Work.Spaces.eta)) Work.Spaces.Iθ ∧
      (∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (2 * α / 3 - Work.Spaces.eta)) ≤ 400 ∧
      MeasureTheory.IntegrableOn
          (fun θ : ℝ => (Real.sin (2 * θ)) ^ (2 * α / 3 - Work.Spaces.gam α)) Work.Spaces.Iθ ∧
      (∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (2 * α / 3 - Work.Spaces.gam α))
        ≤ 120 / (17 * α) :=
    Work.FTS.StrongEps.E4R3.Nblock6.Auxiliary.sin_two_rpow_block_integrals
  have hBangsq : 0 ≤ ∑ i ∈ Finset.range 7, 2 * (B i) ^ 2 :=
    Finset.sum_nonneg fun i _ => by positivity
  refine ⟨400 + (14 * 120 / 17) * (10 : ℝ) ^ 10
      + Real.pi / 2 * (∑ i ∈ Finset.range 7, 2 * (B i) ^ 2) + 1, ?_, fun α hαmem => ?_⟩
  · have hπ : (0 : ℝ) ≤ Real.pi / 2 := by positivity
    have := mul_nonneg hπ hBangsq
    linarith
  obtain ⟨hα, hα1⟩ := hαmem
  have hmem : α ∈ Set.Ioc (0 : ℝ) 1 := ⟨hα, hα1⟩
  obtain ⟨hEAint, hEAle, hEGint, hEGle⟩ := hIntBlock α hmem
  set T : ℝ := ∑ i ∈ Finset.range 7, 2 * (B i) ^ 2 with hT
  have hTnn : 0 ≤ T := by rw [hT]; exact hBangsq
  have hIntA : MeasureTheory.IntegrableOn
      (fun θ : ℝ => (Real.sin (2 * θ)) ^ (2 * α / 3 - Work.Spaces.eta)) Work.Spaces.Iθ := hEAint
  have hIntB : MeasureTheory.IntegrableOn
      (fun θ : ℝ => 14 * (α * 100000) ^ 2
        * (Real.sin (2 * θ)) ^ (2 * α / 3 - Work.Spaces.gam α)) Work.Spaces.Iθ :=
    hEGint.const_mul _
  have hIntT : MeasureTheory.IntegrableOn (fun _ : ℝ => T) Work.Spaces.Iθ :=
    MeasureTheory.integrableOn_const (C := T) volume_Iθ_ne_top
  have hMajInt : MeasureTheory.IntegrableOn
      (fun θ : ℝ => (Real.sin (2 * θ)) ^ (2 * α / 3 - Work.Spaces.eta)
        + 14 * (α * 100000) ^ 2 * (Real.sin (2 * θ)) ^ (2 * α / 3 - Work.Spaces.gam α) + T)
      Work.Spaces.Iθ := (hIntA.add hIntB).add hIntT
  -- measurability
  have hIoo : Set.Ioo (0 : ℝ) (Real.pi / 2) =ᵐ[volume] Work.Spaces.Iθ := by
    rw [Work.Spaces.Iθ]; exact MeasureTheory.Ioo_ae_eq_Icc
  have hcontWeight : ContinuousOn (fun θ : ℝ => (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))
      (Set.Ioo 0 (Real.pi / 2)) := by
    refine ContinuousOn.rpow_const (by fun_prop) ?_
    intro θ hθ
    exact Or.inl (ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1])
      (by linarith [hθ.2, Real.pi_pos])))
  have hcontWeightEta : ContinuousOn (fun θ : ℝ => (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
      (Set.Ioo 0 (Real.pi / 2)) := by
    refine ContinuousOn.rpow_const (by fun_prop) ?_
    intro θ hθ
    exact Or.inl (ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1])
      (by linarith [hθ.2, Real.pi_pos])))
  have hmeasJet : ∀ i : ℕ, i ≤ 6 → AEStronglyMeasurable
      (fun θ : ℝ => (Work.Spaces.dthU^[i] (sinSqGam α) θ) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) (volume.restrict Work.Spaces.Iθ) := by
    intro i _
    have hcont_i : ContinuousOn (fun θ : ℝ => Work.Spaces.dthU^[i] (sinSqGam α) θ)
        (Set.Ioo 0 (Real.pi / 2)) :=
      (dthU_iter_contDiffOn_Ioo (sinSqGam_contDiffOn_Ioo α) i).continuousOn
    rw [← MeasureTheory.Measure.restrict_congr_set hIoo]
    exact ((hcont_i.pow 2).mul hcontWeight).aestronglyMeasurable measurableSet_Ioo
  have hmeas0 : AEStronglyMeasurable
      (fun θ : ℝ => (sinSqGam α θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
      (volume.restrict Work.Spaces.Iθ) := by
    have hcont0 : ContinuousOn (fun θ : ℝ => sinSqGam α θ) (Set.Ioo 0 (Real.pi / 2)) :=
      (sinSqGam_contDiffOn_Ioo α).continuousOn
    rw [← MeasureTheory.Measure.restrict_congr_set hIoo]
    exact ((hcont0.pow 2).mul hcontWeightEta).aestronglyMeasurable measurableSet_Ioo
  have hmeasSum : AEStronglyMeasurable
      (∑ i ∈ Finset.range 7, fun θ : ℝ => (if 1 ≤ i then
        (Work.Spaces.dthU^[i] (sinSqGam α) θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
        else 0)) (volume.restrict Work.Spaces.Iθ) := by
    refine Finset.aestronglyMeasurable_sum _ fun i hi => ?_
    by_cases h1 : 1 ≤ i
    · have hi6 : i ≤ 6 := by have := Finset.mem_range.mp hi; omega
      simpa only [h1, if_true] using hmeasJet i hi6
    · simpa only [h1, if_false] using
        (measurable_const : Measurable (fun _ : ℝ => (0 : ℝ))).aestronglyMeasurable
  have hmeas : AEStronglyMeasurable (fun θ => AngBlk α (sinSqGam α) θ)
      (volume.restrict Work.Spaces.Iθ) := by
    have hstep : (fun θ => AngBlk α (sinSqGam α) θ)
        = (fun θ : ℝ => (sinSqGam α θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
          + (∑ i ∈ Finset.range 7, fun θ : ℝ => (if 1 ≤ i then
              (Work.Spaces.dthU^[i] (sinSqGam α) θ) ^ 2
                * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) else 0)) := by
      funext θ
      simp only [AngBlk, Pi.add_apply, Finset.sum_apply]
    rw [hstep]
    exact hmeas0.add hmeasSum
  -- nonnegativity and the pointwise bound
  have hnn : ∀ θ ∈ Work.Spaces.Iθ, 0 ≤ AngBlk α (sinSqGam α) θ := by
    intro θ hθ
    have hs0 := sin_two_nonneg_Iθ hθ
    simp only [AngBlk]
    refine add_nonneg (mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hs0 _)) ?_
    refine Finset.sum_nonneg fun i _ => ?_
    by_cases h1 : 1 ≤ i
    · simp only [h1, if_true]
      exact mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hs0 _)
    · simp only [h1, if_false]; exact le_refl 0
  have hpoint : ∀ θ ∈ Work.Spaces.Iθ, AngBlk α (sinSqGam α) θ
      ≤ (Real.sin (2 * θ)) ^ (2 * α / 3 - Work.Spaces.eta)
        + 14 * (α * 100000) ^ 2 * (Real.sin (2 * θ)) ^ (2 * α / 3 - Work.Spaces.gam α) + T :=
    fun θ hθ => angBlk_le_majorant hα hα1 hBnn (hB α hmem) T hT hθ
  -- integrability of `AngBlk` by domination
  have hAngInt : MeasureTheory.IntegrableOn (fun θ => AngBlk α (sinSqGam α) θ)
      Work.Spaces.Iθ :=
    hMajInt.mono' hmeas (by
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ hθ
      rw [Real.norm_of_nonneg (hnn θ hθ)]
      exact hpoint θ hθ)
  refine ⟨hAngInt, ?_⟩
  -- the integral bound
  have hmono := MeasureTheory.integral_mono_of_nonneg
    (f := fun θ => AngBlk α (sinSqGam α) θ)
    (g := fun θ : ℝ => (Real.sin (2 * θ)) ^ (2 * α / 3 - Work.Spaces.eta)
      + 14 * (α * 100000) ^ 2 * (Real.sin (2 * θ)) ^ (2 * α / 3 - Work.Spaces.gam α) + T)
    (by filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ hθ
        exact hnn θ hθ)
    hMajInt
    (by filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ hθ
        exact hpoint θ hθ)
  have hval : (∫ θ in Work.Spaces.Iθ, ((Real.sin (2 * θ)) ^ (2 * α / 3 - Work.Spaces.eta)
        + 14 * (α * 100000) ^ 2 * (Real.sin (2 * θ)) ^ (2 * α / 3 - Work.Spaces.gam α) + T))
      = (∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (2 * α / 3 - Work.Spaces.eta))
        + 14 * (α * 100000) ^ 2
            * (∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (2 * α / 3 - Work.Spaces.gam α))
        + (Real.pi / 2) * T := by
    have hsplit1 : (∫ θ in Work.Spaces.Iθ, ((Real.sin (2 * θ)) ^ (2 * α / 3 - Work.Spaces.eta)
          + 14 * (α * 100000) ^ 2 * (Real.sin (2 * θ)) ^ (2 * α / 3 - Work.Spaces.gam α) + T))
        = (∫ θ in Work.Spaces.Iθ, ((Real.sin (2 * θ)) ^ (2 * α / 3 - Work.Spaces.eta)
            + 14 * (α * 100000) ^ 2 * (Real.sin (2 * θ)) ^ (2 * α / 3 - Work.Spaces.gam α)))
          + (∫ θ in Work.Spaces.Iθ, T) :=
      MeasureTheory.integral_add (hIntA.add hIntB) hIntT
    have hsplit2 : (∫ θ in Work.Spaces.Iθ, ((Real.sin (2 * θ)) ^ (2 * α / 3 - Work.Spaces.eta)
          + 14 * (α * 100000) ^ 2 * (Real.sin (2 * θ)) ^ (2 * α / 3 - Work.Spaces.gam α)))
        = (∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (2 * α / 3 - Work.Spaces.eta))
          + (∫ θ in Work.Spaces.Iθ, 14 * (α * 100000) ^ 2
              * (Real.sin (2 * θ)) ^ (2 * α / 3 - Work.Spaces.gam α)) :=
      MeasureTheory.integral_add hIntA hIntB
    rw [hsplit1, hsplit2, MeasureTheory.integral_const_mul, MeasureTheory.setIntegral_const,
      volume_real_Iθ, smul_eq_mul]
  have hb2 : 14 * (α * 100000) ^ 2
        * (∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (2 * α / 3 - Work.Spaces.gam α))
      ≤ 14 * (α * 100000) ^ 2 * (120 / (17 * α)) :=
    mul_le_mul_of_nonneg_left hEGle (by positivity)
  have hb3 : 14 * (α * 100000) ^ 2 * (120 / (17 * α)) ≤ (14 * 120 / 17) * (10 : ℝ) ^ 10 := by
    rw [show 14 * (α * 100000) ^ 2 * (120 / (17 * α))
        = (14 * 120 / 17) * (10 : ℝ) ^ 10 * α by
      field_simp
      ring]
    nlinarith [hα, hα1]
  linarith [hmono, hval, hEAle, hb2, hb3]

/-! ## The requested statement -/

theorem angBlk_sinSqGam : ∀ α ∈ Set.Ioc (0 : ℝ) 1, ∃ Bang : ℝ, 0 < Bang ∧
    MeasureTheory.IntegrableOn (fun θ => Work.FTS.StrongEps.E4R3.Apriori4Proofs.blocks.N0Aux.AngBlk α
      (fun θ => -(Real.sin θ) ^ 2 * Work.Spaces.Gam α θ / Work.Spaces.c α) θ) Work.Spaces.Iθ ∧
    (∫ θ in Work.Spaces.Iθ, Work.FTS.StrongEps.E4R3.Apriori4Proofs.blocks.N0Aux.AngBlk α
      (fun θ => -(Real.sin θ) ^ 2 * Work.Spaces.Gam α θ / Work.Spaces.c α) θ) ≤ Bang := by
  intro α hαmem
  obtain ⟨hα, hα1⟩ := hαmem
  have hmem : α ∈ Set.Ioc (0 : ℝ) 1 := ⟨hα, hα1⟩
  obtain ⟨B0, hB0pos, hB0⟩ := angBlk_sinSqGam_bound
  obtain ⟨hIntG, hleG⟩ := hB0 α hmem
  have hc10 : (1 : ℝ) / 10 ≤ Work.Spaces.c α := (Work.Spaces.c_bounds α hα hα1).1
  have hcpos : 0 < Work.Spaces.c α := by linarith
  have hinv_le : (Work.Spaces.c α)⁻¹ ≤ 10 := by
    rw [inv_le_comm₀ hcpos (by norm_num : (0 : ℝ) < 10)]
    norm_num
    linarith
  have hinvnn : 0 ≤ (Work.Spaces.c α)⁻¹ := le_of_lt (inv_pos.mpr hcpos)
  have hc2 : (-(Work.Spaces.c α)⁻¹) ^ 2 ≤ 100 := by
    nlinarith [hinv_le, hinvnn]
  have hfun : (fun θ : ℝ => -(Real.sin θ) ^ 2 * Work.Spaces.Gam α θ / Work.Spaces.c α)
      = fun θ => (-(Work.Spaces.c α)⁻¹) * sinSqGam α θ := by
    funext θ; simp only [sinSqGam]; ring
  have hAng : ∀ θ : ℝ, AngBlk α (fun θ => (-(Work.Spaces.c α)⁻¹) * sinSqGam α θ) θ
      = (-(Work.Spaces.c α)⁻¹) ^ 2 * AngBlk α (sinSqGam α) θ :=
    fun θ => AngBlk_const_mul α (-(Work.Spaces.c α)⁻¹) (sinSqGam α) θ
  rw [hfun]
  simp only [hAng]
  refine ⟨100 * B0 + 1, by positivity, ?_, ?_⟩
  · exact hIntG.const_mul _
  · rw [MeasureTheory.integral_const_mul]
    calc (-(Work.Spaces.c α)⁻¹) ^ 2 * (∫ θ in Work.Spaces.Iθ, AngBlk α (sinSqGam α) θ)
        ≤ (-(Work.Spaces.c α)⁻¹) ^ 2 * B0 := mul_le_mul_of_nonneg_left hleG (sq_nonneg _)
      _ ≤ 100 * B0 := mul_le_mul_of_nonneg_right hc2 hB0pos.le
      _ ≤ 100 * B0 + 1 := by linarith

end Work.FTS.StrongEps.E4R3.Nblock6.aux
