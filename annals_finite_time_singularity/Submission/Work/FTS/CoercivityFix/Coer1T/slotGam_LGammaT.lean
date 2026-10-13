/-
# `Coer1T` — the `D_θ`-slot (`P₄`) of the level-1 coercivity of `𝓛_Γ^T`

This file proves the fourth slot estimate of `NOTES_coer1_LGammaT.md`, the paper's
Proposition `prop:thetaderivative` in the *interior* class `CoerAdm`:

  `(17/40 − 1/100)·EDth α f − 10⁻⁶·Ef f ≤ ⟨D_θ(𝓛_Γ^T f), D_θ f⟩_{w²/sin(2θ)^γ}`.

## The route

`𝓛_Γ^T = 𝓛̂ + Corr` (`CoercivityFix.LGammaT_eq_Lhat_add_Corr`), and `Corr` is a `θ`-dependent
multiple of `Γ(θ)` with a `θ`-independent coefficient, so differentiating in `θ` gives back the
two `D_θΓ`-terms `T2`, `T4` of `Coercivity.thetaAux`:

  `D_θ(𝓛_Γ^T f) = D_θ(𝓛̂ f) + T2 α f + T4 α f`     (`Dth_LGammaT_eq`),

and `D_θ` commutes with the clean operator `𝓛̂` exactly, so
`D_θ(𝓛̂ f) = 𝓛̂(D_θ f)` (`LhatCalc.Dth_Lhat`).

Splitting the pairing and using

* `Coer1.est_D` — the coercivity of the clean operator on the `γ`-slot:
  `(17/40)·EDth ≤ ⟨D_θ(𝓛̂ f), D_θ f⟩_γ`;
* `wip_T2_ge_Q` — the first `D_θΓ`-term, bounded by Cauchy–Schwarz with the *sharp* Young split
  `(1/200, 3.2·10⁷α)`;
* `wip_T4_ge_Q` — the projector `D_θΓ`-term, bounded by `(1/200)·EDth` alone (its size is
  `O(α)·EDth` via `C₀² ≤ EDthW ≤ EDth`),

the arithmetic `1/200 + 1/200 = 1/100` and `3.2·10⁷·α ≤ 10⁻⁶` (for `α ≤ 10⁻¹⁴`) closes the
statement.

The reductions above are collected in `slotGam_LGammaT_core`, which assumes the three
deliverables as hypotheses; the named target is then the two-line application.
-/
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.FTS.Vocab
import Submission.Work.Coercivity.Defs
import Submission.Work.Coercivity.Basic
import Submission.Work.Coercivity.thetaAux
import Submission.Work.Coercivity.thetaDerivative
import Submission.Work.Coercivity.wip_Aop_ge
import Submission.Work.Coercivity.EL12z_le
import Submission.Work.Coercivity.L2CoercivityTransport
import Submission.Work.FTS.CoercivityFix.Basic
import Submission.Work.FTS.CoercivityFix.Coer1.zIBP
import Submission.Work.FTS.CoercivityFix.Coer1.thetaIBP
import Submission.Work.FTS.CoercivityFix.Coer1.IntFacts
import Submission.Work.FTS.CoercivityFix.Coer1.Estimates
import Submission.Work.FTS.CoercivityFix.LhatCalc.Dth_Lhat
import Submission.Work.FTS.LocData.SmoothChain
import Submission.Work.FTS.CoercivityFix.Coer1T.C0_sq_le_EDthW_Q
import Submission.Work.FTS.CoercivityFix.Coer1T.intDth_Lhat_gam
import Submission.Work.FTS.CoercivityFix.Coer1T.wip_T4_ge_Q
import Submission.Work.FTS.GalerkinFix.RegQ.regQ_mono

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.CoercivityFix.Coer1T

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-! ## The `θ`-derivative of `𝓛_Γ^T` in the interior class

`𝓛_Γ^T f = 𝓛̂ f + Γ(θ)·K(z)` with a `θ`-independent `K`, so on the open quadrant the `θ`-slice
of `𝓛_Γ^T f` is the sum of the `θ`-slice of `𝓛̂ f` and of `Γ(θ)·K`; differentiating and
multiplying by `sin(2θ)` gives `D_θ(𝓛̂ f) + T2 + T4`. -/

/-- The `θ`-independent coefficient `K(z)` of the `Corr`-part: the `Corr` of `f` is
`Γ(θ)·K(z)`. -/
def slotK (α : ℝ) (f : ℝ → ℝ → ℝ) (z : ℝ) : ℝ :=
  -(2 * z / (Work.Spaces.c α * (1 + z) ^ 2)) * Work.Coercivity.L12f f z
    + (2 * z ^ 2 / (1 + z) ^ 3) * Work.Coercivity.C0 f / Work.Spaces.c α

/-- **The pointwise expansion of `D_θ(𝓛_Γ^T f)` on the open quadrant**, in the interior class
`SmoothQuad`.  This is the `SmoothQuad`-analogue of `Coercivity.dth_LGammaT_expansion`; the
coercive part is written with the clean operator `𝓛̂` (which is what `D_θ` commutes with). -/
theorem Dth_LGammaT_eq (α : ℝ) {f : ℝ → ℝ → ℝ} (hf : Work.FTS.LocData.SmoothQuad f)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    Work.Spaces.Dth (Work.Coercivity.LGammaT α f) z θ
      = Work.Spaces.Dth (Work.FTS.CoercivityFix.Lhat f) z θ
        + Work.Coercivity.T2 α f z θ + Work.Coercivity.T4 α f z θ := by
  have hz1 : z ∈ Set.Ioi (-1 : ℝ) := by simp only [Set.mem_Ioi]; linarith
  have hslice : (fun θ' => Work.Coercivity.LGammaT α f z θ')
      = (fun θ' => Work.FTS.CoercivityFix.Lhat f z θ'
          + slotK α f z * Work.Spaces.Gam α θ') := by
    funext θ'
    rw [Work.FTS.CoercivityFix.LGammaT_eq_Lhat_add_Corr α f]
    simp only [Pi.add_apply, Work.FTS.CoercivityFix.Corr_eq, slotK]
    rw [Work.Coercivity.C0]
    ring
  have hf_diff : DifferentiableAt ℝ (fun θ' => f z θ') θ :=
    ((hf.curry_θ hz1).differentiableOn Work.FTS.LocData.smoothOrder_ne_zero).differentiableAt
      (isOpen_Ioo.mem_nhds hθ)
  have hpz_diff : DifferentiableAt ℝ (fun θ' => Work.Spaces.pz f z θ') θ := by
    have hsq : Work.FTS.LocData.SmoothQuad (Work.Spaces.pz f) :=
      Work.FTS.LocData.contDiffOn_pz (isOpen_Ioi.prod isOpen_Ioo) hf
    exact ((hsq.curry_θ hz1).differentiableOn Work.FTS.LocData.smoothOrder_ne_zero).differentiableAt
      (isOpen_Ioo.mem_nhds hθ)
  have hDth_diff : DifferentiableAt ℝ (fun θ' => Work.Spaces.Dth f z θ') θ := by
    have hsq : Work.FTS.LocData.SmoothQuad (Work.Spaces.Dth f) :=
      Work.FTS.LocData.contDiffOn_Dth (isOpen_Ioi.prod isOpen_Ioo) hf
    exact ((hsq.curry_θ hz1).differentiableOn Work.FTS.LocData.smoothOrder_ne_zero).differentiableAt
      (isOpen_Ioo.mem_nhds hθ)
  have hLhat_diff : DifferentiableAt ℝ (fun θ' => Work.FTS.CoercivityFix.Lhat f z θ') θ := by
    have hfun : (fun θ' => Work.FTS.CoercivityFix.Lhat f z θ') = (fun θ' => f z θ'
        + z * Work.Spaces.pz f z θ' - (2 / (1 + z)) * f z θ'
        - (3 / (1 + z)) * Work.Spaces.Dth f z θ') := by
      funext θ'
      rw [Work.FTS.CoercivityFix.Lhat_eq]
      simp only [Work.Spaces.Dz]
      ring
    rw [hfun]
    exact ((hf_diff.add (hpz_diff.const_mul z)).sub (hf_diff.const_mul (2 / (1 + z)))).sub
      (hDth_diff.const_mul (3 / (1 + z)))
  have hG_diff : DifferentiableAt ℝ (fun θ' => Work.Spaces.Gam α θ') θ :=
    Work.Coercivity.differentiableAt_Gam α hθ
  have hderiv : deriv (fun θ' => Work.Coercivity.LGammaT α f z θ') θ
      = deriv (fun θ' => Work.FTS.CoercivityFix.Lhat f z θ') θ
        + slotK α f z * deriv (fun θ' => Work.Spaces.Gam α θ') θ := by
    rw [hslice]
    have hd2 : DifferentiableAt ℝ (fun θ' => slotK α f z * Work.Spaces.Gam α θ') θ :=
      hG_diff.const_mul _
    rw [show deriv (fun θ' => Work.FTS.CoercivityFix.Lhat f z θ'
          + slotK α f z * Work.Spaces.Gam α θ') θ
        = deriv ((fun θ' => Work.FTS.CoercivityFix.Lhat f z θ')
            + fun y => slotK α f z * Work.Spaces.Gam α y) θ from rfl]
    rw [deriv_add hLhat_diff hd2, deriv_const_mul_field]
  have key : Work.Spaces.Dth (Work.Coercivity.LGammaT α f) z θ
      = Work.Spaces.Dth (Work.FTS.CoercivityFix.Lhat f) z θ
        + Real.sin (2 * θ) * (slotK α f z * deriv (fun t => Work.Spaces.Gam α t) θ) := by
    simp only [Work.Spaces.Dth, Work.Spaces.pth]
    rw [hderiv]
    ring
  rw [key]
  have hT2T4 : Real.sin (2 * θ) * (slotK α f z * deriv (fun t => Work.Spaces.Gam α t) θ)
      = Work.Coercivity.T2 α f z θ + Work.Coercivity.T4 α f z θ := by
    rw [Work.Coercivity.T2, Work.Coercivity.T4, Work.Coercivity.DthGam_eq (α := α) z θ, slotK]
    ring
  rw [hT2T4]
  ring

/-! ## The core of the slot estimate

The three analytic inputs (the two `D_θΓ`-bounds and the integrability of the clean pairing)
are hypotheses here; `slotGam_LGammaT` below supplies them from the sibling files. -/

theorem slotGam_LGammaT_core (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1 / 10 ^ 14) {f : ℝ → ℝ → ℝ}
    (hf : Work.FTS.Nonlin.CoerAdm α f) (hHH : Work.Coercivity.HardyHyp f)
    (hG2 : Work.Coercivity.GammaPointwiseBnd α)
    (hT2 : MeasureTheory.IntegrableOn
        (Function.uncurry (fun z θ => Work.Coercivity.T2 α f z θ * Work.Spaces.Dth f z θ
          * Work.Coercivity.thetaW α z θ)) (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)
      ∧ -((1 / 200) * Work.Coercivity.EDth α f + 32000000 * α * Work.Coercivity.Ef f)
        ≤ Work.Coercivity.wip (Work.Coercivity.thetaW α)
            (Work.Coercivity.T2 α f) (Work.Spaces.Dth f))
    (hT4 : MeasureTheory.IntegrableOn
        (Function.uncurry (fun z θ => Work.Coercivity.T4 α f z θ * Work.Spaces.Dth f z θ
          * Work.Coercivity.thetaW α z θ)) (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)
      ∧ -((1 / 200) * Work.Coercivity.EDth α f)
        ≤ Work.Coercivity.wip (Work.Coercivity.thetaW α)
            (Work.Coercivity.T4 α f) (Work.Spaces.Dth f))
    (hLint : MeasureTheory.IntegrableOn
        (Function.uncurry (fun z θ => Work.Spaces.Dth (Work.FTS.CoercivityFix.Lhat f) z θ
          * Work.Spaces.Dth f z θ * Work.Coercivity.thetaW α z θ))
        (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)) :
    (17 / 40 - 1 / 100) * Work.Coercivity.EDth α f - (1 / 10 ^ 6) * Work.Coercivity.Ef f
      ≤ Work.Coercivity.wip (fun z θ => Work.Spaces.w z ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))
          (Work.Spaces.Dth (Work.Coercivity.LGammaT α f)) (Work.Spaces.Dth f) := by
  have hα4 : α ≤ 1 / 4 := by linarith
  obtain ⟨hsq, hm, hb⟩ := hf.reg
  have hf2 : Work.FTS.Nonlin.RegQ α 2 f :=
    Work.FTS.GalerkinFix.RegQ.regQ_mono hf.reg (by norm_num)
  -- the a.e. pointwise expansion of the `D_θ`-derivative
  have hae : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
      ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      Work.Spaces.Dth (Work.Coercivity.LGammaT α f) z θ
        = Work.Spaces.Dth (Work.FTS.CoercivityFix.Lhat f) z θ
          + Work.Coercivity.T2 α f z θ + Work.Coercivity.T4 α f z θ := by
    filter_upwards [Work.FTS.CoercivityFix.Coer1.ae_restrict_Iz_pos] with z hz
    filter_upwards [Work.FTS.CoercivityFix.Coer1.ae_restrict_Iθ_mem_Ioo] with θ hθ
    exact Dth_LGammaT_eq α hsq hz hθ
  -- integrability of the two-term sum `D_θ𝓛̂ f + T2 f`
  have hA2 : MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => (Work.Spaces.Dth (Work.FTS.CoercivityFix.Lhat f) z θ
          + Work.Coercivity.T2 α f z θ) * Work.Spaces.Dth f z θ
        * Work.Coercivity.thetaW α z θ)) (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) := by
    have h := hLint.add hT2.1
    refine h.congr (MeasureTheory.ae_restrict_of_forall_mem
      (measurableSet_Ici.prod measurableSet_Icc) (fun p _ => ?_))
    rcases p with ⟨z, θ⟩
    simp only [Function.uncurry_apply_pair, Pi.add_apply]
    ring
  -- the split of the pairing into its three summands
  have hsplit : Work.Coercivity.wip (Work.Coercivity.thetaW α)
        (fun z θ => Work.Spaces.Dth (Work.FTS.CoercivityFix.Lhat f) z θ
          + Work.Coercivity.T2 α f z θ + Work.Coercivity.T4 α f z θ) (Work.Spaces.Dth f)
      = Work.Coercivity.wip (Work.Coercivity.thetaW α)
          (Work.Spaces.Dth (Work.FTS.CoercivityFix.Lhat f)) (Work.Spaces.Dth f)
        + Work.Coercivity.wip (Work.Coercivity.thetaW α)
            (Work.Coercivity.T2 α f) (Work.Spaces.Dth f)
        + Work.Coercivity.wip (Work.Coercivity.thetaW α)
            (Work.Coercivity.T4 α f) (Work.Spaces.Dth f) := by
    rw [Work.Coercivity.wip_add_left (g := fun z θ =>
          Work.Spaces.Dth (Work.FTS.CoercivityFix.Lhat f) z θ + Work.Coercivity.T2 α f z θ)
        (h := Work.Coercivity.T4 α f) (k := Work.Spaces.Dth f) hA2 hT4.1,
      Work.Coercivity.wip_add_left (g := Work.Spaces.Dth (Work.FTS.CoercivityFix.Lhat f))
        (h := Work.Coercivity.T2 α f) (k := Work.Spaces.Dth f) hLint hT2.1]
  -- the coercivity of the clean operator on the `γ`-slot
  have hD := Work.FTS.CoercivityFix.Coer1.est_D α hα hα4 hf2
  have hD' : (17 / 40) * Work.Coercivity.EDth α f
      ≤ Work.Coercivity.wip (Work.Coercivity.thetaW α)
          (Work.Spaces.Dth (Work.FTS.CoercivityFix.Lhat f)) (Work.Spaces.Dth f) := by
    rw [Work.FTS.CoercivityFix.Coer1.EDth_eq_En α f, ← Work.FTS.CoercivityFix.Coer1.Rho_gam α]
    exact hD
  -- the two energies are nonnegative
  have hEfnn : 0 ≤ Work.Coercivity.Ef f := by
    rw [Work.Coercivity.Ef, Work.Spaces.L2Sq]
    exact integral_nonneg fun z => integral_nonneg fun θ => sq_nonneg _
  have hEDnn : 0 ≤ Work.Coercivity.EDth α f := by
    rw [Work.Coercivity.EDth, Work.Spaces.L2Sq]
    exact integral_nonneg fun z => integral_nonneg fun θ => sq_nonneg _
  -- the smallness of `3.2·10⁷ α`
  have hαb : (32000000 : ℝ) * α ≤ 1 / 10 ^ 6 := by
    have h1 : (32000000 : ℝ) * (1 / 10 ^ 14) = 32 / 10 ^ 8 := by norm_num
    calc (32000000 : ℝ) * α ≤ 32000000 * (1 / 10 ^ 14) :=
          mul_le_mul_of_nonneg_left hα1 (by norm_num)
      _ = 32 / 10 ^ 8 := h1
      _ ≤ 1 / 10 ^ 6 := by norm_num
  have hsmall : 32000000 * α * Work.Coercivity.Ef f
      ≤ (1 / 10 ^ 6) * Work.Coercivity.Ef f :=
    mul_le_mul_of_nonneg_right hαb hEfnn
  change (17 / 40 - 1 / 100) * Work.Coercivity.EDth α f - (1 / 10 ^ 6) * Work.Coercivity.Ef f
    ≤ Work.Coercivity.wip (Work.Coercivity.thetaW α)
        (Work.Spaces.Dth (Work.Coercivity.LGammaT α f)) (Work.Spaces.Dth f)
  rw [Work.Coercivity.wip_congr_ae hae, hsplit]
  linarith [hD', hT2.2, hT4.2, hsmall]

/-! ## The `T2`-bound: a short Cauchy–Schwarz route

`T2 α f = -D_θΓ(θ)·A(z)` with `A(z) = (2z/(c(1+z)²))·L₁₂(f)(z)` is a product of a function of
`θ` alone and one of `z` alone, so the `γ`-weighted pairing factors as the product of *two*
`L²`-norms:

  `|⟨T2 α f, D_θ f⟩_γ| ≤ ‖D_θΓ·sin^{-γ/2}‖₂ · ‖A·w‖₂ · ‖D_θf·w·sin^{-γ/2}‖₂`.

The three factors are `γamDth_l2_bound` (`∫ (D_θΓ)²sin^{-γ} ≤ 100α`), the Hardy inequality
`EL12z ≤ 16Ef` (giving `∫ (A w)² = (4/c²)EL12z ≤ 6400 Ef`) and `EDth α f` itself.  This gives
`800·√α·√(Ef)·√(EDth)`, which the Young split `(1/200, 3.2·10⁷α)` turns into the estimate
needed by the slot. -/

theorem wip_T2_ge_Q_crude (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) {f : ℝ → ℝ → ℝ}
    (hf : Work.FTS.Nonlin.RegQ α 2 f) (hfH : Work.Coercivity.HardyHyp f)
    (hΓ2 : Work.Coercivity.GammaPointwiseBnd α) :
    MeasureTheory.IntegrableOn
        (Function.uncurry (fun z θ => Work.Coercivity.T2 α f z θ * Work.Spaces.Dth f z θ
          * Work.Coercivity.thetaW α z θ)) (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)
      ∧ -((1 / 200) * Work.Coercivity.EDth α f + 32000000 * α * Work.Coercivity.Ef f)
        ≤ Work.Coercivity.wip (Work.Coercivity.thetaW α)
            (Work.Coercivity.T2 α f) (Work.Spaces.Dth f) := by
  obtain ⟨hsq, hm, _hb⟩ := hf
  set P : MeasureTheory.Measure (ℝ × ℝ) :=
    (MeasureTheory.volume.restrict Work.Spaces.Iz).prod
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) with hP
  have hvol : MeasureTheory.volume.restrict (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) = P := by
    rw [hP, MeasureTheory.Measure.prod_restrict, ← MeasureTheory.Measure.volume_eq_prod]
  have hquad : ∀ᵐ p ∂P, p.1 ∈ Work.Spaces.Iz ∧ p.2 ∈ Work.Spaces.Iθ := by
    rw [hP]; exact Work.Coercivity.ae_prod_quadrant
  set g₁ : ℝ × ℝ → ℝ := fun p => Work.Coercivity.T2 α f p.1 p.2 * Work.Spaces.w p.1
      * (Real.sin (2 * p.2)) ^ (-(Work.Spaces.gam α / 2)) with hg₁
  set g₂ : ℝ × ℝ → ℝ := fun p => Work.Spaces.Dth f p.1 p.2 * Work.Spaces.w p.1
      * (Real.sin (2 * p.2)) ^ (-(Work.Spaces.gam α / 2)) with hg₂
  set Az : ℝ → ℝ := fun z => (2 * z / (Work.Spaces.c α * (1 + z) ^ 2))
      * Work.Coercivity.L12f f z with hAz
  set arad : ℝ → ℝ := fun z => Az z ^ 2 * Work.Spaces.w z ^ 2 with harad
  set aθ : ℝ → ℝ := fun θ => (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
      * (Work.Coercivity.DthGam α 0 θ) ^ 2 with haθ
  -- ## the two energies are nonnegative
  have hEfnn : 0 ≤ Work.Coercivity.Ef f := by
    rw [Work.Coercivity.Ef, Work.Spaces.L2Sq]
    exact integral_nonneg fun z => integral_nonneg fun θ => sq_nonneg _
  have hEDnn : 0 ≤ Work.Coercivity.EDth α f := by
    rw [Work.Coercivity.EDth, Work.Spaces.L2Sq]
    exact integral_nonneg fun z => integral_nonneg fun θ => sq_nonneg _
  -- ## the `θ`-factor: integrability and `∫ aθ ≤ 100α`
  have haθ_int : MeasureTheory.Integrable aθ (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
    have hmed : MeasureTheory.Integrable (fun θ : ℝ => 4 * α ^ 2
        * ((Work.Spaces.Gam α θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))))
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
      ((Work.Coercivity.Gam_sq_sin_neg_gam α hα hα1).1.const_mul (4 * α ^ 2)).congr
        (Filter.Eventually.of_forall (fun θ => by ring))
    refine Integrable.mono' hmed ?_ ?_
    · rw [haθ]
      exact (((Real.measurable_sin.comp
        (measurable_const.mul measurable_id)).pow_const _).mul
          ((Work.Coercivity.measurable_DthGam α).pow_const (2 : ℕ))).aestronglyMeasurable
    · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ hθ
      have hs0 : 0 ≤ Real.sin (2 * θ) := Real.sin_nonneg_of_mem_Icc
        ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩
      have hsγ : 0 ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) := Real.rpow_nonneg hs0 _
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hsγ (sq_nonneg _))]
      have hD := Work.Coercivity.DthGam_sq_le_GamSq α hΓ2 θ hθ
      calc (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) * (Work.Coercivity.DthGam α 0 θ) ^ 2
          ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
              * (4 * α ^ 2 * (Work.Spaces.Gam α θ) ^ 2) := mul_le_mul_of_nonneg_left hD hsγ
        _ = 4 * α ^ 2 * ((Work.Spaces.Gam α θ) ^ 2
              * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) := by ring
  have haθ_val : ∫ θ in Work.Spaces.Iθ, aθ θ ≤ 100 * α := by
    rw [haθ]
    exact Work.Coercivity.gamDth_l2_bound α hα hα1 hΓ2
  -- ## the `z`-factor: integrability and `∫ arad ≤ 6400 Ef`
  have hbase : MeasureTheory.Integrable
      (fun z : ℝ => Work.Coercivity.L12f f z ^ 2 / z ^ 2)
      (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
    have h := hfH.intA 1 (by norm_num)
    have h1 : MeasureTheory.Integrable (fun z : ℝ => Work.Coercivity.L12f f z ^ 2 / z ^ 2)
        (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) := by
      refine h.congr (Filter.Eventually.of_forall fun z => ?_)
      show Work.Coercivity.L12f f z ^ 2 / z ^ (2 * ((1 : ℕ) : ℝ))
          = Work.Coercivity.L12f f z ^ 2 / z ^ 2
      have hz : (z : ℝ) ^ (2 * ((1 : ℕ) : ℝ)) = z ^ (2 : ℕ) := by
        rw [show (2 * ((1 : ℕ) : ℝ)) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
      rw [hz]
    rw [Work.Spaces.Iz, ← MeasureTheory.Measure.restrict_congr_set
      (MeasureTheory.Ioi_ae_eq_Ici (a := (0 : ℝ)))]
    exact h1
  have harad_pt : arad =ᵐ[MeasureTheory.volume.restrict Work.Spaces.Iz]
      (fun z : ℝ => (4 / Work.Spaces.c α ^ 2) * (Work.Coercivity.L12f f z ^ 2 / z ^ 2)) := by
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ici] with z hz
    show ((2 * z / (Work.Spaces.c α * (1 + z) ^ 2)) * Work.Coercivity.L12f f z) ^ 2
          * Work.Spaces.w z ^ 2
        = (4 / Work.Spaces.c α ^ 2) * (Work.Coercivity.L12f f z ^ 2 / z ^ 2)
    rcases eq_or_ne z 0 with hz0 | hz0
    · subst hz0
      rw [Work.Coercivity.w_eq]
      norm_num
    · have hc : Work.Spaces.c α ≠ 0 := Work.Coercivity.c_ne_zero hα hα1
      have hz1 : (1 : ℝ) + z ≠ 0 := by linarith [Set.mem_Ici.mp hz]
      rw [Work.Coercivity.w_eq]
      field_simp
      ring
  have harad_int : MeasureTheory.Integrable arad (MeasureTheory.volume.restrict Work.Spaces.Iz) :=
    ((hbase.const_mul (4 / Work.Spaces.c α ^ 2))).congr harad_pt.symm
  have harad_val : ∫ z in Work.Spaces.Iz, arad z ≤ 6400 * Work.Coercivity.Ef f := by
    have hEL := EL12z_le_Q α hα hsq hm hfH
    have hELnn : 0 ≤ Work.Coercivity.EL12z f := by
      rw [Work.Coercivity.EL12z, Work.Coercivity.L2Sqz]
      exact integral_nonneg fun z => sq_nonneg _
    have hc2 : (4 : ℝ) / Work.Spaces.c α ^ 2 ≤ 400 := by
      have hc := (Work.Spaces.c_bounds α hα hα1).1
      have hcp : 0 < Work.Spaces.c α := Work.Coercivity.c_pos hα hα1
      rw [div_le_iff₀ (by positivity)]
      nlinarith [hc, hcp]
    rw [MeasureTheory.integral_congr_ae harad_pt, MeasureTheory.integral_const_mul]
    rw [show (∫ z in Work.Spaces.Iz, Work.Coercivity.L12f f z ^ 2 / z ^ 2)
        = Work.Coercivity.EL12z f from by
      rw [Work.Coercivity.EL12z, Work.Coercivity.L2Sqz]
      refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
      show Work.Coercivity.L12f f z ^ 2 / z ^ 2 = (Work.Coercivity.L12f f z / z) ^ 2
      rw [div_pow]]
    calc (4 / Work.Spaces.c α ^ 2) * Work.Coercivity.EL12z f
        ≤ 400 * Work.Coercivity.EL12z f := mul_le_mul_of_nonneg_right hc2 hELnn
      _ ≤ 400 * (16 * Work.Coercivity.Ef f) := by linarith
      _ = 6400 * Work.Coercivity.Ef f := by ring
  -- ## the pointwise identifications of the two `L²`-blocks
  have hg₁_pt : (fun p => g₁ p ^ 2) =ᵐ[P] fun p => arad p.1 * aθ p.2 := by
    filter_upwards [hquad] with p hp
    obtain ⟨hz, hθ⟩ := hp
    have hs := Work.FTS.CoercivityFix.Coer1.sin_half_sq (Work.Spaces.gam α) p.2 hθ
    simp only [hg₁, harad, haθ, hAz]
    rw [show Work.Coercivity.T2 α f p.1 p.2 = -(Work.Coercivity.DthGam α p.1 p.2)
        * (2 * p.1 / (Work.Spaces.c α * (1 + p.1) ^ 2))
          * Work.Coercivity.L12f f p.1 from rfl,
      show Work.Coercivity.DthGam α p.1 p.2 = Work.Coercivity.DthGam α 0 p.2 from by
        rw [Work.Coercivity.DthGam_eq, Work.Coercivity.DthGam_eq]]
    rw [mul_pow, mul_pow, mul_pow, hs]
    ring
  have hg₂_pt : (fun p => g₂ p ^ 2) =ᵐ[P] fun p => Work.Spaces.Dth f p.1 p.2 ^ 2
      * (Work.Spaces.w p.1 ^ 2 * (Real.sin (2 * p.2)) ^ (-(Work.Spaces.gam α))) := by
    filter_upwards [hquad] with p hp
    obtain ⟨hz, hθ⟩ := hp
    have hs := Work.FTS.CoercivityFix.Coer1.sin_half_sq (Work.Spaces.gam α) p.2 hθ
    simp only [hg₂]
    rw [mul_pow, mul_pow, hs]
    ring
  have hg₁g₂_pt : (fun p => g₁ p * g₂ p) =ᵐ[P] fun p => Work.Coercivity.T2 α f p.1 p.2
      * Work.Spaces.Dth f p.1 p.2 * Work.Coercivity.thetaW α p.1 p.2 := by
    filter_upwards [hquad] with p hp
    obtain ⟨hz, hθ⟩ := hp
    have hs := Work.FTS.CoercivityFix.Coer1.sin_half_sq (Work.Spaces.gam α) p.2 hθ
    simp only [hg₁, hg₂, Work.Coercivity.thetaW]
    rw [← hs]
    ring
  -- ## integrability of the three blocks
  have hDth2 : MeasureTheory.Integrable (fun p : ℝ × ℝ => Work.Spaces.Dth f p.1 p.2 ^ 2
      * (Work.Spaces.w p.1 ^ 2 * (Real.sin (2 * p.2)) ^ (-(Work.Spaces.gam α)))) P := by
    have h := Work.FTS.CoercivityFix.Coer1.sq_MixedGam α hα hsq hm 1 0 (by norm_num) (by norm_num)
    have h1 : MeasureTheory.Integrable (fun p : ℝ × ℝ => Work.Spaces.mixed 0 1 f p.1 p.2 ^ 2
        * Work.FTS.CoercivityFix.Coer1.Rho (Work.Spaces.gam α) p.1 p.2) P := by
      rw [hP]; exact Work.Coercivity.integrableOn_prod h
    refine h1.congr ?_
    filter_upwards with p
    simp only [Work.Spaces.mixed_zero_left, Work.Spaces.DthIter_succ, Work.Spaces.DthIter_zero,
      Work.FTS.CoercivityFix.Coer1.Rho, Work.FTS.CoercivityFix.Coer1.sig]
    try ring
  have hg₂sq : MeasureTheory.Integrable (fun p => g₂ p ^ 2) P := hDth2.congr hg₂_pt.symm
  have hg₁rad : MeasureTheory.Integrable (fun p : ℝ × ℝ => arad p.1 * aθ p.2) P :=
    harad_int.mul_prod haθ_int
  have hg₁sq : MeasureTheory.Integrable (fun p => g₁ p ^ 2) P := hg₁rad.congr hg₁_pt.symm
  -- ## a.e. strong measurability
  have hL12aem : AEMeasurable (fun z : ℝ => Work.Coercivity.L12f f z)
      (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
    have h1 : AEStronglyMeasurable (fun z : ℝ => Work.Coercivity.L12f f z)
        (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) :=
      (Work.Coercivity.L12f_continuousOn f hfH).aestronglyMeasurable measurableSet_Ioi
    have h2 : MeasureTheory.volume.restrict Work.Spaces.Iz
        = MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ)) := by
      rw [Work.Spaces.Iz]
      exact (Measure.restrict_congr_set (MeasureTheory.Ioi_ae_eq_Ici (a := (0 : ℝ)))).symm
    rw [h2]; exact h1.aemeasurable
  have hsin_aesm : AEStronglyMeasurable (fun p : ℝ × ℝ =>
      (Real.sin (2 * p.2)) ^ (-(Work.Spaces.gam α / 2))) P :=
    ((Real.measurable_sin.comp (measurable_const.mul measurable_snd)).pow_const _)
      |>.aestronglyMeasurable
  have hg₂_aesm : AEStronglyMeasurable g₂ P := by
    rw [hg₂, hP]
    exact (aesm_dth_mul_w_Q hsq).mul hsin_aesm
  have hg₁_aesm : AEStronglyMeasurable g₁ P := by
    have hT2 : AEStronglyMeasurable (fun p : ℝ × ℝ => Work.Coercivity.T2 α f p.1 p.2) P := by
      have hfun : (fun p : ℝ × ℝ => Work.Coercivity.T2 α f p.1 p.2) = fun p =>
          -(Work.Coercivity.DthGam α p.1 p.2)
            * (2 * p.1 / (Work.Spaces.c α * (1 + p.1) ^ 2))
            * Work.Coercivity.L12f f p.1 := rfl
      rw [hfun, hP]
      have hL : AEStronglyMeasurable (fun p : ℝ × ℝ => Work.Coercivity.L12f f p.1) P :=
        (AEMeasurable.comp_fst hL12aem).aestronglyMeasurable
      have hrat : AEStronglyMeasurable
          (fun p : ℝ × ℝ => 2 * p.1 / (Work.Spaces.c α * (1 + p.1) ^ 2)) P :=
        ((measurable_const.mul measurable_fst).div
          (measurable_const.mul ((measurable_const.add measurable_fst).pow_const 2)))
          |>.aestronglyMeasurable
      exact (((Work.Coercivity.measurable_DthGam_prod α).neg.aestronglyMeasurable).mul hrat).mul hL
    have hg₁a : AEStronglyMeasurable (fun p : ℝ × ℝ => Work.Spaces.w p.1) P :=
      ((Work.Coercivity.measurable_w).comp measurable_fst).aestronglyMeasurable
    rw [hg₁]
    exact (hT2.mul hg₁a).mul hsin_aesm
  -- ## Cauchy–Schwarz
  have hg₁g₂_int : MeasureTheory.Integrable (fun p => g₁ p * g₂ p) P :=
    ((MeasureTheory.memLp_two_iff_integrable_sq hg₁_aesm).mpr hg₁sq).integrable_mul
      ((MeasureTheory.memLp_two_iff_integrable_sq hg₂_aesm).mpr hg₂sq)
  have hCS := Work.Coercivity.sq_integral_mul_le P g₁ g₂ hg₁_aesm hg₂_aesm hg₁sq hg₂sq
  have hg₁nn : 0 ≤ ∫ p, g₁ p ^ 2 ∂P := integral_nonneg fun p => sq_nonneg _
  have hg₂_val : ∫ p, g₂ p ^ 2 ∂P = Work.Coercivity.EDth α f := by
    have hOn : MeasureTheory.IntegrableOn
        (Function.uncurry (fun z θ => Work.Spaces.Dth f z θ * Work.Spaces.Dth f z θ
          * (Work.Spaces.w z ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))))
        (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) := by
      rw [MeasureTheory.IntegrableOn, hvol]
      refine hDth2.congr ?_
      filter_upwards with p
      rcases p with ⟨z, θ⟩
      show Work.Spaces.Dth f z θ ^ 2
            * (Work.Spaces.w z ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))
          = Work.Spaces.Dth f z θ * Work.Spaces.Dth f z θ
            * (Work.Spaces.w z ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))
      ring
    rw [MeasureTheory.integral_congr_ae hg₂_pt, Work.Coercivity.EDth_eq_wip α f,
      Work.Coercivity.wip_eq_integral_prod (fun z θ => Work.Spaces.w z ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) (Work.Spaces.Dth f) (Work.Spaces.Dth f)
        hOn,
      ← hP]
    exact MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun p => by ring)
  -- ## the bound `∫ g₁² ≤ 640000 α Ef` (the two one-variable factors separate)
  have haθ_nn : 0 ≤ ∫ θ in Work.Spaces.Iθ, aθ θ := by
    refine integral_nonneg_of_ae ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ hθ
    rw [haθ]
    exact mul_nonneg (Real.rpow_nonneg (Real.sin_nonneg_of_mem_Icc
      ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩) _) (sq_nonneg _)
  have hg₁_val : ∫ p, g₁ p ^ 2 ∂P ≤ 640000 * α * Work.Coercivity.Ef f := by
    rw [MeasureTheory.integral_congr_ae hg₁_pt,
      Work.Coercivity.integral_prod_sep arad aθ harad_int haθ_int]
    calc (∫ z in Work.Spaces.Iz, arad z) * (∫ θ in Work.Spaces.Iθ, aθ θ)
        ≤ (6400 * Work.Coercivity.Ef f) * (100 * α) :=
          mul_le_mul harad_val haθ_val haθ_nn (mul_nonneg (by norm_num) hEfnn)
      _ = 640000 * α * Work.Coercivity.Ef f := by ring
  -- ## integrability of the pairing (the pointwise identity above)
  have hOn : MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => Work.Coercivity.T2 α f z θ * Work.Spaces.Dth f z θ
        * Work.Coercivity.thetaW α z θ)) (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) := by
    rw [MeasureTheory.IntegrableOn, hvol]
    refine hg₁g₂_int.congr ?_
    filter_upwards [hg₁g₂_pt] with p hp
    rcases p with ⟨z, θ⟩
    show g₁ (z, θ) * g₂ (z, θ)
      = Work.Coercivity.T2 α f z θ * Work.Spaces.Dth f z θ * Work.Coercivity.thetaW α z θ
    exact hp
  -- ## the final bound on the pairing
  have hkey : |Work.Coercivity.wip (Work.Coercivity.thetaW α)
      (Work.Coercivity.T2 α f) (Work.Spaces.Dth f)|
      ≤ 800 * Real.sqrt α * Real.sqrt (Work.Coercivity.Ef f)
        * Real.sqrt (Work.Coercivity.EDth α f) := by
    have hwip : Work.Coercivity.wip (Work.Coercivity.thetaW α)
        (Work.Coercivity.T2 α f) (Work.Spaces.Dth f) = ∫ p, g₁ p * g₂ p ∂P := by
      rw [Work.Coercivity.wip_eq_integral_prod (Work.Coercivity.thetaW α)
        (Work.Coercivity.T2 α f) (Work.Spaces.Dth f) hOn]
      exact MeasureTheory.integral_congr_ae
        (hg₁g₂_pt.mono fun p hp => hp.symm)
    rw [hwip]
    have hsq : (∫ p, g₁ p * g₂ p ∂P) ^ 2
        ≤ (800 * Real.sqrt α * Real.sqrt (Work.Coercivity.Ef f)
            * Real.sqrt (Work.Coercivity.EDth α f)) ^ 2 := by
      have hb : (∫ p, g₁ p ^ 2 ∂P) * (∫ p, g₂ p ^ 2 ∂P)
          ≤ (640000 * α * Work.Coercivity.Ef f) * Work.Coercivity.EDth α f := by
        rw [hg₂_val]
        exact mul_le_mul_of_nonneg_right hg₁_val hEDnn
      have h2 : (800 * Real.sqrt α * Real.sqrt (Work.Coercivity.Ef f)
            * Real.sqrt (Work.Coercivity.EDth α f)) ^ 2
          = (640000 * α * Work.Coercivity.Ef f) * Work.Coercivity.EDth α f := by
        rw [mul_pow, mul_pow, mul_pow, Real.sq_sqrt hα.le, Real.sq_sqrt hEfnn,
          Real.sq_sqrt hEDnn]
        norm_num
      rw [h2]
      exact hCS.trans hb
    calc |∫ p, g₁ p * g₂ p ∂P| = Real.sqrt ((∫ p, g₁ p * g₂ p ∂P) ^ 2) :=
          (Real.sqrt_sq_eq_abs _).symm
      _ ≤ Real.sqrt ((800 * Real.sqrt α * Real.sqrt (Work.Coercivity.Ef f)
            * Real.sqrt (Work.Coercivity.EDth α f)) ^ 2) := Real.sqrt_le_sqrt hsq
      _ = 800 * Real.sqrt α * Real.sqrt (Work.Coercivity.Ef f)
            * Real.sqrt (Work.Coercivity.EDth α f) := Real.sqrt_sq (by positivity)
  -- ## the numerical conclusion
  have hyoung : 800 * Real.sqrt α * Real.sqrt (Work.Coercivity.Ef f)
      * Real.sqrt (Work.Coercivity.EDth α f)
      ≤ (1 / 200) * Work.Coercivity.EDth α f + 32000000 * α * Work.Coercivity.Ef f := by
    have h1 : (Real.sqrt α * Real.sqrt (Work.Coercivity.Ef f)) ^ 2
        = α * Work.Coercivity.Ef f := by
      rw [mul_pow, Real.sq_sqrt hα.le, Real.sq_sqrt hEfnn]
    have h2 : (Real.sqrt (Work.Coercivity.EDth α f)) ^ 2 = Work.Coercivity.EDth α f :=
      Real.sq_sqrt hEDnn
    nlinarith [sq_nonneg (Real.sqrt (Work.Coercivity.EDth α f)
      - 80000 * (Real.sqrt α * Real.sqrt (Work.Coercivity.Ef f))), h1, h2]
  refine ⟨hOn, ?_⟩
  linarith [neg_abs_le (Work.Coercivity.wip (Work.Coercivity.thetaW α)
    (Work.Coercivity.T2 α f) (Work.Spaces.Dth f)), hkey, hyoung]

theorem slotGam_LGammaT (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1 / 10 ^ 14) {f : ℝ → ℝ → ℝ}
    (hf : Work.FTS.Nonlin.CoerAdm α f) (hHH : Work.Coercivity.HardyHyp f)
    (hG2 : Work.Coercivity.GammaPointwiseBnd α) :
    (17 / 40 - 1 / 100) * Work.Coercivity.EDth α f - (1 / 10 ^ 6) * Work.Coercivity.Ef f
      ≤ Work.Coercivity.wip (fun z θ => Work.Spaces.w z ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))
          (Work.Spaces.Dth (Work.Coercivity.LGammaT α f)) (Work.Spaces.Dth f) := by
  have hα1' : α ≤ 1 := by linarith
  have hα9 : α ≤ 1 / 10 ^ 9 := by linarith
  have hf2 : Work.FTS.Nonlin.RegQ α 2 f :=
    Work.FTS.GalerkinFix.RegQ.regQ_mono hf.reg (by norm_num)
  exact slotGam_LGammaT_core α hα hα1 hf hHH hG2
    (wip_T2_ge_Q_crude α hα hα1' hf2 hHH hG2)
    (wip_T4_ge_Q α hα hα9 hf2 hG2)
    (intDth_Lhat_gam α hα hα1' hf2)

end Work.FTS.CoercivityFix.Coer1T
