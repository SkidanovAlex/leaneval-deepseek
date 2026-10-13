/-
Copyright: work module for the Elgindi finite-time singularity project.

# `RXT0.QlimTauLipW` — the fake-time Lipschitz bound of the angular moments `Qlim · k`, `k ≤ 2`

For a family `g` satisfying the approximation clause `LimApprox (pExp α) C₀ Φs E g`, every
horizon `[0,S]`, every `k ≤ 2` and every `z > 0`,

  `|Qlim α g τ k z − Qlim α g τ' k z| ≤ C · SW z · |τ − τ'|`,

where `Qlim α g τ k z = ∫_θ K(θ)·(D_z^k F_*(z,θ) + D_z^k (slice g τ)(z,θ)) dθ` is the `k`-th
angular moment of the limit profile `F(τ) = F_* + g(τ)` (`K(θ) = 3 sinθ cos²θ`,
`SW z = z^{3/2}/(1+z)²`).

**Route.**  `LimApprox` supplies approximants `gn n` which are class-`C` on the horizon,
uniformly bounded in `ℋ⁴`, `ℋ⁴`-Lipschitz in the fake time, and whose jets converge on the
quadrant.  The two standing bounds `Horizon.app_slot_bound` / `Horizon.ftau_slot_bound` are
exactly the hypotheses of `FKJets.Qapp_tendsto` (dominated convergence in `θ`), so
`Qapp α gn τ n k z → Qlim α g τ k z` along `n`.  The per-`n` increment `Qapp τ − Qapp τ'` is
an angular integral of `D_z^k (Ftau τ) − D_z^k (Ftau τ') = D_z^k (slice τ) − D_z^k (slice τ')`
(the `F_*`-part cancels — `FtauSlot.DzIter_Fstar_add`), which the weighted `τ`-modulus
`app_diff_w` of the approximants bounds by `Cw · SW z · |τ − τ'|`; `KweightIntegralSub` turns
that into the bound on the angular integrals, and `le_of_tendsto` passes it to the limit.

Everything here is `sorry`-free and rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.FinalV2.Defs
import Submission.Work.FTS_RegExport.RXT.Sys.L12FKaux.Horizon
import Submission.Work.FTS_RegExport.RXT.Sys.L12FKaux.FKJets
import Submission.Work.FTS_RegExport.RXT.Sys.L12FKaux.Standing
import Submission.Work.FTS_RegExport.RXT.Sys.L12FKaux.app_diff_w
import Submission.Work.FTS_RegExport.RXT.Sys.L12FKaux.KweightIntegralSub
import Submission.Work.FTS_RegExport.RXT.Sys.L12FKaux.FKDeriv
import Submission.Work.FTS_RegExport.RXT.Sys.L12FKaux.FtauSlot
import Submission.Work.FTS.StrongEps.HkMem_of_tendsto
import Submission.Work.Spaces.aesm_slice_of_continuousOn_Qd

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS_RegExport.RXT0

open Work.FTS_RegExport.RXT.Sys.L12FKaux
open Work.FTS.Galerkin (Fn Fam slice)

set_option autoImplicit false
set_option maxHeartbeats 800000

/-! ## §1 Two elementary inputs of the limit passage -/

/-- `θ ↦ K(θ)` is continuous on the open quadrant. -/
private theorem continuousOn_K_snd :
    ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.K p.2) Work.FTS.EllipticEst.Q0 := by
  have hfun : (fun p : ℝ × ℝ => Work.Spaces.K p.2)
      = fun p : ℝ × ℝ => 3 * Real.sin p.2 * Real.cos p.2 ^ 2 := by
    funext p; rw [Work.Spaces.K]
  rw [hfun]
  exact ((continuous_const.mul (Real.continuous_sin.comp continuous_snd)).mul
    ((Real.continuous_cos.comp continuous_snd).pow 2)).continuousOn

/-- **`θ`-integrability of the angular slices of a profile `F(τ) = F_* + slice (gn n) τ`**,
from an interior `L^∞` bound and open-quadrant smoothness. -/
private theorem integrable_K_DzIter_Ftau {α : ℝ} {gn : ℕ → Fam} {σ CB : ℝ} {n : ℕ}
    (hCB : 0 ≤ CB)
    (hCD : ContDiffOn ℝ 4 (Function.uncurry (Work.Construction.Ftau
      (Work.FTS.Regularity.pExp α) (gn n) σ)) Work.FTS.EllipticEst.Q0)
    (hsl : ∀ (j : ℕ), j ≤ 3 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      |Work.Spaces.DzIter j (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
        (gn n) σ) z θ| ≤ CB)
    {z : ℝ} (hz : 0 < z) (j : ℕ) (hj : j ≤ 3) :
    Integrable (fun θ : ℝ => Work.Spaces.K θ * Work.Spaces.DzIter j
      (Work.Construction.Ftau (Work.FTS.Regularity.pExp α) (gn n) σ) z θ)
      (volume.restrict Work.Spaces.Iθ) := by
  have hj4 : j ≤ 4 := le_trans hj (by norm_num)
  have hD : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.DzIter j
      (Work.Construction.Ftau (Work.FTS.Regularity.pExp α) (gn n) σ) p.1 p.2)
      Work.FTS.EllipticEst.Q0 :=
    Work.FTS.StrongEps.continuousOn_DzIter_of_contDiffOn (k := 4) (i := j) hCD hj4
  refine Integrable.mono' (integrable_const (3 * CB)) ?_ ?_
  · exact Work.Spaces.aesm_slice_of_continuousOn_Qd
      (fun p : ℝ × ℝ => Work.Spaces.K p.2 * Work.Spaces.DzIter j
        (Work.Construction.Ftau (Work.FTS.Regularity.pExp α) (gn n) σ) p.1 p.2)
      (continuousOn_K_snd.mul hD) hz
  · rw [Work.FTS_RegExport.RXT.Slots.restrict_Iθ_eq_restrict_Ioo]
    refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo (fun θ hθ => ?_)
    have hb := hsl j hj z θ hz hθ.1 hθ.2
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul (abs_K_le_three θ) hb (abs_nonneg _) (by norm_num)

/-- **The weighted `τ`-increment of a single `D_z^k`-slot of the approximants.**  The
`F_*`-part cancels (`FtauSlot.DzIter_Fstar_add`), leaving the `k`-th radial slot of the
difference of the two slices, which the standing weighted modulus controls. -/
private theorem diff_DzIter_Ftau_le {α : ℝ} (hα : 0 < α) (hα13 : α ≤ 1 / 3)
    {gn : ℕ → Fam} {τ τ' CwD : ℝ} {n : ℕ}
    (h4τ : ContDiffOn ℝ 4 (Function.uncurry (slice (gn n) τ)) Work.FTS.EllipticEst.Q0)
    (h4τ' : ContDiffOn ℝ 4 (Function.uncurry (slice (gn n) τ')) Work.FTS.EllipticEst.Q0)
    (hCwD : ∀ (b a : ℕ), a + b ≤ 2 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      |Work.Spaces.mixed b a (slice (gn n) τ) z θ
        - Work.Spaces.mixed b a (slice (gn n) τ') z θ| ≤ CwD * SW z * |τ - τ'|)
    {k : ℕ} (hk : k ≤ 2) {z θ : ℝ} (hz : 0 < z) (h0 : 0 < θ) (h1 : θ < Real.pi / 2) :
    |Work.Spaces.DzIter k (Work.Construction.Ftau (Work.FTS.Regularity.pExp α) (gn n) τ) z θ
      - Work.Spaces.DzIter k (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
          (gn n) τ') z θ| ≤ CwD * SW z * |τ - τ'| := by
  have hβ : 0 < Work.FTS.Regularity.pExp α := Work.FTS.Regularity.pExp_pos hα
  have hβ1 : Work.FTS.Regularity.pExp α ≤ 1 := Work.FTS.Regularity.pExp_le_one hα13
  have hsplitτ : Work.Spaces.DzIter k
      (Work.Construction.Ftau (Work.FTS.Regularity.pExp α) (gn n) τ) z θ
      = Work.Spaces.DzIter k (Work.Construction.Fstar (Work.FTS.Regularity.pExp α)) z θ
        + Work.Spaces.DzIter k (slice (gn n) τ) z θ := by
    rw [show Work.Construction.Ftau (Work.FTS.Regularity.pExp α) (gn n) τ
        = fun z θ => Work.Construction.Fstar (Work.FTS.Regularity.pExp α) z θ
          + slice (gn n) τ z θ from rfl]
    exact DzIter_Fstar_add hβ hβ1 h4τ hk z θ hz h0 h1
  have hsplitτ' : Work.Spaces.DzIter k
      (Work.Construction.Ftau (Work.FTS.Regularity.pExp α) (gn n) τ') z θ
      = Work.Spaces.DzIter k (Work.Construction.Fstar (Work.FTS.Regularity.pExp α)) z θ
        + Work.Spaces.DzIter k (slice (gn n) τ') z θ := by
    rw [show Work.Construction.Ftau (Work.FTS.Regularity.pExp α) (gn n) τ'
        = fun z θ => Work.Construction.Fstar (Work.FTS.Regularity.pExp α) z θ
          + slice (gn n) τ' z θ from rfl]
    exact DzIter_Fstar_add hβ hβ1 h4τ' hk z θ hz h0 h1
  rw [hsplitτ, hsplitτ']
  have hrd : (Work.Spaces.DzIter k (Work.Construction.Fstar (Work.FTS.Regularity.pExp α)) z θ
        + Work.Spaces.DzIter k (slice (gn n) τ) z θ)
      - (Work.Spaces.DzIter k (Work.Construction.Fstar (Work.FTS.Regularity.pExp α)) z θ
        + Work.Spaces.DzIter k (slice (gn n) τ') z θ)
      = Work.Spaces.DzIter k (slice (gn n) τ) z θ
        - Work.Spaces.DzIter k (slice (gn n) τ') z θ := by ring
  rw [hrd]
  have h := hCwD k 0 (by omega) z θ hz h0 h1
  simpa only [Work.Spaces.mixed_zero_right] using h

/-! ## §2 The target -/

theorem QlimTauLipW {α C₀ : ℝ} {Φs : Work.FTS.Galerkin.Fn}
    {E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn} {g : Work.FTS.Galerkin.Fam}
    (hα : 0 < α) (hα13 : α ≤ 1 / 3)
    (hA : Work.FTS.FinalV2.LimApprox (Work.FTS.Regularity.pExp α) C₀ Φs E g) :
    ∀ S > 0, ∃ C : ℝ, 0 ≤ C ∧ ∀ k : ℕ, k ≤ 2 →
      ∀ τ ∈ Set.Icc (0:ℝ) S, ∀ τ' ∈ Set.Icc (0:ℝ) S, ∀ z : ℝ, 0 < z →
        |Work.FTS_RegExport.RXT.Sys.L12FKaux.Qlim α g τ k z
          - Work.FTS_RegExport.RXT.Sys.L12FKaux.Qlim α g τ' k z|
          ≤ C * Work.FTS_RegExport.RXT.Sys.L12FKaux.SW z * |τ - τ'| := by
  intro S hS
  have hβ : 0 < Work.FTS.Regularity.pExp α := Work.FTS.Regularity.pExp_pos hα
  have hβ1 : Work.FTS.Regularity.pExp α ≤ 1 := Work.FTS.Regularity.pExp_le_one hα13
  obtain ⟨gn, B, L, hC, hLip, hjet0, -⟩ := hA S hS
  -- the standing weighted slot bounds of the approximants
  obtain ⟨Cw, hCw0, hCw⟩ := approx_slot_bound (α := α) (C₀ := C₀) (T := S) hα hα13 hS
    (fun n τ hτ => (hC n τ hτ).1) (fun n τ hτ => (hC n τ hτ).2.1)
  -- the order-`3` slot bounds of the profiles `F(τ) = F_* + slice (gn n) τ`
  obtain ⟨CB, hCB0, hCB⟩ := ftau_slot_bound (α := α) (B := B) (T := S) hα hα13
    (fun n τ hτ => (hC n τ hτ).1) (fun n τ hτ => (hC n τ hτ).2.2)
  -- the weighted `τ`-modulus of the approximants
  obtain ⟨CwD, hCwD0, hCwD⟩ := app_diff_w (α := Work.FTS.Regularity.pExp α) (T := S) (L := L)
    hβ hβ1 (fun n τ hτ => (hC n τ hτ).1)
    (fun n τ hτ τ' hτ' => hLip n τ hτ τ' hτ')
  refine ⟨3 * (Real.pi / 2) * CwD, mul_nonneg (mul_nonneg (by norm_num) (by positivity)) hCwD0,
    ?_⟩
  intro k hk τ hτ τ' hτ' z hz
  -- the standing inputs on the horizon
  have h4s : ∀ (σ : ℝ), σ ∈ Set.Icc (0 : ℝ) S → ∀ n : ℕ, ContDiffOn ℝ 4
      (Function.uncurry (slice (gn n) σ)) Work.FTS.EllipticEst.Q0 :=
    fun σ hσ n => (hC n σ hσ).1.reg.forall 4
  have h2s : ∀ (σ : ℝ), σ ∈ Set.Icc (0 : ℝ) S → ∀ n : ℕ, ContDiffOn ℝ 4
      (Function.uncurry (Work.Construction.Ftau (Work.FTS.Regularity.pExp α) (gn n) σ))
      Work.FTS.EllipticEst.Q0 :=
    fun σ hσ n => (Fstar_contDiffOn hβ hβ1 4).add ((hC n σ hσ).1.reg.forall 4)
  have hbds : ∀ (σ : ℝ), σ ∈ Set.Icc (0 : ℝ) S → ∀ (n j : ℕ), j ≤ 2 →
      ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      |Work.Spaces.DzIter j (slice (gn n) σ) z θ| ≤ Cw * SW z :=
    fun σ hσ n j hj z' θ hz' h0 h1 => hCw n σ hσ j hj z' θ hz' h0 h1
  have hsls : ∀ (σ : ℝ), σ ∈ Set.Icc (0 : ℝ) S → ∀ (n j : ℕ), j ≤ 3 →
      ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      |Work.Spaces.DzIter j (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
        (gn n) σ) z θ| ≤ CB :=
    fun σ hσ n j hj z' θ hz' h0 h1 => hCB σ hσ n j hj z' θ hz' h0 h1
  have hjets : ∀ (σ : ℝ), σ ∈ Set.Icc (0 : ℝ) S → ∀ (j : ℕ), j ≤ 2 →
      ∀ z θ : ℝ, (z, θ) ∈ Work.Construction.Qd →
      Filter.Tendsto (fun n => Work.Spaces.DzIter j (slice (gn n) σ) z θ) Filter.atTop
        (𝓝 (Work.Spaces.DzIter j (slice g σ) z θ)) := by
    intro σ hσ j hj z' θ hQd
    simpa only [Work.Spaces.mixed_zero_right] using hjet0 σ hσ j 0 (by omega) z' θ hQd
  -- the moments of the approximants converge to the moments of the limit
  have hlimτ : Filter.Tendsto (fun n => Qapp α gn τ n k z) Filter.atTop
      (𝓝 (Qlim α g τ k z)) :=
    Qapp_tendsto (α := α) hα hα13 hCw0 hCB0 (h4s τ hτ) (hbds τ hτ) (h2s τ hτ)
      (hsls τ hτ) (hjets τ hτ) hk hz
  have hlimτ' : Filter.Tendsto (fun n => Qapp α gn τ' n k z) Filter.atTop
      (𝓝 (Qlim α g τ' k z)) :=
    Qapp_tendsto (α := α) hα hα13 hCw0 hCB0 (h4s τ' hτ') (hbds τ' hτ') (h2s τ' hτ')
      (hsls τ' hτ') (hjets τ' hτ') hk hz
  -- the per-`n` bound on the increment of the moments
  have hper : ∀ n : ℕ, |Qapp α gn τ n k z - Qapp α gn τ' n k z|
      ≤ 3 * (Real.pi / 2) * (CwD * SW z * |τ - τ'|) := by
    intro n
    have hint := integrable_K_DzIter_Ftau (α := α) (gn := gn) (σ := τ) (CB := CB) (n := n)
      hCB0 (h2s τ hτ n) (fun j hj z' θ hz' h0 h1 => hsls τ hτ n j hj z' θ hz' h0 h1)
      hz k (by omega)
    have hint' := integrable_K_DzIter_Ftau (α := α) (gn := gn) (σ := τ') (CB := CB) (n := n)
      hCB0 (h2s τ' hτ' n) (fun j hj z' θ hz' h0 h1 => hsls τ' hτ' n j hj z' θ hz' h0 h1)
      hz k (by omega)
    have hae : ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ),
        |Work.Spaces.DzIter k (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
            (gn n) τ) z θ
          - Work.Spaces.DzIter k (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
            (gn n) τ') z θ| ≤ CwD * SW z * |τ - τ'| := by
      rw [Work.FTS_RegExport.RXT.Slots.restrict_Iθ_eq_restrict_Ioo]
      refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo (fun θ hθ => ?_)
      exact diff_DzIter_Ftau_le (α := α) (gn := gn) (τ := τ) (τ' := τ') (CwD := CwD) (n := n)
        hα hα13 ((hC n τ hτ).1.reg.forall 4) ((hC n τ' hτ').1.reg.forall 4)
        (fun b a hab z' θ hz' h0 h1 => hCwD n τ hτ τ' hτ' b a hab z' θ hz' h0 h1)
        hk hz hθ.1 hθ.2
    exact KweightIntegralSub (F := fun θ => Work.Spaces.DzIter k
        (Work.Construction.Ftau (Work.FTS.Regularity.pExp α) (gn n) τ) z θ)
      (F' := fun θ => Work.Spaces.DzIter k
        (Work.Construction.Ftau (Work.FTS.Regularity.pExp α) (gn n) τ') z θ)
      (C := CwD * SW z * |τ - τ'|)
      (mul_nonneg (mul_nonneg hCwD0 (SW_nonneg hz.le)) (abs_nonneg _)) hint hint' hae
  -- pass to the limit `n → ∞`
  have htend : Filter.Tendsto (fun n => |Qapp α gn τ n k z - Qapp α gn τ' n k z|) Filter.atTop
      (𝓝 |Qlim α g τ k z - Qlim α g τ' k z|) := (hlimτ.sub hlimτ').abs
  refine le_of_tendsto htend (Filter.Eventually.of_forall fun n => ?_)
  have h := hper n
  have hgoal : 3 * (Real.pi / 2) * (CwD * SW z * |τ - τ'|)
      = 3 * (Real.pi / 2) * CwD * SW z * |τ - τ'| := by ring
  rw [hgoal] at h
  exact h

end Work.FTS_RegExport.RXT0
