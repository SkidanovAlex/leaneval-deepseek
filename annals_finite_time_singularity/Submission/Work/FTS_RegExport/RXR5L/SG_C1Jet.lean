/-
# `Work.FTS_RegExport.RXR5L.SG_C1Jet` — the class-1 jet of the sanitised family

This file proves `SG_C1Jet`: from the dynamic package `DynOK'` and the `St1`-class data of the
sanitised right-Taylor family `SG α g = gS α (tauExt g)`, the family carries a `C1Jet` on the
horizon `[0,S]`, i.e. (`RegPkgGal.Der.Defs`)

* `Jet α S N (SG α g)`: a uniform sup bound on `z ≥ 0`, `θ ∈ Iθ`, `τ ∈ [0,S]` together with the
  *joint* `α`-Hölder modulus for the metric `|Δz| + |Δθ| + |Δτ|`;
* a genuine `z`-derivative of every slice at every `z > 0`, bounded by `N`.

## The decomposition

* the **value bound** is the interior `L^∞`–`ℋ⁴` trade-off `RXA2.lim_mixed_bounds_proved` at the
  slot `(b,a) = (0,0)` (it needs only the `LimApprox` half of `DynOK'`); the closed angular
  endpoints and `z = 0` are handled by the *exact* vanishing of `SG` there
  (`RegPkgMin.vanish`, resp. the definition of `gS`) — `SG_sup_le_aux`;
* the **`θ`-modulus** is literally `St1Class.hhθ`, which is a statement about
  `extG (SG α g)`; on the box `extG (SG α g) = SG α g` — `SG_theta_mod`;
* the **`τ`-modulus** is the weighted `τ`-Lipschitz bound `mixed_slice_tau_modulus` at
  `(b,a) = (0,0)` with the weight `z^{3/2}/(1+z)² ≤ 1`, upgraded from the exponent `1` to `α` —
  `SG_tau_mod_aux`;
* the **`z`-modulus** is the `RXR5.zhmod_of` interpolation between the `z`-Lipschitz bound
  (from the derivative bound) and the sup bound — `SG_zmod`;
* the **derivative bound** is `RXA2.lim_mixed_bounds_proved` at the slot `(1,0)`
  (`D_z g = z ∂_z g`) for `z ≥ 1` and the near-origin class datum `St1Class.quad` for `z ≤ 1` —
  `SG_zderiv_aux`;
* continuity at `z = 0` is the quadratic vanishing `St1Class.quad` — `SG_cont0`;
* the assembly is `RegPkgGal.R3d.jet_of_bounded_holder`.

The three `_aux`-named ingredients are stated (with the same statement, up to the name) in the
sibling modules `RXR5L.SG_sup_le`, `RXR5L.SG_tau_mod`, `RXR5L.SG_zderiv_clause`; they are proved
here as well so that this file is self-contained and does not depend on modules that may still be
under construction.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Order.CompletePartialOrder
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS_RegExport.RXR5.Basic
import Submission.Work.FTS_RegExport.RXR5.R5PiecesF
import Submission.Work.FTS_RegExport.RXA2.lim_mixed_bounds_proved
import Submission.Work.FTS_RegExport.RXR5.Pieces.mixed_slice_tau_modulus
import Submission.Work.FTS_RegExport.RXR5.zhmod_of
import Submission.Work.FTS.RegPkgGal.R3d.jet_g
import Submission.Work.FTS_RegExport.RXT.jc3_aux
import Submission.Work.FTS.RegPkgGal.St1Class
import Submission.Work.FTS.FinalV2.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open Set Filter MeasureTheory

namespace Work.FTS_RegExport.RXR5L

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## §1 Elementary helpers -/

/-- Monotonicity of `Jet` in its constant. -/
theorem Jet_mono {α S N N' : ℝ} {h : ℝ → ℝ → ℝ → ℝ} (H : Work.FTS.Regularity.Jet α S N h)
    (hN : N ≤ N') : Work.FTS.Regularity.Jet α S N' h := by
  refine ⟨le_trans H.1 hN, ?_, ?_⟩
  · intro z θ τ hz hθ hτ
    exact le_trans (H.2.1 z θ τ hz hθ hτ) hN
  · intro z z' θ θ' τ τ' hz hz' hθ hθ' hτ hτ'
    have h1 := H.2.2 z z' θ θ' τ τ' hz hz' hθ hθ' hτ hτ'
    have hd : (0 : ℝ) ≤ (|z - z'| + |θ - θ'| + |τ - τ'|) ^ α :=
      Real.rpow_nonneg (by positivity) α
    exact le_trans h1 (mul_le_mul_of_nonneg_right hN hd)

/-- On the box `z ≥ 0`, `θ ∈ Iθ`, `τ ∈ [0,S]` the extension `extG` of the sanitised family is the
family itself (they differ only in the `τ < 0` jet and for `z < 0`). -/
theorem SG_extG_eq {α S z θ τ : ℝ} {g : Work.FTS.Galerkin.Fam} (hz : 0 ≤ z)
    (hθ : θ ∈ Work.Spaces.Iθ) (hτ : τ ∈ Set.Icc 0 S) :
    Work.FTS.RegPkgGal.extG (Work.FTS_RegExport.RXR5.SG α g) z θ τ
      = Work.FTS_RegExport.RXR5.SG α g z θ τ := by
  rcases eq_or_lt_of_le hz with h | h
  · rw [← h, Work.FTS.RegPkgGal.extG_of_nonpos le_rfl,
      Work.FTS_RegExport.RXR5.SG_apply_of_nonpos le_rfl]
  · rw [Work.FTS.RegPkgGal.extG_of_pos h hτ.1,
      Work.FTS_RegExport.RXR5.SG_apply_of_pos h hθ.1 hθ.2]

/-- `C₀ ≥ 0`: the `ℋ⁴`-smallness clause of `DynOK` bounds the nonnegative `Xn` by
`C₀ (pExp α)²`. -/
theorem C0_nonneg {α C₀ : ℝ} {Φs : Work.FTS.Galerkin.Fn}
    {E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn} {g : Work.FTS.Galerkin.Fam}
    (hα : 0 < α) (hOK : Work.FTS.FinalV2.DynOK' (Work.FTS.Regularity.pExp α) C₀ Φs E g) :
    0 ≤ C₀ := by
  have h1 : Work.FTS.Nonlin.Xn (Work.FTS.Regularity.pExp α) (Work.FTS.Galerkin.slice g 0)
      ≤ C₀ * (Work.FTS.Regularity.pExp α) ^ 2 :=
    Work.FTS.Final.DynOK.Xn_le hOK.1 0 le_rfl
  have h2 : 0 ≤ Work.FTS.Nonlin.Xn (Work.FTS.Regularity.pExp α)
      (Work.FTS.Galerkin.slice g 0) := Real.sqrt_nonneg _
  have h3 : 0 < (Work.FTS.Regularity.pExp α) ^ 2 := by
    have := Work.FTS.Regularity.pExp_pos hα; positivity
  nlinarith [h1, h2, h3]

/-- `SG α g · θ ·` vanishes identically when `θ` is one of the two angular endpoints (for
`τ ≥ 0`), and also for `z ≤ 0`. -/
theorem SG_eq_zero_of_endpoint {α S z θ τ : ℝ} {g : Work.FTS.Galerkin.Fam}
    (hvanish : ∀ τ : ℝ, 0 ≤ τ → ∀ z : ℝ, 0 ≤ z → g z 0 τ = 0 ∧ g z (π / 2) τ = 0)
    (hτ : τ ∈ Set.Icc 0 S) (hz : 0 ≤ z) (hθ : θ = 0 ∨ θ = π / 2) :
    Work.FTS_RegExport.RXR5.SG α g z θ τ = 0 := by
  rcases eq_or_lt_of_le hz with h | h
  · rw [← h]; exact Work.FTS_RegExport.RXR5.SG_apply_of_nonpos le_rfl
  · rcases hθ with rfl | rfl
    · rw [Work.FTS_RegExport.RXR5.SG_apply_of_pos h le_rfl (by linarith [Real.pi_pos]),
        Work.FTS.FinalV2.tauExt_of_nonneg g hτ.1]
      exact (hvanish τ hτ.1 z h.le).1
    · rw [Work.FTS_RegExport.RXR5.SG_apply_of_pos h (by linarith [Real.pi_pos]) le_rfl,
        Work.FTS.FinalV2.tauExt_of_nonneg g hτ.1]
      exact (hvanish τ hτ.1 z h.le).2

/-- The weight `z^{3/2}/(1+z)²` is bounded by `1`. -/
theorem z_rpow_three_halves_div_sq_le_one {z : ℝ} (hz : 0 < z) :
    z ^ ((3 : ℝ) / 2) / (1 + z) ^ 2 ≤ 1 := by
  have h1 : 0 < (1 + z) ^ 2 := by positivity
  rw [div_le_iff₀ h1, one_mul]
  have hA : z ^ ((3 : ℝ) / 2) ≤ (1 + z) ^ ((3 : ℝ) / 2) :=
    Real.rpow_le_rpow hz.le (by linarith) (by norm_num)
  have hB : (1 + z) ^ ((3 : ℝ) / 2) ≤ (1 + z) ^ (2 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
  rw [Real.rpow_two] at hB
  linarith

/-- On a horizon `[0,S]` the Lipschitz modulus `L|τ - τ'|` upgrades to the `α`-modulus
`L · max S 1 · |τ - τ'|^α`. -/
theorem abs_sub_le_max_mul_rpow {S α τ τ' : ℝ} (hα0 : 0 < α) (hα1 : α ≤ 1)
    (hτ : τ ∈ Set.Icc 0 S) (hτ' : τ' ∈ Set.Icc 0 S) :
    |τ - τ'| ≤ max S 1 * |τ - τ'| ^ α := by
  have ht0 : 0 ≤ |τ - τ'| := abs_nonneg _
  have htS : |τ - τ'| ≤ S := by
    rw [abs_le]
    exact ⟨by linarith [hτ.1, hτ'.2], by linarith [hτ.2, hτ'.1]⟩
  have hmax1 : 1 ≤ max S 1 := le_max_right _ _
  have hle : |τ - τ'| ≤ max S 1 := le_trans htS (le_max_left _ _)
  rcases eq_or_lt_of_le ht0 with h | ht
  · rw [← h, Real.zero_rpow hα0.ne', mul_zero]
  · rcases lt_or_ge |τ - τ'| 1 with h1 | h1
    · have h3 : |τ - τ'| ^ (1 : ℝ) ≤ |τ - τ'| ^ α :=
        Real.rpow_le_rpow_of_exponent_ge ht h1.le hα1
      rw [Real.rpow_one] at h3
      calc |τ - τ'| ≤ |τ - τ'| ^ α := h3
        _ = 1 * |τ - τ'| ^ α := (one_mul _).symm
        _ ≤ max S 1 * |τ - τ'| ^ α :=
            mul_le_mul_of_nonneg_right hmax1 (Real.rpow_nonneg ht0 α)
    · have h2 : 1 ≤ |τ - τ'| ^ α := Real.one_le_rpow h1 hα0.le
      calc |τ - τ'| ≤ max S 1 := hle
        _ = max S 1 * 1 := (mul_one _).symm
        _ ≤ max S 1 * |τ - τ'| ^ α :=
            mul_le_mul_of_nonneg_left h2 (by linarith)

/-! ## §2 The `θ`-modulus and the continuity at `z = 0` -/

/-- The `θ`-modulus of `SG α g`: on the box it is `St1Class.hhθ`. -/
theorem SG_theta_mod {α C₀ : ℝ} {Φs : Work.FTS.Galerkin.Fn}
    {E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn} {g : Work.FTS.Galerkin.Fam}
    (hα : 0 < α) (hα13 : α ≤ 1 / 3)
    (hOK : Work.FTS.FinalV2.DynOK' (Work.FTS.Regularity.pExp α) C₀ Φs E g)
    {S : ℝ} (hS : 0 < S)
    (hSt1 : Work.FTS.RegPkgGal.St1Class α S (Work.FTS_RegExport.RXR5.SG α g)) :
    ∃ Lθ : ℝ, 0 ≤ Lθ ∧ ∀ τ ∈ Set.Icc 0 S, ∀ z : ℝ, 0 ≤ z →
      ∀ θ ∈ Work.Spaces.Iθ, ∀ θ' ∈ Work.Spaces.Iθ,
        |Work.FTS_RegExport.RXR5.SG α g z θ τ - Work.FTS_RegExport.RXR5.SG α g z θ' τ|
          ≤ Lθ * |θ - θ'| ^ α := by
  obtain ⟨Lθ, hLθ, hh⟩ := hSt1.hhθ
  refine ⟨Lθ, hLθ, ?_⟩
  intro τ hτ z hz θ hθ θ' hθ'
  rw [← SG_extG_eq hz hθ hτ, ← SG_extG_eq hz hθ' hτ]
  exact hh τ hτ z hz θ hθ θ' hθ'

/-- Continuity of the `z`-slices of `SG α g` at `z = 0`, from the quadratic vanishing of the
`St1`-class data at the origin. -/
theorem SG_cont0 {α C₀ : ℝ} {Φs : Work.FTS.Galerkin.Fn}
    {E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn} {g : Work.FTS.Galerkin.Fam}
    (hα : 0 < α) (hα13 : α ≤ 1 / 3)
    (hOK : Work.FTS.FinalV2.DynOK' (Work.FTS.Regularity.pExp α) C₀ Φs E g)
    {S : ℝ} (hS : 0 < S)
    (hSt1 : Work.FTS.RegPkgGal.St1Class α S (Work.FTS_RegExport.RXR5.SG α g)) :
    ∀ τ ∈ Set.Icc 0 S, ∀ θ ∈ Work.Spaces.Iθ,
      ContinuousAt (fun z' => Work.FTS_RegExport.RXR5.SG α g z' θ τ) 0 := by
  obtain ⟨K, Q, hK, hQ, hquad⟩ := hSt1.quad
  intro τ hτ θ hθ
  have hquad' : ∀ z' : ℝ, 0 ≤ z' → z' ≤ 2 →
      |Work.FTS_RegExport.RXR5.SG α g z' θ τ| ≤ K * z' ^ 2 := by
    intro z' hz' hz'2
    have h1 := (hquad τ hτ θ hθ).1 z' hz' hz'2
    rwa [SG_extG_eq hz' hθ hτ] at h1
  have h0 : Work.FTS_RegExport.RXR5.SG α g 0 θ τ = 0 :=
    Work.FTS_RegExport.RXR5.SG_apply_of_nonpos le_rfl
  have hnorm : Filter.Tendsto (fun z' => ‖Work.FTS_RegExport.RXR5.SG α g z' θ τ‖)
      (𝓝 0) (𝓝 0) := by
    refine squeeze_zero' (f := fun z' : ℝ => ‖Work.FTS_RegExport.RXR5.SG α g z' θ τ‖)
      (g := fun z' : ℝ => K * z' ^ 2) ?_ ?_ ?_
    · filter_upwards with z' using norm_nonneg _
    · filter_upwards [Iic_mem_nhds (show (0 : ℝ) < 2 by norm_num)] with z' hz'2
      rcases lt_or_ge z' 0 with h | h
      · rw [Work.FTS_RegExport.RXR5.SG_apply_of_nonpos h.le, norm_zero]
        exact mul_nonneg hK (sq_nonneg z')
      · rw [Real.norm_eq_abs]
        exact hquad' z' h hz'2
    · have hcont : ContinuousAt (fun z' : ℝ => K * z' ^ 2) 0 :=
        continuousAt_const.mul (continuousAt_id.pow 2)
      have hv : (fun z' : ℝ => K * z' ^ 2) 0 = 0 := by ring
      simpa only [hv] using hcont.tendsto
  have htend : Filter.Tendsto (fun z' => Work.FTS_RegExport.RXR5.SG α g z' θ τ) (𝓝 0) (𝓝 0) :=
    tendsto_zero_iff_norm_tendsto_zero.mpr hnorm
  show Filter.Tendsto (fun z' => Work.FTS_RegExport.RXR5.SG α g z' θ τ) (𝓝 0)
    (𝓝 (Work.FTS_RegExport.RXR5.SG α g 0 θ τ))
  rw [h0]
  exact htend

/-! ## §3 The sup bound -/

/-- The uniform sup bound of the sanitised family on the box: the `(b,a) = (0,0)` slot of the
interior `L^∞`–`ℋ⁴` trade-off, with the angular endpoints and `z = 0` from the exact vanishing. -/
theorem SG_sup_le_aux {α C₀ : ℝ} {Φs : Work.FTS.Galerkin.Fn}
    {E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn} {g : Work.FTS.Galerkin.Fam}
    (hα : 0 < α) (hα13 : α ≤ 1 / 3)
    (hOK : Work.FTS.FinalV2.DynOK' (Work.FTS.Regularity.pExp α) C₀ Φs E g)
    {S : ℝ} (hS : 0 < S) :
    ∀ τ ∈ Set.Icc 0 S, ∀ z : ℝ, 0 ≤ z → ∀ θ ∈ Work.Spaces.Iθ,
      |Work.FTS_RegExport.RXR5.SG α g z θ τ| ≤
        10 / Real.sqrt (Work.Spaces.gam (Work.FTS.Regularity.pExp α) - 1)
          * (C₀ * (Work.FTS.Regularity.pExp α) ^ 2) := by
  obtain ⟨Lτ, hLτ0, hb⟩ := Work.FTS_RegExport.RXA2.lim_mixed_bounds_proved
    (hα := Work.FTS.Regularity.pExp_pos hα) (hα1 := Work.FTS.Regularity.pExp_le_one hα13)
    (hA := hOK.2) S hS
  have hK0 : 0 ≤ 10 / Real.sqrt (Work.Spaces.gam (Work.FTS.Regularity.pExp α) - 1)
      * (C₀ * (Work.FTS.Regularity.pExp α) ^ 2) :=
    mul_nonneg (div_nonneg (by norm_num) (Real.sqrt_nonneg _))
      (mul_nonneg (C0_nonneg hα hOK) (sq_nonneg _))
  intro τ hτ z hz θ hθ
  have hvanish := hOK.1.1.vanish τ hτ.1
  rcases eq_or_lt_of_le hz with h | hz'
  · rw [← h, Work.FTS_RegExport.RXR5.SG_apply_of_nonpos le_rfl, abs_zero]
    exact hK0
  · rw [Work.FTS_RegExport.RXR5.SG_apply_of_pos hz' hθ.1 hθ.2,
      Work.FTS.FinalV2.tauExt_of_nonneg g hτ.1]
    by_cases hθ0 : θ = 0
    · rw [hθ0, (hvanish z hz).1, abs_zero]; exact hK0
    · by_cases hθ2 : θ = π / 2
      · rw [hθ2, (hvanish z hz).2, abs_zero]; exact hK0
      · have hθp : 0 < θ := lt_of_le_of_ne hθ.1 (Ne.symm hθ0)
        have hθl : θ < π / 2 := lt_of_le_of_ne hθ.2 hθ2
        simpa using (hb τ hτ τ hτ 0 0 (by norm_num) z θ hz' hθp hθl).1

/-! ## §4 The `τ`-modulus -/

/-- The `τ`-modulus of `SG α g`, from the weighted `τ`-Lipschitz bound of
`Pieces.mixed_slice_tau_modulus` at the slot `(0,0)`. -/
theorem SG_tau_mod_aux {α C₀ : ℝ} {Φs : Work.FTS.Galerkin.Fn}
    {E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn} {g : Work.FTS.Galerkin.Fam}
    (hα : 0 < α) (hα13 : α ≤ 1 / 3)
    (hOK : Work.FTS.FinalV2.DynOK' (Work.FTS.Regularity.pExp α) C₀ Φs E g)
    {S : ℝ} (hS : 0 < S) :
    ∃ Lt : ℝ, 0 ≤ Lt ∧ ∀ τ ∈ Set.Icc 0 S, ∀ τ' ∈ Set.Icc 0 S, ∀ z : ℝ, 0 ≤ z →
      ∀ θ ∈ Work.Spaces.Iθ,
        |Work.FTS_RegExport.RXR5.SG α g z θ τ - Work.FTS_RegExport.RXR5.SG α g z θ τ'|
          ≤ Lt * |τ - τ'| ^ α := by
  obtain ⟨L, hL, hb⟩ := Work.FTS_RegExport.RXR5.Pieces.mixed_slice_tau_modulus
    (hA := hOK.2) (hαG := Work.FTS.Regularity.pExp_pos hα)
    (hαG1 := Work.FTS.Regularity.pExp_le_one hα13) S hS
  have hmax1 : (1 : ℝ) ≤ max S 1 := le_max_right _ _
  refine ⟨L * max S 1, mul_nonneg hL (le_trans zero_le_one hmax1), ?_⟩
  intro τ hτ τ' hτ' z hz θ hθ
  have hRnn : 0 ≤ L * max S 1 * |τ - τ'| ^ α :=
    mul_nonneg (mul_nonneg hL (le_trans zero_le_one hmax1))
      (Real.rpow_nonneg (abs_nonneg _) α)
  have hvanish : ∀ τ : ℝ, 0 ≤ τ → ∀ z : ℝ, 0 ≤ z → g z 0 τ = 0 ∧ g z (π / 2) τ = 0 :=
    fun τ hτ z hz => hOK.1.1.vanish τ hτ z hz
  by_cases hθe : θ = 0 ∨ θ = π / 2
  · rw [SG_eq_zero_of_endpoint hvanish hτ hz hθe, SG_eq_zero_of_endpoint hvanish hτ' hz hθe,
      sub_self, abs_zero]
    exact hRnn
  · push Not at hθe
    obtain ⟨hθne0, hθne2⟩ := hθe
    have hθp : 0 < θ := lt_of_le_of_ne hθ.1 (Ne.symm hθne0)
    have hθl : θ < π / 2 := lt_of_le_of_ne hθ.2 hθne2
    rcases eq_or_lt_of_le hz with h | hz'
    · rw [← h, Work.FTS_RegExport.RXR5.SG_apply_of_nonpos (le_refl (0 : ℝ)),
        Work.FTS_RegExport.RXR5.SG_apply_of_nonpos (le_refl (0 : ℝ)), sub_self, abs_zero]
      exact hRnn
    · have hSG : ∀ τ ∈ Set.Icc 0 S,
          Work.FTS_RegExport.RXR5.SG α g z θ τ = Work.FTS.Galerkin.slice g τ z θ := by
        intro τ hτ
        rw [Work.FTS_RegExport.RXR5.SG_apply_of_pos hz' hθ.1 hθ.2,
          Work.FTS.FinalV2.tauExt_of_nonneg g hτ.1]
        rfl
      rw [hSG τ hτ, hSG τ' hτ']
      have hb' := hb τ hτ τ' hτ' 0 0 (by norm_num) z θ hz' hθp hθl
      have hw := z_rpow_three_halves_div_sq_le_one hz'
      have hkey := abs_sub_le_max_mul_rpow (S := S) hα (by linarith) hτ hτ'
      calc |Work.FTS.Galerkin.slice g τ z θ - Work.FTS.Galerkin.slice g τ' z θ|
          ≤ L * (z ^ ((3 : ℝ) / 2) / (1 + z) ^ 2) * |τ - τ'| := hb'
        _ ≤ L * 1 * |τ - τ'| := by
            refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
            exact mul_le_mul_of_nonneg_left hw hL
        _ = L * |τ - τ'| := by ring
        _ ≤ L * (max S 1 * |τ - τ'| ^ α) := mul_le_mul_of_nonneg_left hkey hL
        _ = L * max S 1 * |τ - τ'| ^ α := by ring

/-! ## §5 The bounded `z`-derivative -/

/-- Every slice of `SG α g` has a `z`-derivative at every `z > 0`, with a uniform bound:
for `z ≥ 1` the `(b,a) = (1,0)` slot of the interior trade-off, for `z ≤ 1` the near-origin class
datum `St1Class.quad`. -/
theorem SG_zderiv_aux {α C₀ : ℝ} {Φs : Work.FTS.Galerkin.Fn}
    {E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn} {g : Work.FTS.Galerkin.Fam}
    (hα : 0 < α) (hα13 : α ≤ 1 / 3)
    (hOK : Work.FTS.FinalV2.DynOK' (Work.FTS.Regularity.pExp α) C₀ Φs E g)
    {S : ℝ} (hS : 0 < S)
    (hSt1 : Work.FTS.RegPkgGal.St1Class α S (Work.FTS_RegExport.RXR5.SG α g)) :
    ∃ N : ℝ, 0 ≤ N ∧ ∀ τ ∈ Set.Icc 0 S, ∀ θ ∈ Work.Spaces.Iθ, ∀ z ∈ Set.Ioi (0 : ℝ),
      ∃ d : ℝ, HasDerivAt (fun z' => Work.FTS_RegExport.RXR5.SG α g z' θ τ) d z ∧
        |d| ≤ N := by
  obtain ⟨Lτ, hLτ0, hb⟩ := Work.FTS_RegExport.RXA2.lim_mixed_bounds_proved
    (hα := Work.FTS.Regularity.pExp_pos hα) (hα1 := Work.FTS.Regularity.pExp_le_one hα13)
    (hA := hOK.2) S hS
  obtain ⟨K, Q, hK, hQ, hquad⟩ := hSt1.quad
  set Cw : ℝ := 10 / Real.sqrt (Work.Spaces.gam (Work.FTS.Regularity.pExp α) - 1)
      * (C₀ * (Work.FTS.Regularity.pExp α) ^ 2) with hCwdef
  have hCw0 : 0 ≤ Cw := by
    rw [hCwdef]
    exact mul_nonneg (div_nonneg (by norm_num) (Real.sqrt_nonneg _))
      (mul_nonneg (C0_nonneg hα hOK) (sq_nonneg _))
  have hN0 : 0 ≤ max Cw Q := le_trans hCw0 (le_max_left _ _)
  refine ⟨max Cw Q, hN0, ?_⟩
  intro τ hτ θ hθ z hz
  have hvanish : ∀ τ : ℝ, 0 ≤ τ → ∀ z : ℝ, 0 ≤ z → g z 0 τ = 0 ∧ g z (π / 2) τ = 0 :=
    fun τ hτ z hz => hOK.1.1.vanish τ hτ z hz
  by_cases hθe : θ = 0 ∨ θ = π / 2
  · have hv : (fun z' : ℝ => Work.FTS_RegExport.RXR5.SG α g z' θ τ)
        =ᶠ[𝓝 z] (fun _ => (0 : ℝ)) := by
      filter_upwards [isOpen_Ioi.mem_nhds hz] with z' hz'
      exact SG_eq_zero_of_endpoint hvanish hτ hz'.le hθe
    exact ⟨0, (hasDerivAt_const z 0).congr_of_eventuallyEq hv, by rw [abs_zero]; exact hN0⟩
  · push Not at hθe
    obtain ⟨hθne0, hθne2⟩ := hθe
    have hθp : 0 < θ := lt_of_le_of_ne hθ.1 (Ne.symm hθne0)
    have hθl : θ < π / 2 := lt_of_le_of_ne hθ.2 hθne2
    have hmem : (z, θ) ∈ Work.FTS.EllipticEst.Q0 := by
      rw [Work.FTS.EllipticEst.mem_Q0]; exact ⟨hz, hθp, hθl⟩
    have h1 : ContDiffOn ℝ 1 (Function.uncurry (Work.FTS.Galerkin.slice g τ))
        Work.FTS.EllipticEst.Q0 := (hOK.1.1.c4 τ hτ.1).of_le (by norm_num)
    have hd : HasDerivAt (fun z' => Work.FTS.Galerkin.slice g τ z' θ)
        (Work.Spaces.pz (Work.FTS.Galerkin.slice g τ) z θ) z :=
      Work.FTS_RegExport.RXT.hasDerivAt_slice_fst_of_contDiffOn
        Work.FTS.EllipticEst.isOpen_Q0 h1 hmem
    have hcongr : (fun z' : ℝ => Work.FTS_RegExport.RXR5.SG α g z' θ τ)
        =ᶠ[𝓝 z] (fun z' => Work.FTS.Galerkin.slice g τ z' θ) := by
      filter_upwards [isOpen_Ioi.mem_nhds hz] with z' hz'
      rw [Work.FTS_RegExport.RXR5.SG_apply_of_pos hz' hθ.1 hθ.2,
        Work.FTS.FinalV2.tauExt_of_nonneg g hτ.1]
      rfl
    refine ⟨Work.Spaces.pz (Work.FTS.Galerkin.slice g τ) z θ,
      hd.congr_of_eventuallyEq hcongr, ?_⟩
    rcases lt_or_ge z 1 with hz1 | hz1
    · -- near the origin: the quadratic class datum
      have hpz : Work.Spaces.pz (Work.FTS.Galerkin.slice g τ) z θ
          = Work.Spaces.pz (Work.FTS.Regularity.gSlice
              (Work.FTS.RegPkgGal.extG (Work.FTS_RegExport.RXR5.SG α g)) τ) z θ := by
        show deriv (fun z' => Work.FTS.Galerkin.slice g τ z' θ) z
          = deriv (fun z' => Work.FTS.RegPkgGal.extG (Work.FTS_RegExport.RXR5.SG α g) z' θ τ) z
        refine Filter.EventuallyEq.deriv_eq ?_
        filter_upwards [isOpen_Ioi.mem_nhds hz] with z' hz'
        rw [SG_extG_eq hz'.le hθ hτ]
        rw [Work.FTS_RegExport.RXR5.SG_apply_of_pos hz' hθ.1 hθ.2,
          Work.FTS.FinalV2.tauExt_of_nonneg g hτ.1]
        rfl
      rw [hpz]
      calc |Work.Spaces.pz (Work.FTS.Regularity.gSlice
              (Work.FTS.RegPkgGal.extG (Work.FTS_RegExport.RXR5.SG α g)) τ) z θ|
          ≤ Q * z := (hquad τ hτ θ hθ).2 z hz.le (by linarith)
        _ ≤ Q := by nlinarith [hz, hQ]
        _ ≤ max Cw Q := le_max_right _ _
    · -- far from the origin: the `D_z g = z ∂_z g` slot
      have hmix := (hb τ hτ τ hτ 1 0 (by norm_num) z θ hz hθp hθl).1
      have hpzm : Work.Spaces.mixed 1 0 (Work.FTS.Galerkin.slice g τ) z θ
          = z * Work.Spaces.pz (Work.FTS.Galerkin.slice g τ) z θ := rfl
      have hzabs : |z| = z := abs_of_pos hz
      have heq : |Work.Spaces.pz (Work.FTS.Galerkin.slice g τ) z θ|
          = |Work.Spaces.mixed 1 0 (Work.FTS.Galerkin.slice g τ) z θ| / z := by
        rw [hpzm, abs_mul, hzabs]
        exact (eq_div_iff hz.ne').mpr (by ring)
      calc |Work.Spaces.pz (Work.FTS.Galerkin.slice g τ) z θ|
          = |Work.Spaces.mixed 1 0 (Work.FTS.Galerkin.slice g τ) z θ| / z := heq
        _ ≤ Cw / z := div_le_div_of_nonneg_right hmix hz.le
        _ ≤ max Cw Q := by
            rw [div_le_iff₀ hz]
            calc Cw = Cw * 1 := (mul_one _).symm
              _ ≤ max Cw Q * z :=
                  mul_le_mul (le_max_left _ _) hz1 zero_le_one hN0

/-! ## §6 The `z`-modulus -/

/-- The `z`-modulus of `SG α g`: the interpolation `RXR5.zhmod_of` between the `z`-Lipschitz
bound supplied by the derivative bound `M` and the sup bound `B`. -/
theorem SG_zmod {α : ℝ} {g : Work.FTS.Galerkin.Fam} (hα : 0 < α) (hα1 : α ≤ 1)
    {S M B : ℝ} (hM : 0 ≤ M) (hB : 0 ≤ B)
    (hderiv : ∀ τ ∈ Set.Icc 0 S, ∀ θ ∈ Work.Spaces.Iθ, ∀ z ∈ Set.Ioi (0 : ℝ),
      ∃ d : ℝ, HasDerivAt (fun z' => Work.FTS_RegExport.RXR5.SG α g z' θ τ) d z ∧ |d| ≤ M)
    (hcont0 : ∀ τ ∈ Set.Icc 0 S, ∀ θ ∈ Work.Spaces.Iθ,
      ContinuousAt (fun z' => Work.FTS_RegExport.RXR5.SG α g z' θ τ) 0)
    (hsup : ∀ τ ∈ Set.Icc 0 S, ∀ z θ : ℝ, 0 ≤ z → θ ∈ Work.Spaces.Iθ →
      |Work.FTS_RegExport.RXR5.SG α g z θ τ| ≤ B) :
    ∃ Lz : ℝ, 0 ≤ Lz ∧ ∀ τ ∈ Set.Icc 0 S, ∀ z z' : ℝ, 0 ≤ z → 0 ≤ z' →
      ∀ θ ∈ Work.Spaces.Iθ,
        |Work.FTS_RegExport.RXR5.SG α g z θ τ - Work.FTS_RegExport.RXR5.SG α g z' θ τ|
          ≤ Lz * |z - z'| ^ α := by
  have hmod := Work.FTS_RegExport.RXR5.zhmod_of (α := α) (S := S) (M := M) (B := B)
    (h := fun z θ τ => Work.FTS_RegExport.RXR5.SG α g z θ τ) hα hα1 hM hB
    (fun τ hτ θ hθ x hx => (hderiv τ hτ θ hθ x hx).choose_spec.1.differentiableAt)
    (fun τ hτ θ hθ x hx => by
      obtain ⟨d, hd, hbd⟩ := hderiv τ hτ θ hθ x hx
      rw [hd.deriv]; exact hbd)
    hcont0 (fun τ hτ θ hθ z hz => hsup τ hτ z θ hz hθ)
  exact ⟨max M (2 * B), le_trans hM (le_max_left _ _),
    fun τ hτ z z' hz hz' θ hθ => hmod τ hτ θ hθ z z' hz hz'⟩

/-! ## §7 The assembly -/

theorem SG_C1Jet {α C₀ : ℝ} {Φs : Work.FTS.Galerkin.Fn}
    {E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn} {g : Work.FTS.Galerkin.Fam}
    (hα : 0 < α) (hα13 : α ≤ 1 / 3)
    (hOK : Work.FTS.FinalV2.DynOK' (Work.FTS.Regularity.pExp α) C₀ Φs E g)
    {S : ℝ} (hS : 0 < S)
    (hSt1 : Work.FTS.RegPkgGal.St1Class α S
      (Work.FTS.FinalV2.gS α (Work.FTS.FinalV2.tauExt g))) :
    ∃ N₁ : ℝ, 0 ≤ N₁ ∧
      Work.FTS.RegPkgGal.C1Jet α S N₁ (Work.FTS_RegExport.RXR5.SG α g) := by
  have hα1 : α ≤ 1 := by linarith
  have hSt1' : Work.FTS.RegPkgGal.St1Class α S (Work.FTS_RegExport.RXR5.SG α g) := hSt1
  set Mval : ℝ := 10 / Real.sqrt (Work.Spaces.gam (Work.FTS.Regularity.pExp α) - 1)
      * (C₀ * (Work.FTS.Regularity.pExp α) ^ 2) with hMvaldef
  have hMval0 : 0 ≤ Mval := by
    rw [hMvaldef]
    exact mul_nonneg (div_nonneg (by norm_num) (Real.sqrt_nonneg _))
      (mul_nonneg (C0_nonneg hα hOK) (sq_nonneg _))
  have hsup : ∀ τ ∈ Set.Icc 0 S, ∀ z θ : ℝ, 0 ≤ z → θ ∈ Work.Spaces.Iθ →
      |Work.FTS_RegExport.RXR5.SG α g z θ τ| ≤ Mval := by
    intro τ hτ z θ hz hθ
    rw [hMvaldef]
    exact SG_sup_le_aux hα hα13 hOK hS τ hτ z hz θ hθ
  obtain ⟨Md, hMd0, hderiv⟩ := SG_zderiv_aux hα hα13 hOK hS hSt1'
  have hcont0 := SG_cont0 hα hα13 hOK hS hSt1'
  obtain ⟨Lθ, hLθ0, hth⟩ := SG_theta_mod hα hα13 hOK hS hSt1'
  obtain ⟨Lt, hLt0, htau⟩ := SG_tau_mod_aux hα hα13 hOK hS
  obtain ⟨Lz, hLz0, hzmod⟩ := SG_zmod hα hα1 hMd0 hMval0 hderiv hcont0 hsup
  obtain ⟨Njet, hJet⟩ := Work.FTS.RegPkgGal.R3d.jet_of_bounded_holder
    (hα := hα) (hM := hMval0) (hLz := hLz0) (hLθ := hLθ0) (hLt := hLt0)
    (h := fun z θ τ => Work.FTS_RegExport.RXR5.SG α g z θ τ)
    hsup hzmod hth htau
  refine ⟨max Njet Md, le_trans hJet.1 (le_max_left _ _), ?_, ?_⟩
  · exact Jet_mono hJet (le_max_left _ _)
  · intro τ hτ θ hθ z hz
    obtain ⟨d, hd, hbd⟩ := hderiv τ hτ θ hθ z hz
    exact ⟨d, hd, le_trans hbd (le_max_right _ _)⟩

end Work.FTS_RegExport.RXR5L
