/-
# Integrability of the `L₁₂`-density of the transport term `Transport f`

`Transport f = 3 sin(2θ) ∂_θ f/(1+z) = 3 D_θ f/(1+z)` is the transport (projector) term of the
coercivity form, and `Transport_L12_integrable` is the *honesty* statement needed to use it in
the `L₁₂`-bookkeeping of the `RHS` chapter: both the angular slices of its `L₁₂`-density and the
density itself are integrable.

## What is being asked

```
(∀ s > 0, ∫_θ |K θ · Transport f s θ / s| < ∞)  ∧  ∫_{(0,∞)} |L12dens (Transport f)| < ∞
```

for `f` of class `SmoothOpen` (i.e. `C^∞` on the open quadrant, all that the a.e. strong
measurability arguments need) and `f ∈ ℋ⁴_α` (`Work.Spaces.HkMem α 4 f`).

## Route

`Work.Coercivity.Transport f = 3 sin(2θ) ∂_θ f/(1+z)`, so its weighted angular derivative is the
`(i,j) = (1,0)` **slot of the `ℋ⁴`-integrand of `f` itself**:

* the factorisation `tl12_Transport_integrand_eq` of `Work.FTS.StrongPersist.L3Aux` writes
  `K θ·Transport f s θ/s = Wlam3 s · (KG α θ · (D_θ f s θ · W s))` with
  `KG α θ = 3 K θ sin(2θ)^{γ/2}` (`√(∫_θ KG²) ≤ 13`) and `W = w sin(2θ)^{-γ/2}` the `ℋ⁴`-weight;
* `|D_θ f s θ · W| ≤ √(HkIntegrand α 4 f s θ)` is `sq_le_HkIntegrand_mixed` at `(i,j) = (1,0)`,
  which is one of the summands of `HkIntegrand α 4 f` — **no hypothesis on `Transport f` itself
  is needed** (and indeed `ℋ⁴ ∋ f` does *not* imply `Transport f ∈ ℋ⁴`: the slot `D_z^4 D_θ f`
  has total order 5);
* AM–GM `√x ≤ (1+x)/2` turns this into the integrable majorant
  `Wlam3 s · 9(1 + HkIntegrand α 4 f s θ)/2` of the angular slice (`hmf.1`), and
  `Wlam3 s · A s ≤ Wlam3 s² + A s²` (`A s = √(∫_θ HkIntegrand α 4 f s θ)`) into the integrable
  majorant `13 (Wlam3² + A²)` of the density (`hmf.2` for `A²`, `psi_sq_integrable_aux` for
  `Wlam3² ≤ Wlam²`);
* the a.e. strong measurabilities come from the joint continuity on the open quadrant of
  `(z,θ) ↦ K θ·Transport f z θ/z` (`SmoothOpen.pth`), through
  `Work.Spaces.aesm_of_continuousOn_Qd` (+ Fubini measurability of the partial integral) and
  `Work.Spaces.aesm_slice_of_continuousOn_Qd`.

Everything rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.FTS.StrongPersist.L3Aux.Transport_L12_zero_le
import Submission.Work.FTS.GalBasis.cc.L12_add_of_HkMem

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open MeasureTheory Set Filter
open scoped Real Topology

namespace Work.FTS.GalFields.RHS

set_option linter.unusedVariables false

/-! ## Continuity of the density integrand on the open quadrant -/

/-- The joint integrand `(z,θ) ↦ K θ·Transport f z θ/z` of the `L₁₂`-density of `Transport f`
is continuous on the open quadrant, for `f` of class `SmoothOpen`. -/
private theorem transport_dens_continuousOn {f : ℝ → ℝ → ℝ}
    (hSf : Work.FTS.EllipticEst.SmoothOpen f) :
    ContinuousOn (fun p : ℝ × ℝ =>
      Work.Spaces.K p.2 * Work.Coercivity.Transport f p.1 p.2 / p.1)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) := by
  have hpth : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.pth f p.1 p.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) := (hSf.pth).continuousOn
  have hK : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.K p.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) := by
    have hc : Continuous fun θ : ℝ => Work.Spaces.K θ := by
      change Continuous fun θ : ℝ => 3 * Real.sin θ * Real.cos θ ^ 2
      fun_prop
    exact (hc.comp continuous_snd).continuousOn
  have hTr : ContinuousOn (fun p : ℝ × ℝ => Work.Coercivity.Transport f p.1 p.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) := by
    show ContinuousOn (fun p : ℝ × ℝ =>
      3 * (Real.sin (2 * p.2) * Work.Spaces.pth f p.1 p.2) / (1 + p.1))
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2))
    refine ContinuousOn.div ?_ (continuousOn_const.add continuousOn_fst) (fun p hp => ?_)
    · exact continuousOn_const.mul
        (((Real.continuous_sin.comp (continuous_const.mul continuous_snd)).continuousOn).mul hpth)
    · have h1 : (0 : ℝ) < p.1 := (Set.mem_prod.mp hp).1
      linarith
  exact (hK.mul hTr).div continuousOn_fst
    (fun p hp => ne_of_gt (Set.mem_prod.mp hp).1)

/-- **A.e. strong measurability of the `L₁₂`-density of the transport term** on `(0,∞)`: the
density is the partial `θ`-integral of the jointly continuous integrand of
`transport_dens_continuousOn`, hence a.e. strongly measurable by Fubini measurability. -/
private theorem aesm_L12dens_transport {f : ℝ → ℝ → ℝ}
    (hSf : Work.FTS.EllipticEst.SmoothOpen f) :
    AEStronglyMeasurable (Work.Construction.L12dens (Work.Coercivity.Transport f))
      (volume.restrict (Set.Ioi 0)) := by
  have hcont := transport_dens_continuousOn hSf
  have hjoint := Work.Spaces.aesm_of_continuousOn_Qd
    (fun p : ℝ × ℝ => Work.Spaces.K p.2 * Work.Coercivity.Transport f p.1 p.2 / p.1) hcont
  have h := hjoint.integral_prod_right' (μ := volume.restrict Work.Spaces.Iz)
  have h3 : AEStronglyMeasurable (Work.Construction.L12dens (Work.Coercivity.Transport f))
      (volume.restrict Work.Spaces.Iz) := by
    convert h using 1
    funext z
    rfl
  have hset : Set.Ioi (0 : ℝ) =ᵐ[volume] Work.Spaces.Iz := MeasureTheory.Ioi_ae_eq_Ici
  rw [MeasureTheory.Measure.restrict_congr_set hset]
  exact h3

/-! ## The two pointwise bounds -/

/-- **Pointwise bound on an angular slice.**  For `s > 0` and `θ ∈ Iθ`, the slice integrand of
the `L₁₂`-density of `Transport f` is dominated by `Wlam3 s·9(1 + HkIntegrand α 4 f s θ)/2`,
an integrable function of `θ` as soon as `f ∈ ℋ⁴_α`.  The `ℋ⁴`-slot used is the `(i,j) = (1,0)`
one, `(D_θ f·W)² ≤ HkIntegrand α 4 f`. -/
private theorem transport_slice_pointwise_le {α : ℝ} (hα : 0 < α) {f : ℝ → ℝ → ℝ} {s θ : ℝ}
    (hs : 0 < s) (hθ : θ ∈ Work.Spaces.Iθ) :
    |Work.Spaces.K θ * Work.Coercivity.Transport f s θ / s|
      ≤ Work.FTS.StrongPersist.L3Aux.Wlam3 s
        * (9 * (1 + Work.Spaces.HkIntegrand α 4 f s θ) / 2) := by
  rw [Work.FTS.StrongPersist.L3Aux.tl12_Transport_integrand_eq α f hs hθ]
  rw [abs_mul, abs_of_nonneg (Work.FTS.StrongPersist.L3Aux.tl12_Wlam3_nonneg (le_of_lt hs))]
  refine mul_le_mul_of_nonneg_left ?_
    (Work.FTS.StrongPersist.L3Aux.tl12_Wlam3_nonneg (le_of_lt hs))
  have hKGnn : 0 ≤ Work.FTS.StrongPersist.L3Aux.KG α θ :=
    Work.FTS.StrongPersist.L3Aux.tl12_KG_nonneg α hθ
  have hKGle : Work.FTS.StrongPersist.L3Aux.KG α θ ≤ 9 :=
    Work.FTS.StrongPersist.L3Aux.tl12_KG_le_nine α hθ
      (Work.FTS.StrongPersist.L3Aux.tl12_gam_half_nonneg hα)
  have hsq : (Work.Spaces.mixed 0 1 f s θ * Work.Spaces.Wt α s θ) ^ 2
      ≤ Work.Spaces.HkIntegrand α 4 f s θ :=
    Work.Spaces.sq_le_HkIntegrand_mixed α 4 f s θ 1 0 (le_refl 1) (by norm_num)
  have hb : |Work.Spaces.mixed 0 1 f s θ * Work.Spaces.Wt α s θ|
      ≤ Real.sqrt (Work.Spaces.HkIntegrand α 4 f s θ) := by
    rw [← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_le_sqrt hsq
  have hAM := Work.FTS.GalBasis.cc.sqrt_le_half_one_add
    (Work.Spaces.HkIntegrand_nonneg α 4 f s θ)
  calc |Work.FTS.StrongPersist.L3Aux.KG α θ
        * (Work.Spaces.mixed 0 1 f s θ * Work.Spaces.Wt α s θ)|
      = Work.FTS.StrongPersist.L3Aux.KG α θ
          * |Work.Spaces.mixed 0 1 f s θ * Work.Spaces.Wt α s θ| := by
        rw [abs_mul, abs_of_nonneg hKGnn]
    _ ≤ 9 * Real.sqrt (Work.Spaces.HkIntegrand α 4 f s θ) :=
        mul_le_mul hKGle hb (abs_nonneg _) (by norm_num)
    _ ≤ 9 * (1 + Work.Spaces.HkIntegrand α 4 f s θ) / 2 := by
        have h := mul_le_mul_of_nonneg_left hAM (by norm_num : (0 : ℝ) ≤ 9)
        linarith

/-- **Pointwise bound on the density.**  For `s > 0` and `f ∈ ℋ⁴_α`, the `L₁₂`-density of
`Transport f` is dominated by `13·(Wlam3 s² + (√(∫_θ HkIntegrand α 4 f s θ))²)`: the angular
Cauchy–Schwarz step `tl12_abs_integral_KG_le` (with `√(∫_θ KG²) ≤ 13`) followed by AM–GM. -/
private theorem transport_L12dens_pointwise_le {α : ℝ} (hα : 0 < α) {f : ℝ → ℝ → ℝ}
    (hmf : Work.Spaces.HkMem α 4 f) {s : ℝ} (hs : 0 < s) :
    |Work.Construction.L12dens (Work.Coercivity.Transport f) s|
      ≤ 13 * (Work.FTS.StrongPersist.L3Aux.Wlam3 s ^ 2
          + (Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 f s θ)) ^ 2) := by
  have hsz : s ∈ Work.Spaces.Iz := le_of_lt hs
  have hInt : IntegrableOn (fun θ => Work.Spaces.HkIntegrand α 4 f s θ) Work.Spaces.Iθ :=
    hmf.1 s hsz
  have hW3nn : 0 ≤ Work.FTS.StrongPersist.L3Aux.Wlam3 s :=
    Work.FTS.StrongPersist.L3Aux.tl12_Wlam3_nonneg (le_of_lt hs)
  rw [Work.FTS.StrongPersist.L3Aux.tl12_L12dens_Transport_eq α f hs, abs_mul,
    abs_of_nonneg hW3nn]
  have h1 : |∫ θ in Work.Spaces.Iθ, Work.FTS.StrongPersist.L3Aux.KG α θ
        * (Work.Spaces.mixed 0 1 f s θ * Work.Spaces.Wt α s θ)|
      ≤ 13 * Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 f s θ) := by
    refine le_trans (Work.FTS.StrongPersist.L3Aux.tl12_abs_integral_KG_le α hα f hInt) ?_
    have h13 := Work.FTS.StrongPersist.L3Aux.tl12_sqrt_KG_sq_le α hα
    exact mul_le_mul_of_nonneg_right h13 (Real.sqrt_nonneg _)
  calc Work.FTS.StrongPersist.L3Aux.Wlam3 s
        * |∫ θ in Work.Spaces.Iθ, Work.FTS.StrongPersist.L3Aux.KG α θ
            * (Work.Spaces.mixed 0 1 f s θ * Work.Spaces.Wt α s θ)|
      ≤ Work.FTS.StrongPersist.L3Aux.Wlam3 s
          * (13 * Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 f s θ)) :=
        mul_le_mul_of_nonneg_left h1 hW3nn
    _ = 13 * (Work.FTS.StrongPersist.L3Aux.Wlam3 s
          * Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 f s θ)) := by ring
    _ ≤ 13 * (Work.FTS.StrongPersist.L3Aux.Wlam3 s ^ 2
          + (Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 f s θ)) ^ 2) := by
        refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
        nlinarith [sq_nonneg (Work.FTS.StrongPersist.L3Aux.Wlam3 s
          - Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 f s θ))]

/-! ## The theorem -/

theorem Transport_L12_integrable {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {f : ℝ → ℝ → ℝ}
    (hSf : Work.FTS.EllipticEst.SmoothOpen f) (hmf : Work.Spaces.HkMem α 4 f) :
    (∀ s : ℝ, 0 < s → MeasureTheory.IntegrableOn
        (fun θ => Work.Spaces.K θ * Work.Coercivity.Transport f s θ / s) Work.Spaces.Iθ) ∧
      MeasureTheory.IntegrableOn
        (fun s => Work.Construction.L12dens (Work.Coercivity.Transport f) s) (Set.Ioi 0) := by
  have hcont := transport_dens_continuousOn hSf
  have hIθ : MeasurableSet Work.Spaces.Iθ := measurableSet_Icc
  constructor
  · intro s hs
    have hsz : s ∈ Work.Spaces.Iz := le_of_lt hs
    have hHk : IntegrableOn (fun θ => Work.Spaces.HkIntegrand α 4 f s θ) Work.Spaces.Iθ :=
      hmf.1 s hsz
    have haesm : AEStronglyMeasurable
        (fun θ => Work.Spaces.K θ * Work.Coercivity.Transport f s θ / s)
        (volume.restrict Work.Spaces.Iθ) :=
      Work.Spaces.aesm_slice_of_continuousOn_Qd _ hcont hs
    have hconst : IntegrableOn (fun _ : ℝ => (1 : ℝ)) Work.Spaces.Iθ :=
      continuous_const.integrableOn_Icc
    have hmaj : IntegrableOn (fun θ => Work.FTS.StrongPersist.L3Aux.Wlam3 s
        * (9 * (1 + Work.Spaces.HkIntegrand α 4 f s θ) / 2)) Work.Spaces.Iθ := by
      have h1 : IntegrableOn (fun θ => (Work.FTS.StrongPersist.L3Aux.Wlam3 s * (9 / 2))
          * (1 + Work.Spaces.HkIntegrand α 4 f s θ)) Work.Spaces.Iθ :=
        (hconst.add hHk).const_mul _
      refine h1.congr_fun (fun θ _ => ?_) hIθ
      ring
    refine hmaj.mono' haesm ?_
    rw [ae_restrict_iff' hIθ]
    exact Eventually.of_forall fun θ hθ => by
      rw [Real.norm_eq_abs]
      exact transport_slice_pointwise_le hα hs hθ
  · set H : ℝ → ℝ := fun s => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 f s θ with hH
    set A : ℝ → ℝ := fun s => Real.sqrt (H s) with hA
    have hHnn : ∀ s, 0 ≤ H s :=
      fun s => integral_nonneg fun θ => Work.Spaces.HkIntegrand_nonneg α 4 f s θ
    have hH_int : IntegrableOn H (Set.Ioi 0) := hmf.2.mono_set Set.Ioi_subset_Ici_self
    have hA2_int : IntegrableOn (fun s => A s ^ 2) (Set.Ioi 0) :=
      hH_int.congr (Eventually.of_forall fun s => (Real.sq_sqrt (hHnn s)).symm)
    have hcont3 : ContinuousOn Work.FTS.StrongPersist.L3Aux.Wlam3 (Set.Ioi 0) := by
      change ContinuousOn (fun s : ℝ => s / (1 + s) ^ 3) (Set.Ioi 0)
      refine ContinuousOn.div continuousOn_id ((continuousOn_const.add continuousOn_id).pow 3)
        (fun s hs => ?_)
      have h1 : (0 : ℝ) < 1 + s := by linarith [Set.mem_Ioi.mp hs]
      positivity
    have hW3sq_int : IntegrableOn (fun s => Work.FTS.StrongPersist.L3Aux.Wlam3 s ^ 2)
        (Set.Ioi 0) := by
      refine Work.Elliptic.psi_sq_integrable_aux.mono'
        ((hcont3.pow 2).aestronglyMeasurable measurableSet_Ioi) ?_
      filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with s hs
      have hsm : 0 < s := Set.mem_Ioi.mp hs
      have h0 : 0 ≤ Work.FTS.StrongPersist.L3Aux.Wlam3 s :=
        Work.FTS.StrongPersist.L3Aux.tl12_Wlam3_nonneg (le_of_lt hsm)
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact pow_le_pow_left₀ h0
        (Work.FTS.StrongPersist.L3Aux.tl12_Wlam3_le_Wlam (le_of_lt hsm)) 2
    have hmaj : IntegrableOn
        (fun s => 13 * (Work.FTS.StrongPersist.L3Aux.Wlam3 s ^ 2 + A s ^ 2))
        (Set.Ioi 0) := (hW3sq_int.add hA2_int).const_mul 13
    refine hmaj.mono' (aesm_L12dens_transport hSf) ?_
    rw [ae_restrict_iff' measurableSet_Ioi]
    exact Eventually.of_forall fun s hs => by
      have hb := transport_L12dens_pointwise_le hα hmf hs
      simpa only [hA, hH, Real.norm_eq_abs] using hb

end Work.FTS.GalFields.RHS
