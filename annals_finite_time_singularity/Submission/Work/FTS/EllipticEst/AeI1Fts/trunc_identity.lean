import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.FTS.EllipticEst.AeI1Fts.zibp_zouter
import Submission.Work.FTS.EllipticEst.AeI1Fts.slice_theta_ibp_cut
import Submission.Work.FTS.EllipticEst.SliceMixedAux.smoothCutoffIoo
import Submission.Work.FTS.EllipticEst.AeI1Fts.Defs
import Submission.Work.FTS.EllipticEst.AeI1Fts.identity_defs
import Submission.Work.FTS.EllipticEst.AeI1Fts.UBB_continuousOn_box
import Submission.Work.FTS.EllipticEst.I1Ae.zibpChain
import Submission.Work.FTS.EllipticEst.I1Ae.thetaChain

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `AeI1Fts/trunc_identity` — the truncated `I₁` chain identity

The target is the paper's `I₁` chain identity (Step 2 of `prop:H2` of

  T. M. Elgindi, *Finite-time singularity formation for `C^{1,α}` solutions to the
  incompressible Euler equations on `ℝ³`*, Annals of Math. **194** (2021))

in the weak class `H2W.Ae.AeData`, in the form in which the *radial* cut-off `χ_k = cut k`
and the *angular* cut-off `χ_ε = SliceMixedAux.cut ε` (with `ε = 1/(k+1)`) are kept, and
written as a `z`-outer iterated integral whose inner `θ`-integrand still carries the radial
cut-off.  With `U = z∂_zu`, `V = z∂_z∂_θu`, `Hh = z∂_z∂_θθu`, `AA = z²∂_zzu`,
`BB = ∂_θθu`, `cw z = 2(z-1)/(1+z)`, `w z = (1+z)²/z²`, `σ = sigE = sin(2θ)^{-η}`,
`σ₁ = sig1 = sin(2θ)^{-1-η}`, `Fp u = AA·BB + cw·U·BB + U·Hh` and
`Fd u = z·(z∂_zu)·∂_θθu·w²` (the two `z`-integrands of the pointwise identity
`∂_z Fd = w² Fp`), the identity is

```
∫_z χ_k w² ∫_θ σ χ_ε (AA·BB + cw·U·BB)
  = -∫_z (z χ_k') w² ∫_θ σ χ_ε (U·BB)      -- radial IBP
    + ∫_z χ_k w² ∫_θ σ χ_ε V²               -- angular IBP
    - 2η ∫_z χ_k w² ∫_θ σ₁ χ_ε (U V cos 2θ) -- angular IBP
    + ∫_z χ_k w² ∫_θ σ χ_ε' (U V)           -- angular IBP
```

## Route

* `I1Ae.zibpChain` (proved elsewhere) is the radial integration by parts of
  `∂_z Fd = w² Fp` against `χ_k` in *double*-integral form, with the angular weight
  `σ χ_ε` inserted;
* `I1Ae.thetaChain` (proved elsewhere) is the angular integration by parts of
  `∂_θ(U·V·σ) = V²σ + U·Hh·σ - 2η U·V cos 2θ σ₁` against `χ_ε`, again in double form;
* on the compact box `[1/(2(k+1)), 4(k+1)] × [ε/2, π/2 - ε/2]` both the `Fp u`- and the
  `U u·Hh u`-integrand are continuous and compactly supported, hence summable for
  `dz dθ`; this is what allows the double integral of
  `w²σ χ_k χ_ε (AA·BB + cw·U·BB) = w²σ χ_k χ_ε (Fp u - U u·Hh u)` to be split;
* finally every double integral is converted back to the `z`-outer form of the statement
  by the (unconditional) pull-out of the `z`-dependent constant out of the `θ`-integral.
-/

namespace Work.FTS.EllipticEst.AeI1Fts

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false
set_option maxHeartbeats 1600000

local notation "Iθo" => Set.Ioo (0 : ℝ) (Real.pi / 2)

/-! ## Integrability helpers -/

/-- A function continuous on a compact interval and vanishing off it is integrable on the open
angular interval (which contains the compact interval). -/
private theorem integrableOn_Ioo_of_Icc_support {f : ℝ → ℝ} {c d : ℝ}
    (hcont : ContinuousOn f (Set.Icc c d))
    (hzero : ∀ x ∈ Iθo, x ∉ Set.Icc c d → f x = 0) :
    IntegrableOn f Iθo := by
  have hInd : Integrable ((Set.Icc c d).indicator f) volume :=
    (integrable_indicator_iff measurableSet_Icc).mpr (hcont.integrableOn_compact isCompact_Icc)
  refine (hInd.mono_measure Measure.restrict_le_self).congr ?_
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with x hx
  by_cases hxd : x ∈ Set.Icc c d
  · rw [Set.indicator_of_mem hxd]
  · rw [Set.indicator_of_notMem hxd, hzero x hx hxd]

/-- A function continuous on a compact box of the open quadrant and vanishing off it is
summable for the product of the two restricted measures. -/
private theorem integrable_prod_of_box {g : ℝ → ℝ → ℝ} {a b c d : ℝ}
    (hcont : ContinuousOn (Function.uncurry g) (Set.Icc a b ×ˢ Set.Icc c d))
    (hbox : ∀ z θ, (z ∉ Set.Icc a b ∨ θ ∉ Set.Icc c d) → g z θ = 0) :
    Integrable (Function.uncurry g)
      ((MeasureTheory.volume.restrict (Set.Ioi 0)).prod
        (MeasureTheory.volume.restrict Iθo)) := by
  have hIntK : IntegrableOn (Function.uncurry g) (Set.Icc a b ×ˢ Set.Icc c d) volume :=
    ContinuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc) hcont
  have hvol : Integrable (Function.uncurry g) (volume : Measure (ℝ × ℝ)) :=
    hIntK.integrable_of_forall_notMem_eq_zero (fun p hp => by
      rw [Set.mem_prod] at hp
      exact hbox p.1 p.2 (not_and_or.mp hp))
  rw [MeasureTheory.Measure.prod_restrict]
  exact hvol.mono_measure MeasureTheory.Measure.restrict_le_self

/-! ## Joint continuity of the elementary factors on the open quadrant -/

private theorem continuousOn_wSq_Q0 :
    ContinuousOn (fun p : ℝ × ℝ => (Work.Spaces.w p.1) ^ 2) Work.FTS.EllipticEst.Q0 := by
  have h : ContinuousOn (fun z : ℝ => (Work.Spaces.w z) ^ 2) (Set.Ioi 0) := by
    have h' : ContinuousOn (fun z : ℝ => Work.Spaces.w z) (Set.Ioi 0) := by
      show ContinuousOn (fun z : ℝ => (1 + z) ^ 2 / z ^ 2) (Set.Ioi 0)
      exact ((continuous_const.add continuous_id).pow 2).continuousOn.div
        ((continuous_id.pow 2).continuousOn) (fun z hz => pow_ne_zero 2 (ne_of_gt hz))
    exact h'.pow 2
  exact h.comp continuous_fst.continuousOn (fun _ hp => hp.1)

private theorem continuousOn_sigE_Q0 :
    ContinuousOn (fun p : ℝ × ℝ => sigE p.2) Work.FTS.EllipticEst.Q0 := by
  have hsin2 : ContinuousOn (fun p : ℝ × ℝ => Real.sin (2 * p.2)) Work.FTS.EllipticEst.Q0 :=
    (Real.continuous_sin.comp (continuous_const.mul continuous_snd)).continuousOn
  exact hsin2.rpow_const (fun p hp => by
    left
    have hp' := Work.FTS.EllipticEst.mem_Q0.mp hp
    exact ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (by linarith [hp'.2.1])
      (by linarith [hp'.2.2, Real.pi_pos])))

private theorem continuousOn_cut_Q0 (n : ℕ) :
    ContinuousOn (fun p : ℝ × ℝ => Work.FTS.EllipticEst.cut n p.1)
      Work.FTS.EllipticEst.Q0 :=
  (((Work.FTS.EllipticEst.cut_contDiff n).continuous).continuousOn).comp
    continuous_fst.continuousOn (fun _ _ => Set.mem_univ _)

private theorem continuousOn_cutE_Q0 (ε : ℝ) :
    ContinuousOn (fun p : ℝ × ℝ => Work.FTS.EllipticEst.SliceMixedAux.cut ε p.2)
      Work.FTS.EllipticEst.Q0 :=
  (((Work.FTS.EllipticEst.SliceMixedAux.cut_contDiff ε).continuous).continuousOn).comp
    continuous_snd.continuousOn (fun _ _ => Set.mem_univ _)

private theorem continuousOn_cw_Q0 :
    ContinuousOn (fun p : ℝ × ℝ => Work.FTS.EllipticEst.AngSecond.cw p.1)
      Work.FTS.EllipticEst.Q0 := by
  show ContinuousOn (fun p : ℝ × ℝ => 2 * (p.1 - 1) / (1 + p.1)) Work.FTS.EllipticEst.Q0
  refine ContinuousOn.div (continuousOn_const.mul (continuousOn_fst.sub continuousOn_const))
    (continuousOn_const.add continuousOn_fst) (fun p hp => ?_)
  have hp1 : 0 < p.1 := (Work.FTS.EllipticEst.mem_Q0.mp hp).1
  linarith

/-- Joint continuity of `Fp u` on the open quadrant. -/
private theorem continuousOn_Fp_Q0 {u : ℝ → ℝ → ℝ}
    (hS : Work.FTS.EllipticEst.SmoothOpen u) :
    ContinuousOn (fun p : ℝ × ℝ => Fp u p.1 p.2) Work.FTS.EllipticEst.Q0 := by
  have hpz2 : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.pzIter 2 u p.1 p.2)
      Work.FTS.EllipticEst.Q0 := (hS.pzIter 2).continuousOn
  have hpt2 : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.pthIter 2 u p.1 p.2)
      Work.FTS.EllipticEst.Q0 := (smoothOpen_pthIter hS 2).continuousOn
  have hpz : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.pz u p.1 p.2)
      Work.FTS.EllipticEst.Q0 := (hS.pz).continuousOn
  have hpzp2 : ContinuousOn (fun p : ℝ × ℝ =>
      Work.Spaces.pz (Work.Spaces.pthIter 2 u) p.1 p.2) Work.FTS.EllipticEst.Q0 :=
    ((smoothOpen_pthIter hS 2).pz).continuousOn
  have hmain : ContinuousOn (fun p : ℝ × ℝ =>
      (p.1 ^ 2 * Work.Spaces.pzIter 2 u p.1 p.2) * Work.Spaces.pthIter 2 u p.1 p.2
        + (Work.FTS.EllipticEst.AngSecond.cw p.1 * (p.1 * Work.Spaces.pz u p.1 p.2))
            * Work.Spaces.pthIter 2 u p.1 p.2
        + (p.1 * Work.Spaces.pz u p.1 p.2)
            * (p.1 * Work.Spaces.pz (Work.Spaces.pthIter 2 u) p.1 p.2))
      Work.FTS.EllipticEst.Q0 :=
    (((continuousOn_fst.pow 2).mul hpz2).mul hpt2).add
      ((continuousOn_cw_Q0.mul (continuousOn_fst.mul hpz)).mul hpt2) |>.add
      ((continuousOn_fst.mul hpz).mul (continuousOn_fst.mul hpzp2))
  refine hmain.congr (fun p _ => ?_)
  simp only [Fp]

/-- Joint continuity of `U u · Hh u` on the open quadrant. -/
private theorem continuousOn_UHh_Q0 {u : ℝ → ℝ → ℝ}
    (hS : Work.FTS.EllipticEst.SmoothOpen u) :
    ContinuousOn (fun p : ℝ × ℝ => U u p.1 p.2 * Hh u p.1 p.2)
      Work.FTS.EllipticEst.Q0 := by
  have h1 : ContinuousOn (fun p : ℝ × ℝ => U u p.1 p.2) Work.FTS.EllipticEst.Q0 :=
    continuousOn_U hS
  have h2 : ContinuousOn (fun p : ℝ × ℝ => Hh u p.1 p.2) Work.FTS.EllipticEst.Q0 :=
    continuousOn_Hh hS
  exact h1.mul h2

/-! ## The two elementary integrability facts -/

/-- The angular weight `σ = sin(2θ)^{-η}` is continuous on a compact sub-interval of
`(0, π/2)`. -/
private theorem continuousOn_sigE_Icc {c d : ℝ} (hc : 0 < c) (hd : d < Real.pi / 2) :
    ContinuousOn sigE (Set.Icc c d) := by
  have hsin : ContinuousOn (fun θ : ℝ => Real.sin (2 * θ)) (Set.Icc c d) :=
    (Real.continuous_sin.comp (continuous_const.mul continuous_id)).continuousOn
  refine (hsin.rpow_const (p := -(Work.Spaces.eta)) ?_).congr (fun θ _ => rfl)
  intro θ hθ
  left
  exact ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1, hc])
    (by linarith [hθ.2, hd, Real.pi_pos]))

/-- The `θ`-slice at fixed `z > 0` of the truncated integrand
`w(z)² σ(θ) χ_k(z) χ_ε(θ) F(z,θ)` is integrable on the open angular interval, for a joint
integrand `F` continuous on the open quadrant. -/
private theorem intOn_theta_cut {k : ℕ} {ε : ℝ} (hε : 0 < ε) {z : ℝ} (hz : 0 < z)
    {F : ℝ → ℝ → ℝ} (hF : ContinuousOn (fun p : ℝ × ℝ => F p.1 p.2) Work.FTS.EllipticEst.Q0) :
    IntegrableOn (fun θ => (Work.Spaces.w z) ^ 2 * sigE θ
      * (Work.FTS.EllipticEst.cut k z * Work.FTS.EllipticEst.SliceMixedAux.cut ε θ)
      * F z θ) Iθo := by
  refine integrableOn_Ioo_of_Icc_support
    (c := ε / 2) (d := Real.pi / 2 - ε / 2) ?_ ?_
  · have hsig : ContinuousOn sigE (Set.Icc (ε / 2) (Real.pi / 2 - ε / 2)) :=
      continuousOn_sigE_Icc (by linarith) (by linarith [Real.pi_pos])
    have hcutE : ContinuousOn (fun θ : ℝ =>
        Work.FTS.EllipticEst.SliceMixedAux.cut ε θ)
        (Set.Icc (ε / 2) (Real.pi / 2 - ε / 2)) :=
      ((Work.FTS.EllipticEst.SliceMixedAux.cut_contDiff ε).continuous).continuousOn
    have hFz : ContinuousOn (fun θ : ℝ => F z θ) (Set.Icc (ε / 2) (Real.pi / 2 - ε / 2)) := by
      have hε2 : (0 : ℝ) < ε / 2 := by linarith
      have hcomp : ContinuousOn (fun θ : ℝ => F z (id θ))
          (Set.Icc (ε / 2) (Real.pi / 2 - ε / 2)) :=
        hF.comp (continuousOn_const.prodMk continuousOn_id) (fun θ hθ => by
          refine Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz, ?_, ?_⟩
          · exact lt_of_lt_of_le hε2 (Set.mem_Icc.mp hθ).1
          · have hmid : θ < Real.pi / 2 := by
              have h2 := (Set.mem_Icc.mp hθ).2
              linarith [Real.pi_pos]
            exact hmid)
      simpa only [id_eq] using hcomp
    exact ((continuousOn_const.mul hsig).mul
      (continuousOn_const.mul hcutE)).mul hFz
  · intro x hx hxnot
    rw [Set.mem_Icc, not_and_or, not_le, not_le] at hxnot
    rcases hxnot with h | h
    · rw [Work.FTS.EllipticEst.SliceMixedAux.cut_eq_zero_low hε (le_of_lt h)]
      ring
    · rw [Work.FTS.EllipticEst.SliceMixedAux.cut_eq_zero_high hε (le_of_lt h)]
      ring

/-- The `z`-marginal of the truncated integrand is integrable on `(0,∞)`: both cut-offs have
compact support, so everything lives on the box
`[1/(2(k+1)), 4(k+1)] × [ε/2, π/2 - ε/2]`, where the integrand is continuous. -/
private theorem intOn_z_marginal {k : ℕ} {ε : ℝ} (hε : 0 < ε) {F : ℝ → ℝ → ℝ}
    (hF : ContinuousOn (fun p : ℝ × ℝ => F p.1 p.2) Work.FTS.EllipticEst.Q0) :
    IntegrableOn (fun z => ∫ θ in Iθo, (Work.Spaces.w z) ^ 2 * sigE θ
      * (Work.FTS.EllipticEst.cut k z * Work.FTS.EllipticEst.SliceMixedAux.cut ε θ)
      * F z θ) (Set.Ioi 0) := by
  have hk : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  set a : ℝ := 1 / (2 * ((k : ℝ) + 1)) with ha
  set b : ℝ := 4 * ((k : ℝ) + 1) with hb
  set c : ℝ := ε / 2 with hc
  set d : ℝ := Real.pi / 2 - ε / 2 with hd
  have ha_pos : 0 < a := by rw [ha]; positivity
  have hc_pos : 0 < c := by rw [hc]; linarith
  have hd_lt : d < Real.pi / 2 := by rw [hd]; linarith
  have hKsub : Set.Icc a b ×ˢ Set.Icc c d ⊆ Work.FTS.EllipticEst.Q0 :=
    box_subset_Q0 ha_pos hc_pos hd_lt
  have hcutk : ∀ z, z ∉ Set.Icc a b → Work.FTS.EllipticEst.cut k z = 0 := by
    intro z hz
    rw [Set.mem_Icc, not_and_or, not_le, not_le] at hz
    rcases hz with hz | hz
    · rw [ha] at hz
      refine Work.FTS.EllipticEst.cut_apply_zero_of_le k ?_
      have h2 : 1 / (2 * ((k : ℝ) + 1)) ≤ 1 / ((k : ℝ) + 1) :=
        one_div_le_one_div_of_le hk (by linarith)
      linarith
    · rw [hb] at hz
      refine Work.FTS.EllipticEst.cut_apply_zero_of_ge k ?_
      push_cast
      linarith
  have hcutE : ∀ θ, θ ∉ Set.Icc c d → Work.FTS.EllipticEst.SliceMixedAux.cut ε θ = 0 := by
    intro θ hθ
    rw [Set.mem_Icc, not_and_or, not_le, not_le] at hθ
    rcases hθ with hθ | hθ
    · rw [hc] at hθ
      exact Work.FTS.EllipticEst.SliceMixedAux.cut_eq_zero_low hε (le_of_lt hθ)
    · rw [hd] at hθ
      exact Work.FTS.EllipticEst.SliceMixedAux.cut_eq_zero_high hε (le_of_lt hθ)
  have h1 : ContinuousOn (fun p : ℝ × ℝ => (Work.Spaces.w p.1) ^ 2 * sigE p.2)
      (Set.Icc a b ×ˢ Set.Icc c d) :=
    (continuousOn_wSq_Q0.mono hKsub).mul (continuousOn_sigE_Q0.mono hKsub)
  have h2 : ContinuousOn (fun p : ℝ × ℝ => Work.FTS.EllipticEst.cut k p.1
      * Work.FTS.EllipticEst.SliceMixedAux.cut ε p.2)
      (Set.Icc a b ×ˢ Set.Icc c d) :=
    (continuousOn_cut_Q0 k).mono hKsub |>.mul ((continuousOn_cutE_Q0 ε).mono hKsub)
  have h3 : ContinuousOn (fun p : ℝ × ℝ => (Work.Spaces.w p.1) ^ 2 * sigE p.2
      * (Work.FTS.EllipticEst.cut k p.1
        * Work.FTS.EllipticEst.SliceMixedAux.cut ε p.2))
      (Set.Icc a b ×ˢ Set.Icc c d) := h1.mul h2
  have hcont' : ContinuousOn (fun p : ℝ × ℝ => (Work.Spaces.w p.1) ^ 2 * sigE p.2
      * (Work.FTS.EllipticEst.cut k p.1
        * Work.FTS.EllipticEst.SliceMixedAux.cut ε p.2)
        * F p.1 p.2) (Set.Icc a b ×ˢ Set.Icc c d) := h3.mul (hF.mono hKsub)
  have hcont : ContinuousOn (Function.uncurry (fun z θ =>
      (Work.Spaces.w z) ^ 2 * sigE θ
        * (Work.FTS.EllipticEst.cut k z * Work.FTS.EllipticEst.SliceMixedAux.cut ε θ)
        * F z θ)) (Set.Icc a b ×ˢ Set.Icc c d) := by
    refine hcont'.congr (fun p _ => ?_)
    simp only [Function.uncurry]
  have hbox : ∀ z θ, (z ∉ Set.Icc a b ∨ θ ∉ Set.Icc c d) →
      (Work.Spaces.w z) ^ 2 * sigE θ
        * (Work.FTS.EllipticEst.cut k z * Work.FTS.EllipticEst.SliceMixedAux.cut ε θ)
        * F z θ = 0 := by
    intro z θ h
    rcases h with h | h
    · rw [hcutk z h]; ring
    · rw [hcutE θ h]; ring
  have h2 := (integrable_prod_of_box hcont hbox).integral_prod_left
  simpa only [MeasureTheory.IntegrableOn, Function.uncurry] using h2

/-! ## Splitting the truncated integrand along `Fp u = (AA·BB + cw·U·BB) + U·Hh` -/

/-- **The sum-splitting of the truncated identity.**  Writing
`(AA·BB + cw·U·BB) = Fp u - U·Hh` pointwise, the double integral of
`w²σ χ_k χ_ε (AA·BB + cw·U·BB)` splits into the difference of the double integrals of
`w²σ χ_k χ_ε Fp u` and `w²σ χ_k χ_ε (U·Hh)`. -/
private theorem split_joint {u : ℝ → ℝ → ℝ} (hS : Work.FTS.EllipticEst.SmoothOpen u)
    (k : ℕ) {ε : ℝ} (hε : 0 < ε) :
    (∫ z in Set.Ioi 0, ∫ θ in Iθo, (Work.Spaces.w z) ^ 2 * sigE θ
        * (Work.FTS.EllipticEst.cut k z * Work.FTS.EllipticEst.SliceMixedAux.cut ε θ)
        * (AA u z θ * BB u z θ + Work.FTS.EllipticEst.AngSecond.cw z * U u z θ * BB u z θ))
      = (∫ z in Set.Ioi 0, ∫ θ in Iθo, (Work.Spaces.w z) ^ 2 * sigE θ
            * (Work.FTS.EllipticEst.cut k z * Work.FTS.EllipticEst.SliceMixedAux.cut ε θ)
            * Fp u z θ)
        - (∫ z in Set.Ioi 0, ∫ θ in Iθo, (Work.Spaces.w z) ^ 2 * sigE θ
            * (Work.FTS.EllipticEst.cut k z * Work.FTS.EllipticEst.SliceMixedAux.cut ε θ)
            * (U u z θ * Hh u z θ)) := by
  have hFp : ContinuousOn (fun p : ℝ × ℝ => Fp u p.1 p.2) Work.FTS.EllipticEst.Q0 :=
    continuousOn_Fp_Q0 hS
  have hUHh : ContinuousOn (fun p : ℝ × ℝ => U u p.1 p.2 * Hh u p.1 p.2)
      Work.FTS.EllipticEst.Q0 := continuousOn_UHh_Q0 hS
  have hpt : ∀ z θ : ℝ,
      (Work.Spaces.w z) ^ 2 * sigE θ
          * (Work.FTS.EllipticEst.cut k z * Work.FTS.EllipticEst.SliceMixedAux.cut ε θ)
          * (AA u z θ * BB u z θ
              + Work.FTS.EllipticEst.AngSecond.cw z * U u z θ * BB u z θ)
        = (Work.Spaces.w z) ^ 2 * sigE θ
            * (Work.FTS.EllipticEst.cut k z * Work.FTS.EllipticEst.SliceMixedAux.cut ε θ)
            * Fp u z θ
          - (Work.Spaces.w z) ^ 2 * sigE θ
            * (Work.FTS.EllipticEst.cut k z * Work.FTS.EllipticEst.SliceMixedAux.cut ε θ)
            * (U u z θ * Hh u z θ) := by
    intro z θ
    simp only [Fp, AA, BB, U, Hh]
    ring
  have e1 : (∫ z in Set.Ioi 0, ∫ θ in Iθo, (Work.Spaces.w z) ^ 2 * sigE θ
        * (Work.FTS.EllipticEst.cut k z * Work.FTS.EllipticEst.SliceMixedAux.cut ε θ)
        * (AA u z θ * BB u z θ
            + Work.FTS.EllipticEst.AngSecond.cw z * U u z θ * BB u z θ))
      = ∫ z in Set.Ioi 0, ∫ θ in Iθo,
          ((Work.Spaces.w z) ^ 2 * sigE θ
              * (Work.FTS.EllipticEst.cut k z * Work.FTS.EllipticEst.SliceMixedAux.cut ε θ)
              * Fp u z θ
            - (Work.Spaces.w z) ^ 2 * sigE θ
              * (Work.FTS.EllipticEst.cut k z * Work.FTS.EllipticEst.SliceMixedAux.cut ε θ)
              * (U u z θ * Hh u z θ)) := by
    refine setIntegral_congr_fun measurableSet_Ioi (fun z _ => ?_)
    exact setIntegral_congr_fun measurableSet_Ioo (fun θ _ => hpt z θ)
  have e2 : (∫ z in Set.Ioi 0, ∫ θ in Iθo,
        ((Work.Spaces.w z) ^ 2 * sigE θ
            * (Work.FTS.EllipticEst.cut k z * Work.FTS.EllipticEst.SliceMixedAux.cut ε θ)
            * Fp u z θ
          - (Work.Spaces.w z) ^ 2 * sigE θ
            * (Work.FTS.EllipticEst.cut k z * Work.FTS.EllipticEst.SliceMixedAux.cut ε θ)
            * (U u z θ * Hh u z θ)))
      = ∫ z in Set.Ioi 0,
          ((∫ θ in Iθo, (Work.Spaces.w z) ^ 2 * sigE θ
              * (Work.FTS.EllipticEst.cut k z * Work.FTS.EllipticEst.SliceMixedAux.cut ε θ)
              * Fp u z θ)
            - ∫ θ in Iθo, (Work.Spaces.w z) ^ 2 * sigE θ
              * (Work.FTS.EllipticEst.cut k z * Work.FTS.EllipticEst.SliceMixedAux.cut ε θ)
              * (U u z θ * Hh u z θ)) := by
    refine setIntegral_congr_fun measurableSet_Ioi (fun z hz => ?_)
    exact integral_sub
      (intOn_theta_cut (k := k) hε hz hFp)
      (intOn_theta_cut (k := k) hε hz (F := fun z θ => U u z θ * Hh u z θ) hUHh)
  have e3 : (∫ z in Set.Ioi 0,
        ((∫ θ in Iθo, (Work.Spaces.w z) ^ 2 * sigE θ
            * (Work.FTS.EllipticEst.cut k z * Work.FTS.EllipticEst.SliceMixedAux.cut ε θ)
            * Fp u z θ)
          - ∫ θ in Iθo, (Work.Spaces.w z) ^ 2 * sigE θ
            * (Work.FTS.EllipticEst.cut k z * Work.FTS.EllipticEst.SliceMixedAux.cut ε θ)
            * (U u z θ * Hh u z θ)))
      = (∫ z in Set.Ioi 0, ∫ θ in Iθo, (Work.Spaces.w z) ^ 2 * sigE θ
            * (Work.FTS.EllipticEst.cut k z * Work.FTS.EllipticEst.SliceMixedAux.cut ε θ)
            * Fp u z θ)
        - (∫ z in Set.Ioi 0, ∫ θ in Iθo, (Work.Spaces.w z) ^ 2 * sigE θ
            * (Work.FTS.EllipticEst.cut k z * Work.FTS.EllipticEst.SliceMixedAux.cut ε θ)
            * (U u z θ * Hh u z θ)) := by
    exact integral_sub (intOn_z_marginal (k := k) hε hFp)
      (intOn_z_marginal (k := k) hε (F := fun z θ => U u z θ * Hh u z θ) hUHh)
  exact e1.trans (e2.trans e3)

/-! ## Converting between the `z`-outer form and the double-integral form -/

/-- Pull a `z`-dependent constant out of the angular integral (unconditional). -/
private theorem zouter_eq_joint {K ρ : ℝ → ℝ} {f : ℝ → ℝ → ℝ} :
    (∫ z in Set.Ioi 0, K z * ∫ θ in Iθo, ρ θ * f z θ)
      = ∫ z in Set.Ioi 0, ∫ θ in Iθo, K z * (ρ θ * f z θ) := by
  refine setIntegral_congr_fun measurableSet_Ioi (fun z _ => ?_)
  rw [MeasureTheory.integral_const_mul]

/-- The statement's left-hand side as a double integral. -/
private theorem convL {u : ℝ → ℝ → ℝ} (k : ℕ) :
    (∫ z in Set.Ioi 0, Work.FTS.EllipticEst.cut k z * (Work.Spaces.w z) ^ 2
        * ∫ θ in Set.Ioo 0 (Real.pi / 2), Work.FTS.EllipticEst.AeI1Fts.sigE θ
            * Work.FTS.EllipticEst.SliceMixedAux.cut (1 / ((k : ℝ) + 1)) θ
            * (Work.FTS.EllipticEst.AeI1Fts.AA u z θ * Work.FTS.EllipticEst.AeI1Fts.BB u z θ
                + Work.FTS.EllipticEst.AngSecond.cw z * Work.FTS.EllipticEst.AeI1Fts.U u z θ
                  * Work.FTS.EllipticEst.AeI1Fts.BB u z θ))
      = ∫ z in Set.Ioi 0, ∫ θ in Set.Ioo 0 (Real.pi / 2), (Work.Spaces.w z) ^ 2
          * sigE θ * (Work.FTS.EllipticEst.cut k z
              * Work.FTS.EllipticEst.SliceMixedAux.cut (1 / ((k : ℝ) + 1)) θ)
          * (AA u z θ * BB u z θ
              + Work.FTS.EllipticEst.AngSecond.cw z * U u z θ * BB u z θ) := by
  refine (zouter_eq_joint (K := fun z => Work.FTS.EllipticEst.cut k z * (Work.Spaces.w z) ^ 2)
    (ρ := fun θ => sigE θ
      * Work.FTS.EllipticEst.SliceMixedAux.cut (1 / ((k : ℝ) + 1)) θ)
    (f := fun z θ => AA u z θ * BB u z θ
      + Work.FTS.EllipticEst.AngSecond.cw z * U u z θ * BB u z θ)).trans ?_
  refine setIntegral_congr_fun measurableSet_Ioi (fun z _ =>
    setIntegral_congr_fun measurableSet_Ioo (fun θ _ => by ring))

/-- The radial integration by parts term as a `z`-outer integral. -/
private theorem convA {u : ℝ → ℝ → ℝ} (k : ℕ) :
    (∫ z in Set.Ioi 0, ∫ θ in Set.Ioo 0 (Real.pi / 2), sigE θ
        * deriv (Work.FTS.EllipticEst.cut k) z
        * (Work.FTS.EllipticEst.SliceMixedAux.cut (1 / ((k : ℝ) + 1)) θ * Fd u z θ))
      = ∫ z in Set.Ioi 0, (z * deriv (Work.FTS.EllipticEst.cut k) z)
          * (Work.Spaces.w z) ^ 2
          * ∫ θ in Set.Ioo 0 (Real.pi / 2), sigE θ
              * Work.FTS.EllipticEst.SliceMixedAux.cut (1 / ((k : ℝ) + 1)) θ
              * (U u z θ * BB u z θ) := by
  calc (∫ z in Set.Ioi 0, ∫ θ in Set.Ioo 0 (Real.pi / 2), sigE θ
        * deriv (Work.FTS.EllipticEst.cut k) z
        * (Work.FTS.EllipticEst.SliceMixedAux.cut (1 / ((k : ℝ) + 1)) θ * Fd u z θ))
      = ∫ z in Set.Ioi 0, ∫ θ in Set.Ioo 0 (Real.pi / 2),
          deriv (Work.FTS.EllipticEst.cut k) z
            * (sigE θ * (Work.FTS.EllipticEst.SliceMixedAux.cut (1 / ((k : ℝ) + 1)) θ
                * Fd u z θ)) := by
        refine setIntegral_congr_fun measurableSet_Ioi (fun z _ =>
          setIntegral_congr_fun measurableSet_Ioo (fun θ _ => by ring))
    _ = ∫ z in Set.Ioi 0, deriv (Work.FTS.EllipticEst.cut k) z
          * ∫ θ in Set.Ioo 0 (Real.pi / 2), sigE θ
              * (Work.FTS.EllipticEst.SliceMixedAux.cut (1 / ((k : ℝ) + 1)) θ
                  * Fd u z θ) :=
        (zouter_eq_joint (K := fun z => deriv (Work.FTS.EllipticEst.cut k) z)
          (ρ := fun θ => sigE θ)
          (f := fun z θ => Work.FTS.EllipticEst.SliceMixedAux.cut (1 / ((k : ℝ) + 1)) θ
            * Fd u z θ)).symm
    _ = ∫ z in Set.Ioi 0, deriv (Work.FTS.EllipticEst.cut k) z
          * (z * (Work.Spaces.w z) ^ 2
            * ∫ θ in Set.Ioo 0 (Real.pi / 2), sigE θ
                * Work.FTS.EllipticEst.SliceMixedAux.cut (1 / ((k : ℝ) + 1)) θ
                * (U u z θ * BB u z θ)) := by
        refine setIntegral_congr_fun measurableSet_Ioi (fun z _ => ?_)
        have hinner : (∫ θ in Set.Ioo 0 (Real.pi / 2), sigE θ
              * (Work.FTS.EllipticEst.SliceMixedAux.cut (1 / ((k : ℝ) + 1)) θ * Fd u z θ))
            = (z * (Work.Spaces.w z) ^ 2) * ∫ θ in Set.Ioo 0 (Real.pi / 2), sigE θ
                * Work.FTS.EllipticEst.SliceMixedAux.cut (1 / ((k : ℝ) + 1)) θ
                * (U u z θ * BB u z θ) := by
          rw [show (∫ θ in Set.Ioo 0 (Real.pi / 2), sigE θ
                * (Work.FTS.EllipticEst.SliceMixedAux.cut (1 / ((k : ℝ) + 1)) θ
                    * Fd u z θ))
              = ∫ θ in Set.Ioo 0 (Real.pi / 2), (z * (Work.Spaces.w z) ^ 2)
                  * (sigE θ
                    * Work.FTS.EllipticEst.SliceMixedAux.cut (1 / ((k : ℝ) + 1)) θ
                    * (U u z θ * BB u z θ)) from
            setIntegral_congr_fun measurableSet_Ioo (fun θ _ => by
              simp only [Fd, U, BB]; ring)]
          rw [MeasureTheory.integral_const_mul]
        rw [hinner]
    _ = ∫ z in Set.Ioi 0, (z * deriv (Work.FTS.EllipticEst.cut k) z)
          * (Work.Spaces.w z) ^ 2
          * ∫ θ in Set.Ioo 0 (Real.pi / 2), sigE θ
              * Work.FTS.EllipticEst.SliceMixedAux.cut (1 / ((k : ℝ) + 1)) θ
              * (U u z θ * BB u z θ) := by
        refine setIntegral_congr_fun measurableSet_Ioi (fun z _ => by ring)

/-- The diagonal angular term as a `z`-outer integral. -/
private theorem convB {u : ℝ → ℝ → ℝ} (k : ℕ) :
    (∫ z in Set.Ioi 0, ∫ θ in Set.Ioo 0 (Real.pi / 2), (Work.Spaces.w z) ^ 2 * sigE θ
        * (Work.FTS.EllipticEst.cut k z
            * Work.FTS.EllipticEst.SliceMixedAux.cut (1 / ((k : ℝ) + 1)) θ)
        * (V u z θ) ^ 2)
      = ∫ z in Set.Ioi 0, Work.FTS.EllipticEst.cut k z * (Work.Spaces.w z) ^ 2
          * ∫ θ in Set.Ioo 0 (Real.pi / 2), sigE θ
              * Work.FTS.EllipticEst.SliceMixedAux.cut (1 / ((k : ℝ) + 1)) θ
              * (V u z θ) ^ 2 := by
  have hstep : (∫ z in Set.Ioi 0, ∫ θ in Set.Ioo 0 (Real.pi / 2), (Work.Spaces.w z) ^ 2 * sigE θ
        * (Work.FTS.EllipticEst.cut k z
            * Work.FTS.EllipticEst.SliceMixedAux.cut (1 / ((k : ℝ) + 1)) θ)
        * (V u z θ) ^ 2)
      = ∫ z in Set.Ioi 0, ∫ θ in Set.Ioo 0 (Real.pi / 2),
          (Work.FTS.EllipticEst.cut k z * (Work.Spaces.w z) ^ 2)
            * ((sigE θ * Work.FTS.EllipticEst.SliceMixedAux.cut (1 / ((k : ℝ) + 1)) θ)
                * (V u z θ) ^ 2) := by
    refine setIntegral_congr_fun measurableSet_Ioi (fun z _ =>
      setIntegral_congr_fun measurableSet_Ioo (fun θ _ => by ring))
  rw [hstep]
  exact (zouter_eq_joint
    (K := fun z => Work.FTS.EllipticEst.cut k z * (Work.Spaces.w z) ^ 2)
    (ρ := fun θ => sigE θ
      * Work.FTS.EllipticEst.SliceMixedAux.cut (1 / ((k : ℝ) + 1)) θ)
    (f := fun z θ => (V u z θ) ^ 2)).symm

/-- The cross angular term as a `z`-outer integral. -/
private theorem convC {u : ℝ → ℝ → ℝ} (k : ℕ) :
    (∫ z in Set.Ioi 0, ∫ θ in Set.Ioo 0 (Real.pi / 2), (Work.Spaces.w z) ^ 2 * sig1 θ
        * (Work.FTS.EllipticEst.cut k z
            * Work.FTS.EllipticEst.SliceMixedAux.cut (1 / ((k : ℝ) + 1)) θ)
        * (U u z θ * V u z θ * Real.cos (2 * θ)))
      = ∫ z in Set.Ioi 0, Work.FTS.EllipticEst.cut k z * (Work.Spaces.w z) ^ 2
          * ∫ θ in Set.Ioo 0 (Real.pi / 2), sig1 θ
              * Work.FTS.EllipticEst.SliceMixedAux.cut (1 / ((k : ℝ) + 1)) θ
              * (U u z θ * V u z θ * Real.cos (2 * θ)) := by
  have hstep : (∫ z in Set.Ioi 0, ∫ θ in Set.Ioo 0 (Real.pi / 2), (Work.Spaces.w z) ^ 2 * sig1 θ
        * (Work.FTS.EllipticEst.cut k z
            * Work.FTS.EllipticEst.SliceMixedAux.cut (1 / ((k : ℝ) + 1)) θ)
        * (U u z θ * V u z θ * Real.cos (2 * θ)))
      = ∫ z in Set.Ioi 0, ∫ θ in Set.Ioo 0 (Real.pi / 2),
          (Work.FTS.EllipticEst.cut k z * (Work.Spaces.w z) ^ 2)
            * ((sig1 θ * Work.FTS.EllipticEst.SliceMixedAux.cut (1 / ((k : ℝ) + 1)) θ)
                * (U u z θ * V u z θ * Real.cos (2 * θ))) := by
    refine setIntegral_congr_fun measurableSet_Ioi (fun z _ =>
      setIntegral_congr_fun measurableSet_Ioo (fun θ _ => by ring))
  rw [hstep]
  exact (zouter_eq_joint
    (K := fun z => Work.FTS.EllipticEst.cut k z * (Work.Spaces.w z) ^ 2)
    (ρ := fun θ => sig1 θ
      * Work.FTS.EllipticEst.SliceMixedAux.cut (1 / ((k : ℝ) + 1)) θ)
    (f := fun z θ => U u z θ * V u z θ * Real.cos (2 * θ))).symm

/-- The angular cut-off derivative term as a `z`-outer integral. -/
private theorem convD {u : ℝ → ℝ → ℝ} (k : ℕ) :
    (∫ z in Set.Ioi 0, ∫ θ in Set.Ioo 0 (Real.pi / 2), (Work.Spaces.w z) ^ 2 * sigE θ
        * (Work.FTS.EllipticEst.cut k z
            * deriv (Work.FTS.EllipticEst.SliceMixedAux.cut (1 / ((k : ℝ) + 1))) θ)
        * (U u z θ * V u z θ))
      = ∫ z in Set.Ioi 0, Work.FTS.EllipticEst.cut k z * (Work.Spaces.w z) ^ 2
          * ∫ θ in Set.Ioo 0 (Real.pi / 2), sigE θ
              * deriv (Work.FTS.EllipticEst.SliceMixedAux.cut (1 / ((k : ℝ) + 1))) θ
              * (U u z θ * V u z θ) := by
  have hstep : (∫ z in Set.Ioi 0, ∫ θ in Set.Ioo 0 (Real.pi / 2), (Work.Spaces.w z) ^ 2 * sigE θ
        * (Work.FTS.EllipticEst.cut k z
            * deriv (Work.FTS.EllipticEst.SliceMixedAux.cut (1 / ((k : ℝ) + 1))) θ)
        * (U u z θ * V u z θ))
      = ∫ z in Set.Ioi 0, ∫ θ in Set.Ioo 0 (Real.pi / 2),
          (Work.FTS.EllipticEst.cut k z * (Work.Spaces.w z) ^ 2)
            * ((sigE θ
                * deriv (Work.FTS.EllipticEst.SliceMixedAux.cut (1 / ((k : ℝ) + 1))) θ)
                * (U u z θ * V u z θ)) := by
    refine setIntegral_congr_fun measurableSet_Ioi (fun z _ =>
      setIntegral_congr_fun measurableSet_Ioo (fun θ _ => by ring))
  rw [hstep]
  exact (zouter_eq_joint
    (K := fun z => Work.FTS.EllipticEst.cut k z * (Work.Spaces.w z) ^ 2)
    (ρ := fun θ => sigE θ
      * deriv (Work.FTS.EllipticEst.SliceMixedAux.cut (1 / ((k : ℝ) + 1))) θ)
    (f := fun z θ => U u z θ * V u z θ)).symm

/-! ## The target -/

theorem trunc_identity {α : ℝ} {u G : ℝ → ℝ → ℝ}
    (h : Work.FTS.EllipticEst.H2W.Ae.AeData α u G) (k : ℕ) :
    (∫ z in Set.Ioi 0, Work.FTS.EllipticEst.cut k z * (Work.Spaces.w z) ^ 2
        * ∫ θ in Set.Ioo 0 (Real.pi / 2), Work.FTS.EllipticEst.AeI1Fts.sigE θ
            * Work.FTS.EllipticEst.SliceMixedAux.cut (1 / ((k : ℝ) + 1)) θ
            * (Work.FTS.EllipticEst.AeI1Fts.AA u z θ * Work.FTS.EllipticEst.AeI1Fts.BB u z θ
                + Work.FTS.EllipticEst.AngSecond.cw z * Work.FTS.EllipticEst.AeI1Fts.U u z θ
                  * Work.FTS.EllipticEst.AeI1Fts.BB u z θ))
      = - (∫ z in Set.Ioi 0, (z * deriv (Work.FTS.EllipticEst.cut k) z) * (Work.Spaces.w z) ^ 2
            * ∫ θ in Set.Ioo 0 (Real.pi / 2), Work.FTS.EllipticEst.AeI1Fts.sigE θ
              * Work.FTS.EllipticEst.SliceMixedAux.cut (1 / ((k : ℝ) + 1)) θ
              * (Work.FTS.EllipticEst.AeI1Fts.U u z θ * Work.FTS.EllipticEst.AeI1Fts.BB u z θ))
        + (∫ z in Set.Ioi 0, Work.FTS.EllipticEst.cut k z * (Work.Spaces.w z) ^ 2
            * ∫ θ in Set.Ioo 0 (Real.pi / 2), Work.FTS.EllipticEst.AeI1Fts.sigE θ
              * Work.FTS.EllipticEst.SliceMixedAux.cut (1 / ((k : ℝ) + 1)) θ
              * (Work.FTS.EllipticEst.AeI1Fts.V u z θ) ^ 2)
        - 2 * Work.Spaces.eta * (∫ z in Set.Ioi 0, Work.FTS.EllipticEst.cut k z
            * (Work.Spaces.w z) ^ 2 * ∫ θ in Set.Ioo 0 (Real.pi / 2),
              Work.FTS.EllipticEst.AeI1Fts.sig1 θ
                * Work.FTS.EllipticEst.SliceMixedAux.cut (1 / ((k : ℝ) + 1)) θ
                * (Work.FTS.EllipticEst.AeI1Fts.U u z θ * Work.FTS.EllipticEst.AeI1Fts.V u z θ
                    * Real.cos (2 * θ)))
        + (∫ z in Set.Ioi 0, Work.FTS.EllipticEst.cut k z * (Work.Spaces.w z) ^ 2
            * ∫ θ in Set.Ioo 0 (Real.pi / 2), Work.FTS.EllipticEst.AeI1Fts.sigE θ
              * deriv (Work.FTS.EllipticEst.SliceMixedAux.cut (1 / ((k : ℝ) + 1))) θ
              * (Work.FTS.EllipticEst.AeI1Fts.U u z θ * Work.FTS.EllipticEst.AeI1Fts.V u z θ)) := by
  have hS : Work.FTS.EllipticEst.SmoothOpen u :=
    Work.FTS.EllipticEst.smoothOpen_of_forall (fun n => h.smooth n)
  have hε : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
  have hsplit := split_joint hS k (ε := 1 / ((k : ℝ) + 1)) hε
  have hzib := Work.FTS.EllipticEst.I1Ae.zibpChain h k hε
  have hth := Work.FTS.EllipticEst.I1Ae.thetaChain h k hε
  rw [convL k, hsplit, hzib, hth, convA k, convB k, convC k, convD k]
  ring

end

end Work.FTS.EllipticEst.AeI1Fts
