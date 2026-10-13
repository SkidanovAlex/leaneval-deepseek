import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.EllipticEst.AeI1Fts.Defs
import Submission.Work.FTS.EllipticEst.SliceMixedAux.smoothCutoffIoo
import Submission.Work.FTS.EllipticEst.H2W.I1cb.ftc_open_interval
import Submission.Work.FTS.EllipticEst.AeI1Fts.identity_defs
import Submission.Work.FTS.EllipticEst.TanTheta.slice_ident

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The angular integration by parts of the `I₁` chain against the cut-off `χ_ε`

Target: `Work.FTS.EllipticEst.AeI1Fts.slice_theta_ibp_cut`.  For a datum `u` smooth on the open
quadrant, `z > 0` and `ε > 0`,

```
∫_{0<θ<π/2} σ·χ_ε·(U·Hh) = -∫ σ·χ_ε·V² + 2η·∫ σ₁·χ_ε·(U·V·cos 2θ) - ∫ σ·χ_ε'·(U·V),
```

where `U = z∂_zu`, `V = z∂_z∂_θu`, `Hh = z∂_z∂_θθu`, `σ = sin(2θ)^{-η}`,
`σ₁ = sin(2θ)^{-1-η}`, `η = 99/100` and `χ_ε = SliceMixedAux.cut ε` is the smooth two-plateau
cut-off of `SliceMixedAux.smoothCutoffIoo`.

The proof is the integration by parts of the pointwise identity
`∂_θ(U·V·σ) = V²σ + U·Hh·σ - 2η·U·V·cos(2θ)·σ₁` (`hasDerivAt_theta_ident`) against `χ_ε`:
the antiderivative `G = χ_ε·(U·V·σ)` vanishes identically near both endpoints (because `χ_ε` does),
so `∫ G' = 0`, and expanding `G' = χ_ε'·(U·V·σ) + χ_ε·(V²σ + U·Hh·σ - 2η U·V cos(2θ)σ₁)` and
splitting the integral gives the claim.
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.AeI1Fts

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-! ## Continuity of the two angular weights on the open interval -/

private theorem sigE_continuousOn_Iθo : ContinuousOn sigE (Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
  have hsin : ContinuousOn (fun θ : ℝ => Real.sin (2 * θ)) (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    (Real.continuous_sin.comp (continuous_const.mul continuous_id)).continuousOn
  refine (hsin.rpow_const (p := -(Work.Spaces.eta)) ?_).congr ?_
  · intro θ hθ
    left
    exact ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1])
      (by linarith [hθ.2, Real.pi_pos]))
  · intro θ _
    rfl

private theorem sig1_continuousOn_Iθo : ContinuousOn sig1 (Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
  have hsin : ContinuousOn (fun θ : ℝ => Real.sin (2 * θ)) (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    (Real.continuous_sin.comp (continuous_const.mul continuous_id)).continuousOn
  refine (hsin.rpow_const (p := -(1 + Work.Spaces.eta)) ?_).congr ?_
  · intro θ hθ
    left
    exact ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1])
      (by linarith [hθ.2, Real.pi_pos]))
  · intro θ _
    rfl

/-! ## Integrability on `(0,π/2)` of a function continuous on a compact subinterval and
vanishing outside it -/

private theorem integrableOn_Ioo_of_Icc_support {f : ℝ → ℝ} {c d : ℝ}
    (hcont : ContinuousOn f (Set.Icc c d))
    (hzero : ∀ x ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), x ∉ Set.Icc c d → f x = 0) :
    IntegrableOn f (Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
  have hInd : Integrable ((Set.Icc c d).indicator f) volume :=
    (integrable_indicator_iff measurableSet_Icc).mpr (hcont.integrableOn_compact isCompact_Icc)
  refine (hInd.mono_measure Measure.restrict_le_self).congr ?_
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with x hx
  by_cases hxd : x ∈ Set.Icc c d
  · rw [Set.indicator_of_mem hxd]
  · rw [Set.indicator_of_notMem hxd, hzero x hx hxd]

/-! ## Vanishing of the derivative of the cut-off outside its plateau band -/

private theorem cut_deriv_eq_zero_of_lt {ε θ : ℝ} (hε : 0 < ε) (h : θ < ε / 2) :
    deriv (SliceMixedAux.cut ε) θ = 0 := by
  have hEq : (fun y : ℝ => SliceMixedAux.cut ε y) =ᶠ[𝓝 θ] (fun _ => (0 : ℝ)) := by
    filter_upwards [isOpen_Iio.mem_nhds h] with y hy
    exact SliceMixedAux.cut_eq_zero_low hε (le_of_lt hy)
  simpa using hEq.deriv_eq

private theorem cut_deriv_eq_zero_of_gt {ε θ : ℝ} (hε : 0 < ε)
    (h : Real.pi / 2 - ε / 2 < θ) : deriv (SliceMixedAux.cut ε) θ = 0 := by
  have hEq : (fun y : ℝ => SliceMixedAux.cut ε y) =ᶠ[𝓝 θ] (fun _ => (0 : ℝ)) := by
    filter_upwards [isOpen_Ioi.mem_nhds h] with y hy
    exact SliceMixedAux.cut_eq_zero_high hε (le_of_lt hy)
  simpa using hEq.deriv_eq

/-! ## The main lemma -/

theorem slice_theta_ibp_cut {u : ℝ → ℝ → ℝ} (hS : Work.FTS.EllipticEst.SmoothOpen u)
    {z ε : ℝ} (hz : 0 < z) (hε : 0 < ε) :
    (∫ θ in Set.Ioo 0 (Real.pi / 2),
        Work.FTS.EllipticEst.AeI1Fts.sigE θ * Work.FTS.EllipticEst.SliceMixedAux.cut ε θ
          * (Work.FTS.EllipticEst.AeI1Fts.U u z θ * Work.FTS.EllipticEst.AeI1Fts.Hh u z θ))
      = - (∫ θ in Set.Ioo 0 (Real.pi / 2),
            Work.FTS.EllipticEst.AeI1Fts.sigE θ * Work.FTS.EllipticEst.SliceMixedAux.cut ε θ
              * (Work.FTS.EllipticEst.AeI1Fts.V u z θ) ^ 2)
        + 2 * Work.Spaces.eta * (∫ θ in Set.Ioo 0 (Real.pi / 2),
            Work.FTS.EllipticEst.AeI1Fts.sig1 θ * Work.FTS.EllipticEst.SliceMixedAux.cut ε θ
              * (Work.FTS.EllipticEst.AeI1Fts.U u z θ * Work.FTS.EllipticEst.AeI1Fts.V u z θ
                  * Real.cos (2 * θ)))
        - (∫ θ in Set.Ioo 0 (Real.pi / 2),
            Work.FTS.EllipticEst.AeI1Fts.sigE θ
              * deriv (Work.FTS.EllipticEst.SliceMixedAux.cut ε) θ
              * (Work.FTS.EllipticEst.AeI1Fts.U u z θ * Work.FTS.EllipticEst.AeI1Fts.V u z θ)) := by
  have hπ : (0 : ℝ) < Real.pi / 2 := by linarith [Real.pi_pos]
  set a : ℝ := ε / 2 with ha
  set b : ℝ := Real.pi / 2 - ε / 2 with hb
  have ha_pos : 0 < a := by rw [ha]; linarith
  have hb_lt : b < Real.pi / 2 := by rw [hb]; linarith
  have hsub : Set.Icc a b ⊆ Set.Ioo (0 : ℝ) (Real.pi / 2) := fun x hx =>
    ⟨lt_of_lt_of_le ha_pos hx.1, lt_of_le_of_lt hx.2 hb_lt⟩
  -- continuity of the angular factors on the open interval
  have hUc : ContinuousOn (fun θ => U u z θ) (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    (contDiffOn_slice_U hS hz).continuousOn
  have hVc : ContinuousOn (fun θ => V u z θ) (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    (contDiffOn_slice_V hS hz).continuousOn
  have hHc : ContinuousOn (fun θ => Hh u z θ) (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    ((smoothOpen_Hh hS).curry_θ hz).continuousOn
  have hcutc : ContinuousOn (SliceMixedAux.cut ε) (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    ((SliceMixedAux.cut_contDiff ε).continuous).continuousOn
  have hdc : Continuous (deriv (SliceMixedAux.cut ε)) :=
    (SliceMixedAux.cut_contDiff ε).continuous_deriv (by norm_num)
  have hcosc : ContinuousOn (fun θ : ℝ => Real.cos (2 * θ)) (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    (Real.continuous_cos.comp (continuous_const.mul continuous_id)).continuousOn
  -- the cut-off and its derivative vanish off `[a,b]`
  have hsupp : ∀ x ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), x ∉ Set.Icc a b →
      SliceMixedAux.cut ε x = 0 ∧ deriv (SliceMixedAux.cut ε) x = 0 := by
    intro x _ hxnot
    rw [Set.mem_Icc, not_and_or, not_le, not_le] at hxnot
    rcases hxnot with hlt | hgt
    · exact ⟨SliceMixedAux.cut_eq_zero_low hε (le_of_lt hlt), cut_deriv_eq_zero_of_lt hε hlt⟩
    · exact ⟨SliceMixedAux.cut_eq_zero_high hε (le_of_lt hgt), cut_deriv_eq_zero_of_gt hε hgt⟩
  -- the four integrands of the target
  let T1 : ℝ → ℝ := fun θ => sigE θ * deriv (SliceMixedAux.cut ε) θ * (U u z θ * V u z θ)
  let T2 : ℝ → ℝ := fun θ => sigE θ * SliceMixedAux.cut ε θ * (V u z θ) ^ 2
  let T3 : ℝ → ℝ := fun θ => sigE θ * SliceMixedAux.cut ε θ * (U u z θ * Hh u z θ)
  let T4 : ℝ → ℝ := fun θ => sig1 θ * SliceMixedAux.cut ε θ
      * (U u z θ * V u z θ * Real.cos (2 * θ))
  have hI1 : IntegrableOn T1 (Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
    simp only [T1]
    refine integrableOn_Ioo_of_Icc_support (c := a) (d := b) ?_ ?_
    · exact ((sigE_continuousOn_Iθo.mono hsub).mul (hdc.continuousOn.mono hsub)).mul
        ((hUc.mono hsub).mul (hVc.mono hsub))
    · intro x hx hxnot
      obtain ⟨-, hd0⟩ := hsupp x hx hxnot
      rw [hd0]; ring
  have hI2 : IntegrableOn T2 (Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
    simp only [T2]
    refine integrableOn_Ioo_of_Icc_support (c := a) (d := b) ?_ ?_
    · exact ((sigE_continuousOn_Iθo.mono hsub).mul (hcutc.mono hsub)).mul
        ((hVc.mono hsub).pow 2)
    · intro x hx hxnot
      obtain ⟨hc0, -⟩ := hsupp x hx hxnot
      rw [hc0]; ring
  have hI3 : IntegrableOn T3 (Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
    simp only [T3]
    refine integrableOn_Ioo_of_Icc_support (c := a) (d := b) ?_ ?_
    · exact ((sigE_continuousOn_Iθo.mono hsub).mul (hcutc.mono hsub)).mul
        ((hUc.mono hsub).mul (hHc.mono hsub))
    · intro x hx hxnot
      obtain ⟨hc0, -⟩ := hsupp x hx hxnot
      rw [hc0]; ring
  have hI4 : IntegrableOn T4 (Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
    simp only [T4]
    refine integrableOn_Ioo_of_Icc_support (c := a) (d := b) ?_ ?_
    · exact ((sig1_continuousOn_Iθo.mono hsub).mul (hcutc.mono hsub)).mul
        (((hUc.mono hsub).mul (hVc.mono hsub)).mul (hcosc.mono hsub))
    · intro x hx hxnot
      obtain ⟨hc0, -⟩ := hsupp x hx hxnot
      rw [hc0]; ring
  -- the antiderivative and its derivative
  let G : ℝ → ℝ := fun θ => SliceMixedAux.cut ε θ * (U u z θ * V u z θ * sigE θ)
  let G' : ℝ → ℝ := fun θ => T1 θ + T2 θ + T3 θ - 2 * Work.Spaces.eta * T4 θ
  let S : ℝ → ℝ := fun x => T1 x + T2 x + T3 x
  let S2 : ℝ → ℝ := fun x => T1 x + T2 x
  let T4c : ℝ → ℝ := fun x => 2 * Work.Spaces.eta * T4 x
  have hSint : IntegrableOn S (Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
    simp only [S]
    exact (hI1.add hI2).add hI3
  have hS2 : IntegrableOn S2 (Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
    simp only [S2]
    exact hI1.add hI2
  have hT4c : IntegrableOn T4c (Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
    simp only [T4c]
    exact Integrable.const_mul hI4 (2 * Work.Spaces.eta)
  have hG'S : G' = fun x => S x - T4c x := by
    funext x
    simp only [G', S, T4c]
    try ring
  have hderiv : ∀ x ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), HasDerivAt G (G' x) x := by
    intro x hx
    have hcut : HasDerivAt (SliceMixedAux.cut ε) (deriv (SliceMixedAux.cut ε) x) x :=
      (((SliceMixedAux.cut_contDiff ε).differentiable (by norm_num)).differentiableAt).hasDerivAt
    have hth := hasDerivAt_theta_ident hS hz hx
    have hprod := hcut.mul hth
    refine hprod.congr_deriv ?_
    simp only [G', T1, T2, T3, T4]
    ring
  have hint : IntegrableOn G' (Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
    rw [hG'S]
    exact hSint.sub hT4c
  have hbot : Tendsto G (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    refine Tendsto.congr' ?_ tendsto_const_nhds
    filter_upwards [nhdsWithin_le_nhds
      (isOpen_Iio.mem_nhds (show (0 : ℝ) < ε / 2 by linarith))] with x hx
    simp only [G]
    rw [SliceMixedAux.cut_eq_zero_low hε (le_of_lt hx), zero_mul]
  have htop : Tendsto G (𝓝[<] (Real.pi / 2)) (𝓝 0) := by
    refine Tendsto.congr' ?_ tendsto_const_nhds
    filter_upwards [nhdsWithin_le_nhds
      (isOpen_Ioi.mem_nhds (show Real.pi / 2 - ε / 2 < Real.pi / 2 by linarith))]
      with x hx
    simp only [G]
    rw [SliceMixedAux.cut_eq_zero_high hε (le_of_lt hx), zero_mul]
  have hFTC := Work.FTS.EllipticEst.TanTheta.integral_Ioo_eq_sub_of_tendsto hπ
    (G := G) (G' := G') hderiv hint hbot htop
  have hsplit : (∫ x in Set.Ioo (0 : ℝ) (Real.pi / 2), G' x)
      = (∫ x in Set.Ioo (0 : ℝ) (Real.pi / 2), S x)
        - (∫ x in Set.Ioo (0 : ℝ) (Real.pi / 2), T4c x) := by
    rw [hG'S]
    exact integral_sub hSint hT4c
  have hsplit2 : (∫ x in Set.Ioo (0 : ℝ) (Real.pi / 2), S x)
      = (∫ x in Set.Ioo (0 : ℝ) (Real.pi / 2), S2 x)
        + (∫ x in Set.Ioo (0 : ℝ) (Real.pi / 2), T3 x) := by
    rw [show S = fun x => S2 x + T3 x from by
      funext x
      simp only [S, S2]
      try ring]
    exact integral_add hS2 hI3
  have hsplit3 : (∫ x in Set.Ioo (0 : ℝ) (Real.pi / 2), S2 x)
      = (∫ x in Set.Ioo (0 : ℝ) (Real.pi / 2), T1 x)
        + (∫ x in Set.Ioo (0 : ℝ) (Real.pi / 2), T2 x) := by
    rw [show S2 = fun x => T1 x + T2 x from by
      funext x
      simp only [S2]]
    exact integral_add hI1 hI2
  have hT4int : (∫ x in Set.Ioo (0 : ℝ) (Real.pi / 2), T4c x)
      = 2 * Work.Spaces.eta * (∫ x in Set.Ioo (0 : ℝ) (Real.pi / 2), T4 x) := by
    rw [show T4c = fun x => 2 * Work.Spaces.eta * T4 x from by
      funext x
      simp only [T4c]]
    exact integral_const_mul (2 * Work.Spaces.eta) T4
  have h0 : (∫ x in Set.Ioo (0 : ℝ) (Real.pi / 2), G' x) = 0 := by
    rw [hFTC]
    ring
  have hkey : (∫ x in Set.Ioo (0 : ℝ) (Real.pi / 2), T1 x)
      + (∫ x in Set.Ioo (0 : ℝ) (Real.pi / 2), T2 x)
      + (∫ x in Set.Ioo (0 : ℝ) (Real.pi / 2), T3 x)
      - 2 * Work.Spaces.eta * (∫ x in Set.Ioo (0 : ℝ) (Real.pi / 2), T4 x) = 0 := by
    rw [hsplit, hsplit2, hsplit3, hT4int] at h0
    linarith
  simp only [T1, T2, T3, T4] at hkey ⊢
  linarith

end Work.FTS.EllipticEst.AeI1Fts
