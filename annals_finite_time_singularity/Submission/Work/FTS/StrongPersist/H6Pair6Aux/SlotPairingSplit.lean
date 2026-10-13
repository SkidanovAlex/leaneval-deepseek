import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.StrongPersist.Clauses
import Submission.Work.FTS.TransportS.Slots
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T3Row
import Submission.Work.FTS.CoercivityFix.Assembly.H1IP_core_Q
import Submission.Work.Coercivity.wip_add_of_PairHonest
import Submission.Work.FTS.CoercivityFix.StepAssembly.H1IP_congr_qd
import Submission.Work.FTS.IPGen.OpenBasic
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.FTS.H2.Whz_Wm_sq

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.H6Pair6Aux

/-! ## Splitting the elementary slot pairing in its first argument

`slotPairing ρ a b u v = ∫_z ∫_θ ρ · D_z^bD_θ^a u · D_z^bD_θ^a v` is the elementary
`ρ`-weighted pairing of the two slots `D_z^bD_θ^a u`, `D_z^bD_θ^a v`.  It is a `Work.Coercivity.wip`
in disguise (`slotPairing_eq_wip`), so additivity in the first argument reduces to the
additivity of `wip` on honest pairings (`wip_add_of_PairHonest`).

The two ingredients are the ones already used by `H1IP_add_weak` for the `ℋ¹`-pairing:

* the *pointwise* additivity of `D_z^bD_θ^a` on the open quadrant,
  `Work.FTS.CoercivityFix.Assembly.BlocksAdd`, which for `SmoothOpen` data is
  `Work.FTS.IPGen.BlocksAdd_of_smoothOpen` — this gives the `wip`-congruence `wip_congr_Qd`;
* the *honesty* of each of the two pairing integrands on the closed quadrant, which is
  `I2Mem_of_dominated` applied to the AM–GM domination of
  `|D_z^bD_θ^a u · D_z^bD_θ^a v · ρ|` by `(HkIntegrand α 6 u + HkIntegrand α 6 v)/2`.

For the second point, both slot factors are `ℋ⁶`-blocks (`sq_le_HkIntegrand_z` for the
`D_z`-only slots `a = 0`, `sq_le_HkIntegrand_mixed` for the mixed slots `a ≥ 1`) and each leaf
weight `ρ` is dominated by the corresponding slot weight `slotW α a`
(`Work.FTS.TransportS.IsLeafW_le`), whose square root is precisely the block weight
`Whz` resp. `Wm`. -/

/-- `slotPairing` is the `wip` of the two slots (the two integrands differ only by the
association of the product). -/
theorem slotPairing_eq_wip (ρ : ℝ → ℝ → ℝ) (a b : ℕ) (u v : ℝ → ℝ → ℝ) :
    Work.FTS.TransportS.slotPairing ρ a b u v
      = Work.Coercivity.wip ρ (Work.Spaces.mixed b a u) (Work.Spaces.mixed b a v) := by
  unfold Work.FTS.TransportS.slotPairing Work.Coercivity.wip
  refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
  refine integral_congr_ae (Filter.Eventually.of_forall fun θ => ?_)
  ring

/-! ## The elementary pointwise bounds -/

/-- `|X|·|Y|·W² = |X·W|·|Y·W|` for every real `W` (no positivity needed). -/
private lemma abs_mul_abs_mul_sq (X Y W : ℝ) : |X| * |Y| * W ^ 2 = |X * W| * |Y * W| := by
  rw [abs_mul, abs_mul, ← sq_abs]
  ring

/-- **The pointwise domination of one slot-pairing integrand** at level six: for every leaf
weight `ρ` of the slot `a`, every `z ≥ 0` and every interior angle,
`|D_z^bD_θ^a U · D_z^bD_θ^a F · ρ| ≤ (HkIntegrand α 6 U + HkIntegrand α 6 F)/2`.

The proof is AM–GM after writing the integrand through the *block* weight of the slot
(`Whz` for `a = 0`, `Wm` for `a ≥ 1`): `IsLeafW_le` bounds `ρ` by `slotW α a`, which is the
square of that block weight, and each squared block is a summand of the `ℋ⁶`-integrand
(`sq_le_HkIntegrand_z` / `sq_le_HkIntegrand_mixed`).  At `z = 0` the weight `ρ` vanishes. -/
private lemma leaf_point_le {α : ℝ} (hα : 0 < α) {a b : ℕ} (hab : a + b ≤ 6)
    {ρ : ℝ → ℝ → ℝ} (hleaf : Work.FTS.TransportS.IsLeafW α a ρ)
    {U F : ℝ → ℝ → ℝ} (z θ : ℝ) (hz : 0 ≤ z) (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    |Work.Spaces.mixed b a U z θ * Work.Spaces.mixed b a F z θ * ρ z θ|
      ≤ (Work.Spaces.HkIntegrand α 6 U z θ + Work.Spaces.HkIntegrand α 6 F z θ) / 2 := by
  rcases eq_or_lt_of_le hz with h0 | hpos
  · subst h0
    have hρ : ρ 0 θ = 0 := by
      rcases hleaf with rfl | rfl | ⟨_, rfl⟩ <;>
        simp [Work.FTS.TransportS.leafEta, Work.FTS.TransportS.leafOne,
          Work.FTS.TransportS.leafGam, Work.Spaces.w]
    rw [hρ, mul_zero, abs_zero]
    exact div_nonneg (add_nonneg (Work.Spaces.HkIntegrand_nonneg α 6 U 0 θ)
      (Work.Spaces.HkIntegrand_nonneg α 6 F 0 θ)) (by norm_num)
  · obtain ⟨hρ0, hρle⟩ := Work.FTS.TransportS.IsLeafW_le α hα hleaf
    have hρnn : 0 ≤ ρ z θ := hρ0 z θ hpos hθ.1 hθ.2
    have hle : ρ z θ ≤ Work.FTS.TransportS.slotW α a z θ := hρle z θ hpos hθ.1 hθ.2
    have hAB : |Work.Spaces.mixed b a U z θ * Work.Spaces.mixed b a F z θ * ρ z θ|
        = |Work.Spaces.mixed b a U z θ| * |Work.Spaces.mixed b a F z θ| * ρ z θ := by
      rw [abs_mul, abs_mul, abs_of_nonneg hρnn]
    rw [hAB]
    have step : |Work.Spaces.mixed b a U z θ| * |Work.Spaces.mixed b a F z θ| * ρ z θ
        ≤ |Work.Spaces.mixed b a U z θ| * |Work.Spaces.mixed b a F z θ|
            * Work.FTS.TransportS.slotW α a z θ :=
      mul_le_mul_of_nonneg_left hle (mul_nonneg (abs_nonneg _) (abs_nonneg _))
    refine le_trans step ?_
    rcases eq_or_ne a 0 with ha0 | ha0
    · subst ha0
      have hsw : Work.FTS.TransportS.slotW α 0 z θ = (Work.FTS.H2.Whz z θ) ^ 2 := by
        simp [Work.FTS.TransportS.slotW_zero]
      rw [hsw, abs_mul_abs_mul_sq, Work.Spaces.mixed_zero_right]
      have h1 : (Work.Spaces.DzIter b U z θ * Work.FTS.H2.Whz z θ) ^ 2
          ≤ Work.Spaces.HkIntegrand α 6 U z θ := by
        simpa only [Work.FTS.H2.Whz_eq] using
          Work.Spaces.sq_le_HkIntegrand_z α 6 U z θ b (by omega)
      have h2 : (Work.Spaces.DzIter b F z θ * Work.FTS.H2.Whz z θ) ^ 2
          ≤ Work.Spaces.HkIntegrand α 6 F z θ := by
        simpa only [Work.FTS.H2.Whz_eq] using
          Work.Spaces.sq_le_HkIntegrand_z α 6 F z θ b (by omega)
      calc |Work.Spaces.DzIter b U z θ * Work.FTS.H2.Whz z θ|
              * |Work.Spaces.DzIter b F z θ * Work.FTS.H2.Whz z θ|
          ≤ ((Work.Spaces.DzIter b U z θ * Work.FTS.H2.Whz z θ) ^ 2
              + (Work.Spaces.DzIter b F z θ * Work.FTS.H2.Whz z θ) ^ 2) / 2 :=
            Work.FTS.CoercivityFix.Assembly.abs_mul_abs_le_half _ _
        _ ≤ (Work.Spaces.HkIntegrand α 6 U z θ + Work.Spaces.HkIntegrand α 6 F z θ) / 2 := by
            linarith
    · have ha1 : 1 ≤ a := Nat.one_le_iff_ne_zero.mpr ha0
      have hsw : Work.FTS.TransportS.slotW α a z θ = (Work.FTS.H2.Wm α z θ) ^ 2 := by
        simp [Work.FTS.TransportS.slotW_of_pos' α ha1]
      rw [hsw, abs_mul_abs_mul_sq]
      have h1 : (Work.Spaces.mixed b a U z θ * Work.FTS.H2.Wm α z θ) ^ 2
          ≤ Work.Spaces.HkIntegrand α 6 U z θ := by
        simpa only [Work.FTS.H2.Wm_eq] using
          Work.Spaces.sq_le_HkIntegrand_mixed α 6 U z θ a b ha1 hab
      have h2 : (Work.Spaces.mixed b a F z θ * Work.FTS.H2.Wm α z θ) ^ 2
          ≤ Work.Spaces.HkIntegrand α 6 F z θ := by
        simpa only [Work.FTS.H2.Wm_eq] using
          Work.Spaces.sq_le_HkIntegrand_mixed α 6 F z θ a b ha1 hab
      calc |Work.Spaces.mixed b a U z θ * Work.FTS.H2.Wm α z θ|
              * |Work.Spaces.mixed b a F z θ * Work.FTS.H2.Wm α z θ|
          ≤ ((Work.Spaces.mixed b a U z θ * Work.FTS.H2.Wm α z θ) ^ 2
              + (Work.Spaces.mixed b a F z θ * Work.FTS.H2.Wm α z θ) ^ 2) / 2 :=
            Work.FTS.CoercivityFix.Assembly.abs_mul_abs_le_half _ _
        _ ≤ (Work.Spaces.HkIntegrand α 6 U z θ + Work.Spaces.HkIntegrand α 6 F z θ) / 2 := by
            linarith

/-- Honesty of the level-six AM–GM majorant `(HkIntegrand α 6 U + HkIntegrand α 6 F)/2`
(the level-six instance of `Assembly.I2Mem_HkPairDom`). -/
private theorem I2Mem_HkPairDom6 (α : ℝ) {U F : ℝ → ℝ → ℝ}
    (hU : Work.Spaces.HkMem α 6 U) (hF : Work.Spaces.HkMem α 6 F) :
    Work.Coercivity.I2Mem (fun z θ => (Work.Spaces.HkIntegrand α 6 U z θ
      + Work.Spaces.HkIntegrand α 6 F z θ) / 2) := by
  refine ⟨fun z hz => (hU.1 z hz |>.add (hF.1 z hz)).div_const 2, ?_⟩
  refine (hU.2.div_const 2 |>.add (hF.2.div_const 2)).congr ?_
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ici] with z hz
  simp only [Pi.add_apply]
  rw [MeasureTheory.integral_div, MeasureTheory.integral_add (hU.1 z hz) (hF.1 z hz)]
  ring

/-- **Honesty of the leaf-weighted slot pairing** at level six, for `SmoothOpen` data.  This is
`I2Mem_of_dominated` with the continuity of the integrand read off from the `SmoothOpen` class,
the vanishing at `z = 0` from the weight `w(z)²`, and the domination from `leaf_point_le`. -/
private theorem PairHonest_leaf {α : ℝ} (hα : 0 < α) {a b : ℕ} (hab : a + b ≤ 6)
    {ρ : ℝ → ℝ → ℝ} (hleaf : Work.FTS.TransportS.IsLeafW α a ρ)
    {U F : ℝ → ℝ → ℝ} (hsmU : Work.FTS.EllipticEst.SmoothOpen U)
    (hsmF : Work.FTS.EllipticEst.SmoothOpen F)
    (hmU : Work.Spaces.HkMem α 6 U) (hmF : Work.Spaces.HkMem α 6 F) :
    Work.Coercivity.PairHonest ρ (Work.Spaces.mixed b a U) (Work.Spaces.mixed b a F) := by
  refine Work.FTS.CoercivityFix.Assembly.I2Mem_of_dominated (I2Mem_HkPairDom6 α hmU hmF) ?_ ?_ ?_
  · rcases hleaf with rfl | rfl | ⟨_, rfl⟩
    · have hfun : Function.uncurry (fun z θ => Work.Spaces.mixed b a U z θ
            * Work.Spaces.mixed b a F z θ * Work.FTS.TransportS.leafEta z θ)
          = fun p : ℝ × ℝ => Function.uncurry (Work.Spaces.mixed b a U) p
              * Function.uncurry (Work.Spaces.mixed b a F) p
              * Function.uncurry Work.Coercivity.lamEta p := by
        funext p; rcases p with ⟨z, θ⟩; rfl
      rw [hfun]
      exact (((hsmU.mixed b a).continuousOn).mul ((hsmF.mixed b a).continuousOn)).mul
        Work.FTS.CoercivityFix.Assembly.continuousOn_lamEta
    · have hfun : Function.uncurry (fun z θ => Work.Spaces.mixed b a U z θ
            * Work.Spaces.mixed b a F z θ * Work.FTS.TransportS.leafOne z θ)
          = fun p : ℝ × ℝ => Function.uncurry (Work.Spaces.mixed b a U) p
              * Function.uncurry (Work.Spaces.mixed b a F) p
              * Function.uncurry Work.Coercivity.lamW p := by
        funext p; rcases p with ⟨z, θ⟩; rfl
      rw [hfun]
      exact (((hsmU.mixed b a).continuousOn).mul ((hsmF.mixed b a).continuousOn)).mul
        Work.FTS.CoercivityFix.Assembly.continuousOn_lamW
    · have hfun : Function.uncurry (fun z θ => Work.Spaces.mixed b a U z θ
            * Work.Spaces.mixed b a F z θ * Work.FTS.TransportS.leafGam α z θ)
          = fun p : ℝ × ℝ => Function.uncurry (Work.Spaces.mixed b a U) p
              * Function.uncurry (Work.Spaces.mixed b a F) p
              * Function.uncurry (Work.Coercivity.lamGam α) p := by
        funext p; rcases p with ⟨z, θ⟩; rfl
      rw [hfun]
      exact (((hsmU.mixed b a).continuousOn).mul ((hsmF.mixed b a).continuousOn)).mul
        (Work.FTS.CoercivityFix.Assembly.continuousOn_lamGam α)
  · intro θ
    rcases hleaf with rfl | rfl | ⟨_, rfl⟩ <;>
      simp [Work.FTS.TransportS.leafEta, Work.FTS.TransportS.leafOne,
        Work.FTS.TransportS.leafGam, Work.Spaces.w]
  · intro z hz
    have hmeas : MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2))
        = MeasureTheory.volume.restrict Work.Spaces.Iθ :=
      MeasureTheory.Measure.restrict_congr_set MeasureTheory.Ioo_ae_eq_Icc
    rw [← hmeas]
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with θ hθ
    exact leaf_point_le hα hab hleaf z θ hz hθ

/-! ## The target -/

theorem SlotPairingSplit {α : ℝ} (hα : 0 < α) {a b : ℕ} (hab : a + b ≤ 6)
      {ρ : ℝ → ℝ → ℝ} (hρ : Work.FTS.TransportS.IsLeafW α a ρ)
      {u₁ u₂ f : ℝ → ℝ → ℝ} (h₁ : Work.FTS.EllipticEst.SmoothOpen u₁)
      (h₂ : Work.FTS.EllipticEst.SmoothOpen u₂) (hf : Work.FTS.EllipticEst.SmoothOpen f)
      (m₁ : Work.Spaces.HkMem α 6 u₁) (m₂ : Work.Spaces.HkMem α 6 u₂)
      (mf : Work.Spaces.HkMem α 6 f) :
      Work.FTS.TransportS.slotPairing ρ a b (fun z θ => u₁ z θ + u₂ z θ) f
        = Work.FTS.TransportS.slotPairing ρ a b u₁ f
          + Work.FTS.TransportS.slotPairing ρ a b u₂ f := by
  -- the slot of `u₁ + u₂` splits on the open quadrant
  have hmix : ∀ z θ : ℝ, (z, θ) ∈ Work.Construction.Qd →
      Work.Spaces.mixed b a (fun z θ => u₁ z θ + u₂ z θ) z θ
        = Work.Spaces.mixed b a u₁ z θ + Work.Spaces.mixed b a u₂ z θ := by
    intro z θ hzθ
    have hfe : (fun z θ : ℝ => u₁ z θ + u₂ z θ) = (u₁ + u₂) := by funext z θ; rfl
    rw [hfe]
    exact (Work.FTS.IPGen.BlocksAdd_of_smoothOpen (k := 6) h₁ h₂) a b hab z θ hzθ
  rw [slotPairing_eq_wip ρ a b (fun z θ => u₁ z θ + u₂ z θ) f,
    slotPairing_eq_wip ρ a b u₁ f,
    slotPairing_eq_wip ρ a b u₂ f,
    Work.FTS.CoercivityFix.StepAssembly.wip_congr_Qd (ρ := ρ)
      (A := Work.Spaces.mixed b a (fun z θ => u₁ z θ + u₂ z θ))
      (A' := Work.Spaces.mixed b a u₁ + Work.Spaces.mixed b a u₂)
      (B := Work.Spaces.mixed b a f) hmix]
  exact Work.Coercivity.wip_add_of_PairHonest ρ (Work.Spaces.mixed b a u₁)
    (Work.Spaces.mixed b a u₂) (Work.Spaces.mixed b a f)
    (PairHonest_leaf hα hab hρ h₁ hf m₁ mf)
    (PairHonest_leaf hα hab hρ h₂ hf m₂ mf)

end Work.FTS.StrongPersist.H6Pair6Aux
