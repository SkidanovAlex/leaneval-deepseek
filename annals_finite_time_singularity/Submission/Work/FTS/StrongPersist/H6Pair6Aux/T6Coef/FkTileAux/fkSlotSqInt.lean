/-
Copyright: work module for the Elgindi finite-time singularity project.

# The product-measure `L²`-integrability of a single `ρ`-weighted slot

The level-six coefficient rows consume the single-slot energies of a *leaf* weight `ρ` in two
forms: the iterated integral `∫_z ∫_θ ρ · (D_z^jD_θ^a f)² ≤ HkSq α 6 f`
(`Work.FTS.StrongPersist.H6Pair6Aux.leaf_slot_le6`, via `intSlotLeHkSq`), and — because the
level-six pairing is an integral over the *product* measure
`(volume.restrict Iz).prod (volume.restrict Iθ)` — the assertion that the very same integrand
is `MeasureTheory.Integrable` with respect to that product measure, together with the product
form of the bound.  This file supplies the second form.

The passage from the iterated statement to the product statement is bookkeeping:

* the dominating integrand `HkIntegrand α 6 f` is integrable for the product measure by
  `Work.Spaces.integrable_prod_of_iterated`, whose inputs are exactly the two halves of
  `Work.Spaces.HkMem` together with the a.e. strong measurability coming from
  `SmoothOpen.continuousOn_HkIntegrand` (`aesm_of_continuousOn_Qd`);
* the leaf weight is nonnegative on the open quadrant and dominated there by the corresponding
  slot weight of `HkIntegrand` (`IsLeafW_le`, `leaf_le_slotW_of_le`, `slotW_slot_le`), so the
  target is dominated a.e. by `HkIntegrand α 6 f` and inherits both measurability (from
  `aesm_of_continuousOn_Qd`, using that `ρ` and `D_z^jD_θ^a f` are continuous on the open
  quadrant) and integrability (`Integrable.mono'`);
* the two a.e. statements on the product measure are transported from the open quadrant
  `(0,∞) × (0,π/2)`, which is conull for `(volume.restrict Iz).prod (volume.restrict Iθ)`
  (`Measure.prod_restrict` + `Measure.set_prod_ae_eq`);
* `MeasureTheory.integral_integral` finally identifies the product integral with the iterated
  one, where the already-proved iterated bound applies.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.FkTileAux.fkSlotLeHkSq
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T4bSlotAux
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.leaf_slot_le6
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.Spaces.integrable_prod_of_iterated
import Submission.Work.Spaces.aesm_of_continuousOn_Qd

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.FkTileAux

open scoped Real Topology
open MeasureTheory Set Filter

/-! ## The open quadrant `(0,∞) × (0,π/2)` as seen by the product measure -/

/-- The open quadrant is conull for the product of the two restrictions, so both the a.e.
strong measurability and the a.e. domination may be checked there. -/
private lemma quad_ae_eq {α : ℝ} {f : ℝ → ℝ → ℝ} {a j : ℕ} {ρ : ℝ → ℝ → ℝ}
    (h : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 →
      0 ≤ ρ z θ * Work.Spaces.mixed j a f z θ ^ 2 ∧
        ρ z θ * Work.Spaces.mixed j a f z θ ^ 2 ≤ Work.Spaces.HkIntegrand α 6 f z θ) :
    ∀ᵐ p ∂((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)),
      0 ≤ ρ p.1 p.2 * Work.Spaces.mixed j a f p.1 p.2 ^ 2 ∧
        ρ p.1 p.2 * Work.Spaces.mixed j a f p.1 p.2 ^ 2
          ≤ Work.Spaces.HkIntegrand α 6 f p.1 p.2 := by
  have hprod : (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ : Set (ℝ × ℝ)) =ᵐ[volume.prod volume]
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) :=
    MeasureTheory.Measure.set_prod_ae_eq
      (MeasureTheory.Ioi_ae_eq_Ici (μ := volume) (a := 0)).symm
      (MeasureTheory.Ioo_ae_eq_Icc (μ := volume) (a := 0) (b := π / 2)).symm
  rw [MeasureTheory.Measure.prod_restrict]
  refine (MeasureTheory.ae_restrict_congr_set hprod).mpr ?_
  refine (MeasureTheory.ae_restrict_iff' (measurableSet_Ioi.prod measurableSet_Ioo)).mpr ?_
  refine Filter.Eventually.of_forall fun p hp => ?_
  obtain ⟨hz, hθ⟩ := Set.mem_prod.mp hp
  exact h p.1 p.2 hz hθ.1 hθ.2

/-! ## Continuity of the leaf weights on the open quadrant -/

/-- The plain square of the radial weight is continuous on the open quadrant. -/
private lemma continuousOn_w_sq_Q0 :
    ContinuousOn (fun p : ℝ × ℝ => (Work.Spaces.w p.1) ^ 2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) := by
  simp only [Work.Spaces.w]
  refine ContinuousOn.pow ?_ 2
  exact ContinuousOn.div ((continuousOn_const.add continuousOn_fst).pow 2)
    (continuousOn_fst.pow 2) (fun p hp => pow_ne_zero 2 (ne_of_gt hp.1))

/-- `sin(2θ)^c` is continuous on the open quadrant for every exponent `c`. -/
private lemma continuousOn_sin_rpow_Q0 (c : ℝ) :
    ContinuousOn (fun p : ℝ × ℝ => (Real.sin (2 * p.2)) ^ c)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) := by
  have hf : Continuous fun p : ℝ × ℝ => Real.sin (2 * p.2) :=
    Real.continuous_sin.comp (continuous_const.mul continuous_snd)
  refine (hf.continuousOn).rpow_const ?_
  intro p hp
  obtain ⟨-, hθ⟩ := Set.mem_prod.mp hp
  exact Or.inl (ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1])
    (by linarith [hθ.2, Real.pi_pos])))

/-- Every leaf weight is continuous on the open quadrant. -/
private lemma continuousOn_leaf {α : ℝ} {a : ℕ} {ρ : ℝ → ℝ → ℝ}
    (hρ : Work.FTS.TransportS.IsLeafW α a ρ) :
    ContinuousOn (fun p : ℝ × ℝ => ρ p.1 p.2) (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) := by
  rcases hρ with rfl | rfl | ⟨_, rfl⟩
  · simp only [Work.FTS.TransportS.leafEta]
    exact continuousOn_w_sq_Q0.mul (continuousOn_sin_rpow_Q0 _)
  · exact continuousOn_w_sq_Q0
  · simp only [Work.FTS.TransportS.leafGam]
    exact continuousOn_w_sq_Q0.mul (continuousOn_sin_rpow_Q0 _)

/-! ## The main statement -/

theorem fkSlotSqInt {α : ℝ} (hα : 0 < α) {f : ℝ → ℝ → ℝ} {a j : ℕ} (haj : a + j ≤ 6)
    {ρ : ℝ → ℝ → ℝ} (hρ : Work.FTS.TransportS.IsLeafW α a ρ)
    (hsm : Work.FTS.EllipticEst.SmoothOpen f) (hm6 : Work.Spaces.HkMem α 6 f) :
    MeasureTheory.Integrable (fun p : ℝ × ℝ => ρ p.1 p.2
        * Work.Spaces.mixed j a f p.1 p.2 ^ 2)
        ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ)) ∧
      (∫ p, ρ p.1 p.2 * Work.Spaces.mixed j a f p.1 p.2 ^ 2
          ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
            (MeasureTheory.volume.restrict Work.Spaces.Iθ))) ≤ Work.Spaces.HkSq α 6 f := by
  -- the a.e. strong measurability of the target integrand (continuity on the open quadrant)
  have hAESM : MeasureTheory.AEStronglyMeasurable
      (fun p : ℝ × ℝ => ρ p.1 p.2 * Work.Spaces.mixed j a f p.1 p.2 ^ 2)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
    refine Work.Spaces.aesm_of_continuousOn_Qd _ ?_
    show ContinuousOn ((fun p : ℝ × ℝ => ρ p.1 p.2)
      * (fun p : ℝ × ℝ => Work.Spaces.mixed j a f p.1 p.2) ^ 2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2))
    exact (continuousOn_leaf hρ).mul (((hsm.mixed j a).continuousOn).pow 2)
  -- the dominating `HkIntegrand α 6 f` is a.e. strongly measurable ...
  have hAESMHk : MeasureTheory.AEStronglyMeasurable
      (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α 6 f p.1 p.2)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
    Work.Spaces.aesm_of_continuousOn_Qd _ (hsm.continuousOn_HkIntegrand α 6)
  -- ... and integrable for the product measure (the two halves of `HkMem` are exactly the
  -- slice and the outer integrability of `integrable_prod_of_iterated`)
  have hHk : MeasureTheory.Integrable
      (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α 6 f p.1 p.2)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
    (Work.Spaces.integrable_prod_of_iterated
      (μ := MeasureTheory.volume.restrict Work.Spaces.Iz)
      (ν := MeasureTheory.volume.restrict Work.Spaces.Iθ)
      (G := Work.Spaces.HkIntegrand α 6 f)
      (fun x y => Work.Spaces.HkIntegrand_nonneg α 6 f x y)
      hAESMHk
      (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ici (fun z hz => hm6.1 z hz))
      hm6.2).1
  -- the pointwise domination on the open quadrant
  have hpoint : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 →
      0 ≤ ρ z θ * Work.Spaces.mixed j a f z θ ^ 2 ∧
        ρ z θ * Work.Spaces.mixed j a f z θ ^ 2 ≤ Work.Spaces.HkIntegrand α 6 f z θ := by
    intro z θ hz hθ0 hθ1
    have hθ : θ ∈ Set.Ioo (0 : ℝ) (π / 2) := ⟨hθ0, hθ1⟩
    have h0 : 0 ≤ ρ z θ := (Work.FTS.TransportS.IsLeafW_le α hα hρ).1 z θ hz hθ0 hθ1
    have hle : ρ z θ ≤ Work.FTS.TransportS.slotW α a z θ :=
      Work.FTS.StrongPersist.H6Pair6Aux.leaf_le_slotW_of_le hα hρ le_rfl z θ hz hθ
    have h2 : Work.FTS.TransportS.slotW α a z θ
        * (Work.Spaces.mixed j a f z θ) ^ 2 ≤ Work.Spaces.HkIntegrand α 6 f z θ :=
      Work.FTS.StrongPersist.H6Pair6Aux.slotW_slot_le hα hθ haj
    exact ⟨mul_nonneg h0 (sq_nonneg _),
      le_trans (mul_le_mul_of_nonneg_right hle (sq_nonneg _)) h2⟩
  have hbound := quad_ae_eq hpoint
  -- the target is integrable, being dominated a.e. by the integrable `HkIntegrand`
  have hInt : MeasureTheory.Integrable
      (fun p : ℝ × ℝ => ρ p.1 p.2 * Work.Spaces.mixed j a f p.1 p.2 ^ 2)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
    hHk.mono' hAESM (by
      filter_upwards [hbound] with p hp
      rw [Real.norm_of_nonneg hp.1]
      exact hp.2)
  refine ⟨hInt, ?_⟩
  -- the product integral is the iterated integral, for which the bound is already proved
  have hval : (∫ p : ℝ × ℝ, ρ p.1 p.2 * Work.Spaces.mixed j a f p.1 p.2 ^ 2
        ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ)))
      = ∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
          ρ z θ * Work.Spaces.mixed j a f z θ ^ 2 :=
    (MeasureTheory.integral_integral
      (μ := MeasureTheory.volume.restrict Work.Spaces.Iz)
      (ν := MeasureTheory.volume.restrict Work.Spaces.Iθ)
      (f := fun z θ => ρ z θ * Work.Spaces.mixed j a f z θ ^ 2) hInt).symm
  rw [hval]
  exact Work.FTS.StrongPersist.H6Pair6Aux.leaf_slot_le6 hα hm6 a j ρ haj hρ

end Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.FkTileAux
