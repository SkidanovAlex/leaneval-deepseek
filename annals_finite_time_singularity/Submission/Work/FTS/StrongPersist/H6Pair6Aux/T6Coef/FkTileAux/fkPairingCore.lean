/-
# `FkTileAux/fkPairingLow` — the low `D_z`-power pairing of the angular moment `FK f`

The coefficient slot of the level-six `N`-row contains the *angular moment*
`FK f z = ∫_θ f(z,θ)K(θ)dθ`, a function of `z` alone.  Its `b₁`-th radial iterate
`D_z^{b₁}(FK f) = DzdIter b₁ (FK f)` is paired against **two** slots of the datum `f`:

  `∫∫ ρ · DzdIter b₁ (FK f) z · (D_z^{b-b₁}D_θ^a f) · (D_z^bD_θ^a f)`,

where `ρ` is a leaf weight of the slot `a` (`IsLeafW α a ρ`), `4 ≤ b₁ ≤ 5`, `b₁ ≤ b` and
`a + b ≤ 6`.  The claim is that this triple pairing is bounded by
`C α^{-2}(1+M)(1 + |f|²_{ℋ⁶})` for `DatData α f M` (i.e. `SmoothOpen f`, `HkMem α 6 f`,
`HkMem α 7 f`, `VanishTheta f`, the axis conditions and `Xn α f ≤ M`).

## The route

Since `4 ≤ b₁`, the slot `(b - b₁, a)` has order `≤ 6 - 4 = 2`: it is a **low** slot, and
every low slot of `f` has a *pointwise* bound `|D_z^jD_θ^i f| ≤ C α^{-1/2}(Xn α f)` for
`i+j ≤ 2`.  The triple is therefore handled by two Cauchy–Schwarz inequalities:

* in `θ`, between `θw·(low slot)²` and `θw·(top slot)²` where `ρ = w²·θw`;
* in `z`, between `w²·(D_z^{b₁}(FK f))²` and `w²·P(z)·Q(z)`, where
  `P(z) = ∫_θ θw·(low slot)²` is bounded pointwise in `z` by `C(1+M)²` and
  `Q(z) = ∫_θ θw·(top slot)²` is only needed in `L¹(w²dz)`.

The two a priori inputs are

* `P(z) ≤ C(1+M)²`: for `a ≥ 1` this is the *slicewise radial Agmon* inequality
  (`H6Row6Gam.mixed_slice_z_le_three`), for `a = 0` the pointwise bound
  (`FkTileAux.fkLowPointwise`) together with `∫_{Iθ} sin(2θ)^{-η} < ∞`;
* `∫_z w²Q(z) ≤ |f|²_{ℋ⁶}`: a single summand of `HkIntegrand α 6 f` (`FkTileAux.fkSlotLeHkSq`
  and the pointwise domination `FkTileAux.fkSlotDom`).

The mass of the angular-moment factor, `∫_z w²(DzdIter b₁(FK f))² ≤ C(1+|f|²_{ℋ⁶})`, is
`FkTileAux.fkMomentSq` (the a.e. identity `D_z^j(FK f) = FK(D_z^j f)`), and the measurability
bookkeeping is `FkTileAux.fkMomentAe` (a.e. strong measurability of `DzdIter b₁(FK f) ∘ fst`).

The whole estimate is assembled in `fkCore`; the three leaf weights (and the `a = 0`/`a ≥ 1`
split) only enter through the hypotheses of that lemma.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.Defs
import Submission.Work.FTS.TransportS.Slots
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6SupAux.DzIter_FK_eq_ae
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.FkTileAux.fkSlotDom
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.FkTileAux.fkSlotLeHkSq
import Submission.Work.FTS.StrongPersist.H6Row6Gam.gamSliceSup11
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T6CoefAux.cs_sqrt_int
import Submission.Work.Spaces.aesm_of_continuousOn_Qd
import Submission.Work.Spaces.aesm_slice_of_continuousOn_Qd
import Submission.Work.Spaces.integrable_prod_of_iterated
import Submission.Work.Spaces.sin_two_rpow

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.FkTileAux

open scoped Real Topology
open MeasureTheory Set Filter

set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

/-! ## Elementary facts about the weights -/

/-- `sin(2θ) ≥ 0` on `Iθ`. -/
lemma sin_two_nonneg_Iθ' {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ Real.sin (2 * θ) :=
  Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])

/-- `(w ∘ fst)²` is continuous on the open quadrant. -/
lemma continuousOn_w_sq :
    ContinuousOn (fun p : ℝ × ℝ => (Work.Spaces.w p.1) ^ 2) Work.FTS.EllipticEst.Q0 := by
  have hw : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.w p.1) Work.FTS.EllipticEst.Q0 := by
    have hfun : (fun p : ℝ × ℝ => Work.Spaces.w p.1)
        = fun p : ℝ × ℝ => (1 + p.1) ^ 2 / p.1 ^ 2 := by funext p; rfl
    rw [hfun]
    exact ContinuousOn.div ((continuousOn_const.add continuousOn_fst).pow 2)
      (continuousOn_fst.pow 2) (fun p hp => pow_ne_zero 2 (ne_of_gt (Set.mem_prod.mp hp).1))
  exact hw.pow 2

/-- `sin(2θ) > 0` on the open quadrant. -/
lemma sin_two_pos_Q0' {p : ℝ × ℝ} (hp : p ∈ Work.FTS.EllipticEst.Q0) :
    0 < Real.sin (2 * p.2) := by
  obtain ⟨-, h1, h2⟩ := Work.FTS.EllipticEst.mem_Q0.mp hp
  exact Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])

/-- `θ ↦ sin(2θ)^{-q}` is continuous on the open quadrant. -/
lemma continuousOn_sin_rpow_neg (q : ℝ) :
    ContinuousOn (fun p : ℝ × ℝ => (Real.sin (2 * p.2)) ^ (-q)) Work.FTS.EllipticEst.Q0 :=
  ((Real.continuous_sin.comp (continuous_const.mul continuous_snd)).continuousOn).rpow_const
    (fun p hp => Or.inl (ne_of_gt (sin_two_pos_Q0' hp)))

/-! ## Slice integrability from the pointwise domination -/

/-- If `(w z)²·(θw θ·V z θ)` is dominated by the level-six integrand of `f` and is continuous
in `θ` on the open interval, then the `θ`-slice `θw·V z ·` is integrable. -/
lemma sliceIntegrable_theta {α : ℝ} {f : ℝ → ℝ → ℝ}
    (h6 : Work.Spaces.HkMem α 6 f)
    {θw : ℝ → ℝ}
    (hθwnn : ∀ θ ∈ Work.Spaces.Iθ, 0 ≤ θw θ)
    (hθwcont : ContinuousOn (fun p : ℝ × ℝ => θw p.2) Work.FTS.EllipticEst.Q0)
    {V : ℝ → ℝ → ℝ}
    (hVcont : ContinuousOn (fun p : ℝ × ℝ => V p.1 p.2) Work.FTS.EllipticEst.Q0)
    {z : ℝ} (hz : 0 < z)
    (hVnn : ∀ θ ∈ Work.Spaces.Iθ, 0 ≤ V z θ)
    (hVle : ∀ θ : ℝ, 0 < θ → θ < Real.pi / 2 →
      (Work.Spaces.w z) ^ 2 * θw θ * V z θ ≤ Work.Spaces.HkIntegrand α 6 f z θ) :
    MeasureTheory.Integrable (fun θ => θw θ * V z θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
  have hcont : ContinuousOn (fun p : ℝ × ℝ =>
      (Work.Spaces.w p.1) ^ 2 * (θw p.2 * V p.1 p.2)) Work.FTS.EllipticEst.Q0 :=
    continuousOn_w_sq.mul (hθwcont.mul hVcont)
  have hbig : MeasureTheory.Integrable
      (fun θ => (Work.Spaces.w z) ^ 2 * (θw θ * V z θ))
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
    refine MeasureTheory.Integrable.mono' (h6.1 z (le_of_lt hz))
      (Work.Spaces.aesm_slice_of_continuousOn_Qd _ hcont hz) ?_
    refine Work.Spaces.Slots.ae_restrict_Iθ_of_Ioo (fun θ hθ0 hθ1 => ?_)
    have hθ : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ0, le_of_lt hθ1⟩
    have hnn : 0 ≤ (Work.Spaces.w z) ^ 2 * (θw θ * V z θ) :=
      mul_nonneg (sq_nonneg _) (mul_nonneg (hθwnn θ hθ) (hVnn θ hθ))
    rw [Real.norm_of_nonneg hnn]
    calc (Work.Spaces.w z) ^ 2 * (θw θ * V z θ)
        = (Work.Spaces.w z) ^ 2 * θw θ * V z θ := by ring
      _ ≤ Work.Spaces.HkIntegrand α 6 f z θ := hVle θ hθ0 hθ1
  have hwz : (Work.Spaces.w z) ^ 2 ≠ 0 := by
    have hpos : 0 < Work.Spaces.w z := by
      rw [Work.Spaces.w]
      exact div_pos (by positivity) (by positivity)
    exact pow_ne_zero 2 (ne_of_gt hpos)
  refine (hbig.const_mul (((Work.Spaces.w z) ^ 2)⁻¹)).congr
    (Filter.Eventually.of_forall fun θ => ?_)
  show ((Work.Spaces.w z) ^ 2)⁻¹ * ((Work.Spaces.w z) ^ 2 * (θw θ * V z θ)) = θw θ * V z θ
  rw [← mul_assoc, inv_mul_cancel₀ hwz, one_mul]

/-! ## The core triple-pairing estimate -/

/-- **The triple pairing of the angular-moment iterate against two slots of `f`.**

`θw` is the angular factor of the leaf weight (`ρ = w²·θw`).  The lemma takes the two
pointwise dominations (`hYdom`, `hZdom`, from `FkTileAux.fkSlotDom`), the pointwise-in-`z`
bound `hPbd` on the angular `L²`-mass of the low slot, the radial mass bound
(`hXint`/`hXbd`, from `FkTileAux.fkMomentSq`) and the a.e. strong measurability of `X`
(`hXaesm`, from `FkTileAux.fkMomentAe`), and returns the integrability of the triple product on
the product measure together with the bound `√KP·√(KX(1+|f|²))·√(|f|²)`. -/
theorem fkCore
    {α : ℝ} {f : ℝ → ℝ → ℝ} (hsm : Work.FTS.EllipticEst.SmoothOpen f)
    (h6 : Work.Spaces.HkMem α 6 f)
    {X : ℝ → ℝ} {a b b₁ : ℕ} {θw : ℝ → ℝ} {KP KX : ℝ}
    (hXint : MeasureTheory.Integrable (fun z : ℝ => (Work.Spaces.w z) ^ 2 * (X z) ^ 2)
      (MeasureTheory.volume.restrict Work.Spaces.Iz))
    (hXbd : (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 * (X z) ^ 2)
      ≤ KX * (1 + Work.Spaces.HkSq α 6 f))
    (hXaesm : MeasureTheory.AEStronglyMeasurable (fun p : ℝ × ℝ => X p.1)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)))
    (hθwnn : ∀ θ ∈ Work.Spaces.Iθ, 0 ≤ θw θ)
    (hθwcont : ContinuousOn (fun p : ℝ × ℝ => θw p.2) Work.FTS.EllipticEst.Q0)
    (hYdom : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      (Work.Spaces.w z) ^ 2 * θw θ * (Work.Spaces.mixed (b - b₁) a f z θ) ^ 2
        ≤ Work.Spaces.HkIntegrand α 6 f z θ)
    (hZdom : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      (Work.Spaces.w z) ^ 2 * θw θ * (Work.Spaces.mixed b a f z θ) ^ 2
        ≤ Work.Spaces.HkIntegrand α 6 f z θ)
    (hPbd : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
      (∫ θ in Work.Spaces.Iθ, θw θ * (Work.Spaces.mixed (b - b₁) a f z θ) ^ 2) ≤ KP)
    (hKPpos : 0 < KP) :
    MeasureTheory.Integrable (fun p : ℝ × ℝ =>
        (Work.Spaces.w p.1) ^ 2 * θw p.2 * X p.1
          * Work.Spaces.mixed (b - b₁) a f p.1 p.2 * Work.Spaces.mixed b a f p.1 p.2)
        ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ)) ∧
      |∫ p, (Work.Spaces.w p.1) ^ 2 * θw p.2 * X p.1
            * Work.Spaces.mixed (b - b₁) a f p.1 p.2 * Work.Spaces.mixed b a f p.1 p.2
          ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
            (MeasureTheory.volume.restrict Work.Spaces.Iθ))|
        ≤ Real.sqrt KP * Real.sqrt (KX * (1 + Work.Spaces.HkSq α 6 f))
            * Real.sqrt (Work.Spaces.HkSq α 6 f) := by
  let Yu : ℝ → ℝ → ℝ := fun z θ => Work.Spaces.mixed (b - b₁) a f z θ
  let Zu : ℝ → ℝ → ℝ := fun z θ => Work.Spaces.mixed b a f z θ
  let Fp : ℝ × ℝ → ℝ := fun p =>
    (Work.Spaces.w p.1) ^ 2 * θw p.2 * X p.1 * Yu p.1 p.2 * Zu p.1 p.2
  let Qz : ℝ → ℝ := fun z => ∫ θ in Work.Spaces.Iθ, θw θ * (Zu z θ) ^ 2
  let Pz : ℝ → ℝ := fun z => ∫ θ in Work.Spaces.Iθ, θw θ * (Yu z θ) ^ 2
  -- ## 0. basic facts
  have hIzm : MeasurableSet Work.Spaces.Iz := measurableSet_Ici
  have hIθm : MeasurableSet Work.Spaces.Iθ := measurableSet_Icc
  have hwnn : ∀ z : ℝ, 0 ≤ Work.Spaces.w z := fun z => by
    rw [Work.Spaces.w]
    exact div_nonneg (sq_nonneg _) (sq_nonneg _)
  have hz_ne : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz), z ≠ 0 :=
    (MeasureTheory.ae_restrict_iff' hIzm).mpr (by
      filter_upwards [MeasureTheory.Measure.ae_ne MeasureTheory.volume (0 : ℝ)] with z hz _
      exact hz)
  have hYcont : ContinuousOn (fun p : ℝ × ℝ => Yu p.1 p.2) Work.FTS.EllipticEst.Q0 :=
    (hsm.mixed (b - b₁) a).continuousOn
  have hZcont : ContinuousOn (fun p : ℝ × ℝ => Zu p.1 p.2) Work.FTS.EllipticEst.Q0 :=
    (hsm.mixed b a).continuousOn
  -- ## 1. the two angular slices
  have hYsli : ∀ z : ℝ, 0 < z → MeasureTheory.Integrable (fun θ => θw θ * (Yu z θ) ^ 2)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) := fun z hz =>
    sliceIntegrable_theta (V := fun z θ => (Yu z θ) ^ 2) h6 hθwnn hθwcont (hYcont.pow 2) hz
      (fun θ _ => sq_nonneg _) (fun θ h0 h1 => hYdom z θ hz h0 h1)
  have hZsli : ∀ z : ℝ, 0 < z → MeasureTheory.Integrable (fun θ => θw θ * (Zu z θ) ^ 2)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) := fun z hz =>
    sliceIntegrable_theta (V := fun z θ => (Zu z θ) ^ 2) h6 hθwnn hθwcont (hZcont.pow 2) hz
      (fun θ _ => sq_nonneg _) (fun θ h0 h1 => hZdom z θ hz h0 h1)
  -- ## 2. the angular Cauchy–Schwarz
  have hCSabs : ∀ z : ℝ, 0 < z →
      (∫ θ in Work.Spaces.Iθ, θw θ * |Yu z θ| * |Zu z θ|)
        ≤ Real.sqrt (∫ θ in Work.Spaces.Iθ, θw θ * (Yu z θ) ^ 2)
          * Real.sqrt (∫ θ in Work.Spaces.Iθ, θw θ * (Zu z θ) ^ 2) := by
    intro z hz
    obtain ⟨_, hle⟩ := T6CoefAux.cs_sqrt_int (hYsli z hz) (hZsli z hz)
      (MeasureTheory.ae_restrict_of_forall_mem hIθm
        (fun θ hθ => mul_nonneg (hθwnn θ hθ) (sq_nonneg _)))
      (MeasureTheory.ae_restrict_of_forall_mem hIθm
        (fun θ hθ => mul_nonneg (hθwnn θ hθ) (sq_nonneg _)))
    refine le_trans (le_of_eq ?_) hle
    refine MeasureTheory.setIntegral_congr_fun hIθm (fun θ hθ => ?_)
    have h0 : 0 ≤ θw θ := hθwnn θ hθ
    have h1 : Real.sqrt (θw θ * (Yu z θ) ^ 2) = Real.sqrt (θw θ) * |Yu z θ| := by
      rw [Real.sqrt_mul h0, Real.sqrt_sq_eq_abs]
    have h2 : Real.sqrt (θw θ * (Zu z θ) ^ 2) = Real.sqrt (θw θ) * |Zu z θ| := by
      rw [Real.sqrt_mul h0, Real.sqrt_sq_eq_abs]
    rw [h1, h2]
    have hsq : Real.sqrt (θw θ) * Real.sqrt (θw θ) = θw θ := Real.mul_self_sqrt h0
    calc θw θ * |Yu z θ| * |Zu z θ|
        = (Real.sqrt (θw θ) * Real.sqrt (θw θ)) * (|Yu z θ| * |Zu z θ|) := by
          rw [hsq]; ring
      _ = Real.sqrt (θw θ) * |Yu z θ| * (Real.sqrt (θw θ) * |Zu z θ|) := by ring
  -- ## 3. the top-slot angular mass
  have hQnn : ∀ z : ℝ, 0 ≤ Qz z := fun z =>
    MeasureTheory.integral_nonneg_of_ae (MeasureTheory.ae_restrict_of_forall_mem hIθm
      (fun θ hθ => mul_nonneg (hθwnn θ hθ) (sq_nonneg _)))
  have hPnn : ∀ z : ℝ, 0 ≤ Pz z := fun z =>
    MeasureTheory.integral_nonneg_of_ae (MeasureTheory.ae_restrict_of_forall_mem hIθm
      (fun θ hθ => mul_nonneg (hθwnn θ hθ) (sq_nonneg _)))
  have hQdom_ae : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
      (Work.Spaces.w z) ^ 2 * Qz z
        ≤ ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 6 f z θ := by
    filter_upwards [hz_ne, MeasureTheory.ae_restrict_mem hIzm] with z hzne hzmem
    have hpos : 0 < z := lt_of_le_of_ne hzmem (Ne.symm hzne)
    show (Work.Spaces.w z) ^ 2 * (∫ θ in Work.Spaces.Iθ, θw θ * (Zu z θ) ^ 2) ≤ _
    rw [← MeasureTheory.integral_const_mul]
    refine MeasureTheory.integral_mono_of_nonneg ?_ (h6.1 z hzmem) ?_
    · refine MeasureTheory.ae_restrict_of_forall_mem hIθm (fun θ hθ => ?_)
      exact mul_nonneg (sq_nonneg _) (mul_nonneg (hθwnn θ hθ) (sq_nonneg _))
    · refine Work.Spaces.Slots.ae_restrict_Iθ_of_Ioo (fun θ h0 h1 => ?_)
      calc (Work.Spaces.w z) ^ 2 * (θw θ * (Zu z θ) ^ 2)
          = (Work.Spaces.w z) ^ 2 * θw θ * (Zu z θ) ^ 2 := by ring
        _ ≤ Work.Spaces.HkIntegrand α 6 f z θ := hZdom z θ hpos h0 h1
  have hQint : MeasureTheory.Integrable
      (fun z : ℝ => (Work.Spaces.w z) ^ 2 * Qz z)
      (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
    refine MeasureTheory.Integrable.mono' h6.2 ?_ ?_
    · refine (Work.Spaces.aesm_of_continuousOn_Qd _
        (continuousOn_w_sq.mul (hθwcont.mul (hZcont.pow 2)))).integral_prod_right'.congr
        (Filter.Eventually.of_forall (fun z => ?_))
      show (∫ θ in Work.Spaces.Iθ, (Work.Spaces.w z) ^ 2 * (θw θ * (Zu z θ) ^ 2))
        = (Work.Spaces.w z) ^ 2 * Qz z
      rw [MeasureTheory.integral_const_mul]
    · filter_upwards [hQdom_ae] with z hz
      rw [Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) (hQnn z))]
      exact hz
  have hQbd : (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 * Qz z)
      ≤ Work.Spaces.HkSq α 6 f := by
    calc (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 * Qz z)
        ≤ ∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
            Work.Spaces.HkIntegrand α 6 f z θ :=
          MeasureTheory.integral_mono_ae hQint h6.2 hQdom_ae
      _ = Work.Spaces.HkSq α 6 f := rfl
  -- ## 4. the sharp angular slice bound
  have hPbd_ae : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz), Pz z ≤ KP := hPbd
  have hsliceY : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
      (∫ θ in Work.Spaces.Iθ, |Fp (z, θ)|)
        ≤ Real.sqrt KP * ((Work.Spaces.w z * |X z|)
            * (Work.Spaces.w z * Real.sqrt (Qz z))) := by
    filter_upwards [hz_ne, MeasureTheory.ae_restrict_mem hIzm, hPbd_ae] with z hzne hzmem hPle
    have hpos : 0 < z := lt_of_le_of_ne hzmem (Ne.symm hzne)
    have hcongr : (∫ θ in Work.Spaces.Iθ, |Fp (z, θ)|)
        = (Work.Spaces.w z) ^ 2 * |X z|
          * (∫ θ in Work.Spaces.Iθ, θw θ * |Yu z θ| * |Zu z θ|) := by
      rw [← MeasureTheory.integral_const_mul]
      refine MeasureTheory.setIntegral_congr_fun hIθm (fun θ hθ => ?_)
      have h0 : 0 ≤ θw θ := hθwnn θ hθ
      rw [show Fp (z, θ)
          = (Work.Spaces.w z) ^ 2 * θw θ * X z * Yu z θ * Zu z θ from rfl]
      simp only [abs_mul, abs_of_nonneg (sq_nonneg (Work.Spaces.w z)), abs_of_nonneg h0]
      ring
    rw [hcongr]
    calc (Work.Spaces.w z) ^ 2 * |X z|
          * (∫ θ in Work.Spaces.Iθ, θw θ * |Yu z θ| * |Zu z θ|)
        ≤ (Work.Spaces.w z) ^ 2 * |X z| * (Real.sqrt (Pz z) * Real.sqrt (Qz z)) :=
          mul_le_mul_of_nonneg_left (hCSabs z hpos) (mul_nonneg (sq_nonneg _) (abs_nonneg _))
      _ ≤ (Work.Spaces.w z) ^ 2 * |X z| * (Real.sqrt KP * Real.sqrt (Qz z)) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hPle) (Real.sqrt_nonneg _))
            (mul_nonneg (sq_nonneg _) (abs_nonneg _))
      _ = Real.sqrt KP * ((Work.Spaces.w z * |X z|)
            * (Work.Spaces.w z * Real.sqrt (Qz z))) := by ring
  have hslice_AMgm : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
      (∫ θ in Work.Spaces.Iθ, |Fp (z, θ)|)
        ≤ Real.sqrt KP * (((Work.Spaces.w z) ^ 2 * (X z) ^ 2 + (Work.Spaces.w z) ^ 2 * Qz z)
            / 2) := by
    filter_upwards [hsliceY] with z hz
    refine hz.trans ?_
    refine mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg KP)
    have ha : (Work.Spaces.w z * |X z|) ^ 2 = (Work.Spaces.w z) ^ 2 * (X z) ^ 2 := by
      rw [mul_pow, sq_abs]
    have hb : (Work.Spaces.w z * Real.sqrt (Qz z)) ^ 2 = (Work.Spaces.w z) ^ 2 * Qz z := by
      rw [mul_pow, Real.sq_sqrt (hQnn z)]
    nlinarith [sq_nonneg (Work.Spaces.w z * |X z| - Work.Spaces.w z * Real.sqrt (Qz z))]
  -- ## 5. measurability of the triple product
  have hFXcont : ContinuousOn (fun p : ℝ × ℝ =>
      (Work.Spaces.w p.1) ^ 2 * θw p.2 * Yu p.1 p.2 * Zu p.1 p.2)
      Work.FTS.EllipticEst.Q0 :=
    ((continuousOn_w_sq.mul hθwcont).mul hYcont).mul hZcont
  have hFaesm : MeasureTheory.AEStronglyMeasurable Fp
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
    have h1 : MeasureTheory.AEStronglyMeasurable
        (fun p : ℝ × ℝ => (Work.Spaces.w p.1) ^ 2)
        ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
      Work.Spaces.aesm_of_continuousOn_Qd _ continuousOn_w_sq
    have h2 : MeasureTheory.AEStronglyMeasurable (fun p : ℝ × ℝ => θw p.2)
        ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
      Work.Spaces.aesm_of_continuousOn_Qd _ hθwcont
    have h3 : MeasureTheory.AEStronglyMeasurable (fun p : ℝ × ℝ => Yu p.1 p.2)
        ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
      Work.Spaces.aesm_of_continuousOn_Qd _ hYcont
    have h4 : MeasureTheory.AEStronglyMeasurable (fun p : ℝ × ℝ => Zu p.1 p.2)
        ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
      Work.Spaces.aesm_of_continuousOn_Qd _ hZcont
    exact (((h1.mul h2).mul hXaesm).mul h3).mul h4
  -- ## 6. the a.e. slice integrability of the triple product
  have hIslice : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
      MeasureTheory.Integrable (fun θ => |Fp (z, θ)|)
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
    filter_upwards [hz_ne, MeasureTheory.ae_restrict_mem hIzm] with z hzne hzmem
    have hpos : 0 < z := lt_of_le_of_ne hzmem (Ne.symm hzne)
    have hmaj : MeasureTheory.Integrable
        (fun θ => ((Work.Spaces.w z) ^ 2 * |X z|)
          * ((θw θ * (Yu z θ) ^ 2 + θw θ * (Zu z θ) ^ 2) / 2))
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
      (((hYsli z hpos).add (hZsli z hpos)).div_const 2).const_mul _
    refine MeasureTheory.Integrable.mono' hmaj ?_ ?_
    · have hbase : MeasureTheory.AEStronglyMeasurable
          (fun θ : ℝ => (Work.Spaces.w z) ^ 2 * θw θ * Yu z θ * Zu z θ)
          (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
        (Work.Spaces.aesm_slice_of_continuousOn_Qd
          (fun p : ℝ × ℝ => (Work.Spaces.w p.1) ^ 2 * θw p.2 * Yu p.1 p.2 * Zu p.1 p.2)
          hFXcont hpos)
      exact continuous_abs.comp_aestronglyMeasurable
        ((hbase.const_mul (X z)).congr (Filter.Eventually.of_forall (fun θ => by
          show X z * ((Work.Spaces.w z) ^ 2 * θw θ * Yu z θ * Zu z θ) = Fp (z, θ)
          ring)))
    · refine Work.Spaces.Slots.ae_restrict_Iθ_of_Ioo (fun θ h0 h1 => ?_)
      have hθ : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt h0, le_of_lt h1⟩
      have h0' : 0 ≤ θw θ := hθwnn θ hθ
      have hcongr : |Fp (z, θ)|
          = ((Work.Spaces.w z) ^ 2 * |X z|) * (θw θ * |Yu z θ| * |Zu z θ|) := by
        rw [show Fp (z, θ)
            = (Work.Spaces.w z) ^ 2 * θw θ * X z * Yu z θ * Zu z θ from rfl]
        simp only [abs_mul, abs_of_nonneg (sq_nonneg (Work.Spaces.w z)), abs_of_nonneg h0']
        ring
      rw [hcongr, Real.norm_of_nonneg (mul_nonneg (mul_nonneg (sq_nonneg _) (abs_nonneg _))
        (mul_nonneg (mul_nonneg h0' (abs_nonneg _)) (abs_nonneg _)))]
      refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg (sq_nonneg _) (abs_nonneg _))
      have hAM : |Yu z θ| * |Zu z θ| ≤ ((Yu z θ) ^ 2 + (Zu z θ) ^ 2) / 2 := by
        nlinarith [sq_nonneg (|Yu z θ| - |Zu z θ|), sq_abs (Yu z θ), sq_abs (Zu z θ)]
      calc θw θ * |Yu z θ| * |Zu z θ|
          = θw θ * (|Yu z θ| * |Zu z θ|) := by ring
        _ ≤ θw θ * (((Yu z θ) ^ 2 + (Zu z θ) ^ 2) / 2) :=
            mul_le_mul_of_nonneg_left hAM h0'
        _ = (θw θ * (Yu z θ) ^ 2 + θw θ * (Zu z θ) ^ 2) / 2 := by ring
  -- ## 7. the radial majorant and the outer integrability
  have hmaj_int : MeasureTheory.Integrable
      (fun z : ℝ => Real.sqrt KP
        * (((Work.Spaces.w z) ^ 2 * (X z) ^ 2 + (Work.Spaces.w z) ^ 2 * Qz z) / 2))
      (MeasureTheory.volume.restrict Work.Spaces.Iz) :=
    ((hXint.add hQint).div_const 2).const_mul _
  have hIouter : MeasureTheory.Integrable
      (fun z : ℝ => ∫ θ, |Fp (z, θ)| ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ))
      (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
    refine MeasureTheory.Integrable.mono' hmaj_int
      ((continuous_abs.comp_aestronglyMeasurable hFaesm).integral_prod_right'
        (ν := MeasureTheory.volume.restrict Work.Spaces.Iθ)) ?_
    filter_upwards [hslice_AMgm] with z hz
    rw [Real.norm_of_nonneg (MeasureTheory.integral_nonneg_of_ae
      (MeasureTheory.ae_restrict_of_forall_mem hIθm (fun θ _ => abs_nonneg _)))]
    exact hz
  -- ## 8. Fubini
  obtain ⟨hFabs_int, hFabs_val⟩ := Work.Spaces.integrable_prod_of_iterated
    (μ := MeasureTheory.volume.restrict Work.Spaces.Iz)
    (ν := MeasureTheory.volume.restrict Work.Spaces.Iθ)
    (G := fun z θ => |Fp (z, θ)|) (fun z θ => abs_nonneg _)
    (continuous_abs.comp_aestronglyMeasurable hFaesm) hIslice hIouter
  have hFint : MeasureTheory.Integrable Fp
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
    MeasureTheory.Integrable.mono' hFabs_int hFaesm
      (Filter.Eventually.of_forall (fun p => le_of_eq (Real.norm_eq_abs (Fp p))))
  -- ## 9. the value of the integral
  have hAint : MeasureTheory.Integrable (fun z : ℝ => (Work.Spaces.w z * |X z|) ^ 2)
      (MeasureTheory.volume.restrict Work.Spaces.Iz) :=
    hXint.congr (Filter.Eventually.of_forall (fun z => by
      simp only [Pi.mul_apply, mul_pow, sq_abs]))
  have hBint : MeasureTheory.Integrable
      (fun z : ℝ => (Work.Spaces.w z * Real.sqrt (Qz z)) ^ 2)
      (MeasureTheory.volume.restrict Work.Spaces.Iz) :=
    hQint.congr (Filter.Eventually.of_forall (fun z => by
      simp only [Pi.mul_apply, mul_pow, Real.sq_sqrt (hQnn z)]))
  obtain ⟨hCSz_int, hCSz_le⟩ := T6CoefAux.cs_sqrt_int hAint hBint
    (Filter.Eventually.of_forall (fun z => sq_nonneg _))
    (Filter.Eventually.of_forall (fun z => sq_nonneg _))
  have hCSz_le' : (∫ z, (Work.Spaces.w z * |X z|) * (Work.Spaces.w z * Real.sqrt (Qz z))
        ∂(MeasureTheory.volume.restrict Work.Spaces.Iz))
      ≤ Real.sqrt (∫ z, (Work.Spaces.w z * |X z|) ^ 2
            ∂(MeasureTheory.volume.restrict Work.Spaces.Iz))
        * Real.sqrt (∫ z, (Work.Spaces.w z * Real.sqrt (Qz z)) ^ 2
            ∂(MeasureTheory.volume.restrict Work.Spaces.Iz)) := by
    refine le_trans (le_of_eq ?_) hCSz_le
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
    show (Work.Spaces.w x * |X x|) * (Work.Spaces.w x * Real.sqrt (Qz x))
        = Real.sqrt ((Work.Spaces.w x * |X x|) ^ 2)
          * Real.sqrt ((Work.Spaces.w x * Real.sqrt (Qz x)) ^ 2)
    rw [Real.sqrt_sq_eq_abs, Real.sqrt_sq_eq_abs,
      abs_of_nonneg (mul_nonneg (hwnn x) (abs_nonneg _)),
      abs_of_nonneg (mul_nonneg (hwnn x) (Real.sqrt_nonneg _))]
  have hprodint : MeasureTheory.Integrable
      (fun z : ℝ => Real.sqrt KP * ((Work.Spaces.w z * |X z|)
        * (Work.Spaces.w z * Real.sqrt (Qz z))))
      (MeasureTheory.volume.restrict Work.Spaces.Iz) :=
    (hCSz_int.const_mul (Real.sqrt KP)).congr (Filter.Eventually.of_forall (fun z => by
      show Real.sqrt KP * (Real.sqrt ((Work.Spaces.w z * |X z|) ^ 2)
          * Real.sqrt ((Work.Spaces.w z * Real.sqrt (Qz z)) ^ 2))
        = Real.sqrt KP * ((Work.Spaces.w z * |X z|) * (Work.Spaces.w z * Real.sqrt (Qz z)))
      rw [Real.sqrt_sq_eq_abs, Real.sqrt_sq_eq_abs,
        abs_of_nonneg (mul_nonneg (hwnn z) (abs_nonneg _)),
        abs_of_nonneg (mul_nonneg (hwnn z) (Real.sqrt_nonneg _))]))
  have hmain : (∫ z, (∫ θ, |Fp (z, θ)| ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ))
        ∂(MeasureTheory.volume.restrict Work.Spaces.Iz))
      ≤ Real.sqrt KP * Real.sqrt (KX * (1 + Work.Spaces.HkSq α 6 f))
          * Real.sqrt (Work.Spaces.HkSq α 6 f) := by
    have e1 : (∫ z, (Work.Spaces.w z * |X z|) ^ 2 ∂(MeasureTheory.volume.restrict Work.Spaces.Iz))
        = ∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 * (X z) ^ 2 :=
      MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun z => by
        simp only [Pi.mul_apply, mul_pow, sq_abs]))
    have e2 : (∫ z, (Work.Spaces.w z * Real.sqrt (Qz z)) ^ 2
          ∂(MeasureTheory.volume.restrict Work.Spaces.Iz))
        = ∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 * Qz z :=
      MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun z => by
        simp only [Pi.mul_apply, mul_pow, Real.sq_sqrt (hQnn z)]))
    calc (∫ z, (∫ θ, |Fp (z, θ)| ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ))
          ∂(MeasureTheory.volume.restrict Work.Spaces.Iz))
        ≤ ∫ z, Real.sqrt KP * ((Work.Spaces.w z * |X z|)
            * (Work.Spaces.w z * Real.sqrt (Qz z)))
          ∂(MeasureTheory.volume.restrict Work.Spaces.Iz) :=
          MeasureTheory.integral_mono_ae hIouter hprodint hsliceY
      _ = Real.sqrt KP * (∫ z, (Work.Spaces.w z * |X z|)
            * (Work.Spaces.w z * Real.sqrt (Qz z))
          ∂(MeasureTheory.volume.restrict Work.Spaces.Iz)) :=
          MeasureTheory.integral_const_mul _ _
      _ ≤ Real.sqrt KP * (Real.sqrt (∫ z, (Work.Spaces.w z * |X z|) ^ 2
              ∂(MeasureTheory.volume.restrict Work.Spaces.Iz))
            * Real.sqrt (∫ z, (Work.Spaces.w z * Real.sqrt (Qz z)) ^ 2
              ∂(MeasureTheory.volume.restrict Work.Spaces.Iz))) :=
          mul_le_mul_of_nonneg_left hCSz_le' (Real.sqrt_nonneg _)
      _ = Real.sqrt KP * (Real.sqrt (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 * (X z) ^ 2)
            * Real.sqrt (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 * Qz z)) := by
          rw [e1, e2]
      _ ≤ Real.sqrt KP * (Real.sqrt (KX * (1 + Work.Spaces.HkSq α 6 f))
            * Real.sqrt (Work.Spaces.HkSq α 6 f)) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul (Real.sqrt_le_sqrt hXbd) (Real.sqrt_le_sqrt hQbd)
              (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
            (Real.sqrt_nonneg _)
      _ = Real.sqrt KP * Real.sqrt (KX * (1 + Work.Spaces.HkSq α 6 f))
            * Real.sqrt (Work.Spaces.HkSq α 6 f) := by ring
  refine ⟨hFint, ?_⟩
  calc |∫ p, Fp p ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ))|
      ≤ ∫ p, ‖Fp p‖ ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
        MeasureTheory.norm_integral_le_integral_norm Fp
    _ = ∫ p, |Fp p| ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by simp only [Real.norm_eq_abs]
    _ = ∫ z, (∫ θ, |Fp (z, θ)| ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ))
          ∂(MeasureTheory.volume.restrict Work.Spaces.Iz) := hFabs_val
    _ ≤ Real.sqrt KP * Real.sqrt (KX * (1 + Work.Spaces.HkSq α 6 f))
          * Real.sqrt (Work.Spaces.HkSq α 6 f) := hmain


end Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.FkTileAux
