import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseFixB1.boxQ1CrossSqrtB1
import Submission.Work.BoseFixB1S.wSmall1Pair_fibre_le_chiB_sharpConst
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseB1Cube.cubeDiluteFibre` — the **sharp-constant** fibre row

The dilute-band arm of the per-box row (`τ = flatTau ≤ θμ`) needs an upper bound on the fibre term
`μ·flatFibSum` that is *linear in the windowed count* and does **not** carry the astronomical
constants of the on-disk fibre rows (`fibSum_le_localSup`/`fibSum_le_chiSup_mul_occChi` carry
`bandK = 16π(a v)/smallConvLower M`, i.e. `≈ 2^{150}`; `fibSum_le_manifest` carries `chiSmallDecay`).
The sharp input is the PROVED pointwise row

    `Work.BoseFixB1S.wSmall1Pair_fibre_le_chiB_sharpConst`
      `|∫_{acube ℓ} wSmall1Pair h M ℓ d u x y dy| ≤ K·(a v)·χ_B(x)`    with `K ≤ 10^6` ,

which is *linear in the window* `χ_B` — the correct shape at the small-box face (where `χ_B → 0`
linearly while the fibre's convolution stays bounded below, the reason the `χ_B²`-form of the
sharp fibre is still open).  Integrating it against `Φ²` gives this module's row

* `Work.BoseB1Cube.flatFibSum_le_sharp_mul_occChi`
    `flatFibSum h M ℓ d u Φ ≤ (10^6·(a v))·occChi M ℓ d u Φ`

where `occChi M ℓ d u Φ = ∫_{abox}Φ²·Σᵢχ_B(xᵢ)` (`Work.BoseFixR.occChi`) is the **linear**
χ-count.  Together with Cauchy–Schwarz `occChi² ≤ n·scountB·N` (available in place) this makes the
dilute-band accounting `μ·flatFibSum ≲ μ·(10^6(a v))·occChi ≤ (½−2c₁)μ²·w1MassB·‖Φ‖²` close as soon
as `τ = flatTau ≤ θμ` with `θ` fixed — see `FINDING_cubePerBox_sector.md` §8–§9.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped Topology Real BigOperators ENNReal

namespace Work.BoseB1Cube

open _root_.BoseGases Submission.BoseGases Work.BoseBoxFix Work.BoseBox Work.UBB
open Work.SmallBoxSliding

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 2000000

/-- **The sharp-constant fibre row.**  Integrating the PROVED pointwise bound
(`wSmall1Pair_fibre_le_chiB_sharpConst`, constant `K ≤ 10^6`) against `Φ²` gives

    `|flatFibSum| ≤ (10^6·(a v))·occChi`,

i.e. the fibre sum is controlled by the **linear** windowed count, with a constant that is a fixed
number — the input the dilute band arm's accounting needs. -/
theorem abs_flatFibSum_le_sharp_mul_occChi {v : E3 → ℝ} (h : Work.UBB.ScatSol v)
    (hv : 0 ≤ v) (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : E3) R) {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d)
    (hR16 : R ≤ ℓ * d / 16) (hRχ : R ≤ ℓ * Submission.BoseGases.chiR0)
    (u : E3) {n : ℕ} (Φ : X n → ℝ) (hΦc : Continuous Φ) :
    |Work.BoseFixB1.flatFibSum h Work.BoseBox.mValue ℓ d u Φ|
      ≤ (10 ^ 6 * (_root_.BoseGases.a v)) * Work.BoseFixR.occChi Work.BoseBox.mValue ℓ d u Φ := by
  obtain ⟨K, _hK0, hKle, hK⟩ :=
    Work.BoseFixB1S.wSmall1Pair_fibre_le_chiB_sharpConst hv_supp hR hv hvrad h
  have ha : 0 ≤ _root_.BoseGases.a v := Work.BoseFixB1.a_nonneg hR hv hvrad hv_supp h
  have hchi0 : ∀ x : E3, 0 ≤ Submission.BoseGases.chiScale ℓ x
      * Submission.BoseGases.chiSmall Work.BoseBox.mValue ((ℓ * d)⁻¹ • x - u) := fun x =>
    mul_nonneg (Submission.BoseGases.chiScale_nonneg ℓ x)
      (Submission.BoseGases.chiSmall_nonneg _ _)
  -- ## the pointwise bound, at every `x`
  have hpt : ∀ x : E3, ‖∫ y in Submission.BoseGases.acube ℓ,
        Submission.BoseGases.wSmall1Pair h Work.BoseBox.mValue ℓ d u x y‖
      ≤ (10 ^ 6 * (_root_.BoseGases.a v)) *
          (Submission.BoseGases.chiScale ℓ x *
            Submission.BoseGases.chiSmall Work.BoseBox.mValue ((ℓ * d)⁻¹ • x - u)) := by
    intro x
    refine le_trans (hK hℓ hd hR16 hRχ u x) ?_
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hKle ha) (hchi0 x)
  -- ## the sum bound, pointwise in `x : X n`
  have hsum : ∀ x : X n, ‖∑ i : Fin n, ∫ y in Submission.BoseGases.acube ℓ,
        Submission.BoseGases.wSmall1Pair h Work.BoseBox.mValue ℓ d u (x i) y‖
      ≤ (10 ^ 6 * (_root_.BoseGases.a v)) *
          ∑ i : Fin n, (Submission.BoseGases.chiScale ℓ (x i)
            * Submission.BoseGases.chiSmall Work.BoseBox.mValue ((ℓ * d)⁻¹ • (x i) - u)) := by
    intro x
    refine le_trans (norm_sum_le _ _) ?_
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun i _ => hpt (x i)
  -- ## integrability of the dominating function
  have hIntB : IntegrableOn (fun x : X n => (Φ x) ^ 2 *
      ((10 ^ 6 * (_root_.BoseGases.a v)) *
        ∑ i : Fin n, (Submission.BoseGases.chiScale ℓ (x i)
          * Submission.BoseGases.chiSmall Work.BoseBox.mValue ((ℓ * d)⁻¹ • (x i) - u))))
      (abox n ℓ) := by
    refine Work.UBBInputs9.B.integrableOn_abox_of_continuous' ?_
    have hchi : Continuous (fun x : E3 => Submission.BoseGases.chiScale ℓ x
        * Submission.BoseGases.chiSmall Work.BoseBox.mValue ((ℓ * d)⁻¹ • x - u)) :=
      (Submission.BoseGases.chiScale_continuous ℓ).mul
        ((Work.SmallBoxSliding.chiSmall_continuous_all _).comp (by fun_prop))
    exact (hΦc.pow 2).mul (continuous_const.mul
      (continuous_finsetSum _ fun i _ => hchi.comp (continuous_apply i)))
  -- ## monotonicity of the integral in norm form
  have hmain : ‖∫ x in abox n ℓ, (Φ x) ^ 2 *
        (∑ i : Fin n, ∫ y in Submission.BoseGases.acube ℓ,
          Submission.BoseGases.wSmall1Pair h Work.BoseBox.mValue ℓ d u (x i) y)‖
      ≤ ∫ x in abox n ℓ, (Φ x) ^ 2 *
          ((10 ^ 6 * (_root_.BoseGases.a v)) *
            ∑ i : Fin n, (Submission.BoseGases.chiScale ℓ (x i)
              * Submission.BoseGases.chiSmall Work.BoseBox.mValue ((ℓ * d)⁻¹ • (x i) - u))) := by
    refine MeasureTheory.norm_integral_le_of_norm_le hIntB ?_
    filter_upwards with x
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (sq_nonneg (Φ x))]
    exact mul_le_mul_of_nonneg_left (hsum x) (sq_nonneg _)
  -- ## the dominated integral, reidentified as `occChi`
  have hIntEq : (∫ x in abox n ℓ, (Φ x) ^ 2 *
        ((10 ^ 6 * (_root_.BoseGases.a v)) *
          ∑ i : Fin n, (Submission.BoseGases.chiScale ℓ (x i)
            * Submission.BoseGases.chiSmall Work.BoseBox.mValue ((ℓ * d)⁻¹ • (x i) - u))))
      = (10 ^ 6 * (_root_.BoseGases.a v)) *
          (∫ x in abox n ℓ, (Φ x) ^ 2 *
            ∑ i : Fin n, Submission.BoseGases.chiSmallB Work.BoseBox.mValue ℓ d u (x i)) := by
    rw [show (fun x : X n => (Φ x) ^ 2 * ((10 ^ 6 * (_root_.BoseGases.a v)) *
          ∑ i : Fin n, (Submission.BoseGases.chiScale ℓ (x i)
            * Submission.BoseGases.chiSmall Work.BoseBox.mValue ((ℓ * d)⁻¹ • (x i) - u))))
        = fun x => (10 ^ 6 * (_root_.BoseGases.a v)) *
            ((Φ x) ^ 2 * ∑ i : Fin n, Submission.BoseGases.chiSmallB Work.BoseBox.mValue ℓ d u (x i)) from by
      funext x
      rw [show (∑ i : Fin n, (Submission.BoseGases.chiScale ℓ (x i)
            * Submission.BoseGases.chiSmall Work.BoseBox.mValue ((ℓ * d)⁻¹ • (x i) - u)))
          = ∑ i : Fin n, Submission.BoseGases.chiSmallB Work.BoseBox.mValue ℓ d u (x i) from by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Submission.BoseGases.chiSmallB]]
      ring]
    rw [MeasureTheory.integral_const_mul]
  rw [Work.BoseFixR.occChi]
  rw [hIntEq] at hmain
  simpa only [Work.BoseFixB1.flatFibSum, Real.norm_eq_abs] using hmain

/-- The one-sided form used by the dilute band accounting. -/
theorem flatFibSum_le_sharp_mul_occChi {v : E3 → ℝ} (h : Work.UBB.ScatSol v)
    (hv : 0 ≤ v) (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : E3) R) {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d)
    (hR16 : R ≤ ℓ * d / 16) (hRχ : R ≤ ℓ * Submission.BoseGases.chiR0)
    (u : E3) {n : ℕ} (Φ : X n → ℝ) (hΦc : Continuous Φ) :
    Work.BoseFixB1.flatFibSum h Work.BoseBox.mValue ℓ d u Φ
      ≤ (10 ^ 6 * (_root_.BoseGases.a v)) * Work.BoseFixR.occChi Work.BoseBox.mValue ℓ d u Φ :=
  le_trans (le_abs_self _)
    (abs_flatFibSum_le_sharp_mul_occChi h hv hvrad hR hv_supp hℓ hd hR16 hRχ u Φ hΦc)

/-! ## 2. The `F`-half of the dilute arm

With `t(x) = nCountB(x)/chiMass`, the PROVED pointwise bound
`psiWeight 1 μ t ≤ μ(t+μ)` (`Work.BoseFixB1S.psiWeight_one_le_mu_add`) turns the `F`-debit into the
**linear** form `μ·∫Φ²(nCountB/chiMass) + μ²·∫Φ²`.  (The identification
`∫Φ²(nCountB/chiMass) = flatScountB/chiMass` is `MeasureTheory.integral_div`, applied by the
caller; keeping it out of the statement makes this brick independent of the count normalisation.) -/
theorem flatFterm_le_mu_sq_add {M : ℕ} {ℓ d μ : ℝ} (hμ : 0 < μ) {n : ℕ}
    (Φ : X n → ℝ) (hΦc : Continuous Φ) (u : E3) :
    (∫ x in abox n ℓ, (Φ x) ^ 2 *
        Work.SmallBoxSliding.psiWeight 1 μ
          (Work.BoseFixB1.nCountB M ℓ d u x / Work.SmallBoxSliding.chiMass M ℓ d u))
      ≤ μ * (∫ x in abox n ℓ, (Φ x) ^ 2 * Work.BoseFixB1.nCountB M ℓ d u x
            / Work.SmallBoxSliding.chiMass M ℓ d u)
        + μ ^ 2 * (∫ x in abox n ℓ, (Φ x) ^ 2) := by
  have hnn : ∀ x : X n, 0 ≤ Work.BoseFixB1.nCountB M ℓ d u x := by
    intro x
    rw [Work.BoseFixB1.nCountB]
    exact Finset.sum_nonneg fun i _ => sq_nonneg _
  have hχ : 0 ≤ Work.SmallBoxSliding.chiMass M ℓ d u :=
    Work.SmallBoxSliding.chiMass_nonneg M ℓ d u
  have hchi : Continuous (fun x : E3 => Submission.BoseGases.chiSmallB M ℓ d u x) := by
    rw [show (fun x : E3 => Submission.BoseGases.chiSmallB M ℓ d u x)
        = fun x => Submission.BoseGases.chiScale ℓ x
            * Submission.BoseGases.chiSmall M ((ℓ * d)⁻¹ • x - u) from by
      funext x; rw [Submission.BoseGases.chiSmallB]]
    exact (Submission.BoseGases.chiScale_continuous ℓ).mul
      ((Work.SmallBoxSliding.chiSmall_continuous_all _).comp (by fun_prop))
  have hnc : Continuous (fun x : X n => Work.BoseFixB1.nCountB M ℓ d u x) := by
    rw [show (fun x : X n => Work.BoseFixB1.nCountB M ℓ d u x)
        = fun x => ∑ i : Fin n, (Submission.BoseGases.chiSmallB M ℓ d u (x i)) ^ 2 from by
      funext x; rw [Work.BoseFixB1.nCountB]]
    exact continuous_finsetSum _ fun i _ => (hchi.comp (continuous_apply i)).pow 2
  -- ## the pointwise bound
  have hpt : ∀ x : X n, (Φ x) ^ 2 *
        Work.SmallBoxSliding.psiWeight 1 μ
          (Work.BoseFixB1.nCountB M ℓ d u x / Work.SmallBoxSliding.chiMass M ℓ d u)
      ≤ (Φ x) ^ 2 * (μ * (Work.BoseFixB1.nCountB M ℓ d u x
            / Work.SmallBoxSliding.chiMass M ℓ d u) + μ ^ 2) := by
    intro x
    refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
    refine (Work.BoseFixB1S.psiWeight_one_le_mu_add hμ (div_nonneg (hnn x) hχ)).trans ?_
    refine le_of_eq ?_
    ring
  have hLnn : ∀ x : X n, 0 ≤ (Φ x) ^ 2 *
      Work.SmallBoxSliding.psiWeight 1 μ
        (Work.BoseFixB1.nCountB M ℓ d u x / Work.SmallBoxSliding.chiMass M ℓ d u) := by
    intro x
    refine mul_nonneg (sq_nonneg _) ?_
    rw [Work.SmallBoxSliding.psiWeight]
    refine div_nonneg (mul_nonneg zero_le_one (sq_nonneg _)) ?_
    have h1 : 0 ≤ (Work.BoseFixB1.nCountB M ℓ d u x / Work.SmallBoxSliding.chiMass M ℓ d u)
        * μ⁻¹ := mul_nonneg (div_nonneg (hnn x) hχ) (inv_nonneg.mpr hμ.le)
    linarith
  have hIntR : IntegrableOn (fun x : X n => (Φ x) ^ 2 *
      (μ * (Work.BoseFixB1.nCountB M ℓ d u x / Work.SmallBoxSliding.chiMass M ℓ d u) + μ ^ 2))
      (abox n ℓ) :=
    Work.UBBInputs9.B.integrableOn_abox_of_continuous'
      ((hΦc.pow 2).mul ((continuous_const.mul (hnc.div_const _)).add continuous_const))
  have hmono := MeasureTheory.integral_mono_of_nonneg
    (Filter.Eventually.of_forall hLnn) hIntR (Filter.Eventually.of_forall hpt)
  -- ## identify the right-hand side
  have hsplit : (fun x : X n => (Φ x) ^ 2 * (μ * (Work.BoseFixB1.nCountB M ℓ d u x
          / Work.SmallBoxSliding.chiMass M ℓ d u) + μ ^ 2))
      = fun x => μ * ((Φ x) ^ 2 * Work.BoseFixB1.nCountB M ℓ d u x
            / Work.SmallBoxSliding.chiMass M ℓ d u) + μ ^ 2 * (Φ x) ^ 2 := by
    funext x
    rw [show μ * (Work.BoseFixB1.nCountB M ℓ d u x / Work.SmallBoxSliding.chiMass M ℓ d u) + μ ^ 2
        = μ * (Work.BoseFixB1.nCountB M ℓ d u x / Work.SmallBoxSliding.chiMass M ℓ d u) + μ ^ 2
        from rfl]
    ring
  have hkey : (∫ x in abox n ℓ, (Φ x) ^ 2 * (μ * (Work.BoseFixB1.nCountB M ℓ d u x
          / Work.SmallBoxSliding.chiMass M ℓ d u) + μ ^ 2))
      = μ * (∫ x in abox n ℓ, (Φ x) ^ 2 * Work.BoseFixB1.nCountB M ℓ d u x
            / Work.SmallBoxSliding.chiMass M ℓ d u)
        + μ ^ 2 * (∫ x in abox n ℓ, (Φ x) ^ 2) := by
    rw [hsplit]
    rw [MeasureTheory.integral_add]
    · rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
    · exact Work.UBBInputs9.B.integrableOn_abox_of_continuous'
        (continuous_const.mul (((hΦc.pow 2).mul hnc).div_const _))
    · exact Work.UBBInputs9.B.integrableOn_abox_of_continuous' ((hΦc.pow 2).const_mul _)
  rw [hkey] at hmono
  exact hmono

end Work.BoseB1Cube
