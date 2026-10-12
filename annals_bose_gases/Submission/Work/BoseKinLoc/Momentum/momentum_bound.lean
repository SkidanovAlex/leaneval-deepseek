import Mathlib.Tactic.Have
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.BoseKinLoc.Momentum.abs_one_sub_cubFT_le
import Submission.Work.BoseKinLoc.Momentum.cubFT_exterior_bounds
import Submission.Work.BoseKinLoc.Momentum.momForm_u_integral
import Submission.Work.BoseKinLoc.Momentum.symbol_bound
import Submission.Work.BoseKinLoc.Residuals
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseKinLoc.Momentum.momentum_bound` — FS `eq:Q1Qslide`

The residual `Work.BoseKinLoc.MomBound`: there is a universal `b₀ > 0` such that for all
`0 < b ≤ b₀`, all smooth compactly supported `ψ`, all `ℓ > 0` and `0 < d ≤ 1`,

`b · ∫_u momForm ℓ d u ψ  ≤  ½ · raFrac ℓ d ψ`.

This is FS's `eq:Q1Qslide` (Fournais–Solovej, *The energy of dilute Bose gases*, §"Localization
of the kinetic and potential energies"), whose proof is the Bratteli–Solovej Lemma 3.3
Fourier-multiplier computation.  `momForm ℓ d u ψ` is the form of `Q_u 1_{(d⁻²ℓ⁻¹,∞)}(√−Δ) Q_u`
in the corpus's `p`-convention momentum language and `raFrac ℓ d ψ` is the form of
`(−Δ)(−Δ+(dℓ)⁻²)⁻¹`.

The chapter decomposes the proof into

* `momForm_u_integral` — the exact `u`-average of the sliding mean-free box family, in which the
  `u`-dependence is resolved by Plancherel: the `u`-integral of `momForm` equals
  `(2π)⁻³ ∫_s ‖fhat ψ s‖² · (2π)⁻³ ∫_{‖w‖>(d²)⁻¹}(θ(w−ℓs) − θ(ℓs)θ(w))² dw ds`, with `θ` the
  unit-cube symbol `cubFT` (FS's `θ̂`);
* `symbol_bound` — the pointwise bound `∫_{‖w‖>L}(θ(w−v) − θ(v)θ(w))² ≤ C‖v‖²/(‖v‖²+L)`, from
  the decay `cubFT_exterior_bounds` of the cube symbol;
* the present module assembles them.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators ENNReal

namespace Work.BoseKinLoc.Momentum

open Submission.BoseGases

set_option maxHeartbeats 800000

/-- The identified symbol of the `u`-averaged sliding family: `momSym ℓ d s` is the coefficient
of `‖fhat ψ s‖²` in `momForm_u_integral`. -/
def momSym (ℓ d : ℝ) (s : ℝ³) : ℝ :=
  ((2 * Real.pi) ^ 3)⁻¹ *
    ∫ w in {q : ℝ³ | (d ^ 2)⁻¹ < ‖q‖},
      (cubFT (w - ℓ • s) - cubFT (ℓ • s) * cubFT w) ^ 2

/-- **The assembly step.**  Given the exact `u`-averaged identity (`momForm_u_integral`) and the
pointwise symbol bound (`symbol_bound`), `MomBound` follows. -/
theorem momBound_of_pieces
    (hId : ∀ (ψ : ℝ³ → ℝ), ContDiff ℝ ∞ ψ → HasCompactSupport ψ → ∀ ℓ d : ℝ, 0 < ℓ → 0 < d →
      ∫ u : ℝ³, momForm ℓ d u ψ =
        ((2 * Real.pi) ^ 3)⁻¹ * ∫ s : ℝ³, ‖fhat ψ s‖ ^ 2 * momSym ℓ d s)
    (hSym : ∃ C : ℝ, 0 < C ∧ ∀ v : ℝ³, ∀ L : ℝ, 0 < L →
      ∫ w in {q : ℝ³ | L < ‖q‖}, (cubeB v w) ^ 2 ≤ C * ‖v‖ ^ 2 / (‖v‖ ^ 2 + L))
    (hInt : ∀ (ψ : ℝ³ → ℝ), ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      Integrable (fun s : ℝ³ => ‖fhat ψ s‖ ^ 2)) :
    MomBound := by
  obtain ⟨C, hCpos, hSym'⟩ := hSym
  refine ⟨min 1 ((2 * Real.pi) ^ 3 / (2 * C)), lt_min one_pos (by positivity), ?_⟩
  intro b hb hbb ψ hψ hcs ℓ d hℓ hd hd1 hIntM
  -- the pointwise bound on the symbol of the family
  have hKs : ∀ s : ℝ³, momSym ℓ d s ≤ ((2 * Real.pi) ^ 3)⁻¹ * (C * raSym ℓ d s) := by
    intro s
    have h := hSym' (ℓ • s) ((d ^ 2)⁻¹) (by positivity)
    have hcube : cubeB (ℓ • s) = fun w => cubFT (w - ℓ • s) - cubFT (ℓ • s) * cubFT w := rfl
    rw [hcube] at h
    have hratio : ‖ℓ • s‖ ^ 2 / (‖ℓ • s‖ ^ 2 + ((d ^ 2)⁻¹)) = raSym ℓ d s := by
      have h1 : ‖ℓ • s‖ ^ 2 = ℓ ^ 2 * ‖s‖ ^ 2 := by
        rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
      rw [raSym, h1, zpow_neg, zpow_two]
      field_simp
    have h2 : C * ‖ℓ • s‖ ^ 2 / (‖ℓ • s‖ ^ 2 + ((d ^ 2)⁻¹)) = C * raSym ℓ d s := by
      rw [mul_div_assoc, hratio]
    rw [h2] at h
    unfold momSym
    exact mul_le_mul_of_nonneg_left h (by positivity)
  -- the comparison integrands
  set G : ℝ³ → ℝ := fun s => ‖fhat ψ s‖ ^ 2 * momSym ℓ d s with hG
  set g : ℝ³ → ℝ := fun s => ‖fhat ψ s‖ ^ 2 * (((2 * Real.pi) ^ 3)⁻¹ * (C * raSym ℓ d s))
    with hg
  have hGg : ∀ s : ℝ³, G s ≤ g s := by
    intro s
    have h2 : 0 ≤ ‖fhat ψ s‖ ^ 2 := sq_nonneg _
    rw [hG, hg]
    exact mul_le_mul_of_nonneg_left (hKs s) h2
  have hra : Continuous fun s : ℝ³ => raSym ℓ d s := by
    show Continuous fun s : ℝ³ => ‖s‖ ^ 2 / (‖s‖ ^ 2 + (d * ℓ) ^ (-2 : ℤ))
    refine Continuous.div ?_ ?_ ?_
    · fun_prop
    · fun_prop
    · intro s; positivity
  have hgint : Integrable g := by
    have hbase : Integrable (fun s : ℝ³ => ‖fhat ψ s‖ ^ 2) := hInt ψ hψ hcs
    have hconst : 0 ≤ ((2 * Real.pi) ^ 3)⁻¹ * C :=
      mul_nonneg (by positivity) hCpos.le
    have hbound : ∀ s : ℝ³, ‖g s‖ ≤ (((2 * Real.pi) ^ 3)⁻¹ * C) * ‖fhat ψ s‖ ^ 2 := by
      intro s
      have hRat : raSym ℓ d s ≤ 1 := by
        rw [raSym, div_le_one (by positivity)]
        have : 0 ≤ (d * ℓ) ^ (-2 : ℤ) := by positivity
        linarith
      have h2 : 0 ≤ ‖fhat ψ s‖ ^ 2 := sq_nonneg _
      rw [hg, Real.norm_eq_abs, abs_of_nonneg (by
        refine mul_nonneg (sq_nonneg _) ?_
        exact mul_nonneg (by positivity) (mul_nonneg hCpos.le (by rw [raSym]; positivity)))]
      calc ‖fhat ψ s‖ ^ 2 * (((2 * Real.pi) ^ 3)⁻¹ * (C * raSym ℓ d s))
          = (((2 * Real.pi) ^ 3)⁻¹ * C) * (‖fhat ψ s‖ ^ 2 * raSym ℓ d s) := by ring
        _ ≤ (((2 * Real.pi) ^ 3)⁻¹ * C) * (‖fhat ψ s‖ ^ 2 * 1) :=
              mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hRat h2) hconst
        _ = (((2 * Real.pi) ^ 3)⁻¹ * C) * ‖fhat ψ s‖ ^ 2 := by ring
    refine Integrable.mono' (hbase.const_mul (((2 * Real.pi) ^ 3)⁻¹ * C)) ?_ ?_
    · show AEStronglyMeasurable g
      have h1 : AEStronglyMeasurable (fun s : ℝ³ => ‖fhat ψ s‖ ^ 2) :=
        hbase.aestronglyMeasurable
      have h2 : AEStronglyMeasurable
          (fun s : ℝ³ => (((2 * Real.pi) ^ 3)⁻¹ * (C * raSym ℓ d s))) :=
        ((continuous_const.mul (continuous_const.mul hra))).aestronglyMeasurable
      rw [hg]
      exact h1.mul h2
    · exact Eventually.of_forall hbound
  have hmono : ∫ s : ℝ³, G s ≤ ∫ s : ℝ³, g s :=
    integral_mono_of_nonneg (Eventually.of_forall fun s => by
      rw [hG]
      exact mul_nonneg (sq_nonneg _) (by
        unfold momSym
        exact mul_nonneg (by positivity)
          (setIntegral_nonneg (measurableSet_lt measurable_const continuous_norm.measurable)
            fun w _ => sq_nonneg _)))
      hgint (Eventually.of_forall hGg)
  have hgval : ∫ s : ℝ³, g s = C * raFrac ℓ d ψ := by
    have h1 : ∫ s : ℝ³, g s
        = (((2 * Real.pi) ^ 3)⁻¹ * C) * ∫ s : ℝ³, (raSym ℓ d s * ‖fhat ψ s‖ ^ 2) := by
      rw [hg]
      rw [show (fun s : ℝ³ => ‖fhat ψ s‖ ^ 2 * (((2 * Real.pi) ^ 3)⁻¹ * (C * raSym ℓ d s)))
          = (fun s : ℝ³ => (((2 * Real.pi) ^ 3)⁻¹ * C) * (raSym ℓ d s * ‖fhat ψ s‖ ^ 2))
          from by funext s; ring]
      rw [integral_const_mul]
    rw [h1]
    unfold raFrac
    ring
  rw [hId ψ hψ hcs ℓ d hℓ hd]
  have hmain : ∫ s : ℝ³, G s ≤ C * raFrac ℓ d ψ := by
    rw [← hgval]; exact hmono
  have hraF : 0 ≤ raFrac ℓ d ψ := by
    unfold raFrac
    exact mul_nonneg (by positivity) (integral_nonneg fun s => by
      rw [raSym]
      exact mul_nonneg (by positivity) (sq_nonneg _))
  have hbC : b * (((2 * Real.pi) ^ 3)⁻¹ * C) ≤ 1 / 2 := by
    have hb' : b ≤ (2 * Real.pi) ^ 3 / (2 * C) := le_trans hbb (min_le_right _ _)
    calc b * (((2 * Real.pi) ^ 3)⁻¹ * C)
        ≤ ((2 * Real.pi) ^ 3 / (2 * C)) * (((2 * Real.pi) ^ 3)⁻¹ * C) :=
          mul_le_mul_of_nonneg_right hb' (by positivity)
      _ = 1 / 2 := by
          field_simp
  calc b * (((2 * Real.pi) ^ 3)⁻¹ * ∫ s : ℝ³, G s)
      ≤ b * (((2 * Real.pi) ^ 3)⁻¹ * (C * raFrac ℓ d ψ)) := by
        refine mul_le_mul_of_nonneg_left ?_ hb.le
        exact mul_le_mul_of_nonneg_left hmain (by positivity)
    _ = (b * (((2 * Real.pi) ^ 3)⁻¹ * C)) * raFrac ℓ d ψ := by ring
    _ ≤ (1 / 2) * raFrac ℓ d ψ :=
        mul_le_mul_of_nonneg_right hbC hraF

/-- The squared `p`-convention Fourier transform of a smooth compactly supported state is
integrable (the `fhat` spelling of `Work.BSKinetic.integrable_kinFT_sq`). -/
theorem integrable_fhat_sq (ψ : ℝ³ → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hcs : HasCompactSupport ψ) :
    Integrable (fun s : ℝ³ => ‖fhat ψ s‖ ^ 2) :=
  Work.BSKinetic.integrable_kinFT_sq ψ hψ hcs

/-- **FS `eq:Q1Qslide`**, the residual `MomBound`, assembled from the chapter's pieces. -/
theorem momentum_bound : MomBound := by
  obtain ⟨C₁, hC₁, hM, hH⟩ := Work.BoseKinLoc.Momentum.cubFT_exterior_bounds
  obtain ⟨hTotInt, hTot⟩ := Work.BoseKinLoc.Momentum.cubFT_total
  have hM' : ∀ L : ℝ, 0 < L →
      ∫ w in {q : ℝ³ | L < ‖q‖}, (cubFT w) ^ 2 ≤ max C₁ 4096 / L := fun L hL =>
    le_trans (hM L hL) (div_le_div_of_nonneg_right (le_max_left _ _) hL.le)
  have hH' : ∀ L : ℝ, 0 < L → ∑ i : Fin 3,
      ∫ w in {q : ℝ³ | L < ‖q‖},
        (fderiv ℝ cubFT w (Submission.BoseGases.kcStdBasis i)) ^ 2 ≤ max C₁ 4096 / L :=
    fun L hL => le_trans (hH L hL) (div_le_div_of_nonneg_right (le_max_left _ _) hL.le)
  have hTot' : ∫ q : ℝ³, (cubFT q) ^ 2 ≤ max C₁ 4096 := le_trans hTot (le_max_right _ _)
  obtain ⟨C, hC, hSym⟩ := Work.BoseKinLoc.Momentum.symbol_bound (max C₁ 4096)
    (lt_max_of_lt_left hC₁) hM' hTot' hH' Work.BoseKinLoc.Momentum.abs_one_sub_cubFT_le
  refine momBound_of_pieces ?_ ⟨C, hC, hSym⟩ ?_
  · intro ψ hψ hcs ℓ d hℓ hd
    rw [Work.BoseKinLoc.Momentum.momForm_u_integral ψ hψ hcs ℓ d hℓ hd]
    rfl
  · exact fun ψ hψ hcs => integrable_fhat_sq ψ hψ hcs

end Work.BoseKinLoc.Momentum
