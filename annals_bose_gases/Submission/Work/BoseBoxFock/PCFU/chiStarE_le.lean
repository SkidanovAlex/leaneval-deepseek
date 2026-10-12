import Mathlib.Analysis.Convolution
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Submission.Work.BoseBoxFock.uvSmear_L1_tendsto
import Submission.Work.BoseFixB3.CS.Pieces.chi_lipschitz
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.PCFU.chiStarE_le`

The `(E)`-row of the cubic dictionary: the **UV-smearing error paired against the box
localisation** is `O(1/Λ)` uniformly in `z`,

    `|∫ w, χ_Λ(w) · ((ψ_Λ ⋆ W₁)(z−w) − W₁(z−w))| ≤ C/Λ`     (`Λ ≥ 1`),

where `χ_Λ = corpusBox.chiLam ℓ` is the box localisation function (`χ_Λ(x) = χ(x/ℓ)`, the
`C^∞` bump of `Submission/CubicChi.lean` supported in the cube of side `ℓ`), `W₁ = W1fun v h ℓ`
is the renormalised weight (`L¹` only — this is the sole hypothesis on it), and
`ψ_Λ = uvKernel fu Λ`, `uvSmear fu Λ f = ψ_Λ ⋆ f`.

## Why the estimate is not the trivial `L¹`/`L^∞` bound

The hypothesis `hI` gives `W₁ ∈ L¹` with **no regularity**, so the naive route

    `|∫ w χ_Λ(w) g(z−w)| ≤ ‖χ_Λ‖_∞ ‖g‖_1`     (`g = ψ_Λ ⋆ W₁ − W₁`)

only produces an `O(1)` bound (uniform in `Λ`: `‖ψ_Λ‖₁` is uniformly bounded), not the required
`O(1/Λ)`.  The rate comes from the **smoothness of `χ_Λ`**: the difference is transferred from
`W₁` to `χ_Λ` by the exact translation of the integration variable,

    `∫ w, χ(w)·W₁(z−w−t) dw = ∫ u, χ(u−t)·W₁(z−u) du`     (`u = w + t`),

after which `χ_Λ`'s Lipschitz constant `L/ℓ` (`χ_Λ(x) = chi(ℓ⁻¹x)` with `chi` compactly
supported and `C^∞`) produces the `1/Λ`: the remaining factor is the first moment
`∫ t, |ψ_Λ(t)|·‖t‖ dt ≤ C/Λ` of the smearing kernel (`ψ_Λ(t) = Λ³ k(Λt)` is a scaled Schwartz
kernel, so each extra power of `Λ` buys a factor `1/Λ`; this is read off directly from the
scaled Schwartz decay `Work.BoseBoxFock.uvKernel_decay`).

The one genuinely analytic ingredient is therefore the **Fubini/interchange identity**
`smear_interchange` below, which moves the difference onto `χ_Λ`:

    `∫ w, χ(w) (∫ t, K(t)(f(z−w−t) − f(z−w)))
        = ∫ t, K(t) (∫ u, (χ(u−t) − χ(u)) f(z−u))`.

Everything else is bookkeeping; the `C^∞` bump properties used are `chi_lipschitz`
(`Work.BoseFixB3.CS.Pieces`) and `chi_hasCompactSupport` (boundedness).
-/

namespace Work.BoseBoxFock.PCFU

open MeasureTheory
open scoped Real Convolution

local notation "E3" => EuclideanSpace ℝ (Fin 3)

noncomputable section

set_option maxHeartbeats 1000000

/-! ## 1. The localisation function `χ_Λ` -/

/-- The box localisation function is the rescaled corpus bump: `χ_Λ(x) = chi (ℓ⁻¹ • x)`. -/
private lemma corpusBox_chiLam_eq (ℓ : ℝ) (x : E3) :
    Work.BoseK15.corpusBox.chiLam ℓ x = Submission.BoseGases.chi (ℓ⁻¹ • x) := by
  simp only [Work.BoseB4.BoxData.chiLam, Work.BoseK15.corpusBox_chi]

/-- `χ_Λ` is bounded, uniformly in the scaling `ℓ`. -/
private lemma chiLam_bound : ∃ C : ℝ, 0 ≤ C ∧ ∀ (ℓ : ℝ) (x : E3),
    ‖Work.BoseK15.corpusBox.chiLam ℓ x‖ ≤ C := by
  obtain ⟨C, hC⟩ := Submission.BoseGases.chi_hasCompactSupport.exists_bound_of_continuous
    Submission.BoseGases.chi_continuous
  exact ⟨C, le_trans (norm_nonneg _) (hC 0), fun ℓ x => by
    rw [corpusBox_chiLam_eq]; exact hC _⟩

/-- **The Lipschitz constant of `χ_Λ` scales as `1/ℓ`**: this is what converts the UV smearing
at momentum scale `Λ` into the `1/Λ`-rate of the target. -/
private lemma chiLam_lipschitz_shift : ∃ L : ℝ, 0 ≤ L ∧ ∀ (ℓ : ℝ), 0 < ℓ → ∀ u t : E3,
    |Work.BoseK15.corpusBox.chiLam ℓ (u - t) - Work.BoseK15.corpusBox.chiLam ℓ u|
      ≤ L / ℓ * ‖t‖ := by
  obtain ⟨L, hL0, hL⟩ := Work.BoseFixB3.CS.Pieces.chi_lipschitz
  refine ⟨L, hL0, fun ℓ hℓ u t => ?_⟩
  rw [corpusBox_chiLam_eq, corpusBox_chiLam_eq]
  have h := hL (ℓ⁻¹ • (u - t)) (ℓ⁻¹ • u)
  have hd : ℓ⁻¹ • (u - t) - ℓ⁻¹ • u = -(ℓ⁻¹ • t) := by rw [smul_sub]; abel
  rw [hd, norm_neg, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hℓ.le)] at h
  have he : L * (ℓ⁻¹ * ‖t‖) = L / ℓ * ‖t‖ := by ring
  rw [he] at h
  exact h

/-! ## 2. The scaled integrable profile of the smearing kernel -/

/-- The scaled profile `t ↦ (1 + Λ‖t‖)^{-4}` is integrable for `Λ > 0`: `4 > 3 = dim ℝ³`. -/
private lemma integrable_one_add_mul_norm_zpow {Λ : ℝ} (hΛ : 0 < Λ) :
    Integrable (fun t : E3 => (1 + Λ * ‖t‖) ^ (-(4 : ℤ))) := by
  have h1 : Integrable (fun t : E3 => (1 + ‖Λ • t‖) ^ (-(4 : ℤ))) :=
    (Work.BoseBoxFock.integrable_one_add_norm_zpow 4 (by norm_num)).comp_smul hΛ.ne'
  refine h1.congr (Filter.Eventually.of_forall fun t => ?_)
  simp only [norm_smul, Real.norm_of_nonneg hΛ.le]

/-- **The scaling of the profile**: `∫ t, (1 + Λ‖t‖)^{-4} = (∫ y, (1 + ‖y‖)^{-4})/Λ³`. -/
private lemma integral_one_add_mul_norm_neg_four {Λ : ℝ} (hΛ : 0 < Λ) :
    ∫ t : E3, (1 + Λ * ‖t‖) ^ (-(4 : ℤ))
      = (∫ y : E3, (1 + ‖y‖) ^ (-(4 : ℤ))) / Λ ^ 3 := by
  have h : ∫ t : E3, (1 + ‖Λ • t‖) ^ (-(4 : ℤ))
      = |(Λ ^ 3)⁻¹| * ∫ y : E3, (1 + ‖y‖) ^ (-(4 : ℤ)) := by
    have h0 := Measure.integral_comp_smul (μ := (volume : Measure E3))
      (f := fun y : E3 => (1 + ‖y‖) ^ (-(4 : ℤ))) Λ
    rw [show Module.finrank ℝ E3 = 3 from by rw [finrank_euclideanSpace]; simp] at h0
    simpa using h0
  rw [show (∫ t : E3, (1 + ‖Λ • t‖) ^ (-(4 : ℤ)))
      = ∫ t : E3, (1 + Λ * ‖t‖) ^ (-(4 : ℤ)) from
    integral_congr_ae (Filter.Eventually.of_forall fun t => by
      simp only [norm_smul, Real.norm_of_nonneg hΛ.le])] at h
  rw [h, abs_of_pos (inv_pos.mpr (by positivity : (0 : ℝ) < Λ ^ 3)), inv_mul_eq_div]

/-! ## 3. The interchange identity (the analytic core) -/

/-- **The UV-smearing error paired against a smooth weight: the interchange identity.**

For integrable `f`, `K` and a *continuous, bounded* localisation `χ`,

    `∫ w, χ(w)·(∫ t, K(t)(f(z−w−t) − f(z−w))) = ∫ t, K(t)·(∫ u, (χ(u−t) − χ(u))·f(z−u))`.

The two sides are the same double integral, rearranged: in the `t`-direction one uses the
translation invariance `∫ w χ(w) f(z−w−t) dw = ∫ u χ(u−t) f(z−u) du` (with `u = w + t`), which
moves the `t`-difference from `f` onto `χ`.  This is exactly why the smoothness of `χ` (and
*not* any regularity of `f`) controls the error.

Formal proof: `Φ(w,t) = χ(w)(K(t)(f(z−w−t) − f(z−w)))` is product-integrable (the first summand
is the convolution integrand `K(t)f(v−t)` under the measure-preserving change `w ↦ z−w`, the
second is separable), `integral_integral_swap` gives the Fubini step, and the inner integral is
rearranged pointwise in `t`. -/
theorem smear_interchange {χ K f : E3 → ℝ} {z : E3} {Cχ : ℝ}
    (hχc : Continuous χ) (hχbdd : ∀ x : E3, ‖χ x‖ ≤ Cχ)
    (hK : Integrable K) (hf : Integrable f) :
    ∫ w : E3, χ w * (∫ t : E3, K t * (f (z - w - t) - f (z - w)))
      = ∫ t : E3, K t * (∫ u : E3, (χ (u - t) - χ u) * f (z - u)) := by
  -- the `χ (y - ·) f` integrability pattern
  have hχmul : ∀ y : E3, Integrable (fun w : E3 => χ w * f (y - w)) := by
    intro y
    have h1 : Integrable (fun w : E3 => f (y - w) * χ w) :=
      (hf.comp_sub_left y).mul_bdd (c := Cχ) hχc.aestronglyMeasurable
        (Filter.Eventually.of_forall fun w => hχbdd w)
    exact h1.congr (Filter.Eventually.of_forall fun w => mul_comm _ _)
  -- product integrability of the double integrand
  have hΦ : Integrable (fun p : E3 × E3 =>
      χ p.1 * (K p.2 * (f (z - p.1 - p.2) - f (z - p.1)))) (volume.prod volume) := by
    have hA : Integrable (fun p : E3 × E3 =>
        K p.2 * f (p.1 - p.2)) (volume.prod volume) := by
      have h := Integrable.convolution_integrand (L := ContinuousLinearMap.lsmul ℝ ℝ)
        (f := K) (g := f) (μ := (volume : Measure E3)) (ν := (volume : Measure E3)) hK hf
      simpa [ContinuousLinearMap.lsmul_apply, smul_eq_mul] using h
    have hχc' : Continuous (fun p : E3 × E3 => χ (z - p.1)) :=
      hχc.comp (continuous_const.sub continuous_fst)
    have hA2 : Integrable (fun p : E3 × E3 =>
        K p.2 * f (p.1 - p.2) * χ (z - p.1)) (volume.prod volume) :=
      hA.mul_bdd (c := Cχ) hχc'.aestronglyMeasurable
        (Filter.Eventually.of_forall fun p => hχbdd _)
    have hmp1 : MeasurePreserving (fun w : E3 => z - w) (volume : Measure E3)
        (volume : Measure E3) :=
      (measurePreserving_add_left _ z).comp (Measure.measurePreserving_neg _)
    have hmp : MeasurePreserving (Prod.map (fun w : E3 => z - w) (id : E3 → E3))
        ((volume : Measure E3).prod volume) ((volume : Measure E3).prod volume) :=
      hmp1.prod (MeasurePreserving.id _)
    have hΦ₁ : Integrable (fun p : E3 × E3 =>
        χ p.1 * (K p.2 * f (z - p.1 - p.2))) (volume.prod volume) :=
      ((hmp.integrable_comp hA2.aestronglyMeasurable).mpr hA2).congr
        (Filter.Eventually.of_forall fun p => by
          simp only [Function.comp_apply, Prod.map_fst, Prod.map_snd, id_eq, sub_sub_self]
          ring)
    have hχf : Integrable (fun w : E3 => χ w * f (z - w)) := hχmul z
    have hΦ₂ : Integrable (fun p : E3 × E3 =>
        χ p.1 * (K p.2 * f (z - p.1))) (volume.prod volume) := by
      have h1 : Integrable (fun p : E3 × E3 =>
          (χ p.1 * f (z - p.1)) * K p.2) (volume.prod volume) :=
        Integrable.mul_prod hχf hK
      exact h1.congr (Filter.Eventually.of_forall fun p => by ring)
    exact (hΦ₁.sub hΦ₂).congr
      (Filter.Eventually.of_forall fun p => by simp only [Pi.sub_apply]; ring)
  calc ∫ w : E3, χ w * (∫ t : E3, K t * (f (z - w - t) - f (z - w)))
      = ∫ w : E3, ∫ t : E3, χ w * (K t * (f (z - w - t) - f (z - w))) := by
        apply integral_congr_ae
        filter_upwards with w
        rw [integral_const_mul]
    _ = ∫ t : E3, ∫ w : E3, χ w * (K t * (f (z - w - t) - f (z - w))) :=
        integral_integral_swap hΦ
    _ = ∫ t : E3, K t * (∫ u : E3, (χ (u - t) - χ u) * f (z - u)) := by
        apply integral_congr_ae
        filter_upwards with t
        have harg : ∀ w : E3, (z - t) - w = z - w - t := fun w => by abel
        have hA : Integrable (fun w : E3 => χ w * f (z - w - t)) :=
          (hχmul (z - t)).congr (Filter.Eventually.of_forall fun w => by simp only [harg w])
        have hC : Integrable (fun u : E3 => χ (u - t) * f (z - u)) := by
          have h1 : Integrable (fun u : E3 => f (z - u) * χ (u - t)) :=
            (hf.comp_sub_left z).mul_bdd (c := Cχ)
              ((hχc.comp (continuous_id.sub continuous_const)).aestronglyMeasurable)
              (Filter.Eventually.of_forall fun u => hχbdd _)
          exact h1.congr (Filter.Eventually.of_forall fun u => mul_comm _ _)
        have hsplit : ∫ w : E3, χ w * (f (z - w - t) - f (z - w))
            = (∫ w : E3, χ w * f (z - w - t))
              - ∫ w : E3, χ w * f (z - w) := by
          rw [show (∫ w : E3, χ w * (f (z - w - t) - f (z - w)))
              = ∫ w : E3, (χ w * f (z - w - t) - χ w * f (z - w)) from
              integral_congr_ae (Filter.Eventually.of_forall fun w => by ring)]
          rw [integral_sub hA (hχmul z)]
        have hshift : ∫ w : E3, χ w * f (z - w - t)
            = ∫ u : E3, χ (u - t) * f (z - u) := by
          have h1 : ∫ w : E3, χ w * f (z - w - t)
              = ∫ w : E3, (fun v : E3 => χ (v - t) * f (z - v)) (w + t) := by
            apply integral_congr_ae
            filter_upwards with w
            have ha : (w + t) - t = w := add_sub_cancel_right w t
            have hb : z - (w + t) = z - w - t := by abel
            rw [ha, hb]
          rw [h1]
          exact integral_add_right_eq_self (fun v : E3 => χ (v - t) * f (z - v)) t
        rw [show (∫ w : E3, χ w * (K t * (f (z - w - t) - f (z - w))))
            = ∫ w : E3, K t * (χ w * (f (z - w - t) - f (z - w))) from
            integral_congr_ae (Filter.Eventually.of_forall fun w => by ring)]
        rw [integral_const_mul]
        congr 1
        rw [hsplit, hshift]
        rw [← integral_sub hC (hχmul z)]
        apply integral_congr_ae
        filter_upwards with u
        ring

/-! ## 4. The target -/

theorem chiStarE_le {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : Work.UBB.ScatSol v}
    {fu : Work.BoseBoxFix.LowCut} {ℓ : ℝ} (hℓ : 0 < ℓ)
    (hI : MeasureTheory.Integrable (Work.BoseFixR.W1fun v h ℓ)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (Λ : ℝ), 1 ≤ Λ → ∀ z : EuclideanSpace ℝ (Fin 3),
      |∫ w : EuclideanSpace ℝ (Fin 3), (Work.BoseK15.corpusBox.chiLam ℓ w) *
          (Work.BoseBoxFock.uvSmear fu Λ (Work.BoseFixR.W1fun v h ℓ) (z - w)
            - Work.BoseFixR.W1fun v h ℓ (z - w))| ≤ C / Λ := by
  obtain ⟨L, hL0, hLip⟩ := chiLam_lipschitz_shift
  obtain ⟨Cχ, _hCχ0, hCχ⟩ := chiLam_bound
  obtain ⟨Cd, hCd0, hdec⟩ := Work.BoseBoxFock.uvKernel_decay fu 5
  refine ⟨Cd * (L / ℓ) * (∫ x : E3, |Work.BoseFixR.W1fun v h ℓ x|)
      * (∫ y : E3, (1 + ‖y‖) ^ (-(4 : ℤ))), ?_, ?_⟩
  · have h1 : 0 ≤ L / ℓ := div_nonneg hL0 hℓ.le
    have h2 : 0 ≤ ∫ x : E3, |Work.BoseFixR.W1fun v h ℓ x| :=
      integral_nonneg fun x => abs_nonneg _
    have h3 : 0 ≤ ∫ y : E3, (1 + ‖y‖) ^ (-(4 : ℤ)) :=
      integral_nonneg fun y => zpow_nonneg (by positivity) _
    exact mul_nonneg (mul_nonneg (mul_nonneg hCd0 h1) h2) h3
  · intro Λ hΛ1 z
    have hΛ : 0 < Λ := lt_of_lt_of_le zero_lt_one hΛ1
    set f : E3 → ℝ := Work.BoseFixR.W1fun v h ℓ with hfdef
    set K : E3 → ℝ := Work.BoseBoxFock.uvKernel fu Λ with hKdef
    set χ : E3 → ℝ := Work.BoseK15.corpusBox.chiLam ℓ with hχdef
    have hfint : Integrable f := by rw [hfdef]; exact hI
    have hI0 : 0 ≤ ∫ x : E3, |f x| := integral_nonneg fun x => abs_nonneg _
    have hcχ : Continuous χ := by
      rw [hχdef]; exact Work.BoseB4.BoxData.chiLam_cont Work.BoseK15.corpusBox ℓ
    have hχbdd : ∀ x : E3, ‖χ x‖ ≤ Cχ := by intro x; rw [hχdef]; exact hCχ ℓ x
    have hKint : Integrable K := by
      rw [hKdef]; exact Work.BoseBoxFock.integrable_uvKernel fu hΛ
    have hK1 : ∫ t : E3, K t = 1 := by
      rw [hKdef]; exact Work.BoseBoxFock.integral_uvKernel fu hΛ
    obtain ⟨C₁, _hC₁0, hdec1⟩ := Work.BoseBoxFock.uvKernel_decay fu 1
    have hKbdd : ∀ t : E3, ‖K t‖ ≤ C₁ * Λ ^ 3 := by
      intro t
      have h1 : (1 + Λ * ‖t‖) ^ (-(1 : ℤ)) ≤ 1 := by
        rw [zpow_neg_one]
        exact inv_le_one_of_one_le₀ (by
          have : (0 : ℝ) ≤ Λ * ‖t‖ := mul_nonneg hΛ.le (norm_nonneg t)
          linarith)
      have h2 : ‖K t‖ ≤ C₁ * Λ ^ 3 * (1 + Λ * ‖t‖) ^ (-(1 : ℤ)) := by
        rw [hKdef]; exact hdec1 Λ hΛ t
      calc ‖K t‖ ≤ C₁ * Λ ^ 3 * (1 + Λ * ‖t‖) ^ (-(1 : ℤ)) := h2
        _ ≤ C₁ * Λ ^ 3 * 1 := mul_le_mul_of_nonneg_left h1 (by positivity)
        _ = C₁ * Λ ^ 3 := by ring
    -- `uvSmear fu Λ f` as the convolution integral `∫ t, K t * f (x - t)`
    have huv : ∀ x : E3, Work.BoseBoxFock.uvSmear fu Λ f x = ∫ t : E3, K t * f (x - t) := by
      intro x
      have h2 : (∫ y : E3, K (x - y) * f (x - (x - y))) = ∫ t : E3, K t * f (x - t) :=
        MeasureTheory.integral_sub_left_eq_self (fun t : E3 => K t * f (x - t)) volume x
      rw [show Work.BoseBoxFock.uvSmear fu Λ f x = ∫ y : E3, K (x - y) * f y from by
        rw [hKdef]; rfl]
      rw [show (∫ y : E3, K (x - y) * f y) = ∫ y : E3, K (x - y) * f (x - (x - y)) from
        integral_congr_ae (Filter.Eventually.of_forall fun y => by simp only [sub_sub_self])]
      exact h2
    -- the differenced form of the smearing
    have hsub : ∀ x : E3, Work.BoseBoxFock.uvSmear fu Λ f x - f x
        = ∫ t : E3, K t * (f (x - t) - f x) := by
      intro x
      rw [huv x]
      have hcx : MeasureTheory.convolution K f (ContinuousLinearMap.lsmul ℝ ℝ) volume x
          = ∫ t : E3, K t * f (x - t) := by
        rw [MeasureTheory.convolution_lsmul]; simp only [smul_eq_mul]
      rw [← hcx]
      exact Work.BoseBoxFock.convolution_sub_eq_integral hfint hKint hK1 hKbdd x
    -- the exact form of the LHS
    have hmain : ∫ w : E3, χ w * (Work.BoseBoxFock.uvSmear fu Λ f (z - w) - f (z - w))
        = ∫ t : E3, K t * (∫ u : E3, (χ (u - t) - χ u) * f (z - u)) := by
      calc ∫ w : E3, χ w * (Work.BoseBoxFock.uvSmear fu Λ f (z - w) - f (z - w))
          = ∫ w : E3, χ w * (∫ t : E3, K t * (f (z - w - t) - f (z - w))) := by
              apply integral_congr_ae
              filter_upwards with w
              rw [hsub (z - w)]
        _ = ∫ t : E3, K t * (∫ u : E3, (χ (u - t) - χ u) * f (z - u)) :=
              smear_interchange hcχ hχbdd hKint hfint
    rw [hmain]
    -- the inner integral is bounded by the Lipschitz constant of `χ`
    have hInner : ∀ t : E3, |∫ u : E3, (χ (u - t) - χ u) * f (z - u)|
        ≤ L / ℓ * ‖t‖ * (∫ x : E3, |f x|) := by
      intro t
      have h1 : |∫ u : E3, (χ (u - t) - χ u) * f (z - u)|
          ≤ ∫ u : E3, |χ (u - t) - χ u| * |f (z - u)| := by
        calc |∫ u : E3, (χ (u - t) - χ u) * f (z - u)|
            ≤ ∫ u : E3, |(χ (u - t) - χ u) * f (z - u)| := abs_integral_le_integral_abs
          _ = ∫ u : E3, |χ (u - t) - χ u| * |f (z - u)| := by
              apply integral_congr_ae
              filter_upwards with u
              rw [abs_mul]
      have h2 : ∫ u : E3, |χ (u - t) - χ u| * |f (z - u)|
          ≤ ∫ u : E3, (L / ℓ * ‖t‖) * |f (z - u)| := by
        refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun u => by positivity)
          ((hfint.abs.comp_sub_left z).const_mul _) (Filter.Eventually.of_forall fun u => ?_)
        exact mul_le_mul_of_nonneg_right (hLip ℓ hℓ u t) (abs_nonneg _)
      have h3 : ∫ u : E3, (L / ℓ * ‖t‖) * |f (z - u)| = (L / ℓ * ‖t‖) * ∫ x : E3, |f x| := by
        rw [MeasureTheory.integral_const_mul]
        congr 1
        exact MeasureTheory.integral_sub_left_eq_self (fun x : E3 => |f x|) volume z
      exact h1.trans (h2.trans (le_of_eq h3))
    -- the explicit integrable majorant `c (1 + Λ‖t‖)^{-4}`
    set c : ℝ := Cd * Λ ^ 2 * (L / ℓ) * (∫ x : E3, |f x|) with hcdef
    have hintg : Integrable (fun t : E3 => c * (1 + Λ * ‖t‖) ^ (-(4 : ℤ))) :=
      (integrable_one_add_mul_norm_zpow hΛ).const_mul c
    have hbound : ∀ t : E3, |K t| * |∫ u : E3, (χ (u - t) - χ u) * f (z - u)|
        ≤ c * (1 + Λ * ‖t‖) ^ (-(4 : ℤ)) := by
      intro t
      have hkt : |K t| ≤ Cd * Λ ^ 3 * (1 + Λ * ‖t‖) ^ (-(5 : ℤ)) := by
        rw [hKdef, ← Real.norm_eq_abs]; exact hdec Λ hΛ t
      have hat := hInner t
      have h2 : (0 : ℝ) < 1 + Λ * ‖t‖ := by
        have : (0 : ℝ) ≤ Λ * ‖t‖ := mul_nonneg hΛ.le (norm_nonneg t)
        linarith
      have h1 : (0 : ℝ) ≤ (1 + Λ * ‖t‖) ^ (-(5 : ℤ)) := zpow_nonneg (by positivity) _
      have h3 : (1 + Λ * ‖t‖) ^ (-(5 : ℤ)) * ‖t‖ ≤ (1 + Λ * ‖t‖) ^ (-(4 : ℤ)) / Λ := by
        have h4 : ‖t‖ ≤ (1 + Λ * ‖t‖) / Λ := by rw [le_div_iff₀ hΛ]; linarith
        calc (1 + Λ * ‖t‖) ^ (-(5 : ℤ)) * ‖t‖
            ≤ (1 + Λ * ‖t‖) ^ (-(5 : ℤ)) * ((1 + Λ * ‖t‖) / Λ) :=
              mul_le_mul_of_nonneg_left h4 h1
          _ = (1 + Λ * ‖t‖) ^ (-(4 : ℤ)) / Λ := by
              have h5 : (1 + Λ * ‖t‖) ^ (-(5 : ℤ)) * (1 + Λ * ‖t‖)
                  = (1 + Λ * ‖t‖) ^ (-(4 : ℤ)) := by
                have h5a : (1 + Λ * ‖t‖) ^ (-(5 : ℤ) + 1)
                    = (1 + Λ * ‖t‖) ^ (-(5 : ℤ)) * (1 + Λ * ‖t‖) ^ (1 : ℤ) :=
                  zpow_add₀ h2.ne' _ _
                rw [zpow_one, show (-(5 : ℤ) + 1) = -(4 : ℤ) by norm_num] at h5a
                exact h5a.symm
              rw [← mul_div_assoc, h5]
      calc |K t| * |∫ u : E3, (χ (u - t) - χ u) * f (z - u)|
          ≤ (Cd * Λ ^ 3 * (1 + Λ * ‖t‖) ^ (-(5 : ℤ)))
              * (L / ℓ * ‖t‖ * (∫ x : E3, |f x|)) :=
            mul_le_mul hkt hat (abs_nonneg _) (by positivity)
        _ = c * Λ * ((1 + Λ * ‖t‖) ^ (-(5 : ℤ)) * ‖t‖) := by rw [hcdef]; ring
        _ ≤ c * Λ * ((1 + Λ * ‖t‖) ^ (-(4 : ℤ)) / Λ) :=
            mul_le_mul_of_nonneg_left h3 (by positivity)
        _ = c * (1 + Λ * ‖t‖) ^ (-(4 : ℤ)) := by
            field_simp
    have hintval : ∫ t : E3, c * (1 + Λ * ‖t‖) ^ (-(4 : ℤ))
        = c * ((∫ y : E3, (1 + ‖y‖) ^ (-(4 : ℤ))) / Λ ^ 3) := by
      rw [MeasureTheory.integral_const_mul, integral_one_add_mul_norm_neg_four hΛ]
    calc |∫ t : E3, K t * (∫ u : E3, (χ (u - t) - χ u) * f (z - u))|
        ≤ ∫ t : E3, |K t| * |∫ u : E3, (χ (u - t) - χ u) * f (z - u)| := by
          refine (abs_integral_le_integral_abs).trans (le_of_eq ?_)
          apply integral_congr_ae
          filter_upwards with t
          rw [abs_mul]
      _ ≤ ∫ t : E3, c * (1 + Λ * ‖t‖) ^ (-(4 : ℤ)) :=
          integral_mono_of_nonneg (Filter.Eventually.of_forall fun t => by positivity) hintg
            (Filter.Eventually.of_forall fun t => hbound t)
      _ = c * ((∫ y : E3, (1 + ‖y‖) ^ (-(4 : ℤ))) / Λ ^ 3) := hintval
      _ = Cd * (L / ℓ) * (∫ x : E3, |f x|) * (∫ y : E3, (1 + ‖y‖) ^ (-(4 : ℤ))) / Λ := by
          rw [hcdef]; field_simp

end

end Work.BoseBoxFock.PCFU
