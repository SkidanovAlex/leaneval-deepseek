import Mathlib.Order.CompletePartialOrder
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Submission.Work.BoseFixB1.KH._tmpIBP
import Submission.Work.BoseFixB1.KH.chiB_iteratedFDeriv_le
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1.KH.chiB_kinFT_decay`

**The Fourier decay of the sliding window, with the box volume as weight.**

    ‖kinFT (χ_{B(u)}) p‖ ≤ C·|B(u)| / (1 + (ℓd)‖p‖)^K

for every `K`, uniformly in `ℓ, d, u, p` (with `0 < ℓ`, `0 < d ≤ 1`).

The window `χ_{B(u)} = chiB ℓ d u = χ_ℓ · (χ_{ℓd}(· − ℓd·u))` is `C^∞` with support in the
sliding box `B(u) = dlBox ℓ d u`, whose volume is `Work.SmallBoxSliding.boxMass ℓ d u`.  The
proof is the standard two-bound argument for a bump concentrated in a box of side `ℓd`:

* the **low-frequency** bound `‖kinFT f p‖ ≤ ∫‖f‖ ≤ chiSupAbs²·|B(u)|` (only `|f| ≤ chiSupAbs²`
  and the support containment `supp χ_{B(u)} ⊆ B(u)` are used);
* the **high-frequency** bound `(ℓd‖p‖)^K‖kinFT f p‖ ≤ |B(u)|·D_K`, obtained from integration by
  parts: `‖p‖^K‖kinFT f p‖ ≤ ∫‖D^K f‖ ≤ |B(u)|·D_K(ℓd)^{-K}`, where `D_K(ℓd)^{-K}` is the
  uniform `K`-th derivative bound for `χ_{B(u)}` (two-scale Leibniz rule; here `d ≤ 1` is used to
  replace the small factor `ℓ^{-j}` by the larger `(ℓd)^{-j}`);
* combining with `(1+x)^K ≤ 2^K(1+x^K)` for `x = (ℓd)‖p‖`.

The two analytic inputs are the delegated lemmas
`Work.BoseFixB1.KH.chiB_iteratedFDeriv_le` (the derivative bound) and
`Work.BoseFixB1.KH.fourier_pow_norm_le` (the integration-by-parts bound).
-/

noncomputable section

open MeasureTheory
open scoped ContDiff Topology Real BigOperators FourierTransform

namespace Work.BoseFixB1.KH

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false

/-! ## 1. Pointwise bounds and smoothness of the window -/

/-- `|χ_{B(u)}| ≤ chiSupAbs²` pointwise (both factors are bounded by `chiSupAbs`). -/
lemma norm_chiB_le_sup_sq (ℓ d : ℝ) (u z : E3) :
    ‖((Submission.BoseGases.chiB ℓ d u z : ℝ) : ℂ)‖
      ≤ Submission.BoseGases.chiSupAbs ^ 2 := by
  have h1 := Submission.BoseGases.chiScale_abs_le_sup ℓ z
  have h2 := Submission.BoseGases.chiScale_abs_le_sup (ℓ * d) (z - (ℓ * d) • u)
  have hC : ((Submission.BoseGases.chiB ℓ d u z : ℝ) : ℂ)
      = ((Submission.BoseGases.chiScale ℓ z : ℝ) : ℂ)
        * ((Submission.BoseGases.chiScale (ℓ * d) (z - (ℓ * d) • u) : ℝ) : ℂ) := by
    simp only [Submission.BoseGases.chiB]
    push_cast
    ring
  rw [hC, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs]
  calc |Submission.BoseGases.chiScale ℓ z|
        * |Submission.BoseGases.chiScale (ℓ * d) (z - (ℓ * d) • u)|
      ≤ Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSupAbs :=
        mul_le_mul h1 h2 (abs_nonneg _) Submission.BoseGases.chiSupAbs_nonneg
    _ = Submission.BoseGases.chiSupAbs ^ 2 := by ring

/-- `χ_{B(u)}` vanishes off the sliding box. -/
lemma chiB_eq_zero_of_not_mem {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d)
    (u z : E3) (hz : z ∉ Submission.BoseGases.dlBox ℓ d u) :
    Submission.BoseGases.chiB ℓ d u z = 0 := by
  by_contra h
  exact hz (Submission.BoseGases.chiB_support_mem hℓ hd u z h)

/-- The complexified window is dominated by the (scalar) box indicator. -/
lemma norm_chiB_le_ind {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d) (u z : E3) :
    ‖((Submission.BoseGases.chiB ℓ d u z : ℝ) : ℂ)‖
      ≤ Submission.BoseGases.chiSupAbs ^ 2 * Work.SmallBoxSliding.boxInd ℓ d u z := by
  by_cases hz : z ∈ Submission.BoseGases.dlBox ℓ d u
  · rw [Work.SmallBoxSliding.boxInd, Set.indicator_of_mem hz, mul_one]
    exact norm_chiB_le_sup_sq ℓ d u z
  · have hzero := chiB_eq_zero_of_not_mem hℓ hd u z hz
    rw [Work.SmallBoxSliding.boxInd, Set.indicator_of_notMem hz, mul_zero, hzero]
    simp

/-- The support of the complexified window lies in the sliding box. -/
lemma support_chiB_subset {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d) (u : E3) :
    Function.support (fun z : E3 => ((Submission.BoseGases.chiB ℓ d u z : ℝ) : ℂ))
      ⊆ Submission.BoseGases.dlBox ℓ d u := by
  intro z hz
  exact Submission.BoseGases.chiB_support_mem hℓ hd u z (by simpa using hz)

/-- The centred cube `acube ℓ` is closed. -/
lemma isClosed_acube (ℓ : ℝ) : IsClosed (Submission.BoseGases.acube ℓ) := by
  rw [show Submission.BoseGases.acube ℓ
      = ⋂ m : Fin 3, (fun y : E3 => y m) ⁻¹' Set.Icc (-ℓ / 2) (ℓ / 2) by
    ext y
    simp [Submission.BoseGases.acube, Set.mem_iInter]]
  exact isClosed_iInter fun m => isClosed_Icc.preimage (by fun_prop)

/-- The sliding box `B(u) = dlBox ℓ d u` is closed. -/
lemma isClosed_dlBox (ℓ d : ℝ) (u : E3) : IsClosed (Submission.BoseGases.dlBox ℓ d u) := by
  rw [show Submission.BoseGases.dlBox ℓ d u = Submission.BoseGases.acube ℓ
      ∩ (fun x : E3 => x - (ℓ * d) • u) ⁻¹' Submission.BoseGases.acube (ℓ * d) by
    ext x
    rw [Submission.BoseGases.mem_dlBox_iff, Set.mem_inter_iff, Set.mem_preimage]]
  exact (isClosed_acube ℓ).inter ((isClosed_acube (ℓ * d)).preimage (by fun_prop))

/-- The closed support of the complexified window lies in the sliding box. -/
lemma tsupport_chiB_subset {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d) (u : E3) :
    tsupport (fun z : E3 => ((Submission.BoseGases.chiB ℓ d u z : ℝ) : ℂ))
      ⊆ Submission.BoseGases.dlBox ℓ d u :=
  closure_minimal (support_chiB_subset hℓ hd u) (isClosed_dlBox ℓ d u)

/-- The complexified window is compactly supported (`χ_B` is a multiple of `χ_ℓ`, which is). -/
lemma hasCompactSupport_chiB {ℓ d : ℝ} (hℓ : 0 < ℓ) (u : E3) :
    HasCompactSupport (fun z : E3 => ((Submission.BoseGases.chiB ℓ d u z : ℝ) : ℂ)) := by
  have hreal : HasCompactSupport (fun z : E3 => Submission.BoseGases.chiB ℓ d u z) :=
    (Submission.BoseGases.chiScale_hasCompactSupport (ne_of_gt hℓ)).mono fun z hz => by
      simp only [Function.mem_support] at hz ⊢
      intro h
      exact hz (by simp [Submission.BoseGases.chiB, h])
  exact hreal.comp_left (by simp : Complex.ofReal 0 = 0)

/-- The `K`-th iterated derivative of the complexified window is supported in `B(u)`. -/
lemma support_iteratedFDeriv_chiB_subset {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d)
    (u : E3) (K : ℕ) :
    Function.support
        (iteratedFDeriv ℝ K (fun z : E3 => ((Submission.BoseGases.chiB ℓ d u z : ℝ) : ℂ)))
      ⊆ Submission.BoseGases.dlBox ℓ d u :=
  (support_iteratedFDeriv_subset (𝕜 := ℝ) (f := fun z : E3 =>
      ((Submission.BoseGases.chiB ℓ d u z : ℝ) : ℂ)) K).trans (tsupport_chiB_subset hℓ hd u)

/-- `chiScale s` is `C^K` for every `K` (and `s ≠ 0`). -/
lemma contDiff_chiScale_nat {s : ℝ} (hs : s ≠ 0) (k : ℕ) :
    ContDiff ℝ (k : ℕ∞) (Submission.BoseGases.chiScale s) :=
  (Submission.BoseGases.chiScale_contDiff hs).of_le (WithTop.coe_le_coe.mpr le_top)

/-- The complexified window is `C^K` for every `K`. -/
lemma contDiff_chiB_complex {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d) (u : E3) (K : ℕ) :
    ContDiff ℝ (K : ℕ∞) (fun z : E3 => ((Submission.BoseGases.chiB ℓ d u z : ℝ) : ℂ)) := by
  have hℓne : ℓ ≠ 0 := ne_of_gt hℓ
  have hldne : ℓ * d ≠ 0 := mul_ne_zero hℓne (ne_of_gt hd)
  have h1 : ContDiff ℝ (K : ℕ∞)
      (fun z : E3 => (Submission.BoseGases.chiScale ℓ z : ℂ)) :=
    (contDiff_chiScale_nat hℓne K).continuousLinearMap_comp Complex.ofRealCLM
  have h2 : ContDiff ℝ (K : ℕ∞)
      (fun z : E3 => (Submission.BoseGases.chiScale (ℓ * d) (z - (ℓ * d) • u) : ℂ)) := by
    have hinner : ContDiff ℝ (K : ℕ∞) (fun z : E3 => z - (ℓ * d) • u) :=
      (contDiff_id.sub contDiff_const).of_le le_top
    exact ((contDiff_chiScale_nat hldne K).comp hinner).continuousLinearMap_comp
      Complex.ofRealCLM
  have hprod : (fun z : E3 => ((Submission.BoseGases.chiB ℓ d u z : ℝ) : ℂ))
      = (fun z : E3 => (Submission.BoseGases.chiScale ℓ z : ℂ))
        * (fun z : E3 => (Submission.BoseGases.chiScale (ℓ * d) (z - (ℓ * d) • u) : ℂ)) := by
    funext z
    simp only [Pi.mul_apply, Submission.BoseGases.chiB]
    push_cast
    ring
  rw [hprod]
  exact h1.mul h2

/-! ## 2. Integrability of the box indicator -/

lemma integrable_boxInd {ℓ d : ℝ} (hℓ : 0 < ℓ) (u : E3) :
    Integrable (Work.SmallBoxSliding.boxInd ℓ d u) := by
  rw [show Work.SmallBoxSliding.boxInd ℓ d u
      = (Submission.BoseGases.dlBox ℓ d u).indicator (fun _ => (1 : ℝ)) from rfl]
  exact (integrableOn_const (C := (1 : ℝ))
    (ne_of_lt (Work.SmallBoxSliding.volume_dlBox_lt_top hℓ d u))).integrable_indicator
    (Work.SmallBoxSliding.measurableSet_dlBox ℓ d u)

/-! ## 3. The two bounds -/

/-- **Low frequencies**: `‖kinFT f p‖ ≤ chiSupAbs²·|B(u)|`. -/
lemma kinFT_chiB_le_boxMass {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d) (u : E3) (p : E3) :
    ‖Submission.BoseGases.kinFT
        (fun z : E3 => ((Submission.BoseGases.chiB ℓ d u z : ℝ) : ℂ)) p‖
      ≤ Submission.BoseGases.chiSupAbs ^ 2 * Work.SmallBoxSliding.boxMass ℓ d u := by
  have hmaj : Integrable (fun z : E3 =>
      Submission.BoseGases.chiSupAbs ^ 2 * Work.SmallBoxSliding.boxInd ℓ d u z) :=
    (integrable_boxInd hℓ u).const_mul _
  have h1 : ‖Submission.BoseGases.kinFT
        (fun z : E3 => ((Submission.BoseGases.chiB ℓ d u z : ℝ) : ℂ)) p‖
      ≤ ∫ z : E3, ‖((Submission.BoseGases.chiB ℓ d u z : ℝ) : ℂ)‖ := by
    rw [Submission.BoseGases.kinFT]
    refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
    apply integral_congr_ae
    filter_upwards with z
    rw [norm_mul,
      show -(Complex.I * (inner ℝ p z : ℂ)) = ((-(inner ℝ p z) : ℝ) : ℂ) * Complex.I by
        push_cast; ring,
      Complex.norm_exp_ofReal_mul_I, one_mul]
  refine h1.trans ?_
  calc ∫ z : E3, ‖((Submission.BoseGases.chiB ℓ d u z : ℝ) : ℂ)‖
      ≤ ∫ z : E3, Submission.BoseGases.chiSupAbs ^ 2 * Work.SmallBoxSliding.boxInd ℓ d u z :=
        integral_mono_of_nonneg (ae_of_all _ (fun z => norm_nonneg _)) hmaj
          (ae_of_all _ (fun z => norm_chiB_le_ind hℓ hd u z))
    _ = Submission.BoseGases.chiSupAbs ^ 2 * Work.SmallBoxSliding.boxMass ℓ d u := by
        rw [integral_const_mul]
        rfl

/-- **High frequencies**: from a uniform `K`-th derivative bound `D·(ℓd)^{-K}` for the window,
`(ℓd‖p‖)^K‖kinFT f p‖ ≤ D·|B(u)|`. -/
lemma kinFT_chiB_pow_le (K : ℕ) {D : ℝ}
    (hD : ∀ (ℓ d : ℝ) (u : E3), 0 < ℓ → 0 < d → d ≤ 1 → ∀ z : E3,
      ‖iteratedFDeriv ℝ K
          (fun z : E3 => ((Submission.BoseGases.chiB ℓ d u z : ℝ) : ℂ)) z‖
        ≤ D * ((ℓ * d)⁻¹) ^ K)
    {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d) (hd1 : d ≤ 1) (u : E3) (p : E3) :
    ((ℓ * d) * ‖p‖) ^ K * ‖Submission.BoseGases.kinFT
        (fun z : E3 => ((Submission.BoseGases.chiB ℓ d u z : ℝ) : ℂ)) p‖
      ≤ D * Work.SmallBoxSliding.boxMass ℓ d u := by
  set f : E3 → ℂ := fun z : E3 => ((Submission.BoseGases.chiB ℓ d u z : ℝ) : ℂ) with hfdef
  have hcont : ContDiff ℝ (K : ℕ∞) f := contDiff_chiB_complex hℓ hd u K
  have hcs : HasCompactSupport f := hasCompactSupport_chiB hℓ u
  have hint : ∀ n : ℕ, n ≤ K → Integrable (iteratedFDeriv ℝ n f) := by
    intro n hn
    exact (ContDiff.continuous_iteratedFDeriv (𝕜 := ℝ) (m := n) (n := (K : WithTop ℕ∞))
      (by exact_mod_cast hn) hcont).integrable_of_hasCompactSupport (hcs.iteratedFDeriv n)
  -- integration by parts at the frequency `(2π)⁻¹ • p`
  have hIBP := fourier_pow_norm_le_aux K f hcont hint ((2 * π)⁻¹ • p)
  have h2pi : (0 : ℝ) < 2 * π := by positivity
  have hfreq : (2 * π) ^ K * ‖((2 * π)⁻¹ : ℝ) • p‖ ^ K = ‖p‖ ^ K := by
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (le_of_lt h2pi))]
    rw [← mul_pow, ← mul_assoc, mul_inv_cancel₀ (ne_of_gt h2pi), one_mul]
  have hkin : Submission.BoseGases.kinFT f p = FourierTransform.fourier f ((2 * π)⁻¹ • p) :=
    Work.SmallBoxBridge.Resolve.kinFT_eq_fourier f p
  -- the integral of the `K`-th derivative, via the pointwise bound and the box indicator
  have hmaj : Integrable (fun z : E3 =>
      D * ((ℓ * d)⁻¹) ^ K * Work.SmallBoxSliding.boxInd ℓ d u z) :=
    (integrable_boxInd hℓ u).const_mul _
  have hpoint : ∀ z : E3, ‖iteratedFDeriv ℝ K f z‖
      ≤ D * ((ℓ * d)⁻¹) ^ K * Work.SmallBoxSliding.boxInd ℓ d u z := by
    intro z
    by_cases hz : z ∈ Submission.BoseGases.dlBox ℓ d u
    · rw [Work.SmallBoxSliding.boxInd, Set.indicator_of_mem hz, mul_one]
      exact hD ℓ d u hℓ hd hd1 z
    · have hz' : z ∉ Function.support (iteratedFDeriv ℝ K f) :=
        fun h => hz (support_iteratedFDeriv_chiB_subset hℓ hd u K h)
      rw [Function.mem_support, not_not] at hz'
      rw [Work.SmallBoxSliding.boxInd, Set.indicator_of_notMem hz, mul_zero, hz', norm_zero]
  have hderiv : ∫ z : E3, ‖iteratedFDeriv ℝ K f z‖
      ≤ D * ((ℓ * d)⁻¹) ^ K * Work.SmallBoxSliding.boxMass ℓ d u := by
    calc ∫ z : E3, ‖iteratedFDeriv ℝ K f z‖
        ≤ ∫ z : E3, D * ((ℓ * d)⁻¹) ^ K * Work.SmallBoxSliding.boxInd ℓ d u z :=
          integral_mono_of_nonneg (ae_of_all _ (fun z => norm_nonneg _)) hmaj
            (ae_of_all _ hpoint)
      _ = D * ((ℓ * d)⁻¹) ^ K * Work.SmallBoxSliding.boxMass ℓ d u := by
          rw [integral_const_mul]
          rfl
  have hld : (ℓ * d) ^ K * ((ℓ * d)⁻¹) ^ K = 1 := by
    rw [← mul_pow, mul_inv_cancel₀ (mul_ne_zero (ne_of_gt hℓ) (ne_of_gt hd)), one_pow]
  calc ((ℓ * d) * ‖p‖) ^ K * ‖Submission.BoseGases.kinFT f p‖
      = (ℓ * d) ^ K * ((2 * π) ^ K * ‖((2 * π)⁻¹ : ℝ) • p‖ ^ K)
          * ‖FourierTransform.fourier f ((2 * π)⁻¹ • p)‖ := by
        rw [hkin, mul_pow, hfreq]
    _ = (ℓ * d) ^ K
          * ((2 * π) ^ K * ‖((2 * π)⁻¹ : ℝ) • p‖ ^ K
              * ‖FourierTransform.fourier f ((2 * π)⁻¹ • p)‖) := by ring
    _ ≤ (ℓ * d) ^ K * ∫ z : E3, ‖iteratedFDeriv ℝ K f z‖ :=
        mul_le_mul_of_nonneg_left hIBP (by positivity)
    _ ≤ (ℓ * d) ^ K * (D * ((ℓ * d)⁻¹) ^ K * Work.SmallBoxSliding.boxMass ℓ d u) :=
        mul_le_mul_of_nonneg_left hderiv (by positivity)
    _ = D * ((ℓ * d) ^ K * ((ℓ * d)⁻¹) ^ K) * Work.SmallBoxSliding.boxMass ℓ d u := by ring
    _ = D * Work.SmallBoxSliding.boxMass ℓ d u := by rw [hld, mul_one]

/-! ## 4. The decay theorem -/

theorem chiB_kinFT_decay (K : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (ℓ d : ℝ) (u p : EuclideanSpace ℝ (Fin 3)),
      0 < ℓ → 0 < d → d ≤ 1 →
      ‖Submission.BoseGases.kinFT (fun z : EuclideanSpace ℝ (Fin 3) =>
          ((Submission.BoseGases.chiB ℓ d u z : ℝ) : ℂ)) p‖
        ≤ C * Work.SmallBoxSliding.boxMass ℓ d u / (1 + (ℓ * d) * ‖p‖) ^ K := by
  obtain ⟨D, hD0, hD⟩ := chiB_iteratedFDeriv_le K
  refine ⟨2 ^ K * (Submission.BoseGases.chiSupAbs ^ 2 + D), by positivity, ?_⟩
  intro ℓ d u p hℓ hd hd1
  have hx0 : 0 ≤ (ℓ * d) * ‖p‖ := by positivity
  have hpow : (1 + (ℓ * d) * ‖p‖) ^ K ≤ 2 ^ K * (1 + ((ℓ * d) * ‖p‖) ^ K) := by
    rcases le_total ((ℓ * d) * ‖p‖) 1 with hx | hx
    · have hle : 1 + (ℓ * d) * ‖p‖ ≤ 2 := by linarith
      have h2K : (0 : ℝ) ≤ 2 ^ K := pow_nonneg (by norm_num) K
      have hxK : (0 : ℝ) ≤ ((ℓ * d) * ‖p‖) ^ K := pow_nonneg hx0 K
      calc (1 + (ℓ * d) * ‖p‖) ^ K ≤ 2 ^ K := pow_le_pow_left₀ (by positivity) hle K
        _ ≤ 2 ^ K * (1 + ((ℓ * d) * ‖p‖) ^ K) := by nlinarith
    · have hle : 1 + (ℓ * d) * ‖p‖ ≤ 2 * ((ℓ * d) * ‖p‖) := by linarith
      have h2K : (0 : ℝ) ≤ 2 ^ K := pow_nonneg (by norm_num) K
      have hxK : (0 : ℝ) ≤ ((ℓ * d) * ‖p‖) ^ K := pow_nonneg hx0 K
      calc (1 + (ℓ * d) * ‖p‖) ^ K ≤ (2 * ((ℓ * d) * ‖p‖)) ^ K :=
            pow_le_pow_left₀ (by positivity) hle K
        _ = 2 ^ K * ((ℓ * d) * ‖p‖) ^ K := mul_pow _ _ _
        _ ≤ 2 ^ K * (1 + ((ℓ * d) * ‖p‖) ^ K) := by nlinarith
  have hlow := kinFT_chiB_le_boxMass hℓ hd u p
  have hhigh := kinFT_chiB_pow_le K (D := D) hD hℓ hd hd1 u p
  rw [le_div_iff₀ (by positivity)]
  calc ‖Submission.BoseGases.kinFT (fun z : E3 =>
        ((Submission.BoseGases.chiB ℓ d u z : ℝ) : ℂ)) p‖ * (1 + (ℓ * d) * ‖p‖) ^ K
      ≤ ‖Submission.BoseGases.kinFT (fun z : E3 =>
          ((Submission.BoseGases.chiB ℓ d u z : ℝ) : ℂ)) p‖
          * (2 ^ K * (1 + ((ℓ * d) * ‖p‖) ^ K)) :=
        mul_le_mul_of_nonneg_left hpow (norm_nonneg _)
    _ = 2 ^ K * (‖Submission.BoseGases.kinFT (fun z : E3 =>
          ((Submission.BoseGases.chiB ℓ d u z : ℝ) : ℂ)) p‖
          + ((ℓ * d) * ‖p‖) ^ K * ‖Submission.BoseGases.kinFT (fun z : E3 =>
          ((Submission.BoseGases.chiB ℓ d u z : ℝ) : ℂ)) p‖) := by ring
    _ ≤ 2 ^ K * (Submission.BoseGases.chiSupAbs ^ 2 * Work.SmallBoxSliding.boxMass ℓ d u
          + D * Work.SmallBoxSliding.boxMass ℓ d u) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact add_le_add hlow hhigh
    _ = 2 ^ K * (Submission.BoseGases.chiSupAbs ^ 2 + D)
          * Work.SmallBoxSliding.boxMass ℓ d u := by ring

end Work.BoseFixB1.KH
