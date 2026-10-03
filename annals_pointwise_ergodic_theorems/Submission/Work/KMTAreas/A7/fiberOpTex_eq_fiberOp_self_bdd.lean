import Mathlib
import Submission.Work.KMTAreas.A7.mStarF_plateau
import Submission.Work.KMTAreas.A7.periodize_mStarF_one
import Submission.Work.KMTAreas.A7.FiberOpWideCutEqSelf
import Submission.Work.KMTAreas.A7.cw_etaCut_decay
import Submission.Work.KMTAreas.A7.KmtKernelL1Uniform

set_option maxHeartbeats 2000000

/-!
# The gate identity for the fibre of the §6 model operator

`Work.KMTAreas.A7.fiberOpTex_eq_fiberOp_self_bdd`: the fibre of the twisted projection at the
residue `n₀`, applied to the exact-height projection `Tex ρ l φ f`, equals the fibre of `φ`
itself:

  `fiberOp ρ l (mStarF U) n₀ (Tex ρ l φ f) = fiberOp ρ l φ n₀ f`

whenever `φ` is supported in the ball of radius `2^{-2U-1}`, its coefficients are `ℓ¹`, and the
exact-height arithmetic frequency set is non-aliasing at the scale `-2U`.

The mathematical content is the aliasing/plateau collapse of §6 (`form-1`) at the level of the
kernel convolution: the wider cut `m_* = mStarF U = η_{≤-2U}` is `1` on the packet of `φ` and
supported in the arc of twice the radius, so—by non-aliasing—it disappears from the product of
the symbols, leaving the fibre of `φ`.  The proof is the multiplier calculus in the `ℓ¹`(kernel)
form: Poisson summation identifies the kernel of the fibre with the Fourier coefficients of the
*twisted* Ionescu–Wainger symbol `twistSymSet (ℚ/ℤ)_l (periodize m) n₀`, and the composition is
reduced (via the product theorem for Fourier coefficients `fourierCoeff_mul_l1` and the
associativity of `tsum`-convolution `tsum_conv_conv`) to the *pointwise* gate
`fiberOpTex_twistSymSet_mul_iwSymbolSet`, which is the elementary aliasing collapse
(`Work.KMTAreas.A7.aliasingSymbolProduct`).
-/

namespace Work.KMTAreas.A7

open MeasureTheory Finset
open scoped BigOperators
open Work.Analysis.IonescuWainger

noncomputable section

local notation "Circ" => Work.Analysis.IonescuWainger.Circle

/-! ## Elementary facts about arcs, non-aliasing and periodisations -/

/-- `2 · 2^{k-1} = 2^k`. -/
lemma fiberOpTex_two_mul_zpow_pred (k : ℤ) : (2 : ℝ) * (2 : ℝ) ^ (k - 1) = (2 : ℝ) ^ k := by
  rw [show k = k - 1 + 1 by ring, zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0), zpow_one]
  ring

/-- **Non-aliasing separates the arcs.**  If the arcs `α + ℝ_{≤k}` are pairwise disjoint
(`NonAliasing k A`), then the arcs of radius `2^k` around two distinct elements of `A` are
disjoint. -/
lemma fiberOpTex_arcSet_sep_of_nonAliasing {k : ℤ} {A : Finset Circ}
    (hna : NonAliasing k A) :
    ∀ a ∈ A, ∀ b ∈ A, ∀ t : Circ,
      t ∈ Work.BourgainPlan.IonescuWainger.arcSet a ((2 : ℝ) ^ k) →
      t ∈ Work.BourgainPlan.IonescuWainger.arcSet b ((2 : ℝ) ^ k) → a = b := by
  intro a ha b hb t ht1 ht2
  obtain ⟨θ, hθ, rfl⟩ := ht1
  obtain ⟨θ', hθ', heq⟩ := ht2
  have hθm : θ ∈ realArc k := by
    rw [realArc, Set.mem_Icc]; exact abs_le.mp hθ
  have hθ'm : θ' ∈ realArc k := by
    rw [realArc, Set.mem_Icc]; exact abs_le.mp hθ'
  exact (hna a ha b hb θ hθm θ' hθ'm heq).1

/-- **A nonvanishing periodisation detects a real representative in the support.**  If `m`
vanishes off `[-δ,δ]` and `periodize m θ ≠ 0`, then `θ` is the image of some real `θ₀` with
`|θ₀| ≤ δ` (some translate `x + k` of the canonical representative `x ∈ [0,1)` of `θ` carries a
nonzero value of `m`). -/
lemma fiberOpTex_exists_coe_abs_le_of_periodize_ne_zero {m : ℝ → ℂ} {δ : ℝ}
    (hsupp : ∀ y : ℝ, m y ≠ 0 → |y| ≤ δ) {θ : Circ} (h : periodize m θ ≠ 0) :
    ∃ θ₀ : ℝ, |θ₀| ≤ δ ∧ (θ₀ : Circ) = θ := by
  set x : ℝ := (AddCircle.equivIco (1 : ℝ) 0 θ).val with hxdef
  have hxθ : (x : Circ) = θ := by rw [hxdef]; exact AddCircle.coe_equivIco
  have hper : periodize m θ = ∑' k : ℤ, m (x + (k : ℝ)) := by
    rw [← hxθ]
    exact Work.KMTContract.periodizeCoeEqTsum m x
  have hne : ∃ k : ℤ, m (x + (k : ℝ)) ≠ 0 := by
    by_contra hcon
    refine h ?_
    rw [hper]
    have h0 : (fun k : ℤ => m (x + (k : ℝ))) = fun _ => (0 : ℂ) := by
      funext k
      by_contra hk
      exact hcon ⟨k, hk⟩
    rw [h0, tsum_zero]
  obtain ⟨k, hk⟩ := hne
  refine ⟨x + (k : ℝ), hsupp _ hk, ?_⟩
  have hkc : (((k : ℝ)) : Circ) = 0 := by
    rw [AddCircle.coe_eq_zero_iff]
    exact ⟨k, by simp⟩
  rw [AddCircle.coe_add, hxθ, hkc, add_zero]

/-- A nonvanishing periodisation of a function supported in `[-δ,δ]` lies in the arc of radius
`δ` around `0`. -/
lemma fiberOpTex_periodize_ne_zero_mem_arcSet {m : ℝ → ℂ} {δ : ℝ}
    (hsupp : ∀ y : ℝ, m y ≠ 0 → |y| ≤ δ) {θ : Circ} (h : periodize m θ ≠ 0) :
    θ ∈ Work.BourgainPlan.IonescuWainger.arcSet 0 δ := by
  obtain ⟨θ₀, hle, heq⟩ := fiberOpTex_exists_coe_abs_le_of_periodize_ne_zero hsupp h
  exact ⟨θ₀, hle, by rw [zero_add]; exact heq.symm⟩

/-! ## The twisted Ionescu--Wainger symbol of the fibre -/

/-- **The Fourier coefficients of the twisted symbol** (integrable form).  For a finite set `A` of
circle frequencies, an integrable symbol `M` and integers `n₀, j`,

  `fourierCoeff (twistSymSet A M n₀) j = (∑_{α ∈ A} e(α (n₀ - j))) · fourierCoeff M j`. -/
lemma fiberOpTex_fourierCoeff_twistSymSet (A : Finset Circ) {M : Circ → ℂ}
    (hM : Integrable M circleMeasure) (n₀ j : ℤ) :
    fourierCoeff (twistSymSet A M n₀) j
      = (∑ α ∈ A, fourier (T := 1) (n₀ - j) α) * fourierCoeff M j := by
  have hterm : ∀ α ∈ A, Integrable
      (fun ξ : Circ => fourier (T := 1) n₀ α * M (ξ - α)) circleMeasure :=
    fun α _ => (hM.comp_sub_right α).const_mul _
  have hsym : twistSymSet A M n₀
      = ∑ α ∈ A, (fun ξ : Circ => fourier (T := 1) n₀ α * M (ξ - α)) := by
    funext ξ
    simp only [twistSymSet, Finset.sum_apply]
  rw [hsym]
  have h1 : fourierCoeff (∑ α ∈ A, (fun ξ : Circ => fourier (T := 1) n₀ α * M (ξ - α))) j
      = ∑ α ∈ A, fourierCoeff (fun ξ : Circ => fourier (T := 1) n₀ α * M (ξ - α)) j := by
    simpa only [Finset.sum_apply] using congrFun (fourierCoeff.sum A _ hterm) j
  rw [h1]
  have h2 : ∀ α ∈ A, fourierCoeff (fun ξ : Circ => fourier (T := 1) n₀ α * M (ξ - α)) j
      = fourier (T := 1) (n₀ - j) α * fourierCoeff M j := by
    intro α _
    rw [fourierCoeff.const_mul (fun ξ : Circ => M (ξ - α)) (fourier (T := 1) n₀ α) j,
      fourierCoeff_comp_sub M α j]
    rw [show n₀ - j = n₀ + -j by ring, fourier_add]
    ring
  rw [Finset.sum_congr rfl h2, Finset.sum_mul]

/-- The twisted symbol of an integrable symbol is integrable. -/
lemma fiberOpTex_integrable_twistSymSet (A : Finset Circ) {M : Circ → ℂ}
    (hM : Integrable M circleMeasure) (n₀ : ℤ) :
    Integrable (twistSymSet A M n₀) circleMeasure := by
  have hterm : ∀ α ∈ A, Integrable
      (fun ξ : Circ => fourier (T := 1) n₀ α * M (ξ - α)) circleMeasure :=
    fun α _ => (hM.comp_sub_right α).const_mul _
  have hsym : twistSymSet A M n₀
      = ∑ α ∈ A, (fun ξ : Circ => fourier (T := 1) n₀ α * M (ξ - α)) := by
    funext ξ
    simp only [twistSymSet, Finset.sum_apply]
  rw [hsym]
  exact integrable_finsetSum' A hterm

/-- If an integrable symbol has absolutely summable Fourier coefficients, so does its twisted
Ionescu--Wainger symbol (the loss is the cardinality of the frequency set). -/
lemma fiberOpTex_summable_norm_fourierCoeff_twistSymSet (A : Finset Circ) {M : Circ → ℂ}
    (hM : Integrable M circleMeasure) (hs : Summable (fun j : ℤ => ‖fourierCoeff M j‖))
    (n₀ : ℤ) : Summable (fun j : ℤ => ‖fourierCoeff (twistSymSet A M n₀) j‖) := by
  have hb : Summable (fun j : ℤ => ((A.card : ℕ) : ℝ) * ‖fourierCoeff M j‖) := hs.mul_left _
  refine Summable.of_nonneg_of_le (fun j => norm_nonneg _) (fun j => ?_) hb
  rw [fiberOpTex_fourierCoeff_twistSymSet A hM n₀ j, norm_mul]
  refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
  calc ‖∑ α ∈ A, fourier (T := 1) (n₀ - j) α‖
      ≤ ∑ α ∈ A, ‖fourier (T := 1) (n₀ - j) α‖ := norm_sum_le _ _
    _ = ∑ _α ∈ A, (1 : ℝ) :=
        Finset.sum_congr rfl (fun α _ => by rw [fourier_apply]; exact Circle.norm_coe _)
    _ = ((A.card : ℕ) : ℝ) := by simp

/-! ## The aliasing gate -/

/-- **The aliasing gate for the twisted symbol.**  If the frequency set `A` is `2ε`-separated
(equivalently the arcs of radius `2ε` around its points are disjoint), if `M` is `1` on the arc of
radius `ε` around `0` and vanishes off the arc of radius `2ε`, and if `P` vanishes off the arc of
radius `ε` around `0`, then

  `twistSymSet A M n₀ · iwSymbolSet A P = twistSymSet A P n₀`

pointwise on the circle: the plateau factor `M` disappears from the product. -/
lemma fiberOpTex_twistSymSet_mul_iwSymbolSet (A : Finset Circ) {M P : Circ → ℂ} {eps : ℝ} (heps : 0 < eps)
    (hsep : ∀ a ∈ A, ∀ b ∈ A, ∀ t : Circ,
      t ∈ Work.BourgainPlan.IonescuWainger.arcSet a (2 * eps) →
      t ∈ Work.BourgainPlan.IonescuWainger.arcSet b (2 * eps) → a = b)
    (hm1 : ∀ θ : Circ, θ ∈ Work.BourgainPlan.IonescuWainger.arcSet 0 eps →
      M θ = 1)
    (hms : ∀ θ : Circ, M θ ≠ 0 → θ ∈ Work.BourgainPlan.IonescuWainger.arcSet 0 (2 * eps))
    (hp : ∀ θ : Circ, P θ ≠ 0 → θ ∈ Work.BourgainPlan.IonescuWainger.arcSet 0 eps)
    (n₀ : ℤ) (ζ : Circ) :
    twistSymSet A M n₀ ζ * iwSymbolSet A P ζ = twistSymSet A P n₀ ζ := by
  have h := aliasingSymbolProduct A eps heps (fun a : Circ => fourier (T := 1) n₀ a) M P
    hsep hm1 hms hp ζ
  simpa only [twistSymSet, iwSymbolSet] using h

/-! ## The `ℓ¹`-decay of the coefficients of the §6 cut `m_* = η_{≤-2U}` -/

/-- The coefficients of `m_* = η_{≤-2u}` are `ℓ¹` (quadratic decay of the Fourier transform of a
`C²` compactly supported bump). -/
lemma fiberOpTex_summable_norm_cw_mStarF (u : ℕ) : Summable (fun j : ℤ => ‖cw (mStarF u) j‖) := by
  obtain ⟨C, _hCpos, hC⟩ := cw_etaCut_decay (-(2 * (u : ℤ)))
  refine Summable.of_nonneg_of_le (fun j => norm_nonneg _) (fun j => ?_)
    (summable_kmtKernWeight.mul_left C)
  rw [norm_kmtKernWeight, mul_one_div]
  simpa only [mStarF] using hC j

/-! ## The gate identity for the fibre -/

theorem fiberOpTex_eq_fiberOp_self_bdd (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (l U : ℕ) (hU : 1 ≤ U)
    (hna : Work.Analysis.IonescuWainger.NonAliasing (-(2 * (U : ℤ)))
      (Work.Analysis.IonescuWainger.iwArithFreqsNew ρ l))
    (φ : ℝ → ℂ) (hφ : MeasureTheory.Integrable φ)
    (hφsum : Summable (fun j : ℤ => ‖Work.KMTAreas.A7.cw φ j‖))
    (hφsupp : ∀ ξ : ℝ, φ ξ ≠ 0 → |ξ| ≤ (2 : ℝ) ^ (-(2 * (U : ℤ)) - 1))
    (f : ℤ → ℂ) (B : ℝ) (hB : ∀ x : ℤ, ‖f x‖ ≤ B) (n₀ : ℤ) :
    Work.KMTAreas.A7.fiberOp ρ l (Work.KMTAreas.A7.mStarF U) n₀ (Work.KMTAreas.A7.Tex ρ l φ f)
      = Work.KMTAreas.A7.fiberOp ρ l φ n₀ f := by
  -- the arithmetic frequency set and the two radii `2^{-2U-1} < 2^{-2U}`
  have heps : 0 < (2 : ℝ) ^ (-(2 * (U : ℤ)) - 1) := zpow_pos (by norm_num) _
  have h2eps : 2 * (2 : ℝ) ^ (-(2 * (U : ℤ)) - 1) = (2 : ℝ) ^ (-(2 * (U : ℤ))) :=
    fiberOpTex_two_mul_zpow_pred (-(2 * (U : ℤ)))
  -- integrability of the bump `m_* = η_{≤-2U}` and of the two periodisations
  have hmInt : Integrable (mStarF U) volume := by
    have h : Integrable (⇑(etaCutSchwartz (-(2 * (U : ℤ)))) : ℝ → ℂ) volume :=
      (etaCutSchwartz (-(2 * (U : ℤ)))).integrable
    rw [etaCutSchwartz_coe] at h
    simpa only [mStarF] using h
  have hMint : Integrable (periodize (mStarF U)) circleMeasure :=
    Work.KMTPlan.A6.IntegrablePeriodize hmInt
  have hPint : Integrable (periodize φ) circleMeasure := Work.KMTPlan.A6.IntegrablePeriodize hφ
  -- the plateau / support / separation hypotheses of the gate
  have hsep : ∀ a ∈ iwArithFreqsNew ρ l, ∀ b ∈ iwArithFreqsNew ρ l, ∀ t : Circ,
      t ∈ Work.BourgainPlan.IonescuWainger.arcSet a (2 * (2 : ℝ) ^ (-(2 * (U : ℤ)) - 1)) →
      t ∈ Work.BourgainPlan.IonescuWainger.arcSet b (2 * (2 : ℝ) ^ (-(2 * (U : ℤ)) - 1)) →
        a = b := by
    intro a ha b hb t ht1 ht2
    rw [h2eps] at ht1 ht2
    exact fiberOpTex_arcSet_sep_of_nonAliasing (k := -(2 * (U : ℤ))) hna a ha b hb t ht1 ht2
  have hm1 : ∀ θ : Circ,
      θ ∈ Work.BourgainPlan.IonescuWainger.arcSet 0 ((2 : ℝ) ^ (-(2 * (U : ℤ)) - 1)) →
      periodize (mStarF U) θ = 1 := (periodize_mStarF_one U hU).1
  have hms : ∀ θ : Circ, periodize (mStarF U) θ ≠ 0 →
      θ ∈ Work.BourgainPlan.IonescuWainger.arcSet 0 (2 * (2 : ℝ) ^ (-(2 * (U : ℤ)) - 1)) := by
    intro θ hθ
    rw [h2eps]
    exact fiberOpTex_periodize_ne_zero_mem_arcSet (m := mStarF U) (δ := (2 : ℝ) ^ (-(2 * (U : ℤ))))
      (fun y hy => by
        by_contra hlt
        exact hy ((mStarF_plateau U).2 y (le_of_lt (not_le.mp hlt)))) hθ
  have hp : ∀ θ : Circ, periodize φ θ ≠ 0 →
      θ ∈ Work.BourgainPlan.IonescuWainger.arcSet 0 ((2 : ℝ) ^ (-(2 * (U : ℤ)) - 1)) :=
    fun θ hθ => fiberOpTex_periodize_ne_zero_mem_arcSet (m := φ)
      (δ := (2 : ℝ) ^ (-(2 * (U : ℤ)) - 1)) hφsupp hθ
  have hgate : ∀ ζ : Circ, twistSymSet (iwArithFreqsNew ρ l) (periodize (mStarF U)) n₀ ζ
      * iwSymbolSet (iwArithFreqsNew ρ l) (periodize φ) ζ
      = twistSymSet (iwArithFreqsNew ρ l) (periodize φ) n₀ ζ :=
    fun ζ => fiberOpTex_twistSymSet_mul_iwSymbolSet (iwArithFreqsNew ρ l) heps hsep hm1 hms hp n₀ ζ
  -- integrability of the three symbols and of the product
  have hFint : Integrable (twistSymSet (iwArithFreqsNew ρ l) (periodize (mStarF U)) n₀)
      circleMeasure := fiberOpTex_integrable_twistSymSet _ hMint n₀
  have hGint : Integrable (iwSymbolSet (iwArithFreqsNew ρ l) (periodize φ)) circleMeasure :=
    integrable_iwSymbolSet _ hPint
  have hHint : Integrable (twistSymSet (iwArithFreqsNew ρ l) (periodize φ) n₀) circleMeasure :=
    fiberOpTex_integrable_twistSymSet _ hPint n₀
  have hFGint : Integrable (fun ζ : Circ =>
      twistSymSet (iwArithFreqsNew ρ l) (periodize (mStarF U)) n₀ ζ
        * iwSymbolSet (iwArithFreqsNew ρ l) (periodize φ) ζ) circleMeasure :=
    hHint.congr (Filter.Eventually.of_forall (fun ζ => (hgate ζ).symm))
  -- summability of the coefficient sequences
  have hMs : Summable (fun j : ℤ => ‖fourierCoeff (periodize (mStarF U)) j‖) := by
    refine (fiberOpTex_summable_norm_cw_mStarF U).congr (fun j => ?_)
    rw [fourierCoeff_periodize_eq_cw hmInt j]
  have hPs : Summable (fun j : ℤ => ‖fourierCoeff (periodize φ) j‖) := by
    refine hφsum.congr (fun j => ?_)
    rw [fourierCoeff_periodize_eq_cw hφ j]
  have hFs : Summable (fun j : ℤ => fourierCoeff
      (twistSymSet (iwArithFreqsNew ρ l) (periodize (mStarF U)) n₀) j) :=
    (fiberOpTex_summable_norm_fourierCoeff_twistSymSet (iwArithFreqsNew ρ l) hMint hMs n₀).of_norm
  have hGs : Summable (fun j : ℤ => fourierCoeff
      (iwSymbolSet (iwArithFreqsNew ρ l) (periodize φ)) j) :=
    (summable_norm_fourierCoeff_iwSymbolSet (iwArithFreqsNew ρ l) hPint hPs).of_norm
  -- the exact-height projection is the IW convolution with `periodize φ`
  have hTex : ∀ y : ℤ, Tex ρ l φ f y
      = ∑' k : ℤ, fourierCoeff (iwSymbolSet (iwArithFreqsNew ρ l) (periodize φ)) k
          * f (y - k) := by
    intro y
    have h1 : Tex ρ l φ f y = ∑' k : ℤ, Work.Analysis.IWMultiplier.iwKernel
        (iwSymbolSet (iwArithFreqsNew ρ l) (periodize φ)) k * f (y - k) := rfl
    rw [h1]
    exact tsum_congr (fun k => by rw [Work.Analysis.IWMultiplier.iwKernel])
  funext x
  rw [fiberOp_eq_kernel_conv, fiberOp_eq_kernel_conv]
  have step1 : (∑' j : ℤ, (∑ α ∈ iwArithFreqsNew ρ l, fourier (T := 1) (n₀ - j) α)
        * cw (mStarF U) j * Tex ρ l φ f (x - j))
      = ∑' j : ℤ, fourierCoeff (twistSymSet (iwArithFreqsNew ρ l) (periodize (mStarF U)) n₀) j
          * (∑' k : ℤ, fourierCoeff (iwSymbolSet (iwArithFreqsNew ρ l) (periodize φ)) k
              * f (x - j - k)) := by
    refine tsum_congr (fun j => ?_)
    rw [hTex (x - j), fiberOpTex_fourierCoeff_twistSymSet _ hMint n₀ j,
      fourierCoeff_periodize_eq_cw hmInt j]
  have step2 : (∑' j : ℤ,
        fourierCoeff (twistSymSet (iwArithFreqsNew ρ l) (periodize (mStarF U)) n₀) j
          * (∑' k : ℤ, fourierCoeff (iwSymbolSet (iwArithFreqsNew ρ l) (periodize φ)) k
              * f (x - j - k)))
      = ∑' i : ℤ, (∑' j : ℤ,
            fourierCoeff (twistSymSet (iwArithFreqsNew ρ l) (periodize (mStarF U)) n₀) j
              * fourierCoeff (iwSymbolSet (iwArithFreqsNew ρ l) (periodize φ)) (i - j))
          * f (x - i) :=
    tsum_conv_conv hFs.norm hGs.norm hB x
  have step3 : (∑' i : ℤ, (∑' j : ℤ,
          fourierCoeff (twistSymSet (iwArithFreqsNew ρ l) (periodize (mStarF U)) n₀) j
            * fourierCoeff (iwSymbolSet (iwArithFreqsNew ρ l) (periodize φ)) (i - j))
        * f (x - i))
      = ∑' i : ℤ, fourierCoeff (twistSymSet (iwArithFreqsNew ρ l) (periodize φ) n₀) i
          * f (x - i) := by
    refine tsum_congr (fun i => ?_)
    rw [← fourierCoeff_mul_l1 hFint hGint hFGint hFs hGs i,
      congrFun (fourierCoeff_congr_ae (Filter.Eventually.of_forall hgate)) i]
  have step4 : (∑' i : ℤ, fourierCoeff (twistSymSet (iwArithFreqsNew ρ l) (periodize φ) n₀) i
        * f (x - i))
      = ∑' j : ℤ, (∑ α ∈ iwArithFreqsNew ρ l, fourier (T := 1) (n₀ - j) α) * cw φ j
          * f (x - j) := by
    refine tsum_congr (fun i => ?_)
    rw [fiberOpTex_fourierCoeff_twistSymSet _ hPint n₀ i, fourierCoeff_periodize_eq_cw hφ i]
  exact step1.trans (step2.trans (step3.trans step4))

end

end Work.KMTAreas.A7
