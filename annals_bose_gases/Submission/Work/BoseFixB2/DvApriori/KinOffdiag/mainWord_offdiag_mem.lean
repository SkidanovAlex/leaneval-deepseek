import Mathlib.Tactic.Have
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.BoseFixB2.DvApriori.BandDefs
import Submission.Work.BoseFixB2.DvApriori.box_meanFree_mul_const_eq_zero
import Submission.Work.BoseFixB2.DvApriori.bsOneBody_polar
import Submission.Work.BoseFixB2.DvApriori.integrable_fsKinCoeff_polar
import Submission.Work.BoseFixB2.DvApriori.swap_p_abox_tBamp_pair
import Submission.Work.BoseFixB2.DvApriori.tBamp_pair_fixed_p_zero
import Submission.Work.BoseFixB2.Polar.polB_symm
import Submission.Work.BoseFixB2.Sector.aQ_sym_box
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseFixB2.DvApriori.KinOffdiag.mainWord_offdiag_mem`

The kinetic word `mainWord` (FS `eq:DefT`'s fourth term) is a *quadratic* form in the one-body
state, so the difference

`mainWord (fibre (E_SΨ + E_TΨ) x) − mainWord (fibre (E_SΨ − E_TΨ) x)`

is (four times) the polarisation of `mainWord` evaluated on the pair of *fibres*
`(fibre (E_SΨ) x, fibre (E_TΨ) x)`, where `E_S`, `E_T` are two joint sector projections
(`Work.BoseFixB2.jointProj`, FS §6 `lem:LocMatrices`).  Whenever `j ∈ S ∩ T` and `S ≠ T` the
box integral of that polarisation vanishes (the FS §6 "band" cancellation).  The statement is
`Work.BoseFixB2.DvApriori.mainWord_fibre_offdiag`.

## Why this module exists

This is a *re-homing* of `Work.BoseFixB2.DvApriori.mainWord_fibre_offdiag`, for two reasons:

* that module imports the **temporary** stub `...DvApriori._OffdiagStmts`, whose five
  conjuncts are stated with `sorry`; the five real modules
  (`box_meanFree_mul_const_eq_zero`, `bsOneBody_polar`, `integrable_fsKinCoeff_polar`,
  `swap_p_abox_tBamp_pair`, `tBamp_pair_fixed_p_zero`) are proved and are imported here
  directly, so this file carries no `sorry`;
* that module declares the helper `Work.BoseFixB2.DvApriori.Qfree_fibre_eq` (and
  `contDiff_fibre`), whose names collide with the declarations of the modules
  `...DvApriori.Qfree_fibre_eq` and `...DvApriori.momWord_fibre_offdiag`, so that two consumers
  of the FS §6 kinetic band lemmas cannot be imported into one environment.  Placing the copy in
  the `KinOffdiag` namespace removes the collision.

## The proof (unchanged)

Since `j ∈ S ∩ T` and `S ≠ T`, there is a *slot* `k < n`, `k ≠ j`, at which the two sectors
differ.  For that slot one of `(E_SΨ, E_TΨ)` is mean-free in the slot variable while the other
is independent of it, and the polarised fibre integrand is linear in each of the two fibres, so
the `x`-integral of the polarisation vanishes:

* the polarisation of `mainWord` is the explicit bilinear form
  `(2π)⁻³∫_p [‖p‖−c]₊²·Re(star(kinFT(χ₀Q₀f))·kinFT(χ₀Q₀g))` (`bsOneBody_polar`), which after the
  `tBamp`-dictionary `kinFT(χ₀Q₀(fibre_j Ψ x)) = tBamp χ₀ p (Q_jΨ) j x` becomes the pairing
  `tPair ℓ W V j p x = Re(star(tBamp χ₀ p W j x)·tBamp χ₀ p V j x)`;
* the momentum integral commutes with the configuration-box integral (`swap_p_abox_tBamp_pair`,
  a consequence of the uniform `(1+‖p‖)⁻³` decay of `tBamp` on the box);
* for each momentum `p` the box integral of the pairing vanishes because the `x_k`-mean of the
  mean-free factor is zero while the other factor is slot-`k`-independent
  (`box_meanFree_mul_const_eq_zero`, expanded through `tBamp` by `tBamp_pair_fixed_p_zero`).
-/

noncomputable section

namespace Work.BoseFixB2.DvApriori.KinOffdiag

open MeasureTheory

open Submission.BoseGases Work.BoseKinLoc

set_option maxHeartbeats 1000000

/-- **The polarised `tBamp` pairing.**  `tPair ℓ W V j p x = Re(star(tBamp χ₀ p W j x)·
tBamp χ₀ p V j x)` is the bilinear form in which the polarisation of the windowed spectral word
`mainWord` is written. -/
private def tPair {n : ℕ} (ℓ : ℝ) (W V : X n → ℝ) (j : Fin n) (p : ℝ³) (x : X n) : ℝ :=
  (star (Work.SmallBoxTBWord.tBamp (Work.BSKinetic.bsWin ℓ 0) p W j x) *
    Work.SmallBoxTBWord.tBamp (Work.BSKinetic.bsWin ℓ 0) p V j x).re

/-- **The kinetic symbol of the `mainWord` polarisation**:
`4(1−ε_T)[r−c₁]₊² + 4ε_T[r−c₂]₊²` with `c₁ = (2sℓ)⁻¹`, `c₂ = (2dsℓ)⁻¹`. -/
private def mwSym (ℓ d s εT : ℝ) (r : ℝ) : ℝ :=
  4 * (1 - εT) * Submission.BoseGases.fsKinCoeff ((2 * (s * ℓ))⁻¹) r
    + 4 * εT * Submission.BoseGases.fsKinCoeff ((2 * (d * s * ℓ))⁻¹) r

/-! ## 1. Elementary slot algebra -/

/-- The pointwise form of `aP ℓ k W = 0`: the box mean of `W` in the slot `k` vanishes. -/
private lemma aP_eq_zero_imp_mean_eq_zero {ℓ : ℝ} {n : ℕ} (k : Fin n) {W : X n → ℝ}
    (h : aP ℓ k W = 0) :
    ∀ y : X n, (1 / ℓ ^ 3) * ∫ w in acube ℓ, W (Function.update y k w) = 0 := by
  intro y
  have h' := congrFun h y
  simpa only [aP, Pi.zero_apply] using h'

/-- **`Q_j` fixes the sector `E_S Ψ` when the slot `j` belongs to `S`.**

In the recursion `jointProj = blockOp` the slot-`j` operator is `Q_j`, and the later slot
operators commute with `P_j`; hence `P_j (E_S Ψ) = 0` (`Sector.aP_blockOp_eq_zero`) and
`Q_j (E_S Ψ) = (1 − P_j) (E_S Ψ) = E_S Ψ`. -/
private lemma aQ_jointProj_eq_self_of_mem {ℓ : ℝ} (hℓ : 0 < ℓ) {n : ℕ} {S : Finset ℕ} {j : ℕ}
    (hjS : j ∈ S) (hjn : j < n) {Ψ : X n → ℝ} (hΨ : ContDiff ℝ (⊤ : ℕ∞) Ψ) :
    aQ ℓ ⟨j, hjn⟩ (jointProj ℓ S Ψ) = jointProj ℓ S Ψ := by
  have h := Sector.aP_blockOp_eq_zero hℓ hjn hjS hΨ.continuous
  funext x
  simp only [aQ]
  rw [congrFun h x, Pi.zero_apply, sub_zero]

/-- **The mean-free part of a slot-`j` fibre is the fibre of `Q_j`:**

`Q_{Λ}(fibre_j Ψ x) = fibre_j (Q_j Ψ) x`, i.e. `Qfree ℓ 0 (fibre n j Ψ x) = fibre n j (aQ ℓ j Ψ) x`.

Both sides are `Ψ(x_j ← z) − |Λ|⁻¹∫_{Λ}Ψ(x_j ← z') dz'`. -/
private lemma Qfree_fibre_eq {ℓ : ℝ} {n : ℕ} (j : Fin n) {Ψ : X n → ℝ} (x : X n) :
    Qfree ℓ 0 (fibre n j Ψ x) = fibre n j (aQ ℓ j Ψ) x := by
  funext z
  simp only [Qfree, Work.BSKinetic.bsQ, Work.BSKinetic.bsMean, fibre, aQ, aP,
    smul_zero, zero_add, one_div]
  have hme : (∫ y in acube ℓ, Ψ (Function.update (Function.update x j z) j y))
      = ∫ y in acube ℓ, Ψ (Function.update x j y) := by
    congr 1
    ext y
    rw [Function.update_idem]
  rw [hme]

/-- **The windowed fibre dictionary.**  The windowed mean-free fibre of a slot state is the
`tBamp` amplitude of the mean-free state:

`kinFT (χ · Q_{Λ}(fibre_j Ψ x)) p = tBamp χ p (Q_j Ψ) j x`. -/
private lemma kinFT_win_Qfree_fibre {ℓ : ℝ} {n : ℕ} (j : Fin n) (χ : ℝ³ → ℝ) (p : ℝ³)
    {Ψ : X n → ℝ} (x : X n) :
    kinFT (fun z : ℝ³ => (χ z : ℂ) * (Qfree ℓ 0 (fibre n j Ψ x) z : ℂ)) p
      = Work.SmallBoxTBWord.tBamp χ p (aQ ℓ j Ψ) j x := by
  rw [Qfree_fibre_eq j x, Work.SmallBoxTBWord.tBamp]
  apply MeasureTheory.integral_congr_ae
  filter_upwards with z
  have h : fibre n j (aQ ℓ j Ψ) x z = aQ ℓ j Ψ (Function.update x j z) := rfl
  rw [h]
  ring

/-- Linearity of the fibre in the state (pointwise sum). -/
private lemma fibre_add' {n : ℕ} (j : Fin n) (W V : X n → ℝ) (x : X n) :
    fibre n j (W + V) x = fun z => fibre n j W x z + fibre n j V x z := rfl

/-- Linearity of the fibre in the state (pointwise difference). -/
private lemma fibre_sub' {n : ℕ} (j : Fin n) (W V : X n → ℝ) (x : X n) :
    fibre n j (W - V) x = fun z => fibre n j W x z - fibre n j V x z := rfl

/-- The slot-`j` fibre of a smooth state is smooth. -/
private lemma contDiff_fibre {n : ℕ} {W : X n → ℝ} (hW : ContDiff ℝ (⊤ : ℕ∞) W) (j : Fin n)
    (x : X n) : ContDiff ℝ (⊤ : ℕ∞) (fibre n j W x) :=
  hW.comp (contDiff_update (𝕜 := ℝ) (⊤ : ℕ∞) x j)

/-- The box indicator `indU ℓ 0 = 1_{acube ℓ}` is `1` on the configuration box. -/
private lemma indU_zero_eq_one_of_mem {n : ℕ} {ℓ : ℝ} {x : X n} (j : Fin n) (hx : x ∈ abox n ℓ) :
    indU ℓ 0 (x j) = 1 := by
  have hmem : x j ∈ lamBox ℓ 0 := by
    show x j - ℓ • (0 : ℝ³) ∈ acube ℓ
    simpa using hx j
  simp only [indU, Set.indicator_of_mem hmem]

/-- Swapping the two slot states: the polarised combination is symmetric under `W ↔ V`
(`mainWord` is even, `fibre_j (−ψ) = −fibre_j ψ`). -/
private lemma mainWord_fibre_swap {ℓ d s εT : ℝ} {n : ℕ} (j : Fin n) (W V : X n → ℝ)
    (x : X n) :
    mainWord ℓ d s εT 0 (fibre n j (W + V) x) - mainWord ℓ d s εT 0 (fibre n j (W - V) x)
      = mainWord ℓ d s εT 0 (fibre n j (V + W) x)
        - mainWord ℓ d s εT 0 (fibre n j (V - W) x) := by
  have h : fibre n j (V - W) x = fun z => -(fibre n j (W - V) x z) := by
    funext z
    simp only [fibre, Pi.sub_apply]
    ring
  rw [add_comm W V, h, Work.BoseFixB2.Polar.PolB.mainWord_neg]

/-! ## 2. The pointwise polarisation identity -/

/-- **The polarisation identity for `mainWord` at a single configuration.**  For smooth slot
states `W`, `V`,

`mainWord (fibre (W+V) x) − mainWord (fibre (W−V) x) = (2π)⁻³∫_p mwSym ‖p‖ · tPair ℓ (Q_jW) (Q_jV) j p x`.

This is the two `bsOneBody` polarisation identities (`bsOneBody_polar`), the `tBamp`
dictionary, and the linearity of the `p`-integral in the symbol. -/
private lemma mainWord_fibre_polar_at {ℓ d s εT : ℝ} (hℓ : 0 < ℓ) {n : ℕ} (j : Fin n) (x : X n)
    {W V : X n → ℝ} (hW : ContDiff ℝ (⊤ : ℕ∞) W) (hV : ContDiff ℝ (⊤ : ℕ∞) V) :
    mainWord ℓ d s εT 0 (fibre n j (W + V) x) - mainWord ℓ d s εT 0 (fibre n j (W - V) x)
      = ((2 * Real.pi) ^ 3)⁻¹ *
          ∫ p : ℝ³, mwSym ℓ d s εT ‖p‖ * tPair ℓ (aQ ℓ j W) (aQ ℓ j V) j p x := by
  have hf : ContDiff ℝ (⊤ : ℕ∞) (fibre n j W x) := contDiff_fibre hW j x
  have hg : ContDiff ℝ (⊤ : ℕ∞) (fibre n j V x) := contDiff_fibre hV j x
  -- integrability of the polarised `p`-integrand, in the `tBamp` form
  have hInt : ∀ c : ℝ, MeasureTheory.Integrable (fun p : ℝ³ => fsKinCoeff c ‖p‖ *
      tPair ℓ (aQ ℓ j W) (aQ ℓ j V) j p x) := by
    intro c
    refine (integrable_fsKinCoeff_polar (ℓ := ℓ) (c := c) hℓ hf hg).congr ?_
    filter_upwards with p
    rw [kinFT_win_Qfree_fibre, kinFT_win_Qfree_fibre]
    rfl
  -- the polarisation of each `bsOneBody`, with the `(2π)⁻³` constant inside the integral
  have hpol : ∀ c : ℝ, Work.BSKinetic.bsOneBody ℓ (fsKinCoeff c) 0 (fibre n j (W + V) x)
        - Work.BSKinetic.bsOneBody ℓ (fsKinCoeff c) 0 (fibre n j (W - V) x)
      = ∫ p : ℝ³, (4 * ((2 * Real.pi) ^ 3)⁻¹) *
          (fsKinCoeff c ‖p‖ * tPair ℓ (aQ ℓ j W) (aQ ℓ j V) j p x) := by
    intro c
    rw [fibre_add' (j := j) W V x, fibre_sub' (j := j) W V x]
    rw [bsOneBody_polar (ℓ := ℓ) (c := c) hℓ hf hg]
    simp only [kinFT_win_Qfree_fibre]
    rw [← MeasureTheory.integral_const_mul (4 * ((2 * Real.pi) ^ 3)⁻¹)
      (fun p : ℝ³ => fsKinCoeff c ‖p‖ *
        (star (Work.SmallBoxTBWord.tBamp (Work.BSKinetic.bsWin ℓ 0) p (aQ ℓ j W) j x) *
          Work.SmallBoxTBWord.tBamp (Work.BSKinetic.bsWin ℓ 0) p (aQ ℓ j V) j x).re)]
    apply MeasureTheory.integral_congr_ae
    filter_upwards with p
    simp only [tPair]
  -- group the difference of the two `bsOneBody` differences
  have hgroup : mainWord ℓ d s εT 0 (fibre n j (W + V) x)
        - mainWord ℓ d s εT 0 (fibre n j (W - V) x)
      = (1 - εT) * (Work.BSKinetic.bsOneBody ℓ (fsKinCoeff ((2 * (s * ℓ))⁻¹)) 0
              (fibre n j (W + V) x)
            - Work.BSKinetic.bsOneBody ℓ (fsKinCoeff ((2 * (s * ℓ))⁻¹)) 0
              (fibre n j (W - V) x))
        + εT * (Work.BSKinetic.bsOneBody ℓ (fsKinCoeff ((2 * (d * s * ℓ))⁻¹)) 0
              (fibre n j (W + V) x)
            - Work.BSKinetic.bsOneBody ℓ (fsKinCoeff ((2 * (d * s * ℓ))⁻¹)) 0
              (fibre n j (W - V) x)) := by
    simp only [mainWord]
    ring
  rw [hgroup, hpol ((2 * (s * ℓ))⁻¹), hpol ((2 * (d * s * ℓ))⁻¹)]
  -- move the coefficients `(1−ε_T)`, `ε_T` inside their integrals
  rw [← MeasureTheory.integral_const_mul (1 - εT)
        (fun p : ℝ³ => (4 * ((2 * Real.pi) ^ 3)⁻¹) *
          (fsKinCoeff ((2 * (s * ℓ))⁻¹) ‖p‖ * tPair ℓ (aQ ℓ j W) (aQ ℓ j V) j p x)),
      ← MeasureTheory.integral_const_mul εT
        (fun p : ℝ³ => (4 * ((2 * Real.pi) ^ 3)⁻¹) *
          (fsKinCoeff ((2 * (d * s * ℓ))⁻¹) ‖p‖ * tPair ℓ (aQ ℓ j W) (aQ ℓ j V) j p x))]
  -- combine the two integrals
  rw [← MeasureTheory.integral_add
        (((hInt ((2 * (s * ℓ))⁻¹)).const_mul (4 * ((2 * Real.pi) ^ 3)⁻¹)).const_mul (1 - εT))
        (((hInt ((2 * (d * s * ℓ))⁻¹)).const_mul (4 * ((2 * Real.pi) ^ 3)⁻¹)).const_mul εT)]
  -- move `(2π)⁻³` of the right-hand side inside its integral
  rw [← MeasureTheory.integral_const_mul (((2 * Real.pi) ^ 3)⁻¹)
        (fun p : ℝ³ => mwSym ℓ d s εT ‖p‖ * tPair ℓ (aQ ℓ j W) (aQ ℓ j V) j p x)]
  apply MeasureTheory.integral_congr_ae
  filter_upwards with p
  simp only [mwSym]
  ring

/-! ## 3. The vanishing for a single slot -/

/-- **The off-diagonal vanishing at a fixed slot.**  Let `W` be mean-free in the slot `k` and
`V` independent of the slot-`k` variable, and let both be fixed by the slot-`j` mean-free
projection (`k ≠ j`).  Then the polarised fibre integral of `mainWord` over the box vanishes. -/
private lemma mainWord_fibre_offdiag_of_slot {ℓ d s εT : ℝ} (hℓ : 0 < ℓ) {n : ℕ} {j k : Fin n}
    (hjk : j ≠ k) {W V : X n → ℝ} (hW : ContDiff ℝ (⊤ : ℕ∞) W)
    (hV : ContDiff ℝ (⊤ : ℕ∞) V) (hWj : aQ ℓ j W = W) (hVj : aQ ℓ j V = V)
    (hfree : ∀ y : X n, (1 / ℓ ^ 3) * ∫ w in acube ℓ, W (Function.update y k w) = 0)
    (hconst : ∀ (y : X n) (w : ℝ³), V (Function.update y k w) = V y) :
    (∫ x in abox n ℓ, indU ℓ 0 (x j) *
      (mainWord ℓ d s εT 0 (fibre n j (W + V) x)
        - mainWord ℓ d s εT 0 (fibre n j (W - V) x))) = 0 := by
  have hWc : Continuous W := hW.continuous
  have hVc : Continuous V := hV.continuous
  -- the slot-`k` peel
  have hpeel : ∀ z z' : ℝ³, (∫ x in abox n ℓ, indU ℓ 0 (x j) *
      (W (Function.update x j z) * V (Function.update x j z'))) = 0 :=
    box_meanFree_mul_const_eq_zero (ℓ := ℓ) (j := j) (k := k) hℓ hjk hWc hVc hfree hconst
  -- the fixed-momentum vanishing
  have hkill : ∀ p : ℝ³, (∫ x in abox n ℓ, indU ℓ 0 (x j) *
      (star (Work.SmallBoxTBWord.tBamp (Work.BSKinetic.bsWin ℓ 0) p W j x) *
        Work.SmallBoxTBWord.tBamp (Work.BSKinetic.bsWin ℓ 0) p V j x).re) = 0 :=
    fun p => tBamp_pair_fixed_p_zero (ℓ := ℓ) (j := j) (k := k) hℓ hjk hWc hVc hpeel p
  -- the symbol: measurability and polynomial growth
  have hc₁m : Measurable (fun r : ℝ => Submission.BoseGases.fsKinCoeff ((2 * (s * ℓ))⁻¹) r) :=
    Work.BoseKinLoc.Kinetic.measurable_fsKinCoeff _
  have hc₂m : Measurable (fun r : ℝ => Submission.BoseGases.fsKinCoeff ((2 * (d * s * ℓ))⁻¹) r) :=
    Work.BoseKinLoc.Kinetic.measurable_fsKinCoeff _
  have hFm : Measurable (mwSym ℓ d s εT) :=
    (measurable_const.mul hc₁m).add (measurable_const.mul hc₂m)
  have hK : 0 ≤ |4 * (1 - εT)| * (1 + |(2 * (s * ℓ))⁻¹|) ^ 2
      + |4 * εT| * (1 + |(2 * (d * s * ℓ))⁻¹|) ^ 2 := by positivity
  have hFbd : ∀ r : ℝ, 0 ≤ r → |mwSym ℓ d s εT r| ≤
      (|4 * (1 - εT)| * (1 + |(2 * (s * ℓ))⁻¹|) ^ 2
        + |4 * εT| * (1 + |(2 * (d * s * ℓ))⁻¹|) ^ 2) * (1 + r) ^ 2 := by
    intro r hr
    have h1 : 0 ≤ Submission.BoseGases.fsKinCoeff ((2 * (s * ℓ))⁻¹) r :=
      Submission.BoseGases.fsKinCoeff_nonneg _ _
    have h2 : 0 ≤ Submission.BoseGases.fsKinCoeff ((2 * (d * s * ℓ))⁻¹) r :=
      Submission.BoseGases.fsKinCoeff_nonneg _ _
    have b1 : Submission.BoseGases.fsKinCoeff ((2 * (s * ℓ))⁻¹) r
        ≤ (1 + |(2 * (s * ℓ))⁻¹|) ^ 2 * (1 + r) ^ 2 :=
      Work.BSKinetic.SwapTBAmp.fsKinCoeff_le hr
    have b2 : Submission.BoseGases.fsKinCoeff ((2 * (d * s * ℓ))⁻¹) r
        ≤ (1 + |(2 * (d * s * ℓ))⁻¹|) ^ 2 * (1 + r) ^ 2 :=
      Work.BSKinetic.SwapTBAmp.fsKinCoeff_le hr
    simp only [mwSym]
    calc |4 * (1 - εT) * Submission.BoseGases.fsKinCoeff ((2 * (s * ℓ))⁻¹) r
          + 4 * εT * Submission.BoseGases.fsKinCoeff ((2 * (d * s * ℓ))⁻¹) r|
        ≤ |4 * (1 - εT) * Submission.BoseGases.fsKinCoeff ((2 * (s * ℓ))⁻¹) r|
          + |4 * εT * Submission.BoseGases.fsKinCoeff ((2 * (d * s * ℓ))⁻¹) r| := by
            rw [abs_le]
            constructor
            · linarith [neg_abs_le (4 * (1 - εT) * Submission.BoseGases.fsKinCoeff ((2 * (s * ℓ))⁻¹) r),
                neg_abs_le (4 * εT * Submission.BoseGases.fsKinCoeff ((2 * (d * s * ℓ))⁻¹) r)]
            · linarith [le_abs_self (4 * (1 - εT) * Submission.BoseGases.fsKinCoeff ((2 * (s * ℓ))⁻¹) r),
                le_abs_self (4 * εT * Submission.BoseGases.fsKinCoeff ((2 * (d * s * ℓ))⁻¹) r)]
      _ = |4 * (1 - εT)| * Submission.BoseGases.fsKinCoeff ((2 * (s * ℓ))⁻¹) r
          + |4 * εT| * Submission.BoseGases.fsKinCoeff ((2 * (d * s * ℓ))⁻¹) r := by
            simp only [abs_mul, abs_of_nonneg h1, abs_of_nonneg h2]
      _ ≤ |4 * (1 - εT)| * ((1 + |(2 * (s * ℓ))⁻¹|) ^ 2 * (1 + r) ^ 2)
          + |4 * εT| * ((1 + |(2 * (d * s * ℓ))⁻¹|) ^ 2 * (1 + r) ^ 2) := by
            gcongr
      _ = (|4 * (1 - εT)| * (1 + |(2 * (s * ℓ))⁻¹|) ^ 2
          + |4 * εT| * (1 + |(2 * (d * s * ℓ))⁻¹|) ^ 2) * (1 + r) ^ 2 := by ring
  -- the pointwise polarisation identity, converted to `W`, `V`
  have hpt : ∀ x : X n, mainWord ℓ d s εT 0 (fibre n j (W + V) x)
        - mainWord ℓ d s εT 0 (fibre n j (W - V) x)
      = ((2 * Real.pi) ^ 3)⁻¹ * ∫ p : ℝ³, mwSym ℓ d s εT ‖p‖ *
          (star (Work.SmallBoxTBWord.tBamp (Work.BSKinetic.bsWin ℓ 0) p W j x) *
            Work.SmallBoxTBWord.tBamp (Work.BSKinetic.bsWin ℓ 0) p V j x).re := by
    intro x
    rw [mainWord_fibre_polar_at (ℓ := ℓ) (d := d) (s := s) (εT := εT) hℓ j x hW hV]
    rw [hWj, hVj]
    simp only [tPair]
  -- the configuration integral of the polarisation
  rw [show (∫ x in abox n ℓ, indU ℓ 0 (x j) *
        (mainWord ℓ d s εT 0 (fibre n j (W + V) x)
          - mainWord ℓ d s εT 0 (fibre n j (W - V) x)))
      = ∫ x in abox n ℓ, indU ℓ 0 (x j) * (((2 * Real.pi) ^ 3)⁻¹ *
          ∫ p : ℝ³, mwSym ℓ d s εT ‖p‖ *
            (star (Work.SmallBoxTBWord.tBamp (Work.BSKinetic.bsWin ℓ 0) p W j x) *
              Work.SmallBoxTBWord.tBamp (Work.BSKinetic.bsWin ℓ 0) p V j x).re)
      from by
        apply MeasureTheory.integral_congr_ae
        filter_upwards with x
        rw [hpt x]]
  -- exchange the momentum integral with the box integral
  rw [swap_p_abox_tBamp_pair (ℓ := ℓ) (j := j) hℓ hK hFm hFbd hW hV]
  -- for each momentum the inner box integral vanishes
  rw [show (∫ p : ℝ³, mwSym ℓ d s εT ‖p‖ *
          (∫ x in abox n ℓ, indU ℓ 0 (x j) *
            (star (Work.SmallBoxTBWord.tBamp (Work.BSKinetic.bsWin ℓ 0) p W j x) *
              Work.SmallBoxTBWord.tBamp (Work.BSKinetic.bsWin ℓ 0) p V j x).re))
      = ∫ p : ℝ³, mwSym ℓ d s εT ‖p‖ * 0
      from by
        apply MeasureTheory.integral_congr_ae
        filter_upwards with p
        rw [hkill p]]
  simp

/-! ## 4. The target -/

/-- **The `mainWord` off-diagonal fibre bracket vanishes** for `j ∈ S ∩ T`, `S ≠ T`. -/
theorem mainWord_offdiag_mem {ℓ d s εT : ℝ} (hℓ : 0 < ℓ) {n : ℕ} (j : Fin n)
    {Φ : Submission.BoseGases.X n → ℝ} (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ)
    {S T : Finset ℕ} (hS : S ⊆ Finset.range n) (hT : T ⊆ Finset.range n)
    (hjS : (j : ℕ) ∈ S) (hjT : (j : ℕ) ∈ T) (hST : S ≠ T) :
    (∫ x in Submission.BoseGases.abox n ℓ, Work.BoseKinLoc.indU ℓ 0 (x j) *
      (Work.BoseKinLoc.mainWord ℓ d s εT 0
          (Work.BoseKinLoc.fibre n j (Work.BoseFixB2.jointProj ℓ S Φ + Work.BoseFixB2.jointProj ℓ T Φ) x)
       - Work.BoseKinLoc.mainWord ℓ d s εT 0
          (Work.BoseKinLoc.fibre n j (Work.BoseFixB2.jointProj ℓ S Φ - Work.BoseFixB2.jointProj ℓ T Φ) x))) = 0 := by
  cases n with
  | zero => exact Fin.elim0 j
  | succ m =>
    -- a slot in which the two sectors differ
    obtain ⟨k, hkST⟩ : ∃ k, (k ∈ S ∧ k ∉ T) ∨ (k ∈ T ∧ k ∉ S) := by
      by_contra h
      push Not at h
      exact hST (Finset.ext fun k => ⟨fun hk => (h k).1 hk, fun hk => (h k).2 hk⟩)
    have hkn : k < m + 1 := by
      rcases hkST with ⟨h1, -⟩ | ⟨h1, -⟩
      · exact Finset.mem_range.mp (hS h1)
      · exact Finset.mem_range.mp (hT h1)
    have hkj : k ≠ (j : ℕ) := by
      rcases hkST with ⟨-, h2⟩ | ⟨-, h2⟩
      · intro hc; exact h2 (by rw [hc]; exact hjT)
      · intro hc; exact h2 (by rw [hc]; exact hjS)
    have hjk : j ≠ (⟨k, hkn⟩ : Fin (m + 1)) := fun hc => hkj (congrArg Fin.val hc).symm
    -- smoothness and the slot-`j` mean-free invariance of the two sectors
    have hWcd : ContDiff ℝ (⊤ : ℕ∞) (jointProj ℓ S Φ) := Sector.jointProj_contDiff hℓ S hΦ
    have hVcd : ContDiff ℝ (⊤ : ℕ∞) (jointProj ℓ T Φ) := Sector.jointProj_contDiff hℓ T hΦ
    have hWj : aQ ℓ j (jointProj ℓ S Φ) = jointProj ℓ S Φ :=
      aQ_jointProj_eq_self_of_mem hℓ hjS j.isLt hΦ
    have hVj : aQ ℓ j (jointProj ℓ T Φ) = jointProj ℓ T Φ :=
      aQ_jointProj_eq_self_of_mem hℓ hjT j.isLt hΦ
    rcases hkST with ⟨hkS, hkT⟩ | ⟨hkT, hkS⟩
    · -- `k ∈ S \ T`: `E_SΦ` is mean-free in the slot `k`, `E_TΦ` is independent of it
      have hfree : ∀ y : X (m + 1), (1 / ℓ ^ 3) * ∫ w in acube ℓ,
          (jointProj ℓ S Φ) (Function.update y ⟨k, hkn⟩ w) = 0 :=
        aP_eq_zero_imp_mean_eq_zero ⟨k, hkn⟩
          (Sector.aP_blockOp_eq_zero hℓ hkn hkS hΦ.continuous)
      have hconst : ∀ (y : X (m + 1)) (w : ℝ³),
          (jointProj ℓ T Φ) (Function.update y ⟨k, hkn⟩ w) = (jointProj ℓ T Φ) y :=
        fun y w => Sector.constIn_jointProj hℓ hkn hkT hΦ.continuous y w
      exact mainWord_fibre_offdiag_of_slot (ℓ := ℓ) (d := d) (s := s) (εT := εT)
        (j := j) (k := ⟨k, hkn⟩) hℓ hjk hWcd hVcd hWj hVj hfree hconst
    · -- `k ∈ T \ S`: apply the slot lemma to the swapped pair and use the symmetry
      have hfree : ∀ y : X (m + 1), (1 / ℓ ^ 3) * ∫ w in acube ℓ,
          (jointProj ℓ T Φ) (Function.update y ⟨k, hkn⟩ w) = 0 :=
        aP_eq_zero_imp_mean_eq_zero ⟨k, hkn⟩
          (Sector.aP_blockOp_eq_zero hℓ hkn hkT hΦ.continuous)
      have hconst : ∀ (y : X (m + 1)) (w : ℝ³),
          (jointProj ℓ S Φ) (Function.update y ⟨k, hkn⟩ w) = (jointProj ℓ S Φ) y :=
        fun y w => Sector.constIn_jointProj hℓ hkn hkS hΦ.continuous y w
      have hswap := mainWord_fibre_offdiag_of_slot (ℓ := ℓ) (d := d) (s := s) (εT := εT)
        (j := j) (k := ⟨k, hkn⟩) (W := jointProj ℓ T Φ) (V := jointProj ℓ S Φ)
        hℓ hjk hVcd hWcd hVj hWj hfree hconst
      rw [← hswap]
      apply MeasureTheory.integral_congr_ae
      filter_upwards with x
      exact congrArg (fun t : ℝ => indU ℓ 0 (x j) * t)
        (mainWord_fibre_swap j (jointProj ℓ S Φ) (jointProj ℓ T Φ) x)

end Work.BoseFixB2.DvApriori.KinOffdiag
