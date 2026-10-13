/-
# `Transfer/E2_norm` — the `ℋⁿ`-norm estimate for the `D_z`-defect of the transfer

For `0 < α ≤ 1` and `f ∈ CoerAdm α` the `D_z`-defect of the transfer identity
`D_z(𝓛_Γ^T f) = 𝓛̂(D_z f) + E2 α f` is

  `E2 α f = Ê₂ f + Γ(θ)·radS α f z`   (`Transfer/Profiles.lean`),

and this file proves the **`α`-uniform `ℋⁿ`-norm bound**

  `|E2 α f|_{ℋⁿ} ≤ κ·(|f|_{ℋⁿ} + |D_θ f|_{ℋⁿ})`,  `n ≤ 3`,

with a single constant `κ` for all `α ∈ (0,1]`, all `n ≤ 3` and all `f ∈ CoerAdm α`.
This is the "norm half" of the (refuted-in-its-`RegQ`-part) obligation
`Transfer/E2_regQ_norm`; it is the hypothesis `hE2` of `Transfer/main.headline_of_errors`.

## The route

* **The split.**  `E2 α f = Ê₂ f + (Γ·radS)` and the two summands are `Cⁿ` on the open
  quadrant, so `HkSq` is subadditive (`E2norm.Pieces.HkSq_add_le`, fed by
  `E2pkg.hkIntegrand_add_le_of_contDiffOn`).
* **The `Ê₂` part.**  `Assembly.E2hat_HkSq_le_uniform n` gives
  `HkSq α n (Ê₂ f) ≤ Cₙ·(HkSq α n f + HkSq α n (D_θ f))` for `RegQ α (n+1) f`; the four
  constants `C₀,…,C₃` are merged into one number `Cmax`.
* **The separated part.**  `Γ(θ)·radS(z)` is smooth in `θ` and radial in `z`; hence
  * `E2norm.gam_rad_integral_le` (a purely angular statement, uniform in `α`) bounds the
    `θ`-integral of the `ℋⁿ`-integrand by a uniform constant `KA` times the *radial*
    majorant `∑_{j≤n}(D_z^j radS)²w²`;
  * `E2norm.radS_DzdIter_le` bounds each radial integral by `CE·(KB+1)(KC+1)` times
    `(|f|²_{ℋⁿ} + |D_θf|²_{ℋⁿ})`, using the multiplier bound
    `E2norm.ampB_DzdIter_sq_w_sq_le` (`KB`), the zero-mode bound
    `E2norm.L12f_Transport_zero_sq_le` (`KC`) and the two level-`n` bounds
    `E2norm.Pieces.qang_sq_w_sq_le`, `E2norm.Pieces.L12f_DzdIter_sq_w_sq_le`.
* **The square root.**  `HkNorm = √HkSq`, `√(a+b) ≤ √a + √b`.

All constants are `α`-, `f`- and `n`-uniform (the `n`-dependence is absorbed by
`(n+1) ≤ 4` and by `Cmax`).
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.CoercivityFix.Transfer.Profiles
import Submission.Work.FTS.Vocab
import Submission.Work.FTS.CoercivityFix.Transfer.E1Parts.RadL12
import Submission.Work.FTS.CoercivityFix.Transfer.E1Parts.HardyOne
import Submission.Work.FTS.CoercivityFix.Transfer.E2norm.Pieces
import Submission.Work.FTS.CoercivityFix.Transfer.E2norm.ampB_DzdIter_sq_w_sq_le
import Submission.Work.FTS.CoercivityFix.Transfer.E2norm.L12f_Transport_zero_sq_le
import Submission.Work.FTS.CoercivityFix.Transfer.E2norm.radS_DzdIter_le
import Submission.Work.FTS.CoercivityFix.Transfer.E2norm.gam_rad_integral_le
import Submission.Work.FTS.CoercivityFix.Transfer.E2pkg.RadS
import Submission.Work.FTS.CoercivityFix.Transfer.E2pkg.FinCalc
import Submission.Work.FTS.CoercivityFix.Transfer.E2pkg.HkMemGam
import Submission.Work.FTS.CoercivityFix.Transfer.E2_pkg
import Submission.Work.FTS.CoercivityFix.Transfer.AuxE2.E2hat_contDiffOn_three
import Submission.Work.FTS.CoercivityFix.Assembly.E2hat_HkSq_le_uniform
import Submission.Work.FTS.CoercivityFix.Assembly.E2hat_RegQ
import Submission.Work.FTS.CoercivityStep.Norm.HkSq_mono_le
import Submission.Work.FTS.H2.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.CoercivityFix.Transfer

set_option autoImplicit false

/-- `√(X+Y) ≤ √X + √Y` for nonnegative `X`, `Y`. -/
private theorem sqrt_add_le_sqrt_add_sqrt {X Y : ℝ} (hX : 0 ≤ X) (hY : 0 ≤ Y) :
    Real.sqrt (X + Y) ≤ Real.sqrt X + Real.sqrt Y := by
  rw [Real.sqrt_le_iff]
  refine ⟨by positivity, ?_⟩
  have h1 : Real.sqrt X ^ 2 = X := Real.sq_sqrt hX
  have h2 : Real.sqrt Y ^ 2 = Y := Real.sq_sqrt hY
  have hexp : (Real.sqrt X + Real.sqrt Y) ^ 2
      = X + 2 * (Real.sqrt X * Real.sqrt Y) + Y := by
    rw [add_sq, h1, h2]; ring
  nlinarith [hexp, mul_nonneg (Real.sqrt_nonneg X) (Real.sqrt_nonneg Y)]

theorem E2_norm :
    ∃ κ : ℝ, 0 ≤ κ ∧ ∀ (α : ℝ), 0 < α → α ≤ 1 → ∀ (n : ℕ), n ≤ 3 → ∀ f : ℝ → ℝ → ℝ,
      Work.FTS.Nonlin.CoerAdm α f →
        Work.Spaces.HkNorm α n (Work.FTS.CoercivityFix.Transfer.E2 α f)
          ≤ κ * (Work.Spaces.HkNorm α n f
              + Work.Spaces.HkNorm α n (Work.Spaces.Dth f)) := by
  -- ## (0) the uniform constants
  obtain ⟨KB, hKBnn, hKB⟩ := E2norm.ampB_DzdIter_sq_w_sq_le
  obtain ⟨KC, hKCnn, hKC⟩ := E2norm.L12f_Transport_zero_sq_le
  obtain ⟨CE, hCEnn, hCE⟩ := E2norm.radS_DzdIter_le
  obtain ⟨KA, hKAnn, hKA⟩ := E2norm.gam_rad_integral_le
  obtain ⟨C0, hC0pos, hE2hat0⟩ := Work.FTS.CoercivityFix.Assembly.E2hat_HkSq_le_uniform 0
  obtain ⟨C1, hC1pos, hE2hat1⟩ := Work.FTS.CoercivityFix.Assembly.E2hat_HkSq_le_uniform 1
  obtain ⟨C2, hC2pos, hE2hat2⟩ := Work.FTS.CoercivityFix.Assembly.E2hat_HkSq_le_uniform 2
  obtain ⟨C3, hC3pos, hE2hat3⟩ := Work.FTS.CoercivityFix.Assembly.E2hat_HkSq_le_uniform 3
  let Cmax : ℝ := max (max C0 C1) (max C2 C3)
  let M : ℝ := 4 * KA * CE * (KB + 1) * (KC + 1)
  have hCmaxdef : Cmax = max (max C0 C1) (max C2 C3) := rfl
  have hMdef : M = 4 * KA * CE * (KB + 1) * (KC + 1) := rfl
  have hCmax_nn : 0 ≤ Cmax := by
    rw [hCmaxdef]
    have h : C0 ≤ max (max C0 C1) (max C2 C3) :=
      le_trans (le_max_left C0 C1) (le_max_left _ _)
    linarith
  have hKB1 : (0 : ℝ) ≤ KB + 1 := by linarith
  have hKC1 : (0 : ℝ) ≤ KC + 1 := by linarith
  have hMnn : 0 ≤ M := by
    rw [hMdef]
    exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hKAnn) hCEnn) hKB1) hKC1
  refine ⟨Real.sqrt (2 * Cmax + 2 * M), Real.sqrt_nonneg _, ?_⟩
  intro α hα hα1 n hn f hf
  have hreg1 : Work.FTS.Nonlin.RegQ α (n + 1) f :=
    Work.FTS.CoercivityFix.Assembly.regQ_mono (by omega) hf.reg
  -- ## (1) the `Ê₂` part
  have hE2hat : Work.Spaces.HkSq α n (Work.FTS.CoercivityFix.E2hat f)
      ≤ Cmax * (Work.Spaces.HkSq α n f + Work.Spaces.HkSq α n (Work.Spaces.Dth f)) := by
    have hZnn : 0 ≤ Work.Spaces.HkSq α n f + Work.Spaces.HkSq α n (Work.Spaces.Dth f) := by
      have h1 := Work.Spaces.HkSq_nonneg α n f
      have h2 := Work.Spaces.HkSq_nonneg α n (Work.Spaces.Dth f)
      linarith
    rcases (by omega : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3) with hn0 | hn1 | hn2 | hn3
    · subst hn0
      refine le_trans (hE2hat0 α (by linarith) f hreg1) ?_
      rw [hCmaxdef]
      exact mul_le_mul_of_nonneg_right (le_trans (le_max_left C0 C1) (le_max_left _ _)) hZnn
    · subst hn1
      refine le_trans (hE2hat1 α (by linarith) f hreg1) ?_
      rw [hCmaxdef]
      exact mul_le_mul_of_nonneg_right (le_trans (le_max_right C0 C1) (le_max_left _ _)) hZnn
    · subst hn2
      refine le_trans (hE2hat2 α (by linarith) f hreg1) ?_
      rw [hCmaxdef]
      exact mul_le_mul_of_nonneg_right (le_trans (le_max_left C2 C3) (le_max_right _ _)) hZnn
    · subst hn3
      refine le_trans (hE2hat3 α (by linarith) f hreg1) ?_
      rw [hCmaxdef]
      exact mul_le_mul_of_nonneg_right (le_trans (le_max_right C2 C3) (le_max_right _ _)) hZnn
  -- ## (2) the separated part `Γ·radS`
  have hKB' : ∀ c : ℕ, c ≤ 4 → ∫ z in Work.Spaces.Iz,
      (Work.Elliptic.DzdIter c (Work.FTS.CoercivityFix.Transfer.ampB α) z) ^ 2
        * (Work.Spaces.w z) ^ 2 ≤ KB :=
    fun c hc => (hKB α hα hα1 c hc).2
  have hCEx : ∀ j : ℕ, j ≤ n → ∫ z in Work.Spaces.Iz,
      (Work.Elliptic.DzdIter j (Work.FTS.CoercivityFix.Transfer.radS α f) z) ^ 2
        * (Work.Spaces.w z) ^ 2
      ≤ CE * (KB + 1) * (KC + 1)
        * (Work.Spaces.HkSq α n f + Work.Spaces.HkSq α n (Work.Spaces.Dth f)) :=
    fun j hj => hCE α hα hα1 n hn f hf KB hKBnn hKB' KC hKCnn
      (hKC α hα hα1 n hn f hf) j hj
  have hint_rad : ∀ j : ℕ, j ≤ n → MeasureTheory.IntegrableOn
      (fun z : ℝ => (Work.Elliptic.DzdIter j (Work.FTS.CoercivityFix.Transfer.radS α f) z) ^ 2
        * (Work.Spaces.w z) ^ 2) Work.Spaces.Iz :=
    fun j hj => Work.FTS.CoercivityFix.Transfer.E2pkg.radS_DzdIter_sq_w_sq_integrable α hα hα1
      hf j (by omega)
  have hintRadMaj : MeasureTheory.IntegrableOn
      (fun z : ℝ => ∑ j ∈ Finset.range (n + 1),
        (Work.Elliptic.DzdIter j (Work.FTS.CoercivityFix.Transfer.radS α f) z) ^ 2
          * (Work.Spaces.w z) ^ 2) Work.Spaces.Iz :=
    MeasureTheory.integrable_finsetSum _ (fun j hj => by
      have hj' : j ≤ n := by
        have h := Finset.mem_range.mp hj
        omega
      exact hint_rad j hj')
  -- the angular reduction, integrated in `z`
  have hgam : Work.Spaces.HkSq α n
        (fun z θ => Work.Spaces.Gam α θ * Work.FTS.CoercivityFix.Transfer.radS α f z)
      ≤ KA * ∫ z in Work.Spaces.Iz, (∑ j ∈ Finset.range (n + 1),
          (Work.Elliptic.DzdIter j (Work.FTS.CoercivityFix.Transfer.radS α f) z) ^ 2
            * (Work.Spaces.w z) ^ 2) := by
    have hstep := MeasureTheory.integral_mono_of_nonneg
      (Filter.Eventually.of_forall fun z => MeasureTheory.integral_nonneg fun θ =>
        Work.Spaces.HkIntegrand_nonneg α n
          (fun z θ => Work.Spaces.Gam α θ * Work.FTS.CoercivityFix.Transfer.radS α f z) z θ)
      (hintRadMaj.const_mul KA)
      (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ici
        (fun z hz => hKA α hα hα1 n hn
          (Work.FTS.CoercivityFix.Transfer.radS α f) z hz))
    rw [Work.Spaces.HkSq]
    calc ∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
          Work.Spaces.HkIntegrand α n
            (fun z θ => Work.Spaces.Gam α θ * Work.FTS.CoercivityFix.Transfer.radS α f z) z θ
        ≤ ∫ z in Work.Spaces.Iz, KA * (∑ j ∈ Finset.range (n + 1),
            (Work.Elliptic.DzdIter j (Work.FTS.CoercivityFix.Transfer.radS α f) z) ^ 2
              * (Work.Spaces.w z) ^ 2) := hstep
      _ = KA * ∫ z in Work.Spaces.Iz, (∑ j ∈ Finset.range (n + 1),
            (Work.Elliptic.DzdIter j (Work.FTS.CoercivityFix.Transfer.radS α f) z) ^ 2
              * (Work.Spaces.w z) ^ 2) :=
          MeasureTheory.integral_const_mul KA _
  -- the radial sum
  have hsum : ∫ z in Work.Spaces.Iz, (∑ j ∈ Finset.range (n + 1),
        (Work.Elliptic.DzdIter j (Work.FTS.CoercivityFix.Transfer.radS α f) z) ^ 2
          * (Work.Spaces.w z) ^ 2)
      ≤ 4 * (CE * (KB + 1) * (KC + 1)
          * (Work.Spaces.HkSq α n f + Work.Spaces.HkSq α n (Work.Spaces.Dth f))) := by
    rw [MeasureTheory.integral_finsetSum _ (fun j hj => by
      have hj' : j ≤ n := by
        have h := Finset.mem_range.mp hj
        omega
      exact hint_rad j hj')]
    have h1 : (∑ j ∈ Finset.range (n + 1), ∫ z in Work.Spaces.Iz,
          (Work.Elliptic.DzdIter j (Work.FTS.CoercivityFix.Transfer.radS α f) z) ^ 2
            * (Work.Spaces.w z) ^ 2)
        ≤ ∑ _j ∈ Finset.range (n + 1), CE * (KB + 1) * (KC + 1)
            * (Work.Spaces.HkSq α n f + Work.Spaces.HkSq α n (Work.Spaces.Dth f)) :=
      Finset.sum_le_sum (fun j hj => by
        have hj' : j ≤ n := by
          have h := Finset.mem_range.mp hj
          omega
        exact hCEx j hj')
    have h2 : (∑ _j ∈ Finset.range (n + 1), CE * (KB + 1) * (KC + 1)
            * (Work.Spaces.HkSq α n f + Work.Spaces.HkSq α n (Work.Spaces.Dth f)))
        = ((n : ℝ) + 1) * (CE * (KB + 1) * (KC + 1)
            * (Work.Spaces.HkSq α n f + Work.Spaces.HkSq α n (Work.Spaces.Dth f))) := by
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      push_cast
      ring
    have h3 : ((n : ℝ) + 1) ≤ 4 := by
      have hn' : (n : ℝ) ≤ 3 := by exact_mod_cast hn
      linarith
    have h4 : 0 ≤ CE * (KB + 1) * (KC + 1)
        * (Work.Spaces.HkSq α n f + Work.Spaces.HkSq α n (Work.Spaces.Dth f)) := by
      have h7 : (0 : ℝ) ≤ Work.Spaces.HkSq α n f + Work.Spaces.HkSq α n
          (Work.Spaces.Dth f) := by
        have h7a := Work.Spaces.HkSq_nonneg α n f
        have h7b := Work.Spaces.HkSq_nonneg α n (Work.Spaces.Dth f)
        linarith
      exact mul_nonneg (mul_nonneg (mul_nonneg hCEnn hKB1) hKC1) h7
    calc (∑ j ∈ Finset.range (n + 1), ∫ z in Work.Spaces.Iz,
          (Work.Elliptic.DzdIter j (Work.FTS.CoercivityFix.Transfer.radS α f) z) ^ 2
            * (Work.Spaces.w z) ^ 2)
        ≤ ∑ _j ∈ Finset.range (n + 1), CE * (KB + 1) * (KC + 1)
            * (Work.Spaces.HkSq α n f + Work.Spaces.HkSq α n (Work.Spaces.Dth f)) := h1
      _ = ((n : ℝ) + 1) * (CE * (KB + 1) * (KC + 1)
            * (Work.Spaces.HkSq α n f + Work.Spaces.HkSq α n (Work.Spaces.Dth f))) := h2
      _ ≤ 4 * (CE * (KB + 1) * (KC + 1)
            * (Work.Spaces.HkSq α n f + Work.Spaces.HkSq α n (Work.Spaces.Dth f))) :=
          mul_le_mul_of_nonneg_right h3 h4
  have hGam : Work.Spaces.HkSq α n
        (fun z θ => Work.Spaces.Gam α θ * Work.FTS.CoercivityFix.Transfer.radS α f z)
      ≤ M * (Work.Spaces.HkSq α n f + Work.Spaces.HkSq α n (Work.Spaces.Dth f)) := by
    calc Work.Spaces.HkSq α n
          (fun z θ => Work.Spaces.Gam α θ * Work.FTS.CoercivityFix.Transfer.radS α f z)
        ≤ KA * ∫ z in Work.Spaces.Iz, (∑ j ∈ Finset.range (n + 1),
            (Work.Elliptic.DzdIter j (Work.FTS.CoercivityFix.Transfer.radS α f) z) ^ 2
              * (Work.Spaces.w z) ^ 2) := hgam
      _ ≤ KA * (4 * (CE * (KB + 1) * (KC + 1)
            * (Work.Spaces.HkSq α n f + Work.Spaces.HkSq α n (Work.Spaces.Dth f)))) :=
          mul_le_mul_of_nonneg_left hsum hKAnn
      _ = M * (Work.Spaces.HkSq α n f + Work.Spaces.HkSq α n (Work.Spaces.Dth f)) := by
          rw [hMdef]; ring
  -- ## (3) the split
  have hcd1 : ContDiffOn ℝ (n : ℕ∞)
      (Function.uncurry (Work.FTS.CoercivityFix.E2hat f))
      Work.FTS.CoercivityFix.Transfer.E2pkg.Qd :=
    (Work.FTS.CoercivityFix.Transfer.AuxE2.E2hat_contDiffOn_three hf.reg.1).of_le
      (Nat.cast_le.mpr hn)
  have hcd2 : ContDiffOn ℝ (n : ℕ∞)
      (Function.uncurry (fun z θ => Work.Spaces.Gam α θ * Work.FTS.CoercivityFix.Transfer.radS α f z))
      Work.FTS.CoercivityFix.Transfer.E2pkg.Qd :=
    Work.FTS.CoercivityFix.Transfer.E2pkg.contDiffOn_uncurry_gam_rad α hα hα1 hf hn
  have hsplit : Work.Spaces.HkSq α n (Work.FTS.CoercivityFix.Transfer.E2 α f)
      ≤ 2 * Work.Spaces.HkSq α n (Work.FTS.CoercivityFix.E2hat f)
        + 2 * Work.Spaces.HkSq α n
            (fun z θ => Work.Spaces.Gam α θ * Work.FTS.CoercivityFix.Transfer.radS α f z) := by
    have h1 : Work.Spaces.HkMem α n (Work.FTS.CoercivityFix.E2hat f) :=
      (Work.FTS.CoercivityFix.Assembly.E2hat_RegQ α hα hreg1).2.1
    have h2 : Work.Spaces.HkMem α n
        (fun z θ => Work.Spaces.Gam α θ * Work.FTS.CoercivityFix.Transfer.radS α f z) :=
      Work.FTS.CoercivityFix.Transfer.E2pkg.HkMem_gam_rad α hα hα1 hf hn
    have h3 : Work.Spaces.HkMem α n (Work.FTS.CoercivityFix.Transfer.E2 α f) :=
      (Work.FTS.CoercivityFix.Transfer.E2_pkg α hα hα1 n hn f hf).1
    have hpt := Work.FTS.CoercivityFix.Transfer.E2pkg.hkIntegrand_add_le_of_contDiffOn α n hcd1 hcd2
    exact E2norm.HkSq_add_le α n h1 h2 h3 hpt
  -- ## (4) the assembly and the square root
  have htotal : Work.Spaces.HkSq α n (Work.FTS.CoercivityFix.Transfer.E2 α f)
      ≤ (2 * Cmax + 2 * M)
          * (Work.Spaces.HkSq α n f + Work.Spaces.HkSq α n (Work.Spaces.Dth f)) := by
    have h1 : 2 * Work.Spaces.HkSq α n (Work.FTS.CoercivityFix.E2hat f)
        ≤ 2 * (Cmax * (Work.Spaces.HkSq α n f + Work.Spaces.HkSq α n (Work.Spaces.Dth f))) :=
      mul_le_mul_of_nonneg_left hE2hat (by norm_num)
    have h2 : 2 * Work.Spaces.HkSq α n
          (fun z θ => Work.Spaces.Gam α θ * Work.FTS.CoercivityFix.Transfer.radS α f z)
        ≤ 2 * (M * (Work.Spaces.HkSq α n f + Work.Spaces.HkSq α n (Work.Spaces.Dth f))) :=
      mul_le_mul_of_nonneg_left hGam (by norm_num)
    calc Work.Spaces.HkSq α n (Work.FTS.CoercivityFix.Transfer.E2 α f)
        ≤ 2 * Work.Spaces.HkSq α n (Work.FTS.CoercivityFix.E2hat f)
          + 2 * Work.Spaces.HkSq α n
              (fun z θ => Work.Spaces.Gam α θ * Work.FTS.CoercivityFix.Transfer.radS α f z) := hsplit
      _ ≤ 2 * (Cmax * (Work.Spaces.HkSq α n f + Work.Spaces.HkSq α n (Work.Spaces.Dth f)))
          + 2 * (M * (Work.Spaces.HkSq α n f + Work.Spaces.HkSq α n (Work.Spaces.Dth f))) := by
          linarith
      _ = (2 * Cmax + 2 * M)
          * (Work.Spaces.HkSq α n f + Work.Spaces.HkSq α n (Work.Spaces.Dth f)) := by ring
  have hKnn : 0 ≤ 2 * Cmax + 2 * M := by linarith
  rw [Work.Spaces.HkNorm]
  calc Real.sqrt (Work.Spaces.HkSq α n (Work.FTS.CoercivityFix.Transfer.E2 α f))
      ≤ Real.sqrt ((2 * Cmax + 2 * M)
          * (Work.Spaces.HkSq α n f + Work.Spaces.HkSq α n (Work.Spaces.Dth f))) :=
        Real.sqrt_le_sqrt htotal
    _ = Real.sqrt (2 * Cmax + 2 * M)
        * Real.sqrt (Work.Spaces.HkSq α n f + Work.Spaces.HkSq α n (Work.Spaces.Dth f)) :=
        Real.sqrt_mul hKnn _
    _ ≤ Real.sqrt (2 * Cmax + 2 * M)
        * (Real.sqrt (Work.Spaces.HkSq α n f)
            + Real.sqrt (Work.Spaces.HkSq α n (Work.Spaces.Dth f))) :=
        mul_le_mul_of_nonneg_left
          (sqrt_add_le_sqrt_add_sqrt (Work.Spaces.HkSq_nonneg α n f)
            (Work.Spaces.HkSq_nonneg α n (Work.Spaces.Dth f)))
          (Real.sqrt_nonneg _)
    _ = Real.sqrt (2 * Cmax + 2 * M)
        * (Work.Spaces.HkNorm α n f + Work.Spaces.HkNorm α n (Work.Spaces.Dth f)) := by
        rw [Work.Spaces.HkNorm, Work.Spaces.HkNorm]

end Work.FTS.CoercivityFix.Transfer
