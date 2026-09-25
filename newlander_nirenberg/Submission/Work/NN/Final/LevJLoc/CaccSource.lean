import Mathlib
import Submission.Work.NN.Core.Lev.powCaccioppoliSource

/-!
# The level-`0` Caccioppoli source estimate

`Work.NN.Core.Lev.powCaccioppoliSource` with the smallness hypothesis on the perturbation at
Hölder level `0` instead of level `1`, and with the almost-complexity hypothesis
`(Jstd+A')² = -1` localised to the polydisc `polydisc 0 ρ` (it is unused in the proof).  The proof is a verbatim copy of the original, whose only
use of the smallness hypothesis is the pointwise bound obtained from
`Work.CR.Flat.norm_apply_le_holderNorm` (an arbitrary-level statement).
-/

namespace Work.NN.Final.LevJLoc

open scoped NNReal ENNReal ContDiff Topology
open Set MeasureTheory Filter
open Work.NN.Core Work.NN.Core.Lev

noncomputable section

variable {n : ℕ}

theorem powCaccioppoliSource_v {n : ℕ} (hn : 0 < n) {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    {ρ : Fin n → ℝ} (hρ0 : ∀ j, 0 < ρ j) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∃ A : ℝ, 0 < A ∧
      ∀ {A' : Work.NN.Core.Cn n → Work.NN.Core.Cn n →L[ℝ] Work.NN.Core.Cn n},
        (∀ m : ℕ, ContDiff ℝ m A') → ∀ {ε : ℝ}, ε ≤ ε₀ →
        (∀ i j : Fin n, Work.CR.Flat.holderNorm 0 α
            (fun z => A' z (Pi.single i 1) j) (Work.CR.Flat.polydisc 0 ρ) ≤ ENNReal.ofReal ε) →
        (∀ z, z ∈ Work.CR.Flat.polydisc 0 ρ → ∀ v : Work.NN.Core.Cn n,
          (Work.NN.Core.JstdCn n + A') z ((Work.NN.Core.JstdCn n + A') z v) = -v) →
        ∀ (k : ℕ), 1 ≤ k → ∀ (u : Work.NN.Core.Cn n → ℂ),
          ContDiffOn ℝ 1 u (Work.CR.Flat.polydisc 0 ρ) → ∀ {Λ : ℝ}, 0 ≤ Λ →
          (∀ z ∈ Work.CR.Flat.polydisc 0 ρ,
            ∑ j : Fin n,
              ‖Work.NN.Core.dbarCn (Work.NN.Core.JstdCn n + A') u z (Pi.single j 1)‖^2 ≤ Λ^2) →
          ∀ φ : Work.NN.Core.Cn n → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
            tsupport φ ⊆ Work.CR.Flat.polydisc 0 ρ → (∀ z, 0 ≤ φ z) →
            ∫ z in Work.CR.Flat.polydisc 0 ρ,
                (k : ℝ)^2 * (φ z)^2 * (‖u z‖^2)^(k-1) *
                  (∑ j : Fin n, (‖Work.CR.Flat.dCoord j u z‖^2
                    + ‖Work.CR.Flat.dbarCoord j u z‖^2))
              ≤ A * ((∫ z in Work.CR.Flat.polydisc 0 ρ,
                        ‖fderiv ℝ φ z‖^2 * (‖u z‖^2)^k)
                    + (k : ℝ)^2 * ∫ z in Work.CR.Flat.polydisc 0 ρ,
                        (φ z)^2 * (‖u z‖^2)^(k-1) * Λ^2) := by
  set ε₀ : ℝ := 1 / (16 * ((n : ℝ) + 1)) with hε₀def
  have hε₀pos : 0 < ε₀ := by rw [hε₀def]; positivity
  have hε₀ineq : 24 * (n : ℝ) ^ 2 * ε₀ ^ 2 ≤ 1 / 2 := by
    rw [hε₀def, div_eq_mul_inv, mul_pow, inv_pow]
    have h1 : (16 * ((n : ℝ) + 1)) ≠ 0 := by positivity
    have h2 : (0:ℝ) ≤ (n:ℝ) := Nat.cast_nonneg n
    have h3 : (n:ℝ)^2 ≤ ((n:ℝ)+1)^2 := by nlinarith
    field_simp
    nlinarith [h2, h3]
  set A : ℝ := max 20 (16 * (n : ℝ)) with hAdef
  have hApos : 0 < A := by
    rw [hAdef]; exact lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  have hAle20 : (20:ℝ) ≤ A := by rw [hAdef]; exact le_max_left _ _
  have hAle16n : (16:ℝ) * (n:ℝ) ≤ A := by rw [hAdef]; exact le_max_right _ _
  refine ⟨ε₀, hε₀pos, A, hApos, ?_⟩
  intro A' hA'sm ε hεle hholder hJ k hk u hu Λ hΛ hdbar φ hφsm hφcs hφsupp hφ0
  have hφC1 : ContDiff ℝ 1 φ := hφsm.of_le (by simp)
  have hφd : ∀ z : Cn n, DifferentiableAt ℝ φ z := fun z => hφC1.differentiable_one z
  obtain ⟨χ, V, hχsm, hχcs, hχU, hVopen, hφV, hχone⟩ :=
    exists_contDiff_bump_of_isCompact_subset hφcs (Work.CR.Flat.isOpen_polydisc 0 ρ) hφsupp
  have hχC1 : ContDiff ℝ 1 χ := hχsm.of_le (by norm_num)
  set η : Cn n → ℂ := fun z => (φ z : ℂ) with hηdef
  set H : Cn n → ℂ := fun z => χ z * (u z) ^ k with hHdef
  set u' : Cn n → ℂ := fun z => χ z * u z with hu'def
  have hηc : ContDiff ℝ 1 η := by
    have h2 : ContDiff ℝ 1 (⇑Complex.ofRealCLM ∘ φ) :=
      (ContinuousLinearMap.contDiff (𝕜 := ℝ) (n := 1) Complex.ofRealCLM).comp (hφsm.of_le (by simp))
    simpa [hηdef, Function.comp_def, Complex.ofRealCLM_apply] using h2
  have hηcs : HasCompactSupport η := by
    rw [hηdef]
    exact IsCompact.of_isClosed_subset hφcs (isClosed_tsupport _) (by rw [tsupport_ofReal])
  have hu'c : ContDiff ℝ 1 u' := by
    rw [hu'def]
    exact contDiff_mul_of_tsupp_subset (Work.CR.Flat.isOpen_polydisc 0 ρ) hχC1 hχcs hχU hu
  have huPow : ContDiffOn ℝ 1 (fun z => (u z) ^ k) (Work.CR.Flat.polydisc 0 ρ) :=
    contDiffOn_pow hu k
  have hHc : ContDiff ℝ 1 H := by
    rw [hHdef]
    exact contDiff_mul_of_tsupp_subset (Work.CR.Flat.isOpen_polydisc 0 ρ) hχC1 hχcs hχU huPow
  have hHcs : HasCompactSupport H := by rw [hHdef]; exact hχcs.mul_right
  have hA'cont : Continuous A' := contDiff_zero.mp (hA'sm 0)
  have hAsm : ∀ z ∈ tsupport η, ∀ i j : Fin n, ‖A' z (Pi.single i 1) j‖ ≤ ε₀ := by
    intro z hz i j
    have hz1 : z ∈ Work.CR.Flat.polydisc 0 ρ := by
      rw [hηdef, tsupport_ofReal] at hz
      exact hφsupp hz
    have h1 := Work.CR.Flat.norm_apply_le_holderNorm 0 α
      (fun z => A' z (Pi.single i 1) j) (Work.CR.Flat.polydisc 0 ρ) hz1
    have h2 := hholder i j
    have h3 : ENNReal.ofReal ‖A' z (Pi.single i 1) j‖ ≤ ENNReal.ofReal ε₀ :=
      le_trans h1 (le_trans h2 (ENNReal.ofReal_le_ofReal hεle))
    exact (ENNReal.ofReal_le_ofReal_iff hε₀pos.le).mp h3
  have hI := weightedEnergyPerturbed (n := n) (A' := A') (ε := ε₀)
    hε₀pos.le hε₀ineq hηc hHc hηcs hHcs hA'cont hAsm
  have hηsq : ∀ z : Cn n, ‖η z‖ ^ 2 = (φ z) ^ 2 := by
    intro z
    rw [hηdef, Complex.norm_def, Complex.normSq_ofReal, Real.sq_sqrt (mul_self_nonneg (φ z)), sq]
  have hzp_of : ∀ z ∈ tsupport φ, z ∈ Work.CR.Flat.polydisc 0 ρ := fun z hz => hφsupp hz
  have hud : ∀ z ∈ tsupport φ, DifferentiableAt ℝ u z := by
    intro z hz
    have h1 : ContDiffAt ℝ 1 u z :=
      hu.contDiffAt ((Work.CR.Flat.isOpen_polydisc 0 ρ).mem_nhds (hzp_of z hz))
    exact h1.differentiableAt (by norm_num)
  have hevV : ∀ z ∈ tsupport φ, H =ᶠ[𝓝 z] (fun w => (u w) ^ k) := by
    intro z hz
    rw [hHdef]
    filter_upwards [hVopen.mem_nhds (hφV hz)] with w hw
    rw [hχone w hw, one_mul]
  have hu'eq : ∀ z ∈ tsupport φ, u' z = u z := by
    intro z hz
    simp only [hu'def, hχone z (hφV hz), one_mul]
  have hL : ∀ z : Cn n, (‖u z‖ ^ (k - 1)) ^ 2 = (‖u z‖ ^ 2) ^ (k - 1) := by
    intro z
    rw [← pow_mul, ← pow_mul, show (k - 1) * 2 = 2 * (k - 1) from by ring]
  -- ===== the left hand side =====
  have hGT : ∀ z : Cn n, ‖η z‖ ^ 2 * (∑ j : Fin n, (‖Work.CR.Flat.dCoord j H z‖ ^ 2
        + ‖Work.CR.Flat.dbarCoord j H z‖ ^ 2))
      = (k : ℝ) ^ 2 * (φ z) ^ 2 * (‖u z‖ ^ 2) ^ (k - 1)
        * (∑ j : Fin n, (‖Work.CR.Flat.dCoord j u z‖ ^ 2
            + ‖Work.CR.Flat.dbarCoord j u z‖ ^ 2)) := by
    intro z
    rw [hηsq z]
    by_cases hz : φ z = 0
    · rw [hz]; simp
    · have hzts : z ∈ tsupport φ := subset_closure (Function.mem_support.mpr hz)
      have hd := hud z hzts
      have hev := hevV z hzts
      have hsum : (∑ j : Fin n, (‖Work.CR.Flat.dCoord j H z‖ ^ 2
            + ‖Work.CR.Flat.dbarCoord j H z‖ ^ 2))
          = (k : ℝ) ^ 2 * (‖u z‖ ^ 2) ^ (k - 1) * (∑ j : Fin n,
              (‖Work.CR.Flat.dCoord j u z‖ ^ 2 + ‖Work.CR.Flat.dbarCoord j u z‖ ^ 2)) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        have hcd : Work.CR.Flat.dCoord j H z = (k : ℂ) * (u z) ^ (k - 1)
            * Work.CR.Flat.dCoord j u z := by
          rw [dCoord_congr_of_eventuallyEq j hev, dCoord_pow j u z k hd]
        have hbd : Work.CR.Flat.dbarCoord j H z = (k : ℂ) * (u z) ^ (k - 1)
            * Work.CR.Flat.dbarCoord j u z := by
          rw [dbarCoord_congr_of_eventuallyEq j hev, dbarCoord_pow j u z k hd]
        have e1 : ‖Work.CR.Flat.dCoord j H z‖ ^ 2
            = (k:ℝ)^2 * (‖u z‖^2)^(k-1) * ‖Work.CR.Flat.dCoord j u z‖ ^ 2 := by
          have hc := congrArg (fun w : ℂ => ‖w‖ ^ 2) hcd
          simp only [norm_mul, mul_pow, Complex.norm_natCast, norm_pow] at hc
          rw [hc, hL z]
        have e2 : ‖Work.CR.Flat.dbarCoord j H z‖ ^ 2
            = (k:ℝ)^2 * (‖u z‖^2)^(k-1) * ‖Work.CR.Flat.dbarCoord j u z‖ ^ 2 := by
          have hc := congrArg (fun w : ℂ => ‖w‖ ^ 2) hbd
          simp only [norm_mul, mul_pow, Complex.norm_natCast, norm_pow] at hc
          rw [hc, hL z]
        rw [e1, e2]; ring
      rw [hsum]; ring
  -- ===== the `Y` term =====
  have hYbd : ∀ z : Cn n, ‖η z‖ ^ 2 * (∑ j : Fin n,
        ‖dbarCn (JstdCn n + A') H z (Pi.single j (1:ℂ))‖ ^ 2)
      ≤ (k:ℝ)^2 * (φ z)^2 * (‖u z‖^2)^(k-1) * Λ^2 := by
    intro z
    rw [hηsq z]
    by_cases hz : φ z = 0
    · rw [hz]; simp
    · have hzts : z ∈ tsupport φ := subset_closure (Function.mem_support.mpr hz)
      have hzp2 := hzp_of z hzts
      have hd := hud z hzts
      have hev := hevV z hzts
      have hY : (∑ j : Fin n, ‖dbarCn (JstdCn n + A') H z (Pi.single j (1:ℂ))‖ ^ 2)
          = (k:ℝ)^2 * (‖u z‖^2)^(k-1) * (∑ j : Fin n,
              ‖dbarCn (JstdCn n + A') u z (Pi.single j (1:ℂ))‖ ^ 2) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        have h1 : dbarCn (JstdCn n + A') H z (Pi.single j (1:ℂ))
            = (k:ℂ) * (u z)^(k-1) * dbarCn (JstdCn n + A') u z (Pi.single j (1:ℂ)) := by
          rw [dbarCn_congr_of_eventuallyEq _ hev,
            dbarCn_pow (JstdCn n + A') u z (Pi.single j (1:ℂ)) k hd]
        have hc := congrArg (fun w : ℂ => ‖w‖ ^ 2) h1
        simp only [norm_mul, mul_pow, Complex.norm_natCast, norm_pow] at hc
        rw [hc, hL z]
      rw [hY]
      have h1 : (k:ℝ)^2 * (‖u z‖^2)^(k-1) * (∑ j : Fin n,
            ‖dbarCn (JstdCn n + A') u z (Pi.single j (1:ℂ))‖ ^ 2)
          ≤ (k:ℝ)^2 * (‖u z‖^2)^(k-1) * Λ^2 :=
        mul_le_mul_of_nonneg_left (hdbar z hzp2) (by positivity)
      calc (φ z) ^ 2 * ((k:ℝ)^2 * (‖u z‖^2)^(k-1) * (∑ j : Fin n,
              ‖dbarCn (JstdCn n + A') u z (Pi.single j (1:ℂ))‖ ^ 2))
          ≤ (φ z) ^ 2 * ((k:ℝ)^2 * (‖u z‖^2)^(k-1) * Λ^2) :=
            mul_le_mul_of_nonneg_left h1 (sq_nonneg _)
        _ = (k:ℝ)^2 * (φ z)^2 * (‖u z‖^2)^(k-1) * Λ^2 := by ring
  -- ===== the `M` term =====
  have hMbd : ∀ z : Cn n, ‖H z‖ ^ 2 * (∑ j : Fin n, (‖Work.CR.Flat.dCoord j η z‖ ^ 2
        + ‖Work.CR.Flat.dbarCoord j η z‖ ^ 2))
      ≤ 2 * (n:ℝ) * ‖fderiv ℝ φ z‖ ^ 2 * (‖u' z‖ ^ 2) ^ k := by
    intro z
    by_cases hz : (∑ j : Fin n, (‖Work.CR.Flat.dCoord j η z‖ ^ 2
        + ‖Work.CR.Flat.dbarCoord j η z‖ ^ 2)) = 0
    · rw [hz, mul_zero]; positivity
    · have hzts : z ∈ tsupport φ := by
        by_contra hc
        refine hz ?_
        have hf0 : fderiv ℝ η z = 0 := by
          rw [hηdef]
          exact fderiv_of_notMem_tsupport ℝ (by rwa [tsupport_ofReal])
        refine Finset.sum_eq_zero fun j _ => ?_
        rw [Work.CR.Flat.dCoord, Work.CR.Flat.dbarCoord, hf0]
        simp
      have hHz : ‖H z‖ ^ 2 = (‖u' z‖ ^ 2) ^ k := by
        have h1 : H z = (u z)^k := by
          simp only [hHdef, hχone z (hφV hzts), one_mul]
        have h2 : u' z = u z := hu'eq z hzts
        rw [h1, h2, norm_pow]
        rw [show (‖u z‖ ^ k) ^ 2 = (‖u z‖ ^ 2) ^ k from by
          rw [← pow_mul, ← pow_mul, show k * 2 = 2 * k from by ring]]
      rw [hHz]
      have h1 := sum_dCoord_ofReal_le (hφd z)
      have h2 : (0:ℝ) ≤ (‖u' z‖ ^ 2) ^ k := by positivity
      calc (‖u' z‖ ^ 2) ^ k * (∑ j : Fin n, (‖Work.CR.Flat.dCoord j η z‖ ^ 2
              + ‖Work.CR.Flat.dbarCoord j η z‖ ^ 2))
          ≤ (‖u' z‖ ^ 2) ^ k * (2 * (n:ℝ) * ‖fderiv ℝ φ z‖ ^ 2) :=
            mul_le_mul_of_nonneg_left h1 h2
        _ = 2 * (n:ℝ) * ‖fderiv ℝ φ z‖ ^ 2 * (‖u' z‖ ^ 2) ^ k := by ring
  -- ===== integrability =====
  have hJ' : Continuous (fun z : Cn n => (JstdCn n + A') z) := by
    have heq : (fun z : Cn n => (JstdCn n + A') z) = fun z => JstdCn n z + A' z := by
      funext z; simp [Pi.add_apply]
    rw [heq]
    exact (continuous_const : Continuous (fun z : Cn n => JstdCn n z)).add hA'cont
  have hGYint : Integrable (fun z => ‖η z‖ ^ 2 * (∑ j : Fin n,
      ‖dbarCn (JstdCn n + A') H z (Pi.single j (1:ℂ))‖ ^ 2)) := by
    have hcont : Continuous (fun z => ‖η z‖ ^ 2 * (∑ j : Fin n,
        ‖dbarCn (JstdCn n + A') H z (Pi.single j (1:ℂ))‖ ^ 2)) :=
      (hηc.continuous.norm.pow 2).mul
        (continuous_finsetSum _ (fun j _ => (continuous_dbarCn_apply hJ' hHc _).norm.pow 2))
    have hsub : tsupport (fun z => ‖η z‖ ^ 2 * (∑ j : Fin n,
        ‖dbarCn (JstdCn n + A') H z (Pi.single j (1:ℂ))‖ ^ 2)) ⊆ tsupport φ :=
      tsupport_subset_of_eq_zero_off
        (f := fun z => ‖η z‖ ^ 2 * (∑ j : Fin n,
          ‖dbarCn (JstdCn n + A') H z (Pi.single j (1:ℂ))‖ ^ 2))
        (g := φ) (fun z hz => by
          have h0 : φ z = 0 := by
            by_contra h
            exact hz (subset_closure (Function.mem_support.mpr h))
          have hη0 : η z = 0 := by simp only [hηdef, h0, Complex.ofReal_zero]
          rw [hη0, norm_zero]; ring)
    exact Continuous.integrable_of_hasCompactSupport hcont
      (IsCompact.of_isClosed_subset hφcs (isClosed_tsupport _) hsub)
  have hYu'int : Integrable (fun z => (k:ℝ)^2 * (φ z)^2 * (‖u' z‖^2)^(k-1) * Λ^2) := by
    have hcont : Continuous (fun z => (k:ℝ)^2 * (φ z)^2 * (‖u' z‖^2)^(k-1) * Λ^2) :=
      (((continuous_const.mul ((hφC1.continuous).pow 2)).mul
        ((hu'c.continuous.norm.pow 2).pow (k-1))).mul continuous_const)
    have hsub : tsupport (fun z => (k:ℝ)^2 * (φ z)^2 * (‖u' z‖^2)^(k-1) * Λ^2) ⊆ tsupport φ :=
      tsupport_subset_of_eq_zero_off
        (f := fun z => (k:ℝ)^2 * (φ z)^2 * (‖u' z‖^2)^(k-1) * Λ^2)
        (g := φ) (fun z hz => by
          have h0 : φ z = 0 := by
            by_contra h; exact hz (subset_closure (Function.mem_support.mpr h))
          rw [h0]; ring)
    exact Continuous.integrable_of_hasCompactSupport hcont
      (IsCompact.of_isClosed_subset hφcs (isClosed_tsupport _) hsub)
  have hGMint : Integrable (fun z => ‖H z‖ ^ 2 * (∑ j : Fin n,
      (‖Work.CR.Flat.dCoord j η z‖ ^ 2 + ‖Work.CR.Flat.dbarCoord j η z‖ ^ 2))) := by
    have hcont : Continuous (fun z => ‖H z‖ ^ 2 * (∑ j : Fin n,
        (‖Work.CR.Flat.dCoord j η z‖ ^ 2 + ‖Work.CR.Flat.dbarCoord j η z‖ ^ 2))) :=
      (hHc.continuous.norm.pow 2).mul (continuous_finsetSum _ (fun j _ =>
        ((Work.NN.Core.continuous_dCoord j hηc).norm.pow 2).add
          ((Work.NN.Core.continuous_dbarCoord j hηc).norm.pow 2)))
    have hsub : tsupport (fun z => ‖H z‖ ^ 2 * (∑ j : Fin n,
        (‖Work.CR.Flat.dCoord j η z‖ ^ 2 + ‖Work.CR.Flat.dbarCoord j η z‖ ^ 2))) ⊆ tsupport φ :=
      tsupport_subset_of_eq_zero_off
        (f := fun z => ‖H z‖ ^ 2 * (∑ j : Fin n,
          (‖Work.CR.Flat.dCoord j η z‖ ^ 2 + ‖Work.CR.Flat.dbarCoord j η z‖ ^ 2)))
        (g := φ) (fun z hz => by
          have hzη : z ∉ tsupport η := by rwa [hηdef, tsupport_ofReal]
          have hf0 : fderiv ℝ η z = 0 := fderiv_of_notMem_tsupport ℝ hzη
          have hsum0 : (∑ j : Fin n, (‖Work.CR.Flat.dCoord j η z‖ ^ 2
              + ‖Work.CR.Flat.dbarCoord j η z‖ ^ 2)) = 0 := by
            refine Finset.sum_eq_zero fun j _ => ?_
            rw [Work.CR.Flat.dCoord, Work.CR.Flat.dbarCoord, hf0]
            simp
          rw [hsum0, mul_zero])
    exact Continuous.integrable_of_hasCompactSupport hcont
      (IsCompact.of_isClosed_subset hφcs (isClosed_tsupport _) hsub)
  have hMu'int : Integrable (fun z => 2 * (n:ℝ) * ‖fderiv ℝ φ z‖ ^ 2 * (‖u' z‖ ^ 2) ^ k) := by
    have hcont : Continuous (fun z => 2 * (n:ℝ) * ‖fderiv ℝ φ z‖ ^ 2 * (‖u' z‖ ^ 2) ^ k) :=
      ((continuous_const.mul (((hφC1.continuous_fderiv (by norm_num)).norm).pow 2)).mul
        ((hu'c.continuous.norm.pow 2).pow k))
    have hsub : tsupport (fun z => 2 * (n:ℝ) * ‖fderiv ℝ φ z‖ ^ 2 * (‖u' z‖ ^ 2) ^ k)
        ⊆ tsupport φ :=
      tsupport_subset_of_eq_zero_off
        (f := fun z => 2 * (n:ℝ) * ‖fderiv ℝ φ z‖ ^ 2 * (‖u' z‖ ^ 2) ^ k)
        (g := φ) (fun z hz => by
          have hf0 : fderiv ℝ φ z = 0 := fderiv_of_notMem_tsupport ℝ hz
          rw [hf0, norm_zero]; ring)
    exact Continuous.integrable_of_hasCompactSupport hcont
      (IsCompact.of_isClosed_subset hφcs (isClosed_tsupport _) hsub)
  -- ===== integral bounds =====
  have hYle : ∫ z, ‖η z‖ ^ 2 * (∑ j : Fin n,
        ‖dbarCn (JstdCn n + A') H z (Pi.single j (1:ℂ))‖ ^ 2)
      ≤ (k:ℝ)^2 * ∫ z in Work.CR.Flat.polydisc 0 ρ,
          (φ z)^2 * (‖u z‖^2)^(k-1) * Λ^2 := by
    have h1 : ∫ z, ‖η z‖ ^ 2 * (∑ j : Fin n,
          ‖dbarCn (JstdCn n + A') H z (Pi.single j (1:ℂ))‖ ^ 2)
        ≤ ∫ z, (k:ℝ)^2 * (φ z)^2 * (‖u' z‖^2)^(k-1) * Λ^2 := by
      refine integral_mono hGYint hYu'int (fun z => le_trans (hYbd z) (le_of_eq ?_))
      by_cases hz : φ z = 0
      · rw [hz]; ring
      · rw [hu'eq z (subset_closure (Function.mem_support.mpr hz))]
    have h2 : (∫ z, (k:ℝ)^2 * (φ z)^2 * (‖u' z‖^2)^(k-1) * Λ^2)
        = (k:ℝ)^2 * ∫ z, (φ z)^2 * (‖u' z‖^2)^(k-1) * Λ^2 := by
      rw [← integral_const_mul]
      exact integral_congr_ae (Filter.Eventually.of_forall (fun z => by ring))
    refine (h1.trans (le_of_eq h2)).trans (le_of_eq ?_)
    congr 1
    exact integral_eq_setIntegral_of_eq_on (Work.CR.Flat.isOpen_polydisc 0 ρ).measurableSet
      (fun z hz => by
        have h0 : φ z = 0 := by
          by_contra h
          exact hz (hφsupp (subset_closure (Function.mem_support.mpr h)))
        rw [h0]; ring)
      (fun z hz => by
        by_cases hz0 : φ z = 0
        · rw [hz0]; ring
        · rw [hu'eq z (subset_closure (Function.mem_support.mpr hz0))])
  have hMle : ∫ z, ‖H z‖ ^ 2 * (∑ j : Fin n, (‖Work.CR.Flat.dCoord j η z‖ ^ 2
        + ‖Work.CR.Flat.dbarCoord j η z‖ ^ 2))
      ≤ 2 * (n:ℝ) * ∫ z in Work.CR.Flat.polydisc 0 ρ,
          ‖fderiv ℝ φ z‖ ^ 2 * (‖u z‖ ^ 2) ^ k := by
    have h1 : ∫ z, ‖H z‖ ^ 2 * (∑ j : Fin n, (‖Work.CR.Flat.dCoord j η z‖ ^ 2
          + ‖Work.CR.Flat.dbarCoord j η z‖ ^ 2))
        ≤ ∫ z, 2 * (n:ℝ) * ‖fderiv ℝ φ z‖ ^ 2 * (‖u' z‖ ^ 2) ^ k :=
      integral_mono hGMint hMu'int hMbd
    have h2 : (∫ z, 2 * (n:ℝ) * ‖fderiv ℝ φ z‖ ^ 2 * (‖u' z‖ ^ 2) ^ k)
        = 2 * (n:ℝ) * ∫ z, ‖fderiv ℝ φ z‖ ^ 2 * (‖u' z‖ ^ 2) ^ k := by
      rw [← integral_const_mul]
      exact integral_congr_ae (Filter.Eventually.of_forall (fun z => by ring))
    refine (h1.trans (le_of_eq h2)).trans (le_of_eq ?_)
    congr 1
    exact integral_eq_setIntegral_of_eq_on (Work.CR.Flat.isOpen_polydisc 0 ρ).measurableSet
      (fun z hz => by
        have hf0 : fderiv ℝ φ z = 0 := fderiv_of_notMem_tsupport ℝ (by
          intro hmem; exact hz (hφsupp hmem))
        rw [hf0, norm_zero]; ring)
      (fun z hz => by
        by_cases hf : fderiv ℝ φ z = 0
        · rw [hf, norm_zero]; ring
        · rw [hu'eq z (by
            by_contra hc; exact hf (fderiv_of_notMem_tsupport ℝ hc))])
  -- ===== the left hand side as a space integral =====
  have hTL : (∫ z in Work.CR.Flat.polydisc 0 ρ,
        (k : ℝ)^2 * (φ z)^2 * (‖u z‖^2)^(k-1) *
          (∑ j : Fin n, (‖Work.CR.Flat.dCoord j u z‖^2
            + ‖Work.CR.Flat.dbarCoord j u z‖^2)))
      = ∫ z, ‖η z‖ ^ 2 * (∑ j : Fin n, (‖Work.CR.Flat.dCoord j H z‖ ^ 2
          + ‖Work.CR.Flat.dbarCoord j H z‖ ^ 2)) := by
    have hz0 : ∀ z ∉ Work.CR.Flat.polydisc 0 ρ,
        (k : ℝ)^2 * (φ z)^2 * (‖u z‖^2)^(k-1) *
          (∑ j : Fin n, (‖Work.CR.Flat.dCoord j u z‖^2
            + ‖Work.CR.Flat.dbarCoord j u z‖^2)) = 0 := by
      intro z hz
      have h : φ z = 0 := by
        by_contra hc
        exact hz (hφsupp (subset_closure (Function.mem_support.mpr hc)))
      rw [h]; ring
    rw [setIntegral_eq_integral_of_eq_zero_off (Work.CR.Flat.isOpen_polydisc 0 ρ).measurableSet hz0]
    exact integral_congr_ae (Filter.Eventually.of_forall (fun z => (hGT z).symm))
  rw [hTL]
  set R1 : ℝ := ∫ z in Work.CR.Flat.polydisc 0 ρ, ‖fderiv ℝ φ z‖ ^ 2 * (‖u z‖ ^ 2) ^ k
    with hR1def
  set R2 : ℝ := ∫ z in Work.CR.Flat.polydisc 0 ρ, (φ z) ^ 2 * (‖u z‖ ^ 2) ^ (k-1) * Λ ^ 2
    with hR2def
  have hR1nn : 0 ≤ R1 := integral_nonneg (fun z => by positivity)
  have hR2nn : 0 ≤ R2 := integral_nonneg (fun z => by positivity)
  calc ∫ z, ‖η z‖ ^ 2 * (∑ j : Fin n, (‖Work.CR.Flat.dCoord j H z‖ ^ 2
        + ‖Work.CR.Flat.dbarCoord j H z‖ ^ 2))
      ≤ 20 * (∫ z, ‖η z‖ ^ 2 * (∑ j : Fin n,
            ‖dbarCn (JstdCn n + A') H z (Pi.single j (1:ℂ))‖ ^ 2))
        + 8 * (∫ z, ‖H z‖ ^ 2 * (∑ j : Fin n, (‖Work.CR.Flat.dCoord j η z‖ ^ 2
            + ‖Work.CR.Flat.dbarCoord j η z‖ ^ 2))) := hI
    _ ≤ 20 * ((k:ℝ)^2 * R2) + 16 * (n:ℝ) * R1 := by
        have h1 : 20 * (∫ z, ‖η z‖ ^ 2 * (∑ j : Fin n,
              ‖dbarCn (JstdCn n + A') H z (Pi.single j (1:ℂ))‖ ^ 2)) ≤ 20 * ((k:ℝ)^2 * R2) := by
          linarith [hYle]
        have h2 : 8 * (∫ z, ‖H z‖ ^ 2 * (∑ j : Fin n, (‖Work.CR.Flat.dCoord j η z‖ ^ 2
              + ‖Work.CR.Flat.dbarCoord j η z‖ ^ 2))) ≤ 16 * (n:ℝ) * R1 := by
          linarith [hMle]
        linarith [h1, h2]
    _ ≤ A * ((k:ℝ)^2 * R2) + A * R1 := by
        have h1 : 20 * ((k:ℝ)^2 * R2) ≤ A * ((k:ℝ)^2 * R2) :=
          mul_le_mul_of_nonneg_right hAle20 (by positivity)
        have h2 : 16 * (n:ℝ) * R1 ≤ A * R1 := mul_le_mul_of_nonneg_right hAle16n hR1nn
        linarith [h1, h2]
    _ = A * (R1 + (k:ℝ)^2 * R2) := by ring



end

end Work.NN.Final.LevJLoc
