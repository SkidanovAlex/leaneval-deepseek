import Mathlib
import Submission.Work.KMTAreas.A7.SmallModApproxSum
import Submission.Work.KMTAreas.A7.KmtProjCrude
import Submission.Work.KMTAreas.A7.SmallModMassFinal
import Submission.Work.KMTAreas.A7.SmallModMassFinal

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace Work.KMTAreas.A7

noncomputable section

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal BigOperators
open PointwiseErgodicTheorems Submission.PointwiseErgodicTheorems
open Work.KMTContract Work.Analysis.EndVar Work.Analysis.IWMultiplier Work.Analysis.IonescuWainger

/-- **The summation step, in the form adapted to the unsharp per-scale weight.** -/
theorem SmallModApprox_of_singleB (P : ℤ[X]) (p₁ p₂ : ENNReal) (hdeg : 2 ≤ P.natDegree)
    (hA1 : Work.KMTContract.AreaA1) (hp₁ : 1 < p₁) (htp₁ : p₁ < ⊤) (hp₂ : 1 < p₂)
    (htp₂ : p₂ < ⊤) (hsum : p₁⁻¹ + p₂⁻¹ ≤ 1)
    (hsingle : SmallSingleScaleB P p₁ p₂) :
    ∀ (C₀ : ℕ) (r : NNReal), 1 ≤ C₀ → (2 : NNReal) < r →
      ∃ c : ℝ, 0 ≤ c ∧ ∃ ρ₀ : ℝ, 0 < ρ₀ ∧
        ∀ ρ : ℝ, 0 < ρ → ρ ≤ ρ₀ → ∃ K : NNReal → NNReal,
          ∀ (a : ℕ → ℝ≥0) (Λ : ℝ≥0) (l₁ l₂ k₁ k₂ : ℕ) (f g : ℤ → ℂ),
            1 < Λ → PointwiseErgodicTheorems.Lacunary Λ a → (∀ n, 1 ≤ a n) →
            MeasureTheory.eLpNorm (fun x : ℤ =>
                PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ =>
                  smallMainPart ρ P C₀ a f g l₁ l₂ k₁ k₂ n x
                    - smallModelTuple ρ P C₀ a f g l₁ l₂ k₁ k₂ n x))
              (p₁⁻¹ + p₂⁻¹)⁻¹ MeasureTheory.Measure.count
            ≤ (K Λ : ENNReal) *
                ENNReal.ofReal (lossWeight c ρ l₁ l₂ k₁ k₂) *
                MeasureTheory.eLpNorm f p₁ MeasureTheory.Measure.count *
                MeasureTheory.eLpNorm g p₂ MeasureTheory.Measure.count := by
  classical
  intro C₀ r hC₀ hr
  obtain ⟨ρc, hρc, hS⟩ := hsingle C₀ r hC₀ hr
  have hD := invFloorSum_le C₀ hC₀
  have hr1 : (1 : NNReal) ≤ r := le_of_lt (lt_trans (by norm_num) hr)
  have hq : (1 : ENNReal) ≤ (p₁⁻¹ + p₂⁻¹)⁻¹ := ENNReal.one_le_inv.mpr hsum
  set Dfun : ℝ≥0 → ℝ := fun Λ =>
    if h : 1 < Λ then Classical.choose (hD Λ h) else 0 with hDfun
  have hDfun0 : ∀ Λ : ℝ≥0, 0 ≤ Dfun Λ := by
    intro Λ
    by_cases h : 1 < Λ
    · rw [hDfun]; simp only [dif_pos h]
      exact (Classical.choose_spec (hD Λ h)).1
    · rw [hDfun]; simp [h]
  have hDfunb : ∀ Λ : ℝ≥0, 1 < Λ → ∀ (L : ℕ), 1 ≤ L → ∀ (a : ℕ → ℝ≥0),
      PointwiseErgodicTheorems.Lacunary Λ a → (∀ n, 1 ≤ a n) →
      (∑' n : ℕ, (if L ≤ heightScale C₀ (Nat.floor (a n))
        then (((Nat.floor (a n) : ℕ)) : ℝ)⁻¹ else 0))
        ≤ Dfun Λ * (2 : ℝ) ^ (-((2 : ℝ) ^ ((L : ℝ) / (C₀ : ℝ))) + 2) := by
    intro Λ hΛ L hL a ha ha1
    rw [hDfun]; simp only [dif_pos hΛ]
    exact (Classical.choose_spec (hD Λ hΛ)).2 L hL a ha ha1
  set Efun : ℝ≥0 → ℝ := fun Λ => max (2 * (Λ : ℝ) / ((Λ : ℝ) - 1)) (Dfun Λ) with hEfun
  have hEfun0 : ∀ Λ : ℝ≥0, 0 ≤ Efun Λ := by
    intro Λ
    rw [hEfun]
    exact le_trans (hDfun0 Λ) (le_max_right _ _)
  refine ⟨0, le_refl 0, min ρc (1 / (4 * (C₀ : ℝ))), lt_min hρc (by positivity), ?_⟩
  intro ρ hρ hρle
  have hρc' : ρ ≤ ρc := le_trans hρle (min_le_left _ _)
  have hρ4 : ρ ≤ 1 / (4 * (C₀ : ℝ)) := le_trans hρle (min_le_right _ _)
  obtain ⟨C, hC, K, hK⟩ := hS ρ hρ hρc'
  obtain ⟨Kabs, hKabs1, hKabs⟩ := SmallWeightArith C hC C₀ hC₀ ρ hρ.le hρ4
  have hKabsnn : (0 : ℝ) ≤ Kabs := le_trans zero_le_one hKabs1
  have hKc0 : ∀ Λ : ℝ≥0, (0 : ℝ) ≤ 4 * (K Λ : ℝ) * Efun Λ * Kabs + 16 := by
    intro Λ
    have h1 : (0 : ℝ) ≤ (K Λ : ℝ) := by positivity
    have h2 : (0 : ℝ) ≤ Efun Λ := hEfun0 Λ
    have h3 : (0 : ℝ) ≤ 4 * (K Λ : ℝ) * Efun Λ * Kabs :=
      mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) h1) h2) (le_trans zero_le_one hKabs1)
    linarith
  let Kfun : ℝ≥0 → ℝ≥0 := fun Λ => ⟨4 * (K Λ : ℝ) * Efun Λ * Kabs + 16, hKc0 Λ⟩
  have hKfun_coe : ∀ ν : ℝ≥0, (Kfun ν : ENNReal)
      = ENNReal.ofReal (4 * (K ν : ℝ) * Efun ν * Kabs + 16) := fun ν =>
    (ENNReal.ofReal_coe_nnreal (p := Kfun ν)).symm
  refine ⟨Kfun, ?_⟩
  intro a Λ l₁ l₂ k₁ k₂ f g hΛ ha ha1
  set u : ℕ → ℤ → ℂ := fun n x =>
    smallMainPart ρ P C₀ a f g l₁ l₂ k₁ k₂ n x
      - smallModelTuple ρ P C₀ a f g l₁ l₂ k₁ k₂ n x with hu
  set Gc : ℕ → Prop := fun n => smallCond ρ C₀ a l₁ l₂ k₁ k₂ n with hGc
  set W : ℝ := smallScaleWeight C ρ l₁ l₂ k₁ k₂ with hW
  set Lr : ℝ := lmaxR l₁ l₂ k₁ k₂ with hLr
  set sig : ℝ := (2 : ℝ) ^ (-((2 : ℝ) ^ (Lr / (C₀ : ℝ))) + 2) with hsig
  have hLrcast : ((smallL l₁ l₂ k₁ k₂ : ℕ) : ℝ) = Lr := by
    rw [hLr, lmaxR, Work.Analysis.EndVar.lmax, smallL]
    push_cast
    rfl
  have hzero : ∀ n : ℕ, ¬ Gc n → u n = 0 := by
    intro n hn
    rw [hu]
    exact smallDiff_eq_zero_of_not_cond ρ P C₀ a f g l₁ l₂ k₁ k₂ n hn
  have hper : ∀ n : ℕ, MeasureTheory.eLpNorm (fun x : ℤ => u n x)
      ((p₁⁻¹ + p₂⁻¹)⁻¹) MeasureTheory.Measure.count
      ≤ if Gc n then (K Λ : ENNReal) * ENNReal.ofReal W *
          ENNReal.ofReal ((((Nat.floor (a n) : ℕ)) : ℝ)⁻¹) *
          MeasureTheory.eLpNorm f p₁ MeasureTheory.Measure.count *
          MeasureTheory.eLpNorm g p₂ MeasureTheory.Measure.count else 0 := by
    intro n
    by_cases hg : Gc n
    · rw [if_pos hg, hu]
      have h := hK a Λ l₁ l₂ k₁ k₂ f g hΛ ha ha1 n
      rw [hW]
      exact h
    · rw [if_neg hg, hzero n hg]
      simp
  have hcond : ∀ n : ℕ, Gc n → smallL l₁ l₂ k₁ k₂ ≤ heightScale C₀ (Nat.floor (a n)) := by
    intro n hg
    have h1 : inIndexSet C₀ (max (l₁ : ℤ) (l₂ : ℤ)) (k₁ : ℤ) (k₂ : ℤ) (Nat.floor (a n)) := hg.1
    rw [inIndexSet] at h1
    have h2 : max (l₁ : ℤ) (l₂ : ℤ) ≤ ((heightScale C₀ (Nat.floor (a n)) : ℕ) : ℤ) := h1.1
    have h3 : (k₁ : ℤ) ≤ ((heightScale C₀ (Nat.floor (a n)) : ℕ) : ℤ) := h1.2.1
    have h4 : (k₂ : ℤ) ≤ ((heightScale C₀ (Nat.floor (a n)) : ℕ) : ℤ) := h1.2.2
    rw [smallL]
    omega
  have hsum2 : (∑' n : ℕ, (if Gc n then
        ENNReal.ofReal ((((Nat.floor (a n) : ℕ)) : ℝ)⁻¹) else 0))
      ≤ ENNReal.ofReal (Efun Λ * sig) := by
    have hthis := tsum_ite_floor_le_indexSet C₀ hC₀ Λ hΛ (Dfun Λ) (hDfun0 Λ)
      (fun L hL a ha ha1 => hDfunb Λ hΛ L hL a ha ha1) (smallL l₁ l₂ k₁ k₂) (Efun Λ)
      (le_of_eq rfl) a ha ha1 Gc hcond
    rw [hLrcast] at hthis
    rw [hsig]
    exact hthis
  have hWsig : W * sig ≤ Kabs := by
    have h := hKabs (smallL l₁ l₂ k₁ k₂)
    rw [hLrcast] at h
    rw [hW, hsig, smallScaleWeight, hLr]
    exact h
  have hW0 : 0 ≤ W := by rw [hW]; exact smallScaleWeight_nonneg C ρ l₁ l₂ k₁ k₂
  have hE0 : 0 ≤ Efun Λ := hEfun0 Λ
  have hK0 : (0 : ℝ) ≤ (K Λ : ℝ) := by positivity
  have hsig0 : 0 ≤ sig := by
    rw [hsig]; positivity
  have hKE : (0 : ℝ) ≤ 4 * (K Λ : ℝ) * Efun Λ :=
    mul_nonneg (mul_nonneg (by norm_num) hK0) hE0
  have hKabsnn : (0 : ℝ) ≤ Kabs := le_trans zero_le_one hKabs1
  have hreal : 4 * (K Λ : ℝ) * W * (Efun Λ * sig)
      ≤ (4 * (K Λ : ℝ) * Efun Λ * Kabs + 16) * lossWeight 0 ρ l₁ l₂ k₁ k₂ := by
    have hWsig' : 4 * (K Λ : ℝ) * Efun Λ * (W * sig) ≤ 4 * (K Λ : ℝ) * Efun Λ * Kabs :=
      mul_le_mul_of_nonneg_left hWsig hKE
    have hLw : lossWeight (0 : ℝ) ρ l₁ l₂ k₁ k₂ = 1 := by
      rw [lossWeight]; simp
    calc 4 * (K Λ : ℝ) * W * (Efun Λ * sig)
        = 4 * (K Λ : ℝ) * Efun Λ * (W * sig) := by ring
      _ ≤ 4 * (K Λ : ℝ) * Efun Λ * Kabs := hWsig'
      _ ≤ (4 * (K Λ : ℝ) * Efun Λ * Kabs + 16) * lossWeight 0 ρ l₁ l₂ k₁ k₂ := by
          rw [hLw]; nlinarith [mul_nonneg hKE hKabsnn]
  have hmul : 4 * (K Λ : ENNReal) * ENNReal.ofReal W * ENNReal.ofReal (Efun Λ * sig)
      ≤ (Kfun Λ : ENNReal) * ENNReal.ofReal (lossWeight 0 ρ l₁ l₂ k₁ k₂) := by
    rw [hKfun_coe Λ]
    have hKcoe : (4 : ENNReal) * (K Λ : ENNReal) = ENNReal.ofReal (4 * (K Λ : ℝ)) := by
      rw [← ENNReal.ofReal_ofNat, ← ENNReal.ofReal_coe_nnreal,
        ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4)]
    have hmerge : ENNReal.ofReal (4 * (K Λ : ℝ)) * ENNReal.ofReal W *
          ENNReal.ofReal (Efun Λ * sig)
        = ENNReal.ofReal (4 * (K Λ : ℝ) * W * (Efun Λ * sig)) := by
      rw [← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 4 * (K Λ : ℝ)),
        ← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 4 * (K Λ : ℝ) * W)]
    calc 4 * (K Λ : ENNReal) * ENNReal.ofReal W * ENNReal.ofReal (Efun Λ * sig)
        = ENNReal.ofReal (4 * (K Λ : ℝ) * W * (Efun Λ * sig)) := by rw [hKcoe, hmerge]
      _ ≤ ENNReal.ofReal ((4 * (K Λ : ℝ) * Efun Λ * Kabs + 16) *
            lossWeight 0 ρ l₁ l₂ k₁ k₂) := ENNReal.ofReal_le_ofReal hreal
      _ = ENNReal.ofReal (4 * (K Λ : ℝ) * Efun Λ * Kabs + 16)
            * ENNReal.ofReal (lossWeight 0 ρ l₁ l₂ k₁ k₂) := by
          rw [ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 4 * (K Λ : ℝ) * Efun Λ * Kabs + 16)]
  have hVar := VarNormTsumLp (r := r) hr1 (p := (p₁⁻¹ + p₂⁻¹)⁻¹) hq u
  refine hVar.trans ?_
  have hstep1 : (∑' n : ℕ, 4 * MeasureTheory.eLpNorm (fun x : ℤ => u n x)
        ((p₁⁻¹ + p₂⁻¹)⁻¹) MeasureTheory.Measure.count)
      ≤ ∑' n : ℕ, 4 * (if Gc n then (K Λ : ENNReal) * ENNReal.ofReal W *
          ENNReal.ofReal ((((Nat.floor (a n) : ℕ)) : ℝ)⁻¹) *
          MeasureTheory.eLpNorm f p₁ MeasureTheory.Measure.count *
          MeasureTheory.eLpNorm g p₂ MeasureTheory.Measure.count else 0) :=
    ENNReal.tsum_le_tsum (fun n => mul_le_mul' le_rfl (hper n))
  refine hstep1.trans ?_
  have hstep2 : (∑' n : ℕ, 4 * (if Gc n then (K Λ : ENNReal) * ENNReal.ofReal W *
        ENNReal.ofReal ((((Nat.floor (a n) : ℕ)) : ℝ)⁻¹) *
        MeasureTheory.eLpNorm f p₁ MeasureTheory.Measure.count *
        MeasureTheory.eLpNorm g p₂ MeasureTheory.Measure.count else 0))
      = (4 * (K Λ : ENNReal) * ENNReal.ofReal W *
          MeasureTheory.eLpNorm f p₁ MeasureTheory.Measure.count *
          MeasureTheory.eLpNorm g p₂ MeasureTheory.Measure.count) *
        (∑' n : ℕ, (if Gc n then
          ENNReal.ofReal ((((Nat.floor (a n) : ℕ)) : ℝ)⁻¹) else 0)) := by
    rw [← ENNReal.tsum_mul_left]
    refine tsum_congr (fun n => ?_)
    by_cases hg : Gc n
    · rw [if_pos hg, if_pos hg]; ring
    · rw [if_neg hg, if_neg hg]; simp
  rw [hstep2]
  calc (4 * (K Λ : ENNReal) * ENNReal.ofReal W *
          MeasureTheory.eLpNorm f p₁ MeasureTheory.Measure.count *
          MeasureTheory.eLpNorm g p₂ MeasureTheory.Measure.count) *
        (∑' n : ℕ, (if Gc n then
          ENNReal.ofReal ((((Nat.floor (a n) : ℕ)) : ℝ)⁻¹) else 0))
      ≤ (4 * (K Λ : ENNReal) * ENNReal.ofReal W *
          MeasureTheory.eLpNorm f p₁ MeasureTheory.Measure.count *
          MeasureTheory.eLpNorm g p₂ MeasureTheory.Measure.count) *
            ENNReal.ofReal (Efun Λ * sig) := mul_le_mul' le_rfl hsum2
    _ = (4 * (K Λ : ENNReal) * ENNReal.ofReal W * ENNReal.ofReal (Efun Λ * sig)) *
          (MeasureTheory.eLpNorm f p₁ MeasureTheory.Measure.count *
          MeasureTheory.eLpNorm g p₂ MeasureTheory.Measure.count) := by ring
    _ ≤ ((Kfun Λ : ENNReal) * ENNReal.ofReal (lossWeight 0 ρ l₁ l₂ k₁ k₂)) *
          (MeasureTheory.eLpNorm f p₁ MeasureTheory.Measure.count *
          MeasureTheory.eLpNorm g p₂ MeasureTheory.Measure.count) :=
        mul_le_mul' hmul le_rfl
    _ = (Kfun Λ : ENNReal) * ENNReal.ofReal (lossWeight 0 ρ l₁ l₂ k₁ k₂) *
          MeasureTheory.eLpNorm f p₁ MeasureTheory.Measure.count *
          MeasureTheory.eLpNorm g p₂ MeasureTheory.Measure.count := by ring


/-- **The single-scale model approximation of §6 in its unsharp (summable) form.** -/
theorem SmallSingleScaleB_holds (P : ℤ[X]) (p₁ p₂ : ENNReal) (hdeg : 2 ≤ P.natDegree)
    (hA1 : Work.KMTContract.AreaA1) (hp₁ : 1 < p₁) (htp₁ : p₁ < ⊤) (hp₂ : 1 < p₂)
    (htp₂ : p₂ < ⊤) (hsum : p₁⁻¹ + p₂⁻¹ ≤ 1) : SmallSingleScaleB P p₁ p₂ := by
  intro C₀ r hC₀ hr
  obtain ⟨ρB, hρBz, hB⟩ := Work.KMTAreas.A7z.smallKernelMass_le P hdeg hA1 C₀
  refine ⟨min ρB 1, lt_min hρBz one_pos, ?_⟩
  intro ρ hρ hρle
  have hρB : ρ ≤ ρB := le_trans hρle (min_le_left _ _)
  have hρ1 : ρ ≤ 1 := le_trans hρle (min_le_right _ _)
  obtain ⟨C, hC, K₀, hK₀⟩ := hB ρ hρ hρB
  let Kfun : NNReal → NNReal := fun Λ => max (K₀ Λ) 1
  have hKge : ∀ Λ : NNReal, (K₀ Λ : ENNReal) ≤ (Kfun Λ : ENNReal) :=
    fun Λ => ENNReal.coe_le_coe.mpr (le_max_left (K₀ Λ) 1)
  have hK1 : ∀ Λ : NNReal, (1 : ENNReal) ≤ (Kfun Λ : ENNReal) := fun Λ =>
    ENNReal.coe_le_coe.mpr (le_max_right (K₀ Λ) 1)
  refine ⟨C, hC, Kfun, ?_⟩
  intro a Λ l₁ l₂ k₁ k₂ f g hΛ ha ha1 n
  have hp1ne : p₁ ≠ 0 := ne_of_gt (lt_trans zero_lt_one hp₁)
  have hp2ne : p₂ ≠ 0 := ne_of_gt (lt_trans zero_lt_one hp₂)
  have hWpos : (0 : ℝ) < smallScaleWeight C ρ l₁ l₂ k₁ k₂ := by
    rw [smallScaleWeight]; positivity
  have hKpos : (0 : ENNReal) < (Kfun Λ : ENNReal) := lt_of_lt_of_le zero_lt_one (hK1 Λ)
  have hWposE : (0 : ENNReal) < ENNReal.ofReal (smallScaleWeight C ρ l₁ l₂ k₁ k₂) :=
    ENNReal.ofReal_pos.mpr hWpos
  have hflpos : (0 : ℝ) < ((Nat.floor (a n) : ℕ) : ℝ) := by
    have h1 : (1 : NNReal) ≤ a n := ha1 n
    have h2 : (1 : ℕ) ≤ Nat.floor (a n) := Nat.le_floor (by exact_mod_cast h1)
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one h2)
  have hFposE : (0 : ENNReal) < ENNReal.ofReal ((((Nat.floor (a n) : ℕ)) : ℝ)⁻¹) :=
    ENNReal.ofReal_pos.mpr (by positivity)
  have hRpos : (0 : ENNReal) < (Kfun Λ : ENNReal)
      * ENNReal.ofReal (smallScaleWeight C ρ l₁ l₂ k₁ k₂)
      * ENNReal.ofReal ((((Nat.floor (a n) : ℕ)) : ℝ)⁻¹) :=
    ENNReal.mul_pos (ne_of_gt (ENNReal.mul_pos (ne_of_gt hKpos) (ne_of_gt hWposE)))
      (ne_of_gt hFposE)
  have hRne : ((Kfun Λ : ENNReal) * ENNReal.ofReal (smallScaleWeight C ρ l₁ l₂ k₁ k₂)
      * ENNReal.ofReal ((((Nat.floor (a n) : ℕ)) : ℝ)⁻¹)) ≠ 0 := ne_of_gt hRpos
  have hRfin : ((Kfun Λ : ENNReal) * ENNReal.ofReal (smallScaleWeight C ρ l₁ l₂ k₁ k₂)
      * ENNReal.ofReal ((((Nat.floor (a n) : ℕ)) : ℝ)⁻¹)) ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.mul_ne_top (by simp) (by simp)) (by simp)
  by_cases hf0 : MeasureTheory.eLpNorm f p₁ Measure.count = 0
  · have hfzero : f = 0 := by
      have hae : f =ᵐ[Measure.count] 0 :=
        (MeasureTheory.eLpNorm_eq_zero_iff
          hp1ne).mp hf0
      funext x
      by_contra hx
      have hnull : Measure.count {y : ℤ | ¬ (f y = 0)} = 0 := MeasureTheory.ae_iff.mp hae
      have hsub : ({x} : Set ℤ) ⊆ {y : ℤ | ¬ (f y = 0)} := by
        intro y hy
        rw [Set.mem_singleton_iff] at hy
        rw [hy]; exact hx
      have hle : Measure.count ({x} : Set ℤ) ≤ Measure.count {y : ℤ | ¬ (f y = 0)} :=
        MeasureTheory.measure_mono hsub
      rw [hnull] at hle
      simp only [Measure.count_singleton, le_zero_iff, one_ne_zero] at hle
    rw [hfzero]
    have hzero : (fun x : ℤ => smallMainPart ρ P C₀ a 0 g l₁ l₂ k₁ k₂ n x
        - smallModelTuple ρ P C₀ a 0 g l₁ l₂ k₁ k₂ n x) = 0 := by
      funext x
      simp [smallMainPart_zero_left, smallModelTuple_zero_left]
    rw [hzero, eLpNorm_zero]
    exact bot_le
  · by_cases hg0 : MeasureTheory.eLpNorm g p₂ Measure.count = 0
    · have hgzero : g = 0 := by
        have hae : g =ᵐ[Measure.count] 0 :=
          (MeasureTheory.eLpNorm_eq_zero_iff
            hp2ne).mp hg0
        funext x
        by_contra hx
        have hnull : Measure.count {y : ℤ | ¬ (g y = 0)} = 0 := MeasureTheory.ae_iff.mp hae
        have hsub : ({x} : Set ℤ) ⊆ {y : ℤ | ¬ (g y = 0)} := by
          intro y hy
          rw [Set.mem_singleton_iff] at hy
          rw [hy]; exact hx
        have hle : Measure.count ({x} : Set ℤ) ≤ Measure.count {y : ℤ | ¬ (g y = 0)} :=
          MeasureTheory.measure_mono hsub
        rw [hnull] at hle
        simp only [Measure.count_singleton, le_zero_iff, one_ne_zero] at hle
      rw [hgzero]
      have hzero : (fun x : ℤ => smallMainPart ρ P C₀ a f 0 l₁ l₂ k₁ k₂ n x
          - smallModelTuple ρ P C₀ a f 0 l₁ l₂ k₁ k₂ n x) = 0 := by
        funext x
        simp [smallMainPart_zero_right, smallModelTuple_zero_right]
      rw [hzero, eLpNorm_zero]
      exact bot_le
    · by_cases hft : MeasureTheory.eLpNorm f p₁ Measure.count = ⊤
      · rw [hft]
        refine le_top.trans (le_of_eq ?_)
        rw [ENNReal.mul_top hRne, ENNReal.top_mul hg0]
      · by_cases hgt : MeasureTheory.eLpNorm g p₂ Measure.count = ⊤
        · rw [hgt]
          refine le_top.trans (le_of_eq ?_)
          rw [ENNReal.mul_top (mul_ne_zero hRne hf0)]
        · have hMf : MemLp f p₁ Measure.count :=
            (MeasureTheory.memLp_iff.mpr (lt_top_iff_ne_top.mpr hft))
          have hMg : MemLp g p₂ Measure.count :=
            (MeasureTheory.memLp_iff.mpr (lt_top_iff_ne_top.mpr hgt))
          have hbf : Work.KMTAreas.A5.BoundedZ f := Work.KMTAreas.A5.boundedZ_of_memLp hp₁ hMf
          have hbg : Work.KMTAreas.A5.BoundedZ g := Work.KMTAreas.A5.boundedZ_of_memLp hp₂ hMg
          by_cases hcond : smallCond ρ C₀ a l₁ l₂ k₁ k₂ n
          · have hA := smallModReduction ρ P C₀ a f g l₁ l₂ k₁ k₂ n hρ hρ1 hbf hbg hcond
            rw [hA]
            set Kd : ℤ → ℤ → ℂ := fun x y => smallKconc ρ P l₁ l₂ k₁ k₂ (Nat.floor (a n)) x y
              - smallKmod ρ P l₁ l₂ k₁ k₂ (Nat.floor (a n)) x y with hKd
            have hmass : smKernMass Kd ≤ (Kfun Λ : ENNReal)
                * ENNReal.ofReal (smallScaleWeight C ρ l₁ l₂ k₁ k₂)
                * ENNReal.ofReal ((((Nat.floor (a n) : ℕ)) : ℝ)⁻¹) :=
              (hK₀ a Λ l₁ l₂ k₁ k₂ n hΛ ha ha1 hcond).trans
                (mul_le_mul' (mul_le_mul' (hKge Λ) le_rfl) le_rfl)
            have hfin : Summable fun q : ℤ × ℤ => ‖Kd q.1 q.2‖ := by
              have hne : smKernMass Kd ≠ ⊤ := ne_top_of_le_ne_top hRfin hmass
              have h1 : Summable fun q : ℤ × ℤ => ‖Kd q.1 q.2‖₊ := by
                refine ENNReal.tsum_coe_ne_top_iff_summable.mp ?_
                simpa only [enorm_eq_nnnorm, smKernMass] using hne
              have h2 : Summable fun q : ℤ × ℤ => ((‖Kd q.1 q.2‖₊ : NNReal) : ℝ) :=
                NNReal.summable_coe.mpr h1
              simpa only [coe_nnnorm] using h2
            have hp : p₁⁻¹ + p₂⁻¹ = ((p₁⁻¹ + p₂⁻¹)⁻¹)⁻¹ := by rw [inv_inv]
            have hple : (1 : ENNReal) ≤ (p₁⁻¹ + p₂⁻¹)⁻¹ := ENNReal.one_le_inv.mpr hsum
            have hbil := BilinOpLp (K := Kd) (p := (p₁⁻¹ + p₂⁻¹)⁻¹) hp hple hfin f g
            refine hbil.trans ?_
            have hsm : smKernMass Kd = ENNReal.ofReal (tsum (fun q : ℤ × ℤ => ‖Kd q.1 q.2‖)) := by
              have hL : smKernMass Kd = tsum (fun q : ℤ × ℤ => ‖Kd q.1 q.2‖ₑ) := rfl
              have hR : ENNReal.ofReal (tsum (fun q : ℤ × ℤ => ‖Kd q.1 q.2‖))
                  = tsum (fun q : ℤ × ℤ => ENNReal.ofReal ‖Kd q.1 q.2‖) :=
                ENNReal.ofReal_tsum_of_nonneg (fun q => norm_nonneg _) hfin
              rw [hL, hR]
              refine tsum_congr (fun q => ?_)
              rw [enorm_eq_nnnorm]
              exact (ENNReal.ofReal_coe_nnreal (p := ‖Kd q.1 q.2‖₊)).symm
            rw [← hsm]
            exact mul_le_mul' (mul_le_mul' hmass le_rfl) le_rfl
          · rw [smallDiff_eq_zero_of_not_cond ρ P C₀ a f g l₁ l₂ k₁ k₂ n hcond, eLpNorm_zero]
            exact bot_le

/-- The small-scale model approximation: hypothesis `h1` of `Work.KMTAreas.A7.SmallLossOfBounds`.
The model operator behind `smallModelTuple` is built from the *exact-height* multipliers
(`Tm`) and the exact-height arithmetic kernel `smallArithKernel`, as the paper's §5-§6 and the
contract's pieces `Fpiece`/`Gpiece` require, so the statement is the paper's §6 Proposition
`mod-approx` composed with the functional calculus `bn-ident`.

The single-scale estimate `SmallSingleScaleB_holds` supplies the per-scale input, and the
summation over the lacunary scales (`VarNormTsumLp`, `invFloorSum_le`, `SmallWeightArith`)
converts it into the variational statement below. -/
theorem SmallModApprox (P : ℤ[X]) (p₁ p₂ : ENNReal) (hdeg : 2 ≤ P.natDegree)
    (hA1 : Work.KMTContract.AreaA1) (hp₁ : 1 < p₁) (htp₁ : p₁ < ⊤) (hp₂ : 1 < p₂)
    (htp₂ : p₂ < ⊤) (hsum : p₁⁻¹ + p₂⁻¹ ≤ 1) :
    ∀ (C₀ : ℕ) (r : NNReal), 1 ≤ C₀ → (2 : NNReal) < r →
      ∃ c : ℝ, 0 ≤ c ∧ ∃ ρ₀ : ℝ, 0 < ρ₀ ∧
        ∀ ρ : ℝ, 0 < ρ → ρ ≤ ρ₀ → ∃ K : NNReal → NNReal,
          ∀ (a : ℕ → ℝ≥0) (Λ : ℝ≥0) (l₁ l₂ k₁ k₂ : ℕ) (f g : ℤ → ℂ),
            1 < Λ → PointwiseErgodicTheorems.Lacunary Λ a → (∀ n, 1 ≤ a n) →
            MeasureTheory.eLpNorm (fun x : ℤ =>
                PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ =>
                  smallMainPart ρ P C₀ a f g l₁ l₂ k₁ k₂ n x
                    - smallModelTuple ρ P C₀ a f g l₁ l₂ k₁ k₂ n x))
              (p₁⁻¹ + p₂⁻¹)⁻¹ MeasureTheory.Measure.count
            ≤ (K Λ : ENNReal) *
                ENNReal.ofReal (lossWeight c ρ l₁ l₂ k₁ k₂) *
                MeasureTheory.eLpNorm f p₁ MeasureTheory.Measure.count *
                MeasureTheory.eLpNorm g p₂ MeasureTheory.Measure.count :=
  SmallModApprox_of_singleB P p₁ p₂ hdeg hA1 hp₁ htp₁ hp₂ htp₂ hsum
    (SmallSingleScaleB_holds P p₁ p₂ hdeg hA1 hp₁ htp₁ hp₂ htp₂ hsum)


end

end Work.KMTAreas.A7
