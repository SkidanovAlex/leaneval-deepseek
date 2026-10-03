import Mathlib
import Submission.Work.KMTAreas.A7.LoMixedModel
import Submission.Work.KMTAreas.A7.LpMixedModelSymbol
import Submission.Work.KMTAreas.A7.LpNonAliasAtWindow
import Submission.Work.KMTAreas.A7.LpSymDMass
import Submission.Work.KMTAreas.A7.LpSymMWinBounds
import Submission.Work.KMTAreas.A7.LpSymMwCollapse
import Submission.Work.KMTAreas.A7.OffBandLoMixedOpHolds
import Submission.Work.KMTAreas.A7.OffBandVarpPieceLp
import Submission.Port.Aesm

namespace Work.KMTAreas.A7

noncomputable section

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal BigOperators
open PointwiseErgodicTheorems Submission.PointwiseErgodicTheorems
open Work.KMTContract Work.Analysis.EndVar Work.Analysis.IonescuWainger Work.Analysis.IWMultiplier

/-! ## The summation of the single-scale §6 error over the lacunary scales -/

/-- **The mixed-range §6 model-approximation error, summed over the lacunary scales.**  From the
single-scale estimate `LoMixedSingleScaleStatement` the variational bound follows by the `ℓ¹`-of-`Lᵖ`
spike bound `VarNormTsumLp`, the lacunary reciprocal sum `invFloorSum_le`
(`∑_{n : L ≤ l_{(⌊a n⌋)}} ⌊a n⌋⁻¹ ≲ 2^{-2^{L/C₀}}`) and the absorption `SmallWeightArith`
(`2^{C·max(2^{ρL},L)}·2^{-2^{L/C₀}+2} ≤ Kabs`), exactly as in
`Work.KMTAreas.A7.SmallModApprox_of_singleB`.  The resulting loss exponent is `c = 0`. -/
theorem loMixedBandErr_of_singleScale (P : ℤ[X]) (p₁ p₂ : ENNReal) (hdeg : 2 ≤ P.natDegree)
    (hA1 : Work.KMTContract.AreaA1) (hp₁ : 1 < p₁) (htp₁ : p₁ < ⊤) (hp₂ : 1 < p₂)
    (htp₂ : p₂ < ⊤) (hsum : p₁⁻¹ + p₂⁻¹ ≤ 1)
    (hsingle : LoMixedSingleScaleStatement P p₁ p₂) : LoMixedBandErrStatement P p₁ p₂ := by
  classical
  intro C₀ r hC₀ hr
  obtain ⟨ρc, hρc, hS⟩ := hsingle C₀ hC₀
  have hD := invFloorSum_le C₀ hC₀
  have hr1 : (1 : NNReal) ≤ r := le_of_lt (lt_trans (by norm_num) hr)
  have hq : (1 : ENNReal) ≤ (p₁⁻¹ + p₂⁻¹)⁻¹ := ENNReal.one_le_inv.mpr hsum
  set Dfun : NNReal → ℝ := fun Λ =>
    if h : 1 < Λ then Classical.choose (hD Λ h) else 0 with hDfun
  have hDfun0 : ∀ Λ : NNReal, 0 ≤ Dfun Λ := by
    intro Λ
    by_cases h : 1 < Λ
    · rw [hDfun]; simp only [dif_pos h]
      exact (Classical.choose_spec (hD Λ h)).1
    · rw [hDfun]; simp [h]
  have hDfunb : ∀ Λ : NNReal, 1 < Λ → ∀ (L : ℕ), 1 ≤ L → ∀ (a : ℕ → NNReal),
      PointwiseErgodicTheorems.Lacunary Λ a → (∀ n, 1 ≤ a n) →
      (∑' n : ℕ, (if L ≤ Work.Analysis.EndVar.heightScale C₀ (Nat.floor (a n))
        then (((Nat.floor (a n) : ℕ)) : ℝ)⁻¹ else 0))
        ≤ Dfun Λ * (2 : ℝ) ^ (-((2 : ℝ) ^ ((L : ℝ) / (C₀ : ℝ))) + 2) := by
    intro Λ hΛ L hL a ha ha1
    rw [hDfun]; simp only [dif_pos hΛ]
    exact (Classical.choose_spec (hD Λ hΛ)).2 L hL a ha ha1
  set Efun : NNReal → ℝ := fun Λ => max (2 * (Λ : ℝ) / ((Λ : ℝ) - 1)) (Dfun Λ) with hEfun
  have hEfun0 : ∀ Λ : NNReal, 0 ≤ Efun Λ := by
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
  have hKc_fun : ∀ Λ : NNReal, (0 : ℝ) ≤ 4 * (K Λ : ℝ) * Efun Λ * Kabs + 16 := by
    intro Λ
    have h1 : (0 : ℝ) ≤ (K Λ : ℝ) := by positivity
    have h3 : (0 : ℝ) ≤ 4 * (K Λ : ℝ) * Efun Λ * Kabs :=
      mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) h1) (hEfun0 Λ)) hKabsnn
    linarith
  refine ⟨fun Λ => ⟨4 * (K Λ : ℝ) * Efun Λ * Kabs + 16, hKc_fun Λ⟩, ?_⟩
  intro a Λ l₂ k₁ k₂ f g hΛ ha ha1 hl₂
  set Band : ℕ → Prop := fun n => loBandCond ρ P l₂ k₁ k₂ (Nat.floor (a n)) with hBand
  set Gc : ℕ → Prop := fun n => loGuard ρ C₀ a 0 l₂ k₁ k₂ n with hGc
  set u : ℕ → ℤ → ℂ := fun n x =>
    if Gc n ∧ Band n then
      mainPartTuple ρ P C₀ a f g 0 l₂ k₁ k₂ n x - loMixedTuple ρ P C₀ a f g l₂ k₁ k₂ n x
    else 0 with hu
  set W : ℝ := smallScaleWeight C ρ 0 l₂ k₁ k₂ with hW
  set Lr : ℝ := lmaxR 0 l₂ k₁ k₂ with hLr
  set Ln : ℕ := max (max 0 l₂) (max k₁ k₂) with hLn
  set sig : ℝ := (2 : ℝ) ^ (-((2 : ℝ) ^ (Lr / (C₀ : ℝ))) + 2) with hsig
  have hLrcast : ((Ln : ℕ) : ℝ) = Lr := by
    rw [hLr, hLn, lmaxR, Work.Analysis.EndVar.lmax]
    push_cast
    rfl
  have hzero : ∀ n : ℕ, ¬ Gc n → u n = 0 := by
    intro n hn
    funext x
    have h1 : ¬ (Gc n ∧ Band n) := fun h => hn h.1
    simp only [hu, if_neg h1, Pi.zero_apply]
  have hper : ∀ n : ℕ, MeasureTheory.eLpNorm (fun x : ℤ => u n x)
      ((p₁⁻¹ + p₂⁻¹)⁻¹) MeasureTheory.Measure.count
      ≤ if Gc n then (K Λ : ENNReal) * ENNReal.ofReal W *
          ENNReal.ofReal ((((Nat.floor (a n) : ℕ)) : ℝ)⁻¹) *
          MeasureTheory.eLpNorm f p₁ MeasureTheory.Measure.count *
          MeasureTheory.eLpNorm g p₂ MeasureTheory.Measure.count else 0 := by
    intro n
    by_cases hg : Gc n
    · rw [if_pos hg]
      by_cases hb : Band n
      · have hgate : Gc n ∧ Band n := ⟨hg, hb⟩
        have hthis := hK a Λ l₂ k₁ k₂ f g hΛ ha ha1 hl₂ n
        rw [hW]
        have hun : u n = fun x : ℤ =>
            (if loGuard ρ C₀ a 0 l₂ k₁ k₂ n ∧ loBandCond ρ P l₂ k₁ k₂ (Nat.floor (a n)) then
              mainPartTuple ρ P C₀ a f g 0 l₂ k₁ k₂ n x
                - loMixedTuple ρ P C₀ a f g l₂ k₁ k₂ n x else 0) := by
          funext x
          simp only [hu, hGc, hBand]
        rw [hun]
        exact hthis
      · have h1 : ¬ (Gc n ∧ Band n) := fun h => hb h.2
        have hun : u n = 0 := by
          funext x
          simp only [hu, if_neg h1, Pi.zero_apply]
        rw [hun]
        simp
    · rw [if_neg hg, hzero n hg]
      simp
  have hcond : ∀ n : ℕ, Gc n →
      Ln ≤ Work.Analysis.EndVar.heightScale C₀ (Nat.floor (a n)) := by
    intro n hg
    have hg' : loGuard ρ C₀ a 0 l₂ k₁ k₂ n := by simpa only [hGc] using hg
    have h1 : Work.Analysis.EndVar.inIndexSet C₀ (max ((0 : ℕ) : ℤ) (l₂ : ℤ))
        ((k₁ : ℤ)) ((k₂ : ℤ)) (Nat.floor (a n)) := hg'.1
    rw [Work.Analysis.EndVar.inIndexSet] at h1
    obtain ⟨h2, h3, h4⟩ := h1
    have h2' : (l₂ : ℤ) ≤ ((Work.Analysis.EndVar.heightScale C₀ (Nat.floor (a n)) : ℕ) : ℤ) :=
      le_trans (le_max_right _ _) h2
    have h2'' : l₂ ≤ Work.Analysis.EndVar.heightScale C₀ (Nat.floor (a n)) := by omega
    have h3'' : k₁ ≤ Work.Analysis.EndVar.heightScale C₀ (Nat.floor (a n)) := by omega
    have h4'' : k₂ ≤ Work.Analysis.EndVar.heightScale C₀ (Nat.floor (a n)) := by omega
    have hmain : max (max 0 l₂) (max k₁ k₂)
        ≤ Work.Analysis.EndVar.heightScale C₀ (Nat.floor (a n)) :=
      max_le (max_le (Nat.zero_le _) h2'') (max_le h3'' h4'')
    simpa only [hLn] using hmain
  have hsum2 : (∑' n : ℕ, (if Gc n then
        ENNReal.ofReal ((((Nat.floor (a n) : ℕ)) : ℝ)⁻¹) else 0))
      ≤ ENNReal.ofReal (Efun Λ * sig) := by
    have hthis := tsum_ite_floor_le_indexSet C₀ hC₀ Λ hΛ (Dfun Λ) (hDfun0 Λ)
      (fun L hL a ha ha1 => hDfunb Λ hΛ L hL a ha ha1) Ln (Efun Λ) (le_of_eq rfl)
      a ha ha1 Gc hcond
    rw [hLrcast] at hthis
    rw [hsig]
    exact hthis
  have hWsig : W * sig ≤ Kabs := by
    have h := hKabs Ln
    rw [hLrcast] at h
    rw [hW, hsig, smallScaleWeight, hLr]
    exact h
  have hW0 : 0 ≤ W := by rw [hW]; exact smallScaleWeight_nonneg C ρ 0 l₂ k₁ k₂
  have hE0 : 0 ≤ Efun Λ := hEfun0 Λ
  have hK0 : (0 : ℝ) ≤ (K Λ : ℝ) := by positivity
  have hsig0 : 0 ≤ sig := by rw [hsig]; positivity
  have hKE : (0 : ℝ) ≤ 4 * (K Λ : ℝ) * Efun Λ :=
    mul_nonneg (mul_nonneg (by norm_num) hK0) hE0
  have hLw : lossWeight (0 : ℝ) ρ 0 l₂ k₁ k₂ = 1 := by rw [lossWeight]; simp
  have hreal : 4 * (K Λ : ℝ) * W * (Efun Λ * sig)
      ≤ (4 * (K Λ : ℝ) * Efun Λ * Kabs + 16) * lossWeight 0 ρ 0 l₂ k₁ k₂ := by
    have hWsig' : 4 * (K Λ : ℝ) * Efun Λ * (W * sig) ≤ 4 * (K Λ : ℝ) * Efun Λ * Kabs :=
      mul_le_mul_of_nonneg_left hWsig hKE
    calc 4 * (K Λ : ℝ) * W * (Efun Λ * sig)
        = 4 * (K Λ : ℝ) * Efun Λ * (W * sig) := by ring
      _ ≤ 4 * (K Λ : ℝ) * Efun Λ * Kabs := hWsig'
      _ ≤ (4 * (K Λ : ℝ) * Efun Λ * Kabs + 16) * lossWeight 0 ρ 0 l₂ k₁ k₂ := by
          rw [hLw]; nlinarith [mul_nonneg hKE hKabsnn]
  let Kc : NNReal := ⟨4 * (K Λ : ℝ) * Efun Λ * Kabs + 16, hKc_fun Λ⟩
  have hKc_coe : (Kc : ENNReal) = ENNReal.ofReal (4 * (K Λ : ℝ) * Efun Λ * Kabs + 16) :=
    ENNReal.ofReal_coe_nnreal.symm
  have hmul : 4 * (K Λ : ENNReal) * ENNReal.ofReal W * ENNReal.ofReal (Efun Λ * sig)
      ≤ (Kc : ENNReal) * ENNReal.ofReal (lossWeight 0 ρ 0 l₂ k₁ k₂) := by
    rw [hKc_coe]
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
            lossWeight 0 ρ 0 l₂ k₁ k₂) := ENNReal.ofReal_le_ofReal hreal
      _ = ENNReal.ofReal (4 * (K Λ : ℝ) * Efun Λ * Kabs + 16)
            * ENNReal.ofReal (lossWeight 0 ρ 0 l₂ k₁ k₂) := by
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
    _ ≤ ((Kc : ENNReal) * ENNReal.ofReal (lossWeight 0 ρ 0 l₂ k₁ k₂)) *
          (MeasureTheory.eLpNorm f p₁ MeasureTheory.Measure.count *
          MeasureTheory.eLpNorm g p₂ MeasureTheory.Measure.count) :=
        mul_le_mul' hmul le_rfl
    _ = (Kc : ENNReal) * ENNReal.ofReal (lossWeight 0 ρ 0 l₂ k₁ k₂) *
          MeasureTheory.eLpNorm f p₁ MeasureTheory.Measure.count *
          MeasureTheory.eLpNorm g p₂ MeasureTheory.Measure.count := by ring

/-! ## The band/off-band split of the §6 error -/

/-- **The §6 model-approximation error of the mixed range from its band and off-band parts.**  On
the guard the error splits pointwise into the part gated by `loBandCond` (where the repaired model
satisfies the band condition, so the §6 comparison is an `O(1/N)` estimate) and its complement
(where the comparison is only `O(1)`, but the number of admissible scales is `≲ 2^{2ρL}`, absorbed
by the weight `lossWeight c ρ …` with `c ≥ 2`; `NOTES_A7_ModelApprox.md` §2).  Subadditivity of the
variational norm and of `eLpNorm` and the weight upgrade give the claim with exponent `max cB cO`. -/
theorem loMixedErr_of_inputs (P : ℤ[X]) (p₁ p₂ : ENNReal) (hdeg : 2 ≤ P.natDegree)
    (hA1 : Work.KMTContract.AreaA1) (hp₁ : 1 < p₁) (htp₁ : p₁ < ⊤) (hp₂ : 1 < p₂)
    (htp₂ : p₂ < ⊤) (hsum : p₁⁻¹ + p₂⁻¹ ≤ 1)
    (hBand : LoMixedBandErrStatement P p₁ p₂) (hOff : LoMixedOffBandStatement P p₁ p₂) :
    LoMixedErrStatement P p₁ p₂ := by
  classical
  intro C₀ r hC₀ hr
  obtain ⟨cB, hcB, ρB, hρB, hB⟩ := hBand C₀ r hC₀ hr
  obtain ⟨cO, hcO, ρO, hρO, hO⟩ := hOff C₀ r hC₀ hr
  refine ⟨max cB cO, le_trans hcB (le_max_left _ _), min ρB ρO, lt_min hρB hρO, ?_⟩
  intro ρ hρ hρle
  have hρnn : (0 : ℝ) ≤ ρ := le_of_lt hρ
  have hρB' : ρ ≤ ρB := le_trans hρle (min_le_left _ _)
  have hρO' : ρ ≤ ρO := le_trans hρle (min_le_right _ _)
  obtain ⟨KB, hB'⟩ := hB ρ hρ hρB'
  obtain ⟨KO, hO'⟩ := hO ρ hρ hρO'
  refine ⟨fun Λ => KB Λ + KO Λ, ?_⟩
  intro a Λ l₂ k₁ k₂ f g hΛ ha ha1 hl₂
  have hq : (1 : ENNReal) ≤ (p₁⁻¹ + p₂⁻¹)⁻¹ := ENNReal.one_le_inv.mpr hsum
  have hr1 : (1 : NNReal) ≤ r := le_trans (by norm_num) (le_of_lt hr)
  set bf : ℕ → ℤ → ℂ := fun n x =>
    if loGuard ρ C₀ a 0 l₂ k₁ k₂ n ∧ loBandCond ρ P l₂ k₁ k₂ (Nat.floor (a n)) then
      mainPartTuple ρ P C₀ a f g 0 l₂ k₁ k₂ n x - loMixedTuple ρ P C₀ a f g l₂ k₁ k₂ n x
    else 0 with hbf
  set of_ : ℕ → ℤ → ℂ := fun n x =>
    if loGuard ρ C₀ a 0 l₂ k₁ k₂ n ∧ ¬ loBandCond ρ P l₂ k₁ k₂ (Nat.floor (a n)) then
      mainPartTuple ρ P C₀ a f g 0 l₂ k₁ k₂ n x - loMixedTuple ρ P C₀ a f g l₂ k₁ k₂ n x
    else 0 with hof
  have hnb : ∀ n : ℕ, ¬ loBandCond ρ P l₂ k₁ k₂ (Nat.floor (a n)) →
      ¬ (loGuard ρ C₀ a 0 l₂ k₁ k₂ n ∧ loBandCond ρ P l₂ k₁ k₂ (Nat.floor (a n))) :=
    fun n h hh => h hh.2
  have hna : ∀ n : ℕ, ¬ loGuard ρ C₀ a 0 l₂ k₁ k₂ n →
      ¬ (loGuard ρ C₀ a 0 l₂ k₁ k₂ n ∧ loBandCond ρ P l₂ k₁ k₂ (Nat.floor (a n))) :=
    fun n h hh => h hh.1
  have hna' : ∀ n : ℕ, ¬ loGuard ρ C₀ a 0 l₂ k₁ k₂ n →
      ¬ (loGuard ρ C₀ a 0 l₂ k₁ k₂ n ∧ ¬ loBandCond ρ P l₂ k₁ k₂ (Nat.floor (a n))) :=
    fun n h hh => h hh.1
  have hsplit : ∀ n x, mainPartTuple ρ P C₀ a f g 0 l₂ k₁ k₂ n x
        - loMixedTuple ρ P C₀ a f g l₂ k₁ k₂ n x = bf n x + of_ n x := by
    intro n x
    by_cases hg : loGuard ρ C₀ a 0 l₂ k₁ k₂ n
    · by_cases hb : loBandCond ρ P l₂ k₁ k₂ (Nat.floor (a n))
      · have h1 : loGuard ρ C₀ a 0 l₂ k₁ k₂ n
            ∧ loBandCond ρ P l₂ k₁ k₂ (Nat.floor (a n)) := ⟨hg, hb⟩
        have h2 : ¬ (loGuard ρ C₀ a 0 l₂ k₁ k₂ n
            ∧ ¬ loBandCond ρ P l₂ k₁ k₂ (Nat.floor (a n))) := fun h => h.2 hb
        simp only [hbf, hof, if_pos h1, if_neg h2]
        ring
      · have h1 : ¬ (loGuard ρ C₀ a 0 l₂ k₁ k₂ n
            ∧ loBandCond ρ P l₂ k₁ k₂ (Nat.floor (a n))) := fun h => hb h.2
        have h2 : loGuard ρ C₀ a 0 l₂ k₁ k₂ n
            ∧ ¬ loBandCond ρ P l₂ k₁ k₂ (Nat.floor (a n)) := ⟨hg, hb⟩
        simp only [hbf, hof, if_neg h1, if_pos h2]
        ring
    · simp only [hbf, hof, mainPartTuple_apply, loMixedTuple, if_neg hg,
        if_neg (hna n hg), if_neg (hna' n hg)]
      ring
  have hpw : ∀ x : ℤ, PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ =>
        mainPartTuple ρ P C₀ a f g 0 l₂ k₁ k₂ n x - loMixedTuple ρ P C₀ a f g l₂ k₁ k₂ n x)
      ≤ PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ => bf n x)
        + PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ => of_ n x) := by
    intro x
    have hfun : (fun n : ℕ => mainPartTuple ρ P C₀ a f g 0 l₂ k₁ k₂ n x
          - loMixedTuple ρ P C₀ a f g l₂ k₁ k₂ n x)
        = fun n : ℕ => bf n x + of_ n x := funext fun n => hsplit n x
    rw [hfun]
    exact variationalNorm_add_le hr1 _ _
  have hbnd := hB' a Λ l₂ k₁ k₂ f g hΛ ha ha1 hl₂
  have hoff := hO' a Λ l₂ k₁ k₂ f g hΛ ha ha1 hl₂
  set wgt : ENNReal := ENNReal.ofReal (lossWeight (max cB cO) ρ 0 l₂ k₁ k₂) with hwgt
  have hbnd' : MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
        (fun n : ℕ => bf n x)) (p₁⁻¹ + p₂⁻¹)⁻¹ MeasureTheory.Measure.count
      ≤ (KB Λ : ENNReal) * wgt * MeasureTheory.eLpNorm f p₁ MeasureTheory.Measure.count
          * MeasureTheory.eLpNorm g p₂ MeasureTheory.Measure.count := by
    refine hbnd.trans ?_
    rw [hwgt]
    exact mul_le_mul_of_le_left (mul_le_mul_of_le_left (mul_le_mul_of_le_right
      (ofReal_lossWeight_mono_L hρnn (le_max_left cB cO) 0 l₂ k₁ k₂) (KB Λ : ENNReal)) _) _
  have hoff' : MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
        (fun n : ℕ => of_ n x)) (p₁⁻¹ + p₂⁻¹)⁻¹ MeasureTheory.Measure.count
      ≤ (KO Λ : ENNReal) * wgt * MeasureTheory.eLpNorm f p₁ MeasureTheory.Measure.count
          * MeasureTheory.eLpNorm g p₂ MeasureTheory.Measure.count := by
    refine hoff.trans ?_
    rw [hwgt]
    exact mul_le_mul_of_le_left (mul_le_mul_of_le_left (mul_le_mul_of_le_right
      (ofReal_lossWeight_mono_L hρnn (le_max_right cB cO) 0 l₂ k₁ k₂) (KO Λ : ENNReal)) _) _
  refine (MeasureTheory.eLpNorm_mono_enorm (hf := by pw_aesm)
    (f := fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ =>
        mainPartTuple ρ P C₀ a f g 0 l₂ k₁ k₂ n x - loMixedTuple ρ P C₀ a f g l₂ k₁ k₂ n x))
    (g := fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ => bf n x)
      + PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ => of_ n x))
    (fun x => by simpa only [enorm_eq_self] using hpw x)).trans ?_
  refine (MeasureTheory.eLpNorm_add_le hq).trans ?_
  refine (add_le_add hbnd' hoff').trans ?_
  show (KB Λ : ENNReal) * wgt * MeasureTheory.eLpNorm f p₁ MeasureTheory.Measure.count
        * MeasureTheory.eLpNorm g p₂ MeasureTheory.Measure.count
      + (KO Λ : ENNReal) * wgt * MeasureTheory.eLpNorm f p₁ MeasureTheory.Measure.count
        * MeasureTheory.eLpNorm g p₂ MeasureTheory.Measure.count
      ≤ ((KB Λ + KO Λ : NNReal) : ENNReal) * wgt
        * MeasureTheory.eLpNorm f p₁ MeasureTheory.Measure.count
        * MeasureTheory.eLpNorm g p₂ MeasureTheory.Measure.count
  calc (KB Λ : ENNReal) * wgt * MeasureTheory.eLpNorm f p₁ MeasureTheory.Measure.count
          * MeasureTheory.eLpNorm g p₂ MeasureTheory.Measure.count
        + (KO Λ : ENNReal) * wgt * MeasureTheory.eLpNorm f p₁ MeasureTheory.Measure.count
          * MeasureTheory.eLpNorm g p₂ MeasureTheory.Measure.count
      = ((KB Λ : ENNReal) + (KO Λ : ENNReal)) * wgt
          * MeasureTheory.eLpNorm f p₁ MeasureTheory.Measure.count
          * MeasureTheory.eLpNorm g p₂ MeasureTheory.Measure.count := by ring
    _ ≤ ((KB Λ + KO Λ : NNReal) : ENNReal) * wgt
          * MeasureTheory.eLpNorm f p₁ MeasureTheory.Measure.count
          * MeasureTheory.eLpNorm g p₂ MeasureTheory.Measure.count := by
        rw [← ENNReal.coe_add]

/-! ## The assembly of the mixed case -/

/-- **The mixed case `l₁ = 0`, `l₂ ≥ 1` of the model approximation, from its two analytic
inputs.**  On this range the exact-height model tuple vanishes (`modelTuple_eq_zero_of_lo`), so
the target is the bound for the concrete columns.  Writing

  `mainPartTuple = (mainPartTuple − loMixedTuple) + loMixedTuple`

and using the subadditivity of the variational norm and of `eLpNorm`, the two inputs
`LoMixedErrStatement` (§6, the model-approximation error) and `LoMixedModelStatement` (§8, the
bound for the mixed model tuple) give the claim with the exponent `max cE cM`. -/
theorem loMixedLeft_of_inputs (P : ℤ[X]) (p₁ p₂ : ENNReal) (hdeg : 2 ≤ P.natDegree)
    (hA1 : Work.KMTContract.AreaA1) (hp₁ : 1 < p₁) (htp₁ : p₁ < ⊤) (hp₂ : 1 < p₂)
    (htp₂ : p₂ < ⊤) (hsum : p₁⁻¹ + p₂⁻¹ ≤ 1)
    (hErr : LoMixedErrStatement P p₁ p₂) (hModel : LoMixedModelStatement P p₁ p₂) :
    LoMixedLeftStatement P p₁ p₂ := by
  intro C₀ r hC₀ hr
  obtain ⟨cE, hcE, ρE, hρE, hE⟩ := hErr C₀ r hC₀ hr
  obtain ⟨cM, hcM, ρM, hρM, hM⟩ := hModel C₀ r hC₀ hr
  refine ⟨max cE cM, le_trans hcE (le_max_left _ _), min ρE ρM, lt_min hρE hρM, ?_⟩
  intro ρ hρ hρle
  have hρnn : (0 : ℝ) ≤ ρ := le_of_lt hρ
  have hρE' : ρ ≤ ρE := le_trans hρle (min_le_left _ _)
  have hρM' : ρ ≤ ρM := le_trans hρle (min_le_right _ _)
  obtain ⟨KE, hE'⟩ := hE ρ hρ hρE'
  obtain ⟨KM, hM'⟩ := hM ρ hρ hρM'
  refine ⟨fun Λ => KE Λ + KM Λ, ?_⟩
  intro a Λ l₁ l₂ k₁ k₂ f g hΛ ha ha1 hΦ
  obtain ⟨hl₁, hl₂⟩ := hΦ
  subst hl₁
  have hq : (1 : ENNReal) ≤ (p₁⁻¹ + p₂⁻¹)⁻¹ := ENNReal.one_le_inv.mpr hsum
  have hr1 : (1 : NNReal) ≤ r := le_trans (by norm_num) (le_of_lt hr)
  have hMT : ∀ n x, modelTuple ρ P C₀ a f g 0 l₂ k₁ k₂ n x = 0 :=
    fun n x => modelTuple_apply_eq_zero_of_lo ρ P C₀ a f g 0 l₂ k₁ k₂ n x (by omega)
  have hpw : ∀ x : ℤ, PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ =>
        mainPartTuple ρ P C₀ a f g 0 l₂ k₁ k₂ n x
          - modelTuple ρ P C₀ a f g 0 l₂ k₁ k₂ n x)
      ≤ PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ =>
            mainPartTuple ρ P C₀ a f g 0 l₂ k₁ k₂ n x
              - loMixedTuple ρ P C₀ a f g l₂ k₁ k₂ n x)
        + PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ =>
            loMixedTuple ρ P C₀ a f g l₂ k₁ k₂ n x) := by
    intro x
    have hfun : (fun n : ℕ => mainPartTuple ρ P C₀ a f g 0 l₂ k₁ k₂ n x
          - modelTuple ρ P C₀ a f g 0 l₂ k₁ k₂ n x)
        = fun n : ℕ => (mainPartTuple ρ P C₀ a f g 0 l₂ k₁ k₂ n x
            - loMixedTuple ρ P C₀ a f g l₂ k₁ k₂ n x)
            + loMixedTuple ρ P C₀ a f g l₂ k₁ k₂ n x := by
      funext n
      rw [hMT n x]
      ring
    rw [hfun]
    exact variationalNorm_add_le hr1 _ _
  refine (MeasureTheory.eLpNorm_mono_enorm (hf := by pw_aesm)
    (f := fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ =>
        mainPartTuple ρ P C₀ a f g 0 l₂ k₁ k₂ n x
          - modelTuple ρ P C₀ a f g 0 l₂ k₁ k₂ n x))
    (g := fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ =>
        mainPartTuple ρ P C₀ a f g 0 l₂ k₁ k₂ n x
          - loMixedTuple ρ P C₀ a f g l₂ k₁ k₂ n x)
      + PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ =>
        loMixedTuple ρ P C₀ a f g l₂ k₁ k₂ n x))
    (fun x => by simpa only [enorm_eq_self] using hpw x)).trans ?_
  refine (MeasureTheory.eLpNorm_add_le hq).trans ?_
  have herr := hE' a Λ l₂ k₁ k₂ f g hΛ ha ha1 hl₂
  have hmod := hM' a Λ l₂ k₁ k₂ f g hΛ ha ha1 hl₂
  set wgt : ENNReal := ENNReal.ofReal (lossWeight (max cE cM) ρ 0 l₂ k₁ k₂) with hwgt
  have herr' : MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
        (fun n : ℕ => mainPartTuple ρ P C₀ a f g 0 l₂ k₁ k₂ n x
          - loMixedTuple ρ P C₀ a f g l₂ k₁ k₂ n x))
      (p₁⁻¹ + p₂⁻¹)⁻¹ MeasureTheory.Measure.count
      ≤ (KE Λ : ENNReal) * wgt
          * MeasureTheory.eLpNorm f p₁ MeasureTheory.Measure.count
          * MeasureTheory.eLpNorm g p₂ MeasureTheory.Measure.count := by
    refine herr.trans ?_
    rw [hwgt]
    exact mul_le_mul_of_le_left (mul_le_mul_of_le_left (mul_le_mul_of_le_right
      (ofReal_lossWeight_mono_L hρnn (le_max_left cE cM) 0 l₂ k₁ k₂) (KE Λ : ENNReal)) _) _
  have hmod' : MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
        (fun n : ℕ => loMixedTuple ρ P C₀ a f g l₂ k₁ k₂ n x))
      (p₁⁻¹ + p₂⁻¹)⁻¹ MeasureTheory.Measure.count
      ≤ (KM Λ : ENNReal) * wgt
          * MeasureTheory.eLpNorm f p₁ MeasureTheory.Measure.count
          * MeasureTheory.eLpNorm g p₂ MeasureTheory.Measure.count := by
    refine hmod.trans ?_
    rw [hwgt]
    exact mul_le_mul_of_le_left (mul_le_mul_of_le_left (mul_le_mul_of_le_right
      (ofReal_lossWeight_mono_L hρnn (le_max_right cE cM) 0 l₂ k₁ k₂) (KM Λ : ENNReal)) _) _
  refine (add_le_add herr' hmod').trans ?_
  show (KE Λ : ENNReal) * wgt * MeasureTheory.eLpNorm f p₁ MeasureTheory.Measure.count
          * MeasureTheory.eLpNorm g p₂ MeasureTheory.Measure.count
        + (KM Λ : ENNReal) * wgt * MeasureTheory.eLpNorm f p₁ MeasureTheory.Measure.count
          * MeasureTheory.eLpNorm g p₂ MeasureTheory.Measure.count
      ≤ ((KE Λ + KM Λ : NNReal) : ENNReal) * wgt
          * MeasureTheory.eLpNorm f p₁ MeasureTheory.Measure.count
          * MeasureTheory.eLpNorm g p₂ MeasureTheory.Measure.count
  calc (KE Λ : ENNReal) * wgt * MeasureTheory.eLpNorm f p₁ MeasureTheory.Measure.count
          * MeasureTheory.eLpNorm g p₂ MeasureTheory.Measure.count
        + (KM Λ : ENNReal) * wgt * MeasureTheory.eLpNorm f p₁ MeasureTheory.Measure.count
          * MeasureTheory.eLpNorm g p₂ MeasureTheory.Measure.count
      = ((KE Λ : ENNReal) + (KM Λ : ENNReal)) * wgt
          * MeasureTheory.eLpNorm f p₁ MeasureTheory.Measure.count
          * MeasureTheory.eLpNorm g p₂ MeasureTheory.Measure.count := by ring
    _ ≤ ((KE Λ + KM Λ : NNReal) : ENNReal) * wgt
          * MeasureTheory.eLpNorm f p₁ MeasureTheory.Measure.count
          * MeasureTheory.eLpNorm g p₂ MeasureTheory.Measure.count := by
        rw [← ENNReal.coe_add]

/-! ## The `g`-side factor estimate, rewired onto the *clean* `A7Hi.LinVarG`

`Work.KMTAreas.A7.LoMixedModel` pins its `g`-side factor on
`Work.KMTAreas.A7HiRep.chainPartSqFunPosMemLp`, an open (and per its own docstring possibly
mis-stated) node.  The same linear estimate is however available in the tree *proved and
axiom-clean* as `Work.KMTAreas.A7Hi.LinVarG` — its statement is verbatim the `Gcl`-form consumed by
`Work.KMTAreas.A7MixedG`'s `LinVarGuard` bookkeeping (see `A7/LinVarGuardWiring.lean`'s
`gmixedFam_eq_gcl`).

The three definitions below re-run that bookkeeping locally, so that this file's target rests on the
clean `A7Hi.LinVarG` rather than on the open node.  (`A7/LoMixedModel.lean` is imported only for the
*statements* `loMixedModel_of_inputs`/`loMixedFSide`, both axiom-clean; none of its tainted
declarations is used here.) -/

end

end Work.KMTAreas.A7
