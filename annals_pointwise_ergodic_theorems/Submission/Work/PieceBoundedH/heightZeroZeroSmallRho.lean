import Mathlib
import Submission.Work.KMTAreas.A7.LoErrSingleScale00
import Submission.Work.KMTAreas.A7.LoModelLargeScaleHolds
import Submission.Port.Aesm

/-
# The bounded-height `(2,2,1)` piece at arithmetic height `(0,0)` and small `ρ`

`Work.PieceBoundedH.heightZeroZeroSmallRho` is the `(l₁,l₂) = (0,0)`, `p₁ = p₂ = 2` instance of the
§6 model approximation at bounded modulation height: for small `ρ` the variational norm of the
concrete §5 column `n ↦ mainPartTuple ρ P C₀ a f g 0 0 k₁ k₂ n` is bounded by
`K(Λ) · lossWeight c ρ 0 0 k₁ k₂ · ‖f‖₂‖g‖₂`, with `K` allowed to depend on `ρ`.

The estimate is the `l = 0` case of `Work.KMTAreas.A7.ModelApproxLo`.  At arithmetic height `0`
the exact-height model tuple vanishes (`modelTuple_apply_eq_zero_of_lo`), so the concrete column is
split as

  `mainPartTuple = (mainPartTuple − loModelTuple) + loModelTuple`,

* the **model part** `loModelTuple` is bounded by the §8 large-scale estimate
  `LoModelStatement` (proved: `Work.KMTAreas.A7.LoModelLargeScaleHolds`);
* the **error** `mainPartTuple − loModelTuple` has the single-scale §6 size
  `2^{cL}⌊a n⌋^{-1}‖f‖₂‖g‖₂` (`LoErrStatement`, proved: `Work.KMTAreas.A7.LoErrSingleScale00`);
  summing the `ℓ²` norms over the scales with the spike bound `VarNormTsumLp`
  (`‖V^r u‖_{ℓᵖ} ≤ ∑ₙ 4‖u n‖_{ℓᵖ}`) and bounding `∑ₙ ⌊a n⌋^{-1}` over the index set by the
  doubly-exponential smallness `2^{-2^{L/C₀}+2}` (`invFloorSum_le`, `tsum_ite_floor_le_indexSet`)
  absorbs it into the weight `lossWeight c ρ 0 0 k₁ k₂`.

The two bookkeeping lemmas (`expGeLinearZ`, `rpowMulTwoRpowNegBoundZ`) and the assembly
`modelApproxZeroZeroZ` below are the `(0,0)` half of `Work.KMTAreas.A7.ModelApproxLo`, restated in
this module so that it can be imported without the (still open) mixed `l₁ = 0`, `l₂ ≥ 1` chapter;
the target is then its `p₁ = p₂ = 2` instance.  The extra hypotheses `lcL 0 0 k₁ k₂ ≤ B` and
`k₁ = 0 ∨ k₂ = 0` of the target are not used by this route — the estimate holds for every pair
`(k₁,k₂)` — but they do not weaken it.
-/

set_option maxHeartbeats 4000000

namespace Work.PieceBoundedH

noncomputable section

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal BigOperators
open PointwiseErgodicTheorems Submission.PointwiseErgodicTheorems
open Work.KMTAreas.A7
open Work.Analysis.EndVar
open Work.KMTContract Work.Analysis.IonescuWainger Work.Analysis.IWMultiplier

/-! ## The bookkeeping of the summability of the §6 error -/

/-- For `C₀ ≥ 1` and `c ≥ 0`, eventually `(c+2) * y ≤ 2^{y/C₀}`. -/
lemma expGeLinearZ (c : ℝ) (hc : 0 ≤ c) (C₀ : ℕ) (hC₀ : 1 ≤ C₀) :
    ∃ Y : ℝ, ∀ y : ℝ, Y ≤ y → (c + 2) * y ≤ (2 : ℝ) ^ (y / (C₀ : ℝ)) := by
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hC0 : (0 : ℝ) < (C₀ : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hC₀)
  have hpos : (0 : ℝ) < Real.log 2 / (C₀ : ℝ) := div_pos hlog2 hC0
  have hz : Tendsto (fun z : ℝ => Real.exp z / z) atTop atTop := by
    simpa using Real.tendsto_exp_div_pow_atTop 1
  have hlin : Tendsto (fun y : ℝ => y * (Real.log 2 / (C₀ : ℝ))) atTop atTop :=
    Tendsto.atTop_mul_const hpos tendsto_id
  have hcomp : Tendsto (fun y : ℝ => Real.exp (y * (Real.log 2 / (C₀ : ℝ)))
      / (y * (Real.log 2 / (C₀ : ℝ)))) atTop atTop := hz.comp hlin
  have hcomp2 : Tendsto (fun y : ℝ => (Real.exp (y * (Real.log 2 / (C₀ : ℝ)))
      / (y * (Real.log 2 / (C₀ : ℝ)))) * (Real.log 2 / (C₀ : ℝ))) atTop atTop :=
    hcomp.atTop_mul_const hpos
  have heq : ∀ y : ℝ, y ≠ 0 →
      (Real.exp (y * (Real.log 2 / (C₀ : ℝ))) / (y * (Real.log 2 / (C₀ : ℝ))))
        * (Real.log 2 / (C₀ : ℝ)) = (2 : ℝ) ^ (y / (C₀ : ℝ)) / y := by
    intro y hy
    have ha : Real.log 2 / (C₀ : ℝ) ≠ 0 := ne_of_gt hpos
    rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
    have harg : Real.log 2 * (y / (C₀ : ℝ)) = y * (Real.log 2 / (C₀ : ℝ)) := by ring
    rw [harg]
    field_simp
  have hevent : (fun y : ℝ => (Real.exp (y * (Real.log 2 / (C₀ : ℝ)))
      / (y * (Real.log 2 / (C₀ : ℝ)))) * (Real.log 2 / (C₀ : ℝ)))
      =ᶠ[atTop] fun y : ℝ => (2 : ℝ) ^ (y / (C₀ : ℝ)) / y := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with y hy
    exact heq y (ne_of_gt hy)
  have hkey : Tendsto (fun y : ℝ => (2 : ℝ) ^ (y / (C₀ : ℝ)) / y) atTop atTop :=
    Tendsto.congr' hevent hcomp2
  have hev := hkey.eventually_ge_atTop (c + 2)
  rw [eventually_atTop] at hev
  obtain ⟨Y, hY⟩ := hev
  refine ⟨max Y 1, fun y hy => ?_⟩
  have hy0 : (0 : ℝ) < y := lt_of_lt_of_le zero_lt_one (le_trans (le_max_right _ _) hy)
  have h := hY y (le_trans (le_max_left _ _) hy)
  rw [le_div_iff₀ hy0] at h
  linarith

/-- The doubly-exponential weight is bounded. -/
lemma rpowMulTwoRpowNegBoundZ (c : ℝ) (hc : 0 ≤ c) (C₀ : ℕ) (hC₀ : 1 ≤ C₀)
    (D : ℝ) (hD : 0 ≤ D) :
    ∃ E : ℝ, 0 ≤ E ∧ ∀ L : ℕ, D * (2:ℝ) ^ (c * (L:ℝ)) *
        (2:ℝ) ^ (-((2:ℝ) ^ ((L:ℝ)/(C₀:ℝ))) + 2) ≤ E := by
  obtain ⟨Y, hY⟩ := expGeLinearZ c hc C₀ hC₀
  have hC0 : (0 : ℝ) < (C₀ : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hC₀)
  set X : ℝ := max Y 1 with hX
  set N₀ : ℕ := ⌈X⌉₊ with hN₀
  have hXN₀ : X ≤ (N₀ : ℝ) := Nat.le_ceil X
  refine ⟨max D (D * (2:ℝ) ^ (c * (N₀:ℝ)) * 4), ?_, fun L => ?_⟩
  · refine le_trans hD (le_max_left _ _)
  by_cases hL : L ≤ N₀
  · have h1 : (2:ℝ) ^ (c * (L:ℝ)) ≤ (2:ℝ) ^ (c * (N₀:ℝ)) := by
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      have : (L:ℝ) ≤ (N₀:ℝ) := by exact_mod_cast hL
      nlinarith
    have h2 : (2:ℝ) ^ (-((2:ℝ) ^ ((L:ℝ)/(C₀:ℝ))) + 2) ≤ 4 := by
      have h3 : (1:ℝ) ≤ (2:ℝ) ^ ((L:ℝ)/(C₀:ℝ)) := Real.one_le_rpow (by norm_num) (by positivity)
      have h4 := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 2)
        (by linarith : -((2:ℝ) ^ ((L:ℝ)/(C₀:ℝ))) + 2 ≤ 2)
      rw [show (2:ℝ)^(2:ℝ) = 4 from by rw [Real.rpow_two]; norm_num] at h4
      exact h4
    have hD4 : (0:ℝ) ≤ D * (2:ℝ) ^ (c * (N₀:ℝ)) := by positivity
    have hDnn : (0:ℝ) ≤ D := hD
    calc D * (2:ℝ) ^ (c * (L:ℝ)) * (2:ℝ) ^ (-((2:ℝ) ^ ((L:ℝ)/(C₀:ℝ))) + 2)
        ≤ D * (2:ℝ) ^ (c * (N₀:ℝ)) * (2:ℝ) ^ (-((2:ℝ) ^ ((L:ℝ)/(C₀:ℝ))) + 2) := by
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1 hD) (by positivity)
      _ ≤ D * (2:ℝ) ^ (c * (N₀:ℝ)) * 4 := mul_le_mul_of_nonneg_left h2 hD4
      _ ≤ max D (D * (2:ℝ) ^ (c * (N₀:ℝ)) * 4) := le_max_right _ _
  · push Not at hL
    have hLX : X ≤ (L:ℝ) := le_trans hXN₀ (by exact_mod_cast (le_of_lt hL))
    have hL1 : (1:ℝ) ≤ (L:ℝ) := le_trans (le_max_right _ 1) hLX
    have hLY : Y ≤ (L:ℝ) := le_trans (le_max_left Y 1) hLX
    have hle := hY (L:ℝ) hLY
    have hkey : c * (L:ℝ) + 2 ≤ (2:ℝ) ^ ((L:ℝ)/(C₀:ℝ)) := by
      have h2 : c * (L:ℝ) + 2 ≤ (c+2) * (L:ℝ) := by nlinarith
      linarith
    have hfin : c * (L:ℝ) - (2:ℝ) ^ ((L:ℝ)/(C₀:ℝ)) + 2 ≤ 0 := by linarith
    have hsplit : D * (2:ℝ) ^ (c * (L:ℝ)) * (2:ℝ) ^ (-((2:ℝ) ^ ((L:ℝ)/(C₀:ℝ))) + 2)
        = D * (2:ℝ) ^ (c * (L:ℝ) - (2:ℝ) ^ ((L:ℝ)/(C₀:ℝ)) + 2) := by
      rw [mul_assoc, ← Real.rpow_add (by norm_num : (0:ℝ) < 2)]
      ring_nf
    rw [hsplit]
    calc D * (2:ℝ) ^ (c * (L:ℝ) - (2:ℝ) ^ ((L:ℝ)/(C₀:ℝ)) + 2)
        ≤ D * 1 := by
          refine mul_le_mul_of_nonneg_left ?_ hD
          exact Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) hfin
      _ = D := mul_one D
      _ ≤ max D (D * (2:ℝ) ^ (c * (N₀:ℝ)) * 4) := le_max_left _ _

/-- The nonnegative constant of the assembly (a structure-literal `NNReal`). -/
def loKcZ (a : ℝ) (h : 0 ≤ a) : NNReal := ⟨a, h⟩
/-- **The assembly of the `l = 0` model approximation** from its two analytic inputs
(`LoErrStatement`, the single-scale §6 comparison, and `LoModelStatement`, the §8 bound for the
level-`0` model tuple). -/
theorem modelApproxZeroZeroZ (P : Polynomial ℤ) (p₁ p₂ : ENNReal) (hdeg : 2 ≤ P.natDegree)
    (hA1 : Work.KMTContract.AreaA1) (hp₁ : 1 < p₁) (htp₁ : p₁ < ⊤) (hp₂ : 1 < p₂)
    (htp₂ : p₂ < ⊤) (hsum : p₁⁻¹ + p₂⁻¹ ≤ 1)
    (hErr : LoErrStatement P p₁ p₂) (hModel : LoModelStatement P p₁ p₂) :
    ∀ (C₀ : ℕ) (r : NNReal), 1 ≤ C₀ → (2 : NNReal) < r →
      ∃ c : ℝ, 0 ≤ c ∧ ∃ ρ₀ : ℝ, 0 < ρ₀ ∧
        ∀ ρ : ℝ, 0 < ρ → ρ ≤ ρ₀ → ∃ K : NNReal → NNReal,
          ∀ (a : ℕ → NNReal) (Λ : NNReal) (l₁ l₂ k₁ k₂ : ℕ) (f g : ℤ → ℂ),
            1 < Λ → PointwiseErgodicTheorems.Lacunary Λ a → (∀ n, 1 ≤ a n) →
            l₁ = 0 ∧ l₂ = 0 →
            MeasureTheory.eLpNorm (fun x : ℤ =>
                PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ =>
                  Work.KMTAreas.A7.mainPartTuple ρ P C₀ a f g l₁ l₂ k₁ k₂ n x
                    - Work.KMTAreas.A7.modelTuple ρ P C₀ a f g l₁ l₂ k₁ k₂ n x))
              (p₁⁻¹ + p₂⁻¹)⁻¹ MeasureTheory.Measure.count
            ≤ (K Λ : ENNReal) *
                ENNReal.ofReal (Work.KMTAreas.A7.lossWeight c ρ l₁ l₂ k₁ k₂) *
                MeasureTheory.eLpNorm f p₁ MeasureTheory.Measure.count *
                MeasureTheory.eLpNorm g p₂ MeasureTheory.Measure.count := by
  intro C₀ r hC₀ hr
  classical
  have hC₀pos : (0 : ℝ) < (C₀ : ℝ) := by
    have : (1 : ℕ) ≤ C₀ := hC₀
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hC₀)
  have hr1 : (1 : NNReal) ≤ r := le_trans (by norm_num) hr.le
  have hp : (1 : ENNReal) ≤ (p₁⁻¹ + p₂⁻¹)⁻¹ := ENNReal.one_le_inv.mpr hsum
  obtain ⟨cE, hcE, ρE, hρE, hE⟩ := hErr C₀ hC₀
  obtain ⟨cM, hcM, ρM, hρM, hM⟩ := hModel C₀ r hC₀ hr
  -- the summability constant `D(Λ)` of `invFloorSum_le`
  set Dfun : NNReal → ℝ :=
    fun Λ => if h : 1 < Λ then Classical.choose (invFloorSum_le C₀ hC₀ Λ h) else 0 with hDfun
  have hDfun0 : ∀ Λ : NNReal, 0 ≤ Dfun Λ := by
    intro Λ
    by_cases h : 1 < Λ
    · rw [hDfun]; simp only [dif_pos h]
      exact (Classical.choose_spec (invFloorSum_le C₀ hC₀ Λ h)).1
    · rw [hDfun]; simp [h]
  have hDfunb : ∀ (Λ : NNReal), 1 < Λ → ∀ (L : ℕ), 1 ≤ L → ∀ (a : ℕ → NNReal),
      PointwiseErgodicTheorems.Lacunary Λ a → (∀ n, 1 ≤ a n) →
      (∑' n : ℕ, (if L ≤ Work.Analysis.EndVar.heightScale C₀ (Nat.floor (a n))
        then (((Nat.floor (a n) : ℕ)) : ℝ)⁻¹ else 0))
        ≤ Dfun Λ * (2 : ℝ) ^ (-((2 : ℝ) ^ ((L : ℝ) / (C₀ : ℝ))) + 2) := by
    intro Λ hΛ L hL a ha ha1
    rw [hDfun]; simp only [dif_pos hΛ]
    exact (Classical.choose_spec (invFloorSum_le C₀ hC₀ Λ hΛ)).2 L hL a ha ha1
  refine ⟨max cE cM + 2, by positivity, min ρE (min ρM (1 / (4 * (C₀ : ℝ)))), ?_, ?_⟩
  · exact lt_min hρE (lt_min hρM (by positivity))
  intro ρ hρ hρle
  have hρnn : (0 : ℝ) ≤ ρ := le_of_lt hρ
  have hρE' : ρ ≤ ρE := le_trans hρle (min_le_left _ _)
  have hρM' : ρ ≤ ρM := le_trans hρle (le_trans (min_le_right _ _) (min_le_left _ _))
  obtain ⟨KE, hE'⟩ := hE ρ hρ hρE'
  obtain ⟨KM, hM'⟩ := hM ρ hρ hρM'
  -- the two exponential constants
  set Emax : NNReal → ℝ := fun Λ => max (2 * (Λ : ℝ) / ((Λ : ℝ) - 1)) (Dfun Λ) with hEmax
  have hEmax0 : ∀ Λ : NNReal, 0 ≤ Emax Λ := by
    intro Λ
    have : 0 ≤ Dfun Λ := hDfun0 Λ
    rw [hEmax]
    exact le_trans this (le_max_right _ _)
  have hEmax1 : ∀ (Λ : NNReal), 1 < Λ →
      max (2 * (Λ : ℝ) / ((Λ : ℝ) - 1)) (Dfun Λ) ≤ Emax Λ := fun Λ _ => le_of_eq rfl
  have hsup : ∀ Λ : NNReal, ∃ E : ℝ, 0 ≤ E ∧ ∀ L : ℕ,
      4 * (KE Λ : ℝ) * Emax Λ * (2 : ℝ) ^ (cE * (L : ℝ)) *
        (2 : ℝ) ^ (-((2 : ℝ) ^ ((L : ℝ) / (C₀ : ℝ))) + 2) ≤ E := by
    intro Λ
    have hD : 0 ≤ 4 * (KE Λ : ℝ) * Emax Λ := by
      have := hEmax0 Λ; positivity
    exact rpowMulTwoRpowNegBoundZ cE hcE C₀ hC₀ (4 * (KE Λ : ℝ) * Emax Λ) hD
  set Efun : NNReal → ℝ := fun Λ => Classical.choose (hsup Λ) with hEfun
  have hEfun0 : ∀ Λ : NNReal, 0 ≤ Efun Λ := fun Λ => (Classical.choose_spec (hsup Λ)).1
  have hEfunb : ∀ (Λ : NNReal) (L : ℕ),
      4 * (KE Λ : ℝ) * Emax Λ * (2 : ℝ) ^ (cE * (L : ℝ)) *
        (2 : ℝ) ^ (-((2 : ℝ) ^ ((L : ℝ) / (C₀ : ℝ))) + 2) ≤ Efun Λ :=
    fun Λ L => (Classical.choose_spec (hsup Λ)).2 L
  refine ⟨fun Λ => loKcZ (Efun Λ + (KM Λ : ℝ)) (add_nonneg (hEfun0 Λ) (by positivity)), ?_⟩
  intro a Λ l₁ l₂ k₁ k₂ f g hΛ ha ha1 h00
  have hl₁ : l₁ = 0 := h00.1
  have hl₂ : l₂ = 0 := h00.2
  have hlo : ¬ (1 ≤ l₁ ∧ 1 ≤ l₂) := by omega
  -- (0) the exact-height model vanishes in this range
  have hMT : ∀ n x, modelTuple ρ P C₀ a f g l₁ l₂ k₁ k₂ n x = 0 :=
    fun n x => modelTuple_apply_eq_zero_of_lo ρ P C₀ a f g l₁ l₂ k₁ k₂ n x hlo
  -- (1) the pointwise split
  have hpt : ∀ x : ℤ,
      PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ =>
          mainPartTuple ρ P C₀ a f g l₁ l₂ k₁ k₂ n x
            - modelTuple ρ P C₀ a f g l₁ l₂ k₁ k₂ n x)
        ≤ PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ =>
            mainPartTuple ρ P C₀ a f g l₁ l₂ k₁ k₂ n x
              - loModelTuple ρ P C₀ a f g l₁ l₂ k₁ k₂ n x)
          + PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ =>
              loModelTuple ρ P C₀ a f g l₁ l₂ k₁ k₂ n x) := by
    intro x
    have hfun : (fun n : ℕ => mainPartTuple ρ P C₀ a f g l₁ l₂ k₁ k₂ n x
          - modelTuple ρ P C₀ a f g l₁ l₂ k₁ k₂ n x)
        = fun n : ℕ => (mainPartTuple ρ P C₀ a f g l₁ l₂ k₁ k₂ n x
            - loModelTuple ρ P C₀ a f g l₁ l₂ k₁ k₂ n x)
            + loModelTuple ρ P C₀ a f g l₁ l₂ k₁ k₂ n x := by
      funext n
      rw [hMT n x]
      ring
    rw [hfun]
    exact Submission.PointwiseErgodicTheorems.variationalNorm_add_le hr1 _ _
  refine (MeasureTheory.eLpNorm_mono_enorm (hf := by pw_aesm)
    (f := fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ =>
        mainPartTuple ρ P C₀ a f g l₁ l₂ k₁ k₂ n x - modelTuple ρ P C₀ a f g l₁ l₂ k₁ k₂ n x))
    (g := fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ =>
        mainPartTuple ρ P C₀ a f g l₁ l₂ k₁ k₂ n x - loModelTuple ρ P C₀ a f g l₁ l₂ k₁ k₂ n x)
      + PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ =>
        loModelTuple ρ P C₀ a f g l₁ l₂ k₁ k₂ n x))
    (fun x => by simpa only [enorm_eq_self] using hpt x)).trans ?_
  refine (MeasureTheory.eLpNorm_add_le hp).trans ?_
  -- (2) the model part
  have hmod : MeasureTheory.eLpNorm (fun x : ℤ =>
        PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ =>
          loModelTuple ρ P C₀ a f g l₁ l₂ k₁ k₂ n x))
      (p₁⁻¹ + p₂⁻¹)⁻¹ MeasureTheory.Measure.count
      ≤ (KM Λ : ENNReal) * ENNReal.ofReal (lossWeight cM ρ l₁ l₂ k₁ k₂)
          * MeasureTheory.eLpNorm f p₁ MeasureTheory.Measure.count
          * MeasureTheory.eLpNorm g p₂ MeasureTheory.Measure.count :=
    hM' a Λ l₁ l₂ k₁ k₂ f g hΛ ha ha1 hlo
  -- (3) the error part
  set Xe : ENNReal := (KE Λ : ENNReal)
      * ENNReal.ofReal ((2 : ℝ) ^ (cE * lmaxR l₁ l₂ k₁ k₂))
      * MeasureTheory.eLpNorm f p₁ MeasureTheory.Measure.count
      * MeasureTheory.eLpNorm g p₂ MeasureTheory.Measure.count with hXe
  have hper : ∀ n : ℕ, MeasureTheory.eLpNorm (fun x : ℤ =>
        mainPartTuple ρ P C₀ a f g l₁ l₂ k₁ k₂ n x
          - loModelTuple ρ P C₀ a f g l₁ l₂ k₁ k₂ n x)
      (p₁⁻¹ + p₂⁻¹)⁻¹ MeasureTheory.Measure.count
      ≤ Xe * ENNReal.ofReal ((((Nat.floor (a n) : ℕ)) : ℝ)⁻¹) := by
    intro n
    have h := hE' a Λ l₁ l₂ k₁ k₂ f g hΛ ha ha1 hl₁ hl₂ n
    rw [hXe]
    exact h.trans (le_of_eq (by ac_rfl))
  have hzero : ∀ n : ℕ, ¬ loGuard ρ C₀ a l₁ l₂ k₁ k₂ n →
      (fun x : ℤ => mainPartTuple ρ P C₀ a f g l₁ l₂ k₁ k₂ n x
          - loModelTuple ρ P C₀ a f g l₁ l₂ k₁ k₂ n x) = 0 := by
    intro n hn
    funext x
    rw [mainPartTuple_apply, loModelTuple]
    rw [if_neg hn, if_neg hn]
    simp
  have hper' : ∀ n : ℕ, MeasureTheory.eLpNorm (fun x : ℤ =>
        mainPartTuple ρ P C₀ a f g l₁ l₂ k₁ k₂ n x
          - loModelTuple ρ P C₀ a f g l₁ l₂ k₁ k₂ n x)
      (p₁⁻¹ + p₂⁻¹)⁻¹ MeasureTheory.Measure.count
      ≤ if loGuard ρ C₀ a l₁ l₂ k₁ k₂ n
        then Xe * ENNReal.ofReal ((((Nat.floor (a n) : ℕ)) : ℝ)⁻¹) else 0 := by
    intro n
    by_cases hn : loGuard ρ C₀ a l₁ l₂ k₁ k₂ n
    · rw [if_pos hn]; exact hper n
    · rw [if_neg hn, hzero n hn]; simp
  have hvar := VarNormTsumLp hr1 hp (fun n x => mainPartTuple ρ P C₀ a f g l₁ l₂ k₁ k₂ n x
      - loModelTuple ρ P C₀ a f g l₁ l₂ k₁ k₂ n x)
  have hstep : (∑' n : ℕ, 4 * MeasureTheory.eLpNorm (fun x : ℤ =>
        mainPartTuple ρ P C₀ a f g l₁ l₂ k₁ k₂ n x
          - loModelTuple ρ P C₀ a f g l₁ l₂ k₁ k₂ n x)
      (p₁⁻¹ + p₂⁻¹)⁻¹ MeasureTheory.Measure.count)
      ≤ 4 * Xe * (∑' n : ℕ, (if loGuard ρ C₀ a l₁ l₂ k₁ k₂ n
          then ENNReal.ofReal ((((Nat.floor (a n) : ℕ)) : ℝ)⁻¹) else 0)) := by
    calc (∑' n : ℕ, 4 * MeasureTheory.eLpNorm (fun x : ℤ =>
          mainPartTuple ρ P C₀ a f g l₁ l₂ k₁ k₂ n x
            - loModelTuple ρ P C₀ a f g l₁ l₂ k₁ k₂ n x)
        (p₁⁻¹ + p₂⁻¹)⁻¹ MeasureTheory.Measure.count)
        ≤ ∑' n : ℕ, 4 * (if loGuard ρ C₀ a l₁ l₂ k₁ k₂ n
            then Xe * ENNReal.ofReal ((((Nat.floor (a n) : ℕ)) : ℝ)⁻¹) else 0) :=
          ENNReal.tsum_le_tsum (fun n => mul_le_mul' le_rfl (hper' n))
      _ = 4 * Xe * (∑' n : ℕ, (if loGuard ρ C₀ a l₁ l₂ k₁ k₂ n
            then ENNReal.ofReal ((((Nat.floor (a n) : ℕ)) : ℝ)⁻¹) else 0)) := by
          rw [← ENNReal.tsum_mul_left]
          refine tsum_congr (fun n => ?_)
          by_cases hn : loGuard ρ C₀ a l₁ l₂ k₁ k₂ n
          · rw [if_pos hn, if_pos hn]; ring
          · rw [if_neg hn, if_neg hn]; ring
  -- the guard implies the height condition
  have hcond : ∀ n : ℕ, loGuard ρ C₀ a l₁ l₂ k₁ k₂ n →
      max (max l₁ l₂) (max k₁ k₂) ≤ Work.Analysis.EndVar.heightScale C₀ (Nat.floor (a n)) := by
    intro n hg
    have h1 : inIndexSet C₀ (max (l₁ : ℤ) (l₂ : ℤ)) (k₁ : ℤ) (k₂ : ℤ) (Nat.floor (a n)) := hg.1
    rw [inIndexSet] at h1
    obtain ⟨ha1', hk1', hk2'⟩ := h1
    have h2 : max (l₁ : ℤ) (l₂ : ℤ) ≤
        ((Work.Analysis.EndVar.heightScale C₀ (Nat.floor (a n)) : ℕ) : ℤ) := ha1'
    have h3 : (k₁ : ℤ) ≤
        ((Work.Analysis.EndVar.heightScale C₀ (Nat.floor (a n)) : ℕ) : ℤ) := hk1'
    have h4 : (k₂ : ℤ) ≤
        ((Work.Analysis.EndVar.heightScale C₀ (Nat.floor (a n)) : ℕ) : ℤ) := hk2'
    omega
  have hLcast : (((max (max l₁ l₂) (max k₁ k₂) : ℕ)) : ℝ) = lmaxR l₁ l₂ k₁ k₂ := by
    rw [lmaxR, Work.Analysis.EndVar.lmax, Nat.cast_max, Nat.cast_max]
    push_cast
    rfl
  have hsum4 : (∑' n : ℕ, (if loGuard ρ C₀ a l₁ l₂ k₁ k₂ n
        then ENNReal.ofReal ((((Nat.floor (a n) : ℕ)) : ℝ)⁻¹) else 0))
      ≤ ENNReal.ofReal (Emax Λ
          * (2 : ℝ) ^ (-((2 : ℝ) ^ (lmaxR l₁ l₂ k₁ k₂ / (C₀ : ℝ))) + 2)) := by
    have hmain := tsum_ite_floor_le_indexSet C₀ hC₀ Λ hΛ (Dfun Λ) (hDfun0 Λ)
      (fun L hL a ha ha1 => hDfunb Λ hΛ L hL a ha ha1)
      (max (max l₁ l₂) (max k₁ k₂)) (Emax Λ) (hEmax1 Λ hΛ) a ha ha1
      (fun n => loGuard ρ C₀ a l₁ l₂ k₁ k₂ n) hcond
    rwa [hLcast] at hmain
  -- the real weight arithmetic
  have hreal : 4 * (KE Λ : ℝ) * (2 : ℝ) ^ (cE * lmaxR l₁ l₂ k₁ k₂)
        * (Emax Λ * (2 : ℝ) ^ (-((2 : ℝ) ^ (lmaxR l₁ l₂ k₁ k₂ / (C₀ : ℝ))) + 2))
      ≤ Efun Λ := by
    have hb := hEfunb Λ (max (max l₁ l₂) (max k₁ k₂))
    rw [hLcast] at hb
    calc 4 * (KE Λ : ℝ) * (2 : ℝ) ^ (cE * lmaxR l₁ l₂ k₁ k₂)
          * (Emax Λ * (2 : ℝ) ^ (-((2 : ℝ) ^ (lmaxR l₁ l₂ k₁ k₂ / (C₀ : ℝ))) + 2))
        = 4 * (KE Λ : ℝ) * Emax Λ * (2 : ℝ) ^ (cE * lmaxR l₁ l₂ k₁ k₂)
          * (2 : ℝ) ^ (-((2 : ℝ) ^ (lmaxR l₁ l₂ k₁ k₂ / (C₀ : ℝ))) + 2) := by ring
      _ ≤ Efun Λ := hb
  have hofReal : ENNReal.ofReal (4 * (KE Λ : ℝ) * (2 : ℝ) ^ (cE * lmaxR l₁ l₂ k₁ k₂)
        * (Emax Λ * (2 : ℝ) ^ (-((2 : ℝ) ^ (lmaxR l₁ l₂ k₁ k₂ / (C₀ : ℝ))) + 2)))
      = (4 : ENNReal) * (KE Λ : ENNReal) * ENNReal.ofReal ((2 : ℝ) ^ (cE * lmaxR l₁ l₂ k₁ k₂))
        * ENNReal.ofReal (Emax Λ
            * (2 : ℝ) ^ (-((2 : ℝ) ^ (lmaxR l₁ l₂ k₁ k₂ / (C₀ : ℝ))) + 2)) := by
    have harg : 4 * (KE Λ : ℝ) * (2 : ℝ) ^ (cE * lmaxR l₁ l₂ k₁ k₂)
          * (Emax Λ * (2 : ℝ) ^ (-((2 : ℝ) ^ (lmaxR l₁ l₂ k₁ k₂ / (C₀ : ℝ))) + 2))
        = ((4 : ℝ) * (KE Λ : ℝ)) * ((2 : ℝ) ^ (cE * lmaxR l₁ l₂ k₁ k₂)
          * (Emax Λ * (2 : ℝ) ^ (-((2 : ℝ) ^ (lmaxR l₁ l₂ k₁ k₂ / (C₀ : ℝ))) + 2))) := by
      ring
    rw [harg, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
      ENNReal.ofReal_mul (by positivity),
      show (4 : ENNReal) = ENNReal.ofReal (4 : ℝ) from by norm_num]
    rw [ENNReal.ofReal_coe_nnreal]
    ring
  -- the error bound
  have herr : MeasureTheory.eLpNorm (fun x : ℤ =>
        PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ =>
          mainPartTuple ρ P C₀ a f g l₁ l₂ k₁ k₂ n x
            - loModelTuple ρ P C₀ a f g l₁ l₂ k₁ k₂ n x))
      (p₁⁻¹ + p₂⁻¹)⁻¹ MeasureTheory.Measure.count
      ≤ ENNReal.ofReal (Efun Λ)
          * ENNReal.ofReal (lossWeight (max cE cM + 2) ρ l₁ l₂ k₁ k₂)
          * MeasureTheory.eLpNorm f p₁ MeasureTheory.Measure.count
          * MeasureTheory.eLpNorm g p₂ MeasureTheory.Measure.count := by
    refine hvar.trans ?_
    refine hstep.trans ?_
    refine (mul_le_mul' le_rfl hsum4).trans ?_
    have hZ1 : (1 : ENNReal) ≤
        ENNReal.ofReal (lossWeight (max cE cM + 2) ρ l₁ l₂ k₁ k₂) :=
      ENNReal.one_le_ofReal.mpr (one_le_lossWeight_L (by positivity) hρnn l₁ l₂ k₁ k₂)
    calc 4 * Xe * ENNReal.ofReal (Emax Λ
            * (2 : ℝ) ^ (-((2 : ℝ) ^ (lmaxR l₁ l₂ k₁ k₂ / (C₀ : ℝ))) + 2))
        = ((4 : ENNReal) * (KE Λ : ENNReal) * ENNReal.ofReal ((2 : ℝ) ^ (cE * lmaxR l₁ l₂ k₁ k₂))
            * ENNReal.ofReal (Emax Λ
                * (2 : ℝ) ^ (-((2 : ℝ) ^ (lmaxR l₁ l₂ k₁ k₂ / (C₀ : ℝ))) + 2)))
          * (MeasureTheory.eLpNorm f p₁ MeasureTheory.Measure.count
              * MeasureTheory.eLpNorm g p₂ MeasureTheory.Measure.count) := by
          rw [hXe]; ring
      _ = ENNReal.ofReal (4 * (KE Λ : ℝ) * (2 : ℝ) ^ (cE * lmaxR l₁ l₂ k₁ k₂)
            * (Emax Λ * (2 : ℝ) ^ (-((2 : ℝ) ^ (lmaxR l₁ l₂ k₁ k₂ / (C₀ : ℝ))) + 2)))
          * (MeasureTheory.eLpNorm f p₁ MeasureTheory.Measure.count
              * MeasureTheory.eLpNorm g p₂ MeasureTheory.Measure.count) := by rw [hofReal]
      _ ≤ ENNReal.ofReal (Efun Λ)
            * (MeasureTheory.eLpNorm f p₁ MeasureTheory.Measure.count
              * MeasureTheory.eLpNorm g p₂ MeasureTheory.Measure.count) :=
          mul_le_mul_of_le_left (ENNReal.ofReal_le_ofReal hreal) _
      _ = ENNReal.ofReal (Efun Λ)
            * (1 * (MeasureTheory.eLpNorm f p₁ MeasureTheory.Measure.count
                * MeasureTheory.eLpNorm g p₂ MeasureTheory.Measure.count)) := by rw [one_mul]
      _ ≤ ENNReal.ofReal (Efun Λ)
            * (ENNReal.ofReal (lossWeight (max cE cM + 2) ρ l₁ l₂ k₁ k₂)
              * (MeasureTheory.eLpNorm f p₁ MeasureTheory.Measure.count
                * MeasureTheory.eLpNorm g p₂ MeasureTheory.Measure.count)) :=
          mul_le_mul_of_le_right (mul_le_mul_of_le_left hZ1 _) _
      _ = ENNReal.ofReal (Efun Λ)
            * ENNReal.ofReal (lossWeight (max cE cM + 2) ρ l₁ l₂ k₁ k₂)
            * MeasureTheory.eLpNorm f p₁ MeasureTheory.Measure.count
            * MeasureTheory.eLpNorm g p₂ MeasureTheory.Measure.count := by ring
  -- the model part with the final weight
  have hmod' : MeasureTheory.eLpNorm (fun x : ℤ =>
        PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ =>
          loModelTuple ρ P C₀ a f g l₁ l₂ k₁ k₂ n x))
      (p₁⁻¹ + p₂⁻¹)⁻¹ MeasureTheory.Measure.count
      ≤ (KM Λ : ENNReal)
          * ENNReal.ofReal (lossWeight (max cE cM + 2) ρ l₁ l₂ k₁ k₂)
          * MeasureTheory.eLpNorm f p₁ MeasureTheory.Measure.count
          * MeasureTheory.eLpNorm g p₂ MeasureTheory.Measure.count := by
    refine hmod.trans ?_
    have hw : ENNReal.ofReal (lossWeight cM ρ l₁ l₂ k₁ k₂)
        ≤ ENNReal.ofReal (lossWeight (max cE cM + 2) ρ l₁ l₂ k₁ k₂) :=
      ofReal_lossWeight_mono_L hρnn (le_trans (le_max_right cE cM) (by linarith)) l₁ l₂ k₁ k₂
    exact mul_le_mul_of_le_left (mul_le_mul_of_le_left
      (mul_le_mul_of_le_right hw (KM Λ : ENNReal)) _) _
  -- combining the two parts
  refine (add_le_add herr hmod').trans ?_
  have hKfun : ENNReal.ofReal (Efun Λ) + (KM Λ : ENNReal)
      ≤ (loKcZ (Efun Λ + (KM Λ : ℝ)) (add_nonneg (hEfun0 Λ) (by positivity)) : ENNReal) := by
    conv_rhs => rw [← ENNReal.ofReal_coe_nnreal]
    show ENNReal.ofReal (Efun Λ) + (KM Λ : ENNReal) ≤ ENNReal.ofReal (Efun Λ + (KM Λ : ℝ))
    rw [ENNReal.ofReal_add (hEfun0 Λ) (by positivity), ENNReal.ofReal_coe_nnreal]
  calc ENNReal.ofReal (Efun Λ)
        * ENNReal.ofReal (lossWeight (max cE cM + 2) ρ l₁ l₂ k₁ k₂)
        * MeasureTheory.eLpNorm f p₁ MeasureTheory.Measure.count
        * MeasureTheory.eLpNorm g p₂ MeasureTheory.Measure.count
      + (KM Λ : ENNReal) * ENNReal.ofReal (lossWeight (max cE cM + 2) ρ l₁ l₂ k₁ k₂)
        * MeasureTheory.eLpNorm f p₁ MeasureTheory.Measure.count
        * MeasureTheory.eLpNorm g p₂ MeasureTheory.Measure.count
      = (ENNReal.ofReal (Efun Λ) + (KM Λ : ENNReal))
        * ENNReal.ofReal (lossWeight (max cE cM + 2) ρ l₁ l₂ k₁ k₂)
        * MeasureTheory.eLpNorm f p₁ MeasureTheory.Measure.count
        * MeasureTheory.eLpNorm g p₂ MeasureTheory.Measure.count := by ring
    _ ≤ (loKcZ (Efun Λ + (KM Λ : ℝ)) (add_nonneg (hEfun0 Λ) (by positivity)) : ENNReal)
        * ENNReal.ofReal (lossWeight (max cE cM + 2) ρ l₁ l₂ k₁ k₂)
        * MeasureTheory.eLpNorm f p₁ MeasureTheory.Measure.count
        * MeasureTheory.eLpNorm g p₂ MeasureTheory.Measure.count :=
        mul_le_mul_of_le_left (mul_le_mul_of_le_left (mul_le_mul_of_le_left hKfun _) _) _
theorem heightZeroZeroSmallRho (P : Polynomial ℤ) (hd : 2 ≤ P.natDegree) (r : NNReal)
    (hr : 2 < r) (C₀ : ℕ) (hC₀ : 1 ≤ C₀) (hA1 : Work.KMTContract.AreaA1) (B : ℕ) :
    ∃ c : ℝ, 0 ≤ c ∧ ∃ ρ₀ : ℝ, 0 < ρ₀ ∧
      ∀ ρ : ℝ, 0 < ρ → ρ ≤ ρ₀ → ∃ K : NNReal → NNReal,
        ∀ (a : ℕ → NNReal) (Λ : NNReal) (k₁ k₂ : ℕ) (f g : ℤ → ℂ),
          1 < Λ → PointwiseErgodicTheorems.Lacunary Λ a → (∀ m, 1 ≤ a m) →
          Work.KMTPlan.A6.lcL 0 0 k₁ k₂ ≤ B → (k₁ = 0 ∨ k₂ = 0) →
          MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
              (fun n : ℕ => Work.KMTAreas.A7.mainPartTuple ρ P C₀ a f g 0 0 k₁ k₂ n x))
            1 MeasureTheory.Measure.count
            ≤ (K Λ : ENNReal) * ENNReal.ofReal (Work.KMTAreas.A7.lossWeight c ρ 0 0 k₁ k₂)
                * MeasureTheory.eLpNorm f 2 MeasureTheory.Measure.count
                * MeasureTheory.eLpNorm g 2 MeasureTheory.Measure.count := by
  -- the Hölder exponent at `p₁ = p₂ = 2` is admissible
  have hsum2 : ((2 : ENNReal)⁻¹ + (2 : ENNReal)⁻¹) ≤ 1 := by
    rw [ENNReal.inv_two_add_inv_two]
  -- the `(0,0)` model approximation at the exponents `(2,2)`
  obtain ⟨c, hc, ρ₀, hρ₀, hK⟩ :=
    modelApproxZeroZeroZ P 2 2 hd hA1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      hsum2
      (LoErrSingleScale00 P 2 2 hd hA1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        hsum2)
      (LoModelLargeScaleHolds P 2 2 hd hA1 (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) hsum2)
      C₀ r hC₀ hr
  refine ⟨c, hc, ρ₀, hρ₀, ?_⟩
  intro ρ hρ hρle
  obtain ⟨K, hK'⟩ := hK ρ hρ hρle
  refine ⟨K, ?_⟩
  intro a Λ k₁ k₂ f g hΛ ha ha1 _hB _hQ
  have h := hK' a Λ 0 0 k₁ k₂ f g hΛ ha ha1 ⟨rfl, rfl⟩
  -- the exponent `(2⁻¹ + 2⁻¹)⁻¹` is `1`
  have hexp : ((2 : ENNReal)⁻¹ + (2 : ENNReal)⁻¹)⁻¹ = 1 := by
    rw [ENNReal.inv_two_add_inv_two, inv_one]
  rw [hexp] at h
  -- the model tuple vanishes at arithmetic height `0`
  have hpt : ∀ x : ℤ, PointwiseErgodicTheorems.variationalNorm r
        (fun n : ℕ => Work.KMTAreas.A7.mainPartTuple ρ P C₀ a f g 0 0 k₁ k₂ n x)
      = PointwiseErgodicTheorems.variationalNorm r
        (fun n : ℕ => Work.KMTAreas.A7.mainPartTuple ρ P C₀ a f g 0 0 k₁ k₂ n x
          - Work.KMTAreas.A7.modelTuple ρ P C₀ a f g 0 0 k₁ k₂ n x) := by
    intro x
    refine congrArg (fun u : ℕ → ℂ =>
      PointwiseErgodicTheorems.variationalNorm r u) ?_
    funext n
    rw [Work.KMTAreas.A7.modelTuple_apply_eq_zero_of_lo ρ P C₀ a f g 0 0 k₁ k₂ n x
      (by omega), sub_zero]
  have heq : MeasureTheory.eLpNorm (fun x : ℤ =>
        PointwiseErgodicTheorems.variationalNorm r
          (fun n : ℕ => Work.KMTAreas.A7.mainPartTuple ρ P C₀ a f g 0 0 k₁ k₂ n x))
      1 MeasureTheory.Measure.count
      = MeasureTheory.eLpNorm (fun x : ℤ =>
        PointwiseErgodicTheorems.variationalNorm r
          (fun n : ℕ => Work.KMTAreas.A7.mainPartTuple ρ P C₀ a f g 0 0 k₁ k₂ n x
            - Work.KMTAreas.A7.modelTuple ρ P C₀ a f g 0 0 k₁ k₂ n x))
      1 MeasureTheory.Measure.count := by
    refine congrArg (fun u : ℤ → ENNReal =>
      MeasureTheory.eLpNorm u 1 MeasureTheory.Measure.count) ?_
    funext x
    exact hpt x
  rw [heq]
  exact h

end

end Work.PieceBoundedH
