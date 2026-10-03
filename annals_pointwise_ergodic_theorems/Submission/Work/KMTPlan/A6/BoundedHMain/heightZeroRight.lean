import Mathlib
import Submission.Work.KMTPlan.A6.BoundedHMain.Defs
import Submission.Work.KMTAreas.A7.LoMixedWinDefs
import Submission.Work.KMTAreas.A7.LpSymDMass
import Submission.Work.KMTPlan.A6.LowModApproxBoundedH.plainVarF_lev0
import Submission.Work.KMTPlan.A6.LowModApproxBoundedH.plainVarG_lev0
import Submission.Work.KMTPlan.A6.BoundedHMain.loMixedRSingleScaleUncond

namespace Work.KMTPlan.A6.BoundedHMain

open MeasureTheory
open scoped ENNReal NNReal BigOperators
open PointwiseErgodicTheorems Submission.PointwiseErgodicTheorems

noncomputable section

/-! ## The bounded-height parts of the proof of `heightZeroRight`

`heightZeroRight` is the `l₂ = 0`, `1 ≤ l₁` half of the bounded-height (`lcL l₁ 0 k₁ k₂ ≤ B`)
estimate for the concrete §5 columns `mainPartTuple`.  On this range the exact-height model
`modelTuple` (and the repaired model `modelTupleRep`) vanishes identically, so the estimate is a
direct one for the concrete column, and it is available for `0 < ρ ≤ 1` in the single-scale form

  `‖mainPartTuple ρ … l₁ 0 k₁ k₂ n‖_{ℓ^p} ≤ C(Λ) · modelWeight A ρ l₁ 0 k₁ k₂ · ⌊a n⌋⁻¹ ‖f‖‖g‖`

(the `A1`-free version `Work.KMTPlan.A6.BoundedHMain.loMixedRSingleScaleUncond`, proved from the
`ℓ¹(ℤ²)` mass bound `Work.KMTAreas.A7.LoMixedRMass`).

Two elementary steps turn it into the variational estimate of the target:

* at bounded height the weight `modelWeight A ρ l₁ 0 k₁ k₂` is a *constant* depending only on
  `ρ, B` (`modelWeight_le_of_lcL_le` below), so no lacunary weight absorption is needed;
* the variational norm of a family is dominated by the sum of the norms of its members
  (`Work.KMTAreas.A7.VarNormTsumLp`), and the reciprocal lacunary sum `∑ₙ ⌊a n⌋⁻¹` is finite
  (`Work.KMTAreas.A7.invFloor_tsum_le`) — no index-set restriction is needed, because the
  single-scale bound holds for *every* scale. -/

/-- `lmaxR l₁ l₂ k₁ k₂` is the cast of `lcL l₁ l₂ k₁ k₂`. -/
lemma lmaxR_eq_lcL (l₁ l₂ k₁ k₂ : ℕ) :
    Work.KMTAreas.A7.lmaxR l₁ l₂ k₁ k₂ = (Work.KMTPlan.A6.lcL l₁ l₂ k₁ k₂ : ℝ) := by
  rw [Work.KMTAreas.A7.lmaxR, ← Work.KMTPlan.A6.lcL_eq]
  norm_cast

/-- `modelWeight` depends on the quadruple only through `lcL`. -/
lemma modelWeight_eq_lcL (A ρ : ℝ) (l₁ l₂ k₁ k₂ : ℕ) :
    Work.KMTAreas.A7.modelWeight A ρ l₁ l₂ k₁ k₂
      = Work.KMTAreas.A7.modelWeight A ρ (Work.KMTPlan.A6.lcL l₁ l₂ k₁ k₂)
          (Work.KMTPlan.A6.lcL l₁ l₂ k₁ k₂) (Work.KMTPlan.A6.lcL l₁ l₂ k₁ k₂)
          (Work.KMTPlan.A6.lcL l₁ l₂ k₁ k₂) := by
  simp only [Work.KMTAreas.A7.modelWeight, lmaxR_eq_lcL, Work.KMTPlan.A6.lcL, max_self]

/-- `lmaxR L L L L = L`. -/
lemma lmaxR_diag (L : ℕ) : Work.KMTAreas.A7.lmaxR L L L L = (L : ℝ) := by
  rw [lmaxR_eq_lcL]
  simp [Work.KMTPlan.A6.lcL]

/-- `modelWeight A ρ L L L L` is monotone in `L` for `A ≥ 0`, `ρ ≥ 0`. -/
lemma modelWeight_diag_mono (A ρ : ℝ) (hA : 0 ≤ A) (hρ : 0 ≤ ρ) :
    Monotone (fun L : ℕ => Work.KMTAreas.A7.modelWeight A ρ L L L L) := by
  intro L M hLM
  have h1 : (L : ℝ) ≤ (M : ℝ) := by exact_mod_cast hLM
  simp only [Work.KMTAreas.A7.modelWeight, lmaxR_diag]
  refine mul_le_mul (Real.rpow_le_rpow (by linarith) (by linarith) hA) ?_
    (Real.rpow_nonneg (by norm_num) _) (Real.rpow_nonneg (by linarith) A)
  refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
  refine mul_le_mul_of_nonneg_left ?_ hA
  exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by nlinarith)

/-- **The `§6` weight at bounded height is a constant.**  For `A ≥ 0` and `ρ ≥ 0`,
`lcL l₁ l₂ k₁ k₂ ≤ B` bounds `modelWeight A ρ l₁ l₂ k₁ k₂` by the diagonal value at `B`. -/
lemma modelWeight_le_of_lcL_le (A ρ : ℝ) (hA : 0 ≤ A) (hρ : 0 ≤ ρ)
    {l₁ l₂ k₁ k₂ B : ℕ} (h : Work.KMTPlan.A6.lcL l₁ l₂ k₁ k₂ ≤ B) :
    Work.KMTAreas.A7.modelWeight A ρ l₁ l₂ k₁ k₂
      ≤ Work.KMTAreas.A7.modelWeight A ρ B B B B := by
  rw [modelWeight_eq_lcL]
  exact modelWeight_diag_mono A ρ hA hρ h

/-- **The assembly of `heightZeroRight`** from the (`A1`-free) single-scale estimate
`loMixedRSingleScaleUncond` at the exponents `(2,2)`. -/
theorem heightZeroRight_aux (P : Polynomial ℤ) (hd : 2 ≤ P.natDegree)
    (hsingle : ∀ (p₁ p₂ : ENNReal) (hdeg : 2 ≤ P.natDegree) (hp₁ : 1 < p₁) (htp₁ : p₁ < ⊤)
      (hp₂ : 1 < p₂) (htp₂ : p₂ < ⊤), p₁⁻¹ + p₂⁻¹ ≤ 1 →
      ∃ A : ℝ, 0 ≤ A ∧
        ∀ (C₀ : ℕ), 1 ≤ C₀ → ∀ (ρ : ℝ), 0 < ρ → ρ ≤ 1 → ∃ C : NNReal → NNReal,
          ∀ (a : ℕ → NNReal) (Λ : NNReal) (l₁ k₁ k₂ : ℕ) (f g : ℤ → ℂ),
            1 < Λ → PointwiseErgodicTheorems.Lacunary Λ a → (∀ n, 1 ≤ a n) →
            1 ≤ l₁ → ∀ n : ℕ,
            MeasureTheory.eLpNorm (fun x : ℤ =>
                Work.KMTAreas.A7.mainPartTuple ρ P C₀ a f g l₁ 0 k₁ k₂ n x)
              (p₁⁻¹ + p₂⁻¹)⁻¹ MeasureTheory.Measure.count
            ≤ (C Λ : ENNReal) * ENNReal.ofReal (Work.KMTAreas.A7.modelWeight A ρ l₁ 0 k₁ k₂)
                * ENNReal.ofReal ((((Nat.floor (a n) : ℕ)) : ℝ)⁻¹)
                * MeasureTheory.eLpNorm f p₁ MeasureTheory.Measure.count
                * MeasureTheory.eLpNorm g p₂ MeasureTheory.Measure.count)
    (r : NNReal) (hr : 2 < r) (C₀ : ℕ) (hC₀ : 1 ≤ C₀) (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (B : ℕ) :
    ∃ K : NNReal → NNReal,
      ∀ (a : ℕ → NNReal) (Λ : NNReal) (l₁ k₁ k₂ : ℕ) (f g : ℤ → ℂ),
        1 < Λ → PointwiseErgodicTheorems.Lacunary Λ a → (∀ m, 1 ≤ a m) →
        Work.KMTPlan.A6.lcL l₁ 0 k₁ k₂ ≤ B → (k₁ = 0 ∨ k₂ = 0) → 1 ≤ l₁ →
        MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
            (fun n : ℕ => Work.KMTAreas.A7.mainPartTuple ρ P C₀ a f g l₁ 0 k₁ k₂ n x))
          1 MeasureTheory.Measure.count
          ≤ (K Λ : ENNReal) * MeasureTheory.eLpNorm f 2 MeasureTheory.Measure.count
              * MeasureTheory.eLpNorm g 2 MeasureTheory.Measure.count := by
  classical
  obtain ⟨A, hA0, hcore⟩ :=
    hsingle 2 2 hd (by norm_num) (by simp) (by norm_num) (by simp)
      (le_of_eq ENNReal.inv_two_add_inv_two)
  obtain ⟨C, hC⟩ := hcore C₀ hC₀ ρ hρ hρ1
  -- the bounded weight
  set W : ℝ := Work.KMTAreas.A7.modelWeight A ρ B B B B with hWdef
  have hW1 : 1 ≤ W := by
    rw [hWdef, Work.KMTAreas.A7.modelWeight]
    exact one_le_mul_of_one_le_of_one_le
      (Real.one_le_rpow (by linarith [Work.KMTAreas.A7.lmaxR_nonneg B B B B]) hA0)
      (Real.one_le_rpow (by norm_num) (by positivity))
  have hWnn : 0 ≤ W := le_trans zero_le_one hW1
  -- the lacunary reciprocal sum constant
  set CTf : NNReal → ℝ := fun Λ =>
    if h : 1 < Λ then Classical.choose (Work.KMTAreas.A7.invFloor_tsum_le Λ h) else 0 with hCTf
  have hCTf0 : ∀ Λ : NNReal, 0 ≤ CTf Λ := by
    intro Λ
    by_cases h : 1 < Λ
    · rw [hCTf]; simp only [dif_pos h]
      exact (Classical.choose_spec (Work.KMTAreas.A7.invFloor_tsum_le Λ h)).1
    · rw [hCTf]; simp [h]
  have hCTfb : ∀ (Λ : NNReal), 1 < Λ → ∀ (a : ℕ → NNReal),
      PointwiseErgodicTheorems.Lacunary Λ a → (∀ n, 1 ≤ a n) →
      Summable (fun n : ℕ => (((Nat.floor (a n) : ℕ) : ℝ))⁻¹) ∧
      (∑' n : ℕ, (((Nat.floor (a n) : ℕ) : ℝ))⁻¹) ≤ CTf Λ := by
    intro Λ hΛ a ha ha1
    rw [hCTf]; simp only [dif_pos hΛ]
    exact (Classical.choose_spec (Work.KMTAreas.A7.invFloor_tsum_le Λ hΛ)).2 a ha ha1
  refine ⟨fun Λ => 4 * C Λ * Real.toNNReal W * Real.toNNReal (CTf Λ), ?_⟩
  intro a Λ l₁ k₁ k₂ f g hΛ ha ha1 hlcL _hk hl₁
  have hr1 : (1 : NNReal) ≤ r := le_of_lt (lt_trans (by norm_num) hr)
  set A₁ : ENNReal := MeasureTheory.eLpNorm f 2 MeasureTheory.Measure.count with hA₁
  set B₁ : ENNReal := MeasureTheory.eLpNorm g 2 MeasureTheory.Measure.count with hB₁
  set c₀ : ENNReal := (C Λ : ENNReal) * ENNReal.ofReal W * A₁ * B₁ with hc₀
  -- the weight is bounded by the constant `W`
  have hmw : ENNReal.ofReal (Work.KMTAreas.A7.modelWeight A ρ l₁ 0 k₁ k₂)
      ≤ ENNReal.ofReal W := by
    refine ENNReal.ofReal_le_ofReal ?_
    rw [hWdef]
    exact modelWeight_le_of_lcL_le A ρ hA0 hρ.le hlcL
  -- the pointwise single-scale bounds, with the constant weight
  have hsingle_le : ∀ n : ℕ,
      MeasureTheory.eLpNorm (fun x : ℤ =>
          Work.KMTAreas.A7.mainPartTuple ρ P C₀ a f g l₁ 0 k₁ k₂ n x)
        1 MeasureTheory.Measure.count
        ≤ c₀ * ENNReal.ofReal ((((Nat.floor (a n) : ℕ)) : ℝ)⁻¹) := by
    intro n
    have hC1 : MeasureTheory.eLpNorm (fun x : ℤ =>
          Work.KMTAreas.A7.mainPartTuple ρ P C₀ a f g l₁ 0 k₁ k₂ n x)
        1 MeasureTheory.Measure.count
        ≤ (C Λ : ENNReal) * ENNReal.ofReal (Work.KMTAreas.A7.modelWeight A ρ l₁ 0 k₁ k₂)
            * ENNReal.ofReal ((((Nat.floor (a n) : ℕ)) : ℝ)⁻¹)
            * MeasureTheory.eLpNorm f 2 MeasureTheory.Measure.count
            * MeasureTheory.eLpNorm g 2 MeasureTheory.Measure.count := by
      simpa [ENNReal.inv_two_add_inv_two] using hC a Λ l₁ k₁ k₂ f g hΛ ha ha1 hl₁ n
    refine hC1.trans ?_
    have hstep : (C Λ : ENNReal)
          * ENNReal.ofReal (Work.KMTAreas.A7.modelWeight A ρ l₁ 0 k₁ k₂)
          * ENNReal.ofReal ((((Nat.floor (a n) : ℕ)) : ℝ)⁻¹) * A₁ * B₁
        ≤ c₀ * ENNReal.ofReal ((((Nat.floor (a n) : ℕ)) : ℝ)⁻¹) := by
      have h1 : (C Λ : ENNReal)
          * ENNReal.ofReal (Work.KMTAreas.A7.modelWeight A ρ l₁ 0 k₁ k₂)
          ≤ (C Λ : ENNReal) * ENNReal.ofReal W := mul_le_mul' le_rfl hmw
      calc (C Λ : ENNReal)
            * ENNReal.ofReal (Work.KMTAreas.A7.modelWeight A ρ l₁ 0 k₁ k₂)
            * ENNReal.ofReal ((((Nat.floor (a n) : ℕ)) : ℝ)⁻¹) * A₁ * B₁
          = ((C Λ : ENNReal)
              * ENNReal.ofReal (Work.KMTAreas.A7.modelWeight A ρ l₁ 0 k₁ k₂)
              * A₁ * B₁) * ENNReal.ofReal ((((Nat.floor (a n) : ℕ)) : ℝ)⁻¹) := by ring
        _ ≤ (((C Λ : ENNReal) * ENNReal.ofReal W) * A₁ * B₁)
              * ENNReal.ofReal ((((Nat.floor (a n) : ℕ)) : ℝ)⁻¹) := by
            exact mul_le_mul' (mul_le_mul' (mul_le_mul' h1 le_rfl) le_rfl) le_rfl
        _ = c₀ * ENNReal.ofReal ((((Nat.floor (a n) : ℕ)) : ℝ)⁻¹) := by rw [hc₀]
    exact hstep
  -- the variational norm through `VarNormTsumLp`
  have hmain := Work.KMTAreas.A7.VarNormTsumLp (r := r) hr1 (p := 1) (by norm_num)
    (fun n x => Work.KMTAreas.A7.mainPartTuple ρ P C₀ a f g l₁ 0 k₁ k₂ n x)
  refine hmain.trans ?_
  obtain ⟨hsumm, hsumle⟩ := hCTfb Λ hΛ a ha ha1
  -- the lacunary sum of the single-scale bounds
  have hstep1 : (∑' n : ℕ, 4 * MeasureTheory.eLpNorm (fun x : ℤ =>
        Work.KMTAreas.A7.mainPartTuple ρ P C₀ a f g l₁ 0 k₁ k₂ n x)
        1 MeasureTheory.Measure.count)
      ≤ 4 * c₀ * (∑' n : ℕ, ENNReal.ofReal ((((Nat.floor (a n) : ℕ)) : ℝ)⁻¹)) := by
    calc (∑' n : ℕ, 4 * MeasureTheory.eLpNorm (fun x : ℤ =>
          Work.KMTAreas.A7.mainPartTuple ρ P C₀ a f g l₁ 0 k₁ k₂ n x)
          1 MeasureTheory.Measure.count)
        ≤ ∑' n : ℕ, 4 * (c₀ * ENNReal.ofReal ((((Nat.floor (a n) : ℕ)) : ℝ)⁻¹)) :=
          ENNReal.tsum_le_tsum (fun n => mul_le_mul' le_rfl (hsingle_le n))
      _ = (4 * c₀) * (∑' n : ℕ, ENNReal.ofReal ((((Nat.floor (a n) : ℕ)) : ℝ)⁻¹)) := by
          rw [← ENNReal.tsum_mul_left]
          exact tsum_congr (fun n => by ring)
      _ = 4 * c₀ * (∑' n : ℕ, ENNReal.ofReal ((((Nat.floor (a n) : ℕ)) : ℝ)⁻¹)) := by
          ring
  -- the sum of the reciprocals is finite and bounded by `CTf Λ`
  have hstep2 : (∑' n : ℕ, ENNReal.ofReal ((((Nat.floor (a n) : ℕ)) : ℝ)⁻¹))
      ≤ ENNReal.ofReal (CTf Λ) := by
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => by positivity) hsumm]
    exact ENNReal.ofReal_le_ofReal hsumle
  refine hstep1.trans ?_
  have hfinal : 4 * c₀ * ENNReal.ofReal (CTf Λ)
      = ((4 * C Λ * Real.toNNReal W * Real.toNNReal (CTf Λ) : NNReal) : ENNReal) * A₁ * B₁ := by
    rw [hc₀, ENNReal.coe_mul, ENNReal.coe_mul, ENNReal.coe_mul, ENNReal.coe_ofNat,
      ENNReal.ofNNReal_toNNReal, ENNReal.ofNNReal_toNNReal]
    ring
  refine (mul_le_mul' le_rfl hstep2).trans ?_
  exact le_of_eq hfinal

theorem heightZeroRight (P : Polynomial ℤ) (hd : 2 ≤ P.natDegree) (r : NNReal) (hr : 2 < r)
    (C₀ : ℕ) (hC₀ : 1 ≤ C₀) (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (B : ℕ) :
    ∃ K : NNReal → NNReal,
      ∀ (a : ℕ → NNReal) (Λ : NNReal) (l₁ k₁ k₂ : ℕ) (f g : ℤ → ℂ),
        1 < Λ → PointwiseErgodicTheorems.Lacunary Λ a → (∀ m, 1 ≤ a m) →
        Work.KMTPlan.A6.lcL l₁ 0 k₁ k₂ ≤ B → (k₁ = 0 ∨ k₂ = 0) → 1 ≤ l₁ →
        MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
            (fun n : ℕ => Work.KMTAreas.A7.mainPartTuple ρ P C₀ a f g l₁ 0 k₁ k₂ n x))
          1 MeasureTheory.Measure.count
          ≤ (K Λ : ENNReal) * MeasureTheory.eLpNorm f 2 MeasureTheory.Measure.count
              * MeasureTheory.eLpNorm g 2 MeasureTheory.Measure.count :=
  heightZeroRight_aux P hd (loMixedRSingleScaleUncond P) r hr C₀ hC₀ ρ hρ hρ1 B

end

end Work.KMTPlan.A6.BoundedHMain
