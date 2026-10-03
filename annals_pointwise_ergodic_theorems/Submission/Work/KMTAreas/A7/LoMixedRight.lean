/-
# The mixed case `l₁ ≥ 1`, `l₂ = 0` of the `l = 0` model approximation (Area A7)

The target is `Work.KMTAreas.A7.LoMixedRightStatement P p₁ p₂` (see
`Submission/Work/KMTAreas/A7/LoDefs.lean`): the variational estimate

  `‖ V^r (mainPartTuple − modelTuple) ‖_{ℓ^p} ≤ K(Λ) · lossWeight c ρ l₁ 0 k₁ k₂ ·
      ‖f‖_{ℓ^{p₁}} ‖g‖_{ℓ^{p₂}}`,   `p = (p₁⁻¹+p₂⁻¹)⁻¹`,

restricted to the quadruples with `1 ≤ l₁` and `l₂ = 0`.

## The two halves of the proof

* **The exact-height model vanishes.**  `iwArithFreqsNew ρ 0 = ∅`, hence `Tex ρ 0 = 0`, hence
  `modelTuple ρ P C₀ a f g l₁ 0 k₁ k₂ = 0` (`LoDefs.modelTuple_eq_zero_of_lo`).  The target is
  therefore an estimate for the concrete column `mainPartTuple` alone.
* **The lacunary assembly.**  The passage from the single-scale bound
  `LoMixedRSingleScaleStatement` (`Submission/Work/KMTAreas/A7/LoMixedRDefs.lean`) to the
  variational bound is the §5 bookkeeping already used by
  `Work.KMTAreas.A7.ModelApproxHelpers.modelApprox_of_inputs`: the variational norm is bounded by
  the `ℓ¹`-sum of the single-scale norms (`VarNormTsumLp`), the sum over the lacunary scales is
  restricted to the index set and bounded by the doubly exponentially small quantity
  `D(Λ)·2^{-2^{L/C₀}+2}` (`invFloorSum_le`), and — this is the point where the mixed case differs
  from the `(0,0)` case — the *whole* product `modelWeight A ρ L · 2^{-2^{L/C₀}+2}` is bounded by
  a constant `B(ρ,A,C₀,Λ)`, because the single-scale exponent `A` may depend on `ρ` and hence
  `lossWeight c ρ L` cannot carry it.  The bound is
  `modelWeight_mul_two_rpow_neg_bounded` below: since `ρ ≤ 1/(4C₀)`, `2^{ρL} ≤ 2^{L/(4C₀)}`, and
  `(1+L)^A ≤ Cd(ρ)·2^{ρL}` (`Work.KMTAreas.A7.rpow_poly_le_const_exp`), so that the exponent
  `log₂(2^{ρL}) + A 2^{ρL} - 2^{L/C₀} + 2` is bounded above by `K·K^{1/3}+2` with
  `K = A + 1/log 2` (`Work.KMTAreas.A7.weightArith_rpowCore`).  The constant is then absorbed by
  the `K(Λ)` of the target.

The single-scale input is proved separately
(`Submission/Work/KMTAreas/A7/LoMixedRSingleScale.lean`).
-/
import Mathlib
import Submission.Work.KMTAreas.A7.WeightArith
import Submission.Work.KMTAreas.A7.LoMixedRMass
import Submission.Work.KMTAreas.A7.LoMixedRSingleScaleOfMass
import Submission.Work.KMTPlan.A6.KernComp_khalf_eq
import Submission.Work.KMTPlan.A6.SymToolbox_tsum_coeff2_le

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace Work.KMTAreas.A7

noncomputable section

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal BigOperators
open PointwiseErgodicTheorems Submission.PointwiseErgodicTheorems
open Work.Analysis.EndVar Work.KMTContract

/-! ## The weight arithmetic: the product with the doubly exponential decay is bounded -/

/-- `lmaxR L L L L = L`. -/
lemma lmaxR_diag (L : ℕ) : lmaxR L L L L = (L : ℝ) := by
  rw [lmaxR, Work.Analysis.EndVar.lmax]
  simp

/-- **The model weight times the doubly exponential lacunary decay is bounded.**

For `A ≥ 0`, `0 < ρ ≤ 1/(4C₀)` and `D ≥ 0` there is `B ≥ 0` with, for every scale `L`,

  `D · modelWeight A ρ L L L L · 2^{-2^{L/C₀}+2} ≤ B`.

This is the absorption step specific to the mixed case: the single-scale exponent `A` of
`LoMixedRSingleScaleStatement` may depend on `ρ`, so `lossWeight c ρ L` (whose exponent `c` is
fixed before `ρ` in `LoCase`) cannot carry it; instead the whole product is a *constant* which the
target's `K(Λ)` absorbs.  The proof uses `(1+L)^A ≤ Cd·2^{ρL}` (`rpow_poly_le_const_exp`), the
inequality `ρL ≤ (1/log 2)·2^{ρL}` (from `log y ≤ y-1` with `y = 2^{ρL}`), the comparison
`2^{L/C₀} ≥ (2^{ρL})^4` (from `4ρL ≤ L/C₀`), and finally
`K·2^{ρL} - (2^{ρL})^4 ≤ K·K^{1/3}` (`weightArith_rpowCore`) with `K = A + 1/log 2`. -/
lemma modelWeight_mul_two_rpow_neg_bounded (A ρ D : ℝ) (hA : 0 ≤ A) (hρ : 0 < ρ) (hD : 0 ≤ D)
    (C₀ : ℕ) (hC₀ : 1 ≤ C₀) (hρle : ρ ≤ 1 / (4 * (C₀ : ℝ))) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ L : ℕ,
      D * modelWeight A ρ L L L L * (2 : ℝ) ^ (-((2 : ℝ) ^ ((L : ℝ) / (C₀ : ℝ))) + 2) ≤ B := by
  obtain ⟨Cd, hCd1, hCd⟩ := rpow_poly_le_const_exp A ρ hA hρ
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hC0pos : (0 : ℝ) < (C₀ : ℝ) := by
    have h : (1 : ℝ) ≤ (C₀ : ℝ) := by exact_mod_cast hC₀
    linarith
  set K₁ : ℝ := 1 / Real.log 2 with hK₁
  set K : ℝ := A + K₁ with hK
  have hK0 : 0 ≤ K := by rw [hK, hK₁]; positivity
  set Bc : ℝ := D * Cd * (2 : ℝ) ^ (K * K ^ ((1 : ℝ) / 3) + 2) with hBc
  have hBc0 : 0 ≤ Bc := by rw [hBc]; positivity
  refine ⟨max Bc 0, le_max_right _ _, fun L => ?_⟩
  have hL0 : (0 : ℝ) ≤ (L : ℝ) := Nat.cast_nonneg L
  have hlmax : modelWeight A ρ L L L L
      = (1 + (L : ℝ)) ^ A * (2 : ℝ) ^ (A * (2 : ℝ) ^ (ρ * (L : ℝ))) := by
    rw [modelWeight, lmaxR_diag]
  rw [hlmax]
  set y : ℝ := (2 : ℝ) ^ (ρ * (L : ℝ)) with hy
  have hypos : 0 < y := Real.rpow_pos_of_pos (by norm_num) _
  have hlogy : Real.log y = ρ * (L : ℝ) * Real.log 2 := by
    rw [hy, Real.log_rpow (by norm_num)]
  have hsy : ρ * (L : ℝ) * Real.log 2 ≤ y := by
    have h1 : Real.log y ≤ y - 1 := Real.log_le_sub_one_of_pos hypos
    rw [hlogy] at h1; linarith
  have hyK₁ : y ≤ (2 : ℝ) ^ (K₁ * y) := by
    have h3 : ρ * (L : ℝ) ≤ K₁ * y := by
      have h : ρ * (L : ℝ) ≤ y / Real.log 2 := by rw [le_div_iff₀ hlog2]; linarith
      rw [hK₁]
      calc ρ * (L : ℝ) ≤ y / Real.log 2 := h
        _ = (1 / Real.log 2) * y := by ring
    calc y = (2 : ℝ) ^ (ρ * (L : ℝ)) := hy.symm
      _ ≤ (2 : ℝ) ^ (K₁ * y) := Real.rpow_le_rpow_of_exponent_le (by norm_num) h3
  have hy4 : y ^ (4 : ℝ) = (2 : ℝ) ^ (4 * (ρ * (L : ℝ))) := by
    rw [hy, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    congr 1; ring
  have h4r : 4 * (ρ * (L : ℝ)) ≤ (L : ℝ) / (C₀ : ℝ) := by
    have h4 : 4 * ρ ≤ 1 / (C₀ : ℝ) := by
      have h := mul_le_mul_of_nonneg_left hρle (show (0 : ℝ) ≤ 4 by norm_num)
      have he : 4 * (1 / (4 * (C₀ : ℝ))) = 1 / (C₀ : ℝ) := by field_simp
      rwa [he] at h
    have h := mul_le_mul_of_nonneg_right h4 hL0
    have he : 4 * ρ * (L : ℝ) = 4 * (ρ * (L : ℝ)) := by ring
    have he2 : 1 / (C₀ : ℝ) * (L : ℝ) = (L : ℝ) / (C₀ : ℝ) := by ring
    rw [he, he2] at h
    exact h
  have hxd : (2 : ℝ) ^ (-((2 : ℝ) ^ ((L : ℝ) / (C₀ : ℝ))) + 2)
      ≤ (2 : ℝ) ^ (-(y ^ (4 : ℝ)) + 2) := by
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    have h1 : y ^ (4 : ℝ) ≤ (2 : ℝ) ^ ((L : ℝ) / (C₀ : ℝ)) := by
      rw [hy4]; exact Real.rpow_le_rpow_of_exponent_le (by norm_num) h4r
    linarith
  have hcore0 := weightArith_rpowCore K (ρ * (L : ℝ)) hK0
  have hcore : K * y - y ^ (4 : ℝ) ≤ K * K ^ ((1 : ℝ) / 3) := by
    rw [hy.symm, ← hy4] at hcore0
    exact hcore0
  have hCd' : (1 + (L : ℝ)) ^ A ≤ Cd * y := by
    have h := hCd L
    rwa [← hy] at h
  have hexp : (1 + (L : ℝ)) ^ A * (2 : ℝ) ^ (A * y) * (2 : ℝ) ^ (-(y ^ (4 : ℝ)) + 2)
      ≤ Cd * (2 : ℝ) ^ (K * K ^ ((1 : ℝ) / 3) + 2) := by
    have h1 : (1 + (L : ℝ)) ^ A * (2 : ℝ) ^ (A * y) * (2 : ℝ) ^ (-(y ^ (4 : ℝ)) + 2)
        ≤ (Cd * y) * (2 : ℝ) ^ (A * y) * (2 : ℝ) ^ (-(y ^ (4 : ℝ)) + 2) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCd' (by positivity)) (by positivity)
    refine h1.trans ?_
    have h2 : (Cd * y) * (2 : ℝ) ^ (A * y) * (2 : ℝ) ^ (-(y ^ (4 : ℝ)) + 2)
        = Cd * (y * (2 : ℝ) ^ (A * y) * (2 : ℝ) ^ (-(y ^ (4 : ℝ)) + 2)) := by ring
    rw [h2]
    have h3 : y * (2 : ℝ) ^ (A * y) * (2 : ℝ) ^ (-(y ^ (4 : ℝ)) + 2)
        ≤ (2 : ℝ) ^ (K₁ * y) * (2 : ℝ) ^ (A * y) * (2 : ℝ) ^ (-(y ^ (4 : ℝ)) + 2) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hyK₁ (by positivity)) (by positivity)
    have h4 : (2 : ℝ) ^ (K₁ * y) * (2 : ℝ) ^ (A * y) = (2 : ℝ) ^ (K₁ * y + A * y) :=
      (Real.rpow_add (by norm_num : (0 : ℝ) < 2) _ _).symm
    have h5 : (2 : ℝ) ^ (K₁ * y + A * y) * (2 : ℝ) ^ (-(y ^ (4 : ℝ)) + 2)
        = (2 : ℝ) ^ ((K₁ * y + A * y) + (-(y ^ (4 : ℝ)) + 2)) :=
      (Real.rpow_add (by norm_num : (0 : ℝ) < 2) _ _).symm
    have h6 : (K₁ * y + A * y) + (-(y ^ (4 : ℝ)) + 2) ≤ K * K ^ ((1 : ℝ) / 3) + 2 := by
      have h7 : K₁ * y + A * y = K * y := by rw [hK]; ring
      rw [h7]; linarith [hcore]
    refine (mul_le_mul_of_nonneg_left h3 (by positivity)).trans ?_
    rw [h4, h5]
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le (by norm_num) h6) (by positivity)
  have hfinal : D * ((1 + (L : ℝ)) ^ A * (2 : ℝ) ^ (A * y)
      * (2 : ℝ) ^ (-(y ^ (4 : ℝ)) + 2)) ≤ Bc := by
    refine (mul_le_mul_of_nonneg_left hexp hD).trans ?_
    rw [hBc]
    exact le_of_eq (by ring)
  calc D * ((1 + (L : ℝ)) ^ A * (2 : ℝ) ^ (A * y))
        * (2 : ℝ) ^ (-((2 : ℝ) ^ ((L : ℝ) / (C₀ : ℝ))) + 2)
      = D * ((1 + (L : ℝ)) ^ A * (2 : ℝ) ^ (A * y)
          * (2 : ℝ) ^ (-((2 : ℝ) ^ ((L : ℝ) / (C₀ : ℝ))) + 2)) := by ring
    _ ≤ D * ((1 + (L : ℝ)) ^ A * (2 : ℝ) ^ (A * y) * (2 : ℝ) ^ (-(y ^ (4 : ℝ)) + 2)) := by
        apply mul_le_mul_of_nonneg_left _ hD
        apply mul_le_mul_of_nonneg_left hxd (by positivity)
    _ ≤ Bc := hfinal
    _ ≤ max Bc 0 := le_max_left _ _

/-! ## The assembly -/

/-- `lmaxR` depends only on `max (max l₁ l₂) (max k₁ k₂)`. -/
lemma lmaxR_lmax_eq (l₁ l₂ k₁ k₂ : ℕ) :
    lmaxR l₁ l₂ k₁ k₂
      = lmaxR (max (max l₁ l₂) (max k₁ k₂)) (max (max l₁ l₂) (max k₁ k₂))
          (max (max l₁ l₂) (max k₁ k₂)) (max (max l₁ l₂) (max k₁ k₂)) := by
  have h1 : ((max (max l₁ l₂) (max k₁ k₂) : ℕ) : ℤ)
      = max (max (l₁ : ℤ) (l₂ : ℤ)) (max (k₁ : ℤ) (k₂ : ℤ)) := by
    push_cast
    rfl
  rw [lmaxR, lmaxR, Work.Analysis.EndVar.lmax, Work.Analysis.EndVar.lmax, h1, max_self, max_self]

/-- The model weight depends only on the four indices through `lmaxR`. -/
lemma modelWeight_lmaxR (A ρ : ℝ) (l₁ l₂ k₁ k₂ : ℕ) :
    modelWeight A ρ l₁ l₂ k₁ k₂
      = modelWeight A ρ (max (max l₁ l₂) (max k₁ k₂)) (max (max l₁ l₂) (max k₁ k₂))
          (max (max l₁ l₂) (max k₁ k₂)) (max (max l₁ l₂) (max k₁ k₂)) := by
  rw [modelWeight, modelWeight, lmaxR_lmax_eq]

/-- **The assembly of the mixed right case from its single-scale estimate.**  The lacunary
bookkeeping of §5 (`VarNormTsumLp`, `invFloorSum_le`, `modelWeight_mul_two_rpow_neg_bounded`)
turns the single-scale estimate `LoMixedRSingleScaleStatement` into the variational target. -/
theorem loMixedRight_of_singleScale (P : Polynomial ℤ) (p₁ p₂ : ENNReal) (hdeg : 2 ≤ P.natDegree)
    (hA1 : Work.KMTContract.AreaA1) (hp₁ : 1 < p₁) (htp₁ : p₁ < ⊤) (hp₂ : 1 < p₂)
    (htp₂ : p₂ < ⊤) (hsum : p₁⁻¹ + p₂⁻¹ ≤ 1)
    (hcore : LoMixedRSingleScaleStatement P p₁ p₂ hdeg hA1 hp₁ htp₁ hp₂ htp₂ hsum) :
    LoMixedRightStatement P p₁ p₂ := by
  obtain ⟨ρc, hρc, hcore'⟩ := hcore
  intro C₀ r hC₀ hr
  have hC₀' : (0 : ℕ) < C₀ := lt_of_lt_of_le Nat.zero_lt_one hC₀
  have h1r : (1 : NNReal) ≤ r := le_trans (by norm_num) hr.le
  have hp : (1 : ENNReal) ≤ (p₁⁻¹ + p₂⁻¹)⁻¹ := ENNReal.one_le_inv.mpr hsum
  refine ⟨0, le_refl 0, min ρc (1 / (4 * (C₀ : ℝ))), lt_min hρc (by positivity), ?_⟩
  intro ρ hρ hρle
  have hρc' : ρ ≤ ρc := le_trans hρle (min_le_left _ _)
  have hρ4 : ρ ≤ 1 / (4 * (C₀ : ℝ)) := le_trans hρle (min_le_right _ _)
  obtain ⟨A, hA, hcore''⟩ := hcore' ρ hρ hρc'
  obtain ⟨C, hC⟩ := hcore'' C₀ hC₀
  -- the summability constant `D(Λ)` of `invFloorSum_le`
  set D : NNReal → ℝ :=
    fun Λ => if h : 1 < Λ then Classical.choose (invFloorSum_le C₀ hC₀ Λ h) else 0 with hD
  have hD0 : ∀ Λ : NNReal, 0 ≤ D Λ := by
    intro Λ
    by_cases h : 1 < Λ
    · rw [hD]; simp only [dif_pos h]
      exact (Classical.choose_spec (invFloorSum_le C₀ hC₀ Λ h)).1
    · rw [hD]; simp [h]
  have hDb : ∀ (Λ : NNReal), 1 < Λ → ∀ (L : ℕ), 1 ≤ L → ∀ (a : ℕ → NNReal),
      PointwiseErgodicTheorems.Lacunary Λ a → (∀ n, 1 ≤ a n) →
      (∑' n : ℕ, (if L ≤ heightScale C₀ (Nat.floor (a n))
        then (((Nat.floor (a n) : ℕ)) : ℝ)⁻¹ else 0))
        ≤ D Λ * (2 : ℝ) ^ (-((2 : ℝ) ^ ((L : ℝ) / (C₀ : ℝ))) + 2) := by
    intro Λ hΛ L hL a ha ha1
    rw [hD]; simp only [dif_pos hΛ]
    exact (Classical.choose_spec (invFloorSum_le C₀ hC₀ Λ hΛ)).2 L hL a ha ha1
  set E : NNReal → ℝ := fun Λ => max (2 * (Λ : ℝ) / ((Λ : ℝ) - 1)) (D Λ) with hE
  have hE0 : ∀ Λ : NNReal, 0 ≤ E Λ := by
    intro Λ
    have h := hD0 Λ
    rw [hE]
    exact le_trans h (le_max_right (2 * (Λ : ℝ) / ((Λ : ℝ) - 1)) (D Λ))
  have hE1 : ∀ (Λ : NNReal), 1 < Λ → max (2 * (Λ : ℝ) / ((Λ : ℝ) - 1)) (D Λ) ≤ E Λ :=
    fun Λ _ => le_of_eq rfl
  -- the constant `B(Λ)` of the weight absorption
  set Bfun : NNReal → ℝ := fun Λ =>
    Classical.choose (modelWeight_mul_two_rpow_neg_bounded A ρ (E Λ) hA hρ (hE0 Λ) C₀ hC₀ hρ4)
    with hBfun
  have hBfun0 : ∀ Λ : NNReal, 0 ≤ Bfun Λ := by
    intro Λ
    rw [hBfun]
    exact (Classical.choose_spec
      (modelWeight_mul_two_rpow_neg_bounded A ρ (E Λ) hA hρ (hE0 Λ) C₀ hC₀ hρ4)).1
  have hBfunb : ∀ (Λ : NNReal) (L : ℕ),
      E Λ * modelWeight A ρ L L L L * (2 : ℝ) ^ (-((2 : ℝ) ^ ((L : ℝ) / (C₀ : ℝ))) + 2)
        ≤ Bfun Λ := by
    intro Λ L
    rw [hBfun]
    exact (Classical.choose_spec
      (modelWeight_mul_two_rpow_neg_bounded A ρ (E Λ) hA hρ (hE0 Λ) C₀ hC₀ hρ4)).2 L
  refine ⟨fun Λ => 4 * C Λ * NNReal.mk (Bfun Λ) (hBfun0 Λ), ?_⟩
  intro a Λ l₁ l₂ k₁ k₂ f g hΛ ha ha1 hΦ
  set Kc : ℝ := Bfun Λ with hKc
  have hlo : ¬ (1 ≤ l₁ ∧ 1 ≤ l₂) := by omega
  -- the exact-height model tuple vanishes at `l₂ = 0`
  have hMT : ∀ n x, modelTuple ρ P C₀ a f g l₁ l₂ k₁ k₂ n x = 0 :=
    fun n x => modelTuple_apply_eq_zero_of_lo ρ P C₀ a f g l₁ l₂ k₁ k₂ n x hlo
  have hlhs : (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ =>
        mainPartTuple ρ P C₀ a f g l₁ l₂ k₁ k₂ n x
          - modelTuple ρ P C₀ a f g l₁ l₂ k₁ k₂ n x))
      = fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ =>
        mainPartTuple ρ P C₀ a f g l₁ l₂ k₁ k₂ n x) := by
    funext x
    congr 1
    funext n
    rw [hMT n x, sub_zero]
  rw [hlhs]
  -- the family and its guard
  set u : ℕ → ℤ → ℂ := fun n x => mainPartTuple ρ P C₀ a f g l₁ l₂ k₁ k₂ n x with hu
  set A₁ : ENNReal := MeasureTheory.eLpNorm f p₁ MeasureTheory.Measure.count with hA₁
  set B₁ : ENNReal := MeasureTheory.eLpNorm g p₂ MeasureTheory.Measure.count with hB₁
  set Xe : ENNReal := (C Λ : ENNReal)
      * ENNReal.ofReal (modelWeight A ρ l₁ l₂ k₁ k₂) * A₁ * B₁ with hXe
  set w : ℝ := modelWeight A ρ l₁ l₂ k₁ k₂ with hw
  set Lr : ℝ := lmaxR l₁ l₂ k₁ k₂ with hLr
  set Lnat : ℕ := max (max l₁ l₂) (max k₁ k₂) with hLnat
  set S : ℝ := E Λ * (2 : ℝ) ^ (-((2 : ℝ) ^ (Lr / (C₀ : ℝ))) + 2) with hS
  have hLr0 : 0 ≤ Lr := by rw [hLr]; exact lmaxR_nonneg l₁ l₂ k₁ k₂
  have hS0 : 0 ≤ S := by
    rw [hS]
    exact mul_nonneg (hE0 Λ) (by positivity)
  have hLrLnat : Lr = (Lnat : ℝ) := by
    rw [hLr, lmaxR, Work.Analysis.EndVar.lmax, hLnat]
    push_cast
    ring
  have hwl : w = modelWeight A ρ Lnat Lnat Lnat Lnat := by
    rw [hw, hLnat]
    exact modelWeight_lmaxR A ρ l₁ l₂ k₁ k₂
  set Gc : ℕ → Prop := fun n =>
      inIndexSet C₀ (max (l₁ : ℤ) (l₂ : ℤ)) (k₁ : ℤ) (k₂ : ℤ) (Nat.floor (a n))
      ∧ splitCut ρ (max (max l₁ l₂) (max k₁ k₂)) < Nat.floor (a n)
      ∧ mainRegime ρ k₁ k₂ (Nat.floor (a n)) with hGc
  have hzero : ∀ n : ℕ, ¬ Gc n → u n = 0 := by
    intro n hg
    funext x
    rw [hu]
    simp only [Work.KMTAreas.A7.mainPartTuple]
    rw [if_neg hg]
    simp
  -- (1) the variational norm is bounded by the `ℓ¹`-sum of the single-scale norms
  refine (VarNormTsumLp h1r hp u).trans ?_
  -- (2) the per-scale bound, in guarded form
  have hper : ∀ n : ℕ, MeasureTheory.eLpNorm (fun x : ℤ => u n x)
      (p₁⁻¹ + p₂⁻¹)⁻¹ MeasureTheory.Measure.count
      ≤ Xe * ENNReal.ofReal ((((Nat.floor (a n) : ℕ)) : ℝ)⁻¹) := by
    intro n
    have h := hC a Λ l₁ l₂ k₁ k₂ f g hΛ ha ha1 hΦ.1 hΦ.2 n
    rw [hXe, hw, hA₁, hB₁, hu]
    refine (h.trans (le_of_eq ?_))
    ac_rfl
  have hper' : ∀ n : ℕ, MeasureTheory.eLpNorm (fun x : ℤ => u n x)
      (p₁⁻¹ + p₂⁻¹)⁻¹ MeasureTheory.Measure.count
      ≤ if Gc n then Xe * ENNReal.ofReal ((((Nat.floor (a n) : ℕ)) : ℝ)⁻¹) else 0 := by
    intro n
    by_cases hg : Gc n
    · rw [if_pos hg]
      refine (hper n).trans (le_of_eq ?_)
      ac_rfl
    · rw [if_neg hg, hzero n hg]
      simp
  -- (3) sum over the scales and pull out the constants
  have hstep3 : (∑' n : ℕ, 4 * MeasureTheory.eLpNorm (fun x : ℤ => u n x)
        (p₁⁻¹ + p₂⁻¹)⁻¹ MeasureTheory.Measure.count)
      ≤ 4 * Xe * (∑' n : ℕ, (if Gc n
          then ENNReal.ofReal ((((Nat.floor (a n) : ℕ)) : ℝ)⁻¹) else 0)) := by
    calc (∑' n : ℕ, 4 * MeasureTheory.eLpNorm (fun x : ℤ => u n x)
          (p₁⁻¹ + p₂⁻¹)⁻¹ MeasureTheory.Measure.count)
        ≤ ∑' n : ℕ, 4 * (if Gc n
            then Xe * ENNReal.ofReal ((((Nat.floor (a n) : ℕ)) : ℝ)⁻¹) else 0) :=
          ENNReal.tsum_le_tsum (fun n => mul_le_mul' le_rfl (hper' n))
      _ = ∑' n : ℕ, (4 * Xe) * (if Gc n
            then ENNReal.ofReal ((((Nat.floor (a n) : ℕ)) : ℝ)⁻¹) else 0) := by
          refine tsum_congr (fun n => ?_)
          by_cases hg : Gc n
          · rw [if_pos hg, if_pos hg]; ac_rfl
          · rw [if_neg hg, if_neg hg]; simp
      _ = (4 * Xe) * (∑' n : ℕ, (if Gc n
            then ENNReal.ofReal ((((Nat.floor (a n) : ℕ)) : ℝ)⁻¹) else 0)) :=
          ENNReal.tsum_mul_left
      _ = 4 * Xe * (∑' n : ℕ, (if Gc n
            then ENNReal.ofReal ((((Nat.floor (a n) : ℕ)) : ℝ)⁻¹) else 0)) := rfl
  -- (4) the lacunary sum bound
  have hcond : ∀ n : ℕ, Gc n → max (max l₁ l₂) (max k₁ k₂) ≤ heightScale C₀ (Nat.floor (a n)) := by
    intro n hg
    have h1 : inIndexSet C₀ (max (l₁ : ℤ) (l₂ : ℤ)) (k₁ : ℤ) (k₂ : ℤ) (Nat.floor (a n)) := hg.1
    rw [inIndexSet] at h1
    have h2 : max (l₁ : ℤ) (l₂ : ℤ) ≤ ((heightScale C₀ (Nat.floor (a n)) : ℕ) : ℤ) := h1.1
    have h3 : (k₁ : ℤ) ≤ ((heightScale C₀ (Nat.floor (a n)) : ℕ) : ℤ) := h1.2.1
    have h4 : (k₂ : ℤ) ≤ ((heightScale C₀ (Nat.floor (a n)) : ℕ) : ℤ) := h1.2.2
    omega
  have hstep4 : (∑' n : ℕ, (if Gc n
        then ENNReal.ofReal ((((Nat.floor (a n) : ℕ)) : ℝ)⁻¹) else 0))
      ≤ ENNReal.ofReal S := by
    have hexp : ((max (max l₁ l₂) (max k₁ k₂) : ℕ) : ℝ) / (C₀ : ℝ) = Lr / (C₀ : ℝ) := by
      rw [← hLrLnat]
    have hmain := tsum_ite_floor_le_indexSet C₀ hC₀ Λ hΛ (D Λ) (hD0 Λ)
      (fun L hL a ha ha1 => hDb Λ hΛ L hL a ha ha1)
      (max (max l₁ l₂) (max k₁ k₂)) (E Λ) (hE1 Λ hΛ) a ha ha1 Gc hcond
    rw [hexp] at hmain
    rw [hS]
    exact hmain
  -- (5) the weight absorption
  have hB : w * S ≤ Bfun Λ := by
    have h := hBfunb Λ Lnat
    rw [← hLrLnat] at h
    calc w * S = E Λ * modelWeight A ρ Lnat Lnat Lnat Lnat
          * (2 : ℝ) ^ (-((2 : ℝ) ^ (Lr / (C₀ : ℝ))) + 2) := by
          rw [hwl, hS]; ring
      _ ≤ Bfun Λ := h
  have hofReal : ENNReal.ofReal w * ENNReal.ofReal S = ENNReal.ofReal (w * S) :=
    (ENNReal.ofReal_mul (modelWeight_nonneg A ρ hA l₁ l₂ k₁ k₂)).symm
  have hKval : ((4 * C Λ * NNReal.mk (Bfun Λ) (hBfun0 Λ) : NNReal) : ENNReal)
      = 4 * (C Λ : ENNReal) * ENNReal.ofReal (Bfun Λ) := by
    rw [ENNReal.coe_mul, ENNReal.coe_mul, ENNReal.coe_ofNat,
      (ENNReal.ofReal_coe_nnreal (p := (NNReal.mk (Bfun Λ) (hBfun0 Λ)))).symm]
    rfl
  have hlw : lossWeight 0 ρ l₁ l₂ k₁ k₂ = 1 := by
    rw [lossWeight]
    simp
  refine (hstep3.trans (mul_le_mul' le_rfl hstep4)).trans ?_
  calc 4 * Xe * ENNReal.ofReal S
      = 4 * ((C Λ : ENNReal) * ENNReal.ofReal w * A₁ * B₁) * ENNReal.ofReal S := by
        rw [hXe, hw]
    _ = 4 * (C Λ : ENNReal) * (ENNReal.ofReal w * ENNReal.ofReal S) * A₁ * B₁ := by ac_rfl
    _ = 4 * (C Λ : ENNReal) * ENNReal.ofReal (w * S) * A₁ * B₁ := by rw [hofReal]
    _ ≤ 4 * (C Λ : ENNReal) * ENNReal.ofReal (Bfun Λ) * A₁ * B₁ :=
        mul_le_mul' (mul_le_mul' (mul_le_mul' le_rfl (ENNReal.ofReal_le_ofReal hB)) le_rfl) le_rfl
    _ = ((4 * C Λ * NNReal.mk (Bfun Λ) (hBfun0 Λ) : NNReal) : ENNReal)
          * ENNReal.ofReal (lossWeight 0 ρ l₁ l₂ k₁ k₂) * A₁ * B₁ := by
        rw [hKval, hlw, ENNReal.ofReal_one, mul_one]

end

end Work.KMTAreas.A7