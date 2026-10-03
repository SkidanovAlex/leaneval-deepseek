/-
# The off-band part of the mixed-range §6 model approximation (Area A7, `…Holds`)

Target: `Work.KMTAreas.A7.LoMixedOffBandStatement P p₁ p₂`
(`Submission/Work/KMTAreas/A7/LoMixedDefs.lean`): on the guard but *outside* the band
(`¬ loBandCond`, i.e. `Log N < max k₁ k₂ + 1 + 2·loMixedU`), the §6 model-approximation error
`mainPartTuple − loMixedTuple` of the mixed range is only `O(1)` per scale, but the number of
admissible lacunary scales satisfying the off-band condition is `≲ 2^{2ρL}`; the weight
`lossWeight c ρ 0 l₂ k₁ k₂` with `c ≥ 2` absorbs that count.

This is Krause--Mirek--Tao, Ann. of Math. 195 (3) 2022, the exceptional-scale part of §6 at the
arithmetic heights `(0,l₂)` (the companion of `LoMixedBandErrStatement`, which handles the band
itself, cf. `LoMixedSingleScaleHolds`/`LoMixedLeft`).

## The assembly (this file)

The proof is the `ℓ¹`-of-`L^p` spike argument of `Work.KMTAreas.A7.ExceptionalBound`:

* `LoMixedOffBandRegimeHolds` bounds the whole off-band regime: the parameters `l₂,k₁,k₂,Log N`
  and `N` are bounded in terms of `(P, C₀, ρ)` alone, so the family of scales that can contribute
  is finite;
* `OffBandVarpPieceLp` is the crude (`O(1)` in `N`) `ℓ^p` bound for the concrete column
  `varpPiece (kmtPj ρ) P P.natDegree N f g 0 l₂ k₁ k₂`, with *no* hypothesis on `f, g`;
* `OffBandLoMixedOpHolds` is the same crude `ℓ^p` bound for the §6 model operator `loMixedOp`;
* the family `n ↦ mainPartTuple − loMixedTuple` vanishes off the guard, and off the band on the
  guard (by `LoMixedOffBandRegimeHolds`), hence for `n ≥ nBound Λ B`; subadditivity of `eLpNorm`
  (`eLpNorm_sub_le`) plus `eLpNorm_variationalNorm_le_sum` (a family supported on a finite set of
  scales has variational norm bounded by the sum of the `L^p` norms) finish the estimate, and
  `floor_a_gt` (lacunary growth) provides the index bound.
-/
import Mathlib
import Submission.Work.KMTAreas.A7.ExceptionalBound
import Submission.Work.KMTAreas.A7.OffBandVarpPieceLp
import Submission.Work.KMTAreas.A7.LoMixedOffBandRegimeHolds
import Submission.Work.KMTAreas.A7.OffBandLoMixedOpHolds

namespace Work.KMTAreas.A7

noncomputable section

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal BigOperators
open PointwiseErgodicTheorems Submission.PointwiseErgodicTheorems
open Work.KMTContract Work.Analysis.EndVar Work.Analysis.IonescuWainger Work.Analysis.IWMultiplier

/-! ## Elementary `ℝ≥0∞` arithmetic -/

/-- `4 · (c · Y) = (4c) · Y` for `ofReal` constants. -/
private lemma four_mul_ofReal_mul (c : ℝ) (Y : ENNReal) :
    (4 : ENNReal) * (ENNReal.ofReal c * Y) = ENNReal.ofReal (4 * c) * Y := by
  have h4 : (4 : ENNReal) = ENNReal.ofReal (4 : ℝ) := (ENNReal.ofReal_ofNat 4).symm
  rw [h4, ← mul_assoc, ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4)]

/-- A scalar comparison of `NNReal`-valued constants, transported to `ℝ≥0∞`. -/
private lemma nNReal_mul_le_of_scalar {m : ℝ} {K : NNReal} (hKm : m ≤ (K : ℝ))
    (Y : ENNReal) : ENNReal.ofReal m * Y ≤ (K : ENNReal) * Y := by
  rw [← ENNReal.ofReal_coe_nnreal (p := K)]
  exact mul_le_mul' (ENNReal.ofReal_le_ofReal hKm) le_rfl

/-! ## The assembly -/

theorem LoMixedOffBandHolds (P : Polynomial ℤ) (p₁ p₂ : ENNReal) (hdeg : 2 ≤ P.natDegree)
    (hA1 : Work.KMTContract.AreaA1) (hp₁ : 1 < p₁) (htp₁ : p₁ < ⊤) (hp₂ : 1 < p₂)
    (htp₂ : p₂ < ⊤) (hsum : p₁⁻¹ + p₂⁻¹ ≤ 1) :
    Work.KMTAreas.A7.LoMixedOffBandStatement P p₁ p₂ := by
  classical
  intro C₀ r hC₀ hr
  have hq : (1 : ENNReal) ≤ (p₁⁻¹ + p₂⁻¹)⁻¹ := ENNReal.one_le_inv.mpr hsum
  have hr1 : (1 : NNReal) ≤ r := le_trans (by norm_num) (le_of_lt hr)
  refine ⟨0, le_refl 0, 1 / (4 * (C₀ : ℝ)), by positivity, ?_⟩
  intro ρ hρ hρle
  have hρ1 : ρ ≤ 1 := by
    have h4 : (1 : ℝ) ≤ 4 * (C₀ : ℝ) := by
      have h : (1 : ℝ) ≤ (C₀ : ℝ) := by exact_mod_cast hC₀
      linarith
    have h : 1 / (4 * (C₀ : ℝ)) ≤ 1 := by
      rw [div_le_one (by positivity)]
      linarith
    exact le_trans hρle h
  obtain ⟨B, hB1, hreg⟩ := LoMixedOffBandRegimeHolds P C₀ hC₀ ρ hρ hρle
  obtain ⟨Cv, hCv, hCvb⟩ := OffBandVarpPieceLp P p₁ p₂ hp₁ htp₁ hp₂ htp₂ hsum ρ hρ hρ1 B
  obtain ⟨Cm, hCm, hCmb⟩ := OffBandLoMixedOpHolds P hdeg p₁ p₂ hp₁ htp₁ hp₂ htp₂ hsum ρ hρ hρ1 B
  have hc2 : (0 : ℝ) < 2 * (Cv + Cm) := by linarith
  set Kfun : NNReal → NNReal := fun Λ =>
    ⟨max 1 (4 * ((nBound Λ B + 1 : ℕ) : ℝ) * (2 * (Cv + Cm))),
      le_trans zero_le_one (le_max_left (1 : ℝ) _)⟩ with hKfun
  refine ⟨Kfun, ?_⟩
  intro a Λ l₂ k₁ k₂ f g hΛ ha ha1 hl₂
  have hKval : (Kfun Λ : ℝ)
      = max 1 (4 * ((nBound Λ B + 1 : ℕ) : ℝ) * (2 * (Cv + Cm))) := by
    rw [hKfun]
    rfl
  set M : ℕ := nBound Λ B + 1 with hM
  set A : ENNReal := MeasureTheory.eLpNorm f p₁ MeasureTheory.Measure.count with hA
  set Bv : ENNReal := MeasureTheory.eLpNorm g p₂ MeasureTheory.Measure.count with hBv
  set u : ℕ → ℤ → ℂ := fun n x =>
    if loGuard ρ C₀ a 0 l₂ k₁ k₂ n ∧ ¬ loBandCond ρ P l₂ k₁ k₂ (Nat.floor (a n)) then
      mainPartTuple ρ P C₀ a f g 0 l₂ k₁ k₂ n x - loMixedTuple ρ P C₀ a f g l₂ k₁ k₂ n x
    else 0 with hu
  change MeasureTheory.eLpNorm (fun x : ℤ => variationalNorm r (fun n : ℕ => u n x))
      ((p₁⁻¹ + p₂⁻¹)⁻¹) Measure.count ≤
    (Kfun Λ : ENNReal) * ENNReal.ofReal (lossWeight 0 ρ 0 l₂ k₁ k₂) *
      MeasureTheory.eLpNorm f p₁ Measure.count * MeasureTheory.eLpNorm g p₂ Measure.count
  -- the support of the off-band family is finite
  have hsupp : ∀ n : ℕ, n ∉ Finset.range M → u n = 0 := by
    intro n hn
    have hn' : M ≤ n := by simpa [Finset.mem_range] using hn
    have hgate : ¬ (loGuard ρ C₀ a 0 l₂ k₁ k₂ n
        ∧ ¬ loBandCond ρ P l₂ k₁ k₂ (Nat.floor (a n))) := by
      rintro ⟨hg, hoff⟩
      have hb := hreg l₂ k₁ k₂ (Nat.floor (a n)) hg.1 hg.2.1 hg.2.2 hoff
      have hgt : 2 ^ B < Nat.floor (a n) :=
        floor_a_gt hΛ ha ha1 B (by rw [hM] at hn'; omega)
      have := hb.2.2.2.2
      omega
    funext x
    simp only [hu, if_neg hgate, Pi.zero_apply]
  -- the per-scale bound
  have hper : ∀ n ∈ Finset.range M,
      4 * MeasureTheory.eLpNorm (u n) ((p₁⁻¹ + p₂⁻¹)⁻¹) Measure.count
        ≤ ENNReal.ofReal (8 * (Cv + Cm)) * (A * Bv) := by
    intro n _
    have hsub : MeasureTheory.eLpNorm (u n) ((p₁⁻¹ + p₂⁻¹)⁻¹) Measure.count
        ≤ ENNReal.ofReal (2 * (Cv + Cm)) * (A * Bv) := by
      by_cases hg : loGuard ρ C₀ a 0 l₂ k₁ k₂ n
          ∧ ¬ loBandCond ρ P l₂ k₁ k₂ (Nat.floor (a n))
      · have hguard := hg.1
        have hoff := hg.2
        have hb := hreg l₂ k₁ k₂ (Nat.floor (a n)) hguard.1 hguard.2.1 hguard.2.2 hoff
        obtain ⟨hl₂B, hk₁B, hk₂B, hlogB, hNB⟩ := hb
        have hb1 := hCvb l₂ k₁ k₂ (Nat.floor (a n)) f g hl₂B hk₁B hk₂B hlogB
        have hN1 : 1 ≤ Nat.floor (a n) := Nat.le_floor (by simpa using ha1 n)
        have hb2 := hCmb l₂ k₁ k₂ (Nat.floor (a n)) f g hl₂B hk₁B hk₂B hN1 hNB
        have hmain : mainPartTuple ρ P C₀ a f g 0 l₂ k₁ k₂ n
            = varpPiece (kmtPj ρ) P P.natDegree (((Nat.floor (a n) : ℕ)) : NNReal)
                f g 0 l₂ k₁ k₂ := by
          funext y
          rw [mainPartTuple_apply, if_pos hguard]
          simp only [varpPiece, AhalfR, Nat.floor_natCast]
        have hmodel : loMixedTuple ρ P C₀ a f g l₂ k₁ k₂ n
            = loMixedOp ρ P (Nat.floor (a n)) l₂ k₁ k₂ f g := by
          funext x
          simp only [loMixedTuple, if_pos hguard]
        have hunfold : u n = fun x : ℤ =>
            mainPartTuple ρ P C₀ a f g 0 l₂ k₁ k₂ n x
              - loMixedTuple ρ P C₀ a f g l₂ k₁ k₂ n x := by
          funext x
          simp only [hu, if_pos hg]
        rw [hunfold, hmain, hmodel, hA, hBv]
        refine (eLpNorm_sub_le hq).trans ?_
        refine (add_le_add hb1 hb2).trans ?_
        rw [← add_mul]
        refine mul_le_mul' ?_ le_rfl
        rw [← ENNReal.ofReal_add hCv.le hCm.le]
        exact ENNReal.ofReal_le_ofReal (by linarith)
      · have hunfold : u n = 0 := by
          funext x
          simp only [hu, if_neg hg, Pi.zero_apply]
        rw [hunfold, hA, hBv]
        simp
    calc 4 * MeasureTheory.eLpNorm (u n) ((p₁⁻¹ + p₂⁻¹)⁻¹) Measure.count
        ≤ 4 * (ENNReal.ofReal (2 * (Cv + Cm)) * (A * Bv)) :=
          mul_le_mul' le_rfl hsub
      _ = ENNReal.ofReal (8 * (Cv + Cm)) * (A * Bv) := by
          rw [four_mul_ofReal_mul,
            show (4 : ℝ) * (2 * (Cv + Cm)) = 8 * (Cv + Cm) from by ring]
  -- the `ℓ¹`-of-`L^p` spike bound
  have hsum1 := eLpNorm_variationalNorm_le_sum (μ := Measure.count) (r := r)
    (p := (p₁⁻¹ + p₂⁻¹)⁻¹) hr1 hq (s := Finset.range M) hsupp
    (fun n _ => (measurable_of_countable (u n)).aestronglyMeasurable)
  refine hsum1.trans ?_
  have hsum2 : ∑ n ∈ Finset.range M, 4 * MeasureTheory.eLpNorm (u n) ((p₁⁻¹ + p₂⁻¹)⁻¹)
        Measure.count
      ≤ ∑ _n ∈ Finset.range M, ENNReal.ofReal (8 * (Cv + Cm)) * (A * Bv) :=
    Finset.sum_le_sum (fun n hn => hper n hn)
  refine hsum2.trans ?_
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  -- `M · (8(Cv+Cm)) ≤ K(Λ)`
  have hscalar : ((M : ℕ) : ℝ) * (8 * (Cv + Cm)) ≤ (Kfun Λ : ℝ) := by
    rw [hKval, hM]
    have heq : ((nBound Λ B + 1 : ℕ) : ℝ) * (8 * (Cv + Cm))
        = 4 * ((nBound Λ B + 1 : ℕ) : ℝ) * (2 * (Cv + Cm)) := by ring
    rw [heq]
    exact le_max_right _ _
  have hMle : (M : ENNReal) * ENNReal.ofReal (8 * (Cv + Cm)) ≤ (Kfun Λ : ENNReal) := by
    rw [← ENNReal.ofReal_natCast M, ← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ (M : ℝ))]
    simpa using nNReal_mul_le_of_scalar hscalar (1 : ENNReal)
  -- reassociate and conclude
  have hstep : (M : ENNReal) * (ENNReal.ofReal (8 * (Cv + Cm)) * (A * Bv))
      = ((M : ENNReal) * ENNReal.ofReal (8 * (Cv + Cm))) * (A * Bv) := (mul_assoc _ _ _).symm
  rw [hstep]
  refine (mul_le_mul' hMle le_rfl).trans ?_
  rw [lossWeight]
  simp only [zero_mul, Real.rpow_zero, mul_one, ENNReal.ofReal_one]
  exact le_of_eq (mul_assoc _ _ _).symm

end

end Work.KMTAreas.A7
