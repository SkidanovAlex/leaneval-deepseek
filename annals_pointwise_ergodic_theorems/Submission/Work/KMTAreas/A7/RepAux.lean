/-
# Auxiliary estimates for `Work.KMTAreas.A7.ModelApproxHiRep`

This module collects the pieces of the proof of `Work.KMTAreas.A7.ModelApproxHiRep` that are
independent of the §6 single-scale estimate:

* `repWeight A ρ l₁ l₂ k₁ k₂ = 2^{A (2^{ρL} + L)}` (`L = lmaxR l₁ l₂ k₁ k₂`) — the weight of the
  single-scale mass bound of the repaired model.  The exponential factor `2^{A 2^{ρL}}` and the
  factor `2^{A L}` are killed by the lacunary decay `2^{-2^{L/C₀}}` in the assembly, cf.
  `RepAbsorb`;
* `repHiCoreDecidable` — `hiCore` is decidable;
* `repOffBand_of_ingredients` — the off-band part of the estimate.
-/
import Mathlib
import Submission.Work.KMTAreas.A7.ExcAux2
import Submission.Work.KMTAreas.A7.uRep_nonAliasing
import Submission.Work.KMTAreas.A7.hiModelTupleRep_eq_bilinOp
import Submission.Work.KMTPlan.A6.vpc_bilinOp_sub

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace Work.KMTAreas.A7

noncomputable section

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal BigOperators
open PointwiseErgodicTheorems Submission.PointwiseErgodicTheorems
open Work.Analysis.IonescuWainger Work.Analysis.EndVar Work.KMTContract

/-- **The weight of the single-scale mass bound of the repaired model**:
`repWeight A ρ l₁ l₂ k₁ k₂ = 2^{A (2^{ρ L} + L)}`, `L = lmaxR l₁ l₂ k₁ k₂`. -/
noncomputable def repWeight (A ρ : ℝ) (l₁ l₂ k₁ k₂ : ℕ) : ℝ :=
  (2 : ℝ) ^ (A * ((2 : ℝ) ^ (ρ * lmaxR l₁ l₂ k₁ k₂) + lmaxR l₁ l₂ k₁ k₂))

theorem repWeight_nonneg (A ρ : ℝ) (l₁ l₂ k₁ k₂ : ℕ) : 0 ≤ repWeight A ρ l₁ l₂ k₁ k₂ := by
  rw [repWeight]; positivity

theorem repWeight_pos (A ρ : ℝ) (l₁ l₂ k₁ k₂ : ℕ) : 0 < repWeight A ρ l₁ l₂ k₁ k₂ := by
  rw [repWeight]; positivity

/-- `hiCore` is decidable (it is a conjunction of decidable comparisons). -/
instance repHiCoreDecidable (ρ : ℝ) (P : ℤ[X]) (C₀ : ℕ) (a : ℕ → NNReal)
    (l₁ l₂ k₁ k₂ n : ℕ) : Decidable (hiCore ρ P C₀ a l₁ l₂ k₁ k₂ n) := by
  unfold hiCore
  infer_instance

/-- **The off-band part of the estimate.**  The family is the (clamped) error on the scales which
are admissible, in the main regime, but off the band `bandCond`; there the model tuple vanishes
and the error is the concrete column.  The two mathematical ingredients are supplied as
hypotheses:

* `hreg` — the parameter bound of the off-band regime (`RepOffBandRegime`);
* `hcrude` — the crude single-scale bound for the concrete column (`RepOffBandCrude`). -/
theorem repOffBand_of_ingredients (P : Polynomial ℤ) (p₁ p₂ : ENNReal) (hdeg : 2 ≤ P.natDegree)
    (hp₁ : 1 < p₁) (htp₁ : p₁ < ⊤) (hp₂ : 1 < p₂) (htp₂ : p₂ < ⊤)
    (hsum : p₁⁻¹ + p₂⁻¹ ≤ 1) (C₀ : ℕ) (hC₀ : 1 ≤ C₀) (r : NNReal) (hr : 2 < r)
    (hreg : ∀ (ρ : ℝ), 0 < ρ → ρ ≤ 1 / (4 * (C₀ : ℝ)) →
      ∃ B : ℕ, 1 ≤ B ∧ ∀ (l₁ l₂ k₁ k₂ N : ℕ),
        inIndexSet C₀ (max (l₁ : ℤ) (l₂ : ℤ)) (k₁ : ℤ) (k₂ : ℤ) N →
        splitCut ρ (max (max l₁ l₂) (max k₁ k₂)) < N →
        mainRegime ρ k₁ k₂ N →
        ¬ bandCond ρ l₁ l₂ k₁ k₂ N →
        l₁ ≤ B ∧ l₂ ≤ B ∧ k₁ ≤ B ∧ k₂ ≤ B ∧ (Work.Analysis.EndVar.logN N).toNat ≤ B
          ∧ N ≤ 2 ^ B)
    (hcrude : ∀ (ρ : ℝ), 0 < ρ → ρ ≤ 1 / (4 * (C₀ : ℝ)) → ∀ B : ℕ,
      ∃ C : ℝ, 0 < C ∧ ∀ (l₁ l₂ k₁ k₂ N : ℕ) (f g : ℤ → ℂ),
        l₁ ≤ B → l₂ ≤ B → k₁ ≤ B → k₂ ≤ B → N ≤ 2 ^ B →
        MeasureTheory.eLpNorm (varpPiece (kmtPj ρ) P P.natDegree
            (N : NNReal) f g l₁ l₂ k₁ k₂)
          (p₁⁻¹ + p₂⁻¹)⁻¹ MeasureTheory.Measure.count
        ≤ ENNReal.ofReal C * (MeasureTheory.eLpNorm f p₁ MeasureTheory.Measure.count
            * MeasureTheory.eLpNorm g p₂ MeasureTheory.Measure.count)) :
    ∀ (ρ : ℝ), 0 < ρ → ρ ≤ 1 / (4 * (C₀ : ℝ)) → ∃ K : NNReal → NNReal,
      ∀ (a : ℕ → NNReal) (Λ : NNReal) (l₁ l₂ k₁ k₂ : ℕ) (f g : ℤ → ℂ),
        1 < Λ → PointwiseErgodicTheorems.Lacunary Λ a → (∀ n, 1 ≤ a n) →
        MeasureTheory.eLpNorm (fun x : ℤ =>
            PointwiseErgodicTheorems.variationalNorm r
              (fun n : ℕ =>
                if hiCore ρ P C₀ a l₁ l₂ k₁ k₂ n
                    ∧ ¬ bandCond ρ l₁ l₂ k₁ k₂ (Nat.floor (a n)) then
                  mainPartTuple ρ P C₀ a f g l₁ l₂ k₁ k₂ n x
                    - modelTupleRep ρ P C₀ a f g l₁ l₂ k₁ k₂ n x
                else 0))
          (p₁⁻¹ + p₂⁻¹)⁻¹ MeasureTheory.Measure.count
        ≤ (K Λ : ENNReal)
            * (MeasureTheory.eLpNorm f p₁ MeasureTheory.Measure.count
              * MeasureTheory.eLpNorm g p₂ MeasureTheory.Measure.count) := by
  classical
  intro ρ hρ hρ4
  obtain ⟨B, hB1, hB⟩ := hreg ρ hρ hρ4
  obtain ⟨Cv, hCv, hCvB⟩ := hcrude ρ hρ hρ4 B
  refine ⟨fun Λ => ⟨max 1 (4 * (((nBound Λ B + 1 : ℕ)) : ℝ) * Cv),
    le_trans zero_le_one (le_max_left _ _)⟩, ?_⟩
  intro a Λ l₁ l₂ k₁ k₂ f g hΛ ha ha1
  set Mv : ℕ := nBound Λ B + 1 with hMv
  set X : ENNReal := MeasureTheory.eLpNorm f p₁ MeasureTheory.Measure.count
      * MeasureTheory.eLpNorm g p₂ MeasureTheory.Measure.count with hX
  set off : ℕ → ℤ → ℂ := fun n x =>
      if hiCore ρ P C₀ a l₁ l₂ k₁ k₂ n
          ∧ ¬ bandCond ρ l₁ l₂ k₁ k₂ (Nat.floor (a n)) then
        mainPartTuple ρ P C₀ a f g l₁ l₂ k₁ k₂ n x
          - modelTupleRep ρ P C₀ a f g l₁ l₂ k₁ k₂ n x
      else 0 with hoff
  have hq : (1 : ENNReal) ≤ (p₁⁻¹ + p₂⁻¹)⁻¹ := ENNReal.one_le_inv.mpr hsum
  have hr1 : (1 : NNReal) ≤ r := le_of_lt (lt_trans (by norm_num) hr)
  have hsupp : ∀ n : ℕ, n ∉ Finset.range Mv → off n = 0 := by
    intro n hn
    by_cases hc : hiCore ρ P C₀ a l₁ l₂ k₁ k₂ n
        ∧ ¬ bandCond ρ l₁ l₂ k₁ k₂ (Nat.floor (a n))
    · exfalso
      have hguard : inIndexSet C₀ (max (l₁ : ℤ) (l₂ : ℤ)) (k₁ : ℤ) (k₂ : ℤ)
            (Nat.floor (a n)) ∧ splitCut ρ (max (max l₁ l₂) (max k₁ k₂)) < Nat.floor (a n)
            ∧ mainRegime ρ k₁ k₂ (Nat.floor (a n)) := hc.1
      have hNle : Nat.floor (a n) ≤ 2 ^ B :=
        (hB l₁ l₂ k₁ k₂ (Nat.floor (a n)) hguard.1 hguard.2.1 hguard.2.2 hc.2).2.2.2.2.2
      have hnm : nBound Λ B + 1 ≤ n := by
        have h1 : ¬ (n < nBound Λ B + 1) := by
          simpa only [Finset.mem_range, hMv] using hn
        omega
      have hlt : 2 ^ B < Nat.floor (a n) := floor_a_gt hΛ ha ha1 B (by omega)
      omega
    · funext x
      simp only [hoff, if_neg hc, Pi.zero_apply]
  have hper : ∀ n ∈ Finset.range Mv,
      4 * MeasureTheory.eLpNorm (off n) (p₁⁻¹ + p₂⁻¹)⁻¹ MeasureTheory.Measure.count
        ≤ 4 * (ENNReal.ofReal Cv * X) := by
    intro n _
    by_cases hc : hiCore ρ P C₀ a l₁ l₂ k₁ k₂ n
        ∧ ¬ bandCond ρ l₁ l₂ k₁ k₂ (Nat.floor (a n))
    · have hguard : inIndexSet C₀ (max (l₁ : ℤ) (l₂ : ℤ)) (k₁ : ℤ) (k₂ : ℤ)
            (Nat.floor (a n)) ∧ splitCut ρ (max (max l₁ l₂) (max k₁ k₂)) < Nat.floor (a n)
            ∧ mainRegime ρ k₁ k₂ (Nat.floor (a n)) := hc.1
      have hNb := hB l₁ l₂ k₁ k₂ (Nat.floor (a n)) hguard.1 hguard.2.1 hguard.2.2 hc.2
      obtain ⟨hl₁B, hl₂B, hk₁B, hk₂B, -, hNB⟩ := hNb
      have hmain : ∀ x : ℤ,
          mainPartTuple ρ P C₀ a f g l₁ l₂ k₁ k₂ n x
            = varpPiece (kmtPj ρ) P P.natDegree (((Nat.floor (a n) : ℕ)) : NNReal)
                f g l₁ l₂ k₁ k₂ x := by
        intro x
        rw [mainPartTuple, if_pos hguard]
        simp only [varpPiece, AhalfR, Nat.floor_natCast]
      have hmodel : modelTupleRep ρ P C₀ a f g l₁ l₂ k₁ k₂ n = 0 := by
        funext x
        rw [modelTupleRep, if_neg (fun h => hc.2 h.2.2.2), Pi.zero_apply]
      have hunf : off n = fun x : ℤ =>
          varpPiece (kmtPj ρ) P P.natDegree (((Nat.floor (a n) : ℕ)) : NNReal)
            f g l₁ l₂ k₁ k₂ x := by
        funext x
        rw [hoff]
        simp only [if_pos hc]
        rw [hmain x, hmodel, Pi.zero_apply, sub_zero]
      rw [hunf, hX]
      exact mul_le_mul' le_rfl (hCvB l₁ l₂ k₁ k₂ (Nat.floor (a n)) f g
        hl₁B hl₂B hk₁B hk₂B hNB)
    · have hzero : off n = 0 := by
        funext x
        simp only [hoff, if_neg hc, Pi.zero_apply]
      rw [hzero, MeasureTheory.eLpNorm_zero, hX]
      simp
  have hsum1 := eLpNorm_variationalNorm_le_sum (μ := MeasureTheory.Measure.count) (r := r)
    (p := (p₁⁻¹ + p₂⁻¹)⁻¹) hr1 hq (s := Finset.range Mv) hsupp
    (fun n _ => (measurable_of_countable (off n)).aestronglyMeasurable)
  refine hsum1.trans ?_
  have hsum2 : ∑ n ∈ Finset.range Mv,
        4 * MeasureTheory.eLpNorm (off n) (p₁⁻¹ + p₂⁻¹)⁻¹ MeasureTheory.Measure.count
      ≤ ∑ _n ∈ Finset.range Mv, 4 * (ENNReal.ofReal Cv * X) :=
    Finset.sum_le_sum (fun n hn => hper n hn)
  refine hsum2.trans ?_
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hscalar : ((Mv : ℕ) : ℝ) * (4 * Cv)
      ≤ ((⟨max 1 (4 * (((nBound Λ B + 1 : ℕ)) : ℝ) * Cv),
            le_trans zero_le_one (le_max_left _ _)⟩ : NNReal) : ℝ) := by
    change ((Mv : ℕ) : ℝ) * (4 * Cv)
      ≤ max 1 (4 * (((nBound Λ B + 1 : ℕ)) : ℝ) * Cv)
    rw [hMv]
    exact le_trans (le_of_eq (by ring)) (le_max_right _ _)
  exact term_sum_le Mv Cv X hscalar

/-- `iwConv` of the zero function (local copy). -/
private theorem rep_iwConv_zero_right (A : Finset Work.Analysis.IonescuWainger.Circle)
    (Φ : Work.Analysis.IonescuWainger.Circle → ℂ) :
    Work.Analysis.IWMultiplier.iwConv A Φ (0 : ℤ → ℂ) = 0 := by
  funext n
  simp [Work.Analysis.IWMultiplier.iwConv]

/-! ## Degenerate cases

Both tuples are bilinear in `f` and `g`, so with a vanishing argument they vanish identically. -/

/-- With `g = 0` the concrete column vanishes (pointwise). -/
theorem repMainPartTuple_zero_right (ρ : ℝ) (P : Polynomial ℤ) (C₀ : ℕ) (a : ℕ → NNReal)
    (f : ℤ → ℂ) (l₁ l₂ k₁ k₂ n : ℕ) (x : ℤ) :
    mainPartTuple ρ P C₀ a f 0 l₁ l₂ k₁ k₂ n x = 0 := by
  have h : mainPartTuple ρ P C₀ a f 0 l₁ l₂ k₁ k₂ = 0 := by
    funext n x
    simp only [mainPartTuple]
    split_ifs with h
    · simp only [varpPiece, AhalfR, Fpiece, Gpiece, piece, piExact, kmtProj, kmtPj]
      simp [rep_iwConv_zero_right, Ahalf, Ablock]
    · rfl
  exact congrFun (congrFun h n) x

/-- With `f = 0` the concrete column vanishes (pointwise). -/
theorem repMainPartTuple_zero_left (ρ : ℝ) (P : Polynomial ℤ) (C₀ : ℕ) (a : ℕ → NNReal)
    (g : ℤ → ℂ) (l₁ l₂ k₁ k₂ n : ℕ) (x : ℤ) :
    mainPartTuple ρ P C₀ a 0 g l₁ l₂ k₁ k₂ n x = 0 := by
  have h : mainPartTuple ρ P C₀ a 0 g l₁ l₂ k₁ k₂ = 0 := by
    funext n x
    simp only [mainPartTuple]
    split_ifs with h
    · simp only [varpPiece, AhalfR, Fpiece, Gpiece, piece, piExact, kmtProj, kmtPj]
      simp [rep_iwConv_zero_right, Ahalf, Ablock]
    · rfl
  exact congrFun (congrFun h n) x

/-- With `g = 0` the repaired model tuple vanishes (pointwise). -/
theorem repModelTupleRep_zero_right (ρ : ℝ) (P : Polynomial ℤ) (C₀ : ℕ) (a : ℕ → NNReal)
    (f : ℤ → ℂ) (l₁ l₂ k₁ k₂ n : ℕ) (x : ℤ) :
    modelTupleRep ρ P C₀ a f 0 l₁ l₂ k₁ k₂ n x = 0 := by
  have h : modelTupleRep ρ P C₀ a f 0 l₁ l₂ k₁ k₂ = 0 := by
    funext n x
    simp only [modelTupleRep]
    split_ifs with h
    · have h0 : ∀ t : ℝ,
          BtwistExact ρ P l₁ l₂
            (mStarF (uRep ρ l₁ l₂ k₁ k₂))
            (mStargF P.natDegree (uRep ρ l₁ l₂ k₁ k₂))
            (Tex ρ l₁ (varphiNt (Nat.floor (a n)) k₁ t) f)
            (Tex ρ l₂ (varphitildeNt P P.natDegree (Nat.floor (a n)) k₂ t) 0) x = 0 := by
        intro t
        rw [show Tex ρ l₂ (varphitildeNt P P.natDegree (Nat.floor (a n)) k₂ t) (0 : ℤ → ℂ) = 0
          from rep_iwConv_zero_right _ _]
        simp [BtwistExact]
      simp only [h0, Pi.zero_apply]
      simp
    · rfl
  exact congrFun (congrFun h n) x

/-- With `f = 0` the repaired model tuple vanishes (pointwise). -/
theorem repModelTupleRep_zero_left (ρ : ℝ) (P : Polynomial ℤ) (C₀ : ℕ) (a : ℕ → NNReal)
    (g : ℤ → ℂ) (l₁ l₂ k₁ k₂ n : ℕ) (x : ℤ) :
    modelTupleRep ρ P C₀ a 0 g l₁ l₂ k₁ k₂ n x = 0 := by
  have h : modelTupleRep ρ P C₀ a 0 g l₁ l₂ k₁ k₂ = 0 := by
    funext n x
    simp only [modelTupleRep]
    split_ifs with h
    · have h0 : ∀ t : ℝ,
          BtwistExact ρ P l₁ l₂
            (mStarF (uRep ρ l₁ l₂ k₁ k₂))
            (mStargF P.natDegree (uRep ρ l₁ l₂ k₁ k₂))
            (Tex ρ l₁ (varphiNt (Nat.floor (a n)) k₁ t) 0)
            (Tex ρ l₂ (varphitildeNt P P.natDegree (Nat.floor (a n)) k₂ t) g) x = 0 := by
        intro t
        rw [show Tex ρ l₁ (varphiNt (Nat.floor (a n)) k₁ t) (0 : ℤ → ℂ) = 0
          from rep_iwConv_zero_right _ _]
        simp [BtwistExact]
      simp only [h0, Pi.zero_apply]
      simp
    · rfl
  exact congrFun (congrFun h n) x

/-- On `ℤ` with the counting measure a function of vanishing `ℒ^p` seminorm (`p ≠ 0`) is
identically zero. -/
theorem rep_eq_zero_of_eLpNorm_count_eq_zero {p : ENNReal} (hp : p ≠ 0) {u : ℤ → ℂ}
    (h : MeasureTheory.eLpNorm u p (MeasureTheory.Measure.count : MeasureTheory.Measure ℤ) = 0) :
    u = 0 := by
  have hsm : AEStronglyMeasurable u (MeasureTheory.Measure.count : MeasureTheory.Measure ℤ) :=
    AEStronglyMeasurable.of_discrete
  have h0 : u =ᵐ[MeasureTheory.Measure.count] 0 :=
    (MeasureTheory.eLpNorm_eq_zero_iff hp).mp h
  have hnull : MeasureTheory.Measure.count {m : ℤ | u m ≠ 0} = 0 := ae_iff.mp h0
  funext n
  by_contra hn
  have hne : MeasureTheory.Measure.count {m : ℤ | u m ≠ 0} ≠ 0 := by
    rw [MeasureTheory.Measure.count_ne_zero_iff]
    exact ⟨n, hn⟩
  exact hne hnull

/-- **The mass-bound hypothesis of the repaired §6 estimate** (the conclusion of
`RepMassBound` with the constants `A, ρ, D` fixed). -/
def RepMassHyp (P : Polynomial ℤ) (A ρ D : ℝ) : Prop :=
  ∀ (N l₁ l₂ k₁ k₂ : ℕ), 1 ≤ N → 1 ≤ l₁ → 1 ≤ l₂ →
    (k₁ : ℤ) + 1 + 2 * (uRep ρ l₁ l₂ k₁ k₂ : ℤ) ≤ logN N →
    (k₂ : ℤ) + 1 + 2 * (uRep ρ l₁ l₂ k₁ k₂ : ℤ) ≤ logN N →
    (2 : ℝ) ^ k₁ ≤ (N : ℝ) →
    (2 : ℝ) ^ (P.natDegree * k₂) ≤ (N : ℝ) ^ P.natDegree →
    NonAliasing (1 - 2 * (uRep ρ l₁ l₂ k₁ k₂ : ℤ)) (diffFreqs ρ l₁) →
    NonAliasing (1 - 2 * (uRep ρ l₁ l₂ k₁ k₂ : ℤ)) (diffFreqs ρ l₂) →
    (Summable fun p : ℤ × ℤ => ‖hiKconcN ρ P N l₁ l₂ k₁ k₂ p.1 p.2
        - hiKmodNRep ρ P N l₁ l₂ k₁ k₂ p.1 p.2‖) ∧
    (∑' p : ℤ × ℤ, ‖hiKconcN ρ P N l₁ l₂ k₁ k₂ p.1 p.2
        - hiKmodNRep ρ P N l₁ l₂ k₁ k₂ p.1 p.2‖)
      ≤ D * repWeight A ρ l₁ l₂ k₁ k₂ * ((N : ℝ))⁻¹

/-- **The single-scale estimate of §6 on the band.**  On the admissible scales of the main regime
which also satisfy the band condition, the `ℓ^p` distance between the concrete column and the
repaired model is at most `D · repWeight A ρ L · ⌊a n⌋⁻¹ ‖f‖_{p₁}‖g‖_{p₂}`. -/
theorem repSingleScale (P : Polynomial ℤ) (p₁ p₂ : ENNReal) (hdeg : 2 ≤ P.natDegree)
    (hp₁ : 1 < p₁) (htp₁ : p₁ < ⊤) (hp₂ : 1 < p₂) (htp₂ : p₂ < ⊤)
    (hsum : p₁⁻¹ + p₂⁻¹ ≤ 1)
    (A ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (D : ℝ) (hD : 0 < D) (hmass : RepMassHyp P A ρ D)
    (C₀ : ℕ) (a : ℕ → NNReal) (l₁ l₂ k₁ k₂ n : ℕ) (f g : ℤ → ℂ)
    (hl₁ : 1 ≤ l₁) (hl₂ : 1 ≤ l₂) (hf : Work.KMTAreas.A5.BoundedZ f)
    (hg : Work.KMTAreas.A5.BoundedZ g)
    (hcore : hiCore ρ P C₀ a l₁ l₂ k₁ k₂ n)
    (hband : bandCond ρ l₁ l₂ k₁ k₂ (Nat.floor (a n))) :
    MeasureTheory.eLpNorm (fun x : ℤ => mainPartTuple ρ P C₀ a f g l₁ l₂ k₁ k₂ n x
        - modelTupleRep ρ P C₀ a f g l₁ l₂ k₁ k₂ n x) (p₁⁻¹ + p₂⁻¹)⁻¹ Measure.count
      ≤ ENNReal.ofReal D * ENNReal.ofReal (repWeight A ρ l₁ l₂ k₁ k₂)
          * ENNReal.ofReal ((((Nat.floor (a n) : ℕ)) : ℝ)⁻¹)
          * (MeasureTheory.eLpNorm f p₁ Measure.count
            * MeasureTheory.eLpNorm g p₂ Measure.count) := by
  classical
  set N : ℕ := Nat.floor (a n) with hNdef
  have hguard : inIndexSet C₀ (max (l₁ : ℤ) (l₂ : ℤ)) (k₁ : ℤ) (k₂ : ℤ) N
      ∧ splitCut ρ (max (max l₁ l₂) (max k₁ k₂)) < N ∧ mainRegime ρ k₁ k₂ N := hcore
  have hN2 : 2 ≤ N := by
    have h1 : 1 ≤ splitCut ρ (max (max l₁ l₂) (max k₁ k₂)) := by
      rw [splitCut]
      exact Nat.one_le_pow _ _ (by norm_num)
    have h2 := hguard.2.1
    omega
  have hN1 : 1 ≤ N := le_trans (by norm_num) hN2
  -- the band conditions imply `2^{k₁} ≤ N` and `2^{d k₂} ≤ N^d`
  have hpow1 : 2 ^ (k₁ + 1) ≤ N := by
    have hk : (k₁ : ℤ) + 1 ≤ logN N := by
      have h := hband.1
      have hcast : (k₁ : ℤ) + 1 + 2 * (uRep ρ l₁ l₂ k₁ k₂ : ℤ) ≤ ((logN N).toNat : ℤ) := by
        exact_mod_cast h
      have htoNat : ((logN N).toNat : ℤ) ≤ logN N := by
        rw [Int.toNat_of_nonneg (logN_nonneg N)]
      have hu : (0 : ℤ) ≤ (uRep ρ l₁ l₂ k₁ k₂ : ℤ) := by positivity
      linarith
    have hk' : k₁ + 1 ≤ (logN N).toNat := by omega
    have h2 : 2 ^ Nat.log 2 (max N 2) ≤ max N 2 :=
      Nat.pow_log_le_self 2 (by omega : max N 2 ≠ 0)
    calc 2 ^ (k₁ + 1) ≤ 2 ^ ((logN N).toNat) := Nat.pow_le_pow_right (by norm_num) hk'
      _ = 2 ^ Nat.log 2 (max N 2) := by rw [logN]; simp
      _ ≤ max N 2 := h2
      _ = N := max_eq_left hN2
  have hpow2 : 2 ^ (k₂ + 1) ≤ N := by
    have hk : (k₂ : ℤ) + 1 ≤ logN N := by
      have h := hband.2
      have hcast : (k₂ : ℤ) + 1 + 2 * (uRep ρ l₁ l₂ k₁ k₂ : ℤ) ≤ ((logN N).toNat : ℤ) := by
        exact_mod_cast h
      have htoNat : ((logN N).toNat : ℤ) ≤ logN N := by
        rw [Int.toNat_of_nonneg (logN_nonneg N)]
      have hu : (0 : ℤ) ≤ (uRep ρ l₁ l₂ k₁ k₂ : ℤ) := by positivity
      linarith
    have hk' : k₂ + 1 ≤ (logN N).toNat := by omega
    have h2 : 2 ^ Nat.log 2 (max N 2) ≤ max N 2 :=
      Nat.pow_log_le_self 2 (by omega : max N 2 ≠ 0)
    calc 2 ^ (k₂ + 1) ≤ 2 ^ ((logN N).toNat) := Nat.pow_le_pow_right (by norm_num) hk'
      _ = 2 ^ Nat.log 2 (max N 2) := by rw [logN]; simp
      _ ≤ max N 2 := h2
      _ = N := max_eq_left hN2
  have h2k₁ : (2 : ℝ) ^ k₁ ≤ (N : ℝ) := by
    have := hpow1
    have h3 : 2 ^ k₁ ≤ N := by
      have : 2 ^ k₁ * 2 ≤ N := by simpa [pow_succ] using hpow1
      nlinarith [Nat.one_le_pow k₁ 2 (by norm_num)]
    exact_mod_cast h3
  have h2k₂ : (2 : ℝ) ^ (P.natDegree * k₂) ≤ (N : ℝ) ^ P.natDegree := by
    have h3 : 2 ^ k₂ ≤ N := by
      have : 2 ^ k₂ * 2 ≤ N := by simpa [pow_succ] using hpow2
      nlinarith [Nat.one_le_pow k₂ 2 (by norm_num)]
    have h4 : 2 ^ (P.natDegree * k₂) ≤ N ^ P.natDegree := by
      rw [mul_comm, pow_mul]
      exact Nat.pow_le_pow_left h3 P.natDegree
    exact_mod_cast h4
  -- the non-aliasing conditions of the repaired window
  have hna₁ : NonAliasing (1 - 2 * (uRep ρ l₁ l₂ k₁ k₂ : ℤ)) (diffFreqs ρ l₁) :=
    uRep_nonAliasing ρ hρ hρ1 l₁ l₂ k₁ k₂ l₁ (le_max_left _ _)
  have hna₂ : NonAliasing (1 - 2 * (uRep ρ l₁ l₂ k₁ k₂ : ℤ)) (diffFreqs ρ l₂) :=
    uRep_nonAliasing ρ hρ hρ1 l₁ l₂ k₁ k₂ l₂ (le_max_right _ _)
  have hbandZ₁ : (k₁ : ℤ) + 1 + 2 * (uRep ρ l₁ l₂ k₁ k₂ : ℤ) ≤ logN N := by
    have hcast : (k₁ : ℤ) + 1 + 2 * (uRep ρ l₁ l₂ k₁ k₂ : ℤ) ≤ ((logN N).toNat : ℤ) := by
      exact_mod_cast hband.1
    exact le_trans hcast (by rw [Int.toNat_of_nonneg (logN_nonneg N)])
  have hbandZ₂ : (k₂ : ℤ) + 1 + 2 * (uRep ρ l₁ l₂ k₁ k₂ : ℤ) ≤ logN N := by
    have hcast : (k₂ : ℤ) + 1 + 2 * (uRep ρ l₁ l₂ k₁ k₂ : ℤ) ≤ ((logN N).toNat : ℤ) := by
      exact_mod_cast hband.2
    exact le_trans hcast (by rw [Int.toNat_of_nonneg (logN_nonneg N)])
  obtain ⟨hsumm, hmassbd⟩ := hmass N l₁ l₂ k₁ k₂ hN1 hl₁ hl₂ hbandZ₁ hbandZ₂ h2k₁ h2k₂ hna₁ hna₂
  -- the two kernels and their mass
  set K : ℤ → ℤ → ℂ := hiKconcN ρ P N l₁ l₂ k₁ k₂ with hK
  set L : ℤ → ℤ → ℂ := hiKmodNRep ρ P N l₁ l₂ k₁ k₂ with hL
  have hKc : Summable fun p : ℤ × ℤ => ‖K p.1 p.2‖ := by
    have h := summable_hiKconc ρ P a l₁ l₂ k₁ k₂ n
    rw [hiKconc_eq ρ hρ hρ1 P a l₁ l₂ k₁ k₂ n] at h
    simpa only [hK, hNdef] using h
  have hKm : Summable fun p : ℤ × ℤ => ‖L p.1 p.2‖ := by
    refine Summable.of_nonneg_of_le (fun p => norm_nonneg _) (fun p => ?_) (hKc.add hsumm)
    have key : L p.1 p.2 = K p.1 p.2 - (K p.1 p.2 - L p.1 p.2) := by ring
    calc ‖L p.1 p.2‖ = ‖K p.1 p.2 - (K p.1 p.2 - L p.1 p.2)‖ :=
          congrArg (fun z : ℂ => ‖z‖) key
      _ ≤ ‖K p.1 p.2‖ + ‖K p.1 p.2 - L p.1 p.2‖ := norm_sub_le _ _
  -- the tuples as bilinear convolutions
  have hmain : mainPartTuple ρ P C₀ a f g l₁ l₂ k₁ k₂ n
      = bilinOp K f g := by
    funext x
    rw [mainPartTuple, if_pos hguard]
    rw [varpPiece_eq_bilinOp_hiKconc ρ P a l₁ l₂ k₁ k₂ n hf hg x,
      hiKconc_eq ρ hρ hρ1 P a l₁ l₂ k₁ k₂ n]
  have hmdl : modelTupleRep ρ P C₀ a f g l₁ l₂ k₁ k₂ n = bilinOp L f g := by
    funext x
    exact hiModelTupleRep_eq_bilinOp ρ P C₀ a l₁ l₂ k₁ k₂ n hl₁ hl₂ hf hg x hcore hband
  have hdiff : (fun x : ℤ => mainPartTuple ρ P C₀ a f g l₁ l₂ k₁ k₂ n x
        - modelTupleRep ρ P C₀ a f g l₁ l₂ k₁ k₂ n x)
      = fun x : ℤ => bilinOp (fun p₁' p₂' => K p₁' p₂' - L p₁' p₂') f g x := by
    funext x
    rw [congr_fun hmain x, congr_fun hmdl x]
    exact Work.KMTPlan.A6.vpc_bilinOp_sub hKc hKm hf.choose_spec hg.choose_spec x
  rw [hdiff]
  have hp_eq : p₁⁻¹ + p₂⁻¹ = ((p₁⁻¹ + p₂⁻¹)⁻¹)⁻¹ := (inv_inv _).symm
  have hp1' : (1 : ENNReal) ≤ (p₁⁻¹ + p₂⁻¹)⁻¹ := ENNReal.one_le_inv.mpr hsum
  refine (BilinOpLp (K := fun p₁' p₂' => K p₁' p₂' - L p₁' p₂')
    (p := (p₁⁻¹ + p₂⁻¹)⁻¹) (p₁ := p₁) (p₂ := p₂) hp_eq hp1' hsumm f g).trans ?_
  have hbound : (∑' p : ℤ × ℤ, ‖K p.1 p.2 - L p.1 p.2‖)
      ≤ D * repWeight A ρ l₁ l₂ k₁ k₂ * ((N : ℝ))⁻¹ := hmassbd
  have hDnn : 0 ≤ D := le_of_lt hD
  have hDwnn : 0 ≤ D * repWeight A ρ l₁ l₂ k₁ k₂ :=
    mul_nonneg hDnn (repWeight_nonneg A ρ l₁ l₂ k₁ k₂)
  calc ENNReal.ofReal (∑' p : ℤ × ℤ, ‖K p.1 p.2 - L p.1 p.2‖)
        * MeasureTheory.eLpNorm f p₁ MeasureTheory.Measure.count
        * MeasureTheory.eLpNorm g p₂ MeasureTheory.Measure.count
      ≤ ENNReal.ofReal (D * repWeight A ρ l₁ l₂ k₁ k₂ * ((N : ℝ))⁻¹)
        * MeasureTheory.eLpNorm f p₁ MeasureTheory.Measure.count
        * MeasureTheory.eLpNorm g p₂ MeasureTheory.Measure.count :=
        mul_le_mul' (mul_le_mul' (ENNReal.ofReal_le_ofReal hbound) le_rfl) le_rfl
    _ = ENNReal.ofReal D * ENNReal.ofReal (repWeight A ρ l₁ l₂ k₁ k₂)
          * ENNReal.ofReal ((((N : ℕ)) : ℝ)⁻¹)
          * (MeasureTheory.eLpNorm f p₁ MeasureTheory.Measure.count
            * MeasureTheory.eLpNorm g p₂ MeasureTheory.Measure.count) := by
        rw [ENNReal.ofReal_mul hDwnn, ENNReal.ofReal_mul hDnn]
        ring


end

end Work.KMTAreas.A7
