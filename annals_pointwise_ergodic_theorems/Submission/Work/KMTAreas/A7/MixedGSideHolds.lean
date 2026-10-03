/-
# The `g`-side (lin-2) estimate of the mixed range (Area A7, KMT §8)

Target: `Work.KMTAreas.A7.MixedGSideHolds`, i.e. `Work.KMTAreas.A7.MixedGSideEstimate P p₂`
(see `Submission/Work/KMTAreas/A7/LoMixedModel.lean` for the statement, and
`Submission/Work/KMTAreas/A7/MixedGSideAux.lean` for the vocabulary and the auxiliary lemmas).

This module reduces the target to **two** analytic inputs and proves the reduction:

* `Work.KMTAreas.A7.LinVarGuard P p₂` — the *linear* lacunary variational estimate for the
  guarded `g`-side family `GmixedFam` (paper `(lin-2)` without the fibre cut);
* `Work.KMTAreas.A7.FiberGuard P p₂` — the *relative* fibre estimate with the repaired window
  `loMixedU` (KMT §8, `form-1` + the quantitative Shannon sampling);
* `Work.KMTAreas.A7.MixedGSideHolds_of_pieces` — the assembly.

The argument is the paper's:

1. **`form-1` of the mixed range** (`convOp_loMixedGKer_eq_fiberSum`): the arithmetic kernel
   `loMixedGKer` is the average over the residues `n₀ < arithQ ρ l₂` of the arithmetic characters
   (`loMixedGKer_eq_fiberAvg`), so with `q = arithQ ρ l₂`,

     `convOp (loMixedGKer ρ P l₂ m₂) v x = q⁻¹ ∑_{n₀<q} fiberOpP ρ P l₂ m₂ n₀ v x`;

2. **subadditivity and Hölder in the residue variable**
   (`variationalNorm_finset_sum_le`, `inv_mul_sum_le_residueLp`):

     `V^r_n (convOp (loMixedGKer) (v n)) (x)
        ≤ residueLp p₂ (fun y n₀ ↦ V^r_n (fiberOpP n₀ (v n)) (y)) x`;

3. the `ℓ^{p₂}`-norm of the residue average is bounded by `FiberGuard`, and the `ℓ^{p₂}`-norm of
   the family itself by `LinVarGuard`; the two losses multiply
   (`lossWeight a · lossWeight b = lossWeight (a+b)`).
-/
import Mathlib
import Submission.Work.KMTAreas.A7.MixedGSideAux
import Submission.Port.Aesm

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace Work.KMTAreas.A7

noncomputable section

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal BigOperators
open PointwiseErgodicTheorems Submission.PointwiseErgodicTheorems
open Work.Analysis.IonescuWainger Work.Analysis.IWMultiplier

/-! ## §8.  The two analytic inputs -/

/-! ## §9.  The assembly -/

/-- **The mixed `g`-side estimate from its two analytic inputs.** -/
theorem MixedGSideHolds_of_pieces (P : Polynomial ℤ) (p₂ : ENNReal) (hdeg : 2 ≤ P.natDegree)
    (hp₂ : 1 < p₂) (htp₂ : p₂ < ⊤) (hlin : LinVarGuard P p₂ hdeg hp₂ htp₂)
    (hfib : FiberGuard P p₂ hdeg hp₂ htp₂) :
    MixedGSideEstimate P p₂ := by
  intro C₀ r hC₀ hr
  obtain ⟨A₁, hA₁, ρ₁, hρ₁, hlin'⟩ := hlin C₀ r hC₀ hr
  obtain ⟨A₂, hA₂, ρ₂, hρ₂, hfib'⟩ := hfib C₀ r hC₀ hr
  refine ⟨A₁ + A₂, by positivity, min ρ₁ ρ₂, lt_min hρ₁ hρ₂, ?_⟩
  intro ρ hρ hρle
  have hρ₁' : ρ ≤ ρ₁ := le_trans hρle (min_le_left _ _)
  have hρ₂' : ρ ≤ ρ₂ := le_trans hρle (min_le_right _ _)
  obtain ⟨C₁, hC₁⟩ := hlin' ρ hρ hρ₁'
  obtain ⟨C₂, hC₂⟩ := hfib' ρ hρ hρ₂'
  have hr1 : (1 : NNReal) ≤ r := le_trans (by norm_num : (1 : NNReal) ≤ 2) (le_of_lt hr)
  have hp2real : (1 : ℝ) < p₂.toReal := by
    rw [← ENNReal.toReal_one]
    exact (ENNReal.toReal_lt_toReal ENNReal.one_ne_top htp₂.ne).mpr hp₂
  have hp2ne : p₂ ≠ 0 := (lt_trans zero_lt_one hp₂).ne'
  refine ⟨fun Λ => max 1 (C₁ Λ * C₂ Λ), ?_⟩
  intro a Λ l₂ k₁ k₂ t g hΛ ha ha1 hl₂ ht
  by_cases hgT : MeasureTheory.eLpNorm g p₂ MeasureTheory.Measure.count = ⊤
  · -- the right-hand side is `⊤`
    have hK : (((max 1 (C₁ Λ * C₂ Λ) : NNReal)) : ENNReal) ≠ 0 := by
      rw [Ne, ENNReal.coe_eq_zero]
      exact ne_of_gt (lt_of_lt_of_le zero_lt_one (le_max_left _ _))
    have hL : ENNReal.ofReal (lossWeight (A₁ + A₂) ρ 0 l₂ k₁ k₂) ≠ 0 := by
      rw [Ne, ENNReal.ofReal_eq_zero, not_le]
      exact lt_of_lt_of_le zero_lt_one (one_le_lossWeight' (by positivity) hρ.le 0 l₂ k₁ k₂)
    rw [hgT, ENNReal.mul_top (mul_ne_zero hK hL)]
    exact le_top
  · -- the main case: `g` is bounded
    obtain ⟨Cg, hCg⟩ := bounded_of_eLpNorm_count_lt_top (p := p₂) hp2ne (lt_top_iff_ne_top.mpr hgT)
    have hCgbd : BddAbove (Set.range fun y : ℤ => ‖g y‖) :=
      ⟨Cg, fun b hb => by obtain ⟨z, rfl⟩ := hb; exact hCg z⟩
    -- the guarded family is pointwise bounded
    have hvbdd : ∀ n : ℕ, ∃ Bv : ℝ, ∀ y : ℤ, ‖GmixedFam ρ P C₀ a l₂ k₁ k₂ t g n y‖ ≤ Bv := by
      intro n
      by_cases hn : loGuard ρ C₀ a 0 l₂ k₁ k₂ n
      · obtain ⟨C, hC⟩ := Tm_varphitildeNt_bounded_g P ρ l₂ (Nat.floor (a n)) k₂ (by omega)
          g Cg hCg t ht
        refine ⟨max C 0, fun y => ?_⟩
        unfold GmixedFam
        rw [if_pos hn]
        exact (hC y).trans (le_max_left _ _)
      · refine ⟨0, fun y => ?_⟩
        unfold GmixedFam
        rw [if_neg hn]
        simp
    -- the pointwise bound by the residue average
    have hpt : ∀ x : ℤ, PointwiseErgodicTheorems.variationalNorm r
          (fun n : ℕ => convOp (loMixedGKer ρ P l₂ (GmixedKer ρ P l₂ k₁ k₂))
            (GmixedFam ρ P C₀ a l₂ k₁ k₂ t g n) x)
        ≤ residueLp p₂.toReal (arithQ ρ l₂)
            (GmixedFib r ρ P C₀ a l₂ k₁ k₂ t g) x := by
      intro x
      exact variationalNorm_convOp_loMixedGKer_le hr1 ρ P l₂ hl₂ p₂.toReal hp2real
        (GmixedKer ρ P l₂ k₁ k₂) (GmixedFam ρ P C₀ a l₂ k₁ k₂ t g) x
        (fun n n₀ => summable_fiber_family_of_bounded ρ P l₂ _
          (cw_mStargF_decay P.natDegree (loMixedU ρ P.natDegree l₂ k₁ k₂)) _
          (GmixedFam ρ P C₀ a l₂ k₁ k₂ t g n) (hvbdd n).choose_spec x n₀)
    -- identify the target family with the unclipped fibre average
    have hif : MeasureTheory.eLpNorm (GmixedVarTuple r ρ P C₀ a l₂ k₁ k₂ t g) p₂
          MeasureTheory.Measure.count
        = MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
            (fun n : ℕ => convOp (loMixedGKer ρ P l₂ (GmixedKer ρ P l₂ k₁ k₂))
              (GmixedFam ρ P C₀ a l₂ k₁ k₂ t g n) x)) p₂ MeasureTheory.Measure.count := by
      congr 1
      funext x
      exact variationalNorm_convOp_ite r (loMixedGKer ρ P l₂ (GmixedKer ρ P l₂ k₁ k₂))
        (fun n => loGuard ρ C₀ a 0 l₂ k₁ k₂ n)
        (fun n => Tm ρ l₂ (varphitildeNt P P.natDegree (Nat.floor (a n)) k₂ t) g) x
    have hstep1 : MeasureTheory.eLpNorm (GmixedVarTuple r ρ P C₀ a l₂ k₁ k₂ t g) p₂
          MeasureTheory.Measure.count
        ≤ MeasureTheory.eLpNorm (GmixedRes p₂ r ρ P C₀ a l₂ k₁ k₂ t g) p₂
            MeasureTheory.Measure.count := by
      rw [hif]
      exact MeasureTheory.eLpNorm_mono_enorm (hf := by pw_aesm) (p := p₂) (fun x => by
        rw [enorm_eq_self, enorm_eq_self]; exact hpt x)
    have hstep2 := hC₂ a Λ l₂ k₁ k₂ t g hΛ ha ha1 hl₂ ht hCgbd
    have hstep3 := hC₁ a Λ l₂ k₁ k₂ t g hΛ ha ha1 hl₂ ht hCgbd
    have hkey : (C₂ Λ : ENNReal) * ENNReal.ofReal (lossWeight A₂ ρ 0 l₂ k₁ k₂) *
          ((C₁ Λ : ENNReal) * ENNReal.ofReal (lossWeight A₁ ρ 0 l₂ k₁ k₂) *
            MeasureTheory.eLpNorm g p₂ MeasureTheory.Measure.count)
        = ((C₁ Λ * C₂ Λ : NNReal) : ENNReal) *
            ENNReal.ofReal (lossWeight (A₁ + A₂) ρ 0 l₂ k₁ k₂) *
            MeasureTheory.eLpNorm g p₂ MeasureTheory.Measure.count := by
      calc (C₂ Λ : ENNReal) * ENNReal.ofReal (lossWeight A₂ ρ 0 l₂ k₁ k₂) *
              ((C₁ Λ : ENNReal) * ENNReal.ofReal (lossWeight A₁ ρ 0 l₂ k₁ k₂) *
                MeasureTheory.eLpNorm g p₂ MeasureTheory.Measure.count)
          = ((C₁ Λ : ENNReal) * (C₂ Λ : ENNReal)) *
              (ENNReal.ofReal (lossWeight A₁ ρ 0 l₂ k₁ k₂) *
                ENNReal.ofReal (lossWeight A₂ ρ 0 l₂ k₁ k₂)) *
              MeasureTheory.eLpNorm g p₂ MeasureTheory.Measure.count := by ring
        _ = ((C₁ Λ : ENNReal) * (C₂ Λ : ENNReal)) *
              ENNReal.ofReal (lossWeight A₁ ρ 0 l₂ k₁ k₂ * lossWeight A₂ ρ 0 l₂ k₁ k₂) *
              MeasureTheory.eLpNorm g p₂ MeasureTheory.Measure.count := by
            rw [ENNReal.ofReal_mul (lossWeight_nonneg' A₁ ρ 0 l₂ k₁ k₂)]
        _ = ((C₁ Λ * C₂ Λ : NNReal) : ENNReal) *
              ENNReal.ofReal (lossWeight (A₁ + A₂) ρ 0 l₂ k₁ k₂) *
              MeasureTheory.eLpNorm g p₂ MeasureTheory.Measure.count := by
            rw [lossWeight_mul' A₁ A₂ ρ 0 l₂ k₁ k₂]
            push_cast
            ring
    refine hstep1.trans (hstep2.trans ?_)
    refine (mul_le_mul_of_nonneg_left hstep3 bot_le).trans ?_
    rw [hkey]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (ENNReal.coe_le_coe.mpr (le_max_right _ _)) bot_le) bot_le

/-- **The `g`-side (lin-2) estimate of the mixed range.** -/
theorem MixedGSideHolds (P : Polynomial ℤ) (p₂ : ENNReal) (hdeg : 2 ≤ P.natDegree)
    (hp₂ : 1 < p₂) (htp₂ : p₂ < ⊤) : Work.KMTAreas.A7.MixedGSideEstimate P p₂ := by
  sorry

end

end Work.KMTAreas.A7

