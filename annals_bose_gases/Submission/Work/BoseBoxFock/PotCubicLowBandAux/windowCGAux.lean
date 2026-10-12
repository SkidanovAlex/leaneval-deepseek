import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.PotCubicLowBandAux.boxSlotSumBoxT0Decomp
import Submission.Work.BoseBoxFock.PotCubicLowBandAux.nCfSecondMomentLe
import Submission.Work.BoseBoxFock.PotCubicLowBandAux.nPlusSqWindowTransport
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.PotCubicLowBandAux.windowCGAux`

The **second-moment `n₊`-window** of the cubic low band: for a state `Θ = boxRestrictC ℓ Φ` whose
`n₊`-spectrum lies in `[0, 𝓜]` (the all-moments hypothesis `hmom`), the quadratic form of the
*square* of the model excited-number operator `S = dΓ(boxT0)` is bounded by `𝓜` times the box
excited count `cnPlusC ℓ Θ`.

The proof splits into

* `boxSlotSum_boxT0_sq_le` — the second-moment comparison `⟨Θ, S²Θ⟩ ≤ ‖n₊Θ‖²`, i.e.
  `S² ≤ n₊²` at the state `Θ`, using the slot decompositions
  `S = Σ_j (A_j − P_j)` and `n₊ = Σ_j (1 − P_j)` (with `A_j = slotProj1 e j` the mode-slot
  projection and `P_j = aPC ℓ j` the condensate-slot projection) together with the box
  self-adjointness of `A_j`/`P_j` and the positivity `0 ≤ 1 − A_j`;
* `nPlusSqWindowTransport` (delegated) — the transport of the corpus's `spectralNPlusSqLe`
  `∫ n₊²Φ·Φ ≤ 𝓜 ∫ n₊Φ·Φ` to the complex `nCf`/`cnPlusC` vocabulary.

Everything is developed at the honest (measurable, everywhere bounded, box supported) bundle.
-/

namespace Work.BoseBoxFock.PotCubicLowBandAux

open MeasureTheory
open scoped BigOperators

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## 0. Data for the box restriction -/

lemma boxRestrictC_measurable' {n : ℕ} (ℓ : ℝ) {Φ : Submission.BoseGases.X n → ℝ}
    (hΦc : Continuous Φ) : Measurable (Work.BoseBoxFock.boxRestrictC ℓ Φ) := by
  have h : Work.BoseBoxFock.boxRestrictC ℓ Φ = fun x : Submission.BoseGases.X n =>
      ((Φ x : ℝ) : ℂ) *
        ((((Submission.BoseGases.abox n ℓ).indicator (fun _ => (1 : ℝ)) x : ℝ)) : ℂ) := rfl
  rw [h]
  exact (Complex.continuous_ofReal.measurable.comp hΦc.measurable).mul
    (Complex.continuous_ofReal.measurable.comp
      (measurable_const.indicator (Submission.BoseGases.abox_measurable n ℓ)))

lemma boxRestrictC_bound' {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {Φ : Submission.BoseGases.X n → ℝ}
    (hΦc : Continuous Φ) :
    ∃ C : ℝ, ∀ x, ‖Work.BoseBoxFock.boxRestrictC ℓ Φ x‖ ≤ C := by
  obtain ⟨C, hC⟩ := (Submission.BoseGases.abox_compact n hℓ).exists_bound_of_continuousOn
    hΦc.continuousOn
  refine ⟨max C 0, fun x => ?_⟩
  rw [show Work.BoseBoxFock.boxRestrictC ℓ Φ x = ((Φ x : ℝ) : ℂ) *
      ((((Submission.BoseGases.abox n ℓ).indicator (fun _ => (1 : ℝ)) x : ℝ)) : ℂ) from rfl]
  by_cases hx : x ∈ Submission.BoseGases.abox n ℓ
  · rw [Set.indicator_of_mem hx]
    simp only [Complex.ofReal_one, mul_one, Complex.norm_real]
    exact (hC x hx).trans (le_max_left _ _)
  · rw [Set.indicator_of_notMem hx]
    simp

lemma boxRestrictC_support' {n : ℕ} (ℓ : ℝ) (Φ : Submission.BoseGases.X n → ℝ) :
    Function.support (Work.BoseBoxFock.boxRestrictC ℓ Φ)
      ⊆ Submission.BoseGases.abox n ℓ := by
  intro x hx
  by_contra h
  exact hx (by
    rw [show Work.BoseBoxFock.boxRestrictC ℓ Φ x = ((Φ x : ℝ) : ℂ) *
      ((((Submission.BoseGases.abox n ℓ).indicator (fun _ => (1 : ℝ)) x : ℝ)) : ℂ) from rfl]
    rw [Set.indicator_of_notMem h]
    simp)

/-! ## 1. The second-moment comparison -/

theorem boxSlotSum_boxT0_sq_le {m n : ℕ} [NeZero m] {ℓ : ℝ} (hℓ : 0 < ℓ)
    {e : Fin m → E3 → ℂ}
    (hmeas : ∀ l, Measurable (e l)) (hbdd : ∀ l, ∃ C : ℝ, ∀ x, ‖e l x‖ ≤ C)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    (horth : ∀ l l', (∫ z : E3, star (e l z) * e l' z) = (if l = l' then (1 : ℂ) else 0))
    (hMemLp : ∀ l, MeasureTheory.MemLp (e l) ⊤)
    (hc : ∃ c : ℂ, (starRingEnd ℂ) c * c = (ℓ ^ 3)⁻¹ ∧
      e 0 =ᵐ[MeasureTheory.volume] fun x => c * Work.BoseK15.corpusBox.thetaFun ℓ x)
    {Θ : Submission.BoseGases.X n → ℂ} (hΘm : Measurable Θ)
    (hΘb : ∃ C : ℝ, ∀ x, ‖Θ x‖ ≤ C)
    (hΘsupp : Function.support Θ ⊆ Submission.BoseGases.abox n ℓ) :
    (Work.BoseDict.cIPn n Θ
        (Work.BoseDict.boxSlotSum e (Work.BoseBoxFock.boxT0 m)
          (Work.BoseDict.boxSlotSum e (Work.BoseBoxFock.boxT0 m) Θ))).re
      ≤ ∫ x in Submission.BoseGases.abox n ℓ, ‖nCf ℓ Θ x‖ ^ 2 := by
  classical
  have hdec : ∀ {d : ℕ} (Ψ : Submission.BoseGases.X d → ℂ), Measurable Ψ →
      (∃ C : ℝ, ∀ x, ‖Ψ x‖ ≤ C) → Function.support Ψ ⊆ Submission.BoseGases.abox d ℓ →
      Work.BoseDict.boxSlotSum e (Work.BoseBoxFock.boxT0 m) Ψ
        =ᵐ[(MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X d)).restrict
            (Submission.BoseGases.abox d ℓ)]
        fun x => (∑ j : Fin d, Work.BoseBoxFock.slotProj1 e j Ψ x)
          - ∑ j : Fin d, Work.BoseBoxFock.aPC ℓ j Ψ x :=
    fun Ψ hΨm hΨb hΨs => boxSlotSumBoxT0Decomp hℓ hmeas hbdd hsupp hMemLp hc hΨm hΨb hΨs
  have hΘb' : ∃ C : ℝ, ∀ x, ‖Θ x‖ ≤ C := hΘb
  obtain ⟨CΘ, hCΘ⟩ := hΘb
  have hCΘ0 : 0 ≤ CΘ := le_trans (norm_nonneg (Θ 0)) (hCΘ 0)
  have hΘmemLp : MeasureTheory.MemLp Θ (⊤ : ENNReal) :=
    MeasureTheory.memLp_top_of_bound hΘm.aestronglyMeasurable CΘ
      (Filter.Eventually.of_forall hCΘ)
  set S := Submission.BoseGases.abox n ℓ with hSdef
  set SΘ : Submission.BoseGases.X n → ℂ :=
    Work.BoseDict.boxSlotSum e (Work.BoseBoxFock.boxT0 m) Θ with hSΘdef
  obtain ⟨hSm, ⟨C1, hC10, hC1b⟩, hSsupp⟩ :=
    (Work.MB.boxSlotSum_bdd hmeas hbdd hsupp (Work.BoseBoxFock.boxT0 m)).2 Θ hΘm hΘb'
  have hSsupp' : Function.support SΘ ⊆ S := by
    have hmem : Function.support Θ ⊆ Work.MB.boxPow n ℓ := by
      rw [boxPow_eq_abox hℓ]; exact hΘsupp
    have h := hSsupp hmem
    rw [boxPow_eq_abox hℓ] at h
    rw [hSdef, hSΘdef]
    exact h
  have bΘ : AEStronglyMeasurable Θ
        (MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X n)) ∧
      (∃ C : ℝ, ∀ x, ‖Θ x‖ ≤ C) := ⟨hΘm.aestronglyMeasurable, ⟨CΘ, hCΘ⟩⟩
  have bS : AEStronglyMeasurable SΘ
        (MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X n)) ∧
      (∃ C : ℝ, ∀ x, ‖SΘ x‖ ≤ C) := ⟨hSm.aestronglyMeasurable, ⟨C1, hC1b⟩⟩
  have bAΘ : ∀ j : Fin n, AEStronglyMeasurable (Work.BoseBoxFock.slotProj1 e j Θ)
        (MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X n)) ∧
      (∃ C : ℝ, ∀ x, ‖Work.BoseBoxFock.slotProj1 e j Θ x‖ ≤ C) := fun j => by
    have hweak := Work.MB.slotProj_mb_weak hmeas hbdd hsupp {j} hΘm hΘb'
    rw [Work.BoseBoxFock.slotProj_singleton_eq_slotProj1_aux] at hweak
    exact ⟨hweak.1.aestronglyMeasurable, hweak.2⟩
  have bAS : ∀ j : Fin n, AEStronglyMeasurable (Work.BoseBoxFock.slotProj1 e j SΘ)
        (MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X n)) ∧
      (∃ C : ℝ, ∀ x, ‖Work.BoseBoxFock.slotProj1 e j SΘ x‖ ≤ C) := fun j => by
    have hweak := Work.MB.slotProj_mb_weak hmeas hbdd hsupp {j} hSm ⟨C1, hC1b⟩
    rw [Work.BoseBoxFock.slotProj_singleton_eq_slotProj1_aux] at hweak
    exact ⟨hweak.1.aestronglyMeasurable, hweak.2⟩
  have bPΘ : ∀ j : Fin n, AEStronglyMeasurable (Work.BoseBoxFock.aPC ℓ j Θ)
        (MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X n)) ∧
      (∃ C : ℝ, ∀ x, ‖Work.BoseBoxFock.aPC ℓ j Θ x‖ ≤ C) := fun j =>
    ⟨Work.BoseBoxFock.aPC_aesm_full ℓ j hΘm.aestronglyMeasurable,
      ⟨CΘ, fun x => Work.BoseBoxFock.norm_aPC_le hℓ j hCΘ0 hCΘ x⟩⟩
  have bPS : ∀ j : Fin n, AEStronglyMeasurable (Work.BoseBoxFock.aPC ℓ j SΘ)
        (MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X n)) ∧
      (∃ C : ℝ, ∀ x, ‖Work.BoseBoxFock.aPC ℓ j SΘ x‖ ≤ C) := fun j =>
    ⟨Work.BoseBoxFock.aPC_aesm_full ℓ j hSm.aestronglyMeasurable,
      ⟨C1, fun x => Work.BoseBoxFock.norm_aPC_le hℓ j hC10 hC1b x⟩⟩
  set u : Submission.BoseGases.X n → ℂ :=
    fun x => ∑ j : Fin n,
      (Work.BoseBoxFock.slotProj1 e j Θ x - Work.BoseBoxFock.aPC ℓ j Θ x) with hu
  have huA : AEStronglyMeasurable u
      (MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X n)) := by
    have h : AEStronglyMeasurable (∑ j : Fin n,
        fun x => (Work.BoseBoxFock.slotProj1 e j Θ x - Work.BoseBoxFock.aPC ℓ j Θ x)) _ :=
      Finset.aestronglyMeasurable_sum (Finset.univ : Finset (Fin n))
        (fun j _ => (bAΘ j).1.sub (bPΘ j).1)
    have h2 : (∑ j : Fin n, fun x =>
          (Work.BoseBoxFock.slotProj1 e j Θ x - Work.BoseBoxFock.aPC ℓ j Θ x))
        = fun x => ∑ j : Fin n,
          (Work.BoseBoxFock.slotProj1 e j Θ x - Work.BoseBoxFock.aPC ℓ j Θ x) := by
      funext x
      rw [Finset.sum_apply]
    rw [h2] at h
    exact h
  choose DA hDA using fun j : Fin n => (bAΘ j).2
  have huB : ∃ C : ℝ, ∀ x, ‖u x‖ ≤ C := by
    refine ⟨∑ j : Fin n, (DA j + CΘ), fun x => ?_⟩
    show ‖∑ j : Fin n, (Work.BoseBoxFock.slotProj1 e j Θ x - Work.BoseBoxFock.aPC ℓ j Θ x)‖
      ≤ ∑ j : Fin n, (DA j + CΘ)
    calc ‖∑ j : Fin n, (Work.BoseBoxFock.slotProj1 e j Θ x - Work.BoseBoxFock.aPC ℓ j Θ x)‖
        ≤ ∑ j : Fin n, ‖Work.BoseBoxFock.slotProj1 e j Θ x - Work.BoseBoxFock.aPC ℓ j Θ x‖ :=
          norm_sum_le _ _
      _ ≤ ∑ j : Fin n, (DA j + CΘ) := Finset.sum_le_sum (fun j _ =>
            le_trans (norm_sub_le _ _)
              (add_le_add (hDA j x) (Work.BoseBoxFock.norm_aPC_le hℓ j hCΘ0 hCΘ x)))
  have bU : AEStronglyMeasurable u
        (MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X n)) ∧
      (∃ C : ℝ, ∀ x, ‖u x‖ ≤ C) := ⟨huA, huB⟩
  have int2 : ∀ {f g : Submission.BoseGases.X n → ℂ},
      AEStronglyMeasurable f (MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X n)) →
      (∃ C : ℝ, ∀ x, ‖f x‖ ≤ C) →
      AEStronglyMeasurable g (MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X n)) →
      (∃ C : ℝ, ∀ x, ‖g x‖ ≤ C) →
      MeasureTheory.Integrable (fun x => star (f x) * g x)
        ((MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X n)).restrict S) :=
    fun hf hfb hg hgb => integrableOn_star_mul_bdd hℓ hf hfb hg hgb
  -- beta-reduced forms of the a.e. decompositions
  have hdecΘ : ∀ᵐ x ∂(MeasureTheory.volume : MeasureTheory.Measure
      (Submission.BoseGases.X n)).restrict S,
      SΘ x = (∑ j : Fin n, Work.BoseBoxFock.slotProj1 e j Θ x)
          - ∑ j : Fin n, Work.BoseBoxFock.aPC ℓ j Θ x := by
    have h := hdec Θ hΘm hΘb' hΘsupp
    filter_upwards [h] with x hx
    rw [show SΘ = Work.BoseDict.boxSlotSum e (Work.BoseBoxFock.boxT0 m) Θ from hSΘdef]
    exact hx
  have hdecSΘ : ∀ᵐ x ∂(MeasureTheory.volume : MeasureTheory.Measure
      (Submission.BoseGases.X n)).restrict S,
      Work.BoseDict.boxSlotSum e (Work.BoseBoxFock.boxT0 m) SΘ x
        = (∑ j : Fin n, Work.BoseBoxFock.slotProj1 e j SΘ x)
          - ∑ j : Fin n, Work.BoseBoxFock.aPC ℓ j SΘ x := by
    have h := hdec SΘ hSm ⟨C1, hC1b⟩ hSsupp'
    filter_upwards [h] with x hx
    exact hx
  have huae : SΘ =ᵐ[(MeasureTheory.volume : MeasureTheory.Measure
      (Submission.BoseGases.X n)).restrict S] u := by
    filter_upwards [hdecΘ] with x hx
    show SΘ x = u x
    rw [hx, hu]
    show (∑ j : Fin n, Work.BoseBoxFock.slotProj1 e j Θ x)
        - ∑ j : Fin n, Work.BoseBoxFock.aPC ℓ j Θ x
      = ∑ j : Fin n, (Work.BoseBoxFock.slotProj1 e j Θ x - Work.BoseBoxFock.aPC ℓ j Θ x)
    exact (Finset.sum_sub_distrib _ _).symm
  -- ## PART 1: the left side is `∫_S ‖u‖²`
  have hP1 : (Work.BoseDict.cIPn n Θ
        (Work.BoseDict.boxSlotSum e (Work.BoseBoxFock.boxT0 m) SΘ)).re
      = ∫ x in S, ‖u x‖ ^ 2 := by
    have hcx : Work.BoseDict.cIPn n Θ
          (Work.BoseDict.boxSlotSum e (Work.BoseBoxFock.boxT0 m) SΘ)
        = ∫ x in S, star (u x) * u x := by
      rw [Work.BoseDict.cIPn]
      simp only [starRingEnd_apply]
      rw [(MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero (s := S)
        (f := fun x => star (Θ x)
          * Work.BoseDict.boxSlotSum e (Work.BoseBoxFock.boxT0 m) SΘ x) (fun x hx => by
          have h0 : Θ x = 0 := by
            by_contra h
            exact hx (hΘsupp (Function.mem_support.mpr h))
          rw [h0, star_zero, zero_mul])).symm]
      -- (a)
      trans ∫ x in S, ∑ j : Fin n, (star (Θ x)
            * Work.BoseBoxFock.slotProj1 e j SΘ x
          - star (Θ x) * Work.BoseBoxFock.aPC ℓ j SΘ x)
      · refine MeasureTheory.integral_congr_ae ?_
        filter_upwards [hdecSΘ] with x hx
        rw [hx]
        show star (Θ x)
            * ((∑ j : Fin n, Work.BoseBoxFock.slotProj1 e j SΘ x)
              - ∑ j : Fin n, Work.BoseBoxFock.aPC ℓ j SΘ x)
          = ∑ j : Fin n, (star (Θ x) * Work.BoseBoxFock.slotProj1 e j SΘ x
              - star (Θ x) * Work.BoseBoxFock.aPC ℓ j SΘ x)
        rw [mul_sub, Finset.mul_sum, Finset.mul_sum, Finset.sum_sub_distrib]
      -- (b)
      trans ∑ j : Fin n, ∫ x in S, (star (Θ x)
              * Work.BoseBoxFock.slotProj1 e j SΘ x
            - star (Θ x) * Work.BoseBoxFock.aPC ℓ j SΘ x)
      · exact MeasureTheory.integral_finsetSum _
          (fun j _ => (int2 (bΘ.1) bΘ.2 (bAS j).1 (bAS j).2).sub
            (int2 (bΘ.1) bΘ.2 (bPS j).1 (bPS j).2))
      -- (c)
      trans ∑ j : Fin n, ∫ x in S,
          star (Work.BoseBoxFock.slotProj1 e j Θ x
              - Work.BoseBoxFock.aPC ℓ j Θ x) * SΘ x
      · refine Finset.sum_congr rfl (fun j _ => ?_)
        rw [MeasureTheory.integral_sub
            (int2 (bΘ.1) bΘ.2 (bAS j).1 (bAS j).2)
            (int2 (bΘ.1) bΘ.2 (bPS j).1 (bPS j).2),
          ← slotProj1_box_adjoint hℓ hmeas hbdd hsupp j hΘm hΘb' hSm ⟨C1, hC1b⟩,
          ← aPC_box_adjoint hℓ j hΘm hΘb' hSm ⟨C1, hC1b⟩,
          ← MeasureTheory.integral_sub
            (int2 (bAΘ j).1 (bAΘ j).2 (bS.1) (bS.2))
            (int2 (bPΘ j).1 (bPΘ j).2 (bS.1) (bS.2))]
        refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
        show star (Work.BoseBoxFock.slotProj1 e j Θ x) * SΘ x
              - star (Work.BoseBoxFock.aPC ℓ j Θ x) * SΘ x
            = star (Work.BoseBoxFock.slotProj1 e j Θ x
                - Work.BoseBoxFock.aPC ℓ j Θ x) * SΘ x
        rw [star_sub, sub_mul]
      -- (d)
      trans ∫ x in S, star (u x) * SΘ x
      · rw [← MeasureTheory.integral_finsetSum]
        · refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
          show (∑ j : Fin n, star (Work.BoseBoxFock.slotProj1 e j Θ x
                - Work.BoseBoxFock.aPC ℓ j Θ x) * SΘ x) = star (u x) * SΘ x
          rw [hu]
          simp only [Finset.sum_apply]
          rw [star_sum, Finset.sum_mul]
        · intro j _
          exact int2 ((bAΘ j).1.sub (bPΘ j).1)
            ⟨DA j + CΘ, fun x => le_trans (norm_sub_le _ _)
              (add_le_add (hDA j x) (Work.BoseBoxFock.norm_aPC_le hℓ j hCΘ0 hCΘ x))⟩
            (bS.1) (bS.2)
      -- (e)
      · refine MeasureTheory.integral_congr_ae ?_
        filter_upwards [huae] with x hx
        rw [hx]
    rw [hcx]
    have hInt : MeasureTheory.Integrable (fun x => star (u x) * u x)
        ((MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X n)).restrict S) :=
      int2 bU.1 bU.2 bU.1 bU.2
    rw [Work.BoseBoxFock.setIntegral_re_complex_xn S _ hInt]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
    show (star (u x) * u x).re = ‖u x‖ ^ 2
    rw [Work.BoseBoxFock.sq_norm_eq_re_sq_add_im_sq (u x)]
    simp only [Complex.star_def, Complex.mul_re, Complex.conj_re, Complex.conj_im]
    ring
  -- ## PART 2 (delegated): the second-moment slot comparison
  have hP2 : (∫ x in S, ‖u x‖ ^ 2)
      ≤ ∫ x in S, ‖nCf ℓ Θ x‖ ^ 2 := by
    have h := nCfSecondMomentLe (m := m) (n := n) hℓ hmeas hbdd hsupp horth hMemLp hc
      hΘm hΘb' hΘsupp
    simpa only [hu] using h
  rw [hP1]
  exact hP2

/-! ## 2. The target -/

theorem windowCGAux {m n : ℕ} [NeZero m] {ℓ 𝓜 : ℝ} (hℓ : 0 < ℓ) (h𝓜 : 0 ≤ 𝓜)
    {e : Fin m → EuclideanSpace ℝ (Fin 3) → ℂ}
    (hmeas : ∀ l, Measurable (e l)) (hbdd : ∀ l, ∃ C : ℝ, ∀ x, ‖e l x‖ ≤ C)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    (horth : ∀ l l', (∫ z : EuclideanSpace ℝ (Fin 3), star (e l z) * e l' z)
      = (if l = l' then (1 : ℂ) else 0))
    (hMemLp : ∀ l, MeasureTheory.MemLp (e l) ⊤)
    (hc : ∃ c : ℂ, (starRingEnd ℂ) c * c = (ℓ ^ 3)⁻¹ ∧
      e 0 =ᵐ[MeasureTheory.volume] fun x => c * Work.BoseK15.corpusBox.thetaFun ℓ x)
    {Φ : Submission.BoseGases.X n → ℝ} (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ)
    (hmom : ∀ k : ℕ, ∫ x in Submission.BoseGases.abox n ℓ,
        Work.BoseBox.nPlusPow ℓ n k Φ x * Φ x
      ≤ 𝓜 ^ k * ∫ x in Submission.BoseGases.abox n ℓ, (Φ x) ^ 2) :
    (Work.BoseDict.cIPn n (Work.BoseBoxFock.boxRestrictC ℓ Φ)
        (Work.BoseDict.boxSlotSum e (Work.BoseBoxFock.boxT0 m)
          (Work.BoseDict.boxSlotSum e (Work.BoseBoxFock.boxT0 m)
            (Work.BoseBoxFock.boxRestrictC ℓ Φ)))).re
      ≤ 𝓜 * Work.BoseBoxFock.cnPlusC ℓ (Work.BoseBoxFock.boxRestrictC ℓ Φ) := by
  have h1 := boxSlotSum_boxT0_sq_le (m := m) (n := n) hℓ hmeas hbdd hsupp horth hMemLp hc
    (boxRestrictC_measurable' ℓ hΦ.continuous)
    (boxRestrictC_bound' hℓ hΦ.continuous)
    (boxRestrictC_support' ℓ Φ)
  have h2 := nPlusSqWindowTransport (n := n) hℓ h𝓜 hΦ hmom
  exact le_trans h1 h2

end Work.BoseBoxFock.PotCubicLowBandAux
