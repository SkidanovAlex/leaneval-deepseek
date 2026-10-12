import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.BoseKinLoc.Kinetic.fibre_lift_general
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseFixKin.Kinetic

noncomputable section

open MeasureTheory
open scoped ContDiff Topology Real BigOperators ENNReal

open Submission.BoseGases Work.BoseKinLoc.Kinetic

/-- **The `N`-body lifting from a pointwise one-body bound** (node G2 of `BOSE_BCLASH_LEAD.md`).

This is `Work.BoseKinLoc.Kinetic.fibre_lift_general` with the two hypotheses `hKin` (a
`KineticLocalisation c₀`) and `hreg` (a `KinRegime c₀` block) replaced by the single unpacked
one-body hypothesis `hKin1` plus `hℓ : 0 < ℓ`, `hd : 0 < d`.  The proof is a *copy* of that file's
proof: `fibre_lift_general` is proved by peeling to the fibre `genFibre i Φ r` and applying
`hKin ℓ d s εT b hreg`; here one applies `hKin1` instead, obtaining `hℓ`/`hd` from the new
hypotheses.  All helpers used in that proof (`genFibre_contDiff`,
`genFibre_hasCompactSupport_of_supp`, `neuFrac_Qfree_fibre_aemeasurable_alt`,
`exists_abs_bound_of_tsupport_subset_abox`, `slotForm_eq_fibre_integral`, `dSpace_fibre_eq`,
`integral_fibre_sq`, `fsT_bound_abs`, `fsT_fibre_eq_zero_of_not_mem_coverBoxU`) are public. -/
theorem fibre_lift_pt {N : ℕ} {ℓ L d s εT b : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d)
    (hKin1 : ∀ ψ : ℝ³ → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      Integrable (fun u : ℝ³ => Work.BoseKinLoc.fsT ℓ d s εT b u ψ) →
        ∫ u : ℝ³, Work.BoseKinLoc.fsT ℓ d s εT b u ψ ≤ Work.BSKinetic.dSpace ψ)
    (hL : 0 ≤ L) {Φ : Submission.BoseGases.X N → ℝ} (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ)
    (hsupp : tsupport Φ ⊆ Submission.BoseGases.abox N L)
    (hint : Integrable (fun u : ℝ³ => Work.BoseKinLoc.kinForm N ℓ d s εT b u Φ)) :
    (∫ u : ℝ³, Work.BoseKinLoc.kinForm N ℓ d s εT b u Φ)
      ≤ ∑ i : Fin N, ∫ x : Submission.BoseGases.X N, ∑ k : Fin 3,
          (fderiv ℝ Φ x (Submission.BoseGases.kcDir N i k)) ^ 2 := by
  rcases N with _ | n
  · -- no particles: both sides vanish
    simp [Work.BoseKinLoc.kinForm]
  have hcsΦ : HasCompactSupport Φ :=
    IsCompact.of_isClosed_subset (abox_compact_of_nonneg (n + 1) hL) (isClosed_tsupport Φ) hsupp
  -- the absolute one-body bound, using the pointwise momentum bound
  obtain ⟨C, hC0, hCbd⟩ := Work.BoseKinLoc.Kinetic.fsT_bound_abs (ℓ := ℓ) (d := d) (s := s)
    (εT := εT) (b := b) hℓ hd (fun u ψ hψ hcs =>
      Work.BoseKinLoc.Kinetic.momForm_le_box hℓ hd u hψ hcs)
  -- the support estimate: `Λ(u)` can only meet `acube L` for `u ∈ acube ((L+ℓ)/ℓ)`
  have hKnn : 0 ≤ (L + ℓ) / ℓ := by positivity
  have hcov_sub : Work.BoseKinLoc.Compare.coverBoxU ℓ L
      ⊆ Submission.BoseGases.acube ((L + ℓ) / ℓ) := by
    intro u hu
    rw [Submission.BoseGases.mem_acube_iff]
    intro k
    have h := (Work.BoseKinLoc.Compare.mem_coverBoxU_iff hℓ hL u).mp hu k
    have h2 : -((L + ℓ) / (2 * ℓ)) ≤ u k ∧ u k ≤ (L + ℓ) / (2 * ℓ) := abs_le.mp h
    rw [Set.mem_Icc]
    constructor
    · have h3 : -((L + ℓ) / ℓ) / 2 = -((L + ℓ) / (2 * ℓ)) := by ring
      linarith [h3, h2.1]
    · have h3 : ((L + ℓ) / ℓ) / 2 = (L + ℓ) / (2 * ℓ) := by ring
      linarith [h3, h2.2]
  -- a global bound for `Φ` (used by the measurability of the `sInf`)
  obtain ⟨MΦ, hMΦ⟩ := exists_abs_bound_of_tsupport_subset_abox (n := n) (L := L) hL hΦ hsupp
  -- the per-slot estimate
  have hstep : ∀ i : Fin (n + 1),
      MeasureTheory.Integrable (fun u : ℝ³ =>
          Work.BoseKinLoc.slotForm (n + 1) (Work.BoseKinLoc.fsT ℓ d s εT b u) ℓ u i Φ)
        ∧ (∫ u : ℝ³, Work.BoseKinLoc.slotForm (n + 1)
              (Work.BoseKinLoc.fsT ℓ d s εT b u) ℓ u i Φ)
            ≤ ∫ r : Submission.BoseGases.X n, Work.BSKinetic.dSpace (genFibre i Φ r) := by
    intro i
    set F : ℝ³ → Submission.BoseGases.X n → ℝ := fun u r =>
      Work.BoseKinLoc.fsT ℓ d s εT b u (genFibre i Φ r) with hF
    -- the peel
    have hpeel : ∀ u : ℝ³, Work.BoseKinLoc.slotForm (n + 1)
        (Work.BoseKinLoc.fsT ℓ d s εT b u) ℓ u i Φ = ∫ r : Submission.BoseGases.X n, F u r := by
      intro u
      rw [Work.BoseKinLoc.Kinetic.slotForm_eq_fibre_integral hℓ
        (Work.BoseKinLoc.fsT ℓ d s εT b u) u i Φ]
      rfl
    -- the majorant
    set M : Submission.BoseGases.X n → ℝ := fun r => (∫ z : ℝ³, (genFibre i Φ r z) ^ 2)
      + ∑ k : Fin 3, ∫ z : ℝ³,
          (fderiv ℝ (genFibre i Φ r) z (Submission.BoseGases.kcStdBasis k)) ^ 2 with hM
    have hAint : MeasureTheory.Integrable (fun r : Submission.BoseGases.X n =>
        ∫ z : ℝ³, (genFibre i Φ r z) ^ 2) :=
      (Work.BoseKinLoc.Kinetic.integral_fibre_sq (n := n) hΦ hcsΦ i).1.congr
        (Filter.Eventually.of_forall (fun r => rfl))
    have hDint : MeasureTheory.Integrable (fun r : Submission.BoseGases.X n =>
        Work.BSKinetic.dSpace (genFibre i Φ r)) :=
      (Work.BoseKinLoc.Kinetic.dSpace_fibre_eq (n := n) hΦ hcsΦ i).1
    have hMint : MeasureTheory.Integrable M := by
      rw [hM]
      exact hAint.add (by simpa only [Work.BSKinetic.dSpace] using hDint)
    -- joint measurability
    have hmeas : MeasureTheory.AEStronglyMeasurable (Function.uncurry F)
        ((volume : Measure ℝ³).prod (volume : Measure (Submission.BoseGases.X n))) := by
      have h1 : MeasureTheory.AEStronglyMeasurable (fun q : ℝ³ × Submission.BoseGases.X n =>
          Work.BoseKinLoc.neuFrac ℓ ((d * ℓ) ^ (-2 : ℤ)) q.1
            (Work.BoseKinLoc.Qfree ℓ q.1 (genFibre i Φ q.2)))
          ((volume : Measure ℝ³).prod (volume : Measure (Submission.BoseGases.X n))) := by
        show MeasureTheory.AEStronglyMeasurable (fun q : ℝ³ × Submission.BoseGases.X n =>
            Work.BoseKinLoc.neuFrac ℓ ((d * ℓ) ^ (-2 : ℤ)) q.1
              (Work.BoseKinLoc.Qfree ℓ q.1 (fun z : ℝ³ =>
                Φ (Submission.BoseGases.kcInsN n i (z, q.2)))))
            ((volume : Measure ℝ³).prod (volume : Measure (Submission.BoseGases.X n)))
        exact neuFrac_Qfree_fibre_aemeasurable_alt (ℓ := ℓ) (a2 := (d * ℓ) ^ (-2 : ℤ))
          (M := MΦ) (L := L) hℓ (by positivity) hL hΦ hMΦ hsupp i
      have h2 := Work.BoseKinLoc.Kinetic.gapBare_fibre_aemeasurable (ℓ := ℓ) hΦ i
      have h3 := Work.BoseKinLoc.Kinetic.momForm_fibre_aemeasurable (ℓ := ℓ) (d := d) hΦ i
      have h4 := Work.BoseKinLoc.Kinetic.mainWord_fibre_aemeasurable (ℓ := ℓ) (d := d)
        (s := s) (εT := εT) hΦ i
      have hsum : MeasureTheory.AEStronglyMeasurable (fun q : ℝ³ × Submission.BoseGases.X n =>
          Work.BoseKinLoc.neuWord ℓ d εT q.1 (genFibre i Φ q.2)
            + Work.BoseKinLoc.gapWord ℓ b q.1 (genFibre i Φ q.2)
            + Work.BoseKinLoc.momWord ℓ d εT b q.1 (genFibre i Φ q.2)
            + Work.BoseKinLoc.mainWord ℓ d s εT q.1 (genFibre i Φ q.2))
          ((volume : Measure ℝ³).prod (volume : Measure (Submission.BoseGases.X n))) :=
        (((h1.const_mul ((1 / 2) * εT * (d * ℓ) ^ (-2 : ℤ))).add
          (h2.const_mul (b * ℓ ^ (-2 : ℤ)))).add
          (h3.const_mul (b * εT * (d * ℓ) ^ (-2 : ℤ)))).add h4
      refine hsum.congr (Filter.Eventually.of_forall (fun q => ?_))
      exact (Work.BoseKinLoc.fsT_eq_sum ℓ d s εT b q.1 (genFibre i Φ q.2)).symm
    -- the majorant is integrable
    have hind : MeasureTheory.Integrable (fun u : ℝ³ =>
        C * (Submission.BoseGases.acube ((L + ℓ) / ℓ)).indicator (fun _ => (1 : ℝ)) u) := by
      refine MeasureTheory.Integrable.const_mul ?_ C
      rw [integrable_indicator_iff (Submission.BoseGases.acube_measurable _)]
      exact integrableOn_const (by
        rw [Submission.BoseGases.acube_volume _ hKnn]
        exact ENNReal.ofReal_lt_top.ne) (by simp)
    have hGint : MeasureTheory.Integrable (fun q : ℝ³ × Submission.BoseGases.X n =>
        (C * (Submission.BoseGases.acube ((L + ℓ) / ℓ)).indicator (fun _ => (1 : ℝ)) q.1) * M q.2)
        ((volume : Measure ℝ³).prod (volume : Measure (Submission.BoseGases.X n))) :=
      MeasureTheory.Integrable.mul_prod hind hMint
    have hFint : MeasureTheory.Integrable (Function.uncurry F)
        ((volume : Measure ℝ³).prod (volume : Measure (Submission.BoseGases.X n))) := by
      refine MeasureTheory.Integrable.mono' hGint hmeas
        (Filter.Eventually.of_forall (fun q => ?_))
      obtain ⟨u, r⟩ := q
      change ‖F u r‖ ≤
        (C * (Submission.BoseGases.acube ((L + ℓ) / ℓ)).indicator (fun _ => (1 : ℝ)) u) * M r
      by_cases hu : u ∈ Work.BoseKinLoc.Compare.coverBoxU ℓ L
      · have hb := hCbd u (genFibre i Φ r) (genFibre_contDiff hΦ i r)
          (genFibre_hasCompactSupport_of_supp hL hsupp i r)
        rw [Set.indicator_of_mem (hcov_sub hu), mul_one]
        simpa only [hF, hM, Real.norm_eq_abs] using hb
      · have hzero : F u r = 0 := by
          have hzero' := Work.BoseKinLoc.Compare.fsT_fibre_eq_zero_of_not_mem_coverBoxU
            (N := n + 1) (ℓ := ℓ) (L := L) (d := d) (s := s) (εT := εT) (b := b)
            hℓ hsupp hu (Submission.BoseGases.kcInsN n i (0, r)) i
          have hfun : genFibre i Φ r
              = Work.BoseKinLoc.fibre (n + 1) i Φ (Submission.BoseGases.kcInsN n i (0, r)) :=
            funext (fun z => genFibre_eq_fibre i Φ r 0 z)
          change Work.BoseKinLoc.fsT ℓ d s εT b u (genFibre i Φ r) = 0
          rw [hfun]
          exact hzero'
        rw [hzero, norm_zero]
        have hMnn : 0 ≤ M r := by
          rw [hM]
          refine add_nonneg (integral_nonneg (fun z => sq_nonneg _))
            (Finset.sum_nonneg (fun k _ => integral_nonneg (fun z => sq_nonneg _)))
        have hindnn : 0 ≤ (Submission.BoseGases.acube ((L + ℓ) / ℓ)).indicator
            (fun _ => (1 : ℝ)) u := Set.indicator_nonneg (fun _ _ => zero_le_one) u
        exact mul_nonneg (mul_nonneg hC0 hindnn) hMnn
    -- assemble
    have hper : ∀ᵐ r ∂(volume : Measure (Submission.BoseGases.X n)),
        MeasureTheory.Integrable (fun u : ℝ³ => F u r) :=
      ((MeasureTheory.integrable_prod_iff' hmeas).1 hFint).1
    refine ⟨hFint.integral_prod_left.congr
      (Filter.Eventually.of_forall (fun u => (hpeel u).symm)), ?_⟩
    calc (∫ u : ℝ³, Work.BoseKinLoc.slotForm (n + 1)
            (Work.BoseKinLoc.fsT ℓ d s εT b u) ℓ u i Φ)
        = ∫ u : ℝ³, ∫ r : Submission.BoseGases.X n, F u r :=
          MeasureTheory.integral_congr_ae
            (Filter.Eventually.of_forall (fun u => hpeel u))
      _ = ∫ r : Submission.BoseGases.X n, ∫ u : ℝ³, F u r :=
          MeasureTheory.integral_integral_swap hFint
      _ ≤ ∫ r : Submission.BoseGases.X n, Work.BSKinetic.dSpace (genFibre i Φ r) := by
          refine MeasureTheory.integral_mono_ae hFint.integral_prod_right hDint ?_
          filter_upwards [hper] with r hr
          exact hKin1 (genFibre i Φ r)
            (genFibre_contDiff hΦ i r) (genFibre_hasCompactSupport_of_supp hL hsupp i r) hr
  calc (∫ u : ℝ³, Work.BoseKinLoc.kinForm (n + 1) ℓ d s εT b u Φ)
      = ∑ i : Fin (n + 1), ∫ u : ℝ³,
          Work.BoseKinLoc.slotForm (n + 1) (Work.BoseKinLoc.fsT ℓ d s εT b u) ℓ u i Φ := by
        simp_rw [Work.BoseKinLoc.kinForm_eq]
        exact MeasureTheory.integral_finsetSum _ (fun i _ => (hstep i).1)
    _ ≤ ∑ i : Fin (n + 1), ∫ r : Submission.BoseGases.X n,
          Work.BSKinetic.dSpace (genFibre i Φ r) :=
        Finset.sum_le_sum (fun i _ => (hstep i).2)
    _ = ∑ i : Fin (n + 1), ∫ x : Submission.BoseGases.X (n + 1), ∑ k : Fin 3,
          (fderiv ℝ Φ x (Submission.BoseGases.kcDir (n + 1) i k)) ^ 2 := by
        refine Finset.sum_congr rfl (fun i _ => ?_)
        exact (Work.BoseKinLoc.Kinetic.dSpace_fibre_eq (n := n) hΦ hcsΦ i).2.symm

end

end Work.BoseFixKin.Kinetic
