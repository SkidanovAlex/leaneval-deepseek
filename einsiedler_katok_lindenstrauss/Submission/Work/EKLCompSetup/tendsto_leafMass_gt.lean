import Mathlib
import Submission.Work.EKLComp.C8Defs

/-!
# Right-continuity of the leaf mass in the radius

`Work.EKLComp.leafMass ν S R x = ∫⁻ g in ballU h01 R, 1_S (g • x) ∂(ν x)` is the `ν x`-mass of
the part of the plaque `ballU h01 R` through `x` that is sent into `S`.  Since
`ballU h01 R = {u_01(t) | t ∈ [-R,R]}` is a *compact* neighbourhood which grows with `R`, and
`(ν x)` is finite on compact sets, this mass is continuous from the right in `R`:

`leafMass ν S r x → leafMass ν S R x` as `r ↓ R`.

The proof is the standard continuity from above of a measure along the decreasing family
`r ↦ ballU h01 r ∩ {g | g • x ∈ S}` (`r` decreasing to `R`): every member is contained in the
compact set `ballU h01 (R+1)` of finite `ν x`-measure, and the intersection of the family is
`ballU h01 R ∩ {g | g • x ∈ S}` because `ballU h01 R` is closed (equivalently, because the
parameter of `u_01` is continuous).  The link between the leaf mass and the measure of that
intersection is `MeasureTheory.lintegral_indicator_const` together with
`Measure.restrict_apply`.

Nothing beyond `MeasurableSet S` and `IsFiniteMeasureOnCompacts (ν x)` is used, so the lemma
applies to an arbitrary weakly measurable leafwise family.
-/

open MeasureTheory Filter Topology
open scoped ENNReal Matrix

noncomputable section

namespace Work.EKLCompSetup

theorem tendsto_leafMass_gt
    {ν : Work.EKLContract.X3 → MeasureTheory.Measure Work.EKLContract.SL3}
    (hν : ∀ x, MeasureTheory.IsFiniteMeasureOnCompacts (ν x))
    {X₁ : Set Work.EKLContract.X3} (hX₁ : MeasurableSet X₁) (R : ℝ) (x : Work.EKLContract.X3) :
    Filter.Tendsto (fun r : ℝ => Work.EKLComp.leafMass ν X₁ r x)
      (nhdsWithin R (Set.Ioi R)) (nhds (Work.EKLComp.leafMass ν X₁ R x)) := by
  classical
  -- The set of group elements of the plaque that send `x` into `X₁`.
  let E : Set Work.EKLContract.SL3 := {g : Work.EKLContract.SL3 | g • x ∈ X₁}
  have hE : MeasurableSet E := hX₁.preimage (by fun_prop)
  -- `ballU` is monotone in the radius.
  have hball_mono : ∀ {a b : ℝ}, a ≤ b →
      Work.EKLContract.ballU Work.EKLComp.h01 a ⊆ Work.EKLContract.ballU Work.EKLComp.h01 b := by
    intro a b hab
    exact Set.image_mono (Set.Icc_subset_Icc (by linarith) hab)
  -- The leaf mass is the measure of the intersection of the plaque with `E`.
  have hkey : ∀ r : ℝ, Work.EKLComp.leafMass ν X₁ r x
      = ν x (Work.EKLContract.ballU Work.EKLComp.h01 r ∩ E) := by
    intro r
    have h1 : Work.EKLComp.leafMass ν X₁ r x
        = ∫⁻ g, (E.indicator (fun _ => (1 : ℝ≥0∞))) g
            ∂(ν x).restrict (Work.EKLContract.ballU Work.EKLComp.h01 r) := by
      rw [Work.EKLComp.leafMass]
      apply MeasureTheory.lintegral_congr
      intro g
      by_cases hg : g • x ∈ X₁ <;> simp [E, Set.indicator_of_mem, Set.indicator_of_notMem, hg]
    rw [h1, MeasureTheory.lintegral_indicator_const (μ := (ν x).restrict _) hE (1 : ℝ≥0∞),
      one_mul, Measure.restrict_apply hE, Set.inter_comm]
  -- The plaques decrease to the plaque of radius `R`; this uses that `u_01` is injective with
  -- continuous inverse parameter `par`.
  have hInter_ball : (⋂ r : ℝ, ⋂ (_ : r > R),
      Work.EKLContract.ballU Work.EKLComp.h01 r) = Work.EKLContract.ballU Work.EKLComp.h01 R := by
    refine le_antisymm ?_ ?_
    · intro g hg
      simp only [Set.mem_iInter] at hg
      have hpar : Work.EKLComp.par g ∈ Set.Icc (-R) R := by
        refine ⟨?_, ?_⟩
        · have h : -Work.EKLComp.par g ≤ R :=
            le_of_forall_gt_imp_ge_of_dense (fun r hr => by
              have h2 := hg r hr
              rw [← Work.EKLComp.par_preimage_Icc r, Set.mem_inter_iff] at h2
              linarith [h2.2.1])
          linarith
        · exact le_of_forall_gt_imp_ge_of_dense (fun r hr => by
            have h2 := hg r hr
            rw [← Work.EKLComp.par_preimage_Icc r, Set.mem_inter_iff] at h2
            exact h2.2.2)
      have hU : g ∈ (Work.EKLContract.Uij Work.EKLComp.h01 : Set Work.EKLContract.SL3) := by
        have h1 := hg (R + 1) (by linarith)
        rw [← Work.EKLComp.par_preimage_Icc (R + 1), Set.mem_inter_iff] at h1
        exact h1.1
      rw [← Work.EKLComp.par_preimage_Icc R, Set.mem_inter_iff]
      exact ⟨hU, hpar⟩
    · intro g hg
      simp only [Set.mem_iInter]
      intro r hr
      exact hball_mono (le_of_lt hr) hg
  have hInter : (⋂ r : ℝ, ⋂ (_ : r > R),
      (Work.EKLContract.ballU Work.EKLComp.h01 r ∩ E))
      = Work.EKLContract.ballU Work.EKLComp.h01 R ∩ E := by
    refine le_antisymm ?_ ?_
    · intro g hg
      simp only [Set.mem_iInter] at hg
      refine ⟨?_, (hg (R + 1) (by linarith)).2⟩
      rw [← hInter_ball]
      simp only [Set.mem_iInter]
      exact fun r hr => (hg r hr).1
    · intro g hg
      simp only [Set.mem_iInter]
      intro r hr
      exact ⟨hball_mono (le_of_lt hr) hg.1, hg.2⟩
  -- Every member of the family is contained in the compact set `ballU h01 (R+1)`.
  have hfin : ∃ r > R, ν x (Work.EKLContract.ballU Work.EKLComp.h01 r ∩ E) ≠ ⊤ := by
    refine ⟨R + 1, by linarith, ?_⟩
    have h2 : ν x (Work.EKLContract.ballU Work.EKLComp.h01 (R + 1) ∩ E) < ⊤ :=
      lt_of_le_of_lt (MeasureTheory.measure_mono (μ := ν x) Set.inter_subset_left)
        ((hν x).lt_top_of_isCompact (Work.EKLComp.isCompact_ballU (R + 1)))
    exact h2.ne
  have hlim := MeasureTheory.tendsto_measure_biInter_gt (μ := ν x)
      (s := fun r : ℝ => Work.EKLContract.ballU Work.EKLComp.h01 r ∩ E) (a := R)
      (fun r _ => ((Work.EKLComp.isCompact_ballU r).measurableSet.inter hE).nullMeasurableSet)
      (fun i j _ hij => Set.inter_subset_inter (hball_mono hij) subset_rfl)
      hfin
  rw [hInter] at hlim
  simpa only [hkey, Function.comp_def] using hlim

end Work.EKLCompSetup
