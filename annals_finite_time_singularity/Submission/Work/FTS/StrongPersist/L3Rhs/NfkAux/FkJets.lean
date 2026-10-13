/-
# `Submission/Work/FTS/StrongPersist/L3Rhs/NfkAux/FkJets.lean`

The pointwise bound on the `z`-jets of the angular moment `FK f` by its own `ℋ⁴`-norm, for
`H6Adm` data.  This is the input of the product estimates `N₄^{gg}`, `N₅^{gg}` of the
`NFkSum` block.

Route: the radial Agmon inequality `NfkAux.RadSupZ` applied to `z ↦ D_z^a(FK f)`, whose two
weighted `L²`-integrals are the slots `a`, `a+1` of `HkSq α 4 (fun z _ => FK f z)` (`FK_slot_le`).

Everything rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongPersist.L3Rhs.Defs
import Submission.Work.FTS.StrongPersist.L3Rhs.NfkAux.Basic
import Submission.Work.FTS.StrongPersist.L3Rhs.NfkAux.FkSlots
import Submission.Work.FTS.StrongPersist.L3Rhs.NfkAux.RadSupZ

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.L3Rhs.NfkAux

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

/-- `z ↦ FK f z` is `C^m` on `(0,∞)` for `m ≤ 5` in the honest class. -/
theorem FK_smooth {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {f : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.EllipticEst.SmoothOpen f) (hmem : Work.Spaces.HkMem α 6 f) :
    ∀ (m : ℕ), m ≤ 5 → ContDiffOn ℝ m (fun z => Work.Construction.FK f z) (Set.Ioi (0 : ℝ)) :=
  contDiffOn_FK hα hα1 hsm hmem

/-- **The `z`-jets of the angular moment are bounded by its `ℋ⁴`-norm**, uniformly in `α` and in
the datum, pointwise on `(0,∞)`, for `a ≤ 3`. -/
theorem FK_jets : ∃ C : ℝ, 0 < C ∧
    ∀ (α : ℝ), α ∈ Set.Ioc 0 1 → ∀ (f : ℝ → ℝ → ℝ),
      Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.HkMem α 6 f →
      Work.Spaces.HkMem α 4 (fun z (_ : ℝ) => Work.Construction.FK f z) →
      ∀ (a : ℕ), a ≤ 3 → ∀ z ∈ Set.Ioi (0 : ℝ),
        (Work.Elliptic.DzdIter a (Work.Construction.FK f) z) ^ 2
          ≤ C * Work.Spaces.HkSq α 4 (fun z (_ : ℝ) => Work.Construction.FK f z) := by
  obtain ⟨Crs, hCrs, hrs⟩ := RadSupZ
  refine ⟨Crs * (8 / π), mul_pos hCrs (by positivity), ?_⟩
  intro α hαIoc f hsm hmem hFKmem a ha z hz
  obtain ⟨hα, hα1⟩ := Set.mem_Ioc.mp hαIoc
  have hsmooth : ∀ (m : ℕ), m ≤ 5 → ContDiffOn ℝ m (fun z => Work.Construction.FK f z)
      (Set.Ioi (0 : ℝ)) := FK_smooth hα hα1 hsm hmem
  have hslot : ∀ (b : ℕ), b ≤ 4 →
      MeasureTheory.IntegrableOn
          (fun z => (Work.Elliptic.DzdIter b (Work.Construction.FK f) z) ^ 2
            * (Work.Spaces.w z) ^ 2) Work.Spaces.Iz ∧
        (∫ z in Work.Spaces.Iz,
            (Work.Elliptic.DzdIter b (Work.Construction.FK f) z) ^ 2
              * (Work.Spaces.w z) ^ 2)
          ≤ (4 / π) * Work.Spaces.HkSq α 4 (fun z (_ : ℝ) => Work.Construction.FK f z) :=
    fun b hb => FK_slot_le (r := fun z => Work.Construction.FK f z) (n := 5)
      hsmooth hFKmem hb (by omega)
  -- the two integrability hypotheses of the radial Agmon bound, on `Ioi 0`
  have h1 : MeasureTheory.IntegrableOn
      (fun z => (Work.Elliptic.DzdIter a (Work.Construction.FK f) z) ^ 2
        * (Work.Spaces.w z) ^ 2) (Set.Ioi (0 : ℝ)) := by
    show MeasureTheory.Integrable _ (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ)))
    rw [restrict_Ioi_eq_Iz]
    exact (hslot a (by omega)).1
  have h2 : MeasureTheory.IntegrableOn
      (fun z => (Work.Spaces.Dz (fun z _ => Work.Elliptic.DzdIter a
        (Work.Construction.FK f) z) z 0) ^ 2 * (Work.Spaces.w z) ^ 2) (Set.Ioi (0 : ℝ)) := by
    show MeasureTheory.Integrable _ (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ)))
    rw [restrict_Ioi_eq_Iz]
    have heq : (fun z => (Work.Spaces.Dz (fun z _ => Work.Elliptic.DzdIter a
        (Work.Construction.FK f) z) z 0) ^ 2 * (Work.Spaces.w z) ^ 2)
        = fun z => (Work.Elliptic.DzdIter (a + 1) (Work.Construction.FK f) z) ^ 2
            * (Work.Spaces.w z) ^ 2 := by
      funext z'
      rw [Work.Elliptic.DzdIter_succ]
      rfl
    rw [heq]
    exact (hslot (a + 1) (by omega)).1
  have hdiff : ∀ z ∈ Set.Ioi (0 : ℝ),
      DifferentiableAt ℝ (fun z => Work.Elliptic.DzdIter a (Work.Construction.FK f) z) z := by
    intro z hz
    have hcd := contDiffOn_DzdIter_of_radial (r := fun z => Work.Construction.FK f z)
      (n := 5) hsmooth (a := a) (t := 1) (by omega)
    exact (hcd.differentiableOn (by norm_num)).differentiableAt (isOpen_Ioi.mem_nhds hz)
  have hr := hrs (fun z => Work.Elliptic.DzdIter a (Work.Construction.FK f) z) hdiff h1 h2 z hz
  -- rewrite the two integrals in `hr` (over `Ioi 0`) into integrals over `Iz`
  have heq1 : (∫ z' in Set.Ioi (0 : ℝ),
        (Work.Elliptic.DzdIter a (Work.Construction.FK f) z') ^ 2
          * (Work.Spaces.w z') ^ 2)
      = (∫ z' in Work.Spaces.Iz,
          (Work.Elliptic.DzdIter a (Work.Construction.FK f) z') ^ 2
            * (Work.Spaces.w z') ^ 2) := by
    rw [restrict_Ioi_eq_Iz]
  have heq2 : (∫ z' in Set.Ioi (0 : ℝ),
        (Work.Spaces.Dz (fun z _ => Work.Elliptic.DzdIter a (Work.Construction.FK f) z)
            z' 0) ^ 2 * (Work.Spaces.w z') ^ 2)
      = (∫ z' in Work.Spaces.Iz,
          (Work.Elliptic.DzdIter (a + 1) (Work.Construction.FK f) z') ^ 2
            * (Work.Spaces.w z') ^ 2) := by
    rw [restrict_Ioi_eq_Iz]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun z' => ?_)
    rw [Work.Elliptic.DzdIter_succ]
    rfl
  have hb1 := (hslot a (by omega)).2
  have hb2 := (hslot (a + 1) (by omega)).2
  have hHnn : (0 : ℝ) ≤ Work.Spaces.HkSq α 4
      (fun z (_ : ℝ) => Work.Construction.FK f z) := Work.Spaces.HkSq_nonneg α 4 _
  have hsum : (∫ z' in Work.Spaces.Iz,
        (Work.Elliptic.DzdIter a (Work.Construction.FK f) z') ^ 2 * (Work.Spaces.w z') ^ 2)
      + (∫ z' in Work.Spaces.Iz,
        (Work.Elliptic.DzdIter (a + 1) (Work.Construction.FK f) z') ^ 2
          * (Work.Spaces.w z') ^ 2)
      ≤ (8 / π) * Work.Spaces.HkSq α 4 (fun z (_ : ℝ) => Work.Construction.FK f z) := by
    have h5 : (4 / π) * Work.Spaces.HkSq α 4 (fun z (_ : ℝ) => Work.Construction.FK f z)
        + (4 / π) * Work.Spaces.HkSq α 4 (fun z (_ : ℝ) => Work.Construction.FK f z)
        = (8 / π) * Work.Spaces.HkSq α 4 (fun z (_ : ℝ) => Work.Construction.FK f z) := by
      ring
    linarith [hb1, hb2, hHnn, Real.pi_pos, h5]
  rw [heq1, heq2] at hr
  calc (Work.Elliptic.DzdIter a (Work.Construction.FK f) z) ^ 2
      ≤ Crs * ((∫ z' in Work.Spaces.Iz,
            (Work.Elliptic.DzdIter a (Work.Construction.FK f) z') ^ 2
              * (Work.Spaces.w z') ^ 2)
          + (∫ z' in Work.Spaces.Iz,
            (Work.Elliptic.DzdIter (a + 1) (Work.Construction.FK f) z') ^ 2
              * (Work.Spaces.w z') ^ 2)) := hr
    _ ≤ Crs * ((8 / π) * Work.Spaces.HkSq α 4
          (fun z (_ : ℝ) => Work.Construction.FK f z)) :=
        mul_le_mul_of_nonneg_left hsum hCrs.le
    _ = Crs * (8 / π) * Work.Spaces.HkSq α 4
          (fun z (_ : ℝ) => Work.Construction.FK f z) := by ring

end Work.FTS.StrongPersist.L3Rhs.NfkAux
