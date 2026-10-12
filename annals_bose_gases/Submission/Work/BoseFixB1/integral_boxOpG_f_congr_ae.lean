import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB1.BoxTauGenMeasToolbox
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1.integral_boxOpG_f_congr_ae`

The box operator `boxOpG A g 1` carries the created/annihilated slot weight `g` evaluated at the
(slot) coordinate `x i`, so it depends on `g` only through the values of `g` on `A`.  Consequently
if `g = g'` almost everywhere on `A`, the pairings agree:

  `∫ x in abox (N+1) a, Φ x * boxOpG A g 1 Ψ x = ∫ x in abox (N+1) a, Φ x * boxOpG A g' 1 Ψ x`.

The only measure-theoretic input is that the set of configurations with *some* coordinate inside
the (null) difference set `B = A ∩ {g ≠ g'}` is null, which is
`MeasureTheory.Measure.pi_eval_preimage_null` applied to the product decomposition
`restrict (abox (N+1) a) = π (volume ↾ acube a)` (`Submission.BoseGases.restrict_abox_eq_pi`).
No boundedness, integrability or measurability of `g, g', Φ, Ψ` is needed beyond what the set
manipulations ask for: both integrals are of functions which agree a.e.
-/

namespace Work.BoseFixB1

open MeasureTheory

set_option linter.unusedVariables false

theorem integral_boxOpG_f_congr_ae {N : ℕ} {a : ℝ} (ha : 0 < a)
    {A : Set (EuclideanSpace ℝ (Fin 3))} (hAm : MeasurableSet A)
    (hAc : A ⊆ Submission.BoseGases.acube a)
    {g g' : EuclideanSpace ℝ (Fin 3) → ℝ} (hgm : AEMeasurable g) (hg'm : Measurable g')
    (hgg' : g =ᵐ[MeasureTheory.volume.restrict A] g')
    {Cg : ℝ} (hgC : ∀ z, |g z| ≤ Cg) (hg'C : ∀ z, |g' z| ≤ Cg)
    {Φ Ψ : Submission.BoseGases.X (N + 1) → ℝ} (hΦm : Measurable Φ) (hΨm : Measurable Ψ)
    {CΦ CΨ : ℝ}
    (hΦb : ∀ x ∈ Submission.BoseGases.abox (N + 1) a, |Φ x| ≤ CΦ)
    (hΨb : ∀ x ∈ Submission.BoseGases.abox (N + 1) a, |Ψ x| ≤ CΨ) :
    (∫ x in Submission.BoseGases.abox (N + 1) a,
        Φ x * Work.BoseFixB1.boxOpG A g (fun _ => (1 : ℝ)) Ψ x)
      = ∫ x in Submission.BoseGases.abox (N + 1) a,
          Φ x * Work.BoseFixB1.boxOpG A g' (fun _ => (1 : ℝ)) Ψ x := by
  classical
  -- The set of points of `A` on which `g` and `g'` differ (a null set).
  set B : Set (EuclideanSpace ℝ (Fin 3)) := A ∩ {z | g z ≠ g' z} with hBdef
  -- `B` is also the set `{z | ¬ (z ∈ A → g z = g' z)}`, i.e. the set of points violating `hgg'`.
  have hBeq : B = {z : EuclideanSpace ℝ (Fin 3) | ¬ (z ∈ A → g z = g' z)} := by
    ext z
    simp only [hBdef, Set.mem_inter_iff, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨hzA, hzne⟩ h; exact hzne (h hzA)
    · intro h
      refine ⟨?_, ?_⟩
      · by_contra hzA
        exact h (fun hzA' => absurd hzA' hzA)
      · intro hgg
        exact h (fun _ => hgg)
  have hB0 : (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))) B = 0 := by
    rw [hBeq, ← MeasureTheory.ae_iff]
    exact (MeasureTheory.ae_restrict_iff' hAm).mp hgg'
  -- `B` is null for the cube-restricted measure, because `B ⊆ A ⊆ acube a`.
  have hνB : (MeasureTheory.volume.restrict (Submission.BoseGases.acube a)) B = 0 := by
    rw [MeasureTheory.Measure.restrict_apply' (Submission.BoseGases.acube_measurable a)]
    have hsub : B ⊆ Submission.BoseGases.acube a := fun z hz => hAc hz.1
    rw [Set.inter_eq_left.mpr hsub, hB0]
  -- The set of configurations with a coordinate in `B` is null on the box.
  have hS : (MeasureTheory.volume.restrict (Submission.BoseGases.abox (N + 1) a))
      (⋃ i : Fin (N + 1), (Function.eval i) ⁻¹' B) = 0 := by
    rw [Submission.BoseGases.restrict_abox_eq_pi]
    exact MeasureTheory.measure_iUnion_null
      (fun i => MeasureTheory.Measure.pi_eval_preimage_null
        (μ := fun _ : Fin (N + 1) => MeasureTheory.volume.restrict (Submission.BoseGases.acube a))
        hνB)
  have hae : ∀ᵐ x ∂(MeasureTheory.volume.restrict (Submission.BoseGases.abox (N + 1) a)),
      ∀ i : Fin (N + 1), x i ∉ B := by
    rw [MeasureTheory.ae_iff]
    have hset : {x : Submission.BoseGases.X (N + 1) | ¬ (∀ i : Fin (N + 1), x i ∉ B)}
        = ⋃ i : Fin (N + 1), (Function.eval i) ⁻¹' B := by
      ext x
      simp [Function.eval]
    rw [hset]
    exact hS
  -- The two integrands agree almost everywhere.
  apply MeasureTheory.integral_congr_ae
  filter_upwards [hae] with x hx
  have hbox : Work.BoseFixB1.boxOpG A g (fun _ => (1 : ℝ)) Ψ x
      = Work.BoseFixB1.boxOpG A g' (fun _ => (1 : ℝ)) Ψ x := by
    simp only [Work.BoseFixB1.boxOpG]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hxi : x i ∈ A
    · have hgii : g (x i) = g' (x i) := by
        by_contra hne
        exact hx i ⟨hxi, hne⟩
      simp only [Set.indicator_of_mem hxi, one_mul]
      rw [hgii]
    · simp only [Set.indicator_of_notMem hxi, zero_mul]
  rw [hbox]

end Work.BoseFixB1
