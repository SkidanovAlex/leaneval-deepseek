import Mathlib
import Submission.Work.EKLRelCross.LeafMeasDefs

namespace Work.EKLRelCross

open Work.EKLContract
open MeasureTheory Topology Filter ProbabilityTheory
open scoped ENNReal

/-- The kernel `(x, t) ↦ κ x`, i.e. `κ` composed with the first projection. -/
def kernelFst (κ : Kernel X3 X3) : Kernel (X3 × ℝ) X3 :=
  κ.comap (fun a : X3 × ℝ => a.1) measurable_fst

/-- Measurability of the field `x ↦ ∫⁻ t in (0,∞), κ x (orbImg U x ({f > t} ∩ B))` for a
σ-compact set `B` of group elements and a continuous `f`. -/
theorem measurable_orbitLintegral {U : Subgroup Work.EKLContract.SL3}
    (hUcl : IsClosed (U : Set Work.EKLContract.SL3))
    (κ : ProbabilityTheory.Kernel Work.EKLContract.X3 Work.EKLContract.X3)
    (hκ : ∀ x, MeasureTheory.IsFiniteMeasure (κ x))
    {f : Work.EKLContract.SL3 → ℝ} (hf : Continuous f)
    {B : Set Work.EKLContract.SL3}
    (hB : ∃ K : ℕ → Set Work.EKLContract.SL3, (∀ n, IsCompact (K n)) ∧ ⋃ n, K n = B) :
    Measurable (fun x : Work.EKLContract.X3 =>
      ∫⁻ t in Set.Ioi (0 : ℝ),
        κ x (Work.EKLRelCross.orbImg U x ({g : Work.EKLContract.SL3 | t < f g} ∩ B))) := by
  classical
  obtain ⟨K, hKc, hKB⟩ := hB
  -- The Borel "relation" in `(x, t, y)` encoding `y ∈ orbImg U x ({f > t} ∩ B)`.
  set R : Set ((X3 × ℝ) × X3) :=
    {p | ∃ q : ℚ, p.1.2 < (q : ℝ) ∧
      ∃ u ∈ (B ∩ {g : SL3 | (q : ℝ) ≤ f g}) ∩ (U : Set SL3), u • p.1.1 = p.2} with hRdef
  have hR : MeasurableSet R := by
    have hcover : ∀ q : ℚ, MeasurableSet
        {p' : X3 × X3 | ∃ u ∈ (B ∩ {g : SL3 | (q : ℝ) ≤ f g}) ∩ (U : Set SL3),
          u • p'.1 = p'.2} := by
      intro q
      refine measurableSet_orbitRel_cover hUcl
        ⟨fun n => K n ∩ {g : SL3 | (q : ℝ) ≤ f g}, fun n => ?_, ?_⟩
      · exact (hKc n).inter_right (isClosed_le continuous_const hf)
      · rw [← Set.iUnion_inter ({g : SL3 | (q : ℝ) ≤ f g}) K, hKB]
    have hset : R = ⋃ q : ℚ,
        ({p : (X3 × ℝ) × X3 | p.1.2 < (q : ℝ)} ∩
          {p : (X3 × ℝ) × X3 | (p.1.1, p.2) ∈
            {p' : X3 × X3 | ∃ u ∈ (B ∩ {g : SL3 | (q : ℝ) ≤ f g}) ∩ (U : Set SL3),
              u • p'.1 = p'.2}}) := by
      ext p
      simp only [hRdef, Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_inter_iff]
    rw [hset]
    refine MeasurableSet.iUnion fun q => MeasurableSet.inter ?_ ?_
    · exact measurableSet_lt (by fun_prop) measurable_const
    · exact (hcover q).preimage (by fun_prop)
  have hsec : ∀ a : X3 × ℝ, {y : X3 | (a, y) ∈ R} =
      orbImg U a.1 ({g : SL3 | a.2 < f g} ∩ B) := by
    intro a
    ext y
    rw [hRdef]
    simp only [Set.mem_ofPred_eq]
    constructor
    · rintro ⟨q, hq, u, hu, hux⟩
      rw [mem_orbImg]
      exact ⟨u, ⟨lt_of_lt_of_le hq hu.1.2, hu.1.1⟩, hu.2, hux⟩
    · intro hy
      rw [mem_orbImg] at hy
      simp only [Set.mem_inter_iff, Set.mem_ofPred_eq] at hy
      obtain ⟨u, ⟨hfu, huB⟩, huU, hux⟩ := hy
      obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn hfu
      exact ⟨q, hq1, u, ⟨⟨huB, le_of_lt hq2⟩, huU⟩, hux⟩
  -- The map `(x,t) ↦ κ x {y | (x,t,y) ∈ R}` is measurable.
  have hmeas : Measurable (fun a : X3 × ℝ => κ a.1 {y : X3 | (a, y) ∈ R}) := by
    have hκ' : ∀ a : X3 × ℝ, IsFiniteMeasure (kernelFst κ a) := by
      intro a
      rw [kernelFst, Kernel.comap_apply]
      exact hκ a.1
    have hfm : Measurable (Function.uncurry (fun (a : X3 × ℝ) (y : X3) =>
        R.indicator (fun _ => (1 : ℝ≥0∞)) (a, y))) := by
      have heq : Function.uncurry (fun (a : X3 × ℝ) (y : X3) =>
          R.indicator (fun _ => (1 : ℝ≥0∞)) (a, y)) =
          R.indicator (fun _ => (1 : ℝ≥0∞)) := rfl
      rw [heq]
      exact measurable_const.indicator hR
    have hmain := EKLCompLeaf.measurable_lintegral_kernel_prod_right_of_finite
      (κ := kernelFst κ) hκ' hfm
    convert hmain using 1
    funext a
    rw [lintegral_indicator_const_comp (f := fun y : X3 => (a, y)) measurable_prodMk_left hR
      (1 : ℝ≥0∞), one_mul, kernelFst, Kernel.comap_apply]
    congr 1
  -- Integrate in `t`.
  have hF : Measurable (fun x : X3 => ∫⁻ t, κ x {y : X3 | ((x, t), y) ∈ R}
      ∂(volume.restrict (Set.Ioi (0 : ℝ)))) :=
    hmeas.lintegral_prod_right' (ν := volume.restrict (Set.Ioi (0 : ℝ)))
  convert hF using 1
  funext x
  exact lintegral_congr fun t => by rw [hsec (x, t)]

end Work.EKLRelCross
