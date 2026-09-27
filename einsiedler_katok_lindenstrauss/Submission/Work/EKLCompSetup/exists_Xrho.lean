import Mathlib
import Submission.Work.EKLComp.C8Defs
import Submission.Work.EKLCompLeaf.measurable_nu

namespace Work.EKLCompSetup

open MeasureTheory Filter Topology
open scoped ENNReal

/-- For a leafwise system whose `U_01`-leafwise measure has no atom at the identity, there is a
radius `ρ ∈ (0, 1/2]` such that the set `𝒳(ρ) = {x ∈ X'' | ν_x^ℝ([-ρ,ρ]) < 1/2}` is measurable
and has `μ`-measure bigger than `1 - ε²`.

The proof is the elementary shrinking argument:  for `x ∈ X''` the values
`ν_x^ℝ([-ρ,ρ])` decrease to the atom `ν_x^ℝ({0}) = 0`, so the sets `𝒳(1/(n+2))` increase to
`X''`; continuity from below of the probability measure `μ` then gives the claim. -/
theorem exists_Xrho
    {μ : MeasureTheory.Measure Work.EKLContract.X3} [MeasureTheory.IsProbabilityMeasure μ]
    {ν : Work.EKLContract.X3 → MeasureTheory.Measure Work.EKLContract.SL3}
    {X' X'' : Set Work.EKLContract.X3}
    (hL : Work.EKLContract.IsLeafwise μ (Work.EKLContract.Uij Work.EKLComp.h01) ν X')
    (hν : ∀ x, MeasureTheory.IsFiniteMeasureOnCompacts (ν x))
    (hX''meas : MeasurableSet X'') (hX''conull : μ X''ᶜ = 0)
    (hnoAtom : ∀ x ∈ X'', (Work.EKLComp.nuR (ν x)) {0} = 0)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ 1 / 2 ∧
      MeasurableSet {x | x ∈ X'' ∧
        (Work.EKLComp.nuR (ν x)).real (Set.Icc (-ρ) ρ) < (1 / 2 : ℝ)} ∧
      1 - ε ^ 2 < (μ {x | x ∈ X'' ∧
        (Work.EKLComp.nuR (ν x)).real (Set.Icc (-ρ) ρ) < (1 / 2 : ℝ)}).toReal := by
  -- ## Measurability of `x ↦ ν_x^ℝ([-R,R])`
  have hGmeas : ∀ R : ℝ, Measurable (fun x : Work.EKLContract.X3 =>
      (Work.EKLComp.nuR (ν x)).real (Set.Icc (-R) R)) := by
    intro R
    have h1 := Work.EKLCompLeaf.measurable_nu hL hν R Set.univ MeasurableSet.univ
    have h2 : (fun x : Work.EKLContract.X3 => (Work.EKLComp.nuR (ν x)).real (Set.Icc (-R) R))
        = fun x : Work.EKLContract.X3 =>
            (ν x (Set.univ ∩ Work.EKLContract.ballU Work.EKLComp.h01 R)).toReal := by
      funext x
      rw [Set.univ_inter, MeasureTheory.Measure.real_def, Work.EKLComp.nuR_Icc]
    rw [h2]; exact h1
  let S : ℝ → Set Work.EKLContract.X3 := fun ρ =>
    {x | x ∈ X'' ∧ (Work.EKLComp.nuR (ν x)).real (Set.Icc (-ρ) ρ) < (1/2 : ℝ)}
  have hSmeas : ∀ ρ : ℝ, MeasurableSet (S ρ) := by
    intro ρ
    exact hX''meas.inter ((hGmeas ρ) measurableSet_Iio)
  -- ## `S` is antitone in `ρ`
  have hanti : ∀ ⦃a b : ℝ⦄, a ≤ b → S b ⊆ S a := by
    intro a b hab x hx
    obtain ⟨hxX, hxg⟩ := hx
    refine ⟨hxX, ?_⟩
    have hsub : Set.Icc (-a) a ⊆ Set.Icc (-b) b := Set.Icc_subset_Icc (neg_le_neg hab) hab
    have hle := MeasureTheory.measureReal_mono (μ := Work.EKLComp.nuR (ν x)) hsub
      (Work.EKLComp.nuR_finite (hν x) b)
    linarith
  have hrhoanti : Antitone (fun n : ℕ => (1:ℝ)/((n:ℝ)+2)) := by
    intro m n hmn
    apply one_div_le_one_div_of_le
    · positivity
    · exact_mod_cast (Nat.add_le_add_right hmn 2)
  have hmono : Monotone (fun n : ℕ => S (1/((n:ℝ)+2))) := by
    intro m n hmn
    exact hanti (hrhoanti hmn)
  -- ## The sets `S(1/(n+2))` cover `X''`
  have hcover : X'' ⊆ ⋃ n : ℕ, S (1/((n:ℝ)+2)) := by
    intro x hx
    have ha : Tendsto (fun n : ℕ => (Work.EKLComp.nuR (ν x))
        (Set.Icc (-(1/((n:ℝ)+2))) (1/((n:ℝ)+2)))) atTop (𝓝 0) := by
      have hint : (⋂ n : ℕ, Set.Icc (-(1/((n:ℝ)+2))) (1/((n:ℝ)+2))) = {0} := by
        apply Set.Subset.antisymm
        · intro t ht
          rw [Set.mem_singleton_iff]
          by_contra ht0
          have hle : ∀ n : ℕ, |t| ≤ 1/((n:ℝ)+2) := fun n =>
            abs_le.mpr ⟨(Set.mem_iInter.mp ht n).1, (Set.mem_iInter.mp ht n).2⟩
          obtain ⟨m, hm⟩ := exists_nat_one_div_lt (abs_pos.mpr ht0)
          have hm3 : (1:ℝ)/((m:ℝ)+3) ≤ 1/((m:ℝ)+1) :=
            one_div_le_one_div_of_le (by positivity) (by linarith)
          have h1 : |t| ≤ (1:ℝ)/((m:ℝ)+3) := by
            have h2 := hle (m+1)
            rwa [show (((m+1 : ℕ) : ℝ) + 2) = (m:ℝ)+3 from by push_cast; ring] at h2
          linarith
        · intro t ht
          rw [Set.mem_singleton_iff] at ht
          subst ht
          rw [Set.mem_iInter]
          intro n
          rw [Set.mem_Icc]
          exact ⟨neg_nonpos.mpr (by positivity), by positivity⟩
      have ht := MeasureTheory.tendsto_measure_iInter_atTop (μ := Work.EKLComp.nuR (ν x))
        (s := fun n : ℕ => Set.Icc (-(1/((n:ℝ)+2))) (1/((n:ℝ)+2)))
        (fun n => (measurableSet_Icc).nullMeasurableSet)
        (fun m n hmn => Set.Icc_subset_Icc (neg_le_neg (hrhoanti hmn)) (hrhoanti hmn))
        ⟨0, by simpa using Work.EKLComp.nuR_finite (hν x) (1/2)⟩
      rwa [hint, hnoAtom x hx] at ht
    have hev := (tendsto_order.1 ha).2 (1/2) (by norm_num : (0:ℝ≥0∞) < 1/2)
    obtain ⟨n, hn⟩ := hev.exists
    refine Set.mem_iUnion.mpr ⟨n, ?_⟩
    refine ⟨hx, ?_⟩
    have hreal : (Work.EKLComp.nuR (ν x)).real (Set.Icc (-(1/((n:ℝ)+2))) (1/((n:ℝ)+2)))
        = ((Work.EKLComp.nuR (ν x)) (Set.Icc (-(1/((n:ℝ)+2))) (1/((n:ℝ)+2)))).toReal :=
      MeasureTheory.Measure.real_def _ _
    rw [hreal]
    have := (ENNReal.toReal_lt_toReal (ne_top_of_lt hn)
      (by norm_num : (1/2 : ℝ≥0∞) ≠ ⊤)).mpr hn
    simpa using this
  -- ## `X''` has full measure
  have hXuniv : μ X'' = 1 := by
    have hle : μ X'' ≤ μ Set.univ := measure_mono (Set.subset_univ _)
    rw [MeasureTheory.measure_univ] at hle
    refine le_antisymm hle ?_
    calc (1:ℝ≥0∞) = μ Set.univ := (MeasureTheory.measure_univ).symm
      _ = μ (X'' ∪ X''ᶜ) := by rw [Set.union_compl_self]
      _ ≤ μ X'' + μ X''ᶜ := measure_union_le _ _
      _ = μ X'' := by rw [hX''conull, add_zero]
  have hUnull : μ (⋃ n : ℕ, S (1/((n:ℝ)+2))) = 1 := by
    have hle : μ (⋃ n : ℕ, S (1/((n:ℝ)+2))) ≤ 1 := by
      rw [← MeasureTheory.measure_univ (μ := μ)]
      exact measure_mono (Set.subset_univ _)
    refine le_antisymm hle ?_
    calc (1:ℝ≥0∞) = μ X'' := hXuniv.symm
      _ ≤ μ (⋃ n : ℕ, S (1/((n:ℝ)+2))) := measure_mono hcover
  -- ## Continuity from below
  have hconv : Tendsto (fun n : ℕ => μ (S (1/((n:ℝ)+2)))) atTop (𝓝 1) := by
    have h := MeasureTheory.tendsto_measure_iUnion_atTop (μ := μ) hmono
    rwa [hUnull] at h
  have hev : ∀ᶠ n : ℕ in atTop, ENNReal.ofReal (1 - ε^2) < μ (S (1/((n:ℝ)+2))) := by
    refine (tendsto_order.1 hconv).1 (ENNReal.ofReal (1 - ε^2)) ?_
    rw [ENNReal.ofReal_lt_one]
    linarith [pow_pos hε 2]
  obtain ⟨n, hn⟩ := hev.exists
  have hnreal : 1 - ε^2 < (μ (S (1/((n:ℝ)+2)))).toReal := by
    by_cases h0 : 0 ≤ 1 - ε^2
    · have h1 : (ENNReal.ofReal (1 - ε^2)).toReal < (μ (S (1/((n:ℝ)+2)))).toReal :=
        (ENNReal.toReal_lt_toReal ENNReal.ofReal_ne_top
          (ne_top_of_le_ne_top ENNReal.one_ne_top (by
            rw [← MeasureTheory.measure_univ (μ := μ)]
            exact measure_mono (Set.subset_univ _)))).mpr hn
      rwa [ENNReal.toReal_ofReal h0] at h1
    · have : (0:ℝ) ≤ (μ (S (1/((n:ℝ)+2)))).toReal := ENNReal.toReal_nonneg
      linarith
  refine ⟨1/((n:ℝ)+2), ?_, ?_, ?_, ?_⟩
  · positivity
  · have h2 : (2:ℝ) ≤ (n:ℝ) + 2 := by
      have : (0:ℝ) ≤ (n:ℝ) := Nat.cast_nonneg n
      linarith
    exact one_div_le_one_div_of_le (by norm_num : (0:ℝ) < 2) h2
  · exact hSmeas _
  · exact hnreal

end Work.EKLCompSetup
