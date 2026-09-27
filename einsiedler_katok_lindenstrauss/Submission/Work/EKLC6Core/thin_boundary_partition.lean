import Mathlib
import Submission.Work.EKLC6Core.Basic
import Submission.Work.EKLComp.X3Background
import Submission.Work.Misiurewicz.exists_null_frontier_Vball_radius
import Submission.Work.Misiurewicz.Vball_eq_empty_of_nonpos
import Submission.Work.Misiurewicz.frontier_finite_subset
import Submission.Work.EKLC6Core.smul_frontier_Vball_subset
import Submission.Work.EKLC6Core.exists_one_sided_bound_of_hasDerivAt
import Submission.Work.EKLC6Core.exists_pattern_partition_thin

namespace Work.EKLC6Core

open MeasureTheory Filter Topology
open scoped ENNReal
open Work.EKLContract

set_option linter.style.haveILetI false

noncomputable section

/-- `V`-balls are measurable. -/
theorem measurableSet_Vball (z : X3) (t : ℝ) : MeasurableSet (Work.EKLComp.Vball t z) := by
  by_cases ht : t ≤ 0
  · rw [Work.Misiurewicz.Vball_eq_empty_of_nonpos ht z]; exact MeasurableSet.empty
  · exact (Work.Misiurewicz.isOpen_Vball z (lt_of_not_ge ht)).measurableSet

/-- The "thin frontier at radius `r`" property of a `V`-ball around `x`: the `V η`-collar of the
frontier of `Vball r x` has `μ`-measure at most `c η`, uniformly in `η > 0`. -/
def ThinAtRadius (μ : Measure X3) (x : X3) (r : ℝ) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ η : ℝ, 0 < η →
    μ ((fun p : SL3 × X3 => p.1 • p.2) '' ((V η) ×ˢ frontier (Work.EKLComp.Vball r x)))
      ≤ ENNReal.ofReal (c * η)

/-- For every centre `x ∈ X₃` and `0 < δ < r₀` there is a radius `r ∈ [δ, r₀]` at which the
`V`-ball around `x` has a *thin* frontier in the quantitative sense of `ThinAtRadius`.

The radius is chosen at a point of differentiability of the monotone function
`ρ ↦ μ (Vball ρ x)`: at such a point both one-sided difference quotients are bounded
(`exists_one_sided_bound_of_hasDerivAt`), and the `V η`-collar of the frontier is sandwiched in
the annulus `Vball (r + Cη) x \ Vball (r - Cη) x` (`smul_frontier_Vball_subset`). -/
theorem exists_thin_radius (μ : Measure X3) [IsFiniteMeasure μ] (x : X3) {δ r₀ : ℝ}
    (hδ : 0 < δ) (hδr₀ : δ < r₀) :
    ∃ r : ℝ, δ ≤ r ∧ r ≤ r₀ ∧ ThinAtRadius μ x r := by
  classical
  set f : ℝ → ℝ := fun t => (μ (Work.EKLComp.Vball t x)).toReal with hfdef
  have hfmono : Monotone f := by
    intro a b hab
    exact ENNReal.toReal_mono (measure_ne_top μ _)
      (measure_mono (Work.Misiurewicz.Vball_mono x hab))
  have hfA : ∀ t : ℝ, (0 : ℝ) ≤ f t := fun t => ENNReal.toReal_nonneg
  have hfB : ∀ t : ℝ, f t ≤ (μ Set.univ).toReal := by
    intro t
    exact ENNReal.toReal_mono (measure_ne_top μ _)
      (measure_mono (Set.subset_univ _))
  have hbad : volume {t : ℝ |
      ¬ HasDerivAt f ((hfmono.stieltjesFunction.measure.rnDeriv volume t).toReal) t} = 0 :=
    MeasureTheory.ae_iff.mp hfmono.ae_hasDerivAt
  obtain ⟨r, hrIoo, hd⟩ : ∃ r ∈ Set.Ioo δ r₀,
      HasDerivAt f ((hfmono.stieltjesFunction.measure.rnDeriv volume r).toReal) r := by
    by_contra hcon
    have hsub : Set.Ioo δ r₀ ⊆ {t : ℝ |
        ¬ HasDerivAt f ((hfmono.stieltjesFunction.measure.rnDeriv volume t).toReal) t} :=
      fun t ht htG => hcon ⟨t, ht, htG⟩
    have h0 : volume (Set.Ioo δ r₀) = 0 := measure_mono_null hsub hbad
    rw [Real.volume_Ioo] at h0
    have hpos : (0 : ℝ) < r₀ - δ := by linarith
    rw [ENNReal.ofReal_eq_zero] at h0
    linarith
  have hrδ : δ < r := hrIoo.1
  have hrpos : 0 < r := lt_trans hδ hrδ
  obtain ⟨cp, cm, hcp, hcm, hbp, hbm⟩ :=
    exists_one_sided_bound_of_hasDerivAt hfmono (A := 0) (B := (μ Set.univ).toReal)
      hfA hfB hrpos hd
  obtain ⟨C, hCpos, hC⟩ := smul_frontier_Vball_subset x hrpos
  set cc : ℝ := max ((cp + cm) * C) (μ Set.univ).toReal + 1 with hccdef
  have hccpos : 0 < cc := by
    have : (0 : ℝ) ≤ max ((cp + cm) * C) (μ Set.univ).toReal := le_max_of_le_right ENNReal.toReal_nonneg
    rw [hccdef]; linarith
  refine ⟨r, le_of_lt hrδ, le_of_lt hrIoo.2, cc, hccpos, ?_⟩
  intro η hηpos
  by_cases hη1 : η ≤ 1
  · have hsub : (fun p : SL3 × X3 => p.1 • p.2) ''
          ((V η) ×ˢ frontier (Work.EKLComp.Vball r x))
        ⊆ Work.EKLComp.Vball (r + C * η) x \ Work.EKLComp.Vball (r - C * η) x :=
      hC η hηpos hη1
    have h1 : (μ ((fun p : SL3 × X3 => p.1 • p.2) ''
          ((V η) ×ˢ frontier (Work.EKLComp.Vball r x)))).toReal
        ≤ (μ (Work.EKLComp.Vball (r + C * η) x \ Work.EKLComp.Vball (r - C * η) x)).toReal :=
      ENNReal.toReal_mono (measure_ne_top μ _) (measure_mono hsub)
    have hCp : 0 < C * η := mul_pos hCpos hηpos
    have hle : Work.EKLComp.Vball (r - C * η) x ⊆ Work.EKLComp.Vball (r + C * η) x :=
      Work.Misiurewicz.Vball_mono x (by linarith [hCp])
    have hsdiff : μ (Work.EKLComp.Vball (r + C * η) x \ Work.EKLComp.Vball (r - C * η) x)
        = μ (Work.EKLComp.Vball (r + C * η) x) - μ (Work.EKLComp.Vball (r - C * η) x) :=
      measure_sdiff hle (measurableSet_Vball x _).nullMeasurableSet (measure_ne_top μ _)
    have h2 : (μ (Work.EKLComp.Vball (r + C * η) x \ Work.EKLComp.Vball (r - C * η) x)).toReal
        = f (r + C * η) - f (r - C * η) := by
      rw [hsdiff, ENNReal.toReal_sub_of_le (measure_mono hle) (measure_ne_top μ _)]
    have h3 : f (r + C * η) - f (r - C * η) ≤ ((cp + cm) * C) * η := by
      have h1' : f (r + C * η) - f r ≤ cp * (C * η) := hbp (C * η) hCp
      have h2' : f r - f (r - C * η) ≤ cm * (C * η) := hbm (C * η) hCp
      nlinarith [h1', h2']
    have h4 : ((cp + cm) * C) * η ≤ cc * η := by
      have hle' : ((cp + cm) * C) ≤ cc := by
        rw [hccdef]
        linarith [le_max_left ((cp + cm) * C) (μ Set.univ).toReal]
      exact mul_le_mul_of_nonneg_right hle' (le_of_lt hηpos)
    have hfin : (μ ((fun p : SL3 × X3 => p.1 • p.2) ''
          ((V η) ×ˢ frontier (Work.EKLComp.Vball r x)))).toReal ≤ cc * η :=
      h1.trans_eq h2 |>.trans (h3.trans h4)
    rw [← ENNReal.ofReal_toReal (measure_ne_top μ _)]
    exact ENNReal.ofReal_le_ofReal hfin
  · simp only [not_le] at hη1
    have hle1 : μ ((fun p : SL3 × X3 => p.1 • p.2) ''
        ((V η) ×ˢ frontier (Work.EKLComp.Vball r x))) ≤ μ Set.univ :=
      measure_mono (Set.subset_univ _)
    have hcη : (μ Set.univ).toReal ≤ cc * η := by
      have h1 : (μ Set.univ).toReal ≤ max ((cp + cm) * C) (μ Set.univ).toReal :=
        le_max_right _ _
      have h2 : max ((cp + cm) * C) (μ Set.univ).toReal ≤ cc := by
        rw [hccdef]; linarith
      have h3 : cc ≤ cc * η := by
        have : (1 : ℝ) ≤ η := le_of_lt hη1
        nlinarith [hccpos]
      linarith
    calc μ ((fun p : SL3 × X3 => p.1 • p.2) ''
            ((V η) ×ˢ frontier (Work.EKLComp.Vball r x)))
        ≤ μ Set.univ := hle1
      _ = ENNReal.ofReal (μ Set.univ).toReal := (ENNReal.ofReal_toReal (measure_ne_top μ _)).symm
      _ ≤ ENNReal.ofReal (cc * η) := ENNReal.ofReal_le_ofReal hcη

/-- **Thin-boundary partition.**  For every probability measure `μ` on `X₃`, every `ε > 0` and
every `ρ > 0` there is a finite measurable partition `(P i)` of `X₃`, an exceptional index `i₀`
of measure `< ε`, and a constant `c > 0` such that

* every non-exceptional piece is contained in a `V ρ`-ball around some point, and
* the total `V η`-collar of the union of the frontiers has `μ`-measure at most `c η`. -/
theorem thin_boundary_partition (μ : MeasureTheory.Measure Work.EKLContract.X3)
    [MeasureTheory.IsProbabilityMeasure μ] (ε ρ : ℝ) (hε : 0 < ε) (hρ : 0 < ρ) :
    ∃ (N : ℕ) (P : Fin N → Set Work.EKLContract.X3) (i₀ : Fin N) (c : ℝ),
      0 < c ∧ (∀ i, MeasurableSet (P i)) ∧
      (∀ i j, i ≠ j → Disjoint (P i) (P j)) ∧
      (⋃ i, P i) = Set.univ ∧
      (∀ i, i ≠ i₀ → ∃ x : Work.EKLContract.X3,
        P i ⊆ (fun g : Work.EKLContract.SL3 => g • x) '' (Work.EKLContract.V ρ)) ∧
      μ (P i₀) < ENNReal.ofReal ε ∧
      (∀ η : ℝ, 0 < η → μ (⋃ i, (fun p : Work.EKLContract.SL3 × Work.EKLContract.X3 =>
          p.1 • p.2) '' ((Work.EKLContract.V η) ×ˢ (frontier (P i))))
        ≤ ENNReal.ofReal (c * η)) := by
  classical
  haveI hT2 : T2Space X3 := Work.EKLComp.X3Background.1
  haveI hLC : LocallyCompactSpace X3 := Work.EKLComp.X3Background.2.1
  haveI hSC : SecondCountableTopology X3 := Work.EKLComp.X3Background.2.2.1
  haveI hPol : PolishSpace X3 := Work.EKLComp.X3Background.2.2.2.1
  haveI : IsFiniteMeasure μ := inferInstance
  set r₀ : ℝ := ρ / 2 with hr₀def
  set δ : ℝ := ρ / 4 with hδdef
  have hδpos : 0 < δ := by rw [hδdef]; linarith
  have hδr₀ : δ < r₀ := by rw [hδdef, hr₀def]; linarith
  have hr₀ρ : r₀ < ρ := by rw [hr₀def]; linarith
  set ε' : ℝ := min (ε / 2) (1 / 2) with hε'def
  have hε'pos : 0 < ε' := lt_min (by linarith) (by norm_num)
  have hε'lt : ε' < ε := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  obtain ⟨K, hKc, hKν⟩ := (MeasureTheory.isTightMeasureSet_iff_exists_isCompact_measure_compl_le.mp
      (MeasureTheory.isTightMeasureSet_singleton (μ := μ)))
      (ENNReal.ofReal ε') (ENNReal.ofReal_pos.mpr hε'pos)
  have hKν' : μ Kᶜ ≤ ENNReal.ofReal ε' := hKν μ (Set.mem_singleton μ)
  have hcoverK : K ⊆ ⋃ y : X3, Work.EKLComp.Vball δ y := by
    intro y hy
    refine Set.mem_iUnion.mpr ⟨y, ?_⟩
    rw [Work.EKLComp.mem_Vball]
    exact ⟨1, (Work.EKLContract.Lemmas.V_open_one δ hδpos).2, one_smul _ y⟩
  obtain ⟨t, ht⟩ := hKc.elim_finite_subcover (fun y : X3 => Work.EKLComp.Vball δ y)
      (fun y => Work.Misiurewicz.isOpen_Vball y hδpos) hcoverK
  let xs : Fin t.card → X3 := fun i => (t.equivFin.symm i).val
  have hloc : ∀ i : Fin t.card, ∃ r : ℝ, (δ ≤ r ∧ r ≤ r₀) ∧ ThinAtRadius μ (xs i) r := by
    intro i
    obtain ⟨rr, h1, h2, h3⟩ := exists_thin_radius μ (xs i) hδpos hδr₀
    exact ⟨rr, ⟨h1, h2⟩, h3⟩
  choose r hr hthin using hloc
  let U : Fin t.card → Set X3 := fun i => Work.EKLComp.Vball (r i) (xs i)
  have hUmeas : ∀ i, MeasurableSet (U i) := fun i => measurableSet_Vball (xs i) (r i)
  have hUthin : ∀ i, ∃ c : ℝ, 0 < c ∧ ∀ η : ℝ, 0 < η →
      μ ((fun p : SL3 × X3 => p.1 • p.2) '' ((V η) ×ˢ frontier (U i)))
        ≤ ENNReal.ofReal (c * η) := fun i => hthin i
  have hKsub : K ⊆ ⋃ i, U i := by
    intro y hy
    rw [Set.mem_iUnion]
    have hy' := ht hy
    rw [Set.mem_iUnion] at hy'
    obtain ⟨z, hz⟩ := hy'
    rw [Set.mem_iUnion] at hz
    obtain ⟨hzt, hyz⟩ := hz
    refine ⟨t.equivFin ⟨z, hzt⟩, ?_⟩
    have hxz : xs (t.equivFin ⟨z, hzt⟩) = z := by
      show (t.equivFin.symm (t.equivFin ⟨z, hzt⟩)).val = z
      rw [Equiv.symm_apply_apply]
    show y ∈ Work.EKLComp.Vball (r (t.equivFin ⟨z, hzt⟩)) (xs (t.equivFin ⟨z, hzt⟩))
    rw [hxz]
    exact Work.Misiurewicz.Vball_mono z (hr (t.equivFin ⟨z, hzt⟩)).1 hyz
  have hcomp : μ ((⋃ i, U i))ᶜ < ENNReal.ofReal ε := by
    have h1 : μ ((⋃ i, U i))ᶜ ≤ μ Kᶜ := measure_mono (Set.compl_subset_compl.mpr hKsub)
    have h2 : ENNReal.ofReal ε' < ENNReal.ofReal ε :=
      (ENNReal.ofReal_lt_ofReal_iff hε).mpr hε'lt
    exact lt_of_le_of_lt (le_trans h1 hKν') h2
  obtain ⟨N, P, i₀, c, hc, hPmeas, hPdisj, hPcov, hPsub, hPi₀, hPthin⟩ :=
    exists_pattern_partition_thin μ U hUmeas hUthin ε hε hcomp
  refine ⟨N, P, i₀, c, hc, hPmeas, hPdisj, hPcov, ?_, hPi₀, hPthin⟩
  intro i hi
  obtain ⟨j, hj⟩ := hPsub i hi
  refine ⟨xs j, ?_⟩
  intro y hy
  have hyj : y ∈ Work.EKLComp.Vball (r j) (xs j) := hj hy
  rw [Work.EKLComp.mem_Vball] at hyj
  obtain ⟨u, hu, huy⟩ := hyj
  exact ⟨u, Work.Misiurewicz.V_mono (le_of_lt (lt_of_le_of_lt (hr j).2 hr₀ρ)) hu, huy⟩

end

end Work.EKLC6Core
