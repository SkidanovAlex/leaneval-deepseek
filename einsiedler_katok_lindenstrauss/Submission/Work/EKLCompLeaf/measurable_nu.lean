import Mathlib
import Submission.Work.EKLComp.C8Defs
import Submission.Work.EKLRelCross.Instances
import Submission.Work.EKLCompLeaf.cofinal_open_cover

/-!
# Measurability of the leafwise measure evaluated at a Borel set intersected with `ballU 1`

The leafwise-measure system `ν` of `Work.EKLContract.IsLeafwise` is *weakly measurable*: for every
compactly supported continuous `f : SL₃(ℝ) → ℝ` the function `x ↦ ∫ g, f g ∂(ν x)` is measurable
(field `IsLeafwise.measurable`).  Together with the hypothesis that each `ν x` is finite on
compact sets, this forces `x ↦ (ν x) B` to be measurable for every Borel set `B` — in particular
for `B = A ∩ ballU 1`.

The argument has two steps.

* **Compact sets.**  For a compact `K` we show `x ↦ (ν x) K` is measurable.  Since `SL₃(ℝ)` is
  second countable, `Work.EKLCompLeaf.cofinal_open_cover` provides a countable family `W` of open
  sets which refines every pair `K ⊆ U` (`K` compact, `U` open): there is a finite union
  `V s = ⋃ n ∈ s, W n` with `K ⊆ V s ⊆ U`.  Urysohn's lemma (`exists_continuous_one_zero_of_isCompact`)
  produces, for each finite `s` with `K ⊆ V s`, a compactly supported continuous `φ s` with
  `1_K ≤ φ s ≤ 1_{V s}`.  Hence, for every `x`,
  `ν x K ≤ ∫ φ s dν x ≤ ν x (V s)`, and letting `s` run over the cofinal family, outer regularity
  of the Radon measure `ν x` (`IsCompact.measure_eq_iInf_isOpen`) gives
  `ν x K = ⨅ s, ENNReal.ofReal (∫ φ s dν x)`.
  A countable infimum of the measurable functions `x ↦ ∫ φ s dν x` is measurable
  (`Measurable.iInf`).  This is `measurable_apply_isCompact` below.

* **All Borel sets.**  With `K = ballU 1` compact, the π-λ theorem
  (`MeasurableSpace.induction_on_inter`) applied to the π-system of *closed* sets and the predicate
  `B ↦ Measurable (fun x => (ν x) (B ∩ K))` gives all Borel `B`: closed `B` reduce to the compact
  case (`B ∩ K` is compact), complements use `ν x (Bᶜ ∩ K) = ν x K - ν x (B ∩ K)` (both terms
  finite because `B ∩ K ⊆ K` and `ν x K < ∞`), and countable disjoint unions use countable
  additivity (`Measurable.ennreal_tsum`).  Composing with `ENNReal.toReal` yields the claim.
-/

set_option linter.style.haveILetI false

open MeasureTheory Filter Topology
open scoped ENNReal
open Work.EKLContract

noncomputable section

namespace Work.EKLCompLeaf

/-! ## Instances for `SL₃(ℝ)` needed by the regularity/Urysohn machinery

`Matrix (Fin 3) (Fin 3) ℝ` is a finite product of copies of `ℝ`, but instance search does not
unfold the `def Matrix`, so the completely-pseudometrizable instance is transported by hand.  Then
`SL₃(ℝ) = {A | A.det = 1}` inherits it as a closed subspace. -/

instance instICPMSMatrix3 :
    TopologicalSpace.IsCompletelyPseudoMetrizableSpace (Matrix (Fin 3) (Fin 3) ℝ) :=
  inferInstanceAs (TopologicalSpace.IsCompletelyPseudoMetrizableSpace (Fin 3 → Fin 3 → ℝ))

instance instICPMSSL3 : TopologicalSpace.IsCompletelyPseudoMetrizableSpace SL3 := by
  have h : IsClosed {A : Matrix (Fin 3) (Fin 3) ℝ | A.det = 1} :=
    isClosed_eq (continuous_id.matrix_det (n := Fin 3) (R := ℝ)) continuous_const
  exact h.isCompletelyPseudoMetrizableSpace

/-- A measure which is finite on compact sets of a locally compact space is locally finite.
(Mathlib only provides the instance from `IsFiniteMeasure`.) -/
instance instLocallyFiniteMeasureOfIsFiniteMeasureOnCompacts {α : Type*} [MeasurableSpace α]
    [TopologicalSpace α] [LocallyCompactSpace α] [R1Space α] (μ : Measure α)
    [IsFiniteMeasureOnCompacts μ] : IsLocallyFiniteMeasure μ where
  finiteAtNhds x := by
    obtain ⟨C, hCc, hC⟩ := exists_compact_mem_nhds x
    exact ⟨C, hC, IsFiniteMeasureOnCompacts.lt_top_of_isCompact hCc⟩

/-- **Weak measurability plus finiteness on compacts gives measurability on compact sets.**
For a family of measures `ν` on `SL₃(ℝ)` indexed by a measurable space, if all the functionals
`x ↦ ∫ f dν x` (`f` compactly supported continuous) are measurable and each `ν x` is finite on
compact sets, then `x ↦ ν x K` is measurable for every compact `K`. -/
theorem measurable_apply_isCompact {τ : Type*} [MeasurableSpace τ]
    {ν : τ → Measure SL3}
    (hmeas : ∀ f : CompactlySupportedContinuousMap SL3 ℝ,
      Measurable (fun x => ∫ g, f g ∂(ν x)))
    (hν : ∀ x : τ, IsFiniteMeasureOnCompacts (ν x))
    {K : Set SL3} (hK : IsCompact K) :
    Measurable fun x => ν x K := by
  classical
  obtain ⟨W, hWo, hWcov⟩ := cofinal_open_cover
  let V : Finset ℕ → Set SL3 := fun s => ⋃ n ∈ s, W n
  have hVo : ∀ s, IsOpen (V s) := fun s =>
    isOpen_iUnion (fun n => isOpen_iUnion (fun _ => hWo n))
  have hex : ∀ s : {s : Finset ℕ // K ⊆ V s}, ∃ f : C(SL3, ℝ),
      Set.EqOn f 1 K ∧ Set.EqOn f 0 (V s.1)ᶜ ∧ HasCompactSupport f ∧
        ∀ y, f y ∈ Set.Icc (0:ℝ) 1 := by
    intro s
    refine exists_continuous_one_zero_of_isCompact hK (hVo s.1).isClosed_compl ?_
    rw [Set.disjoint_compl_right_iff_subset]
    exact s.2
  let F : (s : {s : Finset ℕ // K ⊆ V s}) → C(SL3, ℝ) := fun s => Classical.choose (hex s)
  have hF : ∀ s, Set.EqOn (F s) 1 K ∧ Set.EqOn (F s) 0 (V s.1)ᶜ ∧ HasCompactSupport (F s) ∧
      ∀ y, F s y ∈ Set.Icc (0:ℝ) 1 := fun s => Classical.choose_spec (hex s)
  let φ : (s : {s : Finset ℕ // K ⊆ V s}) → CompactlySupportedContinuousMap SL3 ℝ :=
    fun s => CompactlySupportedContinuousMap.mk (F s) (hF s).2.2.1
  have hφ1 : ∀ t : {s : Finset ℕ // K ⊆ V s}, ∀ y ∈ K, (φ t) y = 1 :=
    fun t y hy => (hF t).1 hy
  have hφ2 : ∀ t : {s : Finset ℕ // K ⊆ V s}, ∀ y, y ∉ V t.1 → (φ t) y = 0 :=
    fun t y hy => (hF t).2.1 hy
  have hφ3 : ∀ t : {s : Finset ℕ // K ⊆ V s}, ∀ y, (φ t) y ∈ Set.Icc (0:ℝ) 1 :=
    fun t y => (hF t).2.2.2 y
  have key : ∀ x, ν x K = ⨅ t : {s : Finset ℕ // K ⊆ V s},
      ENNReal.ofReal (∫ g, φ t g ∂(ν x)) := by
    intro x
    haveI hνx : IsFiniteMeasureOnCompacts (ν x) := hν x
    apply le_antisymm
    · -- `ν x K ≤ ∫ φ t dν x` since `φ t ≥ 1_K`
      refine le_iInf (fun t => ?_)
      have hInt : Integrable (fun g => (φ t : SL3 → ℝ) g) (ν x) :=
        (φ t).continuous.integrable_of_hasCompactSupport (φ t).hasCompactSupport
      exact hInt.measure_le_integral (Eventually.of_forall (fun g => (hφ3 t g).1))
        (fun g hg => le_of_eq (hφ1 t g hg).symm)
    · -- `⨅ t ∫ φ t dν x ≤ ν x K` by outer regularity and cofinality of the family `V`
      rw [IsCompact.measure_eq_iInf_isOpen hK]
      refine le_iInf (fun U => le_iInf (fun hKU => le_iInf (fun hUo => ?_)))
      obtain ⟨s, hs1, hs2⟩ := hWcov K U hK hUo hKU
      have hle1 : ENNReal.ofReal (∫ g, φ ⟨s, hs1⟩ g ∂(ν x)) ≤ ν x (V s) := by
        have hInt : Integrable (fun g => (φ ⟨s, hs1⟩ : SL3 → ℝ) g) (ν x) :=
          (φ ⟨s, hs1⟩).continuous.integrable_of_hasCompactSupport (φ ⟨s, hs1⟩).hasCompactSupport
        have h0 : 0 ≤ᵐ[ν x] (fun g => (φ ⟨s, hs1⟩ : SL3 → ℝ) g) :=
          Eventually.of_forall (fun g => (hφ3 ⟨s, hs1⟩ g).1)
        rw [ofReal_integral_eq_lintegral_ofReal hInt h0]
        calc ∫⁻ g, ENNReal.ofReal ((φ ⟨s, hs1⟩ : SL3 → ℝ) g) ∂(ν x)
            ≤ ∫⁻ g, (V s).indicator (1 : SL3 → ℝ≥0∞) g ∂(ν x) := by
              refine lintegral_mono (fun g => ?_)
              by_cases hg : g ∈ V s
              · rw [Set.indicator_of_mem hg]
                simp only [Pi.one_apply]
                rw [← ENNReal.ofReal_one]
                exact ENNReal.ofReal_le_ofReal (hφ3 ⟨s, hs1⟩ g).2
              · rw [Set.indicator_of_notMem hg, hφ2 ⟨s, hs1⟩ g hg]
                simp
          _ = ν x (V s) := lintegral_indicator_one (hVo s).measurableSet
      exact (iInf_le (fun t : {s : Finset ℕ // K ⊆ V s} =>
        ENNReal.ofReal (∫ g, φ t g ∂(ν x))) ⟨s, hs1⟩).trans (hle1.trans (measure_mono hs2))
  have hfin : (fun x => ν x K) = fun x => ⨅ t : {s : Finset ℕ // K ⊆ V s},
      ENNReal.ofReal (∫ g, φ t g ∂(ν x)) := funext key
  rw [hfin]
  exact Measurable.iInf (fun t => (hmeas (φ t)).ennreal_ofReal)

/-- **The requested lemma.**  For a weakly measurable family of leafwise measures `ν`, finite on
compacts, the evaluation of `ν x` on `A ∩ ballU 1` (for `A` Borel) is measurable in `x`. -/
theorem measurable_nu {μ : MeasureTheory.Measure Work.EKLContract.X3}
    {ν : Work.EKLContract.X3 → MeasureTheory.Measure Work.EKLContract.SL3}
    {X' : Set Work.EKLContract.X3}
    (hL : Work.EKLContract.IsLeafwise μ (Work.EKLContract.Uij Work.EKLComp.h01) ν X')
    (hν : ∀ x : Work.EKLContract.X3, MeasureTheory.IsFiniteMeasureOnCompacts (ν x))
    (R : ℝ) (A : Set Work.EKLContract.SL3) (hA : MeasurableSet A) :
    Measurable fun x => (ν x (A ∩ Work.EKLContract.ballU Work.EKLComp.h01 R)).toReal := by
  set K : Set SL3 := ballU h01 R with hKdef
  have hKc : IsCompact K := by rw [hKdef]; exact Work.EKLComp.isCompact_ballU R
  have hstep : ∀ B : Set SL3, MeasurableSet B → Measurable (fun x => ν x (B ∩ K)) := by
    refine MeasurableSpace.induction_on_inter (m := borel SL3)
      (s := {s : Set SL3 | IsClosed s}) borel_eq_generateFrom_isClosed isPiSystem_isClosed
      ?_ ?_ ?_ ?_
    · simp only [Set.empty_inter, measure_empty]
      exact measurable_const
    · intro t ht
      exact measurable_apply_isCompact hL.measurable hν
        (hKc.of_isClosed_subset (ht.inter hKc.isClosed) Set.inter_subset_right)
    · intro t htm ih
      have hmeasK : Measurable (fun x => ν x K) :=
        measurable_apply_isCompact hL.measurable hν hKc
      have hfin : ∀ x, ν x (t ∩ K) ≠ ∞ := fun x =>
        ne_top_of_le_ne_top (IsFiniteMeasureOnCompacts.lt_top_of_isCompact (μ := ν x) hKc).ne
          (measure_mono Set.inter_subset_right)
      have key : (fun x => ν x (tᶜ ∩ K)) = fun x => ν x K - ν x (t ∩ K) := by
        funext x
        have h1 : K \ (t ∩ K) = tᶜ ∩ K := by
          ext y
          simp only [Set.mem_sdiff, Set.mem_inter_iff, Set.mem_compl_iff]
          tauto
        rw [← h1]
        exact measure_sdiff Set.inter_subset_right
          ((htm.inter hKc.measurableSet).nullMeasurableSet) (hfin x)
      rw [key]
      exact hmeasK.sub ih
    · intro f hfd hfm ihf
      have key : (fun x => ν x ((⋃ i, f i) ∩ K)) = fun x => ∑' i, ν x (f i ∩ K) := by
        funext x
        rw [Set.iUnion_inter]
        exact measure_iUnion
          (fun i j hij => (hfd hij).mono Set.inter_subset_left Set.inter_subset_left)
          (fun i => (hfm i).inter hKc.measurableSet)
      rw [key]
      exact Measurable.ennreal_tsum ihf
  have := (hstep A hA).ennreal_toReal
  simpa [hKdef] using this

end Work.EKLCompLeaf
