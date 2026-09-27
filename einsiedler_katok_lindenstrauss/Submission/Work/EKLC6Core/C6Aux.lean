import Mathlib
import Submission.Work.EKLC6Core.growth_le_HcondSig
import Submission.Work.EKLC6Core.isPlaqueAlgebra_comap
import Submission.Work.EKLC6Core.Hcond_mono
import Submission.Work.EKLComp.partSigma_eq_unions_atoms
import Submission.Work.EKLContract.All
import Submission.Work.EKLRelCross.leafwise_acovariant
import Submission.Work.EKLNonExc.VFacts
import Submission.Work.EKLProd.sl3EntryBox_compact

/-!
# `Work.EKLC6Core.C6Aux` — auxiliary notation and lemmas for `lintegral_atomInfo_le`

This module collects the technical facts about the *pulled back* plaque algebra
`comap (aDiag t ·) A` needed to compute the conditional expectation of the indicator of a
`partSigma P`-atom as a leafwise (`ν x`-)average over the shape.

It deliberately re-proves (under new names) the facts `Work.EKLC6Core.measurableSet_shape`,
`Work.EKLC6Core.exists_V_subset_shape`, `Work.EKLC6Core.shape_mass_pos_and_lt_top` and
`Work.EKLC6Core.condExp_shape_eq` of the module `EKLC6Core.HcondSig_le_growth`: that module
cannot be imported together with `EKLC6Core.growth_le_HcondSig` (which defines `atomInfo`),
because the two declare clashing auxiliary declarations (`shape_comap_eq`).  Here only
`isPlaqueAlgebra_comap` (which *is* importable together with `growth_le_HcondSig`) is used for
the plaque-algebra transport.

The σ-algebras are passed through the wrapper `Work.EKLRelCross.MSAlg` wherever the *ambient*
σ-algebra of `X₃` is needed as well: a local hypothesis of class type `MeasurableSpace X₃`
would otherwise be preferred over the global Borel instance by type class search.
-/

open MeasureTheory Filter Topology
open scoped ENNReal

noncomputable section

set_option linter.unusedVariables false
set_option linter.style.haveILetI false

namespace Work.EKLC6Core

open Work.EKLContract

/-! ## 1. The conditional probability of the atom of a finite partition -/

/-- The `comap (aDiag t ·) A`-conditional probability of the atom of the finite partition `P`
containing `x`, written as the finite sum of the products of the indicators of the parts with the
conditional expectations of those indicators.  Since the parts of `P` partition `X₃`, exactly one
term survives and this is `condExp (comap (aDiag t ·) A) μ 1_[x]_P x`. -/
def atomCondProb (μ : Measure X3) (S : Work.EKLRelCross.MSAlg) (t : Fin 3 → ℝ)
    (P : FinPart X3) : X3 → ℝ :=
  fun x => ∑ i, (P.parts i).indicator
    (condExp (MeasurableSpace.comap (fun y : X3 => aDiag t • y) S.m) μ
      ((P.parts i).indicator (fun _ => (1 : ℝ)))) x

/-- The defining formula of `atomCondProb`, atom by atom. -/
theorem atomCondProb_apply (μ : Measure X3) (S : Work.EKLRelCross.MSAlg) (t : Fin 3 → ℝ)
    (P : FinPart X3) (x : X3) :
    atomCondProb μ S t P x = ∑ i, (P.parts i).indicator (fun _ =>
      condExp (MeasurableSpace.comap (fun y : X3 => aDiag t • y) S.m) μ
        ((P.parts i).indicator (fun _ => (1 : ℝ))) x) x := rfl

/-- Measurability of `atomCondProb`. -/
theorem measurable_atomCondProb (μ : Measure X3) (S : Work.EKLRelCross.MSAlg)
    (hSle : S.m ≤ borel X3) (t : Fin 3 → ℝ) (P : FinPart X3) :
    Measurable (atomCondProb μ S t P) := by
  classical
  have hm : MeasurableSpace.comap (fun y : X3 => aDiag t • y) S.m ≤ borel X3 :=
    (MeasurableSpace.comap_mono hSle).trans
      ((continuous_const_smul (aDiag t)).measurable.comap_le)
  refine Finset.measurable_sum Finset.univ (fun i _ => ?_)
  refine Measurable.indicator ?_ (P.measurable i)
  exact Measurable.mono (MeasureTheory.stronglyMeasurable_condExp (m := MeasurableSpace.comap
    (fun y : X3 => aDiag t • y) S.m) (μ := μ)
      (f := ((P.parts i).indicator (fun _ => (1 : ℝ))))).measurable hm le_rfl

/-! ## 2. The shape of a plaque algebra -/

theorem one_mem_shape_of_plaque (A : MeasurableSpace X3) (U : Subgroup SL3) (x : X3) :
    (1 : SL3) ∈ shape A U x :=
  ⟨U.one_mem, by rw [one_smul]; exact Set.mem_sInter.mpr (fun s hs => hs.2)⟩

/-- The shape of a plaque algebra is measurable. -/
theorem measurableSet_shape_of_plaque {U : Subgroup SL3} (hU : IsHoro U) {A : MeasurableSpace X3}
    {Z : Set X3} (hA : IsPlaqueAlgebra U Z A) {x : X3} (hx : x ∈ Z) :
    MeasurableSet (shape A U x) := by
  obtain ⟨O, hOopen, hOeq⟩ := (hA.2.2.2 x hx).2.2.1
  rw [hOeq]
  exact hOopen.measurableSet.inter hU.1.measurableSet

/-- The shape of a plaque algebra contains `V δ ∩ U` for some `δ > 0`. -/
theorem exists_V_subset_shape_of_plaque {U : Subgroup SL3} {A : MeasurableSpace X3}
    {Z : Set X3} (hA : IsPlaqueAlgebra U Z A) {x : X3} (hx : x ∈ Z) :
    ∃ δ : ℝ, 0 < δ ∧ V δ ∩ (U : Set SL3) ⊆ shape A U x := by
  obtain ⟨O, hOopen, hOeq⟩ := (hA.2.2.2 x hx).2.2.1
  have h1 : (1 : SL3) ∈ O := by
    have h := one_mem_shape_of_plaque A U x
    rw [hOeq] at h
    exact h.1
  obtain ⟨δ, hδ, hsub⟩ := Work.EKLNonExc.V_nhds_basis O (hOopen.mem_nhds h1)
  exact ⟨δ, hδ, fun g hg => by rw [hOeq]; exact ⟨hsub hg.1, hg.2⟩⟩

/-- The `ν x`-mass of the shape of a plaque algebra is positive and finite. -/
theorem shape_mass_pos_and_lt_top_of_plaque {μ : Measure X3} [IsProbabilityMeasure μ]
    {U : Subgroup SL3} (hU : IsHoro U) {ν : X3 → Measure SL3} {X' : Set X3}
    (hL : IsLeafwise μ U ν X') {A : MeasurableSpace X3} {Z : Set X3}
    (hA : IsPlaqueAlgebra U Z A) {x : X3} (hx : x ∈ X') (hZ : x ∈ Z) :
    0 < ν x (shape A U x) ∧ ν x (shape A U x) < ⊤ := by
  constructor
  · obtain ⟨δ, hδ, hsub⟩ := exists_V_subset_shape_of_plaque hA hZ
    have h1 : ν x (V δ ∩ (U : Set SL3)) = ν x (V δ) := by
      have hdiff : ν x (V δ \ (U : Set SL3)) = 0 :=
        le_antisymm (le_trans (measure_mono (fun g hg => hg.2))
          (le_of_eq (hL.carried x hx))) bot_le
      have hadd := measure_inter_add_sdiff (V δ) hU.1.measurableSet (μ := ν x)
      rw [hdiff, add_zero] at hadd
      exact hadd
    calc 0 < ν x (V δ) := hL.pos x hx δ hδ
      _ = ν x (V δ ∩ (U : Set SL3)) := h1.symm
      _ ≤ ν x (shape A U x) := measure_mono hsub
  · obtain ⟨C, hC⟩ := (hA.2.2.2 x hZ).2.2.2
    have hbox : IsCompact {g : SL3 | ∀ p q : Fin 3, -(|C| + 1) ≤ g p q ∧ g p q ≤ |C| + 1} :=
      Work.EKLProd.sl3EntryBox_compact (fun _ _ => -(|C| + 1)) (fun _ _ => |C| + 1)
    refine lt_of_le_of_lt (measure_mono ?_) ((hL.radon x hx).lt_top_of_isCompact hbox)
    intro u hu p q
    have h1 : |u p q| ≤ |C| + 1 := le_trans (hC u hu p q) (by linarith [le_abs_self C])
    exact abs_le.mp h1

/-! ## 3. The conditional expectation of the pulled-back algebra is a leafwise average -/

/-- The `condexp` field of `IsLeafwise`, applied to the pulled-back plaque algebra
`comap (aDiag t ·) A`: for a bounded Borel test function, the conditional expectation w.r.t.
`comap (aDiag t ·) A` is the `ν x`-average over the shape of the pull-back atom. -/
theorem condExp_shape_eq_pullback {μ : Measure X3} [IsProbabilityMeasure μ]
    {U : Subgroup SL3} (hU : IsHoro U) {ν : X3 → Measure SL3} {X' : Set X3}
    (hL : IsLeafwise μ U ν X') {S : Work.EKLRelCross.MSAlg} {Z : Set X3}
    (hA : IsPlaqueAlgebra U Z S.m) (t : Fin 3 → ℝ)
    (hmp : MeasurePreserving (fun y : X3 => aDiag t • y) μ μ) (hZ : μ Zᶜ = 0)
    (f : X3 → ℝ) (hf : Measurable f) (hfb : ∃ C, ∀ y, |f y| ≤ C) :
    ∀ᵐ x ∂μ, condExp (MeasurableSpace.comap (fun y : X3 => aDiag t • y) S.m) μ f x =
      (∫ u in shape (MeasurableSpace.comap (fun y : X3 => aDiag t • y) S.m) U x,
          f (u • x) ∂(ν x))
        / (ν x (shape (MeasurableSpace.comap (fun y : X3 => aDiag t • y) S.m) U x)).toReal := by
  have hAZ : MeasurableSet Z := hA.1 Z hA.2.2.1
  have hTZ : μ ((fun y : X3 => aDiag t • y) ⁻¹' Z)ᶜ = 0 := by
    rw [← Set.preimage_compl, hmp.measure_preimage hAZ.compl.nullMeasurableSet]
    exact hZ
  have hres : μ.restrict ((fun y : X3 => aDiag t • y) ⁻¹' Z) = μ :=
    Measure.restrict_eq_self_of_ae_mem (by rw [ae_iff]; exact hTZ)
  have hfield := hL.condexp ((fun y : X3 => aDiag t • y) ⁻¹' Z)
    (MeasurableSpace.comap (fun y : X3 => aDiag t • y) S.m) (isPlaqueAlgebra_comap hU t hA)
    f hf hfb
  rw [← hres]
  filter_upwards [hfield] with x hx
  exact hx

/-! ## 4. Set integrals of indicators over the shape -/

/-- The `ν`-integral over a set `W ⊆ SL₃(ℝ)` of the indicator of `{u | u • x ∈ S}`. -/
theorem setIntegral_indicator_smul {ν : Measure SL3} {W : Set SL3} (hW : MeasurableSet W)
    {S : Set X3} (hS : MeasurableSet S) (x : X3) :
    (∫ u in W, (S.indicator (fun _ => (1 : ℝ))) (u • x) ∂ν) =
      (ν (W ∩ {u : SL3 | u • x ∈ S})).toReal := by
  classical
  have hT : MeasurableSet {u : SL3 | u • x ∈ S} :=
    hS.preimage (continuous_id.smul continuous_const).measurable
  have hfun : (fun u : SL3 => (S.indicator (fun _ => (1 : ℝ))) (u • x))
      = ({u : SL3 | u • x ∈ S}).indicator (fun _ => (1 : ℝ)) := by
    funext u
    by_cases h : u • x ∈ S
    · rw [Set.indicator_of_mem h, Set.indicator_of_mem (show u ∈ {u : SL3 | u • x ∈ S} from h)]
    · rw [Set.indicator_of_notMem h,
        Set.indicator_of_notMem (show u ∉ {u : SL3 | u • x ∈ S} from h)]
  rw [hfun, MeasureTheory.setIntegral_indicator hT, MeasureTheory.setIntegral_const, smul_eq_mul,
    mul_one, MeasureTheory.measureReal_def, Set.inter_comm]

/-! ## 5. The pointwise surprisal of a partition atom -/

/-- The Shannon surprisal `-log μ_x(atom)` of the `comap (aDiag t ·) S.m`-atom of a finite
partition `P`. -/
def atomSurprisal (μ : Measure X3) (S : Work.EKLRelCross.MSAlg) (t : Fin 3 → ℝ)
    (P : FinPart X3) : X3 → ℝ :=
  fun x => -Real.log (atomCondProb μ S t P x)

/-- The same surprisal written atom by atom: the "height function" of the partition. -/
def atomSurprisalSum (μ : Measure X3) (S : Work.EKLRelCross.MSAlg) (t : Fin 3 → ℝ)
    (P : FinPart X3) : X3 → ℝ :=
  fun x => ∑ i, ((P.parts i).indicator (fun y => -Real.log
    (condExp (MeasurableSpace.comap (fun y : X3 => aDiag t • y) S.m) μ
      ((P.parts i).indicator (fun _ => (1 : ℝ))) y)) x)

/-- **Exactly one part of `P` contains `x`**, so the two forms of the surprisal agree. -/
theorem atomSurprisal_eq_sum (μ : Measure X3) (S : Work.EKLRelCross.MSAlg) (t : Fin 3 → ℝ)
    (P : FinPart X3) (x : X3) :
    atomSurprisal μ S t P x = atomSurprisalSum μ S t P x := by
  classical
  obtain ⟨i₀, hi₀⟩ : ∃ i, x ∈ P.parts i := by
    have h : x ∈ ⋃ i, P.parts i := by rw [P.cover]; exact Set.mem_univ x
    simpa using h
  have huniq : ∀ i, x ∈ P.parts i → i = i₀ := by
    intro i hi
    by_contra hne
    exact Set.disjoint_left.mp (P.disjoint hne) hi hi₀
  let E : (i : Fin P.n) → X3 → ℝ := fun i => condExp
    (MeasurableSpace.comap (fun y : X3 => aDiag t • y) S.m) μ
      ((P.parts i).indicator (fun _ => (1 : ℝ)))
  have h1 : (∑ i, (P.parts i).indicator (E i) x) = E i₀ x := by
    have hsum : (∑ i, (P.parts i).indicator (E i) x) = (P.parts i₀).indicator (E i₀) x := by
      refine Finset.sum_eq_single (f := fun i : Fin P.n => (P.parts i).indicator (E i) x) i₀
        (fun i _ hne => ?_) (fun h => absurd (Finset.mem_univ i₀) h)
      exact Set.indicator_of_notMem (fun hx => hne (huniq i hx)) (E i)
    rw [hsum, Set.indicator_of_mem hi₀]
  have h2 : (∑ i, ((P.parts i).indicator (fun y => -Real.log (E i y)) x)) = -Real.log (E i₀ x) := by
    have hsum : (∑ i, ((P.parts i).indicator (fun y => -Real.log (E i y)) x))
        = (P.parts i₀).indicator (fun y => -Real.log (E i₀ y)) x := by
      refine Finset.sum_eq_single
        (f := fun i : Fin P.n => (P.parts i).indicator (fun y => -Real.log (E i y)) x) i₀
        (fun i _ hne => ?_) (fun h => absurd (Finset.mem_univ i₀) h)
      exact Set.indicator_of_notMem (fun hx => hne (huniq i hx)) (fun y => -Real.log (E i y))
    rw [hsum, Set.indicator_of_mem hi₀]
  have h3 : atomCondProb μ S t P x = E i₀ x := by
    simp only [atomCondProb]
    exact h1
  have h4 : atomSurprisalSum μ S t P x = -Real.log (E i₀ x) := by
    simp only [atomSurprisalSum]
    exact h2
  rw [atomSurprisal, h3, h4]

/-- Measurability of the surprisal. -/
theorem measurable_atomSurprisal (μ : Measure X3) (S : Work.EKLRelCross.MSAlg)
    (hSle : S.m ≤ borel X3) (t : Fin 3 → ℝ) (P : FinPart X3) :
    Measurable (atomSurprisal μ S t P) :=
  (measurable_atomCondProb μ S hSle t P).log.neg

/-- Measurability of the atom-by-atom form of the surprisal. -/
theorem measurable_atomSurprisalSum (μ : Measure X3) (S : Work.EKLRelCross.MSAlg)
    (hSle : S.m ≤ borel X3) (t : Fin 3 → ℝ) (P : FinPart X3) :
    Measurable (atomSurprisalSum μ S t P) := by
  classical
  have hm : MeasurableSpace.comap (fun y : X3 => aDiag t • y) S.m ≤ borel X3 :=
    (MeasurableSpace.comap_mono hSle).trans
      ((continuous_const_smul (aDiag t)).measurable.comap_le)
  refine Finset.measurable_sum Finset.univ (fun i _ => ?_)
  refine Measurable.indicator ?_ (P.measurable i)
  exact (Measurable.mono (MeasureTheory.stronglyMeasurable_condExp (m := MeasurableSpace.comap
    (fun y : X3 => aDiag t • y) S.m) (μ := μ)
      (f := ((P.parts i).indicator (fun _ => (1 : ℝ))))).measurable hm le_rfl).log.neg

/-! ## 6. The pull-back σ-algebra and the shape of its atoms -/

/-- The pull-back of a σ-algebra along the diagonal flow `y ↦ aDiag t • y`.  (An `abbrev`, so
that it is unfolded by elaboration and never competes with the ambient σ-algebra of `X₃` as a
type class candidate.) -/
abbrev pullAlg (t : Fin 3 → ℝ) (S : Work.EKLRelCross.MSAlg) : MeasurableSpace X3 :=
  MeasurableSpace.comap (fun y : X3 => aDiag t • y) S.m

/-- The pull-back of a sub-σ-algebra of the Borel σ-algebra is again a sub-σ-algebra of it. -/
theorem pullAlg_le_borel (t : Fin 3 → ℝ) (S : Work.EKLRelCross.MSAlg) (h : S.m ≤ borel X3) :
    pullAlg t S ≤ borel X3 :=
  (MeasurableSpace.comap_mono h).trans ((continuous_const_smul (aDiag t)).measurable.comap_le)

/-- The shape of an atom of the pull-back algebra, inside the shape of the original atom: the
inclusion `shape (pullAlg t S) U x ⊆ shape S.m U x` requires the additivity of the atom on the
algebra. -/
theorem pullAlg_mass_pos_and_lt_top {μ : Measure X3} [IsProbabilityMeasure μ] {U : Subgroup SL3}
    (hU : IsHoro U) {ν : X3 → Measure SL3} {X' : Set X3} (hL : IsLeafwise μ U ν X')
    {S : Work.EKLRelCross.MSAlg} {Z : Set X3} (hA : IsPlaqueAlgebra U Z S.m) (t : Fin 3 → ℝ)
    {x : X3} (hx : x ∈ X') (hZ : x ∈ (fun y : X3 => aDiag t • y) ⁻¹' Z) :
    0 < ν x (shape (pullAlg t S) U x) ∧ ν x (shape (pullAlg t S) U x) < ⊤ :=
  shape_mass_pos_and_lt_top_of_plaque (μ := μ) hU hL (isPlaqueAlgebra_comap hU t hA) hx hZ

/-! ## 7. The conditional expectation of the indicator of a part -/

/-- The conditional expectation of the indicator of the `i`-th part of `P`, given the pull-back
σ-algebra `comap (aDiag t ·) S.m`. -/
def atomCondExp (μ : Measure X3) (S : Work.EKLRelCross.MSAlg) (t : Fin 3 → ℝ)
    (P : FinPart X3) (i : Fin P.n) : X3 → ℝ :=
  condExp (pullAlg t S) μ ((P.parts i).indicator (fun _ => (1 : ℝ)))

/-- The defining equation of `atomCondExp`. -/
@[simp] theorem atomCondExp_eq (μ : Measure X3) (S : Work.EKLRelCross.MSAlg) (t : Fin 3 → ℝ)
    (P : FinPart X3) (i : Fin P.n) :
    atomCondExp μ S t P i
      = condExp (pullAlg t S) μ ((P.parts i).indicator (fun _ => (1 : ℝ))) := rfl

/-- `atomCondExp` is measurable for the pull-back σ-algebra. -/
theorem measurable_atomCondExp (μ : Measure X3) (S : Work.EKLRelCross.MSAlg)
    (t : Fin 3 → ℝ) (P : FinPart X3) (i : Fin P.n) :
    Measurable[pullAlg t S] (atomCondExp μ S t P i) :=
  (MeasureTheory.stronglyMeasurable_condExp (m := pullAlg t S) (μ := μ)
    (f := ((P.parts i).indicator (fun _ => (1 : ℝ))))).measurable

/-- `atomCondExp` is Borel measurable. -/
theorem measurable_atomCondExp_borel (μ : Measure X3) (S : Work.EKLRelCross.MSAlg)
    (hSle : S.m ≤ borel X3) (t : Fin 3 → ℝ) (P : FinPart X3) (i : Fin P.n) :
    Measurable (atomCondExp μ S t P i) :=
  Measurable.mono (measurable_atomCondExp μ S t P i) (pullAlg_le_borel t S hSle) le_rfl

/-- The `comap (aDiag t ·) S.m`-conditional expectation of the indicator of a part lies in
`[0,1]` almost everywhere. -/
theorem atomCondExp_mem_Icc {μ : Measure X3} [IsProbabilityMeasure μ]
    (S : Work.EKLRelCross.MSAlg) (hSle : S.m ≤ borel X3) (t : Fin 3 → ℝ) (P : FinPart X3)
    (i : Fin P.n) : ∀ᵐ x ∂μ, atomCondExp μ S t P i x ∈ Set.Icc (0 : ℝ) 1 := by
  refine condExp_mem_Icc (μ := μ) (m := pullAlg t S) (pullAlg_le_borel t S hSle) ?_ ?_ ?_
  · exact Filter.Eventually.of_forall fun x => Set.indicator_nonneg (fun _ _ => zero_le_one) x
  · refine Filter.Eventually.of_forall fun x => ?_
    by_cases hx : x ∈ P.parts i
    · rw [Set.indicator_of_mem hx]
    · rw [Set.indicator_of_notMem hx]; norm_num
  · exact (integrable_const (1 : ℝ)).indicator (P.measurable i)

/-- The `ν x`-integral over the shape of the pulled-back atom of an integrable test function is
the `ν x`-integral over the shape of the pull-back atom.  (Trivial restatement used to fix the
elaboration.) -/
theorem atomSurprisal_eq (μ : Measure X3) (S : Work.EKLRelCross.MSAlg) (t : Fin 3 → ℝ)
    (P : FinPart X3) (x : X3) :
    atomSurprisal μ S t P x = -Real.log (atomCondProb μ S t P x) := rfl

/-! ## 8. The atom of a part and the conditional probability of the atom -/

/-- The atom of the σ-algebra of a finite partition, at a point of a part, is that part. -/
theorem atom_partSigma_eq_of_mem (P : FinPart X3) {i : Fin P.n} {x : X3}
    (hx : x ∈ P.parts i) : atom (partSigma P) x = P.parts i := by
  refine le_antisymm ?_ ?_
  · exact Set.sInter_subset_of_mem ⟨MeasurableSpace.measurableSet_generateFrom ⟨i, rfl⟩, hx⟩
  · intro y hy
    refine Set.mem_sInter.mpr (fun S hS => ?_)
    obtain ⟨K, hK⟩ := (Work.EKLComp.partSigma_eq_unions_atoms P S).mp hS.1
    have hxK : x ∈ ⋃ j ∈ K, P.parts j := by rw [← hK]; exact hS.2
    simp only [Set.mem_iUnion, exists_prop] at hxK
    obtain ⟨j, hjK, hxj⟩ := hxK
    have hji : j = i := by
      by_contra hne
      exact Set.disjoint_left.mp (P.disjoint hne) hxj hx
    rw [hK]
    exact Set.mem_biUnion hjK (hji ▸ hy)

/-- The conditional probability of the atom of a partition containing `x` is the conditional
probability of that part. -/
theorem atomCondProb_eq_atomCondExp_of_mem (μ : Measure X3) (S : Work.EKLRelCross.MSAlg)
    (t : Fin 3 → ℝ) (P : FinPart X3) {i : Fin P.n} {x : X3} (hx : x ∈ P.parts i) :
    atomCondProb μ S t P x = atomCondExp μ S t P i x := by
  classical
  have huniq : ∀ j, x ∈ P.parts j → j = i := by
    intro j hj
    by_contra hne
    exact Set.disjoint_left.mp (P.disjoint hne) hj hx
  have hsum : (∑ j, (P.parts j).indicator
      (condExp (pullAlg t S) μ ((P.parts j).indicator (fun _ => (1 : ℝ)))) x)
      = condExp (pullAlg t S) μ ((P.parts i).indicator (fun _ => (1 : ℝ))) x := by
    have hsum' : (∑ j, (P.parts j).indicator
        (condExp (pullAlg t S) μ ((P.parts j).indicator (fun _ => (1 : ℝ)))) x)
        = (P.parts i).indicator (condExp (pullAlg t S) μ
            ((P.parts i).indicator (fun _ => (1 : ℝ)))) x := by
      refine Finset.sum_eq_single
        (f := fun j : Fin P.n =>
          (P.parts j).indicator (condExp (pullAlg t S) μ
            ((P.parts j).indicator (fun _ => (1 : ℝ)))) x)
        i (fun j _ hne => ?_) (fun h => absurd (Finset.mem_univ i) h)
      exact Set.indicator_of_notMem (fun hxj => hne (huniq j hxj))
        (condExp (pullAlg t S) μ ((P.parts j).indicator (fun _ => (1 : ℝ))))
    rw [hsum', Set.indicator_of_mem hx]
  have h1 : atomCondProb μ S t P x = (∑ j, (P.parts j).indicator
      (condExp (pullAlg t S) μ ((P.parts j).indicator (fun _ => (1 : ℝ)))) x) := rfl
  rw [h1, hsum]
  rfl

end Work.EKLC6Core
