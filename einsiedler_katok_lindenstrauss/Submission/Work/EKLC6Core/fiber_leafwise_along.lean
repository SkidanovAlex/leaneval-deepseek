import Mathlib
import Submission.Work.EKLC6Core.FibreAlongDefs
import Submission.Work.EKLC6Core.Basic
import Submission.Work.EKLC6Core.hopf_saturate
import Submission.Work.EKLC6Core.invariant_inter_plaque_ae
import Submission.Work.EKLC6Core.uminus_isHoro
import Submission.Work.EKLC6Core.covAlong
import Submission.Work.EKLC6Core.leafwise_eq_of_flower_clauses
import Submission.Work.EKLC6Core.fibre_condExp_transfer
import Submission.Work.EKLComp.prove_X3
import Submission.Work.EKLComp.LeafExistence
import Submission.Work.EKLComp.AeFreeness
import Submission.Work.EKLEntJacobs.fiber_inv
import Submission.Work.EKLRelCross.bigShape_flowers
import Submission.Work.EKLRelCross.leafwise_unique

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 800000

noncomputable section

namespace Work.EKLC6Core

open Work.EKLContract

/-! ## Helper lemmas -/

/-- Rewriting the `ν`-average along a pointwise equality of the systems. -/
private lemma nuAvg_congr {U : Subgroup SL3} {ν ν' : X3 → Measure SL3} {m : MeasurableSpace X3}
    {f : X3 → ℝ} {y : X3} (h : ν' y = ν y) : nuAvg U ν' m f y = nuAvg U ν m f y := by
  simp only [nuAvg_def, h]

/-- A `μ`-null measurable set is `fibre μ t x`-null for `μ`-a.e. `x`. -/
private lemma fibre_eq_zero_of_null {μ : Measure X3} [IsProbabilityMeasure μ]
    (t : Fin 3 → ℝ) {B : Set X3} (hB : MeasurableSet B) (hB0 : μ B = 0) :
    ∀ᵐ x ∂μ, fibre μ t x B = 0 := by
  have hm : invSig t ≤ borel X3 := by
    show MeasurableSpace.invariants (diagMap t) ≤ borel X3
    exact MeasurableSpace.invariants_le _
  have h := Work.EKLComp.kernel_measure_eq_zero μ (𝔪 := ⟨invSig t⟩) hm hB hB0
  filter_upwards [h] with x hx
  simpa [fibre, invSig_def, diagMap_def] using hx

/-- **The assembly**: the target statement, given the fibre-wise transfer of the `condexp` field
(Pisa 7.23) as a hypothesis. -/
private theorem fiber_leafwise_along_of_transfer
    (htransfer : ∀ {μ : Measure X3} [IsProbabilityMeasure μ]
        {ν : X3 → Measure SL3} {X' : Set X3} (t : Fin 3 → ℝ),
        MeasurePreserving (diagMap t) μ μ → IsLeafwise μ (Uminus t) ν X' →
        ∀ {Z : Set X3} {m : MeasurableSpace X3}, IsPlaqueAlgebra (Uminus t) Z m →
          ∀ {f : X3 → ℝ}, BorelMeas f → (∃ C, ∀ y, |f y| ≤ C) →
          ∀ᵐ x ∂μ, condExp m ((fibre μ t x).restrict Z) f
            =ᵐ[(fibre μ t x).restrict Z] nuAvg (Uminus t) ν m f)
    {μ : Measure X3} [IsProbabilityMeasure μ] [StandardBorelSpace X3]
    {ν : X3 → Measure SL3} {X' X'' : Set X3} (t : Fin 3 → ℝ)
    (hmp : MeasurePreserving (fun x : X3 => aDiag t • x) μ μ)
    (hL : IsLeafwise μ (Uminus t) ν X')
    (hcov : ACovariantAlong ν t X'') (hX'' : μ (X''ᶜ) = 0) :
    ∀ᵐ x ∂μ, IsLeafwise
      (condExpKernel μ (MeasurableSpace.invariants (fun x : X3 => aDiag t • x)) x)
      (Uminus t) ν X' := by
  classical
  have hTmeas : Measurable (fun x : X3 => aDiag t • x) :=
    (continuous_const_smul (aDiag t)).measurable
  have hU : IsHoro (Uminus t) := (uminus_isHoro t).1
  have hcontr : ∀ u ∈ Uminus t, Filter.Tendsto
      (fun n : ℕ => aDiag t ^ n * u * (aDiag t ^ n)⁻¹) Filter.atTop (𝓝 1) :=
    (uminus_isHoro t).2
  -- the flower family at every scale
  have hfam : ∀ n : ℕ, ∃ (Z G : ℕ → Set X3) (m : ℕ → MeasurableSpace X3),
      (∀ k, IsPlaqueAlgebra (Uminus t) (Z k) (m k)) ∧
      (∀ k, MeasurableSet (G k) ∧ G k ⊆ Z k) ∧
      μ (⋃ k, G k)ᶜ = 0 ∧
      (∀ k, ∀ x ∈ G k, ∀ u ∈ (V ((n : ℝ) + 2) ∩ (Uminus t : Set SL3)),
        u • x ∈ atom (m k) x) := by
    intro n
    exact Work.EKLRelCross.bigShape_flowers Work.EKLComp.prove_X3 μ (Uminus t) hU t hmp hcontr
      ((n : ℝ) + 2) (by positivity)
  choose Z G m hP using hfam
  have hplaq : ∀ n k, IsPlaqueAlgebra (Uminus t) (Z n k) (m n k) := fun n k => (hP n).1 k
  have hGmeas : ∀ n k, MeasurableSet (G n k) := fun n k => ((hP n).2.1 k).1
  have hGZ : ∀ n k, G n k ⊆ Z n k := fun n k => ((hP n).2.1 k).2
  have hcoverμ : ∀ n, μ (⋃ k, G n k)ᶜ = 0 := fun n => (hP n).2.2.1
  have hshape : ∀ n k, ∀ x ∈ G n k, ∀ u ∈ (V ((n : ℝ) + 2) ∩ (Uminus t : Set SL3)),
      u • x ∈ atom (m n k) x := fun n k => (hP n).2.2.2 k
  -- the fibre is carried by `X'` and by all the flower covers
  have hX'fib : ∀ᵐ x ∂μ, fibre μ t x X'ᶜ = 0 :=
    fibre_eq_zero_of_null t hL.meas_dom.compl hL.conull
  have hcoverfib : ∀ᵐ x ∂μ, ∀ n, fibre μ t x (⋃ k, G n k)ᶜ = 0 := by
    rw [eventually_countable_forall]
    intro n
    exact fibre_eq_zero_of_null t ((MeasurableSet.iUnion fun k => hGmeas n k).compl) (hcoverμ n)
  -- the fibre is preserved by the diagonal map
  have hinv : ∀ᵐ x ∂μ, MeasurePreserving (diagMap t) (fibre μ t x) (fibre μ t x) := by
    have h := Work.EKLEntJacobs.fiber_inv μ (fun x : X3 => aDiag t • x) hTmeas hmp
    filter_upwards [h] with x hx
    exact hx
  -- the transfer hypothesis, for the countably many flower plaque algebras and π-system tests
  have hclauseall : ∀ᵐ x ∂μ,
      ∀ i : ℕ × ℕ × Finset ↥(TopologicalSpace.countableBasis X3),
        condExp (m i.1 i.2.1) ((fibre μ t x).restrict (Z i.1 i.2.1))
            ((⋂ b ∈ (i.2.2 : Set ↥(TopologicalSpace.countableBasis X3)),
              (b : Set X3)).indicator (1 : X3 → ℝ))
          =ᵐ[(fibre μ t x).restrict (Z i.1 i.2.1)]
          nuAvg (Uminus t) ν (m i.1 i.2.1)
            ((⋂ b ∈ (i.2.2 : Set ↥(TopologicalSpace.countableBasis X3)),
              (b : Set X3)).indicator (1 : X3 → ℝ)) := by
    rw [eventually_countable_forall]
    intro i
    obtain ⟨n, k, tt⟩ := i
    set C : Set X3 := ⋂ b ∈ (tt : Set ↥(TopologicalSpace.countableBasis X3)), (b : Set X3)
      with hCdef
    have hCmem : C ∈ Work.EKLRelCross.piSys := ⟨tt, rfl⟩
    have hCmeas : Measurable (C.indicator (1 : X3 → ℝ)) :=
      measurable_const.indicator (Work.EKLRelCross.measurableSet_of_mem_piSys hCmem)
    have hCbdd : ∃ C₀, ∀ y, |(C.indicator (1 : X3 → ℝ)) y| ≤ C₀ := by
      refine ⟨1, fun y => ?_⟩
      by_cases hy : y ∈ C
      · rw [Set.indicator_of_mem hy]; norm_num
      · rw [Set.indicator_of_notMem hy]; norm_num
    exact htransfer t hmp hL (hplaq n k) hCmeas hCbdd
  filter_upwards [hinv, hX'fib, hcoverfib, hclauseall] with x hinvx hX'fibx hcoverfibx hclauseallx
  show IsLeafwise (fibre μ t x) (Uminus t) ν X'
  -- the existence of a leafwise system for the fibre
  haveI : IsProbabilityMeasure (fibre μ t x) := by
    rw [fibre_def]
    exact IsMarkovKernel.is_probability_measure' x
  obtain ⟨ν', X''', hL'⟩ := Work.EKLComp.leafwise_exists_of_free (Uminus t) hU (fibre μ t x)
    (Work.EKLComp.ae_freeness (Uminus t) hU (fibre μ t x) t hinvx hcontr)
  -- the two systems agree a.e.
  have hclausex : ∀ (n k : ℕ) (C : Set X3), C ∈ Work.EKLRelCross.piSys →
      condExp (m n k) ((fibre μ t x).restrict (Z n k)) (C.indicator (1 : X3 → ℝ))
        =ᵐ[(fibre μ t x).restrict (Z n k)]
        nuAvg (Uminus t) ν (m n k) (C.indicator (1 : X3 → ℝ)) := by
    intro n k C hC
    rw [Work.EKLRelCross.piSys, Set.mem_range] at hC
    obtain ⟨tt, htt⟩ := hC
    rw [← htt]
    exact hclauseallx (n, k, tt)
  have hνeq : ∀ᵐ y ∂(fibre μ t x), ν' y = ν y :=
    leafwise_eq_of_flower_clauses Work.EKLComp.prove_X3 (Uminus t) hU t hinvx hcontr
      hX'fibx hL.radon hL.carried hL.normalised Z G m hplaq hGmeas hGZ hcoverfibx hshape
      hclausex hL'
  -- assemble the structure
  refine ⟨hL.meas_dom, hX'fibx, hL.radon, hL.carried, hL.normalised, hL.measurable, hL.pos,
    hL.equivariant, ?_⟩
  intro Z' m' hPA' f hf hfb
  have h1 := hL'.condexp Z' m' hPA' f hf hfb
  have h2 : ∀ᵐ y ∂((fibre μ t x).restrict Z'), ν' y = ν y :=
    MeasureTheory.ae_mono MeasureTheory.Measure.restrict_le_self hνeq
  filter_upwards [h1, h2] with y h1y h2y
  rw [h1y]
  exact nuAvg_congr h2y

theorem fiber_leafwise_along {μ : MeasureTheory.Measure Work.EKLContract.X3}
    [MeasureTheory.IsProbabilityMeasure μ] [StandardBorelSpace Work.EKLContract.X3]
    {ν : Work.EKLContract.X3 → MeasureTheory.Measure Work.EKLContract.SL3}
    {X' X'' : Set Work.EKLContract.X3} (t : Fin 3 → ℝ)
    (hmp : MeasureTheory.MeasurePreserving
      (fun x : Work.EKLContract.X3 => Work.EKLContract.aDiag t • x) μ μ)
    (hL : Work.EKLContract.IsLeafwise μ (Work.EKLC6Core.Uminus t) ν X')
    (hcov : Work.EKLC6Core.ACovariantAlong ν t X'') (hX'' : μ (X''ᶜ) = 0) :
    ∀ᵐ x ∂μ, Work.EKLContract.IsLeafwise
      (ProbabilityTheory.condExpKernel μ (MeasurableSpace.invariants
        (fun x : Work.EKLContract.X3 => Work.EKLContract.aDiag t • x)) x)
      (Work.EKLC6Core.Uminus t) ν X' := by
  refine fiber_leafwise_along_of_transfer (htransfer := ?_) t hmp hL hcov hX''
  intro μ' inst ν' X'' t' hmp' hL' Z m hPA f hf hfb
  exact fibre_condExp_transfer t' hmp' hL' hPA hf hfb

/-- **The `ACovariant` form.**  The conclusion of `Work.EKLC6Core.fiber_leafwise_along` with the
single-direction covariance `ACovariantAlong ν t X''` replaced by the full `A`-covariance
`ACovariant ν X''` (this is the statement of `Work.EKLC6Core.fiber_leafwise_thm`). -/
theorem fiber_leafwise_of_acovariant {μ : MeasureTheory.Measure Work.EKLContract.X3}
    [MeasureTheory.IsProbabilityMeasure μ] [StandardBorelSpace Work.EKLContract.X3]
    {ν : Work.EKLContract.X3 → MeasureTheory.Measure Work.EKLContract.SL3}
    {X' X'' : Set Work.EKLContract.X3} (t : Fin 3 → ℝ)
    (hmp : MeasureTheory.MeasurePreserving
      (fun x : Work.EKLContract.X3 => Work.EKLContract.aDiag t • x) μ μ)
    (hL : Work.EKLContract.IsLeafwise μ (Work.EKLC6Core.Uminus t) ν X')
    (hcov : Work.EKLC6Core.ACovariant ν X'') (hX'' : μ (X''ᶜ) = 0) :
    ∀ᵐ x ∂μ, Work.EKLContract.IsLeafwise
      (ProbabilityTheory.condExpKernel μ (MeasurableSpace.invariants
        (fun x : Work.EKLContract.X3 => Work.EKLContract.aDiag t • x)) x)
      (Work.EKLC6Core.Uminus t) ν X' := by
  refine fiber_leafwise_along t hmp hL ?_ hX''
  intro z x hx hzx
  exact hcov ((z : ℝ) • t) x hx hzx

end Work.EKLC6Core
