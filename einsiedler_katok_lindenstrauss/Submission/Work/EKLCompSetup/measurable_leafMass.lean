import Mathlib
import Submission.Work.EKLComp.C8Defs
import Submission.Work.EKLCompLeaf.measurable_nu

/-!
# Measurability of the leaf mass `x ↦ ν x (ballU R ∩ {g | g • x ∈ X₁})`

`Work.EKLComp.leafMass ν S R x = ∫⁻ g in ballU h01 R, 1_S (g • x) ∂(ν x)`, i.e. the `ν x`-mass of
the part of the plaque `ballU h01 R` through `x` that is mapped by the action into `S`.

The family `ν` is only assumed to be weakly measurable (`IsLeafwise.measurable`: `x ↦ ∫ f dν x` is
measurable for every compactly supported continuous `f`) and finite on compact sets.  Both the
measure `ν x` *and* the integrand `g ↦ 1_S (g • x)` vary with `x`, so the statement is not a direct
consequence of `Measurable.apply_isCompact`.

The proof has three steps.

* `K = ballU h01 R` is compact, so `x ↦ ν x K` is measurable
  (`Work.EKLCompLeaf.measurable_apply_isCompact`), and a π–λ argument on the closed sets of
  `SL₃(ℝ)` (using finiteness of `ν x` on the compact `K` for the complement step) shows that the
  *Giry measurable* map `x ↦ (ν x).restrict K` exists: `Measurable.measure_of_isPiSystem`.

* Normalising to a Markov kernel.  The only obstruction to applying the kernel-integral
  measurability theorem `Measurable.lintegral_kernel_prod_right'` is that its kernel must be
  s-finite, i.e. a countable sum of *uniformly* bounded kernels; this fails here because
  `x ↦ ν x K` is not bounded.  Instead we replace `(ν x).restrict K` by the probability kernel
  `κ x = δ_1` if `ν x K = 0` and `κ x = (ν x K)⁻¹ • (ν x).restrict K` otherwise.  Then
  `(ν x).restrict K = (ν x K) • κ x` for every `x` and `κ` is a Markov kernel, hence s-finite.

* The integrand `(x, g) ↦ 1_{X₁} (g • x)` is measurable on the product (the action is continuous),
  so `x ↦ ∫⁻ g, 1_{X₁} (g • x) ∂(κ x)` is measurable
  (`Measurable.lintegral_kernel_prod_right'`), and multiplying by the measurable function
  `x ↦ ν x K` gives the claim.
-/

open MeasureTheory Filter Topology
open scoped ENNReal Matrix
open Work.EKLContract Work.EKLComp

set_option linter.style.haveILetI false
set_option linter.unusedVariables false

noncomputable section

namespace Work.EKLCompSetup

theorem measurable_leafMass
    {μ : MeasureTheory.Measure Work.EKLContract.X3}
    {ν : Work.EKLContract.X3 → MeasureTheory.Measure Work.EKLContract.SL3}
    {X' X₁ : Set Work.EKLContract.X3}
    (hL : Work.EKLContract.IsLeafwise μ (Work.EKLContract.Uij Work.EKLComp.h01) ν X')
    (hν : ∀ x, MeasureTheory.IsFiniteMeasureOnCompacts (ν x))
    (hX₁ : MeasurableSet X₁) (R : ℝ) :
    Measurable fun x => Work.EKLComp.leafMass ν X₁ R x := by
  classical
  set K : Set Work.EKLContract.SL3 := Work.EKLContract.ballU Work.EKLComp.h01 R with hKdef
  have hKc : IsCompact K := by rw [hKdef]; exact Work.EKLComp.isCompact_ballU R
  -- Step 1a: `x ↦ ν x K` is measurable.
  have hmeasK : Measurable fun x : Work.EKLContract.X3 => ν x K :=
    Work.EKLCompLeaf.measurable_apply_isCompact hL.measurable hν hKc
  -- Step 1b: the restricted family is a measurable map into the space of measures.
  have hres : Measurable fun x : Work.EKLContract.X3 => (ν x).restrict K := by
    have hfin : ∀ x : Work.EKLContract.X3, IsFiniteMeasure ((ν x).restrict K) := fun x => by
      haveI := hν x
      exact ⟨by rw [Measure.restrict_apply_univ]
                exact IsFiniteMeasureOnCompacts.lt_top_of_isCompact hKc⟩
    haveI := hfin
    refine Measurable.measure_of_isPiSystem (μ := fun x => (ν x).restrict K)
      borel_eq_generateFrom_isClosed isPiSystem_isClosed ?_ ?_
    · intro s hs
      have hcomp : IsCompact (s ∩ K) :=
        hKc.of_isClosed_subset (hs.inter hKc.isClosed) Set.inter_subset_right
      have h1 : Measurable fun x : Work.EKLContract.X3 => ν x (s ∩ K) :=
        Work.EKLCompLeaf.measurable_apply_isCompact hL.measurable hν hcomp
      convert h1 using 2
      exact Measure.restrict_apply hs.measurableSet
    · show Measurable fun x : Work.EKLContract.X3 => ((ν x).restrict K) Set.univ
      convert Work.EKLCompLeaf.measurable_apply_isCompact hL.measurable hν hKc using 2
      exact Measure.restrict_apply_univ K
  -- Step 2: the normalised probability kernel.
  have hscalar : Measurable fun p : ℝ≥0∞ × Measure Work.EKLContract.SL3 => p.1 • p.2 := by
    refine Measure.measurable_of_measurable_coe _ (fun s hs => ?_)
    simp only [Measure.smul_apply, smul_eq_mul]
    exact measurable_fst.mul ((Measure.measurable_coe hs).comp measurable_snd)
  have hnorm : Measurable fun x : Work.EKLContract.X3 =>
      (ν x K)⁻¹ • (ν x).restrict K :=
    hscalar.comp (Measurable.prod (f := fun x : Work.EKLContract.X3 =>
      ((ν x K)⁻¹, (ν x).restrict K)) hmeasK.inv hres)
  -- The normalising scalar `c x = 1 - ν x K * (ν x K)⁻¹` vanishes exactly when `ν x K` is a
  -- finite nonzero number, so `κ` below is a Markov kernel.
  have hc : Measurable fun x : Work.EKLContract.X3 =>
      (1 : ℝ≥0∞) - (ν x K) * (ν x K)⁻¹ :=
    measurable_const.sub (hmeasK.mul hmeasK.inv)
  have hdirac : Measurable fun x : Work.EKLContract.X3 =>
      ((1 : ℝ≥0∞) - (ν x K) * (ν x K)⁻¹) • Measure.dirac (1 : Work.EKLContract.SL3) :=
    hscalar.comp (Measurable.prod (f := fun x : Work.EKLContract.X3 =>
      ((1 : ℝ≥0∞) - (ν x K) * (ν x K)⁻¹, Measure.dirac (1 : Work.EKLContract.SL3)))
      hc measurable_const)
  have hkmeas : Measurable fun x : Work.EKLContract.X3 =>
      (ν x K)⁻¹ • (ν x).restrict K
        + ((1 : ℝ≥0∞) - (ν x K) * (ν x K)⁻¹) • Measure.dirac (1 : Work.EKLContract.SL3) :=
    hnorm.add hdirac
  let κ : ProbabilityTheory.Kernel Work.EKLContract.X3 Work.EKLContract.SL3 := ⟨_, hkmeas⟩
  have hκx : ∀ x : Work.EKLContract.X3, κ x = (ν x K)⁻¹ • (ν x).restrict K
      + ((1 : ℝ≥0∞) - (ν x K) * (ν x K)⁻¹) • Measure.dirac (1 : Work.EKLContract.SL3) :=
    fun x => rfl
  have htop : ∀ x : Work.EKLContract.X3, ν x K ≠ ∞ := fun x => by
    haveI := hν x
    exact (IsFiniteMeasureOnCompacts.lt_top_of_isCompact hKc).ne
  haveI hκ : ProbabilityTheory.IsMarkovKernel κ := ⟨fun x => ⟨by
    rw [hκx x, Measure.add_apply, Measure.smul_apply, Measure.smul_apply,
      Measure.restrict_apply_univ, Measure.dirac_apply_of_mem (Set.mem_univ (1 : Work.EKLContract.SL3))]
    simp only [smul_eq_mul, mul_one]
    by_cases h0 : ν x K = 0
    · simp [h0]
    · rw [ENNReal.inv_mul_cancel h0 (htop x), ENNReal.mul_inv_cancel h0 (htop x), tsub_self,
        add_zero]⟩⟩
  -- Step 3: the decomposition `(ν x).restrict K = (ν x K) • κ x`.
  have hdecomp : ∀ x : Work.EKLContract.X3, (ν x).restrict K = (ν x K) • (κ x) := by
    intro x
    rw [hκx x, smul_add, smul_smul, smul_smul]
    by_cases h0 : ν x K = 0
    · have hμ0 : (ν x).restrict K = 0 := by
        rw [← Measure.measure_univ_eq_zero, Measure.restrict_apply_univ, h0]
      rw [hμ0, h0]
      simp
    · rw [ENNReal.mul_inv_cancel h0 (htop x), tsub_self, mul_zero, zero_smul, one_smul, add_zero]
  -- Step 4: joint measurability of the integrand and the kernel integral.
  have hF : Measurable fun p : Work.EKLContract.X3 × Work.EKLContract.SL3 =>
      (X₁.indicator (fun _ => (1 : ℝ≥0∞))) (p.2 • p.1) := by
    have hsm : Measurable fun p : Work.EKLContract.X3 × Work.EKLContract.SL3 => p.2 • p.1 := by
      fun_prop
    exact (Measurable.indicator measurable_const hX₁).comp hsm
  have hInt : Measurable fun x : Work.EKLContract.X3 =>
      ∫⁻ g, (X₁.indicator (fun _ => (1 : ℝ≥0∞))) (g • x) ∂(κ x) :=
    Measurable.lintegral_kernel_prod_right' (κ := κ) hF
  -- Step 5: assembly.
  have hmain : ∀ x : Work.EKLContract.X3, Work.EKLComp.leafMass ν X₁ R x =
      ν x K * ∫⁻ g, (X₁.indicator (fun _ => (1 : ℝ≥0∞))) (g • x) ∂(κ x) := by
    intro x
    rw [Work.EKLComp.leafMass, ← hKdef, hdecomp x, lintegral_smul_measure, smul_eq_mul]
  rw [show (fun x => Work.EKLComp.leafMass ν X₁ R x) = fun x : Work.EKLContract.X3 =>
      ν x K * ∫⁻ g, (X₁.indicator (fun _ => (1 : ℝ≥0∞))) (g • x) ∂(κ x) from funext hmain]
  exact hmeasK.mul hInt

/-- The same statement with real values, which is the form in which the leaf mass is used in
`Work.EKLComp.C8Setup.X₂_def`. -/
theorem measurable_leafMass_toReal
    {μ : MeasureTheory.Measure Work.EKLContract.X3}
    {ν : Work.EKLContract.X3 → MeasureTheory.Measure Work.EKLContract.SL3}
    {X' X₁ : Set Work.EKLContract.X3}
    (hL : Work.EKLContract.IsLeafwise μ (Work.EKLContract.Uij Work.EKLComp.h01) ν X')
    (hν : ∀ x, MeasureTheory.IsFiniteMeasureOnCompacts (ν x))
    (hX₁ : MeasurableSet X₁) (R : ℝ) :
    Measurable fun x => (Work.EKLComp.leafMass ν X₁ R x).toReal :=
  (measurable_leafMass hL hν hX₁ R).ennreal_toReal

end Work.EKLCompSetup
