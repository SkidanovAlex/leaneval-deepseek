/-
# The `l₂ = 0` single-scale estimate from the `ℓ¹(ℤ²)` mass bound

The target is `Work.KMTAreas.A7.LoMixedRSingleScaleStatement` (`LoMixedRDefs.lean`), the paper's
§6 model approximation in the *mixed right* case `l₁ ≥ 1`, `l₂ = 0`:

  `‖ mainPartTuple ρ P C₀ a f g l₁ 0 k₁ k₂ n ‖_{ℓ^p} ≤ C(Λ)·modelWeight A ρ l₁ 0 k₁ k₂·⌊a n⌋⁻¹
     ·‖f‖_{ℓ^{p₁}}‖g‖_{ℓ^{p₂}}`.

This module *reduces* it to the `ℓ¹(ℤ²)` mass bound `Work.KMTAreas.A7.LoMixedRMassStatement`
(`LoMixedRMassDefs.lean`): at the arithmetic height `l₂ = 0` the §6 model kernel vanishes
identically -- its arithmetic fibre set is `iwArithFreqsNew ρ 0 = ∅` -- so the mass bound is a
bound for the mass of the concrete kernel `hiKconc` alone.

The reduction is the `ℓ^p` bookkeeping described in the docstring of `LoMixedRSingleScale.lean`:

* the concrete column is the bilinear convolution with `hiKconc`
  (`varpPiece_eq_bilinOp_hiKconc`, on the guard, for bounded `f, g`);
* Young's inequality `BilinOpLp` turns the `ℓ¹(ℤ²)` mass of the kernel into the `ℓ^p` bound;
* the degenerate exponents (`eLpNorm f p₁ = ⊤` or `= 0`) are handled separately: an `ℓ^p`
  function (`1 < p`) is bounded whenever its seminorm is finite
  (`Work.KMTAreas.A5.boundedZ_of_memLp`), and a vanishing `ℒ^p`-seminorm (`p ≠ 0`) forces the
  function to be identically zero (`eq_zero_of_eLpNorm_count_eq_zero`, from `ModelApproxHi.lean`),
  in which case the column vanishes by bilinearity (`mainPartTuple_zero_left/right`).

The bookkeeping is the `l₂ = 0` analogue of `ModelApproxHiCore_of_mass`
(`Submission/Work/KMTAreas/A7/ModelApproxHi.lean`), with the model kernel replaced by `0`.
-/
import Mathlib
import Submission.Work.KMTAreas.A7.LoMixedRMassDefs
import Submission.Work.KMTAreas.A7.LoMixedRDefs

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

namespace Work.KMTAreas.A7

noncomputable section

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal BigOperators
open PointwiseErgodicTheorems Submission.PointwiseErgodicTheorems
open Work.Analysis.EndVar Work.KMTContract

/-- **The §6 model kernel vanishes at the arithmetic height `l₂ = 0`.**  The arithmetic fibre set
of the model is `iwArithFreqsNew ρ 0 = ∅` (`iwArithFreqsNew_zero`), so `arithKernelExact` -- and
therefore the twisted bilinear kernel `hiTwKernel` and its composition `hiKmod` with the two
exact-height multiplier kernels -- is identically zero. -/
theorem loMixedR_hiKmod_eq_zero (ρ : ℝ) (P : ℤ[X]) (a : ℕ → ℝ≥0) (l₁ k₁ k₂ n : ℕ) :
    hiKmod ρ P a l₁ 0 k₁ k₂ n = 0 := by
  funext j₁ j₂
  have htw : hiTwKernel ρ P l₁ 0
      (mStarF (uScale ρ (max (max l₁ 0) (max k₁ k₂))))
      (mStargF P.natDegree (uScale ρ (max (max l₁ 0) (max k₁ k₂)))) = 0 := by
    funext i₁ i₂
    simp only [hiTwKernel, arithKernelExact, iwArithFreqsNew_zero, Finset.sum_empty]
    simp
  simp only [hiKmod]
  rw [htw]
  simp [kernComp]

/-- Pointwise form of `loMixedR_hiKmod_eq_zero`. -/
theorem loMixedR_hiKmod_apply_eq_zero (ρ : ℝ) (P : ℤ[X]) (a : ℕ → ℝ≥0) (l₁ k₁ k₂ n : ℕ)
    (j₁ j₂ : ℤ) : hiKmod ρ P a l₁ 0 k₁ k₂ n j₁ j₂ = 0 :=
  congrFun (congrFun (loMixedR_hiKmod_eq_zero ρ P a l₁ k₁ k₂ n) j₁) j₂

/-! ## Degenerate cases

The single-scale estimate is bilinear in its two arguments, so if one of `f`, `g` vanishes then so
does the column.  We record the two elementary unfoldings here (they are the `mainPartTuple`
analogues of `smallMainPart`'s, in `SmallModDefs.lean`), together with the fact that on `ℤ` with
the counting measure a vanishing `ℒ^p`-seminorm (`p ≠ 0`) forces the function to vanish
identically. -/

/-- `iwConv` of the zero function (local copy of `Work.KMTAreas.A7.iwConv_zero_right`, kept here
so that the module does not have to import `SmallModDefs`). -/
theorem loMixedR_iwConv_zero_right (A : Finset Work.Analysis.IonescuWainger.Circle)
    (Φ : Work.Analysis.IonescuWainger.Circle → ℂ) :
    Work.Analysis.IWMultiplier.iwConv A Φ (0 : ℤ → ℂ) = 0 := by
  funext n
  simp [Work.Analysis.IWMultiplier.iwConv]

/-- On `ℤ` with the counting measure a function of vanishing `ℒ^p` seminorm (`p ≠ 0`) is
identically zero: every set is measurable and the counting measure has no non-empty null sets. -/
theorem loMixedR_eq_zero_of_eLpNorm_count_eq_zero {p : ENNReal} (hp : p ≠ 0) {u : ℤ → ℂ}
    (h : MeasureTheory.eLpNorm u p (MeasureTheory.Measure.count : MeasureTheory.Measure ℤ) = 0) :
    u = 0 := by
  have hsm : MeasureTheory.AEStronglyMeasurable u
      (MeasureTheory.Measure.count : MeasureTheory.Measure ℤ) :=
    MeasureTheory.AEStronglyMeasurable.of_discrete
  have h0 : u =ᵐ[MeasureTheory.Measure.count] 0 :=
    (MeasureTheory.eLpNorm_eq_zero_iff hp).mp h
  have hnull : MeasureTheory.Measure.count {m : ℤ | u m ≠ 0} = 0 := MeasureTheory.ae_iff.mp h0
  funext n
  by_contra hn
  have hne : MeasureTheory.Measure.count {m : ℤ | u m ≠ 0} ≠ 0 := by
    rw [MeasureTheory.Measure.count_ne_zero_iff]
    exact ⟨n, hn⟩
  exact hne hnull

/-- With `g = 0` the concrete column vanishes (pointwise). -/
theorem loMixedR_mainPartTuple_zero_right (ρ : ℝ) (P : Polynomial ℤ) (C₀ : ℕ) (a : ℕ → ℝ≥0)
    (f : ℤ → ℂ) (l₁ l₂ k₁ k₂ n : ℕ) (x : ℤ) :
    mainPartTuple ρ P C₀ a f 0 l₁ l₂ k₁ k₂ n x = 0 := by
  have h : mainPartTuple ρ P C₀ a f 0 l₁ l₂ k₁ k₂ = 0 := by
    funext n x
    simp only [mainPartTuple]
    split_ifs with h
    · simp only [varpPiece, AhalfR, Ahalf, Ablock, Fpiece, Gpiece, piece, piExact, kmtProj,
        kmtPj]
      simp [loMixedR_iwConv_zero_right]
    · rfl
  exact congrFun (congrFun h n) x

/-- With `f = 0` the concrete column vanishes (pointwise). -/
theorem loMixedR_mainPartTuple_zero_left (ρ : ℝ) (P : Polynomial ℤ) (C₀ : ℕ) (a : ℕ → ℝ≥0)
    (g : ℤ → ℂ) (l₁ l₂ k₁ k₂ n : ℕ) (x : ℤ) :
    mainPartTuple ρ P C₀ a 0 g l₁ l₂ k₁ k₂ n x = 0 := by
  have h : mainPartTuple ρ P C₀ a 0 g l₁ l₂ k₁ k₂ = 0 := by
    funext n x
    simp only [mainPartTuple]
    split_ifs with h
    · simp only [varpPiece, AhalfR, Ahalf, Ablock, Fpiece, Gpiece, piece, piExact, kmtProj,
        kmtPj]
      simp [loMixedR_iwConv_zero_right]
    · rfl
  exact congrFun (congrFun h n) x

/-- **The single-scale estimate of the mixed right case from the `ℓ¹(ℤ²)` mass bound.** -/
theorem LoMixedRSingleScaleOfMass (P : Polynomial ℤ) (p₁ p₂ : ENNReal)
    (hdeg : 2 ≤ P.natDegree) (hA1 : Work.KMTContract.AreaA1) (hp₁ : 1 < p₁) (htp₁ : p₁ < ⊤)
    (hp₂ : 1 < p₂) (htp₂ : p₂ < ⊤) (hsum : p₁⁻¹ + p₂⁻¹ ≤ 1)
    (hmass : Work.KMTAreas.A7.LoMixedRMassStatement P) :
    Work.KMTAreas.A7.LoMixedRSingleScaleStatement P p₁ p₂ hdeg hA1 hp₁ htp₁ hp₂ htp₂ hsum := by
  classical
  obtain ⟨A, hA, ρc, hρc, H⟩ := hmass
  refine ⟨ρc, hρc, ?_⟩
  intro ρ hρ hρle
  obtain ⟨C, hsumm, hbound⟩ := H ρ hρ hρle
  refine ⟨A, hA, ?_⟩
  intro C₀ hC₀
  refine ⟨fun Λ => max (C Λ) 1, ?_⟩
  intro a Λ l₁ l₂ k₁ k₂ f g hΛ ha ha1 hl₁ hl₂ n
  subst hl₂
  have hp₁0 : p₁ ≠ 0 := ne_of_gt (lt_trans zero_lt_one hp₁)
  have hp₂0 : p₂ ≠ 0 := ne_of_gt (lt_trans zero_lt_one hp₂)
  have hN1 : 1 ≤ Nat.floor (a n) := Nat.floor_pos.mpr (ha1 n)
  have hw1 : (1 : ℝ) ≤ modelWeight A ρ l₁ 0 k₁ k₂ := by
    rw [modelWeight]
    exact one_le_mul_of_one_le_of_one_le
      (Real.one_le_rpow (by linarith [lmaxR_nonneg l₁ 0 k₁ k₂]) hA)
      (Real.one_le_rpow (by norm_num) (by positivity))
  have hw0 : 0 ≤ modelWeight A ρ l₁ 0 k₁ k₂ := le_trans zero_le_one hw1
  have hCnn : (0 : ℝ) ≤ (C Λ : ℝ) := by positivity
  set Xe : ENNReal := ((max (C Λ) 1 : ℝ≥0) : ENNReal)
    * ENNReal.ofReal (modelWeight A ρ l₁ 0 k₁ k₂)
    * ENNReal.ofReal (((Nat.floor (a n) : ℕ) : ℝ)⁻¹) with hXe
  have hXe0 : Xe ≠ 0 := by
    rw [hXe]
    refine mul_ne_zero (mul_ne_zero (ENNReal.coe_ne_zero.mpr ?_) ?_) ?_
    · exact ne_of_gt (lt_of_lt_of_le zero_lt_one (le_max_right (C Λ) 1))
    · exact ENNReal.ofReal_ne_zero_iff.mpr (lt_of_lt_of_le zero_lt_one hw1)
    · refine ENNReal.ofReal_ne_zero_iff.mpr ?_
      exact inv_pos.mpr (by exact_mod_cast lt_of_lt_of_le Nat.zero_lt_one hN1)
  have hgoal : MeasureTheory.eLpNorm (fun x : ℤ =>
        mainPartTuple ρ P C₀ a f g l₁ 0 k₁ k₂ n x)
      (p₁⁻¹ + p₂⁻¹)⁻¹ MeasureTheory.Measure.count
      ≤ Xe * MeasureTheory.eLpNorm f p₁ MeasureTheory.Measure.count
          * MeasureTheory.eLpNorm g p₂ MeasureTheory.Measure.count := by
    by_cases hfin : MeasureTheory.eLpNorm f p₁ MeasureTheory.Measure.count < ⊤
        ∧ MeasureTheory.eLpNorm g p₂ MeasureTheory.Measure.count < ⊤
    · obtain ⟨hf, hg⟩ := hfin
      have hfBd : Work.KMTAreas.A5.BoundedZ f := Work.KMTAreas.A5.boundedZ_of_memLp hp₁
        (MeasureTheory.memLp_iff.mpr (hf))
      have hgBd : Work.KMTAreas.A5.BoundedZ g := Work.KMTAreas.A5.boundedZ_of_memLp hp₂
        (MeasureTheory.memLp_iff.mpr (hg))
      by_cases hguard : loGuard ρ C₀ a l₁ 0 k₁ k₂ n
      · have hmain : ∀ x : ℤ, mainPartTuple ρ P C₀ a f g l₁ 0 k₁ k₂ n x
            = bilinOp (hiKconc ρ P a l₁ 0 k₁ k₂ n) f g x := by
          intro x
          rw [mainPartTuple_apply, if_pos hguard]
          exact varpPiece_eq_bilinOp_hiKconc (ρ := ρ) (P := P) (a := a) (l₁ := l₁) (l₂ := 0)
            (k₁ := k₁) (k₂ := k₂) (n := n) (f := f) (g := g) hfBd hgBd x
        have heq : MeasureTheory.eLpNorm (fun x : ℤ =>
              mainPartTuple ρ P C₀ a f g l₁ 0 k₁ k₂ n x)
            (p₁⁻¹ + p₂⁻¹)⁻¹ MeasureTheory.Measure.count
            = MeasureTheory.eLpNorm (fun x : ℤ =>
                bilinOp (hiKconc ρ P a l₁ 0 k₁ k₂ n) f g x)
              (p₁⁻¹ + p₂⁻¹)⁻¹ MeasureTheory.Measure.count := by
          congr 1
          funext x
          exact hmain x
        rw [heq]
        have hp_eq : p₁⁻¹ + p₂⁻¹ = ((p₁⁻¹ + p₂⁻¹)⁻¹)⁻¹ := (inv_inv _).symm
        have hp1' : (1 : ENNReal) ≤ (p₁⁻¹ + p₂⁻¹)⁻¹ := ENNReal.one_le_inv.mpr hsum
        have hKc : Summable fun p : ℤ × ℤ => ‖hiKconc ρ P a l₁ 0 k₁ k₂ n p.1 p.2‖ :=
          summable_hiKconc ρ P a l₁ 0 k₁ k₂ n
        have hmass_n : (∑' p : ℤ × ℤ, ‖hiKconc ρ P a l₁ 0 k₁ k₂ n p.1 p.2
              - hiKmod ρ P a l₁ 0 k₁ k₂ n p.1 p.2‖)
            ≤ (C Λ : ℝ) * modelWeight A ρ l₁ 0 k₁ k₂ * ((Nat.floor (a n) : ℕ) : ℝ)⁻¹ :=
          hbound C₀ a Λ l₁ k₁ k₂ hΛ ha ha1 hl₁ n hguard
        have htsum_eq : (∑' p : ℤ × ℤ, ‖hiKconc ρ P a l₁ 0 k₁ k₂ n p.1 p.2
              - hiKmod ρ P a l₁ 0 k₁ k₂ n p.1 p.2‖)
            = ∑' p : ℤ × ℤ, ‖hiKconc ρ P a l₁ 0 k₁ k₂ n p.1 p.2‖ := by
          refine tsum_congr (fun p => ?_)
          rw [loMixedR_hiKmod_apply_eq_zero ρ P a l₁ k₁ k₂ n p.1 p.2, sub_zero]
        have hof : ENNReal.ofReal (∑' p : ℤ × ℤ, ‖hiKconc ρ P a l₁ 0 k₁ k₂ n p.1 p.2‖)
            ≤ Xe := by
          rw [← htsum_eq, hXe]
          refine (ENNReal.ofReal_le_ofReal hmass_n).trans ?_
          rw [ENNReal.ofReal_mul (mul_nonneg hCnn hw0), ENNReal.ofReal_mul hCnn,
            ENNReal.ofReal_coe_nnreal]
          exact mul_le_mul' (mul_le_mul' (ENNReal.coe_le_coe.mpr (le_max_left (C Λ) 1)) le_rfl)
            le_rfl
        refine (BilinOpLp (K := hiKconc ρ P a l₁ 0 k₁ k₂ n)
          (p := (p₁⁻¹ + p₂⁻¹)⁻¹) (p₁ := p₁) (p₂ := p₂) hp_eq hp1' hKc f g).trans ?_
        exact mul_le_mul' (mul_le_mul' hof le_rfl) le_rfl
      · have hzero : (fun x : ℤ => mainPartTuple ρ P C₀ a f g l₁ 0 k₁ k₂ n x) = 0 := by
          funext x
          rw [mainPartTuple_apply, if_neg hguard]
          rfl
        rw [hzero]
        simp
    · rcases not_and_or.mp hfin with hf | hg
      · have hftop : MeasureTheory.eLpNorm f p₁ MeasureTheory.Measure.count = ⊤ :=
          eq_top_iff.mpr (not_lt.mp hf)
        by_cases hg0 : MeasureTheory.eLpNorm g p₂ MeasureTheory.Measure.count = 0
        · have hgz : g = 0 := loMixedR_eq_zero_of_eLpNorm_count_eq_zero hp₂0 hg0
          rw [hgz]
          have hz : (fun x : ℤ => mainPartTuple ρ P C₀ a f 0 l₁ 0 k₁ k₂ n x) = 0 := by
            funext y
            exact loMixedR_mainPartTuple_zero_right ρ P C₀ a f l₁ 0 k₁ k₂ n y
          rw [hz]
          simp
        · have hgne : MeasureTheory.eLpNorm g p₂ MeasureTheory.Measure.count ≠ 0 := hg0
          rw [hftop, ENNReal.mul_top hXe0, ENNReal.top_mul hgne]
          exact le_top
      · have hgtop : MeasureTheory.eLpNorm g p₂ MeasureTheory.Measure.count = ⊤ :=
          eq_top_iff.mpr (not_lt.mp hg)
        by_cases hf0 : MeasureTheory.eLpNorm f p₁ MeasureTheory.Measure.count = 0
        · have hfz : f = 0 := loMixedR_eq_zero_of_eLpNorm_count_eq_zero hp₁0 hf0
          rw [hfz]
          have hz : (fun x : ℤ => mainPartTuple ρ P C₀ a 0 g l₁ 0 k₁ k₂ n x) = 0 := by
            funext y
            exact loMixedR_mainPartTuple_zero_left ρ P C₀ a g l₁ 0 k₁ k₂ n y
          rw [hz]
          simp
        · have hfne : MeasureTheory.eLpNorm f p₁ MeasureTheory.Measure.count ≠ 0 := hf0
          rw [hgtop, ENNReal.mul_top (mul_ne_zero hXe0 hfne)]
          exact le_top
  rw [hXe] at hgoal
  exact hgoal

end

end Work.KMTAreas.A7
