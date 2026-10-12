import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB1.BoxPairIntGenC2.fibreFreeContDiff
import Submission.Work.BoseFixB1B.boxPairDensFourier_re_eqC0
import Submission.Work.BoseFixB1B.wMR_diagFourier
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1B.wMR_memLp_one_contDiff`

The momentum-space windowed pairing content `q ↦ boxWinModeRGen ℓ volA A χ Φ q` of the box
Schrödinger operator is integrable in the momentum variable, for a merely *continuous* window
`χ` (vanishing off the measurable box `A ⊆ acube ℓ`) and a smooth state `Φ`.

The proof combines three ingredients:

* `Work.BoseFixB1B.boxPairDensFourier_re_eqC0` (already proved): the real part of the
  momentum-space box pair content is `volA⁻¹` times `boxWinModeRGen`;
* `Work.BoseFixB1B.wMR_diagFourier` (the analytic core, a separate file): the "diagonal Fourier
  transform" `q ↦ ∫_A ∫_A χ y χ z e^{i⟪q,y−z⟫} F (y,z)` of a *smooth* kernel against a continuous
  window is in `L¹`;
* `Work.BoseFixB1.BoxPairIntGenC2.fibreFactorC` + `fibreFreeContDiff`: the peeled box pair
  fibre factors through the two box indicators times an indicator-free fibre which is jointly
  smooth, so that on `A × A` the fibre *is* that smooth function.
-/

noncomputable section

open MeasureTheory

namespace Work.BoseFixB1B

/-- On `A × A` the peeled box pair fibre agrees with the indicator-free (smooth) fibre, so the
per-pair momentum integral is unchanged when the fibre is replaced by `boxPairFibreFree`. -/
theorem wMR_perPair_int_eq_free {N : ℕ} {ℓ volA : ℝ} {A : Set (EuclideanSpace ℝ (Fin 3))}
    (hA : MeasurableSet A) (hℓ : 0 < ℓ) (hAc : A ⊆ Submission.BoseGases.acube ℓ)
    {χ : EuclideanSpace ℝ (Fin 3) → ℝ}
    {Φ : Submission.BoseGases.X (N + 2) → ℝ} (hΦc : Continuous Φ)
    (i j : Fin (N + 2)) (hij : i ≠ j) (q : EuclideanSpace ℝ (Fin 3)) :
    (∫ y in A, ∫ z in A, (χ y : ℂ) * (χ z : ℂ)
        * Complex.exp (Complex.I * ((inner ℝ q (y - z) : ℝ) : ℂ))
        * ((Work.BoseFixB1.boxPairFibreFun volA ℓ A Φ i j y z : ℝ) : ℂ))
      = (∫ y in A, ∫ z in A, (χ y : ℂ) * (χ z : ℂ)
        * Complex.exp (Complex.I * ((inner ℝ q (y - z) : ℝ) : ℂ))
        * ((Work.BoseFixB1.BoxPairIntGenC2.boxPairFibreFree volA ℓ A Φ i
            (Submission.BoseGases.sucAboveInv i j hij) y z : ℝ) : ℂ)) := by
  refine setIntegral_congr_fun hA (fun y hy => ?_)
  refine setIntegral_congr_fun hA (fun z hz => ?_)
  rw [Work.BoseFixB1.BoxPairIntGenC2.fibreFactorC hℓ hAc i j hij hΦc y z,
    Set.indicator_of_mem hy, Set.indicator_of_mem hz, one_mul, one_mul]

theorem wMR_memLp_one_contDiff {N : ℕ} {ℓ volA : ℝ} {A : Set (EuclideanSpace ℝ (Fin 3))}
    (hA : MeasurableSet A) (hℓ : 0 < ℓ) (hAc : A ⊆ Submission.BoseGases.acube ℓ)
    (hvolA : volA = (MeasureTheory.volume A).toReal) (hvolpos : 0 < volA)
    {χ : EuclideanSpace ℝ (Fin 3) → ℝ} (hχc : Continuous χ) (hχs : HasCompactSupport χ)
    (hχsupp : ∀ z, z ∉ A → χ z = 0)
    {Φ : Submission.BoseGases.X (N + 2) → ℝ} (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) :
    MeasureTheory.MemLp (Work.BoseFixB1.boxWinModeRGen ℓ volA A χ Φ) 1
      (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))) := by
  classical
  have hΦc : Continuous Φ := hΦ.continuous
  -- `A ⊆ acube ℓ` in the unfolded coordinate form used by the analytic input
  have hAc' : ∀ z ∈ A, ∀ j : Fin 3, -(ℓ/2) ≤ z j ∧ z j ≤ ℓ/2 := by
    intro z hz j
    obtain ⟨h1, h2⟩ := Set.mem_Icc.mp (hAc hz j)
    refine ⟨?_, h2⟩
    have he : -ℓ / 2 = -(ℓ / 2) := by ring
    rwa [he] at h1
  -- Step 1: the momentum-space pair content is in `L¹`
  have hBF : MeasureTheory.MemLp
      (Work.BoseFixB1.boxPairDensFourier volA ℓ A χ Φ) 1
      (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))) := by
    unfold Work.BoseFixB1.boxPairDensFourier
    refine MeasureTheory.memLp_finsetSum (Submission.BoseGases.pairSet (N + 2)) (fun p hp => ?_)
    obtain ⟨i, j⟩ := p
    have hij : i ≠ j := by simpa [Submission.BoseGases.pairSet] using hp
    have hF : ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry (fun y z : EuclideanSpace ℝ (Fin 3) =>
        Work.BoseFixB1.BoxPairIntGenC2.boxPairFibreFree volA ℓ A Φ i
          (Submission.BoseGases.sucAboveInv i j hij) y z)) :=
      Work.BoseFixB1.BoxPairIntGenC2.fibreFreeContDiff hA hℓ hAc hΦ i
        (Submission.BoseGases.sucAboveInv i j hij)
    have hfree := wMR_diagFourier (A := A) hA hℓ hAc' hχc hχs hF
    refine hfree.ae_eq (Filter.Eventually.of_forall (fun q => ?_))
    exact (wMR_perPair_int_eq_free (volA := volA) hA hℓ hAc hΦc i j hij q).symm
  -- Step 2: take real parts and multiply by `volA`
  have h2 : MeasureTheory.MemLp
      (fun q : EuclideanSpace ℝ (Fin 3) =>
        volA * (Work.BoseFixB1.boxPairDensFourier volA ℓ A χ Φ q).re) 1
      (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))) :=
    hBF.re.const_mul volA
  -- Step 3: `boxWinModeRGen` is that function
  refine h2.ae_eq (Filter.Eventually.of_forall (fun q => ?_))
  have h := Work.BoseFixB1B.boxPairDensFourier_re_eqC0 hA hℓ hAc hvolA hvolpos hχc hχs
    hχsupp hΦc q
  rw [h]
  exact mul_inv_cancel_left₀ (ne_of_gt hvolpos) _

end Work.BoseFixB1B
