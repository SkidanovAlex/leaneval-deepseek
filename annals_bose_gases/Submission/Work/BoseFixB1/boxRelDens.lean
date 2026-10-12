import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB1.WinPair.pairWord_subst_win
import Submission.Work.BoseFixB1.integrableOn_boxPairKernel
import Submission.Work.BoseFixB1.integrable_W_mul_boxPairDens
import Submission.Work.BoseFixB1.integrable_relDensJointAlt
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1.boxRelDens` — the relative-coordinate decomposition of `boxA2`

The box (`B(u)`) analogue of the corpus's relative-density decomposition of `q4PairWord`
(`SmallBoxPairRelDecomp.q4PairWord_eq_relDens`):

    boxA2 ℓ volA A (χ(xᵢ)χ(xⱼ)W(xᵢ−xⱼ)) Φ
      = ∫_u W(u)·boxPairDensSum volA ℓ A χ Φ u ,

i.e. the pairing word `Σ_{i≠j}∫_{abox}(PᵢPⱼΦ)(QⱼQᵢΦ)χ(xᵢ)χ(xⱼ)W(xᵢ−xⱼ)` is the integral over
the *relative* coordinate `u = xᵢ − xⱼ` of the kernel `W` against the summed pair density.

The route is the corpus's: per pair `(i,j)`,

* the two-slot peel `Submission.BoseGases.peel_pair_kernel` turns the box integral into
  `∫_{acube}∫_{acube}` of the kernel against the peeled fibre,
* which is `boxPairFibreFun` by definition, and
* the relative-coordinate substitution `Work.BoseFixB1.WinPair.pairWord_subst_win` (applied
  to the box-restricted window `winChi ℓ χ`, which equals `χ` because `χ` vanishes off the
  box `A ⊆ acube ℓ`) replaces `z ↦ u = y − z`, the circle closing because `boxPairDens`
  integrates over `A` and `χ` vanishes off `A`.

Integrability inputs (the two `hF`/`hInt` hypotheses of `boxA2Summand`) are
`Work.BoseFixB1.integrableOn_boxPairKernel` (`Submission/Work/BoseFixB1/integrableOn_boxPairKernel.lean`)
and `Work.BoseFixB1.integrable_relDensJointAlt`
(`Submission/Work/BoseFixB1/integrable_relDensJointAlt.lean`); the finite-sum/`u`-integral
exchange uses `Work.BoseFixB1.integrable_W_mul_boxPairDens`.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped Topology Real BigOperators ENNReal

namespace Work.BoseFixB1

open _root_.BoseGases Submission.BoseGases

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

/-- `sucAboveInv` inverts `Fin.succAbove`: the unique `j'` with `i.succAbove j' = j` is
`sucAboveInv i j h`. -/
lemma sucAboveInv_succAbove {n : ℕ} (i : Fin (n + 1)) (j' : Fin n)
    (h : i ≠ i.succAbove j') : Submission.BoseGases.sucAboveInv i (i.succAbove j') h = j' :=
  Fin.succAbove_right_injective (succAbove_sucAboveInv i (i.succAbove j') h)

/-- `boxPairFibreFun` at `(i, i.succAbove j')` is the raw peeled pair fibre with the
distinguished slot `j'`. -/
lemma boxPairFibreFun_succAbove {N : ℕ} (volA ℓ : ℝ) {A : Set E3}
    (Φ : X (N + 2) → ℝ) (i : Fin (N + 2)) (j' : Fin (N + 1)) (y z : E3) :
    boxPairFibreFun volA ℓ A Φ i (i.succAbove j') y z
      = ∫ r2 in abox N ℓ,
          (Work.UBBInputs8.boxPInd volA A i
              (Work.UBBInputs8.boxPInd volA A (i.succAbove j') Φ) (ins2 i j' y z r2))
            * (Work.UBBInputs8.boxQInd volA A (i.succAbove j')
                (Work.UBBInputs8.boxQInd volA A i Φ) (ins2 i j' y z r2)) := by
  rw [boxPairFibreFun, dif_pos (Fin.ne_succAbove i j'), sucAboveInv_succAbove]

/-- **The per-pair relative-coordinate identity.**  For distinct slots the box integral of the
pairing summand against the kernel `χ(xᵢ)χ(xⱼ)W(xᵢ−xⱼ)` is `∫_u W(u)·(∫_{z∈A} χ(z+u)χ(z)·
boxPairFibreFun (z+u) z)`.  The two hypotheses are the integrability inputs: `hF` (the box
integrand, `Work.BoseFixB1.integrableOn_boxPairKernel`) and `hInt` (the joint relative
integrand, `Work.BoseFixB1.integrable_relDensJoint`). -/
theorem boxA2Summand {N : ℕ} {ℓ volA : ℝ} {A : Set E3}
    (hℓ : 0 < ℓ) (hAc : A ⊆ acube ℓ)
    {χ : E3 → ℝ} (hχsupp : ∀ z, z ∉ A → χ z = 0)
    {Φ : X (N + 2) → ℝ} {W : E3 → ℝ}
    {i j : Fin (N + 2)} (hij : i ≠ j)
    (hF : IntegrableOn (fun x : X (N + 2) =>
      Work.UBBInputs8.boxPInd volA A i (Work.UBBInputs8.boxPInd volA A j Φ) x
        * Work.UBBInputs8.boxQInd volA A j (Work.UBBInputs8.boxQInd volA A i Φ) x
        * (χ (x i) * χ (x j) * W (x i - x j)))
      (abox (N + 2) ℓ) volume)
    (hInt : Integrable (Function.uncurry (fun y u : E3 =>
      winChi ℓ χ y * W u * winChi ℓ χ (y - u)
        * boxPairFibreFun volA ℓ A Φ i j y (y - u)))
      (volume.prod volume)) :
    (∫ x in abox (N + 2) ℓ,
      Work.UBBInputs8.boxPInd volA A i (Work.UBBInputs8.boxPInd volA A j Φ) x
        * Work.UBBInputs8.boxQInd volA A j (Work.UBBInputs8.boxQInd volA A i Φ) x
        * (χ (x i) * χ (x j) * W (x i - x j)))
      = ∫ u, W u * (∫ z in A, χ (z + u) * χ z
          * boxPairFibreFun volA ℓ A Φ i j (z + u) z) := by
  have hwin : ∀ z : E3, winChi ℓ χ z = χ z := by
    intro z
    by_cases hz : z ∈ acube ℓ
    · exact winChi_of_mem hz
    · rw [winChi_eq_zero hz, hχsupp z (fun h => hz (hAc h))]
  set j' := Submission.BoseGases.sucAboveInv i j hij with hj'def
  have hj : i.succAbove j' = j := Submission.BoseGases.succAbove_sucAboveInv i j hij
  rw [← hj] at hF hInt ⊢
  set Q : E3 → E3 → ℝ := fun y z => boxPairFibreFun volA ℓ A Φ i (i.succAbove j') y z
  have hunfold : ∀ y z : E3, (∫ r2 in abox N ℓ,
        (Work.UBBInputs8.boxPInd volA A i
            (Work.UBBInputs8.boxPInd volA A (i.succAbove j') Φ) (ins2 i j' y z r2))
          * (Work.UBBInputs8.boxQInd volA A (i.succAbove j')
              (Work.UBBInputs8.boxQInd volA A i Φ) (ins2 i j' y z r2)))
      = Q y z := fun y z => (boxPairFibreFun_succAbove (A := A) volA ℓ Φ i j' y z).symm
  have hE : (∫ x in abox (N + 2) ℓ,
        Work.UBBInputs8.boxPInd volA A i (Work.UBBInputs8.boxPInd volA A (i.succAbove j') Φ) x
          * Work.UBBInputs8.boxQInd volA A (i.succAbove j')
              (Work.UBBInputs8.boxQInd volA A i Φ) x
          * (χ (x i) * χ (x (i.succAbove j')) * W (x i - x (i.succAbove j'))))
      = ∫ y in acube ℓ, ∫ z in acube ℓ,
          (χ y * χ z * W (y - z)) * Q y z := by
    rw [peel_pair_kernel (p := N) (ℓ := ℓ) hℓ i j'
      (G := fun x : X (N + 2) =>
        Work.UBBInputs8.boxPInd volA A i (Work.UBBInputs8.boxPInd volA A (i.succAbove j') Φ) x
          * Work.UBBInputs8.boxQInd volA A (i.succAbove j')
              (Work.UBBInputs8.boxQInd volA A i Φ) x)
      (w := fun y z : E3 => χ y * χ z * W (y - z)) hF]
    simp only [hunfold]
  rw [hE]
  -- the substitution: `z ↦ u = y − z` (via the box-restricted window `winChi ℓ χ = χ`)
  have hLHS : (∫ y in acube ℓ, ∫ z in acube ℓ, (χ y * χ z * W (y - z)) * Q y z)
      = ∫ y in acube ℓ, ∫ z in acube ℓ,
          winChi ℓ χ y * W (y - z) * winChi ℓ χ z * Q y z := by
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    refine integral_congr_ae (Eventually.of_forall fun z => ?_)
    simp only [← hwin y, ← hwin z]
    ring
  rw [hLHS, WinPair.pairWord_subst_win (s := ℓ) (χ := χ) (W := W) (Q := Q) hInt]
  -- the `z`-integral collapses onto `A` because `χ` vanishes off `A`
  refine integral_congr_ae (Eventually.of_forall fun u => ?_)
  have hsupp : ∀ z : E3, z ∉ A → χ (z + u) * χ z * Q (z + u) z = 0 := by
    intro z hz
    rw [hχsupp z hz]
    ring
  have h1 : (∫ z in A, χ (z + u) * χ z * Q (z + u) z)
      = ∫ z, χ (z + u) * χ z * Q (z + u) z :=
    setIntegral_eq_integral_of_forall_compl_eq_zero hsupp
  have h2 : (∫ z, winChi ℓ χ (z + u) * winChi ℓ χ z * Q (z + u) z)
      = ∫ z, χ (z + u) * χ z * Q (z + u) z := by
    refine integral_congr_ae (Eventually.of_forall fun z => ?_)
    simp only [hwin (z + u), hwin z]
  have hpt : (∫ z, winChi ℓ χ (z + u) * winChi ℓ χ z * Q (z + u) z)
      = ∫ z in A, χ (z + u) * χ z * Q (z + u) z := h2.trans h1.symm
  exact congrArg (fun t => W u * t) hpt

/-- **The assembly.**  Summing the per-pair identity `boxA2Summand` over `pairSet` and
exchanging the finite sum with the `u`-integral (whose summands are integrable by
`integrable_W_mul_boxPairDens`, from the joint integrability hypothesis) gives the
relative-density form of `boxA2`. -/
private theorem boxRelDens_assembly {N : ℕ} {ℓ volA : ℝ} {A : Set E3}
    (hℓ : 0 < ℓ) (hAc : A ⊆ acube ℓ)
    {χ : E3 → ℝ} (hχsupp : ∀ z, z ∉ A → χ z = 0)
    {Φ : X (N + 2) → ℝ} {W : E3 → ℝ}
    (hFAll : ∀ p ∈ pairSet (N + 2), IntegrableOn (fun x : X (N + 2) =>
      Work.UBBInputs8.boxPInd volA A p.1 (Work.UBBInputs8.boxPInd volA A p.2 Φ) x
        * Work.UBBInputs8.boxQInd volA A p.2 (Work.UBBInputs8.boxQInd volA A p.1 Φ) x
        * (χ (x p.1) * χ (x p.2) * W (x p.1 - x p.2)))
      (abox (N + 2) ℓ) volume)
    (hIntAll : ∀ p ∈ pairSet (N + 2), Integrable (Function.uncurry (fun y u : E3 =>
      winChi ℓ χ y * W u * winChi ℓ χ (y - u)
        * boxPairFibreFun volA ℓ A Φ p.1 p.2 y (y - u)))
      (volume.prod volume)) :
    boxA2 ℓ volA A (fun x y => χ x * χ y * W (x - y)) Φ
      = ∫ u, W u * boxPairDensSum volA ℓ A χ Φ u := by
  have hpair : ∀ p ∈ pairSet (N + 2),
      (∫ x in abox (N + 2) ℓ,
        Work.UBBInputs8.boxPInd volA A p.1 (Work.UBBInputs8.boxPInd volA A p.2 Φ) x
          * Work.UBBInputs8.boxQInd volA A p.2 (Work.UBBInputs8.boxQInd volA A p.1 Φ) x
          * (χ (x p.1) * χ (x p.2) * W (x p.1 - x p.2)))
        = ∫ u, W u * boxPairDens volA ℓ A χ Φ p.1 p.2 u := by
    intro p hp
    exact boxA2Summand (i := p.1) (j := p.2) hℓ hAc hχsupp (Finset.mem_filter.mp hp).2
      (hFAll p hp) (hIntAll p hp)
  simp only [boxA2, boxPairDensSum]
  rw [show (∫ u, W u * ∑ p ∈ pairSet (N + 2), boxPairDens volA ℓ A χ Φ p.1 p.2 u)
      = ∑ p ∈ pairSet (N + 2), ∫ u, W u * boxPairDens volA ℓ A χ Φ p.1 p.2 u from by
    rw [show (fun u : E3 => W u * ∑ p ∈ pairSet (N + 2),
              boxPairDens volA ℓ A χ Φ p.1 p.2 u)
        = (fun u : E3 => ∑ p ∈ pairSet (N + 2),
              W u * boxPairDens volA ℓ A χ Φ p.1 p.2 u) from by
      funext u
      rw [Finset.mul_sum]]
    rw [integral_finsetSum]
    intro p hp
    exact integrable_W_mul_boxPairDens hℓ hAc hχsupp (Finset.mem_filter.mp hp).2 (hIntAll p hp)]
  exact Finset.sum_congr rfl hpair

theorem boxRelDens {N : ℕ} {ℓ volA : ℝ} {A : Set (EuclideanSpace ℝ (Fin 3))}
    (hA : MeasurableSet A) (hℓ : 0 < ℓ) (hAc : A ⊆ Submission.BoseGases.acube ℓ)
    (hvolA : volA = (MeasureTheory.volume A).toReal) (hvolpos : 0 < volA)
    {χ : EuclideanSpace ℝ (Fin 3) → ℝ} (hχc : ContDiff ℝ (⊤ : ℕ∞) χ)
    (hχs : HasCompactSupport χ) (hχsupp : ∀ z, z ∉ A → χ z = 0)
    {Φ : Submission.BoseGases.X (N + 2) → ℝ} (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ)
    {W : EuclideanSpace ℝ (Fin 3) → ℝ} (hWint : MeasureTheory.Integrable W) :
    Work.BoseFixB1.boxA2 ℓ volA A (fun x y => χ x * χ y * W (x - y)) Φ
      = ∫ u, W u * Work.BoseFixB1.boxPairDensSum volA ℓ A χ Φ u := by
  exact boxRelDens_assembly hℓ hAc hχsupp
    (fun p hp => integrableOn_boxPairKernel hA hℓ hAc hvolA hvolpos hχc hχs hΦ hWint
      (Finset.mem_filter.mp hp).2)
    (fun p hp => integrable_relDensJointAlt hA hℓ hAc hvolA hvolpos hχc hχs hΦ hWint
      (Finset.mem_filter.mp hp).2)

end Work.BoseFixB1
