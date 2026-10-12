import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB1B.integral_abox_indep_mul_two_coords
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1B.boxPIndPairFactor`

Pair factorisation of the FS box projection `P_i P_j` (`Work.UBBInputs8.boxPInd`).

With `P_{i}Φ = 1_A(x i) · (1/volA)∫_{z∈A} Φ(x|i↦z)` (FS `eq:HBU`), the two-fold projection
`P_i P_j Φ` is, pointwise,

    P_i P_j Φ (x) = 1_A(x i) · 1_A(x j) · ((1/volA)·((1/volA)·J x)) ,

where `J x = ∫_{z∈A} ∫_{z'∈A} Φ(x|i↦z|j↦z')` is independent of the two slots `i ≠ j`
(`boxPInd_pair_eq`).  Hence, with `G := ((1/volA)·((1/volA)·J))²` (which is exactly the
integrand of the hypotheses `hInt1`, `hInt2`, `hInt5`),

    (P_i P_j Φ)² = G · (1_A(x i) · 1_A(x j))   and
    (P_i P_j Φ)² · w(x i, x j) = G · (1_A(x i) · (1_A(x j) · w(x i, x j))) ,

i.e. the integrand factorises as `G` (depending on no slot in `{i,j}`) times a function of the
two slots `(x i, x j)`.  The two-slot peel
`Work.BoseFixB1B.integral_abox_indep_mul_two_coords` then integrates the slot pair out:

    ∫_{abox N L} G·(1_A⊗1_A)(x i,x j) = ((∫_{abox N L} G)/L⁶)·∫_{acube L × acube L} 1_A⊗1_A ,
    ∫_{abox N L} G·(1_A⊗(1_A·w))       = ((∫_{abox N L} G)/L⁶)·∫_{acube L × acube L} 1_A⊗(1_A·w) .

Dividing the second by the (nonzero, `hApos`) normalisation of the first gives the requested
identity: the `x`-integral of `(P_i P_j Φ)² w(x i, x j)` is the ratio of the `x`-integral of
`(P_i P_j Φ)²` to the normalisation `∫_{acube L × acube L} 1_A⊗1_A`, times the double integral
of `1_A⊗(1_A·w)`.
-/

noncomputable section

open MeasureTheory

namespace Work.BoseFixB1B

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option maxHeartbeats 1000000

/-- The slot-independent double mean `J x = ∫_{z∈A} ∫_{z'∈A} Φ(x|i↦z|j↦z')` of `P_i P_j Φ`. -/
abbrev boxPairJ (volA : ℝ) (A : Set E3) {N : ℕ} (i j : Fin N)
    (Φ : Submission.BoseGases.X N → ℝ) : Submission.BoseGases.X N → ℝ :=
  fun x => ∫ z in A, ∫ z' in A, Φ (Function.update (Function.update x i z) j z')

/-- `G = ((1/volA)·((1/volA)·J))²`, the slot-independent factor of `(P_i P_j Φ)²`. -/
abbrev boxPairG (volA : ℝ) (A : Set E3) {N : ℕ} (i j : Fin N)
    (Φ : Submission.BoseGases.X N → ℝ) : Submission.BoseGases.X N → ℝ :=
  fun x => ((1 / volA) * ((1 / volA) * boxPairJ volA A i j Φ x)) ^ 2

/-- **The two-fold box projection, pointwise.** -/
theorem boxPInd_pair_eq {N : ℕ} (volA : ℝ) (A : Set E3) {i j : Fin N} (hij : i ≠ j)
    (Φ : Submission.BoseGases.X N → ℝ) (x : Submission.BoseGases.X N) :
    Work.UBBInputs8.boxPInd volA A i (Work.UBBInputs8.boxPInd volA A j Φ) x
      = A.indicator (fun _ => (1 : ℝ)) (x i) * A.indicator (fun _ => (1 : ℝ)) (x j)
        * ((1 / volA) * ((1 / volA) * ∫ z in A, ∫ z' in A,
            Φ (Function.update (Function.update x i z) j z'))) := by
  simp only [Work.UBBInputs8.boxPInd, Function.update_apply, if_neg (Ne.symm hij)]
  rw [MeasureTheory.integral_mul_const, MeasureTheory.integral_const_mul]
  ring

/-- **The square of the two-fold box projection, pointwise**: the indicator product times the
slot-independent factor `G`. -/
theorem boxPInd_pair_sq {N : ℕ} (volA : ℝ) (A : Set E3) {i j : Fin N} (hij : i ≠ j)
    (Φ : Submission.BoseGases.X N → ℝ) (x : Submission.BoseGases.X N) :
    (Work.UBBInputs8.boxPInd volA A i (Work.UBBInputs8.boxPInd volA A j Φ) x) ^ 2
      = boxPairG volA A i j Φ x
        * (A.indicator (fun _ => (1 : ℝ)) (x i) * A.indicator (fun _ => (1 : ℝ)) (x j)) := by
  rw [boxPInd_pair_eq volA A hij Φ x]
  simp only [boxPairG, boxPairJ]
  by_cases hi : x i ∈ A <;> by_cases hj : x j ∈ A <;>
    simp [Set.indicator_of_mem, Set.indicator_of_notMem, hi, hj]

/-- **The square of the two-fold box projection against a pair weight, pointwise.** -/
theorem boxPInd_pair_w {N : ℕ} (volA : ℝ) (A : Set E3) {i j : Fin N} (hij : i ≠ j)
    (Φ : Submission.BoseGases.X N → ℝ) (w : E3 → E3 → ℝ) (x : Submission.BoseGases.X N) :
    (Work.UBBInputs8.boxPInd volA A i (Work.UBBInputs8.boxPInd volA A j Φ) x) ^ 2
        * w (x i) (x j)
      = boxPairG volA A i j Φ x
        * (A.indicator (fun _ => (1 : ℝ)) (x i)
            * (A.indicator (fun _ => (1 : ℝ)) (x j) * w (x i) (x j))) := by
  rw [boxPInd_pair_eq volA A hij Φ x]
  simp only [boxPairG, boxPairJ]
  by_cases hi : x i ∈ A <;> by_cases hj : x j ∈ A <;>
    simp [Set.indicator_of_mem, Set.indicator_of_notMem, hi, hj]

/-- **`G` does not depend on the slots `i ≠ j`.** -/
theorem boxPairG_indep {N : ℕ} (volA : ℝ) (A : Set E3) {i j : Fin N} (hij : i ≠ j)
    (Φ : Submission.BoseGases.X N → ℝ) (x : Submission.BoseGases.X N) (a b : E3) :
    boxPairG volA A i j Φ (Function.update (Function.update x i a) j b)
      = boxPairG volA A i j Φ x := by
  have hupd : ∀ z z' : E3,
      Function.update (Function.update (Function.update (Function.update x i a) j b) i z) j z'
        = Function.update (Function.update x i z) j z' := by
    intro z z'
    funext w
    simp only [Function.update_apply]
    by_cases hwi : w = i
    · subst hwi; simp [hij]
    · by_cases hwj : w = j
      · subst hwj; simp [Ne.symm hij]
      · simp [hwi, hwj]
  simp only [boxPairG, boxPairJ]
  have hJ : (∫ z in A, ∫ z' in A, Φ (Function.update
        (Function.update (Function.update (Function.update x i a) j b) i z) j z'))
      = ∫ z in A, ∫ z' in A, Φ (Function.update (Function.update x i z) j z') := by
    refine integral_congr_ae (Filter.Eventually.of_forall (fun z => ?_))
    refine integral_congr_ae (Filter.Eventually.of_forall (fun z' => ?_))
    exact congrArg Φ (hupd z z')
  rw [hJ]

theorem boxPIndPairFactor {N : ℕ} {L : ℝ} (hL : 0 < L) {A : Set (EuclideanSpace ℝ (Fin 3))}
    (hA : MeasurableSet A) (hAc : A ⊆ Submission.BoseGases.acube L) {volA : ℝ} (hvol : volA ≠ 0)
    {i j : Fin N} (hij : i ≠ j) {Φ : Submission.BoseGases.X N → ℝ}
    {w : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) → ℝ}
    (hInt1 : MeasureTheory.IntegrableOn (fun x : Submission.BoseGases.X N =>
        (((1 / volA) * ((1 / volA) * ∫ z in A, ∫ z' in A,
            Φ (Function.update (Function.update x i z) j z')))) ^ 2
          * (A.indicator (fun _ => (1 : ℝ)) (x i)
              * (A.indicator (fun _ => (1 : ℝ)) (x j) * w (x i) (x j))))
      (Submission.BoseGases.abox N L))
    (hInt2 : MeasureTheory.IntegrableOn (fun x : Submission.BoseGases.X N =>
        (((1 / volA) * ((1 / volA) * ∫ z in A, ∫ z' in A,
            Φ (Function.update (Function.update x i z) j z')))) ^ 2)
      (Submission.BoseGases.abox N L))
    (hInt3 : MeasureTheory.IntegrableOn
      (fun p : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) =>
        A.indicator (fun _ => (1 : ℝ)) p.1
          * (A.indicator (fun _ => (1 : ℝ)) p.2 * w p.1 p.2))
      (Submission.BoseGases.acube L ×ˢ Submission.BoseGases.acube L))
    (hInt4 : MeasureTheory.IntegrableOn
      (fun p : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) =>
        A.indicator (fun _ => (1 : ℝ)) p.1 * A.indicator (fun _ => (1 : ℝ)) p.2)
      (Submission.BoseGases.acube L ×ˢ Submission.BoseGases.acube L))
    (hInt5 : MeasureTheory.IntegrableOn (fun x : Submission.BoseGases.X N =>
        (((1 / volA) * ((1 / volA) * ∫ z in A, ∫ z' in A,
            Φ (Function.update (Function.update x i z) j z')))) ^ 2
          * (A.indicator (fun _ => (1 : ℝ)) (x i) * A.indicator (fun _ => (1 : ℝ)) (x j)))
      (Submission.BoseGases.abox N L))
    (hApos : 0 < ∫ p in Submission.BoseGases.acube L ×ˢ Submission.BoseGases.acube L,
        A.indicator (fun _ => (1 : ℝ)) p.1 * A.indicator (fun _ => (1 : ℝ)) p.2) :
    ∫ x in Submission.BoseGases.abox N L,
        (Work.UBBInputs8.boxPInd volA A i (Work.UBBInputs8.boxPInd volA A j Φ) x) ^ 2
          * w (x i) (x j)
      = ((∫ x in Submission.BoseGases.abox N L,
              (Work.UBBInputs8.boxPInd volA A i (Work.UBBInputs8.boxPInd volA A j Φ) x) ^ 2)
            / (∫ p in Submission.BoseGases.acube L ×ˢ Submission.BoseGases.acube L,
                A.indicator (fun _ => (1 : ℝ)) p.1 * A.indicator (fun _ => (1 : ℝ)) p.2))
          * (∫ p in Submission.BoseGases.acube L ×ˢ Submission.BoseGases.acube L,
              A.indicator (fun _ => (1 : ℝ)) p.1
                * (A.indicator (fun _ => (1 : ℝ)) p.2 * w p.1 p.2)) := by
  -- the three integrability hypotheses, restated for the slot-independent factor `G`
  have hI1 : MeasureTheory.IntegrableOn (fun x : Submission.BoseGases.X N =>
      boxPairG volA A i j Φ x
        * (A.indicator (fun _ => (1 : ℝ)) (x i)
            * (A.indicator (fun _ => (1 : ℝ)) (x j) * w (x i) (x j))))
      (Submission.BoseGases.abox N L) := by
    dsimp only [boxPairG, boxPairJ]
    exact hInt1
  have hI2 : MeasureTheory.IntegrableOn (boxPairG volA A i j Φ)
      (Submission.BoseGases.abox N L) := by
    simpa only [boxPairG, boxPairJ] using hInt2
  have hI5 : MeasureTheory.IntegrableOn (fun x : Submission.BoseGases.X N =>
      boxPairG volA A i j Φ x
        * (A.indicator (fun _ => (1 : ℝ)) (x i) * A.indicator (fun _ => (1 : ℝ)) (x j)))
      (Submission.BoseGases.abox N L) := by
    dsimp only [boxPairG, boxPairJ]
    exact hInt5
  -- the two peelings of the slot pair `(i, j)`
  have hindep : ∀ (x : Submission.BoseGases.X N) (a b : E3),
      boxPairG volA A i j Φ (Function.update (Function.update x i a) j b)
        = boxPairG volA A i j Φ x :=
    fun x a b => boxPairG_indep volA A hij Φ x a b
  have hpeel1 := integral_abox_indep_mul_two_coords (n := N) (ℓ := L) hL
    (i := i) (j := j) hij (g := boxPairG volA A i j Φ)
    (h := fun a b : E3 =>
      A.indicator (fun _ => (1 : ℝ)) a * (A.indicator (fun _ => (1 : ℝ)) b * w a b))
    hindep hI1 hI2 hInt3
  have hpeel2 := integral_abox_indep_mul_two_coords (n := N) (ℓ := L) hL
    (i := i) (j := j) hij (g := boxPairG volA A i j Φ)
    (h := fun a b : E3 => A.indicator (fun _ => (1 : ℝ)) a * A.indicator (fun _ => (1 : ℝ)) b)
    hindep hI5 hI2 hInt4
  -- the pointwise factorisations, integrated
  have hLHS : (∫ x in Submission.BoseGases.abox N L,
        (Work.UBBInputs8.boxPInd volA A i (Work.UBBInputs8.boxPInd volA A j Φ) x) ^ 2
          * w (x i) (x j))
      = ((∫ x in Submission.BoseGases.abox N L, boxPairG volA A i j Φ x) / L ^ 6)
        * (∫ p in Submission.BoseGases.acube L ×ˢ Submission.BoseGases.acube L,
            A.indicator (fun _ => (1 : ℝ)) p.1
              * (A.indicator (fun _ => (1 : ℝ)) p.2 * w p.1 p.2)) := by
    have h1 : (∫ x in Submission.BoseGases.abox N L,
          (Work.UBBInputs8.boxPInd volA A i (Work.UBBInputs8.boxPInd volA A j Φ) x) ^ 2
            * w (x i) (x j))
        = ∫ x in Submission.BoseGases.abox N L, boxPairG volA A i j Φ x
            * (A.indicator (fun _ => (1 : ℝ)) (x i)
                * (A.indicator (fun _ => (1 : ℝ)) (x j) * w (x i) (x j))) := by
      refine integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
      exact boxPInd_pair_w volA A hij Φ w x
    rw [h1]
    exact hpeel1
  have hG : (∫ x in Submission.BoseGases.abox N L,
        (Work.UBBInputs8.boxPInd volA A i (Work.UBBInputs8.boxPInd volA A j Φ) x) ^ 2)
      = ((∫ x in Submission.BoseGases.abox N L, boxPairG volA A i j Φ x) / L ^ 6)
        * (∫ p in Submission.BoseGases.acube L ×ˢ Submission.BoseGases.acube L,
            A.indicator (fun _ => (1 : ℝ)) p.1 * A.indicator (fun _ => (1 : ℝ)) p.2) := by
    have h1 : (∫ x in Submission.BoseGases.abox N L,
          (Work.UBBInputs8.boxPInd volA A i (Work.UBBInputs8.boxPInd volA A j Φ) x) ^ 2)
        = ∫ x in Submission.BoseGases.abox N L, boxPairG volA A i j Φ x
            * (A.indicator (fun _ => (1 : ℝ)) (x i)
                * A.indicator (fun _ => (1 : ℝ)) (x j)) := by
      refine integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
      exact boxPInd_pair_sq volA A hij Φ x
    rw [h1]
    exact hpeel2
  rw [hLHS, hG]
  rw [mul_comm ((∫ x in Submission.BoseGases.abox N L, boxPairG volA A i j Φ x) / L ^ 6)
      (∫ p in Submission.BoseGases.acube L ×ˢ Submission.BoseGases.acube L,
        A.indicator (fun _ => (1 : ℝ)) p.1 * A.indicator (fun _ => (1 : ℝ)) p.2),
    mul_div_cancel_left₀ ((∫ x in Submission.BoseGases.abox N L, boxPairG volA A i j Φ x) / L ^ 6)
      (ne_of_gt hApos)]

end Work.BoseFixB1B

end
