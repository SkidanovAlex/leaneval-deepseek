import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB1.BoxPairIntGenC2.AuxIntegrable
import Submission.Work.BoseFixB1.BoxPairIntGenC2.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `fibreFactorC` — the box pair-fibre factorisation with the hypotheses it actually needs

`Work.BoseFixB1.BoxPairIntGenC2.fibreFactor` is stated with **no** hypothesis on `Φ`, `A`, `ℓ`
or `volA`:

    boxPairFibreFun volA ℓ A Φ i j y z
      = 1_A(y) · 1_A(z) · boxPairFibreFree volA ℓ A Φ i (sucAboveInv i j hij) y z .

In that generality the statement is **FALSE**.  The peeling identity is pure algebra on the
slot projections `P_k = 1_A(x_k)·M_k`, `Q_k = 1_A(x_k)·(1 − M_k)` (`M_k` the slot mean
`boxIndMean`), *except* at one point: the mean of `Q_i Φ` has to be split,

    M_j(Q_i Φ)(x) = 1_A(x_i) · (∫_A Φ(x_{j←v}) dv − ∫_A M_iΦ(x_{j←v}) dv) ,

and passing from the integral of the difference to the difference of the integrals is
`MeasureTheory.integral_sub`, which **needs** the integrability of the two slot slices.  When a
slice is not integrable, Mathlib's Bochner integral takes the junk value `0`
(`MeasureTheory.integral_undef`), and the two sides of the identity differ.

Concretely (counterexample to the hypothesis-free statement): take `N = 0`, `ℓ` any nonzero
number, `A = Set.univ`, `volA = 1`, `i = 0`, `j = 1`, `y = z = 0`, and

    Φ (w₀, w₁) = 1 + ψ(w₀) · h(w₁),   h = 1_{ball 0 1},   ψ(0) = 0,   C := ∫ψ ≠ 0 .

Then `f(v) = Φ(0,v) = 1` is *not* integrable on `A` (infinite measure), so `∫_A f = 0`, while
`g(v) = M_0Φ(0,v) = C·h(v)` is integrable with `∫_A g = C·vol(ball 0 1) ≠ 0`; hence
`∫_A (f − g) = 0` but `∫_A f − ∫_A g = −C·vol(ball 0 1) ≠ 0`.  Working this through the
peeling gives `LHS = vol(ball)·C·(1 − C)` and `RHS = vol(ball)·C·(1 − C + C·vol(ball))`, which
differ by `−C²vol(ball)² ≠ 0`.  (The same mechanism makes the sibling statement
`boxQIndBoxQInd` false as stated.)

This file proves the corrected statement under the hypotheses under which the identity *is*
true, namely that `A` sits in the box `acube ℓ` and `Φ` is continuous: then the slot slices
`v ↦ Φ(x_{j←v})` and `v ↦ M_iΦ(x_{j←v})` are integrable on `A`, and `integral_sub` applies.
Note that `MeasurableSet A`, `volA = (volume A).toReal` and `0 < volA` are *not* needed — the
remaining algebra uses only `MeasureTheory.integral_const_mul`, which is unconditional.
-/

noncomputable section

open MeasureTheory

namespace Work.BoseFixB1.BoxPairIntGenC2

open _root_.BoseGases Submission.BoseGases

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## The two slot-mean identities -/

/-- The slot mean of a box projection: the indicator `1_A(x_j)` of the *other* slot is a
constant of the `A`-integral and comes out.  This needs no integrability hypothesis. -/
lemma boxIndMean_boxPInd {M : ℕ} {volA : ℝ} {A : Set E3} (i j : Fin M) (hij : i ≠ j)
    (Φ : X M → ℝ) (x : X M) :
    Work.BoseFixB1.boxIndMean volA A i (Work.UBBInputs8.boxPInd volA A j Φ) x
      = A.indicator (fun _ => (1 : ℝ)) (x j)
        * Work.BoseFixB1.boxIndMean volA A i (Work.BoseFixB1.boxIndMean volA A j Φ) x := by
  have hpt : ∀ w : E3, Work.UBBInputs8.boxPInd volA A j Φ (Function.update x i w)
      = A.indicator (fun _ => (1 : ℝ)) (x j)
        * Work.BoseFixB1.boxIndMean volA A j Φ (Function.update x i w) := by
    intro w
    rw [Work.BoseFixB1.boxPInd_eq_mean_mul_indicator, Function.update_of_ne hij.symm]
    ring
  rw [Work.BoseFixB1.boxIndMean, Work.BoseFixB1.boxIndMean]
  simp only [hpt]
  rw [MeasureTheory.integral_const_mul]
  ring

/-- The slot mean of a box `Q`-projection.  Unlike `boxIndMean_boxPInd`, this identity needs
the two slot slices to be integrable: `Q_i = 1_A(x_i)·(Φ − M_iΦ)` and the mean of the
difference must be split into the difference of the means (`MeasureTheory.integral_sub`).
This is the single place where the hypothesis-free statement fails. -/
lemma boxIndMean_boxQInd {M : ℕ} {volA : ℝ} {A : Set E3} (i j : Fin M) (hij : i ≠ j)
    (Φ : X M → ℝ) (x : X M)
    (h1 : IntegrableOn (fun w : E3 => Φ (Function.update x j w)) A volume)
    (h2 : IntegrableOn (fun w : E3 =>
      Work.BoseFixB1.boxIndMean volA A i Φ (Function.update x j w)) A volume) :
    Work.BoseFixB1.boxIndMean volA A j (Work.UBBInputs8.boxQInd volA A i Φ) x
      = A.indicator (fun _ => (1 : ℝ)) (x i)
        * (Work.BoseFixB1.boxIndMean volA A j Φ x
            - Work.BoseFixB1.boxIndMean volA A j (Work.BoseFixB1.boxIndMean volA A i Φ) x) := by
  have hpt : ∀ w : E3, Work.UBBInputs8.boxQInd volA A i Φ (Function.update x j w)
      = A.indicator (fun _ => (1 : ℝ)) (x i)
        * (Φ (Function.update x j w)
            - Work.BoseFixB1.boxIndMean volA A i Φ (Function.update x j w)) := by
    intro w
    rw [Work.BoseFixB1.boxQInd_eq_indicator_mul_sub, Function.update_of_ne hij]
  rw [Work.BoseFixB1.boxIndMean, Work.BoseFixB1.boxIndMean, Work.BoseFixB1.boxIndMean]
  simp only [hpt]
  rw [MeasureTheory.integral_const_mul]
  rw [MeasureTheory.integral_sub h1 h2]
  ring

/-! ## The factorisation -/

/-- **The box pair fibre factors through the two box indicators.**  For `A ⊆ acube ℓ` and a
continuous `Φ` (so that the slot slices are integrable on `A`), the peeled box pair fibre is
the product of the two distinguished box indicators and the indicator-free fibre.  This is the
corrected form of `Work.BoseFixB1.BoxPairIntGenC2.fibreFactor`, which omits the hypotheses and
is therefore false. -/
theorem fibreFactorC {N : ℕ} {ℓ volA : ℝ} {A : Set E3}
    (hℓ : 0 < ℓ) (hAc : A ⊆ Submission.BoseGases.acube ℓ)
    (i : Fin (N + 2)) (j : Fin (N + 2)) (hij : i ≠ j)
    {Φ : X (N + 2) → ℝ} (hΦc : Continuous Φ) (y z : E3) :
    Work.BoseFixB1.boxPairFibreFun volA ℓ A Φ i j y z
      = A.indicator (fun _ => (1 : ℝ)) y * A.indicator (fun _ => (1 : ℝ)) z
        * boxPairFibreFree volA ℓ A Φ i (Submission.BoseGases.sucAboveInv i j hij) y z := by
  classical
  rw [Work.BoseFixB1.boxPairFibreFun, dif_pos hij]
  rw [boxPairFibreFree]
  rw [Submission.BoseGases.succAbove_sucAboveInv i j hij]
  set j' := Submission.BoseGases.sucAboveInv i j hij with hj'def
  have hj : i.succAbove j' = j := by
    rw [hj'def]
    exact Submission.BoseGases.succAbove_sucAboveInv i j hij
  by_cases hy : y ∈ A
  · by_cases hz : z ∈ A
    · -- both distinguished slots lie in `A`: the two integrands agree pointwise
      rw [← MeasureTheory.integral_const_mul]
      refine setIntegral_congr_fun (Submission.BoseGases.abox_measurable N ℓ) (fun r2 _ => ?_)
      set x := Submission.BoseGases.ins2 i j' y z r2 with hxdef
      have hxi : x i = y := Submission.BoseGases.ins2_apply_i i j' y z r2
      have hxj : x j = z := by
        rw [hxdef, ← hj]
        exact Submission.BoseGases.ins2_apply_succ i j' y z r2
      -- integrability of the two slot slices over `A`
      have hcont1 : Continuous (fun v : E3 => Φ (Function.update x j v)) := by fun_prop
      have hint1 : IntegrableOn (fun v : E3 => Φ (Function.update x j v)) A volume :=
        (hcont1.continuousOn.integrableOn_compact
          (Submission.BoseGases.acube_compact hℓ)).mono_set hAc
      have hint2 : IntegrableOn (fun v : E3 =>
          Work.BoseFixB1.boxIndMean volA A i Φ (Function.update x j v)) A volume :=
        (Work.BoseFixB1.BoxPairIntGenC2.integrable_parametricIntegral hℓ hAc
          (f := fun u v : E3 => Φ (Function.update (Function.update x j v) i u))
          (by fun_prop)).const_mul (1 / volA)
      -- the pointwise algebra
      have hP : Work.UBBInputs8.boxPInd volA A i (Work.UBBInputs8.boxPInd volA A j Φ) x
          = A.indicator (fun _ => (1 : ℝ)) (x i) * A.indicator (fun _ => (1 : ℝ)) (x j)
            * Work.BoseFixB1.boxIndMean volA A i (Work.BoseFixB1.boxIndMean volA A j Φ) x := by
        rw [Work.BoseFixB1.boxPInd_eq_mean_mul_indicator, boxIndMean_boxPInd i j hij Φ x]
        ring
      have hQ : Work.UBBInputs8.boxQInd volA A j (Work.UBBInputs8.boxQInd volA A i Φ) x
          = A.indicator (fun _ => (1 : ℝ)) (x j)
            * (Work.UBBInputs8.boxQInd volA A i Φ x
                - Work.BoseFixB1.boxIndMean volA A j
                    (Work.UBBInputs8.boxQInd volA A i Φ) x) :=
        Work.BoseFixB1.boxQInd_eq_indicator_mul_sub volA A j
          (Work.UBBInputs8.boxQInd volA A i Φ) x
      have hQ0 : Work.UBBInputs8.boxQInd volA A i Φ x
          = A.indicator (fun _ => (1 : ℝ)) (x i)
            * (Φ x - Work.BoseFixB1.boxIndMean volA A i Φ x) :=
        Work.BoseFixB1.boxQInd_eq_indicator_mul_sub volA A i Φ x
      have hMjQ : Work.BoseFixB1.boxIndMean volA A j (Work.UBBInputs8.boxQInd volA A i Φ) x
          = A.indicator (fun _ => (1 : ℝ)) (x i)
            * (Work.BoseFixB1.boxIndMean volA A j Φ x
                - Work.BoseFixB1.boxIndMean volA A j
                    (Work.BoseFixB1.boxIndMean volA A i Φ) x) :=
        boxIndMean_boxQInd i j hij Φ x hint1 hint2
      rw [hP, hQ, hQ0, hMjQ, hxi, hxj]
      simp only [Set.indicator_of_mem hy, Set.indicator_of_mem hz]
      ring
    · -- `z ∉ A`: the `Q`-projection vanishes
      have hzero : ∀ r2 : X N,
          Work.UBBInputs8.boxPInd volA A i (Work.UBBInputs8.boxPInd volA A j Φ)
              (Submission.BoseGases.ins2 i j' y z r2)
            * Work.UBBInputs8.boxQInd volA A j (Work.UBBInputs8.boxQInd volA A i Φ)
              (Submission.BoseGases.ins2 i j' y z r2) = 0 := by
        intro r2
        have hxj : (Submission.BoseGases.ins2 i j' y z r2) j = z := by
          rw [← hj]
          exact Submission.BoseGases.ins2_apply_succ i j' y z r2
        simp only [Work.BoseFixB1.boxQInd_eq_indicator_mul_sub, hxj,
          Set.indicator_of_notMem hz, zero_mul, mul_zero]
      simp only [hzero]
      simp [Set.indicator_of_notMem hz]
  · -- `y ∉ A`: the `P`-projection vanishes
    have hzero : ∀ r2 : X N,
        Work.UBBInputs8.boxPInd volA A i (Work.UBBInputs8.boxPInd volA A j Φ)
            (Submission.BoseGases.ins2 i j' y z r2)
          * Work.UBBInputs8.boxQInd volA A j (Work.UBBInputs8.boxQInd volA A i Φ)
            (Submission.BoseGases.ins2 i j' y z r2) = 0 := by
      intro r2
      have hxi : (Submission.BoseGases.ins2 i j' y z r2) i = y :=
        Submission.BoseGases.ins2_apply_i i j' y z r2
      simp only [Work.BoseFixB1.boxPInd_eq_mean_mul_indicator, hxi,
        Set.indicator_of_notMem hy, mul_zero, zero_mul]
    simp only [hzero]
    simp [Set.indicator_of_notMem hy]

end Work.BoseFixB1.BoxPairIntGenC2
