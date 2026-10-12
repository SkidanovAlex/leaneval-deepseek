import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB1.BoxD1Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1.boxCoreDefs` — vocabulary for the box core identity

The target `Work.BoseFixB1.boxCoreIdentity` (`Submission/Work/BoseFixB1/boxCoreIdentity.lean`)
states that the double box integral of the mean-free windowed modes
`boxWinModeC volA A χ (-p) y * boxWinModeC volA A χ p z` against the doubly box-projected state
`Q_{A,i.succAbove j'}Q_{A,i}Φ` may be replaced by the *unprojected* window product
`χ y χ z e^{i⟪p,y-z⟫}`.

The reason is that `Q_{A,k}` is **mean-free in its own slot**: for fixed `y` the function
`z ↦ Q_{A,k}Ψ(x|k↦z)` has vanishing box integral, so the two correction constants
`boxCoreC volA A (boxCoreU χ p)` and `boxCoreC volA A (boxCoreV χ p)` that the mean-free
projection subtracts integrate to zero against a function that is mean-free in the other slot.

This module fixes the vocabulary used by that proof:

* `boxCoreQ` — the doubly projected state of the identity,
* `boxCoreU` / `boxCoreV` — the two unprojected mode factors,
* `boxCoreC` — the box mean `volA⁻¹∫_A g`,

together with the algebraic facts about them: the pointwise form of `boxWinModeC` at momentum
`±p` on `A`, the product identity `boxCoreU χ p y * boxCoreV χ p z = χ y χ z e^{i⟪p,y-z⟫}`,
and the indicator form of `boxCoreQ` on `A × A`.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped Topology Real BigOperators ENNReal

namespace Work.BoseFixB1

open Submission.BoseGases

set_option maxHeartbeats 1000000

/-- The doubly box-projected state of the core identity:
`boxQInd volA A (i.succAbove j') (boxQInd volA A i Φ)` evaluated at the configuration with
`y` inserted in slot `i` and `z` in slot `i.succAbove j'` (the rest being `x`). -/
noncomputable def boxCoreQ {N : ℕ} (volA : ℝ) (A : Set (EuclideanSpace ℝ (Fin 3)))
    (Φ : X (N + 2) → ℝ) (i : Fin (N + 2)) (j' : Fin (N + 1)) (x : X N)
    (y z : EuclideanSpace ℝ (Fin 3)) : ℝ :=
  (Work.UBBInputs8.boxQInd volA A (i.succAbove j') (Work.UBBInputs8.boxQInd volA A i Φ))
    (ins2 i j' y z x)

/-- The unprojected `-p` mode factor `χ y · e^{i⟪p,y⟫}`. -/
noncomputable def boxCoreU (χ : EuclideanSpace ℝ (Fin 3) → ℝ) (p y : EuclideanSpace ℝ (Fin 3)) :
    ℂ :=
  (χ y : ℂ) * Complex.exp (Complex.I * ((inner ℝ p y : ℝ) : ℂ))

/-- The unprojected `+p` mode factor `χ z · e^{-i⟪p,z⟫}`. -/
noncomputable def boxCoreV (χ : EuclideanSpace ℝ (Fin 3) → ℝ) (p z : EuclideanSpace ℝ (Fin 3)) :
    ℂ :=
  (χ z : ℂ) * Complex.exp (-(Complex.I * ((inner ℝ p z : ℝ) : ℂ)))

/-- The box mean `volA⁻¹ ∫_A g` of a complex-valued function. -/
noncomputable def boxCoreC (volA : ℝ) (A : Set (EuclideanSpace ℝ (Fin 3)))
    (g : EuclideanSpace ℝ (Fin 3) → ℂ) : ℂ :=
  ((volA⁻¹ : ℝ) : ℂ) * ∫ w in A, g w

/-- The complexified doubly projected state of the identity. -/
noncomputable def boxCoreKc {N : ℕ} (volA : ℝ) (A : Set (EuclideanSpace ℝ (Fin 3)))
    (Φ : X (N + 2) → ℝ) (i : Fin (N + 2)) (j' : Fin (N + 1)) (x : X N)
    (y z : EuclideanSpace ℝ (Fin 3)) : ℂ :=
  ((boxCoreQ volA A Φ i j' x y z : ℝ) : ℂ)

/-- `‖boxCoreV χ p z‖ = ‖χ z‖`. -/
lemma boxCore_norm_boxCoreV (χ : EuclideanSpace ℝ (Fin 3) → ℝ)
    (p z : EuclideanSpace ℝ (Fin 3)) : ‖boxCoreV χ p z‖ = ‖χ z‖ := by
  have hre : (-(Complex.I * ((inner ℝ p z : ℝ) : ℂ))).re = 0 := by
    simp [Complex.mul_re, Complex.I_re, Complex.I_im]
  rw [boxCoreV, norm_mul, Complex.norm_exp, hre, Real.exp_zero, mul_one,
    Real.norm_eq_abs]
  exact RCLike.norm_ofReal (χ z)

/-- `‖boxCoreU χ p y‖ = ‖χ y‖`. -/
lemma boxCore_norm_boxCoreU (χ : EuclideanSpace ℝ (Fin 3) → ℝ)
    (p y : EuclideanSpace ℝ (Fin 3)) : ‖boxCoreU χ p y‖ = ‖χ y‖ := by
  have hre : (Complex.I * ((inner ℝ p y : ℝ) : ℂ)).re = 0 := by
    simp [Complex.mul_re, Complex.I_re, Complex.I_im]
  rw [boxCoreU, norm_mul, Complex.norm_exp, hre, Real.exp_zero, mul_one,
    Real.norm_eq_abs]
  exact RCLike.norm_ofReal (χ y)

/-- `-(I * ⟪-p,w⟫) = I * ⟪p,w⟫`. -/
lemma boxCore_neg_exp (p w : EuclideanSpace ℝ (Fin 3)) :
    -(Complex.I * ((inner ℝ (-p) w : ℝ) : ℂ)) = Complex.I * ((inner ℝ p w : ℝ) : ℂ) := by
  rw [inner_neg_left]
  push_cast
  ring

/-- On `A`, `boxWinModeC` at momentum `-p` is the unprojected mode minus its box mean. -/
lemma boxWinModeC_neg_eq {volA : ℝ} {A : Set (EuclideanSpace ℝ (Fin 3))}
    {χ : EuclideanSpace ℝ (Fin 3) → ℝ} (p : EuclideanSpace ℝ (Fin 3))
    {y : EuclideanSpace ℝ (Fin 3)} (hy : y ∈ A) :
    boxWinModeC volA A χ (-p) y = boxCoreU χ p y - boxCoreC volA A (boxCoreU χ p) := by
  have hInt : (∫ w in A, (χ w : ℂ) * Complex.exp (-(Complex.I * ((inner ℝ (-p) w : ℝ) : ℂ))))
      = ∫ w in A, boxCoreU χ p w := by
    apply integral_congr_ae
    filter_upwards with w
    rw [boxCore_neg_exp, boxCoreU]
  rw [boxWinModeC, boxCoreU, boxCoreC, hInt, Set.indicator_of_mem hy, one_mul]
  rw [boxCore_neg_exp]

/-- On `A`, `boxWinModeC` at momentum `p` is the unprojected mode minus its box mean. -/
lemma boxWinModeC_pos_eq {volA : ℝ} {A : Set (EuclideanSpace ℝ (Fin 3))}
    {χ : EuclideanSpace ℝ (Fin 3) → ℝ} (p : EuclideanSpace ℝ (Fin 3))
    {z : EuclideanSpace ℝ (Fin 3)} (hz : z ∈ A) :
    boxWinModeC volA A χ p z = boxCoreV χ p z - boxCoreC volA A (boxCoreV χ p) := by
  have hInt : (∫ w in A, (χ w : ℂ) * Complex.exp (-(Complex.I * ((inner ℝ p w : ℝ) : ℂ))))
      = ∫ w in A, boxCoreV χ p w := by
    apply integral_congr_ae
    filter_upwards with w
    rw [boxCoreV]
  rw [boxWinModeC, boxCoreV, boxCoreC, hInt, Set.indicator_of_mem hz, one_mul]

/-- The product of the two unprojected modes is the unprojected window product. -/
lemma boxCoreU_mul_boxCoreV (χ : EuclideanSpace ℝ (Fin 3) → ℝ)
    (p y z : EuclideanSpace ℝ (Fin 3)) :
    boxCoreU χ p y * boxCoreV χ p z
      = (χ y : ℂ) * (χ z : ℂ)
        * Complex.exp (Complex.I * ((inner ℝ p (y - z) : ℝ) : ℂ)) := by
  have hexp : Complex.exp (Complex.I * ((inner ℝ p y : ℝ) : ℂ))
        * Complex.exp (-(Complex.I * ((inner ℝ p z : ℝ) : ℂ)))
      = Complex.exp (Complex.I * ((inner ℝ p (y - z) : ℝ) : ℂ)) := by
    rw [← Complex.exp_add, inner_sub_right]
    push_cast
    ring
  calc boxCoreU χ p y * boxCoreV χ p z
      = ((χ y : ℂ) * Complex.exp (Complex.I * ((inner ℝ p y : ℝ) : ℂ)))
          * ((χ z : ℂ) * Complex.exp (-(Complex.I * ((inner ℝ p z : ℝ) : ℂ)))) := by
        rw [boxCoreU, boxCoreV]
    _ = (χ y : ℂ) * (χ z : ℂ)
          * (Complex.exp (Complex.I * ((inner ℝ p y : ℝ) : ℂ))
              * Complex.exp (-(Complex.I * ((inner ℝ p z : ℝ) : ℂ)))) := by ring
    _ = (χ y : ℂ) * (χ z : ℂ)
          * Complex.exp (Complex.I * ((inner ℝ p (y - z) : ℝ) : ℂ)) := by rw [hexp]

/-- The indicator form of the doubly projected state on `A × A`. -/
lemma boxCoreQ_indicator {N : ℕ} {volA : ℝ} {A : Set (EuclideanSpace ℝ (Fin 3))}
    {Φ : X (N + 2) → ℝ} (i : Fin (N + 2)) (j' : Fin (N + 1)) (x : X N)
    {y z : EuclideanSpace ℝ (Fin 3)} (hy : y ∈ A) (hz : z ∈ A) :
    boxCoreQ volA A Φ i j' x y z
      = Φ (ins2 i j' y z x)
        - (1 / volA) * (∫ w in A, Φ (ins2 i j' w z x))
        - (1 / volA) * (∫ w in A,
            (Φ (ins2 i j' y w x) - (1 / volA) * (∫ v in A, Φ (ins2 i j' v w x)))) := by
  have hy' : A.indicator (fun _ => (1 : ℝ)) y = 1 := Set.indicator_of_mem hy _
  have hz' : A.indicator (fun _ => (1 : ℝ)) z = 1 := Set.indicator_of_mem hz _
  have h1 : ∀ w : EuclideanSpace ℝ (Fin 3),
      Function.update (ins2 i j' y z x) (i.succAbove j') w = ins2 i j' y w x :=
    fun w => ins2_update_succ i j' y z w x
  have h2 : ∀ w : EuclideanSpace ℝ (Fin 3),
      Function.update (ins2 i j' y z x) i w = ins2 i j' w z x :=
    fun w => ins2_update_i i j' y w z x
  have h3 : ∀ v w : EuclideanSpace ℝ (Fin 3),
      Function.update (ins2 i j' y w x) i v = ins2 i j' v w x :=
    fun v w => ins2_update_i i j' y v w x
  simp only [boxCoreQ, Work.UBBInputs8.boxQInd, Work.UBBInputs8.boxPInd, h1, h2, h3,
    ins2_apply_i, ins2_apply_succ, hy', hz', one_mul, mul_one]

/-- `boxCoreQ` vanishes when `z ∉ A`. -/
lemma boxCoreQ_eq_zero_of_notMem_right {N : ℕ} {volA : ℝ}
    {A : Set (EuclideanSpace ℝ (Fin 3))} {Φ : X (N + 2) → ℝ} (i : Fin (N + 2))
    (j' : Fin (N + 1)) (x : X N) {y z : EuclideanSpace ℝ (Fin 3)} (hz : z ∉ A) :
    boxCoreQ volA A Φ i j' x y z = 0 := by
  have h4 : (ins2 i j' y z x) (i.succAbove j') = z := ins2_apply_succ i j' y z x
  simp only [boxCoreQ, Work.UBBInputs8.boxQInd, Work.UBBInputs8.boxPInd, h4,
    Set.indicator_of_notMem hz, zero_mul, mul_zero, sub_zero]

/-- `boxCoreQ` vanishes when `y ∉ A`. -/
lemma boxCoreQ_eq_zero_of_notMem_left {N : ℕ} {volA : ℝ}
    {A : Set (EuclideanSpace ℝ (Fin 3))} {Φ : X (N + 2) → ℝ} (i : Fin (N + 2))
    (j' : Fin (N + 1)) (x : X N) {y z : EuclideanSpace ℝ (Fin 3)} (hy : y ∉ A) :
    boxCoreQ volA A Φ i j' x y z = 0 := by
  have h1 : ∀ w : EuclideanSpace ℝ (Fin 3),
      Function.update (ins2 i j' y z x) (i.succAbove j') w = ins2 i j' y w x :=
    fun w => ins2_update_succ i j' y z w x
  have hΨ : ∀ t : EuclideanSpace ℝ (Fin 3),
      (Work.UBBInputs8.boxQInd volA A i Φ) (ins2 i j' y t x) = 0 := by
    intro t
    have ht : (ins2 i j' y t x) i = y := ins2_apply_i i j' y t x
    simp only [Work.UBBInputs8.boxQInd, Work.UBBInputs8.boxPInd, ht,
      Set.indicator_of_notMem hy, zero_mul, mul_zero, sub_zero]
  have hInt0 : (∫ w in A, (Work.UBBInputs8.boxQInd volA A i Φ)
        (Function.update (ins2 i j' y z x) (i.succAbove j') w)) = 0 := by
    rw [show (fun w => (Work.UBBInputs8.boxQInd volA A i Φ)
        (Function.update (ins2 i j' y z x) (i.succAbove j') w)) = fun _ => (0 : ℝ) from
      funext fun w => by rw [h1 w]; exact hΨ w]
    simp
  have hY : boxCoreQ volA A Φ i j' x y z
      = A.indicator (fun _ => (1 : ℝ)) z *
        ((Work.UBBInputs8.boxQInd volA A i Φ) (ins2 i j' y z x)
          - (1 / volA) * (∫ w in A, (Work.UBBInputs8.boxQInd volA A i Φ)
              (Function.update (ins2 i j' y z x) (i.succAbove j') w))) := by
    simp only [boxCoreQ, Work.UBBInputs8.boxQInd, Work.UBBInputs8.boxPInd, ins2_apply_succ]
    ring
  rw [hY, hInt0, hΨ z, mul_zero, sub_zero]
  simp

end Work.BoseFixB1
