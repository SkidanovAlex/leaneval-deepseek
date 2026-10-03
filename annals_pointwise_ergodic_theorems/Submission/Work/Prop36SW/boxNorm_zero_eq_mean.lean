import Mathlib
import Submission.Work.Peluse.Basic

/-!
# The level-`0` box norm is the mean of `f`

The Gowers box norm of Peluse's Definition 2.1 at level `0` has an empty direction family
`Q : Fin 0 → Finset ℤ` and one cube corner only (`Fin 0 → Bool` is a singleton), so the cube
average collapses to the plain mean of `f` over the window `S`:

`‖f‖_{□^0_Q(S)} = ‖ |S|⁻¹ ∑_x f x ‖`.

Both sides are read off from the definition: the products over `Fin 0` and over the singleton
type `Fin 0 → Bool` are `1`, the sums over the function types `(i : Fin 0) → {x // x ∈ Q i}` are
singletons, `cornerShift` vanishes (its sum is empty) and `weight` vanishes (it counts the
elements of an empty index set), so `star^[0]` is the identity, and the two remaining `tsum`s
agree.  The normalisation exponent `1 / 2 ^ 0 = 1` of `boxNorm` is trivial, so no root has to be
extracted and the finiteness hypothesis `hf` is not needed.
-/

set_option autoImplicit false

open scoped BigOperators

namespace Work.Prop36SW

open Work.Peluse

/-- **The cube average at level `0`.**  With no directions, `prodCubeSum 0` is the mean of the
single function `g default`. -/
private lemma prodCubeSum_zero (Q : Fin 0 → Finset ℤ) (S : Finset ℤ)
    (g : (Fin 0 → Bool) → ℤ → ℂ) :
    prodCubeSum 0 Q S g = ((S.card : ℂ))⁻¹ * ∑' x : ℤ, g default x := by
  rw [prodCubeSum_eq]
  simp only [Finset.univ_eq_empty, Finset.prod_empty, mul_one]
  congr 1
  rw [Fintype.sum_subsingleton _ (default : (i : Fin 0) → {x : ℤ // x ∈ Q i})]
  rw [Fintype.sum_subsingleton _ (default : (i : Fin 0) → {x : ℤ // x ∈ Q i})]
  apply tsum_congr
  intro x
  rw [Fintype.prod_subsingleton _ (default : Fin 0 → Bool)]
  simp [weight, cornerShift]

/-- **The box sum at level `0`.**  `boxSumPow 0 Q S f = |S|⁻¹ ∑_x f x`. -/
private lemma boxSumPow_zero (Q : Fin 0 → Finset ℤ) (S : Finset ℤ) (f : ℤ → ℂ) :
    boxSumPow 0 Q S f = ((S.card : ℂ))⁻¹ * ∑' x : ℤ, f x := by
  rw [boxSumPow]
  exact prodCubeSum_zero Q S (fun _ => f)

theorem boxNorm_zero_eq_mean (S : Finset ℤ) (Q : Fin 0 → Finset ℤ) (f : ℤ → ℂ)
    (hf : Work.Peluse.FinSuppZ f) :
    Work.Peluse.boxNorm 0 Q S f = ‖(((S.card : ℂ))⁻¹) * ∑' x : ℤ, f x‖ := by
  rw [show Work.Peluse.boxNorm 0 Q S f = Work.Peluse.boxNormPow 0 Q S f by
    simp [Work.Peluse.boxNorm]]
  rw [Work.Peluse.boxNormPow, boxSumPow_zero]

end Work.Prop36SW
