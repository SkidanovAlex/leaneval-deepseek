import Mathlib
import Submission.Work.ORHughesFree.NaturalExtension.Defs
import Submission.Work.ORHughesFree.NaturalExtension.EltDeg

namespace Work.ORHughesFree.NaturalExtension

open Matrix

/-- Auxiliary rewriting rule: `ofAdd` of a difference of integers is the corresponding quotient in
`Multiplicative ℤ`. -/
theorem ofAdd_sub_toAdd (a : Multiplicative ℤ) (w : ℤ) :
    Multiplicative.ofAdd (w - Multiplicative.toAdd a) = a⁻¹ * Multiplicative.ofAdd w := by
  rw [ofAdd_sub, ofAdd_toAdd, div_eq_mul_inv, mul_comm]

/-- The `w`-th coefficient of a product `f * g`, written as a sum over the degrees occurring
in `f`. -/
theorem coeffElt_mul_support {U : Type} [Ring U] [MulSemiringAction (Multiplicative ℤ) U]
    (f g : SkewL U) (w : ℤ) :
    coeffElt (f * g) w =
      ∑ v ∈ f.support.image Multiplicative.toAdd,
        coeffElt f v * (Multiplicative.ofAdd v • coeffElt g (w - v)) := by
  rw [coeffElt, SkewMonoidAlgebra.coeff_mul_left, Finsupp.sum]
  rw [Finset.sum_image (s := f.support) (g := Multiplicative.toAdd)
      (f := fun v => coeffElt f v * (Multiplicative.ofAdd v • coeffElt g (w - v)))
      (fun x _ y _ h => Multiplicative.toAdd.injective h)]
  apply Finset.sum_congr rfl
  intro a _
  simp only [coeffElt, ofAdd_toAdd, ofAdd_sub_toAdd]

/-- The degrees occurring in `f` lie in the interval cut out by any pair of degree bounds. -/
theorem image_toAdd_support_subset_Icc {U : Type} [AddMonoid U] (f : SkewL U) {L K : ℕ}
    (hL : lowDeg f ≤ L) (hK : upDeg f ≤ K) :
    f.support.image Multiplicative.toAdd ⊆ Finset.Icc (-(L : ℤ)) (K : ℤ) := by
  intro v hv
  rw [Finset.mem_image] at hv
  obtain ⟨a, ha, rfl⟩ := hv
  have ha' := support_subset_Icc_image f hL hK ha
  rw [Finset.mem_image] at ha'
  obtain ⟨u, hu, hua⟩ := ha'
  rw [← hua]
  simpa using hu

/-- Coefficient formula for a product of two elements of `U[t^{±1};τ]`, summed over an interval
containing all degrees occurring in the left factor. -/
theorem coeffElt_mul_bdd {U : Type} [Ring U] [MulSemiringAction (Multiplicative ℤ) U]
    (f g : SkewL U) (w : ℤ) {L K : ℕ} (hL : lowDeg f ≤ L) (hK : upDeg f ≤ K) :
    coeffElt (f * g) w =
      ∑ v ∈ Finset.Icc (-(L : ℤ)) (K : ℤ),
        coeffElt f v * (Multiplicative.ofAdd v • coeffElt g (w - v)) := by
  rw [coeffElt_mul_support]
  refine Finset.sum_subset (image_toAdd_support_subset_Icc f hL hK) ?_
  intro v _ hvnot
  have h1 : Multiplicative.ofAdd v ∉ f.support := by
    intro hmem
    exact hvnot (Finset.mem_image.mpr ⟨v, hmem, rfl⟩)
  simp only [coeffElt]
  rw [Finsupp.notMem_support_iff.mp h1, zero_mul]

/-- Coefficient extraction at a fixed degree is additive. -/
def coeffEltAddHom {U : Type} [AddCommMonoid U] (w : ℤ) : SkewL U →+ U where
  toFun f := coeffElt f w
  map_zero' := by simp [coeffElt]
  map_add' f g := by simp [coeffElt, SkewMonoidAlgebra.coeff_add]

/-- Coefficient extraction commutes with finite sums. -/
theorem coeffElt_sum {U : Type} [AddCommMonoid U] {ι : Type} (s : Finset ι)
    (f : ι → SkewL U) (w : ℤ) :
    coeffElt (∑ i ∈ s, f i) w = ∑ i ∈ s, coeffElt (f i) w :=
  map_sum (coeffEltAddHom w) f s

/-- The lower degree of an entry of a matrix is bounded by the lower degree of the matrix. -/
theorem lowDeg_le_lowerDeg {U : Type} [AddMonoid U] {n m : ℕ}
    (A : Matrix (Fin n) (Fin m) (SkewL U)) (i : Fin n) (j : Fin m) :
    lowDeg (A i j) ≤ lowerDeg A :=
  Finset.le_sup (f := fun p : Fin n × Fin m =>
      (SkewMonoidAlgebra.coeff (A p.1 p.2)).support.sup
        (fun g => Int.toNat (-(Multiplicative.toAdd g)))) (Finset.mem_univ (i, j))

/-- The upper degree of an entry of a matrix is bounded by the upper degree of the matrix. -/
theorem upDeg_le_upperDeg {U : Type} [AddMonoid U] {n m : ℕ}
    (A : Matrix (Fin n) (Fin m) (SkewL U)) (i : Fin n) (j : Fin m) :
    upDeg (A i j) ≤ upperDeg A :=
  Finset.le_sup (f := fun p : Fin n × Fin m =>
      (SkewMonoidAlgebra.coeff (A p.1 p.2)).support.sup
        (fun g => Int.toNat (Multiplicative.toAdd g))) (Finset.mem_univ (i, j))

theorem coeffMat_mul_bdd {U : Type} [Ring U] [MulSemiringAction (Multiplicative ℤ) U]
    {n m k : ℕ} (A : Matrix (Fin n) (Fin m) (SkewL U)) (B : Matrix (Fin m) (Fin k) (SkewL U))
    (w : ℤ) :
    coeffMat (A * B) w =
      ∑ v ∈ Finset.Icc (-(lowerDeg A : ℤ)) (upperDeg A : ℤ),
        coeffMat A v * ((Multiplicative.ofAdd v) • coeffMat B (w - v)) := by
  classical
  ext i j
  rw [coeffMat_apply, Matrix.mul_apply]
  rw [coeffElt_sum]
  rw [Matrix.sum_apply]
  simp only [Matrix.mul_apply, Matrix.smul_apply, coeffMat_apply]
  have hterm : ∀ p : Fin m, coeffElt (A i p * B p j) w =
      ∑ v ∈ Finset.Icc (-(lowerDeg A : ℤ)) (upperDeg A : ℤ),
        coeffElt (A i p) v * ((Multiplicative.ofAdd v) • coeffElt (B p j) (w - v)) :=
    fun p => coeffElt_mul_bdd (A i p) (B p j) w (lowDeg_le_lowerDeg A i p)
      (upDeg_le_upperDeg A i p)
  simp only [hterm]
  rw [Finset.sum_comm]

end Work.ORHughesFree.NaturalExtension
