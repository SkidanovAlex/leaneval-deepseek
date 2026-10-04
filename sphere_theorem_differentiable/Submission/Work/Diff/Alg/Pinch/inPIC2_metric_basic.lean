import Mathlib
import Submission.Work.Diff.Alg.Pinch.Defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Basic metric consequences of nonnegative complex sectional curvature (`InPIC2`)

For an arbitrary `4`-index array `R : Curv4 n`, the condition `InPIC2 R` says that the isotropic
curvature form `EFun R x y z w` is nonnegative for all real vectors `x y z w` (real form of
`R(ζ,η,ζ̄,η̄) ≥ 0` for `ζ = x+iy`, `η = z+iw`).  Specialising to `y = w = 0` already yields
`R4 R x z x z ≥ 0`, from which the three classical consequences follow:

* nonnegative sectional curvature (`secK R u v ≥ 0`),
* nonnegative Ricci (the quadratic form `v ↦ ∑ᵢⱼ (∑ₖ R k i k j) vᵢ vⱼ ≥ 0`), and
* nonnegative scalar curvature (`scalAlg R ≥ 0`).

No algebraic-curvature hypothesis is needed: the choice `y = w = 0` kills every term of `EFun`
except `R4 R x z x z`, and the Ricci / scalar contractions are obtained by summing these over an
orthonormal basis (the standard basis of `ℝⁿ`).
-/

namespace Work.Diff.Alg.Pinch

open Finset Submission.Diff.Alg

variable {n : ℕ}

/-- `InPIC2` implies `R4 R x z x z ≥ 0` for all vectors `x, z` (take `y = w = 0`). -/
lemma inPIC2_R4_nonneg (R : Curv4 n) (hR : InPIC2 R) (x z : Fin n → ℝ) :
    0 ≤ R4 R x z x z := by
  have h := hR x 0 z 0
  simp only [R4, Pi.zero_apply, mul_zero, zero_mul] at h
  simpa [R4] using h

/-- `R4` on four standard basis vectors is the corresponding component. -/
lemma R4_basis (R : Curv4 n) (i j k l : Fin n) :
    R4 R (Pi.single i 1) (Pi.single j 1) (Pi.single k 1) (Pi.single l 1) = R i j k l := by
  simp only [R4]
  rw [Finset.sum_eq_single i]
  · rw [Finset.sum_eq_single j]
    · rw [Finset.sum_eq_single k]
      · rw [Finset.sum_eq_single l]
        · simp
        · intro d _ hd; simp [Pi.single_eq_of_ne hd]
        · intro h; exact absurd (Finset.mem_univ l) h
      · intro c _ hc
        apply Finset.sum_eq_zero; intro d _
        simp [Pi.single_eq_of_ne hc]
      · intro h; exact absurd (Finset.mem_univ k) h
    · intro b _ hb
      apply Finset.sum_eq_zero; intro c _
      apply Finset.sum_eq_zero; intro d _
      simp [Pi.single_eq_of_ne hb]
    · intro h; exact absurd (Finset.mem_univ j) h
  · intro a _ ha
    apply Finset.sum_eq_zero; intro b _
    apply Finset.sum_eq_zero; intro c _
    apply Finset.sum_eq_zero; intro d _
    simp [Pi.single_eq_of_ne ha]
  · intro h; exact absurd (Finset.mem_univ i) h

/-- `R4 R eₖ v eₖ v = ∑ᵢⱼ R k i k j vᵢ vⱼ` for the `k`-th standard basis vector `eₖ`. -/
lemma R4_single (R : Curv4 n) (v : Fin n → ℝ) (k : Fin n) :
    R4 R (Pi.single k 1) v (Pi.single k 1) v = ∑ i, ∑ j, R k i k j * v i * v j := by
  simp only [R4]
  rw [Finset.sum_eq_single k]
  · apply Finset.sum_congr rfl; intro b _
    rw [Finset.sum_eq_single k]
    · simp only [Pi.single_eq_same, mul_one]
    · intro c _ hc
      apply Finset.sum_eq_zero; intro d _
      simp [Pi.single_eq_of_ne hc]
    · intro h; exact absurd (Finset.mem_univ k) h
  · intro a _ ha
    apply Finset.sum_eq_zero; intro b _
    apply Finset.sum_eq_zero; intro c _
    apply Finset.sum_eq_zero; intro d _
    simp [Pi.single_eq_of_ne ha]
  · intro h; exact absurd (Finset.mem_univ k) h

/-- Rewriting the Ricci quadratic form as a sum of `InPIC2`-controlled terms. -/
lemma ricForm_eq (R : Curv4 n) (v : Fin n → ℝ) :
    (∑ i, ∑ j, (∑ k, R k i k j) * v i * v j)
      = ∑ k, R4 R (Pi.single k 1) v (Pi.single k 1) v := by
  have h1 : (∑ i, ∑ j, (∑ k, R k i k j) * v i * v j)
      = ∑ i, ∑ j, ∑ k, R k i k j * v i * v j := by
    apply Finset.sum_congr rfl; intro i _
    apply Finset.sum_congr rfl; intro j _
    rw [Finset.sum_mul, Finset.sum_mul]
  have h2 : (∑ i, ∑ j, ∑ k, R k i k j * v i * v j)
      = ∑ k, ∑ i, ∑ j, R k i k j * v i * v j := by
    trans ∑ i, ∑ k, ∑ j, R k i k j * v i * v j
    · apply Finset.sum_congr rfl; intro i _
      rw [Finset.sum_comm]
    · rw [Finset.sum_comm]
  rw [h1, h2]
  apply Finset.sum_congr rfl; intro k _
  exact (R4_single R v k).symm

/-- The scalar curvature as a sum of `InPIC2`-controlled terms. -/
lemma scalAlg_eq (R : Curv4 n) :
    scalAlg R
      = ∑ i, ∑ j, R4 R (Pi.single i 1) (Pi.single j 1) (Pi.single i 1) (Pi.single j 1) := by
  simp only [scalAlg]
  apply Finset.sum_congr rfl; intro i _
  apply Finset.sum_congr rfl; intro j _
  exact (R4_basis R i j i j).symm

theorem inPIC2_metric_basic (n : ℕ) :
    (∀ R : Submission.Diff.Alg.Curv4 n, Submission.Diff.Alg.InPIC2 R →
      ∀ u v : Fin n → ℝ, 0 ≤ Submission.Diff.Alg.secK R u v) ∧
    (∀ R : Submission.Diff.Alg.Curv4 n, Submission.Diff.Alg.InPIC2 R →
      ∀ v : Fin n → ℝ, 0 ≤ ∑ i, ∑ j, (∑ k, R k i k j) * v i * v j) ∧
    (∀ R : Submission.Diff.Alg.Curv4 n, Submission.Diff.Alg.InPIC2 R →
      0 ≤ Submission.Diff.Alg.scalAlg R) := by
  refine ⟨?_, ?_, ?_⟩
  · intro R hR u v
    simpa [secK] using inPIC2_R4_nonneg R hR u v
  · intro R hR v
    rw [ricForm_eq R v]
    apply Finset.sum_nonneg; intro k _
    exact inPIC2_R4_nonneg R hR _ _
  · intro R hR
    rw [scalAlg_eq R]
    apply Finset.sum_nonneg; intro i _
    apply Finset.sum_nonneg; intro j _
    exact inPIC2_R4_nonneg R hR _ _

end Work.Diff.Alg.Pinch
