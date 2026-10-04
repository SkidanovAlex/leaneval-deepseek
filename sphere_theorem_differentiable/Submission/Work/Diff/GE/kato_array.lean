import Mathlib
import Submission.Work.Diff.GE.bianchi_kato_defs
import Submission.Work.Diff.GE.curv4_trace

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Kato's inequality for the arrays `R` and `∇Rm` (`Work.Diff.GE.kato_array`)

The lemma is pure finite-dimensional linear algebra on curvature arrays
`Curv4 n = Fin n → Fin n → Fin n → Fin n → ℝ`.

* `kato_cs` is Cauchy–Schwarz for the Frobenius pairing of two arrays,
  `(∑ Aᵢⱼₖₗ Bᵢⱼₖₗ)² ≤ (∑ Aᵢⱼₖₗ²)(∑ Bᵢⱼₖₗ²)`.  The four nested finite sums are flattened to a
  single sum over the product type `((Fin n × Fin n) × Fin n) × Fin n`, where
  `Finset.sum_mul_sq_le_sq_mul_sq` applies.  The flattening is `kato_sum4_prod`.
* `kato_tf_norm` identifies the trace-free norm `frobSqTF A = |A|² − 2 (scalAlg A)²/(n(n−1))` with
  the sum of squares of the trace-free part `A − (scalAlg A/(n(n−1))) • Iso n`; it uses the trace
  identities of `Work.Diff.GE.curv4_trace` and only the antisymmetry in the FIRST pair of `A`
  (which is what a covariant derivative `∇Rm` provides, without the first Bianchi identity).
* `kato_sum_tf` moves the `∑_m` past the definition of `frobSqTF`.
* `kato_array_aux` assembles these into Kato's inequality `|∇|R°|²|² ≤ 4 |R°|² |∇R°|²` on the arrays.
* `kato_array` is the requested statement, obtained from the auxiliary form by rewriting the bracket
  on the right-hand side into `∑_m frobSqTF (T m)`.
-/

namespace Work.Diff.GE

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric

set_option maxHeartbeats 800000
set_option linter.unusedVariables false

variable {n : ℕ}

/-- The trace-free part of a curvature array: `A° = A − (scalAlg A/(n(n−1))) • Iso n`. -/
noncomputable def katoTF (A : Curv4 n) : Curv4 n := fun i j k l =>
  A i j k l - (scalAlg A / ((n : ℝ) * ((n : ℝ) - 1))) * Iso n i j k l

/-- Flattening of a 4-fold finite sum over `Fin n` into a single sum over the product type
`((Fin n × Fin n) × Fin n) × Fin n`. -/
theorem kato_sum4_prod {M : Type*} [AddCommMonoid M]
    (F : Fin n → Fin n → Fin n → Fin n → M) :
    (∑ i, ∑ j, ∑ k, ∑ l, F i j k l)
      = ∑ p : ((Fin n × Fin n) × Fin n) × Fin n,
          F p.1.1.1 p.1.1.2 p.1.2 p.2 := by
  rw [← Fintype.sum_prod_type (f := fun p : Fin n × Fin n => ∑ k, ∑ l, F p.1 p.2 k l),
      ← Fintype.sum_prod_type
        (f := fun p : (Fin n × Fin n) × Fin n => ∑ l, F p.1.1 p.1.2 p.2 l),
      ← Fintype.sum_prod_type
        (f := fun p : ((Fin n × Fin n) × Fin n) × Fin n => F p.1.1.1 p.1.1.2 p.1.2 p.2)]

/-- **Cauchy–Schwarz for curvature arrays**: `(∑ Aᵢⱼₖₗ Bᵢⱼₖₗ)² ≤ (∑ Aᵢⱼₖₗ²)(∑ Bᵢⱼₖₗ²)`. -/
theorem kato_cs (A B : Curv4 n) :
    (∑ i, ∑ j, ∑ k, ∑ l, A i j k l * B i j k l) ^ 2
      ≤ (∑ i, ∑ j, ∑ k, ∑ l, A i j k l ^ 2) *
        (∑ i, ∑ j, ∑ k, ∑ l, B i j k l ^ 2) := by
  rw [kato_sum4_prod (fun i j k l => A i j k l * B i j k l),
      kato_sum4_prod (fun i j k l => A i j k l ^ 2),
      kato_sum4_prod (fun i j k l => B i j k l ^ 2)]
  exact Finset.sum_mul_sq_le_sq_mul_sq Finset.univ _ _

/-- **Trace-free norm as a sum of squares.**  For an array `A` antisymmetric in its first pair,
`frobSqTF A = |A − (scalAlg A/(n(n−1))) • Iso n|²`. -/
theorem kato_tf_norm (A : Curv4 n) (hanti : ∀ i j k l, A j i k l = - A i j k l) :
    frobSqTF A = ∑ i, ∑ j, ∑ k, ∑ l,
      (A i j k l - (scalAlg A / ((n : ℝ) * ((n : ℝ) - 1))) * Iso n i j k l) ^ 2 := by
  have hpair := rm_iso_trace A hanti
  have hexpand := frobSq_sub_smul A (scalAlg A / ((n : ℝ) * ((n : ℝ) - 1)))
  rw [hpair, iso_norm_sq n] at hexpand
  rw [hexpand, show frobSqTF A = frobSq A - 2 * scalAlg A ^ 2 / ((n : ℝ) * ((n : ℝ) - 1)) from rfl]
  linarith [div_sq_algebra (scalAlg A) ((n : ℝ) * ((n : ℝ) - 1))]

/-- `∑_m frobSqTF (T m)` expanded into the bracket appearing in the statement of `kato_array`. -/
theorem kato_sum_tf (T : Fin n → Curv4 n) :
    (∑ m, frobSqTF (T m)) = (∑ m, frobSq (T m)) -
      2 * (∑ m, (∑ i, ∑ j, T m i j i j) ^ 2) / ((n : ℝ) * ((n : ℝ) - 1)) := by
  simp only [frobSqTF, scalAlg, Finset.sum_sub_distrib, Finset.sum_div, Finset.mul_sum]

/-- **Kato's inequality, trace-free form.**  `∑_m (2 ⟪R°, T°_m⟫)² ≤ 4 |R°|² ∑_m |T°_m|²`, proved
termwise by Cauchy–Schwarz `kato_cs`. -/
theorem kato_array_aux (R : Curv4 n) (hR : IsAlgCurv R) (T : Fin n → Curv4 n)
    (hT1 : ∀ m i j k l, T m j i k l = - T m i j k l) :
    (∑ m, (2 * (∑ i, ∑ j, ∑ k, ∑ l, katoTF R i j k l * katoTF (T m) i j k l)) ^ 2)
      ≤ 4 * frobSqTF R * (∑ m, frobSqTF (T m)) := by
  have hRnorm : (∑ i, ∑ j, ∑ k, ∑ l, katoTF R i j k l ^ 2) = frobSqTF R :=
    (kato_tf_norm R hR.1).symm
  have hTnorm : ∀ m, (∑ i, ∑ j, ∑ k, ∑ l, katoTF (T m) i j k l ^ 2) = frobSqTF (T m) :=
    fun m => (kato_tf_norm (T m) (hT1 m)).symm
  have hle : (∑ m, ((∑ i, ∑ j, ∑ k, ∑ l, katoTF R i j k l * katoTF (T m) i j k l)) ^ 2)
      ≤ ∑ m, (frobSqTF R * frobSqTF (T m)) := by
    apply Finset.sum_le_sum; intro m _
    calc ((∑ i, ∑ j, ∑ k, ∑ l, katoTF R i j k l * katoTF (T m) i j k l)) ^ 2
        ≤ (∑ i, ∑ j, ∑ k, ∑ l, katoTF R i j k l ^ 2) *
          (∑ i, ∑ j, ∑ k, ∑ l, katoTF (T m) i j k l ^ 2) := kato_cs _ _
      _ = frobSqTF R * frobSqTF (T m) := by rw [hRnorm, hTnorm m]
  calc (∑ m, (2 * (∑ i, ∑ j, ∑ k, ∑ l, katoTF R i j k l * katoTF (T m) i j k l)) ^ 2)
      = 4 * ∑ m, ((∑ i, ∑ j, ∑ k, ∑ l, katoTF R i j k l * katoTF (T m) i j k l)) ^ 2 := by
        rw [show (∑ m, (2 * (∑ i, ∑ j, ∑ k, ∑ l,
                katoTF R i j k l * katoTF (T m) i j k l)) ^ 2)
            = ∑ m, 4 * ((∑ i, ∑ j, ∑ k, ∑ l,
                katoTF R i j k l * katoTF (T m) i j k l)) ^ 2 from
          Finset.sum_congr rfl (fun m _ => by ring)]
        rw [Finset.mul_sum]
    _ ≤ 4 * ∑ m, (frobSqTF R * frobSqTF (T m)) :=
        mul_le_mul_of_nonneg_left hle (by norm_num)
    _ = 4 * frobSqTF R * (∑ m, frobSqTF (T m)) := by rw [← Finset.mul_sum]; ring

/-- **Kato inequality at the level of curvature arrays.** `R : Curv4 n` is a curvature array
(`IsAlgCurv`) and `T m i j k l = (∇_m Rm)_{ijkl}` its covariant derivative array, with the two
antisymmetries `T m j i k l = -T m i j k l`, `T m i j l k = -T m i j k l`. Writing `R°` and `T°_m`
for the trace-free parts (`R° = R − (scalAlg R/(n(n−1)))•Iso n`, `T°_m = T m − (∑ᵢⱼ T m i j i j/(n(n−1)))•Iso n`),
the squared norm of the gradient of `|Rm°|²` is bounded by `4|Rm°|²|∇Rm°|²`:
`∑_m (2∑ᵢⱼₖₗ R°ᵢⱼₖₗ (T°_m)ᵢⱼₖₗ)² ≤ 4 (frobSqTF R) (∑_m frobSq (T°_m))`,
where the right-hand trace-free norm is `∑_m (frobSq (T m) − 2(∑ᵢⱼ T m i j i j)²/(n(n−1)))`.
This is Cauchy–Schwarz `(∑ R°·T°)² ≤ (∑R°²)(∑T°²)` summed over `m`. -/
theorem kato_array {n : ℕ} (R : Curv4 n) (hR : IsAlgCurv R) (T : Fin n → Curv4 n)
    (hT1 : ∀ m i j k l, T m j i k l = - T m i j k l)
    (hT2 : ∀ m i j k l, T m i j l k = - T m i j k l) :
    (∑ m, (2 * (∑ i, ∑ j, ∑ k, ∑ l,
        (R i j k l - (scalAlg R / ((n : ℝ) * ((n : ℝ) - 1))) * Iso n i j k l) *
        (T m i j k l - ((∑ i', ∑ j', T m i' j' i' j') / ((n : ℝ) * ((n : ℝ) - 1))) *
          Iso n i j k l))) ^ 2)
      ≤ 4 * frobSqTF R * (∑ m, frobSq (T m) - 2 * (∑ m, (∑ i, ∑ j, T m i j i j) ^ 2) /
          ((n : ℝ) * ((n : ℝ) - 1))) := by
  have h := kato_array_aux R hR T hT1
  rw [kato_sum_tf T] at h
  exact h

end Work.Diff.GE
