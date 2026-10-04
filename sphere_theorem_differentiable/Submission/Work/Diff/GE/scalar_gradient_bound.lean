import Mathlib
import Submission.Work.Diff.GE.bianchi_kato_defs
import Submission.Work.Diff.GE.scalar_gradient_defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1000000

namespace Work.Diff.GE

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric

variable {n : ℕ}

/-! ## Part 1. Elementary contractions of `Iso n` -/

/-- `∑ᵢ Iso n i j i m = (n−1)` if `j = m` and `0` otherwise. -/
theorem sum_Iso_pattern (j m : Fin n) :
    (∑ i : Fin n, Iso n i j i m) = if j = m then ((n : ℝ) - 1) else 0 := by
  have h : ∀ i : Fin n, Iso n i j i m
      = (if j = m then (1 : ℝ) else 0)
        - (if i = m then (1 : ℝ) else 0) * (if j = i then (1 : ℝ) else 0) := by
    intro i
    simp only [Submission.Diff.Alg.Iso]
    norm_num
  rw [Finset.sum_congr rfl (fun i _ => h i), Finset.sum_sub_distrib]
  have h2 : ∀ i : Fin n,
      (if i = m then (1 : ℝ) else 0) * (if j = i then (1 : ℝ) else 0)
        = (if i = m then (if j = i then (1 : ℝ) else 0) else 0) := by
    intro i
    by_cases hi : i = m <;> simp [hi]
  rw [Finset.sum_congr rfl (fun i _ => h2 i), Finset.sum_ite_eq']
  simp only [Finset.mem_univ, ite_true]
  have hc : (∑ _x : Fin n, (if j = m then (1 : ℝ) else 0))
      = (n : ℝ) * (if j = m then (1 : ℝ) else 0) := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [hc]
  by_cases hjm : j = m <;> simp [hjm]

/-- `scalAlg (Iso n) = n (n−1)`. -/
theorem scalAlg_Iso : scalAlg (Iso n) = (n : ℝ) * ((n : ℝ) - 1) := by
  rw [show scalAlg (Iso n) = ∑ i : Fin n, ∑ j : Fin n, Iso n i j i j from rfl]
  have h : ∀ i j : Fin n, Iso n i j i j = 1 - (if i = j then (1 : ℝ) else 0) := by
    intro i j
    simp only [Submission.Diff.Alg.Iso]
    by_cases hij : i = j <;> simp_all
  rw [Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => h i j))]
  have hsum : ∀ i : Fin n, (∑ j : Fin n, (1 - (if i = j then (1 : ℝ) else 0)))
      = (n : ℝ) - 1 := by
    intro i
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.sum_ite_eq]
    simp only [Finset.mem_univ, ite_true, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring
  rw [Finset.sum_congr rfl (fun i _ => hsum i), Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]

/-- `∑_{abcd} A_{abcd} Iso n_{abcd} = 2 scalAlg A` for an array antisymmetric in the last pair. -/
theorem sum_mul_Iso (A : Curv4 n) (hA : ∀ i j k l, A i j l k = - A i j k l) :
    (∑ i, ∑ j, ∑ k, ∑ l, A i j k l * Iso n i j k l) = 2 * scalAlg A := by
  have h1 : (∑ i, ∑ j, ∑ k, ∑ l,
      A i j k l * (if i = k then (1 : ℝ) else 0) * (if j = l then (1 : ℝ) else 0))
        = scalAlg A := by
    simp only [scalAlg]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    have hl : ∀ k : Fin n,
        (∑ l, A i j k l * (if i = k then (1 : ℝ) else 0) * (if j = l then (1 : ℝ) else 0))
          = (if i = k then A i j k j else 0) := by
      intro k
      have hll : (∑ l, A i j k l * (if i = k then (1 : ℝ) else 0)
            * (if j = l then (1 : ℝ) else 0))
          = (if i = k then (1 : ℝ) else 0) * (∑ l, if j = l then A i j k l else 0) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun l _ => ?_
        by_cases hik : i = k <;> simp [hik]
      rw [hll, Finset.sum_ite_eq Finset.univ j (fun l => A i j k l)]
      simp only [Finset.mem_univ, ite_true]
      by_cases hik : i = k <;> simp [hik]
    rw [Finset.sum_congr rfl (fun k _ => hl k),
      Finset.sum_ite_eq Finset.univ i (fun k => A i j k j)]
    simp
  have h2 : (∑ i, ∑ j, ∑ k, ∑ l,
      A i j k l * (if i = l then (1 : ℝ) else 0) * (if j = k then (1 : ℝ) else 0))
        = -scalAlg A := by
    have hstep : (∑ i, ∑ j, ∑ k, ∑ l,
        A i j k l * (if i = l then (1 : ℝ) else 0) * (if j = k then (1 : ℝ) else 0))
          = ∑ i, ∑ j, A i j j i := by
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      have hl : ∀ k : Fin n,
          (∑ l, A i j k l * (if i = l then (1 : ℝ) else 0) * (if j = k then (1 : ℝ) else 0))
            = (if j = k then A i j k i else 0) := by
        intro k
        have hll : (∑ l, A i j k l * (if i = l then (1 : ℝ) else 0)
              * (if j = k then (1 : ℝ) else 0))
            = (if j = k then (1 : ℝ) else 0) * (∑ l, if i = l then A i j k l else 0) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun l _ => ?_
          by_cases hjk : j = k <;> simp [hjk]
        rw [hll, Finset.sum_ite_eq Finset.univ i (fun l => A i j k l)]
        simp only [Finset.mem_univ, ite_true]
        by_cases hjk : j = k <;> simp [hjk]
      rw [Finset.sum_congr rfl (fun k _ => hl k),
        Finset.sum_ite_eq Finset.univ j (fun k => A i j k i)]
      simp
    rw [hstep]
    have hneg : ∀ i j : Fin n, A i j j i = -A i j i j := fun i j => hA i j i j
    simp only [hneg, scalAlg, Finset.sum_neg_distrib]
  calc (∑ i, ∑ j, ∑ k, ∑ l, A i j k l * Iso n i j k l)
      = (∑ i, ∑ j, ∑ k, ∑ l,
            A i j k l * (if i = k then (1 : ℝ) else 0) * (if j = l then (1 : ℝ) else 0))
        - (∑ i, ∑ j, ∑ k, ∑ l,
            A i j k l * (if i = l then (1 : ℝ) else 0) * (if j = k then (1 : ℝ) else 0)) := by
        simp only [Submission.Diff.Alg.Iso, mul_sub, mul_assoc, Finset.sum_sub_distrib]
    _ = 2 * scalAlg A := by rw [h1, h2]; ring

/-- `frobSq (Iso n) = 2 n (n−1)`. -/
theorem frobSq_Iso : frobSq (Iso n) = 2 * (n : ℝ) * ((n : ℝ) - 1) := by
  have hanti : ∀ i j k l, Iso n i j l k = - Iso n i j k l := by
    intro i j k l
    simp only [Submission.Diff.Alg.Iso]
    ring
  have hself : frobSq (Iso n) = (∑ i, ∑ j, ∑ k, ∑ l, Iso n i j k l * Iso n i j k l) := by
    simp only [frobSq, pow_two]
  rw [hself, sum_mul_Iso (Iso n) hanti, scalAlg_Iso]
  ring

/-- `frobSq` is nonnegative. -/
theorem frobSq_nonneg (A : Curv4 n) : 0 ≤ frobSq A := by
  simp only [frobSq]
  exact Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ =>
    Finset.sum_nonneg (fun k _ => Finset.sum_nonneg (fun l _ => sq_nonneg _))))

/-- Every squared component is at most the squared Frobenius norm. -/
theorem sq_le_frobSq (A : Curv4 n) (a b c d : Fin n) : (A a b c d) ^ 2 ≤ frobSq A := by
  rw [frobSq]
  calc (A a b c d) ^ 2
      ≤ ∑ l : Fin n, (A a b c l) ^ 2 :=
        Finset.single_le_sum (fun l _ => sq_nonneg _) (Finset.mem_univ d)
    _ ≤ ∑ k : Fin n, ∑ l : Fin n, (A a b k l) ^ 2 :=
        Finset.single_le_sum (fun k _ => Finset.sum_nonneg (fun l _ => sq_nonneg _))
          (Finset.mem_univ c)
    _ ≤ ∑ j : Fin n, ∑ k : Fin n, ∑ l : Fin n, (A a j k l) ^ 2 :=
        Finset.single_le_sum (fun j _ => Finset.sum_nonneg (fun k _ =>
          Finset.sum_nonneg (fun l _ => sq_nonneg _))) (Finset.mem_univ b)
    _ ≤ ∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n, ∑ l : Fin n, (A i j k l) ^ 2 :=
        Finset.single_le_sum (fun i _ => Finset.sum_nonneg (fun j _ =>
          Finset.sum_nonneg (fun k _ => Finset.sum_nonneg (fun l _ => sq_nonneg _))))
          (Finset.mem_univ a)

/-- Cauchy–Schwarz: `(∑ f)² ≤ #ι · ∑ f²`. -/
theorem sum_sq_le_card_mul_sum_sq {ι : Type*} [Fintype ι] (f : ι → ℝ) :
    (∑ i, f i) ^ 2 ≤ (Fintype.card ι : ℝ) * ∑ i, (f i) ^ 2 := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ) f (fun _ => (1 : ℝ))
  simpa [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_comm] using h

/-- Expansion of `∑ (f − c g)²`. -/
theorem sum_sq_sub_mul (f g : Fin n → Fin n → Fin n → Fin n → ℝ) (c : ℝ) :
    (∑ a, ∑ b, ∑ e, ∑ d, (f a b e d - c * g a b e d) ^ 2)
      = (∑ a, ∑ b, ∑ e, ∑ d, f a b e d ^ 2)
        - 2 * c * (∑ a, ∑ b, ∑ e, ∑ d, f a b e d * g a b e d)
        + c ^ 2 * (∑ a, ∑ b, ∑ e, ∑ d, g a b e d ^ 2) := by
  have h : ∀ a b e d, (f a b e d - c * g a b e d) ^ 2
      = f a b e d ^ 2 - 2 * c * (f a b e d * g a b e d) + c ^ 2 * g a b e d ^ 2 := by
    intro a b e d
    ring
  simp only [h, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  have hmid : (∑ a, ∑ b, ∑ e, ∑ d, 2 * c * (f a b e d * g a b e d))
      = 2 * c * (∑ a, ∑ b, ∑ e, ∑ d, f a b e d * g a b e d) := by
    simp only [Finset.mul_sum]
  have hlast : (∑ a, ∑ b, ∑ e, ∑ d, c ^ 2 * g a b e d ^ 2)
      = c ^ 2 * (∑ a, ∑ b, ∑ e, ∑ d, g a b e d ^ 2) := by
    simp only [Finset.mul_sum]
  rw [hmid, hlast]

/-- The squared norm of the trace-free part of a slice, per derivative index. -/
theorem frobSq_tfPart (hn : 2 ≤ n) (T : Fin n → Curv4 n)
    (h2 : ∀ m i j k l, T m i j l k = - T m i j k l) (m : Fin n) :
    frobSq (tfPart T m)
      = frobSq (T m) - 2 * (scTrace T m) ^ 2 / ((n : ℝ) * ((n : ℝ) - 1)) := by
  have hn0 : (n : ℝ) ≠ 0 := by
    exact_mod_cast (by omega : n ≠ 0)
  have hn1 : ((n : ℝ) - 1) ≠ 0 := by
    have hne : n ≠ 1 := by omega
    intro h
    exact hne (by exact_mod_cast (by linarith : (n : ℝ) = 1))
  have hscal : scalAlg (T m) = scTrace T m := by simp only [scalAlg, scTrace]
  have hIso : (∑ i, ∑ j, ∑ k, ∑ l, T m i j k l * Iso n i j k l)
      = 2 * scTrace T m := by
    rw [sum_mul_Iso (T m) (h2 m), hscal]
  have hsq : (∑ i, ∑ j, ∑ k, ∑ l, Iso n i j k l ^ 2)
      = 2 * (n : ℝ) * ((n : ℝ) - 1) := by
    rw [show (∑ i, ∑ j, ∑ k, ∑ l, Iso n i j k l ^ 2) = frobSq (Iso n) from by
      simp only [frobSq, pow_two], frobSq_Iso]
  have hsqT : (∑ i, ∑ j, ∑ k, ∑ l, T m i j k l ^ 2) = frobSq (T m) := by
    simp only [frobSq, pow_two]
  have htf : frobSq (tfPart T m)
      = (∑ a, ∑ b, ∑ e, ∑ d,
          (T m a b e d - (scTrace T m / ((n : ℝ) * ((n : ℝ) - 1)))
            * Iso n a b e d) ^ 2) := by
    simp only [frobSq]
    exact Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ =>
      Finset.sum_congr rfl (fun e _ => Finset.sum_congr rfl (fun d _ => by
        simp only [tfPart]))))
  rw [htf, sum_sq_sub_mul, hIso, hsq, hsqT]
  field_simp
  ring

/-- `∑ₘ frobSq (T m) − 2 (∑ₘ (scTrace T m)²)/(n(n−1)) = ∑ₘ frobSq (tfPart T m)`. -/
theorem frob_sum_eq_tfNormSq (hn : 2 ≤ n) (T : Fin n → Curv4 n)
    (h2 : ∀ m i j k l, T m i j l k = - T m i j k l) :
    (∑ m : Fin n, frobSq (T m))
        - 2 * (∑ m : Fin n, (scTrace T m) ^ 2) / ((n : ℝ) * ((n : ℝ) - 1))
      = ∑ m : Fin n, frobSq (tfPart T m) := by
  have hsplit : (∑ m : Fin n, (frobSq (T m)
          - 2 * (scTrace T m) ^ 2 / ((n : ℝ) * ((n : ℝ) - 1))))
      = (∑ m : Fin n, frobSq (T m))
        - 2 * (∑ m : Fin n, (scTrace T m) ^ 2) / ((n : ℝ) * ((n : ℝ) - 1)) := by
    rw [Finset.sum_sub_distrib, ← Finset.sum_div, ← Finset.mul_sum]
  rw [← hsplit]
  exact Finset.sum_congr rfl (fun m _ => (frobSq_tfPart hn T h2 m).symm)

/-! ## Part 2. The contracted second Bianchi identity -/

/-- The scalar-curvature gradient is twice the "divergence of the Ricci tensor" of the array. -/
theorem scTrace_eq_two_sum (T : Fin n → Curv4 n)
    (h1 : ∀ m i j k l, T m j i k l = - T m i j k l)
    (h2 : ∀ m i j k l, T m i j l k = - T m i j k l)
    (h3 : ∀ m i j k l, T m i j k l + T i j m k l + T j m i k l = 0) :
    ∀ j : Fin n, scTrace T j = 2 * ∑ i : Fin n, ∑ m : Fin n, T m i j i m := by
  intro j
  have step1 : ∀ i j k : Fin n,
      ∑ m : Fin n, (T m i j k m + T i j m k m + T j m i k m) = 0 :=
    fun i j k => Finset.sum_eq_zero (fun m _ => h3 m i j k m)
  have step2 : ∀ i j k : Fin n,
      ∑ m : Fin n, T m i j k m = (∑ m : Fin n, T j i m k m) - ∑ m : Fin n, T i j m k m := by
    intro i j k
    have h := step1 i j k
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib] at h
    have hc : ∑ m : Fin n, T j m i k m = - ∑ m : Fin n, T j i m k m := by
      rw [← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl (fun m _ => h1 j i m k m)
    linarith
  have step3 : ∑ i : Fin n, ∑ m : Fin n, T m i j i m
      = (∑ i : Fin n, ∑ m : Fin n, T j i m i m)
        - ∑ i : Fin n, ∑ m : Fin n, T i j m i m := by
    rw [Finset.sum_congr rfl (fun i _ => step2 i j i), Finset.sum_sub_distrib]
  have hA : ∑ i : Fin n, ∑ m : Fin n, T j i m i m = scTrace T j := rfl
  have hB : ∑ i : Fin n, ∑ m : Fin n, T i j m i m = ∑ i : Fin n, ∑ m : Fin n, T m i j i m := by
    have key : ∑ i : Fin n, ∑ m : Fin n, T m i j i m
        = ∑ i : Fin n, ∑ m : Fin n, T m j i m i := by
      refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun m _ => ?_))
      have e1 := h1 m j i i m
      have e2 := h2 m j i m i
      linarith
    rw [key, Finset.sum_comm]
  rw [hA, hB] at step3
  linarith

/-! ## Part 3. Decomposition of the divergence pair -/

/-- `∑ᵢₘ T m i j i m = ∑ᵢₘ (tfPart T m) i j i m + (scTrace T j)/n`. -/
theorem sum_eq_tfPart_add (hn : 2 ≤ n) (T : Fin n → Curv4 n) (j : Fin n) :
    (∑ i : Fin n, ∑ m : Fin n, T m i j i m)
      = (∑ i : Fin n, ∑ m : Fin n, tfPart T m i j i m) + scTrace T j / (n : ℝ) := by
  have hn0 : (n : ℝ) ≠ 0 := by
    exact_mod_cast (by omega : n ≠ 0)
  have hn1 : ((n : ℝ) - 1) ≠ 0 := by
    have hne : n ≠ 1 := by omega
    intro h
    exact hne (by exact_mod_cast (by linarith : (n : ℝ) = 1))
  have hdec : ∀ (i m : Fin n), T m i j i m
      = tfPart T m i j i m
        + (scTrace T m / ((n : ℝ) * ((n : ℝ) - 1))) * Iso n i j i m := by
    intro i m
    simp only [tfPart]
    ring
  have hstep : ∀ m : Fin n,
      (∑ i : Fin n, scTrace T m / ((n : ℝ) * ((n : ℝ) - 1)) * Iso n i j i m)
        = (if j = m then scTrace T m / ((n : ℝ) * ((n : ℝ) - 1)) * ((n : ℝ) - 1) else 0) := by
    intro m
    rw [← Finset.mul_sum, sum_Iso_pattern]
    by_cases hjm : j = m <;> simp [hjm]
  have hS : (∑ i : Fin n, ∑ m : Fin n,
        (scTrace T m / ((n : ℝ) * ((n : ℝ) - 1))) * Iso n i j i m)
      = scTrace T j / (n : ℝ) := by
    rw [Finset.sum_comm,
      Finset.sum_congr rfl (fun m _ => hstep m), Finset.sum_ite_eq]
    simp only [Finset.mem_univ, ite_true]
    field_simp
  calc (∑ i : Fin n, ∑ m : Fin n, T m i j i m)
      = ∑ i : Fin n, ∑ m : Fin n, (tfPart T m i j i m
          + (scTrace T m / ((n : ℝ) * ((n : ℝ) - 1))) * Iso n i j i m) :=
        Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun m _ => hdec i m))
    _ = (∑ i : Fin n, ∑ m : Fin n, tfPart T m i j i m)
          + ∑ i : Fin n, ∑ m : Fin n,
              (scTrace T m / ((n : ℝ) * ((n : ℝ) - 1))) * Iso n i j i m := by
        simp only [Finset.sum_add_distrib]
    _ = (∑ i : Fin n, ∑ m : Fin n, tfPart T m i j i m) + scTrace T j / (n : ℝ) := by
        rw [hS]

/-! ## Part 4. Cauchy–Schwarz -/

/-- From the homogeneous contracted Bianchi identity, Cauchy–Schwarz bounds the scalar gradients. -/
theorem bound_of_tfPart (hn : 3 ≤ n) (T : Fin n → Curv4 n)
    (hid : ∀ j : Fin n, scTrace T j =
      (2 * (n : ℝ) / ((n : ℝ) - 2)) * ∑ i : Fin n, ∑ m : Fin n, tfPart T m i j i m) :
    (∑ m : Fin n, (scTrace T m) ^ 2)
      ≤ (4 * (n : ℝ) ^ 6 / ((n : ℝ) - 2) ^ 2) * ∑ m : Fin n, frobSq (tfPart T m) := by
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by
    have : (1 : ℕ) ≤ n := by omega
    exact_mod_cast this
  have hnn : (0 : ℝ) ≤ (n : ℝ) := by positivity
  have hden : (0 : ℝ) < ((n : ℝ) - 2) := by
    have : (2 : ℝ) < (n : ℝ) := by
      have : (2 : ℕ) < n := by omega
      exact_mod_cast this
    linarith
  have hPnn : 0 ≤ ∑ m : Fin n, frobSq (tfPart T m) :=
    Finset.sum_nonneg (fun m _ => frobSq_nonneg _)
  -- Cauchy–Schwarz for the outer (`i`) sum
  have hcs1 : ∀ j : Fin n, (∑ i : Fin n, ∑ m : Fin n, tfPart T m i j i m) ^ 2
      ≤ (n : ℝ) * ∑ i : Fin n, (∑ m : Fin n, tfPart T m i j i m) ^ 2 := by
    intro j
    have h := sum_sq_le_card_mul_sum_sq
      (fun i : Fin n => ∑ m : Fin n, tfPart T m i j i m)
    simpa [Fintype.card_fin] using h
  -- Cauchy–Schwarz for the inner (`m`) sum
  have hcs2 : ∀ (j i : Fin n), (∑ m : Fin n, tfPart T m i j i m) ^ 2
      ≤ (n : ℝ) * ∑ m : Fin n, (tfPart T m i j i m) ^ 2 := by
    intro j i
    have h := sum_sq_le_card_mul_sum_sq (fun m : Fin n => tfPart T m i j i m)
    simpa [Fintype.card_fin] using h
  -- the `(i, j, i, m)` components of one slice
  have hslice_i : ∀ (j m : Fin n),
      (∑ i : Fin n, (tfPart T m i j i m) ^ 2) ≤ frobSq (tfPart T m) := by
    intro j m
    rw [frobSq]
    calc (∑ i : Fin n, (tfPart T m i j i m) ^ 2)
        ≤ ∑ i : Fin n, ∑ k : Fin n, ∑ l : Fin n, (tfPart T m i j k l) ^ 2 := by
          refine Finset.sum_le_sum (fun i _ => ?_)
          calc (tfPart T m i j i m) ^ 2
              ≤ ∑ l : Fin n, (tfPart T m i j i l) ^ 2 :=
                Finset.single_le_sum (fun l _ => sq_nonneg _) (Finset.mem_univ m)
            _ ≤ ∑ k : Fin n, ∑ l : Fin n, (tfPart T m i j k l) ^ 2 :=
                Finset.single_le_sum (fun k _ => Finset.sum_nonneg (fun l _ => sq_nonneg _))
                  (Finset.mem_univ i)
      _ ≤ ∑ i : Fin n, ∑ j' : Fin n, ∑ k : Fin n, ∑ l : Fin n, (tfPart T m i j' k l) ^ 2 := by
          refine Finset.sum_le_sum (fun i _ => ?_)
          exact Finset.single_le_sum (fun j' _ => Finset.sum_nonneg (fun k _ =>
            Finset.sum_nonneg (fun l _ => sq_nonneg _))) (Finset.mem_univ j)
  have hsum_slice : ∀ j : Fin n,
      (∑ i : Fin n, ∑ m : Fin n, (tfPart T m i j i m) ^ 2)
        ≤ ∑ m : Fin n, frobSq (tfPart T m) := by
    intro j
    calc (∑ i : Fin n, ∑ m : Fin n, (tfPart T m i j i m) ^ 2)
        = ∑ m : Fin n, ∑ i : Fin n, (tfPart T m i j i m) ^ 2 := Finset.sum_comm
      _ ≤ ∑ m : Fin n, frobSq (tfPart T m) := Finset.sum_le_sum (fun m _ => hslice_i j m)
  -- bound on the inner sum
  have hE : ∀ j : Fin n, (∑ i : Fin n, (∑ m : Fin n, tfPart T m i j i m) ^ 2)
      ≤ (n : ℝ) * ∑ m : Fin n, frobSq (tfPart T m) := by
    intro j
    calc (∑ i : Fin n, (∑ m : Fin n, tfPart T m i j i m) ^ 2)
        ≤ ∑ i : Fin n, (n : ℝ) * ∑ m : Fin n, (tfPart T m i j i m) ^ 2 :=
          Finset.sum_le_sum (fun i _ => hcs2 j i)
      _ = (n : ℝ) * ∑ i : Fin n, ∑ m : Fin n, (tfPart T m i j i m) ^ 2 := by
          rw [Finset.mul_sum]
      _ ≤ (n : ℝ) * ∑ m : Fin n, frobSq (tfPart T m) :=
          mul_le_mul_of_nonneg_left (hsum_slice j) hnn
  have key : ∀ j : Fin n, (scTrace T j) ^ 2
      ≤ ((2 * (n : ℝ) / ((n : ℝ) - 2)) ^ 2 * (n : ℝ) * (n : ℝ))
          * ∑ m : Fin n, frobSq (tfPart T m) := by
    intro j
    calc (scTrace T j) ^ 2
        = (2 * (n : ℝ) / ((n : ℝ) - 2)) ^ 2
            * (∑ i : Fin n, ∑ m : Fin n, tfPart T m i j i m) ^ 2 := by
          rw [hid j]; ring
      _ ≤ (2 * (n : ℝ) / ((n : ℝ) - 2)) ^ 2
            * ((n : ℝ) * ∑ i : Fin n, (∑ m : Fin n, tfPart T m i j i m) ^ 2) :=
          mul_le_mul_of_nonneg_left (hcs1 j) (sq_nonneg _)
      _ ≤ (2 * (n : ℝ) / ((n : ℝ) - 2)) ^ 2
            * ((n : ℝ) * ((n : ℝ) * ∑ m : Fin n, frobSq (tfPart T m))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hE j) hnn) (sq_nonneg _)
      _ = ((2 * (n : ℝ) / ((n : ℝ) - 2)) ^ 2 * (n : ℝ) * (n : ℝ))
            * ∑ m : Fin n, frobSq (tfPart T m) := by ring
  have hsum : (∑ m : Fin n, (scTrace T m) ^ 2)
      ≤ (n : ℝ) * (((2 * (n : ℝ) / ((n : ℝ) - 2)) ^ 2 * (n : ℝ) * (n : ℝ))
          * ∑ m : Fin n, frobSq (tfPart T m)) := by
    calc (∑ m : Fin n, (scTrace T m) ^ 2)
        ≤ ∑ m : Fin n, ((2 * (n : ℝ) / ((n : ℝ) - 2)) ^ 2 * (n : ℝ) * (n : ℝ))
            * ∑ m : Fin n, frobSq (tfPart T m) := Finset.sum_le_sum (fun j _ => key j)
      _ = (n : ℝ) * (((2 * (n : ℝ) / ((n : ℝ) - 2)) ^ 2 * (n : ℝ) * (n : ℝ))
            * ∑ m : Fin n, frobSq (tfPart T m)) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  refine le_trans hsum ?_
  have hd : ((n : ℝ) - 2) ≠ 0 := ne_of_gt hden
  have hL : (n : ℝ) * (((2 * (n : ℝ) / ((n : ℝ) - 2)) ^ 2 * (n : ℝ) * (n : ℝ))
      * ∑ m : Fin n, frobSq (tfPart T m))
      = (4 * (n : ℝ) ^ 5 / ((n : ℝ) - 2) ^ 2) * ∑ m : Fin n, frobSq (tfPart T m) := by
    field_simp
    ring
  rw [hL]
  refine mul_le_mul_of_nonneg_right ?_ hPnn
  refine div_le_div_of_nonneg_right ?_ (by positivity)
  have hpow : (n : ℝ) ^ 5 ≤ (n : ℝ) ^ 6 := pow_le_pow_right₀ hn1 (by norm_num)
  nlinarith [hpow]

/-! ## Part 5. The scalar-curvature gradient bound -/

/-- **Scalar-curvature gradient bound at the level of curvature arrays.**
`T : Fin n → Curv4 n` is the array of covariant derivatives `(∇_m Rm)_{ijkl}` of a curvature tensor,
in an orthonormal frame: `T m j i k l = -T m i j k l` (antisymmetry in the first pair),
`T m i j l k = -T m i j k l` (antisymmetry in the last pair) and the *second Bianchi identity*
`T m i j k l + T i j m k l + T j m i k l = 0`. Then the "trace" `∇_m S = ∑ᵢⱼ T m i j i j` of `∇Rm`
is controlled by the *trace-free* part of `∇Rm`: with `|∇Rm°|² := ∑_m (frobSq (T m) − 2(∑ᵢⱼ T m i j i j)²/(n(n−1)))`,
`∑_m (∑ᵢⱼ T m i j i j)² ≤ K · |∇Rm°|²` for a constant `K` depending only on `n ≥ 3`.
This is the contracted second Bianchi identity `(1−2/n)∇S = 2 div Ric°` together with the algebraic
bounds on the trace-free Ricci tensor. -/
theorem scalar_gradient_bound {n : ℕ} (hn : 3 ≤ n) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (T : Fin n → Curv4 n),
      (∀ m i j k l, T m j i k l = - T m i j k l) →
      (∀ m i j k l, T m i j l k = - T m i j k l) →
      (∀ m i j k l, T m i j k l + T i j m k l + T j m i k l = 0) →
      (∑ m, (∑ i, ∑ j, T m i j i j) ^ 2) ≤
        K * (∑ m, frobSq (T m) - 2 * (∑ m, (∑ i, ∑ j, T m i j i j) ^ 2) /
          ((n : ℝ) * ((n : ℝ) - 1))) := by
  have hn2 : (2 : ℝ) < (n : ℝ) := by
    have : (2 : ℕ) < n := by omega
    exact_mod_cast this
  refine ⟨4 * (n : ℝ) ^ 6 / ((n : ℝ) - 2) ^ 2, ?_, ?_⟩
  · have hden : (0 : ℝ) < ((n : ℝ) - 2) := by linarith
    positivity
  · intro T h1 h2 h3
    have hn2' : 2 ≤ n := by omega
    have hident := scTrace_eq_two_sum T h1 h2 h3
    have hdec : ∀ j : Fin n,
        (∑ i : Fin n, ∑ m : Fin n, T m i j i m)
          = (∑ i : Fin n, ∑ m : Fin n, tfPart T m i j i m) + scTrace T j / (n : ℝ) :=
      fun j => sum_eq_tfPart_add hn2' T j
    have hna : (n : ℝ) ≠ 0 := by positivity
    have hnb : ((n : ℝ) - 2) ≠ 0 := ne_of_gt (by linarith : (0 : ℝ) < (n : ℝ) - 2)
    have hid : ∀ j : Fin n, scTrace T j =
        (2 * (n : ℝ) / ((n : ℝ) - 2)) * ∑ i : Fin n, ∑ m : Fin n, tfPart T m i j i m := by
      intro j
      have hA := hident j
      rw [hdec j] at hA
      have hA' := hA
      field_simp at hA'
      field_simp
      linarith
    have hb := bound_of_tfPart hn T hid
    have hf := frob_sum_eq_tfNormSq hn2' T h2
    simp only [scTrace] at hb hf ⊢
    rw [hf]
    exact hb

end Work.Diff.GE
