import Mathlib
import Submission.Work.Diff.Alg.Pinch.ChatShiftDefs
import Submission.Work.Diff.Alg.Pinch.inPIC2_comp_bound

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The traceless Ricci form of an `InPIC2` tensor is bounded by its scalar curvature

`Work.Diff.Alg.Pinch.ChatShift.ric0_form_bound` produces the constant `C` with

`|∑ᵢⱼ Ric₀(S)ᵢⱼ vᵢ vⱼ| ≤ C · scal(S) · ∑ᵢ vᵢ²`

for every algebraic curvature tensor `S` with nonnegative complex sectional curvature (`InPIC2`,
i.e. `S ∈ Ĉ`) and every vector `v`.

The proof only uses the *component* consequence of `InPIC2`:
`Work.Diff.Alg.Pinch.inPIC2_comp_bound` shows that some constant `C₀` satisfies `|Sᵢⱼₖₗ| ≤ C₀ · scal S`,
whence
* `|Ric(S)ᵢⱼ| = |∑ₖ Sₖᵢₖⱼ| ≤ n C₀ scal S`, and
* `|Ric₀(S)ᵢⱼ| = |Ric(S)ᵢⱼ − (scal S/n) δᵢⱼ| ≤ (n C₀ + 1) scal S`,
so that, by Cauchy–Schwarz on the coefficients of `v`,
`|∑ᵢⱼ Ric₀ᵢⱼ vᵢ vⱼ| ≤ (n C₀ + 1) scal S · (∑ᵢ |vᵢ|)² ≤ (n C₀ + 1) n scal S · ∑ᵢ vᵢ²`.

The constant necessarily grows with `n`: `Ric₀` never vanishes for tensors whose Ricci form is the
identity, while `scal S` stays bounded.
-/

namespace Work.Diff.Alg.Pinch.ChatShift

open Finset Submission.Diff.Alg

variable {n : ℕ}

/-- Componentwise bound for the Ricci tensor of a tensor whose curvature components are bounded
by `c · scal`. -/
private lemma abs_ric_le {R : Curv4 n} {c : ℝ}
    (hcomp : ∀ i j k l : Fin n, |R i j k l| ≤ c * scalAlg R) (i j : Fin n) :
    |ric R i j| ≤ (n : ℝ) * (c * scalAlg R) := by
  rw [ric]
  calc |∑ k, R k i k j| ≤ ∑ k, |R k i k j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _k : Fin n, c * scalAlg R := Finset.sum_le_sum (fun k _ => hcomp k i k j)
    _ = (n : ℝ) * (c * scalAlg R) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- The identity `∑ᵢ∑ⱼ |vᵢ| |vⱼ| = (∑ᵢ |vᵢ|)²`. -/
private lemma sum_sum_abs_eq (v : Fin n → ℝ) :
    (∑ i, ∑ j, (|v i| : ℝ) * |v j|) = (∑ i, |v i|) ^ 2 := by
  rw [sq, Finset.sum_mul_sum]

/-- Cauchy–Schwarz (squared, `f = |v|`, `g = 1`): `(∑ᵢ |vᵢ|)² ≤ n · ∑ᵢ vᵢ²`. -/
private lemma sq_abs_sum_le (v : Fin n → ℝ) :
    (∑ i, |v i|) ^ 2 ≤ (n : ℝ) * (∑ i, v i * v i) := by
  have h := sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun i : Fin n => |v i|)
  simp only [Fintype.card_fin, Finset.card_univ] at h
  refine h.trans_eq ?_
  congr 1
  apply Finset.sum_congr rfl; intro i _
  rw [sq_abs, pow_two]

theorem ric0_form_bound (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ S : Submission.Diff.Alg.Curv4 n, Submission.Diff.Alg.IsAlgCurv S →
      Submission.Diff.Alg.InPIC2 S → ∀ v : Fin n → ℝ,
      |∑ i, ∑ j, Work.Diff.Alg.Pinch.ric0 S i j * v i * v j|
        ≤ C * Submission.Diff.Alg.scalAlg S * (∑ i, v i * v i) := by
  obtain ⟨C0, hC0⟩ := (inPIC2_comp_bound n).1
  let C1 : ℝ := max C0 0
  have hC1 : 0 ≤ C1 := le_max_right C0 0
  refine ⟨((n : ℝ) * C1 + 1) * (n : ℝ), ?_, ?_⟩
  · exact mul_nonneg (add_nonneg (mul_nonneg (Nat.cast_nonneg n) hC1) zero_le_one)
      (Nat.cast_nonneg n)
  · intro S _ hP v
    have hscal : 0 ≤ scalAlg S := (inPIC2_metric_basic n).2.2 S hP
    -- every component of `S` is bounded by `C1 · scal S`
    have hcompS : ∀ i j k l : Fin n, |S i j k l| ≤ C1 * scalAlg S := by
      intro i j k l
      exact (hC0 S hP i j k l).trans (mul_le_mul_of_nonneg_right (le_max_left C0 0) hscal)
    have hric : ∀ i j : Fin n, |ric S i j| ≤ (n : ℝ) * (C1 * scalAlg S) :=
      fun i j => abs_ric_le hcompS i j
    -- hence every component of the traceless Ricci tensor is bounded by `(n C₁ + 1) · scal S`
    have hric0 : ∀ i j : Fin n, |ric0 S i j| ≤ ((n : ℝ) * C1 + 1) * scalAlg S := by
      intro i j
      have hdiv : |scalAlg S / (n : ℝ)| ≤ scalAlg S := by
        have hn : 0 < n := Fin.pos i
        have hn' : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
        rw [abs_of_nonneg (div_nonneg hscal hn'.le), div_le_iff₀ hn']
        calc scalAlg S = scalAlg S * 1 := by ring
          _ ≤ scalAlg S * (n : ℝ) := mul_le_mul_of_nonneg_left (by exact_mod_cast hn) hscal
      have hid2 : |id2 n i j| ≤ (1 : ℝ) := by
        rw [id2]; split <;> simp
      have hterm : |(scalAlg S / (n : ℝ)) * id2 n i j| ≤ scalAlg S := by
        rw [abs_mul]
        calc |scalAlg S / (n : ℝ)| * |id2 n i j| ≤ scalAlg S * 1 :=
              mul_le_mul hdiv hid2 (abs_nonneg _) hscal
          _ = scalAlg S := by ring
      calc |ric0 S i j| = |ric S i j - (scalAlg S / (n : ℝ)) * id2 n i j| := by
              simp only [ric0]
        _ ≤ |ric S i j| + |(scalAlg S / (n : ℝ)) * id2 n i j| := abs_sub _ _
        _ ≤ (n : ℝ) * (C1 * scalAlg S) + scalAlg S := add_le_add (hric i j) hterm
        _ = ((n : ℝ) * C1 + 1) * scalAlg S := by ring
    have hK : 0 ≤ ((n : ℝ) * C1 + 1) * scalAlg S :=
      mul_nonneg (add_nonneg (mul_nonneg (Nat.cast_nonneg n) hC1) zero_le_one) hscal
    calc |∑ i, ∑ j, ric0 S i j * v i * v j|
        ≤ ∑ i, ∑ j, |ric0 S i j| * |v i| * |v j| := by
          calc |∑ i, ∑ j, ric0 S i j * v i * v j|
              ≤ ∑ i, |∑ j, ric0 S i j * v i * v j| := Finset.abs_sum_le_sum_abs _ _
            _ ≤ ∑ i, ∑ j, |ric0 S i j * v i * v j| :=
                Finset.sum_le_sum (fun i _ => Finset.abs_sum_le_sum_abs _ _)
            _ = ∑ i, ∑ j, |ric0 S i j| * |v i| * |v j| := by
                apply Finset.sum_congr rfl; intro i _
                apply Finset.sum_congr rfl; intro j _
                rw [abs_mul, abs_mul]
      _ ≤ ∑ i, ∑ j, (((n : ℝ) * C1 + 1) * scalAlg S) * |v i| * |v j| := by
          apply Finset.sum_le_sum; intro i _
          apply Finset.sum_le_sum; intro j _
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right (hric0 i j) (abs_nonneg _)) (abs_nonneg _)
      _ = (((n : ℝ) * C1 + 1) * scalAlg S) * (∑ i, |v i|) ^ 2 := by
          rw [← sum_sum_abs_eq v, Finset.mul_sum]
          apply Finset.sum_congr rfl; intro i _
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl; intro j _
          ring
      _ ≤ (((n : ℝ) * C1 + 1) * scalAlg S) * ((n : ℝ) * ∑ i, v i * v i) :=
          mul_le_mul_of_nonneg_left (sq_abs_sum_le v) hK
      _ = (((n : ℝ) * C1 + 1) * (n : ℝ)) * scalAlg S * (∑ i, v i * v i) := by ring

end Work.Diff.Alg.Pinch.ChatShift
