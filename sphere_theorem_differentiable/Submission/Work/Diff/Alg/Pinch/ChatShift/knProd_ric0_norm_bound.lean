import Mathlib
import Submission.Work.Diff.Alg.Pinch.ChatShiftDefs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# `‖Ric₀ ∧ id‖ ≤ C · scal` for tensors with nonnegative complex sectional curvature

For an algebraic curvature tensor `S` with nonnegative complex sectional curvature (`InPIC2 S`),
the Kulkarni–Nomizu product of the traceless Ricci tensor with the identity is bounded in norm by
the scalar curvature: there is a constant `C` (depending only on `n`, not on `S`) with

  `‖Ric₀ S ∧ id‖ ≤ C · scalAlg S`.

The proof is purely componentwise.  `Work.Diff.Alg.Pinch.inPIC2_comp_bound` bounds every component
of `S` by `Cm · scalAlg S`, whence every component of the Ricci tensor satisfies
`|Ricᵢⱼ| ≤ n · Cm · scalAlg S` (a sum of `n` components), and the correction term
`(scalAlg S / n) · δᵢⱼ` is bounded by `scalAlg S` because `scalAlg S ≥ 0` and `n ≥ 1`
(`Work.Diff.Alg.Pinch.inPIC2_metric_basic` gives `scalAlg S ≥ 0`; the hypothesis `n ≥ 1` is
available from the index `i` on which the bound is evaluated, so that there is nothing to prove
in the empty case `n = 0`).  The four terms of the Kulkarni–Nomizu pattern are then each bounded
by `((n) · Cm + 1) · scalAlg S`, and the norm estimate follows from the fact that the norm on
`Curv4 n` is the supremum norm (`pi_norm_le_iff_of_nonneg`).
-/

namespace Work.Diff.Alg.Pinch.ChatShift

open Finset Submission.Diff.Alg Work.Diff.Alg.Pinch

variable {n : ℕ}

/-! ## Elementary component estimates -/

/-- Every entry of the identity `2`-tensor `id2 n` has absolute value at most `1`. -/
private lemma abs_id2_le_one (i j : Fin n) : |id2 n i j| ≤ 1 := by
  rw [id2]; split <;> simp

/-- Triangle inequality for the Kulkarni–Nomizu pattern `A - B - C + D`. -/
private lemma abs_sub_sub_add_le (A B C D : ℝ) : |A - B - C + D| ≤ |A| + |B| + |C| + |D| := by
  have h1 : |A - B - C + D| ≤ |A - B - C| + |D| := abs_add_le _ _
  have h2 : |A - B - C| ≤ |A - B| + |C| := abs_sub _ _
  have h3 : |A - B| ≤ |A| + |B| := abs_sub _ _
  linarith

/-- A `4`-index array is bounded in norm as soon as all its components are bounded by the same
nonnegative constant. -/
private lemma norm_le_of_components {X : Curv4 n} {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ i j k l, |X i j k l| ≤ c) : ‖X‖ ≤ c := by
  rw [pi_norm_le_iff_of_nonneg hc]
  intro i
  rw [pi_norm_le_iff_of_nonneg hc]
  intro j
  rw [pi_norm_le_iff_of_nonneg hc]
  intro k
  rw [pi_norm_le_iff_of_nonneg hc]
  intro l
  rw [Real.norm_eq_abs]
  exact h i j k l

/-! ## Component bounds for the Ricci and traceless Ricci tensors -/

/-- If every component of `S` is at most `Cm · scalAlg S` with `Cm ≥ 0` and `scalAlg S ≥ 0`, then
every component of the Ricci tensor is at most `n · (Cm · scalAlg S)`. -/
private lemma abs_ric_le {S : Curv4 n} {Cm : ℝ}
    (hCm : ∀ p q r s : Fin n, |S p q r s| ≤ Cm * scalAlg S) (p q : Fin n) :
    |ric S p q| ≤ (n : ℝ) * (Cm * scalAlg S) := by
  rw [ric]
  calc |∑ k, S k p k q| ≤ ∑ k, |S k p k q| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _k : Fin n, Cm * scalAlg S := Finset.sum_le_sum (fun k _ => hCm k p k q)
    _ = (n : ℝ) * (Cm * scalAlg S) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- Component bound for the traceless Ricci tensor: for `S` (no algebraic-curvature hypothesis
needed) with `scalAlg S ≥ 0` and components bounded by `Cm · scalAlg S`, `Cm ≥ 0`,

`|Ric₀ S ᵢⱼ| ≤ (n · Cm + 1) · scalAlg S`.

The index `i` only serves to provide the inequality `1 ≤ n` (there is nothing to prove for
`Fin 0`). -/
private lemma abs_ric0_le {S : Curv4 n} {Cm : ℝ}
    (hCm : ∀ p q r s : Fin n, |S p q r s| ≤ Cm * scalAlg S) (hσ : 0 ≤ scalAlg S)
    (i p q : Fin n) :
    |ric0 S p q| ≤ ((n : ℝ) * Cm + 1) * scalAlg S := by
  have hn1nat : 1 ≤ n := by have := i.isLt; omega
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1nat
  have hn0 : (0 : ℝ) < (n : ℝ) := lt_of_lt_of_le zero_lt_one hn1
  have hric := abs_ric_le (n := n) hCm p q
  have hid : |scalAlg S / (n : ℝ) * id2 n p q| ≤ scalAlg S := by
    have h2 : 0 ≤ scalAlg S / (n : ℝ) := div_nonneg hσ hn0.le
    rw [abs_mul, abs_of_nonneg h2]
    have hδ : |id2 n p q| ≤ 1 := abs_id2_le_one p q
    have h1 : scalAlg S / (n : ℝ) ≤ scalAlg S := by
      rw [div_le_iff₀ hn0]
      nlinarith
    calc scalAlg S / (n : ℝ) * |id2 n p q|
        ≤ scalAlg S / (n : ℝ) * 1 := mul_le_mul_of_nonneg_left hδ h2
      _ = scalAlg S / (n : ℝ) := by ring
      _ ≤ scalAlg S := h1
  simp only [ric0]
  calc |ric S p q - scalAlg S / (n : ℝ) * id2 n p q|
      ≤ |ric S p q| + |scalAlg S / (n : ℝ) * id2 n p q| := abs_sub _ _
    _ ≤ (n : ℝ) * (Cm * scalAlg S) + scalAlg S := add_le_add hric hid
    _ = ((n : ℝ) * Cm + 1) * scalAlg S := by ring

/-- Component bound for `Ric₀ ∧ id`: with the hypotheses of `abs_ric0_le` and `Cm ≥ 0`,
`|(Ric₀ ∧ id)ᵢⱼₖₗ| ≤ 4 · ((n · Cm + 1) · scalAlg S)`. -/
private lemma abs_knProd_ric0_id2_le {S : Curv4 n} {Cm : ℝ} (hCm0 : 0 ≤ Cm)
    (hCm : ∀ p q r s : Fin n, |S p q r s| ≤ Cm * scalAlg S) (hσ : 0 ≤ scalAlg S)
    (i j k l : Fin n) :
    |knProd (ric0 S) (id2 n) i j k l| ≤ 4 * (((n : ℝ) * Cm + 1) * scalAlg S) := by
  have hX0 : 0 ≤ ((n : ℝ) * Cm + 1) * scalAlg S := by
    refine mul_nonneg ?_ hσ
    have : 0 ≤ (n : ℝ) * Cm := mul_nonneg (Nat.cast_nonneg n) hCm0
    linarith
  have e1 : |ric0 S i k * id2 n j l| ≤ ((n : ℝ) * Cm + 1) * scalAlg S := by
    rw [abs_mul]
    calc |ric0 S i k| * |id2 n j l|
        ≤ (((n : ℝ) * Cm + 1) * scalAlg S) * 1 :=
          mul_le_mul (abs_ric0_le hCm hσ i i k) (abs_id2_le_one j l) (abs_nonneg _) hX0
      _ = ((n : ℝ) * Cm + 1) * scalAlg S := by ring
  have e2 : |ric0 S i l * id2 n j k| ≤ ((n : ℝ) * Cm + 1) * scalAlg S := by
    rw [abs_mul]
    calc |ric0 S i l| * |id2 n j k|
        ≤ (((n : ℝ) * Cm + 1) * scalAlg S) * 1 :=
          mul_le_mul (abs_ric0_le hCm hσ i i l) (abs_id2_le_one j k) (abs_nonneg _) hX0
      _ = ((n : ℝ) * Cm + 1) * scalAlg S := by ring
  have e3 : |ric0 S j k * id2 n i l| ≤ ((n : ℝ) * Cm + 1) * scalAlg S := by
    rw [abs_mul]
    calc |ric0 S j k| * |id2 n i l|
        ≤ (((n : ℝ) * Cm + 1) * scalAlg S) * 1 :=
          mul_le_mul (abs_ric0_le hCm hσ i j k) (abs_id2_le_one i l) (abs_nonneg _) hX0
      _ = ((n : ℝ) * Cm + 1) * scalAlg S := by ring
  have e4 : |ric0 S j l * id2 n i k| ≤ ((n : ℝ) * Cm + 1) * scalAlg S := by
    rw [abs_mul]
    calc |ric0 S j l| * |id2 n i k|
        ≤ (((n : ℝ) * Cm + 1) * scalAlg S) * 1 :=
          mul_le_mul (abs_ric0_le hCm hσ i j l) (abs_id2_le_one i k) (abs_nonneg _) hX0
      _ = ((n : ℝ) * Cm + 1) * scalAlg S := by ring
  have hexp : knProd (ric0 S) (id2 n) i j k l
      = ric0 S i k * id2 n j l - ric0 S i l * id2 n j k
        - ric0 S j k * id2 n i l + ric0 S j l * id2 n i k := rfl
  rw [hexp]
  refine (abs_sub_sub_add_le _ _ _ _).trans ?_
  linarith

/-! ## The main statement -/

theorem knProd_ric0_norm_bound (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ S : Submission.Diff.Alg.Curv4 n, Submission.Diff.Alg.IsAlgCurv S →
      Submission.Diff.Alg.InPIC2 S →
      ‖Work.Diff.Alg.Pinch.knProd (Work.Diff.Alg.Pinch.ric0 S) (Work.Diff.Alg.Pinch.id2 n)‖
        ≤ C * Submission.Diff.Alg.scalAlg S := by
  obtain ⟨Cm, hCm⟩ := (inPIC2_comp_bound n).1
  set Cm' : ℝ := max Cm 0 with hCm'def
  have hCm'0 : 0 ≤ Cm' := le_max_right _ _
  have hComp : ∀ S : Curv4 n, InPIC2 S → ∀ p q r s : Fin n, |S p q r s| ≤ Cm' * scalAlg S := by
    intro S hS p q r s
    have hσ : 0 ≤ scalAlg S := (inPIC2_metric_basic n).2.2 S hS
    exact (hCm S hS p q r s).trans (mul_le_mul_of_nonneg_right (le_max_left Cm 0) hσ)
  refine ⟨4 * ((n : ℝ) * Cm' + 1), ?_, ?_⟩
  · have hnCm' : 0 ≤ (n : ℝ) * Cm' := mul_nonneg (Nat.cast_nonneg n) hCm'0
    nlinarith
  · intro S _ hPIC
    have hσ : 0 ≤ scalAlg S := (inPIC2_metric_basic n).2.2 S hPIC
    have hC : 0 ≤ 4 * ((n : ℝ) * Cm' + 1) := by
      have hnCm' : 0 ≤ (n : ℝ) * Cm' := mul_nonneg (Nat.cast_nonneg n) hCm'0
      nlinarith
    refine norm_le_of_components (mul_nonneg hC hσ) ?_
    intro i j k l
    calc |knProd (ric0 S) (id2 n) i j k l|
        ≤ 4 * (((n : ℝ) * Cm' + 1) * scalAlg S) :=
          abs_knProd_ric0_id2_le hCm'0 (hComp S hPIC) hσ i j k l
      _ = (4 * ((n : ℝ) * Cm' + 1)) * scalAlg S := by ring

end Work.Diff.Alg.Pinch.ChatShift
