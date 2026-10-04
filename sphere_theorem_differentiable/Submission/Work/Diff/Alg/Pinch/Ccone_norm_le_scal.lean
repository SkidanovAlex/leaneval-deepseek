import Mathlib
import Submission.Work.Diff.Alg.Pinch.Ccone_transversal_a_aux
import Submission.Work.Diff.Alg.Pinch.inPIC2_comp_bound
import Submission.Work.Diff.Alg.Pinch.Linv
import Submission.Work.Diff.Alg.Pinch.inPIC2_metric_basic
import Submission.Work.Diff.Alg.Pinch.Defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# `‖R‖ ≤ C · scal R` on the Böhm–Wilking cones `Ccone a b p`

The cones of the Böhm–Wilking construction are `Ccone a b p = ℓ_{a,b} '' Dpic p`, where
`Dpic p = {R | IsAlgCurv R ∧ InPIC2 R ∧ RicPinch p R}` is the "pinched" cone (nonnegative complex
sectional curvature plus a Ricci pinching).  The point of this file is that such a cone has *uniformly
bounded shape*: there is a constant `C > 0` (depending only on `n, a, b`) with

`‖R‖ ≤ C * scalAlg R`     for every `R ∈ Ccone a b p`.

This is what makes the cones usable as a closed family of "model geometries": it bounds the
Euclidean norm of the curvature tensor by its scalar curvature, so that a tensor in the cone cannot
be wild while having small scalar curvature.

## Proof

Write `R = ℓ_{a,b} S` with `S ∈ Dpic p`.  Since `InPIC2 S`, the componentwise bound
`|Sᵢⱼₖₗ| ≤ C₀ · scal S` holds (`Work.Diff.Alg.Pinch.inPIC2_comp_bound`, which does not even need the
algebraic-curvature hypothesis), and `scal S ≥ 0` (`Work.Diff.Alg.Pinch.inPIC2_metric_basic`).
Expanding `ℓ_{a,b} S = S + b • (Ric₀ S ∧ id) + (a/n · scal S) • (id ∧ id)` componentwise gives

`|ℓ_{a,b} S ᵢⱼₖₗ| ≤ (C₀ + 4|b|(n C₀ + 1/n) + 4a/n) · scal S`,

because `|Ric₀ S| ≤ n C₀ · scal S + scal S / n`, every entry of `id2` has absolute value at most `1`,
and `(Ric₀ ∧ id)`, `(id ∧ id)` have four products each.  Finally
`scal (ℓ_{a,b} S) = (1 + 2(n-1)a) · scal S` (`Work.Diff.Alg.Pinch.scalAlg_ell`), and
`1 + 2(n-1)a ≥ 1 > 0` because `a ≥ 0` and `n ≥ 2`; dividing the bound by that factor concludes.
-/

namespace Work.Diff.Alg.Pinch

open Finset Submission.Diff.Alg

variable {n : ℕ}

/-! ## Elementary triangle inequalities and componentwise norm bounds -/

/-- Every entry of the identity `2`-tensor `id2 n` has absolute value at most `1`. -/
private lemma abs_id2_le_one (i j : Fin n) : |id2 n i j| ≤ 1 := by
  rw [id2]; split <;> simp

/-- Triangle inequality for three summands. -/
private lemma abs_add_three_le (A B C : ℝ) : |A + B + C| ≤ |A| + |B| + |C| := by
  have h1 : |A + B + C| ≤ |A + B| + |C| := abs_add_le _ _
  have h2 : |A + B| ≤ |A| + |B| := abs_add_le _ _
  linarith

/-- Triangle inequality for the Kulkarni–Nomizu pattern `A - B - C + D`. -/
private lemma abs_sub_sub_add_le (A B C D : ℝ) : |A - B - C + D| ≤ |A| + |B| + |C| + |D| := by
  have h1 : |A - B - C + D| ≤ |A - B - C| + |D| := abs_add_le _ _
  have h2 : |A - B - C| ≤ |A - B| + |C| := abs_sub _ _
  have h3 : |A - B| ≤ |A| + |B| := abs_sub _ _
  linarith

/-- A `4`-index array is bounded in norm as soon as its components are bounded by a nonnegative
constant. -/
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

/-! ## The componentwise bound for `ell a b` -/

/-- Componentwise bound for the Böhm–Wilking transform of a `PIC2` tensor: if every component of
`S` is bounded by `Cm * scalAlg S` (with `Cm ≥ 0`) then

`|(ℓ_{a,b} S)ᵢⱼₖₗ| ≤ (Cm + 4|b|(n·Cm + 1/n) + 4a/n) · scalAlg S`  for `a ≥ 0`. -/
private lemma ell_comp_abs_le (n : ℕ) (hn : 2 ≤ n) (a b : ℝ) (ha : 0 ≤ a) (Cm : ℝ)
    (hCm0 : 0 ≤ Cm)
    (hCb : ∀ S : Curv4 n, InPIC2 S → ∀ p q r s, |S p q r s| ≤ Cm * scalAlg S)
    {S : Curv4 n} (hS : InPIC2 S) (i j k l : Fin n) :
    |ell a b S i j k l| ≤ (Cm + 4 * |b| * ((n : ℝ) * Cm + 1 / (n : ℝ)) + 4 * (a / (n : ℝ)))
      * scalAlg S := by
  have hn0 : (0 : ℝ) < (n : ℝ) := by
    have h2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  have hσ : 0 ≤ scalAlg S := (inPIC2_metric_basic n).2.2 S hS
  have hE0 : 0 ≤ (n : ℝ) * Cm + 1 / (n : ℝ) :=
    add_nonneg (mul_nonneg (Nat.cast_nonneg n) hCm0) (div_nonneg zero_le_one hn0.le)
  have hEσ : 0 ≤ ((n : ℝ) * Cm + 1 / (n : ℝ)) * scalAlg S := mul_nonneg hE0 hσ
  -- bound on the Ricci tensor
  have hric0 : ∀ p q : Fin n, |ric0 S p q| ≤ ((n : ℝ) * Cm + 1 / (n : ℝ)) * scalAlg S := by
    intro p q
    have h1 : |ric S p q| ≤ (n : ℝ) * (Cm * scalAlg S) := by
      rw [ric]
      calc |∑ k, S k p k q| ≤ ∑ k, |S k p k q| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _k : Fin n, Cm * scalAlg S := Finset.sum_le_sum (fun k _ => hCb S hS k p k q)
        _ = (n : ℝ) * (Cm * scalAlg S) := by
              rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have h2 : |(scalAlg S / (n : ℝ)) * id2 n p q| ≤ (1 / (n : ℝ)) * scalAlg S := by
      rw [abs_mul, abs_of_nonneg (div_nonneg hσ hn0.le)]
      have hid : |id2 n p q| ≤ 1 := abs_id2_le_one p q
      have h4 : scalAlg S / (n : ℝ) * |id2 n p q| ≤ scalAlg S / (n : ℝ) * 1 :=
        mul_le_mul_of_nonneg_left hid (div_nonneg hσ hn0.le)
      calc scalAlg S / (n : ℝ) * |id2 n p q| ≤ scalAlg S / (n : ℝ) := by linarith
        _ = (1 / (n : ℝ)) * scalAlg S := by ring
    simp only [ric0]
    calc |ric S p q - scalAlg S / (n : ℝ) * id2 n p q|
        ≤ |ric S p q| + |scalAlg S / (n : ℝ) * id2 n p q| := abs_sub _ _
      _ ≤ (n : ℝ) * (Cm * scalAlg S) + (1 / (n : ℝ)) * scalAlg S := add_le_add h1 h2
      _ = ((n : ℝ) * Cm + 1 / (n : ℝ)) * scalAlg S := by ring
  -- bound on `Ric₀ ∧ id`
  have hkn1 : |knProd (ric0 S) (id2 n) i j k l|
      ≤ 4 * (((n : ℝ) * Cm + 1 / (n : ℝ)) * scalAlg S) := by
    have hterm : ∀ p q r s : Fin n,
        |ric0 S p q * id2 n r s| ≤ ((n : ℝ) * Cm + 1 / (n : ℝ)) * scalAlg S := by
      intro p q r s
      rw [abs_mul]
      have hid : |id2 n r s| ≤ 1 := abs_id2_le_one r s
      calc |ric0 S p q| * |id2 n r s|
          ≤ (((n : ℝ) * Cm + 1 / (n : ℝ)) * scalAlg S) * 1 :=
            mul_le_mul (hric0 p q) hid (abs_nonneg _) hEσ
        _ = ((n : ℝ) * Cm + 1 / (n : ℝ)) * scalAlg S := by ring
    have h1 := hterm i k j l
    have h2 := hterm i l j k
    have h3 := hterm j k i l
    have h4 := hterm j l i k
    simp only [knProd]
    refine (abs_sub_sub_add_le _ _ _ _).trans ?_
    linarith
  -- bound on `id ∧ id`
  have hkn2 : |knProd (id2 n) (id2 n) i j k l| ≤ 4 := by
    have hterm : ∀ p q r s : Fin n, |id2 n p q * id2 n r s| ≤ 1 := by
      intro p q r s
      rw [abs_mul]
      calc |id2 n p q| * |id2 n r s| ≤ 1 * 1 :=
            mul_le_mul (abs_id2_le_one p q) (abs_id2_le_one r s) (abs_nonneg _) (by norm_num)
        _ = 1 := by norm_num
    have h1 := hterm i k j l
    have h2 := hterm i l j k
    have h3 := hterm j k i l
    have h4 := hterm j l i k
    simp only [knProd]
    refine (abs_sub_sub_add_le _ _ _ _).trans ?_
    linarith
  -- assemble
  have hb1 : |b * knProd (ric0 S) (id2 n) i j k l|
      ≤ |b| * (4 * (((n : ℝ) * Cm + 1 / (n : ℝ)) * scalAlg S)) := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left hkn1 (abs_nonneg b)
  have ha1 : |(a / (n : ℝ) * scalAlg S) * knProd (id2 n) (id2 n) i j k l|
      ≤ (a / (n : ℝ) * scalAlg S) * 4 := by
    rw [abs_mul, abs_of_nonneg (mul_nonneg (div_nonneg ha hn0.le) hσ)]
    exact mul_le_mul_of_nonneg_left hkn2 (mul_nonneg (div_nonneg ha hn0.le) hσ)
  have h0 : |S i j k l| ≤ Cm * scalAlg S := hCb S hS i j k l
  have hexp : ell a b S i j k l = S i j k l + b * knProd (ric0 S) (id2 n) i j k l
      + (a / (n : ℝ) * scalAlg S) * knProd (id2 n) (id2 n) i j k l := by
    simp only [ell, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [hexp]
  refine (abs_add_three_le _ _ _).trans ?_
  calc |S i j k l| + |b * knProd (ric0 S) (id2 n) i j k l|
        + |(a / (n : ℝ) * scalAlg S) * knProd (id2 n) (id2 n) i j k l|
      ≤ Cm * scalAlg S + |b| * (4 * (((n : ℝ) * Cm + 1 / (n : ℝ)) * scalAlg S))
        + (a / (n : ℝ) * scalAlg S) * 4 := by linarith
    _ = (Cm + 4 * |b| * ((n : ℝ) * Cm + 1 / (n : ℝ)) + 4 * (a / (n : ℝ))) * scalAlg S := by
        ring

/-! ## The main statement -/

theorem Ccone_norm_le_scal (n : ℕ) (hn : 2 ≤ n) (a b p : ℝ) (ha : 0 ≤ a) :
    ∃ C : ℝ, 0 < C ∧ ∀ R : Submission.Diff.Alg.Curv4 n,
      R ∈ Work.Diff.Alg.Pinch.Ccone (n := n) a b p → ‖R‖ ≤ C * Submission.Diff.Alg.scalAlg R := by
  obtain ⟨Cm, hCm⟩ := (inPIC2_comp_bound n).1
  have hCb : ∀ S : Curv4 n, InPIC2 S → ∀ p q r s, |S p q r s| ≤ max Cm 0 * scalAlg S := by
    intro S hS p q r s
    have hσ : 0 ≤ scalAlg S := (inPIC2_metric_basic n).2.2 S hS
    exact (hCm S hS p q r s).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hσ)
  have hCm0 : 0 ≤ max Cm 0 := le_max_right _ _
  have hn0 : (0 : ℝ) < (n : ℝ) := by
    have h2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  have hden : 0 < 1 + 2 * ((n : ℝ) - 1) * a := by
    have h2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    nlinarith [ha, h2]
  refine ⟨max (max Cm 0 + 4 * |b| * ((n : ℝ) * max Cm 0 + 1 / (n : ℝ))
      + 4 * (a / (n : ℝ))) 1 / (1 + 2 * ((n : ℝ) - 1) * a),
    div_pos (lt_of_lt_of_le one_pos (le_max_right _ _)) hden, ?_⟩
  intro R hR
  obtain ⟨S, hS, hSR⟩ := hR
  have hσ : 0 ≤ scalAlg S := (inPIC2_metric_basic n).2.2 S hS.2.1
  have hscalR : scalAlg R = (1 + 2 * ((n : ℝ) - 1) * a) * scalAlg S := by
    rw [← hSR, scalAlg_ell]
  have hscalR0 : 0 ≤ scalAlg R := by
    rw [hscalR]; exact mul_nonneg hden.le hσ
  have hD0 : (1 + 2 * ((n : ℝ) - 1) * a) ≠ 0 := ne_of_gt hden
  have hcomp : ∀ i j k l : Fin n, |R i j k l|
      ≤ (max (max Cm 0 + 4 * |b| * ((n : ℝ) * max Cm 0 + 1 / (n : ℝ)) + 4 * (a / (n : ℝ))) 1
          / (1 + 2 * ((n : ℝ) - 1) * a)) * scalAlg R := by
    intro i j k l
    have h1 : |ell a b S i j k l|
        ≤ max (max Cm 0 + 4 * |b| * ((n : ℝ) * max Cm 0 + 1 / (n : ℝ)) + 4 * (a / (n : ℝ))) 1
          * scalAlg S :=
      (ell_comp_abs_le n hn a b ha (max Cm 0) hCm0 hCb hS.2.1 i j k l).trans
        (mul_le_mul_of_nonneg_right (le_max_left _ _) hσ)
    have h2 : max (max Cm 0 + 4 * |b| * ((n : ℝ) * max Cm 0 + 1 / (n : ℝ))
          + 4 * (a / (n : ℝ))) 1 * scalAlg S
        = (max (max Cm 0 + 4 * |b| * ((n : ℝ) * max Cm 0 + 1 / (n : ℝ)) + 4 * (a / (n : ℝ))) 1
            / (1 + 2 * ((n : ℝ) - 1) * a)) * scalAlg R := by
      rw [hscalR, ← mul_assoc, div_mul_cancel₀ _ hD0]
    calc |R i j k l| = |ell a b S i j k l| := by rw [← hSR]
      _ ≤ max (max Cm 0 + 4 * |b| * ((n : ℝ) * max Cm 0 + 1 / (n : ℝ)) + 4 * (a / (n : ℝ))) 1
            * scalAlg S := h1
      _ = _ := h2
  exact norm_le_of_components
    (mul_nonneg (div_pos (lt_of_lt_of_le one_pos (le_max_right _ _)) hden).le hscalR0) hcomp

end Work.Diff.Alg.Pinch
