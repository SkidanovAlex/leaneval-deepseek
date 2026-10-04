import Mathlib
import Submission.Work.Diff.Alg.Pinch.Defs
import Submission.Work.Diff.Alg.Pinch.inPIC2_comp_bound
import Submission.Work.Diff.Alg.Pinch.inPIC2_metric_basic

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Component bound for `R + (1/2)·(Ric₀(R) ∧ id)`

Brendle–Schoen's convergence argument for the Ricci flow uses the decomposition of the curvature
tensor into its `Ĉ`-part (the `(1/2)·Ric₀(R) ∧ id` correction) and its complement; every estimate
is against the scalar curvature, so one needs a *scale-invariant component bound*

`|(R + (1/2)·(Ric₀(R) ∧ id))ᵢⱼₖₗ| ≤ C · scalAlg R`

for all `i j k l`, valid for every tensor with nonnegative complex sectional curvature (no
algebraic-curvature hypothesis is needed).

The proof is bookkeeping on top of `inPIC2_comp_bound`, which already gives `|Rᵢⱼₖₗ| ≤ D·scalAlg R`
for some constant `D ≥ 0`, together with `scalAlg R ≥ 0` (`inPIC2_metric_basic`).  From these:

* `|Ric(R)ᵢⱼ| ≤ n·D·scalAlg R` (a sum of `n` components),
* hence `|Ric₀(R)ᵢⱼ| = |Ric(R)ᵢⱼ - (scalAlg R/n)·δᵢⱼ| ≤ (n·D + 1)·scalAlg R`
  (using `scalAlg R / n ≤ scalAlg R`, which holds for `n ≥ 0` when `scalAlg R ≥ 0`),
* hence `|(Ric₀(R) ∧ id)ᵢⱼₖₗ| ≤ 4·(n·D + 1)·scalAlg R` (four products with `|δ| ≤ 1`),
* and finally `C = D + 2·(n·D + 1)`.
-/

namespace Work.Diff.Alg.Pinch

open Finset Submission.Diff.Alg

variable {n : ℕ}

/-- For `n ≥ 0` in `ℝ` and `x ≥ 0`, division by `n` does not increase `x`. -/
private lemma div_natCast_le_self {x : ℝ} (hx : 0 ≤ x) (m : ℕ) : x / (m : ℝ) ≤ x := by
  rcases Nat.eq_zero_or_pos m with h | h
  · simp only [h, Nat.cast_zero, div_zero]; exact hx
  · have hn : (1 : ℝ) ≤ m := by exact_mod_cast h
    have hpos : (0 : ℝ) < (m : ℝ) := by linarith
    rw [div_le_iff₀ hpos]
    nlinarith

/-- The Ricci tensor of a tensor whose components are bounded by `D · scalAlg R` is bounded by
`n · (D · scalAlg R)`. -/
private lemma ric_abs_le {R : Curv4 n} {D : ℝ}
    (hD : ∀ i j k l, |R i j k l| ≤ D * scalAlg R) (i j : Fin n) :
    |ric R i j| ≤ (n : ℝ) * (D * scalAlg R) := by
  have h : |∑ k : Fin n, R k i k j| ≤ ∑ k : Fin n, D * scalAlg R := by
    refine le_trans (Finset.abs_sum_le_sum_abs (fun k : Fin n => R k i k j) Finset.univ) ?_
    exact Finset.sum_le_sum (fun k _ => hD k i k j)
  have h2 : (∑ k : Fin n, D * scalAlg R) = (n : ℝ) * (D * scalAlg R) := by
    simp [Finset.sum_const, Finset.card_univ, mul_left_comm]
  simpa [ric, h2] using h

/-- Traceless Ricci bound: `|Ric₀(R)ᵢⱼ| ≤ (n·D + 1)·scalAlg R`. -/
private lemma ric0_abs_le {R : Curv4 n} {D : ℝ} (hscal : 0 ≤ scalAlg R)
    (hD : ∀ i j k l, |R i j k l| ≤ D * scalAlg R) (i j : Fin n) :
    |ric0 R i j| ≤ ((n : ℝ) * D + 1) * scalAlg R := by
  have hric : |ric R i j| ≤ (n : ℝ) * (D * scalAlg R) := ric_abs_le hD i j
  have hid : |id2 n i j| ≤ 1 := by
    simp only [id2]; split <;> norm_num
  have hq : 0 ≤ scalAlg R / (n : ℝ) := div_nonneg hscal (Nat.cast_nonneg n)
  have h1 : |(scalAlg R / (n : ℝ)) * id2 n i j| ≤ scalAlg R := by
    rw [abs_mul, abs_of_nonneg hq]
    calc scalAlg R / (n : ℝ) * |id2 n i j| ≤ scalAlg R / (n : ℝ) * 1 :=
          mul_le_mul_of_nonneg_left hid hq
      _ = scalAlg R / (n : ℝ) := by ring
      _ ≤ scalAlg R := div_natCast_le_self hscal n
  have hue : ric0 R i j = ric R i j - (scalAlg R / (n : ℝ)) * id2 n i j := rfl
  calc |ric0 R i j| = |ric R i j - (scalAlg R / (n : ℝ)) * id2 n i j| := by rw [hue]
    _ ≤ |ric R i j| + |(scalAlg R / (n : ℝ)) * id2 n i j| := abs_sub _ _
    _ ≤ (n : ℝ) * (D * scalAlg R) + scalAlg R := add_le_add hric h1
    _ = ((n : ℝ) * D + 1) * scalAlg R := by ring

/-- Kulkarni–Nomizu bound: `|(Ric₀(R) ∧ id)ᵢⱼₖₗ| ≤ 4·(n·D + 1)·scalAlg R`. -/
private lemma knProd_ric0_id2_abs_le {R : Curv4 n} {D : ℝ} (hD0 : 0 ≤ D)
    (hscal : 0 ≤ scalAlg R) (hD : ∀ i j k l, |R i j k l| ≤ D * scalAlg R) (i j k l : Fin n) :
    |knProd (ric0 R) (id2 n) i j k l| ≤ 4 * (((n : ℝ) * D + 1) * scalAlg R) := by
  have hBn : (0 : ℝ) ≤ (n : ℝ) * D + 1 := by
    have := Nat.cast_nonneg (α := ℝ) n; nlinarith
  have hr : ∀ a b : Fin n, |ric0 R a b| ≤ ((n : ℝ) * D + 1) * scalAlg R :=
    fun a b => ric0_abs_le hscal hD a b
  have hi : ∀ a b : Fin n, |id2 n a b| ≤ 1 := by
    intro a b; simp only [id2]; split <;> norm_num
  have ht : ∀ a b c d : Fin n,
      |ric0 R a b * id2 n c d| ≤ ((n : ℝ) * D + 1) * scalAlg R := by
    intro a b c d
    calc |ric0 R a b * id2 n c d| = |ric0 R a b| * |id2 n c d| := abs_mul _ _
      _ ≤ |ric0 R a b| * 1 := mul_le_mul_of_nonneg_left (hi c d) (abs_nonneg _)
      _ = |ric0 R a b| := by ring
      _ ≤ ((n : ℝ) * D + 1) * scalAlg R := hr a b
  have h1 := ht i k j l; have h2 := ht i l j k
  have h3 := ht j k i l; have h4 := ht j l i k
  have hexp : knProd (ric0 R) (id2 n) i j k l
      = ric0 R i k * id2 n j l - ric0 R i l * id2 n j k
        - ric0 R j k * id2 n i l + ric0 R j l * id2 n i k := rfl
  rw [hexp, abs_le]
  constructor <;> linarith [abs_le.mp h1, abs_le.mp h2, abs_le.mp h3, abs_le.mp h4]

/-- `inPIC2_comp_bound` with an explicitly nonnegative constant. -/
private lemma comp_bound_nonneg (n : ℕ) :
    ∃ D : ℝ, 0 ≤ D ∧
      ∀ R : Curv4 n, InPIC2 R → ∀ i j k l, |R i j k l| ≤ D * scalAlg R := by
  obtain ⟨C, hC⟩ := (inPIC2_comp_bound n).1
  refine ⟨max C 2, le_trans (by norm_num : (0 : ℝ) ≤ 2) (le_max_right _ _), ?_⟩
  intro R hR i j k l
  have hscal : 0 ≤ scalAlg R := (inPIC2_metric_basic n).2.2 R hR
  have h1 := hC R hR i j k l
  have hle : C * scalAlg R ≤ max C 2 * scalAlg R :=
    mul_le_mul_of_nonneg_right (le_max_left _ _) hscal
  linarith

theorem Chat_err_comp_bound (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ R : Submission.Diff.Alg.Curv4 n, Submission.Diff.Alg.InPIC2 R →
      ∀ i j k l : Fin n,
        |(R + (1 / 2 : ℝ) • Work.Diff.Alg.Pinch.knProd (Work.Diff.Alg.Pinch.ric0 R)
            (Work.Diff.Alg.Pinch.id2 n)) i j k l|
          ≤ C * Submission.Diff.Alg.scalAlg R := by
  obtain ⟨D, hD0, hD⟩ := comp_bound_nonneg n
  refine ⟨D + 2 * ((n : ℝ) * D + 1), ?_, ?_⟩
  · have := Nat.cast_nonneg (α := ℝ) n; nlinarith
  · intro R hR i j k l
    have hscal : 0 ≤ scalAlg R := (inPIC2_metric_basic n).2.2 R hR
    have hR' := hD R hR
    have hK : |knProd (ric0 R) (id2 n) i j k l| ≤ 4 * (((n : ℝ) * D + 1) * scalAlg R) :=
      knProd_ric0_id2_abs_le hD0 hscal hR' i j k l
    have hexp : (R + (1 / 2 : ℝ) • knProd (ric0 R) (id2 n)) i j k l
        = R i j k l + (1 / 2 : ℝ) * knProd (ric0 R) (id2 n) i j k l := by
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [hexp, abs_le]
    have h1 := abs_le.mp (hR' i j k l)
    have h2 := abs_le.mp hK
    constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]

end Work.Diff.Alg.Pinch
