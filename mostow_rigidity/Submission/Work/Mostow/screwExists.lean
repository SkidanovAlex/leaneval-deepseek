import Mathlib
import Submission.Work.Mostow.geodDeps

namespace Work.Mostow

/-!
# The Dirichlet screw (`screwExists`)

Given a finite angle group `A ≤ (ℝ/2πℤ)^r`, a "screw" translation `ψ` of the torus, weights
`ρ i > 0` and a scale `δ > 0` which is a *minimal* weighted chord length of a non-zero element of
`A`, the pigeonhole count `dirichletBox` produces an element `j • ψ + a` (`1 ≤ j ≤ J`, `a ∈ A`) of
weighted chord-length `≤ δ` (indeed `≤ δ/2`), whose translation length `j * T` is bounded by
`δ / W`.

The only input beyond `dirichletBox` is the elementary bound `chord x = 2 sin(‖x‖/2) ≤ ‖x‖`, which
turns "all coordinates `< α i = δ/(2√r ρ i)`" into "weighted chord-square `< δ²/4`".
-/

private lemma screw_chord_sq_le_norm_sq (x : AddCircle (2 * Real.pi)) :
    (Submission.Mostow.chord x) ^ 2 ≤ ‖x‖ ^ 2 := by
  rw [sq_le_sq, Submission.Mostow.chord, abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2),
      abs_of_nonneg (norm_nonneg x)]
  have := Real.abs_sin_le_abs (x := ‖x‖ / 2)
  rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ ‖x‖ / 2)] at this
  linarith

/-- If every coordinate of `x` has norm at most `δ/(2√r ρ i)`, then the weighted sum of squared
chords of `x` is at most `δ²/4`. -/
private lemma screw_sum_le (r : ℕ) (hr : 0 < r) (δ : ℝ) (hδ : 0 < δ) (ρ : Fin r → ℝ)
    (hρ : ∀ i, 0 < ρ i) (x : Fin r → AddCircle (2 * Real.pi))
    (hx : ∀ i, ‖x i‖ ≤ δ / (2 * Real.sqrt (r : ℝ) * ρ i)) :
    ∑ i, (ρ i) ^ 2 * (Submission.Mostow.chord (x i)) ^ 2 ≤ δ ^ 2 / 4 := by
  have hrR : (0 : ℝ) < (r : ℝ) := Nat.cast_pos.mpr hr
  have hterm : ∀ i, (ρ i) ^ 2 * (Submission.Mostow.chord (x i)) ^ 2 ≤ δ ^ 2 / (4 * (r : ℝ)) := by
    intro i
    have h2 : (Submission.Mostow.chord (x i)) ^ 2
        ≤ (δ / (2 * Real.sqrt (r : ℝ) * ρ i)) ^ 2 :=
      le_trans (screw_chord_sq_le_norm_sq (x i)) (pow_le_pow_left₀ (norm_nonneg _) (hx i) 2)
    have h3 : (ρ i) ^ 2 * (δ / (2 * Real.sqrt (r : ℝ) * ρ i)) ^ 2 = δ ^ 2 / (4 * (r : ℝ)) := by
      rw [div_pow]
      have hsq : (Real.sqrt (r : ℝ)) ^ 2 = (r : ℝ) := Real.sq_sqrt (le_of_lt hrR)
      have hden2 : (2 * Real.sqrt (r : ℝ) * ρ i) ^ 2 = 4 * (r : ℝ) * (ρ i) ^ 2 := by
        rw [mul_pow, mul_pow, hsq]; ring
      rw [hden2]
      field_simp [ne_of_gt (hρ i), ne_of_gt hrR]
    calc (ρ i) ^ 2 * (Submission.Mostow.chord (x i)) ^ 2
        ≤ (ρ i) ^ 2 * (δ / (2 * Real.sqrt (r : ℝ) * ρ i)) ^ 2 :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = δ ^ 2 / (4 * (r : ℝ)) := h3
  calc ∑ i, (ρ i) ^ 2 * (Submission.Mostow.chord (x i)) ^ 2
      ≤ ∑ _i : Fin r, δ ^ 2 / (4 * (r : ℝ)) := Finset.sum_le_sum (fun i _ => hterm i)
    _ = (r : ℝ) * (δ ^ 2 / (4 * (r : ℝ))) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    _ = δ ^ 2 / 4 := by field_simp

theorem screwExists (r : ℕ) (hr : 0 < r) (T δ W : ℝ) (hT : 0 < T) (hδ : 0 < δ) (hW : 0 < W)
    (ψ : Fin r → AddCircle (2 * Real.pi))
    (A : AddSubgroup (Fin r → AddCircle (2 * Real.pi))) [Finite A]
    (ρ : Fin r → ℝ) (hρ : ∀ i, 0 < ρ i) (J : ℕ)
    (hJT : (J : ℝ) * T ≤ δ / W)
    (hsm : ∀ i, δ ≤ 2 * Real.pi * (2 * Real.sqrt (r : ℝ) * ρ i))
    (hmin : ∀ a ∈ A, a ≠ 0 → δ ^ 2 ≤ ∑ i, (ρ i) ^ 2 * (Submission.Mostow.chord (a i)) ^ 2)
    (hcount : ∏ i, ⌈2 * Real.pi / (δ / (2 * Real.sqrt (r : ℝ) * ρ i))⌉₊ < (J + 1) * Nat.card A) :
    ∃ j : ℕ, 1 ≤ j ∧ j ≤ J ∧ ∃ a ∈ A, (j : ℝ) * T ≤ δ / W ∧
      ∑ i, (ρ i) ^ 2 * (Submission.Mostow.chord ((j • ψ + a) i)) ^ 2 ≤ δ ^ 2 := by
  classical
  have hrR : (0 : ℝ) < (r : ℝ) := Nat.cast_pos.mpr hr
  have hden : ∀ i, 0 < 2 * Real.sqrt (r : ℝ) * ρ i := fun i =>
    mul_pos (mul_pos two_pos (Real.sqrt_pos.mpr hrR)) (hρ i)
  -- the combinatorial pigeonhole, with the box size `α i = δ / (2 √r ρ i)`
  obtain ⟨j, hj1, hjJ, a, haA, hsmall⟩ :=
    dirichletBox r A ψ (fun i => δ / (2 * Real.sqrt (r : ℝ) * ρ i)) J
      (fun i => ⟨div_pos hδ (hden i), (div_le_iff₀ (hden i)).mpr (hsm i)⟩)
      (by
        -- a non-zero `a` with all coordinates `< α i` would have weighted chord-square `< δ²`
        intro a haA ha
        by_contra hne
        have hmin_a := hmin a haA hne
        have hle := screw_sum_le r hr δ hδ ρ hρ a (fun i => le_of_lt (ha i))
        nlinarith [hδ, hmin_a, hle])
      hcount
  refine ⟨j, hj1, hjJ, a, haA, ?_, ?_⟩
  · have hjJR : (j : ℝ) ≤ (J : ℝ) := by exact_mod_cast hjJ
    nlinarith [hT, hJT]
  · have hle := screw_sum_le r hr δ hδ ρ hρ (fun i => (j • ψ + a) i) (fun i => by
      have := hsmall i
      simpa using le_of_lt this)
    calc ∑ i, (ρ i) ^ 2 * (Submission.Mostow.chord ((j • ψ + a) i)) ^ 2 ≤ δ ^ 2 / 4 := hle
      _ ≤ δ ^ 2 := by nlinarith [hδ, sq_nonneg δ]

end Work.Mostow
