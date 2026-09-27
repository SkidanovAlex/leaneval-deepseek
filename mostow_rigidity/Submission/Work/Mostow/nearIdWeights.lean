import Mathlib
import Submission.Work.Mostow.displacementBlocks

/-!
# Weights of a near-identity block rotation

`nearIdWeights` converts the *exact* block displacement identity of `displacementBlocks`

  `‖R Wz - Wz‖² = ∑ᵢ ‖Pᵢ Wz‖² · chord (φᵢ)²`

(where `Pᵢ` is the orthogonal projection onto the `i`-th rotation plane) into the *weighted*
estimate used by the GeodStrata/Dirichlet-box chapter, in which each block is weighted by
`max ‖Pᵢ Wz‖ ρ_` rather than by `‖Pᵢ Wz‖`:

  `∑ᵢ (max ‖Pᵢ Wz‖ ρ_)² · chord (φᵢ)² ≤ (2 sinh (η/2) + 4 η ρ_ √(m/2))²`.

The two extra ingredients are: (a) the chord of a circle angle is nonnegative, so the hypothesis
`chord (φᵢ) ≤ 4η` gives `chord (φᵢ)² ≤ (4η)²`; (b) for each block either `max = ‖Pᵢ Wz‖` (and the
contributions are dominated by the displacement) or `max = ρ_`, and then the whole block
contributes at most `ρ_² (4η)²`.  Summing the `m/2` blocks and expanding the square
`(A + ρ √(m/2) · 4η)² = A² + 2 A ρ √(m/2) 4η + ρ² (m/2) (4η)²` absorbs the second family.
-/

namespace Work.Mostow

open Submission.Mostow

/-- The chord `2 sin (‖x‖/2)` of an angle of the circle of circumference `2π` is nonnegative:
`‖x‖ ≤ π` is the distance of `x` to the origin, so `‖x‖/2 ∈ [0, π/2]`. -/
private lemma chord_nonneg_circle (x : AddCircle (2 * Real.pi)) :
    0 ≤ Submission.Mostow.chord x := by
  have hnorm : ‖x‖ ≤ Real.pi := by
    have h := AddCircle.norm_le_half_period (p := 2 * Real.pi) (x := x) (by positivity)
    rw [abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)] at h
    linarith
  have hs : 0 ≤ Real.sin (‖x‖ / 2) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (by positivity) (by linarith [Real.pi_pos])
  rw [Submission.Mostow.chord]
  nlinarith

/-- **Abstract weighted-chord bound.**  If `∑ᵢ aᵢ² cᵢ² ≤ A²` and `∑ᵢ cᵢ² ≤ B²`, then replacing
each weight `aᵢ` by `max aᵢ ρ` costs exactly one cross term `2 A ρ B`. -/
private lemma weightedMaxSum_le {r : ℕ} (a c : Fin r → ℝ) (ρ A B : ℝ)
    (hA : 0 ≤ A) (hρ : 0 ≤ ρ) (hB : 0 ≤ B)
    (hmain : ∑ i, (a i) ^ 2 * (c i) ^ 2 ≤ A ^ 2)
    (hbound : ∑ i, (c i) ^ 2 ≤ B ^ 2) :
    ∑ i, (max (a i) ρ) ^ 2 * (c i) ^ 2 ≤ (A + ρ * B) ^ 2 := by
  have hstep : ∑ i : Fin r, (max (a i) ρ) ^ 2 * (c i) ^ 2
      ≤ ∑ i : Fin r, ((a i) ^ 2 * (c i) ^ 2 + ρ ^ 2 * (c i) ^ 2) := by
    refine Finset.sum_le_sum (fun i _ => ?_)
    rcases le_total (a i) ρ with h | h
    · rw [max_eq_right h]
      nlinarith [mul_nonneg (sq_nonneg (a i)) (sq_nonneg (c i))]
    · rw [max_eq_left h]
      nlinarith [mul_nonneg (sq_nonneg ρ) (sq_nonneg (c i))]
  have harith : A ^ 2 + ρ ^ 2 * B ^ 2 ≤ (A + ρ * B) ^ 2 := by
    nlinarith [mul_nonneg (mul_nonneg hA hρ) hB]
  calc ∑ i : Fin r, (max (a i) ρ) ^ 2 * (c i) ^ 2
      ≤ ∑ i : Fin r, ((a i) ^ 2 * (c i) ^ 2 + ρ ^ 2 * (c i) ^ 2) := hstep
    _ = ∑ i : Fin r, (a i) ^ 2 * (c i) ^ 2 + ρ ^ 2 * ∑ i : Fin r, (c i) ^ 2 := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum]
    _ ≤ A ^ 2 + ρ ^ 2 * B ^ 2 := by
        have h2 := mul_le_mul_of_nonneg_left hbound (sq_nonneg ρ)
        linarith
    _ ≤ (A + ρ * B) ^ 2 := harith

theorem nearIdWeights (m : ℕ) (hm : Even m) (hm0 : 0 < m) (e : OrthonormalBasis (Fin (m / 2) × Fin 2) ℝ (Submission.Mostow.E m)) (R : Submission.Mostow.E m ≃ₗᵢ[ℝ] Submission.Mostow.E m) (φ : Fin (m / 2) → AddCircle (2 * Real.pi)) (hblock : ∀ (i : Fin (m / 2)) (x y : ℝ), ∃ t : ℝ, (t : AddCircle (2 * Real.pi)) = φ i ∧ R (x • e (i, Fin.castSucc 0) + y • e (i, 1)) = (Real.cos t * x - Real.sin t * y) • e (i, Fin.castSucc 0) + (Real.sin t * x + Real.cos t * y) • e (i, 1)) (Wz : Submission.Mostow.E m) (η ρ_ : ℝ) (hη : 0 < η) (hρ_ : 0 < ρ_) (hdisp : ‖R Wz - Wz‖ ≤ 2 * Real.sinh (η / 2)) (hchord : ∀ i : Fin (m / 2), Submission.Mostow.chord (φ i) ≤ 4 * η) : ∑ i : Fin (m / 2), (max ‖(inner ℝ (e (i, Fin.castSucc 0)) Wz) • e (i, Fin.castSucc 0) + (inner ℝ (e (i, 1)) Wz) • e (i, 1)‖ ρ_) ^ 2 * (Submission.Mostow.chord (φ i)) ^ 2 ≤ (2 * Real.sinh (η / 2) + 2 * Real.sqrt ((m : ℝ) / 2) * 2 * η * ρ_) ^ 2 := by
  -- abbreviate the displacement tolerance
  set A : ℝ := 2 * Real.sinh (η / 2) with hAdef
  have hApos : 0 < A := by
    rw [hAdef]
    have h : 0 < η / 2 := by linarith
    have h2 := Real.sinh_pos_iff.mpr h
    linarith
  have hdisp' : ‖R Wz - Wz‖ ≤ A := by simpa only [hAdef] using hdisp
  -- the exact block displacement identity
  have hblocks := displacementBlocks m hm e R φ hblock Wz A hApos.le hdisp'
  have hcast : ((m / 2 : ℕ) : ℝ) = (m : ℝ) / 2 := by
    rw [Nat.cast_div (even_iff_two_dvd.mp hm) (by norm_num : (2 : ℝ) ≠ 0)]
    norm_num
  -- each chord is at most `4η`, hence its square at most `(4η)²`
  have hsum_c : ∑ i : Fin (m / 2), (Submission.Mostow.chord (φ i)) ^ 2
      ≤ ((m / 2 : ℕ) : ℝ) * (4 * η) ^ 2 := by
    calc ∑ i : Fin (m / 2), (Submission.Mostow.chord (φ i)) ^ 2
        ≤ ∑ _i : Fin (m / 2), (4 * η) ^ 2 :=
          Finset.sum_le_sum (fun i _ => pow_le_pow_left₀ (chord_nonneg_circle _) (hchord i) 2)
      _ = ((m / 2 : ℕ) : ℝ) * (4 * η) ^ 2 := by simp
  have hsum_c' : ∑ i : Fin (m / 2), (Submission.Mostow.chord (φ i)) ^ 2
      ≤ (4 * η * Real.sqrt (((m / 2 : ℕ) : ℝ))) ^ 2 := by
    have hr : (0 : ℝ) ≤ ((m / 2 : ℕ) : ℝ) := by positivity
    calc ∑ i : Fin (m / 2), (Submission.Mostow.chord (φ i)) ^ 2
        ≤ ((m / 2 : ℕ) : ℝ) * (4 * η) ^ 2 := hsum_c
      _ = (4 * η * Real.sqrt (((m / 2 : ℕ) : ℝ))) ^ 2 := by
          conv_rhs => rw [mul_pow, Real.sq_sqrt hr]
          ring
  have key := weightedMaxSum_le
    (a := fun i : Fin (m / 2) => ‖(inner ℝ (e (i, Fin.castSucc 0)) Wz) • e (i, Fin.castSucc 0) +
      (inner ℝ (e (i, 1)) Wz) • e (i, 1)‖)
    (c := fun i : Fin (m / 2) => Submission.Mostow.chord (φ i))
    (ρ := ρ_) (A := A) (B := 4 * η * Real.sqrt (((m / 2 : ℕ) : ℝ)))
    hApos.le hρ_.le (by positivity) hblocks hsum_c'
  have hrepr : (A + 2 * Real.sqrt ((m : ℝ) / 2) * 2 * η * ρ_) ^ 2
      = (A + ρ_ * (4 * η * Real.sqrt (((m / 2 : ℕ) : ℝ)))) ^ 2 := by
    rw [hcast]; ring
  rw [hrepr]
  exact key

end Work.Mostow
