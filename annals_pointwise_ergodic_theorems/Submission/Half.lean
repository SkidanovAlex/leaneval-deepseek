import ChallengeDeps
import Mathlib.Tactic
import Submission.Transfer

/-!
# The upper half average at a real scale

Krause--Mirek--Tao replace the averaging operator `A_N` by the "upper half" average
`Ã_N = (1/⌊N⌋) ∑_{⌊N⌋/2 < n ≤ ⌊N⌋} f(T^{P₁(n)}x) g(T^{P₂(n)}x)`.

Because the telescoping reduction has to be applied to the rescaled families `N ↦ a n / 2^k` of a
`Λ`-lacunary sequence `a : ℕ → ℝ≥0` (which must remain `Λ`-lacunary), the half average is
conveniently viewed as a function of the real scale `N`.  The key point is that
`Ã_{N/2^k} = Ã_{⌊N⌋/2^k}`, i.e. the floor commutes with division by a power of two
(`Nat.floor_div_pow_two`).
-/

set_option maxHeartbeats 800000

namespace Submission

open _root_.PointwiseErgodicTheorems
set_option autoImplicit false

namespace PointwiseErgodicTheorems

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal PNat

variable {𝓧 : Type*} [MeasurableSpace 𝓧]

/-- `((m / n : ℕ) : ℝ≥0) ≤ (m : ℝ≥0) / n`. -/
lemma natCast_div_le_nnreal (m n : ℕ) : ((m / n : ℕ) : ℝ≥0) ≤ (m : ℝ≥0) / n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · rw [le_div_iff₀ (by exact_mod_cast hn : (0:ℝ≥0) < (n:ℝ≥0))]
    calc ((m / n : ℕ) : ℝ≥0) * (n : ℝ≥0) = (((m / n) * n : ℕ) : ℝ≥0) := by push_cast; ring
      _ ≤ (m : ℝ≥0) := by exact_mod_cast Nat.div_mul_le_self m n

/-- Floors commute with division by a natural number, for nonnegative reals:
`⌊N / n⌋ = ⌊N⌋ / n`. -/
lemma nat_floor_div_natCast (N : ℝ≥0) (n : ℕ) :
    Nat.floor (N / (n : ℝ≥0)) = Nat.floor N / n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  refine le_antisymm ?_ ?_
  · rw [Nat.le_div_iff_mul_le hn]
    have h1 : ((Nat.floor (N / (n:ℝ≥0)) : ℕ) : ℝ≥0) ≤ N / (n:ℝ≥0) :=
      Nat.floor_le (show (0:ℝ≥0) ≤ _ by positivity)
    have h2 : (((Nat.floor (N / (n:ℝ≥0)) * n) : ℕ) : ℝ≥0) ≤ N := by
      rw [Nat.cast_mul]
      calc (Nat.floor (N/(n:ℝ≥0)) : ℝ≥0) * (n:ℝ≥0)
          ≤ (N / (n:ℝ≥0)) * (n:ℝ≥0) := by gcongr
        _ = N := by rw [div_mul_cancel₀ _ (by exact_mod_cast hn.ne' : (n:ℝ≥0) ≠ 0)]
    have h3 := Nat.floor_mono h2
    rwa [Nat.floor_natCast] at h3
  · have h1 : ((Nat.floor N / n : ℕ) : ℝ≥0) ≤ (Nat.floor N : ℝ≥0) / (n:ℝ≥0) :=
      natCast_div_le_nnreal (Nat.floor N) n
    have h2 : (Nat.floor N : ℝ≥0) / (n:ℝ≥0) ≤ N / (n:ℝ≥0) := by
      gcongr; exact Nat.floor_le (show (0:ℝ≥0) ≤ _ by positivity)
    have h3 := Nat.floor_mono (le_trans h1 h2)
    rwa [Nat.floor_natCast] at h3

/-- Floors commute with division by a power of two. -/
lemma nat_floor_div_pow_two (N : ℝ≥0) (k : ℕ) :
    Nat.floor (N / (2 : ℝ≥0) ^ k) = Nat.floor N / 2 ^ k := by
  have := nat_floor_div_natCast N (2 ^ k)
  rwa [Nat.cast_pow, Nat.cast_ofNat] at this

/-- The "upper half" average at an arbitrary nonnegative real scale,
`Ã_N = (1/⌊N⌋) ∑_{⌊N⌋/2 < n ≤ ⌊N⌋} f(T^{P₁(n)}x) g(T^{P₂(n)}x)`. -/
noncomputable def AhalfR (T : 𝓧 ≃ᵐ 𝓧) (N : ℝ≥0) (P₁ P₂ : ℤ[X]) (f g : 𝓧 → ℂ) (x : 𝓧) : ℂ :=
  Ahalf T (Nat.floor N) P₁ P₂ f g x

/-- Unfolding of `AhalfR`. -/
lemma AhalfR_eq (T : 𝓧 ≃ᵐ 𝓧) (N : ℝ≥0) (P₁ P₂ : ℤ[X]) (f g : 𝓧 → ℂ) (x : 𝓧) :
    AhalfR T N P₁ P₂ f g x
      = (Nat.floor N : ℝ)⁻¹ * Ablock T (Nat.floor N) P₁ P₂ f g x := rfl

/-- The half average at the rescaled scale `N / 2^k` is the half average of the floored scale. -/
lemma AhalfR_div_pow_two (T : 𝓧 ≃ᵐ 𝓧) (N : ℝ≥0) (k : ℕ) (P₁ P₂ : ℤ[X])
    (f g : 𝓧 → ℂ) (x : 𝓧) :
    AhalfR T (N / 2 ^ k) P₁ P₂ f g x = Ahalf T (Nat.floor N / 2 ^ k) P₁ P₂ f g x := by
  rw [AhalfR, nat_floor_div_pow_two]

/-- The half average vanishes at scale zero. -/
lemma Ahalf_zero (T : 𝓧 ≃ᵐ 𝓧) (P₁ P₂ : ℤ[X]) (f g : 𝓧 → ℂ) (x : 𝓧) :
    Ahalf T 0 P₁ P₂ f g x = 0 := by
  simp [Ahalf, Ablock]

/-- The half average vanishes when the floored scale is zero. -/
lemma AhalfR_eq_zero_of_floor_eq_zero (T : 𝓧 ≃ᵐ 𝓧) {N : ℝ≥0} (h : Nat.floor N = 0)
    (P₁ P₂ : ℤ[X]) (f g : 𝓧 → ℂ) (x : 𝓧) : AhalfR T N P₁ P₂ f g x = 0 := by
  rw [AhalfR, h]; exact Ahalf_zero T P₁ P₂ f g x

/-- **Dyadic telescoping identity, real-scale form.**  The ordinary average at scale `N` is a
weighted sum of the halved averages at the rescaled scales `N / 2^k`. -/
lemma A_eq_sum_AhalfR (T : 𝓧 ≃ᵐ 𝓧) (N : ℝ≥0) (P : ℤ[X]) (f g : 𝓧 → ℂ) (x : 𝓧)
    (hN : 1 ≤ Nat.floor N) :
    A T N X P f g x
      = ∑ k ∈ Finset.range (Nat.log2 (Nat.floor N) + 1),
          ((Nat.floor N / 2 ^ k : ℕ) : ℝ) / (Nat.floor N : ℝ)
            * AhalfR T (N / 2 ^ k) X P f g x := by
  rw [A_eq_sum_Ahalf T N X P f g x hN]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [AhalfR_div_pow_two]

end PointwiseErgodicTheorems
end Submission
