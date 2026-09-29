import Mathlib

namespace Work.TMComp.RedC7T

open GenContFract

/-- **Strict convergent approximation bound.**  For a real number `v` whose continued fraction
expansion does not terminate at any stage (equivalently, an irrational `v`), every convergent
satisfies `|v - convs n| < 1 / (dens n)^2`.

The proof uses the exact error formula `GenContFract.sub_convs_eq`
`v - convs n = (-1)^n / (B * (fr⁻¹ * B + pB))`, where `B = dens n` and `fr = fract(stream v n)`
lies in `(0,1)`.  Since `fr⁻¹ > 1` and `pB ≥ 0`, the denominator `B * (fr⁻¹ * B + pB)` is
strictly larger than `B * B = B^2`. -/
theorem cf_convs_lt_inv_dens_sq (v : ℝ) (hv : ∀ n, ¬ (GenContFract.of v).TerminatedAt n) (n : ℕ) :
    |v - (GenContFract.of v).convs n| < 1 / ((GenContFract.of v).dens n) ^ 2 := by
  -- `hv n` (non-termination) produces an `IntFractPair` at position `n` with non-zero fractional
  -- part.
  have hsucc : IntFractPair.stream v (n + 1) ≠ none := fun h =>
    hv n ((of_terminatedAt_n_iff_succ_nth_intFractPair_stream_eq_none).mpr h)
  obtain ⟨ifp_succ, hsucc_eq⟩ := Option.ne_none_iff_exists'.mp hsucc
  obtain ⟨ifp, hstream, hfr_ne, -⟩ :=
    IntFractPair.succ_nth_stream_eq_some_iff.mp hsucc_eq
  have hfr_pos : 0 < ifp.fr :=
    lt_of_le_of_ne (IntFractPair.nth_stream_fr_nonneg hstream) (Ne.symm hfr_ne)
  have hfr_lt_one : ifp.fr < 1 := IntFractPair.nth_stream_fr_lt_one hstream
  have hfr_inv : 1 < ifp.fr⁻¹ := (one_lt_inv₀ hfr_pos).mpr hfr_lt_one
  -- the `n`-th denominator is positive
  have hBpos : 0 < (GenContFract.of v).dens n := by
    have hmono : Monotone fun k => (GenContFract.of v).dens k :=
      monotone_nat_of_le_succ fun k => GenContFract.of_den_mono
    have h0 : (GenContFract.of v).dens 0 ≤ (GenContFract.of v).dens n := hmono (Nat.zero_le n)
    have hden0 : (GenContFract.of v).dens 0 = 1 := rfl
    rw [hden0] at h0
    linarith
  have hpB : 0 ≤ ((GenContFract.of v).contsAux n).b := GenContFract.zero_le_of_contsAux_b
  -- rewrite `dens n` in the goal as the continuant `(contsAux (n+1)).b`, as produced by
  -- `sub_convs_eq`.
  have hB : (GenContFract.of v).dens n = ((GenContFract.of v).contsAux (n + 1)).b := rfl
  rw [hB]
  -- the exact error formula
  have hsub := GenContFract.sub_convs_eq (v := v) (n := n) hstream
  dsimp only at hsub
  rw [if_neg hfr_ne] at hsub
  -- the exact denominator is positive
  have hDpos : 0 < ((GenContFract.of v).contsAux (n + 1)).b *
      (ifp.fr⁻¹ * ((GenContFract.of v).contsAux (n + 1)).b +
        ((GenContFract.of v).contsAux n).b) := by
    have h1 : 0 < ifp.fr⁻¹ * ((GenContFract.of v).contsAux (n + 1)).b :=
      mul_pos (lt_trans zero_lt_one hfr_inv) hBpos
    have h2 : 0 < ifp.fr⁻¹ * ((GenContFract.of v).contsAux (n + 1)).b +
        ((GenContFract.of v).contsAux n).b := by linarith
    exact mul_pos hBpos h2
  rw [hsub, abs_div, abs_neg_one_pow, abs_of_pos hDpos]
  -- reduce to the comparison of the two (positive) denominators
  apply one_div_lt_one_div_of_lt
  · positivity
  · have hlt : ((GenContFract.of v).contsAux (n + 1)).b <
        ifp.fr⁻¹ * ((GenContFract.of v).contsAux (n + 1)).b +
          ((GenContFract.of v).contsAux n).b := by
      have h1 : 0 < (ifp.fr⁻¹ - 1) * ((GenContFract.of v).contsAux (n + 1)).b :=
        mul_pos (by linarith) hBpos
      nlinarith [h1, hpB]
    nlinarith [mul_lt_mul_of_pos_left hlt hBpos]

end Work.TMComp.RedC7T
