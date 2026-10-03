import Mathlib
import Submission.Work.Peluse.Concat.boxNormPow_iteratedPeel

/-!
# The mean of the peeled box norms is at most the parent box norm

Iterating Peluse's peel `Work.Peluse.Concat.boxNormPow_iteratedPeel` expresses the `2^{m+t}`-th
power of the box norm of `f` on the concatenated family `Fin.append Q P` as the `|Q j|⁻²`-weighted
average, over all tuples of pairs of shifts from the `Q j`, of the `2^t`-th powers of the box norms
of the iterated differences `iterDelta m`:

`‖f‖^{2^{m+t}}_{□_{Q,P}(S)} = (∏_j |Q j|⁻²) ∑_{sh} ‖iterDelta m sh f‖^{2^t}_{□_{P}(S)}`.

Since the weight is the reciprocal of the number of shift tuples, this reads
`‖f‖_{□_{Q,P}(S)} = ((1/#) ∑_{sh} ‖iterDelta m sh f‖^{2^t}_{□_P(S)})^{1/2^{m+t}}`.

The lemma `meanPeelLeBoxNorm` compares this with the *mean of the peeled norms*: assuming that every
peeled norm is at most `1`, one has

`(∏_j |Q j|⁻²) ∑_{sh} ‖iterDelta m sh f‖_{□_P(S)} ≤ ‖f‖_{□_{Q,P}(S)}`,

i.e. the normalised average of the `2^t`-th roots is dominated by the `2^{m+t}`-th root of the
normalised average of the `2^t`-th powers.

The analytic content is the elementary inequality

`(1/#) ∑_i a_i^{1/2^t} ≤ ((1/#) ∑_i a_i)^{1/2^{m+t}}`  for `0 ≤ a_i ≤ 1`

(`Work.Peluse.Prop36SW.inv_card_mul_sum_rpow_le`, proved by the weighted power mean
`Real.arith_mean_le_rpow_mean` for the concave function `x ↦ x^{1/2^t}`, followed by the comparison
of the exponents `1/2^{m+t} ≤ 1/2^t` at a base `≤ 1`).
-/

open scoped BigOperators

namespace Work.Peluse.Prop36SW

noncomputable section

/-- **The weighted power mean for the concave family.**  For a finite type `ι`, exponents
`α, β ∈ (0,1]` and `u_i ∈ [0,1]`,

`(#ι)⁻¹ ∑_i u_i^α ≤ ((#ι)⁻¹ ∑_i u_i)^{α β}`.

The proof is Jensen in the form `Real.arith_mean_le_rpow_mean` at the exponent `1/α ≥ 1` applied to
the numbers `u_i^α ≥ 0`, giving `(#ι)⁻¹ ∑_i u_i^α ≤ ((#ι)⁻¹ ∑_i u_i)^α`; since
`(#ι)⁻¹ ∑_i u_i ≤ 1` and `α β ≤ α`, the monotonicity of `x ↦ x^λ` on `[0,1]` for the *decreasing*
exponent finishes.  Both the empty case (`#ι = 0`) and the case `Σ u_i = 0` are degenerate and
handled by `0^λ = 0`. -/
lemma inv_card_mul_sum_rpow_le {ι : Type*} [Fintype ι] {α β : ℝ}
    (hα0 : 0 < α) (hα1 : α ≤ 1) (hβ0 : 0 < β) (hβ1 : β ≤ 1)
    (u : ι → ℝ) (hu0 : ∀ i, 0 ≤ u i) (hu1 : ∀ i, u i ≤ 1) :
    ((Fintype.card ι : ℝ))⁻¹ * ∑ i, (u i) ^ α
      ≤ (((Fintype.card ι : ℝ))⁻¹ * ∑ i, u i) ^ (α * β) := by
  rcases Nat.eq_zero_or_pos (Fintype.card ι) with hN | hN
  · rw [hN, Nat.cast_zero, inv_zero, zero_mul, zero_mul,
      Real.zero_rpow (ne_of_gt (mul_pos hα0 hβ0))]
  · set S : ℝ := ∑ i, u i with hSdef
    have hS0 : 0 ≤ S := Finset.sum_nonneg (fun i _ => hu0 i)
    have hSN : S ≤ (Fintype.card ι : ℝ) := by
      rw [hSdef]
      calc ∑ i : ι, u i ≤ ∑ _i : ι, (1:ℝ) := Finset.sum_le_sum (fun i _ => hu1 i)
        _ = (Fintype.card ι : ℝ) := by simp
    have hcard_ne : (Fintype.card ι : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
    have hw : ∀ i ∈ (Finset.univ : Finset ι), 0 ≤ ((Fintype.card ι : ℝ))⁻¹ := fun i _ => by positivity
    have hw1 : ∑ i ∈ (Finset.univ : Finset ι), ((Fintype.card ι : ℝ))⁻¹ = 1 := by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_inv_cancel₀ hcard_ne]
    have hz : ∀ i ∈ (Finset.univ : Finset ι), 0 ≤ (u i) ^ α :=
      fun i _ => Real.rpow_nonneg (hu0 i) _
    have hp : (1:ℝ) ≤ 1 / α := by
      rw [one_le_div hα0]; exact hα1
    have hjens := Real.arith_mean_le_rpow_mean (Finset.univ)
        (fun _ : ι => ((Fintype.card ι : ℝ))⁻¹) (fun i => (u i) ^ α) hw hw1 hz hp
    have harg : ∀ i : ι, ((u i) ^ α) ^ (1 / α) = u i := by
      intro i
      rw [← Real.rpow_mul (hu0 i), mul_one_div_cancel (ne_of_gt hα0), Real.rpow_one]
    have hsum_lhs : (∑ i : ι, ((Fintype.card ι : ℝ))⁻¹ * (u i) ^ α)
        = ((Fintype.card ι : ℝ))⁻¹ * ∑ i, (u i) ^ α := (Finset.mul_sum _ _ _).symm
    have hsum_rhs : (∑ i : ι, ((Fintype.card ι : ℝ))⁻¹ * ((u i) ^ α) ^ (1 / α))
        = ((Fintype.card ι : ℝ))⁻¹ * S := by
      rw [show (∑ i : ι, ((Fintype.card ι : ℝ))⁻¹ * ((u i) ^ α) ^ (1 / α))
            = ((Fintype.card ι : ℝ))⁻¹ * ∑ i, ((u i) ^ α) ^ (1 / α)
          from (Finset.mul_sum _ _ _).symm]
      congr 1
      rw [hSdef]
      exact Finset.sum_congr rfl (fun i _ => harg i)
    have hexp2 : (1:ℝ) / (1 / α) = α := by field_simp
    have hstep1 : ((Fintype.card ι : ℝ))⁻¹ * ∑ i, (u i) ^ α
        ≤ (((Fintype.card ι : ℝ))⁻¹ * S) ^ α := by
      have h := hjens
      rw [hsum_lhs, hsum_rhs, hexp2] at h
      exact h
    have hx0 : 0 ≤ ((Fintype.card ι : ℝ))⁻¹ * S := mul_nonneg (by positivity) hS0
    have hx1 : ((Fintype.card ι : ℝ))⁻¹ * S ≤ 1 := by
      calc ((Fintype.card ι : ℝ))⁻¹ * S ≤ ((Fintype.card ι : ℝ))⁻¹ * (Fintype.card ι : ℝ) :=
            mul_le_mul_of_nonneg_left hSN (by positivity)
        _ = 1 := inv_mul_cancel₀ hcard_ne
    have hstep2 : (((Fintype.card ι : ℝ))⁻¹ * S) ^ α
        ≤ (((Fintype.card ι : ℝ))⁻¹ * S) ^ (α * β) := by
      rcases eq_or_lt_of_le hx0 with hx | hx
      · rw [← hx, Real.zero_rpow (ne_of_gt hα0), Real.zero_rpow (ne_of_gt (mul_pos hα0 hβ0))]
      · exact Real.rpow_le_rpow_of_exponent_ge hx hx1 (mul_le_of_le_one_right (le_of_lt hα0) hβ1)
    exact le_trans hstep1 hstep2

theorem meanPeelLeBoxNorm {m t : ℕ} (ht : 1 ≤ t) (Q : Fin m → Finset ℤ) (P : Fin t → Finset ℤ)
    (S : Finset ℤ) (f : ℤ → ℂ) (hf : Work.Peluse.FinSuppZ f)
    (hX : ∀ sh : (i : Fin m) → ↥(Q i) × ↥(Q i),
      Work.Peluse.boxNorm t P S
        (Work.Peluse.Ulower.iterDelta m (fun i => (((sh i).1 : ℤ), ((sh i).2 : ℤ))) f) ≤ 1) :
    (∏ i : Fin m, (((Q i).card : ℝ))⁻¹ ^ 2) *
      ∑ sh : (i : Fin m) → ↥(Q i) × ↥(Q i),
        Work.Peluse.boxNorm t P S
          (Work.Peluse.Ulower.iterDelta m (fun i => (((sh i).1 : ℤ), ((sh i).2 : ℤ))) f)
      ≤ Work.Peluse.boxNorm (m + t) (Fin.append Q P) S f := by
  classical
  -- The weight `∏_j |Q j|⁻²` is the reciprocal of the number of shift tuples.
  set N : ℕ := Fintype.card ((i : Fin m) → ↥(Q i) × ↥(Q i)) with hN
  have hcard : (∏ i : Fin m, (((Q i).card : ℝ))⁻¹ ^ 2) = ((N : ℝ))⁻¹ := by
    rw [hN]
    have hcardN : ((Fintype.card ((i : Fin m) → ↥(Q i) × ↥(Q i)) : ℕ) : ℝ)
        = ∏ i : Fin m, ((Q i).card : ℝ) ^ 2 := by
      rw [Fintype.card_pi]
      push_cast
      refine Finset.prod_congr rfl (fun i _ => ?_)
      rw [Fintype.card_prod, Fintype.card_coe]
      push_cast
      ring
    rw [show (∏ i : Fin m, (((Q i).card : ℝ))⁻¹ ^ 2)
          = ∏ i : Fin m, ((((Q i).card : ℝ)) ^ 2)⁻¹ from
        Finset.prod_congr rfl (fun i _ => inv_pow ((Q i).card : ℝ) 2),
      Finset.prod_inv_distrib, ← hcardN]
  -- The peel identity, in the normalisation by the number of shift tuples.
  have hpeel := Work.Peluse.Concat.boxNormPow_iteratedPeel (t := t) (m := m) ht Q P S f hf
  rw [hcard] at hpeel
  rw [hcard]
  -- Unfold the box norm on the right into the box-norm power at the exponent `1/2^{m+t}`.
  rw [show Work.Peluse.boxNorm (m + t) (Fin.append Q P) S f
      = (Work.Peluse.boxNormPow (m + t) (Fin.append Q P) S f) ^ ((1:ℝ)/(2:ℝ)^(m+t)) from rfl]
  rw [hpeel]
  -- Unfold the box norms on the left into the box-norm powers at the exponent `1/2^t`.
  simp only [Work.Peluse.boxNorm]
  -- `1/2^{m+t} = (1/2^t)·(1/2^m)`.
  have hexp : ((1:ℝ)/(2:ℝ)^t) * ((1:ℝ)/(2:ℝ)^m) = (1:ℝ)/(2:ℝ)^(m+t) := by
    rw [pow_add, one_div, one_div, one_div, mul_inv]
    ring
  rw [← hexp]
  -- The finite power-mean inequality, with `u sh` the peeled box-norm powers.
  exact inv_card_mul_sum_rpow_le (α := (1:ℝ)/(2:ℝ)^t) (β := (1:ℝ)/(2:ℝ)^m)
    (by positivity)
    (by rw [div_le_one (by positivity)]; exact one_le_pow₀ (by norm_num))
    (by positivity)
    (by rw [div_le_one (by positivity)]; exact one_le_pow₀ (by norm_num))
    (fun sh : (i : Fin m) → ↥(Q i) × ↥(Q i) => Work.Peluse.boxNormPow t P S
      (Work.Peluse.Ulower.iterDelta m (fun i => (((sh i).1 : ℤ), ((sh i).2 : ℤ))) f))
    (fun sh => norm_nonneg _)
    (fun sh => by
      -- `boxNormPow t P S · ≤ 1`, from the hypothesis `boxNorm t P S · ≤ 1`.
      have h1 := hX sh
      simp only [Work.Peluse.boxNorm] at h1
      have hx0 : 0 ≤ Work.Peluse.boxNormPow t P S
          (Work.Peluse.Ulower.iterDelta m (fun i => (((sh i).1 : ℤ), ((sh i).2 : ℤ))) f) :=
        norm_nonneg _
      have hα0 : 0 < (1:ℝ)/(2:ℝ)^t := by positivity
      have h := Real.rpow_le_rpow
        (x := (Work.Peluse.boxNormPow t P S
          (Work.Peluse.Ulower.iterDelta m (fun i => (((sh i).1 : ℤ), ((sh i).2 : ℤ))) f)) ^
            ((1:ℝ)/(2:ℝ)^t))
        (y := 1) (z := 1 / ((1:ℝ)/(2:ℝ)^t))
        (Real.rpow_nonneg hx0 _) h1 (by positivity)
      rw [← Real.rpow_mul hx0, mul_one_div_cancel (ne_of_gt hα0), Real.rpow_one,
        Real.one_rpow] at h
      exact h)

end

end Work.Peluse.Prop36SW
