import Mathlib
import Submission.Work.Peluse.Peel.boxSumPow_peel
import Submission.Work.Peluse.Peel.boxNormPow_one_tsum

/-!
# The level-two box-norm power as a sum of squares

Peluse's box-norm power of order `2` over the direction set `Q` (used twice) and the window `S`
is, for a finitely supported `f`, the elementary sum of squares

`‖f‖^{2^2}_{□²_Q(S)}
   = |S|⁻¹ · |Q|⁻⁴ · ∑_{a ∈ Q} ∑_{b ∈ Q} ∑_x ‖∑_{k ∈ Q} f (x + a + k) · conj (f (x + b + k))‖²`.

The proof peels the first coordinate of the box sum (`Work.Peluse.Peel.boxSumPow_peel`, which
identifies the level-`2` box sum with the average over `a, b ∈ Q` of the level-`1` box sums of the
differences `Δ'_{(a,b)} f (u) = f (u + a) · conj (f (u + b))`), then evaluates each level-`1` box
norm as a `tsum` of squares (`Work.Peluse.Peel.boxNormPow_one_tsum`).  Since all the terms are
nonnegative, the modulus of the (real, nonnegative) box sum is the displayed real number; this is
`Work.Peluse.BoxNorm.boxSumPow_eq_boxNormPow`.

This is the base case `t = 2` of the dilation comparison `Work.Peluse.BoxNormDilation`
(`dilated_directions_ge.lean`).

## Main result

* `Work.Peluse.BoxNormDilation.boxNormPow_two_eq`
-/

namespace Work.Peluse.BoxNormDilation

theorem boxNormPow_two_eq (Q S : Finset ℤ) {f : ℤ → ℂ} (hf : Work.Peluse.FinSuppZ f) :
    Work.Peluse.boxNormPow 2 (fun _ : Fin 2 => Q) S f
      = ((S.card : ℝ))⁻¹ * ((Q.card : ℝ))⁻¹ ^ 4 *
        ∑ a ∈ Q, ∑ b ∈ Q, ∑' x : ℤ,
          ‖∑ k ∈ Q, f (x + a + k) * star (f (x + b + k))‖ ^ 2 := by
  obtain ⟨N, hN⟩ := hf
  -- The difference `Δ'_{(h,h')} f = f (· + h) · conj (f (· + h'))` is supported in a ball.
  have hsupp : ∀ h h' : ℤ, Work.Peluse.SupportIn
      (fun u : ℤ => f (u + h) * star (f (u + h'))) (N + h.natAbs + h'.natAbs) := by
    intro h h' u hu
    by_cases h1 : f (u + h) = 0
    · simp [h1]
    · exfalso
      have hle : (u + h).natAbs ≤ N := by
        by_contra hc
        exact h1 (hN (u + h) (by omega))
      have htri : u.natAbs ≤ (u + h).natAbs + h.natAbs := by
        simpa using Int.natAbs_add_le (u + h) (-h)
      omega
  let Z : ℤ → ℤ → ℝ := fun h h' => ∑' x : ℤ,
      ‖∑ a ∈ Q, f ((x + a) + h) * star (f ((x + a) + h'))‖^2
  -- Peel the first coordinate of the box sum and pass to the modulus.
  have hstep1 : Work.Peluse.boxNormPow 2 (fun _ : Fin 2 => Q) S f
      = ((Q.card : ℝ))⁻¹ ^ 2 * ∑ h ∈ Q, ∑ h' ∈ Q,
          Work.Peluse.boxNormPow 1 (fun _ : Fin 1 => Q) S
            (fun u : ℤ => f (u + h) * star (f (u + h'))) := by
    have hsum_nonneg : 0 ≤ ∑ h ∈ Q, ∑ h' ∈ Q,
          Work.Peluse.boxNormPow 1 (fun _ : Fin 1 => Q) S
            (fun u : ℤ => f (u + h) * star (f (u + h'))) :=
      Finset.sum_nonneg (fun h _ => Finset.sum_nonneg (fun h' _ => by
        rw [Work.Peluse.boxNormPow]; exact norm_nonneg _))
    have hpeelC : Work.Peluse.boxSumPow 2 (fun _ : Fin 2 => Q) S f
        = ((((Q.card : ℝ))⁻¹ ^ 2 * ∑ h ∈ Q, ∑ h' ∈ Q,
            Work.Peluse.boxNormPow 1 (fun _ : Fin 1 => Q) S
              (fun u : ℤ => f (u + h) * star (f (u + h'))) : ℝ) : ℂ) := by
      rw [Work.Peluse.Peel.boxSumPow_peel (t := 1) (fun _ : Fin 2 => Q) S f]
      rw [Finset.sum_congr rfl (fun h _ => Finset.sum_congr rfl (fun h' _ =>
            Work.Peluse.BoxNorm.boxSumPow_eq_boxNormPow (t := 1) le_rfl
              (⟨N + h.natAbs + h'.natAbs, hsupp h h'⟩ : Work.Peluse.FinSuppZ _)))]
      push_cast
      ring
    show ‖Work.Peluse.boxSumPow 2 (fun _ : Fin 2 => Q) S f‖ = _
    rw [hpeelC]
    exact Complex.norm_of_nonneg (mul_nonneg (sq_nonneg _) hsum_nonneg)
  -- Evaluate each level-one box norm as a `tsum` of squares.
  have hZ : ∀ h h' : ℤ, Work.Peluse.boxNormPow 1 (fun _ : Fin 1 => Q) S
          (fun u : ℤ => f (u + h) * star (f (u + h')))
      = ((S.card:ℝ))⁻¹ * ((Q.card:ℝ))⁻¹^2 * Z h h' :=
    fun h h' => Work.Peluse.Peel.boxNormPow_one_tsum Q S (hsupp h h')
  have hstep2 : ((Q.card : ℝ))⁻¹ ^ 2 * ∑ h ∈ Q, ∑ h' ∈ Q,
          Work.Peluse.boxNormPow 1 (fun _ : Fin 1 => Q) S
            (fun u : ℤ => f (u + h) * star (f (u + h')))
      = ((S.card:ℝ))⁻¹ * ((Q.card:ℝ))⁻¹^4 * ∑ h ∈ Q, ∑ h' ∈ Q, Z h h' := by
    have hAB : (∑ h ∈ Q, ∑ h' ∈ Q, ((S.card:ℝ))⁻¹ * ((Q.card:ℝ))⁻¹^2 * Z h h')
        = ((S.card:ℝ))⁻¹ * ((Q.card:ℝ))⁻¹^2 * ∑ h ∈ Q, ∑ h' ∈ Q, Z h h' := by
      have inner : ∀ h : ℤ, (∑ h' ∈ Q, ((S.card:ℝ))⁻¹ * ((Q.card:ℝ))⁻¹^2 * Z h h')
          = ((S.card:ℝ))⁻¹ * ((Q.card:ℝ))⁻¹^2 * ∑ h' ∈ Q, Z h h' :=
        fun h => (Finset.mul_sum Q (fun h' => Z h h') _).symm
      calc (∑ h ∈ Q, ∑ h' ∈ Q, ((S.card:ℝ))⁻¹ * ((Q.card:ℝ))⁻¹^2 * Z h h')
          = ∑ h ∈ Q, ((S.card:ℝ))⁻¹ * ((Q.card:ℝ))⁻¹^2 * ∑ h' ∈ Q, Z h h' :=
              Finset.sum_congr rfl (fun h _ => inner h)
        _ = ((S.card:ℝ))⁻¹ * ((Q.card:ℝ))⁻¹^2 * ∑ h ∈ Q, ∑ h' ∈ Q, Z h h' :=
              (Finset.mul_sum Q (fun h => ∑ h' ∈ Q, Z h h') _).symm
    calc ((Q.card : ℝ))⁻¹ ^ 2 * ∑ h ∈ Q, ∑ h' ∈ Q,
          Work.Peluse.boxNormPow 1 (fun _ : Fin 1 => Q) S
            (fun u : ℤ => f (u + h) * star (f (u + h')))
        = ((Q.card : ℝ))⁻¹ ^ 2 * ∑ h ∈ Q, ∑ h' ∈ Q,
          ((S.card:ℝ))⁻¹ * ((Q.card:ℝ))⁻¹^2 * Z h h' := by
            rw [Finset.sum_congr rfl (fun h _ => Finset.sum_congr rfl (fun h' _ => hZ h h'))]
      _ = ((Q.card : ℝ))⁻¹ ^ 2 * (((S.card:ℝ))⁻¹ * ((Q.card:ℝ))⁻¹^2 *
            ∑ h ∈ Q, ∑ h' ∈ Q, Z h h') := by rw [hAB]
      _ = ((S.card:ℝ))⁻¹ * ((Q.card:ℝ))⁻¹^4 * ∑ h ∈ Q, ∑ h' ∈ Q, Z h h' := by ring
  -- Rename the summation indices.
  have hfinal : (∑ h ∈ Q, ∑ h' ∈ Q, Z h h')
      = ∑ a ∈ Q, ∑ b ∈ Q, ∑' x : ℤ,
          ‖∑ k ∈ Q, f (x + a + k) * star (f (x + b + k))‖ ^ 2 := by
    refine Finset.sum_congr rfl (fun h _ => Finset.sum_congr rfl (fun h' _ => ?_))
    show (∑' x : ℤ, ‖∑ a ∈ Q, f ((x + a) + h) * star (f ((x + a) + h'))‖^2)
        = ∑' x : ℤ, ‖∑ k ∈ Q, f (x + h + k) * star (f (x + h' + k))‖^2
    refine tsum_congr (fun x => ?_)
    rw [show (∑ a ∈ Q, f ((x + a) + h) * star (f ((x + a) + h')))
          = (∑ a ∈ Q, f (x + h + a) * star (f (x + h' + a))) from
          Finset.sum_congr rfl (fun a _ => by rw [add_right_comm x a h, add_right_comm x a h'])]
  rw [hstep1, hstep2, hfinal]

end Work.Peluse.BoxNormDilation
