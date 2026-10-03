import Mathlib
import Submission.Work.Peluse.Peel.boxSumPow_peel

namespace Work.Peluse.Concat

/-- **Peeling the first coordinate of the box-norm power.**  For `t ≥ 1`, the `2^{t+1}`-th power of
Peluse's box norm of `f` on the shift sets `Q 0, …, Q t` and the support `S` equals the average over
`h, h' ∈ Q 0` of the `2^t`-th power of the box norm of the difference
`Δ'_{h,h'} f (u) = f (u + h) · conj (f (u + h'))` on the remaining sets `Q 1, …, Q t`:

`‖f‖^{2^{t+1}}_{□^{t+1}_{Q₀,…,Q_t}(S)}
   = |Q₀|⁻² ∑_{h,h' ∈ Q₀} ‖Δ'_{h,h'} f‖^{2^t}_{□^t_{Q₁,…,Q_t}(S)}`.

This is the level-lowering recursion of Peluse's Definition 2.1 in the form in which it is applied
in the paper: the complex peel identity `Work.Peluse.Peel.boxSumPow_peel` for the cube sums, read
through `Work.Peluse.BoxNorm.boxSumPow_eq_boxNormPow` (every summand is a nonnegative real, so the
modulus distributes over the `|Q₀|⁻²`-weighted sum). -/
theorem boxNormPow_succ_peel_gen {t : ℕ} (ht : 1 ≤ t) (Q : Fin (t + 1) → Finset ℤ)
    (S : Finset ℤ) {f : ℤ → ℂ} (hf : Work.Peluse.FinSuppZ f) :
    Work.Peluse.boxNormPow (t + 1) Q S f
      = (((Q 0).card : ℝ))⁻¹ ^ 2 *
        ∑ h ∈ Q 0, ∑ h' ∈ Q 0,
          Work.Peluse.boxNormPow t (fun i : Fin t => Q i.succ) S
            (fun u : ℤ => f (u + h) * star (f (u + h'))) := by
  classical
  have hnt : 1 ≤ t + 1 := by omega
  -- the differences `Δ'_{h,h'} f` are finitely supported
  have hfs : ∀ h h' : ℤ,
      Work.Peluse.FinSuppZ (fun u : ℤ => f (u + h) * star (f (u + h'))) := by
    intro h h'
    obtain ⟨N, hN⟩ := hf
    refine ⟨max (N + h.natAbs) (N + h'.natAbs), fun u hu => ?_⟩
    have h1 : f (u + h) = 0 := by
      apply hN
      have htri : u.natAbs ≤ (u + h).natAbs + h.natAbs := by
        have h' := Int.natAbs_add_le (u + h) (-h)
        simpa [Int.natAbs_neg, add_assoc] using h'
      have hlt : N + h.natAbs < u.natAbs := lt_of_le_of_lt (le_max_left _ _) hu
      omega
    simp [h1]
  -- each summand of the complex peel identity is a nonnegative real
  have hinner : ∀ h ∈ Q 0, ∀ h' ∈ Q 0,
      Work.Peluse.boxSumPow t (fun i : Fin t => Q i.succ) S
          (fun u : ℤ => f (u + h) * star (f (u + h')))
        = ((Work.Peluse.boxNormPow t (fun i : Fin t => Q i.succ) S
            (fun u : ℤ => f (u + h) * star (f (u + h'))) : ℝ) : ℂ) :=
    fun h _ h' _ => Work.Peluse.BoxNorm.boxSumPow_eq_boxNormPow ht (hfs h h')
  have hreal : Work.Peluse.boxNormPow (t + 1) Q S f
      = ((Q 0).card : ℝ)⁻¹ * ((Q 0).card : ℝ)⁻¹ *
        ∑ h ∈ Q 0, ∑ h' ∈ Q 0,
          Work.Peluse.boxNormPow t (fun i : Fin t => Q i.succ) S
            (fun u : ℤ => f (u + h) * star (f (u + h'))) := by
    apply Complex.ofReal_inj.mp
    rw [show ((Work.Peluse.boxNormPow (t + 1) Q S f : ℝ) : ℂ)
        = Work.Peluse.boxSumPow (t + 1) Q S f from
      (Work.Peluse.BoxNorm.boxSumPow_eq_boxNormPow hnt hf).symm]
    rw [Work.Peluse.Peel.boxSumPow_peel]
    rw [Finset.sum_congr rfl (fun h hh => Finset.sum_congr rfl (fun h' hh' => hinner h hh h' hh'))]
    simp only [← Complex.ofReal_natCast, ← Complex.ofReal_inv, ← Complex.ofReal_sum,
      ← Complex.ofReal_mul]
  rw [hreal]
  ring

end Work.Peluse.Concat
