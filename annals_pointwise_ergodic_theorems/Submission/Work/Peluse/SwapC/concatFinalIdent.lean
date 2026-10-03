import Mathlib
import Submission.Work.Peluse.SwapC.concatGlue

namespace Work.Peluse.SwapC

open scoped BigOperators
open Work.Peluse Work.Peluse.LadderP.Swap

/-!
# The final concatenation identification: peeling the last slot of a `pbox`

`Work.Peluse.SwapC.concatFinalIdent` is the elementary (but notationally heavy) identity used in the
assembly of KKL Lemma 6.1 (`Work.Peluse.SwapC.concatStep`): the box norm of the `2s + 1` slots

`[q₁ p.1 ++ q₁ p.2, qH p.2]`, `[q₂ p.1 ++ q₂ p.2, qH p.1]`

is the average, over the `(2s + 2)`-tuple of `Fin M`-indices, of the box norm of the `2s` slots
`q₁ p.1 ++ q₁ p.2`, `q₂ p.1 ++ q₂ p.2` of the kernel
`Δ'_{(pdir (qH p.2) (qH p.1) ·, pdir (qH p.2) (qH p.1) ·)} f`.

The content is the peel `pbox_peel` (`Submission/Work/Peluse/SwapC/pbox_peel.lean`), which peels the
*first* slot of `pboxSum`; here the slot to be peeled is the *last* one, so it is first moved to the
front by the rotation `finRotate` via `Fin.snoc_eq_cons_rotate` and the permutation invariance
`pbox_perm` of the slots.  The constant `(M ^ 4)⁻¹` produced by the peel is the reciprocal of the
cardinality of `(Fin M × Fin M) × (Fin M × Fin M)`, i.e. exactly the normalisation of `avg`; the
passage from the norm of the sum of the (nonnegative real) level-`d` box sums to the sum of their
norms uses `pboxSum_real_nonneg`.
-/

/-- `‖((r : ℝ) : ℂ)‖ = |r|`. -/
private lemma norm_ofReal_abs (r : ℝ) : ‖((r : ℝ) : ℂ)‖ = |r| := by
  have h : ‖((r : ℝ) : ℂ)‖ ^ 2 = r ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq (z := ((r : ℝ) : ℂ)), Complex.normSq_ofReal]
    ring
  rw [← Real.sqrt_sq_eq_abs, ← Real.sqrt_sq (norm_nonneg ((r : ℝ) : ℂ)), h]

/-- A `Δ'`-difference of a finitely supported function is finitely supported. -/
private lemma DeltaP_finSupp {f : ℤ → ℂ} (hf : FinSuppZ f) (a b : ℤ) :
    FinSuppZ (DeltaP a b f) := by
  obtain ⟨N, hN⟩ := hf
  refine ⟨N + a.natAbs + b.natAbs, fun x hx => ?_⟩
  have hxa : ¬ ((x + a).natAbs ≤ N) := by
    intro hle
    have h1 : x.natAbs ≤ (x + a).natAbs + a.natAbs := by
      have h2 := Int.natAbs_add_le (x + a) (-a)
      rw [add_neg_cancel_right] at h2
      simpa [Int.natAbs_neg] using h2
    omega
  have h0 : f (x + a) = 0 := hN _ (by omega)
  rw [DeltaP, h0, star_zero, zero_mul]

/-- `catQ` is `Fin.append` read through the identification `Fin (s + s) ≃ Fin (2 * s)`. -/
private lemma catQ_eq_append {s : ℕ} (A B : Fin s → ℤ) :
    (fun k : Fin (2 * s) => Fin.append A B (Fin.cast (Nat.two_mul s) k)) = catQ A B := by
  funext k
  unfold catQ
  by_cases hk : k.val < s
  · rw [dif_pos hk]
    have hcast : Fin.cast (Nat.two_mul s) k = Fin.castAdd s ⟨k.val, hk⟩ :=
      Fin.ext (by simp [Fin.castAdd])
    rw [hcast, Fin.append_left]
  · rw [dif_neg hk]
    have hcast : Fin.cast (Nat.two_mul s) k = Fin.natAdd s ⟨k.val - s, by omega⟩ := by
      apply Fin.ext
      simp [Fin.natAdd, Fin.cast]
      omega
    rw [hcast, Fin.append_right]

/-- Relabelling the slot index of `pbox` along an equality `d = d'`. -/
private theorem pbox_finCongr' {d d' : ℕ} (h : d = d') (Q₁ Q₂ : Fin d → ℤ) (M : ℕ)
    (S : Finset ℤ) (F : ℤ → ℂ) :
    pbox d Q₁ Q₂ M S F
      = pbox d' (fun k => Q₁ (Fin.cast h.symm k)) (fun k => Q₂ (Fin.cast h.symm k)) M S F := by
  subst h
  rfl

/-- **Peeling the last slot of a box norm.**  For `1 ≤ d`, a box norm of the `d + 1` slots
`q₁, u` / `q₂, v` (with `u`, `v` appended at the end) is the average, over the `(2d + 2)`-tuple of
`Fin M`-indices, of the box norm of the `d` slots `q₁`, `q₂` applied to the kernel
`Δ'_{(pdir u v ·, pdir u v ·)} f`.  This is `pbox_peel` (which peels the first slot) after moving
the last slot to the front by the slot-rotation invariance `pbox_perm`. -/
theorem pbox_snoc_peel {d : ℕ} (hd : 1 ≤ d) (q₁ q₂ : Fin d → ℤ) (u v : ℤ) (M : ℕ)
    (S : Finset ℤ) (f : ℤ → ℂ) (hf : FinSuppZ f) :
    pbox (d + 1) (Fin.snoc q₁ u) (Fin.snoc q₂ v) M S f
      = avg (fun q : (Fin M × Fin M) × (Fin M × Fin M) =>
          pbox d q₁ q₂ M S (DeltaP (pdir u v q.1) (pdir u v q.2) f)) := by
  classical
  have hsnoc : pbox (d + 1) (Fin.snoc q₁ u) (Fin.snoc q₂ v) M S f
      = pbox (d + 1) (@Fin.cons d (fun _ : Fin (d + 1) => ℤ) u q₁)
          (@Fin.cons d (fun _ : Fin (d + 1) => ℤ) v q₂) M S f := by
    rw [Fin.snoc_eq_cons_rotate, Fin.snoc_eq_cons_rotate]
    exact pbox_perm (d + 1) (finRotate (d + 1))
      (@Fin.cons d (fun _ : Fin (d + 1) => ℤ) u q₁)
      (@Fin.cons d (fun _ : Fin (d + 1) => ℤ) v q₂) M S f
  have hpeel := pbox_peel d (@Fin.cons d (fun _ : Fin (d + 1) => ℤ) u q₁)
      (@Fin.cons d (fun _ : Fin (d + 1) => ℤ) v q₂) M S f
  have hpeel' : pboxSum (d + 1) (@Fin.cons d (fun _ : Fin (d + 1) => ℤ) u q₁)
        (@Fin.cons d (fun _ : Fin (d + 1) => ℤ) v q₂) M S f
      = ((M : ℂ) ^ 4)⁻¹ * ∑ m : Fin M × Fin M, ∑ m' : Fin M × Fin M,
          pboxSum d q₁ q₂ M S (DeltaP (pdir u v m) (pdir u v m') f) := by
    simpa only [Fin.cons_succ, Fin.cons_zero] using hpeel
  have hreal : ∀ m m' : Fin M × Fin M, ∃ r : ℝ, 0 ≤ r ∧
      pboxSum d q₁ q₂ M S (DeltaP (pdir u v m) (pdir u v m') f) = (r : ℂ) :=
    fun m m' => pboxSum_real_nonneg d hd q₁ q₂ M S _ (DeltaP_finSupp hf _ _)
  let r : Fin M × Fin M → Fin M × Fin M → ℝ := fun m m' => Classical.choose (hreal m m')
  have hr_spec : ∀ m m', 0 ≤ r m m' ∧
      pboxSum d q₁ q₂ M S (DeltaP (pdir u v m) (pdir u v m') f) = (r m m' : ℂ) :=
    fun m m' => Classical.choose_spec (hreal m m')
  have hZnorm : ‖∑ m : Fin M × Fin M, ∑ m' : Fin M × Fin M,
        pboxSum d q₁ q₂ M S (DeltaP (pdir u v m) (pdir u v m') f)‖
      = ∑ m : Fin M × Fin M, ∑ m' : Fin M × Fin M,
        pbox d q₁ q₂ M S (DeltaP (pdir u v m) (pdir u v m') f) := by
    have hZeq : (∑ m : Fin M × Fin M, ∑ m' : Fin M × Fin M,
          pboxSum d q₁ q₂ M S (DeltaP (pdir u v m) (pdir u v m') f))
        = ((∑ m : Fin M × Fin M, ∑ m' : Fin M × Fin M, r m m' : ℝ) : ℂ) := by
      rw [Complex.ofReal_sum]
      refine Finset.sum_congr rfl (fun m _ => ?_)
      rw [Complex.ofReal_sum]
      exact Finset.sum_congr rfl (fun m' _ => (hr_spec m m').2)
    rw [hZeq, norm_ofReal_abs, abs_of_nonneg (Finset.sum_nonneg (fun m _ =>
      Finset.sum_nonneg (fun m' _ => (hr_spec m m').1)))]
    refine Finset.sum_congr rfl (fun m _ => Finset.sum_congr rfl (fun m' _ => ?_))
    show r m m' = ‖pboxSum d q₁ q₂ M S (DeltaP (pdir u v m) (pdir u v m') f)‖
    rw [(hr_spec m m').2, norm_ofReal_abs, abs_of_nonneg (hr_spec m m').1]
  have hnormc : ‖((M : ℂ) ^ 4)⁻¹‖ = ((M : ℝ) ^ 4)⁻¹ := by
    rw [norm_inv, norm_pow, Complex.norm_natCast]
  have hcardXX : ((Fintype.card ((Fin M × Fin M) × (Fin M × Fin M)) : ℝ))⁻¹
      = ((M : ℝ) ^ 4)⁻¹ := by
    have hc : (Fintype.card ((Fin M × Fin M) × (Fin M × Fin M)) : ℝ) = (M : ℝ) ^ 4 := by
      simp only [Fintype.card_prod, Fintype.card_fin]
      push_cast
      ring
    rw [hc]
  calc pbox (d + 1) (Fin.snoc q₁ u) (Fin.snoc q₂ v) M S f
      = pbox (d + 1) (@Fin.cons d (fun _ : Fin (d + 1) => ℤ) u q₁)
          (@Fin.cons d (fun _ : Fin (d + 1) => ℤ) v q₂) M S f := hsnoc
    _ = ‖pboxSum (d + 1) (@Fin.cons d (fun _ : Fin (d + 1) => ℤ) u q₁)
          (@Fin.cons d (fun _ : Fin (d + 1) => ℤ) v q₂) M S f‖ := rfl
    _ = ‖((M : ℂ) ^ 4)⁻¹ * ∑ m : Fin M × Fin M, ∑ m' : Fin M × Fin M,
          pboxSum d q₁ q₂ M S (DeltaP (pdir u v m) (pdir u v m') f)‖ := by rw [hpeel']
    _ = ‖((M : ℂ) ^ 4)⁻¹‖ * ‖∑ m : Fin M × Fin M, ∑ m' : Fin M × Fin M,
          pboxSum d q₁ q₂ M S (DeltaP (pdir u v m) (pdir u v m') f)‖ := norm_mul _ _
    _ = ((M : ℝ) ^ 4)⁻¹ * (∑ m : Fin M × Fin M, ∑ m' : Fin M × Fin M,
          pbox d q₁ q₂ M S (DeltaP (pdir u v m) (pdir u v m') f)) := by rw [hnormc, hZnorm]
    _ = avg (fun q : (Fin M × Fin M) × (Fin M × Fin M) =>
          pbox d q₁ q₂ M S (DeltaP (pdir u v q.1) (pdir u v q.2) f)) := by
        rw [avg, hcardXX]
        congr 1
        conv_rhs => rw [Fintype.sum_prod_type]

theorem concatFinalIdent {I : Type} (s M N : ℕ) (hs : 1 ≤ s) (qH : I → ℤ)
    (q₁ q₂ : I → Fin s → ℤ) (p : I × I) (f : ℤ → ℂ) (hf : Work.Peluse.FinSuppZ f) :
    Work.Peluse.LadderP.Swap.pbox (s + s + 1)
        (Fin.snoc (Fin.append (q₁ p.1) (q₁ p.2)) (qH p.2))
        (Fin.snoc (Fin.append (q₂ p.1) (q₂ p.2)) (qH p.1)) M (Work.Peluse.symIcc N) f
      = Work.Peluse.LadderP.Swap.avg (fun q : (Fin M × Fin M) × (Fin M × Fin M) =>
          Work.Peluse.LadderP.Swap.pbox (2 * s) (Work.Peluse.SwapC.catQ (q₁ p.1) (q₁ p.2))
            (Work.Peluse.SwapC.catQ (q₂ p.1) (q₂ p.2)) M (Work.Peluse.symIcc N)
            (fun y => star (f (y + Work.Peluse.LadderP.Swap.pdir (qH p.2) (qH p.1) q.1))
              * f (y + Work.Peluse.LadderP.Swap.pdir (qH p.2) (qH p.1) q.2))) := by
  have key := pbox_snoc_peel (d := s + s) (by omega)
    (Fin.append (q₁ p.1) (q₁ p.2)) (Fin.append (q₂ p.1) (q₂ p.2))
    (qH p.2) (qH p.1) M (Work.Peluse.symIcc N) f hf
  rw [key]
  congr 1
  funext q
  rw [pbox_finCongr' (Nat.two_mul s).symm]
  rw [catQ_eq_append, catQ_eq_append]
  rfl

end Work.Peluse.SwapC
