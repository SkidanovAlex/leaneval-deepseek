import Mathlib
import Submission.Work.Peluse.SwapC.pboxSum_peel_iter
import Submission.Work.Peluse.SwapC.pbox_eq_re

/-!
# Peeling a block of slots out of `pbox`: the block identity

`pbox (d + e) (Fin.append P₁ R₁) (Fin.append P₂ R₂) M S F` is the box norm (`‖pboxSum‖`) of
order `d + e` whose first `d` slots carry the coefficients `P` and whose last `e` slots carry the
coefficients `R`.  Since `pboxSum` is a *nonnegative real* (for a finitely supported `F`), the peel
identity of `pboxSum_peel_iter` survives the passage to norms: the level-`(d+e)` box norm is the
average, over the `d`-tuples of slot indices `h, h'`, of the level-`e` box norm of the iterated
`Δ'`-difference `iterDeltaP d` taken along the `P`-directions.

The two ingredients are

* `pboxSum_peel_iter` (`d` successive single-slot peels of `pboxSum`), and
* `pboxSum_real_nonneg` / `pbox_eq_re`: the peeled `pboxSum`s are nonnegative reals, so the
  modulus of their sum is the sum of their moduli — this is the step where the triangle
  inequality becomes an equality.
-/

open scoped BigOperators

namespace Work.Peluse.SwapC

noncomputable section

open Work.Peluse
open Work.Peluse.LadderP.Swap

/-! ## Finite support is preserved by `iterDeltaP` -/

private lemma finSuppZ_DeltaP {a b : ℤ} {G : ℤ → ℂ} (h : Work.Peluse.FinSuppZ G) :
    Work.Peluse.FinSuppZ (Work.Peluse.DeltaP a b G) := by
  obtain ⟨N, hN⟩ := h
  refine ⟨N + a.natAbs + b.natAbs, fun x hx => ?_⟩
  have hxa : G (x + a) = 0 := by
    refine hN _ ?_
    have htri : x.natAbs ≤ (x + a).natAbs + a.natAbs := by
      have h := Int.natAbs_add_le (x + a) (-a)
      rw [Int.natAbs_neg] at h
      simpa using h
    omega
  simp [Work.Peluse.DeltaP, hxa]

private lemma finSuppZ_iterDeltaP : ∀ (k : ℕ) (sh : Fin k → ℤ × ℤ) (F : ℤ → ℂ),
    Work.Peluse.FinSuppZ F → Work.Peluse.FinSuppZ (Work.Peluse.SwapC.iterDeltaP k sh F) := by
  intro k
  induction k with
  | zero => intro sh F h; exact h
  | succ k ih =>
      intro sh F h
      rw [Work.Peluse.SwapC.iterDeltaP_succ_eq]
      exact finSuppZ_DeltaP (ih (fun i => sh i.succ) F h)

/-! ## The normalising constant of the peel -/

/-- The peel prefactor `((M^4)⁻¹)^d` is the inverse of the number of `d`-tuples of slot indices,
i.e. exactly the normalisation of `avg` over the pairs of shift tuples. -/
private lemma peelConst (d M : ℕ) :
    (((M : ℂ) ^ 4)⁻¹) ^ d
      = Complex.ofReal
          ((Fintype.card ((Fin d → Fin M × Fin M) × (Fin d → Fin M × Fin M)) : ℝ)⁻¹) := by
  have hA : Fintype.card (Fin d → Fin M × Fin M) = M ^ (2 * d) := by
    simp only [Fintype.card_fun, Fintype.card_prod, Fintype.card_fin]
    rw [← pow_two, ← pow_mul]
  have hcard : Fintype.card ((Fin d → Fin M × Fin M) × (Fin d → Fin M × Fin M))
      = M ^ (4 * d) := by
    rw [Fintype.card_prod, hA]
    rw [← pow_two, ← pow_mul]
    congr 1
    omega
  rw [inv_pow, ← pow_mul, ← Nat.cast_pow, ← hcard, Complex.ofReal_inv, Complex.ofReal_natCast]

/-! ## The complex peel identity -/

/-- **The complex peel identity**: `d` successive single-slot peels of `pboxSum (d+e)`, followed
by the observation that the prefactor `((M^4)⁻¹)^d` is the inverse of the number of shift tuples
and that the coefficient tuples `Fin.append P R (Fin.natAdd d ·)` and the shifts
`pdir (Fin.append P R (Fin.castAdd e ·))` restrict to `R` and `pdir P` respectively. -/
private lemma peelComplex {d e : ℕ} (P₁ P₂ : Fin d → ℤ) (R₁ R₂ : Fin e → ℤ) (M : ℕ)
    (S : Finset ℤ) (F : ℤ → ℂ) :
    pboxSum (d + e) (Fin.append P₁ R₁) (Fin.append P₂ R₂) M S F
      = Complex.ofReal
            ((Fintype.card ((Fin d → Fin M × Fin M) × (Fin d → Fin M × Fin M)) : ℝ)⁻¹) *
        ∑ p : (Fin d → Fin M × Fin M) × (Fin d → Fin M × Fin M),
          pboxSum e R₁ R₂ M S
            (iterDeltaP d (fun j => (pdir (P₁ j) (P₂ j) (p.1 j),
                                     pdir (P₁ j) (P₂ j) (p.2 j))) F) := by
  rw [pboxSum_peel_iter d e (Fin.append P₁ R₁) (Fin.append P₂ R₂) M S F, peelConst d M]
  congr 1
  simp only [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun h _ => Finset.sum_congr rfl fun h' _ => ?_
  have h₁ : (fun i : Fin e => Fin.append P₁ R₁ (Fin.natAdd d i)) = R₁ :=
    funext fun i => Fin.append_right P₁ R₁ i
  have h₂ : (fun i : Fin e => Fin.append P₂ R₂ (Fin.natAdd d i)) = R₂ :=
    funext fun i => Fin.append_right P₂ R₂ i
  have hsh : (fun j : Fin d =>
        (pdir (Fin.append P₁ R₁ (Fin.castAdd e j)) (Fin.append P₂ R₂ (Fin.castAdd e j)) (h j),
         pdir (Fin.append P₁ R₁ (Fin.castAdd e j)) (Fin.append P₂ R₂ (Fin.castAdd e j)) (h' j)))
      = (fun j : Fin d => (pdir (P₁ j) (P₂ j) (h j), pdir (P₁ j) (P₂ j) (h' j))) := by
    funext j
    rw [Fin.append_left, Fin.append_left]
  rw [h₁, h₂]
  exact congrArg (fun sh : Fin d → ℤ × ℤ => pboxSum e R₁ R₂ M S (iterDeltaP d sh F)) hsh

/-! ## The block identity for `pbox` -/

theorem pboxPeelBlocks {d e : ℕ} (he : 1 ≤ e) (P₁ P₂ : Fin d → ℤ) (R₁ R₂ : Fin e → ℤ) (M : ℕ)
    (S : Finset ℤ) (F : ℤ → ℂ) (hF : Work.Peluse.FinSuppZ F) :
    Work.Peluse.LadderP.Swap.pbox (d + e) (Fin.append P₁ R₁) (Fin.append P₂ R₂) M S F
      = Work.Peluse.LadderP.Swap.avg
          (fun p : (Fin d → Fin M × Fin M) × (Fin d → Fin M × Fin M) =>
          Work.Peluse.LadderP.Swap.pbox e R₁ R₂ M S
            (Work.Peluse.SwapC.iterDeltaP d (fun j =>
                (Work.Peluse.LadderP.Swap.pdir (P₁ j) (P₂ j) (p.1 j),
                 Work.Peluse.LadderP.Swap.pdir (P₁ j) (P₂ j) (p.2 j))) F)) := by
  have hsum : (∑ p : (Fin d → Fin M × Fin M) × (Fin d → Fin M × Fin M),
        pboxSum e R₁ R₂ M S
          (iterDeltaP d (fun j => (pdir (P₁ j) (P₂ j) (p.1 j),
                                   pdir (P₁ j) (P₂ j) (p.2 j))) F))
      = Complex.ofReal
          (∑ p : (Fin d → Fin M × Fin M) × (Fin d → Fin M × Fin M),
            pbox e R₁ R₂ M S
              (iterDeltaP d (fun j => (pdir (P₁ j) (P₂ j) (p.1 j),
                                       pdir (P₁ j) (P₂ j) (p.2 j))) F)) := by
    rw [Complex.ofReal_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [pbox_eq_re e he R₁ R₂ M S _
      (finSuppZ_iterDeltaP d (fun j => (pdir (P₁ j) (P₂ j) (p.1 j),
        pdir (P₁ j) (P₂ j) (p.2 j))) F hF)]
    obtain ⟨r, hr, hZr⟩ :=
      pboxSum_real_nonneg e he R₁ R₂ M S _
        (finSuppZ_iterDeltaP d (fun j => (pdir (P₁ j) (P₂ j) (p.1 j),
          pdir (P₁ j) (P₂ j) (p.2 j))) F hF)
    simp only [hZr, Complex.ofReal_re]
  have hmain : pboxSum (d + e) (Fin.append P₁ R₁) (Fin.append P₂ R₂) M S F
      = Complex.ofReal
          ((Fintype.card ((Fin d → Fin M × Fin M) × (Fin d → Fin M × Fin M)) : ℝ)⁻¹ *
            ∑ p : (Fin d → Fin M × Fin M) × (Fin d → Fin M × Fin M),
              pbox e R₁ R₂ M S
                (iterDeltaP d (fun j => (pdir (P₁ j) (P₂ j) (p.1 j),
                                         pdir (P₁ j) (P₂ j) (p.2 j))) F)) := by
    rw [peelComplex P₁ P₂ R₁ R₂ M S F, hsum, ← Complex.ofReal_mul]
  calc pbox (d + e) (Fin.append P₁ R₁) (Fin.append P₂ R₂) M S F
      = (pboxSum (d + e) (Fin.append P₁ R₁) (Fin.append P₂ R₂) M S F).re :=
        pbox_eq_re (d + e) (by omega) (Fin.append P₁ R₁) (Fin.append P₂ R₂) M S F hF
    _ = (Fintype.card ((Fin d → Fin M × Fin M) × (Fin d → Fin M × Fin M)) : ℝ)⁻¹ *
          ∑ p : (Fin d → Fin M × Fin M) × (Fin d → Fin M × Fin M),
            pbox e R₁ R₂ M S
              (iterDeltaP d (fun j => (pdir (P₁ j) (P₂ j) (p.1 j),
                                       pdir (P₁ j) (P₂ j) (p.2 j))) F) := by
        rw [hmain, Complex.ofReal_re]
    _ = avg (fun p : (Fin d → Fin M × Fin M) × (Fin d → Fin M × Fin M) =>
            pbox e R₁ R₂ M S
              (iterDeltaP d (fun j => (pdir (P₁ j) (P₂ j) (p.1 j),
                                       pdir (P₁ j) (P₂ j) (p.2 j))) F)) :=
        (avg_eq_inv_card_mul _).symm

end

end Work.Peluse.SwapC
