import Mathlib
import Submission.Work.Peluse.SwapC.concatDefs
import Submission.Work.Peluse.SwapC.concatFinalIdent
import Submission.Work.Peluse.SwapC.mCubeSumNormDeltaNeg

namespace Work.Peluse.SwapC

open scoped BigOperators
open Work.Peluse Work.Peluse.LadderP.Swap

/-- The reordering `(a₀, a₀', a₁, a₁') ↦ ((a₁, a₀), (a₁', a₀'))` of the four *raw* indices, which
carries the difference `rawIncr qH p.2 a₁ a₁' - rawIncr qH p.1 a₀ a₀'` of the `Zm`-kernel to the
difference `pdir (qH p.2) (qH p.1) q₂ - pdir (qH p.2) (qH p.1) q₁` of the concatenated kernel. -/
private def quadIdx (M : ℕ) :
    (Fin M × Fin M × Fin M × Fin M) ≃ ((Fin M × Fin M) × (Fin M × Fin M)) where
  toFun j := ((j.2.2.1, j.1), (j.2.2.2, j.2.1))
  invFun q := (q.1.2, q.2.2, q.1.1, q.2.1)
  left_inv j := by rcases j with ⟨a, b, c, d⟩; rfl
  right_inv q := by rcases q with ⟨⟨m₁, m₂⟩, ⟨m₁', m₂'⟩⟩; rfl

theorem peelBack {I : Type} [Fintype I] (s M N : ℕ) (hs : 1 ≤ s) (qH : I → ℤ)
    (q₁ q₂ : I → Fin s → ℤ) (p : I × I) (f : ℤ → ℂ) (hf : Work.Peluse.FinSuppZ f) :
    Work.Peluse.LadderP.Swap.avg (fun j : Fin M × Fin M × Fin M × Fin M =>
        Work.Peluse.SwapC.Zm s M N qH q₁ q₂ f p.1 p.2 j.1 j.2.1 j.2.2.1 j.2.2.2)
      = Work.Peluse.LadderP.Swap.pbox (s + s + 1)
          (Fin.snoc (Fin.append (q₁ p.1) (q₁ p.2)) (qH p.2))
          (Fin.snoc (Fin.append (q₂ p.1) (q₂ p.2)) (qH p.1)) M (Work.Peluse.symIcc N) f := by
  -- Peeling the concatenated (last) slot of the `2s + 1`-fold box produces the average over the
  -- pairs `((m, m'), (n, n'))` of the `2s`-fold box of the kernel
  -- `conj (f (· + pdir (qH p.2) (qH p.1) (m, m'))) · f (· + pdir (qH p.2) (qH p.1) (n, n'))`.
  rw [concatFinalIdent s M N hs qH q₁ q₂ p f hf]
  simp only [pbox_catQ]
  rw [Work.Peluse.LadderP.Swap.avg, Work.Peluse.LadderP.Swap.avg]
  -- The `Zm`-kernel has the *raw* increments `rawIncr qH p.1 a₀ a₀'` and `rawIncr qH p.2 a₁ a₁'`;
  -- after the reordering `quadIdx` the two kernels have increments whose differences are opposite.
  have hpoint : ∀ j : Fin M × Fin M × Fin M × Fin M,
      Zm s M N qH q₁ q₂ f p.1 p.2 j.1 j.2.1 j.2.2.1 j.2.2.2
        = ‖mCubeSum (2 * s) (Fin M × Fin M)
            (catDir M (q₁ p.1) (q₂ p.1) (q₁ p.2) (q₂ p.2)) (symIcc N)
            (fun _ y => star (f (y + pdir (qH p.2) (qH p.1) (quadIdx M j).1)) *
              f (y + pdir (qH p.2) (qH p.1) (quadIdx M j).2))‖ := by
    intro j
    have h₁ : (quadIdx M j).1 = (j.2.2.1, j.1) := rfl
    have h₂ : (quadIdx M j).2 = (j.2.2.2, j.2.1) := rfl
    rw [h₁, h₂]
    simp only [Zm]
    exact mCubeSumNormDeltaNeg _ _ f _ _ _ _
      (by simp only [rawIncr, Work.Peluse.LadderP.Swap.pdir]; ring)
  have hsum : (∑ j : Fin M × Fin M × Fin M × Fin M,
        Zm s M N qH q₁ q₂ f p.1 p.2 j.1 j.2.1 j.2.2.1 j.2.2.2)
      = ∑ q : (Fin M × Fin M) × (Fin M × Fin M),
          ‖mCubeSum (2 * s) (Fin M × Fin M)
              (catDir M (q₁ p.1) (q₂ p.1) (q₁ p.2) (q₂ p.2)) (symIcc N)
              (fun _ y => star (f (y + pdir (qH p.2) (qH p.1) q.1)) *
                f (y + pdir (qH p.2) (qH p.1) q.2))‖ :=
    Fintype.sum_equiv (quadIdx M)
      (fun j : Fin M × Fin M × Fin M × Fin M =>
        Zm s M N qH q₁ q₂ f p.1 p.2 j.1 j.2.1 j.2.2.1 j.2.2.2)
      (fun q : (Fin M × Fin M) × (Fin M × Fin M) =>
        ‖mCubeSum (2 * s) (Fin M × Fin M)
            (catDir M (q₁ p.1) (q₂ p.1) (q₁ p.2) (q₂ p.2)) (symIcc N)
            (fun _ y => star (f (y + pdir (qH p.2) (qH p.1) q.1)) *
              f (y + pdir (qH p.2) (qH p.1) q.2))‖)
      (fun j => hpoint j)
  have hcard : (Fintype.card (Fin M × Fin M × Fin M × Fin M) : ℝ)
      = (Fintype.card ((Fin M × Fin M) × (Fin M × Fin M)) : ℝ) := by
    simp only [Fintype.card_prod, Fintype.card_fin]
    push_cast
    ring
  rw [hcard, hsum]

end Work.Peluse.SwapC
