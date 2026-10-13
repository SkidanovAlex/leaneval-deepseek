import Mathlib
import Submission.Work.WilCruxN.DerivGraphClean
import Submission.Work.WilCrux.failSet_mem

namespace Work.WilCruxN

/-
  Port of `Work.WilCrux.failSet_mem` (`Submission/Work/WilCrux/failSet_mem.lean`) with the
  direction `j` FIXED (so the bounds may depend on `j`) and with `hder : S.SharpDeriv` replaced by
  `hcd : S.SharpCD`.

  The source proves `∃ A q, ∀ j, {u | 0 < u (last a) ∧ Fin.init u ∈ failSet G j (u (last a))}
  ∈ S.Ω A (q.eval D) (a+1)` from `S.SharpDeriv`.  Its ONLY use of `hder` is

    `obtain ⟨a0, b0, hb0⟩ := Work.WilG4b.derivGraph_mem S hder (a + b) F`
    `have hT := hb0 D (Work.WilG4c.famFun G) (Fin.natAdd a j) hGf`   -- b0 : MvPolynomial (Fin 2) ℕ

  The replacement is `Work.WilCruxN.derivGraph_mem_clean S hcd (f := Work.WilG4c.famFun G)
  (i := Fin.natAdd a j) hf`, with `hf : graphOf (famFun G) ∈ S.Ω F D (a+b+1)` coming from
  `hG` via `Work.WilG4c.graphOf_famFun`; it returns a format `a0` and a *monovariate* polynomial
  `b0 : Polynomial ℕ` with `derivGraph (famFun G) (Fin.natAdd a j) ∈ S.Ω a0 (b0.eval D) (a+b+1)`.
  The rest of the source proof is unchanged: `Work.WilCrux.fmChain_mem S T (F0 := a0)
  (degT := b0.eval D) hT` needs exactly a set `T` with an `Ω`-membership of that shape, and
  `fmChain_eq_target G j` turns `fmChain a b T` into the target set.  The final degree bookkeeping
  just replaces `(Work.WilG1.psubst b0 1).eval D` by `b0.eval D`, so the stated polynomial is
  `Polynomial.C 2 * b0 + Polynomial.C (10000 * (a + b) + 100000)` (compare the source, which
  rewrote `((Polynomial.C 2 * Polynomial.X + Polynomial.C (10000*(a+b)+100000)).eval
  ((psubst b0 1).eval D))`).
-/
theorem FailSetMemPerJ (S : WilkiesDesign.SOMin) (hcd : S.SharpCD) {a b F D : ℕ}
    (G : (Fin a → ℝ) → (Fin b → ℝ) → ℝ)
    (hG : WilkiesDesign.CG.famGraph G ∈ S.Ω F D (a + b + 1)) (j : Fin b) :
    ∃ (A : ℕ) (q : Polynomial ℕ),
      {u : Fin (a + 1) → ℝ | 0 < u (Fin.last a) ∧
        Fin.init u ∈ Work.WilCrux.failSet G j (u (Fin.last a))} ∈ S.Ω A (q.eval D) (a + 1) := by
  -- `graphOf (famFun G) = famGraph G`, so the hypothesis has the shape `derivGraph_mem_clean` wants
  have hGf : WilkiesDesign.graphOf (Work.WilG4c.famFun G) ∈ S.Ω F D (a + b + 1) := by
    rw [Work.WilG4c.graphOf_famFun]; exact hG
  -- the order-one derivative graph is `Ω`-definable from `SharpCD` alone
  obtain ⟨a0, b0, hT⟩ :=
    derivGraph_mem_clean (S := S) (hcd := hcd) (m := a + b) (F0 := F) (D := D)
      (f := Work.WilG4c.famFun G) (i := Fin.natAdd a j) hGf
  refine ⟨a0 + (500 * (a + b) + 5000),
    Polynomial.C 2 * b0 + Polynomial.C (10000 * (a + b) + 100000), ?_⟩
  -- the chain construction applied to the derivative graph
  have hmem := Work.WilCrux.fmChain_mem (S := S) (a := a) (b := b)
    (Work.WilG4b.derivGraph (Work.WilG4c.famFun G) (Fin.natAdd a j))
    (F0 := a0) (degT := b0.eval D) hT
  rw [Work.WilCrux.fmChain_eq_target G j] at hmem
  -- degree bookkeeping
  have hdeg : ((Polynomial.C 2 * Polynomial.X + Polynomial.C (10000 * (a + b) + 100000)).eval
        (b0.eval D)) =
      ((Polynomial.C 2 * b0 + Polynomial.C (10000 * (a + b) + 100000)).eval D) := by
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
  rw [hdeg] at hmem
  exact hmem

end Work.WilCruxN
