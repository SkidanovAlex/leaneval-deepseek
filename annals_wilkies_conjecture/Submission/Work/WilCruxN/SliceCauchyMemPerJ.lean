import Mathlib
import Submission.Work.WilCruxN.DerivGraphClean
import Submission.Work.WilCrux.sliceCauchy_mem

namespace Work.WilCruxN

/-
  Port of `Work.WilCrux.sliceCauchy_mem` (`Submission/Work/WilCrux/sliceCauchy_mem.lean`) with the
  direction `j` FIXED (so the bounds may depend on `j`) and with `hder : S.SharpDeriv` replaced by
  `hcd : S.SharpCD`.

  The source file proves `∃ A q, ∀ j k ε, sliceCauchySet G j k ε ∈ S.Ω A (q.eval D) a` assuming
  `S.SharpDeriv`.  The ONLY use of `S.SharpDeriv` there is
  `scb_derivGraph_mem S hder (a + b) F`, which produces a format `aDer` and a *bivariate*
  polynomial `bDer` (with `((Work.WilG1.psubst bDer 1).eval D)` as degree) such that
  `derivGraph (famFun G) (Fin.natAdd a j) ∈ S.Ω aDer ((psubst bDer 1).eval D) (a+b+1)` for every
  `j`.  The replacement is available: `Work.WilCruxN.derivGraph_mem_clean S hcd` applied to
  `f := Work.WilG4c.famFun G`, `i := Fin.natAdd a j` and
  `hf : graphOf (famFun G) ∈ S.Ω F D (a+b+1)` (from `Work.WilG4c.graphOf_famFun`) gives
  `∃ a₀ b₀ : Polynomial ℕ, derivGraph (famFun G) (Fin.natAdd a j) ∈ S.Ω a₀ (b₀.eval D) (a+b+1)`.
  With `aDer := a₀`, `degT := b₀.eval D` the rest of the source proof is unchanged: the three
  constituent `Ω`-memberships `SCBig.core_mem`, `SCBig.hyp_mem`, `SCBig.thresh_mem` are already
  independent of the format/degree of the derivative graph, and the final format/degree arithmetic
  must simply be redone with the *monovariate* polynomial `b₀` in place of the bivariate `bDer`
  (no `Work.WilG1.psubst` is needed any more).
-/
theorem SliceCauchyMemPerJ (S : WilkiesDesign.SOMin) (hcd : S.SharpCD) {a b F D : ℕ}
    (G : (Fin a → ℝ) → (Fin b → ℝ) → ℝ)
    (hG : WilkiesDesign.CG.famGraph G ∈ S.Ω F D (a + b + 1)) (j : Fin b) :
    ∃ (A : ℕ) (q : Polynomial ℕ), ∀ (k : ℕ) (ε : ℝ),
      Work.WilCrux.sliceCauchySet G j k ε ∈ S.Ω A (q.eval D) a := by
  -- The graph of `famFun G` is `famGraph G`.
  have hgf : WilkiesDesign.graphOf (Work.WilG4c.famFun G) ∈ S.Ω F D (a + b + 1) := by
    rwa [Work.WilG4c.graphOf_famFun]
  -- The derivative graph in the (fixed) direction `j`; the bounds may depend on `j`.
  obtain ⟨aDer, bDer, hT⟩ :=
    derivGraph_mem_clean S hcd (Work.WilG4c.famFun G) (Fin.natAdd a j) hgf
  -- The three constituent `Ω`-memberships, independent of `j`.
  obtain ⟨Ac, qc, hcm⟩ := Work.WilCrux.SCBig.core_mem S a b
  obtain ⟨Ah, qh, hhm⟩ := Work.WilCrux.SCBig.hyp_mem S a b
  obtain ⟨At, qt, htm⟩ := Work.WilCrux.SCBig.thresh_mem S a
  refine ⟨max (max ((aDer + Ac) + 2 + 1) Ah + 1 + (b + b) + 1) At + 1 + 1,
    (qc.comp bDer + qh) + qt, ?_⟩
  intro k ε
  rw [← Work.WilCrux.bigSet_eq]
  rw [Work.WilCrux.bigSet]
  -- the core set
  have hcore : Work.WilCrux.coreSet (a := a) (b := b)
      (Work.WilG4b.derivGraph (Work.WilG4c.famFun G) (Fin.natAdd a j)) ε ∈ S.Ω (aDer + Ac)
      ((qc.comp bDer).eval D) (((a + 1) + (b + b)) + 2) := by
    simpa [Polynomial.eval_comp] using
      hcm aDer (bDer.eval D)
        (Work.WilG4b.derivGraph (Work.WilG4c.famFun G) (Fin.natAdd a j)) ε hT
  -- project away `y, y'` and complement
  have h1 := Work.WilG5.projN_mem (S := S) (n := (a + 1) + (b + b)) 2 (aDer + Ac) _ hcore
  have h2 := S.compl h1
  -- intersect with the hypothesis set
  have hhyp : Work.WilCrux.hypSet (a := a) (b := b) ∈ S.Ω Ah (qh.eval D) ((a + 1) + (b + b)) :=
    hhm D
  have h3 := Work.WilG1.Omega.inter₂ h2 hhyp
  rw [Set.inter_comm] at h3
  -- project away `z, z'` and complement
  have h4 := Work.WilG5.projN_mem (S := S) (n := a + 1) (b + b) _ _ h3
  have h5 := S.compl h4
  -- intersect with the threshold set
  have hthr : Work.WilCrux.threshSet (a := a) k ∈ S.Ω At (qt.eval D) (a + 1) := htm k D
  have h6 := Work.WilG1.Omega.inter₂ h5 hthr
  rw [Set.inter_comm] at h6
  -- project away `η`
  exact Work.WilG5.projN_mem (S := S) (n := a) 1 _ _ h6

end Work.WilCruxN
