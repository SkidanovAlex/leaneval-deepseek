/-
  WilG4cR / `LimcondFixMem` — a **clean** copy of
  `Work.WilkG4c.CritFixAux.limcond_fix_mem` (module
  `Submission/Work/WilG4c/CritFixAux/limcond_fix_mem.lean`).

  The original file contains a complete proof but does not elaborate, because it refers to
  `Work.WilkG4c.fibreLimitEqMem_pi`; the theorem lives in the namespace `Work.WilG4c`
  (`Submission/Work/WilG4c/fibreLimitEqMem_pi.lean`).  This copy repairs that reference and is
  used by the clean `Ω`-chain `uvfixGlue → CritFixMem → AlDgListSlice_mem` that
  `Submission/Work/WilG4c/FibreBadCoresR.lean` (the sharp fibre-cores statement) rests on.

  `LimCond p n f (m+1) c` is `ProjLim (dgSet p n f (m+1) (cntWord n (m+1) c))`: the punctured
  limit condition at order `m+1` with counts vector `c`.  The joint derivative graph `dgSet` is
  `Ω`-definable with a format/degree uniform in the order (`dgSet_mem`), the punctured-limit set
  `LimeqP` of an `Ω`-set is `Ω`-definable (`fibreLimitEqMem_pi`), and the degree polynomial is
  the substitution `bL.eval₂ C bD` so that the index bound `k` dominates every order `m ≤ k`.
-/
import Mathlib
import Submission.Work.WilG4c.AlSliceBase
import Submission.Work.WilG4c.CritMem
import Submission.Work.WilG4c.fibreLimitEqMem_pi
import Submission.Work.WilG4c.CritFixAux.critIdxFixCard
import Submission.Work.WilG1.Basic

set_option autoImplicit false
noncomputable section
open Classical

namespace Work.WilG4cR

open WilkiesDesign

theorem limcond_fix_mem (S : WilkiesDesign.SOMin) (hder : WilkiesDesign.SOMin.SharpDeriv S)
    (p n F0 : ℕ) :
    ∃ (a : ℕ) (b : MvPolynomial (Fin 2) ℕ), ∀ (D k : ℕ)
      (f : (Fin p → ℝ) → (Fin (n + 1) → ℝ) → ℝ)
      (i : Σ m : Fin k, Fin (n + 1) → Fin (m.val + 2)),
      WilkiesDesign.CG.famGraph f ∈ S.Ω F0 D (p + (n + 1) + 1) →
      Work.WilkG4c.LimCond p n f (i.1.val + 1) (fun j => (i.2 j).val) ∈
        S.Ω a (MvPolynomial.eval ![D, k] b) (p + (n + 1)) := by
  obtain ⟨aD, bD, hD⟩ := Work.WilkG4c.dgSet_mem S hder p n F0
  obtain ⟨aL, bL, hL⟩ := Work.WilG4c.fibreLimitEqMem_pi (S := S) (p := p) (n := n)
  refine ⟨aD + aL + 1, bL.eval₂ MvPolynomial.C bD, ?_⟩
  intro D k f i hf
  set c : Fin (n + 1) → ℕ := fun j => (i.2 j).val with hc
  have hm : i.1.val + 1 ≤ k := by have := i.1.isLt; omega
  have hdg : Work.WilkG4c.dgSet p n f (i.1.val + 1) (Work.WilkG4c.cntWord n (i.1.val + 1) c) ∈
      S.Ω aD (MvPolynomial.eval ![D, i.1.val + 1] bD) (p + (n + 1) + 1) :=
    hD D f hf (i.1.val + 1) (Work.WilkG4c.cntWord n (i.1.val + 1) c)
  have hdeg : bL.eval (MvPolynomial.eval ![D, i.1.val + 1] bD) ≤
      MvPolynomial.eval ![D, k] (bL.eval₂ MvPolynomial.C bD) := by
    have h1 : MvPolynomial.eval ![D, i.1.val + 1] (bL.eval₂ MvPolynomial.C bD) ≤
        MvPolynomial.eval ![D, k] (bL.eval₂ MvPolynomial.C bD) :=
      Work.WilkG4c.CritFixAux.eval_pair_mono _ le_rfl hm
    simp only [Work.WilkG4c.eval_eval₂] at h1
    simpa only [Work.WilkG4c.eval_eval₂] using h1
  have hLimeq := hL (Work.WilkG4c.dgSet p n f (i.1.val + 1)
    (Work.WilkG4c.cntWord n (i.1.val + 1) c)) hdg
  have hmono := Work.WilG1.Omega.mono hLimeq (le_refl (aD + aL)) hdeg
  have hproj := S.proj hmono
  show Work.WilkG4c.LimCond p n f (i.1.val + 1) (fun j => (i.2 j).val) ∈
    S.Ω (aD + aL + 1) (MvPolynomial.eval ![D, k] (bL.eval₂ MvPolynomial.C bD)) (p + (n + 1))
  rw [show Work.WilkG4c.LimCond p n f (i.1.val + 1) (fun j => (i.2 j).val)
      = WilkiesDesign.projLast (Work.WilG4c.LimeqP p n
          (Work.WilkG4c.dgSet p n f (i.1.val + 1) (Work.WilkG4c.cntWord n (i.1.val + 1) c)))
      from rfl]
  exact hproj

end Work.WilG4cR
