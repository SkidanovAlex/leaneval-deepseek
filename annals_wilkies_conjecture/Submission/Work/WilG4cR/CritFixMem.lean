/-
  WilG4cR / `CritFixMem` — a **clean** copy of `Work.WilkG4c.CritFixMem`
  (`Submission/Work/WilG4c/CritFixMem.lean`), which is `sorry`-free but rests on the
  `sorry`-stubs `CritAux.hypoRaw_mem` (through the equality stubs) and
  `CritFixAux.finset_inter_mem`, and on the non-building `limcond_fix_mem`.  The copy below uses
  the clean chain `Work.WilG4cR.uvfixGlue` → `Work.WilG4cR.limcond_fix_mem`,
  `Work.WilG4cR.finset_inter_mem`, `Work.WilG4cR.hypoRaw_mem`.

  `CritFix p n f L = LocCritFix ∩ LimeqP (dgSet p n f |L| L.get)` is the corrected punctured-limit
  criterion; `LocCritFix` is definitionally the product of `HypoRaw (UVFix …)` with a free value
  coordinate, and the value half is `LimeqP` of the joint derivative graph `dgSet`, both
  `Ω`-definable (`fibreLimitEqMem_pi`, `dgSet_mem`).
-/
import Mathlib
import Submission.Work.Wilkies.Defs
import Submission.Work.WilG4c.AlSliceBase
import Submission.Work.WilG4c.CritFixDefs
import Submission.Work.WilG4c.CritMem
import Submission.Work.WilG4c.fibreLimitEqMem_pi
import Submission.Work.WilG4cR.HypoRawMem
import Submission.Work.WilG4cR.UvfixGlue

set_option autoImplicit false
noncomputable section
open Classical

namespace Work.WilG4cR

open WilkiesDesign WilkiesDesign.CG

/-- `LocCritFix` is the product of `HypoRaw (UVFix …)` with a free last coordinate
(definitionally). -/
theorem locCritFix_eq (p n : ℕ) (f : (Fin p → ℝ) → (Fin (n + 1) → ℝ) → ℝ)
    (L : List (Fin (n + 1))) :
    Work.WilkG4c.LocCritFix p n f L
      = {z : Fin (p + (n + 1) + 1) → ℝ |
          Fin.init z ∈ Work.WilkG4c.HypoRaw p n (Work.WilkG4c.UVFix p n f L.length)} :=
  rfl

/-- `CritFix` is that product intersected with the `LimeqP` of the joint derivative graph
along `L` (definitionally). -/
theorem critFix_eq (p n : ℕ) (f : (Fin p → ℝ) → (Fin (n + 1) → ℝ) → ℝ)
    (L : List (Fin (n + 1))) :
    Work.WilkG4c.CritFix p n f L
      = {z : Fin (p + (n + 1) + 1) → ℝ |
          Fin.init z ∈ Work.WilkG4c.HypoRaw p n (Work.WilkG4c.UVFix p n f L.length)}
        ∩ Work.WilG4c.LimeqP p n (Work.WilkG4c.dgSet p n f L.length (fun j => L.get j)) :=
  rfl

/-- **`CritFix` is `Ω`-definable**, with format uniform in `|L|` and degree a polynomial in
`(D, |L|)`. -/
theorem CritFixMem (S : WilkiesDesign.SOMin) (hder : WilkiesDesign.SOMin.SharpDeriv S)
    (p n F0 : ℕ) :
    ∃ (a : ℕ) (b : MvPolynomial (Fin 2) ℕ),
      ∀ (D : ℕ) (f : (Fin p → ℝ) → (Fin (n + 1) → ℝ) → ℝ) (L : List (Fin (n + 1))),
        WilkiesDesign.CG.famGraph f ∈ S.Ω F0 D (p + (n + 1) + 1) →
        Work.WilkG4c.CritFix p n f L ∈
          S.Ω a (MvPolynomial.eval ![D, L.length] b) (p + (n + 1) + 1) := by
  obtain ⟨aU, bU, hU⟩ := Work.WilG4cR.uvfixGlue S hder p n F0
  obtain ⟨aH, bH, hH⟩ := Work.WilG4cR.hypoRaw_mem S p n
  obtain ⟨aD, bD, hD⟩ := Work.WilkG4c.dgSet_mem S hder p n F0
  obtain ⟨aL, bL, hL⟩ := Work.WilG4c.fibreLimitEqMem_pi (S := S) (p := p) (n := n)
  refine ⟨max (aU + aH + 1) (aD + aL) + 1,
    bH.eval₂ MvPolynomial.C bU + bL.eval₂ MvPolynomial.C bD, ?_⟩
  intro D f L hf
  have hUV := hU D L.length f hf
  have hHyp := hH aU (MvPolynomial.eval ![D, L.length] bU)
    (Work.WilkG4c.UVFix p n f L.length) hUV
  have hLoc : {z : Fin (p + (n + 1) + 1) → ℝ |
        Fin.init z ∈ Work.WilkG4c.HypoRaw p n (Work.WilkG4c.UVFix p n f L.length)} ∈
      S.Ω (aU + aH + 1) (MvPolynomial.eval ![D, L.length] (bH.eval₂ MvPolynomial.C bU))
        (p + (n + 1) + 1) := by
    simpa only [Work.WilkG4c.eval_eval₂] using S.prod_right hHyp
  have hdg := hD D f hf L.length (fun j => L.get j)
  have hLimeq : Work.WilG4c.LimeqP p n
        (Work.WilkG4c.dgSet p n f L.length (fun j => L.get j)) ∈
      S.Ω (aD + aL) (MvPolynomial.eval ![D, L.length] (bL.eval₂ MvPolynomial.C bD))
        (p + (n + 1) + 1) := by
    simpa only [Work.WilkG4c.eval_eval₂, Work.WilG4c.LimeqP] using
      hL (Work.WilkG4c.dgSet p n f L.length (fun j => L.get j)) hdg
  rw [critFix_eq]
  exact Work.WilkG4c.inter_mv hLoc hLimeq

end Work.WilG4cR
