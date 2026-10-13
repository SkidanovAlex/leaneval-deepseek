/-
  WilG4c / `CritFixOmega` — `Ω`-definability of the *corrected* punctured-limit criterion
  `Work.WilkG4c.CritFix` (`CritFixDefs`), with format uniform in `|L|` and degree polynomial
  in `D, |L|`.

  `CritFix p n f L = LocCritFix p n f L ∩ LimeqP p n (dgSet p n f |L| L.get)`, and
  `LocCritFix` is (definitionally) the product of the ball-condensation `HypoRaw` applied to
  the value-free criterion `UVFix` with a free last coordinate, so the proof is the assembly

  * `GZ.uvfix_mem`              — `UVFix` is `Ω`-definable (`contSet` + the `Finset`-indexed
                                  intersection of the limit conditions `LimCond`, whose
                                  cardinality over `critIdxFix n k` is `≤ (k+2)^{n+2}`);
  * `hypoRaw_mem_proof`         — the ball-condensation operator `HypoRaw` is `Ω`-definable,
                                  obtained from the proved `CritAux.HypoBuild_mem` through
                                  `HypoRaw = HypoRawE = HypoBuild` (`GZ.hypoRaw_eq_hypoRawE_self`,
                                  `GZ.hypoBuild_eq_HypoRawE`);
  * `CritMem.dgSet_mem`         — the joint derivative graph along a word is `Ω`-definable
                                  (this is `SOMin.SharpDeriv` read in the `AlSliceBase`
                                  coordinates);
  * `fibreLimitEqMem_pi`        — the punctured-limit set `LimeqP` of an `Ω`-definable set is
                                  `Ω`-definable;

  glued by `S.prod_right` and the two-variable `MvPolynomial` bookkeeping `inter_mv`.

  Every module imported here is clean as used: the only unproved declarations in the import
  closure are ones this file never references.
-/
import Mathlib
import Submission.Work.Wilkies.Defs
import Submission.Work.WilG4c.CritFixDefs
import Submission.Work.WilG4c.CritMem
import Submission.Work.WilG4c.fibreLimitEqMem_pi
import Submission.Work.WilG4c.CritAux.HypoDefs
import Submission.Work.WilG4c.CritAux.hypoRaw_mem
import Submission.Work.WilG4c.GZ.Uvfix
import Submission.Work.WilG4c.GZ.HypoEqSelf
import Submission.Work.WilG4c.GZ.HypoBuildEq

set_option autoImplicit false
noncomputable section
open Classical

namespace Work.WilG4c

open WilkiesDesign WilkiesDesign.CG
open Work.WilkG4c

/-- **`Ω`-definability of the ball-condensation operator** `Work.WilkG4c.HypoRaw`, obtained by
transporting the proved `Ω`-construction `HypoBuild` (`CritAux.HypoBuild_mem`) across the two
descriptions `HypoRaw = HypoRawE = HypoBuild`. -/
theorem hypoRaw_mem_proof (S : WilkiesDesign.SOMin) (p n : ℕ) :
    ∃ (a : ℕ) (b : Polynomial ℕ), ∀ (F D : ℕ) (X : Set (Fin (p + (n + 1)) → ℝ)),
      X ∈ S.Ω F D (p + (n + 1)) →
      Work.WilkG4c.HypoRaw p n X ∈ S.Ω (F + a) (b.eval D) (p + (n + 1)) := by
  refine ⟨3 * Work.WilkG4c.hypoM p n + 3 * Work.WilkG4c.hypoN p n + (n + 1) + 12,
    Polynomial.X + Polynomial.C 9, ?_⟩
  intro F D X hX
  have hbuild := Work.WilG4c.CritAux.HypoBuild_mem S p n F D X hX
  have hraw : Work.WilkG4c.HypoRaw p n X ∈
      S.Ω (F + (3 * Work.WilkG4c.hypoM p n + 3 * Work.WilkG4c.hypoN p n + (n + 1) + 12))
        (D + 9) (p + (n + 1)) := by
    rw [Work.WilkG4c.GZ.hypoRaw_eq_hypoRawE_self p n X,
      ← Work.WilkG4c.GZ.hypoBuild_eq_HypoRawE p n X]
    exact hbuild
  refine Work.WilG4a.mem_mono hraw le_rfl ?_
  simp [Polynomial.eval_add, Polynomial.eval_X]

theorem CritFixOmega (S : WilkiesDesign.SOMin) (hder : S.SharpDeriv) (p n F0 : ℕ) :
    ∃ (a : ℕ) (b : MvPolynomial (Fin 2) ℕ), ∀ (D : ℕ)
      (f : (Fin p → ℝ) → (Fin (n + 1) → ℝ) → ℝ) (L : List (Fin (n + 1))),
      WilkiesDesign.CG.famGraph f ∈ S.Ω F0 D (p + (n + 1) + 1) →
      Work.WilkG4c.CritFix p n f L ∈ S.Ω a (MvPolynomial.eval ![D, L.length] b) (p + (n + 1) + 1) := by
  obtain ⟨aU, bU, hU⟩ := Work.WilkG4c.GZ.uvfix_mem S hder p n F0
  obtain ⟨aH, bH, hH⟩ := hypoRaw_mem_proof S p n
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
      S.Ω (aU + aH + 1)
        (MvPolynomial.eval ![D, L.length] (bH.eval₂ MvPolynomial.C bU))
        (p + (n + 1) + 1) := by
    simpa only [Work.WilkG4c.eval_eval₂] using S.prod_right hHyp
  have hdg := hD D f hf L.length (fun j => L.get j)
  have hLimeq : Work.WilG4c.LimeqP p n
        (Work.WilkG4c.dgSet p n f L.length (fun j => L.get j)) ∈
      S.Ω (aD + aL) (MvPolynomial.eval ![D, L.length] (bL.eval₂ MvPolynomial.C bD))
        (p + (n + 1) + 1) := by
    simpa only [Work.WilkG4c.eval_eval₂, Work.WilG4c.LimeqP] using
      hL (Work.WilkG4c.dgSet p n f L.length (fun j => L.get j)) hdg
  rw [show Work.WilkG4c.CritFix p n f L = {z : Fin (p + (n + 1) + 1) → ℝ |
        Fin.init z ∈ Work.WilkG4c.HypoRaw p n (Work.WilkG4c.UVFix p n f L.length)}
      ∩ Work.WilG4c.LimeqP p n
          (Work.WilkG4c.dgSet p n f L.length (fun j => L.get j)) from rfl]
  exact Work.WilkG4c.inter_mv hLoc hLimeq

end Work.WilG4c
