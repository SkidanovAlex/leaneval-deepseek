import Mathlib
import Submission.Work.WilG1.Basic
import Submission.Work.WilG1.ChoiceDefs
import Submission.Work.WilG1.Choice.Eff.Defs
import Submission.Work.WilG1.Calc.lt_mem
import Submission.Work.WilG5.Basic
import Submission.Work.WilG5.Reindex
import Submission.Work.WilG5.Reindex3
import Submission.Work.WilG4a.fiber_endpoints
import Submission.Work.WilG4a.LB1_mem

set_option autoImplicit false
noncomputable section
open Classical

namespace Work.WilG1.Choice.G1Sel

open WilkiesDesign WilkiesConjecture

/-! ## The two elementary `Ω`-sets with explicit bounds

`NE1 p X = {z | ∃ t, (init z, t) ∈ X}` and `LB1 p Z = {z | ∀ t, (init z, t) ∈ Z → z last ≤ t}`
are the coordinate reindexings of `X`/`Sg` (`Work.WilG4a.pullZ2`) intersected with the
half-space `t < y` and projected/complemented.  We record their `Ω`-memberships with the
explicit degree polynomials we need for the arithmetic of the union. -/

/-- `NE1 p X = projLast (pullZ2 p X)` is an `Ω`-set with degree `bX + O(p)`. -/
theorem NE1_mem' {S : WilkiesDesign.SOMin} (p FX : ℕ) :
    ∃ a : ℕ, ∀ (D : ℕ) (bX : Polynomial ℕ) (X : Set (Fin (p + 1) → ℝ)),
      X ∈ S.Ω FX (bX.eval D) (p + 1) →
      Work.WilG4a.NE1 p X ∈
        S.Ω a ((bX + Polynomial.C (32 * (2 * p + 3) + 32)).eval D) (p + 1) := by
  refine ⟨64 * (2 * p + 3) + 65 + FX, ?_⟩
  intro D bX X hX
  have hpre : Work.WilG4a.pullZ2 p X ∈
      S.Ω (FX + 64 * ((p + 2) + (p + 1)) + 64)
        (bX.eval D + 32 * ((p + 2) + (p + 1)) + 32) (p + 2) := by
    have h := Work.WilG5.coordPre_mem (S := S) (m := p + 1) (N := p + 2)
      (ι := Work.WilG4a.iota1 p) (A := X) hX
    rwa [show Work.WilG5.coordPre (Work.WilG4a.iota1 p) X = Work.WilG4a.pullZ2 p X from rfl]
      at h
  have hproj : Work.WilG4a.NE1 p X ∈
      S.Ω (FX + 64 * ((p + 2) + (p + 1)) + 64 + 1)
        (bX.eval D + 32 * ((p + 2) + (p + 1)) + 32) (p + 1) :=
    S.proj hpre
  refine Work.WilG5.mem_mono hproj (64 * (2 * p + 3) + 65 + FX)
    ((bX + Polynomial.C (32 * (2 * p + 3) + 32)).eval D) (by omega) ?_
  simp only [Polynomial.eval_add, Polynomial.eval_C]
  omega

/-- `LB1 p Z = (projLast (pullZ2 p Z ∩ tLtY p))ᶜ` is an `Ω`-set with degree `bSg + O(p)`. -/
theorem LB1_mem' {S : WilkiesDesign.SOMin} (p FSg : ℕ) :
    ∃ a : ℕ, ∀ (D : ℕ) (bSg : Polynomial ℕ) (Sg : Set (Fin (p + 1) → ℝ)),
      Sg ∈ S.Ω FSg (bSg.eval D) (p + 1) →
      Work.WilG4a.LB1 p Sg ∈
        S.Ω a ((bSg + Polynomial.C (32 * (2 * p + 3) + 35)).eval D) (p + 1) := by
  refine ⟨max (FSg + 64 * ((p + 2) + (p + 1)) + 64) (p + 5) + 3 + FSg, ?_⟩
  intro D bSg Sg hSg
  have hPull : Work.WilG4a.pullZ2 p Sg ∈
      S.Ω (FSg + 64 * ((p + 2) + (p + 1)) + 64)
        (bSg.eval D + 32 * ((p + 2) + (p + 1)) + 32) (p + 2) := by
    have h := Work.WilG5.coordPre_mem (S := S) (m := p + 1) (N := p + 2)
      (ι := Work.WilG4a.iota1 p) (A := Sg) hSg
    rwa [show Work.WilG5.coordPre (Work.WilG4a.iota1 p) Sg = Work.WilG4a.pullZ2 p Sg from rfl]
      at h
  have hlt : Work.WilG4a.tLtY p ∈ S.Ω (p + 5) 3 (p + 2) := by
    have h := Work.WilG1.Calc.lt_mem (S := S) (n := p + 2) 0
      (Fin.last (p + 1)) (Fin.castSucc (Fin.last p))
    exact Work.WilG5.mem_mono h (p + 5) 3 (by omega) (by simp)
  have hPull' : Work.WilG4a.pullZ2 p Sg ∈
      S.Ω (max (FSg + 64 * ((p + 2) + (p + 1)) + 64) (p + 5))
        (bSg.eval D + 32 * ((p + 2) + (p + 1)) + 32) (p + 2) :=
    Work.WilG5.mem_mono hPull _ _ (le_max_left _ _) le_rfl
  have hlt' : Work.WilG4a.tLtY p ∈
      S.Ω (max (FSg + 64 * ((p + 2) + (p + 1)) + 64) (p + 5)) 3 (p + 2) :=
    Work.WilG5.mem_mono hlt _ _ (le_max_right _ _) le_rfl
  have hInt : Work.WilG4a.pullZ2 p Sg ∩ Work.WilG4a.tLtY p ∈
      S.Ω (max (FSg + 64 * ((p + 2) + (p + 1)) + 64) (p + 5) + 1)
        ((bSg.eval D + 32 * ((p + 2) + (p + 1)) + 32) + 3) (p + 2) :=
    Work.WilG0.Omega_inter2 (S := S) hPull' hlt'
  have hProj : WilkiesDesign.projLast (Work.WilG4a.pullZ2 p Sg ∩ Work.WilG4a.tLtY p) ∈
      S.Ω (max (FSg + 64 * ((p + 2) + (p + 1)) + 64) (p + 5) + 2)
        ((bSg.eval D + 32 * ((p + 2) + (p + 1)) + 32) + 3) (p + 1) :=
    S.proj hInt
  have hFinal : Work.WilG4a.LB1 p Sg ∈
      S.Ω (max (FSg + 64 * ((p + 2) + (p + 1)) + 64) (p + 5) + 3)
        ((bSg.eval D + 32 * ((p + 2) + (p + 1)) + 32) + 3) (p + 1) :=
    S.compl hProj
  refine Work.WilG5.mem_mono hFinal
    (max (FSg + 64 * ((p + 2) + (p + 1)) + 64) (p + 5) + 3 + FSg)
    ((bSg + Polynomial.C (32 * (2 * p + 3) + 35)).eval D) (by omega) ?_
  simp only [Polynomial.eval_add, Polynomial.eval_C]
  omega

/-- The defining decomposition of `minGraph` into the first disjunct `yZero1 ∩ (NE1)ᶜ`
(the empty fibre region) and the second `Sg ∩ LB1` (the minimal points of `Sg`). -/
theorem minGraph_eq' {p : ℕ} (X Sg : Set (Fin (p + 1) → ℝ)) :
    Work.WilG1.Choice.Eff.minGraph X Sg =
      (Work.WilG4a.yZero1 p ∩ (Work.WilG4a.NE1 p X)ᶜ) ∪ (Sg ∩ Work.WilG4a.LB1 p Sg) := by
  ext z
  simp only [Work.WilG1.Choice.Eff.minGraph, Set.mem_ofPred_eq, Set.mem_union, Set.mem_inter_iff,
    Set.mem_compl_iff, Work.WilG4a.mem_yZero1, Work.WilG4a.mem_NE1, Work.WilG4a.mem_LB1]

/-- `minGraph X Sg` is again an `Ω`-set (see `Choice/Eff/Defs.lean`).

`minGraph X Sg = {z | (z (Fin.last p) = 0 ∧ ¬∃ t, Fin.snoc (Fin.init z) t ∈ X) ∨
  (z ∈ Sg ∧ ∀ t, Fin.snoc (Fin.init z) t ∈ Sg → z (Fin.last p) ≤ t)}`.

Proof strategy: build the two disjuncts separately and union them.
The first is `({z | z (Fin.last p) = 0}) ∩ {z | Fin.init z ∉ projLast X}` — a hypersurface
intersected with `prod_right` of the complement of `projLast X`.
The second is `Sg ∩ {z | ∀ t, ¬(Fin.snoc (Fin.init z) t ∈ Sg ∧ t < z (Fin.last p))}`; the inner
set is the complement of `projLast` of the set
`{y : Fin (p + 2) → ℝ | y ∈ Sg (pulled back along Fin.init) ∧ y (Fin.last (p+1)) < y (Fin.last p)}`,
whose two conjuncts are a `prod_right` lift of `Sg` and the coordinate comparison
`WilG1.Calc.lt_mem`.  Formats add by the usual `+1` per `compl`/`proj`/`prod_right` and `max + 1`
per `inter`; degrees are sums of a bounded number of copies of `bX`, `bSg` plus `O(p)` constants,
which the stated bound `200 * (p+2) * (bX + bSg) + 2000 * (p+2)` dominates.  Both `Ω`-memberships
follow from the raw `SOMin` axioms (no `SharpCD` needed). -/
theorem minGraphOmegaG1 {S : WilkiesDesign.SOMin} (p FX FSg : ℕ) :
    ∃ a : ℕ, ∀ (D : ℕ) (bX bSg : Polynomial ℕ) (X Sg : Set (Fin (p + 1) → ℝ)),
      X ∈ S.Ω FX (bX.eval D) (p + 1) → Sg ∈ S.Ω FSg (bSg.eval D) (p + 1) →
      Work.WilG1.Choice.Eff.minGraph X Sg ∈
        S.Ω a ((Polynomial.C (200 * (p + 2)) * (bX + bSg) + Polynomial.C (2000 * (p + 2))).eval D)
          (p + 1) := by
  obtain ⟨aNE, hNE⟩ := NE1_mem' (S := S) p FX
  obtain ⟨aLB, hLB⟩ := LB1_mem' (S := S) p FSg
  refine ⟨max (max (p + 1) (aNE + 1) + 1) (max FSg aLB + 1), ?_⟩
  intro D bX bSg X Sg hX hSg
  -- First disjunct: `yZero1 p ∩ (NE1 p X)ᶜ`.
  have hy0 : Work.WilG4a.yZero1 p ∈ S.Ω (p + 1) 1 (p + 1) := Work.WilG4a.yZero1_mem S p
  have hy0' : Work.WilG4a.yZero1 p ∈ S.Ω (max (p + 1) (aNE + 1)) 1 (p + 1) :=
    Work.WilG5.mem_mono hy0 _ _ (le_max_left _ _) le_rfl
  have hNEc : (Work.WilG4a.NE1 p X)ᶜ ∈
      S.Ω (aNE + 1) ((bX + Polynomial.C (32 * (2 * p + 3) + 32)).eval D) (p + 1) :=
    S.compl (hNE D bX X hX)
  have hNEc' : (Work.WilG4a.NE1 p X)ᶜ ∈
      S.Ω (max (p + 1) (aNE + 1)) ((bX + Polynomial.C (32 * (2 * p + 3) + 32)).eval D)
        (p + 1) :=
    Work.WilG5.mem_mono hNEc _ _ (le_max_right _ _) le_rfl
  have hA : Work.WilG4a.yZero1 p ∩ (Work.WilG4a.NE1 p X)ᶜ ∈
      S.Ω (max (p + 1) (aNE + 1) + 1)
        (1 + (bX + Polynomial.C (32 * (2 * p + 3) + 32)).eval D) (p + 1) :=
    Work.WilG0.Omega_inter2 (S := S) hy0' hNEc'
  -- Second disjunct: `Sg ∩ LB1 p Sg`.
  have hSgF : Sg ∈ S.Ω (max FSg aLB) (bSg.eval D) (p + 1) :=
    Work.WilG5.mem_mono hSg _ _ (le_max_left _ _) le_rfl
  have hLBF : Work.WilG4a.LB1 p Sg ∈
      S.Ω (max FSg aLB) ((bSg + Polynomial.C (32 * (2 * p + 3) + 35)).eval D) (p + 1) :=
    Work.WilG5.mem_mono (hLB D bSg Sg hSg) _ _ (le_max_right _ _) le_rfl
  have hB : Sg ∩ Work.WilG4a.LB1 p Sg ∈
      S.Ω (max FSg aLB + 1)
        (bSg.eval D + (bSg + Polynomial.C (32 * (2 * p + 3) + 35)).eval D) (p + 1) :=
    Work.WilG0.Omega_inter2 (S := S) hSgF hLBF
  -- Union of the two disjuncts.
  have hA' : Work.WilG4a.yZero1 p ∩ (Work.WilG4a.NE1 p X)ᶜ ∈
      S.Ω (max (max (p + 1) (aNE + 1) + 1) (max FSg aLB + 1))
        (1 + (bX + Polynomial.C (32 * (2 * p + 3) + 32)).eval D) (p + 1) :=
    Work.WilG5.mem_mono hA _ _ (le_max_left _ _) le_rfl
  have hB' : Sg ∩ Work.WilG4a.LB1 p Sg ∈
      S.Ω (max (max (p + 1) (aNE + 1) + 1) (max FSg aLB + 1))
        (bSg.eval D + (bSg + Polynomial.C (32 * (2 * p + 3) + 35)).eval D) (p + 1) :=
    Work.WilG5.mem_mono hB _ _ (le_max_right _ _) le_rfl
  have hAB : (Work.WilG4a.yZero1 p ∩ (Work.WilG4a.NE1 p X)ᶜ) ∪ (Sg ∩ Work.WilG4a.LB1 p Sg) ∈
      S.Ω (max (max (p + 1) (aNE + 1) + 1) (max FSg aLB + 1))
        ((1 + (bX + Polynomial.C (32 * (2 * p + 3) + 32)).eval D) +
          (bSg.eval D + (bSg + Polynomial.C (32 * (2 * p + 3) + 35)).eval D)) (p + 1) :=
    Work.WilG0.Omega_union2 (S := S) hA' hB'
  rw [minGraph_eq' X Sg]
  refine Work.WilG0.Omega_mono_FD le_rfl ?_ hAB
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C]
  have hmain : bX.eval D + 2 * bSg.eval D ≤ 200 * (p + 2) * (bX.eval D + bSg.eval D) := by
    have h1 : 2 * (bX.eval D + bSg.eval D) ≤ 200 * (p + 2) * (bX.eval D + bSg.eval D) :=
      Nat.mul_le_mul_right _ (by omega)
    have h2 : bX.eval D + 2 * bSg.eval D ≤ 2 * (bX.eval D + bSg.eval D) := by omega
    exact le_trans h2 h1
  have hconst : 32 * (2 * p + 3) + 32 + (32 * (2 * p + 3) + 35) + 1 ≤ 2000 * (p + 2) := by omega
  omega

end Work.WilG1.Choice.G1Sel
