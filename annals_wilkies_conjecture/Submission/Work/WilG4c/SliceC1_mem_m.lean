/-
  WilG4c / `SliceC1_mem_m` — the fibre `C¹`-locus of a family is `Ω`-definable.

  This file assembles the result: `c1P` (`Submission.Work.WilG4c.SliceC1Shape`) realises the
  predicate `C1Exp`, which is converted here into Mathlib's `C1Pred` and hence (via
  `Work.WilG4c.c1RealPred_slice` from `Submission.Work.WilG4c.SliceC1Real`) into
  `ContDiffAt ℝ 1`, i.e. into `SliceLocus`.

  Everything is `sorry`-free.
-/
import Mathlib
import Submission.Work.WilG4c.SliceC1Shape
import Submission.Work.WilG4c.SlicedDerivDefs
import Submission.Work.WilG4c.c1RealFD
import Submission.Work.WilG4c.SliceC1Real

set_option autoImplicit false
set_option linter.unusedSimpArgs false
noncomputable section
open Classical

namespace Work.WilG4c

open WilkiesDesign WilkiesDesign.CG Work.WilG5 Work.WilkG4c

/-! ## 1. The family value through the graph -/

/-- `famFunHat f` composed with the affine inclusion `Fin.append l` is `f l`. -/
theorem famFunHat_append_slice {P m : ℕ} {f : (Fin P → ℝ) → (Fin (m + 1) → ℝ) → ℝ}
    (l : Fin P → ℝ) (u : Fin (m + 1) → ℝ) :
    famFunHat f (Fin.append l u) = f l u := by
  rw [famFunHat_eq_parPt_cubePt]
  congr 1
  · funext i
    rw [parPt, Fin.append_left]
  · funext j
    rw [cubePt, Fin.append_right]

/-- Reading the graph membership: `t = f l u`. -/
theorem memGraph_iff {P m : ℕ} (f : (Fin P → ℝ) → (Fin (m + 1) → ℝ) → ℝ)
    (z : Fin (P + (m + 1)) → ℝ) (y : Fin (m + 1) → ℝ) (t : ℝ) :
    Fin.snoc (Fin.append (z ∘ fun i : Fin P => Fin.castAdd (m + 1) i) y) t ∈
        WilkiesDesign.CG.famGraph f ↔ t = f (parPt z) y := by
  rw [Work.WilkG4c.famGraph_eq_graphOf_famFunHat f, graphOf, Set.mem_ofPred_eq,
    Fin.init_snoc, famFunHat_append_slice, Fin.snoc_last]
  rfl

/-- Eliminating the graph coordinate:
`∃ t, (z,y,t) ∈ famGraph f ∧ Ψ t ↔ Ψ (f (parPt z) y)`. -/
theorem exists_snoc_memGraph {P m : ℕ} (f : (Fin P → ℝ) → (Fin (m + 1) → ℝ) → ℝ)
    (z : Fin (P + (m + 1)) → ℝ) (y : Fin (m + 1) → ℝ) (Ψ : ℝ → Prop) :
    (∃ t : ℝ, Fin.snoc (Fin.append (z ∘ fun i : Fin P => Fin.castAdd (m + 1) i) y) t ∈
        WilkiesDesign.CG.famGraph f ∧ Ψ t) ↔ Ψ (f (parPt z) y) := by
  constructor
  · rintro ⟨t, hmem, hΨ⟩
    have ht : t = f (parPt z) y := (memGraph_iff f z y t).mp hmem
    rw [ht] at hΨ
    exact hΨ
  · rintro h
    exact ⟨_, (memGraph_iff f z y _).mpr rfl, h⟩

/-! ## 2. `C1Exp` is `C1Pred` -/

/-- The shape `C1Exp` (a formula about the graph `famGraph f`) says exactly that the slice
`y ↦ f (parPt z) y` is `C¹` at `cubePt z` in the `ε`-`δ` sense `C1Pred`. -/
theorem C1Exp_iff_C1Pred {P m : ℕ} (f : (Fin P → ℝ) → (Fin (m + 1) → ℝ) → ℝ)
    (z : Fin (P + (m + 1)) → ℝ) :
    C1Exp P (m + 1) (WilkiesDesign.CG.famGraph f) z ↔
      C1Pred (fun y : Fin (m + 1) → ℝ => f (parPt z) y) (cubePt z) := by
  simp only [C1Exp, C1Pred, HasFDerivEps, exists_snoc_memGraph, cubePt_apply]

/-! ## 3. The target -/

theorem SliceC1_mem_m (S : WilkiesDesign.SOMin) (hcd : S.SharpCD) (hder : S.SharpDeriv)
    (p n F0 : ℕ) :
    ∃ (a : ℕ) (b : Polynomial ℕ), ∀ (D : ℕ)
      (f : (Fin p → ℝ) → (Fin (n + 1) → ℝ) → ℝ),
      WilkiesDesign.CG.famGraph f ∈ S.Ω F0 D (p + (n + 1) + 1) →
      Work.WilkG4c.SliceLocus p n f 1 ∈ S.Ω a (b.eval D) (p + (n + 1)) := by
  -- the format of the shape (it does not depend on the mem-atom data), named via a dummy `G`
  have hu : (Set.univ : Set (Fin (p + (n + 1) + 1) → ℝ)) ∈
      S.Ω (F0 + ((p + (n + 1) + 1) + 4)) 4 (p + (n + 1) + 1) := by
    have h := Work.WilG5.univ_mem (S := S) (n := p + (n + 1) + 1)
    exact Work.WilG5.mem_mono h _ _ (by omega) (by omega)
  let c1 : PKS S (F0 + ((p + (n + 1) + 1) + 4)) 4 (p + (n + 1)) :=
    c1P (S := S) (F := F0 + ((p + (n + 1) + 1) + 4)) (D := 4) (P := p) (M := n + 1)
      (G := Set.univ) hu
  refine ⟨c1.Fmt, Polynomial.C c1.Atoms * (Polynomial.X + Polynomial.C 2) +
    Polynomial.C (c1.Atoms * 8), ?_⟩
  intro D f hf
  have hf' : WilkiesDesign.CG.famGraph f ∈
      S.Ω (F0 + ((p + (n + 1) + 1) + 4)) D (p + (n + 1) + 1) :=
    Work.WilG5.mem_mono hf _ _ (by omega) le_rfl
  have hb : (Polynomial.C c1.Atoms * (Polynomial.X + Polynomial.C 2) +
      Polynomial.C (c1.Atoms * 8)).eval D = c1.Atoms * (D + 2 + 8) := by
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
    ring
  rw [hb]
  have hmem := PKS.Real_mem_Omega
    (c1P (S := S) (F := F0 + ((p + (n + 1) + 1) + 4)) (D := D) (P := p) (M := n + 1)
      (G := WilkiesDesign.CG.famGraph f) hf')
  rw [c1P_Real] at hmem
  have hset : {z : Fin (p + (n + 1)) → ℝ |
      C1Exp p (n + 1) (WilkiesDesign.CG.famGraph f) z} = Work.WilkG4c.SliceLocus p n f 1 := by
    ext z
    show C1Exp p (n + 1) (WilkiesDesign.CG.famGraph f) z ↔
      ContDiffAt ℝ 1 (fun y : Fin (n + 1) → ℝ => f (parPt z) y) (cubePt z)
    exact (C1Exp_iff_C1Pred f z).trans (Work.WilG4c.c1RealPred_slice _ _)
  rw [hset] at hmem
  have hDeg : (c1P (S := S) (F := F0 + ((p + (n + 1) + 1) + 4)) (D := D) (P := p) (M := n + 1)
      (G := WilkiesDesign.CG.famGraph f) hf').Deg ≤ c1.Atoms * (D + 2 + 8) := by
    have h := PKS.Deg_le (c1P (S := S) (F := F0 + ((p + (n + 1) + 1) + 4)) (D := D) (P := p)
      (M := n + 1) (G := WilkiesDesign.CG.famGraph f) hf')
    rwa [show (c1P (S := S) (F := F0 + ((p + (n + 1) + 1) + 4)) (D := D) (P := p) (M := n + 1)
        (G := WilkiesDesign.CG.famGraph f) hf').Atoms = c1.Atoms from rfl] at h
  have hFmt : (c1P (S := S) (F := F0 + ((p + (n + 1) + 1) + 4)) (D := D) (P := p) (M := n + 1)
      (G := WilkiesDesign.CG.famGraph f) hf').Fmt = c1.Fmt := rfl
  rw [hFmt] at hmem
  exact Work.WilG5.mem_mono hmem c1.Fmt (c1.Atoms * (D + 2 + 8)) le_rfl hDeg

end Work.WilG4c
