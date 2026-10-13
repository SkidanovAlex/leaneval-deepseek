import Mathlib
import Submission.Work.Wilkies.Defs
import Submission.Work.WilG4c.StepCleanDefs
import Submission.Work.WilG4c.SliceC1_mem_m
import Submission.Work.WilG4c.TSh

/-!
# `C1BadLocusMemPB2` — the non-`C¹` locus is `Ω`-definable, *without* `SharpDeriv`

The statement `C1BadLocusMemPB2` asks: if the graph of a family member
`G : ℝ^p → ℝ^N → ℝ` is `Ω`-definable with format `F0` and degree `D`, then the set of
points of `ℝ^{p+N}` at which the *joint* function `famFun G` fails to be `C¹` is
`Ω`-definable with a format `a` depending only on `p, N, F0` and a degree bounded by
`b.eval D`.

Unlike `Work.WilG4c.StepBadLoc`, which produces the same kind of statement from the
*axiom* `S.SharpDeriv`, the present result uses no extra hypothesis beyond the `SOMin`
axioms: the `C¹`-locus is a *first-order* property of the graph, so it is
`Ω`-definable by the ε-δ encoding already built in this area
(`Work.WilG4c.C1Exp`, the `TSh`-shape `Work.WilG4c.c1P` realising it, and the
identification `C1Exp ↔ ContDiffAt ℝ 1` of `SliceC1Shape`/`SliceC1Real`).

The one structural point is that `c1P` is set up for a *slice* — a `P`-dimensional
parameter block followed by an `M`-dimensional cube block — whereas here the function is
joint in all `p+N` variables.  We therefore instantiate the shape with an *empty* parameter
block (`P = 0`, `M = p + N`); the shape then describes exactly `ContDiffAt ℝ 1 (famFun G)`,
and the unavoidable arithmetic identifications (`0 + n = n`) are handled with
`Work.WilG5.mem_ndrec` / `Work.WilG5.omega_ndrec`.

Everything in this file is `sorry`-free.
-/

set_option autoImplicit false
noncomputable section
open Classical

namespace Work.WilG4c

open WilkiesDesign WilkiesDesign.CG

/-- **The joint non-`C¹` locus is `Ω`-definable.**  For any function
`g : ℝ^n → ℝ` whose graph is `Ω`-definable, the set of points at which `g` is not `C¹` is
`Ω`-definable, with format depending only on `n` and on the format of the graph, and degree
bounded by a fixed polynomial in `D`.

The proof is by the syntactic encoding of `C¹` (the shape `c1P` with an empty parameter
block) followed by complementation; `n = 0` is degenerate (every function on the one-point
space `ℝ^0` is `C¹`). -/
theorem jointBad_mem (S : WilkiesDesign.SOMin) (n F0 : ℕ) :
    ∃ (a : ℕ) (b : Polynomial ℕ), ∀ (D : ℕ) (g : (Fin n → ℝ) → ℝ),
      WilkiesDesign.graphOf g ∈ S.Ω F0 D (n + 1) →
      {z : Fin n → ℝ | ¬ ContDiffAt ℝ 1 g z} ∈ S.Ω a (b.eval D) n := by
  cases n with
  | zero =>
    -- `ℝ^0` is a point: every function is `C¹`, so the bad locus is empty.
    refine ⟨0, 0, ?_⟩
    intro D g _
    have hbad : {z : Fin 0 → ℝ | ¬ ContDiffAt ℝ 1 g z} = ∅ := by
      ext z
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_not]
      have hg' : g = fun _ : Fin 0 → ℝ => g z := by
        funext x
        congr 1
        exact funext fun i => Fin.elim0 i
      rw [hg']
      exact contDiffAt_const
    rw [hbad]
    have hempty : (∅ : Set (Fin 0 → ℝ)) ∈ S.Ω 0 0 0 := by
      have h := S.hyp 0 (1 : MvPolynomial (Fin 0) ℝ)
      rw [MvPolynomial.totalDegree_one] at h
      convert h using 1
      ext x
      simp
    simpa using hempty
  | succ m =>
    -- The shape: an empty parameter block and an `(m+1)`-dimensional cube block.
    -- The reference instance `c1` fixes the format/atom count; it is built at the (fixed)
    -- degree `4` from `Set.univ`, whose `Ω`-membership is `Work.WilG5.univ_mem`.
    let Fbig : ℕ := F0 + (((0 + (m + 1)) + 1) + 4)
    have huniv : (Set.univ : Set (Fin ((0 + (m + 1)) + 1) → ℝ)) ∈
        S.Ω Fbig 4 ((0 + (m + 1)) + 1) := by
      have h := Work.WilG5.univ_mem (S := S) (n := (0 + (m + 1)) + 1)
      exact Work.WilG5.mem_mono h Fbig 4 (by omega) le_rfl
    let c1 := c1P (S := S) (F := Fbig) (D := 4) (P := 0) (M := m + 1)
      (G := Set.univ) huniv
    refine ⟨c1.Fmt + 1, Polynomial.C c1.Atoms * (Polynomial.X + Polynomial.C 10), ?_⟩
    intro D g hg
    -- raise the format of the hypothesis to `Fbig`
    have hg' : WilkiesDesign.graphOf g ∈ S.Ω Fbig D (m + 1 + 1) :=
      Work.WilG5.mem_mono hg Fbig D (by omega) le_rfl
    -- the graph of the parameter-free family member `y ↦ g y`, transported to the index
    -- type `Fin (0 + (m+1) + 1)` used by `c1P`
    let f₀ : (Fin 0 → ℝ) → (Fin (m + 1) → ℝ) → ℝ := fun _ y => g y
    have hh : (m + 1) + 1 = (0 + (m + 1)) + 1 := by omega
    have hsetEq : WilkiesDesign.CG.famGraph f₀ = hh ▸ WilkiesDesign.graphOf g := by
      ext w
      rw [Work.WilG5.mem_ndrec]
      have hinit : (Fin.init fun i : Fin ((m + 1) + 1) => w (Fin.cast hh i))
          = fun j : Fin (m + 1) => w (Fin.castSucc (Fin.natAdd 0 j)) := by
        funext j
        simp only [Fin.init_def]
        congr 1
        ext; simp
      have hinit2 : (fun j : Fin (m + 1) => Fin.init w (Fin.natAdd 0 j))
          = fun j : Fin (m + 1) => w (Fin.castSucc (Fin.natAdd 0 j)) := by
        funext j; rfl
      simp only [WilkiesDesign.CG.famGraph, WilkiesDesign.graphOf, Set.mem_ofPred_eq, hinit,
        hinit2, Fin.cast_last, f₀]
    have hG₀ : WilkiesDesign.CG.famGraph f₀ ∈ S.Ω Fbig D ((0 + (m + 1)) + 1) := by
      rw [hsetEq]
      exact Work.WilG5.omega_ndrec hh hg'
    -- the shape at the actual degree `D`; it has the same format and atom count as `c1`
    let P0 := c1P (S := S) (F := Fbig) (D := D) (P := 0) (M := m + 1)
      (G := WilkiesDesign.CG.famGraph f₀) hG₀
    have hFmt : P0.Fmt = c1.Fmt := rfl
    have hAtoms : P0.Atoms = c1.Atoms := rfl
    -- its realisation is the `C¹`-locus of `g`
    have hReal := PKS.Real_mem_Omega P0
    rw [hFmt] at hReal
    have hRealEq : P0.Real =
        {w : Fin (0 + (m + 1)) → ℝ | ContDiffAt ℝ 1 g (Work.WilkG4c.cubePt w)} := by
      rw [show P0.Real = {z : Fin (0 + (m + 1)) → ℝ | C1Exp 0 (m + 1)
        (WilkiesDesign.CG.famGraph f₀) z} from c1P_Real hG₀]
      ext w
      simp only [Set.mem_ofPred_eq]
      rw [C1Exp_iff_C1Pred]
      exact c1RealPred_slice g (Work.WilkG4c.cubePt w)
    rw [hRealEq] at hReal
    -- complement: the non-`C¹` locus
    have hbad1 := S.compl hReal
    rw [Set.compl_ofPred] at hbad1
    -- degree bookkeeping
    have hDeg : P0.Deg ≤ c1.Atoms * (D + 2 + 8) := by
      have h := PKS.Deg_le P0
      rwa [hAtoms] at h
    have hbad2 := Work.WilG5.mem_mono hbad1 (c1.Fmt + 1) (c1.Atoms * (D + 2 + 8)) le_rfl hDeg
    -- transport back to the index type `Fin (m+1)`
    have h0 : 0 + (m + 1) = m + 1 := Nat.zero_add (m + 1)
    have hset7 : h0 ▸ {w : Fin (0 + (m + 1)) → ℝ |
          ¬ ContDiffAt ℝ 1 g (Work.WilkG4c.cubePt w)}
        = {z : Fin (m + 1) → ℝ | ¬ ContDiffAt ℝ 1 g z} := by
      ext z
      rw [Work.WilG5.mem_ndrec]
      have hcp : Work.WilkG4c.cubePt (fun i : Fin (0 + (m + 1)) => z (Fin.cast h0 i)) = z := by
        funext j
        simp only [Work.WilkG4c.cubePt]
        congr 1
        ext; simp
      simp only [Set.mem_ofPred_eq, hcp]
    have hfin := Work.WilG5.omega_ndrec h0 hbad2
    rw [hset7] at hfin
    rw [show Polynomial.eval D (Polynomial.C c1.Atoms * (Polynomial.X + Polynomial.C 10))
        = c1.Atoms * (D + 2 + 8) from by
      simp only [Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_X]]
    exact hfin

/-- **The requested lemma.**  If the graph of the family member
`G : ℝ^p → ℝ^N → ℝ` is `Ω`-definable, then the set of points of `ℝ^{p+N}` where the joint
function `famFun G` is not `C¹` is `Ω`-definable with a fixed format `a` and degree bounded
by `b.eval D`.  This is the instance of `jointBad_mem` for `g = famFun G`
(so that `graphOf g = famGraph G`). -/
theorem C1BadLocusMemPB2 {S : WilkiesDesign.SOMin} (p N F0 : ℕ) :
    ∃ (a : ℕ) (b : Polynomial ℕ), ∀ (D : ℕ) (G : (Fin p → ℝ) → (Fin N → ℝ) → ℝ),
      WilkiesDesign.CG.famGraph G ∈ S.Ω F0 D (p + N + 1) →
      {z : Fin (p + N) → ℝ | ¬ ContDiffAt ℝ 1 (Work.WilG4c.famFun G) z} ∈
        S.Ω a (Polynomial.eval D b) (p + N) := by
  obtain ⟨a, b, h⟩ := jointBad_mem S (p + N) F0
  exact ⟨a, b, fun D G hG => h D (Work.WilG4c.famFun G) (by rw [graphOf_famFun]; exact hG)⟩

end Work.WilG4c
