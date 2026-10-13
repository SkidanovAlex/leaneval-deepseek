/-
  WilG4c — the affine-in-the-last-variable family lemma `Work.WilG4c.famGraph_linX`.

  Given two `Ω Fa Da (p+1)`-definable functions `α β : ℝ^p → ℝ`, the graph of the family

      `(l, t) ↦ α l + β l * t 0`      (`t : Fin (n+1) → ℝ`)

  is `Ω`-definable with format `Fa + K` and degree `2*Da + K`, for a constant `K` depending
  only on `p` and `n`.  The format grows only by a constant because the two input graphs are
  used *simultaneously*, inside a single `SOMin.inter` over a `Fin 3`-indexed family, rather
  than twice in a binary intersection; the degree is linear with coefficient one in each
  input degree because the construction is a single polynomial combination
  (`X 0 + X 1 * X 2`) of three functions whose values are recorded in three fresh
  coordinates.

  The proof is the standard one (BNZ §5, affine charts), realised with the workspace's
  `PolyComb` machinery:

  * flatten the family to `flatFun`, whose graph is the `famGraph`;
  * the flattened function is the polynomial combination `H 0 + H 1 * H 2` of the padded
    functions `H 0 = α ∘ proj`, `H 1 = β ∘ proj` (`GraphComp.subst_mem`), and the
    coordinate function `H 2 = t ↦ t 0` (`graphOf_coord_mem`);
  * work in `ℝ^{(p+n+1)+1+3}` with layout `(x, value, y₀,y₁,y₂)`, pull the three graphs
    back along `PolyComb.sigY`, impose the hypersurface `value = y₀ + y₁*y₂`, and project
    the three fresh coordinates away (`PolyComb.projLastIter_eq_graph`).
-/
import Mathlib
import Submission.Work.Wilkies.CG.Spec
import Submission.Work.WilG0.API
import Submission.Work.WilG1.Basic
import Submission.Work.WilG0.projLastIter_mem
import Submission.Work.WilG0.projLastIter_eq
import Submission.Work.WilG4c.GraphOfComp
import Submission.Work.WilG4c.PolyCombBasic
import Submission.Work.WilG4c.YbddAux

set_option autoImplicit false
noncomputable section
open Classical

namespace Work.WilG4c

open WilkiesDesign WilkiesDesign.CG Work.WilG0 Work.WilG1

/-! ## 1. The padding substitution

The map `padChi` reads the `p` argument coordinates and the value coordinate of a function
`Fin p → ℝ` out of a vector of `Fin (p + (n+1) + 1)` coordinates (the first `p` coordinates
and the last one); pulling the graph of `α` back along it is the graph of
`y ↦ α (fun i => y (Fin.castAdd (n+1) i))`. -/

/-- The coordinate map `Fin (p+1) → Fin (p+(n+1)+1)`: the `p` argument coordinates go to the
first `p` coordinates, the value coordinate to the last one. -/
def padChi (p n : ℕ) : Fin (p + 1) → Fin (p + (n + 1) + 1) :=
  Fin.snoc (fun i : Fin p => Fin.castSucc (Fin.castAdd (n + 1) i))
    (Fin.last (p + (n + 1)))

@[simp] theorem padChi_castSucc (p n : ℕ) (i : Fin p) :
    padChi p n (Fin.castSucc i) = Fin.castSucc (Fin.castAdd (n + 1) i) := by
  simp [padChi]

@[simp] theorem padChi_last (p n : ℕ) :
    padChi p n (Fin.last p) = Fin.last (p + (n + 1)) := by
  simp [padChi]

/-- The pullback of `graphOf α` along `padChi` is the graph of the padded function. -/
theorem padGraph_eq (p n : ℕ) (α : (Fin p → ℝ) → ℝ) :
    {x : Fin (p + (n + 1) + 1) → ℝ | x ∘ padChi p n ∈ graphOf α}
      = graphOf (fun y : Fin (p + (n + 1)) → ℝ => α (fun i => y (Fin.castAdd (n + 1) i))) := by
  ext x
  simp only [Set.mem_ofPred_eq, graphOf, Function.comp_apply, Fin.init_def,
    padChi_last, padChi_castSucc]

/-- **The padding lemma.**  A `Ω`-definable graph stays `Ω`-definable when `n+1` dummy
coordinates are inserted after the arguments.  Format `Fa + 2*((p+(n+1)+1)+(p+1)) + 1`,
degree `Da + 2` (the cost of the coordinate substitution). -/
theorem padGraph_mem (S : SOMin) {p n Fa Da : ℕ} {α : (Fin p → ℝ) → ℝ}
    (hα : graphOf α ∈ S.Ω Fa Da (p + 1)) :
    graphOf (fun y : Fin (p + (n + 1)) → ℝ => α (fun i => y (Fin.castAdd (n + 1) i)))
      ∈ S.Ω (Fa + 2 * ((p + (n + 1) + 1) + (p + 1)) + 1) (Da + 2) (p + (n + 1) + 1) := by
  rw [← padGraph_eq p n α]
  exact GraphComp.subst_mem S (padChi p n) hα

/-! ## 2. The polynomial `X 0 + X 1 * X 2` -/

/-- The polynomial `y₀ + y₁ * y₂`. -/
def linXPoly : MvPolynomial (Fin 3) ℝ :=
  MvPolynomial.X 0 + MvPolynomial.X 1 * MvPolynomial.X 2

theorem linXPoly_totalDegree_le : linXPoly.totalDegree ≤ 2 := by
  simp only [linXPoly]
  refine le_trans (MvPolynomial.totalDegree_add _ _) (max_le ?_ ?_)
  · exact le_trans (le_of_eq (MvPolynomial.totalDegree_X (R := ℝ) (0 : Fin 3))) (by norm_num)
  · refine le_trans (MvPolynomial.totalDegree_mul _ _) ?_
    have h1 : (MvPolynomial.X (1 : Fin 3) : MvPolynomial (Fin 3) ℝ).totalDegree ≤ 1 :=
      le_of_eq (MvPolynomial.totalDegree_X (R := ℝ) _)
    have h2 : (MvPolynomial.X (2 : Fin 3) : MvPolynomial (Fin 3) ℝ).totalDegree ≤ 1 :=
      le_of_eq (MvPolynomial.totalDegree_X (R := ℝ) _)
    omega

theorem linXPoly_eval (a b t : ℝ) : MvPolynomial.eval ![a, b, t] linXPoly = a + b * t := by
  simp [linXPoly]

/-! ## 3. The main theorem -/

theorem famGraph_linX (S : WilkiesDesign.SOMin) (p n : ℕ) :
    ∃ K : ℕ, ∀ (Fa Da : ℕ) (α β : (Fin p → ℝ) → ℝ),
      WilkiesDesign.graphOf α ∈ S.Ω Fa Da (p + 1) →
      WilkiesDesign.graphOf β ∈ S.Ω Fa Da (p + 1) →
      WilkiesDesign.CG.famGraph
        (fun (l : Fin p → ℝ) (t : Fin (n + 1) → ℝ) => α l + β l * t 0)
        ∈ S.Ω (Fa + K) (2 * Da + K) (p + (n + 1) + 1) := by
  refine ⟨2 * ((p + (n + 1) + 1) + (p + 1)) + 1
    + (2 * ((p + (n + 1) + 1 + 3) + (p + (n + 1) + 1)) + 1)
    + 5 + (p + (n + 1) + 1) + 14, ?_⟩
  intro Fa Da α β hα hβ
  -- the three constituent functions of the flattened family, as a `Fin 3`-indexed family
  let h0 : (Fin (p + (n + 1)) → ℝ) → ℝ := fun y => α (fun i => y (Fin.castAdd (n + 1) i))
  let h1 : (Fin (p + (n + 1)) → ℝ) → ℝ := fun y => β (fun i => y (Fin.castAdd (n + 1) i))
  let h2 : (Fin (p + (n + 1)) → ℝ) → ℝ := fun y => y (Fin.natAdd p (0 : Fin (n + 1)))
  let H : Fin 3 → (Fin (p + (n + 1)) → ℝ) → ℝ := ![h0, h1, h2]
  -- uniform format/degree bookkeeping
  let c1 : ℕ := 2 * ((p + (n + 1) + 1) + (p + 1)) + 1
  let cc : ℕ := 2 * ((p + (n + 1) + 1 + 3) + (p + (n + 1) + 1)) + 1
  let FC : ℕ := Fa + c1 + cc
  let Dg : Fin 3 → ℕ := ![Da + 4, Da + 4, 3]
  have hc1 : c1 = 2 * ((p + (n + 1) + 1) + (p + 1)) + 1 := rfl
  have hcc : cc = 2 * ((p + (n + 1) + 1 + 3) + (p + (n + 1) + 1)) + 1 := rfl
  have hFC : FC = Fa + c1 + cc := rfl
  -- membership of the padded graphs
  have hH0 : graphOf (H 0) ∈
      S.Ω (Fa + 2 * ((p + (n + 1) + 1) + (p + 1)) + 1) (Da + 2) (p + (n + 1) + 1) := by
    have h := padGraph_mem (S := S) (n := n) hα
    simpa only [H, h0, Matrix.cons_val_zero] using h
  have hH1 : graphOf (H 1) ∈
      S.Ω (Fa + 2 * ((p + (n + 1) + 1) + (p + 1)) + 1) (Da + 2) (p + (n + 1) + 1) := by
    have h := padGraph_mem (S := S) (n := n) hβ
    simpa only [H, h1, Matrix.cons_val_one, Matrix.cons_val_succ, Matrix.cons_val_zero] using h
  have hH2 : graphOf (H 2) ∈ S.Ω (p + (n + 1) + 1) 1 (p + (n + 1) + 1) := by
    have h := Work.WilkG4c.graphOf_coord_mem (S := S) (Fin.natAdd p (0 : Fin (n + 1)))
    simpa [H, h2] using h
  -- the three pullbacks of the graphs, at the common format `FC`
  have hT0 : {z : Fin (p + (n + 1) + 1 + 3) → ℝ |
        z ∘ PolyComb.sigY (p + (n + 1)) 3 (0 : Fin 3) ∈ graphOf (H 0)} ∈
      S.Ω FC (Da + 4) (p + (n + 1) + 1 + 3) :=
    Omega.mono (GraphComp.subst_mem S (PolyComb.sigY (p + (n + 1)) 3 (0 : Fin 3)) hH0)
      (by omega) (by omega)
  have hT1 : {z : Fin (p + (n + 1) + 1 + 3) → ℝ |
        z ∘ PolyComb.sigY (p + (n + 1)) 3 (1 : Fin 3) ∈ graphOf (H 1)} ∈
      S.Ω FC (Da + 4) (p + (n + 1) + 1 + 3) :=
    Omega.mono (GraphComp.subst_mem S (PolyComb.sigY (p + (n + 1)) 3 (1 : Fin 3)) hH1)
      (by omega) (by omega)
  have hT2 : {z : Fin (p + (n + 1) + 1 + 3) → ℝ |
        z ∘ PolyComb.sigY (p + (n + 1)) 3 (2 : Fin 3) ∈ graphOf (H 2)} ∈
      S.Ω FC 3 (p + (n + 1) + 1 + 3) :=
    Omega.mono (GraphComp.subst_mem S (PolyComb.sigY (p + (n + 1)) 3 (2 : Fin 3)) hH2)
      (by omega) (by omega)
  -- intersect the three pullbacks at the common format
  have hT : ∀ i : Fin 3, {z : Fin (p + (n + 1) + 1 + 3) → ℝ |
        z ∘ PolyComb.sigY (p + (n + 1)) 3 i ∈ graphOf (H i)} ∈
      S.Ω FC (Dg i) (p + (n + 1) + 1 + 3) := by
    intro i
    fin_cases i
    · simpa [Dg] using hT0
    · simpa [Dg] using hT1
    · simpa [Dg] using hT2
  have hInter : (⋂ i : Fin 3, {z : Fin (p + (n + 1) + 1 + 3) → ℝ |
        z ∘ PolyComb.sigY (p + (n + 1)) 3 i ∈ graphOf (H i)}) ∈
      S.Ω (FC + 1) (∑ i : Fin 3, Dg i) (p + (n + 1) + 1 + 3) :=
    S.inter Dg (fun i : Fin 3 => {z : Fin (p + (n + 1) + 1 + 3) → ℝ |
        z ∘ PolyComb.sigY (p + (n + 1)) 3 i ∈ graphOf (H i)}) hT
  -- the hypersurface `value = y_0 + y_1 * y_2`
  have hhyp : {z : Fin (p + (n + 1) + 1 + 3) → ℝ |
        MvPolynomial.eval z (PolyComb.combPoly (p + (n + 1)) 3 linXPoly) = 0} ∈
      S.Ω (p + (n + 1) + 1 + 3) 3 (p + (n + 1) + 1 + 3) := by
    refine Omega.mono
      (S.hyp (p + (n + 1) + 1 + 3) (PolyComb.combPoly (p + (n + 1)) 3 linXPoly))
      le_rfl ?_
    have h1 := PolyComb.combPoly_totalDegree_le (p + (n + 1)) 3 linXPoly
    have h2 := linXPoly_totalDegree_le
    omega
  have hhyp' : {z : Fin (p + (n + 1) + 1 + 3) → ℝ |
        MvPolynomial.eval z (PolyComb.combPoly (p + (n + 1)) 3 linXPoly) = 0} ∈
      S.Ω (FC + 1) 3 (p + (n + 1) + 1 + 3) :=
    Omega.mono hhyp (by omega) le_rfl
  -- intersect and project the three fresh coordinates away
  have hInt2 := Omega_inter2 hInter hhyp'
  have hProj := Work.WilG0.projLastIter_mem S (p + (n + 1) + 1) 3 (FC + 1 + 1)
    ((∑ i : Fin 3, Dg i) + 3)
    ((⋂ i : Fin 3, {z : Fin (p + (n + 1) + 1 + 3) → ℝ |
        z ∘ PolyComb.sigY (p + (n + 1)) 3 i ∈ graphOf (H i)}) ∩
      {z : Fin (p + (n + 1) + 1 + 3) → ℝ |
        MvPolynomial.eval z (PolyComb.combPoly (p + (n + 1)) 3 linXPoly) = 0}) hInt2
  rw [PolyComb.projLastIter_eq_graph (p + (n + 1)) 3 H linXPoly] at hProj
  -- identify the polynomial combination with the flattened family
  have hsumD : (∑ i : Fin 3, Dg i) = 2 * Da + 11 := by
    rw [Fin.sum_univ_three]
    simp [Dg]
    omega
  have hfun : (fun y : Fin (p + (n + 1)) → ℝ => MvPolynomial.eval (fun i => H i y) linXPoly)
      = Work.WilkG4c.flatFun
          (fun (l : Fin p → ℝ) (t : Fin (n + 1) → ℝ) => α l + β l * t 0) := by
    funext y
    rw [linXPoly, MvPolynomial.eval_add, MvPolynomial.eval_mul, MvPolynomial.eval_X,
      MvPolynomial.eval_X, MvPolynomial.eval_X]
    simp only [H, h0, h1, h2, Matrix.cons_val_zero, Matrix.cons_val_one]
    simp [Work.WilkG4c.flatFun]
  have hset : graphOf (fun y : Fin (p + (n + 1)) → ℝ => MvPolynomial.eval (fun i => H i y) linXPoly)
      = WilkiesDesign.CG.famGraph
          (fun (l : Fin p → ℝ) (t : Fin (n + 1) → ℝ) => α l + β l * t 0) := by
    rw [hfun, Work.WilkG4c.famGraph_eq_graphOf_flatFun]
  rw [hset] at hProj
  refine Omega.mono hProj ?_ ?_
  · omega
  · omega

end Work.WilG4c
