/-
  WilG4a : `Work.WilG4a.setOf_lt_graph_mem` — the comparison of two `Ω`-graphs.

  If the graphs of `f g : ℝ^p → ℝ` are `Ω`-definable with format `F` and degree `D`, then the
  parameter set `{l | f l < g l}` is `Ω`-definable, with a format depending only on `F` and
  `p` and a degree bounded by a polynomial in `D` (here `2 * D + 5`).

  Construction.  In the joint ambient `ℝ^{p+2}` with coordinates `(l, y, t)` (`l` = the first
  `p` coordinates, `y` = coordinate `p`, `t` = coordinate `p+1`), put

  * `graphLift f = {w | Fin.init w ∈ graphOf f}` — the lifted graph of `f` (`y = f l`); this is
    `SOMin.prod_right` applied to `graphOf f`, costing `+1` in the format and nothing in the
    degree;
  * `pullZ2 p (graphOf g)` — the pullback of `graphOf g` along `iota1 p`, i.e. `t = g l`; this
    is a *substitution atom* (`Work.WilG4a.subst_mem`), costing `2 * ((p+2) + (p+1)) + 1` in
    the format and `+2` in the degree;
  * `yLtT p = {w | w (last of the first p+1) < w (last)}` — the half-space `y < t`; the
    strict coordinate inequality `Work.WilG1.Calc.lt_mem` gives format `p + 5` and degree `3`.

  Their intersection is `ltJoint p f g`; two projections (`SOMin.proj`) eliminate `t` and then
  `y`, and by `Work.WilG4a.ltJoint_proj_eq` the result is exactly `{l | f l < g l}`.

  Bookkeeping: the common format is `max (F + 2 * ((p+2) + (p+1)) + 1) (p + 5)`, the two
  intersections cost `+2` and the two projections `+2`, so the final format is
  `max (F + 2 * ((p+2) + (p+1)) + 1) (p + 5) + 4`, independent of `D`; the degree is
  `D + (D + 2) + 3 = 2 * D + 5`, which is the value of the fixed two-variable polynomial
  `5 + 2 * X₀` at `![D, r]` (in particular it does not depend on `r`).
-/
import Mathlib
import Submission.Work.WilG4a.Defs
import Submission.Work.WilG1.Basic
import Submission.Work.WilG1.Calc.lt_mem
import Submission.Work.WilG5.Reindex
import Submission.Work.WilG4a.ltGraphDefs
import Submission.Work.WilG4a.subst_mem
import Submission.Work.WilG0.API

set_option autoImplicit false
noncomputable section
open Classical

namespace Work.WilG4a

open WilkiesDesign WilkiesConjecture

theorem setOf_lt_graph_mem (S : WilkiesDesign.SOMin) (p F : ℕ) : ∃ (a : ℕ) (b : MvPolynomial (Fin 2) ℕ), ∀ (D r : ℕ) {f g : (Fin p → ℝ) → ℝ}, WilkiesDesign.graphOf f ∈ S.Ω F D (p + 1) → WilkiesDesign.graphOf g ∈ S.Ω F D (p + 1) → {l : Fin p → ℝ | f l < g l} ∈ S.Ω a (MvPolynomial.eval ![D, r] b) p := by
  refine ⟨max (F + 2 * ((p + 2) + (p + 1)) + 1) (p + 5) + 4,
    MvPolynomial.C 5 + MvPolynomial.C 2 * MvPolynomial.X 0, ?_⟩
  intro D r f g hf hg
  -- The three pieces of the joint set, with their individual format/degree bounds.
  have hA : graphLift f ∈ S.Ω (F + 1) D (p + 2) := S.prod_right hf
  have hB : pullZ2 p (graphOf g) ∈
      S.Ω (F + 2 * ((p + 2) + (p + 1)) + 1) (D + 2) (p + 2) :=
    subst_mem S (iota1 p) hg
  have hC : yLtT p ∈ S.Ω (p + 5) 3 (p + 2) := by
    have h := WilG1.Calc.lt_mem (S := S) (n := p + 2) 0
      (Fin.castSucc (Fin.last p)) (Fin.last (p + 1))
    exact mem_mono h (by omega) (by simp)
  -- Raise all three to the common format.
  have hA' : graphLift f ∈ S.Ω (max (F + 2 * ((p + 2) + (p + 1)) + 1) (p + 5)) D (p + 2) :=
    mem_mono hA (by omega) le_rfl
  have hB' : pullZ2 p (graphOf g) ∈
      S.Ω (max (F + 2 * ((p + 2) + (p + 1)) + 1) (p + 5)) (D + 2) (p + 2) :=
    mem_mono hB (le_max_left _ _) le_rfl
  have hC' : yLtT p ∈ S.Ω (max (F + 2 * ((p + 2) + (p + 1)) + 1) (p + 5)) 3 (p + 2) :=
    mem_mono hC (le_max_right _ _) le_rfl
  -- The two intersections building the joint set.
  have hAB : graphLift f ∩ pullZ2 p (graphOf g) ∈
      S.Ω (max (F + 2 * ((p + 2) + (p + 1)) + 1) (p + 5) + 1) (D + (D + 2)) (p + 2) :=
    WilG0.Omega_inter2 (S := S) hA' hB'
  have hC'' : yLtT p ∈
      S.Ω (max (F + 2 * ((p + 2) + (p + 1)) + 1) (p + 5) + 1) 3 (p + 2) :=
    mem_mono hC' (by omega) le_rfl
  have hJ : ltJoint p f g ∈
      S.Ω (max (F + 2 * ((p + 2) + (p + 1)) + 1) (p + 5) + 1 + 1) (D + (D + 2) + 3) (p + 2) :=
    WilG0.Omega_inter2 (S := S) hAB hC''
  -- Project out `t`, then `y`; these are the two `SOMin.proj` steps.
  have hp1 : projLast (ltJoint p f g) ∈
      S.Ω (max (F + 2 * ((p + 2) + (p + 1)) + 1) (p + 5) + 1 + 1 + 1)
        (D + (D + 2) + 3) (p + 1) :=
    S.proj hJ
  have hp2 : projLast (projLast (ltJoint p f g)) ∈
      S.Ω (max (F + 2 * ((p + 2) + (p + 1)) + 1) (p + 5) + 1 + 1 + 1 + 1)
        (D + (D + 2) + 3) p :=
    S.proj hp1
  -- The set identity: the double projection is `{l | f l < g l}`.
  have hset : projLast (projLast (ltJoint p f g)) = {l : Fin p → ℝ | f l < g l} := by
    ext l
    simp only [projLast, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨z, t, hzt⟩
      rw [snoc_snoc_mem_ltJoint] at hzt
      obtain ⟨hz, ht, hlt⟩ := hzt
      rw [← hz, ← ht]
      exact hlt
    · intro hlt
      exact ⟨f l, g l, (snoc_snoc_mem_ltJoint f g l (f l) (g l)).mpr ⟨rfl, rfl, hlt⟩⟩
  rw [hset] at hp2
  -- Evaluate the degree polynomial: `5 + 2 * D`.
  have hb : MvPolynomial.eval ![D, r]
      (MvPolynomial.C 5 + MvPolynomial.C 2 * MvPolynomial.X 0) = 2 * D + 5 := by
    have h : MvPolynomial.eval ![D, r]
        (MvPolynomial.C 5 + MvPolynomial.C 2 * MvPolynomial.X 0) = 5 + 2 * D := by
      simp [MvPolynomial.eval_add, MvPolynomial.eval_mul]
    omega
  rw [hb]
  exact mem_mono hp2 (by omega) (by omega)

end Work.WilG4a
