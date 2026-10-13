/-
  WilCrux : `Work.WilCrux.AbsLtGraphMem` — the sub-level set of `|h|` for a function whose
  graph is `Ω`-definable.

  If the graph of `h : ℝⁿ → ℝ` lies in `S.Ω F D (n+1)`, then for every real `ε` the set

      {l : ℝⁿ | |h l| < ε}

  is `Ω`-definable, with a format `A` depending only on `F` and `n` (not on `D`, on `h`, or on
  `ε`) and a degree bounded by `q.eval D` for a fixed one-variable polynomial `q ∈ ℕ[X]`.

  Construction.  Since `|h l| < ε ↔ -ε < h l ∧ h l < ε` (Mathlib's `abs_lt`, valid
  unconditionally over a linear ordered additive group), the set is the intersection of the two
  sub-level sets

  * `{l | -ε < h l}` = `{l | (const (-ε)) l < h l}`, and
  * `{l | h l < ε}` = `{l | h l < (const ε) l}`,

  i.e. two comparisons of the graph of `h` with the graphs of constant functions, which are
  supplied by `Work.WilG4a.setOf_lt_graph_mem`.  The graph of a constant `c` is the hyperplane
  `z (last n) = c`, an `Ω`-set of format `n+1` and degree `≤ 1` by `SOMin.hyp`; both the graph
  of `h` and that hyperplane are pushed up to the common format `max F (n+1)` and the common
  degree `max D 1` before the comparison lemma is applied.

  Degree bookkeeping.  The comparison lemma returns the degree

      e := MvPolynomial.eval ![max D 1, 0] b,

  where `b ∈ ℕ[X₀,X₁]` is a fixed two-variable polynomial (the lemma's output); the intersection
  doubles it.  `e` is *not* a polynomial in `D`, but `Work.WilG1.psubst b 0` turns it into a
  one-variable polynomial with `(psubst b 0).eval (max D 1) = e`, and `max D 1 ≤ D + 1`, so the
  shift `X ↦ X + 1` (polynomial composition) bounds it by a polynomial in `D`:

      2 * e ≤ 2 * (psubst b 0).eval (D + 1) = (C 2 * (psubst b 0).comp (X + C 1)).eval D.
-/
import Mathlib
import Submission.Work.Wilkies.CG.Spec
import Submission.Work.WilG4a.setOf_lt_graph_mem
import Submission.Work.WilG1.Basic
import Submission.Work.WilG0.API

namespace Work.WilCrux

open WilkiesDesign WilkiesConjecture

theorem AbsLtGraphMem (S : WilkiesDesign.SOMin) {n F : ℕ} :
    ∃ (A : ℕ) (q : Polynomial ℕ), ∀ (D : ℕ) (h : (Fin n → ℝ) → ℝ),
      WilkiesDesign.graphOf h ∈ S.Ω F D (n + 1) → ∀ (ε : ℝ),
      {l : Fin n → ℝ | |h l| < ε} ∈ S.Ω A (q.eval D) n := by
  -- The comparison of two `Ω`-graphs: format `a` and two-variable degree polynomial `b`,
  -- both attached to the common format `max F (n+1)`.
  obtain ⟨a, b, hb⟩ := Work.WilG4a.setOf_lt_graph_mem S n (max F (n + 1))
  -- The degree polynomial: `2 * (psubst b 0)` shifted by `X ↦ X + 1`, accounting both for the
  -- two comparisons and for the passage from `max D 1` to `D + 1`.
  refine ⟨max (a + 1) n,
    Polynomial.C 2 * (Work.WilG1.psubst b 0).comp (Polynomial.X + Polynomial.C 1), ?_⟩
  intro D h hh ε
  -- The graph of a constant is the zero set of the linear polynomial `X (last n) - C c`.
  have hgraphset : ∀ c : ℝ, WilkiesDesign.graphOf (fun _ : Fin n → ℝ => c) =
      {z : Fin (n + 1) → ℝ | MvPolynomial.eval z
        ((MvPolynomial.X (Fin.last n) : MvPolynomial (Fin (n + 1)) ℝ) -
          MvPolynomial.C c) = 0} := by
    intro c
    ext z
    simp [WilkiesDesign.graphOf, sub_eq_zero]
  -- `graphOf (const c) ∈ S.Ω (max F (n+1)) (max D 1) (n+1)`.
  have hconst : ∀ c : ℝ, WilkiesDesign.graphOf (fun _ : Fin n → ℝ => c) ∈
      S.Ω (max F (n + 1)) (max D 1) (n + 1) := by
    intro c
    have htd : ((MvPolynomial.X (Fin.last n) : MvPolynomial (Fin (n + 1)) ℝ) -
        MvPolynomial.C c).totalDegree ≤ 1 := by
      refine le_trans (MvPolynomial.totalDegree_sub _ _) ?_
      rw [max_le_iff]
      exact ⟨by rw [MvPolynomial.totalDegree_X],
        by rw [MvPolynomial.totalDegree_C]; omega⟩
    have h0 : WilkiesDesign.graphOf (fun _ : Fin n → ℝ => c) ∈ S.Ω (n + 1) 1 (n + 1) := by
      rw [hgraphset c]
      exact Work.WilG0.Omega_mono_D htd (S.hyp (n + 1) _)
    exact Work.WilG0.Omega_mono_FD (le_max_right F (n + 1)) (le_max_right D 1) h0
  -- Raise the graph of `h` to the common format and degree.
  have hh' : WilkiesDesign.graphOf h ∈ S.Ω (max F (n + 1)) (max D 1) (n + 1) :=
    Work.WilG0.Omega_mono_FD (le_max_left F (n + 1)) (le_max_left D 1) hh
  -- The two comparisons with the constant functions `-ε` and `ε`.
  have hp1 := hb (max D 1) 0 (hconst (-ε)) hh'
  have hp2 := hb (max D 1) 0 hh' (hconst ε)
  have hinter := Work.WilG0.Omega_inter2 hp1 hp2
  -- `|h l| < ε ↔ -ε < h l ∧ h l < ε`.
  have hset : {l : Fin n → ℝ | |h l| < ε} =
      {l : Fin n → ℝ | -ε < h l} ∩ {l : Fin n → ℝ | h l < ε} := by
    ext l
    simp only [Set.mem_ofPred_eq, Set.mem_inter_iff]
    exact abs_lt
  rw [← hset] at hinter
  -- Weaken the format to `max (a+1) n` and bound the doubled degree by `q.eval D`.
  refine Work.WilG1.Omega.mono hinter (le_max_left (a + 1) n) ?_
  have he : MvPolynomial.eval ![max D 1, 0] b = (Work.WilG1.psubst b 0).eval (max D 1) :=
    (Work.WilG1.eval_psubst b 0 (max D 1)).symm
  have hmon : (Work.WilG1.psubst b 0).eval (max D 1) ≤ (Work.WilG1.psubst b 0).eval (D + 1) :=
    Work.WilG1.Polynomial.eval_mono (by omega)
  have hcomp : (Work.WilG1.psubst b 0).eval (D + 1) =
      ((Work.WilG1.psubst b 0).comp (Polynomial.X + Polynomial.C 1)).eval D := by
    rw [Polynomial.eval_comp]
    congr 1
    simp [Polynomial.eval_add, Polynomial.eval_X]
  have hle : MvPolynomial.eval ![max D 1, 0] b ≤
      ((Work.WilG1.psubst b 0).comp (Polynomial.X + Polynomial.C 1)).eval D := by
    rw [he, ← hcomp]
    exact hmon
  rw [Polynomial.eval_mul, Polynomial.eval_C]
  omega

end Work.WilCrux
