/-
  WilG4c / HindUniform — uniformity in `q < p` of the induction hypothesis.

  `Work.WilkG4c.FLemPHigh S q (n+1) (PY q n)` supplies, *for each fixed* `q`, a triple of
  witnesses `(a_q, b_q, c_q)` (depending on `q`, and on `F0`).  The strong induction on the
  number of parameters `p` in the §5.3/§5.5 assembly needs a *single* triple that works
  simultaneously for every `q < p`.

  Since `{q : ℕ // q < p}` is finite (`Finset.range p`), the per-`q` witnesses can be merged:

  * the format is the maximum `A = sup_{q < p} a_q` (`ChartsOK` is monotone in it),
  * the degree polynomial is the sum `B = ∑_{q < p} b_q` (it has `ℕ`-coefficients and `D, r ≥ 0`,
    so every summand is dominated by the sum),
  * the count polynomial is `C = ∑_{q < p} (c_q * c_q + c_q + 1)`; for real coefficients `c_q`
    the summand `(c_q)² + c_q + 1` dominates `c_q` and is nonnegative at every real evaluation
    point, so the sum dominates every single `c_q` — the same "merge" device as in
    `StepLipAux.le_mergePoly_left`, folded over a finite set instead of over two summands.
-/
import Mathlib
import Submission.Work.WilG4c.StepLipAux
import Submission.Work.WilG4c.Defs
import Submission.Work.WilG4c.FLemAPI

set_option autoImplicit false
noncomputable section
open Classical
open scoped BigOperators

namespace Work.WilkG4c

/-- The per-summand merge device, folded: `x ≤ x² + x + 1`. -/
theorem le_sq_add_self_add_one (x : ℝ) : x ≤ x * x + x + 1 := by nlinarith [sq_nonneg x]

/-- **Uniformity of `FLemPHigh` in the parameter count.**  If `FLemPHigh` holds for
`(PY q n)` for every `q < p`, then a single triple of witnesses works for all of them at once:
the families live in different numbers of parameters `q`, so the `Ω`-filtration level `F0` is
kept fixed while the format, the degree polynomial and the count polynomial are merged over
the finite set `q < p`. -/
theorem HindUniform (S : WilkiesDesign.SOMin) (n p : ℕ)
    (hind : ∀ q : ℕ, q < p → Work.WilkG4c.FLemPHigh S q (n + 1) (Work.WilkG4c.PY q n))
    (F0 : ℕ) :
    ∃ (A : ℕ) (B : MvPolynomial (Fin 2) ℕ) (C : MvPolynomial (Fin 4) ℝ),
      ∀ (q : ℕ) (hq : q < p) (D r k : ℕ) (ε : ℝ), 0 < ε → ε < 1 → 1 ≤ r →
      ∀ (Λ : Set (Fin q → ℝ)) (F : Work.WilkG4c.Family k q (n + 1)),
        Work.WilkG4c.PY q n r k F →
        (∀ i, WilkiesDesign.CG.famGraph (F i) ∈ S.Ω F0 D (q + (n + 1) + 1)) →
        Work.WilkG4c.ValuesIn01 Λ F →
        ∃ Φ : Finset (Work.WilkG4c.ChartTuple q (n + 1)),
          (Φ.card : ℝ) ≤ MvPolynomial.eval ![(D : ℝ), (r : ℝ), (k : ℝ), -Real.log ε] C ∧
          Work.WilkG4c.ChartsOK S A (MvPolynomial.eval ![D, r] B) r Λ F Φ ∧
          Work.WilkG4c.Covers Λ F Φ ε := by
  classical
  -- the per-`q` witnesses, chosen over the finite set `q ∈ Finset.range p`
  have hsub : ∀ x : {q : ℕ // q ∈ Finset.range p},
      ∃ (a : ℕ) (b : MvPolynomial (Fin 2) ℕ) (c : MvPolynomial (Fin 4) ℝ),
      ∀ (D r k : ℕ) (ε : ℝ), 0 < ε → ε < 1 → 1 ≤ r →
      ∀ (Λ : Set (Fin x.1 → ℝ)) (F : Work.WilkG4c.Family k x.1 (n + 1)),
        Work.WilkG4c.PY x.1 n r k F →
        (∀ i, WilkiesDesign.CG.famGraph (F i) ∈ S.Ω F0 D (x.1 + (n + 1) + 1)) →
        Work.WilkG4c.ValuesIn01 Λ F →
        ∃ Φ : Finset (Work.WilkG4c.ChartTuple x.1 (n + 1)),
          (Φ.card : ℝ) ≤ MvPolynomial.eval ![(D : ℝ), (r : ℝ), (k : ℝ), -Real.log ε] c ∧
          Work.WilkG4c.ChartsOK S a (MvPolynomial.eval ![D, r] b) r Λ F Φ ∧
          Work.WilkG4c.Covers Λ F Φ ε :=
    fun x => hind x.1 (Finset.mem_range.mp x.2) F0
  choose a b c hspec using hsub
  refine ⟨(Finset.range p).attach.sup a,
    (∑ x ∈ (Finset.range p).attach, b x),
    (∑ x ∈ (Finset.range p).attach, (c x * c x + c x + 1)), ?_⟩
  intro q hq D r k ε hε hε1 hr Λ F hPY hΩ hval
  set xq : {q : ℕ // q ∈ Finset.range p} := ⟨q, Finset.mem_range.mpr hq⟩ with hxq
  have hx : xq ∈ (Finset.range p).attach := Finset.mem_attach _ _
  obtain ⟨Φ, hcard, hok, hcov⟩ :=
    hspec xq D r k ε hε hε1 hr Λ F hPY hΩ hval
  refine ⟨Φ, ?_, ?_, hcov⟩
  · -- cardinality: `eval C` is a sum of the nonnegative `(eval c_y)² + eval c_y + 1`
    have hterm : ∀ y ∈ (Finset.range p).attach,
        0 ≤ MvPolynomial.eval ![(D : ℝ), (r : ℝ), (k : ℝ), -Real.log ε]
              (c y * c y + c y + 1) := by
      intro y _
      simp only [map_add, map_mul, map_one]
      nlinarith [sq_nonneg (MvPolynomial.eval
        ![(D : ℝ), (r : ℝ), (k : ℝ), -Real.log ε] (c y))]
    have hsingle := Finset.single_le_sum
      (s := (Finset.range p).attach)
      (f := fun y => MvPolynomial.eval ![(D : ℝ), (r : ℝ), (k : ℝ), -Real.log ε]
        (c y * c y + c y + 1)) hterm hx
    have hself : MvPolynomial.eval ![(D : ℝ), (r : ℝ), (k : ℝ), -Real.log ε] (c xq) ≤
        MvPolynomial.eval ![(D : ℝ), (r : ℝ), (k : ℝ), -Real.log ε]
          (c xq * c xq + c xq + 1) := by
      simp only [map_add, map_mul, map_one]
      exact le_sq_add_self_add_one _
    rw [map_sum]
    linarith
  · -- format and degree: the format is the supremum, the degree polynomial the sum
    have hsup : a xq ≤ (Finset.range p).attach.sup a := Finset.le_sup (f := a) hx
    have hdeg : MvPolynomial.eval ![D, r] (b xq) ≤
        MvPolynomial.eval ![D, r] (∑ y ∈ (Finset.range p).attach, b y) := by
      rw [map_sum]
      exact Finset.single_le_sum (s := (Finset.range p).attach)
        (f := fun y => MvPolynomial.eval ![D, r] (b y)) (fun y _ => Nat.zero_le _) hx
    exact ChartsOK_mono hok hsup hdeg

end Work.WilkG4c

/-!
## Namespace compatibility

The module lives at `Submission/Work/WilG4c/HindUniform.lean`, i.e. in the area whose
convention is `Work.WilG4c`, while the requested statement (which refers to the
`Work.WilkG4c` vocabulary of `Defs`/`FLemAPI`/`StepLipAux`) was written inside
`namespace Work.WilkG4c`.  Both names are provided, with the identical statement, so that
consumers may use either spelling.
-/
namespace Work.WilG4c

/-- `Work.WilG4c.HindUniform`: the same statement as `Work.WilkG4c.HindUniform`, under the
namespace of this module's path. -/
theorem HindUniform (S : WilkiesDesign.SOMin) (n p : ℕ)
    (hind : ∀ q : ℕ, q < p → Work.WilkG4c.FLemPHigh S q (n + 1) (Work.WilkG4c.PY q n))
    (F0 : ℕ) :
    ∃ (A : ℕ) (B : MvPolynomial (Fin 2) ℕ) (C : MvPolynomial (Fin 4) ℝ),
      ∀ (q : ℕ) (hq : q < p) (D r k : ℕ) (ε : ℝ), 0 < ε → ε < 1 → 1 ≤ r →
      ∀ (Λ : Set (Fin q → ℝ)) (F : Work.WilkG4c.Family k q (n + 1)),
        Work.WilkG4c.PY q n r k F →
        (∀ i, WilkiesDesign.CG.famGraph (F i) ∈ S.Ω F0 D (q + (n + 1) + 1)) →
        Work.WilkG4c.ValuesIn01 Λ F →
        ∃ Φ : Finset (Work.WilkG4c.ChartTuple q (n + 1)),
          (Φ.card : ℝ) ≤ MvPolynomial.eval ![(D : ℝ), (r : ℝ), (k : ℝ), -Real.log ε] C ∧
          Work.WilkG4c.ChartsOK S A (MvPolynomial.eval ![D, r] B) r Λ F Φ ∧
          Work.WilkG4c.Covers Λ F Φ ε :=
  _root_.Work.WilkG4c.HindUniform S n p hind F0

end Work.WilG4c
