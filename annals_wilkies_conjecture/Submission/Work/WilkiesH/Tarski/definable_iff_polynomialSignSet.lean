import Mathlib
import Submission.Work.WilkiesH.Defs
import Submission.Work.WilLibTS.All
import Submission.Work.WilkiesI.Basic
import Submission.Work.WilkiesH.Tarski.eval_realize_term
import Submission.Work.WilkiesH.Tarski.isSemialgebraic_of_polynomialSignSet

/-!
# Tarski–Seidenberg over `ℝ`: definable = Boolean combination of polynomial signs

`WilkiesConjecture.IsSemialgebraic S` (frozen in `ChallengeDeps.lean`) is model-theoretic
definability of `S ⊆ ℝⁿ` in the language of rings `Language.ring` with all of `ℝ` as parameters,
i.e. `Set.Definable Set.univ Language.ring S`.  `Work.WilLibTS.TS.PolynomialSignSet` is the
"geometric" predicate: `S` is built from zero sets and positivity sets of real polynomials by
complementation and finite unions.

The two are equivalent, and this file proves it.

* `←` (every `PolynomialSignSet` is definable): the file `isSemialgebraic_of_polynomialSignSet`
  of this area, a structural induction using `Work.WilkiesI.definable_eval_eq` and
  `definable_eval_pos`.

* `→` (every definable set is a `PolynomialSignSet`): the content of this file.  This is
  Tarski–Seidenberg / quantifier elimination.  The proof is a syntactic induction on the formula
  defining `S`, the only non-trivial step being the elimination of a quantifier `∃ y`, which is
  the projection theorem
  `Work.WilLibTS.TS.SignElimination.polynomialSignSet_projection_finite` (the ported
  Tarski–Seidenberg theorem for `PolynomialSignSet`).

The induction is formulated in the following "affine" form.  A formula `φ` with free variables
`β` and `l` further bound variables is interpreted in an ambient space of coordinates `ι` by

* assigning to each free variable `b : β` the polynomial value `eval v (ρ b)`, and
* assigning to each bound variable `i : Fin l` the polynomial value `eval v (q i)`.

Then the set of `v : ι → ℝ` realizing `φ` is a `PolynomialSignSet` in the coordinates `ι`.  The
extra generality in `ι` (rather than fixing `ι = β`) is what makes the universal-quantifier case
work: going under a `∀` we may pass to the ambient `ι ⊕ Fin 1`, interpreting the newly bound
variable by the new coordinate, and then project it away again.
-/

set_option autoImplicit false

noncomputable section

open FirstOrder FirstOrder.Language

namespace Work.WilkiesH.Tarski

universe u

/-- **Quantifier elimination in affine coordinates.**  For a ring formula `φ` with free variables
`β` and `l` bound variables, any polynomial interpretation `ρ` of the free variables and `q` of
the bound variables gives a `PolynomialSignSet` in the ambient coordinates `ι`. -/
theorem pss_of_realize {β : Type u} :
    ∀ {ι : Type u} (ρ : β → MvPolynomial ι ℝ) {l : ℕ} (φ : Language.ring.BoundedFormula β l)
      (q : Fin l → MvPolynomial ι ℝ),
      Work.WilLibTS.TS.PolynomialSignSet (fun v : ι → ℝ => v)
        {v : ι → ℝ | φ.Realize (fun b => MvPolynomial.eval v (ρ b))
          (fun i => MvPolynomial.eval v (q i))} := by
  intro ι ρ l φ q
  induction φ generalizing ι ρ with
  | falsum =>
    refine (Work.WilLibTS.TS.PolynomialSignSet.empty (c := fun v : ι → ℝ => v)).congr ?_
    ext v
    simp only [Set.mem_empty_iff_false, Set.mem_ofPred_eq]
    exact BoundedFormula.realize_bot.symm
  | equal t1 t2 =>
    -- both sides of the equation are interpreted as polynomials by `eval_realize_term`
    obtain ⟨P₁, hP₁⟩ := eval_realize_term (Sum.elim ρ q) t1
    obtain ⟨P₂, hP₂⟩ := eval_realize_term (Sum.elim ρ q) t2
    refine (Work.WilLibTS.TS.PolynomialSignSet.zero (c := fun v : ι → ℝ => v) (P₁ - P₂)).congr ?_
    ext v
    simp only [Set.mem_ofPred_eq]
    show (MvPolynomial.eval v (P₁ - P₂) = 0) ↔
      (Term.realize (Sum.elim (fun b => MvPolynomial.eval v (ρ b))
          (fun i => MvPolynomial.eval v (q i))) t1 =
       Term.realize (Sum.elim (fun b => MvPolynomial.eval v (ρ b))
          (fun i => MvPolynomial.eval v (q i))) t2)
    rw [show Sum.elim (fun b => MvPolynomial.eval v (ρ b)) (fun i => MvPolynomial.eval v (q i))
        = (fun b' => MvPolynomial.eval v (Sum.elim ρ q b')) from
          funext (by rintro (b | i) <;> rfl), hP₁ v, hP₂ v]
    simp [map_sub, sub_eq_zero]
  | rel R _ts => exact R.elim
  | imp f1 f2 ih1 ih2 =>
    -- `φ → ψ` is `¬φ ∨ ψ`
    refine ((ih1 ρ q).compl.union (ih2 ρ q)).congr ?_
    ext v
    simp only [Set.mem_union, Set.mem_compl_iff, Set.mem_ofPred_eq, BoundedFormula.realize_imp]
    exact imp_iff_not_or.symm
  | all f ih =>
    -- pass to the ambient `ι ⊕ Fin 1`, interpret the bound variable `Fin.last` by the new
    -- coordinate, and project it away using Tarski–Seidenberg
    rename_i n
    set ρ' : β → MvPolynomial (ι ⊕ Fin 1) ℝ := fun b => MvPolynomial.rename Sum.inl (ρ b)
    set q' : Fin (n + 1) → MvPolynomial (ι ⊕ Fin 1) ℝ :=
      Fin.snoc (fun i => MvPolynomial.rename Sum.inl (q i)) (MvPolynomial.X (Sum.inr 0))
    have hT : Work.WilLibTS.TS.PolynomialSignSet (fun V : (ι ⊕ Fin 1) → ℝ => V)
        {V | f.Realize (fun b => MvPolynomial.eval V (ρ' b))
          (fun i => MvPolynomial.eval V (q' i))} := ih ρ' q'
    have hproj := Work.WilLibTS.TS.SignElimination.polynomialSignSet_projection_sum
        (ι := ι) (κ := Fin 1) hT.compl
    refine hproj.compl.congr (Set.ext fun v => ?_)
    simp only [BoundedFormula.realize_all, Set.mem_ofPred_eq, Set.mem_compl_iff, not_exists,
      not_not]
    constructor
    · intro hv x
      have hb : (fun i => MvPolynomial.eval (Sum.elim v (fun _ => x)) (q' i)) =
          Fin.snoc (fun i => MvPolynomial.eval v (q i)) x := by
        funext i
        rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
        · simp [q', Fin.snoc_castSucc, MvPolynomial.eval_rename]
        · simp [q', Fin.snoc_last]
      have ha : (fun b => MvPolynomial.eval (Sum.elim v (fun _ => x)) (ρ' b)) =
          fun b => MvPolynomial.eval v (ρ b) := by
        funext b
        simp [ρ', MvPolynomial.eval_rename]
      have h := hv (fun _ => x)
      rwa [ha, hb] at h
    · intro hw y
      have hb : (fun i => MvPolynomial.eval (Sum.elim v y) (q' i)) =
          Fin.snoc (fun i => MvPolynomial.eval v (q i)) (y 0) := by
        funext i
        rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
        · simp [q', Fin.snoc_castSucc, MvPolynomial.eval_rename]
        · simp [q', Fin.snoc_last]
      have ha : (fun b => MvPolynomial.eval (Sum.elim v y) (ρ' b)) =
          fun b => MvPolynomial.eval v (ρ b) := by
        funext b
        simp [ρ', MvPolynomial.eval_rename]
      have h := hw (y 0)
      rw [← ha, ← hb] at h
      exact h

/-- **Tarski–Seidenberg over `ℝ`.**  A subset of `ℝⁿ` is definable in the language of rings over
`ℝ` if and only if it is a Boolean combination of polynomial sign conditions. -/
theorem definable_iff_polynomialSignSet {n : ℕ} {S : Set (Fin n → ℝ)} : WilkiesConjecture.IsSemialgebraic S ↔ Work.WilLibTS.TS.PolynomialSignSet (fun x : Fin n → ℝ => x) S := by
  refine ⟨fun hS => ?_, isSemialgebraic_of_polynomialSignSet⟩
  -- write `S` as the realization set of a single ring formula over the parameters `ℝ`
  rw [WilkiesConjecture.IsSemialgebraic, Set.definable_iff_exists_formula_sum] at hS
  obtain ⟨φ, rfl⟩ := hS
  -- interpret the parameter variables by constants and the `ℝⁿ`-variables by the coordinates
  refine (pss_of_realize (ρ := Sum.elim (fun a : ↥(Set.univ : Set ℝ) => MvPolynomial.C (a : ℝ))
    (fun i : Fin n => MvPolynomial.X i)) φ (fun i : Fin 0 => Fin.elim0 i)).congr ?_
  ext v
  simp only [Set.mem_ofPred_eq]
  rw [show (fun b : ↥(Set.univ : Set ℝ) ⊕ Fin n => MvPolynomial.eval v
      ((Sum.elim (fun a : ↥(Set.univ : Set ℝ) => MvPolynomial.C (a : ℝ))
        (fun i : Fin n => MvPolynomial.X i)) b)) = Sum.elim (Subtype.val) v from
      funext (by rintro (a | i) <;> simp)]
  rw [Formula.Realize]
  exact iff_of_eq (congrArg (fun x : Fin 0 → ℝ =>
    BoundedFormula.Realize φ (Sum.elim Subtype.val v) x) (Subsingleton.elim _ _))

end Work.WilkiesH.Tarski
