/-
  WilG4c / `StepLipHighPsiAux3` — small generic helpers for the `StepLipHighPsiCond` assembly
  (kept in their own module so that the assembly stays inside the per-file build limit).
-/
import Mathlib
import Submission.Work.WilG4c.StepLipHighPsiAux2

set_option autoImplicit false
noncomputable section
open Classical
open scoped BigOperators

namespace Work.WilG4c

/-- Evaluation of `aeval` in general index types: replacing the variables of `p` by the
polynomials `f i` and evaluating the result at `σ` is the same as evaluating `p` at the point
whose `i`-th coordinate is the value of `f i`. -/
theorem eval_aeval_eq_gen {σ τ R : Type*} [CommSemiring R] (f : σ → MvPolynomial τ R)
    (σ' : τ → R) (p : MvPolynomial σ R) :
    MvPolynomial.eval σ' (MvPolynomial.aeval f p)
      = MvPolynomial.eval (fun i => MvPolynomial.eval σ' (f i)) p := by
  have h := MvPolynomial.comp_aeval f (MvPolynomial.aeval σ')
  have key := congrArg (fun (φ : MvPolynomial σ R →ₐ[R] R) => φ p) h
  simpa only [AlgHom.comp_apply, MvPolynomial.aeval_eq_eval] using key

/-- Evaluating a `ℕ`-polynomial that has been cast to `ℝ` and renamed from `Fin 3` into
`Fin 4`, at a point whose first three coordinates are naturals. -/
theorem eval_cast_rename3 (P : MvPolynomial (Fin 3) ℕ) :
    ∀ (D r k : ℕ) (u : ℝ),
      MvPolynomial.eval ![(D : ℝ), (r : ℝ), (k : ℝ), u]
        (MvPolynomial.rename (Fin.castLE (by norm_num : 3 ≤ 4))
          (MvPolynomial.map (Nat.castRingHom ℝ) P))
        = ((MvPolynomial.eval ![D, r, k] P : ℕ) : ℝ) := by
  intro D r k u
  have hcomp : (![(D : ℝ), (r : ℝ), (k : ℝ), u] ∘ (Fin.castLE (by norm_num : 3 ≤ 4)))
      = ![(D : ℝ), (r : ℝ), (k : ℝ)] := by
    funext i; fin_cases i <;> simp [Fin.castLE]
  rw [MvPolynomial.eval_rename, hcomp, MvPolynomial.eval_map]
  have hpt : ![(D : ℝ), (r : ℝ), (k : ℝ)] = ⇑(Nat.castRingHom ℝ) ∘ ![D, r, k] := by
    funext i; fin_cases i <;> simp
  rw [hpt]
  exact (MvPolynomial.eval₂_comp (Nat.castRingHom ℝ) ![D, r, k] P).symm

/-- The cardinality of a `Finset.biUnion` over `attach` is at most the number of indices times
any common upper bound of the cardinalities of the members. -/
theorem card_attach_biUnion_le {α β : Type*} [DecidableEq β] (C : Finset α)
    (f : {x // x ∈ C} → Finset β) (M : ℝ) (h : ∀ i ∈ C.attach, ((f i).card : ℝ) ≤ M) :
    ((C.attach.biUnion f).card : ℝ) ≤ (C.card : ℝ) * M := by
  have h2 : (C.attach.biUnion f).card ≤ ∑ i ∈ C.attach, (f i).card :=
    Finset.card_biUnion_le
  have h3 : (∑ i ∈ C.attach, ((f i).card : ℝ)) ≤ (C.attach.card : ℝ) * M := by
    have := Finset.sum_le_card_nsmul C.attach (fun i => ((f i).card : ℝ)) M h
    simpa only [nsmul_eq_mul] using this
  calc ((C.attach.biUnion f).card : ℝ)
      ≤ ((∑ i ∈ C.attach, (f i).card : ℕ) : ℝ) := by exact_mod_cast h2
    _ = ∑ i ∈ C.attach, ((f i).card : ℝ) := by push_cast; ring
    _ ≤ (C.attach.card : ℝ) * M := h3
    _ = (C.card : ℝ) * M := by rw [Finset.card_attach]

/-- The merging bound for a product of two nonnegative reals. -/
theorem mul_le_merge_sq (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    x * y ≤ x * x + y * y + (x + y) + 1 := by
  nlinarith [sq_nonneg (x - y), mul_nonneg hx hy, sq_nonneg y]

end Work.WilG4c
