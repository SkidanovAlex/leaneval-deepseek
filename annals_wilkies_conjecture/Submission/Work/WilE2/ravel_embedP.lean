/-
  Work.WilE2 — the transport of an EA polynomial along the extension of the ambient space by
  one useless coordinate (`embedP : EPoly n r → EPoly (n+1) r`) and of the chain by a zero
  coefficient in that coordinate (`ESys.ravel`).

  This module proves `ravel_embedP`:
  * evaluation: `(S.ravel).ev (embedP P) z = S.ev P (Fin.init z)` — the new coordinate is
    ignored, and the chain of the new system only sees the old coordinates;
  * the symbolic derivatives in the old directions: `∂ᵢ` commutes with `embedP`;
  * the symbolic derivative in the *new* direction vanishes, because no variable of
    `embedP P` is indexed by `Sum.inl (Fin.last n)` and the new coefficient is `0`;
  * the total degree does not increase.

  The ingredients are the Mathlib lemmas `MvPolynomial.pderiv_rename`,
  `MvPolynomial.pderiv_eq_zero_of_notMem_vars`/`MvPolynomial.mem_vars_rename` and
  `MvPolynomial.totalDegree_rename_le`, plus a short induction for the evaluation of a
  renamed polynomial.
-/
import Mathlib
import Submission.Work.WilE2.KhoSphereDefs

set_option autoImplicit false

noncomputable section
open Classical

namespace Work.WilE2

/-- The reindexing `Sum.map Fin.castSucc id` used to define `embedP` is injective. -/
theorem sumMap_castSucc_id_injective {n r : ℕ} :
    Function.Injective (Sum.map Fin.castSucc id : Fin n ⊕ Fin r → Fin (n + 1) ⊕ Fin r) :=
  (Sum.map_injective).2 ⟨Fin.castSucc_injective n, Function.injective_id⟩

/-- Evaluation of a renamed multivariate polynomial: `eval g` after `rename f` is `eval` along
the reindexed evaluation `g ∘ f`. -/
lemma eval_rename_of_ravel_id {σ τ : Type*} {R : Type*} [CommSemiring R] (f : σ → τ) (g : τ → R)
    (p : MvPolynomial σ R) :
    MvPolynomial.eval g (MvPolynomial.rename f p) = MvPolynomial.eval (g ∘ f) p := by
  induction p using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p X' hp => simp [hp]

/-- `pderiv` of a renamed polynomial vanishes at a variable that is not in the image of the
reindexing. -/
lemma pderiv_rename_eq_zero_of_forall_ne {σ τ : Type*} {R : Type*} [CommSemiring R]
    (f : σ → τ) (k : τ) (hk : ∀ x, f x ≠ k) (p : MvPolynomial σ R) :
    MvPolynomial.pderiv k (MvPolynomial.rename f p) = 0 := by
  rw [MvPolynomial.pderiv_eq_zero_of_notMem_vars]
  intro hmem
  obtain ⟨i, -, hi⟩ := MvPolynomial.mem_vars_rename f p hmem
  exact hk i hi

theorem ravel_embedP {n r : ℕ} (S : ESys n r) (P : EPoly n r) :
    (∀ z : Fin (n + 1) → ℝ, (S.ravel).ev (embedP P) z = S.ev P (Fin.init z)) ∧
    (∀ j : Fin n, (S.ravel).d (Fin.castSucc j) (embedP P) = embedP (S.d j P)) ∧
    ((S.ravel).d (Fin.last n) (embedP P) = 0) ∧
    ((embedP P).totalDegree ≤ P.totalDegree) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- Evaluation: the new coordinate is ignored.
    intro z
    have hcomp : (Sum.elim z fun j => (S.ravel).psi j z) ∘ (Sum.map Fin.castSucc id)
        = Sum.elim (Fin.init z) fun j => S.psi j (Fin.init z) := by
      funext x
      cases x with
      | inl i => simp [Fin.init]
      | inr j => simp [ESys.ravel_psi]
    simp only [ESys.ev, embedP, eval_rename_of_ravel_id, hcomp]
  · -- The old directions: `pderiv` commutes with `embedP`, and the coefficients agree.
    intro j
    have hf := sumMap_castSucc_id_injective (n := n) (r := r)
    have h1 : ∀ i : Fin n, MvPolynomial.pderiv (Sum.inl (Fin.castSucc i)) (embedP P)
        = embedP (MvPolynomial.pderiv (Sum.inl i) P) :=
      fun i => MvPolynomial.pderiv_rename hf (Sum.inl i) P
    have h2 : ∀ j : Fin r, MvPolynomial.pderiv (Sum.inr j) (embedP P)
        = embedP (MvPolynomial.pderiv (Sum.inr j) P) :=
      fun j => MvPolynomial.pderiv_rename hf (Sum.inr j) P
    simp only [ESys.d]
    rw [h1 j]
    simp only [h2, ESys.ravel_a_castSucc]
    simp only [embedP, map_add, map_sum, map_mul, MvPolynomial.rename_C, MvPolynomial.rename_X,
      Sum.map_inr, id_eq]
  · -- The new direction: no variable of `embedP P` is indexed by `Sum.inl (Fin.last n)`, and
    -- the coefficient of the chain in the new direction is zero.
    have h0 : MvPolynomial.pderiv (Sum.inl (Fin.last n)) (embedP P) = 0 := by
      rw [embedP]
      refine pderiv_rename_eq_zero_of_forall_ne _ _ (fun x => ?_) P
      cases x with
      | inl a => exact fun h => (Fin.castSucc_lt_last a).ne (Sum.inl_injective h)
      | inr b => exact fun h => by cases h
    simp only [ESys.d, h0, ESys.ravel_a_last, MvPolynomial.C_0, zero_mul,
      Finset.sum_const_zero, add_zero]
  · -- Total degree: renaming never raises it.
    exact MvPolynomial.totalDegree_rename_le _ P

end Work.WilE2
