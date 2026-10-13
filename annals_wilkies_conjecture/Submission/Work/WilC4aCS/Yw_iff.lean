import Mathlib
import Submission.Work.WilC4aCS.Defs

set_option autoImplicit false
noncomputable section

namespace Work.WilC4aCS

open WilkiesDesign WilkiesDesign.E

/-- The single `Basic` atom family that defines `SAcoef`: the equation `Qpoly d 0 = 0`
together with the inequalities `τ j · Qpoly d (j+1) > 0`. -/
def SAcoefBasic {l : ℕ} (d : Fin (l + 1) → ℕ) (τ : Fin l → ℝ) : E.Basic (∑ i, d i + 1) 0 :=
  ⟨[Qpoly d 0], List.ofFn (fun j : Fin l => MvPolynomial.C (τ j) * Qpoly d (Fin.succ j))⟩

lemma SAcoef_eq (l : ℕ) (d : Fin (l + 1) → ℕ) (τ : Fin l → ℝ) :
    SAcoef l d τ = (⟨[SAcoefBasic d τ]⟩ : E.SA (∑ i, d i + 1)) := rfl

/-- `ev0` is `eaEval` over the empty exp-affine chain. -/
lemma eaEval_nil_eq_ev0 {D : ℕ} (p : EAPoly D 0) (v : Fin D → ℝ) :
    E.eaEval (EAChain.nil D) p v = ev0 v p := by
  have h : (Sum.elim v (fun j : Fin 0 => Real.exp ((EAChain.nil D).ell j v)))
      = (Sum.elim v (fun _ : Fin 0 => (0 : ℝ))) := by
    funext s
    rcases s with i | j
    · rfl
    · exact j.elim0
  unfold E.eaEval ev0
  simp only [h]

/-- Pulling a scalar factor `MvPolynomial.C c` out of `ev0`. -/
lemma ev0_mul_C {D : ℕ} (c : ℝ) (p : EAPoly D 0) (v : Fin D → ℝ) :
    ev0 v (MvPolynomial.C c * p) = c * ev0 v p := by
  simp only [ev0, MvPolynomial.eval_mul, MvPolynomial.eval_C]

/-- Evaluating the semialgebraic atom `Qpoly d i` at the point `Fin.snoc A z`
(coefficient vector `A` followed by the last coordinate `z`) gives `Qeval d A z i`. -/
lemma eval_Qpoly {K : ℕ} (d : Fin K → ℕ) (A : Fin (∑ i, d i) → ℝ) (z : ℝ) (i : Fin K) :
    ev0 (Fin.snoc A z) (Qpoly d i) = Qeval d A z i := by
  unfold ev0 Qpoly Qeval zIdx cIdx coefIdx
  simp only [MvPolynomial.eval_add, MvPolynomial.eval_mul, MvPolynomial.eval_pow,
    MvPolynomial.eval_X, MvPolynomial.eval_sum, Sum.elim_inl]; simp

/-- Membership in the semialgebraic set `SAcoef` in terms of the monic polynomials `Qeval`. -/
lemma SAcoef_mem {l : ℕ} (d : Fin (l + 1) → ℕ) (τ : Fin l → ℝ) (v : Fin (∑ i, d i + 1) → ℝ) :
    v ∈ (SAcoef l d τ).set ↔
      ev0 v (Qpoly d 0) = 0 ∧ ∀ j : Fin l, 0 < τ j * ev0 v (Qpoly d (Fin.succ j)) := by
  have hset : v ∈ (SAcoef l d τ).set ↔
      (SAcoefBasic d τ).holds (EAChain.nil (∑ i, d i + 1)) v := by
    rw [SAcoef_eq]
    simp only [E.SA.set]
    change (∃ B, B ∈ [SAcoefBasic d τ] ∧ B.holds (EAChain.nil (∑ i, d i + 1)) v) ↔
      (SAcoefBasic d τ).holds (EAChain.nil (∑ i, d i + 1)) v
    constructor
    · rintro ⟨B, hB, hh⟩
      rw [List.mem_singleton] at hB
      rw [hB] at hh
      exact hh
    · intro hh
      exact ⟨_, List.mem_singleton.mpr rfl, hh⟩
  rw [hset]
  constructor
  · intro hh
    refine ⟨?_, fun j => ?_⟩
    · have h1 := hh.1 (Qpoly d 0) (by simp [SAcoefBasic])
      rw [eaEval_nil_eq_ev0] at h1
      exact h1
    · have h2 := hh.2 (MvPolynomial.C (τ j) * Qpoly d (Fin.succ j)) (by simp [SAcoefBasic])
      rw [eaEval_nil_eq_ev0, ev0_mul_C] at h2
      exact h2
  · intro hh
    refine ⟨?_, ?_⟩
    · intro f hf
      simp only [SAcoefBasic, List.mem_singleton] at hf
      subst hf
      rw [eaEval_nil_eq_ev0]
      exact hh.1
    · intro g hg
      simp only [SAcoefBasic] at hg
      obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hg
      rw [eaEval_nil_eq_ev0, ev0_mul_C]
      exact hh.2 j

/-- Membership in `Yw` is exactly the system of sign conditions on the Weierstrass
polynomials `Qeval d (coefFun d a (Fin.init y)) (y (Fin.last n)) ·`. -/
theorem Yw_iff {n l : ℕ} (d : Fin (l + 1) → ℕ)
    (a : ∀ i, Fin (d i) → (Fin n → ℝ) → ℝ) (τ : Fin l → ℝ) (y : Fin (n + 1) → ℝ) :
    y ∈ Work.WilC4aCS.Yw d a τ ↔
      Work.WilC4aCS.Qeval d (Work.WilC4aCS.coefFun d a (Fin.init y)) (y (Fin.last n)) 0 = 0 ∧
      ∀ j : Fin l, 0 < τ j * Work.WilC4aCS.Qeval d (Work.WilC4aCS.coefFun d a (Fin.init y))
        (y (Fin.last n)) (Fin.succ j) := by
  rw [Yw]
  simp only [Set.mem_ofPred_eq]
  rw [SAcoef_mem]
  constructor
  · rintro ⟨h0, hτ⟩
    refine ⟨?_, fun j => ?_⟩
    · rw [eval_Qpoly] at h0
      exact h0
    · have hj := hτ j
      rw [eval_Qpoly] at hj
      exact hj
  · rintro ⟨h0, hτ⟩
    refine ⟨?_, fun j => ?_⟩
    · rw [← eval_Qpoly] at h0
      exact h0
    · have hj := hτ j
      rw [← eval_Qpoly] at hj
      exact hj

end Work.WilC4aCS
