/-
  WilE10 / RexpSub — the forward direction of `E10_rexp_to_subpf`.

  Given an rexp-polynomial `P` in `N = n + m` variables and a solution `z = Fin.append x y` of
  `rexpPolyEval P z = 0`, the explicitly constructed point `mkPt n m x ε z` (with `ε` the branch
  pattern `ε i = (|z i| ≤ 1)`) lies in the semi-Pfaffian set `W n m P`.

  The three ingredients are delegated:
  * `mkPt_mem_cube`          — the point lies in the closed cube;
  * `eqs_of_eqsOf_eq_zero`   — the tag/relation equations vanish at the point;
  * `pos_of_posOf_pos`       — the strict inequalities hold at the point.
  This file supplies the branch-equation (`branchPoly`) evaluation and the assembly.
-/
import Mathlib
import Submission.Work.WilE10.RexpSubDefs
import Submission.Work.WilE10.BranchEval.branchPoly_eval
import Submission.Work.WilE10.RexpSub.mkPt_mem_cube
import Submission.Work.WilE10.RexpSub.eqs_of_eqsOf_eq_zero
import Submission.Work.WilE10.RexpSub.pos_of_posOf_pos

set_option autoImplicit false
noncomputable section
open Classical

namespace Work.WilE10.RexpSub

open WilkiesDesign WilkiesDesign.E

/-- The branch-polynomial equation vanishing at `mkPt`, for an arbitrary branch pattern `ε`
satisfying `ε i = true ↔ |z i| ≤ 1`.  This is `branchPoly_eval`: the product of the reciprocal
weights times `rexpPolyEval P z`, which is zero by hypothesis. -/
lemma branchPoly_eaEval_zero (n m : ℕ) (P : MvPolynomial (Fin (n + m) ⊕ Fin (n + m)) ℝ)
    (x : Fin n → ℝ) (ε : Fin (n + m) → Bool) (z : Fin (n + m) → ℝ)
    (hε : ∀ i, ε i = true ↔ |z i| ≤ 1)
    (hP : WilkiesDesign.rexpPolyEval P z = 0) :
    eaEval (chain n m) (branchPoly (degb P) ε (ut n m) (us n m) id P) (mkPt n m x ε z) = 0 := by
  rw [eaEval]
  simp only [ell_chain]
  rw [BranchEval.branchPoly_eval (degb P) ε (ut n m) (us n m) id P
        z (fun i => (z i)⁻¹)
        (fun j => Real.exp (mkPt n m x ε z (ut n m j)))
        (mkPt n m x ε z)]
  · rw [show MvPolynomial.eval (Sum.elim z (fun i => WilkiesDesign.rexp (z i))) P = 0 from hP]
    ring
  · intro i h; rw [mkPt_ut, ite_eq_left h]
  · intro i h; simp only [id_eq]; rw [mkPt_ut, ite_eq_left h]
  · intro i h; exact (hε i).mp h
  · intro i h; rw [mkPt_us, ite_eq_right (by simp [h])]
  · intro i h
    have h1 : 1 < |z i| := by
      have h2 : ¬ (|z i| ≤ 1) := by
        intro hc
        have hne : ¬ (ε i = true) := by rw [h]; exact Bool.false_ne_true
        exact hne ((hε i).mpr hc)
      simpa using h2
    exact inv_mul_cancel₀ (fun hz => by rw [hz, abs_zero] at h1; norm_num at h1)
  · intro i h
    have h2 : ¬ (|z i| ≤ 1) := by
      intro hc
      have hne : ¬ (ε i = true) := by rw [h]; exact Bool.false_ne_true
      exact hne ((hε i).mpr hc)
    simpa using h2
  · intro i mm hm; exact le_degb P hm i

/-- All the equations of `eqsOf n m P ε` vanish at `mkPt`: the head is `branchPoly` and the tail
is the delegated `eqs_of_eqsOf_eq_zero`. -/
lemma eqsOf_eval_zero (n m : ℕ) (P : MvPolynomial (Fin (n + m) ⊕ Fin (n + m)) ℝ)
    (x : Fin n → ℝ) (ε : Fin (n + m) → Bool) (z : Fin (n + m) → ℝ)
    (hzx : ∀ i : Fin n, z (Fin.castAdd m i) = x i)
    (hε : ∀ i, ε i = true ↔ |z i| ≤ 1)
    (hP : WilkiesDesign.rexpPolyEval P z = 0) :
    ∀ f ∈ eqsOf n m P ε, eaEval (chain n m) f (mkPt n m x ε z) = 0 := by
  intro f hf
  simp only [eqsOf] at hf
  rw [List.mem_cons] at hf
  rcases hf with rfl | hf
  · exact branchPoly_eaEval_zero n m P x ε z hε hP
  · exact eqs_of_eqsOf_eq_zero n m x ε z hzx hε f hf

/-- The basic set `basicOf n m P ε` holds at `mkPt`. -/
lemma basicOf_holds (n m : ℕ) (P : MvPolynomial (Fin (n + m) ⊕ Fin (n + m)) ℝ)
    (x : Fin n → ℝ) (ε : Fin (n + m) → Bool) (z : Fin (n + m) → ℝ)
    (hzx : ∀ i : Fin n, z (Fin.castAdd m i) = x i)
    (hε : ∀ i, ε i = true ↔ |z i| ≤ 1)
    (hP : WilkiesDesign.rexpPolyEval P z = 0) :
    Basic.holds (chain n m) (basicOf n m P ε) (mkPt n m x ε z) := by
  simp only [Basic.holds, basicOf]
  exact ⟨eqsOf_eval_zero n m P x ε z hzx hε hP, pos_of_posOf_pos n m x ε z hzx hε⟩

theorem mkPt_mem_W (n m : ℕ) (P : MvPolynomial (Fin (n + m) ⊕ Fin (n + m)) ℝ) (x : Fin n → ℝ)
    (y : Fin m → ℝ) (hP : WilkiesDesign.rexpPolyEval P (Fin.append x y) = 0) :
    Work.WilE10.mkPt n m x (fun i => decide (|Fin.append x y i| ≤ 1)) (Fin.append x y)
      ∈ (Work.WilE10.W n m P).set := by
  have hzx : ∀ i : Fin n, (Fin.append x y) (Fin.castAdd m i) = x i :=
    fun i => Fin.append_left x y i
  have hε : ∀ i : Fin (n + m), (fun i => decide (|Fin.append x y i| ≤ 1)) i = true ↔
      |Fin.append x y i| ≤ 1 := fun i => Iff.of_eq decide_eq_true_eq
  have hlt := basicOf_holds n m P x (fun i => decide (|Fin.append x y i| ≤ 1)) (Fin.append x y)
    hzx hε hP
  rw [SemiPf.set]
  exact ⟨mkPt_mem_cube n m x (fun i => decide (|Fin.append x y i| ≤ 1)) (Fin.append x y) hzx hε,
    basicOf n m P (fun i => decide (|Fin.append x y i| ≤ 1)), mem_W_basics n m P _, hlt⟩

end Work.WilE10.RexpSub
