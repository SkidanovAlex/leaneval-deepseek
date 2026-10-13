import Mathlib
import Submission.Work.Wilkies.E.Spec
import Submission.Work.WilE5.Basic
import Submission.Work.WilE7.Auxiliary.fibreFDeriv

namespace Work.WilE7.Auxiliary

/-! ## Auxiliary: reading `projFirst`/`projSnd` off a `Fin.append` -/

lemma projFirst_append (p q : ℕ) (u : Fin p → ℝ) (y : Fin q → ℝ) :
    WilkiesDesign.E.projFirst p q (Fin.append u y) = u := by
  funext i
  simp [WilkiesDesign.E.projFirst, Fin.append_left]

lemma projSnd_append (p q : ℕ) (u : Fin p → ℝ) (y : Fin q → ℝ) :
    WilkiesDesign.E.projSnd p q (Fin.append u y) = y := by
  funext i
  simp [WilkiesDesign.E.projSnd, Fin.append_right]

/-! ## The derivative of the fibre map, at an arbitrary base point

`fibreFDeriv` computes the derivative of `y ↦ fun a => eaEval c (h a) (Fin.append u y)` at the
base point `projSnd p q z` of the *fixed* point `z`.  Since that statement is about an arbitrary
`z`, feeding it `z := Fin.append u y` (whence `projFirst p q z = u`, `projSnd p q z = y`) gives
the derivative at every base point `y`. -/

lemma fderiv_fibre_eq {p q j r : ℕ} (c : WilkiesDesign.E.EAChain (p + q) r)
    (h : Fin j → WilkiesDesign.E.EAPoly (p + q) r) (u : Fin p → ℝ) (y : Fin q → ℝ) :
    fderiv ℝ (fun y' : Fin q → ℝ => fun a : Fin j =>
        WilkiesDesign.E.eaEval c (h a) (Fin.append u y')) y
      = ContinuousLinearMap.pi (fun a : Fin j => (∑ l : Fin q,
          WilkiesDesign.E.eaEval c (WilkiesDesign.E.eaD c (Work.WilE5.yDir p l) (h a))
            (Fin.append u y) • (ContinuousLinearMap.proj l : (Fin q → ℝ) →L[ℝ] ℝ))) := by
  have key := Work.WilE7.Aux.fibreFDeriv (p := p) (q := q) c h (Fin.append u y)
  rw [projFirst_append p q u y, projSnd_append p q u y] at key
  exact key

/-- Evaluation of the fibre derivative: the linear map `(fderiv …) v` is the `j`-tuple whose
`a`-th entry is the dot product of `v` with the `a`-th row of the coefficient matrix. -/
lemma fderiv_fibre_apply {p q j r : ℕ} (c : WilkiesDesign.E.EAChain (p + q) r)
    (h : Fin j → WilkiesDesign.E.EAPoly (p + q) r) (u : Fin p → ℝ) (y : Fin q → ℝ)
    (v : Fin q → ℝ) :
    (fderiv ℝ (fun y' : Fin q → ℝ => fun a : Fin j =>
        WilkiesDesign.E.eaEval c (h a) (Fin.append u y')) y) v
      = fun a : Fin j => ∑ l : Fin q,
          WilkiesDesign.E.eaEval c (WilkiesDesign.E.eaD c (Work.WilE5.yDir p l) (h a))
            (Fin.append u y) * v l := by
  rw [fderiv_fibre_eq]
  funext a
  rw [ContinuousLinearMap.pi_apply]
  simp [ContinuousLinearMap.proj_apply]

theorem fibreCritCond {p q : ℕ} {j j' r r' : ℕ} (c : WilkiesDesign.E.EAChain (p + q) r)
    (c' : WilkiesDesign.E.EAChain (p + q) r') (h : Fin j → WilkiesDesign.E.EAPoly (p + q) r)
    (h' : Fin j' → WilkiesDesign.E.EAPoly (p + q) r') (l : Fin q) (z : Fin (p + q) → ℝ)
    (hrank_ev : ∀ᶠ y in nhds (WilkiesDesign.E.projSnd p q z),
      (∀ a, WilkiesDesign.E.eaEval c (h a) (Fin.append (WilkiesDesign.E.projFirst p q z) y) = 0) →
      (Matrix.of fun (a : Fin j) (l' : Fin q) =>
        WilkiesDesign.E.eaEval c (WilkiesDesign.E.eaD c (Work.WilE5.yDir p l') (h a))
          (Fin.append (WilkiesDesign.E.projFirst p q z) y)).rank = j)
    (hcrit : ∀ᶠ y in nhds (WilkiesDesign.E.projSnd p q z),
      (∀ a, WilkiesDesign.E.eaEval c (h a) (Fin.append (WilkiesDesign.E.projFirst p q z) y) = 0) →
      (∀ v : Fin q → ℝ,
        (∀ a, ∑ l', WilkiesDesign.E.eaEval c (WilkiesDesign.E.eaD c (Work.WilE5.yDir p l') (h a))
          (Fin.append (WilkiesDesign.E.projFirst p q z) y) * v l' = 0) → v l = 0)) :
    ∀ᶠ y in nhds (WilkiesDesign.E.projSnd p q z),
      (∀ a, WilkiesDesign.E.eaEval c (h a) (Fin.append (WilkiesDesign.E.projFirst p q z) y) = 0) →
      ∀ v : Fin q → ℝ,
        (fderiv ℝ (fun y' : Fin q → ℝ => fun a : Fin j =>
          WilkiesDesign.E.eaEval c (h a) (Fin.append (WilkiesDesign.E.projFirst p q z) y')) y) v = 0 →
        (fderiv ℝ (fun y' : Fin q → ℝ => y' l) y) v = 0 := by
  -- The critical condition transfers verbatim once the derivative is written out in
  -- coordinates: `(fderiv …) v = 0` is exactly the system `∑_l C a l * v l = 0`.
  filter_upwards [hcrit] with y hy hyQ v hv
  rw [fderiv_fibre_apply (p := p) (q := q) (j := j) (r := r) c h
    (WilkiesDesign.E.projFirst p q z) y v] at hv
  have hv' : ∀ a, ∑ l', WilkiesDesign.E.eaEval c
      (WilkiesDesign.E.eaD c (Work.WilE5.yDir p l') (h a))
      (Fin.append (WilkiesDesign.E.projFirst p q z) y) * v l' = 0 := by
    intro a
    have := congrFun hv a
    simpa using this
  have hvl : v l = 0 := hy hyQ v hv'
  rw [(hasFDerivAt_apply l y).fderiv, ContinuousLinearMap.proj_apply, hvl]

end Work.WilE7.Auxiliary
