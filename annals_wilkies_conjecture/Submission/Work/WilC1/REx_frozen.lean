/-
  WilC1 — a self-contained dictionary between `REx` and the frozen `WilkiesDesign.RExpExist`.

  `REx (Fin n) X` uses an arbitrary finite witness type `γ`; the frozen `RExpExist X` uses the
  concrete witnesses `Fin m` and writes the coordinates as `Fin.append`.  This file proves the
  equivalence directly from the vocabulary of `Work.WilC1.Defs`, so that
  `Submission/Work/WilC1/Main.lean` depends only on files inside this directory.
-/
import Submission.Work.WilC1.Defs

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Classical FirstOrder FirstOrder.Language
namespace Work.WilC1

open WilkiesDesign WilkiesConjecture

/-- `rexpEval` and the frozen `rexpPolyEval` are the same evaluation. -/
theorem rexpEval_eq_rexpPolyEval {N : ℕ} (P : MvPolynomial (Fin N ⊕ Fin N) ℝ)
    (z : Fin N → ℝ) : rexpEval z P = rexpPolyEval P z := rfl

/-- `Fin.append` composed with `finSumFinEquiv` is `Sum.elim`. -/
theorem append_finSumFinEquiv {n m : ℕ} (x : Fin n → ℝ) (y : Fin m → ℝ) :
    Fin.append x y ∘ ⇑(finSumFinEquiv (m := n) (n := m)) = Sum.elim x y := by
  funext q
  rcases q with i | j
  · rw [Function.comp_apply, finSumFinEquiv_apply_left, Fin.append_left, Sum.elim_inl]
  · rw [Function.comp_apply, finSumFinEquiv_apply_right, Fin.append_right, Sum.elim_inr]

/-- `Sum.elim` composed with the inverse of `finSumFinEquiv` is `Fin.append`. -/
theorem elim_comp_finSumFinEquiv_symm {n m : ℕ} (x : Fin n → ℝ) (y : Fin m → ℝ) :
    (Sum.elim x y) ∘ ⇑(finSumFinEquiv (m := n) (n := m)).symm = Fin.append x y := by
  funext q
  have h := congrFun (append_finSumFinEquiv (x := x) (y := y))
    (⇑(finSumFinEquiv (m := n) (n := m)).symm q)
  simp only [Function.comp_apply, Equiv.apply_symm_apply] at h
  exact h.symm

/-- `Fin.append` composed with the reindexing `Fin n ⊕ γ → Fin (n+m)` induced by `e : γ ≃ Fin m`
is `Sum.elim` of the coordinates and of the witnesses pulled back along `e`. -/
theorem append_comp_sumMap {n m : ℕ} {γ : Type} (e : γ ≃ Fin m) (x : Fin n → ℝ)
    (z : Fin m → ℝ) :
    (Fin.append x z) ∘
        (fun q : Fin n ⊕ γ => finSumFinEquiv (Sum.map id (⇑e) q)) = Sum.elim x (z ∘ ⇑e) := by
  funext q
  rcases q with i | j
  · simp only [Function.comp_apply, Sum.map_inl, Sum.elim_inl, finSumFinEquiv_apply_left,
      Fin.append_left, id_eq]
  · simp only [Function.comp_apply, Sum.map_inr, Sum.elim_inr, finSumFinEquiv_apply_right,
      Fin.append_right]

/-- The evaluation identity expressing the witnesses `Fin m` in terms of the witnesses `γ`. -/
theorem rexpEval_append_rename {n m : ℕ} {γ : Type} (e : γ ≃ Fin m)
    (P : MvPolynomial ((Fin n ⊕ γ) ⊕ (Fin n ⊕ γ)) ℝ) (x : Fin n → ℝ) (z : Fin m → ℝ) :
    rexpEval (Fin.append x z)
        (MvPolynomial.rename
          (polyMap (fun q : Fin n ⊕ γ => finSumFinEquiv (Sum.map id (⇑e) q))) P)
      = rexpEval (Sum.elim x (z ∘ ⇑e)) P := by
  rw [rexpEval_rename, append_comp_sumMap]

/-- The evaluation identity in the converse direction. -/
theorem rexpEval_rename_finSumFinEquiv_symm {n m : ℕ}
    (P : MvPolynomial (Fin (n + m) ⊕ Fin (n + m)) ℝ) (x : Fin n → ℝ) (y : Fin m → ℝ) :
    rexpEval (Sum.elim x y)
        (MvPolynomial.rename (polyMap ⇑(finSumFinEquiv (m := n) (n := m)).symm) P)
      = rexpEval (Fin.append x y) P := by
  rw [rexpEval_rename, elim_comp_finSumFinEquiv_symm]

/-- `REx` and the frozen `RExpExist` agree on `Fin n`-indexed sets. -/
theorem REx_iff_RExpExist_self {n : ℕ} (X : Set (Fin n → ℝ)) :
    REx (Fin n) X ↔ RExpExist X := by
  constructor
  · rintro ⟨γ, hγ, P, hP⟩
    letI : Fintype γ := hγ
    let e : γ ≃ Fin (Fintype.card γ) := Fintype.equivFin γ
    refine ⟨Fintype.card γ,
      MvPolynomial.rename
        (polyMap (fun q : Fin n ⊕ γ => finSumFinEquiv (Sum.map id (⇑e) q))) P, ?_⟩
    rw [hP]
    ext x
    constructor
    · rintro ⟨y, hy⟩
      refine ⟨y ∘ ⇑e.symm, ?_⟩
      rw [← rexpEval_eq_rexpPolyEval]
      have hcomp : (y ∘ ⇑e.symm) ∘ ⇑e = y := by funext j; simp
      rw [rexpEval_append_rename (e := e), hcomp]
      exact hy
    · rintro ⟨z, hz⟩
      refine ⟨z ∘ ⇑e, ?_⟩
      rw [← rexpEval_eq_rexpPolyEval, rexpEval_append_rename (e := e)] at hz
      exact hz
  · rintro ⟨m, P, hP⟩
    refine ⟨Fin m, inferInstance,
      MvPolynomial.rename (polyMap ⇑(finSumFinEquiv (m := n) (n := m)).symm) P, ?_⟩
    rw [hP]
    ext x
    constructor
    · rintro ⟨y, hy⟩
      refine ⟨y, ?_⟩
      rw [rexpEval_rename_finSumFinEquiv_symm]
      rwa [← rexpEval_eq_rexpPolyEval] at hy
    · rintro ⟨y, hy⟩
      refine ⟨y, ?_⟩
      rw [rexpEval_rename_finSumFinEquiv_symm, rexpEval_eq_rexpPolyEval] at hy
      exact hy

end Work.WilC1
