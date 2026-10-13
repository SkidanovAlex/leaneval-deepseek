/-
  Area C0: the bridge between the general form `RExpExistI` (arbitrary index type of the ambient
  variables, arbitrary finite witness type) and the frozen `WilkiesDesign.RExpExist` for
  `Fin n`-indexed ambient variables and `Fin m` witnesses.
-/
import Submission.Work.WilC0.Basic

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1000000
noncomputable section
open Classical
open FirstOrder FirstOrder.Language
open scoped FirstOrder

namespace Work.WilC0

open WilkiesDesign (rexp rexpPolyEval RExpExist)

theorem rexpPolyEval_eq {N : ℕ} (P : MvPolynomial (Fin N ⊕ Fin N) ℝ) (z : Fin N → ℝ) :
    rexpPolyEval P z = rexpEval z P := rfl

/-- `Fin.append x y` is `Sum.elim x y` after the standard identification of `Fin n ⊕ Fin m` with
`Fin (n + m)`. -/
theorem append_comp_finSumFinEquiv {n m : ℕ} (x : Fin n → ℝ) (y : Fin m → ℝ) :
    Fin.append x y ∘ ⇑(finSumFinEquiv (m := n) (n := m)) = Sum.elim x y := by
  funext q
  rcases q with i | j <;> simp [finSumFinEquiv_apply_left, finSumFinEquiv_apply_right]

/-- The converse form, which is the one used to compare `RExpExistI` with `RExpExist`. -/
theorem sumElim_comp_finSumFinEquiv_symm {n m : ℕ} (x : Fin n → ℝ) (y : Fin m → ℝ) :
    (Sum.elim x y) ∘ ⇑(finSumFinEquiv (m := n) (n := m)).symm = Fin.append x y := by
  funext q
  obtain ⟨q', rfl⟩ := (finSumFinEquiv (m := n) (n := m)).surjective q
  rcases q' with i | j <;> simp [finSumFinEquiv_apply_left, finSumFinEquiv_apply_right]

/-- **The bridge.** On `Fin n`-indexed ambient variables, `RExpExistI` agrees with the frozen
`RExpExist`. -/
theorem rexExistI_iff_rexExist {n : ℕ} (X : Set (Fin n → ℝ)) :
    RExpExistI X ↔ RExpExist X := by
  constructor
  · rintro ⟨μ, hμ, P, rfl⟩
    letI := hμ
    let e : μ ≃ Fin (Fintype.card μ) := Fintype.equivFin μ
    let F : Fin n ⊕ μ → Fin n ⊕ Fin (Fintype.card μ) := Sum.map id ⇑e
    let G : Fin n ⊕ Fin (Fintype.card μ) → Fin (n + Fintype.card μ) :=
      finSumFinEquiv (m := n) (n := Fintype.card μ)
    refine ⟨Fintype.card μ,
      MvPolynomial.rename (Sum.map G G) (MvPolynomial.rename (Sum.map F F) P), ?_⟩
    have key : ∀ (x : Fin n → ℝ) (y : Fin (Fintype.card μ) → ℝ),
        rexpEval (Fin.append x y) (MvPolynomial.rename (Sum.map G G)
            (MvPolynomial.rename (Sum.map F F) P))
          = rexpEval (Sum.elim x (y ∘ ⇑e)) P := by
      intro x y
      rw [rexpEval_rename G (Fin.append x y) (MvPolynomial.rename (Sum.map F F) P),
        append_comp_finSumFinEquiv,
        rexpEval_rename F (Sum.elim x y) P, sumElim_comp_map_id]
    ext x
    constructor
    · rintro ⟨y, hy⟩
      refine ⟨y ∘ ⇑e.symm, ?_⟩
      rw [rexpPolyEval_eq, key]
      have hcomp : (y ∘ ⇑e.symm) ∘ ⇑e = y := by
        funext j
        simp
      rw [hcomp]
      exact hy
    · rintro ⟨y, hy⟩
      refine ⟨y ∘ ⇑e, ?_⟩
      rw [← key, ← rexpPolyEval_eq]
      exact hy
  · rintro ⟨m, Q, rfl⟩
    let G : Fin (n + m) → Fin n ⊕ Fin m := ⇑(finSumFinEquiv (m := n) (n := m)).symm
    refine ⟨Fin m, inferInstance, MvPolynomial.rename (Sum.map G G) Q, ?_⟩
    have key : ∀ (x : Fin n → ℝ) (y : Fin m → ℝ),
        rexpEval (Sum.elim x y) (MvPolynomial.rename (Sum.map G G) Q)
          = rexpEval (Fin.append x y) Q := by
      intro x y
      rw [rexpEval_rename G (Sum.elim x y) Q, sumElim_comp_finSumFinEquiv_symm]
    ext x
    constructor
    · rintro ⟨y, hy⟩
      exact ⟨y, by rw [key, ← rexpPolyEval_eq]; exact hy⟩
    · rintro ⟨y, hy⟩
      refine ⟨y, ?_⟩
      rw [key, ← rexpPolyEval_eq] at hy
      exact hy

end Work.WilC0
