import Mathlib
import Submission.Work.RB.Defs
import Submission.Work.RB.weight_mapDomain
import Submission.Work.RB.isWeightedHomogeneous_rename
import Submission.Work.RB.isWeightedHomogeneous_killCompl
import Submission.Work.RB.rename_killCompl_sub_mem_span
import Submission.Work.RB.finrank_quot_eq_of_retract

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.RB

open MvPolynomial

set_option linter.unusedVariables false in
/-- If the homogeneous ideal `J` contains the variable `X v`, then `R/J` only involves the
remaining variables: the Hilbert function of `R/J` in `σ` equals that of the corresponding
quotient of `MvPolynomial {x // x ≠ v} ℂ`. -/
theorem hilb_reduce {n : ℕ} {σ : Type*} [Fintype σ] (w : σ → Fin n →₀ ℕ) {v : σ}
    (J : Ideal (MvPolynomial σ ℂ)) (hX : MvPolynomial.X v ∈ J) (hJ : IsWHomog w J)
    (d : Fin n →₀ ℕ) :
    hilb w J d = hilb (fun x : {x : σ // x ≠ v} => w x.1)
      (Ideal.comap (MvPolynomial.rename (Subtype.val)) J) d := by
  classical
  -- `(X v)` is contained in `J`, since `X v ∈ J`.
  have hspan : Ideal.span {MvPolynomial.X v} ≤ J := by
    rw [Ideal.span_le]
    simpa using hX
  -- `ψ = rename Subtype.val` sends `R' = ℂ[x : x ≠ v]` into `R`, `T = killCompl` is its
  -- left inverse (it substitutes `X v = 0`).
  have hψA : ∀ b ∈ homPiece (fun x : {x : σ // x ≠ v} => w x.1) d,
      (MvPolynomial.rename (Subtype.val : {x : σ // x ≠ v} → σ)) b ∈ homPiece w d := by
    intro b hb
    exact isWeightedHomogeneous_rename (M := Fin n →₀ ℕ) w (Subtype.val)
      Subtype.val_injective hb
  have hTB : ∀ a ∈ homPiece w d,
      (MvPolynomial.killCompl (f := Subtype.val)
        (Subtype.val_injective (p := fun x => x ≠ v))) a ∈
        homPiece (fun x : {x : σ // x ≠ v} => w x.1) d := by
    intro a ha
    exact isWeightedHomogeneous_killCompl (M := Fin n →₀ ℕ) w
      (f := (Subtype.val : {x : σ // x ≠ v} → σ))
      (Subtype.val_injective (p := fun x => x ≠ v)) ha
  have key : Module.finrank ℂ (homPiece w d ⧸
        Submodule.comap (homPiece w d).subtype (J.restrictScalars ℂ)) =
      Module.finrank ℂ (homPiece (fun x : {x : σ // x ≠ v} => w x.1) d ⧸
        Submodule.comap (homPiece (fun x : {x : σ // x ≠ v} => w x.1) d).subtype
          ((Ideal.comap (MvPolynomial.rename (Subtype.val)) J).restrictScalars ℂ)) := by
    refine finrank_quot_eq_of_retract
      ((MvPolynomial.rename (Subtype.val : {x : σ // x ≠ v} → σ)).toLinearMap)
      ((MvPolynomial.killCompl (f := Subtype.val)
        (Subtype.val_injective (p := fun x => x ≠ v))).toLinearMap)
      (homPiece w d) (homPiece (fun x : {x : σ // x ≠ v} => w x.1) d)
      (J.restrictScalars ℂ)
      ((Ideal.comap (MvPolynomial.rename (Subtype.val)) J).restrictScalars ℂ)
      hψA hTB ?_ ?_ ?_ ?_
    · -- `ψ` maps the pulled-back ideal into `J`
      intro b hb
      exact hb
    · -- `T` maps `J` into the pulled-back ideal: `ψ (T a) ≡ a (mod X v)` and `X v ∈ J`
      intro a ha
      have h1 : (MvPolynomial.rename (Subtype.val : {x : σ // x ≠ v} → σ)
          (MvPolynomial.killCompl (f := Subtype.val)
            (Subtype.val_injective (p := fun x => x ≠ v)) a) - a) ∈ J :=
        hspan (rename_killCompl_sub_mem_span v a)
      simpa using J.add_mem h1 ha
    · -- `T` is a left inverse of `ψ`
      intro b _
      exact MvPolynomial.killCompl_rename_app (Subtype.val_injective (p := fun x => x ≠ v)) b
    · -- `ψ (T a) ≡ a` modulo `J`
      intro a _
      exact hspan (rename_killCompl_sub_mem_span v a)
  unfold hilb
  exact key

end Work.RB
