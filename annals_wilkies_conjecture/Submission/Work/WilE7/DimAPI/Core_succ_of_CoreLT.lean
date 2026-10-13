import Mathlib
import Submission.Work.WilE7.MainDesignDefs

set_option autoImplicit false
noncomputable section
open Classical

namespace Work.WilE7.DimAPI

/-! ## Compressing a three-variable degree bound to two variables

`CoreLT n (n+1)` bounds the cell count by `MvPolynomial.eval ![D, k, l] b` with
`b : MvPolynomial (Fin 3) ℕ`, while `Core (n+1)` needs a bound of the form
`MvPolynomial.eval ![D, k] b'` with `b' : MvPolynomial (Fin 2) ℕ`.  We use the
instance `l = 0` of the `CoreLT` bound and compress `b` by the substitution
`X 0 ↦ X 0`, `X 1 ↦ X 1`, `X 2 ↦ 0`. -/

/-- Substitute `0` for the third variable of a polynomial in three variables,
producing a polynomial in two variables. -/
noncomputable def snd0 {R : Type*} [CommSemiring R] (b : MvPolynomial (Fin 3) R) :
    MvPolynomial (Fin 2) R :=
  MvPolynomial.eval₂Hom MvPolynomial.C
    ![MvPolynomial.X 0, MvPolynomial.X 1, (0 : MvPolynomial (Fin 2) R)] b

/-- Evaluating `snd0 b` at `(D, k)` is the same as evaluating `b` at `(D, k, 0)`. -/
theorem eval_snd0 {R : Type*} [CommSemiring R] (b : MvPolynomial (Fin 3) R) (D k : R) :
    MvPolynomial.eval ![D, k] (snd0 b) = MvPolynomial.eval ![D, k, 0] b := by
  have h := MvPolynomial.map_eval₂Hom (MvPolynomial.C : R →+* MvPolynomial (Fin 2) R)
    ![MvPolynomial.X 0, MvPolynomial.X 1, (0 : MvPolynomial (Fin 2) R)]
    (MvPolynomial.eval ![D, k]) b
  have hC : (MvPolynomial.eval ![D, k]).comp (MvPolynomial.C : R →+* MvPolynomial (Fin 2) R) =
      RingHom.id R := by
    ext r; simp
  have hg : (fun i => (MvPolynomial.eval ![D, k])
        (![MvPolynomial.X 0, MvPolynomial.X 1, (0 : MvPolynomial (Fin 2) R)] i)) = ![D, k, 0] := by
    funext i; fin_cases i <;> simp
  simp only [snd0]
  rw [h, hC, hg]
  rfl

/-! ## The level step -/

/-- **The level step of the BV lexicographic induction.**  `CoreLT n (n+1)` is the
induction statement at the level above, with the trivial measure `K = n+1` (which is
automatic in `ℝ^n` by `nullDimLT_top`); forgetting the auxiliary base family `Y`
(instance `l = 0`) and compressing the degree bound gives `Core (n+1)`. -/
theorem Core_succ_of_CoreLT {n : ℕ} (h : Work.WilE7.MainDesign.CoreLT n (n + 1)) :
    Work.WilE7.Core (n + 1) := by
  intro F
  obtain ⟨a, b, c, hb⟩ := h F
  refine ⟨a, snd0 b, c, ?_⟩
  intro D k m X hX
  obtain ⟨C, hcyl, hcompatX, _hcompatY, hcard, hcell⟩ :=
    hb D k 0 m 0 X (fun i => i.elim0) hX (fun i => i.elim0)
      (fun i => MainDesign.nullDimLT_top _)
  exact ⟨C, hcyl, hcompatX, by rw [eval_snd0 b D k]; exact hcard, hcell⟩

end Work.WilE7.DimAPI
