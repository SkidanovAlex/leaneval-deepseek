import Mathlib
import Submission.Work.WilE9G.Assembly.Defs
import Submission.Work.WilE7.SubPfAux.unionSet_set

namespace Work.WilE9G.Assembly

open WilkiesDesign WilkiesDesign.E

/-! ## Evaluation lemmas for `eaEval` and `eaD` under the chain concatenation `EAChain.cat`

`ambCat S c₂` keeps `S`'s semi-Pfaffian set but concatenates the chain `c₂` to the right of
`S.X.c`, and lifts every equation `S.h a` with `EAPoly.inl`.  The two facts needed below are

* `Work.WilE7.SubPfAux.eaEval_cat_inl` : evaluating a lifted polynomial in the concatenated
  chain is the same as evaluating it in the original chain (`c₂` is invisible to it);
* `eaEval_eaD_cat_inl` : the same is true after applying the symbolic derivative `eaD`, because
  the directional derivative of a function is a function of the function. -/

/-- The directional derivative of `w ↦ eaEval c Q w` at `x` in the coordinate direction `l` is
the evaluation of the symbolic derivative `eaD c l Q` at `x`. -/
theorem fderiv_eaEval_single {k r : ℕ} (c : EAChain k r) (Q : EAPoly k r)
    (x : Fin k → ℝ) (l : Fin k) :
    (fderiv ℝ (fun w => eaEval c Q w) x) (Pi.single l (1 : ℝ)) = eaEval c (eaD c l Q) x := by
  rw [(Work.WilE5.Calc.hasFDerivAt_eaEval c Q x).fderiv]
  simp only [sum_apply, smul_apply, ContinuousLinearMap.proj_apply]
  rw [Finset.sum_eq_single l]
  · rw [Pi.single_eq_same, smul_eq_mul, mul_one]
  · intro i _ hi; rw [Pi.single_eq_of_ne hi, smul_zero]
  · intro hl; exact absurd (Finset.mem_univ l) hl

/-- Symbolic differentiation commutes with the left inclusion of a chain into a concatenation:
applying `eaD` in the concatenated chain to the lift `EAPoly.inl Q` of a polynomial of `c₁`,
then evaluating, agrees with `eaD` in `c₁`. -/
theorem eaEval_eaD_cat_inl {k r₁ r₂ : ℕ} (c₁ : EAChain k r₁) (c₂ : EAChain k r₂)
    (l : Fin k) (Q : EAPoly k r₁) (x : Fin k → ℝ) :
    eaEval (Work.WilE7.EAChain.cat c₁ c₂)
        (eaD (Work.WilE7.EAChain.cat c₁ c₂) l (Work.WilE7.EAPoly.inl Q)) x
      = eaEval c₁ (eaD c₁ l Q) x := by
  rw [← fderiv_eaEval_single (Work.WilE7.EAChain.cat c₁ c₂) (Work.WilE7.EAPoly.inl Q) x l]
  rw [← fderiv_eaEval_single c₁ Q x l]
  have hfun : (fun w => eaEval (Work.WilE7.EAChain.cat c₁ c₂) (Work.WilE7.EAPoly.inl Q) w)
      = (fun w => eaEval c₁ Q w) :=
    funext (fun w => Work.WilE7.SubPfAux.eaEval_cat_inl c₁ c₂ Q w)
  rw [hfun]

theorem ambCat_eval {N r₂ : ℕ} (S : Work.WilE9G.AmbStratum N)
    (c₂ : WilkiesDesign.E.EAChain N r₂) :
    (∀ (a : Fin S.j) (w : Fin N → ℝ),
        WilkiesDesign.E.eaEval (Work.WilE9G.Assembly.ambCat S c₂).X.c
          ((Work.WilE9G.Assembly.ambCat S c₂).h a) w = WilkiesDesign.E.eaEval S.X.c (S.h a) w) ∧
    (∀ (a : Fin S.j) (l : Fin N) (w : Fin N → ℝ),
        WilkiesDesign.E.eaEval (Work.WilE9G.Assembly.ambCat S c₂).X.c
          (WilkiesDesign.E.eaD (Work.WilE9G.Assembly.ambCat S c₂).X.c l
            ((Work.WilE9G.Assembly.ambCat S c₂).h a)) w
          = WilkiesDesign.E.eaEval S.X.c (WilkiesDesign.E.eaD S.X.c l (S.h a)) w) ∧
    (∀ (z : Fin N → ℝ) (a : Fin S.j),
        (fderiv ℝ (fun w : Fin N → ℝ =>
            WilkiesDesign.E.eaEval (Work.WilE9G.Assembly.ambCat S c₂).X.c
              ((Work.WilE9G.Assembly.ambCat S c₂).h a) w) z)
          = (fderiv ℝ (fun w : Fin N → ℝ =>
              WilkiesDesign.E.eaEval S.X.c (S.h a) w) z)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro a w
    simp only [ambCat_X_c, ambCat_h]
    exact Work.WilE7.SubPfAux.eaEval_cat_inl S.X.c c₂ (S.h a) w
  · intro a l w
    simp only [ambCat_X_c, ambCat_h]
    exact eaEval_eaD_cat_inl S.X.c c₂ l (S.h a) w
  · intro z a
    have hfun : (fun w : Fin N → ℝ => WilkiesDesign.E.eaEval
          (Work.WilE9G.Assembly.ambCat S c₂).X.c
          ((Work.WilE9G.Assembly.ambCat S c₂).h a) w)
        = (fun w => WilkiesDesign.E.eaEval S.X.c (S.h a) w) := by
      funext w
      simp only [ambCat_X_c, ambCat_h]
      exact Work.WilE7.SubPfAux.eaEval_cat_inl S.X.c c₂ (S.h a) w
    exact congrArg (fun F => fderiv ℝ F z) hfun

end Work.WilE9G.Assembly
