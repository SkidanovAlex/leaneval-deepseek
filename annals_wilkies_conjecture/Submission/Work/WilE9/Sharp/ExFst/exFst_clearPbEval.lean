import Mathlib
import Submission.Work.WilE9.Sharp.ExDefs
import Submission.Work.WilE9.Sharp.clearNumDen_eval

namespace Work.WilE9.Sharp.ExFst

open WilkiesDesign WilkiesDesign.E

/-- **The pointwise identity underlying the clearing of denominators.**  Reading the substitution
`xᵢ ↦ z (exY i)/z (exW i)`, `s ↦ z (exT)/z (exU)` through the reindexing performed by `clearPb`
and the chain evaluation `z ↦ exp (ℓ_j z)` gives the evaluation of the pulled-back chain at
`exSub z`, provided the affine forms agree (`hell`). -/
private lemma comp_subst_eq_exSub {n m r : ℕ} (c : EAChain (n + (1 + m)) r)
    (z : Fin (Next n m) → ℝ)
    (hell : ∀ j : Fin r, (pbChain c).ell j (exSub z) = (exChain c).ell j z) :
    (Sum.elim
        (fun b : Fin (n + 1) =>
          (Sum.elim z (fun j => Real.exp ((exChain c).ell j z))) (Sum.inl (sNum n m b)) /
          (Sum.elim z (fun j => Real.exp ((exChain c).ell j z))) (Sum.inl (sDen n m b)))
        (fun c' => (Sum.elim z (fun j => Real.exp ((exChain c).ell j z)))
          (Sum.elim (fun k => Sum.inl (sRest n m k)) (fun j => Sum.inr j) c'))) ∘
      (⇑(((pbEquiv n m).sumCongr (Equiv.refl (Fin r))).trans
        (Equiv.sumAssoc (Fin (n + 1)) (Fin (2 * n + m + 2)) (Fin r))))
    = Sum.elim (exSub z) (fun j => Real.exp ((pbChain c).ell j (exSub z))) := by
  funext x
  rcases x with i | j
  · -- the substituted block: the `x`/`s` coordinates are read off by `exSub`
    simp only [Function.comp_apply, Equiv.trans_apply, Equiv.sumCongr_apply, Sum.map_inl,
      Sum.elim_inl, exSub]
    cases h : pbEquiv n m i with
    | inl b => simp [h]
    | inr k => simp [h]
  · -- the remaining coordinates: the exponentials agree by `hell`
    simp only [Function.comp_apply, Equiv.trans_apply, Equiv.sumCongr_apply, Sum.map_inr,
      Equiv.sumAssoc_apply_inr, Sum.elim_inl, Sum.elim_inr, exSub, hell j]
    rw [Equiv.refl_apply]

theorem exFst_clearPbEval {n m r : ℕ} (c : WilkiesDesign.E.EAChain (n + (1 + m)) r) (K : ℕ)
    (P : WilkiesDesign.E.EAPoly (Work.WilE9.Sharp.Npb n m) r) (hK : P.totalDegree ≤ K)
    (z : Fin (Work.WilE9.Sharp.Next n m) → ℝ)
    (hell : ∀ j : Fin r,
      (Work.WilE9.Sharp.pbChain c).ell j (Work.WilE9.Sharp.exSub z) =
        (Work.WilE9.Sharp.exChain c).ell j z)
    (hden : ∀ b : Fin (n + 1), z (Work.WilE9.Sharp.sDen n m b) ≠ 0) :
    WilkiesDesign.E.eaEval (Work.WilE9.Sharp.exChain c)
        (Work.WilE9.Sharp.clearPb n m K P) z =
      (∏ b : Fin (n + 1), z (Work.WilE9.Sharp.sDen n m b)) ^ K *
        WilkiesDesign.E.eaEval (Work.WilE9.Sharp.pbChain c) P (Work.WilE9.Sharp.exSub z) := by
  unfold WilkiesDesign.E.eaEval clearPb
  -- reading the substituted point back through the evaluation of the pulled-back chain
  have heval : MvPolynomial.eval
        (Sum.elim
          (fun b : Fin (n + 1) =>
            (Sum.elim z (fun j => Real.exp ((exChain c).ell j z))) (Sum.inl (sNum n m b)) /
            (Sum.elim z (fun j => Real.exp ((exChain c).ell j z))) (Sum.inl (sDen n m b)))
          (fun c' => (Sum.elim z (fun j => Real.exp ((exChain c).ell j z)))
            (Sum.elim (fun k => Sum.inl (sRest n m k)) (fun j => Sum.inr j) c')))
        (P.rename ⇑(((pbEquiv n m).sumCongr (Equiv.refl (Fin r))).trans
          (Equiv.sumAssoc (Fin (n + 1)) (Fin (2 * n + m + 2)) (Fin r))))
      = MvPolynomial.eval
          (Sum.elim (exSub z) (fun j => Real.exp ((pbChain c).ell j (exSub z)))) P := by
    rw [MvPolynomial.eval_rename, comp_subst_eq_exSub c z hell]
  -- the denominator product
  have hprod : (∏ b : Fin (n + 1),
        (Sum.elim z (fun j => Real.exp ((exChain c).ell j z))) (Sum.inl (sDen n m b)))
      = ∏ b, z (sDen n m b) :=
    Finset.prod_congr rfl (fun b _ => rfl)
  -- the denominator clearing identity of `clearNumDen`
  have hmain := clearNumDen_eval
    (β := Fin (n + 1)) (γ := Fin (2 * n + m + 2) ⊕ Fin r) (α := Fin (Next n m) ⊕ Fin r)
    (fun b => Sum.inl (sNum n m b)) (fun b => Sum.inl (sDen n m b))
    (Sum.elim (fun k => Sum.inl (sRest n m k)) (fun j => Sum.inr j)) K
    (P.rename ⇑(((pbEquiv n m).sumCongr (Equiv.refl (Fin r))).trans
      (Equiv.sumAssoc (Fin (n + 1)) (Fin (2 * n + m + 2)) (Fin r))))
    (Sum.elim z (fun j => Real.exp ((exChain c).ell j z)))
    (le_trans (MvPolynomial.totalDegree_rename_le _ P) hK)
    (fun b => by simpa using hden b)
  rw [← hmain, hprod, heval]

end Work.WilE9.Sharp.ExFst
