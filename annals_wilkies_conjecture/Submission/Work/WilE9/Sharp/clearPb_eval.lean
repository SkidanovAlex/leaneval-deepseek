/-
  WilE9 / Sharp — the clearing identity of the extended system.

  `clearPb n m K P` is the numerator `∏_b X (sDen b)^K · P (x ↦ y/w, s ↦ τ/u)`
  (`Sharp/ExtSystem.lean`, through `clearNumDen`).  This file proves that evaluating it in the
  extended chain `exChain c` at a point `z` of the extended ambient is the same as evaluating `P`
  in the pulled-back chain `pbChain c` at the reconstructed point `exSub z`, up to the common
  denominator:

      `eaEval (exChain c) (clearPb n m K P) z
         = (∏_b z (sDen b))^K · eaEval (pbChain c) P (exSub z)`.

  The two evaluation points are matched through the coordinate identification `pbEquiv` of
  `clearPb`: on the block `(x, s)` the extended point reads `y/w`, `τ/u` (exactly the entries of
  `exSub z`), and the exponential atoms agree because the chain functions of `pbChain c` at
  `exSub z` are those of `exChain c` at `z` (`pbChain_ell_exSub`).  The polynomial identity itself
  is `clearNumDen_eval`.
-/
import Mathlib
import Submission.Work.WilE9.Sharp.ExDefs
import Submission.Work.WilE9.Sharp.clearNumDen_eval
import Submission.Work.WilE9.Sharp.eaEval_exRaise
import Submission.Work.WilE9.Sharp.eaEval_pbRaise

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace Work.WilE9.Sharp
open WilkiesDesign WilkiesDesign.E

/-- The chain functions of the pulled-back and extended systems agree along the reconstruction
map `exSub`: `pbChain c`'s branch map at the reconstructed point `exSub z` is `exChain c`'s branch
map at `z` — both are the stratum's branch map at the stratum coordinates of `z`. -/
lemma pbChain_ell_exSub {n m r : ℕ} (c : EAChain (n + (1 + m)) r) (j : Fin r)
    (z : Fin (Next n m) → ℝ) :
    (pbChain c).ell j (exSub z) = (exChain c).ell j z := by
  rw [pbChain_ell, pbStrat_exSub, ← exChain_ell]

theorem clearPb_eval {n m r : ℕ} (c : WilkiesDesign.E.EAChain (n + (1 + m)) r) (K : ℕ)
    (P : WilkiesDesign.E.EAPoly (Work.WilE9.Sharp.Npb n m) r)
    (z : Fin (Work.WilE9.Sharp.Next n m) → ℝ) (hK : P.totalDegree ≤ K)
    (hd : ∀ b : Fin (n + 1), z (Work.WilE9.Sharp.sDen n m b) ≠ 0) :
    WilkiesDesign.E.eaEval (Work.WilE9.Sharp.exChain c)
        (Work.WilE9.Sharp.clearPb n m K P) z =
      (∏ b : Fin (n + 1), z (Work.WilE9.Sharp.sDen n m b)) ^ K *
        WilkiesDesign.E.eaEval (Work.WilE9.Sharp.pbChain c) P (Work.WilE9.Sharp.exSub z) := by
  classical
  -- the two branch maps agree, atom by atom
  have hell : ∀ j : Fin r, (pbChain c).ell j (exSub z) = (exChain c).ell j z :=
    fun j => pbChain_ell_exSub c j z
  -- the evaluation point of `exChain c` at `z`, and the substitution point of `clearPb`
  let v : Fin (Next n m) ⊕ Fin r → ℝ := Sum.elim z (fun j => Real.exp ((exChain c).ell j z))
  let ρ : (Fin (2 * n + m + 2) ⊕ Fin r) → Fin (Next n m) ⊕ Fin r :=
    Sum.elim (fun k => Sum.inl (sRest n m k)) (fun j => Sum.inr j)
  let φ : Fin (Npb n m) ⊕ Fin r → Fin (n + 1) ⊕ (Fin (2 * n + m + 2) ⊕ Fin r) :=
    ⇑(((pbEquiv n m).sumCongr (Equiv.refl (Fin r))).trans
        (Equiv.sumAssoc (Fin (n + 1)) (Fin (2 * n + m + 2)) (Fin r)))
  let w0 : Fin (n + 1) ⊕ (Fin (2 * n + m + 2) ⊕ Fin r) → ℝ :=
    Sum.elim (fun b => v (Sum.inl (sNum n m b)) / v (Sum.inl (sDen n m b))) (fun c' => v (ρ c'))
  let w1 : Fin (Npb n m) ⊕ Fin r → ℝ :=
    Sum.elim (exSub z) (fun j => Real.exp ((pbChain c).ell j (exSub z)))
  -- transported along `φ`, the substitution point of `clearPb` is the evaluation point of
  -- `pbChain c` at `exSub z`
  have hw0φ : w0 ∘ φ = w1 := by
    funext x
    rcases x with l | j
    · have hφl : φ (Sum.inl l)
          = Equiv.sumAssoc (Fin (n + 1)) (Fin (2 * n + m + 2)) (Fin r)
              (Sum.inl ((pbEquiv n m) l)) := by
        simp only [φ, Equiv.trans_apply, Equiv.sumCongr_apply, Sum.map_inl]
      rw [Function.comp_apply, hφl]
      simp only [w1, Sum.elim_inl, exSub]
      rcases hx : pbEquiv n m l with b | k
      · rw [Equiv.sumAssoc_apply_inl_inl]
        simp only [w0, v, Sum.elim_inl]
      · rw [Equiv.sumAssoc_apply_inl_inr]
        simp only [w0, v, ρ, Sum.elim_inl, Sum.elim_inr]
    · have hφj : φ (Sum.inr j) = Sum.inr (Sum.inr j) := by
        simp only [φ, Equiv.trans_apply, Equiv.sumCongr_apply, Sum.map_inr,
          Equiv.sumAssoc_apply_inr, Equiv.refl_apply]
      rw [Function.comp_apply, hφj]
      simp only [w1, w0, v, ρ, Sum.elim_inr]
      rw [hell j]
  have hK' : (P.rename φ).totalDegree ≤ K :=
    le_trans (MvPolynomial.totalDegree_rename_le φ P) hK
  have hkey := clearNumDen_eval (β := Fin (n + 1)) (γ := Fin (2 * n + m + 2) ⊕ Fin r)
    (α := Fin (Next n m) ⊕ Fin r)
    (fun b => Sum.inl (sNum n m b)) (fun b => Sum.inl (sDen n m b)) ρ K (P.rename φ) v hK' hd
  rw [show eaEval (exChain c) (clearPb n m K P) z
        = MvPolynomial.eval v (clearNumDen (fun b => Sum.inl (sNum n m b))
            (fun b => Sum.inl (sDen n m b)) ρ K (P.rename φ)) from rfl]
  rw [show eaEval (pbChain c) P (exSub z) = MvPolynomial.eval w1 P from rfl]
  rw [← hkey]
  rw [show MvPolynomial.eval w0 (MvPolynomial.rename φ P) = MvPolynomial.eval w1 P from by
        rw [MvPolynomial.eval_rename φ w0 P, hw0φ]]
  rw [show (∏ b : Fin (n + 1), v (Sum.inl (sDen n m b))) = ∏ b : Fin (n + 1), z (sDen n m b)
        from Finset.prod_congr rfl (fun b _ => rfl)]

end Work.WilE9.Sharp
