import Mathlib
import Submission.Work.WilE5.Sys
import Submission.Work.WilE5.Calc.hasFDerivAt_eaEval
import Submission.Work.WilE5.Calc.fderiv_eq_sum_of_vanishes_on_levelSet
import Submission.Work.WilE5.Operators.detOp_extH_eq_zero
import Submission.Work.Strat.det_extJac_ne_zero
import Submission.Work.WilE5.Strat.flatConormalTools

noncomputable section
open Classical Filter
open scoped Topology

namespace Work.WilE5.Strat

open WilkiesDesign WilkiesDesign.E

/-! ## §0c. The fibrewise conormal form -/

/-- **Fibrewise conormal form.**  If `φ` vanishes on the fibre level set of `h` over `z` (the base
coordinates pinned to those of `z`) and the pivot minor of `h` is invertible at `z`, then the fibre
gradient of `φ` at `z` is a linear combination of the fibre gradients of the `h a`. -/
theorem fibre_conormal {p q r j : ℕ} (c : EAChain (p + q) r)
    (h : Fin j → EAPoly (p + q) r) (ι : Fin j → Fin (p + q))
    (hι : ∀ a, ∃ l : Fin q, ι a = yDir p l)
    (φ : EAPoly (p + q) r) (z : Fin (p + q) → ℝ)
    (hHz : ∀ a, eaEval c (h a) z = 0)
    (hdet : (Matrix.of fun a b => eaEval c (eaD c (ι b) (h a)) z).det ≠ 0)
    (hvan : ∀ᶠ w in nhds z,
      (∀ i : Fin p, w (Fin.castAdd q i) = z (Fin.castAdd q i)) →
      (∀ a, eaEval c (h a) w = 0) → eaEval c φ w = 0) :
    ∃ lam : Fin j → ℝ, ∀ l : Fin q,
      eaEval c (eaD c (yDir p l) φ) z =
        ∑ a : Fin j, lam a * eaEval c (eaD c (yDir p l) (h a)) z := by
  classical
  set h' : Fin (j + p) → EAPoly (p + q) r := extH h z with hh'
  set ι' : Fin (j + p) → Fin (p + q) := extι ι with hι''
  set g : (Fin (p + q) → ℝ) → (Fin (j + p) → ℝ) := fun w b => eaEval c (h' b) w with hg
  set f : (Fin (p + q) → ℝ) → ℝ := fun w => eaEval c φ w with hf
  have hcast : ∀ a : Fin j, h' (Fin.castAdd p a) = h a := fun a => by
    rw [hh', extH, Fin.append_left]
  have hnat : ∀ i : Fin p, h' (Fin.natAdd j i) = xShift (q := q) (r := r) z i := fun i => by
    rw [hh', extH, Fin.append_right]
  have hgz : g z = 0 := by
    funext b
    refine Fin.addCases ?_ ?_ b
    · intro a
      show eaEval c (h' (Fin.castAdd p a)) z = 0
      rw [hcast a]
      exact hHz a
    · intro i
      show eaEval c (h' (Fin.natAdd j i)) z = 0
      rw [hnat i]
      show eaEval c (xShift (q := q) (r := r) z i) z = 0
      rw [Work.WilE5.eaEval_xShift]; simp
  have hgstrict : HasStrictFDerivAt g (fderiv ℝ g z) z := by
    have han : AnalyticAt ℝ g z := by
      rw [hg]
      exact AnalyticAt.pi (fun b => analyticAt_eaEval c (h' b) z)
    exact han.hasStrictFDerivAt
  have hfderiv : HasFDerivAt f (fderiv ℝ f z) z := by
    have h0 := Work.WilE5.Calc.hasFDerivAt_eaEval c φ z
    rw [hf, h0.fderiv]
    exact h0
  have hcomp : fderiv ℝ g z = ContinuousLinearMap.pi (fun b : Fin (j + p) =>
      (∑ i : Fin (p + q), eaEval c (eaD c i (h' b)) z •
        (ContinuousLinearMap.proj i : (Fin (p + q) → ℝ) →L[ℝ] ℝ))) := by
    rw [hg]
    exact fderiv_pi_eaEval c h' z
  have hdetmat : ((Matrix.of fun a b => eaEval c (eaD c (ι' b) (h' a)) z)).det ≠ 0 := by
    have h0 := Work.Strat.det_extJac_ne_zero c h ι hι z hdet
    rwa [← hh', ← hι''] at h0
  have hsurj : (fderiv ℝ g z).range = ⊤ := by
    rw [hcomp]
    exact range_pi_eq_top_of_det_submatrix_ne_zero
      (fun b i => eaEval c (eaD c i (h' b)) z) ι' hdetmat
  have hv : ∀ᶠ w in nhds z, g w = 0 → f w = 0 :=
    hvan.mono fun w hw hgw => by
      have hbase : ∀ i : Fin p, w (Fin.castAdd q i) = z (Fin.castAdd q i) := fun i => by
        have h2 : eaEval c (h' (Fin.natAdd j i)) w = 0 := congrFun hgw _
        rw [hnat i, Work.WilE5.eaEval_xShift] at h2
        exact sub_eq_zero.mp h2
      have hh0 : ∀ a, eaEval c (h a) w = 0 := fun a => by
        have h2 : eaEval c (h' (Fin.castAdd p a)) w = 0 := congrFun hgw _
        rwa [hcast a] at h2
      rw [hf]
      exact hw hbase hh0
  obtain ⟨lam, hlam⟩ := Work.WilE5.Calc.fderiv_eq_sum_of_vanishes_on_levelSet g f z
    hgstrict hfderiv hgz hsurj hv
  refine ⟨fun a => lam (Fin.castAdd p a), fun l => ?_⟩
  calc eaEval c (eaD c (yDir p l) φ) z
      = (fderiv ℝ f z) (Pi.single (yDir p l) 1) := by
        rw [hf, fderiv_eaEval_apply_single]
    _ = (∑ b, lam b • ((ContinuousLinearMap.proj b) ∘L (fderiv ℝ g z)))
          (Pi.single (yDir p l) 1) := by rw [hlam]
    _ = ∑ b : Fin (j + p), lam b * eaEval c (eaD c (yDir p l) (h' b)) z := by
        rw [ContinuousLinearMap.sum_apply]
        refine Finset.sum_congr rfl fun b _ => ?_
        rw [ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply,
          ContinuousLinearMap.proj_apply, smul_eq_mul]
        congr 1
        rw [hcomp]
        exact pi_apply_single _ _ b
    _ = ∑ a : Fin j, lam (Fin.castAdd p a) * eaEval c (eaD c (yDir p l) (h a)) z := by
        rw [Fin.sum_univ_add]
        rw [show (∑ a : Fin j, lam (Fin.castAdd p a) *
              eaEval c (eaD c (yDir p l) (h' (Fin.castAdd p a))) z)
            = ∑ a : Fin j, lam (Fin.castAdd p a) * eaEval c (eaD c (yDir p l) (h a)) z from
          Finset.sum_congr rfl fun a _ => by rw [hcast a]]
        rw [show (∑ i : Fin p, lam (Fin.natAdd j i) *
              eaEval c (eaD c (yDir p l) (h' (Fin.natAdd j i))) z) = 0 from
          Finset.sum_eq_zero fun i _ => by
            rw [hnat i, Work.WilE5.Operators.eaD_yDir_xShift]
            have h0 : eaEval c (0 : EAPoly (p + q) r) z = 0 := by simp [eaEval]
            rw [h0, mul_zero]]
        rw [add_zero]

end Work.WilE5.Strat
