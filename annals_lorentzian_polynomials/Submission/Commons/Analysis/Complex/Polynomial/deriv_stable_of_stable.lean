import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.RingTheory.SimpleRing.Principal

namespace Commons.Analysis.Complex.Polynomial

open Polynomial UpperHalfPlane

noncomputable section

private lemma multiset_X_sub_C_prod_deriv_eval (s : Multiset ℂ) (z : ℂ) :
    ((s.map (fun a => Polynomial.X - Polynomial.C a)).prod).eval z ≠ 0 →
      ((s.map (fun a => Polynomial.X - Polynomial.C a)).prod).derivative.eval z =
        ((s.map (fun a => Polynomial.X - Polynomial.C a)).prod).eval z *
          (s.map (fun a => (z - a)⁻¹)).sum := by
  induction s using Multiset.induction_on with
  | empty =>
      intro hz
      simp
  | cons a t ih =>
      intro hz
      have hzG : ((t.map (fun b => Polynomial.X - Polynomial.C b)).prod).eval z ≠ 0 := by
        have : (z - a) * ((t.map (fun b => Polynomial.X - Polynomial.C b)).prod).eval z ≠ 0 := by
          simpa using hz
        exact (mul_ne_zero_iff.mp this).2
      have hza : z ≠ a := by
        have : (z - a) * ((t.map (fun b => Polynomial.X - Polynomial.C b)).prod).eval z ≠ 0 := by
          simpa using hz
        exact sub_ne_zero.mp (mul_ne_zero_iff.mp this).1
      have hrec := ih hzG
      have hL : (((a ::ₘ t).map (fun b => Polynomial.X - Polynomial.C b)).prod).derivative.eval z
          = ((t.map (fun b => Polynomial.X - Polynomial.C b)).prod).eval z *
              (1 + (z - a) * (t.map (fun b => (z - b)⁻¹)).sum) := by
        calc
          (((a ::ₘ t).map (fun b => Polynomial.X - Polynomial.C b)).prod).derivative.eval z
              = ((Polynomial.X - Polynomial.C a) * (t.map (fun b => Polynomial.X - Polynomial.C b)).prod).derivative.eval z := by
                simp
          _ = ((t.map (fun b => Polynomial.X - Polynomial.C b)).prod).eval z
              + (z - a) * (((t.map (fun b => Polynomial.X - Polynomial.C b)).prod).derivative.eval z) := by
                rw [Polynomial.derivative_mul]
                simp [Polynomial.eval_add, Polynomial.eval_mul]
          _ = ((t.map (fun b => Polynomial.X - Polynomial.C b)).prod).eval z
              + (z - a) * (((t.map (fun b => Polynomial.X - Polynomial.C b)).prod).eval z * (t.map (fun b => (z - b)⁻¹)).sum) := by
                rw [hrec]
          _ = ((t.map (fun b => Polynomial.X - Polynomial.C b)).prod).eval z *
              (1 + (z - a) * (t.map (fun b => (z - b)⁻¹)).sum) := by
                ring
      have hR : (((a ::ₘ t).map (fun b => Polynomial.X - Polynomial.C b)).prod).eval z *
            ((a ::ₘ t).map (fun b => (z - b)⁻¹)).sum
          = ((t.map (fun b => Polynomial.X - Polynomial.C b)).prod).eval z *
              (1 + (z - a) * (t.map (fun b => (z - b)⁻¹)).sum) := by
        simp
        have hmul : (z - a) * (z - a)⁻¹ = 1 := mul_inv_cancel₀ (sub_ne_zero.mpr hza)
        calc
          (z - a) * ((t.map (fun b => Polynomial.X - Polynomial.C b)).prod).eval z * ((z - a)⁻¹ + (t.map (fun b => (z - b)⁻¹)).sum)
              = ((t.map (fun b => Polynomial.X - Polynomial.C b)).prod).eval z * ((z - a) * ((z - a)⁻¹ + (t.map (fun b => (z - b)⁻¹)).sum)) := by ring
          _ = ((t.map (fun b => Polynomial.X - Polynomial.C b)).prod).eval z * ((z - a) * (z - a)⁻¹ + (z - a) * (t.map (fun b => (z - b)⁻¹)).sum) := by ring
          _ = ((t.map (fun b => Polynomial.X - Polynomial.C b)).prod).eval z * (1 + (z - a) * (t.map (fun b => (z - b)⁻¹)).sum) := by rw [hmul]
      exact hL.trans hR.symm

private lemma im_sum (s : Multiset ℂ) : (s.sum).im = (s.map Complex.im).sum := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a t ih => simp [ih]

private lemma sum_lt_zero_of_neg (s : Multiset ℝ) (hs : s ≠ 0)
    (h : ∀ a ∈ s, a < 0) : s.sum < 0 := by
  induction s using Multiset.induction_on with
  | empty => simp at hs
  | cons a t ih =>
      by_cases ht : t = 0
      · subst t
        have ha : a < 0 := h a (by simp)
        simpa using ha
      · have hrest : t.sum < 0 := ih ht (fun b hb => h b (by simp [hb]))
        have ha : a < 0 := h a (by simp)
        simp
        linarith

private lemma root_im_le_zero (P : Polynomial ℂ) (_hP0 : P ≠ 0)
    (hstab : ∀ u : UpperHalfPlane, Polynomial.eval (u : ℂ) P ≠ 0) :
    ∀ a ∈ P.roots, a.im ≤ 0 := by
  intro a ha
  have hroot : Polynomial.eval a P = 0 := by
    simpa using (Polynomial.isRoot_of_mem_roots ha)
  by_contra h
  have him : 0 < a.im := lt_of_not_ge h
  have hstab' : Polynomial.eval a P ≠ 0 := by simpa using hstab ⟨a, him⟩
  exact hstab' hroot

private lemma term_im_neg (z : ℂ) (hz : 0 < z.im) (a : ℂ) (hima : a.im ≤ 0) :
    ((z - a)⁻¹).im < 0 := by
  have hzima : 0 < z.im - a.im := sub_pos.mpr (lt_of_le_of_lt hima hz)
  have hdz : 0 < (z - a).im := by simpa [Complex.sub_im] using hzima
  rw [Complex.inv_im]
  apply div_neg_of_neg_of_pos
  · exact neg_lt_zero.mpr hdz
  · exact Complex.normSq_pos.mpr (by
      intro hza
      have : (z - a).im = 0 := by simpa using congrArg Complex.im hza
      linarith)

/-- If a nonzero complex polynomial `P` does not vanish at any point of the open upper
half plane, then either its derivative is the zero polynomial, or the derivative does
not vanish at any point of the open upper half plane either. (This is the univariate
half of the Gauss--Lucas-type statement: the roots of `P.derivative` lie in the closed
lower half plane whenever the roots of `P` do.) -/
theorem deriv_stable_of_stable (P : Polynomial ℂ) (hP0 : P ≠ 0)
    (hstab : ∀ u : UpperHalfPlane, Polynomial.eval (u : ℂ) P ≠ 0) :
    P.derivative = 0 ∨ ∀ u : UpperHalfPlane, Polynomial.eval (u : ℂ) P.derivative ≠ 0 := by
  classical
  by_cases hs : P.roots = 0
  · left
    exact (Polynomial.derivative_eq_zero (R := ℂ)).2
      (IsAlgClosed.roots_eq_zero_iff_natDegree_eq_zero.mp hs)
  · right
    intro u
    let z : ℂ := (u : ℂ)
    have hzstab : Polynomial.eval z P ≠ 0 := by simpa [z] using hstab u
    have hrootb : ∀ a ∈ P.roots, a.im ≤ 0 := root_im_le_zero P hP0 hstab
    have hfac : Polynomial.C P.leadingCoeff *
          (P.roots.map (fun a => Polynomial.X - Polynomial.C a)).prod = P := by
      exact Polynomial.C_leadingCoeff_mul_prod_multiset_X_sub_C (p := P)
        (IsAlgClosed.card_roots_eq_natDegree (p := P))
    have hFne : ((P.roots.map (fun a => Polynomial.X - Polynomial.C a)).prod).eval z ≠ 0 := by
      intro hF0
      have : Polynomial.eval z P = 0 := by
        rw [← hfac]
        simp [Polynomial.eval_mul, hF0]
      exact hzstab this
    have hFid : ((P.roots.map (fun a => Polynomial.X - Polynomial.C a)).prod).derivative.eval z
        = ((P.roots.map (fun a => Polynomial.X - Polynomial.C a)).prod).eval z *
            (P.roots.map (fun a => (z - a)⁻¹)).sum :=
      multiset_X_sub_C_prod_deriv_eval P.roots z hFne
    have hId : P.derivative.eval z
        = Polynomial.eval z P * (P.roots.map (fun a => (z - a)⁻¹)).sum := by
      calc
        P.derivative.eval z = (Polynomial.C P.leadingCoeff *
            (P.roots.map (fun a => Polynomial.X - Polynomial.C a)).prod).derivative.eval z := by rw [hfac]
        _ = Polynomial.eval z (Polynomial.derivative (Polynomial.C P.leadingCoeff) *
              (P.roots.map (fun a => Polynomial.X - Polynomial.C a)).prod
            + Polynomial.C P.leadingCoeff * Polynomial.derivative ((P.roots.map (fun a => Polynomial.X - Polynomial.C a)).prod)) := by
              rw [Polynomial.derivative_mul]
        _ = P.leadingCoeff * ((P.roots.map (fun a => Polynomial.X - Polynomial.C a)).prod.derivative.eval z) := by
              rw [Polynomial.derivative_C]
              simp [Polynomial.eval_mul]
        _ = P.leadingCoeff * (((P.roots.map (fun a => Polynomial.X - Polynomial.C a)).prod).eval z *
              (P.roots.map (fun a => (z - a)⁻¹)).sum) := by
              rw [hFid]
        _ = P.leadingCoeff * ((P.roots.map (fun a => Polynomial.X - Polynomial.C a)).prod).eval z *
            (P.roots.map (fun a => (z - a)⁻¹)).sum := by ring
        _ = Polynomial.eval z P * (P.roots.map (fun a => (z - a)⁻¹)).sum := by
              calc
                P.leadingCoeff * ((P.roots.map (fun a => Polynomial.X - Polynomial.C a)).prod).eval z * (P.roots.map (fun a => (z - a)⁻¹)).sum
                    = (Polynomial.C P.leadingCoeff * (P.roots.map (fun a => Polynomial.X - Polynomial.C a)).prod).eval z *
                        (P.roots.map (fun a => (z - a)⁻¹)).sum := by
                        simp [Polynomial.eval_mul]
                _ = Polynomial.eval z P * (P.roots.map (fun a => (z - a)⁻¹)).sum := by rw [hfac]
    have hterm : ∀ a ∈ P.roots, (((z - a)⁻¹).im) < 0 := by
      intro a ha
      exact term_im_neg z (by simpa [z] using u.coe_im_pos) a (hrootb a ha)
    have hTne : (P.roots.map (fun a => (z - a)⁻¹)).sum ≠ 0 := by
      have him : ((P.roots.map (fun a => (z - a)⁻¹)).sum).im < 0 := by
        rw [im_sum, Multiset.map_map]
        exact sum_lt_zero_of_neg (P.roots.map (fun a => ((z - a)⁻¹).im))
          (by simpa using hs) (by
            intro b hb
            rcases Multiset.mem_map.mp hb with ⟨a, ha, rfl⟩
            exact hterm a ha)
      intro hzero
      have : ((P.roots.map (fun a => (z - a)⁻¹)).sum).im = 0 := by
        rw [hzero]
        simp
      exact (ne_of_lt him) this
    intro hzero
    have hsum : (P.roots.map (fun a => (z - a)⁻¹)).sum = 0 := by
      have hmul : Polynomial.eval z P * (P.roots.map (fun a => (z - a)⁻¹)).sum = 0 := by
        rw [← hId]
        exact hzero
      exact (mul_eq_zero.mp hmul).resolve_left hzstab
    exact hTne hsum

end
end Commons.Analysis.Complex.Polynomial