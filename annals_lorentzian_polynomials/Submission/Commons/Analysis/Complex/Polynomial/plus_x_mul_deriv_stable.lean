import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.RingTheory.SimpleRing.Principal

set_option linter.ambiguousOpen false

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
half plane, then for all `u`, `x` in the upper half plane the value of
`P + x * P.derivative` at `u` is nonzero.  Equivalently, the differential operator
`P ↦ P + x · P'` preserves the property of having no zeroes in the open upper half
plane, for every `x` in the upper half plane. -/
theorem plus_x_mul_deriv_stable (P : Polynomial ℂ) (hP0 : P ≠ 0)
    (hstab : ∀ u : UpperHalfPlane, Polynomial.eval (u : ℂ) P ≠ 0) :
    ∀ u : UpperHalfPlane, ∀ x : UpperHalfPlane,
      Polynomial.eval (u : ℂ) P + (x : ℂ) * Polynomial.eval (u : ℂ) P.derivative ≠ 0 := by
  classical
  intro u x
  let z : ℂ := (u : ℂ)
  have hz : 0 < z.im := by simpa [z] using u.coe_im_pos
  have hzstab : Polynomial.eval z P ≠ 0 := by simpa [z] using hstab u
  by_cases hs : P.roots = 0
  · have hd : P.derivative = 0 := (Polynomial.derivative_eq_zero (R := ℂ)).2
      (IsAlgClosed.roots_eq_zero_iff_natDegree_eq_zero.mp hs)
    simpa [hd] using hstab u
  · have hfac : Polynomial.C P.leadingCoeff *
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
    let S : ℂ := (P.roots.map (fun a => (z - a)⁻¹)).sum
    have hterm : ∀ a ∈ P.roots, (((z - a)⁻¹).im) < 0 := by
      intro a ha
      exact term_im_neg z hz a (root_im_le_zero P hP0 hstab a ha)
    have hImS : S.im < 0 := by
      have hcore : ((P.roots.map (fun a => (z - a)⁻¹)).sum).im < 0 := by
        rw [im_sum, Multiset.map_map]
        exact sum_lt_zero_of_neg (P.roots.map (fun a => ((z - a)⁻¹).im))
          (by simpa using hs) (by
            intro b hb
            rcases Multiset.mem_map.mp hb with ⟨a, ha, rfl⟩
            exact hterm a ha)
      simpa [S] using hcore
    intro hzero
    have hzero' : Polynomial.eval z P + (x : ℂ) * Polynomial.eval z P.derivative = 0 := by
      simpa [z] using hzero
    have hmul : Polynomial.eval z P * (1 + (x : ℂ) * S) = 0 := by
      calc
        Polynomial.eval z P * (1 + (x : ℂ) * S)
            = Polynomial.eval z P + (x : ℂ) * (Polynomial.eval z P * S) := by ring
        _ = Polynomial.eval z P + (x : ℂ) * Polynomial.eval z P.derivative := by
              rw [hId]
        _ = 0 := hzero'
    have h1 : 1 + (x : ℂ) * S = 0 := (mul_eq_zero.mp hmul).resolve_left hzstab
    have hxS : (x : ℂ) * S = -1 := by
      calc
        (x : ℂ) * S = (1 + (x : ℂ) * S) - 1 := by ring
        _ = -1 := by
              rw [h1]
              ring
    have hxne : (x : ℂ) ≠ 0 := UpperHalfPlane.ne_zero x
    have hS : S = - (x : ℂ)⁻¹ := by
      calc
        S = (x : ℂ)⁻¹ * ((x : ℂ) * S) := by
              rw [← mul_assoc, inv_mul_cancel₀ hxne, one_mul]
        _ = (x : ℂ)⁻¹ * -1 := by rw [hxS]
        _ = - (x : ℂ)⁻¹ := by ring
    have hneg_im : (-(x : ℂ)⁻¹).im = (x : ℂ).im / Complex.normSq (x : ℂ) := by
      simp [Complex.inv_im]
      ring
    have hImPos : 0 < (-(x : ℂ)⁻¹).im := by
      rw [hneg_im]
      exact div_pos x.coe_im_pos (Complex.normSq_pos.mpr hxne)
    have hImSpos : 0 < S.im := by
      rw [hS]
      exact hImPos
    exact (lt_asymm hImS) hImSpos

end
end Commons.Analysis.Complex.Polynomial