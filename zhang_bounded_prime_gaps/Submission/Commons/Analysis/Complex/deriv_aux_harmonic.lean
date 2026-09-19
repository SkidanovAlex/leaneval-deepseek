import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

open Complex
open scoped BigOperators RealInnerProductSpace
open ComplexConjugate

namespace Commons.Analysis.Complex

/-! Helpers for `deriv_aux_harmonic`.

The real derivative of `t ↦ Real.log ‖F t‖` along a complex-differentiable real path
`F` equals `Re (F' / F)`.  We reduce `log ‖·‖` to `(1/2) log (normSq ·)` and use
the squared-norm derivative from inner-product calculus. -/

private lemma re_div_eq_mul_conj_div_normSq (w u : ℂ) (hu : u ≠ 0) :
    Complex.re (w / u) = (w * conj u).re / Complex.normSq u := by
  have hn : Complex.normSq u ≠ 0 := by
    exact fun h => hu (Complex.normSq_eq_zero.mp h)
  rw [Complex.div_re, Complex.mul_re, Complex.conj_re, Complex.conj_im]
  field_simp [hn]
  ring

private lemma hasDerivAt_log_norm_of_hasDerivAt {F : ℝ → ℂ} {x : ℝ} {w : ℂ}
    (hF : HasDerivAt F w x) (h0 : F x ≠ 0) :
    HasDerivAt (fun t : ℝ => Real.log ‖F t‖) (Complex.re (w / F x)) x := by
  have hident : (fun t : ℝ => Real.log ‖F t‖)
      = fun t => (1 / 2 : ℝ) * Real.log (Complex.normSq (F t)) := by
    funext t
    have hs : Real.log ‖F t‖ = Real.log (Complex.normSq (F t)) / 2 := by
      rw [Complex.norm_def, Real.log_sqrt (Complex.normSq_nonneg (F t))]
    rw [hs]
    ring
  have hnsq : HasDerivAt (fun t : ℝ => Complex.normSq (F t))
      (2 * ⟪F x, w⟫) x := by
    simpa [Complex.normSq_eq_norm_sq] using
      (hF.norm_sq : HasDerivAt (fun t : ℝ => ‖F t‖ ^ 2) (2 * ⟪F x, w⟫) x)
  have hnsq0 : Complex.normSq (F x) ≠ 0 := by
    exact ne_of_gt (Complex.normSq_pos.2 h0)
  have hlog : HasDerivAt (fun t : ℝ => Real.log (Complex.normSq (F t)))
      ((2 * ⟪F x, w⟫) / Complex.normSq (F x)) x := hnsq.log hnsq0
  have hhalf : HasDerivAt (fun t : ℝ => (1 / 2 : ℝ) * Real.log (Complex.normSq (F t)))
      ((1 / 2 : ℝ) * ((2 * ⟪F x, w⟫) / Complex.normSq (F x))) x := hlog.const_mul (1 / 2 : ℝ)
  have hval : (1 / 2 : ℝ) * ((2 * ⟪F x, w⟫) / Complex.normSq (F x))
      = ⟪F x, w⟫ / Complex.normSq (F x) := by ring
  convert hhalf using 1
  rw [hval]
  rw [Complex.inner]
  rw [← re_div_eq_mul_conj_div_normSq w (F x) h0]

/-- The real-line path `t ↦ g (a + (t : ℂ))` has complex derivative `deriv g a` at `0`. -/
private lemma deriv_path_g {a : ℂ} {g : ℂ → ℂ} (hg : DifferentiableAt ℂ g a) :
    HasDerivAt (fun t : ℝ => g (a + (t : ℂ))) (deriv g a) (0 : ℝ) := by
  have hg' : HasDerivAt g (deriv g a) a := hg.hasDerivAt
  have hg'a0 : HasDerivAt g (deriv g a) (a + (0 : ℂ)) := by simpa using hg'
  have hid : HasDerivAt (fun t : ℝ => (t : ℂ)) (1 : ℂ) (0 : ℝ) := by
    simpa using ((hasDerivAt_id (0 : ℂ)) : HasDerivAt (fun x : ℂ => x) 1 (0 : ℂ)).comp_ofReal (z := (0 : ℝ))
  have htr : HasDerivAt (fun t : ℝ => a + (t : ℂ)) (1 : ℂ) (0 : ℝ) := by
    simpa using (hid.const_add a : HasDerivAt (fun t : ℝ => a + (t : ℂ)) 1 (0 : ℝ))
  have hcomp : HasDerivAt (fun t : ℝ => g (a + (t : ℂ))) ((deriv g a) * (1 : ℂ)) (0 : ℝ) := by
    simpa [Function.comp_def] using (hg'a0.comp (0 : ℝ) htr)
  simpa using hcomp

/-- The affine real-line path `t ↦ (a + (t : ℂ)) - u` has derivative `1` at `0`. -/
private lemma deriv_path_affine {a u : ℂ} :
    HasDerivAt (fun t : ℝ => (a + (t : ℂ)) - u) (1 : ℂ) (0 : ℝ) := by
  have hid : HasDerivAt (fun t : ℝ => (t : ℂ)) (1 : ℂ) (0 : ℝ) := by
    simpa using ((hasDerivAt_id (0 : ℂ)) : HasDerivAt (fun x : ℂ => x) 1 (0 : ℂ)).comp_ofReal (z := (0 : ℝ))
  simpa using ((hid.const_add a : HasDerivAt (fun t : ℝ => a + (t : ℂ)) 1 (0 : ℝ)).sub_const u)

theorem deriv_aux_harmonic {a : ℂ} {R : ℝ} (hR : 0 < R) {g : ℂ → ℂ} {M : ℂ → ℂ} {D : ℂ → ℤ}
    {S : Finset ℂ}
    (hg : DifferentiableAt ℂ g a) (hg0 : g a ≠ 0)
    (hM : ∀ u ∈ S, a - M u ≠ 0) :
    HasDerivAt (fun t : ℝ => Real.log ‖g (a + (t : ℂ))‖ +
        ∑ u ∈ S, ((D u : ℤ) : ℝ) * Real.log ‖(a + (t : ℂ)) - M u‖)
      (Complex.re (deriv g a / g a) +
        ∑ u ∈ S, ((D u : ℤ) : ℝ) * Complex.re (1 / (a - M u))) 0 := by
  have hg0' : g (a + (0 : ℂ)) ≠ 0 := by simpa using hg0
  have hgder : HasDerivAt (fun t : ℝ => g (a + (t : ℂ))) (deriv g a) (0 : ℝ) :=
    deriv_path_g hg
  have h1 : HasDerivAt (fun t : ℝ => Real.log ‖g (a + (t : ℂ))‖)
      (Complex.re (deriv g a / g a)) (0 : ℝ) := by
    simpa using hasDerivAt_log_norm_of_hasDerivAt hgder hg0'
  have hsummand : ∀ u : ℂ, u ∈ S →
      HasDerivAt (fun t : ℝ => Real.log ‖(a + (t : ℂ)) - M u‖)
        (Complex.re (1 / (a - M u))) (0 : ℝ) := by
    intro u hu
    have hM0 : (a + (0 : ℂ)) - M u ≠ 0 := by simpa using hM u hu
    have hpath : HasDerivAt (fun t : ℝ => (a + (t : ℂ)) - M u) (1 : ℂ) (0 : ℝ) :=
      deriv_path_affine (a := a) (u := M u)
    simpa using hasDerivAt_log_norm_of_hasDerivAt hpath hM0
  have hsummand_mul : ∀ u : ℂ, u ∈ S →
      HasDerivAt (fun t : ℝ => ((D u : ℤ) : ℝ) * Real.log ‖(a + (t : ℂ)) - M u‖)
        (((D u : ℤ) : ℝ) * Complex.re (1 / (a - M u))) (0 : ℝ) := by
    intro u hu
    simpa using (hsummand u hu).const_mul (((D u : ℤ) : ℝ))
  have hS0 : HasDerivAt
      (∑ u ∈ S, (fun t : ℝ => ((D u : ℤ) : ℝ) * Real.log ‖(a + (t : ℂ)) - M u‖))
      (∑ u ∈ S, ((D u : ℤ) : ℝ) * Complex.re (1 / (a - M u))) (0 : ℝ) := by
    simpa using
      (HasDerivAt.sum (A := fun u : ℂ => fun t : ℝ => ((D u : ℤ) : ℝ) * Real.log ‖(a + (t : ℂ)) - M u‖)
        (A' := fun u : ℂ => ((D u : ℤ) : ℝ) * Complex.re (1 / (a - M u))) hsummand_mul)
  have hS : HasDerivAt
      (fun t : ℝ => ∑ u ∈ S, ((D u : ℤ) : ℝ) * Real.log ‖(a + (t : ℂ)) - M u‖)
      (∑ u ∈ S, ((D u : ℤ) : ℝ) * Complex.re (1 / (a - M u))) (0 : ℝ) := by
    convert hS0 using 1
    funext t
    simp
  convert h1.add hS using 1
  all_goals try (first | rfl | (funext t; rfl))
  all_goals (funext t; simp)

end Commons.Analysis.Complex