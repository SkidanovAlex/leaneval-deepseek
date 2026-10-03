/-
# `Submission.Work.FIArea6Hecke.R.LamOneNeZeroDefs`

Vocabulary for `Work.FIArea6Hecke.R.Lam_one_ne_zero`: the **entire continuation**
`Lcont d Lam s = Lam s · (4d/π)^{-s} · Γ(s)^{-1}` of the Hecke `L`-function built from an entire
completion `Lam` of `(4d/π)^s Γ(s)·L(s,ψ)`.

Mathlib has `Complex.differentiable_one_div_Gamma` (the function `s ↦ Γ(s)^{-1}` is entire, with
the convention `Γ(-n) = 0` so that `Γ^{-1}` has a simple zero at the poles of `Γ`), so `Lcont` is
entire and equals `Lam s / heckeArch d 0 s` — i.e. the honest `L(s,ψ)` — everywhere.
-/
import Mathlib
import Submission.Commons.NumberTheory.GaussianInt.two_squares_repr_count_eq_sum_chi4
import Submission.Commons.NumberTheory.DirichletCharacter.estermann_positivity
import Submission.Commons.NumberTheory.Zeta.riemannZeta_neg_of_Ioo_half_one
import Submission.Commons.NumberTheory.DirichletCharacter.exists_odd_character_mod_four
import Submission.Work.FIArea6Hecke.R.ZFRStatementDefs
import Submission.Work.FIArea6Hecke.ZFRDefs
import Submission.Work.FIArea6Hecke.R.heckeLSeries_principalStrict_eq
import Submission.Work.FIArea6Hecke.R.AxisLogDefs
import Submission.Work.FIArea6Hecke.R.axisChi4_LSeries_facts
import Submission.Commons.NumberTheory.GaussianInt.primary_associate_exists_unique
import Submission.Work.FIArea5.S16Hecke.primaryAux

set_option autoImplicit false

namespace Work.FIArea6Hecke.R

open scoped BigOperators

noncomputable section

/-! ## The archimedean base and the entire continuation -/

/-- The real base `4d/π` of the archimedean factor, as a complex number. -/
def archBase (d : ℕ) : ℂ := (((4 * (d : ℝ)) / Real.pi : ℝ) : ℂ)

lemma archBase_ne_zero {d : ℕ} (hd : 1 ≤ d) : archBase d ≠ 0 := by
  rw [archBase, Complex.ofReal_ne_zero]
  have hd' : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  positivity

/-- `heckeArch d 0 s = (4d/π)^s·Γ(s)`, with the base written as `archBase d`. -/
lemma heckeArch_zero_eq (d : ℕ) (s : ℂ) :
    Work.FITop4.Bridge.heckeArch d 0 s = archBase d ^ s * Complex.Gamma s := by
  rw [Work.FITop4.Bridge.heckeArch, archBase]
  norm_num

/-- **The entire continuation of `L(s,ψ)` attached to a completion `Lam`.**  Since `s ↦ Γ(s)^{-1}`
is entire (`Complex.differentiable_one_div_Gamma`) the function `Lcont d Lam` is entire whenever
`Lam` is, and it equals `Lam s / heckeArch d 0 s` identically. -/
def Lcont (d : ℕ) (Lam : ℂ → ℂ) : ℂ → ℂ :=
  fun s => Lam s * (archBase d) ^ (-s) * (Complex.Gamma s)⁻¹

/-- `Lcont d Lam` is entire when `Lam` is. -/
theorem Lcont_differentiable {d : ℕ} (hd : 1 ≤ d) {Lam : ℂ → ℂ}
    (h : Differentiable ℂ Lam) : Differentiable ℂ (Lcont d Lam) := by
  have hb : archBase d ≠ 0 := archBase_ne_zero hd
  intro s
  refine DifferentiableAt.mul (DifferentiableAt.mul (h s) ?_) ?_
  · exact (differentiableAt_id (x := s)).neg.const_cpow (c := archBase d) (Or.inl hb)
  · exact Complex.differentiable_one_div_Gamma.differentiableAt

/-- `Lcont d Lam` is the quotient of `Lam` by the archimedean factor — identically, because
`(4d/π)^s·(4d/π)^{-s} = 1` and `Γ(s)·Γ(s)^{-1} = 1`. -/
theorem Lcont_eq_div (d : ℕ) (Lam : ℂ → ℂ) (s : ℂ) :
    Lcont d Lam s = Lam s / Work.FITop4.Bridge.heckeArch d 0 s := by
  rw [heckeArch_zero_eq, Lcont, Complex.cpow_neg, div_eq_mul_inv, mul_inv]
  ring

/-- On the half-plane of absolute convergence, `Lcont d Lam` is the Hecke `L`-series of `χ`. -/
theorem Lcont_eq_heckeLSeries {d : ℕ} (hd : 1 ≤ d) {chi : GaussianInt → ℂ} {Lam : ℂ → ℂ}
    (hagr : ∀ s : ℂ, 1 < s.re →
      Lam s = Work.FITop4.Bridge.heckeArch d 0 s * Work.FIArea5.S16Hecke.heckeLSeries chi 0 s)
    {s : ℂ} (hs : 1 < s.re) : Lcont d Lam s = Work.FIArea5.S16Hecke.heckeLSeries chi 0 s := by
  rw [Lcont_eq_div, hagr s hs]
  have hne : Work.FITop4.Bridge.heckeArch d 0 s ≠ 0 := by
    rw [heckeArch_zero_eq]
    refine mul_ne_zero ?_ ?_
    · rw [Complex.cpow_ne_zero_iff]; exact Or.inl (archBase_ne_zero hd)
    · exact Complex.Gamma_ne_zero_of_re_pos (by linarith)
  exact mul_div_cancel_left₀ _ hne

/-- The value of `Lcont d Lam` at `s = 1` is `Lam 1·π/(4d)`. -/
theorem Lcont_one_eq (d : ℕ) (Lam : ℂ → ℂ) :
    Lcont d Lam 1 = Lam 1 * (archBase d)⁻¹ := by
  rw [Lcont, Complex.cpow_neg, Complex.cpow_one, Complex.Gamma_one, inv_one, mul_one]

theorem Lcont_one_eq_zero_iff {d : ℕ} (hd : 1 ≤ d) (Lam : ℂ → ℂ) :
    Lcont d Lam 1 = 0 ↔ Lam 1 = 0 := by
  rw [Lcont_one_eq]
  constructor
  · intro h
    exact (mul_eq_zero.mp h).resolve_right (inv_ne_zero (archBase_ne_zero hd))
  · intro h; rw [h, zero_mul]

/-- `Lam 1 = heckeArch d 0 1 · Lcont d Lam 1`. -/
theorem Lam_one_eq_arch_mul_Lcont {d : ℕ} (hd : 1 ≤ d) (Lam : ℂ → ℂ) :
    Lam 1 = Work.FITop4.Bridge.heckeArch d 0 1 * Lcont d Lam 1 := by
  rw [Lcont_one_eq, heckeArch_zero_eq, Complex.cpow_one, Complex.Gamma_one, mul_one]
  rw [← mul_assoc, mul_comm (archBase d) (Lam 1), mul_assoc,
    mul_inv_cancel₀ (archBase_ne_zero hd), mul_one]

/-- The archimedean factor is non-zero at `s = 1`. -/
theorem heckeArch_zero_one_ne_zero {d : ℕ} (hd : 1 ≤ d) :
    Work.FITop4.Bridge.heckeArch d 0 1 ≠ 0 := by
  rw [heckeArch_zero_eq, Complex.cpow_one, Complex.Gamma_one, mul_one]
  exact archBase_ne_zero hd

/-- `heckeArch d 0` is holomorphic at every point of the open right half-plane. -/
theorem heckeArch_zero_differentiableAt {d : ℕ} (hd : 1 ≤ d) {s : ℂ} (hs : 0 < s.re) :
    DifferentiableAt ℂ (Work.FITop4.Bridge.heckeArch d 0) s := by
  have hfun : Work.FITop4.Bridge.heckeArch d 0
      = fun t : ℂ => archBase d ^ t * Complex.Gamma t := by
    funext t; exact heckeArch_zero_eq d t
  rw [hfun]
  refine DifferentiableAt.mul ?_ ?_
  · exact (differentiableAt_id (x := s)).const_cpow (c := archBase d) (Or.inl (archBase_ne_zero hd))
  · refine Complex.differentiableAt_Gamma s (fun m hm => ?_)
    have : s.re = -(m : ℝ) := by rw [hm]; simp
    have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    linarith

/-- `σ ↦ heckeArch d 0 (σ:ℂ)` is continuous at `1`. -/
theorem heckeArch_zero_continuousAt_one {d : ℕ} (hd : 1 ≤ d) :
    ContinuousAt (fun σ : ℝ => Work.FITop4.Bridge.heckeArch d 0 (σ : ℂ)) (1 : ℝ) := by
  have h1 : ContinuousAt (Work.FITop4.Bridge.heckeArch d 0) (((1 : ℝ)) : ℂ) :=
    (heckeArch_zero_differentiableAt hd (s := (((1 : ℝ)) : ℂ))
      (by norm_num : (0:ℝ) < ((((1 : ℝ)) : ℂ)).re)).continuousAt
  exact h1.comp (Complex.continuous_ofReal.continuousAt (x := (1 : ℝ)))

/-! ## Hecke eigenvalues depend only on the values on primary elements -/

/-- The Hecke eigenvalue `λ(n) = ∑_{z primary, |z|²=n} ψ(z)` depends only on the values of `χ`
on the *primary* elements. -/
lemma heckeLam_eq_of_primary_agree {chi chi' : GaussianInt → ℂ} {k : ℤ}
    (h : ∀ z : GaussianInt, Work.FIPlan.IsPrimary z → chi z = chi' z) (n : ℕ) :
    Work.FIArea5.S16Hecke.heckeLam chi k n = Work.FIArea5.S16Hecke.heckeLam chi' k n := by
  classical
  unfold Work.FIArea5.S16Hecke.heckeLam
  refine Finset.sum_congr rfl (fun z hz => ?_)
  rw [Finset.mem_filter] at hz
  simp only [Work.FIArea5.S16Hecke.psi]
  rw [h z hz.2.1]

/-- The Hecke `L`-series of `(χ,k)` depends only on the values of `χ` on primary elements. -/
lemma heckeLSeries_eq_of_primary_agree {chi chi' : GaussianInt → ℂ} {k : ℤ}
    (h : ∀ z : GaussianInt, Work.FIPlan.IsPrimary z → chi z = chi' z) :
    Work.FIArea5.S16Hecke.heckeLSeries chi k = Work.FIArea5.S16Hecke.heckeLSeries chi' k := by
  funext s
  simp only [Work.FIArea5.S16Hecke.heckeLSeries]
  congr 1
  funext n
  exact heckeLam_eq_of_primary_agree h n

end

end Work.FIArea6Hecke.R
