/-
# HB (11.16) — the regularised twisted contour integrand

Namespace `Work.LinnikAreas2`.  This module is the vocabulary of the off-diagonal pair bound
HB (1992) §11, (11.16): the two-exponential smoothing

    T = Σ_n (Σ_{d|n}θ_d)² χ(n)χ̄'(n) n^{1-ρ-ρ̄'} (e^{-n/X} - e^{-n𝓛²/U})

is the difference `Ssm X - Ssm Y` (with `Y = U/𝓛²`) of two smoothed Dirichlet sums of the
*mollified* coefficient `Θ(n)²`, whose Dirichlet series is `L(w, χχ̄')·F(w)` with the finite
lcm-weight `F` of HB §11.  Both sums are represented by the Mellin integral of the *naive*
integrand `Γ(s)(X^s - Y^s)L(σ+s, χχ̄')F(σ+s)` on `Re s = 1`; the difference kernel is regular at
`s = 0` (the two poles cancel), so the contour may be shifted to `Re s = 1 - σ.re - 1/k`.

`Ptw` is that difference kernel, written in the manifestly holomorphic form
`Γ(s+1)·dslope (u ↦ X^u - Y^u) 0 s · L(σ+s)·F(σ+s)`, which agrees with the naive integrand for
`s ≠ 0` (`Ptw_eq_naive`) and is differentiable on the half-plane `Re s > -1`.
-/
import Mathlib
import Submission.Work.LinnikAreas.Density4.SsmSetup
import Submission.Work.LinnikAreas.Density4.diffOn_Gamma_dslope_mul_lcmF

open DirichletCharacter Complex
open scoped Classical BigOperators
noncomputable section

namespace Work.LinnikAreas2

open Work.LinnikAreas.Density4

/-- The regularised twisted contour integrand of HB (11.16): the difference kernel
`Γ(s)(X^s - Y^s) L(σ+s, χ) F(σ+s)`, written as `Γ(s+1)·dslope (u ↦ X^u - Y^u) 0 s·L·F` so that
the removable singularity at `s = 0` (cancellation of the two `Γ`-poles) is already performed. -/
def Ptw (q : ℕ) [NeZero q] (U V W X Y : ℝ) (χ : DirichletCharacter ℂ q) (σ : ℂ) : ℂ → ℂ :=
  fun s => Complex.Gamma (s + 1) *
    dslope (fun u : ℂ => (X : ℂ) ^ u - (Y : ℂ) ^ u) 0 s *
    DirichletCharacter.LFunction χ (σ + s) *
    lcmF q U V W χ (σ + s)

/-- The kernel of the `dslope` vanishes at `0`. -/
@[simp] lemma Ptw_zero_arg (X Y : ℝ) :
    (fun u : ℂ => (X : ℂ) ^ u - (Y : ℂ) ^ u) 0 = 0 := by simp

/-- Off `s = 0`, `Ptw` is the naive integrand (the difference of the two exponential kernels). -/
lemma Ptw_eq_naive (q : ℕ) [NeZero q] (U V W X Y : ℝ) (χ : DirichletCharacter ℂ q) (σ s : ℂ)
    (hs : s ≠ 0) :
    Ptw q U V W X Y χ σ s =
      Complex.Gamma s * ((X : ℂ) ^ s - (Y : ℂ) ^ s) *
        DirichletCharacter.LFunction χ (σ + s) * lcmF q U V W χ (σ + s) := by
  rw [Ptw, dslope_of_ne (fun u : ℂ => (X : ℂ) ^ u - (Y : ℂ) ^ u) hs, slope,
    Complex.Gamma_add_one s hs]
  simp only [Complex.cpow_zero, sub_self, sub_zero, vsub_eq_sub, smul_eq_mul]
  field_simp

/-- `Ptw` is complex differentiable on the half-plane `Re s > -1`. -/
lemma differentiableOn_Ptw (q : ℕ) [NeZero q] (U V W X Y : ℝ) (χ : DirichletCharacter ℂ q)
    (hχ : χ ≠ 1) (hX : 0 < X) (hY : 0 < Y) (σ : ℂ) :
    DifferentiableOn ℂ (Ptw q U V W X Y χ σ) {s : ℂ | -1 < s.re} := by
  have hds : DifferentiableOn ℂ (dslope (fun u : ℂ => (X : ℂ) ^ u - (Y : ℂ) ^ u) 0)
      {s : ℂ | -1 < s.re} :=
    (Complex.differentiableOn_dslope (f := fun u : ℂ => (X : ℂ) ^ u - (Y : ℂ) ^ u) (c := 0)
      (s := {s : ℂ | -1 < s.re}) (hc := (isOpen_lt continuous_const continuous_re).mem_nhds
        (by simp))).mpr (by
        intro s hs
        have hXne : (X : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hX
        have hYne : (Y : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hY
        exact ((differentiableAt_id.const_cpow (Or.inl hXne)).sub
          (differentiableAt_id.const_cpow (Or.inl hYne))).differentiableWithinAt)
  have hshift : Differentiable ℂ (fun u : ℂ => σ + u) := differentiable_id.const_add σ
  have hL : Differentiable ℂ (fun s : ℂ => DirichletCharacter.LFunction χ (σ + s)) :=
    (differentiable_LFunction hχ).comp hshift
  have hlcm : Differentiable ℂ (fun s : ℂ => lcmF q U V W χ (σ + s)) :=
    (differentiable_lcmF q U V W χ).comp hshift
  have hGam : DifferentiableOn ℂ (fun s : ℂ => Complex.Gamma (s + 1)) {s : ℂ | -1 < s.re} := by
    intro s hs
    refine ((Complex.differentiableAt_Gamma (s + 1) ?_).comp s
      (differentiableAt_id.add_const 1)).differentiableWithinAt
    intro m hm
    have hre : (s + 1).re = (-(m : ℂ)).re := congrArg Complex.re hm
    have h1 : (-(m : ℂ)).re = -(m : ℝ) := by simp
    have h2 : (s + 1).re = s.re + 1 := by simp
    have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    have hs' : -1 < s.re := hs
    linarith [hre, h1, h2, hm0, hs']
  exact ((hGam.mul hds).mul hL.differentiableOn).mul hlcm.differentiableOn

end Work.LinnikAreas2
