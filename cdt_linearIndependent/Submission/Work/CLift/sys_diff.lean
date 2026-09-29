import Mathlib
import Submission.Work.CLift.bridge
import Submission.Work.CLift.Phi_ne_root
import Submission.Work.CLift.Phi_small
import Submission.Work.CLift.basic_aux
import Submission.Work.CLift.R2p_ne_zero
import Submission.Work.CLift.entry_diff

namespace Work.CLift

open Work.CLift Submission.CDTPlan Metric

/-- The pulled-back system of Theorem C, `(u,v) ↦ sysA(m,n,Φ)(z)(u,v) + sysb(m,n,Φ)(z)`, is
holomorphic on the annulus `3.2·10⁻⁴ < ‖z‖ < 1`.

Indeed `sysA m n Φ z = deriv Φ z • A₀(Φ z)` and `sysb m n ra rb rab Φ z = deriv Φ z • c₀(Φ z)`:
the scalar factor `deriv Φ` is holomorphic because `Φ` is holomorphic on the (open) unit disc
(`DifferentiableOn.deriv`), and every entry of `A₀`, `c₀` is a rational function of `Φ z` whose
only poles are the roots of `R2p = (x-1)xQ₄`.  Those are avoided on the annulus by
`R2p_ne_zero` (from `Phi_ne_one`, `hΦ0`, `q4_roots` and `Phi_ne_root`), so the entries are
holomorphic there (`entry_diff`); the `Fin 2`-indexed matrix/vector is assembled pointwise. -/
theorem sys_diff (m n : ℕ) (ra rb rab r0 : ℤ) (hL : CLocation) (hN : CNumerics)
    (hM : HauptFacts) (hP : PsiCFacts) (hAdm : CAdm m n) (hRel : CRel m n ra rb rab r0)
    (Φ : ℂ → ℂ)
    (hΦdiff : DifferentiableOn ℂ Φ (ball (0 : ℂ) 1))
    (hΦeq : ∀ z ∈ ball (0 : ℂ) 1, Φ z + Φ (-z) = phiC (z ^ 2) ∧ Φ z * Φ (-z) = phiC (z ^ 2))
    (hΦ0 : ∀ z ∈ ball (0 : ℂ) 1, Φ z = 0 → z = 0) :
    DifferentiableOn ℂ (sysA m n Φ) {z : ℂ | 3.2e-4 < ‖z‖ ∧ ‖z‖ < 1} ∧
      DifferentiableOn ℂ (sysb m n ra rb rab Φ) {z : ℂ | 3.2e-4 < ‖z‖ ∧ ‖z‖ < 1} := by
  have hball : ∀ z : ℂ, 3.2e-4 < ‖z‖ ∧ ‖z‖ < 1 → z ∈ ball (0 : ℂ) 1 := by
    intro z hz
    rw [mem_ball, dist_zero_right]
    exact hz.2
  -- `Φ` and `deriv Φ` are holomorphic on the annulus
  have hΦA : DifferentiableOn ℂ Φ {z : ℂ | 3.2e-4 < ‖z‖ ∧ ‖z‖ < 1} :=
    hΦdiff.mono (fun z hz => hball z hz)
  have hderivA : DifferentiableOn ℂ (deriv Φ) {z : ℂ | 3.2e-4 < ‖z‖ ∧ ‖z‖ < 1} :=
    (hΦdiff.deriv isOpen_ball).mono (fun z hz => hball z hz)
  -- `Φ z` never hits a pole of the gauge coefficients on the annulus
  have hR2 : ∀ z : ℂ, z ∈ {z : ℂ | 3.2e-4 < ‖z‖ ∧ ‖z‖ < 1} → R2p m n (Φ z) ≠ 0 := by
    intro z hz
    exact R2p_ne_zero m n ra rb rab r0 hL hN hM hP hAdm hRel Φ hΦeq hΦ0 hz.1 hz.2
  obtain ⟨hdA21, hdA22, hdc2⟩ := entry_diff m n ra rb rab Φ hΦA hR2
  -- the remaining entries
  have hdA11 : DifferentiableOn ℂ (fun _ : ℂ => A11) {z : ℂ | 3.2e-4 < ‖z‖ ∧ ‖z‖ < 1} :=
    differentiableOn_const A11
  have hdA12 : DifferentiableOn ℂ (fun z => A12 (Φ z)) {z : ℂ | 3.2e-4 < ‖z‖ ∧ ‖z‖ < 1} := by
    simpa only [A12] using hΦA.add_const 1
  have hdbbeta : DifferentiableOn ℂ (fun _ : ℂ => bbeta m n ra rb)
      {z : ℂ | 3.2e-4 < ‖z‖ ∧ ‖z‖ < 1} :=
    differentiableOn_const (bbeta m n ra rb)
  constructor
  · unfold sysA
    rw [differentiableOn_pi]
    intro i
    rw [differentiableOn_pi]
    intro j
    fin_cases i <;> fin_cases j <;> simp only [Fin.isValue]
    · exact hderivA.mul_const A11
    · exact hderivA.mul hdA12
    · exact hderivA.mul hdA21
    · exact hderivA.mul hdA22
  · unfold sysb
    rw [differentiableOn_pi]
    intro i
    fin_cases i <;> simp only [Fin.isValue]
    · exact hderivA.mul_const (bbeta m n ra rb)
    · exact hderivA.mul hdc2

end Work.CLift
