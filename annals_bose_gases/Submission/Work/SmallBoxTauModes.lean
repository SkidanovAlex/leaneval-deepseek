import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import ChallengeDeps
import Submission.Q0Sector
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Session-272 — the D1 b-mode operators `τ_g` (FS `tau_p`, lm:appbogolubov)

FS `lm:appbogolubov` (= the corpus's `lm_appbogolubov_refined_concrete`)
introduces the second-quantized operators

    tau_p^dag = |B|^{-1/2} a^dag(Q_B chi_B e^{-ipx}) a_0

(FS ll.4787-4790) and controls `A_2` with Bogoliubov's method applied to
`h(p) = A(p)(tau_p^dag tau_p + tau_{-p}^dag tau_{-p})
          + B(p)(tau_p^dag tau_{-p}^dag + tau_{-p} tau_p)`.

The crucial structural fact — FS's display
`(2 pi)^{-3} int f(p) tau_p^dag tau_p dp = |B|^{-1}(n_0+1) sum_j
(Q_B chi_B f(sqrt(-Delta)) chi_B Q_B)_j` — is that these operators are the
**mode expansion of the corpus's one- and two-body words**: `tau_p^dag`
removes one condensate particle and creates one in the (box-supported,
`Q_B`-projected) mode `g = Q_B chi_B e^{-ipx}`.

This module gives the two operators in the corpus's own position-slot
language (`X N = Fin N -> R^3`, `acube s`, `aP`/`aQ`) **explicitly**:

  * `tauDag s g Ψ x  = |B|^{-1/2} Σ_i g(x_i) ∫_{acube s} Ψ(x with slot i := z) dz`
  * `tauAnn s g Ψ x  = |B|^{-1/2} Σ_i ∫_{acube s} g z · Ψ(x with slot i := z) dz`

`tauAnn s g` is the (formal) adjoint of `tauDag s g` (a Fubini/change of
variables computation), and both are *bounded* operators (no derivative),
exactly as required by FS's abstract `thm:bogolubov-complete`
(`Commons.Analysis.Bogoliubov.two_mode_operator_identity`).

The key corpus bridge is `tauDag_eq_aP`: the condensate integral
`∫_{acube s} Ψ(update x i z) dz` is `s³` times the corpus's box-mean
projection `aP s i Ψ x`.

NOTATION CAVEAT: `|B| = s^3`; the factor `|B|^{-1/2}` is `sqrt(s^3)^{-1}`.
With `a_0 = a(1_B)` (the *unnormalised* constant mode) one has
`a_0 a_0^dag = |B|(n_0+1)`, whence `tau^dag tau = a^dag(g)(n_0+1)a(g)` —
the `(n_0+1)` of FS's display.
-/

noncomputable section
open MeasureTheory Metric
open scoped ContDiff Topology Real BigOperators ENNReal
namespace Submission
open _root_.BoseGases
namespace BoseGases

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-! ## 1 The two operators -/

/-- **the D1 creation operator** `tauDag s g = |B|^{-1/2} a†(g) a_0` in the
corpus's position-slot language. -/
noncomputable def tauDag (s : ℝ) {N : ℕ} (g : ℝ³ → ℝ) (Ψ : X N → ℝ) (x : X N) : ℝ :=
  (Real.sqrt (s ^ 3))⁻¹ * ∑ i : Fin N, g (x i) * ∫ z in acube s, Ψ (Function.update x i z)

/-- **the D1 annihilation operator** `tauAnn s g = |B|^{-1/2} a_0† a(g)`, the
formal adjoint of `tauDag s g`. -/
noncomputable def tauAnn (s : ℝ) {N : ℕ} (g : ℝ³ → ℝ) (Ψ : X N → ℝ) (x : X N) : ℝ :=
  (Real.sqrt (s ^ 3))⁻¹ * ∑ i : Fin N, ∫ z in acube s, g z * Ψ (Function.update x i z)

/-! ## 2 Elementary algebra -/

@[simp] lemma tauDag_zero_g (s : ℝ) {N : ℕ} (Ψ : X N → ℝ) :
    tauDag s (fun _ => (0 : ℝ)) Ψ = 0 := by
  funext x
  simp [tauDag]

@[simp] lemma tauAnn_zero_g (s : ℝ) {N : ℕ} (Ψ : X N → ℝ) :
    tauAnn s (fun _ => (0 : ℝ)) Ψ = 0 := by
  funext x
  simp [tauAnn]

lemma tauDag_add_g (s : ℝ) {N : ℕ} (g₁ g₂ : ℝ³ → ℝ) (Ψ : X N → ℝ) :
    tauDag s (fun z => g₁ z + g₂ z) Ψ = tauDag s g₁ Ψ + tauDag s g₂ Ψ := by
  funext x
  have h : ∀ i : Fin N, (g₁ (x i) + g₂ (x i)) * (∫ z in acube s, Ψ (Function.update x i z))
      = g₁ (x i) * (∫ z in acube s, Ψ (Function.update x i z))
        + g₂ (x i) * (∫ z in acube s, Ψ (Function.update x i z)) := fun i => by ring
  simp only [tauDag, Pi.add_apply]
  rw [Finset.sum_congr rfl (fun i _ => h i), Finset.sum_add_distrib, mul_add]

lemma tauDag_smul_g (s c : ℝ) {N : ℕ} (g : ℝ³ → ℝ) (Ψ : X N → ℝ) :
    tauDag s (fun z => c * g z) Ψ = fun x => c * tauDag s g Ψ x := by
  funext x
  have h : ∀ i : Fin N, (c * g (x i)) * (∫ z in acube s, Ψ (Function.update x i z))
      = c * (g (x i) * (∫ z in acube s, Ψ (Function.update x i z))) := fun i => by ring
  simp only [tauDag]
  rw [Finset.sum_congr rfl (fun i _ => h i), ← Finset.mul_sum]
  ring

lemma tauDag_nonneg_mode (s : ℝ) {N : ℕ} {g : ℝ³ → ℝ} (hg : 0 ≤ g) {Ψ : X N → ℝ}
    (hΨ : 0 ≤ Ψ) (x : X N) :
    0 ≤ tauDag s g Ψ x := by
  have hs3 : 0 ≤ (Real.sqrt (s ^ 3))⁻¹ := inv_nonneg.mpr (Real.sqrt_nonneg _)
  refine mul_nonneg hs3 (Finset.sum_nonneg fun i _ => ?_)
  refine mul_nonneg (hg _) (integral_nonneg fun z => ?_)
  exact hΨ _

/-! ## 3 The corpus bridge: `tauDag` and the box-mean projection `aP` -/

/-- the condensate integral is `s³` times the corpus box-mean `aP`. -/
lemma acube_integral_update_eq {s : ℝ} (hs : s ≠ 0) {N : ℕ} (i : Fin N)
    (Ψ : X N → ℝ) (x : X N) :
    (∫ z in acube s, Ψ (Function.update x i z)) = s ^ 3 * aP s i Ψ x := by
  rw [aP]
  field_simp

/-- **the corpus bridge**: `tauDag` is the `aP`-weighted mode sum. -/
theorem tauDag_eq_aP {s : ℝ} (hs : s ≠ 0) {N : ℕ} (g : ℝ³ → ℝ) (Ψ : X N → ℝ) (x : X N) :
    tauDag s g Ψ x = (Real.sqrt (s ^ 3))⁻¹ * ∑ i : Fin N, g (x i) * (s ^ 3 * aP s i Ψ x) := by
  rw [tauDag]
  congr 1
  exact Finset.sum_congr rfl fun i _ => by rw [acube_integral_update_eq hs]

end BoseGases
end Submission
