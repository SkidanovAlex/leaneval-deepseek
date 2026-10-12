import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.SmallBoxBridge.Cauchy.integrable_cModeForm
import Submission.Work.SmallBoxBridge.Fourier.T0Form_slot_eq_dirichlet
import Submission.Work.SmallBoxBridge.Fourier.integrable_rSlotAmp
import Submission.Work.SmallBoxBridge.ModeIdent
import Submission.Work.SmallBoxBridge.ModeIdent.kinPWord_eq_pModeForm
import Submission.Work.SmallBoxBridge.Position.dirichlet_aQ_le
import Submission.Work.SmallBoxBridge.Position.winErrorQ_le_cnPlus
import Submission.Work.SmallBoxSuperadd
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# THE KINETIC BRIDGE OF THE SMALLBOX FIXED-`n` BOUND

This module assembles the sorry-free chapter `Submission/Work/SmallBoxBridge/` into the bridge

    kinPWord s c Φ  ≤  (N̂+1)·(2·chiSup²·kinWord N s Φ + 2·winErrorQ s Φ) ,

dominating the D1 p-space kinetic word by the corpus's honest position-space kinetic word plus the
window-derivative error (constants are free for `theorem_1_2`).

## The chain

1. `kinPWord_eq_pModeForm` — `kinPWord` IS the corpus mode form `pModeForm s (fsKinCoeff c)`
   (`ModeIdent/kinPWord_eq_pModeForm`).
2. `pModeForm_le_pDiagForm` — Cauchy–Schwarz on the `N̂+1` slot amplitudes (FS's `(n+1)` of the
   coefficient `𝒜(p) = |B|/(n+1)[|p|−c]₊² + 2K_sa`: the mode content `b_p†b_p` dominates the
   one-body form only up to the condensate two-body term, bounded by `n_0 ≤ N̂`).
3. `pDiagForm_eq_T0Form` — the corpus mode `qMode s p = Q_B(χ_s e^{−i⟪p,·⟫})` has slot amplitude
   `pSlotAmp = rawSlotAmp ∘ (aQ s i)`: the diagonal mode form IS the `𝒯₀` form
   `Σ_i Q_iχ_iF(√−Δ_i)χ_iQ_i` in its windowed-exponential Fourier form.  (The `(c1)` kernel
   identity itself is `Kernel/windowed_expansion_eq_winKernel` and
   `Kernel/winExpansion_complex_eq_kernel`.)
4. `T0Form_le_kinWord` — the position-space half: the symbol bound
   `fsKinCoeff c = [·−c]₊² ≤ (·)²`, the per-slot fibre Plancherel
   `Fourier/T0Form_slot_eq_dirichlet` (with `Resolve/winModeForm_sq_eq_dirichlet` and the closed
   `FourierDerivEnergy.integral_fderiv_sq_eq_fourier`), the Leibniz/window bound
   `Position/dirichlet_aQ_le` (with the closed `SmallBoxKinBridge.fderiv_mul_coord_sq_le`,
   `SmallBoxKinBridge.fderiv_aQ_kcDir`, `Q0Sector`'s `integral_aQ_sq_le` via
   `kinWord_aQ_le`).

The window error `winErrorQ s Ψ = Σ_i∫_{abox}|∇χ_s(x_i)|²(aQ s i Ψ)²` is the standard
window-derivative remainder produced by the Leibniz step (absorbed in the smallbox assembly by the
`n₊`-gap / `ε_T`-term).
-/

noncomputable section

open MeasureTheory Metric
open scoped ContDiff Topology Real BigOperators

namespace Submission

open _root_.BoseGases
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option linter.unusedVariables false

namespace BoseGases

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-- **The position-space half.**  `𝒯₀` with the D1 symbol `[·−c]₊²` is dominated by twice the
window mass times the corpus's kinetic word plus twice the window-derivative error. -/
theorem T0Form_le_kinWord {n : ℕ} {s c : ℝ} (hs : 0 < s) (hc : 0 ≤ c) {Ψ : X (n + 1) → ℝ}
    (hΨ : ContDiff ℝ ∞ Ψ) (hsupp : tsupport Ψ ⊆ abox (n + 1) s) :
    T0Form s (fsKinCoeff c) Ψ
      ≤ 2 * chiSup ^ 2 * kinWord (n + 1) s Ψ + 2 * winErrorQ s Ψ := by
  -- (a) monotone in the symbol, slot by slot
  have hmono : T0Form s (fsKinCoeff c) Ψ ≤ T0Form s (fun r => r ^ 2) Ψ := by
    unfold T0Form
    refine Finset.sum_le_sum (fun i _ => ?_)
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    refine integral_mono_of_nonneg (Filter.Eventually.of_forall (fun p => ?_))
      (Work.SmallBoxBridge.Fourier.integrable_rSlotAmp (n := n) (s := s) hs hΨ i)
      (Filter.Eventually.of_forall (fun p => ?_))
    · exact mul_nonneg (fsKinCoeff_nonneg c ‖p‖) (mul_nonneg (by positivity)
        (integral_nonneg fun x => sq_nonneg _))
    · exact mul_le_mul_of_nonneg_right (fsKinCoeff_le_sq hc (norm_nonneg p))
        (mul_nonneg (by positivity) (integral_nonneg fun x => sq_nonneg _))
  -- (b) the fibre Plancherel identity, slot by slot
  have hEq : T0Form s (fun r => r ^ 2) Ψ
      = ∑ i : Fin (n + 1), ∫ x in abox (n + 1) s, ∑ k : Fin 3,
          (fderiv ℝ (fun z : X (n + 1) => chiScale s (z i) * aQ s i Ψ z) x
            (kcDir (n + 1) i k)) ^ 2 := by
    unfold T0Form
    exact Finset.sum_congr rfl
      (fun i _ => Work.SmallBoxBridge.Fourier.T0Form_slot_eq_dirichlet hs hΨ hsupp i)
  -- (c) the Leibniz/window step
  calc T0Form s (fsKinCoeff c) Ψ ≤ T0Form s (fun r => r ^ 2) Ψ := hmono
    _ = ∑ i : Fin (n + 1), ∫ x in abox (n + 1) s, ∑ k : Fin 3,
          (fderiv ℝ (fun z : X (n + 1) => chiScale s (z i) * aQ s i Ψ z) x
            (kcDir (n + 1) i k)) ^ 2 := hEq
    _ ≤ 2 * chiSup ^ 2 * kinWord (n + 1) s Ψ + 2 * winErrorQ s Ψ :=
        Work.SmallBoxBridge.Position.dirichlet_aQ_le hs hΨ

/-- **THE KINETIC BRIDGE OF THE SMALLBOX FIXED-`n` BOUND** (`kinWord ≥ ⟨Φ,𝒯₀Φ⟩` sharpened to the
D1 word): the p-space kinetic word of FS's `lm:appbogolubov` is dominated by `N̂+1` times the
corpus's honest position-space kinetic word plus the window-derivative error. -/
theorem kinPWord_le_kinWord {n : ℕ} {s c : ℝ} (hs : 0 < s) (hc : 0 ≤ c) {Φ : X (n + 1) → ℝ}
    (hΦ : ContDiff ℝ ∞ Φ) (hsupp : tsupport Φ ⊆ abox (n + 1) s) :
    kinPWord s c Φ ≤ ((n : ℝ) + 2) *
      (2 * chiSup ^ 2 * kinWord (n + 1) s Φ + 2 * winErrorQ s Φ) := by
  rw [Work.SmallBoxBridge.ModeIdent.kinPWord_eq_pModeForm hs hΦ.continuous]
  have h1 := Work.SmallBoxBridge.Cauchy.pModeForm_le_pDiagForm (N := n + 1) (s := s) (F := fsKinCoeff c)
    hs (fsKinCoeff_nonneg c) hΦ.continuous
    (Work.SmallBoxBridge.Cauchy.integrable_cModeForm (n := n) hs hc hΦ)
  have h2 : pDiagForm s (fsKinCoeff c) Φ = T0Form s (fsKinCoeff c) Φ :=
    pDiagForm_eq_T0Form hs (fsKinCoeff c) hΦ.continuous
  have h3 := T0Form_le_kinWord (n := n) hs hc hΦ hsupp
  have hcast : (((n + 1 : ℕ) : ℝ) + 1) = (n : ℝ) + 2 := by
    push_cast
    ring
  calc pModeForm s (fsKinCoeff c) Φ
      ≤ (((n + 1 : ℕ) : ℝ) + 1) * pDiagForm s (fsKinCoeff c) Φ := h1
    _ = (((n + 1 : ℕ) : ℝ) + 1) * T0Form s (fsKinCoeff c) Φ := by rw [h2]
    _ ≤ (((n + 1 : ℕ) : ℝ) + 1)
          * (2 * chiSup ^ 2 * kinWord (n + 1) s Φ + 2 * winErrorQ s Φ) :=
        mul_le_mul_of_nonneg_left h3 (by positivity)
    _ = ((n : ℝ) + 2) * (2 * chiSup ^ 2 * kinWord (n + 1) s Φ + 2 * winErrorQ s Φ) := by
        rw [hcast]

/-- **The bridge with a `cnPlus`-weighted error.**  The window error is absorbed by the
`n₊`-count (FS's `bℓ⁻²Q_u`-gaps): `winErrorQ s Ψ ≤ B·cnPlus s Ψ` whenever
`B ≥ Σ_k(∂_kχ_s)²` pointwise. -/
theorem kinPWord_le_kinWord_cnPlus {n : ℕ} {s c B : ℝ} (hs : 0 < s) (hc : 0 ≤ c) (hB0 : 0 ≤ B)
    (hB : ∀ x : ℝ³, (∑ k : Fin 3, (fderiv ℝ (chiScale s) x (kcStdBasis k)) ^ 2) ≤ B)
    {Φ : X (n + 1) → ℝ} (hΦ : ContDiff ℝ ∞ Φ) (hsupp : tsupport Φ ⊆ abox (n + 1) s) :
    kinPWord s c Φ ≤ ((n : ℝ) + 2) *
      (2 * chiSup ^ 2 * kinWord (n + 1) s Φ + 2 * B * cnPlus s Φ) := by
  refine le_trans (kinPWord_le_kinWord hs hc hΦ hsupp) ?_
  have hw : winErrorQ s Φ ≤ B * cnPlus s Φ :=
    Work.SmallBoxBridge.Position.winErrorQ_le_cnPlus hs hB0 hB hΦ.continuous
  have hkey : 2 * chiSup ^ 2 * kinWord (n + 1) s Φ + 2 * winErrorQ s Φ
      ≤ 2 * chiSup ^ 2 * kinWord (n + 1) s Φ + 2 * (B * cnPlus s Φ) := by linarith
  have hnn : (0 : ℝ) ≤ (n : ℝ) + 2 := by positivity
  have h2 : ((n : ℝ) + 2) * (2 * chiSup ^ 2 * kinWord (n + 1) s Φ + 2 * (B * cnPlus s Φ))
      = ((n : ℝ) + 2) * (2 * chiSup ^ 2 * kinWord (n + 1) s Φ + 2 * B * cnPlus s Φ) := by ring
  rw [← h2]
  exact mul_le_mul_of_nonneg_left hkey hnn

/-- **The bridge in the shape of the smallbox assembly's energy**
`sboxE N s μ w w1 Φ = kinWord N s Φ + qLHSword N s μ w w1 Φ`: since `kinWord` is the first
summand, the bridge reads `kinPWord ≤ (N̂+1)(sboxE − qLHSword + window error)`. -/
theorem kinPWord_le_sboxE {n : ℕ} {s c μ : ℝ} (hs : 0 < s) (hc : 0 ≤ c)
    {w w1 : ℝ³ → ℝ³ → ℝ} {Φ : X (n + 1) → ℝ} (hΦ : ContDiff ℝ ∞ Φ)
    (hsupp : tsupport Φ ⊆ abox (n + 1) s) :
    kinPWord s c Φ ≤ ((n : ℝ) + 2) *
      (2 * chiSup ^ 2 * (sboxE (n + 1) s μ w w1 Φ - qLHSword (N := n + 1) s μ w w1 Φ)
        + 2 * winErrorQ s Φ) := by
  have he : 2 * chiSup ^ 2 * (sboxE (n + 1) s μ w w1 Φ - qLHSword (N := n + 1) s μ w w1 Φ)
      = 2 * chiSup ^ 2 * kinWord (n + 1) s Φ := by
    simp only [sboxE]
    ring
  rw [he]
  exact kinPWord_le_kinWord hs hc hΦ hsupp

end BoseGases
end Submission
