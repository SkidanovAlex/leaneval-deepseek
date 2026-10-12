import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.SmallBoxKineticP
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The kinetic bridge — the definitions (SESSION-285)

The D1 kinetic word `kinPWord s c Φ = (2π)⁻³ ∫_p [‖p‖−c]₊²·(P_{u_p}+P_{v_p})(Φ)` is the
p-space transcription of FS's one-body operator `𝒯₀ = Σ_i Q_iχ_i F(√−Δ_i) χ_i Q_i` (with
`F = [·−c]₊²`).  The bridge transfers the D1 bound on `kinPWord` to the corpus's honest
position-space kinetic word `kinWord N s Φ = Σ_{i,k}∫_{abox N s}(∂_{ik}Φ)²`.

The chain has two halves:

* **the (c1) half (this chapter's new content)** — the *kernel identity*
  `(2π)⁻³∫_p F(‖p‖)·χ(x)χ(y)·e^{i⟪p,x−y⟫}dp = χ(x)χ(y)·K_F(x−y)` (`K_F = 𝓕⁻¹F`, the kernel
  of `χ·F(√−Δ)·χ`) and the identification of the corpus mode sum with the
  *windowed-exponential Fourier form* `(2π)⁻³∫_p F(‖p‖)‖⟨χ e^{−i⟪p,·⟫}, Ψ⟩‖²`
  (the second-quantization correspondence for `a†(g)a(g)`);
* **the position-space half** — `Σ_i⟨Q_iΨ, χ_iF(√−Δ_i)χ_iQ_iΨ⟩ ≤ kinWord + (window error)`,
  whose ingredients are closed in `Submission/Work/SmallBoxKinBridge.lean`
  (`fderiv_aQ_kcDir`, `kinWord_aQ_le`, `fderiv_mul_coord_sq_le`) and
  `Submission/Work/FourierDerivEnergy.lean` (`integral_fderiv_sq_eq_fourier`).

## Conventions

* `p`-Fourier convention: `kinFT u p = ∫_y e^{−i⟪p,y⟫}u(y)dy` (so that `kinFT u p = 𝓕 u ((2π)⁻¹•p)`
  for Mathlib's `𝓕`); the dual inversion is `(2π)⁻³∫_p F(‖p‖)e^{i⟪p,z⟫}dp`.
* `K_F` is *real* (the symbol is radial, so the sine part cancels); `kinKernelC` is its
  complex version `(2π)⁻³∫_p F(‖p‖)e^{i⟪p,z⟫}dp`, with `kinKernelC F z = (kinKernel F z : ℂ)`.
* `X N = Fin N → ℝ³`, `acube s = [−s/2,s/2]³`, `abox N s = (acube s)^N`, `chiScale s` the
  smooth bump scaled to the box (`∫ chiScale s = s³·…`, `chiScale s` compactly supported).
* `qMode s p = Q_B(χ_B e^{−i⟪p,·⟫})` (`SmallBoxPairMode`) — the mean-free windowed
  exponential; `boxOp 1 g` is `a†(1_B)a(g)` in the corpus's position-slot language
  (`SmallBoxTauComm`), so `modeP s g Ψ = (s³)⁻¹∫‖a†(1_B)a(g)Ψ‖²`.
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

/-! ## 1 The `p`-convention Fourier transform and the kernel `K_F` -/

/-- The `p`-convention Fourier transform on `ℝ³`: `kinFT u p = ∫_y e^{−i⟪p,y⟫}u(y)dy`.
This is Mathlib's `𝓕 u` at the frequency `(2π)⁻¹ • p` (`kinFT_eq_fourier`). -/
noncomputable def kinFT (u : ℝ³ → ℂ) (p : ℝ³) : ℂ :=
  ∫ y : ℝ³, Complex.exp (-(Complex.I * (inner ℝ p y : ℂ))) * u y

/-- The windowed `p`-mode of a one-slot function: `∫_y χ(y)e^{−i⟪p,y⟫}u(y)dy`
(= `kinFT (χ•u) p`). -/
noncomputable def winFT (χ : ℝ³ → ℝ) (u : ℝ³ → ℝ) (p : ℝ³) : ℂ :=
  ∫ y : ℝ³, (χ y : ℂ) * Complex.exp (-(Complex.I * (inner ℝ p y : ℂ))) * u y

/-- **The kernel `K_F = 𝓕⁻¹F` of the radial symbol `p ↦ F(‖p‖)`**, in the `p`-convention:
`kinKernel F z = (2π)⁻³∫_p F(‖p‖)cos⟪p,z⟫dp`.  This is the kernel of the operator
`F(√−Δ)`: `(F(√−Δ)u)(x) = ∫_y kinKernel F (x−y)u(y)dy`. -/
noncomputable def kinKernel (F : ℝ → ℝ) (z : ℝ³) : ℝ :=
  ((2 * π) ^ 3)⁻¹ * ∫ p : ℝ³, F ‖p‖ * Real.cos (inner ℝ p z)

/-- The complex form of the kernel: `(2π)⁻³∫_p F(‖p‖)e^{i⟪p,z⟫}dp` (equal to
`kinKernel F z` cast to `ℂ`, the sine part vanishing by oddness). -/
noncomputable def kinKernelC (F : ℝ → ℝ) (z : ℝ³) : ℂ :=
  ((((2 * π) ^ 3)⁻¹ : ℝ) : ℂ) * ∫ p : ℝ³,
    (F ‖p‖ : ℂ) * Complex.exp (Complex.I * (inner ℝ p z : ℂ))

/-- The *windowed kernel* of `χ·F(√−Δ)·χ`: `χ(x)χ(y)K_F(x−y)`. -/
noncomputable def winKernel (χ : ℝ³ → ℝ) (F : ℝ → ℝ) (x y : ℝ³) : ℝ :=
  χ x * χ y * kinKernel F (x - y)

/-- The *windowed-exponential form* of the symbol at the diagonal pair `(x,y)`:
`(2π)⁻³∫_p F(‖p‖)·χ(x)χ(y)·cos⟪p,x−y⟫dp` — the left side of the (c1) identity. -/
noncomputable def winExpansion (χ : ℝ³ → ℝ) (F : ℝ → ℝ) (x y : ℝ³) : ℝ :=
  ((2 * π) ^ 3)⁻¹ * ∫ p : ℝ³, F ‖p‖ * (χ x * χ y * Real.cos (inner ℝ p (x - y)))

/-- The *windowed mode form*: the quadratic form of the operator `χ·F(√−Δ)·χ` written as the
`p`-integral of the squared windowed modes `χ(y)e^{i⟪p,y⟫}`,
`(2π)⁻³∫_p F(‖p‖)‖kinFT (χ·u) p‖²`. -/
noncomputable def winModeForm (χ : ℝ³ → ℝ) (F : ℝ → ℝ) (u : ℝ³ → ℝ) : ℝ :=
  ((2 * π) ^ 3)⁻¹ * ∫ p : ℝ³, F ‖p‖ * ‖kinFT (fun y => (χ y : ℂ) * u y) p‖ ^ 2

/-! ## 2 The corpus mode language: `boxOp` with a complex kernel, and the mode content -/

/-- `boxOp` with a complex kernel `γ` (the complexification of `boxOp s 1 γ` needed to write
`P_{u_p} + P_{v_p}` as one square): `boxOpC s γ Ψ x = Σ_i ∫_z γ(z)Ψ(x_{i←z})dz`. -/
noncomputable def boxOpC (s : ℝ) {N : ℕ} (γ : ℝ³ → ℂ) (Ψ : X N → ℝ) (x : X N) : ℂ :=
  ∑ i : Fin N, ∫ z in acube s, γ z * (Ψ (Function.update x i z) : ℂ)

/-- The slot-`i` amplitude of the corpus mode `qMode s p`:
`pSlotAmp s p Ψ i x = ∫_z qMode s p z · Ψ(x_{i←z})dz`. -/
noncomputable def pSlotAmp (s : ℝ) (p : ℝ³) {N : ℕ} (Ψ : X N → ℝ) (i : Fin N)
    (x : X N) : ℂ :=
  ∫ z in acube s, qMode s p z * (Ψ (Function.update x i z) : ℂ)

/-- **The corpus's per-`p` mode content** `P_{u_p} + P_{v_p}` of `SmallBoxKineticP`, written
as the norm-square of the sum of slot amplitudes:
`(s³)⁻¹∫_{abox}‖Σ_i pSlotAmp s p Ψ i x‖²`. -/
noncomputable def pModeContent (s : ℝ) (p : ℝ³) {N : ℕ} (Ψ : X N → ℝ) : ℝ :=
  (s ^ 3)⁻¹ * ∫ x in abox N s, ‖∑ i : Fin N, pSlotAmp s p Ψ i x‖ ^ 2

/-- The DIAGONAL (one-body) part of the corpus mode content: the `i = j` terms
`(s³)⁻¹Σ_i∫_{abox}‖pSlotAmp s p Ψ i x‖²`. -/
noncomputable def pModeDiagonal (s : ℝ) (p : ℝ³) {N : ℕ} (Ψ : X N → ℝ) : ℝ :=
  (s ^ 3)⁻¹ * ∑ i : Fin N, ∫ x in abox N s, ‖pSlotAmp s p Ψ i x‖ ^ 2

/-- The corpus's p-space kinetic word in the mode form with symbol `F` (i.e.
`(2π)⁻³∫_p F(‖p‖)·(P_{u_p}+P_{v_p})`), the generalisation of `kinPWord` used in the bridge. -/
noncomputable def pModeForm (s : ℝ) (F : ℝ → ℝ) {N : ℕ} (Ψ : X N → ℝ) : ℝ :=
  ((2 * π) ^ 3)⁻¹ * ∫ p : ℝ³, F ‖p‖ * pModeContent s p Ψ

/-- The diagonal (one-body) mode form: the sum over slots of the slot mode forms
`Σ_i (2π)⁻³∫_p F(‖p‖)·(s³)⁻¹∫_{abox}‖pSlotAmp s p Ψ i x‖²` — the shape of `T0Form`, so that
`pDiagForm = T0Form` is a pointwise (per-slot) statement with no sum/integral interchange. -/
noncomputable def pDiagForm (s : ℝ) (F : ℝ → ℝ) {N : ℕ} (Ψ : X N → ℝ) : ℝ :=
  ∑ i : Fin N, ((2 * π) ^ 3)⁻¹ * ∫ p : ℝ³, F ‖p‖ *
    ((s ^ 3)⁻¹ * ∫ x in abox N s, ‖pSlotAmp s p Ψ i x‖ ^ 2)

/-- The one-body windowed kinetic form of `Ψ`: `Σ_i ∫_x (χ(x_i)Ψ(x))·(K_F-convolution in the
`i`-th slot)`, the quadratic form of `Σ_i Q_iχ_iF(√−Δ_i)χ_iQ_i` (with the outer `χ` inside the
slot-`i` convolution). -/
noncomputable def oneBodyWinForm (s : ℝ) (χ : ℝ³ → ℝ) (F : ℝ → ℝ) {N : ℕ} (Ψ : X N → ℝ) : ℝ :=
  ∑ i : Fin N, ∫ x in abox N s, χ (x i) * Ψ x *
    (∫ y : ℝ³, kinKernel F (x i - y) * χ y * Ψ (Function.update x i y))

/-! ## 3 The unprojected slot amplitude, the `𝒯₀` form and the window error -/

/-- The slot-`i` amplitude of the *unprojected* windowed exponential `χ e^{−i⟪p,·⟫}`:
`rawSlotAmp s p Ψ i x = ∫_z χ(z)e^{−i⟪p,z⟫}Ψ(x_{i←z})dz`, the `i`-th fibre's windowed
`p`-Fourier transform.  (It is independent of `x i`.) -/
noncomputable def rawSlotAmp (s : ℝ) (p : ℝ³) {N : ℕ} (Ψ : X N → ℝ) (i : Fin N)
    (x : X N) : ℂ :=
  ∫ z in acube s, (chiScale s z : ℂ) *
    Complex.exp (-(Complex.I * (inner ℝ p z : ℂ))) * (Ψ (Function.update x i z) : ℂ)

/-- The diagonal mode form built from the *unprojected* windowed exponentials. -/
noncomputable def rawDiagForm (s : ℝ) (F : ℝ → ℝ) {N : ℕ} (Ψ : X N → ℝ) : ℝ :=
  ((2 * π) ^ 3)⁻¹ * ∫ p : ℝ³, F ‖p‖ *
    ((s ^ 3)⁻¹ * ∑ i : Fin N, ∫ x in abox N s, ‖rawSlotAmp s p Ψ i x‖ ^ 2)

/-- **`𝒯₀`** — the one-body kinetic operator `Σ_i Q_iχ_iF(√−Δ_i)χ_iQ_i`, written in the
*windowed-exponential Fourier form* (the second-quantization correspondence of
`Submission/Work/SmallBoxBridge/Defs.lean`'s header): the `p`-integral of the squared windowed
modes of the `Q_i`-projected `i`-th fibres. -/
noncomputable def T0Form (s : ℝ) (F : ℝ → ℝ) {N : ℕ} (Ψ : X N → ℝ) : ℝ :=
  ∑ i : Fin N, ((2 * π) ^ 3)⁻¹ * ∫ p : ℝ³, F ‖p‖ *
    ((s ^ 3)⁻¹ * ∫ x in abox N s, ‖rawSlotAmp s p (aQ s i Ψ) i x‖ ^ 2)

/-- The window-derivative error of the bridge: `Σ_i ∫_{abox}|∇χ(x_i)|²Ψ²`. -/
noncomputable def winError (s : ℝ) {N : ℕ} (Ψ : X N → ℝ) : ℝ :=
  ∑ i : Fin N, ∫ x in abox N s,
    (∑ k : Fin 3, (fderiv ℝ (chiScale s) (x i) (kcStdBasis k)) ^ 2) * (Ψ x) ^ 2

/-- The window-derivative error in its `Q_i`-projected form,
`Σ_i ∫_{abox}|∇χ(x_i)|²(aQ s i Ψ)²` — the shape the Leibniz step of the bridge actually
produces (`fderiv_mul_coord_sq_le` applied to `χ(x_i)·(aQ s i Ψ)`).  Note `winErrorQ ≤ winError`
is FALSE in general (the mean-free part of a fibre can be large exactly where `|∇χ|` is
supported), so the bridge carries `winErrorQ`. -/
noncomputable def winErrorQ (s : ℝ) {N : ℕ} (Ψ : X N → ℝ) : ℝ :=
  ∑ i : Fin N, ∫ x in abox N s,
    (∑ k : Fin 3, (fderiv ℝ (chiScale s) (x i) (kcStdBasis k)) ^ 2) * (aQ s i Ψ x) ^ 2

end BoseGases
end Submission
