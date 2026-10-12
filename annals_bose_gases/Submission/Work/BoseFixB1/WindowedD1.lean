import ChallengeDeps
import Submission.Work.BoseFixB1.PerBoxNames
import Submission.Work.BoseFixB1.SharpCommutator
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1.WindowedD1` — the D1 vocabulary at a **general window**

FS's `lm:appbogolubov` (`final_v2.tex` l. 3762–3800) is stated for a general box `B` with a
general smooth cutoff `χ_B`: the modes of Bogoliubov's method are the *windowed exponentials*
`Q_B χ_B e^{−i⟪p,·⟫}`, the pairing is `A₂ = ½(2π)⁻³∫ĝω₁(p)(b_p†b_{-p}† + h.c.)dp`, and every
estimate consumes only `∫χ_B²` and `‖χ_B‖_∞²`.

The corpus's centred D1 chain (`Work.SmallBoxD1Integral`, `Work.BoseFixB1.SharpCommutator`,
`Work.MGFix`) is stated at the *fixed* window `chiScale s` (through `qMode s p`).  This module
names the same objects at an arbitrary window, so that the general statement of the chain can be
proved once and instantiated at the sliding window `χ_B = chiB ℓ d u`.

* `winModeRe s χ p`, `winModeIm s χ p` — the real and imaginary parts of the mean-free windowed
  exponential `Q_B(χ e^{−i⟪p,·⟫})` on the box `acube s` (the generalisation of
  `qModeRe s p`/`qModeIm s p` from `χ = chiScale s`);
* `winSlotForm s χ F Ψ` — the generalisation of `pDiagForm s F Ψ` (the `p`-diagonal slot form
  with the window `χ`);
* `winPairForm s h χ Ψ` — the generalisation of `q4PairWord` (the pairing word with the
  localised kernel `χ(x)χ(y)·wScaled s (g₀)(x−y)`);
* `winPairR s χ Ψ q` — the generalisation of `pairR` (the pair content of the two modes
  `winModeRe/Im`).
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped Topology Real BigOperators ENNReal

namespace Work.BoseFixB1

open _root_.BoseGases Submission.BoseGases

set_option autoImplicit false
set_option linter.unusedVariables false


/-- The mean-free windowed exponential at the box `acube s`: `χ z − (s³)⁻¹∫_{acube s}χ`
(i.e. `Q_B χ` for the constant mode `p = 0`; the general `p` case is `winModeRe/Im`). -/
noncomputable def winMean (s : ℝ) (χ : EuclideanSpace ℝ (Fin 3) → ℝ) (z : EuclideanSpace ℝ (Fin 3)) : ℝ :=
  χ z - (s ^ 3)⁻¹ * ∫ w in acube s, χ w

/-- **The real part of the mean-free windowed exponential** `Q_B(χ e^{−i⟪p,·⟫})`,
`χ(z)cos⟪p,z⟫ − (s³)⁻¹∫_{acube s}χ(w)cos⟪p,w⟫dw` (the generalisation of `qModeRe s p`). -/
noncomputable def winModeRe (s : ℝ) (χ : EuclideanSpace ℝ (Fin 3) → ℝ) (p z : EuclideanSpace ℝ (Fin 3)) : ℝ :=
  χ z * Real.cos (inner ℝ p z) - (s ^ 3)⁻¹ * ∫ w in acube s, χ w * Real.cos (inner ℝ p w)

/-- **The imaginary part of the mean-free windowed exponential**: with `winModeRe` it satisfies
`winModeRe s χ p z + I·winModeIm s χ p z = Q_B(χ e^{−i⟪p,·⟫})(z)`. -/
noncomputable def winModeIm (s : ℝ) (χ : EuclideanSpace ℝ (Fin 3) → ℝ) (p z : EuclideanSpace ℝ (Fin 3)) : ℝ :=
  - (χ z * Real.sin (inner ℝ p z)
      - (s ^ 3)⁻¹ * ∫ w in acube s, χ w * Real.sin (inner ℝ p w))

/-- **The windowed `p`-diagonal slot form** — the generalisation of `pDiagForm` to an arbitrary
window `χ`:

`Σ_i (2π)⁻³∫_p F‖p‖ (s³)⁻¹∫_{abox}‖∫_{acube s}χ(z)e^{−i⟪p,z⟫}·(Q_iΨ)(x_{i←z})dz‖²`

(the modes are the *plain* windowed exponentials applied to the `Q`-projected state, exactly as
in `tBdiagFormInd`). -/
noncomputable def winSlotForm (s : ℝ) (χ : EuclideanSpace ℝ (Fin 3) → ℝ) (F : ℝ → ℝ) {N : ℕ}
    (Ψ : X N → ℝ) : ℝ :=
  ∑ i : Fin N, ((2 * Real.pi) ^ 3)⁻¹ * ∫ p : EuclideanSpace ℝ (Fin 3), F ‖p‖ *
    ((s ^ 3)⁻¹ * ∫ x in abox N s,
      ‖∫ z in acube s, (χ z : ℂ) * Complex.exp (-(Complex.I * (inner ℝ p z : ℂ))) *
        ((aQ s i Ψ) (Function.update x i z) : ℂ)‖ ^ 2)

/-- **The windowed pairing word** `Σ_{i≠j}∫(P_iP_jΨ)(Q_jQ_iΨ)χ(x_i)χ(x_j)𝒲(x_i−x_j)` — the
generalisation of `q4PairWord` to an arbitrary window (`𝒲 = wScaled s (g₀)`). -/
noncomputable def winPairForm {N : ℕ} {v : EuclideanSpace ℝ (Fin 3) → ℝ}
    (s : ℝ) (h : ∃ w : EuclideanSpace ℝ (Fin 3) → ℝ, _root_.BoseGases.IsRadial w ∧
      _root_.BoseGases.IsScatteringSolution w v)
    (χ : EuclideanSpace ℝ (Fin 3) → ℝ) (Ψ : X N → ℝ) : ℝ :=
  ∑ p ∈ pairSet N, ∫ x in abox N s,
    (aP s p.1 (aP s p.2 Ψ) x) * (aQ s p.2 (aQ s p.1 Ψ) x) *
      (χ (x p.1) * χ (x p.2) * wScaled s (g0 v h) (x p.1 - x p.2))

/-- **The windowed pair content** at momentum `q`: `R_{u_q} + R_{v_q}` for the two modes
`winModeRe/Im` — the generalisation of `pairR s Ψ q`. -/
noncomputable def winPairR (s : ℝ) (χ : EuclideanSpace ℝ (Fin 3) → ℝ) {N : ℕ} (Ψ : X N → ℝ) (q : EuclideanSpace ℝ (Fin 3)) : ℝ :=
  (∫ x in abox N s, tauAnn s (winModeRe s χ q) Ψ x * tauDag s (winModeRe s χ q) Ψ x)
    + (∫ x in abox N s, tauAnn s (winModeIm s χ q) Ψ x * tauDag s (winModeIm s χ q) Ψ x)

/-- **The windowed kinetic content** at momentum `q`: `P_{u_q} + P_{v_q}` — the generalisation
of `modeP s (qModeRe s q) Ψ + modeP s (qModeIm s q) Ψ`. -/
noncomputable def winModeP (s : ℝ) (χ : EuclideanSpace ℝ (Fin 3) → ℝ) {N : ℕ} (Ψ : X N → ℝ) (q : EuclideanSpace ℝ (Fin 3)) : ℝ :=
  (∫ x in abox N s, (tauAnn s (winModeRe s χ q) Ψ x) ^ 2)
    + (∫ x in abox N s, (tauAnn s (winModeIm s χ q) Ψ x) ^ 2)

end Work.BoseFixB1
