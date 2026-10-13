/-
Copyright: work module for the Elgindi finite-time singularity project.

# The heavy-weight two-dimensional mixed-slot interpolation: interfaces

This module fixes the *interfaces* used by the reduction of the outer `z`-integrability of the
mixed slot `D_z∂_θu = z∂_z∂_θu` of an `AeData` datum
(`Work.FTS.EllipticEst.AeCrux.AeVGlobalFin2`) to the paper's two-dimensional Agmon
interpolation in the form in which the workspace's flat-Fourier machinery provides it.

## The two propositions

* `FlatHeavy` — the **flat, shifted** heavy-weight mixed-slot finiteness.  For every shift
  `b : ℝ` and every datum `u` of class `C²` on the open strip `ℝ × (0,π/2)` whose end-point
  *values* vanish, the `σ_η`-weighted `(1,1)`-slot of the shifted operator `∂_t - b` is
  `∫⁻`-finite, provided the three `σ_η`-weighted *diagonal* slots
  (`(∂_t-b)u`, `(∂_t-b)²u`, `∂_θ²u`) are integrable on the strip.
  Here `σ_η = sin(2θ)^{-η}`, `η = 99/100`.
  This is the statement of the tree's `Work.FTS.EllSol.Shift2Flat.mixedSlotFiniteness` (the
  recorded node; its file carries a `sorry`), and its route is documented, hand-verified and
  ingredient-complete in
  `Submission/Work/FTS/EllSol/Shift2Flat/NOTES_mixedSlot_route.md` (truncation in `t` + the
  complex angular Agmon `Trunc.curlAgmon` per frequency + the shifted Plancherel identities
  `ShiftFT.plancherelShift` + Cauchy–Schwarz in the frequency + Fatou).

* `OmHeavy` — the **`Ω`-weighted** heavy-weight mixed-slot finiteness (`b = 0`).  Same, with
  the flat measure replaced by the logarithmic weight `Ω(t) = (1+e^t)^4 e^{-3t}` (the paper's
  `Wt`); it is the exact form in which the `(s,θ)`-picture of the Euler datum appears.

`OmHeavy_of_FlatHeavy` (in the sibling module `HeavyFlat.OmOfFlat`) deduces the second from the
first by the decomposition `Ω(t) = Σ_{k<5} C(4,k)·e^{2 b_k t}`, `b_k = (k-3)/2`, and the identity
`e^{b t}∂_tg = (∂_t - b)(e^{b t}g)`.

Nothing in this file is a proof obligation.
-/
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.StraightDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllSol.HeavyFlat

noncomputable section

open MeasureTheory Set
open scoped Real Topology ENNReal

set_option autoImplicit false

/-- The logarithmic radial weight `Ω(t) = (1+e^t)^4 e^{-3t}`; under `z = e^t` it is exactly
`w(z)^2 · z`, i.e. `w(e^t)^2 dz`. -/
def omw (t : ℝ) : ℝ := (1 + Real.exp t) ^ 4 * Real.exp (-(3 * t))

/-- The heavy angular weight `σ_η(θ) = sin(2θ)^{-η}`. -/
def sigE (θ : ℝ) : ℝ := (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))

/-- `omw t = w (exp t)^2 * exp t`. -/
theorem omw_eq_w_sq_mul (t : ℝ) :
    omw t = (Work.Spaces.w (Real.exp t)) ^ 2 * Real.exp t := by
  have hpos : 0 < Real.exp t := Real.exp_pos t
  have h3 : Real.exp (-(3 * t)) = (Real.exp t)⁻¹ ^ 3 := by
    rw [Real.exp_neg, show (3 : ℝ) * t = (((3 : ℕ) : ℝ)) * t by push_cast; ring, Real.exp_nat_mul,
      inv_pow]
  rw [omw, Work.Spaces.w, h3]
  field_simp [hpos.ne']

/-- `sigE` is the workspace's `sEta` / `thEta`. -/
theorem sigE_eq_sEta (θ : ℝ) : sigE θ = Work.FTS.EllipticEst.sEta θ := rfl

/-- **The flat shifted heavy-weight mixed-slot finiteness.** -/
def FlatHeavy : Prop :=
  ∀ (b : ℝ) (u : ℝ → ℝ → ℝ),
    ContDiffOn ℝ 2 (Function.uncurry u) (Set.univ ×ˢ Set.Ioo 0 (Real.pi / 2)) →
    (∀ t : ℝ, u t 0 = 0) → (∀ t : ℝ, u t (Real.pi / 2) = 0) →
    IntegrableOn (fun p : ℝ × ℝ => (Work.Spaces.pz u p.1 p.2 - b * u p.1 p.2) ^ 2
      * sigE p.2) (Set.univ ×ˢ Work.Spaces.Iθ) →
    IntegrableOn (fun p : ℝ × ℝ => (Work.Spaces.pz (Work.Spaces.pz u) p.1 p.2
      - 2 * b * Work.Spaces.pz u p.1 p.2 + b ^ 2 * u p.1 p.2) ^ 2 * sigE p.2)
      (Set.univ ×ˢ Work.Spaces.Iθ) →
    IntegrableOn (fun p : ℝ × ℝ => (Work.Spaces.pth (Work.Spaces.pth u) p.1 p.2) ^ 2
      * sigE p.2) (Set.univ ×ˢ Work.Spaces.Iθ) →
    ∫⁻ p in Set.univ ×ˢ Work.Spaces.Iθ, ENNReal.ofReal
      ((Work.Spaces.pth (Work.Spaces.pz u) p.1 p.2 - b * Work.Spaces.pth u p.1 p.2) ^ 2
        * sigE p.2) < ⊤

/-- **The `Ω`-weighted heavy-weight mixed-slot finiteness** (on the strip `ℝ × Iθ`). -/
def OmHeavy : Prop :=
  ∀ (g : ℝ → ℝ → ℝ),
    ContDiffOn ℝ 2 (Function.uncurry g) (Set.univ ×ˢ Set.Ioo 0 (Real.pi / 2)) →
    (∀ t : ℝ, g t 0 = 0) → (∀ t : ℝ, g t (Real.pi / 2) = 0) →
    IntegrableOn (fun p : ℝ × ℝ => (Work.Spaces.pz g p.1 p.2) ^ 2 * omw p.1 * sigE p.2)
      (Set.univ ×ˢ Work.Spaces.Iθ) →
    IntegrableOn (fun p : ℝ × ℝ => (Work.Spaces.pz (Work.Spaces.pz g) p.1 p.2) ^ 2
      * omw p.1 * sigE p.2) (Set.univ ×ˢ Work.Spaces.Iθ) →
    IntegrableOn (fun p : ℝ × ℝ => (Work.Spaces.pth (Work.Spaces.pth g) p.1 p.2) ^ 2
      * omw p.1 * sigE p.2) (Set.univ ×ˢ Work.Spaces.Iθ) →
    ∫⁻ p in Set.univ ×ˢ Work.Spaces.Iθ, ENNReal.ofReal ((Work.Spaces.pth (Work.Spaces.pz g) p.1 p.2) ^ 2
      * omw p.1 * sigE p.2) < ⊤

end

end Work.FTS.EllSol.HeavyFlat
