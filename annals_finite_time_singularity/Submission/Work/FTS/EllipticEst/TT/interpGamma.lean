import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllipticEst.TT.WeakDefs
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.Defs
import Submission.Work.Blocks.interpol_mixed_box_proof
import Submission.Work.Blocks.interp_lin_of_box
import Submission.Work.FTS.EllipticEst.interpol_defs
import Submission.Work.FTS.EllipticEst.hardy_shift_two_same_weight
import Submission.Work.FTS.EllipticEst.TT.interpGammaDefs
import Submission.Work.FTS.EllipticEst.TT.interpGamma_slots
import Submission.Work.FTS.EllipticEst.TT.interpGamma_core

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.TT

/-!
# `TT.interpGamma`

The interpolation estimate with the **light** angular weight
`σ_a = sin(2θ)^{2-γ(α)}` (`2 - γ = 1 - α/10 ∈ (0,1)`) on the mixed derivative `D_z∂_θG` and the
**heavy** weights `σ_η = sin(2θ)^{-η}` (`η = 99/100`) on the three `ℋ⁰`-slots
`D_z²G`, `∂_θ²G`, `D_zG` of the right-hand side.

The proof is an assembly of two analytic inputs:

* `interpGamma_core` (`Submission/Work/FTS/EllipticEst/TT/interpGamma_core.lean`) — the analytic
  core `Xint ≤ C (√(DDint · TTint) + HkSq α 0 (DzIter 1 G))`; the naive core without the last slot
  is *false* (see `NOTES_interpGamma.md` §2, the affine counterexample);
* `interpGamma_slots` (`Submission/Work/FTS/EllipticEst/TT/interpGamma_slots.lean`) — the
  comparison of the two light-weight slots with the heavy-weight ones,
  `TTint ≤ HkSq α 0 (pthIter 2 G)` and
  `DDint ≤ 2 HkSq α 0 (DzIter 2 G) + 18 HkSq α 0 (DzIter 1 G)`,
  from `σ_a ≤ σ_η`, `|b| ≤ 3` and `HkMem`.

The arithmetic of the assembly is `interpGamma_of_core` below: with `2√x√y ≤ x + y`,
`α⁴ ≤ α²` for `α ≤ 1`, and the slot bounds, one gets
`α² Xint ≤ 10 C (α⁴ HkSq α 0 (DzIter 2 G) + HkSq α 0 (pthIter 2 G) + α² HkSq α 0 (DzIter 1 G))`,
whence the target with constant `10 C`.

## The analytic core: any of the following equivalent sources may be substituted

The *only* remaining input of `interpGamma` is the core `hcore` of `interpGamma_of_core`.
Equivalent (or stronger) statements already in the workspace, all with the *same* hypothesis
list, are

* `Work.FTS.EllipticEst.TT.interpGamma_core` — the delegated one, consumed below;
* `Work.FTS.EllipticEst.Cores.interpGammaBrick` — identical conclusion (its extra slot is written
  as `∫ z in Iz, ∫ θ in Iθ, (Dz G z θ)^2 * (w z)^2 * sin(2θ)^(-eta)`, which is `HkSq α 0
  (DzIter 1 G)` by `HkSq_zero_eq_integral` and `DzIter 1 G = Dz G`);
* the strictly weaker `σ_η`-slot variant `Work.FTS.EllipticEst.TT.interpGamma_core_eta`
  (`Xint ≤ C(√(NNeta G · HkSq α 0 (pthIter 2 G)) + HkSq α 0 (DzIter 1 G))`, with
  `NNeta = ∫∫(Dz (Dz G) + b · Dz G)^2 w^2 σ_η`): swapping it in needs only the finite pointwise
  comparison `NNeta G ≤ 2 HkSq α 0 (DzIter 2 G) + 18 HkSq α 0 (DzIter 1 G)` (AM–GM plus
  `|b| ≤ 3` plus `HkSq_zero_eq_integral`), i.e. the argument of `interpGamma_slots` restricted
  to the heavy weight, in place of `hslot`.

The mathematical content of the core (and its single unresolved analytic point) is recorded in
`NOTES_interpGamma_core.md`: the `θ`-integration by parts leaves the endpoint ("jump") term
`Φ = -a ∫ cos(2θ) sin(2θ)^{a-1} m'(θ) dθ`, `m(θ) = ∫_z w² (D_zG(z,θ))² dz`, and this term has
to be priced by `HkSq α 0 (DzIter 1 G) = ∫ σ_η m`.

## State of the crux (shared route, 2026-10-06)

The `m`-level reduction of the core is now understood (see
`H2W/AngBW/NOTES_lightFlatCore3_route.md`, `Cores/NOTES_interpGammaBrick.md` §2ter).  With
`f = D_zG`, `ρ = w²`, `σ = σ_a`, `p = L_zG`, `q = ∂_θ²G` and the `θ`-functions
`m(θ) = ∫_z ρ f²`, `Ψ(θ) = ∫_z ρ (∂_θf)²`, `G(θ) = ∫_z ρ f (∂_θ²f) = -∫_z ρ p q`, one has

* `m'' = 2(Ψ + G)`, `|G| ≤ √(f₁ f₂)` pointwise with `f₁ = ∫_z ρ p²`, `f₂ = ∫_z ρ q²`;
* `m ≤ 16 f₁` (radial Hardy twice; `ZCuts/zHardy_compact`, `zHardy_sq_le_cinf`);
* `∫σΨ = Xint`, `∫σf₁ = DDint`, `∫σf₂ = TTint`, `∫σm = ∫∫ρσ_a (D_zG)² ≤ HkSq α 0 (DzIter 1 G)`;
* the `θ`-IBP together with the `z`-adjoint gives exactly `Xint = P + Edge` with
  `P = -∫σG` (whence `|P| ≤ √(DDint·TTint)`), and the *regularised* endpoint term
  `Edge = ∫_θ W(θ)(m01(θ) - m(θ))dθ`, `W = -σ''/2 ≥ 0`, `m01 = lim_{0⁺}m` on `(0,π/4)` and
  `lim_{(π/2)⁻}m` on `(π/4,π/2)`;
* hence the core is **equivalent** to `Edge ≤ K(√(DDint·TTint) + HkSq α 0 (DzIter 1 G))`.

Proved bricks on this route: `Cores.sliceInterpJump` (the 1-D jump interpolation
`∫(Φ')²σ_a ≤ C(√(∫Φ²σ_a∫(Φ'')²σ_a) + ∫Φ²σ_η)` with an **α-uniform** constant —
its proof produces `max 1 (max (16384+4√3) (16384+52K²+4√3L))` from a fixed cutoff),
`Cores.sliceInterpVanishing` (the vanishing-trace case, constant `1`), `slicePriceBound`
(the endpoint price bound `∫ρc₀² ≤ (A/ε^{1+a})Cl + Bε^{1-a}Xl`), and the radial bricks above.

**The single remaining gap** is that `Edge` needs the *α-uniform* form of this 1-D input at the
`m`-level: the chain via the slicewise price bound loses `(1-a)^{-1/2} = √(10/α)`, and closing it
requires the quantitative use of `TTint = ∫σf₂ < ∞` (the dichotomy "`f₂ < ∞` forces
`m(θ) - m(0⁺) = O(θ^s)`, `s > 1-a`").  The tensor case (`G = A(z)η(θ)`) reduces to the sharp
1-D statement `∫σ(η')² ≤ K(∫ση² + √(∫ση²∫σ(η'')²))` with `K` universal, which the proof of
`Cores.sliceInterpJump` already produces (its intermediate `hMfinal`), and which is numerically
true with `K ≈ 1.4`.
-/

/-- `HkSq α 0 (DzIter 1 G)` is the explicit `σ_η`-slot of `Dz G`: the identity that lets any
core stated with `∫ z in Iz, ∫ θ in Iθ, (Dz G z θ)^2 (w z)^2 sin(2θ)^{-η}` on its right-hand
side (e.g. `Work.FTS.EllipticEst.Cores.interpGammaBrick`) be consumed by `interpGamma_of_core`
below. -/
theorem HkSq_DzIter_one_eq (α : ℝ) (G : ℝ → ℝ → ℝ) :
    Work.Spaces.HkSq α 0 (Work.Spaces.DzIter 1 G)
      = ∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
          (Work.Spaces.Dz G z θ) ^ 2 * (Work.Spaces.w z) ^ 2
            * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) := by
  rw [Work.FTS.EllipticEst.TT.HkSq_zero_eq_integral]
  simp only [Work.Spaces.DzIter_succ, Work.Spaces.DzIter_zero, Nat.zero_add]

/-- **Assembly.** `interpGamma` follows from the analytic core `hcore` and the slot comparison
`hslot` by elementary arithmetic in `α`. -/
theorem interpGamma_of_core
    (hcore : ∃ C : ℝ, 0 < C ∧
      ∀ (α : ℝ) (G : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 / 4 →
        Work.FTS.EllipticEst.SmoothOpen G →
        (∀ z : ℝ, G z 0 = 0) → (∀ z : ℝ, G z (Real.pi / 2) = 0) →
        Work.Spaces.HkMem α 0 (Work.Spaces.DzIter 2 G) →
        Work.Spaces.HkMem α 0 (Work.Spaces.pthIter 2 G) →
        Work.Spaces.HkMem α 0 (Work.Spaces.DzIter 1 G) →
        MeasureTheory.IntegrableOn (fun z : ℝ => ∫ θ in Work.Spaces.Iθ,
          (Work.Spaces.Dz (Work.Spaces.pth G) z θ) ^ 2 * (Work.Spaces.w z) ^ 2
            * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α)) Work.Spaces.Iz →
        Work.FTS.EllipticEst.TT.Xint α G
          ≤ C * (Real.sqrt (Work.FTS.EllipticEst.TT.DDint α G
                * Work.FTS.EllipticEst.TT.TTint α G)
              + Work.Spaces.HkSq α 0 (Work.Spaces.DzIter 1 G)))
    (hslot : ∀ (α : ℝ) (G : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 →
      Work.FTS.EllipticEst.SmoothOpen G →
      Work.Spaces.HkMem α 0 (Work.Spaces.DzIter 2 G) →
      Work.Spaces.HkMem α 0 (Work.Spaces.pthIter 2 G) →
      Work.Spaces.HkMem α 0 (Work.Spaces.DzIter 1 G) →
      Work.FTS.EllipticEst.TT.TTint α G ≤ Work.Spaces.HkSq α 0 (Work.Spaces.pthIter 2 G)
        ∧ Work.FTS.EllipticEst.TT.DDint α G
            ≤ 2 * Work.Spaces.HkSq α 0 (Work.Spaces.DzIter 2 G)
              + 18 * Work.Spaces.HkSq α 0 (Work.Spaces.DzIter 1 G)) :
    ∃ C : ℝ, 0 < C ∧
    ∀ (α : ℝ) (G : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 / 4 →
      Work.FTS.EllipticEst.SmoothOpen G →
      (∀ z : ℝ, G z 0 = 0) → (∀ z : ℝ, G z (Real.pi / 2) = 0) →
      Work.Spaces.HkMem α 0 (Work.Spaces.DzIter 2 G) →
      Work.Spaces.HkMem α 0 (Work.Spaces.pthIter 2 G) →
      Work.Spaces.HkMem α 0 (Work.Spaces.DzIter 1 G) →
      MeasureTheory.IntegrableOn (fun z : ℝ => ∫ θ in Work.Spaces.Iθ,
        (Work.Spaces.Dz (Work.Spaces.pth G) z θ) ^ 2 * (Work.Spaces.w z) ^ 2
          * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α)) Work.Spaces.Iz →
      α ^ 4 * Work.Spaces.L2Sq (fun z θ => Work.Spaces.Dz (Work.Spaces.pth G) z θ
            * (Real.sin (2 * θ)) ^ ((2 - Work.Spaces.gam α) / 2) * Work.Spaces.w z)
        ≤ C * α ^ 2 * (α ^ 4 * Work.Spaces.HkSq α 0 (Work.Spaces.DzIter 2 G)
            + Work.Spaces.HkSq α 0 (Work.Spaces.pthIter 2 G)
            + α ^ 2 * Work.Spaces.HkSq α 0 (Work.Spaces.DzIter 1 G)) := by
  obtain ⟨C₀, hC₀pos, hcore'⟩ := hcore
  refine ⟨10 * C₀, by positivity, ?_⟩
  intro α G hα hα4 hS h0 h1 h2 h3 h4 h5
  have hα1 : α ≤ 1 := by linarith
  have hc := hcore' α G hα hα4 hS h0 h1 h2 h3 h4 h5
  obtain ⟨hTT, hDD⟩ := hslot α G hα hα1 hS h2 h3 h4
  -- nonnegativity of the three heavy-weight slots
  have hA0 : 0 ≤ Work.Spaces.HkSq α 0 (Work.Spaces.DzIter 2 G) :=
    Work.Spaces.HkSq_nonneg α 0 (Work.Spaces.DzIter 2 G)
  have hA1 : 0 ≤ Work.Spaces.HkSq α 0 (Work.Spaces.pthIter 2 G) :=
    Work.Spaces.HkSq_nonneg α 0 (Work.Spaces.pthIter 2 G)
  have hA2 : 0 ≤ Work.Spaces.HkSq α 0 (Work.Spaces.DzIter 1 G) :=
    Work.Spaces.HkSq_nonneg α 0 (Work.Spaces.DzIter 1 G)
  -- nonnegativity of the two light-weight slots
  have hTT0 : 0 ≤ Work.FTS.EllipticEst.TT.TTint α G := by
    rw [Work.FTS.EllipticEst.TT.TTint]
    refine MeasureTheory.integral_nonneg_of_ae ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ici] with z _
    refine MeasureTheory.integral_nonneg_of_ae ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ hθ
    exact mul_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _))
      (Work.FTS.EllipticEst.TT.sigA_nonneg α θ hθ)
  have hDD0 : 0 ≤ Work.FTS.EllipticEst.TT.DDint α G := by
    rw [Work.FTS.EllipticEst.TT.DDint]
    refine MeasureTheory.integral_nonneg_of_ae ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ici] with z _
    refine MeasureTheory.integral_nonneg_of_ae ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ hθ
    exact mul_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _))
      (Work.FTS.EllipticEst.TT.sigA_nonneg α θ hθ)
  have hα2nn : (0 : ℝ) ≤ α ^ 2 := by positivity
  have hα4nn : (0 : ℝ) ≤ α ^ 4 := by positivity
  have hα2le1 : α ^ 2 ≤ 1 := by nlinarith
  have hα4le2 : α ^ 4 ≤ α ^ 2 := by
    nlinarith [mul_le_mul_of_nonneg_right hα2le1 hα2nn]
  -- AM–GM in `α`: `α² √(DD·TT) = √(α⁴DD)·√(TT) ≤ (α⁴DD + TT)/2`.
  have hAM : α ^ 2 * Real.sqrt (Work.FTS.EllipticEst.TT.DDint α G
      * Work.FTS.EllipticEst.TT.TTint α G)
      ≤ (α ^ 4 * Work.FTS.EllipticEst.TT.DDint α G
          + Work.FTS.EllipticEst.TT.TTint α G) / 2 := by
    have hx : (0 : ℝ) ≤ α ^ 4 * Work.FTS.EllipticEst.TT.DDint α G :=
      mul_nonneg hα4nn hDD0
    have hsq : α ^ 2 * Real.sqrt (Work.FTS.EllipticEst.TT.DDint α G
          * Work.FTS.EllipticEst.TT.TTint α G)
        = Real.sqrt (α ^ 4 * Work.FTS.EllipticEst.TT.DDint α G)
          * Real.sqrt (Work.FTS.EllipticEst.TT.TTint α G) := by
      rw [Real.sqrt_mul hDD0]
      rw [show α ^ 4 = (α ^ 2) ^ 2 by ring]
      rw [Real.sqrt_mul (show (0 : ℝ) ≤ (α ^ 2) ^ 2 by positivity), Real.sqrt_sq hα2nn]
      ring
    rw [hsq]
    nlinarith [sq_nonneg (Real.sqrt (α ^ 4 * Work.FTS.EllipticEst.TT.DDint α G)
        - Real.sqrt (Work.FTS.EllipticEst.TT.TTint α G)),
      Real.sq_sqrt hx, Real.sq_sqrt hTT0,
      Real.sqrt_nonneg (α ^ 4 * Work.FTS.EllipticEst.TT.DDint α G),
      Real.sqrt_nonneg (Work.FTS.EllipticEst.TT.TTint α G)]
  -- combine the AM–GM with the two slot bounds
  have hAM2 : α ^ 2 * Real.sqrt (Work.FTS.EllipticEst.TT.DDint α G
        * Work.FTS.EllipticEst.TT.TTint α G)
      ≤ (α ^ 4 * (2 * Work.Spaces.HkSq α 0 (Work.Spaces.DzIter 2 G)
            + 18 * Work.Spaces.HkSq α 0 (Work.Spaces.DzIter 1 G))
          + Work.Spaces.HkSq α 0 (Work.Spaces.pthIter 2 G)) / 2 := by
    have h2 : α ^ 4 * Work.FTS.EllipticEst.TT.DDint α G
        ≤ α ^ 4 * (2 * Work.Spaces.HkSq α 0 (Work.Spaces.DzIter 2 G)
            + 18 * Work.Spaces.HkSq α 0 (Work.Spaces.DzIter 1 G)) :=
      mul_le_mul_of_nonneg_left hDD hα4nn
    linarith [hAM, h2, hTT]
  -- the key numerical inequality
  have hkey : α ^ 2 * Real.sqrt (Work.FTS.EllipticEst.TT.DDint α G
        * Work.FTS.EllipticEst.TT.TTint α G)
        + α ^ 2 * Work.Spaces.HkSq α 0 (Work.Spaces.DzIter 1 G)
      ≤ 10 * (α ^ 4 * Work.Spaces.HkSq α 0 (Work.Spaces.DzIter 2 G)
          + Work.Spaces.HkSq α 0 (Work.Spaces.pthIter 2 G)
          + α ^ 2 * Work.Spaces.HkSq α 0 (Work.Spaces.DzIter 1 G)) := by
    have hp : 0 ≤ 9 * (α ^ 2 - α ^ 4) * Work.Spaces.HkSq α 0 (Work.Spaces.DzIter 1 G) :=
      mul_nonneg (mul_nonneg (by norm_num) (by linarith)) hA2
    have hSbound : α ^ 2 * Real.sqrt (Work.FTS.EllipticEst.TT.DDint α G
          * Work.FTS.EllipticEst.TT.TTint α G)
          + α ^ 2 * Work.Spaces.HkSq α 0 (Work.Spaces.DzIter 1 G)
        ≤ α ^ 4 * Work.Spaces.HkSq α 0 (Work.Spaces.DzIter 2 G)
          + 9 * α ^ 4 * Work.Spaces.HkSq α 0 (Work.Spaces.DzIter 1 G)
          + Work.Spaces.HkSq α 0 (Work.Spaces.pthIter 2 G) / 2
          + α ^ 2 * Work.Spaces.HkSq α 0 (Work.Spaces.DzIter 1 G) := by
      have h := hAM2
      have h9 : α ^ 4 * (2 * Work.Spaces.HkSq α 0 (Work.Spaces.DzIter 2 G)
            + 18 * Work.Spaces.HkSq α 0 (Work.Spaces.DzIter 1 G))
          = 2 * (α ^ 4 * Work.Spaces.HkSq α 0 (Work.Spaces.DzIter 2 G))
            + 18 * (α ^ 4 * Work.Spaces.HkSq α 0 (Work.Spaces.DzIter 1 G)) := by ring
      rw [h9] at h
      linarith [h]
    nlinarith [hSbound, hp, hA0, hA1]
  -- the chain, ending with `α² Xint`
  have hmain : α ^ 2 * Work.FTS.EllipticEst.TT.Xint α G
      ≤ 10 * C₀ * (α ^ 4 * Work.Spaces.HkSq α 0 (Work.Spaces.DzIter 2 G)
          + Work.Spaces.HkSq α 0 (Work.Spaces.pthIter 2 G)
          + α ^ 2 * Work.Spaces.HkSq α 0 (Work.Spaces.DzIter 1 G)) := by
    have h1 : α ^ 2 * Work.FTS.EllipticEst.TT.Xint α G
        ≤ C₀ * (α ^ 2 * Real.sqrt (Work.FTS.EllipticEst.TT.DDint α G
              * Work.FTS.EllipticEst.TT.TTint α G)
            + α ^ 2 * Work.Spaces.HkSq α 0 (Work.Spaces.DzIter 1 G)) := by
      calc α ^ 2 * Work.FTS.EllipticEst.TT.Xint α G
          ≤ α ^ 2 * (C₀ * (Real.sqrt (Work.FTS.EllipticEst.TT.DDint α G
                * Work.FTS.EllipticEst.TT.TTint α G)
              + Work.Spaces.HkSq α 0 (Work.Spaces.DzIter 1 G))) :=
            mul_le_mul_of_nonneg_left hc hα2nn
        _ = C₀ * (α ^ 2 * Real.sqrt (Work.FTS.EllipticEst.TT.DDint α G
                * Work.FTS.EllipticEst.TT.TTint α G)
              + α ^ 2 * Work.Spaces.HkSq α 0 (Work.Spaces.DzIter 1 G)) := by ring
    have h2 := mul_le_mul_of_nonneg_left hkey hC₀pos.le
    calc α ^ 2 * Work.FTS.EllipticEst.TT.Xint α G
        ≤ C₀ * (α ^ 2 * Real.sqrt (Work.FTS.EllipticEst.TT.DDint α G
              * Work.FTS.EllipticEst.TT.TTint α G)
            + α ^ 2 * Work.Spaces.HkSq α 0 (Work.Spaces.DzIter 1 G)) := h1
      _ ≤ C₀ * (10 * (α ^ 4 * Work.Spaces.HkSq α 0 (Work.Spaces.DzIter 2 G)
            + Work.Spaces.HkSq α 0 (Work.Spaces.pthIter 2 G)
            + α ^ 2 * Work.Spaces.HkSq α 0 (Work.Spaces.DzIter 1 G))) := h2
      _ = 10 * C₀ * (α ^ 4 * Work.Spaces.HkSq α 0 (Work.Spaces.DzIter 2 G)
            + Work.Spaces.HkSq α 0 (Work.Spaces.pthIter 2 G)
            + α ^ 2 * Work.Spaces.HkSq α 0 (Work.Spaces.DzIter 1 G)) := by ring
  rw [Work.FTS.EllipticEst.TT.L2Sq_eq_Xint]
  calc α ^ 4 * Work.FTS.EllipticEst.TT.Xint α G
      = α ^ 2 * (α ^ 2 * Work.FTS.EllipticEst.TT.Xint α G) := by ring
    _ ≤ α ^ 2 * (10 * C₀ * (α ^ 4 * Work.Spaces.HkSq α 0 (Work.Spaces.DzIter 2 G)
          + Work.Spaces.HkSq α 0 (Work.Spaces.pthIter 2 G)
          + α ^ 2 * Work.Spaces.HkSq α 0 (Work.Spaces.DzIter 1 G))) :=
        mul_le_mul_of_nonneg_left hmain hα2nn
    _ = 10 * C₀ * α ^ 2 * (α ^ 4 * Work.Spaces.HkSq α 0 (Work.Spaces.DzIter 2 G)
          + Work.Spaces.HkSq α 0 (Work.Spaces.pthIter 2 G)
          + α ^ 2 * Work.Spaces.HkSq α 0 (Work.Spaces.DzIter 1 G)) := by ring

theorem interpGamma : ∃ C : ℝ, 0 < C ∧
    ∀ (α : ℝ) (G : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 / 4 →
      Work.FTS.EllipticEst.SmoothOpen G →
      (∀ z : ℝ, G z 0 = 0) → (∀ z : ℝ, G z (Real.pi / 2) = 0) →
      Work.Spaces.HkMem α 0 (Work.Spaces.DzIter 2 G) →
      Work.Spaces.HkMem α 0 (Work.Spaces.pthIter 2 G) →
      Work.Spaces.HkMem α 0 (Work.Spaces.DzIter 1 G) →
      MeasureTheory.IntegrableOn (fun z : ℝ => ∫ θ in Work.Spaces.Iθ,
        (Work.Spaces.Dz (Work.Spaces.pth G) z θ) ^ 2 * (Work.Spaces.w z) ^ 2
          * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α)) Work.Spaces.Iz →
      α ^ 4 * Work.Spaces.L2Sq (fun z θ => Work.Spaces.Dz (Work.Spaces.pth G) z θ
            * (Real.sin (2 * θ)) ^ ((2 - Work.Spaces.gam α) / 2) * Work.Spaces.w z)
        ≤ C * α ^ 2 * (α ^ 4 * Work.Spaces.HkSq α 0 (Work.Spaces.DzIter 2 G)
            + Work.Spaces.HkSq α 0 (Work.Spaces.pthIter 2 G)
            + α ^ 2 * Work.Spaces.HkSq α 0 (Work.Spaces.DzIter 1 G)) :=
  interpGamma_of_core interpGamma_core interpGamma_slots

end Work.FTS.EllipticEst.TT
