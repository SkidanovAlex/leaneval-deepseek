import ChallengeDeps
import Submission.Work.BoseFixB1.RegimeAux
import Submission.Work.BoseFixB1S.cruxUnprojB1
import Submission.Work.SmallBoxOneBody.chiNormSq_ge_pi_div_48
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1S.oneBodyB1.corrInterface` — the two analytic inputs of `CorrInputB1`

The target `Work.BoseFixB1S.oneBodyB1.CorrInputB1 v` (the `(E2)+(E3)` mean-mismatch correction of
the sliding spectral crux, `FINDING_unprojected_route_B.md` §0) is

    ∃ ε₀ > 0, ∀ μ, Adm v ε₀ μ → ∀ g smooth,
      (2π)⁻³ ∫_u bsW F (χ_{B(u)}(g − m_u))
        ≤ (2π)⁻³ ∫_u bsW F (χ_{B(u)}(g − M)) + (bValue/(4ℓ²)) ∫_{acube ℓ}(g − M)²

with `F = fsKinCoeff (sbCut μ (a v))`, `ℓ = sideAt μ (a v)`, `d = (paramsAt μ (a v)).d`,
`s = (paramsAt μ (a v)).s`, `χ_{B(u)} = chiB ℓ d u`, `B(u) = dlBox ℓ d u`,
`m_u = (|B(u)|)⁻¹∫_{B(u)}g`, `M = ℓ⁻³∫_{acube ℓ}g`.

This module fixes the **only two analytic inputs** that the (machine-checked) reduction below
consumes, so that the two can be proved in parallel, in their own files:

* `WindowCutB1` — the **Fourier cut-word bound** for the window `χ_{B(u)}` at the sliding cutoff
  `c := sbCut μ (a v) = (dsℓ)⁻¹`, *parametrically small in `s`* (which is what makes the `∃ε₀`
  of the target exist):

      ∫_p ([‖p‖−c]₊²)² · ‖bsPsi (χ_{B(u)}) p‖²  ≤  K ℓ⁻¹ s^A ,      A > 0 ;

* `SqrtWeightB1` — the **`1/√|B(u)|` geometric weight bound**: for every `0 < ℓ`, `0 < d ≤ 1`
  and every nonnegative measurable `w`,

      ∫_u |B(u)|^{-1/2} ∫_{B(u)} w  ≤  C (ℓd)^{-3/2} ∫_{acube ℓ} w .

## Why exactly these two

Write `ξ := g − M` (mean-free on `acube ℓ`), `c_u := M − m_u`, `a_u := χ_{B(u)}·ξ`,
`b_u := χ_{B(u)}`.  Then `χ_{B(u)}(g − m_u) = a_u + c_u·b_u`, so in `p`-space
`kinFT(χ_{B(u)}(g−m_u)) = kinFT a_u + c_u·kinFT b_u`, whence

    bsW_u(lhs) − bsW_u(rhs)  ≤  2|c_u|·∫_p F‖p‖‖kinFT a_u‖‖kinFT b_u‖  +  c_u²·∫_p F‖p‖‖kinFT b_u‖² .

The two Cauchy–Schwarz steps

    ∫_p F‖p‖‖kinFT a_u‖‖kinFT b_u‖ ≤ √(η2_u)·√(∫_p ‖kinFT a_u‖²),
    ∫_p F‖p‖‖kinFT b_u‖²           ≤ √(η2_u)·√(∫_p ‖kinFT b_u‖²),
    η2_u := ∫_p F‖p‖²‖kinFT b_u‖²,

and Plancherel `(2π)³∫χ_{B(u)}²·ξ² ≤ (2π)³ sup χ² ∫_{B(u)}ξ²`, `(2π)³∫χ_{B(u)}² ≤ (2π)³ sup χ² |B(u)|`
give, with `M_u := ∫_{B(u)}ξ²`, `|c_u| = |(1/|B(u)|)∫_{B(u)}ξ| ≤ √(M_u/|B(u)|)`,

    bsW_u(lhs) − bsW_u(rhs)  ≤  3(2π)^{3/2} sup χ · √η2_u · M_u/√|B(u)| .

`√η2_u ≤ √(K ℓ⁻¹ s^A)` (WindowCutB1) and `Σ_u M_u/√|B(u)| ≤ C(ℓd)^{-3/2}Q₂` (SqrtWeightB1) then give

    ∫_u bsW_u(lhs) − ∫_u bsW_u(rhs)  ≤  3(2π)^{3/2} sup χ √K C · ℓ⁻² s^{A/2−9} Q₂ ,

and since `d = s⁶` and `s = (μa³)^{1/323}` the factor `s^{A/2−9}` beats any fixed constants for
`μa³` below an explicit threshold — this is the `∃ε₀` of `CorrInputB1`.

**No mean-squared estimate `∫_u(⍝_{B(u)}g)²` is needed by this route.**
-/

noncomputable section
open MeasureTheory
open scoped Real Topology ContDiff

namespace Work.BoseFixB1S.oneBodyB1

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false
set_option linter.unusedVariables false

/-- **The window cut-word bound at the sliding cutoff, with the `s`-power.**
`eta2_u := ∫_p ([‖p‖−(dsℓ)⁻¹]₊²)²·‖bsPsi (χ_{B(u)}) p‖²` is bounded by `K·ℓ⁻¹·s^A`.

Intended route: `χ_{B(u)} = chiScale ℓ · chiScale (ℓd)(· − (ℓd)u)`; `kinFT` of a product is a
convolution of `kinFT`s (`(2π)⁻³` normalisation), the corpus lemma
`Work.OneBodyKin.ProfHatDecay` gives `|kinFT (chiScale ℓ)(q)| ≤ C ℓ³(1+ℓ‖q‖)^{-6}`
(translation does not change the modulus), and the convolution of the two decaying factors is
`≤ C ℓ³(1+ℓ‖p‖)^{-6}` because `ℓd ≤ ℓ`.  Then `F(p)² = ([‖p‖−c]₊)⁴ = 0` below `c` and
`≤ ‖p‖⁴` above, and the radial integral `∫_{‖p‖>c}‖p‖⁴(1+ℓ‖p‖)^{-12}dp ∼ ℓ⁻¹(ℓc)^{-5}`
with `ℓc = 1/(ds) = s⁻⁷` gives the asserted `s`-power (`A = 35` suffices; any `A > 18` does). -/
def WindowCutB1 (v : E3 → ℝ) : Prop :=
  ∃ A : ℝ, 18 < A ∧ ∃ K : ℝ, 0 ≤ K ∧ ∃ ε₀ : ℝ, 0 < ε₀ ∧
    ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ → ∀ u : E3,
      MeasureTheory.Integrable (fun p : E3 =>
          (Submission.BoseGases.fsKinCoeff (Work.BoseFixB1.sbCut μ (_root_.BoseGases.a v)) ‖p‖) ^ 2 *
            ‖Work.BSKinetic.Decomp.bsPsi (fun z : E3 =>
              Submission.BoseGases.chiB (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u z) p‖ ^ 2)
      ∧ (∫ p : E3,
            (Submission.BoseGases.fsKinCoeff (Work.BoseFixB1.sbCut μ (_root_.BoseGases.a v)) ‖p‖) ^ 2 *
              ‖Work.BSKinetic.Decomp.bsPsi (fun z : E3 =>
                Submission.BoseGases.chiB (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                  (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u z) p‖ ^ 2)
        ≤ K * ((Work.BoseBox.sideAt μ (_root_.BoseGases.a v))⁻¹ *
            ((Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s) ^ A)

/-- **The `1/√|B(u)|` weight bound.**  For nonnegative measurable `w` integrable on `acube ℓ`,

    ∫_u |B(u)|^{-1/2}∫_{B(u)}w ≤ C (ℓd)^{-3/2} ∫_{acube ℓ} w ,     B(u) = dlBox ℓ d u.

Intended route (elementary, no Fourier): `dlBox` and `volume (dlBox) = boxMass` factorise over
the three coordinates; `∫_u 1_{x∈dlBox ℓ d u}/√(boxMass ℓ d u) du = ∏_j ∫ du_j/√(g_j(u_j))`
with one-dimensional `g_j(u_j) = |[−ℓ/2,ℓ/2] ∩ ((ℓd)u_j + [−ℓd/2,ℓd/2])|`; `g_j` is a piecewise
linear "tent" with `g_j ≤ ℓd`, so `∫ dt/√(g_j) ≤ 2∫_0^{ℓd}dt/√t + ℓd/√(ℓd) ≤ 5√(ℓd)` and
`∫ du_j/√g_j ≤ 5(ℓd)^{-1/2}` (the `1/√` makes the apparent logarithmic divergence at the faces
convergent).  This gives the pointwise bound `∫_{u:x∈B(u)}|B(u)|^{-1/2}du ≤ 125(ℓd)^{-3/2}`, and
Tonelli finishes. -/
def SqrtWeightB1 : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ (ℓ d : ℝ), 0 < ℓ → 0 < d → d ≤ 1 →
    ∀ w : E3 → ℝ, (∀ z, 0 ≤ w z) → Measurable w →
      MeasureTheory.IntegrableOn w (Submission.BoseGases.acube ℓ) →
      MeasureTheory.Integrable (fun u : E3 =>
          (1 / Real.sqrt (Work.SmallBoxSliding.boxMass ℓ d u)) *
            ∫ z in Submission.BoseGases.dlBox ℓ d u, w z)
      ∧ (∫ u : E3,
            (1 / Real.sqrt (Work.SmallBoxSliding.boxMass ℓ d u)) *
              ∫ z in Submission.BoseGases.dlBox ℓ d u, w z)
        ≤ C * (ℓ * d) ^ (-(3 / 2 : ℝ)) * ∫ z in Submission.BoseGases.acube ℓ, w z

/-- **The pointwise mean-mismatch step** (provided by
`Work.BoseFixB1S.oneBodyB1.ptStepB1`), in the `∀`-form consumed by the assembly: replacing the
intersection-box mean `⍝_{B(u)}g` by a constant `c₀` inside the window `χ_{B(u)}` costs the
`L²`-mass of `g − c₀` over `B(u)` divided by `√|B(u)|`, with the `F²`-window cut bound `√Ke` and
the window bound `χ₀`. -/
def PtStepB1 : Prop :=
  ∀ (ℓ d κ c0 χ₀ : ℝ), 0 < ℓ → 0 < d → 0 ≤ χ₀ →
    ∀ g : E3 → ℝ, ContDiff ℝ (⊤ : ENat) g → ∀ u : E3, ∀ Ke : ℝ,
      (∫ p : E3, (Submission.BoseGases.fsKinCoeff κ ‖p‖) ^ 2 *
          ‖Work.BSKinetic.Decomp.bsPsi (fun z : E3 => Submission.BoseGases.chiB ℓ d u z) p‖ ^ 2) ≤ Ke →
      MeasureTheory.Integrable (fun p : E3 => (Submission.BoseGases.fsKinCoeff κ ‖p‖) ^ 2 *
          ‖Work.BSKinetic.Decomp.bsPsi (fun z : E3 => Submission.BoseGases.chiB ℓ d u z) p‖ ^ 2) →
      (∀ z : E3, (Submission.BoseGases.chiB ℓ d u z) ^ 2 ≤ χ₀ ^ 2) →
      Work.BSKinetic.Decomp.bsW (Submission.BoseGases.fsKinCoeff κ)
          (fun z : E3 => Submission.BoseGases.chiB ℓ d u z *
            (g z - (1 / Work.SmallBoxSliding.boxMass ℓ d u) *
              (∫ z' in Submission.BoseGases.dlBox ℓ d u, g z')))
        ≤ Work.BSKinetic.Decomp.bsW (Submission.BoseGases.fsKinCoeff κ)
            (fun z : E3 => Submission.BoseGases.chiB ℓ d u z * (g z - c0))
          + 3 * χ₀ * Real.sqrt Ke * (Real.sqrt (2 * Real.pi)) ^ 3 *
              ((∫ z in Submission.BoseGases.dlBox ℓ d u, (g z - c0) ^ 2) /
                Real.sqrt (Work.SmallBoxSliding.boxMass ℓ d u))

/-- **The `u`-marginal integrability of the windowed cut words** (provided by
`Work.BoseFixB1S.oneBodyB1.marginalB1`): for every smooth `w`, both the `u`-family of the windowed
`bsW`-form of `w` and the one with the sliding intersection mean removed are integrable. -/
def MarginalB1 : Prop :=
  ∀ (ℓ d : ℝ), 0 < ℓ → 0 < d → ∀ c : ℝ, ∀ w : E3 → ℝ, ContDiff ℝ (⊤ : ENat) w →
    MeasureTheory.Integrable (fun u : E3 =>
        Work.BSKinetic.Decomp.bsW (Submission.BoseGases.fsKinCoeff c)
          (fun z : E3 => Submission.BoseGases.chiB ℓ d u z * w z))
    ∧ MeasureTheory.Integrable (fun u : E3 =>
        Work.BSKinetic.Decomp.bsW (Submission.BoseGases.fsKinCoeff c)
          (fun z : E3 => Submission.BoseGases.chiB ℓ d u z *
            (w z - (1 / Work.SmallBoxSliding.boxMass ℓ d u) *
              (∫ z' in Submission.BoseGases.dlBox ℓ d u, w z'))))

end Work.BoseFixB1S.oneBodyB1
