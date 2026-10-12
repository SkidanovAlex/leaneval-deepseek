import ChallengeDeps
import Submission.Work.BoseFixB1.Core.symA_zero_decay_pow
import Submission.Work.BoseFixB1.Smear.bsFamilyFormUnproj_le_mix
import Submission.Work.BoseFixB1S.symAFsParamsB1
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1.Core.spectral_chain` — FS `eq:BSsliding2`: the sliding spectral half

The **spectral chain** of FS's `eq:BSsliding2`: the unprojected moving-box family form of the
anchored-mean-free windowed state `ψ₀ = χ_ℓ·Q₀ψ` at the sliding cut-off `c = sbCut μ(a v)`, at
scale `dℓ`, is dominated by FS's two-cut mixture word `mainWord` plus the constant term of the
symbol comparison times the `L²` mass of `ψ₀`.

The three ingredients, each proved in this workspace:

* `Work.BoseFixB1P.bsFamilyFormUnproj_fsKinCoeff_final` — the family form *is* the Fourier integral
  of its symbol: `bsFamilyFormUnproj a (fsKinCoeff c) ψ = (2π)⁻³ ∫_q symA a (fsKinCoeff c) q
  ‖kinFT ψ q‖² dq`;
* `Work.BoseFixB1S.symAFsParamsB1` — the two-cut pointwise symbol comparison at FS's parameters
  (the FS-parameter instance of `Work.BoseFixB1.symA_fsKinCoeff_mix_scaled` at `a = dℓ`, `C = 1/s`,
  with the tail supplied reflexively by `β = symA 1 (fsKinCoeff (1/(2s))) 0`);
* `Work.BSKinetic.plancherel_pconv` — `(2π)⁻³ ∫_q ‖kinFT ψ₀ q‖² = ∫ ψ₀²`.

The passage from the pointwise comparison to the form bound is
`Work.BoseFixB1.Smear.bsFamilyFormUnproj_le_mix` (integration against `‖kinFT ψ₀‖² ≥ 0`), and the
identification of the mixture integral with `mainWord` is the definitional identity recorded as
`mainWord_unproj_eq` below.
-/

namespace Work.BoseFixB1.Core

noncomputable section

open MeasureTheory Filter
open scoped ContDiff Topology Real

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option maxHeartbeats 1000000
-- The two hypotheses of `spectral_chain` are part of the frozen statement (the scattering
-- solution and `a v > 0` are not needed: `Adm` already forces `0 < a v` via `adm_a_pos`).
set_option linter.unusedVariables false

/-! ## 0. The two bookkeeping lemmas about the mixture integral -/

/-- **Integrability of the mixture-plus-constant integrand.**  For a smooth compactly supported
state `w`, the weight
`((1−ε)[‖q‖−c₁]₊² + ε[‖q‖−c₂]₊² + p)·‖kinFT w q‖²`
is `L¹`: the two cut-off terms are `L¹` by `integrable_fsKinCoeff_mul_bsPsi_sq` and the constant
term by `integrable_kinFT_sq`.  This is exactly the `hint` hypothesis of
`Work.BoseFixB1.Smear.bsFamilyFormUnproj_le_mix`. -/
theorem integrable_mixConst_mul_kinFT_sq {c₁ c₂ ε p : ℝ}
    {w : E3 → ℝ} (hw : ContDiff ℝ (⊤ : ENat) w) (hws : HasCompactSupport w) :
    MeasureTheory.Integrable (fun q : E3 =>
      ((1 - ε) * Submission.BoseGases.fsKinCoeff c₁ ‖q‖
        + ε * Submission.BoseGases.fsKinCoeff c₂ ‖q‖ + p)
      * ‖Submission.BoseGases.kinFT (fun z : E3 => (w z : ℂ)) q‖ ^ 2) := by
  have h1 : Integrable (fun q : E3 => Submission.BoseGases.fsKinCoeff c₁ ‖q‖ *
      ‖Submission.BoseGases.kinFT (fun z : E3 => (w z : ℂ)) q‖ ^ 2) :=
    Work.BSKinetic.Decomp.integrable_fsKinCoeff_mul_bsPsi_sq (c := c₁) hw hws
  have h2 : Integrable (fun q : E3 => Submission.BoseGases.fsKinCoeff c₂ ‖q‖ *
      ‖Submission.BoseGases.kinFT (fun z : E3 => (w z : ℂ)) q‖ ^ 2) :=
    Work.BSKinetic.Decomp.integrable_fsKinCoeff_mul_bsPsi_sq (c := c₂) hw hws
  have h0 : Integrable (fun q : E3 =>
      ‖Submission.BoseGases.kinFT (fun z : E3 => (w z : ℂ)) q‖ ^ 2) :=
    Work.BSKinetic.integrable_kinFT_sq w hw hws
  refine ((h1.const_mul (1 - ε)).add (h2.const_mul ε) |>.add (h0.const_mul p)).congr ?_
  filter_upwards with q
  simp only [Pi.add_apply]
  ring

/-- **Peeling off the constant term of the mixture integrand.**  With `A q = (1−ε)[‖q‖−c₁]₊² +
ε[‖q‖−c₂]₊²`, the `(2π)⁻³`-normalised integral of `(A + p)·‖kinFT w‖²` splits into the
`(2π)⁻³`-integral of `A·‖kinFT w‖²` plus `p·∫_z w z²` (the last step being `plancherel_pconv`). -/
theorem mixConst_integral_eq {c₁ c₂ ε p : ℝ}
    {w : E3 → ℝ} (hw : ContDiff ℝ (⊤ : ENat) w) (hws : HasCompactSupport w) :
    ((2 * Real.pi) ^ 3)⁻¹ * (∫ q : E3,
        ((1 - ε) * Submission.BoseGases.fsKinCoeff c₁ ‖q‖
          + ε * Submission.BoseGases.fsKinCoeff c₂ ‖q‖ + p)
        * ‖Submission.BoseGases.kinFT (fun z : E3 => (w z : ℂ)) q‖ ^ 2)
      = ((2 * Real.pi) ^ 3)⁻¹ * (∫ q : E3,
          ((1 - ε) * Submission.BoseGases.fsKinCoeff c₁ ‖q‖
            + ε * Submission.BoseGases.fsKinCoeff c₂ ‖q‖)
          * ‖Submission.BoseGases.kinFT (fun z : E3 => (w z : ℂ)) q‖ ^ 2)
        + p * ∫ z : E3, (w z) ^ 2 := by
  have h1 : Integrable (fun q : E3 => Submission.BoseGases.fsKinCoeff c₁ ‖q‖ *
      ‖Submission.BoseGases.kinFT (fun z : E3 => (w z : ℂ)) q‖ ^ 2) :=
    Work.BSKinetic.Decomp.integrable_fsKinCoeff_mul_bsPsi_sq (c := c₁) hw hws
  have h2 : Integrable (fun q : E3 => Submission.BoseGases.fsKinCoeff c₂ ‖q‖ *
      ‖Submission.BoseGases.kinFT (fun z : E3 => (w z : ℂ)) q‖ ^ 2) :=
    Work.BSKinetic.Decomp.integrable_fsKinCoeff_mul_bsPsi_sq (c := c₂) hw hws
  have h0 : Integrable (fun q : E3 =>
      ‖Submission.BoseGases.kinFT (fun z : E3 => (w z : ℂ)) q‖ ^ 2) :=
    Work.BSKinetic.integrable_kinFT_sq w hw hws
  have hF : Integrable (fun q : E3 =>
      ((1 - ε) * Submission.BoseGases.fsKinCoeff c₁ ‖q‖
        + ε * Submission.BoseGases.fsKinCoeff c₂ ‖q‖)
      * ‖Submission.BoseGases.kinFT (fun z : E3 => (w z : ℂ)) q‖ ^ 2) := by
    refine ((h1.const_mul (1 - ε)).add (h2.const_mul ε)).congr ?_
    filter_upwards with q
    simp only [Pi.add_apply]
    ring
  have hW : Integrable (fun q : E3 =>
      p * ‖Submission.BoseGases.kinFT (fun z : E3 => (w z : ℂ)) q‖ ^ 2) := h0.const_mul p
  have hsplit : (∫ q : E3,
        ((1 - ε) * Submission.BoseGases.fsKinCoeff c₁ ‖q‖
          + ε * Submission.BoseGases.fsKinCoeff c₂ ‖q‖ + p)
        * ‖Submission.BoseGases.kinFT (fun z : E3 => (w z : ℂ)) q‖ ^ 2)
      = (∫ q : E3,
          ((1 - ε) * Submission.BoseGases.fsKinCoeff c₁ ‖q‖
            + ε * Submission.BoseGases.fsKinCoeff c₂ ‖q‖)
          * ‖Submission.BoseGases.kinFT (fun z : E3 => (w z : ℂ)) q‖ ^ 2)
        + ∫ q : E3, p * ‖Submission.BoseGases.kinFT (fun z : E3 => (w z : ℂ)) q‖ ^ 2 := by
    rw [← integral_add hF hW]
    refine integral_congr_ae (Filter.Eventually.of_forall fun q => ?_)
    ring
  have hsplit' : (∫ q : E3, p * ‖Submission.BoseGases.kinFT (fun z : E3 => (w z : ℂ)) q‖ ^ 2)
      = p * ∫ q : E3, ‖Submission.BoseGases.kinFT (fun z : E3 => (w z : ℂ)) q‖ ^ 2 :=
    integral_const_mul p _
  have hplan := Work.BSKinetic.plancherel_pconv w hw hws
  rw [hsplit, hsplit']
  rw [show ((2 * Real.pi) ^ 3)⁻¹ *
        ((∫ q : E3,
          ((1 - ε) * Submission.BoseGases.fsKinCoeff c₁ ‖q‖
            + ε * Submission.BoseGases.fsKinCoeff c₂ ‖q‖)
          * ‖Submission.BoseGases.kinFT (fun z : E3 => (w z : ℂ)) q‖ ^ 2)
         + p * ∫ q : E3, ‖Submission.BoseGases.kinFT (fun z : E3 => (w z : ℂ)) q‖ ^ 2)
      = ((2 * Real.pi) ^ 3)⁻¹ * (∫ q : E3,
          ((1 - ε) * Submission.BoseGases.fsKinCoeff c₁ ‖q‖
            + ε * Submission.BoseGases.fsKinCoeff c₂ ‖q‖)
          * ‖Submission.BoseGases.kinFT (fun z : E3 => (w z : ℂ)) q‖ ^ 2)
        + p * (((2 * Real.pi) ^ 3)⁻¹ * ∫ q : E3,
            ‖Submission.BoseGases.kinFT (fun z : E3 => (w z : ℂ)) q‖ ^ 2) by ring, hplan]

/-- **The anchored two-cut word `mainWord` is the unprojected mixture integral.**  With
`ψ₀ = χ_ℓ·Q₀ψ` (the window `χ_ℓ = chiScale ℓ` times the box-mean-free projection
`Q₀ψ = bsQ ℓ 0 ψ`),

`mainWord ℓ d s εT 0 ψ = (2π)⁻³ ∫_q ((1−εT)[‖q‖−c₁]₊² + εT[‖q‖−c₂]₊²)·‖kinFT ψ₀(q)‖² dq`

at FS's cut-offs `c₁ = (2sℓ)⁻¹`, `c₂ = (2dsℓ)⁻¹`.  Definitional unfolding of `mainWord`
(=`(1−εT)·bsOneBody c₁ + εT·bsOneBody c₂` at `u = 0`) plus linearity of the Bochner integral. -/
theorem mainWord_unproj_eq (ℓ d s εT : ℝ) (hℓ : 0 < ℓ)
    {ψ : E3 → ℝ} (hψ : ContDiff ℝ (⊤ : ENat) ψ) :
    Work.BoseKinLoc.mainWord ℓ d s εT 0 ψ
      = ((2 * Real.pi) ^ 3)⁻¹ * ∫ q : E3,
          ((1 - εT) * Submission.BoseGases.fsKinCoeff ((2 * (s * ℓ))⁻¹) ‖q‖
            + εT * Submission.BoseGases.fsKinCoeff ((2 * (d * s * ℓ))⁻¹) ‖q‖)
          * ‖Submission.BoseGases.kinFT (fun z : E3 =>
              ((Submission.BoseGases.chiScale ℓ z * Work.BSKinetic.bsQ ℓ 0 ψ z : ℝ) : ℂ)) q‖ ^ 2 := by
  have hcont : ContDiff ℝ (⊤ : ENat) (fun z : E3 =>
      Submission.BoseGases.chiScale ℓ z * Work.BSKinetic.bsQ ℓ 0 ψ z) :=
    (Submission.BoseGases.chiScale_contDiff hℓ.ne').mul (hψ.sub contDiff_const)
  have hcs : HasCompactSupport (fun z : E3 =>
      Submission.BoseGases.chiScale ℓ z * Work.BSKinetic.bsQ ℓ 0 ψ z) :=
    (Submission.BoseGases.chiScale_hasCompactSupport hℓ.ne').mul_right
  have hbase : ∀ F : ℝ → ℝ,
      Work.BSKinetic.bsOneBody ℓ F 0 ψ
        = ((2 * Real.pi) ^ 3)⁻¹ * ∫ q : E3, F ‖q‖ *
            ‖Submission.BoseGases.kinFT (fun z : E3 =>
              ((Submission.BoseGases.chiScale ℓ z * Work.BSKinetic.bsQ ℓ 0 ψ z : ℝ) : ℂ)) q‖ ^ 2 := by
    intro F
    rw [Work.BSKinetic.bsOneBody]
    have hfun : (fun z : E3 => (Work.BSKinetic.bsWin ℓ 0 z : ℂ) *
        (Work.BSKinetic.bsQ ℓ 0 ψ z : ℂ))
        = fun z : E3 => ((Submission.BoseGases.chiScale ℓ z *
            Work.BSKinetic.bsQ ℓ 0 ψ z : ℝ) : ℂ) := by
      funext z
      simp only [Work.BSKinetic.bsWin, smul_zero, sub_zero, Complex.ofReal_mul]
    rw [hfun]
  rw [Work.BoseKinLoc.mainWord,
    hbase (Submission.BoseGases.fsKinCoeff ((2 * (s * ℓ))⁻¹)),
    hbase (Submission.BoseGases.fsKinCoeff ((2 * (d * s * ℓ))⁻¹))]
  have h1 : Integrable (fun q : E3 => Submission.BoseGases.fsKinCoeff ((2 * (s * ℓ))⁻¹) ‖q‖ *
      ‖Submission.BoseGases.kinFT (fun z : E3 =>
        ((Submission.BoseGases.chiScale ℓ z * Work.BSKinetic.bsQ ℓ 0 ψ z : ℝ) : ℂ)) q‖ ^ 2) :=
    Work.BSKinetic.Decomp.integrable_fsKinCoeff_mul_bsPsi_sq hcont hcs
  have h2 : Integrable (fun q : E3 => Submission.BoseGases.fsKinCoeff ((2 * (d * s * ℓ))⁻¹) ‖q‖ *
      ‖Submission.BoseGases.kinFT (fun z : E3 =>
        ((Submission.BoseGases.chiScale ℓ z * Work.BSKinetic.bsQ ℓ 0 ψ z : ℝ) : ℂ)) q‖ ^ 2) :=
    Work.BSKinetic.Decomp.integrable_fsKinCoeff_mul_bsPsi_sq hcont hcs
  have hcomb : (∫ q : E3,
        ((1 - εT) * Submission.BoseGases.fsKinCoeff ((2 * (s * ℓ))⁻¹) ‖q‖
          + εT * Submission.BoseGases.fsKinCoeff ((2 * (d * s * ℓ))⁻¹) ‖q‖)
        * ‖Submission.BoseGases.kinFT (fun z : E3 =>
            ((Submission.BoseGases.chiScale ℓ z * Work.BSKinetic.bsQ ℓ 0 ψ z : ℝ) : ℂ)) q‖ ^ 2)
      = (1 - εT) * (∫ q : E3, Submission.BoseGases.fsKinCoeff ((2 * (s * ℓ))⁻¹) ‖q‖ *
          ‖Submission.BoseGases.kinFT (fun z : E3 =>
            ((Submission.BoseGases.chiScale ℓ z * Work.BSKinetic.bsQ ℓ 0 ψ z : ℝ) : ℂ)) q‖ ^ 2)
        + εT * (∫ q : E3, Submission.BoseGases.fsKinCoeff ((2 * (d * s * ℓ))⁻¹) ‖q‖ *
          ‖Submission.BoseGases.kinFT (fun z : E3 =>
            ((Submission.BoseGases.chiScale ℓ z * Work.BSKinetic.bsQ ℓ 0 ψ z : ℝ) : ℂ)) q‖ ^ 2) := by
    rw [← integral_const_mul, ← integral_const_mul,
      ← integral_add (h1.const_mul (1 - εT)) (h2.const_mul εT)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun q => ?_)
    ring
  rw [hcomb]
  ring

/-! ## 1. The spectral chain with the pointwise comparison as a hypothesis -/

/-- **The spectral chain, parametric form.**  Given the pointwise two-cut symbol comparison at
scale `ℓd`, the unprojected family form of the windowed mean-free state `ψ₀ = χ_ℓ·Q₀ψ` is bounded
by the anchored two-cut word `mainWord` plus the constant payment `p` times the `L²` mass of `ψ₀`.

The proof is the composition

* `Work.BoseFixB1.Smear.bsFamilyFormUnproj_le_mix` (the pointwise comparison integrates against
  `‖kinFT ψ₀‖² ≥ 0`, with integrability `integrable_mixConst_mul_kinFT_sq`),
* `mixConst_integral_eq` (peel the constant `p` off, using `plancherel_pconv`),
* `mainWord_unproj_eq` (identify the mixture integral with `mainWord`). -/
theorem bsFamilyFormUnproj_le_mainWord_add {ℓ d s εT c p : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d)
    (hε0 : 0 ≤ εT)
    (hsym : ∀ q : E3, Work.OneBodyKin.symA (ℓ * d) (Submission.BoseGases.fsKinCoeff c) q
      ≤ (1 - εT) * Submission.BoseGases.fsKinCoeff ((2 * (s * ℓ))⁻¹) ‖q‖
        + εT * Submission.BoseGases.fsKinCoeff ((2 * (d * s * ℓ))⁻¹) ‖q‖ + p)
    {ψ : E3 → ℝ} (hψ : ContDiff ℝ (⊤ : ENat) ψ) :
    Work.BSKinetic.bsFamilyFormUnproj (d * ℓ) (Submission.BoseGases.fsKinCoeff c)
        (fun z : E3 => Submission.BoseGases.chiScale ℓ z * Work.BSKinetic.bsQ ℓ 0 ψ z)
      ≤ Work.BoseKinLoc.mainWord ℓ d s εT 0 ψ
        + p * ∫ z : E3, (Submission.BoseGases.chiScale ℓ z) ^ 2
            * (Work.BSKinetic.bsQ ℓ 0 ψ z) ^ 2 := by
  have hcont : ContDiff ℝ (⊤ : ENat) (fun z : E3 =>
      Submission.BoseGases.chiScale ℓ z * Work.BSKinetic.bsQ ℓ 0 ψ z) :=
    (Submission.BoseGases.chiScale_contDiff hℓ.ne').mul (hψ.sub contDiff_const)
  have hcs : HasCompactSupport (fun z : E3 =>
      Submission.BoseGases.chiScale ℓ z * Work.BSKinetic.bsQ ℓ 0 ψ z) :=
    (Submission.BoseGases.chiScale_hasCompactSupport hℓ.ne').mul_right
  have hint := integrable_mixConst_mul_kinFT_sq (c₁ := (2 * (s * ℓ))⁻¹) (c₂ := (2 * (d * s * ℓ))⁻¹)
    (ε := εT) (p := p) hcont hcs
  have hstep := Work.BoseFixB1.Smear.bsFamilyFormUnproj_le_mix (a := ℓ * d) (c := c)
    (c₁ := (2 * (s * ℓ))⁻¹) (c₂ := (2 * (d * s * ℓ))⁻¹) (ε := εT) (p := p)
    (mul_pos hℓ hd) hε0 hsym
    (fun z : E3 => Submission.BoseGases.chiScale ℓ z * Work.BSKinetic.bsQ ℓ 0 ψ z) hcont hcs hint
  have hsplit := mixConst_integral_eq (c₁ := (2 * (s * ℓ))⁻¹) (c₂ := (2 * (d * s * ℓ))⁻¹)
    (ε := εT) (p := p) hcont hcs
  have hmain := mainWord_unproj_eq ℓ d s εT hℓ hψ
  have hsq : (∫ z : E3,
        (Submission.BoseGases.chiScale ℓ z * Work.BSKinetic.bsQ ℓ 0 ψ z) ^ 2)
      = ∫ z : E3, (Submission.BoseGases.chiScale ℓ z) ^ 2
          * (Work.BSKinetic.bsQ ℓ 0 ψ z) ^ 2 :=
    integral_congr_ae (Filter.Eventually.of_forall fun z => by ring)
  rw [← hmain] at hsplit
  rw [hsq] at hsplit
  rw [← hsplit]
  simpa only [mul_comm ℓ d] using hstep

/-! ## 2. The FS-parameter instance -/

/-- The spectral chain of FS `eq:BSsliding2`'s kinetic core: the unprojected family form of the
anchored-mean-free, `χ_ℓ`-windowed state `ψ₀ = χ_ℓ·Q₀ψ` is bounded by the two-cut mixture word
`mainWord` plus the constant term of the symbol comparison,
`(symA 1 (fsKinCoeff (1/(2s))) 0)/(dℓ)²` times the `L²` mass of `ψ₀`.
Inputs: the proved symbol identity `Work.BoseFixB1P.bsFamilyFormUnproj_fsKinCoeff_final`
(family form `= (2π)⁻³∫_q symA ‖kinFT ψ₀‖²`), the proved scaled two-cut comparison
`Work.BoseFixB1.Core.symA_fsKinCoeff_mix_scaled` at `a = dℓ`, `C = c_sb·dℓ = 1/s` (with
`htail` supplied by `Work.BoseFixB1.Core.symA_zero_decay_pow` at `C = 1/(2s)`, and the moment
hypotheses `hM1`, `hM2` and `d ≤ 1/2`, `εT ≤ 1/2` holding for small `μ(a v)³`), integration of
the pointwise bound against `‖kinFT ψ₀‖² ≥ 0`, `Work.BSKinetic.plancherel_pconv` for
`(2π)⁻³∫_q ‖kinFT ψ₀‖² = ∫ψ₀²`, and the definitional identity
`mainWord ℓ d s εT 0 ψ = (2π)⁻³∫_q [(1−εT)fsKinCoeff c₁‖q‖ + εT fsKinCoeff c₂‖q‖]‖kinFT ψ₀(q)‖²dq`
with `c₁ = (2sℓ)⁻¹`, `c₂ = (2dsℓ)⁻¹`. -/
theorem spectral_chain {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v)
    (hav : 0 < _root_.BoseGases.a v) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
      ∀ ψ : EuclideanSpace ℝ (Fin 3) → ℝ, ContDiff ℝ (⊤ : ENat) ψ →
        Work.BSKinetic.bsFamilyFormUnproj
            ((Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d *
              Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
            (Submission.BoseGases.fsKinCoeff (sbCut μ (_root_.BoseGases.a v)))
            (fun z : EuclideanSpace ℝ (Fin 3) => Submission.BoseGases.chiScale
                (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) z *
              Work.BSKinetic.bsQ (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) 0 ψ z)
          ≤ Work.BoseKinLoc.mainWord (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
              (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d
              (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s
              (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).eT 0 ψ
            + ((Work.OneBodyKin.symA 1 (Submission.BoseGases.fsKinCoeff
                  (1 / (2 * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s))) 0)
                / ((Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d *
                    Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) ^ 2)
              * (∫ z : EuclideanSpace ℝ (Fin 3), (Submission.BoseGases.chiScale
                    (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) z) ^ 2 *
                  (Work.BSKinetic.bsQ (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) 0 ψ z) ^ 2) := by
  obtain ⟨ε₀, hε₀, hsym⟩ := Work.BoseFixB1S.symAFsParamsB1 (v := v)
  refine ⟨ε₀, hε₀, fun μ hAdm ψ hψ => ?_⟩
  set ℓ : ℝ := Work.BoseBox.sideAt μ (_root_.BoseGases.a v) with hℓdef
  set d : ℝ := (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d with hddef
  set s : ℝ := (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s with hsdef
  set eT : ℝ := (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).eT with heTdef
  have hℓ0 : 0 < ℓ := by rw [hℓdef]; exact Work.BoseFixB1.adm_ell_pos hAdm
  have hd0 : 0 < d := by rw [hddef]; exact Work.BoseFixB1.adm_d_pos hAdm
  have heT0 : 0 ≤ eT := by rw [heTdef]; exact (Work.BoseFixB1.adm_eT_bounds hAdm).1
  have hsym' : ∀ q : E3, Work.OneBodyKin.symA (ℓ * d)
      (Submission.BoseGases.fsKinCoeff (Work.BoseFixB1.sbCut μ (_root_.BoseGases.a v))) q
      ≤ (1 - eT) * Submission.BoseGases.fsKinCoeff ((2 * (s * ℓ))⁻¹) ‖q‖
        + eT * Submission.BoseGases.fsKinCoeff ((2 * (d * s * ℓ))⁻¹) ‖q‖
        + ((ℓ * d) ^ 2)⁻¹ * Work.OneBodyKin.symA 1
            (Submission.BoseGases.fsKinCoeff ((2 * s)⁻¹)) 0 := by
    intro q
    have hq := hsym μ hAdm q
    rwa [← hℓdef, ← hddef, ← hsdef, ← heTdef] at hq
  have haux := bsFamilyFormUnproj_le_mainWord_add (ℓ := ℓ) (d := d) (s := s) (εT := eT)
    (c := Work.BoseFixB1.sbCut μ (_root_.BoseGases.a v))
    (p := ((ℓ * d) ^ 2)⁻¹ * Work.OneBodyKin.symA 1
      (Submission.BoseGases.fsKinCoeff ((2 * s)⁻¹)) 0)
    hℓ0 hd0 heT0 hsym' hψ
  have hp : ((ℓ * d) ^ 2)⁻¹ * Work.OneBodyKin.symA 1
        (Submission.BoseGases.fsKinCoeff ((2 * s)⁻¹)) 0
      = Work.OneBodyKin.symA 1 (Submission.BoseGases.fsKinCoeff (1 / (2 * s))) 0 / (d * ℓ) ^ 2 := by
    rw [one_div, show (d * ℓ) ^ 2 = (ℓ * d) ^ 2 by ring, div_eq_mul_inv]
    ring
  rwa [hp] at haux

end

end Work.BoseFixB1.Core
