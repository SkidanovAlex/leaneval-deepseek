/-
Copyright: work module for the Elgindi finite-time singularity project.

# `LevelOneAsm/ParsevalZIntAux`: the measure-theoretic bricks for the `z`-integrated Parseval
identity

The target `Work.FTS.EllipticEst.LevelOneAsm.parseval_zInt` states that the *angular* Parseval
identity `eigFun_parseval` can be applied slicewise in `z` and integrated over `z ∈ (0, ∞)`
against Lebesgue measure: with

  `A_n(z)  = ∫ θ in Iθ, f z θ * Θ_{n+1} θ * cos θ`,
  `B_n(z)  = ∫ θ in Iθ, Θ_{n+1} θ * g z θ * cos θ`,
  `D_n     = ∫ θ in Iθ, Θ_{n+1} θ ^ 2 * cos θ   (= eigDn n > 0)`,
  `Gf(z)   = ∫ θ in Iθ, (f z θ) ^ 2 * cos θ`,

the series `∑_n A_n(z) B_n(z) / D_n` converges to `∫ θ in Iθ, f z θ * g z θ * cos θ` for a.e.
`z`, and integrating over `z` gives the claim.

This module collects the glue needed to pass between the *product* measure of the hypothesis

  `volume.restrict (Set.prod (Set.Ioi 0) Iθ) = (volume.restrict (Set.Ioi 0)).prod (volume.restrict Iθ)`

(the identity `volume_restrict_prod_Ioi_Iθ`) and the *slices*: a.e. strong measurability
(`sliceSM_of_hyp`, from `AEStronglyMeasurable.prodMk_left`), a.e. integrability of the slices
(`sliceSqInt_of_hyp`, `slicePairInt_of_hyp`, from `Integrable.prod_right_ae`), the membership
`MemLp (fun θ => F z θ) 2 angMeasure` for a.e. `z` (`memLp_of_slice`, the slice version of
`memLp_of_hyps`), and the a.e. strong measurability of the slice-integral functions
`z ↦ ∫ θ in Iθ, F z θ * Θ_n θ * cos θ` (`aestronglyMeasurable_sliceIntegral`, from
`AEStronglyMeasurable.integral_prod_right'`).
-/
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.FTS.EllipticEst.LevelOneAsm.eigFun_parseval
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology ENNReal
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.LevelOneAsm

local notation "Iθ" => Work.Spaces.Iθ
local notation "μz" => (volume.restrict (Set.Ioi 0) : Measure ℝ)
local notation "μθ" => (volume.restrict Iθ : Measure ℝ)

/-- The radial measure of the problem: Lebesgue measure restricted to `(0, ∞)`.

A *named* alias of `volume.restrict (Set.Ioi 0)` (definitionally equal to it), so that
statements can be written compactly. -/
def zMeasure : Measure ℝ := volume.restrict (Set.Ioi 0)

/-- The angular measure of the problem: Lebesgue measure restricted to `Iθ = [0, π/2]`. -/
def thMeasure : Measure ℝ := volume.restrict Work.Spaces.Iθ

/-- The product measure used in the hypotheses of `parseval_zInt`, written as a product of the
two restricted Lebesgue measures. -/
theorem volume_restrict_prod_Ioi_Iθ :
    (volume.restrict (Set.prod (Set.Ioi 0) Iθ) : Measure (ℝ × ℝ)) = Measure.prod μz μθ := by
  rw [Measure.volume_eq_prod (α := ℝ) (β := ℝ), Measure.prod_restrict]
  congr 1

/-- Continuity of the angular eigenfunctions `Θ_n = eigFun n` (a polynomial in `sin` and `cos`).

(Private local copy: the same statement exists in `eigFun_span_dense` as a `private` lemma and in
`Cores/eigFun_dense_sEta` under the name `continuous_eigFun`; neither is importable here without
dragging in a heavier cone.) -/
theorem continuous_eigFun_zint (n : ℕ) : Continuous (eigFun n) := by
  change Continuous (fun θ : ℝ => Real.cos θ * eigPoly n (Real.sin θ))
  refine Real.continuous_cos.mul ?_
  change Continuous
    (fun θ : ℝ => ∑ k ∈ Finset.range n, eigCoef n k * (Real.sin θ) ^ (2 * k + 1))
  exact continuous_finsetSum _ fun k _ =>
    continuous_const.mul (Real.continuous_sin.pow _)

/-- The `z`-slices of `F` are a.e. strongly measurable on `Iθ`. -/
def SliceSM (F : ℝ → ℝ → ℝ) : Prop :=
  ∀ᵐ z ∂μz, AEStronglyMeasurable (fun θ => F z θ) μθ

/-- The `z`-slices of `F` are a.e. integrable against the weight `cos θ` on `Iθ`, for the square
of `F`. -/
def SliceSqInt (F : ℝ → ℝ → ℝ) : Prop :=
  ∀ᵐ z ∂μz, IntegrableOn (fun θ => F z θ ^ 2 * Real.cos θ) Iθ

/-- The `z`-slices of `f` and `g` are a.e. jointly integrable against the weight `cos θ`. -/
def SlicePairInt (f g : ℝ → ℝ → ℝ) : Prop :=
  ∀ᵐ z ∂μz, IntegrableOn (fun θ => f z θ * g z θ * Real.cos θ) Iθ

theorem sliceSM_of_hyp {F : ℝ → ℝ → ℝ}
    (hm : AEStronglyMeasurable (Function.uncurry F)
      (volume.restrict (Set.prod (Set.Ioi 0) Iθ))) : SliceSM F := by
  rw [volume_restrict_prod_Ioi_Iθ] at hm
  exact hm.prodMk_left

theorem sliceSqInt_of_hyp {F : ℝ → ℝ → ℝ}
    (hi : IntegrableOn (fun p : ℝ × ℝ => (F p.1 p.2) ^ 2 * Real.cos p.2)
      (Set.prod (Set.Ioi 0) Iθ)) : SliceSqInt F := by
  rw [IntegrableOn] at hi
  rw [volume_restrict_prod_Ioi_Iθ] at hi
  filter_upwards [hi.prod_right_ae] with z hz
  exact hz

theorem slicePairInt_of_hyp {f g : ℝ → ℝ → ℝ}
    (hi : IntegrableOn (fun p : ℝ × ℝ => f p.1 p.2 * g p.1 p.2 * Real.cos p.2)
      (Set.prod (Set.Ioi 0) Iθ)) : SlicePairInt f g := by
  rw [IntegrableOn] at hi
  rw [volume_restrict_prod_Ioi_Iθ] at hi
  filter_upwards [hi.prod_right_ae] with z hz
  exact hz

/-- A slice that is a.e.-strongly measurable and whose square is integrable against `cos θ` lies
in `L²(angMeasure)`.  (Slice version of `memLp_of_hyps`.) -/
theorem memLp_of_slice {F : ℝ → ℝ}
    (hm : AEStronglyMeasurable F μθ)
    (hi : IntegrableOn (fun θ => F θ ^ 2 * Real.cos θ) Iθ) : MemLp F 2 angMeasure := by
  have haesm : AEStronglyMeasurable F angMeasure := hm.mono_ac angMeasure_absolutelyContinuous
  rw [MeasureTheory.memLp_two_iff_integrable_sq haesm]
  rw [angMeasure,
    MeasureTheory.integrable_withDensity_iff_integrable_smul'
      (Real.measurable_cos.ennreal_ofReal)
      (Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  refine hi.congr ?_
  filter_upwards [ae_restrict_mem (s := Iθ) measurableSet_Icc] with θ hθ
  simp only [smul_eq_mul]
  rw [ENNReal.toReal_ofReal (cos_nonneg_of_mem_Iθ hθ)]
  ring

/-- The slice-integral function `z ↦ ∫ θ in Iθ, F z θ * Θ_n θ * cos θ` is a.e.-strongly
measurable as soon as `F` is jointly a.e.-strongly measurable on the quadrant. -/
theorem aestronglyMeasurable_sliceIntegral (n : ℕ) {F : ℝ → ℝ → ℝ}
    (hm : AEStronglyMeasurable (Function.uncurry F)
      (volume.restrict (Set.prod (Set.Ioi 0) Iθ))) :
    AEStronglyMeasurable (fun z => ∫ θ in Iθ, F z θ * eigFun n θ * Real.cos θ) μz := by
  have hm' : AEStronglyMeasurable (Function.uncurry F) (Measure.prod μz μθ) := by
    rw [volume_restrict_prod_Ioi_Iθ] at hm
    exact hm
  have hcont : Continuous (fun p : ℝ × ℝ => eigFun n p.2 * Real.cos p.2) :=
    ((continuous_eigFun_zint n).comp continuous_snd).mul (Real.continuous_cos.comp continuous_snd)
  have h2 : AEStronglyMeasurable
      (fun p : ℝ × ℝ => F p.1 p.2 * (eigFun n p.2 * Real.cos p.2)) (Measure.prod μz μθ) :=
    hm'.mul hcont.aestronglyMeasurable
  refine h2.integral_prod_right'.congr ?_
  filter_upwards with z
  exact integral_congr_ae (Eventually.of_forall (fun θ => by ring))

end Work.FTS.EllipticEst.LevelOneAsm
