/-
# Cauchy–Schwarz for the `ℋ¹` inner product `H1IP`, from `HkMem α 1` alone

`Work.Coercivity.H1IP α` is the paper's `ℋ¹` inner product,

  `H1IP α f g = 10 (D_z f, D_z g)_{w²/sin^η} + 10¹⁰ (f,g)_{w²/sin^η}
                 + 10¹⁷ (f,g)_{w²} + 10²¹ (D_θ f, D_θ g)_{w²/sin^γ}`,

a sum of four weighted `L²` pairings `wip ρ A B = ∫_z ∫_θ A·B·ρ`.  `wip` is a *Bochner*
integral and hence total: when the integrand is not (a.e. strongly measurable and)
integrable its value is the junk value `0`.  So the Cauchy–Schwarz bound

  `|H1IP α f g| ≤ C·|f|_{ℋ¹}·|g|_{ℋ¹}`

cannot be proved by manipulating the pairing integrand as an honest `L²` pairing without
first knowing that the pairing integrand is honest — which is *not* implied by
`HkMem α 1` alone (`HkMem` controls only the sum of the squares of the blocks, not the
individual blocks; see `Work.Coercivity.H1IP_add_fails` for the corresponding
phenomenon for additivity, and `Transfer/H1IP_add_weak` for the honest version).

The point of this file is that no honesty is needed.  The pairing integrand of each of
the four pairings is the *product* `X f·X g` of two blocks whose squares are summands of
the `ℋ¹`-integrand (`XetaDz`, `Xeta`, `Xw`, `XgamDth`), and the bound is proved *inside*
`ℝ≥0∞`, where every step is unconditional:

* `‖∫_z ∫_θ X·Y‖ₑ ≤ ∫⁻_z ∫⁻_θ ‖X·Y‖ₑ` — `enorm_integral_le_lintegral_enorm`, twice, plus
  monotonicity of `∫⁻` (which needs no measurability);
* pointwise (a.e. in `θ`), `‖X·Y‖ₑ ≤ ofReal (√Sf)·ofReal (√Sg)` with `Sf = HkIntegrand α 1 f`
  and `Sg = HkIntegrand α 1 g`, because `‖X‖ ≤ √Sf`, `‖Y‖ ≤ √Sg`;
* Cauchy–Schwarz in `θ` (`ENNReal.lintegral_mul_le_Lp_mul_Lq` with `p = q = 2`, applied to
  the a.e. measurable functions `ofReal (√Sf)`, `ofReal (√Sg)`), which identifies the two
  factors with `ofReal (√(∫_θ Sf))`, `ofReal (√(∫_θ Sg))` by
  `ofReal_integral_eq_lintegral_ofReal`;
* the same Cauchy–Schwarz in `z`, then `HkSq α 1 f = ∫_z ∫_θ Sf` and
  `HkNorm α 1 f = √(HkSq α 1 f)`, and `ofReal_le_ofReal_iff` to get back to `ℝ`.

The four pairings are then summed with the triangle inequality and the arithmetic
`10 + 10¹⁰ + 10¹⁷ + 10²¹ ≤ 10²²`.  This is `Assembly.H1IP_cs_Q` with the `RegQ α 1`
hypothesis (`SmoothQuad` + `BdryTraces`) weakened to `HkMem α 1`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.CoercivityFix.Transfer.H1IP_add_weak
import Submission.Work.Coercivity.Defs
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.CoercivityFix.Transfer

noncomputable section

open scoped Real Topology ENNReal
open MeasureTheory Set Filter

/-! ## The triangle inequality for four terms -/

private theorem abs_add_four (a b c d : ℝ) :
    |a + b + c + d| ≤ |a| + |b| + |c| + |d| := by
  have h1 : |a + b + c + d| ≤ |a + b + c| + |d| := abs_add_le _ _
  have h2 : |a + b + c| ≤ |a + b| + |c| := abs_add_le _ _
  have h3 : |a + b| ≤ |a| + |b| := abs_add_le _ _
  linarith

/-! ## The junk-free Cauchy–Schwarz bound for a pairing of two blocks -/

/-- **Cauchy–Schwarz for a block pairing.**  If the two functions `X`, `Y` are dominated
(a.e. in `θ`, on each radial slice) by the square roots of the `ℋ¹`-integrands of `f`
resp. `g`, then the iterated integral of the product `X·Y` is bounded by the product of
the two `ℋ¹`-norms.  No measurability or integrability of `X`, `Y` themselves is assumed:
all estimates are performed in `ℝ≥0∞`, and the dominating integrands
`HkIntegrand α 1 f`, `HkIntegrand α 1 g` are honest by `HkMem α 1`. -/
private theorem abs_pairing_le (α : ℝ) {X Y f g : ℝ → ℝ → ℝ}
    (hf : Work.Spaces.HkMem α 1 f) (hg : Work.Spaces.HkMem α 1 g)
    (hX : ∀ z ∈ Work.Spaces.Iz, ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ),
      (X z θ) ^ 2 ≤ Work.Spaces.HkIntegrand α 1 f z θ)
    (hY : ∀ z ∈ Work.Spaces.Iz, ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ),
      (Y z θ) ^ 2 ≤ Work.Spaces.HkIntegrand α 1 g z θ) :
    |∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, X z θ * Y z θ|
      ≤ Real.sqrt (Work.Spaces.HkSq α 1 f) * Real.sqrt (Work.Spaces.HkSq α 1 g) := by
  have hSfnn : ∀ z θ, 0 ≤ Work.Spaces.HkIntegrand α 1 f z θ :=
    fun z θ => Work.Spaces.HkIntegrand_nonneg α 1 f z θ
  have hSgnn : ∀ z θ, 0 ≤ Work.Spaces.HkIntegrand α 1 g z θ :=
    fun z θ => Work.Spaces.HkIntegrand_nonneg α 1 g z θ
  -- Pointwise (a.e. in `θ`) domination of the pairing integrand by the two square roots.
  have hpt : ∀ z ∈ Work.Spaces.Iz, ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ),
      ‖X z θ * Y z θ‖ₑ
        ≤ ENNReal.ofReal (Real.sqrt (Work.Spaces.HkIntegrand α 1 f z θ))
          * ENNReal.ofReal (Real.sqrt (Work.Spaces.HkIntegrand α 1 g z θ)) := by
    intro z hz
    filter_upwards [hX z hz, hY z hz] with θ hx hy
    have hx' : |X z θ| ≤ Real.sqrt (Work.Spaces.HkIntegrand α 1 f z θ) := by
      rw [← Real.sqrt_sq_eq_abs]
      exact Real.sqrt_le_sqrt hx
    have hy' : |Y z θ| ≤ Real.sqrt (Work.Spaces.HkIntegrand α 1 g z θ) := by
      rw [← Real.sqrt_sq_eq_abs]
      exact Real.sqrt_le_sqrt hy
    rw [enorm_mul, Real.enorm_eq_ofReal_abs, Real.enorm_eq_ofReal_abs]
    refine mul_le_mul' ?_ ?_
    · exact (ENNReal.ofReal_le_ofReal_iff (Real.sqrt_nonneg _)).mpr hx'
    · exact (ENNReal.ofReal_le_ofReal_iff (Real.sqrt_nonneg _)).mpr hy'
  have hpq : (2 : ℝ).HolderConjugate 2 :=
    Real.holderConjugate_iff.mpr ⟨by norm_num, by norm_num⟩
  -- Cauchy–Schwarz on each angular slice.
  have hslice : ∀ z ∈ Work.Spaces.Iz,
      (∫⁻ θ in Work.Spaces.Iθ,
          ENNReal.ofReal (Real.sqrt (Work.Spaces.HkIntegrand α 1 f z θ))
            * ENNReal.ofReal (Real.sqrt (Work.Spaces.HkIntegrand α 1 g z θ)))
        ≤ ENNReal.ofReal (Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 1 f z θ))
          * ENNReal.ofReal (Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 1 g z θ)) := by
    intro z hz
    have hmeasf : AEMeasurable
        (fun θ => ENNReal.ofReal (Real.sqrt (Work.Spaces.HkIntegrand α 1 f z θ)))
        (volume.restrict Work.Spaces.Iθ) :=
      ((hf.1 z hz).aestronglyMeasurable.aemeasurable.sqrt).ennreal_ofReal
    have hmeasg : AEMeasurable
        (fun θ => ENNReal.ofReal (Real.sqrt (Work.Spaces.HkIntegrand α 1 g z θ)))
        (volume.restrict Work.Spaces.Iθ) :=
      ((hg.1 z hz).aestronglyMeasurable.aemeasurable.sqrt).ennreal_ofReal
    have hH := ENNReal.lintegral_mul_le_Lp_mul_Lq (volume.restrict Work.Spaces.Iθ) hpq hmeasf hmeasg
    have hf2 : (∫⁻ θ in Work.Spaces.Iθ,
          (ENNReal.ofReal (Real.sqrt (Work.Spaces.HkIntegrand α 1 f z θ))) ^ (2 : ℝ))
        = ENNReal.ofReal (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 1 f z θ) := by
      have hcongr : (fun θ =>
            (ENNReal.ofReal (Real.sqrt (Work.Spaces.HkIntegrand α 1 f z θ))) ^ (2 : ℝ))
          = fun θ => ENNReal.ofReal (Work.Spaces.HkIntegrand α 1 f z θ) := by
        funext θ
        rw [ENNReal.ofReal_rpow_of_nonneg (Real.sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ (2 : ℝ)),
          Real.rpow_two, Real.sq_sqrt (hSfnn z θ)]
      rw [hcongr,
        ← ofReal_integral_eq_lintegral_ofReal (hf.1 z hz) (ae_of_all _ (fun θ => hSfnn z θ))]
    have hg2 : (∫⁻ θ in Work.Spaces.Iθ,
          (ENNReal.ofReal (Real.sqrt (Work.Spaces.HkIntegrand α 1 g z θ))) ^ (2 : ℝ))
        = ENNReal.ofReal (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 1 g z θ) := by
      have hcongr : (fun θ =>
            (ENNReal.ofReal (Real.sqrt (Work.Spaces.HkIntegrand α 1 g z θ))) ^ (2 : ℝ))
          = fun θ => ENNReal.ofReal (Work.Spaces.HkIntegrand α 1 g z θ) := by
        funext θ
        rw [ENNReal.ofReal_rpow_of_nonneg (Real.sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ (2 : ℝ)),
          Real.rpow_two, Real.sq_sqrt (hSgnn z θ)]
      rw [hcongr,
        ← ofReal_integral_eq_lintegral_ofReal (hg.1 z hz) (ae_of_all _ (fun θ => hSgnn z θ))]
    have hf3 : (ENNReal.ofReal (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 1 f z θ)) ^ (1 / 2 : ℝ)
        = ENNReal.ofReal (Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 1 f z θ)) := by
      rw [ENNReal.ofReal_rpow_of_nonneg (integral_nonneg (hSfnn z)) (by norm_num : (0 : ℝ) ≤ (1 / 2 : ℝ)),
        ← Real.sqrt_eq_rpow]
    have hg3 : (ENNReal.ofReal (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 1 g z θ)) ^ (1 / 2 : ℝ)
        = ENNReal.ofReal (Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 1 g z θ)) := by
      rw [ENNReal.ofReal_rpow_of_nonneg (integral_nonneg (hSgnn z)) (by norm_num : (0 : ℝ) ≤ (1 / 2 : ℝ)),
        ← Real.sqrt_eq_rpow]
    calc (∫⁻ θ in Work.Spaces.Iθ,
          ENNReal.ofReal (Real.sqrt (Work.Spaces.HkIntegrand α 1 f z θ))
            * ENNReal.ofReal (Real.sqrt (Work.Spaces.HkIntegrand α 1 g z θ)))
        ≤ (∫⁻ θ in Work.Spaces.Iθ,
              (ENNReal.ofReal (Real.sqrt (Work.Spaces.HkIntegrand α 1 f z θ))) ^ (2 : ℝ)) ^ (1 / 2 : ℝ)
            * (∫⁻ θ in Work.Spaces.Iθ,
              (ENNReal.ofReal (Real.sqrt (Work.Spaces.HkIntegrand α 1 g z θ))) ^ (2 : ℝ)) ^ (1 / 2 : ℝ) := hH
      _ = ENNReal.ofReal (Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 1 f z θ))
            * ENNReal.ofReal (Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 1 g z θ)) := by
          rw [hf2, hg2, hf3, hg3]
  have hfz_int : Integrable (fun z => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 1 f z θ)
      (volume.restrict Work.Spaces.Iz) := hf.2
  have hgz_int : Integrable (fun z => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 1 g z θ)
      (volume.restrict Work.Spaces.Iz) := hg.2
  have hfz_nn : ∀ z, 0 ≤ ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 1 f z θ :=
    fun z => integral_nonneg (fun θ => hSfnn z θ)
  have hgz_nn : ∀ z, 0 ≤ ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 1 g z θ :=
    fun z => integral_nonneg (fun θ => hSgnn z θ)
  have hzmeas1 : AEMeasurable
      (fun z => ENNReal.ofReal (Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 1 f z θ)))
      (volume.restrict Work.Spaces.Iz) :=
    (hfz_int.aestronglyMeasurable.aemeasurable.sqrt).ennreal_ofReal
  have hzmeas2 : AEMeasurable
      (fun z => ENNReal.ofReal (Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 1 g z θ)))
      (volume.restrict Work.Spaces.Iz) :=
    (hgz_int.aestronglyMeasurable.aemeasurable.sqrt).ennreal_ofReal
  -- Cauchy–Schwarz in `z`.
  have hzH := ENNReal.lintegral_mul_le_Lp_mul_Lq (volume.restrict Work.Spaces.Iz) hpq hzmeas1 hzmeas2
  have hz2 : (∫⁻ z in Work.Spaces.Iz,
        (ENNReal.ofReal (Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 1 f z θ))) ^ (2 : ℝ))
      = ENNReal.ofReal (Work.Spaces.HkSq α 1 f) := by
    have hcongr : (fun z =>
          (ENNReal.ofReal (Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 1 f z θ))) ^ (2 : ℝ))
        = fun z => ENNReal.ofReal (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 1 f z θ) := by
      funext z
      rw [ENNReal.ofReal_rpow_of_nonneg (Real.sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ (2 : ℝ)),
        Real.rpow_two, Real.sq_sqrt (hfz_nn z)]
    rw [hcongr, ← ofReal_integral_eq_lintegral_ofReal hfz_int (ae_of_all _ hfz_nn)]
    rfl
  have hz2g : (∫⁻ z in Work.Spaces.Iz,
        (ENNReal.ofReal (Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 1 g z θ))) ^ (2 : ℝ))
      = ENNReal.ofReal (Work.Spaces.HkSq α 1 g) := by
    have hcongr : (fun z =>
          (ENNReal.ofReal (Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 1 g z θ))) ^ (2 : ℝ))
        = fun z => ENNReal.ofReal (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 1 g z θ) := by
      funext z
      rw [ENNReal.ofReal_rpow_of_nonneg (Real.sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ (2 : ℝ)),
        Real.rpow_two, Real.sq_sqrt (hgz_nn z)]
    rw [hcongr, ← ofReal_integral_eq_lintegral_ofReal hgz_int (ae_of_all _ hgz_nn)]
    rfl
  have hz3 : (ENNReal.ofReal (Work.Spaces.HkSq α 1 f)) ^ (1 / 2 : ℝ)
      = ENNReal.ofReal (Real.sqrt (Work.Spaces.HkSq α 1 f)) := by
    rw [ENNReal.ofReal_rpow_of_nonneg (Work.Spaces.HkSq_nonneg α 1 f)
        (by norm_num : (0 : ℝ) ≤ (1 / 2 : ℝ)),
      ← Real.sqrt_eq_rpow]
  have hz3g : (ENNReal.ofReal (Work.Spaces.HkSq α 1 g)) ^ (1 / 2 : ℝ)
      = ENNReal.ofReal (Real.sqrt (Work.Spaces.HkSq α 1 g)) := by
    rw [ENNReal.ofReal_rpow_of_nonneg (Work.Spaces.HkSq_nonneg α 1 g)
        (by norm_num : (0 : ℝ) ≤ (1 / 2 : ℝ)),
      ← Real.sqrt_eq_rpow]
  have hzH' : (∫⁻ z in Work.Spaces.Iz,
        ENNReal.ofReal (Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 1 f z θ))
          * ENNReal.ofReal (Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 1 g z θ)))
      ≤ ENNReal.ofReal (Real.sqrt (Work.Spaces.HkSq α 1 f))
          * ENNReal.ofReal (Real.sqrt (Work.Spaces.HkSq α 1 g)) := by
    calc (∫⁻ z in Work.Spaces.Iz,
          ENNReal.ofReal (Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 1 f z θ))
            * ENNReal.ofReal (Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 1 g z θ)))
        ≤ (∫⁻ z in Work.Spaces.Iz,
              (ENNReal.ofReal (Real.sqrt (∫ θ in Work.Spaces.Iθ,
                Work.Spaces.HkIntegrand α 1 f z θ))) ^ (2 : ℝ)) ^ (1 / 2 : ℝ)
            * (∫⁻ z in Work.Spaces.Iz,
              (ENNReal.ofReal (Real.sqrt (∫ θ in Work.Spaces.Iθ,
                Work.Spaces.HkIntegrand α 1 g z θ))) ^ (2 : ℝ)) ^ (1 / 2 : ℝ) := hzH
      _ = ENNReal.ofReal (Real.sqrt (Work.Spaces.HkSq α 1 f))
            * ENNReal.ofReal (Real.sqrt (Work.Spaces.HkSq α 1 g)) := by
          rw [hz2, hz2g, hz3, hz3g]
  have hchain : ‖∫ z in Work.Spaces.Iz, (∫ θ in Work.Spaces.Iθ, X z θ * Y z θ)‖ₑ
      ≤ ENNReal.ofReal (Real.sqrt (Work.Spaces.HkSq α 1 f))
          * ENNReal.ofReal (Real.sqrt (Work.Spaces.HkSq α 1 g)) := by
    calc ‖∫ z in Work.Spaces.Iz, (∫ θ in Work.Spaces.Iθ, X z θ * Y z θ)‖ₑ
        ≤ ∫⁻ z in Work.Spaces.Iz, ‖∫ θ in Work.Spaces.Iθ, X z θ * Y z θ‖ₑ :=
          enorm_integral_le_lintegral_enorm _
      _ ≤ ∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ, ‖X z θ * Y z θ‖ₑ :=
          lintegral_mono fun z => enorm_integral_le_lintegral_enorm _
      _ ≤ ∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ,
            ENNReal.ofReal (Real.sqrt (Work.Spaces.HkIntegrand α 1 f z θ))
              * ENNReal.ofReal (Real.sqrt (Work.Spaces.HkIntegrand α 1 g z θ)) := by
          refine lintegral_mono_ae (ae_restrict_of_forall_mem measurableSet_Ici fun z hz => ?_)
          exact lintegral_mono_ae (hpt z hz)
      _ ≤ ∫⁻ z in Work.Spaces.Iz,
            ENNReal.ofReal (Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 1 f z θ))
              * ENNReal.ofReal (Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 1 g z θ)) := by
          refine lintegral_mono_ae (ae_restrict_of_forall_mem measurableSet_Ici fun z hz => ?_)
          exact hslice z hz
      _ ≤ ENNReal.ofReal (Real.sqrt (Work.Spaces.HkSq α 1 f))
            * ENNReal.ofReal (Real.sqrt (Work.Spaces.HkSq α 1 g)) := hzH'
  rw [Real.enorm_eq_ofReal_abs,
    ← ENNReal.ofReal_mul (Real.sqrt_nonneg (Work.Spaces.HkSq α 1 f))] at hchain
  exact (ENNReal.ofReal_le_ofReal_iff
    (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))).mp hchain

/-! ## The four pairings of `H1IP` -/

/-- **Cauchy–Schwarz for `H1IP` at level `1`, with the constant `10 ^ 22` pinned.**  The
statement is the membership-based bound of the paper's `ℋ¹` pairing; the constant is *independent
of `α` (and even of `0 < α` beyond the hypotheses), which is what makes the transfer
induction's constants uniform in `α` (`Transfer/CSQ_one_unif.lean`). -/
theorem H1IP_cs_of_mem (α : ℝ) (hα : 0 < α) (f g : ℝ → ℝ → ℝ)
    (hf : Work.Spaces.HkMem α 1 f) (hg : Work.Spaces.HkMem α 1 g) :
    |Work.Coercivity.H1IP α f g|
      ≤ (10 : ℝ) ^ 22 * Work.Spaces.HkNorm α 1 f * Work.Spaces.HkNorm α 1 g := by
  set Y : ℝ := Work.Spaces.HkNorm α 1 f * Work.Spaces.HkNorm α 1 g with hY
  have hYnn : 0 ≤ Y := by
    rw [hY]
    exact mul_nonneg (Work.Spaces.HkNorm_nonneg α 1 f) (Work.Spaces.HkNorm_nonneg α 1 g)
  -- ## Term 1: the `D_z`-pairing with weight `w²·sin(2θ)^{-η}`
  have hT1 :
      |Work.Coercivity.wip Work.Coercivity.lamEta (Work.Spaces.Dz f) (Work.Spaces.Dz g)| ≤ Y := by
    rw [hY]
    have hwip : Work.Coercivity.wip Work.Coercivity.lamEta (Work.Spaces.Dz f)
        (Work.Spaces.Dz g)
        = ∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
            Work.Coercivity.XetaDz f z θ * Work.Coercivity.XetaDz g z θ := by
      simp only [Work.Coercivity.wip]
      refine setIntegral_congr_fun measurableSet_Ici (fun z _ => ?_)
      refine setIntegral_congr_fun measurableSet_Icc (fun θ hθ => ?_)
      exact (Work.Coercivity.XetaDz_mul_eq f g z θ hθ).symm
    rw [hwip]
    exact abs_pairing_le α hf hg
      (fun z _ => Eventually.of_forall
        (fun θ => Work.FTS.CoercivityFix.Assembly.sq_XetaDz_le_HkIntegrand α f z θ))
      (fun z _ => Eventually.of_forall
        (fun θ => Work.FTS.CoercivityFix.Assembly.sq_XetaDz_le_HkIntegrand α g z θ))
  -- ## Term 2: the `L²`-pairing with weight `w²·sin(2θ)^{-η}`
  have hT2 : |Work.Coercivity.wip Work.Coercivity.lamEta f g| ≤ Y := by
    rw [hY]
    have hwip : Work.Coercivity.wip Work.Coercivity.lamEta f g
        = ∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
            Work.Coercivity.Xeta f z θ * Work.Coercivity.Xeta g z θ := by
      simp only [Work.Coercivity.wip]
      refine setIntegral_congr_fun measurableSet_Ici (fun z _ => ?_)
      refine setIntegral_congr_fun measurableSet_Icc (fun θ hθ => ?_)
      exact (Work.Coercivity.Xeta_mul_eq f g z θ hθ).symm
    rw [hwip]
    exact abs_pairing_le α hf hg
      (fun z _ => Eventually.of_forall
        (fun θ => Work.FTS.CoercivityFix.Assembly.sq_Xeta_le_HkIntegrand α f z θ))
      (fun z _ => Eventually.of_forall
        (fun θ => Work.FTS.CoercivityFix.Assembly.sq_Xeta_le_HkIntegrand α g z θ))
  -- ## Term 3: the plain `w²`-pairing
  have hT3 : |Work.Coercivity.wip Work.Coercivity.lamW f g| ≤ Y := by
    rw [hY]
    have hwip : Work.Coercivity.wip Work.Coercivity.lamW f g
        = ∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
            Work.Coercivity.Xw f z θ * Work.Coercivity.Xw g z θ := by
      simp only [Work.Coercivity.wip]
      refine setIntegral_congr_fun measurableSet_Ici (fun z _ => ?_)
      refine setIntegral_congr_fun measurableSet_Icc (fun θ _ => ?_)
      simp only [Work.Coercivity.Xw, Work.Coercivity.lamW]
      ring
    rw [hwip]
    exact abs_pairing_le α hf hg
      (fun z _ => Work.FTS.CoercivityFix.Assembly.sq_Xw_le_HkIntegrand_ae α f z)
      (fun z _ => Work.FTS.CoercivityFix.Assembly.sq_Xw_le_HkIntegrand_ae α g z)
  -- ## Term 4: the `D_θ`-pairing with weight `w²·sin(2θ)^{-γ}`
  have hT4 :
      |Work.Coercivity.wip (Work.Coercivity.lamGam α) (Work.Spaces.Dth f)
        (Work.Spaces.Dth g)| ≤ Y := by
    rw [hY]
    have hwip : Work.Coercivity.wip (Work.Coercivity.lamGam α) (Work.Spaces.Dth f)
        (Work.Spaces.Dth g)
        = ∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
            Work.Coercivity.XgamDth α f z θ * Work.Coercivity.XgamDth α g z θ := by
      simp only [Work.Coercivity.wip]
      refine setIntegral_congr_fun measurableSet_Ici (fun z _ => ?_)
      refine setIntegral_congr_fun measurableSet_Icc (fun θ hθ => ?_)
      exact (Work.Coercivity.XgamDth_mul_eq α f g z θ hθ).symm
    rw [hwip]
    exact abs_pairing_le α hf hg
      (fun z _ => Eventually.of_forall
        (fun θ => Work.FTS.CoercivityFix.Assembly.sq_XgamDth_le_HkIntegrand α f z θ))
      (fun z _ => Eventually.of_forall
        (fun θ => Work.FTS.CoercivityFix.Assembly.sq_XgamDth_le_HkIntegrand α g z θ))
  -- ## The triangle inequality for the four terms of `H1IP`
  have h10 : (0 : ℝ) ≤ 10 := by norm_num
  have habs : |Work.Coercivity.H1IP α f g|
      ≤ 10 * |Work.Coercivity.wip Work.Coercivity.lamEta (Work.Spaces.Dz f) (Work.Spaces.Dz g)|
        + 10 ^ 10 * |Work.Coercivity.wip Work.Coercivity.lamEta f g|
        + 10 ^ 17 * |Work.Coercivity.wip Work.Coercivity.lamW f g|
        + 10 ^ 21 * |Work.Coercivity.wip (Work.Coercivity.lamGam α) (Work.Spaces.Dth f)
            (Work.Spaces.Dth g)| := by
    have h := abs_add_four
      ((10 : ℝ) * Work.Coercivity.wip Work.Coercivity.lamEta (Work.Spaces.Dz f)
        (Work.Spaces.Dz g))
      ((10 : ℝ) ^ 10 * Work.Coercivity.wip Work.Coercivity.lamEta f g)
      ((10 : ℝ) ^ 17 * Work.Coercivity.wip Work.Coercivity.lamW f g)
      ((10 : ℝ) ^ 21 * Work.Coercivity.wip (Work.Coercivity.lamGam α) (Work.Spaces.Dth f)
        (Work.Spaces.Dth g))
    simp only [Work.Coercivity.H1IP]
    rw [abs_mul, abs_mul, abs_mul, abs_mul, abs_of_nonneg h10,
      abs_of_nonneg (pow_nonneg h10 10), abs_of_nonneg (pow_nonneg h10 17),
      abs_of_nonneg (pow_nonneg h10 21)] at h
    exact h
  have hT1' : 10 * |Work.Coercivity.wip Work.Coercivity.lamEta (Work.Spaces.Dz f)
      (Work.Spaces.Dz g)| ≤ 10 * Y := mul_le_mul_of_nonneg_left hT1 h10
  have hT2' : 10 ^ 10 * |Work.Coercivity.wip Work.Coercivity.lamEta f g| ≤ 10 ^ 10 * Y :=
    mul_le_mul_of_nonneg_left hT2 (pow_nonneg h10 10)
  have hT3' : 10 ^ 17 * |Work.Coercivity.wip Work.Coercivity.lamW f g| ≤ 10 ^ 17 * Y :=
    mul_le_mul_of_nonneg_left hT3 (pow_nonneg h10 17)
  have hT4' : 10 ^ 21 * |Work.Coercivity.wip (Work.Coercivity.lamGam α) (Work.Spaces.Dth f)
      (Work.Spaces.Dth g)| ≤ 10 ^ 21 * Y :=
    mul_le_mul_of_nonneg_left hT4 (pow_nonneg h10 21)
  have hsum : |Work.Coercivity.H1IP α f g|
      ≤ 10 * Y + 10 ^ 10 * Y + 10 ^ 17 * Y + 10 ^ 21 * Y :=
    le_trans habs (add_le_add (add_le_add (add_le_add hT1' hT2') hT3') hT4')
  calc |Work.Coercivity.H1IP α f g|
      ≤ 10 * Y + 10 ^ 10 * Y + 10 ^ 17 * Y + 10 ^ 21 * Y := hsum
    _ = ((10 : ℝ) + 10 ^ 10 + 10 ^ 17 + 10 ^ 21) * Y := by ring
    _ ≤ (10 : ℝ) ^ 22 * Y := mul_le_mul_of_nonneg_right (by norm_num) hYnn
    _ = (10 : ℝ) ^ 22 * Work.Spaces.HkNorm α 1 f * Work.Spaces.HkNorm α 1 g := by
        rw [hY]
        ring

end

end Work.FTS.CoercivityFix.Transfer
