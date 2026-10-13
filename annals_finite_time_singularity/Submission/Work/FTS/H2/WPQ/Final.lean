/-
Copyright: work module for the Elgindi finite-time singularity project.

# The final layer of the interior product rule `WProdQ`

Given the pointwise majorant

`HkIntegrand α 4 (f·g) ≤ 10^14 |f|_𝒲² · GmajQ α g`  on `Iz × Iθ`

(proved by summing the pure `D_z`-summands and the mixed summands), this module produces the two
conclusions of the product rule:

* `HkMem α 4 (f·g)` (honesty of the `ℋ⁴`-norm of the product), and
* `HkSq α 4 (f·g) ≤ 10^18/(γ-1) · |f|_𝒲² · HkSq α 4 g`.

The point of working with `GmajQ` (which carries the angular `L²`-norm `Aang` of the mixed slots
rather than the radial weight `w²` times `Btil`) is that the `z`-integral of the angular part is
estimated *without any Fubini/measurability input*: for each `z` one has
`∑_{d<4} Aang α g d z ≤ 4 ∫_θ HkIntegrand α 4 g z θ`, so the whole majorant is dominated by a
constant times `∫_θ HkIntegrand α 4 g z θ`, which is integrable in `z` by `HkMem α 4 g` alone.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.FTS.H2.WPQ.Defs
import Submission.Work.FTS.H2.WPQ.Interior
import Submission.Work.FTS.H2.WPQ.AesmPkg

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.H2.WPQ

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-- For every `z ∈ Iz`, the sum of the angular `L²`-norms of the mixed slots of `g` is dominated
by four times the angular integral of the `ℋ⁴`-integrand of `g`. -/
theorem sum_Aang_le (α : ℝ) {g : ℝ → ℝ → ℝ} (hgm : Work.Spaces.HkMem α 4 g) {z : ℝ}
    (hz : z ∈ Work.Spaces.Iz) :
    ∑ d ∈ Finset.range 4, Aang α g d z
      ≤ 4 * ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g z θ := by
  have hd : ∀ d ∈ Finset.range 4, Aang α g d z
      ≤ ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g z θ := by
    intro d hd4
    have hd3 : d ≤ 3 := Nat.le_of_lt_succ (Finset.mem_range.mp hd4)
    refine integral_mono_of_nonneg (Eventually.of_forall fun θ => sq_nonneg _) (hgm.1 z hz)
      (ae_restrict_of_forall_mem measurableSet_Icc fun θ _ =>
        Work.Spaces.sq_le_HkIntegrand_mixed α 4 g z θ 1 d le_rfl (by omega))
  calc ∑ d ∈ Finset.range 4, Aang α g d z
      ≤ ∑ _d ∈ Finset.range 4, ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g z θ :=
        Finset.sum_le_sum hd
    _ = 4 * ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g z θ := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; norm_num

/-- The angular integral of `GmajQ α g z ·`, in closed form. -/
theorem GmajQ_theta_sum {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {g : ℝ → ℝ → ℝ}
    (hgm : Work.Spaces.HkMem α 4 g) {z : ℝ} (hz : z ∈ Work.Spaces.Iz) :
    ∫ θ in Work.Spaces.Iθ, GmajQ α g z θ
      = (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g z θ)
        + (Work.Spaces.gam α - 1)⁻¹ * (∑ d ∈ Finset.range 4, Aang α g d z)
          * (∫ θ in Work.Spaces.Iθ, (α + Real.sin (2 * θ)) ^ 2
              * (Real.sin (2 * θ)) ^ (2 * α / 5 - Work.Spaces.gam α)) := by
  have h2 : IntegrableOn (fun θ : ℝ => ((Work.Spaces.gam α - 1)⁻¹
      * (∑ d ∈ Finset.range 4, Aang α g d z))
      * ((α + Real.sin (2 * θ)) ^ 2
          * (Real.sin (2 * θ)) ^ (2 * α / 5 - Work.Spaces.gam α))) Work.Spaces.Iθ :=
    (Work.Spaces.integrableOn_angular_weight hα hα1).const_mul _
  have hcongr : (fun θ : ℝ => GmajQ α g z θ)
      = fun θ : ℝ => Work.Spaces.HkIntegrand α 4 g z θ
          + ((Work.Spaces.gam α - 1)⁻¹ * (∑ d ∈ Finset.range 4, Aang α g d z))
            * ((α + Real.sin (2 * θ)) ^ 2
                * (Real.sin (2 * θ)) ^ (2 * α / 5 - Work.Spaces.gam α)) := by
    funext θ; rw [GmajQ]
  rw [hcongr, MeasureTheory.integral_add (hgm.1 z hz) h2,
    MeasureTheory.integral_const_mul]

/-! ## The final layer -/

/-- **The two conclusions of the interior product rule, from its pointwise majorant.**

If `HkIntegrand α 4 (f·g) ≤ 10^14 |f|_𝒲² GmajQ α g` pointwise on `Iz × Iθ`, then `f·g` is of
class `ℋ⁴` and `|f·g|²_{ℋ⁴} ≤ 10^18/(γ-1) |f|²_𝒲 |g|²_{ℋ⁴}`. -/
theorem WProdQ_final {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {f g : ℝ → ℝ → ℝ}
    (hf : Work.FTS.LocData.SmoothQuad f) (hg : Work.FTS.LocData.SmoothQuad g)
    (hfm : Work.Spaces.WlInfMem α 4 f) (hgm : Work.Spaces.HkMem α 4 g)
    (hpbi : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α 4 (fun z θ => f z θ * g z θ) z θ
        ≤ 10 ^ 14 * (Work.Spaces.WlInf α 4 f) ^ 2 * GmajQ α g z θ) :
    Work.Spaces.HkMem α 4 (fun z θ => f z θ * g z θ) ∧
      Work.Spaces.HkSq α 4 (fun z θ => f z θ * g z θ)
        ≤ 10 ^ 18 / (Work.Spaces.gam α - 1) * (Work.Spaces.WlInf α 4 f) ^ 2
          * Work.Spaces.HkSq α 4 g := by
  set fg : ℝ → ℝ → ℝ := fun z θ => f z θ * g z θ with hfg
  have hfg_sm : Work.FTS.LocData.SmoothQuad fg := Work.FTS.LocData.smoothQuad_mul hf hg
  have hW : 0 ≤ Work.Spaces.WlInf α 4 f := WlInf_nonneg' hfm
  have hW2 : 0 ≤ (Work.Spaces.WlInf α 4 f) ^ 2 := sq_nonneg _
  have hγ1 : (0 : ℝ) < Work.Spaces.gam α - 1 := by
    rw [Work.Spaces.gam_sub_one]; linarith
  have hγle : Work.Spaces.gam α - 1 ≤ 1 := by
    rw [Work.Spaces.gam_sub_one]; linarith
  have hγinv : 0 ≤ (Work.Spaces.gam α - 1)⁻¹ := by positivity
  set K : ℝ := ∫ θ in Work.Spaces.Iθ, (α + Real.sin (2 * θ)) ^ 2
    * (Real.sin (2 * θ)) ^ (2 * α / 5 - Work.Spaces.gam α) with hKdef
  have hK700 : K ≤ 700 := Work.Spaces.angular_weight_integral_bound hα hα1
  have hKnn : 0 ≤ K := by
    rw [hKdef]
    exact setIntegral_nonneg measurableSet_Icc fun θ hθ =>
      mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (Work.Spaces.sin_two_nonneg' hθ) _)
  -- the slices of the majorant are integrable in `θ`
  have hGslice : ∀ z ∈ Work.Spaces.Iz, IntegrableOn (fun θ => GmajQ α g z θ) Work.Spaces.Iθ := by
    intro z hz
    have h2 : IntegrableOn (fun θ : ℝ => ((Work.Spaces.gam α - 1)⁻¹
        * (∑ d ∈ Finset.range 4, Aang α g d z))
        * ((α + Real.sin (2 * θ)) ^ 2
            * (Real.sin (2 * θ)) ^ (2 * α / 5 - Work.Spaces.gam α))) Work.Spaces.Iθ :=
      (Work.Spaces.integrableOn_angular_weight hα hα1).const_mul _
    have hcongr : (fun θ : ℝ => GmajQ α g z θ)
        = fun θ : ℝ => Work.Spaces.HkIntegrand α 4 g z θ
            + ((Work.Spaces.gam α - 1)⁻¹ * (∑ d ∈ Finset.range 4, Aang α g d z))
              * ((α + Real.sin (2 * θ)) ^ 2
                  * (Real.sin (2 * θ)) ^ (2 * α / 5 - Work.Spaces.gam α)) := by
      funext θ; rw [GmajQ]
    rw [hcongr]
    exact (hgm.1 z hz).add h2
  -- the pointwise (in `z`) bound
  have hF_le_Maj : ∀ z ∈ Work.Spaces.Iz,
      (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 fg z θ)
        ≤ 10 ^ 14 * (Work.Spaces.WlInf α 4 f) ^ 2 * (1 + 4 * K * (Work.Spaces.gam α - 1)⁻¹)
            * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g z θ) := by
    intro z hz
    set A : ℝ := ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g z θ with hAdef
    have hAnn : 0 ≤ A := integral_nonneg fun θ => Work.Spaces.HkIntegrand_nonneg α 4 g z θ
    have hstep1 : (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 fg z θ)
        ≤ ∫ θ in Work.Spaces.Iθ,
            10 ^ 14 * (Work.Spaces.WlInf α 4 f) ^ 2 * GmajQ α g z θ :=
      integral_mono_of_nonneg (Eventually.of_forall fun θ => Work.Spaces.HkIntegrand_nonneg α 4 fg z θ)
        ((hGslice z hz).const_mul _)
        (ae_restrict_of_forall_mem measurableSet_Icc fun θ hθ => hpbi z hz θ hθ)
    have hstep2 : (∫ θ in Work.Spaces.Iθ,
          10 ^ 14 * (Work.Spaces.WlInf α 4 f) ^ 2 * GmajQ α g z θ)
        = 10 ^ 14 * (Work.Spaces.WlInf α 4 f) ^ 2 * (∫ θ in Work.Spaces.Iθ, GmajQ α g z θ) :=
      MeasureTheory.integral_const_mul _ _
    rw [hstep2, GmajQ_theta_sum hα hα1 hgm hz, ← hKdef, ← hAdef] at hstep1
    have hAsum := sum_Aang_le α hgm hz
    have hkey : A + (Work.Spaces.gam α - 1)⁻¹ * (∑ d ∈ Finset.range 4, Aang α g d z) * K
        ≤ (1 + 4 * K * (Work.Spaces.gam α - 1)⁻¹) * A := by
      have h1 : (Work.Spaces.gam α - 1)⁻¹ * (∑ d ∈ Finset.range 4, Aang α g d z) * K
          ≤ (Work.Spaces.gam α - 1)⁻¹ * (4 * A) * K := by
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hAsum hγinv) hKnn
      have h2 : (Work.Spaces.gam α - 1)⁻¹ * (4 * A) * K = 4 * K * (Work.Spaces.gam α - 1)⁻¹ * A := by
        ring
      linarith [h1, h2.le, h2.ge]
    calc (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 fg z θ)
        ≤ 10 ^ 14 * (Work.Spaces.WlInf α 4 f) ^ 2
            * (A + (Work.Spaces.gam α - 1)⁻¹
                * (∑ d ∈ Finset.range 4, Aang α g d z) * K) := hstep1
      _ ≤ 10 ^ 14 * (Work.Spaces.WlInf α 4 f) ^ 2
            * ((1 + 4 * K * (Work.Spaces.gam α - 1)⁻¹) * A) :=
          mul_le_mul_of_nonneg_left hkey (by positivity)
      _ = 10 ^ 14 * (Work.Spaces.WlInf α 4 f) ^ 2 * (1 + 4 * K * (Work.Spaces.gam α - 1)⁻¹)
            * A := by ring
  -- integrability of the majorant in `z`
  have hMaj_int : IntegrableOn
      (fun z => 10 ^ 14 * (Work.Spaces.WlInf α 4 f) ^ 2 * (1 + 4 * K * (Work.Spaces.gam α - 1)⁻¹)
        * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g z θ)) Work.Spaces.Iz :=
    hgm.2.const_mul _
  -- honestly of the `ℋ⁴`-norm of the product
  have hmem : Work.Spaces.HkMem α 4 fg := by
    obtain ⟨haesm_slice, haesm_uncurry⟩ := aesm_HkIntegrand_smoothQuad α 4 fg hfg_sm
    constructor
    · intro z hz
      refine Integrable.mono' ((hGslice z hz).const_mul (10 ^ 14 * (Work.Spaces.WlInf α 4 f) ^ 2))
        (haesm_slice z hz) ?_
      filter_upwards [ae_restrict_mem measurableSet_Icc] with θ hθ
      rw [Real.norm_of_nonneg (Work.Spaces.HkIntegrand_nonneg α 4 fg z θ)]
      exact hpbi z hz θ hθ
    · have haesm_int : AEStronglyMeasurable
          (fun z => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 fg z θ)
          (volume.restrict Work.Spaces.Iz) := by
        have h := haesm_uncurry.integral_prod_right'
        have hfun : (fun z => ∫ θ, Work.Spaces.HkIntegrand α 4 fg z θ
              ∂(volume.restrict Work.Spaces.Iθ))
            = (fun z => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 fg z θ) := rfl
        rw [← hfun]; exact h
      refine Integrable.mono' hMaj_int haesm_int ?_
      filter_upwards [ae_restrict_mem measurableSet_Ici] with z hz
      rw [Real.norm_of_nonneg (integral_nonneg fun θ => Work.Spaces.HkIntegrand_nonneg α 4 fg z θ)]
      exact hF_le_Maj z hz
  refine ⟨hmem, ?_⟩
  -- the estimate
  have hSq : Work.Spaces.HkSq α 4 fg
      ≤ ∫ z in Work.Spaces.Iz, 10 ^ 14 * (Work.Spaces.WlInf α 4 f) ^ 2
          * (1 + 4 * K * (Work.Spaces.gam α - 1)⁻¹)
          * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g z θ) := by
    rw [Work.Spaces.HkSq]
    exact setIntegral_mono_of_nonneg
      (fun z _ => integral_nonneg fun θ => Work.Spaces.HkIntegrand_nonneg α 4 fg z θ)
      (fun z hz => hF_le_Maj z hz) hMaj_int
  have hval : (∫ z in Work.Spaces.Iz, 10 ^ 14 * (Work.Spaces.WlInf α 4 f) ^ 2
        * (1 + 4 * K * (Work.Spaces.gam α - 1)⁻¹)
        * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g z θ))
      = 10 ^ 14 * (1 + 4 * K * (Work.Spaces.gam α - 1)⁻¹)
          * ((Work.Spaces.WlInf α 4 f) ^ 2 * Work.Spaces.HkSq α 4 g) := by
    rw [MeasureTheory.integral_const_mul, Work.Spaces.HkSq]
    ring
  have hnum : 10 ^ 14 * (1 + 4 * K * (Work.Spaces.gam α - 1)⁻¹)
      ≤ 10 ^ 18 * (Work.Spaces.gam α - 1)⁻¹ := by
    have h1 : 4 * K * (Work.Spaces.gam α - 1)⁻¹ ≤ 2800 * (Work.Spaces.gam α - 1)⁻¹ :=
      mul_le_mul_of_nonneg_right (by linarith [hK700]) hγinv
    have h2 : (1 : ℝ) + 4 * K * (Work.Spaces.gam α - 1)⁻¹
        ≤ 1 + 2800 * (Work.Spaces.gam α - 1)⁻¹ := by linarith
    have h3 : (1 : ℝ) + 2800 * (Work.Spaces.gam α - 1)⁻¹
        ≤ 10 ^ 4 * (Work.Spaces.gam α - 1)⁻¹ := by
      have hc1 : (1 : ℝ) ≤ (Work.Spaces.gam α - 1)⁻¹ := by
        rw [one_le_inv₀ hγ1]; exact hγle
      nlinarith [hc1]
    have h5 : 10 ^ 14 * (1 + 4 * K * (Work.Spaces.gam α - 1)⁻¹)
        ≤ 10 ^ 14 * (10 ^ 4 * (Work.Spaces.gam α - 1)⁻¹) :=
      mul_le_mul_of_nonneg_left (le_trans h2 h3) (by norm_num)
    calc 10 ^ 14 * (1 + 4 * K * (Work.Spaces.gam α - 1)⁻¹)
        ≤ 10 ^ 14 * (10 ^ 4 * (Work.Spaces.gam α - 1)⁻¹) := h5
      _ = 10 ^ 18 * (Work.Spaces.gam α - 1)⁻¹ := by ring
  rw [div_eq_mul_inv]
  calc Work.Spaces.HkSq α 4 fg
      ≤ 10 ^ 14 * (1 + 4 * K * (Work.Spaces.gam α - 1)⁻¹)
          * ((Work.Spaces.WlInf α 4 f) ^ 2 * Work.Spaces.HkSq α 4 g) := hval ▸ hSq
    _ ≤ 10 ^ 18 * (Work.Spaces.gam α - 1)⁻¹
          * ((Work.Spaces.WlInf α 4 f) ^ 2 * Work.Spaces.HkSq α 4 g) :=
        mul_le_mul_of_nonneg_right hnum (mul_nonneg hW2 (Work.Spaces.HkSq_nonneg α 4 g))
    _ = 10 ^ 18 * (Work.Spaces.gam α - 1)⁻¹ * (Work.Spaces.WlInf α 4 f) ^ 2
          * Work.Spaces.HkSq α 4 g := by ring

end Work.FTS.H2.WPQ
