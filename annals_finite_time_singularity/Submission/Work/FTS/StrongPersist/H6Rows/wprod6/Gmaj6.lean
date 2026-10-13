/-
# `WProd6/Gmaj6` — the majorant of the `𝒲^{6,∞}`-priced product rule

The level-six shift of `Submission/Work/FTS/OpenPkg/WProdWin/Basic.lean`.  Everything here is
order-independent (the `TW` factor, `Aang`, `sq_le_HkIntegrand_z/mixed`) except the two
definitions, which are the `4 ↦ 6` shifts of `WProdWin.GmajW` / `WProdWin.HgInt`:

* `HgInt6 α g z = ∫_θ HkIntegrand α 6 g z θ` (its `z`-integral is `HkSq α 6 g` by definition);
* `GmajW6 α g z θ = HkIntegrand α 6 g z θ
     + (HgInt6 α g z + (γ-1)⁻¹ ∑_{d<6} Aang α g d z) · TW α θ`.

The elementary estimates (nonnegativity, the `θ`-integrability of the slices, the integral
bounds `∫_θ TW ≤ 700`, `∑_{d<6} Aang d z ≤ 6 HgInt6 z`, `w² ∫_σ (D_z^d g)² ≤ HgInt6`,
`∫_θ GmajW6 ≤ (1 + 700(1+6(γ-1)⁻¹)) HgInt6`, and the `z`-integral of the majorant) are the
verbatim level-six shifts of the level-four ones.

Everything rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.OpenPkg.WProdWin.Basic
import Submission.Work.FTS.H2.WPQ.Defs
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.Spaces.aesm_HkIntegrand_quad

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.H6Rows.WProd6

open Work.Spaces

set_option autoImplicit false
set_option linter.unusedVariables false

/-- `HgInt6 α g z = ∫_θ HkIntegrand α 6 g z θ`, the angular integral of the `ℋ⁶`-integrand of
`g` at fixed radius.  (Its `z`-integral is `HkSq α 6 g` by definition.) -/
def HgInt6 (α : ℝ) (g : ℝ → ℝ → ℝ) (z : ℝ) : ℝ :=
  ∫ θ in Iθ, HkIntegrand α 6 g z θ

/-- **The pointwise majorant of the `𝒲^{6,∞}`-priced product rule**: the `ℋ⁶`-integrand of `g`
plus the angular contribution of the mean-term bound for the radial slots of `g` (`HgInt6`) and
of the angular `L²`-norms `Aang` of the mixed slots of `g`, multiplied by the surviving angular
factor `TW`. -/
def GmajW6 (α : ℝ) (g : ℝ → ℝ → ℝ) (z θ : ℝ) : ℝ :=
  HkIntegrand α 6 g z θ
    + (HgInt6 α g z
        + (gam α - 1)⁻¹ * ∑ d ∈ Finset.range 6, Work.FTS.H2.WPQ.Aang α g d z)
      * Work.FTS.OpenPkg.WProdWin.TW α θ

/-! ## Elementary properties -/

theorem HgInt6_nonneg (α : ℝ) (g : ℝ → ℝ → ℝ) (z : ℝ) : 0 ≤ HgInt6 α g z :=
  integral_nonneg fun θ => HkIntegrand_nonneg α 6 g z θ

theorem Aang_nonneg6 (α : ℝ) (g : ℝ → ℝ → ℝ) (d : ℕ) (z : ℝ) :
    0 ≤ Work.FTS.H2.WPQ.Aang α g d z :=
  setIntegral_nonneg measurableSet_Icc fun σ _ => sq_nonneg _

theorem sum_Aang_nonneg6 (α : ℝ) (g : ℝ → ℝ → ℝ) (z : ℝ) :
    0 ≤ ∑ d ∈ Finset.range 6, Work.FTS.H2.WPQ.Aang α g d z :=
  Finset.sum_nonneg fun d _ => Aang_nonneg6 α g d z

theorem GmajW6_nonneg {α : ℝ} (hα : 0 < α) (g : ℝ → ℝ → ℝ) {z θ : ℝ} (hθ : θ ∈ Iθ) :
    0 ≤ GmajW6 α g z θ := by
  have hγ1 : (0 : ℝ) < gam α - 1 := by rw [gam_sub_one]; linarith
  refine add_nonneg (HkIntegrand_nonneg α 6 g z θ)
    (mul_nonneg (add_nonneg (HgInt6_nonneg α g z)
      (mul_nonneg (inv_nonneg.mpr hγ1.le) (sum_Aang_nonneg6 α g z)))
      (Work.FTS.OpenPkg.WProdWin.TW_nonneg hα.le hθ))

/-- The `ℋ⁶`-integrand of `g` is dominated by the majorant. -/
theorem HkIntegrand_le_GmajW6 {α : ℝ} (hα : 0 < α) (g : ℝ → ℝ → ℝ) {z θ : ℝ}
    (hθ : θ ∈ Iθ) :
    HkIntegrand α 6 g z θ ≤ GmajW6 α g z θ := by
  have hγ1 : (0 : ℝ) < gam α - 1 := by rw [gam_sub_one]; linarith
  refine le_add_of_nonneg_right (mul_nonneg (add_nonneg (HgInt6_nonneg α g z)
    (mul_nonneg (inv_nonneg.mpr hγ1.le) (sum_Aang_nonneg6 α g z)))
    (Work.FTS.OpenPkg.WProdWin.TW_nonneg hα.le hθ))

/-- The `ℋ⁶`-integrand vanishes whenever `sin(2θ) = 0` (the level-six instance of
`Work.FTS.H2.WPQ.HkIntegrand_eq_zero_of_sin_two_eq_zero`). -/
theorem HkIntegrand6_eq_zero_of_sin_two_eq_zero {α : ℝ} (hα : gam α ≠ 0)
    {F : ℝ → ℝ → ℝ} {z θ : ℝ} (h : Real.sin (2 * θ) = 0) :
    HkIntegrand α 6 F z θ = 0 := by
  have hη : (eta / 2 : ℝ) ≠ 0 := by norm_num [eta]
  have hg : -(gam α / 2) ≠ 0 := by
    intro hc
    exact hα (by linarith [neg_eq_zero.mp hc])
  simp only [HkIntegrand, Wt, wTheta]
  rw [h, Real.zero_rpow hη, Real.zero_rpow hg]
  simp

/-- The sum of the angular `L²`-norms of the mixed slots of `g` is dominated by the mean term. -/
theorem sum_Aang_le_HgInt6 {α : ℝ} {g : ℝ → ℝ → ℝ} (hgm : HkMem α 6 g) {z : ℝ}
    (hz : z ∈ Iz) :
    ∑ d ∈ Finset.range 6, Work.FTS.H2.WPQ.Aang α g d z ≤ 6 * HgInt6 α g z := by
  have hd : ∀ d ∈ Finset.range 6, Work.FTS.H2.WPQ.Aang α g d z ≤ HgInt6 α g z := by
    intro d hd6
    have hd5 : d ≤ 5 := Nat.le_of_lt_succ (Finset.mem_range.mp hd6)
    refine integral_mono_of_nonneg (Eventually.of_forall fun θ => sq_nonneg _) (hgm.1 z hz)
      (ae_restrict_of_forall_mem measurableSet_Icc fun θ _ =>
        sq_le_HkIntegrand_mixed α 6 g z θ 1 d le_rfl (by omega))
  calc ∑ d ∈ Finset.range 6, Work.FTS.H2.WPQ.Aang α g d z
      ≤ ∑ _d ∈ Finset.range 6, HgInt6 α g z := Finset.sum_le_sum hd
    _ = 6 * HgInt6 α g z := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; norm_num

/-- **The mean term controls the radial slots of `g`**:
`w(z)² ∫_σ (D_z^d g(z,σ))² ≤ HgInt6 α g z` for `d ≤ 6`. -/
theorem w_sq_mul_slice_le_HgInt6 {α : ℝ} {g : ℝ → ℝ → ℝ} (hgm : HkMem α 6 g) {d : ℕ}
    (hd : d ≤ 6) {z : ℝ} (hz : 0 < z) :
    (w z) ^ 2 * (∫ σ in Iθ, (DzIter d g z σ) ^ 2) ≤ HgInt6 α g z := by
  have hzI : z ∈ Iz := le_of_lt hz
  have hdiv : (w z) ^ 2 * (∫ σ in Iθ, (DzIter d g z σ) ^ 2)
      = ∫ σ in Iθ, (w z) ^ 2 * (DzIter d g z σ) ^ 2 := by
    rw [MeasureTheory.integral_const_mul]
  rw [hdiv]
  refine integral_mono_of_nonneg
    (Eventually.of_forall fun σ => mul_nonneg (sq_nonneg _) (sq_nonneg _)) (hgm.1 z hzI) ?_
  filter_upwards [Work.FTS.OpenPkg.ProdOpen.ae_mem_Ioo_Iθ] with σ hσ
  have hs : 0 < Real.sin (2 * σ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hσ.1]) (by linarith [hσ.2, Real.pi_pos])
  have hspos : 0 < (Real.sin (2 * σ)) ^ (eta / 2) := Real.rpow_pos_of_pos hs _
  have hkey : DzIter d g z σ * (w z / (Real.sin (2 * σ)) ^ (eta / 2))
        * (Real.sin (2 * σ)) ^ (eta / 2) = DzIter d g z σ * w z := by
    rw [mul_assoc, div_mul_cancel₀ _ (ne_of_gt hspos)]
  have hsq : ((Real.sin (2 * σ)) ^ (eta / 2)) ^ (2 : ℕ) = (Real.sin (2 * σ)) ^ eta := by
    rw [pow_two, ← Real.rpow_add hs]
    congr 1
    rw [eta]; ring
  calc (w z) ^ 2 * (DzIter d g z σ) ^ 2
      = (DzIter d g z σ * w z) ^ 2 := by ring
    _ = (DzIter d g z σ * (w z / (Real.sin (2 * σ)) ^ (eta / 2))
          * (Real.sin (2 * σ)) ^ (eta / 2)) ^ 2 := by rw [hkey]
    _ = (DzIter d g z σ * (w z / (Real.sin (2 * σ)) ^ (eta / 2))) ^ 2
          * (Real.sin (2 * σ)) ^ eta := by
        rw [mul_pow, hsq]
    _ ≤ (DzIter d g z σ * (w z / (Real.sin (2 * σ)) ^ (eta / 2))) ^ 2 * 1 := by
        refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
        exact Real.rpow_le_one hs.le (Real.sin_le_one _) (by norm_num [eta])
    _ ≤ HkIntegrand α 6 g z σ := by
        rw [mul_one]
        exact sq_le_HkIntegrand_z α 6 g z σ d hd

/-- `HgInt6` integrates to `HkSq α 6 g` (definitional). -/
theorem HgInt6_z_integral (α : ℝ) (g : ℝ → ℝ → ℝ) :
    (∫ z in Iz, HgInt6 α g z) = HkSq α 6 g := rfl

/-- The angular slice of the majorant is integrable, for every `z ∈ Iz`. -/
theorem GmajW6_integrableOn_theta {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {g : ℝ → ℝ → ℝ}
    (hgm : HkMem α 6 g) {z : ℝ} (hz : z ∈ Iz) :
    IntegrableOn (fun θ => GmajW6 α g z θ) Iθ := by
  have h2 : IntegrableOn (fun θ => (HgInt6 α g z
      + (gam α - 1)⁻¹ * ∑ d ∈ Finset.range 6, Work.FTS.H2.WPQ.Aang α g d z)
        * Work.FTS.OpenPkg.WProdWin.TW α θ) Iθ :=
    (Work.FTS.OpenPkg.WProdWin.TW_integrable hα hα1).const_mul _
  refine Integrable.congr ((hgm.1 z hz).add h2) ?_
  filter_upwards with θ
  simp only [Pi.add_apply, GmajW6]

/-- The angular integral of the majorant at a fixed radius. -/
theorem GmajW6_theta_integral_le {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {g : ℝ → ℝ → ℝ}
    (hgm : HkMem α 6 g) {z : ℝ} (hz : z ∈ Iz) :
    (∫ θ in Iθ, GmajW6 α g z θ) ≤ (1 + 700 * (1 + 6 * (gam α - 1)⁻¹)) * HgInt6 α g z := by
  have hγ1 : (0 : ℝ) < gam α - 1 := by rw [gam_sub_one]; linarith
  have hγinv : 0 ≤ (gam α - 1)⁻¹ := inv_nonneg.mpr hγ1.le
  have hhg : IntegrableOn (fun θ => HkIntegrand α 6 g z θ) Iθ := hgm.1 z hz
  have hsum : ∑ d ∈ Finset.range 6, Work.FTS.H2.WPQ.Aang α g d z ≤ 6 * HgInt6 α g z :=
    sum_Aang_le_HgInt6 hgm hz
  have h2 : IntegrableOn (fun θ => (HgInt6 α g z
      + (gam α - 1)⁻¹ * ∑ d ∈ Finset.range 6, Work.FTS.H2.WPQ.Aang α g d z)
        * Work.FTS.OpenPkg.WProdWin.TW α θ) Iθ :=
    (Work.FTS.OpenPkg.WProdWin.TW_integrable hα hα1).const_mul _
  have hsplit : (∫ θ in Iθ, GmajW6 α g z θ)
      = HgInt6 α g z + (HgInt6 α g z
          + (gam α - 1)⁻¹ * ∑ d ∈ Finset.range 6, Work.FTS.H2.WPQ.Aang α g d z)
            * (∫ θ in Iθ, Work.FTS.OpenPkg.WProdWin.TW α θ) := by
    have hfun : (fun θ : ℝ => GmajW6 α g z θ)
        = fun θ : ℝ => HkIntegrand α 6 g z θ
            + (HgInt6 α g z + (gam α - 1)⁻¹
                * ∑ d ∈ Finset.range 6, Work.FTS.H2.WPQ.Aang α g d z)
              * Work.FTS.OpenPkg.WProdWin.TW α θ := by
      funext θ; rw [GmajW6]
    rw [hfun, MeasureTheory.integral_add hhg h2, MeasureTheory.integral_const_mul]
    rfl
  rw [hsplit]
  have hT := Work.FTS.OpenPkg.WProdWin.TW_integral_le hα hα1
  have hTnn : 0 ≤ ∫ θ in Iθ, Work.FTS.OpenPkg.WProdWin.TW α θ :=
    setIntegral_nonneg measurableSet_Icc (fun θ hθ => Work.FTS.OpenPkg.WProdWin.TW_nonneg hα.le hθ)
  have hbr : HgInt6 α g z + (gam α - 1)⁻¹ * ∑ d ∈ Finset.range 6,
        Work.FTS.H2.WPQ.Aang α g d z
      ≤ HgInt6 α g z + (gam α - 1)⁻¹ * (6 * HgInt6 α g z) :=
    add_le_add le_rfl (mul_le_mul_of_nonneg_left hsum hγinv)
  have hmain : (HgInt6 α g z + (gam α - 1)⁻¹ * ∑ d ∈ Finset.range 6,
        Work.FTS.H2.WPQ.Aang α g d z) * (∫ θ in Iθ, Work.FTS.OpenPkg.WProdWin.TW α θ)
      ≤ (HgInt6 α g z + (gam α - 1)⁻¹ * (6 * HgInt6 α g z)) * 700 :=
    mul_le_mul hbr hT hTnn
      (add_nonneg (HgInt6_nonneg α g z) (mul_nonneg hγinv (mul_nonneg (by norm_num)
        (HgInt6_nonneg α g z))))
  calc HgInt6 α g z + (HgInt6 α g z + (gam α - 1)⁻¹ * ∑ d ∈ Finset.range 6,
        Work.FTS.H2.WPQ.Aang α g d z) * (∫ θ in Iθ, Work.FTS.OpenPkg.WProdWin.TW α θ)
      ≤ HgInt6 α g z + (HgInt6 α g z + (gam α - 1)⁻¹ * (6 * HgInt6 α g z)) * 700 :=
        add_le_add le_rfl hmain
    _ = (1 + 700 * (1 + 6 * (gam α - 1)⁻¹)) * HgInt6 α g z := by ring

/-- The `z`-integral of the majorant, dominated by `(1 + 700(1 + 6(γ-1)⁻¹)) · HkSq α 6 g`. -/
theorem GmajW6_z_integral_le {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {g : ℝ → ℝ → ℝ}
    (hgm : HkMem α 6 g) :
    (∫ z in Iz, ∫ θ in Iθ, GmajW6 α g z θ)
      ≤ (1 + 700 * (1 + 6 * (gam α - 1)⁻¹)) * HkSq α 6 g := by
  have hγ1 : (0 : ℝ) < gam α - 1 := by rw [gam_sub_one]; linarith
  have hint : IntegrableOn (fun z => (1 + 700 * (1 + 6 * (gam α - 1)⁻¹)) * HgInt6 α g z) Iz :=
    hgm.2.const_mul (1 + 700 * (1 + 6 * (gam α - 1)⁻¹))
  have hle : (∫ z in Iz, ∫ θ in Iθ, GmajW6 α g z θ)
      ≤ ∫ z in Iz, (1 + 700 * (1 + 6 * (gam α - 1)⁻¹)) * HgInt6 α g z :=
    setIntegral_mono_of_nonneg
      (fun z _ => setIntegral_nonneg measurableSet_Icc
        (fun θ hθ => GmajW6_nonneg hα g hθ))
      (fun z hz => GmajW6_theta_integral_le hα hα1 hgm hz) hint
  calc (∫ z in Iz, ∫ θ in Iθ, GmajW6 α g z θ)
      ≤ ∫ z in Iz, (1 + 700 * (1 + 6 * (gam α - 1)⁻¹)) * HgInt6 α g z := hle
    _ = (1 + 700 * (1 + 6 * (gam α - 1)⁻¹)) * HkSq α 6 g := by
        rw [MeasureTheory.integral_const_mul, HgInt6_z_integral]

end Work.FTS.StrongPersist.H6Rows.WProd6
