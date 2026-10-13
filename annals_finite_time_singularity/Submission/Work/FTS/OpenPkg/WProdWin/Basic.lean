/-
# `WProdWin` — the `𝒲^{4,∞}`-priced product rule in the open-quadrant class

This module holds the definitions and the elementary lemmas shared by the pieces of the proof of

```
Work.FTS.OpenPkg.wprod_field_winf :
  ∃ C > 0, ∀ α ∈ (0,1], SmoothOpen f → WlInfMem α 4 f → HQo α 4 g →
    HkMem α 4 (f·g) ∧ Xn α (f·g) ≤ C α^{-1/2} WlInf α 4 f · Xn α g
```

i.e. the `wprod` clause of `Work.FTS.OpenPkg.N4Norm'` (Elgindi's `WProductRule`, tex 1086, with
the coefficient `f` priced by the *weighted* norm `𝒲^{4,∞}` so that it need not itself lie in
`ℋ⁴` — the coefficients `F_*`, `D_θF_*`, `D_zF_*` of the route are of this type).

The pointwise majorant of the product `f·g` is the same as in the proved `Work.FTS.H2.WProdQ`,
except that the radial-Hardy contribution of the `g`-side is replaced by its *mean-term*
counterpart: since the open class has no boundary vanishing of the `g`-slices at `θ = 0, π/2`,
the one-dimensional Hardy inequality is unavailable and one uses
`Work.FTS.OpenPkg.ProdOpen.sob_theta_mean`:

`(D_z^d g(z,θ) w z)² ≤ C (w z² ∫_σ (D_z^d g(z,σ))² + (γ-1)⁻¹ Aang α g d z)`,

whose first term is dominated by `HgInt α g z = ∫_σ HkIntegrand α 4 g z σ`.

Contents:

* `TW` — the angular factor `(α + sin 2θ)² sin(2θ)^{2α/5-γ}` surviving the product of the
  `f`-side bound `(α + sin 2θ) sin(2θ)^{α/5}` with the `g`-weight `sin(2θ)^{-γ}`;
* `HgInt` — the angular integral of the `ℋ⁴`-integrand of `g`;
* `GmajW` — the majorant `HkIntegrand α 4 g + (HgInt + (γ-1)⁻¹ ∑_{d<4} Aang d) · TW`;
* the elementary estimates: nonnegativity, integrability of `TW`, the integral bounds
  `∫_θ TW ≤ 700`, `∑_{d<4} Aang d z ≤ 4 HgInt z`, `w² ∫_σ (D_z^d g)² ≤ HgInt`, and the two
  integral estimates of the majorant.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.H2.WPQ.Defs
import Submission.Work.FTS.H2.WPQ.Final
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.OpenPkg.ProdOpen.SlicesOpen
import Submission.Work.Spaces.WProductRule

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.OpenPkg.WProdWin

open Work.Spaces

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

/-- The angular factor surviving the mixed slots of the `𝒲^{4,∞}`-priced product rule:
`(α + sin 2θ)² sin(2θ)^{2α/5 - γ}`, the product of the squared `f`-side factor
`(α + sin 2θ) sin(2θ)^{α/5}` with the `g`-side weight `sin(2θ)^{-γ}`. -/
def TW (α θ : ℝ) : ℝ :=
  (α + Real.sin (2 * θ)) ^ 2 * (Real.sin (2 * θ)) ^ (2 * α / 5 - gam α)

/-- `HgInt α g z = ∫_θ HkIntegrand α 4 g z θ`, the angular integral of the `ℋ⁴`-integrand of `g`
at fixed radius.  (Its `z`-integral is `HkSq α 4 g` by definition.) -/
def HgInt (α : ℝ) (g : ℝ → ℝ → ℝ) (z : ℝ) : ℝ :=
  ∫ θ in Iθ, HkIntegrand α 4 g z θ

/-- **The pointwise majorant of the `𝒲^{4,∞}`-priced product rule.**

It is the `ℋ⁴`-integrand of `g` plus the angular contribution of the mean-term bound for the
radial slots of `g` (`HgInt`, the mean term) and of the angular `L²`-norms `Aang` of the mixed
slots of `g`, together with the surviving angular factor `TW`. -/
def GmajW (α : ℝ) (g : ℝ → ℝ → ℝ) (z θ : ℝ) : ℝ :=
  HkIntegrand α 4 g z θ
    + (HgInt α g z + (gam α - 1)⁻¹ * ∑ d ∈ Finset.range 4, Work.FTS.H2.WPQ.Aang α g d z)
      * TW α θ

/-! ## Elementary properties of `TW` -/

theorem TW_nonneg {α θ : ℝ} (hα : 0 ≤ α) (hθ : θ ∈ Iθ) : 0 ≤ TW α θ :=
  mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (sin_two_nonneg' hθ) _)

/-- On the open quadrant, `TW` splits as `(α+sin2θ)² sin(2θ)^{2α/5} · sin(2θ)^{-γ}`. -/
theorem TW_eq_mul {α θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    TW α θ = ((α + Real.sin (2 * θ)) ^ 2 * (Real.sin (2 * θ)) ^ (2 * α / 5))
      * (Real.sin (2 * θ)) ^ (-(gam α)) := by
  have hs : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
  rw [TW, mul_assoc, ← Real.rpow_add hs, sub_eq_add_neg]

theorem TW_integrable {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) : IntegrableOn (TW α) Iθ :=
  Work.Spaces.integrableOn_angular_weight hα hα1

theorem TW_integral_le {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) :
    (∫ θ in Iθ, TW α θ) ≤ 700 :=
  Work.Spaces.angular_weight_integral_bound hα hα1

/-! ## Elementary properties of `HgInt` and `GmajW` -/

theorem HgInt_nonneg (α : ℝ) (g : ℝ → ℝ → ℝ) (z : ℝ) : 0 ≤ HgInt α g z :=
  integral_nonneg fun θ => HkIntegrand_nonneg α 4 g z θ

theorem GmajW_nonneg {α : ℝ} (hα : 0 < α) (g : ℝ → ℝ → ℝ) {z θ : ℝ} (hθ : θ ∈ Iθ) :
    0 ≤ GmajW α g z θ := by
  have hγ1 : (0 : ℝ) < gam α - 1 := by rw [gam_sub_one]; linarith
  refine add_nonneg (HkIntegrand_nonneg α 4 g z θ) (mul_nonneg (add_nonneg (HgInt_nonneg α g z)
    (mul_nonneg (inv_nonneg.mpr hγ1.le) (Work.FTS.H2.WPQ.sum_Aang_nonneg α g z)))
    (TW_nonneg hα.le hθ))

/-- The `ℋ⁴`-integrand of `g` is dominated by the majorant. -/
theorem HkIntegrand_le_GmajW {α : ℝ} (hα : 0 < α) (g : ℝ → ℝ → ℝ) {z θ : ℝ}
    (hθ : θ ∈ Iθ) :
    HkIntegrand α 4 g z θ ≤ GmajW α g z θ := by
  have hγ1 : (0 : ℝ) < gam α - 1 := by rw [gam_sub_one]; linarith
  refine le_add_of_nonneg_right (mul_nonneg (add_nonneg (HgInt_nonneg α g z)
    (mul_nonneg (inv_nonneg.mpr hγ1.le) (Work.FTS.H2.WPQ.sum_Aang_nonneg α g z)))
    (TW_nonneg hα.le hθ))

/-- The sum of the angular `L²`-norms of the mixed slots of `g` is dominated by the mean term. -/
theorem sum_Aang_le_HgInt {α : ℝ} {g : ℝ → ℝ → ℝ} (hgm : HkMem α 4 g) {z : ℝ} (hz : z ∈ Iz) :
    ∑ d ∈ Finset.range 4, Work.FTS.H2.WPQ.Aang α g d z ≤ 4 * HgInt α g z :=
  Work.FTS.H2.WPQ.sum_Aang_le α hgm hz

/-- `HgInt` integrates to `HkSq α 4 g` (definitional). -/
theorem HgInt_z_integral (α : ℝ) (g : ℝ → ℝ → ℝ) :
    (∫ z in Iz, HgInt α g z) = HkSq α 4 g := rfl

/-- **The mean term controls the radial slots of `g`**: `w(z)² ∫_σ (D_z^d g(z,σ))² ≤ HgInt z`.

The weight `w/sin(2σ)^{η/2}` is `≥ w ≥ 1` on the open quadrant, so the left-hand side is
pointwise dominated by the `(d,0)`-slot of `HkIntegrand α 4 g`. -/
theorem w_sq_mul_slice_le_HgInt {α : ℝ} {g : ℝ → ℝ → ℝ} (hgm : HkMem α 4 g)
    {d : ℕ} (hd : d ≤ 4) {z : ℝ} (hz : 0 < z) :
    (w z) ^ 2 * (∫ σ in Iθ, (DzIter d g z σ) ^ 2) ≤ HgInt α g z := by
  have hzI : z ∈ Iz := le_of_lt hz
  have hdiv : (w z) ^ 2 * (∫ σ in Iθ, (DzIter d g z σ) ^ 2)
      = ∫ σ in Iθ, (w z) ^ 2 * (DzIter d g z σ) ^ 2 := by
    rw [MeasureTheory.integral_const_mul]
  rw [hdiv]
  refine integral_mono_of_nonneg (Eventually.of_forall fun σ => mul_nonneg (sq_nonneg _) (sq_nonneg _))
    (hgm.1 z hzI) ?_
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
    _ ≤ HkIntegrand α 4 g z σ := by
        rw [mul_one]
        exact sq_le_HkIntegrand_z α 4 g z σ d hd

/-- The angular slice of the majorant is integrable, for every `z ∈ Iz`. -/
theorem GmajW_integrableOn_theta {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {g : ℝ → ℝ → ℝ}
    (hgm : HkMem α 4 g) {z : ℝ} (hz : z ∈ Iz) :
    IntegrableOn (fun θ => GmajW α g z θ) Iθ := by
  have h2 : IntegrableOn (fun θ => (HgInt α g z
      + (gam α - 1)⁻¹ * ∑ d ∈ Finset.range 4, Work.FTS.H2.WPQ.Aang α g d z) * TW α θ) Iθ :=
    (TW_integrable hα hα1).const_mul _
  refine Integrable.congr ((hgm.1 z hz).add h2) ?_
  filter_upwards with θ
  simp only [Pi.add_apply, GmajW]

/-- The angular integral of the majorant at a fixed radius, dominated by the mean term. -/
theorem GmajW_theta_integral_le {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {g : ℝ → ℝ → ℝ}
    (hgm : HkMem α 4 g) {z : ℝ} (hz : z ∈ Iz) :
    (∫ θ in Iθ, GmajW α g z θ) ≤ (1 + 700 * (1 + 4 * (gam α - 1)⁻¹)) * HgInt α g z := by
  have hγ1 : (0 : ℝ) < gam α - 1 := by rw [gam_sub_one]; linarith
  have hγinv : 0 ≤ (gam α - 1)⁻¹ := inv_nonneg.mpr hγ1.le
  have hhg : IntegrableOn (fun θ => HkIntegrand α 4 g z θ) Iθ := hgm.1 z hz
  have hsum : ∑ d ∈ Finset.range 4, Work.FTS.H2.WPQ.Aang α g d z ≤ 4 * HgInt α g z :=
    sum_Aang_le_HgInt hgm hz
  have h2 : IntegrableOn (fun θ => (HgInt α g z
      + (gam α - 1)⁻¹ * ∑ d ∈ Finset.range 4, Work.FTS.H2.WPQ.Aang α g d z) * TW α θ) Iθ :=
    (TW_integrable hα hα1).const_mul _
  have hsplit : (∫ θ in Iθ, GmajW α g z θ)
      = HgInt α g z + (HgInt α g z
          + (gam α - 1)⁻¹ * ∑ d ∈ Finset.range 4, Work.FTS.H2.WPQ.Aang α g d z)
            * (∫ θ in Iθ, TW α θ) := by
    have hfun : (fun θ : ℝ => GmajW α g z θ)
        = fun θ : ℝ => HkIntegrand α 4 g z θ
            + (HgInt α g z + (gam α - 1)⁻¹
                * ∑ d ∈ Finset.range 4, Work.FTS.H2.WPQ.Aang α g d z) * TW α θ := by
      funext θ; rw [GmajW]
    rw [hfun, MeasureTheory.integral_add hhg h2, MeasureTheory.integral_const_mul]
    rfl
  rw [hsplit]
  have hT := TW_integral_le hα hα1
  have hTnn : 0 ≤ ∫ θ in Iθ, TW α θ :=
    setIntegral_nonneg measurableSet_Icc (fun θ hθ => TW_nonneg hα.le hθ)
  have hbr : HgInt α g z + (gam α - 1)⁻¹ * ∑ d ∈ Finset.range 4, Work.FTS.H2.WPQ.Aang α g d z
      ≤ HgInt α g z + (gam α - 1)⁻¹ * (4 * HgInt α g z) :=
    add_le_add le_rfl (mul_le_mul_of_nonneg_left hsum hγinv)
  have hmain : (HgInt α g z + (gam α - 1)⁻¹ * ∑ d ∈ Finset.range 4,
        Work.FTS.H2.WPQ.Aang α g d z) * (∫ θ in Iθ, TW α θ)
      ≤ (HgInt α g z + (gam α - 1)⁻¹ * (4 * HgInt α g z)) * 700 :=
    mul_le_mul hbr hT hTnn
      (add_nonneg (HgInt_nonneg α g z) (mul_nonneg hγinv (mul_nonneg (by norm_num)
        (HgInt_nonneg α g z))))
  calc HgInt α g z + (HgInt α g z + (gam α - 1)⁻¹ * ∑ d ∈ Finset.range 4,
        Work.FTS.H2.WPQ.Aang α g d z) * (∫ θ in Iθ, TW α θ)
      ≤ HgInt α g z + (HgInt α g z + (gam α - 1)⁻¹ * (4 * HgInt α g z)) * 700 :=
        add_le_add le_rfl hmain
    _ = (1 + 700 * (1 + 4 * (gam α - 1)⁻¹)) * HgInt α g z := by ring

/-- The `z`-integral of the majorant, dominated by `(1 + 700(1 + 4(γ-1)⁻¹)) · HkSq α 4 g`. -/
theorem GmajW_z_integral_le {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {g : ℝ → ℝ → ℝ}
    (hgm : HkMem α 4 g) :
    (∫ z in Iz, ∫ θ in Iθ, GmajW α g z θ)
      ≤ (1 + 700 * (1 + 4 * (gam α - 1)⁻¹)) * HkSq α 4 g := by
  have hγ1 : (0 : ℝ) < gam α - 1 := by rw [gam_sub_one]; linarith
  have hint : IntegrableOn (fun z => (1 + 700 * (1 + 4 * (gam α - 1)⁻¹)) * HgInt α g z) Iz :=
    hgm.2.const_mul (1 + 700 * (1 + 4 * (gam α - 1)⁻¹))
  have hle : (∫ z in Iz, ∫ θ in Iθ, GmajW α g z θ)
      ≤ ∫ z in Iz, (1 + 700 * (1 + 4 * (gam α - 1)⁻¹)) * HgInt α g z :=
    setIntegral_mono_of_nonneg
      (fun z _ => setIntegral_nonneg measurableSet_Icc (fun θ hθ => GmajW_nonneg hα g hθ))
      (fun z hz => GmajW_theta_integral_le hα hα1 hgm hz) hint
  calc (∫ z in Iz, ∫ θ in Iθ, GmajW α g z θ)
      ≤ ∫ z in Iz, (1 + 700 * (1 + 4 * (gam α - 1)⁻¹)) * HgInt α g z := hle
    _ = (1 + 700 * (1 + 4 * (gam α - 1)⁻¹)) * HkSq α 4 g := by
        rw [MeasureTheory.integral_const_mul, HgInt_z_integral]

end Work.FTS.OpenPkg.WProdWin
