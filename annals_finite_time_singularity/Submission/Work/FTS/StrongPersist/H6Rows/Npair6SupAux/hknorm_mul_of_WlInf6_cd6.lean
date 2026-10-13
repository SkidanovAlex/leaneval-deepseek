/-
# `hknorm_mul_of_WlInf6_cd6` — the norm-priced `𝒲^{6,∞}` product rule with `C^6` data

`Submission/Work/FTS/StrongPersist/H6Rows/wprod6.lean` proves the `α^{-1/2}`-priced product
rule

`HkMem α 6 (f·g) ∧ |f·g|_{ℋ⁶} ≤ C α^{-1/2} |f|_{𝒲^{6,∞}} |g|_{ℋ⁶}`

for `f` of class `SmoothOpen` (i.e. `C^∞` on the open quadrant) and `g ∈ HQo α 6` (which
bundles `SmoothOpen g` with `HkMem α 6 g`).  The consumers of the level-six rows of the
nonlinear estimate only have `C^6` data (`Work.FTS.StrongPersist.H6Rows.piecesC6`), so the
product rule is needed in the `C^6` form proved here: `f`, `g` are only `ContDiffOn ℝ 6` on
`Q0`, and `g` is priced by `HkMem α 6 g` alone.

The proof is the `C^6` shift of `WProd6.wprod6_of_slots`:

* the `ℋ⁶`-membership half is `N0pair6bWork.HkMem_mul_of_WlInf6_cd6`;
* the norm half is assembled from the `C^6` pointwise majorant
  `N0pair6bWork.prod_majorant_cd6` (whose slot inputs are `Cd6.zslot_le_winf6_cd6`,
  `Cd6.dzIter_w_mean_le6_cd6`, `Cd6.mslot_le_winf6_cd6`) exactly as in `WProd6/Assembly6.lean`:
  the angular integral of the product's integrand is bounded by
  `K |f|²_{𝒲^{6,∞}} Kg · HgInt6 α g` with `K = 7 Cz + 49 Cm` and
  `Kg = 1 + 700(1 + 6(γ-1)⁻¹)`, and since `γ - 1 = α/10` and `α ≤ 1` one has
  `Kg ≤ 42701 α⁻¹`, whence `√(K Kg) ≤ √(42701 K) · α^{-1/2}`.

Everything rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongPersist.H6Rows.N0pair6bWork.HkMem_mul_of_WlInf6_cd6
import Submission.Work.FTS.StrongPersist.H6Rows.wprod6

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.H6Rows.Npair6SupAux

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

/-- **The norm half of the `𝒲^{6,∞}`-priced product rule, from the pointwise majorant.**
Given the two `C^6` slot bounds (the seven radial slots against `HkIntegrand α 6 g`, the mixed
slots against `GmajW6 α g`), the `ℋ⁶`-norm of `f·g` is bounded by
`√(42701 (7 Cz + 49 Cm)) · α^{-1/2} · |f|_{𝒲^{6,∞}} · |g|_{ℋ⁶}`. -/
theorem hknorm_mul_aux6 {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {f g : ℝ → ℝ → ℝ}
    (hfs : ContDiffOn ℝ 6 (Function.uncurry f) Work.FTS.EllipticEst.Q0)
    (hfw : Work.Spaces.WlInfMem α 6 f)
    (hgs : ContDiffOn ℝ 6 (Function.uncurry g) Work.FTS.EllipticEst.Q0)
    (hgm : Work.Spaces.HkMem α 6 g)
    {Cz Cm : ℝ} (hCz0 : 0 < Cz) (hCm0 : 0 < Cm)
    (hzslot : ∀ i : ℕ, i ≤ 6 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      (Work.Spaces.DzIter i (fun z θ => f z θ * g z θ) z θ
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
        ≤ Cz * (Work.Spaces.WlInf α 6 f) ^ 2 * Work.Spaces.HkIntegrand α 6 g z θ)
    (hmslot : ∀ I J : ℕ, 1 ≤ I → I + J ≤ 6 → ∀ z θ : ℝ, 0 < z → 0 < θ →
      θ < Real.pi / 2 →
      (Work.Spaces.mixed J I (fun z θ => f z θ * g z θ) z θ * Work.Spaces.Wt α z θ) ^ 2
        ≤ Cm * (Work.Spaces.WlInf α 6 f) ^ 2
            * Work.FTS.StrongPersist.H6Rows.WProd6.GmajW6 α g z θ) :
    Work.Spaces.HkMem α 6 (fun z θ => f z θ * g z θ) ∧
      Work.Spaces.HkNorm α 6 (fun z θ => f z θ * g z θ)
        ≤ Real.sqrt ((7 * Cz + 49 * Cm) * 42701) * α ^ (-(1 / 2 : ℝ))
            * Work.Spaces.WlInf α 6 f * Work.Spaces.HkNorm α 6 g := by
  have hmaj := Work.FTS.StrongPersist.H6Rows.N0pair6bWork.prod_majorant_cd6 hα hα1 hfs hfw
    hgs hgm hCz0 hCm0 hzslot hmslot
  set K : ℝ := 7 * Cz + 49 * Cm with hKdef
  set Kg : ℝ := 1 + 700 * (1 + 6 * (Work.Spaces.gam α - 1)⁻¹) with hKgdef
  have hKpos : 0 < K := by rw [hKdef]; linarith
  have hKgpos : 0 < Kg := by
    rw [hKgdef]
    have h1 : (0 : ℝ) < Work.Spaces.gam α - 1 := by
      rw [Work.Spaces.gam_sub_one]; linarith
    have h2 : 0 ≤ (Work.Spaces.gam α - 1)⁻¹ := inv_nonneg.mpr h1.le
    linarith
  have hWnn : 0 ≤ Work.Spaces.WlInf α 6 f := Work.Spaces.WlInf_nonneg α 6 f hfw
  -- the pointwise majorant, in terms of the local constant `K`
  have hmajor : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α 6 (fun z θ => f z θ * g z θ) z θ
        ≤ K * (Work.Spaces.WlInf α 6 f) ^ 2
            * Work.FTS.StrongPersist.H6Rows.WProd6.GmajW6 α g z θ := by
    intro z hz θ hθ
    rw [hKdef]
    exact hmaj z hz θ hθ
  -- the angular integral of the product's integrand
  have hinner : ∀ z ∈ Work.Spaces.Iz,
      (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 6 (fun z θ => f z θ * g z θ) z θ)
        ≤ K * (Work.Spaces.WlInf α 6 f) ^ 2
            * (Kg * Work.FTS.StrongPersist.H6Rows.WProd6.HgInt6 α g z) := by
    intro z hz
    have hint : IntegrableOn (fun θ => (K * (Work.Spaces.WlInf α 6 f) ^ 2)
        * Work.FTS.StrongPersist.H6Rows.WProd6.GmajW6 α g z θ) Work.Spaces.Iθ :=
      (Work.FTS.StrongPersist.H6Rows.WProd6.GmajW6_integrableOn_theta hα hα1 hgm hz).const_mul _
    have h1 : (∫ θ in Work.Spaces.Iθ,
          Work.Spaces.HkIntegrand α 6 (fun z θ => f z θ * g z θ) z θ)
        ≤ ∫ θ in Work.Spaces.Iθ, (K * (Work.Spaces.WlInf α 6 f) ^ 2)
            * Work.FTS.StrongPersist.H6Rows.WProd6.GmajW6 α g z θ :=
      integral_mono_of_nonneg
        (Eventually.of_forall fun θ => Work.Spaces.HkIntegrand_nonneg α 6 _ z θ) hint
        (ae_restrict_of_forall_mem measurableSet_Icc (fun θ hθ => hmajor z hz θ hθ))
    rw [MeasureTheory.integral_const_mul] at h1
    have h2 : (∫ θ in Work.Spaces.Iθ, Work.FTS.StrongPersist.H6Rows.WProd6.GmajW6 α g z θ)
        ≤ Kg * Work.FTS.StrongPersist.H6Rows.WProd6.HgInt6 α g z := by
      simpa only [hKgdef] using
        Work.FTS.StrongPersist.H6Rows.WProd6.GmajW6_theta_integral_le (α := α) (g := g)
          hα hα1 hgm hz
    calc (∫ θ in Work.Spaces.Iθ,
          Work.Spaces.HkIntegrand α 6 (fun z θ => f z θ * g z θ) z θ)
        ≤ (K * (Work.Spaces.WlInf α 6 f) ^ 2)
            * (∫ θ in Work.Spaces.Iθ,
              Work.FTS.StrongPersist.H6Rows.WProd6.GmajW6 α g z θ) := h1
      _ ≤ (K * (Work.Spaces.WlInf α 6 f) ^ 2)
            * (Kg * Work.FTS.StrongPersist.H6Rows.WProd6.HgInt6 α g z) :=
          mul_le_mul_of_nonneg_left h2 (mul_nonneg hKpos.le (sq_nonneg _))
  have hbdd : ∀ z ∈ Work.Spaces.Iz,
      (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 6 (fun z θ => f z θ * g z θ) z θ)
        ≤ (K * (Work.Spaces.WlInf α 6 f) ^ 2 * Kg)
            * Work.FTS.StrongPersist.H6Rows.WProd6.HgInt6 α g z := by
    intro z hz
    have h1 := hinner z hz
    calc (∫ θ in Work.Spaces.Iθ,
          Work.Spaces.HkIntegrand α 6 (fun z θ => f z θ * g z θ) z θ)
        ≤ K * (Work.Spaces.WlInf α 6 f) ^ 2
            * (Kg * Work.FTS.StrongPersist.H6Rows.WProd6.HgInt6 α g z) := h1
      _ = (K * (Work.Spaces.WlInf α 6 f) ^ 2 * Kg)
            * Work.FTS.StrongPersist.H6Rows.WProd6.HgInt6 α g z := by ring
  have hdom : IntegrableOn (fun z => (K * (Work.Spaces.WlInf α 6 f) ^ 2 * Kg)
      * Work.FTS.StrongPersist.H6Rows.WProd6.HgInt6 α g z) Work.Spaces.Iz :=
    hgm.2.const_mul _
  -- the squared bound
  have hSq : Work.Spaces.HkSq α 6 (fun z θ => f z θ * g z θ)
      ≤ (K * (Work.Spaces.WlInf α 6 f) ^ 2 * Kg) * Work.Spaces.HkSq α 6 g := by
    have h1 : Work.Spaces.HkSq α 6 (fun z θ => f z θ * g z θ)
        ≤ ∫ z in Work.Spaces.Iz, (K * (Work.Spaces.WlInf α 6 f) ^ 2 * Kg)
            * Work.FTS.StrongPersist.H6Rows.WProd6.HgInt6 α g z := by
      rw [Work.Spaces.HkSq]
      exact setIntegral_mono_of_nonneg
        (fun z _ => integral_nonneg fun θ => Work.Spaces.HkIntegrand_nonneg α 6 _ z θ)
        (fun z hz => hbdd z hz) hdom
    refine le_trans h1 ?_
    rw [MeasureTheory.integral_const_mul,
      Work.FTS.StrongPersist.H6Rows.WProd6.HgInt6_z_integral]
  -- the passage to the `ℋ⁶`-norm
  have hXn : Work.Spaces.HkNorm α 6 (fun z θ => f z θ * g z θ)
      ≤ Real.sqrt (K * Kg) * Work.Spaces.WlInf α 6 f * Work.Spaces.HkNorm α 6 g := by
    have h1 : Work.Spaces.HkNorm α 6 (fun z θ => f z θ * g z θ)
        ≤ Real.sqrt ((K * Kg) * (Work.Spaces.WlInf α 6 f) ^ 2
            * Work.Spaces.HkSq α 6 g) := by
      rw [show Work.Spaces.HkNorm α 6 (fun z θ => f z θ * g z θ)
            = Real.sqrt (Work.Spaces.HkSq α 6 (fun z θ => f z θ * g z θ)) from rfl]
      refine Real.sqrt_le_sqrt ?_
      calc Work.Spaces.HkSq α 6 (fun z θ => f z θ * g z θ)
          ≤ (K * (Work.Spaces.WlInf α 6 f) ^ 2 * Kg) * Work.Spaces.HkSq α 6 g := hSq
        _ = (K * Kg) * (Work.Spaces.WlInf α 6 f) ^ 2 * Work.Spaces.HkSq α 6 g := by ring
    refine le_trans h1 (le_of_eq ?_)
    rw [show Work.Spaces.HkNorm α 6 g = Real.sqrt (Work.Spaces.HkSq α 6 g) from rfl,
      Real.sqrt_mul (show (0 : ℝ) ≤ (K * Kg) * (Work.Spaces.WlInf α 6 f) ^ 2 by positivity),
      Real.sqrt_mul (show (0 : ℝ) ≤ K * Kg by positivity),
      Real.sqrt_sq hWnn]
  refine ⟨Work.FTS.StrongPersist.H6Rows.N0pair6bWork.HkMem_mul_of_WlInf6_cd6 hα hα1 hfs hfw
      hgs hgm, ?_⟩
  refine le_trans hXn ?_
  -- `√(K Kg) ≤ √(42701 K) α^{-1/2}`
  have hKg_le : Kg ≤ 42701 * α⁻¹ := by
    have h1 : (0 : ℝ) < Work.Spaces.gam α - 1 := by
      rw [Work.Spaces.gam_sub_one]; linarith
    have hginv : (Work.Spaces.gam α - 1)⁻¹ = 10 / α := by
      rw [Work.Spaces.gam_sub_one, inv_div]
    have hαinv : (1 : ℝ) ≤ α⁻¹ := by rw [one_le_inv₀ hα]; exact hα1
    rw [hKgdef, hginv, div_eq_mul_inv]
    ring_nf
    nlinarith [hαinv]
  have hsqrt : Real.sqrt (K * Kg) ≤ Real.sqrt (42701 * K) * α ^ (-(1 / 2 : ℝ)) := by
    have h1 : K * Kg ≤ 42701 * K * α⁻¹ := by
      calc K * Kg ≤ K * (42701 * α⁻¹) := mul_le_mul_of_nonneg_left hKg_le hKpos.le
        _ = 42701 * K * α⁻¹ := by ring
    refine le_trans (Real.sqrt_le_sqrt h1) ?_
    rw [show (42701 : ℝ) * K * α⁻¹ = (42701 * K) * α⁻¹ from by ring,
      Real.sqrt_mul (show (0 : ℝ) ≤ 42701 * K by positivity),
      Work.FTS.StrongPersist.H6Rows.WProd6.sqrt_inv_eq_rpow_neg_half6 hα]
  have hmain : Real.sqrt (K * Kg) * Work.Spaces.WlInf α 6 f * Work.Spaces.HkNorm α 6 g
      ≤ Real.sqrt (42701 * K) * α ^ (-(1 / 2 : ℝ)) * Work.Spaces.WlInf α 6 f
        * Work.Spaces.HkNorm α 6 g := by
    calc Real.sqrt (K * Kg) * Work.Spaces.WlInf α 6 f * Work.Spaces.HkNorm α 6 g
        = Real.sqrt (K * Kg) * (Work.Spaces.WlInf α 6 f * Work.Spaces.HkNorm α 6 g) := by
          ring
      _ ≤ (Real.sqrt (42701 * K) * α ^ (-(1 / 2 : ℝ)))
            * (Work.Spaces.WlInf α 6 f * Work.Spaces.HkNorm α 6 g) :=
          mul_le_mul_of_nonneg_right hsqrt (mul_nonneg hWnn (Real.sqrt_nonneg _))
      _ = Real.sqrt (42701 * K) * α ^ (-(1 / 2 : ℝ)) * Work.Spaces.WlInf α 6 f
            * Work.Spaces.HkNorm α 6 g := by ring
  refine le_trans hmain ?_
  rw [show K * 42701 = 42701 * K from by ring]

/-- **The `𝒲^{6,∞}`-priced product rule with a norm bound and `C^6` data.**  If `f` is `C^6` on
the open quadrant and of class `𝒲^{6,∞}`, and `g` is `C^6` on the open quadrant and of class
`ℋ⁶`, then `f·g` is of class `ℋ⁶` and
`|f·g|_{ℋ⁶} ≤ C α^{-1/2} |f|_{𝒲^{6,∞}} |g|_{ℋ⁶}`. -/
theorem hknorm_mul_of_WlInf6_cd6 : ∃ C α₂ : ℝ, 0 < C ∧ 0 < α₂ ∧
    ∀ α ∈ Set.Ioc 0 α₂, ∀ f g : ℝ → ℝ → ℝ,
      ContDiffOn ℝ 6 (Function.uncurry f) Work.FTS.EllipticEst.Q0 →
      Work.Spaces.WlInfMem α 6 f →
      ContDiffOn ℝ 6 (Function.uncurry g) Work.FTS.EllipticEst.Q0 →
      Work.Spaces.HkMem α 6 g →
      Work.Spaces.HkMem α 6 (fun z θ => f z θ * g z θ) ∧
      Work.Spaces.HkNorm α 6 (fun z θ => f z θ * g z θ)
        ≤ C * α ^ (-(1 / 2 : ℝ)) * Work.Spaces.WlInf α 6 f * Work.Spaces.HkNorm α 6 g := by
  obtain ⟨Cz, hCz, hZ⟩ := Work.FTS.StrongPersist.H6Rows.N0pair6bWork.Cd6.zslot_le_winf6_cd6
  obtain ⟨CB, _hCB, hCBmean⟩ :=
    Work.FTS.StrongPersist.H6Rows.N0pair6bWork.Cd6.dzIter_w_mean_le6_cd6
  obtain ⟨Cm, hCm, hMx⟩ :=
    Work.FTS.StrongPersist.H6Rows.N0pair6bWork.Cd6.mslot_le_winf6_cd6 CB
  refine ⟨Real.sqrt ((7 * Cz + 49 * Cm) * 42701), 1,
    Real.sqrt_pos.mpr (by positivity), one_pos, ?_⟩
  intro α hαIoc f g hfs hfw hgs hgm
  have hα : 0 < α := hαIoc.1
  have hα1 : α ≤ 1 := hαIoc.2
  exact hknorm_mul_aux6 hα hα1 hfs hfw hgs hgm hCz hCm
    (fun i hi z θ hz hθ0 hθ1 => hZ α f g hα hα1 hfs hfw hgs i hi z θ hz hθ0 hθ1)
    (fun I J hI hIJ z θ hz hθ0 hθ1 => hMx α f g hα hα1 hfs hfw hgs hgm
      (fun d hd z' θ' hz' hθ0' hθ1' =>
        hCBmean α g d hα hα1 hgs hgm hd z' θ' hz' hθ0' hθ1')
      I J hI hIJ z θ hz hθ0 hθ1)

end Work.FTS.StrongPersist.H6Rows.Npair6SupAux
