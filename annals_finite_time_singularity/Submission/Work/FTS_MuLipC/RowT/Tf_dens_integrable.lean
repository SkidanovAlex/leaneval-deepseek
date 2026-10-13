import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Submission.Work.FTS_MuLipC.Defs
import Submission.Work.FTS.Nonlinear.Pieces.rowsAux
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.Spaces.aesm_of_continuousOn_Qd

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS_MuLipC.RowT

set_option autoImplicit false

/-! ## Elementary bounds

Two elementary facts are used repeatedly below: `|K θ| ≤ 3` on the whole line, and
`√(w s) = (1+s)/s` for `s > 0` (the weight is `w s = (1+s)²/s²`). -/

/-- `|K θ| ≤ 3` for every `θ`. -/
lemma abs_K_le_three (θ : ℝ) : |Work.Spaces.K θ| ≤ 3 := by
  have hcos0 : (0 : ℝ) ≤ Real.cos θ ^ 2 := sq_nonneg _
  have hcos1 : Real.cos θ ^ 2 ≤ 1 := by
    nlinarith [Real.sin_sq_add_cos_sq θ, sq_nonneg (Real.sin θ)]
  have hsin : |Real.sin θ| ≤ 1 := Real.abs_sin_le_one θ
  rw [Work.Spaces.K, abs_mul, abs_mul, abs_of_nonneg (show (0 : ℝ) ≤ 3 by norm_num),
    abs_of_nonneg hcos0]
  calc 3 * |Real.sin θ| * Real.cos θ ^ 2
      ≤ 3 * 1 * 1 :=
        mul_le_mul (mul_le_mul_of_nonneg_left hsin (by norm_num : (0 : ℝ) ≤ 3)) hcos1 hcos0
          (by norm_num)
    _ = 3 := by norm_num

/-- `√(w s) = (1+s)/s` for `s > 0`. -/
lemma sqrt_w_eq {s : ℝ} (hs : 0 < s) : Real.sqrt (Work.Spaces.w s) = (1 + s) / s := by
  rw [Work.Spaces.w, Real.sqrt_div' ((1 + s) ^ 2) (by positivity : (0 : ℝ) ≤ s ^ 2),
    Real.sqrt_sq (by linarith : (0 : ℝ) ≤ 1 + s), Real.sqrt_sq (le_of_lt hs)]

/-- `√x ≤ 1 + x` for `x ≥ 0`. -/
lemma sqrt_le_one_add {x : ℝ} (hx : 0 ≤ x) : Real.sqrt x ≤ 1 + x := by
  rw [Real.sqrt_le_iff]
  exact ⟨by linarith, by nlinarith⟩

/-! ## The pointwise bound on the angular integrand

The single pointwise input is `dth_sq_mul_w_le_HkIntegrand`,
`(D_θg s θ)²·w s ≤ HkIntegrand α 4 g s θ` on the open quadrant, together with the identity
`√(w s)·s = 1 + s`. -/

/-- For `s > 0` and `θ ∈ (0,π/2)` the transport integrand is dominated by
`9/(1+s)²·√(HkIntegrand α 4 g s θ)`. -/
lemma abs_K_mul_Tf_le {α s θ : ℝ} (hα : 0 < α) {g : ℝ → ℝ → ℝ} (hs : 0 < s)
    (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    ‖Work.Spaces.K θ * Work.FTS_MuLipC.Tf g s θ / s‖
      ≤ 9 / (1 + s) ^ 2 * Real.sqrt (Work.Spaces.HkIntegrand α 4 g s θ) := by
  have hs0 : s ≠ 0 := ne_of_gt hs
  have hs1 : (1 : ℝ) + s ≠ 0 := by positivity
  have hw : 0 ≤ Work.Spaces.w s := by rw [Work.Spaces.w]; positivity
  -- the `D_θ`-factor: `|D_θ g s θ| ≤ √Hk · s/(1+s)`
  have hkey : (Work.Spaces.Dth g s θ * Real.sqrt (Work.Spaces.w s)) ^ 2
      ≤ Work.Spaces.HkIntegrand α 4 g s θ := by
    have h := Work.FTS.Nonlinear.Pieces.dth_sq_mul_w_le_HkIntegrand α g hα hs hθ
    calc (Work.Spaces.Dth g s θ * Real.sqrt (Work.Spaces.w s)) ^ 2
        = Work.Spaces.Dth g s θ ^ 2 * Work.Spaces.w s := by
          rw [mul_pow, Real.sq_sqrt hw]
      _ ≤ Work.Spaces.HkIntegrand α 4 g s θ := h
  have hDax : |Work.Spaces.Dth g s θ| * ((1 + s) / s)
      ≤ Real.sqrt (Work.Spaces.HkIntegrand α 4 g s θ) := by
    have h := Real.abs_le_sqrt hkey
    rwa [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _), sqrt_w_eq hs] at h
  have hD : |Work.Spaces.Dth g s θ|
      ≤ Real.sqrt (Work.Spaces.HkIntegrand α 4 g s θ) * s / (1 + s) := by
    have hcancel : ((1 + s) / s) * (s / (1 + s)) = 1 := by field_simp
    have hmul := mul_le_mul_of_nonneg_right hDax (by positivity : (0 : ℝ) ≤ s / (1 + s))
    have h1 : (|Work.Spaces.Dth g s θ| * ((1 + s) / s)) * (s / (1 + s))
        = |Work.Spaces.Dth g s θ| := by rw [mul_assoc, hcancel, mul_one]
    calc |Work.Spaces.Dth g s θ|
        = (|Work.Spaces.Dth g s θ| * ((1 + s) / s)) * (s / (1 + s)) := h1.symm
      _ ≤ Real.sqrt (Work.Spaces.HkIntegrand α 4 g s θ) * (s / (1 + s)) := hmul
      _ = Real.sqrt (Work.Spaces.HkIntegrand α 4 g s θ) * s / (1 + s) := by ring
  -- the coefficient
  have hA : ‖Work.Spaces.K θ * 3 / ((1 + s) * s)‖ ≤ 9 / ((1 + s) * s) := by
    have hden : (0 : ℝ) < (1 + s) * s := by positivity
    rw [Real.norm_eq_abs, abs_div, abs_of_pos hden, div_le_div_iff_of_pos_right hden]
    have h2 : |Work.Spaces.K θ * 3| = |Work.Spaces.K θ| * 3 := by
      rw [abs_mul, abs_of_nonneg (show (0 : ℝ) ≤ 3 by norm_num)]
    rw [h2]
    nlinarith [abs_K_le_three θ]
  -- the factorisation `K·Tf/s = (K·3/((1+s)s))·D_θg`
  have hfac : Work.Spaces.K θ * Work.FTS_MuLipC.Tf g s θ / s
      = (Work.Spaces.K θ * 3 / ((1 + s) * s)) * Work.Spaces.Dth g s θ := by
    rw [Work.FTS_MuLipC.Tf_apply]
    field_simp
  calc ‖Work.Spaces.K θ * Work.FTS_MuLipC.Tf g s θ / s‖
      = ‖Work.Spaces.K θ * 3 / ((1 + s) * s)‖ * ‖Work.Spaces.Dth g s θ‖ := by
        rw [hfac, norm_mul]
    _ ≤ (9 / ((1 + s) * s))
          * (Real.sqrt (Work.Spaces.HkIntegrand α 4 g s θ) * s / (1 + s)) :=
        mul_le_mul hA hD (norm_nonneg _) (by positivity)
    _ = 9 / (1 + s) ^ 2 * Real.sqrt (Work.Spaces.HkIntegrand α 4 g s θ) := by
        field_simp

/-! ## The density estimate at fixed `s` -/

/-- For `s > 0` the density of the transport field is bounded by `9/(1+s)²` times the angular
integral of `√(HkIntegrand α 4 g)`. -/
lemma abs_L12dens_Tf_le {α : ℝ} (hα : 0 < α) {g : ℝ → ℝ → ℝ}
    (hmem : Work.Spaces.HkMem α 4 g) {s : ℝ} (hs : 0 < s) :
    |Work.Construction.L12dens (Work.FTS_MuLipC.Tf g) s|
      ≤ 9 / (1 + s) ^ 2
        * ((∫ θ in Work.Spaces.Iθ, (1 : ℝ))
            + ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g s θ) := by
  have hIoo_ae : Work.Spaces.Iθ =ᵐ[volume] Set.Ioo (0 : ℝ) (π / 2) :=
    MeasureTheory.Ioo_ae_eq_Icc.symm
  -- the a.e. pointwise bound on the angular slice
  have hpt : ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ),
      ‖Work.Spaces.K θ * Work.FTS_MuLipC.Tf g s θ / s‖
        ≤ 9 / (1 + s) ^ 2 * Real.sqrt (Work.Spaces.HkIntegrand α 4 g s θ) := by
    rw [MeasureTheory.Measure.restrict_congr_set hIoo_ae]
    exact MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo
      (fun θ hθ => abs_K_mul_Tf_le hα hs hθ)
  -- integrability of the angular pieces
  have hHk : IntegrableOn (fun θ => Work.Spaces.HkIntegrand α 4 g s θ) Work.Spaces.Iθ :=
    hmem.1 s hs.le
  have h1 : IntegrableOn (fun _ : ℝ => (1 : ℝ)) Work.Spaces.Iθ :=
    continuous_const.integrableOn_Icc
  have h1Hk : IntegrableOn (fun θ => (1 : ℝ) + Work.Spaces.HkIntegrand α 4 g s θ)
      Work.Spaces.Iθ := h1.add hHk
  have hsqrt_le : ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ),
      Real.sqrt (Work.Spaces.HkIntegrand α 4 g s θ)
        ≤ 1 + Work.Spaces.HkIntegrand α 4 g s θ :=
    Filter.Eventually.of_forall fun θ =>
      sqrt_le_one_add (Work.Spaces.HkIntegrand_nonneg α 4 g s θ)
  have hsqrt_le_norm : ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ),
      ‖Real.sqrt (Work.Spaces.HkIntegrand α 4 g s θ)‖
        ≤ 1 + Work.Spaces.HkIntegrand α 4 g s θ := by
    filter_upwards [hsqrt_le] with θ hθ
    rwa [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
  have hsqrt_int : IntegrableOn (fun θ => Real.sqrt (Work.Spaces.HkIntegrand α 4 g s θ))
      Work.Spaces.Iθ :=
    h1Hk.mono' (Real.continuous_sqrt.comp_aestronglyMeasurable hHk.aestronglyMeasurable)
      hsqrt_le_norm
  have hInt_le : ∫ θ in Work.Spaces.Iθ, Real.sqrt (Work.Spaces.HkIntegrand α 4 g s θ)
      ≤ ∫ θ in Work.Spaces.Iθ, ((1 : ℝ) + Work.Spaces.HkIntegrand α 4 g s θ) :=
    MeasureTheory.integral_mono_ae hsqrt_int h1Hk hsqrt_le
  have hInt_eq : ∫ θ in Work.Spaces.Iθ, ((1 : ℝ) + Work.Spaces.HkIntegrand α 4 g s θ)
      = (∫ θ in Work.Spaces.Iθ, (1 : ℝ))
        + ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g s θ :=
    MeasureTheory.integral_add h1 hHk
  calc |Work.Construction.L12dens (Work.FTS_MuLipC.Tf g) s|
      = ‖∫ θ in Work.Spaces.Iθ, Work.Spaces.K θ * Work.FTS_MuLipC.Tf g s θ / s‖ := by
        rw [Real.norm_eq_abs]
        congr 1
    _ ≤ ∫ θ in Work.Spaces.Iθ, ‖Work.Spaces.K θ * Work.FTS_MuLipC.Tf g s θ / s‖ :=
        MeasureTheory.norm_integral_le_integral_norm _
    _ ≤ ∫ θ in Work.Spaces.Iθ,
          9 / (1 + s) ^ 2 * Real.sqrt (Work.Spaces.HkIntegrand α 4 g s θ) :=
        MeasureTheory.integral_mono_of_nonneg (Filter.Eventually.of_forall fun θ => norm_nonneg _)
          (hsqrt_int.const_mul _) hpt
    _ = 9 / (1 + s) ^ 2
          * ∫ θ in Work.Spaces.Iθ, Real.sqrt (Work.Spaces.HkIntegrand α 4 g s θ) := by
        rw [MeasureTheory.integral_const_mul]
    _ ≤ 9 / (1 + s) ^ 2
          * ((∫ θ in Work.Spaces.Iθ, (1 : ℝ))
              + ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g s θ) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        rw [← hInt_eq]
        exact hInt_le

/-! ## Integrability of the radial weight -/

/-- `s ↦ (1+s)^{-2}` is integrable on `(0,∞)`. -/
lemma integrableOn_one_add_pow_neg_two :
    IntegrableOn (fun s : ℝ => (1 + s) ^ (-(2 : ℝ))) (Set.Ioi 0) := by
  have h : IntegrableOn (fun s : ℝ => (s + 1) ^ (-(2 : ℝ))) (Set.Ioi 0) :=
    integrableOn_add_rpow_Ioi_of_lt (a := -(2 : ℝ)) (c := 0) (m := 1) (by norm_num)
      (by norm_num)
  refine h.congr_fun (fun s _ => ?_) measurableSet_Ioi
  rw [add_comm]

/-- **The `L₁₂`-density of the transport field is `L¹`.**  For a profile `g` which is `C^∞` on the
open quadrant `(0,∞) × (0,π/2)` (`Work.FTS.EllipticEst.SmoothOpen`) and honestly in `ℋ⁴_α`
(`Work.Spaces.HkMem α 4 g`), the `L₁₂`-density of the transport field
`Work.FTS_MuLipC.Tf g = fun z θ => 3·D_θg z θ/(1+z)`,
`Work.Construction.L12dens (Tf g) = fun s => ∫ θ in Iθ, K θ · Tf g s θ / s`,
is integrable on `(0,∞)`.  This is precisely the `h3`/`h4` input of
`Work.FTS.LocData.L12_add_mul` at the fields `a = Tf f'`, `b = Tf (f - f')`, and together with
`Work.FTS_MuLipC.RowT.Tf_slice_integrable` it is what makes the transport zero-mode additive over
a difference of class-`C` profiles.

Route.  A.e. strong measurability: the integrand `(s,θ) ↦ K θ · Tf g s θ/s` is continuous on the
open quadrant `Q0` (from `hg.Dth.continuousOn`, continuity of `K`, and `s > 0`), so
`Work.Spaces.aesm_of_continuousOn_Qd` + `MeasureTheory.AEStronglyMeasurable.integral_prod_right'`
give it — exactly as in `Work.FTS.GalBasis.cc.aesm_L12dens_of_SmoothOpen` (whose proof can be
copied verbatim with `Tf g` in place of `F`).  Integrability: the pointwise domination
`|D_θg s θ| ≤ √(HkIntegrand α 4 g s θ)/w s` (`s > 0`, `θ ∈ (0,π/2)`, from
`Work.FTS.Nonlinear.Pieces.slot_mixed_le_HkIntegrand` at `(j,i) = (0,1)`, `mixed 0 1 g = D_θ g`,
plus `Wt α s θ = w s·sin(2θ)^{-γ/2}` and `sin(2θ)^{-γ} ≥ 1`) gives, for `s > 0`,
`|L12dens (Tf g) s| ≤ ∫ θ in Iθ, 9s/(1+s)³·√(HkIntegrand α 4 g s θ)
   ≤ 9s/(1+s)³·(π/4 + H s/2)`, `H s := ∫ θ in Iθ, HkIntegrand α 4 g s θ`,
using `‖∫‖ ≤ ∫‖·‖` and `√x ≤ (1+x)/2`.  The majorant is integrable on `(0,∞)`:
`s ↦ s/(1+s)³` is integrable there, and `s/(1+s)³ ≤ 4/27` for `s ≥ 0`, so the second summand is
dominated by `(2/3)·H` with `H` integrable by `hmem.2`. -/
theorem Tf_dens_integrable {α : ℝ} (hα : 0 < α) {g : ℝ → ℝ → ℝ}
    (hg : Work.FTS.EllipticEst.SmoothOpen g) (hmem : Work.Spaces.HkMem α 4 g) :
    MeasureTheory.IntegrableOn (Work.Construction.L12dens (Work.FTS_MuLipC.Tf g))
      (Set.Ioi (0 : ℝ)) := by
  -- a.e. strong measurability of the density, from continuity of the integrand on the quadrant
  have hcontK : Continuous Work.Spaces.K := by
    change Continuous fun θ : ℝ => 3 * Real.sin θ * Real.cos θ ^ 2
    fun_prop
  have hjoint : ContinuousOn (fun p : ℝ × ℝ =>
      Work.Spaces.K p.2 * Work.FTS_MuLipC.Tf g p.1 p.2 / p.1)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) := by
    have hDth : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.Dth g p.1 p.2)
        (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) := hg.Dth.continuousOn
    have hnum : ContinuousOn (fun p : ℝ × ℝ => (3 : ℝ) * Work.Spaces.Dth g p.1 p.2)
        (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) := continuousOn_const.mul hDth
    have hden : ContinuousOn (fun p : ℝ × ℝ => 1 + p.1)
        (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) := continuousOn_const.add continuousOn_fst
    have hTf : ContinuousOn (fun p : ℝ × ℝ => Work.FTS_MuLipC.Tf g p.1 p.2)
        (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) :=
      hnum.div hden (fun p hp => by
        have h1 : (0 : ℝ) < p.1 := (Set.mem_prod.mp hp).1
        positivity)
    have hK2 : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.K p.2)
        (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) := (hcontK.comp continuous_snd).continuousOn
    exact (hK2.mul hTf).div continuousOn_fst (fun p hp => by
      have h1 : (0 : ℝ) < p.1 := (Set.mem_prod.mp hp).1
      positivity)
  have haesm : AEStronglyMeasurable (Work.Construction.L12dens (Work.FTS_MuLipC.Tf g))
      (volume.restrict (Set.Ioi (0 : ℝ))) := by
    have hjointAesm := Work.Spaces.aesm_of_continuousOn_Qd _ hjoint
    have h3 := hjointAesm.integral_prod_right'
    have h4 : AEStronglyMeasurable (Work.Construction.L12dens (Work.FTS_MuLipC.Tf g))
        (volume.restrict Work.Spaces.Iz) := by
      convert h3 using 1
      funext z
      rfl
    rw [MeasureTheory.Measure.restrict_congr_set
      (MeasureTheory.Ioi_ae_eq_Ici (μ := volume) (a := 0))]
    exact h4
  -- the integrable majorant
  set V : ℝ := ∫ θ in Work.Spaces.Iθ, (1 : ℝ) with hV
  set T : ℝ → ℝ := fun s => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g s θ with hT
  set Φ : ℝ → ℝ := fun s => 9 / (1 + s) ^ 2 * (V + T s) with hΦ
  have hT_int : IntegrableOn T (Set.Ioi 0) := by
    rw [hT]
    exact hmem.2.mono_set Set.Ioi_subset_Ici_self
  have hbase : IntegrableOn (fun s : ℝ => (1 + s) ^ (-(2 : ℝ))) (Set.Ioi 0) :=
    integrableOn_one_add_pow_neg_two
  have hVpart : IntegrableOn (fun s : ℝ => 9 / (1 + s) ^ 2 * V) (Set.Ioi 0) := by
    have h : IntegrableOn (fun s : ℝ => (9 * V) * ((1 + s) ^ (-(2 : ℝ)))) (Set.Ioi 0) :=
      hbase.const_mul (9 * V)
    refine h.congr_fun (fun s hs => ?_) measurableSet_Ioi
    have hs0 : (0 : ℝ) < 1 + s := by
      have := Set.mem_Ioi.mp hs
      linarith
    show (9 * V) * ((1 + s) ^ (-((2 : ℕ) : ℝ))) = 9 / (1 + s) ^ 2 * V
    rw [Real.rpow_neg hs0.le, Real.rpow_natCast, div_eq_mul_inv]
    ring
  have hTpart : IntegrableOn (fun s : ℝ => 9 / (1 + s) ^ 2 * T s) (Set.Ioi 0) := by
    have hb : IntegrableOn (fun s : ℝ => 9 * |T s|) (Set.Ioi 0) := hT_int.abs.const_mul 9
    refine hb.mono' ?_ ?_
    · have hcont : ContinuousOn (fun s : ℝ => 9 / (1 + s) ^ 2) (Set.Ioi 0) := by
        refine ContinuousOn.div continuousOn_const
          ((continuousOn_const.add continuousOn_id).pow 2) ?_
        intro s hs
        have hs0 : (0 : ℝ) < 1 + s := by
          have := Set.mem_Ioi.mp hs
          linarith
        positivity
      exact (hcont.aestronglyMeasurable measurableSet_Ioi).mul hT_int.aestronglyMeasurable
    · filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioi] with s hs
      have hspos : (0 : ℝ) < s := Set.mem_Ioi.mp hs
      have hnn : (0 : ℝ) ≤ 9 / (1 + s) ^ 2 := by positivity
      have hle : 9 / (1 + s) ^ 2 ≤ 9 := by
        rw [div_le_iff₀ (by positivity : (0 : ℝ) < (1 + s) ^ 2)]
        nlinarith
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hnn]
      exact mul_le_mul_of_nonneg_right hle (abs_nonneg _)
  have hΦ_int : IntegrableOn Φ (Set.Ioi 0) := by
    have hsum := hVpart.add hTpart
    refine hsum.congr_fun (fun s _ => ?_) measurableSet_Ioi
    show 9 / (1 + s) ^ 2 * V + 9 / (1 + s) ^ 2 * T s = Φ s
    simp only [hΦ]
    ring
  -- assemble
  refine hΦ_int.mono' haesm ?_
  rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioi]
  refine Filter.Eventually.of_forall fun s hs => ?_
  have hs0 : (0 : ℝ) < s := Set.mem_Ioi.mp hs
  rw [Real.norm_eq_abs]
  have hle := abs_L12dens_Tf_le hα hmem hs0
  simp only [hΦ, hV, hT]
  exact hle

end Work.FTS_MuLipC.RowT
