import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.NonlinRows.Rl1.tools
import Submission.Work.FTS.NonlinRows.Rl1.FaStep
import Submission.Work.FTS.Nonlinear.Pieces.rl1Pieces.PsgEnv

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.NonlinRows.Rl1

noncomputable section
open scoped Real Topology ENNReal
open MeasureTheory Set Filter

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

open Work.FTS.Galerkin (Fn)
open Work.FTS.Nonlinear.Pieces (Fa)

/-! ## Elementary facts about the weights

The two rows `N₄^{gs}`, `N₅^{gs}` carry the radial factor `r/(1+r)²` next to the *energy*
`√Φ(r)` of the datum; after the two Cauchy–Schwarz steps the radial weight to integrate is
`r⁻¹·(r/(1+r)²) = 1/(1+r)²`.  Hence the two elementary integrals below. -/

/-- `r ↦ (1+r)^{-4}` is integrable on `(0,∞)`, with integral at most `2`. -/
theorem integrableOn_inv_one_add_pow4 :
    MeasureTheory.IntegrableOn (fun r : ℝ => (1 / (1 + r)) ^ 4) (Set.Ioi (0 : ℝ)) ∧
      (∫ r in Set.Ioi (0 : ℝ), (1 / (1 + r)) ^ 4) ≤ 2 := by
  obtain ⟨hint, hle⟩ := Work.FTS.H2.InvOneAddSq
  have hmeas : AEStronglyMeasurable (fun r : ℝ => (1 / (1 + r)) ^ 4)
      (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) :=
    ((by fun_prop : Measurable (fun r : ℝ => (1 / (1 + r)) ^ 4))).aestronglyMeasurable
  have hpt : ∀ r ∈ Set.Ioi (0 : ℝ), (1 / (1 + r)) ^ 4 ≤ (1 / (1 + r)) ^ 2 := by
    intro r hr
    have hr0 : (0 : ℝ) < r := hr
    have h1 : (0 : ℝ) < 1 + r := by linarith
    have hx0 : (0 : ℝ) ≤ 1 / (1 + r) := by positivity
    have h3 : 1 / (1 + r) ≤ 1 := by
      rw [div_le_one h1]
      linarith
    have h4 : (1 / (1 + r)) ^ 2 ≤ 1 := pow_le_one₀ hx0 h3
    calc (1 / (1 + r)) ^ 4 = (1 / (1 + r)) ^ 2 * (1 / (1 + r)) ^ 2 := by ring
      _ ≤ (1 / (1 + r)) ^ 2 * 1 := mul_le_mul_of_nonneg_left h4 (pow_nonneg hx0 2)
      _ = (1 / (1 + r)) ^ 2 := by ring
  have hint4 : MeasureTheory.IntegrableOn (fun r : ℝ => (1 / (1 + r)) ^ 4) (Set.Ioi (0 : ℝ)) := by
    refine hint.mono' hmeas ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with r hr
    have h1nn : (0 : ℝ) ≤ (1 / (1 + r)) ^ 4 := by positivity
    rw [Real.norm_of_nonneg h1nn]
    exact hpt r hr
  exact ⟨hint4, (MeasureTheory.integral_mono_ae hint4 hint
    (by filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with r hr
        exact hpt r hr)).trans hle⟩

/-- The square of the `L₁₂`-weight of a radial factor: for `K ≥ 0`,
`∫_0^∞ (r⁻¹ (K r/(1+r)²))² ≤ 2K²`. -/
theorem integrableOn_sq_inv_mul_radial {K : ℝ} (hK : 0 ≤ K) :
    MeasureTheory.IntegrableOn (fun r : ℝ => (r⁻¹ * (K * (r / (1 + r) ^ 2))) ^ 2)
      (Set.Ioi (0 : ℝ)) ∧
    (∫ r in Set.Ioi (0 : ℝ), (r⁻¹ * (K * (r / (1 + r) ^ 2))) ^ 2) ≤ 2 * K ^ 2 := by
  have heq : ∀ r ∈ Set.Ioi (0 : ℝ), (r⁻¹ * (K * (r / (1 + r) ^ 2))) ^ 2
      = K ^ 2 * (1 / (1 + r)) ^ 4 := by
    intro r hr
    have hrpos : (0 : ℝ) < r := hr
    have hr0 : r ≠ 0 := ne_of_gt hrpos
    have h1r : (1 : ℝ) + r ≠ 0 := by positivity
    have hlin : r⁻¹ * (K * (r / (1 + r) ^ 2)) = K * (1 / (1 + r)) ^ 2 := by
      field_simp
    rw [hlin, mul_pow]
    ring
  have hint : MeasureTheory.IntegrableOn (fun r : ℝ => K ^ 2 * (1 / (1 + r)) ^ 4)
      (Set.Ioi (0 : ℝ)) := integrableOn_inv_one_add_pow4.1.const_mul _
  refine ⟨MeasureTheory.IntegrableOn.congr_fun hint (fun r hr => (heq r hr).symm)
      measurableSet_Ioi, ?_⟩
  rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioi heq,
    MeasureTheory.integral_const_mul]
  calc K ^ 2 * (∫ r in Set.Ioi (0 : ℝ), (1 / (1 + r)) ^ 4) ≤ K ^ 2 * 2 :=
        mul_le_mul_of_nonneg_left integrableOn_inv_one_add_pow4.2 (sq_nonneg K)
    _ = 2 * K ^ 2 := by ring

/-! ## The angular energy `Φ₀(g)` of the datum and the pointwise Cauchy–Schwarz for `FK g` -/

/-- The radial energy `Φ₀(g) = ∫_θ (g r θ)²` of the datum is integrable with
`∫_r Φ₀(g) r ≤ |g|²_{ℋ⁴}`. -/
theorem phi0_integrableOn_le {α : ℝ} {g : Fn}
    (hsq : Work.FTS.LocData.SmoothQuad g) (hmem : Work.Spaces.HkMem α 4 g)
    (hsl0 : AEStronglyMeasurable (fun θ => g 0 θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :
    MeasureTheory.IntegrableOn (Work.FTS.Nonlinear.Pieces.rl1Pieces.Phi0 g) (Set.Ioi (0 : ℝ)) ∧
      (∫ r in Set.Ioi (0 : ℝ), Work.FTS.Nonlinear.Pieces.rl1Pieces.Phi0 g r)
        ≤ Work.Spaces.HkSq α 4 g := by
  obtain ⟨h0nn, h1, h2meas, h3int, h3le⟩ :=
    Work.FTS.Nonlinear.Pieces.rl1Pieces.Phi0_props hsq hmem hsl0
  have hle : ∀ᵐ r ∂(MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))),
      Work.FTS.Nonlinear.Pieces.rl1Pieces.Phi0 g r
        ≤ Work.Spaces.w r * Work.FTS.Nonlinear.Pieces.rl1Pieces.Phi0 g r := by
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with r hr
    exact le_mul_of_one_le_left (h0nn r) (one_le_w' hr)
  have hint : MeasureTheory.IntegrableOn
      (Work.FTS.Nonlinear.Pieces.rl1Pieces.Phi0 g) (Set.Ioi (0 : ℝ)) := by
    refine h3int.mono' h2meas.aestronglyMeasurable ?_
    filter_upwards [hle] with r hr
    rw [Real.norm_of_nonneg (h0nn r)]
    exact hr
  exact ⟨hint, (MeasureTheory.integral_mono_ae hint h3int hle).trans h3le⟩

/-- The pointwise Cauchy–Schwarz bound for the angular moment: `(FK g r)² ≤ 16·Φ₀(g)(r)`. -/
theorem FK_sq_le_sixteen_Phi0 {g : Fn} {r : ℝ} (hr : 0 < r)
    (hsl : MeasureTheory.IntegrableOn (fun θ => (g r θ) ^ 2) Work.Spaces.Iθ)
    (haesm : AEStronglyMeasurable (fun θ => g r θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :
    (Work.Construction.FK g r) ^ 2
      ≤ 16 * Work.FTS.Nonlinear.Pieces.rl1Pieces.Phi0 g r := by
  have h1 := FK_g_pt (g := g) hr hsl haesm
  calc (Work.Construction.FK g r) ^ 2 = |Work.Construction.FK g r| ^ 2 := (sq_abs _).symm
    _ ≤ (4 * Real.sqrt (∫ θ in Work.Spaces.Iθ, (g r θ) ^ 2)) ^ 2 :=
        pow_le_pow_left₀ (abs_nonneg _) h1 2
    _ = 16 * (∫ θ in Work.Spaces.Iθ, (g r θ) ^ 2) := by
        rw [mul_pow, Real.sq_sqrt (MeasureTheory.integral_nonneg fun θ => sq_nonneg _)]
        norm_num
    _ = 16 * Work.FTS.Nonlinear.Pieces.rl1Pieces.Phi0 g r := by
        rw [Work.FTS.Nonlinear.Pieces.rl1Pieces.Phi0]

/-! ## The `N₄^{gs}`, `N₅^{gs}` rows -/

/-- Pointwise angular bound for `N₄^{gs}`: `|K θ N₄^{gs}| ≤ 40α² r/(1+r)² |FK g r|`. -/
theorem N4gs_pt {α : ℝ} {g : Fn} (hα : 0 < α) (hα1 : α ≤ 1) :
    ∀ r, 0 < r → ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      |Work.Spaces.K θ * Work.FTS.Nonlin.N4gs α g r θ|
        ≤ (40 * α ^ 2 * (r / (1 + r) ^ 2)) * |Work.Construction.FK g r| := by
  intro r hr θ hθ
  have h1 := K_pthFstar_pt (α := α) (r := r) (θ := θ) hα hα1 hr hθ.1 hθ.2
  have hs2 : |Work.Construction.s2 θ| ≤ 1 := by
    rw [show Work.Construction.s2 θ = Real.sin (2 * θ) from rfl]
    exact abs_le.mpr ⟨Real.neg_one_le_sin _, Real.sin_le_one _⟩
  have hFKnn : (0 : ℝ) ≤ |Work.Construction.FK g r| := abs_nonneg _
  have habs : |Work.Spaces.K θ * Work.FTS.Nonlin.N4gs α g r θ|
      = (1 / 2) * (|Work.Construction.s2 θ|
          * |Work.Spaces.K θ * Work.Spaces.pth (Work.Construction.Fstar α) r θ|)
        * |Work.Construction.FK g r| := by
    simp only [Work.FTS.Nonlin.N4gs, abs_mul, abs_neg,
      abs_of_nonneg (by norm_num : (0 : ℝ) ≤ (1 / 2 : ℝ))]
    ring
  rw [habs]
  have hstep : |Work.Construction.s2 θ|
        * |Work.Spaces.K θ * Work.Spaces.pth (Work.Construction.Fstar α) r θ|
      ≤ 1 * (80 * α ^ 2 * (r / (1 + r) ^ 2)) :=
    mul_le_mul hs2 h1 (abs_nonneg _) (by norm_num)
  calc (1 / 2) * (|Work.Construction.s2 θ|
        * |Work.Spaces.K θ * Work.Spaces.pth (Work.Construction.Fstar α) r θ|)
        * |Work.Construction.FK g r|
      ≤ (1 / 2) * (1 * (80 * α ^ 2 * (r / (1 + r) ^ 2)))
          * |Work.Construction.FK g r| := by
        refine mul_le_mul_of_nonneg_right ?_ hFKnn
        exact mul_le_mul_of_nonneg_left hstep (by norm_num)
    _ = 40 * α ^ 2 * (r / (1 + r) ^ 2) * |Work.Construction.FK g r| := by ring

/-- Pointwise angular bound for `N₅^{gs}`: `|K θ N₅^{gs}| ≤ 60α r/(1+r)² |FK g r|`. -/
theorem N5gs_pt {α : ℝ} {g : Fn} (hα : 0 < α) (hα1 : α ≤ 1) :
    ∀ r, 0 < r → ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      |Work.Spaces.K θ * Work.FTS.Nonlin.N5gs α g r θ|
        ≤ (60 * α * (r / (1 + r) ^ 2)) * |Work.Construction.FK g r| := by
  intro r hr θ hθ
  have hFKnn : (0 : ℝ) ≤ |Work.Construction.FK g r| := abs_nonneg _
  have hK : |Work.Spaces.K θ| ≤ 3 := Work.FTS.Nonlinear.Pieces.rl1Pieces.abs_K_le_three θ
  have hsin : (Real.sin θ) ^ 2 ≤ 1 := by
    have h0 : 0 ≤ Real.sin θ :=
      Real.sin_nonneg_of_mem_Icc ⟨hθ.1.le, by linarith [hθ.2, Real.pi_pos]⟩
    nlinarith [Real.sin_le_one θ, sq_nonneg (Real.sin θ)]
  have hF := Fstar_pt (α := α) (z := r) (θ := θ) hα hα1 hr ⟨hθ.1.le, hθ.2.le⟩
  have hFnn : (0 : ℝ) ≤ 20 * α * r / (1 + r) ^ 2 := by positivity
  have habs : |Work.Spaces.K θ * Work.FTS.Nonlin.N5gs α g r θ|
      = (Real.sin θ) ^ 2 * |Work.Spaces.K θ| * |Work.Construction.FK g r|
        * |Work.Construction.Fstar α r θ| := by
    simp only [Work.FTS.Nonlin.N5gs, abs_mul, abs_neg,
      abs_of_nonneg (sq_nonneg (Real.sin θ))]
    ring
  rw [habs]
  have hstep : (Real.sin θ) ^ 2 * |Work.Spaces.K θ| * |Work.Construction.FK g r|
      ≤ 1 * 3 * |Work.Construction.FK g r| := by
    calc (Real.sin θ) ^ 2 * |Work.Spaces.K θ| * |Work.Construction.FK g r|
        ≤ (1 * 3) * |Work.Construction.FK g r| :=
          mul_le_mul (mul_le_mul hsin hK (abs_nonneg _) (by norm_num)) le_rfl
            (abs_nonneg _) (by norm_num)
      _ = 1 * 3 * |Work.Construction.FK g r| := by ring
  calc (Real.sin θ) ^ 2 * |Work.Spaces.K θ| * |Work.Construction.FK g r|
        * |Work.Construction.Fstar α r θ|
      ≤ (1 * 3 * |Work.Construction.FK g r|) * (20 * α * r / (1 + r) ^ 2) :=
        mul_le_mul hstep hF (abs_nonneg _) (by norm_num)
    _ = 60 * α * (r / (1 + r) ^ 2) * |Work.Construction.FK g r| := by ring

/-- **The `r`-step engine for the two `FK(g)`-rows.**  If `|K θ N r θ| ≤ c r · |FK g r|`
pointwise, then `Fa N` is bounded by the two Cauchy–Schwarz losses: the `θ`-energy `Φ₀(g)`
and the radial integral of `(r⁻¹c)²`. -/
theorem Fa_gs_le {α : ℝ} {g : Fn} (hα : 0 < α) (hα1 : α ≤ 1)
    (hsq : Work.FTS.LocData.SmoothQuad g) (hmem : Work.Spaces.HkMem α 4 g)
    (hsl0 : AEStronglyMeasurable (fun θ => g 0 θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ))
    {N : ℝ → ℝ → ℝ} {c : ℝ → ℝ}
    (hc : ∀ r, 0 < r → 0 ≤ c r)
    (hcmeas : AEMeasurable (fun r => r⁻¹ * c r)
      (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))))
    (hcint : MeasureTheory.IntegrableOn (fun r => (r⁻¹ * c r) ^ 2) (Set.Ioi (0 : ℝ)))
    (hpt : ∀ r, 0 < r → ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      |Work.Spaces.K θ * N r θ| ≤ c r * |Work.Construction.FK g r|) :
    Fa N ≤ ENNReal.ofReal (Real.pi / 2 * (4 * Real.sqrt (∫ r in Set.Ioi (0 : ℝ),
        Work.FTS.Nonlinear.Pieces.rl1Pieces.Phi0 g r)
      * Real.sqrt (∫ r in Set.Ioi (0 : ℝ), (r⁻¹ * c r) ^ 2))) := by
  obtain ⟨hΦnn, hslsq, hΦmeas, _hΦintw, _hΦlew⟩ :=
    Work.FTS.Nonlinear.Pieces.rl1Pieces.Phi0_props hsq hmem hsl0
  obtain ⟨hΦint, _hΦle⟩ := phi0_integrableOn_le hsq hmem hsl0
  have hMle : ∀ r, 0 < r → (|Work.Construction.FK g r|) ^ 2
      ≤ 16 * Work.FTS.Nonlinear.Pieces.rl1Pieces.Phi0 g r := by
    intro r hr
    have h := FK_sq_le_sixteen_Phi0 (g := g) hr (hslsq r hr)
      (Work.FTS.Nonlinear.Pieces.rl1Pieces.aesm_slice_of_smoothQuad hsq hr)
    simpa only [sq_abs] using h
  have hmain := Fa_le_of_profile (N := N) (c := c) (M := fun r => |Work.Construction.FK g r|)
    (Ψ := Work.FTS.Nonlinear.Pieces.rl1Pieces.Phi0 g) (C := 16)
    (by norm_num) hc (fun r => abs_nonneg _) hΦnn hΦmeas hΦint hcmeas hcint hMle hpt
  have hs16 : Real.sqrt (16 : ℝ) = 4 := by
    rw [show (16 : ℝ) = 4 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  rwa [hs16] at hmain

/-- Row 21: `N₄^{gs} = -(1/2) sin(2θ) FK(g) ∂_θF_*`, rate `O(α·|g|_{ℋ⁴})`. -/
theorem row4gs_le {α : ℝ} {g : Fn} (hα : 0 < α) (hα1 : α ≤ 1)
    (hsq : Work.FTS.LocData.SmoothQuad g) (hmem : Work.Spaces.HkMem α 4 g)
    (hsl0 : AEStronglyMeasurable (fun θ => g 0 θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :
    Fa (Work.FTS.Nonlin.N4gs α g)
      ≤ ENNReal.ofReal (500 * α * Work.FTS.Nonlin.Xn α g) := by
  have hinte := integrableOn_sq_inv_mul_radial (K := 40 * α ^ 2) (by positivity)
  have hbase := Fa_gs_le (α := α) (g := g) hα hα1 hsq hmem hsl0
    (N := Work.FTS.Nonlin.N4gs α g) (c := fun r => 40 * α ^ 2 * (r / (1 + r) ^ 2))
    (fun r hr => by positivity)
    (by
      have h : Measurable (fun r : ℝ => r⁻¹ * (40 * α ^ 2 * (r / (1 + r) ^ 2))) := by fun_prop
      exact h.aemeasurable)
    hinte.1
    (fun r hr θ hθ => N4gs_pt (α := α) (g := g) hα hα1 r hr θ hθ)
  refine hbase.trans (ENNReal.ofReal_le_ofReal ?_)
  have hX0 : 0 ≤ Work.FTS.Nonlin.Xn α g := Work.Spaces.HkNorm_nonneg α 4 g
  have hPhi := phi0_integrableOn_le hsq hmem hsl0
  have hA : Real.sqrt (∫ r in Set.Ioi (0 : ℝ),
        Work.FTS.Nonlinear.Pieces.rl1Pieces.Phi0 g r) ≤ Work.FTS.Nonlin.Xn α g := by
    rw [Work.FTS.Nonlin.Xn, Work.Spaces.HkNorm]
    exact Real.sqrt_le_sqrt hPhi.2
  have hB : Real.sqrt (∫ r in Set.Ioi (0 : ℝ),
        (r⁻¹ * (40 * α ^ 2 * (r / (1 + r) ^ 2))) ^ 2) ≤ 57 * α ^ 2 := by
    refine (Real.sqrt_le_sqrt hinte.2).trans ?_
    rw [show (2 : ℝ) * (40 * α ^ 2) ^ 2 = 3200 * (α ^ 2) ^ 2 by ring,
      Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 3200), Real.sqrt_sq (sq_nonneg α)]
    have h3200 : Real.sqrt (3200 : ℝ) ≤ 57 := by
      refine (Real.sqrt_le_sqrt (by norm_num : (3200 : ℝ) ≤ 57 ^ 2)).trans_eq ?_
      rw [Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 57)]
    exact mul_le_mul_of_nonneg_right h3200 (sq_nonneg α)
  have hAB : Real.sqrt (∫ r in Set.Ioi (0 : ℝ),
        Work.FTS.Nonlinear.Pieces.rl1Pieces.Phi0 g r)
      * Real.sqrt (∫ r in Set.Ioi (0 : ℝ), (r⁻¹ * (40 * α ^ 2 * (r / (1 + r) ^ 2))) ^ 2)
      ≤ Work.FTS.Nonlin.Xn α g * (57 * α ^ 2) :=
    mul_le_mul hA hB (Real.sqrt_nonneg _) hX0
  have hα2 : α ^ 2 * Work.FTS.Nonlin.Xn α g ≤ α * Work.FTS.Nonlin.Xn α g := by
    have h : α ^ 2 ≤ α := by nlinarith
    exact mul_le_mul_of_nonneg_right h hX0
  calc Real.pi / 2 * (4 * Real.sqrt (∫ r in Set.Ioi (0 : ℝ),
          Work.FTS.Nonlinear.Pieces.rl1Pieces.Phi0 g r)
        * Real.sqrt (∫ r in Set.Ioi (0 : ℝ),
            (r⁻¹ * (40 * α ^ 2 * (r / (1 + r) ^ 2))) ^ 2))
      ≤ Real.pi / 2 * (4 * (Work.FTS.Nonlin.Xn α g * (57 * α ^ 2))) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        rw [show (4 : ℝ) * Real.sqrt (∫ r in Set.Ioi (0 : ℝ),
              Work.FTS.Nonlinear.Pieces.rl1Pieces.Phi0 g r)
            * Real.sqrt (∫ r in Set.Ioi (0 : ℝ),
                (r⁻¹ * (40 * α ^ 2 * (r / (1 + r) ^ 2))) ^ 2)
            = 4 * (Real.sqrt (∫ r in Set.Ioi (0 : ℝ),
                Work.FTS.Nonlinear.Pieces.rl1Pieces.Phi0 g r)
              * Real.sqrt (∫ r in Set.Ioi (0 : ℝ),
                  (r⁻¹ * (40 * α ^ 2 * (r / (1 + r) ^ 2))) ^ 2)) from by ring]
        exact mul_le_mul_of_nonneg_left hAB (by norm_num)
    _ = 114 * Real.pi * (α ^ 2 * Work.FTS.Nonlin.Xn α g) := by ring
    _ ≤ 114 * 4 * (α ^ 2 * Work.FTS.Nonlin.Xn α g) := by
        have h0 : (0 : ℝ) ≤ α ^ 2 * Work.FTS.Nonlin.Xn α g := mul_nonneg (sq_nonneg α) hX0
        nlinarith [Real.pi_lt_four, h0]
    _ = 456 * (α ^ 2 * Work.FTS.Nonlin.Xn α g) := by ring
    _ ≤ 456 * (α * Work.FTS.Nonlin.Xn α g) := mul_le_mul_of_nonneg_left hα2 (by norm_num)
    _ ≤ 500 * (α * Work.FTS.Nonlin.Xn α g) := by
        have h0 : (0 : ℝ) ≤ α * Work.FTS.Nonlin.Xn α g := mul_nonneg hα.le hX0
        linarith
    _ = 500 * α * Work.FTS.Nonlin.Xn α g := by ring

/-- Row 25a: `N₅^{gs} = -sin²θ FK(g) F_*`, rate `O(α·|g|_{ℋ⁴})`. -/
theorem row5gs_le {α : ℝ} {g : Fn} (hα : 0 < α) (hα1 : α ≤ 1)
    (hsq : Work.FTS.LocData.SmoothQuad g) (hmem : Work.Spaces.HkMem α 4 g)
    (hsl0 : AEStronglyMeasurable (fun θ => g 0 θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :
    Fa (Work.FTS.Nonlin.N5gs α g)
      ≤ ENNReal.ofReal (700 * α * Work.FTS.Nonlin.Xn α g) := by
  have hinte := integrableOn_sq_inv_mul_radial (K := 60 * α) (by positivity)
  have hbase := Fa_gs_le (α := α) (g := g) hα hα1 hsq hmem hsl0
    (N := Work.FTS.Nonlin.N5gs α g) (c := fun r => 60 * α * (r / (1 + r) ^ 2))
    (fun r hr => by positivity)
    (by
      have h : Measurable (fun r : ℝ => r⁻¹ * (60 * α * (r / (1 + r) ^ 2))) := by fun_prop
      exact h.aemeasurable)
    hinte.1
    (fun r hr θ hθ => N5gs_pt (α := α) (g := g) hα hα1 r hr θ hθ)
  refine hbase.trans (ENNReal.ofReal_le_ofReal ?_)
  have hX0 : 0 ≤ Work.FTS.Nonlin.Xn α g := Work.Spaces.HkNorm_nonneg α 4 g
  have hPhi := phi0_integrableOn_le hsq hmem hsl0
  have hA : Real.sqrt (∫ r in Set.Ioi (0 : ℝ),
        Work.FTS.Nonlinear.Pieces.rl1Pieces.Phi0 g r) ≤ Work.FTS.Nonlin.Xn α g := by
    rw [Work.FTS.Nonlin.Xn, Work.Spaces.HkNorm]
    exact Real.sqrt_le_sqrt hPhi.2
  have hB : Real.sqrt (∫ r in Set.Ioi (0 : ℝ),
        (r⁻¹ * (60 * α * (r / (1 + r) ^ 2))) ^ 2) ≤ 85 * α := by
    refine (Real.sqrt_le_sqrt hinte.2).trans ?_
    rw [show (2 : ℝ) * (60 * α) ^ 2 = 7200 * α ^ 2 by ring,
      Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 7200), Real.sqrt_sq hα.le]
    have h7200 : Real.sqrt (7200 : ℝ) ≤ 85 := by
      refine (Real.sqrt_le_sqrt (by norm_num : (7200 : ℝ) ≤ 85 ^ 2)).trans_eq ?_
      rw [Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 85)]
    exact mul_le_mul_of_nonneg_right h7200 hα.le
  have hAB : Real.sqrt (∫ r in Set.Ioi (0 : ℝ),
        Work.FTS.Nonlinear.Pieces.rl1Pieces.Phi0 g r)
      * Real.sqrt (∫ r in Set.Ioi (0 : ℝ), (r⁻¹ * (60 * α * (r / (1 + r) ^ 2))) ^ 2)
      ≤ Work.FTS.Nonlin.Xn α g * (85 * α) :=
    mul_le_mul hA hB (Real.sqrt_nonneg _) hX0
  calc Real.pi / 2 * (4 * Real.sqrt (∫ r in Set.Ioi (0 : ℝ),
          Work.FTS.Nonlinear.Pieces.rl1Pieces.Phi0 g r)
        * Real.sqrt (∫ r in Set.Ioi (0 : ℝ),
            (r⁻¹ * (60 * α * (r / (1 + r) ^ 2))) ^ 2))
      ≤ Real.pi / 2 * (4 * (Work.FTS.Nonlin.Xn α g * (85 * α))) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        rw [show (4 : ℝ) * Real.sqrt (∫ r in Set.Ioi (0 : ℝ),
              Work.FTS.Nonlinear.Pieces.rl1Pieces.Phi0 g r)
            * Real.sqrt (∫ r in Set.Ioi (0 : ℝ),
                (r⁻¹ * (60 * α * (r / (1 + r) ^ 2))) ^ 2)
            = 4 * (Real.sqrt (∫ r in Set.Ioi (0 : ℝ),
                Work.FTS.Nonlinear.Pieces.rl1Pieces.Phi0 g r)
              * Real.sqrt (∫ r in Set.Ioi (0 : ℝ),
                  (r⁻¹ * (60 * α * (r / (1 + r) ^ 2))) ^ 2)) from by ring]
        exact mul_le_mul_of_nonneg_left hAB (by norm_num)
    _ = 170 * Real.pi * (α * Work.FTS.Nonlin.Xn α g) := by ring
    _ ≤ 170 * 4 * (α * Work.FTS.Nonlin.Xn α g) := by
        have h0 : (0 : ℝ) ≤ α * Work.FTS.Nonlin.Xn α g := mul_nonneg hα.le hX0
        nlinarith [Real.pi_lt_four, h0]
    _ = 680 * (α * Work.FTS.Nonlin.Xn α g) := by ring
    _ ≤ 700 * (α * Work.FTS.Nonlin.Xn α g) := by
        have h0 : (0 : ℝ) ≤ α * Work.FTS.Nonlin.Xn α g := mul_nonneg hα.le hX0
        linarith
    _ = 700 * α * Work.FTS.Nonlin.Xn α g := by ring

/-! ## The `N₄^{sg}`, `N₅^{sg}` rows -/

/-- Pointwise angular bound for `N₄^{sg}`: `|K θ N₄^{sg}| ≤ 3α (r/(1+r)²)|∂_θg|`. -/
theorem N4sg_pt {α : ℝ} {g : Fn} (hα : 0 < α) (hα1 : α ≤ 1) :
    ∀ r, 0 < r → ∀ θ ∈ Work.Spaces.Iθ,
      |Work.Spaces.K θ * Work.FTS.Nonlin.N4sg α g r θ|
        ≤ (3 * α) * (r / (1 + r) ^ 2) * |Work.Spaces.pth g r θ| := by
  intro r hr θ hθ
  have hFK := FK_Fstar_pt (α := α) (z := r) hα hα1
  have hK : |Work.Spaces.K θ| ≤ 3 := Work.FTS.Nonlinear.Pieces.rl1Pieces.abs_K_le_three θ
  have hs2 : |Work.Construction.s2 θ| ≤ 1 := by
    rw [show Work.Construction.s2 θ = Real.sin (2 * θ) from rfl]
    exact abs_le.mpr ⟨Real.neg_one_le_sin _, Real.sin_le_one _⟩
  have hDth : |Work.Spaces.Dth g r θ| ≤ |Work.Spaces.pth g r θ| := by
    show |Work.Construction.s2 θ * Work.Spaces.pth g r θ| ≤ |Work.Spaces.pth g r θ|
    rw [abs_mul]
    calc |Work.Construction.s2 θ| * |Work.Spaces.pth g r θ| ≤ 1 * |Work.Spaces.pth g r θ| :=
          mul_le_mul_of_nonneg_right hs2 (abs_nonneg _)
      _ = |Work.Spaces.pth g r θ| := one_mul _
  have hFKabs : |Work.Construction.FK (Work.Construction.Fstar α) r|
      = α * (2 * r / (1 + r) ^ 2) := by
    rw [hFK, abs_of_nonneg (mul_nonneg hα.le (by positivity))]
  have hPK : 0 ≤ |Work.Spaces.pth g r θ| := abs_nonneg _
  have habs : |Work.Spaces.K θ * Work.FTS.Nonlin.N4sg α g r θ|
      = (1 / 2) * |Work.Spaces.K θ|
        * |Work.Construction.FK (Work.Construction.Fstar α) r|
        * |Work.Spaces.Dth g r θ| := by
    simp only [Work.FTS.Nonlin.N4sg, abs_mul, abs_neg,
      abs_of_nonneg (by norm_num : (0 : ℝ) ≤ (1 / 2 : ℝ))]
    ring
  rw [habs, hFKabs]
  have hKD : |Work.Spaces.K θ| * |Work.Spaces.Dth g r θ| ≤ 3 * |Work.Spaces.pth g r θ| :=
    (mul_le_mul hK hDth (abs_nonneg _) (by norm_num)).trans_eq (by ring)
  calc (1 / 2) * |Work.Spaces.K θ| * (α * (2 * r / (1 + r) ^ 2))
        * |Work.Spaces.Dth g r θ|
      = α * (r / (1 + r) ^ 2) * (|Work.Spaces.K θ| * |Work.Spaces.Dth g r θ|) := by ring
    _ ≤ α * (r / (1 + r) ^ 2) * (3 * |Work.Spaces.pth g r θ|) :=
        mul_le_mul_of_nonneg_left hKD (by positivity)
    _ = (3 * α) * (r / (1 + r) ^ 2) * |Work.Spaces.pth g r θ| := by ring

/-- Pointwise angular bound for `N₅^{sg}`: `|K θ N₅^{sg}| ≤ 6α (r/(1+r)²)|g|`. -/
theorem N5sg_pt {α : ℝ} {g : Fn} (hα : 0 < α) (hα1 : α ≤ 1) :
    ∀ r, 0 < r → ∀ θ ∈ Work.Spaces.Iθ,
      |Work.Spaces.K θ * Work.FTS.Nonlin.N5sg α g r θ|
        ≤ (6 * α) * (r / (1 + r) ^ 2) * |g r θ| := by
  intro r hr θ hθ
  have hFK := FK_Fstar_pt (α := α) (z := r) hα hα1
  have hK : |Work.Spaces.K θ| ≤ 3 := Work.FTS.Nonlinear.Pieces.rl1Pieces.abs_K_le_three θ
  have hsin : (Real.sin θ) ^ 2 ≤ 1 := by
    have h0 : 0 ≤ Real.sin θ := Real.sin_nonneg_of_mem_Icc ⟨hθ.1, by linarith [hθ.2, Real.pi_pos]⟩
    nlinarith [Real.sin_le_one θ, sq_nonneg (Real.sin θ)]
  have hFKabs : |Work.Construction.FK (Work.Construction.Fstar α) r|
      = α * (2 * r / (1 + r) ^ 2) := by
    rw [hFK, abs_of_nonneg (mul_nonneg hα.le (by positivity))]
  have habs : |Work.Spaces.K θ * Work.FTS.Nonlin.N5sg α g r θ|
      = (Real.sin θ) ^ 2 * |Work.Spaces.K θ|
        * |Work.Construction.FK (Work.Construction.Fstar α) r| * |g r θ| := by
    simp only [Work.FTS.Nonlin.N5sg, abs_mul, abs_neg,
      abs_of_nonneg (sq_nonneg (Real.sin θ))]
    ring
  rw [habs, hFKabs]
  have hKg : (Real.sin θ) ^ 2 * |Work.Spaces.K θ| * (α * (2 * r / (1 + r) ^ 2)) * |g r θ|
      ≤ (6 * α) * (r / (1 + r) ^ 2) * |g r θ| := by
    have h1 : (Real.sin θ) ^ 2 * |Work.Spaces.K θ| ≤ 3 := by nlinarith [hK, hsin]
    have h2 : (Real.sin θ) ^ 2 * |Work.Spaces.K θ| * (α * (2 * r / (1 + r) ^ 2))
        ≤ 3 * (α * (2 * r / (1 + r) ^ 2)) :=
      mul_le_mul_of_nonneg_right h1 (by positivity)
    calc (Real.sin θ) ^ 2 * |Work.Spaces.K θ| * (α * (2 * r / (1 + r) ^ 2)) * |g r θ|
        ≤ (3 * (α * (2 * r / (1 + r) ^ 2))) * |g r θ| :=
          mul_le_mul_of_nonneg_right h2 (abs_nonneg _)
      _ = (6 * α) * (r / (1 + r) ^ 2) * |g r θ| := by ring
  exact hKg

/-- Row 22: `N₄^{sg} = -(1/2) FK(F_*) D_θg`, rate `O(√α·|g|_{ℋ⁴})`. -/
theorem row4sg_le {α : ℝ} {g : Fn} (hα : 0 < α) (hα1 : α ≤ 1)
    (hsq : Work.FTS.LocData.SmoothQuad g) (hmem : Work.Spaces.HkMem α 4 g) :
    Fa (Work.FTS.Nonlin.N4sg α g)
      ≤ ENNReal.ofReal (100 * Real.sqrt α * Work.FTS.Nonlin.Xn α g) := by
  have hbase := Work.FTS.Nonlinear.Pieces.rl1Pieces.rl1_row_le_radial
    (N := Work.FTS.Nonlin.N4sg α g) (k := Work.Spaces.pth g) (c := 3 * α)
    (by positivity)
    (fun r hr θ hθ => N4sg_pt (α := α) (g := g) hα hα1 r hr θ hθ)
    (Work.FTS.Nonlinear.Pieces.rl1Pieces.envPth hα hα1 hsq hmem)
  have hFa : Fa (Work.FTS.Nonlin.N4sg α g)
      = (∫⁻ r in Set.Ioi (0 : ℝ), ENNReal.ofReal r⁻¹ * (∫⁻ θ in Work.Spaces.Iθ,
          ENNReal.ofReal |Work.Spaces.K θ * Work.FTS.Nonlin.N4sg α g r θ|)) := rfl
  rw [hFa]
  have hX0 : 0 ≤ Work.FTS.Nonlin.Xn α g := Work.Spaces.HkNorm_nonneg α 4 g
  have hstep : ENNReal.ofReal (3 * α)
        * ENNReal.ofReal (10 * Real.sqrt (10 / α) * Work.FTS.Nonlin.Xn α g)
      ≤ ENNReal.ofReal (100 * Real.sqrt α * Work.FTS.Nonlin.Xn α g) := by
    rw [← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 3 * α)]
    refine ENNReal.ofReal_le_ofReal ?_
    have hmul := Work.FTS.Nonlinear.Pieces.rl1Pieces.alpha_mul_sqrt_div hα
    have hs10 : Real.sqrt 10 ≤ 10 / 3 := by
      refine (Real.sqrt_le_sqrt (by norm_num : (10 : ℝ) ≤ (10 / 3) ^ 2)).trans_eq ?_
      rw [Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 10 / 3)]
    have hnn : (0 : ℝ) ≤ Real.sqrt α * Work.FTS.Nonlin.Xn α g :=
      mul_nonneg (Real.sqrt_nonneg α) hX0
    have hkey : (3 : ℝ) * α * (10 * Real.sqrt (10 / α) * Work.FTS.Nonlin.Xn α g)
        = 30 * (Real.sqrt 10 * Real.sqrt α) * Work.FTS.Nonlin.Xn α g := by
      rw [show (3 : ℝ) * α * (10 * Real.sqrt (10 / α) * Work.FTS.Nonlin.Xn α g)
          = 30 * (α * Real.sqrt (10 / α)) * Work.FTS.Nonlin.Xn α g from by ring, hmul]
    rw [hkey]
    have hle : 30 * Real.sqrt 10 * (Real.sqrt α * Work.FTS.Nonlin.Xn α g)
        ≤ 100 * (Real.sqrt α * Work.FTS.Nonlin.Xn α g) := by
      calc 30 * Real.sqrt 10 * (Real.sqrt α * Work.FTS.Nonlin.Xn α g)
          ≤ 30 * (10 / 3) * (Real.sqrt α * Work.FTS.Nonlin.Xn α g) :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hs10 (by norm_num)) hnn
        _ = 100 * (Real.sqrt α * Work.FTS.Nonlin.Xn α g) := by ring
    calc 30 * (Real.sqrt 10 * Real.sqrt α) * Work.FTS.Nonlin.Xn α g
        = 30 * Real.sqrt 10 * (Real.sqrt α * Work.FTS.Nonlin.Xn α g) := by ring
      _ ≤ 100 * (Real.sqrt α * Work.FTS.Nonlin.Xn α g) := hle
      _ = 100 * Real.sqrt α * Work.FTS.Nonlin.Xn α g := by ring
  exact hbase.trans hstep

/-- Row 25b: `N₅^{sg} = -sin²θ FK(F_*) g`, rate `O(α·|g|_{ℋ⁴})`. -/
theorem row5sg_le {α : ℝ} {g : Fn} (hα : 0 < α) (hα1 : α ≤ 1)
    (hsq : Work.FTS.LocData.SmoothQuad g) (hmem : Work.Spaces.HkMem α 4 g) :
    Fa (Work.FTS.Nonlin.N5sg α g)
      ≤ ENNReal.ofReal (20 * α * Work.FTS.Nonlin.Xn α g) := by
  have hbase := Work.FTS.Nonlinear.Pieces.rl1Pieces.rl1_row_le_radial
    (N := Work.FTS.Nonlin.N5sg α g) (k := g) (c := 6 * α)
    (by positivity)
    (fun r hr θ hθ => N5sg_pt (α := α) (g := g) hα hα1 r hr θ hθ)
    (Work.FTS.Nonlinear.Pieces.rl1Tools.envG hα hsq hmem)
  have hFa : Fa (Work.FTS.Nonlin.N5sg α g)
      = (∫⁻ r in Set.Ioi (0 : ℝ), ENNReal.ofReal r⁻¹ * (∫⁻ θ in Work.Spaces.Iθ,
          ENNReal.ofReal |Work.Spaces.K θ * Work.FTS.Nonlin.N5sg α g r θ|)) := rfl
  rw [hFa]
  have hX0 : 0 ≤ Work.FTS.Nonlin.Xn α g := Work.Spaces.HkNorm_nonneg α 4 g
  have hstep : ENNReal.ofReal (6 * α) * ENNReal.ofReal (2 * Work.FTS.Nonlin.Xn α g)
      ≤ ENNReal.ofReal (20 * α * Work.FTS.Nonlin.Xn α g) := by
    rw [← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 6 * α)]
    refine ENNReal.ofReal_le_ofReal ?_
    have h0 : (0 : ℝ) ≤ α * Work.FTS.Nonlin.Xn α g := mul_nonneg hα.le hX0
    calc (6 : ℝ) * α * (2 * Work.FTS.Nonlin.Xn α g)
        = 12 * (α * Work.FTS.Nonlin.Xn α g) := by ring
      _ ≤ 20 * (α * Work.FTS.Nonlin.Xn α g) := by linarith
      _ = 20 * α * Work.FTS.Nonlin.Xn α g := by ring
  exact hbase.trans hstep

/-! ## The absorption of the rates into `Env` -/

/-- `√α·|g|_{ℋ⁴} ≤ Env α g`. -/
theorem sqrt_alpha_mul_Xn_le_Env {α : ℝ} (g : Fn) (hα : 0 ≤ α) :
    Real.sqrt α * Work.FTS.Nonlin.Xn α g ≤ Env α g := by
  rw [Env]
  have h1 : (0 : ℝ) ≤ α ^ 2 := sq_nonneg α
  have h2 : (0 : ℝ) ≤ α ^ (-(3 / 2 : ℝ)) * (Work.FTS.Nonlin.Xn α g) ^ 2 :=
    mul_nonneg (Real.rpow_nonneg hα _) (sq_nonneg _)
  linarith

/-- `α·|g|_{ℋ⁴} ≤ Env α g` for `0 < α ≤ 1`. -/
theorem alpha_mul_Xn_le_Env {α : ℝ} (g : Fn) (hα : 0 < α) (hα1 : α ≤ 1) :
    α * Work.FTS.Nonlin.Xn α g ≤ Env α g := by
  have hX0 : 0 ≤ Work.FTS.Nonlin.Xn α g := Work.Spaces.HkNorm_nonneg α 4 g
  have h1 : α ≤ Real.sqrt α := (Real.le_sqrt hα.le hα.le).mpr (by nlinarith)
  exact (mul_le_mul_of_nonneg_right h1 hX0).trans (sqrt_alpha_mul_Xn_le_Env g hα.le)

/-
The four rows whose coefficient is an angular moment: `N4gs = -(1/2)sin2θ·FK(g)·∂_θF_*`,
`N5gs = -sin²θ·FK(g)·F_*`, `N4sg = -(1/2)FK(F_*)·D_θg`, `N5sg = -sin²θ·FK(F_*)·g`.  Only
`α` and `g` occur (`F_* = Fstar α`), so `GalClass α g` is the whole hypothesis.

Bounds to use: `|FK g z| ≤ 4√(∫_θ (g z θ)²)` (`Work.FTS.Nonlinear.Pieces.Rl1.n5_FK_abs_le`),
`FK (Fstar α) z = α·2z/(1+z)²` exactly (`Work.FTS.Nonlin.FK_Fstar`, re-exported as
`Work.FTS.NonlinRows.Rl1.FK_Fstar_pt`), the profile bounds `Fstar_pt`, `DthFstar_pt`,
`K_pthFstar_pt` in `Rl1/tools.lean`, the slot energies via `slot0`/`slot1`
(`Phi0 g`, `Phi1 g`), and `Work.FTS.Nonlinear.Pieces.rl1Pieces.rowStep` for the rows whose
θ-bound is θ-free.  Rates: `O(α·Xn α g)` for all four, and `α·Xn ≤ √α·Xn ≤ Env α g`.
-/
theorem gssgFKBounds : ∃ K : ℝ, 0 < K ∧ ∀ {α : ℝ} {g : Work.FTS.Galerkin.Fn},
    0 < α → α ≤ 1 → Work.FTS.Nonlin.GalClass α g →
    Work.FTS.Nonlinear.Pieces.Fa (Work.FTS.Nonlin.N4gs α g)
        ≤ ENNReal.ofReal (K * Work.FTS.NonlinRows.Rl1.Env α g) ∧
      Work.FTS.Nonlinear.Pieces.Fa (Work.FTS.Nonlin.N5gs α g)
        ≤ ENNReal.ofReal (K * Work.FTS.NonlinRows.Rl1.Env α g) ∧
      Work.FTS.Nonlinear.Pieces.Fa (Work.FTS.Nonlin.N4sg α g)
        ≤ ENNReal.ofReal (K * Work.FTS.NonlinRows.Rl1.Env α g) ∧
      Work.FTS.Nonlinear.Pieces.Fa (Work.FTS.Nonlin.N5sg α g)
        ≤ ENNReal.ofReal (K * Work.FTS.NonlinRows.Rl1.Env α g) := by
  refine ⟨10000, by norm_num, ?_⟩
  intro α g hα hα1 hgal
  have hsq : Work.FTS.LocData.SmoothQuad g := hgal.reg.1
  have hmem : Work.Spaces.HkMem α 4 g := (Work.FTS.Nonlin.galClass_regQ4 hgal).2.1
  have hsl0 : AEStronglyMeasurable (fun θ => g 0 θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
    Work.FTS.Nonlinear.Pieces.rl1Pieces.aesm_slice_zero_of_axis
      (fun θ hθ => (hgal.axis θ hθ).1)
  have hX0 : 0 ≤ Work.FTS.Nonlin.Xn α g := Work.Spaces.HkNorm_nonneg α 4 g
  have hEnv : 0 ≤ Env α g := Env_nonneg g hα.le
  have hαXn : α * Work.FTS.Nonlin.Xn α g ≤ Env α g := alpha_mul_Xn_le_Env g hα hα1
  have hSqrtXn : Real.sqrt α * Work.FTS.Nonlin.Xn α g ≤ Env α g :=
    sqrt_alpha_mul_Xn_le_Env g hα.le
  have h4gs := row4gs_le (α := α) (g := g) hα hα1 hsq hmem hsl0
  have h5gs := row5gs_le (α := α) (g := g) hα hα1 hsq hmem hsl0
  have h4sg := row4sg_le (α := α) (g := g) hα hα1 hsq hmem
  have h5sg := row5sg_le (α := α) (g := g) hα hα1 hsq hmem
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine h4gs.trans (ENNReal.ofReal_le_ofReal ?_)
    nlinarith [hαXn, hEnv, hX0]
  · refine h5gs.trans (ENNReal.ofReal_le_ofReal ?_)
    nlinarith [hαXn, hEnv, hX0]
  · refine h4sg.trans (ENNReal.ofReal_le_ofReal ?_)
    nlinarith [hSqrtXn, hEnv]
  · refine h5sg.trans (ENNReal.ofReal_le_ofReal ?_)
    nlinarith [hαXn, hEnv, hX0]

end

end Work.FTS.NonlinRows.Rl1
