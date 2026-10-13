import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.Coercivity.Basic
import Submission.Work.Coercivity.Defs
import Submission.Work.FM.Core2
import Submission.Work.Spaces.cs_integral
import Submission.Work.Elliptic.tail_l2_cauchy_schwarz
import Submission.Work.Coercivity.L12f_continuousOn

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.Coercivity

set_option autoImplicit false

/-! ## Auxiliary lemmas

The estimate `|∫∫ 2 (Γ/c - K) f w (L₁₂f/z)| ≤ (7/5)√(Ef f)√(EL12z f)` is a single
Cauchy–Schwarz in the product space `Iz ×ˢ Iθ`, applied to the two functions
`(z,θ) ↦ g(θ)·ψ(z)` and `(z,θ) ↦ f(z,θ)w(z)`; the first one has a product structure,
so its `L²`-norm factorises as `‖g‖_{L²(dθ)}·‖ψ‖_{L²(dz)}` with **no** angular
factor.  Everything is organised through `∫⁻` (`ENNReal`) so that no junk values of
Bochner integrals enter.
-/

/-- `z ↦ L₁₂(f)(z)/z` is a.e. strongly measurable on `[0,∞)`: `L₁₂(f)` is continuous on
`(0,∞)` (`L12f_continuousOn`) and `Ioi 0`, `Ici 0` differ by the null set `{0}`. -/
private theorem aemeasurable_L12f_div (f : ℝ → ℝ → ℝ) (hfH : HardyHyp f) :
    AEMeasurable (fun z : ℝ => L12f f z / z) (volume.restrict Spaces.Iz) := by
  have hcont : ContinuousOn (fun z : ℝ => L12f f z / z) (Set.Ioi (0 : ℝ)) :=
    (L12f_continuousOn f hfH).div continuousOn_id (fun z hz => ne_of_gt hz)
  have h1 : AEStronglyMeasurable (fun z : ℝ => L12f f z / z)
      (volume.restrict (Set.Ioi (0 : ℝ))) :=
    hcont.aestronglyMeasurable measurableSet_Ioi
  have h2 : volume.restrict Spaces.Iz = volume.restrict (Set.Ioi (0 : ℝ)) := by
    rw [Spaces.Iz]
    exact (Measure.restrict_congr_set (Ioi_ae_eq_Ici (a := (0 : ℝ)))).symm
  rw [h2]
  exact h1.aemeasurable

/-- `(z,θ) ↦ ENNReal.ofReal ‖f(z,θ)w(z)‖` is a.e. measurable on the quadrant, from the
integrability of `(f w)²`: the latter makes `|f w| = √((f w)²)` a.e. measurable. -/
private theorem aemeasurable_ofReal_abs_mul_w (f : ℝ → ℝ → ℝ)
    (hf2 : MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => f z θ * f z θ * Spaces.w z ^ 2))
      (Spaces.Iz ×ˢ Spaces.Iθ)) :
    AEMeasurable (fun p : ℝ × ℝ => ENNReal.ofReal |f p.1 p.2 * Spaces.w p.1|)
      ((volume.restrict Spaces.Iz).prod (volume.restrict Spaces.Iθ)) := by
  set P : Measure (ℝ × ℝ) := (volume.restrict Spaces.Iz).prod (volume.restrict Spaces.Iθ) with hP
  have hInt : Integrable (fun p : ℝ × ℝ => f p.1 p.2 * f p.1 p.2 * Spaces.w p.1 ^ 2) P := by
    rw [hP, Measure.prod_restrict]
    exact hf2
  have hInt2 : Integrable (fun p : ℝ × ℝ => (f p.1 p.2 * Spaces.w p.1) ^ 2) P :=
    hInt.congr (Eventually.of_forall fun p => by ring)
  have h2 : AEMeasurable (fun p : ℝ × ℝ => Real.sqrt ((f p.1 p.2 * Spaces.w p.1) ^ 2)) P :=
    hInt2.aestronglyMeasurable.aemeasurable.sqrt
  have h3 : AEMeasurable (fun p : ℝ × ℝ => |f p.1 p.2 * Spaces.w p.1|) P := by
    refine h2.congr ?_
    filter_upwards with p
    exact Real.sqrt_sq_eq_abs _
  exact ENNReal.measurable_ofReal.comp_aemeasurable h3

/-- **Tensor Cauchy–Schwarz.**  For `σ`-finite measures `μ` on `α` and `ν` on `β` and
measurable functions `Ge : β → ℝ≥0∞`, `Φf : α × β → ℝ≥0∞`, `Ψf : α → ℝ≥0∞` (with `Ψf`
and `∫⁻Ge²` finite),

`∫∫ Ge(θ) Φf(z,θ) Ψf(z) ≤ (∫Ge²)^{1/2} · (∫∫Φf²)^{1/2} · (∫Ψf²)^{1/2}`.

Note there is **no** angular factor: because `Ge(θ)Ψf(z)` is a product of a function of
`θ` alone and a function of `z` alone, Hölder in the product measure factorises. -/
private theorem tensor_holder_ennreal {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : MeasureTheory.Measure α} {ν : MeasureTheory.Measure β}
    [MeasureTheory.SFinite μ] [MeasureTheory.SFinite ν]
    (Ge : β → ENNReal) (Φf : α × β → ENNReal) (Ψf : α → ENNReal)
    (hΨfin : ∀ z, Ψf z ≠ ⊤) (hGeA : (∫⁻ θ, Ge θ ^ 2 ∂ν) ≠ ⊤)
    (hGe : AEMeasurable Ge ν) (hΦ : AEMeasurable Φf (μ.prod ν)) (hΨ : AEMeasurable Ψf μ) :
    ∫⁻ p, Ge p.2 * Φf p * Ψf p.1 ∂(μ.prod ν)
      ≤ (∫⁻ θ, Ge θ ^ 2 ∂ν) ^ ((1 : ℝ) / 2) * (∫⁻ p, Φf p ^ 2 ∂(μ.prod ν)) ^ ((1 : ℝ) / 2)
        * (∫⁻ z, Ψf z ^ 2 ∂μ) ^ ((1 : ℝ) / 2) := by
  have hpq : (2 : ℝ).HolderConjugate 2 :=
    Real.holderConjugate_iff.mpr ⟨by norm_num, by norm_num⟩
  have hm : AEMeasurable (fun p : α × β => Ge p.2 * Ψf p.1) (μ.prod ν) :=
    (AEMeasurable.comp_snd hGe).mul (AEMeasurable.comp_fst hΨ)
  -- Hölder in the product measure
  have hholder := ENNReal.lintegral_mul_le_Lp_mul_Lq (μ.prod ν) hpq hm hΦ
  set A : ENNReal := ∫⁻ θ, Ge θ ^ 2 ∂ν with hA
  set B : ENNReal := ∫⁻ z, Ψf z ^ 2 ∂μ with hB
  set C : ENNReal := ∫⁻ p, Φf p ^ 2 ∂(μ.prod ν) with hC
  -- the squares
  have hsq : ∀ p : α × β, (Ge p.2 * Ψf p.1) ^ (2 : ℝ) = Ge p.2 ^ 2 * Ψf p.1 ^ 2 := by
    intro p
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, ENNReal.rpow_natCast, mul_pow]
  have hCeq : (∫⁻ p, Φf p ^ (2 : ℝ) ∂(μ.prod ν)) = C := by
    rw [hC]
    exact lintegral_congr fun p => by
      rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, ENNReal.rpow_natCast]
  -- `∫ (Ge∘snd · Ψ∘fst)² = A * B`
  have hAB : (∫⁻ p, (Ge p.2 * Ψf p.1) ^ (2 : ℝ) ∂(μ.prod ν)) = A * B := by
    rw [lintegral_congr hsq]
    have hm2 : AEMeasurable (fun p : α × β => Ge p.2 ^ 2 * Ψf p.1 ^ 2) (μ.prod ν) :=
      ((AEMeasurable.comp_snd hGe).pow_const 2).mul ((AEMeasurable.comp_fst hΨ).pow_const 2)
    rw [MeasureTheory.lintegral_prod _ hm2]
    have hinner : ∀ z : α, ∫⁻ θ, Ge θ ^ 2 * Ψf z ^ 2 ∂ν = A * Ψf z ^ 2 := by
      intro z
      rw [MeasureTheory.lintegral_mul_const' (Ψf z ^ 2) (fun θ => Ge θ ^ 2) ?_, hA]
      rw [pow_two]
      exact ENNReal.mul_ne_top (hΨfin z) (hΨfin z)
    rw [lintegral_congr hinner, hB]
    exact MeasureTheory.lintegral_const_mul' A (fun z => Ψf z ^ 2) hGeA
  rw [hAB] at hholder
  have hholder' : (∫⁻ p, (Ge p.2 * Ψf p.1) * Φf p ∂(μ.prod ν))
      ≤ (A * B) ^ ((1 : ℝ) / 2) * C ^ ((1 : ℝ) / 2) := by
    rw [← hCeq]
    exact hholder
  calc ∫⁻ p, Ge p.2 * Φf p * Ψf p.1 ∂(μ.prod ν)
      = ∫⁻ p, (Ge p.2 * Ψf p.1) * Φf p ∂(μ.prod ν) := by
        refine lintegral_congr fun p => ?_
        ac_rfl
    _ ≤ (A * B) ^ ((1 : ℝ) / 2) * C ^ ((1 : ℝ) / 2) := hholder'
    _ = (A ^ ((1 : ℝ) / 2) * B ^ ((1 : ℝ) / 2)) * C ^ ((1 : ℝ) / 2) := by
        rw [ENNReal.mul_rpow_of_nonneg A B (by norm_num)]
    _ = A ^ ((1 : ℝ) / 2) * C ^ ((1 : ℝ) / 2) * B ^ ((1 : ℝ) / 2) := by
        ac_rfl

/-- The `∫⁻`-version of `EL12z f`: `∫⁻ (ofReal ‖L₁₂(f)(z)/z‖)² = ofReal (EL12z f)`,
using the integrability of `(L₁₂ f)²/z²` supplied by `HardyHyp.intA` at `j = 1`. -/
private theorem lintegral_ofReal_L12z_sq (f : ℝ → ℝ → ℝ) (hfH : HardyHyp f) :
    (∫⁻ z, (ENNReal.ofReal |L12f f z / z|) ^ 2
        ∂(volume.restrict Spaces.Iz)) = ENNReal.ofReal (EL12z f) := by
  -- integrability of `(L₁₂(f)(z)/z)²` on `(0,∞)`, from `HardyHyp.intA 1`
  have hIoi : IntegrableOn (fun z : ℝ => (L12f f z / z) ^ 2) (Set.Ioi (0 : ℝ)) := by
    refine IntegrableOn.congr_fun (hfH.intA 1 (by norm_num)) (fun z hz => ?_) measurableSet_Ioi
    rw [div_pow]
    congr 1
    norm_num
  have hIz : Integrable (fun z : ℝ => (L12f f z / z) ^ 2) (volume.restrict Spaces.Iz) := by
    rw [Spaces.Iz, ← Measure.restrict_congr_set (Ioi_ae_eq_Ici (a := (0 : ℝ)))]
    exact hIoi
  have hpt : ∀ z : ℝ, (ENNReal.ofReal |L12f f z / z|) ^ 2
      = ENNReal.ofReal ((L12f f z / z) ^ 2) := by
    intro z
    rw [← ENNReal.ofReal_pow (abs_nonneg _), sq_abs]
  rw [lintegral_congr hpt]
  rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hIz
        (Eventually.of_forall fun z => sq_nonneg _)]
  congr 1

/-- The `∫⁻`-version of `Ef f`: `∫⁻ (ofReal ‖f w‖)² = ofReal (Ef f)`, using the joint
integrability of `(f w)²` together with Tonelli/Fubini. -/
private theorem lintegral_ofReal_fw_sq (f : ℝ → ℝ → ℝ)
    (hf2 : MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => f z θ * f z θ * Spaces.w z ^ 2))
      (Spaces.Iz ×ˢ Spaces.Iθ)) :
    (∫⁻ p : ℝ × ℝ, (ENNReal.ofReal |f p.1 p.2 * Spaces.w p.1|) ^ 2
        ∂((volume.restrict Spaces.Iz).prod (volume.restrict Spaces.Iθ)))
      = ENNReal.ofReal (Ef f) := by
  set P : Measure (ℝ × ℝ) := (volume.restrict Spaces.Iz).prod (volume.restrict Spaces.Iθ) with hP
  have hInt : Integrable (fun p : ℝ × ℝ => (f p.1 p.2 * Spaces.w p.1) ^ 2) P := by
    have h0 : Integrable (fun p : ℝ × ℝ => f p.1 p.2 * f p.1 p.2 * Spaces.w p.1 ^ 2) P := by
      rw [hP, Measure.prod_restrict]
      exact hf2
    exact h0.congr (Eventually.of_forall fun p => by ring)
  have hpt : ∀ p : ℝ × ℝ, (ENNReal.ofReal |f p.1 p.2 * Spaces.w p.1|) ^ 2
      = ENNReal.ofReal ((f p.1 p.2 * Spaces.w p.1) ^ 2) := by
    intro p
    rw [← ENNReal.ofReal_pow (abs_nonneg _), sq_abs]
  rw [lintegral_congr hpt]
  rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hInt
        (Eventually.of_forall fun p => sq_nonneg _)]
  congr 1
  rw [hP, MeasureTheory.integral_prod _ hInt]
  simp only [Ef, Spaces.L2Sq]

/-- The angular part: `∫⁻ (ofReal ‖g θ‖)² = ofReal (∫ g²)`, from the integrability of
`g²` on the angular interval. -/
private theorem lintegral_ofReal_sq_Iθ (g : ℝ → ℝ)
    (hB : MeasureTheory.IntegrableOn (fun θ : ℝ => g θ ^ 2) Spaces.Iθ) :
    (∫⁻ θ, (ENNReal.ofReal |g θ|) ^ 2 ∂(volume.restrict Spaces.Iθ))
      = ENNReal.ofReal (∫ θ in Spaces.Iθ, g θ ^ 2) := by
  have hpt : ∀ θ : ℝ, (ENNReal.ofReal |g θ|) ^ 2 = ENNReal.ofReal (g θ ^ 2) := by
    intro θ
    rw [← ENNReal.ofReal_pow (abs_nonneg _), sq_abs]
  rw [lintegral_congr hpt]
  exact (MeasureTheory.ofReal_integral_eq_lintegral_ofReal hB
    (Eventually.of_forall fun θ => sq_nonneg _)).symm

/-! ## The main estimate -/

theorem wip_G_bound (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (f : ℝ → ℝ → ℝ)
    (hfH : HardyHyp f)
    (hf2 : MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => f z θ * f z θ * Spaces.w z ^ 2))
      (Spaces.Iz ×ˢ Spaces.Iθ))
    (hΓ : GammaL2Bnd α)
    (hB : MeasureTheory.IntegrableOn
      (fun θ : ℝ => (Spaces.Gam α θ / Spaces.c α - Spaces.K θ) ^ 2) Spaces.Iθ)
    (hint : MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ =>
        2 * (Spaces.Gam α θ / Spaces.c α - Spaces.K θ) * f z θ * Spaces.w z * (L12f f z / z)))
      (Spaces.Iz ×ˢ Spaces.Iθ)) :
    |∫ p : ℝ × ℝ, 2 * (Spaces.Gam α p.2 / Spaces.c α - Spaces.K p.2) * f p.1 p.2 * Spaces.w p.1
        * (L12f f p.1 / p.1)
        ∂((MeasureTheory.volume.restrict Spaces.Iz).prod (MeasureTheory.volume.restrict Spaces.Iθ))|
      ≤ (7 / 5) * Real.sqrt (Ef f) * Real.sqrt (EL12z f) := by
  set P : Measure (ℝ × ℝ) := (volume.restrict Spaces.Iz).prod (volume.restrict Spaces.Iθ) with hP
  set g : ℝ → ℝ := fun θ => Spaces.Gam α θ / Spaces.c α - Spaces.K θ with hg
  set ψ : ℝ → ℝ := fun z => L12f f z / z with hψ
  set G : ℝ × ℝ → ℝ := fun p => (2 * g p.2) * (f p.1 p.2 * Spaces.w p.1) * ψ p.1 with hG
  -- the integrand of the statement, regrouped
  have hGeq : (fun p : ℝ × ℝ => 2 * (Spaces.Gam α p.2 / Spaces.c α - Spaces.K p.2) * f p.1 p.2
      * Spaces.w p.1 * (L12f f p.1 / p.1)) = G := by
    funext p
    simp only [hG, hg, hψ]
    ring
  -- integrability of `g²` and a.e. measurability of `|g|`
  have hB_g : MeasureTheory.IntegrableOn (fun θ : ℝ => g θ ^ 2) Spaces.Iθ := by
    rw [hg]; exact hB
  have hgmeas : AEMeasurable (fun θ : ℝ => |g θ|) (volume.restrict Spaces.Iθ) := by
    have h2 : AEMeasurable (fun θ : ℝ => Real.sqrt (g θ ^ 2)) (volume.restrict Spaces.Iθ) :=
      (hB_g.aestronglyMeasurable.aemeasurable).sqrt
    refine h2.congr ?_
    filter_upwards with θ
    exact Real.sqrt_sq_eq_abs _
  -- joint integrability of `G`
  have hGint : Integrable G P := by
    have h : Integrable (Function.uncurry (fun z θ =>
        2 * (Spaces.Gam α θ / Spaces.c α - Spaces.K θ) * f z θ * Spaces.w z * (L12f f z / z)))
        ((volume.restrict Spaces.Iz).prod (volume.restrict Spaces.Iθ)) := by
      rw [Measure.prod_restrict]
      exact hint
    rw [hP]
    refine h.congr (Eventually.of_forall fun p => ?_)
    simp only [Function.uncurry, hG, hg, hψ]
    ring
  -- the `ENNReal` integrands
  set Ge : ℝ → ENNReal := fun θ => ENNReal.ofReal |g θ| with hGeD
  set Phi : ℝ × ℝ → ENNReal := fun p => ENNReal.ofReal |f p.1 p.2 * Spaces.w p.1| with hPhiD
  set Psi : ℝ → ENNReal := fun z => ENNReal.ofReal |ψ z| with hPsiD
  have hPsi_aem : AEMeasurable Psi (volume.restrict Spaces.Iz) := by
    have h1 : AEMeasurable (fun z : ℝ => |ψ z|) (volume.restrict Spaces.Iz) := by
      rw [hψ]
      simpa only [Real.norm_eq_abs] using (aemeasurable_L12f_div f hfH).norm
    rw [hPsiD]
    exact ENNReal.measurable_ofReal.comp_aemeasurable h1
  have hPhi_aem : AEMeasurable Phi P := by
    rw [hPhiD, hP]
    exact aemeasurable_ofReal_abs_mul_w f hf2
  have hGe_aem : AEMeasurable Ge (volume.restrict Spaces.Iθ) := by
    rw [hGeD]
    exact ENNReal.measurable_ofReal.comp_aemeasurable hgmeas
  -- values of the three `∫⁻`
  have hAval : (∫⁻ θ, Ge θ ^ 2 ∂(volume.restrict Spaces.Iθ))
      = ENNReal.ofReal (∫ θ in Spaces.Iθ, g θ ^ 2) := by
    rw [hGeD]
    exact lintegral_ofReal_sq_Iθ g hB_g
  have hBval : (∫⁻ z, Psi z ^ 2 ∂(volume.restrict Spaces.Iz)) = ENNReal.ofReal (EL12z f) := by
    rw [hPsiD]
    exact lintegral_ofReal_L12z_sq f hfH
  have hCval : (∫⁻ p : ℝ × ℝ, Phi p ^ 2 ∂P) = ENNReal.ofReal (Ef f) := by
    rw [hP, hPhiD]
    exact lintegral_ofReal_fw_sq f hf2
  have hGeA : (∫⁻ θ, Ge θ ^ 2 ∂(volume.restrict Spaces.Iθ)) ≠ ⊤ := by
    rw [hAval]; exact ENNReal.ofReal_ne_top
  have hPsinf : ∀ z : ℝ, Psi z ≠ ⊤ := fun z => by rw [hPsiD]; exact ENNReal.ofReal_ne_top
  -- tensor Cauchy–Schwarz
  have hHolder := tensor_holder_ennreal (μ := volume.restrict Spaces.Iz)
    (ν := volume.restrict Spaces.Iθ) Ge Phi Psi hPsinf hGeA hGe_aem hPhi_aem hPsi_aem
  -- the pointwise identity of the `ℝ≥0∞` integrand
  have hptG : ∀ p : ℝ × ℝ, ENNReal.ofReal |G p| = 2 * Ge p.2 * Phi p * Psi p.1 := by
    intro p
    rw [hG, hGeD, hPhiD, hPsiD]
    rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    rw [ENNReal.ofReal_mul
          (by positivity : (0 : ℝ) ≤ (2 * |g p.2|) * |f p.1 p.2 * Spaces.w p.1|),
        ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 2 * |g p.2|),
        ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  have hENN : ∫⁻ p, ENNReal.ofReal |G p| ∂P
      ≤ 2 * ((∫⁻ θ, Ge θ ^ 2 ∂(volume.restrict Spaces.Iθ)) ^ ((1 : ℝ) / 2)
          * (∫⁻ p, Phi p ^ 2 ∂P) ^ ((1 : ℝ) / 2)
          * (∫⁻ z, Psi z ^ 2 ∂(volume.restrict Spaces.Iz)) ^ ((1 : ℝ) / 2)) := by
    have h1 : (∫⁻ p, ENNReal.ofReal |G p| ∂P)
        = 2 * ∫⁻ p, Ge p.2 * Phi p * Psi p.1 ∂P := by
      rw [lintegral_congr hptG]
      rw [show (fun p : ℝ × ℝ => 2 * Ge p.2 * Phi p * Psi p.1)
          = fun p => 2 * (Ge p.2 * Phi p * Psi p.1) from by funext p; ac_rfl]
      rw [MeasureTheory.lintegral_const_mul' 2 _ (by norm_num)]
    rw [h1]
    exact mul_le_mul_of_nonneg_left hHolder (by norm_num)
  -- the same bound, with the three integrals evaluated
  have hENN' : ∫⁻ p, ENNReal.ofReal |G p| ∂P
      ≤ 2 * (ENNReal.ofReal (Real.sqrt (∫ θ in Spaces.Iθ, g θ ^ 2))
              * ENNReal.ofReal (Real.sqrt (Ef f))
              * ENNReal.ofReal (Real.sqrt (EL12z f))) := by
    refine hENN.trans (le_of_eq ?_)
    have ha0 : 0 ≤ ∫ θ in Spaces.Iθ, g θ ^ 2 := integral_nonneg fun θ => sq_nonneg _
    have hc0 : 0 ≤ Ef f := by
      rw [Ef, Spaces.L2Sq]
      exact integral_nonneg fun z => integral_nonneg fun θ => sq_nonneg _
    have hb0 : 0 ≤ EL12z f := by
      rw [EL12z, L2Sqz]
      exact integral_nonneg fun z => sq_nonneg _
    rw [hAval, hCval, hBval]
    rw [ENNReal.ofReal_rpow_of_nonneg ha0 (by norm_num : (0 : ℝ) ≤ 1 / 2),
        ENNReal.ofReal_rpow_of_nonneg hc0 (by norm_num : (0 : ℝ) ≤ 1 / 2),
        ENNReal.ofReal_rpow_of_nonneg hb0 (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    rw [← Real.sqrt_eq_rpow (∫ θ in Spaces.Iθ, g θ ^ 2),
        ← Real.sqrt_eq_rpow (Ef f), ← Real.sqrt_eq_rpow (EL12z f)]
  -- the non-finiteness needed for `toReal_mono`
  have hne_top : 2 * (ENNReal.ofReal (Real.sqrt (∫ θ in Spaces.Iθ, g θ ^ 2))
              * ENNReal.ofReal (Real.sqrt (Ef f))
              * ENNReal.ofReal (Real.sqrt (EL12z f))) ≠ ⊤ :=
    ENNReal.mul_ne_top (by norm_num)
      (ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)
        ENNReal.ofReal_ne_top)
  -- the value of the LHS integral
  have hAbs : |∫ p, G p ∂P| ≤ (∫⁻ p, ENNReal.ofReal |G p| ∂P).toReal := by
    have h1 : |∫ p, G p ∂P| ≤ ∫ p, |G p| ∂P := abs_integral_le_integral_abs
    have h2 : (∫⁻ p, ENNReal.ofReal |G p| ∂P).toReal = ∫ p, |G p| ∂P := by
      rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hGint.abs
            (Eventually.of_forall fun p => abs_nonneg _)]
      exact ENNReal.toReal_ofReal (integral_nonneg fun p => abs_nonneg _)
    linarith
  -- the integral of the statement is that of `G`
  have hIntEq : (∫ p : ℝ × ℝ, 2 * (Spaces.Gam α p.2 / Spaces.c α - Spaces.K p.2) * f p.1 p.2
        * Spaces.w p.1 * (L12f f p.1 / p.1) ∂P) = ∫ p, G p ∂P :=
    integral_congr_ae (Eventually.of_forall (congrFun hGeq))
  -- the numerical conclusion
  have hsqrt : Real.sqrt (∫ θ in Spaces.Iθ, g θ ^ 2) ≤ 7 / 10 := by
    have hΓ' : ∫ θ in Spaces.Iθ, g θ ^ 2 ≤ ((7 : ℝ) / 10) ^ 2 := by
      rw [hg]; exact hΓ
    calc Real.sqrt (∫ θ in Spaces.Iθ, g θ ^ 2) ≤ Real.sqrt (((7 : ℝ) / 10) ^ 2) :=
          Real.sqrt_le_sqrt hΓ'
      _ = 7 / 10 := Real.sqrt_sq (by norm_num)
  have hEfnn : 0 ≤ Real.sqrt (Ef f) := Real.sqrt_nonneg _
  have hELnn : 0 ≤ Real.sqrt (EL12z f) := Real.sqrt_nonneg _
  calc |∫ p : ℝ × ℝ, 2 * (Spaces.Gam α p.2 / Spaces.c α - Spaces.K p.2) * f p.1 p.2
        * Spaces.w p.1 * (L12f f p.1 / p.1) ∂P|
      = |∫ p, G p ∂P| := by rw [hIntEq]
    _ ≤ (∫⁻ p, ENNReal.ofReal |G p| ∂P).toReal := hAbs
    _ ≤ (2 * (ENNReal.ofReal (Real.sqrt (∫ θ in Spaces.Iθ, g θ ^ 2))
              * ENNReal.ofReal (Real.sqrt (Ef f))
              * ENNReal.ofReal (Real.sqrt (EL12z f)))).toReal :=
          ENNReal.toReal_mono hne_top hENN'
    _ = 2 * Real.sqrt (∫ θ in Spaces.Iθ, g θ ^ 2) * Real.sqrt (Ef f)
          * Real.sqrt (EL12z f) := by
        rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_mul,
            ENNReal.toReal_ofReal (Real.sqrt_nonneg _),
            ENNReal.toReal_ofReal (Real.sqrt_nonneg _),
            ENNReal.toReal_ofReal (Real.sqrt_nonneg _),
            show ENNReal.toReal (2 : ENNReal) = 2 by norm_num]
        ring
    _ ≤ (7 / 5) * Real.sqrt (Ef f) * Real.sqrt (EL12z f) := by
        have h1 : 2 * Real.sqrt (∫ θ in Spaces.Iθ, g θ ^ 2) ≤ 2 * (7 / 10) := by linarith
        have h2 : 2 * Real.sqrt (∫ θ in Spaces.Iθ, g θ ^ 2) * Real.sqrt (Ef f)
            ≤ 2 * (7 / 10) * Real.sqrt (Ef f) :=
          mul_le_mul_of_nonneg_right h1 hEfnn
        have h3 : 2 * Real.sqrt (∫ θ in Spaces.Iθ, g θ ^ 2) * Real.sqrt (Ef f)
              * Real.sqrt (EL12z f)
            ≤ 2 * (7 / 10) * Real.sqrt (Ef f) * Real.sqrt (EL12z f) :=
          mul_le_mul_of_nonneg_right h2 hELnn
        linarith

end Work.Coercivity
