/-
# `|L₁₂(Transport g)(0)| ≤ C · |g|_{ℋ⁴_α}`, with `C` independent of `α`

`Transport g = 3 sin(2θ) ∂_θ g/(1+z) = 3 D_θg/(1+z)`, and

  `L₁₂(Transport g)(0) = ∫_{s>0} ∫_θ K(θ)·3 D_θg(s,θ)/(s(1+s)) dθ ds`.

The proof is a two-step Cauchy–Schwarz, in the *same* normalisation as
`Work.FTS.GalBasis.cc.abs_L12_le_HkNorm`: the `θ`-integrand factorises as

  `K θ·Transport g s θ/s = Wlam3 s · (KG α θ · (D_θg s θ · Wt α s θ))`,

where `Wt α s θ = w(s)·sin(2θ)^{-γ/2}` is the `ℋ⁴`-weight and `D_θg·Wt α` is exactly the
`(i,j) = (1,0)`-slot of `HkIntegrand α 4 g` (so its square is dominated by the integrand).
The angular profile is `KG α θ = 3 K(θ) sin(2θ)^{γ/2}`, whose `L²`-norm is `≤ 13` uniformly
for `α > 0` (because `K ≤ 3` and `sin(2θ)^{γ/2} ≤ 1` on `Iθ`); the radial weight is
`Wlam3 s = s/(1+s)³ = 1/(s(1+s)w(s))`, dominated by the square-integrable `Wlam s = s/(1+s)²`.

  * angular Cauchy–Schwarz: `|∫_θ KG·(D_θg·Wt)| ≤ 13·√(∫_θ HkIntegrand α 4 g s θ)`;
  * radial Cauchy–Schwarz: `∫_{s>0} Wlam3·√(∫_θ HkIntegrand) ≤ √W2·√(HkSq α 4 g)`.

No smoothness of `g` is used: only the (slice-)integrability of the `ℋ⁴`-integrand provided
by `HkMem α 4 g`; a non-integrable integral is `0` (`MeasureTheory.integral_undef`), which
satisfies the bound for free.
-/
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.Coercivity.Defs
import Submission.Work.FM.Defs
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.GalBasis.cc.abs_L12_le_HkNorm
import Submission.Work.FTS.GalBasis.cc.Defs
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.FTS.EllipticEst.remov.Ebs.abs_integral_mul_le_sqrt

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.L3Aux

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## The angular profile and the radial weight of the transport density -/

/-- `SwG α θ = sin(2θ)^{γ/2}`, the angular half of the `ℋ⁴`-weight on the `D_θ`-slot. -/
def SwG (α : ℝ) (θ : ℝ) : ℝ := Real.sin (2 * θ) ^ (Work.Spaces.gam α / 2)

/-- `KG α θ = 3 K(θ) sin(2θ)^{γ/2}`, the angular profile of the transport density. -/
def KG (α : ℝ) (θ : ℝ) : ℝ := 3 * Work.Spaces.K θ * SwG α θ

/-- `Wlam3 s = s/(1+s)³ = 1/(s(1+s)w(s))`, the radial weight of the transport density. -/
def Wlam3 (s : ℝ) : ℝ := s / (1 + s) ^ 3

lemma tl12_gam_half_nonneg {α : ℝ} (hα : 0 < α) : 0 ≤ Work.Spaces.gam α / 2 := by
  rw [Work.Spaces.gam]; linarith

lemma tl12_sin_two_nonneg {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ Real.sin (2 * θ) :=
  Work.FTS.GalBasis.cc.sin_two_nonneg_of_mem_Iθ hθ

lemma tl12_continuous_SwG (α : ℝ) (h : 0 ≤ Work.Spaces.gam α / 2) : Continuous (SwG α) :=
  (Real.continuous_rpow_const h).comp (Real.continuous_sin.comp (continuous_const.mul continuous_id))

lemma tl12_continuous_K : Continuous fun θ : ℝ => Work.Spaces.K θ := by
  change Continuous fun θ : ℝ => 3 * Real.sin θ * Real.cos θ ^ 2
  fun_prop

lemma tl12_continuous_KG (α : ℝ) (hγ : 0 ≤ Work.Spaces.gam α / 2) : Continuous (KG α) :=
  (continuous_const.mul tl12_continuous_K).mul (tl12_continuous_SwG α hγ)

lemma tl12_SwG_nonneg (α : ℝ) {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ SwG α θ :=
  Real.rpow_nonneg (tl12_sin_two_nonneg hθ) _

lemma tl12_KG_nonneg (α : ℝ) {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ KG α θ :=
  mul_nonneg (mul_nonneg (by norm_num) (Work.FTS.GalBasis.cc.K_nonneg_of_mem_Iθ hθ))
    (tl12_SwG_nonneg α hθ)

lemma tl12_KG_le_nine (α : ℝ) {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ)
    (hγ : 0 ≤ Work.Spaces.gam α / 2) : KG α θ ≤ 9 := by
  have hK := Work.FTS.GalBasis.cc.K_le_three_of_mem_Iθ hθ
  have hS := Real.rpow_le_one (tl12_sin_two_nonneg hθ) (Real.sin_le_one (2 * θ)) hγ
  have hK0 := Work.FTS.GalBasis.cc.K_nonneg_of_mem_Iθ hθ
  have hS0 : 0 ≤ Real.sin (2 * θ) ^ (Work.Spaces.gam α / 2) :=
    Real.rpow_nonneg (tl12_sin_two_nonneg hθ) _
  rw [KG, SwG]
  nlinarith

lemma tl12_KG_sq_le (α : ℝ) {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ)
    (hγ : 0 ≤ Work.Spaces.gam α / 2) : (KG α θ) ^ 2 ≤ 81 := by
  have h1 := tl12_KG_le_nine α hθ hγ
  have h2 := tl12_KG_nonneg α hθ
  nlinarith

lemma tl12_Wlam3_nonneg {s : ℝ} (hs : 0 ≤ s) : 0 ≤ Wlam3 s := by
  rw [Wlam3]; exact div_nonneg hs (by positivity)

lemma tl12_Wlam3_le_Wlam {s : ℝ} (hs : 0 ≤ s) : Wlam3 s ≤ Work.FTS.GalBasis.cc.Wlam s := by
  rw [Wlam3, Work.FTS.GalBasis.cc.Wlam]
  rcases eq_or_lt_of_le hs with h | h
  · subst h; simp
  · have h1 : 0 < (1 + s) ^ 2 := by positivity
    have h2 : (1 + s) ^ 2 ≤ (1 + s) ^ 3 := by
      nlinarith [show (1 : ℝ) ≤ 1 + s by linarith]
    exact div_le_div_of_nonneg_left hs h1 h2

/-- `√(∫_θ KG²) ≤ 13` uniformly for `α > 0` (so the Cauchy–Schwarz constants below are
independent of `α`). -/
lemma tl12_sqrt_KG_sq_le (α : ℝ) (hα : 0 < α) :
    Real.sqrt (∫ θ in Work.Spaces.Iθ, (KG α θ) ^ 2) ≤ 13 := by
  have hγ := tl12_gam_half_nonneg hα
  have hcont : Continuous (KG α) := tl12_continuous_KG α hγ
  have hIθ : MeasurableSet Work.Spaces.Iθ := measurableSet_Icc
  have hInt : IntegrableOn (fun θ => (KG α θ) ^ 2) Work.Spaces.Iθ :=
    (hcont.pow 2).continuousOn.integrableOn_compact isCompact_Icc
  have h81 : IntegrableOn (fun _ : ℝ => (81 : ℝ)) Work.Spaces.Iθ :=
    integrableOn_const (by rw [Work.Spaces.Iθ, Real.volume_Icc]; simp)
  have hmono : ∫ θ in Work.Spaces.Iθ, (KG α θ) ^ 2
      ≤ ∫ θ in Work.Spaces.Iθ, (81 : ℝ) :=
    integral_mono_of_nonneg (Eventually.of_forall fun θ => sq_nonneg _) h81
      (MeasureTheory.ae_restrict_of_forall_mem hIθ fun θ hθ => tl12_KG_sq_le α hθ hγ)
  have hval : ∫ _θ in Work.Spaces.Iθ, (81 : ℝ) ≤ 162 := by
    have h : ∫ θ in Work.Spaces.Iθ, (81 : ℝ) ≤ 162 := by
      rw [Work.Spaces.Iθ, MeasureTheory.setIntegral_const]
      simp
      rw [max_eq_left (by positivity : (0 : ℝ) ≤ Real.pi / 2)]
      nlinarith [Real.pi_lt_four]
    exact h
  have hnn : 0 ≤ ∫ θ in Work.Spaces.Iθ, (KG α θ) ^ 2 :=
    integral_nonneg fun θ => sq_nonneg _
  have hsquare : (Real.sqrt (∫ θ in Work.Spaces.Iθ, (KG α θ) ^ 2)) ^ 2 ≤ 162 := by
    rw [Real.sq_sqrt hnn]
    exact le_trans hmono hval
  nlinarith [Real.sqrt_nonneg (∫ θ in Work.Spaces.Iθ, (KG α θ) ^ 2)]

/-! ## The pointwise identity for the transport density -/

/-- **The factorisation of the transport density** (for `s > 0` and `θ ∈ Iθ`): the
`L₁₂`-density of `Transport g` is the radial weight `Wlam3 s` times the angular pairing of
the profile `KG α` with the weighted `D_θ`-derivative of `g`. -/
lemma tl12_Transport_integrand_eq (α : ℝ) (g : ℝ → ℝ → ℝ) {s θ : ℝ} (hs : 0 < s)
    (hθ : θ ∈ Work.Spaces.Iθ) :
    Work.Spaces.K θ * Work.Coercivity.Transport g s θ / s
      = Wlam3 s * (KG α θ * (Work.Spaces.mixed 0 1 g s θ * Work.Spaces.Wt α s θ)) := by
  have ht0 : 0 ≤ Real.sin (2 * θ) := tl12_sin_two_nonneg hθ
  rw [Work.Coercivity.Transport, Work.Spaces.Dth, Work.Spaces.mixed_zero_left,
    Work.Spaces.DthIter_succ, Work.Spaces.DthIter_zero, Work.Spaces.Dth]
  rcases eq_or_lt_of_le ht0 with hzero | hpos
  · have hsin0 : Real.sin (2 * θ) = 0 := hzero.symm
    rw [hsin0]
    simp
  · have hsin : 0 < Real.sin (2 * θ) := hpos
    have hsum : Work.Spaces.gam α / 2 + -(Work.Spaces.gam α / 2) = 0 := by ring
    have hSW : SwG α θ * Work.Spaces.wTheta α θ = 1 := by
      rw [SwG, Work.Spaces.wTheta, ← Real.rpow_add hsin, hsum, Real.rpow_zero]
    have hW3 : Wlam3 s * Work.Spaces.w s = 1 / (s * (1 + s)) := by
      rw [Wlam3, Work.Spaces.w]
      field_simp
    have hre : Wlam3 s * (3 * Work.Spaces.K θ * SwG α θ *
          ((Real.sin (2 * θ) * Work.Spaces.pth g s θ) *
            (Work.Spaces.w s * Work.Spaces.wTheta α θ)))
        = (Wlam3 s * Work.Spaces.w s) * (SwG α θ * Work.Spaces.wTheta α θ)
            * (3 * Work.Spaces.K θ * (Real.sin (2 * θ) * Work.Spaces.pth g s θ)) := by
      ring
    rw [KG, Work.Spaces.Wt, hre, hW3, hSW]
    field_simp

/-- The `L₁₂`-density of the transport term as a constant times an angular integral. -/
lemma tl12_L12dens_Transport_eq (α : ℝ) (g : ℝ → ℝ → ℝ) {s : ℝ} (hs : 0 < s) :
    Work.Construction.L12dens (Work.Coercivity.Transport g) s
      = Wlam3 s * ∫ θ in Work.Spaces.Iθ,
          KG α θ * (Work.Spaces.mixed 0 1 g s θ * Work.Spaces.Wt α s θ) := by
  have hI : Work.Spaces.Iθ = Set.Icc 0 (π / 2) := rfl
  rw [Work.Construction.L12dens, Work.FM.L12dens, hI]
  calc ∫ θ in Set.Icc 0 (π / 2), Work.Spaces.K θ * Work.Coercivity.Transport g s θ / s
      = ∫ θ in Set.Icc 0 (π / 2),
          Wlam3 s * (KG α θ * (Work.Spaces.mixed 0 1 g s θ * Work.Spaces.Wt α s θ)) := by
        refine setIntegral_congr_fun measurableSet_Icc (fun θ hθ => ?_)
        exact tl12_Transport_integrand_eq α g hs (by simpa only [hI] using hθ)
    _ = Wlam3 s * ∫ θ in Set.Icc 0 (π / 2),
          KG α θ * (Work.Spaces.mixed 0 1 g s θ * Work.Spaces.Wt α s θ) :=
        integral_const_mul _ _

/-! ## The angular Cauchy–Schwarz step -/

lemma tl12_abs_integral_KG_le (α : ℝ) (hα : 0 < α) (g : ℝ → ℝ → ℝ) {s : ℝ}
    (hint : IntegrableOn (fun θ => Work.Spaces.HkIntegrand α 4 g s θ) Work.Spaces.Iθ) :
    |∫ θ in Work.Spaces.Iθ, KG α θ * (Work.Spaces.mixed 0 1 g s θ * Work.Spaces.Wt α s θ)|
      ≤ Real.sqrt (∫ θ in Work.Spaces.Iθ, (KG α θ) ^ 2)
        * Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g s θ) := by
  have hγ : 0 ≤ Work.Spaces.gam α / 2 := tl12_gam_half_nonneg hα
  set u : ℝ → ℝ := fun θ => KG α θ with hu
  set v : ℝ → ℝ := fun θ => Work.Spaces.mixed 0 1 g s θ * Work.Spaces.Wt α s θ with hv
  set w : ℝ → ℝ := fun θ => Real.sqrt (Work.Spaces.HkIntegrand α 4 g s θ) with hw
  have hIθ : MeasurableSet Work.Spaces.Iθ := measurableSet_Icc
  have hHk_nn : ∀ θ : ℝ, 0 ≤ Work.Spaces.HkIntegrand α 4 g s θ :=
    fun θ => Work.Spaces.HkIntegrand_nonneg α 4 g s θ
  have hw_nn : ∀ θ : ℝ, 0 ≤ w θ := by intro θ; rw [hw]; exact Real.sqrt_nonneg _
  have hvw : ∀ θ : ℝ, |v θ| ≤ w θ := by
    intro θ
    have h1 : (v θ) ^ 2 ≤ Work.Spaces.HkIntegrand α 4 g s θ := by
      rw [hv]
      exact Work.Spaces.sq_le_HkIntegrand_mixed α 4 g s θ 1 0 (by norm_num) (by norm_num)
    rw [hw, ← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_le_sqrt h1
  have hcont_u : Continuous u := by rw [hu]; exact tl12_continuous_KG α hγ
  have hw_aesm : AEStronglyMeasurable w (volume.restrict Work.Spaces.Iθ) := by
    rw [hw]
    exact (hint.aestronglyMeasurable.aemeasurable.sqrt).aestronglyMeasurable
  have hu2_int : IntegrableOn (fun θ => (u θ) ^ 2) Work.Spaces.Iθ :=
    (hcont_u.pow 2).continuousOn.integrableOn_compact isCompact_Icc
  have hw2_int : IntegrableOn (fun θ => (w θ) ^ 2) Work.Spaces.Iθ := by
    refine hint.congr_fun (fun θ _ => ?_) hIθ
    rw [hw]; exact (Real.sq_sqrt (hHk_nn θ)).symm
  have huw_int : IntegrableOn (fun θ => |u θ| * w θ) Work.Spaces.Iθ := by
    have hmaj : IntegrableOn (fun θ => ((u θ) ^ 2 + (w θ) ^ 2) / 2) Work.Spaces.Iθ :=
      (hu2_int.add hw2_int).div_const 2
    refine hmaj.mono' ((hcont_u.abs.aestronglyMeasurable).mul hw_aesm) ?_
    filter_upwards with θ
    have h1 : 0 ≤ |u θ| := abs_nonneg _
    have h2 : 0 ≤ w θ := hw_nn θ
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg h2, abs_of_nonneg h1]
    have key : |u θ| * w θ ≤ (|u θ| ^ 2 + (w θ) ^ 2) / 2 := by
      nlinarith [sq_nonneg (|u θ| - w θ), sq_nonneg (|u θ| + w θ)]
    rw [sq_abs (u θ)] at key
    exact key
  have hMemLp_u : MemLp (fun θ => |u θ|) 2 (volume.restrict Work.Spaces.Iθ) :=
    (memLp_two_iff_integrable_sq (μ := volume.restrict Work.Spaces.Iθ)
      (f := fun θ => |u θ|) hcont_u.abs.aestronglyMeasurable).mpr
      (hu2_int.congr (Eventually.of_forall fun θ => (sq_abs (u θ)).symm))
  have hMemLp_w : MemLp w 2 (volume.restrict Work.Spaces.Iθ) :=
    (memLp_two_iff_integrable_sq (μ := volume.restrict Work.Spaces.Iθ) hw_aesm).mpr hw2_int
  have hcs := Work.FTS.EllipticEst.remov.Ebs.abs_integral_mul_le_sqrt (u := fun θ => |u θ|)
    (v := w) hMemLp_u hMemLp_w
  have hsqrt_u : Real.sqrt (∫ θ in Work.Spaces.Iθ, |u θ| ^ 2)
      = Real.sqrt (∫ θ in Work.Spaces.Iθ, (KG α θ) ^ 2) := by
    congr 1
    simp only [hu]
    exact integral_congr_ae (Eventually.of_forall fun θ => sq_abs (KG α θ))
  have hsqrt_w : Real.sqrt (∫ θ in Work.Spaces.Iθ, (w θ) ^ 2)
      = Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g s θ) := by
    congr 1
    refine integral_congr_ae (Eventually.of_forall fun θ => ?_)
    rw [hw]; exact Real.sq_sqrt (hHk_nn θ)
  have h1 : |∫ θ in Work.Spaces.Iθ, u θ * v θ|
      ≤ ∫ θ in Work.Spaces.Iθ, |u θ * v θ| := by
    simpa only [Real.norm_eq_abs] using
      (MeasureTheory.norm_integral_le_integral_norm (μ := volume.restrict Work.Spaces.Iθ)
        (f := fun θ => u θ * v θ))
  have h2 : ∫ θ in Work.Spaces.Iθ, |u θ * v θ| ≤ ∫ θ in Work.Spaces.Iθ, |u θ| * w θ := by
    refine integral_mono_of_nonneg (Eventually.of_forall fun θ => abs_nonneg _) huw_int
      (Eventually.of_forall fun θ => ?_)
    show |u θ * v θ| ≤ |u θ| * w θ
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (hvw θ) (abs_nonneg _)
  have h3 : ∫ θ in Work.Spaces.Iθ, |u θ| * w θ
      = |∫ θ in Work.Spaces.Iθ, |u θ| * w θ| := by
    rw [abs_of_nonneg]
    exact integral_nonneg fun θ => mul_nonneg (abs_nonneg _) (hw_nn θ)
  calc |∫ θ in Work.Spaces.Iθ, KG α θ * (Work.Spaces.mixed 0 1 g s θ * Work.Spaces.Wt α s θ)|
      = |∫ θ in Work.Spaces.Iθ, u θ * v θ| := by simp only [hu, hv]
    _ ≤ ∫ θ in Work.Spaces.Iθ, |u θ * v θ| := h1
    _ ≤ ∫ θ in Work.Spaces.Iθ, |u θ| * w θ := h2
    _ = |∫ θ in Work.Spaces.Iθ, |u θ| * w θ| := h3
    _ ≤ Real.sqrt (∫ θ in Work.Spaces.Iθ, |u θ| ^ 2)
          * Real.sqrt (∫ θ in Work.Spaces.Iθ, (w θ) ^ 2) := hcs
    _ = Real.sqrt (∫ θ in Work.Spaces.Iθ, (KG α θ) ^ 2)
          * Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g s θ) := by
        rw [hsqrt_u, hsqrt_w]

/-! ## The radial Cauchy–Schwarz step -/

lemma tl12_integral_abs_L12dens_Transport_le (α : ℝ) (hα : 0 < α) (g : ℝ → ℝ → ℝ)
    (hmem : Work.Spaces.HkMem α 4 g) (B : ℝ) (hB : 0 ≤ B)
    (hbd : ∀ s ∈ Set.Ioi (0 : ℝ),
      |Work.Construction.L12dens (Work.Coercivity.Transport g) s|
        ≤ Wlam3 s * (B * Real.sqrt
            (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g s θ))) :
    ∫ s in Set.Ioi (0 : ℝ), |Work.Construction.L12dens (Work.Coercivity.Transport g) s|
      ≤ B * Real.sqrt Work.FTS.GalBasis.cc.W2 * Real.sqrt (Work.Spaces.HkSq α 4 g) := by
  set H : ℝ → ℝ := fun s => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g s θ with hH
  set A : ℝ → ℝ := fun s => Real.sqrt (H s) with hA
  have hHnn : ∀ s, 0 ≤ H s :=
    fun s => integral_nonneg fun θ => Work.Spaces.HkIntegrand_nonneg α 4 g s θ
  have hAnn : ∀ s, 0 ≤ A s := fun s => Real.sqrt_nonneg _
  -- the marginal `H` is integrable on `(0,∞)`
  have hH_int : IntegrableOn H (Set.Ioi 0) := hmem.2.mono_set Set.Ioi_subset_Ici_self
  have hH_aesm : AEStronglyMeasurable H (volume.restrict (Set.Ioi 0)) :=
    hH_int.aestronglyMeasurable
  have hA_aesm : AEStronglyMeasurable A (volume.restrict (Set.Ioi 0)) := by
    rw [hA]; exact (hH_aesm.aemeasurable.sqrt).aestronglyMeasurable
  have hA2_int : IntegrableOn (fun s => A s ^ 2) (Set.Ioi 0) := by
    refine hH_int.congr ?_
    filter_upwards with s
    rw [hA]
    exact (Real.sq_sqrt (hHnn s)).symm
  have hA_memLp : MemLp A 2 (volume.restrict (Set.Ioi 0)) :=
    (memLp_two_iff_integrable_sq hA_aesm).mpr hA2_int
  -- the radial weight `Wlam3` is square-integrable, dominated by `Wlam`
  have hcont3 : ContinuousOn Wlam3 (Set.Ioi 0) := by
    change ContinuousOn (fun s : ℝ => s / (1 + s) ^ 3) (Set.Ioi 0)
    refine ContinuousOn.div continuousOn_id ((continuousOn_const.add continuousOn_id).pow 3)
      (fun s hs => ?_)
    have hs' : (0 : ℝ) < s := hs
    have h1 : 0 < 1 + s := by linarith
    positivity
  have hWlam3_aesm : AEStronglyMeasurable Wlam3 (volume.restrict (Set.Ioi 0)) :=
    hcont3.aestronglyMeasurable measurableSet_Ioi
  have hWlam3_sq_int : IntegrableOn (fun s => Wlam3 s ^ 2) (Set.Ioi 0) := by
    refine Work.Elliptic.psi_sq_integrable_aux.mono' ((hcont3.pow 2).aestronglyMeasurable
      measurableSet_Ioi) ?_
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with s hs
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (Wlam3 s))]
    exact pow_le_pow_left₀ (tl12_Wlam3_nonneg (le_of_lt hs)) (tl12_Wlam3_le_Wlam (le_of_lt hs)) 2
  have hWlam3_memLp : MemLp Wlam3 2 (volume.restrict (Set.Ioi 0)) :=
    (memLp_two_iff_integrable_sq hWlam3_aesm).mpr hWlam3_sq_int
  have hW2le : ∫ s in Set.Ioi 0, Wlam3 s ^ 2 ≤ Work.FTS.GalBasis.cc.W2 := by
    rw [Work.FTS.GalBasis.cc.W2]
    refine integral_mono_of_nonneg (Eventually.of_forall fun s => sq_nonneg _)
      Work.Elliptic.psi_sq_integrable_aux ?_
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with s hs
    exact pow_le_pow_left₀ (tl12_Wlam3_nonneg (le_of_lt hs)) (tl12_Wlam3_le_Wlam (le_of_lt hs)) 2
  -- `∫_{(0,∞)} A² = HkSq α 4 g`, up to the null set `{0}`
  have hIz_eq : ∫ s in Work.Spaces.Iz, H s = Work.Spaces.HkSq α 4 g := by rw [hH]; rfl
  have hA2sq : ∫ s in Set.Ioi 0, A s ^ 2 = Work.Spaces.HkSq α 4 g := by
    have h1 : ∫ s in Set.Ioi 0, A s ^ 2 = ∫ s in Set.Ioi 0, H s :=
      setIntegral_congr_fun measurableSet_Ioi fun s _ => by
        rw [hA]; exact Real.sq_sqrt (hHnn s)
    have h2 : ∫ s in Set.Ioi 0, H s = ∫ s in Work.Spaces.Iz, H s :=
      MeasureTheory.setIntegral_congr_set
        (MeasureTheory.Ioi_ae_eq_Ici' (MeasureTheory.measure_singleton 0))
    rw [h1, h2, hIz_eq]
  -- Cauchy–Schwarz in the radial variable
  have hCS : ∫ s in Set.Ioi 0, Wlam3 s * A s
      ≤ Real.sqrt Work.FTS.GalBasis.cc.W2 * Real.sqrt (Work.Spaces.HkSq α 4 g) := by
    have hcs := Work.FTS.EllipticEst.remov.Ebs.abs_integral_mul_le_sqrt
      (u := Wlam3) (v := A) (s := Set.Ioi 0) hWlam3_memLp hA_memLp
    rw [hA2sq] at hcs
    have hnn : 0 ≤ ∫ s in Set.Ioi 0, Wlam3 s * A s := by
      refine MeasureTheory.integral_nonneg_of_ae ?_
      show ∀ᵐ s ∂(volume.restrict (Set.Ioi (0 : ℝ))), (0 : ℝ) ≤ Wlam3 s * A s
      rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioi]
      exact Eventually.of_forall fun s hs =>
        mul_nonneg (tl12_Wlam3_nonneg (le_of_lt hs)) (hAnn s)
    rw [abs_of_nonneg hnn] at hcs
    exact le_trans hcs (mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hW2le)
      (Real.sqrt_nonneg _))
  -- AM–GM, giving integrability of the majorant
  have hAMGM : ∀ s ∈ Set.Ioi (0 : ℝ), Wlam3 s * A s ≤ Wlam3 s ^ 2 + A s ^ 2 := by
    intro s _
    nlinarith [sq_nonneg (Wlam3 s - A s)]
  have hsum_int : IntegrableOn (fun s => Wlam3 s ^ 2 + A s ^ 2) (Set.Ioi 0) :=
    hWlam3_sq_int.add hA2_int
  have hdom_int : IntegrableOn (fun s => B * (Wlam3 s * A s)) (Set.Ioi 0) := by
    refine Integrable.mono' (hsum_int.const_mul B) ?_ ?_
    · exact (hWlam3_aesm.mul hA_aesm).const_mul B
    · filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with s hs
      have hnn : 0 ≤ B * (Wlam3 s * A s) :=
        mul_nonneg hB (mul_nonneg (tl12_Wlam3_nonneg (le_of_lt hs)) (hAnn s))
      rw [Real.norm_eq_abs, abs_of_nonneg hnn]
      exact mul_le_mul_of_nonneg_left (hAMGM s hs) hB
  have h2 : ∫ s in Set.Ioi 0, |Work.Construction.L12dens (Work.Coercivity.Transport g) s|
      ≤ ∫ s in Set.Ioi 0, B * (Wlam3 s * A s) := by
    refine integral_mono_of_nonneg (Eventually.of_forall fun s => abs_nonneg _) hdom_int ?_
    show ∀ᵐ s ∂(volume.restrict (Set.Ioi (0 : ℝ))),
      |Work.Construction.L12dens (Work.Coercivity.Transport g) s| ≤ B * (Wlam3 s * A s)
    rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioi]
    refine Eventually.of_forall fun s hs => ?_
    have hb := hbd s hs
    have hbA : |Work.Construction.L12dens (Work.Coercivity.Transport g) s|
        ≤ Wlam3 s * (B * A s) := by simpa only [hA, hH] using hb
    calc |Work.Construction.L12dens (Work.Coercivity.Transport g) s|
        ≤ Wlam3 s * (B * A s) := hbA
      _ = B * (Wlam3 s * A s) := by ring
  calc ∫ s in Set.Ioi 0, |Work.Construction.L12dens (Work.Coercivity.Transport g) s|
      ≤ ∫ s in Set.Ioi 0, B * (Wlam3 s * A s) := h2
    _ = B * ∫ s in Set.Ioi 0, Wlam3 s * A s := integral_const_mul B _
    _ ≤ B * (Real.sqrt Work.FTS.GalBasis.cc.W2 * Real.sqrt (Work.Spaces.HkSq α 4 g)) :=
        mul_le_mul_of_nonneg_left hCS hB
    _ = B * Real.sqrt Work.FTS.GalBasis.cc.W2 * Real.sqrt (Work.Spaces.HkSq α 4 g) := by ring

/-! ## The final estimate -/

theorem Transport_L12_zero_le : ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (g : ℝ → ℝ → ℝ),
    0 < α → α ≤ 1 → Work.Spaces.HkMem α 4 g →
    |Work.Coercivity.L12f (Work.Coercivity.Transport g) 0|
      ≤ C * Work.Spaces.HkNorm α 4 g := by
  refine ⟨1 + 13 * Real.sqrt Work.FTS.GalBasis.cc.W2, by positivity, ?_⟩
  intro α g hα hα1 hmem
  have hBK : Real.sqrt (∫ θ in Work.Spaces.Iθ, (KG α θ) ^ 2) ≤ 13 := tl12_sqrt_KG_sq_le α hα
  -- the pointwise (in `s`) bound
  have hbd : ∀ s ∈ Set.Ioi (0 : ℝ),
      |Work.Construction.L12dens (Work.Coercivity.Transport g) s|
        ≤ Wlam3 s * (13 * Real.sqrt
            (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g s θ)) := by
    intro s hs
    have hslice : IntegrableOn (fun θ => Work.Spaces.HkIntegrand α 4 g s θ) Work.Spaces.Iθ :=
      hmem.1 s (by simpa [Work.Spaces.Iz] using le_of_lt hs)
    have hW3nn : 0 ≤ Wlam3 s := tl12_Wlam3_nonneg (le_of_lt hs)
    rw [tl12_L12dens_Transport_eq α g hs, abs_mul, abs_of_nonneg hW3nn]
    refine mul_le_mul_of_nonneg_left ?_ hW3nn
    calc |∫ θ in Work.Spaces.Iθ,
            KG α θ * (Work.Spaces.mixed 0 1 g s θ * Work.Spaces.Wt α s θ)|
        ≤ Real.sqrt (∫ θ in Work.Spaces.Iθ, (KG α θ) ^ 2)
            * Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g s θ) :=
          tl12_abs_integral_KG_le α hα g hslice
      _ ≤ 13 * Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g s θ) :=
          mul_le_mul_of_nonneg_right hBK (Real.sqrt_nonneg _)
  have hrad := tl12_integral_abs_L12dens_Transport_le α hα g hmem 13 (by norm_num) hbd
  calc |Work.Coercivity.L12f (Work.Coercivity.Transport g) 0|
      = |∫ s in Set.Ioi (0 : ℝ),
          Work.Construction.L12dens (Work.Coercivity.Transport g) s| := by
        simp only [Work.Coercivity.L12f, Work.FM.L12, Work.FM.L12dens,
          Work.Construction.L12dens]
    _ ≤ ∫ s in Set.Ioi (0 : ℝ),
          |Work.Construction.L12dens (Work.Coercivity.Transport g) s| := by
        simpa only [Real.norm_eq_abs] using
          (MeasureTheory.norm_integral_le_integral_norm
            (μ := volume.restrict (Set.Ioi (0 : ℝ)))
            (f := fun s => Work.Construction.L12dens (Work.Coercivity.Transport g) s))
    _ ≤ 13 * Real.sqrt Work.FTS.GalBasis.cc.W2 * Real.sqrt (Work.Spaces.HkSq α 4 g) := hrad
    _ = 13 * Real.sqrt Work.FTS.GalBasis.cc.W2 * Work.Spaces.HkNorm α 4 g := by
        rw [Work.Spaces.HkNorm]
    _ ≤ (1 + 13 * Real.sqrt Work.FTS.GalBasis.cc.W2) * Work.Spaces.HkNorm α 4 g := by
        have h1 := Work.Spaces.HkNorm_nonneg α 4 g
        have h2 := Real.sqrt_nonneg Work.FTS.GalBasis.cc.W2
        nlinarith

end Work.FTS.StrongPersist.L3Aux
