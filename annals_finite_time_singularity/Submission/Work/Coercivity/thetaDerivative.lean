/-
# The `D_θ`-coercivity estimate (`prop:thetaderivative`)

This file proves the paper's Proposition `prop:thetaderivative` of

  T. M. Elgindi, *Finite-time singularity formation for `C^{1,α}` solutions to the
  incompressible Euler equations on `ℝ³`*, Annals of Math. **194** (2021),

in the form

  `(1/4 - α)·|D_θ f · w/√sin(2θ)^γ|² - 10⁷α·|f w|²
      ≤ (D_θ 𝓛_Γ^T f, D_θ f · w²/sin(2θ)^γ)_{L²}`.

The proof expands `D_θ(𝓛_Γ^T f) = Aop(D_θ f) + T2 + T4` pointwise (`dth_LGammaT_expansion`),
bounds the coercive part `Aop(D_θ f)` from below by `(1/2 - 3α/10)EDth` (the cut-off
argument in `theta_coercive`, which reduces to the compact-support estimate `wip_Aop_ge`
of `𝓛 - (3/(1+z))D_θ`), and bounds each of the two `D_θΓ`-terms by Cauchy–Schwarz
(`wip_T2_ge`, `wip_T4_ge`).  The numerical constants close because
`1/14 + 5/28 = 1/4` and `3·10⁶ + 6·10⁶ < 10⁷`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.Coercivity.Defs
import Submission.Work.Coercivity.Basic
import Submission.Work.Coercivity.wip_L_self
import Submission.Work.Coercivity.thetaAux
import Submission.Work.Coercivity.wip_Aop_ge
import Submission.Work.Coercivity.IBP_of_zsupport
import Submission.Work.Coercivity.dth_LGammaT_expansion
import Submission.Work.Coercivity.EDth_eq_wip
import Submission.Work.Coercivity.theta_coercive
import Submission.Work.Coercivity.wip_T2_ge
import Submission.Work.Coercivity.wip_T4_ge

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

/-- Congruence of `wip` in its first argument under an a.e. equality of the two
`(z,θ)`-functions, in the iterated-integral form adapted to `wip`. -/
theorem wip_congr_ae {ρ g₁ g₁' g₂ : ℝ → ℝ → ℝ}
    (h : ∀ᵐ z ∂(MeasureTheory.volume.restrict Spaces.Iz),
      ∀ᵐ θ ∂(MeasureTheory.volume.restrict Spaces.Iθ), g₁ z θ = g₁' z θ) :
    wip ρ g₁ g₂ = wip ρ g₁' g₂ := by
  simp only [wip]
  apply MeasureTheory.integral_congr_ae
  filter_upwards [h] with z hz
  apply MeasureTheory.integral_congr_ae
  filter_upwards [hz] with θ hθ
  rw [hθ]

theorem thetaDerivative (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (f : ℝ → ℝ → ℝ)
    (hf : IBP f) (hfH : HardyHyp f) (hΓ : GammaL2Bnd α) (hΓ2 : GammaPointwiseBnd α)
    (hi : CoerciveData α f) :
    (1 / 4 - α) * EDth α f - 10 ^ 7 * α * Ef f
      ≤ wip (fun z θ => Spaces.w z ^ 2 * (Real.sin (2 * θ)) ^ (-(Spaces.gam α)))
          (Spaces.Dth (LGammaT α f)) (Spaces.Dth f) := by
  obtain ⟨hT2int, hT2ineq⟩ := wip_T2_ge α hα hα1 f hf hfH hΓ2 hi
  obtain ⟨hT4int, hT4ineq⟩ := wip_T4_ge α hα hα1 f hf hfH hΓ2 hi
  -- a.e. positivity in `z` and interiority in `θ`
  have hz_ae : ∀ᵐ z ∂(MeasureTheory.volume.restrict Spaces.Iz), 0 < z := by
    rw [Spaces.Iz, MeasureTheory.ae_restrict_iff' measurableSet_Ici, MeasureTheory.ae_iff]
    have hset : {z : ℝ | ¬ (z ∈ Set.Ici (0:ℝ) → 0 < z)} = {0} := by
      ext z; simp only [Set.mem_setOf_eq, Set.mem_Ici, Set.mem_singleton_iff, not_imp]
      constructor
      · rintro ⟨h1, h2⟩; exact le_antisymm (not_lt.mp h2) h1
      · rintro rfl; exact ⟨le_refl 0, lt_irrefl 0⟩
    rw [hset, Real.volume_singleton]
  have hθ_ae : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Spaces.Iθ), θ ∈ Set.Ioo 0 (π / 2) := by
    rw [Spaces.Iθ, MeasureTheory.ae_restrict_iff' measurableSet_Icc, MeasureTheory.ae_iff]
    have hset : {θ : ℝ | ¬ (θ ∈ Set.Icc (0:ℝ) (π / 2) → θ ∈ Set.Ioo 0 (π / 2))}
        = ({0} : Set ℝ) ∪ {π / 2} := by
      ext θ; simp only [Set.mem_setOf_eq, Set.mem_Icc, Set.mem_Ioo, Set.mem_union,
        Set.mem_singleton_iff, not_imp]
      constructor
      · rintro ⟨⟨h1, h2⟩, h3⟩
        rcases not_and_or.mp h3 with h | h
        · left; exact le_antisymm (not_lt.mp h) h1
        · right; exact le_antisymm h2 (not_lt.mp h)
      · rintro (rfl | rfl)
        · exact ⟨⟨le_refl 0, by positivity⟩, by simp⟩
        · exact ⟨⟨by positivity, le_refl _⟩, by simp⟩
    rw [hset]
    exact MeasureTheory.measure_union_null (by rw [Real.volume_singleton])
      (by rw [Real.volume_singleton])
  -- the a.e. pointwise expansion
  have hpt_iter : ∀ᵐ z ∂(MeasureTheory.volume.restrict Spaces.Iz),
      ∀ᵐ θ ∂(MeasureTheory.volume.restrict Spaces.Iθ),
      Spaces.Dth (LGammaT α f) z θ
        = Aop (Spaces.Dth f) z θ + T2 α f z θ + T4 α f z θ := by
    filter_upwards [hz_ae] with z hz
    filter_upwards [hθ_ae] with θ hθ
    exact dth_LGammaT_expansion α f hf.smooth hz hθ
  have hvol : MeasureTheory.volume.restrict (Spaces.Iz ×ˢ Spaces.Iθ)
      = (MeasureTheory.volume.restrict Spaces.Iz).prod (MeasureTheory.volume.restrict Spaces.Iθ) := by
    rw [MeasureTheory.Measure.volume_eq_prod]
    exact (MeasureTheory.Measure.prod_restrict _ _).symm
  have hprod : ∀ᵐ p ∂(MeasureTheory.volume.restrict (Spaces.Iz ×ˢ Spaces.Iθ)),
      0 < p.1 ∧ p.2 ∈ Set.Ioo 0 (π / 2) := by
    rw [hvol]
    exact (MeasureTheory.Measure.ae_prod_mem_iff_ae_ae_mem
      (s := Set.Ioi (0:ℝ) ×ˢ Set.Ioo (0:ℝ) (π / 2))
      (measurableSet_Ioi.prod measurableSet_Ioo)).mpr
      (hz_ae.mono (fun z hz => hθ_ae.mono (fun θ hθ => ⟨hz, hθ⟩)))
  have hpt_prod : ∀ᵐ p ∂(MeasureTheory.volume.restrict (Spaces.Iz ×ˢ Spaces.Iθ)),
      Spaces.Dth (LGammaT α f) p.1 p.2
        = Aop (Spaces.Dth f) p.1 p.2 + T2 α f p.1 p.2 + T4 α f p.1 p.2 := by
    filter_upwards [hprod] with p hp
    exact dth_LGammaT_expansion α f hf.smooth hp.1 hp.2
  -- integrability of the `Aop` cross term
  have hdth : MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => Spaces.Dth (LGammaT α f) z θ * Spaces.Dth f z θ * thetaW α z θ))
      (Spaces.Iz ×ˢ Spaces.Iθ) :=
    hi.intDthDth.congr (Filter.Eventually.of_forall fun p => by
      obtain ⟨a, b⟩ := p; simp only [Function.uncurry_apply_pair, thetaW]; ring)
  have hintAop : MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => Aop (Spaces.Dth f) z θ * Spaces.Dth f z θ * thetaW α z θ))
      (Spaces.Iz ×ˢ Spaces.Iθ) := by
    have h := (hdth.sub hT2int).sub hT4int
    refine h.congr ?_
    filter_upwards [hpt_prod] with p hp
    obtain ⟨a, b⟩ := p
    simp only [Pi.sub_apply, Function.uncurry_apply_pair] at hp ⊢
    rw [hp]; ring
  have hAop := theta_coercive α hα hα1 f hf hintAop
  -- integrability for the two additivity steps
  have hA2 : MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => (Aop (Spaces.Dth f) z θ + T2 α f z θ) * Spaces.Dth f z θ * thetaW α z θ))
      (Spaces.Iz ×ˢ Spaces.Iθ) := by
    have h := hintAop.add hT2int
    refine h.congr ?_
    filter_upwards with p
    obtain ⟨a, b⟩ := p
    simp only [Pi.add_apply, Pi.sub_apply, Function.uncurry_apply_pair]
    ring
  -- the two splittings
  have hsub2 : wip (thetaW α) (fun z θ => Aop (Spaces.Dth f) z θ + T2 α f z θ + T4 α f z θ)
        (Spaces.Dth f)
      = wip (thetaW α) (Aop (Spaces.Dth f)) (Spaces.Dth f)
        + wip (thetaW α) (T2 α f) (Spaces.Dth f) + wip (thetaW α) (T4 α f) (Spaces.Dth f) := by
    rw [wip_add_left (g := fun z θ => Aop (Spaces.Dth f) z θ + T2 α f z θ)
          (h := T4 α f) (k := Spaces.Dth f) hA2 hT4int,
        wip_add_left (g := Aop (Spaces.Dth f)) (h := T2 α f) (k := Spaces.Dth f)
          hintAop hT2int]
  rw [wip_congr_ae hpt_iter]
  change (1 / 4 - α) * EDth α f - 10 ^ 7 * α * Ef f ≤
    wip (thetaW α)
      (fun z θ => Aop (Spaces.Dth f) z θ + T2 α f z θ + T4 α f z θ) (Spaces.Dth f)
  have hEDth_nn : 0 ≤ EDth α f := by
    simp only [EDth, Spaces.L2Sq]
    exact integral_nonneg (fun z => integral_nonneg (fun θ => sq_nonneg _))
  have hEf_nn : 0 ≤ Ef f := by
    simp only [Ef, Spaces.L2Sq]
    exact integral_nonneg (fun z => integral_nonneg (fun θ => sq_nonneg _))
  rw [hsub2]
  nlinarith [hAop, hT2ineq, hT4ineq, hEDth_nn, hEf_nn, hα]

end Work.Coercivity
