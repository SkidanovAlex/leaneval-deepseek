import Mathlib
import Submission.Work.LayerCont.SplitPoint
import Submission.Work.LayerCont.GcuspHolomorphic
import Submission.Work.LayerCont.TruncContinuation
import Submission.Work.Asymptotics.differentiableAt_integral_Ioo

/-!
# Holomorphy of `highPartAt`

`highPartAt G p r τ = highPart G τ r - sinSqC r · ∫_1^p 𝒢(τ,it) e^{-πr²t} dt` is the sum of
the closed-form high part (a `ℂ`-linear combination of the cusp coefficient functions
`G i j`, holomorphic in `τ`) and a parametric *interval* integral of the cusp model
`Aexp = 𝒢(τ,it)` against the Gaussian weight.  The latter is holomorphic in `τ` because the
interval of integration is compact: the integrand is jointly continuous on
`closedBall z₀ ρ × [min 1 p, max 1 p]`, hence bounded there, and holomorphic in `z` for every
fixed `t`; the general engine `Work.Asymptotics.differentiableAt_integral_Ioo` then gives
differentiation under the integral sign, and the sign bookkeeping converting the interval
integral `∫_a^b` to the signed set integral over `Set.Ioo (min a b) (max a b)` is isolated in
`intervalIntegral_eq_smul_integral_Ioo`.
-/

noncomputable section

namespace Work.LayerCont

open UpperHalfPlane MeasureTheory Filter Topology
open scoped Topology Manifold

/-- **Interval integral as a signed integral over an unordered `Ioo`.**  For a `ℂ`-valued
function `f` and real endpoints `a`, `b`,

  `∫_a^b f = (if a ≤ b then 1 else -1) · ∫_{Ioo (min a b) (max a b)} f`.

This is the identity that lets the set-integral machinery (`differentiableAt_integral_Ioo`,
stated over `Ioo`) be applied to the interval integrals of the CKMRV construction. -/
lemma intervalIntegral_eq_smul_integral_Ioo (f : ℝ → ℂ) (a b : ℝ) :
    ∫ t in a..b, f t
      = (if a ≤ b then (1 : ℂ) else -1) * ∫ t in Set.Ioo (min a b) (max a b), f t := by
  rw [intervalIntegral.intervalIntegral_eq_integral_uIoc]
  split_ifs with h
  · rw [Set.uIoc_of_le h, min_eq_left h, max_eq_right h, one_smul,
      setIntegral_congr_set (Ioo_ae_eq_Ioc (a := a) (b := b)).symm, one_mul]
  · rw [not_le] at h
    rw [Set.uIoc_of_ge h.le, min_eq_right h.le, max_eq_left h.le, neg_one_smul,
      neg_mul, neg_inj,
      setIntegral_congr_set (Ioo_ae_eq_Ioc (a := b) (b := a)).symm, one_mul]

/-- **Differentiation under the integral sign for an interval in the parameter `z`.**

Same hypotheses as `Work.Asymptotics.differentiableAt_integral_Ioo` (a value bound and
holomorphy on a ball `ball z₀ ρ`, and eventual a.e. strong measurability), but for the interval
integral `∫_a^b` instead of the set integral over `Ioo a b`. -/
theorem differentiableAt_intervalIntegral {F : ℂ → ℝ → ℂ} {a b : ℝ} {z₀ : ℂ} {ρ C : ℝ}
    (hρ : 0 < ρ)
    (hbound : ∀ᵐ u ∂(volume.restrict (Set.Ioo (min a b) (max a b))),
      ∀ z ∈ Metric.ball z₀ ρ, ‖F z u‖ ≤ C)
    (hdiff : ∀ᵐ u ∂(volume.restrict (Set.Ioo (min a b) (max a b))),
      ∀ z ∈ Metric.ball z₀ ρ, DifferentiableAt ℂ (fun z' => F z' u) z)
    (hmeas : ∀ᶠ z in nhds z₀, AEStronglyMeasurable (fun u : ℝ => F z u)
      (volume.restrict (Set.Ioo (min a b) (max a b)))) :
    DifferentiableAt ℂ (fun z => ∫ u in a..b, F z u) z₀ := by
  have hmain : DifferentiableAt ℂ
      (fun z => ∫ u in Set.Ioo (min a b) (max a b), F z u) z₀ :=
    Work.Asymptotics.differentiableAt_integral_Ioo (a := min a b) (b := max a b)
      (x₀ := z₀) (ρ := ρ) (C := C) hρ hbound hdiff hmeas
  have hEq : (fun z => ∫ u in a..b, F z u) =
      fun z => (if a ≤ b then (1 : ℂ) else -1) *
        ∫ u in Set.Ioo (min a b) (max a b), F z u :=
    funext fun z => intervalIntegral_eq_smul_integral_Ioo (fun u => F z u) a b
  rw [hEq]
  exact hmain.const_mul _

/-- **Holomorphy of `τ ↦ ∫_1^p Aexp (Gcusp ℓ d) τ t · e^{-πr²t} dt`.**

The integrand is jointly continuous on the compact rectangle `closedBall z₀ ρ × [min 1 p, max 1 p]`
(where `ρ = (Im z₀)/2` keeps the closed ball inside the upper half plane), hence bounded there;
for each fixed `t` it is holomorphic in `τ` (`differentiableAt_Aexp_ofComplex`), and for each `τ`
it is continuous in `t`.  `differentiableAt_intervalIntegral` then applies. -/
theorem mdifferentiable_Aexp_intervalIntegral (ℓ : Work.Kernels.LogLambdaData) (d : ℕ)
    (hd : d = 8 ∨ d = 24) (p r : ℝ) :
    MDifferentiable (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ)
      (fun τ : UpperHalfPlane => ∫ t in (1 : ℝ)..p,
        Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) τ t
          * Work.Asymptotics.gaussWeight r t) := by
  intro τ
  rw [UpperHalfPlane.mdifferentiableAt_iff]
  change DifferentiableAt ℂ (fun z : ℂ => ∫ t in (1 : ℝ)..p,
      Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) (UpperHalfPlane.ofComplex z) t
        * Work.Asymptotics.gaussWeight r t) (τ : ℂ)
  set ρ : ℝ := (τ : ℂ).im / 2 with hρdef
  have hρ : 0 < ρ := by
    rw [hρdef, UpperHalfPlane.coe_im]
    exact half_pos τ.im_pos
  have hK : IsCompact (Metric.closedBall (τ : ℂ) ρ
      ×ˢ Set.Icc (min (1 : ℝ) p) (max (1 : ℝ) p)) :=
    (isCompact_closedBall (τ : ℂ) ρ).prod isCompact_Icc
  have hcont : ContinuousOn (fun q : ℂ × ℝ =>
      Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) (UpperHalfPlane.ofComplex q.1) q.2
        * Work.Asymptotics.gaussWeight r q.2)
      (Metric.closedBall (τ : ℂ) ρ ×ˢ Set.Icc (min (1 : ℝ) p) (max (1 : ℝ) p)) := by
    intro q hq
    have hq1 : q.1 ∈ Metric.closedBall (τ : ℂ) ρ := hq.1
    have hqim : 0 < q.1.im := by
      have h1 : dist q.1 (τ : ℂ) ≤ ρ := by simpa [Metric.mem_closedBall] using hq1
      have h2 : (τ : ℂ).im - q.1.im ≤ |((τ : ℂ) - q.1).im| := by
        rw [Complex.sub_im]
        exact le_abs_self _
      have h3 : |((τ : ℂ) - q.1).im| ≤ ‖(τ : ℂ) - q.1‖ := Complex.abs_im_le_norm _
      have h4 : ‖(τ : ℂ) - q.1‖ = dist q.1 (τ : ℂ) := by
        rw [dist_eq_norm, norm_sub_rev]
      have h5 : (τ : ℂ).im = 2 * ρ := by
        rw [hρdef]; ring
      linarith
    have hofc : ContinuousAt (fun q : ℂ × ℝ => UpperHalfPlane.ofComplex q.1) q :=
      (UpperHalfPlane.contMDiffAt_ofComplex (n := ⊤) hqim).continuousAt.comp continuousAt_fst
    have hpair : ContinuousAt (fun q : ℂ × ℝ => (UpperHalfPlane.ofComplex q.1, q.2)) q :=
      hofc.prodMk continuousAt_snd
    have hA : ContinuousAt (fun q : ℂ × ℝ =>
        Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d)
          (UpperHalfPlane.ofComplex q.1) q.2) q :=
      (Work.Asymptotics.HalfFunnel.continuous_Aexp_tang ℓ d hd).continuousAt.comp hpair
    have hg : ContinuousAt (fun q : ℂ × ℝ => Work.Asymptotics.gaussWeight r q.2) q :=
      (by unfold Work.Asymptotics.gaussWeight; fun_prop :
        Continuous fun q : ℂ × ℝ => Work.Asymptotics.gaussWeight r q.2).continuousAt
    exact (hA.mul hg).continuousWithinAt
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hcont
  have hbound : ∀ᵐ u ∂(volume.restrict (Set.Ioo (min (1 : ℝ) p) (max (1 : ℝ) p))),
      ∀ z ∈ Metric.ball (τ : ℂ) ρ,
        ‖Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) (UpperHalfPlane.ofComplex z) u
          * Work.Asymptotics.gaussWeight r u‖ ≤ C := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with u hu
    intro z hz
    exact hC (z, u) ⟨Metric.ball_subset_closedBall hz, ⟨le_of_lt hu.1, le_of_lt hu.2⟩⟩
  have hdiff : ∀ᵐ u ∂(volume.restrict (Set.Ioo (min (1 : ℝ) p) (max (1 : ℝ) p))),
      ∀ z ∈ Metric.ball (τ : ℂ) ρ,
        DifferentiableAt ℂ (fun z' => Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d)
          (UpperHalfPlane.ofComplex z') u * Work.Asymptotics.gaussWeight r u) z := by
    refine Filter.Eventually.of_forall (fun u z hz => ?_)
    have hzpos : 0 < z.im := by
      have h1 : dist z (τ : ℂ) < ρ := by simpa [Metric.mem_ball] using hz
      have h2 : (τ : ℂ).im - z.im ≤ |((τ : ℂ) - z).im| := by
        rw [Complex.sub_im]
        exact le_abs_self _
      have h3 : |((τ : ℂ) - z).im| ≤ ‖(τ : ℂ) - z‖ := Complex.abs_im_le_norm _
      have h4 : ‖(τ : ℂ) - z‖ = dist z (τ : ℂ) := by
        rw [dist_eq_norm, norm_sub_rev]
      have h5 : (τ : ℂ).im = 2 * ρ := by
        rw [hρdef]; ring
      linarith
    exact (Work.LayerCont.differentiableAt_Aexp_ofComplex ℓ d hd u ⟨z, hzpos⟩).mul_const _
  have hmeas : ∀ᶠ z in nhds (τ : ℂ), AEStronglyMeasurable
      (fun u : ℝ => Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d)
        (UpperHalfPlane.ofComplex z) u * Work.Asymptotics.gaussWeight r u)
      (volume.restrict (Set.Ioo (min (1 : ℝ) p) (max (1 : ℝ) p))) :=
    Filter.Eventually.of_forall (fun z =>
      ((continuous_Aexp_snd ℓ d hd (UpperHalfPlane.ofComplex z)).mul
        (by unfold Work.Asymptotics.gaussWeight; fun_prop)).aestronglyMeasurable)
  exact differentiableAt_intervalIntegral (a := (1 : ℝ)) (b := p) (z₀ := (τ : ℂ))
    (ρ := ρ) (C := C) hρ hbound hdiff hmeas

theorem mdifferentiableOn_highPartAt (ℓ : Work.Kernels.LogLambdaData) (d : ℕ)
    (hd : d = 8 ∨ d = 24) (p r : ℝ) :
    MDifferentiableOn (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ)
      (fun τ : UpperHalfPlane =>
        Work.LayerCont.highPartAt (Work.Asymptotics.Gcusp ℓ d) p r τ) Set.univ := by
  have hhigh : MDifferentiableOn (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ)
      (fun τ : UpperHalfPlane => Work.Asymptotics.highPart (Work.Asymptotics.Gcusp ℓ d) τ r)
      Set.univ := (mdifferentiable_highPart ℓ d hd r).mdifferentiableOn
  have hintegral : MDifferentiableOn (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ)
      (fun τ : UpperHalfPlane => ∫ t in (1 : ℝ)..p,
        Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) τ t
          * Work.Asymptotics.gaussWeight r t) Set.univ :=
    (mdifferentiable_Aexp_intervalIntegral ℓ d hd p r).mdifferentiableOn
  have hmain : MDifferentiableOn (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ)
      (fun τ : UpperHalfPlane => Work.Asymptotics.highPart (Work.Asymptotics.Gcusp ℓ d) τ r
        - Work.Asymptotics.sinSqC r • (fun τ' : UpperHalfPlane => ∫ t in (1 : ℝ)..p,
            Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) τ' t
              * Work.Asymptotics.gaussWeight r t) τ) Set.univ :=
    hhigh.sub (hintegral.const_smul (Work.Asymptotics.sinSqC r))
  have hEq : (fun τ : UpperHalfPlane =>
        Work.LayerCont.highPartAt (Work.Asymptotics.Gcusp ℓ d) p r τ)
      = fun τ : UpperHalfPlane => Work.Asymptotics.highPart (Work.Asymptotics.Gcusp ℓ d) τ r
        - Work.Asymptotics.sinSqC r • (fun τ' : UpperHalfPlane => ∫ t in (1 : ℝ)..p,
            Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) τ' t
              * Work.Asymptotics.gaussWeight r t) τ := by
    funext τ
    simp only [Work.LayerCont.highPartAt, smul_eq_mul]
  rw [hEq]
  exact hmain

end Work.LayerCont
