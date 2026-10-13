/-
Copyright: work module for the Elgindi finite-time singularity project.

# The ODE satisfied by the angular moment `Ψ_*` of a solution of (PolarBSL)

Elgindi, Annals 194 (3) 2021, §'Elliptic Regularity Estimates'.  Integrating the elliptic
equation

  `L(Ψ) = -α²z² ∂_zzΨ - α(5+α)z ∂_zΨ - ∂_θθΨ + ∂_θ(tan θ · Ψ) - 6Ψ = F`

against the angular weight `φ(θ) = sin θ cos²θ` (the weight of the solvability condition,
which lies in the kernel of the adjoint of the `α = 0` part, `Lzero_orthogonal`) gives the
ordinary differential equation

  `α²z² Ψ_*''(z) + α(5+α)z Ψ_*'(z) = -F_*(z)`

for the angular moment `Ψ_*(z) = ∫_0^{π/2} Ψ(z,θ) sinθcos²θ dθ`.  This is the equation
used to build the singular part `G` of §'The singular term' (`Gsing_ode`).

The proof has three ingredients:
* the `θ`-integration by parts `∫_0^{π/2} L₀(Ψ)(z,θ) φ(θ) dθ = 0` (`Lzero_orthogonal`);
* differentiation under the integral sign in `z` (`hasDerivAt_integral_Iθ` below), giving
  `Ψ_*'(z) = ∫ ∂_z Ψ(z,θ) φ(θ) dθ` and `Ψ_*''(z) = ∫ ∂_zzΨ(z,θ) φ(θ) dθ`;
* the a.e. identity `F = bslOp α Ψ` on the interior of the quadrant (`Fstar_bslOp`).

Since `sinθcos²θ` vanishes at `θ = 0, π/2`, the integrability hypotheses needed to split
`∫ (c₁ f₁ + c₂ f₂ + f₃)` into its three pieces are available: the `z`-derivative pieces are
continuous on the compact angular interval (`integrableOn_slice_mul`), and the `θ`-piece,
whose integrand is singular at `θ = π/2`, is a.e. equal to the derivative of a `C¹` function
on the closed interval (`integrableOn_Lzero_mul_sinCos2`).
-/
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Order.CompletePartialOrder
import Submission.Work.Elliptic.Defs
import Submission.Work.Spaces.Defs
import Submission.Work.Spaces.CurrySmooth
import Submission.Work.Spaces.HardyZ
import Submission.Work.Elliptic.Lzero_orthogonal

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.Elliptic

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

/-! ## Elementary rewritings of the angular integral

The angular interval `Iθ` of `Work.Spaces` and the interval of integration `0..π/2` of
`intervalIntegral` give the same integral, since they differ by the point `0`. -/

lemma Iθ_integral_eq_interval (f : ℝ → ℝ) :
    (∫ θ in Work.Spaces.Iθ, f θ) = ∫ θ in (0 : ℝ)..(π / 2), f θ := by
  rw [Work.Spaces.Iθ, MeasureTheory.integral_Icc_eq_integral_Ioc]
  exact (intervalIntegral.integral_of_le (by positivity : (0 : ℝ) ≤ π / 2)).symm

lemma Fstar_eq_interval (G : ℝ → ℝ → ℝ) (z : ℝ) :
    Fstar G z = ∫ θ in (0 : ℝ)..(π / 2), G z θ * sinCos2 θ := by
  rw [Fstar, Iθ_integral_eq_interval]

/-! ## Slices of a smooth function -/

/-- The `θ`-slice of a function smooth on a neighbourhood of the closed quadrant is smooth
on the whole angular interval. -/
lemma contDiffOn_slice_of_smoothNbhd (g : ℝ → ℝ → ℝ) (hg : Work.Spaces.SmoothNbhd g)
    {z : ℝ} (hz : -1 < z) : ContDiffOn ℝ ⊤ (fun θ : ℝ => g z θ) (Set.Icc 0 (π / 2)) := by
  have hsub : Set.Icc (0 : ℝ) (π / 2) ⊆ Set.Ioo (-1) (π / 2 + 1) := by
    intro θ hθ
    exact ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩
  have hp : ContDiffOn ℝ ⊤ (fun θ : ℝ => (z, θ)) (Set.Icc 0 (π / 2)) :=
    contDiffOn_const.prodMk contDiffOn_id
  have hmap : Set.MapsTo (fun θ : ℝ => (z, θ)) (Set.Icc 0 (π / 2)) Work.Spaces.U :=
    fun θ hθ => ⟨hz, hsub hθ⟩
  have h := hg.comp hp hmap
  simpa [Function.comp_def, Function.uncurry] using h

/-- The slice of a `SmoothNbhd` function, multiplied by a function continuous on the angular
interval, is integrable there. -/
lemma integrableOn_slice_mul (g : ℝ → ℝ → ℝ) (hg : Work.Spaces.SmoothNbhd g) {z : ℝ}
    (hz : -1 < z) (φ : ℝ → ℝ) (hφ : ContinuousOn φ (Set.Icc 0 (π / 2))) :
    IntegrableOn (fun θ => g z θ * φ θ) Work.Spaces.Iθ := by
  have h : IntegrableOn (fun θ => g z θ * φ θ) (Set.Icc 0 (π / 2)) :=
    ContinuousOn.integrableOn_compact (μ := volume) isCompact_Icc
      ((contDiffOn_slice_of_smoothNbhd g hg hz).continuousOn.mul hφ)
  simpa [Work.Spaces.Iθ] using h

/-! ## Differentiation under the integral sign in the radial variable -/

/-- **Differentiation under the integral sign in `z`** (interval-integral form): if `g` is
smooth on a neighbourhood of the closed quadrant and `φ` is continuous on `[0,π/2]`, then
`z' ↦ ∫_0^{π/2} g(z',θ) φ(θ) dθ` has derivative `∫_0^{π/2} ∂_z g(z,θ) φ(θ) dθ` at every
`z ∈ (-1,∞)`.

The domination hypothesis of Mathlib's parametric-integral theorem is supplied by the
uniform bound on `∂_z g` over the compact box `closure s × [0,π/2]`, where `s` is a bounded
neighbourhood of `z`; since `∂_z g` is continuous on the closed quadrant, this box is
contained in the open set on which `g` is smooth. -/
lemma hasDerivAt_integral_interval (g : ℝ → ℝ → ℝ) (φ : ℝ → ℝ)
    (hg : Work.Spaces.SmoothNbhd g) (hφ : ContinuousOn φ (Set.Icc 0 (π / 2))) {z : ℝ}
    (hz : -1 < z) :
    HasDerivAt (fun z' => ∫ θ in (0 : ℝ)..(π / 2), g z' θ * φ θ)
      (∫ θ in (0 : ℝ)..(π / 2), Work.Spaces.pz g z θ * φ θ) z := by
  have hle : (0 : ℝ) ≤ π / 2 := by positivity
  have hsm_pz : Work.Spaces.SmoothNbhd (Work.Spaces.pz g) :=
    Work.Spaces.contDiffOn_uncurry_pz Work.Spaces.isOpen_U hg
  -- a bounded neighbourhood `s` of `z`, contained in `(-1,∞)`
  set s : Set ℝ := Set.Ioo ((z - 1) / 2) (z + 1) with hs
  have hs_nhds : s ∈ 𝓝 z := Ioo_mem_nhds (by linarith) (by linarith)
  have hsz : s ⊆ Set.Ioi (-1) := fun x hx => by
    simp only [Set.mem_Ioi]; linarith [hx.1]
  have hsub_u : Set.uIoc (0 : ℝ) (π / 2) ⊆ Set.Icc 0 (π / 2) := by
    intro t ht
    rw [Set.uIoc_of_le hle] at ht
    exact ⟨le_of_lt ht.1, ht.2⟩
  -- the box `closure s × [0,π/2]` is compact and lies in the smoothness set
  have hcl : closure s = Set.Icc ((z - 1) / 2) (z + 1) := by
    rw [hs]; exact closure_Ioo (by linarith)
  have hboxU : closure s ×ˢ Set.Icc (0 : ℝ) (π / 2) ⊆ Work.Spaces.U := by
    rw [hcl]
    rintro ⟨x, t⟩ ⟨hx, ht⟩
    exact ⟨by simp only [Set.mem_Ioi]; linarith [hx.1],
      ⟨by linarith [ht.1], by linarith [ht.2, Real.pi_pos]⟩⟩
  have hcpt : IsCompact (closure s ×ˢ Set.Icc (0 : ℝ) (π / 2)) := by
    rw [hcl]
    exact isCompact_Icc.prod isCompact_Icc
  obtain ⟨C, hC⟩ := hcpt.exists_bound_of_continuousOn
    (((Work.Spaces.contDiffOn_uncurry_pz Work.Spaces.isOpen_U hg).continuousOn).mono hboxU)
  have hC' : ∀ x ∈ s, ∀ t ∈ Set.uIoc (0 : ℝ) (π / 2), ‖Work.Spaces.pz g x t‖ ≤ C :=
    fun x hx t ht => hC (x, t) ⟨subset_closure hx, hsub_u ht⟩
  have hF_meas : ∀ᶠ x in 𝓝 z, AEStronglyMeasurable (fun t : ℝ => g x t * φ t)
      (volume.restrict (Set.uIoc (0 : ℝ) (π / 2))) := by
    filter_upwards [hs_nhds] with x hx
    exact (((contDiffOn_slice_of_smoothNbhd g hg (hsz hx)).continuousOn.mul hφ).mono
      hsub_u).aestronglyMeasurable measurableSet_uIoc
  have hF_int : IntervalIntegrable (fun t : ℝ => g z t * φ t) volume (0 : ℝ) (π / 2) :=
    ((contDiffOn_slice_of_smoothNbhd g hg hz).continuousOn.mul hφ).intervalIntegrable_of_Icc hle
  have hF'_meas : AEStronglyMeasurable (fun t : ℝ => Work.Spaces.pz g z t * φ t)
      (volume.restrict (Set.uIoc (0 : ℝ) (π / 2))) :=
    (((contDiffOn_slice_of_smoothNbhd (Work.Spaces.pz g) hsm_pz hz).continuousOn.mul hφ).mono
      hsub_u).aestronglyMeasurable measurableSet_uIoc
  have h_bound : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ Set.uIoc (0 : ℝ) (π / 2) →
      ∀ x ∈ s, ‖Work.Spaces.pz g x t * φ t‖ ≤ C * ‖φ t‖ := by
    filter_upwards with t ht x hx
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (hC' x hx t ht) (norm_nonneg _)
  have hbound_int : IntervalIntegrable (fun t : ℝ => C * ‖φ t‖) volume (0 : ℝ) (π / 2) :=
    ((hφ.intervalIntegrable_of_Icc hle).norm).const_mul C
  have h_diff : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ Set.uIoc (0 : ℝ) (π / 2) →
      ∀ x ∈ s, HasDerivAt (fun x' : ℝ => g x' t * φ t) (Work.Spaces.pz g x t * φ t) x := by
    filter_upwards with t ht x hx
    exact (Work.Spaces.hardyZ_hasDerivAt_slice g hg (hsub_u ht) (hsz hx)).mul_const (φ t)
  exact (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume) (a := (0 : ℝ)) (b := π / 2) (bound := fun t => C * ‖φ t‖)
    (F := fun x t => g x t * φ t) (F' := fun x t => Work.Spaces.pz g x t * φ t)
    hs_nhds hF_meas hF_int hF'_meas h_bound hbound_int h_diff).2

/-- **Differentiation under the integral sign in `z`**, in the form of the integral over the
angular interval `Iθ`. -/
lemma hasDerivAt_integral_Iθ (g : ℝ → ℝ → ℝ) (φ : ℝ → ℝ)
    (hg : Work.Spaces.SmoothNbhd g) (hφ : ContinuousOn φ (Set.Icc 0 (π / 2))) {z : ℝ}
    (hz : -1 < z) :
    HasDerivAt (fun z' => ∫ θ in Work.Spaces.Iθ, g z' θ * φ θ)
      (∫ θ in Work.Spaces.Iθ, Work.Spaces.pz g z θ * φ θ) z := by
  have h := hasDerivAt_integral_interval g φ hg hφ hz
  have hfun : (fun z' => ∫ θ in Work.Spaces.Iθ, g z' θ * φ θ)
      = (fun z' => ∫ θ in (0 : ℝ)..(π / 2), g z' θ * φ θ) :=
    funext fun z' => Iθ_integral_eq_interval (fun θ => g z' θ * φ θ)
  rw [hfun, Iθ_integral_eq_interval (fun θ => Work.Spaces.pz g z θ * φ θ)]
  exact h

/-! ## The right hand side `F` in terms of the solution -/

/-- The angular moment of `F = bslOp α Ψ` is the θ-integral of `bslOp α Ψ` against the
weight `sinθcos²θ`.  Since `sinθcos²θ` vanishes at the endpoints, the a.e. identity
`bslOp α Ψ = F` on the open quadrant gives a pointwise identity on the whole closed
interval. -/
lemma Fstar_bslOp (α : ℝ) (F Ψ : ℝ → ℝ → ℝ) (z : ℝ) (hz : 0 < z)
    (hsol : IsBslSol α F Ψ) :
    Fstar F z = ∫ θ in Work.Spaces.Iθ, bslOp α Ψ z θ * sinCos2 θ := by
  obtain ⟨hEq, -, -, -⟩ := hsol
  rw [Fstar]
  refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc fun θ hθ => ?_
  rcases eq_or_ne θ 0 with rfl | h0
  · simp [sinCos2]
  · rcases eq_or_ne θ (π / 2) with rfl | h1
    · simp [sinCos2, Real.cos_pi_div_two]
    · rw [hEq z hz θ (lt_of_le_of_ne hθ.1 (Ne.symm h0)) (lt_of_le_of_ne hθ.2 h1)]

/-! ## Integrability of the `θ`-piece -/

/-- The integrand `L₀(Ψ)(z,·) · sinθcos²θ`, which is singular at `θ = π/2`, is integrable on
the angular interval.  On the closed interval it agrees, except at the two endpoints, with
the derivative of the `C¹` function

  `H(θ) = -Ψ_θ(z,θ) sinθcos²θ + Ψ(z,θ) cosθ cos 2θ`,

whose `θ`-derivative is exactly `L₀(Ψ)(z,θ)·sinθcos²θ` (see `hasDerivAt_Lzero_antideriv`). -/
lemma integrableOn_Lzero_mul_sinCos2 (Ψ : ℝ → ℝ → ℝ) (z : ℝ)
    (hsm : ContDiffOn ℝ 2 (fun θ : ℝ => Ψ z θ) (Set.Icc 0 (π / 2))) :
    IntegrableOn (fun θ => Lzero Ψ z θ * sinCos2 θ) Work.Spaces.Iθ := by
  have hle : (0 : ℝ) ≤ π / 2 := by positivity
  have hlt : (0 : ℝ) < π / 2 := by positivity
  set f : ℝ → ℝ := fun θ => Ψ z θ with hf
  set H : ℝ → ℝ := fun θ => -(derivWithin f (Set.Icc 0 (π / 2)) θ) * sinCos2 θ
      + f θ * (Real.cos θ * Real.cos (2 * θ)) with hHdef
  have hsm_f : ContDiffOn ℝ 2 f (Set.Icc 0 (π / 2)) := by rw [hf]; exact hsm
  have hu : UniqueDiffOn ℝ (Set.Icc (0 : ℝ) (π / 2)) := uniqueDiffOn_Icc hlt
  have hHcd : ContDiffOn ℝ 1 H (Set.Icc 0 (π / 2)) := by
    rw [hHdef]
    have hdw : ContDiffOn ℝ 1 (derivWithin f (Set.Icc 0 (π / 2))) (Set.Icc 0 (π / 2)) :=
      hsm_f.derivWithin hu (by norm_num)
    have hsm1 : ContDiffOn ℝ 1 f (Set.Icc 0 (π / 2)) := hsm_f.of_le (by norm_num)
    have hsincos : ContDiffOn ℝ 1 sinCos2 (Set.Icc 0 (π / 2)) := by unfold sinCos2; fun_prop
    have hcc : ContDiffOn ℝ 1 (fun θ : ℝ => Real.cos θ * Real.cos (2 * θ))
        (Set.Icc 0 (π / 2)) := by fun_prop
    exact (hdw.neg.mul hsincos).add (hsm1.mul hcc)
  have hcont : ContinuousOn (derivWithin H (Set.Icc 0 (π / 2))) (Set.Icc 0 (π / 2)) :=
    hHcd.continuousOn_derivWithin hu le_rfl
  have hint : IntegrableOn (derivWithin H (Set.Icc 0 (π / 2))) Work.Spaces.Iθ :=
    ContinuousOn.integrableOn_compact isCompact_Icc hcont
  refine hint.congr ?_
  rw [Filter.EventuallyEq]
  show ∀ᵐ θ ∂(volume.restrict (Set.Icc 0 (π / 2))),
      derivWithin H (Set.Icc 0 (π / 2)) θ = Lzero Ψ z θ * sinCos2 θ
  rw [MeasureTheory.ae_restrict_iff' measurableSet_Icc]
  -- the two endpoints are the only exceptions
  have h1 : ∀ᵐ θ ∂(volume : Measure ℝ), θ ∉ ({0} : Set ℝ) := by
    rw [MeasureTheory.ae_iff]; simp
  have h2 : ∀ᵐ θ ∂(volume : Measure ℝ), θ ∉ ({π / 2} : Set ℝ) := by
    rw [MeasureTheory.ae_iff]; simp
  filter_upwards [h1, h2] with θ hθ1 hθ2 hθmem
  have hpoint : derivWithin H (Set.Icc 0 (π / 2)) θ = Lzero Ψ z θ * sinCos2 θ := by
    have h2' : ContDiffAt ℝ 2 (fun θ : ℝ => Ψ z θ) θ :=
      hsm.contDiffAt (Icc_mem_nhds (lt_of_le_of_ne hθmem.1 (Ne.symm hθ1))
        (lt_of_le_of_ne hθmem.2 hθ2))
    have hHF : H =ᶠ[𝓝 θ] (fun θ' : ℝ => -(deriv (fun θ'' : ℝ => Ψ z θ'') θ') * sinCos2 θ'
        + Ψ z θ' * (Real.cos θ' * Real.cos (2 * θ'))) := by
      filter_upwards [Ioo_mem_nhds (lt_of_le_of_ne hθmem.1 (Ne.symm hθ1))
        (lt_of_le_of_ne hθmem.2 hθ2)] with y hy
      simp only [hHdef, hf, derivWithin_of_mem_nhds
        (Icc_mem_nhds hy.1 hy.2)]
    exact (derivWithin_of_mem_nhds (Icc_mem_nhds (lt_of_le_of_ne hθmem.1 (Ne.symm hθ1))
      (lt_of_le_of_ne hθmem.2 hθ2))).trans
      ((hasDerivAt_Lzero_antideriv Ψ z θ
        ⟨lt_of_le_of_ne hθmem.1 (Ne.symm hθ1), lt_of_le_of_ne hθmem.2 hθ2⟩ h2').congr_of_eventuallyEq
        hHF).deriv
  exact hpoint


/-! ## The ODE for the angular moment -/

theorem PsiStar_ode (α : ℝ) (F Ψ : ℝ → ℝ → ℝ) (z : ℝ) (hα : 0 < α) (hz : 0 < z)
    (hsm : Work.Spaces.SmoothNbhd Ψ) (hsol : Work.Elliptic.IsBslSol α F Ψ) :
    α ^ 2 * z ^ 2 * deriv (fun z' => deriv (fun z'' => Work.Elliptic.Fstar Ψ z'') z') z
        + α * (5 + α) * z * deriv (fun z' => Work.Elliptic.Fstar Ψ z') z
      = - Work.Elliptic.Fstar F z := by
  have hsol0 : ∀ z' : ℝ, Ψ z' 0 = 0 := hsol.2.1
  have hsolpi : ∀ z' : ℝ, Ψ z' (π / 2) = 0 := hsol.2.2.1
  have hz1 : (-1 : ℝ) < z := by linarith
  have hφ : ContinuousOn sinCos2 (Set.Icc 0 (π / 2)) := by unfold sinCos2; fun_prop
  have hslice : ContDiffOn ℝ 2 (fun θ : ℝ => Ψ z θ) (Set.Icc 0 (π / 2)) :=
    (contDiffOn_slice_of_smoothNbhd Ψ hsm hz1).of_le (by norm_num)
  have hsm_pz : Work.Spaces.SmoothNbhd (Work.Spaces.pz Ψ) :=
    Work.Spaces.contDiffOn_uncurry_pz Work.Spaces.isOpen_U hsm
  have hsm_pz2 : Work.Spaces.SmoothNbhd (Work.Spaces.pz (Work.Spaces.pz Ψ)) :=
    Work.Spaces.contDiffOn_uncurry_pz Work.Spaces.isOpen_U hsm_pz
  -- the two radial derivatives of the angular moment
  have hΦ1 : deriv (fun z' => Fstar Ψ z') z
      = ∫ θ in Work.Spaces.Iθ, Work.Spaces.pz Ψ z θ * sinCos2 θ :=
    (hasDerivAt_integral_Iθ Ψ sinCos2 hsm hφ hz1).deriv
  have hΦ2 : deriv (fun z' => deriv (fun z'' => Fstar Ψ z'') z') z
      = ∫ θ in Work.Spaces.Iθ, Work.Spaces.pzIter 2 Ψ z θ * sinCos2 θ := by
    show deriv (deriv (fun z'' => ∫ θ in Work.Spaces.Iθ, Ψ z'' θ * sinCos2 θ)) z = _
    have hns : (deriv (fun z'' => ∫ θ in Work.Spaces.Iθ, Ψ z'' θ * sinCos2 θ))
        =ᶠ[𝓝 z] (fun y => ∫ θ in Work.Spaces.Iθ, Work.Spaces.pz Ψ y θ * sinCos2 θ) := by
      filter_upwards [Ioi_mem_nhds hz1] with y hy
      exact (hasDerivAt_integral_Iθ Ψ sinCos2 hsm hφ hy).deriv
    rw [Filter.EventuallyEq.deriv_eq hns]
    exact (hasDerivAt_integral_Iθ (Work.Spaces.pz Ψ) sinCos2 hsm_pz hφ hz1).deriv
  -- integrability of the three pieces of the right hand side
  have hI1 : IntegrableOn (fun θ => Work.Spaces.pzIter 2 Ψ z θ * sinCos2 θ) Work.Spaces.Iθ :=
    integrableOn_slice_mul (Work.Spaces.pz (Work.Spaces.pz Ψ)) hsm_pz2 hz1 sinCos2 hφ
  have hI2 : IntegrableOn (fun θ => Work.Spaces.pz Ψ z θ * sinCos2 θ) Work.Spaces.Iθ :=
    integrableOn_slice_mul (Work.Spaces.pz Ψ) hsm_pz hz1 sinCos2 hφ
  have hI3 : IntegrableOn (fun θ => Lzero Ψ z θ * sinCos2 θ) Work.Spaces.Iθ :=
    integrableOn_Lzero_mul_sinCos2 Ψ z hslice
  have hL : (∫ θ in Work.Spaces.Iθ, Lzero Ψ z θ * sinCos2 θ) = 0 :=
    Lzero_orthogonal Ψ z hslice (hsol0 z) (hsolpi z)
  -- the main identity: `F`-moment in terms of the two radial derivatives
  have hmain : Fstar F z
      = -(α ^ 2 * z ^ 2) * (∫ θ in Work.Spaces.Iθ, Work.Spaces.pzIter 2 Ψ z θ * sinCos2 θ)
        - (α * (5 + α) * z) * (∫ θ in Work.Spaces.Iθ, Work.Spaces.pz Ψ z θ * sinCos2 θ)
        + ∫ θ in Work.Spaces.Iθ, Lzero Ψ z θ * sinCos2 θ := by
    rw [Fstar_bslOp α F Ψ z hz hsol]
    have hcongr : (fun θ => bslOp α Ψ z θ * sinCos2 θ)
        = (fun θ => ((-(α ^ 2 * z ^ 2)) * (Work.Spaces.pzIter 2 Ψ z θ * sinCos2 θ)
            + (-(α * (5 + α) * z)) * (Work.Spaces.pz Ψ z θ * sinCos2 θ))
            + Lzero Ψ z θ * sinCos2 θ) := by
      funext θ
      rw [bslOp_apply]
      ring
    rw [hcongr]
    have e1 : (∫ θ in Work.Spaces.Iθ, ((-(α ^ 2 * z ^ 2)) * (Work.Spaces.pzIter 2 Ψ z θ * sinCos2 θ)
            + (-(α * (5 + α) * z)) * (Work.Spaces.pz Ψ z θ * sinCos2 θ))
            + Lzero Ψ z θ * sinCos2 θ)
        = (∫ θ in Work.Spaces.Iθ, (-(α ^ 2 * z ^ 2)) * (Work.Spaces.pzIter 2 Ψ z θ * sinCos2 θ)
            + (-(α * (5 + α) * z)) * (Work.Spaces.pz Ψ z θ * sinCos2 θ))
          + ∫ θ in Work.Spaces.Iθ, Lzero Ψ z θ * sinCos2 θ :=
      MeasureTheory.integral_add
        ((hI1.const_mul (-(α ^ 2 * z ^ 2))).add (hI2.const_mul (-(α * (5 + α) * z)))) hI3
    have e2 : (∫ θ in Work.Spaces.Iθ, (-(α ^ 2 * z ^ 2)) * (Work.Spaces.pzIter 2 Ψ z θ * sinCos2 θ)
            + (-(α * (5 + α) * z)) * (Work.Spaces.pz Ψ z θ * sinCos2 θ))
        = (∫ θ in Work.Spaces.Iθ, (-(α ^ 2 * z ^ 2)) * (Work.Spaces.pzIter 2 Ψ z θ * sinCos2 θ))
          + ∫ θ in Work.Spaces.Iθ, (-(α * (5 + α) * z)) * (Work.Spaces.pz Ψ z θ * sinCos2 θ) :=
      MeasureTheory.integral_add (hI1.const_mul (-(α ^ 2 * z ^ 2)))
        (hI2.const_mul (-(α * (5 + α) * z)))
    have e3 : (∫ θ in Work.Spaces.Iθ, (-(α ^ 2 * z ^ 2)) * (Work.Spaces.pzIter 2 Ψ z θ * sinCos2 θ))
        = (-(α ^ 2 * z ^ 2)) * (∫ θ in Work.Spaces.Iθ, Work.Spaces.pzIter 2 Ψ z θ * sinCos2 θ) :=
      MeasureTheory.integral_const_mul (-(α ^ 2 * z ^ 2))
        (fun θ => Work.Spaces.pzIter 2 Ψ z θ * sinCos2 θ)
    have e4 : (∫ θ in Work.Spaces.Iθ, (-(α * (5 + α) * z)) * (Work.Spaces.pz Ψ z θ * sinCos2 θ))
        = (-(α * (5 + α) * z)) * (∫ θ in Work.Spaces.Iθ, Work.Spaces.pz Ψ z θ * sinCos2 θ) :=
      MeasureTheory.integral_const_mul (-(α * (5 + α) * z))
        (fun θ => Work.Spaces.pz Ψ z θ * sinCos2 θ)
    rw [e1, e2, e3, e4]
    ring
  rw [hΦ2, hΦ1]
  rw [hL] at hmain
  linarith [hmain]

end Work.Elliptic
