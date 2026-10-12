import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.BSKinetic.bsW_fsKinCoeff_le
import Submission.Work.BoseFixB1.Defs
import Submission.Work.BoseFixB1S.corrMarg.support_u
import Submission.Work.OneBodyKin.MeasurableBSOneBody
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `u`-integrability of the cut kinetic word `u ↦ bsW (fsKinCoeff c) (χ_{B(u)}·(g − ρ u))`

The sliding window `χ_{B(u)}(z) = chiB ℓ d u z = χ(z/ℓ)·χ(z/(ℓd) − u)` cut against a
smooth profile `g` and a measurable, uniformly bounded shift `ρ u`.  The three ingredients of
the proof are

* **a.e. strong measurability** of `u ↦ bsW (fsKinCoeff c) (·)`.  `bsW` and `bsPsi` are
  parametric Bochner integrals over all of `ℝ³` (`kinFT`), with no integrability hypothesis on
  the integrand, so the right tool is
  `MeasureTheory.StronglyMeasurable.integral_prod_right'` (which is unconditional and
  compatible with the total/zero-on-non-integrable Bochner integral); applied twice — once for
  the position variable of `kinFT`, once for the momentum variable of `bsW`.
* **a uniform bound in `u`** of `bsW (fsKinCoeff c) h_u`.  The state `h_u` is supported in the
  *fixed* box `acube ℓ`, and on that box both `h_u` and its coordinate derivatives are bounded
  uniformly in `u` (the window is `chiSup²`-bounded and its gradient is bounded by
  `√K/s`, `Work.BlockBound4.chiScale_grad_bound`); `Work.BSKinetic.bsW_fsKinCoeff_le` then
  turns this into a uniform constant bound.
* **the `u`-support**: `χ_{B(u)}` vanishes identically as soon as `u` leaves the fixed cube
  `acube ((1+d)/d)` (`Work.BoseFixB1S.chiB_mul_eq_zero_of_not_mem_acube_u`), a set of finite
  Lebesgue measure.  `MeasureTheory.Integrable.mono'` against its indicator finishes.

Everything is proved from scratch here (no use of the `sorry`-carrying
`Work.BoseFixB1S.corrMarg.integrable_bsW_chiB_sub`).
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped Topology Real BigOperators

namespace Work.BoseFixB1S.corr

/-- Shorthand for the configuration space `ℝ³ = EuclideanSpace ℝ (Fin 3)`.  Used only for the
auxiliary lemmas and proofs; the target statement is spelled out in full. -/
abbrev E3 := EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false
set_option maxHeartbeats 800000

/-! ## 1. A.e. strong measurability -/

/-- **General parametric-integral tool.**  If the symbol `F : ℝ → ℝ` is continuous and the
state kernel `H : ℝ³ × ℝ³ → ℝ` is jointly strongly measurable, then
`u ↦ bsW F (fun z => H (u,z))` is a.e. strongly measurable for Lebesgue measure.

`bsW F h = ∫_p F‖p‖·‖bsPsi h p‖²` with `bsPsi h p = ∫_y e^{−i⟪p,y⟫}·h y dy`, a *double*
parametric Bochner integral over all of `ℝ³` with no integrability hypothesis, so this is the
two-fold application of `MeasureTheory.StronglyMeasurable.integral_prod_right'`. -/
private lemma aestronglyMeasurable_bsW_of_joint {F : ℝ → ℝ} (hF : Continuous F)
    {H : E3 × E3 → ℝ} (hH : StronglyMeasurable H) :
    AEStronglyMeasurable
      (fun u : E3 => Work.BSKinetic.Decomp.bsW F (fun z : E3 => H (u, z)))
      (volume : Measure E3) := by
  -- The phase factor is continuous, hence strongly measurable.
  have hexp : StronglyMeasurable (fun s : (E3 × E3) × E3 =>
      Complex.exp (-(Complex.I * (inner ℝ s.1.2 s.2 : ℂ)))) :=
    (by fun_prop : Continuous (fun s : (E3 × E3) × E3 =>
      Complex.exp (-(Complex.I * (inner ℝ s.1.2 s.2 : ℂ))))).stronglyMeasurable
  -- The `y`-integrand of `kinFT`, jointly in `(u,p,y)`.
  have hstat : StronglyMeasurable (fun s : (E3 × E3) × E3 => Complex.ofReal (H (s.1.1, s.2))) :=
    Complex.continuous_ofReal.comp_stronglyMeasurable
      (hH.comp_measurable (by fun_prop : Measurable fun s : (E3 × E3) × E3 => (s.1.1, s.2)))
  -- Integrate out the position `y`: this is `(u,p) ↦ bsPsi (H u) p`.
  have hK : StronglyMeasurable (fun q : E3 × E3 =>
      ∫ y : E3, Complex.exp (-(Complex.I * (inner ℝ q.2 y : ℂ))) * Complex.ofReal (H (q.1, y))) :=
    (hexp.mul hstat).integral_prod_right' (ν := (volume : Measure E3))
  -- Multiply by `F‖p‖` and take the squared norm.
  have hGp : StronglyMeasurable (fun q : E3 × E3 =>
      F ‖q.2‖ * ‖(∫ y : E3, Complex.exp (-(Complex.I * (inner ℝ q.2 y : ℂ))) *
        Complex.ofReal (H (q.1, y)))‖ ^ 2) :=
    ((hF.comp (continuous_norm.comp continuous_snd)).stronglyMeasurable).mul (hK.norm.pow 2)
  -- Integrate out the momentum `p`.
  have hFin : StronglyMeasurable (fun u : E3 =>
      ∫ p : E3, F ‖p‖ * ‖(∫ y : E3, Complex.exp (-(Complex.I * (inner ℝ p y : ℂ))) *
        Complex.ofReal (H (u, y)))‖ ^ 2) :=
    hGp.integral_prod_right' (ν := (volume : Measure E3))
  -- Identify with `bsW` and weaken to a.e. strong measurability.
  refine hFin.aestronglyMeasurable.congr ?_
  filter_upwards with u
  simp only [Work.BSKinetic.Decomp.bsW, Work.BSKinetic.Decomp.bsPsi, Submission.BoseGases.kinFT]

/-- The spectral symbol `r ↦ [r−c]₊²` is continuous. -/
private lemma continuous_fsKinCoeff (c : ℝ) : Continuous (Submission.BoseGases.fsKinCoeff c) := by
  have h : Submission.BoseGases.fsKinCoeff c = fun r : ℝ => (max (r - c) 0) ^ 2 := rfl
  rw [h]
  exact ((continuous_id.sub continuous_const).max continuous_const).pow 2

/-- **A.e. strong measurability of the cut kinetic word.** -/
private lemma aemeasurable_bsW_cut {ℓ d c : ℝ} {g ρ : E3 → ℝ}
    (hg : Continuous g) (hρ : Measurable ρ) :
    AEStronglyMeasurable
      (fun u : E3 => Work.BSKinetic.Decomp.bsW (Submission.BoseGases.fsKinCoeff c)
        (fun z : E3 => Submission.BoseGases.chiB ℓ d u z * (g z - ρ u)))
      (volume : Measure E3) := by
  refine aestronglyMeasurable_bsW_of_joint (F := Submission.BoseGases.fsKinCoeff c)
    (H := fun q : E3 × E3 =>
      Submission.BoseGases.chiB ℓ d q.1 q.2 * (g q.2 - ρ q.1))
    (continuous_fsKinCoeff c) ?_
  -- The window `(u,z) ↦ chiB ℓ d u z` is jointly continuous, hence jointly measurable.
  have hchi1 : Continuous (fun q : E3 × E3 => Submission.BoseGases.chiScale ℓ q.2) :=
    (Submission.BoseGases.chiScale_continuous ℓ).comp continuous_snd
  have hchi2 : Continuous (fun q : E3 × E3 =>
      Submission.BoseGases.chiScale (ℓ * d) (q.2 - (ℓ * d) • q.1)) :=
    (Submission.BoseGases.chiScale_continuous (ℓ * d)).comp (by fun_prop)
  have hchiBm : Measurable (fun q : E3 × E3 => Submission.BoseGases.chiB ℓ d q.1 q.2) := by
    show Measurable (fun q : E3 × E3 => Submission.BoseGases.chiScale ℓ q.2 *
      Submission.BoseGases.chiScale (ℓ * d) (q.2 - (ℓ * d) • q.1))
    exact (hchi1.mul hchi2).measurable
  -- The factor `(u,z) ↦ g z − ρ u` is jointly measurable.
  have hgr : Measurable (fun q : E3 × E3 => g q.2 - ρ q.1) :=
    (hg.measurable.comp measurable_snd).sub (hρ.comp measurable_fst)
  exact (hchiBm.mul hgr).stronglyMeasurable

/-! ## 2. The uniform-in-`u` bound -/

/-- The per-coordinate form of the uniform window-gradient bound
`Σ_k (∂_k chiScale s)² ≤ K/s²`: every coordinate partial derivative of the window is bounded
by `√K/s` (for `s > 0`). -/
private lemma abs_fderiv_chiScale_basis_le_sqrt {K : ℝ}
    (hKb : ∀ (s : ℝ), 0 < s → ∀ x : E3,
      ∑ k : Fin 3,
        (fderiv ℝ (Submission.BoseGases.chiScale s) x (Submission.BoseGases.kcStdBasis k)) ^ 2
        ≤ K / s ^ 2)
    {s : ℝ} (hs : 0 < s) (y : E3) (k : Fin 3) :
    |fderiv ℝ (Submission.BoseGases.chiScale s) y (Submission.BoseGases.kcStdBasis k)|
      ≤ Real.sqrt K / s := by
  have h1 : (fderiv ℝ (Submission.BoseGases.chiScale s) y
        (Submission.BoseGases.kcStdBasis k)) ^ 2 ≤ K / s ^ 2 :=
    le_trans (Finset.single_le_sum (s := Finset.univ)
      (f := fun j : Fin 3 =>
        (fderiv ℝ (Submission.BoseGases.chiScale s) y (Submission.BoseGases.kcStdBasis j)) ^ 2)
      (fun j _ => sq_nonneg _) (Finset.mem_univ k)) (hKb s hs y)
  have h2 : Real.sqrt ((fderiv ℝ (Submission.BoseGases.chiScale s) y
        (Submission.BoseGases.kcStdBasis k)) ^ 2) ≤ Real.sqrt (K / s ^ 2) :=
    Real.sqrt_le_sqrt h1
  rwa [Real.sqrt_sq_eq_abs, Real.sqrt_div' K (sq_nonneg s), Real.sqrt_sq (le_of_lt hs)] at h2

/-- **Uniform bound in `u` for the cut kinetic word.**  `bsW (fsKinCoeff c) h_u ≤ B` for a
constant `B` independent of `u ∈ acube ((1+d)/d)`, where
`h_u = fun z => chiB ℓ d u z * (g z − ρ u)`. -/
private lemma bsW_cut_bound {ℓ d c : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d)
    {g : E3 → ℝ} (hg : ContDiff ℝ (⊤ : ENat) g)
    {ρ : E3 → ℝ} (hρbd : ∃ C : ℝ, ∀ u : E3, |ρ u| ≤ C) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ u : E3,
      u ∈ Submission.BoseGases.acube ((1 + d) / d) →
      Work.BSKinetic.Decomp.bsW (Submission.BoseGases.fsKinCoeff c)
        (fun z : E3 => Submission.BoseGases.chiB ℓ d u z * (g z - ρ u)) ≤ B := by
  -- ## Bounds for `g`, `fderiv g`, `ρ` and the window gradient
  obtain ⟨S₀, hS₀⟩ :=
    (Submission.BoseGases.acube_compact hℓ).exists_bound_of_continuousOn
      hg.continuous.continuousOn
  obtain ⟨M₀, hM₀⟩ := (Submission.BoseGases.acube_compact hℓ).exists_bound_of_continuousOn
    ((hg.continuous_fderiv (by simp)).norm.continuousOn)
  obtain ⟨Cρ, hCρ⟩ := hρbd
  obtain ⟨K, _hK0, hKb⟩ := Work.BlockBound4.chiScale_grad_bound
  set S : ℝ := max S₀ 0 with hSdef
  set M : ℝ := max M₀ 0 with hMdef
  set Cp : ℝ := max Cρ 0 with hCpdef
  have hS0 : 0 ≤ S := le_max_right _ _
  have hM0 : 0 ≤ M := le_max_right _ _
  have hCp0 : 0 ≤ Cp := le_max_right _ _
  have hgb : ∀ z ∈ Submission.BoseGases.acube ℓ, |g z| ≤ S := fun z hz => by
    rw [← Real.norm_eq_abs]
    exact le_trans (hS₀ z hz) (le_max_left _ _)
  have hMb : ∀ z ∈ Submission.BoseGases.acube ℓ, ‖fderiv ℝ g z‖ ≤ M := fun z hz =>
    le_trans (by simpa using hM₀ z hz) (le_max_left _ _)
  have hρC : ∀ u : E3, |ρ u| ≤ Cp := fun u => le_trans (hCρ u) (le_max_left _ _)
  have hDil : ∀ (s : ℝ), 0 < s → ∀ (y : E3) (k : Fin 3),
      |fderiv ℝ (Submission.BoseGases.chiScale s) y (Submission.BoseGases.kcStdBasis k)|
        ≤ Real.sqrt K / s := fun s hs => abs_fderiv_chiScale_basis_le_sqrt hKb hs
  -- ## The constants of the estimate
  set Dχ : ℝ := Submission.BoseGases.chiSup * (Real.sqrt K / (ℓ * d))
    + Submission.BoseGases.chiSup * (Real.sqrt K / ℓ) with hDχdef
  have hDχ0 : 0 ≤ Dχ := by
    rw [hDχdef]
    exact add_nonneg
      (mul_nonneg (le_of_lt Submission.BoseGases.chiSup_pos)
        (div_nonneg (Real.sqrt_nonneg K) (by positivity)))
      (mul_nonneg (le_of_lt Submission.BoseGases.chiSup_pos)
        (div_nonneg (Real.sqrt_nonneg K) (by positivity)))
  set C₁ : ℝ := Submission.BoseGases.chiSup ^ 2 * (S + Cp) with hC₁def
  have hC₁0 : 0 ≤ C₁ := by
    rw [hC₁def]
    exact mul_nonneg (sq_nonneg _) (add_nonneg hS0 hCp0)
  set D : ℝ := Submission.BoseGases.chiSup ^ 2 * M + (S + Cp) * Dχ with hDdef
  have hD0 : 0 ≤ D := by
    rw [hDdef]
    exact add_nonneg (mul_nonneg (sq_nonneg _) hM0)
      (mul_nonneg (add_nonneg hS0 hCp0) hDχ0)
  refine ⟨(2 * Real.pi) ^ 3
    * (2 * c ^ 2 * (C₁ ^ 2 * ℓ ^ 3) + 2 * (3 * (D ^ 2 * ℓ ^ 3))), ?_, ?_⟩
  · exact mul_nonneg (by positivity) (add_nonneg (by positivity) (by positivity))
  -- ## The uniform-in-`u` estimate
  intro u _hu
  have hcont : ContDiff ℝ (⊤ : ENat)
      (fun z : E3 => Submission.BoseGases.chiB ℓ d u z * (g z - ρ u)) :=
    (Work.SmallBoxTBWord.contDiff_chiB hℓ hd u).mul (hg.sub contDiff_const)
  have hcs : HasCompactSupport (fun z : E3 => Submission.BoseGases.chiB ℓ d u z * (g z - ρ u)) :=
    (Work.SmallBoxTBWord.hasCompactSupport_chiB hℓ hd u).mul_right
  have hzero : ∀ z : E3, z ∉ Submission.BoseGases.acube ℓ →
      Submission.BoseGases.chiB ℓ d u z * (g z - ρ u) = 0 := by
    intro z hz
    have h1 : Submission.BoseGases.chiScale ℓ z = 0 := by
      by_contra hc
      exact hz (Submission.BoseGases.chiScale_mem_acube hℓ hc)
    simp only [Submission.BoseGases.chiB, h1, zero_mul]
  -- the sup-bound of the state
  have hb : ∀ z : E3, |Submission.BoseGases.chiB ℓ d u z * (g z - ρ u)| ≤ C₁ := by
    intro z
    by_cases hz : z ∈ Submission.BoseGases.acube ℓ
    · rw [abs_mul, hC₁def]
      refine mul_le_mul (Work.SmallBoxTBWord.abs_chiB_le_chiSup_sq u z) ?_
        (abs_nonneg _) (sq_nonneg _)
      exact le_trans (abs_sub _ _) (add_le_add (hgb z hz) (hρC u))
    · rw [hzero z hz, abs_zero, hC₁def]
      exact mul_nonneg (sq_nonneg _) (add_nonneg hS0 hCp0)
  -- the coordinate-derivative bound of the state
  have hb' : ∀ (k : Fin 3) (z : E3),
      |fderiv ℝ (fun y : E3 => Submission.BoseGases.chiB ℓ d u y * (g y - ρ u)) z
        (Submission.BoseGases.kcStdBasis k)| ≤ D := by
    intro k z
    by_cases hz : z ∈ Submission.BoseGases.acube ℓ
    · -- inside the box: Leibniz plus the uniform bounds
      have hχd : DifferentiableAt ℝ (fun y : E3 => Submission.BoseGases.chiB ℓ d u y) z :=
        ((Work.SmallBoxTBWord.contDiff_chiB hℓ hd u).contDiffAt).differentiableAt (by simp)
      have hWd : DifferentiableAt ℝ (fun y : E3 => g y - ρ u) z :=
        ((hg.sub contDiff_const).contDiffAt).differentiableAt (by simp)
      have hWderiv : fderiv ℝ (fun y : E3 => g y - ρ u) z = fderiv ℝ g z :=
        fderiv_sub_const (ρ u)
      have hχderiv : (fderiv ℝ (fun y : E3 => Submission.BoseGases.chiB ℓ d u y) z)
          (Submission.BoseGases.kcStdBasis k)
          = Submission.BoseGases.chiScale ℓ z
              * (fderiv ℝ (Submission.BoseGases.chiScale (ℓ * d)) (z - (ℓ * d) • u)
                  (Submission.BoseGases.kcStdBasis k))
            + Submission.BoseGases.chiScale (ℓ * d) (z - (ℓ * d) • u)
              * (fderiv ℝ (Submission.BoseGases.chiScale ℓ) z
                  (Submission.BoseGases.kcStdBasis k)) :=
        Work.UBBInputs9.C.fderiv_chiB_apply ℓ d (ne_of_gt hℓ) (ne_of_gt hd) u z
          (Submission.BoseGases.kcStdBasis k)
      have hleib : (fderiv ℝ
            (fun y : E3 => Submission.BoseGases.chiB ℓ d u y * (g y - ρ u)) z)
            (Submission.BoseGases.kcStdBasis k)
          = Submission.BoseGases.chiB ℓ d u z
              * (fderiv ℝ g z (Submission.BoseGases.kcStdBasis k))
            + (g z - ρ u) * (Submission.BoseGases.chiScale ℓ z
                * (fderiv ℝ (Submission.BoseGases.chiScale (ℓ * d)) (z - (ℓ * d) • u)
                    (Submission.BoseGases.kcStdBasis k))
              + Submission.BoseGases.chiScale (ℓ * d) (z - (ℓ * d) • u)
                * (fderiv ℝ (Submission.BoseGases.chiScale ℓ) z
                    (Submission.BoseGases.kcStdBasis k))) := by
        rw [show (fun y : E3 => Submission.BoseGases.chiB ℓ d u y * (g y - ρ u))
              = (fun y : E3 => Submission.BoseGases.chiB ℓ d u y)
                * (fun y : E3 => g y - ρ u) from rfl,
          fderiv_mul hχd hWd]
        simp only [Pi.mul_apply, add_apply, smul_apply, smul_eq_mul, hWderiv, hχderiv]
      rw [hleib, hDdef]
      refine le_trans (abs_add_le _ _) (add_le_add ?_ ?_)
      · -- the `∂g`-term
        rw [abs_mul]
        refine mul_le_mul (Work.SmallBoxTBWord.abs_chiB_le_chiSup_sq u z) ?_
          (abs_nonneg _) (sq_nonneg _)
        calc |fderiv ℝ g z (Submission.BoseGases.kcStdBasis k)|
            = ‖fderiv ℝ g z (Submission.BoseGases.kcStdBasis k)‖ := Real.norm_eq_abs _
          _ ≤ ‖fderiv ℝ g z‖ * ‖Submission.BoseGases.kcStdBasis k‖ :=
              ContinuousLinearMap.le_opNorm _ _
          _ = ‖fderiv ℝ g z‖ := by
              rw [show ‖Submission.BoseGases.kcStdBasis k‖ = 1 from by simp
                [Submission.BoseGases.kcStdBasis], mul_one]
          _ ≤ M := hMb z hz
      · -- the `(g − ρ u)·∂χ`-term
        rw [abs_mul]
        refine mul_le_mul
          (le_trans (abs_sub _ _) (add_le_add (hgb z hz) (hρC u))) ?_
          (abs_nonneg _) (add_nonneg hS0 hCp0)
        refine le_trans (abs_add_le _ _) ?_
        rw [hDχdef]
        exact add_le_add
          (by rw [abs_mul]
              exact mul_le_mul (Submission.BoseGases.abs_chiScale_le_chiSup ℓ z)
                (hDil (ℓ * d) (by positivity) (z - (ℓ * d) • u) k) (abs_nonneg _)
                (le_of_lt Submission.BoseGases.chiSup_pos))
          (by rw [abs_mul]
              exact mul_le_mul
                (Submission.BoseGases.abs_chiScale_le_chiSup (ℓ * d) (z - (ℓ * d) • u))
                (hDil ℓ hℓ z k) (abs_nonneg _)
                (le_of_lt Submission.BoseGases.chiSup_pos))
    · -- outside the box: the state vanishes on the open neighbourhood `(acube ℓ)ᶜ`
      have hev : (fun y : E3 => Submission.BoseGases.chiB ℓ d u y * (g y - ρ u))
          =ᶠ[𝓝 z] Function.const E3 (0 : ℝ) := by
        rw [Filter.eventuallyEq_iff_exists_mem]
        obtain ⟨ε, hε, hsub⟩ :=
          Metric.isOpen_iff.mp (Submission.BoseGases.acube_isClosed ℓ).isOpen_compl z hz
        exact ⟨Metric.ball z ε, Metric.ball_mem_nhds z hε, fun y hy => by
          rw [Function.const_apply]
          exact hzero y (hsub hy)⟩
      have h1 : fderiv ℝ (fun y : E3 => Submission.BoseGases.chiB ℓ d u y * (g y - ρ u)) z
          = fderiv ℝ (Function.const E3 (0 : ℝ)) z :=
        Filter.EventuallyEq.fderiv_eq (𝕜 := ℝ) hev
      rw [h1, fderiv_const]
      simpa using hD0
  -- ## The box-supported a priori estimate for the cutoff kinetic symbol
  have hbs := Work.BSKinetic.bsW_fsKinCoeff_le (ℓ := ℓ) (c := c) hℓ hcont hcs hzero hb hb'
  have hnn : 0 ≤ Work.BSKinetic.Decomp.bsW (Submission.BoseGases.fsKinCoeff c)
      (fun z : E3 => Submission.BoseGases.chiB ℓ d u z * (g z - ρ u)) := by
    rw [Work.BSKinetic.Decomp.bsW]
    exact integral_nonneg (fun p =>
      mul_nonneg (Submission.BoseGases.fsKinCoeff_nonneg c ‖p‖) (sq_nonneg _))
  have hπ : 0 < (2 * Real.pi) ^ 3 := by positivity
  have hmul := mul_le_mul_of_nonneg_left hbs (le_of_lt hπ)
  have hid : (2 * Real.pi) ^ 3
        * (((2 * Real.pi) ^ 3)⁻¹ * Work.BSKinetic.Decomp.bsW (Submission.BoseGases.fsKinCoeff c)
            (fun z : E3 => Submission.BoseGases.chiB ℓ d u z * (g z - ρ u)))
      = Work.BSKinetic.Decomp.bsW (Submission.BoseGases.fsKinCoeff c)
          (fun z : E3 => Submission.BoseGases.chiB ℓ d u z * (g z - ρ u)) := by
    rw [← mul_assoc, mul_inv_cancel₀ (ne_of_gt hπ), one_mul]
  rw [hid] at hmul
  exact hmul

/-! ## 3. The target -/

/-- `u`-integrability of the cut word of a smoothly-varying windowed state with a bounded
measurable mean shift: for `0 < ℓ`, `0 < d`, smooth `g` and measurable, uniformly bounded `ρ`,
the function `u ↦ bsW (fsKinCoeff c) (χ_{B(u)}·(g − ρ u))` is integrable.  The `u`-support of
`χ_{B(u)}` is the fixed cube `acube ((1+d)/d)`.

Route: joint strong measurability of `u ↦ bsW (fsKinCoeff c) h_u` via
`StronglyMeasurable.integral_prod_right'` (as in `Work.OneBodyKin.MeasurableBSOneBody`,
`Work.UBBInputs9.B.pd_aux.aemeasurable_boxMean`); vanishing off `acube ((1+d)/d)`
(`Work.BoseFixB1S.chiB_mul_eq_zero_of_not_mem_acube_u`); a uniform bound on that cube from
`Work.BSKinetic.bsW_fsKinCoeff_le` with `ContDiff`/`HasCompactSupport`/sup/derivative bounds
(the derivative bound from `Work.BlockBound4.chiScale_grad_bound`); then
`MeasureTheory.Integrable.mono'` against `C * (acube ((1+d)/d)).indicator 1`.

CAUTION: the identically-stated `Work.BoseFixB1S.corrMarg.integrable_bsW_chiB_sub` is itself a
`sorry`; proving this by `exact`ing it would make the proof depend on `sorryAx`.  Prove it from
scratch. -/
theorem integrableBSWCutKH {ℓ d c : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d)
    {g : EuclideanSpace ℝ (Fin 3) → ℝ} (hg : ContDiff ℝ (⊤ : ENat) g)
    {ρ : EuclideanSpace ℝ (Fin 3) → ℝ} (hρ : Measurable ρ)
    (hρbd : ∃ C : ℝ, ∀ u : EuclideanSpace ℝ (Fin 3), |ρ u| ≤ C) :
    MeasureTheory.Integrable (fun u : EuclideanSpace ℝ (Fin 3) =>
      Work.BSKinetic.Decomp.bsW (Submission.BoseGases.fsKinCoeff c)
        (fun z : EuclideanSpace ℝ (Fin 3) =>
          Submission.BoseGases.chiB ℓ d u z * (g z - ρ u))) := by
  obtain ⟨B, _hB0, hB⟩ := bsW_cut_bound (ℓ := ℓ) (d := d) (c := c) hℓ hd hg hρbd
  have hmeas := aemeasurable_bsW_cut (ℓ := ℓ) (d := d) (c := c) hg.continuous hρ
  have hdom : Integrable
      ((Submission.BoseGases.acube ((1 + d) / d)).indicator (fun _ : E3 => B))
      (volume : Measure E3) := by
    rw [integrable_indicator_iff (Submission.BoseGases.acube_measurable _)]
    exact integrableOn_const
      (ne_of_lt (Submission.BoseGases.acube_lt_top _ (by positivity))) (by simp)
  refine Integrable.mono' hdom hmeas ?_
  filter_upwards with u
  by_cases hu : u ∈ Submission.BoseGases.acube ((1 + d) / d)
  · rw [Set.indicator_of_mem hu, Real.norm_eq_abs, abs_of_nonneg]
    · exact hB u hu
    · rw [Work.BSKinetic.Decomp.bsW]
      exact integral_nonneg (fun p =>
        mul_nonneg (Submission.BoseGases.fsKinCoeff_nonneg c ‖p‖) (sq_nonneg _))
  · rw [Set.indicator_of_notMem hu]
    have h0 : (fun z : E3 => Submission.BoseGases.chiB ℓ d u z * (g z - ρ u)) = 0 :=
      Work.BoseFixB1S.chiB_mul_eq_zero_of_not_mem_acube_u hℓ hd hu g (ρ u)
    rw [h0]
    simp [Work.BSKinetic.Decomp.bsW, Work.BSKinetic.Decomp.bsPsi, Submission.BoseGases.kinFT]

end Work.BoseFixB1S.corr
