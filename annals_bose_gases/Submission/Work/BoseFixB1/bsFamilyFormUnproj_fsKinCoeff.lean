import Mathlib.Tactic.Have
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.BoseFixB1.symA_Ftrunc_integral_tendsto
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1.bsFamilyFormUnproj_fsKinCoeff`

The **unprojected** moving-box one-body family form of FS's `lem:LocKinEn`, at the FS cut-off
symbol `fsKinCoeff c = [· − c]₊²`, is diagonal in the `p`-convention Fourier transform with the
explicit symbol `symA`:

  `bsFamilyFormUnproj ℓ (fsKinCoeff c) ψ = (2π)⁻³ ∫_q symA ℓ (fsKinCoeff c) q · ‖kinFT ψ q‖² dq`.

The corpus proves this identity (`Work.OneBodyKin.bsFamilyFormUnproj_eq_symbol`) for radial
symbols `F` that are `L¹` in the radial variable (`∫_p F ‖p‖ dp < ∞`); the FS cut-off
`fsKinCoeff c = [· − c]₊²` grows quadratically and is **not** `L¹`, so it is not an instance.

## The argument (monotone/dominated convergence along radial truncations)

Let `Ftrunc c n r = if r ≤ n then [r − c]₊² else 0` (`Work.OneBodyKin.TruncDefs`): nonnegative,
compactly supported in the radial variable (hence `L¹`), increasing in `n`, with
`Ftrunc c n ↑ fsKinCoeff c` pointwise.  For every `n` the `L¹` theorem gives

  `bsFamilyFormUnproj ℓ (Ftrunc c n) ψ = (2π)⁻³ ∫_q symA ℓ (Ftrunc c n) q ‖kinFT ψ q‖² dq`,

and it remains to let `n → ∞` on both sides.
-/

noncomputable section

open MeasureTheory Filter
open scoped Topology Real ContDiff

namespace Work.BoseFixB1

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

open Submission.BoseGases

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## 1. Far-field vanishing of the unprojected one-body form -/

/-- **Far-field vanishing of the unprojected one-body family form**, for an arbitrary symbol `F`:
once the moving window `χ_u` has left the support of `ψ`, the windowed state `χ_u · ψ` is
identically zero, so its `p`-transform vanishes and the form is `0`. -/
theorem bsOneBodyUnproj_eq_zero_of_far {ℓ : ℝ} (hℓ : 0 < ℓ) (F : ℝ → ℝ)
    {ψ : EuclideanSpace ℝ (Fin 3) → ℝ} (hcs : HasCompactSupport ψ) :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ u : EuclideanSpace ℝ (Fin 3), R ≤ ‖u‖ →
      Work.BSKinetic.bsOneBodyUnproj ℓ F u ψ = 0 := by
  obtain ⟨Rψ, hRψ0, hψzero⟩ :=
    Work.BSKinetic.Decomp.exists_radius_eq_zero_of_hasCompactSupport hcs
  refine ⟨(Rψ + ℓ) / ℓ, div_nonneg (by linarith) hℓ.le, ?_⟩
  intro u hu
  have hℓR : ℓ * ((Rψ + ℓ) / ℓ) = Rψ + ℓ := by field_simp
  have hℓu : Rψ + ℓ ≤ ℓ * ‖u‖ := by
    have h1 : ℓ * ((Rψ + ℓ) / ℓ) ≤ ℓ * ‖u‖ := mul_le_mul_of_nonneg_left hu hℓ.le
    linarith
  have hprod : (fun z : ℝ³ => (Work.BSKinetic.bsWin ℓ u z : ℂ) * (ψ z : ℂ))
      = fun _ => 0 := by
    funext z
    by_cases hz : Work.BSKinetic.bsWin ℓ u z = 0
    · rw [hz]; simp
    · have hzfar : Rψ ≤ ‖z‖ := Work.BSKinetic.Decomp.norm_ge_of_bsWin_ne_zero hℓ hℓu hz
      rw [hψzero z hzfar]
      simp
  rw [Work.BSKinetic.bsOneBodyUnproj, hprod]
  simp [Submission.BoseGases.kinFT]

/-! ## 2. Measurability in the box centre -/

/-- **Measurability in the box centre `u` of the unprojected one-body family form.**  For a
measurable symbol `G` and a continuous `ψ`, `u ↦ bsOneBodyUnproj ℓ G u ψ` is a.e. strongly
measurable: `kinFT` is a parametric Bochner integral, so the parametric-integral lemma
`MeasureTheory.StronglyMeasurable.integral_prod_right'` is applied twice (integrate out the
position `y`, then the momentum `p`), exactly as in `Work.OneBodyKin.MeasurableBSOneBody` but
without the `bsMean` subtraction. -/
theorem aestronglyMeasurable_bsOneBodyUnproj {ℓ : ℝ} {G : ℝ → ℝ} (hG : Measurable G)
    {ψ : EuclideanSpace ℝ (Fin 3) → ℝ} (hψ : Continuous ψ) :
    MeasureTheory.AEStronglyMeasurable
      (fun u : EuclideanSpace ℝ (Fin 3) =>
        Work.BSKinetic.bsOneBodyUnproj ℓ G u ψ) := by
  -- the `y`-integrand of `kinFT (χ_u·ψ) p`, jointly in `(u,p,y)`
  have hexp : StronglyMeasurable (fun q : (ℝ³ × ℝ³) × ℝ³ =>
      Complex.exp (-(Complex.I * ((inner ℝ q.1.2 q.2 : ℝ) : ℂ)))) :=
    (by fun_prop : Continuous (fun q : (ℝ³ × ℝ³) × ℝ³ =>
      Complex.exp (-(Complex.I * ((inner ℝ q.1.2 q.2 : ℝ) : ℂ))))).stronglyMeasurable
  have hwin : StronglyMeasurable (fun q : (ℝ³ × ℝ³) × ℝ³ =>
      (Submission.BoseGases.chiScale ℓ (q.2 - ℓ • q.1.1) : ℂ)) :=
    (by
      apply Complex.continuous_ofReal.comp
      apply (Submission.BoseGases.chiScale_continuous ℓ).comp
      fun_prop : Continuous (fun q : (ℝ³ × ℝ³) × ℝ³ =>
        (Submission.BoseGases.chiScale ℓ (q.2 - ℓ • q.1.1) : ℂ))).stronglyMeasurable
  have hpsi : StronglyMeasurable (fun q : (ℝ³ × ℝ³) × ℝ³ => (ψ q.2 : ℂ)) :=
    (Complex.continuous_ofReal.comp hψ).stronglyMeasurable.comp_measurable (by fun_prop)
  have hf : StronglyMeasurable (fun q : (ℝ³ × ℝ³) × ℝ³ =>
      Complex.exp (-(Complex.I * ((inner ℝ q.1.2 q.2 : ℝ) : ℂ))) *
        ((Submission.BoseGases.chiScale ℓ (q.2 - ℓ • q.1.1) : ℂ) * (ψ q.2 : ℂ))) :=
    hexp.mul (hwin.mul hpsi)
  -- integrate out the position `y`: this is `(u,p) ↦ kinFT (χ_u·ψ) p`
  have hK : StronglyMeasurable (fun q : ℝ³ × ℝ³ =>
      ∫ y : ℝ³, Complex.exp (-(Complex.I * ((inner ℝ q.2 y : ℝ) : ℂ))) *
        ((Submission.BoseGases.chiScale ℓ (y - ℓ • q.1) : ℂ) * (ψ y : ℂ))) :=
    hf.integral_prod_right' (ν := (volume : Measure ℝ³))
  -- multiply by the symbol `G‖p‖` and take the squared norm
  have hGp : StronglyMeasurable (fun q : ℝ³ × ℝ³ => G ‖q.2‖ *
      ‖(∫ y : ℝ³, Complex.exp (-(Complex.I * ((inner ℝ q.2 y : ℝ) : ℂ))) *
        ((Submission.BoseGases.chiScale ℓ (y - ℓ • q.1) : ℂ) * (ψ y : ℂ)))‖ ^ 2) := by
    have hGm : StronglyMeasurable (fun q : ℝ³ × ℝ³ => G ‖q.2‖) :=
      (hG.comp continuous_norm.measurable).stronglyMeasurable.comp_measurable (by fun_prop)
    exact hGm.mul (hK.norm.pow 2)
  -- integrate out the momentum `p`
  have hF : StronglyMeasurable (fun u : ℝ³ =>
      ∫ p : ℝ³, G ‖p‖ *
        ‖(∫ y : ℝ³, Complex.exp (-(Complex.I * ((inner ℝ p y : ℝ) : ℂ))) *
          ((Submission.BoseGases.chiScale ℓ (y - ℓ • u) : ℂ) * (ψ y : ℂ)))‖ ^ 2) :=
    hGp.integral_prod_right' (ν := (volume : Measure ℝ³))
  -- identify the integral with `bsOneBodyUnproj ℓ G u ψ` and restore the normalisation
  have hfun : (fun u : ℝ³ => ∫ p : ℝ³, G ‖p‖ *
        ‖(∫ y : ℝ³, Complex.exp (-(Complex.I * ((inner ℝ p y : ℝ) : ℂ))) *
          ((Submission.BoseGases.chiScale ℓ (y - ℓ • u) : ℂ) * (ψ y : ℂ)))‖ ^ 2)
      = fun u : ℝ³ => ∫ p : ℝ³, G ‖p‖ *
          ‖Submission.BoseGases.kinFT (fun z : ℝ³ =>
            (Work.BSKinetic.bsWin ℓ u z : ℂ) * (ψ z : ℂ)) p‖ ^ 2 := by
    funext u
    rfl
  rw [hfun] at hF
  exact (hF.const_mul (((2 * Real.pi) ^ 3)⁻¹)).aestronglyMeasurable

/-! ## 3. Monotone convergence in `n` of the `p`-integral -/

private lemma contDiff_bsWin {ℓ : ℝ} (hℓ : 0 < ℓ) (u : ℝ³) :
    ContDiff ℝ (⊤ : ENat) (Work.BSKinetic.bsWin ℓ u) := by
  change ContDiff ℝ (⊤ : ENat) (fun z : ℝ³ => chiScale ℓ (z - ℓ • u))
  exact (chiScale_contDiff (ne_of_gt hℓ)).comp (contDiff_id.sub contDiff_const)

private lemma hasCompactSupport_bsWin {ℓ : ℝ} (hℓ : 0 < ℓ) (u : ℝ³) :
    HasCompactSupport (Work.BSKinetic.bsWin ℓ u) := by
  change HasCompactSupport (fun z : ℝ³ => chiScale ℓ (z - ℓ • u))
  exact (chiScale_hasCompactSupport (ne_of_gt hℓ)).comp_homeomorph (Homeomorph.subRight (ℓ • u))

/-- The `p`-integrand of the unprojected one-body form at the full FS cut-off is integrable:
it is `Work.BSKinetic.Decomp.integrable_fsKinCoeff_mul_bsPsi_sq` at the windowed state
`χ_u · ψ`, after rewriting the complexification of the pointwise product. -/
private lemma integrable_kinFT_winMul_fsKinCoeff {ℓ c : ℝ} (hℓ : 0 < ℓ)
    {ψ : ℝ³ → ℝ} (hψ : ContDiff ℝ (⊤ : ENat) ψ) (hcs : HasCompactSupport ψ) (u : ℝ³) :
    MeasureTheory.Integrable (fun p : ℝ³ => fsKinCoeff c ‖p‖ *
      ‖Submission.BoseGases.kinFT (fun z : ℝ³ =>
        (Work.BSKinetic.bsWin ℓ u z : ℂ) * (ψ z : ℂ)) p‖ ^ 2) := by
  have hd : ContDiff ℝ (⊤ : ENat) (fun z : ℝ³ => Work.BSKinetic.bsWin ℓ u z * ψ z) :=
    (contDiff_bsWin hℓ u).mul hψ
  have hc : HasCompactSupport (fun z : ℝ³ => Work.BSKinetic.bsWin ℓ u z * ψ z) :=
    (hasCompactSupport_bsWin hℓ u).mul_right
  refine (Work.BSKinetic.Decomp.integrable_fsKinCoeff_mul_bsPsi_sq (c := c) hd hc).congr ?_
  filter_upwards with p
  simp only [Work.BSKinetic.Decomp.bsPsi]
  have hfun : (fun z : ℝ³ => (((Work.BSKinetic.bsWin ℓ u z * ψ z : ℝ)) : ℂ))
      = fun z : ℝ³ => (Work.BSKinetic.bsWin ℓ u z : ℂ) * (ψ z : ℂ) := by
    funext z
    rw [Complex.ofReal_mul]
  rw [hfun]

/-- The `p`-integrand at the truncated symbol is dominated by the untruncated one. -/
private lemma integrable_kinFT_winMul_Ftrunc {ℓ c : ℝ} (hℓ : 0 < ℓ)
    {ψ : ℝ³ → ℝ} (hψ : ContDiff ℝ (⊤ : ENat) ψ) (hcs : HasCompactSupport ψ) (u : ℝ³)
    (n : ℕ) :
    MeasureTheory.Integrable (fun p : ℝ³ => Work.OneBodyKin.Ftrunc c n ‖p‖ *
      ‖Submission.BoseGases.kinFT (fun z : ℝ³ =>
        (Work.BSKinetic.bsWin ℓ u z : ℂ) * (ψ z : ℂ)) p‖ ^ 2) := by
  have hF := integrable_kinFT_winMul_fsKinCoeff (ℓ := ℓ) (c := c) hℓ hψ hcs u
  have hcd : ContDiff ℝ (⊤ : ENat)
      (fun z : ℝ³ => ((Work.BSKinetic.bsWin ℓ u z : ℂ) * (ψ z : ℂ))) :=
    (Complex.ofRealCLM.contDiff.comp (contDiff_bsWin hℓ u)).mul
      (Complex.ofRealCLM.contDiff.comp hψ)
  have hcc : HasCompactSupport (fun z : ℝ³ => ((Work.BSKinetic.bsWin ℓ u z : ℂ) * (ψ z : ℂ))) :=
    ((hasCompactSupport_bsWin hℓ u).comp_left
      (g := (Complex.ofRealCLM : ℝ → ℂ)) (by simp)).mul_right
  have hcont : Continuous (fun p : ℝ³ =>
      ‖Submission.BoseGases.kinFT (fun z : ℝ³ =>
        (Work.BSKinetic.bsWin ℓ u z : ℂ) * (ψ z : ℂ)) p‖ ^ 2) :=
    ((Work.OneBodyKin.continuous_kinFT
      (hcd.continuous.integrable_of_hasCompactSupport hcc)).norm).pow 2
  refine hF.mono' (((Work.OneBodyKin.measurable_Ftrunc c n).comp continuous_norm.measurable).mul
    hcont.measurable).aestronglyMeasurable (Filter.Eventually.of_forall fun p => ?_)
  have hle := Work.OneBodyKin.Ftrunc_le_fsKinCoeff c n ‖p‖
  have hnn : (0:ℝ) ≤ ‖Submission.BoseGases.kinFT (fun z : ℝ³ =>
      (Work.BSKinetic.bsWin ℓ u z : ℂ) * (ψ z : ℂ)) p‖ ^ 2 := sq_nonneg _
  have hf0 : 0 ≤ Work.OneBodyKin.Ftrunc c n ‖p‖ * ‖Submission.BoseGases.kinFT (fun z : ℝ³ =>
      (Work.BSKinetic.bsWin ℓ u z : ℂ) * (ψ z : ℂ)) p‖ ^ 2 :=
    mul_nonneg (Work.OneBodyKin.Ftrunc_nonneg c n ‖p‖) hnn
  rw [Real.norm_of_nonneg hf0]
  exact mul_le_mul_of_nonneg_right hle hnn

/-- **Pointwise (in the box centre `u`) monotone convergence of the truncated unprojected
one-body form.**  `Ftrunc c n ↑ fsKinCoeff c` pointwise, the `p`-integrand is nonnegative and the
prefactor `(2π)⁻³` is positive, so `MeasureTheory.integral_tendsto_of_tendsto_of_monotone`
applies in `p`. -/
theorem bsOneBodyUnproj_Ftrunc_tendsto {ℓ c : ℝ} (hℓ : 0 < ℓ)
    {ψ : EuclideanSpace ℝ (Fin 3) → ℝ} (hψ : ContDiff ℝ (⊤ : ENat) ψ)
    (hcs : HasCompactSupport ψ) (u : EuclideanSpace ℝ (Fin 3)) :
    Filter.Tendsto (fun n : ℕ => Work.BSKinetic.bsOneBodyUnproj ℓ (Work.OneBodyKin.Ftrunc c n) u ψ)
      Filter.atTop (nhds (Work.BSKinetic.bsOneBodyUnproj ℓ (Submission.BoseGases.fsKinCoeff c) u ψ)) := by
  have hFint := integrable_kinFT_winMul_fsKinCoeff (ℓ := ℓ) (c := c) hℓ hψ hcs u
  have hmain : Filter.Tendsto
      (fun n : ℕ => ∫ p : ℝ³, Work.OneBodyKin.Ftrunc c n ‖p‖ *
        ‖Submission.BoseGases.kinFT (fun z : ℝ³ =>
          (Work.BSKinetic.bsWin ℓ u z : ℂ) * (ψ z : ℂ)) p‖ ^ 2)
      Filter.atTop
      (nhds (∫ p : ℝ³, fsKinCoeff c ‖p‖ *
        ‖Submission.BoseGases.kinFT (fun z : ℝ³ =>
          (Work.BSKinetic.bsWin ℓ u z : ℂ) * (ψ z : ℂ)) p‖ ^ 2)) := by
    refine MeasureTheory.integral_tendsto_of_tendsto_of_monotone
      (f := fun n p => Work.OneBodyKin.Ftrunc c n ‖p‖ *
        ‖Submission.BoseGases.kinFT (fun z : ℝ³ =>
          (Work.BSKinetic.bsWin ℓ u z : ℂ) * (ψ z : ℂ)) p‖ ^ 2)
      (F := fun p => fsKinCoeff c ‖p‖ *
        ‖Submission.BoseGases.kinFT (fun z : ℝ³ =>
          (Work.BSKinetic.bsWin ℓ u z : ℂ) * (ψ z : ℂ)) p‖ ^ 2)
      (fun n => integrable_kinFT_winMul_Ftrunc hℓ hψ hcs u n) hFint ?_ ?_
    · filter_upwards with p
      intro n m hnm
      exact mul_le_mul_of_nonneg_right (Work.OneBodyKin.Ftrunc_mono_le c hnm ‖p‖) (sq_nonneg _)
    · filter_upwards with p
      exact (Work.OneBodyKin.Ftrunc_tendsto c ‖p‖).mul_const _
  have hthis := hmain.const_mul (((2 * Real.pi) ^ 3)⁻¹)
  unfold Work.BSKinetic.bsOneBodyUnproj
  exact hthis

/-! ## 4. Uniform-in-`u` bound on the unprojected one-body form -/

private lemma norm_kcStdBasis' (k : Fin 3) :
    ‖Submission.BoseGases.kcStdBasis k‖ = 1 := by
  simp [Submission.BoseGases.kcStdBasis]

/-- The scaled bump vanishes off the centred box `acube ℓ`. -/
private lemma chiScale_eq_zero_of_not_mem_acube {ℓ : ℝ} (hℓ : 0 < ℓ) {z : ℝ³}
    (hz : z ∉ acube ℓ) : chiScale ℓ z = 0 := by
  by_contra h
  apply hz
  rw [mem_acube_iff]
  intro m
  have h1 : ‖z‖ ≤ ℓ / 2 := chiScale_support_le hℓ h
  have h2 : |z m| ≤ ‖z‖ := by
    have := PiLp.norm_apply_le z m
    simpa using this
  have h3 := abs_le.mp (le_trans h2 h1)
  rw [Set.mem_Icc]
  exact ⟨by linarith [h3.1], h3.2⟩

/-- **The co-moving form of the unprojected one-body family form.**  Since translating a function
only multiplies its `p`-transform by a unimodular phase, the windowed state `χ_u · ψ` may be
transported to the origin:

  `bsOneBodyUnproj ℓ F u ψ = (2π)⁻³ · bsW F (fun z => χ_ℓ(z) · ψ(z + ℓ•u))`. -/
private lemma bsOneBodyUnproj_eq_bsW_translate (ℓ : ℝ) (F : ℝ → ℝ) (u : ℝ³) (ψ : ℝ³ → ℝ) :
    Work.BSKinetic.bsOneBodyUnproj ℓ F u ψ
      = ((2 * Real.pi) ^ 3)⁻¹ * Work.BSKinetic.Decomp.bsW F
          (fun z : ℝ³ => chiScale ℓ z * ψ (z + ℓ • u)) := by
  have hkey : ∀ p : ℝ³,
      ‖Submission.BoseGases.kinFT
          (fun z : ℝ³ => (Work.BSKinetic.bsWin ℓ u z : ℂ) * (ψ z : ℂ)) p‖
        = ‖Submission.BoseGases.kinFT
          (fun z : ℝ³ => ((chiScale ℓ z * ψ (z + ℓ • u) : ℝ) : ℂ)) p‖ := by
    intro p
    have h := Work.BSKinetic.Decomp.norm_kinFT_comp_add
      (fun w : ℝ³ => ((chiScale ℓ w * ψ (w + ℓ • u) : ℝ) : ℂ)) (-(ℓ • u)) p
    have h1 : (fun z : ℝ³ =>
          (fun w : ℝ³ => ((chiScale ℓ w * ψ (w + ℓ • u) : ℝ) : ℂ)) (z + -(ℓ • u)))
        = fun z : ℝ³ => (Work.BSKinetic.bsWin ℓ u z : ℂ) * (ψ z : ℂ) := by
      funext z
      show ((chiScale ℓ (z + -(ℓ • u)) * ψ (z + -(ℓ • u) + ℓ • u) : ℝ) : ℂ)
        = (Work.BSKinetic.bsWin ℓ u z : ℂ) * (ψ z : ℂ)
      have hz : z + -(ℓ • u) + ℓ • u = z := by abel
      rw [Work.BSKinetic.bsWin, hz, Complex.ofReal_mul, sub_eq_add_neg]
    rw [h1] at h
    exact h
  unfold Work.BSKinetic.bsOneBodyUnproj Work.BSKinetic.Decomp.bsW Work.BSKinetic.Decomp.bsPsi
  congr 1
  apply MeasureTheory.integral_congr_ae
  filter_upwards with p
  rw [hkey p]

/-- **A uniform-in-`u` bound on the unprojected one-body family form at the FS cut-off.**
The windowed state is transported to the origin (`bsOneBodyUnproj_eq_bsW_translate`) and then
bounded by `Work.BSKinetic.Decomp.bsW_le_L2_Dir`; the `L²` mass and the Dirichlet word of
`χ_ℓ · ψ(· + ℓ•u)` are bounded uniformly in `u` by
`Work.BSKinetic.Decomp.bsL2_le_of_bounded_support` / `bsDir_le_of_bounded_support`, since this
state vanishes off the fixed box `acube ℓ` and both it and its partial derivatives are bounded by
the `u`-independent constants `chiSup·Mψ` and `chiSup·Mψ + Mψ·Mχ`. -/
theorem bsOneBodyUnproj_fsKinCoeff_bound {ℓ c : ℝ} (hℓ : 0 < ℓ)
    {ψ : EuclideanSpace ℝ (Fin 3) → ℝ} (hψ : ContDiff ℝ (⊤ : ENat) ψ)
    (hcs : HasCompactSupport ψ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ u : EuclideanSpace ℝ (Fin 3),
      Work.BSKinetic.bsOneBodyUnproj ℓ (Submission.BoseGases.fsKinCoeff c) u ψ ≤ K := by
  obtain ⟨Mψ, hMψ0, hMψ, hMψd⟩ := Work.BSKinetic.Decomp.exists_bound_fderiv hψ hcs
  obtain ⟨Mχ, hMχ0, hMχ, hMχd⟩ := Work.BSKinetic.Decomp.exists_bound_fderiv
    (chiScale_contDiff (ne_of_gt hℓ)) (chiScale_hasCompactSupport (ne_of_gt hℓ))
  have hC0 : 0 ≤ chiSup * Mψ := mul_nonneg chiSup_pos.le hMψ0
  have hD0 : 0 ≤ chiSup * Mψ + Mψ * Mχ :=
    add_nonneg (mul_nonneg chiSup_pos.le hMψ0) (mul_nonneg hMψ0 hMχ0)
  have hK0 : 0 ≤ 2 * c ^ 2 * ((chiSup * Mψ) ^ 2 * ℓ ^ 3)
      + 2 * (3 * ((chiSup * Mψ + Mψ * Mχ) ^ 2 * ℓ ^ 3)) := by
    have h1 : 0 ≤ (chiSup * Mψ) ^ 2 * ℓ ^ 3 := mul_nonneg (sq_nonneg _) (pow_nonneg hℓ.le 3)
    have h2 : 0 ≤ ((chiSup * Mψ + Mψ * Mχ) ^ 2 * ℓ ^ 3) :=
      mul_nonneg (sq_nonneg _) (pow_nonneg hℓ.le 3)
    have h3 : 0 ≤ 2 * c ^ 2 * ((chiSup * Mψ) ^ 2 * ℓ ^ 3) :=
      mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg c)) h1
    have h4 : 0 ≤ 2 * (3 * ((chiSup * Mψ + Mψ * Mχ) ^ 2 * ℓ ^ 3)) := by positivity
    linarith
  refine ⟨2 * c ^ 2 * ((chiSup * Mψ) ^ 2 * ℓ ^ 3)
      + 2 * (3 * ((chiSup * Mψ + Mψ * Mχ) ^ 2 * ℓ ^ 3)), hK0, fun u => ?_⟩
  have hgd : ContDiff ℝ (⊤ : ENat) (fun z : ℝ³ => chiScale ℓ z * ψ (z + ℓ • u)) :=
    (chiScale_contDiff (ne_of_gt hℓ)).mul (hψ.comp (contDiff_id.add contDiff_const))
  have hgcs : HasCompactSupport (fun z : ℝ³ => chiScale ℓ z * ψ (z + ℓ • u)) :=
    (chiScale_hasCompactSupport (ne_of_gt hℓ)).mul_right
  have hW := Work.BSKinetic.Decomp.bsW_le_L2_Dir (c := c) hgd hgcs
  have hL2 : Work.BSKinetic.Decomp.bsL2 (fun z : ℝ³ => chiScale ℓ z * ψ (z + ℓ • u))
      ≤ (chiSup * Mψ) ^ 2 * ℓ ^ 3 := by
    refine Work.BSKinetic.Decomp.bsL2_le_of_bounded_support hℓ hC0 ?_ ?_
    · intro z
      show |chiScale ℓ z * ψ (z + ℓ • u)| ≤ chiSup * Mψ
      rw [abs_mul]
      exact mul_le_mul (abs_chiScale_le_chiSup ℓ z) (hMψ (z + ℓ • u))
        (abs_nonneg _) chiSup_pos.le
    · intro z hz
      show chiScale ℓ z * ψ (z + ℓ • u) = 0
      rw [chiScale_eq_zero_of_not_mem_acube hℓ hz, zero_mul]
  have hDir : Work.BSKinetic.Decomp.bsDir (fun z : ℝ³ => chiScale ℓ z * ψ (z + ℓ • u))
      ≤ 3 * ((chiSup * Mψ + Mψ * Mχ) ^ 2 * ℓ ^ 3) := by
    refine Work.BSKinetic.Decomp.bsDir_le_of_bounded_support hℓ hD0 ?_ ?_
    · intro k z
      have hz1 : DifferentiableAt ℝ (chiScale ℓ) z :=
        ((chiScale_contDiff (ne_of_gt hℓ)).differentiable (by simp)).differentiableAt
      have hz2 : DifferentiableAt ℝ (fun w : ℝ³ => ψ (w + ℓ • u)) z :=
        (hψ.differentiable (by simp)).differentiableAt.comp z (differentiableAt_id.add_const _)
      have hleib : fderiv ℝ (fun z : ℝ³ => chiScale ℓ z * ψ (z + ℓ • u)) z (kcStdBasis k)
          = chiScale ℓ z * fderiv ℝ ψ (z + ℓ • u) (kcStdBasis k)
            + ψ (z + ℓ • u) * fderiv ℝ (chiScale ℓ) z (kcStdBasis k) := by
        rw [show (fun z : ℝ³ => chiScale ℓ z * ψ (z + ℓ • u))
            = chiScale ℓ * (fun w : ℝ³ => ψ (w + ℓ • u)) from rfl]
        rw [fderiv_mul hz1 hz2]
        simp only [add_apply, smul_apply, smul_eq_mul]
        rw [fderiv_comp_add_right]
      rw [hleib]
      have hb1 : |chiScale ℓ z * fderiv ℝ ψ (z + ℓ • u) (kcStdBasis k)| ≤ chiSup * Mψ := by
        rw [abs_mul]
        refine mul_le_mul (abs_chiScale_le_chiSup ℓ z) ?_ (abs_nonneg _) chiSup_pos.le
        have h := hMψd (z + ℓ • u) (kcStdBasis k)
        rw [Real.norm_eq_abs, norm_kcStdBasis', mul_one] at h
        exact h
      have hb2 : |ψ (z + ℓ • u) * fderiv ℝ (chiScale ℓ) z (kcStdBasis k)| ≤ Mψ * Mχ := by
        rw [abs_mul]
        refine mul_le_mul (hMψ (z + ℓ • u)) ?_ (abs_nonneg _) hMψ0
        have h := hMχd z (kcStdBasis k)
        rw [Real.norm_eq_abs, norm_kcStdBasis', mul_one] at h
        exact h
      calc |chiScale ℓ z * fderiv ℝ ψ (z + ℓ • u) (kcStdBasis k)
            + ψ (z + ℓ • u) * fderiv ℝ (chiScale ℓ) z (kcStdBasis k)|
          ≤ |chiScale ℓ z * fderiv ℝ ψ (z + ℓ • u) (kcStdBasis k)|
            + |ψ (z + ℓ • u) * fderiv ℝ (chiScale ℓ) z (kcStdBasis k)| := abs_add_le _ _
        _ ≤ chiSup * Mψ + Mψ * Mχ := add_le_add hb1 hb2
    · intro z hz
      show chiScale ℓ z * ψ (z + ℓ • u) = 0
      rw [chiScale_eq_zero_of_not_mem_acube hℓ hz, zero_mul]
  rw [bsOneBodyUnproj_eq_bsW_translate ℓ (Submission.BoseGases.fsKinCoeff c) u ψ]
  have h1 : 2 * c ^ 2 * Work.BSKinetic.Decomp.bsL2 (fun z : ℝ³ => chiScale ℓ z * ψ (z + ℓ • u))
      ≤ 2 * c ^ 2 * ((chiSup * Mψ) ^ 2 * ℓ ^ 3) :=
    mul_le_mul_of_nonneg_left hL2 (by positivity)
  have h2 : 2 * Work.BSKinetic.Decomp.bsDir (fun z : ℝ³ => chiScale ℓ z * ψ (z + ℓ • u))
      ≤ 2 * (3 * ((chiSup * Mψ + Mψ * Mχ) ^ 2 * ℓ ^ 3)) :=
    mul_le_mul_of_nonneg_left hDir (by norm_num)
  linarith

/-! ## 5. Monotone convergence of the family form along the truncations -/

/-- **The unprojected family form converges along the radial truncations**, by monotone
convergence in the box centre `u`: the `u`-integrands are `L¹` (`integrable_kinFT_winMul_*`), the
limit is `L¹` because it is bounded (`bsOneBodyUnproj_fsKinCoeff_bound`), a.e. strongly measurable
(`aestronglyMeasurable_bsOneBodyUnproj`) and compactly supported
(`bsOneBodyUnproj_eq_zero_of_far`), and the pointwise convergence in `n` is
`bsOneBodyUnproj_Ftrunc_tendsto`. -/
theorem bsFamilyFormUnproj_Ftrunc_tendsto {ℓ c : ℝ} (hℓ : 0 < ℓ)
    {ψ : EuclideanSpace ℝ (Fin 3) → ℝ} (hψ : ContDiff ℝ (⊤ : ENat) ψ)
    (hcs : HasCompactSupport ψ) :
    Filter.Tendsto
      (fun n : ℕ => Work.BSKinetic.bsFamilyFormUnproj ℓ (Work.OneBodyKin.Ftrunc c n) ψ)
      Filter.atTop
      (nhds (Work.BSKinetic.bsFamilyFormUnproj ℓ (Submission.BoseGases.fsKinCoeff c) ψ)) := by
  obtain ⟨K, hK0, hK⟩ := bsOneBodyUnproj_fsKinCoeff_bound (c := c) hℓ hψ hcs
  obtain ⟨R, hR0, hR⟩ := bsOneBodyUnproj_eq_zero_of_far hℓ (Submission.BoseGases.fsKinCoeff c) hcs
  have hmeasFs : Measurable (Submission.BoseGases.fsKinCoeff c) := by
    have hcont : Continuous (fun r : ℝ => Submission.BoseGases.fsKinCoeff c r) := by
      simp only [Submission.BoseGases.fsKinCoeff]
      exact ((continuous_id.sub continuous_const).max continuous_const).pow 2
    exact hcont.measurable
  have hmeasLim : MeasureTheory.AEStronglyMeasurable
      (fun u : ℝ³ => Work.BSKinetic.bsOneBodyUnproj ℓ (Submission.BoseGases.fsKinCoeff c) u ψ) :=
    aestronglyMeasurable_bsOneBodyUnproj hmeasFs hψ.continuous
  have hnnFull : ∀ u : ℝ³,
      0 ≤ Work.BSKinetic.bsOneBodyUnproj ℓ (Submission.BoseGases.fsKinCoeff c) u ψ := by
    intro u
    rw [Work.BSKinetic.bsOneBodyUnproj]
    exact mul_nonneg (by positivity)
      (MeasureTheory.integral_nonneg fun p =>
        mul_nonneg (Submission.BoseGases.fsKinCoeff_nonneg c ‖p‖) (sq_nonneg _))
  have hIntLim : MeasureTheory.Integrable
      (fun u : ℝ³ => Work.BSKinetic.bsOneBodyUnproj ℓ (Submission.BoseGases.fsKinCoeff c) u ψ) :=
    Work.BSKinetic.integrable_of_compact_support
      ⟨Metric.closedBall 0 R, isCompact_closedBall _ _, fun u hu => by
        rw [Metric.mem_closedBall, dist_zero_right]
        by_contra hc
        push_neg at hc
        exact hu (hR u hc.le)⟩
      hmeasLim ⟨K, fun u => by rw [Real.norm_of_nonneg (hnnFull u)]; exact hK u⟩
  have hnnTr : ∀ (n : ℕ) (u : ℝ³),
      0 ≤ Work.BSKinetic.bsOneBodyUnproj ℓ (Work.OneBodyKin.Ftrunc c n) u ψ := by
    intro n u
    rw [Work.BSKinetic.bsOneBodyUnproj]
    exact mul_nonneg (by positivity)
      (MeasureTheory.integral_nonneg fun p =>
        mul_nonneg (Work.OneBodyKin.Ftrunc_nonneg c n ‖p‖) (sq_nonneg _))
  have hIntTr : ∀ n : ℕ, MeasureTheory.Integrable
      (fun u : ℝ³ => Work.BSKinetic.bsOneBodyUnproj ℓ (Work.OneBodyKin.Ftrunc c n) u ψ) := by
    intro n
    refine hIntLim.mono'
      (aestronglyMeasurable_bsOneBodyUnproj (Work.OneBodyKin.measurable_Ftrunc c n)
        hψ.continuous) ?_
    filter_upwards with u
    rw [Real.norm_of_nonneg (hnnTr n u)]
    rw [Work.BSKinetic.bsOneBodyUnproj]
    exact mul_le_mul_of_nonneg_left (MeasureTheory.integral_mono
      (integrable_kinFT_winMul_Ftrunc hℓ hψ hcs u n)
      (integrable_kinFT_winMul_fsKinCoeff hℓ hψ hcs u)
      (fun p => mul_le_mul_of_nonneg_right (Work.OneBodyKin.Ftrunc_le_fsKinCoeff c n ‖p‖)
        (sq_nonneg _))) (by positivity)
  have hmain : Filter.Tendsto
      (fun n : ℕ => ∫ u : ℝ³, Work.BSKinetic.bsOneBodyUnproj ℓ (Work.OneBodyKin.Ftrunc c n) u ψ)
      Filter.atTop
      (nhds (∫ u : ℝ³,
        Work.BSKinetic.bsOneBodyUnproj ℓ (Submission.BoseGases.fsKinCoeff c) u ψ)) := by
    refine MeasureTheory.integral_tendsto_of_tendsto_of_monotone
      (f := fun n u => Work.BSKinetic.bsOneBodyUnproj ℓ (Work.OneBodyKin.Ftrunc c n) u ψ)
      (F := fun u => Work.BSKinetic.bsOneBodyUnproj ℓ (Submission.BoseGases.fsKinCoeff c) u ψ)
      hIntTr hIntLim ?_ ?_
    · filter_upwards with u
      intro n m hnm
      unfold Work.BSKinetic.bsOneBodyUnproj
      exact mul_le_mul_of_nonneg_left (MeasureTheory.integral_mono
        (integrable_kinFT_winMul_Ftrunc hℓ hψ hcs u n)
        (integrable_kinFT_winMul_Ftrunc hℓ hψ hcs u m)
        (fun p => mul_le_mul_of_nonneg_right (Work.OneBodyKin.Ftrunc_mono_le c hnm ‖p‖)
          (sq_nonneg _))) (by positivity)
    · filter_upwards with u
      exact bsOneBodyUnproj_Ftrunc_tendsto hℓ hψ hcs u
  unfold Work.BSKinetic.bsFamilyFormUnproj
  exact hmain

/-! ## 6. The target -/

theorem bsFamilyFormUnproj_fsKinCoeff {ℓ c : ℝ} (hℓ : 0 < ℓ)
    {ψ : EuclideanSpace ℝ (Fin 3) → ℝ} (hψ : ContDiff ℝ (⊤ : ENat) ψ) (hcs : HasCompactSupport ψ) :
    Work.BSKinetic.bsFamilyFormUnproj ℓ (Submission.BoseGases.fsKinCoeff c) ψ
      = ((2 * Real.pi) ^ 3)⁻¹ * ∫ q : EuclideanSpace ℝ (Fin 3),
          Work.OneBodyKin.symA ℓ (Submission.BoseGases.fsKinCoeff c) q *
            ‖Submission.BoseGases.kinFT (fun z : EuclideanSpace ℝ (Fin 3) => (ψ z : ℂ)) q‖ ^ 2 := by
  -- the truncation identity, for every `n`
  have hkey : ∀ n : ℕ, Work.BSKinetic.bsFamilyFormUnproj ℓ (Work.OneBodyKin.Ftrunc c n) ψ
      = ((2 * Real.pi) ^ 3)⁻¹ * ∫ q : EuclideanSpace ℝ (Fin 3),
          Work.OneBodyKin.symA ℓ (Work.OneBodyKin.Ftrunc c n) q *
            ‖Submission.BoseGases.kinFT (fun z : EuclideanSpace ℝ (Fin 3) => (ψ z : ℂ)) q‖ ^ 2 :=
    fun n => Work.OneBodyKin.bsFamilyFormUnproj_eq_symbol hℓ
      (Work.OneBodyKin.integrable_Ftrunc c n) (Work.OneBodyKin.Ftrunc_nonneg c n) ψ hψ hcs
  -- both sides converge along the truncations, and are equal termwise, so the limits agree
  have hL := bsFamilyFormUnproj_Ftrunc_tendsto (ℓ := ℓ) (c := c) hℓ hψ hcs
  have hR := (Work.BoseFixB1.symA_Ftrunc_integral_tendsto (ℓ := ℓ) (c := c) hℓ hψ hcs).const_mul
    (((2 * Real.pi) ^ 3)⁻¹)
  exact tendsto_nhds_unique
    (hL.congr' (Filter.Eventually.of_forall fun n => hkey n)) hR

end Work.BoseFixB1
