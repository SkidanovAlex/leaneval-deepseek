/-
# The `γ`-weighted angular Cauchy–Schwarz step for the level-six rows (`D_θ`-slots)

This module proves `Work.FTS.StrongPersist.H6Row6Gam.gamSliceCS11`: for a datum `f` which is
`C^∞` on the open quadrant and honestly in `ℋ⁶`, and for every `z > 0`, the two angular slices
`θ ↦ D_z·D_θ f (z,θ)` and `θ ↦ D_z⁵·D_θ f (z,θ)` satisfy the weighted Cauchy–Schwarz
inequality

`∫_Iθ sin(2θ)^{-γ}·|D_zD_θf|·|D_z⁵D_θf| ≤ √(∫_Iθ sin(2θ)^{-γ}(D_zD_θf)²)·√(∫_Iθ sin(2θ)^{-γ}(D_z⁵D_θf)²)`

with weight `sin(2θ)^{-γ}`, `γ = gam α = 1 + α/10`.  It is a *pure* Cauchy–Schwarz statement;
the only work is

* the honestness of the two weighted square integrals, extracted from `HkMem α 6 f`: the slots
  `(i,j) = (1,1)` and `(i,j) = (1,5)` both occur in `HkIntegrand α 6 f` (their weights are
  `(mixed j i f · Wt α)² = w(z)²·sin(2θ)^{-γ}·(mixed j i f)²`), so dividing by the positive
  constant `w(z)²` gives integrability of the slice weight `sin(2θ)^{-γ}` times the slot square;
* the pointwise identity `√(ρX²)·√(ρY²) = ρ|X||Y|` for `ρ = sin(2θ)^{-γ} ≥ 0`, which identifies
  the Cauchy–Schwarz left-hand side with the target integrand.

The same argument works verbatim for *any* pair of mixed slots `(i₁,j₁)`, `(i₂,j₂)` with
`1 ≤ i_k` and `i_k + j_k ≤ 6`; that is the form proved here (`gamSliceCS_weight`), and the
requested statement is its instance `(i₁,j₁) = (1,1)`, `(i₂,j₂) = (1,5)`.

This mirrors `Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.gamSliceCS` (the `(i,j) = (1,0)` case);
nothing is lost beyond the Cauchy–Schwarz inequality itself.
-/
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.Spaces.Defs
import Submission.Work.Spaces.cs_integral
import Submission.Work.Spaces.aesm_slice_of_continuousOn_Qd
import Submission.Work.FTS.EllipticEst.OpenQDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.H6Row6Gam

open MeasureTheory Set Filter
open scoped Real Topology

/-- `sin(2θ) ≥ 0` on `Iθ`. -/
private lemma sin_two_nonneg_gsc {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ Real.sin (2 * θ) :=
  Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])

/-- `sin(2θ) > 0` on the open quadrant. -/
private lemma sin_two_pos_gsc {p : ℝ × ℝ} (hp : p ∈ Work.FTS.EllipticEst.Q0) :
    0 < Real.sin (2 * p.2) := by
  obtain ⟨-, h0, h1⟩ := Work.FTS.EllipticEst.mem_Q0.mp hp
  exact Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])

/-- `(z,θ) ↦ sin(2θ)^{-q}` is continuous on the open quadrant. -/
private lemma continuousOn_sin_rpow_gsc (q : ℝ) :
    ContinuousOn (fun p : ℝ × ℝ => (Real.sin (2 * p.2)) ^ (-q)) Work.FTS.EllipticEst.Q0 :=
  ((Real.continuous_sin.comp (continuous_const.mul continuous_snd)).continuousOn).rpow_const
    (fun _p hp => Or.inl (ne_of_gt (sin_two_pos_gsc hp)))

/-- The square of the mixed weight factorises: `(w·sin(2θ)^{-γ/2})² = w²·sin(2θ)^{-γ}` on `Iθ`. -/
private lemma Wt_sq_eq_gsc (α z θ : ℝ) (hs : 0 ≤ Real.sin (2 * θ)) :
    (Work.Spaces.Wt α z θ) ^ 2
      = (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) := by
  rw [Work.Spaces.Wt, Work.Spaces.wTheta, mul_pow]
  rw [show ((Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α / 2))) ^ 2
        = ((Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α / 2))) ^ ((2 : ℝ)) from
      (Real.rpow_natCast ((Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α / 2))) 2).symm]
  rw [← Real.rpow_mul hs]
  rw [show (-(Work.Spaces.gam α / 2)) * (2 : ℝ) = -(Work.Spaces.gam α) by ring]

/-- **Cauchy–Schwarz in square-root form on the slice `Iθ`**: for `A`, `B` nonnegative on `Iθ`
and integrable there, `∫_Iθ √A·√B ≤ √(∫_Iθ A)·√(∫_Iθ B)`.  (The nonnegativity is needed only on
`Iθ`, which is all the application has.) -/
private lemma cs_sqrt_le_Iθ_gsc {A B : ℝ → ℝ}
    (hA : IntegrableOn A Work.Spaces.Iθ) (hB : IntegrableOn B Work.Spaces.Iθ)
    (hAnn : ∀ θ ∈ Work.Spaces.Iθ, 0 ≤ A θ) (hBnn : ∀ θ ∈ Work.Spaces.Iθ, 0 ≤ B θ) :
    (∫ θ in Work.Spaces.Iθ, Real.sqrt (A θ) * Real.sqrt (B θ))
      ≤ Real.sqrt (∫ θ in Work.Spaces.Iθ, A θ) * Real.sqrt (∫ θ in Work.Spaces.Iθ, B θ) := by
  have hIθm : MeasurableSet Work.Spaces.Iθ := measurableSet_Icc
  have hsmA : AEStronglyMeasurable (fun θ => Real.sqrt (A θ))
      (volume.restrict Work.Spaces.Iθ) :=
    Real.continuous_sqrt.comp_aestronglyMeasurable hA.aestronglyMeasurable
  have hsmB : AEStronglyMeasurable (fun θ => Real.sqrt (B θ))
      (volume.restrict Work.Spaces.Iθ) :=
    Real.continuous_sqrt.comp_aestronglyMeasurable hB.aestronglyMeasurable
  have hAe : A =ᵐ[volume.restrict Work.Spaces.Iθ] (fun θ => Real.sqrt (A θ) ^ 2) :=
    (ae_restrict_mem hIθm).mono (fun θ hθ => (Real.sq_sqrt (hAnn θ hθ)).symm)
  have hBe : B =ᵐ[volume.restrict Work.Spaces.Iθ] (fun θ => Real.sqrt (B θ) ^ 2) :=
    (ae_restrict_mem hIθm).mono (fun θ hθ => (Real.sq_sqrt (hBnn θ hθ)).symm)
  have hAq : Integrable (fun θ => Real.sqrt (A θ) ^ 2) (volume.restrict Work.Spaces.Iθ) :=
    (show Integrable A (volume.restrict Work.Spaces.Iθ) from hA).congr hAe
  have hBq : Integrable (fun θ => Real.sqrt (B θ) ^ 2) (volume.restrict Work.Spaces.Iθ) :=
    (show Integrable B (volume.restrict Work.Spaces.Iθ) from hB).congr hBe
  have hAlp : MemLp (fun θ => Real.sqrt (A θ)) 2 (volume.restrict Work.Spaces.Iθ) :=
    (memLp_two_iff_integrable_sq hsmA).mpr hAq
  have hBlp : MemLp (fun θ => Real.sqrt (B θ)) 2 (volume.restrict Work.Spaces.Iθ) :=
    (memLp_two_iff_integrable_sq hsmB).mpr hBq
  have hcs := Work.Spaces.cs_integral hAlp hBlp
  have e1 : (∫ θ in Work.Spaces.Iθ, Real.sqrt (A θ) ^ 2) = ∫ θ in Work.Spaces.Iθ, A θ :=
    integral_congr_ae hAe.symm
  have e2 : (∫ θ in Work.Spaces.Iθ, Real.sqrt (B θ) ^ 2) = ∫ θ in Work.Spaces.Iθ, B θ :=
    integral_congr_ae hBe.symm
  rw [e1, e2] at hcs
  have hnn : 0 ≤ ∫ θ in Work.Spaces.Iθ, Real.sqrt (A θ) * Real.sqrt (B θ) :=
    integral_nonneg (f := fun θ => Real.sqrt (A θ) * Real.sqrt (B θ))
      (fun θ => mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
  have hP : 0 ≤ ∫ θ in Work.Spaces.Iθ, A θ := setIntegral_nonneg hIθm hAnn
  have hQ : 0 ≤ ∫ θ in Work.Spaces.Iθ, B θ := setIntegral_nonneg hIθm hBnn
  have hle := (Real.le_sqrt hnn (mul_nonneg hP hQ)).mpr hcs
  rwa [Real.sqrt_mul hP] at hle

/-- **The weighted angular Cauchy–Schwarz inequality for two mixed `D_θ`-slots.**  For any two
slots `(i₁,j₁)`, `(i₂,j₂)` with `1 ≤ i_k` and `i_k + j_k ≤ 6` (so that both slots occur in the
`ℋ⁶`-integrand), and every `z > 0`,
`∫_Iθ sin(2θ)^{-γ}·|D_z^{j₁}D_θ^{i₁}f|·|D_z^{j₂}D_θ^{i₂}f| ≤ √(∫ sin^{-γ}(D_z^{j₁}D_θ^{i₁}f)²)
·√(∫ sin^{-γ}(D_z^{j₂}D_θ^{i₂}f)²)`. -/
theorem gamSliceCS_weight (α : ℝ) (f : ℝ → ℝ → ℝ) (i₁ i₂ j₁ j₂ : ℕ)
    (hi₁ : 1 ≤ i₁) (hi₂ : 1 ≤ i₂) (hij₁ : i₁ + j₁ ≤ 6) (hij₂ : i₂ + j₂ ≤ 6)
    (hsm : Work.FTS.EllipticEst.SmoothOpen f) (hmem : Work.Spaces.HkMem α 6 f) :
    ∀ z : ℝ, 0 < z →
      (∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
          * |Work.Spaces.mixed j₁ i₁ f z θ| * |Work.Spaces.mixed j₂ i₂ f z θ|)
        ≤ Real.sqrt (∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
              * (Work.Spaces.mixed j₁ i₁ f z θ) ^ 2)
          * Real.sqrt (∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
              * (Work.Spaces.mixed j₂ i₂ f z θ) ^ 2) := by
  intro z hz
  have hIθm : MeasurableSet Work.Spaces.Iθ := measurableSet_Icc
  have hsin : ∀ θ ∈ Work.Spaces.Iθ, 0 ≤ Real.sin (2 * θ) :=
    fun θ hθ => sin_two_nonneg_gsc hθ
  -- ## Integrability of the two weighted slot squares
  have hslot : ∀ (i j : ℕ), 1 ≤ i → i + j ≤ 6 → IntegrableOn
      (fun θ : ℝ => (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
        * (Work.Spaces.mixed j i f z θ) ^ 2) Work.Spaces.Iθ := by
    intro i j hi hij
    -- continuity of the slice integrand on the open quadrant
    have hcont : ContinuousOn (fun p : ℝ × ℝ => (Real.sin (2 * p.2)) ^ (-(Work.Spaces.gam α))
        * (Work.Spaces.mixed j i f p.1 p.2) ^ 2) Work.FTS.EllipticEst.Q0 :=
      (continuousOn_sin_rpow_gsc (Work.Spaces.gam α)).mul
        (((hsm.mixed j i).forall 0).continuousOn.pow 2)
    have haesm : AEStronglyMeasurable (fun θ : ℝ =>
        (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
          * (Work.Spaces.mixed j i f z θ) ^ 2) (volume.restrict Work.Spaces.Iθ) :=
      Work.Spaces.aesm_slice_of_continuousOn_Qd _ hcont hz
    -- the `w(z)²`-multiple of that integrand is dominated by the `ℋ⁶`-integrand
    have hbig : IntegrableOn (fun θ : ℝ => (Work.Spaces.w z) ^ 2
        * ((Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
          * (Work.Spaces.mixed j i f z θ) ^ 2)) Work.Spaces.Iθ := by
      refine (hmem.1 z (le_of_lt hz)).mono' (haesm.const_mul ((Work.Spaces.w z) ^ 2)) ?_
      refine ae_restrict_of_forall_mem hIθm (fun θ hθ => ?_)
      have hs := hsin θ hθ
      have hnn : 0 ≤ (Work.Spaces.w z) ^ 2 * ((Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
          * (Work.Spaces.mixed j i f z θ) ^ 2) :=
        mul_nonneg (sq_nonneg _) (mul_nonneg (Real.rpow_nonneg hs _) (sq_nonneg _))
      rw [Real.norm_eq_abs, abs_of_nonneg hnn]
      have hkey : (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2
          = (Work.Spaces.w z) ^ 2 * ((Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
              * (Work.Spaces.mixed j i f z θ) ^ 2) := by
        rw [mul_pow, Wt_sq_eq_gsc α z θ hs]
        ring
      rw [← hkey]
      exact Work.Spaces.sq_le_HkIntegrand_mixed α 6 f z θ i j hi hij
    -- divide the constant `w(z)² > 0` out
    have hw : (Work.Spaces.w z) ^ 2 ≠ 0 := by
      have hpos : 0 < Work.Spaces.w z := by
        rw [Work.Spaces.w]
        exact div_pos (by positivity) (by positivity)
      exact pow_ne_zero 2 (ne_of_gt hpos)
    refine ((show Integrable _ (volume.restrict Work.Spaces.Iθ) from hbig).const_mul
      (((Work.Spaces.w z) ^ 2)⁻¹)).congr (Eventually.of_forall fun θ => ?_)
    exact inv_mul_cancel_left₀ hw _
  -- ## Cauchy–Schwarz with the pointwise square-root identity
  have hCS := cs_sqrt_le_Iθ_gsc
    (A := fun θ : ℝ => (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
      * (Work.Spaces.mixed j₁ i₁ f z θ) ^ 2)
    (B := fun θ : ℝ => (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
      * (Work.Spaces.mixed j₂ i₂ f z θ) ^ 2)
    (hslot i₁ j₁ hi₁ hij₁) (hslot i₂ j₂ hi₂ hij₂)
    (fun θ hθ => mul_nonneg (Real.rpow_nonneg (hsin θ hθ) _) (sq_nonneg _))
    (fun θ hθ => mul_nonneg (Real.rpow_nonneg (hsin θ hθ) _) (sq_nonneg _))
  refine le_trans (le_of_eq ?_) hCS
  refine setIntegral_congr_fun hIθm (fun θ hθ => ?_)
  have hρnn : 0 ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) := Real.rpow_nonneg (hsin θ hθ) _
  rw [Real.sqrt_mul hρnn, Real.sqrt_mul hρnn, Real.sqrt_sq_eq_abs, Real.sqrt_sq_eq_abs]
  rw [show (Real.sqrt ((Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))
          * |Work.Spaces.mixed j₁ i₁ f z θ|)
        * (Real.sqrt ((Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))
          * |Work.Spaces.mixed j₂ i₂ f z θ|)
      = (Real.sqrt ((Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))
          * Real.sqrt ((Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))))
        * (|Work.Spaces.mixed j₁ i₁ f z θ| * |Work.Spaces.mixed j₂ i₂ f z θ|) from by ring,
    Real.mul_self_sqrt hρnn]
  ring

theorem gamSliceCS11 : ∀ (α : ℝ) (f : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 →
    Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.HkMem α 6 f →
    ∀ z : ℝ, 0 < z →
      (∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
          * |Work.Spaces.mixed 1 1 f z θ| * |Work.Spaces.mixed 5 1 f z θ|)
        ≤ Real.sqrt (∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
              * (Work.Spaces.mixed 1 1 f z θ) ^ 2)
          * Real.sqrt (∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
              * (Work.Spaces.mixed 5 1 f z θ) ^ 2) := by
  intro α f _hα _hα1 hsm hmem z hz
  exact gamSliceCS_weight α f 1 1 1 5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hsm hmem z hz

end Work.FTS.StrongPersist.H6Row6Gam
