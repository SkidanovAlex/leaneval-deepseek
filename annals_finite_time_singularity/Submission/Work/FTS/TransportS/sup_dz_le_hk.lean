/-
Copyright: work module for the Elgindi finite-time singularity project.

# `sup_dz_le_hk`: the pointwise `L^∞`-bound of order `≤ 2` in the open class

This is the open-class (`SmoothOpen` + `HkMem`) counterpart of Elgindi's Corollary
`SecondDerivativesBounded` (tex 1094) for the pure radial derivatives `D_z^b f`, `b ≤ 2`:

  `|D_z^b f(z,θ)| ≤ C / √(γ - 1) · |f|_{ℋ⁴}`   for `z > 0`, `0 < θ < π/2`, `b ≤ 2`,

where `γ = Work.Spaces.gam α`, `D_z = z ∂_z` and `|f|_{ℋ⁴} = Work.Spaces.HkNorm α 4 f`
(`Work.FTS.Nonlin.Xn α f`).  It is the `a = 0` half of the pointwise bound `T2SupF` of
`Submission/Work/FTS/TransportS/T2S.lean`; the `a ≥ 1` half is the σ-gain `flat_mixed_le`.

The proof is the paper's, in the weaker class:

* **angular oscillation at fixed `z`.**  `Work.FTS.H2.OscSqLe` at the `θ`-slice
  `σ ↦ D_z^b f z σ` gives, for a point `θ₀` of the middle half `[π/8, 3π/8]` at which the
  slice attains a value below its mean (`min_mid_le_avg`),

    `(D_z^bf(z,θ) - D_z^bf(z,θ₀))² ≤ (100/(γ-1)) ∫_σ (∂_θ D_z^bf(z,σ))² sin(2σ)^{2-γ} dσ`,

  so that `(D_z^bf(z,θ))² ≤ (200/(γ-1))·A(z) + (8/π)·V(z)` for the two `θ`-integrals
  `A(z) = ∫_σ (∂_θD_z^bf(z,σ))²sin(2σ)^{2-γ}` and `V(z) = ∫_σ (D_z^bf(z,σ))²`.

* **the two integrals are bounded uniformly in `z`** by `HkSq α 4 f`
  (`Work.FTS.TransportS.SupDzAux.sup_dz_ang_le`, `...sup_dz_avg_le`).  Those two lemmas
  are the analytic content of the missing decay hypothesis: they are proved from the
  *window* form of the radial Hardy inequality
  (`Work.FTS.TransportS.half_line_window_bound`) applied slicewise in the angle, together
  with the pointwise domination of the weighted derivatives by the `ℋ⁴`-integrand and
  Tonelli's theorem (`Work.FTS.H2.swap_iterated_integral_of_nonneg`) to handle the
  measure-zero angles.

The constant `C` is universal (`√(200·CA + 8/π·CV) + 1` with `CA = CV = 3`); the factor
`1/√(γ-1)` is the angular Hardy loss, as in the paper.

Every declaration here rests on the axioms `propext`, `Classical.choice`, `Quot.sound` only.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.TransportS.Defs
import Submission.Work.FTS.H2.OscSqLe
import Submission.Work.FTS.H2.MinLeAvg
import Submission.Work.FTS.H2.SupMixedLeH4
import Submission.Work.FTS.H2.SupMixedNB
import Submission.Work.FTS.TransportS.SupDzAux.HalfLineWindow
import Submission.Work.FTS.TransportS.SupDzAux.sup_dz_avg_le
import Submission.Work.FTS.TransportS.SupDzAux.sup_dz_ang_le
import Submission.Work.FTS.EllipticEst.ThetaU.OpenSliceAux.pth_DzIter_eqOn_of_isOpen
import Submission.Work.Spaces.aesm_slice_of_continuousOn_Qd

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.TransportS

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-! ## Helpers for the assembly -/

/-- `D_z^b (c(θ) · g) = c(θ) · D_z^b g` for a factor `c` depending on `θ` only. -/
theorem DzIter_const_mul (b : ℕ) (c : ℝ → ℝ) (g : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.DzIter b (fun z θ' => c θ' * g z θ') z θ
      = c θ * Work.Spaces.DzIter b g z θ := by
  induction b generalizing z θ with
  | zero => rfl
  | succ b ih =>
      show z * deriv (fun z' => Work.Spaces.DzIter b (fun z θ' => c θ' * g z θ') z' θ) z
        = c θ * (z * deriv (fun z' => Work.Spaces.DzIter b g z' θ) z)
      have hev : (fun z' => Work.Spaces.DzIter b (fun z θ' => c θ' * g z θ') z' θ)
          = fun z' => c θ * Work.Spaces.DzIter b g z' θ := by
        funext z'
        exact ih z' θ
      rw [hev]
      have hder : deriv (fun z' => c θ * Work.Spaces.DzIter b g z' θ) z
          = c θ * deriv (fun z' => Work.Spaces.DzIter b g z' θ) z :=
        deriv_const_mul_field (c θ)
      rw [hder]
      ring

/-- `mixed b 1 f = sin(2θ) · ∂_θ (D_z^b f)` on the open quadrant, for a `SmoothOpen` datum. -/
theorem mixed_one_eq_sin_mul_pth {f : ℝ → ℝ → ℝ} (hF : Work.FTS.EllipticEst.SmoothOpen f)
    (b : ℕ) {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo (0 : ℝ) (π / 2)) :
    Work.Spaces.mixed b 1 f z θ
      = Real.sin (2 * θ) * Work.Spaces.pth (Work.Spaces.DzIter b f) z θ := by
  have h1 : Work.Spaces.mixed b 1 f z θ
      = Work.Spaces.DzIter b (fun z θ' => Real.sin (2 * θ') * Work.Spaces.pth f z θ') z θ := by
    rfl
  rw [h1, DzIter_const_mul b (fun θ' => Real.sin (2 * θ')) (Work.Spaces.pth f) z θ]
  have h2 : Work.Spaces.pth (Work.Spaces.DzIter b f) z θ
      = Work.Spaces.DzIter b (Work.Spaces.pth f) z θ :=
    Work.FTS.EllipticEst.ThetaU.OpenSliceAux.pth_DzIter_eqOn_of_isOpen
      Work.FTS.EllipticEst.isOpen_Q0 ((Work.FTS.EllipticEst.smoothOpen_iff_forall f).mp hF) b
      (Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz, hθ.1, hθ.2⟩)
  rw [h2]

/-- Over the middle half `[π/8, 3π/8]` of `Iθ`, some point has value at most `(4/π)` times
the integral over `Iθ` (the open-class replacement of `MinLeAvg`, which needs continuity
on the *closed* interval `Iθ`). -/
theorem min_mid_le_avg {φ : ℝ → ℝ}
    (hcont : ContinuousOn φ (Set.Icc (π / 8) (3 * π / 8)))
    (hint : MeasureTheory.IntegrableOn φ Work.Spaces.Iθ)
    (hnn : ∀ θ ∈ Work.Spaces.Iθ, 0 ≤ φ θ) :
    ∃ θ₀ ∈ Set.Icc (π / 8) (3 * π / 8),
      φ θ₀ ≤ (4 / Real.pi) * ∫ θ in Work.Spaces.Iθ, φ θ := by
  have hle : π / 8 ≤ 3 * π / 8 := by linarith [Real.pi_pos]
  obtain ⟨θ₀, hθ₀, hmin⟩ :=
    (isCompact_Icc (a := π / 8) (b := 3 * π / 8)).exists_isMinOn
      ⟨π / 8, by simp only [Set.mem_Icc]; exact ⟨le_rfl, hle⟩⟩ hcont
  refine ⟨θ₀, hθ₀, ?_⟩
  have hsub : Set.Icc (π / 8) (3 * π / 8) ⊆ Work.Spaces.Iθ := by
    intro x hx
    simp only [Work.Spaces.Iθ, Set.mem_Icc]
    exact ⟨by linarith [hx.1, Real.pi_pos], by linarith [hx.2, Real.pi_pos]⟩
  have hmeas : MeasurableSet (Set.Icc (π / 8) (3 * π / 8)) := measurableSet_Icc
  have hIccint : MeasureTheory.IntegrableOn φ (Set.Icc (π / 8) (3 * π / 8)) :=
    hcont.integrableOn_compact isCompact_Icc
  have hconst : MeasureTheory.IntegrableOn (fun _ : ℝ => φ θ₀)
      (Set.Icc (π / 8) (3 * π / 8)) :=
    integrableOn_const (μ := MeasureTheory.volume)
      (isCompact_Icc (a := π / 8) (b := 3 * π / 8)).measure_lt_top.ne (by simp)
  have hmono : ∫ θ in Set.Icc (π / 8) (3 * π / 8), φ θ₀
      ≤ ∫ θ in Set.Icc (π / 8) (3 * π / 8), φ θ :=
    setIntegral_mono_on hconst hIccint hmeas (fun θ hθ => hmin hθ)
  have hval : ∫ θ in Set.Icc (π / 8) (3 * π / 8), φ θ₀ = φ θ₀ * (π / 4) := by
    rw [setIntegral_const, MeasureTheory.Measure.real_def, Real.volume_Icc,
      ENNReal.toReal_ofReal (by linarith [Real.pi_pos] : (0 : ℝ) ≤ 3 * π / 8 - π / 8)]
    ring
  have h2 : (∫ θ in Set.Icc (π / 8) (3 * π / 8), φ θ)
      ≤ ∫ θ in Work.Spaces.Iθ, φ θ := by
    rw [show Work.Spaces.Iθ = Set.Icc (0 : ℝ) (π / 2) from rfl]
    exact MeasureTheory.setIntegral_mono_set hint
      (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc hnn)
      (Filter.Eventually.of_forall (fun x hx => hsub hx))
  have h3 : φ θ₀ * (π / 4) ≤ ∫ θ in Work.Spaces.Iθ, φ θ := by
    rw [← hval]
    exact hmono.trans h2
  have h4 : φ θ₀ ≤ (∫ θ in Work.Spaces.Iθ, φ θ) / (π / 4) :=
    (le_div_iff₀ (by linarith [Real.pi_pos] : (0 : ℝ) < π / 4)).mpr (by linarith [h3])
  calc φ θ₀ ≤ (∫ θ in Work.Spaces.Iθ, φ θ) / (π / 4) := h4
    _ = (4 / Real.pi) * ∫ θ in Work.Spaces.Iθ, φ θ := by
        rw [div_eq_mul_inv, inv_div]
        ring

/-- `volume.restrict Iθ = volume.restrict (0, π/2)`. -/
theorem restrict_Iθ_eq :
    MeasureTheory.volume.restrict Work.Spaces.Iθ
      = MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) (π / 2)) := by
  have h : Set.Ioo (0 : ℝ) (π / 2) =ᵐ[MeasureTheory.volume] Work.Spaces.Iθ :=
    MeasureTheory.Ioo_ae_eq_Icc
  exact MeasureTheory.Measure.restrict_congr_set h.symm

/-! ## The target -/

theorem sup_dz_le_hk :
    ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (f : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 →
      Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.HkMem α 4 f →
      ∀ b : ℕ, b ≤ 2 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 →
        |Work.Spaces.DzIter b f z θ| ≤ C / Real.sqrt (Work.Spaces.gam α - 1)
          * Work.FTS.Nonlin.Xn α f := by
  obtain ⟨CV, hCVpos, hV⟩ := Work.FTS.TransportS.SupDzAux.sup_dz_avg_le
  obtain ⟨CA, hCApos, hA⟩ := Work.FTS.TransportS.SupDzAux.sup_dz_ang_le
  set K : ℝ := 200 * CA + 8 / Real.pi * CV with hKdef
  have hKnn : 0 ≤ K := by rw [hKdef]; positivity
  refine ⟨Real.sqrt K + 1, by positivity, ?_⟩
  intro α f hα hα1 hF hmem b hb z θ hz hθ hθ1
  have hγ1 : 0 < Work.Spaces.gam α - 1 := by rw [Work.Spaces.gam_sub_one]; linarith
  have hγ1le : Work.Spaces.gam α - 1 ≤ 1 := by rw [Work.Spaces.gam_sub_one]; linarith
  have hγ2 : Work.Spaces.gam α < 2 := by rw [Work.Spaces.gam]; linarith
  have hHk : 0 ≤ Work.Spaces.HkSq α 4 f := Work.Spaces.HkSq_nonneg α 4 f
  have hzI : z ∈ Work.Spaces.Iz := hz.le
  have hθI : θ ∈ Work.Spaces.Iθ := ⟨hθ.le, hθ1.le⟩
  have hw1 : 1 ≤ (Work.Spaces.w z) ^ 2 := by
    have := one_le_w hz
    nlinarith
  -- pointwise domination by the `ℋ⁴`-integrand
  have hdom : ∀ σ ∈ Set.Ioo (0 : ℝ) (π / 2),
      (Work.Spaces.DzIter b f z σ) ^ 2 ≤ Work.Spaces.HkIntegrand α 4 f z σ := by
    intro σ hσ
    have hsin : 0 < Real.sin (2 * σ) :=
      Real.sin_pos_of_pos_of_lt_pi (by linarith [hσ.1]) (by linarith [hσ.2, Real.pi_pos])
    have h1 : (Work.Spaces.DzIter b f z σ) ^ 2 * (Work.Spaces.w z) ^ 2
        ≤ Work.Spaces.HkIntegrand α 4 f z σ :=
      Work.FTS.H2.dzIter_sq_w_le_HkIntegrand α f hsin b (by omega)
    have h2 : (Work.Spaces.DzIter b f z σ) ^ 2
        ≤ (Work.Spaces.DzIter b f z σ) ^ 2 * (Work.Spaces.w z) ^ 2 :=
      le_mul_of_one_le_right (sq_nonneg _) hw1
    exact le_trans h2 h1
  -- the angular domination
  have hdomA : ∀ σ ∈ Set.Ioo (0 : ℝ) (π / 2),
      (Work.Spaces.pth (Work.Spaces.DzIter b f) z σ) ^ 2
          * (Real.sin (2 * σ)) ^ (2 - Work.Spaces.gam α)
        ≤ Work.Spaces.HkIntegrand α 4 f z σ := by
    intro σ hσ
    have hsin : 0 < Real.sin (2 * σ) :=
      Real.sin_pos_of_pos_of_lt_pi (by linarith [hσ.1]) (by linarith [hσ.2, Real.pi_pos])
    have hθσ : σ ∈ Work.Spaces.Iθ := ⟨hσ.1.le, hσ.2.le⟩
    have hmix : Work.Spaces.mixed b 1 f z σ
        = Real.sin (2 * σ) * Work.Spaces.pth (Work.Spaces.DzIter b f) z σ :=
      mixed_one_eq_sin_mul_pth hF b hz hσ
    have hsγ : (Real.sin (2 * σ)) ^ (2 - Work.Spaces.gam α)
        = (Real.sin (2 * σ)) ^ 2 * (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α)) := by
      rw [show 2 - Work.Spaces.gam α = 2 + (-(Work.Spaces.gam α)) by ring,
        Real.rpow_add hsin, Real.rpow_two]
    have hWt : (Work.Spaces.Wt α z σ) ^ 2
        = (Work.Spaces.w z) ^ 2 * (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α)) :=
      Work.FTS.H2.Wt_sq α hα z σ hθσ
    have hslot : (Work.Spaces.mixed b 1 f z σ * Work.Spaces.Wt α z σ) ^ 2
        ≤ Work.Spaces.HkIntegrand α 4 f z σ :=
      Work.Spaces.sq_le_HkIntegrand_mixed α 4 f z σ 1 b le_rfl (by omega)
    have hnn : 0 ≤ (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α)) :=
      Real.rpow_nonneg hsin.le _
    calc (Work.Spaces.pth (Work.Spaces.DzIter b f) z σ) ^ 2
          * (Real.sin (2 * σ)) ^ (2 - Work.Spaces.gam α)
        = (Real.sin (2 * σ) * Work.Spaces.pth (Work.Spaces.DzIter b f) z σ) ^ 2
            * (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α)) := by
          rw [hsγ]
          ring
      _ = (Work.Spaces.mixed b 1 f z σ) ^ 2
            * (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α)) := by
          rw [← hmix]
      _ ≤ (Work.Spaces.mixed b 1 f z σ * Work.Spaces.Wt α z σ) ^ 2 := by
          have hle : (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α))
              ≤ (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α)) * (Work.Spaces.w z) ^ 2 :=
            le_mul_of_one_le_right hnn hw1
          calc (Work.Spaces.mixed b 1 f z σ) ^ 2 * (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α))
              ≤ (Work.Spaces.mixed b 1 f z σ) ^ 2
                  * ((Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α)) * (Work.Spaces.w z) ^ 2) :=
                mul_le_mul_of_nonneg_left hle (sq_nonneg _)
            _ = (Work.Spaces.mixed b 1 f z σ * Work.Spaces.Wt α z σ) ^ 2 := by
                rw [mul_pow, hWt]
                ring
      _ ≤ Work.Spaces.HkIntegrand α 4 f z σ := hslot
  -- integrability of the two slices at the fixed `z`
  have hintu : MeasureTheory.IntegrableOn
      (fun σ => (Work.Spaces.DzIter b f z σ) ^ 2) Work.Spaces.Iθ := by
    refine MeasureTheory.Integrable.mono' (hmem.1 z hzI) ?_ ?_
    · have hcont2 : ContinuousOn (fun p : ℝ × ℝ => (Work.Spaces.DzIter b f p.1 p.2) ^ 2)
          Work.FTS.EllipticEst.Q0 := (hF.DzIter b).continuousOn.pow 2
      exact Work.Spaces.aesm_slice_of_continuousOn_Qd
        (fun p : ℝ × ℝ => (Work.Spaces.DzIter b f p.1 p.2) ^ 2) hcont2 hz
    · rw [restrict_Iθ_eq]
      refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo (fun σ hσ => ?_)
      rw [Real.norm_of_nonneg (sq_nonneg _)]
      exact hdom σ hσ
  have hintA : MeasureTheory.IntegrableOn
      (fun σ => (Work.Spaces.pth (Work.Spaces.DzIter b f) z σ) ^ 2
        * (Real.sin (2 * σ)) ^ (2 - Work.Spaces.gam α)) Work.Spaces.Iθ := by
    refine MeasureTheory.Integrable.mono' (hmem.1 z hzI) ?_ ?_
    · have hcont2 : ContinuousOn
          (fun p : ℝ × ℝ => (Work.Spaces.pth (Work.Spaces.DzIter b f) p.1 p.2) ^ 2
            * (Real.sin (2 * p.2)) ^ (2 - Work.Spaces.gam α)) Work.FTS.EllipticEst.Q0 := by
        refine ((hF.DzIter b).pth).continuousOn.pow 2 |>.mul ?_
        refine (Real.continuous_sin.comp_continuousOn
          ((continuous_const.mul continuous_snd).continuousOn)).rpow_const ?_
        intro p _
        exact Or.inr (by linarith : (0 : ℝ) ≤ 2 - Work.Spaces.gam α)
      exact Work.Spaces.aesm_slice_of_continuousOn_Qd
        (fun p : ℝ × ℝ => (Work.Spaces.pth (Work.Spaces.DzIter b f) p.1 p.2) ^ 2
          * (Real.sin (2 * p.2)) ^ (2 - Work.Spaces.gam α)) hcont2 hz
    · rw [restrict_Iθ_eq]
      refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo (fun σ hσ => ?_)
      have hsin : 0 < Real.sin (2 * σ) :=
        Real.sin_pos_of_pos_of_lt_pi (by linarith [hσ.1]) (by linarith [hσ.2, Real.pi_pos])
      rw [Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hsin.le _))]
      exact hdomA σ hσ
  -- the minimiser of `(D_z^b f z ·)²` over the middle half
  have hcontmid : ContinuousOn (fun σ => (Work.Spaces.DzIter b f z σ) ^ 2)
      (Set.Icc (π / 8) (3 * π / 8)) := by
    have hc : ContinuousOn (fun σ => Work.Spaces.DzIter b f z σ) (Set.Ioo (0 : ℝ) (π / 2)) :=
      ((hF.DzIter b).curry_θ hz).continuousOn
    refine (hc.mono ?_).pow 2
    intro σ hσ
    exact ⟨by linarith [hσ.1, Real.pi_pos], by linarith [hσ.2, Real.pi_pos]⟩
  obtain ⟨θ₀, hθ₀mem, hθ₀le⟩ :=
    min_mid_le_avg hcontmid hintu (fun σ _ => sq_nonneg _)
  have hθ₀I : θ₀ ∈ Work.Spaces.Iθ :=
    ⟨by linarith [hθ₀mem.1, Real.pi_pos], by linarith [hθ₀mem.2, Real.pi_pos]⟩
  have hsub : Set.uIcc θ θ₀ ⊆ Set.Ioo (0 : ℝ) (π / 2) := by
    intro x hx
    rw [Set.mem_uIcc] at hx
    rcases hx with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨by linarith [h1], by linarith [h2, hθ₀mem.2, Real.pi_pos]⟩
    · exact ⟨by linarith [hθ₀mem.1, Real.pi_pos, h1], by linarith [h2]⟩
  have hderiv : ∀ x ∈ Set.uIcc θ θ₀,
      HasDerivAt (fun σ => Work.Spaces.DzIter b f z σ)
        (deriv (fun σ => Work.Spaces.DzIter b f z σ) x) x := by
    intro x hx
    have hxI := hsub hx
    have hc := ((hF.DzIter b).curry_θ hz).differentiableOn
      Work.FTS.LocData.smoothOrder_ne_zero
    exact (hc.differentiableAt (isOpen_Ioo.mem_nhds hxI)).hasDerivAt
  have hcontd : ContinuousOn (deriv (fun σ => Work.Spaces.DzIter b f z σ)) (Set.uIcc θ θ₀) := by
    have hc : ContinuousOn (fun σ => Work.Spaces.pth (Work.Spaces.DzIter b f) z σ)
        (Set.Ioo (0 : ℝ) (π / 2)) := ((hF.DzIter b).pth.curry_θ hz).continuousOn
    exact hc.mono hsub
  have hosc := Work.FTS.H2.OscSqLe α hα hα1 (fun σ => Work.Spaces.DzIter b f z σ)
    hθI hθ₀I hderiv hcontd hintA
  -- the two uniform-in-`z` bounds
  set A : ℝ := ∫ σ in Work.Spaces.Iθ, (Work.Spaces.pth (Work.Spaces.DzIter b f) z σ) ^ 2
      * (Real.sin (2 * σ)) ^ (2 - Work.Spaces.gam α) with hAdef
  set V : ℝ := ∫ σ in Work.Spaces.Iθ, (Work.Spaces.DzIter b f z σ) ^ 2 with hVdef
  have hAb : A ≤ CA * Work.Spaces.HkSq α 4 f := by
    rw [hAdef]; exact hA α f b hα hα1 hF hmem hb z hz
  have hVb : V ≤ CV * Work.Spaces.HkSq α 4 f := by
    rw [hVdef]; exact hV α f b hα hα1 hF hmem hb z hz
  have hoscA : (Work.Spaces.DzIter b f z θ - Work.Spaces.DzIter b f z θ₀) ^ 2
      ≤ (100 / (Work.Spaces.gam α - 1)) * A := by
    rw [hAdef]
    simpa only [Work.Spaces.pth] using hosc
  have hminA : (Work.Spaces.DzIter b f z θ₀) ^ 2 ≤ (4 / Real.pi) * V := by
    rw [hVdef]
    exact hθ₀le
  -- the combination
  have key : (Work.Spaces.DzIter b f z θ) ^ 2 ≤ K / (Work.Spaces.gam α - 1)
      * Work.Spaces.HkSq α 4 f := by
    have h1 : (Work.Spaces.DzIter b f z θ) ^ 2
        ≤ 2 * (Work.Spaces.DzIter b f z θ - Work.Spaces.DzIter b f z θ₀) ^ 2
          + 2 * (Work.Spaces.DzIter b f z θ₀) ^ 2 :=
      by nlinarith [sq_nonneg (Work.Spaces.DzIter b f z θ - 2 * Work.Spaces.DzIter b f z θ₀)]
    have h2 : 2 * (Work.Spaces.DzIter b f z θ - Work.Spaces.DzIter b f z θ₀) ^ 2
        ≤ (200 / (Work.Spaces.gam α - 1)) * A := by
      have h3 := mul_le_mul_of_nonneg_left hoscA (by norm_num : (0 : ℝ) ≤ 2)
      have h4 : (200 / (Work.Spaces.gam α - 1)) * A
          = 2 * ((100 / (Work.Spaces.gam α - 1)) * A) := by ring
      linarith [h3, h4.le, h4.ge]
    have h3 : 2 * (Work.Spaces.DzIter b f z θ₀) ^ 2 ≤ (8 / Real.pi) * V := by
      have h4 := mul_le_mul_of_nonneg_left hminA (by norm_num : (0 : ℝ) ≤ 2)
      have h5 : (8 / Real.pi) * V = 2 * ((4 / Real.pi) * V) := by ring
      linarith [h4, h5.le, h5.ge]
    have hA' : (200 / (Work.Spaces.gam α - 1)) * A
        ≤ (200 * CA / (Work.Spaces.gam α - 1)) * Work.Spaces.HkSq α 4 f := by
      calc (200 / (Work.Spaces.gam α - 1)) * A
          ≤ (200 / (Work.Spaces.gam α - 1)) * (CA * Work.Spaces.HkSq α 4 f) :=
            mul_le_mul_of_nonneg_left hAb (by positivity)
        _ = (200 * CA / (Work.Spaces.gam α - 1)) * Work.Spaces.HkSq α 4 f := by ring
    have hV' : (8 / Real.pi) * V
        ≤ ((8 / Real.pi) * CV / (Work.Spaces.gam α - 1)) * Work.Spaces.HkSq α 4 f := by
      have hγinv : (1 : ℝ) ≤ 1 / (Work.Spaces.gam α - 1) := by
        rw [le_div_iff₀ hγ1]
        simpa using hγ1le
      have hcoef : 0 ≤ (8 / Real.pi) * CV * Work.Spaces.HkSq α 4 f := by positivity
      have h5 : (8 / Real.pi) * CV * Work.Spaces.HkSq α 4 f
          ≤ (8 / Real.pi) * CV * (1 / (Work.Spaces.gam α - 1)) * Work.Spaces.HkSq α 4 f := by
        have h6 : (8 / Real.pi) * CV * 1 ≤ (8 / Real.pi) * CV * (1 / (Work.Spaces.gam α - 1)) :=
          mul_le_mul_of_nonneg_left hγinv (by positivity)
        calc (8 / Real.pi) * CV * Work.Spaces.HkSq α 4 f
            = ((8 / Real.pi) * CV * 1) * Work.Spaces.HkSq α 4 f := by ring
          _ ≤ ((8 / Real.pi) * CV * (1 / (Work.Spaces.gam α - 1)))
                * Work.Spaces.HkSq α 4 f := mul_le_mul_of_nonneg_right h6 hHk
          _ = (8 / Real.pi) * CV * (1 / (Work.Spaces.gam α - 1))
                * Work.Spaces.HkSq α 4 f := by ring
      calc (8 / Real.pi) * V
          ≤ (8 / Real.pi) * (CV * Work.Spaces.HkSq α 4 f) :=
            mul_le_mul_of_nonneg_left hVb (by positivity)
        _ = (8 / Real.pi) * CV * Work.Spaces.HkSq α 4 f := by ring
        _ ≤ (8 / Real.pi) * CV * (1 / (Work.Spaces.gam α - 1)) * Work.Spaces.HkSq α 4 f := h5
        _ = ((8 / Real.pi) * CV / (Work.Spaces.gam α - 1)) * Work.Spaces.HkSq α 4 f := by ring
    calc (Work.Spaces.DzIter b f z θ) ^ 2
        ≤ 2 * (Work.Spaces.DzIter b f z θ - Work.Spaces.DzIter b f z θ₀) ^ 2
          + 2 * (Work.Spaces.DzIter b f z θ₀) ^ 2 := h1
      _ ≤ (200 / (Work.Spaces.gam α - 1)) * A + (8 / Real.pi) * V := add_le_add h2 h3
      _ ≤ (200 * CA / (Work.Spaces.gam α - 1)) * Work.Spaces.HkSq α 4 f
            + ((8 / Real.pi) * CV / (Work.Spaces.gam α - 1)) * Work.Spaces.HkSq α 4 f :=
          add_le_add hA' hV'
      _ = K / (Work.Spaces.gam α - 1) * Work.Spaces.HkSq α 4 f := by
          rw [hKdef]; ring
  -- conclude
  have h2sq : Real.sqrt (K / (Work.Spaces.gam α - 1) * Work.Spaces.HkSq α 4 f)
      = Real.sqrt K / Real.sqrt (Work.Spaces.gam α - 1) * Work.Spaces.HkNorm α 4 f := by
    rw [Real.sqrt_mul (by positivity : (0 : ℝ) ≤ K / (Work.Spaces.gam α - 1)),
      Real.sqrt_div hKnn, Work.Spaces.HkNorm]
  have h3 : Real.sqrt K / Real.sqrt (Work.Spaces.gam α - 1) * Work.Spaces.HkNorm α 4 f
      ≤ (Real.sqrt K + 1) / Real.sqrt (Work.Spaces.gam α - 1)
        * Work.Spaces.HkNorm α 4 f := by
    have hγs : 0 < Real.sqrt (Work.Spaces.gam α - 1) := Real.sqrt_pos.mpr hγ1
    have h4 : Real.sqrt K / Real.sqrt (Work.Spaces.gam α - 1)
        ≤ (Real.sqrt K + 1) / Real.sqrt (Work.Spaces.gam α - 1) := by
      rw [div_le_div_iff_of_pos_right hγs]
      linarith
    exact mul_le_mul_of_nonneg_right h4 (Work.Spaces.HkNorm_nonneg α 4 f)
  calc |Work.Spaces.DzIter b f z θ| ≤ Real.sqrt (K / (Work.Spaces.gam α - 1)
        * Work.Spaces.HkSq α 4 f) := Real.abs_le_sqrt key
    _ = Real.sqrt K / Real.sqrt (Work.Spaces.gam α - 1) * Work.Spaces.HkNorm α 4 f := h2sq
    _ ≤ (Real.sqrt K + 1) / Real.sqrt (Work.Spaces.gam α - 1)
          * Work.Spaces.HkNorm α 4 f := h3
    _ = (Real.sqrt K + 1) / Real.sqrt (Work.Spaces.gam α - 1)
          * Work.FTS.Nonlin.Xn α f := rfl

end Work.FTS.TransportS
