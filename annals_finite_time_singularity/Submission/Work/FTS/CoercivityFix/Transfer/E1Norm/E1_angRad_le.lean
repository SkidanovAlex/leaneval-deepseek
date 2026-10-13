import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.CoercivityFix.Transfer.Profiles
import Submission.Work.FTS.CoercivityFix.Transfer.E1Norm.Lop_iter_LopGam_Gamma_bound
import Submission.Work.FTS.CoercivityFix.Transfer.E1Norm.Lop_iter_LopGam_gauge_bound
import Submission.Work.FTS.CoercivityFix.Transfer.E1Norm.GaugeMass
import Submission.Work.FTS.Nonlinear.Pieces.rowsN0Q
import Submission.Work.FTS.NonlinRows.AuxAngRad.AngRadWeights
import Submission.Work.Spaces.sin_two_rpow

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `E1Norm.E1_angRad_le` — the angular/radial separation for the transfer defect `E1`

The transfer defect is the separated product

  `E1 α f = (D_θΓ) · (radA α f)`,   `D_θΓ = Lop (Gam α)`,

so write `a θ := Work.Spaces.Lop (Work.Spaces.Gam α) θ` and `r z := radA α f z`.  Since `D_z`
and `D_θ` only see the variable they differentiate, the pure slots of the weighted `ℋⁿ`-integrand
of `a·r` are exactly `a(θ)²·σ(θ)·(D_z^j r(z))²w(z)²` and the mixed slots are exactly
`(D_θ^i a)(θ)²·τ(θ)·(D_z^j r(z))²w(z)²` (`Nonlinear.Pieces.dzIter_ang_rad`,
`Nonlinear.Pieces.mixed_ang_rad`, `RadialProd.light_sq`, `RadialProd.heavy_sq`), where
`σ = sin(2θ)^{-η}` and `τ = sin(2θ)^{-γ}`.  Hence, on the open quadrant,

  `HkIntegrand α n (E1 α f) z θ ≤ R(z)·((K₁α)²σ(θ) + (n+1)(K₂α)² G(θ)²τ(θ))`,

with `R(z) = ∑_{j≤n} (D_z^j r(z))²w(z)²` and `G = Γ(θ)(sin²2θ + α)`, whenever
`|a| ≤ K₁α` and `|D_θ^i a| ≤ K₂α G` for `1 ≤ i ≤ 3`.  Both angular masses are `α`-independent
(and `f`-independent): `∫_θ σ ≤ 10⁴` (`Work.Spaces.sin_two_rpow`) and
`∫_θ G²τ ≤ 1000` (`GaugeMass.gauge_mass`), so integrating in `θ` and then in `z` gives

  `HkSq α n (E1 α f) ≤ C·α²·∫_z R(z)`.

The angular data is supplied by `Lop_iter_LopGam_Gamma_bound` (`i = 0`) and
`Lop_iter_LopGam_gauge_bound`, the `α²` being the `α`-smallness of `D_θΓ`.

Everything here rests on `[propext, Classical.choice, Quot.sound]`.
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.CoercivityFix.Transfer.E1Norm

set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

/-- The angular factor of the pointwise bound: `(K₁α)²σ + (4(K₂α)²)G²τ`, written so that the
two angular masses factor out of the `θ`-integral with `integral_const_mul`. -/
private noncomputable def angF (α K₁ K₂ : ℝ) (θ : ℝ) : ℝ :=
  (K₁ * α) ^ 2 * Work.FTS.Nonlinear.RadialProd.smE θ
    + (4 * (K₂ * α) ^ 2)
        * ((Work.Spaces.Gam α θ * ((Real.sin (2 * θ)) ^ 2 + α)) ^ 2
            * Work.FTS.Nonlinear.RadialProd.smG α θ)

/-- The radial density `∑_{j≤n} (D_z^j r)²w²`. -/
private noncomputable def rsum (n : ℕ) (r : ℝ → ℝ) (z : ℝ) : ℝ :=
  ∑ j ∈ Finset.range (n + 1), (Work.Elliptic.DzdIter j r z) ^ 2 * (Work.Spaces.w z) ^ 2

private lemma rsum_nonneg (n : ℕ) (r : ℝ → ℝ) (z : ℝ) : 0 ≤ rsum n r z := by
  rw [rsum]
  exact Finset.sum_nonneg fun j _ => mul_nonneg (sq_nonneg _) (sq_nonneg _)

/-- The gauge profile `Γ(θ)(sin²2θ + α)` is integrable against `sin(2θ)^{-γ}` on `Iθ`, with
mass at most `1000` (`GaugeMass.gauge_mass`, rewritten in the form used below). -/
private lemma gauge_pair (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) :
    MeasureTheory.IntegrableOn (fun θ : ℝ =>
        (Work.Spaces.Gam α θ * ((Real.sin (2 * θ)) ^ 2 + α)) ^ 2
          * Work.FTS.Nonlinear.RadialProd.smG α θ) Work.Spaces.Iθ ∧
      (∫ θ in Work.Spaces.Iθ, (Work.Spaces.Gam α θ * ((Real.sin (2 * θ)) ^ 2 + α)) ^ 2
          * Work.FTS.Nonlinear.RadialProd.smG α θ) ≤ 1000 := by
  obtain ⟨hint, hbd⟩ := gauge_mass α hα hα1
  have key : ∀ θ : ℝ,
      (Work.Spaces.Gam α θ) ^ 2 * ((Real.sin (2 * θ)) ^ 2 + α) ^ 2
          * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
        = (Work.Spaces.Gam α θ * ((Real.sin (2 * θ)) ^ 2 + α)) ^ 2
          * Work.FTS.Nonlinear.RadialProd.smG α θ := by
    intro θ
    rw [Work.FTS.Nonlinear.RadialProd.smG]
    ring
  refine ⟨hint.congr_fun (fun θ _ => key θ) measurableSet_Icc, ?_⟩
  have hcongr : (∫ θ in Work.Spaces.Iθ, (Work.Spaces.Gam α θ) ^ 2
        * ((Real.sin (2 * θ)) ^ 2 + α) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))
      = ∫ θ in Work.Spaces.Iθ, (Work.Spaces.Gam α θ * ((Real.sin (2 * θ)) ^ 2 + α)) ^ 2
        * Work.FTS.Nonlinear.RadialProd.smG α θ :=
    integral_congr_ae (ae_restrict_of_forall_mem measurableSet_Icc (fun θ _ => key θ))
  rw [← hcongr]
  exact hbd

/-- Integrability of the angular factor `angF` on `Iθ` (stated for the unfolded form; the
`angF`-form is definitionally the same function). -/
private lemma angF_integrable (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (K₁ K₂ : ℝ) :
    Integrable ((fun θ : ℝ => (K₁ * α) ^ 2 * Work.FTS.Nonlinear.RadialProd.smE θ)
      + fun θ : ℝ => (4 * (K₂ * α) ^ 2)
          * ((Work.Spaces.Gam α θ * ((Real.sin (2 * θ)) ^ 2 + α)) ^ 2
              * Work.FTS.Nonlinear.RadialProd.smG α θ))
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
  have hE := Work.Spaces.sin_two_rpow (-(Work.Spaces.eta))
    (by linarith [Work.Spaces.eta_lt_one]) (by linarith [Work.Spaces.eta_pos])
  have hsmE : Integrable (fun θ : ℝ => Work.FTS.Nonlinear.RadialProd.smE θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) := hE.1
  have hGs : Integrable (fun θ : ℝ =>
      (Work.Spaces.Gam α θ * ((Real.sin (2 * θ)) ^ 2 + α)) ^ 2
        * Work.FTS.Nonlinear.RadialProd.smG α θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) := (gauge_pair α hα hα1).1
  exact (hsmE.const_mul ((K₁ * α) ^ 2)).add (hGs.const_mul (4 * (K₂ * α) ^ 2))

/-- The angular mass bound: `∫_θ angF ≤ α²(K₁²10⁴ + 4K₂²10³)` (for the unfolded form). -/
private lemma angF_integral_le (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (K₁ K₂ : ℝ) :
    (∫ θ in Work.Spaces.Iθ, (K₁ * α) ^ 2 * Work.FTS.Nonlinear.RadialProd.smE θ
      + (4 * (K₂ * α) ^ 2) * ((Work.Spaces.Gam α θ * ((Real.sin (2 * θ)) ^ 2 + α)) ^ 2
          * Work.FTS.Nonlinear.RadialProd.smG α θ))
      ≤ α ^ 2 * (K₁ ^ 2 * 10 ^ 4 + 4 * K₂ ^ 2 * 10 ^ 3) := by
  have hE := Work.Spaces.sin_two_rpow (-(Work.Spaces.eta))
    (by linarith [Work.Spaces.eta_lt_one]) (by linarith [Work.Spaces.eta_pos])
  have hsmE : Integrable (fun θ : ℝ => Work.FTS.Nonlinear.RadialProd.smE θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) := hE.1
  have hEbd : (∫ θ in Work.Spaces.Iθ, Work.FTS.Nonlinear.RadialProd.smE θ) ≤ 10 ^ 4 := by
    calc (∫ θ in Work.Spaces.Iθ, Work.FTS.Nonlinear.RadialProd.smE θ)
        = ∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) := rfl
      _ ≤ 100 / (-(Work.Spaces.eta) + 1) := hE.2
      _ = 10 ^ 4 := by rw [Work.Spaces.eta]; norm_num
  obtain ⟨hGsint, hGsbd⟩ := gauge_pair α hα hα1
  have hstep : (∫ θ in Work.Spaces.Iθ, (K₁ * α) ^ 2 * Work.FTS.Nonlinear.RadialProd.smE θ
      + (4 * (K₂ * α) ^ 2) * ((Work.Spaces.Gam α θ * ((Real.sin (2 * θ)) ^ 2 + α)) ^ 2
          * Work.FTS.Nonlinear.RadialProd.smG α θ))
      ≤ (K₁ * α) ^ 2 * 10 ^ 4 + (4 * (K₂ * α) ^ 2) * 1000 := by
    rw [MeasureTheory.integral_add (hsmE.const_mul _) (hGsint.const_mul _)]
    simp only [MeasureTheory.integral_const_mul]
    exact add_le_add (mul_le_mul_of_nonneg_left hEbd (by positivity))
      (mul_le_mul_of_nonneg_left hGsbd (by positivity))
  refine le_trans hstep (le_of_eq ?_)
  ring

/-- **The pointwise (in `θ`) separation of the `ℋⁿ`-integrand of `E1`.** -/
private lemma HkIntegrand_E1_le (α : ℝ) (hα : 0 < α) (n : ℕ) (hn : n ≤ 3)
    {K₁ K₂ : ℝ} (hK₁ : 0 ≤ K₁) (hK₂ : 0 ≤ K₂)
    (ha : ∀ θ ∈ Work.Spaces.Iθ, |Work.Spaces.Lop (Work.Spaces.Gam α) θ| ≤ K₁ * α)
    (hb : ∀ i : ℕ, 1 ≤ i → i ≤ 3 → ∀ θ ∈ Work.Spaces.Iθ,
      |Work.Spaces.DthIter i (fun _ θ' => Work.Spaces.Lop (Work.Spaces.Gam α) θ') 0 θ|
        ≤ K₂ * α * (Work.Spaces.Gam α θ * ((Real.sin (2 * θ)) ^ 2 + α)))
    (f : ℝ → ℝ → ℝ) (z θ : ℝ) (hθ : θ ∈ Set.Ioo (0 : ℝ) (π / 2)) :
    Work.Spaces.HkIntegrand α n (E1 α f) z θ
      ≤ rsum n (radA α f) z * angF α K₁ K₂ θ := by
  change Work.Spaces.HkIntegrand α n
      (fun z θ => Work.Spaces.Lop (Work.Spaces.Gam α) θ * radA α f z) z θ
    ≤ rsum n (radA α f) z * angF α K₁ K₂ θ
  have hsin : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
  have hθI : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
  have hsmEnn : 0 ≤ Work.FTS.Nonlinear.RadialProd.smE θ :=
    Work.FTS.Nonlinear.RadialProd.smE_nonneg hθI
  have hsmGnn : 0 ≤ Work.FTS.Nonlinear.RadialProd.smG α θ :=
    Work.FTS.Nonlinear.RadialProd.smG_nonneg hθI
  have hGnn : 0 ≤ Work.Spaces.Gam α θ * ((Real.sin (2 * θ)) ^ 2 + α) := by
    refine mul_nonneg (Work.Spaces.Gam_bounds α θ hα hθI).1 ?_
    nlinarith [hα, sq_nonneg (Real.sin (2 * θ))]
  have hRnn : 0 ≤ rsum n (radA α f) z := rsum_nonneg n (radA α f) z
  -- ### the two angular bounds
  have ha2 : (Work.Spaces.Lop (Work.Spaces.Gam α) θ) ^ 2 ≤ (K₁ * α) ^ 2 := by
    have h1 : 0 ≤ K₁ * α := mul_nonneg hK₁ hα.le
    have h2 : |Work.Spaces.Lop (Work.Spaces.Gam α) θ| ≤ |K₁ * α| := by
      rw [abs_of_nonneg h1]
      exact ha θ hθI
    calc (Work.Spaces.Lop (Work.Spaces.Gam α) θ) ^ 2
        = |Work.Spaces.Lop (Work.Spaces.Gam α) θ| ^ 2 := by rw [sq_abs]
      _ ≤ |K₁ * α| ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h2 2
      _ = (K₁ * α) ^ 2 := by rw [sq_abs]
  have hb2 : ∀ i : ℕ, 1 ≤ i → i ≤ n →
      (Work.Spaces.DthIter i (fun _ θ' => Work.Spaces.Lop (Work.Spaces.Gam α) θ') 0 θ) ^ 2
        ≤ (K₂ * α * (Work.Spaces.Gam α θ * ((Real.sin (2 * θ)) ^ 2 + α))) ^ 2 := by
    intro i hi1 hin
    have hi3 : i ≤ 3 := by omega
    have h1 : 0 ≤ K₂ * α * (Work.Spaces.Gam α θ * ((Real.sin (2 * θ)) ^ 2 + α)) :=
      mul_nonneg (mul_nonneg hK₂ hα.le) hGnn
    have h2 : |Work.Spaces.DthIter i (fun _ θ' => Work.Spaces.Lop (Work.Spaces.Gam α) θ') 0 θ|
        ≤ |K₂ * α * (Work.Spaces.Gam α θ * ((Real.sin (2 * θ)) ^ 2 + α))| := by
      rw [abs_of_nonneg h1]
      exact hb i hi1 hi3 θ hθI
    calc (Work.Spaces.DthIter i (fun _ θ' => Work.Spaces.Lop (Work.Spaces.Gam α) θ') 0 θ) ^ 2
        = |Work.Spaces.DthIter i (fun _ θ' => Work.Spaces.Lop (Work.Spaces.Gam α) θ') 0 θ| ^ 2 :=
          by rw [sq_abs]
      _ ≤ |K₂ * α * (Work.Spaces.Gam α θ * ((Real.sin (2 * θ)) ^ 2 + α))| ^ 2 :=
          pow_le_pow_left₀ (abs_nonneg _) h2 2
      _ = (K₂ * α * (Work.Spaces.Gam α θ * ((Real.sin (2 * θ)) ^ 2 + α))) ^ 2 := by rw [sq_abs]
  -- ### the pure `D_z`-slots
  have hpure : (∑ i ∈ Finset.range (n + 1),
      (Work.Spaces.DzIter i (fun z θ => Work.Spaces.Lop (Work.Spaces.Gam α) θ * radA α f z) z θ
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
      = (Work.Spaces.Lop (Work.Spaces.Gam α) θ) ^ 2 * Work.FTS.Nonlinear.RadialProd.smE θ
        * rsum n (radA α f) z := by
    have hterm : ∀ i : ℕ,
        (Work.Spaces.DzIter i (fun z θ => Work.Spaces.Lop (Work.Spaces.Gam α) θ * radA α f z) z θ
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
        = (Work.Spaces.Lop (Work.Spaces.Gam α) θ) ^ 2 * Work.FTS.Nonlinear.RadialProd.smE θ
          * ((Work.Elliptic.DzdIter i (radA α f) z) ^ 2 * (Work.Spaces.w z) ^ 2) := by
      intro i
      rw [Work.FTS.Nonlinear.Pieces.dzIter_ang_rad,
        show (Work.Spaces.Lop (Work.Spaces.Gam α) θ * Work.Elliptic.DzdIter i (radA α f) z
              * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
            = ((Work.Spaces.Lop (Work.Spaces.Gam α) θ
                * Work.Elliptic.DzdIter i (radA α f) z)
                * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
          from by ring,
        Work.FTS.Nonlinear.RadialProd.light_sq _ z θ hsin]
      ring
    calc (∑ i ∈ Finset.range (n + 1),
          (Work.Spaces.DzIter i (fun z θ => Work.Spaces.Lop (Work.Spaces.Gam α) θ * radA α f z) z θ
            * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
        = ∑ i ∈ Finset.range (n + 1),
            (Work.Spaces.Lop (Work.Spaces.Gam α) θ) ^ 2 * Work.FTS.Nonlinear.RadialProd.smE θ
              * ((Work.Elliptic.DzdIter i (radA α f) z) ^ 2 * (Work.Spaces.w z) ^ 2) :=
          Finset.sum_congr rfl fun i _ => hterm i
      _ = (Work.Spaces.Lop (Work.Spaces.Gam α) θ) ^ 2 * Work.FTS.Nonlinear.RadialProd.smE θ
            * rsum n (radA α f) z := by
          rw [← Finset.mul_sum, rsum]
  have hpure' : (∑ i ∈ Finset.range (n + 1),
      (Work.Spaces.DzIter i (fun z θ => Work.Spaces.Lop (Work.Spaces.Gam α) θ * radA α f z) z θ
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
      ≤ (K₁ * α) ^ 2 * Work.FTS.Nonlinear.RadialProd.smE θ * rsum n (radA α f) z := by
    rw [hpure]
    exact mul_le_mul_of_nonneg_right (mul_le_mul ha2 le_rfl hsmEnn (sq_nonneg _)) hRnn
  -- ### the mixed `D_θ`-slots
  have hmix : (∑ i ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (n + 1),
        if 1 ≤ i ∧ i + j ≤ n then
          (Work.Spaces.mixed j i
              (fun z θ => Work.Spaces.Lop (Work.Spaces.Gam α) θ * radA α f z) z θ
            * Work.Spaces.Wt α z θ) ^ 2
        else 0)
      ≤ rsum n (radA α f) z
        * (∑ i ∈ Finset.range (n + 1), if 1 ≤ i then
            (Work.Spaces.DthIter i (fun _ θ' => Work.Spaces.Lop (Work.Spaces.Gam α) θ') 0 θ) ^ 2
              * Work.FTS.Nonlinear.RadialProd.smG α θ else 0) := by
    have hterm2 : ∀ i ∈ Finset.range (n + 1), ∀ j ∈ Finset.range (n + 1),
        (if 1 ≤ i ∧ i + j ≤ n then
          (Work.Spaces.mixed j i
              (fun z θ => Work.Spaces.Lop (Work.Spaces.Gam α) θ * radA α f z) z θ
            * Work.Spaces.Wt α z θ) ^ 2
        else 0)
        ≤ (if 1 ≤ i then
              (Work.Spaces.DthIter i (fun _ θ' => Work.Spaces.Lop (Work.Spaces.Gam α) θ') 0 θ) ^ 2
                * Work.FTS.Nonlinear.RadialProd.smG α θ else 0)
          * ((Work.Elliptic.DzdIter j (radA α f) z) ^ 2 * (Work.Spaces.w z) ^ 2) := by
      intro i hi j hj
      by_cases h1 : 1 ≤ i
      · by_cases h2 : i + j ≤ n
        · rw [if_pos ⟨h1, h2⟩, if_pos h1]
          rw [Work.FTS.Nonlinear.Pieces.mixed_ang_rad,
            show (Work.Spaces.DthIter i (fun _ θ' => Work.Spaces.Lop (Work.Spaces.Gam α) θ') 0 θ
                  * Work.Elliptic.DzdIter j (radA α f) z * Work.Spaces.Wt α z θ) ^ 2
                = ((Work.Spaces.DthIter i (fun _ θ' => Work.Spaces.Lop (Work.Spaces.Gam α) θ') 0 θ
                    * Work.Elliptic.DzdIter j (radA α f) z) * Work.Spaces.Wt α z θ) ^ 2
              from by ring,
            Work.FTS.Nonlinear.RadialProd.heavy_sq α _ z θ hsin]
          exact le_of_eq (by ring)
        · rw [if_neg (fun h => h2 h.2), if_pos h1]
          exact mul_nonneg (mul_nonneg (sq_nonneg _) hsmGnn)
            (mul_nonneg (sq_nonneg _) (sq_nonneg _))
      · rw [if_neg (fun h => h1 h.1), if_neg h1]
        simp
    calc (∑ i ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (n + 1),
          if 1 ≤ i ∧ i + j ≤ n then
            (Work.Spaces.mixed j i
                (fun z θ => Work.Spaces.Lop (Work.Spaces.Gam α) θ * radA α f z) z θ
              * Work.Spaces.Wt α z θ) ^ 2
          else 0)
        ≤ ∑ i ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (n + 1),
            (if 1 ≤ i then
                (Work.Spaces.DthIter i (fun _ θ' => Work.Spaces.Lop (Work.Spaces.Gam α) θ') 0 θ) ^ 2
                  * Work.FTS.Nonlinear.RadialProd.smG α θ else 0)
              * ((Work.Elliptic.DzdIter j (radA α f) z) ^ 2 * (Work.Spaces.w z) ^ 2) :=
          Finset.sum_le_sum fun i hi => Finset.sum_le_sum fun j hj => hterm2 i hi j hj
      _ = rsum n (radA α f) z
            * (∑ i ∈ Finset.range (n + 1), if 1 ≤ i then
                (Work.Spaces.DthIter i (fun _ θ' => Work.Spaces.Lop (Work.Spaces.Gam α) θ') 0 θ) ^ 2
                  * Work.FTS.Nonlinear.RadialProd.smG α θ else 0) := by
          rw [← Finset.sum_mul_sum, rsum]
          ring
  -- ### the comparison of the angular profiles
  have hMsum : (∑ i ∈ Finset.range (n + 1), if 1 ≤ i then
        (Work.Spaces.DthIter i (fun _ θ' => Work.Spaces.Lop (Work.Spaces.Gam α) θ') 0 θ) ^ 2
          * Work.FTS.Nonlinear.RadialProd.smG α θ else 0)
      ≤ ((n : ℝ) + 1) * ((K₂ * α) ^ 2
          * (Work.Spaces.Gam α θ * ((Real.sin (2 * θ)) ^ 2 + α)) ^ 2
          * Work.FTS.Nonlinear.RadialProd.smG α θ) := by
    have hCEnn : 0 ≤ (K₂ * α) ^ 2 * (Work.Spaces.Gam α θ * ((Real.sin (2 * θ)) ^ 2 + α)) ^ 2
        * Work.FTS.Nonlinear.RadialProd.smG α θ :=
      mul_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _)) hsmGnn
    have hterm : ∀ i ∈ Finset.range (n + 1),
        (if 1 ≤ i then
          (Work.Spaces.DthIter i (fun _ θ' => Work.Spaces.Lop (Work.Spaces.Gam α) θ') 0 θ) ^ 2
            * Work.FTS.Nonlinear.RadialProd.smG α θ else 0)
        ≤ (K₂ * α) ^ 2 * (Work.Spaces.Gam α θ * ((Real.sin (2 * θ)) ^ 2 + α)) ^ 2
            * Work.FTS.Nonlinear.RadialProd.smG α θ := by
      intro i hi
      by_cases h1 : 1 ≤ i
      · rw [if_pos h1]
        have hin : i ≤ n := by
          have := Finset.mem_range.mp hi
          omega
        have hb2i := hb2 i h1 hin
        have hkey : (K₂ * α * (Work.Spaces.Gam α θ * ((Real.sin (2 * θ)) ^ 2 + α))) ^ 2
            = (K₂ * α) ^ 2 * (Work.Spaces.Gam α θ * ((Real.sin (2 * θ)) ^ 2 + α)) ^ 2 := by
          ring
        calc (Work.Spaces.DthIter i (fun _ θ' => Work.Spaces.Lop (Work.Spaces.Gam α) θ') 0 θ) ^ 2
              * Work.FTS.Nonlinear.RadialProd.smG α θ
            ≤ (K₂ * α * (Work.Spaces.Gam α θ * ((Real.sin (2 * θ)) ^ 2 + α))) ^ 2
                * Work.FTS.Nonlinear.RadialProd.smG α θ :=
              mul_le_mul_of_nonneg_right hb2i hsmGnn
          _ = (K₂ * α) ^ 2 * (Work.Spaces.Gam α θ * ((Real.sin (2 * θ)) ^ 2 + α)) ^ 2
                * Work.FTS.Nonlinear.RadialProd.smG α θ := by rw [hkey]
      · rw [if_neg h1]
        exact hCEnn
    calc (∑ i ∈ Finset.range (n + 1), if 1 ≤ i then
          (Work.Spaces.DthIter i (fun _ θ' => Work.Spaces.Lop (Work.Spaces.Gam α) θ') 0 θ) ^ 2
            * Work.FTS.Nonlinear.RadialProd.smG α θ else 0)
        ≤ ∑ i ∈ Finset.range (n + 1),
            (K₂ * α) ^ 2 * (Work.Spaces.Gam α θ * ((Real.sin (2 * θ)) ^ 2 + α)) ^ 2
              * Work.FTS.Nonlinear.RadialProd.smG α θ := Finset.sum_le_sum hterm
      _ = ((n : ℝ) + 1) * ((K₂ * α) ^ 2
              * (Work.Spaces.Gam α θ * ((Real.sin (2 * θ)) ^ 2 + α)) ^ 2
              * Work.FTS.Nonlinear.RadialProd.smG α θ) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          push_cast
          ring
  have hn4 : ((n : ℝ) + 1) ≤ 4 := by
    have : (n : ℝ) ≤ 3 := by exact_mod_cast hn
    linarith
  have hCEnn : 0 ≤ (K₂ * α) ^ 2 * (Work.Spaces.Gam α θ * ((Real.sin (2 * θ)) ^ 2 + α)) ^ 2
      * Work.FTS.Nonlinear.RadialProd.smG α θ :=
    mul_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _)) hsmGnn
  have hmix' : (∑ i ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (n + 1),
        if 1 ≤ i ∧ i + j ≤ n then
          (Work.Spaces.mixed j i
              (fun z θ => Work.Spaces.Lop (Work.Spaces.Gam α) θ * radA α f z) z θ
            * Work.Spaces.Wt α z θ) ^ 2
        else 0)
      ≤ rsum n (radA α f) z
        * (((n : ℝ) + 1) * ((K₂ * α) ^ 2
            * (Work.Spaces.Gam α θ * ((Real.sin (2 * θ)) ^ 2 + α)) ^ 2
            * Work.FTS.Nonlinear.RadialProd.smG α θ)) :=
    le_trans hmix (mul_le_mul_of_nonneg_left hMsum hRnn)
  -- ### assembly
  have hHk : Work.Spaces.HkIntegrand α n
      (fun z θ => Work.Spaces.Lop (Work.Spaces.Gam α) θ * radA α f z) z θ
      = (∑ i ∈ Finset.range (n + 1),
          (Work.Spaces.DzIter i
              (fun z θ => Work.Spaces.Lop (Work.Spaces.Gam α) θ * radA α f z) z θ
            * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
        + ∑ i ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (n + 1),
            if 1 ≤ i ∧ i + j ≤ n then
              (Work.Spaces.mixed j i
                  (fun z θ => Work.Spaces.Lop (Work.Spaces.Gam α) θ * radA α f z) z θ
                * Work.Spaces.Wt α z θ) ^ 2
            else 0 := by
    rw [Work.Spaces.HkIntegrand]
  calc Work.Spaces.HkIntegrand α n
        (fun z θ => Work.Spaces.Lop (Work.Spaces.Gam α) θ * radA α f z) z θ
      = (∑ i ∈ Finset.range (n + 1),
          (Work.Spaces.DzIter i
              (fun z θ => Work.Spaces.Lop (Work.Spaces.Gam α) θ * radA α f z) z θ
            * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
        + ∑ i ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (n + 1),
            if 1 ≤ i ∧ i + j ≤ n then
              (Work.Spaces.mixed j i
                  (fun z θ => Work.Spaces.Lop (Work.Spaces.Gam α) θ * radA α f z) z θ
                * Work.Spaces.Wt α z θ) ^ 2
            else 0 := hHk
    _ ≤ (K₁ * α) ^ 2 * Work.FTS.Nonlinear.RadialProd.smE θ * rsum n (radA α f) z
          + rsum n (radA α f) z
            * (((n : ℝ) + 1) * ((K₂ * α) ^ 2
                * (Work.Spaces.Gam α θ * ((Real.sin (2 * θ)) ^ 2 + α)) ^ 2
                * Work.FTS.Nonlinear.RadialProd.smG α θ)) := add_le_add hpure' hmix'
    _ = rsum n (radA α f) z
          * ((K₁ * α) ^ 2 * Work.FTS.Nonlinear.RadialProd.smE θ
            + ((n : ℝ) + 1) * ((K₂ * α) ^ 2
                * (Work.Spaces.Gam α θ * ((Real.sin (2 * θ)) ^ 2 + α)) ^ 2
                * Work.FTS.Nonlinear.RadialProd.smG α θ)) := by ring
    _ ≤ rsum n (radA α f) z
          * ((K₁ * α) ^ 2 * Work.FTS.Nonlinear.RadialProd.smE θ
            + 4 * ((K₂ * α) ^ 2
                * (Work.Spaces.Gam α θ * ((Real.sin (2 * θ)) ^ 2 + α)) ^ 2
                * Work.FTS.Nonlinear.RadialProd.smG α θ)) := by
        refine mul_le_mul_of_nonneg_left (add_le_add le_rfl ?_) hRnn
        exact mul_le_mul_of_nonneg_right hn4 hCEnn
    _ = rsum n (radA α f) z * angF α K₁ K₂ θ := by
        rw [angF]
        ring

theorem E1_angRad_le :
    ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (n : ℕ) (f : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 → n ≤ 3 →
      MeasureTheory.IntegrableOn (fun z => ∑ j ∈ Finset.range (n + 1),
        (Work.Elliptic.DzdIter j (Work.FTS.CoercivityFix.Transfer.radA α f) z) ^ 2
          * (Work.Spaces.w z) ^ 2) Work.Spaces.Iz →
      Work.Spaces.HkSq α n (Work.FTS.CoercivityFix.Transfer.E1 α f)
        ≤ C * α ^ 2 * (∫ z in Work.Spaces.Iz, ∑ j ∈ Finset.range (n + 1),
            (Work.Elliptic.DzdIter j (Work.FTS.CoercivityFix.Transfer.radA α f) z) ^ 2
              * (Work.Spaces.w z) ^ 2) := by
  obtain ⟨K₁, hK₁pos, hK₁⟩ := Lop_iter_LopGam_Gamma_bound
  obtain ⟨K₂, hK₂pos, hK₂⟩ := Lop_iter_LopGam_gauge_bound
  refine ⟨K₁ ^ 2 * 10 ^ 4 + 4 * K₂ ^ 2 * 10 ^ 3 + 1, by positivity, ?_⟩
  intro α n f hα hα1 hn hint
  -- ## the angular data of the profile `D_θΓ = Lop (Gam α)`
  have ha : ∀ θ ∈ Work.Spaces.Iθ, |Work.Spaces.Lop (Work.Spaces.Gam α) θ| ≤ K₁ * α := by
    intro θ hθ
    have h := hK₁ α hα hα1 0 (by norm_num) θ hθ
    have hG := (Work.Spaces.Gam_bounds α θ hα hθ).2
    have hKα : 0 ≤ K₁ * α := mul_nonneg hK₁pos.le hα.le
    calc |Work.Spaces.Lop (Work.Spaces.Gam α) θ|
        = |(Work.Spaces.Lop^[0] (Work.Spaces.Lop (Work.Spaces.Gam α))) θ| := rfl
      _ ≤ K₁ * α * Work.Spaces.Gam α θ := h
      _ ≤ K₁ * α * 1 := by nlinarith [hKα, hG]
      _ = K₁ * α := by ring
  have hb : ∀ i : ℕ, 1 ≤ i → i ≤ 3 → ∀ θ ∈ Work.Spaces.Iθ,
      |Work.Spaces.DthIter i (fun _ θ' => Work.Spaces.Lop (Work.Spaces.Gam α) θ') 0 θ|
        ≤ K₂ * α * (Work.Spaces.Gam α θ * ((Real.sin (2 * θ)) ^ 2 + α)) := by
    intro i hi1 hi3 θ hθ
    have h := hK₂ α hα hα1 i hi1 hi3 θ hθ
    have htl : Work.Spaces.DthIter i (fun _ θ' => Work.Spaces.Lop (Work.Spaces.Gam α) θ') 0 θ
        = (Work.Spaces.Lop^[i] (Work.Spaces.Lop (Work.Spaces.Gam α))) θ := by
      rw [Work.Spaces.DthIter_eq_iterate_Lop]
    calc |Work.Spaces.DthIter i (fun _ θ' => Work.Spaces.Lop (Work.Spaces.Gam α) θ') 0 θ|
        = |(Work.Spaces.Lop^[i] (Work.Spaces.Lop (Work.Spaces.Gam α))) θ| := by rw [htl]
      _ ≤ K₂ * α * Work.Spaces.Gam α θ * ((Real.sin (2 * θ)) ^ 2 + α) := h
      _ = K₂ * α * (Work.Spaces.Gam α θ * ((Real.sin (2 * θ)) ^ 2 + α)) := by ring
  -- ## the angular factor
  have hPHIint : MeasureTheory.IntegrableOn (angF α K₁ K₂) Work.Spaces.Iθ :=
    angF_integrable α hα hα1 K₁ K₂
  have hPHIbd : (∫ θ in Work.Spaces.Iθ, angF α K₁ K₂ θ)
      ≤ α ^ 2 * (K₁ ^ 2 * 10 ^ 4 + 4 * K₂ ^ 2 * 10 ^ 3) :=
    angF_integral_le α hα hα1 K₁ K₂
  have hradsum_int : Integrable (fun z => rsum n (radA α f) z)
      (MeasureTheory.volume.restrict Work.Spaces.Iz) := hint
  -- ## the angular integral, slice by slice
  have hinner : ∀ z ∈ Work.Spaces.Iz,
      (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α n (E1 α f) z θ)
        ≤ rsum n (radA α f) z * (∫ θ in Work.Spaces.Iθ, angF α K₁ K₂ θ) := by
    intro z hz
    have hpt : ∀ θ ∈ Set.Ioo (0 : ℝ) (π / 2),
        Work.Spaces.HkIntegrand α n (E1 α f) z θ
          ≤ rsum n (radA α f) z * angF α K₁ K₂ θ :=
      fun θ hθ => HkIntegrand_E1_le α hα n hn hK₁pos.le hK₂pos.le ha hb f z θ hθ
    have hIoo : Set.Ioo (0 : ℝ) (π / 2) =ᵐ[volume] Work.Spaces.Iθ := by
      rw [show Work.Spaces.Iθ = Set.Icc (0 : ℝ) (π / 2) from rfl]
      exact MeasureTheory.Ioo_ae_eq_Icc
    have hae : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
        Work.Spaces.HkIntegrand α n (E1 α f) z θ
          ≤ rsum n (radA α f) z * angF α K₁ K₂ θ := by
      have h1 : ∀ᵐ θ ∂(MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) (π / 2))),
          Work.Spaces.HkIntegrand α n (E1 α f) z θ
            ≤ rsum n (radA α f) z * angF α K₁ K₂ θ :=
        MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo hpt
      rwa [MeasureTheory.Measure.restrict_congr_set hIoo] at h1
    have h1 := MeasureTheory.integral_mono_of_nonneg
      (μ := MeasureTheory.volume.restrict Work.Spaces.Iθ)
      (f := fun θ => Work.Spaces.HkIntegrand α n (E1 α f) z θ)
      (g := fun θ => rsum n (radA α f) z * angF α K₁ K₂ θ)
      (Filter.Eventually.of_forall fun θ =>
        Work.Spaces.HkIntegrand_nonneg α n (E1 α f) z θ)
      (hPHIint.const_mul (rsum n (radA α f) z))
      hae
    rwa [MeasureTheory.integral_const_mul] at h1
  -- ## the radial integral
  have houter := MeasureTheory.integral_mono_of_nonneg
    (μ := MeasureTheory.volume.restrict Work.Spaces.Iz)
    (f := fun z => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α n (E1 α f) z θ)
    (g := fun z => rsum n (radA α f) z * (∫ θ in Work.Spaces.Iθ, angF α K₁ K₂ θ))
    (Filter.Eventually.of_forall fun z =>
      integral_nonneg fun θ => Work.Spaces.HkIntegrand_nonneg α n (E1 α f) z θ)
    (hradsum_int.mul_const _)
    (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ici hinner)
  rw [MeasureTheory.integral_mul_const] at houter
  -- ## assembly
  have hRnn : 0 ≤ ∫ z in Work.Spaces.Iz, rsum n (radA α f) z :=
    integral_nonneg fun z => rsum_nonneg n (radA α f) z
  rw [Work.Spaces.HkSq]
  refine le_trans houter ?_
  calc (∫ z in Work.Spaces.Iz, rsum n (radA α f) z)
        * (∫ θ in Work.Spaces.Iθ, angF α K₁ K₂ θ)
      ≤ (∫ z in Work.Spaces.Iz, rsum n (radA α f) z)
          * (α ^ 2 * (K₁ ^ 2 * 10 ^ 4 + 4 * K₂ ^ 2 * 10 ^ 3)) :=
        mul_le_mul_of_nonneg_left hPHIbd hRnn
    _ ≤ (K₁ ^ 2 * 10 ^ 4 + 4 * K₂ ^ 2 * 10 ^ 3 + 1) * α ^ 2
          * (∫ z in Work.Spaces.Iz, rsum n (radA α f) z) := by
        rw [show (∫ z in Work.Spaces.Iz, rsum n (radA α f) z)
              * (α ^ 2 * (K₁ ^ 2 * 10 ^ 4 + 4 * K₂ ^ 2 * 10 ^ 3))
            = (K₁ ^ 2 * 10 ^ 4 + 4 * K₂ ^ 2 * 10 ^ 3)
              * (α ^ 2 * (∫ z in Work.Spaces.Iz, rsum n (radA α f) z)) by ring]
        rw [show (K₁ ^ 2 * 10 ^ 4 + 4 * K₂ ^ 2 * 10 ^ 3 + 1) * α ^ 2
              * (∫ z in Work.Spaces.Iz, rsum n (radA α f) z)
            = (K₁ ^ 2 * 10 ^ 4 + 4 * K₂ ^ 2 * 10 ^ 3 + 1)
              * (α ^ 2 * (∫ z in Work.Spaces.Iz, rsum n (radA α f) z)) by ring]
        exact mul_le_mul_of_nonneg_right (by linarith)
          (mul_nonneg (sq_nonneg _) hRnn)

end Work.FTS.CoercivityFix.Transfer.E1Norm
