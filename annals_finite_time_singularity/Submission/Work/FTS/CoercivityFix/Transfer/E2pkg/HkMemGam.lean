/-
# `Transfer/E2pkg/HkMemGam.lean` — the second summand `Γ(θ)·radS α f z` lies in `ℋ^n`

The transfer defect splits as `E2 α f = Ê₂ f + Γ(θ)·radS α f z`
(`Transfer/Profiles.E2_eq`).  The first summand is handled by
`Assembly.E2hat_RegQ`; here we prove the `ℋ^n`-membership (`n ≤ 3`) of the *separated*
second summand `(z,θ) ↦ Γ(θ)·radS α f z`.

The two separation identities `Work.FTS.Nonlinear.Pieces.dzIter_ang_rad` /
`mixed_ang_rad` turn every block of the product into a product of a block of `Γ` and a block of
`radS`:

  `D_z^j(Γ·R) = Γ·D_z^j R`,  `D_z^jD_θ^i(Γ·R) = (D_θ^iΓ)·(D_z^jR)`  (`i ≥ 1`),

and the two squared-weight identities `light_sq_nn`/`heavy_sq_nn` (from
`NonlinRows.AuxAngRad.AngRadWeights`, valid on all of `Iθ`, endpoints included) convert the
weights `w/sin(2θ)^{η/2}` and `Wt α` into `w²·sin(2θ)^{-η}` and `w²·sin(2θ)^{-γ}`.  With
`|Γ| ≤ 1`, `|D_θ^iΓ| ≤ 10^5 Γ` (`LocData.DthIter_Gam_abs_le`, `i ≤ 4`) and
`Γ² sin(2θ)^{-γ} ≤ sin(2θ)^{2α/5-γ}` (`LocData.Gam_le_sin_two_rpow`), the whole integrand is
dominated by

  `4·10^10 · (sin(2θ)^{-η} + sin(2θ)^{2α/5-γ}) · ∑_{j≤n} (D_z^j radS)² w²`,

whose angular factor is integrable on `Iθ` (`Spaces.sin_two_rpow`, both exponents in `(-1,0]`)
and whose radial factor is integrable on `Iz` (`E2pkg.radS_DzdIter_sq_w_sq_integrable`,
`j ≤ n ≤ 3`).  `LocData.HkMem_of_majorant` finishes.

Everything here rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.CoercivityFix.Transfer.E2pkg.RadS
import Submission.Work.FTS.CoercivityFix.Transfer.E2pkg.FinCalc
import Submission.Work.FTS.LocData.DthIter_Gam_abs_le
import Submission.Work.FTS.LocData.Gam_le_sin_two_rpow
import Submission.Work.FTS.LocData.HkMem_of_majorant
import Submission.Work.Spaces.sin_two_rpow
import Submission.Work.Spaces.Gam_bounds
import Submission.Work.FTS.Nonlinear.Pieces.rowsN0Q
import Submission.Work.FTS.NonlinRows.AuxAngRad.AngRadWeights
import Submission.Work.FTS.Nonlinear.RadialProd.radial_prod
import Submission.Work.FTS.CoercivityFix.Transfer.AuxE2.radS_contDiffOn_three
import Submission.Work.FTS.CoercivityFix.Transfer.AuxE2.L12_contDiffOn_four_of_five
import Submission.Work.FTS.CoercivityFix.Transfer.GamSmooth

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.CoercivityFix.Transfer.E2pkg

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-! ## The majorant -/

/-- The angular majorant of the separated summand `Γ(θ)·radS α f z`:
`sin(2θ)^{-η} + sin(2θ)^{2α/5-γ}`.  Its first term is the weight of the `D_z`-slots, its
second is what `Γ(θ)²·sin(2θ)^{-γ}` is bounded by. -/
def angMaj (α : ℝ) (θ : ℝ) : ℝ :=
  Work.FTS.Nonlinear.RadialProd.smE θ
    + (Real.sin (2 * θ)) ^ (2 * α / 5 - Work.Spaces.gam α)

/-- The radial density of the `n`-th level of `radS α f`:
`∑_{j≤n} (D_z^j (radS α f)(z))² w(z)²`. -/
def radMaj (α : ℝ) (f : ℝ → ℝ → ℝ) (n : ℕ) (z : ℝ) : ℝ :=
  ∑ j ∈ Finset.range (n + 1),
    (Work.Elliptic.DzdIter j (radS α f) z) ^ 2 * (Work.Spaces.w z) ^ 2

/-! ## The two separation identities, in the shape used below -/

private lemma dzIter_gam_rad (α : ℝ) (f : ℝ → ℝ → ℝ) (i : ℕ) (z θ : ℝ) :
    Work.Spaces.DzIter i (fun z θ => Work.Spaces.Gam α θ * radS α f z) z θ
      = Work.Spaces.Gam α θ * Work.Elliptic.DzdIter i (radS α f) z :=
  Work.FTS.Nonlinear.Pieces.dzIter_ang_rad _ _ i z θ

private lemma mixed_gam_rad (α : ℝ) (f : ℝ → ℝ → ℝ) (j i : ℕ) (z θ : ℝ) :
    Work.Spaces.mixed j i (fun z θ => Work.Spaces.Gam α θ * radS α f z) z θ
      = Work.Spaces.DthIter i (fun _ (θ' : ℝ) => Work.Spaces.Gam α θ') 0 θ
        * Work.Elliptic.DzdIter j (radS α f) z :=
  Work.FTS.Nonlinear.Pieces.mixed_ang_rad _ _ j i z θ

/-! ## The angular inequality `Γ² sin(2θ)^{-γ} ≤ sin(2θ)^{2α/5-γ}` -/

/-- `(sin(2θ)^{α/5})² = sin(2θ)^{2α/5}` for `0 ≤ sin(2θ)`. -/
private lemma sin_rpow_fifth_sq {θ : ℝ} (hs : 0 ≤ Real.sin (2 * θ)) (α : ℝ) :
    ((Real.sin (2 * θ)) ^ (α / 5)) ^ 2 = (Real.sin (2 * θ)) ^ (2 * α / 5) := by
  rw [← Real.rpow_natCast ((Real.sin (2 * θ)) ^ (α / 5)) 2, ← Real.rpow_mul hs]
  congr 1
  push_cast
  ring

/-- `Γ(θ)² · sin(2θ)^{-γ(α)} ≤ sin(2θ)^{2α/5-γ(α)}` on `Iθ`. -/
private lemma gam_sq_mul_smG_le (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) {θ : ℝ}
    (hθ : θ ∈ Work.Spaces.Iθ) :
    (Work.Spaces.Gam α θ) ^ 2 * Work.FTS.Nonlinear.RadialProd.smG α θ
      ≤ (Real.sin (2 * θ)) ^ (2 * α / 5 - Work.Spaces.gam α) := by
  have hs : 0 ≤ Real.sin (2 * θ) :=
    Work.FTS.Nonlinear.RadialProd.sin_two_nonneg_of_mem_Iθ hθ
  have hGnn : 0 ≤ Work.Spaces.Gam α θ := (Work.Spaces.Gam_bounds α θ hα hθ).1
  have hGle : Work.Spaces.Gam α θ ≤ (Real.sin (2 * θ)) ^ (α / 5) :=
    Work.FTS.LocData.Gam_le_sin_two_rpow α hα hθ
  have hsq : (Work.Spaces.Gam α θ) ^ 2 ≤ (Real.sin (2 * θ)) ^ (2 * α / 5) := by
    have h2 : (Work.Spaces.Gam α θ) ^ 2 ≤ ((Real.sin (2 * θ)) ^ (α / 5)) ^ 2 :=
      sq_le_sq' (by linarith [hGnn, Real.rpow_nonneg hs (α / 5)]) hGle
    rwa [sin_rpow_fifth_sq hs α] at h2
  have hne : 2 * α / 5 + -(Work.Spaces.gam α) ≠ 0 := by
    intro h
    have h1 : Work.Spaces.gam α = 2 * α / 5 := by linarith
    rw [Work.Spaces.gam] at h1
    nlinarith
  rw [show Work.FTS.Nonlinear.RadialProd.smG α θ
      = (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) from rfl]
  calc (Work.Spaces.Gam α θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
      ≤ (Real.sin (2 * θ)) ^ (2 * α / 5) * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) :=
        mul_le_mul_of_nonneg_right hsq (Real.rpow_nonneg hs _)
    _ = (Real.sin (2 * θ)) ^ (2 * α / 5 - Work.Spaces.gam α) := by
        rw [show (2 : ℝ) * α / 5 - Work.Spaces.gam α
              = 2 * α / 5 + -(Work.Spaces.gam α) from by ring,
          Real.rpow_add' (x := Real.sin (2 * θ)) (y := 2 * α / 5)
            (z := -(Work.Spaces.gam α)) hs hne]

/-! ## The pointwise domination -/

/-- **Pointwise domination of the `ℋ^n`-integrand of a separated summand.**  For `n ≤ 3` and
`0 < α ≤ 1`, at every `(z,θ)` in the closed quadrant the integrand of `Γ(θ)·radS α f z` is
bounded by `4·10^10 · angMaj α θ · radMaj α f n z`.  (No hypothesis on `f`: the statement is
purely angular/radial bookkeeping.) -/
theorem HkIntegrand_gam_rad_le (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1)
    {n : ℕ} (hn : n ≤ 3) (f : ℝ → ℝ → ℝ) :
    ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α n
          (fun z θ => Work.Spaces.Gam α θ * radS α f z) z θ
        ≤ 4 * 10 ^ 10 * (angMaj α θ * radMaj α f n z) := by
  intro z hz θ hθ
  have hs : 0 ≤ Real.sin (2 * θ) :=
    Work.FTS.Nonlinear.RadialProd.sin_two_nonneg_of_mem_Iθ hθ
  have hsmEnn : 0 ≤ Work.FTS.Nonlinear.RadialProd.smE θ :=
    Work.FTS.Nonlinear.RadialProd.smE_nonneg hθ
  have hsmGnn : 0 ≤ Work.FTS.Nonlinear.RadialProd.smG α θ :=
    Work.FTS.Nonlinear.RadialProd.smG_nonneg hθ
  have hrmnn : 0 ≤ radMaj α f n z := by
    refine Finset.sum_nonneg fun j hj => mul_nonneg (sq_nonneg _) (sq_nonneg _)
  have hGam2 : (Work.Spaces.Gam α θ) ^ 2 ≤ 1 := by
    have h := (Work.Spaces.Gam_bounds α θ hα hθ).2
    nlinarith [(Work.Spaces.Gam_bounds α θ hα hθ).1]
  -- ### the pure (`D_z`-only) slots
  have hpure : (∑ i ∈ Finset.range (n + 1),
        (Work.Spaces.DzIter i (fun z θ => Work.Spaces.Gam α θ * radS α f z) z θ
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
      ≤ 4 * 10 ^ 10 * (Work.FTS.Nonlinear.RadialProd.smE θ * radMaj α f n z) := by
    have hterm : ∀ i ∈ Finset.range (n + 1),
        (Work.Spaces.DzIter i (fun z θ => Work.Spaces.Gam α θ * radS α f z) z θ
            * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
          = (Work.Spaces.Gam α θ) ^ 2 * Work.FTS.Nonlinear.RadialProd.smE θ
              * ((Work.Elliptic.DzdIter i (radS α f) z) ^ 2 * (Work.Spaces.w z) ^ 2) := by
      intro i _
      rw [dzIter_gam_rad α f i z θ,
        show (Work.Spaces.Gam α θ * Work.Elliptic.DzdIter i (radS α f) z
              * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
            = ((Work.Spaces.Gam α θ * Work.Elliptic.DzdIter i (radS α f) z)
              * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
          from by ring,
        Work.FTS.NonlinRows.AuxAngRad.light_sq_nn _ z θ hs]
      ring
    calc (∑ i ∈ Finset.range (n + 1),
            (Work.Spaces.DzIter i (fun z θ => Work.Spaces.Gam α θ * radS α f z) z θ
              * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
        = (Work.Spaces.Gam α θ) ^ 2 * Work.FTS.Nonlinear.RadialProd.smE θ
            * radMaj α f n z := by
          rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum, radMaj]
      _ ≤ 4 * 10 ^ 10 * (Work.FTS.Nonlinear.RadialProd.smE θ * radMaj α f n z) := by
          have h1 : (Work.Spaces.Gam α θ) ^ 2 * Work.FTS.Nonlinear.RadialProd.smE θ
              * radMaj α f n z
              ≤ Work.FTS.Nonlinear.RadialProd.smE θ * radMaj α f n z := by
            have h2 : (Work.Spaces.Gam α θ) ^ 2
                  * (Work.FTS.Nonlinear.RadialProd.smE θ * radMaj α f n z)
                ≤ 1 * (Work.FTS.Nonlinear.RadialProd.smE θ * radMaj α f n z) :=
              mul_le_mul_of_nonneg_right hGam2 (mul_nonneg hsmEnn hrmnn)
            linarith [h2]
          have h3 : (0 : ℝ) ≤ Work.FTS.Nonlinear.RadialProd.smE θ * radMaj α f n z :=
            mul_nonneg hsmEnn hrmnn
          nlinarith [h1, h3]
  -- ### the mixed slots
  have hmix : (∑ i ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (n + 1),
        if 1 ≤ i ∧ i + j ≤ n then
          (Work.Spaces.mixed j i (fun z θ => Work.Spaces.Gam α θ * radS α f z) z θ
            * Work.Spaces.Wt α z θ) ^ 2
        else 0)
      ≤ 4 * 10 ^ 10
          * ((Real.sin (2 * θ)) ^ (2 * α / 5 - Work.Spaces.gam α) * radMaj α f n z) := by
    have hterm2 : ∀ i ∈ Finset.range (n + 1), ∀ j ∈ Finset.range (n + 1),
        (if 1 ≤ i ∧ i + j ≤ n then
          (Work.Spaces.mixed j i (fun z θ => Work.Spaces.Gam α θ * radS α f z) z θ
            * Work.Spaces.Wt α z θ) ^ 2
        else 0)
        ≤ 10 ^ 10 * (Real.sin (2 * θ)) ^ (2 * α / 5 - Work.Spaces.gam α)
            * ((Work.Elliptic.DzdIter j (radS α f) z) ^ 2 * (Work.Spaces.w z) ^ 2) := by
      intro i hi j hj
      by_cases hc : 1 ≤ i ∧ i + j ≤ n
      · rw [if_pos hc]
        have hi3 : i ≤ 3 := by
          have h1 : i ≤ n := le_trans (Nat.le_add_right i j) hc.2
          omega
        have hGbd : |Work.Spaces.DthIter i (fun _ (θ' : ℝ) => Work.Spaces.Gam α θ') 0 θ|
            ≤ 100000 * Work.Spaces.Gam α θ :=
          Work.FTS.LocData.DthIter_Gam_abs_le i (by omega) α hα hα1 hθ
        have hDth2 : (Work.Spaces.DthIter i (fun _ (θ' : ℝ) => Work.Spaces.Gam α θ') 0 θ) ^ 2
            ≤ 10 ^ 10 * (Work.Spaces.Gam α θ) ^ 2 := by
          have h2 := sq_le_sq' (abs_le.mp hGbd).1 (abs_le.mp hGbd).2
          calc (Work.Spaces.DthIter i (fun _ (θ' : ℝ) => Work.Spaces.Gam α θ') 0 θ) ^ 2
              ≤ (100000 * Work.Spaces.Gam α θ) ^ 2 := h2
            _ = 10 ^ 10 * (Work.Spaces.Gam α θ) ^ 2 := by ring
        have hgam := gam_sq_mul_smG_le α hα hα1 hθ
        rw [mixed_gam_rad α f j i z θ,
          show (Work.Spaces.DthIter i (fun _ (θ' : ℝ) => Work.Spaces.Gam α θ') 0 θ
                * Work.Elliptic.DzdIter j (radS α f) z * Work.Spaces.Wt α z θ) ^ 2
              = ((Work.Spaces.DthIter i (fun _ (θ' : ℝ) => Work.Spaces.Gam α θ') 0 θ
                  * Work.Elliptic.DzdIter j (radS α f) z)
                  * Work.Spaces.Wt α z θ) ^ 2 from by ring,
          Work.FTS.NonlinRows.AuxAngRad.heavy_sq_nn α _ z θ hs]
        have hAY : (Work.Spaces.DthIter i (fun _ (θ' : ℝ) => Work.Spaces.Gam α θ') 0 θ) ^ 2
              * Work.FTS.Nonlinear.RadialProd.smG α θ
            ≤ 10 ^ 10 * (Real.sin (2 * θ)) ^ (2 * α / 5 - Work.Spaces.gam α) := by
          have h1 : (Work.Spaces.DthIter i (fun _ (θ' : ℝ) => Work.Spaces.Gam α θ') 0 θ) ^ 2
                * Work.FTS.Nonlinear.RadialProd.smG α θ
              ≤ (10 ^ 10 * (Work.Spaces.Gam α θ) ^ 2)
                  * Work.FTS.Nonlinear.RadialProd.smG α θ :=
            mul_le_mul_of_nonneg_right hDth2 hsmGnn
          have h2 : (10 ^ 10 * (Work.Spaces.Gam α θ) ^ 2)
                * Work.FTS.Nonlinear.RadialProd.smG α θ
              = 10 ^ 10 * ((Work.Spaces.Gam α θ) ^ 2
                  * Work.FTS.Nonlinear.RadialProd.smG α θ) := by ring
          rw [h2] at h1
          exact h1.trans (mul_le_mul_of_nonneg_left hgam (by norm_num))
        have hcw : (0 : ℝ)
            ≤ (Work.Elliptic.DzdIter j (radS α f) z) ^ 2 * (Work.Spaces.w z) ^ 2 :=
          mul_nonneg (sq_nonneg _) (sq_nonneg _)
        rw [show (Work.Spaces.DthIter i (fun _ (θ' : ℝ) => Work.Spaces.Gam α θ') 0 θ
                * Work.Elliptic.DzdIter j (radS α f) z) ^ 2
              * (Work.Spaces.w z) ^ 2 * Work.FTS.Nonlinear.RadialProd.smG α θ
            = ((Work.Elliptic.DzdIter j (radS α f) z) ^ 2 * (Work.Spaces.w z) ^ 2)
              * ((Work.Spaces.DthIter i (fun _ (θ' : ℝ) => Work.Spaces.Gam α θ') 0 θ) ^ 2
                * Work.FTS.Nonlinear.RadialProd.smG α θ) from by ring]
        calc ((Work.Elliptic.DzdIter j (radS α f) z) ^ 2 * (Work.Spaces.w z) ^ 2)
              * ((Work.Spaces.DthIter i (fun _ (θ' : ℝ) => Work.Spaces.Gam α θ') 0 θ) ^ 2
                * Work.FTS.Nonlinear.RadialProd.smG α θ)
            ≤ ((Work.Elliptic.DzdIter j (radS α f) z) ^ 2 * (Work.Spaces.w z) ^ 2)
              * (10 ^ 10 * (Real.sin (2 * θ)) ^ (2 * α / 5 - Work.Spaces.gam α)) :=
            mul_le_mul_of_nonneg_left hAY hcw
          _ = 10 ^ 10 * (Real.sin (2 * θ)) ^ (2 * α / 5 - Work.Spaces.gam α)
              * ((Work.Elliptic.DzdIter j (radS α f) z) ^ 2 * (Work.Spaces.w z) ^ 2) := by
            ring
      · rw [if_neg hc]
        exact mul_nonneg (mul_nonneg (by norm_num) (Real.rpow_nonneg hs _))
          (mul_nonneg (sq_nonneg _) (sq_nonneg _))
    have hsum2 : (∑ j ∈ Finset.range (n + 1),
        (10 ^ 10 * (Real.sin (2 * θ)) ^ (2 * α / 5 - Work.Spaces.gam α)
            * ((Work.Elliptic.DzdIter j (radS α f) z) ^ 2 * (Work.Spaces.w z) ^ 2)))
        = 10 ^ 10 * (Real.sin (2 * θ)) ^ (2 * α / 5 - Work.Spaces.gam α) * radMaj α f n z := by
      rw [← Finset.mul_sum, radMaj]
    calc (∑ i ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (n + 1),
          if 1 ≤ i ∧ i + j ≤ n then
            (Work.Spaces.mixed j i (fun z θ => Work.Spaces.Gam α θ * radS α f z) z θ
              * Work.Spaces.Wt α z θ) ^ 2
          else 0)
        ≤ ∑ i ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (n + 1),
            10 ^ 10 * (Real.sin (2 * θ)) ^ (2 * α / 5 - Work.Spaces.gam α)
              * ((Work.Elliptic.DzdIter j (radS α f) z) ^ 2 * (Work.Spaces.w z) ^ 2) :=
          Finset.sum_le_sum fun i hi => Finset.sum_le_sum fun j hj => hterm2 i hi j hj
      _ = ((n + 1 : ℕ) : ℝ)
            * (10 ^ 10 * (Real.sin (2 * θ)) ^ (2 * α / 5 - Work.Spaces.gam α)
              * radMaj α f n z) := by
          rw [Finset.sum_const, hsum2, Finset.card_range, nsmul_eq_mul]
      _ ≤ 4 * 10 ^ 10
            * ((Real.sin (2 * θ)) ^ (2 * α / 5 - Work.Spaces.gam α) * radMaj α f n z) := by
          have hS : (0 : ℝ)
              ≤ 10 ^ 10 * (Real.sin (2 * θ)) ^ (2 * α / 5 - Work.Spaces.gam α)
                * radMaj α f n z :=
            mul_nonneg (mul_nonneg (by norm_num) (Real.rpow_nonneg hs _)) hrmnn
          have hn4 : ((n + 1 : ℕ) : ℝ) ≤ 4 := by
            have : n + 1 ≤ 4 := by omega
            exact_mod_cast this
          have h1 := mul_le_mul_of_nonneg_right hn4 hS
          linarith [h1]
  -- ### assembly
  rw [Work.Spaces.HkIntegrand]
  have hsum := add_le_add hpure hmix
  have hang : (4 : ℝ) * 10 ^ 10
        * (Work.FTS.Nonlinear.RadialProd.smE θ * radMaj α f n z)
      + 4 * 10 ^ 10
        * ((Real.sin (2 * θ)) ^ (2 * α / 5 - Work.Spaces.gam α) * radMaj α f n z)
      = 4 * 10 ^ 10 * (angMaj α θ * radMaj α f n z) := by
    rw [angMaj]; ring
  linarith [hsum, hang]

/-! ## `ℋ^n`-membership of the separated summand -/

private lemma integrableOn_angMaj (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) :
    IntegrableOn (fun θ : ℝ => angMaj α θ) Work.Spaces.Iθ := by
  have h1 : IntegrableOn (fun θ : ℝ => (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
      Work.Spaces.Iθ :=
    (Work.Spaces.sin_two_rpow (-(Work.Spaces.eta))
      (by rw [Work.Spaces.eta]; norm_num)
      (by rw [Work.Spaces.eta]; norm_num)).1
  have h2 : IntegrableOn (fun θ : ℝ => (Real.sin (2 * θ)) ^ (2 * α / 5 - Work.Spaces.gam α))
      Work.Spaces.Iθ := by
    refine (Work.Spaces.sin_two_rpow (2 * α / 5 - Work.Spaces.gam α) ?_ ?_).1
    · rw [Work.Spaces.gam]; linarith
    · rw [Work.Spaces.gam]; linarith
  refine (h1.add h2).congr_fun (fun θ _ => ?_) measurableSet_Icc
  simp only [Pi.add_apply, angMaj, Work.FTS.Nonlinear.RadialProd.smE]

private lemma integrableOn_radMaj (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1)
    {f : ℝ → ℝ → ℝ} (hf : Work.FTS.Nonlin.CoerAdm α f) {n : ℕ} (hn : n ≤ 3) :
    IntegrableOn (fun z : ℝ => radMaj α f n z) Work.Spaces.Iz := by
  refine MeasureTheory.integrable_finsetSum _ fun j hj => ?_
  have hjn : j ≤ 3 := by
    have := Finset.mem_range.mp hj
    omega
  exact radS_DzdIter_sq_w_sq_integrable α hα hα1 hf j hjn

/-- **`C^n`-regularity of the separated summand `Γ(θ)·radS α f z` on the open quadrant**,
for `CoerAdm α f` and `n ≤ 3`. -/
theorem contDiffOn_uncurry_gam_rad (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) {f : ℝ → ℝ → ℝ}
    (hf : Work.FTS.Nonlin.CoerAdm α f) {n : ℕ} (hn : n ≤ 3) :
    ContDiffOn ℝ n (Function.uncurry (fun z θ => Work.Spaces.Gam α θ * radS α f z)) Qd := by
  have hA : ContDiffOn ℝ 4 (fun z : ℝ => Work.Coercivity.L12f f z) (Set.Ioi 0) :=
    Work.FTS.CoercivityFix.Transfer.AuxE2.L12_contDiffOn_four_of_five α hα hα1
      hf.reg.1 hf.reg.2.1 hf.l12
  have hR : ContDiffOn ℝ 3 (fun z : ℝ => radS α f z) (Set.Ioi 0) :=
    Work.FTS.CoercivityFix.Transfer.AuxE2.radS_contDiffOn_three α hα hα1 hA
  have hR' : ContDiffOn ℝ n (fun p : ℝ × ℝ => radS α f p.1) Qd :=
    (hR.comp contDiffOn_fst (fun p hp => hp.1)).of_le (by exact_mod_cast hn)
  have hG : ContDiffOn ℝ n (fun p : ℝ × ℝ => Work.Spaces.Gam α p.2) Qd :=
    Work.FTS.CoercivityFix.Transfer.contDiffOn_Gam_Qd α n
  have hfun : Function.uncurry (fun z θ => Work.Spaces.Gam α θ * radS α f z)
      = fun p : ℝ × ℝ => Work.Spaces.Gam α p.2 * radS α f p.1 := rfl
  rw [hfun]
  exact hG.mul hR'

/-- **`Γ(θ)·radS α f z ∈ ℋ^n` for `CoerAdm α f` and `n ≤ 3`.** -/
theorem HkMem_gam_rad (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) {f : ℝ → ℝ → ℝ}
    (hf : Work.FTS.Nonlin.CoerAdm α f) {n : ℕ} (hn : n ≤ 3) :
    Work.Spaces.HkMem α n (fun z θ => Work.Spaces.Gam α θ * radS α f z) := by
  have hsm := contDiffOn_uncurry_gam_rad α hα hα1 hf hn
  have hcont : ContinuousOn
      (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α n
        (fun z θ => Work.Spaces.Gam α θ * radS α f z) p.1 p.2) Qd :=
    continuousOn_HkIntegrand_of_blocksCont (blocksCont_of_contDiffOn hsm) α
  have hslice : ∀ z ∈ Work.Spaces.Iz,
      IntegrableOn (fun θ : ℝ => 4 * 10 ^ 10 * (angMaj α θ * radMaj α f n z))
        Work.Spaces.Iθ := by
    intro z hz
    have h := MeasureTheory.Integrable.mul_const (integrableOn_angMaj α hα hα1)
      (radMaj α f n z)
    exact MeasureTheory.Integrable.const_mul h (4 * 10 ^ 10)
  have hz : IntegrableOn (fun z : ℝ => ∫ θ in Work.Spaces.Iθ,
      4 * 10 ^ 10 * (angMaj α θ * radMaj α f n z)) Work.Spaces.Iz := by
    have hconst : IntegrableOn (fun z : ℝ =>
        (4 * 10 ^ 10 * (∫ θ in Work.Spaces.Iθ, angMaj α θ)) * radMaj α f n z)
        Work.Spaces.Iz :=
      MeasureTheory.Integrable.const_mul (integrableOn_radMaj α hα hα1 hf hn) _
    refine MeasureTheory.IntegrableOn.congr_fun hconst (fun z hz => ?_) measurableSet_Ici
    have h1 : (∫ θ in Work.Spaces.Iθ, 4 * 10 ^ 10 * (angMaj α θ * radMaj α f n z))
        = 4 * 10 ^ 10 * (∫ θ in Work.Spaces.Iθ, angMaj α θ * radMaj α f n z) := by
      rw [MeasureTheory.integral_const_mul]
    have h2 : (∫ θ in Work.Spaces.Iθ, angMaj α θ * radMaj α f n z)
        = (∫ θ in Work.Spaces.Iθ, angMaj α θ) * radMaj α f n z :=
      MeasureTheory.integral_mul_const _ _
    rw [h1, h2]
    ring
  refine Work.FTS.LocData.HkMem_of_majorant α n hcont hslice hz
    (fun z hz θ hθ => HkIntegrand_gam_rad_le α hα hα1 hn f z hz θ hθ)

end Work.FTS.CoercivityFix.Transfer.E2pkg
