import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.NonlinRows.Defs
import Submission.Work.FTS.OpenPkg.Defs
import Submission.Work.FTS.OpenPkg.Basic
import Submission.Work.FTS.Nonlinear.Pieces.Basic
import Submission.Work.FTS.OpenPkg.Good
import Submission.Work.Construction.GammaTermAux
import Submission.Work.Construction.H4N_GammaTerm_le
import Submission.Work.Construction.H4N_GammaTerm_rho_bound
import Submission.Work.Construction.H4N_GammaTerm_Lop_bound
import Submission.Work.FTS.LocData.HkMem_of_majorant
import Submission.Work.FTS.EllipticEst.Cert.GbarSin.HkMem_congr_Q0
import Submission.Work.Elliptic.WtoH_IntZ
import Submission.Work.Spaces.sin_two_rpow

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.NonlinRows

open scoped Real Topology
open MeasureTheory Set Filter
open Work.Construction

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

/-!
# Row 1 of the primed §8 table: the `F_*`-quadratic block `N₀₁ + N₀₂`

`N0fix α = N₀₁ + N₀₂` is *unconditional*: it involves only `F_*`, never the data `g, Φs, Φg`.
On the open quadrant it collapses to the separable datum

  `F(z,θ) = Kfac α · rhoR z · psiA α θ`,
  `Kfac α = 8α²/c(α)`,  `rhoR z = z²/(1+z)⁴`,  `psiA α θ = c2m(θ)·Γ(α,θ)`

(`Work.Construction.N0_first_two_eq'`), and the two conjuncts of the row are

* the `ℋ⁴`-honesty `HkMem α 4 (N0fix α)`: the `ℋ⁴`-integrand of `F` is dominated by the
  separable majorant `Kfac α²·(M/(1+z)²)²·gammaAngMaj α D θ`, where `M` and `D` price the radial jets
  of `rhoR` (`Work.Construction.H4N_GammaTerm_rho_bound`) and the angular jets of `psiA`
  (`Work.Construction.H4N_GammaTerm_Lop_bound`); the majorant is integrable because
  `sin(2θ)^{−η}`, `sin(2θ)^{2α/3−γ}` are integrable on `Iθ` (`Work.Spaces.sin_two_rpow`) and
  `(1+z)^{−4}` is integrable on `Iz` (`Work.Elliptic.WtoH_IntZ`), so
  `Work.FTS.LocData.HkMem_of_majorant` applies; the transfer from `F` to `N0fix α` is the
  a.e.-congruence on the open quadrant (`Work.Construction.N0_first_two_eq'` via
  `HkMem_congr_Q0`);
* the norm bound `Xn α (N0fix α) ≤ K·α²`, which is `RowsN0Aux.N0fix_bound` verbatim.

Neither conjunct uses `N4Norm'`, `N4Extra'` or the data `g, Φs, Φg`: the constant `K` is the one
of `RowsN0Aux.N0fix_bound`.

The proof of the pointwise domination is the estimate `hpt` of
`Work.Construction.H4N_GammaTerm_le_of_cores`, re-exposed here as the standalone lemma
`HkIntegrand_sep_le` (with the two cores as hypotheses, so that the constants `M`, `D` are the
existential ones of `H4N_GammaTerm_rho_bound` / `H4N_GammaTerm_Lop_bound`).
-/

/-- The angular majorant of the separable datum `F = Kfac α · rhoR · psiA α`: the two angular
weights of the paper's `ℋ⁴`-integrand, with the angular jet constant `D`. -/
noncomputable def gammaAngMaj (α D θ : ℝ) : ℝ :=
  (20 + 50 * D ^ 2) * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
    + 50 * D ^ 2 * α ^ 2 * (Real.sin (2 * θ)) ^ (2 * α / 3 - Work.Spaces.gam α)

/-- **`N0fix α` is the separable datum `Kfac α · rhoR · psiA α` on the open quadrant**
(`Work.Construction.N0_first_two_eq'`). -/
private theorem N0fix_eq_sep (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) :
    ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Work.FTS.Nonlin.N0fix α z θ
        = Work.Construction.Kfac α * Work.Construction.rhoR z * Work.Construction.psiA α θ := by
  intro z θ hz hθ hθ2
  rw [Work.FTS.Nonlin.N0fix]
  simp only [Work.Construction.N01, Work.Construction.N02]
  rw [show (3 / (2 * α)) * Work.Construction.s2 θ
          * Work.Construction.L12 (Work.Construction.Fstar α) z
          * Work.Spaces.pth (Work.Construction.Fstar α) z θ
        + -Work.Construction.c2m θ * Work.Construction.L12 (Work.Construction.Fstar α) z
          * Work.Spaces.Dz (Work.Construction.Fstar α) z θ
      = (3 / (2 * α)) * Work.Construction.s2 θ
          * Work.Construction.L12 (Work.Construction.Fstar α) z
          * Work.Spaces.pth (Work.Construction.Fstar α) z θ
        - Work.Construction.c2m θ * Work.Construction.L12 (Work.Construction.Fstar α) z
          * Work.Spaces.Dz (Work.Construction.Fstar α) z θ from by ring]
  rw [Work.Construction.N0_first_two_eq' hα hα1 hz.le ⟨hθ.le, hθ2.le⟩]
  simp only [Work.Construction.Kfac, Work.Construction.rhoR, Work.Construction.psiA]
  rw [div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv, mul_inv_rev]
  ring

/-- `F` is `C⁴` on the open quadrant: the product of the smooth radial factor
`Kfac α·rhoR` (a rational function whose only pole is at `z = -1`) and the smooth angular
factor `psiA α = c2m·Γ` (`Γ = (sinθcos²θ)^{α/3}` is smooth on the quadrant). -/
private theorem contDiffOn_uncurry_sep (α : ℝ) :
    ContDiffOn ℝ (4 : ℕ)
      (Function.uncurry (Work.Construction.sepF
        (fun z => Work.Construction.Kfac α * Work.Construction.rhoR z)
        (Work.Construction.psiA α))) Work.FTS.OpenPkg.Q0 := by
  have hrad : ContDiffOn ℝ (4 : ℕ)
      (fun p : ℝ × ℝ => Work.Construction.Kfac α * Work.Construction.rhoR p.1)
      Work.FTS.OpenPkg.Q0 := by
    have h1 : ContDiffOn ℝ (4 : ℕ) (fun p : ℝ × ℝ => p.1 ^ 2)
        Work.FTS.OpenPkg.Q0 := contDiffOn_fst.pow 2
    have h2 : ContDiffOn ℝ (4 : ℕ) (fun p : ℝ × ℝ => (1 + p.1) ^ 4)
        Work.FTS.OpenPkg.Q0 := (contDiffOn_const.add contDiffOn_fst).pow 4
    have h3 : ContDiffOn ℝ (4 : ℕ) (fun p : ℝ × ℝ => p.1 ^ 2 / (1 + p.1) ^ 4)
        Work.FTS.OpenPkg.Q0 :=
      h1.div h2 (fun p hp => pow_ne_zero 4 (ne_of_gt (by
        have hmem : (0 : ℝ) < p.1 := by
          rw [Work.FTS.OpenPkg.Q0] at hp; exact hp.1
        linarith)))
    have h4 : ContDiffOn ℝ (4 : ℕ) (fun p : ℝ × ℝ => Work.Construction.rhoR p.1)
        Work.FTS.OpenPkg.Q0 := by
      simpa only [Work.Construction.rhoR] using h3
    exact contDiffOn_const.mul h4
  have hang : ContDiffOn ℝ (4 : ℕ) (fun p : ℝ × ℝ => Work.Construction.psiA α p.2)
      Work.FTS.OpenPkg.Q0 := by
    have hc2m : ContDiffOn ℝ (4 : ℕ) (fun p : ℝ × ℝ => Work.Construction.c2m p.2)
        Work.FTS.OpenPkg.Q0 := by
      have h1 : ContDiffOn ℝ (4 : ℕ) (fun p : ℝ × ℝ => Real.cos (2 * p.2))
          Work.FTS.OpenPkg.Q0 :=
        (((Real.contDiff_cos.comp (contDiff_const.mul contDiff_snd)).contDiffOn).of_le le_top)
      have h2 : ContDiffOn ℝ (4 : ℕ) (fun p : ℝ × ℝ => Real.sin p.2 ^ 2)
          Work.FTS.OpenPkg.Q0 :=
        ((((Real.contDiff_sin.comp contDiff_snd).pow 2).contDiffOn).of_le le_top)
      simpa only [Work.Construction.c2m] using h1.sub h2
    have hGam : ContDiffOn ℝ (4 : ℕ) (fun p : ℝ × ℝ => Work.Spaces.Gam α p.2)
        Work.FTS.OpenPkg.Q0 := Work.FTS.OpenPkg.contDiffOn_Gam_Q0 α 4
    exact hc2m.mul hGam
  refine (hrad.mul hang).congr ?_
  intro p _
  rfl

/-- `z ↦ (1+z)^{-4}` is integrable on `Iz` (the bound `(1+z)^{-2} ≤ 1` on `Iz` and
`Work.Elliptic.WtoH_IntZ`). -/
private theorem integrableOn_inv_one_add_pow_four :
    IntegrableOn (fun z : ℝ => (1 / (1 + z) ^ 2) ^ 2) Work.Spaces.Iz := by
  refine Work.Elliptic.WtoH_IntZ.1.mono' ?_ ?_
  · exact (by fun_prop : Measurable fun z : ℝ => (1 / (1 + z) ^ 2) ^ 2).aestronglyMeasurable
  · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ici] with z hz
    have hz0 : (0 : ℝ) ≤ z := hz
    have h1 : (0 : ℝ) ≤ 1 / (1 + z) ^ 2 := by positivity
    have h2 : 1 / (1 + z) ^ 2 ≤ 1 := by
      rw [div_le_one (by positivity)]
      nlinarith
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    nlinarith [h1, h2]

/-- The angular majorant `gammaAngMaj α D` is integrable on `Iθ`. -/
private theorem integrableOn_gammaAngMaj (α D : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) :
    IntegrableOn (gammaAngMaj α D) Work.Spaces.Iθ := by
  have hη1 : -1 < -(Work.Spaces.eta) := by
    have := Work.Spaces.eta_lt_one; linarith
  have hη2 : -(Work.Spaces.eta) ≤ 0 := by
    have := Work.Spaces.eta_pos; linarith
  have hg1 : -1 < 2 * α / 3 - Work.Spaces.gam α := by
    rw [Work.Spaces.gam]; linarith
  have hg2 : 2 * α / 3 - Work.Spaces.gam α ≤ 0 := by
    rw [Work.Spaces.gam]; linarith
  have hunfold : gammaAngMaj α D = fun θ => (20 + 50 * D ^ 2) * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
      + 50 * D ^ 2 * α ^ 2 * (Real.sin (2 * θ)) ^ (2 * α / 3 - Work.Spaces.gam α) := rfl
  rw [hunfold]
  exact ((Work.Spaces.sin_two_rpow _ hη1 hη2).1.const_mul _).add
    ((Work.Spaces.sin_two_rpow _ hg1 hg2).1.const_mul _)

/-- **The pointwise domination of the `ℋ⁴`-integrand of the separable `Γ`-term.**  The analytic
core of row 1: given the radial jet bound `hMr` (priced by
`Work.Construction.H4N_GammaTerm_rho_bound`) and the angular jet bound `hDl` (priced by
`Work.Construction.H4N_GammaTerm_Lop_bound`), the `ℋ⁴`-integrand of
`F = sepF (Kfac α·rhoR) (psiA α)` is dominated by the separable majorant
`(Kfac α)²·(M/(1+z)²)²·gammaAngMaj α D θ`.

This is the estimate `hpt` of `Work.Construction.H4N_GammaTerm_le_of_cores`, re-exposed as a
standalone lemma with the two cores as hypotheses. -/
theorem HkIntegrand_sep_le (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) {M D : ℝ}
    (hM : 0 < M) (hD : 0 < D)
    (hMr : ∀ j : ℕ, j ≤ 4 → ∀ z : ℝ, 0 ≤ z →
      |(Work.Spaces.Zop^[j] Work.Construction.rhoR) z * Work.Spaces.w z|
        ≤ M / (1 + z) ^ 2)
    (hDl : ∀ i : ℕ, 1 ≤ i → i ≤ 4 → ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      |(Work.Spaces.Lop^[i] (Work.Construction.psiA α)) θ|
        ≤ D * Work.Spaces.Gam α θ * (Real.sin (2 * θ) ^ 2 + α)) :
    ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α 4
          (Work.Construction.sepF (fun z => Work.Construction.Kfac α * Work.Construction.rhoR z)
            (Work.Construction.psiA α)) z θ
        ≤ (Work.Construction.Kfac α) ^ 2 * (M / (1 + z) ^ 2) ^ 2 * gammaAngMaj α D θ := by
  set Kf : ℝ := Work.Construction.Kfac α with hKfdef
  have hDnn : 0 ≤ D := hD.le
  set F : ℝ → ℝ → ℝ := Work.Construction.sepF (fun z => Kf * Work.Construction.rhoR z)
    (Work.Construction.psiA α) with hFdef
  have hFsep : F = Work.Construction.sepF (fun z => Kf * Work.Construction.rhoR z)
      (Work.Construction.psiA α) := hFdef
  set Big : ℝ → ℝ := fun θ => (20 + 50 * D ^ 2) * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
      + 50 * D ^ 2 * α ^ 2 * (Real.sin (2 * θ)) ^ (2 * α / 3 - Work.Spaces.gam α) with hBigdef
  -- pointwise bound on the integrand
  have hpt : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α 4 F z θ
        ≤ Kf ^ 2 * (M / (1 + z) ^ 2) ^ 2 * Big θ := by
    intro z hz θ hθ
    have hs0 : 0 ≤ Real.sin (2 * θ) := Work.Construction.sin_two_nonneg_of_mem_Iθ hθ
    have h1z : 0 < 1 + z := by have hz0 : (0:ℝ) ≤ z := hz; linarith
    rcases em (θ ∈ Set.Ioo 0 (π / 2)) with hθi | hθi
    · -- interior: use the two cores termwise
      have hbnd : ∀ j : ℕ, j ≤ 4 →
          ((Work.Spaces.Zop^[j] Work.Construction.rhoR) z * Work.Spaces.w z) ^ 2 ≤ (M / (1 + z) ^ 2) ^ 2 := by
        intro j hj
        have hb := hMr j hj z hz
        rw [sq_le_sq, abs_of_nonneg (by positivity : (0:ℝ) ≤ M / (1 + z) ^ 2)]
        exact hb
      have hψ2 : (Work.Construction.psiA α θ) ^ 2 ≤ 4 := by
        have h := mul_self_le_mul_self (abs_nonneg (Work.Construction.psiA α θ)) (Work.Construction.psiA_abs_le_two hα hθ)
        have h2 := sq_abs (Work.Construction.psiA α θ)
        nlinarith [h, h2]
      have hpure : ∀ i : ℕ, i ≤ 4 →
          (Work.Spaces.DzIter i F z θ
              * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
            ≤ Kf ^ 2 * (M / (1 + z) ^ 2) ^ 2
              * (4 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) := by
        intro i hi
        have hsep : Work.Spaces.DzIter i F z θ
            = Kf * (Work.Spaces.Zop^[i] Work.Construction.rhoR) z * Work.Construction.psiA α θ := by
          rw [hFsep, Work.Construction.sepF_DzIter, Work.Construction.Zop_iter_const_mul, sepF]
        have hsq := hbnd i hi
        have hψs : (Kf * Work.Construction.psiA α θ) ^ 2 ≤ Kf ^ 2 * 4 := by
          rw [mul_pow]
          exact mul_le_mul_of_nonneg_left hψ2 (sq_nonneg Kf)
        calc (Work.Spaces.DzIter i F z θ
              * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
            = ((Work.Spaces.Zop^[i] Work.Construction.rhoR) z * Work.Spaces.w z) ^ 2
                * (Kf * Work.Construction.psiA α θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) := by
              rw [hsep]
              rw [Work.Elliptic.sq_mul_div_sin (z := z) (θ := θ)
                (a := Kf * (Work.Spaces.Zop^[i] Work.Construction.rhoR) z * Work.Construction.psiA α θ) hθ]
              ring
          _ ≤ (M / (1 + z) ^ 2) ^ 2 * (Kf ^ 2 * 4)
                * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) :=
              mul_le_mul_of_nonneg_right (mul_le_mul hsq hψs (sq_nonneg _) (sq_nonneg _))
                (Real.rpow_nonneg hs0 _)
          _ = Kf ^ 2 * (M / (1 + z) ^ 2) ^ 2
                * (4 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) := by ring
      have hmixed : ∀ i j : ℕ, 1 ≤ i → i + j ≤ 4 →
          (Work.Spaces.mixed j i F z θ * Work.Spaces.Wt α z θ) ^ 2
            ≤ Kf ^ 2 * (M / (1 + z) ^ 2) ^ 2
              * (2 * D ^ 2 * ((Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
                  + α ^ 2 * (Real.sin (2 * θ)) ^ (2 * α / 3 - Work.Spaces.gam α))) := by
        intro i j hi hij
        have hsep : Work.Spaces.mixed j i F z θ
            = Kf * (Work.Spaces.Zop^[j] Work.Construction.rhoR) z * (Work.Spaces.Lop^[i] (Work.Construction.psiA α)) θ := by
          rw [hFsep, Work.Construction.sepF_mixed, Work.Construction.Zop_iter_const_mul, sepF]
        have hsq := hbnd j (by omega)
        have hcore := hDl i hi (by omega) θ hθi
        have hang := Work.Construction.mixed_angle_le hα hα1 hDnn hθ hcore
        calc (Work.Spaces.mixed j i F z θ * Work.Spaces.Wt α z θ) ^ 2
            = Kf ^ 2 * ((Work.Spaces.Zop^[j] Work.Construction.rhoR) z * Work.Spaces.w z) ^ 2
                * (((Work.Spaces.Lop^[i] (Work.Construction.psiA α)) θ) ^ 2
                    * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) := by
              rw [hsep, mul_pow, Work.Spaces.bt_Wt_sq α z θ hα hθ]
              ring
          _ ≤ Kf ^ 2 * (M / (1 + z) ^ 2) ^ 2
                * (2 * D ^ 2 * ((Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
                    + α ^ 2 * (Real.sin (2 * θ)) ^ (2 * α / 3 - Work.Spaces.gam α))) :=
              mul_le_mul (mul_le_mul_of_nonneg_left hsq (sq_nonneg Kf)) hang
                (by positivity) (by positivity)
      rw [Work.Spaces.HkIntegrand]
      have hZsum : (∑ i ∈ Finset.range (4 + 1),
            (Work.Spaces.DzIter i F z θ
              * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
          ≤ Kf ^ 2 * (M / (1 + z) ^ 2) ^ 2
              * (20 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) := by
        calc ∑ i ∈ Finset.range (4 + 1),
              (Work.Spaces.DzIter i F z θ
                * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
            ≤ ∑ _i ∈ Finset.range (4 + 1),
                (Kf ^ 2 * (M / (1 + z) ^ 2) ^ 2
                  * (4 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))) :=
              Finset.sum_le_sum fun i hi =>
                hpure i (Nat.le_of_lt_succ (Finset.mem_range.mp hi))
          _ = 5 * (Kf ^ 2 * (M / (1 + z) ^ 2) ^ 2
                  * (4 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))) := by
              rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
              norm_num
          _ = Kf ^ 2 * (M / (1 + z) ^ 2) ^ 2
                  * (20 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) := by ring
      have hMsum : (∑ i ∈ Finset.range (4 + 1), ∑ j ∈ Finset.range (4 + 1),
            (if 1 ≤ i ∧ i + j ≤ 4 then
              (Work.Spaces.mixed j i F z θ * Work.Spaces.Wt α z θ) ^ 2 else 0))
          ≤ Kf ^ 2 * (M / (1 + z) ^ 2) ^ 2
              * (50 * D ^ 2 * ((Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
                  + α ^ 2 * (Real.sin (2 * θ)) ^ (2 * α / 3 - Work.Spaces.gam α))) := by
        set Y : ℝ := Kf ^ 2 * (M / (1 + z) ^ 2) ^ 2
            * (2 * D ^ 2 * ((Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
                + α ^ 2 * (Real.sin (2 * θ)) ^ (2 * α / 3 - Work.Spaces.gam α))) with hYdef
        have hYnn : 0 ≤ Y := by rw [hYdef]; positivity
        calc ∑ i ∈ Finset.range (4 + 1), ∑ j ∈ Finset.range (4 + 1),
              (if 1 ≤ i ∧ i + j ≤ 4 then
                (Work.Spaces.mixed j i F z θ * Work.Spaces.Wt α z θ) ^ 2 else 0)
            ≤ ∑ _i ∈ Finset.range (4 + 1), ∑ _j ∈ Finset.range (4 + 1), Y :=
              Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => by
                by_cases hc : 1 ≤ i ∧ i + j ≤ 4
                · rw [if_pos hc]; exact hmixed i j hc.1 hc.2
                · rw [if_neg hc]; exact hYnn
          _ = 25 * Y := by
              rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul,
                Finset.sum_const, Finset.card_range, nsmul_eq_mul]
              ring
          _ = Kf ^ 2 * (M / (1 + z) ^ 2) ^ 2
              * (50 * D ^ 2 * ((Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
                  + α ^ 2 * (Real.sin (2 * θ)) ^ (2 * α / 3 - Work.Spaces.gam α))) := by
              rw [hYdef]; ring
      calc ∑ i ∈ Finset.range (4 + 1),
              (Work.Spaces.DzIter i F z θ
                * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
            + ∑ i ∈ Finset.range (4 + 1), ∑ j ∈ Finset.range (4 + 1),
              (if 1 ≤ i ∧ i + j ≤ 4 then
                (Work.Spaces.mixed j i F z θ * Work.Spaces.Wt α z θ) ^ 2 else 0)
          ≤ Kf ^ 2 * (M / (1 + z) ^ 2) ^ 2
              * (20 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
            + Kf ^ 2 * (M / (1 + z) ^ 2) ^ 2
              * (50 * D ^ 2 * ((Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
                  + α ^ 2 * (Real.sin (2 * θ)) ^ (2 * α / 3 - Work.Spaces.gam α))) :=
            add_le_add hZsum hMsum
        _ = Kf ^ 2 * (M / (1 + z) ^ 2) ^ 2 * Big θ := by simp only [hBigdef]; ring
    · -- boundary: every term vanishes
      have hs : Real.sin (2 * θ) = 0 :=
        Work.Spaces.sin_two_mul_eq_zero_of_mem_Iθ_of_not_mem_Ioo hθ hθi
      rw [Work.Construction.HkIntegrand_eq_zero_of_sin_two_eq_zero hα hs]
      have h0 : Big θ = 0 := by
        simp only [hBigdef, hs,
          Real.zero_rpow (by linarith [Work.Spaces.eta_pos] : (-(Work.Spaces.eta)) ≠ 0),
          Real.zero_rpow (by rw [Work.Spaces.gam]; intro hh; linarith :
            (2 * α / 3 - Work.Spaces.gam α) ≠ 0)]
        ring
      rw [h0]; norm_num
  intro z hz θ hθ
  exact hpt z hz θ hθ

/-- **The `ℋ⁴`-honesty of `N0fix α`** (`0 < α ≤ 1`): transfer from the separable datum
`F = Kfac α · rhoR · psiA α`, whose `ℋ⁴`-integrand is dominated by the separable majorant, so
that `Work.FTS.LocData.HkMem_of_majorant` applies. -/
theorem HkMem_N0fix (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) :
    Work.Spaces.HkMem α 4 (Work.FTS.Nonlin.N0fix α) := by
  obtain ⟨M, hM, hMr⟩ := Work.Construction.H4N_GammaTerm_rho_bound
  obtain ⟨D, hD, hDl⟩ := Work.Construction.H4N_GammaTerm_Lop_bound
  set F : ℝ → ℝ → ℝ := Work.Construction.sepF
    (fun z => Work.Construction.Kfac α * Work.Construction.rhoR z)
    (Work.Construction.psiA α) with hF
  have hpt : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α 4 F z θ
        ≤ (Work.Construction.Kfac α) ^ 2 * (M / (1 + z) ^ 2) ^ 2 * gammaAngMaj α D θ := by
    intro z hz θ hθ
    rw [hF]
    exact HkIntegrand_sep_le α hα hα1 hM hD hMr (hDl α hα hα1) z hz θ hθ
  have hmem : Work.Spaces.HkMem α 4 F := by
    refine Work.FTS.LocData.HkMem_of_majorant α 4
      (M := fun z θ => (Work.Construction.Kfac α) ^ 2 * (M / (1 + z) ^ 2) ^ 2 * gammaAngMaj α D θ)
      ?_ ?_ ?_ ?_
    · exact Work.FTS.OpenPkg.continuousOn_HkIntegrand_of_contDiffOn α (n := 4) (k := 4) le_rfl
        (contDiffOn_uncurry_sep α)
    · intro z hz
      exact (integrableOn_gammaAngMaj α D hα hα1).const_mul _
    · have hbase : IntegrableOn (fun z : ℝ => ((Work.Construction.Kfac α) ^ 2 * M ^ 2
          * (∫ θ in Work.Spaces.Iθ, gammaAngMaj α D θ)) * (1 / (1 + z) ^ 2) ^ 2) Work.Spaces.Iz :=
        integrableOn_inv_one_add_pow_four.const_mul _
      refine hbase.congr_fun ?_ measurableSet_Ici
      intro z hz
      dsimp only
      rw [MeasureTheory.integral_const_mul]
      ring
    · intro z hz θ hθ
      exact hpt z hz θ hθ
  refine Work.FTS.EllipticEst.Cert.GbarSin.HkMem_congr_Q0 α 4 hmem ?_
  intro z hz θ hθ
  exact (N0fix_eq_sep α hα hα1 z θ hz hθ.1 hθ.2).symm

theorem NRow1 (IP : ℝ → Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn → ℝ) {α₂ Ci Ct Ce Cs : ℝ}
    (hN : Work.FTS.OpenPkg.N4Norm' Ci α₂) (hE : Work.FTS.OpenPkg.N4Extra' IP α₂ Ct) :
    ∃ K : ℝ, 0 < K ∧ ∀ {α : ℝ} {g Φs Φg : Work.FTS.Galerkin.Fn},
      Work.FTS.NonlinRows.Ctx α₂ Ci Ct Ce Cs α g Φs Φg →
      Work.Spaces.HkMem α 4 (Work.FTS.Nonlin.N0fix α) ∧
        Work.FTS.Nonlin.Xn α (Work.FTS.Nonlin.N0fix α) ≤ K * α ^ 2 := by
  obtain ⟨K, hK, hbnd⟩ := Work.FTS.Nonlinear.Pieces.RowsN0Aux.N0fix_bound
  refine ⟨K, hK, ?_⟩
  intro α g Φs Φg hctx
  exact ⟨HkMem_N0fix α hctx.hα hctx.hα1, hbnd α hctx.hα hctx.hα1⟩

end Work.FTS.NonlinRows
