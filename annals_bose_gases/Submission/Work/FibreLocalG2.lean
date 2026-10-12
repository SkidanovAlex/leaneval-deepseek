import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.FSKernelCompare
import Submission.Work.FibreLocal
import Submission.Work.QDecompSimpler
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# w₂-fibre pointwise lower bound (row-5/S2 prerequisite, cloned from FibreLocal)

(Work-in-progress module; Session-201.  Clone of the closed
`FibreLocal.w1Fibre_pointwise_lower` (g₀-numerator, mass `8π(av)`) with the
`g₂ = g₀(1+ω₀)`-numerator (mass `8π(av) + g0w0Mass`, `g0w0Mass := ∫g₀·ω₀`
the exact `ĝω(0)`-mass of `SmallBoxKernelMass`/`FSKernelCompare`):

    fibre₂(x) ≥ (8π(av) + g0w0Mass)·(χΛx)² − chiSup·Cχ·(R/ℓ)²·(8π(av) + g0w0Mass)

where `fibre₂(x) := w1Fibre ℓ (wPairC ℓ (g2 v h)) x` — the S2 (eq:Q2n0
`+ρ₀`-half) fibre ingredient of `QDecompSimpler.q2n0_mass_combination_
statement` (row 5 of the Session-125/200 ledger): with the `P`-constancy
peel (Q0Sector/Q1Peel) turning `q2PairWord` into the `ρ₀`-weighted
condensate one-body mass at `fibre₂`, this pointwise bound gives
`q2PairWord ≥ ρ₀·(8π(av)+g0w0Mass)·q2MassChi − ρ₀·C·(R/ℓ)²·(8π(av))·cnPlus`
(up to the peel bookkeeping), exactly as S1's `qmass_fibre_local_lower` did
for the `−μ`-half with `fibre₁`.

Two lemmas (sorry-free): `g2_le_wScaled_ae` (the `g₂(x−y) ≤
wScaled(g₂)(x−y)` sandwich, clone of `g0_le_wScaled_ae`) and
`w2Fibre_pointwise_lower` (the clone of `w1Fibre_pointwise_lower`), plus
the `chiTaylorC`-instantiation `w2Fibre_pointwise_lower_taylor`.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators
set_option maxHeartbeats 800000

namespace Submission

open _root_.BoseGases
open _root_.BoseGases.CInfty0Box
set_option autoImplicit false
set_option linter.unusedVariables false

namespace BoseGases

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-- Pointwise: `g₂(x−y) ≤ wScaled ℓ (g2 v h) (x−y)` a.e. in `y` (dilute
regime `convScale ≥ 1/2` on the support of `g₂`, `convScale ≤ 1`
everywhere) — the `g₂`-twin of `FibreLocal.g0_le_wScaled_ae`. -/
lemma g2_le_wScaled_ae {v : ℝ³ → ℝ} {R ℓ : ℝ} (hR : 0 < R)
    (hv_nonneg : 0 ≤ v) (hvrad : IsRadial v)
    (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v)
    (hℓ : 0 < ℓ) (hRℓ : R ≤ ℓ * chiR0) (x : ℝ³) :
    ∀ᵐ y ∂(volume : Measure ℝ³), g2 v h (x - y) ≤ wScaled ℓ (g2 v h) (x - y) := by
  classical
  have hg2nn : ∀ᵐ z : ℝ³, 0 ≤ g2 v h z := g2_nonneg_ae hR hv_nonneg hvrad hv_supp h
  have htr : ∀ᵐ y ∂(volume : Measure ℝ³), 0 ≤ g2 v h (x - y) :=
    ae_comp_sub_left (p := fun z : ℝ³ => 0 ≤ g2 v h z) hg2nn x
  filter_upwards [htr] with y hy
  by_cases hz : g2 v h (x - y) = 0
  · dsimp [wScaled]
    rw [hz]
    norm_num
  · have hgpos : 0 < g2 v h (x - y) := lt_of_le_of_ne hy (Ne.symm hz)
    have hxRlt : ‖x - y‖ < R := by
      by_contra hn
      have hRle : R ≤ ‖x - y‖ := le_of_not_gt hn
      exact (hgpos.ne' (g2_zero_of_norm_ge (v := v) hv_supp hRle h))
    have hcs : 0 < convScale ℓ (x - y) := by
      have hhalf : 1 / 2 ≤ convScale ℓ (x - y) :=
        convScale_ge_half_ball (ℓ := ℓ) (R := R) hℓ hR.le hRℓ (le_of_lt hxRlt)
      linarith
    have hcs1 : convScale ℓ (x - y) ≤ 1 := convScale_le_one ℓ (x - y)
    have hcinv0 : 0 < (convScale ℓ (x - y))⁻¹ := inv_pos.mpr hcs
    have hinv : 1 ≤ (convScale ℓ (x - y))⁻¹ := by
      have hm := mul_le_mul_of_nonneg_right hcs1 (le_of_lt hcinv0)
      rwa [mul_inv_cancel₀ (ne_of_gt hcs), one_mul] at hm
    dsimp [wScaled]
    have hdiv : (g2 v h (x - y)) / convScale ℓ (x - y)
        ≥ g2 v h (x - y) * 1 := by
      rw [div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_left hinv hy
    linarith

/-- **w₂-fibre pointwise lower bound** (the S2 ingredient): with
`fibre₂(x) := w1Fibre ℓ (wPairC ℓ (g2 v h)) x` and the exact mass
`M := 8π(av) + g0w0Mass` (`g0w0Mass := ∫g₀·ω₀`, so `∫g₂ = M` by
`g2_integral_eq_av_add_g0w0`),

    M·(χΛx)² − chiSup·Cχ·(R/ℓ)²·M ≤ fibre₂(x).

Clone of `FibreLocal.w1Fibre_pointwise_lower` (g₀ ↦ g₂, `8πa` ↦ `M`). -/
lemma w2Fibre_pointwise_lower {v : ℝ³ → ℝ} {R ℓ Cχ : ℝ} (hR : 0 < R)
    (hv_nonneg : 0 ≤ v) (hvrad : IsRadial v)
    (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v)
    (hℓ : 0 < ℓ) (hRℓ : R ≤ ℓ * chiR0)
    (hCχ : 0 ≤ Cχ)
    (hT : ∀ u v : ℝ³, |chi (u - v) - chi u + (fderiv ℝ chi u) v| ≤ Cχ * ‖v‖ ^ 2)
    (x : ℝ³) :
    (8 * π * a v + g0w0Mass (v := v) h) * (chiScale ℓ x) ^ 2
        - chiSup * Cχ * (R / ℓ) ^ 2 * (8 * π * a v + g0w0Mass (v := v) h)
      ≤ w1Fibre ℓ (wPairC ℓ (g2 v h)) x := by
  classical
  let g2f : ℝ³ → ℝ := g2 v h
  let M : ℝ := 8 * π * a v + g0w0Mass (v := v) h
  let E : ℝ := Cχ * (R / ℓ) ^ 2 * M
  have hAv : 0 ≤ a v := (av_bounds_weak hR hv_nonneg hvrad hv_supp h).1
  have hMnn : 0 ≤ M := by
    have hnn : 0 ≤ (∫ x : ℝ³, g2 v h x) :=
      MeasureTheory.integral_nonneg_of_ae (g2_nonneg_ae hR hv_nonneg hvrad hv_supp h)
    have hEq : (∫ x : ℝ³, g2 v h x) = M := by
      dsimp [M, g0w0Mass]
      exact g2_integral_eq_av_add_g0w0 hR hv_nonneg hvrad hv_supp h
    rwa [hEq] at hnn
  have hEnn : 0 ≤ E := by
    dsimp [E]
    exact mul_nonneg (mul_nonneg hCχ (sq_nonneg (R / ℓ))) hMnn
  have hg2supp : ∀ z : ℝ³, R ≤ ‖z‖ → g2f z = 0 := by
    intro z hz
    dsimp [g2f]
    exact g2_zero_of_norm_ge (v := v) hv_supp hz h
  have hg2i : MeasureTheory.Integrable g2f := by
    dsimp [g2f]
    exact g2_integrable hR hv_nonneg hvrad hv_supp h
  have hg2nn : ∀ᵐ z : ℝ³, 0 ≤ g2f z := by
    dsimp [g2f]
    exact g2_nonneg_ae hR hv_nonneg hvrad hv_supp h
  have hg2even : ∀ z : ℝ³, g2f (-z) = g2f z := by
    intro z
    dsimp [g2f]
    exact g2_even hvrad h z
  have hg2int : (∫ z : ℝ³, g2f z) = M := by
    dsimp [g2f, M, g0w0Mass]
    exact g2_integral_eq_av_add_g0w0 hR hv_nonneg hvrad hv_supp h
  have hg2abs : (∫ z : ℝ³, |g2f z|) = M := by
    calc
      (∫ z : ℝ³, |g2f z|) = ∫ z : ℝ³, g2f z := by
        apply integral_congr_ae
        filter_upwards [hg2nn] with z hz
        exact abs_of_nonneg hz
      _ = M := hg2int
  have hwi : MeasureTheory.Integrable (wScaled ℓ g2f) :=
    wScaled_integrable_ae hℓ hR.le hRℓ hg2i hg2supp
  have hconv := convolution_approx (ℓ := ℓ) (R := R) (Cχ := Cχ) hℓ hT hg2i hg2even hg2supp hR.le x
  have hfibE : w1Fibre ℓ (wPairC ℓ (g2 v h)) x
      = chiScale ℓ x * (∫ y : ℝ³, chiScale ℓ y * wScaled ℓ g2f (x - y)) := by
    calc
      w1Fibre ℓ (wPairC ℓ (g2 v h)) x
          = ∫ y in acube ℓ, wPair ℓ (g2 v h) x y := by
              simp [w1Fibre, wPairC]
      _ = ∫ y : ℝ³, wPair ℓ (g2 v h) x y := mean_kernel_full hℓ hwi x
      _ = chiScale ℓ x * (∫ y : ℝ³, chiScale ℓ y * wScaled ℓ g2f (x - y)) := by
              simpa [g2f] using (kernel_fibre hℓ hwi x)
  have hmono : (∫ y : ℝ³, chiScale ℓ y * wScaled ℓ g2f (x - y))
      ≥ ∫ y : ℝ³, chiScale ℓ y * g2f (x - y) := by
    have hle : ∀ᵐ y ∂(volume : Measure ℝ³),
        chiScale ℓ y * wScaled ℓ g2f (x - y) ≥ chiScale ℓ y * g2f (x - y) := by
      have hws : ∀ᵐ y ∂(volume : Measure ℝ³), g2f (x - y) ≤ wScaled ℓ g2f (x - y) := by
        simpa [g2f] using (g2_le_wScaled_ae (v := v) (R := R) hR hv_nonneg hvrad hv_supp h hℓ hRℓ x)
      filter_upwards [hws] with y hy
      exact mul_le_mul_of_nonneg_left hy (chi_nonneg ((ℓ⁻¹) • y))
    have hLHS : MeasureTheory.Integrable (fun y : ℝ³ =>
        chiScale ℓ y * wScaled ℓ g2f (x - y)) := kernel_fibre_integrable hℓ hwi x
    have hRHS : MeasureTheory.Integrable (fun y : ℝ³ =>
        chiScale ℓ y * g2f (x - y)) := by
      have hg2c : MeasureTheory.Integrable (fun y : ℝ³ => g2f (x - y)) :=
        km_integrable_comp_sub_left hg2i x
      have hbnd : ∀ᵐ y ∂(volume : Measure ℝ³),
          ‖chiScale ℓ y * g2f (x - y)‖ ≤ chiSup * |g2f (x - y)| := by
        refine ae_of_all _ (fun y => ?_)
        calc
          ‖chiScale ℓ y * g2f (x - y)‖ = |chiScale ℓ y * g2f (x - y)| := by
                  rw [Real.norm_eq_abs]
          _ = |chiScale ℓ y| * |g2f (x - y)| := by rw [abs_mul]
          _ ≤ chiSup * |g2f (x - y)| := by
            exact mul_le_mul_of_nonneg_right (abs_chiScale_le_chiSup ℓ y) (abs_nonneg _)
      have hcm : AEStronglyMeasurable (fun y : ℝ³ => chiScale ℓ y) volume :=
        (chiScale_continuous ℓ).aestronglyMeasurable
      have hg2m : AEStronglyMeasurable (fun y : ℝ³ => g2f (x - y)) volume :=
        km_aestronglyMeasurable_comp_sub_left hg2i.aestronglyMeasurable x
      exact MeasureTheory.Integrable.mono' (hg2c.abs.const_mul chiSup) (hcm.mul hg2m) hbnd
    exact integral_mono_ae hRHS hLHS hle
  have href : (∫ y : ℝ³, chiScale ℓ y * g2f (x - y))
      = ∫ y : ℝ³, g2f y * chiScale ℓ (x - y) := by
    have hg := integral_comp_sub_left
      (g := fun w : ℝ³ => g2f w * chiScale ℓ (x - w)) x
    calc
      (∫ y : ℝ³, chiScale ℓ y * g2f (x - y))
          = ∫ y : ℝ³, g2f (x - y) * chiScale ℓ y := by
              apply integral_congr_ae
              refine ae_of_all _ (fun y => ?_)
              ring
      _ = ∫ y : ℝ³, g2f y * chiScale ℓ (x - y) := by
              simpa [mul_comm, mul_left_comm, mul_assoc] using hg
  have hJ : chiScale ℓ x * (∫ y : ℝ³, g2f y) - E
      ≤ ∫ y : ℝ³, g2f y * chiScale ℓ (x - y) := by
    have hJint : MeasureTheory.Integrable (fun y : ℝ³ =>
        g2f y * chiScale ℓ (x - y)) := by
      have hbnd : ∀ᵐ y ∂(volume : Measure ℝ³),
          ‖g2f y * chiScale ℓ (x - y)‖ ≤ |g2f y| * chiSup := by
        refine ae_of_all _ (fun y => ?_)
        calc
          ‖g2f y * chiScale ℓ (x - y)‖ = |g2f y * chiScale ℓ (x - y)| := by
                  rw [Real.norm_eq_abs]
          _ = |g2f y| * |chiScale ℓ (x - y)| := by rw [abs_mul]
          _ ≤ |g2f y| * chiSup := by
            exact mul_le_mul_of_nonneg_left (abs_chiScale_le_chiSup ℓ (x - y)) (abs_nonneg _)
      have hg2m : AEStronglyMeasurable g2f volume := hg2i.aestronglyMeasurable
      have hcm : AEStronglyMeasurable (fun y : ℝ³ => chiScale ℓ (x - y)) volume :=
        (chiScale_continuous ℓ).comp (continuous_const.sub continuous_id) |>.aestronglyMeasurable
      exact MeasureTheory.Integrable.mono' (hg2i.abs.mul_const chiSup) (hg2m.mul hcm) hbnd
    have hcst : MeasureTheory.Integrable (fun y : ℝ³ => g2f y * chiScale ℓ x) :=
      hg2i.mul_const (chiScale ℓ x)
    have hdiff : (∫ y : ℝ³, g2f y * (chiScale ℓ (x - y) - chiScale ℓ x))
        = (∫ y : ℝ³, g2f y * chiScale ℓ (x - y))
          - chiScale ℓ x * (∫ y : ℝ³, g2f y) := by
      calc
        (∫ y : ℝ³, g2f y * (chiScale ℓ (x - y) - chiScale ℓ x))
            = ∫ y : ℝ³, g2f y * chiScale ℓ (x - y) - g2f y * chiScale ℓ x := by
                apply integral_congr_ae
                refine ae_of_all _ (fun y => ?_)
                ring
        _ = (∫ y : ℝ³, g2f y * chiScale ℓ (x - y))
            - (∫ y : ℝ³, g2f y * chiScale ℓ x) := by
                rw [← integral_sub hJint hcst]
        _ = (∫ y : ℝ³, g2f y * chiScale ℓ (x - y))
            - chiScale ℓ x * (∫ y : ℝ³, g2f y) := by
                rw [integral_mul_const]
                ring
    have habs : |∫ y : ℝ³, g2f y * (chiScale ℓ (x - y) - chiScale ℓ x)|
        ≤ Cχ * (R / ℓ) ^ 2 * (∫ y : ℝ³, |g2f y|) := by
      simpa using hconv
    have hge : - (Cχ * (R / ℓ) ^ 2 * (∫ y : ℝ³, |g2f y|))
        ≤ (∫ y : ℝ³, g2f y * (chiScale ℓ (x - y) - chiScale ℓ x)) :=
      (abs_le.mp habs).1
    have hE' : Cχ * (R / ℓ) ^ 2 * (∫ y : ℝ³, |g2f y|) = E := by
      rw [hg2abs]
    linarith
  have hχ : 0 ≤ chiScale ℓ x := chi_nonneg ((ℓ⁻¹) • x)
  have hχle : chiScale ℓ x ≤ chiSup := by
    have h := abs_chiScale_le_chiSup ℓ x
    rwa [abs_of_nonneg hχ] at h
  have hfin : chiScale ℓ x * (∫ y : ℝ³, chiScale ℓ y * wScaled ℓ g2f (x - y))
      ≥ M * (chiScale ℓ x) ^ 2 - chiSup * E := by
    have hstep1 : chiScale ℓ x * (∫ y : ℝ³, chiScale ℓ y * wScaled ℓ g2f (x - y))
        ≥ chiScale ℓ x * (∫ y : ℝ³, chiScale ℓ y * g2f (x - y)) :=
      mul_le_mul_of_nonneg_left hmono hχ
    have hstep2 : chiScale ℓ x * (∫ y : ℝ³, chiScale ℓ y * g2f (x - y))
        ≥ chiScale ℓ x * (chiScale ℓ x * (∫ y : ℝ³, g2f y) - E) := by
      rw [href]
      exact mul_le_mul_of_nonneg_left hJ hχ
    have hstep4 : (chiScale ℓ x) ^ 2 * (∫ y : ℝ³, g2f y) - chiScale ℓ x * E
        ≥ M * (chiScale ℓ x) ^ 2 - chiSup * E := by
      rw [hg2int]
      have hb1 : chiScale ℓ x * E ≤ chiSup * E := mul_le_mul_of_nonneg_right hχle hEnn
      have hb2 : M * (chiScale ℓ x) ^ 2 = (chiScale ℓ x) ^ 2 * M := by
        ring
      rw [← hb2]
      linarith
    calc
      chiScale ℓ x * (∫ y : ℝ³, chiScale ℓ y * wScaled ℓ g2f (x - y))
          ≥ chiScale ℓ x * (chiScale ℓ x * (∫ y : ℝ³, g2f y) - E) := le_trans hstep2 hstep1
      _ = (chiScale ℓ x) ^ 2 * (∫ y : ℝ³, g2f y) - chiScale ℓ x * E := by ring
      _ ≥ M * (chiScale ℓ x) ^ 2 - chiSup * E := hstep4
  rw [hfibE]
  have hRHS : M * (chiScale ℓ x) ^ 2 - chiSup * E
      = (8 * π * a v + g0w0Mass (v := v) h) * (chiScale ℓ x) ^ 2
          - chiSup * Cχ * (R / ℓ) ^ 2 * (8 * π * a v + g0w0Mass (v := v) h) := by
    dsimp [M, E]
    ring
  rw [← hRHS]
  exact hfin

/-- **w₂-fibre pointwise lower bound with the corpus Taylor constant**:
instantiation of `w2Fibre_pointwise_lower` at `Cχ := chiTaylorC`. -/
lemma w2Fibre_pointwise_lower_taylor {v : ℝ³ → ℝ} {R ℓ : ℝ} (hR : 0 < R)
    (hv_nonneg : 0 ≤ v) (hvrad : IsRadial v)
    (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v)
    (hℓ : 0 < ℓ) (hRℓ : R ≤ ℓ * chiR0) (x : ℝ³) :
    (8 * π * a v + g0w0Mass (v := v) h) * (chiScale ℓ x) ^ 2
        - chiSup * chiTaylorC * (R / ℓ) ^ 2 * (8 * π * a v + g0w0Mass (v := v) h)
      ≤ w1Fibre ℓ (wPairC ℓ (g2 v h)) x := by
  exact w2Fibre_pointwise_lower hR hv_nonneg hvrad hv_supp h hℓ hRℓ
    chiTaylorC_spec.1 chiTaylorC_spec.2 x


/-- `w₂`-fibre absolute bound on the cube: `|fibre₂(x)| ≤ chiSup²·2·M`
(`M := 8π(av)+g0w0Mass`) — the `g₂`-twin of
`PotChosen.w1c_fibre_acube_abs_le` (`fibre_acube_abs_le` + `∫|g₂| = M`). -/
lemma w2Fibre_acube_abs_le {v : ℝ³ → ℝ} {R ℓ : ℝ} (hR : 0 < R)
    (hv_nonneg : 0 ≤ v) (hvrad : IsRadial v)
    (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v)
    (hℓ : 0 < ℓ) (hRℓ : R ≤ ℓ * chiR0) (x : ℝ³) :
    |∫ y in acube ℓ, wPair ℓ (g2 v h) x y| ≤ chiSup ^ 2 * 2 * (8 * π * a v + g0w0Mass (v := v) h) := by
  have hbnd := fibre_acube_abs_le (h := g2 v h) hℓ (le_of_lt hR) hRℓ
    (g2_integrable hR hv_nonneg hvrad hv_supp h) (fun z hz => g2_zero_of_norm_ge hv_supp hz h) x
  have hnn : ∀ᵐ z : ℝ³, 0 ≤ g2 v h z := g2_nonneg_ae hR hv_nonneg hvrad hv_supp h
  have hEq : (∫ z : ℝ³, |g2 v h z|) = ∫ z : ℝ³, g2 v h z := by
    apply integral_congr_ae
    filter_upwards [hnn] with z hz
    exact abs_of_nonneg hz
  have hM : (∫ z : ℝ³, g2 v h z) = 8 * π * a v + g0w0Mass (v := v) h := by
    dsimp [g0w0Mass]
    exact g2_integral_eq_av_add_g0w0 hR hv_nonneg hvrad hv_supp h
  rwa [hEq, hM] at hbnd

/-- **Summed w₂-fibre localisation, per particle** (clone of
`QMassLower.qmass_fibre_local_lower_per` with `fibre₂` and the exact mass
`M := 8π(av)+g0w0Mass`, error `E := chiSup·chiTaylorC·(R/ℓ)²·M`): for every
slot `i`,

    M·∫(Q_iΦ)²·χΛ(xᵢ)² − E·∫(Q_iΦ)² ≤ ∫(Q_iΦ)²·fibre₂(xᵢ).  -/
lemma w2Fibre_mass_lower_per {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ)
    {v : ℝ³ → ℝ} (hv_nonneg : 0 ≤ v) (hvrad : IsRadial v)
    {R : ℝ} (hR : 0 < R) (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v)
    (hRℓ : R ≤ ℓ * chiR0) (i : Fin N) {Φ : X N → ℝ} (hΦc : Continuous Φ) :
    (8 * π * a v + g0w0Mass (v := v) h) *
          (∫ x in abox N ℓ, (aQ ℓ i Φ x) ^ 2 * (chiScale ℓ (x i)) ^ 2)
      - chiSup * chiTaylorC * (R / ℓ) ^ 2 * (8 * π * a v + g0w0Mass (v := v) h) *
          (∫ x in abox N ℓ, (aQ ℓ i Φ x) ^ 2)
      ≤ ∫ x in abox N ℓ,
          (aQ ℓ i Φ x) ^ 2 * (w1Fibre ℓ (wPairC ℓ (g2 v h)) (x i)) := by
  classical
  let M : ℝ := 8 * π * a v + g0w0Mass (v := v) h
  let E : ℝ := chiSup * chiTaylorC * (R / ℓ) ^ 2 * M
  have hMnn : 0 ≤ M := by
    have hnn : 0 ≤ (∫ x : ℝ³, g2 v h x) :=
      MeasureTheory.integral_nonneg_of_ae (g2_nonneg_ae hR hv_nonneg hvrad hv_supp h)
    have hEq : (∫ x : ℝ³, g2 v h x) = M := by
      dsimp [M, g0w0Mass]
      exact g2_integral_eq_av_add_g0w0 hR hv_nonneg hvrad hv_supp h
    rwa [hEq] at hnn
  have hEnn : 0 ≤ E := by
    dsimp [E]
    exact mul_nonneg (mul_nonneg (mul_nonneg (le_of_lt chiSup_pos) chiTaylorC_spec.1)
      (sq_nonneg (R / ℓ))) hMnn
  have hpw : ∀ x : X N,
      M * (chiScale ℓ (x i)) ^ 2 - E ≤
        w1Fibre ℓ (wPairC ℓ (g2 v h)) (x i) := by
    intro x
    simpa [M, E] using
      (w2Fibre_pointwise_lower_taylor (v := v) (R := R) hR hv_nonneg hvrad hv_supp h
        hℓ hRℓ (x i))
  let f : X N → ℝ := fun x => (aQ ℓ i Φ x) ^ 2 *
      (M * (chiScale ℓ (x i)) ^ 2 - E)
  let g : X N → ℝ := fun x => (aQ ℓ i Φ x) ^ 2 * (w1Fibre ℓ (wPairC ℓ (g2 v h)) (x i))
  have hQc : Continuous (aQ ℓ i Φ) := aQ_continuous hℓ i hΦc
  have hcoor : Continuous (fun x : X N => x i) := continuous_apply i
  have hfc : Continuous f := by
    dsimp [f]
    have h1 : Continuous (fun x : X N => M * (chiScale ℓ (x i)) ^ 2 - E) := by
      exact ((continuous_const.mul (((chiScale_continuous ℓ).comp hcoor).pow 2)).sub
        continuous_const)
    exact (hQc.pow 2).mul h1
  have hfI : IntegrableOn f (abox N ℓ) volume := integrableOn_abox_of_continuous hℓ hfc
  have hgI : IntegrableOn g (abox N ℓ) volume := by
    dsimp [g]
    have hFm : AEStronglyMeasurable (fun z : ℝ³ => w1Fibre ℓ (wPairC ℓ (g2 v h)) z)
        (volume.restrict (acube ℓ)) := by
      have hfac := fibre_acube_aem (ℓ := ℓ) (h := g2 v h) (g2_integrable hR hv_nonneg hvrad hv_supp h)
      simpa [w1Fibre, wPairC] using hfac
    have hbnd : ∀ z : ℝ³, z ∈ acube ℓ →
        |w1Fibre ℓ (wPairC ℓ (g2 v h)) z| ≤ chiSup ^ 2 * 2 * (8 * π * a v + g0w0Mass (v := v) h) := by
      intro z hz
      simpa [w1Fibre, wPairC] using
        (w2Fibre_acube_abs_le hR hv_nonneg hvrad hv_supp h hℓ hRℓ z)
    exact integrableOn_slot_fibre hℓ i hFm hbnd (hQc.pow 2)
  have hmono : (∫ x in abox N ℓ, f x) ≤ ∫ x in abox N ℓ, g x := by
    refine integral_mono hfI hgI ?_
    intro x
    dsimp [f, g, M, E]
    have hc : 0 ≤ (aQ ℓ i Φ x) ^ 2 := sq_nonneg _
    exact mul_le_mul_of_nonneg_left (hpw x) hc
  have hsplit : (∫ x in abox N ℓ, f x)
      = M * (∫ x in abox N ℓ, (aQ ℓ i Φ x) ^ 2 * (chiScale ℓ (x i)) ^ 2)
        - E * (∫ x in abox N ℓ, (aQ ℓ i Φ x) ^ 2) := by
    have hI1 : IntegrableOn (fun x : X N =>
        M * ((aQ ℓ i Φ x) ^ 2 * (chiScale ℓ (x i)) ^ 2)) (abox N ℓ) volume := by
      exact integrableOn_abox_of_continuous hℓ
        (continuous_const.mul ((hQc.pow 2).mul (((chiScale_continuous ℓ).comp hcoor).pow 2)))
    have hI2 : IntegrableOn (fun x : X N => E * (aQ ℓ i Φ x) ^ 2) (abox N ℓ) volume := by
      exact integrableOn_abox_of_continuous hℓ (continuous_const.mul (hQc.pow 2))
    calc
      (∫ x in abox N ℓ, f x)
          = ∫ x in abox N ℓ, (aQ ℓ i Φ x) ^ 2 * (M * (chiScale ℓ (x i)) ^ 2 - E) := by
              dsimp [f]
      _ = ∫ x in abox N ℓ,
            (M * ((aQ ℓ i Φ x) ^ 2 * (chiScale ℓ (x i)) ^ 2) - E * (aQ ℓ i Φ x) ^ 2) := by
              apply integral_congr_ae
              refine ae_of_all _ (fun x => ?_)
              ring
      _ = (∫ x in abox N ℓ, M * ((aQ ℓ i Φ x) ^ 2 * (chiScale ℓ (x i)) ^ 2))
          - (∫ x in abox N ℓ, E * (aQ ℓ i Φ x) ^ 2) := by
              exact integral_sub hI1 hI2
      _ = M * (∫ x in abox N ℓ, (aQ ℓ i Φ x) ^ 2 * (chiScale ℓ (x i)) ^ 2)
          - E * (∫ x in abox N ℓ, (aQ ℓ i Φ x) ^ 2) := by
              rw [integral_const_mul]
              rw [integral_const_mul]
  calc
    M * (∫ x in abox N ℓ, (aQ ℓ i Φ x) ^ 2 * (chiScale ℓ (x i)) ^ 2)
      - E * (∫ x in abox N ℓ, (aQ ℓ i Φ x) ^ 2)
        = ∫ x in abox N ℓ, f x := hsplit.symm
    _ ≤ ∫ x in abox N ℓ, g x := hmono
    _ = ∫ x in abox N ℓ,
        (aQ ℓ i Φ x) ^ 2 * (w1Fibre ℓ (wPairC ℓ (g2 v h)) (x i)) := by
          dsimp [g]

/-- **Summed w₂-fibre localisation** (S2's "fibre-localisation as in S1",
clone of `QMassLower.qmass_fibre_local_lower` with `fibre₂` and mass
`M := 8π(av)+g0w0Mass`):

    M·q2MassChi − chiSup·chiTaylorC·(R/ℓ)²·M·cnPlus
        ≤ Σ_i∫(Q_iΦ)²·fibre₂(xᵢ).  -/
lemma w2Fibre_mass_lower {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ)
    {v : ℝ³ → ℝ} (hv_nonneg : 0 ≤ v) (hvrad : IsRadial v)
    {R : ℝ} (hR : 0 < R) (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v)
    (hRℓ : R ≤ ℓ * chiR0) {Φ : X N → ℝ} (hΦc : Continuous Φ) :
    (8 * π * a v + g0w0Mass (v := v) h) *
          (∑ i : Fin N, ∫ x in abox N ℓ, (aQ ℓ i Φ x) ^ 2 * (chiScale ℓ (x i)) ^ 2)
      - chiSup * chiTaylorC * (R / ℓ) ^ 2 * (8 * π * a v + g0w0Mass (v := v) h) *
          cnPlus ℓ Φ
      ≤ ∑ i : Fin N, ∫ x in abox N ℓ,
          (aQ ℓ i Φ x) ^ 2 * (w1Fibre ℓ (wPairC ℓ (g2 v h)) (x i)) := by
  classical
  let M : ℝ := 8 * π * a v + g0w0Mass (v := v) h
  let E : ℝ := chiSup * chiTaylorC * (R / ℓ) ^ 2 * M
  have hper : ∀ i : Fin N,
      M * (∫ x in abox N ℓ, (aQ ℓ i Φ x) ^ 2 * (chiScale ℓ (x i)) ^ 2)
        - E * (∫ x in abox N ℓ, (aQ ℓ i Φ x) ^ 2)
        ≤ ∫ x in abox N ℓ,
            (aQ ℓ i Φ x) ^ 2 * (w1Fibre ℓ (wPairC ℓ (g2 v h)) (x i)) := by
    intro i
    simpa [M, E] using
      (w2Fibre_mass_lower_per hℓ hv_nonneg hvrad hR hv_supp h hRℓ i hΦc)
  calc
    M * (∑ i : Fin N, ∫ x in abox N ℓ, (aQ ℓ i Φ x) ^ 2 * (chiScale ℓ (x i)) ^ 2)
      - E * cnPlus ℓ Φ
        = M * (∑ i : Fin N, ∫ x in abox N ℓ, (aQ ℓ i Φ x) ^ 2 * (chiScale ℓ (x i)) ^ 2)
          - E * (∑ i : Fin N, ∫ x in abox N ℓ, (aQ ℓ i Φ x) ^ 2) := by
            dsimp [cnPlus]
    _ ≤ ∑ i : Fin N, ∫ x in abox N ℓ,
          (aQ ℓ i Φ x) ^ 2 * (w1Fibre ℓ (wPairC ℓ (g2 v h)) (x i)) := by
            have hsum : ∑ i : Fin N,
                (M * (∫ x in abox N ℓ, (aQ ℓ i Φ x) ^ 2 * (chiScale ℓ (x i)) ^ 2)
                  - E * (∫ x in abox N ℓ, (aQ ℓ i Φ x) ^ 2))
                ≤ ∑ i : Fin N, ∫ x in abox N ℓ,
                    (aQ ℓ i Φ x) ^ 2 * (w1Fibre ℓ (wPairC ℓ (g2 v h)) (x i)) :=
              Finset.sum_le_sum (fun i hi => hper i)
            calc
              M * (∑ i : Fin N, ∫ x in abox N ℓ, (aQ ℓ i Φ x) ^ 2 * (chiScale ℓ (x i)) ^ 2)
                  - E * (∑ i : Fin N, ∫ x in abox N ℓ, (aQ ℓ i Φ x) ^ 2)
                  = ∑ i : Fin N,
                      (M * (∫ x in abox N ℓ, (aQ ℓ i Φ x) ^ 2 * (chiScale ℓ (x i)) ^ 2)
                        - E * (∫ x in abox N ℓ, (aQ ℓ i Φ x) ^ 2)) := by
                      rw [Finset.sum_sub_distrib]
                      rw [← Finset.mul_sum]
                      rw [← Finset.mul_sum]
                  _ ≤ ∑ i : Fin N, ∫ x in abox N ℓ,
                      (aQ ℓ i Φ x) ^ 2 * (w1Fibre ℓ (wPairC ℓ (g2 v h)) (x i)) := hsum
    _ ≤ ∑ i : Fin N, ∫ x in abox N ℓ,
          (aQ ℓ i Φ x) ^ 2 * (w1Fibre ℓ (wPairC ℓ (g2 v h)) (x i)) := le_rfl
end BoseGases

end Submission
