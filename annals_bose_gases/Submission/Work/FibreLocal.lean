import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Submission.ConvChiBound
import Submission.ConvolutionTaylor
import Submission.KernelFibreBound
import Submission.PotWords
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# eq:Q2n0 mass treatment, S1 — fibre localisation of the one-body Q-mass

FS `lem:QDecompSimpler` (`eq:Q2n0`) applies `lem:Convolution` to the
one-body excited mass: with `w₁ := wPairC ℓ (g0 v h)` the fibre

    fibre(x) := w1Fibre ℓ (wPairC ℓ (g0 v h)) x = ∫_y w₁(x,y) dy

equals `8πa v · χΛ(x)²` up to `(R/ℓ)²` errors (χΛ := chiScale ℓ; the corpus
χ is L²-normalised, `chi_L2 : ∫χ² = 1`, so no further constant appears):

    (8πa v)·χΛ(x)² − chiSup·Cχ·(R/ℓ)²·(8πa v) ≤ fibre(x)

where `Cχ` is the second-order Taylor constant of `χ`
(`ConvolutionTaylor.chi_second_order_bound`).  Summing against the excited
squares gives the per-state mass lower bound (S1):

    Σ_i∫(Q_iΦ)²·fibre(x_i)
        ≥ (8πa v)·Σ_i∫(Q_iΦ)²·χΛ(x_i)² − chiSup·Cχ·(R/ℓ)²·(8πa v)·cnPlus ℓ Φ

Proof route (pointwise): `mean_kernel_full` (cube-fibre = full-space fibre),
`kernel_fibre` (fibre = χΛ(x)·∫_y χΛ(y)·wScaled(x−y)),
`wScaled ≥ g₀` on `{g₀ ≥ 0}` (uses `conv3chi_le_one` i.e. `convScale ≤ 1`
and `convScale ≥ 1/2` on supp g₀ in the dilute regime), and
`convolution_approx` (f := g₀, even + supported in ball R):
`∫_y χΛ(y)g₀(x−y) ≥ χΛ(x)∫g₀ − Cχ(R/ℓ)²∫|g₀|`; then
`∫|g₀| = ∫g₀ = 8πa v` (`g0_nonneg_ae`, `g0_integral`).

STATUS: the module currently proves the supporting atoms
`chiTaylorC`/`chiTaylorC_spec` (the Taylor constant), `convScale_le_one`
(`convScale ≤ 1`, from `conv3chi_le_one`), and `g0_le_wScaled_ae` (the
a.e. sandwich lower bound `g₀(x−y) ≤ wScaled ℓ (g0 v h) (x−y)`, the key
kernel step).  The full pointwise lemma `w1Fibre_pointwise_lower` and its
summed form (S1, `qmass_fibre_local_lower`) are the next milestone: chain
`mean_kernel_full` + `kernel_fibre` + `integral_mono_ae` on
`g0_le_wScaled_ae`, identify `∫χΛ(y)g₀(x−y) = ∫g₀(y)χΛ(x−y)` by
`integral_comp_sub_left`, apply `convolution_approx` with `f := g₀`
(`g0_even`, `g0_zero_of_norm_ge`, `∫|g₀| = ∫g₀ = 8πa v`), and assemble
with `0 ≤ χΛ(x) ≤ chiSup`.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators
set_option maxHeartbeats 800000

namespace Submission

open _root_.BoseGases
open _root_.BoseGases.CInfty0Box
set_option autoImplicit false

namespace BoseGases

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-- The second-order Taylor constant of `χ` (`chi_second_order_bound`). -/
noncomputable def chiTaylorC : ℝ := Classical.choose chi_second_order_bound

/-- Specification of `chiTaylorC`: nonnegative and the second-order Taylor
bound `|χ(u−v) − χu + (fderiv χ u)v| ≤ C·‖v‖²`. -/
lemma chiTaylorC_spec : 0 ≤ chiTaylorC ∧
    ∀ u v : ℝ³, |chi (u - v) - chi u + (fderiv ℝ chi u) v| ≤ chiTaylorC * ‖v‖ ^ 2 := by
  exact Classical.choose_spec chi_second_order_bound

/-- `convScale ℓ z ≤ 1` pointwise (from `conv3chi_le_one`). -/
lemma convScale_le_one (ℓ : ℝ) (z : ℝ³) : convScale ℓ z ≤ 1 := by
  dsimp [convScale]
  exact conv3chi_le_one ((ℓ⁻¹) • z)

/-- Pointwise: `g₀(x−y) ≤ wScaled ℓ (g0 v h) (x−y)` a.e. in `y` (the
dilute regime gives `convScale ≥ 1/2` on the support of `g₀`, and
`convScale ≤ 1` everywhere). -/
lemma g0_le_wScaled_ae {v : ℝ³ → ℝ} {R ℓ : ℝ} (hR : 0 < R)
    (hv_nonneg : 0 ≤ v) (hvrad : IsRadial v)
    (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v)
    (hℓ : 0 < ℓ) (hRℓ : R ≤ ℓ * chiR0) (x : ℝ³) :
    ∀ᵐ y ∂(volume : Measure ℝ³), g0 v h (x - y) ≤ wScaled ℓ (g0 v h) (x - y) := by
  classical
  have hg0nn : ∀ᵐ z : ℝ³, 0 ≤ g0 v h z := g0_nonneg_ae hR hv_nonneg hvrad hv_supp h
  have htr : ∀ᵐ y ∂(volume : Measure ℝ³), 0 ≤ g0 v h (x - y) :=
    ae_comp_sub_left (p := fun z : ℝ³ => 0 ≤ g0 v h z) hg0nn x
  filter_upwards [htr] with y hy
  -- wScaled(x−y) = g0(x−y)/cs(x−y) ≥ g0(x−y)
  by_cases hz : g0 v h (x - y) = 0
  · dsimp [wScaled]
    rw [hz]
    norm_num
  · have hgpos : 0 < g0 v h (x - y) := lt_of_le_of_ne hy (Ne.symm hz)
    have hxRlt : ‖x - y‖ < R := by
      by_contra hn
      have hRle : R ≤ ‖x - y‖ := le_of_not_gt hn
      exact (hgpos.ne' (g0_zero_of_norm_ge (v := v) hv_supp hRle h))
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
    have hdiv : (g0 v h (x - y)) / convScale ℓ (x - y)
        ≥ g0 v h (x - y) * 1 := by
      rw [div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_left hinv hy
    linarith


lemma w1Fibre_pointwise_lower {v : ℝ³ → ℝ} {R ℓ Cχ : ℝ} (hR : 0 < R)
    (hv_nonneg : 0 ≤ v) (hvrad : IsRadial v)
    (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v)
    (hℓ : 0 < ℓ) (hRℓ : R ≤ ℓ * chiR0)
    (hCχ : 0 ≤ Cχ)
    (hT : ∀ u v : ℝ³, |chi (u - v) - chi u + (fderiv ℝ chi u) v| ≤ Cχ * ‖v‖ ^ 2)
    (x : ℝ³) :
    (8 * π * a v) * (chiScale ℓ x) ^ 2 - chiSup * Cχ * (R / ℓ) ^ 2 * (8 * π * a v)
      ≤ w1Fibre ℓ (wPairC ℓ (g0 v h)) x := by
  classical
  let g0f : ℝ³ → ℝ := g0 v h
  let E : ℝ := Cχ * (R / ℓ) ^ 2 * (8 * π * a v)
  have hAv : 0 ≤ a v := (av_bounds_weak hR hv_nonneg hvrad hv_supp h).1
  have hEnn : 0 ≤ E := by
    dsimp [E]
    exact mul_nonneg (mul_nonneg hCχ (sq_nonneg (R / ℓ)))
      (mul_nonneg (by positivity : (0 : ℝ) ≤ 8 * π) hAv)
  have hg0supp : ∀ z : ℝ³, R ≤ ‖z‖ → g0f z = 0 := by
    intro z hz
    dsimp [g0f]
    exact g0_zero_of_norm_ge (v := v) hv_supp hz h
  have hg0i : MeasureTheory.Integrable g0f := by
    dsimp [g0f]
    exact g0_integrable hR hv_supp h
  have hg0nn : ∀ᵐ z : ℝ³, 0 ≤ g0f z := by
    dsimp [g0f]
    exact g0_nonneg_ae hR hv_nonneg hvrad hv_supp h
  have hg0even : ∀ z : ℝ³, g0f (-z) = g0f z := by
    intro z
    dsimp [g0f]
    exact g0_even hvrad h z
  have hg0int : (∫ z : ℝ³, g0f z) = 8 * π * a v := by
    dsimp [g0f]
    exact g0_integral hR hv_supp h
  have hg0abs : (∫ z : ℝ³, |g0f z|) = 8 * π * a v := by
    calc
      (∫ z : ℝ³, |g0f z|) = ∫ z : ℝ³, g0f z := by
        apply integral_congr_ae
        filter_upwards [hg0nn] with z hz
        exact abs_of_nonneg hz
      _ = 8 * π * a v := hg0int
  have hwi : MeasureTheory.Integrable (wScaled ℓ g0f) :=
    wScaled_integrable_ae hℓ hR.le hRℓ hg0i hg0supp
  have hconv := convolution_approx (ℓ := ℓ) (R := R) (Cχ := Cχ) hℓ hT hg0i hg0even hg0supp hR.le x
  have hfibE : w1Fibre ℓ (wPairC ℓ (g0 v h)) x
      = chiScale ℓ x * (∫ y : ℝ³, chiScale ℓ y * wScaled ℓ g0f (x - y)) := by
    calc
      w1Fibre ℓ (wPairC ℓ (g0 v h)) x
          = ∫ y in acube ℓ, wPair ℓ (g0 v h) x y := by
              simp [w1Fibre, wPairC]
      _ = ∫ y : ℝ³, wPair ℓ (g0 v h) x y := mean_kernel_full hℓ hwi x
      _ = chiScale ℓ x * (∫ y : ℝ³, chiScale ℓ y * wScaled ℓ g0f (x - y)) := by
              simpa [g0f] using (kernel_fibre hℓ hwi x)
  have hmono : (∫ y : ℝ³, chiScale ℓ y * wScaled ℓ g0f (x - y))
      ≥ ∫ y : ℝ³, chiScale ℓ y * g0f (x - y) := by
    have hle : ∀ᵐ y ∂(volume : Measure ℝ³),
        chiScale ℓ y * wScaled ℓ g0f (x - y) ≥ chiScale ℓ y * g0f (x - y) := by
      have hws : ∀ᵐ y ∂(volume : Measure ℝ³), g0f (x - y) ≤ wScaled ℓ g0f (x - y) := by
        simpa [g0f] using (g0_le_wScaled_ae (v := v) (R := R) hR hv_nonneg hvrad hv_supp h hℓ hRℓ x)
      filter_upwards [hws] with y hy
      exact mul_le_mul_of_nonneg_left hy (chi_nonneg ((ℓ⁻¹) • y))
    have hLHS : MeasureTheory.Integrable (fun y : ℝ³ =>
        chiScale ℓ y * wScaled ℓ g0f (x - y)) := kernel_fibre_integrable hℓ hwi x
    have hRHS : MeasureTheory.Integrable (fun y : ℝ³ =>
        chiScale ℓ y * g0f (x - y)) := by
      have hg0c : MeasureTheory.Integrable (fun y : ℝ³ => g0f (x - y)) :=
        km_integrable_comp_sub_left hg0i x
      have hbnd : ∀ᵐ y ∂(volume : Measure ℝ³),
          ‖chiScale ℓ y * g0f (x - y)‖ ≤ chiSup * |g0f (x - y)| := by
        refine ae_of_all _ (fun y => ?_)
        calc
          ‖chiScale ℓ y * g0f (x - y)‖ = |chiScale ℓ y * g0f (x - y)| := by
                  rw [Real.norm_eq_abs]
          _ = |chiScale ℓ y| * |g0f (x - y)| := by rw [abs_mul]
          _ ≤ chiSup * |g0f (x - y)| := by
            exact mul_le_mul_of_nonneg_right (abs_chiScale_le_chiSup ℓ y) (abs_nonneg _)
      have hcm : AEStronglyMeasurable (fun y : ℝ³ => chiScale ℓ y) volume :=
        (chiScale_continuous ℓ).aestronglyMeasurable
      have hg0m : AEStronglyMeasurable (fun y : ℝ³ => g0f (x - y)) volume :=
        km_aestronglyMeasurable_comp_sub_left hg0i.aestronglyMeasurable x
      exact MeasureTheory.Integrable.mono' (hg0c.abs.const_mul chiSup) (hcm.mul hg0m) hbnd
    exact integral_mono_ae hRHS hLHS hle
  have href : (∫ y : ℝ³, chiScale ℓ y * g0f (x - y))
      = ∫ y : ℝ³, g0f y * chiScale ℓ (x - y) := by
    have hg := integral_comp_sub_left
      (g := fun w : ℝ³ => g0f w * chiScale ℓ (x - w)) x
    calc
      (∫ y : ℝ³, chiScale ℓ y * g0f (x - y))
          = ∫ y : ℝ³, g0f (x - y) * chiScale ℓ y := by
              apply integral_congr_ae
              refine ae_of_all _ (fun y => ?_)
              ring
      _ = ∫ y : ℝ³, g0f y * chiScale ℓ (x - y) := by
              simpa [mul_comm, mul_left_comm, mul_assoc] using hg
  have hJ : chiScale ℓ x * (∫ y : ℝ³, g0f y) - E
      ≤ ∫ y : ℝ³, g0f y * chiScale ℓ (x - y) := by
    have hJint : MeasureTheory.Integrable (fun y : ℝ³ =>
        g0f y * chiScale ℓ (x - y)) := by
      have hbnd : ∀ᵐ y ∂(volume : Measure ℝ³),
          ‖g0f y * chiScale ℓ (x - y)‖ ≤ |g0f y| * chiSup := by
        refine ae_of_all _ (fun y => ?_)
        calc
          ‖g0f y * chiScale ℓ (x - y)‖ = |g0f y * chiScale ℓ (x - y)| := by
                  rw [Real.norm_eq_abs]
          _ = |g0f y| * |chiScale ℓ (x - y)| := by rw [abs_mul]
          _ ≤ |g0f y| * chiSup := by
            exact mul_le_mul_of_nonneg_left (abs_chiScale_le_chiSup ℓ (x - y)) (abs_nonneg _)
      have hg0m : AEStronglyMeasurable g0f volume := hg0i.aestronglyMeasurable
      have hcm : AEStronglyMeasurable (fun y : ℝ³ => chiScale ℓ (x - y)) volume :=
        (chiScale_continuous ℓ).comp (continuous_const.sub continuous_id) |>.aestronglyMeasurable
      exact MeasureTheory.Integrable.mono' (hg0i.abs.mul_const chiSup) (hg0m.mul hcm) hbnd
    have hcst : MeasureTheory.Integrable (fun y : ℝ³ => g0f y * chiScale ℓ x) :=
      hg0i.mul_const (chiScale ℓ x)
    have hdiff : (∫ y : ℝ³, g0f y * (chiScale ℓ (x - y) - chiScale ℓ x))
        = (∫ y : ℝ³, g0f y * chiScale ℓ (x - y))
          - chiScale ℓ x * (∫ y : ℝ³, g0f y) := by
      calc
        (∫ y : ℝ³, g0f y * (chiScale ℓ (x - y) - chiScale ℓ x))
            = ∫ y : ℝ³, g0f y * chiScale ℓ (x - y) - g0f y * chiScale ℓ x := by
                apply integral_congr_ae
                refine ae_of_all _ (fun y => ?_)
                ring
        _ = (∫ y : ℝ³, g0f y * chiScale ℓ (x - y))
            - (∫ y : ℝ³, g0f y * chiScale ℓ x) := by
                rw [← integral_sub hJint hcst]
        _ = (∫ y : ℝ³, g0f y * chiScale ℓ (x - y))
            - chiScale ℓ x * (∫ y : ℝ³, g0f y) := by
                rw [integral_mul_const]
                ring
    have habs : |∫ y : ℝ³, g0f y * (chiScale ℓ (x - y) - chiScale ℓ x)|
        ≤ Cχ * (R / ℓ) ^ 2 * (∫ y : ℝ³, |g0f y|) := by
      simpa using hconv
    have hge : - (Cχ * (R / ℓ) ^ 2 * (∫ y : ℝ³, |g0f y|))
        ≤ (∫ y : ℝ³, g0f y * (chiScale ℓ (x - y) - chiScale ℓ x)) :=
      (abs_le.mp habs).1
    have hE' : Cχ * (R / ℓ) ^ 2 * (∫ y : ℝ³, |g0f y|) = E := by
      rw [hg0abs]
    linarith
  have hχ : 0 ≤ chiScale ℓ x := chi_nonneg ((ℓ⁻¹) • x)
  have hχle : chiScale ℓ x ≤ chiSup := by
    have h := abs_chiScale_le_chiSup ℓ x
    rwa [abs_of_nonneg hχ] at h
  have hfin : chiScale ℓ x * (∫ y : ℝ³, chiScale ℓ y * wScaled ℓ g0f (x - y))
      ≥ (8 * π * a v) * (chiScale ℓ x) ^ 2 - chiSup * E := by
    have hstep1 : chiScale ℓ x * (∫ y : ℝ³, chiScale ℓ y * wScaled ℓ g0f (x - y))
        ≥ chiScale ℓ x * (∫ y : ℝ³, chiScale ℓ y * g0f (x - y)) :=
      mul_le_mul_of_nonneg_left hmono hχ
    have hstep2 : chiScale ℓ x * (∫ y : ℝ³, chiScale ℓ y * g0f (x - y))
        ≥ chiScale ℓ x * (chiScale ℓ x * (∫ y : ℝ³, g0f y) - E) := by
      rw [href]
      exact mul_le_mul_of_nonneg_left hJ hχ
    have hstep4 : (chiScale ℓ x) ^ 2 * (∫ y : ℝ³, g0f y) - chiScale ℓ x * E
        ≥ (8 * π * a v) * (chiScale ℓ x) ^ 2 - chiSup * E := by
      rw [hg0int]
      have hb1 : chiScale ℓ x * E ≤ chiSup * E := mul_le_mul_of_nonneg_right hχle hEnn
      have hb2 : (8 * π * a v) * (chiScale ℓ x) ^ 2 = (chiScale ℓ x) ^ 2 * (8 * π * a v) := by
        ring
      rw [← hb2]
      linarith
    calc
      chiScale ℓ x * (∫ y : ℝ³, chiScale ℓ y * wScaled ℓ g0f (x - y))
          ≥ chiScale ℓ x * (chiScale ℓ x * (∫ y : ℝ³, g0f y) - E) := le_trans hstep2 hstep1
      _ = (chiScale ℓ x) ^ 2 * (∫ y : ℝ³, g0f y) - chiScale ℓ x * E := by ring
      _ ≥ (8 * π * a v) * (chiScale ℓ x) ^ 2 - chiSup * E := hstep4
  rw [hfibE]
  have hEdef : chiSup * Cχ * (R / ℓ) ^ 2 * (8 * π * a v) = chiSup * E := by
    dsimp [E]
    ring
  rw [hEdef]
  exact hfin



/-- **Pointwise fibre lower bound with the corpus Taylor constant**:
instantiating `w1Fibre_pointwise_lower` at `Cχ := chiTaylorC`. -/
lemma w1Fibre_pointwise_lower_taylor {v : ℝ³ → ℝ} {R ℓ : ℝ} (hR : 0 < R)
    (hv_nonneg : 0 ≤ v) (hvrad : IsRadial v)
    (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v)
    (hℓ : 0 < ℓ) (hRℓ : R ≤ ℓ * chiR0) (x : ℝ³) :
    (8 * π * a v) * (chiScale ℓ x) ^ 2 - chiSup * chiTaylorC * (R / ℓ) ^ 2 * (8 * π * a v)
      ≤ w1Fibre ℓ (wPairC ℓ (g0 v h)) x := by
  exact w1Fibre_pointwise_lower (v := v) (R := R) (ℓ := ℓ) (Cχ := chiTaylorC) hR
    hv_nonneg hvrad hv_supp h hℓ hRℓ chiTaylorC_spec.1 chiTaylorC_spec.2 x


/-- First-slot fibre of the symmetric `w₂ := wPairC(g2)` equals its second-slot
`w1Fibre`: `∫_y w₂(y,z)dy = w1Fibre(wPairC(g2)) z` (pointwise symmetry from
`g2_even`, no integrability needed).  This is the fibre that the peel of the
T₂-mass produces when integrating out the `P`-coordinate (S2 pair identity). -/
lemma w2_fibre_first_slot_eq {ℓ : ℝ} {v : ℝ³ → ℝ} (hvrad : IsRadial v)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v) (z : ℝ³) :
    (∫ y in acube ℓ, wPair ℓ (g2 v h) y z) = w1Fibre ℓ (wPairC ℓ (g2 v h)) z := by
  calc
    (∫ y in acube ℓ, wPair ℓ (g2 v h) y z)
        = ∫ y in acube ℓ, wPair ℓ (g2 v h) z y := by
            apply integral_congr_ae
            refine ae_of_all _ (fun y => ?_)
            exact (wPairC_sym (g2_even hvrad h) ℓ y z)
    _ = w1Fibre ℓ (wPairC ℓ (g2 v h)) z := by
            simp [w1Fibre, wPairC]

end BoseGases

end Submission
