import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Submission.Work.BoseBoxFock.errKafz_dominates_uniform
import Submission.Work.BoseBoxFock.pairRowWordParts
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.q2wordAux` — helper layer for the word/mass-row comparison

Vocabulary and elementary lemmas used by the proof of
`Work.BoseBoxFock.q2wordGeWordParts` (the word-side half (B) of the `Q₂`
dictionary: `rowWordPartsH ≤ q2word + ½ errKafz·normB`).
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators

namespace Work.BoseBoxFock

open _root_.BoseGases
open Submission.BoseGases

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## 1. Box-side bookkeeping -/

/-- `ellH v μ = sideAt μ (a v)` for `0 < μ`, `0 < a v`. -/
theorem ellH_eq_sideAt_of_pos {v : ℝ³ → ℝ} {μ : ℝ} (hμ : 0 < μ) (hav : 0 < a v) :
    ellH v μ = Work.BoseBox.sideAt μ (a v) := by
  simp only [ellH, if_pos (Work.BoseBox.sideAt_pos hμ hav)]

/-- The two spellings of the box norm square coincide. -/
theorem normB_eq_norm2N {v : ℝ³ → ℝ} {μ : ℝ} {n : ℕ} (Φ : Submission.BoseGases.X n → ℝ) :
    Work.BoseBoxFix.normB v μ n Φ = Work.BoseBox.norm2N n (Work.BoseBox.sideAt μ (a v)) Φ :=
  rfl

/-! ## 2. `chat` at zero -/

/-- `chat W 0 = ∫ W`: the `p`-Fourier transform at the origin is the total mass. -/
theorem chat_zero (W : ℝ³ → ℝ) : Work.BoseFixR.chat W 0 = ∫ z : ℝ³, W z := by
  have h : Submission.BoseGases.kinFT (fun y : ℝ³ => ((W y : ℝ) : ℂ)) (0 : ℝ³)
      = ((∫ z : ℝ³, W z : ℝ) : ℂ) := by
    simp only [Submission.BoseGases.kinFT, inner_zero_left, Complex.ofReal_zero, mul_zero,
      neg_zero, Complex.exp_zero, one_mul]
    exact integral_complex_ofReal
  simpa only [Work.BoseFixR.chat, Complex.ofReal_re] using congrArg Complex.re h

/-! ## 3. Linearity of `wScaled` and the `g₂`-decomposition -/

/-- `wScaled ℓ` is additive in the numerator. -/
theorem wScaled_add (ℓ : ℝ) (f g : ℝ³ → ℝ) :
    wScaled ℓ (fun z => f z + g z) = fun z => wScaled ℓ f z + wScaled ℓ g z := by
  funext z
  simp only [wScaled, div_eq_mul_inv]
  ring

/-- `wScaled ℓ (fun z => c * f z) = fun z => wScaled ℓ f z * c`. -/
theorem wScaled_const_mul (ℓ c : ℝ) (f : ℝ³ → ℝ) :
    wScaled ℓ (fun z => c * f z) = fun z => wScaled ℓ f z * c := by
  funext z
  simp only [wScaled, div_eq_mul_inv]
  ring

/-- `g₂ = g₀ + g₀ω₀` pointwise (with `ω₀ = Classical.choose h`). -/
theorem g2_eq_g0_add_g0w0 (v : ℝ³ → ℝ)
    (h : ∃ w : ℝ³ → ℝ, BoseGases.IsRadial w ∧ BoseGases.IsScatteringSolution w v) :
    g2 v h = fun z => g0 v h z + g0 v h z * Classical.choose h z := by
  funext z
  simp only [g2, g0]
  ring

/-- `wScaled ℓ (g₂ v h) = wScaled ℓ (g₀ v h) + wScaled ℓ (g₀ω₀)`. -/
theorem wScaled_g2_eq_add (v : ℝ³ → ℝ)
    (h : ∃ w : ℝ³ → ℝ, BoseGases.IsRadial w ∧ BoseGases.IsScatteringSolution w v) (ℓ : ℝ) :
    wScaled ℓ (g2 v h)
      = fun z => wScaled ℓ (g0 v h) z + wScaled ℓ (fun y => g0 v h y * Classical.choose h y) z := by
  rw [g2_eq_g0_add_g0w0 v h, wScaled_add]

/-! ## 4. Weighted `P`-orthogonality -/

/-- **Weighted `P`-self-pairing**: for `i ≠ j` and a weight depending only on slot `i`,
`∫ (P_jΨ)·Ψ·w(x_i) = ∫ (P_jΨ)²·w(x_i)`.

Obtained from `aP_sym_weight` by writing `Ψ = P_jΨ + Q_jΨ`: the cross term vanishes
because `P_j(Q_jΨ) = 0`. -/
theorem P_self_weighted {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {i j : Fin N} (hij : i ≠ j)
    {w : ℝ³ → ℝ} {Cw : ℝ}
    (hwm : AEStronglyMeasurable w (volume.restrict (acube ℓ)))
    (hwb : ∀ z : ℝ³, z ∈ acube ℓ → |w z| ≤ Cw)
    {Ψ : Submission.BoseGases.X N → ℝ} (hΨc : Continuous Ψ) :
    (∫ x in abox N ℓ, (aP ℓ j Ψ x) * Ψ x * w (x i))
      = ∫ x in abox N ℓ, (aP ℓ j Ψ x) ^ 2 * w (x i) := by
  have hPc : Continuous (aP ℓ j Ψ) := aP_continuous hℓ j hΨc
  have hQc : Continuous (aQ ℓ j Ψ) := aQ_continuous hℓ j hΨc
  have hcross : (∫ x in abox N ℓ, (aP ℓ j Ψ x) * (aQ ℓ j Ψ x) * w (x i)) = 0 := by
    have hsym := aP_sym_weight (N := N) (ℓ := ℓ) hℓ (i := i) (j := j) hij w hwm hwb
      (Φ := Ψ) (Ψ := aQ ℓ j Ψ) hΨc hQc
    have h0 : (∫ x in abox N ℓ, Ψ x * (w (x i) * aP ℓ j (aQ ℓ j Ψ) x)) = 0 := by
      rw [show (fun x : Submission.BoseGases.X N =>
            Ψ x * (w (x i) * aP ℓ j (aQ ℓ j Ψ) x)) = (fun _ => (0 : ℝ)) from
          funext (fun x => by rw [aP_aQ_zero hℓ j hΨc x]; ring)]
      simp
    have h1 : (∫ x in abox N ℓ, (aP ℓ j Ψ x) * (aQ ℓ j Ψ x) * w (x i))
        = ∫ x in abox N ℓ, (aP ℓ j Ψ x) * (w (x i) * aQ ℓ j Ψ x) := by
      apply integral_congr_ae
      filter_upwards with x
      ring
    rw [h1, hsym, h0]
  have hI1 : IntegrableOn (fun x : Submission.BoseGases.X N => (aP ℓ j Ψ x) ^ 2 * w (x i))
      (abox N ℓ) volume := by
    have h := integrableOn_slot_fibre (N := N) hℓ i hwm hwb (S := fun x => (aP ℓ j Ψ x) ^ 2)
      (hPc.pow 2)
    simpa [mul_comm] using h
  have hI2 : IntegrableOn
      (fun x : Submission.BoseGases.X N => (aP ℓ j Ψ x) * (aQ ℓ j Ψ x) * w (x i))
      (abox N ℓ) volume := by
    have h := integrableOn_slot_fibre (N := N) hℓ i hwm hwb
      (S := fun x => (aP ℓ j Ψ x) * (aQ ℓ j Ψ x)) (hPc.mul hQc)
    simpa [mul_assoc] using h
  have hsplit : (∫ x in abox N ℓ, (aP ℓ j Ψ x) * Ψ x * w (x i))
      = (∫ x in abox N ℓ, (aP ℓ j Ψ x) ^ 2 * w (x i))
        + (∫ x in abox N ℓ, (aP ℓ j Ψ x) * (aQ ℓ j Ψ x) * w (x i)) := by
    rw [← integral_add hI1 hI2]
    apply integral_congr_ae
    filter_upwards with x
    have hx : Ψ x = aP ℓ j Ψ x + aQ ℓ j Ψ x := by
      simp only [aQ]
      ring
    rw [hx]
    ring
  rw [hsplit, hcross, add_zero]

/-! ## 5. `errKafz` dominates `μ·a` -/

/-- `μ·a v ≤ errKafz v R μ 1` (the `K_ℓ⁻³`-slot of the bracket equals `μa v`), from the proved
`errKafz_ge`. -/
theorem mu_a_le_errKafz (v : ℝ³ → ℝ) (R : ℝ) {μ : ℝ} (hμ : 0 < μ) (hav : 0 < a v) :
    μ * a v ≤ Work.BoseFixR.errKafz v R μ 1 := by
  simpa using errKafz_ge v hμ hav (by norm_num : (0 : ℝ) ≤ 1)

/-! ## 6. The `wScaled` mass bounds -/

/-- A.e. bound `|wScaled ℓ g| ≤ 2·g` for `g ≥ 0` a.e. supported in `ball 0 R`
(`convScale ≥ 1/2` on the support of `g` in the dilute regime). -/
theorem abs_wScaled_le_two_mul {g : ℝ³ → ℝ} {R ℓ : ℝ} (hR : 0 < R) (hℓ : 0 < ℓ)
    (hRℓ : R ≤ ℓ * chiR0)
    (hg0 : ∀ᵐ z : ℝ³, 0 ≤ g z) (hgsupp : ∀ z : ℝ³, R ≤ ‖z‖ → g z = 0) :
    ∀ᵐ z : ℝ³, |wScaled ℓ g z| ≤ 2 * g z := by
  filter_upwards [hg0] with z hz
  by_cases hzt : g z = 0
  · simp only [wScaled, hzt, zero_div, abs_zero, mul_zero, le_refl]
  · have hzpos : 0 < g z := lt_of_le_of_ne hz (Ne.symm hzt)
    have hzR : ‖z‖ < R := by
      by_contra hn
      exact hzpos.ne' (hgsupp z (le_of_not_gt hn))
    have hcs : 1 / 2 ≤ convScale ℓ z := convScale_ge_half_ball hℓ hR.le hRℓ (le_of_lt hzR)
    have hcs0 : 0 < convScale ℓ z := by linarith
    simp only [wScaled]
    rw [abs_of_nonneg (div_nonneg (le_of_lt hzpos) (le_of_lt hcs0)), div_le_iff₀ hcs0]
    nlinarith

/-- `∫ |wScaled ℓ g| ≤ 2∫g` for `g ≥ 0` a.e. supported in `ball 0 R`. -/
theorem integral_abs_wScaled_le {g : ℝ³ → ℝ} {R ℓ : ℝ} (hR : 0 < R) (hℓ : 0 < ℓ)
    (hRℓ : R ≤ ℓ * chiR0) (hgi : Integrable g)
    (hg0 : ∀ᵐ z : ℝ³, 0 ≤ g z) (hgsupp : ∀ z : ℝ³, R ≤ ‖z‖ → g z = 0) :
    (∫ z : ℝ³, |wScaled ℓ g z|) ≤ 2 * ∫ z : ℝ³, g z := by
  have hwI : Integrable (fun z : ℝ³ => wScaled ℓ g z) :=
    wScaled_integrable_ae hℓ hR.le hRℓ hgi hgsupp
  have hmono : (∫ z : ℝ³, |wScaled ℓ g z|) ≤ ∫ z : ℝ³, 2 * g z :=
    integral_mono_ae hwI.abs (hgi.const_mul 2) (abs_wScaled_le_two_mul hR hℓ hRℓ hg0 hgsupp)
  rw [integral_const_mul] at hmono
  linarith

/-- `∫ |wScaled ℓ (g₀ v h)| ≤ 16π(a v)`. -/
theorem abs_wScaled_g0_le {v : ℝ³ → ℝ} (h : Work.UBB.ScatSol v) {R ℓ : ℝ} (hR : 0 < R)
    (hv : 0 ≤ v) (hvrad : _root_.BoseGases.IsRadial v) (hv_supp : tsupport v ⊆ Metric.ball (0 : ℝ³) R)
    (hℓ : 0 < ℓ) (hRℓ : R ≤ ℓ * chiR0) :
    (∫ z : ℝ³, |wScaled ℓ (g0 v h) z|) ≤ 16 * π * a v := by
  have hb := integral_abs_wScaled_le (g := g0 v h) hR hℓ hRℓ (g0_integrable hR hv_supp h)
    (g0_nonneg_ae hR hv hvrad hv_supp h) (fun z hz => g0_zero_of_norm_ge hv_supp hz h)
  rw [g0_integral hR hv_supp h] at hb
  linarith

/-- `∫ |wScaled ℓ (g₂ v h)| ≤ 32π(a v)`. -/
theorem abs_wScaled_g2_le {v : ℝ³ → ℝ} (h : Work.UBB.ScatSol v) {R ℓ : ℝ} (hR : 0 < R)
    (hv : 0 ≤ v) (hvrad : _root_.BoseGases.IsRadial v) (hv_supp : tsupport v ⊆ Metric.ball (0 : ℝ³) R)
    (hℓ : 0 < ℓ) (hRℓ : R ≤ ℓ * chiR0) :
    (∫ z : ℝ³, |wScaled ℓ (g2 v h) z|) ≤ 32 * π * a v := by
  have hb := integral_abs_wScaled_le (g := g2 v h) hR hℓ hRℓ (g2_integrable hR hv hvrad hv_supp h)
    (g2_nonneg_ae hR hv hvrad hv_supp h) (fun z hz => g2_zero_of_norm_ge hv_supp hz h)
  have hg2 : (∫ z : ℝ³, g2 v h z) = 8 * π * a v + g0w0Mass (v := v) h :=
    g2_integral_eq_av_add_g0w0 hR hv hvrad hv_supp h
  rw [hg2] at hb
  have hω : g0w0Mass (v := v) h ≤ 8 * π * a v := by
    have hbnds := chosen_w0_bounds_ae (v := v) hR hv hvrad hv_supp h
    have hnn : ∀ᵐ z : ℝ³, 0 ≤ g0 v h z * Classical.choose h z := by
      filter_upwards [g0_nonneg_ae hR hv hvrad hv_supp h, hbnds.1] with z h1 h2
      exact mul_nonneg h1 h2
    have hle : ∀ᵐ z : ℝ³, g0 v h z * Classical.choose h z ≤ g0 v h z := by
      filter_upwards [g0_nonneg_ae hR hv hvrad hv_supp h, hbnds.2] with z h1 h2
      nlinarith
    have hmono : (∫ z : ℝ³, g0 v h z * Classical.choose h z) ≤ ∫ z : ℝ³, g0 v h z :=
      integral_mono_ae (g0w0_integrable hR hv hvrad hv_supp h) (g0_integrable hR hv_supp h) hle
    rw [g0_integral hR hv_supp h] at hmono
    exact hmono
  linarith

/-! ## 7. The slot-square bound `Σᵢⱼ∫(aP_j(aQ_iΨ))² ≤ N·cnPlus` -/

theorem sum_sq_le {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ)
    {Ψ : Submission.BoseGases.X N → ℝ} (hΨc : Continuous Ψ) :
    (∑ i : Fin N, ∑ j : Fin N,
        ∫ x in Submission.BoseGases.abox N ℓ,
          (Submission.BoseGases.aP ℓ j (Submission.BoseGases.aQ ℓ i Ψ) x) ^ 2)
      ≤ N * Submission.BoseGases.cnPlus ℓ Ψ := by
  have hstep : ∀ i : Fin N,
      (∑ j : Fin N, ∫ x in Submission.BoseGases.abox N ℓ,
          (Submission.BoseGases.aP ℓ j (Submission.BoseGases.aQ ℓ i Ψ) x) ^ 2)
        ≤ N * ∫ x in Submission.BoseGases.abox N ℓ,
            (Submission.BoseGases.aQ ℓ i Ψ x) ^ 2 := by
    intro i
    have hQc : Continuous (Submission.BoseGases.aQ ℓ i Ψ) :=
      Submission.BoseGases.aQ_continuous hℓ i hΨc
    calc (∑ j : Fin N, ∫ x in Submission.BoseGases.abox N ℓ,
            (Submission.BoseGases.aP ℓ j (Submission.BoseGases.aQ ℓ i Ψ) x) ^ 2)
        ≤ ∑ j : Fin N, ∫ x in Submission.BoseGases.abox N ℓ,
            (Submission.BoseGases.aQ ℓ i Ψ x) ^ 2 :=
          Finset.sum_le_sum (fun j _ => Submission.BoseGases.aP_sq_le hℓ j hQc)
      _ = N * ∫ x in Submission.BoseGases.abox N ℓ,
            (Submission.BoseGases.aQ ℓ i Ψ x) ^ 2 := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  calc (∑ i : Fin N, ∑ j : Fin N, ∫ x in Submission.BoseGases.abox N ℓ,
          (Submission.BoseGases.aP ℓ j (Submission.BoseGases.aQ ℓ i Ψ) x) ^ 2)
      ≤ ∑ i : Fin N, N * ∫ x in Submission.BoseGases.abox N ℓ,
          (Submission.BoseGases.aQ ℓ i Ψ x) ^ 2 := Finset.sum_le_sum (fun i _ => hstep i)
    _ = N * ∑ i : Fin N, ∫ x in Submission.BoseGases.abox N ℓ,
          (Submission.BoseGases.aQ ℓ i Ψ x) ^ 2 := by rw [Finset.mul_sum]
    _ = N * Submission.BoseGases.cnPlus ℓ Ψ := by rfl

/-! ## 8. Positivity of `wScaled` for nonnegative numerators -/

/-- `0 ≤ wScaled ℓ g` a.e. for `g ≥ 0` a.e. supported in `ball 0 R`. -/
theorem wScaled_nonneg_ae {g : ℝ³ → ℝ} {R ℓ : ℝ} (hR : 0 < R) (hℓ : 0 < ℓ)
    (hRℓ : R ≤ ℓ * chiR0)
    (hg0 : ∀ᵐ z : ℝ³, 0 ≤ g z) (hgsupp : ∀ z : ℝ³, R ≤ ‖z‖ → g z = 0) :
    ∀ᵐ z : ℝ³, 0 ≤ wScaled ℓ g z := by
  filter_upwards [hg0] with z hz
  by_cases hzt : g z = 0
  · simp only [wScaled, hzt, zero_div, le_refl]
  · have hzpos : 0 < g z := lt_of_le_of_ne hz (Ne.symm hzt)
    have hzR : ‖z‖ < R := by
      by_contra hn
      exact hzpos.ne' (hgsupp z (le_of_not_gt hn))
    have hcs : 1 / 2 ≤ convScale ℓ z := convScale_ge_half_ball hℓ hR.le hRℓ (le_of_lt hzR)
    simp only [wScaled]
    exact div_nonneg (le_of_lt hzpos) (by linarith)

/-- `0 ≤ ∫ wScaled ℓ g` for `g ≥ 0` a.e. supported in `ball 0 R`. -/
theorem wScaled_integral_nonneg {g : ℝ³ → ℝ} {R ℓ : ℝ} (hR : 0 < R) (hℓ : 0 < ℓ)
    (hRℓ : R ≤ ℓ * chiR0)
    (hg0 : ∀ᵐ z : ℝ³, 0 ≤ g z) (hgsupp : ∀ z : ℝ³, R ≤ ‖z‖ → g z = 0) :
    0 ≤ ∫ z : ℝ³, wScaled ℓ g z :=
  integral_nonneg_of_ae (wScaled_nonneg_ae hR hℓ hRℓ hg0 hgsupp)

/-! ## 9. The summed *upper* slot-fibre bound -/

/-- **Summed upper fibre bound**: if `fib z ≤ M·χ(z)² + e` for all `z` (with `fib` aem and
bounded on the cube), then

    Σᵢ ∫_{abox} (Q_iΨ)²·fib(x_i) ≤ M·Σᵢ∫_{abox}(Q_iΨ)²·χ(x_i)² + e·cnPlus ℓ Ψ. -/
theorem sum_slot_upper {N : ℕ} {ℓ M e Cw : ℝ} (hℓ : 0 < ℓ)
    {Ψ : Submission.BoseGases.X N → ℝ} (hΨc : Continuous Ψ)
    {fib : ℝ³ → ℝ}
    (hfibm : AEStronglyMeasurable fib (volume.restrict (Submission.BoseGases.acube ℓ)))
    (hfibb : ∀ z : ℝ³, z ∈ Submission.BoseGases.acube ℓ → |fib z| ≤ Cw)
    (hfib : ∀ z : ℝ³, fib z ≤ M * (Submission.BoseGases.chiScale ℓ z) ^ 2 + e) :
    (∑ i : Fin N, ∫ x in Submission.BoseGases.abox N ℓ,
        (Submission.BoseGases.aQ ℓ i Ψ x) ^ 2 * fib (x i))
      ≤ M * (∑ i : Fin N, ∫ x in Submission.BoseGases.abox N ℓ,
            (Submission.BoseGases.aQ ℓ i Ψ x) ^ 2
              * (Submission.BoseGases.chiScale ℓ (x i)) ^ 2)
        + e * Submission.BoseGases.cnPlus ℓ Ψ := by
  have hper : ∀ i : Fin N,
      (∫ x in Submission.BoseGases.abox N ℓ,
          (Submission.BoseGases.aQ ℓ i Ψ x) ^ 2 * fib (x i))
        ≤ M * (∫ x in Submission.BoseGases.abox N ℓ,
              (Submission.BoseGases.aQ ℓ i Ψ x) ^ 2
                * (Submission.BoseGases.chiScale ℓ (x i)) ^ 2)
          + e * (∫ x in Submission.BoseGases.abox N ℓ,
              (Submission.BoseGases.aQ ℓ i Ψ x) ^ 2) := by
    intro i
    have hQc : Continuous (Submission.BoseGases.aQ ℓ i Ψ) :=
      Submission.BoseGases.aQ_continuous hℓ i hΨc
    have hχcont : Continuous (fun x : Submission.BoseGases.X N =>
        (Submission.BoseGases.chiScale ℓ (x i)) ^ 2) :=
      ((Submission.BoseGases.chiScale_continuous ℓ).comp (continuous_apply i)).pow 2
    have hIfib : IntegrableOn (fun x : Submission.BoseGases.X N =>
        (Submission.BoseGases.aQ ℓ i Ψ x) ^ 2 * fib (x i))
        (Submission.BoseGases.abox N ℓ) volume :=
      Submission.BoseGases.integrableOn_slot_fibre hℓ i hfibm hfibb (hQc.pow 2)
    have hIrhs : IntegrableOn
        (fun x : Submission.BoseGases.X N => (Submission.BoseGases.aQ ℓ i Ψ x) ^ 2
          * (M * (Submission.BoseGases.chiScale ℓ (x i)) ^ 2 + e))
        (Submission.BoseGases.abox N ℓ) volume :=
      Submission.BoseGases.integrableOn_abox_of_continuous hℓ
        ((hQc.pow 2).mul ((continuous_const.mul hχcont).add continuous_const))
    have hmono : (∫ x in Submission.BoseGases.abox N ℓ,
          (Submission.BoseGases.aQ ℓ i Ψ x) ^ 2 * fib (x i))
        ≤ ∫ x in Submission.BoseGases.abox N ℓ,
          (Submission.BoseGases.aQ ℓ i Ψ x) ^ 2
            * (M * (Submission.BoseGases.chiScale ℓ (x i)) ^ 2 + e) :=
      integral_mono hIfib hIrhs (fun x => by
        exact mul_le_mul_of_nonneg_left (hfib (x i)) (sq_nonneg _))
    have hsplit : (∫ x in Submission.BoseGases.abox N ℓ,
          (Submission.BoseGases.aQ ℓ i Ψ x) ^ 2
            * (M * (Submission.BoseGases.chiScale ℓ (x i)) ^ 2 + e))
        = M * (∫ x in Submission.BoseGases.abox N ℓ,
              (Submission.BoseGases.aQ ℓ i Ψ x) ^ 2
                * (Submission.BoseGases.chiScale ℓ (x i)) ^ 2)
          + e * (∫ x in Submission.BoseGases.abox N ℓ,
              (Submission.BoseGases.aQ ℓ i Ψ x) ^ 2) := by
      rw [show (fun x : Submission.BoseGases.X N => (Submission.BoseGases.aQ ℓ i Ψ x) ^ 2
            * (M * (Submission.BoseGases.chiScale ℓ (x i)) ^ 2 + e))
          = (fun x : Submission.BoseGases.X N =>
              M * ((Submission.BoseGases.aQ ℓ i Ψ x) ^ 2
                  * (Submission.BoseGases.chiScale ℓ (x i)) ^ 2)
                + e * (Submission.BoseGases.aQ ℓ i Ψ x) ^ 2) from
          funext (fun x => by ring)]
      rw [integral_add]
      · rw [integral_const_mul, integral_const_mul]
      · exact Submission.BoseGases.integrableOn_abox_of_continuous hℓ
          (continuous_const.mul ((hQc.pow 2).mul hχcont))
      · exact Submission.BoseGases.integrableOn_abox_of_continuous hℓ
          (continuous_const.mul (hQc.pow 2))
    calc (∫ x in Submission.BoseGases.abox N ℓ,
          (Submission.BoseGases.aQ ℓ i Ψ x) ^ 2 * fib (x i))
        ≤ (∫ x in Submission.BoseGases.abox N ℓ,
            (Submission.BoseGases.aQ ℓ i Ψ x) ^ 2
              * (M * (Submission.BoseGases.chiScale ℓ (x i)) ^ 2 + e)) := hmono
      _ = M * (∫ x in Submission.BoseGases.abox N ℓ,
              (Submission.BoseGases.aQ ℓ i Ψ x) ^ 2
                * (Submission.BoseGases.chiScale ℓ (x i)) ^ 2)
          + e * (∫ x in Submission.BoseGases.abox N ℓ,
              (Submission.BoseGases.aQ ℓ i Ψ x) ^ 2) := hsplit
  calc (∑ i : Fin N, ∫ x in Submission.BoseGases.abox N ℓ,
        (Submission.BoseGases.aQ ℓ i Ψ x) ^ 2 * fib (x i))
      ≤ ∑ i : Fin N, (M * (∫ x in Submission.BoseGases.abox N ℓ,
            (Submission.BoseGases.aQ ℓ i Ψ x) ^ 2
              * (Submission.BoseGases.chiScale ℓ (x i)) ^ 2)
          + e * (∫ x in Submission.BoseGases.abox N ℓ,
            (Submission.BoseGases.aQ ℓ i Ψ x) ^ 2)) :=
        Finset.sum_le_sum (fun i _ => hper i)
    _ = M * (∑ i : Fin N, ∫ x in Submission.BoseGases.abox N ℓ,
            (Submission.BoseGases.aQ ℓ i Ψ x) ^ 2
              * (Submission.BoseGases.chiScale ℓ (x i)) ^ 2)
          + e * (∑ i : Fin N, ∫ x in Submission.BoseGases.abox N ℓ,
              (Submission.BoseGases.aQ ℓ i Ψ x) ^ 2) := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    _ = M * (∑ i : Fin N, ∫ x in Submission.BoseGases.abox N ℓ,
            (Submission.BoseGases.aQ ℓ i Ψ x) ^ 2
              * (Submission.BoseGases.chiScale ℓ (x i)) ^ 2)
          + e * Submission.BoseGases.cnPlus ℓ Ψ := by
        rfl

end Work.BoseBoxFock
