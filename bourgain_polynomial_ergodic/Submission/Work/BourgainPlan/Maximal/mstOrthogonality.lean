import Mathlib
import Submission.Work.BourgainPlan.Maximal.level_l2_mst_large_n_aux_defs
import Submission.Work.BourgainPlan.Maximal.mstEta_arcSum_le
import Submission.Work.BourgainPlan.Maximal.mstTorsion
import Submission.Work.Maximal.mstOrtho.ftLp_mstModSeq
import Submission.Work.Maximal.mstOrtho.range_fourier_sq_sum
import Submission.Work.BourgainPlan.IonescuWainger.opArc_l2

/-!
# The diagonalisation of the arc sum by the `u`-average

The MST §4.3 step "(iv)": averaging the `Φ`-free model over the shifts `u ∈ ℕ_{Q_s}` carries the
Gauss decay `(s+1)^{−δl}G0` exactly once, because the characters `u ↦ e^{2πi u β}`, `β ∈ E_s`, are
orthogonal on `ℤ/Q_s` (`mstTorsion`), and after that orthogonality the diagonal is controlled by
`Σ_{β∈E_s}|ψ_s(ξ−β)|² ≤ M²` (`mstEta_arcSum_le`, disjointness of the bump translates).

The two arithmetic/linear-algebraic ingredients are proved as separate lemmas:
* `Work.Maximal.mstOrtho.ftLp_mstModSeq` — the Fourier transform of the modulated input;
* `Work.Maximal.mstOrtho.range_fourier_sq_sum` — the character orthogonality over `ℤ/Q`.

The present file assembles them: the Plancherel identity, the a.e. peeling of the symbol, the
`u`-sum exchange, the per-`β` translation invariance of the Haar measure, and finally the
counting-measure (`lintegral`) bookkeeping.
-/

open MeasureTheory Finset
open scoped BigOperators ENNReal

namespace Work.BourgainPlan.Maximal

open Work.BourgainPlan.IonescuWainger (ftLp shiftLp shiftLp_coeFn opMul opMulLp opMul_memℓp
  ftLp_opMul norm_sq_eq_integral_l2 tsum_norm_sq_eq_norm_ftLp)

noncomputable section

local notation "haarT" => (AddCircle.haarAddCircle (T := 1))

local notation "Circ" => Work.BourgainPlan.IonescuWainger.Circle

/-- The `lintegral`, against the counting measure, of `‖h m‖ₑ ^ 2` is `ofReal` of the squared
`ℓ²`-norm of the Fourier transform of `h`. -/
lemma lintegral_count_enorm_sq (h : ℤ → ℂ) (hh : Memℓp h 2) :
    ∫⁻ m : ℤ, ‖h m‖ₑ ^ (2 : ℝ) ∂(Measure.count : Measure ℤ)
      = ENNReal.ofReal (‖ftLp h hh‖ ^ 2) := by
  rw [lintegral_count]
  have hsumm : Summable (fun m : ℤ => ‖h m‖ ^ 2) := by
    have h' : Summable (fun m : ℤ => ‖h m‖ ^ (2 : ℝ)) := by simpa [Memℓp] using hh
    exact h'.congr (fun m => Real.rpow_two (‖h m‖))
  have h1 : ∀ m : ℤ, ‖h m‖ₑ ^ (2 : ℝ) = ENNReal.ofReal (‖h m‖ ^ 2) := by
    intro m
    rw [show ‖h m‖ₑ = ENNReal.ofReal ‖h m‖ by simp [enorm_eq_nnnorm],
      ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 2),
      Real.rpow_two]
  simp only [h1]
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun m => by positivity) hsumm,
    tsum_norm_sq_eq_norm_ftLp hh]

/-- Translating an `L^∞`-class backwards by `β`: the class of `η ↦ hB (η - β)`. -/
noncomputable def shiftBackLp (β : Circ) (hB : Lp ℂ (⊤ : ℝ≥0∞) haarT) :
    Lp ℂ (⊤ : ℝ≥0∞) haarT :=
  Lp.compMeasurePreserving (fun x : Circ => x + (-β))
    (measurePreserving_add_right haarT (-β)) hB

lemma shiftBackLp_coeFn (β : Circ) (hB : Lp ℂ (⊤ : ℝ≥0∞) haarT) :
    (shiftBackLp β hB : Circ → ℂ) =ᵐ[haarT] fun η => (hB : Circ → ℂ) (η - β) := by
  have hcoe : (shiftBackLp β hB : Circ → ℂ) =ᵐ[haarT]
      fun η => (hB : Circ → ℂ) (η + (-β)) :=
    Lp.coeFn_compMeasurePreserving hB (measurePreserving_add_right haarT (-β))
  filter_upwards [hcoe] with η hη
  rw [hη]
  exact congrArg (hB : Circ → ℂ) (by rw [sub_eq_add_neg])

/-- The a.e. value of `hB • shiftLp β F` is `hB ξ · F (ξ + β)`. -/
lemma ae_eq_coeFn_lpSMul_shiftLp (hB : Lp ℂ (⊤ : ℝ≥0∞) haarT) (F : Lp ℂ 2 haarT)
    (β : Circ) :
    ((hB • shiftLp β F : Lp ℂ 2 haarT) : Circ → ℂ)
      =ᵐ[haarT] fun ξ => (hB : Circ → ℂ) ξ * (F : Circ → ℂ) (ξ + β) := by
  have h1 := Lp.coeFn_lpSMul (r := 2) hB (shiftLp β F)
  have h2 := shiftLp_coeFn β F
  filter_upwards [h1, h2] with ξ e1 e2
  simp only [e1, Pi.smul_apply, smul_eq_mul, Pi.mul_apply, e2]

/-- Integrability of `‖hB‖² · ‖F(·+β)‖²`. -/
lemma integrable_mul_shiftLp (hB : Lp ℂ (⊤ : ℝ≥0∞) haarT) (F : Lp ℂ 2 haarT) (β : Circ) :
    Integrable (fun ξ : Circ => ‖(hB : Circ → ℂ) ξ‖ ^ 2 *
      ‖(F : Circ → ℂ) (ξ + β)‖ ^ 2) haarT := by
  have h1 : Integrable
      (fun ξ : Circ => ‖((hB • shiftLp β F : Lp ℂ 2 haarT) : Circ → ℂ) ξ‖ ^ 2) haarT :=
    MemLp.integrable_norm_pow' (μ := haarT) (Lp.memLp (hB • shiftLp β F))
  refine h1.congr ?_
  filter_upwards [ae_eq_coeFn_lpSMul_shiftLp hB F β] with ξ h
  rw [h, norm_mul, mul_pow]

/-- The "peeling" identity: the a.e. value of `hB • Σ_{β∈E} c_β • shiftLp β F` is the symbol
`hB ξ` times the scalar sum `Σ_{β∈E} c_β 𝓕F (ξ+β)`. -/
lemma ae_eq_peel (hB : Lp ℂ (⊤ : ℝ≥0∞) haarT) (F : Lp ℂ 2 haarT) (E : Finset Circ)
    (G : Circ → ℂ) (u : ℤ) :
    (fun ξ : Circ => ‖((hB • (∑ β ∈ E, (G β * fourier (-u) β) • shiftLp β F) :
        Lp ℂ 2 haarT) : Circ → ℂ) ξ‖ ^ 2)
      =ᵐ[haarT] fun ξ : Circ => ‖(hB : Circ → ℂ) ξ‖ ^ 2 *
        ‖∑ β ∈ E, (G β * fourier (-u) β) * (F : Circ → ℂ) (ξ + β)‖ ^ 2 := by
  have h1 := Lp.coeFn_lpSMul (r := 2) hB (∑ β ∈ E, (G β * fourier (-u) β) • shiftLp β F)
  have hsum := Lp.coeFn_finsetSum E (fun β => (G β * fourier (-u) β) • shiftLp β F)
  have hsm : ∀ᵐ ξ ∂haarT, ∀ β : ↥E,
      (((G β.1 * fourier (-u) β.1) • shiftLp β.1 F : Lp ℂ 2 haarT) : Circ → ℂ) ξ
        = (G β.1 * fourier (-u) β.1) * (F : Circ → ℂ) (ξ + β.1) := by
    rw [Filter.eventually_all]
    intro β
    have hs := Lp.coeFn_smul (G β.1 * fourier (-u) β.1) (shiftLp β.1 F)
    have h2 := shiftLp_coeFn β.1 F
    filter_upwards [hs, h2] with ξ e1 e2
    simp only [e1, Pi.smul_apply, smul_eq_mul, Pi.mul_apply, e2]
  filter_upwards [h1, hsum, hsm] with ξ e1 e2 e3
  simp only [e1, Pi.smul_apply, smul_eq_mul, Pi.mul_apply, e2, Finset.sum_apply]
  have hcongr : (∑ β ∈ E, (((G β * fourier (-u) β) • shiftLp β F :
        Lp ℂ 2 haarT) : Circ → ℂ) ξ)
      = ∑ β ∈ E, (G β * fourier (-u) β) * (F : Circ → ℂ) (ξ + β) :=
    Finset.sum_congr rfl (fun β hβ => e3 ⟨β, hβ⟩)
  rw [hcongr, norm_mul, mul_pow]

/-- **The Plancherel value of one `u`-term**: the squared `ℓ²`-norm of the single multiplier with
symbol `hB` applied to `mstModSeq G E f u` is the circle integral of `‖hB‖²` times the square of the
scalar sum `Σ_{β∈E} G β e^{−2πiuβ} 𝓕f(ξ+β)`. -/
lemma term_eq_integral (hB : Lp ℂ (⊤ : ℝ≥0∞) haarT) (E : Finset Circ) (G : Circ → ℂ)
    (f : ℤ → ℂ) (hf : Memℓp f 2) (u : ℤ) :
    ‖ftLp (opMul hB (mstModSeq G E f u) (memℒp_mstModSeq hf u))
        (opMul_memℓp hB (mstModSeq G E f u) (memℒp_mstModSeq hf u))‖ ^ 2
      = ∫ ξ : Circ, ‖(hB : Circ → ℂ) ξ‖ ^ 2 *
          ‖∑ β ∈ E, (G β * fourier (-u) β) * (ftLp f hf : Circ → ℂ) (ξ + β)‖ ^ 2 ∂haarT := by
  have hΦ : ftLp (opMul hB (mstModSeq G E f u) (memℒp_mstModSeq hf u))
        (opMul_memℓp hB (mstModSeq G E f u) (memℒp_mstModSeq hf u))
      = hB • (∑ β ∈ E, (G β * fourier (-u) β) • shiftLp β (ftLp f hf)) := by
    rw [ftLp_opMul]
    simp only [opMulLp]
    rw [Work.Maximal.mstOrtho.ftLp_mstModSeq G E f hf u]
  rw [hΦ, norm_sq_eq_integral_l2]
  exact integral_congr_ae (μ := haarT) (ae_eq_peel hB (ftLp f hf) E G u)

/-- Translation invariance of the Haar measure in the `β`-variable of the integrand. -/
lemma integral_mul_shiftLp_translate (hB : Lp ℂ (⊤ : ℝ≥0∞) haarT) (F : Lp ℂ 2 haarT)
    (β : Circ) :
    (∫ ξ : Circ, ‖(hB : Circ → ℂ) ξ‖ ^ 2 * ‖(F : Circ → ℂ) (ξ + β)‖ ^ 2 ∂haarT)
      = ∫ η : Circ, ‖(hB : Circ → ℂ) (η - β)‖ ^ 2 * ‖(F : Circ → ℂ) η‖ ^ 2 ∂haarT := by
  have h := integral_add_right_eq_self (μ := haarT)
    (fun η : Circ => ‖(hB : Circ → ℂ) (η - β)‖ ^ 2 * ‖(F : Circ → ℂ) η‖ ^ 2) β
  rw [← h]
  refine integral_congr_ae (μ := haarT) (Filter.Eventually.of_forall (fun x => ?_))
  simp only [add_sub_cancel_right]

/-- **The translated sum bound**: if `Σ_{β∈E}‖hB(η−β)‖² ≤ M²` a.e. then the sum of the translated
integrals is bounded by `M²‖F‖²`. -/
lemma sum_integral_mul_shiftLp_le (hB : Lp ℂ (⊤ : ℝ≥0∞) haarT) (F : Lp ℂ 2 haarT)
    (E : Finset Circ) {M : ℝ} (hM0 : 0 ≤ M)
    (hBsum : ∀ᵐ η ∂haarT, ∑ β ∈ E, ‖(hB : Circ → ℂ) (η - β)‖ ^ 2 ≤ M ^ 2) :
    ∑ β ∈ E, ∫ η : Circ, ‖(hB : Circ → ℂ) (η - β)‖ ^ 2 * ‖(F : Circ → ℂ) η‖ ^ 2 ∂haarT
      ≤ M ^ 2 * ‖F‖ ^ 2 := by
  have hInt : ∀ β ∈ E, Integrable
      (fun η : Circ => ‖(hB : Circ → ℂ) (η - β)‖ ^ 2 * ‖(F : Circ → ℂ) η‖ ^ 2) haarT := by
    intro β _
    have h1 : Integrable
        (fun η : Circ => ‖((shiftBackLp β hB • F : Lp ℂ 2 haarT) : Circ → ℂ) η‖ ^ 2) haarT :=
      MemLp.integrable_norm_pow' (μ := haarT) (Lp.memLp (shiftBackLp β hB • F))
    refine h1.congr ?_
    have h2 := Lp.coeFn_lpSMul (r := 2) (shiftBackLp β hB) F
    have h3 := shiftBackLp_coeFn β hB
    filter_upwards [h2, h3] with η e1 e2
    simp only [e1, Pi.smul_apply, smul_eq_mul, Pi.mul_apply, e2, norm_mul, mul_pow]
  have hIntSum : Integrable
      (fun η : Circ => (∑ β ∈ E, ‖(hB : Circ → ℂ) (η - β)‖ ^ 2) * ‖(F : Circ → ℂ) η‖ ^ 2)
      haarT := by
    have h0 : Integrable (fun η : Circ => ∑ β ∈ E,
        ‖(hB : Circ → ℂ) (η - β)‖ ^ 2 * ‖(F : Circ → ℂ) η‖ ^ 2) haarT :=
      integrable_finsetSum E hInt
    refine h0.congr (Filter.Eventually.of_forall (fun η => ?_))
    exact (Finset.sum_mul E (fun β => ‖(hB : Circ → ℂ) (η - β)‖ ^ 2)
      (‖(F : Circ → ℂ) η‖ ^ 2)).symm
  have hM2 : Integrable (fun η : Circ => M ^ 2 * ‖(F : Circ → ℂ) η‖ ^ 2) haarT :=
    (MemLp.integrable_norm_pow' (μ := haarT) (Lp.memLp F)).const_mul (M ^ 2)
  have hle : (∫ η : Circ, (∑ β ∈ E, ‖(hB : Circ → ℂ) (η - β)‖ ^ 2) *
        ‖(F : Circ → ℂ) η‖ ^ 2 ∂haarT)
      ≤ ∫ η : Circ, M ^ 2 * ‖(F : Circ → ℂ) η‖ ^ 2 ∂haarT := by
    refine integral_mono_ae (μ := haarT) hIntSum hM2 ?_
    filter_upwards [hBsum] with η hη
    exact mul_le_mul_of_nonneg_right hη (sq_nonneg _)
  have hlast : (∫ η : Circ, M ^ 2 * ‖(F : Circ → ℂ) η‖ ^ 2 ∂haarT) = M ^ 2 * ‖F‖ ^ 2 := by
    rw [integral_const_mul (M ^ 2) (fun η : Circ => ‖(F : Circ → ℂ) η‖ ^ 2),
      ← norm_sq_eq_integral_l2]
  have hsum_eq : (∑ β ∈ E, ∫ η : Circ, ‖(hB : Circ → ℂ) (η - β)‖ ^ 2 *
        ‖(F : Circ → ℂ) η‖ ^ 2 ∂haarT)
      = ∫ η : Circ, ∑ β ∈ E,
          ‖(hB : Circ → ℂ) (η - β)‖ ^ 2 * ‖(F : Circ → ℂ) η‖ ^ 2 ∂haarT :=
    (integral_finsetSum E hInt).symm
  have hcombined : (∫ η : Circ, ∑ β ∈ E,
        ‖(hB : Circ → ℂ) (η - β)‖ ^ 2 * ‖(F : Circ → ℂ) η‖ ^ 2 ∂haarT)
      = ∫ η : Circ, (∑ β ∈ E, ‖(hB : Circ → ℂ) (η - β)‖ ^ 2) *
          ‖(F : Circ → ℂ) η‖ ^ 2 ∂haarT :=
    integral_congr_ae (μ := haarT) (Filter.Eventually.of_forall (fun η =>
      (Finset.sum_mul E (fun β => ‖(hB : Circ → ℂ) (η - β)‖ ^ 2)
        (‖(F : Circ → ℂ) η‖ ^ 2)).symm))
  calc ∑ β ∈ E, ∫ η : Circ, ‖(hB : Circ → ℂ) (η - β)‖ ^ 2 * ‖(F : Circ → ℂ) η‖ ^ 2 ∂haarT
      = ∫ η : Circ, ∑ β ∈ E,
          ‖(hB : Circ → ℂ) (η - β)‖ ^ 2 * ‖(F : Circ → ℂ) η‖ ^ 2 ∂haarT := hsum_eq
    _ = ∫ η : Circ, (∑ β ∈ E, ‖(hB : Circ → ℂ) (η - β)‖ ^ 2) *
          ‖(F : Circ → ℂ) η‖ ^ 2 ∂haarT := hcombined
    _ ≤ ∫ η : Circ, M ^ 2 * ‖(F : Circ → ℂ) η‖ ^ 2 ∂haarT := hle
    _ = M ^ 2 * ‖F‖ ^ 2 := hlast

/-- **The core Real estimate.**  For `Q`-torsion arcs `E`, weights `G` with `‖G β‖ ≤ G0·A` on `E`,
and a symbol whose translated square-sums are bounded by `M²`, the `u`-average of the frozen model
over `ℤ/Q` is bounded by `(M G0 A)² Q ‖f‖²`. -/
theorem mstOrthogonality_core {Q : ℕ} {E : Finset Circ}
    (hEtor : ∀ β ∈ E, fourier (Q : ℤ) β = 1)
    {G : Circ → ℂ} {G0 A M : ℝ} (hG0 : 0 ≤ G0) (hA0 : 0 ≤ A) (hM0 : 0 ≤ M)
    (hGdec : ∀ β ∈ E, ‖G β‖ ≤ G0 * A)
    (hB : Lp ℂ (⊤ : ℝ≥0∞) haarT)
    (hBsum : ∀ᵐ η ∂haarT, ∑ β ∈ E, ‖(hB : Circ → ℂ) (η - β)‖ ^ 2 ≤ M ^ 2)
    (f : ℤ → ℂ) (hf : Memℓp f 2) :
    ∑ u ∈ Finset.range Q,
        ‖ftLp (opMul hB (mstModSeq G E f u) (memℒp_mstModSeq hf u))
          (opMul_memℓp hB (mstModSeq G E f u) (memℒp_mstModSeq hf u))‖ ^ 2
      ≤ (M * G0 * A) ^ 2 * ((Q : ℝ) * ‖ftLp f hf‖ ^ 2) := by
  have hQ0 : (0 : ℝ) ≤ (Q : ℝ) := Nat.cast_nonneg Q
  have hIntu : ∀ u : ℕ, Integrable (fun ξ : Circ => ‖(hB : Circ → ℂ) ξ‖ ^ 2 *
      ‖∑ β ∈ E, (G β * fourier (-(u : ℤ)) β) * (ftLp f hf : Circ → ℂ) (ξ + β)‖ ^ 2) haarT := by
    intro u
    have h1 : Integrable (fun ξ : Circ =>
        ‖((hB • (∑ β ∈ E, (G β * fourier (-(u : ℤ)) β) • shiftLp β (ftLp f hf)) :
          Lp ℂ 2 haarT) : Circ → ℂ) ξ‖ ^ 2) haarT :=
      MemLp.integrable_norm_pow' (μ := haarT)
        (Lp.memLp (hB • (∑ β ∈ E, (G β * fourier (-(u : ℤ)) β) • shiftLp β (ftLp f hf))))
    exact h1.congr (ae_eq_peel hB (ftLp f hf) E G (u : ℤ))
  have hIntβ : ∀ β : Circ, Integrable (fun ξ : Circ => ‖(hB : Circ → ℂ) ξ‖ ^ 2 *
      (‖G β‖ ^ 2 * ‖(ftLp f hf : Circ → ℂ) (ξ + β)‖ ^ 2)) haarT := by
    intro β
    have h1 : Integrable (fun ξ : Circ => ‖G β‖ ^ 2 *
        (‖(hB : Circ → ℂ) ξ‖ ^ 2 * ‖(ftLp f hf : Circ → ℂ) (ξ + β)‖ ^ 2)) haarT :=
      (integrable_mul_shiftLp hB (ftLp f hf) β).const_mul (‖G β‖ ^ 2)
    exact h1.congr (Filter.Eventually.of_forall (fun ξ => by ring))
  have hE01 : ∑ u ∈ Finset.range Q,
        ‖ftLp (opMul hB (mstModSeq G E f u) (memℒp_mstModSeq hf u))
          (opMul_memℓp hB (mstModSeq G E f u) (memℒp_mstModSeq hf u))‖ ^ 2
      = ∫ ξ : Circ, ∑ u ∈ Finset.range Q, (‖(hB : Circ → ℂ) ξ‖ ^ 2 *
          ‖∑ β ∈ E, (G β * fourier (-(u : ℤ)) β) *
            (ftLp f hf : Circ → ℂ) (ξ + β)‖ ^ 2) ∂haarT := by
    have hcong : ∑ u ∈ Finset.range Q,
          ‖ftLp (opMul hB (mstModSeq G E f u) (memℒp_mstModSeq hf u))
            (opMul_memℓp hB (mstModSeq G E f u) (memℒp_mstModSeq hf u))‖ ^ 2
        = ∑ u ∈ Finset.range Q, ∫ ξ : Circ, ‖(hB : Circ → ℂ) ξ‖ ^ 2 *
            ‖∑ β ∈ E, (G β * fourier (-(u : ℤ)) β) *
              (ftLp f hf : Circ → ℂ) (ξ + β)‖ ^ 2 ∂haarT :=
      Finset.sum_congr rfl (fun u _ => term_eq_integral hB E G f hf (u : ℤ))
    rw [hcong]
    exact (integral_finsetSum (Finset.range Q) (fun u _ => hIntu u)).symm
  have hE12 : (∫ ξ : Circ, ∑ u ∈ Finset.range Q, (‖(hB : Circ → ℂ) ξ‖ ^ 2 *
        ‖∑ β ∈ E, (G β * fourier (-(u : ℤ)) β) *
          (ftLp f hf : Circ → ℂ) (ξ + β)‖ ^ 2) ∂haarT)
      = (Q : ℝ) * ∫ ξ : Circ, ∑ β ∈ E, (‖(hB : Circ → ℂ) ξ‖ ^ 2 *
          (‖G β‖ ^ 2 * ‖(ftLp f hf : Circ → ℂ) (ξ + β)‖ ^ 2)) ∂haarT := by
    have hpt : ∀ ξ : Circ, (∑ u ∈ Finset.range Q, (‖(hB : Circ → ℂ) ξ‖ ^ 2 *
          ‖∑ β ∈ E, (G β * fourier (-(u : ℤ)) β) *
            (ftLp f hf : Circ → ℂ) (ξ + β)‖ ^ 2))
        = (Q : ℝ) * ∑ β ∈ E, (‖(hB : Circ → ℂ) ξ‖ ^ 2 *
            (‖G β‖ ^ 2 * ‖(ftLp f hf : Circ → ℂ) (ξ + β)‖ ^ 2)) := by
      intro ξ
      have h2 := Work.Maximal.mstOrtho.range_fourier_sq_sum hEtor G
        (fun β => (ftLp f hf : Circ → ℂ) (ξ + β))
      calc (∑ u ∈ Finset.range Q, (‖(hB : Circ → ℂ) ξ‖ ^ 2 *
            ‖∑ β ∈ E, (G β * fourier (-(u : ℤ)) β) *
              (ftLp f hf : Circ → ℂ) (ξ + β)‖ ^ 2))
          = ‖(hB : Circ → ℂ) ξ‖ ^ 2 * (∑ u ∈ Finset.range Q,
              ‖∑ β ∈ E, (G β * fourier (-(u : ℤ)) β) *
                (ftLp f hf : Circ → ℂ) (ξ + β)‖ ^ 2) :=
            (Finset.mul_sum (Finset.range Q)
              (fun u => ‖∑ β ∈ E, (G β * fourier (-(u : ℤ)) β) *
                (ftLp f hf : Circ → ℂ) (ξ + β)‖ ^ 2) (‖(hB : Circ → ℂ) ξ‖ ^ 2)).symm
        _ = ‖(hB : Circ → ℂ) ξ‖ ^ 2 * ((Q : ℝ) * ∑ β ∈ E,
              ‖G β‖ ^ 2 * ‖(ftLp f hf : Circ → ℂ) (ξ + β)‖ ^ 2) := by rw [h2]
        _ = (Q : ℝ) * (‖(hB : Circ → ℂ) ξ‖ ^ 2 * ∑ β ∈ E,
              ‖G β‖ ^ 2 * ‖(ftLp f hf : Circ → ℂ) (ξ + β)‖ ^ 2) := by ring
        _ = (Q : ℝ) * ∑ β ∈ E, (‖(hB : Circ → ℂ) ξ‖ ^ 2 *
              (‖G β‖ ^ 2 * ‖(ftLp f hf : Circ → ℂ) (ξ + β)‖ ^ 2)) := by
            rw [Finset.mul_sum]
    rw [integral_congr_ae (μ := haarT) (Filter.Eventually.of_forall hpt), integral_const_mul]
  have hE23 : (∫ ξ : Circ, ∑ β ∈ E, (‖(hB : Circ → ℂ) ξ‖ ^ 2 *
        (‖G β‖ ^ 2 * ‖(ftLp f hf : Circ → ℂ) (ξ + β)‖ ^ 2)) ∂haarT)
      = ∑ β ∈ E, ∫ ξ : Circ, (‖(hB : Circ → ℂ) ξ‖ ^ 2 *
          (‖G β‖ ^ 2 * ‖(ftLp f hf : Circ → ℂ) (ξ + β)‖ ^ 2)) ∂haarT :=
    integral_finsetSum E (fun β _ => hIntβ β)
  have hE34 : (∑ β ∈ E, ∫ ξ : Circ, (‖(hB : Circ → ℂ) ξ‖ ^ 2 *
        (‖G β‖ ^ 2 * ‖(ftLp f hf : Circ → ℂ) (ξ + β)‖ ^ 2)) ∂haarT)
      ≤ (G0 * A) ^ 2 * ∑ β ∈ E, ∫ ξ : Circ, ‖(hB : Circ → ℂ) ξ‖ ^ 2 *
          ‖(ftLp f hf : Circ → ℂ) (ξ + β)‖ ^ 2 ∂haarT := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum (fun β hβ => ?_)
    have hb : ‖G β‖ ^ 2 ≤ (G0 * A) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (hGdec β hβ) 2
    have hI1 : Integrable (fun ξ : Circ => ‖(hB : Circ → ℂ) ξ‖ ^ 2 *
        (‖G β‖ ^ 2 * ‖(ftLp f hf : Circ → ℂ) (ξ + β)‖ ^ 2)) haarT := hIntβ β
    have hI2 : Integrable (fun ξ : Circ => (G0 * A) ^ 2 *
        (‖(hB : Circ → ℂ) ξ‖ ^ 2 * ‖(ftLp f hf : Circ → ℂ) (ξ + β)‖ ^ 2)) haarT :=
      (integrable_mul_shiftLp hB (ftLp f hf) β).const_mul ((G0 * A) ^ 2)
    have hI0 : Integrable (fun ξ : Circ => ‖G β‖ ^ 2 *
        (‖(hB : Circ → ℂ) ξ‖ ^ 2 * ‖(ftLp f hf : Circ → ℂ) (ξ + β)‖ ^ 2)) haarT :=
      (integrable_mul_shiftLp hB (ftLp f hf) β).const_mul (‖G β‖ ^ 2)
    calc (∫ ξ : Circ, (‖(hB : Circ → ℂ) ξ‖ ^ 2 *
          (‖G β‖ ^ 2 * ‖(ftLp f hf : Circ → ℂ) (ξ + β)‖ ^ 2)) ∂haarT)
        = ∫ ξ : Circ, (‖G β‖ ^ 2 * (‖(hB : Circ → ℂ) ξ‖ ^ 2 *
            ‖(ftLp f hf : Circ → ℂ) (ξ + β)‖ ^ 2)) ∂haarT :=
          integral_congr_ae (μ := haarT) (Filter.Eventually.of_forall (fun ξ => by ring))
      _ ≤ ∫ ξ : Circ, ((G0 * A) ^ 2 * (‖(hB : Circ → ℂ) ξ‖ ^ 2 *
            ‖(ftLp f hf : Circ → ℂ) (ξ + β)‖ ^ 2)) ∂haarT := by
          refine integral_mono_ae (μ := haarT) hI0 hI2 ?_
          filter_upwards with ξ
          exact mul_le_mul_of_nonneg_right hb (by positivity)
      _ = (G0 * A) ^ 2 * ∫ ξ : Circ, ‖(hB : Circ → ℂ) ξ‖ ^ 2 *
            ‖(ftLp f hf : Circ → ℂ) (ξ + β)‖ ^ 2 ∂haarT := integral_const_mul _ _
  calc (∑ u ∈ Finset.range Q,
        ‖ftLp (opMul hB (mstModSeq G E f u) (memℒp_mstModSeq hf u))
          (opMul_memℓp hB (mstModSeq G E f u) (memℒp_mstModSeq hf u))‖ ^ 2)
      = ∫ ξ : Circ, ∑ u ∈ Finset.range Q, (‖(hB : Circ → ℂ) ξ‖ ^ 2 *
          ‖∑ β ∈ E, (G β * fourier (-(u : ℤ)) β) *
            (ftLp f hf : Circ → ℂ) (ξ + β)‖ ^ 2) ∂haarT := hE01
    _ = (Q : ℝ) * ∫ ξ : Circ, ∑ β ∈ E, (‖(hB : Circ → ℂ) ξ‖ ^ 2 *
          (‖G β‖ ^ 2 * ‖(ftLp f hf : Circ → ℂ) (ξ + β)‖ ^ 2)) ∂haarT := hE12
    _ = (Q : ℝ) * ∑ β ∈ E, ∫ ξ : Circ, (‖(hB : Circ → ℂ) ξ‖ ^ 2 *
          (‖G β‖ ^ 2 * ‖(ftLp f hf : Circ → ℂ) (ξ + β)‖ ^ 2)) ∂haarT := by rw [hE23]
    _ ≤ (Q : ℝ) * ((G0 * A) ^ 2 * ∑ β ∈ E, ∫ ξ : Circ, ‖(hB : Circ → ℂ) ξ‖ ^ 2 *
          ‖(ftLp f hf : Circ → ℂ) (ξ + β)‖ ^ 2 ∂haarT) :=
        mul_le_mul_of_nonneg_left hE34 hQ0
    _ ≤ (Q : ℝ) * ((G0 * A) ^ 2 * (M ^ 2 * ‖ftLp f hf‖ ^ 2)) := by
        refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)) hQ0
        calc (∑ β ∈ E, ∫ ξ : Circ, ‖(hB : Circ → ℂ) ξ‖ ^ 2 *
              ‖(ftLp f hf : Circ → ℂ) (ξ + β)‖ ^ 2 ∂haarT)
            = ∑ β ∈ E, ∫ η : Circ, ‖(hB : Circ → ℂ) (η - β)‖ ^ 2 *
                ‖(ftLp f hf : Circ → ℂ) η‖ ^ 2 ∂haarT :=
              Finset.sum_congr rfl (fun β _ => integral_mul_shiftLp_translate hB (ftLp f hf) β)
          _ ≤ M ^ 2 * ‖ftLp f hf‖ ^ 2 := sum_integral_mul_shiftLp_le hB (ftLp f hf) E hM0 hBsum
    _ = (M * G0 * A) ^ 2 * ((Q : ℝ) * ‖ftLp f hf‖ ^ 2) := by ring

/-- **The diagonalisation of the arc sum by the `u`-average.**  Averaging the `Φ`-free model over
the shifts `u ∈ ℕ_{Q_s}` — i.e. the single multipliers with symbol `ψ_s` applied to the modulated
inputs `mstModSeq G E f u` — carries the Gauss decay `(s+1)^{−δl}G0` exactly *once* (not `#𝒰`
times): the characters `u ↦ e^{2πi u β}`, `β ∈ E_s`, are orthogonal on `ℤ/Q_s` (each arc is a
`Q_s`-torsion point), and after that orthogonality the diagonal is controlled by
`Σ_{β∈E_s}|ψ_s(ξ−β)|² ≤ M²` (`mstEta_arcSum_le`, i.e. the disjointness of the bump translates),
which supplies `Σ_β|G β|²·|ψ_s(ξ−β)|² ≤ (G0(s+1)^{−δl})²M²`. -/
theorem mstOrthogonality (P : Polynomial ℤ) (hd : 2 ≤ P.natDegree) (l : ℕ) (hl : 1 ≤ l) (χ : ℝ)
    (hχ : 0 < χ) (hχ1 : χ < 1 / 10) (η : ℝ → ℂ) (hηc : ContDiff ℝ 2 η) (hη1 : η 0 = 1)
    (hηsup : ∀ x : ℝ, 1 / 2 ≤ |x| → η x = 0) (δ : ℝ) (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∃ s₀ : ℕ, ∀ s : ℕ, s₀ ≤ s →
      ∀ (G : Work.BourgainPlan.IonescuWainger.Circle → ℂ) (G0 : ℝ), 0 ≤ G0 →
      Work.BourgainPlan.Maximal.HasDecay G G0 l s δ →
      ∀ (hB : Lp ℂ ⊤ Work.BourgainPlan.Maximal.mstHaar),
      Work.BourgainPlan.Maximal.HasBump P.natDegree χ η s hB →
      ∀ (f : ℤ → ℂ) (hf : Memℓp f 2),
        ∑ u ∈ Finset.range (Work.BourgainPlan.Maximal.mstQ' s),
            (∫⁻ m : ℤ, ‖Work.BourgainPlan.IonescuWainger.opMul hB (Work.BourgainPlan.Maximal.mstModSeq G (Work.BourgainPlan.Maximal.mstLvl l s) f u) (Work.BourgainPlan.Maximal.memℒp_mstModSeq hf u) m‖ₑ ^ (2 : ℝ)
              ∂MeasureTheory.Measure.count)
          ≤ ENNReal.ofReal ((C * G0 * ((s : ℝ) + 1) ^ (-(δ * l))) ^ 2)
              * ((Work.BourgainPlan.Maximal.mstQ' s : ℝ≥0∞)
                * (∫⁻ m : ℤ, ‖f m‖ₑ ^ (2 : ℝ) ∂MeasureTheory.Measure.count)) := by
  classical
  obtain ⟨M, hM0, hM⟩ :=
    mstEta_arcSum_le l hl P.natDegree (by omega) χ hχ
    (by
      have h2 : (2 : ℝ) ≤ (P.natDegree : ℝ) := by exact_mod_cast hd
      linarith)
    η hηc.continuous hηsup
  obtain ⟨s₀, hs₀⟩ := mstTorsion l hl
  refine ⟨M, hM0, s₀, fun s hs G G0 hG0 hdec hB hBump f hf => ?_⟩
  have hA0 : (0 : ℝ) ≤ ((s : ℝ) + 1) ^ (-(δ * l)) := Real.rpow_nonneg (by positivity) _
  have hEtor : ∀ β ∈ mstLvl l s, fourier (mstQ' s : ℤ) β = 1 :=
    fun β hβ => hs₀ s hs β (Finset.mem_sdiff.mp hβ).1
  have hBsum : ∀ᵐ η' ∂haarT, ∑ β ∈ mstLvl l s, ‖(hB : Circ → ℂ) (η' - β)‖ ^ 2 ≤ M ^ 2 := by
    have hpt : ∀ᵐ η' ∂haarT, ∀ β : ↥(mstLvl l s),
        (hB : Circ → ℂ) (η' - β) = mstEta P.natDegree χ η s (η' - β) := by
      rw [Filter.eventually_all]
      intro β
      have h := (measurePreserving_add_right haarT (-β.1)).quasiMeasurePreserving.ae hBump
      filter_upwards [h] with x hx
      simpa [sub_eq_add_neg] using hx
    filter_upwards [hpt] with η' hη'
    have hsum : ∑ β ∈ mstLvl l s, ‖mstEta P.natDegree χ η s (η' - β)‖ ≤ M := by
      simpa only [mstLvl] using hM s η'
    calc ∑ β ∈ mstLvl l s, ‖(hB : Circ → ℂ) (η' - β)‖ ^ 2
        = ∑ β ∈ mstLvl l s, ‖mstEta P.natDegree χ η s (η' - β)‖ ^ 2 :=
          Finset.sum_congr rfl (fun β hβ => by rw [hη' ⟨β, hβ⟩])
      _ ≤ (∑ β ∈ mstLvl l s, ‖mstEta P.natDegree χ η s (η' - β)‖) ^ 2 :=
          Finset.sum_sq_le_sq_sum_of_nonneg (fun β _ => norm_nonneg _)
      _ ≤ M ^ 2 := pow_le_pow_left₀ (Finset.sum_nonneg (fun β _ => norm_nonneg _)) hsum 2
  have key : (∑ u ∈ Finset.range (mstQ' s),
        ‖ftLp (opMul hB (mstModSeq G (mstLvl l s) f u) (memℒp_mstModSeq hf u))
          (opMul_memℓp hB (mstModSeq G (mstLvl l s) f u) (memℒp_mstModSeq hf u))‖ ^ 2)
      ≤ (M * G0 * ((s : ℝ) + 1) ^ (-(δ * l))) ^ 2 * ((mstQ' s : ℝ) * ‖ftLp f hf‖ ^ 2) :=
    mstOrthogonality_core hEtor hG0 hA0 (le_of_lt hM0) (fun β hβ => hdec β hβ) hB hBsum f hf
  have hkey : (∑ u ∈ Finset.range (mstQ' s),
        (∫⁻ m : ℤ, ‖opMul hB (mstModSeq G (mstLvl l s) f u) (memℒp_mstModSeq hf u) m‖ₑ ^ (2 : ℝ)
          ∂MeasureTheory.Measure.count))
      = ENNReal.ofReal (∑ u ∈ Finset.range (mstQ' s),
          ‖ftLp (opMul hB (mstModSeq G (mstLvl l s) f u) (memℒp_mstModSeq hf u))
            (opMul_memℓp hB (mstModSeq G (mstLvl l s) f u) (memℒp_mstModSeq hf u))‖ ^ 2) := by
    rw [ENNReal.ofReal_sum_of_nonneg (fun u _ => by positivity)]
    refine Finset.sum_congr rfl (fun u _ => ?_)
    exact lintegral_count_enorm_sq _
      (opMul_memℓp hB (mstModSeq G (mstLvl l s) f u) (memℒp_mstModSeq hf u))
  rw [hkey]
  refine le_trans (ENNReal.ofReal_le_ofReal key) (le_of_eq ?_)
  rw [lintegral_count_enorm_sq f hf, ← ENNReal.ofReal_natCast (mstQ' s),
    ← ENNReal.ofReal_mul (show (0 : ℝ) ≤ (mstQ' s : ℝ) by positivity),
    ← ENNReal.ofReal_mul
      (show (0 : ℝ) ≤ (M * G0 * ((s : ℝ) + 1) ^ (-(δ * l))) ^ 2 by positivity)]

end

end Work.BourgainPlan.Maximal
