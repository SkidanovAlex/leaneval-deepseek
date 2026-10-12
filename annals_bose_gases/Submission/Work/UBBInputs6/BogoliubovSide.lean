import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.UBBInputs6.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.UBBInputs6.BogoliubovSide` — FS §9–11 at the window: the error slack

This file carries the **second input** of the round-6 pair, `BogoliubovWindowedCov`
(FS §9–11 under the window only, at the corpus carrier), and the round-6 *decomposition* of it
into

    (L1)  the intermediate two-term Bogoliubov bound at a coefficient `c₁` with a *relative
          error* `E N L` (FS's `eq:ToProve` shape after `thm:BogHamDiag` + `lem:BogIntegral`,
          with the errors of the Bogoliubov analysis still present), and
    (L2)  the *arithmetic* absorption `E N L ≤ c₁ − lhyC` (the slack in the LHY constant, the
          place where the free parameter `K_ℓ` of the window is consumed),

proved to imply `BogoliubovWindowedCov`.  Why this is the exact place where the *window* and the
*Bogoliubov bound* interact: `BogoliubovWindowedCov` is **contravariant** in the window (a
larger window is a weaker hypothesis, hence a stronger statement), while `AprioriNPlusCov` is
**covariant** in it, and FS's `K_ℓ` both shifts the window
(`fsWindowC_eq_shape`: `W = K_B³K_ℓ²ρL³√(ρa³)`) and shrinks the Bogoliubov error coefficient
(`E ≈ K_ℓ⁻¹`) — the two conditions on the single free parameter are the *window
reconciliation*.

The three delivered corpus layers that supply (L1) at the box are named in
`SharpTwoTermCov`'s documentation (`Work.BlockBound4.diagW_lm_appbogolubov_explicitC` for the
`D1` diagonal component, `Work.FSKernelCompare.w2c_acube_integral_ge_w1c` +
`Work.SmallBoxKernelMass` for the `w₂`-mass, `Submission.LhyIntegral` for the sharp constant);
the passage from the per-small-box layers to the box-level statement (L1) is the one layer
`Submission/Work/UBBInputs2/README.md` §5 records as absent from the corpus.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators ENNReal

namespace Work.UBBInputs6

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

open _root_.BoseGases
open Submission.BoseGases
open Work.UBB
open Work.UBBInputs
open Work.UBBInputs4
open Work.UBBInputs5

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

/-! ## 1. The intermediate form: the two-term bound with a relative error -/

/-- **FS's intermediate §9–11 form at the window** (the round-6 layer (L1)): the sharp two-term
Bogoliubov bound at a coefficient `c₁`, with the errors of the Bogoliubov analysis still
present as a *relative* error `E N L` on the LHY gain:

    −4πρ²(a v)L³ + 4πρ²(a v)L³·c₁·√(ρ(a v)³)·(1 − E N L) ≤ WordDens N L ρ v h Φ · L³ .

The coefficient `E` is a function of the *box data* `(N,L)` (FS's `K_ℓ⁻¹`: their intermediate
errors carry a factor `K_ℓ^{-1}`, and `K_ℓ` is a function of the box data — `fsWindowC_eq_shape`
records that the a-priori window is exactly `K_B³K_ℓ²ρL³√(ρa³)`).  This is the form in which
the delivered per-small-box layers (`D1`, `w₂`-mass, `LhyIntegral`) are expected to arrive. -/
def TwoTermErrorCov (v : ℝ³ → ℝ) (h : ScatSol v) (J : ℝ) (W : ℕ → ℝ → ℝ)
    (ε₀ c₁ : ℝ) (E : ℕ → ℝ → ℝ) : Prop :=
  ∀ (L : ℝ), 1 ≤ L → ∀ N : ℕ, dens N L * (a v) ^ 3 ≤ ε₀ →
    ∀ Φ : CSBox N L,
      cnPlus L (Φ : X N → ℝ) ≤ W N L * sqNormN N L (Φ : X N → ℝ) →
      - (4 * π * (dens N L) ^ 2 * (a v) * L ^ 3)
          + 4 * π * (dens N L) ^ 2 * (a v) * L ^ 3 * c₁
              * Real.sqrt (dens N L * (a v) ^ 3)
          - E N L * (4 * π * (dens N L) ^ 2 * (a v) * L ^ 3
              * Real.sqrt (dens N L * (a v) ^ 3))
        ≤ WordDens N L (dens N L) v h (Φ : X N → ℝ) * L ^ 3

/-- The layer (L1) with zero error coefficient **is** the sharp two-term bound
`SharpTwoTermCov` — so the two statements cohere, and the whole content of the
`TwoTermErrorCov` layer is the *sharp* LHY gain plus the error bookkeeping. -/
theorem sharpTwoTermCov_iff_twoTermError_zero {v : ℝ³ → ℝ} {h : ScatSol v} {J : ℝ}
    {W : ℕ → ℝ → ℝ} {ε₀ c₁ : ℝ} :
    SharpTwoTermCov v h J W ε₀ c₁ ↔ TwoTermErrorCov v h J W ε₀ c₁ (fun _ _ => 0) := by
  constructor <;> intro hS <;> intro L hL N hN Φ hwin <;> have := hS L hL N hN Φ hwin <;>
    simpa using this

/-! ## 2. The absorption: the intermediate form implies the §9–11 input -/

/-- `Λ·L³` expanded in the paper's three terms (the round-5 identity
`Work.UBBInputs5.Bogoliubov.Lambda_mul_eq_bog`, re-proved here to keep this file's import
closure light). -/
theorem Lambda_mul_eq_bogC (A C η₀ ρ L : ℝ) :
    Lambda A C η₀ ρ * L ^ 3
      = - bogQuad A ρ L + bogLhy A ρ L - bogErr A C η₀ ρ L := by
  unfold Lambda bogQuad bogLhy bogErr
  ring

/-- The mean-field size `4πρ²(a v)L³` is nonnegative in the box regime (`L ≥ 1`, `a v ≥ 0`). -/
theorem four_pi_nonneg {v : ℝ³ → ℝ} (ha : 0 ≤ a v) {N : ℕ} {L : ℝ} (hL : 1 ≤ L) :
    0 ≤ 4 * π * (dens N L) ^ 2 * (a v) * L ^ 3 := by
  have hL0 : (0 : ℝ) ≤ L := le_trans zero_le_one hL
  have hρ : 0 ≤ dens N L := by
    unfold dens
    exact div_nonneg (Nat.cast_nonneg N) (pow_nonneg hL0 3)
  exact mul_nonneg (mul_nonneg (mul_nonneg (by positivity) (sq_nonneg _)) ha)
    (pow_nonneg hL0 3)

/-- The LHY gain size `4πρ²(a v)L³·√(ρ(a v)³)` is nonnegative. -/
theorem four_pi_sqrt_nonneg {v : ℝ³ → ℝ} (ha : 0 ≤ a v) {N : ℕ} {L : ℝ} (hL : 1 ≤ L) :
    0 ≤ 4 * π * (dens N L) ^ 2 * (a v) * L ^ 3 * Real.sqrt (dens N L * (a v) ^ 3) :=
  mul_nonneg (four_pi_nonneg ha hL) (Real.sqrt_nonneg _)

/-- The pure-real identity behind the absorption: `x^{1/2+η} = x^η·x^{1/2}` for `x ≥ 0`. -/
theorem rpow_half_add {x η : ℝ} (hx : 0 ≤ x) (hη : 0 ≤ η) :
    x ^ (1 / 2 + η) = x ^ η * x ^ (1 / 2 : ℝ) := by
  rcases lt_or_eq_of_le hx with hxpos | rfl
  · rw [Real.rpow_add hxpos]
    ring_nf
  · rcases lt_or_eq_of_le hη with hηpos | rfl
    · rw [Real.zero_rpow (by positivity : (1 / 2 : ℝ) + η ≠ 0),
        Real.zero_rpow (ne_of_gt hηpos), zero_mul]
    · norm_num

/-- **The round-6 decomposition of the §9–11 input.**  The intermediate two-term bound with
coefficient `c₁` and relative error `E` gives `BogoliubovWindowedCov` **provided the relative
error is dominated by the slack in the LHY constant**:

    E N L ≤ c₁ − lhyC      for every admissible box.

This is FS's absorption step (`c₁` is their effective intermediate coefficient, larger than the
sharp `lhyC` by the amount needed to carry both their own errors and the target's error term):
the conclusion is taken at the coefficient `C = 0`, which is enough because `Λ` is *decreasing*
in its error coefficient — the target's error term is paid for by the slack. -/
theorem bogoliubovWindowedCov_of_twoTermError {v : ℝ³ → ℝ} {h : ScatSol v} {J : ℝ}
    {W : ℕ → ℝ → ℝ} {ε₀ η₀ c₁ : ℝ} {E : ℕ → ℝ → ℝ}
    (ha : 0 ≤ a v) (hc₁ : lhyC ≤ c₁)
    (hE : ∀ (L : ℝ), 1 ≤ L → ∀ N : ℕ, dens N L * (a v) ^ 3 ≤ ε₀ → E N L ≤ c₁ - lhyC)
    (hS : TwoTermErrorCov v h J W ε₀ c₁ E) :
    BogoliubovWindowedCov v h J W ε₀ η₀ := by
  refine ⟨0, le_rfl, fun L hL N hN Φ hwin => ?_⟩
  have hlayer := hS L hL N hN Φ hwin
  have hE' := hE L hL N hN
  have hQv := four_pi_sqrt_nonneg (v := v) ha (N := N) (L := L) hL
  have hkey : E N L * (4 * π * (dens N L) ^ 2 * (a v) * L ^ 3
        * Real.sqrt (dens N L * (a v) ^ 3))
      ≤ (c₁ - lhyC) * (4 * π * (dens N L) ^ 2 * (a v) * L ^ 3
        * Real.sqrt (dens N L * (a v) ^ 3)) :=
    mul_le_mul_of_nonneg_right hE' hQv
  have hL3 : 0 < L ^ 3 := by positivity
  have hgoal : Lambda (a v) 0 η₀ (dens N L) * L ^ 3
      ≤ WordDens N L (dens N L) v h (Φ : X N → ℝ) * L ^ 3 := by
    rw [Lambda_mul_eq_bogC]
    simp only [bogQuad, bogLhy, bogErr, mul_zero]
    nlinarith [hlayer, hkey]
  exact le_of_mul_le_mul_right hgoal hL3

/-- **The same absorption with the target's error coefficient available** (the general form of
`bogoliubovWindowedCov_of_twoTermError`): if the relative error of the intermediate layer is
dominated by `C·(ρ(a v)³)^{η₀} + (c₁ − lhyC)`, then `BogoliubovWindowedCov` holds with that
same coefficient `C`.  The identity `rpow_half_add` is what turns the target's error exponent
`1/2 + η₀` into the box-data coefficient `(ρ(a v)³)^{η₀}`, i.e. it is exactly the bookkeeping
that makes the error absorbable *uniformly* in the density. -/
theorem bogoliubovWindowedCov_of_twoTermError_withCoeff {v : ℝ³ → ℝ} {h : ScatSol v} {J : ℝ}
    {W : ℕ → ℝ → ℝ} {ε₀ η₀ c₁ C : ℝ} {E : ℕ → ℝ → ℝ}
    (ha : 0 ≤ a v) (hC : 0 ≤ C) (hc₁ : lhyC ≤ c₁) (hη₀ : 0 ≤ η₀)
    (hE : ∀ (L : ℝ), 1 ≤ L → ∀ N : ℕ, dens N L * (a v) ^ 3 ≤ ε₀ →
      E N L ≤ C * (dens N L * (a v) ^ 3) ^ η₀ + (c₁ - lhyC))
    (hS : TwoTermErrorCov v h J W ε₀ c₁ E) :
    BogoliubovWindowedCov v h J W ε₀ η₀ := by
  refine ⟨C, hC, fun L hL N hN Φ hwin => ?_⟩
  have hlayer := hS L hL N hN Φ hwin
  have hE' := hE L hL N hN
  have hL0 : (0 : ℝ) ≤ L := le_trans zero_le_one hL
  have hx : 0 ≤ dens N L * (a v) ^ 3 := by
    have hρ : 0 ≤ dens N L := by
      unfold dens
      exact div_nonneg (Nat.cast_nonneg N) (pow_nonneg hL0 3)
    exact mul_nonneg hρ (by positivity)
  have hQv := four_pi_sqrt_nonneg (v := v) ha (N := N) (L := L) hL
  have hpow : (dens N L * (a v) ^ 3) ^ (1 / 2 + η₀)
      = (dens N L * (a v) ^ 3) ^ η₀ * (dens N L * (a v) ^ 3) ^ (1 / 2 : ℝ) :=
    rpow_half_add hx hη₀
  have hsq := Real.sqrt_eq_rpow (dens N L * (a v) ^ 3)
  have hkey : E N L * (4 * π * (dens N L) ^ 2 * (a v) * L ^ 3
        * Real.sqrt (dens N L * (a v) ^ 3))
      ≤ C * (4 * π * (dens N L) ^ 2 * (a v) * L ^ 3
            * (dens N L * (a v) ^ 3) ^ (1 / 2 + η₀))
          + (c₁ - lhyC) * (4 * π * (dens N L) ^ 2 * (a v) * L ^ 3
            * Real.sqrt (dens N L * (a v) ^ 3)) := by
    have h1 : E N L * (4 * π * (dens N L) ^ 2 * (a v) * L ^ 3
          * Real.sqrt (dens N L * (a v) ^ 3))
        ≤ (C * (dens N L * (a v) ^ 3) ^ η₀ + (c₁ - lhyC))
          * (4 * π * (dens N L) ^ 2 * (a v) * L ^ 3
            * Real.sqrt (dens N L * (a v) ^ 3)) :=
      mul_le_mul_of_nonneg_right hE' hQv
    have h2 : C * (dens N L * (a v) ^ 3) ^ η₀
          * (4 * π * (dens N L) ^ 2 * (a v) * L ^ 3
            * Real.sqrt (dens N L * (a v) ^ 3))
        = C * (4 * π * (dens N L) ^ 2 * (a v) * L ^ 3
            * (dens N L * (a v) ^ 3) ^ (1 / 2 + η₀)) := by
      rw [hpow, hsq]
      ring
    rw [add_mul] at h1
    linarith [h1, h2.le]
  have hL3 : 0 < L ^ 3 := by positivity
  have hgoal : Lambda (a v) C η₀ (dens N L) * L ^ 3
      ≤ WordDens N L (dens N L) v h (Φ : X N → ℝ) * L ^ 3 := by
    rw [Lambda_mul_eq_bogC]
    simp only [bogQuad, bogLhy, bogErr]
    have hQ0 : 0 ≤ 4 * π * (dens N L) ^ 2 * (a v) * L ^ 3 :=
      four_pi_nonneg (v := v) ha (N := N) (L := L) hL
    nlinarith [hlayer, hkey, hQ0, hQv, hC, hx]
  exact le_of_mul_le_mul_right hgoal hL3

/-! ## 2bis. The `K_ℓ`-sandwich: the arithmetic of the window reconciliation -/

/-- **The window reconciliation, in arithmetic form.**  FS's §9–11 is applied at a window
`W = K_B³K_ℓ²ρL³√(ρa³)` (`fsWindowC_eq_shape`), and its intermediate error carries the *same*
free parameter as `K_ℓ⁻¹` (the relative error `E N L` of `TwoTermErrorCov`).  Hence `K_ℓ` must
satisfy two inequalities at once:

* `1/K_ℓ ≤ c₁ − lhyC` (the error is absorbed into the LHY slack, `bogoliubovWindowedCov_of_twoTermError`);
* `K_B³K_ℓ²ρL³√(ρa³) ≤ Wmax`, where `Wmax` is the validity bound of the Bogoliubov analysis
  (FS's `(con:KBellKM)`; not formalised here — it is the hypothesis of this lemma).

The two requirements are simultaneously satisfiable **iff the minimal admissible window
`K_B³ρL³√(ρa³)/(c₁ − lhyC)²` is below `Wmax`** — which is exactly the dilute-regime condition
FS arrange by choosing the localisation length.  The witness is `K_ℓ = 1/(c₁ − lhyC)`. -/
theorem window_eligible {c₁ K_B ρ A L Wmax : ℝ} (hδ : 0 < c₁ - lhyC)
    (hreg : K_B ^ 3 * ρ * L ^ 3 * (ρ * A ^ 3) ^ (1 / 2 : ℝ)
      ≤ Wmax * (c₁ - lhyC) ^ 2) :
    ∃ Kℓ : ℝ, 0 < Kℓ ∧ 1 / Kℓ ≤ c₁ - lhyC ∧
      K_B ^ 3 * Kℓ ^ 2 * ρ * L ^ 3 * (ρ * A ^ 3) ^ (1 / 2 : ℝ) ≤ Wmax := by
  refine ⟨1 / (c₁ - lhyC), by positivity, ?_, ?_⟩
  · rw [one_div_one_div]
  · have hδ2 : (0 : ℝ) < (c₁ - lhyC) ^ 2 := pow_pos hδ 2
    have h1 : K_B ^ 3 * ρ * L ^ 3 * (ρ * A ^ 3) ^ (1 / 2 : ℝ) / (c₁ - lhyC) ^ 2 ≤ Wmax := by
      have h := div_le_div_of_nonneg_right hreg hδ2.le
      rwa [mul_div_cancel_right₀ _ (ne_of_gt hδ2)] at h
    calc K_B ^ 3 * (1 / (c₁ - lhyC)) ^ 2 * ρ * L ^ 3 * (ρ * A ^ 3) ^ (1 / 2 : ℝ)
        = K_B ^ 3 * ρ * L ^ 3 * (ρ * A ^ 3) ^ (1 / 2 : ℝ) / (c₁ - lhyC) ^ 2 := by
          field_simp
      _ ≤ Wmax := h1

/-! ## 3. The window API (the reconciliation of the two windows) -/

/-- `BogoliubovWindowedCov` is **contravariant** in the window: a larger window is a weaker
hypothesis, hence a stronger statement, so the input at a larger window gives the input at a
smaller one.  (Compare `Work.UBBInputs4.bogoliubovWindowedNeu_mono_window`.) -/
theorem bogoliubovWindowedCov_mono_window {v : ℝ³ → ℝ} {h : ScatSol v} {J ε₀ η₀ : ℝ}
    {W W' : ℕ → ℝ → ℝ} (hWW' : ∀ N L, W' N L ≤ W N L)
    (hB : BogoliubovWindowedCov v h J W ε₀ η₀) :
    BogoliubovWindowedCov v h J W' ε₀ η₀ := by
  rcases hB with ⟨C, hC, hB⟩
  refine ⟨C, hC, fun L hL N hN Φ hwin => ?_⟩
  refine hB L hL N hN Φ (le_trans hwin ?_)
  exact mul_le_mul_of_nonneg_right (hWW' N L) (le_of_lt Φ.sq_pos)

/-- `AprioriNPlusCov` is **covariant** in the window: a larger window is a weaker claim. -/
theorem aprioriNPlusCov_mono_window {v : ℝ³ → ℝ} {h : ScatSol v} {J ε₀ : ℝ}
    {W W' : ℕ → ℝ → ℝ} (hWW' : ∀ N L, W N L ≤ W' N L)
    (hA : AprioriNPlusCov v h J W ε₀) : AprioriNPlusCov v h J W' ε₀ :=
  fun L hL N hN Φ hΦ => le_trans (hA L hL N hN Φ hΦ)
    (mul_le_mul_of_nonneg_right (hWW' N L) (le_of_lt Φ.sq_pos))

/-- **The two inputs can be consumed at *different* comparable windows**: the a-priori input at
the smaller window and the Bogoliubov input at the larger one suffice for the spectral input
(FS consume the localisation's `n₊`-window and the a-priori window in exactly this way). -/
theorem spectralInput_of_windows {v : ℝ³ → ℝ} {h : ScatSol v} {J ε₀ η₀ : ℝ}
    {W W' : ℕ → ℝ → ℝ} (hWW' : ∀ N L, W N L ≤ W' N L)
    (hA : AprioriNPlusCov v h J W ε₀) (hB : BogoliubovWindowedCov v h J W' ε₀ η₀) :
    SpectralInput v h J ε₀ η₀ :=
  spectralInput_of_cov (aprioriNPlusCov_mono_window hWW' hA)
    (bogoliubovLowCov_of_windowedCov hB)

end Work.UBBInputs6
