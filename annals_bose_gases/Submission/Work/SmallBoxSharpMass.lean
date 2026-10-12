import ChallengeDeps
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.SmallBoxBogMainTerm
import Submission.Work.SmallBoxSlice
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Session-269 — the D1 SHARP-MASS step: the symbol resolution, the continuum
architecture, and the proven reduction

STATUS: this module is **sorry-free** and rc=0; it contains the Session-269
architectural findings plus the measure-theoretic loops that reduce the
sharp-mass step to ONE kernel estimate.  It is the design document for the D1
body (`lm_appbogolubov_refined_target`).

## 1. THE SYMBOL RESOLUTION (decisive, by homogeneity)

FS's `eq:appTB` writes the small-box kinetic as

    `T_B = ½ε_T(1+π⁻²)⁻¹(dℓ)⁻²Q_B + Q_Bχ_B[√−Δ−(dsℓ)⁻¹]_+⁻²χ_BQ_B`

and their Bogoliubov display in the proof of `lm:appbogolubov` is

    `h(p) = ( (|B|/(n+1))[|p|−(dsℓ)⁻¹]_+² + 2K_s a )(b_p†b_p + b_{−p}†b_{−p})
            + ŴS_1(p)(b_p†b_p† + b_{−p}b_p)`.

The first factor of `h(p)` and the second term of `T_B` are the SAME
coefficient.  In the paper's units (`ħ²/2m = 1`, so `[energy] = L⁻²`,
`[x] = L`, `[p] = L⁻¹`), `(2π)⁻³∫h(p)dp` is an energy, so
`[h(p)] = energy·L³ = L`; with `[b_p†] = L^{−3/2}` (`b_p† = |B|^{−1/2}a†(…)a_0`)
this gives `[coefficient] = L·L³ = L⁴`.  And the coefficient is
`(|B|/(n+1))[|p|−c]_+^{σ} + 2K_s a` with `[|B|] = L³` and
`[2K_s a] = L` (scattering length), so `L³·L^{−σ'dim} = L`, forcing the
positive-part factor to carry dimension `L^{−2}`, i.e. `σ` is the **SQUARE**
(not the inverse square): `[|p|−c]_+² = L^{−2}`.  Equivalently `[2K_sa] = L`
matches `(|B|/(n+1))[|p|−c]_+² = L³·L^{−2} = L`.  **Hence the superscript in
`[√−Δ−(dsℓ)⁻¹]_+⁻²` denotes the square** (FS condense
`([√−Δ−c]_+)²` into that script), and the D1 kinetic word's box-mode
transcription must use the SQUARE symbol
`fsKinCoeff c (π‖k‖/s) = [π‖k‖/s−c]_+²`, not the inverse-square
`boxModeCoeff`/`tBword` weight.

Both weights do occur in the D1 layer, in DIFFERENT roles:

  * the SQUARE weight `fsKinCoeff c (π‖k‖/s)` — the diagonal Bogoliubov
    coefficient `𝒜_k = d·[r_k−c]_+² + 2K_s a`, `d = s³/(N̂+1)`;
  * the INVERSE-square weight `boxModeCoeff s c k = fsKinCoeff c r_k⁻¹` —
    the SHARP-MASS/error weight `ℬ²/𝒜 ≤ (1/d)(K_s a)²·[r_k−c]_+⁻²`
    (`mode_error_weight_le`), whose mode sum is `tBword`
    (`SmallBoxBogolubovD1.tBword_error_budget`).

They are RECIPROCAL above threshold (`boxModeCoeff_mul_fsKinCoeff` below),
which is exactly why the Session-267 audit found the old `tBword_diag_target`
(`bModeDiag ≤ tBword`: square weight dominated by inverse-square weight)
FALSE.

## 2. THE SHARP MASS IS INTRINSICALLY CONTINUUM

FS's sharp-mass display is

    `(1/4)(2π)⁻³∫_{ℝ³} ŴS_1(p)²/p² dp = (1/4)∬ WS_1(x)WS_1(y)/(4π|x−y|) dx dy`

where `ŴS_1` is the **full-space** Fourier transform of `WS_1` (defined on all
of `ℝ³`); the box `B` enters only through the `b_p` operators.  So the sharp
mass is not a box quantity.  The corpus already owns the exact identity
`Commons.Analysis.Fourier.newtonian_energy_unitary`
(`∫_q ‖𝓕f(q)‖²/(4π²‖q‖²) = ∬(f x)(f y)/(4π‖x−y‖)`, the unitary-convention
form of `(2π)⁻³∫Ŵ_1(p)²/p²`), together with the χ-Taylor
`NewtonCoulomb.i2_integral_xspace_fs` and
`SmallBoxBogMainTerm.mainMassCoeff_le_coarse`.  **So if the D1 b-mode layer is
built with the continuum (full-space) momentum modes — as FS do — the
sharp-mass step is EXACT and already machine-checked.**  This is the
Session-268 part-4 recommendation, now with a second, dimension-theoretic
argument.

## 3. THE BOX↔CONTINUUM DISCRETISATION ERROR (box-mode route)

If the corpus's box-Neumann modes are used instead, the sharp mass
`Σ_{k≠0}λ_k⁻¹⟨W,ê_k⟩²` (equal to `∬WWG_s`, `G_s` = box Neumann Green
function) must be compared with `D := ∬WW/(4π|x−y|)`.  Numerically
(STATUS-268 part 2) `Σ/D = 1 − c·R/s` with `c ∈ [3.2,5.0]`: the correction is
FIRST order in `R/s` and NEGATIVE (the box-mode sum UNDER-estimates).  Since
the D1 inequality needs an UPPER bound on the sharp mass, the sign is
FAVOURABLE — but the rate `R/s` (not `(R/s)²`) must be used in
`lm_appbogolubov_refined_target`'s `(1+C(R/s)²)` factor, or `A ≤ D` proven
outright.  The analytic route is the Ewald (heat-kernel image) splitting,
whose 1-D building blocks are the fleet's `neumann_heat_one_dim_images`
(exact spectral ⟷ image identity), `neumann_heat_one_dim_sub_le` and
`theta_image_sum_le`.

## 4. THE PROVEN REDUCTION (this module)

  * `volume_diagonal_eq_zero` — the diagonal is null in `ℝ³ × ℝ³`;
  * `coulomb_energy_ge` — for `W ≥ 0`, `∫W`-integrable, with
    `tsupport W ⊆ ball 0 R`: `(∫W)²/(2R) ≤ ∬W(x)W(y)/‖x−y‖`;
  * `newtonian_energy_perturb_le` — a deviation kernel bounded by `C/s` on
    `supp W × supp W` perturbs the double energy by at most `(C/s)(∫W)²`;
  * `sharpMass_le_of_kernel_dev` — the interface: if the box Green kernel
    deviates from `(4π‖x−y‖)⁻¹` by at most `C/s` on `supp W × supp W`, then
    the box sharp mass is at most `(1+8πC·R/s)` times the continuum one.

So the ONLY remaining analytic input of the box-mode route is the kernel
bound; it holds on the box "inner" region (`dist(x,∂B) ≳ s`) and fails near
`∂B` (the reflected Neumann image approaches the point itself), so it must be
paired with the corpus's `χ_B` truncation (`hsR : R0 ≤ s·chiR0`) or with a
separate boundary argument.  The continuum route needs no kernel estimate at
all: its obligation is the CONSISTENCY of the corpus's box-mode kinetic
`kinWord` with the continuum kinetic `∫[2π‖q‖−c]_+²|𝓕(χ_BQ_iΦ)|²dq`.

### 3.1 The sign/size structure of the kernel deviation (numeric, Session-269)

Direct evaluation of `R_s(x,y) := ∫_0^∞(p_N^{(3)}(t,x,y) − K_t(x,y) − s^{-3})dt`
(= `G_s(x,y) − (4π‖x−y‖)⁻¹`) on the unit cube gives:

  * box interior (`max(|x_j|,|y_j|) ≤ 0.45`, `s = 1`): `R_s ∈ [−0.28, −0.08]`
    — NEGATIVE and bounded by `~0.3/s` (the FAVOURABLE sign for the box-mode
    sharp mass, `A ≤ D`);
  * `R_s(x,x) = −0.219` at the centre (so `R_s` is finite on the diagonal, as
    it must be: both singular parts cancel);
  * near a face (`x = y = 0.49·e₁`, `s = 1`): `R_s = +3.70` — POSITIVE and of
    size `≈ 1/(4π·2·dist(x,∂B))` (the reflected Neumann image).  Hence `R_s`
    is NOT globally nonpositive and the kernel bound is genuinely
    region-dependent: `|R_s(x,y)| ≤ C/δ` with `δ := dist(supp W, ∂B)`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 800000

noncomputable section
open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators ENNReal
namespace Submission
open _root_.BoseGases
namespace BoseGases

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-! ## 4.1 The diagonal is null in the product measure -/

/-- The diagonal `{p : ℝ³ × ℝ³ | p.1 = p.2}` is `volume`-null: its sections
are singletons, and `volume` has no atoms. -/
lemma volume_diagonal_eq_zero :
    (volume : Measure (ℝ³ × ℝ³)) {p : ℝ³ × ℝ³ | p.1 = p.2} = 0 := by
  have hmeas : MeasurableSet {p : ℝ³ × ℝ³ | p.1 = p.2} :=
    (isClosed_eq continuous_fst continuous_snd).measurableSet
  have hvol : (volume : Measure (ℝ³ × ℝ³)) = (volume : Measure ℝ³).prod volume := rfl
  rw [hvol, Measure.prod_apply hmeas]
  have h0 : ∀ a : ℝ³, volume (Prod.mk a ⁻¹' {p : ℝ³ × ℝ³ | p.1 = p.2}) = 0 := by
    intro a
    have hset : Prod.mk a ⁻¹' {p : ℝ³ × ℝ³ | p.1 = p.2} = {a} := by
      ext b; simp
    rw [hset, measure_singleton]
  simp only [h0, lintegral_zero]

/-- Almost every pair in `ℝ³ × ℝ³` is off the diagonal. -/
lemma ae_fst_ne_snd : ∀ᵐ p : ℝ³ × ℝ³, p.1 ≠ p.2 := by
  rw [MeasureTheory.ae_iff]
  simpa using volume_diagonal_eq_zero

/-! ## 4.2 The ball lower bound for the Newtonian double energy -/

/-- **Ball lower bound for the Newtonian double energy.**  For `0 < R`,
`W ≥ 0`, `Integrable W`, with `tsupport W ⊆ ball 0 R` (so `‖x−y‖ ≤ 2R` off
the diagonal on the support), the Coulomb double integral dominates
`(∫W)²/(2R)`:

    `(∫W)²/(2R) ≤ ∬ W(x)W(y)/‖x−y‖`.

Equivalently `(∫W)²/R ≤ 4π∬W(x)W(y)/(4π‖x−y‖)`: the absolute lower bound on
the corpus's Newtonian mass that converts a `(C/s)(∫W)²` kernel error into a
relative `8πC·R/s` error. -/
theorem coulomb_energy_ge {W : ℝ³ → ℝ} {R : ℝ} (hR : 0 < R) (hWnn : 0 ≤ W)
    (hWint : Integrable W) (hWsupp : tsupport W ⊆ ball (0 : ℝ³) R)
    (hint : Integrable (fun p : ℝ³ × ℝ³ => W p.1 * W p.2 * (‖p.1 - p.2‖ : ℝ)⁻¹)) :
    (∫ x, W x) ^ 2 / (2 * R) ≤
      ∫ p : ℝ³ × ℝ³, W p.1 * W p.2 * (‖p.1 - p.2‖ : ℝ)⁻¹ := by
  have h2R : (0 : ℝ) < 2 * R := by linarith
  have hprod : Integrable (fun p : ℝ³ × ℝ³ => W p.1 * W p.2) := hWint.mul_prod hWint
  have hsmall : Integrable (fun p : ℝ³ × ℝ³ => W p.1 * W p.2 * (2 * R)⁻¹) :=
    hprod.mul_const _
  have hae : (fun p : ℝ³ × ℝ³ => W p.1 * W p.2 * (2 * R)⁻¹)
      ≤ᵐ[volume] fun p : ℝ³ × ℝ³ => W p.1 * W p.2 * (‖p.1 - p.2‖ : ℝ)⁻¹ := by
    filter_upwards [ae_fst_ne_snd] with p hp
    by_cases hx : p.1 ∈ tsupport W
    · by_cases hy : p.2 ∈ tsupport W
      · have h1 : ‖p.1‖ ≤ R := by
          have h := hWsupp hx
          rw [mem_ball, dist_eq_norm, sub_zero] at h
          exact h.le
        have h2 : ‖p.2‖ ≤ R := by
          have h := hWsupp hy
          rw [mem_ball, dist_eq_norm, sub_zero] at h
          exact h.le
        have hd : ‖p.1 - p.2‖ ≤ 2 * R := by
          calc ‖p.1 - p.2‖ ≤ ‖p.1‖ + ‖p.2‖ := norm_sub_le _ _
            _ ≤ R + R := add_le_add h1 h2
            _ = 2 * R := by ring
        have hpos : 0 < ‖p.1 - p.2‖ := norm_pos_iff.2 (sub_ne_zero.2 hp)
        have : (2 * R)⁻¹ ≤ (‖p.1 - p.2‖ : ℝ)⁻¹ := (inv_le_inv₀ h2R hpos).2 hd
        exact mul_le_mul_of_nonneg_left this (mul_nonneg (hWnn _) (hWnn _))
      · have hz : W p.2 = 0 := image_eq_zero_of_notMem_tsupport hy
        simp [hz]
    · have hz : W p.1 = 0 := image_eq_zero_of_notMem_tsupport hx
      simp [hz]
  have hstep : (∫ x, W x) ^ 2 / (2 * R) =
      ∫ p : ℝ³ × ℝ³, W p.1 * W p.2 * (2 * R)⁻¹ := by
    have hv : (volume : Measure (ℝ³ × ℝ³)) = (volume : Measure ℝ³).prod volume := rfl
    rw [div_eq_mul_inv, integral_mul_const, hv, integral_prod_mul]
    ring
  rw [hstep]
  exact integral_mono_ae hsmall hint hae

/-! ## 4.3 The kernel-perturbation bound -/

/-- **Kernel-perturbation bound.**  A deviation kernel `Dev`, bounded by
`C/s` on `supp W × supp W`, changes the double energy by at most `(C/s)(∫W)²`
in absolute value. -/
theorem newtonian_energy_perturb_le {W : ℝ³ → ℝ} {Dev : ℝ³ → ℝ³ → ℝ}
    {C δ : ℝ} (hδ : 0 < δ) (hC : 0 ≤ C) (hWnn : 0 ≤ W)
    (hdev : ∀ x y, x ∈ tsupport W → y ∈ tsupport W → |Dev x y| ≤ C / δ)
    (hint : Integrable (fun p : ℝ³ × ℝ³ => W p.1 * W p.2 * Dev p.1 p.2))
    (hWint : Integrable W) :
    |∫ p : ℝ³ × ℝ³, W p.1 * W p.2 * Dev p.1 p.2| ≤ (C / δ) * (∫ x, W x) ^ 2 := by
  have hCs : 0 ≤ C / δ := div_nonneg hC hδ.le
  have hbdd : Integrable (fun p : ℝ³ × ℝ³ => (W p.1 * W p.2) * (C / δ)) :=
    (hWint.mul_prod hWint).mul_const _
  have hae : (fun p : ℝ³ × ℝ³ => ‖W p.1 * W p.2 * Dev p.1 p.2‖)
      ≤ᵐ[volume] fun p : ℝ³ × ℝ³ => (W p.1 * W p.2) * (C / δ) := by
    filter_upwards with p
    by_cases hx : p.1 ∈ tsupport W
    · by_cases hy : p.2 ∈ tsupport W
      · have h1 : ‖W p.1 * W p.2 * Dev p.1 p.2‖ = (W p.1 * W p.2) * |Dev p.1 p.2| := by
          rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg (hWnn _), abs_of_nonneg (hWnn _)]
        rw [h1]
        exact mul_le_mul_of_nonneg_left (hdev p.1 p.2 hx hy) (mul_nonneg (hWnn _) (hWnn _))
      · have hz : W p.2 = 0 := image_eq_zero_of_notMem_tsupport hy
        simp [hz]
    · have hz : W p.1 = 0 := image_eq_zero_of_notMem_tsupport hx
      simp [hz]
  have hnorm : Integrable (fun p : ℝ³ × ℝ³ => ‖W p.1 * W p.2 * Dev p.1 p.2‖) :=
    hint.norm
  have hmain : ∫ p : ℝ³ × ℝ³, ‖W p.1 * W p.2 * Dev p.1 p.2‖
      ≤ ∫ p : ℝ³ × ℝ³, (W p.1 * W p.2) * (C / δ) := integral_mono_ae hnorm hbdd hae
  have hval : ∫ p : ℝ³ × ℝ³, (W p.1 * W p.2) * (C / δ) = (C / δ) * (∫ x, W x) ^ 2 := by
    have hv : (volume : Measure (ℝ³ × ℝ³)) = (volume : Measure ℝ³).prod volume := rfl
    rw [integral_mul_const, hv, integral_prod_mul]
    ring
  calc |∫ p : ℝ³ × ℝ³, W p.1 * W p.2 * Dev p.1 p.2|
      = ‖∫ p : ℝ³ × ℝ³, W p.1 * W p.2 * Dev p.1 p.2‖ := by rw [Real.norm_eq_abs]
    _ ≤ ∫ p : ℝ³ × ℝ³, ‖W p.1 * W p.2 * Dev p.1 p.2‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ p : ℝ³ × ℝ³, (W p.1 * W p.2) * (C / δ) := hmain
    _ = (C / δ) * (∫ x, W x) ^ 2 := hval

/-! ## 4.4 The sharp-mass comparison from a Green-kernel bound -/

/-- **The sharp-mass comparison from a Green-kernel bound** — the interface
the D1 body consumes.  If `W ≥ 0` is integrable and supported in `ball 0 R`,
and the box Green kernel `(4π‖x−y‖)⁻¹ + Dev` deviates from the free Newtonian
kernel `(4π‖x−y‖)⁻¹` by at most `C/δ` on `supp W × supp W`, then

    `∬ W(x)W(y)((4π‖x−y‖)⁻¹ + Dev(x,y)) ≤ (1 + 8πC·R/δ)·∬ W(x)W(y)(4π‖x−y‖)⁻¹`.

The relative slack `8πC·R/δ` is exactly the `R/δ`-rate that the box-mode
transcription of the sharp mass costs (Session-268 part 2).  In the
application `δ` is the INNER DISTANCE `dist(supp W, ∂B)` (numerics Session-269:
`G_s(x,y) − (4π‖x−y‖)⁻¹` is bounded by `C/δ` and CHANGES SIGN — negative in
the box interior, of size `~1/(4π·2·dist(y,∂B))` near a face — so the estimate
must be stated with `δ`, and `δ ≳ s` (via the corpus's `hsR`) is needed to
recover the `R/s` rate). -/
theorem sharpMass_le_of_kernel_dev {W : ℝ³ → ℝ} {Dev : ℝ³ → ℝ³ → ℝ} {R C δ : ℝ}
    (hR : 0 < R) (hδ : 0 < δ) (hC : 0 ≤ C) (hWnn : 0 ≤ W) (hWint : Integrable W)
    (hWsupp : tsupport W ⊆ ball (0 : ℝ³) R)
    (hdev : ∀ x y, x ∈ tsupport W → y ∈ tsupport W → |Dev x y| ≤ C / δ)
    (hintC : Integrable (fun p : ℝ³ × ℝ³ => W p.1 * W p.2 * (‖p.1 - p.2‖ : ℝ)⁻¹))
    (hintD : Integrable (fun p : ℝ³ × ℝ³ => W p.1 * W p.2 * Dev p.1 p.2)) :
    ∫ p : ℝ³ × ℝ³, W p.1 * W p.2 * ((4 * π * ‖p.1 - p.2‖ : ℝ)⁻¹ + Dev p.1 p.2)
      ≤ (1 + 8 * π * C * R / δ) *
          ∫ p : ℝ³ × ℝ³, W p.1 * W p.2 * (4 * π * ‖p.1 - p.2‖ : ℝ)⁻¹ := by
  have hfree_eq : (fun p : ℝ³ × ℝ³ => W p.1 * W p.2 * (4 * π * ‖p.1 - p.2‖ : ℝ)⁻¹)
      = fun p : ℝ³ × ℝ³ => (4 * π)⁻¹ * (W p.1 * W p.2 * (‖p.1 - p.2‖ : ℝ)⁻¹) := by
    funext p; rw [mul_inv]; ring
  have hfree_int : Integrable (fun p : ℝ³ × ℝ³ =>
      (4 * π)⁻¹ * (W p.1 * W p.2 * (‖p.1 - p.2‖ : ℝ)⁻¹)) := hintC.const_mul _
  have hfree_val : ∫ p : ℝ³ × ℝ³, W p.1 * W p.2 * (4 * π * ‖p.1 - p.2‖ : ℝ)⁻¹
      = (4 * π)⁻¹ * ∫ p : ℝ³ × ℝ³, W p.1 * W p.2 * (‖p.1 - p.2‖ : ℝ)⁻¹ := by
    rw [hfree_eq, integral_const_mul]
  -- the deviation contributes at most (C/s)(∫W)²
  have hDle : ∫ p : ℝ³ × ℝ³, W p.1 * W p.2 * Dev p.1 p.2 ≤ (C / δ) * (∫ x, W x) ^ 2 := by
    have h := newtonian_energy_perturb_le (W := W) (Dev := Dev) hδ hC hWnn hdev hintD hWint
    exact (abs_le.mp h).2
  -- and (C/s)(∫W)² ≤ (8πCR/s)·(free energy)
  have hkey : (C / δ) * (∫ x, W x) ^ 2
      ≤ (8 * π * C * R / δ) * ((4 * π)⁻¹ *
        ∫ p : ℝ³ × ℝ³, W p.1 * W p.2 * (‖p.1 - p.2‖ : ℝ)⁻¹) := by
    have hce := coulomb_energy_ge (W := W) (R := R) hR hWnn hWint hWsupp hintC
    have hle : (∫ x, W x) ^ 2 ≤
        2 * R * ∫ p : ℝ³ × ℝ³, W p.1 * W p.2 * (‖p.1 - p.2‖ : ℝ)⁻¹ := by
      rw [div_le_iff₀ (by linarith : (0 : ℝ) < 2 * R)] at hce
      linarith [hce]
    calc (C / δ) * (∫ x, W x) ^ 2
        ≤ (C / δ) * (2 * R *
            ∫ p : ℝ³ × ℝ³, W p.1 * W p.2 * (‖p.1 - p.2‖ : ℝ)⁻¹) :=
          mul_le_mul_of_nonneg_left hle (div_nonneg hC hδ.le)
      _ = (8 * π * C * R / δ) * ((4 * π)⁻¹ *
            ∫ p : ℝ³ × ℝ³, W p.1 * W p.2 * (‖p.1 - p.2‖ : ℝ)⁻¹) := by
          have h4 : (4 * π : ℝ) ≠ 0 := by positivity
          have hd' : δ ≠ 0 := ne_of_gt hδ
          field_simp
          ring
  rw [show (fun p : ℝ³ × ℝ³ => W p.1 * W p.2 * ((4 * π * ‖p.1 - p.2‖ : ℝ)⁻¹ + Dev p.1 p.2))
      = fun p : ℝ³ × ℝ³ => (4 * π)⁻¹ * (W p.1 * W p.2 * (‖p.1 - p.2‖ : ℝ)⁻¹)
          + W p.1 * W p.2 * Dev p.1 p.2 by funext p; rw [mul_inv]; ring]
  rw [integral_add hfree_int hintD, integral_const_mul, hfree_val]
  nlinarith [hDle, hkey]

/-! ## 5 The reciprocal-weights algebra (the Session-267 audit fact) -/

/-- **The two D1 weights are reciprocal above threshold**: the box-mode
inverse-square weight times the square symbol equals `1` for
`r = π‖k‖/s > c`.  This is the algebraic content of the Session-267 finding
that `bModeDiag ≤ tBword` (square-symbol weight dominated by the
inverse-square weight) is false, and that the D1 kinetic word must carry the
SQUARE weight. -/
lemma boxModeCoeff_mul_fsKinCoeff {s c : ℝ} (hs : 0 < s) (hc : 0 ≤ c)
    (k : Fin 3 → ℕ) (hk : c < Real.pi * boxModeNorm k / s) :
    boxModeCoeff s c k * fsKinCoeff c (Real.pi * boxModeNorm k / s) = 1 := by
  rw [boxModeCoeff_eq_fsKinCoeff_inv]
  exact inv_mul_cancel₀ (ne_of_gt (fsKinCoeff_pos_of_lt hc hk))


/-! ## 6 The SQUARE-weighted kinetic word — the D1 KINETIC (Session-269) -/

/-- `[r−c]₊² ≤ r²` for `r ≥ 0`: dropping the threshold only decreases the
kinetic symbol, which is why the FS kinetic `[√−Δ−c]₊²` is dominated by the
corpus's physical `kinWord`. -/
lemma fsKinCoeff_le_sq {c r : ℝ} (hc : 0 ≤ c) (hr : 0 ≤ r) : fsKinCoeff c r ≤ r ^ 2 := by
  dsimp [fsKinCoeff]
  have h1 : 0 ≤ max (r - c) 0 := le_max_right _ _
  have h2 : max (r - c) 0 ≤ r := max_le (by linarith) hr
  nlinarith [h1, h2]

/-- **the box-discrete SQUARE-weighted excited-kinetic mode sum**
`kMode(s,c,f) := Σ_k [π‖k‖/s − c]₊²·‖⟨ê_k, f⟩‖²` — the corpus's D1 KINETIC
word (FS `Qχ[√−Δ−c]₊²χQ` diagonalised in the normalised `boxNeumann3` basis,
with the Session-269 symbol resolution: the SQUARE of the positive part).
NOT to be confused with `SmallBoxTBmode.tBmode` (the reciprocal
inverse-square weight, which is the sharp-mass/error weight). -/
noncomputable def kMode (s c : ℝ) (hs : 0 < s) (f : Lp ℝ 2 (boxVol s)) : ℝ :=
  ∑' k : Fin 3 → ℕ,
    fsKinCoeff c (Real.pi * boxModeNorm k / s) * ‖inner ℝ (boxModeOrtho s hs k) f‖ ^ 2

/-- nonnegativity of the D1 kinetic mode sum. -/
lemma kMode_nonneg (s c : ℝ) (hs : 0 < s) (f : Lp ℝ 2 (boxVol s)) :
    0 ≤ kMode s c hs f :=
  tsum_nonneg fun k => mul_nonneg (fsKinCoeff_nonneg c _) (sq_nonneg _)

/-- the per-particle D1 kinetic word: the integral of `kMode` over the
excitation slices (the exact analogue of `SmallBoxTBword.tBwordI` with the
SQUARE weight). -/
noncomputable def kModeWordI (s c : ℝ) (hs : 0 < s) (hc : 0 < c) {n : ℕ}
    (i : Fin (n + 1)) (Φ : X (n + 1) → ℝ) (hΦc : Continuous Φ) : ℝ :=
  ∫ r in abox n s, kMode s c hs (excSlice s hs i Φ hΦc r)

/-- **the D1 KINETIC word** `Σ_i Q_iχ[√−Δ−c]₊²χQ_i` in the corpus's
box-Neumann transcription (the SQUARE-weighted analogue of `tBword`). -/
noncomputable def kModeWord (s c : ℝ) (hs : 0 < s) (hc : 0 < c) {n : ℕ}
    (Φ : X (n + 1) → ℝ) (hΦc : Continuous Φ) : ℝ :=
  ∑ i : Fin (n + 1), kModeWordI s c hs hc i Φ hΦc

lemma kModeWordI_nonneg (s c : ℝ) (hs : 0 < s) (hc : 0 < c) {n : ℕ}
    (i : Fin (n + 1)) (Φ : X (n + 1) → ℝ) (hΦc : Continuous Φ) :
    0 ≤ kModeWordI s c hs hc i Φ hΦc :=
  integral_nonneg fun r => kMode_nonneg s c hs _

lemma kModeWord_nonneg (s c : ℝ) (hs : 0 < s) (hc : 0 < c) {n : ℕ}
    (Φ : X (n + 1) → ℝ) (hΦc : Continuous Φ) :
    0 ≤ kModeWord s c hs hc Φ hΦc :=
  Finset.sum_nonneg fun i _ => kModeWordI_nonneg s c hs hc i Φ hΦc

/-- **D1 — `lm:appbogolubov` in the corpus refined form with the CORRECTED
left-hand side** (Session-269).  This is
`SmallBoxBogolubovLayer.lm_appbogolubov_refined_target` with
(i) the abstract word `tBword : (X N → ℝ) → ℝ` replaced by the CONCRETE
SQUARE-weighted kinetic word `kModeWord s c0 Φ` (FS's
`Σ_i Qχ[√−Δ−c]₊²χQ_i`; the `∀`-quantified abstract word made the old
statement FALSE as a closed `Prop` — the `def`-Prop audit class of
STATUS.md Session-268 part 3), and
(ii) the state space fixed to `X (N+1)` (so that `kModeWord`'s slice
machinery applies; the `N = 0` case is trivial).

The right-hand side is unchanged: the sharp mass
`−½(1+C(R/s)²)(1+Cc₀(av))·g0w0Mass·(N̂+1)N̂/s³`, the log/`c₀³` error bracket
and the `n₊`-term.  Per Sessions-269 parts 1–3 the sharp-mass step is done
EITHER in the continuum (exact, via `newtonian_energy_unitary` +
`i2_integral_xspace_fs` + `mainMassCoeff_le_coarse`) OR via the box-mode
kernel estimate reduced by `sharpMass_le_of_kernel_dev` above. -/
def lm_appbogolubov_refined_concrete {N : ℕ} {s c0 : ℝ} (hs : 0 < s) (hc0 : 0 < c0)
    {v : ℝ³ → ℝ} (hv_nonneg : 0 ≤ v) (hvrad : IsRadial v) (hv_memL1 : MemLp v 1)
    {R : ℝ} (hR : 0 < R) (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v)
    (hsR : R ≤ s * chiR0) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ (Φ : X (N + 1) → ℝ) (hΦc : ContDiff ℝ ∞ Φ),
    (∫ x in abox (N + 1) s, (Φ x) ^ 2) = 1 →
    kModeWord s c0 hs hc0 Φ hΦc.continuous + q4PairWord (ℓ := s) (v := v) h (Φ := Φ) ≥
      - (1 / 2 : ℝ) * (1 + C * (R / s) ^ 2) * (1 + C * c0 * (a v))
          * g0w0Mass (v := v) h * ((((N : ℝ) + 1) * ((N : ℝ) + 1)) / s ^ 3)
      - C * ((a v) ^ 2 * c0 * Real.log ((c0 * (a v))⁻¹)
                * ((((N : ℝ) + 1) * ((N : ℝ) + 1)) / s ^ 3)
            + (a v) ^ 4 * (c0 ^ 3)⁻¹ * ((((N : ℝ) + 1) / s ^ 3) ^ 3) * (((N : ℝ) + 1) / s ^ 3) * s ^ 3
            + (a v) * c0 ^ 3 * (((N : ℝ) + 1) / s ^ 3) * s ^ 3)
      - C * (a v) * (((N : ℝ) + 1) / s ^ 3) * cnPlus s Φ

end BoseGases
end Submission
