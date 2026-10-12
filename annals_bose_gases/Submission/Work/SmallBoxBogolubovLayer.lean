import ChallengeDeps
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Submission.Fock2Mode
import Submission.Work.A0Bridge
import Submission.Work.A0Core
import Submission.Work.FibreLocalG2
import Submission.Work.KineticBound
import Submission.Work.SmallBoxBogolubovKinetic
import Submission.Work.SmallBoxKernelMass
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Session-225 — the b_p-mode diagonalization layer (step (i) of the
Session-224 plan): the zero-point algebra + the tBword targets

Per the Session-224 design-note analysis (grounded in the full reading of
FS final_v2.tex ll.3500–4050), the corpus needs ONE new object for the
sharp Bogolubov step (`lm:appbogolubov`) — the per-particle
weighted-excited kinetic word `tBword` (FS
`Σ_i Q_B,i χ_B,i [√−Δ−(dsℓ)⁻¹]₊⁻² χ_B,i Q_B,i`) — whose only genuinely-new
content is its b_p-plane-wave DIAGONALIZATION against the A₂/Fock2Mode
structure.  This module plants that layer:

**Section A (PROVED, sorry-free)** — the real-algebra core of the
lm:appbogolubov chain:
  * `bog_zero_point_gap_le` — the coarse zero-point gap
    `A − s ≤ B²/A` for `s := √(A²−B²)` (`bogS`), `0 < A`, `|B| ≤ A`;
  * `bog_abs_B_le_of_half` — `|B| ≤ A/2 ⟹ |B| ≤ A` (Fock2Mode regime);
  * `bog_zero_point_gap_split` — the refined split
    `A − s ≤ B²/(2A) + B⁴/A³` (exact identity
    `A−s = B²/(2A) + B⁴/(2A(A+s)²)`; all universal constants in FS are
    absorbed, so `C := 1` suffices);
  * `fock_ground_estimate_sq` / `fock_ground_estimate_refined` — the
    per-mode Fock2Mode bounds with the `B²/A`- resp. `B²/(2A)+B⁴/A³`-
    zero-point packaged from `Fock2Mode.fock_ground_estimate` + the gap
    lemmas (FS: `h(p) ≥ −½(𝒜−√(𝒜²−B²))n₀|B|⁻¹∫χ²` then the two bounds).
  * **Section A.2 (the eq:appgapestimate replay, step (ii) of the plan)**:
    `eT_regime_gap_bound` — `s·C′·√(μ(av)) ≤ √ε_T ⟹ C′²μ(av)s² ≤ ε_T`
    (the squared eq:appdellsassumption regime); `eT_gap_absorbs_onebody` —
    that regime + the ε_T-cap `36·Cgap·ε_T ≤ C′²` give
    `Cgap·μ(av)·n₊(Φ) ≤ kinWord N s Φ` (the corpus replay of FS
    `½ε_T(1+π⁻²)⁻¹(dℓ)⁻²Q ≥ C′²(1+π⁻²)⁻¹μa·n₊`), assembled from
    `KineticBound.kinWord_ge_mu_a_cnPlus`.
  * **Section A.3 (per-mode half-regime)**: `mode_coeff_lower` / `mode_coeff_pos`
    (the diagonal coefficient `𝒜 := d·[r−c]₊² + 2Ka ≥ 2Ka` and its
    positivity) and `mode_half_regime` — `|B(p)| ≤ Ka ⟹ |B(p)| ≤ 𝒜/2`
    (lm:appbogolubov's `|ℬ|/𝒜 ≤ 1/2` Fock2Mode hypothesis).
  * **Section A.4 (momentum-volume leaf of the final-integral layer)**:
    `momentum_ball_integral_one` — `∫_{‖p‖<R}1 dp = (4π/3)R³` over the
    corpus `EuclideanSpace ℝ (Fin 3)` conventions (from `integral_const` on
    the restricted measure + `volume_ball_open_r3` + `toReal_ofReal`); the
    source of lm:appbogolubov's `∫_{|p|<2c}1dp ≤ C(dsℓ)⁻³` at `R := 2c`.

**Section B (typeset def-Props, sorry-free — the precise statements of
the layer)**:
  * `tBword_error_budget_target` (D1, SESSION-267 restatement of the former
    `tBword_diag_target`) — `tBword` (the box-discrete inverse-square
    `[·]₊⁻²`-weighted mode sum, = the Bogoliubov ERROR budget `ℬ²/𝒜`) is
    nonnegative and dominated by `C·cnPlus`; the former "domination of the
    square-symbol diagonal kinetic" shape is FALSE (reciprocal weights);
  * `a2_mode_expansion_target` (D2) — the corpus A₂-word `q4PairWord`
    equals the cross b-mode form `½(2π)⁻³∫Ŵ₁(p)(b_p†b_{−p}†+b_{−p}b_p)dp`;
  * `a1_bound_target` — eq:A1estimate (`A₁ ≤ C·K_s·a·(n₀+1)/|B|·n₊`);
  * `lm_appbogolubov_refined_target` — FS eq:refinedaprioribog in corpus
    variables (tBword + q4PairWord ≥ −½(1+C(R/s)²)(1+C·c0·(av))·ĝω(0)
    ·(N̂+1)N̂/s³ − [log/c0³-error bracket] − C·(av)(N̂+1)n₊/s³), refining
    `SmallBoxBogolubovTarget.bogolubov_sharp_bound_target` with the error
    tail explicit; its `−½ĝω(0)`-part cancels the ∬w₂-excess of the
    A₀-form exactly (`A0Bridge.q0word_w2_mass_sub`).

**Section C (D1 definitional layer)**: `fsInvCoeff c r := [2πr−c]₊⁻²` (the
  weighted-kinetic multiplier symbol in the unitary convention, Session-228)
  + `fsInvCoeff_nonneg`, and the target `tBword_multForm_target` (the
  per-particle multiplier quadratic form `∫_q ‖𝓕 f q‖²·[2π‖q‖−c]₊⁻²dq` on
  Schwartz slices; `𝓕 = SchwartzMap.fourierTransformCLM ℂ`; slices lift via
  Mathlib's `HasCompactSupport.toSchwartzMap`).

The proof obligations of the layer are the bodies of the Section-B Props
(the Fourier/Newtonian layer, next stretch); Section A is the real algebra
they reduce to and is committed here.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

open MeasureTheory Metric
open scoped ContDiff Topology Real BigOperators ENNReal
namespace Submission
open _root_.BoseGases
namespace BoseGases

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-- **zero-point gap (coarse)**: for `0 < A` and `|B| ≤ A`, the Bogoliubov
zero-point constant `A − s` (`s := √(A²−B²)`) is at most `B²/A`. -/
lemma bog_zero_point_gap_le {A B : ℝ} (hA : 0 < A) (hB : |B| ≤ A) :
    A - bogS A B ≤ B ^ 2 / A := by
  have hs2 : bogS A B ^ 2 = A ^ 2 - B ^ 2 := bogS_sq hB
  have hs0 : 0 ≤ bogS A B := bogS_nonneg A B
  have hsA : bogS A B ≤ A := bogS_sq_le (le_of_lt hA) hB
  have hprod : (A - bogS A B) * A ≤ B ^ 2 := by
    have h1 : (A - bogS A B) * A = A ^ 2 - A * bogS A B := by ring
    rw [h1]
    nlinarith [hs2, hsA, hs0]
  exact (le_div_iff₀ hA).2 hprod

/-- **half-regime implies Fock2Mode regime**: `|B| ≤ A/2` with `0 < A`
gives `|B| ≤ A`. -/
lemma bog_abs_B_le_of_half {A B : ℝ} (hA : 0 < A) (hB : |B| ≤ A / 2) :
    |B| ≤ A := by
  exact le_trans hB (by nlinarith)

/-- refined zero-point split, C := 1: `A − s = B²/(A+s) = B²/(2A) + B⁴/(2A(A+s)²) ≤ B²/(2A) + B⁴/A³`. -/
lemma bog_zero_point_gap_split {A B : ℝ} (hA : 0 < A) (hB : |B| ≤ A) :
    A - bogS A B ≤ B ^ 2 / (2 * A) + B ^ 4 / A ^ 3 := by
  have hs2 : bogS A B ^ 2 = A ^ 2 - B ^ 2 := bogS_sq hB
  have hs0 : 0 ≤ bogS A B := bogS_nonneg A B
  have hAs : A + bogS A B ≠ 0 := bog_denom_ne_zero hA hB
  have hAps : 0 < A + bogS A B := by nlinarith [hA, hs0]
  have hid : (A - bogS A B) * (A + bogS A B) = B ^ 2 := by nlinarith [hs2]
  have hgap : A - bogS A B = B ^ 2 / (A + bogS A B) := by
    rw [eq_div_iff hAs]
    exact hid
  -- identity 1/(A+s) − 1/(2A) = B²/(2A(A+s)²)
  have hdiff : (1 / (A + bogS A B)) - (1 / (2 * A)) = B ^ 2 / (2 * A * (A + bogS A B) ^ 2) := by
    field_simp [hAs, ne_of_gt hA]
    ring_nf at hid ⊢
    exact hid
  -- denominator comparison: A² ≤ 2(A+s)² (since A+s ≥ A)
  have hspA : A ≤ A + bogS A B := by nlinarith [hs0]
  have hsqle : A ^ 2 ≤ (A + bogS A B) ^ 2 := by
    exact sq_le_sq.mpr (by
      simpa [abs_of_nonneg (le_of_lt hA), abs_of_nonneg (le_of_lt hAps)] using hspA)
  have hdenle : A ^ 3 ≤ 2 * A * (A + bogS A B) ^ 2 := by
    have hA2 : 0 ≤ A := le_of_lt hA
    have hm := mul_le_mul_of_nonneg_left hsqle hA2   -- A·A² ≤ A·(2(A+s)²)
    nlinarith
  have hle12 : (1 / (2 * A * (A + bogS A B) ^ 2)) ≤ 1 / A ^ 3 := by
    have hposd : 0 < 2 * A * (A + bogS A B) ^ 2 := by positivity
    have hposA3 : 0 < A ^ 3 := pow_pos hA 3
    rw [one_div, one_div]
    exact (inv_le_inv₀ hposd hposA3).mpr hdenle
  -- multiply by B⁴ ≥ 0
  have hb4 : 0 ≤ B ^ 4 := by positivity
  have hleB : B ^ 4 / (2 * A * (A + bogS A B) ^ 2) ≤ B ^ 4 / A ^ 3 := by
    calc
      B ^ 4 / (2 * A * (A + bogS A B) ^ 2)
          = (1 / (2 * A * (A + bogS A B) ^ 2)) * B ^ 4 := by ring
      _ ≤ (1 / A ^ 3) * B ^ 4 := mul_le_mul_of_nonneg_right hle12 hb4
      _ = B ^ 4 / A ^ 3 := by ring
  calc
    A - bogS A B = B ^ 2 / (A + bogS A B) := hgap
    _ = B ^ 2 / (2 * A) + B ^ 2 * ((1 / (A + bogS A B)) - (1 / (2 * A))) := by ring
    _ = B ^ 2 / (2 * A) + B ^ 4 / (2 * A * (A + bogS A B) ^ 2) := by
          rw [hdiff]
          ring
    _ ≤ B ^ 2 / (2 * A) + B ^ 4 / A ^ 3 := by
          simpa [add_comm] using (add_le_add_right hleB (B ^ 2 / (2 * A)))


/-- **per-mode Fock2Mode bound (coarse, `B²/A` zero-point)**: from the ground
estimate `−(A−s)‖φ‖² ≤ fsQuad` and the zero-point gap `A−s ≤ B²/A`,
the per-mode pair form is bounded below by `−(B²/A)·‖φ‖²`. -/
lemma fock_ground_estimate_sq {A B : ℝ} (hA : 0 < A) (hB : |B| ≤ A) (M : ℕ)
    {φ : ℕ × ℕ → ℝ} (hφ : vanishOn M φ) :
    - (B ^ 2 / A) * rectNorm M φ ≤ fsQuad A B M φ := by
  have hg := fock_ground_estimate hA hB M hφ
  have hgap : A - bogS A B ≤ B ^ 2 / A := bog_zero_point_gap_le hA hB
  have hn : 0 ≤ rectNorm M φ := rectNorm_nonneg M φ
  have hmul : (A - bogS A B) * rectNorm M φ ≤ (B ^ 2 / A) * rectNorm M φ :=
    mul_le_mul_of_nonneg_right hgap hn
  have h1 : -((A - bogS A B) * rectNorm M φ) ≤ fsQuad A B M φ := by
    convert hg using 1
    ring
  calc
    - (B ^ 2 / A) * rectNorm M φ ≤ -((A - bogS A B) * rectNorm M φ) := by
        simpa [neg_mul] using neg_le_neg hmul
    _ ≤ fsQuad A B M φ := h1

/-- **per-mode Fock2Mode bound (refined, `B²/(2A) + B⁴/A³` zero-point)**: the
sharpened split of `bog_zero_point_gap_split` — used in the `|p| > 2c` range
of lm:appbogolubov's refined estimate (the `B⁴/A³`-correction integrates to
`Ca⁴(dsℓ)³((n+1)/|B|)³`). -/
lemma fock_ground_estimate_refined {A B : ℝ} (hA : 0 < A) (hB : |B| ≤ A) (M : ℕ)
    {φ : ℕ × ℕ → ℝ} (hφ : vanishOn M φ) :
    - (B ^ 2 / (2 * A) + B ^ 4 / A ^ 3) * rectNorm M φ ≤ fsQuad A B M φ := by
  have hg := fock_ground_estimate hA hB M hφ
  have hgap : A - bogS A B ≤ B ^ 2 / (2 * A) + B ^ 4 / A ^ 3 := bog_zero_point_gap_split hA hB
  have hn : 0 ≤ rectNorm M φ := rectNorm_nonneg M φ
  have hmul : (A - bogS A B) * rectNorm M φ ≤ (B ^ 2 / (2 * A) + B ^ 4 / A ^ 3) * rectNorm M φ :=
    mul_le_mul_of_nonneg_right hgap hn
  have h1 : -((A - bogS A B) * rectNorm M φ) ≤ fsQuad A B M φ := by
    convert hg using 1
    ring
  have hneg : -((B ^ 2 / (2 * A) + B ^ 4 / A ^ 3) * rectNorm M φ)
      ≤ -((A - bogS A B) * rectNorm M φ) := neg_le_neg hmul
  calc
    - (B ^ 2 / (2 * A) + B ^ 4 / A ^ 3) * rectNorm M φ
        = -((B ^ 2 / (2 * A) + B ^ 4 / A ^ 3) * rectNorm M φ) := by rw [neg_mul]
    _ ≤ -((A - bogS A B) * rectNorm M φ) := hneg
    _ ≤ fsQuad A B M φ := h1

/-! ## Section B — the b_p-mode setup and the tBword diagonalization targets
(typeset def-Props, sorry-free — the layer's precise statements; proof
obligations are the bodies, to be discharged by the Fourier/Newtonian
layer). -/

/-- **D1 — the `tBword` ERROR-budget target (Session-267 restatement of the
former `tBword_diag_target`)**.

`SmallBoxTBword.tBword_le` PROVES that the corpus's box-discrete
inverse-square-weighted mode sum
`tBword(Φ) := Σ_i tBmode(s, c0, χ_B·(Q_iΦ)-slice)`, i.e.
`Σ_k [π‖k‖/s − c0]₊⁻²·|c_k(slice)|²` summed over the particles' slices, is
nonnegative and at most `C(s,c0)·cnPlus s Φ`.  In FS `lm:appbogolubov` this
word is the ERROR budget of the per-mode Bogoliubov inequality:
`ℬ²/𝒜 ≤ (1/d)(Ka)²·[r−c]₊⁻²` (`d := |B|/(n+1)`, `r := |p|`;
`SmallBoxBogolubovLayer.mode_error_weight_le`), whose mode sum is
`(1/d)(Ka)²·tBword` — exactly the `−Ca((n+1)/|B|)n₊` term of
`eq:refinedaprioribog`.  It is NOT the "good kinetic": that is the
SQUARE-symbol object (the `kinWord` family, symbol
`[r−c]₊² = fsKinCoeff`), by `boxModeCoeff_eq_fsKinCoeff_inv`.

(Session-266/267: the previous target claimed the domination
`bModeDiag ≤ tBword` of a square-symbol-weighted diagonal b-mode kinetic by
the inverse-square-weighted word, which is FALSE — the two weights are
reciprocal, so no `[r−c]₊²`-weighted object can be dominated by a
`[r−c]₊⁻²`-weighted one.  The statement below is `tBword`'s correct role.)

The word is EXACTLY the corpus mode sum above, so the D1 body has only to
identify its slices; the constant is existential and uniform in `Φ`. -/
def tBword_error_budget_target {N : ℕ} {s c0 : ℝ} (hs : 0 < s) (hc0 : 0 < c0)
    {v : ℝ³ → ℝ} (hv_nonneg : 0 ≤ v) (hvrad : IsRadial v) (hv_memL1 : MemLp v 1)
    {R : ℝ} (hR : 0 < R) (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v)
    (tBword : (X N → ℝ) → ℝ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ Φ : X N → ℝ, ContDiff ℝ ∞ Φ →
    0 ≤ tBword Φ ∧ tBword Φ ≤ C * cnPlus s Φ

/-- **D2 — A₂-mode expansion**: the corpus A₂-word `q4PairWord` (FS
`½Σ_{i≠j} P_iP_j w₁ Q_jQ_i + h.c.` expectation, kernel `w₁ := wPairC s (g0 v h)`)
equals the cross b-mode form `bModeCross` =
`½(2π)⁻³∫Ŵ₁(p)(b_p†b_{−p}† + b_{−p}b_p)dp` (FS lm:appbogolubov, the A₂
second-quantization line). -/
def a2_mode_expansion_target {N : ℕ} {s : ℝ} (hs : 0 < s)
    {v : ℝ³ → ℝ} (hv_nonneg : 0 ≤ v) (hvrad : IsRadial v) (hv_memL1 : MemLp v 1)
    {R : ℝ} (hR : 0 < R) (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v)
    (bModeCross : (X N → ℝ) → ℝ) : Prop :=
  ∀ Φ : X N → ℝ, ContDiff ℝ ∞ Φ →
    q4PairWord (ℓ := s) (v := v) h (Φ := Φ) = bModeCross Φ

/-- **eq:A1estimate — the A₁ mass bound**: the added diagonal b-mode term
`A₁ := (2π)⁻³K_s a ∫(b_p†b_p + b_{−p}†b_{−p})dp` (corpus word `a1mass`)
satisfies `A₁ ≤ C·K_s·a·(n₀+1)/|B|·n₊` — in corpus count form
`≤ C·K_s·(av)·(N̂+1)·n₊/s³`. -/
def a1_bound_target {N : ℕ} {s K_s : ℝ} (hs : 0 < s) (hK : 0 ≤ K_s)
    {v : ℝ³ → ℝ} (hv_nonneg : 0 ≤ v) (hvrad : IsRadial v) (hv_memL1 : MemLp v 1)
    {R : ℝ} (hR : 0 < R) (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v)
    (a1mass : (X N → ℝ) → ℝ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ Φ : X N → ℝ, ContDiff ℝ ∞ Φ →
    a1mass Φ ≤ C * K_s * (a v) * (((N : ℝ) + 1) / s ^ 3) * cnPlus s Φ

/-- **lm:appbogolubov — corpus refined form (D1+D2+per-mode Fock2Mode
assembled, FS eq:refinedaprioribog)**: for a NORMALISED `N`-particle state
over the box of side `s` at threshold `c0` (`N̂ := (N : ℝ)`),

    tBword(Φ) + q4PairWord(Φ)
        ≥ −½(1+C(R/s)²)(1+C·c0·(av))·g0w0Mass·((N̂+1)N̂)/s³
          − C·[ (av)²c0·ln((c0·(av))⁻¹)·(N̂+1)N̂/s³
               + (av)⁴·(c0³)⁻¹·((N̂+1)/s³)³·(N̂/s³)·s³
               + (av)·c0³·(N̂/s³)·s³ ]
          − C·(av)·(N̂+1)·n₊(Φ)/s³

— the `−½(1+…)ĝω(0)`-part cancels the ∬w₂-excess of the A₀-form EXACTLY
(`A0Bridge.q0word_w2_mass_sub`); the log/`c0³`-error bracket is bounded by
the regime caps (`C′(μa³)^{1/2} ≤ ε_T^{1/2}a c0 ≤ … ≤ K_B(μa³)^{1/2}`,
`hKBcap`/`hRcap` of `SmallBoxDLBound`) and the `n₊`-term absorbed by the
small-scale gap.  This refines `bogolubov_sharp_bound_target` with the
error tail made explicit. -/
def lm_appbogolubov_refined_target {N : ℕ} {s c0 : ℝ} (hs : 0 < s) (hc0 : 0 < c0)
    {v : ℝ³ → ℝ} (hv_nonneg : 0 ≤ v) (hvrad : IsRadial v) (hv_memL1 : MemLp v 1)
    {R : ℝ} (hR : 0 < R) (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v)
    (hsR : R ≤ s * chiR0)
    (tBword : (X N → ℝ) → ℝ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ Φ : X N → ℝ, ContDiff ℝ ∞ Φ →
    (∫ x in abox N s, (Φ x) ^ 2) = 1 →
    tBword Φ + q4PairWord (ℓ := s) (v := v) h (Φ := Φ) ≥
      - (1 / 2 : ℝ) * (1 + C * (R / s) ^ 2) * (1 + C * c0 * (a v))
          * g0w0Mass (v := v) h * ((((N : ℝ) + 1) * (N : ℝ)) / s ^ 3)
      - C * ((a v) ^ 2 * c0 * Real.log ((c0 * (a v))⁻¹)
                * ((((N : ℝ) + 1) * (N : ℝ)) / s ^ 3)
            + (a v) ^ 4 * (c0 ^ 3)⁻¹ * ((((N : ℝ) + 1) / s ^ 3) ^ 3) * ((N : ℝ) / s ^ 3) * s ^ 3
            + (a v) * c0 ^ 3 * ((N : ℝ) / s ^ 3) * s ^ 3)
      - C * (a v) * (((N : ℝ) + 1) / s ^ 3) * cnPlus s Φ

/-! ## Section A.2 — the eq:appgapestimate replay at the small-box scale
(CLOSED; the (b)-property of the Session-224 plan, step (ii)) -/

/-- **eq:appdellsassumption ⟹ the squared regime** (Lemma 1 of the
eq:appgapestimate replay): from `s·C′·√(μ·(av)) ≤ √ε_T` (FS
`C′(μa³)^{1/2} ≤ ε_T^{1/2}a·s⁻¹` with `s := dℓ`), squaring gives
`C′²·μ·(av)·s² ≤ ε_T` (needs only `0 ≤ μ(av)`, `0 ≤ s, C′`). -/
lemma eT_regime_gap_bound {ε_T C' s μ av : ℝ} (hεT : 0 ≤ ε_T)
    (hμ : 0 ≤ μ) (hAv : 0 ≤ av) (hC' : 0 ≤ C') (hs : 0 ≤ s)
    (h : s * C' * Real.sqrt (μ * av) ≤ Real.sqrt ε_T) :
    C' ^ 2 * (μ * av) * s ^ 2 ≤ ε_T := by
  have hμav : 0 ≤ μ * av := mul_nonneg hμ hAv
  have hsq : (s * C' * Real.sqrt (μ * av)) ^ 2 ≤ (Real.sqrt ε_T) ^ 2 := by
    exact pow_le_pow_left₀ (by positivity : 0 ≤ s * C' * Real.sqrt (μ * av)) h 2
  have hcalc : (s * C' * Real.sqrt (μ * av)) ^ 2 = C' ^ 2 * (μ * av) * s ^ 2 := by
    calc
      (s * C' * Real.sqrt (μ * av)) ^ 2 = s ^ 2 * C' ^ 2 * (Real.sqrt (μ * av)) ^ 2 := by ring
      _ = s ^ 2 * C' ^ 2 * (μ * av) := by rw [Real.sq_sqrt hμav]
      _ = C' ^ 2 * (μ * av) * s ^ 2 := by ring
  calc
    C' ^ 2 * (μ * av) * s ^ 2 = (s * C' * Real.sqrt (μ * av)) ^ 2 := hcalc.symm
    _ ≤ (Real.sqrt ε_T) ^ 2 := hsq
    _ = ε_T := Real.sq_sqrt hεT

/-- **eq:appgapestimate replay at the corpus small-box scale (CLOSED)**:
from the FS regime `s·C′·√(μ·(av)) ≤ √ε_T` and the ε_T-cap
`36·Cgap·ε_T ≤ C′²` (so that the corpus kinetic gap constant `1/(36s²)`
dominates `Cgap·μ(av)`), the kinetic word absorbs the whole
excited-particle penalty

    Cgap·μ·(av)·n₊(Φ) ≤ kinWord N s Φ

— the corpus form of FS `Σ_i ½ε_T(1+π⁻²)⁻¹(dℓ)⁻²Q_{B,i} ≥
C′²(1+π⁻²)⁻¹μa·n₊` (thm:smallbox proof's absorption step), assembled from
`eT_regime_gap_bound` + `KineticBound.kinWord_ge_mu_a_cnPlus`. -/
lemma eT_gap_absorbs_onebody {N : ℕ} {s μ ε_T C' Cgap : ℝ} {v : ℝ³ → ℝ}
    (hs : 0 < s) (hμ : 0 < μ) (hAv : 0 ≤ a v) (hC' : 0 < C')
    (hCgap : 0 ≤ Cgap) (hεT : 0 ≤ ε_T)
    (hreg : s * C' * Real.sqrt (μ * (a v)) ≤ Real.sqrt ε_T)
    (hcap : 36 * Cgap * ε_T ≤ C' ^ 2)
    {Φ : X N → ℝ} (hΦc : ContDiff ℝ ∞ Φ) :
    Cgap * μ * (a v) * cnPlus s Φ ≤ kinWord N s Φ := by
  have h1 := eT_regime_gap_bound (ε_T := ε_T) (C' := C') (s := s) (μ := μ) (av := a v)
    hεT (le_of_lt hμ) hAv (le_of_lt hC') (le_of_lt hs) hreg
  -- Cgap·μ(av) ≤ 1/(36s²)
  have hle : 36 * Cgap * (C' ^ 2 * (μ * (a v)) * s ^ 2) ≤ 36 * Cgap * ε_T := by
    have c0 : 0 ≤ Cgap * 36 := mul_nonneg hCgap (by norm_num)
    have hm := mul_le_mul_of_nonneg_left h1 c0
    simpa [mul_assoc, mul_comm, mul_left_comm] using hm
  have hA : (Cgap * μ * (a v)) * (36 * s ^ 2) * C' ^ 2 ≤ C' ^ 2 := by
    calc
      (Cgap * μ * (a v)) * (36 * s ^ 2) * C' ^ 2 = 36 * Cgap * (C' ^ 2 * (μ * (a v)) * s ^ 2) := by ring
      _ ≤ 36 * Cgap * ε_T := hle
      _ ≤ C' ^ 2 := hcap
  have hposC'2 : 0 < C' ^ 2 := sq_pos_of_pos hC'
  have hB : (Cgap * μ * (a v)) * (36 * s ^ 2) ≤ 1 := by
    have hq : (Cgap * μ * (a v)) * (36 * s ^ 2) ≤ C' ^ 2 / C' ^ 2 := (le_div_iff₀ hposC'2).mpr hA
    simpa [div_self (ne_of_gt hposC'2)] using hq
  have hgap : Cgap * μ * (a v) ≤ 1 / (36 * s ^ 2) := by
    have hpos : 0 < 36 * s ^ 2 := by positivity
    exact (le_div_iff₀ hpos).mpr hB
  exact kinWord_ge_mu_a_cnPlus (N := N) (s := s) (μ := μ) hs (le_of_lt hμ)
    hAv (Cgap := Cgap) hCgap hgap (Φ := Φ) hΦc



/-! ## Section A.3 — per-mode coefficient lemmas (the Fock2Mode half-regime) -/

/-- the diagonal b-mode coefficient `𝒜 := d·[r−c]₊² + 2Ka` dominates its
`2Ka`-part, for `d, K, a ≥ 0`. -/
lemma mode_coeff_lower {d c r K a : ℝ} (hd : 0 ≤ d) (hK : 0 ≤ K) (ha : 0 ≤ a) :
    2 * K * a ≤ d * fsKinCoeff c r + 2 * K * a := by
  nlinarith [mul_nonneg hd (fsKinCoeff_nonneg c r)]

/-- positivity of the diagonal coefficient when `Ka > 0`:
`0 < d·[r−c]₊² + 2Ka`. -/
lemma mode_coeff_pos {d c r K a : ℝ} (hd : 0 ≤ d) (hKa : 0 < K * a) :
    0 < d * fsKinCoeff c r + 2 * K * a := by
  nlinarith [mul_nonneg hd (fsKinCoeff_nonneg c r), hKa]

/-- **the per-mode half-regime** (lm:appbogolubov's `|ℬ|/𝒜 ≤ 1/2`): with the
diagonal coefficient `𝒜 := d·[r−c]₊² + 2Ka` and the scattering bound
`|B(p)| ≤ Ka`, one has `|B(p)| ≤ 𝒜/2`. -/
lemma mode_half_regime {d c r K a : ℝ} {Bp : ℝ} (hd : 0 ≤ d) (hK : 0 ≤ K)
    (ha : 0 ≤ a) (hB : |Bp| ≤ K * a) :
    |Bp| ≤ (d * fsKinCoeff c r + 2 * K * a) / 2 := by
  have hge : 2 * K * a ≤ d * fsKinCoeff c r + 2 * K * a := mode_coeff_lower hd hK ha
  calc
    |Bp| ≤ K * a := hB
    _ ≤ (d * fsKinCoeff c r + 2 * K * a) / 2 := by
        have hpos : (0 : ℝ) < 2 := by norm_num
        rw [le_div_iff₀ hpos]
        nlinarith [fsKinCoeff_nonneg c r, mul_nonneg hK ha]

/-! ## Section A.4 — the lm:appbogolubov momentum-ball volume estimate
(over the corpus `EuclideanSpace ℝ (Fin 3)` conventions; `RadialIntegral`) -/

/-- **`∫_{‖p‖ < R} 1 dp = (4π/3)·R³`** — the real-integral form of the
lm:appbogolubov volume estimate `∫_{|p|<2c} 1 dp ≤ C·(dsℓ)⁻³` (take
`R := 2c`, `c := (dsℓ)⁻¹`): from `integral_const` on the restricted measure
(`Measure.real_apply`) + `volume_ball_open_r3` + `toReal_ofReal`. -/
lemma momentum_ball_integral_one (R : ℝ) (hR : 0 ≤ R) :
    (∫ p : ℝ³ in Metric.ball (0 : ℝ³) R, (1 : ℝ)) = (4 / 3 : ℝ) * Real.pi * R ^ 3 := by
  have hI : (∫ p : ℝ³ in Metric.ball (0 : ℝ³) R, (1 : ℝ))
      = (volume (Metric.ball (0 : ℝ³) R)).toReal := by
    have hc := MeasureTheory.integral_const (μ := (volume : Measure ℝ³).restrict (Metric.ball (0 : ℝ³) R)) (c := (1 : ℝ))
    rw [hc]
    simp only [smul_eq_mul, mul_one, measureReal_def]
    congr 1
    rw [Measure.restrict_apply (s := Metric.ball (0 : ℝ³) R) (t := Set.univ) MeasurableSet.univ]
    simp
  rw [hI]
  rw [volume_ball_open_r3 R hR]
  have hnonneg : 0 ≤ (4 / 3 : ℝ) * Real.pi * R ^ 3 :=
    mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4 / 3) Real.pi_nonneg) (pow_nonneg hR 3)
  rw [ENNReal.toReal_ofReal hnonneg]



/-! ## Section C — the D1 definitional layer (multiplier symbol + targets) -/

/-- the inverse-square positive-part multiplier symbol of the weighted
excited kinetic in the MATHLIB-unitary convention (Session-228 pinning):
`m_c(r) := [2πr − c]₊⁻²` — the symbol of `[√−Δ − c]₊⁻²` at radial value
`r := ‖q‖` (√−Δ's symbol is `2π‖q‖` in the unitary convention). -/
noncomputable def fsInvCoeff (c r : ℝ) : ℝ :=
  ((max (2 * Real.pi * r - c) 0) ^ 2)⁻¹

/-- nonnegativity: `0 ≤ [2πr−c]₊⁻²`. -/
lemma fsInvCoeff_nonneg (c r : ℝ) : 0 ≤ fsInvCoeff c r := by
  dsimp [fsInvCoeff]
  positivity

/-- **D1 — per-particle multiplier-form nonnegativity (CLOSED)**: for a real
Schwartz slice `f` (the `χ_B·(Q_iΦ)`-orbital, lifted by
`HasCompactSupport.toSchwartzMap`), the weighted-excited kinetic
multiplier form `∫_q ‖𝓕f q‖²·[2π‖q‖−c]₊⁻²dq` (`𝓕 =
`SchwartzMap.fourierTransformCLM ℂ`, unitary convention, Session-228
pinning) is nonnegative — pointwise (`|𝓕f q|² ≥ 0`, `[2π‖q‖−c]₊⁻² ≥ 0`)
via the unconditional `integral_nonneg`.  The corpus `tBword(Φ)` is the
sum over particles of these forms on the slices. -/
lemma tBword_multForm_nonneg (c : ℝ) (f : SchwartzMap ℝ³ ℂ)
    (hreal : ∀ x : ℝ³, (f x).im = 0) :
    0 ≤ ∫ q : ℝ³, ‖(SchwartzMap.fourierTransformCLM ℂ f : ℝ³ → ℂ) q‖ ^ 2 * fsInvCoeff c ‖q‖ := by
  apply integral_nonneg
  intro q
  exact mul_nonneg (sq_nonneg _) (fsInvCoeff_nonneg c ‖q‖)


/-! ## Section C.2 — the box-DISCRETE weighted-kinetic coefficient layer
(Session-231 design: the continuum multiplier form `tBword_multForm_nonneg`
is SUPERSEDED — the full-space symbol `[2π‖q‖−c]₊⁻²` has a nonintegrable
threshold singularity; the weighted excited kinetic is the box-DISCRETE mode
sum over the normalised `boxNeumann3` modes, on which `√−Δ` acts by
`π‖k‖/s` (the Session-224 eigen-bridge)).  This section carries the
coefficient layer: `boxModeCoeff s c k := [π‖k‖/s − c]₊⁻²` with its
nonnegativity and the Newtonian tail bound; the FULL finiteness of
`tBmode(s,c,f) := Σ_k boxModeCoeff s c k · |c_k(f)|²` (Bessel + head/tail
split) is the next target (needs the L²(acube)-Bessel infra). -/


/-- the EUCLIDEAN norm of the mode index `k ∈ ℕ³`: `√(Σ_j (k j)²)` — the
box `√−Δ` eigenvalue on the product mode `k` is `π·boxModeNorm k / s`
(`boxNeumann_deriv_two` product eigen-bridge).  (NB: `‖fun j => (k j : ℝ)‖`
on the RAW Pi type would be the SUP norm — wrong eigenvalue; the explicit
sqrt-form is the Euclidean `‖k‖₂`.) -/
noncomputable def boxModeNorm (k : Fin 3 → ℕ) : ℝ :=
  Real.sqrt (∑ j : Fin 3, ((k j : ℝ) ^ 2))

lemma boxModeNorm_sq (k : Fin 3 → ℕ) : boxModeNorm k ^ 2 = ∑ j : Fin 3, (k j : ℝ) ^ 2 := by
  dsimp [boxModeNorm]
  rw [Real.sq_sqrt]
  exact Finset.sum_nonneg (fun j hj => sq_nonneg ((k j : ℝ)))

lemma boxModeNorm_nonneg (k : Fin 3 → ℕ) : 0 ≤ boxModeNorm k := by
  dsimp [boxModeNorm]
  exact Real.sqrt_nonneg _

lemma boxModeNorm_coord_le (k : Fin 3 → ℕ) (j : Fin 3) : (k j : ℝ) ≤ boxModeNorm k := by
  have hsq : (k j : ℝ) ^ 2 ≤ boxModeNorm k ^ 2 := by
    rw [boxModeNorm_sq]
    exact Finset.single_le_sum (fun j' hj' => sq_nonneg ((k j' : ℕ) : ℝ))
      (Finset.mem_univ j)
  have hk : 0 ≤ (k j : ℝ) := by positivity
  have habs : |(k j : ℝ)| ≤ |boxModeNorm k| := (sq_le_sq.mp hsq)
  rw [abs_of_nonneg hk, abs_of_nonneg (boxModeNorm_nonneg k)] at habs
  exact habs

noncomputable def boxModeCoeff (s c : ℝ) (k : Fin 3 → ℕ) : ℝ :=
  ((max (Real.pi * boxModeNorm k / s - c) 0) ^ 2)⁻¹

lemma boxModeCoeff_nonneg (s c : ℝ) (k : Fin 3 → ℕ) : 0 ≤ boxModeCoeff s c k := by
  dsimp [boxModeCoeff]
  positivity

/-- **tail bound**: on the high modes `2c·s ≤ π·‖k‖` the coefficient is at
most the Newtonian value: `[π‖k‖/s − c]₊⁻² ≤ 4s²/(π²‖k‖²)`. -/
lemma boxModeCoeff_tail_le {s c : ℝ} (hs : 0 < s) (hc : 0 ≤ c) (k : Fin 3 → ℕ)
    (hkn : 0 < boxModeNorm k) (hk : 2 * c * s ≤ Real.pi * boxModeNorm k) :
    boxModeCoeff s c k ≤ (4 * s ^ 2) / (Real.pi ^ 2 * boxModeNorm k ^ 2) := by
  let x : ℝ := Real.pi * boxModeNorm k / s
  have hxge : 2 * c ≤ x := by
    dsimp [x]
    exact (le_div_iff₀ hs).mpr hk   -- 2c ≤ π‖k‖/s ⟺ 2c·s ≤ π‖k‖ (hs>0)
  have hx : 0 < x := by
    dsimp [x]
    exact div_pos (mul_pos Real.pi_pos hkn) hs
  have hxc : 0 < x - c := by nlinarith
  have hhalf : x / 2 ≤ x - c := by nlinarith
  have hmax : max (x - c) 0 = x - c := max_eq_left (by nlinarith)
  have hx2 : 0 < x / 2 := by positivity
  -- inverse comparison
  have hinv : (x - c)⁻¹ ≤ (x / 2)⁻¹ := (inv_le_inv₀ hxc hx2).2 hhalf
  have hinv0 : 0 ≤ (x - c)⁻¹ := inv_nonneg.mpr (le_of_lt hxc)
  have hsq := pow_le_pow_left₀ hinv0 hinv 2
  -- algebra: LHS = (x−c)⁻¹^2 ; RHS target
  have hxne : x - c ≠ 0 := ne_of_gt hxc
  have hsqinv : ((x - c) ^ 2)⁻¹ = ((x - c)⁻¹) ^ 2 := by
    field_simp [hxne]
  have hLHS : boxModeCoeff s c k = ((x - c)⁻¹) ^ 2 := by
    dsimp [boxModeCoeff]
    have hxdef : Real.pi * boxModeNorm k / s - c = x - c := by rfl
    rw [hxdef]
    rw [hmax]
    rw [hsqinv]
  have hRHS : ((x / 2)⁻¹) ^ 2 = (4 * s ^ 2) / (Real.pi ^ 2 * boxModeNorm k ^ 2) := by
    -- (x/2)⁻¹ = 2/x = 2s/(π‖k‖); square
    have hkne : boxModeNorm k ≠ 0 := ne_of_gt hkn
    have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
    dsimp [x]
    field_simp [hs.ne', hkne, hpi]
    ring
  calc
    boxModeCoeff s c k = ((x - c)⁻¹) ^ 2 := hLHS
    _ ≤ ((x / 2)⁻¹) ^ 2 := hsq
    _ = (4 * s ^ 2) / (Real.pi ^ 2 * boxModeNorm k ^ 2) := hRHS

/-! ## Section C.3 — the D1 per-mode diagonal comparison (Session-260 part 4):
fsKinCoeff bridges the box-discrete weight, and the per-mode Bogoliubov
error weight is bounded by the inverse-square weight.

The D1-body (Session-224/232 notes) reduces FS lm:appbogolubov's per-mode
algebra to: (i) the diagonal Bogoliubov coefficient
`𝒜(p) = (|B|/(n+1))·[|p|−c]₊² + 2K_sa` (corpus `d·fsKinCoeff c r + 2Ka`,
`d := s³/(N̂+1)`, `r := π‖k‖/s`), (ii) the cross bound `|ℬ(p)| ≤ C₀a`, and
(iii) the mode content.  This section commits the two pure-algebra bridges
of (i)+(ii):

  * `boxModeCoeff_eq_fsKinCoeff_inv` — `boxModeCoeff s c k =
    (fsKinCoeff c (π·boxModeNorm k/s))⁻¹` (the box-discrete weight
    `[π‖k‖/s − c]₊⁻²` IS the inverse of the diagonal coefficient's
    `[r−c]₊²`-symbol; `rfl` — both sides are `(max(·)²)⁻¹`);
  * `mode_error_weight_le` — FS's `|p| > c` reduction
    `B²/𝒜 ≤ (1/d)·(Ka)²/fsKinCoeff c r` from `𝒜 ≥ d·[r−c]₊²` (drop the
    `2Ka`-part) and `|B| ≤ Ka` — the real-algebra leaf whose mode sum over
    `k` (with `boxModeCoeff_eq_fsKinCoeff_inv`) turns per-mode Fock2Mode
    errors into `tBmode`-weighted content (`≤ C(s,c)·cnPlus`, closed in
    SmallBoxTBword).
-/

/-- the box-mode weight is the inverse-square `fsKinCoeff` at the mode
eigenvalue: `boxModeCoeff s c k = (fsKinCoeff c (π·boxModeNorm k/s))⁻¹`. -/
lemma boxModeCoeff_eq_fsKinCoeff_inv (s c : ℝ) (k : Fin 3 → ℕ) :
    boxModeCoeff s c k = (fsKinCoeff c (Real.pi * boxModeNorm k / s))⁻¹ := by
  rfl

/-- `[r−c]₊²` is positive above threshold. -/
lemma fsKinCoeff_pos_of_lt {c r : ℝ} (hc : 0 ≤ c) (hr : c < r) :
    0 < fsKinCoeff c r := by
  rw [fsKinCoeff_of_lt hc hr]
  have hr' : 0 < r - c := by linarith
  exact sq_pos_of_pos hr'

/-- **per-mode Bogoliubov error weight bound** (FS lm:appbogolubov, the
`|p| > 2(dsℓ)⁻¹` reduction): with the diagonal coefficient
`𝒜 := d·[r−c]₊² + 2Ka` (`d := |B|/(n+1)`, `r := |p|`) and the cross bound
`|B| ≤ Ka`, for `r > c`:

    B² / (d·[r−c]₊² + 2Ka) ≤ (1/d)·(Ka)²/[r−c]₊²  =  (1/d)·(Ka)²·boxModeCoeff-form.

The mode-summed version (over the box modes `k` with the per-particle rest
integrals of `‖⟨ê_k, slice⟩‖²`) converts this into `(N̂+1)/s³·(Ka)²`-scaled
`tBword`-content, bounded by `C(s,c)·cnPlus` via
`SmallBoxTBword.tBword_le`. -/
lemma mode_error_weight_le {d c r B K a : ℝ} (hd : 0 < d) (hc : 0 ≤ c) (hr : c < r)
    (hK : 0 ≤ K) (ha : 0 ≤ a) (hB : |B| ≤ K * a) :
    B ^ 2 / (d * fsKinCoeff c r + 2 * K * a) ≤ (1 / d) * (K * a) ^ 2 / fsKinCoeff c r := by
  have hfs : 0 < fsKinCoeff c r := fsKinCoeff_pos_of_lt hc hr
  have hdf : 0 < d * fsKinCoeff c r := mul_pos hd hfs
  have hn : 0 ≤ 2 * K * a := by positivity
  have hA : 0 < d * fsKinCoeff c r + 2 * K * a := by positivity
  have hAfirst : d * fsKinCoeff c r ≤ d * fsKinCoeff c r + 2 * K * a := by nlinarith
  have hinv : (d * fsKinCoeff c r + 2 * K * a)⁻¹ ≤ (d * fsKinCoeff c r)⁻¹ :=
    (inv_le_inv₀ hA hdf).2 hAfirst
  have hB2 : 0 ≤ B ^ 2 := sq_nonneg B
  have h1 : B ^ 2 / (d * fsKinCoeff c r + 2 * K * a) ≤ B ^ 2 / (d * fsKinCoeff c r) := by
    rw [div_eq_mul_inv, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_left hinv hB2
  have hB2le : B ^ 2 ≤ (K * a) ^ 2 := by
    have hKa : |B| ^ 2 ≤ (K * a) ^ 2 := by
      exact pow_le_pow_left₀ (abs_nonneg B) hB 2
    calc
      B ^ 2 = |B| ^ 2 := by rw [sq_abs]
      _ ≤ (K * a) ^ 2 := hKa
  have h2 : B ^ 2 / (d * fsKinCoeff c r) ≤ (1 / d) * (K * a) ^ 2 / fsKinCoeff c r := by
    calc
      B ^ 2 / (d * fsKinCoeff c r) ≤ (K * a) ^ 2 / (d * fsKinCoeff c r) := by
            exact div_le_div_of_nonneg_right hB2le (le_of_lt hdf)
      _ = (1 / d) * (K * a) ^ 2 / fsKinCoeff c r := by
            field_simp [ne_of_gt hfs, ne_of_gt hd]
  exact le_trans h1 h2

end BoseGases
end Submission
