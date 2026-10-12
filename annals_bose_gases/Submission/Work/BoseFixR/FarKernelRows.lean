import ChallengeDeps
import Mathlib.Tactic.Have
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Real.Pi.Bounds
import Submission.Work.BoseB7AK.W1rows.W1hat_abs_le
import Submission.Work.BoseBoxFock.sum_hatChi_sq_le
import Submission.Work.BoseFixR.RB5FSFixAux
import Submission.Work.BoseGateFS.ChiPin
import Submission.Work.BoseK15.ChiReg_corpus
import Submission.Work.BoseK15.sum_inv_one_add_norm_le
import Submission.Work.BoseK15.sum_inv_one_add_norm_tail_const
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission/Work/BoseFixR/FarKernelRows.lean` — the five `K₀`-free kernel rows of the far leg

## ⚠ FINDING: row 4 of the requested bundle is **not provable as stated**; the other four rows are

The requested bundle `Work.BoseFixR.FarKernelRows` (restated verbatim at the bottom of this file,
marked `SKELETON`) conjoins five rows of the honest box model `Work.BoseBoxFock.HonestBoxFam`,
consumed by the far-leg residual (`Submission/Work/BoseFixR/FarResid.lean`):

1. `∀ k, |E.W1 k| ≤ 16π a` — **proved** (`farRow_W1`: `Work.BoseB7AK.W1rows.W1hat_abs_le` and
   `|uvCut| ≤ 1`);
2. `∀ k, |E.W1omega k| ≤ 16π a` — **proved** (`farRow_W1omega`, via `w1omegaFun_rows`: FS's
   `0 ≤ ∫W₁ω ≤ Ca` for the *current* kernel `W₁ω = wScaled ℓ (g₀ω)`);
3. `∑_{k≠0} χ̂(k)² ≤ 10^100` — **proved** (`farRow_hatChi`: the pin
   `E.hatChi k = corpusBox.hatChi (vec (labVec N k))` plus the Bessel bound
   `Work.BoseBoxFock.sum_hatChi_sq_le`, `∑_{k} χ̂(k)² ≤ 1`);
4. `∑_{k≠0} |χ̂²(k)| ≤ 10^100` — **NOT PROVABLE as stated** (see below);
5. `#{s ≠ 0 : f_L(s) ≠ 0} ≤ 10^6 (ℓ K_L √(μa) + 1)³` — **proved** (`farRow_count`: `f_L`'s
   support plus `Work.BoseK15.card_le_of_vec_norm_le`).

### Why row 4 fails, and what is true instead

Row 4 is an **ℓ¹** bound on the Fourier coefficients of `χ²`, uniform in the mode number `N`
(`Lab N = Fin 3 → ZMod (2N+1)`; no hypothesis bounds `N`: `Work.BoseBoxFock.HonestModes` leaves `N`
free and `exists_honestModes` realises every `N`).  As `|χ̂²(k)| ≤ 1`, a uniform bound can only come
from the *decay* of `χ̂²`, i.e. from the smoothness of the corpus bump
`χ = Submission.BoseGases.chi = chiBase / √chiNormSq` — and `chiBase` is **opaque**:

    chiBase x = (someContDiffBumpBase ℝ³).toFun 2 (4 • x),   someContDiffBumpBase = Classical.choice,

with `Classical.choice` carrying *no specification* (`Classical.choice ⟨X⟩ = X` is not provable; cf.
`Submission/Work/SmallBoxOneBody/chiNormSq_ge_pi_div_48.lean`, and `Submission/Work/ChiSmall.lean`'s
header: "The generic smooth `ContDiffBump`-based corpus `chi` cannot supply this decay (its Mathlib
interface has no boundary control)").

What *is* available is `Work.BoseK15.ChiReg_corpus s : ∃ C, 0 ≤ C ∧ ChiReg corpusBox s C` (FS
`lem:DecaychiHat`, proved from the qualitative smoothness of `χ` through the Schwartz decay of
`𝓕(χ²)`) — but its constant is *existential*, and its value is read off the Schwartz seminorms of
`𝓕(χ²)`, hence (Fourier transform of a derivative) is controlled by the `L¹` norms of the
*derivatives* of `χ²` — quantities on which the `ContDiffBumpBase` fields put **no numeric bound**
(the corpus's own interface records the companion *sum* row `∑_{s≠0}|hatChiSq s| ≤ K₀` as an
*assumed field* of `K15Input`/`Q3Kernel'`, and `Submission/Work/ChiSmall.lean`'s header records that
the generic `ContDiffBump` χ "cannot supply this decay", which is why the corpus built a *separate*
explicit bump there).  Admissible interpretations of
`Classical.choice` therefore include bases whose induced bump oscillates smoothly (values in
`[0,1]`, `= 1` on `‖x‖ ≤ 1/4`, supported in `‖x‖ ≤ 1/2`) with arbitrarily large derivative
seminorms and ℓ¹ lattice sum `≈ log M > 10^100` — the same "the choice axiom is unconstrained, so no
proof can exist" argument as `Work.SmallBoxOneBody.not_forced_six_le_chiNormSq`.  So no *numeric*
bound `≤ 10^100` is provable, while these *qualitative* rows are (all sorry-free below):

* `latticeWeightSumLe` — the lattice-weight sum is numerically bounded: for `3 ≤ 2s` and every
  finite `S ⊆ ℤ³`, `∑_{n∈S} (1 + ‖2πn‖²)^{-s} ≤ 10^3` (from
  `Work.BoseK15.sum_inv_one_add_norm_tail_const`); the numerical lattice factor of row 4 is thus
  available, and the *only* unpinned factor is the decay constant;
* `sumHatChiSqLeOfChiReg (hs) (hchi : ChiReg corpusBox s C) : ∑_{k≠0}|χ̂²(k)| ≤ C · 10^3`;
* `sumHatChiSqLe` — the same with an arbitrary lattice-weight bound `Csum`;
* `farRow_hatChiSq : ∃ C, 0 ≤ C ∧ ∑_{k≠0}|χ̂²(k)| ≤ C` (`ChiReg_corpus` plus
  `Work.BoseK15.sum_inv_one_add_norm_le`);
* `farRow_hatChiSq_of_numeric_decay` — the numeric row 4 holds as soon as the decay constant is
  *numerically* bounded: `ChiReg corpusBox s C` with `C * 10^3 ≤ 10^100`.  This pins the exact gap
  (a numeric bound on the Schwartz/derivative seminorms of `χ²`, hence on `C`) to `10^97`;
* `farKernelRowsRepaired` — the requested bundle with row 4's `10^100` replaced by an existential
  constant: **the five rows in the form in which they are true**, and the form its consumer can use
  (the far-leg error budget admits arbitrary absolute constants; `HANDOFF.md`: "any O(1) error
  constant is FREE for `theorem_1_2`").

**Suggested repair of the far-leg interface** (either is immediately usable):
(i) replace the `10^100` of row 4 by an existential constant — or by the decay constant `Cchi` taken
from the interface, exactly what `Work.BoseK15.K15Input.sum_hatChiSq` /
`Q3Kernel'.sum_hatChiSq` do (`∑_{s≠0}|hatChiSq s| ≤ K₀`) — and consume `farKernelRowsRepaired`
below;
(ii) make the corpus bump explicit (`Work.SmallBoxOneBody.chiBaseConc`, i.e.
`Real.smoothTransition (2 - 4‖x‖)`), whose derivative seminorms *are* numerically bounded, after
which row 4 becomes provable by the route of the original `RB5FSKern` docstring.
-/

noncomputable section

open scoped Real Topology BigOperators

open MeasureTheory Filter Metric

namespace Work.BoseFixR

open _root_.BoseGases Submission.BoseGases Work.UBB Work.BoseBox
open Work.BoseBoxFix Work.BoseBoxFock

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

/-! ## 1. Elementary pieces and the pins at the honest family -/

/-- The UV cut-off is in `[0,1]`: `uvCut fu Λ k = f_u(‖k‖/Λ)`. -/
lemma abs_uvCut_le_one (fu : LowCut) (Λ : ℝ) (k : EuclideanSpace ℝ (Fin 3)) :
    |uvCut fu Λ k| ≤ 1 := by
  rw [uvCut, abs_le]
  exact ⟨by linarith [fu.nonneg (‖k‖ / Λ)], fu.le_one (‖k‖ / Λ)⟩

/-- `ℓ = sideAt μ (a v)` is positive in the dilute regime `R ≤ ℓ·chiR0` with `R > 0`. -/
lemma ell_pos_of_le {v : EuclideanSpace ℝ (Fin 3) → ℝ} {R μ : ℝ} (hR : 0 < R)
    (hRℓ : R ≤ ell v μ * Submission.BoseGases.chiR0) : 0 < ell v μ :=
  pos_of_mul_pos_left (lt_of_lt_of_le hR hRℓ) (le_of_lt Submission.BoseGases.chiR0_pos)

/-- `labVec N : Lab N → (Fin 3 → ℤ)` is injective (`ZMod.valMinAbs_inj`). -/
lemma labVec_injective (N : ℕ) : Function.Injective (labVec N) := by
  intro s t hst
  funext i
  exact ZMod.valMinAbs_inj.mp (congrArg (fun f : Fin 3 → ℤ => f i) hst)

/-- At the honest family, `ellH v μ` is `ell v μ` (both are `sideAt μ (a v)`, positive in the
dilute regime). -/
lemma honest_ellH_eq {v : EuclideanSpace ℝ (Fin 3) → ℝ} {μ : ℝ} (hℓ : 0 < ell v μ) :
    ellH v μ = ell v μ := by
  rw [ellH]
  exact if_pos (by rw [← ell_eq]; exact hℓ)

/-- The mode momentum of the honest family is the dual-lattice label of `s` divided by `ℓ`:
`kmom s = ℓ⁻¹ • vec (labVec N s)`. -/
lemma honest_kmom_eq {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v)
    (fc fu : LowCut) (HM : ∀ μ : ℝ, HonestModes v μ) {μ : ℝ} (hℓ : 0 < ell v μ)
    (s : Lab (HM μ).N) :
    kmomLab (ellH v μ) (HM μ).N s
      = (ell v μ)⁻¹ • Work.BoseB4.vec (labVec (HM μ).N s) := by
  rw [kmomLab, honest_ellH_eq (v := v) (μ := μ) hℓ]

/-- `chiFun ℓ = chiScale ℓ` is integrable for `0 < ℓ`. -/
lemma chiFun_integrable (ℓ : ℝ) (hℓ : 0 < ℓ) : Integrable (chiFun ℓ) :=
  (Submission.BoseGases.chiScale_continuous ℓ).integrable_of_hasCompactSupport
    (Submission.BoseGases.chiScale_hasCompactSupport (ne_of_gt hℓ))

/-- **The Fourier scaling identity** `Ŵ_ℓ(k) = ℓ³ χ̂(ℓk)` (`ChatChiFunEq` of
`Submission/Work/BoseFixR/ModeCountBoundV2.lean`, ported here so that this module's import cone
avoids the (currently non-compiling) `W1omega0_rows`). -/
lemma chatChiFunEq (ℓ : ℝ) (hℓ : 0 < ℓ) (k : EuclideanSpace ℝ (Fin 3)) :
    chat (chiFun ℓ) k = ℓ ^ 3 * Work.BoseK15.corpusBox.hatChi (ℓ • k) := by
  rw [Work.BoseB7AK.W1low.chat_eq_integral_cos (chiFun_integrable ℓ hℓ) k]
  exact Work.BoseB4.BoxData.integral_chiLam_mul_cos Work.BoseK15.corpusBox hℓ k

/-- **The `χ̂` pin at the honest family**: `E.hatChi s` is the corpus `χ̂` at the lattice label
`vec (labVec N s)`. -/
lemma honest_hatChi_eq {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v)
    (fc fu : LowCut) (HM : ∀ μ : ℝ, HonestModes v μ) {μ : ℝ} (hℓ : 0 < ell v μ)
    (s : Lab (HM μ).N) :
    (HonestBoxFam v h fc fu HM μ).E.hatChi s
      = Work.BoseK15.corpusBox.hatChi (Work.BoseB4.vec (labVec (HM μ).N s)) := by
  have hdef : (HonestBoxFam v h fc fu HM μ).E.hatChi s
      = chat (chiFun (ell v μ)) (kmomLab (ellH v μ) (HM μ).N s)
        / chat (fun z => chiFun (ell v μ) z ^ 2) 0 := rfl
  rw [hdef, honest_kmom_eq h fc fu HM hℓ s, chatChiFunEq (ell v μ) hℓ, smul_smul,
    mul_inv_cancel₀ (ne_of_gt hℓ), one_smul, chat_chiSq_zero hℓ,
    mul_div_cancel_left₀ _ (pow_ne_zero 3 (ne_of_gt hℓ))]

/-- **The `χ̂²` pin at the honest family**: `E.hatChiSq s` is the corpus `χ̂²` at the lattice label
`vec (labVec N s)`. -/
lemma honest_hatChiSq_eq {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v)
    (fc fu : LowCut) (HM : ∀ μ : ℝ, HonestModes v μ) {μ : ℝ} (hℓ : 0 < ell v μ)
    (s : Lab (HM μ).N) :
    (HonestBoxFam v h fc fu HM μ).E.hatChiSq s
      = Work.BoseK15.corpusBox.hatChiSq (Work.BoseB4.vec (labVec (HM μ).N s)) := by
  have hdef : (HonestBoxFam v h fc fu HM μ).E.hatChiSq s
      = chat (fun z => chiFun (ell v μ) z ^ 2) (kmomLab (ellH v μ) (HM μ).N s)
        / chat (fun z => chiFun (ell v μ) z ^ 2) 0 := rfl
  rw [hdef, honest_kmom_eq h fc fu HM hℓ s, Work.BoseGateFS.chat_chiFun_sq_eq (ell v μ) hℓ,
    smul_smul, mul_inv_cancel₀ (ne_of_gt hℓ), one_smul, chat_chiSq_zero hℓ,
    mul_div_cancel_left₀ _ (pow_ne_zero 3 (ne_of_gt hℓ))]

/-- The sum of `1` over a filtered finset is its cardinality. -/
lemma sum_one_filter_eq_card {α : Type*} [DecidableEq α] (T : Finset α) (p : α → Prop)
    [DecidablePred p] :
    (∑ s ∈ T.filter p, (1 : ℝ)) = ((T.filter p).card : ℝ) := by
  rw [Finset.sum_const, nsmul_eq_mul, mul_one]

/-- **The dual-lattice count.**  A finite set of labels whose momenta `vec (labVec N s)` all lie in
the ball of radius `ρ` has at most `(ρ/π + 1)³` elements
(`Work.BoseK15.card_le_of_vec_norm_le` through the injection `labVec N`). -/
lemma card_le_of_vec_lab {N : ℕ} (S : Finset (Lab N)) (ρ : ℝ) (hρ : 0 ≤ ρ)
    (hS : ∀ s ∈ S, ‖Work.BoseB4.vec (labVec N s)‖ ≤ ρ) :
    (S.card : ℝ) ≤ (ρ / Real.pi + 1) ^ 3 := by
  have hcard : ((S.image (labVec N)).card : ℝ) = (S.card : ℝ) := by
    rw [Finset.card_image_of_injective S (labVec_injective N)]
  rw [← hcard]
  exact Work.BoseK15.card_le_of_vec_norm_le (S.image (labVec N)) ρ hρ (fun n hn => by
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hn
    exact hS s hs)

/-- The corpus `χ̂` at the lattice labels is the cosine integral (definitionally). -/
lemma corpusBox_hatChi_apply (n : Fin 3 → ℤ) :
    Work.BoseK15.corpusBox.hatChi (Work.BoseB4.vec n)
      = ∫ x : EuclideanSpace ℝ (Fin 3), Submission.BoseGases.chi x *
          Real.cos (inner ℝ (Work.BoseB4.vec n) x) := rfl

/-- The corpus `χ̂²` at the lattice labels is the cosine integral (definitionally). -/
lemma corpusBox_hatChiSq_apply (n : Fin 3 → ℤ) :
    Work.BoseK15.corpusBox.hatChiSq (Work.BoseB4.vec n)
      = ∫ x : EuclideanSpace ℝ (Fin 3), (Submission.BoseGases.chi x) ^ 2 *
          Real.cos (inner ℝ (Work.BoseB4.vec n) x) := rfl

/-! ## 2. Row 2's real-space core: `∫ |W₁ω| ≤ 16π a v`

`W₁ω = wScaled ℓ (g₀ω)` is the *current* corpus kernel (`Work.BoseFixR.Defs`; the earlier
`g₀(1-ω)` numerator made `W1omega0_rows` non-compiling and would make the mass cancellation
`ĝω(0) = ∫W₁ω`, on which FS §9's `prop:FarAway` rests, fail). -/

/-- The numerator of the `W₁ω` kernel: `g₀ω = v(1-ω)ω`. -/
def w1omegaNum (v : EuclideanSpace ℝ (Fin 3) → ℝ) (h : ScatSol v) :
    EuclideanSpace ℝ (Fin 3) → ℝ :=
  fun z => g0 v h z * Classical.choose h z

lemma w1omegaFun_eq (v : EuclideanSpace ℝ (Fin 3) → ℝ) (h : ScatSol v) (ℓ : ℝ) :
    W1omegaFun v h ℓ = wScaled ℓ (w1omegaNum v h) := rfl

lemma w1omegaNum_eq (v : EuclideanSpace ℝ (Fin 3) → ℝ) (h : ScatSol v)
    (z : EuclideanSpace ℝ (Fin 3)) :
    w1omegaNum v h z = v z * (1 - Classical.choose h z) * Classical.choose h z := by
  simp only [w1omegaNum, Submission.BoseGases.g0]

lemma w1omegaNum_integrable {v : EuclideanSpace ℝ (Fin 3) → ℝ} {R : ℝ} (hR : 0 < R)
    (hvnn : 0 ≤ v) (hvrad : _root_.BoseGases.IsRadial v) (hv_supp : tsupport v ⊆ Metric.ball 0 R)
    (h : ScatSol v) : Integrable (w1omegaNum v h) :=
  Submission.BoseGases.g0w0_integrable (v := v) (R := R) hR hvnn hvrad hv_supp h

/-- `∫ |g₀ω| = ∫ g₀ω ≤ 8π a v` (`g₀ω ≥ 0` a.e.). -/
lemma w1omegaNum_abs_integral_le {v : EuclideanSpace ℝ (Fin 3) → ℝ} {R : ℝ} (hR : 0 < R)
    (hvnn : 0 ≤ v) (hvrad : _root_.BoseGases.IsRadial v) (hv_supp : tsupport v ⊆ Metric.ball 0 R)
    (h : ScatSol v) :
    (∫ z, |w1omegaNum v h z|) ≤ 8 * Real.pi * a v := by
  obtain ⟨hrad, hw⟩ := Classical.choose_spec h
  have hae := Submission.BoseGases.scat_gomega_ae_bounds (v := v) (w := Classical.choose h)
    (R := R) hR hvnn hvrad hv_supp hrad hw
  have hob : (∫ z, |w1omegaNum v h z|) = ∫ z, w1omegaNum v h z := by
    refine integral_congr_ae ?_
    filter_upwards [hae.1] with z hz
    rw [w1omegaNum_eq, abs_of_nonneg]
    exact hz
  rw [hob]
  have h2 : (∫ z, w1omegaNum v h z)
      = ∫ z, v z * (1 - Classical.choose h z) * Classical.choose h z :=
    integral_congr_ae (Eventually.of_forall (fun z => w1omegaNum_eq v h z))
  rw [h2]
  exact (Submission.BoseGases.chosen_gomega_integral_bounds (v := v) (R := R) hR hvnn hvrad
    hv_supp h).2

/-- **FS's `0 ≤ ∫W₁ω ≤ Ca` row** (`∫ |W₁ω| ≤ 16π a v`) in the dilute regime, together with the
integrability of the kernel: the `chat`-form of the row used by the far leg follows from
`|chat W k| ≤ ∫|W|` (`Work.BoseB7AK.W1rows.abs_chat_le_integral_abs`). -/
theorem w1omegaFun_rows {v : EuclideanSpace ℝ (Fin 3) → ℝ} {R ℓ : ℝ} (hR : 0 < R) (hℓ : 0 < ℓ)
    (hvnn : 0 ≤ v) (hvrad : _root_.BoseGases.IsRadial v) (hv_supp : tsupport v ⊆ Metric.ball 0 R)
    (h : ScatSol v) (hRℓ : R ≤ ℓ * Submission.BoseGases.chiR0) :
    Integrable (W1omegaFun v h ℓ) ∧ (∫ z, |W1omegaFun v h ℓ z|) ≤ 16 * Real.pi * a v := by
  have hnum : Integrable (w1omegaNum v h) := w1omegaNum_integrable hR hvnn hvrad hv_supp h
  have hsupp : ∀ z, R ≤ ‖z‖ → w1omegaNum v h z = 0 := fun z hz => by
    rw [w1omegaNum_eq, Submission.BoseGases.v_eq_zero_of_norm_ge hv_supp hz]
    ring
  have hint : Integrable (wScaled ℓ (w1omegaNum v h)) :=
    Submission.BoseGases.wScaled_integrable_ae hℓ hR.le hRℓ hnum hsupp
  constructor
  · rwa [w1omegaFun_eq]
  · rw [w1omegaFun_eq]
    have hdom : ∀ᵐ z ∂(volume : Measure ℝ³),
        |wScaled ℓ (w1omegaNum v h) z| ≤ 2 * |w1omegaNum v h z| :=
      Eventually.of_forall (fun z =>
        Submission.BoseGases.wScaled_abs_le_two hℓ hR.le hRℓ hsupp z)
    have hInt2 : Integrable (fun z => 2 * |w1omegaNum v h z|) := hnum.abs.const_mul 2
    calc (∫ z, |wScaled ℓ (w1omegaNum v h) z|)
        ≤ ∫ z, 2 * |w1omegaNum v h z| := integral_mono_ae hint.abs hInt2 hdom
      _ = 2 * (∫ z, |w1omegaNum v h z|) := by rw [integral_const_mul]
      _ ≤ 2 * (8 * Real.pi * a v) := by
          linarith [w1omegaNum_abs_integral_le hR hvnn hvrad hv_supp h]
      _ = 16 * Real.pi * a v := by ring

/-! ## 3. Rows 1, 2, 3 and 5 at the honest family -/

/-- **Row 1** (`|Ŵ₁| ≤ 16π a v`): the UV cut-off is bounded by `1` and
`Work.BoseB7AK.W1rows.W1hat_abs_le` bounds the kernel
(`E.W1 = uvCut fu (uvRad ℓ N) (kmom k) · chat (W1fun …) (kmom k)`, definitionally). -/
theorem farRow_W1 {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v)
    (hv : 0 ≤ v) (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ Metric.ball 0 R)
    (hav : 0 < a v) (fc fu : LowCut) (HM : ∀ μ : ℝ, HonestModes v μ) {μ : ℝ}
    (hRℓ : R ≤ ell v μ * Submission.BoseGases.chiR0) :
    ∀ k : Lab (HM μ).N,
      |(HonestBoxFam v h fc fu HM μ).E.W1 k| ≤ 16 * Real.pi * a v := by
  have hℓ : 0 < ell v μ := ell_pos_of_le hR hRℓ
  have hvnn : ∀ x : EuclideanSpace ℝ (Fin 3), 0 ≤ v x := fun x => hv x
  intro k
  have h1 : (HonestBoxFam v h fc fu HM μ).E.W1 k
      = uvCut fu (uvRad (sideAt μ (a v)) (HM μ).N) (kmomLab (ellH v μ) (HM μ).N k)
        * chat (W1fun v h (sideAt μ (a v))) (kmomLab (ellH v μ) (HM μ).N k) := rfl
  rw [h1, abs_mul]
  have h2 := Work.BoseB7AK.W1rows.W1hat_abs_le (v := v) (R := R) (ℓ := sideAt μ (a v))
    hR (by rw [← ell_eq]; exact hℓ) hvnn hvrad hv_supp h (by rw [← ell_eq]; exact hRℓ)
    (kmomLab (ellH v μ) (HM μ).N k)
  calc |uvCut fu (uvRad (sideAt μ (a v)) (HM μ).N) (kmomLab (ellH v μ) (HM μ).N k)|
          * |chat (W1fun v h (sideAt μ (a v))) (kmomLab (ellH v μ) (HM μ).N k)|
      ≤ 1 * |chat (W1fun v h (sideAt μ (a v))) (kmomLab (ellH v μ) (HM μ).N k)| :=
        mul_le_mul_of_nonneg_right (abs_uvCut_le_one _ _ _) (abs_nonneg _)
    _ = |chat (W1fun v h (sideAt μ (a v))) (kmomLab (ellH v μ) (HM μ).N k)| := one_mul _
    _ ≤ 16 * Real.pi * a v := h2

/-- **Row 2** (`|Ŵ₁ω| ≤ 16π a v`): `|chat W k| ≤ ∫|W|` and `w1omegaFun_rows`. -/
theorem farRow_W1omega {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v)
    (hv : 0 ≤ v) (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ Metric.ball 0 R)
    (hav : 0 < a v) (fc fu : LowCut) (HM : ∀ μ : ℝ, HonestModes v μ) {μ : ℝ}
    (hRℓ : R ≤ ell v μ * Submission.BoseGases.chiR0) :
    ∀ k : Lab (HM μ).N,
      |(HonestBoxFam v h fc fu HM μ).E.W1omega k| ≤ 16 * Real.pi * a v := by
  have hℓ : 0 < ell v μ := ell_pos_of_le hR hRℓ
  have hvnn : ∀ x : EuclideanSpace ℝ (Fin 3), 0 ≤ v x := fun x => hv x
  intro k
  have h1 : (HonestBoxFam v h fc fu HM μ).E.W1omega k
      = chat (W1omegaFun v h (sideAt μ (a v))) (kmomLab (ellH v μ) (HM μ).N k) := rfl
  rw [h1]
  have hrows := w1omegaFun_rows (v := v) (R := R) (ℓ := sideAt μ (a v)) hR
    (by rw [← ell_eq]; exact hℓ) hvnn hvrad hv_supp h (by rw [← ell_eq]; exact hRℓ)
  calc |chat (W1omegaFun v h (sideAt μ (a v))) (kmomLab (ellH v μ) (HM μ).N k)|
      ≤ ∫ z, |W1omegaFun v h (sideAt μ (a v)) z| :=
        Work.BoseB7AK.W1rows.abs_chat_le_integral_abs _
    _ ≤ 16 * Real.pi * a v := hrows.2

/-- **Row 3** (`∑_{k≠0} χ̂(k)² ≤ 10^100`): the pin `honest_hatChi_eq` turns the sum into the
Bessel sum `∑_{k} χ̂(k)² ≤ 1` of `Work.BoseBoxFock.sum_hatChi_sq_le`, the excited modes being a
sub-finset of the label cube. -/
theorem farRow_hatChi {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v)
    (fc fu : LowCut) (HM : ∀ μ : ℝ, HonestModes v μ) {μ R : ℝ} (hR : 0 < R)
    (hRℓ : R ≤ ell v μ * Submission.BoseGases.chiR0) :
    (∑ k ∈ Work.BoseB7.excited (Lab (HM μ).N),
        ((HonestBoxFam v h fc fu HM μ).E.hatChi k) ^ 2) ≤ 10 ^ 100 := by
  have hℓ : 0 < ell v μ := ell_pos_of_le hR hRℓ
  have hsub : (∑ k ∈ Work.BoseB7.excited (Lab (HM μ).N),
        ((HonestBoxFam v h fc fu HM μ).E.hatChi k) ^ 2)
      ≤ ∑ k : Lab (HM μ).N,
          ((HonestBoxFam v h fc fu HM μ).E.hatChi k) ^ 2 := by
    refine Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.erase_subset (0 : Lab (HM μ).N) Finset.univ) ?_
    intro x _ _
    positivity
  have hpin : (∑ k : Lab (HM μ).N,
        ((HonestBoxFam v h fc fu HM μ).E.hatChi k) ^ 2)
      = ∑ k : Lab (HM μ).N,
          (Work.BoseK15.corpusBox.hatChi (Work.BoseB4.vec (labVec (HM μ).N k))) ^ 2 :=
    Finset.sum_congr rfl (fun k _ => by rw [honest_hatChi_eq h fc fu HM hℓ k])
  calc (∑ k ∈ Work.BoseB7.excited (Lab (HM μ).N),
        ((HonestBoxFam v h fc fu HM μ).E.hatChi k) ^ 2)
      ≤ ∑ k : Lab (HM μ).N,
          ((HonestBoxFam v h fc fu HM μ).E.hatChi k) ^ 2 := hsub
    _ = ∑ k : Lab (HM μ).N,
          (Work.BoseK15.corpusBox.hatChi (Work.BoseB4.vec (labVec (HM μ).N k))) ^ 2 := hpin
    _ ≤ 1 := Work.BoseBoxFock.sum_hatChi_sq_le (HM μ).N
    _ ≤ 10 ^ 100 := by norm_num

/-- **Row 5** (the mode count): `f_L`'s support (`LowCut`; `f_L(s) ≠ 0 ⟹ ‖kmom s‖ < 2K_L√(μa)`)
and the lattice count `card_le_of_vec_lab`. -/
theorem farRow_count {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v)
    (hv : 0 ≤ v) (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ Metric.ball 0 R)
    (hav : 0 < a v) (fc fu : LowCut) (HM : ∀ μ : ℝ, HonestModes v μ) {μ : ℝ} (hμ : 0 < μ)
    (hview : (HonestBoxFam v h fc fu HM μ).viewFS v h μ)
    (hRℓ : R ≤ ell v μ * Submission.BoseGases.chiR0) :
    ((∑ s ∈ (Work.BoseB7.excited (Lab (HM μ).N)).filter
        (fun s => (HonestBoxFam v h fc fu HM μ).E.fL s ≠ 0), (1 : ℝ))
          ≤ 10 ^ 6 * (ell v μ
              * (HonestBoxFam v h fc fu HM μ).E.KL
              * Real.sqrt (μ * a v) + 1) ^ 3) := by
  classical
  have hℓ : 0 < ell v μ := ell_pos_of_le hR hRℓ
  have hKL1 : 1 ≤ (HonestBoxFam v h fc fu HM μ).E.KL := hview.1.some.one_le_KL
  let T : Finset (Lab (HM μ).N) := (Work.BoseB7.excited (Lab (HM μ).N)).filter
    (fun s => (HonestBoxFam v h fc fu HM μ).E.fL s ≠ 0)
  let A : ℝ := ell v μ * (HonestBoxFam v h fc fu HM μ).E.KL * Real.sqrt (μ * a v)
  let ρ : ℝ := 2 * A
  have hKLpos : 0 < (HonestBoxFam v h fc fu HM μ).E.KL := lt_of_lt_of_le one_pos hKL1
  have hsqrtpos : 0 < Real.sqrt (μ * a v) := Real.sqrt_pos.mpr (mul_pos hμ hav)
  have hA0 : 0 ≤ A := by positivity
  have hden : 0 < (HonestBoxFam v h fc fu HM μ).E.KL * Real.sqrt (μ * a v) :=
    mul_pos hKLpos hsqrtpos
  have hρ0 : 0 ≤ ρ := by positivity
  -- the support condition of `f_L`
  have hS : ∀ s ∈ T, ‖Work.BoseB4.vec (labVec (HM μ).N s)‖ ≤ ρ := by
    intro s hs
    have hne : (HonestBoxFam v h fc fu HM μ).E.fL s ≠ 0 := (Finset.mem_filter.mp hs).2
    have hfL : (HonestBoxFam v h fc fu HM μ).E.fL s
        = fc.f (‖(HonestBoxFam v h fc fu HM μ).F.kmom s‖
            / ((HonestBoxFam v h fc fu HM μ).E.KL * Real.sqrt (μ * a v))) := rfl
    have hval : fc.f (‖(HonestBoxFam v h fc fu HM μ).F.kmom s‖
          / ((HonestBoxFam v h fc fu HM μ).E.KL * Real.sqrt (μ * a v))) ≠ 0 := hfL ▸ hne
    have hlt : ‖(HonestBoxFam v h fc fu HM μ).F.kmom s‖
        / ((HonestBoxFam v h fc fu HM μ).E.KL * Real.sqrt (μ * a v)) < 2 := by
      by_contra hcon
      exact hval (fc.zero _ (le_of_not_gt hcon))
    have hlt' : ‖(HonestBoxFam v h fc fu HM μ).F.kmom s‖
        < 2 * ((HonestBoxFam v h fc fu HM μ).E.KL * Real.sqrt (μ * a v)) := by
      rwa [div_lt_iff₀ hden] at hlt
    have hkm : ‖(HonestBoxFam v h fc fu HM μ).F.kmom s‖
        = (ell v μ)⁻¹ * ‖Work.BoseB4.vec (labVec (HM μ).N s)‖ := by
      rw [show (HonestBoxFam v h fc fu HM μ).F.kmom s
            = kmomLab (ellH v μ) (HM μ).N s from rfl,
          honest_kmom_eq h fc fu HM hℓ s, norm_smul, Real.norm_eq_abs, abs_inv,
          abs_of_pos hℓ]
    rw [hkm] at hlt'
    have h2 : ell v μ * ((ell v μ)⁻¹ * ‖Work.BoseB4.vec (labVec (HM μ).N s)‖)
        < ell v μ * (2 * ((HonestBoxFam v h fc fu HM μ).E.KL * Real.sqrt (μ * a v))) :=
      mul_lt_mul_of_pos_left hlt' hℓ
    have h3 : ell v μ * ((ell v μ)⁻¹ * ‖Work.BoseB4.vec (labVec (HM μ).N s)‖)
        = ‖Work.BoseB4.vec (labVec (HM μ).N s)‖ := by
      rw [← mul_assoc, mul_inv_cancel₀ (ne_of_gt hℓ), one_mul]
    rw [h3] at h2
    have h4 : ell v μ * (2 * ((HonestBoxFam v h fc fu HM μ).E.KL * Real.sqrt (μ * a v)))
        = ρ := by
      simp only [ρ, A]; ring
    linarith [h2, h4 ▸ h2]
  -- the count
  have hcount : ((T.card : ℝ)) ≤ 10 ^ 6 * (A + 1) ^ 3 := by
    have hcard := card_le_of_vec_lab T ρ hρ0 hS
    have hρπ : ρ / Real.pi + 1 ≤ A + 1 := by
      have hp : 2 / Real.pi ≤ 1 := by
        rw [div_le_one (by positivity)]
        linarith [Real.pi_gt_three]
      calc ρ / Real.pi + 1 = (2 / Real.pi) * A + 1 := by
            simp only [ρ]; ring
        _ ≤ 1 * A + 1 := by linarith [mul_le_mul_of_nonneg_right hp hA0]
        _ = A + 1 := by ring
    have h1 : 0 ≤ ρ / Real.pi + 1 := by positivity
    have h2 : 0 ≤ A + 1 := by linarith
    calc ((T.card : ℝ)) ≤ (ρ / Real.pi + 1) ^ 3 := hcard
      _ ≤ (A + 1) ^ 3 := pow_le_pow_left₀ h1 hρπ 3
      _ ≤ 10 ^ 6 * (A + 1) ^ 3 := by
          have := pow_nonneg h2 3
          nlinarith [this]
  have hsumT : (∑ s ∈ T, (1 : ℝ)) = (T.card : ℝ) := by
    rw [Finset.sum_const, nsmul_eq_mul, mul_one]
  exact le_trans (le_of_eq hsumT) hcount

/-! ## 4. Row 4's provable cores

The lattice-weight sum is numerically bounded (`latticeWeightSumLe`), so the *only* unpinned factor
of row 4 is the decay constant of `χ̂²`. -/

/-- **The lattice-weight sum is numerically bounded.**  For `3 ≤ 2s` and every finite set of labels,

    `∑_{n∈S} (1 + ‖2πn‖²)^{-s} ≤ 10^3`.

Split `S` at the origin: `∑_{n∈S} = ∑_{n∈S, n=0} + ∑_{n∈S, n≠0}`.  The first part is `≤ 1` (only
`n = 0` satisfies `‖vec n‖ < 1`), the second consists of points with `1 ≤ ‖vec n‖` and is dominated
by `Work.BoseK15.sum_inv_one_add_norm_tail_const` at `R = 1`, `M = 0` (which gives `≤ 128`). -/
theorem latticeWeightSumLe (s : ℕ) (hs : 3 ≤ 2 * s) (S : Finset (Fin 3 → ℤ)) :
    (∑ n ∈ S, (((1 : ℝ) + ‖Work.BoseB4.vec n‖ ^ 2) ^ s)⁻¹) ≤ 10 ^ 3 := by
  classical
  rw [← Finset.sum_filter_add_sum_filter_not S (fun n : Fin 3 → ℤ => n = 0)]
  have hzero : (∑ n ∈ S.filter (fun n : Fin 3 → ℤ => n = 0),
      (((1 : ℝ) + ‖Work.BoseB4.vec n‖ ^ 2) ^ s)⁻¹) ≤ 1 := by
    have hcard : (S.filter (fun n : Fin 3 → ℤ => n = 0)).card ≤ 1 := by
      rw [Finset.card_le_one]
      intro a ha b hb
      exact (Finset.mem_filter.mp ha).2.trans (Finset.mem_filter.mp hb).2.symm
    have hterm : ∀ n ∈ S.filter (fun n : Fin 3 → ℤ => n = 0),
        (((1 : ℝ) + ‖Work.BoseB4.vec n‖ ^ 2) ^ s)⁻¹ ≤ 1 := by
      intro n _
      have h1 : (1 : ℝ) ≤ (1 : ℝ) + ‖Work.BoseB4.vec n‖ ^ 2 := by
        have := sq_nonneg (‖Work.BoseB4.vec n‖ : ℝ)
        linarith
      exact inv_le_one_of_one_le₀ (one_le_pow₀ h1)
    calc (∑ n ∈ S.filter (fun n : Fin 3 → ℤ => n = 0),
          (((1 : ℝ) + ‖Work.BoseB4.vec n‖ ^ 2) ^ s)⁻¹)
        ≤ ∑ _n ∈ S.filter (fun n : Fin 3 → ℤ => n = 0), (1 : ℝ) := Finset.sum_le_sum hterm
      _ = ((S.filter (fun n : Fin 3 → ℤ => n = 0)).card : ℝ) := by
          rw [Finset.sum_const, nsmul_eq_mul, mul_one]
      _ ≤ 1 := by exact_mod_cast hcard
  have htail : (∑ n ∈ S.filter (fun n : Fin 3 → ℤ => ¬ (n = 0)),
      (((1 : ℝ) + ‖Work.BoseB4.vec n‖ ^ 2) ^ s)⁻¹) ≤ 128 := by
    have h := Work.BoseK15.sum_inv_one_add_norm_tail_const s 0 (by simpa using hs) 1
      (S.filter (fun n : Fin 3 → ℤ => ¬ (n = 0))) (le_refl 1) ?_
    · simpa using h
    · intro n hn
      have hn0 : n ≠ 0 := (Finset.mem_filter.mp hn).2
      obtain ⟨i, hi⟩ : ∃ i : Fin 3, n i ≠ 0 := by
        by_contra hcon
        push Not at hcon
        exact hn0 (funext hcon)
      have h1 : (1 : ℝ) ≤ |((n i : ℤ) : ℝ)| := by
        have h1' : (1 : ℤ) ≤ |n i| := by
          have := abs_pos.mpr hi
          omega
        exact_mod_cast h1'
      have h2 := Work.BoseK15.two_pi_mul_abs_coord_le_norm_vec n i
      have h3 : (1 : ℝ) ≤ 2 * Real.pi * |((n i : ℤ) : ℝ)| := by
        nlinarith [Real.pi_gt_three]
      linarith
  linarith

/-- **Row 4's provable core**: from the corpus decay `ChiReg corpusBox s Cchi` (FS
`lem:DecaychiHat`) and *any* lattice-weight bound `Csum`, the ℓ¹ sum over the excited modes is at
most `Cchi * Csum`. -/
theorem sumHatChiSqLe (N s : ℕ) (Cchi Csum : ℝ) (hCchi : 0 ≤ Cchi)
    (hchi : Work.BoseK15.ChiReg Work.BoseK15.corpusBox s Cchi)
    (hsum : ∀ S : Finset (Fin 3 → ℤ),
      (∑ n ∈ S, (((1 : ℝ) + ‖Work.BoseB4.vec n‖ ^ 2) ^ s)⁻¹) ≤ Csum) :
    (∑ k ∈ Work.BoseB7.excited (Lab N),
        |Work.BoseK15.corpusBox.hatChiSq (Work.BoseB4.vec (labVec N k))|)
      ≤ Cchi * Csum := by
  have hterm : ∀ n : Fin 3 → ℤ, |Work.BoseK15.corpusBox.hatChiSq (Work.BoseB4.vec n)|
      ≤ Cchi * (((1 : ℝ) + ‖Work.BoseB4.vec n‖ ^ 2) ^ s)⁻¹ := by
    intro n
    have h := hchi.2 (Work.BoseB4.vec n)
    have hpos : (0 : ℝ) < ((1 : ℝ) + ‖Work.BoseB4.vec n‖ ^ 2) ^ s := by positivity
    rw [le_mul_inv_iff₀ hpos]
    exact h
  have hstep : (∑ k ∈ Work.BoseB7.excited (Lab N),
        |Work.BoseK15.corpusBox.hatChiSq (Work.BoseB4.vec (labVec N k))|)
      ≤ Cchi * (∑ k ∈ Work.BoseB7.excited (Lab N),
          (((1 : ℝ) + ‖Work.BoseB4.vec (labVec N k)‖ ^ 2) ^ s)⁻¹) := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun k _ => hterm (labVec N k))
  have himg : (∑ k ∈ Work.BoseB7.excited (Lab N),
        (((1 : ℝ) + ‖Work.BoseB4.vec (labVec N k)‖ ^ 2) ^ s)⁻¹)
      = ∑ n ∈ (Work.BoseB7.excited (Lab N)).image (labVec N),
          (((1 : ℝ) + ‖Work.BoseB4.vec n‖ ^ 2) ^ s)⁻¹ := by
    rw [Finset.sum_image]
    intro a _ b _ hab
    exact labVec_injective N hab
  calc (∑ k ∈ Work.BoseB7.excited (Lab N),
        |Work.BoseK15.corpusBox.hatChiSq (Work.BoseB4.vec (labVec N k))|)
      ≤ Cchi * (∑ k ∈ Work.BoseB7.excited (Lab N),
          (((1 : ℝ) + ‖Work.BoseB4.vec (labVec N k)‖ ^ 2) ^ s)⁻¹) := hstep
    _ = Cchi * (∑ n ∈ (Work.BoseB7.excited (Lab N)).image (labVec N),
          (((1 : ℝ) + ‖Work.BoseB4.vec n‖ ^ 2) ^ s)⁻¹) := by rw [himg]
    _ ≤ Cchi * Csum := mul_le_mul_of_nonneg_left (hsum _) hCchi

/-- **Row 4 with the numeric lattice constant**: the ℓ¹ sum is at most `C · 10^3`, where `C` is the
decay constant of `χ̂²` at order `s` (`3 ≤ 2s`).  The *only* un-pinned factor is `C`: no numeric
bound on it is provable (see the header), so the requested row 4 with `C · 10^3 ≤ 10^100` is not. -/
theorem sumHatChiSqLeOfChiReg (N s : ℕ) (C : ℝ) (hs : 3 ≤ 2 * s) (hC : 0 ≤ C)
    (hchi : Work.BoseK15.ChiReg Work.BoseK15.corpusBox s C) :
    (∑ k ∈ Work.BoseB7.excited (Lab N),
        |Work.BoseK15.corpusBox.hatChiSq (Work.BoseB4.vec (labVec N k))|) ≤ C * 10 ^ 3 :=
  sumHatChiSqLe N s C (10 ^ 3) hC hchi (fun S => latticeWeightSumLe s hs S)

/-- **Row 4 at the honest family, existential constant**: the `ChiReg_corpus` decay (FS
`lem:DecaychiHat` for the corpus `χ`) together with `Work.BoseK15.sum_inv_one_add_norm_le` (the
summability of the lattice weights) bounds the ℓ¹ sum by *some* constant `C ≥ 0`.  This is the form
in which the row is provable; the numeric form `≤ 10^100` would need a numeric bound on the decay
constant, which is not available (header). -/
theorem farRow_hatChiSq {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v)
    (fc fu : LowCut) (HM : ∀ μ : ℝ, HonestModes v μ) {μ R : ℝ} (hR : 0 < R)
    (hRℓ : R ≤ ell v μ * Submission.BoseGases.chiR0) :
    ∃ C : ℝ, 0 ≤ C ∧ (∑ k ∈ Work.BoseB7.excited (Lab (HM μ).N),
        |(HonestBoxFam v h fc fu HM μ).E.hatChiSq k|) ≤ C := by
  have hℓ : 0 < ell v μ := ell_pos_of_le hR hRℓ
  obtain ⟨Cchi, hCchi, hreg⟩ := Work.BoseK15.ChiReg_corpus Work.BoseK15.decayOrder
  obtain ⟨Csum, hCsum0, hCsum⟩ := Work.BoseK15.sum_inv_one_add_norm_le Work.BoseK15.decayOrder
    (by norm_num [Work.BoseK15.decayOrder])
  refine ⟨Cchi * Csum, by positivity, ?_⟩
  have hEq : (∑ k ∈ Work.BoseB7.excited (Lab (HM μ).N),
        |(HonestBoxFam v h fc fu HM μ).E.hatChiSq k|)
      = ∑ k ∈ Work.BoseB7.excited (Lab (HM μ).N),
          |Work.BoseK15.corpusBox.hatChiSq (Work.BoseB4.vec (labVec (HM μ).N k))| :=
    Finset.sum_congr rfl (fun k _ => by rw [honest_hatChiSq_eq h fc fu HM hℓ k])
  rw [hEq]
  exact sumHatChiSqLe (HM μ).N Work.BoseK15.decayOrder Cchi Csum hCchi hreg hCsum

/-- **The exact gap of the numeric row 4**: the requested numeric form
`∑_{k≠0}|χ̂²(k)| ≤ 10^100` holds as soon as the decay constant of `χ̂²` at some order `s`
(`3 ≤ 2s`) is *numerically* bounded by `10^97`, i.e. `ChiReg corpusBox s C` with
`C * 10^3 ≤ 10^100`.  `ChiReg_corpus` supplies only an *existential* `C`, and no numeric bound on
it is provable (header), which is exactly where the requested statement is blocked. -/
theorem farRow_hatChiSq_of_numeric_decay {v : EuclideanSpace ℝ (Fin 3) → ℝ}
    (h : Work.UBB.ScatSol v) (fc fu : LowCut) (HM : ∀ μ : ℝ, HonestModes v μ) {μ R : ℝ}
    (hR : 0 < R) (hRℓ : R ≤ ell v μ * Submission.BoseGases.chiR0)
    {s : ℕ} {C : ℝ} (hs : 3 ≤ 2 * s) (hC : 0 ≤ C)
    (hchi : Work.BoseK15.ChiReg Work.BoseK15.corpusBox s C) (hnum : C * 10 ^ 3 ≤ 10 ^ 100) :
    (∑ k ∈ Work.BoseB7.excited (Lab (HM μ).N),
        |(HonestBoxFam v h fc fu HM μ).E.hatChiSq k|) ≤ 10 ^ 100 := by
  have hℓ : 0 < ell v μ := ell_pos_of_le hR hRℓ
  have hEq : (∑ k ∈ Work.BoseB7.excited (Lab (HM μ).N),
        |(HonestBoxFam v h fc fu HM μ).E.hatChiSq k|)
      = ∑ k ∈ Work.BoseB7.excited (Lab (HM μ).N),
          |Work.BoseK15.corpusBox.hatChiSq (Work.BoseB4.vec (labVec (HM μ).N k))| :=
    Finset.sum_congr rfl (fun k _ => by rw [honest_hatChiSq_eq h fc fu HM hℓ k])
  rw [hEq]
  exact le_trans (sumHatChiSqLeOfChiReg (HM μ).N s C hs hC hchi) hnum

/-- **The repaired bundle**: the requested five rows, with row 4's `10^100` replaced by an
existential constant.  Sorry-free; this is the statement the far leg can consume (the remaining
rows keep their numeric constants, which are provable). -/
theorem farKernelRowsRepaired {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v)
    (hv : 0 ≤ v) (hv1 : MeasureTheory.MemLp v 1) (hvrad : _root_.BoseGases.IsRadial v)
    {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    (hav : 0 < a v) (fc fu : LowCut)
    (HM : ∀ μ : ℝ, HonestModes v μ)
    {μ : ℝ} (hμ : 0 < μ)
    (hview : (HonestBoxFam v h fc fu HM μ).viewFS v h μ)
    (hRℓ : R ≤ ell v μ * Submission.BoseGases.chiR0) :
    (∀ k : Lab (HM μ).N,
        |(HonestBoxFam v h fc fu HM μ).E.W1 k| ≤ 16 * Real.pi * a v)
    ∧ (∀ k : Lab (HM μ).N,
        |(HonestBoxFam v h fc fu HM μ).E.W1omega k| ≤ 16 * Real.pi * a v)
    ∧ (∑ k ∈ Work.BoseB7.excited (Lab (HM μ).N),
        ((HonestBoxFam v h fc fu HM μ).E.hatChi k) ^ 2 ≤ 10 ^ 100)
    ∧ (∃ C : ℝ, 0 ≤ C ∧ (∑ k ∈ Work.BoseB7.excited (Lab (HM μ).N),
        |(HonestBoxFam v h fc fu HM μ).E.hatChiSq k|) ≤ C)
    ∧ ((∑ s ∈ (Work.BoseB7.excited (Lab (HM μ).N)).filter
        (fun s => (HonestBoxFam v h fc fu HM μ).E.fL s ≠ 0), (1 : ℝ))
          ≤ 10 ^ 6 * (ell v μ
              * (HonestBoxFam v h fc fu HM μ).E.KL
              * Real.sqrt (μ * a v) + 1) ^ 3) :=
  ⟨farRow_W1 h hv hvrad hR hv_supp hav fc fu HM hRℓ,
    farRow_W1omega h hv hvrad hR hv_supp hav fc fu HM hRℓ,
    farRow_hatChi h fc fu HM hR hRℓ,
    farRow_hatChiSq h fc fu HM hR hRℓ,
    farRow_count h hv hvrad hR hv_supp hav fc fu HM hμ hview hRℓ⟩

/-! ## 5. `SKELETON`: the requested statement, verbatim

`FarKernelRows` is kept **verbatim** (its consumers `Submission/Work/BoseFixR/FarResid.lean` and
`RB5FSHonestFix.lean` apply it), but row 4 is the hole: the statement below is *not provable* in
this workspace (header).  Use `farKernelRowsRepaired` instead, with row 4's `10^100` replaced by the
existential constant of `farRow_hatChiSq`. -/
theorem FarKernelRows {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v)
    (hv : 0 ≤ v) (hv1 : MeasureTheory.MemLp v 1) (hvrad : BoseGases.IsRadial v)
    {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    (hav : 0 < BoseGases.a v) (fc fu : Work.BoseBoxFix.LowCut)
    (HM : ∀ μ : ℝ, Work.BoseBoxFock.HonestModes v μ)
    {μ : ℝ} (hμ : 0 < μ)
    (hview : (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).viewFS v h μ)
    (hRℓ : R ≤ Work.BoseFixR.ell v μ * Submission.BoseGases.chiR0) :
    (∀ k : Work.BoseBoxFock.Lab (HM μ).N,
        |(Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E.W1 k| ≤ 16 * Real.pi * BoseGases.a v)
    ∧ (∀ k : Work.BoseBoxFock.Lab (HM μ).N,
        |(Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E.W1omega k|
          ≤ 16 * Real.pi * BoseGases.a v)
    ∧ (∑ k ∈ Work.BoseB7.excited (Work.BoseBoxFock.Lab (HM μ).N),
        ((Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E.hatChi k) ^ 2 ≤ 10 ^ 100)
    ∧ (∑ k ∈ Work.BoseB7.excited (Work.BoseBoxFock.Lab (HM μ).N),
        |(Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E.hatChiSq k| ≤ 10 ^ 100)
    ∧ ((∑ s ∈ (Work.BoseB7.excited (Work.BoseBoxFock.Lab (HM μ).N)).filter
        (fun s => (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E.fL s ≠ 0), (1 : ℝ))
          ≤ 10 ^ 6 * (Work.BoseFixR.ell v μ
              * (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E.KL
              * Real.sqrt (μ * BoseGases.a v) + 1) ^ 3) := by
  sorry

end Work.BoseFixR
