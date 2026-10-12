import ChallengeDeps
import Mathlib.Analysis.Convolution
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Submission.Work.BoseBoxFock.KfrU_sub_uvSmear_norm_le
import Submission.Work.BoseBoxFock.PCFU.chBimg_Kchi_sup
import Submission.Work.BoseBoxFock.PCFU.chCslot_aux
import Submission.Work.BoseBoxFock.PCFU.kpSchur
import Submission.Work.BoseBoxFock.PotCubicPoissonAux
import Submission.Work.BoseBoxFock.kernelImage_le
import Submission.Work.BoseBoxFock.latImagesDefs
import Submission.Work.BoseBoxFock.uvSmear_L1_le
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.PCFU.chCslot_kernelPair`

The **pairing form** of the alias-kernel estimate for the `(C)`-slot (the repair, recommended in
`FINDING_chCslot_kernelSup_FALSE.md` §6, of the refuted pointwise sup form `ChKerLe`).

With `ℓ = ellH v μ`, `χ_ℓ = chiLam ℓ` (the corpus bump of support `ball 0 (ℓ/2)`) and
`D = chD = KfrU − ℓ³·W₁` the alias kernel, the target is: for every `η > 0` there is a UV threshold
`T` with, for all `N ≥ T` and all `f g ∈ L²(ℝ³)`,

    ‖∫_w ∫_z f w · χ_ℓ(w) · D(w − z) · χ_ℓ(z) · g z‖
        ≤ (η ℓ³ + C ℓ³ (R/ℓ)¹²) · ‖f‖₂ ‖g‖₂ .

**Proof strategy.**  `D = ℓ³·E + (KfrU − ℓ³·uvSmear)` with `E = uvSmear − W₁` the smoothing error
(`‖E‖₁ → 0` as `Λ = uvRad ℓ N → ∞`, the proved `uvSmear_L1_tendsto`) and
`KfrU − ℓ³·uvSmear = ℓ³·Σ'_{m ≠ 0} uvSmear(· + ℓ m)` the lattice images (`KfrU_periodisation`),
whose `χ`-weighted `lintegral` is estimated by `latImages_lintegral_le` (face-layer flatness of the
corpus bump + the bounded overlap of the balls `ball (w + ℓ m) (ℓ/2)`).  Both pieces give a bound
`≤ ℓ³·C·(R/ℓ)¹²` once the UV threshold makes the smoothing error `≤ (R/ℓ)¹²`; the Schur test
(`schur_pairing_le`) then converts the two `lintegral` bounds (in `w` and in `z`) into the `L²`
pairing bound.

**Provenance of the inputs (all proved, `sorry`-free, axiom-clean).**

* `kp_latImages_lintegral_le` (with `C = latImgC`) is proved *in this file* by the three bricks
  `kp_latImgTsum_le` (geometry: `chiScale_pair_image_le` + uniqueness of the contributing lattice
  index), `kp_latImg_lintegral_le` (Tonelli + the measure-preserving substitution `z ↦ c − z`,
  via `lintegral_add_right_eq_self`/`lintegral_neg_eq_self`) and `kp_latImgLin_le` (the split at
  `‖v‖ ⋚ ρ`, through `ofReal_integral_eq_lintegral_ofReal`).  (The delegated modules
  `latImages_lintegral_le*`, `latImg*` are *not* used: their statements are the same but the
  fix had to be local.)
* `kp_schur_pairing_le` is a copy, in this namespace, of the proved `schur_pairing_le` from
  `Submission/Work/BoseBoxFock/kpSchur.lean`, needed because `schur_pairing_le`'s helper
  `Work.BoseBoxFock.ofReal_integral_le_lintegral` clashes with the identical name already in this
  file's import cone (`B13Main`).
-/

namespace Work.BoseBoxFock.PCFU

open MeasureTheory
open scoped ENNReal

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-! ## 1. Elementary lattice and window facts -/

/-- The lattice vector is odd: `latVec (−m) = − latVec m`. -/
theorem kp_latVec_neg (m : Fin 3 → ℤ) : latVec (-m) = -latVec m := by
  ext i
  simp [latVec]

/-- **Relabelling a lattice sum by `m ↦ −m`** (the index map is a bijection of `ℤ³`). -/
theorem kp_tsum_latVec_neg (F : (Fin 3 → ℤ) → ℝ) :
    (∑' m : Fin 3 → ℤ, F (-m)) = ∑' m : Fin 3 → ℤ, F m :=
  Equiv.tsum_eq (Equiv.neg (Fin 3 → ℤ)) F

/-- The same relabelling for `ℂ`-valued families. -/
theorem kp_tsum_latVec_neg_C (F : (Fin 3 → ℤ) → ℂ) :
    (∑' m : Fin 3 → ℤ, F (-m)) = ∑' m : Fin 3 → ℤ, F m :=
  Equiv.tsum_eq (Equiv.neg (Fin 3 → ℤ)) F

/-- `chiScale` is the corpus bump (`corpusBox.chiLam`), definitionally. -/
theorem kp_chiScale_eq_chiLam (ℓ : ℝ) :
    Submission.BoseGases.chiScale ℓ = Work.BoseK15.corpusBox.chiLam ℓ := rfl

/-- The corpus bump (`corpusBox.chiLam`) is nonnegative. -/
theorem kp_chiLam_nonneg (ℓ : ℝ) (x : E3) : 0 ≤ Work.BoseK15.corpusBox.chiLam ℓ x :=
  Work.BoseB4.BoxData.chiLam_nonneg Work.BoseK15.corpusBox ℓ x

/-- The corpus bump (`corpusBox.chiLam`) is bounded by `chiSup`. -/
theorem kp_chiLam_le_chiSup (ℓ : ℝ) (x : E3) :
    Work.BoseK15.corpusBox.chiLam ℓ x ≤ Submission.BoseGases.chiSup := by
  have h : |Work.BoseK15.corpusBox.chiLam ℓ x| ≤ Submission.BoseGases.chiSup := by
    rw [Submission.BoseGases.chiSup]
    exact Work.BoseBoxFock.PCFU.chiLam_abs_le ℓ x
  exact le_trans (le_abs_self _) h

/-- The corpus window is nonnegative. -/
theorem kp_chiScale_nonneg (ℓ : ℝ) (x : E3) : 0 ≤ Submission.BoseGases.chiScale ℓ x :=
  Work.BoseB4.BoxData.chiLam_nonneg Work.BoseK15.corpusBox ℓ x

/-- The corpus window is bounded by `chiSup`. -/
theorem kp_chiScale_le_chiSup (ℓ : ℝ) (x : E3) :
    Submission.BoseGases.chiScale ℓ x ≤ Submission.BoseGases.chiSup := by
  have h1 : |Work.BoseK15.corpusBox.chiLam ℓ x| ≤ Submission.BoseGases.chiSup := by
    rw [Submission.BoseGases.chiSup]
    exact Work.BoseBoxFock.PCFU.chiLam_abs_le ℓ x
  calc Submission.BoseGases.chiScale ℓ x
      = Work.BoseK15.corpusBox.chiLam ℓ x := rfl
    _ ≤ |Work.BoseK15.corpusBox.chiLam ℓ x| := le_abs_self _
    _ ≤ Submission.BoseGases.chiSup := h1

/-- The corpus window is continuous. -/
theorem kp_chiScale_continuous (ℓ : ℝ) : Continuous (Submission.BoseGases.chiScale ℓ) :=
  Work.BoseB4.BoxData.chiLam_cont Work.BoseK15.corpusBox ℓ

/-- The window is even. -/
theorem kp_chiScale_even (ℓ : ℝ) (x : E3) :
    Submission.BoseGases.chiScale ℓ (-x) = Submission.BoseGases.chiScale ℓ x :=
  Work.BoseB4.BoxData.chiLam_even Work.BoseK15.corpusBox ℓ x

/-! ## 2. Evenness and integrability of `uvSmear` -/

/-- **`uvSmear` of an even function is even.** -/
theorem kp_uvSmear_even (fu : Work.BoseBoxFix.LowCut) {f : E3 → ℝ}
    (hf : ∀ x : E3, f (-x) = f x) (Λ : ℝ) (x : E3) :
    uvSmear fu Λ f (-x) = uvSmear fu Λ f x := by
  have hker : ∀ y : E3, uvKernel fu Λ (-x + y) = uvKernel fu Λ (x - y) := by
    intro y
    have h : -x + y = -(x - y) := by abel
    rw [h, Work.BoseBoxFock.uvKernel_even]
  rw [uvSmear, uvSmear,
    ← MeasureTheory.integral_neg_eq_self (fun z : E3 => uvKernel fu Λ (-x - z) * f z) volume]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  show uvKernel fu Λ (-x - -y) * f (-y) = uvKernel fu Λ (x - y) * f y
  rw [show (-x - -y : E3) = -x + y by abel, hker y, hf y]

/-- **`uvSmear` of a compactly supported integrable function is integrable** (rapid decay). -/
theorem kp_integrable_uvSmear (fu : Work.BoseBoxFix.LowCut) {f : E3 → ℝ}
    (hf : Integrable f) (hfs : HasCompactSupport f) {Λ : ℝ} (hΛ : 0 < Λ) :
    Integrable (uvSmear fu Λ f) := by
  obtain ⟨C, hCnn, hC⟩ := Work.BoseBoxFock.uvSmear_rapidDecay fu hΛ hf hfs 4
  refine Integrable.mono' ((integrable_one_add_norm_zpow 4 (by norm_num)).const_mul C)
    (Work.BoseBoxFock.uvSmear_continuous fu hΛ hf).aestronglyMeasurable ?_
  filter_upwards with x
  rw [Real.norm_eq_abs]
  exact hC x

/-- The kernel `W₁ = W1fun v h ℓ` has compact support in the dilute regime. -/
theorem kp_hasCompactSupport_W1 {v : E3 → ℝ} {h : Work.UBB.ScatSol v} {R : ℝ}
    (hv_supp : tsupport v ⊆ Metric.ball (0 : E3) R) (ℓ : ℝ) :
    HasCompactSupport (Work.BoseFixR.W1fun v h ℓ) := by
  have hsub : tsupport (Work.BoseFixR.W1fun v h ℓ) ⊆ Metric.closedBall (0 : E3) R := by
    intro x hx
    have h1 := Work.BoseFixR.tsupport_W1fun_subset h hv_supp ℓ hx
    rw [Metric.mem_ball, dist_zero_right] at h1
    rw [Metric.mem_closedBall, dist_zero_right]
    exact h1.le
  exact (isCompact_closedBall (0 : E3) R).of_isClosed_subset isClosed_closure hsub

/-- `W₁` vanishes outside the ball of radius `R`. -/
theorem kp_W1_zero_of_norm_ge {v : E3 → ℝ} {h : Work.UBB.ScatSol v} {R : ℝ}
    (hv_supp : tsupport v ⊆ Metric.ball (0 : E3) R) (ℓ : ℝ) {x : E3} (hx : R ≤ ‖x‖) :
    Work.BoseFixR.W1fun v h ℓ x = 0 := by
  by_contra hne
  have hmem : x ∈ tsupport (Work.BoseFixR.W1fun v h ℓ) :=
    subset_closure (Function.mem_support.mpr hne)
  have h1 := Work.BoseFixR.tsupport_W1fun_subset h hv_supp ℓ hmem
  rw [Metric.mem_ball, dist_zero_right] at h1
  exact absurd h1 (not_lt.mpr hx)

/-! ## 3. Two auxiliary estimates -/

/-- **The lattice-image sum is symmetric in its two arguments** (for an even kernel): exchanging
`y ↔ c` only reflects the summand, which the lattice bijection `m ↦ −m` undoes. -/
theorem kp_sum_orient {U : E3 → ℝ} (hU : ∀ x : E3, U (-x) = U x) (ℓ : ℝ) (y c : E3) :
    (∑' m : Fin 3 → ℤ, (if m = 0 then (0 : ℝ) else ‖U (y - c + ℓ • latVec m)‖))
      = ∑' m : Fin 3 → ℤ, (if m = 0 then (0 : ℝ) else ‖U (c - y + ℓ • latVec m)‖) := by
  have hpt : ∀ m : Fin 3 → ℤ,
      (if m = 0 then (0 : ℝ) else ‖U (y - c + ℓ • latVec m)‖)
        = (if (-m) = 0 then (0 : ℝ) else ‖U (c - y + ℓ • latVec (-m))‖) := by
    intro m
    by_cases hm : m = 0
    · subst hm
      simp
    · have hneg : (-m : Fin 3 → ℤ) ≠ 0 := by
        intro hcon
        exact hm (by simpa using congrArg Neg.neg hcon)
      rw [if_neg hm, if_neg hneg]
      have key : c - y + ℓ • latVec (-m) = -(y - c + ℓ • latVec m) := by
        rw [kp_latVec_neg, smul_neg]
        abel
      rw [key, ← hU (y - c + ℓ • latVec m)]
  calc (∑' m : Fin 3 → ℤ, (if m = 0 then (0 : ℝ) else ‖U (y - c + ℓ • latVec m)‖))
      = ∑' m : Fin 3 → ℤ, (if (-m) = 0 then (0 : ℝ) else ‖U (c - y + ℓ • latVec (-m))‖) :=
        tsum_congr hpt
    _ = ∑' m : Fin 3 → ℤ, (if m = 0 then (0 : ℝ) else ‖U (c - y + ℓ • latVec m)‖) :=
        kp_tsum_latVec_neg (fun m => (if m = 0 then (0 : ℝ) else ‖U (c - y + ℓ • latVec m)‖))

/-- **The smoothing row.**  The `χ`-weighted `lintegral` of the smoothing error `E` is bounded by
`chiSup²·∫‖E‖` (both `χ`-factors are simply majorised by `chiSup`). -/
theorem kp_E_le {E : E3 → ℝ} (hE : MeasureTheory.Integrable E) (ℓ : ℝ) (c : E3) :
    ∫⁻ y : E3, ENNReal.ofReal (Submission.BoseGases.chiScale ℓ y
        * Submission.BoseGases.chiScale ℓ c * ‖E (c - y)‖)
      ≤ ENNReal.ofReal (Submission.BoseGases.chiSup ^ 2 * ∫ x : E3, ‖E x‖) := by
  have hshift : ∫ y : E3, ‖E (c - y)‖ = ∫ x : E3, ‖E x‖ :=
    MeasureTheory.integral_sub_left_eq_self (fun x : E3 => ‖E x‖) volume c
  have hpt : ∀ y : E3, ENNReal.ofReal (Submission.BoseGases.chiScale ℓ y
        * Submission.BoseGases.chiScale ℓ c * ‖E (c - y)‖)
      ≤ ENNReal.ofReal (Submission.BoseGases.chiSup ^ 2 * ‖E (c - y)‖) := by
    intro y
    refine ENNReal.ofReal_le_ofReal ?_
    have hy := kp_chiScale_le_chiSup ℓ y
    have hc := kp_chiScale_le_chiSup ℓ c
    have hy0 := kp_chiScale_nonneg ℓ y
    have hc0 := kp_chiScale_nonneg ℓ c
    have hE0 : (0 : ℝ) ≤ ‖E (c - y)‖ := norm_nonneg _
    have hsup0 : (0 : ℝ) ≤ Submission.BoseGases.chiSup := le_trans hy0 hy
    calc Submission.BoseGases.chiScale ℓ y * Submission.BoseGases.chiScale ℓ c * ‖E (c - y)‖
        ≤ Submission.BoseGases.chiSup * Submission.BoseGases.chiSup * ‖E (c - y)‖ := by
          refine mul_le_mul_of_nonneg_right ?_ hE0
          exact mul_le_mul hy hc hc0 hsup0
      _ = Submission.BoseGases.chiSup ^ 2 * ‖E (c - y)‖ := by ring
  have hmp : MeasurePreserving (fun y : E3 => c - y) volume volume :=
    Submission.BoseGases.measurePreserving_sub_left c
  have hae' : AEMeasurable (fun y : E3 => ‖E (c - y)‖) volume := by
    have h2 : AEMeasurable (fun x : E3 => ‖E x‖) (volume.map (fun y : E3 => c - y)) := by
      rw [hmp.map_eq]
      exact hE.aemeasurable.norm
    exact AEMeasurable.comp_measurable (f := fun y : E3 => c - y) (g := fun x : E3 => ‖E x‖)
      h2 (by fun_prop)
  have hae : AEMeasurable (fun y : E3 => ENNReal.ofReal ‖E (c - y)‖) volume :=
    ENNReal.measurable_ofReal.comp_aemeasurable hae'
  have hpt2 : ∀ y : E3, ENNReal.ofReal (Submission.BoseGases.chiSup ^ 2 * ‖E (c - y)‖)
      = ENNReal.ofReal (Submission.BoseGases.chiSup ^ 2) * ENNReal.ofReal ‖E (c - y)‖ :=
    fun y => ENNReal.ofReal_mul (sq_nonneg _)
  calc ∫⁻ y : E3, ENNReal.ofReal (Submission.BoseGases.chiScale ℓ y
        * Submission.BoseGases.chiScale ℓ c * ‖E (c - y)‖)
      ≤ ∫⁻ y : E3, ENNReal.ofReal (Submission.BoseGases.chiSup ^ 2 * ‖E (c - y)‖) :=
        lintegral_mono hpt
    _ = ENNReal.ofReal (Submission.BoseGases.chiSup ^ 2)
          * ∫⁻ y : E3, ENNReal.ofReal ‖E (c - y)‖ := by
        rw [← MeasureTheory.lintegral_const_mul'' (ENNReal.ofReal (Submission.BoseGases.chiSup ^ 2)) hae]
        exact MeasureTheory.lintegral_congr_ae (Filter.Eventually.of_forall hpt2)
    _ = ENNReal.ofReal (Submission.BoseGases.chiSup ^ 2)
          * ENNReal.ofReal (∫ x : E3, ‖E x‖) := by
        congr 1
        have h1 : ∫⁻ y : E3, ENNReal.ofReal ‖E (c - y)‖ = ∫⁻ y : E3, ‖E (c - y)‖ₑ := by
          refine MeasureTheory.lintegral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
          show ENNReal.ofReal ‖E (c - y)‖ = ‖E (c - y)‖ₑ
          rw [Real.enorm_eq_ofReal_abs, Real.norm_eq_abs]
        rw [h1, ← MeasureTheory.ofReal_integral_norm_eq_lintegral_enorm (hE.comp_sub_left c)]
        exact congrArg ENNReal.ofReal hshift
    _ = ENNReal.ofReal (Submission.BoseGases.chiSup ^ 2 * ∫ x : E3, ‖E x‖) := by
        rw [ENNReal.ofReal_mul (sq_nonneg _)]


/-! ## 3bis. The lattice-images estimate (proved from scratch here)

The three bricks of `Work.BoseBoxFock.latImagesDefs`' design, proved directly:

* `kp_latImgTsum_le` — the geometric pointwise bound of the lattice series;
* `kp_latImgLin_le` — the measure-theoretic split at `‖v‖ ⋚ ρ`;
* `kp_latImg_lintegral_le` — the Tonelli/translation rewriting;
* `kp_latImages_lintegral_le` — their assembly (with `C = latImgC`).
-/

/-- A nonzero lattice vector has norm at least `1`. -/
theorem kp_intVec_norm_ge_one (m : Fin 3 → ℤ) (hm : m ≠ 0) : (1 : ℝ) ≤ ‖latVec m‖ := by
  obtain ⟨i, hi⟩ : ∃ i, m i ≠ 0 := by
    by_contra h
    push Not at h
    exact hm (funext fun j => h j)
  have h1 : (1 : ℤ) ≤ |m i| := Int.one_le_abs hi
  have h2 : (1 : ℝ) ≤ |((m i : ℤ) : ℝ)| := by exact_mod_cast h1
  have h3 : (latVec m).ofLp i = ((m i : ℤ) : ℝ) := rfl
  have h4 : ‖(latVec m).ofLp i‖ ≤ ‖latVec m‖ := PiLp.norm_apply_le (latVec m) i
  rw [h3, Real.norm_eq_abs] at h4
  linarith

/-- The lattice vector is additive. -/
theorem kp_latVec_sub (m m' : Fin 3 → ℤ) : latVec (m - m') = latVec m - latVec m' := by
  ext i
  simp [latVec, Pi.sub_apply]

/-- **Brick 3 (geometry).**  The lattice series of the two-factor window is bounded by the
flatness constant on the dense region `‖v‖ ≤ ρ` and by the sup bound elsewhere. -/
theorem kp_latImgTsum_le {ℓ ρ : ℝ} (hℓ : 0 < ℓ) (hρ : 0 ≤ ρ) (w v : E3) :
    (∑' m : Fin 3 → ℤ, (if m = 0 then (0 : ℝ≥0∞) else
        ENNReal.ofReal (Submission.BoseGases.chiScale ℓ w *
          Submission.BoseGases.chiScale ℓ (w + ℓ • latVec m - v))))
      ≤ ENNReal.ofReal (if ‖v‖ ≤ ρ then latImgC * (min 1 (ρ / ℓ)) ^ 12
          else latImgC) := by
  classical
  have hχwnn : 0 ≤ Submission.BoseGases.chiScale ℓ w := kp_chiScale_nonneg ℓ w
  have hχnn : ∀ x : E3, 0 ≤ Submission.BoseGases.chiScale ℓ x := kp_chiScale_nonneg ℓ
  have hχsup : ∀ x : E3, Submission.BoseGases.chiScale ℓ x ≤ Submission.BoseGases.chiSupAbs := by
    intro x
    have h := Submission.BoseGases.chiScale_abs_le_sup ℓ x
    rwa [abs_of_nonneg (hχnn x)] at h
  have hne : ∀ x : E3, Submission.BoseGases.chiScale ℓ x ≠ 0 → ‖x‖ < ℓ / 2 := by
    intro x hx
    by_contra hcon
    push Not at hcon
    refine hx ?_
    rw [Submission.BoseGases.chiScale]
    refine Submission.BoseGases.chi_eq_zero_of_half_le_norm _ ?_
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hℓ), ← div_eq_inv_mul,
      le_div_iff₀ hℓ]
    linarith
  -- the sup bound on a pair
  have hsup2 : ∀ y : E3, Submission.BoseGases.chiScale ℓ w * Submission.BoseGases.chiScale ℓ y
      ≤ Submission.BoseGases.chiSupAbs ^ 2 := by
    intro y
    have h1 := hχsup w
    have h2 := hχsup y
    calc Submission.BoseGases.chiScale ℓ w * Submission.BoseGases.chiScale ℓ y
        ≤ Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSupAbs :=
          mul_le_mul h1 h2 (hχnn y) (le_trans (hχnn w) h1)
      _ = Submission.BoseGases.chiSupAbs ^ 2 := by ring
  set b : ℝ≥0∞ := ENNReal.ofReal (if ‖v‖ ≤ ρ then latImgC * (min 1 (ρ / ℓ)) ^ 12
      else latImgC) with hbdef
  have hterm : ∀ m : Fin 3 → ℤ, (if m = 0 then (0 : ℝ≥0∞) else
        ENNReal.ofReal (Submission.BoseGases.chiScale ℓ w *
          Submission.BoseGases.chiScale ℓ (w + ℓ • latVec m - v))) ≤ b := by
    intro m
    by_cases hm : m = 0
    · rw [if_pos hm]; exact zero_le
    · rw [if_neg hm, hbdef]
      refine ENNReal.ofReal_le_ofReal ?_
      by_cases hv : ‖v‖ ≤ ρ
      · rw [if_pos hv]
        by_cases hρℓ : ρ ≤ ℓ
        · rw [min_eq_right ((div_le_one hℓ).mpr hρℓ)]
          have hpair : Submission.BoseGases.chiScale ℓ w *
              Submission.BoseGases.chiScale ℓ (w + ℓ • latVec m - v)
              ≤ chiImgC 12 * (ρ / ℓ) ^ 12 := by
            refine chiScale_pair_image_le hℓ hρ hρℓ 12 ⟨-m, ?_, ?_⟩
            · intro hcon
              exact hm (by simpa using congrArg Neg.neg hcon)
            · rw [show w - (w + ℓ • latVec m - v) - ℓ • latVec (-m) = v by
                rw [kp_latVec_neg, smul_neg]; abel]
              exact hv
          calc Submission.BoseGases.chiScale ℓ w *
                Submission.BoseGases.chiScale ℓ (w + ℓ • latVec m - v)
              ≤ chiImgC 12 * (ρ / ℓ) ^ 12 := hpair
            _ ≤ latImgC * (ρ / ℓ) ^ 12 :=
                mul_le_mul_of_nonneg_right latImgC_ge_flat (by positivity)
        · have h1 : 1 ≤ ρ / ℓ := by
            rw [le_div_iff₀ hℓ, one_mul]
            exact le_of_lt (lt_of_not_ge hρℓ)
          have hmin1 : (min 1 (ρ / ℓ)) ^ 12 = 1 := by rw [min_eq_left h1, one_pow]
          rw [hmin1, mul_one]
          calc Submission.BoseGases.chiScale ℓ w *
                Submission.BoseGases.chiScale ℓ (w + ℓ • latVec m - v)
              ≤ Submission.BoseGases.chiSupAbs ^ 2 := hsup2 _
            _ ≤ latImgC := latImgC_ge_sup
      · rw [if_neg hv]
        calc Submission.BoseGases.chiScale ℓ w *
              Submission.BoseGases.chiScale ℓ (w + ℓ • latVec m - v)
            ≤ Submission.BoseGases.chiSupAbs ^ 2 := hsup2 _
          _ ≤ latImgC := latImgC_ge_sup
  -- uniqueness of the contributing index
  have huniq : ∀ m m' : Fin 3 → ℤ,
      (if m = 0 then (0 : ℝ≥0∞) else
        ENNReal.ofReal (Submission.BoseGases.chiScale ℓ w *
          Submission.BoseGases.chiScale ℓ (w + ℓ • latVec m - v))) ≠ 0 →
      (if m' = 0 then (0 : ℝ≥0∞) else
        ENNReal.ofReal (Submission.BoseGases.chiScale ℓ w *
          Submission.BoseGases.chiScale ℓ (w + ℓ • latVec m' - v))) ≠ 0 → m = m' := by
    intro m m' hm hm'
    have hm0 : m ≠ 0 := by rintro rfl; exact hm (if_pos rfl)
    have hm0' : m' ≠ 0 := by rintro rfl; exact hm' (if_pos rfl)
    rw [if_neg hm0] at hm
    rw [if_neg hm0'] at hm'
    have hwm : Submission.BoseGases.chiScale ℓ w ≠ 0 := by
      intro h0
      rw [h0, zero_mul, ENNReal.ofReal_zero] at hm
      exact hm rfl
    have hym : Submission.BoseGases.chiScale ℓ (w + ℓ • latVec m - v) ≠ 0 := by
      intro h0
      rw [h0, mul_zero, ENNReal.ofReal_zero] at hm
      exact hm rfl
    have hwm' : Submission.BoseGases.chiScale ℓ w ≠ 0 := by
      intro h0
      rw [h0, zero_mul, ENNReal.ofReal_zero] at hm'
      exact hm' rfl
    have hym' : Submission.BoseGases.chiScale ℓ (w + ℓ • latVec m' - v) ≠ 0 := by
      intro h0
      rw [h0, mul_zero, ENNReal.ofReal_zero] at hm'
      exact hm' rfl
    have h2 : ‖w + ℓ • latVec m - v‖ < ℓ / 2 := hne _ hym
    have h2' : ‖w + ℓ • latVec m' - v‖ < ℓ / 2 := hne _ hym'
    have hkey : ℓ * ‖latVec (m - m')‖ < ℓ := by
      have hsub : (w + ℓ • latVec m - v) - (w + ℓ • latVec m' - v) = ℓ • latVec (m - m') := by
        rw [kp_latVec_sub, smul_sub]; abel
      calc ℓ * ‖latVec (m - m')‖ = ‖ℓ • latVec (m - m')‖ := by
            rw [norm_smul, Real.norm_eq_abs, abs_of_pos hℓ]
        _ = ‖(w + ℓ • latVec m - v) - (w + ℓ • latVec m' - v)‖ := by rw [hsub]
        _ ≤ ‖w + ℓ • latVec m - v‖ + ‖w + ℓ • latVec m' - v‖ := norm_sub_le _ _
        _ < ℓ := by linarith
    have hlt : ‖latVec (m - m')‖ < 1 := by
      have hh : ℓ * ‖latVec (m - m')‖ < ℓ * 1 := by simpa using hkey
      have h2 : ℓ * ‖latVec (m - m')‖ / ℓ < (ℓ * 1) / ℓ := div_lt_div_of_pos_right hh hℓ
      rwa [mul_div_cancel_left₀ _ hℓ.ne', mul_div_cancel_left₀ _ hℓ.ne'] at h2
    by_contra hcon
    have hge := kp_intVec_norm_ge_one (m - m') (sub_ne_zero.mpr hcon)
    linarith
  have hfin : ∀ S : Finset (Fin 3 → ℤ),
      ∑ m ∈ S, (if m = 0 then (0 : ℝ≥0∞) else
        ENNReal.ofReal (Submission.BoseGases.chiScale ℓ w *
          Submission.BoseGases.chiScale ℓ (w + ℓ • latVec m - v))) ≤ b := by
    intro S
    by_cases h : ∃ m ∈ S, (if m = 0 then (0 : ℝ≥0∞) else
        ENNReal.ofReal (Submission.BoseGases.chiScale ℓ w *
          Submission.BoseGases.chiScale ℓ (w + ℓ • latVec m - v))) ≠ 0
    · obtain ⟨m₀, hm₀S, hm₀⟩ := h
      rw [Finset.sum_eq_single m₀
        (fun b' hb' hb'm => by
          by_contra hb'0
          exact hb'm (huniq b' m₀ hb'0 hm₀))
        (fun hnot => absurd hm₀S hnot)]
      exact hterm m₀
    · have hz : ∑ m ∈ S, (if m = 0 then (0 : ℝ≥0∞) else
          ENNReal.ofReal (Submission.BoseGases.chiScale ℓ w *
            Submission.BoseGases.chiScale ℓ (w + ℓ • latVec m - v))) = 0 :=
        Finset.sum_eq_zero (fun m hmS => by
          by_contra hne'
          exact h ⟨m, hmS, hne'⟩)
      rw [hz]; exact zero_le
  rw [ENNReal.tsum_eq_iSup_sum]
  exact iSup_le (fun S => (hfin S).trans (le_of_eq hbdef))

/-- **Brick 1 (measure theory).**  A `v`-pointwise majorant by the two-level constant
`latImgC (min 1 (ρ/ℓ))^12` / `latImgC` integrates to the stated bound. -/
theorem kp_latImgLin_le {ℓ ρ : ℝ} (hℓ : 0 < ℓ) (hρ : 0 ≤ ρ) {U : E3 → ℝ}
    (hU : MeasureTheory.Integrable U) {G : E3 → ℝ≥0∞}
    (hG : ∀ v, G v ≤ ENNReal.ofReal (if ‖v‖ ≤ ρ then latImgC * (min 1 (ρ / ℓ)) ^ 12
        else latImgC)) :
    ∫⁻ v : E3, G v * ENNReal.ofReal (‖U v‖)
      ≤ ENNReal.ofReal (latImgC * (min 1 (ρ / ℓ)) ^ 12 * (∫ u : E3, ‖U u‖)
          + latImgC * (∫ u in {u : E3 | ρ ≤ ‖u‖}, ‖U u‖)) := by
  set c : ℝ := latImgC * (min 1 (ρ / ℓ)) ^ 12 with hcdef
  have hmin0 : 0 ≤ min 1 (ρ / ℓ) := le_min zero_le_one (div_nonneg hρ hℓ.le)
  have hc0 : 0 ≤ c := mul_nonneg latImgC_nonneg (pow_nonneg hmin0 12)
  have hsmeas : MeasurableSet {v : E3 | ρ ≤ ‖v‖} :=
    (isClosed_le continuous_const continuous_norm).measurableSet
  have hgle : ∀ v : E3, (if ‖v‖ ≤ ρ then latImgC * (min 1 (ρ / ℓ)) ^ 12 else latImgC)
      ≤ c + latImgC * (if ρ ≤ ‖v‖ then (1 : ℝ) else 0) := by
    intro v
    by_cases hv : ‖v‖ ≤ ρ
    · rw [if_pos hv]
      have h2 : 0 ≤ latImgC * (if ρ ≤ ‖v‖ then (1 : ℝ) else 0) := by
        by_cases h : ρ ≤ ‖v‖
        · rw [if_pos h, mul_one]; exact latImgC_nonneg
        · rw [if_neg h, mul_zero]
      linarith
    · rw [if_neg hv, if_pos (le_of_lt (lt_of_not_ge hv)), mul_one]
      linarith
  have hifnn : ∀ v : E3, 0 ≤ (if ‖v‖ ≤ ρ then latImgC * (min 1 (ρ / ℓ)) ^ 12
      else latImgC) := by
    intro v
    by_cases hv : ‖v‖ ≤ ρ
    · rw [if_pos hv]; exact mul_nonneg latImgC_nonneg (pow_nonneg hmin0 12)
    · rw [if_neg hv]; exact latImgC_nonneg
  have hpt : ∀ v : E3, G v * ENNReal.ofReal (‖U v‖)
      ≤ ENNReal.ofReal (c * ‖U v‖ + latImgC * (if ρ ≤ ‖v‖ then ‖U v‖ else 0)) := by
    intro v
    have hUv : 0 ≤ ‖U v‖ := norm_nonneg _
    calc G v * ENNReal.ofReal (‖U v‖)
        ≤ ENNReal.ofReal (if ‖v‖ ≤ ρ then latImgC * (min 1 (ρ / ℓ)) ^ 12 else latImgC)
            * ENNReal.ofReal (‖U v‖) := mul_le_mul_of_nonneg_right (hG v) zero_le
      _ = ENNReal.ofReal ((if ‖v‖ ≤ ρ then latImgC * (min 1 (ρ / ℓ)) ^ 12 else latImgC)
            * ‖U v‖) := (ENNReal.ofReal_mul (hifnn v)).symm
      _ ≤ ENNReal.ofReal (c * ‖U v‖ + latImgC * (if ρ ≤ ‖v‖ then ‖U v‖ else 0)) := by
          refine ENNReal.ofReal_le_ofReal ?_
          calc (if ‖v‖ ≤ ρ then latImgC * (min 1 (ρ / ℓ)) ^ 12 else latImgC) * ‖U v‖
              ≤ (c + latImgC * (if ρ ≤ ‖v‖ then (1 : ℝ) else 0)) * ‖U v‖ :=
                mul_le_mul_of_nonneg_right (hgle v) hUv
            _ = c * ‖U v‖ + latImgC * (if ρ ≤ ‖v‖ then ‖U v‖ else 0) := by
                by_cases h : ρ ≤ ‖v‖
                · simp only [if_pos h, mul_one, add_mul]
                · simp only [if_neg h, mul_zero, add_zero]
  have hif_eq : (fun v : E3 => (if ρ ≤ ‖v‖ then ‖U v‖ else 0))
      = {v : E3 | ρ ≤ ‖v‖}.indicator (fun v => ‖U v‖) := by
    funext v
    rw [Set.indicator_apply]
    simp only [Set.mem_setOf_eq]
  have hg2 : MeasureTheory.Integrable
      (fun v : E3 => latImgC * (if ρ ≤ ‖v‖ then ‖U v‖ else 0)) := by
    have h2 : MeasureTheory.Integrable
        ({v : E3 | ρ ≤ ‖v‖}.indicator (fun v => ‖U v‖)) := hU.norm.indicator hsmeas
    refine (h2.const_mul latImgC).congr ?_
    filter_upwards with v
    rw [show (if ρ ≤ ‖v‖ then ‖U v‖ else 0)
        = ({v : E3 | ρ ≤ ‖v‖}.indicator (fun v => ‖U v‖)) v by
      rw [Set.indicator_apply]; simp only [Set.mem_setOf_eq]]
  have hgint : MeasureTheory.Integrable
      (fun v : E3 => c * ‖U v‖ + latImgC * (if ρ ≤ ‖v‖ then ‖U v‖ else 0)) :=
    (hU.norm.const_mul c).add hg2
  have hgnn : ∀ v : E3, 0 ≤ c * ‖U v‖ + latImgC * (if ρ ≤ ‖v‖ then ‖U v‖ else 0) := by
    intro v
    refine add_nonneg (mul_nonneg hc0 (norm_nonneg _)) ?_
    by_cases h : ρ ≤ ‖v‖
    · rw [if_pos h]; exact mul_nonneg latImgC_nonneg (norm_nonneg _)
    · rw [if_neg h, mul_zero]
  have hsplit : ∫ v : E3, (c * ‖U v‖ + latImgC * (if ρ ≤ ‖v‖ then ‖U v‖ else 0))
      = c * (∫ u : E3, ‖U u‖) + latImgC * (∫ u in {u : E3 | ρ ≤ ‖u‖}, ‖U u‖) := by
    have hif : (∫ v : E3, (if ρ ≤ ‖v‖ then ‖U v‖ else 0))
        = ∫ v in {v : E3 | ρ ≤ ‖v‖}, ‖U v‖ := by
      rw [hif_eq, MeasureTheory.integral_indicator hsmeas]
    rw [MeasureTheory.integral_add (f := fun v : E3 => c * ‖U v‖)
        (g := fun v : E3 => latImgC * (if ρ ≤ ‖v‖ then ‖U v‖ else 0))
        (hU.norm.const_mul c) hg2,
      MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul, hif]
  calc ∫⁻ v : E3, G v * ENNReal.ofReal (‖U v‖)
      ≤ ∫⁻ v : E3, ENNReal.ofReal (c * ‖U v‖ + latImgC * (if ρ ≤ ‖v‖ then ‖U v‖ else 0)) :=
        lintegral_mono hpt
    _ = ENNReal.ofReal (∫ v : E3, (c * ‖U v‖ + latImgC * (if ρ ≤ ‖v‖ then ‖U v‖ else 0))) :=
        (MeasureTheory.ofReal_integral_eq_lintegral_ofReal hgint
          (Filter.Eventually.of_forall hgnn)).symm
    _ = ENNReal.ofReal (c * (∫ u : E3, ‖U u‖)
          + latImgC * (∫ u in {u : E3 | ρ ≤ ‖u‖}, ‖U u‖)) := by rw [hsplit]
    _ = ENNReal.ofReal (latImgC * (min 1 (ρ / ℓ)) ^ 12 * (∫ u : E3, ‖U u‖)
          + latImgC * (∫ u in {u : E3 | ρ ≤ ‖u‖}, ‖U u‖)) := by rw [hcdef]

/-- **Brick 2 (Tonelli + translation).**  The `z`-integral of the lattice series is the
`v`-integral of the reflected lattice series against `‖U v‖`. -/
theorem kp_latImg_lintegral_le {ℓ : ℝ} (hℓ : 0 < ℓ) {U : E3 → ℝ}
    (hU : MeasureTheory.AEStronglyMeasurable U (volume : Measure E3)) (w : E3) :
    ∫⁻ z : E3, ENNReal.ofReal (Submission.BoseGases.chiScale ℓ w *
        Submission.BoseGases.chiScale ℓ z *
        (∑' m : Fin 3 → ℤ, (if m = 0 then (0 : ℝ)
          else ‖U (w - z + ℓ • latVec m)‖)))
      ≤ ∫⁻ v : E3,
          (∑' m : Fin 3 → ℤ, (if m = 0 then (0 : ℝ≥0∞) else
            ENNReal.ofReal (Submission.BoseGases.chiScale ℓ w *
              Submission.BoseGases.chiScale ℓ (w + ℓ • latVec m - v))))
          * ENNReal.ofReal (‖U v‖) := by
  have hχwnn : 0 ≤ Submission.BoseGases.chiScale ℓ w := kp_chiScale_nonneg ℓ w
  have hχnn : ∀ x : E3, 0 ≤ Submission.BoseGases.chiScale ℓ x := kp_chiScale_nonneg ℓ
  have hb_nn : ∀ (m : Fin 3 → ℤ) (z : E3),
      0 ≤ (if m = 0 then (0 : ℝ) else ‖U (w - z + ℓ • latVec m)‖) := by
    intro m z
    by_cases hm : m = 0
    · rw [if_pos hm]
    · rw [if_neg hm]; exact norm_nonneg _
  have hA : ∀ z : E3, ENNReal.ofReal (Submission.BoseGases.chiScale ℓ w *
        Submission.BoseGases.chiScale ℓ z *
        (∑' m : Fin 3 → ℤ, (if m = 0 then (0 : ℝ) else ‖U (w - z + ℓ • latVec m)‖)))
      ≤ ∑' m : Fin 3 → ℤ, ENNReal.ofReal (Submission.BoseGases.chiScale ℓ w *
          Submission.BoseGases.chiScale ℓ z *
          (if m = 0 then (0 : ℝ) else ‖U (w - z + ℓ • latVec m)‖)) := by
    intro z
    by_cases hsum : Summable (fun m : Fin 3 → ℤ =>
        (if m = 0 then (0 : ℝ) else ‖U (w - z + ℓ • latVec m)‖))
    · calc ENNReal.ofReal (Submission.BoseGases.chiScale ℓ w *
              Submission.BoseGases.chiScale ℓ z *
              (∑' m : Fin 3 → ℤ, (if m = 0 then (0 : ℝ) else ‖U (w - z + ℓ • latVec m)‖)))
          = ENNReal.ofReal (Submission.BoseGases.chiScale ℓ w *
                Submission.BoseGases.chiScale ℓ z)
              * ENNReal.ofReal (∑' m : Fin 3 → ℤ,
                  (if m = 0 then (0 : ℝ) else ‖U (w - z + ℓ • latVec m)‖)) :=
            ENNReal.ofReal_mul (mul_nonneg hχwnn (hχnn z))
        _ = ENNReal.ofReal (Submission.BoseGases.chiScale ℓ w *
                Submission.BoseGases.chiScale ℓ z)
              * ∑' m : Fin 3 → ℤ, ENNReal.ofReal
                  ((if m = 0 then (0 : ℝ) else ‖U (w - z + ℓ • latVec m)‖)) := by
            rw [ENNReal.ofReal_tsum_of_nonneg (fun m => hb_nn m z) hsum]
        _ = ∑' m : Fin 3 → ℤ, ENNReal.ofReal
                (Submission.BoseGases.chiScale ℓ w * Submission.BoseGases.chiScale ℓ z)
              * ENNReal.ofReal
                  ((if m = 0 then (0 : ℝ) else ‖U (w - z + ℓ • latVec m)‖)) :=
            (ENNReal.tsum_mul_left).symm
        _ ≤ ∑' m : Fin 3 → ℤ, ENNReal.ofReal (Submission.BoseGases.chiScale ℓ w *
              Submission.BoseGases.chiScale ℓ z *
              (if m = 0 then (0 : ℝ) else ‖U (w - z + ℓ • latVec m)‖)) :=
            le_of_eq (by
              refine tsum_congr fun m => ?_
              exact (ENNReal.ofReal_mul (mul_nonneg hχwnn (hχnn z))).symm)
    · rw [tsum_eq_zero_of_not_summable hsum, mul_zero, ENNReal.ofReal_zero]
      exact zero_le
  have hFmeas : ∀ m : Fin 3 → ℤ, AEMeasurable (fun z : E3 => ENNReal.ofReal (
        Submission.BoseGases.chiScale ℓ w * Submission.BoseGases.chiScale ℓ z *
        (if m = 0 then (0 : ℝ) else ‖U (w - z + ℓ • latVec m)‖))) volume := by
    intro m
    by_cases hm : m = 0
    · have hfun : (fun z : E3 => ENNReal.ofReal (
          Submission.BoseGases.chiScale ℓ w * Submission.BoseGases.chiScale ℓ z *
          (if m = 0 then (0 : ℝ) else ‖U (w - z + ℓ • latVec m)‖)))
          = fun _ : E3 => (0 : ℝ≥0∞) := by
        funext z
        rw [if_pos hm, mul_zero, ENNReal.ofReal_zero]
      rw [hfun]
      exact aemeasurable_const
    · have hfun : (fun z : E3 => ENNReal.ofReal (
          Submission.BoseGases.chiScale ℓ w * Submission.BoseGases.chiScale ℓ z *
          (if m = 0 then (0 : ℝ) else ‖U (w - z + ℓ • latVec m)‖)))
          = fun z : E3 => ENNReal.ofReal (Submission.BoseGases.chiScale ℓ w *
              Submission.BoseGases.chiScale ℓ z * ‖U (w - z + ℓ • latVec m)‖) := by
        funext z
        rw [if_neg hm]
      rw [hfun]
      have hUm : AEMeasurable (fun z : E3 => ‖U (w - z + ℓ • latVec m)‖) volume := by
        have hmp := Submission.BoseGases.measurePreserving_sub_left (w + ℓ • latVec m)
        have h1 : AEMeasurable (fun z : E3 => U ((w + ℓ • latVec m) - z)) volume :=
          hU.aemeasurable.comp_quasiMeasurePreserving hmp.quasiMeasurePreserving
        have h2 : (fun z : E3 => ‖U (w - z + ℓ • latVec m)‖)
            = fun z : E3 => ‖U ((w + ℓ • latVec m) - z)‖ := by
          funext z
          rw [show w - z + ℓ • latVec m = (w + ℓ • latVec m) - z by abel]
        rw [h2]
        exact h1.norm
      exact ENNReal.measurable_ofReal.comp_aemeasurable
        ((aemeasurable_const.mul (kp_chiScale_continuous ℓ).aemeasurable).mul hUm)
  have hGmeas : ∀ m : Fin 3 → ℤ, AEMeasurable (fun v : E3 =>
      (if m = 0 then (0 : ℝ≥0∞) else ENNReal.ofReal (Submission.BoseGases.chiScale ℓ w *
        Submission.BoseGases.chiScale ℓ (w + ℓ • latVec m - v)))
        * ENNReal.ofReal (‖U v‖)) volume := by
    intro m
    by_cases hm : m = 0
    · have hfun : (fun v : E3 =>
          (if m = 0 then (0 : ℝ≥0∞) else ENNReal.ofReal (Submission.BoseGases.chiScale ℓ w *
            Submission.BoseGases.chiScale ℓ (w + ℓ • latVec m - v)))
            * ENNReal.ofReal (‖U v‖)) = fun _ : E3 => (0 : ℝ≥0∞) := by
        funext v
        rw [if_pos hm, zero_mul]
      rw [hfun]
      exact aemeasurable_const
    · have hfun : (fun v : E3 =>
          (if m = 0 then (0 : ℝ≥0∞) else ENNReal.ofReal (Submission.BoseGases.chiScale ℓ w *
            Submission.BoseGases.chiScale ℓ (w + ℓ • latVec m - v)))
            * ENNReal.ofReal (‖U v‖)) = fun v : E3 =>
          ENNReal.ofReal (Submission.BoseGases.chiScale ℓ w *
            Submission.BoseGases.chiScale ℓ (w + ℓ • latVec m - v))
          * ENNReal.ofReal (‖U v‖) := by
        funext v
        rw [if_neg hm]
      rw [hfun]
      have h1 : AEMeasurable (fun v : E3 => ENNReal.ofReal (Submission.BoseGases.chiScale ℓ w *
          Submission.BoseGases.chiScale ℓ (w + ℓ • latVec m - v))) volume :=
        ENNReal.measurable_ofReal.comp_aemeasurable
          (aemeasurable_const.mul ((kp_chiScale_continuous ℓ).comp (by fun_prop)).aemeasurable)
      have h2 : AEMeasurable (fun v : E3 => ENNReal.ofReal (‖U v‖)) volume :=
        ENNReal.measurable_ofReal.comp_aemeasurable hU.aemeasurable.norm
      exact h1.mul h2
  have hstep1 : (∫⁻ z : E3, ENNReal.ofReal (Submission.BoseGases.chiScale ℓ w *
        Submission.BoseGases.chiScale ℓ z *
        (∑' m : Fin 3 → ℤ, (if m = 0 then (0 : ℝ) else ‖U (w - z + ℓ • latVec m)‖))))
      ≤ ∑' m : Fin 3 → ℤ, ∫⁻ z : E3, ENNReal.ofReal (Submission.BoseGases.chiScale ℓ w *
          Submission.BoseGases.chiScale ℓ z *
          (if m = 0 then (0 : ℝ) else ‖U (w - z + ℓ • latVec m)‖)) :=
    (lintegral_mono hA).trans (le_of_eq (MeasureTheory.lintegral_tsum hFmeas))
  have hterm : ∀ m : Fin 3 → ℤ,
      ∫⁻ z : E3, ENNReal.ofReal (Submission.BoseGases.chiScale ℓ w *
          Submission.BoseGases.chiScale ℓ z *
          (if m = 0 then (0 : ℝ) else ‖U (w - z + ℓ • latVec m)‖))
        = ∫⁻ v : E3, (if m = 0 then (0 : ℝ≥0∞) else ENNReal.ofReal (
            Submission.BoseGases.chiScale ℓ w *
            Submission.BoseGases.chiScale ℓ (w + ℓ • latVec m - v)))
          * ENNReal.ofReal (‖U v‖) := by
    intro m
    by_cases hm : m = 0
    · have hL : (fun z : E3 => ENNReal.ofReal (Submission.BoseGases.chiScale ℓ w *
          Submission.BoseGases.chiScale ℓ z *
          (if m = 0 then (0 : ℝ) else ‖U (w - z + ℓ • latVec m)‖)))
          = fun _ : E3 => (0 : ℝ≥0∞) := by
        funext z
        rw [if_pos hm, mul_zero, ENNReal.ofReal_zero]
      have hR : (fun v : E3 => (if m = 0 then (0 : ℝ≥0∞) else ENNReal.ofReal (
            Submission.BoseGases.chiScale ℓ w *
            Submission.BoseGases.chiScale ℓ (w + ℓ • latVec m - v)))
          * ENNReal.ofReal (‖U v‖)) = fun _ : E3 => (0 : ℝ≥0∞) := by
        funext v
        rw [if_pos hm, zero_mul]
      rw [hL, hR]
    · have hL : (fun z : E3 => ENNReal.ofReal (Submission.BoseGases.chiScale ℓ w *
          Submission.BoseGases.chiScale ℓ z *
          (if m = 0 then (0 : ℝ) else ‖U (w - z + ℓ • latVec m)‖)))
          = fun z : E3 => ENNReal.ofReal (Submission.BoseGases.chiScale ℓ w *
              Submission.BoseGases.chiScale ℓ z * ‖U (w - z + ℓ • latVec m)‖) := by
        funext z
        rw [if_neg hm]
      have hR : (fun v : E3 => (if m = 0 then (0 : ℝ≥0∞) else ENNReal.ofReal (
            Submission.BoseGases.chiScale ℓ w *
            Submission.BoseGases.chiScale ℓ (w + ℓ • latVec m - v)))
          * ENNReal.ofReal (‖U v‖)) = fun v : E3 =>
          ENNReal.ofReal (Submission.BoseGases.chiScale ℓ w *
              Submission.BoseGases.chiScale ℓ (w + ℓ • latVec m - v))
            * ENNReal.ofReal (‖U v‖) := by
        funext v
        rw [if_neg hm]
      rw [hL, hR]
      have e0 : (fun z : E3 => ENNReal.ofReal (Submission.BoseGases.chiScale ℓ w *
            Submission.BoseGases.chiScale ℓ z * ‖U (w - z + ℓ • latVec m)‖))
          = fun z : E3 => ENNReal.ofReal (Submission.BoseGases.chiScale ℓ w *
            Submission.BoseGases.chiScale ℓ z * ‖U ((w + ℓ • latVec m) - z)‖) := by
        funext z
        rw [show w - z + ℓ • latVec m = (w + ℓ • latVec m) - z by abel]
      set H : E3 → ℝ≥0∞ := fun y : E3 => ENNReal.ofReal (Submission.BoseGases.chiScale ℓ w *
        Submission.BoseGases.chiScale ℓ ((w + ℓ • latVec m) - y) * ‖U y‖) with hHdef
      have hstep_a : (fun z : E3 => ENNReal.ofReal (Submission.BoseGases.chiScale ℓ w *
            Submission.BoseGases.chiScale ℓ z * ‖U ((w + ℓ • latVec m) - z)‖))
          = fun z : E3 => H ((w + ℓ • latVec m) - z) := by
        funext z
        simp only [hHdef, sub_sub_self]
      have hstep_b : (fun z : E3 => H ((w + ℓ • latVec m) - z))
          = fun z : E3 => H (-(z - (w + ℓ • latVec m))) := by
        funext z
        exact congrArg H (neg_sub z (w + ℓ • latVec m)).symm
      have hstep_c : (∫⁻ z : E3, H (-(z - (w + ℓ • latVec m))))
          = ∫⁻ z : E3, H (-z) := by
        rw [show (fun z : E3 => H (-(z - (w + ℓ • latVec m))))
            = fun z : E3 => (fun y : E3 => H (-y)) (z + (-(w + ℓ • latVec m))) from rfl,
          MeasureTheory.lintegral_add_right_eq_self (fun y : E3 => H (-y))
            (-(w + ℓ • latVec m))]
      have hsub : (∫⁻ z : E3, ENNReal.ofReal (Submission.BoseGases.chiScale ℓ w *
            Submission.BoseGases.chiScale ℓ z * ‖U ((w + ℓ • latVec m) - z)‖))
          = ∫⁻ y : E3, H y :=
        (congrArg (fun f : E3 → ℝ≥0∞ => ∫⁻ z : E3, f z) (hstep_a.trans hstep_b)).trans
          (hstep_c.trans (MeasureTheory.lintegral_neg_eq_self H))
      rw [e0, hsub]
      refine lintegral_congr fun v => ?_
      show ENNReal.ofReal (Submission.BoseGases.chiScale ℓ w *
          Submission.BoseGases.chiScale ℓ (w + ℓ • latVec m - v) * ‖U v‖)
        = ENNReal.ofReal (Submission.BoseGases.chiScale ℓ w *
            Submission.BoseGases.chiScale ℓ (w + ℓ • latVec m - v)) * ENNReal.ofReal ‖U v‖
      rw [ENNReal.ofReal_mul (mul_nonneg hχwnn (hχnn _))]
  have hstep2 : (∑' m : Fin 3 → ℤ, ∫⁻ z : E3, ENNReal.ofReal (Submission.BoseGases.chiScale ℓ w *
          Submission.BoseGases.chiScale ℓ z *
          (if m = 0 then (0 : ℝ) else ‖U (w - z + ℓ • latVec m)‖)))
      = ∫⁻ v : E3,
          (∑' m : Fin 3 → ℤ, (if m = 0 then (0 : ℝ≥0∞) else
            ENNReal.ofReal (Submission.BoseGases.chiScale ℓ w *
              Submission.BoseGases.chiScale ℓ (w + ℓ • latVec m - v))))
          * ENNReal.ofReal (‖U v‖) := by
    rw [tsum_congr fun m => hterm m]
    rw [show (∑' m : Fin 3 → ℤ, ∫⁻ v : E3, (if m = 0 then (0 : ℝ≥0∞) else
          ENNReal.ofReal (Submission.BoseGases.chiScale ℓ w *
            Submission.BoseGases.chiScale ℓ (w + ℓ • latVec m - v)))
          * ENNReal.ofReal (‖U v‖))
        = ∫⁻ v : E3, ∑' m : Fin 3 → ℤ, (if m = 0 then (0 : ℝ≥0∞) else
          ENNReal.ofReal (Submission.BoseGases.chiScale ℓ w *
            Submission.BoseGases.chiScale ℓ (w + ℓ • latVec m - v)))
          * ENNReal.ofReal (‖U v‖) from (MeasureTheory.lintegral_tsum hGmeas).symm]
    refine lintegral_congr fun v => ?_
    exact ENNReal.tsum_mul_right
  exact hstep1.trans (le_of_eq hstep2)

/-- **The lattice-images estimate.**  The `χ`-weighted `L¹`-bound for the lattice images of an
integrable potential `U`, with the universal constant `latImgC`. -/
theorem kp_latImages_lintegral_le :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {ℓ ρ : ℝ}, 0 < ℓ → 0 ≤ ρ →
      ∀ {U : E3 → ℝ}, MeasureTheory.Integrable U → ∀ w : E3,
        ∫⁻ z : E3, ENNReal.ofReal (Submission.BoseGases.chiScale ℓ w *
            Submission.BoseGases.chiScale ℓ z *
            (∑' m : Fin 3 → ℤ, (if m = 0 then (0 : ℝ)
              else ‖U (w - z + ℓ • latVec m)‖)))
          ≤ ENNReal.ofReal (C * (ρ / ℓ) ^ 12 * (∫ u : E3, ‖U u‖)
              + C * (∫ u in {u : E3 | ρ ≤ ‖u‖}, ‖U u‖)) := by
  refine ⟨latImgC, latImgC_nonneg, ?_⟩
  intro ℓ ρ hℓ hρ U hU w
  have h1 := kp_latImg_lintegral_le (U := U) hℓ hU.aestronglyMeasurable w
  have h2 := kp_latImgLin_le (U := U) hℓ hρ hU
    (G := fun v : E3 => ∑' m : Fin 3 → ℤ, (if m = 0 then (0 : ℝ≥0∞) else
      ENNReal.ofReal (Submission.BoseGases.chiScale ℓ w *
        Submission.BoseGases.chiScale ℓ (w + ℓ • latVec m - v))))
    (fun v => kp_latImgTsum_le hℓ hρ w v)
  refine (h1.trans h2).trans (ENNReal.ofReal_le_ofReal ?_)
  have hmin : (min 1 (ρ / ℓ)) ^ 12 ≤ (ρ / ℓ) ^ 12 :=
    pow_le_pow_left₀ (le_min zero_le_one (div_nonneg hρ hℓ.le)) (min_le_right 1 (ρ / ℓ)) 12
  have hI : 0 ≤ ∫ u : E3, ‖U u‖ := integral_nonneg fun u => norm_nonneg _
  have h4 : latImgC * (min 1 (ρ / ℓ)) ^ 12 * (∫ u : E3, ‖U u‖)
      ≤ latImgC * (ρ / ℓ) ^ 12 * (∫ u : E3, ‖U u‖) :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hmin latImgC_nonneg) hI
  exact add_le_add h4 le_rfl




theorem chCslot_kernelPair (v : EuclideanSpace ℝ (Fin 3) → ℝ) (h : Work.UBB.ScatSol v)
    (hv : 0 ≤ v) (hv1 : MeasureTheory.MemLp v 1) (hvrad : _root_.BoseGases.IsRadial v)
    {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    (hav : 0 < _root_.BoseGases.a v) (fu : Work.BoseBoxFix.LowCut) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {μ : ℝ}, 0 < μ →
      R ≤ Work.BoseBoxFock.ellH v μ * Submission.BoseGases.chiR0 →
      2 * R ≤ Work.BoseBoxFock.ellH v μ → ∀ η : ℝ, 0 < η →
      ∃ T : ℕ, ∀ {N : ℕ}, T ≤ N →
        Work.BoseBoxFock.PCFU.ChKerPair v h μ fu N
          (η * Work.BoseBoxFock.ellH v μ ^ 3
            + C * Work.BoseBoxFock.ellH v μ ^ 3
                * (R / Work.BoseBoxFock.ellH v μ) ^ 12) := by

  classical
  -- ### the two delegated inputs
  obtain ⟨Cimg, hCimgnn, himg⟩ := kp_latImages_lintegral_le
  obtain ⟨CL1, hCL1nn, hL1⟩ := Work.BoseBoxFock.uvSmear_L1_le fu
  -- ### the fixed mass of `g₀`
  set G : ℝ := ∫ x : E3, |Submission.BoseGases.g0 v h x| with hGdef
  have hGnn : 0 ≤ G := integral_nonneg (fun x => abs_nonneg _)
  refine ⟨Cimg * (CL1 * (2 * G) + 1) + Submission.BoseGases.chiSup ^ 2, by positivity, ?_⟩
  intro μ hμ hRℓ h2R η hη
  -- ### notation
  set ℓ : ℝ := Work.BoseBoxFock.ellH v μ with hℓdef
  have hℓ : 0 < ℓ := by rw [hℓdef]; exact Work.BoseBoxFock.ellH_pos v μ
  have hside0 : 0 < Work.BoseBox.sideAt μ (BoseGases.a v) := Work.BoseBox.sideAt_pos hμ hav
  -- ### the kernel `W₁` (both spellings)
  have hW1int_e : MeasureTheory.Integrable
      (Work.BoseFixR.W1fun v h (Work.BoseBoxFock.ellH v μ)) := by
    rw [← hℓdef]; exact Submission.BoseGases.wScaled_g0_integrable hR hv_supp h hℓ hRℓ
  have hW1cs_e : HasCompactSupport (Work.BoseFixR.W1fun v h (Work.BoseBoxFock.ellH v μ)) := by
    rw [← hℓdef]; exact kp_hasCompactSupport_W1 hv_supp ℓ
  have hW1even_e : ∀ x : E3,
      Work.BoseFixR.W1fun v h (Work.BoseBoxFock.ellH v μ) (-x)
        = Work.BoseFixR.W1fun v h (Work.BoseBoxFock.ellH v μ) x := by
    intro x; rw [← hℓdef]; exact Work.BoseFixR.isEven_W1fun h hvrad ℓ x
  set W1 : E3 → ℝ := Work.BoseFixR.W1fun v h ℓ with hW1def
  have hW1int : MeasureTheory.Integrable W1 := by rw [hW1def]; exact hW1int_e
  have hW1even : ∀ x : E3, W1 (-x) = W1 x := by
    intro x; rw [hW1def]; exact hW1even_e x
  have hW1mass : ∫ x : E3, ‖W1 x‖ ≤ 2 * G := by
    have h0 := Work.BoseBoxFock.PCFU.W1fun_integral_abs_uniform (v := v) (h := h) hR hv_supp hℓ hRℓ
    rw [hGdef, hW1def]
    simpa only [Real.norm_eq_abs] using h0
  -- ### the UV threshold
  have hεpos : 0 < (R / ℓ) ^ 12 := by positivity
  obtain ⟨Λ₀, hΛ₀⟩ : ∃ Λ₀ : ℝ, ∀ Λ : ℝ, Λ₀ ≤ Λ →
      ∫ x : E3, ‖Work.BoseBoxFock.uvSmear fu Λ W1 x - W1 x‖ ≤ (R / ℓ) ^ 12 := by
    have hlim : Filter.Tendsto
        (fun Λ : ℝ => ∫ x : E3, ‖Work.BoseBoxFock.uvSmear fu Λ W1 x - W1 x‖)
        Filter.atTop (nhds 0) := by
      rw [hW1def, hℓdef]
      simpa only [Work.BoseBoxFock.uvSmear, Work.BoseBoxFock.uvKernel] using
        (Work.BoseBoxFock.uvSmear_L1_tendsto fu hW1int_e)
    have hev0 : ∀ᶠ y in nhds (0 : ℝ), y ≤ (R / ℓ) ^ 12 := by
      refine Filter.mem_of_superset (Metric.ball_mem_nhds (0 : ℝ) hεpos) ?_
      intro y hy
      rw [Metric.mem_ball, Real.dist_eq, sub_zero] at hy
      exact le_of_lt (lt_of_le_of_lt (le_abs_self y) hy)
    exact Filter.eventually_atTop.mp (hlim.eventually hev0)
  refine ⟨max 1 (Nat.ceil (2 * ℓ * Λ₀ / Real.pi)), ?_⟩
  intro N hN
  have hN1 : 1 ≤ N := le_trans (le_max_left _ _) hN
  have hΛN : Λ₀ ≤ Work.BoseBoxFock.uvRad ℓ N := by
    have hceil : 2 * ℓ * Λ₀ / Real.pi ≤ (N : ℝ) := by
      have h1 : Nat.ceil (2 * ℓ * Λ₀ / Real.pi) ≤ N := le_trans (le_max_right _ _) hN
      have h2 : ((Nat.ceil (2 * ℓ * Λ₀ / Real.pi) : ℕ) : ℝ) ≤ (N : ℝ) := by exact_mod_cast h1
      have h3 := Nat.le_ceil (2 * ℓ * Λ₀ / Real.pi)
      linarith
    have h1 : 2 * ℓ * Λ₀ ≤ Real.pi * (N : ℝ) := by
      have h := (div_le_iff₀ Real.pi_pos).mp hceil
      linarith
    have h2 : Λ₀ ≤ Real.pi * (N : ℝ) / (2 * ℓ) := by
      rw [le_div_iff₀ (by positivity : (0 : ℝ) < 2 * ℓ)]
      linarith
    rw [Work.BoseBoxFock.uvRad,
      show (2 * Real.pi / ℓ * (N : ℝ)) / 4 = Real.pi * (N : ℝ) / (2 * ℓ) by field_simp; ring]
    exact h2
  have hΛpos : 0 < Work.BoseBoxFock.uvRad ℓ N := by
    rw [Work.BoseBoxFock.uvRad]; positivity
  -- ### the smeared kernel `U` and the smoothing error
  set U : E3 → ℝ := Work.BoseBoxFock.uvSmear fu (Work.BoseBoxFock.uvRad ℓ N) W1 with hUdef
  have hUint : MeasureTheory.Integrable U := by
    rw [hUdef]
    exact kp_integrable_uvSmear fu hW1int (by rw [hW1def]; exact hW1cs_e) hΛpos
  have hUcont : Continuous U := by
    rw [hUdef]; exact Work.BoseBoxFock.uvSmear_continuous fu hΛpos hW1int
  have hUeven : ∀ x : E3, U (-x) = U x := by
    intro x; rw [hUdef]; exact kp_uvSmear_even fu hW1even _ x
  have hEint : MeasureTheory.Integrable (fun x : E3 => U x - W1 x) := hUint.sub hW1int
  have hEbound : ∫ x : E3, ‖U x - W1 x‖ ≤ (R / ℓ) ^ 12 := by
    rw [hUdef]; exact hΛ₀ _ hΛN
  have hUmass : ∫ x : E3, ‖U x‖ ≤ CL1 * (2 * G) := by
    have h0 := hL1 hΛpos hW1int
    have h0' : ∫ x : E3, ‖U x‖ ≤ CL1 * ∫ x : E3, ‖W1 x‖ := by rw [hUdef]; exact h0
    calc ∫ x : E3, ‖U x‖ ≤ CL1 * ∫ x : E3, ‖W1 x‖ := h0'
      _ ≤ CL1 * (2 * G) := by gcongr
  have htail : ∫ u in {u : E3 | R ≤ ‖u‖}, ‖U u‖ ≤ (R / ℓ) ^ 12 := by
    have hms : MeasurableSet {u : E3 | R ≤ ‖u‖} :=
      measurableSet_le measurable_const continuous_norm.measurable
    have hfun : ∀ u ∈ {u : E3 | R ≤ ‖u‖}, ‖U u‖ = ‖U u - W1 u‖ := by
      intro u hu
      have hW0 : W1 u = 0 := by
        rw [hW1def]
        exact kp_W1_zero_of_norm_ge (v := v) (h := h) hv_supp ℓ (by simpa using hu)
      rw [hW0, sub_zero]
    have h1 : ∫ u in {u : E3 | R ≤ ‖u‖}, ‖U u‖
        = ∫ u in {u : E3 | R ≤ ‖u‖}, ‖U u - W1 u‖ :=
      setIntegral_congr_fun hms hfun
    rw [h1]
    refine le_trans ?_ hEbound
    rw [← integral_indicator hms]
    refine integral_mono ?_ hEint.norm ?_
    · exact hEint.norm.indicator hms
    · intro u
      by_cases hu : u ∈ {u : E3 | R ≤ ‖u‖}
      · rw [Set.indicator_of_mem hu]
      · rw [Set.indicator_of_notMem hu]; positivity
  -- ### evenness of `KfrU` and of `chD`
  have hKfrUeven : ∀ u : E3, Work.BoseBoxFock.PCFU.KfrU v h μ fu N (-u)
      = Work.BoseBoxFock.PCFU.KfrU v h μ fu N u := by
    intro u
    have hper : ∀ z : E3, Work.BoseBoxFock.PCFU.KfrU v h μ fu N z
        = (((Work.BoseBoxFock.ellH v μ : ℂ)) ^ 3) * (∑' d : Fin 3 → ℤ,
            ((Work.BoseBoxFock.uvSmear fu (Work.BoseBoxFock.uvRad (Work.BoseBoxFock.ellH v μ) N)
              (Work.BoseFixR.W1fun v h (Work.BoseBoxFock.ellH v μ))
              (z + (Work.BoseBoxFock.ellH v μ) • Work.BoseBoxFock.latVec d) : ℝ) : ℂ)) :=
      fun z => Work.BoseBoxFock.PCFU.KfrU_periodisation (v := v) (h := h) (μ := μ) (fu := fu)
        (N := N) hside0 hW1int_e hW1cs_e hW1even_e hN1 z
    rw [hper (-u), hper u]
    congr 1
    have hpt : ∀ d : Fin 3 → ℤ,
        ((Work.BoseBoxFock.uvSmear fu (Work.BoseBoxFock.uvRad (Work.BoseBoxFock.ellH v μ) N)
            (Work.BoseFixR.W1fun v h (Work.BoseBoxFock.ellH v μ))
            (-u + (Work.BoseBoxFock.ellH v μ) • Work.BoseBoxFock.latVec d) : ℝ) : ℂ)
          = ((Work.BoseBoxFock.uvSmear fu (Work.BoseBoxFock.uvRad (Work.BoseBoxFock.ellH v μ) N)
              (Work.BoseFixR.W1fun v h (Work.BoseBoxFock.ellH v μ))
              (u + (Work.BoseBoxFock.ellH v μ) • Work.BoseBoxFock.latVec (-d)) : ℝ) : ℂ) := by
      intro d
      have h1 : Work.BoseBoxFock.uvSmear fu (Work.BoseBoxFock.uvRad (Work.BoseBoxFock.ellH v μ) N)
            (Work.BoseFixR.W1fun v h (Work.BoseBoxFock.ellH v μ))
            (-u + (Work.BoseBoxFock.ellH v μ) • Work.BoseBoxFock.latVec d)
          = Work.BoseBoxFock.uvSmear fu (Work.BoseBoxFock.uvRad (Work.BoseBoxFock.ellH v μ) N)
            (Work.BoseFixR.W1fun v h (Work.BoseBoxFock.ellH v μ))
            (u + (Work.BoseBoxFock.ellH v μ) • Work.BoseBoxFock.latVec (-d)) := by
        rw [show -u + (Work.BoseBoxFock.ellH v μ) • Work.BoseBoxFock.latVec d
              = -(u - (Work.BoseBoxFock.ellH v μ) • Work.BoseBoxFock.latVec d) by abel]
        rw [kp_uvSmear_even fu hW1even_e _ _]
        rw [kp_latVec_neg, smul_neg]
        abel
      exact congrArg (fun r : ℝ => ((r : ℝ) : ℂ)) h1
    calc (∑' d : Fin 3 → ℤ, ((Work.BoseBoxFock.uvSmear fu
              (Work.BoseBoxFock.uvRad (Work.BoseBoxFock.ellH v μ) N)
              (Work.BoseFixR.W1fun v h (Work.BoseBoxFock.ellH v μ))
              (-u + (Work.BoseBoxFock.ellH v μ) • Work.BoseBoxFock.latVec d) : ℝ) : ℂ))
        = ∑' d : Fin 3 → ℤ, ((Work.BoseBoxFock.uvSmear fu
              (Work.BoseBoxFock.uvRad (Work.BoseBoxFock.ellH v μ) N)
              (Work.BoseFixR.W1fun v h (Work.BoseBoxFock.ellH v μ))
              (u + (Work.BoseBoxFock.ellH v μ) • Work.BoseBoxFock.latVec (-d)) : ℝ) : ℂ) :=
          tsum_congr hpt
      _ = ∑' d : Fin 3 → ℤ, ((Work.BoseBoxFock.uvSmear fu
              (Work.BoseBoxFock.uvRad (Work.BoseBoxFock.ellH v μ) N)
              (Work.BoseFixR.W1fun v h (Work.BoseBoxFock.ellH v μ))
              (u + (Work.BoseBoxFock.ellH v μ) • Work.BoseBoxFock.latVec d) : ℝ) : ℂ) :=
          kp_tsum_latVec_neg_C (fun d => ((Work.BoseBoxFock.uvSmear fu
              (Work.BoseBoxFock.uvRad (Work.BoseBoxFock.ellH v μ) N)
              (Work.BoseFixR.W1fun v h (Work.BoseBoxFock.ellH v μ))
              (u + (Work.BoseBoxFock.ellH v μ) • Work.BoseBoxFock.latVec d) : ℝ) : ℂ))
  have hchDeven : ∀ u : E3, chD v h μ fu N (-u) = chD v h μ fu N u := by
    intro u
    have h1 : Work.BoseBoxFock.PCFU.KfrU v h μ fu N (-u)
        = Work.BoseBoxFock.PCFU.KfrU v h μ fu N u := hKfrUeven u
    simp only [chD]
    rw [← hℓdef, ← hW1def]
    rw [h1, hW1even u]
  -- ### the kernel `lintegral` bound
  have hgen : ∀ c : E3, ∫⁻ z : E3, ENNReal.ofReal
        ‖((Work.BoseK15.corpusBox.chiLam ℓ c : ℝ) : ℂ) * chD v h μ fu N (c - z)
          * ((Work.BoseK15.corpusBox.chiLam ℓ z : ℝ) : ℂ)‖
      ≤ ENNReal.ofReal (η * ℓ ^ 3 + (Cimg * (CL1 * (2 * G) + 1) + Submission.BoseGases.chiSup ^ 2)
          * ℓ ^ 3 * (R / ℓ) ^ 12) := by
    intro c
    -- abbreviations
    set Sfun : E3 → ℝ := fun z => ∑' m : Fin 3 → ℤ,
      (if m = 0 then (0 : ℝ) else ‖U (c - z + ℓ • latVec m)‖) with hSfundef
    set EE : E3 → ℝ := fun z => ‖U (c - z) - W1 (c - z)‖ with hEEdef
    have hSnn : ∀ z : E3, 0 ≤ Sfun z := by
      intro z
      rw [hSfundef]
      exact tsum_nonneg fun m => by split_ifs <;> positivity
    have hEnn : ∀ z : E3, 0 ≤ EE z := by
      intro z; rw [hEEdef]; exact norm_nonneg _
    -- the norm identity
    have hnorm : ∀ z : E3, ‖((Work.BoseK15.corpusBox.chiLam ℓ c : ℝ) : ℂ)
          * chD v h μ fu N (c - z) * ((Work.BoseK15.corpusBox.chiLam ℓ z : ℝ) : ℂ)‖
        = Submission.BoseGases.chiScale ℓ c * ‖chD v h μ fu N (c - z)‖
            * Submission.BoseGases.chiScale ℓ z := by
      intro z
      have hcw : ‖((Work.BoseK15.corpusBox.chiLam ℓ c : ℝ) : ℂ)‖
          = Submission.BoseGases.chiScale ℓ c := by
        have h := kp_chiLam_nonneg ℓ c
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg h, kp_chiScale_eq_chiLam]
      have hzw : ‖((Work.BoseK15.corpusBox.chiLam ℓ z : ℝ) : ℂ)‖
          = Submission.BoseGases.chiScale ℓ z := by
        have h := kp_chiLam_nonneg ℓ z
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg h, kp_chiScale_eq_chiLam]
      rw [norm_mul, norm_mul, hcw, hzw]
    -- the pointwise bound on `chD`
    have hchD : ∀ z : E3, ‖chD v h μ fu N (c - z)‖ ≤ ℓ ^ 3 * (Sfun z + EE z) := by
      intro z
      have hdec : chD v h μ fu N (c - z)
          = (Work.BoseBoxFock.PCFU.KfrU v h μ fu N (c - z)
              - (((ℓ : ℂ) ^ 3) * Complex.ofReal (U (c - z))))
            + (((ℓ : ℂ) ^ 3) * Complex.ofReal (U (c - z) - W1 (c - z))) := by
        rw [chD]
        rw [← hℓdef, ← hW1def]
        push_cast
        ring
      have h1' : ‖Work.BoseBoxFock.PCFU.KfrU v h μ fu N (c - z)
            - (((ℓ : ℂ) ^ 3) * Complex.ofReal (U (c - z)))‖ ≤ ℓ ^ 3 * Sfun z := by
        have h0 := Work.BoseBoxFock.KfrU_sub_uvSmear_norm_le (v := v) (h := h) (μ := μ) (fu := fu)
          (N := N) hside0 hW1int_e hW1cs_e hW1even_e hN1 (c - z)
        rw [← hℓdef, ← hW1def, ← hUdef] at h0
        rw [hSfundef]
        exact h0
      have h2 : ‖(((ℓ : ℂ) ^ 3) * Complex.ofReal (U (c - z) - W1 (c - z)))‖ ≤ ℓ ^ 3 * EE z := by
        have h3 : ‖((ℓ : ℂ) ^ 3)‖ = ℓ ^ 3 := by
          have h1 : ((ℓ : ℂ) ^ 3) = ((ℓ ^ 3 : ℝ) : ℂ) := by push_cast; ring
          rw [h1, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
        have h4 : ‖Complex.ofReal (U (c - z) - W1 (c - z))‖ = EE z := by
          rw [hEEdef]
          exact Complex.norm_real _
        rw [norm_mul, h3, h4]
      rw [hdec]
      calc ‖(Work.BoseBoxFock.PCFU.KfrU v h μ fu N (c - z)
              - (((ℓ : ℂ) ^ 3) * Complex.ofReal (U (c - z))))
            + (((ℓ : ℂ) ^ 3) * Complex.ofReal (U (c - z) - W1 (c - z)))‖
          ≤ ‖Work.BoseBoxFock.PCFU.KfrU v h μ fu N (c - z)
              - (((ℓ : ℂ) ^ 3) * Complex.ofReal (U (c - z)))‖
            + ‖(((ℓ : ℂ) ^ 3) * Complex.ofReal (U (c - z) - W1 (c - z)))‖ := norm_add_le _ _
        _ ≤ ℓ ^ 3 * Sfun z + ℓ ^ 3 * EE z := add_le_add h1' h2
        _ = ℓ ^ 3 * (Sfun z + EE z) := by ring
    -- measurability
    have hEae : AEMeasurable (fun z : E3 => U (c - z) - W1 (c - z)) volume := by
      have h2 : AEMeasurable (fun x : E3 => U x - W1 x)
          (volume.map (fun z : E3 => c - z)) := by
        rw [(Submission.BoseGases.measurePreserving_sub_left c).map_eq]
        exact hEint.aemeasurable
      exact AEMeasurable.comp_measurable (f := fun z : E3 => c - z)
        (g := fun x : E3 => U x - W1 x) h2 (by fun_prop)
    have hSmeas : AEMeasurable (fun z : E3 => ENNReal.ofReal (Submission.BoseGases.chiScale ℓ c
        * Submission.BoseGases.chiScale ℓ z * (ℓ ^ 3 * Sfun z))) volume := by
      have htsum : AEMeasurable (fun z : E3 => Sfun z) volume := by
        rw [hSfundef]
        refine AEMeasurable.tsum fun m => ?_
        by_cases hm : m = 0
        · subst hm
          have h0 : (fun z : E3 => (if ((0 : Fin 3 → ℤ) = 0) then (0 : ℝ)
              else ‖U (c - z + ℓ • latVec (0 : Fin 3 → ℤ))‖)) = fun _ : E3 => (0 : ℝ) := by
            funext z; simp
          rw [h0]
          exact aemeasurable_const
        · simp only [if_neg hm]
          exact ((hUcont.comp (by fun_prop : Continuous fun z : E3 => c - z + ℓ • latVec m)).norm).aemeasurable
      exact ENNReal.measurable_ofReal.comp_aemeasurable
        ((aemeasurable_const.mul (kp_chiScale_continuous ℓ).aemeasurable).mul
          (aemeasurable_const.mul htsum))
    have hEmeas : AEMeasurable (fun z : E3 => ENNReal.ofReal (Submission.BoseGases.chiScale ℓ c
        * Submission.BoseGases.chiScale ℓ z * (ℓ ^ 3 * EE z))) volume := by
      have h1 : AEMeasurable (fun z : E3 => EE z) volume := by
        rw [hEEdef]; exact hEae.norm
      exact ENNReal.measurable_ofReal.comp_aemeasurable
        ((aemeasurable_const.mul (kp_chiScale_continuous ℓ).aemeasurable).mul
          (aemeasurable_const.mul h1))
    have hSae : AEMeasurable (fun z : E3 => ENNReal.ofReal (Submission.BoseGases.chiScale ℓ c
        * Submission.BoseGases.chiScale ℓ z * Sfun z)) volume := by
      have htsum : AEMeasurable (fun z : E3 => Sfun z) volume := by
        rw [hSfundef]
        refine AEMeasurable.tsum fun m => ?_
        by_cases hm : m = 0
        · subst hm
          have h0 : (fun z : E3 => (if ((0 : Fin 3 → ℤ) = 0) then (0 : ℝ)
              else ‖U (c - z + ℓ • latVec (0 : Fin 3 → ℤ))‖)) = fun _ : E3 => (0 : ℝ) := by
            funext z; simp
          rw [h0]
          exact aemeasurable_const
        · simp only [if_neg hm]
          exact ((hUcont.comp (by fun_prop : Continuous fun z : E3 => c - z + ℓ • latVec m)).norm).aemeasurable
      exact ENNReal.measurable_ofReal.comp_aemeasurable
        ((aemeasurable_const.mul (kp_chiScale_continuous ℓ).aemeasurable).mul htsum)
    have hEae2 : AEMeasurable (fun z : E3 => ENNReal.ofReal (Submission.BoseGases.chiScale ℓ c
        * Submission.BoseGases.chiScale ℓ z * EE z)) volume :=
      ENNReal.measurable_ofReal.comp_aemeasurable
        ((aemeasurable_const.mul (kp_chiScale_continuous ℓ).aemeasurable).mul hEae.norm)
    -- the pointwise monotone step
    have hpoint : ∀ z : E3, ENNReal.ofReal (Submission.BoseGases.chiScale ℓ c
          * ‖chD v h μ fu N (c - z)‖ * Submission.BoseGases.chiScale ℓ z)
        ≤ ENNReal.ofReal (Submission.BoseGases.chiScale ℓ c * (ℓ ^ 3 * (Sfun z + EE z))
            * Submission.BoseGases.chiScale ℓ z) := by
      intro z
      have hc0 := kp_chiScale_nonneg ℓ c
      have hz0 := kp_chiScale_nonneg ℓ z
      refine ENNReal.ofReal_le_ofReal ?_
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hchD z) hc0) hz0
    -- the split
    have hsplit : (fun z : E3 => ENNReal.ofReal (Submission.BoseGases.chiScale ℓ c
            * (ℓ ^ 3 * (Sfun z + EE z)) * Submission.BoseGases.chiScale ℓ z))
        = fun z : E3 => ENNReal.ofReal (Submission.BoseGases.chiScale ℓ c
              * Submission.BoseGases.chiScale ℓ z * (ℓ ^ 3 * Sfun z))
            + ENNReal.ofReal (Submission.BoseGases.chiScale ℓ c
              * Submission.BoseGases.chiScale ℓ z * (ℓ ^ 3 * EE z)) := by
      funext z
      have h1 : Submission.BoseGases.chiScale ℓ c * (ℓ ^ 3 * (Sfun z + EE z))
            * Submission.BoseGases.chiScale ℓ z
          = Submission.BoseGases.chiScale ℓ c * Submission.BoseGases.chiScale ℓ z * (ℓ ^ 3 * Sfun z)
            + Submission.BoseGases.chiScale ℓ c * Submission.BoseGases.chiScale ℓ z * (ℓ ^ 3 * EE z) := by
        ring
      have hp : 0 ≤ Submission.BoseGases.chiScale ℓ c * Submission.BoseGases.chiScale ℓ z
            * (ℓ ^ 3 * Sfun z) :=
        mul_nonneg (mul_nonneg (kp_chiScale_nonneg ℓ c) (kp_chiScale_nonneg ℓ z))
          (mul_nonneg (by positivity) (hSnn z))
      have hq : 0 ≤ Submission.BoseGases.chiScale ℓ c * Submission.BoseGases.chiScale ℓ z
            * (ℓ ^ 3 * EE z) :=
        mul_nonneg (mul_nonneg (kp_chiScale_nonneg ℓ c) (kp_chiScale_nonneg ℓ z))
          (mul_nonneg (by positivity) (hEnn z))
      rw [h1, ENNReal.ofReal_add hp hq]
    have hsplitInt : (∫⁻ z : E3, ENNReal.ofReal (Submission.BoseGases.chiScale ℓ c
            * (ℓ ^ 3 * (Sfun z + EE z)) * Submission.BoseGases.chiScale ℓ z))
        = (∫⁻ z : E3, ENNReal.ofReal (Submission.BoseGases.chiScale ℓ c
              * Submission.BoseGases.chiScale ℓ z * (ℓ ^ 3 * Sfun z)))
          + (∫⁻ z : E3, ENNReal.ofReal (Submission.BoseGases.chiScale ℓ c
              * Submission.BoseGases.chiScale ℓ z * (ℓ ^ 3 * EE z))) := by
      rw [hsplit, MeasureTheory.lintegral_add_right' _ hEmeas]
    -- the images piece
    have hX : (∫⁻ z : E3, ENNReal.ofReal (Submission.BoseGases.chiScale ℓ c
          * Submission.BoseGases.chiScale ℓ z * (ℓ ^ 3 * Sfun z)))
        ≤ ENNReal.ofReal (ℓ ^ 3 * (Cimg * (R / ℓ) ^ 12 * (CL1 * (2 * G))
            + Cimg * (R / ℓ) ^ 12)) := by
      have hptfun : (fun z : E3 => ENNReal.ofReal (Submission.BoseGases.chiScale ℓ c
            * Submission.BoseGases.chiScale ℓ z * (ℓ ^ 3 * Sfun z)))
          = fun z : E3 => ENNReal.ofReal (ℓ ^ 3) * ENNReal.ofReal (Submission.BoseGases.chiScale ℓ c
              * Submission.BoseGases.chiScale ℓ z * Sfun z) := by
        funext z
        rw [show Submission.BoseGases.chiScale ℓ c * Submission.BoseGases.chiScale ℓ z
              * (ℓ ^ 3 * Sfun z)
            = ℓ ^ 3 * (Submission.BoseGases.chiScale ℓ c * Submission.BoseGases.chiScale ℓ z
              * Sfun z) by ring,
          ENNReal.ofReal_mul (by positivity)]
      calc (∫⁻ z : E3, ENNReal.ofReal (Submission.BoseGases.chiScale ℓ c
            * Submission.BoseGases.chiScale ℓ z * (ℓ ^ 3 * Sfun z)))
          = ∫⁻ z : E3, ENNReal.ofReal (ℓ ^ 3) * ENNReal.ofReal (Submission.BoseGases.chiScale ℓ c
              * Submission.BoseGases.chiScale ℓ z * Sfun z) := by rw [hptfun]
        _ = ENNReal.ofReal (ℓ ^ 3) * ∫⁻ z : E3, ENNReal.ofReal (Submission.BoseGases.chiScale ℓ c
              * Submission.BoseGases.chiScale ℓ z * Sfun z) :=
            MeasureTheory.lintegral_const_mul'' _ hSae
      have h0 := himg (ℓ := ℓ) (ρ := R) hℓ (le_of_lt hR) (U := U) hUint c
      have h1 : ENNReal.ofReal (ℓ ^ 3) * ENNReal.ofReal (Cimg * (R / ℓ) ^ 12 * (∫ u : E3, ‖U u‖)
            + Cimg * (∫ u in {u : E3 | R ≤ ‖u‖}, ‖U u‖))
          ≤ ENNReal.ofReal (ℓ ^ 3 * (Cimg * (R / ℓ) ^ 12 * (CL1 * (2 * G))
            + Cimg * (R / ℓ) ^ 12)) := by
        rw [← ENNReal.ofReal_mul (by positivity)]
        refine ENNReal.ofReal_le_ofReal ?_
        have h2 : Cimg * (R / ℓ) ^ 12 * (∫ u : E3, ‖U u‖) ≤ Cimg * (R / ℓ) ^ 12 * (CL1 * (2 * G)) :=
          mul_le_mul_of_nonneg_left hUmass (by positivity)
        have h3 : Cimg * (∫ u in {u : E3 | R ≤ ‖u‖}, ‖U u‖) ≤ Cimg * (R / ℓ) ^ 12 :=
          mul_le_mul_of_nonneg_left htail hCimgnn
        have h4 : Cimg * (R / ℓ) ^ 12 * (CL1 * (2 * G) + 1)
            = Cimg * (R / ℓ) ^ 12 * (CL1 * (2 * G)) + Cimg * (R / ℓ) ^ 12 := by ring
        have h5 : Cimg * (R / ℓ) ^ 12 * (∫ u : E3, ‖U u‖) + Cimg * (∫ u in {u : E3 | R ≤ ‖u‖}, ‖U u‖)
            ≤ Cimg * (R / ℓ) ^ 12 * (CL1 * (2 * G) + 1) := by
          linarith [h2, h3, h4]
        calc ℓ ^ 3 * (Cimg * (R / ℓ) ^ 12 * (∫ u : E3, ‖U u‖)
              + Cimg * (∫ u in {u : E3 | R ≤ ‖u‖}, ‖U u‖))
            ≤ ℓ ^ 3 * (Cimg * (R / ℓ) ^ 12 * (CL1 * (2 * G) + 1)) :=
              mul_le_mul_of_nonneg_left h5 (by positivity)
          _ = ℓ ^ 3 * (Cimg * (R / ℓ) ^ 12 * (CL1 * (2 * G)) + Cimg * (R / ℓ) ^ 12) := by
              rw [h4]
      calc ENNReal.ofReal (ℓ ^ 3) * ∫⁻ z : E3, ENNReal.ofReal (Submission.BoseGases.chiScale ℓ c
            * Submission.BoseGases.chiScale ℓ z * Sfun z)
          ≤ ENNReal.ofReal (ℓ ^ 3) * ENNReal.ofReal (Cimg * (R / ℓ) ^ 12 * (∫ u : E3, ‖U u‖)
              + Cimg * (∫ u in {u : E3 | R ≤ ‖u‖}, ‖U u‖)) :=
            mul_le_mul_of_nonneg_left h0 (by positivity)
        _ ≤ _ := h1
    -- the smoothing piece
    have hY : (∫⁻ z : E3, ENNReal.ofReal (Submission.BoseGases.chiScale ℓ c
          * Submission.BoseGases.chiScale ℓ z * (ℓ ^ 3 * EE z)))
        ≤ ENNReal.ofReal (ℓ ^ 3 * (Submission.BoseGases.chiSup ^ 2 * ∫ x : E3, ‖U x - W1 x‖)) := by
      have hptfun : (fun z : E3 => ENNReal.ofReal (Submission.BoseGases.chiScale ℓ c
            * Submission.BoseGases.chiScale ℓ z * (ℓ ^ 3 * EE z)))
          = fun z : E3 => ENNReal.ofReal (ℓ ^ 3) * ENNReal.ofReal (Submission.BoseGases.chiScale ℓ c
              * Submission.BoseGases.chiScale ℓ z * EE z) := by
        funext z
        rw [show Submission.BoseGases.chiScale ℓ c * Submission.BoseGases.chiScale ℓ z
              * (ℓ ^ 3 * EE z)
            = ℓ ^ 3 * (Submission.BoseGases.chiScale ℓ c * Submission.BoseGases.chiScale ℓ z
              * EE z) by ring,
          ENNReal.ofReal_mul (by positivity)]
      calc (∫⁻ z : E3, ENNReal.ofReal (Submission.BoseGases.chiScale ℓ c
            * Submission.BoseGases.chiScale ℓ z * (ℓ ^ 3 * EE z)))
          = ∫⁻ z : E3, ENNReal.ofReal (ℓ ^ 3) * ENNReal.ofReal (Submission.BoseGases.chiScale ℓ c
              * Submission.BoseGases.chiScale ℓ z * EE z) := by rw [hptfun]
        _ = ENNReal.ofReal (ℓ ^ 3) * ∫⁻ z : E3, ENNReal.ofReal (Submission.BoseGases.chiScale ℓ c
              * Submission.BoseGases.chiScale ℓ z * EE z) :=
            MeasureTheory.lintegral_const_mul'' _ hEae2
      have h0 := kp_E_le (E := fun x : E3 => U x - W1 x) hEint ℓ c
      have h1 : (∫⁻ z : E3, ENNReal.ofReal (Submission.BoseGases.chiScale ℓ c
            * Submission.BoseGases.chiScale ℓ z * EE z))
          ≤ ENNReal.ofReal (Submission.BoseGases.chiSup ^ 2 * ∫ x : E3, ‖U x - W1 x‖) := by
        refine le_trans (le_of_eq ?_) h0
        refine lintegral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
        congr 1
        rw [hEEdef]
        ring
      calc ENNReal.ofReal (ℓ ^ 3) * ∫⁻ z : E3, ENNReal.ofReal (Submission.BoseGases.chiScale ℓ c
            * Submission.BoseGases.chiScale ℓ z * EE z)
          ≤ ENNReal.ofReal (ℓ ^ 3) * ENNReal.ofReal (Submission.BoseGases.chiSup ^ 2
              * ∫ x : E3, ‖U x - W1 x‖) :=
            mul_le_mul_of_nonneg_left h1 (by positivity)
        _ = _ := by rw [← ENNReal.ofReal_mul (by positivity)]
    -- the final arithmetic
    have hAA : ENNReal.ofReal (ℓ ^ 3 * (Cimg * (R / ℓ) ^ 12 * (CL1 * (2 * G))
            + Cimg * (R / ℓ) ^ 12))
          + ENNReal.ofReal (ℓ ^ 3 * (Submission.BoseGases.chiSup ^ 2 * ∫ x : E3, ‖U x - W1 x‖))
        ≤ ENNReal.ofReal (η * ℓ ^ 3 + (Cimg * (CL1 * (2 * G) + 1) + Submission.BoseGases.chiSup ^ 2)
            * ℓ ^ 3 * (R / ℓ) ^ 12) := by
      rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
      refine ENNReal.ofReal_le_ofReal ?_
      have h2 : Submission.BoseGases.chiSup ^ 2 * ∫ x : E3, ‖U x - W1 x‖
          ≤ Submission.BoseGases.chiSup ^ 2 * (R / ℓ) ^ 12 :=
        mul_le_mul_of_nonneg_left hEbound (by positivity)
      have h5 : Cimg * (R / ℓ) ^ 12 * (CL1 * (2 * G)) + Cimg * (R / ℓ) ^ 12
          + Submission.BoseGases.chiSup ^ 2 * ∫ x : E3, ‖U x - W1 x‖
          ≤ (Cimg * (CL1 * (2 * G) + 1) + Submission.BoseGases.chiSup ^ 2) * (R / ℓ) ^ 12 := by
        nlinarith [h2]
      have h6 : ℓ ^ 3 * (Cimg * (R / ℓ) ^ 12 * (CL1 * (2 * G)) + Cimg * (R / ℓ) ^ 12)
            + ℓ ^ 3 * (Submission.BoseGases.chiSup ^ 2 * ∫ x : E3, ‖U x - W1 x‖)
          ≤ ℓ ^ 3 * ((Cimg * (CL1 * (2 * G) + 1) + Submission.BoseGases.chiSup ^ 2)
              * (R / ℓ) ^ 12) := by
        have h7 := mul_le_mul_of_nonneg_left h5 (show (0 : ℝ) ≤ ℓ ^ 3 by positivity)
        nlinarith [h7]
      have h7 : ℓ ^ 3 * ((Cimg * (CL1 * (2 * G) + 1) + Submission.BoseGases.chiSup ^ 2)
            * (R / ℓ) ^ 12)
          ≤ η * ℓ ^ 3 + (Cimg * (CL1 * (2 * G) + 1) + Submission.BoseGases.chiSup ^ 2)
              * ℓ ^ 3 * (R / ℓ) ^ 12 := by
        nlinarith [hη.le, pow_nonneg hℓ.le 3]
      nlinarith [h6, h7]
    -- assembly
    calc ∫⁻ z : E3, ENNReal.ofReal ‖((Work.BoseK15.corpusBox.chiLam ℓ c : ℝ) : ℂ)
            * chD v h μ fu N (c - z) * ((Work.BoseK15.corpusBox.chiLam ℓ z : ℝ) : ℂ)‖
        = ∫⁻ z : E3, ENNReal.ofReal (Submission.BoseGases.chiScale ℓ c
            * ‖chD v h μ fu N (c - z)‖ * Submission.BoseGases.chiScale ℓ z) := by
          rw [show (fun z : E3 => ENNReal.ofReal ‖((Work.BoseK15.corpusBox.chiLam ℓ c : ℝ) : ℂ)
                * chD v h μ fu N (c - z) * ((Work.BoseK15.corpusBox.chiLam ℓ z : ℝ) : ℂ)‖)
              = (fun z : E3 => ENNReal.ofReal (Submission.BoseGases.chiScale ℓ c
                  * ‖chD v h μ fu N (c - z)‖ * Submission.BoseGases.chiScale ℓ z)) from
            funext fun z => by rw [hnorm z]]
      _ ≤ ∫⁻ z : E3, ENNReal.ofReal (Submission.BoseGases.chiScale ℓ c
            * (ℓ ^ 3 * (Sfun z + EE z)) * Submission.BoseGases.chiScale ℓ z) :=
          lintegral_mono hpoint
      _ = (∫⁻ z : E3, ENNReal.ofReal (Submission.BoseGases.chiScale ℓ c
              * Submission.BoseGases.chiScale ℓ z * (ℓ ^ 3 * Sfun z)))
            + (∫⁻ z : E3, ENNReal.ofReal (Submission.BoseGases.chiScale ℓ c
              * Submission.BoseGases.chiScale ℓ z * (ℓ ^ 3 * EE z))) := hsplitInt
      _ ≤ ENNReal.ofReal (ℓ ^ 3 * (Cimg * (R / ℓ) ^ 12 * (CL1 * (2 * G))
            + Cimg * (R / ℓ) ^ 12))
          + ENNReal.ofReal (ℓ ^ 3 * (Submission.BoseGases.chiSup ^ 2
              * ∫ x : E3, ‖U x - W1 x‖)) := add_le_add hX hY
      _ ≤ ENNReal.ofReal (η * ℓ ^ 3 + (Cimg * (CL1 * (2 * G) + 1) + Submission.BoseGases.chiSup ^ 2)
            * ℓ ^ 3 * (R / ℓ) ^ 12) := hAA
  -- ### the two Schur hypotheses
  have hKrow : ∀ᵐ w ∂(volume : Measure E3), ∫⁻ z : E3, ENNReal.ofReal
        ‖((Work.BoseK15.corpusBox.chiLam ℓ w : ℝ) : ℂ) * chD v h μ fu N (w - z)
          * ((Work.BoseK15.corpusBox.chiLam ℓ z : ℝ) : ℂ)‖
      ≤ ENNReal.ofReal (η * ℓ ^ 3 + (Cimg * (CL1 * (2 * G) + 1) + Submission.BoseGases.chiSup ^ 2)
          * ℓ ^ 3 * (R / ℓ) ^ 12) :=
    Filter.Eventually.of_forall hgen
  have hKcol : ∀ᵐ z ∂(volume : Measure E3), ∫⁻ w : E3, ENNReal.ofReal
        ‖((Work.BoseK15.corpusBox.chiLam ℓ w : ℝ) : ℂ) * chD v h μ fu N (w - z)
          * ((Work.BoseK15.corpusBox.chiLam ℓ z : ℝ) : ℂ)‖
      ≤ ENNReal.ofReal (η * ℓ ^ 3 + (Cimg * (CL1 * (2 * G) + 1) + Submission.BoseGases.chiSup ^ 2)
          * ℓ ^ 3 * (R / ℓ) ^ 12) := by
    refine Filter.Eventually.of_forall fun z => ?_
    have h0 := hgen z
    refine le_trans (le_of_eq ?_) h0
    refine lintegral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
    have hcw : ‖((Work.BoseK15.corpusBox.chiLam ℓ w : ℝ) : ℂ)‖
        = Submission.BoseGases.chiScale ℓ w := by
      have h := kp_chiLam_nonneg ℓ w
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg h, kp_chiScale_eq_chiLam]
    have hzw : ‖((Work.BoseK15.corpusBox.chiLam ℓ z : ℝ) : ℂ)‖
        = Submission.BoseGases.chiScale ℓ z := by
      have h := kp_chiLam_nonneg ℓ z
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg h, kp_chiScale_eq_chiLam]
    show ENNReal.ofReal ‖((Work.BoseK15.corpusBox.chiLam ℓ w : ℝ) : ℂ) * chD v h μ fu N (w - z)
          * ((Work.BoseK15.corpusBox.chiLam ℓ z : ℝ) : ℂ)‖
      = ENNReal.ofReal ‖((Work.BoseK15.corpusBox.chiLam ℓ z : ℝ) : ℂ) * chD v h μ fu N (z - w)
          * ((Work.BoseK15.corpusBox.chiLam ℓ w : ℝ) : ℂ)‖
    rw [norm_mul, norm_mul, hcw, hzw, norm_mul, norm_mul, hzw, hcw]
    congr 1
    have h1 : ‖chD v h μ fu N (w - z)‖ = ‖chD v h μ fu N (z - w)‖ := by
      rw [show w - z = -(z - w) by abel, hchDeven (z - w)]
    rw [h1]
    ring
  -- ### the joint measurability of the kernel
  have hKmeas : AEStronglyMeasurable (Function.uncurry (fun w z : E3 =>
      ((Work.BoseK15.corpusBox.chiLam ℓ w : ℝ) : ℂ) * chD v h μ fu N (w - z)
        * ((Work.BoseK15.corpusBox.chiLam ℓ z : ℝ) : ℂ)))
      ((volume : Measure E3).prod (volume : Measure E3)) := by
    have h1 : AEMeasurable (fun p : E3 × E3 => ((Work.BoseK15.corpusBox.chiLam ℓ p.1 : ℝ) : ℂ))
        ((volume : Measure E3).prod (volume : Measure E3)) :=
      (Complex.continuous_ofReal.comp ((Work.BoseB4.BoxData.chiLam_cont Work.BoseK15.corpusBox ℓ).comp continuous_fst)).aemeasurable
    have h3 : AEMeasurable (fun p : E3 × E3 => ((Work.BoseK15.corpusBox.chiLam ℓ p.2 : ℝ) : ℂ))
        ((volume : Measure E3).prod (volume : Measure E3)) :=
      (Complex.continuous_ofReal.comp ((Work.BoseB4.BoxData.chiLam_cont Work.BoseK15.corpusBox ℓ).comp continuous_snd)).aemeasurable
    have hKfrUC : Continuous (fun p : E3 × E3 => Work.BoseBoxFock.PCFU.KfrU v h μ fu N (p.1 - p.2)) := by
      rw [show (fun p : E3 × E3 => Work.BoseBoxFock.PCFU.KfrU v h μ fu N (p.1 - p.2))
          = (fun p : E3 × E3 => ∑ k : Work.BoseBoxFock.Lab N,
              ((Work.BoseBoxFock.W1h v h μ fu N k : ℝ) : ℂ)
                * Complex.exp (Complex.I * (inner ℝ
                    (Work.BoseBoxFock.kmomLab (Work.BoseBoxFock.ellH v μ) N k) (p.1 - p.2) : ℂ)))
          from funext fun p => by rw [Work.BoseBoxFock.PCFU.KfrU]]
      fun_prop
    have hW1ae : AEStronglyMeasurable (fun p : E3 × E3 =>
        Work.BoseFixR.W1fun v h (Work.BoseBoxFock.ellH v μ) (p.1 - p.2))
        ((volume : Measure E3).prod (volume : Measure E3)) := by
      have h := AEStronglyMeasurable.convolution_integrand (μ := (volume : Measure E3))
        (ν := (volume : Measure E3)) (L := ContinuousLinearMap.lsmul ℝ ℝ)
        (f := fun _ : E3 => (1 : ℝ))
        (g := fun x : E3 => Work.BoseFixR.W1fun v h (Work.BoseBoxFock.ellH v μ) x)
        aestronglyMeasurable_const hW1int_e.aestronglyMeasurable
      simpa only [ContinuousLinearMap.lsmul_apply, smul_eq_mul, one_mul] using h
    have h2 : AEMeasurable (fun p : E3 × E3 => chD v h μ fu N (p.1 - p.2))
        ((volume : Measure E3).prod (volume : Measure E3)) := by
      have hdec : (fun p : E3 × E3 => chD v h μ fu N (p.1 - p.2))
          = fun p : E3 × E3 => (Work.BoseBoxFock.PCFU.KfrU v h μ fu N (p.1 - p.2)
              - ((Work.BoseBoxFock.ellH v μ : ℂ) ^ 3)
                * ((Work.BoseFixR.W1fun v h (Work.BoseBoxFock.ellH v μ) (p.1 - p.2) : ℝ) : ℂ)) := by
        funext p; rw [chD]
      rw [hdec]
      exact hKfrUC.aemeasurable.sub ((aemeasurable_const.mul
        (Complex.continuous_ofReal.measurable.comp_aemeasurable hW1ae.aemeasurable)))
    exact ((h1.mul h2).mul h3).aestronglyMeasurable
  -- ### the Schur test
  intro f g hf hg
  have hschur := Work.BoseBoxFock.PCFU.kp_schur_pairing_le (K := fun w z : E3 =>
      ((Work.BoseK15.corpusBox.chiLam ℓ w : ℝ) : ℂ) * chD v h μ fu N (w - z)
        * ((Work.BoseK15.corpusBox.chiLam ℓ z : ℝ) : ℂ))
    (a := η * ℓ ^ 3 + (Cimg * (CL1 * (2 * G) + 1) + Submission.BoseGases.chiSup ^ 2)
      * ℓ ^ 3 * (R / ℓ) ^ 12)
    (b := η * ℓ ^ 3 + (Cimg * (CL1 * (2 * G) + 1) + Submission.BoseGases.chiSup ^ 2)
      * ℓ ^ 3 * (R / ℓ) ^ 12)
    (by positivity) (by positivity) hKmeas hKrow hKcol hf hg
  rw [Real.sqrt_mul_self (by positivity)] at hschur
  refine le_trans (le_of_eq ?_) hschur
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
  refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
  ring

end Work.BoseBoxFock.PCFU
