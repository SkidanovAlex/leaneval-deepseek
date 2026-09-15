import Submission.FUP.CartanDisk
import Submission.FUP.LensChange
import Submission.FUP.ZeroSet

open MeasureTheory Metric Set Complex Filter
open scoped ENNReal BigOperators Topology

set_option autoImplicit false
set_option maxHeartbeats 800000

/-!
# The single-cell localisation (Han–Schlag `prop:locddim` at one cell)

Ingredients of the per-cell Cartan step:

* `lensMap_hasDerivAt_of_norm_mul_lt_one` — the derivative of `lensMap q ε` with the *correct*
  hypothesis `‖(1-ε)w‖ < 1`.  (`Submission.FUP.Lens.lensMap_hasDerivAt` asks for `‖w‖ < 1`, which
  is too strong: it excludes the boundary `‖w‖ = 1`, and `AnalyticOnNhd` on the *closed* polydisc
  is needed for `cartes_polydisk_measure`.)
* `differentiableOn_lensMap`, `analyticOnNhd_lensMap` — `lensMap q ε` is holomorphic on a
  neighbourhood of the closed unit disk.
* `PsiLens` — the complex coordinatewise lens map.  Its analyticity (`analyticOnNhd_PsiLens`) is
  recorded as a TODO below.
-/

namespace Submission.FUP

variable {d : ℕ}

/-- The derivative of `lensMap q ε` needs only `‖(1-ε)w‖ < 1`. -/
lemma lensMap_hasDerivAt_of_norm_mul_lt_one {q ε : ℝ} {w : ℂ} (hε0 : 0 ≤ ε) (hε : ε < 1)
    (hnorm : ‖((1 - ε : ℝ) : ℂ) * w‖ < 1) :
    HasDerivAt (lensMap q ε)
      (((1 - ε : ℝ) : ℂ) * (((2 * q / Real.pi : ℝ) : ℂ) *
        (2 / (1 - (((1 - ε : ℝ) : ℂ) * w) ^ 2)))) w := by
  have hlin : HasDerivAt (fun w : ℂ => ((1 - ε : ℝ) : ℂ) * w) ((1 - ε : ℝ) : ℂ) w := by
    simpa using (hasDerivAt_id w).const_mul ((1 - ε : ℝ) : ℂ)
  have h := (stripMap_hasDerivAt' q hnorm).comp w hlin
  simp only [Function.comp_def] at h
  have hfun : (fun x : ℂ => stripMap q (((1 - ε : ℝ) : ℂ) * x)) = lensMap q ε := rfl
  rw [hfun] at h
  have hcomm : (((1 - ε : ℝ) : ℂ) * (((2 * q / Real.pi : ℝ) : ℂ) *
      (2 / (1 - (((1 - ε : ℝ) : ℂ) * w) ^ 2))))
      = ((2 * q / Real.pi : ℝ) : ℂ) *
        (2 / (1 - (((1 - ε : ℝ) : ℂ) * w) ^ 2)) * ((1 - ε : ℝ) : ℂ) := by ring
  rw [hcomm]
  exact h

lemma isOpen_norm_mul_lt_one (ε : ℝ) : IsOpen {w : ℂ | ‖((1 - ε : ℝ) : ℂ) * w‖ < 1} :=
  isOpen_lt ((continuous_const.mul continuous_id).norm) continuous_const

/-- `lensMap q ε` is differentiable on `{w | ‖(1-ε)w‖ < 1}`. -/
lemma differentiableOn_lensMap {q ε : ℝ} (hε0 : 0 ≤ ε) (hε : ε < 1) :
    DifferentiableOn ℂ (lensMap q ε) {w : ℂ | ‖((1 - ε : ℝ) : ℂ) * w‖ < 1} :=
  fun _ hw => (lensMap_hasDerivAt_of_norm_mul_lt_one hε0 hε hw).differentiableAt
    |>.differentiableWithinAt

/-- `lensMap q ε` is holomorphic on the closed unit disk. -/
lemma analyticOnNhd_lensMap {q ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) :
    AnalyticOnNhd ℂ (lensMap q ε) (Metric.closedBall 0 1) := by
  have hU : AnalyticOnNhd ℂ (lensMap q ε) {w : ℂ | ‖((1 - ε : ℝ) : ℂ) * w‖ < 1} :=
    (differentiableOn_lensMap (le_of_lt hε0) hε1).analyticOnNhd (isOpen_norm_mul_lt_one ε)
  refine hU.mono ?_
  intro w hw
  rw [Metric.mem_closedBall, dist_zero_right] at hw
  rw [Set.mem_ofPred_eq, norm_mul, norm_ofReal_eq_abs,
    abs_of_nonneg (by linarith : (0:ℝ) ≤ 1 - ε)]
  nlinarith [hε0, hε1, hw]

/-- The complex coordinatewise lens map. -/
noncomputable def PsiLens (q ε : ℝ) (w : Fin d → ℂ) : Fin d → ℂ := fun j => lensMap q ε (w j)

/-- `PsiLens` is holomorphic on the closed polydisc.  (Pin `𝕜`, `e`, `Fm`, `f` at
`AnalyticAt.pi`: without them the codomain family stays a metavariable and instance synthesis
gets stuck — the same failure mode as `hasFDerivAt_pi`.) -/
lemma analyticOnNhd_PsiLens {q ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) :
    AnalyticOnNhd ℂ (PsiLens (d := d) q ε) (Metric.closedBall 0 1) := by
  intro w hw
  have hwj : ∀ j : Fin d, w j ∈ Metric.closedBall (0 : ℂ) 1 := fun j => by
    rw [Metric.mem_closedBall, dist_zero_right] at hw
    rw [Metric.mem_closedBall, dist_zero_right]
    exact (pi_norm_le_iff_of_nonneg (by norm_num)).mp hw j
  have h1 : ∀ j : Fin d, AnalyticAt ℂ (fun y : Fin d → ℂ => lensMap q ε (y j)) w := fun j =>
    AnalyticAt.comp (𝕜 := ℂ) (x := w) (f := fun y : Fin d → ℂ => y j) (g := lensMap q ε)
      (analyticOnNhd_lensMap hε0 hε1 (w j) (hwj j))
      ((ContinuousLinearMap.proj (R := ℂ) j).analyticAt w)
  have h2 := AnalyticAt.pi (𝕜 := ℂ) (e := w) (Fm := fun _ : Fin d => ℂ)
    (f := fun j (y : Fin d → ℂ) => lensMap q ε (y j)) h1
  rw [show PsiLens (d := d) q ε = fun x x_1 => lensMap q ε (x x_1) from rfl]
  exact h2

/-- **The per-cell functions** `G_n(w) = g(c + η • PsiLens q ε w)` are holomorphic on the closed
polydisc whenever `g` is entire.  (`c` is the cell centre and `η` the affine scaling of
Session 57's geometry.) -/
lemma analyticOnNhd_lensComp {q ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1)
    {g : (Fin d → ℂ) → ℂ} (hg : AnalyticOnNhd ℂ g Set.univ) {c : Fin d → ℂ} {η : ℂ} :
    AnalyticOnNhd ℂ (fun w : Fin d → ℂ => g (fun j => c j + η * lensMap q ε (w j)))
      (Metric.closedBall 0 1) := by
  refine hg.comp ?_ (fun w _ => Set.mem_univ _)
  have hPsi : AnalyticOnNhd ℂ (PsiLens (d := d) q ε) (Metric.closedBall 0 1) :=
    analyticOnNhd_PsiLens hε0 hε1
  have hc : AnalyticOnNhd ℂ (fun _ : Fin d → ℂ => c) (Metric.closedBall 0 1) :=
    analyticOnNhd_const
  have hsm : AnalyticOnNhd ℂ (fun w : Fin d → ℂ => fun j => η * PsiLens q ε w j)
      (Metric.closedBall 0 1) := by
    have h := hPsi.const_smul (c := η)
    rw [show (η • PsiLens (d := d) q ε) = fun w : Fin d → ℂ => fun j => η * lensMap q ε (w j)
      from rfl] at h
    simpa [PsiLens] using h
  have h := hc.add hsm
  rw [show (fun _ : Fin d → ℂ => c) + (fun w : Fin d → ℂ => fun j => η * PsiLens q ε w j)
      = fun w : Fin d → ℂ => fun j => c j + η * lensMap q ε (w j) from rfl] at h
  simpa [PsiLens] using h

/-- **The normalised Cartan step (single cell).**  If `G` is holomorphic on the closed polydisc and
bounded by `S > 0`, then with `M := 1` — i.e. after normalising `G ↦ S⁻¹ • G`, so that no
`max 1` slack is introduced — `cartes_polydisk_measure` gives an explicit bound for the bad set,
with level `m (1+L)^d`, `L = 2δ⁻³log(2/δ) + δ⁻²log(2e/H)`. -/
theorem cartan_polydisk_normalised {δ H S m : ℝ} (hδ0 : 0 < δ) (hδ3 : δ < 1 / 3)
    (hH0 : 0 < H) (hH1 : H ≤ 1) (hS : 0 < S)
    (d : ℕ) (hd : 1 ≤ d) (G : (Fin d → ℂ) → ℂ)
    (hG : AnalyticOnNhd ℂ G (Metric.closedBall 0 1))
    (hSb : ∀ z : Fin d → ℂ, (∀ i, ‖z i‖ ≤ 1) → ‖G z‖ ≤ S)
    (hm : ∃ z : Fin d → ℂ, (∀ i, ‖z i‖ ≤ 1 - 3 * δ) ∧
      ((S⁻¹ : ℝ) : ℂ) * G z ≠ 0 ∧ m ≤ Real.log ‖((S⁻¹ : ℝ) : ℂ) * G z‖) :
    MeasureTheory.volume {x : Fin d → ℝ | (∀ i, |x i| ≤ 1 - 2 * δ) ∧
        Real.log ‖((S⁻¹ : ℝ) : ℂ) * G (fun i => (x i : ℂ))‖ <
          m * (1 + (2 * δ⁻¹ ^ 3 * Real.log (2 / δ) +
            δ⁻¹ ^ 2 * Real.log (2 * Real.exp 1 / H))) ^ d}
      ≤ ENNReal.ofReal (20 ^ d * H) := by
  have h1 := cartanDisk_bad_measure (M := 1) hδ0 hδ3 hH0 hH1 le_rfl
  have hG' : AnalyticOnNhd ℂ (fun z : Fin d → ℂ => ((S⁻¹ : ℝ) : ℂ) * G z)
      (Metric.closedBall 0 1) := by
    have hcs := hG.const_smul (c := ((S⁻¹ : ℝ) : ℂ))
    rw [show (((S⁻¹ : ℝ) : ℂ) • G) = fun z : Fin d → ℂ => ((S⁻¹ : ℝ) : ℂ) * G z from by
      funext z; simp [Pi.smul_apply, smul_eq_mul]] at hcs
    exact hcs
  have h := Commons.Analysis.Complex.cartan_polydisk_measure (M := 1) hδ0 hδ3 hH0 hH1 le_rfl h1
    d hd (fun z => ((S⁻¹ : ℝ) : ℂ) * G z) hG' hm ?_
  · have hlev : m - (Real.log (1:ℝ) - m) *
        ((1 + (2 * δ⁻¹ ^ 3 * Real.log (2 / δ) +
          δ⁻¹ ^ 2 * Real.log (2 * Real.exp 1 / H))) ^ d - 1)
        = m * (1 + (2 * δ⁻¹ ^ 3 * Real.log (2 / δ) +
            δ⁻¹ ^ 2 * Real.log (2 * Real.exp 1 / H))) ^ d := by
      rw [Real.log_one, zero_sub, neg_mul]
      ring
    rwa [hlev] at h
  · intro z hz
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (le_of_lt (inv_pos.mpr hS))]
    rw [inv_mul_le_iff₀ hS]
    simpa using hSb z hz

/-- **The algebraic consequence of the normalised Cartan step.**  If `G' = S⁻¹ • G` satisfies
`RMS_mid(G')^{1/κ} ≤ 2 RMS_J(G')` (which is what the Cartan estimate gives, with
`1/κ = (1+L)^d`), then the *unnormalised* RMS satisfies
`RMS_mid(G) ≤ S^{1-κ} (2 RMS_J(G))^κ`.

This is the point at which the `M ≥ 1` requirement of `cartes_polydisk_measure` is honoured
*without* any `max 1` slack: normalising by `S := sup‖G‖` makes `M = 1` the **sharp** sup bound for
`G'`, so no case distinction on `S ≤ 1` is needed. -/
lemma rms_normalised_bound {κ S A B : ℝ} (hκ0 : 0 < κ) (hκ1 : κ ≤ 1) (hS : 0 < S)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (h : A ^ (1 / κ) ≤ 2 * B) :
    S * A ≤ S ^ (1 - κ) * (2 * (S * B)) ^ κ := by
  have hAc : A = (A ^ (1 / κ)) ^ κ := by
    rw [← Real.rpow_mul hA, show (1 : ℝ) / κ * κ = 1 from by field_simp, Real.rpow_one]
  have h1 : A ≤ (2 * B) ^ κ := by
    rw [hAc]
    exact Real.rpow_le_rpow (Real.rpow_nonneg hA _) h (le_of_lt hκ0)
  have h2 : S * A ≤ S * (2 * B) ^ κ := mul_le_mul_of_nonneg_left h1 (le_of_lt hS)
  calc S * A ≤ S * (2 * B) ^ κ := h2
    _ = S ^ (1 - κ) * S ^ κ * (2 * B) ^ κ := by
        rw [← Real.rpow_add hS, sub_add_cancel, Real.rpow_one]
    _ = S ^ (1 - κ) * (S ^ κ * (2 * B) ^ κ) := by ring
    _ = S ^ (1 - κ) * (2 * (S * B)) ^ κ := by
        rw [← Real.mul_rpow (le_of_lt hS) (by positivity : (0:ℝ) ≤ 2 * B)]
        ring

/-- **The integration step of the single-cell localisation.**  If `B` is the Cartan bad set —
`B` measurable, `volume B ≤ ofReal (20^d H)`, and **off `B`** the *exponential* bound
`Real.exp m ≤ ‖G (↑x)‖` holds — and `J` lies in `{|x i| ≤ 1-2δ}`, then the `exp m` level survives
the passage to `∫_J ‖G∘↑‖`, losing only `20^d H` of the measure of `J`.

Note the hypothesis is the **exponential** form, not the log form: the two differ precisely on the
zero set of `G` (`Real.log 0 = 0`), and the caller disposes of the zeros once and for all by
enlarging `B` to `B ∪ {G = 0}` — which is legitimate because
`volume (B ∪ Z) ≤ volume B + volume Z = volume B + 0` by `measure_union_le` and
`volume_zero_set_pi`, and `measure_union_le` needs no measurability of `Z`.  Keeping the zeros out
of this lemma is what makes it independent of the `clipG`/measurability chore. -/
lemma exp_level_mul_measure_le_integral {δ H m : ℝ} (hH0 : 0 < H)
    {G : (Fin d → ℂ) → ℂ} {J B : Set (Fin d → ℝ)}
    (hJmeas : MeasurableSet J) (hBmeas : MeasurableSet B)
    (hbad : MeasureTheory.volume B ≤ ENNReal.ofReal (20 ^ d * H))
    (hexp : ∀ x, x ∉ B → (∀ i, |x i| ≤ 1 - 2 * δ) →
      Real.exp m ≤ ‖G (fun i => (x i : ℂ))‖)
    (hJwide : ∀ x ∈ J, ∀ i, |x i| ≤ 1 - 2 * δ)
    (hJfin : MeasureTheory.volume J ≠ ⊤)
    (hJbig : ENNReal.ofReal (20 ^ d * H) ≤ MeasureTheory.volume J)
    (hint : IntegrableOn (fun x : Fin d → ℝ => ‖G (fun i => (x i : ℂ))‖) J MeasureTheory.volume) :
    Real.exp m * ((MeasureTheory.volume J).toReal - 20 ^ d * H)
      ≤ ∫ x in J, ‖G (fun i => (x i : ℂ))‖ := by
  have hJB_meas : MeasurableSet (J \ B) := hJmeas.diff hBmeas
  have hJB_sub : J \ B ⊆ J := Set.sdiff_subset
  have hJB_fin : MeasureTheory.volume (J \ B) ≠ ⊤ :=
    ne_of_lt (lt_of_le_of_lt (measure_mono hJB_sub) (lt_top_iff_ne_top.mpr hJfin))
  have h2 : MeasureTheory.volume (J \ B)
      = MeasureTheory.volume J - MeasureTheory.volume (J ∩ B) :=
    ENNReal.eq_sub_of_add_eq
      (ne_of_lt (lt_of_le_of_lt (measure_mono Set.inter_subset_left)
        (lt_top_iff_ne_top.mpr hJfin)))
      (measure_sdiff_add_inter J hBmeas)
  have h3 : MeasureTheory.volume (J ∩ B) ≤ ENNReal.ofReal (20 ^ d * H) :=
    le_trans (measure_mono Set.inter_subset_right) hbad
  have hsub : (MeasureTheory.volume J).toReal - 20 ^ d * H
      ≤ (MeasureTheory.volume (J \ B)).toReal := by
    have hle : MeasureTheory.volume (J \ B)
        ≥ MeasureTheory.volume J - ENNReal.ofReal (20 ^ d * H) := by
      rw [h2]
      exact tsub_le_tsub_left h3 _
    have := ENNReal.toReal_mono hJB_fin hle
    rwa [ENNReal.toReal_sub_of_le hJbig hJfin, ENNReal.toReal_ofReal
      (by positivity : (0:ℝ) ≤ 20 ^ d * H)] at this
  have hint' : IntegrableOn (fun x : Fin d → ℝ => ‖G (fun i => (x i : ℂ))‖)
      (J \ B) MeasureTheory.volume := hint.mono_set hJB_sub
  have hmono : ∫ x in J \ B, Real.exp m
      ≤ ∫ x in J \ B, ‖G (fun i => (x i : ℂ))‖ :=
    setIntegral_mono_on (integrableOn_const hJB_fin) hint' hJB_meas
      (fun x hx => hexp x hx.2 (hJwide x hx.1))
  have hconst : ∫ _x in J \ B, Real.exp m
      = Real.exp m * (MeasureTheory.volume (J \ B)).toReal := by
    rw [setIntegral_const, MeasureTheory.Measure.real_def, smul_eq_mul, mul_comm]
  have hle : ∫ x in J \ B, ‖G (fun i => (x i : ℂ))‖
      ≤ ∫ x in J, ‖G (fun i => (x i : ℂ))‖ :=
    setIntegral_mono_set hint (Filter.Eventually.of_forall fun x => norm_nonneg _)
      (Filter.Eventually.of_forall fun x hx => hJB_sub hx)
  calc Real.exp m * ((MeasureTheory.volume J).toReal - 20 ^ d * H)
      ≤ Real.exp m * (MeasureTheory.volume (J \ B)).toReal :=
        mul_le_mul_of_nonneg_left hsub (Real.exp_nonneg _)
    _ = ∫ x in J \ B, Real.exp m := hconst.symm
    _ ≤ ∫ x in J \ B, ‖G (fun i => (x i : ℂ))‖ := hmono
    _ ≤ ∫ x in J, ‖G (fun i => (x i : ℂ))‖ := hle





/-! ## The boxes and the mean-square functional -/

/-- The box `[-c,c]^d` in `Fin d → ℝ`. -/
noncomputable def cbox (d : ℕ) (c : ℝ) : Set (Fin d → ℝ) :=
  Set.pi Set.univ (fun _ : Fin d => Set.Icc (-c) c)

lemma mem_cbox {d : ℕ} {c : ℝ} {x : Fin d → ℝ} : x ∈ cbox d c ↔ ∀ i, |x i| ≤ c := by
  rw [cbox, Set.mem_pi]
  constructor
  · intro h i
    exact abs_le.mpr (h i (Set.mem_univ i))
  · intro h i _
    exact abs_le.mp (h i)

lemma measurableSet_cbox (d : ℕ) (c : ℝ) : MeasurableSet (cbox d c) := by
  rw [cbox]
  exact MeasurableSet.pi Set.countable_univ (fun i _ => measurableSet_Icc)

lemma isCompact_cbox (d : ℕ) (c : ℝ) : IsCompact (cbox d c) := by
  rw [cbox]
  exact isCompact_univ_pi (fun _ => isCompact_Icc)

/-- The mean value of a real function over a set. -/
noncomputable def meanSq (d : ℕ) (S : Set (Fin d → ℝ)) (f : (Fin d → ℝ) → ℝ) : ℝ :=
  ((MeasureTheory.volume S).toReal)⁻¹ * ∫ x in S, f x

lemma meanSq_nonneg {d : ℕ} {S : Set (Fin d → ℝ)} {f : (Fin d → ℝ) → ℝ}
    (hS : 0 < (MeasureTheory.volume S).toReal) (hf : ∀ x, 0 ≤ f x) : 0 ≤ meanSq d S f := by
  rw [meanSq]
  exact mul_nonneg (inv_nonneg.mpr hS.le) (integral_nonneg hf)

/-- **The integration step of the single-cell localisation, squared form.**  The same as
`exp_level_mul_measure_le_integral` but with the *squared* pointwise bound; this is the form
needed to conclude directly about the mean of `‖G‖²` (no Cauchy–Schwarz step). -/
lemma exp2_level_mul_measure_le_integral {δ H m : ℝ} (hH0 : 0 < H)
    {G : (Fin d → ℂ) → ℂ} {J B : Set (Fin d → ℝ)}
    (hJmeas : MeasurableSet J) (hBmeas : MeasurableSet B)
    (hbad : MeasureTheory.volume B ≤ ENNReal.ofReal (20 ^ d * H))
    (hexp : ∀ x, x ∉ B → (∀ i, |x i| ≤ 1 - 2 * δ) →
      Real.exp (2 * m) ≤ ‖G (fun i => (x i : ℂ))‖ ^ 2)
    (hJwide : ∀ x ∈ J, ∀ i, |x i| ≤ 1 - 2 * δ)
    (hJfin : MeasureTheory.volume J ≠ ⊤)
    (hJbig : ENNReal.ofReal (20 ^ d * H) ≤ MeasureTheory.volume J)
    (hint : IntegrableOn (fun x : Fin d → ℝ => ‖G (fun i => (x i : ℂ))‖ ^ 2) J MeasureTheory.volume) :
    Real.exp (2 * m) * ((MeasureTheory.volume J).toReal - 20 ^ d * H)
      ≤ ∫ x in J, ‖G (fun i => (x i : ℂ))‖ ^ 2 := by
  have hJB_meas : MeasurableSet (J \ B) := hJmeas.diff hBmeas
  have hJB_sub : J \ B ⊆ J := Set.sdiff_subset
  have hJB_fin : MeasureTheory.volume (J \ B) ≠ ⊤ :=
    ne_of_lt (lt_of_le_of_lt (measure_mono hJB_sub) (lt_top_iff_ne_top.mpr hJfin))
  have h2 : MeasureTheory.volume (J \ B)
      = MeasureTheory.volume J - MeasureTheory.volume (J ∩ B) :=
    ENNReal.eq_sub_of_add_eq
      (ne_of_lt (lt_of_le_of_lt (measure_mono Set.inter_subset_left)
        (lt_top_iff_ne_top.mpr hJfin)))
      (measure_sdiff_add_inter J hBmeas)
  have h3 : MeasureTheory.volume (J ∩ B) ≤ ENNReal.ofReal (20 ^ d * H) :=
    le_trans (measure_mono Set.inter_subset_right) hbad
  have hsub : (MeasureTheory.volume J).toReal - 20 ^ d * H
      ≤ (MeasureTheory.volume (J \ B)).toReal := by
    have hle : MeasureTheory.volume (J \ B)
        ≥ MeasureTheory.volume J - ENNReal.ofReal (20 ^ d * H) := by
      rw [h2]
      exact tsub_le_tsub_left h3 _
    have := ENNReal.toReal_mono hJB_fin hle
    rwa [ENNReal.toReal_sub_of_le hJbig hJfin, ENNReal.toReal_ofReal
      (by positivity : (0:ℝ) ≤ 20 ^ d * H)] at this
  have hint' : IntegrableOn (fun x : Fin d → ℝ => ‖G (fun i => (x i : ℂ))‖ ^ 2)
      (J \ B) MeasureTheory.volume := hint.mono_set hJB_sub
  have hmono : ∫ x in J \ B, Real.exp (2 * m)
      ≤ ∫ x in J \ B, ‖G (fun i => (x i : ℂ))‖ ^ 2 :=
    setIntegral_mono_on (integrableOn_const hJB_fin) hint' hJB_meas
      (fun x hx => hexp x hx.2 (hJwide x hx.1))
  have hconst : ∫ _x in J \ B, Real.exp (2 * m)
      = Real.exp (2 * m) * (MeasureTheory.volume (J \ B)).toReal := by
    rw [setIntegral_const, MeasureTheory.Measure.real_def, smul_eq_mul, mul_comm]
  have hle : ∫ x in J \ B, ‖G (fun i => (x i : ℂ))‖ ^ 2
      ≤ ∫ x in J, ‖G (fun i => (x i : ℂ))‖ ^ 2 :=
    setIntegral_mono_set hint (Filter.Eventually.of_forall fun x => by positivity)
      (Filter.Eventually.of_forall fun x hx => hJB_sub hx)
  calc Real.exp (2 * m) * ((MeasureTheory.volume J).toReal - 20 ^ d * H)
      ≤ Real.exp (2 * m) * (MeasureTheory.volume (J \ B)).toReal :=
        mul_le_mul_of_nonneg_left hsub (Real.exp_nonneg _)
    _ = ∫ x in J \ B, Real.exp (2 * m) := hconst.symm
    _ ≤ ∫ x in J \ B, ‖G (fun i => (x i : ℂ))‖ ^ 2 := hmono
    _ ≤ ∫ x in J, ‖G (fun i => (x i : ℂ))‖ ^ 2 := hle


/-- **The single-cell Cartan estimate.**  This is the per-cell core of Han–Schlag's
`prop:locddim` in the normalised form (`M := 1` for `S⁻¹ • G`).

`G` is holomorphic on a neighbourhood of the closed unit polydisc and bounded by `S > 0` there;
`J` is a measurable subset of the box `{∀ i, |x i| ≤ 1 - 2δ}` of measure at least
`2 · 20^d H`; `m` is a level which is *witnessed* at a point of the smaller polydisc
(`hm`, which is what `cartes_polydisk_measure` needs) and which dominates the RMS of the
normalised function over the middle box (the caller takes `m := log RMS_mid(S⁻¹ • G)`).

Then the Cartan bad set has measure `≤ 20^d H` and off it — after removing the (null) zero set —
`‖S⁻¹ G‖ ≥ e^{m(1+L)^d}`; integrating over `J` and using `|J| ≥ 2·20^d H` gives
`e^{2m} ≤ (2 · mean_J ‖S⁻¹G‖²)^{1/(1+L)^d}`.

This is Han–Schlag's `prop:B1B2` with the boundary `L²`-norm `B₂` replaced by the sharp sup bound
`M := 1` (Session 57). -/
theorem cell_cartan_exp {δ H S m : ℝ} (hδ0 : 0 < δ) (hδ3 : δ < 1 / 3)
    (hH0 : 0 < H) (hH1 : H ≤ 1) (hS : 0 < S)
    (d : ℕ) (hd : 1 ≤ d) (G : (Fin d → ℂ) → ℂ)
    (hG : AnalyticOnNhd ℂ G (Metric.closedBall 0 1))
    (hSb : ∀ z : Fin d → ℂ, (∀ i, ‖z i‖ ≤ 1) → ‖G z‖ ≤ S)
    {J : Set (Fin d → ℝ)} (hJmeas : MeasurableSet J)
    (hJwide : ∀ x ∈ J, ∀ i, |x i| ≤ 1 - 2 * δ)
    (hJbig : ENNReal.ofReal (2 * (20 ^ d * H)) ≤ MeasureTheory.volume J)
    (hm : ∃ z : Fin d → ℂ, (∀ i, ‖z i‖ ≤ 1 - 3 * δ) ∧
      ((S⁻¹ : ℝ) : ℂ) * G z ≠ 0 ∧ m ≤ Real.log ‖((S⁻¹ : ℝ) : ℂ) * G z‖)
    (hintJ : IntegrableOn (fun x : Fin d → ℝ =>
      ‖((S⁻¹ : ℝ) : ℂ) * G (fun i => (x i : ℂ))‖ ^ 2) J MeasureTheory.volume) :
    Real.exp (2 * m) ≤ (2 * meanSq d J
      (fun x => ‖((S⁻¹ : ℝ) : ℂ) * G (fun i => (x i : ℂ))‖ ^ 2)) ^ (twoConstKappa δ H ^ d) := by
  classical
  set G' : (Fin d → ℂ) → ℂ := fun z => ((S⁻¹ : ℝ) : ℂ) * G z with hG'def
  set K : ℝ := (1 + twoConstK δ H) ^ d with hKdef
  have hLraw : twoConstK δ H = 2 * δ⁻¹ ^ 3 * Real.log (2 / δ) +
      δ⁻¹ ^ 2 * Real.log (2 * Real.exp 1 / H) := rfl
  -- Cartan: the bad set has small measure.
  have hCartan := cartan_polydisk_normalised (d := d) hδ0 hδ3 hH0 hH1 hS hd G hG hSb hm
  have hbad_bound : MeasureTheory.volume {x : Fin d → ℝ | (∀ i, |x i| ≤ 1 - 2 * δ) ∧
      Real.log ‖G' (fun i => (x i : ℂ))‖ < m * K} ≤ ENNReal.ofReal (20 ^ d * H) := by
    have hK : K = (1 + (2 * δ⁻¹ ^ 3 * Real.log (2 / δ) +
        δ⁻¹ ^ 2 * Real.log (2 * Real.exp 1 / H))) ^ d := by rw [hKdef, hLraw]
    rw [hK, hG'def]
    exact hCartan
  -- The bad set is measurable.
  set B : Set (Fin d → ℝ) := {x | (∀ i, |x i| ≤ 1 - 2 * δ) ∧
    Real.log ‖G' (fun i => (x i : ℂ))‖ < m * K} with hBdef
  have hG'ana : AnalyticOnNhd ℂ G' (Metric.closedBall 0 1) := by
    rw [hG'def]
    have hcs := hG.const_smul (c := ((S⁻¹ : ℝ) : ℂ))
    rw [show (((S⁻¹ : ℝ) : ℂ) • G) = fun z : Fin d → ℂ => ((S⁻¹ : ℝ) : ℂ) * G z from by
      funext z; simp [Pi.smul_apply, smul_eq_mul]] at hcs
    exact hcs
  have hBeq : B = cbox d (1 - 2 * δ) ∩ {x : Fin d → ℝ | Real.log ‖clipG G' x‖ < m * K} := by
    rw [hBdef]
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_inter_iff, mem_cbox]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨h1, ?_⟩
      rw [clipG_of_mem G' (fun i => le_trans (h1 i) (by linarith))]
      exact h2
    · rintro ⟨h1, h2⟩
      refine ⟨h1, ?_⟩
      rw [clipG_of_mem G' (fun i => le_trans (h1 i) (by linarith))] at h2
      exact h2
  have hBmeas : MeasurableSet B := by
    rw [hBeq]
    refine MeasurableSet.inter (measurableSet_cbox d _) ?_
    have hcont : Measurable (fun x : Fin d → ℝ => Real.log ‖clipG G' x‖) :=
      Real.measurable_log.comp (continuous_clipG hG'ana).norm.measurable
    exact hcont measurableSet_Iio
  -- The zero set is null.
  set Z : Set (Fin d → ℝ) := {x | (∀ i, |x i| ≤ 1) ∧ G (fun i => (x i : ℂ)) = 0} with hZdef
  obtain ⟨zw, hzw1, hzw2, -⟩ := hm
  have hzwne : G zw ≠ 0 := fun h => hzw2 (by rw [h, mul_zero])
  have hZvol : MeasureTheory.volume Z = 0 :=
    volume_zero_set_pi d G hG ⟨zw, fun i => le_trans (hzw1 i) (by linarith), hzwne⟩
  -- Off `B ∪ Z` (inside the box) the exponential lower bound holds.
  have hexp : ∀ x, x ∉ B ∪ Z → (∀ i, |x i| ≤ 1 - 2 * δ) →
      Real.exp (2 * (m * K)) ≤ ‖G' (fun i => (x i : ℂ))‖ ^ 2 := by
    intro x hx hxw
    have hxB : x ∉ B := fun h => hx (Or.inl h)
    have hxZ : x ∉ Z := fun h => hx (Or.inr h)
    have hlog : m * K ≤ Real.log ‖G' (fun i => (x i : ℂ))‖ := by
      by_contra h
      exact hxB (by rw [hBdef]; exact ⟨hxw, lt_of_not_ge h⟩)
    have hz1 : ∀ i, |x i| ≤ 1 := fun i => le_trans (hxw i) (by linarith)
    have hz : G (fun i => (x i : ℂ)) ≠ 0 := by
      intro h0
      exact hxZ (by rw [hZdef]; exact ⟨hz1, h0⟩)
    have hcnz : ((S⁻¹ : ℝ) : ℂ) ≠ 0 := by
      simp only [ne_eq, Complex.ofReal_eq_zero]
      exact inv_ne_zero (ne_of_gt hS)
    have hnz : G' (fun i => (x i : ℂ)) ≠ 0 := by
      rw [hG'def]
      exact mul_ne_zero hcnz hz
    have h1 : Real.exp (m * K) ≤ ‖G' (fun i => (x i : ℂ))‖ := by
      calc Real.exp (m * K) ≤ Real.exp (Real.log ‖G' (fun i => (x i : ℂ))‖) :=
            Real.exp_le_exp.mpr hlog
        _ = ‖G' (fun i => (x i : ℂ))‖ := Real.exp_log (norm_pos_iff.mpr hnz)
    calc Real.exp (2 * (m * K)) = Real.exp (m * K) * Real.exp (m * K) := by
          rw [show 2 * (m * K) = (m * K) + (m * K) by ring, Real.exp_add]
      _ = (Real.exp (m * K)) ^ 2 := by ring
      _ ≤ ‖G' (fun i => (x i : ℂ))‖ ^ 2 :=
          pow_le_pow_left₀ (Real.exp_nonneg _) h1 2
  -- Measurability and measure of the enlarged bad set.
  have hZeq : Z = cbox d 1 ∩ {x : Fin d → ℝ | clipG G x = 0} := by
    rw [hZdef]
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_inter_iff, mem_cbox]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h1, by rw [clipG_of_mem G h1]; exact h2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨h1, by rw [clipG_of_mem G h1] at h2; exact h2⟩
  have hZmeas : MeasurableSet Z := by
    rw [hZeq]
    exact MeasurableSet.inter (measurableSet_cbox d 1)
      ((isClosed_singleton.preimage (continuous_clipG hG)).measurableSet)
  have hB'meas : MeasurableSet (B ∪ Z) := hBmeas.union hZmeas
  have hB'bad : MeasureTheory.volume (B ∪ Z) ≤ ENNReal.ofReal (20 ^ d * H) := by
    have h1 : MeasureTheory.volume (B ∪ Z) ≤ MeasureTheory.volume B + MeasureTheory.volume Z :=
      measure_union_le B Z
    rw [hZvol, add_zero] at h1
    exact le_trans h1 hbad_bound
  -- The integral bound.
  have hJfin : MeasureTheory.volume J ≠ ⊤ := by
    refine ne_of_lt (lt_of_le_of_lt (measure_mono ?_) (isCompact_cbox d (1 - 2 * δ)).measure_lt_top)
    intro x hx
    exact (mem_cbox).mpr (hJwide x hx)
  have hJbig' : ENNReal.ofReal (20 ^ d * H) ≤ MeasureTheory.volume J := by
    have h0 : (0 : ℝ) ≤ 20 ^ d * H := by positivity
    refine le_trans (ENNReal.ofReal_le_ofReal ?_) hJbig
    linarith
  have hInt := exp2_level_mul_measure_le_integral (δ := δ) (H := H) (m := m * K)
    (G := G') hH0 hJmeas hB'meas hB'bad hexp hJwide hJfin hJbig'
    (by simpa [hG'def] using hintJ)
  -- `|J| - 20^d H ≥ |J|/2`.
  have htwo : 2 * (20 ^ d * H) ≤ (MeasureTheory.volume J).toReal := by
    have h1 : (0 : ℝ) ≤ 2 * (20 ^ d * H) := by positivity
    have h3 : ENNReal.ofReal (2 * (20 ^ d * H)) ≠ ⊤ := ENNReal.ofReal_ne_top
    have h4 := (ENNReal.toReal_le_toReal h3 hJfin).mpr hJbig
    rwa [ENNReal.toReal_ofReal h1] at h4
  have hVJpos : 0 < (MeasureTheory.volume J).toReal := by
    have h5 : (0 : ℝ) < 2 * (20 ^ d * H) := by positivity
    linarith
  have hV : (MeasureTheory.volume J).toReal / 2 ≤
      (MeasureTheory.volume J).toReal - 20 ^ d * H := by linarith
  have hhalf : Real.exp (2 * (m * K)) * ((MeasureTheory.volume J).toReal / 2) ≤
      ∫ x in J, ‖G' (fun i => (x i : ℂ))‖ ^ 2 :=
    le_trans (mul_le_mul_of_nonneg_left hV (Real.exp_nonneg _)) hInt
  have hmean : Real.exp (2 * (m * K)) / 2 ≤ meanSq d J
      (fun x => ‖G' (fun i => (x i : ℂ))‖ ^ 2) := by
    have h1 := div_le_div_of_nonneg_right hhalf hVJpos.le
    have h2 : Real.exp (2 * (m * K)) * ((MeasureTheory.volume J).toReal / 2) /
        (MeasureTheory.volume J).toReal = Real.exp (2 * (m * K)) / 2 := by
      field_simp
    rw [h2] at h1
    simpa [meanSq, div_eq_inv_mul] using h1
  -- Algebra: `(e^{2m})^K ≤ 2 mean`, hence `e^{2m} ≤ (2 mean)^{1/K}`.
  have hexpK : Real.exp (2 * (m * K)) = (Real.exp (2 * m)) ^ K := by
    rw [show 2 * (m * K) = (2 * m) * K by ring, Real.exp_mul]
  have hcK : Real.exp (2 * m) ^ K ≤ 2 * meanSq d J
      (fun x => ‖G' (fun i => (x i : ℂ))‖ ^ 2) := by
    rw [← hexpK]
    linarith
  have hcnn : 0 ≤ 2 * meanSq d J (fun x => ‖G' (fun i => (x i : ℂ))‖ ^ 2) :=
    mul_nonneg (by norm_num) (meanSq_nonneg hVJpos (fun x => sq_nonneg _))
  have hKpos : 0 < K := by
    have hL0 : 0 ≤ twoConstK δ H := twoConstK_nonneg hδ0 hδ3 hH0 hH1
    rw [hKdef]
    positivity
  set κ : ℝ := twoConstKappa δ H ^ d with hκdef
  have hKκ : K * κ = 1 := by
    have hL0 : 0 ≤ twoConstK δ H := twoConstK_nonneg hδ0 hδ3 hH0 hH1
    rw [hκdef, hKdef, twoConstKappa, inv_pow]
    exact mul_inv_cancel₀ (pow_ne_zero d (by linarith))
  have hfinal : Real.exp (2 * m) ≤ (2 * meanSq d J
      (fun x => ‖G' (fun i => (x i : ℂ))‖ ^ 2)) ^ κ := by
    calc Real.exp (2 * m) = ((Real.exp (2 * m)) ^ K) ^ κ := by
          rw [← Real.rpow_mul (Real.exp_nonneg _), hKκ, Real.rpow_one]
      _ ≤ (2 * meanSq d J (fun x => ‖G' (fun i => (x i : ℂ))‖ ^ 2)) ^ κ :=
          Real.rpow_le_rpow (Real.rpow_nonneg (Real.exp_nonneg _) _) hcK (by
            obtain ⟨h1, -⟩ := twoConstKappa_mem hδ0 hδ3 hH0 hH1
            rw [hκdef]
            positivity)
  rw [hG'def] at hfinal
  exact hfinal

end Submission.FUP
