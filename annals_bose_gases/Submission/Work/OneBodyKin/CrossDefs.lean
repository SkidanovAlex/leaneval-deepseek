import Mathlib.MeasureTheory.Group.Integral
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BSKinetic.integrable_bsJoint_J1
import Submission.Work.OneBodyKin.bsMean_eq_boxMean
import Submission.Work.OneBodyKin.bsPair_eq_cos
import Submission.Work.OneBodyKin.integrable_bsKern
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.OneBodyKin.CrossDefs` — the pieces of the cross-term kernel computation

The cross term `∫_u bsMean ℓ u ψ · bsPair ℓ F u ψ du` is computed by rewriting
`bsPair` (via `bsPair_eq_cos`) as the cosine integral

  `bsPair ℓ F u ψ = (2π)⁻³ ℓ⁶ ∫_p F‖p‖ profHat(ℓp) ∫_v χ v ψ(ℓ(v+u)) cos⟪ℓp,v⟫ dv`,

expanding the box mean (`bsMean_eq_boxMean`) and carrying out three substitutions
(`u ↦ x = ℓ(u+s)`, `v ↦ d = ℓ(v-s)`, and the RHS `y ↦ x + d`), which turns it into the
quadratic form of the convolution kernel `bsKern`.  This module collects the three auxiliary
functions the computation is phrased with:

* `bsMf ℓ ψ u = ∫_{s∈acube 1} ψ(ℓ(u+s))` (the box mean, `bsMf_eq_bsMean`);
* `bsLf ℓ F p v = F ‖p‖ · profHat(ℓp) · χ v · cos⟪ℓp,v⟫` (the `(p,v)`-factor);
* `bsAc ψ d = ∫_x ψ x · ψ(x+d)` (the autocorrelation of the test function),

together with the elementary facts about them that the main computation uses.
-/

noncomputable section

open MeasureTheory

namespace Work.OneBodyKin

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

open Submission.BoseGases

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option linter.unusedVariables false

/-- The box mean of `ψ` at `u`, written on the unit cube: `bsMf ℓ ψ u = ∫_{s∈acube 1} ψ(ℓ(u+s))`. -/
noncomputable def bsMf (ℓ : ℝ) (ψ : ℝ³ → ℝ) (u : ℝ³) : ℝ := ∫ s in acube 1, ψ (ℓ • (u + s))

/-- The `(p,v)`-factor of the cosine form of the cross term:
`bsLf ℓ F p v = F ‖p‖ · profHat(ℓ•p) · χ v · cos⟪ℓ•p, v⟫`. -/
noncomputable def bsLf (ℓ : ℝ) (F : ℝ → ℝ) (p v : ℝ³) : ℝ :=
  F ‖p‖ * profHat (ℓ • p) * chi v * Real.cos (inner ℝ (ℓ • p) v)

/-- The autocorrelation of the test function: `bsAc ψ d = ∫_x ψ x · ψ(x+d)`. -/
noncomputable def bsAc (ψ : ℝ³ → ℝ) (d : ℝ³) : ℝ := ∫ x, ψ x * ψ (x + d)

/-- `bsMf` is the box mean: `bsMf ℓ ψ u = bsMean ℓ u ψ`. -/
lemma bsMf_eq_bsMean {ℓ : ℝ} (hℓ : 0 < ℓ) (ψ : ℝ³ → ℝ) (u : ℝ³) :
    bsMf ℓ ψ u = Work.BSKinetic.bsMean ℓ u ψ :=
  (bsMean_eq_boxMean hℓ ψ u).symm

/-- The unit cube is invariant under negation. -/
lemma neg_mem_acube_one (s : ℝ³) : -s ∈ acube 1 ↔ s ∈ acube 1 := by
  simp only [mem_acube_iff]
  constructor
  · intro h m
    have hm := h m
    simp only [PiLp.neg_apply] at hm
    exact ⟨by linarith [hm.2], by linarith [hm.1]⟩
  · intro h m
    have hm := h m
    simp only [PiLp.neg_apply]
    exact ⟨by linarith [hm.2], by linarith [hm.1]⟩

/-- Negation is a measure preserving substitution for the set integral over the symmetric cube. -/
lemma setIntegral_neg_acube (H : ℝ³ → ℝ) :
    (∫ s in acube 1, H (-s)) = ∫ s in acube 1, H s := by
  rw [← integral_indicator (acube_measurable 1), ← integral_indicator (acube_measurable 1)]
  rw [← integral_comp_neg (fun u : ℝ³ => (acube 1).indicator (fun s : ℝ³ => H (-s)) u)]
  apply integral_congr_ae
  filter_upwards with u
  by_cases hu : u ∈ acube 1
  · have hnu : -u ∈ acube 1 := (neg_mem_acube_one u).mpr hu
    rw [Set.indicator_of_mem hnu, Set.indicator_of_mem hu]
    simp
  · have hnu : -u ∉ acube 1 := fun hc => hu ((neg_mem_acube_one u).mp hc)
    rw [Set.indicator_of_notMem hnu, Set.indicator_of_notMem hu]

/-- **The cross kernel is even**: `bsKern ℓ F (-d) = bsKern ℓ F d` (the substitution `s ↦ -s` of
the symmetric cube, together with the parity of `χ` and `cos`). -/
lemma bsKern_even (ℓ : ℝ) (F : ℝ → ℝ) (d : ℝ³) : bsKern ℓ F (-d) = bsKern ℓ F d := by
  rw [bsKern_def, bsKern_def]
  rw [← setIntegral_neg_acube (H := fun s => ∫ p : ℝ³, F ‖p‖ * profHat (ℓ • p) *
        (chi (s + ℓ⁻¹ • (-d)) * Real.cos (inner ℝ (ℓ • p) (s + ℓ⁻¹ • (-d)))))]
  refine setIntegral_congr_fun (acube_measurable 1) (fun s _ => ?_)
  apply integral_congr_ae
  filter_upwards with p
  have h1 : ((-s) + ℓ⁻¹ • (-d)) = -(s + ℓ⁻¹ • d) := by module
  rw [h1, chi_even, inner_neg_right, Real.cos_neg]

/-- **The autocorrelation is even**: `bsAc ψ (-d) = bsAc ψ d`. -/
lemma bsAc_even (ψ : ℝ³ → ℝ) (d : ℝ³) : bsAc ψ (-d) = bsAc ψ d := by
  rw [bsAc, bsAc]
  rw [← integral_add_right_eq_self (f := fun x : ℝ³ => ψ x * ψ (x + (-d))) d]
  apply integral_congr_ae
  filter_upwards with x
  simp only [add_neg_cancel_right]
  ring


/-! ## Elementary bounds

The three ingredients that make every Fubini step of the cross-term computation valid: the test
function `ψ` is bounded and vanishes outside a ball, the box mean `bsMf ℓ ψ` is bounded and
supported in a compact set, and the `(p,v)`-factor `bsLf` is dominated by
`(∫|χ|)·|F ‖p‖|·|χ v|` (the only `L¹` factor being `p ↦ F ‖p‖`). -/

/-- A smooth compactly supported function is bounded. -/
lemma exists_bound_of_contDiff_hasCompactSupport {ψ : ℝ³ → ℝ} (hψ : ContDiff ℝ (⊤ : ENat) ψ)
    (hcs : HasCompactSupport ψ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ x, |ψ x| ≤ C := by
  obtain ⟨C, hC⟩ := hcs.exists_bound_of_continuous hψ.continuous
  refine ⟨C, le_trans (norm_nonneg (ψ 0)) (by simpa [Real.norm_eq_abs] using hC 0), fun x => ?_⟩
  simpa [Real.norm_eq_abs] using hC x

/-- A compactly supported function vanishes outside a ball. -/
lemma exists_radius_eq_zero_of_hasCompactSupport {ψ : ℝ³ → ℝ} (hcs : HasCompactSupport ψ) :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ x, R ≤ ‖x‖ → ψ x = 0 :=
  Work.BSKinetic.Decomp.exists_radius_eq_zero_of_hasCompactSupport hcs

/-- **The box mean is bounded and compactly supported**: there are `C ≥ 0` and a compact set `K`
with `|bsMf ℓ ψ u| ≤ C · 1_K(u)` for every `u`. -/
lemma bsMf_bound {ℓ : ℝ} (hℓ : 0 < ℓ) {ψ : ℝ³ → ℝ} (hψ : ContDiff ℝ (⊤ : ENat) ψ)
    (hcs : HasCompactSupport ψ) :
    ∃ (C : ℝ) (K : Set ℝ³), 0 ≤ C ∧ IsCompact K ∧
      ∀ u : ℝ³, |bsMf ℓ ψ u| ≤ C * K.indicator (fun _ => (1 : ℝ)) u := by
  obtain ⟨R, _hR0, hzero⟩ := exists_radius_eq_zero_of_hasCompactSupport hcs
  obtain ⟨Cψ, hCψ⟩ := hcs.exists_bound_of_continuous hψ.continuous
  have hCψ0 : 0 ≤ Cψ := le_trans (norm_nonneg (ψ 0)) (hCψ 0)
  refine ⟨(volume : Measure ℝ³).real (acube 1) * Cψ, Metric.closedBall (0 : ℝ³) ((R + ℓ) / ℓ),
    by positivity, isCompact_closedBall _ _, fun u => ?_⟩
  by_cases hu : u ∈ Metric.closedBall (0 : ℝ³) ((R + ℓ) / ℓ)
  · rw [Set.indicator_of_mem hu, mul_one]
    have hb : ∀ s ∈ acube 1, ‖ψ (ℓ • (u + s))‖ ≤ Cψ := fun s _ => hCψ _
    have h1 := norm_setIntegral_le_of_norm_le_const (μ := (volume : Measure ℝ³))
      (s := acube 1) (f := fun s : ℝ³ => ψ (ℓ • (u + s))) (C := Cψ)
      (acube_lt_top 1 (by norm_num)) hb
    calc |bsMf ℓ ψ u| = ‖bsMf ℓ ψ u‖ := (Real.norm_eq_abs _).symm
      _ = ‖∫ s in acube 1, ψ (ℓ • (u + s))‖ := by rw [bsMf]
      _ ≤ Cψ * (volume : Measure ℝ³).real (acube 1) := h1
      _ = (volume : Measure ℝ³).real (acube 1) * Cψ := by ring
  · rw [Set.indicator_of_notMem hu, mul_zero]
    have hzero' : bsMf ℓ ψ u = 0 := by
      rw [bsMf_eq_bsMean (ℓ := ℓ) hℓ ψ u]
      by_contra hne
      have hlt := Work.BSKinetic.bs_norm_smul_lt_of_bsMean_ne_zero hℓ hzero hne
      have h1 : ℓ * ‖u‖ < R + ℓ := by
        rw [Work.BSKinetic.bs_norm_smul_eq hℓ]
        exact hlt
      refine hu ?_
      rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]
      exact le_of_lt ((lt_div_iff₀ hℓ).mpr (by rw [mul_comm]; exact h1))
    rw [hzero', abs_zero]

/-- The `(p,v)`-factor `bsLf` is dominated by `(∫|χ|)·|F ‖p‖|·|χ v|`. -/
lemma abs_bsLf_le (ℓ : ℝ) (F : ℝ → ℝ) (p v : ℝ³) :
    |bsLf ℓ F p v| ≤ (∫ z : ℝ³, |chi z|) * |F ‖p‖| * |chi v| := by
  have hC : 0 ≤ ∫ z : ℝ³, |chi z| := integral_nonneg fun z => abs_nonneg _
  calc |bsLf ℓ F p v|
      = |F ‖p‖| * |profHat (ℓ • p)| * |chi v| * |Real.cos (inner ℝ (ℓ • p) v)| := by
        rw [bsLf]; simp only [abs_mul]
    _ ≤ |F ‖p‖| * (∫ z : ℝ³, |chi z|) * |chi v| * 1 := by
        gcongr
        · exact abs_profHat_le _
        · exact Real.abs_cos_le_one _
    _ = (∫ z : ℝ³, |chi z|) * |F ‖p‖| * |chi v| := by ring

/-- The autocorrelation `bsAc` is bounded, `|bsAc ψ d| ≤ C²·|ball 0 R|`, when `|ψ| ≤ C` and `ψ`
vanishes outside the ball of radius `R`. -/
lemma abs_bsAc_le {ψ : ℝ³ → ℝ} {C R : ℝ} (hC : ∀ x, |ψ x| ≤ C)
    (hR : ∀ x, R ≤ ‖x‖ → ψ x = 0) (d : ℝ³) :
    |bsAc ψ d| ≤ C ^ 2 * (volume : Measure ℝ³).real (Metric.closedBall (0 : ℝ³) R) := by
  have hμ : (volume : Measure ℝ³) (Metric.closedBall (0 : ℝ³) R) < ⊤ :=
    (isCompact_closedBall (0 : ℝ³) R).measure_lt_top
  have heq : bsAc ψ d = ∫ x in Metric.closedBall (0 : ℝ³) R, ψ x * ψ (x + d) := by
    rw [bsAc, ← integral_indicator measurableSet_closedBall]
    apply integral_congr_ae
    filter_upwards with x
    by_cases hx : x ∈ Metric.closedBall (0 : ℝ³) R
    · rw [Set.indicator_of_mem hx]
    · rw [Set.indicator_of_notMem hx]
      have hx' : R < ‖x‖ := by
        rw [Metric.mem_closedBall, dist_eq_norm, sub_zero, not_le] at hx
        exact hx
      rw [hR x (le_of_lt hx'), zero_mul]
  rw [heq]
  refine le_trans ?_ (norm_setIntegral_le_of_norm_le_const (μ := (volume : Measure ℝ³))
    (s := Metric.closedBall (0 : ℝ³) R) (f := fun x : ℝ³ => ψ x * ψ (x + d)) (C := C ^ 2) hμ ?_)
  · rw [Real.norm_eq_abs]
  · intro x hx
    rw [norm_mul]
    have h1 : ‖ψ x‖ ≤ C := by rw [Real.norm_eq_abs]; exact hC x
    have h2 : ‖ψ (x + d)‖ ≤ C := by
      by_cases hxd : x + d ∈ Metric.closedBall (0 : ℝ³) R
      · rw [Real.norm_eq_abs]; exact hC _
      · rw [Metric.mem_closedBall, dist_eq_norm, sub_zero, not_le] at hxd
        rw [hR (x + d) (le_of_lt hxd), norm_zero]
        exact le_trans (abs_nonneg _) (hC 0)
    calc ‖ψ x‖ * ‖ψ (x + d)‖ ≤ C * C :=
          mul_le_mul h1 h2 (norm_nonneg _) (le_trans (abs_nonneg _) (hC 0))
      _ = C ^ 2 := by ring

end Work.OneBodyKin
