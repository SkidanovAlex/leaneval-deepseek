import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

namespace Commons.Geometry.Ulam

open MeasureTheory
open scoped RealInnerProductSpace

/-- A convenient version of `HasDerivAt` for real-valued functions of a real variable,
using the normed algebra module structure.  This makes the derivative lemmas in mathlib
(which are stated for normed algebras) match the statements used in the FTC arguments. -/
abbrev ballCapHasDerivAtR (f : ℝ → ℝ) (f' x : ℝ) : Prop :=
  @HasDerivAt ℝ _ ℝ Real.normedCommRing.toCommRing.toAddCommGroup
    (NormedAlgebra.toNormedSpace ℝ).toModule
    Real.pseudoMetricSpace.toUniformSpace.toTopologicalSpace
    (inferInstance : ContinuousSMul ℝ ℝ) f f' x

lemma ballCap_hasDerivAt_u {r x : ℝ} :
    ballCapHasDerivAtR (fun t : ℝ => r ^ 2 - t ^ 2) (-2 * x) x := by
  have h1 : ballCapHasDerivAtR (fun t : ℝ => r ^ 2) (0 : ℝ) x := hasDerivAt_const x (r ^ 2)
  have h2 : ballCapHasDerivAtR (fun t : ℝ => t ^ 2) (2 * x) x := by
    simpa using (hasDerivAt_pow 2 (x : ℝ))
  have h := h1.sub h2
  convert h using 1
  all_goals first
    | (ext t; simp)
    | (ring)
    | rfl

lemma ballCap_hasDerivAt_pow_sqrt {n : ℕ} {r x : ℝ} (hn : 1 ≤ n) (hx : -r < x) (hxr : x < r) :
    ballCapHasDerivAtR (fun t : ℝ => (r ^ 2 - t ^ 2) ^ n * Real.sqrt (r ^ 2 - t ^ 2))
      (-(2 * (n : ℝ) + 1) * x * (r ^ 2 - x ^ 2) ^ (n - 1) * Real.sqrt (r ^ 2 - x ^ 2)) x := by
  have hpos : 0 < r ^ 2 - x ^ 2 := by
    have hsq_lt : x ^ 2 < r ^ 2 := sq_lt_sq' hx hxr
    linarith
  have hne : r ^ 2 - x ^ 2 ≠ 0 := ne_of_gt hpos
  have hu : ballCapHasDerivAtR (fun t : ℝ => r ^ 2 - t ^ 2) (-2 * x) x := ballCap_hasDerivAt_u
  have hpow : ballCapHasDerivAtR (fun t : ℝ => (r ^ 2 - t ^ 2) ^ n)
      ((n : ℝ) * (r ^ 2 - x ^ 2) ^ (n - 1) * (-2 * x)) x := by
    convert hu.pow n using 1
    all_goals first
      | (ext t; simp)
      | rfl
  have hsqrt : ballCapHasDerivAtR (fun t : ℝ => Real.sqrt (r ^ 2 - t ^ 2))
      ((-2 * x) / (2 * Real.sqrt (r ^ 2 - x ^ 2))) x := by
    exact hu.sqrt hne
  have hprod := hpow.mul hsqrt
  have hder : ballCapHasDerivAtR (fun t : ℝ => (r ^ 2 - t ^ 2) ^ n * Real.sqrt (r ^ 2 - t ^ 2))
      (((n : ℝ) * (r ^ 2 - x ^ 2) ^ (n - 1) * (-2 * x)) * Real.sqrt (r ^ 2 - x ^ 2)
        + (r ^ 2 - x ^ 2) ^ n * ((-2 * x) / (2 * Real.sqrt (r ^ 2 - x ^ 2)))) x := by
    convert hprod using 1
    all_goals first
      | (ext t; simp)
      | rfl
  have hsqrt_pos : 0 < Real.sqrt (r ^ 2 - x ^ 2) := Real.sqrt_pos.2 hpos
  have hsqrt_ne : Real.sqrt (r ^ 2 - x ^ 2) ≠ 0 := ne_of_gt hsqrt_pos
  convert hder using 1
  · have hu0 : 0 ≤ r ^ 2 - x ^ 2 := le_of_lt hpos
    have hsq : Real.sqrt (r ^ 2 - x ^ 2) ^ 2 = r ^ 2 - x ^ 2 := Real.sq_sqrt hu0
    have hsucc : (r ^ 2 - x ^ 2) ^ n = (r ^ 2 - x ^ 2) ^ (n - 1) * (r ^ 2 - x ^ 2) := by
      obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
      simp [pow_succ]
    field_simp [hsqrt_ne]
    rw [hsq]
    rw [hsucc]
    ring

lemma ballCap_hasDerivAt_antideriv {n : ℕ} {r x : ℝ} (hn : 1 ≤ n) (hx : -r < x) (hxr : x < r) :
    ballCapHasDerivAtR
      (fun t : ℝ => -((r ^ 2 - t ^ 2) ^ n * Real.sqrt (r ^ 2 - t ^ 2)) / (2 * (n : ℝ) + 1))
      (x * (r ^ 2 - x ^ 2) ^ (n - 1) * Real.sqrt (r ^ 2 - x ^ 2)) x := by
  have hH := ballCap_hasDerivAt_pow_sqrt hn hx hxr
  let c : ℝ := 2 * (n : ℝ) + 1
  have hc : c ≠ 0 := by
    dsimp [c]
    have hn0 : 0 ≤ (n : ℝ) := by exact_mod_cast Nat.zero_le n
    linarith
  have hneg := hH.neg
  have hdiv := hneg.div_const c
  convert hdiv using 1
  all_goals first
    | (ext t; simp [c])
    | (dsimp [c] at *; field_simp [hc])
    | rfl

lemma ball_cap_first_moment_eq {n : ℕ} {r L : ℝ} (hn : 1 ≤ n) (hr : 0 ≤ r)
    (hL_lower : -r ≤ L) (hL_upper : L ≤ r) :
    (∫ z in (-r)..L, z * (r ^ 2 - z ^ 2) ^ (n - 1) * Real.sqrt (r ^ 2 - z ^ 2)) =
      - ((r ^ 2 - L ^ 2) ^ n * Real.sqrt (r ^ 2 - L ^ 2)) / (2 * (n : ℝ) + 1) := by
  let F : ℝ → ℝ := fun t => -((r ^ 2 - t ^ 2) ^ n * Real.sqrt (r ^ 2 - t ^ 2)) / (2 * (n : ℝ) + 1)
  let f' : ℝ → ℝ := fun z => z * (r ^ 2 - z ^ 2) ^ (n - 1) * Real.sqrt (r ^ 2 - z ^ 2)
  have hcontF : ContinuousOn F (Set.Icc (-r) L) := by
    have hcont : Continuous F := by
      unfold F
      continuity
    exact hcont.continuousOn
  have hderiv : ∀ x ∈ Set.Ioo (-r) L, HasDerivAt F (f' x) x := by
    intro x hx
    have hx_lower : -r < x := hx.1
    have hx_upper : x < L := hx.2
    have hxr : x < r := lt_of_lt_of_le hx_upper hL_upper
    have h := ballCap_hasDerivAt_antideriv hn hx_lower hxr
    simpa [F, f', ballCapHasDerivAtR] using h
  have hint : IntervalIntegrable f' volume (-r) L := by
    have hcont : Continuous f' := by
      unfold f'
      continuity
    exact hcont.intervalIntegrable _ _
  have hmain := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le (a := -r) (b := L) (f := F) (f' := f')
    hL_lower hcontF hderiv hint
  have hFL : F L = - ((r ^ 2 - L ^ 2) ^ n * Real.sqrt (r ^ 2 - L ^ 2)) / (2 * (n : ℝ) + 1) := by
    unfold F
    simp
  have hFmr : F (-r) = 0 := by
    unfold F
    have hzero : r ^ 2 - (-r) ^ 2 = 0 := by ring
    simp [hzero]
  calc
    ∫ z in (-r)..L, f' z = F L - F (-r) := by simpa [f'] using hmain
    _ = - ((r ^ 2 - L ^ 2) ^ n * Real.sqrt (r ^ 2 - L ^ 2)) / (2 * (n : ℝ) + 1) := by
      rw [hFL, hFmr, sub_zero]

end Commons.Geometry.Ulam