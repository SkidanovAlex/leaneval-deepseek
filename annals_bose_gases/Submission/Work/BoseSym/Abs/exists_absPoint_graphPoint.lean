import Mathlib.Order.CompletePartialOrder
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.MeasureTheory.Function.LpOrder
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.BoseSym.Abs.fderiv_sqrtSq_sub
import Submission.Work.BoseSym.Abs.gSq_graphPoint_le
import Submission.Work.BoseSym.Abs.tendsto_toLp_of_dominated
import Submission.Work.BoseSym.Basic.exists_graphPoint_close
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# BoseSym.Abs — the absolute value of a graph point

For a test function `F` supported in the open box we produce an element `q` of
the Dirichlet energy space `Hsub N L` whose function part equals `|F|` almost
everywhere and whose gradient norm squared is at most that of
`graphPoint N L F`.

The construction approximates `|F|` by the smooth functions
`Gₙ = √(F² + aₙ²) - aₙ` with `aₙ = (n+1)⁻¹ ↓ 0`.  Each `Gₙ` is a test function
(`absG`, `GT`), and

* `0 ≤ Gₙ ≤ |F|` and `Gₙ → |F|` pointwise (`absG_nonneg`, `absG_le_abs`,
  `absG_tendsto`);
* `∇Gₙ = cₙ ∇F` with `cₙ = F/√(F² + aₙ²)` (`GT_fderiv`), so `|∇Gₙ| ≤ |∇F|`
  pointwise (`absCoef_abs_le_one`);
* `cₙ → sgnZ F` pointwise (`absCoef_tendsto_sgnZ`).

Hence `graphPoint N L Gₙ` converges in the ambient space `Amb N` to the pair
`(|F|, sgnZ(F) ∇F)` (`absT`, `hJT`), whose function part is `|F|` and whose
gradient norm squared is at most `gSq (graphPoint N L F)`.
-/

namespace Work.BoseSym.Abs

open MeasureTheory Filter
open scoped Topology Real ENNReal ContDiff

noncomputable section

set_option autoImplicit false

/-! ## The shrinking parameter -/

/-- The parameter `aₙ = (n+1)⁻¹ ↓ 0`. -/
def absA (n : ℕ) : ℝ := ((n : ℝ) + 1)⁻¹

lemma absA_pos (n : ℕ) : 0 < absA n := by
  rw [absA]; positivity

lemma absA_le_one (n : ℕ) : absA n ≤ 1 := by
  have h2 : (1 : ℝ) ≤ (n : ℝ) + 1 := by
    have := Nat.cast_nonneg (α := ℝ) n; linarith
  rw [absA]
  calc ((n : ℝ) + 1)⁻¹ ≤ (1 : ℝ)⁻¹ := inv_anti₀ one_pos h2
    _ = 1 := inv_one

lemma absA_tendsto : Tendsto absA atTop (𝓝 0) := by
  have h : absA = fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1) := by
    funext n; simp [absA, one_div]
  rw [h]
  exact tendsto_one_div_add_atTop_nhds_zero_nat

/-! ## The smooth approximant `√(F² + a²) - a` of `|F|` -/

/-- The smooth function `x ↦ √(F x ^ 2 + a ^ 2) - a`, which approximates `|F|`
as `a ↓ 0` and vanishes wherever `F` does. -/
def absG {N : ℕ} (F : Conf N → ℝ) (a : ℝ) : Conf N → ℝ :=
  fun x => Real.sqrt ((F x) ^ 2 + a ^ 2) - a

lemma absG_eq {N : ℕ} (F : Conf N → ℝ) (a : ℝ) :
    absG F a = fun x => Real.sqrt ((F x) ^ 2 + a ^ 2) - a := rfl

lemma absG_contDiff {N : ℕ} {F : Conf N → ℝ} (hF : ContDiff ℝ ∞ F) {a : ℝ} (ha : 0 < a) :
    ContDiff ℝ ∞ (absG F a) := by
  have hu : ContDiff ℝ ∞ (fun x => (F x) ^ 2 + a ^ 2) := (hF.pow 2).add contDiff_const
  have hne : ∀ x, (F x) ^ 2 + a ^ 2 ≠ 0 := fun x => by positivity
  have hs : ContDiff ℝ ∞ (fun x => Real.sqrt ((F x) ^ 2 + a ^ 2)) := hu.sqrt hne
  rw [absG_eq]
  exact hs.sub contDiff_const

lemma absG_apply_zero {N : ℕ} {F : Conf N → ℝ} {a : ℝ} (ha : 0 < a) {x : Conf N}
    (hx : F x = 0) : absG F a x = 0 := by
  rw [absG, hx]
  simp [Real.sqrt_sq_eq_abs, abs_of_pos ha]

lemma absG_support_subset {N : ℕ} {F : Conf N → ℝ} {a : ℝ} (ha : 0 < a) :
    Function.support (absG F a) ⊆ Function.support F := by
  intro x hx
  by_contra h
  exact hx (absG_apply_zero ha (not_not.mp h))

lemma absG_tsupport_subset {N : ℕ} {F : Conf N → ℝ} {a : ℝ} (ha : 0 < a) :
    tsupport (absG F a) ⊆ tsupport F := by
  simp only [tsupport]
  exact closure_mono (absG_support_subset ha)

lemma absG_nonneg {N : ℕ} {F : Conf N → ℝ} {a : ℝ} (ha : 0 < a) (x : Conf N) :
    0 ≤ absG F a x := by
  rw [absG]
  have h1 : a ^ 2 ≤ (F x) ^ 2 + a ^ 2 := by nlinarith [sq_nonneg (F x)]
  have h2 := Real.sqrt_le_sqrt h1
  rw [Real.sqrt_sq_eq_abs, abs_of_pos ha] at h2
  linarith

lemma absG_le_abs {N : ℕ} {F : Conf N → ℝ} {a : ℝ} (ha : 0 < a) (x : Conf N) :
    absG F a x ≤ |F x| := by
  rw [absG]
  have h1 : (F x) ^ 2 + a ^ 2 ≤ (|F x| + a) ^ 2 := by
    rw [add_sq, sq_abs]
    nlinarith [abs_nonneg (F x), le_of_lt ha]
  have h2 := Real.sqrt_le_sqrt h1
  rw [Real.sqrt_sq (by positivity : (0 : ℝ) ≤ |F x| + a)] at h2
  linarith

lemma absG_sub_abs_le {N : ℕ} {F : Conf N → ℝ} {a : ℝ} (ha : 0 < a) (x : Conf N) :
    abs (absG F a x - |F x|) ≤ |F x| := by
  have h1 := absG_nonneg (F := F) ha x
  have h2 := absG_le_abs (F := F) ha x
  rw [abs_sub_le_iff]
  exact ⟨by linarith, by linarith⟩

lemma absG_tendsto {N : ℕ} {F : Conf N → ℝ} (x : Conf N) :
    Tendsto (fun n => absG F (absA n) x) atTop (𝓝 |F x|) := by
  have hsq : Tendsto (fun n => (F x) ^ 2 + (absA n) ^ 2) atTop (𝓝 ((F x) ^ 2)) := by
    have h0 : (0 : ℝ) ^ 2 = 0 := by norm_num
    simpa [h0] using tendsto_const_nhds.add (absA_tendsto.pow 2)
  have hs : Tendsto (fun n => Real.sqrt ((F x) ^ 2 + (absA n) ^ 2)) atTop
      (𝓝 (Real.sqrt ((F x) ^ 2))) :=
    (Real.continuous_sqrt.tendsto ((F x) ^ 2)).comp hsq
  have h := hs.sub absA_tendsto
  simpa [absG, Real.sqrt_sq_eq_abs] using h

/-! ## The derivative coefficient of the approximant -/

/-- The coefficient `F x / √(F x ^ 2 + a ^ 2)` appearing in the chain rule. -/
def absCoef {N : ℕ} (F : Conf N → ℝ) (a : ℝ) (x : Conf N) : ℝ :=
  F x / Real.sqrt ((F x) ^ 2 + a ^ 2)

lemma absCoef_abs_le_one {N : ℕ} {F : Conf N → ℝ} {a : ℝ} (ha : 0 < a) (x : Conf N) :
    |absCoef F a x| ≤ 1 := by
  have hden : 0 < Real.sqrt ((F x) ^ 2 + a ^ 2) := by
    apply Real.sqrt_pos_of_pos
    positivity
  rw [absCoef, abs_div, abs_of_nonneg (le_of_lt hden), div_le_one hden]
  calc |F x| = Real.sqrt ((F x) ^ 2) := (Real.sqrt_sq_eq_abs (F x)).symm
    _ ≤ Real.sqrt ((F x) ^ 2 + a ^ 2) := Real.sqrt_le_sqrt (by nlinarith [sq_nonneg a])

lemma absCoef_tendsto_sgnZ {N : ℕ} {F : Conf N → ℝ} (x : Conf N) :
    Tendsto (fun n => absCoef F (absA n) x) atTop (𝓝 (sgnZ (F x))) := by
  have hden : Tendsto (fun n => Real.sqrt ((F x) ^ 2 + (absA n) ^ 2)) atTop (𝓝 |F x|) := by
    have hsq : Tendsto (fun n => (F x) ^ 2 + (absA n) ^ 2) atTop (𝓝 ((F x) ^ 2)) := by
      have h0 : (0 : ℝ) ^ 2 = 0 := by norm_num
      simpa [h0] using tendsto_const_nhds.add (absA_tendsto.pow 2)
    have hc : Tendsto (fun n => Real.sqrt ((F x) ^ 2 + (absA n) ^ 2)) atTop
        (𝓝 (Real.sqrt ((F x) ^ 2))) :=
      (Real.continuous_sqrt.tendsto ((F x) ^ 2)).comp hsq
    simpa only [Real.sqrt_sq_eq_abs] using hc
  rcases lt_trichotomy (F x) 0 with h | h | h
  · have hne : |F x| ≠ 0 := by rw [abs_of_neg h]; exact neg_ne_zero.mpr (ne_of_lt h)
    have hlim : Tendsto (fun n => absCoef F (absA n) x) atTop (𝓝 (F x / |F x|)) :=
      tendsto_const_nhds.div hden hne
    have h1 : F x / |F x| = -1 := by
      rw [abs_of_neg h, div_neg, div_self (ne_of_lt h)]
    have h2 : sgnZ (F x) = -1 := by
      simp only [sgnZ]; rw [if_neg (by linarith), if_pos h]
    rw [h1] at hlim; rw [h2]; exact hlim
  · have hzero : ∀ n, absCoef F (absA n) x = 0 := by
      intro n; rw [absCoef, h]; simp
    have h2 : sgnZ (F x) = 0 := by simp [sgnZ, h]
    rw [h2]
    simp only [hzero]
    exact tendsto_const_nhds
  · have hne : |F x| ≠ 0 := by rw [abs_of_pos h]; exact ne_of_gt h
    have hlim : Tendsto (fun n => absCoef F (absA n) x) atTop (𝓝 (F x / |F x|)) :=
      tendsto_const_nhds.div hden hne
    have h1 : F x / |F x| = 1 := by rw [abs_of_pos h, div_self (ne_of_gt h)]
    have h2 : sgnZ (F x) = 1 := by simp [sgnZ, h]
    rw [h1] at hlim; rw [h2]; exact hlim

/-! ## The candidate limit and the approximating test functions -/

/-- The absolute value of a test function, as a function on configuration space. -/
def absT {N : ℕ} {L : ℝ} (F : testSub N L) : Conf N → ℝ :=
  fun x => |(F : Conf N → ℝ) x|

/-- The `j`-th gradient component of a test function. -/
def dT {N : ℕ} {L : ℝ} (F : testSub N L) (j : GIdx N) : Conf N → ℝ :=
  fun x => fderiv ℝ (F : Conf N → ℝ) x (Submission.BoseGases.kcDir N j.1 j.2)

/-- The signed gradient component `sgnZ(F) ∂_j F`, the limit of `∂_j Gₙ`. -/
def hJT {N : ℕ} {L : ℝ} (F : testSub N L) (j : GIdx N) : Conf N → ℝ :=
  fun x => sgnZ ((F : Conf N → ℝ) x) * dT F j x

/-- The smooth approximating test functions `√(F² + aₙ²) - aₙ`. -/
def GT {N : ℕ} {L : ℝ} (F : testSub N L) (n : ℕ) : testSub N L :=
  ⟨absG (F : Conf N → ℝ) (absA n), absG_contDiff F.2.1 (absA_pos n),
    (absG_tsupport_subset (absA_pos n)).trans F.2.2⟩

lemma GT_coe {N : ℕ} {L : ℝ} (F : testSub N L) (n : ℕ) :
    ((GT F n : testSub N L) : Conf N → ℝ) = absG (F : Conf N → ℝ) (absA n) := rfl

lemma GT_memLp {N : ℕ} {L : ℝ} (F : testSub N L) (n : ℕ) :
    MemLp (absG (F : Conf N → ℝ) (absA n)) 2 (volC N) :=
  memLp_of_contDiff_hasCompactSupport (absG_contDiff F.2.1 (absA_pos n))
    (hasCompactSupport_of_testFun (GT F n).2)

lemma absT_memLp {N : ℕ} {L : ℝ} (F : testSub N L) : MemLp (absT F) 2 (volC N) :=
  (memLp_of_contDiff_hasCompactSupport F.2.1 (hasCompactSupport_of_testFun F.2)).abs

lemma absT_apply {N : ℕ} {L : ℝ} (F : testSub N L) (x : Conf N) :
    absT F x = |(F : Conf N → ℝ) x| := rfl

lemma dT_contDiff {N : ℕ} {L : ℝ} (F : testSub N L) (j : GIdx N) :
    ContDiff ℝ ∞ (dT F j) :=
  Submission.BoseGases.firstDir_contDiff F.2.1 _

lemma dT_hasCompactSupport {N : ℕ} {L : ℝ} (F : testSub N L) (j : GIdx N) :
    HasCompactSupport (dT F j) :=
  IsCompact.of_isClosed_subset (hasCompactSupport_of_testFun F.2) (isClosed_tsupport _)
    (Submission.BoseGases.tsupport_firstDir_subset _)

lemma dT_memLp {N : ℕ} {L : ℝ} (F : testSub N L) (j : GIdx N) :
    MemLp (dT F j) 2 (volC N) :=
  memLp_of_contDiff_hasCompactSupport (dT_contDiff F j) (dT_hasCompactSupport F j)

lemma hJT_memLp {N : ℕ} {L : ℝ} (F : testSub N L) (j : GIdx N) :
    MemLp (hJT F j) 2 (volC N) := by
  refine MemLp.of_le (dT_memLp F j) ?_ ?_
  · exact MeasureTheory.AEStronglyMeasurable.mul
      ((measurable_sgnZ.comp (F.2.1.continuous.measurable)).aestronglyMeasurable)
      ((dT_contDiff F j).continuous.aestronglyMeasurable)
  · refine Eventually.of_forall fun x => ?_
    simp only [hJT]
    rw [Real.norm_eq_abs, abs_mul, Real.norm_eq_abs]
    calc |sgnZ ((F : Conf N → ℝ) x)| * |dT F j x|
        ≤ 1 * |dT F j x| := mul_le_mul_of_nonneg_right (abs_sgnZ_le _) (abs_nonneg _)
      _ = |dT F j x| := one_mul _

/-- The chain rule: the derivative of the approximant is `absCoef` times the
derivative of `F`. -/
lemma GT_fderiv {N : ℕ} {L : ℝ} (F : testSub N L) (n : ℕ) (j : GIdx N) (x : Conf N) :
    fderiv ℝ ((GT F n : testSub N L) : Conf N → ℝ) x
        (Submission.BoseGases.kcDir N j.1 j.2)
      = absCoef (F : Conf N → ℝ) (absA n) x * dT F j x := by
  rw [absCoef, dT, GT_coe, absG_eq]
  exact fderiv_sqrtSq_sub F (absA_pos n) x (Submission.BoseGases.kcDir N j.1 j.2)

/-- The pointwise domination of the gradient difference by `2 |∂_j F|`. -/
lemma GT_grad_sub_le {N : ℕ} {L : ℝ} (F : testSub N L) (j : GIdx N) (n : ℕ) (x : Conf N) :
    ‖fderiv ℝ ((GT F n : testSub N L) : Conf N → ℝ) x
        (Submission.BoseGases.kcDir N j.1 j.2) - hJT F j x‖ ≤ 2 * ‖dT F j x‖ := by
  rw [GT_fderiv F n j x]
  have hsub : absCoef (F : Conf N → ℝ) (absA n) x * dT F j x - hJT F j x
      = (absCoef (F : Conf N → ℝ) (absA n) x - sgnZ ((F : Conf N → ℝ) x)) * dT F j x := by
    simp only [hJT]; ring
  have h2 : |absCoef (F : Conf N → ℝ) (absA n) x| ≤ 1 := absCoef_abs_le_one (absA_pos n) x
  have h3 : |sgnZ ((F : Conf N → ℝ) x)| ≤ 1 := abs_sgnZ_le _
  have h4 : |absCoef (F : Conf N → ℝ) (absA n) x - sgnZ ((F : Conf N → ℝ) x)| ≤ 2 := by
    calc |absCoef (F : Conf N → ℝ) (absA n) x - sgnZ ((F : Conf N → ℝ) x)|
        ≤ |absCoef (F : Conf N → ℝ) (absA n) x| + |sgnZ ((F : Conf N → ℝ) x)| := abs_sub _ _
      _ ≤ 1 + 1 := add_le_add h2 h3
      _ = 2 := by norm_num
  rw [hsub, Real.norm_eq_abs, abs_mul]
  calc |absCoef (F : Conf N → ℝ) (absA n) x - sgnZ ((F : Conf N → ℝ) x)| * |dT F j x|
      ≤ 2 * |dT F j x| := mul_le_mul_of_nonneg_right h4 (abs_nonneg _)
    _ = 2 * ‖dT F j x‖ := by rw [Real.norm_eq_abs]

lemma continuous_gSq (N : ℕ) : Continuous (fun p : Amb N => gSq p) := by
  simp only [gSq]
  fun_prop

/-! ## The main theorem -/

theorem exists_absPoint_graphPoint {N : ℕ} {L : ℝ} (F : testSub N L) :
    ∃ q : Hsub N L, AEEq N (q : Amb N).1 (fun x => |(F : Conf N → ℝ) x|) ∧
      gSq (q : Amb N) ≤ gSq (graphPoint N L F) := by
  classical
  have habs : MemLp (absT F) 2 (volC N) := absT_memLp F
  have hJ : ∀ j : GIdx N, MemLp (hJT F j) 2 (volC N) := fun j => hJT_memLp F j
  let v : Amb N := (MemLp.toLp (absT F) habs, fun j => MemLp.toLp (hJT F j) (hJ j))
  -- convergence of the function part
  have h1 : Tendsto (fun n => (graphPoint N L (GT F n)).1) atTop (𝓝 v.1) := by
    have hmain := tendsto_toLp_of_dominated (μ := volC N)
      (f := fun n => ((GT F n : testSub N L) : Conf N → ℝ)) (g := absT F) (B := absT F)
      (fun n => memLp_of_contDiff_hasCompactSupport (GT F n).2.1
        (hasCompactSupport_of_testFun (GT F n).2))
      habs habs
      (fun n => Eventually.of_forall fun x => by
        simp only [Real.norm_eq_abs, absT, GT_coe, abs_abs]
        exact absG_sub_abs_le (F := (F : Conf N → ℝ)) (absA_pos n) x)
      (Eventually.of_forall fun x => by
        have h := absG_tendsto (F := (F : Conf N → ℝ)) x
        have hfun : (fun n => ((GT F n : testSub N L) : Conf N → ℝ) x)
            = fun n => absG (F : Conf N → ℝ) (absA n) x := by
          funext n; exact congrFun (GT_coe F n) x
        rw [hfun]
        simpa [absT] using h)
    have hv1 : v.1 = MemLp.toLp (absT F) habs := rfl
    rw [hv1]
    exact hmain
  -- convergence of the gradient parts
  have h2 : ∀ j : GIdx N, Tendsto (fun n => (graphPoint N L (GT F n)).2 j) atTop (𝓝 (v.2 j)) := by
    intro j
    have hmain := tendsto_toLp_of_dominated (μ := volC N)
      (f := fun n => fun x => fderiv ℝ ((GT F n : testSub N L) : Conf N → ℝ) x
        (Submission.BoseGases.kcDir N j.1 j.2))
      (g := hJT F j) (B := fun x => (2 : ℝ) * ‖dT F j x‖)
      (fun n => memLp_of_contDiff_hasCompactSupport
        (Submission.BoseGases.firstDir_contDiff (GT F n).2.1 _)
        (IsCompact.of_isClosed_subset (hasCompactSupport_of_testFun (GT F n).2)
          (isClosed_tsupport _) (Submission.BoseGases.tsupport_firstDir_subset _)))
      (hJ j) ((dT_memLp F j).norm.const_mul 2)
      (fun n => Eventually.of_forall fun x => by
        rw [Real.norm_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * ‖dT F j x‖)]
        exact GT_grad_sub_le F j n x)
      (Eventually.of_forall fun x => by
        have hc := absCoef_tendsto_sgnZ (F := (F : Conf N → ℝ)) x
        have hp : Tendsto (fun n => absCoef (F : Conf N → ℝ) (absA n) x * dT F j x) atTop
            (𝓝 (sgnZ ((F : Conf N → ℝ) x) * dT F j x)) :=
          hc.mul tendsto_const_nhds
        have hfun : (fun n => fderiv ℝ ((GT F n : testSub N L) : Conf N → ℝ) x
              (Submission.BoseGases.kcDir N j.1 j.2))
            = fun n => absCoef (F : Conf N → ℝ) (absA n) x * dT F j x := by
          funext n; exact GT_fderiv F n j x
        rw [hfun]
        simpa [hJT] using hp)
    have hv2 : v.2 j = MemLp.toLp (hJT F j) (hJ j) := rfl
    rw [hv2]
    exact hmain
  have hv_tendsto : Tendsto (fun n => graphPoint N L (GT F n)) atTop (𝓝 v) := by
    have h := tendsto_prod_iff'.mpr ⟨h1, tendsto_pi_nhds.mpr h2⟩
    rwa [← nhds_prod_eq] at h
  -- the limit lies in the energy space
  have hv : v ∈ Hsub N L := by
    have hcl : IsClosed ((Hsub N L : Submodule ℝ (Amb N)) : Set (Amb N)) :=
      Submodule.isClosed_topologicalClosure (Submodule.span ℝ (Set.range (graphPoint N L)))
    refine hcl.mem_of_tendsto hv_tendsto (Eventually.of_forall fun n => ?_)
    exact Submodule.le_topologicalClosure (Submodule.span ℝ (Set.range (graphPoint N L)))
      (Submodule.subset_span (Set.mem_range_self (f := graphPoint N L) (GT F n)))
  refine ⟨⟨v, hv⟩, ?_, ?_⟩
  · have hfst : ((⟨v, hv⟩ : Hsub N L) : Amb N).1 = MemLp.toLp (absT F) habs := rfl
    rw [hfst]
    exact MemLp.coeFn_toLp habs
  · have hcont : Tendsto (fun n => gSq (graphPoint N L (GT F n))) atTop (𝓝 (gSq v)) :=
      ((continuous_gSq N).tendsto v).comp hv_tendsto
    refine le_of_tendsto_of_tendsto hcont tendsto_const_nhds (Eventually.of_forall fun n => ?_)
    refine gSq_graphPoint_le F (GT F n) (fun j x => ?_)
    rw [GT_fderiv F n j x, Real.norm_eq_abs, abs_mul, Real.norm_eq_abs]
    calc |absCoef (F : Conf N → ℝ) (absA n) x| * |dT F j x|
        ≤ 1 * |dT F j x| :=
          mul_le_mul_of_nonneg_right (absCoef_abs_le_one (absA_pos n) x) (abs_nonneg _)
      _ = |dT F j x| := one_mul _
      _ = |(fderiv ℝ (F : Conf N → ℝ) x) (Submission.BoseGases.kcDir N j.1 j.2)| := rfl

end

end Work.BoseSym.Abs
