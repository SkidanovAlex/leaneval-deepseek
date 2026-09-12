import Submission.PotentialDefs
import Submission.Serre
import Submission.SerreExample
import Submission.SupportConcentration
import Submission.MuAtomFree
import Submission.LogSingularIntegral
import Submission.NuLogIntegral
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.FieldTheory.Minpoly.Field
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Polynomial.Splits
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Finite-sum log-product identity for the Serre measure (C1)

First ingredient of the arithmeticity assembly (see `SerreArithmetic.serre_arithmetic`,
decomposed item C1).  Let `μ := serreMeasure gSerre aSerre bSerre`.  For any
nonzero `Q ∈ ℤ[x]`, factoring over ℂ (`Qc := Q.map (algebraMap ℤ ℂ) =
C(lc)·∏ over roots (X − C z)`, roots listed with multiplicity by the multiset
`ms := Qc.aroots ℂ`), for real `x`:

    |Q(x)| = |lc| · ∏_{z ∈ ms} |x − z|        (|Q(x)| = |Qc.eval (x:ℂ)|)

so — a.e. in `x` w.r.t. `μ` (the exceptional set is the finite set of real
roots, and `μ` is atom-free) — taking `log` and integrating gives

    ∫ x, log‖Qc.eval (x:ℂ)‖ ∂μ
        = log‖lc‖ + ∫ x, (ms.map (fun z => log‖(x:ℂ) − z‖)).sum ∂μ .

## What this module must deliver
1. `mu_atom_free : ∀ r : ℝ, serreMeasure gSerre aSerre bSerre {r} = 0`
   (μ is a convex combination of pushforwards of Lebesgue along the chart and
   inversion; the preimage of a point is finite, and Lebesgue measure of a
   finite set is zero).
2. The factorization over ℂ: `Qc = C(lc)·∏_{z ∈ ms} (X − C z)`
   (over the algebraically closed ℂ every polynomial splits; use the `aroots`
   API).
3. The pointwise log identity on the complement of the (finite) set of real
   roots, hence `μ`-a.e., and the finite-sum integral identity (linearity of
   the integral over a multiset sum; integrability of each
   `log‖(x:ℂ) − z‖` — bounded on the compact support `[aSerre,bSerre]`
   except for an integrable log-singularity when `z` is a real point of the
   support).

Note: `Q(x) = Qc.eval (x:ℂ)` for real x (`Polynomial.aeval (x:ℂ) Q = Qc.eval (x:ℂ)`
by the ℤ→ℂ evaluation); `‖(x:ℂ) − z‖ = ‖z − (x:ℂ)‖`.
-/

noncomputable section

open MeasureTheory
open scoped Real
open Polynomial

namespace Submission.LogProductMeasure

open Submission.PotentialDefs
open Submission.Equilibrium
open Submission.Serre
open Submission.SerreExample

/-- The multiset of complex roots (with multiplicity) of the ℂ-polynomial
underlying an integer polynomial. -/
noncomputable def rootMultiset (Q : Polynomial ℤ) : Multiset ℂ :=
  (Q.map (algebraMap ℤ ℂ)).aroots ℂ

/-- Serre's measure on `[aSerre,bSerre]`. -/
abbrev serreMu : Measure ℝ := serreMeasure gSerre aSerre bSerre

instance : IsProbabilityMeasure serreMu :=
  ⟨serre_univ (le_of_lt gSerre_pos) gSerre_le_one aSerre bSerre⟩

/-- The Serre measure is atom-free. -/
lemma serre_atom_free (r : ℝ) : serreMeasure gSerre aSerre bSerre {r} = 0 :=
  MuAtomFree.serre_atom_free r

instance : NullSingletonClass serreMu :=
  ⟨serre_atom_free⟩

/-- `rootMultiset Q` is the multiset of roots of the complexified polynomial. -/
lemma rootMultiset_eq_roots (Q : Polynomial ℤ) :
    rootMultiset Q = (Q.map (algebraMap ℤ ℂ)).roots := by
  unfold rootMultiset
  rw [Polynomial.aroots_def]
  simp

/-- `aeval x Q = Qc.eval x` for `x : ℂ` (the ℤ→ℂ evaluation). -/
lemma aeval_eq_eval_map (Q : Polynomial ℤ) (x : ℂ) :
    Polynomial.aeval x Q = (Q.map (algebraMap ℤ ℂ)).eval x := by
  rw [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map]

/-- The complexification of a nonzero integer polynomial is nonzero. -/
lemma map_ne_zero_of_ne_zero (Q : Polynomial ℤ) (hQ : Q ≠ 0) :
    Q.map (algebraMap ℤ ℂ) ≠ 0 := by
  exact (Polynomial.map_ne_zero_iff (f := algebraMap ℤ ℂ)
    (by intro a b h; exact_mod_cast h)).mpr hQ


/-- Over the algebraically closed field ℂ every polynomial factors as leading
coefficient times the product over its roots. -/
lemma factor_eq_of_isAlgClosed (p : Polynomial ℂ) :
    p = C p.leadingCoeff * (p.roots.map (fun z : ℂ => X - C z)).prod := by
  have hcard : p.roots.card = p.natDegree := IsAlgClosed.card_roots_eq_natDegree (k := ℂ) (p := p)
  exact (Polynomial.C_leadingCoeff_mul_prod_multiset_X_sub_C (p := p) hcard).symm

/-- Over ℂ every nonzero polynomial factors as leading coefficient times
the product over its roots: `Qc = C lc · ∏ (X − C z)`. -/
lemma qc_factor_eq (Q : Polynomial ℤ) (hQ : Q ≠ 0) :
    Q.map (algebraMap ℤ ℂ) = C ((Q.leadingCoeff : ℤ) : ℂ) *
      ((Q.map (algebraMap ℤ ℂ)).roots.map (fun z : ℂ => X - C z)).prod := by
  let p : Polynomial ℂ := Q.map (algebraMap ℤ ℂ)
  have hlc : p.leadingCoeff = ((Q.leadingCoeff : ℤ) : ℂ) := by
    rw [Polynomial.leadingCoeff_map_of_injective (f := algebraMap ℤ ℂ)
      (by intro a b h; exact_mod_cast h) Q]
    rfl
  have hf2 : p = C ((Q.leadingCoeff : ℤ) : ℂ) * (p.roots.map (fun z : ℂ => X - C z)).prod := by
    have hfac := factor_eq_of_isAlgClosed p
    rw [hlc] at hfac
    exact hfac
  simpa [p] using hf2

/-- The norm of a product over a multiset is the product of the norms. -/
lemma norm_multiset_prod_eq (m : Multiset ℂ) :
    ‖m.prod‖ = (m.map (fun z : ℂ => ‖z‖)).prod := by
  induction m using Multiset.induction_on with
  | empty => simp
  | cons a t ih => simp [Multiset.prod_cons, ih]

/-- Evaluation of `∏_z (X − C z)` at `x` is `∏_z (x − z)`. -/
lemma eval_prod_X_sub_C (m : Multiset ℂ) (x : ℂ) :
    (m.map (fun z : ℂ => X - C z)).prod.eval x = (m.map (fun z : ℂ => x - z)).prod := by
  rw [Polynomial.eval_multiset_prod]
  simp

/-- Pointwise evaluation of the complexified polynomial:
`‖Qc.eval x‖ = ‖lc‖ · ∏_z ‖x − z‖`. -/
lemma norm_aeval_eq_prod (Q : Polynomial ℤ) (hQ : Q ≠ 0) (x : ℂ) :
    ‖Polynomial.aeval x Q‖ =
      ‖(((Q.leadingCoeff : ℤ) : ℂ))‖ *
        ((rootMultiset Q).map (fun z : ℂ => ‖x - z‖)).prod := by
  let p : Polynomial ℂ := Q.map (algebraMap ℤ ℂ)
  have hlc : p.leadingCoeff = ((Q.leadingCoeff : ℤ) : ℂ) := by
    rw [Polynomial.leadingCoeff_map_of_injective (f := algebraMap ℤ ℂ)
      (by intro a b h; exact_mod_cast h) Q]
    rfl
  have hval0 : p.eval x = ((Q.leadingCoeff : ℤ) : ℂ) *
      (p.roots.map (fun z : ℂ => x - z)).prod := by
    have hfac := factor_eq_of_isAlgClosed p
    have hfac' : p = C ((Q.leadingCoeff : ℤ) : ℂ) *
        (p.roots.map (fun z : ℂ => X - C z)).prod := by
      rw [hlc] at hfac
      exact hfac
    calc
      p.eval x = (C ((Q.leadingCoeff : ℤ) : ℂ) *
          (p.roots.map (fun z : ℂ => X - C z)).prod).eval x := by
          exact congrArg (fun q : Polynomial ℂ => q.eval x) hfac'
      _ = ((Q.leadingCoeff : ℤ) : ℂ) *
            (p.roots.map (fun z : ℂ => x - z)).prod := by
          rw [Polynomial.eval_mul, Polynomial.eval_C]
          rw [eval_prod_X_sub_C]
  have hval : Polynomial.aeval x Q = ((Q.leadingCoeff : ℤ) : ℂ) *
      (p.roots.map (fun z : ℂ => x - z)).prod := by
    rw [aeval_eq_eval_map Q x]
    simpa [p] using hval0
  calc
    ‖Polynomial.aeval x Q‖
        = ‖(((Q.leadingCoeff : ℤ) : ℂ)) *
            (p.roots.map (fun z : ℂ => x - z)).prod‖ := by rw [hval]
    _ = ‖(((Q.leadingCoeff : ℤ) : ℂ))‖ *
          ‖(p.roots.map (fun z : ℂ => x - z)).prod‖ := by
          rw [Complex.norm_mul]
    _ = ‖(((Q.leadingCoeff : ℤ) : ℂ))‖ *
          (p.roots.map (fun z : ℂ => ‖x - z‖)).prod := by
          congr 1
          have hnm := norm_multiset_prod_eq (p.roots.map (fun z : ℂ => x - z))
          simpa [Multiset.map_map, Function.comp_def] using hnm
    _ = ‖(((Q.leadingCoeff : ℤ) : ℂ))‖ *
          ((rootMultiset Q).map (fun z : ℂ => ‖x - z‖)).prod := by
          simp [p, rootMultiset_eq_roots Q]

lemma log_prod_eq_sum_of_ne_zero (m : Multiset ℂ) {y : ℂ}
    (hy : ∀ z ∈ m, ‖y - z‖ ≠ 0) :
    Real.log ((m.map (fun z : ℂ => ‖y - z‖)).prod) =
      (m.map (fun z : ℂ => Real.log ‖y - z‖)).sum := by
  induction m using Multiset.induction_on with
  | empty => simp
  | cons a t ih =>
      have hy_t : ∀ z ∈ t, ‖y - z‖ ≠ 0 := fun z hz => hy z (by simp [hz])
      have hprod : ((t.map (fun z : ℂ => ‖y - z‖)).prod) ≠ 0 := by
        exact Multiset.prod_ne_zero (by
          intro hz
          rcases Multiset.mem_map.mp hz with ⟨w, hw1, hw2⟩
          exact hy_t w hw1 (by simpa [hw2]))
      simp [Multiset.prod_cons, Multiset.sum_cons, Real.log_mul (hy a (by simp)) hprod, ih hy_t]

/-- log of `‖lc‖·∏ factors` splits into `log‖lc‖` plus the sum of logs. -/
lemma log_mul_prod_eq_sum_of_ne_zero (m : Multiset ℂ) {y : ℂ} {c : ℝ}
    (hc : c ≠ 0) (hy : ∀ z ∈ m, ‖y - z‖ ≠ 0) :
    Real.log (c * (m.map (fun z : ℂ => ‖y - z‖)).prod) =
      Real.log c + (m.map (fun z : ℂ => Real.log ‖y - z‖)).sum := by
  have hprod : (m.map (fun z : ℂ => ‖y - z‖)).prod ≠ 0 := by
    exact Multiset.prod_ne_zero (by
      intro hz
      rcases Multiset.mem_map.mp hz with ⟨w, hw1, hw2⟩
      exact hy w hw1 (by simpa [hw2]))
  rw [Real.log_mul hc hprod]
  rw [log_prod_eq_sum_of_ne_zero m hy]

/-- On the complement of the real roots, `log|Q(x)| = log‖lc‖ + Σ log‖x−z‖`
(the pointwise log-product identity). -/
lemma log_aeval_eq_sum_of_not_root (Q : Polynomial ℤ) (hQ : Q ≠ 0) {x : ℝ}
    (hx : Polynomial.aeval (x : ℂ) Q ≠ 0) :
    Real.log ‖Polynomial.aeval (x : ℂ) Q‖ =
      Real.log ‖(((Q.leadingCoeff : ℤ) : ℂ))‖ +
        ((rootMultiset Q).map (fun z : ℂ => Real.log ‖(x : ℂ) - z‖)).sum := by
  have hnorm := norm_aeval_eq_prod Q hQ (x : ℂ)
  have hne0 : ‖(((Q.leadingCoeff : ℤ) : ℂ))‖ ≠ 0 := by
    have hlc : Q.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hQ
    exact norm_ne_zero_iff.mpr (by exact_mod_cast hlc)
  have hprod0 : ((rootMultiset Q).map (fun z : ℂ => ‖(x : ℂ) - z‖)).prod ≠ 0 := by
    intro hz
    have h : ‖Polynomial.aeval (x : ℂ) Q‖ = 0 := by
      rw [hnorm, hz]
      simp
    exact hx (norm_eq_zero.mp h)
  have hfac : ∀ z ∈ rootMultiset Q, ‖(x : ℂ) - z‖ ≠ 0 := by
    intro z hz hz0
    apply hprod0
    exact Multiset.prod_eq_zero (Multiset.mem_map.mpr ⟨z, hz, hz0⟩)
  calc
    Real.log ‖Polynomial.aeval (x : ℂ) Q‖
        = Real.log (‖(((Q.leadingCoeff : ℤ) : ℂ))‖ *
            ((rootMultiset Q).map (fun z : ℂ => ‖(x : ℂ) - z‖)).prod) := by rw [hnorm]
    _ = Real.log ‖(((Q.leadingCoeff : ℤ) : ℂ))‖ +
          ((rootMultiset Q).map (fun z : ℂ => Real.log ‖(x : ℂ) - z‖)).sum := by
          exact log_mul_prod_eq_sum_of_ne_zero (rootMultiset Q) (y := (x : ℂ)) (c := ‖(((Q.leadingCoeff : ℤ) : ℂ))‖) hne0 hfac

/-- `x ↦ x` belongs to `[aSerre,bSerre]` almost everywhere w.r.t. the Serre
measure (the measure is supported on the interval). -/
lemma ae_mem_Icc_serre : (∀ᵐ x ∂serreMu, x ∈ Set.Icc aSerre bSerre) := by
  rw [MeasureTheory.ae_iff]
  have hcompl : serreMeasure gSerre aSerre bSerre ((Set.Icc aSerre bSerre)ᶜ) = 0 := by
    exact Submission.SupportConcentration.serre_compl_Icc aSerre_pos a_le_b
      (le_of_lt gSerre_pos) gSerre_le_one
  have hset : {x : ℝ | ¬x ∈ Set.Icc aSerre bSerre} = (Set.Icc aSerre bSerre)ᶜ := by
    ext x
    simp
  rw [hset]
  exact hcompl

/-- The set of real roots of the complexified `Q`. -/
def realRootSet (Q : Polynomial ℤ) : Set ℝ := {x : ℝ | Polynomial.aeval (x : ℂ) Q = 0}

/-- The real roots of a nonzero `Q` form a null set of the atom-free Serre
measure. -/
lemma measure_realRootSet_zero (Q : Polynomial ℤ) (hQ : Q ≠ 0) : serreMu (realRootSet Q) = 0 := by
  let F : Finset ℝ := (rootMultiset Q).toFinset.image (fun z : ℂ => z.re)
  have hsub : realRootSet Q ⊆ (↑F : Set ℝ) := by
    intro x hx
    have hxmem : (x : ℂ) ∈ rootMultiset Q := by
      rw [rootMultiset_eq_roots Q]
      rw [Polynomial.mem_roots (map_ne_zero_of_ne_zero Q hQ)]
      change (Q.map (algebraMap ℤ ℂ)).eval (x : ℂ) = 0
      rw [← aeval_eq_eval_map Q (x : ℂ)]
      exact hx
    exact Finset.mem_image.mpr ⟨(x : ℂ), (Multiset.mem_toFinset).mpr hxmem, by simp⟩
  have hF : serreMu (↑F : Set ℝ) = 0 := (F.finite_toSet).measure_zero serreMu
  exact measure_mono_null hsub hF

/-- Pointwise log-product identity holds almost everywhere: on the complement
of the real roots the identity is exact (so it holds `μ`-a.e.). -/
lemma ae_log_q_eq_sum (Q : Polynomial ℤ) (hQ : Q ≠ 0) :
    (fun x : ℝ => Real.log ‖Polynomial.aeval (x : ℂ) Q‖) =ᵐ[serreMu]
      (fun x : ℝ =>
        Real.log ‖(((Q.leadingCoeff : ℤ) : ℂ))‖ +
          ((rootMultiset Q).map (fun z : ℂ => Real.log ‖(x : ℂ) - z‖)).sum) := by
  refine (MeasureTheory.ae_iff (p := fun x : ℝ =>
    Real.log ‖Polynomial.aeval (x : ℂ) Q‖ =
      Real.log ‖(((Q.leadingCoeff : ℤ) : ℂ))‖ +
        ((rootMultiset Q).map (fun z : ℂ => Real.log ‖(x : ℂ) - z‖)).sum)).mpr ?_
  refine measure_mono_null ?_ (measure_realRootSet_zero Q hQ)
  intro x hx
  by_contra hxgood
  apply hx
  have hxneq : Polynomial.aeval (x : ℂ) Q ≠ 0 := by
    intro hz
    exact hxgood (by simpa [realRootSet] using hz)
  exact log_aeval_eq_sum_of_not_root Q hQ hxneq

/-- `log‖(x:ℂ) − z‖` is measurable in `x`. -/
lemma measurable_log_dist (z : ℂ) : Measurable (fun x : ℝ => Real.log ‖(x : ℂ) - z‖) := by
  fun_prop

/-- Complex norm of the difference of two real embeddings is the real distance. -/
lemma norm_sub_ofReal (x r : ℝ) : ‖(x : ℂ) - (r : ℂ)‖ = |x - r| := by
  rw [← Complex.ofReal_sub]
  exact norm_complex_ofReal (x - r)

/-- Log-singular integrability for `μ_eq` of Serre's interval at an interior
real point. -/
lemma equilibrium_log_sub_Icc (r : ℝ) (hr : r ∈ Set.Icc aSerre bSerre) :
    Integrable (fun x : ℝ => Real.log ‖(x : ℂ) - (r : ℂ)‖) (equilibrium aSerre bSerre) :=
  LogSingularIntegral.equilibrium_log_sub_integrable (a := aSerre) (b := bSerre) (r := r)
    a_lt_b hr

/-- Log-singular integrability for `ν` of Serre's interval at an interior real
point. -/
lemma nu_log_sub_Icc (r : ℝ) (hr : r ∈ Set.Icc aSerre bSerre) :
    Integrable (fun x : ℝ => Real.log ‖(x : ℂ) - (r : ℂ)‖) (nu aSerre bSerre) :=
  NuLogIntegral.nu_log_sub_integrable (a := aSerre) (b := bSerre) (r := r)
    aSerre_pos a_lt_b hr

/-- If a measurable function is bounded on `[aSerre,bSerre]` between two real
constants, it is integrable against the (supported) Serre measure. -/
lemma integrable_of_bound_on_Icc {f : ℝ → ℝ} (hmeas : Measurable f) (lo hi : ℝ)
    (h : ∀ x ∈ Set.Icc aSerre bSerre, lo ≤ f x ∧ f x ≤ hi) :
    Integrable f serreMu := by
  refine MeasureTheory.Integrable.of_mem_Icc lo hi hmeas.aemeasurable ?_
  filter_upwards [ae_mem_Icc_serre] with x hx
  exact h x hx

/-- For non-real `z`, `log‖(x:ℂ) − z‖` is bounded on the interval. -/
lemma log_dist_bound_nonreal {z : ℂ} (hz : z.im ≠ 0) :
    ∀ x ∈ Set.Icc aSerre bSerre,
      Real.log |z.im| ≤ Real.log ‖(x : ℂ) - z‖ ∧
        Real.log ‖(x : ℂ) - z‖ ≤ Real.log (bSerre + ‖z‖) := by
  intro x hx
  have hle_low : |z.im| ≤ ‖(x : ℂ) - z‖ := by
    calc
      |z.im| = |((x : ℂ) - z).im| := by simp
      _ ≤ ‖(x : ℂ) - z‖ := Complex.abs_im_le_norm _
  constructor
  · exact Real.log_le_log (abs_pos.mpr hz) hle_low
  · have hposx : 0 < ‖(x : ℂ) - z‖ := lt_of_lt_of_le (abs_pos.mpr hz) hle_low
    apply Real.log_le_log hposx
    calc
      ‖(x : ℂ) - z‖ ≤ ‖(x : ℂ)‖ + ‖z‖ := norm_sub_le _ _
      _ = |x| + ‖z‖ := by simp
      _ ≤ bSerre + ‖z‖ := by
        have hxle : |x| ≤ bSerre := by
          have hxpos : 0 ≤ x := le_trans (le_of_lt aSerre_pos) hx.1
          rw [abs_of_nonneg hxpos]
          exact hx.2
        nlinarith

/-- For real `r < aSerre`, `log‖(x:ℂ) − (r:ℂ)‖` is bounded on the interval. -/
lemma log_dist_bound_real_lt {r : ℝ} (hr : r < aSerre) :
    ∀ x ∈ Set.Icc aSerre bSerre,
      Real.log (aSerre - r) ≤ Real.log ‖(x : ℂ) - (r : ℂ)‖ ∧
        Real.log ‖(x : ℂ) - (r : ℂ)‖ ≤ Real.log (bSerre - r) := by
  intro x hx
  have h1 : 0 < aSerre - r := sub_pos.mpr hr
  have hxl : aSerre - r ≤ x - r := by linarith [hx.1]
  have hxr : x - r ≤ bSerre - r := by linarith [hx.2]
  have hxrpos : 0 < x - r := lt_of_lt_of_le h1 hxl
  constructor
  · rw [norm_sub_ofReal, abs_of_pos hxrpos]
    exact Real.log_le_log h1 hxl
  · rw [norm_sub_ofReal, abs_of_pos hxrpos]
    exact Real.log_le_log hxrpos hxr

/-- For real `r > bSerre`, `log‖(x:ℂ) − (r:ℂ)‖` is bounded on the interval. -/
lemma log_dist_bound_real_gt {r : ℝ} (hr : bSerre < r) :
    ∀ x ∈ Set.Icc aSerre bSerre,
      Real.log (r - bSerre) ≤ Real.log ‖(x : ℂ) - (r : ℂ)‖ ∧
        Real.log ‖(x : ℂ) - (r : ℂ)‖ ≤ Real.log (r - aSerre) := by
  intro x hx
  have h1 : 0 < r - bSerre := sub_pos.mpr hr
  have hxl : r - bSerre ≤ r - x := by linarith [hx.2]
  have hxr : r - x ≤ r - aSerre := by linarith [hx.1]
  have hxrpos : 0 < r - x := lt_of_lt_of_le h1 hxl
  have hneg : x - r < 0 := by linarith [hx.2, hr]
  constructor
  · rw [norm_sub_ofReal, abs_of_neg hneg, neg_sub]
    exact Real.log_le_log h1 hxl
  · rw [norm_sub_ofReal, abs_of_neg hneg, neg_sub]
    exact Real.log_le_log hxrpos hxr

/-- Every term `log‖(x:ℂ) − z‖` is integrable against Serre's measure. -/
lemma log_dist_integrable (z : ℂ) : Integrable (fun x : ℝ => Real.log ‖(x : ℂ) - z‖) serreMu := by
  by_cases hzr : ∃ r : ℝ, z = r
  · rcases hzr with ⟨r, rfl⟩
    by_cases hr : r ∈ Set.Icc aSerre bSerre
    · -- r inside the support: use the singular integrability of both components
      have heq : Integrable (fun x : ℝ => Real.log ‖(x : ℂ) - (r : ℂ)‖)
          (equilibrium aSerre bSerre) := equilibrium_log_sub_Icc r hr
      have hnu : Integrable (fun x : ℝ => Real.log ‖(x : ℂ) - (r : ℂ)‖)
          (nu aSerre bSerre) := nu_log_sub_Icc r hr
      unfold serreMu serreMeasure
      exact (MeasureTheory.Integrable.add_measure
        (hnu.smul_measure (c := ENNReal.ofReal gSerre) ENNReal.ofReal_ne_top)
        (heq.smul_measure (c := ENNReal.ofReal (1 - gSerre)) ENNReal.ofReal_ne_top))
    · -- real root outside the support: bounded on the interval
      have hrout : r < aSerre ∨ bSerre < r := by
        have hle : ¬ (aSerre ≤ r ∧ r ≤ bSerre) := by simpa [Set.mem_Icc] using hr
        by_cases h1 : r < aSerre
        · exact Or.inl h1
        · right
          have hle2 : aSerre ≤ r := le_of_not_gt h1
          have hnle : ¬ r ≤ bSerre := by
            intro hrle
            exact hle ⟨hle2, hrle⟩
          exact lt_of_not_ge hnle
      rcases hrout with hlt | hgt
      · exact integrable_of_bound_on_Icc (f := fun x : ℝ => Real.log ‖(x : ℂ) - (r : ℂ)‖)
          (measurable_log_dist (r : ℂ)) (Real.log (aSerre - r)) (Real.log (bSerre - r))
          (log_dist_bound_real_lt hlt)
      · exact integrable_of_bound_on_Icc (f := fun x : ℝ => Real.log ‖(x : ℂ) - (r : ℂ)‖)
          (measurable_log_dist (r : ℂ)) (Real.log (r - bSerre)) (Real.log (r - aSerre))
          (log_dist_bound_real_gt hgt)
  · -- non-real root: bounded below by `|z.im| > 0`
    have hzim : z.im ≠ 0 := by
      intro hz
      apply hzr
      refine ⟨z.re, ?_⟩
      exact Complex.ext (by simp) (by simpa [hz])
    exact integrable_of_bound_on_Icc (f := fun x : ℝ => Real.log ‖(x : ℂ) - z‖)
      (measurable_log_dist z) (Real.log |z.im|) (Real.log (bSerre + ‖z‖))
      (log_dist_bound_nonreal hzim)

/-- The sum over the roots of `log‖(x:ℂ) − z‖` is integrable. -/
lemma sum_log_dist_integrable (Q : Polynomial ℤ) :
    Integrable (fun x : ℝ =>
      ((rootMultiset Q).map (fun z : ℂ => Real.log ‖(x : ℂ) - z‖)).sum) serreMu := by
  let ms0 : Multiset ℂ := rootMultiset Q
  have hmain : ∀ m : Multiset ℂ,
      Integrable (fun x : ℝ => (m.map (fun z : ℂ => Real.log ‖(x : ℂ) - z‖)).sum) serreMu := by
    intro m
    induction m using Multiset.induction_on with
    | empty =>
        simpa using (MeasureTheory.integrable_zero ℝ serreMu)
    | cons z ms ih =>
        have hfun : (fun x : ℝ => ((z ::ₘ ms).map (fun w : ℂ => Real.log ‖(x : ℂ) - w‖)).sum) =
            (fun x : ℝ => Real.log ‖(x : ℂ) - z‖) +
              (fun x : ℝ => (ms.map (fun w : ℂ => Real.log ‖(x : ℂ) - w‖)).sum) := by
          funext x
          simp [Multiset.map_cons, Multiset.sum_cons]
        rw [hfun]
        exact (log_dist_integrable z).add ih
  simpa [ms0] using hmain (rootMultiset Q)

/-- Generic: an a.e. identity `L = c + S` with `S` integrable integrates to
`∫ L = c + ∫ S` for a probability measure. -/
lemma integral_of_ae_eq_add_const {μ : Measure ℝ} [IsProbabilityMeasure μ]
    {L S : ℝ → ℝ} {c : ℝ} (hS : Integrable S μ) (hL : L =ᵐ[μ] fun x => c + S x) :
    (∫ x : ℝ, L x ∂μ) = c + (∫ x : ℝ, S x ∂μ) := by
  calc
    (∫ x : ℝ, L x ∂μ) = (∫ x : ℝ, (c + S x) ∂μ) := by
        apply MeasureTheory.integral_congr_ae
        exact hL
    _ = (∫ x : ℝ, c ∂μ) + (∫ x : ℝ, S x ∂μ) := by
        rw [MeasureTheory.integral_add (MeasureTheory.integrable_const c) hS]
    _ = c + (∫ x : ℝ, S x ∂μ) := by
        rw [MeasureTheory.integral_const]
        simp

/-- (C1) Finite-sum log-product identity for the Serre measure. -/
theorem integral_log_q_eq (Q : Polynomial ℤ) (hQ : Q ≠ 0) :
    (∫ x : ℝ, Real.log ‖Polynomial.aeval (x : ℂ) Q‖ ∂serreMeasure gSerre aSerre bSerre) =
      Real.log ‖(((Q.leadingCoeff : ℤ) : ℂ))‖ +
        (∫ x : ℝ,
          ((rootMultiset Q).map (fun z : ℂ => Real.log ‖(x : ℂ) - z‖)).sum ∂serreMeasure
            gSerre aSerre bSerre) := by
  let L : ℝ → ℝ := fun x => Real.log ‖Polynomial.aeval (x : ℂ) Q‖
  let S : ℝ → ℝ := fun x => ((rootMultiset Q).map (fun z : ℂ => Real.log ‖(x : ℂ) - z‖)).sum
  let c : ℝ := Real.log ‖(((Q.leadingCoeff : ℤ) : ℂ))‖
  have hS : Integrable S serreMu := by
    dsimp [S]
    exact sum_log_dist_integrable Q
  have hL : L =ᵐ[serreMu] (fun x : ℝ => c + S x) := by
    simpa [L, S, c] using ae_log_q_eq_sum Q hQ
  have hmain : (∫ x : ℝ, L x ∂serreMu) = c + (∫ x : ℝ, S x ∂serreMu) :=
    integral_of_ae_eq_add_const (μ := serreMu) hS hL
  simpa [L, S, c, serreMu] using hmain

end Submission.LogProductMeasure
