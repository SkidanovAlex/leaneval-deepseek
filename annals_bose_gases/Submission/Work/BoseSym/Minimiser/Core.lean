import Mathlib.MeasureTheory.Function.Holder
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseSym.Minimiser.Defs
import Submission.Work.BoseSym.Minimiser.cs_bilinear
import Submission.Work.BoseSym.Minimiser.inner_lpSMul
import Submission.Work.BoseSym.Minimiser.minimiser_set_symAvg
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# BoseSym.Minimiser.Core — the bilinear-form calculus for the minimiser argument

Everything here is stated for an explicit `L∞` class `F : L2top N`; the main
proof instantiates `F` with the class of `W` shifted by `constLp N (C+1)`.
-/

namespace Work.BoseSym.Minimiser

open MeasureTheory Filter
open Work.BoseSym
open scoped Topology ENNReal

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000

/-! ## Basic identities -/

@[simp] lemma l2Sq_eq_inner {N : ℕ} (p : Amb N) : l2Sq p = inner ℝ p.1 p.1 :=
  (real_inner_self_eq_norm_sq p.1).symm

@[simp] lemma gSq_eq_inner_sum {N : ℕ} (p : Amb N) :
    gSq p = ∑ j : GIdx N, inner ℝ (p.2 j) (p.2 j) := by
  simp only [gSq]
  exact Finset.sum_congr rfl fun j _ => (real_inner_self_eq_norm_sq (p.2 j)).symm

/-! ## Bilinearity of `formP` -/

section Bilinear

variable {N : ℕ}

lemma formP_add_left (F : L2top N) (p p' q : Amb N) :
    formP F (p + p') q = formP F p q + formP F p' q := by
  have h1 : (p + p' : Amb N).1 = p.1 + p'.1 := rfl
  have h2 : ∀ j : GIdx N, (p + p' : Amb N).2 j = p.2 j + p'.2 j := fun j => rfl
  have h3 : (F • (p + p' : Amb N).1 : L2 N) = F • p.1 + F • p'.1 := by
    rw [h1]; exact MeasureTheory.Lp.add_smul F p.1 p'.1
  simp only [formP, h2, h3, inner_add_left]
  rw [Finset.sum_add_distrib]
  ring

lemma formP_add_right (F : L2top N) (p q q' : Amb N) :
    formP F p (q + q') = formP F p q + formP F p q' := by
  have h1 : (q + q' : Amb N).1 = q.1 + q'.1 := rfl
  have h2 : ∀ j : GIdx N, (q + q' : Amb N).2 j = q.2 j + q'.2 j := fun j => rfl
  simp only [formP, h2, h1, inner_add_right]
  rw [Finset.sum_add_distrib]
  ring

lemma formP_smul_left (F : L2top N) (c : ℝ) (p q : Amb N) :
    formP F (c • p) q = c * formP F p q := by
  have h1 : (c • p : Amb N).1 = c • p.1 := rfl
  have h2 : ∀ j : GIdx N, (c • p : Amb N).2 j = c • p.2 j := fun j => rfl
  have h3 : (F • (c • p : Amb N).1 : L2 N) = c • (F • p.1) := by
    rw [h1, ← MeasureTheory.Lp.smul_comm c F p.1]
  simp only [formP, h2, h3, real_inner_smul_left]
  rw [← Finset.mul_sum]
  ring

lemma formP_smul_right (F : L2top N) (c : ℝ) (p q : Amb N) :
    formP F p (c • q) = c * formP F p q := by
  have h1 : (c • q : Amb N).1 = c • q.1 := rfl
  have h2 : ∀ j : GIdx N, (c • q : Amb N).2 j = c • q.2 j := fun j => rfl
  simp only [formP, h2, h1, real_inner_smul_right]
  rw [← Finset.mul_sum]
  ring

end Bilinear

/-! ## The `L∞` multiplication against the `L²` inner product -/

lemma inner_lpSMul_comm {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (F : Lp ℝ (⊤ : ℝ≥0∞) μ) (u v : Lp ℝ 2 μ) :
    inner ℝ (F • u) v = inner ℝ (F • v) u := by
  rw [inner_lpSMul μ F u v, inner_lpSMul μ F v u]
  exact integral_congr_ae (Filter.Eventually.of_forall fun x => by ring)

lemma formP_comm {N : ℕ} (F : L2top N) (p q : Amb N) : formP F p q = formP F q p := by
  simp only [formP]
  rw [inner_lpSMul_comm (volC N) F p.1 q.1]
  congr 1
  exact Finset.sum_congr rfl fun j _ => real_inner_comm (q.2 j) (p.2 j)

section AddClass

variable {N : ℕ}

/-- Splitting off the constant class in the multiplication pairing. -/
lemma inner_lpSMul_sub_add (F : L2top N) (p q : Amb N) :
    inner ℝ (F • p.1) q.1
      = inner ℝ ((F - constLp N 1) • p.1) q.1 + inner ℝ (constLp N 1 • p.1) q.1 := by
  conv_lhs => rw [← sub_add_cancel F (constLp N 1)]
  rw [MeasureTheory.Lp.smul_add, inner_add_left]

lemma inner_lpSMul_add_left (F G : L2top N) (u v : L2 N) :
    inner ℝ ((F + G) • u) v = inner ℝ (F • u) v + inner ℝ (G • u) v := by
  rw [MeasureTheory.Lp.smul_add, inner_add_left]

lemma inner_lpSMul_constLp (c : ℝ) (u v : L2 N) :
    inner ℝ (constLp N c • u) v = c * inner ℝ u v := by
  have h : constLp N c • u = c • u := by
    refine MeasureTheory.Lp.ext ?_
    filter_upwards [MeasureTheory.Lp.coeFn_lpSMul (p := ⊤) (q := 2) (r := 2) (constLp N c) u,
      constLp_coeFn (N := N) c, MeasureTheory.Lp.coeFn_smul c u] with x h1 h2 h3
    rw [h1, h3]
    simp only [Pi.smul_apply, smul_eq_mul, Pi.mul_apply, h2]
  rw [h, real_inner_smul_left]

lemma inner_lpSMul_eq_potSq {F : L2top N} {W : Conf N → ℝ}
    (hF : (F : Conf N → ℝ) =ᵐ[volC N] W) (p : Amb N) :
    inner ℝ (F • p.1) p.1 = potSq W p := by
  rw [inner_lpSMul (volC N) F p.1 p.1, potSq]
  refine integral_congr_ae ?_
  filter_upwards [hF] with x hx
  rw [hx]
  ring

lemma inner_lpSMul_nonneg_of {F : L2top N}
    (hF : (0 : Conf N → ℝ) ≤ᵐ[volC N] (F : Conf N → ℝ)) (u : L2 N) :
    0 ≤ inner ℝ (F • u) u := by
  rw [inner_lpSMul (volC N) F u u]
  refine integral_nonneg_of_ae ?_
  filter_upwards [hF] with x hx
  have hu : 0 ≤ (u : Conf N → ℝ) x * (u : Conf N → ℝ) x := mul_self_nonneg _
  calc 0 ≤ (F : Conf N → ℝ) x * ((u : Conf N → ℝ) x * (u : Conf N → ℝ) x) :=
        mul_nonneg hx hu
    _ = (F : Conf N → ℝ) x * (u : Conf N → ℝ) x * (u : Conf N → ℝ) x := by ring

/-- Nonnegativity of the diagonal of `formP` for an a.e. nonnegative class. -/
lemma formP_self_nonneg {F : L2top N}
    (hF : (0 : Conf N → ℝ) ≤ᵐ[volC N] (F : Conf N → ℝ)) (p : Amb N) :
    0 ≤ formP F p p := by
  rw [formP_self]
  have h := inner_lpSMul_nonneg_of hF p.1
  have hg : 0 ≤ gSq p := by simp only [gSq]; positivity
  linarith

/-- The graph norm is dominated by the diagonal of `formP`, provided the class
`F` dominates the constant `1` (this is where `W + C + 1 ≥ 1` is used). -/
lemma hSq_le_formP_self {F : L2top N}
    (hF : (0 : Conf N → ℝ) ≤ᵐ[volC N] ((F - constLp N 1 : L2top N) : Conf N → ℝ))
    (p : Amb N) : hSq p ≤ formP F p p := by
  rw [formP_self, hSq, l2Sq_eq_inner]
  have hsplit := inner_lpSMul_sub_add F p p
  have hnn : 0 ≤ inner ℝ ((F - constLp N 1) • p.1) p.1 := inner_lpSMul_nonneg_of hF p.1
  have hone : inner ℝ (constLp N 1 • p.1) p.1 = inner ℝ p.1 p.1 := by
    rw [inner_lpSMul_constLp]; ring
  rw [hsplit, hone]
  linarith

/-- Cauchy–Schwarz for `formP`. -/
lemma formP_sq_le {F : L2top N} (hF : ∀ p : Amb N, 0 ≤ formP F p p) (p q : Amb N) :
    formP F p q ^ 2 ≤ formP F p p * formP F q q :=
  cs_bilinear (formP F) (fun x y => formP_comm F x y)
    (fun x y z => formP_add_left F x y z) (fun c x y => formP_smul_left F c x y) hF p q

/-- The quadratic expansion of `formP` on a difference. -/
lemma formP_sub_self {F : L2top N} (p q : Amb N) :
    formP F (p - q) (p - q) = formP F p p + formP F q q - 2 * formP F p q := by
  have hq : (-q : Amb N) = (-1 : ℝ) • q := (neg_one_smul ℝ q).symm
  rw [sub_eq_add_neg, hq]
  simp only [formP_add_left, formP_add_right, formP_smul_left, formP_smul_right,
    neg_mul, neg_neg, one_mul, formP_comm F q p]
  ring

/-- The lower bound for the weighted quadratic form: if `F` represents a
function bounded below by `-C`, then `potSq` dominates `-C * l2Sq`. -/
lemma potSq_ge_shift {F : L2top N} {W : Conf N → ℝ} {C : ℝ}
    (hF : (F : Conf N → ℝ) =ᵐ[volC N] W)
    (hFC : (0 : Conf N → ℝ) ≤ᵐ[volC N] ((F + constLp N C : L2top N) : Conf N → ℝ))
    (p : Amb N) : -C * l2Sq p ≤ potSq W p := by
  rw [← inner_lpSMul_eq_potSq hF p, l2Sq_eq_inner]
  have hsplit : inner ℝ ((F + constLp N C) • p.1) p.1
      = inner ℝ (F • p.1) p.1 + C * inner ℝ p.1 p.1 := by
    rw [MeasureTheory.Lp.smul_add, inner_add_left, inner_lpSMul_constLp]
  have hnn := inner_lpSMul_nonneg_of hFC p.1
  rw [hsplit] at hnn
  linarith

end AddClass

/-! ## The shifted form on the energy space -/

section Shift

variable {N : ℕ}

/-- Cauchy–Schwarz for the shifted form `formP F - κ * ⟪·,·⟫` on the energy
space, given that its diagonal is nonnegative there. -/
lemma shiftH_sq_le {L : ℝ} (F : L2top N) (κ : ℝ)
    (hpos : ∀ p : Hsub N L,
      0 ≤ formP F (p : Amb N) (p : Amb N) - κ * inner ℝ (p : Amb N).1 (p : Amb N).1)
    (p q : Hsub N L) :
    (formP F (p : Amb N) (q : Amb N) - κ * inner ℝ (p : Amb N).1 (q : Amb N).1) ^ 2
      ≤ (formP F (p : Amb N) (p : Amb N) - κ * inner ℝ (p : Amb N).1 (p : Amb N).1)
        * (formP F (q : Amb N) (q : Amb N) - κ * inner ℝ (q : Amb N).1 (q : Amb N).1) := by
  refine cs_bilinear
    (fun a b : Hsub N L =>
      formP F (a : Amb N) (b : Amb N) - κ * inner ℝ (a : Amb N).1 (b : Amb N).1)
    ?_ ?_ ?_ hpos p q
  · intro a b
    rw [formP_comm F (a : Amb N) (b : Amb N), real_inner_comm ((b : Amb N).1)]
  · intro a b c
    rw [show ((a + b : Hsub N L) : Amb N) = (a : Amb N) + (b : Amb N) from rfl]
    rw [formP_add_left, Prod.fst_add, inner_add_left]
    ring
  · intro c a b
    rw [show ((c • a : Hsub N L) : Amb N) = c • (a : Amb N) from rfl]
    rw [formP_smul_left, Prod.smul_fst, real_inner_smul_left]
    ring

end Shift

/-! ## Norm comparison -/

section Norms

variable {N : ℕ}

/-- The ambient (sup-product) norm is dominated by the graph norm. -/
lemma norm_sq_le_hSq (p : Amb N) : ‖p‖ ^ 2 ≤ hSq p := by
  have h1 : ‖p.1‖ ^ 2 ≤ hSq p := by
    rw [hSq, l2Sq]
    have : 0 ≤ gSq p := by simp only [gSq]; positivity
    linarith
  have h2 : ‖p.2‖ ^ 2 ≤ hSq p := by
    have hle : ‖p.2‖ ≤ Real.sqrt (∑ j : GIdx N, ‖p.2 j‖ ^ 2) := by
      refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).mpr fun j => ?_
      have hsingle : ‖p.2 j‖ ^ 2 ≤ ∑ i : GIdx N, ‖p.2 i‖ ^ 2 :=
        Finset.single_le_sum (f := fun i : GIdx N => ‖p.2 i‖ ^ 2)
          (fun i _ => by positivity) (Finset.mem_univ j)
      calc ‖p.2 j‖ = Real.sqrt (‖p.2 j‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
        _ ≤ Real.sqrt (∑ i : GIdx N, ‖p.2 i‖ ^ 2) := Real.sqrt_le_sqrt hsingle
    have h2' : ‖p.2‖ ^ 2 ≤ ∑ j : GIdx N, ‖p.2 j‖ ^ 2 := by
      calc ‖p.2‖ ^ 2 ≤ (Real.sqrt (∑ j : GIdx N, ‖p.2 j‖ ^ 2)) ^ 2 :=
            pow_le_pow_left₀ (norm_nonneg _) hle 2
        _ = ∑ j : GIdx N, ‖p.2 j‖ ^ 2 :=
            Real.sq_sqrt (Finset.sum_nonneg fun _ _ => by positivity)
    rw [hSq, l2Sq, gSq]
    have : 0 ≤ ‖p.1‖ ^ 2 := by positivity
    linarith
  rw [Prod.norm_def]
  rcases le_total ‖p.1‖ ‖p.2‖ with h | h
  · rw [max_eq_right h]; exact h2
  · rw [max_eq_left h]; exact h1

end Norms

end

end Work.BoseSym.Minimiser
