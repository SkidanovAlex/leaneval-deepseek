/-
Copyright: work module for the Elgindi finite-time singularity project.

# Scaling the norms of the chapter, and the `prop:H2` ⟸ `prop:Hk` corollary

The operators `pz`, `pth`, `Dz`, `Dth` and their iterates are *linear over constants* — Lean's
totalised `deriv` commutes with multiplication by a constant unconditionally
(`deriv_const_mul_field`), because both sides vanish at a non-differentiable point.  Hence all
the functionals of the chapter (`L2Sq`, `L2Norm`, `HkIntegrand`, `HkSq`, `HkNorm`) scale
homogeneously, and the honesty predicates `Work.Spaces.HkMem`, `Work.Spaces.L2Mem` are invariant
under multiplication by a nonzero constant.

This file also records the observation that Proposition `prop:H2` (tex 837) is Proposition
`prop:Hk` (tex 986) at `k = 2`: the paper's `C_2` is exactly the universal constant `C_2` of
`prop:Hk`.  A consumer who has `propHk_fts` therefore has `propH2_fts` with no extra work; the
corollary below is stated with the `prop:Hk` statement as an explicit hypothesis so that it can
be used before (or instead of) the `Hk` core.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Order.Interval.Basic
import Submission.Work.FTS.EllipticEst.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology Interval
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst

set_option autoImplicit false
set_option linter.unusedSimpArgs false

/-! ## The derivative operators commute with scalar multiplication -/

theorem pz_smul (c : ℝ) (f : ℝ → ℝ → ℝ) : Work.Spaces.pz (c • f) = c • Work.Spaces.pz f := by
  funext z θ
  simp only [Work.Spaces.pz, Pi.smul_apply, smul_eq_mul]
  exact deriv_const_mul_field c

theorem pth_smul (c : ℝ) (f : ℝ → ℝ → ℝ) : Work.Spaces.pth (c • f) = c • Work.Spaces.pth f := by
  funext z θ
  simp only [Work.Spaces.pth, Pi.smul_apply, smul_eq_mul]
  exact deriv_const_mul_field c

theorem pzIter_smul (c : ℝ) (f : ℝ → ℝ → ℝ) (n : ℕ) :
    Work.Spaces.pzIter n (c • f) = c • Work.Spaces.pzIter n f := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Work.Spaces.pzIter_succ, ih, pz_smul, Work.Spaces.pzIter_succ]

theorem pthIter_smul (c : ℝ) (f : ℝ → ℝ → ℝ) (n : ℕ) :
    Work.Spaces.pthIter n (c • f) = c • Work.Spaces.pthIter n f := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Work.Spaces.pthIter_succ, ih, pth_smul, Work.Spaces.pthIter_succ]

theorem Dz_smul (c : ℝ) (f : ℝ → ℝ → ℝ) : Work.Spaces.Dz (c • f) = c • Work.Spaces.Dz f := by
  funext z θ
  simp only [Work.Spaces.Dz, pz_smul, Pi.smul_apply, smul_eq_mul]
  ring

theorem Dth_smul (c : ℝ) (f : ℝ → ℝ → ℝ) : Work.Spaces.Dth (c • f) = c • Work.Spaces.Dth f := by
  funext z θ
  simp only [Work.Spaces.Dth, pth_smul, Pi.smul_apply, smul_eq_mul]
  ring

theorem DzIter_smul (c : ℝ) (f : ℝ → ℝ → ℝ) (n : ℕ) :
    Work.Spaces.DzIter n (c • f) = c • Work.Spaces.DzIter n f := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Work.Spaces.DzIter_succ, ih, Dz_smul, Work.Spaces.DzIter_succ]

theorem DthIter_smul (c : ℝ) (f : ℝ → ℝ → ℝ) (n : ℕ) :
    Work.Spaces.DthIter n (c • f) = c • Work.Spaces.DthIter n f := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Work.Spaces.DthIter_succ, ih, Dth_smul, Work.Spaces.DthIter_succ]

theorem mixed_smul (c : ℝ) (f : ℝ → ℝ → ℝ) (j i : ℕ) :
    Work.Spaces.mixed j i (c • f) = c • Work.Spaces.mixed j i f := by
  simp only [Work.Spaces.mixed, DzIter_smul, DthIter_smul]

/-! ## The norm functionals are homogeneous -/

theorem HkIntegrand_smul (c : ℝ) (α : ℝ) (k : ℕ) (f : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.HkIntegrand α k (c • f) z θ = c ^ 2 * Work.Spaces.HkIntegrand α k f z θ := by
  simp only [Work.Spaces.HkIntegrand, DzIter_smul, mixed_smul, Pi.smul_apply, smul_eq_mul]
  rw [mul_add]
  congr 1
  · rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  · rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    by_cases h : (1 ≤ i ∧ i + j ≤ k)
    · simp only [if_pos h]
      ring
    · simp only [if_neg h]
      ring

theorem HkSq_smul (c : ℝ) (α : ℝ) (k : ℕ) (f : ℝ → ℝ → ℝ) :
    Work.Spaces.HkSq α k (c • f) = c ^ 2 * Work.Spaces.HkSq α k f := by
  have hfun : (fun z => ∫ θ in Work.Spaces.Iθ,
        Work.Spaces.HkIntegrand α k (c • f) z θ)
      = fun z => c ^ 2 * ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k f z θ := by
    funext z
    rw [show (fun θ => Work.Spaces.HkIntegrand α k (c • f) z θ)
        = fun θ => c ^ 2 * Work.Spaces.HkIntegrand α k f z θ from
      funext fun θ => HkIntegrand_smul c α k f z θ]
    exact integral_const_mul _ _
  simp only [Work.Spaces.HkSq]
  rw [hfun]
  exact integral_const_mul _ _

theorem HkNorm_smul (c : ℝ) (α : ℝ) (k : ℕ) (f : ℝ → ℝ → ℝ) :
    Work.Spaces.HkNorm α k (c • f) = |c| * Work.Spaces.HkNorm α k f := by
  rw [Work.Spaces.HkNorm, HkSq_smul, Work.Spaces.HkNorm]
  rw [Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq_eq_abs]

theorem L2Sq_smul (c : ℝ) (f : ℝ → ℝ → ℝ) :
    Work.Spaces.L2Sq (c • f) = c ^ 2 * Work.Spaces.L2Sq f := by
  have hfun : (fun z => ∫ θ in Work.Spaces.Iθ, ((c • f) z θ) ^ 2)
      = fun z => c ^ 2 * ∫ θ in Work.Spaces.Iθ, (f z θ) ^ 2 := by
    funext z
    rw [show (fun θ => ((c • f) z θ) ^ 2) = fun θ => c ^ 2 * (f z θ) ^ 2 from
      funext fun θ => by simp only [Pi.smul_apply, smul_eq_mul]; ring]
    exact integral_const_mul _ _
  simp only [Work.Spaces.L2Sq]
  rw [hfun]
  exact integral_const_mul _ _

theorem L2Norm_smul (c : ℝ) (f : ℝ → ℝ → ℝ) : L2Norm (c • f) = |c| * L2Norm f := by
  rw [L2Norm_eq_sqrt, L2Sq_smul, L2Norm_eq_sqrt, Real.sqrt_mul (sq_nonneg c),
    Real.sqrt_sq_eq_abs]

/-! ## Honesty is invariant under a nonzero scalar -/

theorem HkMem_smul {c : ℝ} (_hc : c ≠ 0) (α : ℝ) (k : ℕ) {f : ℝ → ℝ → ℝ}
    (h : Work.Spaces.HkMem α k f) : Work.Spaces.HkMem α k (c • f) := by
  constructor
  · intro z hz
    have h1 : (fun θ : ℝ => Work.Spaces.HkIntegrand α k (c • f) z θ)
        = fun θ => c ^ 2 * Work.Spaces.HkIntegrand α k f z θ :=
      funext fun θ => HkIntegrand_smul c α k f z θ
    rw [h1]
    exact (h.1 z hz).const_mul _
  · have h1 : (fun z : ℝ => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k (c • f) z θ)
        = fun z => c ^ 2 * ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k f z θ := by
      funext z
      rw [show (fun θ => Work.Spaces.HkIntegrand α k (c • f) z θ)
          = fun θ => c ^ 2 * Work.Spaces.HkIntegrand α k f z θ from
        funext fun θ => HkIntegrand_smul c α k f z θ]
      exact integral_const_mul _ _
    rw [h1]
    exact h.2.const_mul _

theorem L2Mem_smul {c : ℝ} (_hc : c ≠ 0) {f : ℝ → ℝ → ℝ} (h : Work.Spaces.L2Mem f) :
    Work.Spaces.L2Mem (c • f) := by
  constructor
  · intro z hz
    have h1 : (fun θ : ℝ => ((c • f) z θ) ^ 2) = fun θ => c ^ 2 * (f z θ) ^ 2 :=
      funext fun θ => by simp only [Pi.smul_apply, smul_eq_mul]; ring
    rw [h1]
    exact (h.1 z hz).const_mul _
  · have h1 : (fun z : ℝ => ∫ θ in Work.Spaces.Iθ, ((c • f) z θ) ^ 2)
        = fun z => c ^ 2 * ∫ θ in Work.Spaces.Iθ, (f z θ) ^ 2 := by
      funext z
      rw [show (fun θ => ((c • f) z θ) ^ 2) = fun θ => c ^ 2 * (f z θ) ^ 2 from
        funext fun θ => by simp only [Pi.smul_apply, smul_eq_mul]; ring]
      exact integral_const_mul _ _
    rw [h1]
    exact h.2.const_mul _

/-! ## `prop:H2` is `prop:Hk` at `k = 2` -/

/-- **Proposition `prop:H2` (tex 837) follows from Proposition `prop:Hk` (tex 986) at `k = 2`.**
The paper's `C_2` is the `k = 2` instance of its `C_k`; the `k`-dependence of the constant is
already allowed in the `prop:Hk` statement, so no further analysis is needed. -/
theorem propH2_of_propHk
    (hHk : ∀ k : ℕ, 2 ≤ k → ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (F Ψ : ℝ → ℝ → ℝ),
      0 < α → α ≤ 1 / 4 → EllHyp α k F Ψ →
      Work.Elliptic.OrthCond F → Work.Elliptic.OrthCond Ψ →
      α ^ 2 * Work.Spaces.HkNorm α k (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)
        + Work.Spaces.HkNorm α k (Work.Spaces.pthIter 2 Ψ)
      ≤ C * Work.Spaces.HkNorm α k F) :
    ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (F Ψ : ℝ → ℝ → ℝ),
      0 < α → α ≤ 1 / 4 → EllHyp α 2 F Ψ →
      Work.Elliptic.OrthCond F → Work.Elliptic.OrthCond Ψ →
      α ^ 2 * Work.Spaces.HkNorm α 2 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)
        + Work.Spaces.HkNorm α 2 (Work.Spaces.pthIter 2 Ψ)
      ≤ C * Work.Spaces.HkNorm α 2 F := by
  obtain ⟨C, hC, h⟩ := hHk 2 (by norm_num)
  exact ⟨C, hC, fun α F Ψ hα hα4 hH hF hΨ => h α F Ψ hα hα4 hH hF hΨ⟩

end Work.FTS.EllipticEst
