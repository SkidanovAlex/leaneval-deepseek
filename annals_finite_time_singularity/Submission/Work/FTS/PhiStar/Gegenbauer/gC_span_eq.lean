/-
# `Work.FTS.PhiStar.Gegenbauer.gC_span_eq` — the odd Gegenbauer polynomials are a basis

The target is

`span {C^{(3/2)}_{2k+1} | k ≤ N} = span {x^{2k+1} | k ≤ N}`  (as subspaces of `ℝ → ℝ`).

`C^{(3/2)}_{2k+1} = gC (2k+1)` is an odd polynomial whose leading term is a nonzero multiple of
`x^{2k+1}`; hence the two families are related by a triangular change of basis, and the two spans
agree.  The triangularity is made explicit:

* `gC_tail_struct k` (proved by induction) states that the "tails"
  `A (k+1) - a (k+1) • X (k+1)` and `B (k+1) - c (k+1) • Y (k+1)` lie one degree lower, in
  `evenSpan k` resp. `oddSpan k`, where `a k`, `c k` are the (nonzero) leading coefficients of
  `gC (2k)` and `gC (2k+1)`.  The induction steps are exactly the tail identities `A_tail`,
  `B_tail` of `gCSpanDefs` applied to the `mulX`-calculus for the spans.
* `oddSpan_le_span_B k` (proved by induction) is the reverse inclusion: every odd monomial of
  degree `≤ 2k+1` is a linear combination of `gC 1, gC 3, …, gC (2k+1)`, obtained by solving the
  triangular system.

Everything else is bookkeeping. -/
import Mathlib.Algebra.Algebra.Operations
import Mathlib.Algebra.Algebra.Pi
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Submission.Work.FTS.PhiStar.Gegenbauer.Defs
import Submission.Work.FTS.PhiStar.Gegenbauer.gC_ode
import Submission.Work.FTS.PhiStar.Gegenbauer.gCSpanDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real

namespace Work.FTS.PhiStar.Gegenbauer

set_option autoImplicit false

/-! ## The low-index monomials and the two explicit low-degree values -/

lemma X_zero : X 0 = fun _ : ℝ => (1 : ℝ) := by
  funext x
  show x ^ (2 * 0) = 1
  rw [show 2 * 0 = 0 by norm_num, pow_zero]

lemma X_one : X 1 = fun x : ℝ => x ^ 2 := by
  funext x
  show x ^ (2 * 1) = x ^ 2
  rw [show 2 * 1 = 2 by norm_num]

lemma Y_zero : Y 0 = fun x : ℝ => x := by
  funext x
  show x ^ (2 * 0 + 1) = x
  rw [show 2 * 0 + 1 = 1 by norm_num, pow_one]

lemma Y_one : Y 1 = fun x : ℝ => x ^ 3 := by
  funext x
  show x ^ (2 * 1 + 1) = x ^ 3
  rw [show 2 * 1 + 1 = 3 by norm_num]

lemma gC_two (x : ℝ) : gC 2 x = (15 * x ^ 2 - 3) / 2 := by
  simp only [gC]; norm_num; ring

lemma gC_three (x : ℝ) : gC 3 x = (35 * x ^ 3 - 15 * x) / 2 := by
  simp only [gC]; norm_num; ring

lemma a_one : a 1 = 15 / 2 := by
  rw [show a 1 = cfA 0 * c 0 from a_succ 0, c_zero, cfA]
  norm_num

lemma c_one : c 1 = 35 / 2 := by
  rw [show c 1 = cfC 0 * (cfA 0 * c 0) from c_succ 0, c_zero, cfC, cfA]
  norm_num

/-! ## The structural (triangularity) induction -/

/-- The tails of the odd/even indexed Gegenbauer polynomials drop one degree: the difference of
`gC (2k+2) = A (k+1)` from its leading term `a (k+1) • x^{2k+2}` is an even polynomial of degree
`≤ 2k`, and likewise for `gC (2k+3) = B (k+1)` with `c (k+1) • x^{2k+3}`. -/
lemma gC_tail_struct (k : ℕ) :
    A (k + 1) - a (k + 1) • X (k + 1) ∈ evenSpan k ∧
      B (k + 1) - c (k + 1) • Y (k + 1) ∈ oddSpan k := by
  induction k with
  | zero =>
    refine ⟨?_, ?_⟩
    · have h : A 1 - a 1 • X 1 = (-(3 / 2) : ℝ) • X 0 := by
        funext x
        simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
        rw [show A 1 x = (15 * x ^ 2 - 3) / 2 from gC_two x, a_one, X_one, X_zero]
        norm_num
        ring
      rw [h]
      exact Submodule.smul_mem _ _ (X_mem 0)
    · have h : B 1 - c 1 • Y 1 = (-(15 / 2) : ℝ) • Y 0 := by
        funext x
        simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
        rw [show B 1 x = (35 * x ^ 3 - 15 * x) / 2 from gC_three x, c_one, Y_one, Y_zero]
        norm_num
        ring
      rw [h]
      exact Submodule.smul_mem _ _ (Y_mem 0)
  | succ k ih =>
    obtain ⟨hU, hT⟩ := ih
    -- `A (k+1) ∈ evenSpan (k+1)` and `B (k+1) ∈ oddSpan (k+1)`, from the tails at level `k`
    have hA : A (k + 1) ∈ evenSpan (k + 1) := by
      have h1 : A (k + 1) - a (k + 1) • X (k + 1) ∈ evenSpan (k + 1) :=
        evenSpan_mono (Nat.le_succ k) hU
      have h2 : a (k + 1) • X (k + 1) ∈ evenSpan (k + 1) :=
        Submodule.smul_mem _ _ (X_mem (k + 1))
      have h3 := Submodule.add_mem _ h1 h2
      rwa [sub_add_cancel] at h3
    have hB : B (k + 1) ∈ oddSpan (k + 1) := by
      have h1 : B (k + 1) - c (k + 1) • Y (k + 1) ∈ oddSpan (k + 1) :=
        oddSpan_mono (Nat.le_succ k) hT
      have h2 : c (k + 1) • Y (k + 1) ∈ oddSpan (k + 1) :=
        Submodule.smul_mem _ _ (Y_mem (k + 1))
      have h3 := Submodule.add_mem _ h1 h2
      rwa [sub_add_cancel] at h3
    -- the new even tail, from `A_tail`
    have hU2 : A (k + 2) - a (k + 2) • X (k + 2) ∈ evenSpan (k + 1) := by
      rw [A_tail (k + 1)]
      exact Submodule.sub_mem _ (Submodule.smul_mem _ _ (mulX_mem_of_mem_oddSpan hT))
        (Submodule.smul_mem _ _ hA)
    refine ⟨hU2, ?_⟩
    -- the new odd tail, from `B_tail`
    rw [B_tail (k + 1)]
    exact Submodule.sub_mem _ (Submodule.smul_mem _ _ (mulX_mem_of_mem_evenSpan hU2))
      (Submodule.smul_mem _ _ hB)

/-! ## The reverse inclusion -/

/-- Every odd monomial `x^{2j+1}`, `j ≤ k`, is a linear combination of `gC 1, gC 3, …,
gC (2k+1)`. -/
lemma oddSpan_le_span_B (k : ℕ) : oddSpan k ≤ Submodule.span ℝ (B '' Set.Iic k) := by
  induction k with
  | zero =>
    rw [oddSpan, Submodule.span_le]
    rintro f ⟨j, hj, rfl⟩
    have hj0 : j = 0 := Nat.le_zero.mp (Set.mem_Iic.mp hj)
    subst hj0
    have h : Y 0 = (1 / 3 : ℝ) • B 0 := by
      funext x
      show x ^ (2 * 0 + 1) = (1 / 3 : ℝ) * (3 * x)
      norm_num
      ring
    rw [h]
    exact Submodule.smul_mem _ _
      (Submodule.subset_span ⟨0, Set.mem_Iic.mpr le_rfl, rfl⟩)
  | succ k ih =>
    have hT : B (k + 1) - c (k + 1) • Y (k + 1) ∈ oddSpan k := (gC_tail_struct k).2
    have hmono : Submodule.span ℝ (B '' Set.Iic k) ≤ Submodule.span ℝ (B '' Set.Iic (k + 1)) :=
      Submodule.span_mono (Set.image_mono (fun j hj => le_trans hj (Nat.le_succ k)))
    have hV : B (k + 1) - c (k + 1) • Y (k + 1)
        ∈ Submodule.span ℝ (B '' Set.Iic (k + 1)) := hmono (ih hT)
    have hB1 : B (k + 1) ∈ Submodule.span ℝ (B '' Set.Iic (k + 1)) :=
      Submodule.subset_span ⟨k + 1, Set.mem_Iic.mpr le_rfl, rfl⟩
    have hY : Y (k + 1) ∈ Submodule.span ℝ (B '' Set.Iic (k + 1)) := by
      have htail : B (k + 1) - (B (k + 1) - c (k + 1) • Y (k + 1))
          = c (k + 1) • Y (k + 1) := by abel
      have hcz : (c (k + 1))⁻¹
          • (B (k + 1) - (B (k + 1) - c (k + 1) • Y (k + 1))) = Y (k + 1) := by
        rw [htail, smul_smul, inv_mul_cancel₀ (c_ne_zero (k + 1)), one_smul]
      rw [← hcz]
      exact Submodule.smul_mem _ _ (Submodule.sub_mem _ hB1 hV)
    rw [oddSpan_succ]
    refine sup_le ?_ ?_
    · rwa [Submodule.span_singleton_le_iff_mem]
    · exact le_trans ih hmono

/-- `gC (2k+1) = B k` lies in the span of the first `k+1` odd monomials. -/
lemma B_mem (k : ℕ) : B k ∈ oddSpan k := by
  cases k with
  | zero =>
    have h : B 0 = (3 : ℝ) • Y 0 := by
      funext x
      show 3 * x = (3 : ℝ) * x ^ (2 * 0 + 1)
      rw [show 2 * 0 + 1 = (1 : ℕ) by norm_num, pow_one]
    rw [h]
    exact Submodule.smul_mem _ _ (Y_mem 0)
  | succ k =>
    have hT : B (k + 1) - c (k + 1) • Y (k + 1) ∈ oddSpan k := (gC_tail_struct k).2
    have h : B (k + 1) = (B (k + 1) - c (k + 1) • Y (k + 1)) + c (k + 1) • Y (k + 1) := by
      abel
    rw [h]
    exact Submodule.add_mem _ (oddSpan_mono (Nat.le_succ k) hT)
      (Submodule.smul_mem _ _ (Y_mem (k + 1)))

/-! ## The target -/

theorem gC_span_eq (N : ℕ) :
    Submodule.span ℝ ((fun k : ℕ => Work.FTS.PhiStar.Gegenbauer.gC (2 * k + 1)) '' Set.Iic N)
      = Submodule.span ℝ ((fun k : ℕ => fun u : ℝ => u ^ (2 * k + 1)) '' Set.Iic N) := by
  have hBfun : (fun k : ℕ => Work.FTS.PhiStar.Gegenbauer.gC (2 * k + 1)) = B := rfl
  have hYfun : (fun k : ℕ => fun u : ℝ => u ^ (2 * k + 1)) = Y := rfl
  rw [hBfun, hYfun]
  refine le_antisymm ?_ ?_
  · rw [Submodule.span_le]
    rintro f ⟨k, hk, rfl⟩
    exact oddSpan_mono hk (B_mem k)
  · exact oddSpan_le_span_B N

end Work.FTS.PhiStar.Gegenbauer
