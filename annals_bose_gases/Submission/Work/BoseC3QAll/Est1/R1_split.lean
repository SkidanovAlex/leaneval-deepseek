import Mathlib.Tactic.Abel
import Mathlib.Algebra.Module.BigOperators
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Module.LinearMap.End
import Submission.Work.BoseC3QAll.Est1.estR1_defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseC3QAll.Est1.R1_split` — the decomposition of the leftover `R1`

The leftover `R1` of `Est1.Defs` (FS's `T₁(k)` plus the commutator part of `T₂`) is the
`(s,k)`-double sum

  `R1 = (z/ℓ³) Σ_{s ∈ excited} Σ_{k ∈ P_H} γ_{sk}β_{sk} •
        ( κB_{sk}(b_k†+b_k) + κA_{sk}(b_{s-k}†+b_{s-k}) - κC_{sk}(ã_{-s}†+ã_{-s}) )`,

and the three pieces of the linear word are estimated one by one (`Est1.Wta` for the
`κC`-word, `Est1.Wb1` for the `κB`-word, `Est1.Wb2` for the `κA`-word).  This module
proves the purely algebraic split

  `R1 = Wta + Wb1 + Wb2`,

which is what lets `Est1.Wta_bound`, `Est1.Wb1_bound`, `Est1.Wb2_bound` be applied to
the three families separately.

The proof is bookkeeping with the definitions:

* the `s`-sum may be restricted from `excited Mode` to `suppL E` because every summand
  carries the factor `gA E s k = f_L(s)·Ŵ₁(k)·q3Denom(s,k)`, which vanishes when
  `f_L(s) = 0` (`Est1.mem_suppL`);
* the common factor `gA·bA` is pushed into the three coefficients (`smul_smul`), which
  turns the inner bracket into a sum of the three separately-collected words;
* in `Wta` the `-` of the `κC`-coefficient is absorbed into the mode sum.

## Contents

* `smul_smul_sub`, `smul_double_sum`, `double_sum_add_sub`, `smul_sum_neg` — the four
  elementary rewrites used in the bookkeeping.
* `R1_split` — the identity itself.
-/

noncomputable section

open scoped BigOperators

namespace Work.BoseC3QAll

namespace Est1

open Work.BoseB7

variable {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]

/-! ## Elementary rewrites -/

/-- Pushing a scalar through a two-term combination: the normal form of the summand of
`R1`. -/
theorem smul_smul_sub {M : Type*} [AddCommGroup M] [Module ℝ M] (a b c d : ℝ) (X Y Z : M) :
    a • (b • X + c • Y - d • Z) = (a * b) • X + (a * c) • Y - (a * d) • Z := by
  simp only [smul_sub, smul_add, smul_smul]

/-- Pushing a scalar inside a double sum and collecting it into the coefficients. -/
theorem smul_double_sum {ι κ M : Type*} [AddCommGroup M] [Module ℝ M]
    (S : Finset ι) (K : Finset κ) (a : ℝ) (c : ι → κ → ℝ) (x : ι → κ → M) :
    a • (∑ i ∈ S, ∑ j ∈ K, c i j • x i j) = ∑ i ∈ S, ∑ j ∈ K, (a * c i j) • x i j := by
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Finset.smul_sum]
  exact Finset.sum_congr rfl (fun j _ => smul_smul a (c i j) (x i j))

/-- Splitting a double sum of a three-term combination into three double sums. -/
theorem double_sum_add_sub {ι κ M : Type*} [AddCommGroup M]
    (S : Finset ι) (K : Finset κ) (A B C : ι → κ → M) :
    (∑ i ∈ S, ∑ j ∈ K, (A i j + B i j - C i j))
      = (∑ i ∈ S, ∑ j ∈ K, A i j) + (∑ i ∈ S, ∑ j ∈ K, B i j)
        - (∑ i ∈ S, ∑ j ∈ K, C i j) := by
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib]

/-- Absorbing the `-` of a negated coefficient into the mode sum. -/
theorem smul_sum_neg {ι M : Type*} [AddCommGroup M] [Module ℝ M]
    (s : Finset ι) (a : ℝ) (c : ι → ℝ) (x : M) :
    (a * ∑ i ∈ s, -(c i)) • x = -(∑ i ∈ s, (a * c i) • x) := by
  rw [← smul_smul, Finset.sum_smul, Finset.smul_sum]
  have h : ∀ i ∈ s, a • ((-(c i)) • x) = -((a * c i) • x) := by
    intro i _
    rw [smul_smul, mul_neg, neg_smul]
  rw [Finset.sum_congr rfl h, Finset.sum_neg_distrib]

/-! ## The split -/

/-- **`R1` splits into its three families**: the `κC`- (θ-) word `Wta`, the `κB`-word
`Wb1` and the `κA`-word `Wb2`. -/
theorem R1_split {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    (F : Work.BoseB7.FockData Mode) (T : Work.BoseC3QAll.TildeData F) (E : Work.BoseB7.Q3Env Mode) :
    Work.BoseC3QAll.Est1.R1 F T E = Work.BoseC3QAll.Est1.Wta F T E + Work.BoseC3QAll.Est1.Wb1 F T E
      + Work.BoseC3QAll.Est1.Wb2 F T E := by
  set L1 : F.H →ₗ[ℝ] F.H := ∑ s ∈ Work.BoseC3QAll.Est1.suppL E, ∑ k ∈ F.PHset E,
      (Work.BoseC3QAll.Est1.gA E s k * Work.BoseC3QAll.Est1.bA E s k
        * Work.BoseC3QAll.Est1.kB T E s k) •
        (F.bOpDag E.alpha k + F.bOp E.alpha k) with hL1
  set L2 : F.H →ₗ[ℝ] F.H := ∑ s ∈ Work.BoseC3QAll.Est1.suppL E, ∑ k ∈ F.PHset E,
      (Work.BoseC3QAll.Est1.gA E s k * Work.BoseC3QAll.Est1.bA E s k
        * Work.BoseC3QAll.Est1.kA T E s k) •
        (F.bOpDag E.alpha (s - k) + F.bOp E.alpha (s - k)) with hL2
  set L3 : F.H →ₗ[ℝ] F.H := ∑ s ∈ Work.BoseC3QAll.Est1.suppL E, ∑ k ∈ F.PHset E,
      (Work.BoseC3QAll.Est1.gA E s k * Work.BoseC3QAll.Est1.bA E s k
        * Work.BoseC3QAll.Est1.kC E s k) •
        (T.taDag (-s) + T.ta (-s)) with hL3
  -- the `s`-sum may be restricted to `suppL E`
  have hsupp : (∑ s ∈ Work.BoseB7.excited Mode, ∑ k ∈ F.PHset E,
        (Work.BoseC3QAll.Est1.gA E s k * Work.BoseC3QAll.Est1.bA E s k) •
          (Work.BoseC3QAll.Est1.kB T E s k • (F.bOpDag E.alpha k + F.bOp E.alpha k)
            + Work.BoseC3QAll.Est1.kA T E s k •
                (F.bOpDag E.alpha (s - k) + F.bOp E.alpha (s - k))
            - Work.BoseC3QAll.Est1.kC E s k • (T.taDag (-s) + T.ta (-s))))
      = ∑ s ∈ Work.BoseC3QAll.Est1.suppL E, ∑ k ∈ F.PHset E,
        (Work.BoseC3QAll.Est1.gA E s k * Work.BoseC3QAll.Est1.bA E s k) •
          (Work.BoseC3QAll.Est1.kB T E s k • (F.bOpDag E.alpha k + F.bOp E.alpha k)
            + Work.BoseC3QAll.Est1.kA T E s k •
                (F.bOpDag E.alpha (s - k) + F.bOp E.alpha (s - k))
            - Work.BoseC3QAll.Est1.kC E s k • (T.taDag (-s) + T.ta (-s))) := by
    refine (Finset.sum_subset (s₁ := Work.BoseC3QAll.Est1.suppL E)
      (s₂ := Work.BoseB7.excited Mode) Work.BoseC3QAll.Est1.suppL_subset ?_).symm
    intro s hs hns
    have hfL : E.fL s = 0 := by
      by_contra h
      exact hns (Work.BoseC3QAll.Est1.mem_suppL.mpr ⟨hs, h⟩)
    refine Finset.sum_eq_zero (fun k _ => ?_)
    simp only [Work.BoseC3QAll.Est1.gA, hfL, zero_mul, zero_smul]
  have hLHS : Work.BoseC3QAll.Est1.R1 F T E = (E.z / E.ell ^ 3) • (L1 + L2 - L3) := by
    rw [Work.BoseC3QAll.Est1.R1, hsupp]
    congr 1
    rw [hL1, hL2, hL3]
    simp only [Work.BoseC3QAll.Est1.smul_smul_sub]
    rw [Work.BoseC3QAll.Est1.double_sum_add_sub]
  have hWb1 : (E.z / E.ell ^ 3) • L1 = Work.BoseC3QAll.Est1.Wb1 F T E := by
    rw [hL1, Work.BoseC3QAll.Est1.Wb1]
    exact Work.BoseC3QAll.Est1.smul_double_sum (Work.BoseC3QAll.Est1.suppL E) (F.PHset E)
      (E.z / E.ell ^ 3)
      (fun s k => Work.BoseC3QAll.Est1.gA E s k * Work.BoseC3QAll.Est1.bA E s k
        * Work.BoseC3QAll.Est1.kB T E s k)
      (fun s k => F.bOpDag E.alpha k + F.bOp E.alpha k)
  have hWb2 : (E.z / E.ell ^ 3) • L2 = Work.BoseC3QAll.Est1.Wb2 F T E := by
    rw [hL2, Work.BoseC3QAll.Est1.Wb2]
    exact Work.BoseC3QAll.Est1.smul_double_sum (Work.BoseC3QAll.Est1.suppL E) (F.PHset E)
      (E.z / E.ell ^ 3)
      (fun s k => Work.BoseC3QAll.Est1.gA E s k * Work.BoseC3QAll.Est1.bA E s k
        * Work.BoseC3QAll.Est1.kA T E s k)
      (fun s k => F.bOpDag E.alpha (s - k) + F.bOp E.alpha (s - k))
  have hWta : (E.z / E.ell ^ 3) • L3 = - Work.BoseC3QAll.Est1.Wta F T E := by
    rw [hL3, Work.BoseC3QAll.Est1.Wta]
    rw [Work.BoseC3QAll.Est1.smul_double_sum (Work.BoseC3QAll.Est1.suppL E) (F.PHset E)
      (E.z / E.ell ^ 3)
      (fun s k => Work.BoseC3QAll.Est1.gA E s k * Work.BoseC3QAll.Est1.bA E s k
        * Work.BoseC3QAll.Est1.kC E s k)
      (fun s _ => T.taDag (-s) + T.ta (-s))]
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl (fun s _ => ?_)
    simp only [Work.BoseC3QAll.Est1.cTa]
    have hsum : (∑ k ∈ F.PHset E,
          Work.BoseC3QAll.Est1.gA E s k * Work.BoseC3QAll.Est1.bA E s k
            * -(Work.BoseC3QAll.Est1.kC E s k))
        = ∑ k ∈ F.PHset E, -((fun k => Work.BoseC3QAll.Est1.gA E s k
            * Work.BoseC3QAll.Est1.bA E s k * Work.BoseC3QAll.Est1.kC E s k) k) := by
      refine Finset.sum_congr rfl (fun k _ => ?_)
      exact mul_neg _ _
    rw [hsum]
    rw [Work.BoseC3QAll.Est1.smul_sum_neg (F.PHset E) (E.z / E.ell ^ 3)
      (fun k => Work.BoseC3QAll.Est1.gA E s k * Work.BoseC3QAll.Est1.bA E s k
        * Work.BoseC3QAll.Est1.kC E s k)
      (T.taDag (-s) + T.ta (-s))]
    rw [neg_neg]
  rw [hLHS, smul_sub, smul_add, hWb1, hWb2, hWta]
  abel

end Est1

end Work.BoseC3QAll
