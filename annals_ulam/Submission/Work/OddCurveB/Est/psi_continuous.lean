import Mathlib
import Submission.Work.OddCurveB.Est.Defs

/-!
# Continuity of the diagonal linearization `s ↦ Psi n s`

This file proves `Work.OddCurveB.Est.psi_continuous`: on every compact slope interval
`[a, b]` with `a > 0` the map

`s ↦ Psi n s = ContinuousLinearMap.pi ![Proj 0, Proj 1, psiRow2 n s, psiRow3 n s]`

is continuous.

`Psi n s` is the candidate inverse of the diagonal linearization `Phi n s = fderiv (Godd n 0 s)`
at the base state (see `Est/Defs.lean`).  Its two non-constant rows are scalar combinations of the
four fixed coordinate projections `Proj 0, …, Proj 3`, so the whole statement is the continuity of
the four scalar coefficient functions

`dc1 n ·`, `dc2 n ·`, `profileX`, `deriv profileX`

on `(0, ∞)` (they are built from `s ↦ (-s)^k / √(2s)` and `s ↦ 1/√(1+s²)`), combined with the
inversion `s ↦ (2 pA n s)⁻¹`, `s ↦ (2 pC n s)⁻¹` (legitimate on `(0, ∞)` by `pA_ne_zero`,
`pC_ne_zero`).

The one point that is not an instance of `ContinuousOn.mul/div` is that `ContinuousLinearMap.pi`
is not a `ContinuousOn` combinator: `Psi n s` is a continuous linear map, not a function into a
product.  The bridge is `pi_eq_sum_smulRight`: on the finite coordinate space
`St = Fin 4 → ℝ` the map `pi` agrees with the finite sum `∑ i, (f i).smulRight (Pi.single i 1)`,
and each summand is the composition of the continuous linear map `ContinuousLinearMap.smulRightL`
with the (continuous) row `f i`.
-/

namespace Work.OddCurveB.Est

open MeasureTheory Set Filter
open scoped Topology ContDiff Interval

open Work.OddVolterra

noncomputable section

/-! ## A matrix decomposition of `ContinuousLinearMap.pi` -/

/-- On the coordinate space `St = Fin 4 → ℝ`, the `pi`-construction of continuous linear maps is
the finite sum of the `smulRight`s of its components: the operator `ContinuousLinearMap.pi f` and
`∑ i, (f i).smulRight (Pi.single i 1)` have the same `(i, j)`-entry `f i (Pi.single j 1)`. -/
lemma pi_eq_sum_smulRight {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : ι → St →L[ℝ] ℝ) :
    ContinuousLinearMap.pi f = ∑ i, (f i).smulRight (Pi.single i (1 : ℝ)) := by
  ext x j
  simp only [ContinuousLinearMap.pi_apply, sum_apply, ContinuousLinearMap.smulRight_apply]
  rw [Finset.sum_apply]
  simp only [Pi.smul_apply, Pi.single_apply]
  simp

/-! ## The scalar coefficient functions are continuous on `(0, ∞)` -/

lemma continuous_profileX : Continuous (fun s : ℝ => Commons.Geometry.Ulam.profileX s) := by
  unfold Commons.Geometry.Ulam.profileX
  refine Continuous.div continuous_const ?_ ?_
  · exact (by fun_prop : Continuous fun s : ℝ => 1 + s ^ 2).sqrt
  · intro s
    exact ne_of_gt (Real.sqrt_pos.2 (by positivity))

/-- `deriv profileX` is continuous: `profileX s = 1/√(1+s²)` is `C¹`. -/
lemma continuous_deriv_profileX :
    Continuous (fun s : ℝ => deriv Commons.Geometry.Ulam.profileX s) := by
  have h : ContDiff ℝ 1 Commons.Geometry.Ulam.profileX := by
    unfold Commons.Geometry.Ulam.profileX
    refine ContDiff.div contDiff_const ?_ ?_
    · apply ContDiff.sqrt (by fun_prop)
      intro s; positivity
    · intro x
      exact ne_of_gt (Real.sqrt_pos.2 (by positivity))
  exact h.continuous_deriv le_rfl

lemma continuousOn_dc1 (n : ℕ) : ContinuousOn (fun s : ℝ => dc1 n s) (Set.Ioi 0) := by
  unfold dc1
  refine ContinuousOn.div ?_ ?_ ?_
  · fun_prop
  · exact ((by fun_prop : Continuous fun s : ℝ => 2 * s).sqrt).continuousOn
  · intro s hs
    exact ne_of_gt (Real.sqrt_pos.2 (mul_pos two_pos (Set.mem_Ioi.mp hs)))

lemma continuousOn_dc2 (n : ℕ) : ContinuousOn (fun s : ℝ => dc2 n s) (Set.Ioi 0) := by
  unfold dc2
  refine ContinuousOn.div ?_ ?_ ?_
  · fun_prop
  · exact ((by fun_prop : Continuous fun s : ℝ => 2 * s).sqrt).continuousOn
  · intro s hs
    exact ne_of_gt (Real.sqrt_pos.2 (mul_pos two_pos (Set.mem_Ioi.mp hs)))

lemma continuousOn_pA (n : ℕ) : ContinuousOn (fun s : ℝ => pA n s) (Set.Ioi 0) := by
  unfold pA
  refine ContinuousOn.mul (ContinuousOn.mul continuousOn_const (continuousOn_dc1 n)) ?_
  exact (continuous_profileX.continuousOn.pow _)

lemma continuousOn_pC (n : ℕ) : ContinuousOn (fun s : ℝ => pC n s) (Set.Ioi 0) := by
  unfold pC
  refine ContinuousOn.neg (ContinuousOn.mul (ContinuousOn.mul continuousOn_const (continuousOn_dc2 n)) ?_)
  exact (continuous_profileX.continuousOn.pow _)

lemma continuousOn_pAA (n : ℕ) : ContinuousOn (fun s : ℝ => pAA n s) (Set.Ioi 0) := by
  unfold pAA
  refine ContinuousOn.mul (ContinuousOn.mul (ContinuousOn.mul continuousOn_const (continuousOn_dc1 n)) ?_)
    continuous_deriv_profileX.continuousOn
  exact ContinuousOn.mul continuousOn_const (continuous_profileX.continuousOn.pow _)

lemma continuousOn_pGG (n : ℕ) : ContinuousOn (fun s : ℝ => pGG n s) (Set.Ioi 0) := by
  unfold pGG
  refine ContinuousOn.neg (ContinuousOn.mul (ContinuousOn.mul (ContinuousOn.mul continuousOn_const ?_)
    ?_) continuous_deriv_profileX.continuousOn)
  · exact ContinuousOn.mul continuousOn_const (continuousOn_dc2 n)
  · exact continuous_profileX.continuousOn.pow _

lemma continuousOn_invU (n : ℕ) : ContinuousOn (fun s : ℝ => invU n s) (Set.Ioi 0) := by
  unfold invU
  refine ContinuousOn.add
    (ContinuousOn.div (continuousOn_pAA n) (ContinuousOn.const_mul (continuousOn_pA n) 2) ?_)
    (ContinuousOn.div (continuousOn_pGG n) (ContinuousOn.const_mul (continuousOn_pC n) 2) ?_)
  · intro s hs
    exact mul_ne_zero two_ne_zero (pA_ne_zero n (show 0 < s from Set.mem_Ioi.mp hs))
  · intro s hs
    exact mul_ne_zero two_ne_zero (pC_ne_zero n (show 0 < s from Set.mem_Ioi.mp hs))

lemma continuousOn_invV (n : ℕ) : ContinuousOn (fun s : ℝ => invV n s) (Set.Ioi 0) := by
  unfold invV
  refine ContinuousOn.sub
    (ContinuousOn.div (continuousOn_pAA n) (ContinuousOn.const_mul (continuousOn_pA n) 2) ?_)
    (ContinuousOn.div (continuousOn_pGG n) (ContinuousOn.const_mul (continuousOn_pC n) 2) ?_)
  · intro s hs
    exact mul_ne_zero two_ne_zero (pA_ne_zero n (show 0 < s from Set.mem_Ioi.mp hs))
  · intro s hs
    exact mul_ne_zero two_ne_zero (pC_ne_zero n (show 0 < s from Set.mem_Ioi.mp hs))

lemma continuousOn_inv2pA (n : ℕ) :
    ContinuousOn (fun s : ℝ => (2 * pA n s)⁻¹) (Set.Ioi 0) :=
  ContinuousOn.inv₀ (ContinuousOn.const_mul (continuousOn_pA n) 2)
    (fun s hs => mul_ne_zero two_ne_zero (pA_ne_zero n (show 0 < s from Set.mem_Ioi.mp hs)))

lemma continuousOn_inv2pC (n : ℕ) :
    ContinuousOn (fun s : ℝ => (2 * pC n s)⁻¹) (Set.Ioi 0) :=
  ContinuousOn.inv₀ (ContinuousOn.const_mul (continuousOn_pC n) 2)
    (fun s hs => mul_ne_zero two_ne_zero (pC_ne_zero n (show 0 < s from Set.mem_Ioi.mp hs)))

lemma continuousOn_psiRow2 (n : ℕ) : ContinuousOn (fun s : ℝ => psiRow2 n s) (Set.Ioi 0) := by
  unfold psiRow2
  exact ContinuousOn.add
    (ContinuousOn.add
      (ContinuousOn.sub ((continuousOn_invU n).neg.smul continuousOn_const)
        ((continuousOn_invV n).smul continuousOn_const))
      ((continuousOn_inv2pA n).smul continuousOn_const))
    ((continuousOn_inv2pC n).smul continuousOn_const)

lemma continuousOn_psiRow3 (n : ℕ) : ContinuousOn (fun s : ℝ => psiRow3 n s) (Set.Ioi 0) := by
  unfold psiRow3
  exact ContinuousOn.sub
    (ContinuousOn.add
      (ContinuousOn.sub ((continuousOn_invV n).neg.smul continuousOn_const)
        ((continuousOn_invU n).smul continuousOn_const))
      ((continuousOn_inv2pA n).smul continuousOn_const))
    ((continuousOn_inv2pC n).smul continuousOn_const)

/-! ## Continuity of `s ↦ Psi n s` -/

theorem psi_continuous (n : ℕ) {a b : ℝ} (ha : 0 < a) :
    ContinuousOn (fun s : ℝ => Work.OddCurveB.Est.Psi n s) (Set.Icc a b) := by
  have hT : Set.Icc a b ⊆ Set.Ioi (0 : ℝ) := fun s hs => lt_of_lt_of_le ha hs.1
  have hrow2 : ContinuousOn (fun s : ℝ => psiRow2 n s) (Set.Icc a b) :=
    (continuousOn_psiRow2 n).mono hT
  have hrow3 : ContinuousOn (fun s : ℝ => psiRow3 n s) (Set.Icc a b) :=
    (continuousOn_psiRow3 n).mono hT
  -- each summand `(PsiRows n s i).smulRight (Pi.single i 1)` is continuous
  have hterm : ∀ i : Fin 4,
      ContinuousOn (fun s : ℝ => (PsiRows n s i).smulRight (Pi.single i (1 : ℝ) : St))
        (Set.Icc a b) := by
    intro i
    have hrow : ContinuousOn (fun s : ℝ => PsiRows n s i) (Set.Icc a b) := by
      fin_cases i
      · simpa [PsiRows] using
          (continuousOn_const : ContinuousOn (fun _ : ℝ => Proj 0) (Set.Icc a b))
      · simpa [PsiRows] using
          (continuousOn_const : ContinuousOn (fun _ : ℝ => Proj 1) (Set.Icc a b))
      · simpa [PsiRows] using hrow2
      · simpa [PsiRows] using hrow3
    have h1 : ContinuousOn
        (fun s : ℝ => (ContinuousLinearMap.smulRightL ℝ St St) (PsiRows n s i))
        (Set.Icc a b) :=
      ContinuousOn.clm_apply continuousOn_const hrow
    exact h1.clm_apply continuousOn_const
  have hsum : ContinuousOn
      (fun s : ℝ => ∑ i : Fin 4, (PsiRows n s i).smulRight (Pi.single i (1 : ℝ) : St))
      (Set.Icc a b) :=
    continuousOn_finsetSum _ (fun i _ => hterm i)
  exact hsum.congr (fun s _ => by rw [Psi]; exact pi_eq_sum_smulRight (PsiRows n s))

end

end Work.OddCurveB.Est
