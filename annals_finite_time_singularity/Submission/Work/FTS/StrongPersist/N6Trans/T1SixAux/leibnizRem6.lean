import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.StrongPersist.N6Trans.T1SixAux.SlicePrep
import Submission.Work.FTS.StrongPersist.N6Trans.T1SixAux.Basic
import Submission.Work.FTS.EllipticEst.SliceDecompDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.N6Trans.T1SixAux

set_option autoImplicit false

/-! ## The `(0,0)`-deleted double `range`-sum

The Leibniz rule `leibniz_Dth` of `SlicePrep` expands `mixed b a (f · D_θ g)` into a double
`Finset.range`-sum over `i ∈ range (a+1)`, `j ∈ range (b+1)`; the summand at `(i,j) = (0,0)`
is the pure angular transport term `f · D_θ (D_z^b D_θ^a g)`.  The statement `leibnizRem6`
deletes that single summand, so the combinatorial content of its proof is the elementary
identity

`∑_i ∑_j (if (i,j) = (0,0) then 0 else C i j) = (∑_i ∑_j C i j) - C 0 0`. -/

private lemma sum_range_sum_range_ite_zero (a b : ℕ) (C : ℕ → ℕ → ℝ) :
    (∑ i ∈ Finset.range (a + 1), ∑ j ∈ Finset.range (b + 1),
        (if i = 0 ∧ j = 0 then (0 : ℝ) else C i j))
      = (∑ i ∈ Finset.range (a + 1), ∑ j ∈ Finset.range (b + 1), C i j) - C 0 0 := by
  have hzero : (∑ i ∈ Finset.range (a + 1), ∑ j ∈ Finset.range (b + 1),
        (if i = 0 ∧ j = 0 then C i j else 0)) = C 0 0 := by
    have hinner : ∀ i : ℕ, (∑ j ∈ Finset.range (b + 1),
        (if i = 0 ∧ j = 0 then C i j else 0)) = if i = 0 then C 0 0 else 0 := by
      intro i
      by_cases hi : i = 0
      · subst hi
        rw [if_pos rfl]
        rw [show (∑ j ∈ Finset.range (b + 1), (if 0 = 0 ∧ j = 0 then C 0 j else 0))
            = ∑ j ∈ Finset.range (b + 1), (if j = 0 then C 0 j else 0) from by
          refine Finset.sum_congr rfl fun j _ => ?_
          by_cases hj : j = 0 <;> simp [hj]]
        rw [Finset.sum_ite_eq']
        simp
      · rw [if_neg hi]
        refine Finset.sum_eq_zero fun j _ => ?_
        rw [if_neg]
        rintro ⟨h, -⟩
        exact hi h
    calc (∑ i ∈ Finset.range (a + 1), ∑ j ∈ Finset.range (b + 1),
          (if i = 0 ∧ j = 0 then C i j else 0))
        = ∑ i ∈ Finset.range (a + 1), (if i = 0 then C 0 0 else 0) :=
          Finset.sum_congr rfl fun i _ => hinner i
      _ = C 0 0 := by
          rw [Finset.sum_ite_eq']
          simp
  have hpt : ∀ i j : ℕ, (if i = 0 ∧ j = 0 then (0 : ℝ) else C i j)
      = C i j - (if i = 0 ∧ j = 0 then C i j else 0) := by
    intro i j
    by_cases h : i = 0 ∧ j = 0
    · rw [if_pos h, if_pos h]; ring
    · rw [if_neg h, if_neg h]; ring
  calc (∑ i ∈ Finset.range (a + 1), ∑ j ∈ Finset.range (b + 1),
        (if i = 0 ∧ j = 0 then (0 : ℝ) else C i j))
      = ∑ i ∈ Finset.range (a + 1), ∑ j ∈ Finset.range (b + 1),
          (C i j - (if i = 0 ∧ j = 0 then C i j else 0)) :=
        Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => hpt i j
    _ = (∑ i ∈ Finset.range (a + 1), ∑ j ∈ Finset.range (b + 1), C i j)
        - ∑ i ∈ Finset.range (a + 1), ∑ j ∈ Finset.range (b + 1),
            (if i = 0 ∧ j = 0 then C i j else 0) := by
        simp only [Finset.sum_sub_distrib]
    _ = (∑ i ∈ Finset.range (a + 1), ∑ j ∈ Finset.range (b + 1), C i j) - C 0 0 := by
        rw [hzero]

/-- **The Leibniz rule for `mixed b a (f · D_θ g)` with the transport term deleted.**  With
`leibniz_Dth` (`SlicePrep`) in hand this is pure bookkeeping: the deleted `(0,0)`-summand of
that expansion is exactly `f · D_θ (D_z^b D_θ^a g)`, since `D_θ` commutes with `D_z` on the
open quadrant (`DthIter_DzIter_eq_mixed_open`). -/
theorem leibnizRem6 {f g : ℝ → ℝ → ℝ} (hF : Work.FTS.EllipticEst.SmoothOpen f)
    (hG : Work.FTS.EllipticEst.SmoothOpen g) (a b : ℕ) :
    ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 →
      Work.Spaces.mixed b a (fun z θ => f z θ * Work.Spaces.Dth g z θ) z θ
        - f z θ * Work.Spaces.Dth (Work.Spaces.mixed b a g) z θ
      = ∑ i ∈ Finset.range (a + 1), ∑ j ∈ Finset.range (b + 1),
          (if i = 0 ∧ j = 0 then 0
            else (a.choose i : ℝ) * (b.choose j : ℝ)
              * (Work.Spaces.mixed j i f z θ
                  * Work.Spaces.mixed (b - j) (a - i + 1) g z θ)) := by
  intro z θ hz hθ0 hθ1
  -- The transport term `D_θ (D_z^b D_θ^a g)` is the `(0,0)`-summand of the expansion.
  have hshift : Work.Spaces.Dth (Work.Spaces.mixed b a g) z θ
      = Work.Spaces.mixed b (a + 1) g z θ := by
    have hda : ∀ n : ℕ, ContDiffOn ℝ n
        (Function.uncurry (Work.Spaces.DthIter a g))
        (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) :=
      (Work.FTS.EllipticEst.smoothOpen_iff_forall _).mp (hG.DthIter a)
    have h := Work.FTS.EllipticEst.DthIter_DzIter_eq_mixed_open hda b 1 hz ⟨hθ0, hθ1⟩
    simpa [Work.Spaces.mixed] using h
  have hB : f z θ * Work.Spaces.Dth (Work.Spaces.mixed b a g) z θ
      = (a.choose 0 : ℝ) * (b.choose 0 : ℝ)
          * (Work.Spaces.mixed 0 0 f z θ
              * Work.Spaces.mixed (b - 0) (a - 0 + 1) g z θ) := by
    rw [Nat.choose_zero_right, Nat.choose_zero_right, Nat.sub_zero, Nat.sub_zero, hshift]
    simp only [Work.Spaces.mixed_zero_left, Work.Spaces.mixed_zero_right,
      Work.Spaces.DthIter_zero, Work.Spaces.DzIter_zero]
    ring
  rw [leibniz_Dth hF hG b a z θ hz hθ0 hθ1, hB]
  exact (sum_range_sum_range_ite_zero a b
    (fun i j => (a.choose i : ℝ) * (b.choose j : ℝ)
      * (Work.Spaces.mixed j i f z θ
          * Work.Spaces.mixed (b - j) (a - i + 1) g z θ))).symm

end Work.FTS.StrongPersist.N6Trans.T1SixAux
