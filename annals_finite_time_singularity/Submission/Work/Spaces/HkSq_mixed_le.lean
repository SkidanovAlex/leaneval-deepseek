/-
Copyright: work module for the Elgindi finite-time singularity project.

# `HkSq α 2 (mixed b a g) ≤ HkSq α 4 g` for `a + b ≤ 2`

The operators `D_z = z ∂_z` and `D_θ = sin(2θ) ∂_θ` commute on the domain for a
function smooth on a neighbourhood of the closed quadrant, so for `a + b ≤ 2` every
weighted derivative occurring in the `H²`-norm of `D_z^b D_θ^a g` is a weighted
derivative of `g` of total order at most `4`; the `D_z`-weight
`w/sin(2θ)^{η/2}` is dominated by the mixed weight `W = w/sin(2θ)^{γ/2}`
(`η = 99/100 < γ = 1 + α/10`), and the `H⁴`-norm of `g` collects all of them.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.Spaces.Defs
import Submission.Work.Spaces.mixed_comm
import Submission.Work.Spaces.H_le_Wt

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.Spaces

set_option autoImplicit false

/-- Composition of iterates of `D_z`. -/
private lemma DzIter_add_hk (i b : ℕ) (f : ℝ → ℝ → ℝ) :
    DzIter (i + b) f = DzIter i (DzIter b f) := by
  induction i with
  | zero => simp
  | succ n ih => rw [Nat.succ_add, DzIter_succ, ih, DzIter_succ]

/-- `DzIter` passes through `mixed` on the left. -/
private lemma DzIter_mixed_hk (i b a : ℕ) (f : ℝ → ℝ → ℝ) :
    DzIter i (mixed b a f) = mixed (i + b) a f := by
  simp only [mixed]; rw [DzIter_add_hk]

/-- Pointwise domination of the `H²`-integrand of `mixed b a g` by the `H⁴`-integrand of `g`,
for `a + b ≤ 2`.  Each term of the former is (a square whose base is) a weighted mixed
derivative of `g` of total order `≤ 4`; the index sets match up and the weights are dominated. -/
private lemma HkIntegrand_mixed_le (α : ℝ) (hα : 0 < α) (g : ℝ → ℝ → ℝ)
    (hsm : SmoothNbhd g) (b a : ℕ) (hab : a + b ≤ 2) (z θ : ℝ) (hz : z ∈ Iz)
    (hθ : θ ∈ Iθ) :
    HkIntegrand α 2 (mixed b a g) z θ ≤ HkIntegrand α 4 g z θ := by
  have hb2 : b ≤ 2 := by omega
  have ha2 : a ≤ 2 := by omega
  set H : ℝ := w z / (Real.sin (2 * θ)) ^ (eta / 2) with hH
  set W : ℝ := Wt α z θ with hW
  -- Index convention: a pair `x = (p, q)` records `p = D_θ`-order and `q = D_z`-order.
  set T : ℕ × ℕ → ℝ := fun x =>
    if x.1 = 0 then (DzIter x.2 g z θ * H) ^ 2 else (mixed x.2 x.1 g z θ * W) ^ 2 with hT
  set S1 : Finset (ℕ × ℕ) := (Finset.range 3).image (fun i => (a, i + b)) with hS1def
  set S2 : Finset (ℕ × ℕ) := ((Finset.range 3 ×ˢ Finset.range 3).filter
      (fun x : ℕ × ℕ => 1 ≤ x.1 ∧ x.1 + x.2 ≤ 2)).image (fun x => (x.1 + a, x.2 + b))
    with hS2def
  set R1 : Finset (ℕ × ℕ) := (Finset.range 5).image (fun q => ((0 : ℕ), q)) with hR1def
  set R2 : Finset (ℕ × ℕ) := (Finset.range 5 ×ˢ Finset.range 5).filter
      (fun x : ℕ × ℕ => 1 ≤ x.1 ∧ x.1 + x.2 ≤ 4) with hR2def
  have hTnn : ∀ x, 0 ≤ T x := by
    rintro ⟨x1, x2⟩; simp only [hT]; split <;> exact sq_nonneg _
  -- The first sum of `HkIntegrand α 4 g` sits on the index set `R1`.
  have hR1 : (∑ x ∈ R1, T x) = ∑ i ∈ Finset.range 5, (DzIter i g z θ * H) ^ 2 := by
    rw [hR1def]
    have hinj : Set.InjOn (fun q : ℕ => ((0 : ℕ), q)) (↑(Finset.range 5) : Set ℕ) := by
      intro x _ y _ h; simpa using h
    rw [Finset.sum_image (f := T) hinj]
    refine Finset.sum_congr rfl (fun q _ => ?_)
    simp only [hT]; simp
  -- The second sum of `HkIntegrand α 4 g` sits on the index set `R2`.
  have hR2 : (∑ x ∈ R2, T x)
      = ∑ p ∈ Finset.range 5, ∑ q ∈ Finset.range 5,
          (if 1 ≤ p ∧ p + q ≤ 4 then (mixed q p g z θ * W) ^ 2 else 0) := by
    rw [hR2def, Finset.sum_filter, Finset.sum_product]
    refine Finset.sum_congr rfl (fun p _ => Finset.sum_congr rfl (fun q _ => ?_))
    simp only [hT]
    by_cases hc : 1 ≤ p ∧ p + q ≤ 4
    · rw [if_pos hc, if_pos hc, if_neg (by omega : ¬ p = 0)]
    · rw [if_neg hc, if_neg hc]
  -- The first sum of `HkIntegrand α 2 (mixed b a g)` is dominated on `S1`.
  have hS1 : (∑ i ∈ Finset.range 3, (DzIter i (mixed b a g) z θ * H) ^ 2) ≤ ∑ x ∈ S1, T x := by
    rw [hS1def]
    have hinj : Set.InjOn (fun i : ℕ => (a, i + b)) (↑(Finset.range 3) : Set ℕ) := by
      intro x _ y _ h; simpa using h
    rw [Finset.sum_image (f := T) hinj]
    refine Finset.sum_le_sum (fun i _ => ?_)
    rw [DzIter_mixed_hk i b a g]
    simp only [hT]
    by_cases ha : a = 0
    · subst ha; rw [if_pos rfl]; simp [mixed]
    · rw [if_neg ha]
      have hHW : H ^ 2 ≤ W ^ 2 := by rw [hH, hW]; exact H_le_Wt α hα z θ hz hθ
      nlinarith [hHW, sq_nonneg (mixed (i + b) a g z θ)]
  -- The second sum of `HkIntegrand α 2 (mixed b a g)` equals the sum on `S2`.
  have hS2a : (∑ i ∈ Finset.range 3, ∑ j ∈ Finset.range 3,
        (if 1 ≤ i ∧ i + j ≤ 2 then (mixed j i (mixed b a g) z θ * W) ^ 2 else 0))
      = ∑ x ∈ (Finset.range 3 ×ˢ Finset.range 3).filter
            (fun x : ℕ × ℕ => 1 ≤ x.1 ∧ x.1 + x.2 ≤ 2),
          T (x.1 + a, x.2 + b) := by
    rw [Finset.sum_filter, Finset.sum_product]
    refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
    dsimp only
    by_cases hc : 1 ≤ i ∧ i + j ≤ 2
    · rw [if_pos hc, if_pos hc]
      simp only [hT]
      rw [if_neg (by omega : ¬ i + a = 0)]
      rw [mixed_comm g hsm j i b a z θ hz hθ]
    · rw [if_neg hc, if_neg hc]
  have hS2b : (∑ x ∈ (Finset.range 3 ×ˢ Finset.range 3).filter
          (fun x : ℕ × ℕ => 1 ≤ x.1 ∧ x.1 + x.2 ≤ 2), T (x.1 + a, x.2 + b))
      = ∑ x ∈ S2, T x := by
    rw [hS2def]
    have hinj : Set.InjOn (fun x : ℕ × ℕ => (x.1 + a, x.2 + b))
        (↑((Finset.range 3 ×ˢ Finset.range 3).filter
          (fun x : ℕ × ℕ => 1 ≤ x.1 ∧ x.1 + x.2 ≤ 2)) : Set (ℕ × ℕ)) := by
      intro x _ y _ h
      simp only [Prod.mk.injEq] at h
      exact Prod.ext (Nat.add_right_cancel h.1) (Nat.add_right_cancel h.2)
    rw [Finset.sum_image (f := T) hinj]
  have hS2 : (∑ i ∈ Finset.range 3, ∑ j ∈ Finset.range 3,
        (if 1 ≤ i ∧ i + j ≤ 2 then (mixed j i (mixed b a g) z θ * W) ^ 2 else 0))
      = ∑ x ∈ S2, T x := hS2a.trans hS2b
  -- `S1` and `S2` are disjoint, and so are `R1` and `R2`.
  have hdisjS : Disjoint S1 S2 := by
    rw [Finset.disjoint_left]
    intro x hx1 hx2
    rw [hS1def, Finset.mem_image] at hx1
    obtain ⟨i, _, rfl⟩ := hx1
    rw [hS2def, Finset.mem_image] at hx2
    obtain ⟨y, hy, hxy⟩ := hx2
    rw [Finset.mem_filter] at hy
    simp only [Prod.mk.injEq] at hxy
    have hy1 : 1 ≤ y.1 := hy.2.1
    omega
  have hdisjR : Disjoint R1 R2 := by
    rw [Finset.disjoint_left]
    intro x hx1 hx2
    rw [hR1def, Finset.mem_image] at hx1
    obtain ⟨q, _, rfl⟩ := hx1
    rw [hR2def, Finset.mem_filter] at hx2
    have h := hx2.2.1
    simp only [] at h
    omega
  -- Every index of `S1 ∪ S2` is an index of `R1 ∪ R2`.
  have hsub : S1 ∪ S2 ⊆ R1 ∪ R2 := by
    intro x hx
    rw [Finset.mem_union] at hx ⊢
    rcases hx with hx | hx
    · rw [hS1def, Finset.mem_image] at hx
      obtain ⟨i, hi, rfl⟩ := hx
      rw [Finset.mem_range] at hi
      by_cases ha : a = 0
      · left
        rw [hR1def, Finset.mem_image]
        exact ⟨i + b, by rw [Finset.mem_range]; omega, by simp [ha]⟩
      · right
        rw [hR2def, Finset.mem_filter, Finset.mem_product, Finset.mem_range, Finset.mem_range]
        dsimp only
        refine ⟨⟨by omega, by omega⟩, by omega, by omega⟩
    · rw [hS2def, Finset.mem_image] at hx
      obtain ⟨y, hy, rfl⟩ := hx
      rw [Finset.mem_filter, Finset.mem_product, Finset.mem_range, Finset.mem_range] at hy
      right
      rw [hR2def, Finset.mem_filter, Finset.mem_product, Finset.mem_range, Finset.mem_range]
      dsimp only
      refine ⟨⟨by omega, by omega⟩, by omega, by omega⟩
  have hLHSunfold : HkIntegrand α 2 (mixed b a g) z θ
      = (∑ i ∈ Finset.range 3, (DzIter i (mixed b a g) z θ * H) ^ 2)
        + ∑ i ∈ Finset.range 3, ∑ j ∈ Finset.range 3,
            (if 1 ≤ i ∧ i + j ≤ 2 then (mixed j i (mixed b a g) z θ * W) ^ 2 else 0) := by
    simp [HkIntegrand, ← hH, ← hW]
  have hRHSunfold : HkIntegrand α 4 g z θ
      = (∑ i ∈ Finset.range 5, (DzIter i g z θ * H) ^ 2)
        + ∑ i ∈ Finset.range 5, ∑ j ∈ Finset.range 5,
            (if 1 ≤ i ∧ i + j ≤ 4 then (mixed j i g z θ * W) ^ 2 else 0) := by
    simp [HkIntegrand, ← hH, ← hW]
  have hstep1 : (∑ i ∈ Finset.range 3, (DzIter i (mixed b a g) z θ * H) ^ 2)
        + (∑ i ∈ Finset.range 3, ∑ j ∈ Finset.range 3,
            (if 1 ≤ i ∧ i + j ≤ 2 then (mixed j i (mixed b a g) z θ * W) ^ 2 else 0))
      ≤ ∑ x ∈ S1 ∪ S2, T x := by
    rw [hS2, Finset.sum_union hdisjS]
    linarith [hS1]
  have hstep2 : (∑ x ∈ S1 ∪ S2, T x)
      ≤ (∑ i ∈ Finset.range 5, (DzIter i g z θ * H) ^ 2)
        + ∑ i ∈ Finset.range 5, ∑ j ∈ Finset.range 5,
            (if 1 ≤ i ∧ i + j ≤ 4 then (mixed j i g z θ * W) ^ 2 else 0) := by
    rw [← hR1, ← hR2, ← Finset.sum_union hdisjR]
    exact Finset.sum_le_sum_of_subset_of_nonneg hsub (fun x _ _ => hTnn x)
  rw [hLHSunfold, hRHSunfold]
  exact le_trans hstep1 hstep2

theorem HkSq_mixed_le (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (g : ℝ → ℝ → ℝ)
    (hsm : Work.Spaces.SmoothNbhd g) (hmem : Work.Spaces.HkMem α 4 g)
    (b a : ℕ) (hab : a + b ≤ 2) :
    Work.Spaces.HkSq α 2 (Work.Spaces.mixed b a g) ≤ Work.Spaces.HkSq α 4 g := by
  simp only [HkSq]
  apply setIntegral_mono_of_nonneg
  · intro z _
    exact integral_nonneg fun θ => HkIntegrand_nonneg α 2 (mixed b a g) z θ
  · intro z hz
    apply setIntegral_mono_of_nonneg
    · intro θ _
      exact HkIntegrand_nonneg α 2 (mixed b a g) z θ
    · intro θ hθ
      exact HkIntegrand_mixed_le α hα g hsm b a hab z θ hz hθ
    · exact hmem.1 z hz
  · exact hmem.2

end Work.Spaces
