import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.StrongPersist.N6_L12H
import Submission.Work.FTS.StrongPersist.QangSq6
import Submission.Work.FTS.StrongPersist.QangDiff6
import Submission.Work.FTS.H2.L12k0Q

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.L6Aux

/-- **The `H^6`-bound for the `z`-slots of `L₁₂(g)`.**

`L₁₂(g)` is a function of `z` alone; the `q`-th summand is the weighted square of its `q`-th
`D_z`-iterate, `D_z^q = (z ∂_z)^q`.  The `q = 0` slot is controlled by the weighted Hardy
inequality (`l12L6_bundle`), and the slots `1 ≤ q ≤ 6` by the index-raising recursion
`D_z^q L₁₂(g) = -Qang g (q-1)` together with the level-six angular-moment bound `QangSq6`.
The constant is `113 · ∫_θ K² + 1`, with `K(θ) = 3 sinθ cos²θ`. -/
theorem L12SlotSum6 : ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ), 0 < α → α ≤ 1 → ∀ g : ℝ → ℝ → ℝ,
    Work.FTS.EllipticEst.SmoothOpen g → Work.Spaces.HkMem α 6 g →
      Work.Construction.L12 g 0 = 0 →
      MeasureTheory.IntegrableOn
          (fun z => ∑ q ∈ Finset.range 7,
            (Work.Spaces.DzIter q (fun z _ => Work.Construction.L12 g z) z 0) ^ 2
              * (Work.Spaces.w z) ^ 2) Work.Spaces.Iz ∧
        (∫ z in Work.Spaces.Iz, ∑ q ∈ Finset.range 7,
            (Work.Spaces.DzIter q (fun z _ => Work.Construction.L12 g z) z 0) ^ 2
              * (Work.Spaces.w z) ^ 2) ≤ C * Work.Spaces.HkSq α 6 g := by
  refine ⟨113 * (∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2) + 1, ?_, ?_⟩
  · have h : 0 ≤ ∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2 :=
      MeasureTheory.integral_nonneg fun θ => sq_nonneg _
    linarith
  intro α hα hα1 g hO hmem h0
  -- the elliptic spelling of the vanishing hypothesis
  have h0e : Work.Elliptic.L12 g 0 = 0 := by
    rw [← Work.FTS.H2.constructionL12_eq_ellipticL12 g]
    exact h0
  -- the level-six `L₁₂`-bundle: the recursion `D_z^{k+1} L₁₂(g) = -Qang g k` (`k ≤ 5`),
  -- the weighted Hardy slot `k = 0`, and the level-six angular-moment bound
  obtain ⟨hgen, hInt0, hBnd0⟩ :=
    Work.FTS.StrongPersist.l12L6_bundle (α := α) (g := g) hO hmem h0e
      (fun j hj z hz =>
        (Work.FTS.StrongPersist.QangDiff6 (α := α) (g := g) hO hmem).1 j hj z hz)
      ((Work.FTS.StrongPersist.QangSq6 (α := α) (g := g) hO hmem) 0 (by norm_num)).1
  have hQsq := Work.FTS.StrongPersist.QangSq6 (α := α) (g := g) hO hmem
  -- the abstract slot sum, for an arbitrary radial `u` satisfying the three facts
  have main : ∀ (u : ℝ → ℝ),
      (∀ k : ℕ, k ≤ 5 → ∀ z : ℝ, 0 < z →
        Work.Elliptic.DzdIter (k + 1) u z = - Work.Elliptic.Qang g k z) →
      MeasureTheory.IntegrableOn (fun z => (u z) ^ 2 * (Work.Spaces.w z) ^ 2)
        Work.Spaces.Iz →
      (∫ z in Work.Spaces.Iz, (u z) ^ 2 * (Work.Spaces.w z) ^ 2)
        ≤ 107 * (∫ z in Work.Spaces.Iz,
            (Work.Elliptic.Qang g 0 z) ^ 2 * (Work.Spaces.w z) ^ 2) →
      MeasureTheory.IntegrableOn
            (fun z => ∑ q ∈ Finset.range 7,
              (Work.Elliptic.DzdIter q u z) ^ 2 * (Work.Spaces.w z) ^ 2)
            Work.Spaces.Iz ∧
        (∫ z in Work.Spaces.Iz, ∑ q ∈ Finset.range 7,
              (Work.Elliptic.DzdIter q u z) ^ 2 * (Work.Spaces.w z) ^ 2)
          ≤ 113 * ((∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2)
              * Work.Spaces.HkSq α 6 g) := by
    intro u hu hIntu hBndu
    -- the recursion identifies the slots `1 ≤ i ≤ 6` with the angular moments, a.e.
    have htr : ∀ i : ℕ, 1 ≤ i → i ≤ 6 →
        ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
          (Work.Elliptic.Qang g (i - 1) z) ^ 2 * (Work.Spaces.w z) ^ 2
            = (Work.Elliptic.DzdIter i u z) ^ 2 * (Work.Spaces.w z) ^ 2 := by
      intro i hi hi6
      rw [MeasureTheory.ae_restrict_iff' (s := Work.Spaces.Iz) measurableSet_Ici]
      filter_upwards [MeasureTheory.Measure.ae_ne MeasureTheory.volume (0 : ℝ)]
        with z hz0 hzI
      have hzpos : 0 < z := lt_of_le_of_ne hzI (Ne.symm hz0)
      have key : Work.Elliptic.DzdIter i u z = - Work.Elliptic.Qang g (i - 1) z := by
        have h := hu (i - 1) (by omega) z hzpos
        rwa [show i - 1 + 1 = i by omega] at h
      rw [key, neg_sq]
    -- integrability of every slot
    have hslot : ∀ i : ℕ, i ≤ 6 → MeasureTheory.IntegrableOn
        (fun z => (Work.Elliptic.DzdIter i u z) ^ 2 * (Work.Spaces.w z) ^ 2)
        Work.Spaces.Iz := by
      intro i hi6
      rcases Nat.eq_zero_or_pos i with h | h
      · subst h
        simpa only [Work.Elliptic.DzdIter_zero] using hIntu
      · exact ((hQsq (i - 1) (by omega)).1).congr (htr i h hi6)
    have hsum_int : ∀ i ∈ Finset.range 7, MeasureTheory.IntegrableOn
        (fun z => (Work.Elliptic.DzdIter i u z) ^ 2 * (Work.Spaces.w z) ^ 2)
        Work.Spaces.Iz :=
      fun i hi => hslot i (Nat.le_of_lt_succ (Finset.mem_range.mp hi))
    -- the bounds of the individual slots
    have hBnd0' : (∫ z in Work.Spaces.Iz,
          (Work.Elliptic.DzdIter 0 u z) ^ 2 * (Work.Spaces.w z) ^ 2)
        ≤ 107 * ((∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2)
            * Work.Spaces.HkSq α 6 g) := by
      have hb : (∫ z in Work.Spaces.Iz,
            (Work.Elliptic.DzdIter 0 u z) ^ 2 * (Work.Spaces.w z) ^ 2)
          ≤ 107 * (∫ z in Work.Spaces.Iz,
              (Work.Elliptic.Qang g 0 z) ^ 2 * (Work.Spaces.w z) ^ 2) := by
        simpa only [Work.Elliptic.DzdIter_zero] using hBndu
      exact le_trans hb (mul_le_mul_of_nonneg_left (hQsq 0 (by norm_num)).2 (by norm_num))
    have hBndI : ∀ i : ℕ, 1 ≤ i → i ≤ 6 →
        (∫ z in Work.Spaces.Iz, (Work.Elliptic.DzdIter i u z) ^ 2 * (Work.Spaces.w z) ^ 2)
          ≤ (∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2) * Work.Spaces.HkSq α 6 g := by
      intro i hi hi6
      rw [← MeasureTheory.integral_congr_ae (htr i hi hi6)]
      exact (hQsq (i - 1) (by omega)).2
    -- the sum of the slots
    have hsum_le : (∫ z in Work.Spaces.Iz, ∑ i ∈ Finset.range 7,
          (Work.Elliptic.DzdIter i u z) ^ 2 * (Work.Spaces.w z) ^ 2)
        ≤ 113 * ((∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2)
            * Work.Spaces.HkSq α 6 g) := by
      rw [MeasureTheory.integral_finsetSum (Finset.range 7) hsum_int, Finset.sum_range_succ']
      have h6 : (∑ i ∈ Finset.range 6, (∫ z in Work.Spaces.Iz,
            (Work.Elliptic.DzdIter (i + 1) u z) ^ 2 * (Work.Spaces.w z) ^ 2))
          ≤ ∑ _i ∈ Finset.range 6,
              ((∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2)
                * Work.Spaces.HkSq α 6 g) :=
        Finset.sum_le_sum fun i hi => by
          rw [Finset.mem_range] at hi
          exact hBndI (i + 1) (by omega) (by omega)
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at h6
      refine le_trans (add_le_add h6 hBnd0') (le_of_eq ?_)
      ring
    exact ⟨MeasureTheory.integrable_finsetSum (Finset.range 7) hsum_int, hsum_le⟩
  -- rewrite the goal into the elliptic spelling
  have hfun : (fun z (_ : ℝ) => Work.Construction.L12 g z)
      = (fun z (_ : ℝ) => Work.Elliptic.L12 g z) := by
    funext z θ
    exact congrFun (Work.FTS.H2.constructionL12_eq_ellipticL12 g) z
  rw [hfun]
  -- replace the `Spaces`-iterates by the one-dimensional `DzdIter`
  have hsumfun : (fun z => ∑ q ∈ Finset.range 7,
        (Work.Spaces.DzIter q (fun z _ => Work.Elliptic.L12 g z) z 0) ^ 2
          * (Work.Spaces.w z) ^ 2)
      = (fun z => ∑ q ∈ Finset.range 7,
        (Work.Elliptic.DzdIter q (fun z => Work.Elliptic.L12 g z) z) ^ 2
          * (Work.Spaces.w z) ^ 2) := by
    funext z
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [Work.Elliptic.DzIter_rad]
  rw [hsumfun]
  obtain ⟨hI, hB⟩ :=
    main (fun z => Work.Elliptic.L12 g z) (fun k hk z hz => hgen k hk z hz) hInt0 hBnd0
  refine ⟨hI, ?_⟩
  refine le_trans hB ?_
  have hnn : 0 ≤ Work.Spaces.HkSq α 6 g := Work.Spaces.HkSq_nonneg α 6 g
  nlinarith [hnn]

end Work.FTS.StrongPersist.L6Aux
