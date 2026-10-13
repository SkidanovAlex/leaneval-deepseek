import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.L12Rec7
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.QangDiff7
import Submission.Work.FTS.StrongPersist.QangSq6Full
import Submission.Work.FTS.StrongPersist.N6_L12H
import Submission.Work.FTS.StrongPersist.L6Aux.L12SlotSum6
import Submission.Work.FTS.H2.L12HQ
import Submission.Work.Elliptic.L12Aux

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `L12slotLe7` — the level-six weighted `L²`-bound for the `z`-slots of `L₁₂(g)` up to order 7

`L₁₂(g)` is a radial function; the `q`-th summand of the `ℋ⁶`-energy of `(z,θ) ↦ L₁₂(g)(z)` is
the weighted square `(D_z^q L₁₂(g))² w²` of its `q`-th iterate `D_z = z ∂_z`.  This module
proves the *individual slot* bound

  `∫_z (D_z^q L₁₂(g))² w(z)² dz ≤ C · |g|²_{ℋ⁶}`   for every `q ≤ 7`,

with the constant `C = 107·∫_θ K² + 1`.  It is the per-slot refinement of
`Work.FTS.StrongPersist.L6Aux.L12SlotSum6` (which bounds the *sum* over `q ≤ 6`), extended by
one order:

* the `q = 0` slot is the weighted Hardy estimate `∫ (L₁₂ g)² w² ≤ 107 ∫ (Qang g 0)² w²`
  (`Work.FTS.StrongPersist.l12L6_bundle`, which uses `L₁₂(g)(0) = 0`);
* the slots `1 ≤ q ≤ 7` are, a.e. in `z`, the angular moments: the index-raising recursion
  `D_z^q L₁₂(g) = -Qang g (q-1)` (the `k ≤ 6` case of `L12Rec7`, whose `z`-differentiation input
  is `QangDiff7`) together with the level-six weighted `L²`-bound for the angular moments
  `QangSq6Full` (`i ≤ 6`).

The two hypotheses `HkMem α 6 g` and `HkMem α 7 g` feed respectively `QangSq6Full` and
`QangDiff7`.  Everything rests on `[propext, Classical.choice, Quot.sound]`.
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.H6Pair6Aux

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

theorem L12slotLe7 : ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (g : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 →
    Work.FTS.EllipticEst.SmoothOpen g → Work.Spaces.HkMem α 6 g → Work.Spaces.HkMem α 7 g →
    Work.Construction.L12 g 0 = 0 →
    ∀ q : ℕ, q ≤ 7 → MeasureTheory.IntegrableOn
        (fun z => (Work.Elliptic.DzdIter q (fun z => Work.Construction.L12 g z) z) ^ 2
          * (Work.Spaces.w z) ^ 2) Work.Spaces.Iz ∧
      (∫ z in Work.Spaces.Iz,
          (Work.Elliptic.DzdIter q (fun z => Work.Construction.L12 g z) z) ^ 2
            * (Work.Spaces.w z) ^ 2) ≤ C * Work.Spaces.HkSq α 6 g := by
  -- the universal constant `∫_θ K²` is nonnegative
  have hK2nn : 0 ≤ ∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2 :=
    MeasureTheory.integral_nonneg fun θ => sq_nonneg _
  refine ⟨107 * (∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2) + 1,
    by linarith, ?_⟩
  intro α g hα hα1 hO hmem6 hmem7 h0 q hq
  -- the vanishing hypothesis in the elliptic spelling, and the identification of the two `L₁₂`
  have h0e : Work.Elliptic.L12 g 0 = 0 := by
    rw [← Work.FTS.H2.constructionL12_eq_ellipticL12 g]
    exact h0
  have hfun : (fun z : ℝ => Work.Construction.L12 g z)
      = (fun z : ℝ => Work.Elliptic.L12 g z) :=
    Work.FTS.H2.constructionL12_eq_ellipticL12 g
  -- the level-six angular-moment bound (`i ≤ 6`)
  have hQ : ∀ i : ℕ, i ≤ 6 →
      MeasureTheory.IntegrableOn
          (fun z => (Work.Elliptic.Qang g i z) ^ 2 * (Work.Spaces.w z) ^ 2) Work.Spaces.Iz ∧
        (∫ z in Work.Spaces.Iz, (Work.Elliptic.Qang g i z) ^ 2 * (Work.Spaces.w z) ^ 2)
          ≤ (∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2) * Work.Spaces.HkSq α 6 g :=
    Work.FTS.StrongPersist.QangSq6Full (α := α) (g := g) hO hmem6
  -- the `q = 0` slot: the weighted Hardy estimate from the level-six `L₁₂`-bundle
  obtain ⟨-, hInt0, hBnd0⟩ :=
    Work.FTS.StrongPersist.l12L6_bundle (α := α) (g := g) hO hmem6 h0e
      (fun j hj z hz =>
        (Work.FTS.StrongPersist.QangDiff6 (α := α) (g := g) hO hmem6).1 j hj z hz)
      ((hQ 0 (by norm_num)).1)
  -- the index-raising recursion `D_z^{k+1} L₁₂(g) = -Qang g k`, up to `k = 6`
  have hrec : ∀ k : ℕ, k ≤ 6 → ∀ z : ℝ, 0 < z →
      Work.Elliptic.DzdIter (k + 1) (fun z => Work.Elliptic.L12 g z) z
        = - Work.Elliptic.Qang g k z :=
    L12Rec7 hO hmem6
      (fun j hj z hz => QangDiff7 (α := α) (g := g) hO hmem7 j hj z hz)
  -- the slots `q ≥ 1` are, a.e. in `z` on `Iz`, the angular moments
  have htr : ∀ q : ℕ, 1 ≤ q → q ≤ 7 →
      ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
        (Work.Elliptic.Qang g (q - 1) z) ^ 2 * (Work.Spaces.w z) ^ 2
          = (Work.Elliptic.DzdIter q (fun z => Work.Elliptic.L12 g z) z) ^ 2
              * (Work.Spaces.w z) ^ 2 := by
    intro q hq1 hq7
    rw [MeasureTheory.ae_restrict_iff' (s := Work.Spaces.Iz) measurableSet_Ici]
    filter_upwards [MeasureTheory.Measure.ae_ne MeasureTheory.volume (0 : ℝ)]
      with z hz0 hzI
    have hzpos : 0 < z := lt_of_le_of_ne hzI (Ne.symm hz0)
    have key : Work.Elliptic.DzdIter q (fun z => Work.Elliptic.L12 g z) z
        = - Work.Elliptic.Qang g (q - 1) z := by
      have h := hrec (q - 1) (by omega) z hzpos
      rwa [show q - 1 + 1 = q by omega] at h
    rw [key, neg_sq]
  have hHknn : 0 ≤ Work.Spaces.HkSq α 6 g := Work.Spaces.HkSq_nonneg α 6 g
  -- pass to the elliptic spelling of `L₁₂`
  rw [hfun]
  rcases Nat.eq_zero_or_pos q with hq0 | hqpos
  · -- the `q = 0` slot
    subst hq0
    refine ⟨?_, ?_⟩
    · simpa only [Work.Elliptic.DzdIter_zero] using hInt0
    · have hstep : (∫ z in Work.Spaces.Iz,
            (Work.Elliptic.DzdIter 0 (fun z => Work.Elliptic.L12 g z) z) ^ 2
              * (Work.Spaces.w z) ^ 2)
          ≤ 107 * ((∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2)
              * Work.Spaces.HkSq α 6 g) := by
        have h1 := le_trans hBnd0
          (mul_le_mul_of_nonneg_left (hQ 0 (by norm_num)).2 (by norm_num))
        simpa only [Work.Elliptic.DzdIter_zero] using h1
      calc (∫ z in Work.Spaces.Iz,
            (Work.Elliptic.DzdIter 0 (fun z => Work.Elliptic.L12 g z) z) ^ 2
              * (Work.Spaces.w z) ^ 2)
          ≤ 107 * ((∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2)
              * Work.Spaces.HkSq α 6 g) := hstep
        _ ≤ (107 * (∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2) + 1)
              * Work.Spaces.HkSq α 6 g := by
            have hr : (107 * (∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2) + 1)
                * Work.Spaces.HkSq α 6 g
                = 107 * ((∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2)
                    * Work.Spaces.HkSq α 6 g) + Work.Spaces.HkSq α 6 g := by
              ring
            rw [hr]
            linarith
  · -- the slots `1 ≤ q ≤ 7`
    have hq6 : q - 1 ≤ 6 := by omega
    refine ⟨((hQ (q - 1) hq6).1).congr (htr q hqpos hq), ?_⟩
    rw [← MeasureTheory.integral_congr_ae (htr q hqpos hq)]
    calc (∫ z in Work.Spaces.Iz,
          (Work.Elliptic.Qang g (q - 1) z) ^ 2 * (Work.Spaces.w z) ^ 2)
        ≤ (∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2) * Work.Spaces.HkSq α 6 g :=
          (hQ (q - 1) hq6).2
      _ ≤ (107 * (∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2) + 1)
            * Work.Spaces.HkSq α 6 g := by
          have hr : (107 * (∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2) + 1)
              * Work.Spaces.HkSq α 6 g
              = 107 * ((∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2)
                  * Work.Spaces.HkSq α 6 g) + Work.Spaces.HkSq α 6 g := by
            ring
          rw [hr]
          nlinarith [hK2nn, hHknn]

end Work.FTS.StrongPersist.H6Pair6Aux
