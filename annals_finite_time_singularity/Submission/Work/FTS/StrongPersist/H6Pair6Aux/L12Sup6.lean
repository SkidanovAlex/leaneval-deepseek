import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.StrongPersist.L3Rhs.L12fJetUniform
import Submission.Work.FTS.StrongPersist.N6_L12H
import Submission.Work.FTS.StrongPersist.L6Aux.L12SlotSum6
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.L12Rec7
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.QangDiff7
import Submission.Work.FTS.StrongPersist.QangDiff6
import Submission.Work.FTS.StrongPersist.QangSq6Full
import Submission.Work.FTS.OpenPkg.QangOpen
import Submission.Work.FTS.OpenPkg.ProdOpen.Tools1d
import Submission.Work.FTS.StrongPersist.L3Rhs.window_le_slot
import Submission.Work.FTS.H2.L12HQ
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.L12slotLe7

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `L12Sup6` — uniform-in-`z` bounds on the `D_z`-jets of `L₁₂(g)`, order `≤ 6`

`L₁₂(g)(z) = ∫_z^∞ ∫_θ K(θ) g(r,θ)/r dθ dr` is a function of `z` alone.  This module proves
the pointwise (in `z > 0`) bound

  `|D_z^b L₁₂(g)(z)| ≤ C · |g|_{ℋ⁶}`   for all `b ≤ 6`,

with a universal constant `C > 0`, for every datum of the open-quadrant class
`SmoothOpen g ∧ HkMem α 6 g ∧ HkMem α 7 g` (`α ∈ (0,1]`) with vanishing zero mode
`L₁₂(g)(0) = 0`.

## Route

`D_z^q L₁₂(g)` is the `q`-th slot of the weighted space `ℋ⁶`; the slot bound
(`Work.FTS.StrongPersist.H6Pair6Aux.L12slotLe7`)

  `∫_z (D_z^q L₁₂(g) · w(z))² dz ≤ C₁ · |g|²_{ℋ⁶}`   (`q ≤ 7`)

is the analytic input.  Given it, the pointwise bound is the one-dimensional Agmon/Sobolev
inequality `Work.FTS.OpenPkg.ProdOpen.sob_z_mean` applied to `h = Zop^b (L₁₂ g)` (where
`Zop u = z ∂_z u = Dzd u`):

  `h(z)² ≤ Cz · (∫_1^2 h² + ∫_z (x h'(x) w(x))²)`,

in which the second integral is `∫ (Zop^{b+1} (L₁₂ g) · w)²` — the slot of order `b + 1 ≤ 7` —
and the first is dominated by the slot of order `b` because `w ≥ 1` on `[1,2]`
(`Work.FTS.StrongPersist.L3Rhs.window_le_slot`).  Taking square roots gives the claim; this is
the level-six analogue of `Work.FTS.StrongPersist.L3Rhs.L12fJetUniform` (which is the same
statement at level four, `b ≤ 3`).
-/

namespace Work.FTS.StrongPersist.H6Pair6Aux

open MeasureTheory Set Filter
open scoped Real Topology

set_option autoImplicit false

/-- `Zop^[b] u = DzdIter b u`: both are the `b`-fold iterate of `u ↦ z ∂_z u`. -/
lemma Zop_iter_eq_DzdIter (b : ℕ) (u : ℝ → ℝ) :
    Work.Spaces.Zop^[b] u = Work.Elliptic.DzdIter b u := by
  induction b with
  | zero => rfl
  | succ n ih =>
      funext z
      rw [Function.iterate_succ_apply', ih]
      rfl

theorem L12Sup6 : ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (g : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 →
    Work.FTS.EllipticEst.SmoothOpen g → Work.Spaces.HkMem α 6 g → Work.Spaces.HkMem α 7 g →
    Work.Construction.L12 g 0 = 0 →
    ∀ b : ℕ, b ≤ 6 → ∀ z : ℝ, 0 < z →
      |Work.Elliptic.DzdIter b (fun z => Work.Construction.L12 g z) z|
        ≤ C * Work.Spaces.HkNorm α 6 g := by
  obtain ⟨C₁, hC₁pos, hslotC⟩ := L12slotLe7
  obtain ⟨Cz, hCzpos, hCz⟩ := Work.FTS.OpenPkg.ProdOpen.sob_z_mean
  refine ⟨Real.sqrt (2 * Cz * C₁) + 1, ?_, ?_⟩
  · have h : 0 ≤ 2 * Cz * C₁ := by positivity
    linarith [Real.sqrt_nonneg (2 * Cz * C₁)]
  · intro α g hα hα1 hO hmem6 hmem7 h0 b hb z hz
    set φ : ℝ → ℝ := fun z => Work.Construction.L12 g z with hφ
    -- `L₁₂(g)` is `C⁷` on `(0,∞)`
    have hCd : ContDiffOn ℝ 7 φ (Set.Ioi 0) := by
      have h := Work.FTS.EllipticEst.UopHk.contDiffOn_L12_k α 7 g hα hα1 hO hmem7
        (by norm_num)
      rw [hφ]
      exact h.congr (fun x _ =>
        (congrFun (Work.FTS.H2.constructionL12_eq_ellipticL12 g) x).symm)
    -- the slot bounds, in the `Zop` spelling
    have hslotZ : ∀ q : ℕ, q ≤ 7 →
        MeasureTheory.IntegrableOn
            (fun x => (Work.Spaces.Zop^[q] φ x * Work.Spaces.w x) ^ 2) Work.Spaces.Iz ∧
          (∫ x in Work.Spaces.Iz, (Work.Spaces.Zop^[q] φ x * Work.Spaces.w x) ^ 2)
            ≤ C₁ * Work.Spaces.HkSq α 6 g := by
      intro q hq
      obtain ⟨hi, hb⟩ := hslotC α g hα hα1 hO hmem6 hmem7 h0 q hq
      have heq : (fun x => (Work.Spaces.Zop^[q] φ x * Work.Spaces.w x) ^ 2)
          = (fun x => (Work.Elliptic.DzdIter q (fun y => Work.Construction.L12 g y) x) ^ 2
              * (Work.Spaces.w x) ^ 2) := by
        funext x
        rw [Zop_iter_eq_DzdIter q φ, hφ]
        ring
      rw [heq]
      exact ⟨hi, hb⟩
    -- smoothness of the iterate and of its derivative
    have hCd1 : ContDiffOn ℝ (b + 1) φ (Set.Ioi 0) :=
      hCd.of_le (by exact_mod_cast (by omega : b + 1 ≤ 7))
    have hCd_b : ContDiffOn ℝ (7 - b) (Work.Spaces.Zop^[b] φ) (Set.Ioi 0) :=
      Work.FTS.CoercivityFix.Transfer.E1Parts.contDiffOn_Zop_iter' b (7 - b)
        (by
          have h : b + (7 - b) = 7 := by omega
          rw [← Nat.cast_add, h]
          exact hCd)
    have hder : ∀ x : ℝ, 0 < x →
        HasDerivAt (Work.Spaces.Zop^[b] φ) (deriv (Work.Spaces.Zop^[b] φ) x) x :=
      fun x hx =>
        (Work.FTS.CoercivityFix.Transfer.E1Parts.differentiableAt_Zop_iter_of_contDiffOn
          (u := φ) (b := b) hCd1 hx).hasDerivAt
    have hcont : ContinuousOn (deriv (Work.Spaces.Zop^[b] φ)) (Set.Ioi 0) := by
      have h1 : ((1 : ℕ) : WithTop ℕ∞) ≤ ((7 - b : ℕ) : WithTop ℕ∞) := by
        exact_mod_cast (by omega : 1 ≤ 7 - b)
      exact hCd_b.continuousOn_deriv_of_isOpen isOpen_Ioi h1
    have heq2 : (fun x => (x * deriv (Work.Spaces.Zop^[b] φ) x * Work.Spaces.w x) ^ 2)
        = (fun x => (Work.Spaces.Zop^[b+1] φ x * Work.Spaces.w x) ^ 2) := by
      funext x
      rw [show x * deriv (Work.Spaces.Zop^[b] φ) x = Work.Spaces.Zop^[b+1] φ x from by
        rw [Function.iterate_succ_apply']; rfl]
    have hint : MeasureTheory.IntegrableOn
        (fun x => (x * deriv (Work.Spaces.Zop^[b] φ) x * Work.Spaces.w x) ^ 2)
        Work.Spaces.Iz := by
      rw [heq2]
      exact (hslotZ (b + 1) (by omega)).1
    -- the one-dimensional Sobolev/Agmon inequality
    have hsob := hCz (Work.Spaces.Zop^[b] φ) (deriv (Work.Spaces.Zop^[b] φ))
      z hz hder hcont hint
    rw [heq2] at hsob
    have hwin : (∫ x in (1 : ℝ)..2, (Work.Spaces.Zop^[b] φ x) ^ 2)
        ≤ C₁ * Work.Spaces.HkSq α 6 g :=
      le_trans (Work.FTS.StrongPersist.L3Rhs.window_le_slot (hslotZ b (by omega)).1)
        (hslotZ b (by omega)).2
    have hsq : (Work.Spaces.Zop^[b] φ z) ^ 2 ≤ 2 * Cz * C₁ * Work.Spaces.HkSq α 6 g := by
      have h2 := (hslotZ (b + 1) (by omega)).2
      have hw' : Cz * (∫ x in (1 : ℝ)..2, (Work.Spaces.Zop^[b] φ x) ^ 2)
          ≤ Cz * (C₁ * Work.Spaces.HkSq α 6 g) :=
        mul_le_mul_of_nonneg_left hwin hCzpos.le
      have hs' : Cz * (∫ x in Work.Spaces.Iz,
            (Work.Spaces.Zop^[b+1] φ x * Work.Spaces.w x) ^ 2)
          ≤ Cz * (C₁ * Work.Spaces.HkSq α 6 g) :=
        mul_le_mul_of_nonneg_left h2 hCzpos.le
      nlinarith [hsob, hw', hs']
    have hsqrt : |Work.Spaces.Zop^[b] φ z|
        ≤ Real.sqrt (2 * Cz * C₁) * Work.Spaces.HkNorm α 6 g := by
      have hCn : 0 ≤ 2 * Cz * C₁ := by positivity
      calc |Work.Spaces.Zop^[b] φ z|
          = Real.sqrt ((Work.Spaces.Zop^[b] φ z) ^ 2) := (Real.sqrt_sq_eq_abs _).symm
        _ ≤ Real.sqrt (2 * Cz * C₁ * Work.Spaces.HkSq α 6 g) := Real.sqrt_le_sqrt hsq
        _ = Real.sqrt (2 * Cz * C₁) * Real.sqrt (Work.Spaces.HkSq α 6 g) :=
            Real.sqrt_mul hCn _
        _ = Real.sqrt (2 * Cz * C₁) * Work.Spaces.HkNorm α 6 g := rfl
    calc |Work.Elliptic.DzdIter b (fun z => Work.Construction.L12 g z) z|
        = |Work.Spaces.Zop^[b] φ z| := by
          rw [← hφ, ← Zop_iter_eq_DzdIter b φ]
      _ ≤ Real.sqrt (2 * Cz * C₁) * Work.Spaces.HkNorm α 6 g := hsqrt
      _ ≤ (Real.sqrt (2 * Cz * C₁) + 1) * Work.Spaces.HkNorm α 6 g :=
          mul_le_mul_of_nonneg_right
            (by linarith [Real.sqrt_nonneg (2 * Cz * C₁)])
            (Real.sqrt_nonneg (Work.Spaces.HkSq α 6 g))

end Work.FTS.StrongPersist.H6Pair6Aux
