import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.EllipticEst.TT.psiDerivSq_lower
import Submission.Work.FTS.StrongEps.blocks.L12_Fstar_add_open
import Submission.Work.FTS.StrongPersist.N6TP.summandBound
import Submission.Work.FTS.StrongPersist.N6Trans.SixAux.MainBound
import Submission.Work.FTS.StrongPersist.N6Trans.SixRoute.sixExpansion
import Submission.Work.FTS.StrongPersist.N6Trans.slotT2Six
import Submission.Work.FTS.StrongPersist.N6_prod
import Submission.Work.FTS.TransportS.ip4SlotDomFixed
import Submission.Work.FTS_StreamBdry.Inputs.theta_part_theta
import Submission.Work.H2.T1Q.SliceIntQ
import Submission.Work.H2.WPQ.m_term_le_smoothQuad
import Submission.Work.H2W.PsiSlices.weakPos2_dilate
import Submission.Work.H6Pair6Aux.T6Fix.mixed_sinGain_of_pthFlat
import Submission.Work.PhiStar.Honesty.sqrt_weight_mul_eq_of_mem_Ioo
import Submission.Work.Spaces.HProductRule_Badsummand
import Submission.Work.Spaces.SmoothStripDefs
import Submission.Work.Spaces.mixed_mul_le
-- ===== merged: Submission.Work.FTS.EllipticEst.AeI1Fts.I1WMOuter =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-! Split out of `AeI1Fts/I1PaperWeakMixed.lean`: the `z`-integrated outer bounds and the
leaf theorem `I1PaperWeakMixed`.  Names and namespace are unchanged. -/

namespace Work.FTS.EllipticEst.AeI1Fts

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false
set_option maxHeartbeats 1000000

local notation "Iθo" => Set.Ioo (0 : ℝ) (Real.pi / 2)




end

end Work.FTS.EllipticEst.AeI1Fts
end
-- ===== merged: Submission.Work.FTS.StrongPersist.N6TransPriced =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS.StrongPersist.N6TransPriced`

The level-six transport clauses `T1/T2/T3` for the concrete coercive pairing `IP6 1 … 1`.

`IP6 1 … 1 = IPn α 5` (the five-fold iterate above `H1IP`), and the proved unfolding bound
`TransportS.ip4_unfold_bound` dominates `IPn α 5 u v` by `3^5 · 10^22 · SlotSum α 6 u v`, the
sum of the absolute values of the leaf slot pairings over the `28` slots `a + b ≤ 6` with the
three leaf weights `leafEta`, `leafOne`, `leafGam α` (`a ≥ 1`).  Hence each clause follows from
the corresponding *per-slot* estimate at level six:

* `slotT1Six` (`D_θ`-transport with an `ℋ⁶`-coefficient) — proved elsewhere in the tree;
* `slotT2Six` (`D_z`-transport with a flat angular coefficient of order 1) — proved elsewhere;
* `slotT3Coef5` (below): the paper's `Transport3` at level six, in the priced form
  `WlInf α 6 f + CoefTh 5 f` with the matching hypothesis `CoefThMem 5 f`.

The per-slot `D_z`-transport bound is obtained from the exact Leibniz expansion
`SixRoute.sixExpansion` and the per-summand estimate `N6TP.summandBound`; the one non-pointwise
branch is the leaf `(a₁,b₁) = (0,0)`, which is the radial integration by parts of
`SixRoute.fluxFamSix` / `fluxFamSixTop`.
-/

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.N6TPPriced

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option maxHeartbeats 4000000

/-! ## Elementary closure of `SmoothOpen` -/

/-- `SmoothOpen` is closed under products (interior `C^∞` on the open quadrant). -/
theorem SmoothOpen.mul {F G : ℝ → ℝ → ℝ} (hF : Work.FTS.EllipticEst.SmoothOpen F)
    (hG : Work.FTS.EllipticEst.SmoothOpen G) :
    Work.FTS.EllipticEst.SmoothOpen (fun z θ => F z θ * G z θ) := by
  unfold Work.FTS.EllipticEst.SmoothOpen
  convert hF.mul hG using 1
  ext p
  rfl

/-! ## The `IP6` unfolding -/

/-- `IPn α 5` is the concrete `IP6 1 1 1 1 1 1 1 1 1 1`. -/
theorem IP6_one_eq_IPn_five (α : ℝ) (u v : Fn) :
    Work.FTS.StrongPersist.IP6 1 1 1 1 1 1 1 1 1 1 α u v = Work.FTS.TransportS.IPn α 5 u v := by
  have hIP6 : Work.FTS.StrongPersist.IP6 1 1 1 1 1 1 1 1 1 1 α
      = Work.Coercivity.HkIPStep 1 1 (Work.Coercivity.HkIPStep 1 1
          (Work.FTS.CoercivityFix.Assembly.IP4 1 1 1 1 1 1 α)) := rfl
  have h5 : Work.FTS.TransportS.IPn α 5
      = Work.Coercivity.HkIPStep 1 1 (Work.Coercivity.HkIPStep 1 1
          (Work.FTS.CoercivityFix.Assembly.IP4 1 1 1 1 1 1 α)) := rfl
  rw [hIP6, h5]

/-- The level-six slot sum is bounded by `84 * B` when every leaf slot is bounded by `B`:
there are `28` slots `(a,b)` with `a + b ≤ 6` and three leaf weights each. -/
theorem SlotSum_six_le (α : ℝ) (u v : Fn) (B : ℝ) (hB0 : 0 ≤ B)
    (hB : ∀ (a b : ℕ) (ρ : ℝ → ℝ → ℝ), a + b ≤ 6 →
      Work.FTS.TransportS.IsLeafW α a ρ →
      |Work.FTS.TransportS.slotPairing ρ a b u v| ≤ B) :
    Work.FTS.TransportS.SlotSum α 6 u v ≤ 84 * B := by
  have hterm : ∀ a ∈ Finset.range 7, ∀ b ∈ Finset.range (7 - a),
      Work.FTS.TransportS.SlotTerm α a b u v ≤ 3 * B := by
    intro a ha b hb
    have hab : a + b ≤ 6 := by
      have h1 : a ≤ 6 := Nat.le_of_lt_succ (Finset.mem_range.mp ha)
      have h2 : b < 7 - a := Finset.mem_range.mp hb
      omega
    have hE := hB a b Work.FTS.TransportS.leafEta hab (Or.inl rfl)
    have hO := hB a b Work.FTS.TransportS.leafOne hab (Or.inr (Or.inl rfl))
    have hG : (if 1 ≤ a then
        |Work.FTS.TransportS.slotPairing (Work.FTS.TransportS.leafGam α) a b u v| else 0) ≤ B := by
      by_cases h : 1 ≤ a
      · rw [ite_eq_left h]
        exact hB a b (Work.FTS.TransportS.leafGam α) hab (Or.inr (Or.inr ⟨h, rfl⟩))
      · rw [ite_eq_right h]; exact hB0
    calc Work.FTS.TransportS.SlotTerm α a b u v
        = |Work.FTS.TransportS.slotPairing Work.FTS.TransportS.leafEta a b u v|
          + |Work.FTS.TransportS.slotPairing Work.FTS.TransportS.leafOne a b u v|
          + (if 1 ≤ a then
              |Work.FTS.TransportS.slotPairing (Work.FTS.TransportS.leafGam α) a b u v| else 0) := rfl
      _ ≤ B + B + B := by linarith
      _ = 3 * B := by ring
  calc Work.FTS.TransportS.SlotSum α 6 u v
      = ∑ a ∈ Finset.range 7, ∑ b ∈ Finset.range (7 - a),
          Work.FTS.TransportS.SlotTerm α a b u v :=
        Work.FTS.TransportS.SlotSum_eq_sum_SlotTerm α 6 u v
    _ ≤ ∑ a ∈ Finset.range 7, ∑ b ∈ Finset.range (7 - a), (3 * B) :=
        Finset.sum_le_sum fun a ha => Finset.sum_le_sum fun b hb => hterm a ha b hb
    _ = ∑ a ∈ Finset.range 7, ((7 - a : ℕ) : ℝ) * (3 * B) := by
        refine Finset.sum_congr rfl fun a ha => ?_
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    _ = (∑ a ∈ Finset.range 7, ((7 - a : ℕ) : ℝ)) * (3 * B) := by
        rw [Finset.sum_mul]
    _ = 84 * B := by
        have h : (∑ a ∈ Finset.range 7, (7 - a)) = 28 := by decide
        have h' : (∑ a ∈ Finset.range 7, ((7 - a : ℕ) : ℝ)) = 28 := by
          exact_mod_cast h
        rw [h']; ring

/-! ## The level-six `D_z`-transport slot bound with a flat coefficient of order five -/


/-! ## The three clauses from the per-slot bounds -/




end Work.FTS.StrongPersist.N6TPPriced

namespace Work.FTS.StrongPersist

/-! ## The final assembly -/


end Work.FTS.StrongPersist
end
end
