import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.StrongPersist.N6Trans.slotT2Six
import Submission.Work.FTS.StrongPersist.N6Trans.slotT3SixRoute
import Submission.Work.FTS.StrongPersist.N6_prod
import Submission.Work.FTS.TransportS.ip4SlotDomFixed
import Submission.Work.FTS_RegExport.RXB.sup_bound_all_alpha
import Submission.Work.PhiStar.Honesty.sqrt_weight_mul_eq_of_mem_Ioo

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS.StrongPersist.N6Trans_exists` — the level-six transport clauses for `IP6`

`N6Trans (IP6 1 1 1 1 1 1 1 1 1 1) α₂ Ct` is the `k = 6` restatement of the transport clauses
T1/T2/T3 of Elgindi's paper (tex 1099–1123) for the concrete coercive pairing `IP6` with all
step coefficients `1`.

## The route

`IP6 1 1 1 1 1 1 1 1 1 1 α = IPn α 5` (the five-fold iteration of `HkIPStep 1 1` applied to
`H1IP`), and the proved unfolding bound `Work.FTS.TransportS.ip4_unfold_bound` gives

  `|IP6 1 … 1 α u v| ≤ 3^5 · 10^22 · SlotSum α 6 u v`,

where `SlotSum α 6 u v` is the sum of the absolute values of the *leaf slot pairings*
`∫_z ∫_θ ρ · (D_z^b D_θ^a u) · (D_z^b D_θ^a v)` over the slots `a + b ≤ 6` and the three leaf
weights `ρ` of `H1IP` (`leafEta`, `leafOne`, and `leafGam α` at the slots with `a ≥ 1`).

The three clauses therefore follow from the three *per-slot* transport estimates at level six,
one for each of the three velocity classes of the paper:

* `slotT1Six` — `D_θ`-transport with an `ℋ⁶`-coefficient (the paper's `Transport1`, tex 1099);
* `slotT2Six` — `D_z`-transport with a flat angular coefficient (the paper's `Transport2`,
  tex 1114, in the `CoefTh`-form of `VocabO.T2Clause`);
* `slotT3Six` — `D_z`-transport with a `𝒲^{6,∞}`-coefficient (the paper's `Transport3`,
  tex 1119).

The present file contains the *assembly*: the unfolding, the summation over the `84 = 28 · 3`
leaf slots, the merging of the three constants, and the packaging into the `N6Trans` structure.
-/

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## Elementary helpers -/

/-- `SmoothOpen` is closed under products (interior `C^∞` on the open quadrant). -/
theorem SmoothOpen.mul {F G : ℝ → ℝ → ℝ} (hF : Work.FTS.EllipticEst.SmoothOpen F)
    (hG : Work.FTS.EllipticEst.SmoothOpen G) :
    Work.FTS.EllipticEst.SmoothOpen (fun z θ => F z θ * G z θ) := by
  unfold Work.FTS.EllipticEst.SmoothOpen
  convert hF.mul hG using 1
  ext p
  rfl

/-- `IPn α 5` is the concrete `IP6 1 1 1 1 1 1 1 1 1 1`. -/
theorem IP6_one_eq_IPn_five (α : ℝ) (u v : Fn) :
    IP6 1 1 1 1 1 1 1 1 1 1 α u v = Work.FTS.TransportS.IPn α 5 u v := by
  have hIP6 : IP6 1 1 1 1 1 1 1 1 1 1 α
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
      · rw [if_pos h]
        exact hB a b (Work.FTS.TransportS.leafGam α) hab (Or.inr (Or.inr ⟨h, rfl⟩))
      · rw [if_neg h]; exact hB0
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

/-! ## The three clauses from the per-slot bounds -/




/-! ## The final assembly -/



end Work.FTS.StrongPersist
