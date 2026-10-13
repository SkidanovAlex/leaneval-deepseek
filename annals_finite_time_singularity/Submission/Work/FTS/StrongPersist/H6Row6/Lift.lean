/-
# `H6Row6/Lift` — from a per-slot bound to the `IP6` bound

`Npair6Aux.IP6_unfold_bound` bounds `|IP6 1…1 α u f|` by `3^5·10^22` times
`SlotSum α 6 u f = Σ_{a+b≤6} Σ_ρ |slotPairing ρ a b u f|`.  Hence a bound that is *uniform* in
the slot `(a,b)` and the leaf `ρ` lifts to the pairing: there are `28 ≤ 49` slots and `3` leaves,
so `SlotSum α 6 u f ≤ 147 · B` whenever every slot pairing is `≤ B`.

Everything here is elementary arithmetic on `Finset.sum`.
-/
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Order.Filter.Defs
import Submission.Work.FTS.StrongPersist.H6Row6.Basic
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6Aux.Unfold

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.H6Row6

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option linter.unusedVariables false

/-- The three leaf weights of the slot `a` satisfy `IsLeafW α a ρ`. -/
theorem isLeafW_eta (α : ℝ) (a : ℕ) : Work.FTS.TransportS.IsLeafW α a
    Work.FTS.TransportS.leafEta := Or.inl rfl

theorem isLeafW_one (α : ℝ) (a : ℕ) : Work.FTS.TransportS.IsLeafW α a
    Work.FTS.TransportS.leafOne := Or.inr (Or.inl rfl)

theorem isLeafW_gam (α : ℝ) {a : ℕ} (ha : 1 ≤ a) : Work.FTS.TransportS.IsLeafW α a
    (Work.FTS.TransportS.leafGam α) := Or.inr (Or.inr ⟨ha, rfl⟩)

/-- **The `IP6` pairing is bounded by `147` times any uniform per-slot bound.** -/
theorem ip6_le_of_slotRow {α B : ℝ} (hα : 0 < α) {u f : Fn}
    (hu : Work.FTS.EllipticEst.SmoothOpen u) (hf : Work.FTS.EllipticEst.SmoothOpen f)
    (hB0 : 0 ≤ B)
    (hB : ∀ (a b : ℕ) (ρ : ℝ → ℝ → ℝ), a + b ≤ 6 → Work.FTS.TransportS.IsLeafW α a ρ →
      |Work.FTS.TransportS.slotPairing ρ a b u f| ≤ B) :
    |Work.FTS.StrongPersist.IP6 1 1 1 1 1 1 1 1 1 1 α u f|
      ≤ (3 : ℝ) ^ 5 * (10 : ℝ) ^ 22 * (147 * B) := by
  have h := Work.FTS.StrongPersist.H6Rows.Npair6Aux.IP6_unfold_bound α u f hu hf
  refine le_trans h (mul_le_mul_of_nonneg_left ?_ (by positivity))
  -- the slot sum is at most `147 B`
  have hterm : ∀ a b : ℕ, a + b ≤ 6 → Work.FTS.TransportS.SlotTerm α a b u f ≤ 3 * B := by
    intro a b hab
    have hE : |Work.FTS.TransportS.slotPairing Work.FTS.TransportS.leafEta a b u f| ≤ B :=
      hB a b _ hab (isLeafW_eta α a)
    have hO : |Work.FTS.TransportS.slotPairing Work.FTS.TransportS.leafOne a b u f| ≤ B :=
      hB a b _ hab (isLeafW_one α a)
    rw [Work.FTS.TransportS.SlotTerm]
    by_cases ha : 1 ≤ a
    · rw [if_pos ha]
      have hG : |Work.FTS.TransportS.slotPairing (Work.FTS.TransportS.leafGam α) a b u f|
          ≤ B := hB a b _ hab (isLeafW_gam α ha)
      linarith
    · rw [if_neg ha]
      linarith
  have htwo : 0 ≤ 3 * B := by linarith
  have hinner : ∀ a ∈ Finset.range 7,
      (∑ b ∈ Finset.range (7 - a), Work.FTS.TransportS.SlotTerm α a b u f) ≤ 7 * (3 * B) := by
    intro a ha
    rw [Finset.mem_range] at ha
    have h1 : ∀ b ∈ Finset.range (7 - a), Work.FTS.TransportS.SlotTerm α a b u f ≤ 3 * B := by
      intro b hb
      rw [Finset.mem_range] at hb
      exact hterm a b (by omega)
    have h2 := Finset.sum_le_card_nsmul (Finset.range (7 - a))
      (fun b => Work.FTS.TransportS.SlotTerm α a b u f) (3 * B) h1
    have h3 : ((7 - a : ℕ) : ℝ) ≤ 7 := by
      have h4 : (7 - a : ℕ) ≤ 7 := Nat.sub_le _ _
      exact_mod_cast h4
    calc (∑ b ∈ Finset.range (7 - a), Work.FTS.TransportS.SlotTerm α a b u f)
        ≤ (Finset.range (7 - a)).card • (3 * B) := h2
      _ = ((7 - a : ℕ) : ℝ) * (3 * B) := by rw [Finset.card_range, nsmul_eq_mul]
      _ ≤ 7 * (3 * B) := mul_le_mul_of_nonneg_right h3 htwo
  show (∑ a ∈ Finset.range 7, ∑ b ∈ Finset.range (7 - a),
          Work.FTS.TransportS.SlotTerm α a b u f) ≤ 147 * B
  have hout := Finset.sum_le_card_nsmul (Finset.range 7)
    (fun a => ∑ b ∈ Finset.range (7 - a), Work.FTS.TransportS.SlotTerm α a b u f)
    (7 * (3 * B)) hinner
  calc (∑ a ∈ Finset.range 7, ∑ b ∈ Finset.range (7 - a),
          Work.FTS.TransportS.SlotTerm α a b u f)
      ≤ (Finset.range 7).card • (7 * (3 * B)) := hout
    _ = 147 * B := by rw [Finset.card_range, nsmul_eq_mul]; ring

end Work.FTS.StrongPersist.H6Row6
