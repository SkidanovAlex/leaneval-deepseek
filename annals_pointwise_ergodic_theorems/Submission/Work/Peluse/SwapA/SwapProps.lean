import Mathlib
import Submission.Work.Peluse.Holds.SwapDefs

/-!
# The dense-concatenation interface of the regime-swap route (subproject `SwapA`)

Design: `Submission/Work/Peluse/P2P3_LEAD.md`.  The assembly `Work.Peluse.SwapA.p3Heart_all`
( = `∀ t ≥ 1, p3Heart t`, the heart of `lemma51P` at *every* level, with no induction hypothesis)
consumes three nodes that live in sibling subprojects:

* `concatStep`  (KKL Lemma 6.1, one concatenation step) -- subproject `Peluse/SwapC`;
* `concatAll`   (KKL Prop. 6.2, the full concatenation) -- subproject `Peluse/SwapC`;
* `denseEndgame`(the linear-in-law endgame) -- subproject `Peluse/SwapE`.

This module names those three statements as `Prop`s, verbatim from
`Submission/Work/Peluse/P2P3_STATEMENTS.lean.txt` (the lead-frozen reference), so that the assembly
can be stated and proved *against the frozen statements* before the sibling modules land.  When a
sibling's theorem exists, it is used directly: each `Prop` is a transparent `def` whose body is
literally the sibling's statement, so `exact hconcatStep` discharges a `ConcatStepP` hypothesis.

The vocabulary (`pbox`, `pboxSum`, `avg`, `denseAvg`, `slotSet`, `slotCard`, `slotAt`, `genPair`,
`pdir`) is LEAD-FROZEN in `Submission/Work/Peluse/Holds/SwapDefs.lean` and is *not* redefined here.
-/

set_option autoImplicit false
open scoped BigOperators

namespace Work.Peluse.SwapA

noncomputable section

open Work.Peluse.LadderP.Swap

/-- **(L61) One concatenation step** (Kuca / Kravitz–Kuca–Leng Lemma 6.1): the raw slot `qH i` is
concatenated across two independent indices, the other slots are doubled.  Verbatim from the frozen
node list; this is the statement of the subproject `Peluse/SwapC`. -/
def ConcatStepP : Prop :=
  ∀ s : ℕ, ∃ C : ℝ, 0 < C ∧ ∃ e : ℕ, 1 ≤ e ∧
    ∀ (I : Type) [Fintype I] [Nonempty I] (qH : I → ℤ) (q₁ q₂ : I → Fin s → ℤ)
      (M N : ℕ) (x₀ : ℤ) (δ : ℝ) (f : ℤ → ℂ),
      1 ≤ M → (∀ x : ℤ, (N : ℤ) < |x - x₀| → f x = 0) → (∀ x : ℤ, ‖f x‖ ≤ 1) → 0 < δ →
      δ ≤ Work.Peluse.LadderP.Swap.avg (fun i : I => Work.Peluse.LadderP.Swap.pbox (s + 1)
            (Fin.cons (qH i) (q₁ i)) (Fin.cons 0 (q₂ i)) M (Work.Peluse.symIcc N) f) →
      C * δ ^ e ≤ Work.Peluse.LadderP.Swap.avg (fun p : I × I =>
        Work.Peluse.LadderP.Swap.pbox (s + s + 1)
          (Fin.snoc (Fin.append (q₁ p.1) (q₁ p.2)) (qH p.2))
          (Fin.snoc (Fin.append (q₂ p.1) (q₂ p.2)) (qH p.1)) M (Work.Peluse.symIcc N) f)

/-- **(P62) Full concatenation** (KKL Prop. 6.2): all `s` raw slots concatenated; slot `k` of the
output is `q_j(ι ε)[M] − q_j(ι ε')[M]` for `(j,ε,ε') = slotAt s k`.  Verbatim from the frozen node
list; this is the statement of the subproject `Peluse/SwapC`. -/
def ConcatAllP : Prop :=
  ∀ s : ℕ, 1 ≤ s → ∃ C : ℝ, 0 < C ∧ ∃ e : ℕ, 1 ≤ e ∧
    ∀ (I : Type) [Fintype I] [Nonempty I] (q : I → Fin s → ℤ) (M N : ℕ) (δ : ℝ) (f : ℤ → ℂ),
      1 ≤ M → Work.Peluse.SupportIn f N → (∀ x : ℤ, ‖f x‖ ≤ 1) → 0 < δ →
      δ ≤ Work.Peluse.LadderP.Swap.avg (fun i : I => Work.Peluse.LadderP.Swap.pbox s (q i)
        (fun _ => 0) M (Work.Peluse.symIcc N) f) →
      C * δ ^ e ≤ Work.Peluse.LadderP.Swap.avg (fun ι : (Fin s → Bool) → I =>
        Work.Peluse.LadderP.Swap.pbox (Work.Peluse.LadderP.Swap.slotCard s)
          (fun k => q (ι (Work.Peluse.LadderP.Swap.slotAt s k).2.1)
            (Work.Peluse.LadderP.Swap.slotAt s k).1)
          (fun k => q (ι (Work.Peluse.LadderP.Swap.slotAt s k).2.2)
            (Work.Peluse.LadderP.Swap.slotAt s k).1) M (Work.Peluse.symIcc N) f)

open Classical in
/-- **(END) Linear-in-law endgame.**  Generic multiset slots have bounded density on
`[−2HM, 2HM]`, so the averaged multiset box norm controls a uniformity norm at any window
`D ≤ HM`, `D ≤ N`.  Verbatim from the frozen node list; this is the statement of the subproject
`Peluse/SwapE`. -/
def DenseEndgameP : Prop :=
  ∀ d : ℕ, 1 ≤ d → ∃ K : ℕ, 1 ≤ K ∧ ∃ s' : ℕ, 2 ≤ s' ∧ ∃ C : ℝ, 0 < C ∧
    ∀ (Ω : Type) [Fintype Ω] [Nonempty Ω] (q₁ q₂ : Ω → Fin d → ℤ) (G : Finset Ω)
      (H M D N : ℕ) (η δ : ℝ) (f : ℤ → ℂ),
      1 ≤ H → 1 ≤ M → 1 ≤ D → D ≤ H * M → D ≤ N →
      Work.Peluse.SupportIn f N → (∀ x : ℤ, ‖f x‖ ≤ 1) → 0 < η → η ≤ 1 → 0 < δ →
      (∀ ω k, |q₁ ω k| ≤ (H : ℤ) ∧ |q₂ ω k| ≤ (H : ℤ)) →
      (∀ ω ∈ G, ∀ k, Work.Peluse.LadderP.Swap.genPair H η (q₁ ω k) (q₂ ω k)) →
      (((Finset.univ \ G).card : ℝ) ≤ δ / 2 * (Fintype.card Ω : ℝ)) →
      δ ≤ Work.Peluse.LadderP.Swap.avg (fun ω : Ω =>
        Work.Peluse.LadderP.Swap.pbox d (q₁ ω) (q₂ ω) M (Work.Peluse.symIcc N) f) →
      C * (δ * η ^ 2 * (M : ℝ) / ((M : ℝ) + (H : ℝ))) ^ K
        ≤ Work.Peluse.uNorm s' (Work.Peluse.arithIcc 1 D) (Work.Peluse.symIcc N) f

end

end Work.Peluse.SwapA
