/-
# EL nest, part 9 (N3): co-landing of the arm pairs at `b₂` for all levels

The first clause of the contract's N3: the level-`n` arm pairs of the nest at `b₂` co-land, for
every `n`.  The level-`0` case is the root-orbit pair `P₀`, `P₂`, `P₄`; every further level is one
application of the certified arm chains (`armChain_lands`) with the angle identification
(`armChain_nest`), the three arms being advanced together.
-/
import Mathlib
import Submission.Work.ELNest.ArmChain
import Submission.Work.ELNest.armChain_lands
import Submission.Work.ELNest.armChain_nest

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Filter Set Topology Function
open scoped Topology ComplexConjugate

set_option linter.unusedVariables false

noncomputable section

namespace Work.ELNest

open Work.EL

/-- **N3, co-landing of the arm pairs for all levels.**  Given the co-landing of the level-`0`
arm pairs (`P₀`, `P₂`, `P₄`), the non-degeneracy of the arm angles and the `c`-side conditions of
the six-step chains at every level, the level-`n` arm pairs co-land for every `n`. -/
theorem armPair_coLands {c : ℂ} (hc : c ∈ LeanEval.ComplexAnalysis.Mandelbar)
    (hN : Work.ELPull.DynB c)
    (hφ : Work.ParamRays.IsDynBottcher c (Work.ParamRays.dynPhiOf c))
    (htop : Work.ELPull.PB1Top hN)
    (hbaseA : ∃ y : ℂ, Work.ELPull.LandsN hN (armA1 0) y ∧ Work.ELPull.LandsN hN (armA2 0) y)
    (hbaseB : ∃ y : ℂ, Work.ELPull.LandsN hN (armB1 0) y ∧ Work.ELPull.LandsN hN (armB2 0) y)
    (hbaseC : ∃ y : ℂ, Work.ELPull.LandsN hN (armC1 0) y ∧ Work.ELPull.LandsN hN (armC2 0) y)
    (hndA : ∀ n, Work.EL.arcLen (armA1 n) (armA2 n) ≠ 0)
    (hndB : ∀ n, Work.EL.arcLen (armB1 n) (armB2 n) ≠ 0)
    (hndC : ∀ n, Work.EL.arcLen (armC1 n) (armC2 n) ≠ 0)
    (hcvA : ∀ (n t : ℕ) (Q : Work.ELPull.CoPair hN), t < 6 →
      Q.a = (armPairOf nearA kA (armA1 n, armA2 n) t).1 →
      Q.b = (armPairOf nearA kA (armA1 n, armA2 n) t).2 →
      c ∈ Work.ELPull.arcSide hN Q
        (armArcOf nearA (5 - t) (armPairOf nearA kA (armA1 n, armA2 n) t)).2
        (armArcOf nearA (5 - t) (armPairOf nearA kA (armA1 n, armA2 n) t)).1)
    (hcvB : ∀ (n t : ℕ) (Q : Work.ELPull.CoPair hN), t < 6 →
      Q.a = (armPairOf nearB kB (armB1 n, armB2 n) t).1 →
      Q.b = (armPairOf nearB kB (armB1 n, armB2 n) t).2 →
      c ∈ Work.ELPull.arcSide hN Q
        (armArcOf nearB (5 - t) (armPairOf nearB kB (armB1 n, armB2 n) t)).2
        (armArcOf nearB (5 - t) (armPairOf nearB kB (armB1 n, armB2 n) t)).1)
    (hcvC : ∀ (n t : ℕ) (Q : Work.ELPull.CoPair hN), t < 6 →
      Q.a = (armPairOf nearC kC (armC1 n, armC2 n) t).1 →
      Q.b = (armPairOf nearC kC (armC1 n, armC2 n) t).2 →
      c ∈ Work.ELPull.arcSide hN Q
        (armArcOf nearC (5 - t) (armPairOf nearC kC (armC1 n, armC2 n) t)).2
        (armArcOf nearC (5 - t) (armPairOf nearC kC (armC1 n, armC2 n) t)).1) :
    ∀ n : ℕ,
      (∃ y : ℂ, Work.ELPull.LandsN hN (armA1 n) y ∧ Work.ELPull.LandsN hN (armA2 n) y) ∧
      (∃ y : ℂ, Work.ELPull.LandsN hN (armB1 n) y ∧ Work.ELPull.LandsN hN (armB2 n) y) ∧
      (∃ y : ℂ, Work.ELPull.LandsN hN (armC1 n) y ∧ Work.ELPull.LandsN hN (armC2 n) y) := by
  intro n
  induction n with
  | zero => exact ⟨hbaseA, hbaseB, hbaseC⟩
  | succ n ih =>
    obtain ⟨⟨yA, hA1, hA2⟩, ⟨yB, hB1, hB2⟩, ⟨yC, hC1, hC2⟩⟩ := ih
    obtain ⟨⟨yA', hA1', hA2'⟩, ⟨yB', hB1', hB2'⟩, ⟨yC', hC1', hC2'⟩⟩ :=
      armChain_lands hc hN hφ htop (armA1 n) (armA2 n) (armB1 n) (armB2 n) (armC1 n) (armC2 n)
        hA1 hA2 hB1 hB2 hC1 hC2 (hndA n) (hndB n) (hndC n)
        (hcvA n) (hcvB n) (hcvC n)
    rw [(armChain_nest n).1] at hA1' hA2'
    rw [(armChain_nest n).2.1] at hB1' hB2'
    rw [(armChain_nest n).2.2] at hC1' hC2'
    -- the `C` chain produces the swapped order `(armC2, armC1)` of the same pair
    exact ⟨⟨yA', hA1', hA2'⟩, ⟨yB', hB1', hB2'⟩, ⟨yC', hC2', hC1'⟩⟩

end Work.ELNest
