import Mathlib
import Submission.Work.ELAssembly.PullInputs
import Submission.Work.ELAssembly.pullD_arc
import Submission.Work.ELAssembly.pullD_pair
import Submission.Work.ELAssembly.pullD_one
import Submission.Work.ELNest.armChain_nest

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option linter.unusedVariables false

noncomputable section

namespace Work.ELAssembly

open LeanEval.ComplexAnalysis (Tantibar)

/-! ## The angle translation between the nest list `[Za n, Zb n, Zc n]` and the arms

The `b₂`-nest of `Work.ELAssembly.PullInputs` is the three-pair list
`[N.Za n, N.Zb n, N.Zc n]`, whose angle pairs are by construction
`(armA1 n, armA2 n)`, `(armB1 n, armB2 n)`, `(armC1 n, armC2 n + 1)` (`N.Zaa … N.Zcb`).  The
four little lemmas below translate a statement about *all* pairs of the list into the three arm
statements, and back. -/

variable {c : ℂ} {d : Work.EL.RootParabolic c} {N : NestPairs d}

/-- Membership in the three-element nest list, unfolded. -/
lemma mem_armList_iff {n : ℕ} (P : Work.EL.CoPair d.hN) :
    P ∈ [N.Za n, N.Zb n, N.Zc n] ↔ P = N.Za n ∨ P = N.Zb n ∨ P = N.Zc n := by
  simp

/-- The arm-`A` statement extracted from a statement about the whole nest list. -/
lemma notInClosedArc_armA {n : ℕ} {x : ℝ}
    (h : ∀ P ∈ [N.Za n, N.Zb n, N.Zc n], ¬ Work.EL.InClosedArc x P.a P.b) :
    ¬ Work.EL.InClosedArc x (Work.ELNest.armA1 n) (Work.ELNest.armA2 n) := by
  have h' := h (N.Za n) (by simp)
  rwa [N.Zaa n, N.Zab n] at h'

/-- The arm-`B` statement extracted from a statement about the whole nest list. -/
lemma notInClosedArc_armB {n : ℕ} {x : ℝ}
    (h : ∀ P ∈ [N.Za n, N.Zb n, N.Zc n], ¬ Work.EL.InClosedArc x P.a P.b) :
    ¬ Work.EL.InClosedArc x (Work.ELNest.armB1 n) (Work.ELNest.armB2 n) := by
  have h' := h (N.Zb n) (by simp)
  rwa [N.Zba n, N.Zbb n] at h'

/-- The arm-`C` statement extracted from a statement about the whole nest list. -/
lemma notInClosedArc_armC {n : ℕ} {x : ℝ}
    (h : ∀ P ∈ [N.Za n, N.Zb n, N.Zc n], ¬ Work.EL.InClosedArc x P.a P.b) :
    ¬ Work.EL.InClosedArc x (Work.ELNest.armC1 n) (Work.ELNest.armC2 n + 1) := by
  have h' := h (N.Zc n) (by simp)
  rwa [N.Zca n, N.Zcb n] at h'

/-- The three arm statements reassembled into a statement about the whole nest list. -/
lemma notInClosedArc_of_arms {n : ℕ} {y : ℝ}
    (hA : ¬ Work.EL.InClosedArc y (Work.ELNest.armA1 n) (Work.ELNest.armA2 n))
    (hB : ¬ Work.EL.InClosedArc y (Work.ELNest.armB1 n) (Work.ELNest.armB2 n))
    (hC : ¬ Work.EL.InClosedArc y (Work.ELNest.armC1 n) (Work.ELNest.armC2 n + 1)) :
    ∀ P ∈ [N.Za n, N.Zb n, N.Zc n], ¬ Work.EL.InClosedArc y P.a P.b := by
  intro P hP
  rcases (mem_armList_iff (N := N) P).mp hP with rfl | rfl | rfl
  · rwa [N.Zaa n, N.Zab n]
  · rwa [N.Zba n, N.Zbb n]
  · rwa [N.Zca n, N.Zcb n]

/-! ## The middle of the near arc of the `b₂`-nest

`Work.EL.midNear [Za n, Zb n, Zc n]` is a point of the near arc `[armA2 n, armB1 n]` following
the first pair (`armA2` is the end of the arm-`A` pair, `armB1` the start of the arm-`B` pair):
it is `armA2 n + (1/2)·arcLen (armA2 n) (armB1 n)`.  This is the `hm` input of
`Work.ELAssembly.pullD_one`; the second component (`≠ armA2 n`) is the non-degeneracy of that near
arc. -/

/-- The defining equation of `Work.EL.midNear` on a list of at least two pairs. -/
lemma midNear_cons_cons (P Q : Work.EL.CoPair d.hN) (l : List (Work.EL.CoPair d.hN)) :
    Work.EL.midNear (P :: Q :: l) = P.b + Int.fract (Q.a - P.b) / 2 := rfl

/-- **`midNear` lies in the near arc `[armA2 n, armB1 n]`** (and is not its left end). -/
lemma midNear_Z_mem {n : ℕ} :
    Work.EL.InClosedArc (Work.EL.midNear [N.Za n, N.Zb n, N.Zc n])
        (Work.ELNest.armA2 n) (Work.ELNest.armB1 n) ∧
      Work.EL.midNear [N.Za n, N.Zb n, N.Zc n] ≠ Work.ELNest.armA2 n := by
  set L : ℝ := (1197 : ℝ) / 21483 * ((64 : ℝ) ^ n)⁻¹ with hLdef
  have hLpos : 0 < L := by rw [hLdef]; positivity
  have hLlt : L < 1 := by
    rw [hLdef]
    nlinarith [Work.ELAssembly.inv_pow_64_le_one n]
  have harc2 : Work.EL.arcLen (Work.ELNest.armA2 n) (Work.ELNest.armB1 n) = L := by
    rw [hLdef, Work.ELAssembly.arcLen_A2B1 n]
  have harc : Int.fract (Work.ELNest.armB1 n - Work.ELNest.armA2 n) = L := by
    rw [← Work.EL.arcLen, harc2]
  have hmid : Work.EL.midNear [N.Za n, N.Zb n, N.Zc n] = Work.ELNest.armA2 n + L / 2 := by
    rw [midNear_cons_cons, N.Zab n, N.Zba n, harc]
  have hfrac : Int.fract (Work.EL.midNear [N.Za n, N.Zb n, N.Zc n] - Work.ELNest.armA2 n)
      = L / 2 := by
    rw [show Work.EL.midNear [N.Za n, N.Zb n, N.Zc n] - Work.ELNest.armA2 n = L / 2 from by
      rw [hmid]; ring]
    exact Int.fract_eq_self.mpr ⟨by linarith, by linarith⟩
  constructor
  · rw [Work.EL.InClosedArc, hfrac, harc2]
    exact ⟨by linarith, by linarith⟩
  · rw [hmid]
    intro hc
    linarith

/-! ## The statement -/

-- Shell: `namespace Work.ELAssembly` (area `Submission/Work/ELAssembly/`).
/-- **The `b₂`-nest pull-back inputs from the rational certificate.**  The analogue of
`Work.ELAssembly.qPullInputs_of` for the three-chain nest `[N.Za n, N.Zb n, N.Zc n]`: the three
angle fields `arc`, `pair`, `one` of `Work.ELAssembly.DPullInputs` (the inputs of
`Work.ELAssembly.pullD_bij`) follow from `Work.ELAssembly.pullD_arc` / `pullD_pair` / `pullD_one`
(the exact rational arithmetic on the closed forms `armA1 … armC2` of
`Work.ELNest.armChain_nest`) together with the angle specifications `N.Zaa`/`N.Zab`/`N.Zba`/… of
`NestPairs`, so that only `hL` and `hcv` remain as inputs. -/
theorem dPullInputs_of {c : ℂ} {d : Work.EL.RootParabolic c} {L : ℝ} {N : NestPairs d}
    (hL : 1 < L)
    (hcv : ∀ n : ℕ, ∀ k ∈ Set.Icc 1 6,
      (LeanEval.ComplexAnalysis.Tantibar c)^[k] 0 ∉
        Work.EL.polyRegion [N.Za n, N.Zb n, N.Zc n] (Work.ELNest.Dlev L n)) :
    DPullInputs c d L N := by
  refine ⟨hL, hcv, ?_, ?_, ?_⟩
  · -- `arc`: `pullD_arc` transported along the angle specifications of `NestPairs`.
    intro n x hx
    have hp := pullD_arc n x
      (notInClosedArc_armA (n := n + 1) hx)
      (notInClosedArc_armB (n := n + 1) hx)
      (notInClosedArc_armC (n := n + 1) hx)
    exact notInClosedArc_of_arms hp.1 hp.2.1 hp.2.2
  · -- `pair`: the first angle of each pair of the list maps to the first angle of the target pair
    -- (`pullD_pair`, first conjunct in each arm).
    intro n P' hP'
    rcases (mem_armList_iff (N := N) P').mp hP' with rfl | rfl | rfl
    · exact ⟨N.Za n, by simp,
        Or.inl (by rw [N.Zaa (n + 1), N.Zaa n, (pullD_pair n).1])⟩
    · exact ⟨N.Zb n, by simp,
        Or.inl (by rw [N.Zba (n + 1), N.Zba n, (pullD_pair n).2.2.1])⟩
    · exact ⟨N.Zc n, by simp,
        Or.inl (by rw [N.Zca (n + 1), N.Zca n, (pullD_pair n).2.2.2.2.1])⟩
  · -- `one`: `pullD_one` at the middle of the near arc `[armA2 n, armB1 n]`.
    intro n x y hx hy hxk hyk
    exact pullD_one n (Work.EL.midNear [N.Za n, N.Zb n, N.Zc n]) x y
      (midNear_Z_mem (n := n) (N := N)).1 (midNear_Z_mem (n := n) (N := N)).2
      (notInClosedArc_armA (n := n + 1) hx) (notInClosedArc_armB (n := n + 1) hx)
      (notInClosedArc_armC (n := n + 1) hx)
      (notInClosedArc_armA (n := n + 1) hy) (notInClosedArc_armB (n := n + 1) hy)
      (notInClosedArc_armC (n := n + 1) hy)
      hxk hyk

end Work.ELAssembly
