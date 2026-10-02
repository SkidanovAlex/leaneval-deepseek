/-
# EL nest, part 3 (N1/N3): the co-landing sequences of the two nests exist

The nest pairs `Qp n` (at `z₁`) and `Za n`, `Zb n`, `Zc n` (at `b₂`) are *sequences* of
co-landing pairs whose angles are prescribed by the certificate.  This file proves that such
sequences exist as soon as (i) the base pair of the sequence co-lands, and (ii) the one-step
pull-back of a co-landing pair of the sequence is again a co-landing pair of the sequence
(hypothesis `hstep`, which the certificate chains of `ELPull` supply: `pb1Top` applied to the ten
`T`-preimages of the near arc, with the c-free-arc condition).

What is proved here is the *recursion*: the sequence of co-landing pairs with the prescribed
angles, and (for the nest at `z₁`) the landing-point shift `F c y_{n+1} = y_n` that goes with it.
-/
import Mathlib
import Submission.Work.ELNest.Setup
import Submission.Work.ELNest.Qp_shift

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

variable {c : ℂ} {φ : ℂ → ℂ}

/-- **The recursion of a co-landing sequence.**  If the pair of angles `(A 0, B 0)` co-lands and
every co-landing pair of angles `(A n, B n)` pulls back to a co-landing pair of angles
`(A (n+1), B (n+1))`, then there is a sequence of co-landing pairs with those angles. -/
theorem exists_seq_of_step (hN : DynB c φ) (A B : ℕ → ℝ)
    (hbase : ∃ y : ℂ, LandsN hN (A 0) y ∧ LandsN hN (B 0) y)
    (hstep : ∀ (n : ℕ) (y : ℂ), LandsN hN (A n) y → LandsN hN (B n) y →
      ∃ y' : ℂ, LandsN hN (A (n + 1)) y' ∧ LandsN hN (B (n + 1)) y') :
    ∃ Q : ℕ → CoPair hN, (∀ n, (Q n).a = A n) ∧ (∀ n, (Q n).b = B n) := by
  have hE : ∀ n : ℕ, ∃ y : ℂ, LandsN hN (A n) y ∧ LandsN hN (B n) y := by
    intro n
    induction n with
    | zero => exact hbase
    | succ n ih =>
      obtain ⟨y, hy1, hy2⟩ := ih
      obtain ⟨y', hy'1, hy'2⟩ := hstep n y hy1 hy2
      exact ⟨y', hy'1, hy'2⟩
  choose y hy using hE
  refine ⟨fun n => ⟨⟨A n, B n, y n⟩, (hy n).1, (hy n).2⟩, fun n => rfl, fun n => rfl⟩

/-- The base case of the `z₁`-nest: `beta0' = bAng' 0` and `beta0 + 1 = bAng 0 + 1`. -/
theorem bAng_zero : bAng' 0 = beta0' := by simp [bAng']

theorem bAng_zero' : bAng 0 + 1 = beta0 + 1 := by simp [bAng]

/-- **N1, existence of the nest pairs at `z₁`**: from the co-landing of the level-`0` `u`-pair
and the one-step pull-back, the whole sequence `Qp n` of co-landing pairs with angles
`(bAng' n, bAng n + 1)` exists, and it satisfies the shift `F c y_{n+1} = y_n` (the level-`n+1`
landing point is mapped to the level-`n` one by `F c = f_c^{10}`). -/
theorem exists_Qp_of_step (hN : DynB c φ) (hB : Work.ParamRays.IsDynBottcher c φ)
    (hbase : ∃ y : ℂ, LandsN hN beta0' y ∧ LandsN hN (beta0 + 1) y)
    (hstep : ∀ (n : ℕ) (y : ℂ), LandsN hN (bAng' n) y → LandsN hN (bAng n + 1) y →
      ∃ y' : ℂ, LandsN hN (bAng' (n + 1)) y' ∧ LandsN hN (bAng (n + 1) + 1) y') :
    ∃ Qp : ℕ → CoPair hN,
      (∀ n, (Qp n).a = bAng' n) ∧ (∀ n, (Qp n).b = bAng n + 1) ∧
      (∀ n, F c ((Qp (n + 1)).y) = (Qp n).y) := by
  have hbase' : ∃ y : ℂ, LandsN hN (bAng' 0) y ∧ LandsN hN (bAng 0 + 1) y := by
    obtain ⟨y, hy1, hy2⟩ := hbase
    exact ⟨y, by rwa [bAng_zero], by rwa [bAng_zero']⟩
  obtain ⟨Qp, ha, hb⟩ := exists_seq_of_step hN (fun n => bAng' n) (fun n => bAng n + 1)
    hbase' hstep
  refine ⟨Qp, ha, hb, ?_⟩
  intro n
  have h1 : LandsN hN (T^[10] (bAng' (n + 1))) (F c ((Qp (n + 1)).y)) :=
    landsN_iterate_F hN hB (by rw [← ha (n + 1)]; exact (Qp (n + 1)).lands_a)
  rw [(T_iterate_bAng n).2] at h1
  have h2 : LandsN hN (bAng' n) ((Qp n).y) := by rw [← ha n]; exact (Qp n).lands_a
  exact landsN_unique h1 h2

/-- **N3, existence of the arm pairs at `b₂`.**  From the co-landing of the level-`0` arm pairs
and the one-step pull-back for each arm, the three sequences `Za`, `Zb`, `Zc` of co-landing pairs
with the arm angles of the certificate exist. -/
theorem exists_Z_of_step (hN : DynB c φ)
    (hbaseA : ∃ y : ℂ, LandsN hN (armA1 0) y ∧ LandsN hN (armA2 0) y)
    (hbaseB : ∃ y : ℂ, LandsN hN (armB1 0) y ∧ LandsN hN (armB2 0) y)
    (hbaseC : ∃ y : ℂ, LandsN hN (armC1 0) y ∧ LandsN hN (armC2 0 + 1) y)
    (hstepA : ∀ (n : ℕ) (y : ℂ), LandsN hN (armA1 n) y → LandsN hN (armA2 n) y →
      ∃ y' : ℂ, LandsN hN (armA1 (n + 1)) y' ∧ LandsN hN (armA2 (n + 1)) y')
    (hstepB : ∀ (n : ℕ) (y : ℂ), LandsN hN (armB1 n) y → LandsN hN (armB2 n) y →
      ∃ y' : ℂ, LandsN hN (armB1 (n + 1)) y' ∧ LandsN hN (armB2 (n + 1)) y')
    (hstepC : ∀ (n : ℕ) (y : ℂ), LandsN hN (armC1 n) y → LandsN hN (armC2 n + 1) y →
      ∃ y' : ℂ, LandsN hN (armC1 (n + 1)) y' ∧ LandsN hN (armC2 (n + 1) + 1) y') :
    (∃ Za : ℕ → CoPair hN, (∀ n, (Za n).a = armA1 n) ∧ (∀ n, (Za n).b = armA2 n)) ∧
    (∃ Zb : ℕ → CoPair hN, (∀ n, (Zb n).a = armB1 n) ∧ (∀ n, (Zb n).b = armB2 n)) ∧
    (∃ Zc : ℕ → CoPair hN, (∀ n, (Zc n).a = armC1 n) ∧ (∀ n, (Zc n).b = armC2 n + 1)) :=
  ⟨exists_seq_of_step hN armA1 armA2 hbaseA hstepA,
   exists_seq_of_step hN armB1 armB2 hbaseB hstepB,
   exists_seq_of_step hN armC1 (fun n => armC2 n + 1) hbaseC hstepC⟩

end Work.ELNest
