import Mathlib.LinearAlgebra.DFinsupp
import Mathlib.Algebra.CharP.Defs
import Mathlib.Analysis.Real.Sqrt
import Submission.Work.BoseB7.boseDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseB7.bCCR` — the canonical commutation relations on the Fock space

The bosonic Fock space `boseH Mode` (`Work.BoseB7.boseDefs`) carries the ladder
operators `bCre i` (`a_i†`) and `bAnn i` (`a_i`), defined by

  `bCre i |m⟩ = √(m_i + 1)·|inc i m⟩`, `bAnn i |m⟩ = √(m_i)·|dec i m⟩`

on the occupation-number basis `|m⟩`.  This file proves the resulting canonical
commutation relation

  `[bAnn i, bCre j] = bAnn i ∘ bCre j - bCre j ∘ bAnn i = δ_{ij} · 1`.

## Contents

* `bCre_apply'` — pointwise action of `bCre`: `(bCre i Ψ) m = √(occ i m)·Ψ(dec i m)`.
* `bAnn_apply'` — pointwise action of `bAnn`: `(bAnn i Ψ) m = √(occ i m + 1)·Ψ(inc i m)`.
* `bCCR` — the canonical commutation relation.

The two pointwise formulas are proved by `Finsupp.induction_linear`: it suffices to
check the linear identity `bCre i Ψ = (fun m => √(occ i m)·Ψ(dec i m))` on the
occupation-number basis vectors `Finsupp.single μ r`, where it reduces to the
elementary arithmetic of `inc`/`dec`/`occ` from `boseDefs`.  The commutation
relation then follows by evaluating both sides at an occupation vector `m` and
splitting into `i = j` (where the two `√` factors collapse by `occ_inc_self`,
`dec_inc_self`, `occ_dec_self`, `inc_dec_self`) and `i ≠ j` (where the modes are
independent: `occ_inc_ne`, `occ_dec_ne`, `inc_dec_comm`).
-/

noncomputable section

open scoped BigOperators

namespace Work.BoseB7

universe u v

/-- The pointwise action of the creation operator on the occupation-number basis:
`(bCre i Ψ) m = √(occ i m) · Ψ (dec i m)`. -/
lemma bCre_apply' {Mode : Type*} [DecidableEq Mode] (i : Mode) (Ψ : boseH Mode)
    (m : occIdx Mode) :
    bCre i Ψ m = Real.sqrt (occ i m) * Ψ (dec i m) := by
  induction Ψ using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg =>
      rw [map_add, Finsupp.add_apply, hf, hg, Finsupp.add_apply, mul_add]
  | single μ r =>
      rw [bCre, Finsupp.lsum_single]
      simp only [LinearMap.smul_apply, Finsupp.lsingle_apply, Finsupp.smul_apply,
        Finsupp.single_apply]
      by_cases h : inc i μ = m
      · have hdec : μ = dec i m := by rw [← h, dec_inc_self]
        have hocc : occ i m = occ i μ + 1 := by rw [← h, occ_inc_self]
        rw [if_pos h, if_pos hdec, hocc, Nat.cast_add, Nat.cast_one, smul_eq_mul]
      · rw [if_neg h]
        by_cases h2 : μ = dec i m
        · rw [if_pos h2]
          have hocc : occ i m = 0 := by
            by_contra hc
            have hpos : 0 < occ i m := Nat.pos_of_ne_zero hc
            exact h (by rw [h2, inc_dec_self m hpos])
          rw [hocc]; simp
        · rw [if_neg h2]; simp

/-- The pointwise action of the annihilation operator on the occupation-number
basis: `(bAnn i Ψ) m = √(occ i m + 1) · Ψ (inc i m)`. -/
lemma bAnn_apply' {Mode : Type*} [DecidableEq Mode] (i : Mode) (Ψ : boseH Mode)
    (m : occIdx Mode) :
    bAnn i Ψ m = Real.sqrt ((occ i m : ℝ) + 1) * Ψ (inc i m) := by
  induction Ψ using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg =>
      rw [map_add, Finsupp.add_apply, hf, hg, Finsupp.add_apply, mul_add]
  | single μ r =>
      rw [bAnn, Finsupp.lsum_single]
      simp only [LinearMap.smul_apply, Finsupp.lsingle_apply, Finsupp.smul_apply,
        Finsupp.single_apply]
      by_cases h : μ = inc i m
      · have hdec : dec i μ = m := by rw [h, dec_inc_self]
        have hocc : occ i μ = occ i m + 1 := by rw [h, occ_inc_self]
        rw [if_pos hdec, if_pos h, hocc, Nat.cast_add, Nat.cast_one, smul_eq_mul]
      · rw [if_neg h]
        by_cases h2 : dec i μ = m
        · rw [if_pos h2]
          have hocc : occ i μ = 0 := by
            by_contra hc
            have hpos : 0 < occ i μ := Nat.pos_of_ne_zero hc
            exact h (by rw [← inc_dec_self μ hpos, h2])
          rw [hocc]; simp
        · rw [if_neg h2]; simp

/-- **The canonical commutation relations** of the Fock ladder operators:
`bAnn i ∘ bCre j = bCre j ∘ bAnn i + δ_{ij} • 1`. -/
theorem bCCR {Mode : Type*} [DecidableEq Mode] (i j : Mode) :
    Work.BoseB7.bAnn i ∘ₗ Work.BoseB7.bCre j
      = Work.BoseB7.bCre j ∘ₗ Work.BoseB7.bAnn i
        + (if i = j then (1 : ℝ) else 0) •
          (1 : Work.BoseB7.boseH Mode →ₗ[ℝ] Work.BoseB7.boseH Mode) := by
  apply LinearMap.ext
  intro Ψ
  apply Finsupp.ext
  intro m
  simp only [LinearMap.comp_apply, LinearMap.add_apply, LinearMap.smul_apply,
    Module.End.one_apply, Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul]
  rw [bAnn_apply' i (bCre j Ψ) m, bCre_apply' j Ψ (inc i m),
    bCre_apply' j (bAnn i Ψ) m, bAnn_apply' i Ψ (dec j m)]
  by_cases hij : i = j
  · subst hij
    rw [if_pos rfl, one_mul, dec_inc_self]
    have hA : Real.sqrt ((occ i (inc i m) : ℝ)) = Real.sqrt ((occ i m : ℝ) + 1) := by
      rw [occ_inc_self, Nat.cast_add, Nat.cast_one]
    rw [hA]
    by_cases h0 : occ i m = 0
    · rw [h0]; simp
    · have hpos : 0 < occ i m := Nat.pos_of_ne_zero h0
      have hB : Real.sqrt ((occ i (dec i m) : ℝ) + 1) = Real.sqrt ((occ i m : ℝ)) := by
        rw [← Nat.cast_one, ← Nat.cast_add, occ_dec_self m hpos]
      rw [hB, inc_dec_self m hpos]
      have h1 : Real.sqrt ((occ i m : ℝ) + 1) * Real.sqrt ((occ i m : ℝ) + 1)
          = (occ i m : ℝ) + 1 := by
        rw [← sq, Real.sq_sqrt (by positivity)]
      have h2 : Real.sqrt ((occ i m : ℝ)) * Real.sqrt ((occ i m : ℝ))
          = (occ i m : ℝ) := by
        rw [← sq, Real.sq_sqrt (by positivity)]
      rw [← mul_assoc, h1, ← mul_assoc, h2]
      ring
  · rw [if_neg hij, zero_mul, add_zero]
    rw [occ_inc_ne (Ne.symm hij) m, ← inc_dec_comm (Ne.symm hij) m, occ_dec_ne hij m]
    ring

end Work.BoseB7
