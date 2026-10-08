/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The split case of DS10a: reduction to the standard involution

`splitCase` (the requested lemma) is deduced from `splitCase_std` by conjugating the whole
configuration by an element `g ∈ PGL(2,q)` that moves the two fixed points `a, b` of `t` to
`0` and `∞`; then `g t g⁻¹` is an involution of `PGL(2,q)` fixing `0` and `∞`, hence equals the
standard split involution `x ↦ -x`.
-/
import Mathlib
import Submission.Work.DSTR.M110.SplitCase.StdCase

open scoped MatrixGroups LinearAlgebra.Projectivization
open OnePoint

namespace Work.DSTR.M110

open Work.AUTL2 Work.DSTR.M110.SplitAux

variable (p k : ℕ) [Fact p.Prime] [DecidableEq (GaloisField p k)]

/-- There is a point different from two given distinct points (since `|ℙ¹(F)| ≥ 6`). -/
private lemma exists_ne_ne (hp : Odd p) (hq : 5 ≤ p ^ k) (a b : P1 (GaloisField p k)) :
    ∃ c : P1 (GaloisField p k), c ≠ a ∧ c ≠ b := by
  by_contra h
  push_neg at h
  have hne : (((0 : GaloisField p k)) : P1 (GaloisField p k)) ≠
      (((1 : GaloisField p k)) : P1 (GaloisField p k)) := by
    intro hh
    exact one_ne_zero (OnePoint.coe_eq_coe.mp hh).symm
  have h0inf : (((0 : GaloisField p k)) : P1 (GaloisField p k)) ≠ (∞ : P1 (GaloisField p k)) :=
    OnePoint.coe_ne_infty 0
  have h1inf : (((1 : GaloisField p k)) : P1 (GaloisField p k)) ≠ (∞ : P1 (GaloisField p k)) :=
    OnePoint.coe_ne_infty 1
  by_cases h0a : (((0 : GaloisField p k)) : P1 (GaloisField p k)) = a
  · have h1b : (((1 : GaloisField p k)) : P1 (GaloisField p k)) = b := by
      refine h _ ?_
      intro h1a
      exact hne (h0a.trans h1a.symm)
    have hinfb : (∞ : P1 (GaloisField p k)) = b := by
      refine h _ ?_
      intro hinfa
      exact h0inf (h0a.trans hinfa.symm)
    exact h1inf (h1b.trans hinfb.symm)
  · have h0b : (((0 : GaloisField p k)) : P1 (GaloisField p k)) = b := h _ h0a
    by_cases h1a : (((1 : GaloisField p k)) : P1 (GaloisField p k)) = a
    · have hinfb : (∞ : P1 (GaloisField p k)) = b := by
        refine h _ ?_
        intro hinfa
        exact h1inf (h1a.trans hinfa.symm)
      exact h0inf (h0b.trans hinfb.symm)
    · have h1b : (((1 : GaloisField p k)) : P1 (GaloisField p k)) = b := h _ h1a
      exact hne (h0b.trans h1b.symm)

/-- **Conjugation to the standard split involution.**  An involution `t ∈ PGL(2,F)` fixing two
distinct points `a ≠ b` is conjugate by an element of `PGL(2,F)` sending `a ↦ 0`, `b ↦ ∞` to the
standard split involution `x ↦ -x`. -/
theorem exists_conj_negPerm (hp : Odd p) (hq : 5 ≤ p ^ k)
    (t : Equiv.Perm (P1 (GaloisField p k))) (htpgl : t ∈ pglImage (GaloisField p k))
    (ht2 : orderOf t = 2) (a b : P1 (GaloisField p k)) (hab : a ≠ b)
    (ha : t a = a) (hb : t b = b) :
    ∃ g ∈ pglImage (GaloisField p k), g a = (((0 : GaloisField p k)) : P1 (GaloisField p k)) ∧
      g b = (∞ : P1 (GaloisField p k)) ∧ g * t * g⁻¹ = negPerm (GaloisField p k) := by
  obtain ⟨c, hca, hcb⟩ := exists_ne_ne p k hp hq a b
  have hz : (((0 : GaloisField p k)) : P1 (GaloisField p k)) ≠ (∞ : P1 (GaloisField p k)) :=
    OnePoint.coe_ne_infty 0
  have ho : (∞ : P1 (GaloisField p k)) ≠ (((1 : GaloisField p k)) : P1 (GaloisField p k)) :=
    (OnePoint.coe_ne_infty 1).symm
  have hzo : (((0 : GaloisField p k)) : P1 (GaloisField p k)) ≠
      (((1 : GaloisField p k)) : P1 (GaloisField p k)) := by
    intro hh
    exact one_ne_zero (OnePoint.coe_eq_coe.mp hh).symm
  obtain ⟨gm, hg1, hg2, _⟩ := Work.AUTL2.Mobius.perm_three_transitive (GaloisField p k)
    a b c (((0 : GaloisField p k)) : P1 (GaloisField p k)) (∞ : P1 (GaloisField p k))
    (((1 : GaloisField p k)) : P1 (GaloisField p k)) hab (Ne.symm hca) (Ne.symm hcb) hz hzo ho
  set g : Equiv.Perm (P1 (GaloisField p k)) := pglHom (GaloisField p k) gm with hgdef
  have hgmem : g ∈ pglImage (GaloisField p k) := ⟨gm, rfl⟩
  have hgpg : g ∈ pgammaL (GaloisField p k) := (le_sup_left : _ ≤ pgammaL _) hgmem
  have ha' : g a = (((0 : GaloisField p k)) : P1 (GaloisField p k)) := hg1
  have hb' : g b = (∞ : P1 (GaloisField p k)) := hg2
  refine ⟨g, hgmem, ha', hb', ?_⟩
  set t' : Equiv.Perm (P1 (GaloisField p k)) := g * t * g⁻¹ with ht'def
  have ht'pgl : t' ∈ pglImage (GaloisField p k) :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ hgmem htpgl) (Subgroup.inv_mem _ hgmem)
  have ht'0 : t' (((0 : GaloisField p k)) : P1 (GaloisField p k)) =
      (((0 : GaloisField p k)) : P1 (GaloisField p k)) := by
    have h1 : g⁻¹ (((0 : GaloisField p k)) : P1 (GaloisField p k)) = a := by
      rw [← ha']; exact Equiv.symm_apply_apply g a
    rw [ht'def, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, h1, ha, ha']
  have ht'inf : t' (∞ : P1 (GaloisField p k)) = ∞ := by
    have h1 : g⁻¹ (∞ : P1 (GaloisField p k)) = b := by
      rw [← hb']; exact Equiv.symm_apply_apply g b
    rw [ht'def, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, h1, hb, hb']
  have ht'tor : t' ∈ torSub (GaloisField p k) :=
    pglImage_fixing_zero_infty (GaloisField p k) t' ht'pgl ht'0 ht'inf
  obtain ⟨u, hu⟩ := MonoidHom.mem_range.mp ht'tor
  -- `t' * t' = 1`
  have ht2sq : t * t = 1 := by rw [← pow_two, ← ht2, pow_orderOf_eq_one]
  have ht'sq : t' * t' = 1 := by
    rw [ht'def]
    rw [show (g * t * g⁻¹) * (g * t * g⁻¹) = g * (t * t) * g⁻¹ by group, ht2sq]
    group
  have ht'ne : t' ≠ 1 := by
    intro h1
    have h2 : t = 1 := by
      rw [ht'def] at h1
      calc t = g⁻¹ * (g * t * g⁻¹) * g := by group
        _ = g⁻¹ * 1 * g := by rw [h1]
        _ = 1 := by group
    rw [h2, orderOf_one] at ht2
    exact absurd ht2 (by norm_num)
  -- `u * u = 1` and `u ≠ 1`
  have hu2 : u * u = 1 := by
    apply smulHom_injective (GaloisField p k)
    rw [map_mul, map_one, hu]
    exact ht'sq
  have hune : u ≠ 1 := by
    intro h1
    exact ht'ne (by rw [← hu, h1, map_one])
  have hupm : u = 1 ∨ u = -1 := by
    have h : ((u : GaloisField p k) - 1) * ((u : GaloisField p k) + 1) = 0 := by
      have h2 : (u : GaloisField p k) ^ 2 = 1 := by
        have h2' := congrArg (fun z : (GaloisField p k)ˣ => (z : GaloisField p k)) hu2
        rw [pow_two]
        simpa using h2'
      linear_combination h2
    rcases mul_eq_zero.mp h with h1 | h1
    · left; exact Units.ext (sub_eq_zero.mp h1)
    · right; exact Units.ext (eq_neg_of_add_eq_zero_left h1)
  have hue : u = -1 := by
    rcases hupm with h1 | h1
    · exact absurd h1 hune
    · exact h1
  rw [← hu, hue]
  exact negPerm_eq_smulHom (GaloisField p k)

end Work.DSTR.M110
