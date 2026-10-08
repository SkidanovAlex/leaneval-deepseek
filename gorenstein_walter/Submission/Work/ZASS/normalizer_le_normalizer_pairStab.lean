/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Area ZASS: the normalizer of a nontrivial subgroup of a two-point stabilizer

Let `G` act on `X` with `ZassHyps2 G X q`: the action is faithful, `Nat.card X = q + 1`,
2-pretransitive, and every nonidentity element fixes at most two points.  For distinct
points `a b : X` write `H = G_{a,b} = pairStab G a b`.

**`normalizer_le_normalizer_pairStab`.**  If `Q ≠ ⊥` is a subgroup of `H`, then
`N_G(Q) ≤ N_G(H)`.

The mathematical content is that `H`, together with the "at most two fixed points"
condition, *determines* the unordered pair `{a,b}`: any nonidentity `q ∈ Q ≤ H` fixes `a`
and `b`, and since it fixes at most two points its full fixed-point set is exactly `{a,b}`.
For `g ∈ N_G(Q)` the conjugate `g q g⁻¹` again lies in `Q ≤ H`, so `q` fixes `g⁻¹ • a` and
`g⁻¹ • b`; these are two distinct points of the fixed-point set of `q`, hence they are `a`
and `b`.  Thus `g` preserves the pair `{a,b}`, and the setwise stabilizer of a pair is
contained in the normalizer of its pointwise stabilizer.
-/
import Mathlib
import Submission.Work.ZASS.Defs

namespace Work.ZASS

open Work.Zassenhaus

theorem normalizer_le_normalizer_pairStab {G X : Type} [Group G] [Finite G] [MulAction G X] [Finite X] {q : ℕ} (h : Work.GW2.ZassHyps2 G X q) {a b : X} (hab : a ≠ b) (hq : 5 ≤ q) {Q : Subgroup G} (hQH : Q ≤ Work.Zassenhaus.pairStab G a b) (hQ : Q ≠ ⊥) : Subgroup.normalizer (Q : Set G) ≤ Subgroup.normalizer (Work.Zassenhaus.pairStab G a b : Set G) := by
  -- A nonidentity element of `Q`.
  obtain ⟨q0, hq0Q, hq0ne⟩ : ∃ q0 : G, q0 ∈ Q ∧ q0 ≠ 1 := by
    obtain ⟨⟨q0, hq0Q⟩, hq0ne⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hQ
    exact ⟨q0, hq0Q, fun h1 => hq0ne (Subtype.ext h1)⟩
  intro g hg
  rw [Subgroup.mem_normalizer_iff] at hg ⊢
  -- `q0 ∈ H`, so `q0` fixes both `a` and `b`.
  have hq0H : q0 ∈ pairStab G a b := hQH hq0Q
  have hq0a : q0 • a = a := (mem_pairStab_iff.mp hq0H).2
  have hq0b : q0 • b = b := (mem_pairStab_iff.mp hq0H).1
  -- The conjugate `g * q0 * g⁻¹` also lies in `Q ≤ H`, hence fixes both points as well.
  have hconj : g * q0 * g⁻¹ ∈ pairStab G a b := hQH ((hg q0).1 hq0Q)
  have hconja : (g * q0 * g⁻¹) • a = a := (mem_pairStab_iff.mp hconj).2
  have hconjb : (g * q0 * g⁻¹) • b = b := (mem_pairStab_iff.mp hconj).1
  -- Consequently `q0` fixes the preimages `g⁻¹ • a` and `g⁻¹ • b`.
  have hmul_q0 : g⁻¹ * (g * q0 * g⁻¹) = q0 * g⁻¹ := by group
  have hfix (x : X) (hx : x = a ∨ x = b) : q0 • (g⁻¹ • x) = g⁻¹ • x := by
    have hconjx : (g * q0 * g⁻¹) • x = x := by
      rcases hx with rfl | rfl
      · exact hconja
      · exact hconjb
    calc q0 • (g⁻¹ • x) = (q0 * g⁻¹) • x := (mul_smul q0 g⁻¹ x).symm
      _ = (g⁻¹ * (g * q0 * g⁻¹)) • x := by rw [hmul_q0]
      _ = g⁻¹ • ((g * q0 * g⁻¹) • x) := mul_smul g⁻¹ (g * q0 * g⁻¹) x
      _ = g⁻¹ • x := by rw [hconjx]
  -- `q0 ≠ 1` fixes at most two points, and it fixes `a ≠ b`; hence its fixed-point set is
  -- exactly `{a, b}`, so `g⁻¹ • a` and `g⁻¹ • b` are `a` and `b`.
  have hcard : ({x : X | q0 • x = x} : Set X).ncard ≤ 2 := h.2.2.2.1 q0 hq0ne
  have hsub : ({a, b} : Set X) ⊆ {x : X | q0 • x = x} := by
    intro x hx
    rcases (show x = a ∨ x = b from by simpa using hx) with rfl | rfl
    · exact hq0a
    · exact hq0b
  have hF : ({a, b} : Set X) = {x : X | q0 • x = x} := by
    refine Set.eq_of_subset_of_ncard_le hsub ?_
    rw [Set.ncard_pair hab]
    exact hcard
  have ha' : g⁻¹ • a ∈ ({a, b} : Set X) := by
    rw [hF]; exact hfix a (Or.inl rfl)
  have hb' : g⁻¹ • b ∈ ({a, b} : Set X) := by
    rw [hF]; exact hfix b (Or.inr rfl)
  have hne' : g⁻¹ • a ≠ g⁻¹ • b := fun hh => hab (smul_left_cancel (g⁻¹) hh)
  have hpair : ({g⁻¹ • a, g⁻¹ • b} : Set X) = {a, b} := by
    refine Set.eq_of_subset_of_ncard_le ?_ ?_
    · intro x hx
      rcases (show x = g⁻¹ • a ∨ x = g⁻¹ • b from by simpa using hx) with rfl | rfl
      · exact ha'
      · exact hb'
    · rw [Set.ncard_pair hab, Set.ncard_pair hne']
  -- It remains to show that `g` normalizes `H`: the setwise stabilizer of `{a, b}` is
  -- contained in the normalizer of the pointwise stabilizer `H = G_{a,b}`.
  intro y
  constructor
  · intro hy
    rw [mem_pairStab_iff] at hy ⊢
    obtain ⟨hyb, hya⟩ := hy
    have hyfa : y • (g⁻¹ • a) = g⁻¹ • a := by
      rcases (show g⁻¹ • a = a ∨ g⁻¹ • a = b from by
        have hm : g⁻¹ • a ∈ ({a, b} : Set X) := by rw [← hpair]; exact Or.inl rfl
        simpa using hm) with h' | h'
      · rw [h']; exact hya
      · rw [h']; exact hyb
    have hyfb : y • (g⁻¹ • b) = g⁻¹ • b := by
      rcases (show g⁻¹ • b = a ∨ g⁻¹ • b = b from by
        have hm : g⁻¹ • b ∈ ({a, b} : Set X) := by rw [← hpair]; exact Or.inr rfl
        simpa using hm) with h' | h'
      · rw [h']; exact hya
      · rw [h']; exact hyb
    refine mem_pairStab_iff.mpr ⟨?_, ?_⟩
    · simp only [mul_smul, hyfb, smul_inv_smul]
    · simp only [mul_smul, hyfa, smul_inv_smul]
  · intro hy
    rw [mem_pairStab_iff] at hy
    obtain ⟨hyb, hya⟩ := hy
    have hmul_y : g⁻¹ * (g * y * g⁻¹) = y * g⁻¹ := by group
    have hyfa : y • (g⁻¹ • a) = g⁻¹ • a := by
      calc y • (g⁻¹ • a) = (y * g⁻¹) • a := (mul_smul y g⁻¹ a).symm
        _ = (g⁻¹ * (g * y * g⁻¹)) • a := by rw [hmul_y]
        _ = g⁻¹ • ((g * y * g⁻¹) • a) := mul_smul g⁻¹ (g * y * g⁻¹) a
        _ = g⁻¹ • a := by rw [hya]
    have hyfb : y • (g⁻¹ • b) = g⁻¹ • b := by
      calc y • (g⁻¹ • b) = (y * g⁻¹) • b := (mul_smul y g⁻¹ b).symm
        _ = (g⁻¹ * (g * y * g⁻¹)) • b := by rw [hmul_y]
        _ = g⁻¹ • ((g * y * g⁻¹) • b) := mul_smul g⁻¹ (g * y * g⁻¹) b
        _ = g⁻¹ • b := by rw [hyb]
    have hma : a ∈ ({g⁻¹ • a, g⁻¹ • b} : Set X) := by rw [hpair]; exact Or.inl rfl
    have hmb : b ∈ ({g⁻¹ • a, g⁻¹ • b} : Set X) := by rw [hpair]; exact Or.inr rfl
    refine mem_pairStab_iff.mpr ⟨?_, ?_⟩
    · rcases (show b = g⁻¹ • a ∨ b = g⁻¹ • b from by simpa using hmb) with h' | h'
      · rw [h']; exact hyfa
      · rw [h']; exact hyfb
    · rcases (show a = g⁻¹ • a ∨ a = g⁻¹ • b from by simpa using hma) with h' | h'
      · rw [h']; exact hyfa
      · rw [h']; exact hyfb

end Work.ZASS
