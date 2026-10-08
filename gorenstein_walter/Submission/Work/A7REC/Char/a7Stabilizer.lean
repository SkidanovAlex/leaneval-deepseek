/-
Area `A7REC`, file `Char/a7Stabilizer.lean`: **C3b** of the pass-8 contract
(`Submission/Work/_design_gw/Core8.lean` §1, `A7StabilizerProp`; Suzuki 1959 p. 270).

The stabilizer `H` of the vector `m` provided by C3a contains `U` and `S'`, and `7 ∣ [G : H]`.

The whole content is the observation that an element of order `7` has **no** nonzero fixed
vector.  Indeed, for `x` of order `7`, let `Z = ⟨x⟩` (a group of order `7`) and restrict `ρ` to
`Z`: the averaging projection `(1/7) ∑_{w ∈ Z} ρ(w)` realises `Fix(ρ|_Z)` as the image of a
projection, so

  `∑_{w ∈ Z} trace ρ(w) = 7 · dim Fix(ρ|_Z)`.

Rep6 gives `trace ρ(1) = dim W = 6` and `trace ρ(w) = -1` for the six nonidentity `w ∈ Z`, so the
sum is `6 − 6 = 0` and `dim Fix(ρ|_Z) = 0`.  Hence no nonzero `m` is fixed by `x`.

Now take `H = {g | ρ g m = m}`.  It contains `U` and `S'` by hypothesis, and it has no element of
order `7` (that element would fix `m`).  By Cauchy, `7 ∤ |H|`; since `|G| = 2520 = 7 · 360`, the
identity `|H| · [G : H] = 2520` forces `7 ∣ [G : H]`.

The character-theoretic input is `OddOrder.RepresentationTheory.sum_character_eq_card_mul_finrank_invariants`
(the same lemma used elsewhere in the workspace for the Suzuki/TI computations).
-/
import Mathlib
import Submission.Work.A7REC.Excl
import Submission.OddOrder.GroupTheory.RepresentationTheory.SumCharacterInvariants

namespace Work.A7REC.Char

open Subgroup

/-- The subgroup of elements fixing the vector `m` under the representation `ρ`. -/
def fixedSubgroup {G W : Type*} [Group G] [AddCommGroup W] [Module ℂ W]
    (ρ : Representation ℂ G W) (m : W) : Subgroup G where
  carrier := {g | ρ g m = m}
  one_mem' := by simp
  mul_mem' := by
    intro a b ha hb
    show ρ (a * b) m = m
    rw [map_mul, Module.End.mul_apply]
    show ρ a (ρ b m) = m
    rw [hb, ha]
  inv_mem' := by
    intro a ha
    show ρ a⁻¹ m = m
    have h : ρ (a⁻¹ * a) m = ρ a⁻¹ m := by
      rw [map_mul, Module.End.mul_apply]
      exact congrArg (ρ a⁻¹) ha
    rw [inv_mul_cancel, map_one, Module.End.one_apply] at h
    exact h.symm

/-- **An element of order `7` has no nonzero fixed vector.**  If `ρ` has degree `6` and
`trace ρ(y) = -1` for every `y` of order `7`, then `ρ x m = m` forces `m = 0` for `x` of order
`7`.  The averaging projection onto `Fix(ρ|_⟨x⟩)` gives
`∑_{w ∈ ⟨x⟩} trace ρ(w) = 7 · dim Fix(ρ|_⟨x⟩)`, and the left-hand side is `6 − 6 = 0`. -/
theorem eq_zero_of_rho_eq_self_of_orderOf_eq_seven
    {G W : Type*} [Group G] [Finite G] [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (ρ : Representation ℂ G W) (x : G) (hx : orderOf x = 7)
    (htr : ∀ y : G, orderOf y = 7 → LinearMap.trace ℂ W (ρ y) = -1)
    (hfin : Module.finrank ℂ W = 6) {m : W} (hm : ρ x m = m) : m = 0 := by
  classical
  let Z : Subgroup G := Subgroup.zpowers x
  haveI : Fintype Z := Fintype.ofFinite _
  let ρZ : Representation ℂ Z W := ρ.comp Z.subtype
  have hcardZ : Fintype.card Z = 7 := by
    rw [← Nat.card_eq_fintype_card, show Nat.card Z = orderOf x from Nat.card_zpowers x, hx]
  haveI : Invertible (Fintype.card Z : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr (by rw [hcardZ]; norm_num))
  -- `∑_{w ∈ Z} trace ρ(w) = 7 · dim Fix(ρ|_Z)`.
  have hsum := OddOrder.RepresentationTheory.sum_character_eq_card_mul_finrank_invariants ρZ
  -- The six nonidentity elements of `Z` have order `7`, hence trace `-1`.
  have hterm : ∀ w : Z, w ≠ 1 → ρZ.character w = -1 := by
    intro w hw
    have hmem : (w : G) ∈ Subgroup.zpowers x := w.2
    have hdvd : orderOf (w : G) ∣ 7 := by
      rw [← hx]; exact orderOf_dvd_of_mem_zpowers hmem
    have hne1 : (w : G) ≠ 1 := fun h => hw (Subtype.ext h)
    have horder : orderOf (w : G) = 7 := by
      rcases (Nat.dvd_prime Nat.prime_seven).mp hdvd with h | h
      · exact absurd (orderOf_eq_one_iff.mp h) hne1
      · exact h
    exact htr _ horder
  -- The sum collapses to `6 + 6 · (-1) = 0`.
  have hLHS : ∑ w : Z, ρZ.character w = 0 := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (1 : Z))]
    rw [Finset.sum_congr rfl (fun w hw => hterm w (Finset.ne_of_mem_erase hw))]
    rw [Representation.char_one, hfin]
    rw [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, hcardZ]
    simp
  have hzero : (Module.finrank ℂ ρZ.invariants : ℂ) = 0 := by
    have h := hsum
    rw [hLHS, hcardZ] at h
    have h7 : (7 : ℂ) ≠ 0 := by norm_num
    exact (mul_eq_zero.mp h.symm).resolve_left h7
  have hfin0 : Module.finrank ℂ ρZ.invariants = 0 := Nat.cast_eq_zero.mp hzero
  have hbot : ρZ.invariants = ⊥ := Submodule.finrank_eq_zero.mp hfin0
  -- `m` is fixed by `x`, so it lies in the (trivial) invariants of `ρ|_Z`.
  have hle : Subgroup.zpowers x ≤ fixedSubgroup ρ m := Subgroup.zpowers_le.mpr hm
  have hmZ : m ∈ ρZ.invariants := by
    rw [Representation.mem_invariants]
    intro w
    exact hle w.2
  rw [hbot] at hmZ
  simpa using hmZ

/-- **C3b** (`A7StabilizerProp`): the stabilizer of `m` contains `U` and `S'` and has index
divisible by `7`. -/
theorem a7Stabilizer : Work.A7REC.A7StabilizerProp := by
  intro G _ _ S z U V W _ _ _ ρ S' m hyps hρ hm0 hmU hmS'
  obtain ⟨hfin, _hz, _hU, h7⟩ := hρ
  have hcardG : Nat.card G = 2520 := hyps.2.1
  refine ⟨fixedSubgroup ρ m, ?_, ?_, ?_⟩
  · intro u hu
    exact hmU u hu
  · intro x hx
    exact hmS' x hx
  · -- `H` has no element of order `7`, since such an element would fix `m ≠ 0`.
    have hnodvd : ¬ 7 ∣ Nat.card (fixedSubgroup ρ m) := by
      intro hdvd
      haveI : Fact (Nat.Prime 7) := ⟨Nat.prime_seven⟩
      obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' (G := fixedSubgroup ρ m) 7 hdvd
      have hog : orderOf (g : G) = 7 := by rw [Subgroup.orderOf_coe, hg]
      have hfix : ρ (g : G) m = m := g.2
      exact hm0 (eq_zero_of_rho_eq_self_of_orderOf_eq_seven ρ (g : G) hog h7 hfin hfix)
    -- Lagrange: `|H| · [G : H] = 2520 = 7 · 360`.
    have hmul : Nat.card (fixedSubgroup ρ m) * (fixedSubgroup ρ m).index = 2520 := by
      rw [Subgroup.card_mul_index, hcardG]
    have hdvd : 7 ∣ Nat.card (fixedSubgroup ρ m) * (fixedSubgroup ρ m).index := by
      rw [hmul]; norm_num
    rcases (Nat.prime_seven.dvd_mul.mp hdvd) with h | h
    · exact absurd h hnodvd
    · exact h

end Work.A7REC.Char
