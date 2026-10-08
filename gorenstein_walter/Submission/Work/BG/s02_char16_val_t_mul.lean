import Mathlib
import Submission.Work.BG.S02
import Submission.Work.BG.lemma16_mod_two

/-!
# Area BG: Lemma 1.6 for an irreducible character of `H₀`, evaluated on `U` (BG §2)

`Work.BG.lemma16_mod_two` is Bender–Glauberman's Lemma 1.6 for an *arbitrary* finite group
`G`: if `t` is an involution commuting with `u` of odd order and `φ` is a virtual character
(`φ ∈ ZIrr G`), then `φ (t·u) ≡ φ u (mod 2)`.

The present file instantiates it in the §2 situation of Bender–Glauberman 1981 with
`G := ↥C.P.H0`, `t := C.t` (the unique involution of `H₀`, central in `H`) and `u ∈ U`, where
`ν` is an *irreducible* character of `H₀`:

  `ν (C.t * u) ≡ ν u  (mod 2)`.

The two inputs specific to the §2 setting are

* `C.t * C.t = 1` in `↥C.P.H0` (from `C.t_sq`) and `C.t * u = u * C.t` (from `C.t_comm_H`:
  `t` is central in `H ⊇ H₀`), and
* `u` has odd order.  This is not an extra hypothesis: an element of `U` of even order would
  have a power `w ≠ 1` of order `2`, so `w ∈ U ⊆ H₀` with `w² = 1`, and `C.inv_H0` would
  force `w = t`, contradicting `C.t_not_mem_U`.
-/

namespace Work.BG

open OddOrder.RepresentationTheory

/-- **An element of `U` has odd order** (the §2 context `C : Sec2Ctx G`).

`U ≤ H₀` is contained in the subgroup whose only involutions are `1` and `t`, and `t ∉ U`;
hence no element of `U` has even order. -/
theorem Sec2Ctx.odd_orderOf_of_mem_U {G : Type} [Group G] [Finite G] (C : Work.BG.Sec2Ctx G)
    {u : ↥C.P.H0} (hu : (u : G) ∈ C.P.U) : Odd (orderOf u) := by
  by_contra h
  rw [Nat.not_odd_iff_even] at h
  obtain ⟨k, hk⟩ := h
  have hkpos : 0 < k := by
    have hfin : IsOfFinOrder u := isOfFinOrder_of_finite u
    have := (orderOf_pos_iff).mpr hfin
    omega
  set w : ↥C.P.H0 := u ^ k with hw
  have hw2 : w ^ 2 = 1 := by
    rw [hw, ← pow_mul, show k * 2 = k + k from by ring, ← hk]
    exact pow_orderOf_eq_one u
  have hwne : w ≠ 1 := by
    intro hc
    have hdvd : orderOf u ∣ k := by
      rw [hw] at hc
      exact orderOf_dvd_iff_pow_eq_one.mpr hc
    have hle := Nat.le_of_dvd hkpos hdvd
    omega
  have hwU : (w : G) ∈ C.P.U := by
    rw [hw, Subgroup.coe_pow]
    exact C.P.U.pow_mem hu k
  have hw2G : (w : G) ^ 2 = 1 := by
    have := congrArg (fun x : ↥C.P.H0 => (x : G)) hw2
    simpa using this
  rcases C.inv_H0 (w : G) w.2 hw2G with h1 | h1
  · exact hwne (Subtype.ext h1)
  · exact C.t_not_mem_U (h1 ▸ hwU)

/-- **Bender–Glauberman 1981, Lemma 1.6, in the §2 setting, for an irreducible character
`ν` of `H₀` and `u ∈ U`**: `ν (t·u) ≡ ν u (mod 2)`.

This is `Work.BG.lemma16_mod_two` applied to the finite group `↥C.P.H0` with `t := C.t`,
the element `u` of odd order (`Sec2Ctx.odd_orderOf_of_mem_U`), and the virtual character
`(ν : ClassFunction ↥C.P.H0 ℂ) ∈ ZIrr ↥C.P.H0` (`IrreducibleCharacter.mem_ZIrr`). -/
theorem s02_char16_val_t_mul {G : Type} [Group G] [Finite G] (C : Work.BG.Sec2Ctx G) {u : ↥C.P.H0}
    (hu : (u : G) ∈ C.P.U) (ν : OddOrder.RepresentationTheory.IrreducibleCharacter ↥C.P.H0) :
    Work.BG.AlgIntModTwo
      ((ν : OddOrder.RepresentationTheory.ClassFunction ↥C.P.H0 ℂ) (C.t * u))
      ((ν : OddOrder.RepresentationTheory.ClassFunction ↥C.P.H0 ℂ) u) := by
  have ht : C.t * C.t = (1 : ↥C.P.H0) := by rw [← pow_two]; exact C.t_sq
  have hcomm : C.t * u = u * C.t := by
    apply Subtype.ext
    have h := C.t_comm_H (u : G) (C.P.H0_le_H u.2)
    simpa using h.symm
  exact lemma16_mod_two C.t u ht (C.odd_orderOf_of_mem_U hu) hcomm (ν : _) ν.2.mem_ZIrr

end Work.BG
