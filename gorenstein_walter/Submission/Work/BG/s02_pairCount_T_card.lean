import Mathlib
import Submission.Work.BG.S02
import Submission.Work.BG.s02_l22c1Defs

/-!
# Area BG: the two pair counts on `T` agree (BG 2.2, case one, p. 205)

This file proves `Work.BG.s02_pairCount_T_card`, the combinatorial heart of
Bender–Glauberman 1981, Lemma 2.2, first case:

> for `h ∈ T = H₀ ∖ U`, the number of pairs `(x,y) ∈ t^G × t^G` with `x*y = h` equals the
> number of pairs of involutions `x, y ∈ H ∖ H₀` with `x*y = h`.

The two filtered pair sets are `Work.BG.pairSet (Work.BG.tClass C) h` (pairs inside `G`) and
`Work.BG.pairSet (Work.BG.XH C) h` (pairs inside `H = C_G(t)`), and the bijection between them
is the identity on the underlying elements; everything is in the two membership statements,
proved here from `Sec2Ctx` alone:

* **forward** (`Work.BG.s02pc_pair_mem_of_conj`): if `x, y` are conjugate to `t` and
  `x*y = h ∈ T` then `x, y ∈ H ∖ H₀` and `x² = y² = 1`.  Since `x² = y² = 1`, one has
  `x * h * x⁻¹ = h⁻¹` and `y * h * y⁻¹ = h⁻¹`; with `h⁻¹ ∈ T` the TI condition
  (`Hyp12.mem_H_of_conj_mem`, `N_G(T) = H`) gives `x, y ∈ H`.  If `x ∈ H₀` then, `H₀` having
  the single involution `t` (`Sec2Ctx.inv_H0`), `x = t`, so `y = x⁻¹h ∈ H₀` is an involution
  `≠ 1`, hence `y = t = x` and `h = x*y = 1 ∈ U`, contradiction; symmetrically for `y`.
* **inverse** (`Work.BG.s02pc_pairSet_tClass_of_mem_XH`): an element of `XH C` is an involution
  of `G` which is not `1` (as `1 ∈ H₀`), hence conjugate to `t` by `Sec2Ctx.one_class`.

The bijection itself is the `Equiv` `Work.BG.s02pc_pairEquiv`, and the count follows from
`Fintype.card_congr` and `Fintype.card_coe`.

This file deliberately does **not** import `Submission.Work.BG.s02_involutionPair` (which still
contains a `sorry`), so that nothing here depends on `sorryAx`; the TI argument is reproduced
inline in the form needed by the pair count.
-/

namespace Work.BG

open Subgroup

/-! ## 1. Elementary facts about the class of `t` -/

/-- An element conjugate to `1` is `1`. -/
theorem s02pc_isConj_one_eq_one {G : Type} [Group G] {a : G} (h : IsConj a 1) : a = 1 := by
  obtain ⟨c, hc⟩ := isConj_iff.mp h
  have h3 : c⁻¹ * (c * a * c⁻¹) * c = 1 := by rw [hc]; group
  rw [← h3]
  group

/-- `t ≠ 1`: `t ∉ U` while `1 ∈ U`. -/
theorem s02pc_t_ne_one {G : Type} [Group G] [Finite G] (C : Sec2Ctx G) :
    (C.t : G) ≠ 1 := by
  intro h1
  exact C.t_not_mem_U (h1 ▸ C.P.U.one_mem)

/-- `t * t = 1` in `G` (`C.t_sq` coerced from `H₀`). -/
theorem s02pc_t_mul_self {G : Type} [Group G] [Finite G] (C : Sec2Ctx G) :
    (C.t : G) * (C.t : G) = 1 := by
  have := congrArg (fun a : ↥C.P.H0 => (a : G)) C.t_sq
  simpa [pow_two] using this

/-- Every conjugate of `t` is an involution. -/
theorem s02pc_conj_t_sq {G : Type} [Group G] [Finite G] (C : Sec2Ctx G) {x : G}
    (h : IsConj x (C.t : G)) : x ^ 2 = 1 := by
  have ht : (C.t : G) ^ 2 = 1 := by rw [pow_two, s02pc_t_mul_self C]
  have h2 : IsConj (x ^ 2) 1 := by
    rw [← ht]
    exact IsConj.pow 2 h
  exact s02pc_isConj_one_eq_one h2

/-- A conjugate of `t` is `≠ 1` (`t ≠ 1`). -/
theorem s02pc_conj_t_ne_one {G : Type} [Group G] [Finite G] (C : Sec2Ctx G) {x : G}
    (h : IsConj x (C.t : G)) : x ≠ 1 := by
  intro h1
  obtain ⟨c, hc⟩ := isConj_iff.mp (h1 ▸ h)
  simp only [mul_one] at hc
  exact s02pc_t_ne_one C (by simpa using hc.symm)

/-- Membership in the `G`-class `t^G` of `t`. -/
theorem s02pc_mem_tClass {G : Type} [Group G] [Finite G] [Fintype G] (C : Sec2Ctx G) {x : G} :
    x ∈ tClass C ↔ IsConj x (C.t : G) := by
  classical
  simp [tClass]

/-! ## 2. The TI step: both factors of a pair with product in `T` lie in `H ∖ H₀` -/

/-- **The combinatorial heart of BG 2.2, case one.**  If `x` and `y` are involutions of `G`
conjugate to `t` (so `≠ 1`) with `x * y = h ∈ T = H₀ ∖ U`, then `x` and `y` both lie in
`H = N_G(T)` and outside `H₀`, and both are involutions.

Both `x` and `y` invert `h` (`x h x⁻¹ = (xy)⁻¹ = h⁻¹`, and likewise for `y`), so `h⁻¹ ∈ T`
and the TI condition give `x, y ∈ H`.  If `x ∈ H₀`, then `x = t` (the only involution of
`H₀`), `y = x⁻¹h ∈ H₀` is an involution `≠ 1`, hence `y = t = x` and `h = 1 ∈ U`, which is
absurd; the argument for `y ∈ H₀` is symmetric. -/
theorem s02pc_pair_mem_of_conj {G : Type} [Group G] [Finite G]
    (C : Sec2Ctx G)
    (h : ↥C.P.H) (hh : (h : G) ∈ Tset C.P.H0 C.P.U)
    {x y : G} (hx : IsConj x (C.t : G)) (hy : IsConj y (C.t : G)) (hxy : x * y = (h : G)) :
    x ∈ C.P.H ∧ x ∉ C.P.H0 ∧ x ^ 2 = 1 ∧ y ∈ C.P.H ∧ y ∉ C.P.H0 ∧ y ^ 2 = 1 := by
  have hx2 : x ^ 2 = 1 := s02pc_conj_t_sq C hx
  have hy2 : y ^ 2 = 1 := s02pc_conj_t_sq C hy
  have hx2' : x * x = 1 := by rwa [pow_two] at hx2
  have hy2' : y * y = 1 := by rwa [pow_two] at hy2
  have hxinv : x⁻¹ = x := inv_eq_of_mul_eq_one_left hx2'
  have hyinv : y⁻¹ = y := inv_eq_of_mul_eq_one_left hy2'
  have hhH0 : (h : G) ∈ C.P.H0 := hh.1
  have hhU : (h : G) ∉ C.P.U := hh.2
  -- `h⁻¹ ∈ T`
  have hh_invT : (h : G)⁻¹ ∈ Tset C.P.H0 C.P.U :=
    ⟨C.P.H0.inv_mem hhH0, fun hc => hhU (C.P.U.inv_mem_iff.mp hc)⟩
  -- `x` and `y` invert `h`
  have hxsq : x * (h : G) * x⁻¹ = (h : G)⁻¹ := by
    have h1 : x * (h : G) * x⁻¹ = (x * x) * (y * x⁻¹) := by rw [← hxy]; group
    rw [h1, hx2', one_mul, hxinv, ← hxy, mul_inv_rev, hxinv, hyinv]
  have hysq : y * (h : G) * y⁻¹ = (h : G)⁻¹ := by
    have h1 : y * (h : G) * y⁻¹ = (y * x) * (y * y⁻¹) := by rw [← hxy]; group
    rw [h1, mul_inv_cancel y, mul_one, ← hxy, mul_inv_rev, hxinv, hyinv]
  -- hence `x, y ∈ H` by TI / `N_G(T) = H`
  have hxH : x ∈ C.P.H := C.P.mem_H_of_conj_mem hh (hxsq ▸ hh_invT)
  have hyH : y ∈ C.P.H := C.P.mem_H_of_conj_mem hh (hysq ▸ hh_invT)
  have hxtnt : x ≠ (1 : G) := s02pc_conj_t_ne_one C hx
  have hytnt : y ≠ (1 : G) := s02pc_conj_t_ne_one C hy
  -- `x ∉ H₀`
  have hx_notH0 : x ∉ C.P.H0 := by
    intro hxH0
    have hxt : x = (C.t : G) := (C.inv_H0 x hxH0 hx2).resolve_left hxtnt
    have hyH0 : y ∈ C.P.H0 := by
      have hy : y = x⁻¹ * (h : G) := by rw [← hxy]; group
      rw [hy]
      exact C.P.H0.mul_mem (C.P.H0.inv_mem hxH0) hhH0
    have hyt : y = (C.t : G) := (C.inv_H0 y hyH0 hy2).resolve_left hytnt
    have h1 : (h : G) = 1 := by
      rw [← hxy, hxt, hyt, s02pc_t_mul_self C]
    exact hhU (h1 ▸ C.P.U.one_mem)
  -- `y ∉ H₀`
  have hy_notH0 : y ∉ C.P.H0 := by
    intro hyH0
    have hyt : y = (C.t : G) := (C.inv_H0 y hyH0 hy2).resolve_left hytnt
    have hxH0 : x ∈ C.P.H0 := by
      have hx' : x = (h : G) * y⁻¹ := by rw [← hxy]; group
      rw [hx']
      exact C.P.H0.mul_mem hhH0 (C.P.H0.inv_mem hyH0)
    have hxt : x = (C.t : G) := (C.inv_H0 x hxH0 hx2).resolve_left hxtnt
    have h1 : (h : G) = 1 := by
      rw [← hxy, hxt, hyt, s02pc_t_mul_self C]
    exact hhU (h1 ▸ C.P.U.one_mem)
  exact ⟨hxH, hx_notH0, hx2, hyH, hy_notH0, hy2⟩

/-! ## 3. The inverse direction: involutions of `H ∖ H₀` lie in `t^G` -/

/-- A member of `XH C` (an involution of `H` outside `H₀`) is an involution of `G` different
from `1` (since `1 ∈ H₀`), hence conjugate to `t` by the one-class hypothesis; therefore a
pair in `pairSet (XH C) h`, viewed in `G`, belongs to `pairSet (tClass C) h`. -/
theorem s02pc_pairSet_tClass_of_mem_XH {G : Type} [Group G] [Finite G] [Fintype G]
    (C : Sec2Ctx G) [Fintype ↥C.P.H]
    (h : ↥C.P.H) {z w : ↥C.P.H} (hz : z ∈ XH C) (hw : w ∈ XH C)
    (hzw : z * w = h) :
    ((z : G), (w : G)) ∈ pairSet (tClass C) (h : G) := by
  rw [mem_pairSet]
  obtain ⟨hzH0, hz2⟩ := mem_XH.mp hz
  obtain ⟨hwH0, hw2⟩ := mem_XH.mp hw
  have hz2G : (z : G) ^ 2 = 1 := by
    have := congrArg (fun a : ↥C.P.H => (a : G)) hz2
    simpa using this
  have hw2G : (w : G) ^ 2 = 1 := by
    have := congrArg (fun a : ↥C.P.H => (a : G)) hw2
    simpa using this
  have hzwG : (z : G) * (w : G) = (h : G) := by
    have := congrArg (fun a : ↥C.P.H => (a : G)) hzw
    simpa using this
  refine ⟨?_, ?_, hzwG⟩
  · rw [s02pc_mem_tClass]
    exact C.one_class (z : G) hz2G (fun h1 => hzH0 (h1 ▸ C.P.H0.one_mem))
  · rw [s02pc_mem_tClass]
    exact C.one_class (w : G) hw2G (fun h1 => hwH0 (h1 ▸ C.P.H0.one_mem))

/-! ## 4. The bijection between the two pair sets and the count -/

/-- The identity on the underlying elements is a bijection from the pairs of conjugates of `t`
with product `h` to the pairs of involutions of `H ∖ H₀` with product `h`: both directions are
the membership statements of §§2–3. -/
noncomputable def s02pc_pairEquiv {G : Type} [Group G] [Finite G] [Fintype G]
    (C : Sec2Ctx G) [Fintype ↥C.P.H]
    (h : ↥C.P.H) (hh : (h : G) ∈ Tset C.P.H0 C.P.U) :
    {p : G × G // p ∈ pairSet (tClass C) (h : G)} ≃
      {q : ↥C.P.H × ↥C.P.H // q ∈ pairSet (XH C) h} where
  toFun := fun p => by
    obtain ⟨⟨x, y⟩, hp⟩ := p
    obtain ⟨hxt, hyt, hxy⟩ := mem_pairSet.mp hp
    rw [s02pc_mem_tClass] at hxt hyt
    obtain ⟨hxH, hxH0, hx2, hyH, hyH0, hy2⟩ := s02pc_pair_mem_of_conj C h hh hxt hyt hxy
    refine ⟨(⟨x, hxH⟩, ⟨y, hyH⟩), ?_⟩
    rw [mem_pairSet]
    refine ⟨?_, ?_, ?_⟩
    · rw [mem_XH]
      exact ⟨hxH0, by apply Subtype.ext; simpa using hx2⟩
    · rw [mem_XH]
      exact ⟨hyH0, by apply Subtype.ext; simpa using hy2⟩
    · exact Subtype.ext (by simpa using hxy)
  invFun := fun q => by
    obtain ⟨⟨z, w⟩, hq⟩ := q
    obtain ⟨hzX, hwX, hzw⟩ := mem_pairSet.mp hq
    exact ⟨((z : G), (w : G)), s02pc_pairSet_tClass_of_mem_XH C h hzX hwX hzw⟩
  left_inv := fun p => by
    obtain ⟨⟨x, y⟩, hp⟩ := p
    rfl
  right_inv := fun q => by
    obtain ⟨⟨z, w⟩, hq⟩ := q
    rfl

/-- **The pair counts of `t^G` and of the involutions of `H ∖ H₀` agree on `T`.**
For `h ∈ T = H₀ ∖ U` the number of pairs `(x,y) ∈ t^G × t^G` with `x*y = h` equals the number
of pairs of involutions `x,y ∈ H ∖ H₀` with `x*y = h`.

This is the combinatorial heart of BG 2.2, case one (p. 205): if `x, y ∈ G` are involutions
(so conjugate to `t`, `Sec2Ctx.one_class`, hence `≠ 1`) with `x*y ∈ T`, then `x h x⁻¹ = h⁻¹ ∈ T`
and `y h y⁻¹ = h⁻¹ ∈ T`, so `x, y ∈ N_G(T) = H` (TI property) and `x, y ∉ H₀` (otherwise `x = t`
by `Sec2Ctx.inv_H0` and then `y ∈ H₀`, `y = t`, `xy = 1 ∉ T`).  The resulting bijection between
the two filtered pair sets is `(x,y) ↦ (⟨x, _⟩, ⟨y, _⟩)` with inverse `(x,y) ↦ ((x : G), (y : G))`.

IMPORTANT: do NOT import `Submission.Work.BG.s02_involutionPair` and do NOT use
`Work.BG.InvolutionPairProp` (that file still contains a `sorry`, so importing it would make
this statement depend on `sorryAx`).  Prove the `x, y ∈ H ∖ H₀` step inline from `Sec2Ctx`
(`C.P.TI`, `C.P.mem_H_of_conj_mem`, `C.inv_H0`, `C.t_sq`, `C.t_not_mem_U`, `C.one_class`). -/
theorem s02_pairCount_T_card {G : Type} [Group G] [Finite G] [Fintype G]
    (C : Work.BG.Sec2Ctx G) [Fintype ↥C.P.H]
    (h : ↥C.P.H) (hh : (h : G) ∈ Work.BG.Tset C.P.H0 C.P.U) :
    (Work.BG.pairSet (Work.BG.tClass C) (h : G)).card =
      (Work.BG.pairSet (Work.BG.XH C) h).card := by
  calc (pairSet (tClass C) (h : G)).card
      = Fintype.card {p : G × G // p ∈ pairSet (tClass C) (h : G)} :=
        (Fintype.card_coe _).symm
    _ = Fintype.card {q : ↥C.P.H × ↥C.P.H // q ∈ pairSet (XH C) h} :=
        Fintype.card_congr (s02pc_pairEquiv C h hh)
    _ = (pairSet (XH C) h).card := Fintype.card_coe _

end Work.BG
