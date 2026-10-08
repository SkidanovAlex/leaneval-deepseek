/-
# `Work.PSU3.StageB.Canon` — the canonical maps `f, g, h` of Ch. VII §1 and H1–H6

Peterfalvi II Ch. VII §1: for a split rank-one datum `H = Q ⋊ D`, `D = H ∩ Hᵗ`, `t ∉ H` an
involution, and `x ∈ Q#` the element `t x t` has a unique canonical form
`t x t = g(x) h(x) t f(x)` with `g(x), f(x) ∈ Q#`, `h(x) ∈ D`.  This module builds those three
maps as functions on `↥Q` (with junk value `1` at the identity) and records the identities
H1–H6 (of which the `Canon3` versions are already proved in `Submission.Work.PSU3.RankOne.*`).

The file also records the canonical data of the conjugates `s^a = a⁻¹ s a` of `s = zc 1`
(`a ∈ Ksub`): `g(s^a) = f(s^a) = s^{a⁻¹}`, `h(s^a) = a²`.
-/
import Mathlib
import Submission.Work.PSU3.StageB.Frame
import Submission.Work.RankOneUniqueness.f_exists
import Submission.Work.RankOneUniqueness.f_unique
import Submission.Work.PSU3.RankOne.H16
import Submission.Work.PSU3.RankOne.canon_conj
import Submission.Work.PSU3.RankOne.canon_mul
import Submission.Work.PSU3.RankOne.canon_mul_ne_one

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open LeanEval.GroupTheory.Defs
open Submission.Blueprint
open Work.RankOneUniqueness
open Classical

namespace Work.PSU3.StageB

open Work.ThmF
open Work.PSU3
open Work.PSU3.RankOne

variable {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G} {n : ℕ}

/-! ## The canonical data of `t x t` -/

section CanonData

/-- Existence of the canonical data of `t x t` for `x ∈ Q#`. -/
lemma exists_canon3 (h : IsSplitRankOne H Q t) (x : ↥Q) (hx : (x : G) ≠ 1) :
    ∃ p : ↥Q × ↥(twoPoint H t) × ↥Q,
      t * (x : G) * t = (p.1 : G) * (p.2.1 : G) * t * (p.2.2 : G) := by
  obtain ⟨y, hy, m, hm, heq⟩ := f_exists h x.2 hx
  obtain ⟨g, hg, d, hd, hgd⟩ := fact_exists h hm
  exact ⟨(⟨g, hg⟩, ⟨d, hd⟩, ⟨y, hy⟩), by rw [heq, hgd]⟩

/-- The canonical data of `t x t` (a choice). -/
noncomputable def ctriple (h : IsSplitRankOne H Q t) (x : ↥Q) (hx : (x : G) ≠ 1) :
    ↥Q × ↥(twoPoint H t) × ↥Q :=
  Classical.choose (exists_canon3 h x hx)

lemma ctriple_spec (h : IsSplitRankOne H Q t) (x : ↥Q) (hx : (x : G) ≠ 1) :
    t * (x : G) * t = ((ctriple h x hx).1 : G) * ((ctriple h x hx).2.1 : G) * t *
      ((ctriple h x hx).2.2 : G) :=
  Classical.choose_spec (exists_canon3 h x hx)

/-- `g(x)`: the `Q`-part of the canonical form of `t x t`. -/
noncomputable def gcan (h : IsSplitRankOne H Q t) (x : ↥Q) : ↥Q :=
  if hx : (x : G) = 1 then 1 else (ctriple h x hx).1

/-- `h(x)`: the `D`-part of the canonical form of `t x t`. -/
noncomputable def hcan (h : IsSplitRankOne H Q t) (x : ↥Q) : ↥(twoPoint H t) :=
  if hx : (x : G) = 1 then 1 else (ctriple h x hx).2.1

/-- `f(x)`: the second `Q`-part of the canonical form of `t x t`. -/
noncomputable def fcan (h : IsSplitRankOne H Q t) (x : ↥Q) : ↥Q :=
  if hx : (x : G) = 1 then 1 else (ctriple h x hx).2.2

lemma gcan_of_ne_one (h : IsSplitRankOne H Q t) {x : ↥Q} (hx : (x : G) ≠ 1) :
    gcan h x = (ctriple h x hx).1 := dif_neg hx

lemma hcan_of_ne_one (h : IsSplitRankOne H Q t) {x : ↥Q} (hx : (x : G) ≠ 1) :
    hcan h x = (ctriple h x hx).2.1 := dif_neg hx

lemma fcan_of_ne_one (h : IsSplitRankOne H Q t) {x : ↥Q} (hx : (x : G) ≠ 1) :
    fcan h x = (ctriple h x hx).2.2 := dif_neg hx

/-- The defining relation of the canonical maps. -/
lemma canon_spec (h : IsSplitRankOne H Q t) {x : ↥Q} (hx : (x : G) ≠ 1) :
    t * (x : G) * t = (gcan h x : G) * (hcan h x : G) * t * (fcan h x : G) := by
  simpa only [gcan, hcan, fcan, dif_neg hx] using ctriple_spec h x hx

/-- Uniqueness of the canonical data (coerced form). -/
lemma canon_unique'' (h : IsSplitRankOne H Q t) {x : ↥Q} (hx : (x : G) ≠ 1)
    {g : ↥Q} {d : ↥(twoPoint H t)} {y : ↥Q}
    (heq : t * (x : G) * t = (g : G) * (d : G) * t * (y : G)) :
    (g : G) = (gcan h x : G) ∧ (d : G) = (hcan h x : G) ∧ (y : G) = (fcan h x : G) := by
  have hs := canon_spec h hx
  have hdH : (d : G) ∈ H := twoPoint_le_left H t d.2
  have hdH' : (hcan h x : G) ∈ H := twoPoint_le_left H t (hcan h x).2
  obtain ⟨hprod, hy⟩ := canon_unique h (H.mul_mem (h.le g.2) hdH)
    (H.mul_mem (h.le (gcan h x).2) hdH')
    y.2 (fcan h x).2 (by rw [← heq, hs])
  obtain ⟨hg, hd⟩ := fact_unique h g.2 (gcan h x).2 d.2 (hcan h x).2 hprod
  exact ⟨by rw [hg], by rw [hd], hy⟩

/-- `Canon3` form of the defining relation. -/
lemma canon3_spec (h : IsSplitRankOne H Q t) {x : ↥Q} (hx : (x : G) ≠ 1) :
    Canon3 H Q t (x : G) (gcan h x : G) (hcan h x : G) (fcan h x : G) :=
  ⟨(gcan h x).2, (hcan h x).2, (fcan h x).2, canon_spec h hx⟩

lemma inv_ne_one {x : ↥Q} (hx : (x : G) ≠ 1) : ((x⁻¹ : ↥Q) : G) ≠ 1 := by
  simpa using hx

end CanonData

/-! ## H1–H6 for the canonical maps -/

section H

variable (h : IsSplitRankOne H Q t)

/-- **`f(x) ≠ 1` for `x ∈ Q#`.**  If `f(x) = 1` then `t x t = g(x)h(x)·t`, so `t x ∈ H` and
`t = (t x) x⁻¹ ∈ H`, a contradiction. -/
lemma fcan_ne_one {x : ↥Q} (hx : (x : G) ≠ 1) : ((fcan h x : G)) ≠ 1 := by
  intro hcon
  have ht : t * t = 1 := mul_self_eq_one h
  have hs := canon_spec h hx
  rw [hcon, mul_one] at hs
  have hm : (gcan h x : G) * (hcan h x : G) ∈ H :=
    H.mul_mem (h.le (gcan h x).2) (twoPoint_le_left H t (hcan h x).2)
  have htx : t * (x : G) = (gcan h x : G) * (hcan h x : G) := by
    have h2 : t * (x : G) * t * t = ((gcan h x : G) * (hcan h x : G)) * t * t := by
      rw [← hs]
    rwa [mul_assoc, ht, mul_one, mul_assoc, ht, mul_one] at h2
  have hmem : t ∈ H := by
    have h1 : (t * (x : G)) * (x : G)⁻¹ ∈ H := by
      rw [htx]; exact H.mul_mem hm (H.inv_mem (h.le x.2))
    have h2 : (t * (x : G)) * (x : G)⁻¹ = t := by group
    rwa [h2] at h1
  exact h.not_mem hmem

/-- **H1 + H4b.** `f(x⁻¹) = g(x)⁻¹`, `g(x⁻¹) = f(x)⁻¹`, `h(x⁻¹) = t h(x)⁻¹ t`. -/
lemma canon_inv_fun {x : ↥Q} (hx : (x : G) ≠ 1) :
    (fcan h (x⁻¹) : G) = ((gcan h x : G))⁻¹ ∧
    (gcan h (x⁻¹) : G) = ((fcan h x : G))⁻¹ ∧
    (hcan h (x⁻¹) : G) = t * ((hcan h x : G))⁻¹ * t := by
  have hx' := inv_ne_one hx
  have hc := canon_inv h (canon3_spec h hx)
  obtain ⟨hgm, hdm, hym, heq⟩ := hc
  have key := canon_unique'' h hx'
    (g := ⟨((fcan h x : G))⁻¹, Q.inv_mem (fcan h x).2⟩)
    (d := ⟨t * ((hcan h x : G))⁻¹ * t, hdm⟩)
    (y := ⟨((gcan h x : G))⁻¹, hym⟩) heq
  exact ⟨(key.2.2).symm, (key.1).symm, (key.2.1).symm⟩

/-- **H1 (f-part).** `f(x⁻¹) = g(x)⁻¹`. -/
lemma fcan_inv {x : ↥Q} (hx : (x : G) ≠ 1) :
    (fcan h (x⁻¹) : G) = ((gcan h x : G))⁻¹ := (canon_inv_fun h hx).1

/-- **H1 (g-part).** `g(x⁻¹) = f(x)⁻¹`. -/
lemma gcan_inv {x : ↥Q} (hx : (x : G) ≠ 1) :
    (gcan h (x⁻¹) : G) = ((fcan h x : G))⁻¹ := (canon_inv_fun h hx).2.1

/-- **H4b.** `h(x⁻¹) = t h(x)⁻¹ t`. -/
lemma hcan_inv {x : ↥Q} (hx : (x : G) ≠ 1) :
    (hcan h (x⁻¹) : G) = t * ((hcan h x : G))⁻¹ * t := (canon_inv_fun h hx).2.2

/-- **`g(x) ≠ 1` for `x ∈ Q#`.** -/
lemma gcan_ne_one {x : ↥Q} (hx : (x : G) ≠ 1) : ((gcan h x : G)) ≠ 1 := by
  intro hcon
  have h1 := fcan_inv h hx
  rw [hcon, inv_one] at h1
  exact fcan_ne_one h (inv_ne_one hx) h1

/-- **H2 + H4c.** `f(f(x)) = x`, `h(f(x)) = h(x)⁻¹`, `g(f(x)) = h(x)⁻¹ g(x)⁻¹ h(x)`. -/
lemma fcan_fcan {x : ↥Q} (hx : (x : G) ≠ 1) :
    (fcan h (fcan h x) : G) = (x : G) ∧
    (hcan h (fcan h x) : G) = ((hcan h x : G))⁻¹ ∧
    (gcan h (fcan h x) : G) = ((hcan h x : G))⁻¹ * ((gcan h x : G))⁻¹ * (hcan h x : G) := by
  have hfx := fcan_ne_one h hx
  have hc := canon_f h x.2 (canon3_spec h hx)
  obtain ⟨hgm, hdm, hym, heq⟩ := hc
  have key := canon_unique'' h hfx
    (g := ⟨((hcan h x : G))⁻¹ * ((gcan h x : G))⁻¹ * (hcan h x : G), hgm⟩)
    (d := ⟨((hcan h x : G))⁻¹, hdm⟩) (y := x) heq
  exact ⟨(key.2.2).symm, (key.2.1).symm, (key.1).symm⟩

/-- **H3 + H4a.**  For `a ∈ D` and `x ∈ Q#`, with `xa := a⁻¹ x a`:
`f(xa) = (t a t)⁻¹ f(x) (t a t)`, `g(xa) = (t a t)⁻¹ g(x) (t a t)`, `h(xa) = (t a t)⁻¹ h(x) a`. -/
lemma canon_conj_fun {x : ↥Q} (hx : (x : G) ≠ 1) (a : ↥(twoPoint H t)) :
    ∃ (xa : ↥Q) (_ : (xa : G) = (a : G)⁻¹ * (x : G) * (a : G)),
      (fcan h xa : G) = (t * (a : G) * t)⁻¹ * (fcan h x : G) * (t * (a : G) * t) ∧
      (gcan h xa : G) = (t * (a : G) * t)⁻¹ * (gcan h x : G) * (t * (a : G) * t) ∧
      (hcan h xa : G) = (t * (a : G) * t)⁻¹ * (hcan h x : G) * (a : G) := by
  have haD : (a : G) ∈ H := twoPoint_le_left H t a.2
  have haQ : (a : G)⁻¹ * (x : G) * (a : G) ∈ Q := by
    simpa using conj_mem_of_mem h (H.inv_mem haD) x.2
  have hx' : ((a : G)⁻¹ * (x : G) * (a : G)) ≠ 1 := by
    intro hcon
    have h2 : (x : G) = 1 := by
      have := congrArg (fun z : G => (a : G) * z * (a : G)⁻¹) hcon
      simpa [mul_assoc] using this
    exact hx h2
  have hc := canon_conj h a.2 (canon3_spec h hx)
  obtain ⟨hgm, hdm, hym, heq⟩ := hc
  have key := canon_unique'' h (x := ⟨_, haQ⟩) hx'
    (g := ⟨(t * (a : G) * t)⁻¹ * (gcan h x : G) * (t * (a : G) * t), hgm⟩)
    (d := ⟨(t * (a : G) * t)⁻¹ * (hcan h x : G) * (a : G), hdm⟩)
    (y := ⟨(t * (a : G) * t)⁻¹ * (fcan h x : G) * (t * (a : G) * t), hym⟩) heq
  exact ⟨⟨_, haQ⟩, rfl, (key.2.2).symm, (key.1).symm, (key.2.1).symm⟩

/-- **H6.**  The canonical data of a product. -/
lemma canon_mul_fun {x y : ↥Q} (hx : (x : G) ≠ 1) (hy : (y : G) ≠ 1)
    (hxy : ((x * y : ↥Q) : G) ≠ 1) :
    (fcan h (x * y) : G) =
      (t * (hcan h y : G) * t)⁻¹ * (fcan h (fcan h x * gcan h y) : G) *
        (t * (hcan h y : G) * t) * (fcan h y : G) ∧
    (hcan h (x * y) : G) =
      (hcan h x : G) * (hcan h (fcan h x * gcan h y) : G) * (hcan h y : G) := by
  have hz : ((fcan h x * gcan h y : ↥Q) : G) ≠ 1 := by
    have hzz := canon_mul_ne_one h x.2 hx y.2 hy (canon3_spec h hx) (canon3_spec h hy) hxy
    simpa using hzz
  have hc := canon_mul h (canon3_spec h hx) (canon3_spec h hy) (canon3_spec h hz)
  obtain ⟨hgm, hdm, hym, heq⟩ := hc
  have key := canon_unique'' h hxy
    (g := ⟨(gcan h x : G) * ((hcan h x : G) * (gcan h (fcan h x * gcan h y) : G) *
        (hcan h x : G)⁻¹), hgm⟩)
    (d := ⟨(hcan h x : G) * (hcan h (fcan h x * gcan h y) : G) * (hcan h y : G), hdm⟩)
    (y := ⟨(t * (hcan h y : G) * t)⁻¹ * (fcan h (fcan h x * gcan h y) : G) *
        (t * (hcan h y : G) * t) * (fcan h y : G), hym⟩) heq
  exact ⟨key.2.2.symm, key.2.1.symm⟩

/-- **H5.**  With `j(x) = x⁻¹`: `(f ∘ j)³(x) = h(x) x h(x)⁻¹`. -/
lemma fcan_jjj {x : ↥Q} (hx : (x : G) ≠ 1) :
    (fcan h ((fcan h ((fcan h (x⁻¹))⁻¹))⁻¹) : G) =
      (hcan h x : G) * (x : G) * ((hcan h x : G))⁻¹ := by
  have ht : t * t = 1 := mul_self_eq_one h
  have hx' : ((x⁻¹ : ↥Q) : G) ≠ 1 := inv_ne_one hx
  have hz1 : ((fcan h (x⁻¹) : ↥Q) : G) ≠ 1 := fcan_ne_one h hx'
  have hgx1 : ((gcan h x : ↥Q) : G) ≠ 1 := gcan_ne_one h hx
  -- `f(x⁻¹) = g(x)⁻¹`
  have hge : (fcan h (x⁻¹) : ↥Q) = (gcan h x)⁻¹ := by
    apply Subtype.ext
    rw [Subgroup.coe_inv]
    exact fcan_inv h hx
  have hge' : (gcan h x : ↥Q) = (fcan h (x⁻¹) : ↥Q)⁻¹ := by
    have hh := congrArg (fun z : ↥Q => z⁻¹) hge
    simpa using hh.symm
  -- canonical data of `gcan h x = (f(x⁻¹))⁻¹`
  have hdata := canon_inv_fun h hz1
  have hff := fcan_fcan h hx'
  have hfinv := canon_inv_fun h hx
  have hg1 : (gcan h (gcan h x) : G) = (x : G) := by
    rw [hge']
    rw [hdata.2.1, hff.1]
    simp
  have hh1 : (hcan h (gcan h x) : G) = ((hcan h x : G))⁻¹ := by
    rw [hge', hdata.2.2, hff.2.1, hfinv.2.2]
    have hcl : t * (t * ((hcan h x : G))⁻¹ * t)⁻¹⁻¹ * t = (t * t) * ((hcan h x : G))⁻¹ * (t * t) := by
      group
    rw [hcl, ht, one_mul, mul_one]
  -- `(f ∘ j)³(x) = (gcan h (fcan h (gcan h x)))⁻¹`
  have hstep : (fcan h ((fcan h ((fcan h (x⁻¹))⁻¹))⁻¹) : G) =
      (((gcan h (fcan h (gcan h x)) : ↥Q)) : G)⁻¹ := by
    rw [hge']
    rw [fcan_inv h (fcan_ne_one h (inv_ne_one hz1))]
  rw [hstep, (fcan_fcan h hgx1).2.2, hh1, hg1]
  group

end H

end Work.PSU3.StageB
