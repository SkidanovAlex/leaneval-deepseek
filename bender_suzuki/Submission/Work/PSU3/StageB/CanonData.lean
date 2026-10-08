/-
# `Work.PSU3.StageB.CanonData` — the maps `f, g, h` of Peterfalvi Ch. VII §1

This module packages the canonical form `t x t = g(x) · h(x) · t · f(x)` of Peterfalvi II
Ch. VII §1 into total maps on `Q`, so that the identities H1–H6 become statements about
functions and can be used in the Stage B (Ch. VII §2) computation.

* `cdTriple h x` — a (junk-typed) choice of the triple `(g, d, y)` for `x : Q`; for
  `(x : G) ≠ 1` it is the canonical data.
* `gMap`, `hMap`, `fMap` — its components.
* `canon3_cdTriple` — for `(x : G) ≠ 1`, `Canon3 H Q t (x:G) (gMap h x) (hMap h x) (fMap h x)`.
* `cdTriple_unique` — the canonical data is unique (from `canon_unique`).
* `H1`–`H6` in function form.
-/
import Mathlib
import Submission.Work.PSU3.Defs
import Submission.Work.RankOneUniqueness.Basic
import Submission.Work.RankOneUniqueness.canon_exists
import Submission.Work.RankOneUniqueness.canon_unique
import Submission.Work.RankOneUniqueness.canon_unique
import Submission.Work.RankOneUniqueness.f_exists
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

open LeanEval.GroupTheory.Defs
open Submission.Blueprint
open Work.RankOneUniqueness

namespace Work.PSU3.StageB

variable {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G}

/-! ## Existence and uniqueness of the canonical data -/

/-- Every `x ∈ Q` with `x ≠ 1` has canonical data: `t x t = g · d · t · y` with
`g, y ∈ Q` and `d ∈ D = H ∩ H^t`. -/
theorem canon3_exists (h : IsSplitRankOne H Q t) {x : G} (hx : x ∈ Q) (hx1 : x ≠ 1) :
    ∃ g ∈ Q, ∃ d ∈ twoPoint H t, ∃ y ∈ Q, Canon3 H Q t x g d y := by
  obtain ⟨a, ha, q, hq, hg⟩ := canon_exists h (conj_notMem h hx hx1)
  obtain ⟨g, hgQ, d, hdD, had⟩ := fact_exists h ha
  exact ⟨g, hgQ, d, hdD, q, hq, hgQ, hdD, hq, by rw [hg, had]⟩

/-- Packaged form: a single triple. -/
theorem canon3_exists_pack (h : IsSplitRankOne H Q t) {x : G} (hx : x ∈ Q) (hx1 : x ≠ 1) :
    ∃ p : Q × (twoPoint H t) × Q, Canon3 H Q t x (p.1 : G) (p.2.1 : G) (p.2.2 : G) := by
  obtain ⟨g, hgQ, d, hdD, y, hyQ, hc⟩ := canon3_exists h hx hx1
  exact ⟨(⟨g, hgQ⟩, (⟨d, hdD⟩, ⟨y, hyQ⟩)), hc⟩

/-- Uniqueness of the canonical data. -/
theorem canon3_unique' (h : IsSplitRankOne H Q t) {x g g' d d' y y' : G}
    (h1 : Canon3 H Q t x g d y) (h2 : Canon3 H Q t x g' d' y') :
    g = g' ∧ d = d' ∧ y = y' := by
  obtain ⟨hg, hd, hy, heq1⟩ := h1
  obtain ⟨hg', hd', hy', heq2⟩ := h2
  have hdHD : d ∈ H := (Subgroup.mem_inf.mp hd).1
  have hd'HD : d' ∈ H := (Subgroup.mem_inf.mp hd').1
  have hmain : g * d = g' * d' ∧ y = y' :=
    canon_unique h (H.mul_mem (h.le hg) hdHD) (H.mul_mem (h.le hg') hd'HD) hy hy'
      (by rw [← heq1, heq2])
  exact ⟨(fact_unique h hg hg' hd hd' hmain.1).1, (fact_unique h hg hg' hd hd' hmain.1).2,
    hmain.2⟩

/-! ## The totalised maps `g, h, f` -/

/-- A choice of canonical data for `x : Q`; junk (`1, 1, 1`) at `x = 1`. -/
noncomputable def cdTriple (h : IsSplitRankOne H Q t) (x : Q) : Q × (twoPoint H t) × Q := by
  classical
  exact if hx : (x : G) = 1 then ((1 : Q), (1 : twoPoint H t), (1 : Q))
  else Classical.choose (canon3_exists_pack h x.2 hx)

/-- For `x ≠ 1`, `cdTriple` is the canonical data. -/
theorem canon3_cdTriple (h : IsSplitRankOne H Q t) {x : Q} (hx : (x : G) ≠ 1) :
    Canon3 H Q t (x : G) ((cdTriple h x).1 : G) ((cdTriple h x).2.1 : G)
      ((cdTriple h x).2.2 : G) := by
  rw [cdTriple, dif_neg hx]
  exact Classical.choose_spec (canon3_exists_pack h x.2 hx)

/-- The `g`-component `g(x)`. -/
noncomputable def gMap (h : IsSplitRankOne H Q t) (x : Q) : Q := (cdTriple h x).1

/-- The `h`-component `h(x) ∈ D`. -/
noncomputable def hMap (h : IsSplitRankOne H Q t) (x : Q) : twoPoint H t := (cdTriple h x).2.1

/-- The `f`-component `f(x)`. -/
noncomputable def fMap (h : IsSplitRankOne H Q t) (x : Q) : Q := (cdTriple h x).2.2

/-- The defining property of the maps, in `Canon3` form. -/
theorem canon3_fgh (h : IsSplitRankOne H Q t) {x : Q} (hx : (x : G) ≠ 1) :
    Canon3 H Q t (x : G) (gMap h x : G) (hMap h x : G) (fMap h x : G) :=
  canon3_cdTriple h hx

section H16

variable (h : IsSplitRankOne H Q t)

/-! ### H1 (`f(x⁻¹) = g(x)⁻¹`, `g(x⁻¹) = f(x)⁻¹`) -/

theorem H1_f {x : Q} (hx : (x : G) ≠ 1) : (fMap h (x⁻¹) : G) = (gMap h x : G)⁻¹ := by
  have hx' : ((x⁻¹ : Q) : G) ≠ 1 := by
    rw [Subgroup.coe_inv]
    exact inv_ne_one.mpr hx
  have hc := canon_inv h (canon3_fgh h hx)
  have h2 := canon3_unique' h hc (canon3_fgh h hx')
  exact h2.2.2.symm

theorem H1_g {x : Q} (hx : (x : G) ≠ 1) : (gMap h (x⁻¹) : G) = (fMap h x : G)⁻¹ := by
  have hx' : ((x⁻¹ : Q) : G) ≠ 1 := by
    rw [Subgroup.coe_inv]
    exact inv_ne_one.mpr hx
  have hc := canon_inv h (canon3_fgh h hx)
  have h2 := canon3_unique' h hc (canon3_fgh h hx')
  exact h2.1.symm

/-! ### H2 (`f(f(x)) = x`, `h(f(x)) = h(x)⁻¹`) -/

theorem fMap_ne_one {x : Q} (hx : (x : G) ≠ 1) : ((fMap h x : Q) : G) ≠ 1 := by
  intro hc
  have ht : t * t = 1 := mul_self_eq_one h
  obtain ⟨-, hdD, -, heq⟩ := canon3_fgh h hx
  have htd : t * (x : G) = (gMap h x : G) * (hMap h x : G) := by
    have h1 := congrArg (fun z : G => z * t) heq
    rw [hc, mul_one] at h1
    simpa [mul_assoc, ht] using h1
  have htH : t ∈ H := by
    have h2 : t * (x : G) ∈ H := by
      rw [htd]
      exact H.mul_mem (h.le (gMap h x).2) (Subgroup.mem_inf.mp hdD).1
    have h3 := H.mul_mem h2 (H.inv_mem (h.le x.2))
    simpa [mul_assoc] using h3
  exact h.not_mem htH

theorem gMap_ne_one {x : Q} (hx : (x : G) ≠ 1) : ((gMap h x : Q) : G) ≠ 1 := by
  have hxin : (((x⁻¹ : Q)) : G) ≠ 1 := by
    rw [Subgroup.coe_inv]
    exact inv_ne_one.mpr hx
  have h1 : (gMap h ((x⁻¹)⁻¹) : G) = (fMap h (x⁻¹))⁻¹ := H1_g h hxin
  have h2 : ((fMap h (x⁻¹) : Q) : G) ≠ 1 := fMap_ne_one h hxin
  intro hc
  have h3 : (gMap h ((x⁻¹)⁻¹) : G) = 1 := by simpa using hc
  rw [h1] at h3
  exact h2 (by simpa using congrArg (fun z : G => z⁻¹) h3)

theorem H2_f {x : Q} (hx : (x : G) ≠ 1) : fMap h (fMap h x) = x := by
  have hfx : ((fMap h x : Q) : G) ≠ 1 := fMap_ne_one h hx
  have hc := canon_f h (x := (x : G)) x.2 (canon3_fgh h hx)
  exact Subtype.ext (canon3_unique' h hc (canon3_fgh h hfx)).2.2.symm

theorem H2_h {x : Q} (hx : (x : G) ≠ 1) : hMap h (fMap h x) = (hMap h x)⁻¹ := by
  have hfx : ((fMap h x : Q) : G) ≠ 1 := fMap_ne_one h hx
  have hc := canon_f h (x := (x : G)) x.2 (canon3_fgh h hx)
  exact Subtype.ext (canon3_unique' h hc (canon3_fgh h hfx)).2.1.symm

/-! ### H6 (`f(xy)`, `h(xy)` from the data of `x`, `y` and `f(x) g(y)`) -/

theorem H6 {x y : Q} (hx : (x : G) ≠ 1) (hy : (y : G) ≠ 1)
    (hxy : ((x * y : Q) : G) ≠ 1) :
    Canon3 H Q t ((x : G) * (y : G))
      ((gMap h x : G) * ((hMap h x : G) * (gMap h (fMap h x * gMap h y) : G) *
        (hMap h x : G)⁻¹))
      ((hMap h x : G) * (hMap h (fMap h x * gMap h y) : G) * (hMap h y : G))
      ((t * (hMap h y : G) * t)⁻¹ * (fMap h (fMap h x * gMap h y) : G) *
        (t * (hMap h y : G) * t) * (fMap h y : G)) := by
  have hz : ((fMap h x * gMap h y : Q) : G) ≠ 1 :=
    Work.PSU3.RankOne.canon_mul_ne_one (h := h) (x := (x : G)) (y := (y : G))
      (gx := (gMap h x : G)) (dx := (hMap h x : G)) (fx := (fMap h x : G))
      (gy := (gMap h y : G)) (dy := (hMap h y : G)) (fy := (fMap h y : G))
      x.2 hx y.2 hy (canon3_fgh h hx) (canon3_fgh h hy)
      (by simpa [Subgroup.coe_mul] using hxy)
  exact Work.PSU3.RankOne.canon_mul h (canon3_fgh h hx) (canon3_fgh h hy) (canon3_fgh h hz)

end H16

end Work.PSU3.StageB
