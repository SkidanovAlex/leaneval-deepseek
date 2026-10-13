/-
  WilC4 : the two-sided germ obstruction.

  The four one-sided germ sets `MonoLm`, `MonoLp`, `MonoHm`, `MonoHp` of `MonoDefs.lean` encode,
  at a point `a` of the domain of a partial function `Y ⊆ ℝ²`:

  * `MonoLm Y a` : on the left of `a` the values are *strictly below* the value at `a`;
  * `MonoHm Y a` : on the left of `a` the values are *strictly above* the value at `a`;
  * `MonoLp Y a` : on the right of `a` the values are *strictly below* the value at `a`;
  * `MonoHp Y a` : on the right of `a` the values are *strictly above* the value at `a`.

  This file proves that neither of the two "two-sided" pairs can hold at *every* point of a
  nondegenerate interval:

    `(Ioo a b ⊆ MonoLm Y ∧ Ioo a b ⊆ MonoLp Y) → False`
    `(Ioo a b ⊆ MonoHm Y ∧ Ioo a b ⊆ MonoHp Y) → False`

  (`MonoLm ∩ MonoLp` = strict local maximum germ at every point, `MonoHm ∩ MonoHp` = strict local
  minimum germ at every point.)

  The argument is purely order-theoretic; in particular no definability or o-minimality hypothesis
  is needed.

  * `countable_locallyR` : for any asymmetric relation `R` on `ℝ` and any function `f : ℝ → ℝ`,
    the set of points `x` such that `R (f x) (f z)` holds for all `z ≠ x` sufficiently close to `x`
    is **countable**: each such `x` can be assigned a rational interval `(p, q) ∋ x` on which it is
    the unique `R`-maximum, and two distinct points never receive the same interval, because
    `x ∈ (p, q)` would then give both `R (f x) (f y)` and `R (f y) (f x)`, contradicting asymmetry.
    The assignment `x ↦ (p, q)` is an injection into the countable set `ℚ × ℚ`.
  * `germ_extr_aux` : materialises the partial function `Y` as a genuine function `F` (well defined
    by `hfun`), shows that the four germ conditions force `Ioo a b` to consist of `R`-maxima of `F`,
    and concludes `False` from the countability of `Ioo a b` (`Cardinal.Real.Ioo_countable_iff`).
  * `germ_extr` : the two instances `R u v := v < u` (both germs below) and `R u v := u < v`
    (both germs above).
-/
import Mathlib
import Submission.Work.WilC4.monoDefs

set_option autoImplicit false

noncomputable section

open Set

namespace Work.WilC4

/-- **Local maxima of an asymmetric relation form a countable set.**

Given an asymmetric relation `R` on `ℝ` and a function `f : ℝ → ℝ`, the points at which `f` is an
`R`-extremum relative to every nearby point form a countable set.

Concretely, if `x` has the property that `R (f x) (f z)` for all `z ≠ x` in a neighbourhood of `x`,
choose rationals `p < x < q` inside that neighbourhood. Two distinct points cannot be assigned the
same pair `(p, q)`: if they were, each of them would witness the `R`-relation at the other, giving
`R (f x) (f y)` and `R (f y) (f x)` simultaneously, contradicting asymmetry. -/
lemma countable_locallyR {R : ℝ → ℝ → Prop} (hR : ∀ u v : ℝ, R u v → R v u → False)
    (f : ℝ → ℝ) :
    Set.Countable {x : ℝ | ∃ ε : ℝ, 0 < ε ∧
      ∀ z : ℝ, 0 < |z - x| → |z - x| < ε → R (f x) (f z)} := by
  classical
  set S : Set ℝ := {x : ℝ | ∃ ε : ℝ, 0 < ε ∧
      ∀ z : ℝ, 0 < |z - x| → |z - x| < ε → R (f x) (f z)} with hS
  -- a rational interval around each point of `S` on which it is the unique `R`-extremum
  have key : ∀ x ∈ S, ∃ pq : ℚ × ℚ, (pq.1 : ℝ) < x ∧ x < (pq.2 : ℝ) ∧
      ∀ z : ℝ, (pq.1 : ℝ) < z → z < (pq.2 : ℝ) → z ≠ x → R (f x) (f z) := by
    intro x hx
    obtain ⟨ε, hε, hg⟩ := hx
    obtain ⟨p, hp1, hp2⟩ := exists_rat_btwn (show x - ε < x by linarith)
    obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (show x < x + ε by linarith)
    refine ⟨(p, q), hp2, hq1, ?_⟩
    intro z hz1 hz2 hzx
    refine hg z ?_ ?_
    · exact abs_pos.mpr (sub_ne_zero.mpr hzx)
    · exact abs_sub_lt_iff.mpr ⟨by linarith, by linarith⟩
  let φ : ∀ x : ℝ, x ∈ S → ℚ × ℚ := fun x hx => Classical.choose (key x hx)
  have hφ : ∀ x (hx : x ∈ S), (φ x hx).1 < x ∧ x < (φ x hx).2 ∧
      ∀ z : ℝ, ((φ x hx).1 : ℝ) < z → z < ((φ x hx).2 : ℝ) → z ≠ x → R (f x) (f z) :=
    fun x hx => Classical.choose_spec (key x hx)
  let Φ : ℝ → ℚ × ℚ := fun x => if hx : x ∈ S then φ x hx else 0
  have hΦ : ∀ x (hx : x ∈ S), Φ x = φ x hx := fun x hx => dite_eq_left hx
  have hinj : Set.InjOn Φ S := by
    intro x hx y hy hxy
    by_contra hne
    have e : φ x hx = φ y hy := by rw [← hΦ x hx, ← hΦ y hy, hxy]
    have e1 : (φ x hx).1 = (φ y hy).1 := congrArg Prod.fst e
    have e2 : (φ x hx).2 = (φ y hy).2 := congrArg Prod.snd e
    have h1 : R (f x) (f y) :=
      (hφ x hx).2.2 y (by rw [e1]; exact (hφ y hy).1)
        (by rw [e2]; exact (hφ y hy).2.1) (Ne.symm hne)
    have h2 : R (f y) (f x) :=
      (hφ y hy).2.2 x (by rw [← e1]; exact (hφ x hx).1)
        (by rw [← e2]; exact (hφ x hx).2.1) hne
    exact hR (f x) (f y) h1 h2
  have hSc : S.Countable :=
    Set.MapsTo.countable_of_injOn (f := Φ) (s := S) (t := Set.univ)
      (fun x _ => Set.mem_univ (Φ x)) hinj Set.countable_univ
  rwa [hS] at hSc

/-- **Two-sided germ obstruction, general form.**

Let `Y ⊆ ℝ²` describe a partial function (each `x` carries at most one value, `hfun`), let `R` be an
asymmetric relation on `ℝ`, and suppose that on `(a, b)` every point has both a left germ and a
right germ that are `R`-below its value. Then `(a, b) = ∅`.

The proof materialises the partial function as a total function `F` (unique value where defined,
`0` elsewhere), so that the germ conditions say that every point of `(a, b)` is an `R`-extremum of
`F`; `countable_locallyR` makes `(a, b)` countable, while `a < b` makes it uncountable. -/
private lemma germ_extr_aux {Y : Set (Fin 2 → ℝ)} {a b : ℝ} (hab : a < b)
    (hfun : ∀ x y y' : ℝ, ![x, y] ∈ Y → ![x, y'] ∈ Y → y = y')
    {R : ℝ → ℝ → Prop} (hR : ∀ u v : ℝ, R u v → R v u → False)
    (hleft : ∀ x ∈ Set.Ioo a b, ∃ ε y : ℝ, 0 < ε ∧ ![x, y] ∈ Y ∧
       ∀ z : ℝ, x - ε < z → z < x → ∃ y' : ℝ, ![z, y'] ∈ Y ∧ R y y')
    (hright : ∀ x ∈ Set.Ioo a b, ∃ ε y : ℝ, 0 < ε ∧ ![x, y] ∈ Y ∧
       ∀ z : ℝ, x < z → z < x + ε → ∃ y' : ℝ, ![z, y'] ∈ Y ∧ R y y') :
    False := by
  classical
  -- materialise the partial function
  let F : ℝ → ℝ := fun x => if h : ∃ y : ℝ, ![x, y] ∈ Y then Classical.choose h else 0
  have hFeq : ∀ x y : ℝ, ![x, y] ∈ Y → F x = y := by
    intro x y hy
    have h : ∃ y : ℝ, ![x, y] ∈ Y := ⟨y, hy⟩
    have h1 : F x = Classical.choose h := dite_eq_left h
    rw [h1]
    exact hfun x (Classical.choose h) y (Classical.choose_spec h) hy
  -- every point of `(a, b)` is an `R`-extremum of `F`
  have hsub : Set.Ioo a b ⊆ {x : ℝ | ∃ ε : ℝ, 0 < ε ∧
      ∀ z : ℝ, 0 < |z - x| → |z - x| < ε → R (F x) (F z)} := by
    intro x hx
    obtain ⟨εm, ym, hεm, hym, hgm⟩ := hleft x hx
    obtain ⟨εp, yp, hεp, hyp, hgp⟩ := hright x hx
    have hymyp : ym = yp := hfun x ym yp hym hyp
    have hFx : F x = ym := hFeq x ym hym
    refine ⟨min εm εp, lt_min hεm hεp, ?_⟩
    intro z hz0 hzlt
    have hzm : |z - x| < εm := lt_of_lt_of_le hzlt (min_le_left _ _)
    have hzp : |z - x| < εp := lt_of_lt_of_le hzlt (min_le_right _ _)
    have hne : z ≠ x := by
      intro h; rw [h, sub_self, abs_zero] at hz0; exact lt_irrefl 0 hz0
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · obtain ⟨y', hy', hRy⟩ := hgm z (by have h2 := (abs_sub_lt_iff.mp hzm).2; linarith) hlt
      rw [hFeq z y' hy', hFx]
      exact hRy
    · obtain ⟨y', hy', hRy⟩ := hgp z hgt (by have h1 := (abs_sub_lt_iff.mp hzp).1; linarith)
      rw [hFeq z y' hy', hFx, hymyp]
      exact hRy
  have hcount : (Set.Ioo a b).Countable :=
    (countable_locallyR hR F).mono hsub
  exact absurd (Cardinal.Real.Ioo_countable_iff.mp hcount) (not_le.mpr hab)

theorem germ_extr {Y : Set (Fin 2 → ℝ)} {a b : ℝ} (hab : a < b) (hfun : ∀ x y y' : ℝ, ![x, y] ∈ Y → ![x, y'] ∈ Y → y = y') : ((Set.Ioo a b ⊆ MonoLm Y ∧ Set.Ioo a b ⊆ MonoLp Y) → False) ∧ ((Set.Ioo a b ⊆ MonoHm Y ∧ Set.Ioo a b ⊆ MonoHp Y) → False) := by
  constructor
  · rintro ⟨hLm, hLp⟩
    exact germ_extr_aux hab hfun (R := fun u v => v < u)
      (fun u v huv hvu => lt_asymm hvu huv)
      (fun x hx => hLm hx) (fun x hx => hLp hx)
  · rintro ⟨hHm, hHp⟩
    exact germ_extr_aux hab hfun (R := fun u v => u < v)
      (fun u v huv hvu => lt_asymm huv hvu)
      (fun x hx => hHm hx) (fun x hx => hHp hx)

end Work.WilC4
