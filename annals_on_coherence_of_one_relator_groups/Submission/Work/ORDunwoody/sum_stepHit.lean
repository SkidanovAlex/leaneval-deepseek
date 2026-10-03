/-
Copyright: work of the ORDunwoody subproject (node N13 of the
`annals_on_coherence_of_one_relator_groups` project).

# The sum of the contributions of the steps of a walk is the number of visits in the track

`Work.ORDunwoody.alphaFaceWalkDefs` defines the contribution `stepHit τ s` of a directed step `s`
of a boundary walk: by `Dunwoody.phi_mid_tgt` (`Dunwoody.phi_tgt_mid`) it is `[m ∈ τ]`, where `m`
is the pattern point of `s` and `τ` is a track, while a collapsed step (`DStep.skip`), which
visits no pattern point, contributes `0`.  Consequently the sum of the contributions of the steps
of a list `l` is, in `ZMod 2`, the number of the entries of `l` whose pattern point lies in `τ` —
which is `Work.ORDunwoody.sum_stepHit` below.

This file isolates the *purely combinatorial* content of that statement (no geometry is used: the
only properties of `phi τ` that enter are `phi_mid_tgt` and `phi_tgt_mid`): the auxiliary Boolean
predicate `stepHitB τ s` ("the pattern point of `s` lies in `τ`") and the two lists it counts,

* `stepHit_eq_stepHitB`: `stepHit τ s = [stepHitB τ s]`;
* `stepHitB_eq_false`, `stepHitB_eq_decide`: the value of `stepHitB` in terms of `DStep.mid?`.

Then the sum of a list of `0`/`1` values is its number of `1`s (`stepHit_eq_stepHitB` together
with the induction on the list) and, filtering `l.filterMap DStep.mid?` by `τ`, exactly the
entries of `l` with `stepHitB τ s = true` are counted (`List.filterMap_cons_none`,
`List.filterMap_cons_some`).
-/
import Mathlib
import Submission.Work.ORDunwoody.alphaFaceWalkDefs

namespace Work.ORDunwoody

universe u

variable {G : Type u} [Group G] {V : Type u} [MulAction G V] [DecidableEq V]
variable {T : GTree G V} {t₀ : V} {P : FinPresentation G}
variable {D : Cayley.GeoData T t₀ P} [DecidableEq (Dunwoody.Track D)]

/-- **Does a directed step visit the track `τ`?**  The Boolean predicate recording whether the
pattern point of the step lies in `τ`; a collapsed step visits no pattern point, hence is not a
visit of any track. -/
def stepHitB (τ : Dunwoody.Track D) : Dunwoody.DStep D → Bool
  | Dunwoody.DStep.fwd e => decide (Dunwoody.trackOf e.mid = τ)
  | Dunwoody.DStep.bwd e => decide (Dunwoody.trackOf e.mid = τ)
  | Dunwoody.DStep.skip _ _ => false

/-- **The contribution of a step is the indicator of whether it visits the track.** -/
theorem stepHit_eq_stepHitB (τ : Dunwoody.Track D) (s : Dunwoody.DStep D) :
    Dunwoody.stepHit τ s = (if stepHitB τ s then (1 : ZMod 2) else 0) := by
  cases s with
  | fwd e =>
    show Dunwoody.phi τ (Sum.inr e.mid) (Sum.inl (Dunwoody.MidV.tgt e.mid)) = _
    rw [Dunwoody.phi_mid_tgt]
    by_cases h : Dunwoody.trackOf e.mid = τ <;> simp [stepHitB, h]
  | bwd e =>
    show Dunwoody.phi τ (Sum.inl (Dunwoody.MidV.tgt e.mid)) (Sum.inr e.mid) = _
    rw [Dunwoody.phi_tgt_mid]
    by_cases h : Dunwoody.trackOf e.mid = τ <;> simp [stepHitB, h]
  | skip u w => simp [stepHitB]

/-- A collapsed step is not a visit of any track. -/
theorem stepHitB_eq_false (τ : Dunwoody.Track D) {s : Dunwoody.DStep D}
    (h : s.mid? = none) : stepHitB τ s = false := by
  cases s <;> simp_all [stepHitB]

/-- A step with pattern point `m` visits the track `τ` exactly when `m ∈ τ`. -/
theorem stepHitB_eq_decide (τ : Dunwoody.Track D) {s : Dunwoody.DStep D}
    {m : Dunwoody.MidV D} (h : s.mid? = some m) :
    stepHitB τ s = decide (Dunwoody.trackOf m = τ) := by
  cases s <;> simp_all [stepHitB]

theorem sum_stepHit {G : Type u} [Group G] {V : Type u} [MulAction G V] [DecidableEq V]
    {T : Work.ORDunwoody.GTree G V} {t₀ : V} {P : Work.ORDunwoody.FinPresentation G}
    {D : Work.ORDunwoody.Cayley.GeoData T t₀ P}
    [DecidableEq (Work.ORDunwoody.Dunwoody.Track D)]
    (τ : Work.ORDunwoody.Dunwoody.Track D)
    (l : List (Work.ORDunwoody.Dunwoody.DStep D)) :
    (l.map (Work.ORDunwoody.Dunwoody.stepHit τ)).sum =
      (((l.filterMap Work.ORDunwoody.Dunwoody.DStep.mid?).filter
        (fun m => Work.ORDunwoody.Dunwoody.trackOf m = τ)).length : ZMod 2) := by
  induction l with
  | nil => simp
  | cons s l ih =>
    rw [List.map_cons, List.sum_cons, stepHit_eq_stepHitB, ih]
    cases hs : s.mid? with
    | none =>
      rw [stepHitB_eq_false τ hs, List.filterMap_cons_none hs]
      simp
    | some m =>
      rw [stepHitB_eq_decide τ hs, List.filterMap_cons_some hs]
      by_cases hq : Dunwoody.trackOf m = τ
      · rw [if_pos (by simp [hq]), List.filter_cons_of_pos (by simp [hq]), List.length_cons,
          Nat.cast_add, Nat.cast_one]
        ring
      · rw [if_neg (by simp [hq]), List.filter_cons_of_neg (by simp [hq])]
        simp

end Work.ORDunwoody
