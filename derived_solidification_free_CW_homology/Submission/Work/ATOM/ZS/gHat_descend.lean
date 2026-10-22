import Mathlib
import Submission.Work.ATOM.ZS.Topo.TSpace
import Submission.Work.ATOM.ZS.Topo.Maps
import Submission.Work.ATOM.zmap_ext_of_closed_cover
import Submission.Work.ATOM.ZS.pullback_cover
import Submission.Work.ATOM.ZS.map_to_explicit_pullback

namespace Work.ATOM.ZS

open CategoryTheory LightProfinite OnePoint

/-! ## Reduction to the explicit pullback of `tProj`

`Work.ATOM.zmap_ext_of_closed_cover` glues morphisms out of `ℤ[T]` along a jointly surjective
family.  Applied to the kernel pair of `tProj : T' ⟶ ℕ∪{∞}` we need a usable point-set model of
that kernel pair; the categorical `Limits.pullback` is only available through its universal
property, whereas `CompHausLike.pullback` is Mathlib's explicit model (the set of pairs
`(p, q)` with `tProj p = tProj q` inside `T' × T'`).  The two lemmas below bridge the gap:
`Work.ATOM.ZS.map_to_explicit_pullback` compares the two pullback objects, and
`Work.ATOM.ZS.pullback_cover` supplies the two-piece cover of the explicit one.

The two pieces are the `∞`-fibre piece (`S × S`, mapping `(x,y) ↦ ((∞,x),(∞,y))`) and the diagonal
(`T'`, `p ↦ (p,p)`):

* on the diagonal the two projections of the kernel pair coindice, so the two composites agree on
  the nose;
* on the `∞`-piece the first coordinate has index `∞`, hence — by the pullback condition — so does
  the second, and there `β` and `pr₂` agree pointwise
  (`Work.ATOM.ZS.betaT_eq_pr₂T_of_infty`, `Work.ATOM.betaFun_infty`), so both composites vanish. -/

noncomputable section

/-- The difference `zmap a - zmap b` reappears as the difference of the composites: functoriality
of `zmap` plus additivity of precomposition. -/
lemma zmap_comp_zmap_sub {S : LightProfinite.{0}} [Infinite S] {X : LightProfinite.{0}}
    (u : X ⟶ Work.ATOM.T' S) :
    Work.ATOM.zmap u ≫
        (Work.ATOM.zmap (Work.ATOM.pr₂T S) - Work.ATOM.zmap (Work.ATOM.betaT S)) =
      Work.ATOM.zmap (u ≫ Work.ATOM.pr₂T S) - Work.ATOM.zmap (u ≫ Work.ATOM.betaT S) := by
  rw [Preadditive.comp_sub, ← Functor.map_comp, ← Functor.map_comp]

/-- A morphism into `T'` whose first coordinate is everywhere `∞` has `pr₂T = betaT`: pointwise
both sides are the second coordinate of the point. -/
lemma comp_pr₂T_eq_comp_betaT_of_infty {S : LightProfinite.{0}} [Infinite S]
    {X : LightProfinite.{0}} (u : X ⟶ Work.ATOM.T' S)
    (h : ∀ x : ↥X, (u x).1.1 = (∞ : ℕ∪{∞})) :
    u ≫ Work.ATOM.pr₂T S = u ≫ Work.ATOM.betaT S := by
  ext x
  show (u x).1.2 = Work.ATOM.betaFun S (u x).1
  rw [show (u x).1 = ((∞ : ℕ∪{∞}), (u x).1.2) from Prod.ext (h x) rfl]
  exact (Work.ATOM.betaFun_infty _).symm

/-- On the `∞`-piece of the kernel pair the section `pr₂ - β` vanishes. -/
lemma zmap_comp_zmap_sub_eq_zero_of_infty {S : LightProfinite.{0}} [Infinite S]
    {X : LightProfinite.{0}} (u : X ⟶ Work.ATOM.T' S)
    (h : ∀ x : ↥X, (u x).1.1 = (∞ : ℕ∪{∞})) :
    Work.ATOM.zmap u ≫
      (Work.ATOM.zmap (Work.ATOM.pr₂T S) - Work.ATOM.zmap (Work.ATOM.betaT S)) = 0 := by
  rw [zmap_comp_zmap_sub (S := S) u, comp_pr₂T_eq_comp_betaT_of_infty (S := S) u h, sub_self]

/-- **The descent condition for the null sequence `g`.**  The section
`ĝ = zmap pr₂ − zmap β` on `T'` agrees on the two projections of the kernel pair of
`tProj : T' ⟶ ℕ∪{∞}`, so it descends to `ℤ[ℕ∪{∞}]` (`Work.ATOM.zdesc`).  Route: cover the
pullback by the two *closed* pieces `{q | (fst q).1.1 = ∞}` and `{q | fst q = snd q}`
(`Work.ATOM.zmap_ext_of_closed_cover` with the inclusions as the cover maps); on the diagonal the
two sides are equal on the nose, and on the `∞`-piece use
`Work.ATOM.betaT_eq_pr₂T_of_infty` pointwise. -/
theorem gHat_descend (S : LightProfinite.{0}) [Infinite S] :
    Work.ATOM.zmap (CategoryTheory.Limits.pullback.fst (Work.ATOM.tProj S) (Work.ATOM.tProj S)) ≫
        (Work.ATOM.zmap (Work.ATOM.pr₂T S) - Work.ATOM.zmap (Work.ATOM.betaT S)) =
      Work.ATOM.zmap (CategoryTheory.Limits.pullback.snd (Work.ATOM.tProj S) (Work.ATOM.tProj S)) ≫
        (Work.ATOM.zmap (Work.ATOM.pr₂T S) - Work.ATOM.zmap (Work.ATOM.betaT S)) := by
  -- the explicit (point-set) model of the kernel pair and its two-piece cover
  obtain ⟨C, ι, h0, h1, hcov⟩ := Work.ATOM.ZS.pullback_cover S
  -- the comparison of the categorical pullback with the explicit one
  obtain ⟨e, he1, he2⟩ := Work.ATOM.ZS.map_to_explicit_pullback S
  -- the equality for the explicit pullback, glued along the cover
  have key : Work.ATOM.zmap (CompHausLike.pullback.fst (Work.ATOM.tProj S) (Work.ATOM.tProj S)) ≫
        (Work.ATOM.zmap (Work.ATOM.pr₂T S) - Work.ATOM.zmap (Work.ATOM.betaT S)) =
      Work.ATOM.zmap (CompHausLike.pullback.snd (Work.ATOM.tProj S) (Work.ATOM.tProj S)) ≫
        (Work.ATOM.zmap (Work.ATOM.pr₂T S) - Work.ATOM.zmap (Work.ATOM.betaT S)) := by
    refine Work.ATOM.zmap_ext_of_closed_cover _ _ 2 C ι ?_ ?_
    · -- the two pieces jointly cover the pullback
      intro t
      rcases hcov t with h | h
      · exact ⟨0, h⟩
      · exact ⟨1, h⟩
    · -- and on each piece the two composites agree
      rw [Fin.forall_fin_two]
      constructor
      · -- the `∞`-piece: both composites vanish
        have hL : Work.ATOM.zmap (ι 0) ≫
            (Work.ATOM.zmap (CompHausLike.pullback.fst (Work.ATOM.tProj S) (Work.ATOM.tProj S)) ≫
              (Work.ATOM.zmap (Work.ATOM.pr₂T S) - Work.ATOM.zmap (Work.ATOM.betaT S))) = 0 := by
          rw [← Category.assoc, ← Functor.map_comp]
          exact zmap_comp_zmap_sub_eq_zero_of_infty
            (ι 0 ≫ CompHausLike.pullback.fst (Work.ATOM.tProj S) (Work.ATOM.tProj S))
            (fun x => h0 x)
        have hR : Work.ATOM.zmap (ι 0) ≫
            (Work.ATOM.zmap (CompHausLike.pullback.snd (Work.ATOM.tProj S) (Work.ATOM.tProj S)) ≫
              (Work.ATOM.zmap (Work.ATOM.pr₂T S) - Work.ATOM.zmap (Work.ATOM.betaT S))) = 0 := by
          rw [← Category.assoc, ← Functor.map_comp]
          exact zmap_comp_zmap_sub_eq_zero_of_infty
            (ι 0 ≫ CompHausLike.pullback.snd (Work.ATOM.tProj S) (Work.ATOM.tProj S))
            (fun x => by
              -- the second coordinate of a point of the `∞`-piece also has index `∞`
              have h : Work.ATOM.tProj S ((ι 0 x).1.1) = Work.ATOM.tProj S ((ι 0 x).1.2) :=
                (ι 0 x).2
              rw [Work.ATOM.tProj_apply] at h
              exact h.symm.trans (h0 x))
        rw [hL, hR]
      · -- the diagonal: the two projections of the kernel pair coincide
        have hmc : Work.ATOM.zmap (ι 1) ≫
              Work.ATOM.zmap (CompHausLike.pullback.fst (Work.ATOM.tProj S) (Work.ATOM.tProj S)) =
            Work.ATOM.zmap (ι 1) ≫
              Work.ATOM.zmap (CompHausLike.pullback.snd (Work.ATOM.tProj S) (Work.ATOM.tProj S)) := by
          rw [← Functor.map_comp, ← Functor.map_comp, h1]
        rw [← Category.assoc, ← Category.assoc, hmc]
  -- transport the equality from the explicit pullback to the categorical one
  have hPf : Work.ATOM.zmap (CategoryTheory.Limits.pullback.fst (Work.ATOM.tProj S)
        (Work.ATOM.tProj S)) =
      Work.ATOM.zmap e ≫
        Work.ATOM.zmap (CompHausLike.pullback.fst (Work.ATOM.tProj S) (Work.ATOM.tProj S)) := by
    rw [← Functor.map_comp, he1]
  have hPs : Work.ATOM.zmap (CategoryTheory.Limits.pullback.snd (Work.ATOM.tProj S)
        (Work.ATOM.tProj S)) =
      Work.ATOM.zmap e ≫
        Work.ATOM.zmap (CompHausLike.pullback.snd (Work.ATOM.tProj S) (Work.ATOM.tProj S)) := by
    rw [← Functor.map_comp, he2]
  rw [hPf, hPs, Category.assoc, Category.assoc, key]

end

end Work.ATOM.ZS
