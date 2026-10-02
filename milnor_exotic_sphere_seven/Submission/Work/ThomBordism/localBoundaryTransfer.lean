import Mathlib
import Submission.Work.ThomBordism.stdHalfBallBoundarySign
import Submission.Work.ThomBordism.boundarySign_transfer
import Submission.Work.ThomBordism.relLocClass_germ_eq
import Submission.Work.ThomBordism.relHmapOf_injective_of_localHomeo

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# THOM: the *local* (one-point) boundary-sign transfer, with the model constant

`Work.ThomBordism.boundarySign_transfer` compares the boundary class of a relative fundamental class
with a given class `ψ` through a homeomorphism of the **whole** manifold with the standard half-ball,
and concludes `locClass (hPairδ w) y = c • locClass ψ y` with `c` the constant of
`Work.ThomBordism.stdHalfBallBoundarySign`.  A homeomorphism of the whole manifold is unavailable for
a *bordism* (its boundary is the disjoint union of the pieces), so the global lemma cannot be applied
to the residual of the last mile.

This file contains the *local* form: the comparison is made at a **single** boundary point `y` along a
map `Ψb` of the boundary (thought of as a chart reading at `y`), and the constant is **the model's**,
quantified once and for all outside the data.  Consequently the constant obtained is literally the
same in every instance, which is exactly the *uniformity* that the residual of the last mile needs
(`Work.ThomBordism.sign_of_piecewise_locClass` then assembles the pointwise identities at one point
per piece into the single `ε`).

## The hypotheses

* `Ψb : ↥B ⟶ ↥(stdHalfBallBdry (m+1))` and a left inverse `ginv` of it (needed only through
  `Work.ThomBordism.relHmapOf_injective_of_leftInverse`, which makes the transport along `Ψb`
  injective); the fibre condition of `Ψb` at `y` follows from the left inverse;
* `hgy` — the left inverse moves `Ψb y`'s complement away from `y` (the other half of the pair map
  condition of `ginv`);
* `hw'`, `hψ'` — the standard local classes of the *model* classes `w'`, `ψ'`;
* `hψ`, `hPair` — the two transport hypotheses at `y`: the transports along `Ψb` of the local classes
  of `ψ` and of `hPairδ w` are the model's.

## Relation to the residual (an honest remark)

Given the transports and the model facts, the pair of hypotheses `hψ`, `hPair` is *equivalent* to the
conclusion `locClass (hPairδ w) y = c • locClass ψ y` (the transport is injective and the model's
constant is known).  So this file is a **reformulation** of the pointwise identity in transported
form — it does *not* by itself reduce the mathematical content of the residual.  What it does make
explicit is the **uniformity** of the constant, and it isolates the content into the two *chart-level*
statements `hψ`, `hPair`.  See `NOTE_SESSION55.md` §3–§4 for the consequences (in particular the
*applicability* obstruction: a global `Ψb` with a global left inverse requires `↥B` to embed into
`↥(stdHalfBallBdry (m+1))`, which fails when `∂W` has more than one component, so the
localisation/germ route is mandatory).

## Main results

* `Work.ThomBordism.fibre_of_leftInverse`
* `Work.ThomBordism.localBoundaryTransfer`
-/

set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false

open CategoryTheory
open Work.PTGeometric.HOF

namespace Work.ThomBordism

noncomputable section

/-- A map with a global left inverse has singletons as fibres. -/
theorem fibre_of_leftInverse {X Y : TopCat} (f : X ⟶ Y) (g : Y ⟶ X) (hgf : ∀ x : X, g (f x) = x)
    (y : X) : ∀ z : X, z ∉ ({y} : Set X) → f z ∉ ({f y} : Set Y) := by
  intro z hz hzy
  have h : z = y := by rw [← hgf z, hzy, hgf]
  exact hz (by simp [h])

/-- **The local (one-point) boundary-sign transfer, with the model constant.**

The constant `c` is the one of `Work.ThomBordism.stdHalfBallBoundarySign` (`c = ±1`), chosen once and
for all *outside* the data: the same `c` works at every boundary point and in every instance. -/
theorem localBoundaryTransfer (m : ℕ) (hm : 1 ≤ m) :
    ∃ c : ℤ, (c = 1 ∨ c = -1) ∧
      ∀ (W : TopCat) [CompactSpace W] [T2Space W]
        [ChartedSpace (EuclideanHalfSpace (m + 1)) W]
        [IsManifold (modelWithCornersEuclideanHalfSpace (m + 1)) 1 W]
        {B : Set W} (hB : (modelWithCornersEuclideanHalfSpace (m + 1)).boundary W = B)
        {y : W} (hy : y ∈ B)
        (Ψb : TopCat.of ↥B ⟶ TopCat.of ↥(Work.ThomBordism.stdHalfBallBdry (m + 1)))
        (ginv : TopCat.of ↥(Work.ThomBordism.stdHalfBallBdry (m + 1)) ⟶ TopCat.of ↥B)
        (hgf : ∀ x : ↥B, ginv (Ψb x) = x)
        (hgy : ∀ z : ↥(Work.ThomBordism.stdHalfBallBdry (m + 1)),
          z ≠ Ψb ⟨y, hy⟩ → ginv z ≠ ⟨y, hy⟩)
        (hyc : Ψb ⟨y, hy⟩ ∈ (Work.ThomBordism.stdFlatChart m).source)
        (w : (Work.Cohomology.relChains W B).homology (m + 1))
        (ψ : (Work.Cohomology.singularChains ℤ (TopCat.of ↥B)).homology m)
        (w' : (Work.Cohomology.relChains (TopCat.of ↥(Work.ThomBordism.stdHalfBall (m + 1)))
            (Work.ThomBordism.stdHalfBallBdry (m + 1))).homology (m + 1))
        (ψ' : (Work.Cohomology.singularChains ℤ
            (TopCat.of ↥(Work.ThomBordism.stdHalfBallBdry (m + 1)))).homology m)
        (hw' : ∀ (x : ↥(Work.ThomBordism.stdHalfBall (m + 1)))
            (hx : x ∈ (Work.ThomBordism.stdIntChart (m + 1)).source),
          (HomologicalComplex.homologyMap
            (Work.Orient.relPunct (TopCat.of ↥(Work.ThomBordism.stdHalfBall (m + 1)))
              (Work.ThomBordism.stdHalfBallBdry (m + 1)) x
              (Work.ThomBordism.stdIntChart_source_notMem (m + 1) hx)) (m + 1)).hom w'
            = Work.ThomBordism.stdIntOrient m x hx)
        (hψ' : ∀ (y : ↥(Work.ThomBordism.stdHalfBallBdry (m + 1)))
            (hy : y ∈ (Work.ThomBordism.stdFlatChart m).source),
          Work.Orient.locClass (TopCat.of ↥(Work.ThomBordism.stdHalfBallBdry (m + 1))) m ψ' y
            = Work.ThomBordism.stdFlatGen m hm y hy)
        (hψ : Work.PTGeometric.HOF.RelHmapOf m Ψb ({⟨y, hy⟩} : Set ↥B)
            ({Ψb ⟨y, hy⟩} : Set ↥(Work.ThomBordism.stdHalfBallBdry (m + 1)))
            (fibre_of_leftInverse Ψb ginv hgf ⟨y, hy⟩)
            (Work.Orient.locClass (TopCat.of ↥B) m ψ ⟨y, hy⟩)
          = Work.Orient.locClass (TopCat.of ↥(Work.ThomBordism.stdHalfBallBdry (m + 1))) m
              ψ' (Ψb ⟨y, hy⟩))
        (hPair : Work.PTGeometric.HOF.RelHmapOf m Ψb ({⟨y, hy⟩} : Set ↥B)
            ({Ψb ⟨y, hy⟩} : Set ↥(Work.ThomBordism.stdHalfBallBdry (m + 1)))
            (fibre_of_leftInverse Ψb ginv hgf ⟨y, hy⟩)
            (Work.Orient.locClass (TopCat.of ↥B) m
              ((Work.Cohomology.hPairδ W B m).hom w) ⟨y, hy⟩)
          = Work.Orient.locClass (TopCat.of ↥(Work.ThomBordism.stdHalfBallBdry (m + 1))) m
              ((Work.Cohomology.hPairδ (TopCat.of ↥(Work.ThomBordism.stdHalfBall (m + 1)))
                (Work.ThomBordism.stdHalfBallBdry (m + 1)) m).hom w') (Ψb ⟨y, hy⟩)),
        Work.Orient.locClass (TopCat.of ↥B) m
            ((Work.Cohomology.hPairδ W B m).hom w) ⟨y, hy⟩
          = c • Work.Orient.locClass (TopCat.of ↥B) m ψ ⟨y, hy⟩ := by
  classical
  obtain ⟨c, hc, hspec⟩ := stdHalfBallBoundarySign m hm
  refine ⟨c, hc, ?_⟩
  intro W _ _ _ _ B hB y hy Ψb ginv hgf hgy hyc w ψ w' ψ' hw' hψ' hψ hPair
  have hfib : ∀ z : ↥B, Ψb z = Ψb ⟨y, hy⟩ → z = ⟨y, hy⟩ := by
    intro z hz
    rw [← hgf z, hz, hgf]
  have hinj := relHmapOf_injective_of_leftInverse (n := m) (f := Ψb) (g := ginv)
    (K := ({⟨y, hy⟩} : Set ↥B))
    (K' := ({Ψb ⟨y, hy⟩} : Set ↥(Work.ThomBordism.stdHalfBallBdry (m + 1))))
    (fun z hz hzy => hz (hfib z hzy)) hgy hgf
  have key : RelHmapOf m Ψb ({⟨y, hy⟩} : Set ↥B)
        ({Ψb ⟨y, hy⟩} : Set ↥(Work.ThomBordism.stdHalfBallBdry (m + 1)))
        (fun z hz hzy => hz (hfib z hzy))
        (Work.Orient.locClass (TopCat.of ↥B) m
          ((Work.Cohomology.hPairδ W B m).hom w) ⟨y, hy⟩)
      = RelHmapOf m Ψb ({⟨y, hy⟩} : Set ↥B)
        ({Ψb ⟨y, hy⟩} : Set ↥(Work.ThomBordism.stdHalfBallBdry (m + 1)))
        (fun z hz hzy => hz (hfib z hzy))
        (c • Work.Orient.locClass (TopCat.of ↥B) m ψ ⟨y, hy⟩) := by
    calc RelHmapOf m Ψb ({⟨y, hy⟩} : Set ↥B)
          ({Ψb ⟨y, hy⟩} : Set ↥(Work.ThomBordism.stdHalfBallBdry (m + 1)))
          (fun z hz hzy => hz (hfib z hzy))
          (Work.Orient.locClass (TopCat.of ↥B) m
            ((Work.Cohomology.hPairδ W B m).hom w) ⟨y, hy⟩)
        = Work.Orient.locClass (TopCat.of ↥(Work.ThomBordism.stdHalfBallBdry (m + 1))) m
            ((Work.Cohomology.hPairδ (TopCat.of ↥(Work.ThomBordism.stdHalfBall (m + 1)))
              (Work.ThomBordism.stdHalfBallBdry (m + 1)) m).hom w') (Ψb ⟨y, hy⟩) := hPair
      _ = c • Work.ThomBordism.stdFlatGen m hm (Ψb ⟨y, hy⟩) hyc := hspec w' hw' (Ψb ⟨y, hy⟩) hyc
      _ = c • Work.Orient.locClass (TopCat.of ↥(Work.ThomBordism.stdHalfBallBdry (m + 1))) m
              ψ' (Ψb ⟨y, hy⟩) := by rw [hψ' (Ψb ⟨y, hy⟩) hyc]
      _ = c • RelHmapOf m Ψb ({⟨y, hy⟩} : Set ↥B)
            ({Ψb ⟨y, hy⟩} : Set ↥(Work.ThomBordism.stdHalfBallBdry (m + 1)))
            (fun z hz hzy => hz (hfib z hzy))
            (Work.Orient.locClass (TopCat.of ↥B) m ψ ⟨y, hy⟩) := by rw [hψ]
      _ = RelHmapOf m Ψb ({⟨y, hy⟩} : Set ↥B)
            ({Ψb ⟨y, hy⟩} : Set ↥(Work.ThomBordism.stdHalfBallBdry (m + 1)))
            (fun z hz hzy => hz (hfib z hzy))
            (c • Work.Orient.locClass (TopCat.of ↥B) m ψ ⟨y, hy⟩) :=
          (map_zsmul (f := RelHmapOf m Ψb ({⟨y, hy⟩} : Set ↥B)
            ({Ψb ⟨y, hy⟩} : Set ↥(Work.ThomBordism.stdHalfBallBdry (m + 1)))
            (fun z hz hzy => hz (hfib z hzy))) c
            (Work.Orient.locClass (TopCat.of ↥B) m ψ ⟨y, hy⟩)).symm
  exact hinj key

/-- **The local boundary-sign transfer in the APPLICABLE form.**

Same conclusion as `Work.ThomBordism.localBoundaryTransfer` (the model's constant, quantified once and
for all outside the data), but the injectivity of the transport at `y` is obtained from the *local*
hypotheses on `Ψb` (`Work.ThomBordism.relHmapOf_injective_of_localHomeo`: `Ψb` restricts to a
homeomorphism of pairs on an open neighbourhood `N` of `y`) instead of a *global* left inverse — the
latter forces `Ψb` to be injective on all of `↥B`, which is impossible when `↥B` is the boundary of a
bordism with several pieces (a connected target).  With this form the brick applies to the source
construction: there `Ψb` is a chart reading on the piece containing `y` (a constant elsewhere), which
satisfies the global fibre condition `hfB` and the local homeomorphism data, while being far from
injective. -/
theorem localBoundaryTransfer' (m : ℕ) (hm : 1 ≤ m) :
    ∃ c : ℤ, (c = 1 ∨ c = -1) ∧
      ∀ (W : TopCat) [CompactSpace W] [T2Space W]
        [ChartedSpace (EuclideanHalfSpace (m + 1)) W]
        [IsManifold (modelWithCornersEuclideanHalfSpace (m + 1)) 1 W]
        {B : Set W} (hB : (modelWithCornersEuclideanHalfSpace (m + 1)).boundary W = B)
        {y : W} (hy : y ∈ B)
        (Ψb : TopCat.of ↥B ⟶ TopCat.of ↥(Work.ThomBordism.stdHalfBallBdry (m + 1)))
        (hfB : ∀ x : ↥B, x ∉ ({⟨y, hy⟩} : Set ↥B) →
          Ψb x ∉ ({Ψb ⟨y, hy⟩} : Set ↥(Work.ThomBordism.stdHalfBallBdry (m + 1))))
        (N : Set ↥B) (hN : IsOpen N) (hyN : ⟨y, hy⟩ ∈ N)
        (hIm : IsOpen (Ψb '' N))
        (hcl : IsClosed ({Ψb ⟨y, hy⟩} : Set ↥(Work.ThomBordism.stdHalfBallBdry (m + 1))))
        (ginv : ↥(Ψb '' N) → ↥N) (hgcont : Continuous ginv)
        (hgf : ∀ z : ↥N, ginv ⟨(Ψb z.1 : ↥(Work.ThomBordism.stdHalfBallBdry (m + 1))),
          ⟨z.1, z.2, rfl⟩⟩ = z)
        (hfg : ∀ w : ↥(Ψb '' N),
          (Ψb (ginv w).1 : ↥(Work.ThomBordism.stdHalfBallBdry (m + 1))) = w.1)
        (hyc : Ψb ⟨y, hy⟩ ∈ (Work.ThomBordism.stdFlatChart m).source)
        (w : (Work.Cohomology.relChains W B).homology (m + 1))
        (ψ : (Work.Cohomology.singularChains ℤ (TopCat.of ↥B)).homology m)
        (w' : (Work.Cohomology.relChains (TopCat.of ↥(Work.ThomBordism.stdHalfBall (m + 1)))
            (Work.ThomBordism.stdHalfBallBdry (m + 1))).homology (m + 1))
        (ψ' : (Work.Cohomology.singularChains ℤ
            (TopCat.of ↥(Work.ThomBordism.stdHalfBallBdry (m + 1)))).homology m)
        (hw' : ∀ (x : ↥(Work.ThomBordism.stdHalfBall (m + 1)))
            (hx : x ∈ (Work.ThomBordism.stdIntChart (m + 1)).source),
          (HomologicalComplex.homologyMap
            (Work.Orient.relPunct (TopCat.of ↥(Work.ThomBordism.stdHalfBall (m + 1)))
              (Work.ThomBordism.stdHalfBallBdry (m + 1)) x
              (Work.ThomBordism.stdIntChart_source_notMem (m + 1) hx)) (m + 1)).hom w'
            = Work.ThomBordism.stdIntOrient m x hx)
        (hψ' : ∀ (y : ↥(Work.ThomBordism.stdHalfBallBdry (m + 1)))
            (hy : y ∈ (Work.ThomBordism.stdFlatChart m).source),
          Work.Orient.locClass (TopCat.of ↥(Work.ThomBordism.stdHalfBallBdry (m + 1))) m ψ' y
            = Work.ThomBordism.stdFlatGen m hm y hy)
        (hψ : Work.PTGeometric.HOF.RelHmapOf m Ψb ({⟨y, hy⟩} : Set ↥B)
            ({Ψb ⟨y, hy⟩} : Set ↥(Work.ThomBordism.stdHalfBallBdry (m + 1))) hfB
            (Work.Orient.locClass (TopCat.of ↥B) m ψ ⟨y, hy⟩)
          = Work.Orient.locClass (TopCat.of ↥(Work.ThomBordism.stdHalfBallBdry (m + 1))) m
              ψ' (Ψb ⟨y, hy⟩))
        (hPair : Work.PTGeometric.HOF.RelHmapOf m Ψb ({⟨y, hy⟩} : Set ↥B)
            ({Ψb ⟨y, hy⟩} : Set ↥(Work.ThomBordism.stdHalfBallBdry (m + 1))) hfB
            (Work.Orient.locClass (TopCat.of ↥B) m
              ((Work.Cohomology.hPairδ W B m).hom w) ⟨y, hy⟩)
          = Work.Orient.locClass (TopCat.of ↥(Work.ThomBordism.stdHalfBallBdry (m + 1))) m
              ((Work.Cohomology.hPairδ (TopCat.of ↥(Work.ThomBordism.stdHalfBall (m + 1)))
                (Work.ThomBordism.stdHalfBallBdry (m + 1)) m).hom w') (Ψb ⟨y, hy⟩)),
        Work.Orient.locClass (TopCat.of ↥B) m
            ((Work.Cohomology.hPairδ W B m).hom w) ⟨y, hy⟩
          = c • Work.Orient.locClass (TopCat.of ↥B) m ψ ⟨y, hy⟩ := by
  classical
  obtain ⟨c, hc, hspec⟩ := stdHalfBallBoundarySign m hm
  refine ⟨c, hc, ?_⟩
  intro W _ _ _ _ B hB y hy Ψb hfB N hN hyN hIm hcl ginv hgcont hgf hfg hyc
    w ψ w' ψ' hw' hψ' hψ hPair
  have hinj := relHmapOf_injective_of_localHomeo (n := m) Ψb hN hyN hIm hcl ginv hgcont
    hgf hfg hfB
  have key : RelHmapOf m Ψb ({⟨y, hy⟩} : Set ↥B)
        ({Ψb ⟨y, hy⟩} : Set ↥(Work.ThomBordism.stdHalfBallBdry (m + 1))) hfB
        (Work.Orient.locClass (TopCat.of ↥B) m
          ((Work.Cohomology.hPairδ W B m).hom w) ⟨y, hy⟩)
      = RelHmapOf m Ψb ({⟨y, hy⟩} : Set ↥B)
        ({Ψb ⟨y, hy⟩} : Set ↥(Work.ThomBordism.stdHalfBallBdry (m + 1))) hfB
        (c • Work.Orient.locClass (TopCat.of ↥B) m ψ ⟨y, hy⟩) := by
    calc RelHmapOf m Ψb ({⟨y, hy⟩} : Set ↥B)
          ({Ψb ⟨y, hy⟩} : Set ↥(Work.ThomBordism.stdHalfBallBdry (m + 1))) hfB
          (Work.Orient.locClass (TopCat.of ↥B) m
            ((Work.Cohomology.hPairδ W B m).hom w) ⟨y, hy⟩)
        = Work.Orient.locClass (TopCat.of ↥(Work.ThomBordism.stdHalfBallBdry (m + 1))) m
            ((Work.Cohomology.hPairδ (TopCat.of ↥(Work.ThomBordism.stdHalfBall (m + 1)))
              (Work.ThomBordism.stdHalfBallBdry (m + 1)) m).hom w') (Ψb ⟨y, hy⟩) := hPair
      _ = c • Work.ThomBordism.stdFlatGen m hm (Ψb ⟨y, hy⟩) hyc := hspec w' hw' (Ψb ⟨y, hy⟩) hyc
      _ = c • Work.Orient.locClass (TopCat.of ↥(Work.ThomBordism.stdHalfBallBdry (m + 1))) m
              ψ' (Ψb ⟨y, hy⟩) := by rw [hψ' (Ψb ⟨y, hy⟩) hyc]
      _ = c • RelHmapOf m Ψb ({⟨y, hy⟩} : Set ↥B)
            ({Ψb ⟨y, hy⟩} : Set ↥(Work.ThomBordism.stdHalfBallBdry (m + 1))) hfB
            (Work.Orient.locClass (TopCat.of ↥B) m ψ ⟨y, hy⟩) := by rw [hψ]
      _ = RelHmapOf m Ψb ({⟨y, hy⟩} : Set ↥B)
            ({Ψb ⟨y, hy⟩} : Set ↥(Work.ThomBordism.stdHalfBallBdry (m + 1))) hfB
            (c • Work.Orient.locClass (TopCat.of ↥B) m ψ ⟨y, hy⟩) :=
          (map_zsmul (f := RelHmapOf m Ψb ({⟨y, hy⟩} : Set ↥B)
            ({Ψb ⟨y, hy⟩} : Set ↥(Work.ThomBordism.stdHalfBallBdry (m + 1))) hfB) c
            (Work.Orient.locClass (TopCat.of ↥B) m ψ ⟨y, hy⟩)).symm
  exact hinj key

end

end Work.ThomBordism
