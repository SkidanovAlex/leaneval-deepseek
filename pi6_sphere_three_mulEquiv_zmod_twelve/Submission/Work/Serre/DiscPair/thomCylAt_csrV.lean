import Mathlib
import Submission.Work.Serre.csrAssembly
import Submission.Work.Serre.DiscPair.thomCylAt_of_relVanishing
import Submission.Work.Serre.DiscPair.isZero_relCoh_fibreBottom
import Submission.Work.Serre.DiscPair.relCoh_cylBot_trimming
import Submission.Work.Serre.C1CylExplicit
import Submission.Work.Thom.relCohHomeomorph

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option linter.style.haveILetI false
set_option linter.unusedVariables false

namespace Work.Serre.DiscPair

open CategoryTheory CategoryTheory.Limits

-- ROUTE (please follow it): apply `Work.Serre.DiscPair.thomCylAt_of_relVanishing q r N S V`
-- with `S = Set.range (attachIncl n Y ι f)` (closed, by `Work.RatHurewicz.isClosed_range_attachIncl`)
-- and `V = csrV n Y ι f` (open, by `Work.Serre.csrGeom`), `hSV` from the first conjunct of
-- `Work.Serre.csrCompress`'s proof.  The two vanishing hypotheses are:
-- (a) `hvanV : IsZero (RelCoh ℚ j ↥V {x | (x : Z) ∈ S})` for `j ≤ N+2`.  Get it from
--     `(csrCompress n Y ι f q hq j).1` (integral homology vanishing of `(V,S)`) by
--     `Work.Stems.Engine.isZero_relChainsR_rat_of_isZero_relChains` (transfer ℤ→ℚ) followed by
--     `Work.StemsB.ratDualUCT` (`RelCoh ℚ j = H^j` of the dual complex `= (H_j)^*`) — a zero
--     module has zero dual.  (`Submission/Work/Serre/csrAssembly.lean` performs exactly the ℤ→ℚ
--     transfer; reuse its pattern.)
-- (b) `hvanX : IsZero (RelCoh ℚ j ↥((cylRetract q) ⁻¹' V) (A_V ∪ (cylRetract q) ⁻¹' S))` for
--     `j ≤ N+2`.  Derive it from (a) and from `(csrCompress n Y ι f q hq j).2` as follows: the
--     long exact sequence of the triple `(cylRetract q)⁻¹S ⊆ A_V ∪ (cylRetract q)⁻¹S ⊆
--     (cylRetract q)⁻¹V` (`Work.Serre.tripleShortCoh`/`TripleCohLES`) reads
--       `H^j(X,Z) → H^j(X,Y) → H^j(Y,Z) → H^{j+1}(X,Z)`;
--     here `H^j(X,Y) = H^j(cylPre q V, cylPre q S) = 0` for `j ≤ N+2` by
--     `Work.Serre.subsingleton_relCoh_cylPre q S V hSV N hvanV j hj`, and
--     `H^j(Y,Z) ≅ H^j(A_V, A_V ∩ cylPre q S) = H^j(q⁻¹V, q⁻¹S) = 0` for all `j` by
--     `(csrCompress n Y ι f q hq j).2` + the ℤ→ℚ transfer + `ratDualUCT` (the bottom copy
--     `range (cylIncl q) ∩ (cylRetract q)⁻¹V` is homeomorphic to `q⁻¹V`, compatibly with the
--     relative sets).  Both outer terms vanishing in every degree `≤ N+2` gives `H^j(X,Z) = 0`.
--
-- IMPLEMENTATION NOTE (this proof).  The route above is followed; `tripleShortCoh` is packaged as
-- `Work.Serre.DiscPair.isIso_relCohMap_id_of_vanishingRV`, which turns the vanishing of
-- `H^k(Y,Z)` into the isomorphism `H^j(P,Y) ≅ H^j(P,Z)` (`P = cylPre q V`, `Z = cylPre q S`,
-- `Y = P ∩ (cylBot q ∪ Z)`), and the vanishing of the target is `subsingleton_relCoh_cylPre`.
-- The input `H^k(Y,Z) = H^k(trimAp q S V, trimAp q S V ∩ Z) = 0` is assembled from
-- `Work.Serre.DiscPair.relCoh_cylBot_trimming` (collar excision + collar shrink, one degree down:
-- the pair `(↥{x : ↥P | x ∈ cylBot ∨ x ∈ Z}, ...∩ Z)` is isomorphic to `(trimC q V, ... ∩ Z)`) and
-- the explicit homeomorphism `q⁻¹V ≃ₜ cylBot q ∩ cylPre q V` induced by `cylHomeoExplicit q`, which
-- identifies the bottom-copy pair with `(q⁻¹V, q⁻¹S)`; the latter vanishes by `csrCompress.2`.
-- The ℤ→ℚ transfer is `Work.Serre.DiscPair.isZero_relCoh_of_isZero_relH_rat`.
theorem thomCylAt_csrV (n : ℕ) (Y : Type) [TopologicalSpace Y] (ι : Type)
    (f : ι → C(Work.RatHurewicz.cellSphere n, Y)) {E : Type} [TopologicalSpace E]
    (q : C(E, Work.RatHurewicz.attachCells n Y ι f)) (hq : Work.StemsB.IsSerreFibration q)
    (r N : ℕ) (hr : 1 ≤ r)
    (IH : Work.Serre.ThomCylAt r N (Work.Serre.restrictFibre q
      (Set.range (Work.RatHurewicz.attachIncl n Y ι f)))) :
    Work.Serre.ThomCylAt r N (Work.Serre.restrictFibre q (Work.Serre.csrV n Y ι f)) := by
  classical
  obtain ⟨-, -, -, -, -, -, -, -, -, hVop, -, -⟩ := Work.Serre.csrGeom n Y ι f
  -- the closed old part `S` and the open complement `V` of the cell centres
  have hSV : Set.range (Work.RatHurewicz.attachIncl n Y ι f) ⊆ Work.Serre.csrV n Y ι f := by
    rintro z ⟨y, rfl⟩ ⟨i, hi⟩
    refine Work.RatHurewicz.cellOrigin_notMem_range_attachIncl (f := f) i ?_
    change Work.Serre.csrCentre n Y ι f i ∈ Set.range (Work.RatHurewicz.attachIncl n Y ι f)
    exact hi ▸ ⟨y, rfl⟩
  have hScl : IsClosed (Set.range (Work.RatHurewicz.attachIncl n Y ι f)) :=
    Work.RatHurewicz.isClosed_range_attachIncl
  -- (a) the vanishing over `(V,S)`
  have hvanV : ∀ j ≤ N + 2, CategoryTheory.Limits.IsZero (Work.Thom.RelCoh ℚ j
      ↥(Work.Serre.csrV n Y ι f)
      {x : ↥(Work.Serre.csrV n Y ι f) |
        (x : Work.RatHurewicz.attachCells n Y ι f) ∈
          Set.range (Work.RatHurewicz.attachIncl n Y ι f)}) := by
    intro j _
    exact Work.Serre.DiscPair.isZero_relCoh_of_isZero_relH_rat
      {x : ↥(Work.Serre.csrV n Y ι f) |
        (x : Work.RatHurewicz.attachCells n Y ι f) ∈
          Set.range (Work.RatHurewicz.attachIncl n Y ι f)} j
      (Work.Stems.Engine.isZero_relChainsR_rat_of_isZero_relChains _ _ j
        (Work.Serre.csrCompress n Y ι f q hq j).1)
  -- (b) the vanishing over `(q⁻¹V, q⁻¹S)`
  have hvanBS : ∀ k : ℕ, CategoryTheory.Limits.IsZero (Work.Thom.RelCoh ℚ k
      ↥(q ⁻¹' Work.Serre.csrV n Y ι f)
      {x : ↥(q ⁻¹' Work.Serre.csrV n Y ι f) |
        (x : E) ∈ q ⁻¹' (Set.range (Work.RatHurewicz.attachIncl n Y ι f))}) := by
    intro k
    exact Work.Serre.DiscPair.isZero_relCoh_of_isZero_relH_rat
      {x : ↥(q ⁻¹' Work.Serre.csrV n Y ι f) |
        (x : E) ∈ q ⁻¹' (Set.range (Work.RatHurewicz.attachIncl n Y ι f))} k
      (Work.Stems.Engine.isZero_relChainsR_rat_of_isZero_relChains _ _ k
        (Work.Serre.csrCompress n Y ι f q hq k).2)
  -- the explicit homeomorphism between the source and the bottom copy of the mapping cylinder
  obtain ⟨e, he⟩ := Work.Serre.cylHomeoExplicit q
  have hret : ∀ p : E, (Work.Serre.cylRetract q) (Work.Serre.cylIncl q p) = q p :=
    fun p => ContinuousMap.congr_fun (Work.Serre.cylRetract_cylIncl q) p
  have hmem : ∀ x : ↥(q ⁻¹' Work.Serre.csrV n Y ι f),
      (e (x : E) : Work.Serre.cyl q) ∈
        Work.Serre.cylBot q ∩ Work.Serre.cylPre q (Work.Serre.csrV n Y ι f) := by
    intro x
    refine ⟨(e (x : E)).2, ?_⟩
    show (Work.Serre.cylRetract q) (e (x : E) : Work.Serre.cyl q) ∈ Work.Serre.csrV n Y ι f
    rw [he (x : E), hret (x : E)]
    exact x.2
  have hmeminv : ∀ y : ↥(Work.Serre.cylBot q ∩
        Work.Serre.cylPre q (Work.Serre.csrV n Y ι f)),
      q (e.symm ⟨y.1, y.2.1⟩) ∈ Work.Serre.csrV n Y ι f := by
    intro y
    rw [← hret (e.symm ⟨y.1, y.2.1⟩), ← he (e.symm ⟨y.1, y.2.1⟩)]
    rw [show ((e (e.symm ⟨y.1, y.2.1⟩) : ↥(Work.Serre.cylBot q)) : Work.Serre.cyl q) = y.1
      from by rw [Homeomorph.apply_symm_apply]]
    exact y.2.2
  let g : ↥(q ⁻¹' Work.Serre.csrV n Y ι f) ≃ₜ
      ↥(Work.Serre.cylBot q ∩ Work.Serre.cylPre q (Work.Serre.csrV n Y ι f)) :=
    { toFun := fun x => ⟨(e (x : E) : Work.Serre.cyl q), hmem x⟩
      invFun := fun y => ⟨e.symm ⟨y.1, y.2.1⟩, hmeminv y⟩
      left_inv := fun x => Subtype.ext (e.symm_apply_apply (x : E))
      right_inv := fun y => Subtype.ext (by
        show ((e (e.symm ⟨y.1, y.2.1⟩) : ↥(Work.Serre.cylBot q)) : Work.Serre.cyl q) = y.1
        rw [Homeomorph.apply_symm_apply])
      continuous_toFun := by
        refine Continuous.subtype_mk ?_ hmem
        exact continuous_subtype_val.comp (e.continuous.comp continuous_subtype_val)
      continuous_invFun := by
        have hf : Continuous fun y : ↥(Work.Serre.cylBot q ∩
            Work.Serre.cylPre q (Work.Serre.csrV n Y ι f)) =>
            e.symm ⟨y.1, y.2.1⟩ :=
          e.symm.continuous.comp
            (Continuous.subtype_mk continuous_subtype_val (fun y => y.2.1))
        exact Continuous.subtype_mk hf hmeminv }
  have hgB : ∀ x : ↥(q ⁻¹' Work.Serre.csrV n Y ι f),
      x ∈ {z : ↥(q ⁻¹' Work.Serre.csrV n Y ι f) |
          (z : E) ∈ q ⁻¹' (Set.range (Work.RatHurewicz.attachIncl n Y ι f))} ↔
        g x ∈ {y : ↥(Work.Serre.cylBot q ∩
            Work.Serre.cylPre q (Work.Serre.csrV n Y ι f)) |
          (y : Work.Serre.cyl q) ∈ Work.Serre.cylPre q
            (Set.range (Work.RatHurewicz.attachIncl n Y ι f))} := by
    intro x
    show (x : E) ∈ q ⁻¹' (Set.range (Work.RatHurewicz.attachIncl n Y ι f)) ↔
      (e (x : E) : Work.Serre.cyl q) ∈
        Work.Serre.cylPre q (Set.range (Work.RatHurewicz.attachIncl n Y ι f))
    rw [Set.mem_preimage, he (x : E), ← hret (x : E)]
    rfl
  -- the bottom copy over `V`, relative to the bottom copy over `S`
  have htrimC : ∀ k : ℕ, CategoryTheory.Limits.IsZero (Work.Thom.RelCoh ℚ k
      ↥(Work.Serre.cylBot q ∩ Work.Serre.cylPre q (Work.Serre.csrV n Y ι f))
      {y : ↥(Work.Serre.cylBot q ∩ Work.Serre.cylPre q (Work.Serre.csrV n Y ι f)) |
        (y : Work.Serre.cyl q) ∈
          Work.Serre.cylPre q (Set.range (Work.RatHurewicz.attachIncl n Y ι f))}) := by
    intro k
    obtain ⟨iso⟩ := Work.Thom.relCohHomeomorph
      {z : ↥(q ⁻¹' Work.Serre.csrV n Y ι f) |
        (z : E) ∈ q ⁻¹' (Set.range (Work.RatHurewicz.attachIncl n Y ι f))}
      {y : ↥(Work.Serre.cylBot q ∩ Work.Serre.cylPre q (Work.Serre.csrV n Y ι f)) |
        (y : Work.Serre.cyl q) ∈
          Work.Serre.cylPre q (Set.range (Work.RatHurewicz.attachIncl n Y ι f))}
      g hgB ℚ k
    exact (hvanBS k).of_iso iso
  -- the collar part of `trimAp`, relative to its part over `S`
  have hF3 : ∀ k : ℕ, CategoryTheory.Limits.IsZero (Work.Thom.RelCoh ℚ k
      ↥{x : ↥(Work.Serre.cylPre q (Work.Serre.csrV n Y ι f)) |
          (x : Work.Serre.cyl q) ∈ Work.Serre.cylBot q ∨
            (x : Work.Serre.cyl q) ∈
              Work.Serre.cylPre q (Set.range (Work.RatHurewicz.attachIncl n Y ι f))}
      {y : ↥{x : ↥(Work.Serre.cylPre q (Work.Serre.csrV n Y ι f)) |
            (x : Work.Serre.cyl q) ∈ Work.Serre.cylBot q ∨
              (x : Work.Serre.cyl q) ∈
                Work.Serre.cylPre q (Set.range (Work.RatHurewicz.attachIncl n Y ι f))} |
        ((y : ↥(Work.Serre.cylPre q (Work.Serre.csrV n Y ι f))) : Work.Serre.cyl q) ∈
          Work.Serre.cylPre q (Set.range (Work.RatHurewicz.attachIncl n Y ι f))}) := by
    intro k
    obtain ⟨iso4⟩ := Work.Serre.DiscPair.relCoh_subtype_restrict
      (Work.Serre.cylPre q (Work.Serre.csrV n Y ι f)) (Work.Serre.cylBot q)
      (Work.Serre.cylPre q (Set.range (Work.RatHurewicz.attachIncl n Y ι f))) ℚ k
    obtain ⟨isoTrim⟩ := Work.Serre.DiscPair.relCoh_cylBot_trimming q
      (Set.range (Work.RatHurewicz.attachIncl n Y ι f)) (Work.Serre.csrV n Y ι f) hSV k
    exact ((htrimC k).of_iso iso4).of_iso isoTrim
  -- (c) the assembled vanishing over the pair of `hvanX`
  have hvanX : ∀ j ≤ N + 2, CategoryTheory.Limits.IsZero (Work.Thom.RelCoh ℚ j
      ↥(Work.Serre.cylPre q (Work.Serre.csrV n Y ι f))
      {x : ↥(Work.Serre.cylPre q (Work.Serre.csrV n Y ι f)) |
        (x : Work.Serre.cyl q) ∈ Work.Serre.cylBot q ∨
          (x : Work.Serre.cyl q) ∈
            Work.Serre.cylPre q (Set.range (Work.RatHurewicz.attachIncl n Y ι f))}) := by
    intro j hj
    have hsub : {x : ↥(Work.Serre.cylPre q (Work.Serre.csrV n Y ι f)) |
          (x : Work.Serre.cyl q) ∈
            Work.Serre.cylPre q (Set.range (Work.RatHurewicz.attachIncl n Y ι f))} ⊆
        {x : ↥(Work.Serre.cylPre q (Work.Serre.csrV n Y ι f)) |
          (x : Work.Serre.cyl q) ∈ Work.Serre.cylBot q ∨
            (x : Work.Serre.cyl q) ∈
              Work.Serre.cylPre q (Set.range (Work.RatHurewicz.attachIncl n Y ι f))} :=
      fun x hx => Or.inr hx
    have hQz : CategoryTheory.Limits.IsZero (Work.Thom.RelCoh ℚ j
        ↥(Work.Serre.cylPre q (Work.Serre.csrV n Y ι f))
        {x : ↥(Work.Serre.cylPre q (Work.Serre.csrV n Y ι f)) |
          (x : Work.Serre.cyl q) ∈
            Work.Serre.cylPre q (Set.range (Work.RatHurewicz.attachIncl n Y ι f))}) :=
      ModuleCat.isZero_iff_subsingleton.mpr
        (Work.Serre.DiscPair.subsingleton_relCoh_cylPre q
          (Set.range (Work.RatHurewicz.attachIncl n Y ι f))
          (Work.Serre.csrV n Y ι f) hSV N hvanV j hj)
    have hI : CategoryTheory.IsIso (Work.Thom.relCohMap
        (ContinuousMap.id ↥(Work.Serre.cylPre q (Work.Serre.csrV n Y ι f)))
        {x : ↥(Work.Serre.cylPre q (Work.Serre.csrV n Y ι f)) |
          (x : Work.Serre.cyl q) ∈
            Work.Serre.cylPre q (Set.range (Work.RatHurewicz.attachIncl n Y ι f))}
        {x : ↥(Work.Serre.cylPre q (Work.Serre.csrV n Y ι f)) |
          (x : Work.Serre.cyl q) ∈ Work.Serre.cylBot q ∨
            (x : Work.Serre.cyl q) ∈
              Work.Serre.cylPre q (Set.range (Work.RatHurewicz.attachIncl n Y ι f))}
        hsub ℚ j) :=
      Work.Serre.DiscPair.isIso_relCohMap_id_of_vanishingRV _ _ hsub j
        (fun k _ => ModuleCat.isZero_iff_subsingleton.mp (hF3 k))
    haveI := hI
    exact hQz.of_iso (asIso (Work.Thom.relCohMap
      (ContinuousMap.id ↥(Work.Serre.cylPre q (Work.Serre.csrV n Y ι f)))
      {x : ↥(Work.Serre.cylPre q (Work.Serre.csrV n Y ι f)) |
        (x : Work.Serre.cyl q) ∈
          Work.Serre.cylPre q (Set.range (Work.RatHurewicz.attachIncl n Y ι f))}
      {x : ↥(Work.Serre.cylPre q (Work.Serre.csrV n Y ι f)) |
        (x : Work.Serre.cyl q) ∈ Work.Serre.cylBot q ∨
          (x : Work.Serre.cyl q) ∈
            Work.Serre.cylPre q (Set.range (Work.RatHurewicz.attachIncl n Y ι f))}
      hsub ℚ j))
  exact Work.Serre.DiscPair.thomCylAt_of_relVanishing q r N
    (Set.range (Work.RatHurewicz.attachIncl n Y ι f)) (Work.Serre.csrV n Y ι f)
    hSV hScl hVop hvanV hvanX IH


end Work.Serre.DiscPair
