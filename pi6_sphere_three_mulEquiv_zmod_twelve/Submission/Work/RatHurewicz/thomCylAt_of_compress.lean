import Mathlib
import Submission.Work.Serre.DiscPair.thomCylAt_csrV
import Submission.Work.Serre.CellStep.Tools
import Submission.Work.RatHurewicz.ExcisionSetup

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option synthInstance.maxHeartbeats 400000


/-!
# The `ThomCylAt` transport to a thickening of the old part

`Work.RatHurewicz.thomCylAt_of_compress` generalises the proof of
`Work.Serre.DiscPair.thomCylAt_csrV` (which is the case `V = csrV`, the complement of the cell
centres) to an *arbitrary* open `V` containing the closed old part `S`: if the pair `(V,S)` is
compressible in every dimension (so that `V` is a "thickening" of `S`), and the map `q` is a Serre
fibration, then `ThomCylAt r N (restrictFibre q S)` implies `ThomCylAt r N (restrictFibre q V)`.

The two inputs of the underlying `Work.Serre.DiscPair.thomCylAt_of_relVanishing` are the vanishing
of the relative cohomology of `(V,S)` (from the compression of the base pair) and of the pair
`(q⁻¹V, q⁻¹S)` of preimages (from the *base compression* of a Serre fibration, which is what the
Serre-fibration hypothesis and the composition of `q` with the relevant homotopies are needed for).
-/

namespace Work.RatHurewicz

open CategoryTheory CategoryTheory.Limits
open scoped Topology

theorem thomCylAt_of_compress (r N : ℕ) (hr : 1 ≤ r)
    {B : Type} [TopologicalSpace B] {E : Type} [TopologicalSpace E] (q : C(E, B))
    (hq : Work.StemsB.IsSerreFibration q)
    (S V : Set B) (hSV : S ⊆ V) (hScl : IsClosed S) (hVop : IsOpen V)
    (hcomp : ∀ d, Work.RatHurewicz.CompressRel ↥V {x : ↥V | (x : B) ∈ S} d)
    (IH : Work.Serre.ThomCylAt r N (Work.Serre.restrictFibre q S)) :
    Work.Serre.ThomCylAt r N (Work.Serre.restrictFibre q V) := by
  classical
    -- (a) the vanishing over `(V,S)`
    have hvanV : ∀ j ≤ N + 2, CategoryTheory.Limits.IsZero (Work.Thom.RelCoh ℚ j
        ↥(V)
        {x : ↥(V) |
          (x : B) ∈
            S}) := by
      intro j _
      exact Work.Serre.DiscPair.isZero_relCoh_of_isZero_relH_rat
        {x : ↥(V) |
          (x : B) ∈
            S} j
        (Work.Stems.Engine.isZero_relChainsR_rat_of_isZero_relChains _ _ j
          (Work.Serre.isZero_relChains_of_compress hcomp j))
    -- (b) the vanishing over `(q⁻¹V, q⁻¹S)`
    have hvanBS : ∀ k : ℕ, CategoryTheory.Limits.IsZero (Work.Thom.RelCoh ℚ k
        ↥(q ⁻¹' V)
        {x : ↥(q ⁻¹' V) |
          (x : E) ∈ q ⁻¹' (S)}) := by
      intro k
      exact Work.Serre.DiscPair.isZero_relCoh_of_isZero_relH_rat
        {x : ↥(q ⁻¹' V) |
          (x : E) ∈ q ⁻¹' (S)} k
        (Work.Stems.Engine.isZero_relChainsR_rat_of_isZero_relChains _ _ k
          (Work.Serre.isZero_relChains_preimage_of_compress q hq hSV hcomp k))
    -- the explicit homeomorphism between the source and the bottom copy of the mapping cylinder
    obtain ⟨e, he⟩ := Work.Serre.cylHomeoExplicit q
    have hret : ∀ p : E, (Work.Serre.cylRetract q) (Work.Serre.cylIncl q p) = q p :=
      fun p => ContinuousMap.congr_fun (Work.Serre.cylRetract_cylIncl q) p
    have hmem : ∀ x : ↥(q ⁻¹' V),
        (e (x : E) : Work.Serre.cyl q) ∈
          Work.Serre.cylBot q ∩ Work.Serre.cylPre q (V) := by
      intro x
      refine ⟨(e (x : E)).2, ?_⟩
      show (Work.Serre.cylRetract q) (e (x : E) : Work.Serre.cyl q) ∈ V
      rw [he (x : E), hret (x : E)]
      exact x.2
    have hmeminv : ∀ y : ↥(Work.Serre.cylBot q ∩
          Work.Serre.cylPre q (V)),
        q (e.symm ⟨y.1, y.2.1⟩) ∈ V := by
      intro y
      rw [← hret (e.symm ⟨y.1, y.2.1⟩), ← he (e.symm ⟨y.1, y.2.1⟩)]
      rw [show ((e (e.symm ⟨y.1, y.2.1⟩) : ↥(Work.Serre.cylBot q)) : Work.Serre.cyl q) = y.1
        from by rw [Homeomorph.apply_symm_apply]]
      exact y.2.2
    let g : ↥(q ⁻¹' V) ≃ₜ
        ↥(Work.Serre.cylBot q ∩ Work.Serre.cylPre q (V)) :=
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
              Work.Serre.cylPre q (V)) =>
              e.symm ⟨y.1, y.2.1⟩ :=
            e.symm.continuous.comp
              (Continuous.subtype_mk continuous_subtype_val (fun y => y.2.1))
          exact Continuous.subtype_mk hf hmeminv }
    have hgB : ∀ x : ↥(q ⁻¹' V),
        x ∈ {z : ↥(q ⁻¹' V) |
            (z : E) ∈ q ⁻¹' (S)} ↔
          g x ∈ {y : ↥(Work.Serre.cylBot q ∩
              Work.Serre.cylPre q (V)) |
            (y : Work.Serre.cyl q) ∈ Work.Serre.cylPre q
              (S)} := by
      intro x
      show (x : E) ∈ q ⁻¹' (S) ↔
        (e (x : E) : Work.Serre.cyl q) ∈
          Work.Serre.cylPre q (S)
      rw [Set.mem_preimage, he (x : E), ← hret (x : E)]
      rfl
    -- the bottom copy over `V`, relative to the bottom copy over `S`
    have htrimC : ∀ k : ℕ, CategoryTheory.Limits.IsZero (Work.Thom.RelCoh ℚ k
        ↥(Work.Serre.cylBot q ∩ Work.Serre.cylPre q (V))
        {y : ↥(Work.Serre.cylBot q ∩ Work.Serre.cylPre q (V)) |
          (y : Work.Serre.cyl q) ∈
            Work.Serre.cylPre q (S)}) := by
      intro k
      obtain ⟨iso⟩ := Work.Thom.relCohHomeomorph
        {z : ↥(q ⁻¹' V) |
          (z : E) ∈ q ⁻¹' (S)}
        {y : ↥(Work.Serre.cylBot q ∩ Work.Serre.cylPre q (V)) |
          (y : Work.Serre.cyl q) ∈
            Work.Serre.cylPre q (S)}
        g hgB ℚ k
      exact (hvanBS k).of_iso iso
    -- the collar part of `trimAp`, relative to its part over `S`
    have hF3 : ∀ k : ℕ, CategoryTheory.Limits.IsZero (Work.Thom.RelCoh ℚ k
        ↥{x : ↥(Work.Serre.cylPre q (V)) |
            (x : Work.Serre.cyl q) ∈ Work.Serre.cylBot q ∨
              (x : Work.Serre.cyl q) ∈
                Work.Serre.cylPre q (S)}
        {y : ↥{x : ↥(Work.Serre.cylPre q (V)) |
              (x : Work.Serre.cyl q) ∈ Work.Serre.cylBot q ∨
                (x : Work.Serre.cyl q) ∈
                  Work.Serre.cylPre q (S)} |
          ((y : ↥(Work.Serre.cylPre q (V))) : Work.Serre.cyl q) ∈
            Work.Serre.cylPre q (S)}) := by
      intro k
      obtain ⟨iso4⟩ := Work.Serre.DiscPair.relCoh_subtype_restrict
        (Work.Serre.cylPre q (V)) (Work.Serre.cylBot q)
        (Work.Serre.cylPre q (S)) ℚ k
      obtain ⟨isoTrim⟩ := Work.Serre.DiscPair.relCoh_cylBot_trimming q
        (S) (V) hSV k
      exact ((htrimC k).of_iso iso4).of_iso isoTrim
    -- (c) the assembled vanishing over the pair of `hvanX`
    have hvanX : ∀ j ≤ N + 2, CategoryTheory.Limits.IsZero (Work.Thom.RelCoh ℚ j
        ↥(Work.Serre.cylPre q (V))
        {x : ↥(Work.Serre.cylPre q (V)) |
          (x : Work.Serre.cyl q) ∈ Work.Serre.cylBot q ∨
            (x : Work.Serre.cyl q) ∈
              Work.Serre.cylPre q (S)}) := by
      intro j hj
      have hsub : {x : ↥(Work.Serre.cylPre q (V)) |
            (x : Work.Serre.cyl q) ∈
              Work.Serre.cylPre q (S)} ⊆
          {x : ↥(Work.Serre.cylPre q (V)) |
            (x : Work.Serre.cyl q) ∈ Work.Serre.cylBot q ∨
              (x : Work.Serre.cyl q) ∈
                Work.Serre.cylPre q (S)} :=
        fun x hx => Or.inr hx
      have hQz : CategoryTheory.Limits.IsZero (Work.Thom.RelCoh ℚ j
          ↥(Work.Serre.cylPre q (V))
          {x : ↥(Work.Serre.cylPre q (V)) |
            (x : Work.Serre.cyl q) ∈
              Work.Serre.cylPre q (S)}) :=
        ModuleCat.isZero_iff_subsingleton.mpr
          (Work.Serre.DiscPair.subsingleton_relCoh_cylPre q
            (S)
            (V) hSV N hvanV j hj)
      have hI : CategoryTheory.IsIso (Work.Thom.relCohMap
          (ContinuousMap.id ↥(Work.Serre.cylPre q (V)))
          {x : ↥(Work.Serre.cylPre q (V)) |
            (x : Work.Serre.cyl q) ∈
              Work.Serre.cylPre q (S)}
          {x : ↥(Work.Serre.cylPre q (V)) |
            (x : Work.Serre.cyl q) ∈ Work.Serre.cylBot q ∨
              (x : Work.Serre.cyl q) ∈
                Work.Serre.cylPre q (S)}
          hsub ℚ j) :=
        Work.Serre.DiscPair.isIso_relCohMap_id_of_vanishingRV _ _ hsub j
          (fun k _ => ModuleCat.isZero_iff_subsingleton.mp (hF3 k))
      haveI := hI
      exact hQz.of_iso (asIso (Work.Thom.relCohMap
        (ContinuousMap.id ↥(Work.Serre.cylPre q (V)))
        {x : ↥(Work.Serre.cylPre q (V)) |
          (x : Work.Serre.cyl q) ∈
            Work.Serre.cylPre q (S)}
        {x : ↥(Work.Serre.cylPre q (V)) |
          (x : Work.Serre.cyl q) ∈ Work.Serre.cylBot q ∨
            (x : Work.Serre.cyl q) ∈
              Work.Serre.cylPre q (S)}
        hsub ℚ j))
    exact Work.Serre.DiscPair.thomCylAt_of_relVanishing q r N
      (S) (V)
      hSV hScl hVop hvanV hvanX IH

end Work.RatHurewicz
