import Mathlib
import Submission.Work.Serre.E3aModel
import Submission.Work.Serre.skeletonMap_kernel_of_iso
import Submission.Work.Serre.jointKillStepKernel

namespace Work.Serre

/-!
# The base stage of the `famSpace` route to `serreC3FiniteOne`

`Work.Serre.E3aModel.BaseSpace X pt` is the `1`-skeleton of `X` with one `2`-cell attached along a
representative loop of every element of `ker π₁(E3aModel.skelMap X pt)`; its X-side structure map
is `E3aModel.baseMap` (`baseMap_base`, `baseMap_pi1_bij`).

Given a group isomorphism `φ : π₁(X,pt) ≃* π₁(L,l₀)`, the claim below produces an `L`-side map on
the **same** space whose `π₁` is bijective (its kernel agrees with the X-side's by construction).

Ingredients, all already proved in this workspace:
* `Work.Serre.skeletonMap_kernel_of_iso pt l₀ φ` — a map `f' : Skeleton X pt → L` with
  `f' (skeletonBase X pt) = l₀`, `π₁(f')` surjective and
  `ker π₁(f') = ker π₁(E3aModel.skelMap X pt)`;
* `Work.Serre.attachG_killStep_bijective` — the extension of a based skeleton map over the killing
  cells, yielding bijectivity of `π₁`; apply it with the index set `E3aModel.KilIdx X pt` and the
  family `fun k => k.1`, whose two hypotheses are read off from the kernel equality above;
* `Work.Serre.CWModel.attachG` / `attachG_incl` for the resulting map.
-/
theorem baseStageFamMap {X : Type} [TopologicalSpace X] (pt : X)
    {L : Type} [TopologicalSpace L] (l₀ : L)
    (φ : HomotopyGroup (Fin 1) X pt ≃* HomotopyGroup (Fin 1) L l₀) :
    ∃ gL : C(Work.Serre.E3aModel.BaseSpace X pt, L),
      gL (Work.Serre.E3aModel.basePt X pt) = l₀ ∧
      Function.Bijective (Work.Serre.piMapN gL 1 (Work.Serre.E3aModel.basePt X pt)) := by
  classical
  obtain ⟨f', hbase, hsurj, hker⟩ :=
    Work.Serre.skeletonMap_kernel_of_iso pt l₀ φ
  -- the family `k ↦ k.1` of kernel elements lies in `ker π₁(f')` and covers it
  have hφker : ∀ k : Work.Serre.E3aModel.KilIdx X pt,
      Work.Serre.piMapN f' 1 (Work.Serre.E3aSk.skeletonBase X pt) k.1 = 1 :=
    fun k => (hker k.1).mpr k.2
  have hφsurj : ∀ α : HomotopyGroup (Fin 1) (Work.Serre.E3aSk.Skeleton X pt)
        (Work.Serre.E3aSk.skeletonBase X pt),
      Work.Serre.piMapN f' 1 (Work.Serre.E3aSk.skeletonBase X pt) α = 1 →
        ∃ k : Work.Serre.E3aModel.KilIdx X pt, k.1 = α :=
    fun α hα => ⟨⟨α, (hker α).mp hα⟩, rfl⟩
  obtain ⟨G, hG, hbij⟩ :=
    Work.Serre.attachG_killStep_bijective l₀ (Work.Serre.E3aSk.skeletonBase X pt) f' hbase hsurj
      (fun k : Work.Serre.E3aModel.KilIdx X pt => k.1) hφker hφsurj
  refine ⟨Work.Serre.CWModel.attachG 0 (Work.Serre.E3aSk.Skeleton X pt)
    (Work.Serre.E3aModel.KilIdx X pt) (Work.Serre.E3aModel.KilFam X pt) f' G hG, ?_, hbij⟩
  show Work.Serre.CWModel.attachG 0 (Work.Serre.E3aSk.Skeleton X pt)
      (Work.Serre.E3aModel.KilIdx X pt) (Work.Serre.E3aModel.KilFam X pt) f' G hG
      (Work.RatHurewicz.attachIncl 0 (Work.Serre.E3aSk.Skeleton X pt)
        (Work.Serre.E3aModel.KilIdx X pt) (Work.Serre.E3aModel.KilFam X pt)
        (Work.Serre.E3aSk.skeletonBase X pt)) = l₀
  rw [Work.Serre.CWModel.attachG_incl]
  exact hbase

end Work.Serre
