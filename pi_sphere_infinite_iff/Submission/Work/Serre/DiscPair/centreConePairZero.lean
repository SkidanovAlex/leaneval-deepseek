import Mathlib
import Submission.Work.Serre.C1Cyl
import Submission.Work.StemsB.RelChainsR
import Submission.Work.Serre.csrDefs
import Submission.Work.RatHurewicz.AttachCells
import Submission.Work.StemsB.Fibrations
import Submission.Work.RatHurewicz.Cofibre.subsingleton_homology_zero_relChains
import Submission.Work.Serre.Csr.Base

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The zeroth relative homology of the cone pair of a fibre

For a continuous map `q : X → Z` and a point `z : Z`, the preimage
`P := (cylRetract q) ⁻¹' {z} ⊆ cyl q` of `z` under the retraction of the mapping cylinder onto its
target is the **cone on the fibre** `F := q ⁻¹' {z}`: its apex is the point of the target copy, its
base the copy of `F` at the bottom of the cylinder.  The companion file `centreConePair.lean`
computes the relative homology of the cone pair in positive degrees,

`H_k(P, F; ℚ) ≅ H_{k-1}(F; ℚ)`   (`k ≥ 1`),

and `Work.Serre.DiscPair.centreConePairZero` is the remaining degree-`0` case: since `P` is a cone
it is path connected, and `F` (the base) is nonempty as soon as the fibre is nonempty, so the
degree-`0` map `H_0(F; ℚ) → H_0(P; ℚ)` is onto and `H_0(P, F; ℚ) = 0`.

The geometric input is the explicit "push to the apex" of the cone: for `y = ⟦(p,t)⟧` with
`q p = z` the path `s ↦ ⟦(p, (1-s)t + s)⟧` (`Work.Serre.unitIntervalLin`) runs from `y` to the
apex `⟦z⟧`.  Every point of `P` is joined to the apex by such a path, so `P` is path connected.
-/

namespace Work.Serre.DiscPair

open scoped Topology unitInterval
open CategoryTheory CategoryTheory.Limits

noncomputable section

variable {P X : Type} [TopologicalSpace P] [TopologicalSpace X]

/-! ## Elementary computations in the mapping cylinder -/

@[simp] lemma cylRetract_cylMk_inl (f : C(P, X)) (p : P) (t : unitInterval) :
    Work.Serre.cylRetract f (Work.Serre.cylMk f (Sum.inl (p, t))) = f p := rfl

@[simp] lemma cylRetract_cylMk_inr (f : C(P, X)) (x : X) :
    Work.Serre.cylRetract f (Work.Serre.cylMk f (Sum.inr x)) = x := rfl

@[simp] lemma cylRetract_cylInr (f : C(P, X)) (z : X) :
    Work.Serre.cylRetract f (Work.Serre.cylInr f z) = z := rfl

/-- Continuity of the second variable of `Work.Serre.unitIntervalLin`. -/
lemma continuous_unitIntervalLin_right (t : unitInterval) :
    Continuous fun s : unitInterval => Work.Serre.unitIntervalLin s t := by
  refine Continuous.subtype_mk ?_ _
  show Continuous fun s : unitInterval => (1 - (s : ℝ)) * (t : ℝ) + (s : ℝ)
  fun_prop

/-- The **apex** of the mapping cylinder of `f` over `z`, viewed as a point of the preimage
`(cylRetract f) ⁻¹' {z}`: the point of the target copy lying over `z`. -/
def cylPreimageApex (f : C(P, X)) (z : X) :
    ↥((Work.Serre.cylRetract f) ⁻¹' {z}) :=
  ⟨Work.Serre.cylInr f z, by
    rw [Set.mem_preimage, Set.mem_singleton_iff]
    exact cylRetract_cylInr f z⟩

/-! ## Every point of the cone is joined to the apex -/

/-- **Every point of `(cylRetract f) ⁻¹' {z}` is joined to the apex by a path inside the preimage.**
For a point represented by `⟦(p,t)⟧` with `f p = z` the path is `s ↦ ⟦(p, (1-s)t + s)⟧`, whose
image consists again of points `⟦(p,·)⟧` and hence lies in the preimage; it ends at
`⟦(p,1)⟧ = cylInr f (f p) = apex`. -/
theorem exists_path_cylPreimage_apex (f : C(P, X)) (z : X)
    (y : ↥((Work.Serre.cylRetract f) ⁻¹' {z})) :
    Nonempty (Path y (cylPreimageApex f z)) := by
  have key : ∀ (a : (P × unitInterval) ⊕ X),
      ∀ (h : Work.Serre.cylMk f a ∈ (Work.Serre.cylRetract f) ⁻¹' {z}),
        Nonempty (Path (⟨Work.Serre.cylMk f a, h⟩ :
          ↥((Work.Serre.cylRetract f) ⁻¹' {z})) (cylPreimageApex f z)) := by
    rintro (⟨p, t⟩ | x) h
    · have hp : f p = z := by
        have h1 := h
        rw [Set.mem_preimage, Set.mem_singleton_iff] at h1
        simpa using h1
      have hmem : ∀ s : unitInterval,
          Work.Serre.cylMk f (Sum.inl (p, Work.Serre.unitIntervalLin s t))
            ∈ (Work.Serre.cylRetract f) ⁻¹' {z} := fun s => by
        rw [Set.mem_preimage, Set.mem_singleton_iff]
        simp [hp]
      refine ⟨{ toFun := fun s =>
                  ⟨Work.Serre.cylMk f (Sum.inl (p, Work.Serre.unitIntervalLin s t)), hmem s⟩
                continuous_toFun := Continuous.subtype_mk ?_ hmem
                source' := ?_
                target' := ?_ }⟩
      · exact continuous_quotient_mk'.comp (continuous_inl.comp
          (continuous_const.prodMk (continuous_unitIntervalLin_right t)))
      · apply Subtype.ext
        rw [Work.Serre.unitIntervalLin_zero_left]
      · refine Subtype.ext ?_
        show Work.Serre.cylMk f (Sum.inl (p, Work.Serre.unitIntervalLin 1 t))
          = Work.Serre.cylInr f z
        rw [Work.Serre.unitIntervalLin_one_left]
        exact (Work.Serre.cyl_mk_inl_one f p).trans (congrArg (Work.Serre.cylInr f) hp)
    · have hx : x = z := by
        have h1 := h
        rw [Set.mem_preimage, Set.mem_singleton_iff] at h1
        simpa using h1
      have heq : (⟨Work.Serre.cylMk f (Sum.inr x), h⟩ :
            ↥((Work.Serre.cylRetract f) ⁻¹' {z})) = cylPreimageApex f z := by
        apply Subtype.ext
        show Work.Serre.cylMk f (Sum.inr x) = Work.Serre.cylInr f z
        rw [show Work.Serre.cylMk f (Sum.inr x) = Work.Serre.cylInr f x from rfl, hx]
      exact ⟨Path.cast (Path.refl (cylPreimageApex f z)) heq rfl⟩
  exact Quotient.inductionOn y.1 (motive := fun u =>
      ∀ h : u ∈ (Work.Serre.cylRetract f) ⁻¹' {z},
        Nonempty (Path (⟨u, h⟩ : ↥((Work.Serre.cylRetract f) ⁻¹' {z})) (cylPreimageApex f z)))
    key y.2

/-- **The preimage of a point under the retraction of the mapping cylinder is path connected.**
It is the cone on the fibre, and every point is joined to the apex. -/
theorem pathConnectedSpace_cylPreimage (f : C(P, X)) (z : X) :
    PathConnectedSpace ↥((Work.Serre.cylRetract f) ⁻¹' {z}) :=
  PathConnectedSpace.mk ⟨cylPreimageApex f z⟩ (fun x y => by
    obtain ⟨p⟩ := exists_path_cylPreimage_apex f z x
    obtain ⟨q⟩ := exists_path_cylPreimage_apex f z y
    exact ⟨p.trans q.symm⟩)

/-! ## The base of the cone is nonempty as soon as the fibre is -/

/-- **The bottom copy of the fibre inside the cone is nonempty** when the fibre is: the point
`cylIncl f x` for `x` with `f x = z` lies in the preimage of `z` and in the bottom copy. -/
theorem nonempty_cylPreimageBase (f : C(P, X)) (z : X) (x : P) (hx : f x = z) :
    Nonempty ↥({w : ↥((Work.Serre.cylRetract f) ⁻¹' {z}) |
      (w : Work.Serre.cyl f) ∈ Set.range (Work.Serre.cylIncl f)}) := by
  have h1 : Work.Serre.cylRetract f (Work.Serre.cylIncl f x) = z := by
    rw [show Work.Serre.cylRetract f (Work.Serre.cylIncl f x) = f x from rfl, hx]
  exact ⟨⟨⟨Work.Serre.cylIncl f x, by
      rw [Set.mem_preimage, Set.mem_singleton_iff]; exact h1⟩, ⟨x, rfl⟩⟩⟩

/-! ## The degree-`0` cone pair of a fibre -/

/-- **The degree-`0` relative homology of the cone pair of a fibre vanishes.**

`P := (cylRetract q) ⁻¹' {z}` is the cone on the fibre `F := q ⁻¹' {z}` (apex the target copy of
`z`, base the bottom copy of `F`).  It is path connected, and `F` is nonempty as soon as the fibre
is, so `H_0(F; ℚ) → H_0(P; ℚ)` is onto and `H_0(P, F; ℚ) = 0`. -/
theorem centreConePairZero (D : ℕ) (hD : 2 ≤ D) (Γ : Type) [TopologicalSpace Γ] (ι : Type)
    (f : ι → C(Work.RatHurewicz.cellSphere (D-2), Γ)) {X : Type} [TopologicalSpace X]
    (q : C(X, Work.RatHurewicz.attachCells (D-2) Γ ι f)) (hq : Work.StemsB.IsSerreFibration q)
    (hne : ∀ i : ι, Nonempty (Work.StemsB.fibre q (Work.Serre.csrCentre (D - 2) Γ ι f i)))
    (i : ι) :
    CategoryTheory.Limits.IsZero ((Work.StemsB.relChainsR ℚ
        (TopCat.of ↥((Work.Serre.cylRetract q) ⁻¹' {Work.Serre.csrCentre (D-2) Γ ι f i}))
        {x | (x : Work.Serre.cyl q) ∈ Set.range (Work.Serre.cylIncl q)}).homology 0) := by
  haveI hpc : PathConnectedSpace ↥(TopCat.of
      ↥((Work.Serre.cylRetract q) ⁻¹' {Work.Serre.csrCentre (D-2) Γ ι f i})) :=
    pathConnectedSpace_cylPreimage q (Work.Serre.csrCentre (D-2) Γ ι f i)
  obtain ⟨b⟩ := hne i
  obtain ⟨x, hx⟩ := b
  haveI hbase : Nonempty ↥({w : ↥(TopCat.of
        ↥((Work.Serre.cylRetract q) ⁻¹' {Work.Serre.csrCentre (D-2) Γ ι f i})) |
      (w : Work.Serre.cyl q) ∈ Set.range (Work.Serre.cylIncl q)}) :=
    nonempty_cylPreimageBase q (Work.Serre.csrCentre (D-2) Γ ι f i) x hx
  have hZ : IsZero ((Work.Cohomology.relChains (TopCat.of
      ↥((Work.Serre.cylRetract q) ⁻¹' {Work.Serre.csrCentre (D-2) Γ ι f i}))
      {x | (x : Work.Serre.cyl q) ∈ Set.range (Work.Serre.cylIncl q)}).homology 0) :=
    ModuleCat.isZero_iff_subsingleton.mpr
      (Work.RatHurewicz.Cofibre.subsingleton_homology_zero_relChains _ _)
  exact Work.Serre.Csr.isZero_relChainsR_rat_of_isZero_int _ _ 0 hZ

end

end Work.Serre.DiscPair
