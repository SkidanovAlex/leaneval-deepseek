import Mathlib
import Submission.Work.Drive.Mono.Geom2Defs
import Submission.Work.Drive.Mono.BoxGenE
import Submission.Work.Drive.Mono.junctionGenC_of_arcs

namespace Work.Drive.Mono

/-- **The junction bundle from the data bundle with the trace arcs.**

This is pure bookkeeping around the proved `Work.Drive.Mono.junctionGenC_of_arcs`: the bundle
`Work.Drive.Mono.Geom2DataPlus` carries

* all the hypotheses of `junctionGenC_of_arcs` except clause (c) of `JunctionGenC` and the
  no-corner-face condition — the arc family `γ` with its height parametrisation, its `C³` regularity,
  its face property, the cover of the box trace in the closed slab away from the box-edge points, and
  the two arc genericity conditions `harcℓ`, `harcv`;
* the finiteness of the surface's points on the **edges** of the box sphere inside the closed slab
  (`Geom2Data`'s `cornerSlab`), which yields clause (c) by putting the (finitely many, in-window)
  `ℓ`-values of those points into `exc`;
* the no-corner-face condition (`Geom2DataPlus`'s last conjunct);
* the window conditions `hwin` (`Geom2Data`'s `winC`) and `hexcWin` (`TiltData`).

Hence, given `Work.Drive.Mono.BoxGen` (from the `BoxGenE` hypothesis of the crux), every datum
satisfying `Geom2DataPlus` also satisfies `JunctionGenC` with an exceptional set enlarged by a finite
set of levels inside the window. -/
theorem junctionGenC_of_geom2DataPlus
    (ψ : Submission.Diffeo) (K : LeanEval.KnotTheory.PardonDistortion.Knot) {r s u : ℝ}
    (hr : 0 < r) (hrs : r < s)
    (c : LeanEval.KnotTheory.PardonDistortion.R3) (σ : Equiv.Perm (Fin 3)) (p q : ℕ)
    (v : LeanEval.KnotTheory.PardonDistortion.R3) (h R : ℝ)
    (ℓ : LeanEval.KnotTheory.PardonDistortion.R3 →L[ℝ] ℝ) (exc : Finset ℝ) (lam0 lam1 : ℝ)
    (hBG : Work.Drive.Mono.BoxGen ψ c σ s)
    (hG : Work.Drive.Mono.Geom2DataPlus ψ K s u c σ v h R ℓ exc lam0 lam1 p q) :
    ∃ B : Finset ℝ, (∀ t ∈ B, lam0 < t ∧ t < lam1) ∧
      Work.Drive.Mono.JunctionGenC ψ s c σ u v h ℓ (exc ∪ B) lam0 lam1 := by
  classical
  -- unpack the data bundle
  obtain ⟨hTilt, hwinC, _hSlabCuts, _hlne, _hthin, _hvclose, _htraceBand, hcornerSlab,
    _hfaceReg, _hnograzBox, _hnograzD, _hℓK, _hvgraz, _hexcK, _hcount, _hoffK, _hknotGP,
    _hevFace, _hevBend, _hevTriple⟩ := hG.1
  obtain ⟨_hGen, _hvnorm, _hℓne, _hℓv, _hsize, _hhpos, _hboxR, _hwin0, _hwin1, _hlamlt,
    hexcWin⟩ := hTilt
  obtain ⟨_N, _γ, _η, hη, hγ, hγh, hγβ, hcover, harcℓ, harcv⟩ := hG.2.1
  have hnoCornerFace := hG.2.2
  have hs : 0 < s := lt_trans hr hrs
  -- the levels of the box-edge points of the closed slab: clause (c) of the bundle
  set F : Finset LeanEval.KnotTheory.PardonDistortion.R3 := hcornerSlab.toFinset with hF
  set B₀ : Finset ℝ := F.image ℓ with hB₀
  have hcornerC : ∀ z : LeanEval.KnotTheory.PardonDistortion.R3,
      z ∈ (Work.Drive.EpsSphere.torusOf ψ).carrier → Submission.boxNorm c σ z = s →
      |inner ℝ v z - (inner ℝ v c + u)| ≤ h →
      (∃ i j : Fin 3, i ≠ j ∧ |z (σ i) - c (σ i)| = Submission.boxSide i * s ∧
        |z (σ j) - c (σ j)| = Submission.boxSide j * s) →
      ℓ z ∈ ((exc ∪ B₀ : Finset ℝ) : Set ℝ) := by
    intro z hz hzbox hslab hext
    refine Finset.mem_coe.mpr (Finset.mem_union_right exc ?_)
    refine Finset.mem_image.mpr ⟨z, ?_, rfl⟩
    exact (Set.Finite.mem_toFinset hcornerSlab).mpr ⟨hz, hzbox, hslab, hext⟩
  -- the enlarged exceptional set stays inside the window
  have hexcWin' : ∀ t ∈ (exc ∪ B₀ : Finset ℝ), lam0 < t ∧ t < lam1 := by
    intro t ht
    rw [Finset.mem_union] at ht
    rcases ht with h1 | h2
    · exact hexcWin t h1
    · obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp h2
      obtain ⟨hzcar, hzbox, -⟩ := (Set.Finite.mem_toFinset hcornerSlab).mp hz
      have hfr : z ∈ frontier (Submission.PBox s c σ) := by
        rw [Work.Topology.SphereSlicing.frontier_PBox hs c σ]
        exact hzbox
      exact hwinC z (frontier_subset_closure hfr)
  -- the proved arcs lemma
  obtain ⟨exc', hsub, hexc'Win, hJG⟩ :=
    Work.Drive.Mono.junctionGenC_of_arcs ψ hs c σ v h ℓ (exc ∪ B₀) lam0 lam1 hBG hcornerC
      hnoCornerFace hη hγ hγh hγβ hcover harcℓ harcv hwinC hexcWin'
  refine ⟨exc', hexc'Win, ?_⟩
  have hsubexc : exc ⊆ exc' := fun t ht => hsub t (Finset.mem_union_left B₀ ht)
  rw [Finset.union_eq_right.mpr hsubexc]
  exact hJG

end Work.Drive.Mono
