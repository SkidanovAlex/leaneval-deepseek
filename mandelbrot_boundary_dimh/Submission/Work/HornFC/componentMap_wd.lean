import Mathlib

open Set

namespace Work.HornFC

/-- If `g` is continuous on an open set `P` and maps `P` into itself, then `g` sends each
connected component `C` of `P` into a single connected component of `P`: for any two points
`z, z'` of `C`, the components of `P` through `g z` and `g z'` coincide.

The hypotheses `IsOpen P` and `Set.MapsTo g P P` are what the caller of this lemma records;
the argument itself only uses the continuity of `g` on `C` and that `g` maps `C` into `P`. -/
theorem componentMap_wd {P : Set ℂ} (hP : IsOpen P) {g : ℂ → ℂ} (hg : ContinuousOn g P)
    (hmap : Set.MapsTo g P P) {C : Set ℂ} (hC : ∃ z ∈ P, C = connectedComponentIn P z)
    {z z' : ℂ} (hz : z ∈ C) (hz' : z' ∈ C) :
    connectedComponentIn P (g z) = connectedComponentIn P (g z') := by
  -- `C` is a connected component of `P`, hence preconnected and contained in `P`.
  obtain ⟨w, _hwP, hCw⟩ := hC
  have hCpre : IsPreconnected C := hCw ▸ isPreconnected_connectedComponentIn
  have hCsubP : C ⊆ P := hCw ▸ connectedComponentIn_subset P w
  -- `g` is continuous on `C`, so `g '' C` is preconnected; it lies in `P`.
  have himg : IsPreconnected (g '' C) := hCpre.image g (hg.mono hCsubP)
  have hsub : g '' C ⊆ P := by
    rintro _ ⟨x, hx, rfl⟩
    exact hmap (hCsubP hx)
  -- Both `g z` and `g z'` lie in `g '' C`, which is a preconnected subset of `P`
  -- containing `g z`, so it sits inside the component of `P` through `g z`.
  have hmem : g z ∈ g '' C := ⟨z, hz, rfl⟩
  have hgz' : g z' ∈ connectedComponentIn P (g z) :=
    himg.subset_connectedComponentIn hmem hsub ⟨z', hz', rfl⟩
  -- Two components sharing a point are equal.
  exact connectedComponentIn_eq hgz'

end Work.HornFC
