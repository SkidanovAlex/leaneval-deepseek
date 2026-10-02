import Mathlib
import Submission.Work.ThomBordism.chartModelClassDefs
import Submission.Work.ThomBordism.relH_zeroSection_localisation_injective

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option linter.style.haveILetI false

namespace Work.ThomBordism

/-- **Injectivity of the homology localisation at a zero-section point, for the normal bundle.**
For the normal bundle `ν = NormalTotal E` of an embedded closed oriented smooth `8`-manifold and a
point `x : V.pt`, the map `H_{8+k}(ν, ν∖0) → H_{8+k}(ν, ν∖{0_x})` (the localisation at the
zero-section point `0_x`) is injective.

This is `Work.ThomBordism.relH_zeroSection_localisation_injective` transported to the concrete model
`ν = NormalTotal E` along the homeomorphism of pairs
`Work.Tubular.eucNormalHomeomorph E ND : (normalBundle E ND).TotalSpace ≅ NormalTotal E`; the
Z-world statement is proved by the localisation-locality plus Hatcher 3.27(a) (compactness of the
zero section). -/
theorem relH_localisation_injective_normalTotal {V : Work.ThomBordism.Man8} [ConnectedSpace V.pt]
    {k : ℕ} (hk : 1 ≤ k) (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k)) (x : V.pt) :
    Function.Injective (Work.ThomBordism.RelHmap (TopCat.of (Work.Tubular.NormalTotal E)) (8 + k)
      (A := ({Work.Tubular.zeroSectionNormal E x} : Set (Work.Tubular.NormalTotal E)))
      (B := Set.range (Work.Tubular.zeroSectionNormal E))
      (Set.singleton_subset_iff.mpr (Set.mem_range_self (f := Work.Tubular.zeroSectionNormal E) x))) := by
  classical
  -- the gluing-data model of the normal bundle, and its charted total space
  obtain ⟨ND⟩ := Work.ThomBordism.PontryaginThom.exists_normalData_of_immersion E.e
    (E.smooth.of_le (by simp)) E.injective_mfderiv
  obtain ⟨hChb⟩ := Work.ThomBordism.chartedSpaceTotalSpace hk (Work.Tubular.normalBundle E ND)
  letI : ChartedSpace (EuclideanSpace ℝ (Fin (8 + k)))
      (Work.Tubular.normalBundle E ND).TotalSpace := hChb
  -- transport the charted structure to the concrete normal total space along `eucNormalHomeomorph`;
  -- `compactZero_free` / `relHmap_eq_zero_of_eq_zero_at` are stated for an *arbitrary* such
  -- charted structure, so this is all that is needed.
  haveI : ChartedSpace (EuclideanSpace ℝ (Fin (8 + k))) (Work.Tubular.NormalTotal E) :=
    Homeomorph.chartedSpace (Work.Tubular.eucNormalHomeomorph E ND)
  intro β γ hβγ
  -- it suffices to prove that the kernel at one point of the zero section is trivial
  have hsub : Work.ThomBordism.RelHmap (TopCat.of (Work.Tubular.NormalTotal E)) (8 + k)
      (Set.singleton_subset_iff.mpr
        (Set.mem_range_self (f := Work.Tubular.zeroSectionNormal E) x)) (β - γ) = 0 := by
    rw [map_sub, hβγ, sub_self]
  have hA : IsCompact (Set.range (Work.Tubular.zeroSectionNormal E)) :=
    isCompact_range (Work.Tubular.zeroSectionNormal E).continuous
  have hpre : IsPreconnected (Set.range (Work.Tubular.zeroSectionNormal E)) :=
    isPreconnected_range (Work.Tubular.zeroSectionNormal E).continuous
  -- the localisation is locally constant along the connected zero section
  have hall := Work.ThomBordism.relHmap_eq_zero_of_eq_zero_at (n := 8 + k) (by omega) hA hpre
    (β - γ) (Set.mem_range_self (f := Work.Tubular.zeroSectionNormal E) x) hsub
  -- Hatcher 3.27(a): a class vanishing locally at every point of the compact zero section is zero
  have hzero : β - γ = 0 :=
    Work.ThomBordism.compactZero_free (n := 8 + k) (by omega) hA (β - γ) hall
  exact sub_eq_zero.mp hzero

end Work.ThomBordism
