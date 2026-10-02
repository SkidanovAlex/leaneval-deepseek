import Mathlib
import Submission.Work.FatouCoord.Basic

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.FatouCoord.Flower

theorem exists_antiFatou_of_pushforward {gU Φ : ℂ → ℂ} {Pa : Set ℂ}
    (hanti : Work.FatouCoord.IsAntiholomorphicOn gU Pa)
    (hΦdiff : DifferentiableOn ℂ Φ Pa) (hΦinj : Set.InjOn Φ Pa)
    (hgUinj : Set.InjOn gU Pa)
    (hkey : ∀ z ∈ Pa, gU z ∈ Pa → Φ (gU z) = star (Φ z) + 1 / 2) :
    ∃ φa : ℂ → ℂ, Work.FatouCoord.IsAntiholomorphicFatouOn gU φa Pa ∧ Set.InjOn φa Pa := by
  classical
  -- Extend `Φ` off `Pa`: on `Pa` keep `Φ`, on the extra points `gU '' Pa \ Pa` define the
  -- forced value `Φ (gU z) = star (Φ z) + 1/2` (well defined by injectivity of `gU` on `Pa`),
  -- and arbitrarily elsewhere.
  let φa : ℂ → ℂ := fun z =>
    if hz : z ∈ Pa then Φ z
    else if hzA : z ∈ gU '' Pa then star (Φ (Classical.choose hzA)) + 1 / 2
    else 0
  have hφa_on : ∀ z ∈ Pa, φa z = Φ z := by
    intro z hz
    simp only [φa, dite_eq_left hz]
  -- The key relation: on `Pa` the map `φa` satisfies `φa (gU z) = star (φa z) + 1/2`.
  have hrel : ∀ z ∈ Pa, φa (gU z) = star (φa z) + 1 / 2 := by
    intro z hz
    rw [hφa_on z hz]
    by_cases hgz : gU z ∈ Pa
    · rw [hφa_on (gU z) hgz, hkey z hz hgz]
    · have hmem : gU z ∈ gU '' Pa := ⟨z, hz, rfl⟩
      simp only [φa, dite_eq_right hgz, dite_eq_left hmem]
      have hspec := Classical.choose_spec hmem
      have hchoose : Classical.choose hmem = z := hgUinj hspec.1 hz hspec.2
      rw [hchoose]
  refine ⟨φa, ⟨hanti, ?_, hrel⟩, ?_⟩
  · exact hΦdiff.congr hφa_on
  · intro a ha b hb hab
    have h1 : φa a = Φ a := hφa_on a ha
    have h2 : φa b = Φ b := hφa_on b hb
    exact hΦinj ha hb (by rw [← h1, ← h2, hab])

end Work.FatouCoord.Flower
