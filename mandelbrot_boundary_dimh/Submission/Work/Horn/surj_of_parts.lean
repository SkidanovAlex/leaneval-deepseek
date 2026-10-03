import Mathlib
import Submission.Work.Interfaces.HornParts
import Submission.Work.Horn.surj_aux

/-!
# `Work.Horn.surj_of_parts` — surjectivity of the lifted horn map on each horn component

`Work.Horn.E_image_univ_of_varphi_image` (in `Horn/surj_aux.lean`) turns the inclusion
`B \ critOrbit f₀ c ⊆ φ '' BuOf` (proved in `Horn/varphi_image_BuOf.lean`) into
`d.E '' BuOf = ℂ`.  Here we prove the general form (for an arbitrary `T`-invariant
`S ⊆ d.DE`) and use it to obtain the two surjectivity conjuncts of `HornData`.
-/

namespace Work.Horn

noncomputable section

open MandelDim Set Filter Topology

/-- **`E` maps a `T`-invariant piece of `DE` that covers `B` off the critical orbit onto `ℂ`.**
This is `Work.Horn.E_image_univ_of_varphi_image` with the component `BuOf` replaced by an
arbitrary `S` (the proof is unchanged). -/
theorem E_image_univ_of_varphi_image' {f₀ : ℂ → ℂ} {D₀ B : Set ℂ} {c : ℂ}
    (d : MandelDim.ParabData f₀ D₀) {S : Set ℂ}
    (hPhi : MandelDim.HornPhiStatement) (hsetup : MandelDim.IsF0Setup f₀ D₀ B c)
    (hsub : B \ MandelDim.critOrbit f₀ c ⊆ d.φ '' S)
    (hT : MandelDim.IsTInvariant S) (hDE : S ⊆ d.DE) :
    d.E '' S = Set.univ := by
  have hbas : B ⊆ MandelDim.ParabolicBasin f₀ D₀ := hsetup.2.1.2.2.1
  have hmaps : Set.MapsTo f₀ B B := hsetup.2.1.2.2.2.2.1
  have hcB : c ∈ B := hsetup.2.2.1
  have hφc : c ∈ d.φ '' S :=
    hsub ⟨hcB, crit_not_mem_critOrbit d hsetup⟩
  ext y
  simp only [Set.mem_image, Set.mem_univ, iff_true]
  by_cases hy : ∃ k : ℤ, y = d.Φ c + k
  · obtain ⟨k, rfl⟩ := hy
    obtain ⟨w, hw, hwφ⟩ := hφc
    refine ⟨w + k, MandelDim.IsTInvariant.add_int hT hw k, ?_⟩
    rw [E_add_int_on d hT hDE hw k,
      show d.E w = d.Φ c by simp [MandelDim.ParabData.E, hwφ]]
  · obtain ⟨z, hzB, hzy⟩ := (hPhi f₀ D₀ B c d hsetup).1 y
    have hznot : z ∉ MandelDim.critOrbit f₀ c := by
      rintro ⟨j, hj1, hjc⟩
      exact hy ⟨(j : ℤ), by
        rw [← hzy, hjc, Phi_critOrbit d hbas hmaps hcB j]; push_cast; ring⟩
    obtain ⟨w, hw, hwφ⟩ := hsub ⟨hzB, hznot⟩
    exact ⟨w, hw, by simp [MandelDim.ParabData.E, hwφ, hzy]⟩

/-- **Surjectivity of `E` on the two horn components.** -/
theorem surj_of_parts (hTopo : MandelDim.HornTopoStatement) (hPhi : MandelDim.HornPhiStatement)
    (f₀ : ℂ → ℂ) (D₀ B : Set ℂ) (c : ℂ) (d : MandelDim.ParabData f₀ D₀)
    (hsetup : MandelDim.IsF0Setup f₀ D₀ B c)
    (himage : (B \ MandelDim.critOrbit f₀ c ⊆ d.φ '' MandelDim.BuOf d B) ∧
      (B \ MandelDim.critOrbit f₀ c ⊆ d.φ '' MandelDim.BlOf d B)) :
    (∀ y : ℂ, ∃ w ∈ MandelDim.BuOf d B, d.E w = y) ∧
      (∀ y : ℂ, ∃ w ∈ MandelDim.BlOf d B, d.E w = y) := by
  have htopo := hTopo f₀ D₀ B c d hsetup
  have htBu : MandelDim.IsTInvariant (MandelDim.BuOf d B) := htopo.2.2.1
  have htBl : MandelDim.IsTInvariant (MandelDim.BlOf d B) := htopo.2.2.2.1
  have hsub : MandelDim.BuOf d B ∪ MandelDim.BlOf d B ⊆ d.DE := htopo.2.2.2.2.2.2
  have hDEu : MandelDim.BuOf d B ⊆ d.DE := fun w hw => hsub (Or.inl hw)
  have hDEl : MandelDim.BlOf d B ⊆ d.DE := fun w hw => hsub (Or.inr hw)
  have hu : d.E '' MandelDim.BuOf d B = Set.univ :=
    E_image_univ_of_varphi_image' d hPhi hsetup himage.1 htBu hDEu
  have hl : d.E '' MandelDim.BlOf d B = Set.univ :=
    E_image_univ_of_varphi_image' d hPhi hsetup himage.2 htBl hDEl
  constructor
  · intro y
    have : y ∈ d.E '' MandelDim.BuOf d B := by rw [hu]; exact Set.mem_univ y
    simpa using this
  · intro y
    have : y ∈ d.E '' MandelDim.BlOf d B := by rw [hl]; exact Set.mem_univ y
    simpa using this

end

end Work.Horn
