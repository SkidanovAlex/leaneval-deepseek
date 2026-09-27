import Mathlib
import Submission.Work.Mostow.geomFiniteDefs
import Submission.Work.Mostow.deepCusp

/-! # Area C1 (geomFinite) — dichotomy for elements fixing a boundary point (L1)

An isometry `g` of `ℍⁿ` which fixes `ξ ∈ Sph n` and preserves the horospheres at `ξ`
(`bCocy g ξ = 0`) is either parabolic or has a fixed point in `ℍⁿ`.  The parabolic case is
immediate from `Work.Mostow.deepCusp`: the displacement tends to `0` along the ray to `ξ`.

Consequently, if `g` fixes a point of `ℍⁿ` then `bCocy g ξ = 0` (the elliptic half).
-/

namespace Work.Mostow

open Submission.Mostow LeanEval.Geometry.MostowRigidity MeasureTheory

noncomputable section

variable {n : ℕ}

/-- `L1`: an isometry fixing `ξ` and preserving the horospheres at `ξ` is parabolic or elliptic. -/
theorem stabParabOrEllip (n : ℕ) (hn : 2 ≤ n) (hA : POActionProp n) (hI : HypIsometryProp n)
    (g : PO n 1) (ξ : E n) (hξ : ξ ∈ Sph n) (hgξ : bd g ξ = ξ) (hc : bCocy g ξ = 0) :
    IsParabolic g ∨ ∃ p : E n, g • p = p := by
  have hIc := hI
  obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,hbus⟩ := hI
  by_cases hfix : ∃ p : E n, g • p = p
  · exact Or.inr hfix
  · refine Or.inl ⟨fun u hu => hfix ⟨u, hu⟩, ?_⟩
    have hpres : ∀ u : E n, busemann ξ (g • u) = busemann ξ u := by
      intro u
      have h := hbus g ξ u hξ
      rw [hgξ] at h
      have hc' : busemann ξ (g • (0 : E n)) = 0 := by
        have hb : bCocy g ξ = busemann ξ (g • (0 : E n)) := by rw [bCocy, hgξ]
        rw [← hb]; exact hc
      rw [hc'] at h
      simpa using h
    intro ε hε
    exact deepCusp n hn hA hIc g ξ hξ hgξ hpres ε hε

/-- An isometry with a fixed point in `ℍⁿ` preserves the horospheres at every fixed boundary
point. -/
theorem bCocy_eq_zero_of_fixed (hI : HypIsometryProp n)
    (g : PO n 1) (ξ : E n) (hξ : ξ ∈ Sph n) (hgξ : bd g ξ = ξ) (p : E n) (hp : g • p = p) :
    bCocy g ξ = 0 := by
  obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,hbus⟩ := hI
  have h := hbus g ξ p hξ
  rw [hgξ, hp] at h
  rw [show bCocy g ξ = busemann ξ (g • (0 : E n)) from by rw [bCocy, hgξ]]
  linarith [h]

end

end Work.Mostow
