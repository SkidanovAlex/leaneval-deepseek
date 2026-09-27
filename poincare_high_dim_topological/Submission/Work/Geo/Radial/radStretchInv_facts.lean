import Mathlib
import Submission.Work.Geo.Radial.RadialDefs

namespace Work.Geo.Radial

theorem radStretchInv_facts {ε R S s : ℝ} (hε : 0 < ε) (hεR : ε ≤ R) (hεS : ε < S)
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (hmono : StrictMono (radStretch ε R S s))
    (hsurj : Function.Surjective (radStretch ε R S s)) :
    (∀ t, radStretchInv ε R S s (radStretch ε R S s t) = t) ∧
    (∀ u, radStretch ε R S s (radStretchInv ε R S s u) = u) ∧
    Continuous (radStretchInv ε R S s) ∧
    (∀ u, 0 ≤ u → 0 ≤ radStretchInv ε R S s u) ∧
    (∀ u, 0 ≤ u → radStretchInv ε R S s u ≤ u) := by
  have hinj : Function.Injective (radStretch ε R S s) := hmono.injective
  -- The order isomorphism attached to the strictly monotone surjection.
  let e : ℝ ≃o ℝ := hmono.orderIsoOfSurjective (radStretch ε R S s) hsurj
  have he_apply : ∀ t, e t = radStretch ε R S s t :=
    fun t => congrFun (StrictMono.coe_orderIsoOfSurjective (radStretch ε R S s) hmono hsurj) t
  -- `radStretchInv` coincides with the inverse order isomorphism.
  have hfinv : radStretchInv ε R S s = ⇑e.symm := by
    unfold radStretchInv
    refine Function.invFun_eq_of_injective_of_rightInverse hinj ?_
    intro u
    rw [← he_apply (e.symm u)]
    exact e.apply_symm_apply u
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro t
    rw [hfinv, ← he_apply t]
    exact e.symm_apply_apply t
  · intro u
    rw [hfinv, ← he_apply (e.symm u)]
    exact e.apply_symm_apply u
  · rw [hfinv]
    exact e.symm.continuous
  · intro u hu
    rw [hfinv]
    by_contra hcon
    have hneg : e.symm u < 0 := lt_of_not_ge hcon
    have heq : e (e.symm u) = e.symm u := by
      rw [he_apply]
      unfold radStretch
      rw [radTent_of_nonpos hε (le_of_lt hneg)]
      ring
    rw [e.apply_symm_apply u] at heq
    linarith
  · intro u hu
    rw [hfinv]
    calc e.symm u ≤ radStretch ε R S s (e.symm u) := radStretch_ge_self hs0 hεR
      _ = e (e.symm u) := (he_apply (e.symm u)).symm
      _ = u := e.apply_symm_apply u

end Work.Geo.Radial
