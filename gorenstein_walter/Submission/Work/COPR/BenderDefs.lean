/-
# AREA COPR — Bender's inversion map (definition module)

This module holds the definitions and elementary lemmas used in the proof of
`Work.COPR.coprime15_gen` (Bender 1981, 1.5(i)+(ii)).

Setting: `G` a group, `X : Subgroup G`, `s : G` with `s ∈ N_G(X)`, so that conjugation by `s`
restricts to an endomorphism `sigma` of `X`.  Bender's map is `phi u = u⁻¹ * u^s`.
-/
import Mathlib
import Submission.Work.COPR.Defs

namespace Work.COPR

open Subgroup

variable {G : Type} [Group G] (X : Subgroup G) (s : G)

/-- Conjugation by `s`, as an endomorphism of `X`, when `s` normalizes `X`. -/
def sigma (hN : s ∈ Subgroup.normalizer (X : Set G)) : X →* X where
  toFun u := ⟨s * (u : G) * s⁻¹, (Subgroup.mem_normalizer_iff.mp hN (u : G)).mp u.2⟩
  map_one' := by ext; simp
  map_mul' u v := by
    ext
    show s * ((u * v : X) : G) * s⁻¹ = s * (u : G) * s⁻¹ * (s * (v : G) * s⁻¹)
    rw [Subgroup.coe_mul]
    group

/-- Bender's map `x ↦ x⁻¹ x^s` on `X`. -/
def phi (hN : s ∈ Subgroup.normalizer (X : Set G)) : X → X :=
  fun u => u⁻¹ * sigma X s hN u

lemma sigma_coe (hN : s ∈ Subgroup.normalizer (X : Set G)) (u : X) :
    (sigma X s hN u : G) = s * (u : G) * s⁻¹ := rfl

lemma phi_apply (hN : s ∈ Subgroup.normalizer (X : Set G)) (u : X) :
    phi X s hN u = u⁻¹ * sigma X s hN u := rfl

lemma phi_coe (hN : s ∈ Subgroup.normalizer (X : Set G)) (u : X) :
    (phi X s hN u : G) = (u : G)⁻¹ * (s * (u : G) * s⁻¹) := by
  simp [phi, sigma]

/-- `sigma` is an involution as soon as `s` has order two. -/
lemma sigma_sigma (hN : s ∈ Subgroup.normalizer (X : Set G)) (hs : s * s = 1) (u : X) :
    sigma X s hN (sigma X s hN u) = u := by
  have hsinv : s⁻¹ = s := inv_eq_of_mul_eq_one_right hs
  ext
  show s * (s * (u:G) * s⁻¹) * s⁻¹ = (u:G)
  rw [hsinv]
  calc s * (s * ↑u * s) * s = (s * s) * ↑u * (s * s) := by group
    _ = ↑u := by rw [hs, one_mul, mul_one]

/-- The image of Bender's map is inverted by `s`. -/
lemma sigma_phi (hN : s ∈ Subgroup.normalizer (X : Set G)) (hs : s * s = 1) (u : X) :
    sigma X s hN (phi X s hN u) = (phi X s hN u)⁻¹ := by
  rw [phi, map_mul, map_inv, sigma_sigma X s hN hs]
  group

/-- `sigma u = u` exactly for the elements centralized by `s`. -/
lemma sigma_eq_self_iff (hN : s ∈ Subgroup.normalizer (X : Set G)) (u : X) :
    sigma X s hN u = u ↔ (u : G) ∈ Subgroup.centralizer ({s} : Set G) := by
  rw [Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    have h2 : s * (u : G) * s⁻¹ = (u : G) := by
      have := congrArg (Subtype.val) h
      simpa [sigma_coe] using this
    calc (u : G) * s = (s * (u : G) * s⁻¹) * s := by rw [h2]
      _ = s * (u : G) := by group
  · intro h
    ext
    rw [sigma_coe]
    calc s * (u : G) * s⁻¹ = ((u : G) * s) * s⁻¹ := by rw [h]
      _ = (u : G) := by group

/-- `sigma u = u⁻¹` exactly for the elements inverted by `s`. -/
lemma sigma_eq_inv_iff (hN : s ∈ Subgroup.normalizer (X : Set G)) (u : X) :
    sigma X s hN u = u⁻¹ ↔ s * (u : G) * s⁻¹ = (u : G)⁻¹ := by
  constructor
  · intro h
    have h2 : (sigma X s hN u : G) = ((u⁻¹ : X) : G) := by rw [h]
    simpa [sigma_coe, Subgroup.coe_inv] using h2
  · intro h
    ext
    simpa [sigma_coe, Subgroup.coe_inv] using h

end Work.COPR
