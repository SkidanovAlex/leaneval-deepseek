/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Work.MotC2Cls

# A rational place not containing `x` is the place at infinity

Let `E` be an elliptic Weierstrass curve over a field `L` and let `S ⊆ L(E)` be a rational place
(`Work.MotC2.IsRatPlace E S`): a discrete valuation ring with residue field `L` (via the structure
map) whose fraction field is `L(E)`.  If the coordinate `x = genX E` is *not* in `S`, then `S`
contains the local ring of the point at infinity: `infPlace E ≤ S`.

This is the `x ∉ S` half of the classification of the rational places of `L(E)/L`
(`Work.MotC2.Classification`).  The argument, with `u = 1/x = infU E` and `w = y/x² = infW E`:

* `S` is a discrete valuation ring, hence a prevaluation ring, and its fraction field is `L(E)`
  (`IsRatPlace`).  Since `x ≠ 0` and `x ∉ S`, we get `x⁻¹ = u ∈ S`.
* If `w ∉ S`, then `w ≠ 0` (as `0 ∈ S`) and `w⁻¹ ∈ S`.  Multiplying the Weierstrass relation in
  the chart at infinity
  `w² + a₁uw + a₃u²w = u + a₂u² + a₄u³ + a₆u⁴`
  by `(w⁻¹)²` exhibits `1 = u · s` with `s ∈ S`, so `u` is a unit of `S`, hence `x = u⁻¹ ∈ S`,
  contradiction.  Thus `w ∈ S` and `infCoordRing E = L[u,w] ⊆ S`.
* `u` is a non-unit of `S` (its inverse is `x ∉ S`), so `u ∈ 𝔪_S`.  The relation also shows
  `w² = u(1 + a₂u + a₄u² + a₆u³) - (a₁u + a₃u²)w ∈ 𝔪_S`, and `𝔪_S` is prime, so `w ∈ 𝔪_S`.
* Hence the kernel of the natural map `inc : infCoordRing E → S ⧸ 𝔪_S` contains the ideal
  `I = (u,w) = infCoordIdeal E`.  Now `L → infCoordRing E ⧸ I` is surjective
  (`quot_infCoordRing_surjective`) while `L → S ⧸ 𝔪_S` is bijective, so `infCoordRing E ⧸ I` is a
  field (it is `L`), i.e. `I` is maximal.  A maximal ideal contained in the proper ideal
  `inc⁻¹(𝔪_S)` therefore equals it: every element of `infCoordRing E` outside `infIdeal E` is a
  unit of `S`.
* The algebra `infPlace E` is generated over `L` by `infCoordRing E` and the inverses of the
  elements of `infCoordRing E` outside `infIdeal E`; both kinds of generators lie in `S`.
-/

import Mathlib
import Submission.Work.MotC2Cls.Setup
import Submission.Work.MotC2.Integral
import Submission.Work.MotC2.DVRMaximal
import Submission.Work.MotC2.Relations
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open Work.MotC2

set_option maxHeartbeats 1000000
set_option linter.style.haveILetI false

namespace Work.MotC2Cls

/-- If the rational place `S` does not contain `genX E`, then the chart-at-infinity coordinate ring
`L[1/x, y/x²]` is contained in `S`. -/
theorem infCoordRing_le_of_notMem_genX {L : Type*} [Field L] (E : WeierstrassCurve L)
    [E.IsElliptic] (S : Subalgebra L (Func E)) (hS : IsRatPlace E S) (hx : genX E ∉ S) :
    infCoordRing E ≤ S := by
  obtain ⟨⟨hSdvr, hSbij⟩, hSfrac⟩ := hS
  haveI := hSdvr
  -- `u = 1/x ∈ S`, since `x ≠ 0` and `x ∉ S`
  have huS : infU E ∈ S := by
    rcases mem_or_inv_mem_of_preValuationRing S hSfrac (genX_ne_zero E) with h | h
    · exact absurd h hx
    · simpa [infU] using h
  -- `w = y/x² ∈ S`: otherwise `w⁻¹ ∈ S` and the chart relation forces `x ∈ S`
  have hwS : infW E ∈ S := by
    by_cases hw0 : infW E = 0
    · rw [hw0]; exact S.zero_mem
    · rcases mem_or_inv_mem_of_preValuationRing S hSfrac hw0 with h | h
      · exact h
      · exfalso
        have hrel := infW_sq_relation E
        set g : Func E := (infW E)⁻¹ with hg
        have hgS : g ∈ S := by rw [hg]; exact h
        have h1 : infU E * (((1 + algebraMap L (Func E) E.a₂ * infU E +
              algebraMap L (Func E) E.a₄ * (infU E)^2 + algebraMap L (Func E) E.a₆ * (infU E)^3) * g^2)
              - ((algebraMap L (Func E) E.a₁ + algebraMap L (Func E) E.a₃ * infU E) * g)) = 1 := by
          have hkey : infU E * (1 + algebraMap L (Func E) E.a₂ * infU E +
              algebraMap L (Func E) E.a₄ * (infU E)^2 + algebraMap L (Func E) E.a₆ * (infU E)^3
              - infW E * (algebraMap L (Func E) E.a₁ + algebraMap L (Func E) E.a₃ * infU E))
              = (infW E)^2 := by
            ring_nf
            linear_combination (norm := first | refl_ring1 | ring1) -hrel
          have hfactor : ((1 + algebraMap L (Func E) E.a₂ * infU E +
              algebraMap L (Func E) E.a₄ * (infU E)^2 + algebraMap L (Func E) E.a₆ * (infU E)^3) * g^2)
              - ((algebraMap L (Func E) E.a₁ + algebraMap L (Func E) E.a₃ * infU E) * g)
              = (1 + algebraMap L (Func E) E.a₂ * infU E +
              algebraMap L (Func E) E.a₄ * (infU E)^2 + algebraMap L (Func E) E.a₆ * (infU E)^3
              - infW E * (algebraMap L (Func E) E.a₁ + algebraMap L (Func E) E.a₃ * infU E)) * g^2 := by
            rw [hg]; field_simp
          rw [hfactor, ← mul_assoc, hkey, hg, inv_pow, mul_inv_cancel₀ (pow_ne_zero 2 hw0)]
        have hsS : (((1 + algebraMap L (Func E) E.a₂ * infU E +
              algebraMap L (Func E) E.a₄ * (infU E)^2 + algebraMap L (Func E) E.a₆ * (infU E)^3) * g^2)
              - ((algebraMap L (Func E) E.a₁ + algebraMap L (Func E) E.a₃ * infU E) * g)) ∈ S := by
          refine sub_mem (mul_mem ?_ (pow_mem hgS 2)) (mul_mem ?_ hgS)
          · exact add_mem (add_mem (add_mem S.one_mem
              (mul_mem (S.algebraMap_mem _) huS))
              (mul_mem (S.algebraMap_mem _) (pow_mem huS 2)))
              (mul_mem (S.algebraMap_mem _) (pow_mem huS 3))
          · exact add_mem (S.algebraMap_mem _) (mul_mem (S.algebraMap_mem _) huS)
        have hxS : genX E ∈ S := by
          have hui : (infU E)⁻¹ = (((1 + algebraMap L (Func E) E.a₂ * infU E +
              algebraMap L (Func E) E.a₄ * (infU E)^2 + algebraMap L (Func E) E.a₆ * (infU E)^3) * g^2)
              - ((algebraMap L (Func E) E.a₁ + algebraMap L (Func E) E.a₃ * infU E) * g)) :=
            inv_eq_of_mul_eq_one_right h1
          rw [infU, inv_inv] at hui
          rw [hui]
          exact hsS
        exact hx hxS
  -- the chart ring is generated by `u` and `w`
  rw [infCoordRing]
  refine Algebra.adjoin_le_iff.mpr ?_
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl
  · exact huS
  · exact hwS

/-- If the rational place `S` does not contain `genX E`, then the inverse of every element of the
chart-at-infinity coordinate ring outside the ideal `(1/x, y/x²) = infIdeal E` lies in `S`. -/
theorem inv_mem_of_mem_infCoordRing_of_notMem_infIdeal {L : Type*} [Field L]
    (E : WeierstrassCurve L) [E.IsElliptic] (S : Subalgebra L (Func E)) (hS : IsRatPlace E S)
    (hx : genX E ∉ S) {r : Func E} (hr : r ∈ infCoordRing E) (hnot : r ∉ infIdeal E) :
    r⁻¹ ∈ S := by
  have hring_le := infCoordRing_le_of_notMem_genX E S hS hx
  obtain ⟨⟨hSdvr, _⟩, _⟩ := hS
  haveI := hSdvr
  have huS : infU E ∈ S := hring_le (Algebra.subset_adjoin (by simp))
  have hwS : infW E ∈ S := hring_le (Algebra.subset_adjoin (by simp))
  -- the inclusion `infCoordRing E → S`
  let inc : infCoordRing E →+* S :=
    { toFun := fun x => ⟨(x : Func E), hring_le x.2⟩
      map_one' := Subtype.ext rfl
      map_mul' := fun a b => Subtype.ext rfl
      map_zero' := Subtype.ext rfl
      map_add' := fun a b => Subtype.ext rfl }
  -- `u` lies in the maximal ideal of `S` (otherwise `x = u⁻¹ ∈ S`)
  have hu_mem : ∀ x : infCoordRing E, (x : Func E) = infU E → inc x ∈ IsLocalRing.maximalIdeal S := by
    intro x hxval
    rw [IsLocalRing.mem_maximalIdeal]
    intro hunit
    obtain ⟨u, hu⟩ := hunit
    have hux : (((u⁻¹ : Sˣ) : S) : Func E) = genX E := by
      rw [subalgebra_coe_unit_inv S u, hu]
      change ((x : Func E))⁻¹ = genX E
      rw [hxval, infU, inv_inv]
    exact hx (hux ▸ ((u⁻¹ : Sˣ) : S).2)
  -- `w` lies in the maximal ideal of `S`: `w² ∈ 𝔪_S` by the chart relation, and `𝔪_S` is prime
  have hw_mem : ∀ x : infCoordRing E, (x : Func E) = infW E → inc x ∈ IsLocalRing.maximalIdeal S := by
    intro x hxval
    have hrel := infW_sq_relation E
    have hWeq : inc x = (⟨infW E, hwS⟩ : S) := Subtype.ext hxval
    rw [hWeq]
    have hZmem : (1 + algebraMap L (Func E) E.a₂ * infU E + algebraMap L (Func E) E.a₄ * (infU E)^2
        + algebraMap L (Func E) E.a₆ * (infU E)^3
        - infW E * (algebraMap L (Func E) E.a₁ + algebraMap L (Func E) E.a₃ * infU E)) ∈ S := by
      have hA : algebraMap L (Func E) E.a₁ + algebraMap L (Func E) E.a₃ * infU E ∈ S :=
        add_mem (S.algebraMap_mem _) (mul_mem (S.algebraMap_mem _) huS)
      exact sub_mem (add_mem (add_mem (add_mem S.one_mem
        (mul_mem (S.algebraMap_mem _) huS)) (mul_mem (S.algebraMap_mem _) (pow_mem huS 2)))
        (mul_mem (S.algebraMap_mem _) (pow_mem huS 3))) (mul_mem hwS hA)
    have hW2 : (⟨infW E, hwS⟩ : S) * ⟨infW E, hwS⟩ ∈ IsLocalRing.maximalIdeal S := by
      have heq : (⟨infW E, hwS⟩ : S) * ⟨infW E, hwS⟩ =
          (⟨infU E, hring_le (Algebra.subset_adjoin (by simp))⟩ : S) *
            ⟨1 + algebraMap L (Func E) E.a₂ * infU E + algebraMap L (Func E) E.a₄ * (infU E)^2
              + algebraMap L (Func E) E.a₆ * (infU E)^3
              - infW E * (algebraMap L (Func E) E.a₁ + algebraMap L (Func E) E.a₃ * infU E), hZmem⟩ := by
        apply Subtype.ext
        push_cast
        linear_combination (norm := first | refl_ring1 | ring1) hrel
      rw [heq]
      exact Ideal.mul_mem_right _ _
        (hu_mem ⟨infU E, Algebra.subset_adjoin (by simp)⟩ rfl)
    rcases (IsLocalRing.maximalIdeal.isMaximal S).isPrime.mem_or_mem hW2 with h | h
    · exact h
    · exact h
  -- `(1/x, y/x²) ⊆ inc⁻¹(𝔪_S)`
  have hleIc : infCoordIdeal E ≤ Ideal.comap inc (IsLocalRing.maximalIdeal S) := by
    rw [infCoordIdeal, Ideal.span_le]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact Ideal.mem_comap.mpr (hu_mem _ rfl)
    · exact Ideal.mem_comap.mpr (hw_mem _ rfl)
  have hcomap_ne_top : Ideal.comap inc (IsLocalRing.maximalIdeal S) ≠ ⊤ := by
    intro htop
    have h1 : (1 : infCoordRing E) ∈ Ideal.comap inc (IsLocalRing.maximalIdeal S) := by
      rw [htop]; exact Submodule.mem_top
    have h2 : inc (1 : infCoordRing E) ∈ IsLocalRing.maximalIdeal S := Ideal.mem_comap.mp h1
    rw [map_one] at h2
    exact (IsLocalRing.notMem_maximalIdeal.mpr isUnit_one) h2
  have hI_ne_top : infCoordIdeal E ≠ ⊤ := by
    intro htop
    exact absurd (top_unique (htop ▸ hleIc)) hcomap_ne_top
  -- `L → infCoordRing E ⧸ (u,w)` is bijective, so the quotient is a field and `(u,w)` is maximal
  have hsurj : Function.Surjective (algebraMap L (infCoordRing E ⧸ infCoordIdeal E)) :=
    quot_infCoordRing_surjective E
  haveI : Nontrivial (infCoordRing E ⧸ infCoordIdeal E) :=
    Ideal.Quotient.nontrivial_iff.mpr hI_ne_top
  have hinj : Function.Injective (algebraMap L (infCoordRing E ⧸ infCoordIdeal E)) := by
    rw [injective_iff_map_eq_zero]
    intro c hc
    by_contra hc0
    exact (IsUnit.ne_zero (IsUnit.map _ (isUnit_iff_ne_zero.mpr hc0))) hc
  have hfield : IsField (infCoordRing E ⧸ infCoordIdeal E) :=
    (RingEquiv.ofBijective _ ⟨hinj, hsurj⟩).symm.toMulEquiv.isField (Field.toIsField L)
  have hImax : (infCoordIdeal E).IsMaximal :=
    (Ideal.Quotient.maximal_ideal_iff_isField_quotient (infCoordIdeal E)).mpr hfield
  have hcomap : infCoordIdeal E = Ideal.comap inc (IsLocalRing.maximalIdeal S) :=
    Ideal.IsMaximal.eq_of_le hImax hcomap_ne_top hleIc
  -- conclude for the given element `r`
  have hr₀ : (⟨r, hr⟩ : infCoordRing E) ∉ infCoordIdeal E := fun h =>
    hnot ((mem_infCoordIdeal_iff E ⟨r, hr⟩).mp h)
  have hmem : inc ⟨r, hr⟩ ∉ IsLocalRing.maximalIdeal S := by
    intro hmem
    exact hr₀ (by rw [hcomap]; exact Ideal.mem_comap.mpr hmem)
  obtain ⟨u, hu⟩ := (IsLocalRing.notMem_maximalIdeal).mp hmem
  have hval : (((u⁻¹ : Sˣ) : S) : Func E) = r⁻¹ := by
    rw [subalgebra_coe_unit_inv S u, hu]
    rfl
  change r⁻¹ ∈ S
  rw [← hval]
  exact ((u⁻¹ : Sˣ) : S).2

theorem infPlace_le_of_notMem_genX {L : Type*} [Field L] (E : WeierstrassCurve L) [E.IsElliptic]
    (S : Subalgebra L (Work.MotC2.Func E)) (hS : Work.MotC2.IsRatPlace E S)
    (hx : Work.MotC2.genX E ∉ S) : Work.MotC2.infPlace E ≤ S := by
  refine Algebra.adjoin_le_iff.mpr ?_
  rintro x (hx' | hx')
  · exact infCoordRing_le_of_notMem_genX E S hS hx hx'
  · obtain ⟨r, ⟨hr, hnot⟩, rfl⟩ := hx'
    exact inv_mem_of_mem_infCoordRing_of_notMem_infIdeal E S hS hx hr hnot

end Work.MotC2Cls
