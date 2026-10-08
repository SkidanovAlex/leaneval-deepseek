import Mathlib
import Submission.Work.Fitting.Defs

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.Fitting

/-- If `H` is a characteristic (in particular normal) subgroup of `G` and `A` is a
characteristic subgroup of the quotient `G ⧸ H`, then the preimage of `A` in `G` is
characteristic.  This is the naturality of `Subgroup.comap` along quotient maps for
automorphisms of `G`. -/
theorem characteristic_comap_quotient {G : Type*} [Group G] {H : Subgroup G} [H.Normal]
    (hHc : H.Characteristic) (A : Subgroup (G ⧸ H)) (hAc : A.Characteristic) :
    (A.comap (QuotientGroup.mk' H)).Characteristic := by
  rw [Subgroup.characteristic_iff_map_eq] at hHc hAc ⊢
  intro φ
  let φ' : G ⧸ H ≃* G ⧸ H := QuotientGroup.congr H H φ (hHc φ)
  have hφ' : ∀ x : G, φ' (QuotientGroup.mk' H x) = QuotientGroup.mk' H (φ x) :=
    fun x => QuotientGroup.congr_mk' H H φ (hHc φ) x
  have hπsymm : ∀ x : G, QuotientGroup.mk' H (φ.symm x) = φ'.symm (QuotientGroup.mk' H x) := by
    intro x
    apply φ'.injective
    rw [MulEquiv.apply_symm_apply, hφ']
    simp
  ext x
  rw [Subgroup.mem_map_equiv]
  rw [Subgroup.mem_comap, Subgroup.mem_comap, hπsymm]
  rw [← Subgroup.mem_map_equiv (f := φ'), hAc φ']

theorem pPrimePCore_characteristic (p : ℕ) (G : Type*) [Group G] [Finite G] :
    (Work.Fitting.pPrimePCore p G).Characteristic := by
  rw [pPrimePCore]
  exact characteristic_comap_quotient (pPrimeCore_characteristic p G) _
    (piCore_characteristic (fun q => q = p) _)

end Work.Fitting
