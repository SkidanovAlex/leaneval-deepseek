import Mathlib
import Submission.Work.CFT.ClassFormation.Defs
import Submission.Work.CFT.Kummer.finrank_unitsModPow
import Submission.Work.CFT.Kummer.Defs
import Submission.Work.CFT.ClassFormation.Schur.finrank_homology_fp_eq

/-!
# `rank_p 𝒪_Kˣ = dim_{𝔽_p} 𝒪_Kˣ/(𝒪_Kˣ)^p`

For a number field `K` and a prime `p`, the `p`-rank of the unit group `𝒪_Kˣ` — computed as
`rankP p A = dim_{𝔽_p} (𝔽_p ⊗_ℤ A)` — agrees with the `𝔽_p`-dimension of the elementary abelian
`p`-group `𝒪_Kˣ/(𝒪_Kˣ)^p`.

Both sides are the "`p`-cokernel" of the abelian group `𝒪_Kˣ`: the general fact proved here is that
for *any* commutative group `G`,
`𝔽_p ⊗_ℤ G ≅ G ⧸ G^p` (as abelian groups, and in fact as `𝔽_p`-vector spaces), whence the two
`𝔽_p`-dimensions coincide.

## Main results

* `Work.CFTLib.tensorAddEquiv_quotient_pthPow` — the additive isomorphism above.
* `Work.CFTLib.rankP_eq_finrank_unitsModPow` — the dimension identity.
-/

open scoped TensorProduct

set_option linter.style.haveILetI false

namespace Work.CFTLib

open Work.CFT.Kummer (pthPowerSubgroup)
open Work.CFT.ClassFormation.Schur (mulByP)

/-! ## The `p`-th power cokernel of a commutative group -/

/-- Multiplication by `p` on `Additive G` is given in multiplicative notation by `p`-th powers. -/
lemma mulByP_eq_iff (G : Type) [CommGroup G] (p : ℕ) (y x : Additive G) :
    mulByP p (Additive G) y = x ↔ y.toMul ^ p = x.toMul := by
  dsimp only [Work.CFT.ClassFormation.Schur.mulByP]
  rw [Work.CFT.ClassFormation.Schur.smul_id_apply, Nat.cast_smul_eq_nsmul]
  constructor
  · intro h; rw [← h]; exact toMul_nsmul p y
  · intro h; apply Additive.toMul.injective; rw [toMul_nsmul, h]

/-- The range of multiplication by `p` on `Additive G` is exactly the group of `p`-th powers. -/
lemma mem_range_mulByP_iff (G : Type) [CommGroup G] (p : ℕ) (x : Additive G) :
    x ∈ LinearMap.range (mulByP p (Additive G)) ↔ x.toMul ∈ pthPowerSubgroup G p := by
  rw [LinearMap.mem_range, Work.CFT.Kummer.mem_pthPowerSubgroup]
  constructor
  · rintro ⟨y, hy⟩
    exact ⟨y.toMul, (mulByP_eq_iff G p y x).mp hy⟩
  · rintro ⟨y, hy⟩
    exact ⟨Additive.ofMul y, (mulByP_eq_iff G p (Additive.ofMul y) x).mpr hy⟩

/-- The range of multiplication by `p` on `Additive G`, as a `ℤ`-submodule, is the subgroup of
`p`-th powers. -/
lemma range_mulByP_eq (G : Type) [CommGroup G] (p : ℕ) :
    LinearMap.range (mulByP p (Additive G))
      = AddSubgroup.toIntSubmodule (pthPowerSubgroup G p).toAddSubgroup := by
  ext x
  rw [mem_range_mulByP_iff, ← Submodule.mem_toAddSubgroup,
    AddSubgroup.toIntSubmodule_toAddSubgroup]
  exact (Additive.mem_toAddSubgroup _ x).symm

/-- The kernel of the quotient map `Additive G → Additive (G ⧸ H)` is the subgroup `H`. -/
lemma ker_toAdditive_mk'_eq (G : Type) [CommGroup G] (H : Subgroup G) [H.Normal] :
    LinearMap.ker ((MonoidHom.toAdditive (QuotientGroup.mk' H)).toIntLinearMap)
      = AddSubgroup.toIntSubmodule H.toAddSubgroup := by
  rw [AddMonoidHom.coe_toIntLinearMap_ker]
  congr 1
  ext x
  rw [AddMonoidHom.mem_ker]
  show Additive.ofMul (QuotientGroup.mk' H x.toMul) = (0 : Additive (G ⧸ H)) ↔ x.toMul ∈ H
  rw [show (0 : Additive (G ⧸ H)) = Additive.ofMul (1 : G ⧸ H) from rfl,
      Additive.ofMul.injective.eq_iff]
  exact QuotientGroup.eq_one_iff x.toMul

/-- **The `p`-th power cokernel is the base change to `𝔽_p`.**  For any commutative group `G`,
`𝔽_p ⊗_ℤ G` is the cokernel of `p`-th powers on `G`, i.e. the elementary abelian `p`-group
`G ⧸ G^p`, additively. -/
theorem tensorAddEquiv_quotient_pthPow (G : Type) [CommGroup G] (p : ℕ) :
    Nonempty ((ZMod p ⊗[ℤ] Additive G) ≃+ Additive (G ⧸ pthPowerSubgroup G p)) := by
  let H : Subgroup G := pthPowerSubgroup G p
  haveI : H.Normal := Subgroup.normal_of_isMulCommutative H
  let g : Additive G →ₗ[ℤ] Additive (G ⧸ H) :=
    (MonoidHom.toAdditive (QuotientGroup.mk' H)).toIntLinearMap
  have hker : LinearMap.ker g = AddSubgroup.toIntSubmodule H.toAddSubgroup :=
    ker_toAdditive_mk'_eq G H
  have hrange : LinearMap.range (mulByP p (Additive G))
      = AddSubgroup.toIntSubmodule H.toAddSubgroup := range_mulByP_eq G p
  have hsurj : Function.Surjective g := by
    intro y
    obtain ⟨a, ha⟩ := QuotientGroup.mk'_surjective H y.toMul
    refine ⟨Additive.ofMul a, ?_⟩
    change Additive.ofMul (QuotientGroup.mk' H a) = y
    rw [ha, ofMul_toMul]
  obtain ⟨e0⟩ := Work.CFT.ClassFormation.Schur.coker_mulByP_equiv_tensor p (Additive G)
  exact ⟨e0.symm.trans (((Submodule.quotEquivOfEq _ _ (hrange.trans hker.symm)).toAddEquiv).trans
    (LinearMap.quotKerEquivOfSurjective g hsurj).toAddEquiv)⟩

/-! ## The dimension identity -/

/-- **`rank_p 𝒪_Kˣ = dim_{𝔽_p} 𝒪_Kˣ/(𝒪_Kˣ)^p`.**  This is the special case for the unit group of a
number field of the general identity `𝔽_p ⊗_ℤ G ≅ G ⧸ G^p`. -/
theorem rankP_eq_finrank_unitsModPow (K : Type) [Field K] [NumberField K] (p : ℕ) [Fact p.Prime] :
    Work.CFT.ClassFormation.rankP p (Additive (NumberField.RingOfIntegers K)ˣ)
      = Module.finrank (ZMod p) (Work.CFT.Kummer.unitsModPow K p) := by
  obtain ⟨e⟩ := tensorAddEquiv_quotient_pthPow (NumberField.RingOfIntegers K)ˣ p
  have eL : (ZMod p ⊗[ℤ] Additive (NumberField.RingOfIntegers K)ˣ) ≃ₗ[ZMod p]
      Work.CFT.Kummer.unitsModPow K p :=
    e.toLinearEquiv fun c x => ZMod.map_smul e.toAddMonoidHom c x
  exact LinearEquiv.finrank_eq eL

end Work.CFTLib
