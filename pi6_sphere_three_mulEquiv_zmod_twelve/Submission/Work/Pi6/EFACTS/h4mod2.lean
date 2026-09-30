import Mathlib
import Submission.Work.Pi6.Interfaces
import Submission.Work.Pi6.BOCK.bocksteinLES
import Submission.Work.Pi6.K2Z.kOneField
import Submission.Work.Pi6.EFACTS.sphereModTwoLow
import Submission.Work.Pi6.SRANGE.homQuot_bridge
import Submission.Work.StemsB.FieldDualUCT
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

/-!
# `H⁴(S³⟨3⟩; 𝔽₂) ≅ 𝔽₂` from `H₄(S³⟨3⟩; ℤ) ≅ ℤ/2` and `H₃(S³⟨3⟩; ℤ) = 0`

The integral homology of the 3-connected cover `E = Ecov g3` in degrees 3 and 4 determines its
mod-2 cohomology in degree 4:

* the mod-`2` Bockstein long exact sequence
  `H₄(E;ℤ) --·2--> H₄(E;ℤ) --red--> H₄(E;𝔽₂) --del--> H₃(E;ℤ)`
  (`Work.Pi6.BOCK.bocksteinLES`, homology form) exhibits `red` as bijective: the left `·2` map is
  zero because `H₄(E;ℤ) ≅ ℤ/2`, so `red` is injective; and `del` is zero because `H₃(E;ℤ) = 0`,
  so `red` is surjective.  Hence `H₄(E;𝔽₂) ≅ H₄(E;ℤ) ≅ ℤ/2`;
* the universal coefficient theorem over a field (`Work.Pi6.EFACTS.cohIsoDualField`, i.e.
  `Hⁿ(X;𝕜) ≅ Hom_𝕜(Hₙ(X;𝕜),𝕜)`) turns this into `H⁴(E;𝔽₂) ≅ Hom_𝔽₂(𝔽₂,𝔽₂) ≅ 𝔽₂`.
-/

namespace Work.Pi6.EFACTS

open CategoryTheory CategoryTheory.Limits

theorem h4mod2 {P3 : Type} [TopologicalSpace P3] (g3 : C(Work.Pi6.S3, P3)) (hH4 : Nonempty (Work.Pi6.HR ℤ (Work.Pi6.Ecov g3) 4 ≃ₗ[ℤ] ZMod 2)) (hH3 : Subsingleton (Work.Pi6.HR ℤ (Work.Pi6.Ecov g3) 3)) : Nonempty (Work.Pi6.Coh (ZMod 2) (Work.Pi6.Ecov g3) 4 ≃ₗ[ZMod 2] ZMod 2) := by
  obtain ⟨red, del, hred, hrd, hdel, -, -⟩ := Work.Pi6.BOCK.bocksteinLES 2 (by norm_num)
  obtain ⟨e4⟩ := hH4
  -- Multiplication by `2` is zero on `H₄(E;ℤ)`, since that group is `ℤ/2`.
  have h2zero : ∀ x : ↥(Work.Pi6.HR ℤ (Work.Pi6.Ecov g3) 4), (2 : ℤ) • x = 0 := by
    intro x
    apply e4.injective
    rw [map_zsmul, map_zero]
    rw [two_zsmul]
    exact CharTwo.add_self_eq_zero _
  -- `red₄` is injective by exactness at `H₄(E;ℤ)`.
  have hinj : Function.Injective (red (X := Work.Pi6.Ecov g3) 4) := by
    intro a b hab
    have h1 : red (X := Work.Pi6.Ecov g3) 4 (a - b) = 0 := by
      rw [map_sub, hab, sub_self]
    have h2 : a - b = 0 := by
      obtain ⟨x, hx⟩ := Set.mem_range.mp (((hred (Work.Pi6.Ecov g3) 4) (a - b)).mp h1)
      exact hx ▸ h2zero x
    exact sub_eq_zero.mp h2
  -- `red₄` is surjective by exactness at `H₄(E;𝔽₂)` and `H₃(E;ℤ) = 0`.
  have hsurj : Function.Surjective (red (X := Work.Pi6.Ecov g3) 4) := by
    intro y
    have h0 : del (X := Work.Pi6.Ecov g3) 3 y = 0 := Subsingleton.elim _ _
    exact Set.mem_range.mp (((hrd (Work.Pi6.Ecov g3) 3) y).mp h0)
  have hbij : Function.Bijective (red (X := Work.Pi6.Ecov g3) 4) := ⟨hinj, hsurj⟩
  -- hence `H₄(E;𝔽₂) ≅ H₄(E;ℤ) ≅ ℤ/2`
  have h4mod2lin : Nonempty (Work.Pi6.HR (ZMod 2) (Work.Pi6.Ecov g3) 4 ≃ₗ[ZMod 2] ZMod 2) :=
    ⟨Work.Pi6.K2Z.zmodLinearEquivOfAddEquiv 2
      ((AddEquiv.ofBijective _ hbij).symm.trans e4.toAddEquiv)⟩
  obtain ⟨h4lin⟩ := h4mod2lin
  -- the field universal coefficient theorem and `Hom_𝔽₂(𝔽₂,𝔽₂) ≅ 𝔽₂`
  obtain ⟨eCoh⟩ := Work.Pi6.EFACTS.cohIsoDualField (ZMod 2) (Work.Pi6.Ecov g3) 4
  have edual : (↥(Work.Pi6.HR (ZMod 2) (Work.Pi6.Ecov g3) 4) →ₗ[ZMod 2] ZMod 2) ≃ₗ[ZMod 2] ZMod 2 :=
    (LinearEquiv.arrowCongr h4lin (LinearEquiv.refl (ZMod 2) (ZMod 2))).trans
      (Work.Pi6.K2Z.dualSelfEquiv (ZMod 2))
  exact ⟨(Work.Pi6.SRANGE.isoToLinearEquiv eCoh).trans edual⟩

end Work.Pi6.EFACTS
