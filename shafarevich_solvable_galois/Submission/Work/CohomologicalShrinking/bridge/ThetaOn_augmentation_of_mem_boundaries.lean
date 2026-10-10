import Mathlib.RepresentationTheory.Homological.GroupHomology.LowDegree
import Submission.Work.CohomologicalShrinking.Bridge.Core
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Θ` sends boundaries into the augmentation submodule

Let `G` be a finite group, `k` a commutative ring and `M` a `k`-module with a compatible
`G`-action.  Write `A = M^♯ = Work.Bridge.A` for the coinduced module and
`Θ = Work.Bridge.ThetaOn : Z₁(G,M) → ker(N_A)` for the concrete degree-shift map
`x ↦ x - single 1 (∑ x)` of `Work.Bridge`.

The present file proves that `Θ` carries the boundaries `B₁(G,M) ⊆ Z₁(G,M)` into the
augmentation submodule `I_G · A ⊆ A`:

`((ThetaOn b : K) : A) ∈ augmentation G A` for every `b ∈ Z₁(G,M)` whose underlying chain
lies in `B₁(G,M)`.

The computation is the standard one: on the generators `d₂₁(single (g,h) a)` of the boundaries
one has `θ(d₂₁(single (g,h) a)) = h⁻¹ • φ_{g,a} - φ_{g,a}` with `φ_{g,a} ∈ A`
(`Work.Bridge.thetaFun_d21_single`), which is exactly an element of the augmentation
submodule, and both `θ` and `d₂₁` are additive.
-/

open scoped BigOperators

set_option linter.unusedSectionVars false

namespace Work.CohomologicalShrinking.bridge

open Work.Bridge

variable {G : Type} [Group G] [Fintype G] [DecidableEq G]
variable {k : Type} [CommRing k]
variable {M : Type} [AddCommGroup M] [Module k M] [DistribMulAction G M] [SMulCommClass G k M]

/-- The element `φ_{g,a} = d1 (g⁻¹ • a) - eg g a` of `M^♯`, viewed in `A = M^♯`. -/
noncomputable def phiToA (g : G) (a : M) : A (G:=G) (M:=M) :=
  ⟨phiFun (G:=G) g a, phiFun_mem (G:=G) g a⟩

/-- The map `y ↦ ⟨θ (d₂₁ y), _⟩ : (G × G →₀ M) →+ M^♯`. -/
noncomputable def d21Psi : (G × G →₀ M) →+ A (G:=G) (M:=M) where
  toFun y := ⟨thetaFun (G:=G) ((groupHomology.d₂₁ (repM k G M)).hom y),
      thetaFun_mem_A (k:=k) (groupHomology.d₂₁_apply_mem_cycles₁ (A := repM k G M) y)⟩
  map_zero' := by
    apply Subtype.ext
    show thetaFun (G:=G) ((groupHomology.d₂₁ (repM k G M)).hom 0) = 0
    rw [map_zero, thetaFun_zero]
  map_add' y₁ y₂ := by
    apply Subtype.ext
    show thetaFun (G:=G) ((groupHomology.d₂₁ (repM k G M)).hom (y₁ + y₂))
      = thetaFun (G:=G) ((groupHomology.d₂₁ (repM k G M)).hom y₁)
        + thetaFun (G:=G) ((groupHomology.d₂₁ (repM k G M)).hom y₂)
    rw [map_add, thetaFun_add]

/-- On the generators `single (g,h) a` of the 2-chains, `d21Psi` is `h⁻¹ • φ_{g,a} - φ_{g,a}`. -/
theorem d21Psi_single (g : G × G) (a : M) :
    d21Psi (k:=k) (Finsupp.single g a)
      = g.2⁻¹ • phiToA (G:=G) (M:=M) g.1 a - phiToA (G:=G) (M:=M) g.1 a := by
  obtain ⟨g₁, g₂⟩ := g
  apply Subtype.ext
  show thetaFun (G:=G) ((groupHomology.d₂₁ (repM k G M)).hom (Finsupp.single (g₁,g₂) a))
      = ((g₂⁻¹ • phiToA (G:=G) (M:=M) g₁ a
          - phiToA (G:=G) (M:=M) g₁ a : A (G:=G) (M:=M)) : G → M)
  rw [thetaFun_d21_single]
  rfl

/-- `d21Psi` sends each generator of the 2-chains into the augmentation submodule. -/
theorem d21Psi_single_mem (g : G × G) (a : M) :
    d21Psi (k:=k) (Finsupp.single g a) ∈ Work.Tate.augmentation G (A (G:=G) (M:=M)) := by
  rw [d21Psi_single]
  exact Work.Tate.smul_sub_self_mem_augmentation _ _

/-- `d21Psi` takes all of `(G × G →₀ M)` into the augmentation submodule. -/
theorem d21Psi_mem_augmentation (y : G × G →₀ M) :
    d21Psi (k:=k) y ∈ Work.Tate.augmentation G (A (G:=G) (M:=M)) := by
  induction y using Finsupp.induction with
  | zero =>
      rw [map_zero]
      exact Work.Tate.zero_mem_augmentation
  | single_add a b f _ _ ih =>
      rw [map_add]
      exact add_mem (d21Psi_single_mem a b) ih

theorem ThetaOn_augmentation_of_mem_boundaries (k : Type) [CommRing k] (G : Type) [Group G]
    [Fintype G] [DecidableEq G] (M : Type) [AddCommGroup M] [Module k M] [DistribMulAction G M]
    [SMulCommClass G k M] (b : ↥(Work.Bridge.Z k G M))
    (hb : (b : G →₀ M) ∈ Work.Bridge.B k G M) :
    ((Work.Bridge.ThetaOn k G M b : Work.Bridge.K (G:=G) (M:=M))
        : Work.Bridge.A (G:=G) (M:=M))
      ∈ Work.Tate.augmentation G (Work.Bridge.A (G:=G) (M:=M)) := by
  obtain ⟨y, hy⟩ := hb
  rw [show ((Work.Bridge.ThetaOn k G M b : Work.Bridge.K (G:=G) (M:=M))
        : Work.Bridge.A (G:=G) (M:=M)) = d21Psi (k:=k) y from Subtype.ext (by
      rw [Work.Bridge.ThetaOn_coe]
      show thetaFun (G:=G) (b : G →₀ M)
        = thetaFun (G:=G) ((groupHomology.d₂₁ (repM k G M)).hom y)
      rw [hy])]
  exact d21Psi_mem_augmentation y

end Work.CohomologicalShrinking.bridge
