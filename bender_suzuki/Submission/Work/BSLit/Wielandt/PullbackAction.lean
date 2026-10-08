import Mathlib
import Submission.Work.BSLit.Defs
import Submission.Work.Coprime.Defs
import Submission.Work.Coprime.Basic

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# Restricting an automorphism action `ρ : F →* MulAut Q` to a subgroup `H ≤ F`

`Work.BSLit.fixedBy ρ H` is the subgroup of `Q` fixed by `H`, where `F` acts on `Q` through the
monoid homomorphism `ρ : F →* MulAut Q`.  The library of coprime-action results
(`Submission.Work.Coprime`, `Submission.Work.Hering.AppVII`) is phrased in terms of a
`MulDistribMulAction A G` and the subgroup `FT.fixedPoints A G`.

This file provides the translation between the two languages:

* `pullbackAction ρ H` — the `MulDistribMulAction ↥H Q` obtained by restricting `ρ` to `H`
  (pull the tautological `MulAut`-action back along `ρ.comp H.subtype`);
* `pullbackAction_smul` — its computation rule, `h • q = ρ h q`;
* `fixedPoints_pullbackAction` — `C_Q(H)` is `fixedBy ρ H`;
* `isInvariant_pullbackAction` — an `F`-invariant subgroup `N` (i.e. `N.map (ρ g) = N`) is
  `H`-invariant for `pullbackAction ρ H`;
* `fixedPoints_quotientAction_pullbackAction` — the fixed points of `H` on the quotient `Q ⧸ N`
  computed with the canonical quotient action of the coprime-action library coincide with
  `fixedBy (quotientAction ρ N hN) H`.
-/

set_option autoImplicit false
set_option linter.style.haveILetI false

open scoped Pointwise

namespace Work.BSLit.Wielandt

variable {F Q : Type*} [Group F] [Group Q]

/-- The action of a subgroup `H ≤ F` on `Q` obtained by restricting the action `ρ : F →* MulAut Q`
along the inclusion `H →* F`. -/
noncomputable def pullbackAction (ρ : F →* MulAut Q) (H : Subgroup F) : MulDistribMulAction H Q :=
  MulDistribMulAction.compHom Q (ρ.comp H.subtype)

/-- Computation rule for `pullbackAction`. -/
theorem pullbackAction_smul (ρ : F →* MulAut Q) (H : Subgroup F) (h : H) (q : Q) :
    letI := pullbackAction ρ H
    h • q = ρ (h : F) q := rfl

/-- `C_Q(H)`, computed with the restricted action, is `fixedBy ρ H`. -/
theorem fixedPoints_pullbackAction (ρ : F →* MulAut Q) (H : Subgroup F) :
    @FT.fixedPoints H Q _ _ (pullbackAction ρ H) = fixedBy ρ H := by
  ext q
  simp only [FT.mem_fixedPoints, mem_fixedBy]
  exact ⟨fun h g hg => h ⟨g, hg⟩, fun h g => h g g.2⟩

/-- An `F`-invariant subgroup `N` of `Q` is invariant under the restricted action of `H`. -/
theorem isInvariant_pullbackAction (ρ : F →* MulAut Q) (N : Subgroup Q)
    (hN : ∀ g : F, N.map (ρ g) = N) (H : Subgroup F) :
    @FT.IsInvariant H Q _ _ (pullbackAction ρ H) N := by
  letI := pullbackAction ρ H
  refine ⟨fun h => ?_⟩
  rw [Subgroup.pointwise_smul_def]
  have hkey : (MulDistribMulAction.toMonoidEnd H Q) h = (ρ (h : F) : Q →* Q) := by
    ext q
    rfl
  rw [hkey, hN]

/-- The fixed points of `H` on the quotient `Q ⧸ N`, computed with the canonical quotient action
induced by `pullbackAction ρ H`, are exactly the fixed points of `H` for the quotient action
`quotientAction ρ N hN` on the cosets. -/
theorem fixedPoints_quotientAction_pullbackAction (ρ : F →* MulAut Q) (N : Subgroup Q) [N.Normal]
    (hN : ∀ g : F, N.map (ρ g) = N) (H : Subgroup F)
    (hInv : @FT.IsInvariant H Q _ _ (pullbackAction ρ H) N) :
    @FT.fixedPoints H (Q ⧸ N) _ _
        (@FT.instQuotientMulDistribMulAction H Q _ _ (pullbackAction ρ H) N _ hInv)
      = fixedBy (quotientAction ρ N hN) H := by
  letI := pullbackAction ρ H
  haveI := hInv
  have key : ∀ (a : H) (x : Q ⧸ N), a • x = quotientAction ρ N hN (a : F) x := by
    intro a x
    refine Quotient.inductionOn x (fun q => ?_)
    rw [FT.quotient_smul_mk, quotientAction_mk]
    rfl
  ext x
  simp only [FT.mem_fixedPoints, mem_fixedBy]
  constructor
  · intro h g hg
    have h1 := h ⟨g, hg⟩
    rwa [key ⟨g, hg⟩ x] at h1
  · intro h a
    rw [key a x]
    exact h a a.2

end Work.BSLit.Wielandt
