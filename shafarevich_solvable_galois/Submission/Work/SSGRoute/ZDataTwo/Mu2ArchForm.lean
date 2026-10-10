import Mathlib.FieldTheory.KrullTopology
import Mathlib.GroupTheory.Nilpotent
import Mathlib.RingTheory.Henselian
import Mathlib.Algebra.Algebra.ZMod
import Mathlib.Algebra.Field.ZMod
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Submission.Work.SSGRoute.ZDataTwo.Mu2InvolutionForm
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END
/-!
# The `p = 2` local Tate system with archimedean terms

The predicate `Work.SSGRoute.ZDataTwo.IsMu2LocalTateSystemWithArch` is established from a family of
local forms on the local cohomology `H1loc 2 k Ω K (ZMod 2) H` which is non-degenerate at every
local group and whose values on the classes of global cocycles satisfy the archimedean-corrected
reciprocity identity; the formal passage from such a family to the predicate is
`Work.SSGRoute.ZDataTwo.mu2LocalTateSystemWithArch_of_forms`
(module `Submission.Work.SSGRoute.ZDataTwo.Mu2ArchReduction`).

The remaining arithmetic input is the existence of such a family: the local Tate pairing at a finite
place in the `μ₂` case, whose value on the classes of the global cocycles with Kummer elements
`α, β ∈ kˣ` is `⟪α, β⟫_v` — the local Hilbert symbol at the prime `v` of `k` below the prime from
`k⟮√α⟯`, i.e. the indicator of "`β` is not a local norm at `v` from `k⟮√α⟯`" — bilinear and
non-degenerate because the local norm subgroup of a quadratic local extension has index two and by
the norm criterion `NK.NUV2.LC.hilbertSymbol_eq_one_iff_normGroup`; together with the archimedean
pairing at an involution `c`, whose value on a global pair is `a c * b c`; the reciprocity identity
is then the product formula `Work.HilbertSymbolGeneral.hilbertReciprocityTwo`.

This file contains the archimedean half of the construction in full (the functional "evaluate an
involution at `c`", its well-definedness on `H1loc`, the form `Φ x y = (x c) * (y c)`, its value on
the classes of global cocycles, and its non-degeneracy); the finite-place half is assembled from the
local Hilbert symbol and the Kummer dictionary.  See `NOTES_mu2_plan.md` in this directory for the
complete architecture and the delegation queue.
-/

namespace Work.SSGRoute.ZDataTwo

open _root_.SSGRoute

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

variable (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
  (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
  [DistribMulAction (K ≃ₐ[k] K) (ZMod 2)] [SMulCommClass (K ≃ₐ[k] K) (ZMod 2) (ZMod 2)]

/-! ## The archimedean local form -/

/-- The cochain functional "evaluate at `c`", on the module of locally constant cocycles. -/
noncomputable def evalCocycle (c : Ω ≃ₐ[k] Ω) :
    ↥(lcCocycles 2 k Ω K (ZMod 2) (Subgroup.zpowers c)) →ₗ[ZMod 2] ZMod 2 where
  toFun f := (f : (Ω ≃ₐ[k] Ω) → ZMod 2) c
  map_add' f g := rfl
  map_smul' m f := rfl

lemma evalCocycle_apply (c : Ω ≃ₐ[k] Ω)
    (f : ↥(lcCocycles 2 k Ω K (ZMod 2) (Subgroup.zpowers c))) :
    evalCocycle k Ω K c f = (f : (Ω ≃ₐ[k] Ω) → ZMod 2) c := rfl

/-- **The evaluation at an involution is well defined on the local cohomology.**  A coboundary on
`⟨c⟩` vanishes identically (the action of `Gal(K/k)` on `ZMod 2` is trivial), so the cochain
functional "evaluate at `c`" descends to `H1loc` (this is the class-level form of
`Mu2InvolutionForm.eval_zpowers_wellDefined`). -/
noncomputable def evalAtInv (c : Ω ≃ₐ[k] Ω) :
    H1loc 2 k Ω K (ZMod 2) (Subgroup.zpowers c) →ₗ[ZMod 2] ZMod 2 :=
  Submodule.liftQ _ (evalCocycle k Ω K c) (by
    intro f hf
    have h2 : IsCoboundaryOn (res k K) (Subgroup.zpowers c) (f : (Ω ≃ₐ[k] Ω) → ZMod 2) :=
      (mem_coboundaries 2 k Ω K (ZMod 2) (Subgroup.zpowers c) _).mp (Submodule.mem_comap.mp hf)
    have h3 := (isCoboundaryOn_iff_eq_zero k Ω K (Subgroup.zpowers c)
      (f : (Ω ≃ₐ[k] Ω) → ZMod 2)).mp h2
    show evalCocycle k Ω K c f = 0
    rw [evalCocycle_apply]
    exact h3 c (Subgroup.mem_zpowers c))

/-- The computation rule for `evalAtInv` on the class of a cocycle. -/
lemma evalAtInv_toClass (c : Ω ≃ₐ[k] Ω) {f : (Ω ≃ₐ[k] Ω) → ZMod 2}
    (hf : f ∈ lcCocycles 2 k Ω K (ZMod 2) (Subgroup.zpowers c)) :
    evalAtInv k Ω K c (toClass 2 k Ω K (ZMod 2) (Subgroup.zpowers c) f) = f c := by
  rw [evalAtInv, toClass, dif_pos hf]
  rfl

/-- **The evaluation at an involution is injective** (at an involution `c` with `c ^ 2 = 1`): a
local class with `x c = 0` is zero, because a cocycle on `{1, c}` vanishing at `c` vanishes at `1`
as well, hence is a coboundary. -/
lemma evalAtInv_eq_zero_iff {c : Ω ≃ₐ[k] Ω} (hc : c ^ 2 = 1)
    (x : H1loc 2 k Ω K (ZMod 2) (Subgroup.zpowers c)) :
    evalAtInv k Ω K c x = 0 ↔ x = 0 := by
  constructor
  · intro hx
    obtain ⟨f, hf, rfl⟩ := toClass_surjective 2 k Ω K (ZMod 2) (Subgroup.zpowers c) x
    have hfc : f c = 0 := by rw [← evalAtInv_toClass k Ω K c hf]; exact hx
    have hadd := (isCocycleOn_iff_add k Ω K (Subgroup.zpowers c) f).mp hf.1
    have hvan : ∀ g ∈ Subgroup.zpowers c, f g = 0 := by
      intro g hg
      rcases mem_zpowers_eq_one_or k Ω c hc hg with h1 | h1
      · rw [h1]; exact eq_zero_one_of_cocycle_zpowers hc hadd
      · rw [h1]; exact hfc
    have hcob : IsCoboundaryOn (res k K) (Subgroup.zpowers c) f :=
      (isCoboundaryOn_iff_eq_zero k Ω K (Subgroup.zpowers c) f).mpr hvan
    rw [toClass_eq_zero_iff 2 k Ω K (ZMod 2) (Subgroup.zpowers c) hf]
    exact (mem_coboundaries 2 k Ω K (ZMod 2) (Subgroup.zpowers c) f).mpr hcob
  · intro hx; rw [hx]; exact map_zero _

/-- **The archimedean local form** at an involution: `Φ c x y = (x c) * (y c)`. -/
noncomputable def archForm (c : Ω ≃ₐ[k] Ω) :
    H1loc 2 k Ω K (ZMod 2) (Subgroup.zpowers c) →ₗ[ZMod 2]
      (H1loc 2 k Ω K (ZMod 2) (Subgroup.zpowers c) →ₗ[ZMod 2] ZMod 2) :=
  (evalAtInv k Ω K c).smulRight (evalAtInv k Ω K c)

lemma archForm_apply (c : Ω ≃ₐ[k] Ω)
    (x y : H1loc 2 k Ω K (ZMod 2) (Subgroup.zpowers c)) :
    archForm k Ω K c x y = evalAtInv k Ω K c x * evalAtInv k Ω K c y := by
  rw [archForm, LinearMap.smulRight_apply, LinearMap.smul_apply, smul_eq_mul]

/-- **The value of the archimedean form on the classes of global cocycles** is `a c * b c`. -/
lemma archForm_toClass {c : Ω ≃ₐ[k] Ω} {f g : (Ω ≃ₐ[k] Ω) → ZMod 2}
    (hf : f ∈ lcCocycles 2 k Ω K (ZMod 2) (Subgroup.zpowers c))
    (hg : g ∈ lcCocycles 2 k Ω K (ZMod 2) (Subgroup.zpowers c)) :
    archForm k Ω K c (toClass 2 k Ω K (ZMod 2) (Subgroup.zpowers c) f)
        (toClass 2 k Ω K (ZMod 2) (Subgroup.zpowers c) g) = f c * g c := by
  rw [archForm_apply, evalAtInv_toClass k Ω K c hf, evalAtInv_toClass k Ω K c hg]

/-- **Non-degeneracy of the archimedean form** at an involution. -/
lemma archForm_nondegenerate {c : Ω ≃ₐ[k] Ω} (hc : c ^ 2 = 1) :
    (∀ x : H1loc 2 k Ω K (ZMod 2) (Subgroup.zpowers c),
        (∀ y, archForm k Ω K c x y = 0) → x = 0) ∧
      (∀ y : H1loc 2 k Ω K (ZMod 2) (Subgroup.zpowers c),
        (∀ x, archForm k Ω K c x y = 0) → y = 0) := by
  have key : ∀ x : H1loc 2 k Ω K (ZMod 2) (Subgroup.zpowers c),
      archForm k Ω K c x x = 0 → x = 0 := by
    intro x hx
    rw [archForm_apply] at hx
    have hzero : evalAtInv k Ω K c x = 0 := by
      rcases mul_eq_zero.mp hx with h | h
      · exact h
      · exact h
    exact (evalAtInv_eq_zero_iff k Ω K hc x).mp hzero
  exact ⟨fun x hx => key x (hx x), fun y hy => key y (hy y)⟩

end Work.SSGRoute.ZDataTwo
