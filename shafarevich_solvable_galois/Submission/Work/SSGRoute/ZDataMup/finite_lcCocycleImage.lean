import Mathlib.FieldTheory.KrullTopology
import Mathlib.GroupTheory.Nilpotent
import Mathlib.RingTheory.Henselian
import Mathlib.Algebra.Field.ZMod
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.Valuation.ValuationSubring
import Submission.Work.SSGRoute.ZDataMup.QuotDefs
import Submission.Work.SSGRoute.finite_openKernel_homs_decomp_kernel
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Finiteness of the locally constant cocycles on a level-`K` local group

`lcCocycleImage K H` is the image of the locally constant `1`-cocycles on `G_k` (a submodule of the
functions `G_k → ZMod p`, restricted to `H`) inside the functions `↥H → ZMod p`.  For the level-`K`
local group `H = decomp k A ⊓ K.fixingSubgroup` of a finite place `A`, the target
`finite_lcCocycleImage` shows that this image is **finite**.

## Route

An element `x` of `lcCocycleImage K H` is the restriction to `H` of a cocycle `b` which is locally
constant on `H`.  Because `res k K` is trivial on `H ≤ K.fixingSubgroup`
(`res_eq_one_of_mem_fixingSubgroup`), the cocycle condition on `H` is exactly additivity
`x (g * h) = x g + x h`, and the local constancy of `b` says that the kernel of the resulting
homomorphism `x : ↥H →* Multiplicative (ZMod p)` contains an open subgroup.  So `x ↦` its
underlying homomorphism is an injection of `↥(lcCocycleImage K H)` into the finite set

`{χ : ↥H →* Multiplicative (ZMod p) // IsOpen (χ.ker : Set ↥H)}`

of `Work.SSGRoute.finite_openKernel_homs_decomp_kernel`.
-/

namespace Work.SSGRoute.ZDataMup

open scoped Pointwise

open _root_.SSGRoute

/-- **The locally constant `H`-cocycles are homomorphisms with open kernel.**  For `H ≤ G_K` a
level-`K` local group, the underlying function `x : ↥H → ZMod p` of an element of
`lcCocycleImage K H` is (additively) a group homomorphism `↥H →* Multiplicative (ZMod p)`, and its
kernel is open for the subspace (Krull) topology of `↥H`.

The cocycle condition `b (g * h) = b g + res k K g • b h` becomes additivity on `H` because
`res k K` is trivial there; local constancy produces an open subgroup `U ≤ G_k` with
`U ∩ H ≤ ker x`, and an open subgroup contained in a subgroup makes it open. -/
theorem lcCocycleImage_hom {p : ℕ} {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω]
    {K : IntermediateField k Ω} [Normal k K]
    [DistribMulAction (K ≃ₐ[k] K) (ZMod p)] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) (ZMod p)]
    {H : Subgroup (Ω ≃ₐ[k] Ω)} (hH : H ≤ K.fixingSubgroup)
    (x : ↥(lcCocycleImage (p := p) K H)) :
    ∃ χ : ↥H →* Multiplicative (ZMod p), χ.toFun = x.1 ∧ IsOpen (χ.ker : Set ↥H) := by
  obtain ⟨b, hb, hbx⟩ := (Submodule.mem_map).mp x.2
  have hbxf : ∀ g : ↥H, b g.1 = x.1 g := by
    intro g
    have h := congrFun hbx g
    simpa using h
  have hone : b 1 = 0 := by
    have h := hb.1 1 H.one_mem 1 H.one_mem
    rw [mul_one, map_one, one_smul] at h
    have h2 : b 1 + b 1 = b 1 + 0 := by rw [add_zero]; exact h.symm
    exact add_left_cancel h2
  obtain ⟨U, hUopen, hUprop⟩ := hb.2
  let χ : ↥H →* Multiplicative (ZMod p) :=
    { toFun := x.1
      map_one' := by
        show x.1 1 = (0 : ZMod p)
        rw [← hbxf 1]
        exact hone
      map_mul' := by
        intro g h
        show x.1 (g * h) = x.1 g + x.1 h
        have hc := hb.1 g.1 g.2 h.1 h.2
        rw [res_eq_one_of_mem_fixingSubgroup (hH g.2), one_smul] at hc
        rw [← hbxf g, ← hbxf h, ← hbxf (g * h)]
        exact hc }
  refine ⟨χ, rfl, ?_⟩
  refine Subgroup.isOpen_mono ?_ (Subgroup.subgroupOf_isOpen H U hUopen)
  intro u hu
  rw [Subgroup.mem_subgroupOf] at hu
  rw [MonoidHom.mem_ker]
  show x.1 u = (0 : ZMod p)
  have h := hUprop 1 H.one_mem u.1 hu u.2
  rw [one_mul, hone] at h
  rw [← hbxf u]
  exact h

theorem finite_lcCocycleImage {p : ℕ} [Fact p.Prime] {k Ω : Type} [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] {K : IntermediateField k Ω}
    [FiniteDimensional k K] [IsGalois k K]
    [DistribMulAction (K ≃ₐ[k] K) (ZMod p)] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) (ZMod p)]
    {A : ValuationSubring Ω} (hA : SSGRoute.IsFinPlace k A) :
    Finite ↥(Work.SSGRoute.ZDataMup.lcCocycleImage (p := p) K
      (SSGRoute.decomp k A ⊓ K.fixingSubgroup)) := by
  let H : Subgroup (Ω ≃ₐ[k] Ω) := SSGRoute.decomp k A ⊓ K.fixingSubgroup
  have hH : H ≤ K.fixingSubgroup := inf_le_right
  haveI : Finite {χ : ↥H →* Multiplicative (ZMod p) // IsOpen (χ.ker : Set ↥H)} :=
    finite_openKernel_homs_decomp_kernel p k Ω K A hA (ZMod p)
  let Ψ : ↥(lcCocycleImage (p := p) K H) →
      {χ : ↥H →* Multiplicative (ZMod p) // IsOpen (χ.ker : Set ↥H)} :=
    fun x => let χ := Classical.choose (lcCocycleImage_hom hH x)
             ⟨χ, (Classical.choose_spec (lcCocycleImage_hom hH x)).2⟩
  have hΨ : ∀ x, ⇑(Ψ x).1 = x.1 := fun x =>
    (Classical.choose_spec (lcCocycleImage_hom hH x)).1
  have hinj : Function.Injective Ψ := by
    intro x y hxy
    apply Subtype.ext
    funext g
    have h1 : (Ψ x).1 = (Ψ y).1 := congrArg Subtype.val hxy
    have h3 := congrArg (fun f : ↥H →* Multiplicative (ZMod p) => f g) h1
    rw [hΨ x, hΨ y] at h3
    exact h3
  exact Finite.of_injective Ψ hinj

end Work.SSGRoute.ZDataMup
