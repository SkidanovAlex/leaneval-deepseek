import Mathlib
import Submission.Work.SSGRoute.Interfaces
import Submission.Work.SSGRoute.place_basics
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute

open _root_.SSGRoute
open scoped Pointwise

set_option linter.unusedVariables false

/-! ## Conjugating a subgroup

`conjSubgroup a S` is the subgroup `a S a⁻¹ = {x | a⁻¹ x a ∈ S}`, the conjugate of `S` by `a`.
It is the subgroup on which the right-translation argument for the corestriction runs: for an
element `u` in `⋂_s conjSubgroup (sec s) U₀` the conjugate `(sec s)⁻¹ u (sec s)` lands back in `U₀`,
which is exactly the input `IsLocConstOn` needs. -/

/-- The conjugate `a S a⁻¹` of a subgroup `S` by a group element `a`, presented as the set
`{x | a⁻¹ * x * a ∈ S}`. -/
def conjSubgroup {G : Type*} [Group G] (a : G) (S : Subgroup G) : Subgroup G where
  carrier := {x | a⁻¹ * x * a ∈ S}
  one_mem' := by simp
  mul_mem' := by
    intro x y hx hy
    show a⁻¹ * (x * y) * a ∈ S
    have h : a⁻¹ * (x * y) * a = (a⁻¹ * x * a) * (a⁻¹ * y * a) := by group
    rw [h]
    exact S.mul_mem hx hy
  inv_mem' := by
    intro x hx
    show a⁻¹ * x⁻¹ * a ∈ S
    have h : a⁻¹ * x⁻¹ * a = (a⁻¹ * x * a)⁻¹ := by group
    rw [h]
    exact S.inv_mem hx

@[simp]
theorem mem_conjSubgroup {G : Type*} [Group G] {a : G} {S : Subgroup G} {x : G} :
    x ∈ conjSubgroup a S ↔ a⁻¹ * x * a ∈ S := Iff.rfl

/-- Conjugating an open subgroup of a topological group gives an open subgroup. -/
theorem isOpen_conjSubgroup {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (a : G) (S : Subgroup G) (hS : IsOpen (S : Set G)) :
    IsOpen ((conjSubgroup a S : Subgroup G) : Set G) := by
  have hset : ((conjSubgroup a S : Subgroup G) : Set G)
      = (fun x : G => a⁻¹ * x * a) ⁻¹' (S : Set G) := rfl
  rw [hset]
  exact hS.preimage (by continuity)

/-- The formal corestriction `X δ = ∑_{s : Gal(K/k)} s • y(sec(s)⁻¹ * δ * sec(s))` is locally constant
on `G_K = K.fixingSubgroup` whenever `y` is.

If `U₀` is an open subgroup on which `y` is right-`U₀`-constant on `G_K`, then
`U := ⋂_{s : K ≃ₐ[k] K} (sec s) U₀ (sec s)⁻¹` is a finite intersection of conjugates of the open
subgroup `U₀` (hence open), and for `δ ∈ G_K`, `u ∈ U ∩ G_K` and every `s`,
`(sec s)⁻¹ (δ*u) (sec s) = ((sec s)⁻¹ δ sec s) · ((sec s)⁻¹ u sec s)` with
`(sec s)⁻¹ u sec s ∈ U₀ ∩ G_K`, so `y` has the same value at `(sec s)⁻¹ δ sec s` and at
`(sec s)⁻¹ (δ*u) sec s`; summing gives `X (δ*u) = X δ`. -/
theorem isLocConstOn_corestriction (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k]
    [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
    (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    [Fintype (K ≃ₐ[k] K)]
    (E : Type) [AddCommGroup E] [Module (ZMod p) E] [DistribMulAction (K ≃ₐ[k] K) E]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E]
    (y : (Ω ≃ₐ[k] Ω) → E)
    (hy : ∀ g ∈ K.fixingSubgroup, ∀ h ∈ K.fixingSubgroup, y (g * h) = y g + y h)
    (hyc : IsLocConstOn K.fixingSubgroup y)
    (sec : (K ≃ₐ[k] K) → (Ω ≃ₐ[k] Ω)) (hsec : ∀ s, res k K (sec s) = s) :
    IsLocConstOn K.fixingSubgroup (fun δ => ∑ s : K ≃ₐ[k] K, s • y ((sec s)⁻¹ * δ * sec s)) := by
  obtain ⟨U₀, hU₀open, hU₀prop⟩ := hyc
  -- `K.fixingSubgroup` is the kernel of the restriction `res k K : G_k →* Gal(K/k)`.
  have hker : ∀ (u : Ω ≃ₐ[k] Ω), res k K u = 1 ↔ u ∈ K.fixingSubgroup := by
    intro u
    rw [show res k K u = u.restrictNormal K from rfl, AlgEquiv.restrictNormal_eq_one_iff,
      IntermediateField.mem_fixingSubgroup_iff]
  -- The open subgroup `U = ⋂_s (sec s) U₀ (sec s)⁻¹` on which the corestriction is right-constant.
  refine ⟨⨅ s : K ≃ₐ[k] K, conjSubgroup (sec s) U₀, ?_, ?_⟩
  · -- It is open: a finite intersection of conjugates of the open subgroup `U₀`.
    rw [Subgroup.coe_iInf]
    exact isOpen_iInter_of_finite (fun s => isOpen_conjSubgroup (sec s) U₀ hU₀open)
  · intro δ hδ u hu huH
    -- Every summand is unchanged, since `(sec s)⁻¹ u (sec s) ∈ U₀ ∩ G_K`.
    have key : ∀ s : K ≃ₐ[k] K,
        y ((sec s)⁻¹ * (δ * u) * sec s) = y ((sec s)⁻¹ * δ * sec s) := by
      intro s
      have hδ' : (sec s)⁻¹ * δ * sec s ∈ K.fixingSubgroup := by
        rw [← hker, map_mul, map_mul, map_inv, hsec s, (hker δ).mpr hδ]
        simp
      have huH' : (sec s)⁻¹ * u * sec s ∈ K.fixingSubgroup := by
        rw [← hker, map_mul, map_mul, map_inv, hsec s, (hker u).mpr huH]
        simp
      have hu' : (sec s)⁻¹ * u * sec s ∈ U₀ := Subgroup.mem_iInf.mp hu s
      have hmul : (sec s)⁻¹ * (δ * u) * sec s
          = ((sec s)⁻¹ * δ * sec s) * ((sec s)⁻¹ * u * sec s) := by group
      rw [hmul]
      exact hU₀prop _ hδ' _ hu' huH'
    refine Finset.sum_congr rfl (fun s _ => ?_)
    show s • y ((sec s)⁻¹ * (δ * u) * sec s) = s • y ((sec s)⁻¹ * δ * sec s)
    rw [key s]

end Work.SSGRoute
