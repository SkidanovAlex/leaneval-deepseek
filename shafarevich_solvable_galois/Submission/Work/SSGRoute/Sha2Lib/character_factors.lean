import Mathlib
import Submission.Work.SSGRoute.PTDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.Sha2Lib

open Additive

/-- **A hom that vanishes on the kernel of a surjection factors through it.**

Let `f : G →* H` be a surjective group homomorphism and let `g : Additive G →+ A` kill every
element of `f.ker`.  Then `g` factors through `f`: there is `g' : Additive H →+ A` with
`g' (ofMul (f x)) = g (ofMul x)` for all `x`.

The construction is the naive one: fix a section `s` of `f` (`Classical.choose`), set
`g' y := g (ofMul (s y))` and observe that any two preimages of the same point differ by an
element of `ker f`, on which `g` vanishes; additivity is the same computation at `s x * s y`. -/
theorem factor_through_surjective {G H A : Type*} [Group G] [Group H] [AddCommGroup A]
    (f : G →* H) (hf : Function.Surjective f) (g : Additive G →+ A)
    (hg : ∀ x : G, x ∈ f.ker → g (Additive.ofMul x) = 0) :
    ∃ g' : Additive H →+ A, ∀ x : G, g' (Additive.ofMul (f x)) = g (Additive.ofMul x) := by
  classical
  -- a section of `f`
  set s : Additive H → G := fun y => Classical.choose (hf y.toMul) with hs
  have hs' : ∀ y : Additive H, f (s y) = y.toMul := fun y => Classical.choose_spec (hf y.toMul)
  -- `g` only depends on `f x`
  have key : ∀ x y : G, f x = f y → g (Additive.ofMul x) = g (Additive.ofMul y) := by
    intro x y hxy
    have hmem : x⁻¹ * y ∈ f.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hxy, inv_mul_cancel]
    have h0 := hg _ hmem
    rw [ofMul_mul, ofMul_inv, map_add, map_neg] at h0
    exact neg_add_eq_zero.mp h0
  refine ⟨{ toFun := fun y => g (Additive.ofMul (s y))
            map_zero' := ?_, map_add' := ?_ }, ?_⟩
  · have h := key (s 0) (1 : G) (by rw [hs', toMul_zero, map_one])
    rw [ofMul_one, map_zero] at h
    exact h
  · intro x y
    have h := key (s x * s y) (s (x + y)) (by simp only [map_mul, hs', toMul_add])
    rw [ofMul_mul, map_add] at h
    exact h.symm
  · intro x
    exact key (s (ofMul (f x))) x (by rw [hs', toMul_ofMul])

/-- **The character factors through the restriction to `F`.**

For a finite Galois extension `L/k`, an intermediate field `F` and a nonzero additive character
`g : Gal(L/k) → ℤ/p` whose kernel is the fixing subgroup of `F`, there is a nonzero additive
character `gF : Gal(F/k) → ℤ/p` with `g σ = gF (ofMul (galRes k F L σ))` for all `σ`.
(`galRes k F L` is `SSGRoute.PTExt.galRes`; `open SSGRoute.PTExt` so that it is in scope.)

Route: `IntermediateField.restrictNormalHom_ker` identifies `ker (galRes k F L)` with
`F.fixingSubgroup` (which is `ker g` by hypothesis), and `AlgEquiv.restrictNormalHom_surjective`
makes `galRes k F L` onto, so `g` factors through `galRes`: pick a section `s` of `galRes` and set
`gF y := g (s y)` (well defined because `σ⁻¹τ ∈ ker (galRes) = ker g` whenever `galRes σ = galRes τ`,
and additive for the same reason, using `Additive.ofMul_mul`/`Additive.ofMul_inv`).
`gF ≠ 0` because `g ≠ 0` and `galRes` is onto. -/
theorem character_factors (k L : Type) [Field k] [NumberField k] [Field L] [NumberField L]
    [Algebra k L] [FiniteDimensional k L] [IsGalois k L]
    (p : ℕ) [Fact p.Prime] (F : IntermediateField k L) [FiniteDimensional k F] [NumberField F]
    [IsGalois k F]
    (g : Additive (L ≃ₐ[k] L) →+ ZMod p) (hne : g ≠ 0)
    (hker : ∀ σ : L ≃ₐ[k] L, g (Additive.ofMul σ) = 0 ↔ σ ∈ F.fixingSubgroup) :
    ∃ gF : Additive (F ≃ₐ[k] F) →+ ZMod p, gF ≠ 0 ∧
      ∀ σ : L ≃ₐ[k] L, g (Additive.ofMul σ) = gF (Additive.ofMul (SSGRoute.PTExt.galRes k F L σ)) := by
  classical
  -- `F/k` is normal (it is even Galois), so restriction to `F` makes sense and is onto
  have hsurj : Function.Surjective (SSGRoute.PTExt.galRes k F L) :=
    AlgEquiv.restrictNormalHom_surjective (F := k) (K₁ := ↥F) (E := L)
  -- its kernel is exactly the fixing subgroup of `F`, i.e. `ker g`
  have hkerf : (SSGRoute.PTExt.galRes k F L).ker = F.fixingSubgroup :=
    IntermediateField.restrictNormalHom_ker F
  have hg : ∀ x : L ≃ₐ[k] L, x ∈ (SSGRoute.PTExt.galRes k F L).ker →
      g (Additive.ofMul x) = 0 :=
    fun x hx => (hker x).mpr (hkerf ▸ hx)
  -- hence `g` factors through `galRes k F L`
  obtain ⟨gF, hgF⟩ := factor_through_surjective (SSGRoute.PTExt.galRes k F L) hsurj g hg
  refine ⟨gF, ?_, fun σ => (hgF σ).symm⟩
  -- and it is nonzero because `g` is nonzero and `galRes k F L` is onto
  intro hzero
  apply hne
  refine AddMonoidHom.ext fun x => ?_
  have hx := hgF (Additive.toMul x)
  rw [hzero] at hx
  simpa using hx.symm

end Work.SSGRoute.Sha2Lib
