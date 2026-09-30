import Mathlib
import Submission.Work.Pi6.SRANGE.Defs
import Submission.Work.Pi6.SRANGE.intR_map_ker_eq_range
import Submission.Work.Pi6.SRANGE.bijective_mapQ_iff
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

/-!
# Extension of scalars preserves the presentation `Z ⧸ B`

Let `ι₁ : B₁ → Z₁`, `ι₂ : B₂ → Z₂` be injective `ℤ`-linear maps, `b : B₁ → B₂` and
`z : Z₁ → Z₂` with `z ∘ ι₁ = ι₂ ∘ b`.  Assume

* `h1` : `z ⁻¹' (range ι₂) ⊆ range ι₁`, i.e. the induced map `z̄ : Z₁ ⧸ B₁ → Z₂ ⧸ B₂` is injective;
* `h2` : `range z + range ι₂ = Z₂`, i.e. `z̄` is surjective;

equivalently `z̄` is an isomorphism between the two presentations of the same cokernel.  Then for
every commutative ring `S` the same two properties hold after extension of scalars along `ℤ → S`:
the base change of `z` still presents the base-changed cokernel, i.e.

* `x̄ ∈ range (ι₂ ⊗ S)` implies `x ∈ range (ι₁ ⊗ S)` for `x : Z₁ ⊗ S`,
* every `y : Z₂ ⊗ S` is congruent modulo `range (ι₂ ⊗ S)` to a class in the image of `z ⊗ S`.

The mathematical content is right exactness of `- ⊗[ℤ] S` (`intR_map_ker_eq_range`): with the
quotient maps `qᵢ : Zᵢ → Zᵢ ⧸ Bᵢ` one has `ker (qᵢ ⊗ S) = range (ιᵢ ⊗ S)`, while
`z̄ ⊗ S : (Z₁ ⧸ B₁) ⊗ S → (Z₂ ⧸ B₂) ⊗ S` is an isomorphism because `z̄` is
(injectivity: `intRPres_bcMap_injective_of_bijective`; surjectivity: `intRKerBcMap_surjective`).
-/

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

namespace Work.Pi6.SRANGE

noncomputable section

-- Make the module structures on submodules and quotients the ones induced from the ambient
-- module, so that the various `Submodule` constructions are `defeq`-compatible.
attribute [local instance 5000] Submodule.module
attribute [local instance 5000] Submodule.Quotient.module

/-- Extension of scalars along `ℤ → S` sends a bijective `ℤ`-linear map to an injective map:
the base change of a linear inverse of `f` is a linear left inverse of `f ⊗ S`, and this is
checked on the tensor product level, where `lTensor` is available. -/
lemma intRPres_bcMap_injective_of_bijective (S : Type) [CommRing S] {M N : Type}
    [AddCommGroup M] [Module ℤ M] [AddCommGroup N] [Module ℤ N]
    (f : M →ₗ[ℤ] N) (hf : Function.Bijective f) :
    Function.Injective (intRKerBcMap S f) := by
  let e : M ≃ₗ[ℤ] N := LinearEquiv.ofBijective f hf
  have hcomp : e.symm.toLinearMap.comp f = LinearMap.id := by
    ext x
    have hx : e x = f x := LinearEquiv.ofBijective_apply (f := f) (hf := hf) x
    rw [LinearMap.comp_apply, LinearMap.id_apply, ← hx] <;>
      exact LinearEquiv.symm_apply_apply e x
  have hstep : ∀ u : intRKerRmod S ⊗[ℤ] M,
      (LinearMap.lTensor (intRKerRmod S) e.symm.toLinearMap)
        ((LinearMap.lTensor (intRKerRmod S) f) u) = u := by
    intro u
    rw [← LinearMap.comp_apply, ← LinearMap.lTensor_comp, hcomp,
      LinearMap.lTensor_id] <;> rfl
  have h1 : Function.Injective ⇑(LinearMap.lTensor (intRKerRmod S) f) := by
    intro u v huv
    have hu := hstep u
    have hv := hstep v
    rw [huv] at hu
    exact hu.symm.trans hv
  rwa [← intRKerBcMap_fun_eq_lTensor (R := S) f] at h1

theorem intR_presentation_bijective (S : Type) [CommRing S]
    {B₁ Z₁ B₂ Z₂ : Type}
    [AddCommGroup B₁] [Module ℤ B₁] [AddCommGroup Z₁] [Module ℤ Z₁]
    [AddCommGroup B₂] [Module ℤ B₂] [AddCommGroup Z₂] [Module ℤ Z₂]
    (ι₁ : B₁ →ₗ[ℤ] Z₁) (hι₁ : Function.Injective ι₁)
    (ι₂ : B₂ →ₗ[ℤ] Z₂) (hι₂ : Function.Injective ι₂)
    (b : B₁ →ₗ[ℤ] B₂) (z : Z₁ →ₗ[ℤ] Z₂) (hz : z.comp ι₁ = ι₂.comp b)
    (h1 : ∀ x : Z₁, z x ∈ LinearMap.range ι₂ → x ∈ LinearMap.range ι₁)
    (h2 : ∀ w : Z₂, ∃ w' : Z₁, ∃ v : B₂, z w' + ι₂ v = w) :
    (∀ x : ↥((Work.Pi6.SRANGE.IntR S).obj (ModuleCat.of ℤ Z₁)),
        (ModuleCat.Hom.hom ((Work.Pi6.SRANGE.IntR S).map (ModuleCat.ofHom z))) x
            ∈ LinearMap.range (ModuleCat.Hom.hom ((Work.Pi6.SRANGE.IntR S).map (ModuleCat.ofHom ι₂))) →
          x ∈ LinearMap.range (ModuleCat.Hom.hom ((Work.Pi6.SRANGE.IntR S).map (ModuleCat.ofHom ι₁))))
    ∧ (∀ y : ↥((Work.Pi6.SRANGE.IntR S).obj (ModuleCat.of ℤ Z₂)),
        ∃ x : ↥((Work.Pi6.SRANGE.IntR S).obj (ModuleCat.of ℤ Z₁)),
          (ModuleCat.Hom.hom ((Work.Pi6.SRANGE.IntR S).map (ModuleCat.ofHom z))) x - y
            ∈ LinearMap.range (ModuleCat.Hom.hom ((Work.Pi6.SRANGE.IntR S).map (ModuleCat.ofHom ι₂)))) := by
  change (∀ x : ↥((IntR S).obj (ModuleCat.of ℤ Z₁)),
        intRKerBcMap S z x ∈ LinearMap.range (intRKerBcMap S ι₂) →
          x ∈ LinearMap.range (intRKerBcMap S ι₁)) ∧
    (∀ y : ↥((IntR S).obj (ModuleCat.of ℤ Z₂)),
      ∃ x : ↥((IntR S).obj (ModuleCat.of ℤ Z₁)),
        intRKerBcMap S z x - y ∈ LinearMap.range (intRKerBcMap S ι₂))
  -- ### Step 1: the induced map of quotients `zbar : Z₁ ⧸ B₁ → Z₂ ⧸ B₂` and its bijectivity
  let p₁ : Submodule ℤ Z₁ := LinearMap.range ι₁
  let p₂ : Submodule ℤ Z₂ := LinearMap.range ι₂
  have hz' : ∀ u : B₁, z (ι₁ u) = ι₂ (b u) := fun u => by
    have h := congrArg (fun (g : B₁ →ₗ[ℤ] Z₂) => g u) hz
    simpa only [LinearMap.comp_apply] using h
  have hle : p₁ ≤ Submodule.comap z p₂ := by
    intro x hx
    have hx' : x ∈ LinearMap.range ι₁ := hx
    obtain ⟨u, rfl⟩ := LinearMap.mem_range.mp hx'
    rw [Submodule.mem_comap]
    exact LinearMap.mem_range.mpr ⟨b u, (hz' u).symm⟩
  let zbar : Z₁ ⧸ p₁ →ₗ[ℤ] Z₂ ⧸ p₂ := Submodule.mapQ p₁ p₂ z hle
  have hzbar_apply : ∀ x : Z₁, zbar (p₁.mkQ x) = p₂.mkQ (z x) := by
    intro x
    simp only [zbar, Submodule.mkQ_apply]
    exact Submodule.mapQ_apply p₁ p₂ z (h := hle) x
  have hzbar_comp : zbar.comp p₁.mkQ = p₂.mkQ.comp z := by
    ext x
    rw [LinearMap.comp_apply, LinearMap.comp_apply]
    exact hzbar_apply x
  have hbij : Function.Bijective zbar := by
    refine (bijective_mapQ_iff p₁ p₂ z hle).mpr ⟨?_, ?_⟩
    · intro x y hxy
      have hsub : z (x - y) ∈ LinearMap.range ι₂ := by
        have h : z x - z y ∈ p₂ := hxy
        rwa [← map_sub] at h
      have hmem : x - y ∈ LinearMap.range ι₁ := h1 (x - y) hsub
      exact hmem
    · intro w
      obtain ⟨w', v, hwv⟩ := h2 w
      refine ⟨w', ?_⟩
      refine LinearMap.mem_range.mpr ⟨-v, ?_⟩
      have hw : w = z w' + ι₂ v := hwv.symm
      rw [map_neg, hw, sub_eq_add_neg, neg_add, ← add_assoc, add_neg_cancel, zero_add]
  -- ### Step 2: right exactness of the extension of scalars
  have hker₁ : LinearMap.ker (intRKerBcMap S p₁.mkQ) = LinearMap.range (intRKerBcMap S ι₁) :=
    intR_map_ker_eq_range S p₁.mkQ (Submodule.mkQ_surjective p₁) ι₁
      (by rw [Submodule.ker_mkQ])
  have hker₂ : LinearMap.ker (intRKerBcMap S p₂.mkQ) = LinearMap.range (intRKerBcMap S ι₂) :=
    intR_map_ker_eq_range S p₂.mkQ (Submodule.mkQ_surjective p₂) ι₂
      (by rw [Submodule.ker_mkQ])
  have hcomm : (intRKerBcMap S zbar).comp (intRKerBcMap S p₁.mkQ)
      = (intRKerBcMap S p₂.mkQ).comp (intRKerBcMap S z) := by
    rw [← intRKerBcMap_comp (p₁.mkQ) zbar, ← intRKerBcMap_comp z (p₂.mkQ), hzbar_comp]
  -- ### Step 3: the two properties
  have hinj : Function.Injective (intRKerBcMap S zbar) :=
    intRPres_bcMap_injective_of_bijective S zbar hbij
  have hsurj₁ : Function.Surjective (intRKerBcMap S p₁.mkQ) :=
    intRKerBcMap_surjective p₁.mkQ (Submodule.mkQ_surjective p₁)
  have hsurjZ : Function.Surjective (intRKerBcMap S zbar) :=
    intRKerBcMap_surjective zbar hbij.2
  refine ⟨?_, ?_⟩
  · intro x hx
    have h₁ : intRKerBcMap S p₂.mkQ (intRKerBcMap S z x) = 0 := by
      rw [← LinearMap.mem_ker, hker₂]
      exact hx
    have h₂ : intRKerBcMap S zbar (intRKerBcMap S p₁.mkQ x)
        = intRKerBcMap S p₂.mkQ (intRKerBcMap S z x) := by
      have h := congrArg (fun g => g x) hcomm
      simpa only [LinearMap.comp_apply] using h
    have h₃ : intRKerBcMap S zbar (intRKerBcMap S p₁.mkQ x) = 0 := h₂.trans h₁
    have h₄ : intRKerBcMap S p₁.mkQ x = 0 := hinj (by rw [h₃, map_zero])
    rw [← hker₁, LinearMap.mem_ker]
    exact h₄
  · intro y
    obtain ⟨u, hu⟩ := hsurjZ (intRKerBcMap S p₂.mkQ y)
    obtain ⟨x, hx⟩ := hsurj₁ u
    refine ⟨x, ?_⟩
    have hpt : intRKerBcMap S zbar (intRKerBcMap S p₁.mkQ x)
        = intRKerBcMap S p₂.mkQ (intRKerBcMap S z x) := by
      have h := congrArg (fun g => g x) hcomm
      simpa only [LinearMap.comp_apply] using h
    rw [← hker₂, LinearMap.mem_ker, map_sub, ← hpt, hx, hu, sub_self]

end

end Work.Pi6.SRANGE
