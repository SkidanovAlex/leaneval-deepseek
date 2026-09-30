import Mathlib
import Submission.Work.Pi6.SRANGE.Defs
import Submission.Work.Pi6.SRANGE.intR_map_ker_eq_range
import Submission.Work.Pi6.SRANGE.intR_presentation_bijective
import Submission.Work.Pi6.SRANGE.bijective_mapQ_iff
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

/-!
# Surjectivity of a presentation after extension of scalars

Let `ι₁ : B₁ → Z₁`, `ι₂ : B₂ → Z₂` be `ℤ`-linear maps, `b : B₁ → B₂`, `z : Z₁ → Z₂` with
`z ∘ ι₁ = ι₂ ∘ b`, and assume that `z` is surjective modulo `ι₂`:

`h2 : ∀ w, ∃ w', ∃ v, z w' + ι₂ v = w`,  i.e.  `range z + range ι₂ = ⊤`.

Then for every commutative ring `S` the base change of `z` is surjective modulo the base change
of `ι₂`: every `y : S ⊗ Z₂` is congruent modulo `range (ι₂ ⊗ S)` to some `(z ⊗ S) x`.

Note that, unlike `Work.Pi6.SRANGE.intR_presentation_bijective`, no injectivity hypothesis is
needed: only the surjectivity half of that statement is used, and it only requires `h2`.  The
proof is that of the corresponding second conjunct there: with `pᵢ = range ιᵢ`, the induced map
`zbar : Z₁ ⧸ p₁ → Z₂ ⧸ p₂` is surjective by `h2`, hence so is `zbar ⊗ S`; one lifts `y` through
`(Z₁ ⧸ p₁) ⊗ S → (Z₂ ⧸ p₂) ⊗ S → Z₂ ⊗ S` and concludes with right exactness of `- ⊗ S`.
-/

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

namespace Work.Pi6.SQ

-- Make the module structures on submodules and quotients the ones induced from the ambient
-- module, so that the various `Submodule` constructions are `defeq`-compatible.
attribute [local instance 5000] Submodule.module
attribute [local instance 5000] Submodule.Quotient.module

theorem intRPresentationSurjective (S : Type) [CommRing S]
    {B₁ Z₁ B₂ Z₂ : Type}
    [AddCommGroup B₁] [Module ℤ B₁] [AddCommGroup Z₁] [Module ℤ Z₁]
    [AddCommGroup B₂] [Module ℤ B₂] [AddCommGroup Z₂] [Module ℤ Z₂]
    (ι₁ : B₁ →ₗ[ℤ] Z₁) (ι₂ : B₂ →ₗ[ℤ] Z₂)
    (b : B₁ →ₗ[ℤ] B₂) (z : Z₁ →ₗ[ℤ] Z₂) (hz : z.comp ι₁ = ι₂.comp b)
    (h2 : ∀ w : Z₂, ∃ w' : Z₁, ∃ v : B₂, z w' + ι₂ v = w) :
    ∀ y : ↥((Work.Pi6.SRANGE.IntR S).obj (ModuleCat.of ℤ Z₂)),
      ∃ x : ↥((Work.Pi6.SRANGE.IntR S).obj (ModuleCat.of ℤ Z₁)),
        (ModuleCat.Hom.hom ((Work.Pi6.SRANGE.IntR S).map (ModuleCat.ofHom z))) x - y
          ∈ LinearMap.range
              (ModuleCat.Hom.hom ((Work.Pi6.SRANGE.IntR S).map (ModuleCat.ofHom ι₂))) := by
  change ∀ y : ↥((Work.Pi6.SRANGE.IntR S).obj (ModuleCat.of ℤ Z₂)),
      ∃ x : ↥((Work.Pi6.SRANGE.IntR S).obj (ModuleCat.of ℤ Z₁)),
        Work.Pi6.SRANGE.intRKerBcMap S z x - y
          ∈ LinearMap.range (Work.Pi6.SRANGE.intRKerBcMap S ι₂)
  intro y
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
  -- `zbar` is surjective: this is exactly the hypothesis `h2` modulo the ranges of `ιᵢ`.
  have hsurj_zbar : Function.Surjective zbar := by
    intro c
    obtain ⟨w, rfl⟩ := Submodule.Quotient.mk_surjective p₂ c
    obtain ⟨w', v, hv⟩ := h2 w
    refine ⟨Submodule.Quotient.mk w', ?_⟩
    have hzw' : zbar (Submodule.Quotient.mk w') = Submodule.Quotient.mk (z w') := by
      rw [← Submodule.mkQ_apply p₁ w', hzbar_apply w', Submodule.mkQ_apply p₂ (z w')]
    rw [hzw', Submodule.Quotient.eq]
    have : z w' - w = -(ι₂ v) := by rw [← hv]; abel
    rw [this]
    exact p₂.neg_mem (LinearMap.mem_range.mpr ⟨v, rfl⟩)
  -- Right exactness of `- ⊗ S` on the two quotients.
  have hker₂ : LinearMap.ker (Work.Pi6.SRANGE.intRKerBcMap S p₂.mkQ)
      = LinearMap.range (Work.Pi6.SRANGE.intRKerBcMap S ι₂) :=
    Work.Pi6.SRANGE.intR_map_ker_eq_range S p₂.mkQ (Submodule.mkQ_surjective p₂) ι₂
      (by rw [Submodule.ker_mkQ])
  have hcomm : (Work.Pi6.SRANGE.intRKerBcMap S zbar).comp
        (Work.Pi6.SRANGE.intRKerBcMap S p₁.mkQ)
      = (Work.Pi6.SRANGE.intRKerBcMap S p₂.mkQ).comp
        (Work.Pi6.SRANGE.intRKerBcMap S z) := by
    have hzbar_comp : zbar.comp p₁.mkQ = p₂.mkQ.comp z := by
      ext x
      rw [LinearMap.comp_apply, LinearMap.comp_apply]
      exact hzbar_apply x
    rw [← Work.Pi6.SRANGE.intRKerBcMap_comp (p₁.mkQ) zbar,
        ← Work.Pi6.SRANGE.intRKerBcMap_comp z (p₂.mkQ), hzbar_comp]
  have hsurj₁ : Function.Surjective (Work.Pi6.SRANGE.intRKerBcMap S p₁.mkQ) :=
    Work.Pi6.SRANGE.intRKerBcMap_surjective p₁.mkQ (Submodule.mkQ_surjective p₁)
  have hsurjZ : Function.Surjective (Work.Pi6.SRANGE.intRKerBcMap S zbar) :=
    Work.Pi6.SRANGE.intRKerBcMap_surjective zbar hsurj_zbar
  obtain ⟨u, hu⟩ := hsurjZ (Work.Pi6.SRANGE.intRKerBcMap S p₂.mkQ y)
  obtain ⟨x, hx⟩ := hsurj₁ u
  refine ⟨x, ?_⟩
  have hpt : Work.Pi6.SRANGE.intRKerBcMap S zbar (Work.Pi6.SRANGE.intRKerBcMap S p₁.mkQ x)
      = Work.Pi6.SRANGE.intRKerBcMap S p₂.mkQ (Work.Pi6.SRANGE.intRKerBcMap S z x) := by
    have h := congrArg (fun g => g x) hcomm
    simpa only [LinearMap.comp_apply] using h
  rw [← hker₂, LinearMap.mem_ker, map_sub, ← hpt, hx, hu, sub_self]

end Work.Pi6.SQ
