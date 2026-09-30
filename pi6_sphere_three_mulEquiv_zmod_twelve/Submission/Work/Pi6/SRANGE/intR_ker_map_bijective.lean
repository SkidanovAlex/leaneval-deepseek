import Mathlib
import Submission.Work.Pi6.SRANGE.Defs
import Submission.Work.Pi6.SRANGE.ker_rTensor_incl_bijective
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

/-!
# The kernel of `ι ⊗ S` in the `extendScalars` language

`Work.Pi6.SRANGE.ker_rTensor_incl_bijective` computes, for two inclusions `ι₁ : B₁ ↪ Z₁`,
`ι₂ : B₂ ↪ Z₂` of torsion free `ℤ`-modules inducing the same quotient and a compatible map
`b : B₁ → B₂`, the map `b ⊗ S` on the kernels of `ι₁ ⊗ S` and `ι₂ ⊗ S`, in the
`TensorProduct ℤ B S` (`rTensor`) orientation.

The present file restates that result in the orientation in which
`ModuleCat.extendScalars (Int.castRingHom S)` produces it:  the object
`(Work.Pi6.SRANGE.IntR S).obj (ModuleCat.of ℤ B)` is `S ⊗[ℤ] B` and the map
`(IntR S).map (ModuleCat.ofHom f)` is `f.lTensor S`, up to definitional unfolding
(`ModuleCat.ExtendScalars.map_tmul`).  `intR_map_eq_lTensor` records that identification, and
`lTensor_ker_incl_bijective` is the resulting `lTensor` form of the kernel computation; the
target `intR_ker_map_bijective` follows by rewriting along the identification.
-/

set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

namespace Work.Pi6.SRANGE

/-- The `extendScalars` map on `S ⊗[ℤ] B` is the `lTensor` map, elementwise.

Note the explicit `Module ℤ S` structure: `(IntR S).obj (ModuleCat.of ℤ B)` is the tensor product
with `S` carrying the structure induced by `Module.compHom`, which is *not* syntactically the
canonical `Module ℤ S` structure of a ring; the two are definitionally equal, so the statement
below is the honest identification. -/
theorem intR_map_eq_lTensor (S : Type) [CommRing S]
    {M N : Type} [AddCommGroup M] [Module ℤ M] [AddCommGroup N] [Module ℤ N]
    (f : M →ₗ[ℤ] N) :
    letI : Module ℤ S := Module.compHom S (Int.castRingHom S)
    ∀ x : (IntR S).obj (ModuleCat.of ℤ M),
      ModuleCat.Hom.hom ((IntR S).map (ModuleCat.ofHom f)) x = f.lTensor S x := by
  letI : Module ℤ S := Module.compHom S (Int.castRingHom S)
  intro x
  have h : (⇑(ModuleCat.Hom.hom ((IntR S).map (ModuleCat.ofHom f)))) = (⇑(f.lTensor S)) := rfl
  exact congrFun h x

/-- **`lTensor` form of `ker_rTensor_incl_bijective`.**  Same statement as
`Work.Pi6.SRANGE.ker_rTensor_incl_bijective` with the tensor factors in the order produced by
`ModuleCat.extendScalars`. -/
theorem lTensor_ker_incl_bijective (S : Type) [CommRing S]
    {B₁ Z₁ B₂ Z₂ : Type}
    [AddCommGroup B₁] [Module ℤ B₁] [AddCommGroup Z₁] [Module ℤ Z₁]
    [AddCommGroup B₂] [Module ℤ B₂] [AddCommGroup Z₂] [Module ℤ Z₂]
    (ι₁ : B₁ →ₗ[ℤ] Z₁) (hι₁ : Function.Injective ι₁) (hZ₁ : Module.IsTorsionFree ℤ Z₁)
    (ι₂ : B₂ →ₗ[ℤ] Z₂) (hι₂ : Function.Injective ι₂) (hZ₂ : Module.IsTorsionFree ℤ Z₂)
    (b : B₁ →ₗ[ℤ] B₂) (z : Z₁ →ₗ[ℤ] Z₂) (hz : z.comp ι₁ = ι₂.comp b)
    (h1 : ∀ x : Z₁, z x ∈ LinearMap.range ι₂ → x ∈ LinearMap.range ι₁)
    (h2 : ∀ w : Z₂, ∃ w' : Z₁, ∃ v : B₂, z w' + ι₂ v = w) :
    letI : Module ℤ S := Module.compHom S (Int.castRingHom S)
    (∀ x₁ x₂ : TensorProduct ℤ S B₁, ι₁.lTensor S x₁ = 0 → ι₁.lTensor S x₂ = 0 →
        b.lTensor S x₁ = b.lTensor S x₂ → x₁ = x₂)
    ∧ (∀ y : TensorProduct ℤ S B₂, ι₂.lTensor S y = 0 →
        ∃ x : TensorProduct ℤ S B₁, ι₁.lTensor S x = 0 ∧ b.lTensor S x = y) := by
  letI : Module ℤ S := Module.compHom S (Int.castRingHom S)
  -- Fix the canonical `ℤ`-module structure on the product (two competing instances exist).
  letI : Module ℤ (Z₁ × B₂) := Prod.instModule
  -- The total maps whose exactness encodes the hypotheses.
  let φ : B₁ →ₗ[ℤ] Z₁ × B₂ := LinearMap.prod ι₁ b
  let ψ : Z₁ × B₂ →ₗ[ℤ] Z₂ :=
    (z.comp (LinearMap.fst ℤ Z₁ B₂)) - (ι₂.comp (LinearMap.snd ℤ Z₁ B₂))
  have hz' : ∀ u : B₁, z (ι₁ u) = ι₂ (b u) := fun u => by
    have h := congrArg (fun f : B₁ →ₗ[ℤ] Z₂ => f u) hz
    simpa [LinearMap.comp_apply] using h
  have hψφ : ψ.comp φ = 0 := by
    ext u
    simp [ψ, φ, LinearMap.prod_apply, LinearMap.comp_apply, hz' u]
  have hsurjψ : Function.Surjective ψ := by
    intro y
    obtain ⟨w', v, hv⟩ := h2 y
    exact ⟨(w', -v), by simp [ψ, LinearMap.comp_apply, LinearMap.sub_apply, hv]⟩
  have hkerψ : LinearMap.ker ψ ≤ LinearMap.range φ := by
    intro x hx
    obtain ⟨w, v⟩ := x
    have hx' : z w = ι₂ v := by
      have : z w - ι₂ v = 0 := hx
      exact sub_eq_zero.mp this
    obtain ⟨u, hu⟩ := LinearMap.mem_range.mp (h1 w (LinearMap.mem_range.mpr ⟨v, hx'.symm⟩))
    refine LinearMap.mem_range.mpr ⟨u, ?_⟩
    have hbu : b u = v := hι₂ (by rw [← hz' u, hu, hx'])
    simp [φ, LinearMap.prod_apply, hu, hbu]
  have hrangeφ : LinearMap.range φ ≤ LinearMap.ker ψ := by
    intro x hx
    obtain ⟨u, rfl⟩ := LinearMap.mem_range.mp hx
    exact congrArg (fun f : B₁ →ₗ[ℤ] Z₂ => f u) hψφ
  have hinjφ : Function.Injective φ := by
    intro u v huv
    apply hι₁
    have := congrArg (fun x => x.1) huv
    simpa [φ, LinearMap.prod_apply] using this
  have hExact : Function.Exact φ ψ := LinearMap.exact_iff.mpr (le_antisymm hkerψ hrangeφ)
  -- `Z₂` is torsion free, hence flat over the PID `ℤ`.
  haveI : Module.IsTorsionFree ℤ Z₂ := hZ₂
  haveI : Module.Flat ℤ Z₂ := inferInstance
  -- Injectivity half: `φ ⊗ S` is injective.
  have hφl : Function.Injective (φ.lTensor S) :=
    LinearMap.lTensor_injective_of_exact_of_flat ψ hsurjψ φ hinjφ hExact S
  -- Surjectivity half: right exactness of `S ⊗ -` on the exact sequence for `φ`, `ψ`.
  have hex : Function.Exact (φ.lTensor S) (ψ.lTensor S) := lTensor_exact S hExact hsurjψ
  -- `S ⊗ (Z₁ × B₂)` is detected by its two components.
  have hdec : ∀ t : TensorProduct ℤ S (Z₁ × B₂),
      (TensorProduct.map (LinearMap.id : S →ₗ[ℤ] S) (LinearMap.inl ℤ Z₁ B₂))
          ((LinearMap.fst ℤ Z₁ B₂).lTensor S t)
      + (TensorProduct.map (LinearMap.id : S →ₗ[ℤ] S) (LinearMap.inr ℤ Z₁ B₂))
          ((LinearMap.snd ℤ Z₁ B₂).lTensor S t) = t := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul v w =>
      obtain ⟨w₁, w₂⟩ := w
      simp only [LinearMap.lTensor_tmul, LinearMap.fst_apply, LinearMap.snd_apply,
        TensorProduct.map_tmul, LinearMap.inl_apply, LinearMap.inr_apply, LinearMap.id_apply]
      rw [← TensorProduct.tmul_add]
      simp
    | add p q hp hq =>
      simp only [map_add]
      conv_rhs => rw [← hp, ← hq]
      abel
  have hzero_of : ∀ t : TensorProduct ℤ S (Z₁ × B₂),
      (LinearMap.fst ℤ Z₁ B₂).lTensor S t = 0 →
      (LinearMap.snd ℤ Z₁ B₂).lTensor S t = 0 → t = 0 := by
    intro t h₁ h₂
    have h := hdec t
    rw [h₁, h₂] at h
    simpa using h.symm
  -- Bookkeeping identities relating `φ`, `ψ` to the components.
  have hfst_comp : (LinearMap.fst ℤ Z₁ B₂).comp φ = ι₁ := by ext u; rfl
  have hsnd_comp : (LinearMap.snd ℤ Z₁ B₂).comp φ = b := by ext u; rfl
  have hinr_fst : (LinearMap.fst ℤ Z₁ B₂).comp (LinearMap.inr ℤ Z₁ B₂) = 0 := by ext v; rfl
  have hinr_snd : (LinearMap.snd ℤ Z₁ B₂).comp (LinearMap.inr ℤ Z₁ B₂) = LinearMap.id := by
    ext v; rfl
  have hcompψ : ψ.comp (LinearMap.inr ℤ Z₁ B₂) = -ι₂ := by
    ext v
    simp [ψ, LinearMap.comp_apply, LinearMap.inr_apply, LinearMap.sub_apply]
  constructor
  · -- Injectivity of `b ⊗ S` on `ker (ι₁ ⊗ S)`.
    intro x₁ x₂ hi1 hi2 hb'
    have h₁ : (LinearMap.fst ℤ Z₁ B₂).lTensor S (φ.lTensor S (x₁ - x₂)) = 0 := by
      rw [← LinearMap.comp_apply, ← LinearMap.lTensor_comp, hfst_comp]
      simp [map_sub, hi1, hi2]
    have h₂ : (LinearMap.snd ℤ Z₁ B₂).lTensor S (φ.lTensor S (x₁ - x₂)) = 0 := by
      rw [← LinearMap.comp_apply, ← LinearMap.lTensor_comp, hsnd_comp]
      simp [map_sub, hb']
    have hz0 : φ.lTensor S (x₁ - x₂) = 0 := hzero_of _ h₁ h₂
    have : x₁ - x₂ = 0 := hφl (by rw [hz0, map_zero])
    exact sub_eq_zero.mp this
  · -- Surjectivity of `b ⊗ S` onto `ker (ι₂ ⊗ S)`.
    intro y hy
    have hψw : (ψ.lTensor S) ((LinearMap.inr ℤ Z₁ B₂).lTensor S y) = 0 := by
      rw [← LinearMap.lTensor_comp_apply, hcompψ, LinearMap.lTensor_neg]
      simp [hy]
    have hw : (LinearMap.inr ℤ Z₁ B₂).lTensor S y ∈ Set.range (φ.lTensor S) :=
      (hex _).mp hψw
    obtain ⟨x, hx⟩ := hw
    refine ⟨x, ?_, ?_⟩
    · have h₁ : (LinearMap.fst ℤ Z₁ B₂).lTensor S (φ.lTensor S x) = 0 := by
        rw [hx, ← LinearMap.lTensor_comp_apply, hinr_fst]
        simp
      rwa [← LinearMap.comp_apply, ← LinearMap.lTensor_comp, hfst_comp] at h₁
    · have h₂ : (LinearMap.snd ℤ Z₁ B₂).lTensor S (φ.lTensor S x) = y := by
        rw [hx, ← LinearMap.lTensor_comp_apply, hinr_snd]
        simp
      rwa [← LinearMap.comp_apply, ← LinearMap.lTensor_comp, hsnd_comp] at h₂

theorem intR_ker_map_bijective (S : Type) [CommRing S]
    {B₁ Z₁ B₂ Z₂ : Type}
    [AddCommGroup B₁] [Module ℤ B₁] [AddCommGroup Z₁] [Module ℤ Z₁]
    [AddCommGroup B₂] [Module ℤ B₂] [AddCommGroup Z₂] [Module ℤ Z₂]
    (ι₁ : B₁ →ₗ[ℤ] Z₁) (hι₁ : Function.Injective ι₁) (hZ₁ : Module.IsTorsionFree ℤ Z₁)
    (ι₂ : B₂ →ₗ[ℤ] Z₂) (hι₂ : Function.Injective ι₂) (hZ₂ : Module.IsTorsionFree ℤ Z₂)
    (b : B₁ →ₗ[ℤ] B₂) (z : Z₁ →ₗ[ℤ] Z₂) (hz : z.comp ι₁ = ι₂.comp b)
    (h1 : ∀ x : Z₁, z x ∈ LinearMap.range ι₂ → x ∈ LinearMap.range ι₁)
    (h2 : ∀ w : Z₂, ∃ w' : Z₁, ∃ v : B₂, z w' + ι₂ v = w) :
    (∀ x₁ x₂ : ↥((Work.Pi6.SRANGE.IntR S).obj (ModuleCat.of ℤ B₁)),
        (ModuleCat.Hom.hom ((Work.Pi6.SRANGE.IntR S).map (ModuleCat.ofHom ι₁))) x₁ = 0 →
        (ModuleCat.Hom.hom ((Work.Pi6.SRANGE.IntR S).map (ModuleCat.ofHom ι₁))) x₂ = 0 →
        (ModuleCat.Hom.hom ((Work.Pi6.SRANGE.IntR S).map (ModuleCat.ofHom b))) x₁
          = (ModuleCat.Hom.hom ((Work.Pi6.SRANGE.IntR S).map (ModuleCat.ofHom b))) x₂ → x₁ = x₂)
    ∧ (∀ y : ↥((Work.Pi6.SRANGE.IntR S).obj (ModuleCat.of ℤ B₂)),
        (ModuleCat.Hom.hom ((Work.Pi6.SRANGE.IntR S).map (ModuleCat.ofHom ι₂))) y = 0 →
        ∃ x : ↥((Work.Pi6.SRANGE.IntR S).obj (ModuleCat.of ℤ B₁)),
          (ModuleCat.Hom.hom ((Work.Pi6.SRANGE.IntR S).map (ModuleCat.ofHom ι₁))) x = 0 ∧
            (ModuleCat.Hom.hom ((Work.Pi6.SRANGE.IntR S).map (ModuleCat.ofHom b))) x = y) := by
  letI : Module ℤ S := Module.compHom S (Int.castRingHom S)
  obtain ⟨key1, key2⟩ := lTensor_ker_incl_bijective S ι₁ hι₁ hZ₁ ι₂ hι₂ hZ₂ b z hz h1 h2
  constructor
  · intro x₁ x₂ hx₁ hx₂ hb
    rw [intR_map_eq_lTensor S ι₁ x₁] at hx₁
    rw [intR_map_eq_lTensor S ι₁ x₂] at hx₂
    rw [intR_map_eq_lTensor S b x₁, intR_map_eq_lTensor S b x₂] at hb
    exact key1 x₁ x₂ hx₁ hx₂ hb
  · intro y hy
    rw [intR_map_eq_lTensor S ι₂ y] at hy
    obtain ⟨x, hx1, hx2⟩ := key2 y hy
    refine ⟨x, ?_, ?_⟩
    · rw [intR_map_eq_lTensor S ι₁ x]
      exact hx1
    · rw [intR_map_eq_lTensor S b x]
      exact hx2

end Work.Pi6.SRANGE
