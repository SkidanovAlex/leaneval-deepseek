import Mathlib

/-!
# `Work.DSM2p.flat_of_ker_inf_smul_top_eq_smul`

Let `R` be a commutative ring, `M` a **flat** `R`-module, `f : M →ₗ[R] N` a surjective linear map
and `K = f.ker`. If for every ideal `I ⊆ R` the submodule `K` is *pure* in `M`, i.e.

`K ⊓ I • ⊤ = I • K`   (equivalently `K ⊓ I·M = I·K`),

then `N` is flat over `R`.

This is the standard theorem that a quotient of a flat module by a pure submodule is flat. The
purity hypothesis is exactly the vanishing of `Tor₁^R(N, R ⧸ I)`:

* tensoring `0 → K → M → N → 0` by `R ⧸ I` and using `Tor₁^R(M, R ⧸ I) = 0` (`M` flat) gives
  `Tor₁^R(N, R ⧸ I) ≅ ker(K ⧸ IK → M ⧸ IM) = (K ∩ IM)/IK`;
* the hypothesis says this is `0`, so `Tor₁^R(N, R ⧸ I) = 0` for all `I`, i.e. `N` is flat.

The formal proof avoids `Tor` altogether and works with the canonical maps

`I ⊗ M → M`, `i ⊗ m ↦ i·m`   (`lsmulLift I M`)

which are the "`Tor₁`-detecting" maps. The facts used are

* `range (lsmulLift I M) = I • ⊤` (`range_lsmulLift`);
* `lsmulLift` is natural in the module (`lsmulLift_lTensor`);
* `ker (lTensor I K.mkQ) = range (lTensor I K.subtype)` (`lTensor_mkQ`, right exactness);
* `lsmulLift I M` is injective when `M` is flat
  (`Module.Flat.iff_lift_lsmul_comp_subtype_injective`).
-/

open scoped TensorProduct

namespace Work.DSM2p

namespace FlatPurity

variable {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N]

/-- The canonical map `I ⊗[R] M → M`, `i ⊗ₜ m ↦ i • m`.

This is the map whose injectivity detects flatness of `M`
(`Module.Flat.iff_lift_lsmul_comp_subtype_injective`) and whose image is `I • ⊤`. -/
noncomputable def lsmulLift (I : Ideal R) (M : Type*) [AddCommGroup M] [Module R M] :
    I ⊗[R] M →ₗ[R] M :=
  TensorProduct.lift (LinearMap.lsmul R M ∘ₗ Submodule.subtype I)

/-- The image of `I ⊗[R] M → M`, `i ⊗ₜ m ↦ i • m`, is `I • ⊤`. -/
theorem range_lsmulLift (I : Ideal R) :
    (lsmulLift I M).range = I • (⊤ : Submodule R M) := by
  apply le_antisymm
  · rintro x ⟨z, rfl⟩
    induction z with
    | tmul i m =>
        simp only [lsmulLift, LinearMap.comp_apply, LinearMap.lsmul_apply,
          TensorProduct.lift.tmul]
        exact Submodule.smul_mem_smul i.2 Submodule.mem_top
    | add x y hx hy =>
        rw [map_add]
        exact Submodule.add_mem _ hx hy
  · rw [Submodule.smul_le]
    intro r hr m _
    exact ⟨⟨r, hr⟩ ⊗ₜ[R] m, by simp [lsmulLift, LinearMap.lsmul_apply]⟩

/-- Naturality of `lsmulLift`: for `f : M →ₗ[R] N` the square

`I ⊗ M --→ I ⊗ N`
`  ↓          ↓`
`  M   --→    N`

commutes, i.e. `lsmulLift I N ∘ (lTensor I f) = f ∘ lsmulLift I M`. -/
theorem lsmulLift_lTensor (I : Ideal R) (f : M →ₗ[R] N) :
    (lsmulLift I N).comp (LinearMap.lTensor I f) = f.comp (lsmulLift I M) := by
  apply TensorProduct.ext'
  intro i m
  simp [lsmulLift, LinearMap.lsmul_apply]

end FlatPurity

open FlatPurity

/-- **A quotient of a flat module by a pure submodule is flat.**

Let `M` be a flat `R`-module and `K ⊆ M` a submodule which is *pure*, in the sense that
`K ⊓ I • ⊤ = I • K` for every ideal `I ⊆ R`. Then `M ⧸ K` is flat over `R`.

Indeed, for a finitely generated ideal `I`, the canonical map `I ⊗ (M ⧸ K) → M ⧸ K` has kernel
`(lTensor I K.mkQ)((lsmulLift I M)⁻¹ K)`; and if `z` lies over `K`, the purity hypothesis together
with `range (lsmulLift I M) = I • ⊤` shows that `z` comes from `I ⊗ K`, hence is killed by
`lTensor I K.mkQ` (right exactness). -/
theorem flat_quot_of_pure {R : Type*} {M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [Module.Flat R M] (K : Submodule R M)
    (h : ∀ I : Ideal R, K ⊓ I • (⊤ : Submodule R M) = I • K) :
    Module.Flat R (M ⧸ K) := by
  rw [Module.Flat.iff_lift_lsmul_comp_subtype_injective]
  intro I hI
  rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
  intro x hx
  -- `x : I ⊗ (M ⧸ K)` lies in the kernel; lift it to `z : I ⊗ M` along the surjection
  -- `lTensor I K.mkQ`.
  obtain ⟨z, rfl⟩ := LinearMap.lTensor_surjective I (Submodule.mkQ_surjective K) x
  -- `lsmulLift I M` is injective because `M` is flat.
  have hinj : Function.Injective (lsmulLift I M) :=
    Module.Flat.iff_lift_lsmul_comp_subtype_injective.mp ‹Module.Flat R M› hI
  have hnatK := lsmulLift_lTensor (R := R) I K.mkQ
  have hnatS := lsmulLift_lTensor (R := R) I K.subtype
  -- `lsmulLift I M z ∈ K`
  have hz1 : lsmulLift I M z ∈ K := by
    have hx1 : lsmulLift I (M ⧸ K) (LinearMap.lTensor I K.mkQ z) = 0 := by
      rw [LinearMap.mem_ker] at hx
      exact hx
    have hx2 : K.mkQ (lsmulLift I M z) = 0 := by
      calc K.mkQ (lsmulLift I M z)
          = lsmulLift I (M ⧸ K) (LinearMap.lTensor I K.mkQ z) :=
            (LinearMap.congr_fun hnatK z).symm
        _ = 0 := hx1
    rw [← LinearMap.mem_ker, Submodule.ker_mkQ] at hx2
    exact hx2
  -- `lsmulLift I M z ∈ I • ⊤`
  have hz2 : lsmulLift I M z ∈ I • (⊤ : Submodule R M) := by
    rw [← range_lsmulLift (M := M) I]
    exact ⟨z, rfl⟩
  -- purity: it lies in `I • K`
  have hzK : lsmulLift I M z ∈ I • K := by
    rw [← h I]
    exact ⟨hz1, hz2⟩
  -- hence it lifts to `I ⊗ K`
  have hy : (⟨lsmulLift I M z, hz1⟩ : K) ∈ I • (⊤ : Submodule R K) :=
    (Submodule.mem_smul_top_iff I K ⟨lsmulLift I M z, hz1⟩).mpr hzK
  rw [← range_lsmulLift (M := K) I] at hy
  obtain ⟨w, hw⟩ := hy
  -- `z` is the image of that lift, so it is killed by `lTensor I K.mkQ`
  have hstep : lsmulLift I M (LinearMap.lTensor I K.subtype w) = lsmulLift I M z := by
    rw [← LinearMap.comp_apply, hnatS, LinearMap.comp_apply, hw]
    rfl
  have hzw : LinearMap.lTensor I K.subtype w = z := hinj hstep
  rw [← hzw, ← LinearMap.mem_ker, lTensor_mkQ I K]
  exact ⟨w, rfl⟩

set_option linter.style.haveILetI false in
/-- **Flatness descends along a surjection whose kernel is pure.**

Let `M` be a flat `R`-module, `f : M →ₗ[R] N` a surjective linear map, and suppose the kernel
`f.ker` is pure in `M`, i.e. `f.ker ⊓ I • ⊤ = I • f.ker` for every ideal `I`. Then `N` is flat.

Since `f` is surjective, `N ≃ₗ[R] M ⧸ f.ker`, and `M ⧸ f.ker` is flat by `flat_quot_of_pure`. -/
theorem flat_of_ker_inf_smul_top_eq_smul {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] [Module.Flat R M] (f : M →ₗ[R] N) (hf : Function.Surjective f) (h : ∀ I : Ideal R, f.ker ⊓ I • (⊤ : Submodule R M) = I • f.ker) : Module.Flat R N := by
  haveI : Module.Flat R (M ⧸ f.ker) := flat_quot_of_pure f.ker h
  exact Module.Flat.of_linearEquiv (f.quotKerEquivOfSurjective hf).symm

end Work.DSM2p
