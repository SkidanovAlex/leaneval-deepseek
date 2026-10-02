import Mathlib
import Submission.Work.Serre.coprodChainAux

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Kernels commute with coproducts in `ModuleCat ℚ`

For a family of morphisms `f i : A i ⟶ B i` of `ℚ`-modules, the canonical comparison map
`∐ i, kernel (f i) ⟶ kernel (∐ i, f i)` (`Work.Serre.sigmaKernelMap`) is an isomorphism.
`ModuleCat ℚ` satisfies AB4 (coproducts are exact), but here we give the elementary proof:
transport along `ModuleCat.coprodIsoDirectSum` and use `DirectSum.ker_lmap`.

The main technical input is `csr_sigmaMap_coprodIsoDirectSum_apply`, the elementwise naturality of
`ModuleCat.coprodIsoDirectSum` with respect to `Limits.Sigma.map`.
-/

namespace Work.Serre

open CategoryTheory Limits
open CategoryTheory.Limits ModuleCat

noncomputable section

/-- Elementwise naturality of `ModuleCat.coprodIsoDirectSum` with respect to `Limits.Sigma.map`. -/
lemma csr_sigmaMap_coprodIsoDirectSum_apply {ι : Type} [DecidableEq ι] {X Y : ι → ModuleCat ℚ}
    (u : ∀ i, X i ⟶ Y i) (z : DirectSum ι (fun i => ↑(X i))) :
    (ModuleCat.coprodIsoDirectSum Y).hom
        (Limits.Sigma.map u ((ModuleCat.coprodIsoDirectSum X).inv z))
      = DirectSum.lmap (fun i => (u i).hom) z := by
  classical
  have key_of : ∀ (i : ι) (x : ↑(X i)),
      (ModuleCat.coprodIsoDirectSum Y).hom
          (Limits.Sigma.map u ((ModuleCat.coprodIsoDirectSum X).inv
            (DirectSum.lof ℚ ι (fun i => ↑(X i)) i x)))
        = DirectSum.lmap (fun i => (u i).hom) (DirectSum.lof ℚ ι (fun i => ↑(X i)) i x) := by
    intro i x
    rw [ModuleCat.lof_coprodIsoDirectSum_inv_apply]
    rw [← ConcreteCategory.comp_apply (Limits.Sigma.ι X i) (Limits.Sigma.map u)]
    rw [Limits.Sigma.ι_map]
    rw [ConcreteCategory.comp_apply]
    rw [ModuleCat.ι_coprodIsoDirectSum_hom_apply]
    rw [DirectSum.lmap_lof]
  have key_of' : ∀ (i : ι) (x : ↑(X i)),
      (ModuleCat.coprodIsoDirectSum Y).hom
          (Limits.Sigma.map u ((ModuleCat.coprodIsoDirectSum X).inv
            (DirectSum.of (fun i => ↑(X i)) i x)))
        = DirectSum.lmap (fun i => (u i).hom) (DirectSum.of (fun i => ↑(X i)) i x) :=
    fun i x => key_of i x
  conv_rhs => rw [← DirectSum.sum_support_of z]
  conv_lhs => rw [← DirectSum.sum_support_of z]
  simp only [map_sum, key_of']

/-- Morphism form of the naturality of `ModuleCat.coprodIsoDirectSum`: under the identification of
a coproduct of modules with a direct sum, `Limits.Sigma.map` is `DirectSum.lmap`. -/
lemma csr_coprodIsoDirectSum_sigmaMap {ι : Type} [DecidableEq ι] {M N : ι → ModuleCat ℚ}
    (f : ∀ i, M i ⟶ N i) :
    (ModuleCat.coprodIsoDirectSum M).inv ≫ Limits.Sigma.map f ≫ (ModuleCat.coprodIsoDirectSum N).hom
      = ModuleCat.ofHom (DirectSum.lmap (fun i => (f i).hom)) := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  exact csr_sigmaMap_coprodIsoDirectSum_apply f z

/-- The range of the categorical kernel inclusion of `f` is the kernel of `f`. -/
lemma csr_range_kernel_ι {M N : ModuleCat ℚ} (f : M ⟶ N) :
    LinearMap.range ((kernel.ι f).hom) = LinearMap.ker f.hom := by
  refine le_antisymm ?_ ?_
  · rintro _ ⟨x, rfl⟩
    exact LinearMap.mem_ker.mpr (by
      show f.hom ((kernel.ι f).hom x) = 0
      rw [← ModuleCat.comp_apply (kernel.ι f) f x, kernel.condition]
      rfl)
  · intro y hy
    refine ⟨(ModuleCat.kernelIsoKer f).inv ⟨y, hy⟩, ?_⟩
    rw [← ConcreteCategory.comp_apply (ModuleCat.kernelIsoKer f).inv (kernel.ι f),
      ModuleCat.kernelIsoKer_inv_kernel_ι]
    rfl

/-- Componentwise description of the vanishing of `DirectSum.lmap`. -/
lemma csr_lmap_eq_zero_iff {ι : Type} {M N : ι → ModuleCat ℚ} (f : ∀ i, M i ⟶ N i)
    (z : DirectSum ι (fun i => ↑(M i))) :
    DirectSum.lmap (fun i => (f i).hom) z = 0 ↔ ∀ i, (f i).hom (z i) = 0 := by
  constructor
  · intro h i
    have := congrArg (fun w => w i) h
    simpa [DirectSum.lmap_apply] using this
  · intro h
    ext i
    simpa [DirectSum.lmap_apply] using h i

/-- Every element killed by `DirectSum.lmap f` is in the range of `DirectSum.lmap k`, provided
`k i` has range equal to the kernel of `f i`. -/
lemma csr_exists_lmap_eq_of_lmap_eq_zero {ι : Type} [DecidableEq ι] {K A B : ι → ModuleCat ℚ}
    (k : ∀ i, K i ⟶ A i) (f : ∀ i, A i ⟶ B i)
    (h : ∀ i, LinearMap.range ((k i).hom) = LinearMap.ker ((f i).hom))
    (z : DirectSum ι (fun i => ↑(A i)))
    (hz : DirectSum.lmap (fun i => (f i).hom) z = 0) :
    ∃ z' : DirectSum ι (fun i => ↑(K i)), DirectSum.lmap (fun i => (k i).hom) z' = z := by
  classical
  have hzi : ∀ i, (f i).hom (z i) = 0 := (csr_lmap_eq_zero_iff f z).mp hz
  have hzr : ∀ i, z i ∈ LinearMap.range ((k i).hom) := fun i => by
    rw [h i]
    exact LinearMap.mem_ker.mpr (hzi i)
  choose χ hχ using fun i => LinearMap.mem_range.mp (hzr i)
  refine ⟨DirectSum.mk (fun i => ↑(K i)) z.support (fun i => χ i.val), ?_⟩
  ext j
  by_cases hj : j ∈ z.support
  · rw [DirectSum.lmap_apply, DirectSum.mk_apply_of_mem (β := fun i => ↑(K i)) hj, hχ j]
  · rw [DirectSum.lmap_apply, DirectSum.mk_apply_of_notMem (β := fun i => ↑(K i)) hj, map_zero,
      DFinsupp.notMem_support_iff.mp hj]

/-- `DirectSum.lmap` is injective whenever all components are. -/
lemma csr_lmap_injective_of_injective {ι : Type} {M N : ι → ModuleCat ℚ} (f : ∀ i, M i ⟶ N i)
    (hf : ∀ i, Function.Injective (f i).hom) :
    Function.Injective (DirectSum.lmap (fun i => (f i).hom)) := by
  intro a b hab
  ext i
  have h := congrArg (fun w => w i) hab
  simp only [DirectSum.lmap_apply] at h
  exact hf i h

/-- An isomorphism of `ℚ`-modules is injective on the nose: `e.inv (e.hom x) = x`. -/
lemma csr_iso_inv_hom_apply {X Y : ModuleCat ℚ} (e : X ≅ Y) (x : ↑X) : e.inv (e.hom x) = x := by
  have h := ConcreteCategory.congr_hom (Iso.hom_inv_id e) x
  rw [ModuleCat.comp_apply, ModuleCat.id_apply] at h
  exact h

/-- **Kernels commute with coproducts in `ModuleCat ℚ`**: the canonical comparison map
`∐ i, kernel (f i) ⟶ kernel (∐ i, f i)` is an isomorphism. -/
theorem isIso_sigmaKernelMap {ι : Type} {A B : ι → ModuleCat ℚ} (f : ∀ i, A i ⟶ B i) :
    IsIso (sigmaKernelMap f) := by
  classical
  let K : ι → ModuleCat ℚ := fun i => kernel (f i)
  let k : ∀ i, K i ⟶ A i := fun i => kernel.ι (f i)
  have hφ : sigmaKernelMap f ≫ kernel.ι (Limits.Sigma.map f) = Limits.Sigma.map k :=
    sigmaKernelMap_comp_ι f
  have hEl : ∀ y : ↑(∐ K), (kernel.ι (Limits.Sigma.map f)) (sigmaKernelMap f y)
      = Limits.Sigma.map k y := by
    intro y
    rw [← ConcreteCategory.comp_apply, hφ]
  have hbij : Function.Bijective ⇑(ConcreteCategory.hom (sigmaKernelMap f)) := by
    refine ⟨?_, ?_⟩
    · intro a b hab
      have hc : Limits.Sigma.map k a = Limits.Sigma.map k b := by
        rw [← hEl a, ← hEl b, hab]
      have hinj_lmap : Function.Injective (DirectSum.lmap (fun i => (k i).hom)) :=
        csr_lmap_injective_of_injective k
          (fun i => (ModuleCat.mono_iff_injective (kernel.ι (f i))).mp inferInstance)
      have ha : DirectSum.lmap (fun i => (k i).hom) ((ModuleCat.coprodIsoDirectSum K).hom a)
          = (ModuleCat.coprodIsoDirectSum A).hom (Limits.Sigma.map k a) := by
        have hkey := csr_sigmaMap_coprodIsoDirectSum_apply (X := K) (Y := A) k
          ((ModuleCat.coprodIsoDirectSum K).hom a)
        rw [csr_iso_inv_hom_apply] at hkey
        exact hkey.symm
      have hb : DirectSum.lmap (fun i => (k i).hom) ((ModuleCat.coprodIsoDirectSum K).hom b)
          = (ModuleCat.coprodIsoDirectSum A).hom (Limits.Sigma.map k b) := by
        have hkey := csr_sigmaMap_coprodIsoDirectSum_apply (X := K) (Y := A) k
          ((ModuleCat.coprodIsoDirectSum K).hom b)
        rw [csr_iso_inv_hom_apply] at hkey
        exact hkey.symm
      have h2 : (ModuleCat.coprodIsoDirectSum K).hom a = (ModuleCat.coprodIsoDirectSum K).hom b := by
        apply hinj_lmap
        rw [ha, hb, hc]
      exact (ConcreteCategory.bijective_of_isIso (ModuleCat.coprodIsoDirectSum K).hom).1 h2
    · intro y
      set y₀ := (ModuleCat.kernelIsoKer (Limits.Sigma.map f)).hom y with hy₀
      have hy0 : (Limits.Sigma.map f).hom y₀.val = 0 :=
        LinearMap.mem_ker.mp y₀.property
      have hw : DirectSum.lmap (fun i => (f i).hom)
          ((ModuleCat.coprodIsoDirectSum A).hom y₀.val) = 0 := by
        have hkey := csr_sigmaMap_coprodIsoDirectSum_apply (X := A) (Y := B) f
          ((ModuleCat.coprodIsoDirectSum A).hom y₀.val)
        rw [csr_iso_inv_hom_apply] at hkey
        rw [← hkey, hy0]
        simp
      obtain ⟨z, hz⟩ := csr_exists_lmap_eq_of_lmap_eq_zero k f (fun i => csr_range_kernel_ι (f i))
        ((ModuleCat.coprodIsoDirectSum A).hom y₀.val) hw
      refine ⟨(ModuleCat.coprodIsoDirectSum K).inv z, ?_⟩
      have hxa : Limits.Sigma.map k ((ModuleCat.coprodIsoDirectSum K).inv z) = y₀.val := by
        apply (ConcreteCategory.bijective_of_isIso (ModuleCat.coprodIsoDirectSum A).hom).1
        have hkey := csr_sigmaMap_coprodIsoDirectSum_apply (X := K) (Y := A) k z
        rw [hkey, hz]
      have hfinj : Function.Injective
          ⇑(ConcreteCategory.hom (ModuleCat.kernelIsoKer (Limits.Sigma.map f)).hom) :=
        (ConcreteCategory.bijective_of_isIso _).1
      apply hfinj
      rw [← hy₀]
      apply Subtype.ext
      rw [ModuleCat.kernelIsoKer_hom_ker_subtype_apply, hEl, hxa]
  exact (ConcreteCategory.isIso_iff_bijective (sigmaKernelMap f)).mpr hbij

end

end Work.Serre
