import Mathlib
import Submission.NK.CFTLib.roquetteDefs

/-!
# The `p`-rank of an abelian group

For a prime `p` and an abelian group `M` we define the **`p`-rank** `pRank p M` to be the
`𝔽_p`-dimension of `𝔽_p ⊗[ℤ] M`.  This file collects the elementary general lemmas used by
`NK.CFTLib.finrank_normQuotient_le`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace NK.CFTLib

open TensorProduct

/-- The **`p`-rank** of an abelian group `M`: the `𝔽_p`-dimension of `𝔽_p ⊗[ℤ] M`. -/
noncomputable def pRank (p : ℕ) (M : Type*) [AddCommGroup M] : ℕ :=
  Module.finrank (ZMod p) (TensorProduct ℤ (ZMod p) M)

/-- The **rational rank** of an abelian group `M`: the `ℚ`-dimension of `ℚ ⊗[ℤ] M`. -/
noncomputable def qRank (M : Type*) [AddCommGroup M] : ℕ :=
  Module.finrank ℚ (TensorProduct ℤ ℚ M)

variable {p : ℕ}

/-! ## Elementary invariance and monotonicity -/

/-- `pRank` is invariant under additive equivalences. -/
theorem pRank_congr {M N : Type*} [AddCommGroup M] [AddCommGroup N] (e : M ≃+ N) :
    pRank p M = pRank p N :=
  LinearEquiv.finrank_eq (TensorProduct.AlgebraTensorModule.congr
    (LinearEquiv.refl (ZMod p) (ZMod p)) e.toIntLinearEquiv)

/-- `pRank` is antitone along surjections. -/
theorem pRank_le_of_surjective [Fact p.Prime] {M N : Type*} [AddCommGroup M] [AddCommGroup N]
    [Module.Finite ℤ M] (f : M →ₗ[ℤ] N) (hf : Function.Surjective f) :
    pRank p N ≤ pRank p M := by
  haveI : Module.Finite (ZMod p) (TensorProduct ℤ (ZMod p) M) :=
    Module.Finite.base_change ℤ (ZMod p) M
  set F : TensorProduct ℤ (ZMod p) M →ₗ[ZMod p] TensorProduct ℤ (ZMod p) N :=
    TensorProduct.AlgebraTensorModule.map (LinearMap.id : ZMod p →ₗ[ZMod p] ZMod p) f with hF
  have hsurj : Function.Surjective F := by
    intro y
    induction y using TensorProduct.induction_on with
    | zero => exact ⟨0, map_zero F⟩
    | add x₁ x₂ h₁ h₂ =>
        obtain ⟨u, hu⟩ := h₁
        obtain ⟨v, hv⟩ := h₂
        exact ⟨u + v, by rw [map_add, hu, hv]⟩
    | tmul a n =>
        obtain ⟨m, rfl⟩ := hf n
        exact ⟨a ⊗ₜ[ℤ] m, by rw [hF, TensorProduct.AlgebraTensorModule.map_tmul]; rfl⟩
  exact LinearMap.finrank_le_finrank_of_surjective hsurj

/-- `qRank` is antitone along surjections. -/
theorem qRank_le_of_surjective {M N : Type*} [AddCommGroup M] [AddCommGroup N]
    [Module.Finite ℤ M] (f : M →ₗ[ℤ] N) (hf : Function.Surjective f) :
    qRank N ≤ qRank M := by
  haveI : Module.Finite ℚ (TensorProduct ℤ ℚ M) := Module.Finite.base_change ℤ ℚ M
  set F : TensorProduct ℤ ℚ M →ₗ[ℚ] TensorProduct ℤ ℚ N :=
    TensorProduct.AlgebraTensorModule.map (LinearMap.id : ℚ →ₗ[ℚ] ℚ) f with hF
  have hsurj : Function.Surjective F := by
    intro y
    induction y using TensorProduct.induction_on with
    | zero => exact ⟨0, map_zero F⟩
    | add x₁ x₂ h₁ h₂ =>
        obtain ⟨u, hu⟩ := h₁
        obtain ⟨v, hv⟩ := h₂
        exact ⟨u + v, by rw [map_add, hu, hv]⟩
    | tmul a n =>
        obtain ⟨m, rfl⟩ := hf n
        exact ⟨a ⊗ₜ[ℤ] m, by rw [hF, TensorProduct.AlgebraTensorModule.map_tmul]; rfl⟩
  exact LinearMap.finrank_le_finrank_of_surjective hsurj

/-! ## Ranks of finite free modules -/

/-- `pRank` of a finite free `ℤ`-module. -/
theorem pRank_free (s : ℕ) [Fact p.Prime] : pRank p (Fin s → ℤ) = s := by
  have h : Module.finrank (ZMod p) (TensorProduct ℤ (ZMod p) (Fin s → ℤ))
      = Module.finrank (ZMod p) (ZMod p) * Module.finrank ℤ (Fin s → ℤ) :=
    Module.finrank_tensorProduct (R := ZMod p) (S := ℤ) (M := ZMod p) (M' := Fin s → ℤ)
  rw [pRank, h, Module.finrank_self, one_mul, Module.finrank_fin_fun]

/-- `qRank` of a finite free `ℤ`-module. -/
theorem qRank_free (s : ℕ) : qRank (Fin s → ℤ) = s := by
  have h : Module.finrank ℚ (TensorProduct ℤ ℚ (Fin s → ℤ))
      = Module.finrank ℚ ℚ * Module.finrank ℤ (Fin s → ℤ) :=
    Module.finrank_tensorProduct (R := ℚ) (S := ℤ) (M := ℚ) (M' := Fin s → ℤ)
  rw [qRank, h, Module.finrank_self, one_mul, Module.finrank_fin_fun]

/-! ## The exact-sequence inequality -/

/-- **The exact-sequence inequality for `pRank`**: for a surjective `ℤ`-linear map `f` with kernel
`K`, `pRank` of the source is at most `pRank K + pRank` of the target. -/
theorem pRank_le_add_ker [Fact p.Prime] {G Q : Type*} [AddCommGroup G] [AddCommGroup Q]
    [Module.Finite ℤ G] [Module.Finite ℤ Q] (f : G →ₗ[ℤ] Q) (hf : Function.Surjective f) :
    pRank p G ≤ pRank p ↥(f.ker) + pRank p Q := by
  have hbaseK : Module.Finite (ZMod p) (TensorProduct ℤ (ZMod p) ↥(f.ker)) :=
    Module.Finite.base_change ℤ (ZMod p) ↥(f.ker)
  have hbaseQ : Module.Finite (ZMod p) (TensorProduct ℤ (ZMod p) Q) :=
    Module.Finite.base_change ℤ (ZMod p) Q
  let F : TensorProduct ℤ (ZMod p) G →ₗ[ZMod p] TensorProduct ℤ (ZMod p) Q :=
    TensorProduct.AlgebraTensorModule.map (LinearMap.id : ZMod p →ₗ[ZMod p] ZMod p) f
  let K : TensorProduct ℤ (ZMod p) ↥(f.ker) →ₗ[ZMod p] TensorProduct ℤ (ZMod p) G :=
    TensorProduct.AlgebraTensorModule.map (LinearMap.id : ZMod p →ₗ[ZMod p] ZMod p)
      (Submodule.subtype f.ker)
  have hfunF : ⇑F = ⇑(LinearMap.lTensor (ZMod p) f) := by
    funext x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => rw [map_add, map_add, hx, hy]
    | tmul a m => rw [LinearMap.lTensor_tmul, TensorProduct.AlgebraTensorModule.map_tmul]; rfl
  have hfunK : ⇑K = ⇑(LinearMap.lTensor (ZMod p) (Submodule.subtype f.ker)) := by
    funext x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => rw [map_add, map_add, hx, hy]
    | tmul a m => rw [LinearMap.lTensor_tmul, TensorProduct.AlgebraTensorModule.map_tmul]; rfl
  have hexact := lTensor_exact (R := ℤ) (Q := ZMod p) (LinearMap.exact_subtype_ker_map f) hf
  have hker : F.ker = K.range := by
    ext x
    constructor
    · intro hx
      have hx2 : (LinearMap.lTensor (ZMod p) f) x = 0 := by
        rw [← congr_fun hfunF x]; exact hx
      have hx4 : x ∈ (LinearMap.lTensor (ZMod p) (Submodule.subtype f.ker)).range := by
        rw [← Function.Exact.linearMap_ker_eq hexact]
        exact (LinearMap.mem_ker).mpr hx2
      obtain ⟨y, hy⟩ := hx4
      exact ⟨y, by rw [congr_fun hfunK y]; exact hy⟩
    · rintro ⟨y, hy⟩
      have hy1 : (LinearMap.lTensor (ZMod p) (Submodule.subtype f.ker)) y = x := by
        rw [← congr_fun hfunK y]; exact hy
      have hx4 : x ∈ (LinearMap.lTensor (ZMod p) (Submodule.subtype f.ker)).range := ⟨y, hy1⟩
      have hx3 : x ∈ (LinearMap.lTensor (ZMod p) f).ker := by
        rw [Function.Exact.linearMap_ker_eq hexact]; exact hx4
      have hx2 : (LinearMap.lTensor (ZMod p) f) x = 0 := hx3
      rw [← congr_fun hfunF x] at hx2
      exact hx2
  have hrn := LinearMap.finrank_range_add_finrank_ker F
  have h1 : Module.finrank (ZMod p) ↥F.ker ≤ Module.finrank (ZMod p)
      (TensorProduct ℤ (ZMod p) ↥(f.ker)) := by
    rw [hker]
    exact LinearMap.finrank_range_le K
  have h2 : Module.finrank (ZMod p) ↥F.range ≤ Module.finrank (ZMod p)
      (TensorProduct ℤ (ZMod p) Q) :=
    Submodule.finrank_le F.range
  change Module.finrank (ZMod p) (TensorProduct ℤ (ZMod p) G) ≤
      Module.finrank (ZMod p) (TensorProduct ℤ (ZMod p) ↥(f.ker)) +
      Module.finrank (ZMod p) (TensorProduct ℤ (ZMod p) Q)
  linarith

/-- **The exact-sequence inequality for `pRank`**, additive-homomorphism form: for a surjective
additive homomorphism `f` with kernel `K`, `pRank` of the source is at most `pRank K + pRank` of the
target. -/
theorem pRank_le_add_ker_hom [Fact p.Prime] {G Q : Type*} [AddCommGroup G] [AddCommGroup Q]
    [Module.Finite ℤ G] [Module.Finite ℤ Q] (f : G →+ Q) (hf : Function.Surjective f) :
    pRank p G ≤ pRank p ↥(f.ker) + pRank p Q := by
  haveI : Module.Finite ℤ ↥(f.ker) :=
    Module.Finite.of_injective (AddSubgroup.subtype f.ker).toIntLinearMap Subtype.coe_injective
  have hbaseK : Module.Finite (ZMod p) (TensorProduct ℤ (ZMod p) ↥(f.ker)) :=
    Module.Finite.base_change ℤ (ZMod p) ↥(f.ker)
  have hbaseQ : Module.Finite (ZMod p) (TensorProduct ℤ (ZMod p) Q) :=
    Module.Finite.base_change ℤ (ZMod p) Q
  let g : G →ₗ[ℤ] Q := f.toIntLinearMap
  have hg : Function.Surjective g := hf
  let k : ↥(f.ker) →ₗ[ℤ] G := (AddSubgroup.subtype f.ker).toIntLinearMap
  have hkg : Function.Exact ⇑k ⇑g := by
    rw [LinearMap.exact_iff]
    ext x
    constructor
    · intro hx
      exact ⟨⟨x, hx⟩, rfl⟩
    · rintro ⟨y, rfl⟩
      exact y.2
  let F : TensorProduct ℤ (ZMod p) G →ₗ[ZMod p] TensorProduct ℤ (ZMod p) Q :=
    TensorProduct.AlgebraTensorModule.map (LinearMap.id : ZMod p →ₗ[ZMod p] ZMod p) g
  let K : TensorProduct ℤ (ZMod p) ↥(f.ker) →ₗ[ZMod p] TensorProduct ℤ (ZMod p) G :=
    TensorProduct.AlgebraTensorModule.map (LinearMap.id : ZMod p →ₗ[ZMod p] ZMod p) k
  have hfunF : ⇑F = ⇑(LinearMap.lTensor (ZMod p) g) := by
    funext x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => rw [map_add, map_add, hx, hy]
    | tmul a m => rw [LinearMap.lTensor_tmul, TensorProduct.AlgebraTensorModule.map_tmul]; rfl
  have hfunK : ⇑K = ⇑(LinearMap.lTensor (ZMod p) k) := by
    funext x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => rw [map_add, map_add, hx, hy]
    | tmul a m => rw [LinearMap.lTensor_tmul, TensorProduct.AlgebraTensorModule.map_tmul]; rfl
  have hexact := lTensor_exact (R := ℤ) (Q := ZMod p) hkg hg
  have hker : F.ker = K.range := by
    ext x
    constructor
    · intro hx
      have hx2 : (LinearMap.lTensor (ZMod p) g) x = 0 := by
        rw [← congr_fun hfunF x]; exact hx
      have hx4 : x ∈ (LinearMap.lTensor (ZMod p) k).range := by
        rw [← Function.Exact.linearMap_ker_eq hexact]
        exact (LinearMap.mem_ker).mpr hx2
      obtain ⟨y, hy⟩ := hx4
      exact ⟨y, by rw [congr_fun hfunK y]; exact hy⟩
    · rintro ⟨y, hy⟩
      have hy1 : (LinearMap.lTensor (ZMod p) k) y = x := by
        rw [← congr_fun hfunK y]; exact hy
      have hx4 : x ∈ (LinearMap.lTensor (ZMod p) k).range := ⟨y, hy1⟩
      have hx3 : x ∈ (LinearMap.lTensor (ZMod p) g).ker := by
        rw [Function.Exact.linearMap_ker_eq hexact]; exact hx4
      have hx2 : (LinearMap.lTensor (ZMod p) g) x = 0 := hx3
      rw [← congr_fun hfunF x] at hx2
      exact hx2
  have hrn := LinearMap.finrank_range_add_finrank_ker F
  have h1 : Module.finrank (ZMod p) ↥F.ker ≤ Module.finrank (ZMod p)
      (TensorProduct ℤ (ZMod p) ↥(f.ker)) := by
    rw [hker]
    exact LinearMap.finrank_range_le K
  have h2 : Module.finrank (ZMod p) ↥F.range ≤ Module.finrank (ZMod p)
      (TensorProduct ℤ (ZMod p) Q) :=
    Submodule.finrank_le F.range
  change Module.finrank (ZMod p) (TensorProduct ℤ (ZMod p) G) ≤
      Module.finrank (ZMod p) (TensorProduct ℤ (ZMod p) ↥(f.ker)) +
      Module.finrank (ZMod p) (TensorProduct ℤ (ZMod p) Q)
  linarith

/-- **The exact-sequence inequality for `pRank`**, additive-homomorphism form, with the finiteness
assumption only on the source. -/
theorem pRank_le_add_ker_hom' [Fact p.Prime] {G Q : Type*} [AddCommGroup G] [AddCommGroup Q]
    [Module.Finite ℤ G] (f : G →+ Q) (hf : Function.Surjective f) :
    pRank p G ≤ pRank p ↥(f.ker) + pRank p Q := by
  haveI : Module.Finite ℤ ↥(f.ker) :=
    Module.Finite.of_injective (AddSubgroup.subtype f.ker).toIntLinearMap Subtype.coe_injective
  have hbaseK : Module.Finite (ZMod p) (TensorProduct ℤ (ZMod p) ↥(f.ker)) :=
    Module.Finite.base_change ℤ (ZMod p) ↥(f.ker)
  let g : G →ₗ[ℤ] Q := f.toIntLinearMap
  have hg : Function.Surjective g := hf
  let k : ↥(f.ker) →ₗ[ℤ] G := (AddSubgroup.subtype f.ker).toIntLinearMap
  have hkg : Function.Exact ⇑k ⇑g := by
    rw [LinearMap.exact_iff]
    ext x
    constructor
    · intro hx
      exact ⟨⟨x, hx⟩, rfl⟩
    · rintro ⟨y, rfl⟩
      exact y.2
  let F : TensorProduct ℤ (ZMod p) G →ₗ[ZMod p] TensorProduct ℤ (ZMod p) Q :=
    TensorProduct.AlgebraTensorModule.map (LinearMap.id : ZMod p →ₗ[ZMod p] ZMod p) g
  let K : TensorProduct ℤ (ZMod p) ↥(f.ker) →ₗ[ZMod p] TensorProduct ℤ (ZMod p) G :=
    TensorProduct.AlgebraTensorModule.map (LinearMap.id : ZMod p →ₗ[ZMod p] ZMod p) k
  have hFsurj : Function.Surjective F := by
    intro y
    induction y using TensorProduct.induction_on with
    | zero => exact ⟨0, map_zero F⟩
    | add x y hx hy =>
        obtain ⟨u, hu⟩ := hx
        obtain ⟨v, hv⟩ := hy
        exact ⟨u + v, by rw [map_add, hu, hv]⟩
    | tmul a n =>
        obtain ⟨m, rfl⟩ := hg n
        exact ⟨a ⊗ₜ[ℤ] m, by
          show (TensorProduct.AlgebraTensorModule.map (LinearMap.id : ZMod p →ₗ[ZMod p] ZMod p) g)
            (a ⊗ₜ[ℤ] m) = a ⊗ₜ[ℤ] g m
          rw [TensorProduct.AlgebraTensorModule.map_tmul]; rfl⟩
  have hfunF : ⇑F = ⇑(LinearMap.lTensor (ZMod p) g) := by
    funext x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => rw [map_add, map_add, hx, hy]
    | tmul a m => rw [LinearMap.lTensor_tmul, TensorProduct.AlgebraTensorModule.map_tmul]; rfl
  have hfunK : ⇑K = ⇑(LinearMap.lTensor (ZMod p) k) := by
    funext x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => rw [map_add, map_add, hx, hy]
    | tmul a m => rw [LinearMap.lTensor_tmul, TensorProduct.AlgebraTensorModule.map_tmul]; rfl
  have hexact := lTensor_exact (R := ℤ) (Q := ZMod p) hkg hg
  have hker : F.ker = K.range := by
    ext x
    constructor
    · intro hx
      have hx2 : (LinearMap.lTensor (ZMod p) g) x = 0 := by
        rw [← congr_fun hfunF x]; exact hx
      have hx4 : x ∈ (LinearMap.lTensor (ZMod p) k).range := by
        rw [← Function.Exact.linearMap_ker_eq hexact]
        exact (LinearMap.mem_ker).mpr hx2
      obtain ⟨y, hy⟩ := hx4
      exact ⟨y, by rw [congr_fun hfunK y]; exact hy⟩
    · rintro ⟨y, hy⟩
      have hy1 : (LinearMap.lTensor (ZMod p) k) y = x := by
        rw [← congr_fun hfunK y]; exact hy
      have hx4 : x ∈ (LinearMap.lTensor (ZMod p) k).range := ⟨y, hy1⟩
      have hx3 : x ∈ (LinearMap.lTensor (ZMod p) g).ker := by
        rw [Function.Exact.linearMap_ker_eq hexact]; exact hx4
      have hx2 : (LinearMap.lTensor (ZMod p) g) x = 0 := hx3
      rw [← congr_fun hfunF x] at hx2
      exact hx2
  have hrn := LinearMap.finrank_range_add_finrank_ker F
  have h1 : Module.finrank (ZMod p) ↥F.ker ≤ Module.finrank (ZMod p)
      (TensorProduct ℤ (ZMod p) ↥(f.ker)) := by
    rw [hker]
    exact LinearMap.finrank_range_le K
  have h2 : Module.finrank (ZMod p) ↥F.range ≤ Module.finrank (ZMod p)
      (TensorProduct ℤ (ZMod p) Q) := by
    rw [LinearMap.range_eq_top.mpr hFsurj]
    exact le_of_eq (LinearEquiv.finrank_eq (Submodule.topEquiv (R := ZMod p) (M := TensorProduct ℤ (ZMod p) Q)))
  change Module.finrank (ZMod p) (TensorProduct ℤ (ZMod p) G) ≤
      Module.finrank (ZMod p) (TensorProduct ℤ (ZMod p) ↥(f.ker)) +
      Module.finrank (ZMod p) (TensorProduct ℤ (ZMod p) Q)
  linarith

end NK.CFTLib
