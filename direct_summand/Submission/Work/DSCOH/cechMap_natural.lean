import Mathlib
import Submission.Work.DSCOH.Cech

namespace Work.DSCOH

/-- The localization transition maps `resAt` commute with the maps `locMapOf` induced by a linear
map of the coefficient modules: the two ways around the square
```
M[1/X_S] --resAt--> M[1/X_T]
   |                   |
locMapOf φ S       locMapOf φ T
   v                   v
N[1/X_S] --resAt--> N[1/X_T]
```
agree after precomposition with `M → M[1/X_S]`, so they agree by the universal property of the
localization (`IsLocalizedModule.ext`). -/
lemma resAt_locMapOf_comm {A : Type*} [CommRing A] {n : ℕ}
    {M : Type*} [AddCommGroup M] [Module A M] [Module (Poly A n) M] [IsScalarTower A (Poly A n) M]
    {N : Type*} [AddCommGroup N] [Module A N] [Module (Poly A n) N] [IsScalarTower A (Poly A n) N]
    (φ : M →ₗ[Poly A n] N) {S T : Finset (Fin n)} (h : S ⊆ T) :
    (locMapOf (A := A) (M := M) (N := N) φ T).comp (resAt (A := A) (M := M) h) =
      (resAt (A := A) (M := N) h).comp (locMapOf (A := A) (M := M) (N := N) φ S) := by
  have hunit : ∀ x : subS (A := A) S,
      IsUnit (algebraMap (Poly A n)
        (Module.End (Poly A n) (locAt (A := A) (M := N) T)) x) :=
    fun x => IsLocalizedModule.map_units (LocalizedModule.mkLinearMap (subS (A := A) T) N)
      ⟨x.1, subS_mono (A := A) h x.2⟩
  refine IsLocalizedModule.ext (S := subS (A := A) S)
    (f := LocalizedModule.mkLinearMap (subS (A := A) S) M) hunit ?_
  ext m
  simp only [LinearMap.comp_apply, resAt, LocalizedModule.liftOfLE,
    IsLocalizedModule.liftOfLE_apply, locMapOf, IsLocalizedModule.map_apply]

/-- Naturality of the degree-zero part of the chart localizations: restricting from the chart `S` to
the chart `T` and then applying the map induced by `φ` agrees with applying the map induced by `φ`
and then restricting. -/
lemma degZeroMapOf_resAt_apply {A : Type*} [CommRing A] {n : ℕ}
    {M : Type*} [AddCommGroup M] [Module A M] [Module (Poly A n) M] [IsScalarTower A (Poly A n) M]
    (ℳ : ℕ → Submodule A M) [SetLike.GradedSMul (homSub A n) ℳ]
    {N : Type*} [AddCommGroup N] [Module A N] [Module (Poly A n) N] [IsScalarTower A (Poly A n) N]
    (𝒩 : ℕ → Submodule A N) [SetLike.GradedSMul (homSub A n) 𝒩]
    (φ : M →ₗ[Poly A n] N)
    (hφ : ∀ d, Submodule.map (φ.restrictScalars A) (ℳ d) ≤ 𝒩 d)
    {S T : Finset (Fin n)} (h : S ⊆ T) (y : degZero (A := A) (n := n) (M := M) ℳ S) :
    degZeroMapOf (A := A) (n := n) ℳ 𝒩 φ T
        (fun x hx => degZero_locMapOf (A := A) (n := n) ℳ 𝒩 φ hφ T x hx)
        (degPartRestrict (A := A) (n := n) (M := M) ℳ (resAt (A := A) (M := M) h)
          (fun x hx => resAt_degZero (A := A) (n := n) (M := M) (ℳ := ℳ) h x hx) y)
      =
    degPartRestrict (A := A) (n := n) (M := N) 𝒩 (resAt (A := A) (M := N) h)
        (fun x hx => resAt_degZero (A := A) (n := n) (M := N) (ℳ := 𝒩) h x hx)
        (degZeroMapOf (A := A) (n := n) ℳ 𝒩 φ S
          (fun x hx => degZero_locMapOf (A := A) (n := n) ℳ 𝒩 φ hφ S x hx) y) := by
  refine Subtype.ext ?_
  exact LinearMap.congr_fun (resAt_locMapOf_comm (A := A) φ h) y.1

theorem cechMap_natural {A : Type*} [CommRing A] {n : ℕ}
    {M : Type*} [AddCommGroup M] [Module A M] [Module (Poly A n) M] [IsScalarTower A (Poly A n) M]
    {N : Type*} [AddCommGroup N] [Module A N] [Module (Poly A n) N] [IsScalarTower A (Poly A n) N]
    (ℳ : ℕ → Submodule A M) [SetLike.GradedSMul (homSub A n) ℳ]
    (𝒩 : ℕ → Submodule A N) [SetLike.GradedSMul (homSub A n) 𝒩]
    (φ : M →ₗ[Poly A n] N) (hφ : ∀ d, Submodule.map (φ.restrictScalars A) (ℳ d) ≤ 𝒩 d)
    (q : ℕ) :
    (cechMap (A := A) (n := n) ℳ 𝒩 φ hφ (q + 1)).comp
      (cechDiff (A := A) (n := n) (M := M) ℳ q) =
      (cechDiff (A := A) (n := n) (M := N) 𝒩 q).comp
        (cechMap (A := A) (n := n) ℳ 𝒩 φ hφ q) := by
  apply LinearMap.ext
  intro x
  funext T
  simp only [LinearMap.comp_apply, cechMap, cechDiff, LinearMap.pi_apply, LinearMap.proj_apply]
  rw [cechDiffComp, cechDiffComp]
  rw [LinearMap.sum_apply, LinearMap.sum_apply, map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [LinearMap.smul_apply, LinearMap.comp_apply, LinearMap.proj_apply, map_zsmul]
  rw [LinearMap.smul_apply, LinearMap.comp_apply, LinearMap.proj_apply, LinearMap.pi_apply,
    LinearMap.comp_apply, LinearMap.proj_apply]
  have hkey := degZeroMapOf_resAt_apply (A := A) (n := n) ℳ 𝒩 φ hφ (S := (T.1).erase i.1)
    (T := T.1) (Finset.erase_subset i.1 T.1)
    (x ⟨(T.1).erase i.1, by rw [Finset.card_erase_of_mem i.2]; omega⟩)
  rw [hkey]

end Work.DSCOH
