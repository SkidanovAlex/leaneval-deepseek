import Mathlib
import Submission.Work.DSG4a.FreeResDefs

/-!
# `Work.DSG4a.quasiIso_qdown`

The syzygy resolution `Kcc` of `FreeResDefs` comes with a comparison map
`qdown : Kcc ⟶ (single₀ (ModuleCat A)).obj M` given in degree `0` by the surjection
`phi0 : (Fin (n0) → A) ↠ M`, whose kernel is exactly the range of the first differential
`base.f : (Fin (base.n) → A) →ₗ (Fin (n0) → A)` (that is `range_base`).

This file proves that `qdown` is a quasi-isomorphism:

* in **positive degrees** `i = n+1`, both `Kcc` and the single complex are exact
  (`Kcc_exactAt`, `ChainComplex.exactAt_succ_single_obj`), so the induced maps on homology
  are isomorphisms (`quasiIsoAt_iff_exactAt'`);
* in **degree `0`**, the map is identified, via `ShortComplex.quasiIso_iff_isIso_descOpcycles`,
  with the map `coker (base.f) ⟶ M` induced by `phi0`; since `range (base.f) = ker (phi0)` and
  `phi0` is surjective (`range_base`, `phi0_surj`), this map is bijective, hence an isomorphism.

The two cases are proved as the separate lemmas `quasiIsoAt_zero_qdown` and
`quasiIsoAt_succ_qdown`; the target `quasiIso_qdown` assembles them with `quasiIso_iff`.
-/

open CategoryTheory Limits

universe u

namespace Work.DSG4a

variable {A : Type u} [CommRing A] [IsNoetherianRing A]
variable (M : Type u) [AddCommGroup M] [Module A M] [Module.Finite A M]

/-- **The comparison map `qdown` is a quasi-isomorphism in degree `0`.**

The short complex `S₁ := Kcc.sc' 1 0 0` is `Kcc.X 1 --base.f--> Kcc.X 0 --0--> Kcc.X 0`,
so its `opcycles` identify with the cokernel of `base.f`, while the corresponding short
complex of the single complex is `0 → M → M` with both maps zero.  The map induced by
`qdown.f 0 = phi0` on opcycles is bijective because `range (base.f) = ker (phi0)` and
`phi0` is surjective. -/
lemma quasiIsoAt_zero_qdown : QuasiIsoAt (qdown (A:=A) M) 0 := by
  rw [ChainComplex.quasiIsoAt₀_iff]
  let S₁ := HomologicalComplex.sc' (Kcc (A:=A) M) 1 0 0
  let S₂ := HomologicalComplex.sc'
    ((ChainComplex.single₀ (ModuleCat.{u} A)).obj (ModuleCat.of A M)) 1 0 0
  let φ : S₁ ⟶ S₂ :=
    (HomologicalComplex.shortComplexFunctor' (ModuleCat.{u} A) (ComplexShape.down ℕ) 1 0 0).map
      (qdown (A:=A) M)
  change ShortComplex.QuasiIso φ
  -- `S₁.g = Kcc.d 0 0 = 0`, and both differentials of `S₂` vanish
  have hg₁ : S₁.g = 0 := by
    show (Kcc (A:=A) M).d 0 0 = 0
    apply HomologicalComplex.shape
    simp [ComplexShape.down]
  have hf₂ : S₂.f = 0 := by
    show ((ChainComplex.single₀ (ModuleCat.{u} A)).obj (ModuleCat.of A M)).d 1 0 = 0
    exact HomologicalComplex.single_obj_d (ComplexShape.down ℕ) 0 (ModuleCat.of A M) 1 0
  have hg₂ : S₂.g = 0 := by
    show ((ChainComplex.single₀ (ModuleCat.{u} A)).obj (ModuleCat.of A M)).d 0 0 = 0
    exact HomologicalComplex.single_obj_d (ComplexShape.down ℕ) 0 (ModuleCat.of A M) 0 0
  rw [ShortComplex.quasiIso_iff_isIso_descOpcycles φ hg₁ hf₂ hg₂]
  -- the two inputs: the range/kernel condition and surjectivity of `phi0`
  have hrange : LinearMap.range (S₁.f).hom = LinearMap.ker (φ.τ₂).hom := by
    show LinearMap.range (base (A:=A) M).f = LinearMap.ker (phi0 (A:=A) M)
    exact range_base (A:=A) M
  have hs : Function.Surjective (φ.τ₂).hom := by
    show Function.Surjective (phi0 (A:=A) M)
    exact phi0_surj (A:=A) M
  have key : ∀ (hk : S₁.f ≫ φ.τ₂ = 0), IsIso (S₁.descOpcycles φ.τ₂ hk) := by
    intro hk
    have hp : S₁.pOpcycles ≫ S₁.descOpcycles φ.τ₂ hk = φ.τ₂ :=
      ShortComplex.p_descOpcycles _ _ _
    have hp_surj : Function.Surjective (S₁.pOpcycles).hom :=
      (ModuleCat.epi_iff_surjective S₁.pOpcycles).mp inferInstance
    -- surjectivity of the descended map, from surjectivity of `phi0`
    have hsurj : Function.Surjective (S₁.descOpcycles φ.τ₂ hk).hom := by
      intro y
      obtain ⟨x, hx⟩ := hs y
      refine ⟨(S₁.pOpcycles).hom x, ?_⟩
      have h := LinearMap.congr_fun (congrArg ModuleCat.Hom.hom hp) x
      simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h
      rw [h, hx]
    -- injectivity of the descended map, from `range (base.f) = ker (phi0)`
    have hinj : Function.Injective (S₁.descOpcycles φ.τ₂ hk).hom := by
      intro a b hab
      obtain ⟨x, rfl⟩ := hp_surj a
      obtain ⟨y, rfl⟩ := hp_surj b
      have hxy : (φ.τ₂).hom (x - y) = 0 := by
        have h1 := LinearMap.congr_fun (congrArg ModuleCat.Hom.hom hp) x
        have h2 := LinearMap.congr_fun (congrArg ModuleCat.Hom.hom hp) y
        simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h1 h2
        rw [map_sub, ← h1, ← h2, hab, sub_self]
      have hxy' : x - y ∈ LinearMap.ker (φ.τ₂).hom := LinearMap.mem_ker.mpr hxy
      rw [← hrange] at hxy'
      obtain ⟨z, hz⟩ := LinearMap.mem_range.mp hxy'
      have hfz : (S₁.pOpcycles).hom ((S₁.f).hom z) = 0 := by
        rw [← ModuleCat.comp_apply, ShortComplex.f_pOpcycles]
        simp
      have hsub : (S₁.pOpcycles).hom (x - y) = 0 := by
        rw [← hz]; exact hfz
      rw [map_sub, sub_eq_zero] at hsub
      exact hsub
    rw [isIso_iff_mono_and_epi, ModuleCat.mono_iff_injective, ModuleCat.epi_iff_surjective]
    exact ⟨hinj, hsurj⟩
  exact key _

/-- **The comparison map `qdown` is a quasi-isomorphism in positive degrees.**

In degree `n + 1`, the single complex `M[0]` is exact (`ChainComplex.exactAt_succ_single_obj`)
and `Kcc` is exact by construction (`Kcc_exactAt`), so the induced map on homology is an
isomorphism by `quasiIsoAt_iff_exactAt'`. -/
lemma quasiIsoAt_succ_qdown (n : ℕ) : QuasiIsoAt (qdown (A:=A) M) (n + 1) := by
  rw [quasiIsoAt_iff_exactAt' (qdown (A:=A) M) (n + 1)
    (ChainComplex.exactAt_succ_single_obj (ModuleCat.of A M) n)]
  exact Kcc_exactAt (A:=A) M n

end Work.DSG4a

namespace Work.DSG4a

open CategoryTheory Limits

/-- The comparison map from the free resolution of a finitely generated module over a
Noetherian ring to the module concentrated in degree zero is a quasi-isomorphism. -/
theorem quasiIso_qdown {A : Type u} [CommRing A] [IsNoetherianRing A]
    (M : Type u) [AddCommGroup M] [Module A M] [Module.Finite A M] :
    QuasiIso (qdown (A:=A) M) := by
  rw [quasiIso_iff]
  intro i
  cases i with
  | zero => exact quasiIsoAt_zero_qdown (A:=A) M
  | succ n => exact quasiIsoAt_succ_qdown (A:=A) M n

end Work.DSG4a
