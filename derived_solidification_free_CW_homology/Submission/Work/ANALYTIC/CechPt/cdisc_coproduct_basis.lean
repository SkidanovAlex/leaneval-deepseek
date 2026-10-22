import Mathlib
import Submission.Work.ANALYTIC.CechPt.DdZfAux

/-!
# `Cdisc T` is a coproduct of copies of `ℤ` (the Haar basis, in condensed form)

For an infinite light profinite set `T` the discrete light condensed abelian group
`Cdisc T = C(T,ℤ)_disc` of locally constant `ℤ`-valued functions is the coproduct
`∐_{j : Haar.JIdx} ℤ` of one copy of `ℤ` for each element of the Haar/Schauder basis
`Haar.fJ T` (`Haar.JIdx = ℕ ∪ {∞}`), and the isomorphism can be chosen so that the `j`-th
coproduct inclusion is the *global section* of `Cdisc T` classified by the basis vector
`fJ T j`:

`toPointEquiv (Cdisc T) (Sigma.ι j ≫ Θ.inv) = LocallyConstant.const pt (fJ T j)`.

## The route

`Cdisc T = lcDisc (LC T)` where `lcDisc = LightCondMod.LocallyConstant.functor ℤ` and
`LC T = C(T,ℤ)`.  The Haar/Schauder basis theorem `Haar.haar_basisIso` gives a `ℤ`-linear
isomorphism `e : LC T ≅ (Haar.JIdx →₀ ℤ)` whose inverse sends `Finsupp.single j 1` to `fJ T j`.
Applying the (coproduct preserving) functor `lcDisc` gives

`Cdisc T ≅ lcDisc (JIdx →₀ ℤ) ≅ ∐_{j : JIdx} ℤ`,

using `lcDisc (JIdx →₀ ℤ) ≅ disc (JIdx →₀ ℤ)` (`lcDiscIntIso`) and
`disc (JIdx →₀ ℤ) ≅ ∐_{j} ℤ` (`disc_finsupp_iso_coprod`).

The point of the statement is the compatibility with the canonical generator, i.e. with the
identification `toPointEquiv` of `Submission/Work/ATOM/projective_P.lean` (evaluation of a
morphism `𝟙 ⟶ Y` at the point `∗`).

The only place where this compatibility enters is the canonical comparison
`lcDiscIntIso.inv : 𝟙 ⟶ lcDisc ℤ`: both `lcDiscIntIso.inv ≫ unitIso.hom ≫ LCZhom` and the
identity are endomorphisms of `lcDisc ℤ`, hence (`lcDisc` being fully faithful and `End(ℤ) = ℤ`)
multiplication by an integer scalar `u`; since the composite is invertible, `u` is a *unit* of
`ℤ`.  Multiplying a `lcDisc`-isomorphism by such a unit scalar (which is an isomorphism, being
`±1`-multiplication) does not change the truth of the pointwise condition but *does* take care of
the mismatch: the pointwise statement becomes

`σ_j ≫ Θ.inv = u • (the standard component)`

and the standard components were computed above (`sigma_iota_comp_coproductZlcIso_inv`).

Note that we never need to know *which* unit `u` is: the pointwise condition is insensitive to
it, because it is imposed by `toPointEquiv`-inverting the target element, and we simply build `Θ`
with the extra scalar built into it.
-/

open CategoryTheory Limits LightProfinite LightCondensed MonoidalCategory MonoidalClosed
open _root_.LightCondensed _root_.LightCondensed.Solid OnePoint Opposite

noncomputable section

namespace Work.ANALYTIC.CechPt

/-- The locally constant functor `lcDisc = LightCondMod.LocallyConstant.functor ℤ`. -/
private abbrev lcF : ModuleCat ℤ ⥤ LightCondAb := LightCondMod.LocallyConstant.functor ℤ

/-- The constant family `j ↦ ℤ` indexing the coproduct `∐_j ℤ`. -/
private abbrev hIdxFam : Work.ANALYTIC.Haar.JIdx → ModuleCat ℤ :=
  fun _ => (ModuleCat.of ℤ ℤ : ModuleCat ℤ)

/-- The morphism `ℤ ⟶ M` of `ModuleCat ℤ` sending `1` to `m`. -/
private abbrev spn {M : ModuleCat ℤ} (m : ↥M) :
    (ModuleCat.of ℤ ℤ : ModuleCat ℤ) ⟶ M :=
  ModuleCat.ofHom (LinearMap.toSpanSingleton ℤ ↥M m)

private theorem spn_apply_one {M : ModuleCat ℤ} (m : ↥M) : (spn m).hom 1 = m :=
  LinearMap.toSpanSingleton_apply_one ℤ ↥M m

private theorem spn_comp {M N : ModuleCat ℤ} (m : ↥M) (g : M ⟶ N) :
    spn m ≫ g = spn (g.hom m) := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext_ring
  rw [ModuleCat.comp_apply]
  rw [show (ModuleCat.Hom.hom (spn m)) 1 = m from spn_apply_one m]
  rw [show (ModuleCat.Hom.hom (spn (g.hom m))) 1 = g.hom m from spn_apply_one (g.hom m)]

/-- The scalar case: multiplying by a scalar commutes with `spn`, with the scalar on either
side. -/
private theorem spn_comp_smul {M : ModuleCat ℤ} (u : ℤ) (m : ↥M) :
    spn m ≫ (u • 𝟙 M) = (u • 𝟙 (ModuleCat.of ℤ ℤ)) ≫ spn m := by
  rw [Preadditive.comp_zsmul, Preadditive.zsmul_comp, Category.comp_id, Category.id_comp]

private theorem ofHom_lsingle_eq_spn (j : Work.ANALYTIC.Haar.JIdx) :
    ModuleCat.ofHom (Finsupp.lsingle j) =
      spn (M := ModuleCat.of ℤ (Work.ANALYTIC.Haar.JIdx →₀ ℤ)) (Finsupp.single j 1) := by
  have h : (Finsupp.lsingle j : ℤ →ₗ[ℤ] (Work.ANALYTIC.Haar.JIdx →₀ ℤ)) =
      LinearMap.toSpanSingleton ℤ (Work.ANALYTIC.Haar.JIdx →₀ ℤ) (Finsupp.single j 1) := by
    apply LinearMap.ext_ring
    rw [Finsupp.lsingle_apply, LinearMap.toSpanSingleton_apply_one]
  rw [h]

private theorem const_map_one (X : Type*) [TopologicalSpace X] {Z : Type*} (y : Z) (f : ℤ → Z)
    (hf : f 1 = y) : (LocallyConstant.const X (1 : ℤ)).map f = LocallyConstant.const X y := by
  rw [← hf]
  apply LocallyConstant.ext
  intro s
  simp only [LocallyConstant.map_apply, Function.comp_apply, LocallyConstant.coe_const,
    Function.const_apply]

section

local instance lcFIsLeftAdjoint : lcF.IsLeftAdjoint :=
  (LightCondMod.LocallyConstant.adjunction ℤ).isLeftAdjoint

/-! ## The inverse of the finsupp coproduct comparison on the inclusions -/

/-- The `j`-th coproduct inclusion composed with the inverse of
`finsuppIsoCoproductZ J : ℤ[J] ≅ ∐_j ℤ` is the `j`-th basis vector `Finsupp.lsingle j`. -/
theorem iota_finsuppIsoCoproductZ_inv (J : Type) (j : J) :
    CategoryTheory.CategoryStruct.comp
      (CategoryTheory.Limits.Sigma.ι (fun _ : J => (ModuleCat.of ℤ ℤ : ModuleCat ℤ)) j)
      (Work.ANALYTIC.finsuppIsoCoproductZ J).inv = ModuleCat.ofHom (Finsupp.lsingle j) := by
  rw [Work.ANALYTIC.finsuppIsoCoproductZ]
  exact IsColimit.comp_coconePointUniqueUpToIso_inv (ModuleCat.finsuppCoconeIsColimit ℤ ℤ J)
    (coproductIsCoproduct _) (Discrete.mk j)

/-! ## The comparison `lcDisc (ℤ[JIdx]) ≅ ∐_{j} ℤ` -/

/-- **The coproduct description of `lcDisc (ℤ[Haar.JIdx])`.**  Since `lcDisc` preserves
coproducts and `ℤ[JIdx]` is the coproduct of `JIdx` copies of `ℤ`, the locally constant model of
`ℤ[JIdx]` is the coproduct of `JIdx` copies of the unit `𝟙 = lcDisc ℤ`. -/
noncomputable def coproductZlcIso :
    lcF.obj (ModuleCat.of ℤ (Work.ANALYTIC.Haar.JIdx →₀ ℤ)) ≅
      ∐ (fun _ : Work.ANALYTIC.Haar.JIdx => 𝟙_ LightCondAb) :=
  lcF.mapIso (Work.ANALYTIC.finsuppIsoCoproductZ Work.ANALYTIC.Haar.JIdx) ≪≫
    PreservesCoproduct.iso lcF hIdxFam ≪≫
    Sigma.mapIso (fun _ : Work.ANALYTIC.Haar.JIdx => lcDiscIntIso)

/-- **The value of `coproductZlcIso.inv` on the coproduct inclusions.**  The `j`-th inclusion is
sent to the composite of the canonical comparison `𝟙 ⟶ lcDisc ℤ` with the `lcDisc`-image of the
`j`-th basis vector of `ℤ[JIdx]`. -/
theorem sigma_iota_comp_coproductZlcIso_inv (j : Work.ANALYTIC.Haar.JIdx) :
    Sigma.ι (fun _ : Work.ANALYTIC.Haar.JIdx => 𝟙_ LightCondAb) j ≫ coproductZlcIso.inv =
      (lcDiscIntIso.inv : (𝟙_ LightCondAb) ⟶ Work.ATOM.ZS.Unred.LCZ) ≫
        lcF.map (ModuleCat.ofHom (Finsupp.lsingle j)) := by
  rw [coproductZlcIso, Iso.trans_inv, Iso.trans_inv]
  simp only [Category.assoc]
  rw [← Category.assoc, Sigma.ι_mapIso_inv, Category.assoc]
  rw [PreservesCoproduct.inv_hom lcF hIdxFam,
    CategoryTheory.Limits.ι_comp_sigmaComparison_assoc lcF hIdxFam j]
  rw [Functor.mapIso_inv, ← Functor.map_comp, iota_finsuppIsoCoproductZ_inv]

end

/-! ## The scalar relating the two canonical comparisons `𝟙 ≅ lcDisc ℤ` -/

/-- **`IsIso` of a unit multiple of the identity.**  If `u * v = 1` then multiplication by `u` is
an isomorphism with inverse multiplication by `v`. -/
private theorem isIso_zsmul_id_of_mul_eq_one (u v : ℤ) (h : u * v = 1) (X : ModuleCat ℤ) :
    IsIso (u • 𝟙 X) :=
  ⟨(v • 𝟙 X : X ⟶ X),
    by rw [Preadditive.zsmul_comp, Preadditive.comp_zsmul, smul_smul, h, one_smul,
      Category.id_comp],
    by rw [Preadditive.zsmul_comp, Preadditive.comp_zsmul, smul_smul, mul_comm v u, h, one_smul,
      Category.id_comp]⟩

/-- **A unit scalar for `ℤ` is a unit scalar everywhere.**  If multiplication by `u` is invertible
on `ℤ`, then it is invertible on every `ℤ`-module. -/
private theorem isIso_zsmul_id_of_isIso (u : ℤ) (h : IsIso (u • 𝟙 (ModuleCat.of ℤ ℤ)))
    (X : ModuleCat ℤ) : IsIso (u • 𝟙 X) := by
  let v : ℤ := (inv (u • 𝟙 (ModuleCat.of ℤ ℤ))).hom 1
  have hv : u * v = 1 := by
    have h1 : (ConcreteCategory.hom ((u • 𝟙 (ModuleCat.of ℤ ℤ)) ≫
        inv (u • 𝟙 (ModuleCat.of ℤ ℤ)))) (1 : ℤ) = 1 := by
      rw [IsIso.hom_inv_id]
      rfl
    have h2 : (ConcreteCategory.hom ((u • 𝟙 (ModuleCat.of ℤ ℤ)) ≫
        inv (u • 𝟙 (ModuleCat.of ℤ ℤ)))) (1 : ℤ) = u * v := by
      rw [ModuleCat.comp_apply]
      show (ModuleCat.Hom.hom (inv (u • 𝟙 (ModuleCat.of ℤ ℤ))))
          ((ModuleCat.Hom.hom (u • 𝟙 (ModuleCat.of ℤ ℤ))) 1) = u * v
      rw [show (ModuleCat.Hom.hom (u • 𝟙 (ModuleCat.of ℤ ℤ))) 1 = u • (1 : ℤ) from by
        rw [ModuleCat.hom_smul, ModuleCat.hom_id]
        rfl]
      rw [map_zsmul, smul_eq_mul]
    rw [← h2, h1]
  exact isIso_zsmul_id_of_mul_eq_one u v hv X

/-- **The two canonical comparisons `𝟙 ⟶ lcDisc ℤ` differ by a unit scalar.**

The composite `lcDiscIntIso.hom ≫ unitIso.hom ≫ LCZhom` is an endomorphism of `lcDisc ℤ`; as
`lcDisc` is fully faithful and `End(ℤ) = ℤ`, it is multiplication by some integer `u`, and being
invertible, `u` is a unit.  Consequently `unitIso.hom ≫ LCZhom = lcDiscIntIso.inv ≫ (the same
endomorphism)`.  We do not determine the sign of the scalar, and never need to. -/
private theorem cmp_scalar :
    ∃ (β : (ModuleCat.of ℤ ℤ : ModuleCat ℤ) ⟶ (ModuleCat.of ℤ ℤ : ModuleCat ℤ)),
      IsIso β ∧
      (Work.ATOM.unitIso.hom ≫ Work.ATOM.ZS.Unred.LCZhom) = lcDiscIntIso.inv ≫ lcF.map β ∧
      β = (β.hom 1) • 𝟙 (ModuleCat.of ℤ ℤ) := by
  have hFF := LightCondMod.LocallyConstant.fullyFaithfulFunctor ℤ
  haveI : IsIso Work.ATOM.ZS.Unred.LCZhom := Work.ATOM.ZS.Unred.isIso_LCZhom
  let γ : lcF.obj (ModuleCat.of ℤ ℤ) ⟶ lcF.obj (ModuleCat.of ℤ ℤ) :=
    lcDiscIntIso.hom ≫ Work.ATOM.unitIso.hom ≫ Work.ATOM.ZS.Unred.LCZhom
  haveI hγ : IsIso γ := by
    dsimp only [γ]
    infer_instance
  let β : (ModuleCat.of ℤ ℤ : ModuleCat ℤ) ⟶ (ModuleCat.of ℤ ℤ : ModuleCat ℤ) := hFF.preimage γ
  have hβγ : lcF.map β = γ := hFF.map_preimage γ
  have hβIso : IsIso β := by
    refine ⟨hFF.preimage (inv γ), ?_, ?_⟩
    · apply hFF.map_injective
      rw [lcF.map_comp, hβγ, hFF.map_preimage (inv γ), IsIso.hom_inv_id γ]
      exact (CategoryTheory.Functor.map_id lcF (ModuleCat.of ℤ ℤ)).symm
    · apply hFF.map_injective
      rw [lcF.map_comp, hFF.map_preimage (inv γ), hβγ, IsIso.inv_hom_id γ]
      exact (CategoryTheory.Functor.map_id lcF (ModuleCat.of ℤ ℤ)).symm
  have hβ : β = (β.hom 1) • 𝟙 (ModuleCat.of ℤ ℤ) := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext_ring
    show (ModuleCat.Hom.hom β) 1 = (ModuleCat.Hom.hom ((β.hom 1) • 𝟙 (ModuleCat.of ℤ ℤ))) 1
    rw [ModuleCat.hom_smul, ModuleCat.hom_id]
    show (ModuleCat.Hom.hom β) 1 = ((β.hom 1) • LinearMap.id) 1
    rw [LinearMap.smul_apply, LinearMap.id_coe, _root_.id_eq, smul_eq_mul, mul_one]
  refine ⟨β, hβIso, ?_, hβ⟩
  have hkey : lcDiscIntIso.inv ≫ γ = Work.ATOM.unitIso.hom ≫ Work.ATOM.ZS.Unred.LCZhom := by
    show lcDiscIntIso.inv ≫ (lcDiscIntIso.hom ≫
      (Work.ATOM.unitIso.hom ≫ Work.ATOM.ZS.Unred.LCZhom)) = _
    rw [Iso.inv_hom_id_assoc]
  rw [← hkey, ← hβγ]

/-! ## The point level of `lcDisc`-maps -/

/-- **The section of `lcDisc M` attached to a linear map `ψ : ℤ ⟶ M`.**  The inverse image of the
constant function `x` under `homFreeEquiv ∗` is the `lcDisc`-image of the map `1 ↦ x`, expressed
with the canonical generator: this is the freeness of `ℤ[∗]` (`LCZhom`). -/
private theorem homFreeEquiv_symm_const (M : ModuleCat ℤ) (x : ↥M) :
    (Work.ATOM.homFreeEquiv Work.ATOM.pt (lcF.obj M)).symm
        (LocallyConstant.const ↥(Work.ATOM.pt.toTop) x :
          ↥((lcF.obj M).obj.obj (op Work.ATOM.pt)))
      = Work.ATOM.ZS.Unred.LCZhom ≫ lcF.map (spn x) := by
  have h : Work.ATOM.homFreeEquiv Work.ATOM.pt (lcF.obj M)
      (Work.ATOM.ZS.Unred.LCZhom ≫ lcF.map (spn x))
      = (LocallyConstant.const ↥(Work.ATOM.pt.toTop) x :
          ↥((lcF.obj M).obj.obj (op Work.ATOM.pt))) := by
    rw [Work.ATOM.ZS.Unred.homFreeEquiv_comp, Work.ATOM.ZS.Unred.homFreeEquiv_LCZhom]
    rw [show ((lcF.map (spn x)).hom.app (op Work.ATOM.pt)) Work.ATOM.ZS.Unred.oneLCZ
        = Work.ATOM.ZS.Unred.oneLCZ.map ((spn x).hom) from rfl]
    show (LocallyConstant.const ↥(Work.ATOM.pt.toTop) (1 : ℤ)).map ((spn x).hom)
        = LocallyConstant.const ↥(Work.ATOM.pt.toTop) x
    rw [const_map_one ↥(Work.ATOM.pt.toTop) x ((spn x).hom) (spn_apply_one x)]
  exact (Equiv.symm_apply_eq _).mpr h.symm

/-- **The inverse of `toPointEquiv` at a constant function.**  By definition `toPointEquiv` is
`homFreeEquiv ∗` composed with the identification `𝟙 ≅ ℤ[∗]`; hence inverting it and applying it
to the constant function `x` gives the `lcDisc`-image of the map `1 ↦ x` composed with the
canonical comparison `𝟙 ≅ lcDisc ℤ`. -/
private theorem toPointEquiv_symm_const (M : ModuleCat ℤ) (x : ↥M) :
    (Work.ATOM.toPointEquiv (lcF.obj M)).symm
        (LocallyConstant.const ↥(Work.ATOM.pt.toTop) x : ↥((lcF.obj M).obj.obj (op Work.ATOM.pt)))
      = (Work.ATOM.unitIso.hom ≫ Work.ATOM.ZS.Unred.LCZhom) ≫ lcF.map (spn x) := by
  show Work.ATOM.unitIso.hom ≫ (Work.ATOM.homFreeEquiv Work.ATOM.pt (lcF.obj M)).symm
      (LocallyConstant.const ↥(Work.ATOM.pt.toTop) x : ↥((lcF.obj M).obj.obj (op Work.ATOM.pt)))
    = _
  rw [homFreeEquiv_symm_const, Category.assoc]

section Main

variable (T : LightProfinite.{0}) [Infinite T]

/-- **`Cdisc T` is a coproduct of copies of the unit, compatibly with the Haar basis.**  This is
`cdisc_coproduct_basis` with the monoidal unit `𝟙_ LightCondAb = Z` written explicitly; the two
are the same statement because `Z = 𝟙_ LightCondAb` definitionally. -/
theorem cdisc_coproduct_basis_aux :
    ∃ Θ : Work.ANALYTIC.Cdisc T ≅ ∐ (fun _ : Work.ANALYTIC.Haar.JIdx => 𝟙_ LightCondAb),
      ∀ j : Work.ANALYTIC.Haar.JIdx,
        Work.ATOM.toPointEquiv (Work.ANALYTIC.Cdisc T)
          (CategoryTheory.CategoryStruct.comp
            (CategoryTheory.Limits.Sigma.ι
              (fun _ : Work.ANALYTIC.Haar.JIdx => 𝟙_ LightCondAb) j) Θ.inv) =
        LocallyConstant.const ↥(Work.ATOM.pt.toTop) (Work.ANALYTIC.Haar.fJ T j) := by
  obtain ⟨e, -, he⟩ := Work.ANALYTIC.Haar.haar_basisIso T
  obtain ⟨β, hβIso, hCmp, hβ⟩ := cmp_scalar
  haveI hIsoβ : IsIso ((β.hom 1) • 𝟙 (ModuleCat.of ℤ (Work.ANALYTIC.Haar.LC T))) :=
    isIso_zsmul_id_of_isIso (β.hom 1) (by rw [← hβ]; exact hβIso) _
  let standard : lcF.obj (ModuleCat.of ℤ (Work.ANALYTIC.Haar.LC T)) ≅
      ∐ (fun _ : Work.ANALYTIC.Haar.JIdx => 𝟙_ LightCondAb) := lcF.mapIso e ≪≫ coproductZlcIso
  let Θ : Work.ANALYTIC.Cdisc T ≅
      ∐ (fun _ : Work.ANALYTIC.Haar.JIdx => 𝟙_ LightCondAb) :=
    (asIso (standard.inv ≫
      lcF.map ((β.hom 1) • 𝟙 (ModuleCat.of ℤ (Work.ANALYTIC.Haar.LC T))))).symm
  refine ⟨Θ, fun j => ?_⟩
  -- the `j`-th component of the new isomorphism
  have hcomp : Sigma.ι (fun _ : Work.ANALYTIC.Haar.JIdx => 𝟙_ LightCondAb) j ≫ Θ.inv
      = (Work.ATOM.unitIso.hom ≫ Work.ATOM.ZS.Unred.LCZhom) ≫
        lcF.map (spn (Work.ANALYTIC.Haar.fJ T j)) := by
    show Sigma.ι (fun _ : Work.ANALYTIC.Haar.JIdx => 𝟙_ LightCondAb) j ≫
      (standard.inv ≫ lcF.map ((β.hom 1) •
        𝟙 (ModuleCat.of ℤ (Work.ANALYTIC.Haar.LC T)))) = _
    rw [← Category.assoc]
    -- the component of the standard isomorphism
    have hstd : Sigma.ι (fun _ : Work.ANALYTIC.Haar.JIdx => 𝟙_ LightCondAb) j ≫ standard.inv
        = lcDiscIntIso.inv ≫ lcF.map (spn (Work.ANALYTIC.Haar.fJ T j)) := by
      show Sigma.ι (fun _ : Work.ANALYTIC.Haar.JIdx => 𝟙_ LightCondAb) j ≫
        (coproductZlcIso.inv ≫ (lcF.mapIso e).inv) = _
      rw [← Category.assoc, sigma_iota_comp_coproductZlcIso_inv j, Functor.mapIso_inv]
      simp only [Category.assoc]
      rw [← Functor.map_comp, ofHom_lsingle_eq_spn j, spn_comp, he j]
    rw [hstd, Category.assoc, ← Functor.map_comp, spn_comp_smul, ← hβ, Functor.map_comp,
      ← Category.assoc, hCmp]
  -- convert to the `toPointEquiv`-inverse of the constant function
  have hX : Sigma.ι (fun _ : Work.ANALYTIC.Haar.JIdx => 𝟙_ LightCondAb) j ≫ Θ.inv
      = (Work.ATOM.toPointEquiv (lcF.obj (ModuleCat.of ℤ (Work.ANALYTIC.Haar.LC T)))).symm
        (LocallyConstant.const ↥(Work.ATOM.pt.toTop) (Work.ANALYTIC.Haar.fJ T j) :
          ↥((lcF.obj (ModuleCat.of ℤ (Work.ANALYTIC.Haar.LC T))).obj.obj (op Work.ATOM.pt))) := by
    rw [hcomp, ← toPointEquiv_symm_const]
  rw [hX]
  exact Equiv.apply_symm_apply _ _

end Main

/-- **`Cdisc T ≅ ∐_{j : JIdx} ℤ`, compatibly with the Haar/Schauder basis.**  The `j`-th
coproduct inclusion is the global section of `Cdisc T` whose class in `C(T,ℤ) = LC T` is the
basis vector `Haar.fJ T j`. -/
theorem cdisc_coproduct_basis (T : LightProfinite.{0}) [Infinite T] :
    ∃ Θ : Work.ANALYTIC.Cdisc T ≅
        ∐ (fun _ : Work.ANALYTIC.Haar.JIdx => Work.ANALYTIC.Z),
      ∀ j : Work.ANALYTIC.Haar.JIdx,
        Work.ATOM.toPointEquiv (Work.ANALYTIC.Cdisc T)
          (CategoryTheory.CategoryStruct.comp
            (CategoryTheory.Limits.Sigma.ι
              (fun _ : Work.ANALYTIC.Haar.JIdx => Work.ANALYTIC.Z) j) Θ.inv) =
        LocallyConstant.const ↥(Work.ATOM.pt.toTop) (Work.ANALYTIC.Haar.fJ T j) := by
  have h := cdisc_coproduct_basis_aux T
  simpa only [Work.ANALYTIC.unit_eq_Z] using h

end Work.ANALYTIC.CechPt
