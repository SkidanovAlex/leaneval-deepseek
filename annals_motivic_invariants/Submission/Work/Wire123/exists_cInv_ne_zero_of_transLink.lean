import Mathlib
import Submission.Work.Wire123.TransLink
import Submission.Work.CrauderKatz.cInv_conj_eq
import Submission.Work.LLink.Count
import Submission.Work.CY3Stab.Main
import Submission.Work.CY3Stab.Prod.exDiv_prodMap_eq
import Submission.Work.CY3Stab.Prod.prodMap_symm
import Submission.Work.CY3Stab.Prod.cInv_prodMap_eq_zero_of_strong
import Submission.Work.CY3Stab.Prod.prodMap_isOver_pinned
import Submission.Work.CY3Stab.Prod.isDomain_cylTriplet_tensor
import Submission.Work.CY3Stab.Prod.stronglyBirational_wProd_affine
import Submission.Work.CY3Stab.Prod.stablyBirational_of_resEquiv_cyl_of_p1Bundle
import Submission.Work.Motivic.exDiv_finite_of_variety
import Submission.Work.Motivic.cInv_add
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1600000
attribute [instance] MotivicInvariants.Variety.over MotivicInvariants.Variety.isIntegral

namespace Work.Wire123

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
  MotivicInvariants Order

noncomputable section

theorem exists_cInv_ne_zero_of_transLink {n : ℕ} (hn : 5 ≤ n) (𝕜 : Type) [Field 𝕜]
    (D : Work.Wire123.TransLink 𝕜) :
    ∃ (Z : AlgebraicGeometry.Scheme.{0}) (_ : Z.Over (AlgebraicGeometry.Spec (CommRingCat.of 𝕜)))
      (z₀ : Z) (φ : MotivicInvariants.Cr 𝕜 n),
      _root_.cInv 𝕜 z₀ (φ : (Work.CY3.Affine 𝕜 n).BirationalMap (Work.CY3.Affine 𝕜 n)) ≠ 0 := by
  classical
  rw [show n = n - 5 + 5 from (Nat.sub_add_cancel hn).symm]
  set k := n - 5 with hk
  -- (L2) of the link: the strong birationality `γ : P ⇢ P'`
  obtain ⟨γ, hγover, hγ0⟩ := D.stronglyBirational
  haveI hγ : γ.IsOver (Spec (CommRingCat.of 𝕜)) := hγover
  haveI hγs : (γ.symm).IsOver (Spec (CommRingCat.of 𝕜)) :=
    inferInstanceAs (γ.inv.IsOver (Spec (CommRingCat.of 𝕜)))
  haveI hψs : (D.psi.symm).IsOver (Spec (CommRingCat.of 𝕜)) :=
    inferInstanceAs (D.psi.inv.IsOver (Spec (CommRingCat.of 𝕜)))
  haveI hιs : (D.iota.symm).IsOver (Spec (CommRingCat.of 𝕜)) :=
    inferInstanceAs (D.iota.inv.IsOver (Spec (CommRingCat.of 𝕜)))
  -- The `Over`-structures of the cylinders of `D.P`, `D.P'` found by instance search, together
  -- with the `Variety`-structures whose `over` field is exactly that instance.
  letI hCP : (Work.CY3Stab.WProd (𝕜 := 𝕜) D.P k).Over
      (AlgebraicGeometry.Spec (CommRingCat.of 𝕜)) :=
    inferInstanceAs ((Work.CY3Stab.WProd (𝕜 := 𝕜) D.P k).Over
      (AlgebraicGeometry.Spec (CommRingCat.of 𝕜)))
  letI hCP' : (Work.CY3Stab.WProd (𝕜 := 𝕜) D.P' k).Over
      (AlgebraicGeometry.Spec (CommRingCat.of 𝕜)) :=
    inferInstanceAs ((Work.CY3Stab.WProd (𝕜 := 𝕜) D.P' k).Over
      (AlgebraicGeometry.Spec (CommRingCat.of 𝕜)))
  have hccP : (CategoryTheory.over (Work.CY3Stab.WProd (𝕜 := 𝕜) D.P k)
        (AlgebraicGeometry.Spec (CommRingCat.of 𝕜))) =
      (Work.CY3Stab.wProdOver (𝕜 := 𝕜) D.P k).1 := by
    show (pullback.snd (Work.CY3Stab.AffineK (𝕜 := 𝕜) k ↘ Spec (CommRingCat.of 𝕜))
        (D.P ↘ Spec (CommRingCat.of 𝕜)) ≫ (D.P ↘ Spec (CommRingCat.of 𝕜))) =
      (pullback.fst (Work.CY3Stab.AffineK (𝕜 := 𝕜) k ↘ Spec (CommRingCat.of 𝕜))
        (D.P ↘ Spec (CommRingCat.of 𝕜)) ≫
          (Work.CY3Stab.AffineK (𝕜 := 𝕜) k ↘ Spec (CommRingCat.of 𝕜)))
    exact pullback.condition.symm
  have hccP' : (CategoryTheory.over (Work.CY3Stab.WProd (𝕜 := 𝕜) D.P' k)
        (AlgebraicGeometry.Spec (CommRingCat.of 𝕜))) =
      (Work.CY3Stab.wProdOver (𝕜 := 𝕜) D.P' k).1 := by
    show (pullback.snd (Work.CY3Stab.AffineK (𝕜 := 𝕜) k ↘ Spec (CommRingCat.of 𝕜))
        (D.P' ↘ Spec (CommRingCat.of 𝕜)) ≫ (D.P' ↘ Spec (CommRingCat.of 𝕜))) =
      (pullback.fst (Work.CY3Stab.AffineK (𝕜 := 𝕜) k ↘ Spec (CommRingCat.of 𝕜))
        (D.P' ↘ Spec (CommRingCat.of 𝕜)) ≫
          (Work.CY3Stab.AffineK (𝕜 := 𝕜) k ↘ Spec (CommRingCat.of 𝕜)))
    exact pullback.condition.symm
  letI hV5 : Variety 𝕜 (Work.CY3Stab.WProd (𝕜 := 𝕜) (Work.CY3.Affine 𝕜 5) k) :=
    Work.CY3Stab.varietyWProd (𝕜 := 𝕜) (Work.CY3.Affine 𝕜 5) k
  letI hVP : Variety 𝕜 (Work.CY3Stab.WProd (𝕜 := 𝕜) D.P k) :=
    { «over» := hCP
      isIntegral := (Work.CY3Stab.varietyWProd (𝕜 := 𝕜) D.P k).isIntegral
      isSeparated := hccP ▸ (Work.CY3Stab.varietyWProd (𝕜 := 𝕜) D.P k).isSeparated
      locallyOfFiniteType := hccP ▸ (Work.CY3Stab.varietyWProd (𝕜 := 𝕜) D.P k).locallyOfFiniteType
      quasicompact := hccP ▸ (Work.CY3Stab.varietyWProd (𝕜 := 𝕜) D.P k).quasicompact }
  letI hVP' : Variety 𝕜 (Work.CY3Stab.WProd (𝕜 := 𝕜) D.P' k) :=
    { «over» := hCP'
      isIntegral := (Work.CY3Stab.varietyWProd (𝕜 := 𝕜) D.P' k).isIntegral
      isSeparated := hccP' ▸ (Work.CY3Stab.varietyWProd (𝕜 := 𝕜) D.P' k).isSeparated
      locallyOfFiniteType := hccP' ▸ (Work.CY3Stab.varietyWProd (𝕜 := 𝕜) D.P' k).locallyOfFiniteType
      quasicompact := hccP' ▸ (Work.CY3Stab.varietyWProd (𝕜 := 𝕜) D.P' k).quasicompact }
  -- the cylinder points over the two exceptional divisors, and the `IsDomain` instances
  have hDx : ∀ x : D.P, IsDomain (Work.CY3Stab.cylTriplet (𝕜 := 𝕜) D.P x k).tensor :=
    fun x => Work.CY3Stab.Prod.isDomain_cylTriplet_tensor 𝕜 k D.P x
  have hDy : ∀ y : D.P', IsDomain (Work.CY3Stab.cylTriplet (𝕜 := 𝕜) D.P' y k).tensor :=
    fun y => Work.CY3Stab.Prod.isDomain_cylTriplet_tensor 𝕜 k D.P' y
  haveI hDxI : ∀ x : D.P, IsDomain (Work.CY3Stab.cylTriplet (𝕜 := 𝕜) D.P x k).tensor := hDx
  haveI hDyI : ∀ y : D.P', IsDomain (Work.CY3Stab.cylTriplet (𝕜 := 𝕜) D.P' y k).tensor := hDy
  -- `IsOver`-instances of the three product maps
  haveI hψkOver : (Work.CY3Stab.prodMap (𝕜 := 𝕜) k D.psi).IsOver
      (Spec (CommRingCat.of 𝕜)) :=
    Work.CY3Stab.Prod.prodMap_isOver_pinned k D.psi hccP hccP'
  haveI hψkOverS : ((Work.CY3Stab.prodMap (𝕜 := 𝕜) k D.psi).symm).IsOver
      (Spec (CommRingCat.of 𝕜)) :=
    inferInstanceAs ((Work.CY3Stab.prodMap (𝕜 := 𝕜) k D.psi).inv.IsOver (Spec (CommRingCat.of 𝕜)))
  haveI hγkOver : (Work.CY3Stab.prodMap (𝕜 := 𝕜) k γ).IsOver
      (Spec (CommRingCat.of 𝕜)) :=
    Work.CY3Stab.Prod.prodMap_isOver_pinned k γ hccP hccP'
  haveI hγkOverS : ((Work.CY3Stab.prodMap (𝕜 := 𝕜) k γ).symm).IsOver
      (Spec (CommRingCat.of 𝕜)) :=
    inferInstanceAs ((Work.CY3Stab.prodMap (𝕜 := 𝕜) k γ).inv.IsOver (Spec (CommRingCat.of 𝕜)))
  haveI hιkOver : (Work.CY3Stab.prodMap (𝕜 := 𝕜) k D.iota).IsOver
      (Spec (CommRingCat.of 𝕜)) :=
    Work.CY3Stab.Prod.prodMap_isOver_pinned k D.iota rfl hccP
  haveI hιkOverS : ((Work.CY3Stab.prodMap (𝕜 := 𝕜) k D.iota).symm).IsOver
      (Spec (CommRingCat.of 𝕜)) :=
    inferInstanceAs ((Work.CY3Stab.prodMap (𝕜 := 𝕜) k D.iota).inv.IsOver (Spec (CommRingCat.of 𝕜)))
  -- the `exDiv` of the cylinder of the link and of its inverse
  have hexi : exDiv (Work.CY3Stab.prodMap (𝕜 := 𝕜) k D.psi) =
      {Work.CY3Stab.prodPt (𝕜 := 𝕜) D.P D.x k} := by
    rw [Work.CY3Stab.Prod.exDiv_prodMap_eq 𝕜 k D.psi, D.exDiv_psi]
    simp
  have hexi' : exDiv ((Work.CY3Stab.prodMap (𝕜 := 𝕜) k D.psi).symm) =
      {Work.CY3Stab.prodPt (𝕜 := 𝕜) D.P' D.y k} := by
    rw [Work.CY3Stab.Prod.prodMap_symm 𝕜 k D.psi,
      Work.CY3Stab.Prod.exDiv_prodMap_eq 𝕜 k D.psi.symm, D.exDiv_psi_symm]
    simp
  -- the two cylinder points are distinguished (Totaro + the `ℙ¹`-bundle cancellation)
  have hcancel : ¬ ResEquiv 𝕜 (Work.CY3Stab.prodPt (𝕜 := 𝕜) D.P D.x k)
      (Work.CY3Stab.prodPt (𝕜 := 𝕜) D.P' D.y k) := fun hres =>
    D.not_stablyBirat
      (Work.CY3Stab.Prod.stablyBirational_cyl_two k D.p1Bundle_x D.p1Bundle_y hres)
  -- the cylinder of the link contributes `1` at the cylinder point over `D.y`
  have hψval : cInv 𝕜 (Work.CY3Stab.prodPt (𝕜 := 𝕜) D.P' D.y k)
      (Work.CY3Stab.prodMap (𝕜 := 𝕜) k D.psi) = 1 := by
    unfold cInv
    rw [Work.LLink.excCount_eq_one_of_exDiv_eq_singleton
        (Work.CY3Stab.prodPt (𝕜 := 𝕜) D.P' D.y k)
        (Work.CY3Stab.prodMap (𝕜 := 𝕜) k D.psi).symm hexi'
        (Work.Motivic.ResEquiv.refl 𝕜 _),
      Work.LLink.excCount_eq_zero_of_exDiv_eq_singleton
        (Work.CY3Stab.prodPt (𝕜 := 𝕜) D.P' D.y k)
        (Work.CY3Stab.prodMap (𝕜 := 𝕜) k D.psi) hexi hcancel]
    norm_num
  -- the cylinder of the strong birationality contributes nothing
  have hγkval : cInv 𝕜 (Work.CY3Stab.prodPt (𝕜 := 𝕜) D.P' D.y k)
      (Work.CY3Stab.prodMap (𝕜 := 𝕜) k γ) = 0 :=
    Work.CY3Stab.Prod.cInv_prodMap_eq_zero_of_strong (𝕜 := 𝕜) k γ
      (Work.Motivic.exDiv_finite_of_variety 𝕜 γ)
      (Work.Motivic.exDiv_finite_of_variety 𝕜 γ.symm) hγ0
      (Work.CY3Stab.WProd (𝕜 := 𝕜) D.P' k)
      (Work.CY3Stab.prodPt (𝕜 := 𝕜) D.P' D.y k)
  have hγksval : cInv 𝕜 (Work.CY3Stab.prodPt (𝕜 := 𝕜) D.P' D.y k)
      ((Work.CY3Stab.prodMap (𝕜 := 𝕜) k γ).symm) = 0 := by
    rw [Work.LLink.cInv_eq_neg_symm (𝕜 := 𝕜)
      (Work.CY3Stab.prodPt (𝕜 := 𝕜) D.P' D.y k) (Work.CY3Stab.prodMap (𝕜 := 𝕜) k γ),
      hγkval]
    first | refl_ring1 | ring
  -- the self-map `ΦR = ψ_k ∘ γ_k⁻¹` of the cylinder `𝔸ᵏ × P`
  let ΦR : (Work.CY3Stab.WProd (𝕜 := 𝕜) D.P k).BirationalMap
      (Work.CY3Stab.WProd (𝕜 := 𝕜) D.P k) :=
    (Work.CY3Stab.prodMap (𝕜 := 𝕜) k D.psi).trans (Work.CY3Stab.prodMap (𝕜 := 𝕜) k γ).symm
  haveI hΦRover : ΦR.IsOver (Spec (CommRingCat.of 𝕜)) :=
    Work.Motivic.pseudoReg_isOver_trans (Work.CY3Stab.prodMap (𝕜 := 𝕜) k D.psi)
      (Work.CY3Stab.prodMap (𝕜 := 𝕜) k γ).symm
  have hΦRval : cInv 𝕜 (Work.CY3Stab.prodPt (𝕜 := 𝕜) D.P' D.y k) ΦR = 1 := by
    show cInv 𝕜 _ ((Work.CY3Stab.prodMap (𝕜 := 𝕜) k D.psi).trans
      (Work.CY3Stab.prodMap (𝕜 := 𝕜) k γ).symm) = 1
    rw [Work.Motivic.cInv_add (𝕜 := 𝕜)
      (X := Work.CY3Stab.WProd (𝕜 := 𝕜) D.P k)
      (Y := Work.CY3Stab.WProd (𝕜 := 𝕜) D.P' k)
      (Z := Work.CY3Stab.WProd (𝕜 := 𝕜) D.P k)
      (Work.CY3Stab.prodPt (𝕜 := 𝕜) D.P' D.y k)
      (Work.CY3Stab.prodMap (𝕜 := 𝕜) k D.psi)
      (Work.CY3Stab.prodMap (𝕜 := 𝕜) k γ).symm, hψval, hγksval]
    norm_num
  -- the self-map `ΦQ = ι_k ∘ ΦR ∘ ι_k⁻¹` of the cylinder `𝔸ᵏ × 𝔸⁵`
  let ΦQ : (Work.CY3Stab.WProd (𝕜 := 𝕜) (Work.CY3.Affine 𝕜 5) k).BirationalMap
      (Work.CY3Stab.WProd (𝕜 := 𝕜) (Work.CY3.Affine 𝕜 5) k) :=
    (Work.CY3Stab.prodMap (𝕜 := 𝕜) k D.iota).trans
      (ΦR.trans (Work.CY3Stab.prodMap (𝕜 := 𝕜) k D.iota).symm)
  haveI hΦQtailOver : (ΦR.trans (Work.CY3Stab.prodMap (𝕜 := 𝕜) k D.iota).symm).IsOver
      (Spec (CommRingCat.of 𝕜)) :=
    Work.Motivic.pseudoReg_isOver_trans ΦR (Work.CY3Stab.prodMap (𝕜 := 𝕜) k D.iota).symm
  haveI hΦQover : ΦQ.IsOver (Spec (CommRingCat.of 𝕜)) :=
    Work.Motivic.pseudoReg_isOver_trans (Work.CY3Stab.prodMap (𝕜 := 𝕜) k D.iota)
      (ΦR.trans (Work.CY3Stab.prodMap (𝕜 := 𝕜) k D.iota).symm)
  have hΦQval : cInv 𝕜 (Work.CY3Stab.prodPt (𝕜 := 𝕜) D.P' D.y k) ΦQ = 1 := by
    show cInv 𝕜 _ ((Work.CY3Stab.prodMap (𝕜 := 𝕜) k D.iota).trans
      (ΦR.trans (Work.CY3Stab.prodMap (𝕜 := 𝕜) k D.iota).symm)) = 1
    rw [Work.CrauderKatz.cInv_conj_eq (𝕜 := 𝕜)
      (S := Work.CY3Stab.WProd (𝕜 := 𝕜) (Work.CY3.Affine 𝕜 5) k)
      (T := Work.CY3Stab.WProd (𝕜 := 𝕜) D.P k)
      (Work.CY3Stab.prodPt (𝕜 := 𝕜) D.P' D.y k)
      (Work.CY3Stab.prodMap (𝕜 := 𝕜) k D.iota) ΦR, hΦRval]
  -- the identification `𝔸ᵏ × 𝔸⁵ ≅ 𝔸ⁿ` as a strong birationality
  obtain ⟨γA, hγAover, hγA0⟩ :=
    Work.CY3Stab.Prod.stronglyBirational_wProd_affine 𝕜 k
  haveI hγA : γA.IsOver (Spec (CommRingCat.of 𝕜)) := hγAover
  haveI hγAs : (γA.symm).IsOver (Spec (CommRingCat.of 𝕜)) :=
    inferInstanceAs (γA.inv.IsOver (Spec (CommRingCat.of 𝕜)))
  -- the transported Cremona transformation of `𝔸ⁿ`
  haveI hΦQγAOver : (ΦQ.trans γA).IsOver (Spec (CommRingCat.of 𝕜)) :=
    Work.Motivic.pseudoReg_isOver_trans ΦQ γA
  let Ψ : (Work.CY3.Affine 𝕜 (k + 5)).BirationalMap (Work.CY3.Affine 𝕜 (k + 5)) :=
    γA.symm.trans (ΦQ.trans γA)
  haveI hΨover : Ψ.IsOver (Spec (CommRingCat.of 𝕜)) :=
    Work.Motivic.pseudoReg_isOver_trans γA.symm (ΦQ.trans γA)
  have hΨval : cInv 𝕜 (Work.CY3Stab.prodPt (𝕜 := 𝕜) D.P' D.y k) Ψ = 1 := by
    have h := Work.CrauderKatz.cInv_conj_eq (𝕜 := 𝕜)
      (S := Work.CY3.Affine 𝕜 (k + 5))
      (T := Work.CY3Stab.WProd (𝕜 := 𝕜) (Work.CY3.Affine 𝕜 5) k)
      (Work.CY3Stab.prodPt (𝕜 := 𝕜) D.P' D.y k) γA.symm ΦQ
    rw [Work.LLink.birationalMap_symm_symm γA] at h
    show cInv 𝕜 (Work.CY3Stab.prodPt (𝕜 := 𝕜) D.P' D.y k) Ψ = 1
    rw [show Ψ = γA.symm.trans (ΦQ.trans γA) from rfl, h, hΦQval]
  refine ⟨Work.CY3Stab.WProd (𝕜 := 𝕜) D.P' k, hCP',
    Work.CY3Stab.prodPt (𝕜 := 𝕜) D.P' D.y k, ⟨Ψ, hΨover⟩, ?_⟩
  intro hzero
  rw [hΨval] at hzero
  exact absurd hzero (by norm_num)

end

end Work.Wire123
