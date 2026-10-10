import Mathlib
import Submission.Work.CY3Stab.Prod.exists_cInv_ne_zero_of_CY3Data
import Submission.Work.CY3Stab.LinkInput
import Submission.Work.CY3Stab.Main
import Submission.Work.CY3Stab.Prod.exDiv_prodMap_eq
import Submission.Work.CY3Stab.Prod.stablyBirational_of_resEquiv_cyl_of_p1Bundle
import Submission.Work.CY3Stab.Prod.resEquiv_prodPt_of_resEquiv
import Submission.Work.CY3Stab.Prod.cInv_prodMap_eq_zero_of_strong
import Submission.Work.CY3Stab.Prod.prodMap_isOver_pinned
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
/-- In namespace `Work.Wire123`, file `Submission.Work.Wire123.exists_cInv_ne_zero_of_CY3Data_sep.lean`. The stabilisation of the CY3 link to `Cr 𝕜 n`, `n ≥ 5`, with Totaro's input used in its per-pair form: this is `Work.CY3Stab.Prod.exists_cInv_ne_zero_of_CY3Data` with the universal named input `Work.CY3.TotaroInput 𝕜` (uninstantiable: it quantifies over all `𝕜`-varieties with fieldless hypotheses) and the non-isomorphism `¬ Work.CY3.IsoOver 𝕜 D.Z D.Z'` replaced by the single hypothesis that the two centres of `D` are not stably birational — the conclusion of Totaro's `cor-CYnSB` at the pair `(D.Z', D.Z)`.

The witness is the *symmetric walk* `γ⁻¹ ∘ ε ∘ Ψ ∘ S ∘ ε⁻¹ ∘ γ`: the coefficients of `ε = D.eps × id_{𝔸ᵏ}` and of its inverse are opposite to each other (`Work.LLink.cInv_eq_neg_symm`), the cylinder `S` of the strong birationality `G/P' ⤏ G/P` contributes nothing, the identification `γ : 𝔸ᵏ × 𝔸⁵ ⤏ 𝔸ⁿ` contributes nothing, and the cylinder of the link contributes `1` at the cylinder point over the exceptional divisor `D.y` (the paper's `c(φ × id_W) = [Z × ℙ¹ × W] − [Z' × ℙ¹ × W]`), where the only use of the hypothesis is the cancellation `Work.CY3Stab.Prod.stablyBirational_cyl_two` producing `Work.CY3.StablyBirational 𝕜 D.Z' D.Z` from the residue equivalence of the two cylinder points. -/
theorem exists_cInv_ne_zero_of_CY3Data_sep {n : ℕ} (hn : 5 ≤ n) (𝕜 : Type) [Field 𝕜]
    (D : Work.CY3.CY3Data 𝕜) (hsep : ¬ Work.CY3.StablyBirational 𝕜 D.Z' D.Z)
    (F : Work.CY3Stab.CY3P1Bundle 𝕜 D) :
    ∃ (Z : AlgebraicGeometry.Scheme.{0}) (_ : Z.Over (AlgebraicGeometry.Spec (CommRingCat.of 𝕜)))
      (z₀ : Z) (φ : MotivicInvariants.Cr 𝕜 n),
      _root_.cInv 𝕜 z₀ (φ : (Work.CY3.Affine 𝕜 n).BirationalMap (Work.CY3.Affine 𝕜 n)) ≠ 0 := by
  classical
  rw [show n = n - 5 + 5 from (Nat.sub_add_cancel hn).symm]
  set k := n - 5 with hk
  -- The `Over`-structures of the three cylinders as found by instance search, together with the
  -- `Variety`-structures whose `over` field is exactly that instance (the pinned `varietyWProd`
  -- has the `pullback.fst` flavour, which is only *propositionally* the same).
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
  -- `IsOver`-ness of the two transports and of the strong map (instances for the inverses)
  haveI hEpsSymmOver : (D.eps.symm).IsOver (AlgebraicGeometry.Spec (CommRingCat.of 𝕜)) :=
    inferInstanceAs (D.eps.inv.IsOver (AlgebraicGeometry.Spec (CommRingCat.of 𝕜)))
  haveI hPsiSymmOver : (D.psi.symm).IsOver (AlgebraicGeometry.Spec (CommRingCat.of 𝕜)) :=
    inferInstanceAs (D.psi.inv.IsOver (AlgebraicGeometry.Spec (CommRingCat.of 𝕜)))
  -- the cylinder points of the two exceptional divisors
  have hDx : ∀ x : D.P, IsDomain (Work.CY3Stab.cylTriplet (𝕜 := 𝕜) D.P x k).tensor :=
    fun x => Work.CY3Stab.Prod.isDomain_cylTriplet_tensor 𝕜 k D.P x
  have hDy : ∀ y : D.P', IsDomain (Work.CY3Stab.cylTriplet (𝕜 := 𝕜) D.P' y k).tensor :=
    fun y => Work.CY3Stab.Prod.isDomain_cylTriplet_tensor 𝕜 k D.P' y
  haveI hDxI : ∀ x : D.P, IsDomain (Work.CY3Stab.cylTriplet (𝕜 := 𝕜) D.P x k).tensor := hDx
  haveI hDyI : ∀ y : D.P', IsDomain (Work.CY3Stab.cylTriplet (𝕜 := 𝕜) D.P' y k).tensor := hDy
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
  -- the two exceptional divisors are distinguished (Totaro and the `ℙ¹`-bundle cancellation)
  have hcancel : ¬ ResEquiv 𝕜 (Work.CY3Stab.prodPt (𝕜 := 𝕜) D.P D.x k)
      (Work.CY3Stab.prodPt (𝕜 := 𝕜) D.P' D.y k) := fun hres =>
    hsep (Work.CY3Stab.Prod.stablyBirational_cyl_two k F.isP1Bundle_x F.isP1Bundle_y hres)
  -- the coefficient of the cylinder of the link at the cylinder point over `D.y`
  have hPsi : cInv 𝕜 (Work.CY3Stab.prodPt (𝕜 := 𝕜) D.P' D.y k)
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
  -- (L2) of the link: the cylinder of the strong birationality `G/P' ⤏ G/P` is strong
  have hStrong : @Work.CY3.StronglyBirational 𝕜 _
      (Work.CY3Stab.WProd (𝕜 := 𝕜) D.P' k) (Work.CY3Stab.WProd (𝕜 := 𝕜) D.P k)
      hVP' hVP := by
    obtain ⟨φ, hφover, hφ0⟩ :=
      (Work.CY3.G2Grassmannian.stronglyBirational D.toG2Grassmannian).symm
    refine ⟨Work.CY3Stab.prodMap (𝕜 := 𝕜) k φ, ?_, ?_⟩
    · exact Work.CY3Stab.Prod.prodMap_isOver_pinned k φ hccP' hccP
    · intro W _ w
      exact Work.CY3Stab.Prod.cInv_prodMap_eq_zero_of_strong k φ
        (Work.Motivic.exDiv_finite_of_variety 𝕜 φ)
        (Work.Motivic.exDiv_finite_of_variety 𝕜 φ.symm) hφ0 W w
  obtain ⟨S, hSover, hS0⟩ := hStrong
  -- the identification `𝔸ᵏ × 𝔸⁵ ≅ 𝔸^{k+5}`
  obtain ⟨γ, hγover, hγ0⟩ := Work.CY3Stab.Prod.stronglyBirational_wProd_affine 𝕜 k
  -- the `IsOver` instances of the transported maps
  haveI hγOver : γ.IsOver (AlgebraicGeometry.Spec (CommRingCat.of 𝕜)) := hγover
  haveI hSOver : S.IsOver (AlgebraicGeometry.Spec (CommRingCat.of 𝕜)) := hSover
  haveI hγsOver : (γ.symm).IsOver (AlgebraicGeometry.Spec (CommRingCat.of 𝕜)) :=
    inferInstanceAs (γ.inv.IsOver (AlgebraicGeometry.Spec (CommRingCat.of 𝕜)))
  haveI hEpsOver : (Work.CY3Stab.prodMap (𝕜 := 𝕜) k D.eps).IsOver
      (AlgebraicGeometry.Spec (CommRingCat.of 𝕜)) :=
    Work.CY3Stab.Prod.prodMap_isOver_pinned k D.eps (by rfl) hccP
  haveI hPsiOver : (Work.CY3Stab.prodMap (𝕜 := 𝕜) k D.psi).IsOver
      (AlgebraicGeometry.Spec (CommRingCat.of 𝕜)) :=
    Work.CY3Stab.Prod.prodMap_isOver_pinned k D.psi hccP hccP'
  haveI hEps'Over : (Work.CY3Stab.prodMap (𝕜 := 𝕜) k (D.eps.symm)).IsOver
      (AlgebraicGeometry.Spec (CommRingCat.of 𝕜)) :=
    Work.CY3Stab.Prod.prodMap_isOver_pinned k D.eps.symm hccP (by rfl)
  -- the composite factors of the walk
  let tail : (Work.CY3Stab.WProd (𝕜 := 𝕜) D.P' k).BirationalMap
      (Work.CY3.Affine 𝕜 (k + 5)) :=
    S.trans ((Work.CY3Stab.prodMap (𝕜 := 𝕜) k (D.eps.symm)).trans γ)
  haveI hTail1Over : ((Work.CY3Stab.prodMap (𝕜 := 𝕜) k (D.eps.symm)).trans γ).IsOver
      (AlgebraicGeometry.Spec (CommRingCat.of 𝕜)) :=
    Work.Motivic.pseudoReg_isOver_trans (Work.CY3Stab.prodMap (𝕜 := 𝕜) k (D.eps.symm)) γ
  haveI hTailOver : tail.IsOver (AlgebraicGeometry.Spec (CommRingCat.of 𝕜)) :=
    Work.Motivic.pseudoReg_isOver_trans S _
  haveI hTail2Over : ((Work.CY3Stab.prodMap (𝕜 := 𝕜) k D.psi).trans tail).IsOver
      (AlgebraicGeometry.Spec (CommRingCat.of 𝕜)) :=
    Work.Motivic.pseudoReg_isOver_trans (Work.CY3Stab.prodMap (𝕜 := 𝕜) k D.psi) tail
  haveI hTail3Over : ((Work.CY3Stab.prodMap (𝕜 := 𝕜) k D.eps).trans
      ((Work.CY3Stab.prodMap (𝕜 := 𝕜) k D.psi).trans tail)).IsOver
      (AlgebraicGeometry.Spec (CommRingCat.of 𝕜)) :=
    Work.Motivic.pseudoReg_isOver_trans (Work.CY3Stab.prodMap (𝕜 := 𝕜) k D.eps) _
  have hΦover : (γ.symm.trans ((Work.CY3Stab.prodMap (𝕜 := 𝕜) k D.eps).trans
      ((Work.CY3Stab.prodMap (𝕜 := 𝕜) k D.psi).trans tail))).IsOver
      (AlgebraicGeometry.Spec (CommRingCat.of 𝕜)) :=
    Work.Motivic.pseudoReg_isOver_trans γ.symm _
  -- the values of the five factors at the cylinder point of `D.y`
  have hγval : cInv 𝕜 (Work.CY3Stab.prodPt (𝕜 := 𝕜) D.P' D.y k) γ = 0 :=
    hγ0 (Work.CY3Stab.WProd (𝕜 := 𝕜) D.P' k) (Work.CY3Stab.prodPt (𝕜 := 𝕜) D.P' D.y k)
  have hSval : cInv 𝕜 (Work.CY3Stab.prodPt (𝕜 := 𝕜) D.P' D.y k) S = 0 :=
    hS0 (Work.CY3Stab.WProd (𝕜 := 𝕜) D.P' k) (Work.CY3Stab.prodPt (𝕜 := 𝕜) D.P' D.y k)
  have hγsval : cInv 𝕜 (Work.CY3Stab.prodPt (𝕜 := 𝕜) D.P' D.y k) γ.symm = 0 := by
    rw [Work.LLink.cInv_eq_neg_symm 𝕜 (Work.CY3Stab.prodPt (𝕜 := 𝕜) D.P' D.y k) γ, hγval]
    first | refl_ring1 | ring
  have hεsval : cInv 𝕜 (Work.CY3Stab.prodPt (𝕜 := 𝕜) D.P' D.y k)
        (Work.CY3Stab.prodMap (𝕜 := 𝕜) k (D.eps.symm)) =
      - cInv 𝕜 (Work.CY3Stab.prodPt (𝕜 := 𝕜) D.P' D.y k)
        (Work.CY3Stab.prodMap (𝕜 := 𝕜) k D.eps) := by
    rw [← Work.CY3Stab.Prod.prodMap_symm 𝕜 k D.eps]
    exact Work.LLink.cInv_eq_neg_symm 𝕜 (Work.CY3Stab.prodPt (𝕜 := 𝕜) D.P' D.y k)
      (Work.CY3Stab.prodMap (𝕜 := 𝕜) k D.eps)
  -- the coefficient of the walk
  have hcoeff : cInv 𝕜 (Work.CY3Stab.prodPt (𝕜 := 𝕜) D.P' D.y k)
      (γ.symm.trans ((Work.CY3Stab.prodMap (𝕜 := 𝕜) k D.eps).trans
        ((Work.CY3Stab.prodMap (𝕜 := 𝕜) k D.psi).trans tail))) = 1 := by
    show cInv 𝕜 (Work.CY3Stab.prodPt (𝕜 := 𝕜) D.P' D.y k)
      (γ.symm.trans ((Work.CY3Stab.prodMap (𝕜 := 𝕜) k D.eps).trans
        ((Work.CY3Stab.prodMap (𝕜 := 𝕜) k D.psi).trans
          (S.trans ((Work.CY3Stab.prodMap (𝕜 := 𝕜) k (D.eps.symm)).trans γ))))) = 1
    simp only [Work.Motivic.cInv_add]
    rw [hγsval, hγval, hSval, hεsval, hPsi]
    first | refl_ring1 | ring
  refine ⟨Work.CY3Stab.WProd (𝕜 := 𝕜) D.P' k, inferInstance,
    Work.CY3Stab.prodPt (𝕜 := 𝕜) D.P' D.y k,
    ⟨γ.symm.trans ((Work.CY3Stab.prodMap (𝕜 := 𝕜) k D.eps).trans
      ((Work.CY3Stab.prodMap (𝕜 := 𝕜) k D.psi).trans tail)), hΦover⟩, ?_⟩
  intro hzero
  rw [hcoeff] at hzero
  exact absurd hzero (by norm_num)

end

end Work.Wire123
