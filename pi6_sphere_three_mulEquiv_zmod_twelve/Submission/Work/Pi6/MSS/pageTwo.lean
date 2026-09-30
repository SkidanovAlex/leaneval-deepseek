import Mathlib
import Submission.Work.Pi6.MSS.PagesComp
import Submission.Work.Pi6.MSS.pagesData
import Submission.Work.Pi6.MSS.PageData
import Submission.Work.Pi6.MSS.convPage

/-!
# `E_2 = H(E_1)`

The page `E_2` of the spectral sequence of a filtered cochain complex with a product is the
homology of the `E_1` row complex: `E_2^{s,q} ≅ H^s(E_1^{•,q}, d_1)`, where
`E_1^{s,q} = pEraw 𝕜 W 1 s (q+s)` and `d_1 = pD 𝕜 W 1` is the differential of the pages.

The proof uses the projection `pd_proj 𝕜 W 1 s n : ker (d_1 : E_1^s → E_1^{s+1}) → E_2^s` of
`Submission/Work/Pi6/MSS/pagesData.lean` — surjective (in degree `s = s'+1` with kernel the image of
the incoming differential `d_1 : E_1^{s'} → E_1^{s'+1}`, and bijective in degree `0`, where there is
no incoming differential) — together with the concrete description of the homology of a cochain
complex of modules (`Work.Pi6.MSS.convHomologyLocal`).
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace Work.Pi6.MSS

open CategoryTheory CategoryTheory.Limits

noncomputable section

variable {𝕜 : Type} [Field 𝕜] {W : CohFilt 𝕜}

/-! ## 1. The projection `ker d_1 → E_2` -/

/-- The `r = 1` case of `pd_proj_surj` (the hypothesis `2 ≤ r` is not used in its proof). -/
theorem pageTwo_proj_surj_one (𝕜 : Type) [Field 𝕜] (W : CohFilt 𝕜) (s n : ℕ) :
    Function.Surjective (pd_proj 𝕜 W 1 s n) := by
  intro v
  obtain ⟨a, ha⟩ := pd_pFun_surj 𝕜 W 1 s n v
  exact ⟨pd_Phi 𝕜 W 1 s n a, by rw [pd_proj_eq_of 𝕜 W 1 s n a, ha]⟩

/-- The `r = 1` case of `pd_proj_ker`: the kernel of `ker d_1^{s'} → E_2^{s'+1}` is the image of the
incoming differential `d_1 : E_1^{s'} → E_1^{s'+1}`. -/
theorem pageTwo_proj_ker_one (𝕜 : Type) [Field 𝕜] (W : CohFilt 𝕜) (s' n' : ℕ)
    (x : ↥(LinearMap.ker (pD 𝕜 W 1 (s'+1) (n'+1)).hom)) :
    pd_proj 𝕜 W 1 (s'+1) (n'+1) x = 0 ↔ ∃ w : pEraw 𝕜 W 1 s' n',
      (pD 𝕜 W 1 s' n').hom w = (x : pEraw 𝕜 W 1 (s'+1) (n'+1)) := by
  set az := Function.surjInv (pd_Phi_surj 𝕜 W 1 (s'+1) (n'+1)) x with haz
  have hzx : pd_Phi 𝕜 W 1 (s'+1) (n'+1) az = x := Function.surjInv_eq _ x
  have hproj : pd_proj 𝕜 W 1 (s'+1) (n'+1) x
      = pd_pFun 𝕜 W 1 (s'+1) (n'+1) az := by
    rw [← hzx]
    exact pd_proj_eq_of 𝕜 W 1 (s'+1) (n'+1) az
  have hmain : (pd_pFun 𝕜 W 1 (s'+1) (n'+1) az = 0)
      ↔ az.1 ∈ pDen 𝕜 W 1 (s'+1) (n'+1) ⊔ (pZ 𝕜 W 1 s' n').map (W.d n') := by
    rw [pd_pFun_zero_iff 𝕜 W 1 (s'+1) (n'+1) az,
      pd_pDen_sup_pZmap (𝕜 := 𝕜) (W := W) (r := 1) (s' := s') (n' := n')]
  have hL : (pd_proj 𝕜 W 1 (s'+1) (n'+1) x = 0)
      ↔ (pd_pFun 𝕜 W 1 (s'+1) (n'+1) az = 0) := by rw [hproj]
  have hR : (∃ w : pEraw 𝕜 W 1 s' n',
        (pD 𝕜 W 1 s' n').hom w = (x : pEraw 𝕜 W 1 (s'+1) (n'+1)))
      ↔ (∃ w : pEraw 𝕜 W 1 s' n', (pD 𝕜 W 1 s' n').hom w
          = (pd_Phi 𝕜 W 1 (s'+1) (n'+1) az : pEraw 𝕜 W 1 (s'+1) (n'+1))) := by
    rw [show (x : pEraw 𝕜 W 1 (s'+1) (n'+1))
      = (pd_Phi 𝕜 W 1 (s'+1) (n'+1) az : pEraw 𝕜 W 1 (s'+1) (n'+1)) from by rw [hzx]]
  exact (hL.trans hmain).trans
    ((hR.trans (pd_Phi_mem_range_iff (𝕜 := 𝕜) (W := W) 1 s' n' az)).symm)

/-- The kernel of `ker d_1^{s'+1} → E_2^{s'+1}`, as a submodule of the cycles. -/
theorem pageTwo_proj_ker_one_eq (𝕜 : Type) [Field 𝕜] (W : CohFilt 𝕜) (s' n' : ℕ) :
    LinearMap.ker (pd_proj 𝕜 W 1 (s'+1) (n'+1))
      = Submodule.comap (LinearMap.ker (pD 𝕜 W 1 (s'+1) (n'+1)).hom).subtype
          (LinearMap.range (pD 𝕜 W 1 s' n').hom) := by
  ext x
  rw [LinearMap.mem_ker, Submodule.mem_comap, Submodule.subtype_apply, LinearMap.mem_range]
  exact pageTwo_proj_ker_one 𝕜 W s' n' x

/-! ## 2. The degree-zero case -/

/-- `B_2^0 = B_1^0` (both are `F^0 ∩ d(F^0)`: the two truncated indices agree). -/
theorem pageTwo_pB_two_zero (𝕜 : Type) [Field 𝕜] (W : CohFilt 𝕜) (n : ℕ) :
    pB 𝕜 W 2 0 n = pB 𝕜 W 1 0 n := rfl

/-- `D_2^0 ⊆ D_1^0`: the denominator of `E_2^0` is contained in the denominator of the cycles
of `d_1^0`. -/
theorem pageTwo_pDen_two_zero_le (𝕜 : Type) [Field 𝕜] (W : CohFilt 𝕜) (n : ℕ) :
    pDen 𝕜 W 2 0 n ≤ pDen 𝕜 W 1 0 n := by
  refine sup_le ?_ ?_
  · exact le_trans (pd_pZ_anti (𝕜 := 𝕜) (W := W) (r := 0) (r' := 1) (s := 1) (s' := 1)
      (by omega) le_rfl) le_sup_left
  · rw [pageTwo_pB_two_zero 𝕜 W n]
    exact le_sup_right

/-- If `pd_pFun 1 0 n` vanishes on `a`, then so does the class map `pd_Phi`. -/
theorem pageTwo_pFun_zero_imp_Phi_zero (𝕜 : Type) [Field 𝕜] (W : CohFilt 𝕜) (n : ℕ)
    (a : ↥(pd_K 𝕜 W 1 0 n)) (h : pd_pFun 𝕜 W 1 0 n a = 0) :
    pd_Phi 𝕜 W 1 0 n a = 0 := by
  have hmem : a.1 ∈ pDen 𝕜 W 1 0 n ⊔ pDen 𝕜 W 2 0 n :=
    (pd_pFun_zero_iff 𝕜 W 1 0 n a).mp h
  have hle : pDen 𝕜 W 1 0 n ⊔ pDen 𝕜 W 2 0 n ≤ pDen 𝕜 W 1 0 n :=
    sup_le le_rfl (pageTwo_pDen_two_zero_le 𝕜 W n)
  exact (pd_Phi_ker_iff 𝕜 W 1 0 n a).mpr (hle hmem)

/-- `ker d_1^0 → E_2^0` is injective (there is no incoming differential in degree `0`). -/
theorem pageTwo_proj_ker_zero (𝕜 : Type) [Field 𝕜] (W : CohFilt 𝕜) (n : ℕ) :
    LinearMap.ker (pd_proj 𝕜 W 1 0 n) = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro x hx
  rw [LinearMap.mem_ker] at hx
  set a := Function.surjInv (pd_Phi_surj 𝕜 W 1 0 n) x with haz
  have hPhi : pd_Phi 𝕜 W 1 0 n a = x := Function.surjInv_eq _ x
  have hp : pd_pFun 𝕜 W 1 0 n a = 0 := by
    rw [← pd_proj_eq_of 𝕜 W 1 0 n a, hPhi]
    exact hx
  have h0 : pd_Phi 𝕜 W 1 0 n a = 0 := pageTwo_pFun_zero_imp_Phi_zero 𝕜 W n a hp
  rw [← hPhi]
  exact h0

/-! ## 3. The two cases of the theorem -/

/-- `E_2^0 = H^0(E_1)`. -/
theorem pageTwo_zero (𝕜 : Type) [Field 𝕜] (W : CohFilt 𝕜) (q : ℕ) :
    Nonempty (pEraw 𝕜 W 2 0 (q + 0) ≅ (E1Row 𝕜 W q).homology 0) := by
  classical
  obtain ⟨e1⟩ := convHomologyLocal 𝕜 (E1Row 𝕜 W q) 0
  have hd1 : (E1Row 𝕜 W q).d 0 (0 + 1) = pD 𝕜 W 1 0 (q + 0) := E1Row_d 𝕜 W q 0
  have hd2 : (E1Row 𝕜 W q).d (0 - 1) 0 = 0 := by
    have h : (E1Row 𝕜 W q).d 0 0 = 0 :=
      HomologicalComplex.shape _ 0 0 (by simp only [ComplexShape.up_Rel]; omega)
    simpa using h
  -- the incoming differential at degree `0` is zero, so its image is trivial
  have hden : Submodule.comap
      (LinearMap.ker ((E1Row 𝕜 W q).d 0 (0+1)).hom).subtype
      (LinearMap.range ((E1Row 𝕜 W q).d (0-1) 0).hom) = ⊥ := by
    simp only [hd2, ModuleCat.hom_zero]
    erw [LinearMap.range_zero]
    rw [Submodule.comap_bot]
    exact Submodule.ker_subtype _
  rw [hden] at e1
  have e1' : (E1Row 𝕜 W q).homology 0 ≃ₗ[𝕜]
      ↥(LinearMap.ker ((E1Row 𝕜 W q).d 0 (0+1)).hom) :=
    e1.trans (Submodule.quotEquivOfEqBot ⊥ rfl)
  have hker : LinearMap.ker ((E1Row 𝕜 W q).d 0 (0+1)).hom
      = LinearMap.ker (pD 𝕜 W 1 0 (q + 0)).hom := by
    rw [hd1]
    rfl
  have hf : Function.Bijective (pd_proj 𝕜 W 1 0 (q + 0)) :=
    ⟨LinearMap.ker_eq_bot.mp (pageTwo_proj_ker_zero 𝕜 W (q + 0)),
      pageTwo_proj_surj_one 𝕜 W 0 (q + 0)⟩
  refine ⟨LinearEquiv.toModuleIso ?_⟩
  exact (LinearEquiv.ofBijective _ hf).symm.trans
    ((LinearEquiv.ofEq (LinearMap.ker ((E1Row 𝕜 W q).d 0 (0+1)).hom)
      (LinearMap.ker (pD 𝕜 W 1 0 (q + 0)).hom) hker).trans e1'.symm)

/-- `E_2^{s'+1} = H^{s'+1}(E_1)`. -/
theorem pageTwo_succ (𝕜 : Type) [Field 𝕜] (W : CohFilt 𝕜) (q s' : ℕ) :
    Nonempty (pEraw 𝕜 W 2 (s'+1) (q + (s'+1)) ≅ (E1Row 𝕜 W q).homology (s'+1)) := by
  classical
  obtain ⟨e1⟩ := convHomologyLocal 𝕜 (E1Row 𝕜 W q) (s'+1)
  -- rewrite the two differentials of `E_1` appearing in the description of the homology
  have hd1 : (E1Row 𝕜 W q).d (s'+1) (s'+1+1) = pD 𝕜 W 1 (s'+1) (q + (s'+1)) :=
    E1Row_d 𝕜 W q (s'+1)
  have hd0 : (E1Row 𝕜 W q).d (s'+1-1) (s'+1) = pD 𝕜 W 1 s' (q + s') :=
    E1Row_d 𝕜 W q s'
  rw [hd1, hd0] at e1
  have hker := pageTwo_proj_ker_one_eq 𝕜 W s' (q + s')
  have e1' : (E1Row 𝕜 W q).homology (s'+1) ≃ₗ[𝕜]
      (↥(LinearMap.ker (pD 𝕜 W 1 (s'+1) (q + (s'+1))).hom) ⧸
        (LinearMap.ker (pd_proj 𝕜 W 1 (s'+1) (q + (s'+1))))) :=
    e1.trans (Submodule.quotEquivOfEq _ _ hker.symm)
  have g : (↥(LinearMap.ker (pD 𝕜 W 1 (s'+1) (q + (s'+1))).hom) ⧸
      (LinearMap.ker (pd_proj 𝕜 W 1 (s'+1) (q + (s'+1))))) ≃ₗ[𝕜]
      ↥(pEraw 𝕜 W 2 (s'+1) (q + (s'+1))) :=
    (pd_proj 𝕜 W 1 (s'+1) (q + (s'+1))).quotKerEquivOfSurjective
      (pageTwo_proj_surj_one 𝕜 W (s'+1) (q + (s'+1)))
  exact ⟨LinearEquiv.toModuleIso (g.symm.trans e1'.symm)⟩

end

theorem pageTwo (𝕜 : Type) [Field 𝕜] (W : Work.Pi6.MSS.CohFilt 𝕜) (q s : ℕ) :
    Nonempty (Work.Pi6.MSS.pEraw 𝕜 W 2 s (q + s) ≅
      (Work.Pi6.MSS.E1Row 𝕜 W q).homology s) := by
  cases s with
  | zero => exact pageTwo_zero 𝕜 W q
  | succ s' => exact pageTwo_succ 𝕜 W q s'

end Work.Pi6.MSS
