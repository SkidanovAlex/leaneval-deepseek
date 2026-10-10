import Mathlib
import ChallengeDeps
import Submission.Work.MotT.Defs
import Submission.Work.MotT.TKSetup
import Submission.Work.MotT.functionField_baseChange_map
import Submission.Work.MotT.coeffAlgEquiv
import Submission.Work.MotT.fixedField_descent_finite
import Submission.Work.MotT.isField_functionField_tensor
import Submission.Work.MotT.isGalois_adjoin_root5
import Submission.Work.MotT.twistField_generate
import Submission.Work.MotT.twistFieldTK_sup_eq_top
import Submission.Work.MotT.tensorProduct_algEquiv_of_linearDisjoint
import Submission.Work.MotT.tensorProduct_algEquiv_of_linearDisjointL
import Submission.Work.MotC.adjoin_genX_genY_eq_top
import Submission.Work.MotV.Defs
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 800000
set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Work.MotT

noncomputable section

open WeierstrassCurve WeierstrassCurve.Affine
open scoped TensorProduct

variable {K : Type} [Field K]

/-! ## §1 The base change map `ι : L(E) → K̄(E)` -/

section Iota

/-- The base change map `L(E) → K̄(E)` induced by the inclusion `L ⊆ K̄`
(`functionField_baseChange_map`). -/
def iota (D : Work.MotV.KleinData K) (h : K) (hk : ringChar K ≠ 5) : ML D h hk →ₐ[K] OmK D :=
  Classical.choose (functionField_baseChange_map K D.E ↥(KummerField K h hk) (KbK K)
    (IsScalarTower.toAlgHom K ↥(KummerField K h hk) (KbK K)))

theorem iota_spec (D : Work.MotV.KleinData K) (h : K) (hk : ringChar K ≠ 5) :
    (∀ l : ↥(KummerField K h hk),
        iota D h hk (algebraMap ↥(KummerField K h hk) (ML D h hk) l) =
          algebraMap (KbK K) (OmK D) l) ∧
      iota D h hk (Work.MotV.genX (D.E.baseChange ↥(KummerField K h hk))) =
        Work.MotV.genX (D.E.baseChange (KbK K)) ∧
      iota D h hk (Work.MotV.genY (D.E.baseChange ↥(KummerField K h hk))) =
        Work.MotV.genY (D.E.baseChange (KbK K)) ∧
      Function.Injective (iota D h hk) := by
  have h := Classical.choose_spec (functionField_baseChange_map K D.E ↥(KummerField K h hk) (KbK K)
    (IsScalarTower.toAlgHom K ↥(KummerField K h hk) (KbK K)))
  exact ⟨fun l => h.1 l, h.2.1, h.2.2.1,
    h.2.2.2 (fun a b hab => Subtype.ext hab)⟩

theorem iota_algebraMap (D : Work.MotV.KleinData K) (h : K) (hk : ringChar K ≠ 5)
    (l : ↥(KummerField K h hk)) :
    iota D h hk (algebraMap ↥(KummerField K h hk) (ML D h hk) l) = algebraMap (KbK K) (OmK D) l :=
  (iota_spec D h hk).1 l

theorem iota_genX (D : Work.MotV.KleinData K) (h : K) (hk : ringChar K ≠ 5) :
    iota D h hk (Work.MotV.genX (D.E.baseChange ↥(KummerField K h hk))) =
      Work.MotV.genX (D.E.baseChange (KbK K)) := (iota_spec D h hk).2.1

theorem iota_genY (D : Work.MotV.KleinData K) (h : K) (hk : ringChar K ≠ 5) :
    iota D h hk (Work.MotV.genY (D.E.baseChange ↥(KummerField K h hk))) =
      Work.MotV.genY (D.E.baseChange (KbK K)) := (iota_spec D h hk).2.2.1

theorem iota_injective (D : Work.MotV.KleinData K) (h : K) (hk : ringChar K ≠ 5) :
    Function.Injective (iota D h hk) := (iota_spec D h hk).2.2.2

/-- The base change map sends the Klein coordinates over `L` to those over `K̄`. -/
theorem iota_kleinCoord (D : Work.MotV.KleinData K) (h : K) (hk : ringChar K ≠ 5) (i : Fin 5) :
    iota D h hk (Work.MotV.kleinCoord D ↥(KummerField K h hk) i) =
      Work.MotV.kleinCoord D (KbK K) i := by
  rw [Work.MotV.kleinCoord_eq_sum, Work.MotV.kleinCoord_eq_sum]
  simp only [map_sum, map_mul]
  refine Finset.sum_congr rfl fun m _ => ?_
  congr 1
  · rw [iota_algebraMap]
    exact (IsScalarTower.algebraMap_apply K ↥(KummerField K h hk) (OmK D) (D.coord i m)).symm
  · rw [Work.MotV.kleinBas, Work.MotV.kleinBas]
    fin_cases m <;>
      simp only [Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.head_cons, Matrix.tail_cons,
        Fin.isValue, Fin.succ_zero_eq_one, Fin.reduceFinMk, Matrix.cons_val_fin_one]
    · simp
    · exact iota_genX D h hk
    · exact iota_genY D h hk
    · simp [iota_genX D h hk]
    · simp [iota_genX D h hk, iota_genY D h hk]

/-- The base change map sends the twisted coordinates of `M = L(E)` to those of `K̄(E)`. -/
theorem iota_yM (D : Work.MotV.KleinData K) (h : K) (hk : ringChar K ≠ 5) (i : Fin 5) :
    iota D h hk (yM D h hk i) = twCoordK D h i := by
  rw [yM, twCoordK, wK]
  simp only [map_mul, map_inv₀, map_pow, map_div₀]
  rw [iota_algebraMap, iota_kleinCoord, iota_kleinCoord]
  rfl

end Iota

/-! ## §2 The twisted action of `Aut_K(L)` on `M = L(E)` -/

section Twisted

/-- The automorphism of `M = L(E)` given by `Good.T_diag`. -/
def sigma (D : Work.MotV.KleinData K) (hD : D.Good) (h : K) (hh : h ≠ 0)
    (hk : ringChar K ≠ 5) : ML D h hk ≃ₐ[↥(KummerField K h hk)] ML D h hk :=
  Classical.choose (hD.T_diag ↥(KummerField K h hk) (zL K h hk) (zL_isPrimitiveRoot K h hk))

theorem sigma_kleinCoord (D : Work.MotV.KleinData K) (hD : D.Good) (h : K) (hh : h ≠ 0)
    (hk : ringChar K ≠ 5) (i : Fin 5) :
    sigma D hD h hh hk (Work.MotV.kleinCoord D ↥(KummerField K h hk) i /
        Work.MotV.kleinCoord D ↥(KummerField K h hk) 0) =
      (algebraMap ↥(KummerField K h hk) (ML D h hk) (zL K h hk)) ^ (i : ℕ) *
        (Work.MotV.kleinCoord D ↥(KummerField K h hk) i /
          Work.MotV.kleinCoord D ↥(KummerField K h hk) 0) :=
  Classical.choose_spec
    (hD.T_diag ↥(KummerField K h hk) (zL K h hk) (zL_isPrimitiveRoot K h hk)) i

/-- `sigma`, restricted to `K`-algebras, acts diagonally on the Klein coordinates. -/
theorem sigmaRestrict_kleinCoord (D : Work.MotV.KleinData K) (hD : D.Good) (h : K) (hh : h ≠ 0)
    (hk : ringChar K ≠ 5) (i : Fin 5) :
    (sigma D hD h hh hk).restrictScalars K
        (Work.MotV.kleinCoord D ↥(KummerField K h hk) i /
          Work.MotV.kleinCoord D ↥(KummerField K h hk) 0) =
      (algebraMap ↥(KummerField K h hk) (ML D h hk) (zL K h hk)) ^ (i : ℕ) *
        (Work.MotV.kleinCoord D ↥(KummerField K h hk) i /
          Work.MotV.kleinCoord D ↥(KummerField K h hk) 0) :=
  sigma_kleinCoord D hD h hh hk i

theorem sigmaK_commutes (D : Work.MotV.KleinData K) (hD : D.Good) (h : K) (hh : h ≠ 0)
    (hk : ringChar K ≠ 5) (l : ↥(KummerField K h hk)) :
    (sigma D hD h hh hk).restrictScalars K
        (algebraMap ↥(KummerField K h hk) (ML D h hk) l) =
      algebraMap ↥(KummerField K h hk) (ML D h hk) l :=
  (sigma D hD h hh hk).commutes l

/-- The coefficient action of `γ ∈ Aut_K(L)` on `M = L(E)`. -/
def coeffAut (D : Work.MotV.KleinData K) (hD : D.Good) (h : K) (hh : h ≠ 0)
    (hk : ringChar K ≠ 5) (γ : ↥(KummerField K h hk) ≃ₐ[K] ↥(KummerField K h hk)) :
    ML D h hk ≃ₐ[K] ML D h hk :=
  Classical.choose (coeffAlgEquiv K D.E ↥(KummerField K h hk) γ)

theorem coeffAut_spec (D : Work.MotV.KleinData K) (hD : D.Good) (h : K) (hh : h ≠ 0)
    (hk : ringChar K ≠ 5) (γ : ↥(KummerField K h hk) ≃ₐ[K] ↥(KummerField K h hk)) :
    (∀ l : ↥(KummerField K h hk),
        coeffAut D hD h hh hk γ (algebraMap ↥(KummerField K h hk) (ML D h hk) l) =
          algebraMap ↥(KummerField K h hk) (ML D h hk) (γ l)) ∧
      coeffAut D hD h hh hk γ (Work.MotV.genX (D.E.baseChange ↥(KummerField K h hk))) =
        Work.MotV.genX (D.E.baseChange ↥(KummerField K h hk)) ∧
      coeffAut D hD h hh hk γ (Work.MotV.genY (D.E.baseChange ↥(KummerField K h hk))) =
        Work.MotV.genY (D.E.baseChange ↥(KummerField K h hk)) :=
  Classical.choose_spec (coeffAlgEquiv K D.E ↥(KummerField K h hk) γ)

theorem coeffAut_kleinBas (D : Work.MotV.KleinData K) (hD : D.Good) (h : K) (hh : h ≠ 0)
    (hk : ringChar K ≠ 5) (γ : ↥(KummerField K h hk) ≃ₐ[K] ↥(KummerField K h hk)) (m : Fin 5) :
    coeffAut D hD h hh hk γ (Work.MotV.kleinBas D ↥(KummerField K h hk) m) =
      Work.MotV.kleinBas D ↥(KummerField K h hk) m := by
  rw [Work.MotV.kleinBas]
  fin_cases m <;>
    simp only [Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.head_cons, Matrix.tail_cons,
      Fin.isValue, Fin.succ_zero_eq_one, Fin.reduceFinMk, Matrix.cons_val_fin_one]
  · simp
  · exact (coeffAut_spec D hD h hh hk γ).2.1
  · exact (coeffAut_spec D hD h hh hk γ).2.2
  · simp [(coeffAut_spec D hD h hh hk γ).2.1]
  · simp [(coeffAut_spec D hD h hh hk γ).2.1, (coeffAut_spec D hD h hh hk γ).2.2]

theorem coeffAut_kleinCoord (D : Work.MotV.KleinData K) (hD : D.Good) (h : K) (hh : h ≠ 0)
    (hk : ringChar K ≠ 5) (γ : ↥(KummerField K h hk) ≃ₐ[K] ↥(KummerField K h hk)) (i : Fin 5) :
    coeffAut D hD h hh hk γ (Work.MotV.kleinCoord D ↥(KummerField K h hk) i) =
      Work.MotV.kleinCoord D ↥(KummerField K h hk) i := by
  conv_lhs => rw [Work.MotV.kleinCoord_eq_sum]
  conv_rhs => rw [Work.MotV.kleinCoord_eq_sum]
  simp only [map_sum, map_mul]
  refine Finset.sum_congr rfl fun m _ => ?_
  congr 1
  · rw [(coeffAut_spec D hD h hh hk γ).1, γ.commutes (D.coord i m)]
  · exact coeffAut_kleinBas D hD h hh hk γ m

theorem coeffAut_yM (D : Work.MotV.KleinData K) (hD : D.Good) (h : K) (hh : h ≠ 0)
    (hk : ringChar K ≠ 5) (γ : ↥(KummerField K h hk) ≃ₐ[K] ↥(KummerField K h hk)) (i : Fin 5) :
    coeffAut D hD h hh hk γ (yM D h hk i) =
      (algebraMap ↥(KummerField K h hk) (ML D h hk) (γ (wL K h hk)))⁻¹ ^ (i : ℕ) *
        (Work.MotV.kleinCoord D ↥(KummerField K h hk) i /
          Work.MotV.kleinCoord D ↥(KummerField K h hk) 0) := by
  rw [yM]
  simp only [map_mul, map_inv₀, map_pow, map_div₀]
  rw [(coeffAut_spec D hD h hh hk γ).1]
  simp only [coeffAut_kleinCoord D hD h hh hk γ]

/-- `c(γ) = γ(w)/w`, the Kummer cocycle of the twist. -/
def cK (D : Work.MotV.KleinData K) (hD : D.Good) (h : K) (hh : h ≠ 0) (hk : ringChar K ≠ 5)
    (γ : ↥(KummerField K h hk) ≃ₐ[K] ↥(KummerField K h hk)) : ↥(KummerField K h hk) :=
  γ (wL K h hk) / wL K h hk

theorem cK_pow_five (D : Work.MotV.KleinData K) (hD : D.Good) (h : K) (hh : h ≠ 0)
    (hk : ringChar K ≠ 5) (γ : ↥(KummerField K h hk) ≃ₐ[K] ↥(KummerField K h hk)) :
    (cK D hD h hh hk γ) ^ 5 = 1 := by
  have hne : algebraMap K ↥(KummerField K h hk) h ≠ 0 := fun h0 =>
    hh ((algebraMap K ↥(KummerField K h hk)).injective (by rw [h0, map_zero]))
  have hγ : (γ (wL K h hk)) ^ 5 = algebraMap K ↥(KummerField K h hk) h := by
    rw [← map_pow, wL_pow_five]
    exact γ.commutes h
  rw [cK, div_pow, hγ, wL_pow_five, div_self hne]

/-- The exponent `m` with `ζ ^ m = c(γ)`. -/
def mK (D : Work.MotV.KleinData K) (hD : D.Good) (h : K) (hh : h ≠ 0) (hk : ringChar K ≠ 5)
    (γ : ↥(KummerField K h hk) ≃ₐ[K] ↥(KummerField K h hk)) : ℕ :=
  Classical.choose
    (IsPrimitiveRoot.eq_pow_of_pow_eq_one (zL_isPrimitiveRoot K h hk) (cK_pow_five D hD h hh hk γ))

theorem zL_pow_mK (D : Work.MotV.KleinData K) (hD : D.Good) (h : K) (hh : h ≠ 0)
    (hk : ringChar K ≠ 5) (γ : ↥(KummerField K h hk) ≃ₐ[K] ↥(KummerField K h hk)) :
    (zL K h hk) ^ (mK D hD h hh hk γ) = cK D hD h hh hk γ :=
  (Classical.choose_spec
    (IsPrimitiveRoot.eq_pow_of_pow_eq_one (zL_isPrimitiveRoot K h hk) (cK_pow_five D hD h hh hk γ))).2

/-- **The twisted action** `γ ↦ τ_{c(γ)} ∘ γ̃` of `Aut_K(L)` on `M = L(E)`. -/
def rhoFun (D : Work.MotV.KleinData K) (hD : D.Good) (h : K) (hh : h ≠ 0) (hk : ringChar K ≠ 5)
    (γ : ↥(KummerField K h hk) ≃ₐ[K] ↥(KummerField K h hk)) :
    ML D h hk ≃ₐ[K] ML D h hk :=
  (sigma D hD h hh hk).restrictScalars K ^ (mK D hD h hh hk γ) * coeffAut D hD h hh hk γ

theorem sigma_pow_algebraMap (D : Work.MotV.KleinData K) (hD : D.Good) (h : K) (hh : h ≠ 0)
    (hk : ringChar K ≠ 5) (m : ℕ) (l : ↥(KummerField K h hk)) :
    ((sigma D hD h hh hk).restrictScalars K ^ m)
        (algebraMap ↥(KummerField K h hk) (ML D h hk) l) =
      algebraMap ↥(KummerField K h hk) (ML D h hk) l := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ, AlgEquiv.mul_apply, sigmaK_commutes D hD h hh hk l, ih]

theorem sigma_pow_ratio (D : Work.MotV.KleinData K) (hD : D.Good) (h : K) (hh : h ≠ 0)
    (hk : ringChar K ≠ 5) (m : ℕ) (i : Fin 5) :
    ((sigma D hD h hh hk).restrictScalars K ^ m)
        (Work.MotV.kleinCoord D ↥(KummerField K h hk) i /
          Work.MotV.kleinCoord D ↥(KummerField K h hk) 0) =
      (algebraMap ↥(KummerField K h hk) (ML D h hk) (zL K h hk)) ^ ((i : ℕ) * m) *
        (Work.MotV.kleinCoord D ↥(KummerField K h hk) i /
          Work.MotV.kleinCoord D ↥(KummerField K h hk) 0) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ, AlgEquiv.mul_apply, sigmaRestrict_kleinCoord D hD h hh hk i]
    simp only [map_mul, map_pow]
    rw [sigma_pow_algebraMap D hD h hh hk m (zL K h hk), ih]
    rw [show (i : ℕ) * (m + 1) = (i : ℕ) * m + (i : ℕ) by ring, pow_add]
    refl_ring1

theorem rhoFun_algebraMap (D : Work.MotV.KleinData K) (hD : D.Good) (h : K) (hh : h ≠ 0)
    (hk : ringChar K ≠ 5) (γ : ↥(KummerField K h hk) ≃ₐ[K] ↥(KummerField K h hk))
    (l : ↥(KummerField K h hk)) :
    rhoFun D hD h hh hk γ (algebraMap ↥(KummerField K h hk) (ML D h hk) l) =
      algebraMap ↥(KummerField K h hk) (ML D h hk) (γ l) := by
  rw [rhoFun, AlgEquiv.mul_apply, (coeffAut_spec D hD h hh hk γ).1]
  exact sigma_pow_algebraMap D hD h hh hk _ _

theorem rhoFun_yM (D : Work.MotV.KleinData K) (hD : D.Good) (h : K) (hh : h ≠ 0)
    (hk : ringChar K ≠ 5) (γ : ↥(KummerField K h hk) ≃ₐ[K] ↥(KummerField K h hk)) (i : Fin 5) :
    rhoFun D hD h hh hk γ (yM D h hk i) = yM D h hk i := by
  have hwL0 : wL K h hk ≠ 0 := by
    intro h0
    have h5 : (wL K h hk) ^ 5 = 0 := by rw [h0]; exact zero_pow (by norm_num)
    rw [wL_pow_five] at h5
    exact hh ((algebraMap K ↥(KummerField K h hk)).injective (by rw [h5, map_zero]))
  have hne : algebraMap ↥(KummerField K h hk) (ML D h hk) (γ (wL K h hk)) ≠ 0 := by
    intro h0
    have h1 : γ (wL K h hk) = 0 := (algebraMap _ _).injective (by rw [h0, map_zero])
    have h2 : wL K h hk = 0 := by
      have hh2 := congrArg (fun z => γ.symm z) h1
      rwa [AlgEquiv.symm_apply_apply, map_zero] at hh2
    exact hwL0 h2
  have hAi : (algebraMap ↥(KummerField K h hk) (ML D h hk) (γ (wL K h hk))) ^ (i : ℕ) ≠ 0 :=
    pow_ne_zero _ hne
  rw [rhoFun, AlgEquiv.mul_apply, coeffAut_yM, yM]
  simp only [map_mul, map_pow, map_inv₀]
  have hzm : (algebraMap ↥(KummerField K h hk) (ML D h hk) (zL K h hk)) ^
        ((i : ℕ) * mK D hD h hh hk γ) =
      (algebraMap ↥(KummerField K h hk) (ML D h hk) (cK D hD h hh hk γ)) ^ (i : ℕ) := by
    rw [mul_comm ((i : ℕ)) (mK D hD h hh hk γ), pow_mul, ← map_pow, zL_pow_mK]
  rw [sigma_pow_algebraMap, sigma_pow_ratio, hzm, cK, map_div₀, div_pow]
  simp only [inv_pow, div_eq_mul_inv]
  rw [mul_assoc, ← mul_assoc, inv_mul_cancel₀ hAi, one_mul]

end Twisted

/-! ## §3 Uniqueness of `K`-algebra automorphisms of `M = L(y_i)` -/

section Uniqueness

/-- The field range of `K → L` inside `M` is the field generated by the image of `L`. -/
theorem fieldRange_eq_adjoin (D : Work.MotV.KleinData K) (hD : D.Good) (h : K) (hh : h ≠ 0)
    (hk : ringChar K ≠ 5) :
    (IsScalarTower.toAlgHom K ↥(KummerField K h hk) (ML D h hk)).fieldRange =
      IntermediateField.adjoin K
        (Set.range (algebraMap ↥(KummerField K h hk) (ML D h hk))) := by
  refine le_antisymm ?_ ?_
  · intro x hx
    rw [AlgHom.mem_fieldRange] at hx
    obtain ⟨l, rfl⟩ := hx
    exact IntermediateField.subset_adjoin K _ ⟨l, (IsScalarTower.toAlgHom_apply K _ _ l).symm⟩
  · rw [IntermediateField.adjoin_le_iff]
    rintro x ⟨l, rfl⟩
    exact AlgHom.mem_fieldRange.mpr ⟨l, rfl⟩

theorem adjoin_union_eq_sup (D : Work.MotV.KleinData K) (hD : D.Good) (h : K) (hh : h ≠ 0)
    (hk : ringChar K ≠ 5) (S T : Set (ML D h hk)) :
    IntermediateField.adjoin K (S ∪ T) =
      IntermediateField.adjoin K S ⊔ IntermediateField.adjoin K T := by
  refine le_antisymm ?_ ?_
  · rw [IntermediateField.adjoin_le_iff]
    rintro x (hx | hx)
    · exact (le_sup_left : IntermediateField.adjoin K S ≤ _) (IntermediateField.subset_adjoin K _ hx)
    · exact (le_sup_right : IntermediateField.adjoin K T ≤ _) (IntermediateField.subset_adjoin K _ hx)
  · refine sup_le ?_ ?_
    · rw [IntermediateField.adjoin_le_iff]
      intro x hx
      exact IntermediateField.subset_adjoin K _ (Or.inl hx)
    · rw [IntermediateField.adjoin_le_iff]
      intro x hx
      exact IntermediateField.subset_adjoin K _ (Or.inr hx)

/-- `M = L(y_i)`: the twisted coordinates together with the constants generate `M`. -/
theorem hgen (D : Work.MotV.KleinData K) (hD : D.Good) (h : K) (hh : h ≠ 0)
    (hk : ringChar K ≠ 5) :
    IntermediateField.adjoin K
        (Set.range (algebraMap ↥(KummerField K h hk) (ML D h hk)) ∪
          Set.range (yM D h hk)) = ⊤ := by
  have hg := twistField_generate (D := D) (hD := hD) (h := h) (hh := hh) (wL K h hk)
    (wL_pow_five K h hk)
  rw [show (fun i : Fin 5 =>
        (algebraMap ↥(KummerField K h hk) (ML D h hk) (wL K h hk))⁻¹ ^ (i : ℕ) *
          (Work.MotV.kleinCoord D ↥(KummerField K h hk) i /
            Work.MotV.kleinCoord D ↥(KummerField K h hk) 0)) = yM D h hk from rfl] at hg
  rw [adjoin_union_eq_sup D hD h hh hk, ← fieldRange_eq_adjoin D hD h hh hk, sup_comm]
  exact hg

/-- An element fixed by a `K`-algebra automorphism `w` of `M` which fixes a set `S` generates a
fixed field. -/
theorem le_fixedField_zpowers (D : Work.MotV.KleinData K) (hD : D.Good) (h : K) (hh : h ≠ 0)
    (hk : ringChar K ≠ 5) (w : ML D h hk ≃ₐ[K] ML D h hk) {S : Set (ML D h hk)}
    (hS : ∀ s ∈ S, w s = s) :
    IntermediateField.adjoin K S ≤ IntermediateField.fixedField (Subgroup.zpowers w) := by
  rw [IntermediateField.adjoin_le_iff]
  intro s hs
  refine (IntermediateField.mem_fixedField_iff _ s).mpr ?_
  intro f hf
  have hstab : Subgroup.zpowers w ≤ MulAction.stabilizer (ML D h hk ≃ₐ[K] ML D h hk) s :=
    Subgroup.zpowers_le.mpr ((MulAction.mem_stabilizer_iff).mpr (by simpa using hS s hs))
  simpa using (MulAction.mem_stabilizer_iff).mp (hstab hf)

/-- Two `K`-algebra automorphisms of `M` agreeing on the constants `L` and on the twisted
coordinates are equal. -/
theorem algEquiv_ext (D : Work.MotV.KleinData K) (hD : D.Good) (h : K) (hh : h ≠ 0)
    (hk : ringChar K ≠ 5) (f g : ML D h hk ≃ₐ[K] ML D h hk)
    (hL : ∀ l : ↥(KummerField K h hk),
      f (algebraMap ↥(KummerField K h hk) (ML D h hk) l) =
        g (algebraMap ↥(KummerField K h hk) (ML D h hk) l))
    (hy : ∀ i, f (yM D h hk i) = g (yM D h hk i)) : f = g := by
  have hS : ∀ s ∈ (Set.range (algebraMap ↥(KummerField K h hk) (ML D h hk)) ∪
      Set.range (yM D h hk)), (g⁻¹ * f) s = s := by
    rintro s (⟨l, rfl⟩ | ⟨i, rfl⟩)
    · rw [AlgEquiv.mul_apply, hL l]
      exact AlgEquiv.symm_apply_apply g _
    · rw [AlgEquiv.mul_apply, hy i]
      exact AlgEquiv.symm_apply_apply g _
  have htop := le_fixedField_zpowers D hD h hh hk (g⁻¹ * f) hS
  rw [hgen D hD h hh hk] at htop
  ext x
  have hx : (g⁻¹ * f) x = x :=
    (IntermediateField.mem_fixedField_iff _ x).mp (htop trivial) _ (Subgroup.mem_zpowers (g⁻¹ * f))
  calc f x = g (g⁻¹ (f x)) := (AlgEquiv.apply_symm_apply g (f x)).symm
    _ = g ((g⁻¹ * f) x) := by rw [AlgEquiv.mul_apply]
    _ = g x := by rw [hx]

theorem rhoFun_one (D : Work.MotV.KleinData K) (hD : D.Good) (h : K) (hh : h ≠ 0)
    (hk : ringChar K ≠ 5) : rhoFun D hD h hh hk 1 = 1 := by
  refine algEquiv_ext D hD h hh hk _ _ (fun l => ?_) (fun i => ?_)
  · rw [rhoFun_algebraMap]
    simp
  · rw [rhoFun_yM]
    simp

theorem rhoFun_mul (D : Work.MotV.KleinData K) (hD : D.Good) (h : K) (hh : h ≠ 0)
    (hk : ringChar K ≠ 5) (γ δ : ↥(KummerField K h hk) ≃ₐ[K] ↥(KummerField K h hk)) :
    rhoFun D hD h hh hk (γ * δ) = rhoFun D hD h hh hk γ * rhoFun D hD h hh hk δ := by
  refine algEquiv_ext D hD h hh hk _ _ (fun l => ?_) (fun i => ?_)
  · rw [AlgEquiv.mul_apply, rhoFun_algebraMap, rhoFun_algebraMap, rhoFun_algebraMap,
      AlgEquiv.mul_apply]
  · rw [AlgEquiv.mul_apply, rhoFun_yM, rhoFun_yM, rhoFun_yM]

/-- The twisted action as a group homomorphism. -/
def rho (D : Work.MotV.KleinData K) (hD : D.Good) (h : K) (hh : h ≠ 0) (hk : ringChar K ≠ 5) :
    ↥(⊤ : Subgroup (↥(KummerField K h hk) ≃ₐ[K] ↥(KummerField K h hk))) →*
      (ML D h hk ≃ₐ[K] ML D h hk) where
  toFun γ := rhoFun D hD h hh hk (γ : ↥(KummerField K h hk) ≃ₐ[K] ↥(KummerField K h hk))
  map_one' := rhoFun_one D hD h hh hk
  map_mul' γ δ := rhoFun_mul D hD h hh hk _ _

end Uniqueness

/-! ## §4 The descent and the main theorem -/

section Descent

theorem hfix (D : Work.MotV.KleinData K) (hD : D.Good) (h : K) (hh : h ≠ 0)
    (hk : ringChar K ≠ 5) : ∀ l : ↥(KummerField K h hk),
    (∀ γ : ↥(KummerField K h hk) ≃ₐ[K] ↥(KummerField K h hk), γ l = l) →
    ∃ c : K, algebraMap K ↥(KummerField K h hk) c = l := by
  haveI : FiniteDimensional K ↥(KummerField K h hk) :=
    (isGalois_adjoin_root5 K hk h hh (zeta5K K hk) (zeta5K_isPrimitiveRoot K hk)).1
  haveI : IsGalois K ↥(KummerField K h hk) :=
    (isGalois_adjoin_root5 K hk h hh (zeta5K K hk) (zeta5K_isPrimitiveRoot K hk)).2
  intro l hl
  refine IntermediateField.mem_bot.mp ((IsGalois.mem_bot_iff_fixed l).mpr ?_)
  intro f
  exact hl f

theorem fixedField_descent_rho (D : Work.MotV.KleinData K) (hD : D.Good) (h : K) (hh : h ≠ 0)
    (hk : ringChar K ≠ 5) :
    (IntermediateField.fixedField (rho D hD h hh hk).range).LinearDisjoint
        ↥(KummerField K h hk) ∧
      IntermediateField.fixedField (rho D hD h hh hk).range ⊔
        (IsScalarTower.toAlgHom K ↥(KummerField K h hk) (ML D h hk)).fieldRange = ⊤ := by
  haveI : FiniteDimensional K ↥(KummerField K h hk) :=
    (isGalois_adjoin_root5 K hk h hh (zeta5K K hk) (zeta5K_isPrimitiveRoot K hk)).1
  haveI : Fintype ↥(⊤ : Subgroup (↥(KummerField K h hk) ≃ₐ[K] ↥(KummerField K h hk))) :=
    Fintype.ofEquiv (↥(KummerField K h hk) ≃ₐ[K] ↥(KummerField K h hk))
      (Subgroup.topEquiv (G := ↥(KummerField K h hk) ≃ₐ[K] ↥(KummerField K h hk))).symm.toEquiv
  exact fixedField_descent_finite (𝕜 := K) (L := ↥(KummerField K h hk)) (M := ML D h hk)
    (⊤ : Subgroup (↥(KummerField K h hk) ≃ₐ[K] ↥(KummerField K h hk)))
    (fun l hl => hfix D hD h hh hk l (fun γ => hl ⟨γ, Subgroup.mem_top γ⟩))
    (rho D hD h hh hk)
    (fun γ l => rhoFun_algebraMap D hD h hh hk
      (γ : ↥(KummerField K h hk) ≃ₐ[K] ↥(KummerField K h hk)) l)

theorem AM_le_fixedField (D : Work.MotV.KleinData K) (hD : D.Good) (h : K) (hh : h ≠ 0)
    (hk : ringChar K ≠ 5) :
    AM D h hk ≤ IntermediateField.fixedField (rho D hD h hh hk).range := by
  rw [AM, IntermediateField.adjoin_le_iff]
  rintro x ⟨i, rfl⟩
  refine (IntermediateField.mem_fixedField_iff _ _).mpr ?_
  intro f hf
  obtain ⟨γ, rfl⟩ := MonoidHom.mem_range.mp hf
  exact rhoFun_yM D hD h hh hk (γ : ↥(KummerField K h hk) ≃ₐ[K] ↥(KummerField K h hk)) i
theorem AM_linearDisjoint (D : Work.MotV.KleinData K) (hD : D.Good) (h : K) (hh : h ≠ 0)
    (hk : ringChar K ≠ 5) : (AM D h hk).LinearDisjoint ↥(KummerField K h hk) :=
  IntermediateField.LinearDisjoint.of_le_left (fixedField_descent_rho D hD h hh hk).1
    (AM_le_fixedField D hD h hh hk)

end Descent

/-! ## §5 The isomorphism `A_M ≃ₐ[K] F_h` -/

section Iso

theorem map_AM_le (D : Work.MotV.KleinData K) (h : K) (hk : ringChar K ≠ 5) :
    (AM D h hk).map (iota D h hk) ≤ twistFieldTK D h := by
  rw [AM, IntermediateField.map_le_iff_le_comap, IntermediateField.adjoin_le_iff]
  rintro x ⟨i, rfl⟩
  show iota D h hk (yM D h hk i) ∈ twistFieldTK D h
  rw [iota_yM]
  exact IntermediateField.subset_adjoin K _ ⟨i, rfl⟩

theorem twistFieldTK_le_map_AM (D : Work.MotV.KleinData K) (h : K) (hk : ringChar K ≠ 5) :
    twistFieldTK D h ≤ (AM D h hk).map (iota D h hk) := by
  rw [twistFieldTK, IntermediateField.adjoin_le_iff]
  rintro x ⟨i, rfl⟩
  rw [AM, ← iota_yM D h hk i]
  exact ⟨yM D h hk i, IntermediateField.subset_adjoin K _ ⟨i, rfl⟩, rfl⟩

theorem map_AM (D : Work.MotV.KleinData K) (h : K) (hk : ringChar K ≠ 5) :
    (AM D h hk).map (iota D h hk) = twistFieldTK D h :=
  le_antisymm (map_AM_le D h hk) (twistFieldTK_le_map_AM D h hk)

/-- The `K`-algebra homomorphism `A_M → F_h` induced by `ι`. -/
def AMtoFh (D : Work.MotV.KleinData K) (h : K) (hk : ringChar K ≠ 5) :
    ↥(AM D h hk) →ₐ[K] ↥(twistFieldTK D h) where
  toFun x := ⟨iota D h hk x, by rw [← map_AM D h hk]; exact ⟨x, x.2, rfl⟩⟩
  map_one' := by ext; simp
  map_mul' x y := by ext; simp
  map_zero' := by ext; simp
  map_add' x y := by ext; simp
  commutes' c := by ext; simp

theorem AMtoFh_injective (D : Work.MotV.KleinData K) (h : K) (hk : ringChar K ≠ 5) :
    Function.Injective (AMtoFh D h hk) := by
  intro x y hxy
  exact Subtype.ext (iota_injective D h hk (congrArg Subtype.val hxy))

theorem AMtoFh_surjective (D : Work.MotV.KleinData K) (h : K) (hk : ringChar K ≠ 5) :
    Function.Surjective (AMtoFh D h hk) := by
  intro y
  have hy : y.1 ∈ (AM D h hk).map (iota D h hk) := by rw [map_AM D h hk]; exact y.2
  obtain ⟨x, hx, hxy⟩ := (IntermediateField.mem_map (AM D h hk) (f := iota D h hk)).mp hy
  exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩

/-- The restricted isomorphism `A_M ≃ₐ[K] F_h` induced by `ι`. -/
def AMalgEquiv (D : Work.MotV.KleinData K) (h : K) (hk : ringChar K ≠ 5) :
    ↥(AM D h hk) ≃ₐ[K] ↥(twistFieldTK D h) :=
  AlgEquiv.ofBijective (AMtoFh D h hk) ⟨AMtoFh_injective D h hk, AMtoFh_surjective D h hk⟩

end Iso

/-- The main linear-disjointness statement, in the form used by the assembly: `A_M` is linearly
disjoint from `K̄` over `K`. -/
theorem AM_linearDisjoint_Kb (D : Work.MotV.KleinData K) (hD : D.Good) (h : K) (hh : h ≠ 0)
    (hk : ringChar K ≠ 5) :
    IsField (TensorProduct K ↥(AM D h hk) (KbK K)) := by
  haveI : IsScalarTower K ↥(KummerField K h hk) (KbK K) := inferInstance
  obtain ⟨eL⟩ := tensorProduct_algEquiv_of_linearDisjointL (A := AM D h hk)
    (↥(KummerField K h hk)) (AM_linearDisjoint D hD h hh hk)
    (twistField_generate (D := D) (hD := hD) (h := h) (hh := hh) (wL K h hk) (wL_pow_five K h hk))
  have hΔ : (D.E.baseChange ↥(KummerField K h hk)).Δ ≠ 0 := by
    rw [WeierstrassCurve.baseChange, WeierstrassCurve.map_Δ]
    intro h0
    exact (WeierstrassCurve.isElliptic_iff D.E).mp hD.elliptic |>.ne_zero
      ((algebraMap K ↥(KummerField K h hk)).injective (by rw [h0, map_zero]))
  have hM : IsField (TensorProduct ↥(KummerField K h hk) (ML D h hk) (KbK K)) :=
    isField_functionField_tensor ↥(KummerField K h hk) (KbK K)
      (D.E.baseChange ↥(KummerField K h hk)) hΔ
  letI : Semiring (TensorProduct ↥(KummerField K h hk)
      (TensorProduct K ↥(KummerField K h hk) ↥(AM D h hk)) (KbK K)) :=
    @Algebra.TensorProduct.instSemiring ↥(KummerField K h hk)
      (TensorProduct K ↥(KummerField K h hk) ↥(AM D h hk)) (KbK K) _ _ _ _ _
  letI : Semiring (TensorProduct ↥(KummerField K h hk) (KbK K)
      (TensorProduct K ↥(KummerField K h hk) ↥(AM D h hk))) :=
    @Algebra.TensorProduct.instSemiring ↥(KummerField K h hk) (KbK K)
      (TensorProduct K ↥(KummerField K h hk) ↥(AM D h hk)) _ _ _ _ _
  have hfieldD : IsField (TensorProduct ↥(KummerField K h hk)
      (TensorProduct K ↥(KummerField K h hk) ↥(AM D h hk)) (KbK K)) :=
    (Algebra.TensorProduct.congr eL
      (AlgEquiv.refl : (KbK K) ≃ₐ[↥(KummerField K h hk)] (KbK K))).toMulEquiv.isField hM
  have hfieldC : IsField (TensorProduct ↥(KummerField K h hk) (KbK K)
      (TensorProduct K ↥(KummerField K h hk) ↥(AM D h hk))) :=
    (Algebra.TensorProduct.comm ↥(KummerField K h hk)
      (TensorProduct K ↥(KummerField K h hk) ↥(AM D h hk)) (KbK K)).symm.toMulEquiv.isField
        hfieldD
  have hfieldB : IsField (TensorProduct K (KbK K) ↥(AM D h hk)) :=
    (Algebra.TensorProduct.cancelBaseChange K ↥(KummerField K h hk) ↥(KummerField K h hk)
      (KbK K) ↥(AM D h hk)).symm.toMulEquiv.isField hfieldC
  exact (Algebra.TensorProduct.comm K (KbK K) ↥(AM D h hk)).symm.toMulEquiv.isField hfieldB

/-- **T2 (`C1T`/REG over `K`, the hard node).** The T-twist field `F_h = K(C_h)` is a `K`-form of
`K̄(E)`: it is linearly disjoint from `K̄` over `K` and, together with `K̄`, generates `K̄(E)`.

Route (`MOTIVIC_C6_R4_LEAD.md` §3.3, T2a/T2b/T2c).
* `L := K(ζ, w) ⊆ K̄` with `w := Work.MotT.root5K h`; `L/K` is finite Galois because `char K ≠ 5`;
  `G := Gal(L/K)` and `c(γ) := γ w / w ∈ μ₅`.
* The twisted action `γ* := τ*_{c(γ)T} ∘ γ` on `L(E)` is a group action by `K`-automorphisms
  restricting to `γ` on `L`; `Work.MotV.KleinData.Good.T_diag` gives the diagonal action of the
  translation by the marked five-torsion point.  Its fixed field `Φ` is linearly disjoint from `L`
  and satisfies `Φ ⊔ L = L(E)` (Artin/Speiser for a finite group of semilinear automorphisms;
  generalise `Work.MotC.fixedField_descent`, which is the cyclic order-five case).
* `Work.MotT.twCoordK D h i` is `γ*`-invariant, so `F_h ⊆ Φ`; and `x, y ∈ L·F_h` by
  `Work.MotV.KleinData.Good.spans`, so `F_h ⊔ L = L(E)`; a degree comparison gives `F_h = Φ`.
* `L(E)` is linearly disjoint from `K̄` over `L` (from the base change `L[E] ⊗_L K̄ = K̄[E]` of the
  `AdjoinRoot` model, a domain); transitivity of linear disjointness gives the claim.

Declare it in namespace `Work.MotT` so that its full name is `Work.MotT.twistFieldTK_descent`. -/
theorem twistFieldTK_descent {K : Type} [Field K] (D : Work.MotV.KleinData K) (hD : D.Good)
    (hk : ringChar K ≠ 5) (h : K) (hh : h ≠ 0) :
    (Work.MotT.twistFieldTK D h).LinearDisjoint (Work.MotT.KbK K) ∧
      Work.MotT.twistFieldTK D h ⊔
        (IsScalarTower.toAlgHom K (Work.MotT.KbK K) (Work.MotT.OmK D)).fieldRange = ⊤ := by
  classical
  refine ⟨?_, twistFieldTK_sup_eq_top D hD h hh⟩
  have hfieldA : IsField (TensorProduct K ↥(twistFieldTK D h) (KbK K)) :=
    (Algebra.TensorProduct.congr (R := K) (S := K) (AMalgEquiv D h hk)
      (AlgEquiv.refl : (KbK K) ≃ₐ[K] (KbK K))).symm.toMulEquiv.isField
        (AM_linearDisjoint_Kb D hD h hh hk)
  exact IntermediateField.LinearDisjoint.of_isField hfieldA

end

end Work.MotT
