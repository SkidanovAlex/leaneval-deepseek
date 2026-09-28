import Mathlib
import Submission.Work.Cohomology.CompatTrans.prodSphereDefs
import Submission.Work.Cohomology.homotopyEquiv_prod_fst

namespace Work.Cohomology

open ContinuousMap

set_option linter.style.haveILetI false

noncomputable section

/-- The punctured sphere `Sᵖ⁺¹ \ {N_p}`. -/
def PunctP (p : ℕ) : Set ↥(sphSet (p+1)) := {x | x ≠ sphN p}

/-- The subset `{w : Sᵖ⁺¹ × Sᵠ⁺¹ | w.1 ≠ N_p}` of the product of spheres. -/
def A2set (p q : ℕ) : Set (↥(sphSet (p+1)) × ↥(sphSet (q+1))) := {w | w.1 ≠ sphN p}

/-- `↥(A1set p q)` is homeomorphic to `↥(A2set p q)`. -/
def homeo_A1_A2 (p q : ℕ) : ↥(A1set p q) ≃ₜ ↥(A2set p q) where
  toFun z := ⟨(z : ↥(Yset p q)), z.2⟩
  invFun w := ⟨⟨w.1, by intro h; exact w.2 (by simp [ptP, h])⟩, w.2⟩
  left_inv z := rfl
  right_inv w := rfl
  continuous_toFun :=
    Continuous.subtype_mk (continuous_subtype_val.comp continuous_subtype_val) (fun z => z.2)
  continuous_invFun :=
    Continuous.subtype_mk
      (Continuous.subtype_mk continuous_subtype_val
        (fun w => by intro h; exact w.2 (by simp [ptP, h])))
      (fun w => w.2)

/-- `↥(A2set p q)` is homeomorphic to the product of the punctured sphere with the sphere. -/
def homeo_A2_prod (p q : ℕ) :
    ↥(A2set p q) ≃ₜ ↥(PunctP p) × ↥(sphSet (q+1)) :=
  (Homeomorph.setCongr (by ext w; simp [A2set, PunctP])).trans
    ((Homeomorph.Set.prod (PunctP p) (Set.univ : Set ↥(sphSet (q+1)))).trans
      ((Homeomorph.refl ↥(PunctP p)).prodCongr (Homeomorph.Set.univ ↥(sphSet (q+1)))))

theorem homotopyEquiv_A1set (p q : ℕ) :
    Nonempty (ContinuousMap.HomotopyEquiv ↥(A1set p q) ↥(sphSet (q+1))) := by
  haveI : ContractibleSpace ↥(PunctP p) := contractible_compl_sphN p
  exact ⟨((homeo_A1_A2 p q).trans (homeo_A2_prod p q)).toHomotopyEquiv.trans
    (((Homeomorph.prodComm ↥(PunctP p) ↥(sphSet (q+1))).toHomotopyEquiv).trans
      (homotopyEquiv_prod_fst ↥(sphSet (q+1)) ↥(PunctP p)).some)⟩

end

end Work.Cohomology
