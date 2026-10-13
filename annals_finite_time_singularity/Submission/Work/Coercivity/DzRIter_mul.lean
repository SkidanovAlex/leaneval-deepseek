import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.InnerProductSpace.Basic
import Submission.Work.Coercivity.CTDefs
import Submission.Work.Spaces.DerivLikeBasic
import Submission.Work.Spaces.DerivLikeDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open Set Filter

namespace Work.Coercivity

set_option maxHeartbeats 1000000

/-! ## `D_z = z ∂_z` as a derivation on the `C^∞` functions of `(0,∞)`

The operator `DzR R = fun z => z * deriv R z` is a derivation for the pointwise
product, so its iterates obey the binomial (Leibniz) rule.  The combinatorial
part of that induction (the Pascal reindexing and the induction itself) is the
general `Work.Spaces.DerivLike.iterate_mul`; here we only have to observe that
`DzR` is `DerivLike` for the class of functions `C^∞` on `(0,∞)`, and that
`DzRIter` is the corresponding iterate. -/

/-- The class of functions of `z` alone that are `C^∞` on `(0,∞)`. -/
def SmoothIoi0 (A : ℝ → ℝ) : Prop := ContDiffOn ℝ ⊤ A (Set.Ioi 0)

/-- `SmoothIoi0` is closed under `+`, `*` and scalar multiples. -/
theorem SmoothIoi0_FunClass : Spaces.FunClass SmoothIoi0 where
  add := fun A B hA hB => hA.add hB
  mul := fun A B hA hB => hA.mul hB
  smul := fun c A hA => by
    show ContDiffOn ℝ ⊤ (fun p => c * A p) (Set.Ioi 0)
    exact ContDiffOn.const_smul c hA

/-- **`D_z = z ∂_z` is a derivation-like operator** on the `C^∞` functions of `(0,∞)`. -/
theorem DzR_DerivLike : Spaces.DerivLike (Set.Ioi 0) SmoothIoi0 CT.DzR where
  add := fun A B hA hB => by
    intro z hz
    have hA' : DifferentiableAt ℝ A z :=
      (hA.contDiffAt (isOpen_Ioi.mem_nhds hz)).differentiableAt (by norm_num)
    have hB' : DifferentiableAt ℝ B z :=
      (hB.contDiffAt (isOpen_Ioi.mem_nhds hz)).differentiableAt (by norm_num)
    show CT.DzR (A + B) z = CT.DzR A z + CT.DzR B z
    simp only [CT.DzR]
    rw [deriv_add hA' hB']
    ring
  mul := fun A B hA hB => by
    intro z hz
    have hA' : DifferentiableAt ℝ A z :=
      (hA.contDiffAt (isOpen_Ioi.mem_nhds hz)).differentiableAt (by norm_num)
    have hB' : DifferentiableAt ℝ B z :=
      (hB.contDiffAt (isOpen_Ioi.mem_nhds hz)).differentiableAt (by norm_num)
    show CT.DzR (A * B) z = CT.DzR A z * B z + A z * CT.DzR B z
    simp only [CT.DzR]
    rw [deriv_mul hA' hB']
    ring
  congr := fun A B h => by
    intro z hz
    show CT.DzR A z = CT.DzR B z
    simp only [CT.DzR]
    rw [h.deriv isOpen_Ioi hz]
  preserve := fun A hA => by
    have hfd : ContDiffOn ℝ ⊤ (fderiv ℝ A) (Set.Ioi 0) :=
      hA.fderiv_of_isOpen isOpen_Ioi (by simp)
    have hev : ContDiffOn ℝ ⊤ (fun z : ℝ => (fderiv ℝ A z) 1) (Set.Ioi 0) :=
      hfd.clm_apply contDiffOn_const
    have hfun : ContDiffOn ℝ ⊤ (fun z : ℝ => z * (fderiv ℝ A z) 1) (Set.Ioi 0) :=
      (contDiff_id.contDiffOn).mul hev
    refine hfun.congr (fun z hz => ?_)
    show CT.DzR A z = z * (fderiv ℝ A z) 1
    simp only [CT.DzR]
    rw [fderiv_apply_one_eq_deriv]
  smul := fun c A hA => by
    intro z hz
    have hA' : DifferentiableAt ℝ A z :=
      (hA.contDiffAt (isOpen_Ioi.mem_nhds hz)).differentiableAt (by norm_num)
    show CT.DzR (fun p => c * A p) z = c * CT.DzR A z
    simp only [CT.DzR]
    rw [deriv_const_mul c hA']
    ring

/-- `DzRIter j` is the `j`-fold iterate of `DzR`. -/
theorem DzRIter_eq_iterate (j : ℕ) (R : ℝ → ℝ) :
    CT.DzRIter j R = CT.DzR^[j] R := by
  induction j with
  | zero => rfl
  | succ n ih =>
      rw [CT.DzRIter_succ, ih, Function.iterate_succ_apply']

theorem DzRIter_mul (j : ℕ) (R S : ℝ → ℝ)
    (hR : ContDiffOn ℝ ⊤ R (Set.Ioi 0)) (hS : ContDiffOn ℝ ⊤ S (Set.Ioi 0)) :
    ∀ z : ℝ, 0 < z → Work.Coercivity.CT.DzRIter j (fun t => R t * S t) z
      = ∑ k ∈ Finset.range (j + 1),
          ((j.choose k : ℝ) * Work.Coercivity.CT.DzRIter k R z
            * Work.Coercivity.CT.DzRIter (j - k) S z) := by
  intro z hz
  have h := Spaces.DerivLike.iterate_mul (s := Set.Ioi 0) (P := SmoothIoi0)
    DzR_DerivLike SmoothIoi0_FunClass j hR hS hz
  have hbridge : (fun t : ℝ => R t * S t) = R * S := by funext t; rfl
  rw [hbridge, DzRIter_eq_iterate j (R * S), h]
  apply Finset.sum_congr rfl
  intro k _
  rw [DzRIter_eq_iterate k R, DzRIter_eq_iterate (j - k) S]
  ring

end Work.Coercivity

