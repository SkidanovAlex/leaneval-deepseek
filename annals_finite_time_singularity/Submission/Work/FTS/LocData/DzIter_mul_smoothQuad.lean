/-
Copyright: work module for the Elgindi finite-time singularity project.

# Leibniz rule for the iterated radial operator `D_z` in the *smooth* order

For fixed `θ`, the operator `D_z f = z ∂_z f` acts on the `z`-slice `z ↦ f z θ` as the
derivation `Zop u z = z · u'(z)`.  Consequently every iterate satisfies the binomial
(Leibniz) rule

`D_z^j (f · g) = ∑_{b ≤ j} (j.choose b) · (D_z^b f · D_z^{j-b} g)`.

This is the exact analogue of `Work.Spaces.DthIter_mul` (the `D_θ`-version) and of
`Work.Spaces.DzIter_mul` (in `Submission.Work.Spaces.mixed_mul_eq`), but with the
regularity hypothesis expressed in the **genuine `C^∞` order** `Work.Stability.smoothOrder
= ((⊤ : ℕ∞) : ℕ∞ω)` rather than in the *analytic* order `⊤ : ℕ∞ω` used by
`Work.Spaces.SmoothZ`.  This is the order in which the cut-off `χ(z/L)` of the localised
data of this chapter is smooth (`Work.FTS.LocData.SmoothQuad`, and the remark in
`Submission/Work/Stability/NotSmoothNbhdZcut`), so the `⊤`-version does not apply to it.

The combinatorial part of the induction (Pascal reindexing) is the general
`Work.Spaces.leibniz_step`, packaged for one abstract derivation-like operator as
`Work.Spaces.DerivLike.iterate_mul`; here we only have to observe that `Zop` is
`DerivLike` for the class of functions `C^∞` (not analytic) on `(-1,∞)`, and that
`DzIter` is the corresponding iterate on slices.
-/
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.InnerProductSpace.Basic
import Submission.Work.FTS.LocData.Defs
import Submission.Work.Spaces.MixedMulDefs
import Submission.Work.Spaces.DerivLikeBasic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open Set Filter

namespace Work.FTS.LocData

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-! ## The class of smooth (non-analytic) functions of `z` -/

/-- The functions of the single variable `z` which are `C^∞` on `(-1,∞)` in the genuine
smooth order `Work.Stability.smoothOrder = ((⊤ : ℕ∞) : ℕ∞ω)` — *not* in the analytic
order `⊤ : ℕ∞ω` of `Work.Spaces.SmoothZ`.  A cut-off `χ(z/L)` belongs to this class but
not to the analytic one. -/
def SmoothZsm (u : ℝ → ℝ) : Prop :=
  ContDiffOn ℝ Work.Stability.smoothOrder u (Set.Ioi (-1))

/-- `SmoothZsm` is closed under `+`, `*` and scalar multiples. -/
theorem SmoothZsm_FunClass : Work.Spaces.FunClass SmoothZsm where
  add := fun A B hA hB => hA.add hB
  mul := fun A B hA hB => hA.mul hB
  smul := fun c A hA => by
    show ContDiffOn ℝ Work.Stability.smoothOrder (fun p => c * A p) (Set.Ioi (-1))
    exact ContDiffOn.const_smul c hA

/-! ## `Zop = z ∂_z` is a derivation on the smooth functions of `(-1,∞)` -/

/-- **`Zop u = fun z => z · u'(z)`** (the action of `D_z` on the `z`-slice) is a
derivation-like operator on the functions `C^∞` on `(-1,∞)`, in the exact sense of
`Work.Spaces.DerivLike`: this is `Work.Spaces.Zop_DerivLike` with the analytic class
`Work.Spaces.SmoothZ` replaced by the smooth class `SmoothZsm`. -/
theorem Zop_DerivLike_smoothZd :
    Work.Spaces.DerivLike (Set.Ioi (-1)) SmoothZsm Work.Spaces.Zop where
  add := fun A B hA hB => by
    intro z hz
    have hA' : DifferentiableAt ℝ A z :=
      (hA.contDiffAt (isOpen_Ioi.mem_nhds hz)).differentiableAt (by simp)
    have hB' : DifferentiableAt ℝ B z :=
      (hB.contDiffAt (isOpen_Ioi.mem_nhds hz)).differentiableAt (by simp)
    show Work.Spaces.Zop (A + B) z = Work.Spaces.Zop A z + Work.Spaces.Zop B z
    simp only [Work.Spaces.Zop]
    rw [deriv_add hA' hB']
    ring
  mul := fun A B hA hB => by
    intro z hz
    have hA' : DifferentiableAt ℝ A z :=
      (hA.contDiffAt (isOpen_Ioi.mem_nhds hz)).differentiableAt (by simp)
    have hB' : DifferentiableAt ℝ B z :=
      (hB.contDiffAt (isOpen_Ioi.mem_nhds hz)).differentiableAt (by simp)
    show Work.Spaces.Zop (A * B) z = Work.Spaces.Zop A z * B z + A z * Work.Spaces.Zop B z
    simp only [Work.Spaces.Zop]
    rw [deriv_mul hA' hB']
    ring
  congr := fun A B h => by
    intro z hz
    show Work.Spaces.Zop A z = Work.Spaces.Zop B z
    simp only [Work.Spaces.Zop]
    rw [h.deriv isOpen_Ioi hz]
  preserve := fun A hA => by
    have hfd : ContDiffOn ℝ Work.Stability.smoothOrder (fderiv ℝ A) (Set.Ioi (-1)) :=
      hA.fderiv_of_isOpen isOpen_Ioi (by simp)
    have hev : ContDiffOn ℝ Work.Stability.smoothOrder (fun z : ℝ => (fderiv ℝ A z) 1)
        (Set.Ioi (-1)) :=
      hfd.clm_apply contDiffOn_const
    have hfun : ContDiffOn ℝ Work.Stability.smoothOrder
        (fun z : ℝ => z * (fderiv ℝ A z) 1) (Set.Ioi (-1)) :=
      (contDiff_id.contDiffOn).mul hev
    refine hfun.congr (fun z hz => ?_)
    show Work.Spaces.Zop A z = z * (fderiv ℝ A z) 1
    simp only [Work.Spaces.Zop]
    rw [fderiv_apply_one_eq_deriv]
  smul := fun c A hA => by
    intro z hz
    have hA' : DifferentiableAt ℝ A z :=
      (hA.contDiffAt (isOpen_Ioi.mem_nhds hz)).differentiableAt (by simp)
    show Work.Spaces.Zop (fun p => c * A p) z = c * Work.Spaces.Zop A z
    simp only [Work.Spaces.Zop]
    rw [deriv_const_mul c hA']
    ring

/-! ## `DzIter` on a slice is the iterate of `Zop` -/

/-- For fixed `θ`, the iterated operator `D_z^n` on the `z`-slice is the `n`-fold iterate
of `Zop`. -/
theorem Zop_iterate_slice (n : ℕ) (f : ℝ → ℝ → ℝ) (θ : ℝ) :
    (fun z => Work.Spaces.DzIter n f z θ) = Work.Spaces.Zop^[n] (fun z => f z θ) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      funext z
      rw [Function.iterate_succ_apply']
      show Work.Spaces.Dz (Work.Spaces.DzIter n f) z θ
          = Work.Spaces.Zop (Work.Spaces.Zop^[n] (fun z => f z θ)) z
      simp only [Work.Spaces.Dz, Work.Spaces.pz, Work.Spaces.Zop]
      rw [ih]

/-! ## The Leibniz rule -/

theorem DzIter_mul_smoothQuad (j : ℕ) (f g : ℝ → ℝ → ℝ) {z θ : ℝ} (hz : z ∈ Work.Spaces.Iz)
    (hf : ContDiffOn ℝ Work.Stability.smoothOrder (fun z' => f z' θ) (Set.Ioi (-1)))
    (hg : ContDiffOn ℝ Work.Stability.smoothOrder (fun z' => g z' θ) (Set.Ioi (-1))) :
    Work.Spaces.DzIter j (fun z θ => f z θ * g z θ) z θ =
      ∑ b ∈ Finset.range (j + 1),
        (j.choose b : ℝ) * (Work.Spaces.DzIter b f z θ * Work.Spaces.DzIter (j - b) g z θ) := by
  have hz1 : z ∈ Set.Ioi (-1) := by
    rw [Work.Spaces.Iz, Set.mem_Ici] at hz
    exact Set.mem_Ioi.mpr (by linarith)
  have key := (Work.Spaces.DerivLike.iterate_mul Zop_DerivLike_smoothZd SmoothZsm_FunClass
    j hf hg) hz1
  rw [show (fun z => f z θ) * (fun z => g z θ) = (fun z => f z θ * g z θ) from rfl] at key
  have htr : Work.Spaces.Zop^[j] (fun z => (fun z θ => f z θ * g z θ) z θ) z =
      Work.Spaces.Zop^[j] (fun z => f z θ * g z θ) z := rfl
  rw [congrFun (Zop_iterate_slice j (fun z θ => f z θ * g z θ) θ) z, htr, key]
  apply Finset.sum_congr rfl
  intro b hb
  rw [← congrFun (Zop_iterate_slice b f θ) z,
    ← congrFun (Zop_iterate_slice (j - b) g θ) z]

end Work.FTS.LocData
