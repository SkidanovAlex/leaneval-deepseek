/-
# `Work.FTS.LocData.Fstar_factor` — the product structure of `F_* = α(Γ(θ)/c)·φ(z)`

`F_* = Work.Construction.Fstar α` is the product of a function of `θ` and a function of `z`:
`Fstar α z θ = α * (Gam α θ / c α) * FM.Fstar z`.  Consequently every `D_z`-iterate acts on the
`z`-factor, every `D_θ`-iterate acts on the `θ`-factor, and the mixed iterates split:

* `DzIter i (Fstar α) z θ = (α/c)·Γ(θ)·(z∂_z)^i φ(z)`
* `DthIter i (Fstar α) z θ = (α/c)·φ(z)·DthIter i Γ(θ)`
* `mixed j i (Fstar α) z θ = (α/c)·(DthIter i Γ)(θ)·((z∂_z)^j φ)(z)`

(the `θ`-argument of `DthIter i (fun _ θ' => Gam α θ')` being dummy). -/
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.RCLike.Basic
import Submission.Work.FTS.LocData.Defs
import Submission.Work.FTS.LocData.HkFstarDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.LocData

set_option autoImplicit false

/-- The `z`-argument of `DthIter i (fun _ θ' => Gam α θ')` is dummy. -/
theorem DthIter_gamFn_z_indep (α : ℝ) (i : ℕ) (z z' θ : ℝ) :
    Work.Spaces.DthIter i (fun _ θ' => Work.Spaces.Gam α θ') z θ
      = Work.Spaces.DthIter i (fun _ θ' => Work.Spaces.Gam α θ') z' θ := by
  induction i generalizing z z' θ with
  | zero => rfl
  | succ i ih =>
      simp only [Work.Spaces.DthIter_succ, Work.Spaces.Dth, Work.Spaces.pth]
      rw [show (fun θ' => Work.Spaces.DthIter i (fun _ θ' => Work.Spaces.Gam α θ') z θ')
            = (fun θ' => Work.Spaces.DthIter i (fun _ θ' => Work.Spaces.Gam α θ') z' θ')
          from funext (fun t => ih z z' t)]

/-- The `∂_z`-iterates of `Fstar α` act on the `z`-factor `FM.Fstar`. -/
theorem DzIter_Fstar_eq (α : ℝ) (i : ℕ) :
    Work.Spaces.DzIter i (Work.Construction.Fstar α)
      = fun z θ => (α / Work.Spaces.c α) * Work.Spaces.Gam α θ
          * Work.Spaces.DzIter i (fun z _ => Work.FM.Fstar z) z θ := by
  induction i with
  | zero =>
      funext z θ
      simp only [Work.Spaces.DzIter_zero]
      rw [Work.Construction.Fstar]
      ring
  | succ i ih =>
      rw [Work.Spaces.DzIter_succ, ih, Work.Spaces.DzIter_succ]
      funext z θ
      simp only [Work.Spaces.Dz, Work.Spaces.pz]
      rw [deriv_const_mul_field]
      ring

/-- The `∂_θ`-iterates of `Fstar α` act on the `θ`-factor `Gam α`. -/
theorem DthIter_Fstar_eq (α : ℝ) (i : ℕ) :
    Work.Spaces.DthIter i (Work.Construction.Fstar α)
      = fun z θ => (α / Work.Spaces.c α) * Work.FM.Fstar z
          * Work.Spaces.DthIter i (fun _ θ' => Work.Spaces.Gam α θ') z θ := by
  induction i with
  | zero =>
      funext z θ
      simp only [Work.Spaces.DthIter_zero]
      rw [Work.Construction.Fstar]
      ring
  | succ i ih =>
      rw [Work.Spaces.DthIter_succ, ih, Work.Spaces.DthIter_succ]
      funext z θ
      simp only [Work.Spaces.Dth, Work.Spaces.pth]
      rw [deriv_const_mul_field]
      ring

/-- The mixed iterates of `Fstar α` are the product of the two one-dimensional iterates. -/
theorem mixed_Fstar_eq (α : ℝ) (i j : ℕ) :
    Work.Spaces.mixed j i (Work.Construction.Fstar α)
      = fun z θ => (α / Work.Spaces.c α)
          * Work.Spaces.DthIter i (fun _ θ' => Work.Spaces.Gam α θ') 0 θ
          * Work.Spaces.DzIter j (fun z _ => Work.FM.Fstar z) z θ := by
  have h2 : Work.Spaces.DthIter i (Work.Construction.Fstar α)
      = fun z θ => ((α / Work.Spaces.c α)
            * Work.Spaces.DthIter i (fun _ θ' => Work.Spaces.Gam α θ') 0 θ)
          * (fun z _ => Work.FM.Fstar z) z θ := by
    rw [DthIter_Fstar_eq]
    funext z θ
    rw [DthIter_gamFn_z_indep α i z 0 θ]
    ring
  rw [Work.Spaces.mixed, h2, DzIter_mul_theta_factor]

end Work.FTS.LocData
