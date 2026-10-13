/-
# `Submission/Work/FTS/StrongPersist/L3Rhs/NfkAux/NfkSmooth.lean`

The **`C³`-regularity** of the six summands of the angular-moment block
`NFkSum α f = N₄^{gg} + N₅^{gg} + N₄^{gs} + N₅^{gs} + N₄^{sg} + N₅^{sg}`
on the open quadrant `Q0`, together with the order bookkeeping (`n ≤ smoothOrder`) and the two
elementary transfers (`θ`-only factors, radial functions).

The angular moment `z ↦ FK f z` is only `C⁵` on `(0,∞)` — *not* `C^∞` — so every step here is
done at the *finite* order `3`; in particular the `ContDiff` regularity of the `θ`-only factors
is stated at the honest `C^∞` order `smoothOrder = ((⊤ : ℕ∞) : WithTop ℕ∞)` and *not* at the
analytic order `⊤ : WithTop ℕ∞`.

Everything rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Submission.Work.FTS.StrongPersist.L3Rhs.Defs
import Submission.Work.FTS.StrongPersist.L3Rhs.Assembly
import Submission.Work.FTS.StrongPersist.L3Rhs.NfkAux.Basic
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.LocData.SmoothQuad_Fstar
import Submission.Work.FTS.OpenPkg.Basic
import Submission.Work.FTS.OpenPkg.fkH_field

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.L3Rhs.NfkAux

open Work.FTS.Galerkin (Fn)
open Work.Spaces (HkMem HkSq HkNorm)

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

/-! ## Small order bookkeeping -/

/-- `n ≤ smoothOrder`: `smoothOrder = ((⊤ : ℕ∞) : WithTop ℕ∞)` is the honest `C^∞` order, not
the analytic one. -/
theorem le_smoothOrder (n : ℕ) : ((n : ℕ) : WithTop ℕ∞) ≤ Work.Stability.smoothOrder :=
  WithTop.coe_le_coe.mpr le_top

/-! ## Two elementary smoothness transfers -/

/-- A factor depending only on `θ` which is `C^n`: a `C^n` function of the pair
`(z, θ) ↦ c θ`. -/
theorem contDiffOn_theta {c : ℝ → ℝ} {n : ℕ} (hc : ContDiff ℝ (n : WithTop ℕ∞) c) :
    ContDiffOn ℝ n (Function.uncurry (fun (_ : ℝ) θ => c θ)) Work.FTS.EllipticEst.Q0 := by
  have h1 : ContDiffOn ℝ (n : WithTop ℕ∞) (fun p : ℝ × ℝ => c p.2) Work.FTS.EllipticEst.Q0 :=
    ((hc.comp contDiff_snd).contDiffOn).mono (Set.subset_univ _)
  exact h1.congr (fun p _ => rfl)

/-- A factor depending only on `θ` which is `C^n`, multiplied into a `C^n` datum. -/
theorem contDiffOn_theta_mul {c : ℝ → ℝ} {n : ℕ} (hc : ContDiff ℝ (n : WithTop ℕ∞) c)
    {f : ℝ → ℝ → ℝ}
    (hf : ContDiffOn ℝ n (Function.uncurry f) Work.FTS.EllipticEst.Q0) :
    ContDiffOn ℝ n (Function.uncurry (fun z θ => c θ * f z θ)) Work.FTS.EllipticEst.Q0 := by
  have h1 : ContDiffOn ℝ (n : WithTop ℕ∞) (fun p : ℝ × ℝ => c p.2) Work.FTS.EllipticEst.Q0 :=
    ((hc.comp contDiff_snd).contDiffOn).mono (Set.subset_univ _)
  exact (h1.mul hf).congr (fun p _ => rfl)

/-- A function of `z` alone which is `C^n` on `(0,∞)`, read on the open quadrant. -/
theorem contDiffOn_radial {g : ℝ → ℝ} {n : ℕ}
    (hg : ContDiffOn ℝ (n : WithTop ℕ∞) g (Set.Ioi 0)) :
    ContDiffOn ℝ n (Function.uncurry (fun z (_ : ℝ) => g z)) Work.FTS.EllipticEst.Q0 := by
  have h := hg.comp contDiffOn_fst (fun p hp => (Work.FTS.EllipticEst.mem_Q0.mp hp).1)
  exact h.congr (fun p _ => rfl)

/-! ## The angular moment `z ↦ FK f z` at order three -/

/-- `z ↦ FK f z`, pulled back to the open quadrant, is `C³` for `H6Adm`-data. -/
theorem contDiffOn_FK_Q0 {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {f : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.EllipticEst.SmoothOpen f) (hmem : HkMem α 6 f) :
    ContDiffOn ℝ 3 (Function.uncurry (fun z (_ : ℝ) => Work.Construction.FK f z))
      Work.FTS.EllipticEst.Q0 :=
  contDiffOn_radial (contDiffOn_FK hα hα1 hsm hmem 3 (by norm_num))

/-- `z ↦ FK (F_* α) z = α·(2z/(1+z)²)`, pulled back to the open quadrant, is `C³`. -/
theorem contDiffOn_FKstar_Q0 (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) :
    ContDiffOn ℝ 3
      (Function.uncurry (fun z (_ : ℝ) => Work.Construction.FK (Work.Construction.Fstar α) z))
      Work.FTS.EllipticEst.Q0 := by
  have htwoZ : ContDiffOn ℝ 3 (fun z => α * twoZ z) (Set.Ioi 0) :=
    ((contDiffOn_twoZ_const_mul α).of_le (le_smoothOrder 3)).mono
      (Set.Ioi_subset_Ioi (by norm_num))
  have hFKstar : ContDiffOn ℝ 3
      (fun z => Work.Construction.FK (Work.Construction.Fstar α) z) (Set.Ioi 0) := by
    have heq : (fun z => Work.Construction.FK (Work.Construction.Fstar α) z)
        = fun z => α * twoZ z := by
      funext z
      rw [Work.FTS.Nonlin.FK_Fstar hα hα1]
      rfl
    rw [heq]
    exact htwoZ
  exact contDiffOn_radial hFKstar

/-! ## `C³`-regularity of the six summands -/

theorem contDiffOn_N4gg {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {f : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.EllipticEst.SmoothOpen f) (hmem : HkMem α 6 f) :
    ContDiffOn ℝ 3 (Function.uncurry (Work.FTS.Nonlin.N4gg α f))
      Work.FTS.EllipticEst.Q0 := by
  have hA : ContDiffOn ℝ 3 (fun p : ℝ × ℝ => (-(1 / 2)) * Work.Construction.FK f p.1)
      Work.FTS.EllipticEst.Q0 :=
    contDiffOn_const.mul (contDiffOn_FK_Q0 hα hα1 hsm hmem)
  have hB : ContDiffOn ℝ 3 (Function.uncurry (Work.Spaces.Dth f))
      Work.FTS.EllipticEst.Q0 := hsm.Dth.forall 3
  refine (hA.mul hB).congr (fun p _ => ?_)
  simp only [Work.FTS.Nonlin.N4gg, Function.uncurry] <;> ring

theorem contDiffOn_N5gg {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {f : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.EllipticEst.SmoothOpen f) (hmem : HkMem α 6 f) :
    ContDiffOn ℝ 3 (Function.uncurry (Work.FTS.Nonlin.N5gg f))
      Work.FTS.EllipticEst.Q0 := by
  have hA : ContDiffOn ℝ 3 (fun p : ℝ × ℝ => (-1) * Work.Construction.FK f p.1)
      Work.FTS.EllipticEst.Q0 :=
    contDiffOn_const.mul (contDiffOn_FK_Q0 hα hα1 hsm hmem)
  have hB : ContDiffOn ℝ 3 (Function.uncurry (fun z θ => Real.sin θ ^ 2 * f z θ))
      Work.FTS.EllipticEst.Q0 :=
    contDiffOn_theta_mul (Real.contDiff_sin.pow 2) (hsm.forall 3)
  refine (hA.mul hB).congr (fun p _ => ?_)
  simp only [Work.FTS.Nonlin.N5gg, Function.uncurry]
  ring

theorem contDiffOn_N4gs (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) {f : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.EllipticEst.SmoothOpen f) (hmem : HkMem α 6 f) :
    ContDiffOn ℝ 3 (Function.uncurry (Work.FTS.Nonlin.N4gs α f))
      Work.FTS.EllipticEst.Q0 := by
  have hF : Work.FTS.EllipticEst.SmoothOpen (Work.Construction.Fstar α) :=
    Work.FTS.OpenPkg.smoothOpen_of_smoothQuad (Work.FTS.LocData.SmoothQuad_Fstar α)
  have hs2 : ContDiff ℝ (3 : WithTop ℕ∞) (fun θ : ℝ => Work.Construction.s2 θ) := by
    have h : ContDiff ℝ (3 : WithTop ℕ∞) (fun θ : ℝ => Real.sin (2 * θ)) :=
      Real.contDiff_sin.comp (contDiff_const.mul contDiff_id)
    have heq : (fun θ : ℝ => Real.sin (2 * θ)) = fun θ : ℝ => Work.Construction.s2 θ := by
      funext θ
      simp only [Work.Construction.s2]
    rw [heq] at h
    exact h
  have hB : ContDiffOn ℝ 3
      (Function.uncurry (fun z θ => Work.Construction.s2 θ
        * Work.Spaces.pth (Work.Construction.Fstar α) z θ)) Work.FTS.EllipticEst.Q0 :=
    contDiffOn_theta_mul hs2 (hF.pth.forall 3)
  have hA : ContDiffOn ℝ 3
      (fun p : ℝ × ℝ => (-(1 / 2)) * Work.Construction.FK f p.1) Work.FTS.EllipticEst.Q0 :=
    contDiffOn_const.mul (contDiffOn_FK_Q0 hα hα1 hsm hmem)
  refine (hA.mul hB).congr (fun p _ => ?_)
  simp only [Work.FTS.Nonlin.N4gs, Function.uncurry]
  ring

theorem contDiffOn_N5gs (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) {f : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.EllipticEst.SmoothOpen f) (hmem : HkMem α 6 f) :
    ContDiffOn ℝ 3 (Function.uncurry (Work.FTS.Nonlin.N5gs α f))
      Work.FTS.EllipticEst.Q0 := by
  have hF : Work.FTS.EllipticEst.SmoothOpen (Work.Construction.Fstar α) :=
    Work.FTS.OpenPkg.smoothOpen_of_smoothQuad (Work.FTS.LocData.SmoothQuad_Fstar α)
  have hA : ContDiffOn ℝ 3 (fun p : ℝ × ℝ => (-1) * Work.Construction.FK f p.1)
      Work.FTS.EllipticEst.Q0 :=
    contDiffOn_const.mul (contDiffOn_FK_Q0 hα hα1 hsm hmem)
  have hB : ContDiffOn ℝ 3
      (Function.uncurry (fun z θ => Real.sin θ ^ 2 * Work.Construction.Fstar α z θ))
      Work.FTS.EllipticEst.Q0 :=
    contDiffOn_theta_mul (Real.contDiff_sin.pow 2) (hF.forall 3)
  refine (hA.mul hB).congr (fun p _ => ?_)
  simp only [Work.FTS.Nonlin.N5gs, Function.uncurry]
  ring

theorem contDiffOn_N4sg (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) {f : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.EllipticEst.SmoothOpen f) (hmem : HkMem α 6 f) :
    ContDiffOn ℝ 3 (Function.uncurry (Work.FTS.Nonlin.N4sg α f))
      Work.FTS.EllipticEst.Q0 := by
  have hA : ContDiffOn ℝ 3
      (fun p : ℝ × ℝ => (-(1 / 2)) * Work.Construction.FK (Work.Construction.Fstar α) p.1)
      Work.FTS.EllipticEst.Q0 :=
    contDiffOn_const.mul (contDiffOn_FKstar_Q0 α hα hα1)
  have hB : ContDiffOn ℝ 3 (Function.uncurry (Work.Spaces.Dth f))
      Work.FTS.EllipticEst.Q0 := hsm.Dth.forall 3
  refine (hA.mul hB).congr (fun p _ => ?_)
  simp only [Work.FTS.Nonlin.N4sg, Function.uncurry] <;> ring

theorem contDiffOn_N5sg (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) {f : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.EllipticEst.SmoothOpen f) (hmem : HkMem α 6 f) :
    ContDiffOn ℝ 3 (Function.uncurry (Work.FTS.Nonlin.N5sg α f))
      Work.FTS.EllipticEst.Q0 := by
  have hA : ContDiffOn ℝ 3
      (fun p : ℝ × ℝ => (-1) * Work.Construction.FK (Work.Construction.Fstar α) p.1)
      Work.FTS.EllipticEst.Q0 :=
    contDiffOn_const.mul (contDiffOn_FKstar_Q0 α hα hα1)
  have hB : ContDiffOn ℝ 3 (Function.uncurry (fun z θ => Real.sin θ ^ 2 * f z θ))
      Work.FTS.EllipticEst.Q0 :=
    contDiffOn_theta_mul (Real.contDiff_sin.pow 2) (hsm.forall 3)
  refine (hA.mul hB).congr (fun p _ => ?_)
  simp only [Work.FTS.Nonlin.N5sg, Function.uncurry]
  ring

end Work.FTS.StrongPersist.L3Rhs.NfkAux
