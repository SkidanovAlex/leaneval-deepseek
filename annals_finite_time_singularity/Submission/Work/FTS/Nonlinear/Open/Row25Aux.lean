/-
# Row 25 of the §8 table in the open-quadrant (primed) vocabulary

`Work.FTS.Nonlinear.Open.Row25`: the `ℋ⁴`-honesty together with the `√α`-bound of the two pieces

  `N₅^{gs} = -sin²θ·FK(g)·F_*`,        `N₅^{sg} = -sin²θ·FK(F_*)·g`,

in the primed context `N4Norm'`/`N4Extra'` with the open-quadrant packages `StarPkgo`/`EllPkgGo`.

## Route

Write `FM.Fstar z = 2z/(1+z)² = 2·hKer z`, `F_* z θ = α(Γ(θ)/c)·FM.Fstar z` and
`FK(F_*) z = α·FM.Fstar z` (`FstarPkg.FK_Fstar`), so that

* `N₅^{sg} = -2α·(sin²θ · (hKer·g))`, a *radial* `𝒲^{4,∞}`-coefficient `2α·hKer` times `g`
  composed with the angular factor `sin²θ`;
* `N₅^{gs} = -(α/c)·(aG·(FM.Fstar·FK g))` with the angular profile `aG = sin²θ·Γ(α)`.

**`N₅^{sg}`.**  `hKer·g ∈ ℋ⁴` with `|hKer·g| ≤ Ci·α^{-1/2}·200·|g|` by the primed `wprod` clause
(`WlInfMem α 4 hKer` from `hKerConstWlInf`, `WlInf α 4 hKer ≤ 200`), and the angular factor is
handled by the primed `angmul` clause applied to the rescaled profile
`asq θ = ε·(-sin²θ)`, `ε = Ci/(2·192)`, which satisfies the two hypotheses `|asq| ≤ Ci` and
`|D_θ^i asq| ≤ Ci·sin(2θ)` (from `angProfile_sinSq`).  The constant of the clause is `Ci²`, and
the rescaling `1/ε = 2·192/Ci` together with `α·α^{-1/2} = √α` produces exactly the stated `√α`.

**`N₅^{gs}`.**  This is the row proved in the un-primed vocabulary
(`Pieces/RNP/row25.lean`), whose proof uses only the primed-independent lemmas
`fkH`, `Rr_le_HkSq`, `Rint_mul_le`, `HkIntegrand_ang_rad_sin_le`, `HkSq_ang_rad_of_le` and the
`𝒲^{4,∞}`-bound of `FM.Fstar`; the only adaptation needed is that the primed `fkH` clause takes
`HQo α 4 g` (`= SmoothOpen g ∧ HkMem α 4 g`, both from `GalClass α g`) instead of `RegQ α 4 g`.
The `ℋ⁴`-honesty conjunct is the same pointwise computation fed into `HkMem_ang_rad`
(angular × radial products), with the angular majorant `G θ = sin(2θ)^{α/5}` of
`dthSinSqGam_le`.
-/
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.OpenPkg.Defs
import Submission.Work.FTS.VocabO
import Submission.Work.FTS.Nonlinear.Pieces.Rows
import Submission.Work.FTS.Nonlinear.Defs
import Submission.Work.FTS.Nonlinear.Pieces.RNP.row25
import Submission.Work.FTS.Nonlinear.FstarPkgAll
import Submission.Work.FTS.Nonlinear.Open.smoothOpen_FK_radial
import Submission.Work.FTS.NonlinRows.AuxAngRad.HkMem_ang_rad
import Submission.Work.FTS.Nonlinear.Pieces.Rl1.EggBound
import Submission.Work.FTS.NonlinRows.NRow1_7Aux

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.Nonlinear.Open

open Work.FTS.Galerkin (Fn)

set_option linter.unusedVariables false

/-! ## Small `SmoothOpen` helpers on the open quadrant -/

/-! ## The smoothness/integrability helpers of row 25 -/

/-- The product of two angular `SmoothOpen` profiles is `SmoothOpen`. -/

theorem row25_smoothOpen_ang_mul {a b : ℝ → ℝ}
    (ha : Work.FTS.EllipticEst.SmoothOpen (fun _ (θ : ℝ) => a θ))
    (hb : Work.FTS.EllipticEst.SmoothOpen (fun _ (θ : ℝ) => b θ)) :
    Work.FTS.EllipticEst.SmoothOpen (fun _ (θ : ℝ) => a θ * b θ) := by
  refine Work.FTS.EllipticEst.smoothOpen_of_forall (fun n => ?_)
  have h1 := (Work.FTS.EllipticEst.smoothOpen_iff_forall (fun _ (θ : ℝ) => a θ)).mp ha n
  have h2 := (Work.FTS.EllipticEst.smoothOpen_iff_forall (fun _ (θ : ℝ) => b θ)).mp hb n
  have hfun : Function.uncurry (fun (_ : ℝ) (θ : ℝ) => a θ * b θ)
      = fun p : ℝ × ℝ => a p.2 * b p.2 := rfl
  rw [hfun]
  exact h1.mul h2

/-- The product of two radial `SmoothOpen` profiles is `SmoothOpen`. -/
theorem row25_smoothOpen_rad_mul {r s : ℝ → ℝ}
    (hr : Work.FTS.EllipticEst.SmoothOpen (fun z _ => r z))
    (hs : Work.FTS.EllipticEst.SmoothOpen (fun z _ => s z)) :
    Work.FTS.EllipticEst.SmoothOpen (fun z _ => r z * s z) := by
  refine Work.FTS.EllipticEst.smoothOpen_of_forall (fun n => ?_)
  have h1 := (Work.FTS.EllipticEst.smoothOpen_iff_forall (fun z _ => r z)).mp hr n
  have h2 := (Work.FTS.EllipticEst.smoothOpen_iff_forall (fun z _ => s z)).mp hs n
  have hfun : Function.uncurry (fun (z : ℝ) (_ : ℝ) => r z * s z)
      = fun p : ℝ × ℝ => r p.1 * s p.1 := rfl
  rw [hfun]
  exact h1.mul h2

/-- A constant angular profile is `SmoothOpen`. -/
theorem row25_smoothOpen_ang_const (c : ℝ) :
    Work.FTS.EllipticEst.SmoothOpen (fun _ (θ : ℝ) => c) := by
  refine Work.FTS.EllipticEst.smoothOpen_of_forall (fun n => ?_)
  have hfun : Function.uncurry (fun (_ : ℝ) (_ : ℝ) => c) = fun _ : ℝ × ℝ => c := rfl
  rw [hfun]
  exact contDiffOn_const

/-- `θ ↦ -sin²θ` is `SmoothOpen`. -/
theorem row25_smoothOpen_neg_sinSq :
    Work.FTS.EllipticEst.SmoothOpen (fun _ (θ : ℝ) => -((Real.sin θ) ^ 2)) := by
  refine Work.FTS.EllipticEst.smoothOpen_of_forall (fun n => ?_)
  have hfun : Function.uncurry (fun (_ : ℝ) (θ : ℝ) => -((Real.sin θ) ^ 2))
      = fun p : ℝ × ℝ => -((Real.sin p.2) ^ 2) := rfl
  rw [hfun]
  exact (((Real.contDiff_sin.comp contDiff_snd).pow 2).neg.contDiffOn).of_le le_top

/-- `Γ(θ) = (sinθ·cos²θ)^{α/3}` is `SmoothOpen`. -/
theorem row25_smoothOpen_Gam (α : ℝ) :
    Work.FTS.EllipticEst.SmoothOpen (fun _ (θ : ℝ) => Work.Spaces.Gam α θ) := by
  have hG : (fun (_ : ℝ) (θ : ℝ) => Work.Spaces.Gam α θ)
      = fun (_ : ℝ) (θ : ℝ) => (Real.sin θ * Real.cos θ ^ 2) ^ (α / 3) := by
    funext z θ
    rw [Work.Spaces.Gam]
  rw [hG]
  refine Work.FTS.EllipticEst.smoothOpen_of_forall (fun n => ?_)
  have hbase : ContDiffOn ℝ n (fun p : ℝ × ℝ => Real.sin p.2 * Real.cos p.2 ^ 2)
      Work.FTS.EllipticEst.Q0 :=
    (((Real.contDiff_sin.comp contDiff_snd).mul
      ((Real.contDiff_cos.comp contDiff_snd).pow 2)).contDiffOn).of_le le_top
  have hpos : ∀ p ∈ Work.FTS.EllipticEst.Q0, 0 < Real.sin p.2 * Real.cos p.2 ^ 2 := by
    intro p hp
    have hp' := Work.FTS.EllipticEst.mem_Q0.mp hp
    have hs : 0 < Real.sin p.2 := Real.sin_pos_of_pos_of_lt_pi
      (by linarith [hp'.2.1, Real.pi_pos]) (by linarith [hp'.2.2, Real.pi_pos])
    have hc : 0 < Real.cos p.2 := Real.cos_pos_of_mem_Ioo
      ⟨by linarith [hp'.2.1, Real.pi_pos], hp'.2.2⟩
    positivity
  have hfun : Function.uncurry (fun (_ : ℝ) (θ : ℝ) => (Real.sin θ * Real.cos θ ^ 2) ^ (α / 3))
      = fun p : ℝ × ℝ => (Real.sin p.2 * Real.cos p.2 ^ 2) ^ (α / 3) := rfl
  rw [hfun]
  exact hbase.rpow_const_of_ne (fun p hp => ne_of_gt (hpos p hp))

/-- `z ↦ hKer z = z/(1+z)²` is `C^∞` on `(0,∞)`. -/
theorem row25_contDiffOn_hKer : ∀ n : ℕ,
    ContDiffOn ℝ n (fun z : ℝ => Work.Spaces.hKer z) (Set.Ioi 0) := by
  intro n
  simp only [Work.Spaces.hKer_apply]
  refine ContDiffOn.div (n := (n : WithTop ℕ∞)) (s := Set.Ioi 0)
    (contDiffOn_id (𝕜 := ℝ) (s := Set.Ioi 0))
    (((contDiffOn_const (c := (1 : ℝ)) (s := Set.Ioi 0)).add
      (contDiffOn_id (𝕜 := ℝ) (s := Set.Ioi 0))).pow 2) ?_
  intro z hz
  have hz' : (0 : ℝ) < z := hz
  exact pow_ne_zero 2 (by linarith)

/-- `z ↦ FM.Fstar z = 2z/(1+z)²` is `C^∞` on `(0,∞)`. -/
theorem row25_contDiffOn_Fstar : ∀ n : ℕ,
    ContDiffOn ℝ n (fun z : ℝ => Work.FM.Fstar z) (Set.Ioi 0) := by
  intro n
  have hfun : (fun z : ℝ => Work.FM.Fstar z) = fun z => 2 * z / (1 + z) ^ 2 := by
    funext z
    rw [Work.FM.Fstar]
  rw [hfun]
  refine ContDiffOn.div (n := (n : WithTop ℕ∞)) (s := Set.Ioi 0)
    (contDiffOn_const.mul (contDiffOn_id (𝕜 := ℝ) (s := Set.Ioi 0)))
    (((contDiffOn_const (c := (1 : ℝ)) (s := Set.Ioi 0)).add
      (contDiffOn_id (𝕜 := ℝ) (s := Set.Ioi 0))).pow 2) ?_
  intro z hz
  have hz' : (0 : ℝ) < z := hz
  exact pow_ne_zero 2 (by linarith)

/-- **The angular majorant stays integrable after multiplying by the heavy weight**:
`G θ = sin(2θ)^{α/5}`, and `G²·smG α = sin(2θ)^{2α/5 - γ}` with `-1 < 2α/5 - γ ≤ 0`. -/
theorem row25_G_sq_smG_integrable {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) :
    MeasureTheory.IntegrableOn
      (fun θ : ℝ => ((Real.sin (2 * θ)) ^ (α / 5)) ^ 2
        * Work.FTS.Nonlinear.RadialProd.smG α θ) Work.Spaces.Iθ := by
  have hexp1 : -1 < 2 * (α / 5) - Work.Spaces.gam α := by
    rw [Work.Spaces.gam]; linarith
  have hexp2 : 2 * (α / 5) - Work.Spaces.gam α ≤ 0 := by
    rw [Work.Spaces.gam]; linarith
  refine (Work.Spaces.sin_two_rpow (2 * (α / 5) - Work.Spaces.gam α) hexp1 hexp2).1
    |>.congr_fun ?_ measurableSet_Icc
  intro θ hθ
  have hs : 0 ≤ Real.sin (2 * θ) :=
    Work.FTS.Nonlinear.RadialProd.sin_two_nonneg_of_mem_Iθ hθ
  have hne1 : α / 5 + α / 5 ≠ 0 := by intro hc; linarith
  have hne2 : α / 5 + α / 5 + (-(Work.Spaces.gam α)) ≠ 0 := by
    rw [Work.Spaces.gam]; intro hc; linarith
  show (Real.sin (2 * θ)) ^ (2 * (α / 5) - Work.Spaces.gam α)
      = ((Real.sin (2 * θ)) ^ (α / 5)) ^ 2 * ((Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))
  rw [pow_two, ← Real.rpow_add' hs hne1, ← Real.rpow_add' hs hne2]
  congr 1
  ring

/-! ## The row -/


end Work.FTS.Nonlinear.Open
