/-
# `GzProfile_smooth`: the explicit radial profile is `C^∞` on `(0,∞)`

`GzProfile α = -Gsing α (Construction.Fstar α)` is the paper's explicit radial profile `G` of
§'The singular term' (the decaying solution of `GzOde α`).  It is a function of `z` alone, and
the claim is that it is `C^∞` on the open half-line `(0,∞)`.

The work is entirely in the two analytic inputs of `Gsing_smooth_ode_of_facts`
(`Submission/Work/FTS/EllipticEst/Cert/Gsing_smooth_ode_of_facts.lean`), which reduces the
smoothness of `Gsing` to that of the angular moment `F_* = Elliptic.Fstar F` of the source:

* `hFsm`: `F_*(Construction.Fstar α)` is `C^∞` on `(0,∞)`;
* `hFint`: `r ↦ F_*(Construction.Fstar α)(r)/r` is integrable on `(0,∞)`.

Both are immediate from the explicit value `F_*(Construction.Fstar α)(z) = α·F_*(z)/3` with
`F_*(z) = 2z/(1+z)²` (`EllFstar_Fstar`, i.e. `Work.FTS.H2.PhiStarE.EllFstar_Fstar`), which turns
them into

* `z ↦ α·(2z/(1+z)²)/3`, a rational function whose denominator `(1+z)²` is nonzero on `(0,∞)`;
* `α·(2z/(1+z)²)/3/z = (2α/3)·(1+z)^{-2}`, integrable on `(0,∞)` by
  `integrableOn_add_rpow_Ioi_of_lt` (`-2 < -1`).

Then `GzProfile α = -(Gsing α (Construction.Fstar α))` is `C^∞` as the negative of a `C^∞`
function.
-/
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Submission.Work.FTS.PhiStar.Defs
import Submission.Work.FTS.PhiStar.Basic
import Submission.Work.FTS.PhiStar.GzProfile_ode
import Submission.Work.FTS.EllipticEst.Cert.Gsing_smooth_ode_of_facts
import Submission.Work.FTS.EllipticEst.HasDerivAt_L12_of_Fstar_facts
import Submission.Work.FTS.H2.PhiStarE.Gbar_wiln
import Submission.Work.FM.Core

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.PhiStar

set_option autoImplicit false

/-- **The angular moment of the profile is smooth.**  For `0 < α ≤ 1` the angular moment
`F_*(Construction.Fstar α)` is the explicit rational function `z ↦ α·(2z/(1+z)²)/3`, hence
`C^∞` on `(0,∞)`. -/
theorem ellFstar_GzProfile_smooth (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) :
    ∀ m : ℕ, ContDiffOn ℝ m (Work.Elliptic.Fstar (Work.Construction.Fstar α)) (Set.Ioi 0) := by
  intro m
  rw [Work.FTS.H2.PhiStarE.EllFstar_Fstar α hα hα1]
  have : (fun z : ℝ => α * Work.FM.Fstar z / 3)
      = fun z : ℝ => ((α / 3) * (2 * z)) / (1 + z) ^ 2 := by
    funext z; simp only [Work.FM.Fstar]; ring
  rw [this]
  refine ContDiffOn.div ?_ ?_ ?_
  · exact ContDiffOn.mul contDiffOn_const (contDiffOn_const.mul contDiffOn_id)
  · exact (contDiffOn_const.add contDiffOn_id).pow 2
  · intro z hz
    have : (0 : ℝ) < 1 + z := by simp only [Set.mem_Ioi] at hz; linarith
    positivity

/-- **The density `F_*/r` of the profile is integrable.**  On `(0,∞)` it equals
`(2α/3)·(1+r)^{-2}`, which is integrable there. -/
theorem ellFstar_GzProfile_integrable (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) :
    IntegrableOn (fun r : ℝ => Work.Elliptic.Fstar (Work.Construction.Fstar α) r / r)
      (Set.Ioi 0) := by
  have hA : IntegrableOn (fun s : ℝ => (s + 1) ^ (-2 : ℝ)) (Set.Ioi 0) :=
    integrableOn_add_rpow_Ioi_of_lt (a := (-2 : ℝ)) (c := 0) (m := 1)
      (by norm_num) (by norm_num)
  refine IntegrableOn.congr_fun (hA.const_mul (2 * α / 3)) ?_ measurableSet_Ioi
  intro s hs
  simp only [Set.mem_Ioi] at hs
  rw [Work.FTS.H2.PhiStarE.EllFstar_Fstar α hα hα1]
  simp only [Work.FM.Fstar]
  have hs1 : (0 : ℝ) < s + 1 := by linarith
  rw [show (s + 1) ^ (-2 : ℝ) = ((s + 1) ^ 2)⁻¹ from by
    rw [Real.rpow_neg (le_of_lt hs1), Real.rpow_ofNat]]
  field_simp
  ring

/-- **The explicit radial profile `GzProfile` is `C^∞` on `(0,∞)`.**

`GzProfile α = -Gsing α (Construction.Fstar α)`, and `Gsing_smooth_ode_of_facts` gives the
`C^∞`-smoothness of `Gsing α F` as soon as the angular moment `F_*` of the source is smooth on
`(0,∞)` and `r ↦ F_*(r)/r` is integrable there — both established above for the profile
`F = Construction.Fstar α`. -/
theorem GzProfile_smooth {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1 / 4) :
    ∀ n : ℕ, ContDiffOn ℝ n (Work.FTS.PhiStar.GzProfile α) (Set.Ioi 0) := by
  have hα1' : α ≤ 1 := by linarith
  have hFsm := ellFstar_GzProfile_smooth α hα hα1'
  have hFint := ellFstar_GzProfile_integrable α hα hα1'
  have hGs := (Work.FTS.EllipticEst.Cert.Gsing_smooth_ode_of_facts α
    (Work.Construction.Fstar α) hα hFsm hFint
    (Work.FTS.EllipticEst.HasDerivAt_L12_of_Fstar_facts _ hFsm hFint)).1
  intro n
  exact (hGs n).neg

end Work.FTS.PhiStar
