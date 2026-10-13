/-
# `Work.FTS.CoercivityFix.Coer1.coer1_Lhat`

The level-1 coercivity of the clean operator `Lhat = 𝓛 - Transport`:

  `2 * |f|²_{ℋ¹} ≤ H1IP α (Lhat f) f`   for `f ∈ RegQ α 2`.

This file is the final assembly: the `ℋ¹`-energy is identified with the three weighted energies
(`HkSq_one_eq` together with `EDz_eq_En`, `EfEta_eq_En`, `EDth_eq_En`), the plain `D_θ`-energy is
dominated by the `γ`-weighted one (`EDthW_le_En_gam`), and the four coercivity estimates
`est_A` … `est_D` feed the arithmetic of `assembly`.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.CoercivityFix.Basic
import Submission.Work.FTS.CoercivityFix.Coer1.Estimates
import Submission.Work.FTS.CoercivityFix.Coer1.Assembly
import Submission.Work.FTS.LocDataExt.Monotone

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.CoercivityFix.Coer1

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false

theorem coer1_Lhat (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1 / 4) {f : ℝ → ℝ → ℝ}
    (hf : Work.FTS.Nonlin.RegQ α 2 f) :
    2 * Work.Spaces.HkSq α 1 f
      ≤ Work.Coercivity.H1IP α (Work.FTS.CoercivityFix.Lhat f) f := by
  -- the `ℋ¹`-membership of `f` (monotonicity in the order `k = 2 → 1`)
  have hHk1 : Work.Spaces.HkMem α 1 f :=
    Work.FTS.LocDataExt.HkMem_mono (by norm_num) hf.1 hf.2.1
  -- the ℋ¹-energy is the sum of the three weighted energies
  have hHk : Work.Spaces.HkSq α 1 f
      = En Work.Spaces.eta (Work.Spaces.Dz f) + En Work.Spaces.eta f
        + En (Work.Spaces.gam α) (Work.Spaces.Dth f) := by
    rw [HkSq_one_eq α hf.1 hHk1, EDz_eq_En, EfEta_eq_En, EDth_eq_En]
  -- the integrability certificates
  have hp := IntPkg_Q α hα hf
  have hDθW : MeasureTheory.IntegrableOn (Function.uncurry (fun z θ =>
      (Work.Spaces.Dth f z θ) ^ 2 * Work.Spaces.w z ^ 2))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) :=
    integrableOn_congr_fun_Q (A := fun z θ =>
      (Work.Spaces.mixed 0 1 f z θ) ^ 2 * Work.Spaces.w z ^ 2)
      (hp.sqMixedOne 1 0 (by norm_num) (by norm_num)) (fun z θ => by
        simp only [Work.Spaces.mixed, Work.Spaces.DzIter_zero, Work.Spaces.DthIter_zero,
          Work.Spaces.DthIter_succ])
  have hDθG : MeasureTheory.IntegrableOn (Function.uncurry (fun z θ =>
      (Work.Spaces.Dth f z θ) ^ 2 * Work.Spaces.w z ^ 2 * sig (Work.Spaces.gam α) θ))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) :=
    integrableOn_congr_fun_Q
      (A := fun z θ => (Work.Spaces.mixed 0 1 f z θ) ^ 2
        * Work.Spaces.w z ^ 2 * sig (Work.Spaces.gam α) θ)
      (to_h1 (hp.sqMixedGam 1 0 (by norm_num) (by norm_num))) (fun z θ => by
        simp only [Work.Spaces.mixed, Work.Spaces.DzIter_zero, Work.Spaces.DthIter_zero,
          Work.Spaces.DthIter_succ])
  have hW : Work.Coercivity.EDthW f ≤ En (Work.Spaces.gam α) (Work.Spaces.Dth f) :=
    EDthW_le_En_gam α hα f hDθW hDθG
  exact assembly α hα hα1 hHk hW (est_A α hα hα1 hf) (est_B α hα hα1 hf)
    (est_C α hα hα1 hf) (est_D α hα hα1 hf)

end Work.FTS.CoercivityFix.Coer1
