import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.Construction.Defs
import Submission.Work.Spaces.Defs
import Submission.Work.Elliptic.Defs
import Submission.Work.FTS.StrongEps.L12_tendsto_of_dominated
import Submission.Work.Elliptic.L12Aux
import Submission.Work.FM.Core2
import Submission.Work.FTS.EllipticEst.RegQ.pthU_slot_alg
import Submission.Work.FTS_RegExport.RXT.Slots.v2_Prelim
import Submission.Work.FTS_RegExport.RXT.Slots.v2_Mine

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_RegExport.RXT.Slots

open MeasureTheory Set Filter
open scoped Real Topology

set_option maxHeartbeats 800000

theorem v2_L12DzIterTendsto {C0 : ℝ} {F : ℕ → ℝ → ℝ → ℝ} {G : ℝ → ℝ → ℝ}
    (hC0 : 0 ≤ C0)
    (hF : ∀ n : ℕ, ContDiffOn ℝ 4 (Function.uncurry (F n)) Work.FTS.EllipticEst.Q0)
    (hG : ContDiffOn ℝ 4 (Function.uncurry G) Work.FTS.EllipticEst.Q0)
    (hbnd : ∀ (n : ℕ) (b a : ℕ), a + b ≤ 2 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      |Work.Spaces.mixed b a (F n) z θ| ≤ C0 * (z ^ ((3 : ℝ) / 2) / (1 + z) ^ 2))
    (hconv : ∀ (b a : ℕ), a + b ≤ 4 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Filter.Tendsto (fun n : ℕ => Work.Spaces.mixed b a (F n) z θ) Filter.atTop
        (nhds (Work.Spaces.mixed b a G z θ))) :
    ∀ j : ℕ, j ≤ 3 → ∀ z : ℝ, 0 < z →
      Filter.Tendsto (fun n : ℕ => Work.Spaces.DzIter j (fun z _ => Work.Construction.L12 (F n) z) z 0)
        Filter.atTop (nhds (Work.Spaces.DzIter j (fun z _ => Work.Construction.L12 G z) z 0)) := by
  intro j hj z hz
  -- the pointwise bound, in the `JetBnd` package
  have hbndJet : ∀ n : ℕ, JetBnd C0 (F n) := fun n => hbnd n
  have hbndG : JetBnd C0 G :=
    JetBnd.of_tendsto hbndJet (fun b a hab => hconv b a (by omega))
  -- continuity of the density of `L₁₂`, for every datum of the slot's class
  have hcontD : ∀ f : ℝ → ℝ → ℝ, ContDiffOn ℝ 4 (Function.uncurry f) Work.FTS.EllipticEst.Q0 →
      JetBnd C0 f → ContinuousOn (fun s => Work.Elliptic.L12dens f s) (Set.Ioi 0) := by
    intro f hf hb
    refine ContinuousOn.congr (s := Set.Ioi 0)
      (f := fun s => Work.Elliptic.Qang f 0 s / s)
      (g := fun s => Work.Elliptic.L12dens f s) ?_ ?_
    · intro s hs
      exact ((QangZeroDeriv_jet hC0 hf hb hs).continuousAt.div continuousAt_id
        (ne_of_gt hs)).continuousWithinAt
    · intro s _
      exact Work.Elliptic.L12dens_eq_Qang_div f s
  -- the angular-moment tower, for every datum of the slot's class
  have hkey : ∀ f : ℝ → ℝ → ℝ, ContDiffOn ℝ 4 (Function.uncurry f) Work.FTS.EllipticEst.Q0 →
      JetBnd C0 f →
      Work.Spaces.DzIter j (fun z _ => Work.Construction.L12 f z) z 0 = L12jet f j z := by
    intro f hf hb
    rw [Work.Elliptic.DzIter_rad (fun z => Work.Construction.L12 f z) j z 0]
    exact dzdIter_L12_jet hC0 hf hb
      (fun w hw => QangZeroDeriv_jet hC0 hf hb hw)
      (fun w hw => QangOneDeriv_jet hC0 hf hb hw)
      (fun w hw => Construction_L12_hasDerivAt_jet hC0 hb (hcontD f hf hb) hw) hj hz
  have hFL : (fun n : ℕ => Work.Spaces.DzIter j (fun z _ => Work.Construction.L12 (F n) z) z 0)
      = fun n : ℕ => L12jet (F n) j z := funext fun n => hkey (F n) (hF n) (hbndJet n)
  have hGL : Work.Spaces.DzIter j (fun z _ => Work.Construction.L12 G z) z 0 = L12jet G j z :=
    hkey G hG hbndG
  rw [hFL, hGL]
  -- the four levels
  have hj' : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by omega
  rcases hj' with rfl | rfl | rfl | rfl
  · -- `j = 0`: the radial dominated convergence
    change Filter.Tendsto (fun n : ℕ => Work.Construction.L12 (F n) z) Filter.atTop
      (nhds (Work.Construction.L12 G z))
    have hconvL : ∀ s : ℝ, 0 < s →
        Filter.Tendsto (fun n : ℕ => Work.Elliptic.L12dens (F n) s) Filter.atTop
          (nhds (Work.Elliptic.L12dens G s)) := by
      intro s hs
      have hq := (QangTendsto_conv hC0 hF hbndJet hbndG hconv (k := 0) (by norm_num) hs).div_const s
      rw [show (fun n : ℕ => Work.Elliptic.Qang (F n) 0 s / s)
            = fun n : ℕ => Work.Elliptic.L12dens (F n) s from
            funext fun n => (Work.Elliptic.L12dens_eq_Qang_div (F n) s).symm,
          show Work.Elliptic.Qang G 0 s / s = Work.Elliptic.L12dens G s from
            (Work.Elliptic.L12dens_eq_Qang_div G s).symm] at hq
      exact hq
    have hmeasn : ∀ n : ℕ, AEStronglyMeasurable (fun s => Work.Elliptic.L12dens (F n) s)
        (volume.restrict (Set.Ioi z)) :=
      fun n => ((hcontD (F n) (hF n) (hbndJet n)).mono
        (Set.Ioi_subset_Ioi hz.le)).aestronglyMeasurable measurableSet_Ioi
    exact L12Tendsto_dens hC0 hbndJet hmeasn hconvL hz
  · -- `j = 1`
    change Filter.Tendsto (fun n : ℕ => -Work.Elliptic.Qang (F n) 0 z) Filter.atTop
      (nhds (-(Work.Elliptic.Qang G 0 z)))
    exact (QangTendsto_conv hC0 hF hbndJet hbndG hconv (k := 0) (by norm_num) hz).neg
  · -- `j = 2`
    change Filter.Tendsto (fun n : ℕ => -Work.Elliptic.Qang (F n) 1 z) Filter.atTop
      (nhds (-(Work.Elliptic.Qang G 1 z)))
    exact (QangTendsto_conv hC0 hF hbndJet hbndG hconv (k := 1) (by norm_num) hz).neg
  · -- `j = 3`
    change Filter.Tendsto (fun n : ℕ => -Work.Elliptic.Qang (F n) 2 z) Filter.atTop
      (nhds (-(Work.Elliptic.Qang G 2 z)))
    exact (QangTendsto_conv hC0 hF hbndJet hbndG hconv (k := 2) (by norm_num) hz).neg

end Work.FTS_RegExport.RXT.Slots
