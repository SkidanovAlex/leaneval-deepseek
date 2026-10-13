import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS_RegExport.RXT0.DtauProto
import Submission.Work.FTS_RegExport.RXT.Sys.hasDerivAt_mixed_z
import Submission.Work.FTS_RegExport.RXT.Sys.hasDerivAt_mixed_theta
import Submission.Work.FTS.PhiStar.Series.SmoothAux.contDiffOn_of_families_nat
import Submission.Work.FTS_RegExport.RXT.jc3

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS_RegExport.RXT0.DtauGeo` — the Fréchet-derivative data of the slot map

For `β = (b,a)`, `a + b ≤ 2`, the spatial slice `(z,θ) ↦ D_z^bD_θ^a g(z,θ,τ)` is `C¹` on the
open quadrant (from the `C⁴`-regularity `RegPkgMin.c4`) with the explicit derivative `Lfun …`,
and that derivative is jointly continuous on the slab `z > 0, 0 < θ < π/2, τ ∈ [0,S]` (from
`jc3`).  These are the `hd`/`hL` hypotheses of `RXT0.slabC1`.
-/

noncomputable section
open scoped Real Topology NNReal
open Set Filter MeasureTheory

namespace Work.FTS_RegExport.RXT0

open Work.FTS.Galerkin (Fn Fam slice gdot)
open Work.FTS.Regularity (pExp)
open Work.FTS.FinalV2 (DynOK' Sol)
open Work.FTS.RegExportIface

set_option autoImplicit false

variable {α C₀ Ce Cs : ℝ} {Φs : Fn} {E : Fn →ₗ[ℝ] Fn} {g : Fam}

/-- The candidate spatial Fréchet derivative of the slot map `(z,θ) ↦ D_z^bD_θ^a g(z,θ,τ)`. -/
noncomputable def Lfun (g : Fam) (b a : ℕ) (p : ℝ × ℝ × ℝ) : (ℝ × ℝ) →L[ℝ] ℝ :=
  Work.FTS.PhiStar.Series.SmoothAux.cclm
    (Work.Spaces.mixed (b + 1) a (slice g p.2.2) p.1 p.2.1 / p.1,
     Work.Spaces.mixed b (a + 1) (slice g p.2.2) p.1 p.2.1 / Real.sin (2 * p.2.1))

/-- **The spatial Fréchet derivative of a slot.** -/
theorem dtau_hasFDerivAt (hOK : DynOK' (pExp α) C₀ Φs E g)
    {S : ℝ} (hS : 0 < S) {b a : ℕ} (hba : a + b ≤ 2) :
    ∀ p ∈ Set.Ioi (0:ℝ) ×ˢ (Set.Ioo (0:ℝ) (Real.pi / 2) ×ˢ Set.Icc (0:ℝ) S),
      HasFDerivAt (fun q : ℝ × ℝ => Work.Spaces.mixed b a (slice g p.2.2) q.1 q.2)
        (Lfun g b a p) (p.1, p.2.1) := by
  intro p hp
  have hz : 0 < p.1 := hp.1
  have hθ : 0 < p.2.1 := hp.2.1.1
  have hθ2 : p.2.1 < Real.pi / 2 := hp.2.1.2
  have hτ : 0 ≤ p.2.2 := hp.2.2.1
  have h4 : ContDiffOn ℝ 4 (Function.uncurry (slice g p.2.2)) Work.FTS.EllipticEst.Q0 :=
    hOK.1.1.c4 p.2.2 hτ
  -- continuity of the two partial derivatives on the quadrant
  have hnum1 : ContinuousOn
      (Function.uncurry (Work.Spaces.mixed (b + 1) a (slice g p.2.2)))
      Work.FTS.EllipticEst.Q0 :=
    (Work.FTS_RegExport.RXT.contDiffOn_mixed_of_four h4 (j := b + 1) (i := a) (by omega)).continuousOn
  have hnum2 : ContinuousOn
      (Function.uncurry (Work.Spaces.mixed b (a + 1) (slice g p.2.2)))
      Work.FTS.EllipticEst.Q0 :=
    (Work.FTS_RegExport.RXT.contDiffOn_mixed_of_four h4 (j := b) (i := a + 1) (by omega)).continuousOn
  have hg : ContinuousOn (Function.uncurry (fun z θ =>
      Work.Spaces.mixed (b + 1) a (slice g p.2.2) z θ / z)) Work.FTS.EllipticEst.Q0 := by
    refine (hnum1.div continuousOn_fst (fun q hq => ne_of_gt hq.1)).congr (fun q hq => ?_)
    simp only [Function.uncurry, Pi.div_apply]
  have hh : ContinuousOn (Function.uncurry (fun z θ =>
      Work.Spaces.mixed b (a + 1) (slice g p.2.2) z θ / Real.sin (2 * θ)))
      Work.FTS.EllipticEst.Q0 := by
    have hsin : ContinuousOn (fun q : ℝ × ℝ => Real.sin (2 * q.2))
        Work.FTS.EllipticEst.Q0 :=
      (Real.continuous_sin.comp (continuous_const.mul continuous_snd)).continuousOn
    refine (hnum2.div hsin (fun q hq => ?_)).congr (fun q hq => ?_)
    · exact ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (by linarith [hq.2.1])
        (by linarith [hq.2.2, Real.pi_pos]))
    · simp only [Function.uncurry, Pi.div_apply]
  -- the two slice derivatives
  have hderiv_z : ∀ z θ : ℝ, (z, θ) ∈ Work.FTS.EllipticEst.Q0 →
      HasDerivAt (fun z' => Work.Spaces.mixed b a (slice g p.2.2) z' θ)
        (Work.Spaces.mixed (b + 1) a (slice g p.2.2) z θ / z) z :=
    fun z θ hzθ => Work.FTS_RegExport.RXT.Sys.hasDerivAt_mixed_z h4 b a (by omega)
      hzθ.1 hzθ.2.1 hzθ.2.2
  have hderiv_θ : ∀ z θ : ℝ, (z, θ) ∈ Work.FTS.EllipticEst.Q0 →
      HasDerivAt (fun θ' => Work.Spaces.mixed b a (slice g p.2.2) z θ')
        (Work.Spaces.mixed b (a + 1) (slice g p.2.2) z θ / Real.sin (2 * θ)) θ :=
    fun z θ hzθ => Work.FTS_RegExport.RXT.Sys.hasDerivAt_mixed_theta h4 b a (by omega)
      hzθ.1 hzθ.2.1 hzθ.2.2
  have hpt : (p.1, p.2.1) ∈ Work.FTS.EllipticEst.Q0 :=
    Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz, hθ, hθ2⟩
  have hmain : HasFDerivAt (fun q : ℝ × ℝ => Work.Spaces.mixed b a (slice g p.2.2) q.1 q.2)
      (Work.FTS.PhiStar.Series.SmoothAux.cclm
        (Work.Spaces.mixed (b + 1) a (slice g p.2.2) p.1 p.2.1 / p.1,
         Work.Spaces.mixed b (a + 1) (slice g p.2.2) p.1 p.2.1 / Real.sin (2 * p.2.1)))
      (p.1, p.2.1) :=
    (Work.FTS.PhiStar.Series.SmoothAux.hasFDerivAt_of_hasDerivAt_slices
      Work.FTS.EllipticEst.isOpen_Q0 hg hh hderiv_z hderiv_θ) (p.1, p.2.1) hpt
  show HasFDerivAt (fun q : ℝ × ℝ => Work.Spaces.mixed b a (slice g p.2.2) q.1 q.2)
      (Lfun g b a p) (p.1, p.2.1)
  unfold Lfun
  exact hmain

/-- **Joint continuity of the spatial Fréchet derivative on the slab.** -/
theorem dtau_Lcont (hα : 0 < α) (hα13 : α ≤ 1 / 3)
    (hOK : DynOK' (pExp α) C₀ Φs E g)
    {S : ℝ} (hS : 0 < S) {b a : ℕ} (hba : a + b ≤ 2) :
    ContinuousOn (fun p : ℝ × ℝ × ℝ => Lfun g b a p)
      (Set.Ioi (0:ℝ) ×ˢ (Set.Ioo (0:ℝ) (Real.pi / 2) ×ˢ Set.Icc (0:ℝ) S)) := by
  set K : Set (ℝ × ℝ × ℝ) :=
    Set.Ioi (0:ℝ) ×ˢ (Set.Ioo (0:ℝ) (Real.pi / 2) ×ˢ Set.Icc (0:ℝ) S) with hK
  have h1 : ContinuousOn (fun p : ℝ × ℝ × ℝ =>
      Work.Spaces.mixed (b + 1) a (slice g p.2.2) p.1 p.2.1 / p.1) K :=
    (Work.FTS_RegExport.RXT.jc3 hα hα13 hOK S hS (b + 1) a (by omega)).div
      continuousOn_fst (fun p hp => ne_of_gt hp.1)
  have h2 : ContinuousOn (fun p : ℝ × ℝ × ℝ =>
      Work.Spaces.mixed b (a + 1) (slice g p.2.2) p.1 p.2.1 / Real.sin (2 * p.2.1)) K :=
    (Work.FTS_RegExport.RXT.jc3 hα hα13 hOK S hS b (a + 1) (by omega)).div
      ((Real.continuous_sin.comp (continuous_const.mul continuous_snd.fst)).continuousOn)
      (fun p hp => ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (by linarith [hp.2.1.1])
        (by linarith [hp.2.1.2, Real.pi_pos])))
  refine (Work.FTS.PhiStar.Series.SmoothAux.cclm.continuous.comp_continuousOn
    (h1.prodMk h2)).congr (fun p hp => ?_)
  rfl

end Work.FTS_RegExport.RXT0
