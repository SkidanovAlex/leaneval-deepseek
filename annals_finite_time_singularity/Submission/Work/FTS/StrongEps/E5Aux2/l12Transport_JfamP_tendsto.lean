import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.LocData.bumpZ_eq_zero_of_notMem_Icc
import Submission.Work.FTS.StrongEps.EpsHbdd
import Submission.Work.FTS.StrongEps.EpsMem
import Submission.Work.FTS.StrongEps.EpsSqTools.LinAux.LinPartArith
import Submission.Work.FTS.StrongEps.PZeroScheme
import Submission.Work.FTS.StrongPersist.H6Rows.N0pair6bWork.HkMem_mul_of_WlInf6_cd6
import Submission.Work.FTS_EllLimOK.Decay.DecayTools
import Submission.Work.FTS_RegExport.RXR1.HJ.AKBounds
import Submission.Work.FTS_RegExport.RXT.Slots.JetCalc.Expand
import Submission.Work.FTS_RegExport.RXVP.thLip
import Submission.Work.Spaces.bt_integral_weight_id
import Submission.Work.Spaces.one_le_mul_w
import Submission.Work.Stability.L12Add
import Submission.Work.StabilityFar.Profile.exists_Fstar_add_ge
-- ===== merged: Submission.Work.FTS.StrongEps.E5Aux2.L12_Ftau_marginal =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.E5Aux2

set_option autoImplicit false

open Work.FTS.Galerkin (Fn Fam slice)

/-- **The θ-slice of the `L₁₂`-integrand of a `Maj`-bounded, quadrant-continuous profile is
integrable** on `Iθ`. -/
theorem sliceK_integrableOn_of_bound {h : ℝ → ℝ → ℝ} {Maj : ℝ → ℝ}
    (hh : ContinuousOn (Function.uncurry h) Work.FTS.EllipticEst.Q0)
    (hbd : ∀ σ ∈ Set.Ioi (0 : ℝ), ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), |h σ θ| ≤ Maj σ)
    {σ : ℝ} (hσ : 0 < σ) :
    MeasureTheory.IntegrableOn (fun θ => Work.Spaces.K θ * h σ θ / σ) Work.Spaces.Iθ := by
  have hmeas0 : MeasureTheory.AEStronglyMeasurable
      (fun θ => Work.Spaces.K θ * h σ θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
    aesm_slice_K_of_contOn hh hσ
  have hmeas : MeasureTheory.AEStronglyMeasurable
      (fun θ => Work.Spaces.K θ * h σ θ / σ)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
    (hmeas0.mul_const (1 / σ)).congr
      (Filter.Eventually.of_forall fun θ => by ring)
  have hMajσ : 0 ≤ Maj σ := by
    have hθ : (Real.pi / 4 : ℝ) ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) :=
      ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
    exact le_trans (abs_nonneg _) (hbd σ hσ (Real.pi / 4) hθ)
  have hfin : MeasureTheory.volume Work.Spaces.Iθ < ⊤ := by
    simp only [Work.Spaces.Iθ]
    exact isCompact_Icc.measure_lt_top
  refine MeasureTheory.IntegrableOn.of_bound hfin hmeas (3 * Maj σ / σ) ?_
  filter_upwards [ae_mem_Ioo_Iθ] with θ hθ
  have hθI : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
  have hK0 : 0 ≤ Work.Spaces.K θ := K_nonneg_of_mem_Iθ hθI
  have hK3 : Work.Spaces.K θ ≤ 3 := le_trans (le_abs_self _) (abs_K_le_three θ)
  rw [Real.norm_eq_abs, abs_div, abs_mul, abs_of_nonneg hK0, abs_of_pos hσ]
  have hb : |h σ θ| ≤ Maj σ := hbd σ hσ θ hθ
  have h1 : Work.Spaces.K θ * |h σ θ| / σ ≤ Work.Spaces.K θ * Maj σ / σ := by
    gcongr
  have h2 : Work.Spaces.K θ * Maj σ / σ ≤ 3 * Maj σ / σ := by
    gcongr
  linarith

/-- **`L₁₂dens (F_*)` is continuous at every `z > 0`**: it equals the elementary function
`α · (F_{*,rad}(s)/s)`. -/
theorem continuousAt_L12dens_Fstar {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {z : ℝ}
    (hz : 0 < z) :
    ContinuousAt (Work.FM.L12dens Work.Spaces.K (Work.Construction.Fstar α)) z := by
  have h1 : ContinuousAt (fun σ : ℝ => (2 : ℝ) * σ) z :=
    continuousAt_const.mul continuousAt_id
  have h2 : ContinuousAt (fun σ : ℝ => ((1 : ℝ) + σ) ^ 2) z :=
    (continuousAt_const.add continuousAt_id).pow 2
  have h3 : ((1 : ℝ) + z) ^ 2 ≠ 0 := pow_ne_zero 2 (by linarith)
  have h4 : ContinuousAt (fun σ : ℝ => Work.FM.Fstar σ) z := h1.div h2 h3
  have h5 : ContinuousAt (fun σ : ℝ => α * (Work.FM.Fstar σ / σ)) z :=
    (h4.div continuousAt_id (ne_of_gt hz)).const_mul α
  refine h5.congr ?_
  filter_upwards [isOpen_Ioi.mem_nhds hz] with σ hσ
  exact (Work.Construction.L12dens_Fstar hα hα1 σ).symm

/-- **Density continuity for `F_* + h`**, for a `Maj`-bounded (hence bounded by `1`),
quadrant-continuous datum `h`. -/
theorem continuousAt_L12dens_Fstar_add_of_majorant {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    {h : ℝ → ℝ → ℝ} {Maj : ℝ → ℝ} (hMaj1 : ∀ σ, Maj σ ≤ 1)
    (hh : ContinuousOn (Function.uncurry h) Work.FTS.EllipticEst.Q0)
    (hbd : ∀ σ ∈ Set.Ioi (0 : ℝ), ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), |h σ θ| ≤ Maj σ)
    {z : ℝ} (hz : 0 < z) :
    ContinuousAt (Work.FM.L12dens Work.Spaces.K
      (fun z θ => Work.Construction.Fstar α z θ + h z θ)) z := by
  have h1 : ContinuousAt (Work.FM.L12dens Work.Spaces.K (Work.Construction.Fstar α)) z :=
    continuousAt_L12dens_Fstar hα hα1 hz
  have h2 : ContinuousAt (Work.FM.L12dens Work.Spaces.K h) z :=
    L12FtauAux.L12dens_continuousAt_of_bound (M := 1) (by norm_num) hh
      (fun σ hσ θ hθ => le_trans (hbd σ hσ θ hθ) (hMaj1 σ)) hz
  refine (h1.add h2).congr ?_
  filter_upwards [isOpen_Ioi.mem_nhds hz] with σ hσ
  exact (L12FtauAux.L12dens_add_Fstar_of_majorant hα hh hbd hσ).symm

/-- **Density integrability for `F_* + h`**, for a `Maj`-bounded, quadrant-continuous datum. -/
theorem integrableOn_L12dens_Fstar_add_of_majorant {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    {h : ℝ → ℝ → ℝ} {Maj : ℝ → ℝ}
    (hh : ContinuousOn (Function.uncurry h) Work.FTS.EllipticEst.Q0)
    (hMaj : MeasureTheory.IntegrableOn (fun z => Maj z / z) (Set.Ioi 0))
    (hbd : ∀ σ ∈ Set.Ioi (0 : ℝ), ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), |h σ θ| ≤ Maj σ) :
    MeasureTheory.IntegrableOn (Work.FM.L12dens Work.Spaces.K
      (fun z θ => Work.Construction.Fstar α z θ + h z θ)) (Set.Ioi 0) := by
  have hA : MeasureTheory.IntegrableOn
      (Work.FM.L12dens Work.Spaces.K (Work.Construction.Fstar α)) (Set.Ioi 0) :=
    Work.FTS.MeridianDyn.Bridge.Pieces.L12dens_Fstar_integrableOn hα hα1 0 le_rfl
  have hB : MeasureTheory.IntegrableOn (Work.FM.L12dens Work.Spaces.K h) (Set.Ioi 0) :=
    L12FtauAux.integrableOn_L12dens_of_majorant hh hMaj hbd
  have hsum : MeasureTheory.IntegrableOn
      (fun σ => Work.FM.L12dens Work.Spaces.K (Work.Construction.Fstar α) σ
        + Work.FM.L12dens Work.Spaces.K h σ) (Set.Ioi 0) := hA.add hB
  refine hsum.congr_fun (fun σ hσ => ?_) measurableSet_Ioi
  exact (L12FtauAux.L12dens_add_Fstar_of_majorant hα hh hbd hσ).symm

/-- **The value-level `F_*`-split of `L₁₂`** at `z ≥ 0`, for a `Maj`-bounded,
quadrant-continuous datum. -/
theorem L12_Fstar_add_of_majorant {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    {h : ℝ → ℝ → ℝ} {Maj : ℝ → ℝ}
    (hh : ContinuousOn (Function.uncurry h) Work.FTS.EllipticEst.Q0)
    (hMaj : MeasureTheory.IntegrableOn (fun z => Maj z / z) (Set.Ioi 0))
    (hbd : ∀ σ ∈ Set.Ioi (0 : ℝ), ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), |h σ θ| ≤ Maj σ)
    {z : ℝ} (hz : 0 ≤ z) :
    Work.Construction.L12 (fun z θ => Work.Construction.Fstar α z θ + h z θ) z
      = Work.Construction.L12 (Work.Construction.Fstar α) z + Work.Construction.L12 h z :=
  (Work.FTS.LocData.L12_add_mul 0 (a := Work.Construction.Fstar α) (b := h) (z := z)
    (fun s _ => Work.Stability.integrableOn_slice_Fstar α hα s)
    (fun _s hs => sliceK_integrableOn_of_bound hh hbd (lt_of_le_of_lt hz hs))
    (Work.FTS.MeridianDyn.Bridge.Pieces.L12dens_Fstar_integrableOn hα hα1 z hz)
    ((L12FtauAux.integrableOn_L12dens_of_majorant hh hMaj hbd).mono_set
      (Set.Ioi_subset_Ioi hz))).1

/-- **The `z`-derivative of `L₁₂ (F_* + h)` at `z > 0`**, in terms of the angular moment
`𝔽K`: it is `-𝔽K (F_* + h) z / z`. -/
theorem deriv_L12_Fstar_add_of_majorant {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    {h : ℝ → ℝ → ℝ} {Maj : ℝ → ℝ} (hMaj1 : ∀ σ, Maj σ ≤ 1)
    (hh : ContinuousOn (Function.uncurry h) Work.FTS.EllipticEst.Q0)
    (hMaj : MeasureTheory.IntegrableOn (fun z => Maj z / z) (Set.Ioi 0))
    (hbd : ∀ σ ∈ Set.Ioi (0 : ℝ), ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), |h σ θ| ≤ Maj σ)
    {z : ℝ} (hz : 0 < z) :
    deriv (fun z' => Work.Construction.L12
        (fun z θ => Work.Construction.Fstar α z θ + h z θ) z') z
      = -(Work.Construction.FK (fun z θ => Work.Construction.Fstar α z θ + h z θ) z / z) := by
  change deriv (fun z' => Work.FM.L12 Work.Spaces.K
        (fun z θ => Work.Construction.Fstar α z θ + h z θ) z') z
      = -(Work.Construction.FK (fun z θ => Work.Construction.Fstar α z θ + h z θ) z / z)
  have hderiv : HasDerivAt
      (fun z' => Work.FM.L12 Work.Spaces.K
        (fun z θ => Work.Construction.Fstar α z θ + h z θ) z')
      (-(Work.FM.L12dens Work.Spaces.K
        (fun z θ => Work.Construction.Fstar α z θ + h z θ) z)) z :=
    Work.FM.hasDerivAt_L12 (a := 0) (ρ := z)
      (integrableOn_L12dens_Fstar_add_of_majorant hα hα1 hh hMaj hbd)
      (continuousAt_L12dens_Fstar_add_of_majorant hα hα1 hMaj1 hh hbd hz) hz
  have hz0 : z ≠ 0 := ne_of_gt hz
  have hmul : z * Work.FM.L12dens Work.Spaces.K
      (fun z θ => Work.Construction.Fstar α z θ + h z θ) z
      = Work.Construction.FK (fun z θ => Work.Construction.Fstar α z θ + h z θ) z :=
    Work.Construction.mul_L12dens_eq_FK hz0
  have hden : Work.FM.L12dens Work.Spaces.K
      (fun z θ => Work.Construction.Fstar α z θ + h z θ) z
      = Work.Construction.FK (fun z θ => Work.Construction.Fstar α z θ + h z θ) z / z := by
    rw [eq_div_iff hz0, mul_comm]
    exact hmul
  rw [hderiv.deriv, hden]

/-! ## The marginal convergence -/

theorem L12_Ftau_marginal {α B : ℝ} {ρ : ℝ × ℝ → ℝ} {Φs : Work.FTS.Galerkin.Fn}
    {E : Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn} {g : Work.FTS.Galerkin.Fam}
    {ε : ℕ → ℝ} {G : ℕ → Work.FTS.Galerkin.Fam} {s : ℝ} {Maj : ℝ → ℝ}
    (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ) (hα : α ∈ Set.Ioc 0 1)
    (hε : ∀ n : ℕ, ε n ∈ Set.Ioc 0 1) (hε0 : Filter.Tendsto ε Filter.atTop (nhds 0))
    (hsm : ∀ n : ℕ, ∀ k : ℕ,
      ContDiffOn ℝ k (Function.uncurry (Work.FTS.Galerkin.slice (G n) s)) Work.FTS.StrongEps.Quad)
    (hconv : Work.FTS.StrongEps.ConvLocUnifH6 α B (fun n => Work.FTS.Galerkin.slice (G n) s) (Work.FTS.Galerkin.slice g s))
    (hC : ∀ n : ℕ, Work.FTS.ClassC.ClassC α (Work.FTS.Galerkin.slice (Work.FTS.StrongEps.JfamP ρ (ε n) (G n)) s))
    (hMajint : MeasureTheory.IntegrableOn (fun z => Maj z / z) (Set.Ioi 0))
    (hDec : ∀ n : ℕ, Work.FTS.StrongEps.EpsDecay α ρ Φs E (ε n) s (G n) Maj)
    (hl12 : Filter.Tendsto (fun n : ℕ => Work.Construction.L12
      (Work.FTS.StrongEps.Jeps ρ (ε n) (Work.FTS.Galerkin.slice (G n) s)) 0) Filter.atTop (nhds 0)) :
    (∀ z ∈ Set.Ioi (0 : ℝ), Filter.Tendsto
      (fun n : ℕ => Work.Construction.L12
        (Work.Construction.Ftau α (Work.FTS.StrongEps.JfamP ρ (ε n) (G n)) s) z)
      Filter.atTop (nhds (Work.Construction.L12 (Work.Construction.Ftau α g s) z))) ∧
    (∀ z ∈ Set.Ioi (0 : ℝ), Filter.Tendsto
      (fun n : ℕ => deriv (fun z' => Work.Construction.L12
        (Work.Construction.Ftau α (Work.FTS.StrongEps.JfamP ρ (ε n) (G n)) s) z') z)
      Filter.atTop (nhds (deriv (fun z' => Work.Construction.L12
        (Work.Construction.Ftau α g s) z') z))) := by
  have hα0 : 0 < α := hα.1
  have hα1 : α ≤ 1 := hα.2
  have hMaj1 : ∀ σ, Maj σ ≤ 1 := fun σ => (hDec 0).2.1 σ
  have hsm' : ∀ n : ℕ, ∀ k : ℕ, ContDiffOn ℝ k
      (Function.uncurry (Work.FTS.Galerkin.slice (G n) s))
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
    fun n k => by simpa only [Work.FTS.StrongEps.Quad] using hsm n k
  -- continuity of the two families of slices
  have hcont_n : ∀ n : ℕ, ContinuousOn
      (Function.uncurry (Work.FTS.Galerkin.slice
        (Work.FTS.StrongEps.JfamP ρ (ε n) (G n)) s)) Work.FTS.EllipticEst.Q0 :=
    fun n => (hC n).reg.continuousOn
  have hcont_f : ContinuousOn
      (Function.uncurry (Work.FTS.Galerkin.slice g s)) Work.FTS.EllipticEst.Q0 :=
    hconv.contDiffOn.continuousOn
  -- the `Maj`-bounds
  have hbd_n : ∀ n : ℕ, ∀ σ ∈ Set.Ioi (0 : ℝ), ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      |Work.FTS.Galerkin.slice (Work.FTS.StrongEps.JfamP ρ (ε n) (G n)) s σ θ| ≤ Maj σ := by
    intro n σ hσ θ hθ
    have h := (hDec n).2.2.2.1 σ hσ θ 0 0 (by norm_num)
    simpa only [Work.Spaces.mixed_zero_left, Work.Spaces.DthIter_zero] using h
  have hbd_f : ∀ σ ∈ Set.Ioi (0 : ℝ), ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      |Work.FTS.Galerkin.slice g s σ θ| ≤ Maj σ := by
    intro σ hσ θ hθ
    have hp : (σ, θ) ∈ Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (Real.pi / 2) := ⟨hσ, hθ⟩
    have hlim := mixed_JfamP_tendsto hρ hsm' hconv (fun n => (hε n).1) hε0 hl12 hp
      (j := 0) (i := 0) (by norm_num)
    have hlim' : Filter.Tendsto
        (fun n : ℕ => Work.FTS.Galerkin.slice
          (Work.FTS.StrongEps.JfamP ρ (ε n) (G n)) s σ θ)
        Filter.atTop (nhds (Work.FTS.Galerkin.slice g s σ θ)) := by
      simpa only [Work.Spaces.mixed_zero_left, Work.Spaces.DthIter_zero] using hlim
    refine le_of_tendsto_of_tendsto' hlim'.abs tendsto_const_nhds (fun n => ?_)
    have h := (hDec n).2.2.2.1 σ hσ θ 0 0 (by norm_num)
    simpa only [Work.Spaces.mixed_zero_left, Work.Spaces.DthIter_zero] using h
  constructor
  · -- ## The `L₁₂`-values
    intro z hz
    have hz0 : 0 ≤ z := le_of_lt hz
    have hslice_t := l12Slice_JfamP_tendsto hρ hα hε hε0 hsm hconv hC hMajint hDec hl12 z hz0
    have hgoal : Filter.Tendsto (fun n : ℕ => Work.Construction.L12
          (Work.Construction.Fstar α) z
          + Work.Construction.L12
            (Work.FTS.Galerkin.slice (Work.FTS.StrongEps.JfamP ρ (ε n) (G n)) s) z)
        Filter.atTop (nhds (Work.Construction.L12 (Work.Construction.Fstar α) z
          + Work.Construction.L12 (Work.FTS.Galerkin.slice g s) z)) :=
      hslice_t.const_add _
    have hfun : (fun n : ℕ => Work.Construction.L12
          (Work.Construction.Ftau α (Work.FTS.StrongEps.JfamP ρ (ε n) (G n)) s) z)
        = fun n : ℕ => Work.Construction.L12 (Work.Construction.Fstar α) z
          + Work.Construction.L12
            (Work.FTS.Galerkin.slice (Work.FTS.StrongEps.JfamP ρ (ε n) (G n)) s) z := by
      funext n
      exact L12_Fstar_add_of_majorant hα0 hα1 (hcont_n n) hMajint (hbd_n n) hz0
    have hval : Work.Construction.L12 (Work.Construction.Ftau α g s) z
        = Work.Construction.L12 (Work.Construction.Fstar α) z
          + Work.Construction.L12 (Work.FTS.Galerkin.slice g s) z :=
      L12_Fstar_add_of_majorant hα0 hα1 hcont_f hMajint hbd_f hz0
    rw [hfun, hval]
    exact hgoal
  · -- ## The derivatives
    intro z hz
    have hFK := FK_JfamP_tendsto hρ hα hε hε0 hsm hconv hC hMajint hDec hl12 z hz
    have hgoal : Filter.Tendsto (fun n : ℕ => -(Work.Construction.FK
          (Work.Construction.Ftau α (Work.FTS.StrongEps.JfamP ρ (ε n) (G n)) s) z / z))
        Filter.atTop (nhds (-(Work.Construction.FK
          (Work.Construction.Ftau α g s) z / z))) :=
      hFK.div_const z |>.neg
    have hfun : (fun n : ℕ => deriv (fun z' => Work.Construction.L12
          (Work.Construction.Ftau α (Work.FTS.StrongEps.JfamP ρ (ε n) (G n)) s) z') z)
        = fun n : ℕ => -(Work.Construction.FK
          (Work.Construction.Ftau α (Work.FTS.StrongEps.JfamP ρ (ε n) (G n)) s) z / z) := by
      funext n
      exact deriv_L12_Fstar_add_of_majorant hα0 hα1 hMaj1 (hcont_n n) hMajint (hbd_n n) hz
    have hval : deriv (fun z' => Work.Construction.L12 (Work.Construction.Ftau α g s) z') z
        = -(Work.Construction.FK (Work.Construction.Ftau α g s) z / z) :=
      deriv_L12_Fstar_add_of_majorant hα0 hα1 hMaj1 hcont_f hMajint hbd_f hz
    rw [hfun, hval]
    exact hgoal

end Work.FTS.StrongEps.E5Aux2
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.E5Aux2.l12Transport_JfamP_tendsto =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The `L₁₂`-zero-mode convergence of the transport block

`Work.Coercivity.Transport f = 3 D_θ f/(1+z)`, and the paper's `L₁₂`-zero-mode of the
transport block of the right-hand side is the *radial* functional
`L₁₂(Transport f)(0) = ∫_0^∞ L12dens K (Transport f)(z) dz`.

This module proves that `L₁₂(Transport (P₀ J_ε G_n)(s))(0) → L₁₂(Transport g(s))(0)` for the
approximating sequence of the `E5` extraction, by **dominated convergence in `z`**
(`L12_tendsto_of_dominated` with the measure `volume.restrict (Ioi 0)`):

* the pointwise convergence of the density at every `z > 0` is
  `l12dens_transport_tendsto_at` (a `θ`-DCT, fed by the slot convergence
  `mixed_JfamP_tendsto` at `(j,i) = (0,1)`);
* the domination `|L12dens K (Transport f_n) z| ≤ 6 Maj z / z` is
  `L12dens_transport_abs_le`, fed by the `SlotMaj 1` clause of `EpsDecay`; the majorant
  `z ↦ Maj z/z` is integrable by hypothesis (`hMajint`);
* the a.e. strong measurability of the densities comes from a.e. strong measurability of the
  uncurried `Transport`-profiles, which is joint continuity on the open quadrant
  (`MuHGlue.aesm_L12dens_of_contOn`), which in turn is
  `continuousOn_uncurry_transport` applied to the `SmoothOpen` clause of `ClassC`.
-/

namespace Work.FTS.StrongEps.E5Aux2

open MeasureTheory Set Filter

theorem l12Transport_JfamP_tendsto {α B : ℝ} {ρ : ℝ × ℝ → ℝ} {Φs : Work.FTS.Galerkin.Fn} {E : Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn}
    {g : Work.FTS.Galerkin.Fam} {ε : ℕ → ℝ} {G : ℕ → Work.FTS.Galerkin.Fam} {s : ℝ} {Maj : ℝ → ℝ}
    (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ) (hα : α ∈ Set.Ioc 0 1)
    (hε : ∀ n : ℕ, ε n ∈ Set.Ioc 0 1) (hε0 : Filter.Tendsto ε Filter.atTop (nhds 0))
    (hsm : ∀ n : ℕ, ∀ k : ℕ,
      ContDiffOn ℝ k (Function.uncurry (Work.FTS.Galerkin.slice (G n) s)) Work.FTS.StrongEps.Quad)
    (hconv : Work.FTS.StrongEps.ConvLocUnifH6 α B (fun n => Work.FTS.Galerkin.slice (G n) s)
      (Work.FTS.Galerkin.slice g s))
    (hC : ∀ n : ℕ, Work.FTS.ClassC.ClassC α
      (Work.FTS.Galerkin.slice (Work.FTS.StrongEps.JfamP ρ (ε n) (G n)) s))
    (hMajint : MeasureTheory.IntegrableOn (fun z => Maj z / z) (Set.Ioi 0))
    (hDec : ∀ n : ℕ, Work.FTS.StrongEps.EpsDecay α ρ Φs E (ε n) s (G n) Maj)
    (hl12 : Filter.Tendsto (fun n : ℕ => Work.Construction.L12
      (Work.FTS.StrongEps.Jeps ρ (ε n) (Work.FTS.Galerkin.slice (G n) s)) 0)
      Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun n : ℕ => Work.Coercivity.L12f
      (Work.Coercivity.Transport (Work.FTS.Galerkin.slice
        (Work.FTS.StrongEps.JfamP ρ (ε n) (G n)) s)) 0) Filter.atTop
      (nhds (Work.Coercivity.L12f (Work.Coercivity.Transport
        (Work.FTS.Galerkin.slice g s)) 0)) := by
  -- **(0)** Joint continuity on the open quadrant of the approximating transport profiles,
  -- from the `SmoothOpen` clause of the class `ClassC`.
  have hcont : ∀ n : ℕ, ContinuousOn (Function.uncurry (Work.Coercivity.Transport
      (Work.FTS.Galerkin.slice (Work.FTS.StrongEps.JfamP ρ (ε n) (G n)) s)))
      Work.FTS.EllipticEst.Q0 :=
    fun n => continuousOn_uncurry_transport ((hC n).reg)
  -- **(1)** A.e. strong measurability of every density `z ↦ L12dens K (Transport f_n) z`.
  have hmeas : ∀ n : ℕ, MeasureTheory.AEStronglyMeasurable
      (fun z => Work.FM.L12dens Work.Spaces.K (Work.Coercivity.Transport
        (Work.FTS.Galerkin.slice (Work.FTS.StrongEps.JfamP ρ (ε n) (G n)) s)) z)
      (MeasureTheory.volume.restrict (Set.Ioi 0)) :=
    fun n => aesm_L12dens_of_contOn (hcont n)
  -- **(2)** Pointwise convergence of the density at every `z > 0` (`θ`-DCT), hence a.e.
  have hconvae : ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi 0)),
      Filter.Tendsto (fun n : ℕ => Work.FM.L12dens Work.Spaces.K (Work.Coercivity.Transport
        (Work.FTS.Galerkin.slice (Work.FTS.StrongEps.JfamP ρ (ε n) (G n)) s)) z)
      Filter.atTop (nhds (Work.FM.L12dens Work.Spaces.K (Work.Coercivity.Transport
        (Work.FTS.Galerkin.slice g s)) z)) := by
    refine (MeasureTheory.ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall ?_)
    intro z hz
    exact l12dens_transport_tendsto_at hρ hε hε0 hsm hconv hcont hDec hl12 hz
  -- **(3)** Domination by the integrable majorant `6 Maj z / z`, uniformly in `n`.
  have hbdd : ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi 0)), ∀ n : ℕ,
      ‖Work.FM.L12dens Work.Spaces.K (Work.Coercivity.Transport
        (Work.FTS.Galerkin.slice (Work.FTS.StrongEps.JfamP ρ (ε n) (G n)) s)) z‖
      ≤ 6 * Maj z / z := by
    refine (MeasureTheory.ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall ?_)
    intro z hz n
    rw [Real.norm_eq_abs]
    exact L12dens_transport_abs_le (fun r => (hDec n).1 r)
      (fun r hr θ j i hji => (hDec n).2.2.2.1 r hr θ j i hji) hz
  -- **(4)** The majorant is integrable, by hypothesis (`Maj z / z ∈ L¹(0,∞)`).
  have hM : MeasureTheory.Integrable (fun z : ℝ => 6 * Maj z / z)
      (MeasureTheory.volume.restrict (Set.Ioi 0)) :=
    (MeasureTheory.Integrable.const_mul hMajint 6).congr
      (Filter.Eventually.of_forall (fun z => by ring))
  -- **(5)** Dominated convergence in `z`.
  have h := Work.FTS.StrongEps.L12_tendsto_of_dominated (ρ := (0 : ℝ))
    (f := fun n => Work.Coercivity.Transport
      (Work.FTS.Galerkin.slice (Work.FTS.StrongEps.JfamP ρ (ε n) (G n)) s))
    (g := Work.Coercivity.Transport (Work.FTS.Galerkin.slice g s))
    (M := fun z => 6 * Maj z / z) hmeas hconvae hbdd hM
  simpa only [Work.Coercivity.L12f, Work.Construction.L12] using h

end Work.FTS.StrongEps.E5Aux2
end
