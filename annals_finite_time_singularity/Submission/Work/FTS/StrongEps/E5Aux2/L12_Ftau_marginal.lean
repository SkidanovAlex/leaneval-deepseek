/-
# `L12_Ftau_marginal` — the `L₁₂`-marginal of the `Ftau`-family, with its `z`-derivative

Along the `ε`-scheme (`ε n → 0`) the `L₁₂`-functional of the *full* profiles
`F(τ) = F_τ = F_* + slice g τ` converges at every `z > 0`, and so does its `z`-derivative:

  `L₁₂ (Ftau α (JfamP ρ (ε n) (G n)) s) z ⟶ L₁₂ (Ftau α g s) z`,
  `∂_z L₁₂ (Ftau α (JfamP ρ (ε n) (G n)) s) z ⟶ ∂_z L₁₂ (Ftau α g s) z`.

Both statements reduce to the corresponding ones for the **modulation** `h` alone:

* **the `F_*`-split.**  `L₁₂` is an integral in the profile, so
  `L₁₂ (F_* + h) z = L₁₂ (F_*) z + L₁₂ h z` for `z ≥ 0` as soon as the four integrability
  certificates exist (`LocData.L12_add_mul`).  The `F_*`-part is `n`-independent, so the value
  convergence follows from the proved `E5Aux2.l12Slice_JfamP_tendsto`.
* **the derivative.**  `∂_z L₁₂ (F_* + h) z = - L₁₂dens (F_* + h) z` (`FM.hasDerivAt_L12`,
  from the integrability and the continuity of the density), and
  `z · L₁₂dens F z = 𝔽K F z` (`Construction.mul_L12dens_eq_FK`), so
  `∂_z L₁₂ (F_* + h) z = - 𝔽K (F_* + h) z / z`.  The `𝔽K`-convergence is the proved
  `E5Aux2.FK_JfamP_tendsto`.

The two analytic inputs about the density are supplied in the auxiliary chapter `L12FtauAux`:

* `L12FtauAux.L12dens_continuousAt_of_bound` — continuity of the density at `z > 0` from
  continuity on the open quadrant plus a *pointwise* bound;
* `L12FtauAux.integrableOn_L12dens_of_majorant` — integrability of the density on `(0,∞)`
  from a radial majorant `Maj` with `Maj s / s` integrable;
* `L12FtauAux.L12dens_add_Fstar_of_majorant` — the (pointwise) additivity of the density.

The pointwise bound on the *limit* slice `|slice g s σ θ| ≤ Maj σ` (used to feed the first two
inputs at the limit profile, whose `ℋ⁴`-data is not otherwise available) is the pointwise limit
of the `SlotMaj`-bounds of the `EpsDecay` clause.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongEps.E5Aux2.MuHGlue
import Submission.Work.FTS.LocData.L12_add_mul
import Submission.Work.Stability.L12Add
import Submission.Work.FTS.MeridianDyn.Bridge.Pieces.L12dens_Fstar_integrableOn
import Submission.Work.FTS.StrongEps.E5Aux2.L12FtauAux.L12dens_continuousAt_of_bound
import Submission.Work.FTS.StrongEps.E5Aux2.L12FtauAux.integrableOn_L12dens_of_majorant
import Submission.Work.FTS.StrongEps.E5Aux2.L12FtauAux.L12dens_add_Fstar_of_majorant

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
