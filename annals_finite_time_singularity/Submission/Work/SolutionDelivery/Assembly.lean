/-
# `Work.SolutionDelivery.Assembly` — the `AssemblyInputs` of the constructed solution

The main theorem of this area: **every field of `Work.StabilityFar.AssemblyInputs α` is produced
from the input package `ConstructedSolution α`** (plus `0 < α` and `α ≤ 1`, the range in which
the Hölder input `th`/`thDt` is satisfiable).

| `AssemblyInputs` field | where it comes from |
|---|---|
| `T`, `hT`, `R`, `hR`, `M`, `hM`, `M₁`, `hM₁` | direct (`ConstructedSolution`) |
| `H`, `hH`, `H₁`, `hH₁` | `Work.SolutionDelivery.HolderInputs` (core `C^{1,α}` of `ω`) |
| `c`, `hc` | `c = c₀α/2` from `ConstructedSolution.hansatz` + `hα` |
| `u₀` | `BS ω₀` (the cut-off datum) |
| `div_u₀`, `odd_u₀`, `cdh_u₀`, `vortDecay_u₀` | `Work.SolutionDelivery.Datum` (`Work.LWP.assembly_data`) |
| `sol`, `odd`, `bsSlice`, `bsTimeSlice` | direct |
| `smooth`, `core` | direct (monotonicity of the window) |
| `supp`, `bdd`, `bddDt` | `Work.SolutionDelivery.Slices` (restriction to the physical window) |
| `meas`, `measDt` | `Work.SolutionDelivery.Slices` |
| `th`, `thDt` | `Work.SolutionDelivery.HolderInputs` |
| `linfLower` | `Work.SolutionDelivery.BKM` (`St5`) |
| `bkmIntegrable` | `Work.SolutionDelivery.BKM` (continuity of `t ↦ ‖ω(·,t)‖_∞`) |
-/
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.PiL2
import Submission.Work.SolutionDelivery.BKM
import Submission.Work.SolutionDelivery.Basic
import Submission.Work.SolutionDelivery.DatumEuler
import Submission.Work.SolutionDelivery.BiotSavartTime

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open FiniteTimeSingularity Set Gradient Matrix Filter Topology MeasureTheory
open scoped Topology Matrix NNReal ENNReal

namespace Work.SolutionDelivery

variable {α : NNReal}

/-- **The assembly's input package, filled from the constructed solution.** -/
def assemblyInputs_of_constructed (C : ConstructedSolution α) (hα : 0 < (α : ℝ))
    (hα1 : (α : ℝ) ≤ 1) : Work.StabilityFar.AssemblyInputs α :=
  let h := C.exists_timeHolder hα1
  let hd := C.exists_timeHolder_timeDeriv
  { T := C.T
    hT := C.hT
    R := C.R
    hR := C.hR
    M := C.M
    hM := C.hM
    M₁ := C.M₁
    hM₁ := C.hM₁
    H := h.choose
    hH := h.choose_spec.1
    H₁ := hd.choose
    hH₁ := hd.choose_spec.1
    c := C.c₀ * (α : ℝ) / 2
    hc := by
      have := C.hc₀
      have := hα
      positivity
    u₀ := Work.LWP.biotSavart C.ω₀
    p := C.p
    u := C.u
    ω := C.ω
    div_u₀ := C.datum_div hα hα1
    odd_u₀ := C.datum_odd hα hα1
    cdh_u₀ := C.datum_contDiffHolder hα hα1
    vortDecay_u₀ := C.datum_vorticityDecay hα hα1
    sol := C.sol
    odd := C.odd
    smooth := C.smooth.mono (fun p hp => ⟨trivial, ⟨by linarith [hp.2.1], by linarith [hp.2.2]⟩⟩)
    core := C.coreU
    bsSlice := C.bsSlice
    bsTimeSlice := isTimeBiotSavartSlice_of_extSlice (u := C.u) (ω := C.ω) (T := C.T)
      (R := C.R) (M := C.M) (M₁ := C.M₁) C.hR.le C.hM C.hM₁ C.bsSliceExt
      (Measurable.hasDerivAt_timeDeriv_slice_of_core (ρ := C.R + 1) (R := C.R) (T := C.T)
        (le_of_lt (lt_add_one C.R)) C.hωcore.1 C.hSupp)
      C.hBdd C.hBddDt C.hSupp
      (Measurable.aestronglyMeasurable_slice_of_core_extWindow (ρ := C.R + 1) (R := C.R)
        (T := C.T) (le_of_lt (lt_add_one C.R)) C.hωcore.1 C.hSupp)
    supp := C.hSupp_window
    bdd := C.hBdd_window
    bddDt := C.hBddDt_window
    meas := C.slicesMeasurable
    measDt := C.slicesMeasurable_timeDeriv
    th := h.choose_spec.2
    thDt := hd.choose_spec.2
    linfLower := C.linfLower hα
    bkmIntegrable := C.bkmIntegrable }

/-- The datum of the filled `AssemblyInputs` is the constructed datum `BS ω₀`, and its
`EulerData` package is available for the scaling step. -/
theorem assemblyInputs_of_constructed_u₀ (C : ConstructedSolution α) (hα : 0 < (α : ℝ))
    (hα1 : (α : ℝ) ≤ 1) :
    (assemblyInputs_of_constructed C hα hα1).u₀ = Work.LWP.biotSavart C.ω₀ := rfl

/-- The joint `C^{1,α}` regularity of the constructed solution on every strip
(`Work.StabilityFar.stability_strip_holder` applied to the filled `AssemblyInputs`). -/
theorem stability_strip_holder_of_constructed (C : ConstructedSolution α) (hα : 0 < (α : ℝ))
    (hα1 : (α : ℝ) ≤ 1) :
    ∀ S ∈ Set.Ioo 0 C.T, IsContDiffHolderOn ℝ α C.u.uncurry (Set.univ ×ˢ Set.Icc 0 S) :=
  Work.StabilityFar.stability_strip_holder (assemblyInputs_of_constructed C hα hα1) hα hα1

/-- The divergence of the BKM integral at the constructed maximal time
(`Work.StabilityFar.stability_bkm_divergence` applied to the filled `AssemblyInputs`). -/
theorem stability_bkm_divergence_of_constructed (C : ConstructedSolution α) (hα : 0 < (α : ℝ))
    (hα1 : (α : ℝ) ≤ 1) :
    Filter.Tendsto (Work.LWP.bkm C.u) (𝓝[<] C.T) Filter.atTop :=
  Work.StabilityFar.stability_bkm_divergence (assemblyInputs_of_constructed C hα hα1)

/-- **The `(p,u)`-shape of `theorem_1` at the constructed maximal time `T*`**, from the
constructed solution alone (this is `Work.StabilityFar.theorem1_shape_of_inputs` applied to the
filled `AssemblyInputs`). -/
theorem theorem1_shape_of_constructed (C : ConstructedSolution α) (hα : 0 < (α : ℝ))
    (hα1 : (α : ℝ) ≤ 1) :
    ∃ p : R3 → ℝ → ℝ, ∃ u : R3 → ℝ → R3,
      (∀ t ∈ Set.Ico 0 C.T, IsOdd (u · t)) ∧
      IsLocalEulerEquationSolution p (Work.LWP.biotSavart C.ω₀) C.T u ∧
      (∀ S ∈ Set.Ioo 0 C.T, IsContDiffHolderOn ℝ α u.uncurry (Set.univ ×ˢ Set.Icc 0 S)) ∧
      Filter.Tendsto (Work.LWP.bkm u) (𝓝[<] C.T) Filter.atTop :=
  let D := assemblyInputs_of_constructed C hα hα1
  ⟨D.p, D.u, D.odd, D.sol, Work.StabilityFar.stability_strip_holder D hα hα1,
    Work.StabilityFar.stability_bkm_divergence D⟩

end Work.SolutionDelivery
