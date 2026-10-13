import Mathlib.Algebra.Category.Grp.Basic
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllipticEst.TT.WeakDefs
import Submission.Work.FTS.EllipticEst.TT.gammaHonesty
import Submission.Work.FTS.EllipticEst.H2W.AeDataAof
import Submission.Work.FTS.EllipticEst.Prop.aslotTwoShift_aeDzTrace_gam
import Submission.Work.FTS.EllipticEst.Prop.aslotTwoShift_mixedSliceHon
import Submission.Work.FTS.EllipticEst.Prop.levelTopSlotsTwoPlumb
import Submission.Work.FTS.EllipticEst.Prop.levelTopSlotsTwoBnds
import Submission.Work.FTS.EllipticEst.H2W.AeProof.AeSliceRightTendsto
import Submission.Work.FTS.EllipticEst.remov.smoothOpen_slices_weak
import Submission.Work.FTS.EllipticEst.TT.bslOp_DzIter_eq
import Submission.Work.FTS.EllipticEst.Cert.GbarSin.HkMem_congr_Q0
import Submission.Work.FTS.EllipticEst.DzAmgm.ZsqPz2Comm
import Submission.Work.EllipticEst.H2W.pthIter2_DzIter_comm
import Submission.Work.FTS.EllipticEst.Prop.traceBoundLeft
import Submission.Work.FTS.EllipticEst.Prop.traceBoundRight
import Submission.Work.FTS.EllipticEst.Prop.thetaInterpCoreOfTraceBounds
import Submission.Work.FTS.EllipticEst.Prop.levelTopSlotsTwoShift
import Submission.Work.FTS.EllipticEst.Final.Level0
import Submission.Work.FTS.EllipticEst.Cores.step2Ae_fts
import Submission.Work.FTS.EllipticEst.AeS1.Assembly
import Submission.Work.FTS.EllipticEst.AeS1.unwEnergyD
import Submission.Work.FTS.EllipticEst.Dispatch.aeSigmaEnergyD
import Submission.Work.FTS.EllipticEst.Dispatch.step3AeD
import Submission.Work.FTS.EllipticEst.Final.AeSigmaUpD
import Submission.Work.FTS.EllipticEst.Cores.AeStep2Aux.aeUHk_mem
import Submission.Work.FTS.EllipticEst.Cores.AeStep2Aux.aeUHk_bnd
import Submission.Work.FTS.EllipticEst.Cores.AeStep2Aux.aeI4_open
import Submission.Work.FTS.EllipticEst.AngAWeak.step1Ae

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.Prop

open scoped Real Topology
open MeasureTheory Set Filter

local notation "Aof" => Work.FTS.EllipticEst.H2W.Aof
local notation "Iz" => Work.Spaces.Iz
local notation "Iθ" => Work.Spaces.Iθ

/-- `z²∂_z²Ψ` is smooth on the open quadrant as soon as `Ψ` is. -/
theorem aofSmoothOpen {Ψ : ℝ → ℝ → ℝ} (hΨ : Work.FTS.EllipticEst.SmoothOpen Ψ) :
    Work.FTS.EllipticEst.SmoothOpen (Aof Ψ) :=
  smoothOpen_zsq_mul (hΨ.pzIter 2)

/-- **The `ℋ⁰`-honesty of `D_z (z²∂_z²Ψ)`** for a level-`2` weak datum: the `i = 1` pure summand
of `HkIntegrand α 2 (Aof Ψ)` dominates the weighted square of `D_z (Aof Ψ)`. -/
theorem hkMem_zero_Dz_Aof {α : ℝ} {F Ψ : ℝ → ℝ → ℝ}
    (h : Work.FTS.EllipticEst.TT.EllWeakPos α 2 F Ψ) :
    Work.Spaces.HkMem α 0 (Work.Spaces.Dz (Aof Ψ)) := by
  have hΨ : Work.FTS.EllipticEst.SmoothOpen Ψ := smoothOpen_of_forall h.smooth
  exact HkMem_zero_of_pointwise (c := 1) zero_le_one ((aofSmoothOpen hΨ).Dz) h.memA
    (fun z θ hz hθ hlt => by
      rw [HkIntegrand_zero_apply]
      simpa only [Work.Spaces.DzIter_succ, Work.Spaces.DzIter_zero, one_mul] using
        Work.Spaces.sq_le_HkIntegrand_z α 2 (Aof Ψ) z θ 1 (by norm_num))

/-- **The two vanishing endpoint traces of `θ ↦ D_z (z²∂_z²Ψ)(z,θ)`** for a level-`2` weak datum,
a.e. in `z`.  This is the `θ`-flux input of the integrations by parts for the twisted datum
`(Aof Ψ, Gof F)`: it discharges the `hMixS`/`hMixO` hypotheses of
`aslotTwoShift_aeDzTrace_gam` (`hMixO` is `TT.gammaHonesty`, `hMixS` is
`aslotTwoShift_mixedSliceHon`, and the `ℋ⁰`-honesty of `D_z (Aof Ψ)` is `hkMem_zero_Dz_Aof`). -/
theorem aof_tendsto_zero {α : ℝ} {F Ψ : ℝ → ℝ → ℝ}
    (hα : 0 < α) (hα4 : α ≤ 1 / 4) (h : Work.FTS.EllipticEst.TT.EllWeakPos α 2 F Ψ) :
    ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi 0)),
      Filter.Tendsto (fun θ => z * Work.Spaces.pz (Aof Ψ) z θ)
          (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) ∧
      Filter.Tendsto (fun θ => z * Work.Spaces.pz (Aof Ψ) z θ)
          (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) := by
  have hAe : Work.FTS.EllipticEst.H2W.Ae.AeData α (Aof Ψ)
      (Work.FTS.EllipticEst.H2W.Gof F) :=
    Work.FTS.EllipticEst.H2W.AeDataAof α F Ψ hα hα4 h
  exact aslotTwoShift_aeDzTrace_gam α (Aof Ψ) (Work.FTS.EllipticEst.H2W.Gof F) hAe
    (hkMem_zero_Dz_Aof h) (aslotTwoShift_mixedSliceHon hα hα4 h)
    (Work.FTS.EllipticEst.TT.gammaHonesty hα hα4 h)

/-- **Membership transfer to the pure radial slots of `HkIntegrand α 2`.**  For a datum with
`HkMem α 2 f`, every pure slot `D_z^j f` with `j ≤ 2` is honestly in `ℋ⁰`. -/
theorem hkMem_zero_DzIter {α : ℝ} {f : ℝ → ℝ → ℝ} (hf : Work.FTS.EllipticEst.SmoothOpen f)
    (h : Work.Spaces.HkMem α 2 f) :
    ∀ j : ℕ, j ≤ 2 → Work.Spaces.HkMem α 0 (Work.Spaces.DzIter j f) := by
  intro j hj
  refine HkMem_zero_of_pointwise (c := 1) zero_le_one (hf.DzIter j) h
    (fun z θ hz hθ hlt => ?_)
  rw [HkIntegrand_zero_apply]
  simpa only [one_mul] using Work.Spaces.sq_le_HkIntegrand_z α 2 f z θ j hj

/-- **The `θ`-endpoint rate of the slices of the twisted datum `Aof Ψ`** for a level-`2` weak
datum: for every `z > 0` the slice `θ ↦ z²∂_z²Ψ (z,θ)` tends to `0` at `(π/2)⁻` **with at least
the linear rate** `π/2 - θ`.

This is the quantitative form of the input (M-II) of
`Submission/Work/FTS/EllipticEst/H2W/AeAux/NOTES_AeI1_crux.md` (the vanishing of the one-sided
`θ`-fluxes needed by the angular integration by parts).  It follows from the *proved*
`H2W.AeProof.sliceRightTendsto_raw` applied to the twisted datum `(Aof Ψ, Gof F)`, which is again
a datum of the a.e. class by `H2W.AeDataAof`; note that no extra hypothesis is needed — the
`ℋ⁰`-honesty of the three fields of `AeData` is exactly what that lemma consumes. -/
theorem aof_slice_rate {α : ℝ} {F Ψ : ℝ → ℝ → ℝ}
    (hα : 0 < α) (hα4 : α ≤ 1 / 4) (h : Work.FTS.EllipticEst.TT.EllWeakPos α 2 F Ψ) :
    ∀ z : ℝ, 0 < z → ∃ K : ℝ, 0 ≤ K ∧
      ∀ᶠ θ in nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2)),
        |Aof Ψ z θ| ≤ K * (Real.pi / 2 - θ) := by
  intro z hz
  have hA : Work.FTS.EllipticEst.H2W.Ae.AeData α (Aof Ψ) (Work.FTS.EllipticEst.H2W.Gof F) :=
    Work.FTS.EllipticEst.H2W.AeDataAof α F Ψ hα hα4 h
  exact (Work.FTS.EllipticEst.H2W.AeProof.sliceRightTendsto_raw α
    (Work.FTS.EllipticEst.H2W.Gof F) (Aof Ψ) hα hα4 hA.eq hA.smooth hA.memG hA.memRad2
    hA.memAng2 z hz).2

/-- **The `θ`-endpoint rate of the slices of every radial shift `D_z^j Ψ`, `j ≤ 2`**, in the weak
class `EllWeakPos α 2 F Ψ`: for every `z > 0` the slice `θ ↦ D_z^j Ψ (z,θ)` vanishes at `(π/2)⁻`
with at least the linear rate `π/2 - θ`.

This is the quantitative strengthening of the *proved* `Mine.DzSliceRightLimit` and it is the
input (M-II) of `H2W/AeAux/NOTES_AeI1_crux.md` in the form an angular integration by parts needs
(the flux `sin(2θ)^{-η}(D_z^jΨ)²` then tends to `0`).  The proof is a direct application of the
*proved* `H2W.AeProof.sliceRightTendsto_raw` to the radially shifted datum `(D_z^j F, D_z^j Ψ)`,
which satisfies the same equation by `TT.bslOp_DzIter_eq` (the paper's "the equation commutes with
`D_R` derivatives"), with the three `ℋ⁰`-honesties supplied by

* `D_z^j F` — pure slot `j` of `HkMem α 2 F`;
* `z²∂_z²(D_z^j Ψ) = D_z^j (z²∂_z²Ψ)` — pure slot `j` of `HkMem α 2 (Aof Ψ)`, transported along
  the open-quadrant identity `DzAmgm.ZsqPz2Comm` by `Cert.GbarSin.HkMem_congr_Q0`;
* `∂_θ²(D_z^j Ψ) = D_z^j (∂_θ²Ψ)` — pure slot `j` of `HkMem α 2 (∂_θ²Ψ)`, transported by
  `H2W.pthIter2_DzIter_comm`. -/
theorem dzIter_slice_rate {α : ℝ} {F Ψ : ℝ → ℝ → ℝ}
    (hα : 0 < α) (hα4 : α ≤ 1 / 4) (h : Work.FTS.EllipticEst.TT.EllWeakPos α 2 F Ψ) :
    ∀ j : ℕ, j ≤ 2 → ∀ z : ℝ, 0 < z → ∃ K : ℝ, 0 ≤ K ∧
      ∀ᶠ θ in nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2)),
        |Work.Spaces.DzIter j Ψ z θ| ≤ K * (Real.pi / 2 - θ) := by
  intro j hj z hz
  obtain ⟨hsmΨ, hsmA, hsmB⟩ :=
    (Work.FTS.EllipticEst.remov.smoothOpen_slices_weak h j).2
  obtain ⟨hF0, -, hA0, hB0⟩ :=
    Work.FTS.EllipticEst.remov.smoothOpen_slices_weak h 0
  have hF0' : Work.FTS.EllipticEst.SmoothOpen F := hF0
  have hA0' : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) := hA0
  have hB0' : Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.pthIter 2 Ψ) := hB0
  have hΨ : Work.FTS.EllipticEst.SmoothOpen Ψ :=
    Work.FTS.EllipticEst.smoothOpen_of_forall h.smooth
  have hmF : Work.Spaces.HkMem α 0 (Work.Spaces.DzIter j F) :=
    hkMem_zero_DzIter hF0' h.memF j hj
  have hmA : Work.Spaces.HkMem α 0
      (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 (Work.Spaces.DzIter j Ψ) z θ) :=
    Work.FTS.EllipticEst.Cert.GbarSin.HkMem_congr_Q0 α 0
      (hkMem_zero_DzIter hA0' h.memA j hj)
      (fun z hz' θ hθ => by
        have h := Work.FTS.EllipticEst.DzAmgm.ZsqPz2Comm Ψ hΨ j 0
          (show (z, θ) ∈ Work.FTS.EllipticEst.Q0 from ⟨hz', hθ.1, hθ.2⟩)
        simpa only [Function.uncurry, Work.Spaces.mixed_zero_right] using h.symm)
  have hmB : Work.Spaces.HkMem α 0 (Work.Spaces.pthIter 2 (Work.Spaces.DzIter j Ψ)) :=
    Work.FTS.EllipticEst.Cert.GbarSin.HkMem_congr_Q0 α 0
      (hkMem_zero_DzIter hB0' h.memB j hj)
      (fun z hz' θ hθ => by
        have h := Work.EllipticEst.H2W.pthIter2_DzIter_comm hΨ j
          (show (z, θ) ∈ Work.FTS.EllipticEst.Q0 from ⟨hz', hθ.1, hθ.2⟩)
        simpa only [Function.uncurry, Work.Spaces.mixed_zero_right] using h.symm)
  exact (Work.FTS.EllipticEst.H2W.AeProof.sliceRightTendsto_raw α
    (Work.Spaces.DzIter j F) (Work.Spaces.DzIter j Ψ) hα hα4
    (Work.FTS.EllipticEst.TT.bslOp_DzIter_eq α F Ψ j h.smooth h.eq)
    ((Work.FTS.EllipticEst.smoothOpen_iff_forall (Work.Spaces.DzIter j Ψ)).mp hsmΨ)
    hmF hmA hmB z hz).2

/-- **The two one-sided endpoint trace bounds, combined.**  This is exactly the hypothesis `hTB`
consumed by `Prop.thetaInterpCoreOfTraceBounds` — the flux-limit assembly of the 1-D open-class
angular interpolation `Work.EllipticEst.Core.i0Aux.thetaInterpCore` — and it is the conjunction of
the two proved bounds `Prop.traceBoundLeft` (`θ = 0⁺`) and `Prop.traceBoundRight` (`θ = (π/2)⁻`).
It closes the "trace bound" gap recorded in
`Submission/Work/EllipticEst/Core/i0Aux/NOTES_thetaInterpCore_state.md` §2. -/
theorem traceBounds : ∃ C : ℝ, 0 < C ∧ ∀ (f : ℝ → ℝ) (F₀ L₀ F₁ L₁ : ℝ),
    ContDiffOn ℝ 2 f (Set.Ioo 0 (Real.pi / 2)) →
    Filter.Tendsto f (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds F₀) →
    Filter.Tendsto (deriv f) (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds L₀) →
    Filter.Tendsto f (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds F₁) →
    Filter.Tendsto (deriv f) (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds L₁) →
    MeasureTheory.IntegrableOn (fun θ : ℝ => (f θ) ^ 2 * Work.FTS.EllipticEst.thEta θ) Work.Spaces.Iθ →
    MeasureTheory.IntegrableOn (fun θ : ℝ => (deriv f θ) ^ 2 * Work.FTS.EllipticEst.thEta θ) Work.Spaces.Iθ →
    MeasureTheory.IntegrableOn (fun θ : ℝ => (deriv (deriv f) θ) ^ 2 * Work.FTS.EllipticEst.thEta θ) Work.Spaces.Iθ →
    max (F₀ * L₀) 0 + F₀ ^ 2 + max (-(F₁ * L₁)) 0 + F₁ ^ 2
      ≤ C * ((∫ θ in Work.Spaces.Iθ, (f θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)
          + Real.sqrt ((∫ θ in Work.Spaces.Iθ, (f θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)
              * (∫ θ in Work.Spaces.Iθ, (deriv (deriv f) θ) ^ 2 * Work.FTS.EllipticEst.thEta θ))) := by
  obtain ⟨C₁, hC₁, h₁⟩ := traceBoundLeft
  obtain ⟨C₂, hC₂, h₂⟩ := traceBoundRight
  refine ⟨C₁ + C₂, by linarith, ?_⟩
  intro f F₀ L₀ F₁ L₁ hcd hT₀ hT₀' hT₁ hT₁' hI₀ hI₁ hI₂
  have h1 := h₁ f F₀ L₀ hcd hT₀ hT₀' hI₀ hI₁ hI₂
  have h2 := h₂ f F₁ L₁ hcd hT₁ hT₁' hI₀ hI₁ hI₂
  have h3 : max (F₀ * L₀) 0 + F₀ ^ 2 + (max (-(F₁ * L₁)) 0 + F₁ ^ 2)
      ≤ (C₁ + C₂) * ((∫ θ in Work.Spaces.Iθ, (f θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)
          + Real.sqrt ((∫ θ in Work.Spaces.Iθ, (f θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)
              * (∫ θ in Work.Spaces.Iθ, (deriv (deriv f) θ) ^ 2 * Work.FTS.EllipticEst.thEta θ))) := by
    nlinarith [h1, h2]
  linarith [h3]

/-- **The 1-D open-class weighted angular interpolation** — the statement of the (still `sorry` in
place) node `Work.EllipticEst.Core.i0Aux.thetaInterpCore`, obtained here **unconditionally** by
combining the proved endpoint trace bounds `Prop.traceBounds` with the flux-limit assembly
`Prop.thetaInterpCoreOfTraceBounds`.

    `∫_{Iθ} (f')²σ ≤ C (∫_{Iθ} f²σ + √(∫_{Iθ} f²σ · ∫_{Iθ} (f'')²σ))`,  `σ = sin(2θ)^{-η}`,

for `f` of class `C²` on the *open* interval `(0,π/2)` whose endpoint *values* are `0` (the
endpoint *traces* are not assumed to vanish).  This is the 1-D angular input of the "Core route"
to the mixed weighted interpolation (`Core.interpMixedGen` / `InterpOpen`), hence of one of the
two inputs of `Prop.aslotTwoShift`. -/
theorem thetaInterpCoreFts : ∃ C : ℝ, 0 < C ∧ ∀ f : ℝ → ℝ,
    ContDiffOn ℝ 2 f (Set.Ioo 0 (Real.pi / 2)) →
    f 0 = 0 → f (Real.pi / 2) = 0 →
    MeasureTheory.IntegrableOn (fun θ : ℝ => (f θ) ^ 2 * Work.FTS.EllipticEst.thEta θ) Work.Spaces.Iθ →
    MeasureTheory.IntegrableOn (fun θ : ℝ => (deriv f θ) ^ 2 * Work.FTS.EllipticEst.thEta θ) Work.Spaces.Iθ →
    MeasureTheory.IntegrableOn (fun θ : ℝ => (deriv (deriv f) θ) ^ 2 * Work.FTS.EllipticEst.thEta θ) Work.Spaces.Iθ →
    (∫ θ in Work.Spaces.Iθ, (deriv f θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)
      ≤ C * ((∫ θ in Work.Spaces.Iθ, (f θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)
          + Real.sqrt ((∫ θ in Work.Spaces.Iθ, (f θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)
              * (∫ θ in Work.Spaces.Iθ, (deriv (deriv f) θ) ^ 2 * Work.FTS.EllipticEst.thEta θ))) :=
  thetaInterpCoreOfTraceBounds traceBounds

/-! ## The assembly of the target from the level-`0` estimate -/

/-- The `(0,1)`-slot of `Ab (D_zΨ)` is the `(1,1)`-slot of `Ab Ψ` on the open quadrant
(`Ab = z²∂_z²` and `D_θ` commute with `D_z`). -/
theorem mixed01_Ab_Dz_eqOn {Ψ : ℝ → ℝ → ℝ} (hΨ : Work.FTS.EllipticEst.SmoothOpen Ψ) :
    Work.FTS.EllipticEst.AgreeOnQ (Work.Spaces.mixed 0 1 (Ab (Work.Spaces.DzIter 1 Ψ)))
      (Work.Spaces.mixed 1 1 (Ab Ψ)) := by
  intro z θ hz hθ hlt
  have hA : Work.FTS.EllipticEst.SmoothOpen (Ab Ψ) := smoothOpen_zsq_mul (hΨ.pzIter 2)
  have h1 : Work.Spaces.Dth (Ab (Work.Spaces.DzIter 1 Ψ)) z θ
      = Work.Spaces.Dth (Work.Spaces.DzIter 1 (Ab Ψ)) z θ :=
    (Ab_Dz_eqOn hΨ).Dth z θ hz hθ hlt
  have h2 : Work.Spaces.Dth (Work.Spaces.DzIter 1 (Ab Ψ)) z θ
      = Work.Spaces.Dz (Work.Spaces.Dth (Ab Ψ)) z θ :=
    Dth_Dz_eqOn hA z θ hz hθ hlt
  simpa only [Work.Spaces.mixed, Work.Spaces.DthIter_succ, Work.Spaces.DthIter_zero,
    Work.Spaces.DzIter_succ, Work.Spaces.DzIter_zero] using h1.trans h2

/-- **`Prop.aslotTwoShift`, assembled from the level-`0` estimate `h0`.**

The two inputs of the tree's `Prop.aShiftSlotTop` are (i) the level-`0` estimate on the radially
shifted data (`TopSlotTwoFts.ShiftZeroSlots2 h0`, used through `HkSq_zero_Ab_DzIter_le` and
`HkSq_zero_DzIter_Bb_le`) and (ii) the mixed weighted interpolation
`Prop.mixedSlotInterpEta`.  Here the conclusion of `aShiftSlotTop` — the *square-root* form
`α²√(Tk α 1 (Ab (D_zΨ))) ≤ C |F|_{ℋ²}` — is squared and the left-hand side is identified with the
target's `α⁴·L2Sq (mixed 1 1 (z²∂_z²Ψ) · Wt α)`.

So the target is reduced to the single level-`0` estimate `∃ C, TT.EllWeak0 C`. -/
theorem aslotTwoShift_of_h0 (h0 : ∃ C₀ : ℝ, 0 < C₀ ∧ Work.FTS.EllipticEst.TT.EllWeak0 C₀) :
    ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (F Ψ : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 / 4 →
      Work.FTS.EllipticEst.TT.EllWeakPos α 2 F Ψ →
      α ^ 4 * Work.Spaces.L2Sq (fun z θ =>
          Work.Spaces.mixed 1 1 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ
            * Work.Spaces.Wt α z θ)
        ≤ C * Work.Spaces.HkSq α 2 F := by
  obtain ⟨C₁, hC₁pos, hA⟩ := aShiftSlotTop h0
  refine ⟨C₁ ^ 2, by positivity, fun α F Ψ hα hα4 h => ?_⟩
  have hΨ : Work.FTS.EllipticEst.SmoothOpen Ψ := smoothOpen_of_forall h.smooth
  have hb := hA α F Ψ hα hα4 h
  have hTknn : 0 ≤ Work.FTS.EllipticEst.remov.Step.Tk α 1 (Ab (Work.Spaces.DzIter 1 Ψ)) :=
    Work.FTS.EllipticEst.remov.Step.Tk_nonneg α 1 _
  -- square the square-root bound
  have hsq := pow_le_pow_left₀ (mul_nonneg (sq_nonneg α) (Real.sqrt_nonneg _)) hb 2
  rw [mul_pow, Real.sq_sqrt hTknn, mul_pow] at hsq
  have hnorm : Work.Spaces.HkNorm α 2 F ^ 2 = Work.Spaces.HkSq α 2 F := by
    rw [Work.Spaces.HkNorm, Real.sq_sqrt (Work.Spaces.HkSq_nonneg α 2 F)]
  rw [hnorm] at hsq
  -- identify `Tk α 1 (Ab (D_zΨ))` with the target's left-hand side
  have hconv : Work.FTS.EllipticEst.remov.Step.Tk α 1 (Ab (Work.Spaces.DzIter 1 Ψ))
      = Work.Spaces.L2Sq (fun z θ => Work.Spaces.mixed 1 1
          (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ * Work.Spaces.Wt α z θ) := by
    rw [show Work.FTS.EllipticEst.remov.Step.Tk α 1 (Ab (Work.Spaces.DzIter 1 Ψ))
        = Work.Spaces.L2Sq (fun z θ => Work.Spaces.mixed 0 1
            (Ab (Work.Spaces.DzIter 1 Ψ)) z θ * Work.Spaces.Wt α z θ) from rfl]
    exact L2Sq_congr_open (fun z θ hz hθ hlt =>
      congrArg (fun r => r * Work.Spaces.Wt α z θ) (mixed01_Ab_Dz_eqOn hΨ z θ hz hθ hlt))
  rw [hconv] at hsq
  have hpow : (α ^ 2) ^ 2 = α ^ 4 := by ring
  rw [hpow] at hsq
  exact hsq

/-- **The level-`0` estimate `∃ C, TT.EllWeak0 C` from the `I₁` coercivity `AngAWeak.AeI1`.**

`Final.ellWeak0_of_steps` (`Final/Level0.lean`, proved) assembles `TT.EllWeak0` from the three
Steps of `prop:H2` in the class `H2W.Ae.AeData`: Step 1 (`AeS1.step1_of` applied to the proved
`AeS1.unwEnergyD`, `Final.aeSigmaUpD`, `Dispatch.aeSigmaEnergyD`), Step 2 (the proved
`Cores.step2Ae_core`, whose only non-proved input is `AngAWeak.AeI1`) and Step 3
(`Dispatch.step3AeD`).  This file supplies Step 2 directly, so the tree's `sorry` in
`Dispatch/step2AeD` (`step2AeI1_holds`) is bypassed.

Hence `h0` and the `I₁` coercivity are *the same* node. -/
theorem h0_of_AeI1 (hI1 : Work.FTS.EllipticEst.AngAWeak.AeI1) :
    ∃ C : ℝ, 0 < C ∧ Work.FTS.EllipticEst.TT.EllWeak0 C :=
  Work.FTS.EllipticEst.Final.ellWeak0_of_steps
    (Work.FTS.EllipticEst.AeS1.step1_of Work.FTS.EllipticEst.AeS1.unwEnergyD
      Work.FTS.EllipticEst.Final.aeSigmaUpD
      Work.FTS.EllipticEst.Dispatch.aeSigmaEnergyD)
    (Work.FTS.EllipticEst.Cores.step2Ae_core
      (fun α u G h => Work.FTS.EllipticEst.Cores.AeStep2Aux.aeUHk_mem α u G h)
      (fun α u G h _ => Work.FTS.EllipticEst.AngAWeak.hkMem_grad_of h)
      Work.FTS.EllipticEst.Cores.AeStep2Aux.aeUHk_bnd
      hI1
      Work.FTS.EllipticEst.Cores.AeStep2Aux.aeI4_open)
    Work.FTS.EllipticEst.Dispatch.step3AeD

/-- **`Prop.aslotTwoShift` from the `I₁` coercivity.**  Composition of `h0_of_AeI1` with
`aslotTwoShift_of_h0`: the only remaining inputs of the target are `AngAWeak.AeI1` and the mixed
weighted interpolation inside `Prop.aShiftSlotTop`. -/
theorem aslotTwoShift_of_AeI1 (hI1 : Work.FTS.EllipticEst.AngAWeak.AeI1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (F Ψ : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 / 4 →
      Work.FTS.EllipticEst.TT.EllWeakPos α 2 F Ψ →
      α ^ 4 * Work.Spaces.L2Sq (fun z θ =>
          Work.Spaces.mixed 1 1 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ
            * Work.Spaces.Wt α z θ)
        ≤ C * Work.Spaces.HkSq α 2 F :=
  aslotTwoShift_of_h0 (h0_of_AeI1 hI1)

theorem aslotTwoShift : ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (F Ψ : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 / 4 →
      Work.FTS.EllipticEst.TT.EllWeakPos α 2 F Ψ →
      α ^ 4 * Work.Spaces.L2Sq (fun z θ =>
          Work.Spaces.mixed 1 1 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ
            * Work.Spaces.Wt α z θ)
        ≤ C * Work.Spaces.HkSq α 2 F := by sorry

end Work.FTS.EllipticEst.Prop