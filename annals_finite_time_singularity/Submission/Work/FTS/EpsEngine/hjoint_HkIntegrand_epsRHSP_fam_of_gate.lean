/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Submission/Work/FTS/EpsEngine/hjoint_HkIntegrand_epsRHSP_fam_of_gate.lean`

**The joint (Horizon × quadrant) measurability of the `H^k`-integrand of the projected
`ε`-scheme's right-hand side.**  Along a family `g` whose slices lie in the `X`-ball and are
`EpsSq`-Lipschitz in the fake time, the function

`(s,z,θ) ↦ HkIntegrand α k (epsRHSP α ρ ε Φs E g s) z θ`

is a.e. strongly measurable for the measure
`(volume.restrict (Icc 0 δ)) ⊗ (volume.restrict Iz) ⊗ (volume.restrict Iθ)`.

This is the measurability input that the Fubini/dominated-convergence bookkeeping of the
`ℋ^k`-estimates needs (the sibling file `hmeas_slot_epsRHSP_fam_of_gate.lean` provides only the
*sliced* statement, and a fixed section of a jointly measurable family says nothing about the
sections of its derivatives).

The route is deliberately short, and consists of two steps.

* **Carathéodory at the level of the whole integrand.**  The `H^k`-integrand is a finite sum of
  squares of weighted derivative slots, so for a *fixed* `(z,θ)` the map
  `s ↦ HkIntegrand α k (Feps (slice g s)) z θ` is a.e. strongly measurable as soon as each slot
  `s ↦ mixed j i (Feps (slice g s)) z θ` is — that is `aesm_HkIntegrand_of_slots` (pure finite
  bookkeeping, in the sibling module `aesm_HkIntegrand_of_slots.lean`).  The slots are supplied by
  the sibling gate `hmeas_slot_epsRHSP_fam_of_gate`; the replacement of `epsRHSP … g s` by its
  slice-determined value `Feps … (slice g s)` is the definitional identity
  `epsRHSP_eq_Feps_slice`.
* **Continuity in `(z,θ)` on the open quadrant.**  For `s` in the horizon each slice is `C^∞` on
  the open quadrant (`smoothOpen_Feps_of_classC` from the `XBall` data), hence the integrand is
  continuous there (`SmoothOpen.continuousOn_HkIntegrand`).  The integrand is cut off to `0`
  outside the horizon and outside the open quadrant — the discarded set is null for the target
  measure — and `aesm_uncurry_restricted` (Carathéodory relative to the horizon) then produces
  joint measurability for `(volume.restrict (Icc 0 δ)) ⊗ volume`; shrinking the angular factor to
  `(volume.restrict Iz) ⊗ (volume.restrict Iθ)` (`Measure.prod_mono`) and comparing a.e. finishes.

No `z`- or `θ`-uniform slot bound is used anywhere: the statement only asks for measurability, and
at an interior point every slot is honest.

Everything here is fully proved, with no extra axioms beyond `propext`, `Classical.choice`
and `Quot.sound`.
-/
import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.EpsEngine.hmeas_slot_epsRHSP_fam_of_gate
import Submission.Work.FTS.EpsEngine.aesm_uncurry_restricted
import Submission.Work.FTS.EpsEngine.LocalStepXBall
import Submission.Work.FTS.EpsEngine.SmoothOpenFeps
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.EpsEngine.aesm_HkIntegrand_of_slots

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EpsEngine

open MeasureTheory Set Filter
open scoped Real Topology

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-! ## The theorem -/

theorem hjoint_HkIntegrand_epsRHSP_fam_of_gate {α C₀ R Ce Cs Lw δ : ℝ} {ρ : ℝ × ℝ → ℝ}
    {Φs : Work.FTS.Galerkin.Fn} {E : Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn}
    {ε : ℝ} {g : Work.FTS.Galerkin.Fam} {k : ℕ}
    (hα : α ∈ Set.Ioc 0 1) (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hEll : ∀ u : Work.FTS.Galerkin.Fn, Work.FTS.ClassC.ClassC α u →
      Work.FTS.VocabO.EllPkgGo α Ce u (E u) ∧ Work.FTS.ClassC.EllPkgK α 6 Ce u (E u))
    (hstar : Work.FTS.VocabO2.StarPkgo2 α Cs Φs)
    (hml : Work.FTS.StrongEps.MuLamOK α C₀ Φs E) (hR : 0 ≤ R) (hLw : 0 ≤ Lw)
    (hP : ∀ s ∈ Set.Icc 0 δ, Work.FTS.EpsEngine.XBall α ρ ε R C₀ (Work.FTS.Galerkin.slice g s))
    (hEq : ∀ s ∈ Set.Icc 0 δ, ∀ t ∈ Set.Icc 0 δ, Work.FTS.StrongEps.EpsSq α (fun z θ =>
      Work.FTS.Galerkin.slice g s z θ - Work.FTS.Galerkin.slice g t z θ) ≤ Lw * (s - t) ^ 2) :
    MeasureTheory.AEStronglyMeasurable
      (fun p : ℝ × ℝ × ℝ => Work.Spaces.HkIntegrand α k
        (Work.FTS.StrongEps.epsRHSP α ρ ε Φs E g p.1) p.2.1 p.2.2)
      ((MeasureTheory.volume.restrict (Set.Icc 0 δ)).prod
        ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ))) := by
  classical
  -- the slice-determined profile family
  set B : ℝ → ℝ → ℝ → ℝ := fun s => Feps α ρ ε Φs E (Work.FTS.Galerkin.slice g s) with hB
  -- ## Step 1: the slotwise measurability in the fake time (the sibling gate)
  have hslot : ∀ (j i : ℕ) (z θ : ℝ), 0 < z → θ ∈ Set.Ioo 0 (Real.pi / 2) →
      MeasureTheory.AEStronglyMeasurable (fun s : ℝ => Work.Spaces.mixed j i (B s) z θ)
        (MeasureTheory.volume.restrict (Set.Icc 0 δ)) := by
    intro j i z θ hz hθ
    have h := hmeas_slot_epsRHSP_fam_of_gate hα hρ hε hε1 hEll hstar hml hR hLw hP hEq
      j i hz hθ
    simpa only [hB, epsRHSP_eq_Feps_slice] using h
  -- ## Step 2: each slice is `C^∞` on the open quadrant
  have hsm : ∀ s ∈ Set.Icc 0 δ, Work.FTS.EllipticEst.SmoothOpen (B s) := fun s hs =>
    smoothOpen_Feps_of_classC (α := α) (Ce := Ce) (Cs := Cs) (ρ := ρ) (Φs := Φs) (E := E)
      (ε := ε) (u := Work.FTS.Galerkin.slice g s) hα hρ hε hEll hstar (hP s hs).classC
  -- ## Step 3: the truncated integrand family
  let H : ℝ → ℝ → ℝ → ℝ := fun s z θ =>
    if s ∈ Set.Icc 0 δ then
      (if (z, θ) ∈ Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2) then
        Work.Spaces.HkIntegrand α k (B s) z θ
      else 0)
    else 0
  -- ### continuity on the open quadrant, for every `s ∈ [0,δ]`
  have hcont : ∀ s ∈ Set.Icc 0 δ, ContinuousOn (fun q : ℝ × ℝ => H s q.1 q.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := by
    intro s hs
    have hq : ContinuousOn (fun q : ℝ × ℝ => Work.Spaces.HkIntegrand α k (B s) q.1 q.2)
        (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := (hsm s hs).continuousOn_HkIntegrand α k
    refine hq.congr ?_
    intro q hq'
    have hq'' : (q.1, q.2) ∈ Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2) := hq'
    dsimp only [H]
    rw [if_pos hs, if_pos hq'']
  -- ### vanishing outside the open quadrant
  have hzero : ∀ s ∈ Set.Icc 0 δ, ∀ q : ℝ × ℝ,
      q ∉ Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2) → H s q.1 q.2 = 0 := by
    intro s hs q hq
    have hq' : ¬ ((q.1, q.2) ∈ Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := hq
    dsimp only [H]
    rw [if_pos hs, if_neg hq']
  -- ### measurability in `s`, at every fixed `(z,θ)`
  have hmeas : ∀ q : ℝ × ℝ, MeasureTheory.AEStronglyMeasurable (fun s : ℝ => H s q.1 q.2)
      (MeasureTheory.volume.restrict (Set.Icc 0 δ)) := by
    intro q
    by_cases hq : q ∈ Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)
    · have hslotq : MeasureTheory.AEStronglyMeasurable
          (fun s : ℝ => Work.Spaces.HkIntegrand α k (B s) q.1 q.2)
          (MeasureTheory.volume.restrict (Set.Icc 0 δ)) :=
        aesm_HkIntegrand_of_slots (fun j i => hslot j i q.1 q.2 hq.1 hq.2)
      have h1 : MeasureTheory.AEStronglyMeasurable
          ((Set.Icc 0 δ).indicator (fun s : ℝ => Work.Spaces.HkIntegrand α k (B s) q.1 q.2))
          MeasureTheory.volume :=
        MeasAlt.aesm_indicator_of_aesm_restrict measurableSet_Icc hslotq
      refine (h1.mono_measure Measure.restrict_le_self).congr ?_
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with s hs
      rw [Set.indicator_of_mem hs]
      have hq'' : (q.1, q.2) ∈ Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2) := hq
      dsimp only [H]
      rw [if_pos hs, if_pos hq'']
    · have hconst : (fun s : ℝ => H s q.1 q.2) = fun _ : ℝ => (0 : ℝ) := by
        funext s
        by_cases hs : s ∈ Set.Icc 0 δ
        · have hq' : ¬ ((q.1, q.2) ∈ Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := hq
          dsimp only [H]
          rw [if_pos hs, if_neg hq']
        · dsimp only [H]
          rw [if_neg hs]
      rw [hconst]
      exact aestronglyMeasurable_const
  -- ## Step 4: Carathéodory on the horizon
  have hbig := aesm_uncurry_restricted (A := Set.Icc 0 δ) measurableSet_Icc (g := H)
    hcont hzero hmeas
  have hle : (MeasureTheory.volume.restrict (Set.Icc 0 δ)).prod
        ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ))
      ≤ (MeasureTheory.volume.restrict (Set.Icc 0 δ)).prod MeasureTheory.volume :=
    Measure.prod_mono le_rfl
      (Measure.prod_mono Measure.restrict_le_self Measure.restrict_le_self)
  refine (hbig.mono_measure hle).congr ?_
  -- ## Step 5: a.e. comparison with the statement's integrand
  -- a.e. `θ` lies in the open interval, a.e. `z` is positive
  have hz_ae : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz), z ∈ Set.Ioi (0 : ℝ) := by
    have h : MeasureTheory.volume.restrict Work.Spaces.Iz
        = MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ)) := by
      rw [Work.Spaces.Iz]
      exact (Measure.restrict_congr_set
        (MeasureTheory.Ioi_ae_eq_Ici (μ := MeasureTheory.volume) (a := (0 : ℝ)))).symm
    rw [h]
    exact MeasureTheory.ae_restrict_mem measurableSet_Ioi
  have hth_ae : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := by
    have h : MeasureTheory.volume.restrict Work.Spaces.Iθ
        = MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
      rw [Work.Spaces.Iθ]
      exact (Measure.restrict_congr_set
        (MeasureTheory.Ioo_ae_eq_Icc (μ := MeasureTheory.volume) (a := (0 : ℝ))
          (b := Real.pi / 2))).symm
    rw [h]
    exact MeasureTheory.ae_restrict_mem measurableSet_Ioo
  have hQae : ∀ᵐ q ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
      (MeasureTheory.volume.restrict Work.Spaces.Iθ)),
      q ∈ Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2) := by
    refine (Measure.ae_prod_mem_iff_ae_ae_mem
      (s := Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2))
      ((isOpen_Ioi.prod isOpen_Ioo).measurableSet)).mpr ?_
    filter_upwards [hz_ae] with z hz
    filter_upwards [hth_ae] with θ hθ
    exact ⟨hz, hθ⟩
  have haeA : ∀ᵐ p ∂((MeasureTheory.volume.restrict (Set.Icc 0 δ)).prod
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ))), p.1 ∈ Set.Icc 0 δ := by
    refine (Measure.ae_prod_mem_iff_ae_ae_mem
      (s := {p : ℝ × (ℝ × ℝ) | p.1 ∈ Set.Icc 0 δ})
      (measurableSet_Icc.preimage measurable_fst)).mpr ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with s hs
    exact Filter.Eventually.of_forall fun q => hs
  have haeQ : ∀ᵐ p ∂((MeasureTheory.volume.restrict (Set.Icc 0 δ)).prod
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ))),
      (p.2.1, p.2.2) ∈ Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2) := by
    refine (Measure.ae_prod_mem_iff_ae_ae_mem
      (s := {p : ℝ × (ℝ × ℝ) | (p.2.1, p.2.2) ∈ Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)})
      ((isOpen_Ioi.prod isOpen_Ioo).measurableSet.preimage measurable_snd)).mpr ?_
    refine Filter.Eventually.of_forall fun x => ?_
    filter_upwards [hQae] with q hq
    exact hq
  filter_upwards [haeA, haeQ] with p hpA hpQ
  dsimp only [H]
  rw [if_pos hpA, if_pos hpQ, hB, epsRHSP_eq_Feps_slice]

end Work.FTS.EpsEngine
