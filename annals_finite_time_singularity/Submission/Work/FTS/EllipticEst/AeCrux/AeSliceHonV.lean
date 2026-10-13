import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.FTS.EllipticEst.H2W.Ae.Defs
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.H2W.AeMixedAeMem
import Submission.Work.FTS.EllipticEst.AngAWeak.Basic
import Submission.Work.FTS.EllipticEst.AeCrux.AeVLib.Main
import Submission.Work.FTS.EllipticEst.AeCrux.AeVGlobalFin2

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

namespace Work.FTS.EllipticEst.AeCrux

open MeasureTheory Set Filter
open scoped Real Topology ENNReal

local notation "Iθ" => Work.Spaces.Iθ
local notation "Iz" => Work.Spaces.Iz

set_option linter.unusedSimpArgs false

/-
The a.e. `σ`-slice honesty of the mixed slot `V = z ∂_z∂_θu = ∂_θ(z ∂_zu)` for a datum of the
a.e. class `AeData α u G` (plus the radial honesty, itself derivable from `AeData` by
`Dispatch.hkMem_gradUD`).  This is the *first conjunct* of `Cores/AeStep2Aux/aeMixedAe_mem` and one
of the two hypotheses of `remov/AeI1PaperOfHonest`, hence a shared bottleneck of the two remaining
`Ae` leaves of `propHkWeakFts`.

## The proof in this file (the "flat heavy" route)

The target is *proved* by the body of `AeSliceHonV` below.  The route is the tree's
two-dimensional (frequency + angular Agmon) interpolation: `Work.FTS.EllSol.HeavyFlat.FlatHeavy`
(from `Work.FTS.EllSol.Shift2Flat.mixedSlotFiniteness`) gives the flat statement — for `u` of
class `C²` on the strip with vanishing end-point *values* whose three `σ_η`-weighted shifted
diagonal slots are integrable, the mixed slot `(∂_θ(∂_t-b)u)² σ_η` has finite `∫⁻` — proved per
frequency by the angular Agmon inequality (`Trunc.curlAgmon`), Plancherel in `t`
(`Shift2Flat.niceRangePlanch`) and Cauchy–Schwarz in the frequency, the general datum being
reached by exact ODE truncation and Fatou.  `HeavyFlat.omOfFlat` transfers it to the logarithmic
weight `Ω(t) = w(e^t)²·e^t`, and the pull-back `z = e^t` (`AeCrux/AeVGlobalFin2.lean`,
`AeCrux/AeVLib/*`) identifies the three `σ_η`-slots of `t ↦ u(e^t,·)` with the `HkMem α 0`-slots
of `D_zu`, `z²∂_zzu`, `∂_θ²u`, i.e. with `hU`, `h.memRad2`, `h.memAng2`.  Finally Tonelli
(`lintegral_prod`) plus `lintegral_box_exp_rev` give the finiteness of the `θ`-`∫⁻` of the
level-`0` `HkIntegrand` of the mixed slot for a.e. `z > 0`, and since
`HkIntegrand α 0 (D_z(pth u)) z θ = w(z)²·((z ∂_z∂_θu)²·σ_η(θ))` with `w z ≠ 0` for `z > 0`,
`lintegral_ofReal_ne_top_iff_integrable` converts this into the stated `IntegrableOn`.

No per-`z` argument is possible (the slicewise version is FALSE,
`AngAWeak/NOTES_aeMixedHon_FALSE.md`).  The three *proved* reductions below state the same
content against the tree's older interfaces; see
`NOTES_AeSliceHonV_analysis.md` / `NOTES_AeSliceHonV_session2.md`.
-/

/-- **The target from the finiteness of the iterated weighted `∫⁻`** (the project's recorded
crux `(⋆)`; the first conjunct of `H2W.AeMixedAeMem_of_fin`, transferred from `Iθ = Icc 0 (π/2)`
to `Ioo 0 (π/2)`). -/
theorem aeSliceHonV_of_fin {α : ℝ} {u G : ℝ → ℝ → ℝ}
    (h : Work.FTS.EllipticEst.H2W.Ae.AeData α u G)
    (hfin : (∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ,
        ENNReal.ofReal ((z * Work.Spaces.pz (Work.Spaces.pth u) z θ) ^ 2
          * Work.FTS.EllipticEst.AngSecond.sig θ)) < ⊤) :
    ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))),
      MeasureTheory.IntegrableOn
        (fun θ => (z * Work.Spaces.pz (Work.Spaces.pth u) z θ) ^ 2
          * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
        (Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
  filter_upwards [Work.FTS.EllipticEst.H2W.AeMixedAeMem_of_fin h hfin] with z hz
  refine hz.mono_set ?_
  intro θ hθ
  exact ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩

/-- **The target from the a.e. `σ`-honesty of the `H`-slot** `∂_θ²(z∂_zu) = pthIter 2 (grad u)`
(the form in which `I₁`-chain consumers carry the slot). -/
theorem aeSliceHonV_of_hslot {α : ℝ} {u G : ℝ → ℝ → ℝ}
    (h : Work.FTS.EllipticEst.H2W.Ae.AeData α u G)
    (hH : ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))),
      MeasureTheory.IntegrableOn
        (fun θ => (Work.Spaces.pthIter 2 (Work.FTS.EllipticEst.H2W.Ae.grad u) z θ) ^ 2
          * ((Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))) Work.Spaces.Iθ) :
    ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))),
      MeasureTheory.IntegrableOn
        (fun θ => (z * Work.Spaces.pz (Work.Spaces.pth u) z θ) ^ 2
          * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
        (Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
  filter_upwards [Work.FTS.EllipticEst.H2W.AeMixedAeMem_of_hslot h hH] with z hz
  refine hz.mono_set ?_
  intro θ hθ
  exact ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩

/-- **The target from the `HkMem`-form honesty of the mixed slot itself** — the exact hypothesis
with which every existing consumer of the slot is stated (`Final/AeI1Paper_mix_fts`,
`H2W/EllCore/AeI1HonestCore.lean`, `AngAWeak/aeI1Mixed.lean`,
`Cores/AeStep2Aux/i1Paper_weakMixed.lean`). -/
theorem aeSliceHonV_of_mixedHkMem {α : ℝ} {u G : ℝ → ℝ → ℝ}
    (h : Work.FTS.EllipticEst.H2W.Ae.AeData α u G)
    (hmix : Work.Spaces.HkMem α 0
      (fun z θ => z * Work.Spaces.pz (Work.Spaces.pth u) z θ)) :
    ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))),
      MeasureTheory.IntegrableOn
        (fun θ => (z * Work.Spaces.pz (Work.Spaces.pth u) z θ) ^ 2
          * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
        (Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
  filter_upwards [Work.FTS.EllipticEst.H2W.AeMixedAeMem_of_mixedHkMem h hmix] with z hz
  refine hz.mono_set ?_
  intro θ hθ
  exact ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩

/-- The requested statement: the angular slice `θ ↦ (z ∂_z∂_θu)^2 σ θ` of the mixed slot is
integrable for almost every `z > 0`.  Proved by the flat heavy route of the module docstring. -/
theorem AeSliceHonV {α : ℝ} {u G : ℝ → ℝ → ℝ}
    (h : Work.FTS.EllipticEst.H2W.Ae.AeData α u G)
    (hU : Work.Spaces.HkMem α 0 (Work.FTS.EllipticEst.H2W.Ae.grad u)) :
    ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))),
      MeasureTheory.IntegrableOn
        (fun θ => (z * Work.Spaces.pz (Work.Spaces.pth u) z θ) ^ 2
          * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
        (Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
  have hAe : Work.FTS.EllipticEst.H2W.Ae.AeData α u G := h
  have hSm : Work.FTS.EllipticEst.SmoothOpen u :=
    Work.FTS.EllipticEst.smoothOpen_of_forall hAe.smooth
  have hU' : Work.Spaces.HkMem α 0 (Work.Spaces.Dz u) := hU
  have hthEta : ∀ θ ∈ Iθ, 0 ≤ Work.FTS.EllipticEst.thEta θ :=
    fun θ hθ => Work.FTS.EllipticEst.thEta_nonneg hθ
  -- ## slot 1 (f = Dz u)
  have hF1nn : ∀ z θ, 0 ≤ Work.Spaces.HkIntegrand α 0 (Work.Spaces.Dz u) z θ := by
    intro z θ; rw [HkIntegrand_zero]; exact sq_nonneg _
  have hF1cont : ContinuousOn (fun p : ℝ × ℝ =>
      Work.Spaces.HkIntegrand α 0 (Work.Spaces.Dz u) p.1 p.2)
      ((Set.Ioi (0:ℝ)) ×ˢ Set.Ioo 0 (Real.pi / 2)) := hSm.Dz.continuousOn_HkIntegrand α 0
  have hg1 : ContinuousOn (fun p : ℝ × ℝ =>
      Real.exp p.1 * Work.Spaces.pz u (Real.exp p.1) p.2)
      ((Set.univ : Set ℝ) ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
    ((Real.continuous_exp.comp continuous_fst).continuousOn
        (s := (Set.univ : Set ℝ) ×ˢ Set.Ioo 0 (Real.pi / 2))).mul
      (contOn_expComp hSm.pz.continuousOn)
  have hidg1 : ∀ t θ, θ ∈ Set.Ioo 0 (Real.pi / 2) →
      (Work.Spaces.pz (pb u) t θ) ^ 2 * Work.FTS.EllSol.HeavyFlat.omw t
          * Work.FTS.EllipticEst.sEta θ
        = (Real.exp t * Work.Spaces.pz u (Real.exp t) θ) ^ 2
          * Work.FTS.EllSol.HeavyFlat.omw t * Work.FTS.EllipticEst.sEta θ := by
    intro t θ hθ; rw [pb_pz hSm hθ]
  have hid1 : ∀ t θ, θ ∈ Set.Ioo 0 (Real.pi / 2) →
      (Work.Spaces.pz (pb u) t θ) ^ 2 * Work.FTS.EllSol.HeavyFlat.omw t
          * Work.FTS.EllipticEst.sEta θ
        = Real.exp t * Work.Spaces.HkIntegrand α 0 (Work.Spaces.Dz u) (Real.exp t) θ := by
    intro t θ hθ
    have hIθ : θ ∈ Iθ := ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
    rw [pb_pz hSm hθ, HkIntegrand_zero_eq α (Work.Spaces.Dz u) hIθ,
      Work.FTS.EllSol.HeavyFlat.omw_eq_w_sq_mul,
      show Work.Spaces.Dz u (Real.exp t) θ
        = Real.exp t * Work.Spaces.pz u (Real.exp t) θ from rfl]
    ring
  have hslot1 : MeasureTheory.IntegrableOn (fun p : ℝ × ℝ =>
      (Work.Spaces.pz (pb u) p.1 p.2) ^ 2 * Work.FTS.EllSol.HeavyFlat.omw p.1
        * Work.FTS.EllipticEst.sEta p.2) ((Set.univ : Set ℝ) ×ˢ Iθ) :=
    slot_integrableOn
      (F := fun z θ => Work.Spaces.HkIntegrand α 0 (Work.Spaces.Dz u) z θ)
      (Φ := fun t θ => (Work.Spaces.pz (pb u) t θ) ^ 2 * Work.FTS.EllSol.HeavyFlat.omw t
        * Work.FTS.EllipticEst.sEta θ)
      hF1nn (Phi_nonneg hidg1) hid1 hF1cont (continuousOn_Phi hg1 hidg1) hU'.1 hU'.2
  -- ## slot 3 (f = pthIter 2 u)
  have hF3nn : ∀ z θ, 0 ≤ Work.Spaces.HkIntegrand α 0 (Work.Spaces.pthIter 2 u) z θ := by
    intro z θ; rw [HkIntegrand_zero]; exact sq_nonneg _
  have hF3cont : ContinuousOn (fun p : ℝ × ℝ =>
      Work.Spaces.HkIntegrand α 0 (Work.Spaces.pthIter 2 u) p.1 p.2)
      ((Set.Ioi (0:ℝ)) ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
    (hSm.pth.pth).continuousOn_HkIntegrand α 0
  have hg3 : ContinuousOn (fun p : ℝ × ℝ =>
      Work.Spaces.pthIter 2 u (Real.exp p.1) p.2)
      ((Set.univ : Set ℝ) ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
    contOn_expComp (hSm.pth.pth).continuousOn
  have hidg3 : ∀ t θ, θ ∈ Set.Ioo 0 (Real.pi / 2) →
      (Work.Spaces.pthIter 2 (pb u) t θ) ^ 2 * Work.FTS.EllSol.HeavyFlat.omw t
          * Work.FTS.EllipticEst.sEta θ
        = (Work.Spaces.pthIter 2 u (Real.exp t) θ) ^ 2
          * Work.FTS.EllSol.HeavyFlat.omw t * Work.FTS.EllipticEst.sEta θ := by
    intro t θ hθ; rw [pb_pthIter]
  have hid3 : ∀ t θ, θ ∈ Set.Ioo 0 (Real.pi / 2) →
      (Work.Spaces.pthIter 2 (pb u) t θ) ^ 2 * Work.FTS.EllSol.HeavyFlat.omw t
          * Work.FTS.EllipticEst.sEta θ
        = Real.exp t * Work.Spaces.HkIntegrand α 0 (Work.Spaces.pthIter 2 u) (Real.exp t) θ := by
    intro t θ hθ
    have hIθ : θ ∈ Iθ := ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
    rw [pb_pthIter, HkIntegrand_zero_eq α (Work.Spaces.pthIter 2 u) hIθ,
      Work.FTS.EllSol.HeavyFlat.omw_eq_w_sq_mul]
    ring
  have hslot3 : MeasureTheory.IntegrableOn (fun p : ℝ × ℝ =>
      (Work.Spaces.pthIter 2 (pb u) p.1 p.2) ^ 2 * Work.FTS.EllSol.HeavyFlat.omw p.1
        * Work.FTS.EllipticEst.sEta p.2) ((Set.univ : Set ℝ) ×ˢ Iθ) :=
    slot_integrableOn
      (F := fun z θ => Work.Spaces.HkIntegrand α 0 (Work.Spaces.pthIter 2 u) z θ)
      (Φ := fun t θ => (Work.Spaces.pthIter 2 (pb u) t θ) ^ 2 * Work.FTS.EllSol.HeavyFlat.omw t
        * Work.FTS.EllipticEst.sEta θ)
      hF3nn (Phi_nonneg hidg3) hid3 hF3cont (continuousOn_Phi hg3 hidg3)
      hAe.memAng2.1 hAe.memAng2.2
  -- ## slot 2 (f = Dz (Dz u))
  have hF2nn : ∀ z θ, 0 ≤ Work.Spaces.HkIntegrand α 0 (Work.Spaces.Dz (Work.Spaces.Dz u)) z θ := by
    intro z θ; rw [HkIntegrand_zero]; exact sq_nonneg _
  have hdom2 : ∀ z θ, θ ∈ Set.Ioo 0 (Real.pi / 2) → 0 < z →
      Work.Spaces.HkIntegrand α 0 (Work.Spaces.Dz (Work.Spaces.Dz u)) z θ
        ≤ 2 * Work.Spaces.HkIntegrand α 0 (Work.Spaces.Dz u) z θ
          + 2 * Work.Spaces.HkIntegrand α 0
              (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 u z θ) z θ := by
    intro z θ hθ hz
    rw [HkIntegrand_zero, HkIntegrand_zero, HkIntegrand_zero]
    rw [show Work.Spaces.Dz (Work.Spaces.Dz u) z θ
        = Work.Spaces.Dz u z θ + z ^ 2 * Work.Spaces.pzIter 2 u z θ from pb_DzDz hSm hz hθ]
    nlinarith [sq_nonneg (Work.Spaces.Dz u z θ
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))
      - z ^ 2 * Work.Spaces.pzIter 2 u z θ
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)))]
  have hslices2 : ∀ z ∈ Work.Spaces.Iz, Integrable (fun θ =>
      Work.Spaces.HkIntegrand α 0 (Work.Spaces.Dz (Work.Spaces.Dz u)) z θ)
      (MeasureTheory.volume.restrict Iθ) := by
    intro z hz
    rcases eq_or_lt_of_le (Set.mem_Ici.mp hz) with h0 | hpos
    · rw [← h0]
      simp only [Work.Spaces.HkIntegrand_zero_z, Pi.zero_apply]
      exact MeasureTheory.integrable_zero ℝ ℝ _
    · refine MeasureTheory.Integrable.mono'
        (f := fun θ => Work.Spaces.HkIntegrand α 0 (Work.Spaces.Dz (Work.Spaces.Dz u)) z θ)
        (g := fun θ => 2 * Work.Spaces.HkIntegrand α 0 (Work.Spaces.Dz u) z θ
          + 2 * Work.Spaces.HkIntegrand α 0 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 u z θ) z θ)
        ?_ ?_ ?_
      · exact (hU'.1 z hz).const_mul 2 |>.add ((hAe.memRad2.1 z hz).const_mul 2)
      · exact Work.Spaces.aesm_slice_of_continuousOn_Qd _
          ((hSm.Dz.Dz).continuousOn_HkIntegrand α 0) hpos
      · filter_upwards [ae_Iθ_Ioo] with θ hθIoo
        rw [Real.norm_of_nonneg (hF2nn z θ)]
        exact hdom2 z θ hθIoo hpos
  have houter2 : Integrable (fun z => ∫ θ,
      Work.Spaces.HkIntegrand α 0 (Work.Spaces.Dz (Work.Spaces.Dz u)) z θ
        ∂(MeasureTheory.volume.restrict Iθ)) (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
    have hg : Integrable (fun z => ∫ θ, (2 * Work.Spaces.HkIntegrand α 0 (Work.Spaces.Dz u) z θ
        + 2 * Work.Spaces.HkIntegrand α 0 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 u z θ) z θ)
        ∂(MeasureTheory.volume.restrict Iθ)) (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
      refine ((hU'.2.const_mul 2).add (hAe.memRad2.2.const_mul 2)).congr ?_
      refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ici fun z hz => ?_
      show 2 * (∫ θ, Work.Spaces.HkIntegrand α 0 (Work.Spaces.Dz u) z θ
            ∂(MeasureTheory.volume.restrict Iθ))
          + 2 * (∫ θ, Work.Spaces.HkIntegrand α 0
              (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 u z θ) z θ
            ∂(MeasureTheory.volume.restrict Iθ))
          = ∫ θ, (2 * Work.Spaces.HkIntegrand α 0 (Work.Spaces.Dz u) z θ
              + 2 * Work.Spaces.HkIntegrand α 0
                  (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 u z θ) z θ)
            ∂(MeasureTheory.volume.restrict Iθ)
      rw [MeasureTheory.integral_add ((hU'.1 z hz).const_mul 2)
          ((hAe.memRad2.1 z hz).const_mul 2),
        MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
    refine MeasureTheory.Integrable.mono'
      (f := fun z => ∫ θ, Work.Spaces.HkIntegrand α 0 (Work.Spaces.Dz (Work.Spaces.Dz u)) z θ
        ∂(MeasureTheory.volume.restrict Iθ))
      (g := fun z => ∫ θ, (2 * Work.Spaces.HkIntegrand α 0 (Work.Spaces.Dz u) z θ
        + 2 * Work.Spaces.HkIntegrand α 0 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 u z θ) z θ)
        ∂(MeasureTheory.volume.restrict Iθ)) ?_ ?_ ?_
    · exact hg
    · exact (Work.Spaces.aesm_of_continuousOn_Qd _
        ((hSm.Dz.Dz).continuousOn_HkIntegrand α 0)).integral_prod_right'
    · refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ici fun z hz => ?_
      rcases eq_or_lt_of_le (Set.mem_Ici.mp hz) with h0 | hpos
      · rw [← h0]
        simp only [Work.Spaces.HkIntegrand_zero_z]
        simp
      · rw [Real.norm_of_nonneg (MeasureTheory.integral_nonneg_of_ae ?_)]
        swap
        · filter_upwards with θ
          exact hF2nn z θ
        refine MeasureTheory.integral_mono_of_nonneg
          (μ := MeasureTheory.volume.restrict Iθ)
          (f := fun θ => Work.Spaces.HkIntegrand α 0 (Work.Spaces.Dz (Work.Spaces.Dz u)) z θ)
          (g := fun θ => 2 * Work.Spaces.HkIntegrand α 0 (Work.Spaces.Dz u) z θ
            + 2 * Work.Spaces.HkIntegrand α 0
                (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 u z θ) z θ) ?_ ?_ ?_
        · filter_upwards with θ; exact hF2nn z θ
        · exact (hU'.1 z hz).const_mul 2 |>.add ((hAe.memRad2.1 z hz).const_mul 2)
        · filter_upwards [ae_Iθ_Ioo] with θ hθIoo
          exact hdom2 z θ hθIoo hpos
  have hg2 : ContinuousOn (fun p : ℝ × ℝ =>
      Work.Spaces.Dz (Work.Spaces.Dz u) (Real.exp p.1) p.2)
      ((Set.univ : Set ℝ) ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
    contOn_expComp (hSm.Dz.Dz).continuousOn
  have hidg2 : ∀ t θ, θ ∈ Set.Ioo 0 (Real.pi / 2) →
      (Work.Spaces.pz (Work.Spaces.pz (pb u)) t θ) ^ 2 * Work.FTS.EllSol.HeavyFlat.omw t
          * Work.FTS.EllipticEst.sEta θ
        = (Work.Spaces.Dz (Work.Spaces.Dz u) (Real.exp t) θ) ^ 2
          * Work.FTS.EllSol.HeavyFlat.omw t * Work.FTS.EllipticEst.sEta θ := by
    intro t θ hθ; rw [pb_pz2 hSm hθ]
  have hid2 : ∀ t θ, θ ∈ Set.Ioo 0 (Real.pi / 2) →
      (Work.Spaces.pz (Work.Spaces.pz (pb u)) t θ) ^ 2 * Work.FTS.EllSol.HeavyFlat.omw t
          * Work.FTS.EllipticEst.sEta θ
        = Real.exp t * Work.Spaces.HkIntegrand α 0 (Work.Spaces.Dz (Work.Spaces.Dz u))
            (Real.exp t) θ := by
    intro t θ hθ
    have hIθ : θ ∈ Iθ := ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
    rw [pb_pz2 hSm hθ, HkIntegrand_zero_eq α (Work.Spaces.Dz (Work.Spaces.Dz u)) hIθ,
      Work.FTS.EllSol.HeavyFlat.omw_eq_w_sq_mul,
      show Work.Spaces.Dz (Work.Spaces.Dz u) (Real.exp t) θ
        = Real.exp t * Work.Spaces.pz (Work.Spaces.Dz u) (Real.exp t) θ from rfl]
    ring
  have hslot2 : MeasureTheory.IntegrableOn (fun p : ℝ × ℝ =>
      (Work.Spaces.pz (Work.Spaces.pz (pb u)) p.1 p.2) ^ 2 * Work.FTS.EllSol.HeavyFlat.omw p.1
        * Work.FTS.EllipticEst.sEta p.2) ((Set.univ : Set ℝ) ×ˢ Iθ) :=
    slot_integrableOn
      (F := fun z θ => Work.Spaces.HkIntegrand α 0 (Work.Spaces.Dz (Work.Spaces.Dz u)) z θ)
      (Φ := fun t θ => (Work.Spaces.pz (Work.Spaces.pz (pb u)) t θ) ^ 2
        * Work.FTS.EllSol.HeavyFlat.omw t * Work.FTS.EllipticEst.sEta θ)
      hF2nn (Phi_nonneg hidg2) hid2 ((hSm.Dz.Dz).continuousOn_HkIntegrand α 0)
      (continuousOn_Phi hg2 hidg2) hslices2 houter2
  -- ## the interface
  have hOm : Work.FTS.EllSol.HeavyFlat.OmHeavy :=
    Work.FTS.EllSol.HeavyFlat.omOfFlat Work.FTS.EllSol.HeavyFlat.flatHeavy
  -- ## the interface
  have hconcl := hOm (pb u) (pb_contDiff hAe.smooth 2)
    (fun t => hAe.dirZero (Real.exp t)) (fun t => hAe.dirPi (Real.exp t))
    hslot1 hslot2 hslot3
  -- ## the reverse transfer
  have hGcont : ContinuousOn (fun p : ℝ × ℝ =>
      Work.Spaces.HkIntegrand α 0 (Work.Spaces.Dz (Work.Spaces.pth u)) (Real.exp p.1) p.2)
      ((Set.univ : Set ℝ) ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
    contOn_expComp ((hSm.pth.Dz).continuousOn_HkIntegrand α 0)
  have hidM : ∀ t θ, θ ∈ Set.Ioo 0 (Real.pi / 2) →
      (Work.Spaces.pth (Work.Spaces.pz (pb u)) t θ) ^ 2 * Work.FTS.EllSol.HeavyFlat.omw t
          * Work.FTS.EllipticEst.sEta θ
        = Real.exp t * Work.Spaces.HkIntegrand α 0 (Work.Spaces.Dz (Work.Spaces.pth u))
            (Real.exp t) θ := by
    intro t θ hθ
    have hIθ : θ ∈ Iθ := ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
    rw [pb_pth_pz hSm hθ, HkIntegrand_zero_eq α (Work.Spaces.Dz (Work.Spaces.pth u)) hIθ,
      Work.FTS.EllSol.HeavyFlat.omw_eq_w_sq_mul,
      show Work.Spaces.Dz (Work.Spaces.pth u) (Real.exp t) θ
        = Real.exp t * Work.Spaces.pz (Work.Spaces.pth u) (Real.exp t) θ from rfl]
    ring
  have hGF : (fun q : ℝ × ℝ => ENNReal.ofReal
        ((Work.Spaces.pth (Work.Spaces.pz (pb u)) q.1 q.2) ^ 2 * Work.FTS.EllSol.HeavyFlat.omw q.1
          * Work.FTS.EllipticEst.sEta q.2))
      =ᵐ[MeasureTheory.Measure.prod (volume : Measure ℝ) (MeasureTheory.volume.restrict Iθ)]
      (fun q : ℝ × ℝ => ENNReal.ofReal (Real.exp q.1)
        * ENNReal.ofReal (Work.Spaces.HkIntegrand α 0 (Work.Spaces.Dz (Work.Spaces.pth u))
            (Real.exp q.1) q.2)) := by
    filter_upwards [ae_strip_of hidM] with q hq
    rw [hq, ENNReal.ofReal_mul (le_of_lt (Real.exp_pos q.1))]
  have hAEz : AEMeasurable (fun p : ℝ × ℝ =>
      ENNReal.ofReal (Work.Spaces.HkIntegrand α 0 (Work.Spaces.Dz (Work.Spaces.pth u)) p.1 p.2))
      ((volume : Measure ℝ).restrict (Set.Ioi 0) |>.prod (MeasureTheory.volume.restrict Iθ)) := by
    have h := Work.Spaces.aesm_of_continuousOn_Qd
      (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α 0 (Work.Spaces.Dz (Work.Spaces.pth u)) p.1 p.2)
      ((hSm.pth.Dz).continuousOn_HkIntegrand α 0)
    rw [show (MeasureTheory.volume : Measure ℝ).restrict Work.Spaces.Iz
        = MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ)) from
      MeasureTheory.Measure.restrict_congr_set
        (MeasureTheory.Ioi_ae_eq_Ici (μ := volume) (a := 0)).symm] at h
    exact (ENNReal.measurable_ofReal.comp_aemeasurable h.aemeasurable)
  have hAEt : AEMeasurable (fun q : ℝ × ℝ => ENNReal.ofReal (Real.exp q.1)
      * ENNReal.ofReal (Work.Spaces.HkIntegrand α 0 (Work.Spaces.Dz (Work.Spaces.pth u))
          (Real.exp q.1) q.2))
      (MeasureTheory.Measure.prod (volume : Measure ℝ) (MeasureTheory.volume.restrict Iθ)) := by
    refine (ENNReal.measurable_ofReal.comp_aemeasurable
      ((Real.measurable_exp.comp measurable_fst).aemeasurable)).mul ?_
    exact ENNReal.measurable_ofReal.comp_aemeasurable
      ((aesm_prod_univ_Iθ (f := fun t θ => Work.Spaces.HkIntegrand α 0
        (Work.Spaces.Dz (Work.Spaces.pth u)) (Real.exp t) θ) hGcont).aemeasurable)
  have hAEt' : AEMeasurable (fun q : ℝ × ℝ => ENNReal.ofReal (Real.exp q.1
      * Work.Spaces.HkIntegrand α 0 (Work.Spaces.Dz (Work.Spaces.pth u)) (Real.exp q.1) q.2))
      (MeasureTheory.Measure.prod (volume : Measure ℝ) (MeasureTheory.volume.restrict Iθ)) := by
    refine hAEt.congr ?_
    filter_upwards with q
    rw [ENNReal.ofReal_mul (le_of_lt (Real.exp_pos q.1))]
  have hfinT := lintegral_box_exp_rev (F := fun z θ =>
      ENNReal.ofReal (Work.Spaces.HkIntegrand α 0 (Work.Spaces.Dz (Work.Spaces.pth u)) z θ))
    hAEz hAEt hGF hconcl
  -- ## Tonelli: the box `∫⁻` of the mixed slot is the iterated one
  have hfinIter : (∫⁻ z, (∫⁻ θ, (fun p : ℝ × ℝ => ENNReal.ofReal
        (Work.Spaces.HkIntegrand α 0 (Work.Spaces.Dz (Work.Spaces.pth u)) p.1 p.2)) (z, θ)
      ∂(MeasureTheory.volume.restrict Iθ))
      ∂((MeasureTheory.volume : Measure ℝ).restrict (Set.Ioi (0 : ℝ)))) < ⊤ := by
    rw [← MeasureTheory.lintegral_prod
      (f := fun p : ℝ × ℝ => ENNReal.ofReal
        (Work.Spaces.HkIntegrand α 0 (Work.Spaces.Dz (Work.Spaces.pth u)) p.1 p.2)) hAEz]
    exact hfinT
  have hmeasZ : AEMeasurable (fun z : ℝ => ∫⁻ θ, ENNReal.ofReal
        (Work.Spaces.HkIntegrand α 0 (Work.Spaces.Dz (Work.Spaces.pth u)) z θ)
      ∂(MeasureTheory.volume.restrict Iθ))
      ((MeasureTheory.volume : Measure ℝ).restrict (Set.Ioi (0 : ℝ))) := by
    have h := AEMeasurable.lintegral_prod_right
      (μ := (MeasureTheory.volume : Measure ℝ).restrict (Set.Ioi (0 : ℝ)))
      (ν := MeasureTheory.volume.restrict Iθ)
      (f := fun z θ => ENNReal.ofReal (Work.Spaces.HkIntegrand α 0
        (Work.Spaces.Dz (Work.Spaces.pth u)) z θ)) hAEz
    exact h
  have haeFin : ∀ᵐ z ∂((MeasureTheory.volume : Measure ℝ).restrict (Set.Ioi (0 : ℝ))),
      (∫⁻ θ, ENNReal.ofReal (Work.Spaces.HkIntegrand α 0
        (Work.Spaces.Dz (Work.Spaces.pth u)) z θ)
        ∂(MeasureTheory.volume.restrict Iθ)) < ⊤ :=
    MeasureTheory.ae_lt_top' hmeasZ (ne_of_lt hfinIter)
  -- ## the a.e. slice
  filter_upwards [haeFin, self_mem_ae_restrict measurableSet_Ioi] with z hzfin hzpos
  have hz : (0 : ℝ) < z := hzpos
  -- the level-0 integrand is `w z ^ 2` times the target integrand on `Iθ`
  have hkey : ∀ θ ∈ Iθ, ENNReal.ofReal (Work.Spaces.HkIntegrand α 0
      (Work.Spaces.Dz (Work.Spaces.pth u)) z θ)
      = ENNReal.ofReal ((Work.Spaces.w z) ^ 2)
        * ENNReal.ofReal ((z * Work.Spaces.pz (Work.Spaces.pth u) z θ) ^ 2
            * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) := by
    intro θ hθ
    rw [HkIntegrand_zero_eq α (Work.Spaces.Dz (Work.Spaces.pth u)) hθ]
    rw [show Work.FTS.EllipticEst.sEta θ
        = (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) from rfl]
    rw [show Work.Spaces.Dz (Work.Spaces.pth u) z θ
        = z * Work.Spaces.pz (Work.Spaces.pth u) z θ from rfl]
    rw [show (z * Work.Spaces.pz (Work.Spaces.pth u) z θ) ^ 2 * (Work.Spaces.w z) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
        = (Work.Spaces.w z) ^ 2 * ((z * Work.Spaces.pz (Work.Spaces.pth u) z θ) ^ 2
            * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) from by ring]
    rw [ENNReal.ofReal_mul (sq_nonneg (Work.Spaces.w z))]
  have hAeq : (∫⁻ θ, ENNReal.ofReal (Work.Spaces.HkIntegrand α 0
        (Work.Spaces.Dz (Work.Spaces.pth u)) z θ) ∂(MeasureTheory.volume.restrict Iθ))
      = ENNReal.ofReal ((Work.Spaces.w z) ^ 2)
        * (∫⁻ θ, ENNReal.ofReal ((z * Work.Spaces.pz (Work.Spaces.pth u) z θ) ^ 2
              * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
            ∂(MeasureTheory.volume.restrict Iθ)) := by
    have hcongr : (fun θ : ℝ => ENNReal.ofReal (Work.Spaces.HkIntegrand α 0
        (Work.Spaces.Dz (Work.Spaces.pth u)) z θ))
        =ᵐ[MeasureTheory.volume.restrict Iθ]
        (fun θ : ℝ => ENNReal.ofReal ((Work.Spaces.w z) ^ 2)
          * ENNReal.ofReal ((z * Work.Spaces.pz (Work.Spaces.pth u) z θ) ^ 2
              * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))) := by
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ hθ
      exact hkey θ hθ
    rw [MeasureTheory.lintegral_congr_ae hcongr,
      MeasureTheory.lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  have hwne : ENNReal.ofReal ((Work.Spaces.w z) ^ 2) ≠ 0 := by
    have hwpos : 0 < (Work.Spaces.w z) ^ 2 := by
      rw [Work.Spaces.w]
      exact pow_pos (div_pos (pow_pos (by linarith) 2) (pow_pos hz 2)) 2
    exact ne_of_gt (ENNReal.ofReal_pos.mpr hwpos)
  have hBfin : (∫⁻ θ, ENNReal.ofReal ((z * Work.Spaces.pz (Work.Spaces.pth u) z θ) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
        ∂(MeasureTheory.volume.restrict Iθ)) < ⊤ := by
    have h1 : ENNReal.ofReal ((Work.Spaces.w z) ^ 2)
        * (∫⁻ θ, ENNReal.ofReal ((z * Work.Spaces.pz (Work.Spaces.pth u) z θ) ^ 2
              * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
            ∂(MeasureTheory.volume.restrict Iθ)) < ⊤ := by
      rw [← hAeq]
      exact hzfin
    rcases ENNReal.mul_lt_top_iff.mp h1 with h2 | h0 | h0'
    · exact h2.2
    · exact absurd h0 hwne
    · rw [h0']; exact ENNReal.zero_lt_top
  have hBfin' : (∫⁻ θ in Set.Ioo (0 : ℝ) (Real.pi / 2),
      ENNReal.ofReal ((z * Work.Spaces.pz (Work.Spaces.pth u) z θ) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))) < ⊤ := by
    refine lt_of_le_of_lt ?_ hBfin
    exact MeasureTheory.lintegral_mono_set (fun θ hθ => ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩)
  -- ## the Bochner statement
  have hcontθ : ContinuousOn (fun θ : ℝ => (z * Work.Spaces.pz (Work.Spaces.pth u) z θ) ^ 2
      * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) (Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
    have hzsl : ContinuousOn (fun θ : ℝ => z * Work.Spaces.pz (Work.Spaces.pth u) z θ)
        (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
      continuousOn_const.mul ((hSm.pth.pz.curry_θ hz).continuousOn)
    have hsigcont : ContinuousOn (fun θ : ℝ => (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
        (Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
      have hsincont : Continuous (fun θ : ℝ => Real.sin (2 * θ)) :=
        Real.continuous_sin.comp (continuous_const.mul continuous_id)
      exact hsincont.continuousOn.rpow_const (p := -(Work.Spaces.eta))
        (fun θ hθ => Or.inl (ne_of_gt (Real.sin_pos_of_pos_of_lt_pi
          (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos]))))
    exact (hzsl.pow 2).mul hsigcont
  have haesm : AEStronglyMeasurable (fun θ : ℝ =>
      (z * Work.Spaces.pz (Work.Spaces.pth u) z θ) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
      (MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2))) :=
    hcontθ.aestronglyMeasurable measurableSet_Ioo
  have hnn : 0 ≤ᵐ[MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2))]
      (fun θ : ℝ => (z * Work.Spaces.pz (Work.Spaces.pth u) z θ) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) := by
    show ∀ᵐ θ ∂(MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2))),
      (0 : ℝ) ≤ (z * Work.Spaces.pz (Work.Spaces.pth u) z θ) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with θ hθ
    exact mul_nonneg (sq_nonneg _) (le_of_lt (Real.rpow_pos_of_pos
      (Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])) _))
  rw [MeasureTheory.IntegrableOn]
  exact (MeasureTheory.lintegral_ofReal_ne_top_iff_integrable haesm hnn).mp (ne_of_lt hBfin')


end Work.FTS.EllipticEst.AeCrux
