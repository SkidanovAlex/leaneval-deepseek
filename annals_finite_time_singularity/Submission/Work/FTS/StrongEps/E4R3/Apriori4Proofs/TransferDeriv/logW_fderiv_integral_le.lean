import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongEps.E4R3.Apriori4Proofs.JepsTransfer.LogInt
import Submission.Work.FTS.StrongEps.E4R3.Apriori4Proofs.JepsTransfer.Recur
import Submission.Work.FTS.StrongEps.E4R3.Apriori4Proofs.TransferDeriv.LogWeightInt.logW_mul_sq_facts
import Submission.Work.FTS.StrongEps.SmoothOpen_Jeps
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6SupAux.StarSlotPcs.DzdIterBound
import Submission.Work.FTS.StrongPersist.H6Rows.wprod6
import Submission.Work.FTS.StrongPersist.N6Trans.SixAux.MainBoundR
import Submission.Work.FTS_LocDatum3a.Basic
import Submission.Work.FTS_LocDatum3a.Defs
import Submission.Work.FTS_RegExport.RXB.sup_bound_all_alpha
import Submission.Work.FTS_RegExport.RXT.Slots.JetCalc.Expand
import Submission.Work.FTS_RegExport.RXT.velVanish2Star
import Submission.Work.GalerkinFix.RegQ.HkMem_mono_Q
import Submission.Work.Spaces.SmoothCompact_HkMem
-- ===== merged: Submission.Work.FTS.StrongEps.E4R3.Apriori4Proofs.JepsTransfer.BaseCase =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `JepsTransfer/BaseCase.lean` — the transfer estimate at level one, and the induction

The base case of the transfer estimate is the estimate for the `ℋ¹`-pairing `H1IP`:

  `|H1IP α (J_ε u) v − H1IP α u (J_ε v)| ≤ K ε |u|₁ |v|₁`;

it is the sum of four `wip`-slots (`leafEta` at the slots `(0,0)` and `(0,1)`, `leafOne` at
`(0,0)` and `leafGam α` at the slot `(1,0)`), each of which is the `pairing_transfer` of
`JepsTransfer/Transfer.lean`.  The induction `delta_bound_of` lifts this to the recursion `IPn`:
the transfer defect `Δₙ(u,v) = IPn α n (J_ε u) v − IPn α n u (J_ε v)` satisfies
`Δₙ₊₁ = Δₙ + Δₙ(D_θ·,D_θ·) + Δₙ(D_z·,D_z·)` (`IPn_succ_Jeps`), and each of the three extra
slots costs one `ℋ`-level (`hkNorm_dth`, `hkNorm_dz`, `hkNorm_mono`), so the constant is
multiplied by `3` at each step.

The two facts about the leaf weights (the uniform two-sided log-shift bound and the joint
integrability of the slot integrands) are isolated as the predicates `LeafShiftUniform` and
`LeafPairIntegrable`; they are discharged in the final assembly.
-/

noncomputable section

open scoped Real Topology ENNReal
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.E4R3.Apriori4Proofs.JT

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false

/-- The uniform two-sided log-shift bound for the three leaf weights. -/
def LeafShiftUniform : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ α ∈ Set.Ioc (0 : ℝ) 1, ∀ w : ℝ → ℝ → ℝ,
    (w = Work.FTS.TransportS.leafEta ∨ w = Work.FTS.TransportS.leafOne
      ∨ w = Work.FTS.TransportS.leafGam α) →
    ∀ y p : ℝ × ℝ,
      (Work.FTS.StrongEps.E4R3.Apriori4Proofs.logW w (y + p)
          ≤ Real.exp (C * (|p.1| + |p.2|)) * Work.FTS.StrongEps.E4R3.Apriori4Proofs.logW w y)
      ∧ (Work.FTS.StrongEps.E4R3.Apriori4Proofs.logW w y
          ≤ Real.exp (C * (|p.1| + |p.2|))
            * Work.FTS.StrongEps.E4R3.Apriori4Proofs.logW w (y + p))

/-- The joint integrability of the slot integrands, at level one. -/
def LeafPairIntegrable (ρ : ℝ × ℝ → ℝ) : Prop :=
  ∀ {α ε : ℝ} (hα : α ∈ Set.Ioc (0 : ℝ) 1) (hε : ε ∈ Set.Ioc (0 : ℝ) 1)
    {w : ℝ → ℝ → ℝ} {a b : ℕ} (hleaf : Work.FTS.TransportS.IsLeafW α a w)
    (hab : a + b ≤ 1) {u v : ℝ → ℝ → ℝ}
    (hu : Work.FTS.VocabO.HQo α 1 u) (hv : Work.FTS.VocabO.HQo α 1 v),
    MeasureTheory.Integrable (Function.uncurry (fun z θ =>
        w z θ * Work.FTS.StrongEps.Jeps ρ ε (Work.Spaces.mixed b a u) z θ
          * Work.Spaces.mixed b a v z θ))
        (MeasureTheory.volume.restrict (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)))
    ∧ MeasureTheory.Integrable (Function.uncurry (fun z θ =>
        w z θ * (Work.Spaces.mixed b a u z θ) ^ 2))
        (MeasureTheory.volume.restrict (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)))
    ∧ MeasureTheory.Integrable (Function.uncurry (fun z θ =>
        w z θ * (Work.Spaces.mixed b a v z θ) ^ 2))
        (MeasureTheory.volume.restrict (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)))

/-- A `mixed` slot of a profile smooth on the open quadrant is smooth there. -/
theorem mixed_smooth_of_smoothOpen {u : Fn} (hu : Work.FTS.EllipticEst.SmoothOpen u)
    (b a : ℕ) :
    ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry (Work.Spaces.mixed b a u))
      Work.FTS.EllipticEst.Q0 :=
  fun n => contDiffOn_iff_forall_nat_le.mp
    ((Work.FTS.StrongEps.smQ_of_forall_nat hu.forall).DthIter a |>.DzIter b) n le_top

/-- **The transfer estimate at a single leaf slot.** -/
theorem slot_transfer_of {ρ : ℝ × ℝ → ℝ} (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ)
    (hρs : ∀ p : ℝ × ℝ, ρ (-p) = ρ p) (hLT : LogPlaneTransfer)
    (hShift : LeafShiftUniform) (hInt : LeafPairIntegrable ρ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ α ∈ Set.Ioc (0 : ℝ) 1, ∀ ε ∈ Set.Ioc (0 : ℝ) 1,
      ∀ {w : ℝ → ℝ → ℝ} {a b : ℕ}, Work.FTS.TransportS.IsLeafW α a w → a + b ≤ 1 →
      ∀ u v : Fn, Work.FTS.VocabO.HQo α 1 u → Work.FTS.VocabO.HQo α 1 v →
      |Work.Coercivity.wip w (Work.Spaces.mixed b a (Work.FTS.StrongEps.Jeps ρ ε u))
          (Work.Spaces.mixed b a v)
        - Work.Coercivity.wip w (Work.Spaces.mixed b a u)
            (Work.Spaces.mixed b a (Work.FTS.StrongEps.Jeps ρ ε v))|
        ≤ K * ε * Work.Spaces.HkNorm α 1 u * Work.Spaces.HkNorm α 1 v := by
  obtain ⟨Cl, hCl0, hCl⟩ := hShift
  refine ⟨100 * (Cl + 1) * Real.exp (4 * Cl), by positivity, ?_⟩
  intro α hα ε hε w a b hleaf hab u v hu hv
  have hw' : w = Work.FTS.TransportS.leafEta ∨ w = Work.FTS.TransportS.leafOne
      ∨ w = Work.FTS.TransportS.leafGam α := by
    rcases hleaf with h | h | ⟨_, h⟩
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
  have hsh : ∀ y p : ℝ × ℝ,
      Work.FTS.StrongEps.E4R3.Apriori4Proofs.logW w (y + p)
          ≤ Real.exp (Cl * (|p.1| + |p.2|)) * Work.FTS.StrongEps.E4R3.Apriori4Proofs.logW w y
        ∧ Work.FTS.StrongEps.E4R3.Apriori4Proofs.logW w y
          ≤ Real.exp (Cl * (|p.1| + |p.2|))
            * Work.FTS.StrongEps.E4R3.Apriori4Proofs.logW w (y + p) :=
    hCl α hα w hw'
  have hwsh : ∀ y p : ℝ × ℝ, Work.FTS.StrongEps.E4R3.Apriori4Proofs.logW w (y + p)
      ≤ Real.exp (Cl * (|p.1| + |p.2|)) * Work.FTS.StrongEps.E4R3.Apriori4Proofs.logW w y :=
    fun y p => (hsh y p).1
  have hwsh' : ∀ y p : ℝ × ℝ, Work.FTS.StrongEps.E4R3.Apriori4Proofs.logW w y
      ≤ Real.exp (Cl * (|p.1| + |p.2|))
        * Work.FTS.StrongEps.E4R3.Apriori4Proofs.logW w (y + p) :=
    fun y p => (hsh y p).2
  have hw0 := logW_nonneg_of_leaf hleaf
  have hwm : Measurable (Work.FTS.StrongEps.E4R3.Apriori4Proofs.logW w) :=
    (Work.FTS.StrongEps.E4R3.Apriori4Proofs.JepsTransfer.continuous_logW_leaf hw').measurable
  have hε0 : 0 < ε := hε.1
  have hsu : Work.FTS.EllipticEst.SmoothOpen u := hu.1
  have hsv : Work.FTS.EllipticEst.SmoothOpen v := hv.1
  -- the joint integrability inputs
  obtain ⟨hJ1, hG1, hG2⟩ := hInt hα hε hleaf hab hu hv
  have hJ2 : MeasureTheory.Integrable
      (Function.uncurry (fun z θ => w z θ * Work.Spaces.mixed b a u z θ
        * Work.FTS.StrongEps.Jeps ρ ε (Work.Spaces.mixed b a v) z θ))
      (MeasureTheory.volume.restrict (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2))) := by
    have h := (hInt hα hε hleaf hab hv hu).1
    refine h.congr (Eventually.of_forall fun q => ?_)
    obtain ⟨q₁, q₂⟩ := q
    simp only [Function.uncurry_apply_pair]
    ring
  -- the two log-side integrability inputs
  have hsm1 := mixed_smooth_of_smoothOpen hsu b a
  have hsm2 := mixed_smooth_of_smoothOpen hsv b a
  have hfin1 : (∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ,
      ENNReal.ofReal (w z θ * (Work.Spaces.mixed b a u z θ) ^ 2)) ≠ ⊤ :=
    ne_top_of_lt (lt_of_le_of_lt (lintegral_leaf_le_HkSq hα.1 hu.2 hab hleaf)
      ENNReal.ofReal_lt_top)
  have hfin2 : (∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ,
      ENNReal.ofReal (w z θ * (Work.Spaces.mixed b a v z θ) ^ 2)) ≠ ⊤ :=
    ne_top_of_lt (lt_of_le_of_lt (lintegral_leaf_le_HkSq hα.1 hv.2 hab hleaf)
      ENNReal.ofReal_lt_top)
  have hI1 : MeasureTheory.Integrable (fun y : ℝ × ℝ
      => Work.FTS.StrongEps.E4R3.Apriori4Proofs.logW w y
          * (Work.FTS.StrongEps.E4R3.Apriori4Proofs.logPull (Work.Spaces.mixed b a u) y) ^ 2) :=
    integrable_logW_sq_of_lintegral hw0 hwm (Work.FTS.StrongEps.E4R3.Apriori4Proofs.JepsTransfer.logPull_continuous hsm1).aemeasurable hfin1
  have hI2 : MeasureTheory.Integrable (fun y : ℝ × ℝ
      => Work.FTS.StrongEps.E4R3.Apriori4Proofs.logW w y
          * (Work.FTS.StrongEps.E4R3.Apriori4Proofs.logPull (Work.Spaces.mixed b a v) y) ^ 2) :=
    integrable_logW_sq_of_lintegral hw0 hwm (Work.FTS.StrongEps.E4R3.Apriori4Proofs.JepsTransfer.logPull_continuous hsm2).aemeasurable hfin2
  -- the quadrant transfer
  have hT := pairing_transfer hρ hρs hLT hCl0 hw0 hwm hwsh hwsh' hε hsm1 hsm2
    hJ1 hJ2 hG1 hG2 hI1 hI2
  -- identify the `wip`-form with the quadrant form
  have e1 : Work.Coercivity.wip w (Work.Spaces.mixed b a (Work.FTS.StrongEps.Jeps ρ ε u))
        (Work.Spaces.mixed b a v)
      = ∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, w z θ
          * Work.FTS.StrongEps.Jeps ρ ε (Work.Spaces.mixed b a u) z θ
          * Work.Spaces.mixed b a v z θ := by
    rw [Work.FTS.StrongEps.EpsE4Thr.wip_congr_Q0_fst (ρ := w)
      (A := Work.Spaces.mixed b a (Work.FTS.StrongEps.Jeps ρ ε u))
      (A' := Work.FTS.StrongEps.Jeps ρ ε (Work.Spaces.mixed b a u))
      (B := Work.Spaces.mixed b a v)
      (fun z θ h => Work.FTS.StrongEps.mixed_Jeps ρ hρ.moll hε0
        (Work.FTS.EllipticEst.SmoothOpen.forall hsu) h.1 h.2 b a)]
    rw [wip_eq_flat]
  have e2 : Work.Coercivity.wip w (Work.Spaces.mixed b a u)
        (Work.Spaces.mixed b a (Work.FTS.StrongEps.Jeps ρ ε v))
      = ∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, w z θ
          * Work.Spaces.mixed b a u z θ
          * Work.FTS.StrongEps.Jeps ρ ε (Work.Spaces.mixed b a v) z θ := by
    rw [Work.FTS.StrongEps.EpsE4Thr.wip_congr_Q0_snd (ρ := w)
      (A := Work.Spaces.mixed b a u)
      (B := Work.Spaces.mixed b a (Work.FTS.StrongEps.Jeps ρ ε v))
      (B' := Work.FTS.StrongEps.Jeps ρ ε (Work.Spaces.mixed b a v))
      (fun z θ h => Work.FTS.StrongEps.mixed_Jeps ρ hρ.moll hε0
        (Work.FTS.EllipticEst.SmoothOpen.forall hsv) h.1 h.2 b a)]
    rw [wip_eq_flat]
  have e3 : Work.Coercivity.wip w (Work.Spaces.mixed b a u) (Work.Spaces.mixed b a u)
      = ∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
          w z θ * (Work.Spaces.mixed b a u z θ) ^ 2 := by
    rw [wip_eq_flat]
    refine MeasureTheory.integral_congr_ae (Eventually.of_forall fun z => ?_)
    refine MeasureTheory.integral_congr_ae (Eventually.of_forall fun θ => ?_)
    ring
  have e4 : Work.Coercivity.wip w (Work.Spaces.mixed b a v) (Work.Spaces.mixed b a v)
      = ∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
          w z θ * (Work.Spaces.mixed b a v z θ) ^ 2 := by
    rw [wip_eq_flat]
    refine MeasureTheory.integral_congr_ae (Eventually.of_forall fun z => ?_)
    refine MeasureTheory.integral_congr_ae (Eventually.of_forall fun θ => ?_)
    ring
  rw [e1, e2]
  refine hT.trans ?_
  have hA : Real.sqrt (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
      w z θ * (Work.Spaces.mixed b a u z θ) ^ 2)
      ≤ Work.Spaces.HkNorm α 1 u := by
    rw [← e3]
    exact sqrt_wip_self_le_HkNorm hα.1 hu.2 hab hleaf
  have hB : Real.sqrt (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
      w z θ * (Work.Spaces.mixed b a v z θ) ^ 2)
      ≤ Work.Spaces.HkNorm α 1 v := by
    rw [← e4]
    exact sqrt_wip_self_le_HkNorm hα.1 hv.2 hab hleaf
  have hu0 : (0 : ℝ) ≤ Work.Spaces.HkNorm α 1 u := Work.Spaces.HkNorm_nonneg α 1 u
  have hv0 : (0 : ℝ) ≤ Work.Spaces.HkNorm α 1 v := Work.Spaces.HkNorm_nonneg α 1 v
  gcongr


/-- The triangle inequality for four terms. -/
theorem abs_sum_four_le (a b c d : ℝ) : |a + b + c + d| ≤ |a| + |b| + |c| + |d| := by
  have h1 := abs_add_le (a + b + c) d
  have h2 := abs_add_le (a + b) c
  have h3 := abs_add_le a b
  linarith

/-- **The transfer estimate for the level-one pairing `H1IP`.** -/
theorem H1IP_transfer_of {ρ : ℝ × ℝ → ℝ} (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ)
    (hρs : ∀ p : ℝ × ℝ, ρ (-p) = ρ p) (hLT : LogPlaneTransfer)
    (hShift : LeafShiftUniform) (hInt : LeafPairIntegrable ρ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ α ∈ Set.Ioc (0 : ℝ) 1, ∀ ε ∈ Set.Ioc (0 : ℝ) 1,
      ∀ u v : Fn, Work.FTS.VocabO.HQo α 1 u → Work.FTS.VocabO.HQo α 1 v →
      |Work.Coercivity.H1IP α (Work.FTS.StrongEps.Jeps ρ ε u) v
        - Work.Coercivity.H1IP α u (Work.FTS.StrongEps.Jeps ρ ε v)|
        ≤ K * ε * Work.Spaces.HkNorm α 1 u * Work.Spaces.HkNorm α 1 v := by
  obtain ⟨Ks, hKs0, hKs⟩ := slot_transfer_of hρ hρs hLT hShift hInt
  refine ⟨(10 + 10 ^ 10 + 10 ^ 17 + 10 ^ 21) * Ks, by positivity, ?_⟩
  intro α hα ε hε u v hu hv
  have hL1 := hKs α hα ε hε (w := Work.FTS.TransportS.leafEta) (a := 0) (b := 1)
    (Or.inl rfl) (by norm_num) u v hu hv
  have hL2 := hKs α hα ε hε (w := Work.FTS.TransportS.leafEta) (a := 0) (b := 0)
    (Or.inl rfl) (by norm_num) u v hu hv
  have hL3 := hKs α hα ε hε (w := Work.FTS.TransportS.leafOne) (a := 0) (b := 0)
    (Or.inr (Or.inl rfl)) (by norm_num) u v hu hv
  have hL4 := hKs α hα ε hε (w := Work.FTS.TransportS.leafGam α) (a := 1) (b := 0)
    (Or.inr (Or.inr ⟨le_refl 1, rfl⟩)) (by norm_num) u v hu hv
  have hA1 : |Work.Coercivity.wip Work.FTS.TransportS.leafEta
        (Work.Spaces.Dz (Work.FTS.StrongEps.Jeps ρ ε u)) (Work.Spaces.Dz v)
      - Work.Coercivity.wip Work.FTS.TransportS.leafEta
        (Work.Spaces.Dz u) (Work.Spaces.Dz (Work.FTS.StrongEps.Jeps ρ ε v))|
      ≤ Ks * ε * Work.Spaces.HkNorm α 1 u * Work.Spaces.HkNorm α 1 v := by
    simpa only [Work.Spaces.mixed_zero_right, Work.Spaces.DzIter_succ,
      Work.Spaces.DzIter_zero, Work.Spaces.DthIter_zero] using hL1
  have hA2 : |Work.Coercivity.wip Work.FTS.TransportS.leafEta
        (Work.FTS.StrongEps.Jeps ρ ε u) v
      - Work.Coercivity.wip Work.FTS.TransportS.leafEta
        u (Work.FTS.StrongEps.Jeps ρ ε v)|
      ≤ Ks * ε * Work.Spaces.HkNorm α 1 u * Work.Spaces.HkNorm α 1 v := by
    simpa only [Work.Spaces.mixed_zero_right, Work.Spaces.mixed_zero_left,
      Work.Spaces.DzIter_zero, Work.Spaces.DthIter_zero] using hL2
  have hA3 : |Work.Coercivity.wip Work.FTS.TransportS.leafOne
        (Work.FTS.StrongEps.Jeps ρ ε u) v
      - Work.Coercivity.wip Work.FTS.TransportS.leafOne
        u (Work.FTS.StrongEps.Jeps ρ ε v)|
      ≤ Ks * ε * Work.Spaces.HkNorm α 1 u * Work.Spaces.HkNorm α 1 v := by
    simpa only [Work.Spaces.mixed_zero_right, Work.Spaces.mixed_zero_left,
      Work.Spaces.DzIter_zero, Work.Spaces.DthIter_zero] using hL3
  have hA4 : |Work.Coercivity.wip (Work.FTS.TransportS.leafGam α)
        (Work.Spaces.Dth (Work.FTS.StrongEps.Jeps ρ ε u)) (Work.Spaces.Dth v)
      - Work.Coercivity.wip (Work.FTS.TransportS.leafGam α)
        (Work.Spaces.Dth u) (Work.Spaces.Dth (Work.FTS.StrongEps.Jeps ρ ε v))|
      ≤ Ks * ε * Work.Spaces.HkNorm α 1 u * Work.Spaces.HkNorm α 1 v := by
    simpa only [Work.Spaces.mixed_zero_left, Work.Spaces.DthIter_succ,
      Work.Spaces.DthIter_zero, Work.Spaces.DzIter_zero] using hL4
  have hdecomp : Work.Coercivity.H1IP α (Work.FTS.StrongEps.Jeps ρ ε u) v
        - Work.Coercivity.H1IP α u (Work.FTS.StrongEps.Jeps ρ ε v)
      = 10 * (Work.Coercivity.wip Work.FTS.TransportS.leafEta
            (Work.Spaces.Dz (Work.FTS.StrongEps.Jeps ρ ε u)) (Work.Spaces.Dz v)
          - Work.Coercivity.wip Work.FTS.TransportS.leafEta
            (Work.Spaces.Dz u) (Work.Spaces.Dz (Work.FTS.StrongEps.Jeps ρ ε v)))
        + 10 ^ 10 * (Work.Coercivity.wip Work.FTS.TransportS.leafEta
            (Work.FTS.StrongEps.Jeps ρ ε u) v
          - Work.Coercivity.wip Work.FTS.TransportS.leafEta
            u (Work.FTS.StrongEps.Jeps ρ ε v))
        + 10 ^ 17 * (Work.Coercivity.wip Work.FTS.TransportS.leafOne
            (Work.FTS.StrongEps.Jeps ρ ε u) v
          - Work.Coercivity.wip Work.FTS.TransportS.leafOne
            u (Work.FTS.StrongEps.Jeps ρ ε v))
        + 10 ^ 21 * (Work.Coercivity.wip (Work.FTS.TransportS.leafGam α)
            (Work.Spaces.Dth (Work.FTS.StrongEps.Jeps ρ ε u)) (Work.Spaces.Dth v)
          - Work.Coercivity.wip (Work.FTS.TransportS.leafGam α)
            (Work.Spaces.Dth u) (Work.Spaces.Dth (Work.FTS.StrongEps.Jeps ρ ε v))) := by
    simp only [Work.Coercivity.H1IP]
    rw [show (fun z θ : ℝ => (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
        = Work.FTS.TransportS.leafEta from rfl,
      show (fun z _ : ℝ => (Work.Spaces.w z) ^ 2) = Work.FTS.TransportS.leafOne from rfl,
      show (fun z θ : ℝ => (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))
        = Work.FTS.TransportS.leafGam α from rfl]
    ring
  rw [hdecomp]
  have hu0 : (0 : ℝ) ≤ Work.Spaces.HkNorm α 1 u := Work.Spaces.HkNorm_nonneg α 1 u
  have hv0 : (0 : ℝ) ≤ Work.Spaces.HkNorm α 1 v := Work.Spaces.HkNorm_nonneg α 1 v
  have hmain : |10 * (Work.Coercivity.wip Work.FTS.TransportS.leafEta
              (Work.Spaces.Dz (Work.FTS.StrongEps.Jeps ρ ε u)) (Work.Spaces.Dz v)
            - Work.Coercivity.wip Work.FTS.TransportS.leafEta
              (Work.Spaces.Dz u) (Work.Spaces.Dz (Work.FTS.StrongEps.Jeps ρ ε v)))
          + 10 ^ 10 * (Work.Coercivity.wip Work.FTS.TransportS.leafEta
              (Work.FTS.StrongEps.Jeps ρ ε u) v
            - Work.Coercivity.wip Work.FTS.TransportS.leafEta
              u (Work.FTS.StrongEps.Jeps ρ ε v))
          + 10 ^ 17 * (Work.Coercivity.wip Work.FTS.TransportS.leafOne
              (Work.FTS.StrongEps.Jeps ρ ε u) v
            - Work.Coercivity.wip Work.FTS.TransportS.leafOne
              u (Work.FTS.StrongEps.Jeps ρ ε v))
          + 10 ^ 21 * (Work.Coercivity.wip (Work.FTS.TransportS.leafGam α)
              (Work.Spaces.Dth (Work.FTS.StrongEps.Jeps ρ ε u)) (Work.Spaces.Dth v)
            - Work.Coercivity.wip (Work.FTS.TransportS.leafGam α)
              (Work.Spaces.Dth u) (Work.Spaces.Dth (Work.FTS.StrongEps.Jeps ρ ε v)))|
      ≤ 10 * (Ks * ε * Work.Spaces.HkNorm α 1 u * Work.Spaces.HkNorm α 1 v)
          + 10 ^ 10 * (Ks * ε * Work.Spaces.HkNorm α 1 u * Work.Spaces.HkNorm α 1 v)
          + 10 ^ 17 * (Ks * ε * Work.Spaces.HkNorm α 1 u * Work.Spaces.HkNorm α 1 v)
          + 10 ^ 21 * (Ks * ε * Work.Spaces.HkNorm α 1 u * Work.Spaces.HkNorm α 1 v) := by
    refine (abs_sum_four_le _ _ _ _).trans ?_
    rw [abs_mul, abs_mul, abs_mul, abs_mul]
    norm_num
    linarith
  refine hmain.trans ?_
  ring_nf
  linarith [hKs0, hα.1, hε.1, hu0, hv0]


/-- The triangle inequality for three terms. -/
theorem abs_sum_three_le (a b c : ℝ) : |a + b + c| ≤ |a| + |b| + |c| := by
  have h1 := abs_add_le (a + b) c
  have h2 := abs_add_le a b
  linarith

/-- **The transfer estimate for the recursion `IPn`.** -/
theorem delta_bound_of {ρ : ℝ × ℝ → ℝ} (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ)
    (hρs : ∀ p : ℝ × ℝ, ρ (-p) = ρ p) (hLT : LogPlaneTransfer)
    (hShift : LeafShiftUniform) (hInt : LeafPairIntegrable ρ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ α ∈ Set.Ioc (0 : ℝ) 1, ∀ ε ∈ Set.Ioc (0 : ℝ) 1,
      ∀ u v : Fn,
      Work.FTS.VocabO.HQo α 6 u → Work.FTS.VocabO.HQo α 6 v →
      |Work.FTS.TransportS.IPn α 5 (Work.FTS.StrongEps.Jeps ρ ε u) v
        - Work.FTS.TransportS.IPn α 5 u (Work.FTS.StrongEps.Jeps ρ ε v)|
        ≤ K * ε * Work.Spaces.HkNorm α 6 u * Work.Spaces.HkNorm α 6 v := by
  obtain ⟨K0, hK00, hK0⟩ := H1IP_transfer_of hρ hρs hLT hShift hInt
  refine ⟨3 ^ 5 * K0, by positivity, ?_⟩
  intro α hα ε hε
  have hα0 : 0 < α := hα.1
  have hε0 : 0 < ε := hε.1
  have hmono : -(1 / 10 : ℝ) ≤ α := by linarith
  have hmain : ∀ n : ℕ, ∀ u v : Fn,
      Work.FTS.VocabO.HQo α (n + 1) u → Work.FTS.VocabO.HQo α (n + 1) v →
      |Work.FTS.TransportS.IPn α n (Work.FTS.StrongEps.Jeps ρ ε u) v
        - Work.FTS.TransportS.IPn α n u (Work.FTS.StrongEps.Jeps ρ ε v)|
        ≤ 3 ^ n * K0 * ε * Work.Spaces.HkNorm α (n + 1) u
            * Work.Spaces.HkNorm α (n + 1) v := by
    intro n
    induction n with
    | zero =>
        intro u v hu hv
        simpa only [Work.FTS.TransportS.IPn, pow_zero, one_mul] using hK0 α hα ε hε u v hu hv
    | succ n ih =>
        intro u v hu hv
        have huQ : ∀ m : ℕ, ContDiffOn ℝ m (Function.uncurry u) Work.FTS.StrongEps.Quad :=
          hu.1.forall
        have hvQ : ∀ m : ℕ, ContDiffOn ℝ m (Function.uncurry v) Work.FTS.StrongEps.Quad :=
          hv.1.forall
        have hrec := Work.FTS.StrongEps.E4R3.Apriori4Proofs.JepsTransfer.IPn_succ_Jeps
          ρ hρ (α := α) hε0 huQ hvQ n
        have hm1 : Work.FTS.VocabO.HQo α (n + 1) u :=
          Work.FTS.StrongPersist.hqo_mono (by omega : n + 1 ≤ n + 2) hu
        have hm2 : Work.FTS.VocabO.HQo α (n + 1) v :=
          Work.FTS.StrongPersist.hqo_mono (by omega : n + 1 ≤ n + 2) hv
        have hthu : Work.FTS.VocabO.HQo α (n + 1) (Work.Spaces.Dth u) :=
          Work.FTS.StrongPersist.hqo_dth hmono hu
        have hthv : Work.FTS.VocabO.HQo α (n + 1) (Work.Spaces.Dth v) :=
          Work.FTS.StrongPersist.hqo_dth hmono hv
        have hzu : Work.FTS.VocabO.HQo α (n + 1) (Work.Spaces.Dz u) :=
          Work.FTS.StrongPersist.hqo_dz hu
        have hzv : Work.FTS.VocabO.HQo α (n + 1) (Work.Spaces.Dz v) :=
          Work.FTS.StrongPersist.hqo_dz hv
        have i1 := ih u v hm1 hm2
        have i2 := ih (Work.Spaces.Dth u) (Work.Spaces.Dth v) hthu hthv
        have i3 := ih (Work.Spaces.Dz u) (Work.Spaces.Dz v) hzu hzv
        have n1u : Work.Spaces.HkNorm α (n + 1) u ≤ Work.Spaces.HkNorm α (n + 2) u :=
          Work.FTS.StrongPersist.hkNorm_mono hu.2
        have n1v : Work.Spaces.HkNorm α (n + 1) v ≤ Work.Spaces.HkNorm α (n + 2) v :=
          Work.FTS.StrongPersist.hkNorm_mono hv.2
        have n2u : Work.Spaces.HkNorm α (n + 1) (Work.Spaces.Dth u)
            ≤ Work.Spaces.HkNorm α (n + 2) u :=
          Work.FTS.StrongPersist.hkNorm_dth hα0 hu.2
        have n2v : Work.Spaces.HkNorm α (n + 1) (Work.Spaces.Dth v)
            ≤ Work.Spaces.HkNorm α (n + 2) v :=
          Work.FTS.StrongPersist.hkNorm_dth hα0 hv.2
        have n3u : Work.Spaces.HkNorm α (n + 1) (Work.Spaces.Dz u)
            ≤ Work.Spaces.HkNorm α (n + 2) u :=
          Work.FTS.StrongPersist.hkNorm_dz hu.1 hu.2
        have n3v : Work.Spaces.HkNorm α (n + 1) (Work.Spaces.Dz v)
            ≤ Work.Spaces.HkNorm α (n + 2) v :=
          Work.FTS.StrongPersist.hkNorm_dz hv.1 hv.2
        have g0 : (0 : ℝ) ≤ 3 ^ n * K0 * ε := by positivity
        have hU0 : (0 : ℝ) ≤ Work.Spaces.HkNorm α (n + 2) u :=
          Work.Spaces.HkNorm_nonneg α (n + 2) u
        have hV0 : (0 : ℝ) ≤ Work.Spaces.HkNorm α (n + 2) v :=
          Work.Spaces.HkNorm_nonneg α (n + 2) v
        have g1 : 3 ^ n * K0 * ε * Work.Spaces.HkNorm α (n + 1) u
              * Work.Spaces.HkNorm α (n + 1) v
            ≤ 3 ^ n * K0 * ε * Work.Spaces.HkNorm α (n + 2) u
              * Work.Spaces.HkNorm α (n + 2) v := by
          refine (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left n1u g0)
            (Work.Spaces.HkNorm_nonneg α (n + 1) v)).trans ?_
          exact mul_le_mul_of_nonneg_left n1v (by positivity)
        have g2 : 3 ^ n * K0 * ε * Work.Spaces.HkNorm α (n + 1) (Work.Spaces.Dth u)
              * Work.Spaces.HkNorm α (n + 1) (Work.Spaces.Dth v)
            ≤ 3 ^ n * K0 * ε * Work.Spaces.HkNorm α (n + 2) u
              * Work.Spaces.HkNorm α (n + 2) v := by
          refine (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left n2u g0)
            (Work.Spaces.HkNorm_nonneg α (n + 1) (Work.Spaces.Dth v))).trans ?_
          exact mul_le_mul_of_nonneg_left n2v (by positivity)
        have g3 : 3 ^ n * K0 * ε * Work.Spaces.HkNorm α (n + 1) (Work.Spaces.Dz u)
              * Work.Spaces.HkNorm α (n + 1) (Work.Spaces.Dz v)
            ≤ 3 ^ n * K0 * ε * Work.Spaces.HkNorm α (n + 2) u
              * Work.Spaces.HkNorm α (n + 2) v := by
          refine (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left n3u g0)
            (Work.Spaces.HkNorm_nonneg α (n + 1) (Work.Spaces.Dz v))).trans ?_
          exact mul_le_mul_of_nonneg_left n3v (by positivity)
        rw [hrec]
        refine (abs_sum_three_le _ _ _).trans ?_
        have hsum : |Work.FTS.TransportS.IPn α n (Work.FTS.StrongEps.Jeps ρ ε u) v
              - Work.FTS.TransportS.IPn α n u (Work.FTS.StrongEps.Jeps ρ ε v)|
            + |Work.FTS.TransportS.IPn α n (Work.FTS.StrongEps.Jeps ρ ε (Work.Spaces.Dth u))
                (Work.Spaces.Dth v)
              - Work.FTS.TransportS.IPn α n (Work.Spaces.Dth u)
                (Work.FTS.StrongEps.Jeps ρ ε (Work.Spaces.Dth v))|
            + |Work.FTS.TransportS.IPn α n (Work.FTS.StrongEps.Jeps ρ ε (Work.Spaces.Dz u))
                (Work.Spaces.Dz v)
              - Work.FTS.TransportS.IPn α n (Work.Spaces.Dz u)
                (Work.FTS.StrongEps.Jeps ρ ε (Work.Spaces.Dz v))|
            ≤ 3 ^ n * K0 * ε * Work.Spaces.HkNorm α (n + 1) u
                * Work.Spaces.HkNorm α (n + 1) v
              + 3 ^ n * K0 * ε * Work.Spaces.HkNorm α (n + 1) (Work.Spaces.Dth u)
                * Work.Spaces.HkNorm α (n + 1) (Work.Spaces.Dth v)
              + 3 ^ n * K0 * ε * Work.Spaces.HkNorm α (n + 1) (Work.Spaces.Dz u)
                * Work.Spaces.HkNorm α (n + 1) (Work.Spaces.Dz v) := by
          linarith [i1, i2, i3]
        refine hsum.trans ?_
        have hfin : 3 ^ n * K0 * ε * Work.Spaces.HkNorm α (n + 1) u
                * Work.Spaces.HkNorm α (n + 1) v
              + 3 ^ n * K0 * ε * Work.Spaces.HkNorm α (n + 1) (Work.Spaces.Dth u)
                * Work.Spaces.HkNorm α (n + 1) (Work.Spaces.Dth v)
              + 3 ^ n * K0 * ε * Work.Spaces.HkNorm α (n + 1) (Work.Spaces.Dz u)
                * Work.Spaces.HkNorm α (n + 1) (Work.Spaces.Dz v)
            ≤ 3 ^ (n + 1) * K0 * ε * Work.Spaces.HkNorm α (n + 2) u
                * Work.Spaces.HkNorm α (n + 2) v := by
          have h3 : (3 : ℝ) ^ (n + 1) * K0 * ε * Work.Spaces.HkNorm α (n + 2) u
                * Work.Spaces.HkNorm α (n + 2) v
              = (3 ^ n * K0 * ε * Work.Spaces.HkNorm α (n + 2) u
                * Work.Spaces.HkNorm α (n + 2) v) * 3 := by
            rw [pow_succ]; ring
          rw [h3]
          linarith [g1, g2, g3]
        exact hfin
  intro u v hu hv
  exact hmain 5 u v hu hv

end Work.FTS.StrongEps.E4R3.Apriori4Proofs.JT
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.E4R3.Apriori4Proofs.TransferDeriv.IP4Leaf =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `TransferDeriv/IP4Leaf.lean` — the level-zero transfer bound

The level-one pairing `H1IP α` is a linear combination of four `wip` slots, so its transfer defect
at the shifted words `D_z^{b₀}D_θ^{a₀}` is the sum of four *slot* defects, each controlled by the
hypothesis `SlotTransfer`; the `√`-factors are replaced by the `ℋ⁴`- and `ℋ⁵`-norms.
-/

namespace Work.FTS.StrongEps.E4R3.Apriori4Proofs.TransferDeriv

open scoped Real Topology
open MeasureTheory Set Filter

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false

/-! ## The level-zero bound -/

/-- The slot transfer hypothesis of the headline, as a predicate. -/
def SlotTransfer (ρ : ℝ × ℝ → ℝ) (K : ℝ) : Prop :=
  ∀ α ∈ Set.Ioc (0 : ℝ) 1, ∀ ε ∈ Set.Ioc (0 : ℝ) 1,
    ∀ {w : ℝ → ℝ → ℝ} {a b : ℕ}, Work.FTS.TransportS.IsLeafW α a w → a + b ≤ 4 →
    ∀ u v : Fn, Work.FTS.EllipticEst.SmoothOpen u → Work.FTS.EllipticEst.SmoothOpen v →
    SlotIntegrableDeriv ρ ε w a b u v →
    |Work.Coercivity.wip w (Work.Spaces.mixed b a (Work.FTS.StrongEps.Jeps ρ ε u))
        (Work.Spaces.mixed b a v)
      - Work.Coercivity.wip w (Work.Spaces.mixed b a u)
          (Work.Spaces.mixed b a (Work.FTS.StrongEps.Jeps ρ ε v))|
      ≤ K * ε * Real.sqrt (Work.Coercivity.wip w (Work.Spaces.mixed b a u)
            (Work.Spaces.mixed b a u))
        * (Real.sqrt (Work.Coercivity.wip w (Work.Spaces.mixed b a v)
              (Work.Spaces.mixed b a v))
          + Real.sqrt (Work.Coercivity.wip w (Work.Spaces.mixed (b + 1) a v)
              (Work.Spaces.mixed (b + 1) a v))
          + Real.sqrt (Work.Coercivity.wip w (Work.Spaces.mixed b (a + 1) v)
              (Work.Spaces.mixed b (a + 1) v)))

theorem abs_sum_four_le (a b c d : ℝ) : |a + b + c + d| ≤ |a| + |b| + |c| + |d| := by
  have h1 := abs_add_le (a + b + c) d
  have h2 := abs_add_le (a + b) c
  have h3 := abs_add_le a b
  linarith

/-- **The slot transfer at the shifted words.**  The slot transfer hypothesis, applied to the two
schematically given profiles `D_z^{b₀}D_θ^{a₀}f` and `D_z^{b₀}D_θ^{a₀}h` through their cuts, with
the `√`-factors replaced by the `ℋ⁴`- and `ℋ⁵`-norms by the composed-slot identity. -/
theorem slot_bound {ρ : ℝ × ℝ → ℝ} (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ) {K : ℝ}
    (hK : 0 ≤ K) (hST : SlotTransfer ρ K) {α : ℝ} (hα : α ∈ Set.Ioc (0 : ℝ) 1)
    {ε : ℝ} (hε : ε ∈ Set.Ioc (0 : ℝ) 1) {f h : Fn}
    (hfs : Work.FTS.EllipticEst.SmoothOpen f) (hhs : Work.FTS.EllipticEst.SmoothOpen h)
    (hmf : Work.Spaces.HkMem α 4 f) (hmh : Work.Spaces.HkMem α 5 h) {a₀ b₀ : ℕ}
    (hab₀ : a₀ + b₀ ≤ 3) {w : ℝ → ℝ → ℝ} {a b : ℕ}
    (hleaf : Work.FTS.TransportS.IsLeafW α a w) (hab : a + b ≤ 1) :
    |Work.Coercivity.wip w
        (Work.Spaces.mixed b a (Work.FTS.StrongEps.Jeps ρ ε (Work.Spaces.mixed b₀ a₀ f)))
        (Work.Spaces.mixed b a (Work.Spaces.mixed b₀ a₀ h))
      - Work.Coercivity.wip w (Work.Spaces.mixed b a (Work.Spaces.mixed b₀ a₀ f))
          (Work.Spaces.mixed b a (Work.FTS.StrongEps.Jeps ρ ε (Work.Spaces.mixed b₀ a₀ h)))|
      ≤ K * ε * Work.Spaces.HkNorm α 4 f * (3 * Work.Spaces.HkNorm α 5 h) := by
  have hα0 : 0 < α := hα.1
  have hε0 : 0 < ε := hε.1
  set U : Fn := cut (Work.Spaces.mixed b₀ a₀ f) with hU
  set V : Fn := cut (Work.Spaces.mixed b₀ a₀ h) with hV
  have hJU : Work.FTS.StrongEps.Jeps ρ ε U
      = Work.FTS.StrongEps.Jeps ρ ε (Work.Spaces.mixed b₀ a₀ f) := Jeps_cut ρ ε _
  have hJV : Work.FTS.StrongEps.Jeps ρ ε V
      = Work.FTS.StrongEps.Jeps ρ ε (Work.Spaces.mixed b₀ a₀ h) := Jeps_cut ρ ε _
  have hint := slotIntegrableDeriv_cut hρ hα hε hfs hhs hmf hmh hab₀ hab hleaf
  have h1 := hST α hα ε hε hleaf (by omega) U V
    (by rw [hU]; exact smoothOpen_cut (hfs.mixed b₀ a₀))
    (by rw [hV]; exact smoothOpen_cut (hhs.mixed b₀ a₀)) hint
  have hconv1 : Work.Coercivity.wip w
        (Work.Spaces.mixed b a (Work.FTS.StrongEps.Jeps ρ ε (Work.Spaces.mixed b₀ a₀ f)))
        (Work.Spaces.mixed b a V)
      = Work.Coercivity.wip w
        (Work.Spaces.mixed b a (Work.FTS.StrongEps.Jeps ρ ε (Work.Spaces.mixed b₀ a₀ f)))
        (Work.Spaces.mixed b a (Work.Spaces.mixed b₀ a₀ h)) :=
    Work.FTS.StrongEps.EpsE4Thr.wip_congr_Q0_snd
      (fun z θ hh => by rw [hV]; exact mixed_cut_eqOn_Q0 (Work.Spaces.mixed b₀ a₀ h) b a hh)
  have hconv2 : Work.Coercivity.wip w (Work.Spaces.mixed b a U)
        (Work.Spaces.mixed b a (Work.FTS.StrongEps.Jeps ρ ε (Work.Spaces.mixed b₀ a₀ h)))
      = Work.Coercivity.wip w (Work.Spaces.mixed b a (Work.Spaces.mixed b₀ a₀ f))
        (Work.Spaces.mixed b a (Work.FTS.StrongEps.Jeps ρ ε (Work.Spaces.mixed b₀ a₀ h))) :=
    Work.FTS.StrongEps.EpsE4Thr.wip_congr_Q0_fst
      (fun z θ hh => by rw [hU]; exact mixed_cut_eqOn_Q0 (Work.Spaces.mixed b₀ a₀ f) b a hh)
  rw [hJU, hJV, hconv1, hconv2] at h1
  -- the `√`-factors
  have hAU : Real.sqrt (Work.Coercivity.wip w (Work.Spaces.mixed b a U)
        (Work.Spaces.mixed b a U)) ≤ Work.Spaces.HkNorm α 4 f := by
    rw [hU]
    exact sqrt_wip_cut_le hα0 hfs (by omega : (a + a₀) + (b + b₀) ≤ 4) (IsLeafW.add hleaf) hmf
  have hBV : Real.sqrt (Work.Coercivity.wip w (Work.Spaces.mixed b a V)
        (Work.Spaces.mixed b a V)) ≤ Work.Spaces.HkNorm α 5 h := by
    rw [hV]
    exact sqrt_wip_cut_le hα0 hhs (by omega : (a + a₀) + (b + b₀) ≤ 5) (IsLeafW.add hleaf) hmh
  have hBV1 : Real.sqrt (Work.Coercivity.wip w (Work.Spaces.mixed (b + 1) a V)
        (Work.Spaces.mixed (b + 1) a V)) ≤ Work.Spaces.HkNorm α 5 h := by
    rw [hV]
    exact sqrt_wip_cut_le hα0 hhs (by omega : (a + a₀) + (b + 1 + b₀) ≤ 5)
      (IsLeafW.mono hleaf (Nat.le_add_right a a₀)) hmh
  have hBV2 : Real.sqrt (Work.Coercivity.wip w (Work.Spaces.mixed b (a + 1) V)
        (Work.Spaces.mixed b (a + 1) V)) ≤ Work.Spaces.HkNorm α 5 h := by
    rw [hV]
    exact sqrt_wip_cut_le hα0 hhs (by omega : (a + 1 + a₀) + (b + b₀) ≤ 5)
      (IsLeafW.mono hleaf (by omega : a ≤ a + 1 + a₀)) hmh
  have hN4 : (0 : ℝ) ≤ Work.Spaces.HkNorm α 4 f := Work.Spaces.HkNorm_nonneg α 4 f
  have hN5 : (0 : ℝ) ≤ Work.Spaces.HkNorm α 5 h := Work.Spaces.HkNorm_nonneg α 5 h
  have hR : (0 : ℝ) ≤ Real.sqrt (Work.Coercivity.wip w (Work.Spaces.mixed b a V)
        (Work.Spaces.mixed b a V))
      + Real.sqrt (Work.Coercivity.wip w (Work.Spaces.mixed (b + 1) a V)
          (Work.Spaces.mixed (b + 1) a V))
      + Real.sqrt (Work.Coercivity.wip w (Work.Spaces.mixed b (a + 1) V)
          (Work.Spaces.mixed b (a + 1) V)) := by positivity
  have hL : K * ε * Real.sqrt (Work.Coercivity.wip w (Work.Spaces.mixed b a U)
        (Work.Spaces.mixed b a U)) ≤ K * ε * Work.Spaces.HkNorm α 4 f :=
    mul_le_mul_of_nonneg_left hAU (mul_nonneg hK hε0.le)
  have h2 : Real.sqrt (Work.Coercivity.wip w (Work.Spaces.mixed b a V)
          (Work.Spaces.mixed b a V))
        + Real.sqrt (Work.Coercivity.wip w (Work.Spaces.mixed (b + 1) a V)
            (Work.Spaces.mixed (b + 1) a V))
        + Real.sqrt (Work.Coercivity.wip w (Work.Spaces.mixed b (a + 1) V)
            (Work.Spaces.mixed b (a + 1) V))
      ≤ 3 * Work.Spaces.HkNorm α 5 h := by linarith
  refine h1.trans ?_
  refine (mul_le_mul hL h2 hR (by positivity)).trans (le_of_eq ?_)
  ring

/-- The four-slot decomposition of `H1IP`. -/
theorem H1IP_eq_slots (α : ℝ) (X Y : Fn) :
    Work.Coercivity.H1IP α X Y
      = 10 * Work.Coercivity.wip Work.FTS.TransportS.leafEta (Work.Spaces.Dz X)
            (Work.Spaces.Dz Y)
        + 10 ^ 10 * Work.Coercivity.wip Work.FTS.TransportS.leafEta X Y
        + 10 ^ 17 * Work.Coercivity.wip Work.FTS.TransportS.leafOne X Y
        + 10 ^ 21 * Work.Coercivity.wip (Work.FTS.TransportS.leafGam α)
            (Work.Spaces.Dth X) (Work.Spaces.Dth Y) := by
  simp only [Work.Coercivity.H1IP]
  rw [show (fun z θ : ℝ => (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
        = Work.FTS.TransportS.leafEta from rfl,
      show (fun z _ : ℝ => (Work.Spaces.w z) ^ 2) = Work.FTS.TransportS.leafOne from rfl,
      show (fun z θ : ℝ => (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))
        = Work.FTS.TransportS.leafGam α from rfl]

/-- **The level-zero transfer bound**: the transfer defect of `H1IP` at the shifted words is
`O(ε)`, with one derivative charged on the second argument. -/
theorem leaf_bound {ρ : ℝ × ℝ → ℝ} (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ) {K : ℝ}
    (hK : 0 ≤ K) (hST : SlotTransfer ρ K) {α : ℝ} (hα : α ∈ Set.Ioc (0 : ℝ) 1)
    {ε : ℝ} (hε : ε ∈ Set.Ioc (0 : ℝ) 1) {f h : Fn}
    (hfs : Work.FTS.EllipticEst.SmoothOpen f) (hhs : Work.FTS.EllipticEst.SmoothOpen h)
    (hmf : Work.Spaces.HkMem α 4 f) (hmh : Work.Spaces.HkMem α 5 h) {a₀ b₀ : ℕ}
    (hab : a₀ + b₀ ≤ 3) :
    |Work.Coercivity.H1IP α
        (Work.FTS.StrongEps.Jeps ρ ε (Work.Spaces.mixed b₀ a₀ f))
        (Work.Spaces.mixed b₀ a₀ h)
      - Work.Coercivity.H1IP α (Work.Spaces.mixed b₀ a₀ f)
          (Work.FTS.StrongEps.Jeps ρ ε (Work.Spaces.mixed b₀ a₀ h))|
      ≤ 3 * (10 + 10 ^ 10 + 10 ^ 17 + 10 ^ 21) * K * ε
          * Work.Spaces.HkNorm α 4 f * Work.Spaces.HkNorm α 5 h := by
  have hdecomp : Work.Coercivity.H1IP α
        (Work.FTS.StrongEps.Jeps ρ ε (Work.Spaces.mixed b₀ a₀ f))
        (Work.Spaces.mixed b₀ a₀ h)
      - Work.Coercivity.H1IP α (Work.Spaces.mixed b₀ a₀ f)
          (Work.FTS.StrongEps.Jeps ρ ε (Work.Spaces.mixed b₀ a₀ h))
      = 10 * (Work.Coercivity.wip Work.FTS.TransportS.leafEta
            (Work.Spaces.Dz (Work.FTS.StrongEps.Jeps ρ ε (Work.Spaces.mixed b₀ a₀ f)))
            (Work.Spaces.Dz (Work.Spaces.mixed b₀ a₀ h))
          - Work.Coercivity.wip Work.FTS.TransportS.leafEta
            (Work.Spaces.Dz (Work.Spaces.mixed b₀ a₀ f))
            (Work.Spaces.Dz (Work.FTS.StrongEps.Jeps ρ ε (Work.Spaces.mixed b₀ a₀ h))))
        + 10 ^ 10 * (Work.Coercivity.wip Work.FTS.TransportS.leafEta
            (Work.FTS.StrongEps.Jeps ρ ε (Work.Spaces.mixed b₀ a₀ f))
            (Work.Spaces.mixed b₀ a₀ h)
          - Work.Coercivity.wip Work.FTS.TransportS.leafEta (Work.Spaces.mixed b₀ a₀ f)
            (Work.FTS.StrongEps.Jeps ρ ε (Work.Spaces.mixed b₀ a₀ h)))
        + 10 ^ 17 * (Work.Coercivity.wip Work.FTS.TransportS.leafOne
            (Work.FTS.StrongEps.Jeps ρ ε (Work.Spaces.mixed b₀ a₀ f))
            (Work.Spaces.mixed b₀ a₀ h)
          - Work.Coercivity.wip Work.FTS.TransportS.leafOne (Work.Spaces.mixed b₀ a₀ f)
            (Work.FTS.StrongEps.Jeps ρ ε (Work.Spaces.mixed b₀ a₀ h)))
        + 10 ^ 21 * (Work.Coercivity.wip (Work.FTS.TransportS.leafGam α)
            (Work.Spaces.Dth (Work.FTS.StrongEps.Jeps ρ ε (Work.Spaces.mixed b₀ a₀ f)))
            (Work.Spaces.Dth (Work.Spaces.mixed b₀ a₀ h))
          - Work.Coercivity.wip (Work.FTS.TransportS.leafGam α)
            (Work.Spaces.Dth (Work.Spaces.mixed b₀ a₀ f))
            (Work.Spaces.Dth (Work.FTS.StrongEps.Jeps ρ ε (Work.Spaces.mixed b₀ a₀ h)))) := by
    rw [H1IP_eq_slots, H1IP_eq_slots]
    ring
  have i1 := slot_bound hρ hK hST hα hε hfs hhs hmf hmh hab
    (w := Work.FTS.TransportS.leafEta) (a := 0) (b := 1) (Or.inl rfl) (by norm_num)
  have i2 := slot_bound hρ hK hST hα hε hfs hhs hmf hmh hab
    (w := Work.FTS.TransportS.leafEta) (a := 0) (b := 0) (Or.inl rfl) (by norm_num)
  have i3 := slot_bound hρ hK hST hα hε hfs hhs hmf hmh hab
    (w := Work.FTS.TransportS.leafOne) (a := 0) (b := 0) (Or.inr (Or.inl rfl)) (by norm_num)
  have i4 := slot_bound hρ hK hST hα hε hfs hhs hmf hmh hab
    (w := Work.FTS.TransportS.leafGam α) (a := 1) (b := 0)
    (Or.inr (Or.inr ⟨le_refl 1, rfl⟩)) (by norm_num)
  have hC : (0 : ℝ) ≤ K * ε * Work.Spaces.HkNorm α 4 f * (3 * Work.Spaces.HkNorm α 5 h) :=
    mul_nonneg (mul_nonneg (mul_nonneg hK hε.1.le) (Work.Spaces.HkNorm_nonneg α 4 f))
      (mul_nonneg (by norm_num) (Work.Spaces.HkNorm_nonneg α 5 h))
  -- the four slot bounds, in the form in which they occur in the decomposition
  have j1 : |Work.Coercivity.wip Work.FTS.TransportS.leafEta
        (Work.Spaces.Dz (Work.FTS.StrongEps.Jeps ρ ε (Work.Spaces.mixed b₀ a₀ f)))
        (Work.Spaces.Dz (Work.Spaces.mixed b₀ a₀ h))
      - Work.Coercivity.wip Work.FTS.TransportS.leafEta
        (Work.Spaces.Dz (Work.Spaces.mixed b₀ a₀ f))
        (Work.Spaces.Dz (Work.FTS.StrongEps.Jeps ρ ε (Work.Spaces.mixed b₀ a₀ h)))|
      ≤ K * ε * Work.Spaces.HkNorm α 4 f * (3 * Work.Spaces.HkNorm α 5 h) := by
    simpa only [Work.Spaces.mixed_zero_right, Work.Spaces.mixed_zero_left,
      Work.Spaces.DzIter_succ, Work.Spaces.DzIter_zero, Work.Spaces.DthIter_succ,
      Work.Spaces.DthIter_zero] using i1
  have j2 : |Work.Coercivity.wip Work.FTS.TransportS.leafEta
        (Work.FTS.StrongEps.Jeps ρ ε (Work.Spaces.mixed b₀ a₀ f))
        (Work.Spaces.mixed b₀ a₀ h)
      - Work.Coercivity.wip Work.FTS.TransportS.leafEta (Work.Spaces.mixed b₀ a₀ f)
        (Work.FTS.StrongEps.Jeps ρ ε (Work.Spaces.mixed b₀ a₀ h))|
      ≤ K * ε * Work.Spaces.HkNorm α 4 f * (3 * Work.Spaces.HkNorm α 5 h) := by
    simpa only [Work.Spaces.mixed_zero_right, Work.Spaces.mixed_zero_left,
      Work.Spaces.DzIter_succ, Work.Spaces.DzIter_zero, Work.Spaces.DthIter_succ,
      Work.Spaces.DthIter_zero] using i2
  have j3 : |Work.Coercivity.wip Work.FTS.TransportS.leafOne
        (Work.FTS.StrongEps.Jeps ρ ε (Work.Spaces.mixed b₀ a₀ f))
        (Work.Spaces.mixed b₀ a₀ h)
      - Work.Coercivity.wip Work.FTS.TransportS.leafOne (Work.Spaces.mixed b₀ a₀ f)
        (Work.FTS.StrongEps.Jeps ρ ε (Work.Spaces.mixed b₀ a₀ h))|
      ≤ K * ε * Work.Spaces.HkNorm α 4 f * (3 * Work.Spaces.HkNorm α 5 h) := by
    simpa only [Work.Spaces.mixed_zero_right, Work.Spaces.mixed_zero_left,
      Work.Spaces.DzIter_succ, Work.Spaces.DzIter_zero, Work.Spaces.DthIter_succ,
      Work.Spaces.DthIter_zero] using i3
  have j4 : |Work.Coercivity.wip (Work.FTS.TransportS.leafGam α)
        (Work.Spaces.Dth (Work.FTS.StrongEps.Jeps ρ ε (Work.Spaces.mixed b₀ a₀ f)))
        (Work.Spaces.Dth (Work.Spaces.mixed b₀ a₀ h))
      - Work.Coercivity.wip (Work.FTS.TransportS.leafGam α)
        (Work.Spaces.Dth (Work.Spaces.mixed b₀ a₀ f))
        (Work.Spaces.Dth (Work.FTS.StrongEps.Jeps ρ ε (Work.Spaces.mixed b₀ a₀ h)))|
      ≤ K * ε * Work.Spaces.HkNorm α 4 f * (3 * Work.Spaces.HkNorm α 5 h) := by
    simpa only [Work.Spaces.mixed_zero_right, Work.Spaces.mixed_zero_left,
      Work.Spaces.DzIter_succ, Work.Spaces.DzIter_zero, Work.Spaces.DthIter_succ,
      Work.Spaces.DthIter_zero] using i4
  rw [hdecomp]
  refine (abs_sum_four_le _ _ _ _).trans ?_
  rw [abs_mul, abs_mul, abs_mul, abs_mul]
  norm_num
  have e : (10 + 10 ^ 10 + 10 ^ 17 + 10 ^ 21)
        * (K * ε * Work.Spaces.HkNorm α 4 f * (3 * Work.Spaces.HkNorm α 5 h))
      = 3 * (10 + 10 ^ 10 + 10 ^ 17 + 10 ^ 21) * K * ε
          * Work.Spaces.HkNorm α 4 f * Work.Spaces.HkNorm α 5 h := by ring
  linarith [e, j1, j2, j3, j4]

end Work.FTS.StrongEps.E4R3.Apriori4Proofs.TransferDeriv
end
-- ===== merged: Submission.Work.FTS.StrongEps.E4R3.Apriori4Proofs.TransferDeriv.PairingTransferDeriv =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `PairingTransferDeriv` — the derivative-priced transfer estimate at the level of the pairing

`pairing_transfer_deriv` is the log-coordinate transfer estimate for a weight `w` whose log
pull-back is log-Lipschitz, with the derivative price on the second argument: the analytic
content (the convolution on the log plane) is the hypothesis `PlaneTransferDeriv`, and the work
here is the two log-coordinate substitutions which turn the quadrant pairings into their plane
counterparts.
-/

noncomputable section
open scoped Real Topology ENNReal
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.E4R3.Apriori4Proofs.TransferDeriv

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false

/-- **The derivative-priced transfer estimate in the quadrant form.** -/
theorem pairing_transfer_deriv {ρ : ℝ × ℝ → ℝ} (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ)
    (hLT : PlaneTransferDeriv)
    {w : ℝ → ℝ → ℝ} {Cw : ℝ} (hCw : 0 ≤ Cw)
    (hw0 : ∀ y : ℝ × ℝ, 0 ≤ Work.FTS.StrongEps.E4R3.Apriori4Proofs.logW w y)
    (hwm : Measurable (Work.FTS.StrongEps.E4R3.Apriori4Proofs.logW w))
    (hwsh : ∀ y p : ℝ × ℝ, Work.FTS.StrongEps.E4R3.Apriori4Proofs.logW w (y + p)
      ≤ Real.exp (Cw * (|p.1| + |p.2|)) * Work.FTS.StrongEps.E4R3.Apriori4Proofs.logW w y)
    (hwsh' : ∀ y p : ℝ × ℝ, Work.FTS.StrongEps.E4R3.Apriori4Proofs.logW w y
      ≤ Real.exp (Cw * (|p.1| + |p.2|)) * Work.FTS.StrongEps.E4R3.Apriori4Proofs.logW w (y + p))
    {ε : ℝ} (hε : ε ∈ Set.Ioc (0 : ℝ) 1)
    {g₁ g₂ : Fn} (hs1 : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry g₁)
        Work.FTS.EllipticEst.Q0)
    (hs2 : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry g₂) Work.FTS.EllipticEst.Q0)
    (hC2 : ContDiff ℝ 1 (Work.FTS.StrongEps.E4R3.Apriori4Proofs.logPull g₂))
    (hJ1 : MeasureTheory.Integrable (Function.uncurry (fun z θ => w z θ
        * Work.FTS.StrongEps.Jeps ρ ε g₁ z θ * g₂ z θ))
      (MeasureTheory.volume.restrict Work.FTS.StrongEps.Quad))
    (hJ2 : MeasureTheory.Integrable (Function.uncurry (fun z θ => w z θ
        * g₁ z θ * Work.FTS.StrongEps.Jeps ρ ε g₂ z θ))
      (MeasureTheory.volume.restrict Work.FTS.StrongEps.Quad))
    (hX1 : MeasureTheory.Integrable (fun y : ℝ × ℝ
        => Work.FTS.StrongEps.E4R3.Apriori4Proofs.logW w y
          * (∫ p : ℝ × ℝ, Work.FTS.StrongEps.Jker ρ ε p
              * Work.FTS.StrongEps.E4R3.Apriori4Proofs.logPull g₁ (y - p))
          * Work.FTS.StrongEps.E4R3.Apriori4Proofs.logPull g₂ y))
    (hX2 : MeasureTheory.Integrable (fun y : ℝ × ℝ
        => Work.FTS.StrongEps.E4R3.Apriori4Proofs.logW w y
          * Work.FTS.StrongEps.E4R3.Apriori4Proofs.logPull g₁ y
          * (∫ p : ℝ × ℝ, Work.FTS.StrongEps.Jker ρ ε p
              * Work.FTS.StrongEps.E4R3.Apriori4Proofs.logPull g₂ (y - p))))
    (hG1 : MeasureTheory.Integrable (Function.uncurry (fun z θ => w z θ * g₁ z θ ^ 2))
      (MeasureTheory.volume.restrict Work.FTS.StrongEps.Quad))
    (hG2 : MeasureTheory.Integrable (Function.uncurry (fun z θ => w z θ * g₂ z θ ^ 2))
      (MeasureTheory.volume.restrict Work.FTS.StrongEps.Quad))
    (hI1 : MeasureTheory.Integrable (fun y : ℝ × ℝ
      => Work.FTS.StrongEps.E4R3.Apriori4Proofs.logW w y
          * (Work.FTS.StrongEps.E4R3.Apriori4Proofs.logPull g₁ y) ^ 2))
    (hI2 : MeasureTheory.Integrable (fun y : ℝ × ℝ
      => Work.FTS.StrongEps.E4R3.Apriori4Proofs.logW w y
          * (Work.FTS.StrongEps.E4R3.Apriori4Proofs.logPull g₂ y) ^ 2))
    (hF2 : MeasureTheory.Integrable (fun y : ℝ × ℝ
      => Work.FTS.StrongEps.E4R3.Apriori4Proofs.logW w y
          * ‖fderiv ℝ (Work.FTS.StrongEps.E4R3.Apriori4Proofs.logPull g₂) y‖ ^ 2)) :
    |(∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, w z θ
        * Work.FTS.StrongEps.Jeps ρ ε g₁ z θ * g₂ z θ)
      - (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, w z θ
          * g₁ z θ * Work.FTS.StrongEps.Jeps ρ ε g₂ z θ)|
      ≤ 100 * (Cw + 1) * Real.exp (4 * Cw) * ε
          * Real.sqrt (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, w z θ * g₁ z θ ^ 2)
          * (Real.sqrt (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, w z θ * g₂ z θ ^ 2)
            + Real.sqrt (∫ y : ℝ × ℝ, Work.FTS.StrongEps.E4R3.Apriori4Proofs.logW w y
                * ‖fderiv ℝ (Work.FTS.StrongEps.E4R3.Apriori4Proofs.logPull g₂) y‖ ^ 2)) := by
  have hε0 : 0 < ε := hε.1
  have hε1 : ε ≤ 1 := hε.2
  have hc1 : Continuous (Work.FTS.StrongEps.E4R3.Apriori4Proofs.logPull g₁) :=
    Work.FTS.StrongEps.E4R3.Apriori4Proofs.JepsTransfer.logPull_continuous hs1
  have hc2 : Continuous (Work.FTS.StrongEps.E4R3.Apriori4Proofs.logPull g₂) :=
    Work.FTS.StrongEps.E4R3.Apriori4Proofs.JepsTransfer.logPull_continuous hs2
  have hkabs : (∫ p : ℝ × ℝ, |Work.FTS.StrongEps.Jker ρ ε p|) ≤ 1 := by
    have h1 : (∫ p : ℝ × ℝ, |Work.FTS.StrongEps.Jker ρ ε p|) = 1 := by
      rw [show (fun p : ℝ × ℝ => |Work.FTS.StrongEps.Jker ρ ε p|) = Work.FTS.StrongEps.Jker ρ ε
        from funext (fun p => abs_of_nonneg (Work.FTS.StrongEps.HkSqAux.Jker_nonneg ρ hρ.moll ε p))]
      exact Work.FTS.StrongEps.Jker_integral_eq_one ρ hρ.moll hε0
    rw [h1]
  have hT := hLT hε0 hε1 hCw (Work.FTS.StrongEps.Jker_continuous hρ.moll ε).measurable
    (Work.FTS.StrongEps.Jker_integrable hρ.moll hε0) hkabs
    (fun p hp => Work.FTS.StrongEps.HkSqAux.Jker_support_abs hρ.moll hε0 hp)
    hw0 hwm hwsh hwsh' hc1.measurable hc2.measurable hC2
    (fun y => Work.FTS.StrongEps.E4R3.Apriori4Proofs.JepsTransfer.jker_conv_integrable
      hρ.moll hε0 hc1 y)
    (fun y => Work.FTS.StrongEps.E4R3.Apriori4Proofs.JepsTransfer.jker_conv_integrable
      hρ.moll hε0 hc2 y)
    hI1 hI2 hF2
  have hm1 : (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, w z θ
        * Work.FTS.StrongEps.Jeps ρ ε g₁ z θ * g₂ z θ)
      = ∫ y : ℝ × ℝ, Work.FTS.StrongEps.E4R3.Apriori4Proofs.logW w y
          * (∫ p : ℝ × ℝ, Work.FTS.StrongEps.Jker ρ ε p
              * Work.FTS.StrongEps.E4R3.Apriori4Proofs.logPull g₁ (y - p))
          * Work.FTS.StrongEps.E4R3.Apriori4Proofs.logPull g₂ y := by
    rw [Work.FTS.CoercivityStep.Base.wip_eq_Ioi_Ioo,
      Work.FTS.StrongEps.E4R3.Apriori4Proofs.JepsTransfer.integral_quad_log_subst hJ1]
    have hprod : (∫ y : ℝ × ℝ, Work.FTS.StrongEps.E4R3.Apriori4Proofs.logW w y
          * (∫ p : ℝ × ℝ, Work.FTS.StrongEps.Jker ρ ε p
              * Work.FTS.StrongEps.E4R3.Apriori4Proofs.logPull g₁ (y - p))
          * Work.FTS.StrongEps.E4R3.Apriori4Proofs.logPull g₂ y)
        = ∫ s, ∫ ζ, Work.FTS.StrongEps.E4R3.Apriori4Proofs.logW w (s, ζ)
          * (∫ p : ℝ × ℝ, Work.FTS.StrongEps.Jker ρ ε p
              * Work.FTS.StrongEps.E4R3.Apriori4Proofs.logPull g₁ ((s, ζ) - p))
          * Work.FTS.StrongEps.E4R3.Apriori4Proofs.logPull g₂ (s, ζ) :=
      MeasureTheory.integral_prod (fun y : ℝ × ℝ => Work.FTS.StrongEps.E4R3.Apriori4Proofs.logW w y
          * (∫ p : ℝ × ℝ, Work.FTS.StrongEps.Jker ρ ε p
              * Work.FTS.StrongEps.E4R3.Apriori4Proofs.logPull g₁ (y - p))
          * Work.FTS.StrongEps.E4R3.Apriori4Proofs.logPull g₂ y) hX1
    rw [hprod]
    refine MeasureTheory.integral_congr_ae (Eventually.of_forall (fun s => ?_))
    refine MeasureTheory.integral_congr_ae (Eventually.of_forall (fun ζ => ?_))
    show Work.FTS.StrongEps.HkSqAux.logJac s ζ
        * (w (Real.exp s) (Real.arctan (Real.exp ζ))
            * Work.FTS.StrongEps.Jeps ρ ε g₁ (Real.exp s) (Real.arctan (Real.exp ζ))
            * g₂ (Real.exp s) (Real.arctan (Real.exp ζ)))
      = (Work.FTS.StrongEps.E4R3.Apriori4Proofs.logW w (s, ζ)
          * (∫ p : ℝ × ℝ, Work.FTS.StrongEps.Jker ρ ε p
              * Work.FTS.StrongEps.E4R3.Apriori4Proofs.logPull g₁ ((s, ζ) - p)))
          * Work.FTS.StrongEps.E4R3.Apriori4Proofs.logPull g₂ (s, ζ)
    have hJ : Work.FTS.StrongEps.Jeps ρ ε g₁ (Real.exp s) (Real.arctan (Real.exp ζ))
        = ∫ p : ℝ × ℝ, Work.FTS.StrongEps.Jker ρ ε p
            * Work.FTS.StrongEps.E4R3.Apriori4Proofs.logPull g₁ ((s, ζ) - p) :=
      Work.FTS.StrongEps.E4R3.Apriori4Proofs.JT.logPull_Jeps_apply ρ ε g₁ (s, ζ)
    rw [hJ, Work.FTS.StrongEps.E4R3.Apriori4Proofs.logPull_apply,
      Work.FTS.StrongEps.E4R3.Apriori4Proofs.logW_apply]
    ring
  have hm2 : (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, w z θ
        * g₁ z θ * Work.FTS.StrongEps.Jeps ρ ε g₂ z θ)
      = ∫ y : ℝ × ℝ, Work.FTS.StrongEps.E4R3.Apriori4Proofs.logW w y
          * Work.FTS.StrongEps.E4R3.Apriori4Proofs.logPull g₁ y
          * (∫ p : ℝ × ℝ, Work.FTS.StrongEps.Jker ρ ε p
              * Work.FTS.StrongEps.E4R3.Apriori4Proofs.logPull g₂ (y - p)) := by
    rw [Work.FTS.CoercivityStep.Base.wip_eq_Ioi_Ioo,
      Work.FTS.StrongEps.E4R3.Apriori4Proofs.JepsTransfer.integral_quad_log_subst hJ2]
    have hprod : (∫ y : ℝ × ℝ, Work.FTS.StrongEps.E4R3.Apriori4Proofs.logW w y
          * Work.FTS.StrongEps.E4R3.Apriori4Proofs.logPull g₁ y
          * (∫ p : ℝ × ℝ, Work.FTS.StrongEps.Jker ρ ε p
              * Work.FTS.StrongEps.E4R3.Apriori4Proofs.logPull g₂ (y - p)))
        = ∫ s, ∫ ζ, Work.FTS.StrongEps.E4R3.Apriori4Proofs.logW w (s, ζ)
          * Work.FTS.StrongEps.E4R3.Apriori4Proofs.logPull g₁ (s, ζ)
          * (∫ p : ℝ × ℝ, Work.FTS.StrongEps.Jker ρ ε p
              * Work.FTS.StrongEps.E4R3.Apriori4Proofs.logPull g₂ ((s, ζ) - p)) :=
      MeasureTheory.integral_prod (fun y : ℝ × ℝ => Work.FTS.StrongEps.E4R3.Apriori4Proofs.logW w y
          * Work.FTS.StrongEps.E4R3.Apriori4Proofs.logPull g₁ y
          * (∫ p : ℝ × ℝ, Work.FTS.StrongEps.Jker ρ ε p
              * Work.FTS.StrongEps.E4R3.Apriori4Proofs.logPull g₂ (y - p))) hX2
    rw [hprod]
    refine MeasureTheory.integral_congr_ae (Eventually.of_forall (fun s => ?_))
    refine MeasureTheory.integral_congr_ae (Eventually.of_forall (fun ζ => ?_))
    show Work.FTS.StrongEps.HkSqAux.logJac s ζ
        * (w (Real.exp s) (Real.arctan (Real.exp ζ))
            * g₁ (Real.exp s) (Real.arctan (Real.exp ζ))
            * Work.FTS.StrongEps.Jeps ρ ε g₂ (Real.exp s) (Real.arctan (Real.exp ζ)))
      = (Work.FTS.StrongEps.E4R3.Apriori4Proofs.logW w (s, ζ)
          * Work.FTS.StrongEps.E4R3.Apriori4Proofs.logPull g₁ (s, ζ))
          * (∫ p : ℝ × ℝ, Work.FTS.StrongEps.Jker ρ ε p
              * Work.FTS.StrongEps.E4R3.Apriori4Proofs.logPull g₂ ((s, ζ) - p))
    have hJ : Work.FTS.StrongEps.Jeps ρ ε g₂ (Real.exp s) (Real.arctan (Real.exp ζ))
        = ∫ p : ℝ × ℝ, Work.FTS.StrongEps.Jker ρ ε p
            * Work.FTS.StrongEps.E4R3.Apriori4Proofs.logPull g₂ ((s, ζ) - p) :=
      Work.FTS.StrongEps.E4R3.Apriori4Proofs.JT.logPull_Jeps_apply ρ ε g₂ (s, ζ)
    rw [hJ, Work.FTS.StrongEps.E4R3.Apriori4Proofs.logPull_apply,
      Work.FTS.StrongEps.E4R3.Apriori4Proofs.logW_apply]
    ring
  have hq1 : (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, w z θ * g₁ z θ ^ 2)
      = ∫ y : ℝ × ℝ, Work.FTS.StrongEps.E4R3.Apriori4Proofs.logW w y
          * (Work.FTS.StrongEps.E4R3.Apriori4Proofs.logPull g₁ y) ^ 2 := by
    rw [Work.FTS.CoercivityStep.Base.wip_eq_Ioi_Ioo,
      Work.FTS.StrongEps.E4R3.Apriori4Proofs.JepsTransfer.integral_quad_log_subst hG1]
    have hprod : (∫ y : ℝ × ℝ, Work.FTS.StrongEps.E4R3.Apriori4Proofs.logW w y
          * (Work.FTS.StrongEps.E4R3.Apriori4Proofs.logPull g₁ y) ^ 2)
        = ∫ s, ∫ ζ, Work.FTS.StrongEps.E4R3.Apriori4Proofs.logW w (s, ζ)
          * (Work.FTS.StrongEps.E4R3.Apriori4Proofs.logPull g₁ (s, ζ)) ^ 2 :=
      MeasureTheory.integral_prod (fun y : ℝ × ℝ => Work.FTS.StrongEps.E4R3.Apriori4Proofs.logW w y
          * (Work.FTS.StrongEps.E4R3.Apriori4Proofs.logPull g₁ y) ^ 2) hI1
    rw [hprod]
    refine MeasureTheory.integral_congr_ae (Eventually.of_forall (fun s => ?_))
    refine MeasureTheory.integral_congr_ae (Eventually.of_forall (fun ζ => ?_))
    simp only [Work.FTS.StrongEps.E4R3.Apriori4Proofs.logW_apply,
      Work.FTS.StrongEps.E4R3.Apriori4Proofs.logPull_apply]
    ring
  have hq2 : (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, w z θ * g₂ z θ ^ 2)
      = ∫ y : ℝ × ℝ, Work.FTS.StrongEps.E4R3.Apriori4Proofs.logW w y
          * (Work.FTS.StrongEps.E4R3.Apriori4Proofs.logPull g₂ y) ^ 2 := by
    rw [Work.FTS.CoercivityStep.Base.wip_eq_Ioi_Ioo,
      Work.FTS.StrongEps.E4R3.Apriori4Proofs.JepsTransfer.integral_quad_log_subst hG2]
    have hprod : (∫ y : ℝ × ℝ, Work.FTS.StrongEps.E4R3.Apriori4Proofs.logW w y
          * (Work.FTS.StrongEps.E4R3.Apriori4Proofs.logPull g₂ y) ^ 2)
        = ∫ s, ∫ ζ, Work.FTS.StrongEps.E4R3.Apriori4Proofs.logW w (s, ζ)
          * (Work.FTS.StrongEps.E4R3.Apriori4Proofs.logPull g₂ (s, ζ)) ^ 2 :=
      MeasureTheory.integral_prod (fun y : ℝ × ℝ => Work.FTS.StrongEps.E4R3.Apriori4Proofs.logW w y
          * (Work.FTS.StrongEps.E4R3.Apriori4Proofs.logPull g₂ y) ^ 2) hI2
    rw [hprod]
    refine MeasureTheory.integral_congr_ae (Eventually.of_forall (fun s => ?_))
    refine MeasureTheory.integral_congr_ae (Eventually.of_forall (fun ζ => ?_))
    simp only [Work.FTS.StrongEps.E4R3.Apriori4Proofs.logW_apply,
      Work.FTS.StrongEps.E4R3.Apriori4Proofs.logPull_apply]
    ring
  rw [hm1, hm2, hq1, hq2]
  exact hT

end Work.FTS.StrongEps.E4R3.Apriori4Proofs.TransferDeriv
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.E4R3.Apriori4Proofs.TransferDeriv.TransferAux =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `TransferAux` — elementary helpers for the derivative-priced slot transfer

Three reusable facts:

* `sqrt_add_le_aux` — `√(a+b) ≤ √a + √b` for `a, b ≥ 0` (not in Mathlib);
* `quad_lint_ne_top` — the iterated `∫⁻` over `Iz × Iθ` of `ofReal F` is finite as soon as `F` is
  integrable on the whole plane;
* `integrable_cross_of_diag` — AM–GM: `w·A·B` is integrable as soon as `w·A²` and `w·B²` are and
  `w ≥ 0` a.e.;
* `wip_self_nonneg` — the diagonal `wip` of a leaf weight is nonnegative;
* `contDiff_one_logPull_of_forall` — `logPull g` is `C¹` when `g` is smooth on the open quadrant.
-/

noncomputable section
open scoped Real Topology ENNReal ContDiff
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.E4R3.Apriori4Proofs.TransferDeriv

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false

/-- `√(a+b) ≤ √a + √b`. -/
theorem sqrt_add_le_aux {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Real.sqrt (a + b) ≤ Real.sqrt a + Real.sqrt b := by
  have h1 : (Real.sqrt (a + b)) ^ 2 ≤ (Real.sqrt a + Real.sqrt b) ^ 2 := by
    rw [Real.sq_sqrt (by linarith : (0:ℝ) ≤ a + b), add_sq, Real.sq_sqrt ha, Real.sq_sqrt hb]
    nlinarith [Real.sqrt_nonneg a, Real.sqrt_nonneg b]
  nlinarith [h1, Real.sqrt_nonneg (a + b), Real.sqrt_nonneg a, Real.sqrt_nonneg b]

/-- The iterated `∫⁻` over `Iz × Iθ` of `ofReal F` is finite as soon as `F` is integrable on the
whole plane. -/
theorem quad_lint_ne_top {F : ℝ → ℝ → ℝ}
    (hF : MeasureTheory.Integrable (Function.uncurry F) MeasureTheory.volume) :
    (∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal (F z θ)) ≠ ⊤ := by
  refine ne_of_lt ?_
  have h_inner : ∀ z : ℝ,
      (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal (F z θ)) ≤ ∫⁻ θ, ENNReal.ofReal |F z θ| :=
    fun z => ((MeasureTheory.lintegral_mono
        (fun θ => ENNReal.ofReal_le_ofReal (le_abs_self _))).trans
      (MeasureTheory.lintegral_mono_set (Set.subset_univ Work.Spaces.Iθ))).trans
      (le_of_eq (MeasureTheory.setLIntegral_univ (fun θ => ENNReal.ofReal |F z θ|)))
  have hAEM : AEMeasurable (fun q : ℝ × ℝ => ENNReal.ofReal |F q.1 q.2|)
      (MeasureTheory.volume.prod MeasureTheory.volume) :=
    ENNReal.measurable_ofReal.comp_aemeasurable hF.aestronglyMeasurable.aemeasurable.norm
  calc (∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal (F z θ))
      ≤ ∫⁻ z, ∫⁻ θ, ENNReal.ofReal |F z θ| :=
        ((MeasureTheory.lintegral_mono h_inner).trans
          (MeasureTheory.lintegral_mono_set (Set.subset_univ Work.Spaces.Iz))).trans
          (le_of_eq (MeasureTheory.setLIntegral_univ
            (fun z => ∫⁻ θ, ENNReal.ofReal |F z θ|)))
    _ = ∫⁻ q : ℝ × ℝ, ENNReal.ofReal |F q.1 q.2| :=
        (MeasureTheory.lintegral_prod (fun q : ℝ × ℝ => ENNReal.ofReal |F q.1 q.2|) hAEM).symm
    _ = ENNReal.ofReal (∫ q : ℝ × ℝ, |F q.1 q.2|) :=
        (MeasureTheory.ofReal_integral_eq_lintegral_ofReal hF.abs
          (Eventually.of_forall (fun q => abs_nonneg _))).symm
    _ < ⊤ := ENNReal.ofReal_lt_top

/-- AM–GM for the diagonal data: `w·A·B` is integrable once `w ≥ 0` a.e., `w·A²` and `w·B²` are,
and the product is a.e. strongly measurable. -/
theorem integrable_cross_of_diag {w A B : ℝ → ℝ → ℝ} {μ : MeasureTheory.Measure (ℝ × ℝ)}
    (hw : ∀ᵐ q ∂μ, 0 ≤ w q.1 q.2)
    (hf : AEStronglyMeasurable (fun q : ℝ × ℝ => w q.1 q.2 * A q.1 q.2 * B q.1 q.2) μ)
    (hA : MeasureTheory.Integrable (fun q : ℝ × ℝ => w q.1 q.2 * (A q.1 q.2) ^ 2) μ)
    (hB : MeasureTheory.Integrable (fun q : ℝ × ℝ => w q.1 q.2 * (B q.1 q.2) ^ 2) μ) :
    MeasureTheory.Integrable (fun q : ℝ × ℝ => w q.1 q.2 * A q.1 q.2 * B q.1 q.2) μ := by
  have hmaj : MeasureTheory.Integrable
      (fun q : ℝ × ℝ => (w q.1 q.2 * (A q.1 q.2) ^ 2 + w q.1 q.2 * (B q.1 q.2) ^ 2) / 2) μ :=
    ((hA.add hB).const_mul (1 / 2)).congr (Eventually.of_forall (fun q => by
      show (1 / 2) * (w q.1 q.2 * A q.1 q.2 ^ 2 + w q.1 q.2 * B q.1 q.2 ^ 2)
          = (w q.1 q.2 * A q.1 q.2 ^ 2 + w q.1 q.2 * B q.1 q.2 ^ 2) / 2
      ring))
  refine MeasureTheory.Integrable.mono' hmaj hf ?_
  filter_upwards [hw] with q hq
  show |w q.1 q.2 * A q.1 q.2 * B q.1 q.2|
      ≤ (w q.1 q.2 * A q.1 q.2 ^ 2 + w q.1 q.2 * B q.1 q.2 ^ 2) / 2
  rw [abs_mul, abs_mul, abs_of_nonneg hq]
  have h5 : |A q.1 q.2| * |B q.1 q.2| ≤ ((A q.1 q.2) ^ 2 + (B q.1 q.2) ^ 2) / 2 := by
    nlinarith [sq_nonneg (A q.1 q.2 - B q.1 q.2), sq_nonneg (A q.1 q.2 + B q.1 q.2),
      abs_nonneg (A q.1 q.2), abs_nonneg (B q.1 q.2), sq_abs (A q.1 q.2), sq_abs (B q.1 q.2)]
  calc w q.1 q.2 * |A q.1 q.2| * |B q.1 q.2|
      = w q.1 q.2 * (|A q.1 q.2| * |B q.1 q.2|) := by ring
    _ ≤ w q.1 q.2 * (((A q.1 q.2) ^ 2 + (B q.1 q.2) ^ 2) / 2) :=
        mul_le_mul_of_nonneg_left h5 hq
    _ = (w q.1 q.2 * (A q.1 q.2) ^ 2 + w q.1 q.2 * (B q.1 q.2) ^ 2) / 2 := by ring

/-- The diagonal `wip` of a leaf weight is nonnegative. -/
theorem wip_self_nonneg {α : ℝ} {a : ℕ} {w : ℝ → ℝ → ℝ}
    (hleaf : Work.FTS.TransportS.IsLeafW α a w) (A : ℝ → ℝ → ℝ) :
    0 ≤ Work.Coercivity.wip w A A := by
  have hleafnn : ∀ z : ℝ, ∀ θ ∈ Work.Spaces.Iθ, 0 ≤ w z θ := fun z θ hθ =>
    Work.FTS.StrongPersist.H6Pair6Aux.leaf_nonneg hleaf z hθ
  rw [Work.FTS.StrongEps.E4R3.Apriori4Proofs.JT.wip_eq_flat]
  refine MeasureTheory.setIntegral_nonneg isClosed_Ici.measurableSet (fun z _ => ?_)
  refine MeasureTheory.setIntegral_nonneg isClosed_Icc.measurableSet (fun θ hθ => ?_)
  have hwθ : (0 : ℝ) ≤ w z θ := hleafnn z θ hθ
  nlinarith [sq_nonneg (A z θ)]

/-- `logPull g` is `C¹` when `g` is `C^∞` on the open quadrant. -/
theorem contDiff_one_logPull_of_forall {g : Fn}
    (hg : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry g) Work.FTS.EllipticEst.Q0) :
    ContDiff ℝ 1 (Work.FTS.StrongEps.E4R3.Apriori4Proofs.logPull g) := by
  have hφ : ContDiff ℝ 1 (fun s : ℝ × ℝ => (Real.exp s.1, Real.arctan (Real.exp s.2))) :=
    (Real.contDiff_exp.comp contDiff_fst).prodMk
      (Real.contDiff_arctan.comp (Real.contDiff_exp.comp contDiff_snd))
  have hmem : ∀ s : ℝ × ℝ, (Real.exp s.1, Real.arctan (Real.exp s.2))
      ∈ Work.FTS.EllipticEst.Q0 := fun s =>
    Work.FTS.EllipticEst.mem_Q0.mpr ⟨Real.exp_pos _, Real.arctan_pos.mpr (Real.exp_pos s.2),
      Real.arctan_lt_pi_div_two _⟩
  have h := (hg 1).comp_contDiff hφ hmem
  have hfun : ((Function.uncurry g)
      ∘ (fun s : ℝ × ℝ => (Real.exp s.1, Real.arctan (Real.exp s.2))))
      = Work.FTS.StrongEps.E4R3.Apriori4Proofs.logPull g := rfl
  rwa [hfun] at h

end Work.FTS.StrongEps.E4R3.Apriori4Proofs.TransferDeriv
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.E4R3.Apriori4Proofs.TransferDeriv.logW_fderiv_integral_le =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.E4R3.Apriori4Proofs.TransferDeriv

open MeasureTheory Set Filter

theorem logW_fderiv_integral_le {w : ℝ → ℝ → ℝ} {g : Work.FTS.Galerkin.Fn}
    (hw0 : ∀ y : ℝ × ℝ, 0 ≤ Work.FTS.StrongEps.E4R3.Apriori4Proofs.logW w y)
    (hwm : Measurable (Work.FTS.StrongEps.E4R3.Apriori4Proofs.logW w))
    (hg : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry g) Work.FTS.EllipticEst.Q0)
    (hz : MeasureTheory.Integrable (Function.uncurry (fun z θ => w z θ * (Work.Spaces.Dz g z θ) ^ 2))
            (MeasureTheory.volume.restrict Work.FTS.StrongEps.Quad))
    (hth : MeasureTheory.Integrable (Function.uncurry (fun z θ => w z θ * (Work.Spaces.Dth g z θ) ^ 2))
            (MeasureTheory.volume.restrict Work.FTS.StrongEps.Quad)) :
    MeasureTheory.Integrable (fun y : ℝ × ℝ => Work.FTS.StrongEps.E4R3.Apriori4Proofs.logW w y
        * ‖fderiv ℝ (Work.FTS.StrongEps.E4R3.Apriori4Proofs.logPull g) y‖ ^ 2)
      ∧ (∫ y : ℝ × ℝ, Work.FTS.StrongEps.E4R3.Apriori4Proofs.logW w y
            * ‖fderiv ℝ (Work.FTS.StrongEps.E4R3.Apriori4Proofs.logPull g) y‖ ^ 2)
          ≤ 2 * Work.Coercivity.wip w (Work.Spaces.Dz g) (Work.Spaces.Dz g)
            + Work.Coercivity.wip w (Work.Spaces.Dth g) (Work.Spaces.Dth g) := by
  -- The fderiv of the pulled-back profile is continuous (it is `C^1`), hence its norm is
  -- a.e.-measurable; this is what makes the two log-side slot functions measurable.
  have hcontfd : Continuous
      (fderiv ℝ (Work.FTS.StrongEps.E4R3.Apriori4Proofs.logPull g)) :=
    (Work.FTS.StrongEps.E4R3.Apriori4Proofs.TransferDeriv.LogPullFacts.contDiff_logPull hg 1)
      |>.continuous_fderiv (by norm_num)
  -- Measurability of the log pull-back of the two slots, from the slot identities.
  have hFmDz : AEMeasurable (Work.FTS.StrongEps.E4R3.Apriori4Proofs.logPull (Work.Spaces.Dz g))
      MeasureTheory.volume := by
    have heq : Work.FTS.StrongEps.E4R3.Apriori4Proofs.logPull (Work.Spaces.Dz g)
        = fun y : ℝ × ℝ => fderiv ℝ (Work.FTS.StrongEps.E4R3.Apriori4Proofs.logPull g) y
            (ContinuousLinearMap.inl ℝ ℝ ℝ (1 : ℝ)) := by
      funext y
      exact (Work.FTS.StrongEps.E4R3.Apriori4Proofs.TransferDeriv.LogPullFacts.fderiv_logPull_slots
        hg y).1.symm
    rw [heq]
    exact (hcontfd.clm_apply continuous_const).aemeasurable
  have hFmDth : AEMeasurable (Work.FTS.StrongEps.E4R3.Apriori4Proofs.logPull (Work.Spaces.Dth g))
      MeasureTheory.volume := by
    have heq : Work.FTS.StrongEps.E4R3.Apriori4Proofs.logPull (Work.Spaces.Dth g)
        = fun y : ℝ × ℝ => 2 * (fderiv ℝ (Work.FTS.StrongEps.E4R3.Apriori4Proofs.logPull g) y
            (ContinuousLinearMap.inr ℝ ℝ ℝ (1 : ℝ))) := by
      funext y
      rw [(Work.FTS.StrongEps.E4R3.Apriori4Proofs.TransferDeriv.LogPullFacts.fderiv_logPull_slots
        hg y).2]
      simp only [Work.FTS.StrongEps.E4R3.Apriori4Proofs.logPull]
      ring
    rw [heq]
    exact (continuous_const.mul (hcontfd.clm_apply continuous_const)).aemeasurable
  -- The two building blocks: log-side integrability and the value of the plane integrals.
  have hA : Integrable (fun y : ℝ × ℝ => Work.FTS.StrongEps.E4R3.Apriori4Proofs.logW w y
      * (Work.FTS.StrongEps.E4R3.Apriori4Proofs.logPull (Work.Spaces.Dz g) y) ^ 2) :=
    (Work.FTS.StrongEps.E4R3.Apriori4Proofs.TransferDeriv.LogWeightInt.logW_mul_sq_facts
      hw0 hwm hFmDz hz).1
  have hAval : (∫ y : ℝ × ℝ, Work.FTS.StrongEps.E4R3.Apriori4Proofs.logW w y
      * (Work.FTS.StrongEps.E4R3.Apriori4Proofs.logPull (Work.Spaces.Dz g) y) ^ 2)
      = Work.Coercivity.wip w (Work.Spaces.Dz g) (Work.Spaces.Dz g) :=
    (Work.FTS.StrongEps.E4R3.Apriori4Proofs.TransferDeriv.LogWeightInt.logW_mul_sq_facts
      hw0 hwm hFmDz hz).2
  have hB : Integrable (fun y : ℝ × ℝ => Work.FTS.StrongEps.E4R3.Apriori4Proofs.logW w y
      * (Work.FTS.StrongEps.E4R3.Apriori4Proofs.logPull (Work.Spaces.Dth g) y) ^ 2) :=
    (Work.FTS.StrongEps.E4R3.Apriori4Proofs.TransferDeriv.LogWeightInt.logW_mul_sq_facts
      hw0 hwm hFmDth hth).1
  have hBval : (∫ y : ℝ × ℝ, Work.FTS.StrongEps.E4R3.Apriori4Proofs.logW w y
      * (Work.FTS.StrongEps.E4R3.Apriori4Proofs.logPull (Work.Spaces.Dth g) y) ^ 2)
      = Work.Coercivity.wip w (Work.Spaces.Dth g) (Work.Spaces.Dth g) :=
    (Work.FTS.StrongEps.E4R3.Apriori4Proofs.TransferDeriv.LogWeightInt.logW_mul_sq_facts
      hw0 hwm hFmDth hth).2
  have hdom : Integrable (fun y : ℝ × ℝ => 2 * (Work.FTS.StrongEps.E4R3.Apriori4Proofs.logW w y
        * (Work.FTS.StrongEps.E4R3.Apriori4Proofs.logPull (Work.Spaces.Dz g) y) ^ 2)
      + Work.FTS.StrongEps.E4R3.Apriori4Proofs.logW w y
        * (Work.FTS.StrongEps.E4R3.Apriori4Proofs.logPull (Work.Spaces.Dth g) y) ^ 2) :=
    (hA.const_mul 2).add hB
  -- The pointwise domination of the integrand by `2 logW (D_z g)² + logW (D_θ g)²`.
  have hle : ∀ y : ℝ × ℝ, Work.FTS.StrongEps.E4R3.Apriori4Proofs.logW w y
        * ‖fderiv ℝ (Work.FTS.StrongEps.E4R3.Apriori4Proofs.logPull g) y‖ ^ 2
      ≤ 2 * (Work.FTS.StrongEps.E4R3.Apriori4Proofs.logW w y
          * (Work.FTS.StrongEps.E4R3.Apriori4Proofs.logPull (Work.Spaces.Dz g) y) ^ 2)
        + Work.FTS.StrongEps.E4R3.Apriori4Proofs.logW w y
          * (Work.FTS.StrongEps.E4R3.Apriori4Proofs.logPull (Work.Spaces.Dth g) y) ^ 2 := by
    intro y
    have hx := mul_le_mul_of_nonneg_left
      (Work.FTS.StrongEps.E4R3.Apriori4Proofs.TransferDeriv.LogPullFacts.norm_fderiv_logPull_sq_le
        hg y) (hw0 y)
    simp only [Work.FTS.StrongEps.E4R3.Apriori4Proofs.logPull_apply] at hx ⊢
    calc Work.FTS.StrongEps.E4R3.Apriori4Proofs.logW w y
          * ‖fderiv ℝ (Work.FTS.StrongEps.E4R3.Apriori4Proofs.logPull g) y‖ ^ 2
        ≤ Work.FTS.StrongEps.E4R3.Apriori4Proofs.logW w y
            * (2 * (Work.Spaces.Dz g (Real.exp y.1) (Real.arctan (Real.exp y.2))) ^ 2
              + (Work.Spaces.Dth g (Real.exp y.1) (Real.arctan (Real.exp y.2))) ^ 2) := hx
      _ = 2 * (Work.FTS.StrongEps.E4R3.Apriori4Proofs.logW w y
            * (Work.Spaces.Dz g (Real.exp y.1) (Real.arctan (Real.exp y.2))) ^ 2)
          + Work.FTS.StrongEps.E4R3.Apriori4Proofs.logW w y
            * (Work.Spaces.Dth g (Real.exp y.1) (Real.arctan (Real.exp y.2))) ^ 2 := by ring
  -- A.e. strong measurability of the integrand.
  have hmeas : AEStronglyMeasurable (fun y : ℝ × ℝ => Work.FTS.StrongEps.E4R3.Apriori4Proofs.logW w y
      * ‖fderiv ℝ (Work.FTS.StrongEps.E4R3.Apriori4Proofs.logPull g) y‖ ^ 2) MeasureTheory.volume :=
    (hwm.aemeasurable.mul ((hcontfd.norm.pow 2).aemeasurable)).aestronglyMeasurable
  have hmain : Integrable (fun y : ℝ × ℝ => Work.FTS.StrongEps.E4R3.Apriori4Proofs.logW w y
      * ‖fderiv ℝ (Work.FTS.StrongEps.E4R3.Apriori4Proofs.logPull g) y‖ ^ 2) := by
    refine hdom.mono' hmeas ?_
    filter_upwards with y
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hw0 y) (sq_nonneg _))]
    exact hle y
  refine ⟨hmain, ?_⟩
  calc ∫ y : ℝ × ℝ, Work.FTS.StrongEps.E4R3.Apriori4Proofs.logW w y
        * ‖fderiv ℝ (Work.FTS.StrongEps.E4R3.Apriori4Proofs.logPull g) y‖ ^ 2
      ≤ ∫ y : ℝ × ℝ, 2 * (Work.FTS.StrongEps.E4R3.Apriori4Proofs.logW w y
          * (Work.FTS.StrongEps.E4R3.Apriori4Proofs.logPull (Work.Spaces.Dz g) y) ^ 2)
        + Work.FTS.StrongEps.E4R3.Apriori4Proofs.logW w y
          * (Work.FTS.StrongEps.E4R3.Apriori4Proofs.logPull (Work.Spaces.Dth g) y) ^ 2 :=
        integral_mono_ae hmain hdom (Eventually.of_forall hle)
    _ = 2 * (∫ y : ℝ × ℝ, Work.FTS.StrongEps.E4R3.Apriori4Proofs.logW w y
          * (Work.FTS.StrongEps.E4R3.Apriori4Proofs.logPull (Work.Spaces.Dz g) y) ^ 2)
        + ∫ y : ℝ × ℝ, Work.FTS.StrongEps.E4R3.Apriori4Proofs.logW w y
          * (Work.FTS.StrongEps.E4R3.Apriori4Proofs.logPull (Work.Spaces.Dth g) y) ^ 2 := by
        rw [integral_add (hA.const_mul 2) hB, integral_const_mul]
    _ = 2 * Work.Coercivity.wip w (Work.Spaces.Dz g) (Work.Spaces.Dz g)
        + Work.Coercivity.wip w (Work.Spaces.Dth g) (Work.Spaces.Dth g) := by
        rw [hAval, hBval]

end Work.FTS.StrongEps.E4R3.Apriori4Proofs.TransferDeriv
end
