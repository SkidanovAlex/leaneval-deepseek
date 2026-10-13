import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongEps.E4R3.Apriori4Proofs.JepsTransfer.Defs
import Submission.Work.FTS.StrongEps.E4R3.Apriori4Proofs.JepsTransfer.Recur
import Submission.Work.FTS.StrongEps.E4R3.Apriori4Proofs.JepsTransfer.KernelFacts
import Submission.Work.FTS.StrongEps.E4R3.Apriori4Proofs.JepsTransfer.LogInt
import Submission.Work.FTS.StrongEps.E4R3.Apriori4Proofs.JepsTransfer.Flat
import Submission.Work.FTS.StrongEps.E4R3.Apriori4Proofs.JepsTransfer.Transfer
import Submission.Work.FTS.StrongEps.E4R3.Apriori4Proofs.JepsTransfer.continuous_logW_leaf

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


