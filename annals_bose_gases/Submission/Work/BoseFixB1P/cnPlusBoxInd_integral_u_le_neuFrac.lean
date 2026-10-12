import Mathlib.Tactic.Have
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB1P.Prelim
import Submission.Work.BoseFixB1P.boxPoincareSharp
import Submission.Work.BoseFixB1P.integral_dlBox_u
import Submission.Work.BoseFixB1P.localVar_le_boxTrialForm
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1P.cnPlusBoxInd_integral_u_le_neuFrac`

FS `eq:appTB` gap term (the small-box excited count) against FS `eq:DefT`'s first term (the
anchored box Neumann-resolvent fraction), at the **sharp** constant `1 + π⁻²`
(Brietzke–Solovej `lm:hQuuav`).

The proof is the assembly described in `Submission/Work/BoseFixB1P/Defs.lean`:

* `cnPlusBoxInd_one_eq` (Prelim): the count is the local mean-free mass `∫_{B(u)}(φ - m_u)²`;
* `localVar_le_boxTrialForm` (with the sharp box Poincaré `boxPoincareSharp`): per box,
  `∫_{B(u)}(h - μ_u)² ≤ (1+π⁻²)·boxTrialForm a⁻² (B(u)) h g` for every smooth trial `g`,
  where `h = Qfree ℓ 0 φ` and `a = ℓ*d`;
* `integral_dlBox_u`: the four pieces of the trial functional are tube integrals, so the
  `u`-integral of the per-box bound is `(1+π⁻²)·boxTrialForm a⁻² (acube ℓ) h g`, which is exactly
  the value of the `neuFrac` trial set at `g`;
* `neuFrac` is the `sInf` of those trial values, so the claim follows.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators ENNReal

namespace Work.BoseFixB1P

open Submission.BoseGases

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1000000

/-! ## 1. Elementary bookkeeping -/

/-- `Qfree ℓ 0 φ` is the mean-free part with respect to the anchored box `acube ℓ`. -/
lemma Qfree_zero_apply (ℓ : ℝ) (φ : ℝ³ → ℝ) (x : ℝ³) :
    Work.BoseKinLoc.Qfree ℓ 0 φ x = φ x - Work.BSKinetic.bsMean ℓ 0 φ := rfl

/-- The anchored box `lamBox ℓ 0` is the cube `acube ℓ`. -/
lemma lamBox_zero (ℓ : ℝ) : Work.BoseKinLoc.lamBox ℓ 0 = Submission.BoseGases.acube ℓ := by
  ext x
  simp [Work.BoseKinLoc.lamBox, Work.BSKinetic.bsBox]

/-- The anchored box mean is the mean over `acube ℓ`. -/
lemma bsMean_zero_eq (ℓ : ℝ) (φ : ℝ³ → ℝ) :
    Work.BSKinetic.bsMean ℓ 0 φ = (ℓ ^ 3)⁻¹ * ∫ z in Submission.BoseGases.acube ℓ, φ z := by
  rw [Work.BSKinetic.bsMean]; simp

/-- The volume of the anchored box. -/
lemma volBox_acube {ℓ : ℝ} (hℓ : 0 < ℓ) : volBox (Submission.BoseGases.acube ℓ) = ℓ ^ 3 := by
  rw [volBox, Measure.real_def, Submission.BoseGases.acube_volume ℓ hℓ.le,
    ENNReal.toReal_ofReal (pow_nonneg hℓ.le 3)]

/-- `boxMass` is nonnegative. -/
lemma boxMass_nonneg (ℓ d : ℝ) (u : ℝ³) : 0 ≤ Work.SmallBoxSliding.boxMass ℓ d u := by
  rw [Work.SmallBoxSliding.boxMass_eq_measureReal, Measure.real_def]
  exact ENNReal.toReal_nonneg

/-- **The mean of a shifted state over a sliding box.** -/
lemma mean_dlBox_sub_const {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d) {u : ℝ³} {M : ℝ}
    {ψ : ℝ³ → ℝ} (hψ : Continuous ψ) (hb : Work.SmallBoxSliding.boxMass ℓ d u ≠ 0) :
    (1 / Work.SmallBoxSliding.boxMass ℓ d u) * ∫ z in dlBox ℓ d u, (ψ z - M)
      = ((1 / Work.SmallBoxSliding.boxMass ℓ d u) * ∫ z in dlBox ℓ d u, ψ z) - M := by
  have hInt1 : IntegrableOn ψ (dlBox ℓ d u) volume :=
    hψ.continuousOn.integrableOn_compact (Work.SmallBoxTBWord.isCompact_dlBox hℓ hd u)
  have hInt2 : IntegrableOn (fun _ : ℝ³ => M) (dlBox ℓ d u) volume :=
    continuousOn_const.integrableOn_compact (Work.SmallBoxTBWord.isCompact_dlBox hℓ hd u)
  have hlin : (∫ z in dlBox ℓ d u, (ψ z - M))
      = (∫ z in dlBox ℓ d u, ψ z) - M * Work.SmallBoxSliding.boxMass ℓ d u := by
    rw [MeasureTheory.integral_sub hInt1 hInt2, MeasureTheory.setIntegral_const, smul_eq_mul,
      ← Work.SmallBoxSliding.boxMass_eq_measureReal]
    ring
  rw [hlin, mul_sub, mul_comm M (Work.SmallBoxSliding.boxMass ℓ d u), ← mul_assoc]
  simp only [div_eq_mul_inv, one_mul]
  rw [inv_mul_cancel₀ hb, one_mul]

/-- An integral over a null set vanishes. -/
lemma setIntegral_eq_zero_of_measure_zero {s : Set ℝ³} (h : (volume : Measure ℝ³) s = 0)
    (f : ℝ³ → ℝ) : (∫ x in s, f x) = 0 := by
  rw [MeasureTheory.Measure.restrict_eq_zero.mpr h]
  simp

/-! ## 2. The two load-bearing steps -/

/-- **The per-box bound, pointwise in `u`.**  For every smooth trial `g`, the local mean-free
mass of `φ` over the sliding box `B(u)` is bounded by `(1+π⁻²)` times the trial functional over
that box, evaluated at `h = Qfree ℓ 0 φ`.

Proof: `localVar_le_boxTrialForm` applied to the box `B(u) = Box3 (boxLo) (boxHi)`
(`dlBox_eq_Box3`, sides `≤ ℓ*d` by `boxHi_sub_boxLo_le`) with the sharp box Poincaré
`boxPoincareSharp`; the mean `(1/|B(u)|)∫_{B(u)}h` is `(1/|B(u)|)∫_{B(u)}φ - M`
(`mean_dlBox_sub_const`), which is the mean of `φ - M` over the box.  When `boxMass = 0` the box
is a null set and both sides vanish. -/
lemma per_box_bound {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d) {φ : ℝ³ → ℝ}
    (hφ : ContDiff ℝ (⊤ : ENat) φ) {g : ℝ³ → ℝ} (hg : ContDiff ℝ (⊤ : ENat) g) (u : ℝ³) :
    (∫ z in dlBox ℓ d u, (φ z - (1 / Work.SmallBoxSliding.boxMass ℓ d u)
        * ∫ w in dlBox ℓ d u, φ w) ^ 2)
      ≤ (1 + (Real.pi ^ 2)⁻¹) *
          boxTrialForm ((d * ℓ) ^ (-2 : ℤ)) (dlBox ℓ d u)
            (fun x => φ x - Work.BSKinetic.bsMean ℓ 0 φ) g := by
  by_cases hb : Work.SmallBoxSliding.boxMass ℓ d u = 0
  · -- degenerate case: the sliding box is a null set, both sides vanish
    have hnull : (volume : Measure ℝ³) (dlBox ℓ d u) = 0 := by
      have hreal : (volume : Measure ℝ³).real (dlBox ℓ d u) = 0 := by
        rw [← Work.SmallBoxSliding.boxMass_eq_measureReal]; exact hb
      rw [Measure.real_def, ENNReal.toReal_eq_zero_iff] at hreal
      rcases hreal with h | h
      · exact h
      · exact absurd h (ne_top_of_le_ne_top
          (ENNReal.ofReal_ne_top) (Submission.BoseGases.acube_volume ℓ hℓ.le ▸
            measure_mono (Set.inter_subset_left)))
    have hL : (∫ z in dlBox ℓ d u, (φ z - (1 / Work.SmallBoxSliding.boxMass ℓ d u)
        * ∫ w in dlBox ℓ d u, φ w) ^ 2) = 0 :=
      setIntegral_eq_zero_of_measure_zero hnull _
    have hR : boxTrialForm ((d * ℓ) ^ (-2 : ℤ)) (dlBox ℓ d u)
        (fun x => φ x - Work.BSKinetic.bsMean ℓ 0 φ) g = 0 := by
      rw [boxTrialForm]
      simp only [setIntegral_eq_zero_of_measure_zero hnull]
      ring
    rw [hL, hR]
    simp
  · -- main case: apply the per-box inequality on `Box3 (boxLo) (boxHi)`
    set p : Fin 3 → ℝ := boxLo ℓ d u with hp
    set q : Fin 3 → ℝ := boxHi ℓ d u with hq
    have hPeq : dlBox ℓ d u = Box3 p q := by
      rw [hp, hq]; exact dlBox_eq_Box3 ℓ d u
    have hside : ∀ j : Fin 3, q j - p j ≤ d * ℓ := by
      intro j
      have h := boxHi_sub_boxLo_le (ℓ := ℓ) (d := d) u j
      rw [← hp, ← hq] at h
      linarith [h]
    have hvol : volBox (Box3 p q) = Work.SmallBoxSliding.boxMass ℓ d u := by
      rw [← hPeq, boxMass_eq_volBox]
    have hvolpos : 0 < volBox (Box3 p q) := by
      rw [hvol]
      exact lt_of_le_of_ne (boxMass_nonneg ℓ d u) (Ne.symm hb)
    have hpoin : ∀ v : ℝ³ → ℝ, ContDiff ℝ (⊤ : ENat) v →
        (∫ x in Box3 p q, v x) = 0 →
        Real.pi ^ 2 / (d * ℓ) ^ 2 * (∫ x in Box3 p q, (v x) ^ 2)
          ≤ ∑ k : Fin 3, ∫ x in Box3 p q,
              (fderiv ℝ v x (Submission.BoseGases.kcStdBasis k)) ^ 2 :=
      fun v hv hmean => boxPoincareSharp (by positivity) p q hside v hv hmean
    have hC := localVar_le_boxTrialForm (a := d * ℓ) (c := (d * ℓ) ^ (-2 : ℤ))
      (by positivity) rfl p q hside hvolpos (fun x => φ x - Work.BSKinetic.bsMean ℓ 0 φ)
      g (hφ.sub contDiff_const) hg hpoin
    have hmean : (1 / Work.SmallBoxSliding.boxMass ℓ d u)
          * (∫ x in dlBox ℓ d u, (φ x - Work.BSKinetic.bsMean ℓ 0 φ))
        = ((1 / Work.SmallBoxSliding.boxMass ℓ d u)
            * (∫ w in dlBox ℓ d u, φ w)) - Work.BSKinetic.bsMean ℓ 0 φ :=
      mean_dlBox_sub_const hℓ hd (M := Work.BSKinetic.bsMean ℓ 0 φ)
        (ψ := φ) hφ.continuous hb
    have hLHS : localVar (Box3 p q) (fun x => φ x - Work.BSKinetic.bsMean ℓ 0 φ)
        = ∫ z in dlBox ℓ d u, (φ z - (1 / Work.SmallBoxSliding.boxMass ℓ d u)
            * ∫ w in dlBox ℓ d u, φ w) ^ 2 := by
      rw [localVar, ← hPeq, ← boxMass_eq_volBox ℓ d u]
      rw [hmean]
      congr 1
      funext z
      ring
    have hRHS : boxTrialForm ((d * ℓ) ^ (-2 : ℤ)) (Box3 p q)
          (fun x => φ x - Work.BSKinetic.bsMean ℓ 0 φ) g
        = boxTrialForm ((d * ℓ) ^ (-2 : ℤ)) (dlBox ℓ d u)
            (fun x => φ x - Work.BSKinetic.bsMean ℓ 0 φ) g := by
      rw [boxTrialForm, boxTrialForm, ← hPeq]
    rw [← hLHS, ← hRHS]
    exact hC

/-- **The `u`-integral of the trial functional.**  The four pieces of `boxTrialForm` are tube
integrals (`integral_dlBox_u`), so integrating `boxTrialForm c (B(u)) h g` over all positions of
the small box recovers `boxTrialForm c (acube ℓ) h g`; the marginal is integrable for the same
reason. -/
lemma integral_u_boxTrialForm {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d) (c : ℝ)
    {h : ℝ³ → ℝ} (hh : Continuous h) {g : ℝ³ → ℝ} (hg : ContDiff ℝ (⊤ : ENat) g) :
    Integrable (fun u : ℝ³ => boxTrialForm c (dlBox ℓ d u) h g)
      ∧ (∫ u : ℝ³, boxTrialForm c (dlBox ℓ d u) h g) = boxTrialForm c (acube ℓ) h g := by
  have hdg : ∀ k : Fin 3,
      Continuous (fun x : ℝ³ => fderiv ℝ g x (Submission.BoseGases.kcStdBasis k)) :=
    fun k => (hg.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have h1 := integral_dlBox_u hℓ hd (hh.pow 2)
  have h2 := integral_dlBox_u hℓ hd (hh.mul hg.continuous)
  have h3 : ∀ k : Fin 3, Integrable (fun u : ℝ³ => ∫ x in dlBox ℓ d u,
        (fderiv ℝ g x (Submission.BoseGases.kcStdBasis k)) ^ 2)
      ∧ (∫ u : ℝ³, ∫ x in dlBox ℓ d u,
            (fderiv ℝ g x (Submission.BoseGases.kcStdBasis k)) ^ 2)
          = ∫ x in acube ℓ, (fderiv ℝ g x (Submission.BoseGases.kcStdBasis k)) ^ 2 :=
    fun k => integral_dlBox_u hℓ hd ((hdg k).pow 2)
  have h4 := integral_dlBox_u hℓ hd (hg.continuous.pow 2)
  have hsum : Integrable (fun u : ℝ³ => ∑ k : Fin 3,
      ∫ x in dlBox ℓ d u, (fderiv ℝ g x (Submission.BoseGases.kcStdBasis k)) ^ 2) :=
    integrable_finsetSum Finset.univ (fun k _ => (h3 k).1)
  set G1 : ℝ³ → ℝ := fun u => ∑ k : Fin 3, ∫ x in dlBox ℓ d u,
      (fderiv ℝ g x (Submission.BoseGases.kcStdBasis k)) ^ 2 with hG1
  set G2 : ℝ³ → ℝ := fun u => ∫ x in dlBox ℓ d u, (g x) ^ 2 with hG2
  set G3 : ℝ³ → ℝ := fun u => ∫ x in dlBox ℓ d u, h x * g x with hG3
  have intG1 : Integrable G1 := hsum
  have intG2 : Integrable G2 := h4.1
  have intG3 : Integrable G3 := h2.1
  set F1 : ℝ³ → ℝ := fun u => ∫ x in dlBox ℓ d u, (h x) ^ 2 with hF1
  set F2 : ℝ³ → ℝ := fun u => 2 * c * G3 u with hF2
  set F3 : ℝ³ → ℝ := fun u => c * (G1 u + c * G2 u) with hF3
  have intF1 : Integrable F1 := h1.1
  have intF2 : Integrable F2 := intG3.const_mul (2 * c)
  have intF3 : Integrable F3 := (intG1.add (intG2.const_mul c)).const_mul c
  have hcongrf : (fun u : ℝ³ => boxTrialForm c (dlBox ℓ d u) h g) = F1 - F2 + F3 := by
    funext u
    rw [boxTrialForm, hF1, hF2, hF3, hG1, hG2, hG3]
    simp only [Pi.add_apply, Pi.sub_apply]
  have hcongr : (∫ u : ℝ³, (F1 - F2 + F3) u) = ∫ u : ℝ³, boxTrialForm c (dlBox ℓ d u) h g := by
    rw [hcongrf]
  have hs : (∑ k : Fin 3, ∫ u : ℝ³, ∫ x in dlBox ℓ d u,
        (fderiv ℝ g x (Submission.BoseGases.kcStdBasis k)) ^ 2)
      = ∑ k : Fin 3, ∫ x in acube ℓ,
          (fderiv ℝ g x (Submission.BoseGases.kcStdBasis k)) ^ 2 :=
    Finset.sum_congr rfl fun k _ => (h3 k).2
  have hG1int : (∫ u : ℝ³, G1 u) = ∑ k : Fin 3, ∫ u : ℝ³, ∫ x in dlBox ℓ d u,
      (fderiv ℝ g x (Submission.BoseGases.kcStdBasis k)) ^ 2 := by
    rw [hG1]
    exact MeasureTheory.integral_finsetSum Finset.univ (fun k _ => (h3 k).1)
  have hF1int : (∫ u : ℝ³, F1 u) = ∫ x in acube ℓ, (h x) ^ 2 := by
    rw [hF1]; exact h1.2
  have hG2int : (∫ u : ℝ³, G2 u) = ∫ x in acube ℓ, (g x) ^ 2 := by
    rw [hG2]; exact h4.2
  have hG3int : (∫ u : ℝ³, G3 u) = ∫ x in acube ℓ, h x * g x := by
    rw [hG3]; exact h2.2
  have hF2int : (∫ u : ℝ³, F2 u) = 2 * c * ∫ u : ℝ³, G3 u := by
    rw [hF2]; exact MeasureTheory.integral_const_mul (2 * c) G3
  have hF3int : (∫ u : ℝ³, F3 u) = c * ∫ u : ℝ³, (G1 u + c * G2 u) := by
    rw [hF3]; exact MeasureTheory.integral_const_mul c _
  have hFmid : (∫ u : ℝ³, (G1 u + c * G2 u)) = (∫ u : ℝ³, G1 u) + c * ∫ u : ℝ³, G2 u := by
    rw [MeasureTheory.integral_add intG1 (intG2.const_mul c)]
    rw [MeasureTheory.integral_const_mul]
  refine ⟨?_, ?_⟩
  · rw [hcongrf]
    exact (intF1.sub intF2).add intF3
  · rw [← hcongr]
    rw [MeasureTheory.integral_add' (f := F1 - F2) (g := F3) (intF1.sub intF2) intF3]
    rw [MeasureTheory.integral_sub' (f := F1) (g := F2) intF1 intF2]
    rw [hF1int, hF2int, hF3int, hFmid, hG1int, hG2int, hG3int]
    rw [hs, boxTrialForm]

/-! ## 3. The assembly -/

theorem cnPlusBoxInd_integral_u_le_neuFrac {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d)
    (φ : EuclideanSpace ℝ (Fin 3) → ℝ) (hφ : ContDiff ℝ (⊤ : ENat) φ) :
    (∫ u : EuclideanSpace ℝ (Fin 3),
        Work.UBBInputs8.cnPlusBoxInd ℓ (Submission.BoseGases.dlBox ℓ d u)
          (Work.SmallBoxSliding.boxMass ℓ d u) (fun x : Submission.BoseGases.X 1 => φ (x 0)))
      ≤ (1 + (Real.pi ^ 2)⁻¹) *
          Work.BoseKinLoc.neuFrac ℓ ((d * ℓ) ^ (-2 : ℤ)) 0 (Work.BoseKinLoc.Qfree ℓ 0 φ) := by
  set c : ℝ := (d * ℓ) ^ (-2 : ℤ) with hc
  set M : ℝ := Work.BSKinetic.bsMean ℓ 0 φ with hM
  have hcont : Continuous (fun x : ℝ³ => φ x - M) := hφ.continuous.sub continuous_const
  have hpos : (0 : ℝ) < 1 + (Real.pi ^ 2)⁻¹ := by positivity
  -- (a) rewrite the left-hand side as the `u`-integral of the local mean-free mass
  have hLHS : (∫ u : ℝ³,
        Work.UBBInputs8.cnPlusBoxInd ℓ (dlBox ℓ d u)
          (Work.SmallBoxSliding.boxMass ℓ d u) (fun x : Submission.BoseGases.X 1 => φ (x 0)))
      = ∫ u : ℝ³, ∫ z in dlBox ℓ d u, (φ z - (1 / Work.SmallBoxSliding.boxMass ℓ d u)
          * ∫ w in dlBox ℓ d u, φ w) ^ 2 := by
    apply integral_congr_ae
    filter_upwards with u
    exact cnPlusBoxInd_one_eq hℓ hd φ hφ.continuous u
  -- (b) for every trial, the `u`-integral is bounded by the trial functional
  have key : ∀ g : ℝ³ → ℝ, ContDiff ℝ (⊤ : ENat) g → HasCompactSupport g →
      (∫ u : ℝ³, ∫ z in dlBox ℓ d u, (φ z - (1 / Work.SmallBoxSliding.boxMass ℓ d u)
          * ∫ w in dlBox ℓ d u, φ w) ^ 2)
        ≤ (1 + (Real.pi ^ 2)⁻¹) * boxTrialForm c (acube ℓ) (fun x => φ x - M) g := by
    intro g hg hgs
    obtain ⟨hint, hint_eq⟩ := integral_u_boxTrialForm hℓ hd c hcont hg
    have hmono : (∫ u : ℝ³, ∫ z in dlBox ℓ d u, (φ z - (1 / Work.SmallBoxSliding.boxMass ℓ d u)
          * ∫ w in dlBox ℓ d u, φ w) ^ 2)
        ≤ ∫ u : ℝ³, (1 + (Real.pi ^ 2)⁻¹) * boxTrialForm c (dlBox ℓ d u)
            (fun x => φ x - M) g := by
      refine MeasureTheory.integral_mono_of_nonneg ?_ (hint.const_mul _) ?_
      · exact Filter.Eventually.of_forall fun u => integral_nonneg fun z => sq_nonneg _
      · exact Filter.Eventually.of_forall fun u => per_box_bound hℓ hd hφ hg u
    calc (∫ u : ℝ³, ∫ z in dlBox ℓ d u, (φ z - (1 / Work.SmallBoxSliding.boxMass ℓ d u)
          * ∫ w in dlBox ℓ d u, φ w) ^ 2)
        ≤ ∫ u : ℝ³, (1 + (Real.pi ^ 2)⁻¹) * boxTrialForm c (dlBox ℓ d u)
            (fun x => φ x - M) g := hmono
      _ = (1 + (Real.pi ^ 2)⁻¹) * ∫ u : ℝ³, boxTrialForm c (dlBox ℓ d u)
            (fun x => φ x - M) g := by rw [integral_const_mul]
      _ = (1 + (Real.pi ^ 2)⁻¹) * boxTrialForm c (acube ℓ) (fun x => φ x - M) g := by
            rw [hint_eq]
  rw [hLHS]
  -- (c) the `sInf` bookkeeping: `neuFrac` is the infimum of the trial values
  have hQ : Work.BoseKinLoc.Qfree ℓ 0 φ = fun x => φ x - M := by
    funext x; rw [Qfree_zero_apply, hM]
  have hlam : Work.BoseKinLoc.lamBox ℓ 0 = Submission.BoseGases.acube ℓ := lamBox_zero ℓ
  have hset : {v : ℝ | ∃ g : ℝ³ → ℝ, ContDiff ℝ (⊤ : ENat) g ∧ HasCompactSupport g ∧
        v = (∫ z in Work.BoseKinLoc.lamBox ℓ 0, ((fun x : ℝ³ => φ x - M) z) ^ 2)
          - 2 * c * (∫ z in Work.BoseKinLoc.lamBox ℓ 0, ((fun x : ℝ³ => φ x - M) z) * g z)
          + c * ((∑ k : Fin 3, ∫ z in Work.BoseKinLoc.lamBox ℓ 0,
                    (fderiv ℝ g z (Submission.BoseGases.kcStdBasis k)) ^ 2)
                  + c * (∫ z in Work.BoseKinLoc.lamBox ℓ 0, (g z) ^ 2))}
      = {v : ℝ | ∃ g : ℝ³ → ℝ, ContDiff ℝ (⊤ : ENat) g ∧ HasCompactSupport g ∧
        v = boxTrialForm c (acube ℓ) (fun x => φ x - M) g} := by
    ext v
    constructor
    · rintro ⟨g, hg, hgs, rfl⟩
      exact ⟨g, hg, hgs, by rw [boxTrialForm, hlam]⟩
    · rintro ⟨g, hg, hgs, rfl⟩
      exact ⟨g, hg, hgs, by rw [boxTrialForm, hlam]⟩
  have hne : Work.BoseKinLoc.neuFrac ℓ c 0 (fun x : ℝ³ => φ x - M)
      = sInf {v : ℝ | ∃ g : ℝ³ → ℝ, ContDiff ℝ (⊤ : ENat) g ∧ HasCompactSupport g ∧
        v = boxTrialForm c (acube ℓ) (fun x => φ x - M) g} := by
    rw [Work.BoseKinLoc.neuFrac, hset]
  rw [hQ, hne]
  have hdiv : (∫ u : ℝ³, ∫ z in dlBox ℓ d u, (φ z - (1 / Work.SmallBoxSliding.boxMass ℓ d u)
          * ∫ w in dlBox ℓ d u, φ w) ^ 2) / (1 + (Real.pi ^ 2)⁻¹)
      ≤ sInf {v : ℝ | ∃ g : ℝ³ → ℝ, ContDiff ℝ (⊤ : ENat) g ∧ HasCompactSupport g ∧
        v = boxTrialForm c (acube ℓ) (fun x => φ x - M) g} := by
    refine le_csInf ⟨boxTrialForm c (acube ℓ) (fun x => φ x - M) 0,
      ⟨0, contDiff_const, HasCompactSupport.zero, rfl⟩⟩ ?_
    rintro v ⟨g, hg, hgs, rfl⟩
    have h := key g hg hgs
    rw [div_le_iff₀ hpos, mul_comm]
    exact h
  calc (∫ u : ℝ³, ∫ z in dlBox ℓ d u, (φ z - (1 / Work.SmallBoxSliding.boxMass ℓ d u)
        * ∫ w in dlBox ℓ d u, φ w) ^ 2)
      = (1 + (Real.pi ^ 2)⁻¹) *
          ((∫ u : ℝ³, ∫ z in dlBox ℓ d u, (φ z - (1 / Work.SmallBoxSliding.boxMass ℓ d u)
            * ∫ w in dlBox ℓ d u, φ w) ^ 2) / (1 + (Real.pi ^ 2)⁻¹)) :=
        (mul_div_cancel₀ _ (ne_of_gt hpos)).symm
    _ ≤ (1 + (Real.pi ^ 2)⁻¹) * sInf {v : ℝ | ∃ g : ℝ³ → ℝ, ContDiff ℝ (⊤ : ENat) g ∧
          HasCompactSupport g ∧
        v = boxTrialForm c (acube ℓ) (fun x => φ x - M) g} :=
        mul_le_mul_of_nonneg_left hdiv hpos.le

end Work.BoseFixB1P
