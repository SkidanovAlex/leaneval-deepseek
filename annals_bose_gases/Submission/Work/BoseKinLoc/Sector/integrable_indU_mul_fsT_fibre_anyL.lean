import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseKinLoc.Sector.aemeasurable_gapWord_zero_fibre
import Submission.Work.BoseKinLoc.Sector.aemeasurable_mainWord_zero_fibre
import Submission.Work.BoseKinLoc.Sector.aemeasurable_momWord_zero_fibre
import Submission.Work.BoseKinLoc.Sector.aemeasurable_neuWord_zero_fibre
import Submission.Work.BoseKinLoc.Sector.fibre_defs_v3
import Submission.Work.BoseKinLoc.Sector.fsT_bound_all
import Submission.Work.BoseKinLoc.Sector.fsT_box_invariant
import Submission.Work.BoseKinLoc.Word.boxFormB_eq_boxForm_of_supp
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

noncomputable section

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators ENNReal

namespace Work.BoseKinLoc.Sector

open Submission.BoseGases

set_option autoImplicit false
set_option linter.unusedVariables false

/-!
# `Work.BoseKinLoc.Sector.integrable_indU_mul_fsT_fibre_anyL` — the slot-`i` kinetic integrand

The target of this module is the *unconditional* (`L` of either sign) version of
`Work.BoseKinLoc.Sector.integrable_indU_mul_fsT_fibre`: for a smooth state `Ψ` with
`tsupport Ψ ⊆ abox N L` and **no hypothesis on `L`**, the `i`-th slot integrand of the localised
kinetic word,

    `x ↦ 1_{Λ(0)}(xᵢ) · fsT ℓ d s ε_T b 0 (fibre N i Ψ x)`,

is integrable on `X N`.

## Strategy

* `L < 0` forces `abox N L = ∅` (the centred cube `acube L` is empty for `L < 0`), hence
  `Ψ = 0`, hence every fibre is zero and the integrand vanishes identically
  (`Word.fsT_zero`).  So there is nothing to prove in that case, and *the conclusion does not
  depend on `L` at all*: only on the fibre family, which is `L`-free.
* `0 ≤ L`: the argument is a *bounding* argument, as opposed to the dominating-`H¹`-data argument
  of the sibling module `integrable_indU_mul_fsT_fibre`.

  1. *Measurability.* `1_{Λ(0)}(q₁) · fsT … 0 (genFibre i Ψ q₂)` is a.e. strongly measurable on
     `ℝ³ × X n`: the anchored fibre word is (`fsT_fibre_zero_aemeasurable`, assembled here from
     the four word lemmas `aemeasurable_gapWord_zero_fibre`, `aemeasurable_momWord_zero_fibre`,
     `aemeasurable_neuWord_zero_fibre`, `aemeasurable_mainWord_zero_fibre`), the indicator is
     measurable, and the pullback along the measure preserving insertion `kcInsN n i` gives
     measurability of the integrand on `X (n+1)` (`MeasurePreserving.aemeasurable_comp_iff`).
  2. *Support.* The integrand vanishes off `abox (n+1) (max L ℓ)`
     (`indU_mul_fsT_fibre_eq_zero_of_notMem_abox_max`), a set of finite measure.
  3. *Bound.* `|fsT … 0 (genFibre i Ψ r)|` is bounded uniformly in `r` by a constant depending
     only on `Ψ, ℓ` (`bound_fsT_genFibre_zero_aux`: `fsT_H1_bound_all` plus the uniform `L²`- and
     Dirichlet-bounds for the fibres, which are supported in `acube L`), and `|1_{Λ(0)}| ≤ 1`.

     `IntegrableOn.of_bound` on the support box then gives `IntegrableOn`, and
     `integrableOn_iff_integrable_of_support_subset` upgrades it to `Integrable` on all of
     `X (n+1)`.
-/

/-! ## 1. Elementary auxiliary facts -/

/-- `a² ≤ M²` whenever `|a| ≤ M`. -/
private lemma sq_le_sq_of_abs_le {a M : ℝ} (h : |a| ≤ M) : a ^ 2 ≤ M ^ 2 := by
  have h1 := pow_le_pow_left₀ (abs_nonneg a) h 2
  rwa [sq_abs] at h1

/-- The indicator of the centred cube of a constant is integrable. -/
private lemma integrable_indicator_const_acube {L : ℝ} (hL : 0 ≤ L) (c : ℝ) :
    MeasureTheory.Integrable ((Submission.BoseGases.acube L).indicator (fun _ => c)) := by
  rw [MeasureTheory.integrable_indicator_iff (Submission.BoseGases.acube_measurable L)]
  refine MeasureTheory.integrableOn_const ?_ ?_
  · rw [Submission.BoseGases.acube_volume L hL]
    exact ENNReal.ofReal_lt_top.ne
  · rw [Real.enorm_eq_ofReal_abs]
    exact ENNReal.ofReal_lt_top.ne

/-- Its integral is `c` times the volume of the cube. -/
private lemma integral_indicator_const_acube {L : ℝ} (hL : 0 ≤ L) (c : ℝ) :
    (∫ z : EuclideanSpace ℝ (Fin 3),
        (Submission.BoseGases.acube L).indicator (fun _ => c) z)
      = c * (MeasureTheory.volume (Submission.BoseGases.acube L)).toReal := by
  rw [MeasureTheory.integral_indicator (Submission.BoseGases.acube_measurable L),
    MeasureTheory.setIntegral_const, Measure.real_def]
  rw [smul_eq_mul, mul_comm]

/-! ## 2. Uniform bound for the anchored fibre word -/

/-- **The anchored fibre word is uniformly bounded in the configuration of the remaining
particles.**  For a smooth `Φ` supported in `abox (n+1) L` with `0 ≤ L`, there is a constant `M`
(depending only on `Φ, ℓ`) with

    `|fsT ℓ d s ε_T b 0 (genFibre i Φ r)| ≤ M`   for every `r : X n`.

The proof is `fsT_H1_bound_all`: `|fsT … ψ| ≤ C (∫ψ² + Σ_k ∫(∂_kψ)²)`, and for the fibres
`ψ = genFibre i Φ r` both terms are bounded *uniformly in `r`*, because the fibre vanishes off the
cube `acube L` and is bounded by `Φ` (resp. its derivative) there. -/
private theorem bound_fsT_genFibre_zero_aux {ℓ L d s εT b : ℝ} (hℓ : 0 < ℓ) (hL : 0 ≤ L) {n : ℕ}
    {Φ : Submission.BoseGases.X (n + 1) → ℝ} (hΦ : ContDiff ℝ (⊤ : ENat) Φ)
    (hsupp : tsupport Φ ⊆ Submission.BoseGases.abox (n + 1) L) (i : Fin (n + 1)) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ r : Submission.BoseGases.X n,
        |Work.BoseKinLoc.fsT ℓ d s εT b 0
          (fun z : EuclideanSpace ℝ (Fin 3) =>
            Φ (Submission.BoseGases.kcInsN n i (z, r)))| ≤ M := by
  have hcs : HasCompactSupport Φ :=
    IsCompact.of_isClosed_subset
      (Work.BoseKinLoc.Kinetic.abox_compact_of_nonneg (n + 1) hL) (isClosed_tsupport Φ) hsupp
  obtain ⟨C, hC0, hCbd⟩ :=
    Work.BoseKinLoc.Kinetic.fsT_H1_bound_all (ℓ := ℓ) (d := d) (s := s) (εT := εT) (b := b) hℓ
  obtain ⟨MΦ, hMΦ⟩ :=
    Work.BoseKinLoc.Kinetic.exists_abs_bound_of_tsupport_subset_abox (n := n) (L := L) hL hΦ hsupp
  obtain ⟨Md0, hMd0⟩ := (hcs.fderiv ℝ).exists_bound_of_continuous (hΦ.continuous_fderiv (by simp))
  set Md : ℝ := max Md0 0 with hMddef
  have hMd : ∀ ξ : Submission.BoseGases.X (n + 1), ‖fderiv ℝ Φ ξ‖ ≤ Md :=
    fun ξ => le_trans (hMd0 ξ) (le_max_left _ _)
  set V : ℝ := (MeasureTheory.volume (Submission.BoseGases.acube L)).toReal with hVdef
  have hV0 : 0 ≤ V := by rw [hVdef]; exact ENNReal.toReal_nonneg
  refine ⟨C * (MΦ ^ 2 * V
      + (∑ k : Fin 3, (Md * ‖Submission.BoseGases.kcDir (n + 1) i k‖) ^ 2) * V), ?_, fun r => ?_⟩
  · refine mul_nonneg hC0 (add_nonneg (mul_nonneg (sq_nonneg _) hV0) (mul_nonneg ?_ hV0))
    exact Finset.sum_nonneg (fun k _ => sq_nonneg _)
  set ψ : EuclideanSpace ℝ (Fin 3) → ℝ := Work.BoseKinLoc.Kinetic.genFibre i Φ r with hψdef
  have hbd := hCbd 0 ψ (Work.BoseKinLoc.Kinetic.genFibre_contDiff hΦ i r)
    (Work.BoseKinLoc.Kinetic.genFibre_hasCompactSupport_of_supp hL hsupp i r)
  -- the `L²`-mass of a fibre is bounded by `MΦ²` times the volume of the cube
  have hA : (∫ z : EuclideanSpace ℝ (Fin 3), (ψ z) ^ 2) ≤ MΦ ^ 2 * V := by
    have hpoint : ∀ z : EuclideanSpace ℝ (Fin 3), (ψ z) ^ 2
        ≤ (Submission.BoseGases.acube L).indicator (fun _ => MΦ ^ 2) z := by
      intro z
      by_cases hz : z ∈ Submission.BoseGases.acube L
      · rw [Set.indicator_of_mem hz, hψdef]
        exact sq_le_sq_of_abs_le (hMΦ (Submission.BoseGases.kcInsN n i (z, r)))
      · rw [Set.indicator_of_notMem hz, hψdef,
          Work.BoseKinLoc.Kinetic.genFibre_eq_zero_of_not_mem_acube hsupp i hz]
        norm_num
    have hmono := MeasureTheory.integral_mono_of_nonneg
      (Filter.Eventually.of_forall fun z => sq_nonneg (ψ z))
      (integrable_indicator_const_acube (L := L) hL (MΦ ^ 2))
      (Filter.Eventually.of_forall hpoint)
    rwa [integral_indicator_const_acube (L := L) hL (MΦ ^ 2)] at hmono
  -- the same for each directional derivative
  have hDk : ∀ k : Fin 3,
      (∫ z : EuclideanSpace ℝ (Fin 3),
          (fderiv ℝ ψ z (Submission.BoseGases.kcStdBasis k)) ^ 2)
        ≤ (Md * ‖Submission.BoseGases.kcDir (n + 1) i k‖) ^ 2 * V := by
    intro k
    have hpoint : ∀ z : EuclideanSpace ℝ (Fin 3),
        (fderiv ℝ ψ z (Submission.BoseGases.kcStdBasis k)) ^ 2
          ≤ (Submission.BoseGases.acube L).indicator
              (fun _ => (Md * ‖Submission.BoseGases.kcDir (n + 1) i k‖) ^ 2) z := by
      intro z
      by_cases hz : z ∈ Submission.BoseGases.acube L
      · rw [Set.indicator_of_mem hz]
        have h1 : fderiv ℝ ψ z (Submission.BoseGases.kcStdBasis k)
            = fderiv ℝ Φ (Submission.BoseGases.kcInsN n i (z, r))
                (Submission.BoseGases.kcDir (n + 1) i k) := by
          rw [hψdef]
          exact Submission.BoseGases.fiber_fderiv_kcDir i hΦ r z k
        rw [h1]
        have h2 : ‖fderiv ℝ Φ (Submission.BoseGases.kcInsN n i (z, r))
              (Submission.BoseGases.kcDir (n + 1) i k)‖
            ≤ Md * ‖Submission.BoseGases.kcDir (n + 1) i k‖ :=
          le_trans ((fderiv ℝ Φ (Submission.BoseGases.kcInsN n i (z, r))).le_opNorm
              (Submission.BoseGases.kcDir (n + 1) i k))
            (mul_le_mul_of_nonneg_right (hMd _) (norm_nonneg _))
        rw [Real.norm_eq_abs] at h2
        exact sq_le_sq_of_abs_le h2
      · -- off the cube the fibre vanishes on a whole neighbourhood, so its derivative vanishes
        rw [Set.indicator_of_notMem hz]
        have hmem : (Submission.BoseGases.acube L)ᶜ ∈ 𝓝 z :=
          (Submission.BoseGases.acube_isClosed L).isOpen_compl.mem_nhds hz
        have hEv : ψ =ᶠ[𝓝 z] (fun _ : EuclideanSpace ℝ (Fin 3) => (0 : ℝ)) := by
          filter_upwards [hmem] with w hw
          rw [hψdef]
          exact Work.BoseKinLoc.Kinetic.genFibre_eq_zero_of_not_mem_acube hsupp i hw
        have hzero : fderiv ℝ ψ z = 0 := by
          rw [Filter.EventuallyEq.fderiv_eq hEv]
          simp
        rw [hzero]
        simp
    have hmono := MeasureTheory.integral_mono_of_nonneg
      (Filter.Eventually.of_forall fun z =>
        sq_nonneg (fderiv ℝ ψ z (Submission.BoseGases.kcStdBasis k)))
      (integrable_indicator_const_acube (L := L) hL
        ((Md * ‖Submission.BoseGases.kcDir (n + 1) i k‖) ^ 2))
      (Filter.Eventually.of_forall hpoint)
    rwa [integral_indicator_const_acube (L := L) hL
      ((Md * ‖Submission.BoseGases.kcDir (n + 1) i k‖) ^ 2)] at hmono
  have hD : (∑ k : Fin 3, ∫ z : EuclideanSpace ℝ (Fin 3),
        (fderiv ℝ ψ z (Submission.BoseGases.kcStdBasis k)) ^ 2)
      ≤ (∑ k : Fin 3, (Md * ‖Submission.BoseGases.kcDir (n + 1) i k‖) ^ 2) * V := by
    calc (∑ k : Fin 3, ∫ z : EuclideanSpace ℝ (Fin 3),
          (fderiv ℝ ψ z (Submission.BoseGases.kcStdBasis k)) ^ 2)
        ≤ ∑ k : Fin 3, (Md * ‖Submission.BoseGases.kcDir (n + 1) i k‖) ^ 2 * V :=
          Finset.sum_le_sum (fun k _ => hDk k)
      _ = (∑ k : Fin 3, (Md * ‖Submission.BoseGases.kcDir (n + 1) i k‖) ^ 2) * V := by
          rw [Finset.sum_mul]
  calc |Work.BoseKinLoc.fsT ℓ d s εT b 0 ψ|
      ≤ C * ((∫ z : EuclideanSpace ℝ (Fin 3), (ψ z) ^ 2)
          + ∑ k : Fin 3, ∫ z : EuclideanSpace ℝ (Fin 3),
              (fderiv ℝ ψ z (Submission.BoseGases.kcStdBasis k)) ^ 2) := hbd
    _ ≤ C * (MΦ ^ 2 * V
          + (∑ k : Fin 3, (Md * ‖Submission.BoseGases.kcDir (n + 1) i k‖) ^ 2) * V) :=
        mul_le_mul_of_nonneg_left (add_le_add hA hD) hC0

/-! ## 3. Monotonicity and emptiness of the boxes -/

/-- `acube L ⊆ acube (max L ℓ)`, with no sign hypothesis on `L`. -/
private lemma acube_subset_acube_max_gen (L ℓ : ℝ) :
    Submission.BoseGases.acube L ⊆ Submission.BoseGases.acube (max L ℓ) := by
  intro y hy
  rw [Submission.BoseGases.mem_acube_iff] at hy ⊢
  intro m
  have h := hy m
  rw [Set.mem_Icc] at h ⊢
  exact ⟨by linarith [h.1, le_max_left L ℓ], by linarith [h.2, le_max_left L ℓ]⟩

/-- The centred cube is empty for a negative side length. -/
private lemma acube_eq_empty_of_neg {ℓ : ℝ} (hℓ : ℓ < 0) : Submission.BoseGases.acube ℓ = ∅ := by
  refine Set.eq_empty_iff_forall_notMem.mpr fun y hy => ?_
  rw [Submission.BoseGases.mem_acube_iff] at hy
  have h := hy 0
  rw [Set.mem_Icc] at h
  linarith [h.1, h.2, hℓ]

/-! ## 4. The support of the slot-`i` kinetic integrand -/

/-- **The slot-`i` kinetic integrand vanishes off `abox N (max L ℓ)`.**  If some slot `j` of the
configuration `x` leaves `acube (max L ℓ)`, then either `j = i`, in which case the box indicator
`indU ℓ 0 (xᵢ)` vanishes (`acube ℓ ⊆ acube (max L ℓ)`), or `j ≠ i`, in which case the fibre
`z ↦ Ψ (x with xᵢ = z)` is identically zero (its `j`-th slot is always `x_j ∉ acube L`), so `fsT`
of it vanishes by `Word.fsT_zero`. -/
private lemma indU_mul_fsT_fibre_eq_zero_of_notMem_abox_max {N : ℕ} {ℓ L d s εT b : ℝ}
    (hℓ : 0 < ℓ) {Ψ : Submission.BoseGases.X N → ℝ}
    (hsupp : tsupport Ψ ⊆ Submission.BoseGases.abox N L)
    {x : Submission.BoseGases.X N} (hx : x ∉ Submission.BoseGases.abox N (max L ℓ)) (i : Fin N) :
    Work.BoseKinLoc.indU ℓ 0 (x i)
      * Work.BoseKinLoc.fsT ℓ d s εT b 0 (Work.BoseKinLoc.fibre N i Ψ x) = 0 := by
  obtain ⟨j, hj⟩ : ∃ j : Fin N, x j ∉ Submission.BoseGases.acube (max L ℓ) := by
    by_contra h
    exact hx fun k => not_not.mp (not_exists.mp h k)
  by_cases hji : j = i
  · rw [hji] at hj
    have hnot : x i ∉ Work.BoseKinLoc.lamBox ℓ 0 := by
      intro hc
      exact hj (Submission.BoseGases.acube_mono hℓ.le (le_max_right L ℓ)
        (by simpa [Work.BoseKinLoc.lamBox, Work.BSKinetic.bsBox] using hc))
    rw [show Work.BoseKinLoc.indU ℓ 0 (x i) = 0 from Set.indicator_of_notMem hnot _, zero_mul]
  · have hfib : Work.BoseKinLoc.fibre N i Ψ x = 0 := by
      funext z
      show Ψ (Function.update x i z) = 0
      refine Work.BoseKinLoc.Word.eq_zero_of_not_mem_abox hsupp ?_
      intro hmem
      have hcoord : x j ∈ Submission.BoseGases.acube L := by
        have h := hmem j
        rwa [Function.update_of_ne hji z x] at h
      exact hj (acube_subset_acube_max_gen L ℓ hcoord)
    rw [hfib, Work.BoseKinLoc.Word.fsT_zero hℓ, mul_zero]

/-! ## 5. Measurability of the integrand -/

/-- The box indicator `indU ℓ 0 q.1` is measurable on `ℝ³ × X n`. -/
private lemma measurable_indU_fst_zero (ℓ : ℝ) {n : ℕ} :
    Measurable (fun q : EuclideanSpace ℝ (Fin 3) × Submission.BoseGases.X n =>
      Work.BoseKinLoc.indU ℓ 0 q.1) := by
  have h1 : Measurable (fun y : EuclideanSpace ℝ (Fin 3) => Work.BoseKinLoc.indU ℓ 0 y) := by
    have h : Work.BoseKinLoc.indU ℓ 0
        = (Work.BoseKinLoc.lamBox ℓ 0).indicator (fun _ => (1 : ℝ)) := rfl
    rw [h]
    exact measurable_const.indicator (Work.BoseKinLoc.Word.measurableSet_lamBox ℓ 0)
  exact h1.comp measurable_fst

/-- The fibre of a re-inserted configuration is the `genFibre` (the fibre does not see the
inserted coordinate). -/
private lemma fibre_kcInsN_eq_genFibre {n : ℕ} (i : Fin (n + 1))
    (Ψ : Submission.BoseGases.X (n + 1) → ℝ) (y : EuclideanSpace ℝ (Fin 3))
    (r : Submission.BoseGases.X n) :
    Work.BoseKinLoc.fibre (n + 1) i Ψ (Submission.BoseGases.kcInsN n i (y, r))
      = Work.BoseKinLoc.Kinetic.genFibre i Ψ r := by
  funext z
  exact (Work.BoseKinLoc.Kinetic.genFibre_eq_fibre i Ψ r y z).symm

/-- **The anchored fibre word is a.e. strongly measurable in the remaining configuration.**
Assembled from the four word lemmas; for `d = 0` the two words `neuWord` and `momWord` carry the
vanishing factor `(dℓ)⁻²` and drop out. -/
private lemma fsT_fibre_zero_aemeasurable {n : ℕ} {ℓ L d s εT b : ℝ} (hℓ : 0 < ℓ) (hL : 0 ≤ L)
    {Ψ : Submission.BoseGases.X (n + 1) → ℝ} (hΨ : ContDiff ℝ (⊤ : ENat) Ψ)
    (hsupp : tsupport Ψ ⊆ Submission.BoseGases.abox (n + 1) L) (i : Fin (n + 1)) :
    MeasureTheory.AEStronglyMeasurable
      (fun r : Submission.BoseGases.X n =>
        Work.BoseKinLoc.fsT ℓ d s εT b 0 (Work.BoseKinLoc.Kinetic.genFibre i Ψ r))
      MeasureTheory.volume := by
  have hgap := aemeasurable_gapWord_zero_fibre (ℓ := ℓ) (b := b) (L := L) hℓ hL hΨ hsupp i
  have hmain := aemeasurable_mainWord_zero_fibre (ℓ := ℓ) (d := d) (s := s) (εT := εT) (L := L)
    hℓ hL hΨ hsupp i
  by_cases hd : d = 0
  · have hsum : (fun r : Submission.BoseGases.X n =>
          Work.BoseKinLoc.fsT ℓ d s εT b 0 (Work.BoseKinLoc.Kinetic.genFibre i Ψ r))
        = fun r => (0 : ℝ)
            + Work.BoseKinLoc.gapWord ℓ b 0 (Work.BoseKinLoc.Kinetic.genFibre i Ψ r)
            + 0 + Work.BoseKinLoc.mainWord ℓ d s εT 0
                (Work.BoseKinLoc.Kinetic.genFibre i Ψ r) := by
      funext r
      rw [Work.BoseKinLoc.fsT_eq_sum, hd]
      simp [Work.BoseKinLoc.neuWord, Work.BoseKinLoc.momWord]
    rw [hsum]
    exact ((aestronglyMeasurable_const.add hgap).add aestronglyMeasurable_const).add hmain
  · have hneu := aemeasurable_neuWord_zero_fibre (ℓ := ℓ) (d := d) (εT := εT) (L := L)
      hℓ hd hL hΨ hsupp i
    have hmom := aemeasurable_momWord_zero_fibre (ℓ := ℓ) (d := d) (εT := εT) (b := b) (L := L)
      hℓ hL hΨ hsupp i
    have hsum : (fun r : Submission.BoseGases.X n =>
          Work.BoseKinLoc.fsT ℓ d s εT b 0 (Work.BoseKinLoc.Kinetic.genFibre i Ψ r))
        = fun r => Work.BoseKinLoc.neuWord ℓ d εT 0 (Work.BoseKinLoc.Kinetic.genFibre i Ψ r)
            + Work.BoseKinLoc.gapWord ℓ b 0 (Work.BoseKinLoc.Kinetic.genFibre i Ψ r)
            + Work.BoseKinLoc.momWord ℓ d εT b 0 (Work.BoseKinLoc.Kinetic.genFibre i Ψ r)
            + Work.BoseKinLoc.mainWord ℓ d s εT 0
                (Work.BoseKinLoc.Kinetic.genFibre i Ψ r) := by
      funext r
      rw [Work.BoseKinLoc.fsT_eq_sum]
    rw [hsum]
    exact ((hneu.add hgap).add hmom).add hmain

/-! ## 6. The target -/

/-- **The slot-`i` kinetic integrand is integrable.**  For a smooth state `Ψ` with
`tsupport Ψ ⊆ abox N L`, the whole-space integrand
`x ↦ indU ℓ 0 (xᵢ) · fsT ℓ d s εT b 0 (fibre N i Ψ x)` of the slot-`i` lifting `slotForm`
(`0 < ℓ`) is integrable.  It is measurable (each of the four words of `fsT` is measurable along the
fibre family) and vanishes off `abox N (max L ℓ)`: if a slot `j` of `x` leaves `acube (max L ℓ)`
then either `j = i`, where `indU ℓ 0 (xᵢ)` vanishes (`acube ℓ ⊆ acube (max L ℓ)`), or `j ≠ i`,
where the fibre `z ↦ Ψ (x with xᵢ = z)` is identically zero (its `j`-th slot is `x_j ∉ acube L`), so
`fsT 0 = 0` (`Work.BoseKinLoc.Word.fsT_zero`).  That set has finite measure, and the integrand is
bounded by `C · (∫ (fibre)² + Σ_k ∫ (∂_k fibre)²) ≤ C · M` with `M` depending only on `Ψ, ℓ`
(`Work.BoseKinLoc.Kinetic.fsT_H1_bound_all`; the fibre is supported in `acube L` and its `L²`-norm
and Dirichlet energy are bounded uniformly in `x`).  The support tools are in
`Submission.Work.BoseKinLoc.Word.boxFormB_eq_boxForm_of_supp`.  Namespace `Work.BoseKinLoc.Sector`;
imports: Mathlib, `Submission.Work.BoseKinLoc.Defs`,
`Submission.Work.BoseKinLoc.Sector.fibre_defs_v3`,
`Submission.Work.BoseKinLoc.Sector.fsT_box_invariant`,
`Submission.Work.BoseKinLoc.Sector.fsT_bound_all`,
`Submission.Work.BoseKinLoc.Word.boxFormB_eq_boxForm_of_supp`,
`Submission.Work.PerSector.FibreResidual`. -/
theorem integrable_indU_mul_fsT_fibre_anyL {N : ℕ} {ℓ L d s εT b : ℝ} (hℓ : 0 < ℓ)
    {Ψ : Submission.BoseGases.X N → ℝ} (hΨ : ContDiff ℝ (⊤ : ENat) Ψ)
    (hsupp : tsupport Ψ ⊆ Submission.BoseGases.abox N L) (i : Fin N) :
    MeasureTheory.Integrable (fun x : Submission.BoseGases.X N =>
        Work.BoseKinLoc.indU ℓ 0 (x i)
          * Work.BoseKinLoc.fsT ℓ d s εT b 0 (Work.BoseKinLoc.fibre N i Ψ x)) := by
  rcases N with _ | n
  · exact i.elim0
  by_cases hL : 0 ≤ L
  · -- ## the genuine case: the support radius is nonnegative
    obtain ⟨M, hM0, hMbd⟩ := bound_fsT_genFibre_zero_aux (ℓ := ℓ) (L := L) (d := d) (s := s)
      (εT := εT) (b := b) hℓ hL hΨ hsupp i
    set H : Submission.BoseGases.X (n + 1) → ℝ := fun x =>
      Work.BoseKinLoc.indU ℓ 0 (x i)
        * Work.BoseKinLoc.fsT ℓ d s εT b 0 (Work.BoseKinLoc.fibre (n + 1) i Ψ x) with hH
    -- ## measurability
    have hFmeas := fsT_fibre_zero_aemeasurable (ℓ := ℓ) (L := L) (d := d) (s := s) (εT := εT)
      (b := b) hℓ hL hΨ hsupp i
    have hAEM : AEMeasurable
        (fun q : EuclideanSpace ℝ (Fin 3) × Submission.BoseGases.X n =>
          Work.BoseKinLoc.indU ℓ 0 q.1
            * Work.BoseKinLoc.fsT ℓ d s εT b 0 (Work.BoseKinLoc.Kinetic.genFibre i Ψ q.2))
        (MeasureTheory.volume : MeasureTheory.Measure
          (EuclideanSpace ℝ (Fin 3) × Submission.BoseGases.X n)) := by
      have h1 : AEMeasurable
          (fun q : EuclideanSpace ℝ (Fin 3) × Submission.BoseGases.X n =>
            Work.BoseKinLoc.fsT ℓ d s εT b 0 (Work.BoseKinLoc.Kinetic.genFibre i Ψ q.2))
          (MeasureTheory.volume : MeasureTheory.Measure
            (EuclideanSpace ℝ (Fin 3) × Submission.BoseGases.X n)) :=
        hFmeas.aemeasurable.comp_snd
      have h2 : AEMeasurable
          (fun q : EuclideanSpace ℝ (Fin 3) × Submission.BoseGases.X n =>
            Work.BoseKinLoc.indU ℓ 0 q.1)
          (MeasureTheory.volume : MeasureTheory.Measure
            (EuclideanSpace ℝ (Fin 3) × Submission.BoseGases.X n)) :=
        (measurable_indU_fst_zero ℓ).aemeasurable
      exact h2.mul h1
    have hHmeas : AEMeasurable H MeasureTheory.volume := by
      have hpt : ∀ q : EuclideanSpace ℝ (Fin 3) × Submission.BoseGases.X n,
          (H ∘ ⇑(Submission.BoseGases.kcInsN n i)) q
            = Work.BoseKinLoc.indU ℓ 0 q.1
              * Work.BoseKinLoc.fsT ℓ d s εT b 0
                  (Work.BoseKinLoc.Kinetic.genFibre i Ψ q.2) := by
        intro q
        obtain ⟨y, r⟩ := q
        simp only [Function.comp_apply, hH, Submission.BoseGases.kc_insN_apply_same]
        rw [fibre_kcInsN_eq_genFibre]
      have hcomp : AEMeasurable (H ∘ ⇑(Submission.BoseGases.kcInsN n i))
          (MeasureTheory.volume : MeasureTheory.Measure
            (EuclideanSpace ℝ (Fin 3) × Submission.BoseGases.X n)) :=
        hAEM.congr (Filter.Eventually.of_forall fun q => (hpt q).symm)
      exact ((Submission.BoseGases.kc_mp_insN n i).aemeasurable_comp_iff
        (Submission.BoseGases.kcInsN n i).measurableEmbedding).mp hcomp
    -- ## the uniform bound
    have hbound : ∀ x : Submission.BoseGases.X (n + 1), ‖H x‖ ≤ M := by
      intro x
      set q : EuclideanSpace ℝ (Fin 3) × Submission.BoseGases.X n :=
        (Submission.BoseGases.kcInsN n i).symm x with hq
      have hx : x = Submission.BoseGases.kcInsN n i (q.1, q.2) := by
        rw [hq]
        exact ((Submission.BoseGases.kcInsN n i).apply_symm_apply x).symm
      rw [hx, hH]
      simp only [Submission.BoseGases.kc_insN_apply_same]
      rw [fibre_kcInsN_eq_genFibre]
      have hind : |Work.BoseKinLoc.indU ℓ 0 q.1| ≤ 1 := by
        by_cases h : q.1 ∈ Work.BoseKinLoc.lamBox ℓ 0
        · rw [Work.BoseKinLoc.indU, Set.indicator_of_mem h]; norm_num
        · rw [Work.BoseKinLoc.indU, Set.indicator_of_notMem h]; norm_num
      calc ‖Work.BoseKinLoc.indU ℓ 0 q.1
            * Work.BoseKinLoc.fsT ℓ d s εT b 0 (Work.BoseKinLoc.Kinetic.genFibre i Ψ q.2)‖
          = |Work.BoseKinLoc.indU ℓ 0 q.1|
              * |Work.BoseKinLoc.fsT ℓ d s εT b 0
                  (Work.BoseKinLoc.Kinetic.genFibre i Ψ q.2)| := by
            rw [Real.norm_eq_abs, abs_mul]
        _ ≤ 1 * M := mul_le_mul hind (hMbd q.2) (abs_nonneg _) (by norm_num)
        _ = M := one_mul M
    -- ## the support
    have hsuppH : Function.support H ⊆ Submission.BoseGases.abox (n + 1) (max L ℓ) := by
      intro x hx
      by_contra hx'
      exact hx (indU_mul_fsT_fibre_eq_zero_of_notMem_abox_max hℓ hsupp hx' i)
    -- ## assembly
    rw [← MeasureTheory.integrableOn_iff_integrable_of_support_subset hsuppH]
    refine MeasureTheory.IntegrableOn.of_bound ?_ ?_ M (Filter.Eventually.of_forall hbound)
    · exact Submission.BoseGases.abox_lt_top (n + 1) (max L ℓ)
        (le_trans hL (le_max_left L ℓ))
    · exact hHmeas.aestronglyMeasurable.mono_measure MeasureTheory.Measure.restrict_le_self
  · -- ## the degenerate case: the box is empty, so the state and the integrand vanish
    have hLneg : L < 0 := lt_of_not_ge hL
    have hΨ0 : ∀ x : Submission.BoseGases.X (n + 1), Ψ x = 0 := fun x => by
      by_contra h
      have hmem : x ∈ Submission.BoseGases.abox (n + 1) L :=
        hsupp (subset_tsupport Ψ (Function.mem_support.mpr h))
      rw [Submission.BoseGases.mem_abox_iff] at hmem
      have hc : x i ∈ Submission.BoseGases.acube L := hmem i
      rw [acube_eq_empty_of_neg hLneg] at hc
      exact hc
    have hzero : (fun x : Submission.BoseGases.X (n + 1) =>
        Work.BoseKinLoc.indU ℓ 0 (x i)
          * Work.BoseKinLoc.fsT ℓ d s εT b 0 (Work.BoseKinLoc.fibre (n + 1) i Ψ x))
        = fun _ => (0 : ℝ) := by
      funext x
      have hfib : Work.BoseKinLoc.fibre (n + 1) i Ψ x = 0 :=
        funext fun z => hΨ0 (Function.update x i z)
      rw [hfib, Work.BoseKinLoc.Word.fsT_zero hℓ, mul_zero]
    rw [hzero]
    exact MeasureTheory.integrable_zero (Submission.BoseGases.X (n + 1)) ℝ MeasureTheory.volume

end Work.BoseKinLoc.Sector
