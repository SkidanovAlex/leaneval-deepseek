/-
# `ℓ¹(ℤ²)`-mass facts for the §6 small-scale kernels (Area A7)

This module collects the elementary facts from which the finiteness statements for the two §6
kernels

* `smallKconc ρ P l₁ l₂ k₁ k₂ N` (the *concrete* column, `kernComp (khalf N P) κ κ'`), and
* `smallKmod ρ P l₁ l₂ k₁ k₂ N` (the `t`-integral of the *model* column)

are assembled, together with the two kernel-mass bookkeeping lemmas of
`Work.KMTAreas.A7.smallKernelMass_le`:

1. the criterion `smKernMass K ≠ ⊤ ↔ Summable (fun p : ℤ × ℤ => ‖K p.1 p.2‖)` and its
   `ENNReal.ofReal` form, plus the two elementary consequences (product kernels, finite sums of
   kernels);
2. quadratic decay and absolute summability of the Fourier coefficients `cw m j = ∫ m(θ)e(-jθ)dθ`
   of a `C²` compactly supported bump `m` (`Work.KMTAreas.A7.FourierDecayExplicit` combined with
   `cw_eq_fourierTransform`), with the specialisations to the §6 bumps `varphiN N k`,
   `varphitildeN d N k`, the modulated `varphiNt N k t`, `varphitildeNt P d N k t`, and the two
   tensor factors `mStarF u`, `mStargF d u`;
3. quadratic decay and absolute summability of the exact-height Ionescu--Wainger kernel
   `tmKernel ρ l F = iwKernel (iwSymbolSet (diffFreqs ρ l) (periodize F))` of a bump `F`
   (`Work.KMTAreas.A7.iwKernel_decay_of_bump`), *uniformly in `t ∈ [1/2,1]`* for the modulated
   bumps `varphiNt N k t`, `varphitildeNt P d N k t` — this is what makes the `t`-integral of
   `smallKmod` controllable;
4. finiteness of the mass of the halved-average kernel `khalf m P` (finite support).
-/
import Mathlib
import Submission.Work.KMTAreas.A7.smallKernelMass_le

/-! ## Integration note (owner of area A6, H61)

`tmKernel_varphitildeNt_decay` is also declared, with the *opposite* argument order
`(P) (ρ) (l N k)`, in `Submission/Work/KMTAreas/A7/tmKernel_varphitildeNt_decay.lean`, which this
module imports (through `smallKernelMass_le`).  The two names collided here and made this module
unbuildable for every downstream file, so the copy below was renamed
`tmKernel_varphitildeNt_decay_rho_first`; its only consumer outside this module is
`Work.KMTAreas.A7.SmallKernMassModel` (line 241), updated accordingly.  Semantics unchanged. -/

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace Work.KMTAreas.A7

noncomputable section

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal BigOperators FourierTransform
open Work.Analysis.IonescuWainger Work.Analysis.IWMultiplier

/-! ## 1. Finiteness criteria for the kernel mass -/

/-- **Finiteness criterion.** The extended-real `ℓ¹(ℤ²)`-mass `smKernMass K` is finite precisely
when the real-valued `ℓ¹`-norm of `K` is summable. -/
theorem smKernMass_ne_top_iff_summable (K : ℤ → ℤ → ℂ) :
    smKernMass K ≠ ⊤ ↔ Summable (fun p : ℤ × ℤ => ‖K p.1 p.2‖) := by
  have h1 : smKernMass K = ∑' p : ℤ × ℤ, ((‖K p.1 p.2‖₊ : ℝ≥0) : ℝ≥0∞) := rfl
  rw [h1, ENNReal.tsum_coe_ne_top_iff_summable]
  constructor
  · intro h
    have h' : Summable fun p : ℤ × ℤ => ((‖K p.1 p.2‖₊ : ℝ≥0) : ℝ) := NNReal.summable_coe.mpr h
    simpa using h'
  · intro h
    have h' : Summable fun p : ℤ × ℤ => ((‖K p.1 p.2‖₊ : ℝ≥0) : ℝ) := by simpa using h
    exact NNReal.summable_coe.mp h'

/-- The finite-mass statement in the form in which the §6 estimates produce it. -/
theorem smKernMass_ne_top_of_summable {K : ℤ → ℤ → ℂ}
    (h : Summable fun p : ℤ × ℤ => ‖K p.1 p.2‖) : smKernMass K ≠ ⊤ :=
  (smKernMass_ne_top_iff_summable K).mpr h

/-- The extended-real mass of a summable kernel is the coercion of its real `ℓ¹`-norm. -/
theorem smKernMass_eq_ofReal_tsum {K : ℤ → ℤ → ℂ}
    (h : Summable fun p : ℤ × ℤ => ‖K p.1 p.2‖) :
    smKernMass K = ENNReal.ofReal (∑' p : ℤ × ℤ, ‖K p.1 p.2‖) := by
  have hnn : Summable fun p : ℤ × ℤ => ‖K p.1 p.2‖₊ :=
    NNReal.summable_coe.mp (by simpa using h)
  have hcoe : ((∑' p : ℤ × ℤ, ‖K p.1 p.2‖₊ : ℝ≥0) : ℝ) = ∑' p : ℤ × ℤ, ‖K p.1 p.2‖ := by
    rw [NNReal.coe_tsum]
    exact tsum_congr fun p => by simp
  calc smKernMass K = (↑(∑' p : ℤ × ℤ, ‖K p.1 p.2‖₊) : ℝ≥0∞) := by
        rw [show smKernMass K = ∑' p : ℤ × ℤ, ((‖K p.1 p.2‖₊ : ℝ≥0) : ℝ≥0∞) from rfl,
          ENNReal.coe_tsum hnn]
    _ = ENNReal.ofReal (∑' p : ℤ × ℤ, ‖K p.1 p.2‖) := by
        rw [← hcoe, ENNReal.ofReal_coe_nnreal]

/-- A bound on the real `ℓ¹`-norm gives a bound on the extended-real mass. -/
theorem smKernMass_le_ofReal_tsum {K : ℤ → ℤ → ℂ} {B : ℝ}
    (h : Summable fun p : ℤ × ℤ => ‖K p.1 p.2‖)
    (hB : (∑' p : ℤ × ℤ, ‖K p.1 p.2‖) ≤ B) :
    smKernMass K ≤ ENNReal.ofReal B :=
  (le_of_eq (smKernMass_eq_ofReal_tsum h)).trans (ENNReal.ofReal_le_ofReal hB)

/-- **The mass of a product kernel.** -/
theorem smKernMass_prod_le {f g : ℤ → ℂ}
    (hf : Summable fun x : ℤ => ‖f x‖) (hg : Summable fun y : ℤ => ‖g y‖) :
    smKernMass (fun a b : ℤ => f a * g b)
      ≤ ENNReal.ofReal ((∑' x : ℤ, ‖f x‖) * (∑' y : ℤ, ‖g y‖)) := by
  have hsum : Summable fun p : ℤ × ℤ => ‖f p.1 * g p.2‖ := hf.mul_norm hg
  have hfg : Summable fun p : ℤ × ℤ => ‖f p.1‖ * ‖g p.2‖ :=
    hf.mul_of_nonneg hg (fun x => norm_nonneg _) (fun y => norm_nonneg _)
  refine smKernMass_le_ofReal_tsum hsum ?_
  calc (∑' p : ℤ × ℤ, ‖f p.1 * g p.2‖) ≤ ∑' p : ℤ × ℤ, ‖f p.1‖ * ‖g p.2‖ :=
        Summable.tsum_le_tsum (fun p => norm_mul_le _ _) hsum hfg
    _ = (∑' x : ℤ, ‖f x‖) * (∑' y : ℤ, ‖g y‖) :=
        (tsum_mul_tsum_of_summable_norm (f := fun x : ℤ => ‖f x‖)
          (g := fun y : ℤ => ‖g y‖) (by simpa using hf) (by simpa using hg)).symm

/-- Interchange of an `ℝ≥0∞`-valued sum with a finite sum. -/
theorem tsum_finset_sum_enorm {ι α : Type*} (s : Finset ι) (f : ι → α → ℝ≥0∞) :
    (∑' a, ∑ i ∈ s, f i a) = ∑ i ∈ s, ∑' a, f i a := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert i s hi ih =>
      rw [Finset.sum_insert hi, ← ih, ← ENNReal.tsum_add]
      exact tsum_congr fun a => Finset.sum_insert hi

/-- **The mass of a finite sum of kernels.** -/
theorem smKernMass_finset_sum_le {ι : Type*} (s : Finset ι) (F : ι → ℤ → ℤ → ℂ) (B : ι → ℝ)
    (hB : ∀ i ∈ s, 0 ≤ B i) (h : ∀ i ∈ s, smKernMass (F i) ≤ ENNReal.ofReal (B i)) :
    smKernMass (fun a b => ∑ i ∈ s, F i a b) ≤ ENNReal.ofReal (∑ i ∈ s, B i) := by
  rw [smKernMass]
  calc (∑' p : ℤ × ℤ, ‖∑ i ∈ s, F i p.1 p.2‖ₑ)
      ≤ ∑' p : ℤ × ℤ, ∑ i ∈ s, ‖F i p.1 p.2‖ₑ :=
        ENNReal.tsum_le_tsum fun p : ℤ × ℤ => enorm_sum_le s fun i => F i p.1 p.2
    _ = ∑ i ∈ s, ∑' p : ℤ × ℤ, ‖F i p.1 p.2‖ₑ :=
        tsum_finset_sum_enorm s fun i (p : ℤ × ℤ) => ‖F i p.1 p.2‖ₑ
    _ = ∑ i ∈ s, smKernMass (F i) := rfl
    _ ≤ ∑ i ∈ s, ENNReal.ofReal (B i) := Finset.sum_le_sum h
    _ = ENNReal.ofReal (∑ i ∈ s, B i) := (ENNReal.ofReal_sum_of_nonneg hB).symm

/-- **Finiteness of the mass of a `cw`-dominated kernel.**  If `‖K j₁ j₂‖` is dominated by
`B · ‖cw m₁ j₁‖ · ‖cw m₂ j₂‖` with the two coefficient families `ℓ¹`, then the mass of `K` is
bounded by `B (∑_j ‖cw m₁ j‖)(∑_j ‖cw m₂ j‖)`. -/
theorem smKernMass_le_of_cw_dominated {K : ℤ → ℤ → ℂ} {m₁ m₂ : ℝ → ℂ} {B : ℝ}
    (h : ∀ j₁ j₂ : ℤ, ‖K j₁ j₂‖ ≤ B * ‖cw m₁ j₁‖ * ‖cw m₂ j₂‖)
    (h₁ : Summable fun j : ℤ => ‖cw m₁ j‖) (h₂ : Summable fun j : ℤ => ‖cw m₂ j‖) :
    smKernMass K ≤ ENNReal.ofReal (B * (∑' j : ℤ, ‖cw m₁ j‖) * (∑' j : ℤ, ‖cw m₂ j‖)) := by
  have hsum : Summable fun p : ℤ × ℤ => ‖cw m₁ p.1‖ * ‖cw m₂ p.2‖ :=
    h₁.mul_of_nonneg h₂ (fun x => norm_nonneg _) (fun y => norm_nonneg _)
  have hK : Summable fun p : ℤ × ℤ => ‖K p.1 p.2‖ := by
    refine Summable.of_nonneg_of_le (fun p => norm_nonneg _) (fun p => ?_)
      (hsum.mul_left B)
    calc ‖K p.1 p.2‖ ≤ B * ‖cw m₁ p.1‖ * ‖cw m₂ p.2‖ := h p.1 p.2
      _ = B * (‖cw m₁ p.1‖ * ‖cw m₂ p.2‖) := mul_assoc _ _ _
  refine smKernMass_le_ofReal_tsum hK ?_
  calc (∑' p : ℤ × ℤ, ‖K p.1 p.2‖)
      ≤ ∑' p : ℤ × ℤ, B * (‖cw m₁ p.1‖ * ‖cw m₂ p.2‖) :=
        Summable.tsum_le_tsum (fun p => le_of_le_of_eq (h p.1 p.2) (mul_assoc _ _ _)) hK
          (hsum.mul_left B)
    _ = B * ∑' p : ℤ × ℤ, ‖cw m₁ p.1‖ * ‖cw m₂ p.2‖ := tsum_mul_left
    _ = B * ((∑' j : ℤ, ‖cw m₁ j‖) * (∑' j : ℤ, ‖cw m₂ j‖)) := by
        rw [show (∑' p : ℤ × ℤ, ‖cw m₁ p.1‖ * ‖cw m₂ p.2‖)
              = (∑' j : ℤ, ‖cw m₁ j‖) * (∑' j : ℤ, ‖cw m₂ j‖) from
            (tsum_mul_tsum_of_summable_norm (f := fun j : ℤ => ‖cw m₁ j‖)
              (g := fun j : ℤ => ‖cw m₂ j‖) (by simpa using h₁) (by simpa using h₂)).symm]
    _ = B * (∑' j : ℤ, ‖cw m₁ j‖) * (∑' j : ℤ, ‖cw m₂ j‖) := (mul_assoc _ _ _).symm

/-- **Finiteness of a single `ℓ¹(ℤ)`-sum of extended norms.** -/
theorem tsum_enorm_ne_top_of_summable {ι : Type*} {E : Type*} [SeminormedAddCommGroup E]
    {f : ι → E} (h : Summable fun i => ‖f i‖) : (∑' i, ‖f i‖ₑ) ≠ ⊤ := by
  rw [show (∑' i, ‖f i‖ₑ) = ∑' i, ((‖f i‖₊ : ℝ≥0) : ℝ≥0∞) from rfl,
    ENNReal.tsum_coe_ne_top_iff_summable]
  exact NNReal.summable_coe.mp (by simpa using h)

/-! ## 2. The Fourier coefficients `cw` of a `C²` compactly supported bump -/

/-- **Absolute summability of the coefficients `cw m` of a `C²` compactly supported bump.** -/
theorem summable_cw_of_contDiff_hasCompactSupport {m : ℝ → ℂ} (hcd : ContDiff ℝ 2 m)
    (hcs : HasCompactSupport m) : Summable fun j : ℤ => ‖cw m j‖ := by
  have h := FourierDecayExplicit hcd hcs
  refine Summable.of_nonneg_of_le (fun j => norm_nonneg _) (fun j => ?_)
    (summable_kmtKernWeight.mul_left
      (4 * max (∫ y, ‖m y‖) (∫ y, ‖iteratedDeriv 2 m y‖) + 1))
  rw [cw_eq_fourierTransform, norm_kmtKernWeight, mul_one_div]
  exact h (j : ℝ)

/-- **The explicit `ℓ¹`-bound for `cw m`** in terms of a bound `S` on `∫‖m‖` and `∫‖m''‖`. -/
theorem tsum_cw_le {m : ℝ → ℂ} (hcd : ContDiff ℝ 2 m) (hcs : HasCompactSupport m) {S : ℝ}
    (hS : 0 ≤ S) (h1 : (∫ y, ‖m y‖) ≤ S) (h2 : (∫ y, ‖iteratedDeriv 2 m y‖) ≤ S) :
    (∑' j : ℤ, ‖cw m j‖) ≤ (4 * S + 1) * (∑' j : ℤ, ‖kmtKernWeight j‖) := by
  have hbase : Summable fun j : ℤ => ‖cw m j‖ :=
    summable_cw_of_contDiff_hasCompactSupport hcd hcs
  have hC : (4 * max (∫ y, ‖m y‖) (∫ y, ‖iteratedDeriv 2 m y‖) + 1) ≤ 4 * S + 1 := by
    have := max_le h1 h2; linarith
  have hbound : ∀ j : ℤ, ‖cw m j‖ ≤ (4 * S + 1) * ‖kmtKernWeight j‖ := by
    intro j
    calc ‖cw m j‖
        ≤ (4 * max (∫ y, ‖m y‖) (∫ y, ‖iteratedDeriv 2 m y‖) + 1) * ‖kmtKernWeight j‖ := by
          rw [cw_eq_fourierTransform, norm_kmtKernWeight, mul_one_div]
          exact FourierDecayExplicit hcd hcs (j : ℝ)
      _ ≤ (4 * S + 1) * ‖kmtKernWeight j‖ :=
          mul_le_mul_of_nonneg_right hC (norm_nonneg _)
  calc (∑' j : ℤ, ‖cw m j‖)
      ≤ ∑' j : ℤ, (4 * S + 1) * ‖kmtKernWeight j‖ :=
        Summable.tsum_le_tsum hbound hbase (summable_kmtKernWeight.mul_left _)
    _ = (4 * S + 1) * (∑' j : ℤ, ‖kmtKernWeight j‖) := tsum_mul_left

/-! ## 3. The bumps of §6 -/

/-- `C²` with compact support for the modulated `φ̃`. -/
theorem contDiff_varphitildeNt_aux (P : Polynomial ℤ) (d N k : ℕ) (t : ℝ) :
    ContDiff ℝ 2 (varphitildeNt P d N k t) := by
  rw [show varphitildeNt P d N k t
      = fun ξ : ℝ => varphitildeN d N k ξ * ee (PevalR P ((N : ℝ) * t) * ξ) from rfl]
  exact (contDiff_varphitildeN d N k).mul (contDiff_ee_const_mul 2 _)

/-- Compact support for the modulated `φ̃`. -/
theorem hasCompactSupport_varphitildeNt_aux (P : Polynomial ℤ) (d N k : ℕ) (t : ℝ) :
    HasCompactSupport (varphitildeNt P d N k t) := by
  rw [show varphitildeNt P d N k t
      = fun ξ : ℝ => varphitildeN d N k ξ * ee (PevalR P ((N : ℝ) * t) * ξ) from rfl]
  exact (hasCompactSupport_varphitildeN d N k).mul_right

theorem summable_cw_varphiN (N k : ℕ) :
    Summable fun j : ℤ => ‖cw (varphiN N k) j‖ :=
  summable_cw_of_contDiff_hasCompactSupport (contDiff_varphiN N k) (hasCompactSupport_varphiN N k)

theorem summable_cw_varphitildeN (d N k : ℕ) :
    Summable fun j : ℤ => ‖cw (varphitildeN d N k) j‖ :=
  summable_cw_of_contDiff_hasCompactSupport (contDiff_varphitildeN d N k)
    (hasCompactSupport_varphitildeN d N k)

theorem summable_cw_varphiNt (N k : ℕ) (t : ℝ) :
    Summable fun j : ℤ => ‖cw (varphiNt N k t) j‖ :=
  summable_cw_of_contDiff_hasCompactSupport (contDiff_varphiNt N k t)
    (hasCompactSupport_varphiNt N k t)

theorem summable_cw_varphitildeNt (P : Polynomial ℤ) (d N k : ℕ) (t : ℝ) :
    Summable fun j : ℤ => ‖cw (varphitildeNt P d N k t) j‖ :=
  summable_cw_of_contDiff_hasCompactSupport (contDiff_varphitildeNt_aux P d N k t)
    (hasCompactSupport_varphitildeNt_aux P d N k t)

/-- The coefficients of the tensor factor `m_* = η_{≤-2u}` are `ℓ¹`. -/
theorem summable_cw_mStarF (u : ℕ) : Summable fun j : ℤ => ‖cw (mStarF u) j‖ := by
  obtain ⟨C, hCpos, hC⟩ := cw_etaCut_decay (-(2 * (u : ℤ)))
  refine Summable.of_nonneg_of_le (fun j => norm_nonneg _) (fun j => ?_)
    (summable_kmtKernWeight.mul_left C)
  rw [norm_kmtKernWeight, mul_one_div]
  simpa only [mStarF] using hC j

/-- The coefficients of the tensor factor `η_{≤-2du}` are `ℓ¹`. -/
theorem summable_cw_mStargF (d u : ℕ) : Summable fun j : ℤ => ‖cw (mStargF d u) j‖ := by
  obtain ⟨C, hCpos, hC⟩ := cw_etaCut_decay (-((d : ℤ) * 2 * (u : ℤ)))
  refine Summable.of_nonneg_of_le (fun j => norm_nonneg _) (fun j => ?_)
    (summable_kmtKernWeight.mul_left C)
  rw [norm_kmtKernWeight, mul_one_div]
  simpa only [mStargF] using hC j

/-! ## 4. The Ionescu--Wainger kernel `tmKernel` of a bump -/

/-- **Quadratic decay of the exact-height IW kernel of a `C²` bump.**  This is
`Work.KMTAreas.A7.iwKernel_decay_of_bump` for the exact-height frequency set `diffFreqs ρ l`. -/
theorem tmKernel_decay_of_bump (ρ : ℝ) (l : ℕ) {F : ℝ → ℂ} (hFcd : ContDiff ℝ 2 F)
    (hFcs : HasCompactSupport F) {S : ℝ} (hSnn : 0 ≤ S) (h1 : (∫ y, ‖F y‖) ≤ S)
    (h2 : (∫ y, ‖iteratedDeriv 2 F y‖) ≤ S) :
    ∀ j : ℤ, ‖tmKernel ρ l F j‖ ≤ (4 * ((diffFreqs ρ l).card * S) + 1) * ‖kmtKernWeight j‖ :=
  iwKernel_decay_of_bump (diffFreqs ρ l) hFcd hFcs hSnn h1 h2

/-- Absolute summability of the exact-height IW kernel of a `C²` compactly supported bump. -/
theorem summable_tmKernel_of_bump (ρ : ℝ) (l : ℕ) {F : ℝ → ℂ} (hFcd : ContDiff ℝ 2 F)
    (hFcs : HasCompactSupport F) {S : ℝ} (hSnn : 0 ≤ S) (h1 : (∫ y, ‖F y‖) ≤ S)
    (h2 : (∫ y, ‖iteratedDeriv 2 F y‖) ≤ S) :
    Summable fun j : ℤ => ‖tmKernel ρ l F j‖ :=
  Summable.of_nonneg_of_le (fun j => norm_nonneg _)
    (tmKernel_decay_of_bump ρ l hFcd hFcs hSnn h1 h2)
    (summable_kmtKernWeight.mul_left (4 * ((diffFreqs ρ l).card * S) + 1))

theorem summable_tmKernel_varphiN (ρ : ℝ) (l N k : ℕ) :
    Summable fun j : ℤ => ‖tmKernel ρ l (varphiN N k) j‖ := by
  refine summable_tmKernel_of_bump ρ l (contDiff_varphiN N k) (hasCompactSupport_varphiN N k)
    (S := max (∫ y, ‖varphiN N k y‖) (∫ y, ‖iteratedDeriv 2 (varphiN N k) y‖)) ?_ ?_ ?_
  · exact le_max_of_le_left (integral_nonneg fun y => norm_nonneg _)
  · exact le_max_left _ _
  · exact le_max_right _ _

theorem summable_tmKernel_varphitildeN (ρ : ℝ) (l d N k : ℕ) :
    Summable fun j : ℤ => ‖tmKernel ρ l (varphitildeN d N k) j‖ := by
  refine summable_tmKernel_of_bump ρ l (contDiff_varphitildeN d N k)
    (hasCompactSupport_varphitildeN d N k)
    (S := max (∫ y, ‖varphitildeN d N k y‖)
      (∫ y, ‖iteratedDeriv 2 (varphitildeN d N k) y‖)) ?_ ?_ ?_
  · exact le_max_of_le_left (integral_nonneg fun y => norm_nonneg _)
  · exact le_max_left _ _
  · exact le_max_right _ _

/-- **The `t`-uniform quadratic decay of `tmKernel ρ l φ_{N,t}`** (the `φ`-side of §6). -/
theorem tmKernel_varphiNt_decay (ρ : ℝ) (l N k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Set.Icc (1/2 : ℝ) 1, ∀ j : ℤ,
      ‖tmKernel ρ l (varphiNt N k t) j‖ ≤ C * ‖kmtKernWeight j‖ := by
  obtain ⟨R, S, hSnn, hB⟩ := varphiNt_bounds N k
  refine ⟨4 * ((diffFreqs ρ l).card * S) + 1, ?_, ?_⟩
  · have : (0 : ℝ) ≤ ((diffFreqs ρ l).card : ℝ) * S := mul_nonneg (Nat.cast_nonneg _) hSnn
    linarith
  · intro t ht j
    obtain ⟨_, hcd, hcs, h1, h2⟩ := hB t ht
    exact tmKernel_decay_of_bump ρ l hcd hcs hSnn h1 h2 j

/-- **The `t`-uniform quadratic decay of `tmKernel ρ l φ̃_{N,t}`** (the `ψ`-side of §6).  The
modulation shifts the Fourier transform of `φ̃_N` by `c_t = P(Nt)`, which is bounded uniformly in
`t ∈ [1/2,1]`; the shifted decay is dominated by the unshifted one with the extra factor
`(2M+1)²` (`Work.KMTAreas.A7.one_div_sq_le_of_abs_sub_le`). -/
theorem tmKernel_varphitildeNt_decay_rho_first (ρ : ℝ) (P : Polynomial ℤ) (l d N k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Set.Icc (1/2 : ℝ) 1, ∀ j : ℤ,
      ‖tmKernel ρ l (varphitildeNt P d N k t) j‖ ≤ C * ‖kmtKernWeight j‖ := by
  obtain ⟨Cf, hCfpos, hCfdec⟩ := fourierDecay_varphitildeN d N k
  set Mv : ℝ := max 1 ((∑ i ∈ Finset.range (P.natDegree + 1), |(P.coeff i : ℝ)|) *
    (1 + (N : ℝ)) ^ P.natDegree) with hMv
  set K : ℝ := (2 * Mv + 1) ^ 2 with hK
  have hMnonneg : 0 ≤ Mv := le_trans zero_le_one (le_max_left 1 _)
  refine ⟨((diffFreqs ρ l).card : ℝ) * Cf * K, ?_, ?_⟩
  · have hcard : (0 : ℝ) ≤ ((diffFreqs ρ l).card : ℝ) := Nat.cast_nonneg _
    have hKpos : 0 < K := by rw [hK]; positivity
    exact mul_nonneg (mul_nonneg hcard hCfpos.le) hKpos.le
  · intro t ht j
    have ht1 : |t| ≤ 1 := by
      obtain ⟨h1, h2⟩ := ht
      rw [abs_le]
      exact ⟨by linarith, h2⟩
    have hc : |PevalR P ((N : ℝ) * t)| ≤ Mv :=
      le_trans (abs_PevalR_mul_le P N ht1) (le_max_right 1 _)
    have hid : tmKernel ρ l (varphitildeNt P d N k t) j
        = (∑ α ∈ diffFreqs ρ l, fourier (T := 1) (-j) α)
          * FourierTransform.fourier (varphitildeN d N k)
              ((j : ℝ) - PevalR P ((N : ℝ) * t)) := by
      rw [tmKernel, Work.KMTPlan.A6.IwKernelArithChar (diffFreqs ρ l)
        (integrable_varphitildeNt_aux P d N k t) j, cw_eq_fourierTransform,
        fourier_varphitildeNt_eq P d N k t (j : ℝ)]
    rw [hid, norm_mul]
    have h1 : ‖∑ α ∈ diffFreqs ρ l, fourier (T := 1) (-j) α‖ ≤ ((diffFreqs ρ l).card : ℝ) := by
      calc ‖∑ α ∈ diffFreqs ρ l, fourier (T := 1) (-j) α‖
          ≤ ∑ α ∈ diffFreqs ρ l, ‖fourier (T := 1) (-j) α‖ := norm_sum_le _ _
        _ = ∑ _α ∈ diffFreqs ρ l, (1 : ℝ) := by
            refine Finset.sum_congr rfl (fun α _ => ?_)
            rw [fourier_apply]
            exact _root_.Circle.norm_coe _
        _ = ((diffFreqs ρ l).card : ℝ) := by simp
    have h2 : ‖FourierTransform.fourier (varphitildeN d N k)
          ((j : ℝ) - PevalR P ((N : ℝ) * t))‖ ≤ Cf * K / (1 + |(j : ℝ)|) ^ 2 := by
      refine le_trans (hCfdec _) ?_
      calc Cf / (1 + |(j : ℝ) - PevalR P ((N : ℝ) * t)|) ^ 2
          = Cf * (1 / (1 + |(j : ℝ) - PevalR P ((N : ℝ) * t)|) ^ 2) := div_eq_mul_one_div _ _
        _ ≤ Cf * (K / (1 + |(j : ℝ)|) ^ 2) := by
            refine mul_le_mul_of_nonneg_left ?_ hCfpos.le
            rw [hK]
            exact one_div_sq_le_of_abs_sub_le hMnonneg hc j
        _ = Cf * K / (1 + |(j : ℝ)|) ^ 2 := (mul_div_assoc _ _ _).symm
    calc ‖∑ α ∈ diffFreqs ρ l, fourier (T := 1) (-j) α‖ *
            ‖FourierTransform.fourier (varphitildeN d N k)
              ((j : ℝ) - PevalR P ((N : ℝ) * t))‖
        ≤ ((diffFreqs ρ l).card : ℝ) * (Cf * K / (1 + |(j : ℝ)|) ^ 2) :=
          mul_le_mul h1 h2 (norm_nonneg _) (Nat.cast_nonneg _)
      _ = (((diffFreqs ρ l).card : ℝ) * Cf * K) * ‖kmtKernWeight j‖ := by
          rw [norm_kmtKernWeight]
          ring

/-! ## 5. The mass of the halved-average kernel -/

/-- **The halved-average kernel has finite `ℓ¹(ℤ²)`-mass**: its support is the graph of
`n ↦ P(n)` over the finite window `n ∈ (m/2, m]`. -/
theorem summable_khalf (m : ℕ) (P : Polynomial ℤ) :
    Summable fun p : ℤ × ℤ => ‖khalf m P p.1 p.2‖ := by
  let T : Finset (ℤ × ℤ) :=
    (Finset.range (m + 1)).image fun n : ℕ => ((n : ℤ), P.eval (n : ℤ))
  refine summable_of_hasFiniteSupport (T.finite_toSet.subset ?_)
  intro p hp
  have hne : khalf m P p.1 p.2 ≠ 0 := by
    simpa [Function.mem_support, norm_eq_zero] using hp
  have hcond : (m : ℤ) / 2 < p.1 ∧ p.1 ≤ (m : ℤ) ∧ p.2 = P.eval p.1 := by
    by_contra hc
    exact hne (by rw [khalf]; exact if_neg hc)
  obtain ⟨h1, h2, h3⟩ := hcond
  have hmnn : (0 : ℤ) ≤ (m : ℤ) / 2 := Int.ediv_nonneg (Int.natCast_nonneg m) (by norm_num)
  have hnn : 0 ≤ p.1 := le_of_lt (lt_of_le_of_lt hmnn h1)
  have hcast : ((p.1.toNat : ℕ) : ℤ) = p.1 := Int.toNat_of_nonneg hnn
  refine Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨p.1.toNat, ?_, ?_⟩)
  · rw [Finset.mem_range]
    omega
  · rw [Prod.mk.injEq]
    exact ⟨hcast, by rw [hcast]; exact h3.symm⟩

theorem smKernMass_khalf_ne_top (m : ℕ) (P : Polynomial ℤ) : smKernMass (khalf m P) ≠ ⊤ :=
  smKernMass_ne_top_of_summable (summable_khalf m P)


/-! ## 6. The arithmetic kernel is a bounded kernel; the concrete column has finite mass -/

/-- The arithmetic symbol `m_Ẑ` is an average of `q` numbers of modulus one. -/
theorem norm_mZ_le_one (P : Polynomial ℤ) (q : ℕ) (hq : 0 < q)
    (α₁ α₂ : Work.Analysis.IonescuWainger.Circle) : ‖mZ P q α₁ α₂‖ ≤ 1 := by
  rw [mZ, norm_mul, norm_inv, Complex.norm_natCast]
  have hsum : ‖∑ n ∈ Finset.range q,
      fourier (T := 1) (n : ℤ) α₁ * fourier (T := 1) (P.eval (n : ℤ)) α₂‖ ≤ (q : ℝ) := by
    calc ‖∑ n ∈ Finset.range q,
          fourier (T := 1) (n : ℤ) α₁ * fourier (T := 1) (P.eval (n : ℤ)) α₂‖
        ≤ ∑ n ∈ Finset.range q,
            ‖fourier (T := 1) (n : ℤ) α₁ * fourier (T := 1) (P.eval (n : ℤ)) α₂‖ :=
          norm_sum_le _ _
      _ = ∑ _n ∈ Finset.range q, (1 : ℝ) := by
          refine Finset.sum_congr rfl (fun n _ => ?_)
          rw [norm_mul, fourier_apply, fourier_apply, Circle.norm_coe, Circle.norm_coe, mul_one]
      _ = (q : ℝ) := by simp
  calc ((q : ℝ))⁻¹ * ‖∑ n ∈ Finset.range q,
        fourier (T := 1) (n : ℤ) α₁ * fourier (T := 1) (P.eval (n : ℤ)) α₂‖
      ≤ ((q : ℝ))⁻¹ * (q : ℝ) :=
        mul_le_mul_of_nonneg_left hsum (inv_nonneg.mpr (Nat.cast_nonneg q))
    _ = 1 := by rw [inv_mul_cancel₀ (by exact_mod_cast hq.ne')]

/-- **The exact-height arithmetic kernel is bounded** by the product of the two exact-height
frequency cardinalities. -/
theorem smallArithKernel_norm_le (ρ : ℝ) (P : Polynomial ℤ) (q l₁ l₂ : ℕ) (hq : 0 < q)
    (j₁ j₂ : ℤ) :
    ‖smallArithKernel ρ P q l₁ l₂ j₁ j₂‖
      ≤ ((diffFreqs ρ l₁).card : ℝ) * ((diffFreqs ρ l₂).card : ℝ) := by
  unfold smallArithKernel
  calc ‖∑ α₁ ∈ diffFreqs ρ l₁, ∑ α₂ ∈ diffFreqs ρ l₂,
        mZ P q α₁ α₂ * fourier (T := 1) (-j₁) α₁ * fourier (T := 1) (-j₂) α₂‖
      ≤ ∑ α₁ ∈ diffFreqs ρ l₁, ‖∑ α₂ ∈ diffFreqs ρ l₂,
          mZ P q α₁ α₂ * fourier (T := 1) (-j₁) α₁ * fourier (T := 1) (-j₂) α₂‖ :=
        norm_sum_le _ _
    _ ≤ ∑ α₁ ∈ diffFreqs ρ l₁, ∑ α₂ ∈ diffFreqs ρ l₂,
          ‖mZ P q α₁ α₂ * fourier (T := 1) (-j₁) α₁ * fourier (T := 1) (-j₂) α₂‖ :=
        Finset.sum_le_sum (fun _ _ => norm_sum_le _ _)
    _ ≤ ∑ _α₁ ∈ diffFreqs ρ l₁, ∑ _α₂ ∈ diffFreqs ρ l₂, (1 : ℝ) := by
        refine Finset.sum_le_sum (fun α₁ _ => Finset.sum_le_sum (fun α₂ _ => ?_))
        rw [norm_mul, norm_mul, fourier_apply, fourier_apply, Circle.norm_coe, Circle.norm_coe,
          mul_one, mul_one]
        exact norm_mZ_le_one P q hq α₁ α₂
    _ = ((diffFreqs ρ l₁).card : ℝ) * ((diffFreqs ρ l₂).card : ℝ) := by
        simp [Finset.sum_const, nsmul_eq_mul]

/-- The kernel of the exact-height twisted bilinear multiplier `smallBtwist`, as a function of the
two summation variables. -/
theorem smallBtwistK_norm_le (ρ : ℝ) (P : Polynomial ℤ) (l₁ l₂ : ℕ) (m₁ m₂ : ℝ → ℂ)
    (j₁ j₂ : ℤ) :
    ‖smallArithKernel ρ P (arithQ ρ (max l₁ l₂)) l₁ l₂ j₁ j₂ * cw m₁ j₁ * cw m₂ j₂‖
      ≤ (((diffFreqs ρ l₁).card : ℝ) * ((diffFreqs ρ l₂).card : ℝ)) * ‖cw m₁ j₁‖
        * ‖cw m₂ j₂‖ := by
  have hk := smallArithKernel_norm_le ρ P (arithQ ρ (max l₁ l₂)) l₁ l₂
    (arithQ_pos ρ (max l₁ l₂)) j₁ j₂
  have hKB : 0 ≤ ((diffFreqs ρ l₁).card : ℝ) * ((diffFreqs ρ l₂).card : ℝ) :=
    mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  rw [norm_mul, norm_mul]
  exact mul_le_mul (mul_le_mul hk le_rfl (norm_nonneg _) hKB) le_rfl (norm_nonneg _)
    (mul_nonneg hKB (norm_nonneg _))

/-- **The concrete §6 column has finite `ℓ¹(ℤ²)`-mass.**  It is the composition (`kernComp`) of the
finitely supported halved-average kernel with the two exact-height IW kernels, whose coefficient
families are `ℓ¹` (quadratic decay of a `C²` bump); the composition is summable by Young's
inequality (`Work.A7.ModelApproxCore_aux.summable_kernComp`). -/
theorem smallKconc_mass_ne_top (ρ : ℝ) (P : Polynomial ℤ) (l₁ l₂ k₁ k₂ N : ℕ) :
    smKernMass (smallKconc ρ P l₁ l₂ k₁ k₂ N) ≠ ⊤ :=
  smKernMass_ne_top_of_summable
    (Work.A7.ModelApproxCore_aux.summable_kernComp (summable_khalf N P)
      (summable_tmKernel_varphiN ρ l₁ N k₁)
      (summable_tmKernel_varphitildeN ρ l₂ P.natDegree N k₂))


end

end Work.KMTAreas.A7
