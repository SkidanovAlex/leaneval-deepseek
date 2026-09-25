import Mathlib
import Submission.Work.NN.Core.telescopeTwo
import Submission.Work.NN.Core.fiberPot
import Submission.Work.NN.Core.fiberPot_dbarCoord_self
import Submission.Work.NN.Core.fiberPot_dbarCoord
import Submission.Work.NN.Core.contDiff_fiberPot
import Submission.Work.NN.Core.sharpCut
import Submission.Work.NN.Core.holderNorm_fiberPot_le
import Submission.Work.NN.Core.TelTwoDF.Setup
import Submission.Work.NN.Core.TelTwoDF.Solves
import Submission.Work.NN.Core.TelTwoDF.S2Bound
import Submission.Work.NN.Core.TelTwoDF.dbarTransform_Eset_le
import Submission.Work.NN.Core.TelTwoDF.holderNorm_bump_mul_le
import Submission.Work.NN.Core.TelTwoDF.contDiff_mul_of_contDiffOn_of_tsupport_subset
import Submission.Work.NN.Core.TelTwoDF.TtwoDF_analyticOn

namespace Work.NN.Core

open scoped NNReal ENNReal ContDiff
open Set Filter

variable {n : ℕ}

/-! ## Germ lemmas for `dbarCoord` -/

/-- `dbarCoord` only depends on the germ of the function. -/
lemma dbarCoord_congr_of_eventuallyEq {n : ℕ} {i : Fin n} {u v : Cn n → ℂ} {z : Cn n}
    (h : u =ᶠ[nhds z] v) : Work.CR.Flat.dbarCoord i u z = Work.CR.Flat.dbarCoord i v z := by
  simp only [Work.CR.Flat.dbarCoord, h.fderiv_eq]

/-- Multiplying by a bump which equals `1` near `z` does not change `dbarCoord` at `z`. -/
lemma dbarCoord_mul_eq_of_eventuallyEq_one {n : ℕ} {χ u : Cn n → ℂ} {z : Cn n} {i : Fin n}
    (h : ∀ᶠ w in nhds z, χ w = 1) :
    Work.CR.Flat.dbarCoord i (fun y => χ y * u y) z = Work.CR.Flat.dbarCoord i u z :=
  dbarCoord_congr_of_eventuallyEq (h.mono fun w hw => by show χ w * u w = u w; rw [hw, one_mul])

/-- The pointwise form of membership in a polydisc with centre `0`. -/
lemma mem_polydisc_zero_iff {n : ℕ} {Cdat : Fin n → ℝ} {z : Cn n} :
    z ∈ Work.CR.Flat.polydisc 0 Cdat ↔ ∀ j, ‖z j‖ < Cdat j := by
  rw [Work.CR.Flat.mem_polydisc]
  constructor
  · intro h j
    have h1 := h j
    rwa [Pi.zero_apply, sub_zero] at h1
  · intro h j
    simpa only [Pi.zero_apply, sub_zero] using h j

/-- Multiplication of the data by the bump, in the notation of `chiMul`. -/
lemma chiMul_eq_fun {n : ℕ} (χ : Cn n → ℂ) (η : Fin n → Fin n → Cn n → ℂ) :
    Work.NN.Core.TelTwoDF.chiMul χ η = fun i l z => χ z * η i l z := rfl

/-- **A loss-free linear solution operator for the `(0,2)` `∂̄`-equation on a polydisc.**

For `0 < α < 1` and multi-radii `0 < ρ' j < ρ j` there is a *linear* operator
`T : (Fin n → Fin n → ℂⁿ → ℂ) →ₗ[ℝ] (Fin n → ℂⁿ → ℂ)` and constants `C k > 0` such that for every
antisymmetric `η` which is `C¹` and `∂̄`-closed on `polydisc 0 ρ`:

* `∂̄_j (T η)_l - ∂̄_l (T η)_j = η_{jl}` on `polydisc 0 ρ'`;
* `‖(T η)_j‖_{C^{k,α}(polydisc 0 ρ')} ≤ C k · Σ_{i,l} ‖η_{il}‖_{C^{k,α}(polydisc 0 ρ)}` for every `k`
  (**loss-free**: no gain, no loss of derivatives), whenever `η` is `C^k` on `polydisc 0 ρ`;
* `T η` is smooth on `polydisc 0 ρ'` whenever `η` is smooth on `polydisc 0 ρ`.

Intended construction ("derivative-free telescoping": the `(0,2)` analogue of
`Work.CR.Flat.Cauchy.recU` in `openSolRec.lean`, and the same recursion as `Work.NN.Final.uD` in
`twoRec.lean`, but with *parameterised* cutoffs so that the ratio `ρ'/ρ` may be arbitrarily close
to `1`; the fixed library constants used by `twoRec` only give the ratio `4 : 3`).

Pick, for each `s : Fin n`, radii `ρ' s < a s < R s < ρ s` and a smooth cutoff `κ_s(z) = κ(z s)`
depending on the `s`-th coordinate only, equal to `1` for `‖z s‖ ≤ a s` and vanishing for
`‖z s‖ ≥ R s` (e.g. `Work.NN.Core.sharpCut`).  Put `P_s := fiberPot R s`
(`Submission.Work.NN.Core.fiberPot`), `D⁽⁰⁾ := η`, and for `s = 0,…,n-2`:

  `ψ⁽ˢ⁾_l := P_s(κ_s · D⁽ˢ⁾_{s l})`,
  `D⁽ˢ⁺¹⁾_{il} := (1 - κ_s)·D⁽ˢ⁾_{il} + P_s((∂̄_s κ_s)·D⁽ˢ⁾_{il})`  for `i, l ≠ s`,
  `D⁽ˢ⁺¹⁾_{s l} := (1 - κ_s)·D⁽ˢ⁾_{s l}`,  `D⁽ˢ⁺¹⁾_{i s} := (1 - κ_s)·D⁽ˢ⁾_{i s}`,  `T η := Σ_{s<n-1} ψ⁽ˢ⁾`.

**This recursion never differentiates the data** (only products and potentials of it), so the
regularity of `D⁽ˢ⁾` never degrades — unlike the recursion of
`Submission.Work.NN.Core.telescopeTwo`, where `D⁽ˢ⁺¹⁾` contains `∂̄ ψ⁽ˢ⁾`.  The pointwise identity to
prove is `Δ ψ⁽ˢ⁾ = D⁽ˢ⁾ - D⁽ˢ⁺¹⁾`, which uses

1. `∂̄_s (κ_s g) = κ_s ∂̄_s g + (∂̄_s κ_s) g`, i.e. `κ_s ∂̄_s g = ∂̄_s(κ_s g) - (∂̄_s κ_s) g`;
2. closedness of `D⁽ˢ⁾`: `∂̄_i D⁽ˢ⁾_{s l} - ∂̄_l D⁽ˢ⁾_{s i} = ∂̄_s D⁽ˢ⁾_{i l}` for `i, l ≠ s`;
3. `P_s(∂̄_s g) = g` for `g` *compactly supported* (for the fixed-disc potential: `P_s(∂̄_s g) - g`
   is holomorphic in `z_s` and tends to `0` as `|z_s| → ∞`), and `P_s(0) = 0`;
4. `∂̄_i(P_s g) = P_s(∂̄_i g)` for `i ≠ s` (`Work.NN.Core.fiberPot_dbarCoord`) and
   `∂̄_s(P_s g) = g` (`Work.NN.Core.fiberPot_dbarCoord_self`).

The invariants are: `D⁽ˢ⁾` is antisymmetric and closed (on the region where the cutoffs equal `1`)
and `D⁽ˢ⁾_{il} = 0` whenever `i < s` or `l < s`; hence `D⁽ⁿ⁻¹⁾ = 0` and
`Δ(T η) = Σ_{s<n-1}(D⁽ˢ⁾ - D⁽ˢ⁺¹⁾) = η - D⁽ⁿ⁻¹⁾ = η` **on the polydisc of radii `min_s a s`**, which
contains `polydisc 0 ρ'` by construction (that is why the identity and the estimate hold on
`polydisc 0 ρ'`).  The *loss-free* estimate follows because every step is a multiplication by the
fixed bounded smooth functions `1 - κ_s`, respectively `∂̄_s κ_s`, followed by `P_s`; the only
analytic input is the `C^{k,α}` boundedness of `fiberPot`
(`Work.NN.Core.holderNorm_fiberPot_le`) together with the product rule
`Work.CR.Flat.Holder.holderNorm_mul_le` and `holderNorm_mono_set`; the smoothness uses
`Work.NN.Core.contDiff_fiberPot`.

Two proof-side caveats found in review (the statement itself was reviewed as correct):
(i) the global facts `fiberPot_dbarCoord_self` / `fiberPot_dbarCoord` / `holderNorm_fiberPot_le`
want *globally* regular data, while the defects are only nice on `polydisc 0 ρ`; either multiply
the data by a fixed bump supported inside `polydisc 0 ρ` (product over all coordinates) inside the
definition of `T`, or first prove localised versions of those three facts by the usual
"cutoff + holomorphic remainder" argument;
(ii) `T` must be built as a `LinearMap` on data that are at least *continuous* on `polydisc 0 ρ`
(the `k = 0` clause quantifies over such data), e.g. by defining it by the explicit formula on that
subspace and extending with `Submodule.exists_isCompl` + `LinearMap.ofIsCompl`, so that the
estimator clause at `k = 0` is genuinely available. -/
theorem exists_telTwoDF {n : ℕ} {α : ℝ} (hα : 0 < α) (hα1 : α < 1)
    {ρ ρ' : Fin n → ℝ} (hρ : ∀ j, 0 < ρ j) (hρ' : ∀ j, 0 < ρ' j) (hlt : ∀ j, ρ' j < ρ j) :
    ∃ (T : (Fin n → Fin n → Work.NN.Core.Cn n → ℂ) →ₗ[ℝ] (Fin n → Work.NN.Core.Cn n → ℂ))
      (C : ℕ → ℝ),
      (∀ k, 0 < C k) ∧
      (∀ η : Fin n → Fin n → Work.NN.Core.Cn n → ℂ,
        (∀ i l, ContDiffOn ℝ 1 (η i l) (Work.CR.Flat.polydisc 0 ρ)) →
        Work.NN.Core.IsAntisymmTwo η → Work.NN.Core.IsClosedTwoOn ρ η →
        ∀ (j l : Fin n) (z : Work.NN.Core.Cn n), z ∈ Work.CR.Flat.polydisc 0 ρ' →
          Work.CR.Flat.dbarCoord j (T η l) z - Work.CR.Flat.dbarCoord l (T η j) z = η j l z) ∧
      (∀ (k : ℕ) (η : Fin n → Fin n → Work.NN.Core.Cn n → ℂ),
        (∀ i l, ContDiffOn ℝ k (η i l) (Work.CR.Flat.polydisc 0 ρ)) →
        Work.NN.Core.IsAntisymmTwo η → Work.NN.Core.IsClosedTwoOn ρ η →
        ∀ j : Fin n, Work.CR.Flat.holderNorm k α (T η j) (Work.CR.Flat.polydisc 0 ρ')
          ≤ ENNReal.ofReal (C k) *
              ∑ i, ∑ l, Work.CR.Flat.holderNorm k α (η i l) (Work.CR.Flat.polydisc 0 ρ)) ∧
      (∀ η : Fin n → Fin n → Work.NN.Core.Cn n → ℂ,
        (∀ i l, ContDiffOn ℝ ⊤ (η i l) (Work.CR.Flat.polydisc 0 ρ)) →
        ∀ j : Fin n, ContDiffOn ℝ ⊤ (T η j) (Work.CR.Flat.polydisc 0 ρ'))
    := by
  obtain ⟨G, Cdat, χ, hρ'e, hbC, hCρ, hχdiff, hχcpt, hχts, hχone⟩ :=
    Work.NN.Core.TelTwoDF.exists_setup hρ hρ' hlt
  -- The solution operator.
  set T : (Fin n → Fin n → Cn n → ℂ) →ₗ[ℝ] (Fin n → Cn n → ℂ) :=
    Work.NN.Core.TelTwoDF.TtwoDF G χ with hTdef
  -- Constants of the estimate.
  have hC2ex : ∀ k : ℕ, ∃ C2 : ENNReal, C2 ≠ ⊤ ∧
      ∀ η : Fin n → Fin n → Cn n → ℂ, (∀ i l, ContDiff ℝ k (η i l)) → ∀ j : Fin n,
        Work.CR.Flat.holderNorm k α (Work.NN.Core.TelTwoDF.S2 G η j)
          (Work.NN.Core.TelTwoDF.Eset G n)
          ≤ C2 * Work.NN.Core.TelTwoDF.datumSum k α G η := fun k =>
    Work.NN.Core.TelTwoDF.S2_holderNorm_E_le_of_transform hα hα1 k G
      (Work.NN.Core.TelTwoDF.dbarTransform_Eset_le hα hα1 k G)
  have hCBex : ∀ k : ℕ, ∃ CB : ℝ, 0 < CB ∧ ∀ u : Cn n → ℂ,
      ContDiffOn ℝ k u (Work.CR.Flat.polydisc 0 ρ) →
      Work.CR.Flat.holderNorm k α (fun z => χ z * u z) Set.univ
        ≤ ENNReal.ofReal CB * Work.CR.Flat.holderNorm k α u (Work.CR.Flat.polydisc 0 ρ) :=
    fun k => Work.NN.Core.TelTwoDF.holderNorm_bump_mul_le hα.le hα1.le k hρ χ
      (hχdiff.of_le (by exact_mod_cast le_top)) hχcpt
      (fun z hz => by
        obtain ⟨j, hj⟩ := hz
        refine image_eq_zero_of_notMem_tsupport (fun hmem => ?_)
        have h1 := (Work.CR.Flat.mem_polydisc.mp (hχts hmem)) j
        simp only [Pi.zero_apply, sub_zero] at h1
        linarith)
  choose C2 hC2ne hC2spec using hC2ex
  choose CB hCBpos hCBspec using hCBex
  refine ⟨T, fun k => max 1 (C2 k).toReal * CB k, ?_, ?_, ?_, ?_⟩
  · -- positivity of the constants
    intro k
    exact mul_pos (lt_of_lt_of_le one_pos (le_max_left _ _)) (hCBpos k)
  · -- clause (a): the telescoping solves the `(0,2)`-equation
    intro η hη hanti hclosed j l z hz
    set η' : Fin n → Fin n → Cn n → ℂ := fun i l y => χ y * η i l y with hη'def
    have hzk : ∀ k : Fin n, ‖z k‖ < ρ' k := fun k => by
      exact mem_polydisc_zero_iff.mp hz k
    have hmemC : ∀ k : Fin n, ‖z k‖ < Cdat k := fun k =>
      ((((hzk k).trans (hρ'e k)).trans (G.hea k)).trans (G.hab k)).trans (hbC k)
    have hχz : ∀ᶠ w in nhds z, χ w = 1 :=
      mem_of_superset ((Work.CR.Flat.isOpen_polydisc (0 : Cn n) Cdat).mem_nhds
          (mem_polydisc_zero_iff.mpr hmemC))
        (fun w hw => hχone w (mem_polydisc_zero_iff.mp hw))
    have hη'cd : ∀ i l, ContDiff ℝ 1 (η' i l) := fun i l =>
      Work.NN.Core.TelTwoDF.contDiff_mul_of_contDiffOn_of_tsupport_subset
        (Work.CR.Flat.isOpen_polydisc (0 : Cn n) ρ)
        (hχdiff.of_le (by exact_mod_cast le_top)) hχts (hη i l)
    have hanti' : ∀ i l y, η' i l y = - η' l i y := by
      intro i l y
      simp only [hη'def]
      rw [hanti i l y]
      ring
    have hcl : ∀ i l m' y, (∀ k : Fin n, ‖y k‖ < G.b k) →
        Work.CR.Flat.dbarCoord i (η' l m') y - Work.CR.Flat.dbarCoord l (η' i m') y
          + Work.CR.Flat.dbarCoord m' (η' i l) y = 0 := by
      intro i l m' y hy
      have hyC : ∀ k : Fin n, ‖y k‖ < Cdat k := fun k => (hy k).trans (hbC k)
      have hyρ : ∀ k : Fin n, ‖y k‖ < ρ k := fun k => (hyC k).trans (hCρ k)
      have hχy : ∀ᶠ w in nhds y, χ w = 1 :=
        mem_of_superset ((Work.CR.Flat.isOpen_polydisc (0 : Cn n) Cdat).mem_nhds
            (mem_polydisc_zero_iff.mpr hyC))
          (fun w hw => hχone w (mem_polydisc_zero_iff.mp hw))
      have e1 : Work.CR.Flat.dbarCoord i (η' l m') y
          = Work.CR.Flat.dbarCoord i (η l m') y :=
        dbarCoord_mul_eq_of_eventuallyEq_one hχy
      have e2 : Work.CR.Flat.dbarCoord l (η' i m') y
          = Work.CR.Flat.dbarCoord l (η i m') y :=
        dbarCoord_mul_eq_of_eventuallyEq_one hχy
      have e3 : Work.CR.Flat.dbarCoord m' (η' i l) y
          = Work.CR.Flat.dbarCoord m' (η i l) y :=
        dbarCoord_mul_eq_of_eventuallyEq_one hχy
      rw [e1, e2, e3]
      exact hclosed i l m' y (mem_polydisc_zero_iff.mpr hyρ)
    have hzE : z ∈ Work.NN.Core.TelTwoDF.solveSet G := fun k => (hzk k).trans (hρ'e k)
    have hsol := Work.NN.Core.TelTwoDF.S2_solves G hη'cd hanti' hcl j l z hzE
    have hTη : T η = Work.NN.Core.TelTwoDF.S2 G η' := by
      rw [hTdef]
      funext i y
      rfl
    rw [hTη]
    rw [hsol]
    simp only [hη'def]
    rw [hχz.self_of_nhds, one_mul]
  · -- clause (b): the loss-free `C^{k,α}` estimate
    intro k η hη _hanti _hclosed j
    have hη'cd : ∀ i l, ContDiff ℝ k (fun y => χ y * η i l y) := fun i l =>
      Work.NN.Core.TelTwoDF.contDiff_mul_of_contDiffOn_of_tsupport_subset
        (Work.CR.Flat.isOpen_polydisc (0 : Cn n) ρ)
        (hχdiff.of_le (by exact_mod_cast le_top)) hχts (hη i l)
    have h2 := hC2spec k (fun i l y => χ y * η i l y) hη'cd j
    have hdatum : Work.NN.Core.TelTwoDF.datumSum k α G (fun i l y => χ y * η i l y)
        ≤ ENNReal.ofReal (CB k) *
            ∑ i, ∑ l, Work.CR.Flat.holderNorm k α (η i l) (Work.CR.Flat.polydisc 0 ρ) := by
      rw [Work.NN.Core.TelTwoDF.datumSum, Work.NN.Core.TelTwoDF.Eset_zero]
      calc ∑ i, ∑ l, Work.CR.Flat.holderNorm k α (fun z => χ z * η i l z)
              (Work.CR.Flat.polydisc 0 G.b)
          ≤ ∑ i, ∑ l, Work.CR.Flat.holderNorm k α (fun z => χ z * η i l z) Set.univ :=
            Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun l _ =>
              Work.CR.Flat.holderNorm_mono_set isOpen_univ
                (Work.CR.Flat.isOpen_polydisc (0 : Cn n) G.b) (subset_univ _) k α _
        _ ≤ ∑ i, ∑ l, ENNReal.ofReal (CB k) *
              Work.CR.Flat.holderNorm k α (η i l) (Work.CR.Flat.polydisc 0 ρ) :=
            Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun l _ => hCBspec k _ (hη i l)
        _ = ENNReal.ofReal (CB k) *
              ∑ i, ∑ l, Work.CR.Flat.holderNorm k α (η i l) (Work.CR.Flat.polydisc 0 ρ) := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [Finset.mul_sum]
    have hmono : Work.CR.Flat.holderNorm k α (T η j) (Work.CR.Flat.polydisc 0 ρ')
        ≤ Work.CR.Flat.holderNorm k α (T η j) (Work.NN.Core.TelTwoDF.Eset G n) := by
      refine Work.CR.Flat.holderNorm_mono_set (Work.NN.Core.TelTwoDF.isOpen_Eset G n)
        (Work.CR.Flat.isOpen_polydisc (0 : Cn n) ρ') ?_ k α (T η j)
      intro y hy
      rw [Work.NN.Core.TelTwoDF.Eset_n, mem_polydisc_zero_iff]
      intro i
      exact lt_trans (mem_polydisc_zero_iff.mp hy i) (hρ'e i)
    have h1 : Work.CR.Flat.holderNorm k α (T η j) (Work.NN.Core.TelTwoDF.Eset G n)
        ≤ C2 k * Work.NN.Core.TelTwoDF.datumSum k α G (fun i l y => χ y * η i l y) := by
      have hTeq : T η = Work.NN.Core.TelTwoDF.S2 G (fun i l y => χ y * η i l y) := by
        rw [hTdef]
        funext i y
        rfl
      rw [hTeq]
      exact h2
    calc Work.CR.Flat.holderNorm k α (T η j) (Work.CR.Flat.polydisc 0 ρ')
        ≤ Work.CR.Flat.holderNorm k α (T η j) (Work.NN.Core.TelTwoDF.Eset G n) := hmono
      _ ≤ C2 k * Work.NN.Core.TelTwoDF.datumSum k α G (fun i l y => χ y * η i l y) := h1
      _ ≤ C2 k * (ENNReal.ofReal (CB k) *
            ∑ i, ∑ l, Work.CR.Flat.holderNorm k α (η i l) (Work.CR.Flat.polydisc 0 ρ)) :=
          mul_le_mul_right hdatum (C2 k)
      _ = (C2 k * ENNReal.ofReal (CB k)) *
            ∑ i, ∑ l, Work.CR.Flat.holderNorm k α (η i l) (Work.CR.Flat.polydisc 0 ρ) := by
          rw [mul_assoc]
      _ ≤ ENNReal.ofReal (max 1 (C2 k).toReal * CB k) *
            ∑ i, ∑ l, Work.CR.Flat.holderNorm k α (η i l) (Work.CR.Flat.polydisc 0 ρ) := by
          refine mul_le_mul_left ?_ _
          calc C2 k * ENNReal.ofReal (CB k)
              = ENNReal.ofReal (C2 k).toReal * ENNReal.ofReal (CB k) := by
                rw [ENNReal.ofReal_toReal (hC2ne k)]
            _ = ENNReal.ofReal ((C2 k).toReal * CB k) := by
                rw [← ENNReal.ofReal_mul ENNReal.toReal_nonneg]
            _ ≤ ENNReal.ofReal (max 1 (C2 k).toReal * CB k) :=
                ENNReal.ofReal_le_ofReal
                  (mul_le_mul_of_nonneg_right (le_max_right _ _) (le_of_lt (hCBpos k)))
  · -- clause (c): real analyticity of `T η` for `η` real analytic
    intro η hη j
    have hηan : ∀ i l, AnalyticOn ℝ (η i l) (Work.CR.Flat.polydisc 0 ρ) :=
      fun i l => (hη i l).analyticOn
    have hχall : ∀ m : ℕ, ContDiff ℝ m χ :=
      fun m => hχdiff.of_le (by exact_mod_cast le_top)
    have hres := Work.NN.Core.TelTwoDF.TtwoDF_analyticOn hlt hρ hρ' G hbC hCρ hχall hχcpt
      hχts hχone hρ'e hηan j
    exact hres.contDiffOn (Work.CR.Flat.isOpen_polydisc (0 : Cn n) ρ').uniqueDiffOn

end Work.NN.Core
