/-
Copyright: none.  Part of the `Newlander-Nirenberg` formalisation project.

# The assembly of the linearised Newton correction

This file proves `Work.NN.Newton.newtonCorrection` from two inputs (kept as hypotheses so that the
assembly can be developed and checked independently of their proofs):

* `hDefect` : the `∂̄`-closedness and the quadratic `C^{0,α}` bound for the defect
  `coordDefect A p = ∂̄₀ (coordDatum A p)` of the coordinate datum
  (`Work.NN.Newton.coordDefectData`);
* `hArith` : the pure real arithmetic that turns the constants `C1`, `C2`, `C3` and the exponents
  `N1`, `N2` of the two thin solvers into a single `C / δ ^ N`
  (`Work.NN.Newton.newtonCorrectionArith`).

The construction is that of `Submission/Work/NN/Newton/DESIGN.md` §3, lemma 4:

  `F^{(p)} := coordDatum A p`, `ψ^{(p)} := flatTwoThin (r, δ/2) (∂̄₀ F^{(p)})`,
  `G^{(p)} := F^{(p)} - ψ^{(p)}`, `v_p := flatOneThin (r(1-δ/2), (δ/2)/(1-δ/2)) G^{(p)}`.
-/
import Mathlib
import Submission.Work.NN.Core.CnPert
import Submission.Work.NN.Final.Defs
import Submission.Work.CR.Flat.Holder
import Submission.Work.CR.Flat.Holder.holderNorm_add_le
import Submission.Work.CR.Flat.Holder.holderNorm_neg
import Submission.Work.CR.Flat.Polydisc
import Submission.Work.NN.Final.holderNormCongr
import Submission.Work.NN.Newton.newtonCorrDefs
import Submission.Work.NN.Newton.newtonCorrAux
import Submission.Work.NN.Newton.flatOneThin
import Submission.Work.NN.Newton.flatTwoThin

noncomputable section

open scoped NNReal ENNReal ContDiff
open Set

namespace Work.NN.Newton

theorem newtonCorrection_core {n : ℕ} (hn : 0 < n) {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    (hDefect : ∃ C : ℝ, 0 < C ∧ ∀ r : ℝ, 1 ≤ r → r ≤ 4 →
      ∀ A : Work.NN.Core.Cn n → Work.NN.Core.Cn n →L[ℝ] Work.NN.Core.Cn n,
        (∀ m : ℕ, ContDiffOn ℝ m A
          (Work.CR.Flat.polydisc (0 : Work.NN.Core.Cn n) (fun _ => r))) →
        (∀ z, z ∈ Work.CR.Flat.polydisc (0 : Work.NN.Core.Cn n) (fun _ => r) →
          ∀ v : Work.NN.Core.Cn n,
            (Work.NN.Core.JstdCn n + A) z ((Work.NN.Core.JstdCn n + A) z v) = -v) →
        (∀ u : Work.NN.Core.Cn n → ℂ, (∀ k : ℕ, ContDiff ℝ k u) →
          ∀ z, z ∈ Work.CR.Flat.polydisc (0 : Work.NN.Core.Cn n) (fun _ => r) →
            ∀ V W : Work.NN.Core.Cn n,
              Work.NN.Final.proj02 (Work.NN.Core.JstdCn n + A)
                (fun z' => Work.NN.Final.dOne
                  (fun z'' => Work.NN.Core.dbarCn (Work.NN.Core.JstdCn n + A) u z'') z')
                z V W = 0) →
        ∀ a : ℝ, 0 ≤ a → a ≤ 1 →
        (∀ w : Work.NN.Core.Cn n, ‖w‖ ≤ 1 → ∀ j : Fin n,
          Work.CR.Flat.holderNorm 1 α (fun z => A z w j)
            (Work.CR.Flat.polydisc (0 : Work.NN.Core.Cn n) (fun _ => r))
            ≤ ENNReal.ofReal a) →
        (∀ p j k l : Fin n, ∀ z,
            z ∈ Work.CR.Flat.polydisc (0 : Work.NN.Core.Cn n) (fun _ => r) →
          Work.CR.Flat.dbarCoord j (coordDefect A p l k) z
            - Work.CR.Flat.dbarCoord l (coordDefect A p j k) z
            + Work.CR.Flat.dbarCoord k (coordDefect A p j l) z = 0) ∧
        (∀ p j k : Fin n, Work.CR.Flat.holderNorm 0 α (coordDefect A p j k)
            (Work.CR.Flat.polydisc (0 : Work.NN.Core.Cn n) (fun _ => r))
            ≤ ENNReal.ofReal (C * a ^ 2)))
    (hArith : ∀ {C1 C2 C3 : ℝ}, 0 < C1 → 0 < C2 → 0 < C3 → ∀ N1 N2 : ℕ,
      ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, ∀ δ a : ℝ, 0 < δ → δ ≤ 1 / 8 → 0 ≤ a → a ≤ 1 →
        C1 / ((δ / 2) / (1 - δ / 2)) ^ N1
            * ((n : ℝ) * (a / 2 + C2 / (δ / 2) ^ N2 * ((n : ℝ) ^ 2 * C3 * a ^ 2)))
          ≤ C / δ ^ N * a ∧
        C2 / (δ / 2) ^ N2 * ((n : ℝ) ^ 2 * C3 * a ^ 2) ≤ C / δ ^ N * a ^ 2) :
    ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, ∀ r δ : ℝ, 1 ≤ r → r ≤ 4 → 0 < δ → δ ≤ 1 / 8 →
      ∀ A : Work.NN.Core.Cn n → Work.NN.Core.Cn n →L[ℝ] Work.NN.Core.Cn n,
        (∀ m : ℕ, ContDiffOn ℝ m A
          (Work.CR.Flat.polydisc (0 : Work.NN.Core.Cn n) (fun _ => r))) →
        (∀ z, z ∈ Work.CR.Flat.polydisc (0 : Work.NN.Core.Cn n) (fun _ => r) →
          ∀ v : Work.NN.Core.Cn n,
            (Work.NN.Core.JstdCn n + A) z ((Work.NN.Core.JstdCn n + A) z v) = -v) →
        (∀ u : Work.NN.Core.Cn n → ℂ, (∀ k : ℕ, ContDiff ℝ k u) →
          ∀ z, z ∈ Work.CR.Flat.polydisc (0 : Work.NN.Core.Cn n) (fun _ => r) →
            ∀ V W : Work.NN.Core.Cn n,
              Work.NN.Final.proj02 (Work.NN.Core.JstdCn n + A)
                (fun z' => Work.NN.Final.dOne
                  (fun z'' => Work.NN.Core.dbarCn (Work.NN.Core.JstdCn n + A) u z'') z')
                z V W = 0) →
        ∀ a : ℝ, 0 ≤ a → a ≤ 1 →
        (∀ w : Work.NN.Core.Cn n, ‖w‖ ≤ 1 → ∀ j : Fin n,
          Work.CR.Flat.holderNorm 1 α (fun z => A z w j)
            (Work.CR.Flat.polydisc (0 : Work.NN.Core.Cn n) (fun _ => r))
            ≤ ENNReal.ofReal a) →
        ∃ v : Fin n → Work.NN.Core.Cn n → ℂ,
          (∀ l, ∀ m : ℕ, ContDiffOn ℝ m (v l)
            (Work.CR.Flat.polydisc (0 : Work.NN.Core.Cn n) (fun _ => r * (1 - δ)))) ∧
          (∀ l, Work.CR.Flat.holderNorm 2 α (v l)
              (Work.CR.Flat.polydisc (0 : Work.NN.Core.Cn n) (fun _ => r * (1 - δ)))
            ≤ ENNReal.ofReal (C / δ ^ N * a)) ∧
          (∀ l k, Work.CR.Flat.holderNorm 1 α
              (fun z => Work.CR.Flat.dbarCoord k (v l) z
                - Work.NN.Core.Lcoef A (fun y => y l) k z)
              (Work.CR.Flat.polydisc (0 : Work.NN.Core.Cn n) (fun _ => r * (1 - δ)))
            ≤ ENNReal.ofReal (C / δ ^ N * a ^ 2)) := by
  obtain ⟨Cq, hCqpos, hDefectB⟩ := hDefect
  obtain ⟨Ct, hCtpos, N2, hTwo⟩ := flatTwoThin hn hα0 hα1
  obtain ⟨Co, hCopos, N1, hOne⟩ := flatOneThin hn hα0 hα1
  obtain ⟨C, hCpos, N, hArithB⟩ :=
    hArith (C1 := Co) (C2 := Ct) (C3 := Cq) hCopos hCtpos hCqpos N1 N2
  refine ⟨C, hCpos, N, ?_⟩
  intro r δ hr1 hr4 hδ0 hδ8 A hAsm hJac hInt a ha0 ha1 hA
  -- ## radii, gaps and the two polydiscs in play
  have hδ2pos : 0 < δ / 2 := by linarith
  have hδ2le : δ / 2 ≤ 1 / 4 := by linarith
  have hmr : r * (1 - δ / 2) ≤ r := by nlinarith only [hr1, hδ0]
  have hor : r * (1 - δ) ≤ r * (1 - δ / 2) := by nlinarith only [hr1, hδ0]
  have hPmPr : Work.CR.Flat.polydisc (0 : Work.NN.Core.Cn n) (fun _ => r * (1 - δ / 2))
      ⊆ Work.CR.Flat.polydisc (0 : Work.NN.Core.Cn n) (fun _ => r) :=
    Work.CR.Flat.polydisc_mono (fun _ => hmr)
  have hPoPm : Work.CR.Flat.polydisc (0 : Work.NN.Core.Cn n) (fun _ => r * (1 - δ))
      ⊆ Work.CR.Flat.polydisc (0 : Work.NN.Core.Cn n) (fun _ => r * (1 - δ / 2)) :=
    Work.CR.Flat.polydisc_mono (fun _ => hor)
  have hPr_open : IsOpen (Work.CR.Flat.polydisc (0 : Work.NN.Core.Cn n) (fun _ => r)) :=
    Work.CR.Flat.isOpen_polydisc 0 _
  have hPm_open : IsOpen (Work.CR.Flat.polydisc (0 : Work.NN.Core.Cn n) (fun _ => r * (1 - δ / 2))) :=
    Work.CR.Flat.isOpen_polydisc 0 _
  have hPo_open : IsOpen (Work.CR.Flat.polydisc (0 : Work.NN.Core.Cn n) (fun _ => r * (1 - δ))) :=
    Work.CR.Flat.isOpen_polydisc 0 _
  have hr_half : 1 / 2 ≤ r := by linarith
  have hr1_half : 1 / 2 ≤ r * (1 - δ / 2) := by nlinarith only [hr1, hδ0, hδ8]
  have hr1_le : r * (1 - δ / 2) ≤ 4 := by nlinarith only [hr1, hr4, hδ0]
  have hd1pos : 0 < (δ / 2) / (1 - δ / 2) := by
    apply div_pos hδ2pos; linarith
  have hd1le : (δ / 2) / (1 - δ / 2) ≤ 1 / 4 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < 1 - δ / 2)]
    nlinarith only [hδ8]
  have hrd : r * (1 - δ / 2) * (1 - (δ / 2) / (1 - δ / 2)) = r * (1 - δ) := by
    have h1 : (1 : ℝ) - δ / 2 ≠ 0 := by linarith
    have h3 : (1 - δ / 2) * ((δ / 2) / (1 - δ / 2)) = δ / 2 := by
      rw [mul_div_assoc', mul_div_cancel_left₀ _ h1]
    rw [mul_sub, mul_one, mul_assoc, h3]
    ring
  -- ## (1) the defect data
  have hDefB := hDefectB r hr1 hr4 A hAsm hJac hInt a ha0 ha1 hA
  obtain ⟨hDefclos, hDefbd⟩ := hDefB
  -- ## (2) the (0,2)-potential ψ and the corrected datum G
  have hPsiExists : ∀ p : Fin n, ∃ ψ : Fin n → Work.NN.Core.Cn n → ℂ,
      (∀ q (m : ℕ), ContDiffOn ℝ m (ψ q)
        (Work.CR.Flat.polydisc (0 : Work.NN.Core.Cn n) (fun _ => r * (1 - δ / 2)))) ∧
      (∀ j l z, z ∈ Work.CR.Flat.polydisc (0 : Work.NN.Core.Cn n) (fun _ => r * (1 - δ / 2)) →
        Work.CR.Flat.dbarCoord j (ψ l) z - Work.CR.Flat.dbarCoord l (ψ j) z
          = coordDefect A p j l z) ∧
      (∀ q, Work.CR.Flat.holderNorm 1 α (ψ q)
          (Work.CR.Flat.polydisc (0 : Work.NN.Core.Cn n) (fun _ => r * (1 - δ / 2)))
        ≤ ENNReal.ofReal (Ct / (δ / 2) ^ N2) *
          ∑ j : Fin n, ∑ l : Fin n, Work.CR.Flat.holderNorm 0 α (coordDefect A p j l)
            (Work.CR.Flat.polydisc (0 : Work.NN.Core.Cn n) (fun _ => r))) := by
    intro p
    exact hTwo r (δ / 2) hr_half hr4 hδ2pos hδ2le (coordDefect A p)
      (fun j l m => coordDefect_contDiffOn hAsm p j l m)
      (fun j l z => coordDefect_antisymm A p j l z)
      (fun j l k z hz => hDefclos p j k l z hz)
  choose ψ hψ using hPsiExists
  have hψsm : ∀ p q (m : ℕ), ContDiffOn ℝ m (ψ p q)
      (Work.CR.Flat.polydisc (0 : Work.NN.Core.Cn n) (fun _ => r * (1 - δ / 2))) :=
    fun p q m => (hψ p).1 q m
  have hψsol : ∀ p j l z,
      z ∈ Work.CR.Flat.polydisc (0 : Work.NN.Core.Cn n) (fun _ => r * (1 - δ / 2)) →
      Work.CR.Flat.dbarCoord j (ψ p l) z - Work.CR.Flat.dbarCoord l (ψ p j) z
        = coordDefect A p j l z := fun p j l z hz => (hψ p).2.1 j l z hz
  have hψbd : ∀ p q, Work.CR.Flat.holderNorm 1 α (ψ p q)
        (Work.CR.Flat.polydisc (0 : Work.NN.Core.Cn n) (fun _ => r * (1 - δ / 2)))
      ≤ ENNReal.ofReal (Ct / (δ / 2) ^ N2) *
        ∑ j : Fin n, ∑ l : Fin n, Work.CR.Flat.holderNorm 0 α (coordDefect A p j l)
          (Work.CR.Flat.polydisc (0 : Work.NN.Core.Cn n) (fun _ => r)) :=
    fun p q => (hψ p).2.2 q
  let G : Fin n → Fin n → Work.NN.Core.Cn n → ℂ := fun p q y => coordDatum A p q y - ψ p q y
  have hGsm : ∀ p q (m : ℕ), ContDiffOn ℝ m (G p q)
      (Work.CR.Flat.polydisc (0 : Work.NN.Core.Cn n) (fun _ => r * (1 - δ / 2))) := fun p q m =>
    ((coordDatum_contDiffOn hAsm p q m).mono hPmPr).sub (hψsm p q m)
  have hGclos : ∀ p j l z,
      z ∈ Work.CR.Flat.polydisc (0 : Work.NN.Core.Cn n) (fun _ => r * (1 - δ / 2)) →
      Work.CR.Flat.dbarCoord j (G p l) z = Work.CR.Flat.dbarCoord l (G p j) z := by
    intro p j l z hz
    have hzn : z ∈ Work.CR.Flat.polydisc (0 : Work.NN.Core.Cn n) (fun _ => r * (1 - δ / 2)) := hz
    have hdl : DifferentiableAt ℝ (coordDatum A p l) z :=
      (((coordDatum_contDiffOn hAsm p l 1).mono hPmPr).contDiffAt
        (hPm_open.mem_nhds hzn)).differentiableAt (by norm_num)
    have hpl : DifferentiableAt ℝ (ψ p l) z :=
      (((hψsm p l 1).contDiffAt (hPm_open.mem_nhds hzn))).differentiableAt (by norm_num)
    have hdj : DifferentiableAt ℝ (coordDatum A p j) z :=
      (((coordDatum_contDiffOn hAsm p j 1).mono hPmPr).contDiffAt
        (hPm_open.mem_nhds hzn)).differentiableAt (by norm_num)
    have hpj : DifferentiableAt ℝ (ψ p j) z :=
      (((hψsm p j 1).contDiffAt (hPm_open.mem_nhds hzn))).differentiableAt (by norm_num)
    have e1 : Work.CR.Flat.dbarCoord j (G p l) z
        = Work.CR.Flat.dbarCoord j (coordDatum A p l) z
          - Work.CR.Flat.dbarCoord j (ψ p l) z :=
      Work.NN.Final.dbarCoord_sub_diff hdl hpl j
    have e2 : Work.CR.Flat.dbarCoord l (G p j) z
        = Work.CR.Flat.dbarCoord l (coordDatum A p j) z
          - Work.CR.Flat.dbarCoord l (ψ p j) z :=
      Work.NN.Final.dbarCoord_sub_diff hdj hpj l
    have hsol := hψsol p j l z hzn
    have hdef : coordDefect A p j l z
        = Work.CR.Flat.dbarCoord j (coordDatum A p l) z
          - Work.CR.Flat.dbarCoord l (coordDatum A p j) z := by
      simp only [coordDefect, Work.NN.Final.ddbar, Work.NN.Final.dbarOne_std]
    have hAB : Work.CR.Flat.dbarCoord j (coordDatum A p l) z
        - Work.CR.Flat.dbarCoord l (coordDatum A p j) z
        = Work.CR.Flat.dbarCoord j (ψ p l) z - Work.CR.Flat.dbarCoord l (ψ p j) z :=
      hdef.symm.trans hsol.symm
    rw [e1, e2]
    linear_combination hAB
  -- ## (3) the constants
  let T : ℝ := Ct / (δ / 2) ^ N2 * ((n : ℝ) ^ 2 * Cq * a ^ 2)
  have hdefsum : ∀ p : Fin n, ∑ j : Fin n, ∑ l : Fin n,
        Work.CR.Flat.holderNorm 0 α (coordDefect A p j l)
          (Work.CR.Flat.polydisc (0 : Work.NN.Core.Cn n) (fun _ => r))
      ≤ ENNReal.ofReal ((n : ℝ) ^ 2 * Cq * a ^ 2) := by
    intro p
    calc ∑ j : Fin n, ∑ l : Fin n, Work.CR.Flat.holderNorm 0 α (coordDefect A p j l)
          (Work.CR.Flat.polydisc (0 : Work.NN.Core.Cn n) (fun _ => r))
        ≤ ∑ _j : Fin n, ∑ _l : Fin n, ENNReal.ofReal (Cq * a ^ 2) :=
          Finset.sum_le_sum (fun j _ => Finset.sum_le_sum (fun l _ => hDefbd p j l))
      _ = (n : ℝ≥0∞) * ((n : ℝ≥0∞) * ENNReal.ofReal (Cq * a ^ 2)) := by
          simp [Finset.sum_const, nsmul_eq_mul]
      _ = ENNReal.ofReal ((n : ℝ) ^ 2 * Cq * a ^ 2) := by
          rw [← ENNReal.ofReal_natCast n, ← ENNReal.ofReal_mul (by positivity),
            ← ENNReal.ofReal_mul (by positivity),
            show (n : ℝ) * ((n : ℝ) * (Cq * a ^ 2)) = (n : ℝ) ^ 2 * Cq * a ^ 2 from by ring]
  have hψT : ∀ p q, Work.CR.Flat.holderNorm 1 α (ψ p q)
        (Work.CR.Flat.polydisc (0 : Work.NN.Core.Cn n) (fun _ => r * (1 - δ / 2)))
      ≤ ENNReal.ofReal T := by
    intro p q
    have h2 := hdefsum p
    calc Work.CR.Flat.holderNorm 1 α (ψ p q)
          (Work.CR.Flat.polydisc (0 : Work.NN.Core.Cn n) (fun _ => r * (1 - δ / 2)))
        ≤ ENNReal.ofReal (Ct / (δ / 2) ^ N2) *
            ∑ j : Fin n, ∑ l : Fin n, Work.CR.Flat.holderNorm 0 α (coordDefect A p j l)
              (Work.CR.Flat.polydisc (0 : Work.NN.Core.Cn n) (fun _ => r)) := hψbd p q
      _ ≤ ENNReal.ofReal (Ct / (δ / 2) ^ N2) *
            ENNReal.ofReal ((n : ℝ) ^ 2 * Cq * a ^ 2) :=
          mul_le_mul_of_nonneg_left h2 (by simp)
      _ = ENNReal.ofReal T := by
          rw [← ENNReal.ofReal_mul (by positivity)]
  have hT : T ≤ C / δ ^ N * a ^ 2 := (hArithB δ a hδ0 hδ8 ha0 ha1).2
  have hfin : Co / ((δ / 2) / (1 - δ / 2)) ^ N1 * ((n : ℝ) * (a / 2 + T))
      ≤ C / δ ^ N * a := (hArithB δ a hδ0 hδ8 ha0 ha1).1
  -- ## (4) the bound on the corrected data
  have hGbd : ∀ p q, Work.CR.Flat.holderNorm 1 α (G p q)
        (Work.CR.Flat.polydisc (0 : Work.NN.Core.Cn n) (fun _ => r * (1 - δ / 2)))
      ≤ ENNReal.ofReal (a / 2 + T) := by
    intro p q
    have huniq : UniqueDiffOn ℝ
        (Work.CR.Flat.polydisc (0 : Work.NN.Core.Cn n) (fun _ => r * (1 - δ / 2))) :=
      hPm_open.uniqueDiffOn
    have hadd := Work.CR.Flat.Holder.holderNorm_add_le
      (k := 1) (α := α) (f := coordDatum A p q) (g := -(ψ p q))
      ((coordDatum_contDiffOn hAsm p q 1).mono hPmPr) ((hψsm p q 1).neg) huniq
    rw [Work.CR.Flat.Holder.holderNorm_neg (hψsm p q 1) huniq] at hadd
    have hsplit : Work.CR.Flat.holderNorm 1 α (G p q)
          (Work.CR.Flat.polydisc (0 : Work.NN.Core.Cn n) (fun _ => r * (1 - δ / 2)))
        ≤ Work.CR.Flat.holderNorm 1 α (coordDatum A p q)
            (Work.CR.Flat.polydisc (0 : Work.NN.Core.Cn n) (fun _ => r * (1 - δ / 2)))
          + Work.CR.Flat.holderNorm 1 α (ψ p q)
            (Work.CR.Flat.polydisc (0 : Work.NN.Core.Cn n) (fun _ => r * (1 - δ / 2))) := by
      have hfun : coordDatum A p q + -(ψ p q) = G p q := rfl
      rw [hfun] at hadd
      exact hadd
    have h1 : Work.CR.Flat.holderNorm 1 α (coordDatum A p q)
          (Work.CR.Flat.polydisc (0 : Work.NN.Core.Cn n) (fun _ => r * (1 - δ / 2)))
        ≤ ENNReal.ofReal (a / 2) :=
      le_trans (Work.CR.Flat.holderNorm_mono_set hPr_open hPm_open hPmPr 1 α _)
        (coordDatum_holderNorm_le_half A hAsm hA p q)
    have h2 : Work.CR.Flat.holderNorm 1 α (ψ p q)
          (Work.CR.Flat.polydisc (0 : Work.NN.Core.Cn n) (fun _ => r * (1 - δ / 2)))
        ≤ ENNReal.ofReal T := hψT p q
    calc Work.CR.Flat.holderNorm 1 α (G p q)
          (Work.CR.Flat.polydisc (0 : Work.NN.Core.Cn n) (fun _ => r * (1 - δ / 2)))
        ≤ ENNReal.ofReal (a / 2) + ENNReal.ofReal T := le_trans hsplit (add_le_add h1 h2)
      _ = ENNReal.ofReal (a / 2 + T) := by
          rw [ENNReal.ofReal_add (by linarith) (by positivity)]
  have hsum : ∀ p : Fin n, ∑ q : Fin n, Work.CR.Flat.holderNorm 1 α (G p q)
        (Work.CR.Flat.polydisc (0 : Work.NN.Core.Cn n) (fun _ => r * (1 - δ / 2)))
      ≤ ENNReal.ofReal ((n : ℝ) * (a / 2 + T)) := by
    intro p
    calc ∑ q : Fin n, Work.CR.Flat.holderNorm 1 α (G p q)
          (Work.CR.Flat.polydisc (0 : Work.NN.Core.Cn n) (fun _ => r * (1 - δ / 2)))
        ≤ ∑ _q : Fin n, ENNReal.ofReal (a / 2 + T) :=
          Finset.sum_le_sum (fun q _ => hGbd p q)
      _ = (n : ℝ≥0∞) * ENNReal.ofReal (a / 2 + T) := by
          simp [Finset.sum_const, nsmul_eq_mul]
      _ = ENNReal.ofReal ((n : ℝ) * (a / 2 + T)) := by
          rw [← ENNReal.ofReal_natCast n, ← ENNReal.ofReal_mul (by positivity)]
  -- ## (5) the (0,1)-primitive of the corrected data
  have hOnEx : ∀ p : Fin n, ∃ u : Work.NN.Core.Cn n → ℂ,
      (∀ (m : ℕ), ContDiffOn ℝ m u (Work.CR.Flat.polydisc (0 : Work.NN.Core.Cn n)
        (fun _ => r * (1 - δ / 2) * (1 - (δ / 2) / (1 - δ / 2))))) ∧
      (∀ j z, z ∈ Work.CR.Flat.polydisc (0 : Work.NN.Core.Cn n)
          (fun _ => r * (1 - δ / 2) * (1 - (δ / 2) / (1 - δ / 2))) →
        Work.CR.Flat.dbarCoord j u z = G p j z) ∧
      Work.CR.Flat.holderNorm 2 α u
          (Work.CR.Flat.polydisc (0 : Work.NN.Core.Cn n)
            (fun _ => r * (1 - δ / 2) * (1 - (δ / 2) / (1 - δ / 2))))
        ≤ ENNReal.ofReal (Co / ((δ / 2) / (1 - δ / 2)) ^ N1) *
          ∑ q : Fin n, Work.CR.Flat.holderNorm 1 α (G p q)
            (Work.CR.Flat.polydisc (0 : Work.NN.Core.Cn n) (fun _ => r * (1 - δ / 2))) := by
    intro p
    exact hOne (r * (1 - δ / 2)) ((δ / 2) / (1 - δ / 2)) hr1_half hr1_le hd1pos hd1le (G p)
      (fun j m => hGsm p j m) (fun j l z hz => hGclos p j l z hz)
  choose v hv using hOnEx
  have hvsm : ∀ l (m : ℕ), ContDiffOn ℝ m (v l)
      (Work.CR.Flat.polydisc (0 : Work.NN.Core.Cn n) (fun _ => r * (1 - δ))) := by
    intro l m
    have h := (hv l).1 m
    rwa [hrd] at h
  have hvsol : ∀ l k z,
      z ∈ Work.CR.Flat.polydisc (0 : Work.NN.Core.Cn n) (fun _ => r * (1 - δ)) →
      Work.CR.Flat.dbarCoord k (v l) z = G l k z := by
    intro l k z hz
    have h := (hv l).2.1 k z
    rw [hrd] at h
    exact h hz
  have hvbd : ∀ l, Work.CR.Flat.holderNorm 2 α (v l)
        (Work.CR.Flat.polydisc (0 : Work.NN.Core.Cn n) (fun _ => r * (1 - δ)))
      ≤ ENNReal.ofReal (Co / ((δ / 2) / (1 - δ / 2)) ^ N1) *
        ∑ q : Fin n, Work.CR.Flat.holderNorm 1 α (G l q)
          (Work.CR.Flat.polydisc (0 : Work.NN.Core.Cn n) (fun _ => r * (1 - δ / 2))) := by
    intro l
    have h := (hv l).2.2
    rwa [hrd] at h
  refine ⟨v, hvsm, ?_, ?_⟩
  · intro l
    calc Work.CR.Flat.holderNorm 2 α (v l)
          (Work.CR.Flat.polydisc (0 : Work.NN.Core.Cn n) (fun _ => r * (1 - δ)))
        ≤ ENNReal.ofReal (Co / ((δ / 2) / (1 - δ / 2)) ^ N1) *
            ∑ q : Fin n, Work.CR.Flat.holderNorm 1 α (G l q)
              (Work.CR.Flat.polydisc (0 : Work.NN.Core.Cn n) (fun _ => r * (1 - δ / 2))) :=
          hvbd l
      _ ≤ ENNReal.ofReal (Co / ((δ / 2) / (1 - δ / 2)) ^ N1) *
            ENNReal.ofReal ((n : ℝ) * (a / 2 + T)) :=
          mul_le_mul_of_nonneg_left (hsum l) (by simp)
      _ = ENNReal.ofReal (Co / ((δ / 2) / (1 - δ / 2)) ^ N1
            * ((n : ℝ) * (a / 2 + T))) := by
          rw [← ENNReal.ofReal_mul (by positivity)]
      _ ≤ ENNReal.ofReal (C / δ ^ N * a) := ENNReal.ofReal_le_ofReal hfin
  · intro l k
    have heq : Set.EqOn
        (fun z => Work.CR.Flat.dbarCoord k (v l) z
          - Work.NN.Core.Lcoef A (fun y => y l) k z)
        (fun z => - ψ l k z)
        (Work.CR.Flat.polydisc (0 : Work.NN.Core.Cn n) (fun _ => r * (1 - δ))) := by
      intro z hz
      dsimp only
      have h := hvsol l k z hz
      have h' : Work.CR.Flat.dbarCoord k (v l) z
          = Work.NN.Core.Lcoef A (fun y => y l) k z - ψ l k z := by
        rw [h]
        simp only [G, coordDatum]
      rw [h']
      ring
    calc Work.CR.Flat.holderNorm 1 α
          (fun z => Work.CR.Flat.dbarCoord k (v l) z
            - Work.NN.Core.Lcoef A (fun y => y l) k z)
          (Work.CR.Flat.polydisc (0 : Work.NN.Core.Cn n) (fun _ => r * (1 - δ)))
        = Work.CR.Flat.holderNorm 1 α (fun z => - ψ l k z)
            (Work.CR.Flat.polydisc (0 : Work.NN.Core.Cn n) (fun _ => r * (1 - δ))) :=
          Work.NN.Final.holderNorm_congr_of_eqOn heq 1 α
      _ = Work.CR.Flat.holderNorm 1 α (ψ l k)
            (Work.CR.Flat.polydisc (0 : Work.NN.Core.Cn n) (fun _ => r * (1 - δ))) := by
          rw [show (fun z : Work.NN.Core.Cn n => - ψ l k z) = -(ψ l k) from rfl,
            Work.CR.Flat.Holder.holderNorm_neg ((hψsm l k 1).mono hPoPm) hPo_open.uniqueDiffOn]
      _ ≤ Work.CR.Flat.holderNorm 1 α (ψ l k)
            (Work.CR.Flat.polydisc (0 : Work.NN.Core.Cn n) (fun _ => r * (1 - δ / 2))) :=
          Work.CR.Flat.holderNorm_mono_set hPm_open hPo_open hPoPm 1 α _
      _ ≤ ENNReal.ofReal T := hψT l k
      _ ≤ ENNReal.ofReal (C / δ ^ N * a ^ 2) := ENNReal.ofReal_le_ofReal hT

end Work.NN.Newton
