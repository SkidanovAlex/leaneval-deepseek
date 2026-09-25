import Mathlib
import Submission.Work.NN.Assemble.flatTwoLossless
import Submission.Work.NN.Core.bmPot_riesz_Ck
import Submission.Work.NN.Core.bmPotential_gain
import Submission.Work.NN.Core.exists_holderNorm_wirtinger_le
import Submission.Work.NN.Core.bmPotential_dCoord_eq
import Submission.Work.NN.Core.contDiff_one_bmPotential_of_holder
import Submission.Work.CR.Flat.Holder.contDiffOn_succ_of_wirtinger
import Submission.Work.CR.Flat.Holder.holderNorm_neg
import Submission.Work.CR.Flat.Cauchy.bmCz.bmPot_dCoord
import Submission.Work.NN.Final.bmPot_contDiff_succ

namespace Work.NN.Final

open scoped NNReal ENNReal ContDiff
open Set MeasureTheory
open Work.CR.Flat Work.CR.Flat.Cauchy

variable {n : ℕ}

/-! ## Elementary vanishings and product bounds -/

/-- `∂̄_a χ` vanishes off `pd n ρ 3` when `tsupport χ ⊆ pd n ρ 3`. -/
lemma dbarCoord_eq_zero_of_notMem_pd {n : ℕ} {ρ : Fin n → ℝ} {χ : (Fin n → ℂ) → ℂ}
    (htsupp : tsupport χ ⊆ pd n ρ 3) (a : Fin n) {z : Fin n → ℂ} (hz : z ∉ pd n ρ 3) :
    dbarCoord a χ z = 0 := by
  by_contra hne
  refine hz (htsupp (Work.NN.Assemble.FT.tsupport_dbarCoord_subset a ?_))
  exact subset_tsupport _ (Function.mem_support.mpr hne)

/-- The product of `χ` (smooth, compactly supported in `pd n ρ 3`) with a function that is `C^k`
on `pd n ρ 4` has finite `C^{k,α}`-norm on `ℂⁿ`, bounded by the `C^{k,α}`-norm of the function on
`pd n ρ 4`. -/
lemma holderNorm_chi_mul_univ_le {n : ℕ} {ρ : Fin n → ℝ} (hρ : ∀ j, 0 < ρ j)
    {χ : (Fin n → ℂ) → ℂ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hcs : HasCompactSupport χ)
    (htsupp : tsupport χ ⊆ pd n ρ 3) {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (k : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ f : (Fin n → ℂ) → ℂ, ContDiffOn ℝ k f (pd n ρ 4) →
      holderNorm k α (fun w => χ w * f w) Set.univ
        ≤ ENNReal.ofReal C * holderNorm k α f (pd n ρ 4) := by
  obtain ⟨C, hCpos, hC⟩ := Work.CR.Flat.Cauchy.holderNorm_mul_le_of_hasCompactSupport
    (Ω := pd n ρ 4) (isOpen_pd ρ 4).uniqueDiffOn hα0 hα1 (hχ.of_le (by simp)) hcs
  refine ⟨C, hCpos, fun f hf => ?_⟩
  refine (Work.CR.Flat.Cauchy.holderNorm_univ_le_holderNorm_polydisc_of_vanishing
    (c := 0) (r := fun j => 3 * ρ j) (r' := fun j => 4 * ρ j) (fun j => by linarith [hρ j])
    hα0 (fun z hz => ?_)).trans (hC f hf)
  obtain ⟨i, hi⟩ := hz
  simp only [Pi.zero_apply, sub_zero] at hi
  rw [Work.NN.Assemble.FT.chi_eq_zero_of_notMem_pd3 htsupp
    (Work.NN.Assemble.FT.notMem_pd_of_three_le ⟨i, hi⟩), zero_mul]

/-- The product of `∂̄_a χ` (smooth, compactly supported in `pd n ρ 3`) with a function that is
`C^k` on `pd n ρ 4` has finite `C^{k,α}`-norm on `ℂⁿ`, uniformly in `a`, bounded by the
`C^{k,α}`-norm of the function on `pd n ρ 4`. -/
lemma holderNorm_dbarCoord_mul_univ_le {n : ℕ} {ρ : Fin n → ℝ} (hρ : ∀ j, 0 < ρ j)
    {χ : (Fin n → ℂ) → ℂ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hcs : HasCompactSupport χ)
    (htsupp : tsupport χ ⊆ pd n ρ 3) {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (k : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (a : Fin n) (f : (Fin n → ℂ) → ℂ), ContDiffOn ℝ k f (pd n ρ 4) →
      holderNorm k α (fun w => dbarCoord a χ w * f w) Set.univ
        ≤ ENNReal.ofReal C * holderNorm k α f (pd n ρ 4) := by
  have hper : ∀ a : Fin n, ∃ Ca : ℝ, 0 < Ca ∧ ∀ f : (Fin n → ℂ) → ℂ,
      ContDiffOn ℝ k f (pd n ρ 4) →
      holderNorm k α (fun w => dbarCoord a χ w * f w) (pd n ρ 4)
        ≤ ENNReal.ofReal Ca * holderNorm k α f (pd n ρ 4) := fun a =>
    Work.CR.Flat.Cauchy.holderNorm_mul_le_of_hasCompactSupport (Ω := pd n ρ 4)
      (isOpen_pd ρ 4).uniqueDiffOn hα0 hα1
      ((Work.NN.Assemble.FT.contDiff_dbarCoord_of hχ a).of_le (by simp))
      (Work.NN.Assemble.FT.hasCompactSupport_dbarCoord hcs a)
  choose Cd hCdpos hCd using hper
  have hsumpos : 0 < ∑ a : Fin n, Cd a + 1 := by
    have h := Finset.sum_nonneg (fun a (_ : a ∈ Finset.univ) => le_of_lt (hCdpos a))
    linarith
  refine ⟨∑ a, Cd a + 1, hsumpos, ?_⟩
  intro a f hf
  refine (Work.CR.Flat.Cauchy.holderNorm_univ_le_holderNorm_polydisc_of_vanishing
    (c := 0) (r := fun j => 3 * ρ j) (r' := fun j => 4 * ρ j) (fun j => by linarith [hρ j])
    hα0 (fun z hz => ?_)).trans ((hCd a f hf).trans ?_)
  · obtain ⟨i, hi⟩ := hz
    simp only [Pi.zero_apply, sub_zero] at hi
    rw [dbarCoord_eq_zero_of_notMem_pd htsupp a
      (Work.NN.Assemble.FT.notMem_pd_of_three_le ⟨i, hi⟩), zero_mul]
  · refine mul_le_mul_left (ENNReal.ofReal_le_ofReal ?_) _
    have h1 := Finset.single_le_sum (f := fun a : Fin n => Cd a)
      (fun i _ => le_of_lt (hCdpos i)) (Finset.mem_univ a)
    linarith

/-- Every component of `bmH χ η j l ·` has finite `C^{k,α}`-norm on `ℂⁿ`, bounded (uniformly in
`j l i`) by the `C^{k,α}`-norm of `η` on `pd n ρ 4`. -/
lemma bmH_holderNorm_univ_le {n : ℕ} {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    {ρ : Fin n → ℝ} (hρ : ∀ j, 0 < ρ j) {χ : (Fin n → ℂ) → ℂ}
    (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hcs : HasCompactSupport χ)
    (htsupp : tsupport χ ⊆ pd n ρ 3) (k : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ η : Fin n → Fin n → (Fin n → ℂ) → ℂ,
      (∀ i l, ContDiffOn ℝ k (η i l) (pd n ρ 4)) → ∀ j l i : Fin n,
        holderNorm k α (fun w => Work.NN.Core.bmH χ η j l i w) Set.univ
          ≤ ENNReal.ofReal C
              * (∑ r : Fin n, ∑ s : Fin n, holderNorm k α (η r s) (pd n ρ 4)) := by
  have htsupp4 : tsupport χ ⊆ pd n ρ 4 := htsupp.trans (pd_mono hρ (by norm_num))
  obtain ⟨Cd, hCdpos, hCd⟩ :=
    holderNorm_dbarCoord_mul_univ_le (n := n) hρ hχ hcs htsupp hα0.le hα1.le k
  have hCpos : 0 < 3 * Cd + 1 := by linarith
  refine ⟨3 * Cd + 1, hCpos, ?_⟩
  intro η hη j l i
  set S : ℝ≥0∞ := ∑ r : Fin n, ∑ s : Fin n, holderNorm k α (η r s) (pd n ρ 4) with hSdef
  have hpr : ∀ (a b c : Fin n), holderNorm k α (fun w => dbarCoord a χ w * η b c w) Set.univ
      ≤ ENNReal.ofReal Cd * S := by
    intro a b c
    refine (hCd a (η b c) (hη b c)).trans (mul_le_mul_right ?_ _)
    rw [hSdef]
    exact le_trans
      (Finset.single_le_sum (f := fun s : Fin n => holderNorm k α (η b s) (pd n ρ 4))
        (fun _ _ => zero_le) (Finset.mem_univ c))
      (Finset.single_le_sum
        (f := fun r : Fin n => ∑ s : Fin n, holderNorm k α (η r s) (pd n ρ 4))
        (fun _ _ => zero_le) (Finset.mem_univ b))
  have hsm : ∀ (a b c : Fin n),
      ContDiff ℝ k (fun w => dbarCoord a χ w * η b c w) := fun a b c =>
    Work.NN.Assemble.FT.contDiff_dbarCoord_mul hχ htsupp4 (hη b c) a
  have hfun : (fun w => Work.NN.Core.bmH χ η j l i w)
      = (fun w => dbarCoord i χ w * η j l w)
        + ((fun w => dbarCoord j χ w * η l i w)
            + -(fun w => dbarCoord l χ w * η j i w)) := by
    funext w
    rw [Work.NN.Assemble.FT.bmH_eq_sum]
    simp only [Pi.add_apply, Pi.neg_apply, Pi.sub_apply]
    ring
  have h1 := Work.CR.Flat.Holder.holderNorm_add_le
    (f := fun w => dbarCoord i χ w * η j l w)
    (g := (fun w => dbarCoord j χ w * η l i w) + -(fun w => dbarCoord l χ w * η j i w))
    (Ω := Set.univ) (α := α) (hsm i j l).contDiffOn
    ((hsm j l i).add (hsm l j i).neg).contDiffOn isOpen_univ.uniqueDiffOn
  have h2 := Work.CR.Flat.Holder.holderNorm_add_le
    (f := fun w => dbarCoord j χ w * η l i w)
    (g := -(fun w => dbarCoord l χ w * η j i w))
    (Ω := Set.univ) (α := α) (hsm j l i).contDiffOn ((hsm l j i).neg).contDiffOn
    isOpen_univ.uniqueDiffOn
  have hneg := Work.CR.Flat.Holder.holderNorm_neg
    (f := fun w => dbarCoord l χ w * η j i w) (Ω := Set.univ) (α := α)
    (hsm l j i).contDiffOn isOpen_univ.uniqueDiffOn
  have hthree : ENNReal.ofReal Cd * S + (ENNReal.ofReal Cd * S + ENNReal.ofReal Cd * S)
      = ENNReal.ofReal (3 * Cd) * S := by
    have h3 : ENNReal.ofReal (3 : ℝ) = (3 : ℝ≥0∞) := by norm_num
    rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 3), h3]
    ring
  calc holderNorm k α (fun w => Work.NN.Core.bmH χ η j l i w) Set.univ
      = holderNorm k α ((fun w => dbarCoord i χ w * η j l w)
          + ((fun w => dbarCoord j χ w * η l i w)
              + -(fun w => dbarCoord l χ w * η j i w))) Set.univ := by rw [hfun]
    _ ≤ holderNorm k α (fun w => dbarCoord i χ w * η j l w) Set.univ
          + holderNorm k α ((fun w => dbarCoord j χ w * η l i w)
              + -(fun w => dbarCoord l χ w * η j i w)) Set.univ := h1
    _ ≤ ENNReal.ofReal Cd * S + (ENNReal.ofReal Cd * S + ENNReal.ofReal Cd * S) :=
        add_le_add (hpr i j l)
          (h2.trans (add_le_add (hpr j l i) (by rw [hneg]; exact hpr l j i)))
    _ = ENNReal.ofReal (3 * Cd) * S := hthree
    _ ≤ ENNReal.ofReal (3 * Cd + 1) * S := by
        refine mul_le_mul_left (ENNReal.ofReal_le_ofReal ?_) _
        linarith

/-- **The Bochner–Martinelli part of the relaxed estimate.**  For data `η` of class `C^k` on
`pd n ρ 4` and with finite `C^{k,α}`-norm there, `bmRow (χ · η) j` is `C^{k+1}` on `pd n ρ 2`
and its `C^{k+1,α}`-norm there is bounded by the `C^{k,α}`-norm of `η` on `pd n ρ 4`. -/
lemma bmRow_contDiffOn_holderNorm_le {n : ℕ} (hn : 0 < n) {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    {ρ : Fin n → ℝ} (hρ : ∀ j, 0 < ρ j) {χ : (Fin n → ℂ) → ℂ}
    (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hcs : HasCompactSupport χ)
    (htsupp : tsupport χ ⊆ pd n ρ 3) (k : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ η : Fin n → Fin n → (Fin n → ℂ) → ℂ,
      (∀ i l, ContDiffOn ℝ k (η i l) (pd n ρ 4)) →
      (∀ i l, holderNorm k α (η i l) (pd n ρ 4) < ⊤) → ∀ j : Fin n,
        ContDiffOn ℝ (k + 1) (Work.NN.Core.bmRow (fun a b w => χ w * η a b w) j) (pd n ρ 2) ∧
        holderNorm (k + 1) α (Work.NN.Core.bmRow (fun a b w => χ w * η a b w) j) (pd n ρ 2)
          ≤ ENNReal.ofReal C
              * (∑ r : Fin n, ∑ s : Fin n, holderNorm k α (η r s) (pd n ρ 4)) := by
  have htsupp4 : tsupport χ ⊆ pd n ρ 4 := htsupp.trans (pd_mono hρ (by norm_num))
  obtain ⟨Cχ, hCχpos, hCχ⟩ :=
    holderNorm_chi_mul_univ_le (n := n) hρ hχ hcs htsupp hα0.le hα1.le k
  obtain ⟨Cg, hCgpos, hCg⟩ := Work.NN.Core.bmPotential_gain (n := n) hn hα0 hα1
    (ρ := fun i => 3 * ρ i) (fun i => by linarith [hρ i]) k
  set Cst : ℝ := ‖(Work.CR.Flat.Cauchy.bmGamma n)⁻¹‖ * Cg * (n : ℝ) * Cχ + 1 with hCstdef
  have hCstpos : 0 < Cst := by
    rw [hCstdef]; positivity
  refine ⟨Cst, hCstpos, ?_⟩
  intro η hη hfin j
  set S : ℝ≥0∞ := ∑ r : Fin n, ∑ s : Fin n, holderNorm k α (η r s) (pd n ρ 4) with hSdef
  set f : Fin n → (Fin n → ℂ) → ℂ := fun l w => χ w * η j l w with hfdef
  have hSlt : S < ⊤ := by
    rw [hSdef, ENNReal.sum_lt_top]
    intro r _
    rw [ENNReal.sum_lt_top]
    intro s _
    exact hfin r s
  have hfsm : ∀ l, ContDiff ℝ k (f l) := fun l =>
    Work.NN.Final.contDiff_mul_of_contDiffOn_tsupport (isOpen_pd ρ 4) hχ htsupp4 (hη j l)
  have hfcs : ∀ l, HasCompactSupport (f l) := fun l => hcs.mul_right
  have hfterm : ∀ l, holderNorm k α (f l) Set.univ ≤ ENNReal.ofReal Cχ * S := by
    intro l
    refine (hCχ (η j l) (hη j l)).trans (mul_le_mul_right ?_ _)
    rw [hSdef]
    exact le_trans
      (Finset.single_le_sum (f := fun s : Fin n => holderNorm k α (η j s) (pd n ρ 4))
        (fun _ _ => zero_le) (Finset.mem_univ l))
      (Finset.single_le_sum
        (f := fun r : Fin n => ∑ s : Fin n, holderNorm k α (η r s) (pd n ρ 4))
        (fun _ _ => zero_le) (Finset.mem_univ j))
  have hffin : ∀ l, holderNorm k α (f l) Set.univ < ⊤ := fun l =>
    lt_of_le_of_lt (hfterm l) (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hSlt)
  have hfvan : ∀ l z, (∃ i, 3 * ρ i ≤ ‖z i‖) → f l z = 0 := by
    intro l z hz
    obtain ⟨i, hi⟩ := hz
    simp only [hfdef]
    rw [Work.NN.Assemble.FT.chi_eq_zero_of_notMem_pd3 htsupp
      (Work.NN.Assemble.FT.notMem_pd_of_three_le ⟨i, hi⟩), zero_mul]
  obtain ⟨hgcd, hgbd⟩ := hCg f hfsm hfcs hffin hfvan
  have hsum : (∑ l : Fin n, holderNorm k α (f l) Set.univ)
      ≤ (n : ℝ≥0∞) * (ENNReal.ofReal Cχ * S) := by
    calc (∑ l : Fin n, holderNorm k α (f l) Set.univ)
        ≤ ∑ _l : Fin n, ENNReal.ofReal Cχ * S := Finset.sum_le_sum fun l _ => hfterm l
      _ = (Fintype.card (Fin n) : ℝ≥0∞) * (ENNReal.ofReal Cχ * S) := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      _ = (n : ℝ≥0∞) * (ENNReal.ofReal Cχ * S) := by rw [Fintype.card_fin]
  have hdef : Work.NN.Core.bmRow (fun a b w => χ w * η a b w) j
      = fun z => -((Work.CR.Flat.Cauchy.bmGamma n)⁻¹)
          * Work.CR.Flat.Cauchy.bmPot (fun l => f l) z := by
    funext z
    simp only [Work.NN.Core.bmRow_apply, hfdef]
  have hcd_pot : ContDiffOn ℝ (k + 1) (Work.CR.Flat.Cauchy.bmPot (fun l => f l)) (pd n ρ 3) := by
    rw [bmPot_eq_bmPotential (fun l => f l)]
    exact hgcd
  have hcd : ContDiffOn ℝ (k + 1) (Work.NN.Core.bmRow (fun a b w => χ w * η a b w) j)
      (pd n ρ 2) := by
    rw [hdef]
    exact (contDiffOn_const.mul hcd_pot).mono (pd_mono hρ (by norm_num : (2 : ℝ) ≤ 3))
  refine ⟨hcd, ?_⟩
  have hsmul : holderNorm (k + 1) α
        (fun z => -((Work.CR.Flat.Cauchy.bmGamma n)⁻¹)
          * Work.CR.Flat.Cauchy.bmPot (fun l => f l) z) (pd n ρ 3)
      = ENNReal.ofReal ‖(Work.CR.Flat.Cauchy.bmGamma n)⁻¹‖
          * holderNorm (k + 1) α (Work.CR.Flat.Cauchy.bmPot (fun l => f l)) (pd n ρ 3) := by
    have h2 : (fun z => -((Work.CR.Flat.Cauchy.bmGamma n)⁻¹)
          * Work.CR.Flat.Cauchy.bmPot (fun l => f l) z)
        = (-((Work.CR.Flat.Cauchy.bmGamma n)⁻¹))
            • (fun z => Work.CR.Flat.Cauchy.bmPot (fun l => f l) z) := by
      funext z; simp [Pi.smul_apply, smul_eq_mul]
    rw [h2, Work.CR.Flat.Holder.holderNorm_smul _ hcd_pot (isOpen_pd ρ 3).uniqueDiffOn,
      norm_neg]
  calc holderNorm (k + 1) α (Work.NN.Core.bmRow (fun a b w => χ w * η a b w) j) (pd n ρ 2)
      = holderNorm (k + 1) α (fun z => -((Work.CR.Flat.Cauchy.bmGamma n)⁻¹)
          * Work.CR.Flat.Cauchy.bmPot (fun l => f l) z) (pd n ρ 2) := by rw [hdef]
    _ ≤ holderNorm (k + 1) α (fun z => -((Work.CR.Flat.Cauchy.bmGamma n)⁻¹)
          * Work.CR.Flat.Cauchy.bmPot (fun l => f l) z) (pd n ρ 3) :=
        Work.CR.Flat.holderNorm_mono_set (isOpen_pd ρ 3) (isOpen_pd ρ 2)
          (pd_mono hρ (by norm_num : (2 : ℝ) ≤ 3)) (k + 1) α _
    _ = ENNReal.ofReal ‖(Work.CR.Flat.Cauchy.bmGamma n)⁻¹‖
          * holderNorm (k + 1) α (Work.CR.Flat.Cauchy.bmPot (fun l => f l)) (pd n ρ 3) := hsmul
    _ = ENNReal.ofReal ‖(Work.CR.Flat.Cauchy.bmGamma n)⁻¹‖
          * holderNorm (k + 1) α (Work.CR.Flat.Cauchy.bmPotential (fun l => f l)) (pd n ρ 3) := by
        rw [bmPot_eq_bmPotential (fun l => f l)]
    _ ≤ ENNReal.ofReal ‖(Work.CR.Flat.Cauchy.bmGamma n)⁻¹‖
          * (ENNReal.ofReal Cg * ((n : ℝ≥0∞) * (ENNReal.ofReal Cχ * S))) :=
        mul_le_mul_right (hgbd.trans (mul_le_mul_right hsum _)) _
    _ = ENNReal.ofReal (‖(Work.CR.Flat.Cauchy.bmGamma n)⁻¹‖ * Cg * (n : ℝ) * Cχ) * S := by
        rw [Work.NN.Assemble.FT.ennreal_reassoc]
        rw [← ENNReal.ofReal_natCast n]
        rw [← ENNReal.ofReal_mul (by positivity)]
        rw [← ENNReal.ofReal_mul (by positivity)]
        rw [← ENNReal.ofReal_mul (by positivity)]
    _ ≤ ENNReal.ofReal Cst * S := by
        rw [hCstdef]
        refine mul_le_mul_left (ENNReal.ofReal_le_ofReal ?_) _
        linarith

/-- **The defect part of the relaxed estimate.**  For data `η` of class `C^k` on `pd n ρ 4` with
finite `C^{k,α}`-norm there, the `∂̄`-closed defect `Edat χ η` is globally `C^{k+1}` and the
`C^{k+1,α}`-norm of `Edat χ η j l` on `pd n ρ (8/3)` is bounded by the `C^{k,α}`-norm of `η` on
`pd n ρ 4`. -/
lemma Edat_contDiff_holderNorm_le {n : ℕ} (hn : 0 < n) {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    {ρ : Fin n → ℝ} (hρ : ∀ j, 0 < ρ j) {χ : (Fin n → ℂ) → ℂ}
    (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hcs : HasCompactSupport χ)
    (htsupp : tsupport χ ⊆ pd n ρ 3) (k : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ η : Fin n → Fin n → (Fin n → ℂ) → ℂ,
      (∀ i l, ContDiffOn ℝ k (η i l) (pd n ρ 4)) →
      (∀ i l, holderNorm k α (η i l) (pd n ρ 4) < ⊤) → ∀ j l : Fin n,
        ContDiff ℝ (k + 1) (Work.NN.Assemble.FT.Edat χ η j l) ∧
        holderNorm (k + 1) α (Work.NN.Assemble.FT.Edat χ η j l) (pd n ρ (8 / 3 : ℝ))
          ≤ ENNReal.ofReal C
              * (∑ r : Fin n, ∑ s : Fin n, holderNorm k α (η r s) (pd n ρ 4)) := by
  have htsupp4 : tsupport χ ⊆ pd n ρ 4 := htsupp.trans (pd_mono hρ (by norm_num))
  obtain ⟨Cbm, hCbmpos, hCbm⟩ := bmH_holderNorm_univ_le (n := n) hα0 hα1 hρ hχ hcs htsupp k
  obtain ⟨Cg, hCgpos, hCg⟩ := Work.NN.Core.bmPotential_gain (n := n) hn hα0 hα1
    (ρ := fun i => 3 * ρ i) (fun i => by linarith [hρ i]) k
  set Cst : ℝ := ‖(Work.CR.Flat.Cauchy.bmGamma n)⁻¹‖ * Cg * (n : ℝ) * Cbm + 1 with hCstdef
  have hCstpos : 0 < Cst := by
    rw [hCstdef]; positivity
  refine ⟨Cst, hCstpos, ?_⟩
  intro η hη hfin j l
  set S : ℝ≥0∞ := ∑ r : Fin n, ∑ s : Fin n, holderNorm k α (η r s) (pd n ρ 4) with hSdef
  set g : Fin n → (Fin n → ℂ) → ℂ := fun i w => Work.NN.Core.bmH χ η j l i w with hgdef
  have hSlt : S < ⊤ := by
    rw [hSdef, ENNReal.sum_lt_top]
    intro r _
    rw [ENNReal.sum_lt_top]
    intro s _
    exact hfin r s
  have hgsm : ∀ i, ContDiff ℝ k (g i) := fun i =>
    Work.NN.Assemble.FT.contDiff_bmH hχ htsupp4 hη j l i
  have hgcs : ∀ i, HasCompactSupport (g i) := fun i =>
    Work.NN.Assemble.FT.bmH_hasCompactSupport hcs j l i
  have hgbd0 : ∀ i, holderNorm k α (g i) Set.univ ≤ ENNReal.ofReal Cbm * S := by
    intro i
    rw [hgdef]
    exact hCbm η hη j l i
  have hgfin : ∀ i, holderNorm k α (g i) Set.univ < ⊤ := fun i =>
    lt_of_le_of_lt (hgbd0 i) (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hSlt)
  have hgvan : ∀ i z, (∃ i', 3 * ρ i' ≤ ‖z i'‖) → g i z = 0 := by
    intro i z hz
    obtain ⟨i', hi'⟩ := hz
    have hz3 : z ∉ pd n ρ 3 := Work.NN.Assemble.FT.notMem_pd_of_three_le ⟨i', hi'⟩
    have h0 : ∀ a : Fin n, dbarCoord a χ z = 0 := fun a =>
      dbarCoord_eq_zero_of_notMem_pd htsupp a hz3
    simp only [hgdef]
    rw [Work.NN.Assemble.FT.bmH_eq_sum, h0 i, h0 j, h0 l]
    ring
  obtain ⟨hgcd, hgbd⟩ := hCg g hgsm hgcs hgfin hgvan
  have hsum : (∑ i : Fin n, holderNorm k α (g i) Set.univ)
      ≤ (n : ℝ≥0∞) * (ENNReal.ofReal Cbm * S) := by
    calc (∑ i : Fin n, holderNorm k α (g i) Set.univ)
        ≤ ∑ _i : Fin n, ENNReal.ofReal Cbm * S := Finset.sum_le_sum fun i _ => hgbd0 i
      _ = (Fintype.card (Fin n) : ℝ≥0∞) * (ENNReal.ofReal Cbm * S) := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      _ = (n : ℝ≥0∞) * (ENNReal.ofReal Cbm * S) := by rw [Fintype.card_fin]
  have hPot : ContDiff ℝ (k + 1) (Work.CR.Flat.Cauchy.bmPot g) :=
    bmPot_contDiff_succ hn hα0 hα1 k g hgsm hgcs hgfin
  have hEdat : Work.NN.Assemble.FT.Edat χ η j l
      = fun z => (Work.CR.Flat.Cauchy.bmGamma n)⁻¹ * Work.CR.Flat.Cauchy.bmPot g z := by
    funext z
    rw [Work.NN.Assemble.FT.Edat_apply]
  refine ⟨?_, ?_⟩
  · rw [hEdat]
    exact contDiff_const.mul hPot
  · have hPot' : ContDiffOn ℝ (k + 1) (Work.CR.Flat.Cauchy.bmPot g) (pd n ρ (8 / 3 : ℝ)) :=
      hPot.contDiffOn
    have hsmul : holderNorm (k + 1) α
          (fun z => (Work.CR.Flat.Cauchy.bmGamma n)⁻¹ * Work.CR.Flat.Cauchy.bmPot g z)
          (pd n ρ (8 / 3 : ℝ))
        = ENNReal.ofReal ‖(Work.CR.Flat.Cauchy.bmGamma n)⁻¹‖
            * holderNorm (k + 1) α (Work.CR.Flat.Cauchy.bmPot g) (pd n ρ (8 / 3 : ℝ)) := by
      have h2 : (fun z => (Work.CR.Flat.Cauchy.bmGamma n)⁻¹ * Work.CR.Flat.Cauchy.bmPot g z)
          = ((Work.CR.Flat.Cauchy.bmGamma n)⁻¹)
              • (fun z => Work.CR.Flat.Cauchy.bmPot g z) := by
        funext z; simp [Pi.smul_apply, smul_eq_mul]
      rw [h2, Work.CR.Flat.Holder.holderNorm_smul _ hPot'
        (isOpen_pd ρ (8 / 3)).uniqueDiffOn]
    calc holderNorm (k + 1) α (Work.NN.Assemble.FT.Edat χ η j l) (pd n ρ (8 / 3 : ℝ))
        = holderNorm (k + 1) α
            (fun z => (Work.CR.Flat.Cauchy.bmGamma n)⁻¹
              * Work.CR.Flat.Cauchy.bmPot g z) (pd n ρ (8 / 3 : ℝ)) := by rw [hEdat]
      _ = ENNReal.ofReal ‖(Work.CR.Flat.Cauchy.bmGamma n)⁻¹‖
            * holderNorm (k + 1) α (Work.CR.Flat.Cauchy.bmPot g) (pd n ρ (8 / 3 : ℝ)) := hsmul
      _ ≤ ENNReal.ofReal ‖(Work.CR.Flat.Cauchy.bmGamma n)⁻¹‖
            * holderNorm (k + 1) α (Work.CR.Flat.Cauchy.bmPot g) (pd n ρ 3) :=
          mul_le_mul_right (Work.CR.Flat.holderNorm_mono_set (isOpen_pd ρ 3)
            (isOpen_pd ρ (8 / 3)) (pd_mono hρ (by norm_num : (8 / 3 : ℝ) ≤ 3)) (k + 1) α _) _
      _ = ENNReal.ofReal ‖(Work.CR.Flat.Cauchy.bmGamma n)⁻¹‖
            * holderNorm (k + 1) α (Work.CR.Flat.Cauchy.bmPotential g) (pd n ρ 3) := by
          rw [bmPot_eq_bmPotential g]
      _ ≤ ENNReal.ofReal ‖(Work.CR.Flat.Cauchy.bmGamma n)⁻¹‖
            * (ENNReal.ofReal Cg * ((n : ℝ≥0∞) * (ENNReal.ofReal Cbm * S))) :=
          mul_le_mul_right (hgbd.trans (mul_le_mul_right hsum _)) _
      _ = ENNReal.ofReal (‖(Work.CR.Flat.Cauchy.bmGamma n)⁻¹‖ * Cg * (n : ℝ) * Cbm) * S := by
          rw [Work.NN.Assemble.FT.ennreal_reassoc]
          rw [← ENNReal.ofReal_natCast n]
          rw [← ENNReal.ofReal_mul (by positivity)]
          rw [← ENNReal.ofReal_mul (by positivity)]
          rw [← ENNReal.ofReal_mul (by positivity)]
      _ ≤ ENNReal.ofReal Cst * S := by
          rw [hCstdef]
          refine mul_le_mul_left (ENNReal.ofReal_le_ofReal ?_) _
          linarith

/-- **The relaxed (`C^k`-data) estimate for the flat `(0,2)`-solution operator of the
Newlander–Nirenberg assembly.**

For a fixed smooth cutoff `χ` supported in `pd n ρ 3`, the operator
`η ↦ bmRow (χ · η) + tfin ρ (Edat χ η)` (the explicit formula behind `T2lin`/`T2` of
`Work.NN.Assemble.FT`) gains exactly one derivative in the `C^{k,α}` scale with *no* loss in the
data hypothesis: the datum is only required to be `C^k` on `pd n ρ 4` (not `C^{k+1}`), and the
right-hand side is the `C^{k,α}`-norm of the datum on `pd n ρ 4`.

This is the relaxation of the estimate `hconst` proved inside
`Work.NN.Assemble.FT.twoCoreMine` (`Assemble/flatTwoLossless.lean`), where the same conclusion is
obtained under the stronger hypothesis `ContDiffOn ℝ (k+1) (η i l) (pd n ρ 4)`.  No antisymmetry
and no closedness of the datum are needed (again as in `hconst`).

PROOF PLAN (mirror the proof of `hconst`, replacing the two lossy inputs):

* Trivial case: if `∑ i, ∑ l, holderNorm k α (η i l) (pd n ρ 4) = ⊤` the right-hand side is `⊤`
  (the constant is positive), so there is nothing to prove.  Hence assume it is finite; then each
  `η i l` has finite `C^{k,α}`-norm on `pd n ρ 4`.
* The Bochner–Martinelli part `bmRow (χ · η)` is `-γ⁻¹ bmPot ((χ·η)_{j·})`.  Here `χ · η` is
  *globally* `C^k` (temporarily assume `k ≥ 1`, or use `contDiff_mul_of_contDiffOn_tsupp` for
  `k = 0` on the continuity level), compactly supported in `pd n ρ 3`, and
  `holderNorm k α (χ * η a b) univ ≤ C (Σ_i Σ_l holderNorm k α (η i l) (pd n ρ 4))` by the
  product estimate (`holderNorm_mul_le_of_hasCompactSupport`, as in the proof of
  `Work.NN.Core.bmRowCutoffEstimate`).  Instead of the lossy `Work.NN.Core.bmRow_holder`
  (`C^{k+1}`-data) use `Work.NN.Core.bmPot_riesz_Ck` (proved, sorry-free) with centre `0` and
  radii `6ρ`: it bounds `holderNorm (k+1) α (bmPot (χ·η)) (polydisc 0 (3ρ))` by the
  `C^{k,α}`-norm of `χ·η` on `univ`, and `pd n ρ 2 ⊆ polydisc 0 (3ρ)` by monotonicity.
  (The proof of `bmRowCutoffEstimate` shows exactly how to package the support/radius bookkeeping.)
* The defect part: `Edat χ η = γ⁻¹ bmPot (bmH χ η)` where
  `bmH χ η j l i = dbarCoord i χ · η j l + dbarCoord j χ · η l i - dbarCoord l χ · η j i`
  (`bmH_eq_sum`) is a sum of products of fixed smooth compactly supported functions with the
  components of `η`; hence `bmH χ η j l i` is *globally* `C^k` (using
  `contDiff_mul_of_contDiffOn_tsupp`), compactly supported, with
  `holderNorm k α (bmH χ η j l i) univ ≤ C (Σ Σ holderNorm k α (η))`.
  Apply `Work.NN.Core.bmPotential_gain` (proved, sorry-free) with `N := k`, `ρ := (8/3)ρ`
  (support hypothesis: `bmH` vanishes where some coordinate reaches `3ρ ≥ (8/3)ρ`): it gives
  `ContDiffOn ℝ (k+1) (Edat χ η j l) (pd n ρ (8/3))` together with the bound
  `holderNorm (k+1) α (Edat χ η j l) (pd n ρ (8/3)) ≤ C (Σ Σ holderNorm k α (η))`
  (monotonicity of `holderNorm` in the set handles the polydisc `polydisc 0 ((8/3)ρ)`).
* `tfin_bound` (proved, in `flatTwoLossless.lean`) at order `k+1` gives
  `holderNorm (k+1) α (tfin ρ (Edat χ η) j) (pd n ρ 2) ≤
     ofReal Ct * Σ i Σ l holderNorm (k+1) α (Edat χ η i l) (polydisc 0 (sgm ρ))`
  — note it needs `∀ i l, ContDiff ℝ (k+1) (Edat χ η i l)` *globally*: obtain this from the
  local `ContDiffOn` of `bmPotential_gain` on `pd n ρ (8/3) ⊇ tsupport (bmH χ η)` together with
  the global smoothness of the potential away from the support of its datum
  (`Work.NN.Core.bmPot_smooth_harmonic_of_vanish`, or `contDiff_bmPotential_Ck`-style lemmas)
  and the gluing `contDiff_of_locally`/`ContDiffAt` criterion; alternatively use the directly
  available `Work.NN.Core.contDiff_one_bmPotential_of_holder` for `k = 0`.
* Assemble with `Work.CR.Flat.Holder.holderNorm_add_le` (the summands are `ContDiffOn ℝ (k+1)`,
  available from the above), `Finset.sum_le_sum`, `sum_const_ofReal_mul`, and the same
  `ℝ≥0∞` arithmetic as in `hconst` (`ENNReal.ofReal_mul`, `mul_assoc`, `add_mul`). -/
theorem bmRow_tfin_relaxed {n : ℕ} (hn : 0 < n) {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    {ρ : Fin n → ℝ} (hρ : ∀ j, 0 < ρ j)
    (χ : (Fin n → ℂ) → ℂ) (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hcs : HasCompactSupport χ)
    (htsupp : tsupport χ ⊆ Work.NN.Final.pd n ρ 3) :
    ∃ C : ℕ → ℝ, (∀ k, 0 < C k) ∧
      ∀ (k : ℕ) (η : Fin n → Fin n → (Fin n → ℂ) → ℂ),
        (∀ i l, ContDiffOn ℝ k (η i l) (Work.NN.Final.pd n ρ 4)) →
        ∀ j : Fin n,
          Work.CR.Flat.holderNorm (k + 1) α
              ((Work.NN.Core.bmRow (fun a b w => χ w * η a b w)
                + Work.NN.Assemble.FT.tfin ρ (Work.NN.Assemble.FT.Edat χ η)) j)
              (Work.NN.Final.pd n ρ 2)
            ≤ ENNReal.ofReal (C k) * ∑ i, ∑ l,
                Work.CR.Flat.holderNorm k α (η i l) (Work.NN.Final.pd n ρ 4) := by
  have hmain : ∀ k : ℕ, ∃ Ck : ℝ, 0 < Ck ∧
      ∀ (η : Fin n → Fin n → (Fin n → ℂ) → ℂ),
        (∀ i l, ContDiffOn ℝ k (η i l) (pd n ρ 4)) → ∀ j : Fin n,
          holderNorm (k + 1) α ((Work.NN.Core.bmRow (fun a b w => χ w * η a b w)
            + Work.NN.Assemble.FT.tfin ρ (Work.NN.Assemble.FT.Edat χ η)) j) (pd n ρ 2)
            ≤ ENNReal.ofReal Ck * ∑ i, ∑ l, holderNorm k α (η i l) (pd n ρ 4) := by
    intro k
    obtain ⟨Cb, hCbpos, hCb⟩ :=
      bmRow_contDiffOn_holderNorm_le (n := n) hn hα0 hα1 hρ hχ hcs htsupp k
    obtain ⟨Ce, hCepos, hCe⟩ :=
      Edat_contDiff_holderNorm_le (n := n) hn hα0 hα1 hρ hχ hcs htsupp k
    obtain ⟨Ct, hCtpos, hCt⟩ := Work.NN.Assemble.FT.tfin_bound (n := n) hα0 hα1 hρ (k + 1)
    refine ⟨Cb + Ct * (n : ℝ) * (n : ℝ) * Ce, by positivity, ?_⟩
    intro η hη j
    set S : ℝ≥0∞ := ∑ r : Fin n, ∑ s : Fin n, holderNorm k α (η r s) (pd n ρ 4) with hSdef
    by_cases htop : S = ⊤
    · rw [htop, ENNReal.mul_top (by rw [ENNReal.ofReal_ne_zero_iff]; positivity)]
      exact le_top
    have hSlt : S < ⊤ := lt_top_iff_ne_top.mpr htop
    have hfin : ∀ i l, holderNorm k α (η i l) (pd n ρ 4) < ⊤ := fun i l =>
      (ENNReal.sum_lt_top.mp ((ENNReal.sum_lt_top.mp hSlt) i (Finset.mem_univ i))) l
        (Finset.mem_univ l)
    obtain ⟨hAcd, hAbd⟩ := hCb η hη hfin j
    have hEcd : ∀ i l, ContDiff ℝ (k + 1) (Work.NN.Assemble.FT.Edat χ η i l) :=
      fun i l => (hCe η hη hfin i l).1
    have hEbd : ∀ i l, holderNorm (k + 1) α (Work.NN.Assemble.FT.Edat χ η i l)
          (Work.CR.Flat.polydisc 0 (Work.NN.Assemble.FT.sgm ρ))
        ≤ ENNReal.ofReal Ce * S := by
      intro i l
      have hset : Work.CR.Flat.polydisc 0 (Work.NN.Assemble.FT.sgm ρ) = pd n ρ (8 / 3 : ℝ) := rfl
      rw [hset]
      exact (hCe η hη hfin i l).2
    have hBcd : ContDiffOn ℝ (k + 1)
        (Work.NN.Assemble.FT.tfin ρ (Work.NN.Assemble.FT.Edat χ η) j) (pd n ρ 2) :=
      (Work.NN.Assemble.FT.contDiff_tfin hEcd j).contDiffOn
    have hsumE : (∑ i : Fin n, ∑ l : Fin n, holderNorm (k + 1) α
          (Work.NN.Assemble.FT.Edat χ η i l)
          (Work.CR.Flat.polydisc 0 (Work.NN.Assemble.FT.sgm ρ)))
        ≤ (n : ℝ≥0∞) * ((n : ℝ≥0∞) * (ENNReal.ofReal Ce * S)) := by
      have hinner : ∀ i : Fin n, (∑ l : Fin n, holderNorm (k + 1) α
            (Work.NN.Assemble.FT.Edat χ η i l)
            (Work.CR.Flat.polydisc 0 (Work.NN.Assemble.FT.sgm ρ)))
          ≤ (n : ℝ≥0∞) * (ENNReal.ofReal Ce * S) := by
        intro i
        calc (∑ l : Fin n, holderNorm (k + 1) α (Work.NN.Assemble.FT.Edat χ η i l)
              (Work.CR.Flat.polydisc 0 (Work.NN.Assemble.FT.sgm ρ)))
            ≤ ∑ _l : Fin n, ENNReal.ofReal Ce * S := Finset.sum_le_sum fun l _ => hEbd i l
          _ = (Fintype.card (Fin n) : ℝ≥0∞) * (ENNReal.ofReal Ce * S) := by
              rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
          _ = (n : ℝ≥0∞) * (ENNReal.ofReal Ce * S) := by rw [Fintype.card_fin]
      calc (∑ i : Fin n, ∑ l : Fin n, holderNorm (k + 1) α (Work.NN.Assemble.FT.Edat χ η i l)
            (Work.CR.Flat.polydisc 0 (Work.NN.Assemble.FT.sgm ρ)))
          ≤ ∑ _i : Fin n, (n : ℝ≥0∞) * (ENNReal.ofReal Ce * S) :=
            Finset.sum_le_sum fun i _ => hinner i
        _ = (Fintype.card (Fin n) : ℝ≥0∞) * ((n : ℝ≥0∞) * (ENNReal.ofReal Ce * S)) := by
            rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        _ = (n : ℝ≥0∞) * ((n : ℝ≥0∞) * (ENNReal.ofReal Ce * S)) := by rw [Fintype.card_fin]
    have hBbd : holderNorm (k + 1) α
          (Work.NN.Assemble.FT.tfin ρ (Work.NN.Assemble.FT.Edat χ η) j) (pd n ρ 2)
        ≤ ENNReal.ofReal (Ct * (n : ℝ) * (n : ℝ) * Ce) * S := by
      refine (hCt (Work.NN.Assemble.FT.Edat χ η) hEcd j).trans
        ((mul_le_mul_right hsumE _).trans ?_)
      rw [Work.NN.Assemble.FT.ennreal_reassoc]
      rw [← ENNReal.ofReal_natCast n]
      rw [← ENNReal.ofReal_mul hCtpos.le]
      rw [← ENNReal.ofReal_mul (by positivity)]
      rw [← ENNReal.ofReal_mul (by positivity)]
    have hadd := Work.CR.Flat.Holder.holderNorm_add_le
      (f := Work.NN.Core.bmRow (fun a b w => χ w * η a b w) j)
      (g := Work.NN.Assemble.FT.tfin ρ (Work.NN.Assemble.FT.Edat χ η) j)
      (Ω := pd n ρ 2) (α := α) hAcd hBcd (isOpen_pd ρ 2).uniqueDiffOn
    calc holderNorm (k + 1) α ((Work.NN.Core.bmRow (fun a b w => χ w * η a b w)
            + Work.NN.Assemble.FT.tfin ρ (Work.NN.Assemble.FT.Edat χ η)) j) (pd n ρ 2)
        = holderNorm (k + 1) α (Work.NN.Core.bmRow (fun a b w => χ w * η a b w) j
            + Work.NN.Assemble.FT.tfin ρ (Work.NN.Assemble.FT.Edat χ η) j) (pd n ρ 2) := by
            simp only [Pi.add_apply]
      _ ≤ holderNorm (k + 1) α (Work.NN.Core.bmRow (fun a b w => χ w * η a b w) j) (pd n ρ 2)
            + holderNorm (k + 1) α
                (Work.NN.Assemble.FT.tfin ρ (Work.NN.Assemble.FT.Edat χ η) j) (pd n ρ 2) := hadd
      _ ≤ ENNReal.ofReal Cb * S + ENNReal.ofReal (Ct * (n : ℝ) * (n : ℝ) * Ce) * S :=
          add_le_add hAbd hBbd
      _ = ENNReal.ofReal (Cb + Ct * (n : ℝ) * (n : ℝ) * Ce) * S := by
          rw [← add_mul, ← ENNReal.ofReal_add hCbpos.le (by positivity)]
  exact ⟨fun k => Classical.choose (hmain k), fun k => (Classical.choose_spec (hmain k)).1,
    fun k η hη j => (Classical.choose_spec (hmain k)).2 η hη j⟩


end Work.NN.Final
