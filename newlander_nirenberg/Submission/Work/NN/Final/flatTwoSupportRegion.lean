import Mathlib
import Submission.Work.NN.Final.Defs
import Submission.Work.CR.Flat.Holder
import Submission.Work.NN.Final.flatTwoCore
import Submission.Work.CR.Flat.Cauchy.openSolDefs
import Submission.Work.NN.Final.twoCore
import Submission.Work.NN.Core.bmRow_holder
import Submission.Work.NN.Core.bmPotential_gain
import Submission.Work.NN.Core.exists_contDiff_bump_of_isCompact_subset
import Submission.Work.NN.Core.open_poincare_two
import Submission.Work.NN.Core.telescopeTwo
import Submission.Work.NN.Core.holderNorm_zero_univ_lt_top_of_contDiff_one
import Submission.Work.NN.Final.bmDefect_eq_local
import Submission.Work.NN.Final.bmPot_bmH_dbarCoord_eq_local
import Submission.Work.NN.Final.bmRow_tfin_relaxed
import Submission.Work.CR.Flat.Cauchy.holderNorm_mul_le_of_hasCompactSupport
import Submission.Work.CR.Flat.Cauchy.holderNorm_univ_le_holderNorm_polydisc_of_vanishing
import Submission.Work.CR.Flat.Holder.holderNorm_add_le
import Submission.Work.NN.Assemble.flatTwoLossless

noncomputable section
open scoped NNReal ENNReal ContDiff
open Set
open Work.CR.Flat

namespace Work.NN.Final

/-! ## Product estimates with the datum only on `pd n ρ 3` -/

/-- The `C^{k,α}`-norm on `ℂⁿ` of `χ · f`, where `χ` is supported in `pd n ρ (29/10)` and `f` is
only known on `pd n ρ 3`, is controlled by the `C^{k,α}`-norm of `f` on `pd n ρ 3`. -/
lemma chiMul_univ_le {n : ℕ} {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α ≤ 1)
    {ρ : Fin n → ℝ} (hρ : ∀ j, 0 < ρ j) {χ : (Fin n → ℂ) → ℂ}
    (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hcs : HasCompactSupport χ)
    (htsupp : tsupport χ ⊆ pd n ρ (29 / 10)) (k : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ f : (Fin n → ℂ) → ℂ,
      ContDiffOn ℝ (k : ℕ∞) f (pd n ρ 3) →
      Work.CR.Flat.holderNorm k α (fun z => χ z * f z) Set.univ
        ≤ ENNReal.ofReal C * Work.CR.Flat.holderNorm k α f (pd n ρ 3) := by
  obtain ⟨C, hC0, hC⟩ := Work.CR.Flat.Cauchy.holderNorm_mul_le_of_hasCompactSupport
    (Ω := pd n ρ 3) (isOpen_pd ρ 3).uniqueDiffOn hα0 hα1 (hχ.of_le (by simp)) hcs
  refine ⟨C, hC0, fun f hf => ?_⟩
  refine (Work.CR.Flat.Cauchy.holderNorm_univ_le_holderNorm_polydisc_of_vanishing
    (c := 0) (r := fun i => (29 / 10) * ρ i) (r' := fun i => 3 * ρ i) (k := k)
    (g := fun z => χ z * f z) ?_ hα0 ?_).trans (hC f hf)
  · intro i; have h := hρ i; linarith
  · intro z hz
    obtain ⟨i, hi⟩ := hz
    simp only [Pi.zero_apply, sub_zero] at hi
    have hzn : z ∉ pd n ρ (29 / 10) := fun h => absurd (mem_pd.mp h i) (not_lt.mpr hi)
    have hts : z ∉ tsupport χ := fun h => hzn (htsupp h)
    show χ z * f z = 0
    rw [Function.notMem_support.mp (fun h => hts (subset_tsupport χ h)), zero_mul]

/-- The `C^{k,α}`-norm on `ℂⁿ` of `∂̄_a χ · f`, where `χ` is supported in `pd n ρ (29/10)` and `f`
is only known on `pd n ρ 3`, is controlled by the `C^{k,α}`-norm of `f` on `pd n ρ 3` — with a
constant uniform in `a`. -/
lemma dbarCoord_mul_univ_le_pd3 {n : ℕ} {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α ≤ 1)
    {ρ : Fin n → ℝ} (hρ : ∀ j, 0 < ρ j) {χ : (Fin n → ℂ) → ℂ}
    (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hcs : HasCompactSupport χ)
    (htsupp : tsupport χ ⊆ pd n ρ (29 / 10)) (k : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (a : Fin n) (f : (Fin n → ℂ) → ℂ),
      ContDiffOn ℝ (k : ℕ∞) f (pd n ρ 3) →
      Work.CR.Flat.holderNorm k α (fun w => Work.CR.Flat.dbarCoord a χ w * f w) Set.univ
        ≤ ENNReal.ofReal C * Work.CR.Flat.holderNorm k α f (pd n ρ 3) := by
  have hper : ∀ a : Fin n, ∃ Ca : ℝ, 0 < Ca ∧ ∀ f : (Fin n → ℂ) → ℂ,
      ContDiffOn ℝ (k : ℕ∞) f (pd n ρ 3) →
      Work.CR.Flat.holderNorm k α (fun w => Work.CR.Flat.dbarCoord a χ w * f w) Set.univ
        ≤ ENNReal.ofReal Ca * Work.CR.Flat.holderNorm k α f (pd n ρ 3) := fun a =>
    chiMul_univ_le (α := α) (χ := fun w => Work.CR.Flat.dbarCoord a χ w) hα0 hα1 hρ
      (Work.NN.Assemble.FT.contDiff_dbarCoord_of hχ a)
      (Work.NN.Assemble.FT.hasCompactSupport_dbarCoord hcs a)
      ((Work.NN.Assemble.FT.tsupport_dbarCoord_subset a).trans htsupp) k
  choose Cd hCdpos hCd using hper
  have hsumpos : 0 < ∑ a : Fin n, Cd a + 1 := by
    have h := Finset.sum_nonneg (fun a (_ : a ∈ Finset.univ) => le_of_lt (hCdpos a))
    linarith
  refine ⟨∑ a, Cd a + 1, hsumpos, fun a f hf => ?_⟩
  refine (hCd a f hf).trans ?_
  refine mul_le_mul_left (ENNReal.ofReal_le_ofReal ?_) _
  have h1 := Finset.single_le_sum (f := fun a : Fin n => Cd a)
    (fun i _ => le_of_lt (hCdpos i)) (Finset.mem_univ a)
  linarith

/-- Every component of `bmH χ η j l ·` has finite `C^{0,α}`-norm on `ℂⁿ`, bounded uniformly in
`j l i` by the `C^{0,α}`-norm of `η` on `pd n ρ 3`. -/
lemma bmH_univ_le_pd3 {n : ℕ} {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α ≤ 1)
    {ρ : Fin n → ℝ} (hρ : ∀ j, 0 < ρ j) {χ : (Fin n → ℂ) → ℂ}
    (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hcs : HasCompactSupport χ)
    (htsupp : tsupport χ ⊆ pd n ρ (29 / 10)) :
    ∃ C : ℝ, 0 < C ∧ ∀ η : Fin n → Fin n → (Fin n → ℂ) → ℂ,
      (∀ i l, ContDiffOn ℝ (0 : ℕ∞) (η i l) (pd n ρ 3)) → ∀ j l i : Fin n,
        Work.CR.Flat.holderNorm 0 α (fun w => Work.NN.Core.bmH χ η j l i w) Set.univ
          ≤ ENNReal.ofReal C * (∑ r : Fin n, ∑ s : Fin n,
              Work.CR.Flat.holderNorm 0 α (η r s) (pd n ρ 3)) := by
  have htsupp3 : tsupport χ ⊆ pd n ρ 3 := htsupp.trans (pd_mono hρ (by norm_num))
  obtain ⟨Cd, hCdpos, hCd⟩ := dbarCoord_mul_univ_le_pd3 (α := α) hα0 hα1 hρ hχ hcs htsupp 0
  refine ⟨3 * Cd + 1, by linarith, ?_⟩
  intro η hη j l i
  set S : ℝ≥0∞ := ∑ r : Fin n, ∑ s : Fin n,
    Work.CR.Flat.holderNorm 0 α (η r s) (pd n ρ 3) with hSdef
  have hpr : ∀ (a b c : Fin n),
      Work.CR.Flat.holderNorm 0 α (fun w => Work.CR.Flat.dbarCoord a χ w * η b c w) Set.univ
        ≤ ENNReal.ofReal Cd * S := by
    intro a b c
    refine (hCd a (η b c) (hη b c)).trans (mul_le_mul_right ?_ _)
    rw [hSdef]
    exact le_trans
      (Finset.single_le_sum (f := fun s : Fin n =>
          Work.CR.Flat.holderNorm 0 α (η b s) (pd n ρ 3))
        (fun _ _ => zero_le) (Finset.mem_univ c))
      (Finset.single_le_sum
        (f := fun r : Fin n => ∑ s : Fin n, Work.CR.Flat.holderNorm 0 α (η r s) (pd n ρ 3))
        (fun _ _ => zero_le) (Finset.mem_univ b))
  have hsm : ∀ (a b c : Fin n),
      ContDiff ℝ 0 (fun w => Work.CR.Flat.dbarCoord a χ w * η b c w) := fun a b c =>
    Work.NN.Final.contDiff_mul_of_contDiffOn_tsupport (m := 0) (isOpen_pd ρ 3)
      (Work.NN.Assemble.FT.contDiff_dbarCoord_of hχ a)
      ((Work.NN.Assemble.FT.tsupport_dbarCoord_subset a).trans htsupp3) (hη b c)
  have hfun : (fun w => Work.NN.Core.bmH χ η j l i w)
      = (fun w => Work.CR.Flat.dbarCoord i χ w * η j l w)
        + ((fun w => Work.CR.Flat.dbarCoord j χ w * η l i w)
            + -(fun w => Work.CR.Flat.dbarCoord l χ w * η j i w)) := by
    funext w
    rw [Work.NN.Assemble.FT.bmH_eq_sum]
    simp only [Pi.add_apply, Pi.neg_apply]
    ring
  have h1 := Work.CR.Flat.Holder.holderNorm_add_le
    (f := fun w => Work.CR.Flat.dbarCoord i χ w * η j l w)
    (g := (fun w => Work.CR.Flat.dbarCoord j χ w * η l i w)
      + -(fun w => Work.CR.Flat.dbarCoord l χ w * η j i w))
    (Ω := Set.univ) (α := α) (hsm i j l).contDiffOn
    ((hsm j l i).add (hsm l j i).neg).contDiffOn isOpen_univ.uniqueDiffOn
  have h2 := Work.CR.Flat.Holder.holderNorm_add_le
    (f := fun w => Work.CR.Flat.dbarCoord j χ w * η l i w)
    (g := -(fun w => Work.CR.Flat.dbarCoord l χ w * η j i w))
    (Ω := Set.univ) (α := α) (hsm j l i).contDiffOn ((hsm l j i).neg).contDiffOn
    isOpen_univ.uniqueDiffOn
  have hneg := Work.CR.Flat.Holder.holderNorm_neg
    (f := fun w => Work.CR.Flat.dbarCoord l χ w * η j i w) (Ω := Set.univ) (α := α)
    (hsm l j i).contDiffOn isOpen_univ.uniqueDiffOn
  have hthree : ENNReal.ofReal Cd * S + (ENNReal.ofReal Cd * S + ENNReal.ofReal Cd * S)
      = ENNReal.ofReal (3 * Cd) * S := by
    have h3 : ENNReal.ofReal (3 : ℝ) = (3 : ℝ≥0∞) := by norm_num
    rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 3), h3]
    ring
  calc Work.CR.Flat.holderNorm 0 α (fun w => Work.NN.Core.bmH χ η j l i w) Set.univ
      = Work.CR.Flat.holderNorm 0 α ((fun w => Work.CR.Flat.dbarCoord i χ w * η j l w)
          + ((fun w => Work.CR.Flat.dbarCoord j χ w * η l i w)
              + -(fun w => Work.CR.Flat.dbarCoord l χ w * η j i w))) Set.univ := by rw [hfun]
    _ ≤ Work.CR.Flat.holderNorm 0 α (fun w => Work.CR.Flat.dbarCoord i χ w * η j l w) Set.univ
          + Work.CR.Flat.holderNorm 0 α ((fun w => Work.CR.Flat.dbarCoord j χ w * η l i w)
              + -(fun w => Work.CR.Flat.dbarCoord l χ w * η j i w)) Set.univ := h1
    _ ≤ ENNReal.ofReal Cd * S + (ENNReal.ofReal Cd * S + ENNReal.ofReal Cd * S) :=
        add_le_add (hpr i j l)
          (h2.trans (add_le_add (hpr j l i) (by rw [hneg]; exact hpr l j i)))
    _ = ENNReal.ofReal (3 * Cd) * S := hthree
    _ ≤ ENNReal.ofReal (3 * Cd + 1) * S := by
        refine mul_le_mul_left (ENNReal.ofReal_le_ofReal ?_) _
        linarith

/-! ## The defect `Edat` of one Bochner–Martinelli step -/

/-- Antisymmetry of `bmH χ η` from antisymmetry of `η` only on `pd n ρ 3`. -/
lemma bmH_antisymm_pd3 {n : ℕ} {ρ : Fin n → ℝ} {χ : (Fin n → ℂ) → ℂ}
    (htsupp : tsupport χ ⊆ pd n ρ 3) {η : Fin n → Fin n → (Fin n → ℂ) → ℂ}
    (hanti : ∀ i l z, z ∈ pd n ρ 3 → η i l z = -η l i z) :
    ∀ j l i w, Work.NN.Core.bmH χ η j l i w = - Work.NN.Core.bmH χ η l j i w := by
  intro j l i w
  rw [Work.NN.Assemble.FT.bmH_eq_sum, Work.NN.Assemble.FT.bmH_eq_sum]
  by_cases hw : w ∈ pd n ρ 3
  · rw [hanti j l w hw, hanti l j w hw]; ring
  · have h0 : ∀ a : Fin n, Work.CR.Flat.dbarCoord a χ w = 0 := fun a => by
      by_contra hne
      exact hw (htsupp (Work.NN.Assemble.FT.tsupport_dbarCoord_subset a
        (subset_tsupport _ (Function.mem_support.mpr hne))))
    rw [h0 i, h0 j, h0 l]; ring

/-- The components of `bmH χ η` are globally `C¹` when `χ` is supported in `pd n ρ 3` and `η` is
`C¹` there. -/
lemma contDiff_bmH_pd3 {n : ℕ} {ρ : Fin n → ℝ} {χ : (Fin n → ℂ) → ℂ}
    (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (htsupp : tsupport χ ⊆ pd n ρ 3)
    {η : Fin n → Fin n → (Fin n → ℂ) → ℂ}
    (hη : ∀ i l, ContDiffOn ℝ 1 (η i l) (pd n ρ 3)) (j l i : Fin n) :
    ContDiff ℝ 1 (fun w => Work.NN.Core.bmH χ η j l i w) := by
  rw [show (fun w => Work.NN.Core.bmH χ η j l i w)
      = fun w => Work.CR.Flat.dbarCoord i χ w * η j l w
          + Work.CR.Flat.dbarCoord j χ w * η l i w
          - Work.CR.Flat.dbarCoord l χ w * η j i w from by
    funext w; rw [Work.NN.Assemble.FT.bmH_eq_sum]]
  have h1 : ContDiff ℝ 1 (fun w => Work.CR.Flat.dbarCoord i χ w * η j l w) :=
    Work.NN.Final.contDiff_mul_of_contDiffOn_tsupport (m := 1) (isOpen_pd ρ 3)
      (Work.NN.Assemble.FT.contDiff_dbarCoord_of hχ i)
      ((Work.NN.Assemble.FT.tsupport_dbarCoord_subset i).trans htsupp) (hη j l)
  have h2 : ContDiff ℝ 1 (fun w => Work.CR.Flat.dbarCoord j χ w * η l i w) :=
    Work.NN.Final.contDiff_mul_of_contDiffOn_tsupport (m := 1) (isOpen_pd ρ 3)
      (Work.NN.Assemble.FT.contDiff_dbarCoord_of hχ j)
      ((Work.NN.Assemble.FT.tsupport_dbarCoord_subset j).trans htsupp) (hη l i)
  have h3 : ContDiff ℝ 1 (fun w => Work.CR.Flat.dbarCoord l χ w * η j i w) :=
    Work.NN.Final.contDiff_mul_of_contDiffOn_tsupport (m := 1) (isOpen_pd ρ 3)
      (Work.NN.Assemble.FT.contDiff_dbarCoord_of hχ l)
      ((Work.NN.Assemble.FT.tsupport_dbarCoord_subset l).trans htsupp) (hη j i)
  exact (h1.add h2).sub h3

/-- `Edat χ η` is globally `C¹` when `χ` is supported in `pd n ρ 3` and `η` is `C¹` there. -/
lemma Edat_contDiff_pd3 {n : ℕ} (hn : 0 < n) {ρ : Fin n → ℝ} {χ : (Fin n → ℂ) → ℂ}
    (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hcs : HasCompactSupport χ)
    (htsupp : tsupport χ ⊆ pd n ρ 3)
    {η : Fin n → Fin n → (Fin n → ℂ) → ℂ}
    (hη : ∀ i l, ContDiffOn ℝ 1 (η i l) (pd n ρ 3)) (i m : Fin n) :
    ContDiff ℝ 1 (Work.NN.Assemble.FT.Edat χ η i m) := by
  rw [show Work.NN.Assemble.FT.Edat χ η i m = fun z =>
      (Work.CR.Flat.Cauchy.bmGamma n)⁻¹
        * Work.CR.Flat.Cauchy.bmPot (fun j => Work.NN.Core.bmH χ η i m j) z from rfl]
  exact contDiff_const.mul (Work.NN.Assemble.FT.contDiff_bmPot (m := 1) hn
    (fun j => contDiff_bmH_pd3 hχ htsupp hη i m j)
    (fun j => Work.NN.Assemble.FT.bmH_hasCompactSupport hcs i m j))

/-- `Edat χ η` is antisymmetric when `η` is antisymmetric on `pd n ρ 3`. -/
lemma Edat_antisymm_pd3 {n : ℕ} (hn : 0 < n) {ρ : Fin n → ℝ} {χ : (Fin n → ℂ) → ℂ}
    (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hcs : HasCompactSupport χ)
    (htsupp : tsupport χ ⊆ pd n ρ 3)
    {η : Fin n → Fin n → (Fin n → ℂ) → ℂ}
    (hη : ∀ i l, ContDiffOn ℝ 1 (η i l) (pd n ρ 3))
    (hanti : ∀ i l z, z ∈ pd n ρ 3 → η i l z = -η l i z) :
    ∀ j l z, Work.NN.Assemble.FT.Edat χ η j l z = - Work.NN.Assemble.FT.Edat χ η l j z := by
  intro j l z
  have hH : ∀ m w, Work.NN.Core.bmH χ η j l m w = - Work.NN.Core.bmH χ η l j m w :=
    fun m w => bmH_antisymm_pd3 htsupp hanti j l m w
  rw [Work.NN.Assemble.FT.Edat_apply, Work.NN.Assemble.FT.Edat_apply]
  have hpot : Work.CR.Flat.Cauchy.bmPot (fun m => Work.NN.Core.bmH χ η j l m) z
      = - Work.CR.Flat.Cauchy.bmPot (fun m => Work.NN.Core.bmH χ η l j m) z := by
    have hcong : (fun m => Work.NN.Core.bmH χ η j l m)
        = fun m y => - Work.NN.Core.bmH χ η l j m y := by
      funext m y; rw [hH m y]
    rw [hcong]
    have hcont : ∀ m : Fin n, Continuous (fun w => Work.NN.Core.bmH χ η l j m w) :=
      fun m => (contDiff_bmH_pd3 hχ htsupp hη l j m).continuous
    have hcs' : ∀ m : Fin n, HasCompactSupport (fun w => Work.NN.Core.bmH χ η l j m w) :=
      fun m => Work.NN.Assemble.FT.bmH_hasCompactSupport hcs l j m
    have h := congrFun (Work.NN.Assemble.FT.bmPot_real_smul hn (-1) hcont hcs') z
    simp only [Pi.smul_apply] at h
    have h2 : (fun m y => (↑(-1 : ℝ) : ℂ) * Work.NN.Core.bmH χ η l j m y)
        = fun m y => - Work.NN.Core.bmH χ η l j m y := by
      funext m y
      rw [Complex.ofReal_neg, Complex.ofReal_one, neg_one_mul]
    rw [h2] at h
    simpa [neg_one_smul] using h
  rw [hpot]; ring

/-- `Edat χ η` is `∂̄`-closed on `pd n ρ (17/6)` when `χ ≡ 1` on a neighbourhood of
`closedBall 0 ((17/6)ρ)` and `η` is `C¹` and closed on `pd n ρ 3`. -/
lemma Edat_closed_pd3 {n : ℕ} (hn : 0 < n) {ρ : Fin n → ℝ} (hρ : ∀ j, 0 < ρ j)
    {χ : (Fin n → ℂ) → ℂ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hcs : HasCompactSupport χ)
    (htsupp : tsupport χ ⊆ pd n ρ (29 / 10))
    {V : Set (Fin n → ℂ)} (hVo : IsOpen V)
    (hKV : Set.univ.pi (fun i => Metric.closedBall (0 : ℂ) ((17 / 6) * ρ i)) ⊆ V)
    (hχ1 : ∀ y ∈ V, χ y = 1)
    {η : Fin n → Fin n → (Fin n → ℂ) → ℂ}
    (hη : ∀ i l, ContDiffOn ℝ 1 (η i l) (pd n ρ 3))
    (hcl : ∀ j l m z, z ∈ pd n ρ 3 →
      Work.CR.Flat.dbarCoord j (η l m) z - Work.CR.Flat.dbarCoord l (η j m) z
        + Work.CR.Flat.dbarCoord m (η j l) z = 0) :
    ∀ j l m z, z ∈ pd n ρ (17 / 6) →
      Work.CR.Flat.dbarCoord j (Work.NN.Assemble.FT.Edat χ η l m) z
        - Work.CR.Flat.dbarCoord l (Work.NN.Assemble.FT.Edat χ η j m) z
        + Work.CR.Flat.dbarCoord m (Work.NN.Assemble.FT.Edat χ η j l) z = 0 := by
  have htsupp3 : tsupport χ ⊆ pd n ρ 3 := htsupp.trans (pd_mono hρ (by norm_num))
  intro j l m z hz
  have hzV : z ∈ V := hKV (by
    rw [Set.mem_univ_pi]
    intro i
    rw [Metric.mem_closedBall, dist_zero_right]
    have h := mem_pd.mp hz i
    linarith [hρ i])
  have hzeq : χ =ᶠ[nhds z] 1 := by
    filter_upwards [hVo.mem_nhds hzV] with w hw
    exact hχ1 w hw
  have hmain := Work.NN.Final.bmPot_bmH_dbarCoord_eq_local (n := n) hn
    (hχ.of_le (by simp)) hcs (isOpen_pd ρ 3) htsupp3 hη hcl j l m z
  have hmain0 : Work.CR.Flat.dbarCoord j
        (fun w => Work.CR.Flat.Cauchy.bmPot (fun i => Work.NN.Core.bmH χ η l m i) w) z
      - Work.CR.Flat.dbarCoord l
        (fun w => Work.CR.Flat.Cauchy.bmPot (fun i => Work.NN.Core.bmH χ η j m i) w) z
      + Work.CR.Flat.dbarCoord m
        (fun w => Work.CR.Flat.Cauchy.bmPot (fun i => Work.NN.Core.bmH χ η j l i) w) z = 0 := by
    rw [hmain, Work.NN.Assemble.FT.bmH_eq_zero_of_eventuallyEq_one hzeq j l m, mul_zero]
  have hd : ∀ a b : Fin n, DifferentiableAt ℝ
      (fun w => Work.CR.Flat.Cauchy.bmPot (fun i => Work.NN.Core.bmH χ η a b i) w) z :=
    fun a b => Work.NN.Assemble.FT.differentiableAt_bmPot hn
      (fun i => contDiff_bmH_pd3 hχ htsupp3 hη a b i)
      (fun i => Work.NN.Assemble.FT.bmH_hasCompactSupport hcs a b i) z
  rw [show Work.NN.Assemble.FT.Edat χ η l m
        = fun w => (Work.CR.Flat.Cauchy.bmGamma n)⁻¹
            * Work.CR.Flat.Cauchy.bmPot (fun i => Work.NN.Core.bmH χ η l m i) w from rfl,
      show Work.NN.Assemble.FT.Edat χ η j m
        = fun w => (Work.CR.Flat.Cauchy.bmGamma n)⁻¹
            * Work.CR.Flat.Cauchy.bmPot (fun i => Work.NN.Core.bmH χ η j m i) w from rfl,
      show Work.NN.Assemble.FT.Edat χ η j l
        = fun w => (Work.CR.Flat.Cauchy.bmGamma n)⁻¹
            * Work.CR.Flat.Cauchy.bmPot (fun i => Work.NN.Core.bmH χ η j l i) w from rfl,
    Work.NN.Assemble.FT.dbarCoord_const_mul (j := j) _ _ z (hd l m),
    Work.NN.Assemble.FT.dbarCoord_const_mul (j := l) _ _ z (hd j m),
    Work.NN.Assemble.FT.dbarCoord_const_mul (j := m) _ _ z (hd j l)]
  linear_combination ((Work.CR.Flat.Cauchy.bmGamma n)⁻¹) * hmain0

/-- A three-fold `ofReal` reassociation in `ℝ≥0∞`. -/
lemma ofReal_mul_three {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (S : ℝ≥0∞) :
    ENNReal.ofReal a * (ENNReal.ofReal b * (ENNReal.ofReal c * S))
      = ENNReal.ofReal (a * b * c) * S := by
  conv_lhs => rw [← mul_assoc, ← mul_assoc]
  rw [← ENNReal.ofReal_mul ha, ← ENNReal.ofReal_mul (mul_nonneg ha hb)]

/-- The double sum of `(n)²` copies of an `ofReal`-multiple. -/
lemma sum_sum_ofReal_mul (n : ℕ) {a : ℝ} (ha : 0 ≤ a) (S : ℝ≥0∞) :
    (∑ _i : Fin n, ∑ _m : Fin n, ENNReal.ofReal a * S)
      = ENNReal.ofReal ((n : ℝ) * ((n : ℝ) * a)) * S := by
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [← ENNReal.ofReal_natCast]
  rw [ofReal_mul_three (a := (n : ℝ)) (b := (n : ℝ)) (c := a)
    (Nat.cast_nonneg n) (Nat.cast_nonneg n) ha]
  congr 1
  ring

/-- The `C^{1,α}`-norm of `Edat χ η` on `pd n ρ (17/6)` is controlled by the `C^{0,α}`-norm of `η`
on `pd n ρ 3`. -/
lemma Edat_gain_pd3 {n : ℕ} (hn : 0 < n) {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    {ρ : Fin n → ℝ} (hρ : ∀ j, 0 < ρ j) {χ : (Fin n → ℂ) → ℂ}
    (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hcs : HasCompactSupport χ)
    (htsupp : tsupport χ ⊆ pd n ρ (29 / 10)) :
    ∃ C : ℝ, 0 < C ∧ ∀ η : Fin n → Fin n → (Fin n → ℂ) → ℂ,
      (∀ i l, ContDiffOn ℝ 1 (η i l) (pd n ρ 3)) → ∀ j l : Fin n,
        Work.CR.Flat.holderNorm 1 α (Work.NN.Assemble.FT.Edat χ η j l)
            (pd n ρ (17 / 6))
          ≤ ENNReal.ofReal C * ∑ r : Fin n, ∑ s : Fin n,
              Work.CR.Flat.holderNorm 0 α (η r s) (pd n ρ 3) := by
  have htsupp3 : tsupport χ ⊆ pd n ρ 3 := htsupp.trans (pd_mono hρ (by norm_num))
  obtain ⟨Ch, hChpos, hCh⟩ :=
    bmH_univ_le_pd3 (α := α) (le_of_lt hα0) (le_of_lt hα1) hρ hχ hcs htsupp
  obtain ⟨Cg, hCgpos, hCg⟩ := Work.NN.Core.bmPotential_gain (n := n) hn hα0 hα1
    (ρ := fun i => 3 * ρ i) (fun i => by linarith [hρ i]) 0
  refine ⟨‖(Work.CR.Flat.Cauchy.bmGamma n)⁻¹‖ * Cg * ((n : ℝ) * Ch) + 1, by positivity, ?_⟩
  intro η hη j l
  have hη0 : ∀ i m : Fin n, ContDiffOn ℝ (0 : ℕ∞) (η i m) (pd n ρ 3) :=
    fun i m => (hη i m).of_le (by norm_num)
  set S : ℝ≥0∞ := ∑ r : Fin n, ∑ s : Fin n,
    Work.CR.Flat.holderNorm 0 α (η r s) (pd n ρ 3) with hSdef
  have hg1 : ∀ i : Fin n, ContDiff ℝ 1 (fun w => Work.NN.Core.bmH χ η j l i w) :=
    fun i => contDiff_bmH_pd3 hχ htsupp3 hη j l i
  have hgcs : ∀ i : Fin n, HasCompactSupport (fun w => Work.NN.Core.bmH χ η j l i w) :=
    fun i => Work.NN.Assemble.FT.bmH_hasCompactSupport hcs j l i
  have hgfin : ∀ i : Fin n,
      Work.CR.Flat.holderNorm 0 α (fun w => Work.NN.Core.bmH χ η j l i w) Set.univ < ⊤ :=
    fun i => Work.NN.Core.holderNorm_zero_univ_lt_top_of_contDiff_one hα0 hα1 (hg1 i) (hgcs i)
  have hgsup : ∀ i : Fin n, ∀ z, (∃ m, 3 * ρ m ≤ ‖z m‖) →
      Work.NN.Core.bmH χ η j l i z = 0 := by
    intro i z hz
    obtain ⟨m, hm⟩ := hz
    have hzm : z ∉ pd n ρ (29 / 10) := fun h => by
      have h1 := mem_pd.mp h m; have h2 := hρ m; linarith
    have h0 : ∀ a : Fin n, Work.CR.Flat.dbarCoord a χ z = 0 := fun a => by
      by_contra hne
      exact hzm (htsupp (Work.NN.Assemble.FT.tsupport_dbarCoord_subset a
        (subset_tsupport _ (Function.mem_support.mpr hne))))
    rw [Work.NN.Assemble.FT.bmH_eq_sum, h0 i, h0 j, h0 l]; ring
  obtain ⟨hcd, hest⟩ := hCg (fun i => fun w => Work.NN.Core.bmH χ η j l i w)
    (fun i => (hg1 i).of_le (by norm_num)) hgcs hgfin hgsup
  have hbmP : (fun z => Work.CR.Flat.Cauchy.bmPot (fun i => Work.NN.Core.bmH χ η j l i) z)
      = fun z => Work.CR.Flat.Cauchy.bmPotential (fun i => Work.NN.Core.bmH χ η j l i) z :=
    funext fun z => (Work.CR.Flat.Cauchy.bmPotential_eq_bmPot _ z).symm
  have hsum : (∑ i : Fin n,
        Work.CR.Flat.holderNorm 0 α (fun w => Work.NN.Core.bmH χ η j l i w) Set.univ)
      ≤ ENNReal.ofReal ((n : ℝ) * Ch) * S := by
    calc (∑ i : Fin n,
            Work.CR.Flat.holderNorm 0 α (fun w => Work.NN.Core.bmH χ η j l i w) Set.univ)
        ≤ ∑ _i : Fin n, (ENNReal.ofReal Ch * S) :=
          Finset.sum_le_sum fun i _ => by rw [hSdef]; exact hCh η hη0 j l i
      _ = (n : ℝ≥0∞) * (ENNReal.ofReal Ch * S) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      _ = ENNReal.ofReal ((n : ℝ) * Ch) * S := by
          rw [← ENNReal.ofReal_natCast, ← mul_assoc, ← ENNReal.ofReal_mul (Nat.cast_nonneg n)]
  have hEdat : Work.NN.Assemble.FT.Edat χ η j l
      = (Work.CR.Flat.Cauchy.bmGamma n)⁻¹
        • (fun z => Work.CR.Flat.Cauchy.bmPot (fun i => Work.NN.Core.bmH χ η j l i) z) := by
    funext z; rw [Work.NN.Assemble.FT.Edat_apply]; rfl
  calc Work.CR.Flat.holderNorm 1 α (Work.NN.Assemble.FT.Edat χ η j l) (pd n ρ (17 / 6))
      ≤ Work.CR.Flat.holderNorm 1 α (Work.NN.Assemble.FT.Edat χ η j l) (pd n ρ 3) :=
        Work.CR.Flat.holderNorm_mono_set (isOpen_pd ρ 3) (isOpen_pd ρ (17 / 6))
          (pd_mono hρ (by norm_num)) 1 α _
    _ = ENNReal.ofReal ‖(Work.CR.Flat.Cauchy.bmGamma n)⁻¹‖
          * Work.CR.Flat.holderNorm 1 α
              (fun z => Work.CR.Flat.Cauchy.bmPot (fun i => Work.NN.Core.bmH χ η j l i) z)
              (pd n ρ 3) := by
        rw [hEdat]
        exact Work.CR.Flat.Holder.holderNorm_smul _ (by rw [hbmP]; exact hcd)
          (isOpen_pd ρ 3).uniqueDiffOn
    _ ≤ ENNReal.ofReal ‖(Work.CR.Flat.Cauchy.bmGamma n)⁻¹‖
          * (ENNReal.ofReal Cg * (∑ i : Fin n,
              Work.CR.Flat.holderNorm 0 α (fun w => Work.NN.Core.bmH χ η j l i w) Set.univ)) := by
        refine mul_le_mul' le_rfl ?_
        rw [hbmP]
        exact hest
    _ ≤ ENNReal.ofReal ‖(Work.CR.Flat.Cauchy.bmGamma n)⁻¹‖
          * (ENNReal.ofReal Cg * (ENNReal.ofReal ((n : ℝ) * Ch) * S)) :=
        mul_le_mul' le_rfl (mul_le_mul' le_rfl hsum)
    _ = ENNReal.ofReal (‖(Work.CR.Flat.Cauchy.bmGamma n)⁻¹‖ * Cg * ((n : ℝ) * Ch)) * S :=
        ofReal_mul_three (norm_nonneg _) (le_of_lt hCgpos) (mul_nonneg (Nat.cast_nonneg n)
          (le_of_lt hChpos)) S
    _ ≤ ENNReal.ofReal (‖(Work.CR.Flat.Cauchy.bmGamma n)⁻¹‖ * Cg * ((n : ℝ) * Ch) + 1) * S :=
        mul_le_mul_left (ENNReal.ofReal_le_ofReal (by linarith)) _

/-! ## The Bochner–Martinelli defect identity on `pd n ρ (8/3)` -/

/-- The pointwise `(0,2)`-defect identity of one Bochner–Martinelli step, with the datum only
`C¹` and closed on `pd n ρ 3`, valid on `pd n ρ (8/3)`. -/
lemma bmDefect_eq_pd83 {n : ℕ} (hn : 0 < n) {ρ : Fin n → ℝ} (hρ : ∀ j, 0 < ρ j)
    {χ : (Fin n → ℂ) → ℂ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hcs : HasCompactSupport χ)
    (htsupp : tsupport χ ⊆ pd n ρ (29 / 10))
    {V : Set (Fin n → ℂ)} (hVo : IsOpen V)
    (hKV : Set.univ.pi (fun i => Metric.closedBall (0 : ℂ) ((17 / 6) * ρ i)) ⊆ V)
    (hχ1 : ∀ y ∈ V, χ y = 1)
    {η : Fin n → Fin n → (Fin n → ℂ) → ℂ}
    (hη : ∀ i l, ContDiffOn ℝ 1 (η i l) (pd n ρ 3))
    (hcl : ∀ j l m z, z ∈ pd n ρ 3 →
      Work.CR.Flat.dbarCoord j (η l m) z - Work.CR.Flat.dbarCoord l (η j m) z
        + Work.CR.Flat.dbarCoord m (η j l) z = 0) :
    ∀ j l z, z ∈ pd n ρ (8 / 3) →
      Work.CR.Flat.dbarCoord j (Work.NN.Core.bmRow (fun a b w => χ w * η a b w) l) z
        - Work.CR.Flat.dbarCoord l (Work.NN.Core.bmRow (fun a b w => χ w * η a b w) j) z
      = η j l z + Work.NN.Core.bmDefect χ η j l z := by
  have htsupp3 : tsupport χ ⊆ pd n ρ 3 := htsupp.trans (pd_mono hρ (by norm_num))
  have hK'c : IsCompact (tsupport χ ∪
      Set.univ.pi fun i => Metric.closedBall (0 : ℂ) ((17 / 6) * ρ i)) :=
    hcs.isCompact.union (isCompact_univ_pi fun i => isCompact_closedBall 0 _)
  have hK'U : (tsupport χ ∪
      Set.univ.pi fun i => Metric.closedBall (0 : ℂ) ((17 / 6) * ρ i)) ⊆ pd n ρ 3 := by
    intro z hz
    rcases hz with hz | hz
    · exact htsupp3 hz
    · rw [mem_pd]; intro i
      have h2 : ‖z i‖ ≤ (17 / 6) * ρ i := by
        have h := hz i; rw [Metric.mem_closedBall, dist_eq_norm] at h; simpa using h
      have h3 : (17 / 6 : ℝ) * ρ i < 3 * ρ i := by linarith [hρ i]
      linarith
  obtain ⟨χ₂, W, hχ₂, _hcs₂, htsupp₂, hWo, hKW, hχ₂1⟩ :=
    Work.NN.Core.exists_contDiff_bump_of_isCompact_subset hK'c (isOpen_pd ρ 3) hK'U
  have hWK : tsupport χ ⊆ W := fun z hz => hKW (Or.inl hz)
  have hUopen : IsOpen (W ∩ pd n ρ 3) := hWo.inter (isOpen_pd ρ 3)
  have hχU : ∀ z, χ z ≠ 0 → z ∈ W ∩ pd n ρ 3 := fun z hz =>
    ⟨hWK (subset_tsupport χ (Function.mem_support.mpr hz)),
      htsupp3 (subset_tsupport χ (Function.mem_support.mpr hz))⟩
  set η₂ : Fin n → Fin n → (Fin n → ℂ) → ℂ := fun i l w => χ₂ w * η i l w with hη₂def
  have hη₂diff : ∀ i l, ContDiff ℝ 1 (η₂ i l) := fun i l =>
    Work.NN.Final.contDiff_mul_of_contDiffOn_tsupport (m := 1) (isOpen_pd ρ 3) hχ₂ htsupp₂ (hη i l)
  have hη₂closed : ∀ j l m z, z ∈ W ∩ pd n ρ 3 →
      Work.CR.Flat.dbarCoord j (η₂ l m) z - Work.CR.Flat.dbarCoord l (η₂ j m) z
        + Work.CR.Flat.dbarCoord m (η₂ j l) z = 0 := by
    intro j l m z hz
    have hder : ∀ a b : Fin n, fderiv ℝ (fun w => χ₂ w * η a b w) z = fderiv ℝ (η a b) z := by
      intro a b
      have h1 : (fun w => χ₂ w * η a b w) =ᶠ[nhds z] (η a b) := by
        filter_upwards [hWo.mem_nhds hz.1] with w hw
        rw [hχ₂1 w hw, one_mul]
      exact h1.fderiv_eq
    have e1 : Work.CR.Flat.dbarCoord j (η₂ l m) z = Work.CR.Flat.dbarCoord j (η l m) z := by
      simp only [hη₂def, Work.CR.Flat.dbarCoord, hder l m]
    have e2 : Work.CR.Flat.dbarCoord l (η₂ j m) z = Work.CR.Flat.dbarCoord l (η j m) z := by
      simp only [hη₂def, Work.CR.Flat.dbarCoord, hder j m]
    have e3 : Work.CR.Flat.dbarCoord m (η₂ j l) z = Work.CR.Flat.dbarCoord m (η j l) z := by
      simp only [hη₂def, Work.CR.Flat.dbarCoord, hder j l]
    rw [e1, e2, e3]
    exact hcl j l m z hz.2
  obtain ⟨R, hRpos, hR⟩ := hcs.isCompact.isBounded.exists_pos_norm_le
  have hgl := Work.NN.Final.bmDefect_eq_local (n := n) hn (R := R + 1) (by linarith)
    (U := W ∩ pd n ρ 3) hUopen χ (hχ.of_le (by simp))
    (fun z hz => by
      by_contra hc
      have hmem : z ∈ tsupport χ := subset_tsupport χ (Function.mem_support.mpr hc)
      linarith [hR z hmem])
    hχU η₂ hη₂diff hη₂closed
  have hprod : ∀ i l' : Fin n, (fun w => χ w * η₂ i l' w) = fun w => χ w * η i l' w := by
    intro i l'
    funext w
    by_cases hc : χ w = 0
    · rw [hc, zero_mul, zero_mul]
    · have hmem : w ∈ tsupport χ := subset_tsupport χ (Function.mem_support.mpr hc)
      simp only [hη₂def]
      rw [hχ₂1 w (hWK hmem), one_mul]
  have hrow : ∀ i : Fin n, Work.NN.Core.bmRow (fun a b w => χ w * η₂ a b w) i
      = Work.NN.Core.bmRow (fun a b w => χ w * η a b w) i := by
    intro i
    have hfg : (fun a b w => χ w * η₂ a b w) = fun a b w => χ w * η a b w := by
      funext a b w; exact congrFun (hprod a b) w
    rw [hfg]
  have hH : ∀ i l' m' w, Work.NN.Core.bmH χ η₂ i l' m' w = Work.NN.Core.bmH χ η i l' m' w := by
    intro i l' m' w
    rw [Work.NN.Assemble.FT.bmH_eq_sum, Work.NN.Assemble.FT.bmH_eq_sum]
    by_cases hw : w ∈ tsupport χ
    · have h1 : η₂ i l' w = η i l' w := by
        simp only [hη₂def]; rw [hχ₂1 w (hWK hw), one_mul]
      have h2 : η₂ l' m' w = η l' m' w := by
        simp only [hη₂def]; rw [hχ₂1 w (hWK hw), one_mul]
      have h3 : η₂ i m' w = η i m' w := by
        simp only [hη₂def]; rw [hχ₂1 w (hWK hw), one_mul]
      rw [h1, h2, h3]
    · have h0 : χ =ᶠ[nhds w] 0 := by
        filter_upwards [(isClosed_tsupport χ).compl_mem_nhds hw] with y hy
        exact Function.notMem_support.mp fun hy' => hy (subset_tsupport χ hy')
      have hfd : fderiv ℝ χ w = 0 := by
        have h := h0.fderiv_eq (𝕜 := ℝ)
        simpa using h
      have hdb : ∀ a : Fin n, Work.CR.Flat.dbarCoord a χ w = 0 :=
        fun a => by simp [Work.CR.Flat.dbarCoord, hfd]
      rw [hdb m', hdb i, hdb l']
      ring
  intro j l z hz
  have hχ₂z : χ₂ z = 1 := hχ₂1 z (hKW (Or.inr (by
    rw [Set.mem_univ_pi]; intro i
    rw [Metric.mem_closedBall, dist_zero_right]
    have h := mem_pd.mp hz i
    linarith [hρ i])))
  have hzj : η₂ j l z = η j l z := by simp only [hη₂def]; rw [hχ₂z, one_mul]
  have hdefz : Work.NN.Core.bmDefect χ η₂ j l z = Work.NN.Core.bmDefect χ η j l z := by
    rw [Work.NN.Core.bmDefect_apply, Work.NN.Core.bmDefect_apply]
    have hF : (fun m' => Work.NN.Core.bmH χ η₂ j l m')
        = fun m' => Work.NN.Core.bmH χ η j l m' := by
      funext m' w; exact hH j l m' w
    rw [hzj, hF]
  have hj := hgl j l z
  rw [hrow j, hrow l] at hj
  rw [hj, hzj, hdefz]

/-! ## The main theorem -/

set_option maxHeartbeats 1000000 in
theorem flatTwoSupportRegion {n : ℕ} (hn : 0 < n) {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    {ρ : Fin n → ℝ} (hρ : ∀ j, 0 < ρ j) :
    ∃ C : ℝ, 0 < C ∧
      ∃ T2 : (Fin n → Fin n → Work.NN.Core.Cn n → ℂ) → (Fin n → Work.NN.Core.Cn n → ℂ),
        (∀ η : Fin n → Fin n → Work.NN.Core.Cn n → ℂ,
          (∀ j l, ContDiffOn ℝ (1 : ℕ∞) (η j l) (Work.NN.Final.pd n ρ 3)) →
          (∀ j l z, z ∈ Work.NN.Final.pd n ρ 3 → η j l z = - η l j z) →
          Work.NN.Final.Clos2 n ρ 3 η →
          ∀ (j l : Fin n) (z : Work.NN.Core.Cn n), z ∈ Work.NN.Final.pd n ρ (8 / 3) →
            Work.CR.Flat.dbarCoord j (T2 η l) z - Work.CR.Flat.dbarCoord l (T2 η j) z = η j l z) ∧
        (∀ η : Fin n → Fin n → Work.NN.Core.Cn n → ℂ,
          (∀ j l, ContDiffOn ℝ (1 : ℕ∞) (η j l) (Work.NN.Final.pd n ρ 3)) →
          (∀ j l z, z ∈ Work.NN.Final.pd n ρ 3 → η j l z = - η l j z) →
          Work.NN.Final.Clos2 n ρ 3 η →
          ∀ j : Fin n,
            Work.CR.Flat.holderNorm 1 α (T2 η j) (Work.NN.Final.pd n ρ (8 / 3))
              ≤ ENNReal.ofReal C
                  * ∑ j, ∑ l, Work.CR.Flat.holderNorm 0 α (η j l) (Work.NN.Final.pd n ρ 3)) := by
  by_cases hn1 : n = 1
  · subst hn1
    refine ⟨1, one_pos, fun _ => 0, ?_, ?_⟩
    · intro η hη hanti hcl j l z hz
      have hjl : j = l := Subsingleton.elim j l
      subst hjl
      have h0 : η j j z = 0 := by
        have h := hanti j j z (pd_mono hρ (by norm_num) hz)
        linear_combination (1 / 2 : ℂ) * h
      rw [h0]
      simp [Work.CR.Flat.dbarCoord]
    · intro η hη hanti hcl j
      have hz : Work.CR.Flat.holderNorm 1 α
          ((fun _ : Fin 1 → Fin 1 → Work.NN.Core.Cn 1 → ℂ =>
            (0 : Fin 1 → Work.NN.Core.Cn 1 → ℂ)) η j) (pd 1 ρ (8 / 3)) = 0 := by
        simp [Work.CR.Flat.holderNorm, Work.CR.Flat.iterDerivNorm, Work.CR.Flat.holderSeminorm]
      rw [hz]
      exact bot_le
  · have hn2 : 2 ≤ n := by omega
    have hKU : (Set.univ.pi fun i => Metric.closedBall (0 : ℂ) ((17 / 6) * ρ i))
        ⊆ pd n ρ (29 / 10) := by
      intro z hz
      rw [mem_pd]; intro i
      have h1 : ‖z i‖ ≤ (17 / 6) * ρ i := by
        have h := hz i; rw [Metric.mem_closedBall, dist_eq_norm] at h; simpa using h
      have h2 : (17 / 6 : ℝ) * ρ i < (29 / 10) * ρ i := by linarith [hρ i]
      linarith
    have hKc : IsCompact (Set.univ.pi fun i => Metric.closedBall (0 : ℂ) ((17 / 6) * ρ i)) :=
      isCompact_univ_pi fun i => isCompact_closedBall 0 _
    obtain ⟨χ, V, hχ, hcs, htsupp, hVo, hKV, hχ1⟩ :=
      Work.NN.Core.exists_contDiff_bump_of_isCompact_subset hKc (isOpen_pd ρ (29 / 10)) hKU
    have htsupp3 : tsupport χ ⊆ pd n ρ 3 := htsupp.trans (pd_mono hρ (by norm_num))
    obtain ⟨T, CT, hCTpos, hTsol, hTest, hTsm, hTreg⟩ :=
      Work.NN.Core.exists_telTwoDF_smooth (n := n) (α := α) hα0 hα1
        (ρ := fun i => (17 / 6) * ρ i) (ρ' := fun i => (8 / 3) * ρ i)
        (fun i => by have h := hρ i; linarith)
        (fun i => by have h := hρ i; linarith)
        (fun i => by have h := hρ i; linarith)
    obtain ⟨Cb, hCbpos, hCb⟩ := Work.NN.Core.bmRow_holder (n := n) hn hα0 hα1
      (c := 0) (r := fun i => 6 * ρ i) (fun i => by linarith [hρ i]) 0
    obtain ⟨Cc, hCcpos, hCc⟩ := chiMul_univ_le (α := α) (χ := χ) hα0.le hα1.le hρ hχ hcs htsupp 0
    obtain ⟨Ce, hCepos, hCe⟩ := Edat_gain_pd3 hn hα0 hα1 hρ hχ hcs htsupp
    have hCpos : 0 < Cb * Cc + CT 1 * Ce * (n : ℝ) * (n : ℝ) + 1 := by
      have h1 := hCbpos; have h2 := hCcpos; have h3 := hCTpos 1; have h4 := hCepos
      have h5 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      positivity
    refine ⟨Cb * Cc + CT 1 * Ce * (n : ℝ) * (n : ℝ) + 1, hCpos,
      fun η => Work.NN.Core.bmRow (fun a b w => χ w * η a b w)
        + T (Work.NN.Assemble.FT.Edat χ η), ?_, ?_⟩
    · -- the equation
      intro η hη hanti hcl j l z hz
      have hη' : ∀ i m, ContDiffOn ℝ 1 (η i m) (pd n ρ 3) := fun i m => hη i m
      have hcl' : ∀ i m m' w, w ∈ pd n ρ 3 →
          Work.CR.Flat.dbarCoord i (η m m') w - Work.CR.Flat.dbarCoord m (η i m') w
            + Work.CR.Flat.dbarCoord m' (η i m) w = 0 := fun i m m' w hw => hcl i m m' w hw
      have hdef := bmDefect_eq_pd83 hn hρ hχ hcs htsupp hVo hKV hχ1 hη' hcl' j l z hz
      have hEd1 : ∀ i m : Fin n,
          ContDiffOn ℝ 1 (Work.NN.Assemble.FT.Edat χ η i m)
            (polydisc 0 (fun i => (17 / 6) * ρ i)) :=
        fun i m => (Edat_contDiff_pd3 hn hχ hcs htsupp3 hη' i m).contDiffOn
      have hEanti : Work.NN.Core.IsAntisymmTwo (Work.NN.Assemble.FT.Edat χ η) :=
        fun i m w => Edat_antisymm_pd3 hn hχ hcs htsupp3 hη' hanti i m w
      have hEcl : Work.NN.Core.IsClosedTwoOn (fun i => (17 / 6) * ρ i)
          (Work.NN.Assemble.FT.Edat χ η) :=
        fun i m m' w hw => Edat_closed_pd3 hn hρ hχ hcs htsupp hVo hKV hχ1 hη' hcl' i m m' w hw
      have hTs := hTsol (Work.NN.Assemble.FT.Edat χ η) hEd1 hEanti hEcl j l z hz
      have hbm : Work.NN.Core.bmDefect χ η j l z
          = - Work.NN.Assemble.FT.Edat χ η j l z := by
        rw [Work.NN.Core.bmDefect_apply, Work.NN.Assemble.FT.Edat_apply]
        have hχz : χ z = 1 := hχ1 z (hKV (by
          rw [Set.mem_univ_pi]; intro i
          rw [Metric.mem_closedBall, dist_zero_right]
          have h := mem_pd.mp hz i; linarith [hρ i]))
        rw [hχz]; ring
      have hAd : ∀ i : Fin n, DifferentiableAt ℝ
          (Work.NN.Core.bmRow (fun a b w => χ w * η a b w) i) z := fun i =>
        Work.NN.Assemble.FT.differentiableAt_bmRow hn
          (fun a b => Work.NN.Final.contDiff_mul_of_contDiffOn_tsupport (m := 1) (isOpen_pd ρ 3)
            hχ htsupp3 (hη' a b))
          (fun a b => hcs.mul_right) i z
      have hz8 : z ∈ polydisc 0 (fun i => (8 / 3) * ρ i) := hz
      have hTd : ∀ i : Fin n, DifferentiableAt ℝ (T (Work.NN.Assemble.FT.Edat χ η) i) z := fun i =>
        ((hTreg 1 (Work.NN.Assemble.FT.Edat χ η) hEd1 i).contDiffAt
          ((isOpen_polydisc (0 : Fin n → ℂ) (fun i => (8 / 3) * ρ i)).mem_nhds hz8)).differentiableAt
            one_ne_zero
      rw [hbm] at hdef
      show Work.CR.Flat.dbarCoord j (Work.NN.Core.bmRow (fun a b w => χ w * η a b w) l
            + T (Work.NN.Assemble.FT.Edat χ η) l) z
          - Work.CR.Flat.dbarCoord l (Work.NN.Core.bmRow (fun a b w => χ w * η a b w) j
            + T (Work.NN.Assemble.FT.Edat χ η) j) z = η j l z
      rw [Work.NN.Assemble.FT.dbarCoord_add_pi j (hAd l) (hTd l),
          Work.NN.Assemble.FT.dbarCoord_add_pi l (hAd j) (hTd j)]
      linear_combination hdef + hTs
    · -- the estimate
      intro η hη hanti hcl j
      have hη' : ∀ i m, ContDiffOn ℝ 1 (η i m) (pd n ρ 3) := fun i m => hη i m
      have hcl' : ∀ i m m' w, w ∈ pd n ρ 3 →
          Work.CR.Flat.dbarCoord i (η m m') w - Work.CR.Flat.dbarCoord m (η i m') w
            + Work.CR.Flat.dbarCoord m' (η i m) w = 0 := fun i m m' w hw => hcl i m m' w hw
      set S : ℝ≥0∞ := ∑ r : Fin n, ∑ s : Fin n,
        Work.CR.Flat.holderNorm 0 α (η r s) (pd n ρ 3) with hSdef
      by_cases htop : S = ⊤
      · rw [htop, ENNReal.mul_top (by rw [ENNReal.ofReal_ne_zero_iff]; positivity)]
        exact le_top
      · have hEd1 : ∀ i m : Fin n,
            ContDiffOn ℝ 1 (Work.NN.Assemble.FT.Edat χ η i m)
              (polydisc 0 (fun i => (17 / 6) * ρ i)) :=
          fun i m => (Edat_contDiff_pd3 hn hχ hcs htsupp3 hη' i m).contDiffOn
        have hEanti : Work.NN.Core.IsAntisymmTwo (Work.NN.Assemble.FT.Edat χ η) :=
          fun i m w => Edat_antisymm_pd3 hn hχ hcs htsupp3 hη' hanti i m w
        have hEcl : Work.NN.Core.IsClosedTwoOn (fun i => (17 / 6) * ρ i)
            (Work.NN.Assemble.FT.Edat χ η) :=
          fun i m m' w hw => Edat_closed_pd3 hn hρ hχ hcs htsupp hVo hKV hχ1 hη' hcl' i m m' w hw
        -- abbreviations
        have hglob : ∀ a b : Fin n, ContDiff ℝ 1 (fun w => χ w * η a b w) := fun a b =>
          Work.NN.Final.contDiff_mul_of_contDiffOn_tsupport (m := 1) (isOpen_pd ρ 3) hχ htsupp3
            (hη' a b)
        have hvan : ∀ a b (w : Fin n → ℂ),
            (∃ i, ((6 : ℝ) * ρ i) / 2 ≤ ‖w i - (0 : Fin n → ℂ) i‖) → χ w * η a b w = 0 := by
          intro a b w hw
          obtain ⟨i, hi⟩ := hw
          simp only [Pi.zero_apply, sub_zero] at hi
          have hwi : 3 * ρ i ≤ ‖w i‖ := by linarith [hi]
          have hnot : w ∉ pd n ρ 3 := fun h => by have h1 := mem_pd.mp h i; linarith
          have hχ0 : χ w = 0 := by
            by_contra hc
            exact hnot (htsupp3 (subset_tsupport χ (Function.mem_support.mpr hc)))
          rw [hχ0, zero_mul]
        -- the Bochner–Martinelli part
        have hbmEst : Work.CR.Flat.holderNorm 1 α
            (Work.NN.Core.bmRow (fun a b w => χ w * η a b w) j) (pd n ρ (8 / 3))
            ≤ ENNReal.ofReal (Cb * Cc) * S := by
          have hset : polydisc (0 : Fin n → ℂ) (fun i => (6 * ρ i) / 2) = pd n ρ 3 := by
            have hfun : (fun i : Fin n => (6 * ρ i) / 2) = fun i : Fin n => 3 * ρ i := by
              funext i; ring
            rw [hfun]; rfl
          have hcb := hCb (fun a b w => χ w * η a b w) hglob hvan j
          rw [hset] at hcb
          have hsumC : (∑ m : Fin n, ∑ m' : Fin n,
                Work.CR.Flat.holderNorm 0 α (fun w => χ w * η m m' w) Set.univ)
              ≤ ENNReal.ofReal Cc * S := by
            rw [hSdef, Finset.mul_sum]
            refine Finset.sum_le_sum fun m _ => ?_
            rw [Finset.mul_sum]
            exact Finset.sum_le_sum fun m' _ => hCc (η m m') ((hη' m m').of_le (by norm_num))
          calc Work.CR.Flat.holderNorm 1 α
                (Work.NN.Core.bmRow (fun a b w => χ w * η a b w) j) (pd n ρ (8 / 3))
              ≤ Work.CR.Flat.holderNorm 1 α
                  (Work.NN.Core.bmRow (fun a b w => χ w * η a b w) j) (pd n ρ 3) :=
                Work.CR.Flat.holderNorm_mono_set (isOpen_pd ρ 3) (isOpen_pd ρ (8 / 3))
                  (pd_mono hρ (by norm_num)) 1 α _
            _ ≤ ENNReal.ofReal Cb * (∑ m : Fin n, ∑ m' : Fin n,
                  Work.CR.Flat.holderNorm 0 α (fun w => χ w * η m m' w) Set.univ) := hcb
            _ ≤ ENNReal.ofReal Cb * (ENNReal.ofReal Cc * S) :=
                mul_le_mul' le_rfl hsumC
            _ = ENNReal.ofReal (Cb * Cc) * S := by
                rw [← mul_assoc, ← ENNReal.ofReal_mul (le_of_lt hCbpos)]
        -- the transferred-solver part
        have hsumE : (∑ i : Fin n, ∑ m : Fin n,
              Work.CR.Flat.holderNorm 1 α (Work.NN.Assemble.FT.Edat χ η i m)
                (polydisc 0 (fun i => (17 / 6) * ρ i)))
            ≤ ENNReal.ofReal ((n : ℝ) * ((n : ℝ) * Ce)) * S := by
          have hle : (∑ i : Fin n, ∑ m : Fin n,
                Work.CR.Flat.holderNorm 1 α (Work.NN.Assemble.FT.Edat χ η i m)
                  (polydisc 0 (fun i => (17 / 6) * ρ i)))
              ≤ ∑ _i : Fin n, ∑ _m : Fin n, (ENNReal.ofReal Ce * S) :=
            Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun m _ => by
              rw [hSdef]; exact hCe η hη' i m
          refine hle.trans (le_of_eq ?_)
          exact sum_sum_ofReal_mul n (le_of_lt hCepos) S
        have hTest' : Work.CR.Flat.holderNorm 1 α (T (Work.NN.Assemble.FT.Edat χ η) j)
              (pd n ρ (8 / 3))
            ≤ ENNReal.ofReal (CT 1 * ((n : ℝ) * ((n : ℝ) * Ce))) * S := by
          have ht := hTest 1 (Work.NN.Assemble.FT.Edat χ η) hEd1 hEanti hEcl j
          calc Work.CR.Flat.holderNorm 1 α (T (Work.NN.Assemble.FT.Edat χ η) j) (pd n ρ (8 / 3))
              ≤ ENNReal.ofReal (CT 1) * (∑ i : Fin n, ∑ m : Fin n,
                  Work.CR.Flat.holderNorm 1 α (Work.NN.Assemble.FT.Edat χ η i m)
                    (polydisc 0 (fun i => (17 / 6) * ρ i))) := ht
            _ ≤ ENNReal.ofReal (CT 1)
                  * (ENNReal.ofReal ((n : ℝ) * ((n : ℝ) * Ce)) * S) :=
                mul_le_mul' le_rfl hsumE
            _ = ENNReal.ofReal (CT 1 * ((n : ℝ) * ((n : ℝ) * Ce))) * S := by
                rw [← mul_assoc, ← ENNReal.ofReal_mul (le_of_lt (hCTpos 1))]
        -- the sum
        have hsplit := Work.CR.Flat.Holder.holderNorm_add_le
          (f := Work.NN.Core.bmRow (fun a b w => χ w * η a b w) j)
          (g := T (Work.NN.Assemble.FT.Edat χ η) j)
          (Ω := pd n ρ (8 / 3)) (α := α)
          (Work.NN.Assemble.FT.contDiff_bmRow hn (fun a b => hglob a b)
            (fun a b => hcs.mul_right) j).contDiffOn
          (hTreg 1 (Work.NN.Assemble.FT.Edat χ η) hEd1 j)
          (isOpen_pd ρ (8 / 3)).uniqueDiffOn
        have harith : ENNReal.ofReal (Cb * Cc) * S
              + ENNReal.ofReal (CT 1 * ((n : ℝ) * ((n : ℝ) * Ce))) * S
            = ENNReal.ofReal (Cb * Cc + CT 1 * ((n : ℝ) * ((n : ℝ) * Ce))) * S := by
          have g1 : (0 : ℝ) ≤ Cb * Cc := le_of_lt (mul_pos hCbpos hCcpos)
          have g2 : (0 : ℝ) ≤ CT 1 * ((n : ℝ) * ((n : ℝ) * Ce)) :=
            mul_nonneg (le_of_lt (hCTpos 1))
              (mul_nonneg (Nat.cast_nonneg n)
                (mul_nonneg (Nat.cast_nonneg n) (le_of_lt hCepos)))
          rw [← add_mul, ← ENNReal.ofReal_add g1 g2]
        refine (hsplit.trans (add_le_add hbmEst hTest')).trans ?_
        rw [harith]
        refine mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal ?_) (bot_le)
        have h1 : CT 1 * ((n : ℝ) * ((n : ℝ) * Ce)) = CT 1 * Ce * (n : ℝ) * (n : ℝ) := by ring
        rw [h1]
        linarith [le_of_lt (hCTpos 1)]

end Work.NN.Final
