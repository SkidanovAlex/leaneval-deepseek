/-
# ZeroFreeTables/HB94/Lam0GeEngine — HB Lemma 9.1 (the `P₃` engine) at the wide height

`HBLemma9_1` (`Submission/Work/ZeroFreeTables/Engine.lean`) is HB's Lemma 9.1 in the shape in
which it is used for Table 8: the second zero `ρ₀` is required to lie in HB's working region
`IsZ χ₁ ρ₀` (`|Im ρ₀| ≤ 1`).  Here the same inequality (9.13) is proved when the second zero has
`|Im ρ₀| ≤ 2` and the character is *complex* (`χ₁ ^ 2 ≠ 1`) — exactly the case needed by
`Work.ZeroFreeTables.HB94.Lam0Ge` (HB Table 8 at the wide height `|Im ρ| ≤ 2`).

The proof is a transcription of `Submission/Work/ZeroFreeTables/HBLemma9_1_proof.lean`
(with the `χ₁ ^ 2 = 1` case deleted, as it is excluded by hypothesis), with every height bound
`|t| ≤ 3` widened to `|t| ≤ 4`.  The only ingredients that had to be re-proved at the wider
height are

* the ζ zero-free strip `1 - ε ≤ Re s ≤ 2`, `|Im s| ≤ 5` (the original has `|Im s| ≤ 4`);
* the support/non-negativity/dropping lemmas for the near zero-sum `nearP3sum` at `|Im s| ≤ 4`
  (the originals assume `|Im s| ≤ 3`);
* the point bounds (`point_bound_prim`, `point_bound_q`, `point_bound_principal`) and the
  `k = 1` input, whose `|Im s| ≤ 3` hypotheses were relaxed to `|Im s| ≤ 4` (resp. `≤ 10`).

Everything else is the colleague's proof, unchanged.
-/

import Mathlib
import Submission.Work.LinnikAreas.boxMaxZero
import Mathlib.NumberTheory.LSeries.ZetaZeros
import Submission.Work.ZeroFreeTables.Engine
import Submission.Work.ZeroFreeTables.P3.DefsL
import Submission.Work.ZeroFreeTables.P3.WLBase
import Submission.Work.ZeroFreeTables.P3.SummableVonMangoldtLogPow
import Submission.Work.ZeroFreeTables.P3.SideConditions
import Submission.Work.ZeroFreeTables.P3.P3Bounds
import Submission.Work.ZeroFreeTables.P3.CaseC_D
import Submission.Work.ZeroFreeTables.P3Pos
import Submission.Work.ZeroFreeTables.HB4_1
import Submission.Work.ZeroFreeTables.P9.Defs
import Submission.Work.ZeroFreeTables.P9.Setup
import Submission.Work.ZeroFreeTables.P9.lDiffExplicit_gen
import Submission.Work.ZeroFreeTables.P9.zetaDiffExplicit_gen
import Submission.Work.ZeroFreeTables.P9.HbCombinationL_nonneg
import Submission.Work.ZeroFreeTables.P9.iteratedDeriv_vonMangoldt
import Submission.Work.ZeroFreeTables.P9.SigmaP3L_eq_logDeriv_derivs
import Submission.Work.ZeroFreeTables.P9.invNearSum_eq_tsum
import Submission.Work.ZeroFreeTables.P9.pointEngine_prim
import Submission.Work.ZeroFreeTables.P9.rescale_variants
import Submission.Work.ZeroFreeTables.P9.trivSeriesBound
import Submission.Work.ZeroFreeTables.P9.zetaLogDeriv_pole_split
import Submission.Work.ZeroFreeTables.P9.nearP3sum_ge_kept
import Submission.Work.ZeroFreeTables.P9.InvNearSum_anti
import Submission.Work.ZeroFreeTables.P9.SigmaP3L_changeLevel_diff
import Submission.Work.ZeroFreeTables.P9.SigmaP3L_conj_eq
import Submission.Work.ZeroFreeTables.P9.zetaZeroInvSq_tsum
import Submission.Work.ZeroFreeTables.P9.zetaEngine_principal
import Submission.Work.LinnikAreas.l31free.lemma3_1_free_gen
import Submission.Work.LinnikAreas.area1
import Submission.Work.LinnikAreas.FarRepel.zeroMult_eq_analyticOrderNatAt_of_isPrimitive
import Submission.Work.A7.zeroMult_conj_sq_one
import Submission.Commons.NumberTheory.Linnik.zeroSum_invSq_bound
import Submission.Commons.NumberTheory.Zeta.zeta_zeroFree_near_axis
import Submission.Commons.NumberTheory.Zeta.zeta_logDeriv_near_axis_bound
import Submission.Commons.NumberTheory.DirichletCharacter.LFunction_logDeriv_eq_neg_LSeries_vonMangoldt
import Submission.Work.ZeroFreeTables.P9.parity_bound_re
import Submission.Work.ZeroFreeTables.P9.absorption_eventual
import Submission.Work.ZeroFreeTables.P9.primeFactors_logPow_div_le
import Submission.Work.ZeroFreeTables.Table4.zeroMult_changeLevel
import Submission.Work.LinnikAreas2.D2Aux

open DirichletCharacter Complex
open scoped Classical BigOperators
noncomputable section



set_option maxHeartbeats 256000000

namespace Work.ZeroFreeTables.HB94.Lam0GeEngine

/-! ## The ζ zero-free strip at `|Im| ≤ 5` -/

/-- **ζ has no zeros in a fixed strip next to the real axis with `|Im| ≤ 5`.**

The proof of `Commons.NumberTheory.Zeta.zeta_zeroFree_near_axis` (there with `|Im| ≤ 4`): the
zeros of ζ in the compact rectangle `1/2 ≤ re s ≤ 2`, `|im s| ≤ 5` are finite, lie strictly to the
left of the line `re s = 1`, and hence are separated from it by a positive distance `d`; the
strip `1 - d/2 ≤ re s`, together with `re s ≤ 2` and `|im s| ≤ 5`, is zero-free. -/
theorem zeta_zeroFree_near_axis_w :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧
      ∀ (t σ : ℝ), |t| ≤ 5 → 1 - ε₀ ≤ σ → σ ≤ 2 →
        riemannZeta (((σ : ℂ) + Complex.I * (t : ℂ)) : ℂ) ≠ 0 := by
  let S₀ : Set ℂ := (fun p : ℝ × ℝ => (p.1 : ℂ) + Complex.I * (p.2 : ℂ)) ''
    (Set.Icc (1 / 2 : ℝ) 2 ×ˢ Set.Icc (-5 : ℝ) 5)
  have hS₀compact : IsCompact S₀ := by
    dsimp [S₀]
    exact (IsCompact.prod isCompact_Icc isCompact_Icc).image
      (by fun_prop : Continuous (fun p : ℝ × ℝ => (p.1 : ℂ) + Complex.I * (p.2 : ℂ)))
  let Z : Set ℂ := S₀ ∩ riemannZetaZeros
  have hZfin : Z.Finite := by
    dsimp [Z]
    exact hS₀compact.inter_riemannZetaZeros_finite
  have hZm : ∀ z : ℂ, z ∈ Z →
      (1 / 2 : ℝ) ≤ z.re ∧ z.re ≤ 2 ∧ |z.im| ≤ 5 ∧ riemannZeta z = 0 := by
    intro z hz
    rcases hz.1 with ⟨p, hp, hpeq⟩
    have hzre : z.re = p.1 := by rw [← hpeq]; simp
    have hzim : z.im = p.2 := by rw [← hpeq]; simp
    have hz0 : riemannZeta z = 0 := by simpa [riemannZetaZeros] using hz.2
    exact ⟨by linarith [hp.1.1, hzre], by linarith [hp.1.2, hzre],
      abs_le.mpr (by simpa [hzim] using hp.2), hz0⟩
  have hZ_re_lt_one : ∀ z : ℂ, z ∈ Z → z.re < 1 := by
    intro z hz
    have hz0 : riemannZeta z = 0 := (hZm z hz).2.2.2
    exact lt_of_not_ge (fun hge : (1 : ℝ) ≤ z.re =>
      riemannZeta_ne_zero_of_one_le_re (s := z) hge hz0)
  by_cases hZempty : Z = ∅
  · refine ⟨(1 / 2 : ℝ), by norm_num, ?_⟩
    intro t σ ht hσlo hσhi hz0
    let s : ℂ := (σ : ℂ) + Complex.I * (t : ℂ)
    have hsZ : s ∈ Z := by
      constructor
      · dsimp [S₀]
        refine ⟨(σ, t), ⟨⟨by linarith, by linarith⟩, abs_le.mp ht⟩, rfl⟩
      · simpa [Z, riemannZetaZeros, s] using hz0
    rw [hZempty] at hsZ
    exact hsZ
  · have hZn : Z.Nonempty := Set.nonempty_iff_ne_empty.mpr hZempty
    let fz : Finset ℂ := hZfin.toFinset
    have hfz_mem_iff : ∀ z : ℂ, z ∈ fz ↔ z ∈ Z := fun z => hZfin.mem_toFinset
    have hg_ne : (fz.image (fun z : ℂ => 1 - z.re)).Nonempty := by
      rcases hZn with ⟨z, hz⟩
      exact ⟨1 - z.re, Finset.mem_image.mpr ⟨z, (hfz_mem_iff z).2 hz, rfl⟩⟩
    let d : ℝ := (fz.image (fun z : ℂ => 1 - z.re)).min' hg_ne
    have hd_mem : d ∈ fz.image (fun z : ℂ => 1 - z.re) := by
      dsimp [d]
      exact Finset.min'_mem _ hg_ne
    rcases Finset.mem_image.mp hd_mem with ⟨z₀, hz₀f, hz₀eq⟩
    have hz₀Z : z₀ ∈ Z := (hfz_mem_iff z₀).1 hz₀f
    have hd0 : 0 < d := by
      have hz₀re : z₀.re < 1 := hZ_re_lt_one z₀ hz₀Z
      have hd : d = 1 - z₀.re := by simpa [d] using hz₀eq.symm
      linarith
    have hd_le_half : d ≤ 1 / 2 := by
      have hz₀ge : (1 / 2 : ℝ) ≤ z₀.re := (hZm z₀ hz₀Z).1
      have hd : d = 1 - z₀.re := by simpa [d] using hz₀eq.symm
      linarith
    have hd_le : ∀ z : ℂ, z ∈ Z → d ≤ 1 - z.re := by
      intro z hz
      dsimp [d]
      exact Finset.min'_le (fz.image (fun z : ℂ => 1 - z.re))
        (1 - z.re) (Finset.mem_image.mpr ⟨z, (hfz_mem_iff z).2 hz, rfl⟩)
    refine ⟨d / 2, by positivity, ?_⟩
    intro t σ ht hσlo hσhi hz0
    let s : ℂ := (σ : ℂ) + Complex.I * (t : ℂ)
    have hsZ : s ∈ Z := by
      constructor
      · dsimp [S₀]
        refine ⟨(σ, t), ⟨⟨by linarith, by linarith⟩, abs_le.mp ht⟩, rfl⟩
      · simpa [Z, riemannZetaZeros, s] using hz0
    have hre : s.re = σ := by simp [s]
    have h1 : d ≤ 1 - σ := by
      have hd' := hd_le s hsZ
      rwa [hre] at hd'
    have h2 : 1 - σ ≤ d / 2 := by linarith
    linarith

/-! ## `λ ≥ 0` from `zeroMult ≠ 0` alone -/

/-- `λ(ρ) = (1 - Re ρ) log q ≥ 0` for a zero `ρ` of non-zero multiplicity. -/
theorem lamOf_nonneg_of_zeroMult {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} {ρ : ℂ}
    (h : Work.LinnikContract.zeroMult χ ρ ≠ 0) : 0 ≤ Work.LinnikContract.lamOf q ρ := by
  have hre : ρ.re < 1 := Work.LinnikAreas.boxMaxZeroAux.zeroMult_re_lt_one χ h
  have hlog : 0 ≤ Real.log (q : ℝ) := Real.log_nonneg (by exact_mod_cast NeZero.one_le)
  rw [Work.LinnikContract.lamOf]
  exact mul_nonneg (by linarith) hlog

/-! ## The near zero-sum at the wide height `|Im s| ≤ 4` -/

/-- Wide version of `P9.nearP3summand_mem_box`: if the summand at `u` is nonzero then `u` is a
genuine zero of `L(·,χ)` with `0 ≤ Re u ≤ 1` and `|Im u| ≤ 5` (from `|Im s| ≤ 4` and `δ < 1`). -/
theorem nearP3summand_mem_box {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1)
    {L a lam₁ δ : ℝ} (hδ1 : δ < 1) {s : ℂ} (hsim : |s.im| ≤ 4) (u : ℂ)
    (hu : P9.nearP3summand N L χ s a lam₁ δ u ≠ 0) :
    Work.LinnikContract.zeroMult χ u ≠ 0 ∧ 0 ≤ u.re ∧ u.re ≤ 1 ∧ |u.im| ≤ 5 := by
  unfold P9.nearP3summand at hu
  have h1 : (Work.LinnikContract.zeroMult χ u : ℝ) * P9.nearInd s δ u ≠ 0 :=
    (mul_ne_zero_iff.mp hu).1
  have hzmR : (Work.LinnikContract.zeroMult χ u : ℝ) ≠ 0 := (mul_ne_zero_iff.mp h1).1
  have hni : P9.nearInd s δ u ≠ 0 := (mul_ne_zero_iff.mp h1).2
  have hzm : Work.LinnikContract.zeroMult χ u ≠ 0 := Nat.cast_ne_zero.mp hzmR
  have hcond : ‖(1 : ℂ) + (s.im : ℂ) * Complex.I - u‖ ≤ δ := by
    by_contra h
    unfold P9.nearInd at hni
    rw [if_neg h] at hni
    exact hni rfl
  have hlt : ‖(1 : ℂ) + (s.im : ℂ) * Complex.I - u‖ < 1 := lt_of_le_of_lt hcond hδ1
  have hre : |1 - u.re| < 1 := by
    have h := lt_of_le_of_lt (Complex.abs_re_le_norm ((1 : ℂ) + (s.im : ℂ) * Complex.I - u)) hlt
    simpa using h
  have him : |s.im - u.im| < 1 := by
    have h := lt_of_le_of_lt (Complex.abs_im_le_norm ((1 : ℂ) + (s.im : ℂ) * Complex.I - u)) hlt
    simpa using h
  refine ⟨hzm, ?_, ?_, ?_⟩
  · have h' : 1 - u.re < 1 := (abs_lt.mp hre).2
    linarith
  · exact le_of_lt (Work.LinnikAreas.boxMaxZeroAux.zeroMult_re_lt_one χ hzm)
  · have h1' : |u.im - s.im| < 1 := abs_sub_comm s.im u.im ▸ him
    have h2 : |u.im| ≤ |u.im - s.im| + |s.im| := by
      have := abs_add_le (u.im - s.im) s.im
      simpa using this
    linarith

/-- Wide version of `P9.nearP3summand_nonneg` at `|Im s| ≤ 4`: the window forces
`|Im u| ≤ 5 ≤ 10`, so the minimality hypothesis applies. -/
theorem nearP3summand_nonneg {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    {L a lam₁ δ : ℝ} (hL : 0 < L) (ha : 0 < a) (hlam₁ : 0 ≤ lam₁) (hδ1 : δ < 1)
    {s : ℂ} (hsre : s.re = 1 + a / L) (hsim : |s.im| ≤ 4)
    (hmin : ∀ u : ℂ, Work.LinnikContract.zeroMult χ u ≠ 0 → |u.im| ≤ 10 →
      lam₁ ≤ (1 - u.re) * L)
    (u : ℂ) : 0 ≤ P9.nearP3summand N L χ s a lam₁ δ u := by
  rw [P9.nearP3summand_eq_P3]
  by_cases hz : Work.LinnikContract.zeroMult χ u = 0
  · simp [hz]
  by_cases hn : P9.nearInd s δ u = 0
  · simp [hn]
  have hw : ‖(1 : ℂ) + (s.im : ℂ) * Complex.I - u‖ ≤ δ := by
    by_contra hc
    exact hn (by rw [P9.nearInd_eq_ite, if_neg hc])
  have him : |u.im| ≤ 10 := by
    have h2 : ((1 : ℂ) + (s.im : ℂ) * Complex.I - u).im = s.im - u.im := by simp
    have h1 : |s.im - u.im| ≤ δ := by
      have h1' := Complex.abs_im_le_norm ((1 : ℂ) + (s.im : ℂ) * Complex.I - u)
      rw [h2] at h1'
      exact h1'.trans hw
    have h3 : |u.im| ≤ |s.im| + |s.im - u.im| := by
      calc |u.im| = |s.im - (s.im - u.im)| := by
            congr 1; ring
        _ ≤ |s.im| + |s.im - u.im| := abs_sub _ _
    linarith
  have hlam : lam₁ ≤ (1 - u.re) * L := hmin u hz him
  exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (P9.nearInd_nonneg s δ u))
    (P9.P3term_nonneg_of_min hL ha hlam₁ hsre hlam)

/-- Wide version of `P9.nearP3sum_ge_kept` at `|Im s| ≤ 4`: the `δ`-window lies in the box
`0 ≤ Re ≤ 1`, `|Im| ≤ 5` (the original uses `|Im| ≤ 4` for `|Im s| ≤ 3`). -/
theorem nearP3sum_ge_kept {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1)
    {L a lam₁ δ : ℝ} (hL : 0 < L) (ha : 0 < a) (hlam₁ : 0 ≤ lam₁) (hδ : 0 < δ) (hδ1 : δ < 1)
    (haδ : 2 * a ≤ δ * L) {s : ℂ} (hsre : s.re = 1 + a / L) (hsim : |s.im| ≤ 4)
    (hmin : ∀ u : ℂ, Work.LinnikContract.zeroMult χ u ≠ 0 → |u.im| ≤ 10 → lam₁ ≤ (1 - u.re) * L)
    (T : Finset ℂ) (hT : ∀ u ∈ T, Work.LinnikContract.zeroMult χ u ≠ 0)
    (hTim : ∀ u ∈ T, |u.im| ≤ 10) :
    ∑ u ∈ T, (Work.ZeroFreeTables.P3 ((a + lam₁) / ((s - u) * (L : ℂ)))).re
      ≤ P9.nearP3sum N L χ s a lam₁ δ
        + (T.card : ℝ) * (8 * (a + lam₁) / (δ * L)) := by
  classical
  set S : Finset ℂ := (Work.LinnikAreas.boxMaxZeroAux.finite_zeroMult_box χ 0 5).toFinset with hS
  have hmemS : ∀ u : ℂ, u ∈ S ↔
      Work.LinnikContract.zeroMult χ u ≠ 0 ∧ 0 ≤ u.re ∧ u.re ≤ 1 ∧ |u.im| ≤ 5 := by
    intro u
    rw [hS, Set.Finite.mem_toFinset]
    rfl
  have hsupp : ∀ u : ℂ, u ∉ S → P9.nearP3summand N L χ s a lam₁ δ u = 0 := by
    intro u hu
    by_contra h
    exact hu ((hmemS u).mpr (nearP3summand_mem_box χ hχ hδ1 hsim u h))
  have htsum : P9.nearP3sum N L χ s a lam₁ δ
      = ∑ u ∈ S ∪ T, P9.nearP3summand N L χ s a lam₁ δ u := by
    rw [P9.nearP3sum_eq_tsum]
    exact tsum_eq_sum (s := S ∪ T) (fun u hu => hsupp u (fun h => hu (Finset.mem_union_left _ h)))
  set p : ℂ → Prop := fun u => ‖(1 : ℂ) + (s.im : ℂ) * Complex.I - u‖ ≤ δ with hp
  have hTsplit : ∑ u ∈ T, (Work.ZeroFreeTables.P3 ((a + lam₁) / ((s - u) * (L : ℂ)))).re
      = ∑ u ∈ T.filter p, (Work.ZeroFreeTables.P3 ((a + lam₁) / ((s - u) * (L : ℂ)))).re
        + ∑ u ∈ T.filter (fun u => ¬ p u),
            (Work.ZeroFreeTables.P3 ((a + lam₁) / ((s - u) * (L : ℂ)))).re :=
    (Finset.sum_filter_add_sum_filter_not T p _).symm
  have hnear_pt : ∀ u ∈ T.filter p,
      (Work.ZeroFreeTables.P3 ((a + lam₁) / ((s - u) * (L : ℂ)))).re
        ≤ P9.nearP3summand N L χ s a lam₁ δ u := by
    intro u hu
    rw [Finset.mem_filter] at hu
    obtain ⟨huT, hpu⟩ := hu
    rw [P9.nearP3summand_eq_P3]
    have hind : P9.nearInd s δ u = 1 := by
      rw [P9.nearInd_eq_ite]
      exact if_pos (by simpa [hp] using hpu)
    rw [hind, mul_one]
    have hmult : (1 : ℝ) ≤ (Work.LinnikContract.zeroMult χ u : ℝ) := by
      have := hT u huT
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr this
    have hP3 : 0 ≤ (Work.ZeroFreeTables.P3 ((a + lam₁) / ((s - u) * (L : ℂ)))).re := by
      have hnn := nearP3summand_nonneg χ hL ha hlam₁ hδ1 hsre hsim hmin u
      rw [P9.nearP3summand_eq_P3, hind, mul_one] at hnn
      by_contra hcon
      push Not at hcon
      have hpos : 0 < (Work.LinnikContract.zeroMult χ u : ℝ) := by linarith
      have hlt := mul_lt_mul_of_pos_left hcon hpos
      rw [mul_zero] at hlt
      linarith
    calc (Work.ZeroFreeTables.P3 ((a + lam₁) / ((s - u) * (L : ℂ)))).re
        = 1 * (Work.ZeroFreeTables.P3 ((a + lam₁) / ((s - u) * (L : ℂ)))).re := by ring
      _ ≤ (Work.LinnikContract.zeroMult χ u : ℝ)
            * (Work.ZeroFreeTables.P3 ((a + lam₁) / ((s - u) * (L : ℂ)))).re :=
          mul_le_mul_of_nonneg_right hmult hP3
  have hnear : ∑ u ∈ T.filter p,
        (Work.ZeroFreeTables.P3 ((a + lam₁) / ((s - u) * (L : ℂ)))).re
      ≤ ∑ u ∈ S ∪ T, P9.nearP3summand N L χ s a lam₁ δ u :=
    le_trans (Finset.sum_le_sum hnear_pt)
      (Finset.sum_le_sum_of_subset_of_nonneg
        (fun u hu => Finset.mem_union_right S (Finset.mem_filter.mp hu).1)
        (fun u _ _ => nearP3summand_nonneg χ hL ha hlam₁ hδ1 hsre hsim hmin u))
  have hfar : ∑ u ∈ T.filter (fun u => ¬ p u),
        (Work.ZeroFreeTables.P3 ((a + lam₁) / ((s - u) * (L : ℂ)))).re
      ≤ (T.card : ℝ) * (8 * (a + lam₁) / (δ * L)) := by
    have hconst : 0 ≤ 8 * (a + lam₁) / (δ * L) := by positivity
    have hpt : ∀ u ∈ T.filter (fun u => ¬ p u),
        (Work.ZeroFreeTables.P3 ((a + lam₁) / ((s - u) * (L : ℂ)))).re
          ≤ 8 * (a + lam₁) / (δ * L) := by
      intro u hu
      rw [Finset.mem_filter] at hu
      obtain ⟨huT, hpu⟩ := hu
      have hminu : lam₁ ≤ (1 - u.re) * L := hmin u (hT u huT) (hTim u huT)
      have hpune : ¬ (‖(1 : ℂ) + (s.im : ℂ) * Complex.I - u‖ ≤ δ) := by simpa [hp] using hpu
      have hfar_lt : δ < ‖(1 : ℂ) + (s.im : ℂ) * Complex.I - u‖ := lt_of_not_ge hpune
      exact le_trans (le_abs_self _) (P9.P3term_abs_le_of_far hL ha hlam₁ hδ haδ hsre hminu hfar_lt)
    calc ∑ u ∈ T.filter (fun u => ¬ p u),
          (Work.ZeroFreeTables.P3 ((a + lam₁) / ((s - u) * (L : ℂ)))).re
        ≤ ∑ u ∈ T.filter (fun u => ¬ p u), 8 * (a + lam₁) / (δ * L) := Finset.sum_le_sum hpt
      _ = ((T.filter (fun u => ¬ p u)).card : ℝ) * (8 * (a + lam₁) / (δ * L)) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (T.card : ℝ) * (8 * (a + lam₁) / (δ * L)) := by
          apply mul_le_mul_of_nonneg_right _ hconst
          exact_mod_cast Finset.card_le_card (Finset.filter_subset _ _)
  rw [hTsplit]
  linarith [hnear, hfar, htsum]



/-! ## Elementary facts about `P₃`, `P₃ℝ`, `Φ`, `A913` -/

/-- `P₃` at a real argument is `P₃ℝ`. -/
theorem P3R_eq_re_P3 (x : ℝ) : (P3 (x : ℂ)).re = P3R x := by
  have h : P3 (x : ℂ) = ((P3R x : ℝ) : ℂ) := by
    simp only [P3, P3R]
    push_cast
    ring
  rw [h, Complex.ofReal_re]

/-- `P₃` has real coefficients, so it commutes with conjugation. -/
theorem P3_conj (w : ℂ) : P3 ((starRingEnd ℂ) w) = (starRingEnd ℂ) (P3 w) := by
  simp only [P3]
  have hc : ((2 : ℂ) / 3) = ((2 / 3 : ℝ) : ℂ) := by norm_num
  rw [hc]
  simp only [map_add, map_mul, map_pow, Complex.conj_ofReal]

/-- `Re P₃` is conjugation invariant. -/
theorem P3_re_conj (w : ℂ) : (P3 ((starRingEnd ℂ) w)).re = (P3 w).re := by
  rw [P3_conj]; simp

/-- `Φ x y (-t) = Φ x y t`. -/
theorem PhiG_neg (x y t : ℝ) :
    (P3 ((x : ℂ) / ((y : ℂ) - (t : ℂ) * Complex.I))).re = P9.PhiG x y t := by
  have h : ((x : ℂ) / ((y : ℂ) - (t : ℂ) * Complex.I))
      = (starRingEnd ℂ) ((x : ℂ) / ((y : ℂ) + (t : ℂ) * Complex.I)) := by
    apply Complex.ext <;>
      simp [Complex.div_re, Complex.div_im, Complex.normSq_apply] <;> ring
  unfold P9.PhiG
  rw [h, P3_re_conj]

/-- `A913` in terms of `Φ`. -/
theorem A913_eq (a lam₁ lam₀ K Δ : ℝ) :
    A913 a lam₁ lam₀ K Δ
      = (K ^ 2 + 3 / 4) * P9.PhiG (a + lam₁) (a + lam₁) Δ
        + 2 * K * P9.PhiG (a + lam₁) (a + lam₀) Δ
        - K * P9.PhiG (a + lam₁) a Δ := by
  have h1 : ((K : ℂ)) ^ 2 + (3 / 4 : ℂ) = ((K ^ 2 + 3 / 4 : ℝ) : ℂ) := by push_cast; ring
  have h2 : (2 : ℂ) * (K : ℂ) = ((2 * K : ℝ) : ℂ) := by push_cast; ring
  have ha1 : ((a : ℂ) + (lam₁ : ℂ)) = ((a + lam₁ : ℝ) : ℂ) := by push_cast; ring
  have ha0 : ((a : ℂ) + (lam₀ : ℂ)) = ((a + lam₀ : ℝ) : ℂ) := by push_cast; ring
  simp only [A913, P9.PhiG, h1, h2, ha1, ha0]
  simp only [Complex.add_re, Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
  ring

/-! ## The test points `σ + i t` and the identification of the arguments -/

/-- The test point `σ + i t` with `σ = 1 + a/L`. -/
def sPt (a L t : ℝ) : ℂ := ((1 + a / L : ℝ) : ℂ) + ((t : ℝ) : ℂ) * Complex.I

/-- `(σ + i t - ρ)·L` for a zero `ρ` with `ρ = (1 - λ/L) + iγ`. -/
theorem sPt_sub_mul_eq {a L lam gam t : ℝ} (hL : L ≠ 0) {ρ : ℂ}
    (hre : ρ.re = 1 - lam / L) (him : ρ.im = gam) :
    (sPt a L t - ρ) * (L : ℂ) = ((a + lam : ℝ) : ℂ) + (((t - gam) * L : ℝ) : ℂ) * Complex.I := by
  have h1 : (sPt a L t).re = 1 + a / L := by simp [sPt]
  have h2 : (sPt a L t).im = t := by simp [sPt]
  apply Complex.ext <;>
    simp only [Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im, Complex.add_re,
      Complex.add_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      mul_one, mul_zero, add_zero, zero_add, sub_zero, h1, h2, hre, him] <;>
    field_simp <;> ring

/-- The zero term `Re P₃(α/((s-u)𝓛))` at the test point `s = σ + it`, in the `Φ` normal form. -/
theorem P3_arg_eq {a L lam gam t : ℝ} (hL : L ≠ 0) {ρ : ℂ}
    (hre : ρ.re = 1 - lam / L) (him : ρ.im = gam) (A : ℝ) :
    (P3 (A / ((sPt a L t - ρ) * (L : ℂ)))).re = P9.PhiG A (a + lam) ((t - gam) * L) := by
  rw [sPt_sub_mul_eq hL hre him]
  rfl

/-- The zero term at a pole point `s = 1`: `(s-1)𝓛 = a + it𝓛`. -/
theorem P3_arg_eq_pole {a L t : ℝ} (hL : L ≠ 0) (A : ℝ) :
    (P3 (A / ((sPt a L t - 1) * (L : ℂ)))).re = P9.PhiG A a (t * L) := by
  have h := P3_arg_eq (a := a) (L := L) (lam := 0) (gam := 0) (t := t) (ρ := 1) hL
    (by simp) (by simp) A
  simpa [sPt] using h

/-! ## The three case bridges: from the eight point bounds to `ineq913` -/

/-- **Case A** (`χ₁² ≠ 1`, `χ₁³ ≠ 1`).  From the eight point bounds of HB (9.2)–(9.7) (with
`(1/6 + ε₁)` the `k = 1` error and `α = a + λ₁`) and HB (9.1) one obtains
`0 ≤ p913 + αε` as soon as `A913 ≥ 0` and the errors plus `αε₁(K²+3K+3/2)` fit into `αε`. -/
theorem caseA_bridge {a lam₁ lam₀ K ε ε₁ Δ : ℝ}
    {S1 S2 S3 S4 S5 S6 S7 S8 e1 e2 e3 e4 e5 e6 e7 e8 corr : ℝ}
    (hK : 0 ≤ K)
    (h1 : S1 ≤ P3R ((a + lam₁) / a) + e1)
    (h2 : S2 ≤ -P3R ((a + lam₁) / (a + lam₀)) - P9.PhiG (a + lam₁) (a + lam₁) Δ
        + (a + lam₁) * (1/6 + ε₁) + e2)
    (h3 : S3 ≤ P9.PhiG (a + lam₁) a Δ + e3)
    (h4 : S4 ≤ -P3R 1 - P9.PhiG (a + lam₁) (a + lam₀) Δ + (a + lam₁) * (1/6 + ε₁) + e4)
    (h5 : S5 ≤ (a + lam₁) * (1/6 + ε₁) + e5)
    (h6 : S6 ≤ -P9.PhiG (a + lam₁) (a + lam₁) Δ + (a + lam₁) * (1/6 + ε₁) + e6)
    (h7 : S7 ≤ (a + lam₁) * (1/6 + ε₁) + e7)
    (h8 : S8 ≤ (a + lam₁) * (1/6 + ε₁) + e8)
    (hcomb : 0 ≤ (K ^ 2 + 1 / 2) * (S1 + S2) + K * (S3 + 2 * S4 + S5)
        + (1 / 4) * (S6 + 2 * S7 + S8) + corr)
    (hA : 0 ≤ A913 a lam₁ lam₀ K Δ)
    (habs : (K ^ 2 + 1 / 2) * (e1 + e2) + K * (e3 + 2 * e4 + e5) + (1 / 4) * (e6 + 2 * e7 + e8)
        + corr + (a + lam₁) * ε₁ * (K ^ 2 + 3 * K + 3 / 2) ≤ (a + lam₁) * ε) :
    ineq913 lam₁ lam₀ a K ε := by
  rw [ineq913, p913, psi13] at *
  rw [A913_eq] at hA
  have hK0 : 0 ≤ K ^ 2 + 1 / 2 := by positivity
  have h14 : (0 : ℝ) ≤ 1 / 4 := by norm_num
  nlinarith [hcomb, h1, h2, h3, h4, h5, h6, h7, h8, hA, habs, hK0, h14]

/-- **Case B** (`χ₁³ = 1`, `χ₁² ≠ 1`).  The terms `Σ(·, χ₁²)` are rewritten through
`Σ(s, χ₁²) = Σ(conj s, χ₁)` and keep the zeros `ρ₁, ρ₀` at the conjugate points; the
resulting drop-out quantity is `A913 + B` with `B` the combination of `rescale_variants`. -/
theorem caseB_bridge {a lam₁ lam₀ K ε ε₁ Δ tB : ℝ}
    {S1 S2 S3 S4 S5 S6 S7 S8 e1 e2 e3 e4 e5 e6 e7 e8 corr : ℝ}
    (hK : 0 ≤ K) (hα : 0 ≤ a + lam₁)
    (h1 : S1 ≤ P3R ((a + lam₁) / a) + e1)
    (h2 : S2 ≤ -P3R ((a + lam₁) / (a + lam₀)) - P9.PhiG (a + lam₁) (a + lam₁) Δ
        + (a + lam₁) * (1/6 + ε₁) + e2)
    (h3 : S3 ≤ P9.PhiG (a + lam₁) a Δ + e3)
    (h4 : S4 ≤ -P3R 1 - P9.PhiG (a + lam₁) (a + lam₀) Δ + (a + lam₁) * (1/6 + ε₁) + e4)
    (h5 : S5 ≤ -P9.PhiG (a + lam₁) (a + lam₁) tB + (a + lam₁) * (1/6 + ε₁) + e5)
    (h6 : S6 ≤ -P9.PhiG (a + lam₁) (a + lam₁) Δ + (a + lam₁) * (1/6 + ε₁) + e6)
    (h7 : S7 ≤ -P9.PhiG (a + lam₁) (a + lam₀) tB + (a + lam₁) * (1/6 + ε₁) + e7)
    (h8 : S8 ≤ P9.PhiG (a + lam₁) a tB + e8)
    (hcomb : 0 ≤ (K ^ 2 + 1 / 2) * (S1 + S2) + K * (S3 + 2 * S4 + S5)
        + (1 / 4) * (S6 + 2 * S7 + S8) + corr)
    (hA : 0 ≤ A913 a lam₁ lam₀ K Δ)
    (hB : 0 ≤ K * P9.PhiG (a + lam₁) (a + lam₁) tB + (1 / 2) * P9.PhiG (a + lam₁) (a + lam₀) tB
        - (1 / 4) * P9.PhiG (a + lam₁) a tB)
    (habs : (K ^ 2 + 1 / 2) * (e1 + e2) + K * (e3 + 2 * e4 + e5) + (1 / 4) * (e6 + 2 * e7 + e8)
        + corr + (a + lam₁) * ε₁ * (K ^ 2 + 3 * K + 5 / 4) ≤ (a + lam₁) * ε) :
    ineq913 lam₁ lam₀ a K ε := by
  rw [ineq913, p913, psi13] at *
  rw [A913_eq] at hA
  have hK0 : 0 ≤ K ^ 2 + 1 / 2 := by positivity
  have h14 : (0 : ℝ) ≤ 1 / 4 := by norm_num
  nlinarith [hcomb, h1, h2, h3, h4, h5, h6, h7, h8, hA, hB, habs, hK0, h14]

/-- **Case C** (`χ₁² = 1`).  Here `χ₁` is real, so the conjugate zeros `ρ̄₁, ρ̄₀` are also zeros
of `χ₁`; the drop-out quantity is `A' + C + D` of HB, whose pieces are non-negative by
`rescale_variants` and `CaseC_D`. -/
theorem caseC_bridge {a lam₁ lam₀ K ε ε₁ Δ β γ : ℝ}
    {S1 S2 S3 S4 S5 S6 S7 S8 e1 e2 e3 e4 e5 e6 e7 e8 corr : ℝ}
    (hK : 0 ≤ K) (hα : 0 ≤ a + lam₁)
    (h1 : S1 ≤ P3R ((a + lam₁) / a) + e1)
    (h2 : S2 ≤ -P3R ((a + lam₁) / (a + lam₀)) - P9.PhiG (a + lam₁) (a + lam₁) Δ
        - P9.PhiG (a + lam₁) (a + lam₁) β + (a + lam₁) * (1/6 + ε₁) + e2)
    (h3 : S3 ≤ P9.PhiG (a + lam₁) a Δ + e3)
    (h4 : S4 ≤ -P3R 1 - P9.PhiG (a + lam₁) (a + lam₀) Δ - P9.PhiG (a + lam₁) (a + lam₀) β
        - P9.PhiG (a + lam₁) (a + lam₁) γ + (a + lam₁) * (1/6 + ε₁) + e4)
    (h5 : S5 ≤ P9.PhiG (a + lam₁) a β + e5)
    (h6 : S6 ≤ -P9.PhiG (a + lam₁) (a + lam₁) Δ - P9.PhiG (a + lam₁) (a + lam₀) γ
        + (a + lam₁) * (1/6 + ε₁) + e6)
    (h7 : S7 ≤ P9.PhiG (a + lam₁) a γ + e7)
    (h8 : S8 ≤ -P9.PhiG (a + lam₁) (a + lam₁) β - P9.PhiG (a + lam₁) (a + lam₀) γ
        + (a + lam₁) * (1/6 + ε₁) + e8)
    (hcomb : 0 ≤ (K ^ 2 + 1 / 2) * (S1 + S2) + K * (S3 + 2 * S4 + S5)
        + (1 / 4) * (S6 + 2 * S7 + S8) + corr)
    (hExpr : 0 ≤
        (K ^ 2 + 3 / 4) * P9.PhiG (a + lam₁) (a + lam₁) Δ
          + K * P9.PhiG (a + lam₁) (a + lam₀) Δ - K * P9.PhiG (a + lam₁) a Δ
        + ((K ^ 2 + 3 / 4) * P9.PhiG (a + lam₁) (a + lam₁) β
          + K * P9.PhiG (a + lam₁) (a + lam₀) β - K * P9.PhiG (a + lam₁) a β)
        + (2 * K * P9.PhiG (a + lam₁) (a + lam₁) γ
          + (1 / 2) * P9.PhiG (a + lam₁) (a + lam₀) γ - (1 / 2) * P9.PhiG (a + lam₁) a γ)
        + K * P9.PhiG (a + lam₁) (a + lam₀) Δ + K * P9.PhiG (a + lam₁) (a + lam₀) β)
    (habs : (K ^ 2 + 1 / 2) * (e1 + e2) + K * (e3 + 2 * e4 + e5) + (1 / 4) * (e6 + 2 * e7 + e8)
        + corr + (a + lam₁) * ε₁ * (K ^ 2 + 2 * K + 1) ≤ (a + lam₁) * ε) :
    ineq913 lam₁ lam₀ a K ε := by
  rw [ineq913, p913, psi13] at *
  have hK0 : 0 ≤ K ^ 2 + 1 / 2 := by positivity
  have h14 : (0 : ℝ) ≤ 1 / 4 := by norm_num
  nlinarith [hcomb, h1, h2, h3, h4, h5, h6, h7, h8, hExpr, habs, hK0, h14, hα, hK]

/-! ## The point bound: engine + dropping rule -/

/-- **The point bound at a primitive non-principal character.**  Combining the engine
`pointEngine_prim` with the dropping rule `nearP3sum_ge_kept`: the sum `Σ(s,χ)` is bounded by
the (explicit) negated kept-zero terms, the `k = 1` error `αc`, the quadratic/cubic far-zero
errors (with the inverse-square zero sum replaced by `Cj` and the trivial series by `Ct`) and
one far-cost `8α/(δ𝓛)` per kept zero. -/
theorem point_bound_prim {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1)
    (hprim : χ.IsPrimitive) {L a lam₁ δ c Ct Cj : ℝ}
    (ha : 0 < a) (hlam₁ : 0 ≤ lam₁) (hδ : 0 < δ) (hδ1 : δ < 1) (hLt : 1 < L)
    (haδL : 2 * a ≤ δ * L) {s : ℂ} (hsre : s.re = 1 + a / L) (hsim : |s.im| ≤ 4)
    (hlog : (-logDeriv (DirichletCharacter.LFunction χ) s).re
      + P9.nearInvSum N χ s δ ≤ c * L)
    (par : ℕ) (hpar0 : χ.Even → par = 0) (hpar1 : χ.Odd → par = 1)
    (hS2 : |∑' n : ℕ, (((1 / (s + ((par + 2 * n : ℕ) : ℂ))) ^ 2)).re| ≤ Ct)
    (hS3 : |∑' n : ℕ, (((1 / (s + ((par + 2 * n : ℕ) : ℂ))) ^ 3)).re| ≤ Ct)
    (hJ : P9.invSqSum N χ s ≤ Cj)
    (hmin : ∀ u : ℂ, Work.LinnikContract.zeroMult χ u ≠ 0 → |u.im| ≤ 10 →
      lam₁ ≤ (1 - u.re) * L)
    (T : Finset ℂ) (hT : ∀ u ∈ T, Work.LinnikContract.zeroMult χ u ≠ 0)
    (hTim : ∀ u ∈ T, |u.im| ≤ 10) :
    SigmaP3L N L χ s a lam₁
      ≤ -(∑ u ∈ T, (P3 ((a + lam₁) / ((s - u) * (L : ℂ)))).re)
        + (a + lam₁) * c + ((a + lam₁) ^ 2 / L ^ 2) * ((1 + 4 / δ ^ 2) * Cj + Ct)
        + (2 / 3) * ((a + lam₁) ^ 3 / L ^ 3) * ((2 / δ) * (1 + 4 / δ ^ 2) * Cj + Ct)
        + (T.card : ℝ) * (8 * (a + lam₁) / (δ * L)) := by
  have h1 := P9.pointEngine_prim χ hχ hprim ha hlam₁ hδ hδ1 hLt haδL hsre
    (le_trans hsim (by norm_num : (4 : ℝ) ≤ 10)) hlog
    par hpar0 hpar1 hS2 hS3
  have h2 := nearP3sum_ge_kept χ hχ (by linarith) ha hlam₁ hδ hδ1 haδL hsre hsim hmin T hT hTim
  have hw : (0 : ℝ) ≤ 1 + 4 / δ ^ 2 := by positivity
  have hc1 : ((a + lam₁) ^ 2 / L ^ 2) * ((1 + 4 / δ ^ 2) * P9.invSqSum N χ s + Ct)
      ≤ ((a + lam₁) ^ 2 / L ^ 2) * ((1 + 4 / δ ^ 2) * Cj + Ct) := by
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    linarith [mul_le_mul_of_nonneg_left hJ hw]
  have hc2 : (2 / 3) * ((a + lam₁) ^ 3 / L ^ 3)
        * ((2 / δ) * (1 + 4 / δ ^ 2) * P9.invSqSum N χ s + Ct)
      ≤ (2 / 3) * ((a + lam₁) ^ 3 / L ^ 3) * ((2 / δ) * (1 + 4 / δ ^ 2) * Cj + Ct) := by
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    have hw2 : (0 : ℝ) ≤ (2 / δ) * (1 + 4 / δ ^ 2) := by positivity
    linarith [mul_le_mul_of_nonneg_left hJ hw2]
  linarith [h1, h2, hc1, hc2]

/-! ## The `k = 1` input at a test point (from HB Lemma 3.1) -/

/-- **The `k = 1` input** of the engine at one test point, from HB Lemma 3.1 in the form
`lemma3_1_free_gen` (`h31`, with the fixed `L₀, δ₀, ε₁`): on shrinking `δ ≤ δ₀` one has
`(-logDeriv L(·,χ)).re + nearInvSum N χ s δ ≤ (1/6 + ε₁)L` for the points `s = 1 + a/L + it`
with `|t| ≤ 3`, provided `L` is large enough (`1 ≤ L`, `1 ≤ a log L`, `a ≤ log L`). -/
theorem k1_input {L₀ δ₀ δ ε₁ a L : ℝ}
    (h31 : ∀ {M : ℕ} [NeZero M], 3 ≤ M → ∀ (χ : DirichletCharacter ℂ M), χ ≠ 1 →
      χ.IsPrimitive →
      ∀ {L : ℝ}, L₀ ≤ L → Real.log (M : ℝ) ≤ L → ∀ s : ℂ,
        1 + 1 / (L * Real.log L) ≤ s.re → s.re ≤ 1 + Real.log L / L → |s.im| ≤ 10 * L →
        (-logDeriv (DirichletCharacter.LFunction χ) s).re
          + (∑ᶠ u : ℂ, ((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
                (Metric.closedBall 0 (|s.im| + 2))) u : ℤ) *
              (if ‖(1 : ℂ) + (s.im : ℂ) * Complex.I - u‖ ≤ δ₀ then ((1 / (s - u)).re) else 0))
          ≤ (1 / 6 + ε₁) * L)
    {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) (hprim : χ.IsPrimitive)
    (hN3 : 3 ≤ N) (hL0 : L₀ ≤ L) (hlogN : Real.log (N : ℝ) ≤ L)
    (hδδ₀ : δ ≤ δ₀) (hδ₀1 : δ₀ ≤ 1) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    (ha : 0 < a) (hL1 : 1 ≤ L) (h1 : 1 ≤ a * Real.log L) (h2 : a ≤ Real.log L)
    {s : ℂ} (hsre : s.re = 1 + a / L) (hsim : |s.im| ≤ 10) :
    (-logDeriv (DirichletCharacter.LFunction χ) s).re + P9.nearInvSum N χ s δ
      ≤ (1 / 6 + ε₁) * L := by
  have hLpos : 0 < L := lt_of_lt_of_le one_pos hL1
  have hlogLpos : 0 < Real.log L := by nlinarith [h1, ha]
  have hs1 : 1 + 1 / (L * Real.log L) ≤ s.re := by
    rw [hsre]
    have hkey : 1 / (L * Real.log L) ≤ a / L := by
      field_simp
      nlinarith [h1, hLpos]
    linarith
  have hs2 : s.re ≤ 1 + Real.log L / L := by
    rw [hsre]
    have h3 : a / L ≤ Real.log L / L := div_le_div_of_nonneg_right h2 hLpos.le
    linarith
  have hs3 : |s.im| ≤ 10 * L := by nlinarith [hsim, hL1]
  have h31' := h31 hN3 χ hχ hprim hL0 hlogN s hs1 hs2 hs3
  have hre1 : (1 : ℝ) ≤ s.re := by
    rw [hsre]
    have h4 : 0 ≤ a / L := div_nonneg ha.le hLpos.le
    linarith
  have hmono : InvNearSum N χ s δ ≤ InvNearSum N χ s δ₀ :=
    P9.InvNearSum_anti χ hχ hprim hre1 hδδ₀ hδ₀1
  have heq : InvNearSum N χ s δ = P9.nearInvSum N χ s δ :=
    P9.invNearSum_eq_tsum χ hχ hprim (by linarith) hδ0 hδ1
  rw [heq] at hmono
  simp only [InvNearSum, pdiv] at hmono
  linarith [h31', hmono]


/-! ## The point bounds at the ambient level `q` -/

/-- `changeLevel` of a non-principal character is non-principal. -/
theorem changeLevel_ne_one {N q : ℕ} [NeZero q] [NeZero N] (hNq : N ∣ q)
    (φ : DirichletCharacter ℂ N) (hφ : φ ≠ 1) :
    DirichletCharacter.changeLevel hNq φ ≠ 1 :=
  fun h => hφ ((DirichletCharacter.changeLevel_eq_one_iff hNq).mp h)

/-- **The point bound at an imprimitive character.**  Reducing `Σ(s,ψ)` at the ambient level `q`
to the primitive level `N` (`SigmaP3L_changeLevel_diff`), applying the engine `point_bound_prim`
there and adding the correction back. -/
theorem point_bound_q {q N : ℕ} [NeZero q] [NeZero N] (hNq : N ∣ q)
    (φ : DirichletCharacter ℂ N) (hφ : φ ≠ 1) (hprim : φ.IsPrimitive)
    {a lam₁ δ L c Ct Cj Cc : ℝ}
    (ha : 0 < a) (hlam₁ : 0 ≤ lam₁) (hδ : 0 < δ) (hδ1 : δ < 1) (hLt : 1 < L)
    (haδL : 2 * a ≤ δ * L) {s : ℂ} (hsre : s.re = 1 + a / L) (hsim : |s.im| ≤ 4)
    (hlog : (-logDeriv (DirichletCharacter.LFunction φ) s).re
        + P9.nearInvSum N φ s δ ≤ c * L)
    (par : ℕ) (hpar0 : φ.Even → par = 0) (hpar1 : φ.Odd → par = 1)
    (hS2 : |∑' n : ℕ, (((1 / (s + ((par + 2 * n : ℕ) : ℂ))) ^ 2)).re| ≤ Ct)
    (hS3 : |∑' n : ℕ, (((1 / (s + ((par + 2 * n : ℕ) : ℂ))) ^ 3)).re| ≤ Ct)
    (hJ : P9.invSqSum N φ s ≤ Cj)
    (hmin : ∀ u : ℂ, Work.LinnikContract.zeroMult φ u ≠ 0 → |u.im| ≤ 10 →
      lam₁ ≤ (1 - u.re) * L)
    (T : Finset ℂ) (hT : ∀ u ∈ T, Work.LinnikContract.zeroMult φ u ≠ 0)
    (hTim : ∀ u ∈ T, |u.im| ≤ 10)
    (hcorr : |SigmaP3L q L (DirichletCharacter.changeLevel hNq φ) s a lam₁
        - SigmaP3L N L φ s a lam₁| ≤ Cc) :
    SigmaP3L q L (DirichletCharacter.changeLevel hNq φ) s a lam₁
      ≤ -(∑ u ∈ T, (P3 ((a + lam₁) / ((s - u) * (L : ℂ)))).re) + (a + lam₁) * c
        + ((a + lam₁) ^ 2 / L ^ 2) * ((1 + 4 / δ ^ 2) * Cj + Ct)
        + (2 / 3) * ((a + lam₁) ^ 3 / L ^ 3) * ((2 / δ) * (1 + 4 / δ ^ 2) * Cj + Ct)
        + (T.card : ℝ) * (8 * (a + lam₁) / (δ * L)) + Cc := by
  have h1 := point_bound_prim φ hφ hprim ha hlam₁ hδ hδ1 hLt haδL hsre hsim
    hlog par hpar0 hpar1 hS2 hS3 hJ hmin T hT hTim
  have h2 : SigmaP3L q L (DirichletCharacter.changeLevel hNq φ) s a lam₁
      ≤ SigmaP3L N L φ s a lam₁ + Cc := by
    have h := (abs_le.mp hcorr).2
    linarith
  linarith [h1, h2]

/-- **The point bound at the principal character.**  `SigmaP3L_changeLevel_diff` at level `1`
plus the ζ-engine `zetaEngine_principal`. -/
theorem point_bound_principal {q : ℕ} [NeZero q] {a lam₁ δ L Ct Cz C₀ Cc : ℝ}
    (ha : 0 < a) (hlam₁ : 0 ≤ lam₁) (hδ : 0 < δ) (hδ1 : δ < 1) (hLt : 1 < L)
    (haδL : 2 * a ≤ δ * L) (haL : a ≤ L)
    (hCz : ∀ s : ℂ, ‖s‖ ≤ 5 → (∑' u : ℂ, (analyticOrderNatAt completedRiemannZeta u : ℝ)
        * (1 / (1 + ‖s - u‖ ^ 2))) ≤ Cz)
    (hC0 : ∀ s : ℂ, 1 < s.re → s.re ≤ 2 → |s.im| ≤ 4 →
        (-logDeriv riemannZeta s).re ≤ (1 / (s - 1)).re + C₀)
    (hnz : ∀ t : ℝ, |t| ≤ 4 → ∀ u : ℂ, riemannZeta u = 0 →
        δ < ‖(1 : ℂ) + (t : ℂ) * Complex.I - u‖)
    {s : ℂ} (hsre : s.re = 1 + a / L) (hsim : |s.im| ≤ 4)
    (hS2 : |∑' n : ℕ, (((1 / (s + ((2 * (n + 1) : ℕ) : ℂ))) ^ 2)).re| ≤ Ct)
    (hS3 : |∑' n : ℕ, (((1 / (s + ((2 * (n + 1) : ℕ) : ℂ))) ^ 3)).re| ≤ Ct)
    (hcorr : |SigmaP3L q L (1 : DirichletCharacter ℂ q) s a lam₁
        - SigmaP3L 1 L 1 s a lam₁| ≤ Cc) :
    SigmaP3L q L (1 : DirichletCharacter ℂ q) s a lam₁
      ≤ (P3 ((a + lam₁) / ((s - 1) * (L : ℂ)))).re + ((a + lam₁) / L) * C₀
        + ((a + lam₁) ^ 2 / L ^ 2) * ((1 + 4 / δ ^ 2) * Cz + Ct)
        + (2 / 3) * ((a + lam₁) ^ 3 / L ^ 3) * ((2 / δ) * (1 + 4 / δ ^ 2) * Cz + Ct) + Cc := by
  have hLpos : 0 < L := lt_trans zero_lt_one hLt
  have hdiv1 : a / L ≤ 1 := div_le_one_of_le₀ haL hLpos.le
  have hsre2 : s.re ≤ 2 := by rw [hsre]; linarith
  have hsre1 : 1 < s.re := by rw [hsre]; have : 0 < a / L := div_pos ha hLpos; linarith
  have hnorm : ‖s‖ ≤ 5 := by
    have hsq : ‖s‖ ^ 2 = s.re ^ 2 + s.im ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]; ring
    have h2 : |s.re| ≤ 2 := abs_le.mpr ⟨by linarith, hsre2⟩
    have h4 : s.re ^ 2 ≤ 4 := by have h := abs_le.mp h2; nlinarith [h.1, h.2]
    have h16 : s.im ^ 2 ≤ 16 := by have h := abs_le.mp hsim; nlinarith [h.1, h.2]
    have h20 : ‖s‖ ^ 2 ≤ 20 := by rw [hsq]; linarith
    nlinarith [norm_nonneg s, h20]
  have hsim4 : |s.im| ≤ 4 := hsim
  have h1 := P9.zetaEngine_principal (a := a) (lam₁ := lam₁) (δ := δ) (L := L)
    (Ct := Ct) (Cz := Cz) (C₀ := C₀) ha hlam₁ hδ hδ1 hLt haδL hsre
    (fun u hu => hnz s.im hsim u hu)
    (hC0 s hsre1 hsre2 hsim4) (hCz s hnorm) hS2 hS3
  have h2 : SigmaP3L q L (1 : DirichletCharacter ℂ q) s a lam₁
      ≤ SigmaP3L 1 L 1 s a lam₁ + Cc := by
    have h := (abs_le.mp hcorr).2
    linarith
  linarith [h1, h2]



/-- **Uniform inverse-square zero sum.**  The multiplicity-weighted inverse-square zero sum of a
primitive non-principal character mod `N` is bounded by `C(log N + log(2+‖s‖) + 2)` with `C`
independent of the character and of `N` (the uniform ball count of `Λ(·,χ)`). -/
theorem invSqSum_uniform :
    ∃ C : ℝ, 0 < C ∧ ∀ {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1)
      (hprim : χ.IsPrimitive) (s : ℂ),
      P9.invSqSum N χ s ≤ C * (Real.log (N : ℝ) + Real.log (2 + ‖s‖) + 2) := by
  obtain ⟨c, hcpos, hc⟩ := Work.LinnikAreas.A5.ball_zeroCount_uniformL_A5
  obtain ⟨C, hCpos, hC⟩ := Work.LinnikAreas.ownRepelNW.orderSum_invSq_bound_of_count hcpos.le
  refine ⟨C, hCpos, ?_⟩
  intro N _ χ hχ hprim s
  have hlogN : (0 : ℝ) ≤ Real.log (N : ℝ) := by
    have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast NeZero.one_le
    exact Real.log_nonneg hN1
  have hΛan : AnalyticOnNhd ℂ (DirichletCharacter.completedLFunction χ) Set.univ :=
    fun z _ => (DirichletCharacter.differentiable_completedLFunction hχ).analyticAt z
  have hfin : ∀ S : Finset ℂ,
      ∑ u ∈ S, (analyticOrderNatAt (DirichletCharacter.completedLFunction χ) u : ℝ) *
          (1 / (1 + ‖s - u‖ ^ 2))
        ≤ C * (Real.log (2 + ‖s‖) + Real.log (N : ℝ) + 2) := by
    intro S
    exact hC (DirichletCharacter.completedLFunction χ) hΛan (Real.log (N : ℝ)) hlogN
      (fun a ρ hρ => hc χ hχ hprim a ρ hρ) s S
  have hcongr : P9.invSqSum N χ s
      = ∑' u : ℂ, (analyticOrderNatAt (DirichletCharacter.completedLFunction χ) u : ℝ) *
          (1 / (1 + ‖s - u‖ ^ 2)) := by
    unfold Work.ZeroFreeTables.P9.invSqSum
    exact tsum_congr (fun u => by
      rw [Work.LinnikAreas.FarRepel.zeroMult_eq_analyticOrderNatAt_of_isPrimitive χ hprim u])
  rw [hcongr]
  have hnn : ∀ u : ℂ, (0 : ℝ) ≤
      (analyticOrderNatAt (DirichletCharacter.completedLFunction χ) u : ℝ) *
        (1 / (1 + ‖s - u‖ ^ 2)) := by
    intro u
    have h1 : (0 : ℝ) ≤ 1 / (1 + ‖s - u‖ ^ 2) := by positivity
    positivity
  have hsumm : Summable (fun u : ℂ =>
      (analyticOrderNatAt (DirichletCharacter.completedLFunction χ) u : ℝ) *
        (1 / (1 + ‖s - u‖ ^ 2))) := summable_of_sum_le hnn hfin
  calc (∑' u : ℂ, (analyticOrderNatAt (DirichletCharacter.completedLFunction χ) u : ℝ) *
          (1 / (1 + ‖s - u‖ ^ 2)))
      ≤ C * (Real.log (2 + ‖s‖) + Real.log (N : ℝ) + 2) := hsumm.tsum_le_of_sum_le hfin
    _ = C * (Real.log (N : ℝ) + Real.log (2 + ‖s‖) + 2) := by ring

/-! ## Small helpers for the assembly -/

/-- `a + λ₁ ≤ (a³(K₀+1))^{1/3}` under the side condition `cond913`. -/
theorem alpha_le_aup {a lam₁ lam₀ K : ℝ} (ha : 0 < a) (hlam₁ : 0 ≤ lam₁) (hlam : lam₁ ≤ lam₀)
    (hcond : cond913 lam₁ lam₀ a K) :
    a + lam₁ ≤ (a ^ 3 * (Kond K + 1)) ^ (1 / 3 : ℝ) := by
  have h3 := P9.alpha_cube_le ha hlam₁ hlam hcond
  have hpos : 0 < a + lam₁ := by linarith
  calc a + lam₁ = ((a + lam₁) ^ 3) ^ (1 / 3 : ℝ) := by
        rw [← Real.rpow_natCast (a + lam₁) 3, ← Real.rpow_mul hpos.le,
          show (((3 : ℕ) : ℝ)) * (1 / 3) = 1 by norm_num, Real.rpow_one]
    _ ≤ (a ^ 3 * (Kond K + 1)) ^ (1 / 3 : ℝ) :=
        Real.rpow_le_rpow (pow_nonneg hpos.le 3) h3 (by norm_num)

/-- A parity `par` attached to a character, with `par ≤ 2` and the parity constraints. -/
theorem exists_par {N : ℕ} (φ : DirichletCharacter ℂ N) :
    ∃ par : ℕ, par ≤ 2 ∧ (φ.Even → par = 0) ∧ (φ.Odd → par = 1) :=
  ⟨if φ.Even then 0 else 1, by split <;> norm_num, fun h => if_pos h,
    fun h => if_neg h.not_even⟩

/-- `Φ(x,y,-t) = Φ(x,y,t)`. -/
theorem PhiG_neg' (x y t : ℝ) : P9.PhiG x y (-t) = P9.PhiG x y t := by
  have h : ((y : ℂ) + ((-t : ℝ) : ℂ) * Complex.I) = ((y : ℂ) - (t : ℂ) * Complex.I) := by
    push_cast; ring
  rw [P9.PhiG, h]
  exact PhiG_neg x y t

/-- `Φ(x,y,0) = P₃ℝ(x/y)`. -/
theorem PhiG_zero (x y : ℝ) : P9.PhiG x y 0 = P3R (x / y) := by
  have h : ((x : ℂ) / ((y : ℂ) + ((0 : ℝ) : ℂ) * Complex.I)) = ((x / y : ℝ) : ℂ) := by
    rw [Complex.ofReal_zero, zero_mul, add_zero, ← Complex.ofReal_div]
  rw [P9.PhiG, h]
  exact P3R_eq_re_P3 _






/-- Pole-term identification matching the numerator shape of `Σ`: the coercion of `a + lam` is
split as `↑a + ↑lam`. -/
theorem P3_arg_eq_pole_split {a L t lam : ℝ} (hL : L ≠ 0) :
    (P3 (((a : ℂ) + (lam : ℂ)) / ((sPt a L t - 1) * (L : ℂ)))).re
      = P9.PhiG (a + lam) a (t * L) := by
  rw [← Complex.ofReal_add]
  exact P3_arg_eq_pole hL (a + lam)

/-- Kept-term identification matching the numerator shape of `Σ`. -/
theorem P3_arg_eq_split {a L lam₁ lam gam t : ℝ} (hL : L ≠ 0) {ρ : ℂ}
    (hre : ρ.re = 1 - lam / L) (him : ρ.im = gam) :
    (P3 (((a : ℂ) + (lam₁ : ℂ)) / ((sPt a L t - ρ) * (L : ℂ)))).re
      = P9.PhiG (a + lam₁) (a + lam) ((t - gam) * L) := by
  rw [← Complex.ofReal_add]
  exact P3_arg_eq hL hre him (a + lam₁)

/-- `‖σ + it‖ ≤ 5` for `σ = 1 + a/L`, `a ≤ L`, `L > 0` and `|t| ≤ 3`. -/
theorem norm_sPt_le_five {a L t : ℝ} (ha : 0 < a) (haL : a ≤ L) (hL : 0 < L) (ht : |t| ≤ 4) :
    ‖sPt a L t‖ ≤ 5 := by
  have h1 : (sPt a L t).re = 1 + a / L := by simp [sPt]
  have h2 : (sPt a L t).im = t := by simp [sPt]
  have h3 : 1 + a / L ≤ 2 := by
    have h : a / L ≤ 1 := (div_le_iff₀ hL).mpr (by linarith)
    linarith
  have h4 : 1 + a / L ≥ 0 := by
    have : 0 ≤ a / L := div_nonneg ha.le hL.le
    linarith
  have h5 : (1 + a / L) ^ 2 + t ^ 2 ≤ 25 := by
    have h6 := abs_le.mp ht
    nlinarith
  calc ‖sPt a L t‖ = Real.sqrt ((sPt a L t).re ^ 2 + (sPt a L t).im ^ 2) := by
        rw [Complex.norm_def, Complex.normSq_apply]; ring_nf
    _ = Real.sqrt ((1 + a / L) ^ 2 + t ^ 2) := by rw [h1, h2]
    _ ≤ Real.sqrt 25 := Real.sqrt_le_sqrt h5
    _ = 5 := by norm_num

/-- The error budget: eight point-bound errors, each below `E`, weighted by the coefficients of
HB (9.1), total at most `2(K+1)²E`. -/
theorem sumErr_le {K E : ℝ} (hK : 0 ≤ K) {e1 e2 e3 e4 e5 e6 e7 e8 : ℝ}
    (he1 : e1 ≤ E) (he2 : e2 ≤ E) (he3 : e3 ≤ E) (he4 : e4 ≤ E) (he5 : e5 ≤ E)
    (he6 : e6 ≤ E) (he7 : e7 ≤ E) (he8 : e8 ≤ E) :
    (K ^ 2 + 1 / 2) * (e1 + e2) + K * (e3 + 2 * e4 + e5) + (1 / 4) * (e6 + 2 * e7 + e8)
      ≤ 2 * (K + 1) ^ 2 * E := by
  have h1 : e1 + e2 ≤ 2 * E := by linarith
  have h2 : e3 + 2 * e4 + e5 ≤ 4 * E := by linarith
  have h3 : e6 + 2 * e7 + e8 ≤ 4 * E := by linarith
  have h4 : (K ^ 2 + 1 / 2) * (e1 + e2) ≤ (K ^ 2 + 1 / 2) * (2 * E) :=
    mul_le_mul_of_nonneg_left h1 (by positivity)
  have h5 : K * (e3 + 2 * e4 + e5) ≤ K * (4 * E) := mul_le_mul_of_nonneg_left h2 hK
  have h6 : (1 / 4) * (e6 + 2 * e7 + e8) ≤ (1 / 4) * (4 * E) :=
    mul_le_mul_of_nonneg_left h3 (by norm_num)
  have h7 : (K ^ 2 + 1 / 2) * (2 * E) + K * (4 * E) + (1 / 4) * (4 * E) = 2 * (K + 1) ^ 2 * E := by
    ring
  linarith [h4, h5, h6, h7.le, h7.ge]

/-- Packing the component bounds into the master error `E`. -/
theorem le_E_of_le {E E2 E3 Fc Corr C0c E2c E3c Corrc : ℝ}
    (hE : E = C0c + E2c + E3c + Corrc + Fc) (hcE2 : E2 ≤ E2c) (hcE3 : E3 ≤ E3c)
    (hcCorr : Corr ≤ Corrc) {e : ℝ} (he : e ≤ E2 + E3 + Fc + Corr + C0c) : e ≤ E := by
  rw [hE]
  linarith [he, hcE2, hcE3, hcCorr]

/-- Packing the component bounds into the master error `E` (ζ form). -/
theorem le_E_of_le_zeta {E E2z E3z Fc Corr C0c E2c E3c Corrc : ℝ}
    (hE : E = C0c + E2c + E3c + Corrc + Fc) (hcE2 : E2z ≤ E2c) (hcE3 : E3z ≤ E3c)
    (hcCorr : Corr ≤ Corrc) {e : ℝ} (he : e ≤ E2z + E3z + Fc + Corr + C0c) : e ≤ E := by
  rw [hE]
  linarith [he, hcE2, hcE3, hcCorr]

/-- **HB Lemma 9.1 / (9.13), the complex case at the wide height `|Im ρ₀| ≤ 2`.**

`Work.ZeroFreeTables.HBLemma9_1` with `IsZ χ₁ ρ₀` relaxed to `zeroMult χ₁ ρ₀ ≠ 0 ∧ |Im ρ₀| ≤ 2`,
`¬(χ₁ ^ 2 = 1 ∧ ρ₁.im = 0)` strengthened to `χ₁ ^ 2 ≠ 1`, and the (then vacuous) exclusion of the
conjugate zero dropped. -/
theorem HBLemma9_1Wide_proof : ∀ (a K ε : ℝ), 0 < a → 0 < K → 0 < ε → ∃ q₀ : ℕ,
    ∀ q : ℕ, q₀ ≤ q → ∀ [NeZero q] (χ₁ : DirichletCharacter ℂ q) (ρ₁ ρ₀ : ℂ),
      Work.ZeroFreeTables.IsMin1WideAt 10 χ₁ ρ₁ → χ₁ ^ 2 ≠ 1 →
      Work.LinnikContract.IsZ χ₁ ρ₁ →
      Work.LinnikContract.zeroMult χ₁ ρ₀ ≠ 0 → |ρ₀.im| ≤ 2 → ρ₁ ≠ ρ₀ →
      Work.ZeroFreeTables.cond913 (Work.LinnikContract.lamOf q ρ₁)
        (Work.LinnikContract.lamOf q ρ₀) a K →
      Work.ZeroFreeTables.ineq913 (Work.LinnikContract.lamOf q ρ₁)
        (Work.LinnikContract.lamOf q ρ₀) a K ε := by
  intro a K ε ha hK hε
  -- ## the constants
  set ε₁ : ℝ := ε / (4 * (K ^ 2 + 3 * K + 4)) with hε₁def
  have hε₁pos : 0 < ε₁ := by rw [hε₁def]; positivity
  have hε₁bud : ε₁ * (K ^ 2 + 3 * K + 3 / 2) ≤ ε / 4 := by
    rw [hε₁def, div_mul_eq_mul_div,
      div_le_iff₀ (by positivity : (0 : ℝ) < 4 * (K ^ 2 + 3 * K + 4))]
    nlinarith [hε.le, sq_nonneg K, hK.le]
  obtain ⟨L₀, δ₀, hδ₀pos, hδ₀lt1, h31⟩ :=
    Work.LinnikAreas.l31free.lemma3_1_free_gen (φ := 1 / 3) (by norm_num) hε₁pos
      Work.LinnikAreas.LBound13_holds
  obtain ⟨εζ, hεζpos, hεζ⟩ := zeta_zeroFree_near_axis_w
  obtain ⟨Ct, hCtpos, hCtS⟩ := Work.ZeroFreeTables.P9.parity_bound_re
  obtain ⟨Czζ, hCzζpos, hCzζ⟩ := P9.zetaZeroInvSq_tsum
  obtain ⟨C₀, hC₀pos, hC₀b⟩ := P9.zetaLogDeriv_pole_split
  obtain ⟨Cc, hCcpos, hCc⟩ := P9.SigmaP3L_changeLevel_diff
  obtain ⟨Cp1, hCp1pos, hCp1⟩ := P9.primeFactors_logPow_div_le 1 (by norm_num)
  obtain ⟨Cp2, hCp2pos, hCp2⟩ := P9.primeFactors_logPow_div_le 2 (by norm_num)
  obtain ⟨Cp3, hCp3pos, hCp3⟩ := P9.primeFactors_logPow_div_le 3 (by norm_num)
  set Cp : ℝ := max (max Cp1 Cp2) Cp3 with hCpdef
  have hCpnn : 0 ≤ Cp := by rw [hCpdef]; positivity
  have hCp1le : Cp1 ≤ Cp := by rw [hCpdef]; exact le_trans (le_max_left _ _) (le_max_left _ _)
  have hCp2le : Cp2 ≤ Cp := by rw [hCpdef]; exact le_trans (le_max_right _ _) (le_max_left _ _)
  have hCp3le : Cp3 ≤ Cp := by rw [hCpdef]; exact le_max_right _ _
  obtain ⟨Cq, hCqpos, hCq⟩ := invSqSum_uniform
  set Cn : ℝ := max Cq 1 with hCndef
  have hCnpos : 0 < Cn := by rw [hCndef]; positivity
  have hCqle : Cq ≤ Cn := by rw [hCndef]; exact le_max_left _ _
  set Cz : ℝ := max Czζ 1 with hCzdef
  have hCzpos : 0 < Cz := by rw [hCzdef]; positivity
  have hCzζle : Czζ ≤ Cz := by rw [hCzdef]; exact le_max_left _ _
  set δ : ℝ := min δ₀ (min (εζ / 2) (1 / 2)) with hδdef
  have hδpos : 0 < δ := lt_min hδ₀pos (lt_min (by linarith only [hεζpos]) (by norm_num))
  have hδleδ₀ : δ ≤ δ₀ := min_le_left _ _
  have hδleζ : δ ≤ εζ / 2 := le_trans (min_le_right _ _) (min_le_left _ _)
  have hδlehalf : δ ≤ 1 / 2 := le_trans (min_le_right _ _) (min_le_right _ _)
  have hδlt1 : δ < 1 := lt_of_le_of_lt hδlehalf (by norm_num)
  set aup : ℝ := (a ^ 3 * (Kond K + 1)) ^ (1 / 3 : ℝ) with haupdef
  have hauppos : 0 < aup := by
    rw [haupdef]
    exact Real.rpow_pos_of_pos (by
      have h1 : 0 < Kond K := lt_min (by positivity) (by positivity)
      positivity) _
  obtain ⟨qabs, habs⟩ := P9.absorption_eventual a K ε aup δ C₀ Ct Cn Cz Cc Cp
    ha hK.le hε hδpos hauppos (le_of_lt hC₀pos) hCtpos hCnpos hCzpos hCcpos.le hCpnn
  set Λ : ℝ := max (max L₀ (2 * a / δ))
    (max (max a 10) (Real.exp (max (1 / a) (max a 1)))) with hΛdef
  refine ⟨max qabs (max 3 (Nat.ceil (Real.exp Λ))), ?_⟩
  intro q hq hqne χ₁ ρ₁ ρ₀ hmin1 hsq hZ1 hzm0 him0 hne hcond
  have hqq : 3 ≤ q := by have h := hq; simp only [max_le_iff] at h; exact h.2.1
  have hqexp : Nat.ceil (Real.exp Λ) ≤ q := by
    have h := hq; simp only [max_le_iff] at h; exact h.2.2
  have hΛL : Λ ≤ Real.log q := by
    have h1 : Real.exp Λ ≤ (q : ℝ) :=
      le_trans (Nat.le_ceil (Real.exp Λ)) (by exact_mod_cast hqexp)
    rw [← Real.log_exp Λ]
    exact Real.log_le_log (Real.exp_pos Λ) h1
  set L : ℝ := Real.log q with hLdef
  have hL₀L : L₀ ≤ L := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hΛL
  have h2aδL : 2 * a / δ ≤ L := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hΛL
  have haL : a ≤ L := le_trans (le_trans (le_trans (le_max_left _ _) (le_max_left _ _))
    (le_max_right _ _)) hΛL
  have hexpL : Real.exp (max (1 / a) (max a 1)) ≤ L :=
    le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hΛL
  have heL : Real.exp 1 ≤ L := by
    refine le_trans (Real.exp_le_exp.mpr ?_) hexpL
    exact le_trans (le_max_right a 1) (le_max_right (1 / a) (max a 1))
  have hLt : 1 < L := lt_of_lt_of_le (Real.one_lt_exp_iff.mpr one_pos) heL
  have hLpos : 0 < L := lt_trans zero_lt_one hLt
  have hLne : L ≠ 0 := ne_of_gt hLpos
  have hL1 : 1 ≤ L := le_of_lt hLt
  have h12L : (1 : ℝ) / 2 ≤ L := by linarith only [hLt]
  have hlogLnn : 0 ≤ Real.log L := Real.log_nonneg hL1
  have hlogLmax : max (1 / a) (max a 1) ≤ Real.log L := by
    rw [← Real.log_exp (max (1 / a) (max a 1))]
    exact Real.log_le_log (Real.exp_pos _) hexpL
  have hlogL1a : 1 / a ≤ Real.log L := le_trans (le_max_left _ _) hlogLmax
  have hlogLa : a ≤ Real.log L :=
    le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hlogLmax
  have h1aL : 1 ≤ a * Real.log L := by
    have h := mul_le_mul_of_nonneg_left hlogL1a ha.le
    have h2 : a * (1 / a) = 1 := by field_simp
    linarith only [h, h2]
  have haδL : 2 * a ≤ δ * L := by
    rw [div_le_iff₀ hδpos] at h2aδL
    linarith only [h2aδL]
  -- ## the E-terms
  set Cj : ℝ := Cn * (L + 6) + Cz with hCjdef
  have hCjnn : 0 ≤ Cj := by rw [hCjdef]; positivity
  set Sp1 : ℝ := ∑ p ∈ q.primeFactors, Real.log (p : ℝ) / (p : ℝ) with hSp1def
  set Sp2 : ℝ := ∑ p ∈ q.primeFactors, (Real.log (p : ℝ)) ^ 2 / (p : ℝ) with hSp2def
  set Sp3 : ℝ := ∑ p ∈ q.primeFactors, (Real.log (p : ℝ)) ^ 3 / (p : ℝ) with hSp3def
  set Corr : ℝ := (Cc / L) * ((a + Work.LinnikContract.lamOf q ρ₁) * Sp1 + ((a + Work.LinnikContract.lamOf q ρ₁) ^ 2 / L) * Sp2
    + ((a + Work.LinnikContract.lamOf q ρ₁) ^ 3 / L ^ 2) * Sp3) with hCorrdef
  set E : ℝ := (aup / L) * C₀ + (aup ^ 2 / L ^ 2) * ((1 + 4 / δ ^ 2) * Cj + Ct)
    + (2 / 3) * (aup ^ 3 / L ^ 3) * ((2 / δ) * (1 + 4 / δ ^ 2) * Cj + Ct)
    + (Cc / L) * (aup * Cp * (Real.log L) ^ 2 + (aup ^ 2 / L) * Cp * (Real.log L) ^ 3
        + (aup ^ 3 / L ^ 2) * Cp * (Real.log L) ^ 4)
    + 64 * aup / (δ * L) with hEdef
  have hEbound : 2 * (K + 1) ^ 2 * E ≤ a * ε / 2 := by
    have h := habs q (by have hh := hq; simp only [max_le_iff] at hh; omega)
    rw [show Real.log q = L from hLdef.symm] at h
    rw [hEdef, hCjdef]
    exact h
  -- ## basic bounds
  have hlam₁nn : 0 ≤ Work.LinnikContract.lamOf q ρ₁ := P9.lamOf_nonneg hZ1
  have hlam₀nn : 0 ≤ Work.LinnikContract.lamOf q ρ₀ := lamOf_nonneg_of_zeroMult hzm0
  have hlam₁lam₀ : Work.LinnikContract.lamOf q ρ₁ ≤ Work.LinnikContract.lamOf q ρ₀ := hmin1.2 χ₁ ρ₀ hZ1.1 hzm0 (by linarith only [him0])
  have hχ₁ne : χ₁ ≠ 1 := hZ1.1
  have hα0 : 0 ≤ a + Work.LinnikContract.lamOf q ρ₁ := by linarith only [ha, hlam₁nn]
  have hαaup : a + Work.LinnikContract.lamOf q ρ₁ ≤ aup := by
    rw [haupdef]
    exact alpha_le_aup ha hlam₁nn hlam₁lam₀ hcond
  have hαaup2 : (a + Work.LinnikContract.lamOf q ρ₁) ^ 2 ≤ aup ^ 2 := pow_le_pow_left₀ hα0 hαaup 2
  have hαaup3 : (a + Work.LinnikContract.lamOf q ρ₁) ^ 3 ≤ aup ^ 3 := pow_le_pow_left₀ hα0 hαaup 3
  have hlamOf_eq : ∀ u : ℂ, Work.LinnikContract.lamOf q u = (1 - u.re) * L := by
    intro u; rw [Work.LinnikContract.lamOf, ← hLdef]
  have hminOf : ∀ (ψ : DirichletCharacter ℂ q), ψ ≠ 1 → ∀ u : ℂ,
      Work.LinnikContract.zeroMult ψ u ≠ 0 → |u.im| ≤ 10 →
      Work.LinnikContract.lamOf q ρ₁ ≤ (1 - u.re) * L := by
    intro ψ hψ u hu him
    rw [← hlamOf_eq u]
    exact hmin1.2 ψ u hψ hu him
  have hminPrim : ∀ {N : ℕ} [NeZero N] (hNq : N ∣ q) (φ : DirichletCharacter ℂ N), φ ≠ 1 →
      φ.IsPrimitive → ∀ u : ℂ, Work.LinnikContract.zeroMult φ u ≠ 0 → |u.im| ≤ 10 →
      Work.LinnikContract.lamOf q ρ₁ ≤ (1 - u.re) * L := by
    intro N _ hNq φ hφ hprim u hu him
    refine hminOf (DirichletCharacter.changeLevel hNq φ) (changeLevel_ne_one hNq φ hφ) u ?_ him
    rw [Work.ZeroFreeTables.Table4.zeroMult_changeLevel hNq φ u]
    exact hu
  -- ## the families of bounds
  have hSpr : ∀ (par : ℕ), par ≤ 2 → ∀ t : ℝ,
      |∑' n : ℕ, (((1 / (sPt a L t + ((par + 2 * n : ℕ) : ℂ))) ^ 2)).re| ≤ Ct ∧
      |∑' n : ℕ, (((1 / (sPt a L t + ((par + 2 * n : ℕ) : ℂ))) ^ 3)).re| ≤ Ct := by
    intro par hpar t
    refine hCtS (sPt a L t) ?_ par hpar
    have h : (sPt a L t).re = 1 + a / L := by simp [sPt]
    rw [h]
    have : 0 ≤ a / L := div_nonneg ha.le hLpos.le
    linarith only [this]
  have hSzeta : ∀ t : ℝ,
      |∑' n : ℕ, (((1 / (sPt a L t + ((2 * (n + 1) : ℕ) : ℂ))) ^ 2)).re| ≤ Ct ∧
      |∑' n : ℕ, (((1 / (sPt a L t + ((2 * (n + 1) : ℕ) : ℂ))) ^ 3)).re| ≤ Ct := by
    intro t
    have h := hSpr 2 (by norm_num) t
    have hnat : ∀ n : ℕ, (2 * (n + 1) : ℕ) = 2 + 2 * n := fun n => by ring
    constructor
    · refine le_trans (le_of_eq ?_) h.1
      apply congrArg abs
      apply tsum_congr
      intro n
      rw [hnat n]
    · refine le_trans (le_of_eq ?_) h.2
      apply congrArg abs
      apply tsum_congr
      intro n
      rw [hnat n]
  have hCzZeta : ∀ s : ℂ, ‖s‖ ≤ 5 →
      (∑' u : ℂ, (analyticOrderNatAt completedRiemannZeta u : ℝ) * (1 / (1 + ‖s - u‖ ^ 2))) ≤ Cz := by
    intro s hs
    exact le_trans (hCzζ s hs) hCzζle
  have hC0b' : ∀ s : ℂ, 1 < s.re → s.re ≤ 2 → |s.im| ≤ 4 →
      (-logDeriv riemannZeta s).re ≤ (1 / (s - 1)).re + C₀ := hC₀b
  have hnzδ : ∀ t : ℝ, |t| ≤ 4 → ∀ u : ℂ, riemannZeta u = 0 →
      δ < ‖(1 : ℂ) + (t : ℂ) * Complex.I - u‖ := by
    intro t ht u hu
    by_contra hle
    push Not at hle
    have hre1 : |(1 : ℝ) - u.re| ≤ δ := by
      have h := Complex.abs_re_le_norm ((1 : ℂ) + (t : ℂ) * Complex.I - u)
      have h2 : ((1 : ℂ) + (t : ℂ) * Complex.I - u).re = 1 - u.re := by
        simp [Complex.sub_re, Complex.add_re, Complex.mul_re]
      rw [h2] at h
      linarith only [h, hle]
    have him1 : |t - u.im| ≤ δ := by
      have h := Complex.abs_im_le_norm ((1 : ℂ) + (t : ℂ) * Complex.I - u)
      have h2 : ((1 : ℂ) + (t : ℂ) * Complex.I - u).im = t - u.im := by
        simp [Complex.sub_im, Complex.add_im, Complex.mul_im]
      rw [h2] at h
      linarith only [h, hle]
    have hure : 1 - εζ ≤ u.re := by
      have h := (abs_le.mp hre1).2
      linarith only [h, hδleζ, hεζpos]
    have hure2 : u.re ≤ 2 := by
      have h := (abs_le.mp hre1).1
      linarith only [h, hδlehalf]
    have huim : |u.im| ≤ 5 := by
      have h1 := (abs_le.mp him1).1
      have h2 := (abs_le.mp him1).2
      have h3 := (abs_le.mp ht)
      rw [abs_le]
      constructor <;> linarith only [h1, h2, h3.1, h3.2, hδlehalf]
    have hz : ((u.re : ℂ) + Complex.I * (u.im : ℂ)) = u := by
      rw [mul_comm]; exact Complex.re_add_im u
    exact hεζ u.im u.re huim hure hure2 (by rw [hz]; exact hu)
  have hJOf : ∀ {N : ℕ} [NeZero N] (hNq : N ∣ q) (φ : DirichletCharacter ℂ N), φ ≠ 1 →
      φ.IsPrimitive → ∀ s : ℂ, ‖s‖ ≤ 5 → P9.invSqSum N φ s ≤ Cj := by
    intro N _ hNq φ hφ hprim s hs
    have h1 : P9.invSqSum N φ s ≤ Cq * (Real.log (N : ℝ) + Real.log (2 + ‖s‖) + 2) :=
      hCq φ hφ hprim s
    have h2 : Real.log (N : ℝ) ≤ L := by
      rw [hLdef]
      have hNpos : (0 : ℝ) < (N : ℝ) := by
        exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
      refine Real.log_le_log hNpos ?_
      exact_mod_cast Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne q)) hNq
    have h3 : Real.log (2 + ‖s‖) ≤ 4 := by
      have h7 : 2 + ‖s‖ ≤ 7 := by linarith only [hs]
      have h8 : (7 : ℝ) ≤ Real.exp 4 := by
        have h5 : Real.exp 4 = Real.exp 1 ^ 4 := by simpa using Real.exp_nat_mul 1 4
        have h6 : (2 : ℝ) < Real.exp 1 := Real.exp_one_gt_two
        have h9 : (2 : ℝ) ^ 4 < Real.exp 1 ^ 4 := pow_lt_pow_left₀ h6 (by norm_num) (by norm_num)
        rw [h5]
        linarith only [h9]
      calc Real.log (2 + ‖s‖) ≤ Real.log 7 := Real.log_le_log (by positivity) h7
        _ ≤ 4 := (Real.log_le_iff_le_exp (by norm_num)).mpr h8
    have h7 : Cq * (Real.log (N : ℝ) + Real.log (2 + ‖s‖) + 2) ≤ Cj := by
      have h8 : Real.log (N : ℝ) + Real.log (2 + ‖s‖) + 2 ≤ L + 6 := by linarith only [h2, h3]
      have h9 : Cq * (Real.log (N : ℝ) + Real.log (2 + ‖s‖) + 2) ≤ Cn * (L + 6) := by
        have h10 : (0 : ℝ) ≤ Real.log (N : ℝ) + Real.log (2 + ‖s‖) + 2 := by
          have ha1 : (0 : ℝ) ≤ Real.log (N : ℝ) := Real.log_nonneg (by exact_mod_cast NeZero.one_le)
          have ha2 : (0 : ℝ) ≤ Real.log (2 + ‖s‖) :=
            Real.log_nonneg (by have h := norm_nonneg s; linarith only [h])
          linarith only [ha1, ha2]
        exact mul_le_mul hCqle h8 h10 (by linarith only [hCnpos.le])
      rw [hCjdef]
      linarith only [h9, hCzpos.le]
    linarith only [h1, h7]
  have hCcOf : ∀ {N : ℕ} [NeZero N] (hNq : N ∣ q) (φ : DirichletCharacter ℂ N) (t : ℝ),
      |SigmaP3L q L (DirichletCharacter.changeLevel hNq φ) (sPt a L t) a (Work.LinnikContract.lamOf q ρ₁)
        - SigmaP3L N L φ (sPt a L t) a (Work.LinnikContract.lamOf q ρ₁)| ≤ Corr := by
    intro N _ hNq φ t
    have h := hCc (hNq := hNq) (ψ := φ) (L := L) hL1 (by
      have h2 : (sPt a L t).re = 1 + a / L := by simp [sPt]
      rw [h2]
      have : 0 < a / L := div_pos ha hLpos
      linarith only [this]) (a := a) (lam₁ := Work.LinnikContract.lamOf q ρ₁) ha hlam₁nn
    rw [hCorrdef, hSp1def, hSp2def, hSp3def]
    rw [← hSp1def, ← hSp2def, ← hSp3def] at h
    exact h
  have h31' : ∀ {N : ℕ} [NeZero N], 3 ≤ N → ∀ (χ : DirichletCharacter ℂ N), χ ≠ 1 →
      χ.IsPrimitive →
      ∀ {L : ℝ}, L₀ ≤ L → Real.log (N : ℝ) ≤ L → ∀ s : ℂ,
        1 + 1 / (L * Real.log L) ≤ s.re → s.re ≤ 1 + Real.log L / L → |s.im| ≤ 10 * L →
        (-logDeriv (DirichletCharacter.LFunction χ) s).re
          + (∑ᶠ u : ℂ, ((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
                (Metric.closedBall 0 (|s.im| + 2))) u : ℤ) *
              (if ‖(1 : ℂ) + (s.im : ℂ) * Complex.I - u‖ ≤ δ₀ then ((1 / (s - u)).re) else 0))
          ≤ (1 / 6 + ε₁) * L := by
    intro M _ hM χ hχ hprim L hL0 hlogN s hs1 hs2 hs3
    simpa only [show ((1 : ℝ) / 3 / 2) = 1 / 6 by norm_num] using
      h31 hM χ hχ hprim hL0 hlogN s hs1 hs2 hs3
  have hk1Of : ∀ {N : ℕ} [NeZero N] (φ : DirichletCharacter ℂ N), φ ≠ 1 → φ.IsPrimitive →
      3 ≤ N → Real.log (N : ℝ) ≤ L → ∀ t : ℝ, |t| ≤ 4 →
      (-logDeriv (DirichletCharacter.LFunction φ) (sPt a L t)).re
        + P9.nearInvSum N φ (sPt a L t) δ ≤ (1 / 6 + ε₁) * L := by
    intro N _ φ hφ hprim hN3 hlogN t ht
    refine k1_input (L₀ := L₀) (δ₀ := δ₀) (δ := δ) (ε₁ := ε₁) (a := a) (L := L) ?_
      (N := N) φ hφ hprim hN3 hL₀L hlogN hδleδ₀ (le_of_lt hδ₀lt1) hδpos (le_of_lt hδlt1)
      ha hL1 h1aL hlogLa (s := sPt a L t) (by simp [sPt])
      (by simpa [sPt] using le_trans ht (by norm_num : (4 : ℝ) ≤ 10))
    exact h31'
  have hSp1le : Sp1 ≤ Cp * (Real.log L) ^ 2 := by
    have h := hCp1 q hqq
    rw [hSp1def]
    have h' : (Real.log (Real.log (q : ℝ))) ^ (1 + 1) = (Real.log L) ^ 2 := by rw [hLdef]
    rw [h'] at h
    simp only [pow_one] at h
    exact le_trans h (mul_le_mul_of_nonneg_right hCp1le (by positivity))
  have hSp2le : Sp2 ≤ Cp * (Real.log L) ^ 3 := by
    have h := hCp2 q hqq
    rw [hSp2def]
    have h' : (Real.log (Real.log (q : ℝ))) ^ (2 + 1) = (Real.log L) ^ 3 := by rw [hLdef]
    rw [h'] at h
    exact le_trans h (mul_le_mul_of_nonneg_right hCp2le (by positivity))
  have hSp3le : Sp3 ≤ Cp * (Real.log L) ^ 4 := by
    have h := hCp3 q hqq
    rw [hSp3def]
    have h' : (Real.log (Real.log (q : ℝ))) ^ (3 + 1) = (Real.log L) ^ 4 := by rw [hLdef]
    rw [h'] at h
    exact le_trans h (mul_le_mul_of_nonneg_right hCp3le (by positivity))
  have hSpnn1 : 0 ≤ Sp1 := by rw [hSp1def]; positivity
  have hSpnn2 : 0 ≤ Sp2 := by rw [hSp2def]; positivity
  have hSpnn3 : 0 ≤ Sp3 := by rw [hSp3def]; positivity
  have hN3 : 3 ≤ χ₁.conductor := Work.LinnikAreas2.three_le_conductor χ₁ hχ₁ne
  haveI hNc : NeZero χ₁.conductor := ⟨χ₁.conductor_ne_zero⟩
  set Δ : ℝ := (ρ₁.im - ρ₀.im) * L with hΔdef
  set β : ℝ := (ρ₁.im + ρ₀.im) * L with hβdef
  set γ : ℝ := 2 * ρ₁.im * L with hγdef
  -- ## E-term comparisons
  set E2 : ℝ := ((a + (Work.LinnikContract.lamOf q ρ₁)) ^ 2 / L ^ 2) * ((1 + 4 / δ ^ 2) * Cj + Ct) with hE2def
  set E3 : ℝ := (2 / 3) * ((a + (Work.LinnikContract.lamOf q ρ₁)) ^ 3 / L ^ 3) * ((2 / δ) * (1 + 4 / δ ^ 2) * Cj + Ct) with hE3def
  set E2z : ℝ := ((a + (Work.LinnikContract.lamOf q ρ₁)) ^ 2 / L ^ 2) * ((1 + 4 / δ ^ 2) * Cz + Ct) with hE2zdef
  set E3z : ℝ := (2 / 3) * ((a + (Work.LinnikContract.lamOf q ρ₁)) ^ 3 / L ^ 3) * ((2 / δ) * (1 + 4 / δ ^ 2) * Cz + Ct) with hE3zdef
  set E2c : ℝ := (aup ^ 2 / L ^ 2) * ((1 + 4 / δ ^ 2) * Cj + Ct) with hE2cdef
  set E3c : ℝ := (2 / 3) * (aup ^ 3 / L ^ 3) * ((2 / δ) * (1 + 4 / δ ^ 2) * Cj + Ct) with hE3cdef
  set Corrc : ℝ := (Cc / L) * (aup * Cp * (Real.log L) ^ 2 + (aup ^ 2 / L) * Cp * (Real.log L) ^ 3
      + (aup ^ 3 / L ^ 2) * Cp * (Real.log L) ^ 4) with hCorrcdef
  set C0c : ℝ := (aup / L) * C₀ with hC0cdef
  set Fc : ℝ := 64 * aup / (δ * L) with hFcdef
  set E : ℝ := C0c + E2c + E3c + Corrc + Fc with hEdef
  have hcE2 : E2 ≤ E2c := by
    rw [hE2def, hE2cdef]
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    exact div_le_div_of_nonneg_right hαaup2 (by positivity)
  have hcE3 : E3 ≤ E3c := by
    rw [hE3def, hE3cdef]
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    exact mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hαaup3 (by positivity))
      (by norm_num : (0 : ℝ) ≤ 2 / 3)
  have hCzCj : Cz ≤ Cj := by
    rw [hCjdef]
    have h1 : 0 ≤ Cn * (L + 6) := by positivity
    linarith only [h1]
  have hcE2z : E2z ≤ E2c := by
    rw [hE2zdef, hE2cdef]
    calc ((a + (Work.LinnikContract.lamOf q ρ₁)) ^ 2 / L ^ 2) * ((1 + 4 / δ ^ 2) * Cz + Ct)
        ≤ (aup ^ 2 / L ^ 2) * ((1 + 4 / δ ^ 2) * Cz + Ct) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          exact div_le_div_of_nonneg_right hαaup2 (by positivity)
      _ ≤ (aup ^ 2 / L ^ 2) * ((1 + 4 / δ ^ 2) * Cj + Ct) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          have h1 : 0 ≤ (1 + 4 / δ ^ 2 : ℝ) := by positivity
          have h2 := mul_le_mul_of_nonneg_left hCzCj h1
          linarith only [h2]
  have hcE3z : E3z ≤ E3c := by
    rw [hE3zdef, hE3cdef]
    calc (2 / 3) * ((a + (Work.LinnikContract.lamOf q ρ₁)) ^ 3 / L ^ 3)
          * ((2 / δ) * (1 + 4 / δ ^ 2) * Cz + Ct)
        ≤ (2 / 3) * (aup ^ 3 / L ^ 3) * ((2 / δ) * (1 + 4 / δ ^ 2) * Cz + Ct) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          exact mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hαaup3 (by positivity))
            (by norm_num : (0 : ℝ) ≤ 2 / 3)
      _ ≤ (2 / 3) * (aup ^ 3 / L ^ 3) * ((2 / δ) * (1 + 4 / δ ^ 2) * Cj + Ct) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          have h1 : 0 ≤ (2 / δ) * (1 + 4 / δ ^ 2 : ℝ) := by positivity
          have h2 := mul_le_mul_of_nonneg_left hCzCj h1
          linarith only [h2]
  have hcFar : ∀ k : ℕ, k ≤ 4 → (k : ℝ) * (8 * (a + (Work.LinnikContract.lamOf q ρ₁)) / (δ * L)) ≤ Fc := by
    intro k hk
    have h1 : (k : ℝ) ≤ 4 := by exact_mod_cast hk
    rw [hFcdef]
    have h2 : (k : ℝ) * (8 * (a + (Work.LinnikContract.lamOf q ρ₁)) / (δ * L)) ≤ 4 * (8 * aup / (δ * L)) := by
      have h3 : (k : ℝ) * (8 * (a + (Work.LinnikContract.lamOf q ρ₁)) / (δ * L)) ≤ (k : ℝ) * (8 * aup / (δ * L)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply div_le_div_of_nonneg_right _ (by positivity)
        linarith only [hαaup]
      have h4 : (k : ℝ) * (8 * aup / (δ * L)) ≤ 4 * (8 * aup / (δ * L)) :=
        mul_le_mul_of_nonneg_right h1 (by positivity)
      linarith only [h3, h4]
    have h5 : (4 : ℝ) * (8 * aup / (δ * L)) = 32 * aup / (δ * L) := by ring_nf
    have h6 : (32 : ℝ) * aup / (δ * L) ≤ 64 * aup / (δ * L) := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      linarith only [hauppos.le]
    linarith only [h2, h5.le, h5.ge, h6]
  have hcC0 : ((a + (Work.LinnikContract.lamOf q ρ₁)) / L) * C₀ ≤ C0c := by
    rw [hC0cdef]
    exact mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hαaup hLpos.le) hC₀pos.le
  have hcCorr : Corr ≤ Corrc := by
    rw [hCorrdef, hCorrcdef]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    have e1 : (a + (Work.LinnikContract.lamOf q ρ₁)) * Sp1 ≤ aup * (Cp * (Real.log L) ^ 2) :=
      le_trans (mul_le_mul_of_nonneg_right hαaup hSpnn1)
        (mul_le_mul_of_nonneg_left hSp1le hauppos.le)
    have e2 : ((a + (Work.LinnikContract.lamOf q ρ₁)) ^ 2 / L) * Sp2 ≤ (aup ^ 2 / L) * (Cp * (Real.log L) ^ 3) := by
      refine le_trans (mul_le_mul_of_nonneg_right
        (div_le_div_of_nonneg_right hαaup2 hLpos.le) hSpnn2) ?_
      exact mul_le_mul_of_nonneg_left hSp2le (by positivity)
    have e3 : ((a + (Work.LinnikContract.lamOf q ρ₁)) ^ 3 / L ^ 2) * Sp3 ≤ (aup ^ 3 / L ^ 2) * (Cp * (Real.log L) ^ 4) := by
      refine le_trans (mul_le_mul_of_nonneg_right
        (div_le_div_of_nonneg_right hαaup3 (by positivity)) hSpnn3) ?_
      exact mul_le_mul_of_nonneg_left hSp3le (by positivity)
    have e4 : (a + (Work.LinnikContract.lamOf q ρ₁)) * Sp1 + ((a + (Work.LinnikContract.lamOf q ρ₁)) ^ 2 / L) * Sp2 + ((a + (Work.LinnikContract.lamOf q ρ₁)) ^ 3 / L ^ 2) * Sp3
        ≤ aup * (Cp * (Real.log L) ^ 2) + (aup ^ 2 / L) * (Cp * (Real.log L) ^ 3)
          + (aup ^ 3 / L ^ 2) * (Cp * (Real.log L) ^ 4) := by linarith only [e1, e2, e3]
    have e5 : aup * (Cp * (Real.log L) ^ 2) + (aup ^ 2 / L) * (Cp * (Real.log L) ^ 3)
        + (aup ^ 3 / L ^ 2) * (Cp * (Real.log L) ^ 4)
        = aup * Cp * (Real.log L) ^ 2 + (aup ^ 2 / L) * Cp * (Real.log L) ^ 3
          + (aup ^ 3 / L ^ 2) * Cp * (Real.log L) ^ 4 := by ring
    linarith only [e4, e5.le, e5.ge]
  have heE : ∀ e : ℝ, e ≤ E2 + E3 + Fc + Corr + C0c → e ≤ E :=
    fun e he => le_E_of_le hEdef hcE2 hcE3 hcCorr he
  have heEz : ∀ e : ℝ, e ≤ E2z + E3z + Fc + Corr + C0c → e ≤ E :=
    fun e he => le_E_of_le_zeta hEdef hcE2z hcE3z hcCorr he
  -- ## the zeta-parity-input, common to all cases
  have hlogNOf : ∀ {N : ℕ} (hNq : N ∣ q), N ≠ 0 → Real.log (N : ℝ) ≤ L := by
    intro N hNq hN0
    rw [hLdef]
    refine Real.log_le_log (by exact_mod_cast Nat.pos_of_ne_zero hN0) ?_
    exact_mod_cast Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne q)) hNq
  -- ## summation of the errors
  -- ## the case distinction
  by_cases hC : χ₁ ^ 2 = 1
  · exact absurd hC hsq
  · by_cases hB : χ₁ ^ 3 = 1
    · -- ### case B (χ₁³ = 1, χ₁² ≠ 1)
      have hχ2 : χ₁ ^ 2 ≠ 1 := hC
      haveI hN1 : NeZero χ₁.conductor := ⟨χ₁.conductor_ne_zero⟩
      have hφ₁ne : χ₁.primitiveCharacter ≠ 1 := by
        intro hh
        exact hχ₁ne (by rw [← DirichletCharacter.changeLevel_primitiveCharacter χ₁, hh,
          DirichletCharacter.changeLevel_one χ₁.conductor_dvd_level])
      have hφ₁prim : χ₁.primitiveCharacter.IsPrimitive :=
        DirichletCharacter.primitiveCharacter_isPrimitive χ₁
      have hlogN1 : Real.log ((χ₁.conductor : ℕ) : ℝ) ≤ L :=
        hlogNOf χ₁.conductor_dvd_level χ₁.conductor_ne_zero
      have hzm1 : ∀ u : ℂ, Work.LinnikContract.zeroMult χ₁ u
          = Work.LinnikContract.zeroMult χ₁.primitiveCharacter u := by
        intro u
        have h := Work.ZeroFreeTables.Table4.zeroMult_changeLevel χ₁.conductor_dvd_level
          χ₁.primitiveCharacter u
        rw [DirichletCharacter.changeLevel_primitiveCharacter] at h
        exact h
      obtain ⟨par₁, hpar₁2, hpar₁0, hpar₁1⟩ := exists_par χ₁.primitiveCharacter
      have hminP1 := hminPrim χ₁.conductor_dvd_level χ₁.primitiveCharacter hφ₁ne hφ₁prim
      have hk1P1 : ∀ t : ℝ, |t| ≤ 4 → (-logDeriv (DirichletCharacter.LFunction χ₁.primitiveCharacter)
          (sPt a L t)).re + P9.nearInvSum χ₁.conductor χ₁.primitiveCharacter (sPt a L t) δ
          ≤ (1 / 6 + ε₁) * L := fun t ht =>
        hk1Of χ₁.primitiveCharacter hφ₁ne hφ₁prim hN3 hlogN1 t ht
      have hJ1 : ∀ s : ℂ, ‖s‖ ≤ 5 → P9.invSqSum χ₁.conductor χ₁.primitiveCharacter s ≤ Cj :=
        fun s hs => hJOf χ₁.conductor_dvd_level χ₁.primitiveCharacter hφ₁ne hφ₁prim s hs
      have hCc1 : ∀ t : ℝ, |SigmaP3L q L (DirichletCharacter.changeLevel χ₁.conductor_dvd_level
            χ₁.primitiveCharacter) (sPt a L t) a (Work.LinnikContract.lamOf q ρ₁)
          - SigmaP3L χ₁.conductor L χ₁.primitiveCharacter (sPt a L t) a (Work.LinnikContract.lamOf q ρ₁)| ≤ Corr :=
        fun t => hCcOf χ₁.conductor_dvd_level χ₁.primitiveCharacter t
      have hρ₁re : ρ₁.re = 1 - (Work.LinnikContract.lamOf q ρ₁) / L := by
        rw [hlamOf_eq ρ₁]; field_simp; ring
      have hρ₀re : ρ₀.re = 1 - (Work.LinnikContract.lamOf q ρ₀) / L := by
        rw [hlamOf_eq ρ₀]; field_simp; ring
      have hm3₀ : |ρ₀.im| ≤ 4 := by linarith only [him0]
      have hm3₁ : |ρ₁.im| ≤ 4 := by linarith only [hZ1.2.2]
      have hm3a : |ρ₁.im - ρ₀.im| ≤ 4 := by
        have h1 := abs_le.mp hZ1.2.2; have h0 := abs_le.mp him0
        rw [abs_le]; constructor <;> linarith only [h1.1, h1.2, h0.1, h0.2]
      have hm3f : |-(ρ₁.im + ρ₀.im)| ≤ 4 := by
        have h1 := abs_le.mp hZ1.2.2; have h0 := abs_le.mp him0
        rw [abs_le]; constructor <;> linarith only [h1.1, h1.2, h0.1, h0.2]
      have hm3d : |2 * ρ₁.im - ρ₀.im| ≤ 4 := by
        have h1 := abs_le.mp hZ1.2.2; have h0 := abs_le.mp him0
        rw [abs_le]; constructor <;> linarith only [h1.1, h1.2, h0.1, h0.2]
      have hm3g : |-(2 * ρ₁.im)| ≤ 4 := by
        have h1 := abs_le.mp hZ1.2.2
        rw [abs_le]; constructor <;> linarith only [h1.1, h1.2]
      have hm3e : |2 * ρ₁.im + ρ₀.im| ≤ 4 := by
        have h1 := abs_le.mp hZ1.2.2; have h0 := abs_le.mp him0
        rw [abs_le]; constructor <;> linarith only [h1.1, h1.2, h0.1, h0.2]
      -- ### error budgets
      set e1 : ℝ := ((a + (Work.LinnikContract.lamOf q ρ₁)) / L) * C₀ + E2z + E3z + Corr with he1def
      set e2 : ℝ := E2 + E3 + 2 * (8 * (a + (Work.LinnikContract.lamOf q ρ₁)) / (δ * L)) + Corr with he2def
      set e3 : ℝ := ((a + (Work.LinnikContract.lamOf q ρ₁)) / L) * C₀ + E2z + E3z + Corr with he3def
      set e4 : ℝ := E2 + E3 + 2 * (8 * (a + (Work.LinnikContract.lamOf q ρ₁)) / (δ * L)) + Corr with he4def
      set e5 : ℝ := E2 + E3 + 8 * (a + (Work.LinnikContract.lamOf q ρ₁)) / (δ * L) + Corr with he5def
      set e6 : ℝ := E2 + E3 + 8 * (a + (Work.LinnikContract.lamOf q ρ₁)) / (δ * L) + Corr with he6def
      set e7 : ℝ := E2 + E3 + 8 * (a + (Work.LinnikContract.lamOf q ρ₁)) / (δ * L) + Corr with he7def
      set e8 : ℝ := ((a + (Work.LinnikContract.lamOf q ρ₁)) / L) * C₀ + E2z + E3z + Corr with he8def
      -- ### the eight points
      set S1 : ℝ := SigmaP3L q L (1 : DirichletCharacter ℂ q) (sPt a L 0) a (Work.LinnikContract.lamOf q ρ₁) with hS1'
      set S2 : ℝ := SigmaP3L q L χ₁ (sPt a L ρ₀.im) a (Work.LinnikContract.lamOf q ρ₁) with hS2'
      set S3 : ℝ := SigmaP3L q L (1 : DirichletCharacter ℂ q) (sPt a L (ρ₁.im - ρ₀.im)) a (Work.LinnikContract.lamOf q ρ₁) with hS3'
      set S4 : ℝ := SigmaP3L q L χ₁ (sPt a L ρ₁.im) a (Work.LinnikContract.lamOf q ρ₁) with hS4'
      set S5 : ℝ := SigmaP3L q L (χ₁ ^ 2) (sPt a L (ρ₁.im + ρ₀.im)) a (Work.LinnikContract.lamOf q ρ₁) with hS5'
      set S6 : ℝ := SigmaP3L q L χ₁ (sPt a L (2 * ρ₁.im - ρ₀.im)) a (Work.LinnikContract.lamOf q ρ₁) with hS6'
      set S7 : ℝ := SigmaP3L q L (χ₁ ^ 2) (sPt a L (2 * ρ₁.im)) a (Work.LinnikContract.lamOf q ρ₁) with hS7'
      set S8 : ℝ := SigmaP3L q L (1 : DirichletCharacter ℂ q) (sPt a L (2 * ρ₁.im + ρ₀.im)) a (Work.LinnikContract.lamOf q ρ₁) with hS8'
      -- ### point 1
      have hS1 : S1 ≤ P3R ((a + (Work.LinnikContract.lamOf q ρ₁)) / a) + e1 := by
        have hcc0 := hCcOf (N := 1) (one_dvd q) (1 : DirichletCharacter ℂ 1) 0
        rw [DirichletCharacter.changeLevel_one (one_dvd q)] at hcc0
        have hb := point_bound_principal (q := q) (a := a) (lam₁ := (Work.LinnikContract.lamOf q ρ₁)) (δ := δ) (L := L)
          (Ct := Ct) (Cz := Cz) (C₀ := C₀) (Cc := Corr) ha hlam₁nn hδpos hδlt1 hLt haδL haL
          hCzZeta hC0b' hnzδ (s := sPt a L 0) (by simp [sPt]) (by simp [sPt])
          (hSzeta 0).1 (hSzeta 0).2 hcc0
        have hpole : (P3 (((a : ℂ) + ((Work.LinnikContract.lamOf q ρ₁) : ℂ)) / ((sPt a L 0 - 1) * (L : ℂ)))).re
            = P3R ((a + (Work.LinnikContract.lamOf q ρ₁)) / a) := by
          rw [P3_arg_eq_pole_split (a := a) (L := L) (t := 0) (lam := (Work.LinnikContract.lamOf q ρ₁)) hLne]
          rw [zero_mul, PhiG_zero]
        rw [hpole] at hb
        linarith only [hb, hS1', he1def, hE2zdef, hE3zdef]
      -- ### point 2 (χ₁ at σ+iγ₀, kept {ρ₀,ρ₁})
      have hS2 : S2 ≤ -P3R ((a + (Work.LinnikContract.lamOf q ρ₁)) / (a + (Work.LinnikContract.lamOf q ρ₀))) - P9.PhiG (a + (Work.LinnikContract.lamOf q ρ₁)) (a + (Work.LinnikContract.lamOf q ρ₁)) Δ
          + (a + (Work.LinnikContract.lamOf q ρ₁)) * (1 / 6 + ε₁) + e2 := by
        have hz₁ : Work.LinnikContract.zeroMult χ₁.primitiveCharacter ρ₁ ≠ 0 := by
          rw [← hzm1 ρ₁]; exact hZ1.2.1
        have hz₀ : Work.LinnikContract.zeroMult χ₁.primitiveCharacter ρ₀ ≠ 0 := by
          rw [← hzm1 ρ₀]; exact hzm0
        have hT : ∀ u ∈ ({ρ₀, ρ₁} : Finset ℂ),
            Work.LinnikContract.zeroMult χ₁.primitiveCharacter u ≠ 0 := by
          intro u hu
          rcases Finset.mem_insert.mp hu with h | h
          · rw [h]; exact hz₀
          · rw [Finset.mem_singleton.mp h]; exact hz₁
        have hTim : ∀ u ∈ ({ρ₀, ρ₁} : Finset ℂ), |u.im| ≤ 10 := by
          intro u hu
          rcases Finset.mem_insert.mp hu with h | h
          · rw [h]; linarith only [him0]
          · rw [Finset.mem_singleton.mp h]; linarith only [hZ1.2.2]
        have hb := point_bound_q (q := q) (N := χ₁.conductor) (hNq := χ₁.conductor_dvd_level)
          (φ := χ₁.primitiveCharacter) hφ₁ne hφ₁prim ha hlam₁nn hδpos hδlt1 hLt haδL
          (s := sPt a L ρ₀.im) (by simp [sPt]) (by simpa [sPt] using hm3₀)
          (hk1P1 ρ₀.im hm3₀) par₁ hpar₁0 hpar₁1
          (hSpr par₁ hpar₁2 ρ₀.im).1 (hSpr par₁ hpar₁2 ρ₀.im).2
          (hJ1 (sPt a L ρ₀.im) (norm_sPt_le_five ha haL hLpos hm3₀))
          hminP1 ({ρ₀, ρ₁} : Finset ℂ) hT hTim (hCc1 ρ₀.im)
        have t1 : (P3 (((a : ℂ) + ((Work.LinnikContract.lamOf q ρ₁) : ℂ)) / ((sPt a L ρ₀.im - ρ₀) * (L : ℂ)))).re
            = P3R ((a + (Work.LinnikContract.lamOf q ρ₁)) / (a + (Work.LinnikContract.lamOf q ρ₀))) := by
          rw [P3_arg_eq_split (a := a) (L := L) (lam₁ := (Work.LinnikContract.lamOf q ρ₁)) (lam := (Work.LinnikContract.lamOf q ρ₀)) (gam := ρ₀.im)
            (t := ρ₀.im) (ρ := ρ₀) hLne hρ₀re rfl]
          rw [sub_self, zero_mul, PhiG_zero]
        have t2 : (P3 (((a : ℂ) + ((Work.LinnikContract.lamOf q ρ₁) : ℂ)) / ((sPt a L ρ₀.im - ρ₁) * (L : ℂ)))).re
            = P9.PhiG (a + (Work.LinnikContract.lamOf q ρ₁)) (a + (Work.LinnikContract.lamOf q ρ₁)) Δ := by
          rw [P3_arg_eq_split (a := a) (L := L) (lam₁ := (Work.LinnikContract.lamOf q ρ₁)) (lam := (Work.LinnikContract.lamOf q ρ₁)) (gam := ρ₁.im)
            (t := ρ₀.im) (ρ := ρ₁) hLne hρ₁re rfl]
          rw [show (ρ₀.im - ρ₁.im) * L = -Δ by rw [hΔdef]; ring]
          rw [PhiG_neg']
        have hsum : (∑ u ∈ ({ρ₀, ρ₁} : Finset ℂ),
            (P3 (((a : ℂ) + ((Work.LinnikContract.lamOf q ρ₁) : ℂ)) / ((sPt a L ρ₀.im - u) * (L : ℂ)))).re)
            = P3R ((a + (Work.LinnikContract.lamOf q ρ₁)) / (a + (Work.LinnikContract.lamOf q ρ₀))) + P9.PhiG (a + (Work.LinnikContract.lamOf q ρ₁)) (a + (Work.LinnikContract.lamOf q ρ₁)) Δ := by
          rw [Finset.sum_pair (Ne.symm hne), t1, t2]
        rw [DirichletCharacter.changeLevel_primitiveCharacter] at hb
        rw [Finset.card_pair (Ne.symm hne), Nat.cast_ofNat, hsum] at hb
        rw [neg_add] at hb
        linarith only [hb, hS2', he2def, hE2def, hE3def]
      -- ### point 3
      have hS3 : S3 ≤ P9.PhiG (a + (Work.LinnikContract.lamOf q ρ₁)) a Δ + e3 := by
        have hcc3 := hCcOf (N := 1) (one_dvd q) (1 : DirichletCharacter ℂ 1) (ρ₁.im - ρ₀.im)
        rw [DirichletCharacter.changeLevel_one (one_dvd q)] at hcc3
        have hb := point_bound_principal (q := q) (a := a) (lam₁ := (Work.LinnikContract.lamOf q ρ₁)) (δ := δ) (L := L)
          (Ct := Ct) (Cz := Cz) (C₀ := C₀) (Cc := Corr) ha hlam₁nn hδpos hδlt1 hLt haδL haL
          hCzZeta hC0b' hnzδ (s := sPt a L (ρ₁.im - ρ₀.im))
          (by simp [sPt]) (by simpa [sPt] using hm3a)
          (hSzeta (ρ₁.im - ρ₀.im)).1 (hSzeta (ρ₁.im - ρ₀.im)).2 hcc3
        have hpole : (P3 (((a : ℂ) + ((Work.LinnikContract.lamOf q ρ₁) : ℂ)) / ((sPt a L (ρ₁.im - ρ₀.im) - 1) * (L : ℂ)))).re
            = P9.PhiG (a + (Work.LinnikContract.lamOf q ρ₁)) a Δ :=
          P3_arg_eq_pole_split (a := a) (L := L) (t := ρ₁.im - ρ₀.im) (lam := (Work.LinnikContract.lamOf q ρ₁)) hLne
        rw [hpole] at hb
        linarith only [hb, hS3', he3def, hE2zdef, hE3zdef]
      -- ### point 4 (χ₁ at σ+iγ₁, kept {ρ₀,ρ₁})
      have hS4 : S4 ≤ -P3R 1 - P9.PhiG (a + (Work.LinnikContract.lamOf q ρ₁)) (a + (Work.LinnikContract.lamOf q ρ₀)) Δ
          + (a + (Work.LinnikContract.lamOf q ρ₁)) * (1 / 6 + ε₁) + e4 := by
        have hz₁ : Work.LinnikContract.zeroMult χ₁.primitiveCharacter ρ₁ ≠ 0 := by
          rw [← hzm1 ρ₁]; exact hZ1.2.1
        have hz₀ : Work.LinnikContract.zeroMult χ₁.primitiveCharacter ρ₀ ≠ 0 := by
          rw [← hzm1 ρ₀]; exact hzm0
        have hT : ∀ u ∈ ({ρ₀, ρ₁} : Finset ℂ),
            Work.LinnikContract.zeroMult χ₁.primitiveCharacter u ≠ 0 := by
          intro u hu
          rcases Finset.mem_insert.mp hu with h | h
          · rw [h]; exact hz₀
          · rw [Finset.mem_singleton.mp h]; exact hz₁
        have hTim : ∀ u ∈ ({ρ₀, ρ₁} : Finset ℂ), |u.im| ≤ 10 := by
          intro u hu
          rcases Finset.mem_insert.mp hu with h | h
          · rw [h]; linarith only [him0]
          · rw [Finset.mem_singleton.mp h]; linarith only [hZ1.2.2]
        have hb := point_bound_q (q := q) (N := χ₁.conductor) (hNq := χ₁.conductor_dvd_level)
          (φ := χ₁.primitiveCharacter) hφ₁ne hφ₁prim ha hlam₁nn hδpos hδlt1 hLt haδL
          (s := sPt a L ρ₁.im) (by simp [sPt]) (by simpa [sPt] using hm3₁)
          (hk1P1 ρ₁.im hm3₁) par₁ hpar₁0 hpar₁1
          (hSpr par₁ hpar₁2 ρ₁.im).1 (hSpr par₁ hpar₁2 ρ₁.im).2
          (hJ1 (sPt a L ρ₁.im) (norm_sPt_le_five ha haL hLpos hm3₁))
          hminP1 ({ρ₀, ρ₁} : Finset ℂ) hT hTim (hCc1 ρ₁.im)
        have t1 : (P3 (((a : ℂ) + ((Work.LinnikContract.lamOf q ρ₁) : ℂ)) / ((sPt a L ρ₁.im - ρ₁) * (L : ℂ)))).re = P3R 1 := by
          rw [P3_arg_eq_split (a := a) (L := L) (lam₁ := (Work.LinnikContract.lamOf q ρ₁)) (lam := (Work.LinnikContract.lamOf q ρ₁)) (gam := ρ₁.im)
            (t := ρ₁.im) (ρ := ρ₁) hLne hρ₁re rfl]
          rw [sub_self, zero_mul, PhiG_zero]
          rw [show (a + (Work.LinnikContract.lamOf q ρ₁)) / (a + (Work.LinnikContract.lamOf q ρ₁)) = 1 by
            rw [div_self (ne_of_gt (lt_of_lt_of_le ha (le_add_of_nonneg_right hlam₁nn)))]]
        have t2 : (P3 (((a : ℂ) + ((Work.LinnikContract.lamOf q ρ₁) : ℂ)) / ((sPt a L ρ₁.im - ρ₀) * (L : ℂ)))).re
            = P9.PhiG (a + (Work.LinnikContract.lamOf q ρ₁)) (a + (Work.LinnikContract.lamOf q ρ₀)) Δ := by
          rw [P3_arg_eq_split (a := a) (L := L) (lam₁ := (Work.LinnikContract.lamOf q ρ₁)) (lam := (Work.LinnikContract.lamOf q ρ₀)) (gam := ρ₀.im)
            (t := ρ₁.im) (ρ := ρ₀) hLne hρ₀re rfl]
        have hsum : (∑ u ∈ ({ρ₀, ρ₁} : Finset ℂ),
            (P3 (((a : ℂ) + ((Work.LinnikContract.lamOf q ρ₁) : ℂ)) / ((sPt a L ρ₁.im - u) * (L : ℂ)))).re)
            = P3R 1 + P9.PhiG (a + (Work.LinnikContract.lamOf q ρ₁)) (a + (Work.LinnikContract.lamOf q ρ₀)) Δ := by
          rw [Finset.sum_pair (Ne.symm hne), t2, t1]
          ring
        rw [DirichletCharacter.changeLevel_primitiveCharacter] at hb
        rw [Finset.card_pair (Ne.symm hne), Nat.cast_ofNat, hsum] at hb
        rw [neg_add] at hb
        linarith only [hb, hS4', he4def, hE2def, hE3def]
      -- ### point 5 (χ₁² via conjugation, kept {ρ₁})
      have hconj5 : SigmaP3L q L (χ₁ ^ 2) (sPt a L (ρ₁.im + ρ₀.im)) a (Work.LinnikContract.lamOf q ρ₁)
          = SigmaP3L q L χ₁ (sPt a L (-(ρ₁.im + ρ₀.im))) a (Work.LinnikContract.lamOf q ρ₁) := by
        rw [P9.SigmaP3L_conj_eq (χ₁ ^ 2) L (sPt a L (ρ₁.im + ρ₀.im)) a (Work.LinnikContract.lamOf q ρ₁)]
        have hinv : (χ₁ ^ 2)⁻¹ = χ₁ := by
          refine inv_eq_of_mul_eq_one_right ?_
          rw [← pow_succ]
          exact hB
        rw [hinv]
        congr 1
        apply Complex.ext <;> simp [sPt, Complex.conj_re, Complex.conj_im]
      have hS5 : S5 ≤ -P9.PhiG (a + (Work.LinnikContract.lamOf q ρ₁)) (a + (Work.LinnikContract.lamOf q ρ₁)) ((2 * ρ₁.im + ρ₀.im) * L)
          + (a + (Work.LinnikContract.lamOf q ρ₁)) * (1 / 6 + ε₁) + e5 := by
        have hz₁ : Work.LinnikContract.zeroMult χ₁.primitiveCharacter ρ₁ ≠ 0 := by
          rw [← hzm1 ρ₁]; exact hZ1.2.1
        have hT : ∀ u ∈ ({ρ₁} : Finset ℂ),
            Work.LinnikContract.zeroMult χ₁.primitiveCharacter u ≠ 0 := by
          intro u hu; rw [Finset.mem_singleton.mp hu]; exact hz₁
        have hTim : ∀ u ∈ ({ρ₁} : Finset ℂ), |u.im| ≤ 10 := by
          intro u hu; rw [Finset.mem_singleton.mp hu]; linarith only [hZ1.2.2]
        have hb := point_bound_q (q := q) (N := χ₁.conductor) (hNq := χ₁.conductor_dvd_level)
          (φ := χ₁.primitiveCharacter) hφ₁ne hφ₁prim ha hlam₁nn hδpos hδlt1 hLt haδL
          (s := sPt a L (-(ρ₁.im + ρ₀.im))) (by simp [sPt]) (by simpa [sPt] using hm3f)
          (hk1P1 (-(ρ₁.im + ρ₀.im)) hm3f) par₁ hpar₁0 hpar₁1
          (hSpr par₁ hpar₁2 (-(ρ₁.im + ρ₀.im))).1 (hSpr par₁ hpar₁2 (-(ρ₁.im + ρ₀.im))).2
          (hJ1 (sPt a L (-(ρ₁.im + ρ₀.im))) (norm_sPt_le_five ha haL hLpos hm3f))
          hminP1 ({ρ₁} : Finset ℂ) hT hTim (hCc1 (-(ρ₁.im + ρ₀.im)))
        have t1 : (P3 (((a : ℂ) + ((Work.LinnikContract.lamOf q ρ₁) : ℂ)) / ((sPt a L (-(ρ₁.im + ρ₀.im)) - ρ₁) * (L : ℂ)))).re
            = P9.PhiG (a + (Work.LinnikContract.lamOf q ρ₁)) (a + (Work.LinnikContract.lamOf q ρ₁)) ((2 * ρ₁.im + ρ₀.im) * L) := by
          rw [P3_arg_eq_split (a := a) (L := L) (lam₁ := (Work.LinnikContract.lamOf q ρ₁)) (lam := (Work.LinnikContract.lamOf q ρ₁)) (gam := ρ₁.im)
            (t := -(ρ₁.im + ρ₀.im)) (ρ := ρ₁) hLne hρ₁re rfl]
          rw [show (-(ρ₁.im + ρ₀.im) - ρ₁.im) * L = -((2 * ρ₁.im + ρ₀.im) * L) by ring]
          rw [PhiG_neg']
        have hsum : (∑ u ∈ ({ρ₁} : Finset ℂ),
            (P3 (((a : ℂ) + ((Work.LinnikContract.lamOf q ρ₁) : ℂ)) / ((sPt a L (-(ρ₁.im + ρ₀.im)) - u) * (L : ℂ)))).re)
            = P9.PhiG (a + (Work.LinnikContract.lamOf q ρ₁)) (a + (Work.LinnikContract.lamOf q ρ₁)) ((2 * ρ₁.im + ρ₀.im) * L) := by
          rw [Finset.sum_singleton, t1]
        rw [DirichletCharacter.changeLevel_primitiveCharacter] at hb
        rw [Finset.card_singleton, Nat.cast_one, one_mul, hsum] at hb
        rw [← hconj5] at hb
        linarith only [hb, hS5', he5def, hE2def, hE3def]
      -- ### point 6 (χ₁ at σ+i(2γ₁-γ₀), kept {ρ₁})
      have hS6 : S6 ≤ -P9.PhiG (a + (Work.LinnikContract.lamOf q ρ₁)) (a + (Work.LinnikContract.lamOf q ρ₁)) Δ
          + (a + (Work.LinnikContract.lamOf q ρ₁)) * (1 / 6 + ε₁) + e6 := by
        have hz₁ : Work.LinnikContract.zeroMult χ₁.primitiveCharacter ρ₁ ≠ 0 := by
          rw [← hzm1 ρ₁]; exact hZ1.2.1
        have hT : ∀ u ∈ ({ρ₁} : Finset ℂ),
            Work.LinnikContract.zeroMult χ₁.primitiveCharacter u ≠ 0 := by
          intro u hu; rw [Finset.mem_singleton.mp hu]; exact hz₁
        have hTim : ∀ u ∈ ({ρ₁} : Finset ℂ), |u.im| ≤ 10 := by
          intro u hu; rw [Finset.mem_singleton.mp hu]; linarith only [hZ1.2.2]
        have hb := point_bound_q (q := q) (N := χ₁.conductor) (hNq := χ₁.conductor_dvd_level)
          (φ := χ₁.primitiveCharacter) hφ₁ne hφ₁prim ha hlam₁nn hδpos hδlt1 hLt haδL
          (s := sPt a L (2 * ρ₁.im - ρ₀.im)) (by simp [sPt]) (by simpa [sPt] using hm3d)
          (hk1P1 (2 * ρ₁.im - ρ₀.im) hm3d) par₁ hpar₁0 hpar₁1
          (hSpr par₁ hpar₁2 (2 * ρ₁.im - ρ₀.im)).1 (hSpr par₁ hpar₁2 (2 * ρ₁.im - ρ₀.im)).2
          (hJ1 (sPt a L (2 * ρ₁.im - ρ₀.im)) (norm_sPt_le_five ha haL hLpos hm3d))
          hminP1 ({ρ₁} : Finset ℂ) hT hTim (hCc1 (2 * ρ₁.im - ρ₀.im))
        have t1 : (P3 (((a : ℂ) + ((Work.LinnikContract.lamOf q ρ₁) : ℂ)) / ((sPt a L (2 * ρ₁.im - ρ₀.im) - ρ₁) * (L : ℂ)))).re
            = P9.PhiG (a + (Work.LinnikContract.lamOf q ρ₁)) (a + (Work.LinnikContract.lamOf q ρ₁)) Δ := by
          rw [P3_arg_eq_split (a := a) (L := L) (lam₁ := (Work.LinnikContract.lamOf q ρ₁)) (lam := (Work.LinnikContract.lamOf q ρ₁)) (gam := ρ₁.im)
            (t := 2 * ρ₁.im - ρ₀.im) (ρ := ρ₁) hLne hρ₁re rfl,
            show (2 * ρ₁.im - ρ₀.im - ρ₁.im) * L = Δ by rw [hΔdef]; ring]
        have hsum : (∑ u ∈ ({ρ₁} : Finset ℂ),
            (P3 (((a : ℂ) + ((Work.LinnikContract.lamOf q ρ₁) : ℂ)) / ((sPt a L (2 * ρ₁.im - ρ₀.im) - u) * (L : ℂ)))).re)
            = P9.PhiG (a + (Work.LinnikContract.lamOf q ρ₁)) (a + (Work.LinnikContract.lamOf q ρ₁)) Δ := by
          rw [Finset.sum_singleton, t1]
        rw [DirichletCharacter.changeLevel_primitiveCharacter] at hb
        rw [Finset.card_singleton, Nat.cast_one, one_mul, hsum] at hb
        linarith only [hb, hS6', he6def, hE2def, hE3def]
      -- ### point 7 (χ₁² via conjugation, kept {ρ₀})
      have hconj7 : SigmaP3L q L (χ₁ ^ 2) (sPt a L (2 * ρ₁.im)) a (Work.LinnikContract.lamOf q ρ₁)
          = SigmaP3L q L χ₁ (sPt a L (-(2 * ρ₁.im))) a (Work.LinnikContract.lamOf q ρ₁) := by
        rw [P9.SigmaP3L_conj_eq (χ₁ ^ 2) L (sPt a L (2 * ρ₁.im)) a (Work.LinnikContract.lamOf q ρ₁)]
        have hinv : (χ₁ ^ 2)⁻¹ = χ₁ := by
          refine inv_eq_of_mul_eq_one_right ?_
          rw [← pow_succ]
          exact hB
        rw [hinv]
        congr 1
        apply Complex.ext <;> simp [sPt, Complex.conj_re, Complex.conj_im]
      have hS7 : S7 ≤ -P9.PhiG (a + (Work.LinnikContract.lamOf q ρ₁)) (a + (Work.LinnikContract.lamOf q ρ₀)) ((2 * ρ₁.im + ρ₀.im) * L)
          + (a + (Work.LinnikContract.lamOf q ρ₁)) * (1 / 6 + ε₁) + e7 := by
        have hz₀ : Work.LinnikContract.zeroMult χ₁.primitiveCharacter ρ₀ ≠ 0 := by
          rw [← hzm1 ρ₀]; exact hzm0
        have hT : ∀ u ∈ ({ρ₀} : Finset ℂ),
            Work.LinnikContract.zeroMult χ₁.primitiveCharacter u ≠ 0 := by
          intro u hu; rw [Finset.mem_singleton.mp hu]; exact hz₀
        have hTim : ∀ u ∈ ({ρ₀} : Finset ℂ), |u.im| ≤ 10 := by
          intro u hu; rw [Finset.mem_singleton.mp hu]; linarith only [him0]
        have hb := point_bound_q (q := q) (N := χ₁.conductor) (hNq := χ₁.conductor_dvd_level)
          (φ := χ₁.primitiveCharacter) hφ₁ne hφ₁prim ha hlam₁nn hδpos hδlt1 hLt haδL
          (s := sPt a L (-(2 * ρ₁.im))) (by simp [sPt]) (by simpa [sPt] using hm3g)
          (hk1P1 (-(2 * ρ₁.im)) hm3g) par₁ hpar₁0 hpar₁1
          (hSpr par₁ hpar₁2 (-(2 * ρ₁.im))).1 (hSpr par₁ hpar₁2 (-(2 * ρ₁.im))).2
          (hJ1 (sPt a L (-(2 * ρ₁.im))) (norm_sPt_le_five ha haL hLpos hm3g))
          hminP1 ({ρ₀} : Finset ℂ) hT hTim (hCc1 (-(2 * ρ₁.im)))
        have t1 : (P3 (((a : ℂ) + ((Work.LinnikContract.lamOf q ρ₁) : ℂ)) / ((sPt a L (-(2 * ρ₁.im)) - ρ₀) * (L : ℂ)))).re
            = P9.PhiG (a + (Work.LinnikContract.lamOf q ρ₁)) (a + (Work.LinnikContract.lamOf q ρ₀)) ((2 * ρ₁.im + ρ₀.im) * L) := by
          rw [P3_arg_eq_split (a := a) (L := L) (lam₁ := (Work.LinnikContract.lamOf q ρ₁)) (lam := (Work.LinnikContract.lamOf q ρ₀)) (gam := ρ₀.im)
            (t := -(2 * ρ₁.im)) (ρ := ρ₀) hLne hρ₀re rfl]
          rw [show (-(2 * ρ₁.im) - ρ₀.im) * L = -((2 * ρ₁.im + ρ₀.im) * L) by ring]
          rw [PhiG_neg']
        have hsum : (∑ u ∈ ({ρ₀} : Finset ℂ),
            (P3 (((a : ℂ) + ((Work.LinnikContract.lamOf q ρ₁) : ℂ)) / ((sPt a L (-(2 * ρ₁.im)) - u) * (L : ℂ)))).re)
            = P9.PhiG (a + (Work.LinnikContract.lamOf q ρ₁)) (a + (Work.LinnikContract.lamOf q ρ₀)) ((2 * ρ₁.im + ρ₀.im) * L) := by
          rw [Finset.sum_singleton, t1]
        rw [DirichletCharacter.changeLevel_primitiveCharacter] at hb
        rw [Finset.card_singleton, Nat.cast_one, one_mul, hsum] at hb
        rw [← hconj7] at hb
        linarith only [hb, hS7', he7def, hE2def, hE3def]
      -- ### point 8 (χ₁³ = 1, principal at σ+i(2γ₁+γ₀))
      have hS8 : S8 ≤ P9.PhiG (a + (Work.LinnikContract.lamOf q ρ₁)) a ((2 * ρ₁.im + ρ₀.im) * L) + e8 := by
        have hcc8 := hCcOf (N := 1) (one_dvd q) (1 : DirichletCharacter ℂ 1) (2 * ρ₁.im + ρ₀.im)
        rw [DirichletCharacter.changeLevel_one (one_dvd q)] at hcc8
        have hb := point_bound_principal (q := q) (a := a) (lam₁ := (Work.LinnikContract.lamOf q ρ₁)) (δ := δ) (L := L)
          (Ct := Ct) (Cz := Cz) (C₀ := C₀) (Cc := Corr) ha hlam₁nn hδpos hδlt1 hLt haδL haL
          hCzZeta hC0b' hnzδ (s := sPt a L (2 * ρ₁.im + ρ₀.im))
          (by simp [sPt]) (by simpa [sPt] using hm3e)
          (hSzeta (2 * ρ₁.im + ρ₀.im)).1 (hSzeta (2 * ρ₁.im + ρ₀.im)).2 hcc8
        have hpole : (P3 (((a : ℂ) + ((Work.LinnikContract.lamOf q ρ₁) : ℂ)) / ((sPt a L (2 * ρ₁.im + ρ₀.im) - 1) * (L : ℂ)))).re
            = P9.PhiG (a + (Work.LinnikContract.lamOf q ρ₁)) a ((2 * ρ₁.im + ρ₀.im) * L) :=
          P3_arg_eq_pole_split (a := a) (L := L) (t := 2 * ρ₁.im + ρ₀.im) (lam := (Work.LinnikContract.lamOf q ρ₁)) hLne
        rw [hpole] at hb
        rw [hS8']
        linarith only [hb, he8def, hE2zdef, hE3zdef]
      -- ### the assembly
      have hFcnn : 0 ≤ Fc := by rw [hFcdef]; positivity
      have hC0cnn : 0 ≤ C0c := by rw [hC0cdef]; positivity
      have h1C0 : ((a + (Work.LinnikContract.lamOf q ρ₁)) / L) * C₀ ≤ C0c := by
        rw [hC0cdef]
        exact mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hαaup hLpos.le) hC₀pos.le
      have hE1 : e1 ≤ E := by rw [he1def]; exact heEz _ (by linarith only [h1C0, hFcnn])
      have hE2 : e2 ≤ E := by rw [he2def]; exact heE _ (by have h := hcFar 2 (by norm_num); linarith only [h, hC0cnn])
      have hE4 : e4 ≤ E := by rw [he4def]; exact heE _ (by have h := hcFar 2 (by norm_num); linarith only [h, hC0cnn])
      have hE5 : e5 ≤ E := by rw [he5def]; exact heE _ (by have h := hcFar 1 (by norm_num); linarith only [h, hC0cnn])
      have hE6 : e6 ≤ E := by rw [he6def]; exact heE _ (by have h := hcFar 1 (by norm_num); linarith only [h, hC0cnn])
      have hE7 : e7 ≤ E := by rw [he7def]; exact heE _ (by have h := hcFar 1 (by norm_num); linarith only [h, hC0cnn])
      have hE8 : e8 ≤ E := by rw [he8def]; exact heEz _ (by linarith only [h1C0, hFcnn])
      have hcomb : 0 ≤ (K ^ 2 + 1 / 2) * (S1 + S2) + K * (S3 + 2 * S4 + S5)
          + (1 / 4) * (S6 + 2 * S7 + S8) + 0 := by
        have h0 := P9.HbCombinationL_nonneg (q := q) χ₁ K (1 + a / L) ρ₀.im ρ₁.im a (Work.LinnikContract.lamOf q ρ₁)
          hK.le (by have h : 0 < a / L := div_pos ha hLpos; linarith only [h]) ha hlam₁nn
        rw [Work.ZeroFreeTables.HbCombinationL, ← hLdef, hB] at h0
        push_cast at h0
        simp only [hS1', hS2', hS3', hS4', hS5', hS6', hS7', hS8', sPt, Complex.ofReal_zero,
          zero_mul, add_zero]
        push_cast
        exact h0
      have habs : (K ^ 2 + 1 / 2) * (e1 + e2) + K * (e3 + 2 * e4 + e5)
          + (1 / 4) * (e6 + 2 * e7 + e8) + 0 + (a + (Work.LinnikContract.lamOf q ρ₁)) * ε₁ * (K ^ 2 + 3 * K + 5 / 4)
          ≤ (a + (Work.LinnikContract.lamOf q ρ₁)) * ε := by
        have hfin : a * ε / 2 + (a + (Work.LinnikContract.lamOf q ρ₁)) * (ε / 4)
            ≤ (a + (Work.LinnikContract.lamOf q ρ₁)) * ε := by
          linarith only [mul_pos ha hε, mul_nonneg hlam₁nn hε.le]
        have hsum := sumErr_le hK.le hE1 hE2 hE1 hE4 hE5 hE6 hE7 hE8
        have hε := mul_le_mul_of_nonneg_left hε₁bud hα0
        have hmain : 2 * (K + 1) ^ 2 * E ≤ a * ε / 2 := hEbound
        have h54 : (a + (Work.LinnikContract.lamOf q ρ₁)) * ε₁ * (K ^ 2 + 3 * K + 5 / 4)
            ≤ (a + (Work.LinnikContract.lamOf q ρ₁)) * (ε / 4) := by
          have h1 : (K ^ 2 + 3 * K + 5 / 4 : ℝ) ≤ K ^ 2 + 3 * K + 3 / 2 := by norm_num
          have h2 : 0 ≤ (a + (Work.LinnikContract.lamOf q ρ₁)) * ε₁ := by positivity
          calc (a + (Work.LinnikContract.lamOf q ρ₁)) * ε₁ * (K ^ 2 + 3 * K + 5 / 4)
              ≤ (a + (Work.LinnikContract.lamOf q ρ₁)) * ε₁ * (K ^ 2 + 3 * K + 3 / 2) :=
                mul_le_mul_of_nonneg_left h1 h2
            _ = (a + (Work.LinnikContract.lamOf q ρ₁)) * (ε₁ * (K ^ 2 + 3 * K + 3 / 2)) := by ring
            _ ≤ (a + (Work.LinnikContract.lamOf q ρ₁)) * (ε / 4) :=
                mul_le_mul_of_nonneg_left hε₁bud hα0
        linarith only [hsum, hmain, hfin, h54]
      exact caseB_bridge (a := a) (lam₁ := (Work.LinnikContract.lamOf q ρ₁))
        (lam₀ := (Work.LinnikContract.lamOf q ρ₀)) (K := K) (ε := ε) (ε₁ := ε₁)
        (Δ := Δ) (tB := (2 * ρ₁.im + ρ₀.im) * L)
        (S1 := S1) (S2 := S2) (S3 := S3) (S4 := S4) (S5 := S5) (S6 := S6)
        (S7 := S7) (S8 := S8) (e1 := e1) (e2 := e2) (e3 := e3) (e4 := e4) (e5 := e5)
        (e6 := e6) (e7 := e7) (e8 := e8) (corr := 0)
        hK.le hα0 hS1 hS2 hS3 hS4 hS5 hS6 hS7 hS8 hcomb
        (P3.P3Bounds.2 a (Work.LinnikContract.lamOf q ρ₁) (Work.LinnikContract.lamOf q ρ₀) K Δ
          ha hK hlam₁nn hlam₁lam₀ (side913 ha hK (by linarith only [ha, hlam₁nn]) (by linarith only [ha, hlam₀nn]) hcond).1)
        ((P9.rescale_variants.2.1) a (Work.LinnikContract.lamOf q ρ₁) (Work.LinnikContract.lamOf q ρ₀) K
          ((2 * ρ₁.im + ρ₀.im) * L) ha hlam₁nn hlam₁lam₀ hK
          (side913 ha hK (by linarith only [ha, hlam₁nn]) (by linarith only [ha, hlam₀nn]) hcond).2.1)
        habs
    · -- ### case A (χ₁ of order neither 2 nor 3)
      have hχ2 : χ₁ ^ 2 ≠ 1 := hC
      have hχ3 : χ₁ ^ 3 ≠ 1 := hB
      haveI hN1 : NeZero χ₁.conductor := ⟨χ₁.conductor_ne_zero⟩
      have hφ₁ne : χ₁.primitiveCharacter ≠ 1 := by
        intro hh
        exact hχ₁ne (by rw [← DirichletCharacter.changeLevel_primitiveCharacter χ₁, hh,
          DirichletCharacter.changeLevel_one χ₁.conductor_dvd_level])
      have hφ₁prim : χ₁.primitiveCharacter.IsPrimitive :=
        DirichletCharacter.primitiveCharacter_isPrimitive χ₁
      have hlogN1 : Real.log ((χ₁.conductor : ℕ) : ℝ) ≤ L :=
        hlogNOf χ₁.conductor_dvd_level χ₁.conductor_ne_zero
      have hzm1 : ∀ u : ℂ, Work.LinnikContract.zeroMult χ₁ u
          = Work.LinnikContract.zeroMult χ₁.primitiveCharacter u := by
        intro u
        have h := Work.ZeroFreeTables.Table4.zeroMult_changeLevel χ₁.conductor_dvd_level
          χ₁.primitiveCharacter u
        rw [DirichletCharacter.changeLevel_primitiveCharacter] at h
        exact h
      obtain ⟨par₁, hpar₁2, hpar₁0, hpar₁1⟩ := exists_par χ₁.primitiveCharacter
      have hminP1 := hminPrim χ₁.conductor_dvd_level χ₁.primitiveCharacter hφ₁ne hφ₁prim
      have hk1P1 : ∀ t : ℝ, |t| ≤ 4 → (-logDeriv (DirichletCharacter.LFunction χ₁.primitiveCharacter)
          (sPt a L t)).re + P9.nearInvSum χ₁.conductor χ₁.primitiveCharacter (sPt a L t) δ
          ≤ (1 / 6 + ε₁) * L := fun t ht =>
        hk1Of χ₁.primitiveCharacter hφ₁ne hφ₁prim hN3 hlogN1 t ht
      have hJ1 : ∀ s : ℂ, ‖s‖ ≤ 5 → P9.invSqSum χ₁.conductor χ₁.primitiveCharacter s ≤ Cj :=
        fun s hs => hJOf χ₁.conductor_dvd_level χ₁.primitiveCharacter hφ₁ne hφ₁prim s hs
      have hCc1 : ∀ t : ℝ, |SigmaP3L q L (DirichletCharacter.changeLevel χ₁.conductor_dvd_level
            χ₁.primitiveCharacter) (sPt a L t) a (Work.LinnikContract.lamOf q ρ₁)
          - SigmaP3L χ₁.conductor L χ₁.primitiveCharacter (sPt a L t) a (Work.LinnikContract.lamOf q ρ₁)| ≤ Corr :=
        fun t => hCcOf χ₁.conductor_dvd_level χ₁.primitiveCharacter t
      have hρ₁re : ρ₁.re = 1 - (Work.LinnikContract.lamOf q ρ₁) / L := by
        rw [hlamOf_eq ρ₁]; field_simp; ring
      have hρ₀re : ρ₀.re = 1 - (Work.LinnikContract.lamOf q ρ₀) / L := by
        rw [hlamOf_eq ρ₀]; field_simp; ring
      have hm3₁ : |ρ₁.im| ≤ 4 := by linarith only [hZ1.2.2]
      have hm3₀ : |ρ₀.im| ≤ 4 := by linarith only [him0]
      have hm3a : |ρ₁.im - ρ₀.im| ≤ 4 := by
        have h1 := abs_le.mp hZ1.2.2; have h0 := abs_le.mp him0
        rw [abs_le]; constructor <;> linarith only [h1.1, h1.2, h0.1, h0.2]
      have hm3b : |ρ₁.im + ρ₀.im| ≤ 4 := by
        have h1 := abs_le.mp hZ1.2.2; have h0 := abs_le.mp him0
        rw [abs_le]; constructor <;> linarith only [h1.1, h1.2, h0.1, h0.2]
      have hm3c : |2 * ρ₁.im| ≤ 4 := by
        have h1 := abs_le.mp hZ1.2.2
        rw [abs_le]; constructor <;> linarith only [h1.1, h1.2]
      have hm3d : |2 * ρ₁.im - ρ₀.im| ≤ 4 := by
        have h1 := abs_le.mp hZ1.2.2; have h0 := abs_le.mp him0
        rw [abs_le]; constructor <;> linarith only [h1.1, h1.2, h0.1, h0.2]
      have hm3e : |2 * ρ₁.im + ρ₀.im| ≤ 4 := by
        have h1 := abs_le.mp hZ1.2.2; have h0 := abs_le.mp him0
        rw [abs_le]; constructor <;> linarith only [h1.1, h1.2, h0.1, h0.2]
      have hcc0 := hCcOf (N := 1) (one_dvd q) (1 : DirichletCharacter ℂ 1) 0
      rw [DirichletCharacter.changeLevel_one (one_dvd q)] at hcc0
      -- ### error budgets
      set e1 : ℝ := ((a + (Work.LinnikContract.lamOf q ρ₁)) / L) * C₀ + E2z + E3z + Corr with he1def
      set e2 : ℝ := E2 + E3 + 2 * (8 * (a + (Work.LinnikContract.lamOf q ρ₁)) / (δ * L)) + Corr with he2def
      set e3 : ℝ := ((a + (Work.LinnikContract.lamOf q ρ₁)) / L) * C₀ + E2z + E3z + Corr with he3def
      set e4 : ℝ := E2 + E3 + 2 * (8 * (a + (Work.LinnikContract.lamOf q ρ₁)) / (δ * L)) + Corr with he4def
      set e5 : ℝ := E2 + E3 + Corr with he5def
      set e6 : ℝ := E2 + E3 + 8 * (a + (Work.LinnikContract.lamOf q ρ₁)) / (δ * L) + Corr with he6def
      set e7 : ℝ := E2 + E3 + Corr with he7def
      set e8 : ℝ := E2 + E3 + Corr with he8def
      -- ### the eight points
      set S1 : ℝ := SigmaP3L q L (1 : DirichletCharacter ℂ q) (sPt a L 0) a (Work.LinnikContract.lamOf q ρ₁) with hS1'
      set S2 : ℝ := SigmaP3L q L χ₁ (sPt a L ρ₀.im) a (Work.LinnikContract.lamOf q ρ₁) with hS2'
      set S3 : ℝ := SigmaP3L q L (1 : DirichletCharacter ℂ q) (sPt a L (ρ₁.im - ρ₀.im)) a (Work.LinnikContract.lamOf q ρ₁) with hS3'
      set S4 : ℝ := SigmaP3L q L χ₁ (sPt a L ρ₁.im) a (Work.LinnikContract.lamOf q ρ₁) with hS4'
      set S5 : ℝ := SigmaP3L q L (χ₁ ^ 2) (sPt a L (ρ₁.im + ρ₀.im)) a (Work.LinnikContract.lamOf q ρ₁) with hS5'
      set S6 : ℝ := SigmaP3L q L χ₁ (sPt a L (2 * ρ₁.im - ρ₀.im)) a (Work.LinnikContract.lamOf q ρ₁) with hS6'
      set S7 : ℝ := SigmaP3L q L (χ₁ ^ 2) (sPt a L (2 * ρ₁.im)) a (Work.LinnikContract.lamOf q ρ₁) with hS7'
      set S8 : ℝ := SigmaP3L q L (χ₁ ^ 3) (sPt a L (2 * ρ₁.im + ρ₀.im)) a (Work.LinnikContract.lamOf q ρ₁) with hS8'
      -- ### point 1: the principal character at σ
      have hS1 : S1 ≤ P3R ((a + (Work.LinnikContract.lamOf q ρ₁)) / a) + e1 := by
        have hb := point_bound_principal (q := q) (a := a) (lam₁ := (Work.LinnikContract.lamOf q ρ₁)) (δ := δ) (L := L)
          (Ct := Ct) (Cz := Cz) (C₀ := C₀) (Cc := Corr) ha hlam₁nn hδpos hδlt1 hLt haδL haL
          hCzZeta hC0b' hnzδ (s := sPt a L 0) (by simp [sPt]) (by simp [sPt])
          (hSzeta 0).1 (hSzeta 0).2 hcc0
        have hpole : (P3 (((a : ℂ) + ((Work.LinnikContract.lamOf q ρ₁) : ℂ)) / ((sPt a L 0 - 1) * (L : ℂ)))).re
            = P3R ((a + (Work.LinnikContract.lamOf q ρ₁)) / a) := by
          rw [P3_arg_eq_pole_split (a := a) (L := L) (t := 0) (lam := (Work.LinnikContract.lamOf q ρ₁)) hLne]
          rw [zero_mul, PhiG_zero]
        rw [hpole] at hb
        linarith only [hb, hS1', he1def, hE2zdef, hE3zdef]
      -- ### point 2: χ₁ at σ + iγ₀, kept {ρ₀, ρ₁}
      have hS2 : S2 ≤ -P3R ((a + (Work.LinnikContract.lamOf q ρ₁)) / (a + (Work.LinnikContract.lamOf q ρ₀))) - P9.PhiG (a + (Work.LinnikContract.lamOf q ρ₁)) (a + (Work.LinnikContract.lamOf q ρ₁)) Δ
          + (a + (Work.LinnikContract.lamOf q ρ₁)) * (1 / 6 + ε₁) + e2 := by
        have hz₁ : Work.LinnikContract.zeroMult χ₁.primitiveCharacter ρ₁ ≠ 0 := by
          rw [← hzm1 ρ₁]; exact hZ1.2.1
        have hz₀ : Work.LinnikContract.zeroMult χ₁.primitiveCharacter ρ₀ ≠ 0 := by
          rw [← hzm1 ρ₀]; exact hzm0
        have hT : ∀ u ∈ ({ρ₀, ρ₁} : Finset ℂ),
            Work.LinnikContract.zeroMult χ₁.primitiveCharacter u ≠ 0 := by
          intro u hu
          rcases Finset.mem_insert.mp hu with h | h
          · rw [h]; exact hz₀
          · rw [Finset.mem_singleton.mp h]; exact hz₁
        have hTim : ∀ u ∈ ({ρ₀, ρ₁} : Finset ℂ), |u.im| ≤ 10 := by
          intro u hu
          rcases Finset.mem_insert.mp hu with h | h
          · rw [h]; linarith only [him0]
          · rw [Finset.mem_singleton.mp h]; linarith only [hZ1.2.2]
        have hb := point_bound_q (q := q) (N := χ₁.conductor) (hNq := χ₁.conductor_dvd_level)
          (φ := χ₁.primitiveCharacter) hφ₁ne hφ₁prim ha hlam₁nn hδpos hδlt1 hLt haδL
          (s := sPt a L ρ₀.im) (by simp [sPt]) (by simpa [sPt] using hm3₀)
          (hk1P1 ρ₀.im hm3₀) par₁ hpar₁0 hpar₁1
          (hSpr par₁ hpar₁2 ρ₀.im).1 (hSpr par₁ hpar₁2 ρ₀.im).2
          (hJ1 (sPt a L ρ₀.im) (norm_sPt_le_five ha haL hLpos hm3₀))
          hminP1 ({ρ₀, ρ₁} : Finset ℂ) hT hTim (hCc1 ρ₀.im)
        have t1 : (P3 (((a : ℂ) + ((Work.LinnikContract.lamOf q ρ₁) : ℂ)) / ((sPt a L ρ₀.im - ρ₀) * (L : ℂ)))).re
            = P3R ((a + (Work.LinnikContract.lamOf q ρ₁)) / (a + (Work.LinnikContract.lamOf q ρ₀))) := by
          rw [P3_arg_eq_split (a := a) (L := L) (lam₁ := (Work.LinnikContract.lamOf q ρ₁)) (lam := (Work.LinnikContract.lamOf q ρ₀)) (gam := ρ₀.im)
            (t := ρ₀.im) (ρ := ρ₀) hLne hρ₀re rfl]
          rw [sub_self, zero_mul, PhiG_zero]
        have t2 : (P3 (((a : ℂ) + ((Work.LinnikContract.lamOf q ρ₁) : ℂ)) / ((sPt a L ρ₀.im - ρ₁) * (L : ℂ)))).re
            = P9.PhiG (a + (Work.LinnikContract.lamOf q ρ₁)) (a + (Work.LinnikContract.lamOf q ρ₁)) Δ := by
          rw [P3_arg_eq_split (a := a) (L := L) (lam₁ := (Work.LinnikContract.lamOf q ρ₁)) (lam := (Work.LinnikContract.lamOf q ρ₁)) (gam := ρ₁.im)
            (t := ρ₀.im) (ρ := ρ₁) hLne hρ₁re rfl]
          rw [show (ρ₀.im - ρ₁.im) * L = -Δ by rw [hΔdef]; ring]
          rw [PhiG_neg']
        have hsum : (∑ u ∈ ({ρ₀, ρ₁} : Finset ℂ),
            (P3 (((a : ℂ) + ((Work.LinnikContract.lamOf q ρ₁) : ℂ)) / ((sPt a L ρ₀.im - u) * (L : ℂ)))).re)
            = P3R ((a + (Work.LinnikContract.lamOf q ρ₁)) / (a + (Work.LinnikContract.lamOf q ρ₀))) + P9.PhiG (a + (Work.LinnikContract.lamOf q ρ₁)) (a + (Work.LinnikContract.lamOf q ρ₁)) Δ := by
          rw [Finset.sum_pair (Ne.symm hne), t1, t2]
        rw [DirichletCharacter.changeLevel_primitiveCharacter, ← hS2'] at hb
        rw [Finset.card_pair (Ne.symm hne), Nat.cast_ofNat, hsum] at hb
        rw [neg_add] at hb
        linarith only [hb, he2def, hE2def, hE3def]
      -- ### point 3: the principal character at σ + i(γ₁-γ₀)
      have hS3 : S3 ≤ P9.PhiG (a + (Work.LinnikContract.lamOf q ρ₁)) a Δ + e3 := by
        have hcc3 := hCcOf (N := 1) (one_dvd q) (1 : DirichletCharacter ℂ 1) (ρ₁.im - ρ₀.im)
        rw [DirichletCharacter.changeLevel_one (one_dvd q)] at hcc3
        have hb := point_bound_principal (q := q) (a := a) (lam₁ := (Work.LinnikContract.lamOf q ρ₁)) (δ := δ) (L := L)
          (Ct := Ct) (Cz := Cz) (C₀ := C₀) (Cc := Corr) ha hlam₁nn hδpos hδlt1 hLt haδL haL
          hCzZeta hC0b' hnzδ (s := sPt a L (ρ₁.im - ρ₀.im))
          (by simp [sPt]) (by simpa [sPt] using hm3a)
          (hSzeta (ρ₁.im - ρ₀.im)).1 (hSzeta (ρ₁.im - ρ₀.im)).2 hcc3
        have hpole : (P3 (((a : ℂ) + ((Work.LinnikContract.lamOf q ρ₁) : ℂ)) / ((sPt a L (ρ₁.im - ρ₀.im) - 1) * (L : ℂ)))).re
            = P9.PhiG (a + (Work.LinnikContract.lamOf q ρ₁)) a Δ :=
          P3_arg_eq_pole_split (a := a) (L := L) (t := ρ₁.im - ρ₀.im)
            (lam := (Work.LinnikContract.lamOf q ρ₁)) hLne
        rw [hpole] at hb
        linarith only [hb, hS3', he3def, hE2zdef, hE3zdef]
      -- ### point 4: χ₁ at σ + iγ₁, kept {ρ₀, ρ₁}
      have hS4 : S4 ≤ -P3R 1 - P9.PhiG (a + (Work.LinnikContract.lamOf q ρ₁)) (a + (Work.LinnikContract.lamOf q ρ₀)) Δ
          + (a + (Work.LinnikContract.lamOf q ρ₁)) * (1 / 6 + ε₁) + e4 := by
        have hz₁ : Work.LinnikContract.zeroMult χ₁.primitiveCharacter ρ₁ ≠ 0 := by
          rw [← hzm1 ρ₁]; exact hZ1.2.1
        have hz₀ : Work.LinnikContract.zeroMult χ₁.primitiveCharacter ρ₀ ≠ 0 := by
          rw [← hzm1 ρ₀]; exact hzm0
        have hT : ∀ u ∈ ({ρ₀, ρ₁} : Finset ℂ),
            Work.LinnikContract.zeroMult χ₁.primitiveCharacter u ≠ 0 := by
          intro u hu
          rcases Finset.mem_insert.mp hu with h | h
          · rw [h]; exact hz₀
          · rw [Finset.mem_singleton.mp h]; exact hz₁
        have hTim : ∀ u ∈ ({ρ₀, ρ₁} : Finset ℂ), |u.im| ≤ 10 := by
          intro u hu
          rcases Finset.mem_insert.mp hu with h | h
          · rw [h]; linarith only [him0]
          · rw [Finset.mem_singleton.mp h]; linarith only [hZ1.2.2]
        have hb := point_bound_q (q := q) (N := χ₁.conductor) (hNq := χ₁.conductor_dvd_level)
          (φ := χ₁.primitiveCharacter) hφ₁ne hφ₁prim ha hlam₁nn hδpos hδlt1 hLt haδL
          (s := sPt a L ρ₁.im) (by simp [sPt]) (by simpa [sPt] using hm3₁)
          (hk1P1 ρ₁.im hm3₁) par₁ hpar₁0 hpar₁1
          (hSpr par₁ hpar₁2 ρ₁.im).1 (hSpr par₁ hpar₁2 ρ₁.im).2
          (hJ1 (sPt a L ρ₁.im) (norm_sPt_le_five ha haL hLpos hm3₁))
          hminP1 ({ρ₀, ρ₁} : Finset ℂ) hT hTim (hCc1 ρ₁.im)
        have t1 : (P3 (((a : ℂ) + ((Work.LinnikContract.lamOf q ρ₁) : ℂ)) / ((sPt a L ρ₁.im - ρ₁) * (L : ℂ)))).re = P3R 1 := by
          rw [P3_arg_eq_split (a := a) (L := L) (lam₁ := (Work.LinnikContract.lamOf q ρ₁)) (lam := (Work.LinnikContract.lamOf q ρ₁)) (gam := ρ₁.im)
            (t := ρ₁.im) (ρ := ρ₁) hLne hρ₁re rfl]
          rw [sub_self, zero_mul, PhiG_zero]
          rw [show (a + (Work.LinnikContract.lamOf q ρ₁)) / (a + (Work.LinnikContract.lamOf q ρ₁)) = 1 by
            rw [div_self (ne_of_gt (lt_of_lt_of_le ha (le_add_of_nonneg_right hlam₁nn)))]]
        have t2 : (P3 (((a : ℂ) + ((Work.LinnikContract.lamOf q ρ₁) : ℂ)) / ((sPt a L ρ₁.im - ρ₀) * (L : ℂ)))).re
            = P9.PhiG (a + (Work.LinnikContract.lamOf q ρ₁)) (a + (Work.LinnikContract.lamOf q ρ₀)) Δ := by
          rw [P3_arg_eq_split (a := a) (L := L) (lam₁ := (Work.LinnikContract.lamOf q ρ₁)) (lam := (Work.LinnikContract.lamOf q ρ₀)) (gam := ρ₀.im)
            (t := ρ₁.im) (ρ := ρ₀) hLne hρ₀re rfl]
        have hsum : (∑ u ∈ ({ρ₀, ρ₁} : Finset ℂ),
            (P3 (((a : ℂ) + ((Work.LinnikContract.lamOf q ρ₁) : ℂ)) / ((sPt a L ρ₁.im - u) * (L : ℂ)))).re)
            = P3R 1 + P9.PhiG (a + (Work.LinnikContract.lamOf q ρ₁)) (a + (Work.LinnikContract.lamOf q ρ₀)) Δ := by
          rw [Finset.sum_pair (Ne.symm hne), t2, t1]
          ring
        rw [DirichletCharacter.changeLevel_primitiveCharacter, ← hS4'] at hb
        rw [Finset.card_pair (Ne.symm hne), Nat.cast_ofNat, hsum] at hb
        rw [neg_add] at hb
        linarith only [hb, he4def, hE2def, hE3def]
      -- ### point 5: χ₁² at σ + i(γ₁+γ₀), nothing kept
      haveI hN2 : NeZero (χ₁ ^ 2).conductor := ⟨(χ₁ ^ 2).conductor_ne_zero⟩
      have hφ₂ne : (χ₁ ^ 2).primitiveCharacter ≠ 1 := by
        intro hh
        exact hχ2 (by rw [← DirichletCharacter.changeLevel_primitiveCharacter (χ₁ ^ 2), hh,
          DirichletCharacter.changeLevel_one (χ₁ ^ 2).conductor_dvd_level])
      have hφ₂prim : (χ₁ ^ 2).primitiveCharacter.IsPrimitive :=
        DirichletCharacter.primitiveCharacter_isPrimitive (χ₁ ^ 2)
      have hlogN2 : Real.log (((χ₁ ^ 2).conductor : ℕ) : ℝ) ≤ L :=
        hlogNOf (χ₁ ^ 2).conductor_dvd_level (χ₁ ^ 2).conductor_ne_zero
      have hN2_3 : 3 ≤ (χ₁ ^ 2).conductor :=
        Work.LinnikAreas2.three_le_conductor (χ₁ ^ 2) hχ2
      have hS5 : S5 ≤ (a + (Work.LinnikContract.lamOf q ρ₁)) * (1 / 6 + ε₁) + e5 := by
        obtain ⟨par₂, hpar₂2, hpar₂0, hpar₂1⟩ := exists_par (χ₁ ^ 2).primitiveCharacter
        have hb := point_bound_q (q := q) (N := (χ₁ ^ 2).conductor)
          (hNq := (χ₁ ^ 2).conductor_dvd_level) (φ := (χ₁ ^ 2).primitiveCharacter) hφ₂ne
          hφ₂prim ha hlam₁nn hδpos hδlt1 hLt haδL
          (s := sPt a L (ρ₁.im + ρ₀.im)) (by simp [sPt]) (by simpa [sPt] using hm3b)
          (hk1Of (χ₁ ^ 2).primitiveCharacter hφ₂ne hφ₂prim hN2_3 hlogN2 (ρ₁.im + ρ₀.im) hm3b)
          par₂ hpar₂0 hpar₂1
          (hSpr par₂ hpar₂2 (ρ₁.im + ρ₀.im)).1 (hSpr par₂ hpar₂2 (ρ₁.im + ρ₀.im)).2
          (hJOf (χ₁ ^ 2).conductor_dvd_level (χ₁ ^ 2).primitiveCharacter hφ₂ne hφ₂prim
            (sPt a L (ρ₁.im + ρ₀.im)) (norm_sPt_le_five ha haL hLpos hm3b))
          (hminPrim (χ₁ ^ 2).conductor_dvd_level (χ₁ ^ 2).primitiveCharacter hφ₂ne hφ₂prim)
          (∅ : Finset ℂ) (by simp) (by simp)
          (hCcOf (χ₁ ^ 2).conductor_dvd_level (χ₁ ^ 2).primitiveCharacter (ρ₁.im + ρ₀.im))
        have hsum : (∑ u ∈ (∅ : Finset ℂ),
            (P3 (((a : ℂ) + ((Work.LinnikContract.lamOf q ρ₁) : ℂ)) / ((sPt a L (ρ₁.im + ρ₀.im) - u) * (L : ℂ)))).re) = 0 :=
          Finset.sum_empty
        rw [DirichletCharacter.changeLevel_primitiveCharacter, ← hS5'] at hb
        rw [hsum, Finset.card_empty, Nat.cast_zero, zero_mul, neg_zero, zero_add, add_zero] at hb
        linarith only [hb, he5def, hE2def, hE3def]
      -- ### point 6: χ₁ at σ + i(2γ₁-γ₀), kept {ρ₁}
      have hS6 : S6 ≤ -P9.PhiG (a + (Work.LinnikContract.lamOf q ρ₁)) (a + (Work.LinnikContract.lamOf q ρ₁)) Δ
          + (a + (Work.LinnikContract.lamOf q ρ₁)) * (1 / 6 + ε₁) + e6 := by
        have hz₁ : Work.LinnikContract.zeroMult χ₁.primitiveCharacter ρ₁ ≠ 0 := by
          rw [← hzm1 ρ₁]; exact hZ1.2.1
        have hT : ∀ u ∈ ({ρ₁} : Finset ℂ),
            Work.LinnikContract.zeroMult χ₁.primitiveCharacter u ≠ 0 := by
          intro u hu; rw [Finset.mem_singleton.mp hu]; exact hz₁
        have hTim : ∀ u ∈ ({ρ₁} : Finset ℂ), |u.im| ≤ 10 := by
          intro u hu; rw [Finset.mem_singleton.mp hu]; linarith only [hZ1.2.2]
        have hb := point_bound_q (q := q) (N := χ₁.conductor) (hNq := χ₁.conductor_dvd_level)
          (φ := χ₁.primitiveCharacter) hφ₁ne hφ₁prim ha hlam₁nn hδpos hδlt1 hLt haδL
          (s := sPt a L (2 * ρ₁.im - ρ₀.im)) (by simp [sPt]) (by simpa [sPt] using hm3d)
          (hk1P1 (2 * ρ₁.im - ρ₀.im) hm3d) par₁ hpar₁0 hpar₁1
          (hSpr par₁ hpar₁2 (2 * ρ₁.im - ρ₀.im)).1 (hSpr par₁ hpar₁2 (2 * ρ₁.im - ρ₀.im)).2
          (hJ1 (sPt a L (2 * ρ₁.im - ρ₀.im)) (norm_sPt_le_five ha haL hLpos hm3d))
          hminP1 ({ρ₁} : Finset ℂ) hT hTim (hCc1 (2 * ρ₁.im - ρ₀.im))
        have t1 : (P3 (((a : ℂ) + ((Work.LinnikContract.lamOf q ρ₁) : ℂ)) / ((sPt a L (2 * ρ₁.im - ρ₀.im) - ρ₁) * (L : ℂ)))).re
            = P9.PhiG (a + (Work.LinnikContract.lamOf q ρ₁)) (a + (Work.LinnikContract.lamOf q ρ₁)) Δ := by
          rw [P3_arg_eq_split (a := a) (L := L) (lam₁ := (Work.LinnikContract.lamOf q ρ₁)) (lam := (Work.LinnikContract.lamOf q ρ₁)) (gam := ρ₁.im)
            (t := 2 * ρ₁.im - ρ₀.im) (ρ := ρ₁) hLne hρ₁re rfl]
          rw [show (2 * ρ₁.im - ρ₀.im - ρ₁.im) * L = Δ by rw [hΔdef]; ring]
        have hsum : (∑ u ∈ ({ρ₁} : Finset ℂ),
            (P3 (((a : ℂ) + ((Work.LinnikContract.lamOf q ρ₁) : ℂ)) / ((sPt a L (2 * ρ₁.im - ρ₀.im) - u) * (L : ℂ)))).re)
            = P9.PhiG (a + (Work.LinnikContract.lamOf q ρ₁)) (a + (Work.LinnikContract.lamOf q ρ₁)) Δ := by
          rw [Finset.sum_singleton, t1]
        rw [DirichletCharacter.changeLevel_primitiveCharacter, ← hS6'] at hb
        rw [Finset.card_singleton, Nat.cast_one, one_mul, hsum] at hb
        linarith only [hb, he6def, hE2def, hE3def]
      -- ### point 7: χ₁² at σ + 2iγ₁, nothing kept
      have hS7 : S7 ≤ (a + (Work.LinnikContract.lamOf q ρ₁)) * (1 / 6 + ε₁) + e7 := by
        obtain ⟨par₂, hpar₂2, hpar₂0, hpar₂1⟩ := exists_par (χ₁ ^ 2).primitiveCharacter
        have hb := point_bound_q (q := q) (N := (χ₁ ^ 2).conductor)
          (hNq := (χ₁ ^ 2).conductor_dvd_level) (φ := (χ₁ ^ 2).primitiveCharacter) hφ₂ne
          hφ₂prim ha hlam₁nn hδpos hδlt1 hLt haδL
          (s := sPt a L (2 * ρ₁.im)) (by simp [sPt]) (by simpa [sPt] using hm3c)
          (hk1Of (χ₁ ^ 2).primitiveCharacter hφ₂ne hφ₂prim hN2_3 hlogN2 (2 * ρ₁.im) hm3c)
          par₂ hpar₂0 hpar₂1
          (hSpr par₂ hpar₂2 (2 * ρ₁.im)).1 (hSpr par₂ hpar₂2 (2 * ρ₁.im)).2
          (hJOf (χ₁ ^ 2).conductor_dvd_level (χ₁ ^ 2).primitiveCharacter hφ₂ne hφ₂prim
            (sPt a L (2 * ρ₁.im)) (norm_sPt_le_five ha haL hLpos hm3c))
          (hminPrim (χ₁ ^ 2).conductor_dvd_level (χ₁ ^ 2).primitiveCharacter hφ₂ne hφ₂prim)
          (∅ : Finset ℂ) (by simp) (by simp)
          (hCcOf (χ₁ ^ 2).conductor_dvd_level (χ₁ ^ 2).primitiveCharacter (2 * ρ₁.im))
        have hsum : (∑ u ∈ (∅ : Finset ℂ),
            (P3 (((a : ℂ) + ((Work.LinnikContract.lamOf q ρ₁) : ℂ)) / ((sPt a L (2 * ρ₁.im) - u) * (L : ℂ)))).re) = 0 :=
          Finset.sum_empty
        rw [DirichletCharacter.changeLevel_primitiveCharacter, ← hS7'] at hb
        rw [hsum, Finset.card_empty, Nat.cast_zero, zero_mul, neg_zero, zero_add, add_zero] at hb
        linarith only [hb, he7def, hE2def, hE3def]
      -- ### point 8: χ₁³ at σ + i(2γ₁+γ₀), nothing kept
      haveI hN3' : NeZero (χ₁ ^ 3).conductor := ⟨(χ₁ ^ 3).conductor_ne_zero⟩
      have hφ₃ne : (χ₁ ^ 3).primitiveCharacter ≠ 1 := by
        intro hh
        exact hχ3 (by rw [← DirichletCharacter.changeLevel_primitiveCharacter (χ₁ ^ 3), hh,
          DirichletCharacter.changeLevel_one (χ₁ ^ 3).conductor_dvd_level])
      have hφ₃prim : (χ₁ ^ 3).primitiveCharacter.IsPrimitive :=
        DirichletCharacter.primitiveCharacter_isPrimitive (χ₁ ^ 3)
      have hlogN3 : Real.log (((χ₁ ^ 3).conductor : ℕ) : ℝ) ≤ L :=
        hlogNOf (χ₁ ^ 3).conductor_dvd_level (χ₁ ^ 3).conductor_ne_zero
      have hN3_3 : 3 ≤ (χ₁ ^ 3).conductor :=
        Work.LinnikAreas2.three_le_conductor (χ₁ ^ 3) hχ3
      have hS8 : S8 ≤ (a + (Work.LinnikContract.lamOf q ρ₁)) * (1 / 6 + ε₁) + e8 := by
        obtain ⟨par₃, hpar₃2, hpar₃0, hpar₃1⟩ := exists_par (χ₁ ^ 3).primitiveCharacter
        have hb := point_bound_q (q := q) (N := (χ₁ ^ 3).conductor)
          (hNq := (χ₁ ^ 3).conductor_dvd_level) (φ := (χ₁ ^ 3).primitiveCharacter) hφ₃ne
          hφ₃prim ha hlam₁nn hδpos hδlt1 hLt haδL
          (s := sPt a L (2 * ρ₁.im + ρ₀.im)) (by simp [sPt]) (by simpa [sPt] using hm3e)
          (hk1Of (χ₁ ^ 3).primitiveCharacter hφ₃ne hφ₃prim hN3_3 hlogN3 (2 * ρ₁.im + ρ₀.im) hm3e)
          par₃ hpar₃0 hpar₃1
          (hSpr par₃ hpar₃2 (2 * ρ₁.im + ρ₀.im)).1 (hSpr par₃ hpar₃2 (2 * ρ₁.im + ρ₀.im)).2
          (hJOf (χ₁ ^ 3).conductor_dvd_level (χ₁ ^ 3).primitiveCharacter hφ₃ne hφ₃prim
            (sPt a L (2 * ρ₁.im + ρ₀.im)) (norm_sPt_le_five ha haL hLpos hm3e))
          (hminPrim (χ₁ ^ 3).conductor_dvd_level (χ₁ ^ 3).primitiveCharacter hφ₃ne hφ₃prim)
          (∅ : Finset ℂ) (by simp) (by simp)
          (hCcOf (χ₁ ^ 3).conductor_dvd_level (χ₁ ^ 3).primitiveCharacter (2 * ρ₁.im + ρ₀.im))
        have hsum : (∑ u ∈ (∅ : Finset ℂ),
            (P3 (((a : ℂ) + ((Work.LinnikContract.lamOf q ρ₁) : ℂ)) / ((sPt a L (2 * ρ₁.im + ρ₀.im) - u) * (L : ℂ)))).re) = 0 :=
          Finset.sum_empty
        rw [DirichletCharacter.changeLevel_primitiveCharacter, ← hS8'] at hb
        rw [hsum, Finset.card_empty, Nat.cast_zero, zero_mul, neg_zero, zero_add, add_zero] at hb
        linarith only [hb, he8def, hE2def, hE3def]
      -- ### the assembly
      have hFcnn : 0 ≤ Fc := by rw [hFcdef]; positivity
      have hC0cnn : 0 ≤ C0c := by rw [hC0cdef]; positivity
      have h1C0 : ((a + (Work.LinnikContract.lamOf q ρ₁)) / L) * C₀ ≤ C0c := by
        rw [hC0cdef]
        exact mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hαaup hLpos.le) hC₀pos.le
      have hE1 : e1 ≤ E := by
        exact heEz _ (by linarith only [he1def, h1C0, hFcnn])
      have hE2 : e2 ≤ E := by
        exact heE _ (by have h := hcFar 2 (by norm_num); linarith only [h, hC0cnn, he2def])
      have hE4 : e4 ≤ E := by
        exact heE _ (by have h := hcFar 2 (by norm_num); linarith only [h, hC0cnn, he4def])
      have hE5 : e5 ≤ E := by
        exact heE _ (by have h := hcFar 0 (by norm_num); linarith only [h, hC0cnn, hFcnn, he5def])
      have hE6 : e6 ≤ E := by
        exact heE _ (by have h := hcFar 1 (by norm_num); linarith only [h, hC0cnn, he6def])
      have hE7 : e7 ≤ E := by
        exact heE _ (by have h := hcFar 0 (by norm_num); linarith only [h, hC0cnn, hFcnn, he7def])
      have hE8 : e8 ≤ E := by
        exact heE _ (by have h := hcFar 0 (by norm_num); linarith only [h, hC0cnn, hFcnn, he8def])
      have hcomb : 0 ≤ (K ^ 2 + 1 / 2) * (S1 + S2) + K * (S3 + 2 * S4 + S5)
          + (1 / 4) * (S6 + 2 * S7 + S8) + 0 := by
        have h0 := P9.HbCombinationL_nonneg (q := q) χ₁ K (1 + a / L) ρ₀.im ρ₁.im a (Work.LinnikContract.lamOf q ρ₁)
          hK.le (by have h : 0 < a / L := div_pos ha hLpos; linarith only [h]) ha hlam₁nn
        rw [Work.ZeroFreeTables.HbCombinationL, ← hLdef] at h0
        push_cast at h0
        simp only [hS1', hS2', hS3', hS4', hS5', hS6', hS7', hS8', sPt, Complex.ofReal_zero,
          zero_mul, add_zero]
        push_cast
        exact h0
      have habs : (K ^ 2 + 1 / 2) * (e1 + e2) + K * (e3 + 2 * e4 + e5)
          + (1 / 4) * (e6 + 2 * e7 + e8) + 0 + (a + (Work.LinnikContract.lamOf q ρ₁)) * ε₁ * (K ^ 2 + 3 * K + 3 / 2)
          ≤ (a + (Work.LinnikContract.lamOf q ρ₁)) * ε := by
        have hfin : a * ε / 2 + (a + (Work.LinnikContract.lamOf q ρ₁)) * (ε / 4) ≤ (a + (Work.LinnikContract.lamOf q ρ₁)) * ε := by
          linarith only [mul_pos ha hε, mul_nonneg hlam₁nn hε.le]
        have hsum := sumErr_le hK.le hE1 hE2 hE1 hE4 hE5 hE6 hE7 hE8
        have hε := mul_le_mul_of_nonneg_left hε₁bud hα0
        have hmain : 2 * (K + 1) ^ 2 * E ≤ a * ε / 2 := hEbound
        linarith only [hsum, hmain, hε, hfin]
      exact caseA_bridge (a := a) (lam₁ := (Work.LinnikContract.lamOf q ρ₁)) (lam₀ := (Work.LinnikContract.lamOf q ρ₀)) (K := K) (ε := ε) (ε₁ := ε₁)
        (Δ := Δ) (S1 := S1) (S2 := S2) (S3 := S3) (S4 := S4) (S5 := S5) (S6 := S6)
        (S7 := S7) (S8 := S8) (e1 := e1) (e2 := e2) (e3 := e3) (e4 := e4) (e5 := e5)
        (e6 := e6) (e7 := e7) (e8 := e8) (corr := 0)
        hK.le hS1 hS2 hS3 hS4 hS5 hS6 hS7 hS8 hcomb
        (P3.P3Bounds.2 a (Work.LinnikContract.lamOf q ρ₁) (Work.LinnikContract.lamOf q ρ₀) K Δ ha hK hlam₁nn hlam₁lam₀
          (side913 ha hK (by linarith only [ha, hlam₁nn]) (by linarith only [ha, hlam₀nn]) hcond).1) habs


end Work.ZeroFreeTables.HB94.Lam0GeEngine
