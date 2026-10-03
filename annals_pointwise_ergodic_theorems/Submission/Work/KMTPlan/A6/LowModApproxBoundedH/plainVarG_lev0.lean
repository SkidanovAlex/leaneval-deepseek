import Mathlib
import Submission.Work.KMTAreas.A7.LoModelLargeScaleHolds
import Submission.Port.Aesm

namespace Work.KMTPlan.A6.LowModApproxBoundedH

open MeasureTheory
open scoped ENNReal NNReal BigOperators
open PointwiseErgodicTheorems Submission.PointwiseErgodicTheorems

noncomputable section

/-! ## Auxiliary facts about the arithmetic-free multiplier and the `core` guard

The family of the target involves only `Tle ρ 0`, which is independent of `ρ`
(`iwArithFreqs ρ 0 = {0}`), clipped at `core ρ C₀ l₁ 0 k₁ k₂`.  The `core` guard is a *tail* in the
index (`core_mono`), so the clipped family is a tail of the unclipped family; the clipped estimate
is therefore reduced to the unclipped estimate along a shifted lacunary sequence, on which the
`core` guard holds identically.  Handling the `ρ`-dependence of the guard needs only the trivial
monotonicity of `splitCut`/`uScale`/`inIndexSet` in `ρ` and in the height parameters. -/

/-- `Tle ρ 0` does not depend on `ρ`: `iwArithFreqs ρ 0` is the singleton `{0}` for every `ρ`. -/
private lemma Tle_zero_rho_indep (ρ ρ' : ℝ) (φ : ℝ → ℂ) (f : ℤ → ℂ) :
    Work.KMTAreas.A7.Tle ρ 0 φ f = Work.KMTAreas.A7.Tle ρ' 0 φ f := by
  simp only [Work.KMTAreas.A7.Tle, Work.KMTAreas.A7.iwArithFreqs_zero]

/-- The auxiliary scale `u = ⌊2^{2ρL}⌋` is monotone in `ρ`. -/
lemma uScale_mono_rho_aux (L : ℕ) : Monotone (fun ρ : ℝ => Work.KMTAreas.A7.uScale ρ L) := by
  intro ρ ρ' hρ
  have hL : (0 : ℝ) ≤ (L : ℝ) := Nat.cast_nonneg L
  have hexp : 2 * ρ * (L : ℝ) ≤ 2 * ρ' * (L : ℝ) := by nlinarith
  have h1 : ((1 : ℕ) : ℝ) * (2 : ℝ) ^ (2 * ρ * (L : ℝ))
      ≤ ((1 : ℕ) : ℝ) * (2 : ℝ) ^ (2 * ρ' * (L : ℝ)) := by
    simpa using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hexp
  simp only [Work.KMTAreas.A7.uScale, Work.Analysis.EndVar.scaleCount]
  exact Nat.floor_mono h1

/-- The small-scale threshold `splitCut ρ L = 2^{2^u}` is monotone in `ρ`. -/
lemma splitCut_mono_rho_aux {ρ ρ' : ℝ} (h : ρ ≤ ρ') (L : ℕ) :
    Work.KMTAreas.A7.splitCut ρ L ≤ Work.KMTAreas.A7.splitCut ρ' L := by
  unfold Work.KMTAreas.A7.splitCut
  exact Nat.pow_le_pow_right (by norm_num)
    (Nat.pow_le_pow_right (by norm_num) (uScale_mono_rho_aux L h))

/-- **The `core` guard is antitone in `ρ` and in the four height parameters.** -/
lemma core_anti {ρ ρ' : ℝ} {C₀ : ℕ} {l₁ l₂ k₁ k₂ l₁' l₂' k₁' k₂' : ℕ} {a : ℕ → NNReal} {n : ℕ}
    (hρ0 : 0 ≤ ρ') (hρ : ρ' ≤ ρ) (h1 : l₁' ≤ l₁) (h2 : l₂' ≤ l₂) (h3 : k₁' ≤ k₁)
    (h4 : k₂' ≤ k₂) (h : Work.KMTAreas.A7.core ρ C₀ l₁ l₂ k₁ k₂ a n) :
    Work.KMTAreas.A7.core ρ' C₀ l₁' l₂' k₁' k₂' a n := by
  obtain ⟨hin, hcut, hmain⟩ := h
  obtain ⟨hi1, hi2, hi3⟩ := hin
  obtain ⟨hm1, hm2⟩ := hmain
  have hmaxl : max l₁' l₂' ≤ max l₁ l₂ :=
    max_le (le_trans h1 (le_max_left _ _)) (le_trans h2 (le_max_right _ _))
  have hmaxk : max k₁' k₂' ≤ max k₁ k₂ :=
    max_le (le_trans h3 (le_max_left _ _)) (le_trans h4 (le_max_right _ _))
  have hL : max (max l₁' l₂') (max k₁' k₂') ≤ max (max l₁ l₂) (max k₁ k₂) :=
    max_le (le_trans hmaxl (le_max_left _ _)) (le_trans hmaxk (le_max_right _ _))
  have hρ0' : 0 ≤ ρ := le_trans hρ0 hρ
  have hu : Work.KMTAreas.A7.uScale ρ' (max k₁' k₂')
      ≤ Work.KMTAreas.A7.uScale ρ (max k₁ k₂) :=
    le_trans (uScale_mono_rho_aux _ hρ) (Work.KMTAreas.A7.uScale_mono hρ0' hmaxk)
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · have hcast : (max l₁' l₂' : ℤ) ≤ (max l₁ l₂ : ℤ) := by exact_mod_cast hmaxl
    exact le_trans hcast hi1
  · have hcast : (k₁' : ℤ) ≤ (k₁ : ℤ) := by exact_mod_cast h3
    exact le_trans hcast hi2
  · have hcast : (k₂' : ℤ) ≤ (k₂ : ℤ) := by exact_mod_cast h4
    exact le_trans hcast hi3
  · exact lt_of_le_of_lt
      (le_trans (Work.KMTAreas.A7.splitCut_mono ρ' hρ0 hL) (splitCut_mono_rho_aux hρ _)) hcut
  · exact le_trans (add_le_add h3 (Nat.mul_le_mul_left 2 hu)) hm1
  · exact le_trans (add_le_add h4 (Nat.mul_le_mul_left 2 hu)) hm2

/-- **The `core` guard at the bottom of the parameter range**: from `core ρ C₀ l₁ 0 k₁ k₂` at a
radius `ρ' ≤ ρ` and heights `0 ≤ l₁`, `0 ≤ k₁` one gets `core ρ' C₀ 0 0 0 k₂`. -/
lemma core_anti_bot {ρ ρ' : ℝ} {C₀ l₁ k₁ k₂ : ℕ} {a : ℕ → NNReal} {n : ℕ}
    (hρ0 : 0 ≤ ρ') (hρ : ρ' ≤ ρ) (h : Work.KMTAreas.A7.core ρ C₀ l₁ 0 k₁ k₂ a n) :
    Work.KMTAreas.A7.core ρ' C₀ 0 0 0 k₂ a n :=
  core_anti hρ0 hρ (Nat.zero_le _) le_rfl (Nat.zero_le _) le_rfl h

/-- **The `g`-side *level-0* (arithmetic-free) lacunary variational estimate at `p = 2`,
clipped to the core index set, for arbitrary `ρ > 0`.**  For every `B` there is `C : ℝ≥0 → ℝ≥0` such
that for every `Λ`-lacunary family `a` with `a n ≥ 1`, every `k₂ ≤ B` and every `t ∈ [1/2,1]`, the
`ℓ²(ℤ)` norm of the `r`-variation of
`n ↦ 1_{core} Tle ρ 0 (varphitildeNt P P.natDegree ⌊a n⌋ k₂ t) G` is at most `C Λ ‖G‖₂`.

How to prove it (all ingredients proved and axiom-clean; no `ρ ≤ 1` is needed):

* `Tle ρ 0` is the plain, `ρ`-free convolution (`iwArithFreqs ρ 0 = {0}` for every `ρ`), so the
  proved `ρ ≤ 1` results (`Work.KMTAreas.A7.LoGLinVarClipped`, and behind it
  `A7.LoGFareyPartBound`, `A7.LoGFareyDiffPartBound`, `A7.LoGLowpassClipped`,
  `A7G.plainBumpVarG`, `A7.LoGBadPartVar`) may be instantiated at `ρ = 1` and transported along
  `Tle ρ 0 = Tle 1 0`;
* the clips: `core ρ …` vs `core 1 …` differ only on a finite set of indices of size bounded in
  terms of `ρ, C₀, B, Λ` (both are tails, `a` is monotone, and the *thresholds*
  `splitCut ρ L`, `splitCut 1 L` with `L = lcL ≤ B` are bounded in terms of `ρ, B`), and the
  `Farey`-clip of the narrow parts is likewise removed on a finite set (`¬Farey` forces
  `logN N < k₂ + Cρc`, i.e. `N ≤ 2^{B+Cρc}`); each of those finitely many scales is bounded
  pointwise by `‖cw φ‖_{ℓ²} ‖G‖₂ ≤ ‖G‖₂`;
* `lcL ≤ B` bounds the `lossWeight 4 ρ …`/`lossWeight 4 1 …` factors by constants in `ρ, C₀, B`. -/
theorem plainVarG_lev0 (P : Polynomial ℤ) (hd : 2 ≤ P.natDegree) (r : NNReal) (hr : 2 < r)
    (C₀ : ℕ) (hC₀ : 1 ≤ C₀) (ρ : ℝ) (hρ : 0 < ρ) (B : ℕ) :
    ∃ C : NNReal → NNReal,
      ∀ (a : ℕ → NNReal) (Λ : NNReal) (l₁ k₁ k₂ : ℕ) (t : ℝ) (G : ℤ → ℂ),
        1 < Λ → PointwiseErgodicTheorems.Lacunary Λ a → (∀ n, 1 ≤ a n) →
        k₂ ≤ B → t ∈ Set.Icc (1 / 2 : ℝ) 1 →
        MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
            (fun n : ℕ => if Work.KMTAreas.A7.core ρ C₀ l₁ 0 k₁ k₂ a n then
              Work.KMTAreas.A7.Tle ρ 0
                (Work.KMTAreas.A7.varphitildeNt P P.natDegree (Nat.floor (a n)) k₂ t) G x
              else 0)) 2 MeasureTheory.Measure.count
          ≤ (C Λ : ENNReal) * MeasureTheory.eLpNorm G 2 MeasureTheory.Measure.count := by
  classical
  have hr1 : (1 : NNReal) ≤ r := le_trans (by norm_num) hr.le
  -- the admissible radius `ρ' = min ρ 1 (1/(2C₀))`, at which `LoGLinVarClipped` applies
  set ρ' : ℝ := min (min ρ 1) (1 / (2 * (C₀ : ℝ))) with hρ'def
  have hρ'pos : 0 < ρ' := by
    rw [hρ'def]
    exact lt_min (lt_min hρ one_pos) (by positivity)
  have hρ'nn : 0 ≤ ρ' := hρ'pos.le
  have hρ'le1 : ρ' ≤ 1 := by
    rw [hρ'def]; exact le_trans (min_le_left _ _) (min_le_right _ _)
  have hρ'leC : ρ' ≤ 1 / (2 * (C₀ : ℝ)) := by rw [hρ'def]; exact min_le_right _ _
  have hρ'leρ : ρ' ≤ ρ := by
    rw [hρ'def]; exact le_trans (min_le_left _ _) (min_le_left _ _)
  -- the constant of the clipped estimate, as a function of `Λ`
  set Clo : NNReal → ℝ := fun Λ =>
    if h : 1 < Λ then Classical.choose (Work.KMTAreas.A7.LoGLinVarClipped P hd C₀ hC₀ ρ'
      hρ'pos hρ'le1 hρ'leC 2 (by norm_num) (by norm_num) r hr Λ h) else 0 with hClodef
  have hClopos : ∀ Λ, 1 < Λ → 0 < Clo Λ := by
    intro Λ hΛ
    rw [hClodef]; simp only [dif_pos hΛ]
    exact (Classical.choose_spec (Work.KMTAreas.A7.LoGLinVarClipped P hd C₀ hC₀ ρ'
      hρ'pos hρ'le1 hρ'leC 2 (by norm_num) (by norm_num) r hr Λ hΛ)).1
  have hClo_spec : ∀ (Λ : NNReal) (hΛ : 1 < Λ) (a : ℕ → NNReal)
      (ha : PointwiseErgodicTheorems.Lacunary Λ a) (ha1 : ∀ n, 1 ≤ a n)
      (l₁ l₂ k₁ k₂ : ℕ) (t : ℝ) (ht : t ∈ Set.Icc (1 / 2 : ℝ) 1) (g : ℤ → ℂ),
      MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
          (fun n : ℕ => if Work.KMTAreas.A7.core ρ' C₀ l₁ l₂ k₁ k₂ a n then
            Work.KMTAreas.A7.Tle ρ' 0
              (Work.KMTAreas.A7.varphitildeNt P P.natDegree (Nat.floor (a n)) k₂ t) g x
            else 0)) 2 MeasureTheory.Measure.count
        ≤ ENNReal.ofReal (Clo Λ * Work.KMTAreas.A7.lossWeight 4 ρ' l₁ l₂ k₁ k₂)
            * MeasureTheory.eLpNorm g 2 MeasureTheory.Measure.count := by
    intro Λ hΛ
    rw [hClodef]; simp only [dif_pos hΛ]
    exact (Classical.choose_spec (Work.KMTAreas.A7.LoGLinVarClipped P hd C₀ hC₀ ρ'
      hρ'pos hρ'le1 hρ'leC 2 (by norm_num) (by norm_num) r hr Λ hΛ)).2
  -- a constant bounding the loss weight at the bottom of the parameter range
  set Cw : ℝ := (1 + (B : ℝ)) ^ (4 : ℝ) * (2 : ℝ) ^ (4 * (B : ℝ)) with hCwdef
  have hCwnn : 0 ≤ Cw := by rw [hCwdef]; positivity
  have hlw : ∀ k₂ : ℕ, k₂ ≤ B → Work.KMTAreas.A7.lossWeight 4 ρ' 0 0 0 k₂ ≤ Cw := by
    intro k₂ hk₂
    have hL : Work.KMTAreas.A7.lmaxR 0 0 0 k₂ = (k₂ : ℝ) := by
      rw [Work.KMTAreas.A7.lmaxR, Work.Analysis.EndVar.lmax]
      norm_num
    rw [Work.KMTAreas.A7.lossWeight, hL, hCwdef]
    have hB1 : (1 : ℝ) + (k₂ : ℝ) ≤ 1 + (B : ℝ) := by
      have : (k₂ : ℝ) ≤ (B : ℝ) := by exact_mod_cast hk₂
      linarith
    have h1 : (1 + (k₂ : ℝ)) ^ (4 : ℝ) ≤ (1 + (B : ℝ)) ^ (4 : ℝ) :=
      Real.rpow_le_rpow (by positivity) hB1 (by norm_num)
    have h2 : (2 : ℝ) ^ (4 * ρ' * (k₂ : ℝ)) ≤ (2 : ℝ) ^ (4 * (B : ℝ)) := by
      refine Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) ?_
      nlinarith [hρ'pos.le, hC₀]
    exact mul_le_mul h1 h2 (Real.rpow_pos_of_pos (by norm_num) _).le
      (Real.rpow_nonneg (by positivity) _)
  refine ⟨fun Λ => if h : 1 < Λ then Real.toNNReal (2 * (Clo Λ * Cw + 1)) else 0, ?_⟩
  intro a Λ l₁ k₁ k₂ t G hΛ ha ha1 hk₂B ht
  have hCval : (((fun Λ => if h : 1 < Λ then Real.toNNReal (2 * (Clo Λ * Cw + 1)) else 0) Λ
      : NNReal) : ENNReal) = ENNReal.ofReal (2 * (Clo Λ * Cw + 1)) := by
    simp only [dif_pos hΛ]
    rfl
  rw [hCval]
  have hamono : Monotone a := Work.KMTAreas.A7.monotone_of_lacunary_aux hΛ ha ha1
  by_cases hex : ∃ n, Work.KMTAreas.A7.core ρ C₀ l₁ 0 k₁ k₂ a n
  · -- the guard is a tail; clip it off and estimate the shifted family
    obtain ⟨m, hm⟩ : ∃ m : ℕ, ∀ n : ℕ, Work.KMTAreas.A7.core ρ C₀ l₁ 0 k₁ k₂ a n ↔ m ≤ n := by
      refine ⟨Nat.find hex, fun n => ⟨fun h => ?_, fun h => ?_⟩⟩
      · by_contra hcon
        rw [not_le] at hcon
        exact Nat.find_min hex hcon h
      · exact Work.KMTAreas.A7.core_mono hamono h (Nat.find_spec hex)
    have hclip : ∀ x : ℤ, PointwiseErgodicTheorems.variationalNorm r
        (fun n : ℕ => if Work.KMTAreas.A7.core ρ C₀ l₁ 0 k₁ k₂ a n then
          Work.KMTAreas.A7.Tle ρ 0
            (Work.KMTAreas.A7.varphitildeNt P P.natDegree (Nat.floor (a n)) k₂ t) G x
          else 0)
        ≤ 2 * PointwiseErgodicTheorems.variationalNorm r
            (fun j : ℕ => Work.KMTAreas.A7.Tle ρ 0
              (Work.KMTAreas.A7.varphitildeNt P P.natDegree (Nat.floor (a (j + m))) k₂ t)
              G x) := by
      intro x
      have h1 := Work.KMTAreas.A7.variationalNorm_clip_tail_le (r := r) hr1 m
        (fun n : ℕ => Work.KMTAreas.A7.Tle ρ 0
          (Work.KMTAreas.A7.varphitildeNt P P.natDegree (Nat.floor (a n)) k₂ t) G x)
        (P := fun n : ℕ => Work.KMTAreas.A7.core ρ C₀ l₁ 0 k₁ k₂ a n) hm
      refine h1.trans (le_of_eq ?_)
      rw [two_mul]
    have hstep : MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
          (fun n : ℕ => if Work.KMTAreas.A7.core ρ C₀ l₁ 0 k₁ k₂ a n then
            Work.KMTAreas.A7.Tle ρ 0
              (Work.KMTAreas.A7.varphitildeNt P P.natDegree (Nat.floor (a n)) k₂ t) G x
            else 0)) 2 MeasureTheory.Measure.count
        ≤ 2 * MeasureTheory.eLpNorm (fun x : ℤ =>
            PointwiseErgodicTheorems.variationalNorm r
              (fun j : ℕ => Work.KMTAreas.A7.Tle ρ 0
                (Work.KMTAreas.A7.varphitildeNt P P.natDegree (Nat.floor (a (j + m))) k₂ t)
                G x)) 2 MeasureTheory.Measure.count :=
      MeasureTheory.eLpNorm_le_nnreal_smul_eLpNorm_of_ae_le_mul' (hf := by pw_aesm) (c := 2)
        (Filter.Eventually.of_forall (fun x => by
          rw [enorm_eq_self, enorm_eq_self]; exact hclip x)) 2
    have hcore_all : ∀ j : ℕ,
        Work.KMTAreas.A7.core ρ' C₀ 0 0 0 k₂ (fun j => a (j + m)) j := by
      intro j
      exact core_anti_bot hρ'nn hρ'leρ ((hm (j + m)).mpr (Nat.le_add_left m j))
    have ha' : PointwiseErgodicTheorems.Lacunary Λ (fun j : ℕ => a (j + m)) := by
      intro j
      have h := ha (j + m)
      have hidx : j + 1 + m = (j + m) + 1 := by omega
      show Λ < a (j + 1 + m) / a (j + m)
      rw [hidx]; exact h
    have hshift : MeasureTheory.eLpNorm (fun x : ℤ =>
          PointwiseErgodicTheorems.variationalNorm r
            (fun j : ℕ => Work.KMTAreas.A7.Tle ρ 0
              (Work.KMTAreas.A7.varphitildeNt P P.natDegree (Nat.floor (a (j + m))) k₂ t)
              G x)) 2 MeasureTheory.Measure.count
        ≤ ENNReal.ofReal (Clo Λ * Work.KMTAreas.A7.lossWeight 4 ρ' 0 0 0 k₂)
            * MeasureTheory.eLpNorm G 2 MeasureTheory.Measure.count := by
      have h2 := hClo_spec Λ hΛ (fun j : ℕ => a (j + m)) ha' (fun j => ha1 (j + m))
        0 0 0 k₂ t ht G
      have hfun : (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
            (fun n : ℕ => if Work.KMTAreas.A7.core ρ' C₀ 0 0 0 k₂ (fun j => a (j + m)) n then
              Work.KMTAreas.A7.Tle ρ' 0
                (Work.KMTAreas.A7.varphitildeNt P P.natDegree
                  (Nat.floor ((fun j => a (j + m)) n)) k₂ t) G x
              else 0))
          = (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
              (fun j : ℕ => Work.KMTAreas.A7.Tle ρ 0
                (Work.KMTAreas.A7.varphitildeNt P P.natDegree (Nat.floor (a (j + m))) k₂ t)
                G x)) := by
        funext x
        congr 1
        funext n
        rw [if_pos (hcore_all n)]
        exact congrFun (Tle_zero_rho_indep ρ' ρ _ G) x
      rw [hfun] at h2
      exact h2
    refine hstep.trans ?_
    calc (2 : ENNReal) * MeasureTheory.eLpNorm (fun x : ℤ =>
            PointwiseErgodicTheorems.variationalNorm r
              (fun j : ℕ => Work.KMTAreas.A7.Tle ρ 0
                (Work.KMTAreas.A7.varphitildeNt P P.natDegree (Nat.floor (a (j + m))) k₂ t)
                G x)) 2 MeasureTheory.Measure.count
        ≤ 2 * (ENNReal.ofReal (Clo Λ * Work.KMTAreas.A7.lossWeight 4 ρ' 0 0 0 k₂)
              * MeasureTheory.eLpNorm G 2 MeasureTheory.Measure.count) :=
          mul_le_mul' le_rfl hshift
      _ = ENNReal.ofReal (2 * (Clo Λ * Work.KMTAreas.A7.lossWeight 4 ρ' 0 0 0 k₂))
            * MeasureTheory.eLpNorm G 2 MeasureTheory.Measure.count := by
          rw [show (2 : ENNReal) * (ENNReal.ofReal (Clo Λ * Work.KMTAreas.A7.lossWeight 4 ρ' 0 0 0 k₂)
                * MeasureTheory.eLpNorm G 2 MeasureTheory.Measure.count)
              = (2 * ENNReal.ofReal (Clo Λ * Work.KMTAreas.A7.lossWeight 4 ρ' 0 0 0 k₂))
                * MeasureTheory.eLpNorm G 2 MeasureTheory.Measure.count from by ring,
            show (2 : ENNReal) = ENNReal.ofReal 2 from (ENNReal.ofReal_natCast 2).symm,
            ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
      _ ≤ ENNReal.ofReal (2 * (Clo Λ * Cw + 1)) * MeasureTheory.eLpNorm G 2 MeasureTheory.Measure.count := by
          refine mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl
          have hlwle := hlw k₂ hk₂B
          have hClo := (hClopos Λ hΛ).le
          nlinarith [hlwle, hClo, hCwnn]
  · -- the guard is empty, so the family vanishes
    have hzero : (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
          (fun n : ℕ => if Work.KMTAreas.A7.core ρ C₀ l₁ 0 k₁ k₂ a n then
            Work.KMTAreas.A7.Tle ρ 0
              (Work.KMTAreas.A7.varphitildeNt P P.natDegree (Nat.floor (a n)) k₂ t) G x
            else 0))
        = fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r (fun _ : ℕ => (0 : ℂ)) := by
      funext x
      congr 1
      funext n
      rw [if_neg (fun hc => hex ⟨n, hc⟩)]
    rw [hzero, Work.KMTAreas.A7.eLpNorm_variationalNorm_zero hr1 2]
    exact bot_le

end

end Work.KMTPlan.A6.LowModApproxBoundedH
