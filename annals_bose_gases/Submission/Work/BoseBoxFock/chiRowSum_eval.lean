import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.chiRow_muEvalAux
import Submission.Work.BoseBoxFock.chiRow_pairSlot_split
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseBoxFock

noncomputable section

open scoped BigOperators
open MeasureTheory

local notation "Sp" => EuclideanSpace ℝ (Fin 3)

open Submission.BoseGases

set_option linter.unusedVariables false

/-!
# `Work.BoseBoxFock.chiRowSum_eval` — the six-term assembly of the `Q₁` `χ`-row

The FS `Q₁` `χ`-row on the box is evaluated against the *linear combination*

  `a₁ • W₁ − b₁ • W₂ + a₁ • W₃ − b₁ • W₄ + a₂ • W₅ + a₂ • W₆`

of six first-quantised slot words (`W₁`, `W₃` = the two orientations of the pair row at the
pinned `χ`-mode, `W₂`, `W₄` = the two orientations of its `μ`-line, `W₅`, `W₆` = the two
orientations of the `χ²`-row at the pinned `θ`-mode).  Each of the six individual pairings is the
content of a separate row lemma; this module performs the *assembly*: `cIPn` is real-linear in its
second slot, so the pairing of the combination is the combination of the pairings, and the real
part of a real-linear combination of complex pairings is the real-linear combination of their real
parts.  The two `μ`-line orientations are combined with `muForm` and each pair of orientations with
`pairSlot = pairHalfOne + pairHalfTwo`.

## Contents

* `integrable_conj_boxRestrictC_mul` — the Bochner integrability of `conj (boxRestrictC ℓ Φ) · G`
  for a measurable, bounded `G` (the box restriction is bounded and supported in the finite-measure
  box);
* `cIPn_sum_smul`, `cIPn_lin6`, `re_six` — the (real-)linearity toolbox of `cIPn`;
* `chiCube_abs_le`, `thetaExp_measurable_box`, `thetaTail_measurable_box`, `thW_measurable_box`,
  `chiW_abs_bound`, `thW_abs_bound` — measurability and global boundedness of the two row weights
  `chiW` and `thW` (the inputs of `chiRow_pairSlot_split` at those weights).
-/

/-! ## 1. Integrability of the pairing against the box restriction -/

/-- **Integrability of `conj (boxRestrictC ℓ Φ) · G`.**  The box restriction is measurable,
bounded and supported in the finite-measure box `abox n ℓ`, so the product with any measurable
bounded `G` is Bochner integrable. -/
theorem integrable_conj_boxRestrictC_mul {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ)
    {Φ : Submission.BoseGases.X n → ℝ} (hΦc : Continuous Φ) {G : Submission.BoseGases.X n → ℂ}
    (hGm : Measurable G) (hGb : ∃ C, ∀ x, ‖G x‖ ≤ C) :
    Integrable (fun x => (starRingEnd ℂ) (boxRestrictC ℓ Φ x) * G x) := by
  obtain ⟨CΦ, hCΦ0, hCΦ⟩ := boxRestrictC_norm_bound hℓ hΦc
  obtain ⟨CG, hCG⟩ := hGb
  refine Work.MB.integrable_of_bdd_of_support (S := Submission.BoseGases.abox n ℓ)
    (Submission.BoseGases.abox_measurable n ℓ)
    (ne_of_lt (Submission.BoseGases.abox_lt_top n ℓ hℓ.le)) ?_ (C := CΦ * CG) ?_ ?_
  · exact ((Complex.continuous_conj.measurable.comp
      (boxRestrictC_measurable ℓ hΦc)).mul hGm).aestronglyMeasurable
  · intro x
    rw [norm_mul, Complex.norm_conj]
    exact mul_le_mul (hCΦ x) (hCG x) (norm_nonneg _) hCΦ0
  · intro x hx
    have h0 : boxRestrictC ℓ Φ x = 0 :=
      Function.notMem_support.mp (fun h => hx (boxRestrictC_support_subset ℓ Φ h))
    rw [h0, map_zero, zero_mul]

/-! ## 2. Real-linearity of `cIPn` in its second slot -/

/-- **`cIPn` is real-linear on finite sums of real multiples.** -/
theorem cIPn_sum_smul {n : ℕ} {ι : Type*} (s : Finset ι) (c : ι → ℝ)
    (f : Submission.BoseGases.X n → ℂ) (G : ι → Submission.BoseGases.X n → ℂ)
    (h : ∀ i ∈ s, Integrable (fun x => (starRingEnd ℂ) (f x) * G i x)) :
    Work.BoseDict.cIPn n f (∑ i ∈ s, c i • G i)
      = ∑ i ∈ s, (c i : ℂ) * Work.BoseDict.cIPn n f (G i) := by
  rw [Work.BoseDict.cIPn]
  have hpt : (fun x => (starRingEnd ℂ) (f x) * (∑ i ∈ s, c i • G i) x)
      = fun x => ∑ i ∈ s, (c i : ℂ) * ((starRingEnd ℂ) (f x) * G i x) := by
    funext x
    rw [Finset.sum_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Pi.smul_apply, Complex.real_smul]
    ring
  rw [hpt, MeasureTheory.integral_finsetSum _
    (fun i hi => (h i hi).const_mul ((c i : ℂ)))]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [MeasureTheory.integral_const_mul, Work.BoseDict.cIPn]

/-- **The six-term linearity of `cIPn` in its second slot.** -/
theorem cIPn_lin6 {n : ℕ} (f G1 G2 G3 G4 G5 G6 : Submission.BoseGases.X n → ℂ)
    (c1 c2 c3 c4 c5 c6 : ℝ)
    (h1 : Integrable fun x => (starRingEnd ℂ) (f x) * G1 x)
    (h2 : Integrable fun x => (starRingEnd ℂ) (f x) * G2 x)
    (h3 : Integrable fun x => (starRingEnd ℂ) (f x) * G3 x)
    (h4 : Integrable fun x => (starRingEnd ℂ) (f x) * G4 x)
    (h5 : Integrable fun x => (starRingEnd ℂ) (f x) * G5 x)
    (h6 : Integrable fun x => (starRingEnd ℂ) (f x) * G6 x) :
    Work.BoseDict.cIPn n f (c1 • G1 - c2 • G2 + c3 • G3 - c4 • G4 + c5 • G5 + c6 • G6)
      = (c1 : ℂ) * Work.BoseDict.cIPn n f G1 - (c2 : ℂ) * Work.BoseDict.cIPn n f G2
        + (c3 : ℂ) * Work.BoseDict.cIPn n f G3 - (c4 : ℂ) * Work.BoseDict.cIPn n f G4
        + (c5 : ℂ) * Work.BoseDict.cIPn n f G5
        + (c6 : ℂ) * Work.BoseDict.cIPn n f G6 := by
  have hexp : c1 • G1 - c2 • G2 + c3 • G3 - c4 • G4 + c5 • G5 + c6 • G6
      = ∑ i : Fin 6, ![c1, -c2, c3, -c4, c5, c6] i • ![G1, G2, G3, G4, G5, G6] i := by
    rw [Fin.sum_univ_six]
    simp only [Matrix.cons_val, neg_smul]
    abel
  rw [hexp, cIPn_sum_smul Finset.univ _ _ _ (fun i _ => ?_)]
  · rw [Fin.sum_univ_six]
    simp only [Matrix.cons_val]
    push_cast
    ring
  · fin_cases i <;> assumption

/-- **The real part of a real-linear combination of six complex numbers.** -/
theorem re_six (Z1 Z2 Z3 Z4 Z5 Z6 : ℂ) (c1 c2 c3 c4 c5 c6 : ℝ) :
    ((c1 : ℂ) * Z1 - (c2 : ℂ) * Z2 + (c3 : ℂ) * Z3 - (c4 : ℂ) * Z4
        + (c5 : ℂ) * Z5 + (c6 : ℂ) * Z6).re
      = c1 * Z1.re - c2 * Z2.re + c3 * Z3.re - c4 * Z4.re + c5 * Z5.re + c6 * Z6.re := by
  simp only [Complex.sub_re, Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero]

/-! ## 3. Measurability and boundedness of the two row weights -/

/-- `|χ_Λ² − 1| ≤ √(48/π)² + 1`. -/
lemma chiCube_abs_le (ℓ : ℝ) (x : Sp) :
    |chiCube ℓ x| ≤ Real.sqrt (48 / Real.pi) ^ 2 + 1 := by
  have h1 : |Work.BoseK15.corpusBox.chiLam ℓ x ^ 2| ≤ Real.sqrt (48 / Real.pi) ^ 2 := by
    rw [abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) (chiLam_abs_le ℓ x) 2
  calc |chiCube ℓ x| = |Work.BoseK15.corpusBox.chiLam ℓ x ^ 2 - 1| := rfl
    _ ≤ |Work.BoseK15.corpusBox.chiLam ℓ x ^ 2| + |(1 : ℝ)| := abs_sub _ _
    _ ≤ Real.sqrt (48 / Real.pi) ^ 2 + 1 := by
        rw [abs_one]
        exact add_le_add h1 le_rfl

/-- The `θ`-mode `e^{i⟪s,·⟫}θ_Λ` is measurable. -/
lemma thetaExp_measurable_box (ℓ : ℝ) (s : Sp) :
    Measurable (Work.BoseK15.corpusBox.thetaExp ℓ s) := by
  have h1 : Continuous (fun z : Sp =>
      Complex.exp (Complex.I * ((inner ℝ s z : ℝ) : ℂ))) :=
    Complex.continuous_exp.comp (continuous_const.mul
      (Complex.continuous_ofReal.comp (Continuous.inner continuous_const continuous_id)))
  rw [show Work.BoseK15.corpusBox.thetaExp ℓ s
      = fun z : Sp => Complex.exp (Complex.I * ((inner ℝ s z : ℝ) : ℂ)) *
          Work.BoseK15.corpusBox.thetaFun ℓ z from
    funext fun z => Work.BoseB4.BoxData.thetaExp_apply _ _ _ _]
  exact h1.measurable.mul (thetaFun_measurable ℓ)

/-- The `χ²`-row truncation tail `thetaTail` is measurable. -/
lemma thetaTail_measurable_box (ℓ : ℝ) (N : ℕ) : Measurable (thetaTail ℓ N) := by
  unfold thetaTail
  refine (((chiLamC_measurable ℓ).pow_const 2).sub (thetaFun_measurable ℓ)).sub ?_
  exact Finset.measurable_sum (Finset.univ.filter (fun s : Lab N => s ≠ 0))
    (fun s _ => measurable_const.mul (thetaExp_measurable_box ℓ (kmomLab ℓ N s)))

/-- The `χ²`-row weight `thW` is measurable. -/
lemma thW_measurable_box (ℓ : ℝ) (N : ℕ) : Measurable (thW ℓ N) := by
  have h : thW ℓ N = fun x : Sp => chiCube ℓ x - (thetaTail ℓ N x).re := rfl
  rw [h]
  exact (chiCube_measurable ℓ).sub
    (Complex.continuous_re.measurable.comp (thetaTail_measurable_box ℓ N))

/-- **The `χ`-row weight is globally bounded** (uniformly in `ℓ`, `N`): `chiW = χ_Λ² − 1 − Re χ̂`,
with `χ_Λ` bounded by `√(48/π)` and the tail bounded by `chiTail_bound 0`. -/
lemma chiW_abs_bound {ℓ : ℝ} (hℓ : 0 < ℓ) (N : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ x : Sp, |chiW ℓ N x| ≤ K := by
  obtain ⟨Cχ, hCχ0, hCχ⟩ := chiTail_bound 0
  refine ⟨Real.sqrt (48 / Real.pi) ^ 2 + 1 + Cχ, by positivity, fun x => ?_⟩
  have h2 : |(chiTail ℓ N x).re| ≤ Cχ := by
    refine (Complex.abs_re_le_norm _).trans ?_
    have h := hCχ ℓ hℓ N x
    simpa using h
  calc |chiW ℓ N x| = |chiCube ℓ x - (chiTail ℓ N x).re| := rfl
    _ ≤ |chiCube ℓ x| + |(chiTail ℓ N x).re| := abs_sub _ _
    _ ≤ Real.sqrt (48 / Real.pi) ^ 2 + 1 + Cχ := add_le_add (chiCube_abs_le ℓ x) h2

/-- **The `χ²`-row weight is globally bounded** (uniformly in `ℓ`, `N`):
`thW = χ_Λ² − 1 − Re θ̂`, with the tail bounded by `thetaTail_bound 0`. -/
lemma thW_abs_bound {ℓ : ℝ} (hℓ : 0 < ℓ) (N : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ x : Sp, |thW ℓ N x| ≤ K := by
  obtain ⟨Cθ, hCθ0, hCθ⟩ := thetaTail_bound 0
  refine ⟨Real.sqrt (48 / Real.pi) ^ 2 + 1 + Cθ, by positivity, fun x => ?_⟩
  have h2 : |(thetaTail ℓ N x).re| ≤ Cθ := by
    refine (Complex.abs_re_le_norm _).trans ?_
    have h := hCθ ℓ hℓ N x
    simpa using h
  calc |thW ℓ N x| = |chiCube ℓ x - (thetaTail ℓ N x).re| := rfl
    _ ≤ |chiCube ℓ x| + |(thetaTail ℓ N x).re| := abs_sub _ _
    _ ≤ Real.sqrt (48 / Real.pi) ^ 2 + 1 + Cθ := add_le_add (chiCube_abs_le ℓ x) h2

/-! ## 4. The assembly -/

theorem chiRowSum_eval {n m : ℕ} [NeZero m] {ℓ : ℝ} (hℓ : 0 < ℓ) {N : ℕ}
    {e : Fin m → EuclideanSpace ℝ (Fin 3) → ℂ} {C C' : Fin m → ℝ}
    {Φ : Submission.BoseGases.X n → ℝ} (hΦc : Continuous Φ)
    (hmeas : ∀ l, Measurable (e l)) (hemem : ∀ l, MeasureTheory.MemLp (e l) ⊤)
    (hbdd : ∀ l, ∃ D : ℝ, ∀ x, ‖e l x‖ ≤ D)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    (h1 : (Work.BoseDict.cIPn n (Work.BoseBoxFock.boxRestrictC ℓ Φ)
        (Work.BoseDict.boxSlotSum e (Work.BoseBoxFock.rankOne (Work.BoseBoxFock.evec0 m))
          (Work.BoseDict.boxSlotSum e (Work.BoseBoxFock.rankOnePair C (Work.BoseBoxFock.evec0 m))
            (Work.BoseBoxFock.boxRestrictC ℓ Φ)))).re
      = Work.BoseBoxFock.pairHalfOne n ℓ (Work.BoseBoxFock.chiW ℓ N) Φ)
    (h3 : (Work.BoseDict.cIPn n (Work.BoseBoxFock.boxRestrictC ℓ Φ)
        (Work.BoseDict.boxSlotSum e (Work.BoseBoxFock.rankOnePair (Work.BoseBoxFock.evec0 m) C)
          (Work.BoseDict.boxSlotSum e (Work.BoseBoxFock.rankOne (Work.BoseBoxFock.evec0 m))
            (Work.BoseBoxFock.boxRestrictC ℓ Φ)))).re
      = Work.BoseBoxFock.pairHalfTwo n ℓ (Work.BoseBoxFock.chiW ℓ N) Φ)
    (h2 : (Work.BoseDict.cIPn n (Work.BoseBoxFock.boxRestrictC ℓ Φ)
        (Work.BoseDict.boxSlotSum e (Work.BoseBoxFock.rankOnePair C (Work.BoseBoxFock.evec0 m))
          (Work.BoseBoxFock.boxRestrictC ℓ Φ))).re
      + (Work.BoseDict.cIPn n (Work.BoseBoxFock.boxRestrictC ℓ Φ)
        (Work.BoseDict.boxSlotSum e (Work.BoseBoxFock.rankOnePair (Work.BoseBoxFock.evec0 m) C)
          (Work.BoseBoxFock.boxRestrictC ℓ Φ))).re
      = Work.BoseBoxFock.muForm n ℓ (Work.BoseBoxFock.chiW ℓ N) Φ)
    (h4 : (Work.BoseDict.cIPn n (Work.BoseBoxFock.boxRestrictC ℓ Φ)
        (Work.BoseDict.boxSlotSum e (Work.BoseBoxFock.rankOne (Work.BoseBoxFock.evec0 m))
          (Work.BoseDict.boxSlotSum e (Work.BoseBoxFock.rankOnePair C' (Work.BoseBoxFock.evec0 m))
            (Work.BoseBoxFock.boxRestrictC ℓ Φ)))).re
      = Work.BoseBoxFock.pairHalfOne n ℓ (Work.BoseBoxFock.thW ℓ N) Φ)
    (h5 : (Work.BoseDict.cIPn n (Work.BoseBoxFock.boxRestrictC ℓ Φ)
        (Work.BoseDict.boxSlotSum e (Work.BoseBoxFock.rankOnePair (Work.BoseBoxFock.evec0 m) C')
          (Work.BoseDict.boxSlotSum e (Work.BoseBoxFock.rankOne (Work.BoseBoxFock.evec0 m))
            (Work.BoseBoxFock.boxRestrictC ℓ Φ)))).re
      = Work.BoseBoxFock.pairHalfTwo n ℓ (Work.BoseBoxFock.thW ℓ N) Φ)
    (a1 b1 a2 : ℝ) :
    (Work.BoseDict.cIPn n (Work.BoseBoxFock.boxRestrictC ℓ Φ)
      (a1 • (Work.BoseDict.boxSlotSum e (Work.BoseBoxFock.rankOne (Work.BoseBoxFock.evec0 m))
              (Work.BoseDict.boxSlotSum e (Work.BoseBoxFock.rankOnePair C (Work.BoseBoxFock.evec0 m))
                (Work.BoseBoxFock.boxRestrictC ℓ Φ)))
        - b1 • (Work.BoseDict.boxSlotSum e (Work.BoseBoxFock.rankOnePair C (Work.BoseBoxFock.evec0 m))
              (Work.BoseBoxFock.boxRestrictC ℓ Φ))
        + a1 • (Work.BoseDict.boxSlotSum e (Work.BoseBoxFock.rankOnePair (Work.BoseBoxFock.evec0 m) C)
              (Work.BoseDict.boxSlotSum e (Work.BoseBoxFock.rankOne (Work.BoseBoxFock.evec0 m))
                (Work.BoseBoxFock.boxRestrictC ℓ Φ)))
        - b1 • (Work.BoseDict.boxSlotSum e (Work.BoseBoxFock.rankOnePair (Work.BoseBoxFock.evec0 m) C)
              (Work.BoseBoxFock.boxRestrictC ℓ Φ))
        + a2 • (Work.BoseDict.boxSlotSum e (Work.BoseBoxFock.rankOne (Work.BoseBoxFock.evec0 m))
              (Work.BoseDict.boxSlotSum e (Work.BoseBoxFock.rankOnePair C' (Work.BoseBoxFock.evec0 m))
                (Work.BoseBoxFock.boxRestrictC ℓ Φ)))
        + a2 • (Work.BoseDict.boxSlotSum e (Work.BoseBoxFock.rankOnePair (Work.BoseBoxFock.evec0 m) C')
              (Work.BoseDict.boxSlotSum e (Work.BoseBoxFock.rankOne (Work.BoseBoxFock.evec0 m))
                (Work.BoseBoxFock.boxRestrictC ℓ Φ))))).re
      = a1 * Work.BoseBoxFock.pairSlot n ℓ (Work.BoseBoxFock.chiW ℓ N) Φ
        - b1 * Work.BoseBoxFock.muForm n ℓ (Work.BoseBoxFock.chiW ℓ N) Φ
        + a2 * Work.BoseBoxFock.pairSlot n ℓ (Work.BoseBoxFock.thW ℓ N) Φ := by
  -- ## the box restriction is a good state
  have hfm : Measurable (boxRestrictC ℓ Φ) := boxRestrictC_measurable ℓ hΦc
  obtain ⟨Cf, -, hCf⟩ := boxRestrictC_norm_bound hℓ hΦc
  have hfb : ∃ K : ℝ, ∀ x, ‖boxRestrictC ℓ Φ x‖ ≤ K := ⟨Cf, hCf⟩
  -- ## measurability and boundedness of the six slot words (and their inner slots)
  obtain ⟨hBm, hBb⟩ := Work.MB.boxSlotSum_measurable_bounded_ae (d := n) hmeas hbdd hsupp
    (rankOnePair C (evec0 m)) (boxRestrictC ℓ Φ) hfm hfb
  obtain ⟨hIm, hIb⟩ := Work.MB.boxSlotSum_measurable_bounded_ae (d := n) hmeas hbdd hsupp
    (rankOne (evec0 m)) (boxRestrictC ℓ Φ) hfm hfb
  obtain ⟨hJm, hJb⟩ := Work.MB.boxSlotSum_measurable_bounded_ae (d := n) hmeas hbdd hsupp
    (rankOnePair C' (evec0 m)) (boxRestrictC ℓ Φ) hfm hfb
  obtain ⟨hAm, hAb⟩ := Work.MB.boxSlotSum_measurable_bounded_ae (d := n) hmeas hbdd hsupp
    (rankOne (evec0 m))
    (Work.BoseDict.boxSlotSum e (rankOnePair C (evec0 m)) (boxRestrictC ℓ Φ)) hBm hBb
  obtain ⟨hCm, hCb⟩ := Work.MB.boxSlotSum_measurable_bounded_ae (d := n) hmeas hbdd hsupp
    (rankOnePair (evec0 m) C)
    (Work.BoseDict.boxSlotSum e (rankOne (evec0 m)) (boxRestrictC ℓ Φ)) hIm hIb
  obtain ⟨hDm, hDb⟩ := Work.MB.boxSlotSum_measurable_bounded_ae (d := n) hmeas hbdd hsupp
    (rankOnePair (evec0 m) C) (boxRestrictC ℓ Φ) hfm hfb
  obtain ⟨hEm, hEb⟩ := Work.MB.boxSlotSum_measurable_bounded_ae (d := n) hmeas hbdd hsupp
    (rankOne (evec0 m))
    (Work.BoseDict.boxSlotSum e (rankOnePair C' (evec0 m)) (boxRestrictC ℓ Φ)) hJm hJb
  obtain ⟨hFm, hFb⟩ := Work.MB.boxSlotSum_measurable_bounded_ae (d := n) hmeas hbdd hsupp
    (rankOnePair (evec0 m) C')
    (Work.BoseDict.boxSlotSum e (rankOne (evec0 m)) (boxRestrictC ℓ Φ)) hIm hIb
  -- ## integrability of the six pairings
  have hiA := integrable_conj_boxRestrictC_mul hℓ hΦc hAm hAb
  have hiB := integrable_conj_boxRestrictC_mul hℓ hΦc hBm hBb
  have hiC := integrable_conj_boxRestrictC_mul hℓ hΦc hCm hCb
  have hiD := integrable_conj_boxRestrictC_mul hℓ hΦc hDm hDb
  have hiE := integrable_conj_boxRestrictC_mul hℓ hΦc hEm hEb
  have hiF := integrable_conj_boxRestrictC_mul hℓ hΦc hFm hFb
  -- ## the linearity of `cIPn` in the second slot
  rw [cIPn_lin6 (boxRestrictC ℓ Φ)
    (Work.BoseDict.boxSlotSum e (rankOne (evec0 m))
      (Work.BoseDict.boxSlotSum e (rankOnePair C (evec0 m)) (boxRestrictC ℓ Φ)))
    (Work.BoseDict.boxSlotSum e (rankOnePair C (evec0 m)) (boxRestrictC ℓ Φ))
    (Work.BoseDict.boxSlotSum e (rankOnePair (evec0 m) C)
      (Work.BoseDict.boxSlotSum e (rankOne (evec0 m)) (boxRestrictC ℓ Φ)))
    (Work.BoseDict.boxSlotSum e (rankOnePair (evec0 m) C) (boxRestrictC ℓ Φ))
    (Work.BoseDict.boxSlotSum e (rankOne (evec0 m))
      (Work.BoseDict.boxSlotSum e (rankOnePair C' (evec0 m)) (boxRestrictC ℓ Φ)))
    (Work.BoseDict.boxSlotSum e (rankOnePair (evec0 m) C')
      (Work.BoseDict.boxSlotSum e (rankOne (evec0 m)) (boxRestrictC ℓ Φ)))
    a1 b1 a1 b1 a2 a2 hiA hiB hiC hiD hiE hiF]
  -- ## the real part of the combination
  rw [re_six]
  -- ## the five row hypotheses
  rw [h1, h3, h4, h5, ← h2]
  -- ## the two `pairSlot`s are the sums of their orientations
  obtain ⟨Kχ, -, hχbnd⟩ := chiW_abs_bound hℓ N
  obtain ⟨Kθ, -, hθbnd⟩ := thW_abs_bound hℓ N
  rw [(chiRow_pairSlot_split hℓ hΦc (chiW_measurable ℓ N) hχbnd).1,
    (chiRow_pairSlot_split hℓ hΦc (thW_measurable_box ℓ N) hθbnd).1]
  ring

end

end Work.BoseBoxFock
