import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.FRK.lowBandDefs
import Submission.Work.BoseBoxFock.PotCubicLowBandAux.boxAnnOf_boxAnnOf_comm
import Submission.Work.BoseBoxFock.PotCubicLowBandAux.cIPn_boxAnnOf_self_pair
import Submission.Work.BoseBoxFock.PotCubicLowBandAux.slotBesselExcited
import Submission.Work.BoseBoxFock.sum_boxSlotOf_symm
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.PotCubicLowBandAux.lowBandChiAuxAux` — the structural lemmas of the χ-sum
(`lowBandChiSumAux`)

The target `lowBandChiSumAux` bounds the double χ-sum `Σ_k Σ_{k'} ‖a_{f k'} a_{f k} Θ‖²` by
`C_B² (𝓜+1) V` from the two count hypotheses `⟪Θ, S Θ⟫ ≤ V`, `⟪Θ, S² Θ⟫ ≤ 𝓜 V`, where
`S = boxSlotSum e (boxT0 m)` is the first-quantised excited number and `a_w = boxAnnOf e w ·`.

The bricks collected here (elementary consequences of the *proved* dictionary lemmas) are

* `boxAnnOf_eq_sum_smul` — `a_w` is the superposition of the mode-wise annihilations `a_{e_l}`;
* `sum_erase_rankOnePair_evec_eq_boxT0` — `Σ_{l ≠ 0} |e_l⟩⟨e_l| = boxT0 m`;
* `cIPn_boxSlotSum_boxT0_selfPair` — `⟪Ψ, S Ψ⟫ = Σ_{l ≠ 0} ‖a_{e_l} Ψ‖²`;
* `frameSum_le_excitedSum` — **Bessel for the χ-frame against the excited number operator**:
  for any state `Ψ` and any frame `{f_k}` with `f_k 0 = 0`,

      `Σ_k ‖a_{f k} Ψ‖² ≤ C_B Σ_{l ≠ 0} ‖a_{e_l} Ψ‖²`

  (`= C_B ⟪Ψ, S Ψ⟫` by the previous item), which is `slotBesselExcited` (proved) plus the three
  identities above.
-/

noncomputable section

open scoped BigOperators
open MeasureTheory

namespace Work.BoseBoxFock.PotCubicLowBandAux

open Work.BoseDict

set_option autoImplicit false
set_option linter.unusedVariables false

local notation "Ω" => EuclideanSpace ℝ (Fin 3)

/-! ## 0. Elementary auxiliary lemmas -/

/-- The continuous map `z ↦ Fin.cons z y` for a fixed `y`. -/
private theorem continuous_cons_fixed_local {d : ℕ} (y : Xn d) :
    Continuous (fun z : Ω => (Fin.cons z y : Xn (d + 1))) := by
  refine continuous_pi (fun i => ?_)
  refine Fin.cases ?_ (fun j => ?_) i
  · exact continuous_id
  · exact continuous_const

/-- `η` at a coordinate vector is the mode: `etaOf e (evec m l) = e l`. -/
private lemma etaOf_evec_local {m : ℕ} (e : Fin m → Ω → ℂ) (l : Fin m) :
    etaOf e (Work.BoseB4.evec m l) = e l := by
  funext z
  simp only [etaOf, Work.BoseB4.evec, Pi.single_apply]
  rw [Finset.sum_eq_single l]
  · simp
  · intro b _ hb; simp [hb]
  · intro h; exact absurd (Finset.mem_univ l) h

/-- The basis expansion: `Σ_l v_l • evec l = v`. -/
private lemma sum_smul_evec {m : ℕ} (v : Fin m → ℝ) :
    (∑ l : Fin m, v l • Work.BoseB4.evec m l) = v := by
  funext i
  rw [Finset.sum_apply, Finset.sum_eq_single i]
  · rw [Pi.smul_apply, Work.BoseB4.evec, Pi.single_eq_same, smul_eq_mul, mul_one]
  · intro b _ hb
    rw [Pi.smul_apply, Work.BoseB4.evec, Pi.single_apply,
      if_neg (by rintro rfl; exact hb rfl), smul_zero]
  · intro h; exact absurd (Finset.mem_univ i) h

/-- The sum of the coordinate rank-one operators is the identity. -/
private lemma sum_rankOnePair_evec_eq_one (m : ℕ) :
    (∑ l : Fin m, Work.BoseBoxFock.rankOnePair (Work.BoseB4.evec m l)
      (Work.BoseB4.evec m l)) = 1 := by
  refine LinearMap.ext fun v => ?_
  rw [LinearMap.sum_apply, Module.End.one_apply]
  refine Eq.trans ?_ (sum_smul_evec v)
  exact Finset.sum_congr rfl (fun x _ => by
    rw [Work.BoseBoxFock.rankOnePair_apply]
    congr 1
    rw [Finset.sum_eq_single x]
    · rw [Work.BoseB4.evec, Pi.single_eq_same, one_mul]
    · intro b _ hb
      rw [Work.BoseB4.evec, Pi.single_apply, if_neg hb, zero_mul]
    · intro h; exact absurd (Finset.mem_univ x) h)

/-- `boxT0 m = 1 − |eVec 0⟩⟨eVec 0|`. -/
private lemma boxT0_eq_one_sub_rankOne (m : ℕ) [NeZero m] :
    Work.BoseBoxFock.boxT0 m
      = 1 - Work.BoseBoxFock.rankOnePair (Work.BoseB4.evec m 0) (Work.BoseB4.evec m 0) := by
  refine LinearMap.ext fun v => ?_
  rw [LinearMap.sub_apply, Module.End.one_apply, Work.BoseBoxFock.boxT0_apply,
    Work.BoseBoxFock.rankOnePair_apply]
  congr 1
  rw [Finset.sum_eq_single (0 : Fin m)]
  · rw [Work.BoseB4.evec, Pi.single_eq_same, one_mul]
  · intro b _ hb
    rw [Work.BoseB4.evec, Pi.single_apply, if_neg hb, zero_mul]
  · intro h; exact absurd (Finset.mem_univ (0 : Fin m)) h

/-- **`boxSlotSum` is additive over finite sums of one-body operators.** -/
theorem boxSlotSum_finset_T_local {m d : ℕ} {e : Fin m → Ω → ℂ} {ι : Type*}
    (s : Finset ι) (A : ι → (Fin m → ℝ) →ₗ[ℝ] (Fin m → ℝ)) (Θ : Xn d → ℂ) :
    Work.BoseDict.boxSlotSum e (∑ l ∈ s, A l) Θ
      = ∑ l ∈ s, Work.BoseDict.boxSlotSum e (A l) Θ := by
  classical
  have hadd : ∀ T T' : (Fin m → ℝ) →ₗ[ℝ] (Fin m → ℝ),
      Work.BoseDict.boxSlotSum e (T + T') Θ
        = Work.BoseDict.boxSlotSum e T Θ + Work.BoseDict.boxSlotSum e T' Θ := by
    intro T T'
    funext x
    simp only [Work.BoseDict.boxSlotSum, Finset.sum_apply, LinearMap.add_apply, Pi.add_apply,
      Pi.smul_apply, Complex.real_smul, Complex.ofReal_add, add_mul, Finset.sum_add_distrib]
  induction s using Finset.induction with
  | empty =>
      funext x
      simp only [Finset.sum_empty, Work.BoseDict.boxSlotSum, Finset.sum_apply,
        LinearMap.zero_apply, Pi.zero_apply, zero_smul, Finset.sum_const_zero]
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, hadd, ih]

/-- The two boxes agree: `boxPow n ℓ = abox n ℓ` for `0 < ℓ`. -/
theorem boxPow_eq_aboxAux {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) :
    Work.MB.boxPow n ℓ = Submission.BoseGases.abox n ℓ := by
  rw [Work.MB.boxPow, Work.BoseBoxFock.boxL_eq_acube hℓ, ← Submission.BoseGases.abox_eq_pi_acube]

/-- The real part of the `n`-body pairing is the integral of the real part. -/
theorem cIPn_re_eq_integralAux {n : ℕ} {f g : Xn n → ℂ}
    (h : Integrable (fun x => star (f x) * g x)) :
    (Work.BoseDict.cIPn n f g).re = ∫ x, (star (f x) * g x).re := by
  rw [Work.BoseDict.cIPn]
  exact (ContinuousLinearMap.integral_comp_comm Complex.reCLM h).symm

/-- `star Θ · boxSlotSum e T Θ` is integrable at the weak bundle. -/
theorem integrable_star_boxSlotSumAux {m d : ℕ} {ℓ : ℝ} {e : Fin m → Ω → ℂ}
    (hmeas : ∀ l, Measurable (e l)) (hbdd : ∀ l, ∃ C : ℝ, ∀ x, ‖e l x‖ ≤ C)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    (T : (Fin m → ℝ) →ₗ[ℝ] (Fin m → ℝ)) {Θ : Xn d → ℂ}
    (hΘm : Measurable Θ) (hΘb : ∃ C : ℝ, ∀ x, ‖Θ x‖ ≤ C)
    (hΘsupp : Function.support Θ ⊆ Work.MB.boxPow d ℓ) :
    Integrable (fun x : Xn d => star (Θ x) * Work.BoseDict.boxSlotSum e T Θ x) := by
  obtain ⟨hSm, C₁, hC₁⟩ :=
    Work.MB.boxSlotSum_measurable_bounded_ae (d := d) hmeas hbdd hsupp T Θ hΘm hΘb
  obtain ⟨C₂, hC₂⟩ := hΘb
  refine Work.MB.integrable_of_bdd_of_support (S := Work.MB.boxPow d ℓ)
    (C := max C₂ 0 * max C₁ 0) (Work.MB.measurableSet_boxPow d ℓ)
    (Work.MB.volume_boxPow_lt_top d ℓ) ?_ ?_ ?_
  · exact ((Complex.continuous_conj.measurable.comp hΘm).mul hSm).aestronglyMeasurable
  · intro x
    rw [norm_mul, norm_star]
    exact mul_le_mul ((hC₂ x).trans (le_max_left _ _)) ((hC₁ x).trans (le_max_left _ _))
      (norm_nonneg _) (le_max_right _ _)
  · intro x hx
    have h0 : Θ x = 0 := Function.notMem_support.mp (fun h => hx (hΘsupp h))
    rw [h0, star_zero, zero_mul]

/-- The `cIPn` pairing is the `abox`-set integral of the real part (for `abox`-supported states). -/
theorem cIPn_re_eq_setIntegral_aboxAux {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {Θ X : Xn n → ℂ}
    (hΘm : Measurable Θ) (hΘb : ∃ C : ℝ, ∀ x, ‖Θ x‖ ≤ C)
    (hΘsupp : Function.support Θ ⊆ Work.MB.boxPow n ℓ)
    (hXm : Measurable X) (hXb : ∃ C : ℝ, ∀ x, ‖X x‖ ≤ C) :
    (Work.BoseDict.cIPn n Θ X).re
      = ∫ x in Submission.BoseGases.abox n ℓ, (star (Θ x) * X x).re := by
  obtain ⟨C₁, hC₁⟩ := hΘb
  obtain ⟨C₂, hC₂⟩ := hXb
  have hInt : Integrable (fun x : Xn n => star (Θ x) * X x) := by
    refine Work.MB.integrable_of_bdd_of_support (S := Work.MB.boxPow n ℓ)
      (C := max C₁ 0 * max C₂ 0) (Work.MB.measurableSet_boxPow n ℓ)
      (Work.MB.volume_boxPow_lt_top n ℓ) ?_ ?_ ?_
    · exact ((Complex.continuous_conj.measurable.comp hΘm).mul hXm).aestronglyMeasurable
    · intro x
      rw [norm_mul, norm_star]
      exact mul_le_mul ((hC₁ x).trans (le_max_left _ _)) ((hC₂ x).trans (le_max_left _ _))
        (norm_nonneg _) (le_max_right _ _)
    · intro x hx
      have h0 : Θ x = 0 := Function.notMem_support.mp (fun h => hx (hΘsupp h))
      rw [h0, star_zero, zero_mul]
  have hsupp : Function.support (fun x : Xn n => (star (Θ x) * X x).re)
      ⊆ Submission.BoseGases.abox n ℓ := by
    intro x hx
    by_contra hxab
    refine hx ?_
    have h0 : Θ x = 0 := by
      by_contra h
      exact hxab (by rw [← boxPow_eq_aboxAux hℓ]; exact hΘsupp (Function.mem_support.mpr h))
    simp [h0]
  rw [cIPn_re_eq_integralAux hInt]
  exact (setIntegral_eq_integral_of_support_subset (Submission.BoseGases.abox_measurable n ℓ)
    hsupp).symm

/-! ## 1. `a_w` is the superposition of the mode-wise annihilations -/

/-- **Linearity of the superposition annihilation in its weight vector.** -/
theorem boxAnnOf_eq_sum_smul {m d : ℕ} {ℓ : ℝ} {e : Fin m → Ω → ℂ}
    (hmeas : ∀ l, Measurable (e l)) (hbdd : ∀ l, ∃ C : ℝ, ∀ x, ‖e l x‖ ≤ C)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    (w : Fin m → ℝ) {Θ : Xn (d + 1) → ℂ} (hΘm : Measurable Θ)
    (hΘb : ∃ C : ℝ, ∀ x, ‖Θ x‖ ≤ C) (hΘsupp : Function.support Θ ⊆ Work.MB.boxPow (d + 1) ℓ) :
    boxAnnOf e w d Θ = ∑ l : Fin m, (w l) • boxAnnOf e (Work.BoseB4.evec m l) d Θ := by
  funext y
  have hint : ∀ l : Fin m, Integrable (fun z : Ω => star (e l z) * Θ (Fin.cons z y)) := by
    intro l
    obtain ⟨C, hC⟩ := hbdd l
    obtain ⟨C', hC'⟩ := hΘb
    refine Work.MB.integrable_of_bdd_of_support
      (S := Work.BoseK15.corpusBox.boxL ℓ) (C := max C 0 * max C' 0)
      (Work.BoseK15.corpusBox.boxL_measurableSet ℓ)
      (Work.BoseK15.corpusBox.boxL_compact ℓ).measure_lt_top.ne
      (((Complex.continuous_conj.measurable.comp (hmeas l)).mul
        (hΘm.comp (continuous_cons_fixed_local y).measurable)).aestronglyMeasurable) ?_ ?_
    · intro z
      rw [norm_mul, norm_star]
      exact mul_le_mul ((hC z).trans (le_max_left _ _)) ((hC' _).trans (le_max_left _ _))
        (norm_nonneg _) (le_max_right _ _)
    · intro z hz
      have hz0 : e l z = 0 := Function.notMem_support.mp (fun h => hz (hsupp l h))
      simp [hz0]
  have hstareta : ∀ z : Ω, star (etaOf e w z)
      = ∑ l : Fin m, ((w l : ℝ) : ℂ) * star (e l z) := by
    intro z
    simp only [etaOf]
    simp
  have hsplit : (∫ z : Ω, (∑ l : Fin m, ((w l : ℝ) : ℂ) * star (e l z)) * Θ (Fin.cons z y))
      = ∑ l : Fin m, ((w l : ℝ) : ℂ) * ∫ z : Ω, star (e l z) * Θ (Fin.cons z y) := by
    have hcongr : (fun z : Ω => (∑ l : Fin m, ((w l : ℝ) : ℂ) * star (e l z))
          * Θ (Fin.cons z y))
        = fun z : Ω => ∑ l : Fin m, ((w l : ℝ) : ℂ) * (star (e l z) * Θ (Fin.cons z y)) := by
      funext z
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl (fun l _ => by ring)
    rw [hcongr, integral_finsetSum _ (fun l _ => (hint l).const_mul _)]
    exact Finset.sum_congr rfl (fun l _ => integral_const_mul _ _)
  have hmain : (∫ z : Ω, star (etaOf e w z) * Θ (Fin.cons z y))
      = ∑ l : Fin m, ((w l : ℝ) : ℂ) * ∫ z : Ω, star (e l z) * Θ (Fin.cons z y) := by
    have h1 : (fun z : Ω => star (etaOf e w z) * Θ (Fin.cons z y))
        = (fun z : Ω => (∑ l : Fin m, ((w l : ℝ) : ℂ) * star (e l z)) * Θ (Fin.cons z y)) := by
      funext z
      rw [hstareta z]
    rw [h1]
    exact hsplit
  simp only [boxAnnOf, Finset.sum_apply, Pi.smul_apply, Complex.real_smul, starRingEnd_apply,
    etaOf_evec_local]
  rw [hmain, Finset.mul_sum]
  exact Finset.sum_congr rfl (fun l _ => by ring)

/-! ## 2. `Σ_{l ≠ 0} |e_l⟩⟨e_l| = boxT0 m` -/

/-- **The excited projection is the sum of the excited coordinate rank-one operators.** -/
theorem sum_erase_rankOnePair_evec_eq_boxT0 {m : ℕ} [NeZero m] :
    (∑ l ∈ Finset.univ.erase (0 : Fin m),
        Work.BoseBoxFock.rankOnePair (Work.BoseB4.evec m l) (Work.BoseB4.evec m l))
      = Work.BoseBoxFock.boxT0 m := by
  rw [boxT0_eq_one_sub_rankOne m, ← sum_rankOnePair_evec_eq_one m,
    Finset.sum_erase_eq_sub (Finset.mem_univ (0 : Fin m))]

/-! ## 3. `⟪Ψ, S Ψ⟫ = Σ_{l ≠ 0} ‖a_{e_l} Ψ‖²` -/

/-- **The self-pairing of the first-quantised excited number is the sum of the squared norms of
the mode-wise annihilations.** -/
theorem cIPn_boxSlotSum_boxT0_selfPair {m d : ℕ} [NeZero m] {ℓ : ℝ} {e : Fin m → Ω → ℂ}
    (hmeas : ∀ l, Measurable (e l)) (hbdd : ∀ l, ∃ C : ℝ, ∀ x, ‖e l x‖ ≤ C)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    (hMemLp : ∀ l, MeasureTheory.MemLp (e l) ⊤)
    {Ψ : Xn (d + 1) → ℂ} (hΨm : Measurable Ψ) {CΨ : ℝ} (hΨb : ∀ x, ‖Ψ x‖ ≤ CΨ)
    (hΨsupp : Function.support Ψ ⊆ Work.MB.boxPow (d + 1) ℓ)
    (hΨsym : ∀ (σ : Equiv.Perm (Fin (d + 1))) (x : Xn (d + 1)), Ψ (x ∘ σ) = Ψ x) :
    (Work.BoseDict.cIPn (d + 1) Ψ
        (Work.BoseDict.boxSlotSum e (Work.BoseBoxFock.boxT0 m) Ψ)).re
      = ∑ l ∈ Finset.univ.erase (0 : Fin m),
          (Work.BoseDict.cIPn d (Work.BoseDict.boxAnnOf e (Work.BoseB4.evec m l) d Ψ)
            (Work.BoseDict.boxAnnOf e (Work.BoseB4.evec m l) d Ψ)).re := by
  have hS0 : Work.BoseDict.boxSlotSum e (Work.BoseBoxFock.boxT0 m) Ψ
      = ∑ l ∈ Finset.univ.erase (0 : Fin m),
          Work.BoseDict.boxSlotSum e
            (Work.BoseBoxFock.rankOnePair (Work.BoseB4.evec m l) (Work.BoseB4.evec m l)) Ψ := by
    rw [← sum_erase_rankOnePair_evec_eq_boxT0 (m := m)]
    exact boxSlotSum_finset_T_local _ _ Ψ
  have hS : Work.BoseDict.boxSlotSum e (Work.BoseBoxFock.boxT0 m) Ψ
      = ∑ l ∈ Finset.univ.erase (0 : Fin m), (1 : ℝ) •
          Work.BoseDict.boxSlotSum e
            (Work.BoseBoxFock.rankOnePair (Work.BoseB4.evec m l) (Work.BoseB4.evec m l)) Ψ := by
    rw [hS0]
    exact Finset.sum_congr rfl (fun l _ => by rw [one_smul])
  have hint : ∀ l ∈ (Finset.univ.erase (0 : Fin m)),
      Integrable (fun x : Xn (d + 1) => star (Ψ x) *
        Work.BoseDict.boxSlotSum e
          (Work.BoseBoxFock.rankOnePair (Work.BoseB4.evec m l) (Work.BoseB4.evec m l)) Ψ x) :=
    fun l _ => integrable_star_boxSlotSumAux hmeas hbdd hsupp _ hΨm ⟨CΨ, hΨb⟩ hΨsupp
  rw [hS, FRK.cIPn_sum_smul _ (fun _ => (1 : ℝ)) hint]
  simp only [Complex.ofReal_one, one_mul, Complex.re_sum]
  exact Finset.sum_congr rfl (fun l _ => (congrArg Complex.re
    (cIPn_boxAnnOf_self_pair hmeas hbdd hsupp hMemLp (Work.BoseB4.evec m l)
      (Work.BoseB4.evec m l) hΨm hΨb hΨsupp hΨsym)).symm)

/-! ## 4. Bessel for the χ-frame against the excited number operator -/

/-- The squared norm of a weakly regular box state is integrable. -/
private lemma integrable_normSq_wregG {n : ℕ} {ℓ : ℝ} {f : Xn n → ℂ}
    (hfm : Measurable f) (hfb : ∃ C : ℝ, ∀ x, ‖f x‖ ≤ C)
    (hfs : Function.support f ⊆ Work.MB.boxPow n ℓ) :
    Integrable (fun x : Xn n => ‖f x‖ ^ 2) := by
  obtain ⟨C, hC⟩ := hfb
  have hIntC : Integrable (fun x : Xn n => ((‖f x‖ ^ 2 : ℝ) : ℂ)) := by
    refine Work.MB.integrable_of_bdd_of_support (S := Work.MB.boxPow n ℓ)
      (C := (max C 0) ^ 2) (Work.MB.measurableSet_boxPow n ℓ)
      (Work.MB.volume_boxPow_lt_top n ℓ) ?_ ?_ ?_
    · exact (Complex.continuous_ofReal.measurable.comp (hfm.norm.pow_const 2)).aestronglyMeasurable
    · intro x
      have h1 : ‖((‖f x‖ ^ 2 : ℝ) : ℂ)‖ = ‖f x‖ ^ 2 := by
        simp
      rw [h1]
      exact pow_le_pow_left₀ (norm_nonneg _) ((hC x).trans (le_max_left _ _)) 2
    · intro x hx
      have h0 : f x = 0 := Function.notMem_support.mp (fun h => hx (hfs h))
      rw [h0]
      simp
  simpa only [Complex.reCLM_apply, Complex.ofReal_re] using Complex.reCLM.integrable_comp hIntC

/-- **The χ-Bessel inequality.**  For a frame `{f_k}` of box modes orthogonal to the condensate
(`f k 0 = 0`), the sum of the squared norms of the box annihilations is bounded by `C_B` times
the sum of the squared norms of the excited mode-wise annihilations:

    `Σ_k ‖a_{f k} Ψ‖² ≤ C_B Σ_{l ≠ 0} ‖a_{e_l} Ψ‖²`.

The proof is the pointwise frame inequality `frame_complex` at the vector
`u_l = (a_{e_l} Ψ)(y)` (using `boxAnnOf_eq_sum_smul` to write `a_{f k} Ψ = Σ_l (f k)_l a_{e_l} Ψ`),
integrated in `y`. -/
theorem frameSum_le_excitedSum {m d : ℕ} [NeZero m] {ℓ : ℝ}
    {e : Fin m → Ω → ℂ}
    (hmeas : ∀ l, Measurable (e l)) (hbdd : ∀ l, ∃ C : ℝ, ∀ x, ‖e l x‖ ≤ C)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    (horth : ∀ l l', (∫ z : Ω, star (e l z) * e l' z) = (if l = l' then (1 : ℂ) else 0))
    (hMemLp : ∀ l, MeasureTheory.MemLp (e l) ⊤)
    {ι : Type*} [Fintype ι] [DecidableEq ι] (f : ι → Fin m → ℝ) (C_B : ℝ) (hC_B : 0 ≤ C_B)
    (hframe : ∀ w : Fin m → ℝ,
      ∑ k : ι, (Work.BoseB4.gram (f k) w) ^ 2 ≤ C_B * ∑ l : Fin m, (w l) ^ 2)
    (h0 : ∀ k : ι, f k 0 = 0)
    {Ψ : Xn (d + 1) → ℂ} (hΨm : Measurable Ψ) {CΨ : ℝ} (hΨb : ∀ x, ‖Ψ x‖ ≤ CΨ)
    (hΨsupp : Function.support Ψ ⊆ Work.MB.boxPow (d + 1) ℓ)
    (hΨsym : ∀ (σ : Equiv.Perm (Fin (d + 1))) (x : Xn (d + 1)), Ψ (x ∘ σ) = Ψ x) :
    (∑ k : ι, (Work.BoseDict.cIPn d (Work.BoseDict.boxAnnOf e (f k) d Ψ)
        (Work.BoseDict.boxAnnOf e (f k) d Ψ)).re)
      ≤ C_B * ∑ l ∈ Finset.univ.erase (0 : Fin m),
          (Work.BoseDict.cIPn d (Work.BoseDict.boxAnnOf e (Work.BoseB4.evec m l) d Ψ)
            (Work.BoseDict.boxAnnOf e (Work.BoseB4.evec m l) d Ψ)).re := by
  -- the mode-wise annihilations are weakly regular
  have hW : ∀ w : Fin m → ℝ, Work.BoseBoxFock.WRegG ℓ (Work.BoseDict.boxAnnOf e w d Ψ) :=
    fun w => boxAnnOf_wregG hmeas hbdd hsupp w ⟨hΨm, ⟨CΨ, hΨb⟩, hΨsupp⟩
  have hintW : ∀ w : Fin m → ℝ, Integrable (fun y : Xn d => ‖(Work.BoseDict.boxAnnOf e w d Ψ) y‖ ^ 2) :=
    fun w => integrable_normSq_wregG (hW w).meas (hW w).bdd (hW w).supp
  -- (i) the pointwise frame inequality
  have hpoint : ∀ y : Xn d, ∑ k : ι, ‖(Work.BoseDict.boxAnnOf e (f k) d Ψ) y‖ ^ 2
      ≤ C_B * ∑ l ∈ Finset.univ.erase (0 : Fin m),
          ‖(Work.BoseDict.boxAnnOf e (Work.BoseB4.evec m l) d Ψ) y‖ ^ 2 := by
    intro y
    have h1 : ∀ k : ι, (Work.BoseDict.boxAnnOf e (f k) d Ψ) y
        = ∑ l : Fin m, (((f k) l : ℝ) : ℂ)
            * (Work.BoseDict.boxAnnOf e (Work.BoseB4.evec m l) d Ψ) y := by
      intro k
      rw [congrFun (boxAnnOf_eq_sum_smul hmeas hbdd hsupp (f k) hΨm ⟨CΨ, hΨb⟩ hΨsupp) y,
        Finset.sum_apply]
      exact Finset.sum_congr rfl (fun l _ => by rw [Pi.smul_apply, Complex.real_smul])
    calc ∑ k : ι, ‖(Work.BoseDict.boxAnnOf e (f k) d Ψ) y‖ ^ 2
        = ∑ k : ι, ‖∑ l : Fin m, (((f k) l : ℝ) : ℂ)
            * (Work.BoseDict.boxAnnOf e (Work.BoseB4.evec m l) d Ψ) y‖ ^ 2 :=
          Finset.sum_congr rfl (fun k _ => by rw [h1 k])
      _ ≤ C_B * ∑ l ∈ Finset.univ.erase (0 : Fin m),
            ‖(Work.BoseDict.boxAnnOf e (Work.BoseB4.evec m l) d Ψ) y‖ ^ 2 :=
          frame_complex f C_B hframe h0
            (fun l => (Work.BoseDict.boxAnnOf e (Work.BoseB4.evec m l) d Ψ) y)
  -- (ii) both sides as integrals of the squared norms
  have hIntL : Integrable (fun y : Xn d => ∑ k : ι,
      ‖(Work.BoseDict.boxAnnOf e (f k) d Ψ) y‖ ^ 2) :=
    integrable_finsetSum _ (fun k _ => hintW (f k))
  have hIntR : Integrable (fun y : Xn d => C_B * ∑ l ∈ Finset.univ.erase (0 : Fin m),
      ‖(Work.BoseDict.boxAnnOf e (Work.BoseB4.evec m l) d Ψ) y‖ ^ 2) :=
    (integrable_finsetSum _ (fun l _ => hintW (Work.BoseB4.evec m l))).const_mul C_B
  have hL : (∑ k : ι, (Work.BoseDict.cIPn d (Work.BoseDict.boxAnnOf e (f k) d Ψ)
        (Work.BoseDict.boxAnnOf e (f k) d Ψ)).re)
      = ∫ y : Xn d, ∑ k : ι, ‖(Work.BoseDict.boxAnnOf e (f k) d Ψ) y‖ ^ 2 := by
    rw [Finset.sum_congr rfl (fun k _ => Work.BoseBoxFock.cIPn_self_re _)]
    exact (integral_finsetSum _ (fun k _ => hintW (f k))).symm
  have hR : (∑ l ∈ Finset.univ.erase (0 : Fin m),
        (Work.BoseDict.cIPn d (Work.BoseDict.boxAnnOf e (Work.BoseB4.evec m l) d Ψ)
          (Work.BoseDict.boxAnnOf e (Work.BoseB4.evec m l) d Ψ)).re)
      = ∫ y : Xn d, ∑ l ∈ Finset.univ.erase (0 : Fin m),
          ‖(Work.BoseDict.boxAnnOf e (Work.BoseB4.evec m l) d Ψ) y‖ ^ 2 := by
    rw [Finset.sum_congr rfl (fun l _ => Work.BoseBoxFock.cIPn_self_re _)]
    exact (integral_finsetSum _ (fun l _ => hintW (Work.BoseB4.evec m l))).symm
  calc (∑ k : ι, (Work.BoseDict.cIPn d (Work.BoseDict.boxAnnOf e (f k) d Ψ)
        (Work.BoseDict.boxAnnOf e (f k) d Ψ)).re)
      = ∫ y : Xn d, ∑ k : ι, ‖(Work.BoseDict.boxAnnOf e (f k) d Ψ) y‖ ^ 2 := hL
    _ ≤ ∫ y : Xn d, C_B * ∑ l ∈ Finset.univ.erase (0 : Fin m),
          ‖(Work.BoseDict.boxAnnOf e (Work.BoseB4.evec m l) d Ψ) y‖ ^ 2 :=
        integral_mono hIntL hIntR hpoint
    _ = C_B * ∫ y : Xn d, ∑ l ∈ Finset.univ.erase (0 : Fin m),
          ‖(Work.BoseDict.boxAnnOf e (Work.BoseB4.evec m l) d Ψ) y‖ ^ 2 :=
        integral_const_mul C_B _
    _ = C_B * ∑ l ∈ Finset.univ.erase (0 : Fin m),
          (Work.BoseDict.cIPn d (Work.BoseDict.boxAnnOf e (Work.BoseB4.evec m l) d Ψ)
            (Work.BoseDict.boxAnnOf e (Work.BoseB4.evec m l) d Ψ)).re := by rw [hR]

/-- `star Θ · boxSlotSum e T Ψ` is integrable when the bra `Θ` is bounded and box-supported
and the slot sum is bounded (with an arbitrary state `Ψ`). -/
theorem integrable_star_mul_boxSlotSumAux {m d : ℕ} {ℓ : ℝ} {e : Fin m → Ω → ℂ}
    (hmeas : ∀ l, Measurable (e l)) (hbdd : ∀ l, ∃ C : ℝ, ∀ x, ‖e l x‖ ≤ C)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    (T : (Fin m → ℝ) →ₗ[ℝ] (Fin m → ℝ)) {Ψ : Xn d → ℂ}
    (hΨm : Measurable Ψ) (hΨb : ∃ C : ℝ, ∀ x, ‖Ψ x‖ ≤ C)
    (hΨsupp : Function.support Ψ ⊆ Work.MB.boxPow d ℓ)
    {Θ : Xn d → ℂ} (hΘm : Measurable Θ) (hΘb : ∃ C : ℝ, ∀ x, ‖Θ x‖ ≤ C)
    (hΘsupp : Function.support Θ ⊆ Work.MB.boxPow d ℓ) :
    Integrable (fun x : Xn d => star (Θ x) * Work.BoseDict.boxSlotSum e T Ψ x) := by
  obtain ⟨hSm, C₁, hC₁⟩ :=
    Work.MB.boxSlotSum_measurable_bounded_ae (d := d) hmeas hbdd hsupp T Ψ hΨm hΨb
  obtain ⟨C₂, hC₂⟩ := hΘb
  refine Work.MB.integrable_of_bdd_of_support (S := Work.MB.boxPow d ℓ)
    (C := max C₂ 0 * max C₁ 0) (Work.MB.measurableSet_boxPow d ℓ)
    (Work.MB.volume_boxPow_lt_top d ℓ) ?_ ?_ ?_
  · exact ((Complex.continuous_conj.measurable.comp hΘm).mul hSm).aestronglyMeasurable
  · intro x
    rw [norm_mul, norm_star]
    exact mul_le_mul ((hC₂ x).trans (le_max_left _ _)) ((hC₁ x).trans (le_max_left _ _))
      (norm_nonneg _) (le_max_right _ _)
  · intro x hx
    have h0 : Θ x = 0 := Function.notMem_support.mp (fun h => hx (hΘsupp h))
    rw [h0, star_zero, zero_mul]

/-! ## 5. Support and symmetry of the slot sums (needed to apply the mixed adjointness) -/

/-- `η_w` is supported in the one-particle box. -/
theorem etaOf_support {m : ℕ} {ℓ : ℝ} {e : Fin m → Ω → ℂ}
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ) (w : Fin m → ℝ) :
    Function.support (etaOf e w) ⊆ Work.BoseK15.corpusBox.boxL ℓ := by
  intro z hz
  by_contra hzbox
  refine hz ?_
  simp only [etaOf]
  refine Finset.sum_eq_zero (fun l _ => ?_)
  have h0 : e l z = 0 := Function.notMem_support.mp (fun h => hzbox (hsupp l h))
  rw [h0, mul_zero]

/-- A single slot operator preserves the box support of the state. -/
theorem boxSlotOf_support {m d : ℕ} {ℓ : ℝ} {e : Fin m → Ω → ℂ} {w v : Fin m → ℝ}
    (hw : Function.support (etaOf e w) ⊆ Work.BoseK15.corpusBox.boxL ℓ) (j : Fin d)
    {Ψ : Xn d → ℂ} (hΨsupp : Function.support Ψ ⊆ Work.MB.boxPow d ℓ) :
    Function.support (Work.BoseDict.boxSlotOf e w v j Ψ) ⊆ Work.MB.boxPow d ℓ := by
  intro x hx
  by_contra hxbox
  have hcoord : ∃ i : Fin d, x i ∉ Work.BoseK15.corpusBox.boxL ℓ := by
    by_contra h
    refine hxbox ?_
    rw [Work.MB.boxPow]
    exact fun i _ => not_not.mp (fun hi => h ⟨i, hi⟩)
  obtain ⟨i, hi⟩ := hcoord
  by_cases hij : i = j
  · subst hij
    refine hx ?_
    have h0 : etaOf e w (x i) = 0 := Function.notMem_support.mp (fun h => hi (hw h))
    change etaOf e w (x i)
      * (∫ z : Ω, (starRingEnd ℂ) (etaOf e v z) * Ψ (Function.update x i z)) = 0
    rw [h0, zero_mul]
  · refine hx ?_
    have h2 : (∫ z : Ω, (starRingEnd ℂ) (etaOf e v z) * Ψ (Function.update x j z)) = 0 := by
      refine integral_eq_zero_of_ae ?_
      filter_upwards with z
      have hzi : (Function.update x j z) i = x i := by
        rw [Function.update_apply, if_neg (by rintro rfl; exact hij rfl)]
      have hz0 : Ψ (Function.update x j z) = 0 := by
        refine Function.notMem_support.mp (fun hmem => ?_)
        have hmem' := hΨsupp hmem
        rw [Work.MB.boxPow] at hmem'
        exact hi (hzi ▸ hmem' i (Set.mem_univ i))
      simp only [hz0, mul_zero, Pi.zero_apply]
    change etaOf e w (x j)
      * (∫ z : Ω, (starRingEnd ℂ) (etaOf e v z) * Ψ (Function.update x j z)) = 0
    rw [h2, mul_zero]

/-- The first-quantised slot sum preserves the box support of the state. -/
theorem boxSlotSum_support {m d : ℕ} {ℓ : ℝ} {e : Fin m → Ω → ℂ}
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    (T : (Fin m → ℝ) →ₗ[ℝ] (Fin m → ℝ)) {Ψ : Xn d → ℂ}
    (hΨsupp : Function.support Ψ ⊆ Work.MB.boxPow d ℓ) :
    Function.support (Work.BoseDict.boxSlotSum e T Ψ) ⊆ Work.MB.boxPow d ℓ := by
  intro x hx
  by_contra hxbox
  refine hx ?_
  have hfull : ∀ T' : (Fin m → ℝ) →ₗ[ℝ] (Fin m → ℝ), Work.BoseDict.boxSlotSum e T' Ψ x = 0 := by
    intro T'
    rw [Work.BoseDict.boxSlotSum, Finset.sum_apply]
    refine Finset.sum_eq_zero (fun j _ => ?_)
    rw [Finset.sum_apply]
    refine Finset.sum_eq_zero (fun l _ => ?_)
    rw [Finset.sum_apply]
    refine Finset.sum_eq_zero (fun l' _ => ?_)
    have h0 : Work.BoseDict.boxSlotOf e (Work.BoseB4.evec m l) (Work.BoseB4.evec m l') j Ψ x = 0 :=
      Function.notMem_support.mp (fun hmem =>
        hxbox (boxSlotOf_support (etaOf_support hsupp (Work.BoseB4.evec m l)) j hΨsupp hmem))
    rw [Pi.smul_apply, h0, smul_zero]
  exact hfull T

/-- **The excited number operator preserves symmetry.** -/
theorem boxSlotSum_boxT0_symm {m d : ℕ} [NeZero m] {e : Fin m → Ω → ℂ}
    {Ψ : Xn (d + 1) → ℂ}
    (hΨm : Measurable Ψ) (hΨb : ∃ C : ℝ, ∀ x, ‖Ψ x‖ ≤ C)
    (hΨsym : ∀ (σ : Equiv.Perm (Fin (d + 1))) (x : Xn (d + 1)), Ψ (x ∘ σ) = Ψ x) :
    ∀ (σ : Equiv.Perm (Fin (d + 1))) (x : Xn (d + 1)),
      Work.BoseDict.boxSlotSum e (Work.BoseBoxFock.boxT0 m) Ψ (x ∘ σ)
        = Work.BoseDict.boxSlotSum e (Work.BoseBoxFock.boxT0 m) Ψ x := by
  have hslot : ∀ j : Fin (d + 1), slotJ e (Work.BoseBoxFock.boxT0 m) j Ψ
      = ∑ l ∈ Finset.univ.erase (0 : Fin m),
          Work.BoseDict.boxSlotOf e (Work.BoseB4.evec m l) (Work.BoseB4.evec m l) j Ψ := by
    intro j
    rw [slotJ_boxT0]
    funext x
    rw [Finset.sum_apply]
    exact Finset.sum_congr rfl (fun l _ => by
      simp only [Work.BoseDict.boxSlotOf, etaOf_evec_local, starRingEnd_apply])
  have hS1 : Work.BoseDict.boxSlotSum e (Work.BoseBoxFock.boxT0 m) Ψ
      = ∑ l ∈ Finset.univ.erase (0 : Fin m),
          ∑ j : Fin (d + 1), Work.BoseDict.boxSlotOf e (Work.BoseB4.evec m l)
            (Work.BoseB4.evec m l) j Ψ := by
    rw [boxSlotSum_eq_sum_slotJ, Finset.sum_congr rfl (fun j _ => hslot j), Finset.sum_comm]
  intro σ x
  rw [hS1, Finset.sum_apply, Finset.sum_apply]
  refine Finset.sum_congr rfl (fun l _ => ?_)
  exact Work.BoseBoxFock.sum_boxSlotOf_symm (e := e) (Work.BoseB4.evec m l)
    (Work.BoseB4.evec m l) Ψ hΨsym σ x

end Work.BoseBoxFock.PotCubicLowBandAux
