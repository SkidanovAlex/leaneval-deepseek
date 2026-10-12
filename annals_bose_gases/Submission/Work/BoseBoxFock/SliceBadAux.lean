import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.BoxFockDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.SliceBadAux` — the slot-count operators of the `ExcWindow` step 6

Vocabulary for `Work.BoseBoxFock.sliceBadCoeff_zero` (the BF3c step-6 lemma).  All three
operators are `ℂ`-valued slot sums of the complex slot mean `aPC` (`slotCountsComplex.lean`):

* `nPlusCSlice ℓ Ψ = Σ_{i : Fin n} (Ψ − aPC ℓ i Ψ)` — the complex excited-count operator `n₊`
  (renamed from `nPlusC` on 2026-10-09 to remove a duplicate-declaration clash with
  `Work.BoseBoxFock.nPlusC` of `KzOpC.lean`; the old name had no user outside this file);
* `nPlusPowC ℓ j` — its `j`-th iterate;
* `XS ℓ S Ψ = Σ_{i ∈ S} (Ψ − aPC ℓ i Ψ)` — the excited count on the slot set `S` (this is the
  operator whose sector form factorises over the complement configuration, `X_S` of
  `FINDING_BF3c_selection_s9.md` §2);
* `XSpow ℓ S j` — its `j`-th iterate.

No statements are proved here; the two analytic lemmas about them are
`Work.BoseBoxFock.sector_XSpow_le` (the moment bound) and the assembly in
`sliceBadCoeff_zero.lean`.
-/

noncomputable section

open MeasureTheory

namespace Work.BoseBoxFock

local notation "Sp" => EuclideanSpace ℝ (Fin 3)

/-- Scalar: if `conj c · c = (ℓ³)⁻¹` then `(conj c)⁻¹ = c·ℓ³`. -/
lemma conj_inv_eq_of_mul {ℓ : ℝ} (hℓ : 0 < ℓ) {c : ℂ}
    (hcstar : (starRingEnd ℂ) c * c = (((ℓ ^ 3 : ℝ)) : ℂ)⁻¹) :
    ((starRingEnd ℂ) c)⁻¹ = c * (((ℓ ^ 3 : ℝ)) : ℂ) := by
  have hℓ3 : (((ℓ ^ 3 : ℝ)) : ℂ) ≠ 0 := by
    simp only [Ne, Complex.ofReal_eq_zero]
    exact pow_ne_zero 3 (ne_of_gt hℓ)
  have hcc : (starRingEnd ℂ) c ≠ 0 := by
    intro h0; rw [h0, zero_mul] at hcstar
    exact (inv_ne_zero hℓ3) hcstar.symm
  have h2 : ((starRingEnd ℂ) c)⁻¹ * ((((ℓ ^ 3 : ℝ)) : ℂ))⁻¹ = c := by
    rw [← hcstar, ← mul_assoc, inv_mul_cancel₀ hcc, one_mul]
  have h4 := congrArg (fun z : ℂ => z * ((((ℓ ^ 3 : ℝ)) : ℂ))) h2
  rw [mul_assoc, inv_mul_cancel₀ hℓ3, mul_one] at h4
  exact h4

/-- **The cube mean of a pinned mode**: `(1/ℓ³)∫_{acube ℓ} e k = c·δ_{k0}` when `e 0 = c·θ_Λ`,
`|c|² = ℓ⁻³` and the modes are orthonormal. -/
lemma cubeMean_eq {ℓ : ℝ} (hℓ : 0 < ℓ) {m : ℕ} [NeZero m] {e : Fin m → Sp → ℂ} {c : ℂ}
    (he : ∀ l l', (∫ x : Sp, (starRingEnd ℂ) (e l x) * e l' x) = if l = l' then 1 else 0)
    (hcae : e 0 =ᵐ[(volume : Measure Sp)] fun x => c * Work.BoseK15.corpusBox.thetaFun ℓ x)
    (hcstar : (starRingEnd ℂ) c * c = (((ℓ ^ 3 : ℝ)) : ℂ)⁻¹) (k : Fin m) :
    (1 / ℓ ^ 3 : ℝ) * ∫ y in Submission.BoseGases.acube ℓ, e k y
      = c * (if k = 0 then 1 else 0) := by
  classical
  have hθ : Work.BoseK15.corpusBox.thetaFun ℓ
      = Set.indicator (Submission.BoseGases.acube ℓ) (fun _ => (1 : ℂ)) :=
    thetaFun_eq_indicator hℓ
  have hθconj : ∀ y : Sp, (starRingEnd ℂ) (Work.BoseK15.corpusBox.thetaFun ℓ y)
      = Set.indicator (Submission.BoseGases.acube ℓ) (fun _ => (1 : ℂ)) y := by
    intro y; rw [hθ]
    by_cases hy : y ∈ Submission.BoseGases.acube ℓ <;>
      simp [Set.indicator_of_mem, Set.indicator_of_notMem, hy]
  have hcne : (starRingEnd ℂ) c ≠ 0 := by
    intro h0; rw [h0, zero_mul] at hcstar
    have h3 : ((((ℓ ^ 3 : ℝ)) : ℂ))⁻¹ ≠ 0 :=
      inv_ne_zero (by simp only [Ne, Complex.ofReal_eq_zero]; exact pow_ne_zero 3 (ne_of_gt hℓ))
    exact h3 hcstar.symm
  -- `∫ conj (e 0) · e k = conj c · ∫_{acube} e k`
  have hkey : (∫ y : Sp, (starRingEnd ℂ) (e 0 y) * e k y)
      = (starRingEnd ℂ) c * ∫ y in Submission.BoseGases.acube ℓ, e k y := by
    have hpt : ∀ᵐ y ∂(volume : Measure Sp),
        (starRingEnd ℂ) (e 0 y) * e k y
          = (starRingEnd ℂ) c * (Set.indicator (Submission.BoseGases.acube ℓ)
              (fun y => e k y) y) := by
      filter_upwards [hcae] with y hy
      rw [hy, map_mul, hθconj y, mul_assoc]
      congr 1
      by_cases hyc : y ∈ Submission.BoseGases.acube ℓ <;>
        simp [Set.indicator_of_mem, Set.indicator_of_notMem, hyc]
    rw [MeasureTheory.integral_congr_ae hpt, MeasureTheory.integral_const_mul,
      MeasureTheory.integral_indicator (Submission.BoseGases.acube_measurable ℓ)]
  have hleft : (starRingEnd ℂ) c * (∫ y in Submission.BoseGases.acube ℓ, e k y)
      = (if k = 0 then 1 else 0) := by
    rw [← hkey, he 0 k]
    by_cases hk : k = 0
    · subst hk; simp
    · rw [if_neg (fun h : (0 : Fin m) = k => hk h.symm), if_neg hk]
  have hI : (∫ y in Submission.BoseGases.acube ℓ, e k y)
      = ((starRingEnd ℂ) c)⁻¹ * ((starRingEnd ℂ) c * ∫ y in Submission.BoseGases.acube ℓ, e k y) := by
    rw [← mul_assoc, inv_mul_cancel₀ hcne, one_mul]
  rw [hI, hleft]
  have hcs' := conj_inv_eq_of_mul hℓ hcstar
  have hAB : ((1 / ℓ ^ 3 : ℝ) : ℂ) * (((ℓ ^ 3 : ℝ)) : ℂ) = 1 := by
    rw [← Complex.ofReal_mul, one_div, inv_mul_cancel₀ (pow_ne_zero 3 (ne_of_gt hℓ)),
      Complex.ofReal_one]
  rw [hcs']
  by_cases hk : k = 0
  · simp only [hk, ↓reduceIte, mul_one, mul_comm c (((ℓ ^ 3 : ℝ)) : ℂ), ← mul_assoc,
      hAB, one_mul]
  · simp only [hk, ↓reduceIte, mul_zero]

/-- On the cube, the pinned mode is the constant `c` (a.e.). -/
lemma e0_ae_eq_c {ℓ : ℝ} (hℓ : 0 < ℓ) {m : ℕ} [NeZero m] {e : Fin m → Sp → ℂ} {c : ℂ}
    (hcae : e 0 =ᵐ[(volume : Measure Sp)] fun x => c * Work.BoseK15.corpusBox.thetaFun ℓ x) :
    ∀ᵐ y ∂((volume : Measure Sp).restrict (Submission.BoseGases.acube ℓ)), e 0 y = c := by
  have hθ : Work.BoseK15.corpusBox.thetaFun ℓ
      = Set.indicator (Submission.BoseGases.acube ℓ) (fun _ => (1 : ℂ)) :=
    thetaFun_eq_indicator hℓ
  have h2 : ∀ᵐ y ∂((volume : Measure Sp).restrict (Submission.BoseGases.acube ℓ)),
      e 0 y = c * Work.BoseK15.corpusBox.thetaFun ℓ y :=
    ae_mono MeasureTheory.Measure.restrict_le_self hcae
  filter_upwards [h2, self_mem_ae_restrict (Submission.BoseGases.acube_measurable ℓ)] with y hy hyc
  rw [hy, hθ, Set.indicator_of_mem hyc, mul_one]

/-- The complex excited-count operator `n₊ = Σ_i (1 − aPC_i)`. -/
noncomputable def nPlusCSlice {n : ℕ} (ℓ : ℝ) (Ψ : Submission.BoseGases.X n → ℂ) :
    Submission.BoseGases.X n → ℂ :=
  fun x => ∑ i : Fin n, (Ψ x - aPC ℓ i Ψ x)

/-- The iterates of the complex excited-count operator. -/
noncomputable def nPlusPowC {n : ℕ} (ℓ : ℝ) :
    ℕ → (Submission.BoseGases.X n → ℂ) → (Submission.BoseGases.X n → ℂ)
  | 0, Ψ => Ψ
  | (j + 1), Ψ => nPlusCSlice ℓ (nPlusPowC ℓ j Ψ)

/-- The excited count on the slot set `S`. -/
noncomputable def XS {n : ℕ} (ℓ : ℝ) (S : Finset (Fin n))
    (Ψ : Submission.BoseGases.X n → ℂ) : Submission.BoseGases.X n → ℂ :=
  fun x => ∑ i ∈ S, (Ψ x - aPC ℓ i Ψ x)

/-- The iterates of `XS`. -/
noncomputable def XSpow {n : ℕ} (ℓ : ℝ) (S : Finset (Fin n)) :
    ℕ → (Submission.BoseGases.X n → ℂ) → (Submission.BoseGases.X n → ℂ)
  | 0, Ψ => Ψ
  | (j + 1), Ψ => XS ℓ S (XSpow ℓ S j Ψ)

end Work.BoseBoxFock
