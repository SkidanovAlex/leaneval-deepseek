import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Star.Real
import Submission.Commons.Combinatorics.Transference.avg_tau_dot

set_option linter.unusedVariables false

open Finset

namespace Commons.Combinatorics.Transference

/-- Coefficient vector of the linear form
`h ↦ (∑ i, (if ω' i then h i else 0)) - (∑ i, (if ω i then h i else 0))`. -/
private def linCoef {p d : ℕ} (ω ω' : Fin d → Bool) : Fin d → ZMod p :=
  fun j => (if ω' j then (1 : ZMod p) else 0) - (if ω j then (1 : ZMod p) else 0)

private lemma linform_eq {p : ℕ} {d : ℕ} (ω ω' : Fin d → Bool) (h : Fin d → ZMod p) :
    (∑ i, (if ω' i then h i else 0)) - (∑ i, (if ω i then h i else 0))
      = ∑ j, linCoef ω ω' j * h j := by
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  simp only [linCoef]
  cases h1 : ω' i <;> cases h2 : ω i <;> simp_all

private lemma linCoef_exists {p : ℕ} [Fact p.Prime] {d : ℕ} (ω ω' : Fin d → Bool)
    (hne : ω ≠ ω') : ∃ j, linCoef (p := p) ω ω' j ≠ 0 := by
  by_contra hc
  simp only [not_exists, not_not] at hc
  apply hne
  funext j
  have hj := hc j
  simp only [linCoef] at hj
  cases h1 : ω j <;> cases h2 : ω' j <;> simp_all

/-- The `(ω, ω')`-term of the inner double sum (zero on the diagonal). -/
private def aval {p d : ℕ} (τ : ZMod p → ℝ) (x : (Fin d → Bool) × (Fin d → Bool))
    (h : Fin d → ZMod p) : ℝ :=
  if x.1 = x.2 then 0 else τ (∑ j, linCoef x.1 x.2 j * h j)

/-- Power-mean + Fubini: given the per-term bound `P⁻¹ ∑_h a x h ^ K ≤ Cm` for every `x`,
the average of `(∑_x a x h)^K` is bounded by `(card ι)^K * Cm`. -/
theorem pow_sum_avg_bound {ι H : Type*} [Fintype ι] [Fintype H]
    (a : ι → H → ℝ) (ha : ∀ x h, 0 ≤ a x h) {P Cm : ℝ} (hP : 0 < P)
    {K : ℕ} (hK : 1 ≤ K)
    (hpair : ∀ x, P⁻¹ * ∑ h, (a x h) ^ K ≤ Cm) :
    P⁻¹ * ∑ h, (∑ x, a x h) ^ K ≤ (Fintype.card ι : ℝ) ^ K * Cm := by
  obtain ⟨K', rfl⟩ : ∃ K', K = K' + 1 := ⟨K - 1, by omega⟩
  have hpow : ∀ h, (∑ x, a x h) ^ (K' + 1)
      ≤ (Fintype.card ι : ℝ) ^ K' * ∑ x, (a x h) ^ (K' + 1) := by
    intro h
    have := pow_sum_le_card_mul_sum_pow (s := (Finset.univ : Finset ι))
      (f := fun x => a x h) (fun x _ => ha x h) K'
    simpa using this
  have e1 : (∑ h, ((Fintype.card ι : ℝ) ^ K' * ∑ x, (a x h) ^ (K' + 1)))
      = (Fintype.card ι : ℝ) ^ K' * ∑ h, (∑ x, (a x h) ^ (K' + 1)) := by
    rw [← Finset.mul_sum]
  have e2 : (∑ h, (∑ x, (a x h) ^ (K' + 1))) = ∑ x, ∑ h, (a x h) ^ (K' + 1) :=
    Finset.sum_comm
  have e3 : (∑ x, (P⁻¹ * ∑ h, (a x h) ^ (K' + 1)))
      = P⁻¹ * ∑ x, (∑ h, (a x h) ^ (K' + 1)) := by
    rw [← Finset.mul_sum]
  calc P⁻¹ * ∑ h, (∑ x, a x h) ^ (K' + 1)
      ≤ P⁻¹ * ∑ h, ((Fintype.card ι : ℝ) ^ K' * ∑ x, (a x h) ^ (K' + 1)) := by
        gcongr with h
        exact hpow h
    _ = (Fintype.card ι : ℝ) ^ K' * ∑ x, (P⁻¹ * ∑ h, (a x h) ^ (K' + 1)) := by
        rw [e1, e2, e3]; ring
    _ ≤ (Fintype.card ι : ℝ) ^ K' * ∑ x, Cm := by
        gcongr with x
        exact hpair x
    _ = (Fintype.card ι : ℝ) ^ (K' + 1) * Cm := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, pow_succ]
        ring

theorem avg_H_pair_bound {p : ℕ} [Fact p.Prime] {d K : ℕ} (hd : 1 ≤ d) {τ : ZMod p → ℝ}
    (hτ : ∀ x, 0 ≤ τ x) {Cm : ℝ}
    (hmom : (Fintype.card (ZMod p) : ℝ)⁻¹ * ∑ y : ZMod p, τ y ^ K ≤ Cm) :
    ((Fintype.card (ZMod p) : ℝ) ^ d)⁻¹ *
      ∑ h : Fin d → ZMod p,
        (∑ ω : Fin d → Bool, ∑ ω' ∈ Finset.univ.filter (fun ω' => ω ≠ ω'),
          τ ((∑ i, (if ω' i then h i else 0)) - (∑ i, (if ω i then h i else 0)))) ^ K
      ≤ ((2 ^ d * 2 ^ d : ℕ) : ℝ) ^ K * Cm := by
  classical
  have hcard_pos : 0 < (Fintype.card (ZMod p) : ℝ) := by
    rw [ZMod.card]
    exact_mod_cast (Fact.out : p.Prime).pos
  have hcard_ne : (Fintype.card (ZMod p) : ℝ) ≠ 0 := ne_of_gt hcard_pos
  have hcardfun : (Fintype.card (Fin d → ZMod p) : ℝ) = (Fintype.card (ZMod p) : ℝ) ^ d := by
    rw [Fintype.card_fun, Fintype.card_fin, Nat.cast_pow]
  have hcardι :
      (Fintype.card ((Fin d → Bool) × (Fin d → Bool)) : ℝ) = ((2 ^ d * 2 ^ d : ℕ) : ℝ) := by
    simp only [Fintype.card_prod, Fintype.card_fun, Fintype.card_fin, Fintype.card_bool]

  have ha_nonneg : ∀ x : (Fin d → Bool) × (Fin d → Bool),
      ∀ h : Fin d → ZMod p, 0 ≤ aval τ x h := by
    rintro ⟨ω, ω'⟩ h
    simp only [aval]
    split_ifs with hne
    · exact le_refl 0
    · exact hτ _
  have hsum_id : ∀ h : Fin d → ZMod p,
      (∑ x : (Fin d → Bool) × (Fin d → Bool), aval τ x h)
        = ∑ ω : Fin d → Bool, ∑ ω' ∈ Finset.univ.filter (fun ω' => ω ≠ ω'),
          τ ((∑ i, (if ω' i then h i else 0)) - (∑ i, (if ω i then h i else 0))) := by
    intro h
    rw [Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro ω _
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro ω' _
    by_cases hne : ω ≠ ω'
    · have haux : aval τ (ω, ω') h = τ (∑ j, linCoef ω ω' j * h j) := by
        simp only [aval]
        rw [if_neg hne]
      rw [haux, if_pos hne, linform_eq]
    · have haux : aval τ (ω, ω') h = 0 := by
        simp only [aval]
        rw [if_pos (not_not.mp hne)]
      rw [haux, if_neg hne]
  have hgoal : (∑ h : Fin d → ZMod p,
        (∑ ω : Fin d → Bool, ∑ ω' ∈ Finset.univ.filter (fun ω' => ω ≠ ω'),
          τ ((∑ i, (if ω' i then h i else 0)) - (∑ i, (if ω i then h i else 0)))) ^ K)
      = ∑ h : Fin d → ZMod p,
          (∑ x : (Fin d → Bool) × (Fin d → Bool), aval τ x h) ^ K := by
    apply Finset.sum_congr rfl
    intro h _
    rw [hsum_id h]
  rw [hgoal]
  rcases K with _ | K'
  · -- K = 0
    have hthis : ((Fintype.card (ZMod p) : ℝ) ^ d)⁻¹ *
        ∑ h : Fin d → ZMod p, (∑ x : (Fin d → Bool) × (Fin d → Bool), aval τ x h) ^ 0
        = 1 := by
      have h1 : (∑ h : Fin d → ZMod p, (1 : ℝ)) = (Fintype.card (Fin d → ZMod p) : ℝ) := by simp
      simp only [pow_zero]
      rw [h1, hcardfun, inv_mul_cancel₀ (pow_ne_zero d hcard_ne)]
    have hCm : 1 ≤ Cm := by
      have h1 : (∑ y : ZMod p, (τ y) ^ 0) = (Fintype.card (ZMod p) : ℝ) := by simp
      have := hmom
      rw [h1, inv_mul_cancel₀ hcard_ne] at this
      exact this
    rw [hthis]
    simpa using hCm
  · -- K = K' + 1
    have hPpos : 0 < (Fintype.card (ZMod p) : ℝ) ^ d := pow_pos hcard_pos d
    have hKpos : 1 ≤ K' + 1 := Nat.le_add_left 1 K'
    have hCm_nonneg : 0 ≤ Cm := by
      have h1 : (0 : ℝ) ≤ (Fintype.card (ZMod p) : ℝ)⁻¹ * ∑ y : ZMod p, τ y ^ (K' + 1) := by
        apply mul_nonneg (inv_nonneg.mpr hcard_pos.le)
        apply Finset.sum_nonneg
        intro y _
        exact pow_nonneg (hτ y) _
      linarith [hmom]
    have hpair : ∀ x : (Fin d → Bool) × (Fin d → Bool),
        ((Fintype.card (ZMod p) : ℝ) ^ d)⁻¹ *
          ∑ h, (aval τ x h) ^ (K' + 1) ≤ Cm := by
      rintro ⟨ω, ω'⟩
      by_cases hne : ω = ω'
      · have hazero : ∀ h, aval τ (ω, ω') h = 0 := by
          intro h
          simp only [aval]
          rw [if_pos hne]
        have hsum : (∑ h, (aval τ (ω, ω') h) ^ (K' + 1)) = 0 := by
          apply Finset.sum_eq_zero
          intro h _
          rw [hazero h, zero_pow (by omega : K' + 1 ≠ 0)]
        rw [hsum, mul_zero]
        exact hCm_nonneg
      · have hc : ∃ j, linCoef (p := p) ω ω' j ≠ 0 := linCoef_exists ω ω' hne
        have haux : ∀ h, aval τ (ω, ω') h = τ (∑ j, linCoef ω ω' j * h j) := by
          intro h
          simp only [aval]
          rw [if_neg hne]
        have hsum_eq : (∑ h, (aval τ (ω, ω') h) ^ (K' + 1))
            = ∑ h : Fin d → ZMod p, (τ (∑ j, linCoef ω ω' j * h j)) ^ (K' + 1) := by
          apply Finset.sum_congr rfl
          intro h _
          rw [haux h]
        rw [hsum_eq]
        have hA := avg_tau_dot (linCoef ω ω') hc τ (K' + 1) hmom
        rwa [hcardfun] at hA
    have hmain := pow_sum_avg_bound (ι := (Fin d → Bool) × (Fin d → Bool))
      (H := Fin d → ZMod p) (a := aval τ) ha_nonneg
      (P := (Fintype.card (ZMod p) : ℝ) ^ d) (Cm := Cm) hPpos hKpos hpair
    rw [hcardι] at hmain
    exact hmain

end Commons.Combinatorics.Transference