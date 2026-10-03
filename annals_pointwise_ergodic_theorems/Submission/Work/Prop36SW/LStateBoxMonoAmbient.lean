import Mathlib
import Submission.Work.Peluse.Prop36SW.roundDefs
import Submission.Work.Peluse.Ulower.finalTarget

/-!
# The ambient (support window) monotonicity of `LStateBox`

`Work.Peluse.Prop36SW.LStateBox` is `LStateAbs` with the non-vanishing conjunct removed (see
`roundDefs.lean`).  This module proves that the state can be *inflated* to a larger window `N' ≥ N`,
at the cost of scaling the family constant `γ` down by the ratio of the window sizes:

`LStateBox kω p M₁ M₂ N Dc A g γ → LStateBox kω p M₁ M₂ N' Dc A g (γ · |symIcc N| / |symIcc N'|)`.

The argument is the verbatim analogue of `LStateAbsMonoAmbient`
(`Submission/Work/Prop36SW/LStateAbsMonoAmbient.lean`): the window `S` enters `boxNormPow t Q S f`
only through the normalising factor `|S|⁻¹`, so

`boxNormPow t Q (symIcc N') f = (|symIcc N| / |symIcc N'|) · boxNormPow t Q (symIcc N) f`,

and taking the `1/2^t`-th root (an exponent in `[0,1]`) of the ratio `≤ 1` only increases it.  All the
other conjuncts are monotone in the window, and the hypothesis `M₁ M₂ ≤ N'` is exactly the new side
condition.  The only difference from `LStateAbs` is that there is no non-vanishing conjunct to carry
across.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000
open scoped BigOperators

namespace Work.Prop36SW

noncomputable section

open Work.Peluse
open Work.Peluse.UControl
open Work.Peluse.Prop36SW

/-! ## Elementary window facts -/

/-- The symmetric intervals are monotone in the radius. -/
private lemma symIcc_subset_of_le_box {N N' : ℕ} (h : N ≤ N') : symIcc N ⊆ symIcc N' := by
  intro x hx
  rw [symIcc, Finset.mem_Icc] at hx ⊢
  obtain ⟨h1, h2⟩ := hx
  have hc : (N : ℤ) ≤ (N' : ℤ) := by exact_mod_cast h
  exact ⟨by omega, by omega⟩

/-- `|symIcc|` is monotone. -/
private lemma card_symIcc_le_box {N N' : ℕ} (h : N ≤ N') :
    (symIcc N).card ≤ (symIcc N').card :=
  Finset.card_le_card (symIcc_subset_of_le_box h)

/-- `symIcc N` always contains `0`, hence is nonempty. -/
private lemma symIcc_nonempty_box (N : ℕ) : (symIcc N).Nonempty :=
  ⟨0, by simp [symIcc]⟩

/-- `symIcc N` has positive cardinality. -/
private lemma symIcc_card_pos_box (N : ℕ) : (0 : ℝ) < ((symIcc N).card : ℝ) := by
  have h : 0 < (symIcc N).card := Finset.card_pos.mpr (symIcc_nonempty_box N)
  exact_mod_cast h

/-! ## The window of a box norm is only a normalisation -/

/-- Scaling of the cube sum in the window. -/
private lemma boxSumPow_scale_box (t : ℕ) (Q : Fin t → Finset ℤ) (S S' : Finset ℤ) (f : ℤ → ℂ)
    (hS' : S'.Nonempty) :
    boxSumPow t Q S f = ((S.card : ℂ))⁻¹ * (S'.card : ℂ) * boxSumPow t Q S' f := by
  have hb : (S'.card : ℂ) ≠ 0 := by
    have h := Finset.card_ne_zero.mpr hS'
    exact_mod_cast h
  rw [boxSumPow, boxSumPow, prodCubeSum_eq, prodCubeSum_eq]
  field_simp
  try ring

/-- The window of a box-norm power is only a normalisation factor. -/
private lemma boxNormPow_window_ratio_box (t : ℕ) (Q : Fin t → Finset ℤ) (S S' : Finset ℤ)
    (f : ℤ → ℂ) (hS' : S'.Nonempty) :
    boxNormPow t Q S f = ((S'.card : ℝ) / (S.card : ℝ)) * boxNormPow t Q S' f := by
  have h := boxSumPow_scale_box t Q S S' f hS'
  have hnorm : ‖((S.card : ℂ))⁻¹‖ = ((S.card : ℝ))⁻¹ := by
    rw [norm_inv, Complex.norm_natCast]
  simp only [boxNormPow]
  rw [h, norm_mul, norm_mul, hnorm, Complex.norm_natCast]
  ring

/-- The same ratio, written for the two symmetric windows. -/
private lemma boxNormPow_symIcc_ratio_box {t : ℕ} (Q : Fin t → Finset ℤ) (N N' : ℕ) (f : ℤ → ℂ) :
    boxNormPow t Q (symIcc N') f
      = (((symIcc N).card : ℝ) / ((symIcc N').card : ℝ)) * boxNormPow t Q (symIcc N) f :=
  boxNormPow_window_ratio_box t Q (symIcc N') (symIcc N) f (symIcc_nonempty_box N)

/-- **Enlarging the window of a box norm**: the exact scaling identity for the box norm itself,
obtained by taking the `1/2^t`-th root of the identity for `boxNormPow`. -/
private lemma boxNorm_symIcc_ratio_box {t : ℕ} (Q : Fin t → Finset ℤ) (N N' : ℕ) (f : ℤ → ℂ) :
    boxNorm t Q (symIcc N') f
      = (((symIcc N).card : ℝ) / ((symIcc N').card : ℝ)) ^ (1 / (2 : ℝ) ^ t)
          * boxNorm t Q (symIcc N) f := by
  have h := boxNormPow_symIcc_ratio_box (t := t) Q N N' f
  have h0 : (0 : ℝ) ≤ ((symIcc N).card : ℝ) / ((symIcc N').card : ℝ) := by positivity
  have h1 : (0 : ℝ) ≤ boxNormPow t Q (symIcc N) f := norm_nonneg _
  simp only [boxNorm]
  rw [h, Real.mul_rpow h0 h1]

/-! ## Two elementary real-variable facts -/

/-- For `0 < x ≤ 1` and `z ≤ 1` one has `x ≤ x^z`. -/
private lemma self_le_rpow_of_le_one_box {x z : ℝ} (hx0 : 0 < x) (hx1 : x ≤ 1) (hz1 : z ≤ 1) :
    x ≤ x ^ z := by
  have h : x ^ (1 : ℝ) ≤ x ^ z := Real.rpow_le_rpow_of_exponent_ge hx0 hx1 hz1
  simpa using h

/-- `1 / 2^t ≤ 1`. -/
private lemma one_div_two_pow_le_one_box (t : ℕ) : (1 : ℝ) / (2 : ℝ) ^ t ≤ 1 :=
  (div_le_one (by positivity)).mpr (one_le_pow₀ (by norm_num))

/-! ## A warm-up for the family inequality: the sum-level comparison -/

/-- If every term is scaled up (weakly) by replacing `B` with `B'` and dropping the factor `r ≥ 0`,
and if `γ ≤ K · ∑ B`, then `γ · r ≤ K · ∑ B'` (for `K ≥ 0`). -/
private lemma fam_sum_mono_box {P S : Type} [DecidableEq P] {A : Finset P} {PB : Finset S}
    {B B' : P → S → ℝ} {r K γ : ℝ} (hK : 0 ≤ K) (hr0 : 0 ≤ r)
    (hterm : ∀ a ∈ A, ∀ a' ∈ PB, r * B a a' ≤ B' a a')
    (hfam : γ ≤ K * (∑ a ∈ A, ∑ a' ∈ PB, B a a')) :
    γ * r ≤ K * (∑ a ∈ A, ∑ a' ∈ PB, B' a a') := by
  have hsum : r * (∑ a ∈ A, ∑ a' ∈ PB, B a a') ≤ ∑ a ∈ A, ∑ a' ∈ PB, B' a a' := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun a ha => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun a' ha' => hterm a ha a' ha'
  calc γ * r ≤ (K * (∑ a ∈ A, ∑ a' ∈ PB, B a a')) * r := mul_le_mul_of_nonneg_right hfam hr0
    _ = K * (r * (∑ a ∈ A, ∑ a' ∈ PB, B a a')) := by ring
    _ ≤ K * (∑ a ∈ A, ∑ a' ∈ PB, B' a a') := mul_le_mul_of_nonneg_left hsum hK

/-! ## The ambient monotonicity -/

theorem LStateBoxMonoAmbient {ι : Type} [Fintype ι] [DecidableEq ι]
    {kω : Work.Peluse.UControl.SlotSet ι (fun _ => 1) → ℕ} {P : Type} [DecidableEq P]
    {p : ι → P → ℤ} {M₁ M₂ N N' Dc : ℕ} {A : Finset P} {g : P → ℤ → ℂ} {γ : ℝ}
    (h : Work.Peluse.Prop36SW.LStateBox kω p M₁ M₂ N Dc A g γ) (hN : N ≤ N')
    (hM : ((M₁ : ℝ) * (M₂ : ℝ)) ≤ (N' : ℝ)) :
    Work.Peluse.Prop36SW.LStateBox kω p M₁ M₂ N' Dc A g
      (γ * (((Work.Peluse.symIcc N).card : ℝ) / ((Work.Peluse.symIcc N').card : ℝ))) := by
  obtain ⟨h0, h1, h2, h3, h4, h5, hpl, hpa, hg1, hg2, hfam⟩ := h
  have hN'1 : 1 ≤ N' := le_trans h4 hN
  set r : ℝ := ((symIcc N).card : ℝ) / ((symIcc N').card : ℝ) with hr
  have hrpos : 0 < r := by
    rw [hr]
    exact div_pos (symIcc_card_pos_box N) (symIcc_card_pos_box N')
  have hr0 : 0 ≤ r := le_of_lt hrpos
  have hrle1 : r ≤ 1 := by
    rw [hr]
    exact div_le_one_of_le₀ (by exact_mod_cast card_symIcc_le_box hN)
      (le_of_lt (symIcc_card_pos_box N'))
  -- the window-family data, with the large expressions hidden in local definitions
  let tB : ℕ := Fintype.card (FamIdx kω)
  let Qf : P → (Slot ι (fun _ => 1) → ℤ) → Fin tB → Finset ℤ :=
    fun a a' j => pDirFamG p M₁ a a' ((Fintype.equivFin (FamIdx kω)).symm j)
  let B : P → (Slot ι (fun _ => 1) → ℤ) → ℝ :=
    fun a a' => boxNorm tB (Qf a a') (symIcc N) (g a)
  let B' : P → (Slot ι (fun _ => 1) → ℤ) → ℝ :=
    fun a a' => boxNorm tB (Qf a a') (symIcc N') (g a)
  let PB : Finset (Slot ι (fun _ => 1) → ℤ) := paramBox (k := fun _ : ι => 1) M₂
  let K : ℝ := ((A.card : ℝ))⁻¹ * (PB.card : ℝ)⁻¹
  refine ⟨?_, ?_, h2, h3, hN'1, hM, ?_, ?_, hg1, ?_, ?_⟩
  · exact mul_pos h0 hrpos
  · calc γ * r ≤ 1 * 1 := mul_le_mul h1 hrle1 hr0 (by norm_num)
      _ = 1 := by norm_num
  · intro i a ha
    exact le_trans (hpl i a ha) (by exact_mod_cast hN)
  · intro i a ha
    exact le_trans (hpa i a ha)
      (Int.mul_le_mul_of_nonneg_left (by exact_mod_cast hN) (by positivity))
  · intro a ha
    exact (hg2 a ha).mono hN
  · -- the family hypothesis
    have hrpow : r ≤ r ^ (1 / (2 : ℝ) ^ tB) :=
      self_le_rpow_of_le_one_box hrpos hrle1 (one_div_two_pow_le_one_box tB)
    have hK0 : (0 : ℝ) ≤ K := by dsimp only [K]; positivity
    have hfamK : γ ≤ K * (∑ a ∈ A, ∑ a' ∈ PB, B a a') := hfam
    have hterm : ∀ a ∈ A, ∀ a' ∈ PB, r * B a a' ≤ B' a a' := by
      intro a ha a' ha'
      have hB0 : (0 : ℝ) ≤ boxNorm tB (Qf a a') (symIcc N) (g a) :=
        Real.rpow_nonneg (norm_nonneg _) _
      dsimp only [B, B']
      rw [boxNorm_symIcc_ratio_box (t := tB) (Qf a a') N N' (g a)]
      exact mul_le_mul_of_nonneg_right hrpow hB0
    exact fam_sum_mono_box hK0 hr0 hterm hfamK

end

end Work.Prop36SW
