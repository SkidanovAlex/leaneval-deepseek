import Mathlib
import Submission.Work.LinnikBurgess.burgess_lead_defs
import Submission.Work.LinnikBurgess.twoPow_zmod_kernel
import Submission.Work.LinnikBurgess.twoPow_kernel_char_sum
import Submission.Work.LinnikBurgess.twoPow_g_lt_K_unit
import Submission.Work.LinnikBurgess.twoPow_g_eq_K
import Submission.Work.LinnikBurgess.twoPow_kernel_annihilates_sq
import Submission.Work.LinnikAreas.LocalCorr.sum_zmod_val_pow_eq
import Submission.Work.LinnikBurgess.zmod_char_val

open scoped BigOperators
open Work.LinnikAreas.LocalCorr

namespace Work.LinnikBurgess

private lemma re_natCast_mul_ite {P : Prop} [Decidable P] (A B : ℕ) :
    ((((A : ℕ) : ℂ) * (if P then ((B : ℕ) : ℂ) else 0))).re
      = ((A : ℕ) : ℝ) * (if P then ((B : ℕ) : ℝ) else 0) := by
  by_cases h : P
  · rw [if_pos h, if_pos h]
    rw [← Complex.ofReal_natCast, ← Complex.ofReal_natCast, ← Complex.ofReal_mul,
      Complex.ofReal_re]
  · simp [h]

theorem twoPow_quadGaussSum {K m : ℕ} (hK : 1 ≤ K) (hm : 1 ≤ m) (hmK : m ≤ K)
    {θ : ℂ} (hθ : IsPrimitiveRoot θ (2 ^ K)) (α γ : ZMod (2 ^ K)) :
    ‖∑ w : ZMod (2 ^ K),
        θ ^ ((α * w - ((2 ^ (m - 1) : ℕ) : ZMod (2 ^ K)) * γ * w ^ 2).val)‖
      ≤ (2 : ℝ) ^ (((K + (m + vcap 2 (K - m) γ.val) : ℕ) : ℝ) / 2)
        * (if 2 ^ (m + vcap 2 (K - m) γ.val - 1) ∣ α.val then 1 else 0) := by
  classical
  have hK0 : 2 ^ K ≠ 0 := pow_ne_zero K (by norm_num)
  haveI : NeZero (2 ^ K) := ⟨hK0⟩
  set g : ℕ := m + vcap 2 (K - m) γ.val with hg
  set δ : ZMod (2 ^ K) := ((2 ^ (m - 1) : ℕ) : ZMod (2 ^ K)) * γ with hδ
  set B : ZMod (2 ^ K) := ((2 ^ m : ℕ) : ZMod (2 ^ K)) * γ with hB
  set G : ℂ := ∑ w : ZMod (2 ^ K), θ ^ ((α * w - δ * w ^ 2).val) with hG
  -- ### elementary facts
  have hgle : g ≤ K := by
    rw [hg]
    have hv : vcap 2 (K - m) γ.val ≤ K - m := by
      unfold vcap
      split_ifs with hx
      · exact le_rfl
      · exact min_le_right _ _
    omega
  -- ### the delegated arithmetic / character-sum facts
  have hUnit : g < K → ∃ u : (ZMod (2 ^ K))ˣ,
      ((((2 ^ g : ℕ) : ZMod (2 ^ K)) * (u : ZMod (2 ^ K)) = B)
        ∧ (((2 ^ (g - 1) : ℕ) : ZMod (2 ^ K)) * (u : ZMod (2 ^ K)) = δ)) := by
    intro hlt
    obtain ⟨u, hu1, hu2⟩ := twoPow_g_lt_K_unit hK hm hmK γ (by rw [← hg]; exact hlt)
    refine ⟨u, ?_, ?_⟩
    · rw [hB, hg]; exact hu1
    · rw [hδ, hg]
      have hexp : m + vcap 2 (K - m) γ.val - 1 = m - 1 + vcap 2 (K - m) γ.val := by omega
      rw [hexp]; exact hu2
  have hChar : ∀ a : ZMod (2 ^ K),
      (∑ h ∈ Finset.univ.filter (fun h : ZMod (2 ^ K) => ((2 ^ g : ℕ) : ZMod (2 ^ K)) * h = 0),
        θ ^ ((a * h).val))
        = if 2 ^ g ∣ a.val then ((2 ^ g : ℕ) : ℂ) else 0 := by
    intro a
    exact twoPow_kernel_char_sum hgle hθ a
  have hSq : g + 1 ≤ K → ∀ h : ZMod (2 ^ K),
      ((2 ^ g : ℕ) : ZMod (2 ^ K)) * h = 0 →
        ((2 ^ (g - 1) : ℕ) : ZMod (2 ^ K)) * h ^ 2 = 0 := by
    intro hgK h hh
    exact twoPow_kernel_annihilates_sq (by omega : 1 ≤ g) hgK hh
  have hEqK : m + vcap 2 (K - m) γ.val = K →
      (B = 0 ∧ ∀ h : ZMod (2 ^ K), δ * h ^ 2 = δ * h) := by
    intro hK'
    obtain ⟨hB0, hδsq⟩ := twoPow_g_eq_K hK hm hmK γ hK'
    refine ⟨?_, ?_⟩
    · rw [hB]; exact hB0
    · intro h
      rw [hδ]
      exact hδsq h
  -- the character toolkit `zmod_char_val` applies verbatim at the modulus `2 ^ K`
  have hFadd : ∀ x y : ZMod (2 ^ K), θ ^ ((x + y).val) = θ ^ x.val * θ ^ y.val :=
    fun x y => zmod_pow_val_add hθ x y
  have hFneg : ∀ x : ZMod (2 ^ K), θ ^ ((-x).val) = (θ ^ x.val)⁻¹ :=
    fun x => zmod_pow_val_neg hθ x
  have hconj : ∀ x : ZMod (2 ^ K), star (θ ^ x.val) = θ ^ ((-x).val) :=
    fun x => zmod_pow_val_star hK0 hθ x
  have hB2δ : B = 2 * δ := by
    rw [hB, hδ]
    rw [show ((2 ^ m : ℕ) : ZMod (2 ^ K))
        = ((2 : ℕ) : ZMod (2 ^ K)) * ((2 ^ (m - 1) : ℕ) : ZMod (2 ^ K)) from by
      rw [← Nat.cast_mul, show (2 : ℕ) ^ m = 2 * 2 ^ (m - 1) from by
        obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : m ≠ 0)
        simp [pow_succ, mul_comm]]]
    ring
  -- ### the key identity
  have hkey : G * star G = ((2 ^ K : ℕ) : ℂ)
      * (∑ h : ZMod (2 ^ K), if B * h = 0 then θ ^ ((α * h - δ * h ^ 2).val) else 0) := by
    have hsplit : G * star G
        = ∑ w : ZMod (2 ^ K), ∑ w' : ZMod (2 ^ K),
            θ ^ (((α * w - δ * w ^ 2) + -(α * w' - δ * w' ^ 2)).val) := by
      rw [hG, star_sum, Finset.sum_mul_sum]
      refine Finset.sum_congr rfl fun w _ => Finset.sum_congr rfl fun w' _ => ?_
      rw [hconj, ← hFadd]
    have hreindex : (∑ w : ZMod (2 ^ K), ∑ w' : ZMod (2 ^ K),
          θ ^ (((α * w - δ * w ^ 2) + -(α * w' - δ * w' ^ 2)).val))
        = ∑ h : ZMod (2 ^ K), ∑ w' : ZMod (2 ^ K),
            θ ^ (((α * h - δ * h ^ 2) - B * h * w').val) := by
      have h1 : (∑ w : ZMod (2 ^ K), ∑ w' : ZMod (2 ^ K),
            θ ^ (((α * w - δ * w ^ 2) + -(α * w' - δ * w' ^ 2)).val))
          = ∑ w' : ZMod (2 ^ K), ∑ w : ZMod (2 ^ K),
            θ ^ (((α * w - δ * w ^ 2) + -(α * w' - δ * w' ^ 2)).val) := Finset.sum_comm
      have h2 : (∑ w' : ZMod (2 ^ K), ∑ w : ZMod (2 ^ K),
            θ ^ (((α * w - δ * w ^ 2) + -(α * w' - δ * w' ^ 2)).val))
          = ∑ w' : ZMod (2 ^ K), ∑ h : ZMod (2 ^ K),
            θ ^ (((α * h - δ * h ^ 2) - B * h * w').val) := by
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [← Equiv.sum_comp (Equiv.addRight a)
          (fun w => θ ^ (((α * w - δ * w ^ 2) + -(α * a - δ * a ^ 2)).val))]
        simp only [Equiv.coe_addRight]
        refine Finset.sum_congr rfl fun b _ => ?_
        apply congrArg (fun z : ZMod (2 ^ K) => θ ^ z.val)
        rw [hB2δ]; ring
      have h3 : (∑ w' : ZMod (2 ^ K), ∑ h : ZMod (2 ^ K),
            θ ^ (((α * h - δ * h ^ 2) - B * h * w').val))
          = ∑ h : ZMod (2 ^ K), ∑ w' : ZMod (2 ^ K),
            θ ^ (((α * h - δ * h ^ 2) - B * h * w').val) := Finset.sum_comm
      exact h1.trans (h2.trans h3)
    have hfin : (∑ h : ZMod (2 ^ K), ∑ w' : ZMod (2 ^ K),
          θ ^ (((α * h - δ * h ^ 2) - B * h * w').val))
        = ((2 ^ K : ℕ) : ℂ)
          * (∑ h : ZMod (2 ^ K), if B * h = 0 then θ ^ ((α * h - δ * h ^ 2).val) else 0) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun h _ => ?_
      have hprod : (∑ w' : ZMod (2 ^ K), θ ^ (((α * h - δ * h ^ 2) - B * h * w').val))
          = θ ^ ((α * h - δ * h ^ 2).val)
            * (∑ w' : ZMod (2 ^ K), θ ^ (((-B) * h * w').val)) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun w' _ => ?_
        rw [← hFadd (α * h - δ * h ^ 2) ((-B) * h * w')]
        apply congrArg (fun z : ZMod (2 ^ K) => θ ^ z.val)
        ring
      rw [hprod, sum_zmod_val_pow_eq (2 ^ K) hθ ((-B) * h)]
      by_cases hc : B * h = 0
      · have hc' : ((-B) * h : ZMod (2 ^ K)) = 0 := by rw [neg_mul, neg_eq_zero]; exact hc
        rw [if_pos hc', if_pos hc]; ring
      · have hc' : ¬ ((-B) * h : ZMod (2 ^ K)) = 0 := by rw [neg_mul, neg_eq_zero]; exact hc
        rw [if_neg hc', if_neg hc]; ring
    rw [hsplit, hreindex, hfin]
  have hnorm : ‖G‖ ^ 2 = (((2 ^ K : ℕ) : ℂ)
      * (∑ h : ZMod (2 ^ K), if B * h = 0 then θ ^ ((α * h - δ * h ^ 2).val) else 0)).re := by
    have h := congrArg Complex.re hkey
    rw [Complex.star_def] at h
    rw [Complex.mul_conj, Complex.ofReal_re] at h
    rw [Complex.sq_norm]
    exact h
  rcases lt_or_eq_of_le hgle with hlt | heq
  · -- #### case g < K
    have hg1 : 1 ≤ g := by rw [hg]; omega
    have hgK1 : g + 1 ≤ K := by omega
    obtain ⟨u, hu1, hu2⟩ := hUnit hlt
    have hker : ∀ h : ZMod (2 ^ K), B * h = 0 ↔ ((2 ^ g : ℕ) : ZMod (2 ^ K)) * h = 0 := by
      intro h
      have hBexpr : B * h = (u : ZMod (2 ^ K)) * (((2 ^ g : ℕ) : ZMod (2 ^ K)) * h) := by
        rw [← hu1]; ring
      rw [hBexpr, IsUnit.mul_right_eq_zero (Units.isUnit u)]
    have hAkern : ∀ h : ZMod (2 ^ K),
        ((2 ^ g : ℕ) : ZMod (2 ^ K)) * h = 0 → α * h - δ * h ^ 2 = α * h := by
      intro h hh
      have hsq := hSq hgK1 h hh
      have hδh2 : δ * h ^ 2 = 0 := by
        rw [← hu2]
        rw [show (((2 ^ (g - 1) : ℕ) : ZMod (2 ^ K)) * (u : ZMod (2 ^ K))) * h ^ 2
            = (u : ZMod (2 ^ K)) * (((2 ^ (g - 1) : ℕ) : ZMod (2 ^ K)) * h ^ 2) from by ring,
          hsq, mul_zero]
      rw [hδh2, sub_zero]
    have hSval : (∑ h : ZMod (2 ^ K), if B * h = 0 then θ ^ ((α * h - δ * h ^ 2).val) else 0)
        = if 2 ^ g ∣ α.val then ((2 ^ g : ℕ) : ℂ) else 0 := by
      trans ∑ h : ZMod (2 ^ K),
          (if ((2 ^ g : ℕ) : ZMod (2 ^ K)) * h = 0 then θ ^ ((α * h).val) else 0)
      · refine Finset.sum_congr rfl fun h _ => ?_
        by_cases hc : ((2 ^ g : ℕ) : ZMod (2 ^ K)) * h = 0
        · rw [if_pos ((hker h).mpr hc), if_pos hc, hAkern h hc]
        · rw [if_neg (fun hh => hc ((hker h).mp hh)), if_neg hc]
      · rw [← Finset.sum_filter]
        exact hChar α
    have hGsq : ‖G‖ ^ 2 = (2 : ℝ) ^ K * (if 2 ^ g ∣ α.val then (2 : ℝ) ^ g else 0) := by
      rw [hnorm, hSval, re_natCast_mul_ite]
      rw [show ((2 ^ K : ℕ) : ℝ) = (2 : ℝ) ^ K from by rw [Nat.cast_pow, Nat.cast_ofNat],
          show ((2 ^ g : ℕ) : ℝ) = (2 : ℝ) ^ g from by rw [Nat.cast_pow, Nat.cast_ofNat]]
    by_cases hc : 2 ^ g ∣ α.val
    · have hgl1 : 2 ^ (g - 1) ∣ α.val :=
        dvd_trans (pow_dvd_pow 2 (by omega : g - 1 ≤ g)) hc
      rw [if_pos hgl1, mul_one]
      have h2 : ‖G‖ ^ 2 = (2 : ℝ) ^ (K + g) := by
        rw [hGsq, if_pos hc, ← pow_add]
      have h3 : ((2 : ℝ) ^ (((K + g : ℕ) : ℝ) / 2)) ^ 2 = (2 : ℝ) ^ (K + g) := by
        rw [← Real.rpow_natCast ((2 : ℝ) ^ (((K + g : ℕ) : ℝ) / 2)) 2,
          ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
        rw [show ((K + g : ℕ) : ℝ) / 2 * ((2 : ℕ) : ℝ) = ((K + g : ℕ) : ℝ) from by
          push_cast; ring]
        exact Real.rpow_natCast 2 (K + g)
      have h4 : ‖G‖ = (2 : ℝ) ^ (((K + g : ℕ) : ℝ) / 2) := by
        rcases sq_eq_sq_iff_eq_or_eq_neg.mp (h2.trans h3.symm) with hh | hh
        · exact hh
        · have hpos := Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) (((K + g : ℕ) : ℝ) / 2)
          linarith [norm_nonneg G]
      rw [h4]
    · have h2 : ‖G‖ ^ 2 = 0 := by rw [hGsq, if_neg hc, mul_zero]
      have hG0 : ‖G‖ = 0 := sq_eq_zero_iff.mp h2
      rw [hG0]
      apply mul_nonneg
      · exact Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) _
      · split_ifs <;> norm_num
  · -- #### case g = K
    rw [heq]
    have hexp : ((K + K : ℕ) : ℝ) / 2 = (K : ℝ) := by push_cast; ring
    rw [hexp, Real.rpow_natCast]
    obtain ⟨hB0, hδsq⟩ := hEqK (hg.symm.trans heq)
    have hBzero : B = 0 := hB0
    have hδ2 : (2 : ZMod (2 ^ K)) * δ = 0 := by rw [← hB2δ, hBzero]
    have hSval : (∑ h : ZMod (2 ^ K), if B * h = 0 then θ ^ ((α * h - δ * h ^ 2).val) else 0)
        = if α - δ = 0 then ((2 ^ K : ℕ) : ℂ) else 0 := by
      trans ∑ h : ZMod (2 ^ K), θ ^ (((α - δ) * h).val)
      · refine Finset.sum_congr rfl fun h _ => ?_
        have hA : α * h - δ * h ^ 2 = (α - δ) * h := by
          rw [hδsq h]; ring
        rw [hBzero, zero_mul, if_pos rfl, hA]
      · exact sum_zmod_val_pow_eq (2 ^ K) hθ (α - δ)
    have hGsqK : ‖G‖ ^ 2
        = ((2 : ℝ) ^ K) * ((2 : ℝ) ^ K) * (if α - δ = 0 then 1 else 0) := by
      rw [hnorm, hSval, re_natCast_mul_ite]
      rw [show ((2 ^ K : ℕ) : ℝ) = (2 : ℝ) ^ K from by rw [Nat.cast_pow, Nat.cast_ofNat]]
      by_cases hc : α - δ = 0 <;> simp [hc]
    have hαne : α - δ = 0 → 2 ^ (K - 1) ∣ α.val := by
      intro h
      have hα : α = δ := sub_eq_zero.mp h
      have h2α : (2 : ZMod (2 ^ K)) * α = 0 := by rw [hα]; exact hδ2
      have hcast : ((2 * α.val : ℕ) : ZMod (2 ^ K)) = (2 : ZMod (2 ^ K)) * α := by
        rw [Nat.cast_mul, ZMod.natCast_zmod_val α]; ring
      have h2α' : 2 ^ K ∣ 2 * α.val := by
        have hzero : ((2 * α.val : ℕ) : ZMod (2 ^ K)) = 0 := by rw [hcast, h2α]
        exact (ZMod.natCast_eq_zero_iff (2 * α.val) (2 ^ K)).mp hzero
      have h2K : 2 ^ K = 2 * 2 ^ (K - 1) := by
        obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : K ≠ 0)
        simp [pow_succ, mul_comm]
      have h2α'' : 2 * 2 ^ (K - 1) ∣ 2 * α.val := by
        rw [← h2K]; exact h2α'
      exact (Nat.mul_dvd_mul_iff_left (by norm_num : 0 < 2)).mp h2α''
    by_cases hc : 2 ^ (K - 1) ∣ α.val
    · rw [if_pos hc, mul_one]
      have hb : (0 : ℝ) ≤ (2 : ℝ) ^ K := by positivity
      have h1 : ‖G‖ ^ 2 ≤ ((2 : ℝ) ^ K) ^ 2 := by
        rw [hGsqK]
        by_cases hh : α - δ = 0
        · rw [if_pos hh]; nlinarith [sq_nonneg ((2 : ℝ) ^ K)]
        · rw [if_neg hh]; simp
      have h2 := sq_le_sq.mp h1
      rw [abs_of_nonneg hb, abs_of_nonneg (norm_nonneg G)] at h2
      exact h2
    · rw [if_neg hc, mul_zero]
      have hαne' : α - δ ≠ 0 := fun h => hc (hαne h)
      have hG0 : ‖G‖ = 0 := by
        have h2 : ‖G‖ ^ 2 = 0 := by rw [hGsqK, if_neg hαne', mul_zero]
        exact sq_eq_zero_iff.mp h2
      rw [hG0]

end Work.LinnikBurgess
