import Mathlib
import Submission.Work.FIPlan.Interface

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.FIArea7.P231M

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-! ## 1. The shell `max (|Re z|) (|Im z|)` and the box count -/

/-- The `max` of the absolute values of the coordinates of a Gaussian integer. -/
def mfun (e : GaussianInt) : ℕ := max e.re.natAbs e.im.natAbs

lemma gnorm_eq_coords (z : GaussianInt) :
    Work.FIPlan.gnorm z = z.re.natAbs ^ 2 + z.im.natAbs ^ 2 := by
  simp only [Work.FIPlan.gnorm, GaussianInt.natAbs_norm_eq, pow_two]

lemma sq_mfun_le_gnorm (e : GaussianInt) : (mfun e) ^ 2 ≤ Work.FIPlan.gnorm e := by
  rw [gnorm_eq_coords]
  rcases le_total e.re.natAbs e.im.natAbs with h | h
  · rw [mfun, max_eq_right h]
    exact Nat.le_add_left _ _
  · rw [mfun, max_eq_left h]
    exact Nat.le_add_right _ _

lemma mfun_zero_iff {e : GaussianInt} : mfun e = 0 ↔ e = 0 := by
  constructor
  · intro h
    have h1 : e.re.natAbs = 0 := Nat.le_zero.mp (le_trans (le_max_left _ _) (le_of_eq h))
    have h2 : e.im.natAbs = 0 := Nat.le_zero.mp (le_trans (le_max_right _ _) (le_of_eq h))
    exact Zsqrtd.ext (by simpa using h1) (by simpa using h2)
  · intro h
    subst h
    simp [mfun]

lemma mem_gBox_of_mfun_le {e : GaussianInt} {j : ℕ} (h : mfun e ≤ j) :
    e ∈ Work.FIPlan.gBox ((j : ℤ)) := by
  rw [Work.FIPlan.gBox, Finset.mem_image]
  have hre : e.re.natAbs ≤ j := le_trans (le_max_left _ _) h
  have him : e.im.natAbs ≤ j := le_trans (le_max_right _ _) h
  have key : ∀ a : ℤ, a.natAbs ≤ j → -(j : ℤ) ≤ a ∧ a ≤ (j : ℤ) := by
    intro a ha
    have hcast : (a.natAbs : ℤ) ≤ (j : ℤ) := by exact_mod_cast ha
    rcases Int.natAbs_eq a with hh | hh <;> rw [hh] at hcast ⊢ <;> constructor <;> omega
  obtain ⟨h1, h2⟩ := key e.re hre
  obtain ⟨h3, h4⟩ := key e.im him
  exact ⟨(e.re, e.im), Finset.mem_product.mpr
    ⟨Finset.mem_Icc.mpr ⟨h1, h2⟩, Finset.mem_Icc.mpr ⟨h3, h4⟩⟩, rfl⟩

lemma mfun_le_of_mem_gBox {e : GaussianInt} {R : ℕ} (h : e ∈ Work.FIPlan.gBox ((R : ℤ))) :
    mfun e ≤ R := by
  rw [Work.FIPlan.gBox, Finset.mem_image] at h
  obtain ⟨p, hp, rfl⟩ := h
  obtain ⟨hp1, hp2⟩ := Finset.mem_product.mp hp
  obtain ⟨hp1a, hp1b⟩ := Finset.mem_Icc.mp hp1
  obtain ⟨hp2a, hp2b⟩ := Finset.mem_Icc.mp hp2
  refine max_le ?_ ?_
  · have h1 : |p.1| ≤ (R : ℤ) := abs_le.mpr ⟨hp1a, hp1b⟩
    rw [Int.abs_eq_natAbs] at h1
    exact_mod_cast h1
  · have h1 : |p.2| ≤ (R : ℤ) := abs_le.mpr ⟨hp2a, hp2b⟩
    rw [Int.abs_eq_natAbs] at h1
    exact_mod_cast h1

lemma gBox_mono {R S : ℤ} (h : R ≤ S) : Work.FIPlan.gBox R ⊆ Work.FIPlan.gBox S := by
  intro e he
  rw [Work.FIPlan.gBox, Finset.mem_image] at he ⊢
  obtain ⟨p, hp, rfl⟩ := he
  obtain ⟨hp1, hp2⟩ := Finset.mem_product.mp hp
  obtain ⟨q1, q2⟩ := Finset.mem_Icc.mp hp1
  obtain ⟨q3, q4⟩ := Finset.mem_Icc.mp hp2
  exact ⟨p, Finset.mem_product.mpr
    ⟨Finset.mem_Icc.mpr ⟨by omega, by omega⟩, Finset.mem_Icc.mpr ⟨by omega, by omega⟩⟩, rfl⟩

lemma mem_gBox_iff_mfun {e : GaussianInt} {R : ℕ} :
    e ∈ Work.FIPlan.gBox ((R : ℤ)) ↔ mfun e ≤ R :=
  ⟨mfun_le_of_mem_gBox, mem_gBox_of_mfun_le⟩

lemma card_gBox (j : ℕ) : (Work.FIPlan.gBox ((j : ℤ))).card = (2 * j + 1) ^ 2 := by
  have hinj : Function.Injective (fun p : ℤ × ℤ => (⟨p.1, p.2⟩ : GaussianInt)) :=
    fun a b h => Prod.ext (by simpa using congrArg Zsqrtd.re h) (by simpa using congrArg Zsqrtd.im h)
  rw [Work.FIPlan.gBox, Finset.card_image_of_injective _ hinj, Finset.product_eq_sprod,
    Finset.card_product]
  have hc : (Finset.Icc (-(j : ℤ)) (j : ℤ)).card = 2 * j + 1 := by
    rw [Int.card_Icc]
    have h2 : (j : ℤ) + 1 - (-(j : ℤ)) = ((2 * j + 1 : ℕ) : ℤ) := by push_cast; ring
    rw [h2, Int.toNat_natCast]
  rw [hc]; ring

/-! ## 2. The convergence of `∑_z |z|^{-2t}` over the Gaussian integers -/

theorem sumGnormPowLe (t : ℝ) (ht : 1 < t) :
    ∃ S : ℝ, 0 ≤ S ∧ ∀ E : Finset GaussianInt,
      (∑ e ∈ E, ((Work.FIPlan.gnorm e : ℝ)) ^ (-t)) ≤ S := by
  have h1t : (0 : ℝ) < t := lt_trans zero_lt_one ht
  -- summability of the majorant `k ↦ k^{1-2t}`
  have hsumm : Summable (fun k : ℕ => ((k : ℝ) ^ (1 - 2 * t))) := by
    have h := (Real.summable_nat_rpow_inv (p := 2 * t - 1)).mpr (by linarith)
    refine h.congr (fun n => ?_)
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn
      rw [Nat.cast_zero, Real.zero_rpow (by linarith : (2 * t - 1) ≠ 0), inv_zero,
        Real.zero_rpow (by linarith : (1 - 2 * t) ≠ 0)]
    · have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
      rw [← Real.rpow_neg (le_of_lt hn0)]
      congr 1
      ring
  have hnn : (0 : ℝ) ≤ ∑' k : ℕ, ((k : ℝ) ^ (1 - 2 * t)) :=
    tsum_nonneg (fun k => Real.rpow_nonneg (by positivity) _)
  refine ⟨8 * ∑' k : ℕ, ((k : ℝ) ^ (1 - 2 * t)), by positivity, ?_⟩
  intro E
  -- (1) the pointwise bound `|z|^{-2t} ≤ mfun z^{-2t}`
  have hpt : ∀ e : GaussianInt,
      ((Work.FIPlan.gnorm e : ℝ)) ^ (-t) ≤ ((mfun e : ℝ)) ^ (-(2 * t)) := by
    intro e
    by_cases h0 : mfun e = 0
    · have he0 : e = 0 := mfun_zero_iff.mp h0
      subst he0
      rw [mfun, Work.FIPlan.gnorm]
      simp only [Zsqrtd.re_zero, Int.natAbs_zero, Zsqrtd.im_zero, max_self,
        Zsqrtd.norm_zero, Int.natAbs_zero, Nat.cast_zero]
      rw [Real.zero_rpow (by linarith : -t ≠ 0), Real.zero_rpow (by linarith : -(2 * t) ≠ 0)]
    · have hm0 : (0 : ℝ) < (mfun e : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero h0
      have hle : (mfun e : ℝ) ^ 2 ≤ (Work.FIPlan.gnorm e : ℝ) := by
        exact_mod_cast sq_mfun_le_gnorm e
      have hgn : (0 : ℝ) < (Work.FIPlan.gnorm e : ℝ) := lt_of_lt_of_le (by positivity) hle
      calc ((Work.FIPlan.gnorm e : ℝ)) ^ (-t)
          ≤ (((mfun e : ℝ) ^ 2)) ^ (-t) :=
            Real.rpow_le_rpow_of_nonpos (by positivity) hle (by linarith)
        _ = ((mfun e : ℝ)) ^ (-(2 * t)) := by
            rw [← Real.rpow_natCast (mfun e : ℝ) 2, ← Real.rpow_mul (le_of_lt hm0)]
            congr 1
            ring
  -- (2) reindex by the value of `mfun`
  have hstep : (∑ e ∈ E, ((mfun e : ℝ)) ^ (-(2 * t)))
      = ∑ j ∈ E.image mfun,
          ((E.filter (fun e => mfun e = j)).card : ℝ) * ((j : ℝ) ^ (-(2 * t))) := by
    rw [← Finset.sum_fiberwise_of_maps_to' (fun x _ => Finset.mem_image_of_mem mfun ‹x ∈ E›)
      (f := fun j : ℕ => ((j : ℝ) ^ (-(2 * t))))]
    refine Finset.sum_congr rfl (fun j hj => ?_)
    rw [Finset.sum_const, nsmul_eq_mul]
  -- (3) the fiber count
  have hfiber : ∀ j : ℕ,
      (((E.filter (fun e => mfun e = j)).card : ℝ)) * ((j : ℝ) ^ (-(2 * t)))
        ≤ 8 * (j : ℝ) ^ (1 - 2 * t) := by
    intro j
    rcases Nat.eq_zero_or_pos j with hj | hj
    · subst hj
      have h1 : (((0 : ℕ) : ℝ) ^ (-(2 * t))) = 0 := by
        rw [Nat.cast_zero]
        exact Real.zero_rpow (by linarith : -(2 * t) ≠ 0)
      have h2 : (((0 : ℕ) : ℝ) ^ (1 - 2 * t)) = 0 := by
        rw [Nat.cast_zero]
        exact Real.zero_rpow (by linarith : (1 - 2 * t) ≠ 0)
      rw [h1, h2, mul_zero, mul_zero]
    · have hcard : (E.filter (fun e => mfun e = j)).card ≤ 8 * j := by
        have hsub : E.filter (fun e => mfun e = j)
            ⊆ (Work.FIPlan.gBox ((j : ℤ))) \ (Work.FIPlan.gBox (((j - 1 : ℕ) : ℤ))) := by
          intro e he
          obtain ⟨_, hmj⟩ := Finset.mem_filter.mp he
          refine Finset.mem_sdiff.mpr ⟨mem_gBox_of_mfun_le (le_of_eq hmj), ?_⟩
          intro hmem
          have hle : mfun e ≤ j - 1 := mfun_le_of_mem_gBox hmem
          omega
        have hcard8 : ((Work.FIPlan.gBox ((j : ℤ))) \ (Work.FIPlan.gBox (((j - 1 : ℕ) : ℤ)))).card
            = 8 * j := by
          rw [Finset.card_sdiff]
          rw [Finset.inter_eq_left.mpr (gBox_mono (by omega : ((j - 1 : ℕ) : ℤ) ≤ (j : ℤ)))]
          rw [card_gBox j, card_gBox (j - 1)]
          have h2 : 2 * (j - 1) + 1 ≤ 2 * j + 1 := by omega
          have hcast : (((2 * j + 1) ^ 2 - (2 * (j - 1) + 1) ^ 2 : ℕ) : ℤ) = 8 * (j : ℤ) := by
            have h3 : ((2 * (j - 1) + 1 : ℕ) : ℤ) = 2 * (j : ℤ) - 1 := by
              have h4 : 2 * (j - 1) + 1 = 2 * j - 1 := by omega
              rw [h4, Nat.cast_sub (by omega : 1 ≤ 2 * j)]
              push_cast; ring
            rw [Nat.cast_sub (Nat.pow_le_pow_left h2 2), Nat.cast_pow, Nat.cast_pow, h3]
            push_cast
            ring
          exact_mod_cast hcast
        calc (E.filter (fun e => mfun e = j)).card
            ≤ ((Work.FIPlan.gBox ((j : ℤ))) \ (Work.FIPlan.gBox (((j - 1 : ℕ) : ℤ)))).card :=
              Finset.card_le_card hsub
          _ = 8 * j := hcard8
      have hj0 : (0 : ℝ) < (j : ℝ) := by exact_mod_cast hj
      have hpow : (0 : ℝ) ≤ (j : ℝ) ^ (-(2 * t)) := Real.rpow_nonneg (le_of_lt hj0) _
      have hmul : ((E.filter (fun e => mfun e = j)).card : ℝ) * ((j : ℝ) ^ (-(2 * t)))
          ≤ (8 * j : ℝ) * ((j : ℝ) ^ (-(2 * t))) :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) hpow
      have hpow : (j : ℝ) * (j : ℝ) ^ (-(2 * t)) = (j : ℝ) ^ (1 - 2 * t) := by
        have hID : (1 : ℝ) - 2 * t = 1 + (-(2 * t)) := by ring
        rw [hID, Real.rpow_add hj0 1 (-(2 * t)), Real.rpow_one]
      calc ((E.filter (fun e => mfun e = j)).card : ℝ) * ((j : ℝ) ^ (-(2 * t)))
          ≤ (8 * j : ℝ) * ((j : ℝ) ^ (-(2 * t))) := hmul
        _ = 8 * ((j : ℝ) * (j : ℝ) ^ (-(2 * t))) := by ring
        _ = 8 * (j : ℝ) ^ (1 - 2 * t) := by rw [hpow]
  calc (∑ e ∈ E, ((Work.FIPlan.gnorm e : ℝ)) ^ (-t))
      ≤ ∑ e ∈ E, ((mfun e : ℝ)) ^ (-(2 * t)) := Finset.sum_le_sum (fun e _ => hpt e)
    _ = ∑ j ∈ E.image mfun,
          ((E.filter (fun e => mfun e = j)).card : ℝ) * ((j : ℝ) ^ (-(2 * t))) := hstep
    _ ≤ ∑ j ∈ E.image mfun, 8 * (j : ℝ) ^ (1 - 2 * t) := Finset.sum_le_sum (fun j _ => hfiber j)
    _ = 8 * ∑ j ∈ E.image mfun, (j : ℝ) ^ (1 - 2 * t) := by rw [Finset.mul_sum]
    _ ≤ 8 * ∑' j : ℕ, (j : ℝ) ^ (1 - 2 * t) := by
        refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
        exact hsumm.sum_le_tsum _ (fun j _ => Real.rpow_nonneg (by positivity) _)

end

end Work.FIArea7.P231M
