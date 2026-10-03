/-
# Non-aliasing of the exact-height IW frequencies at the repaired window (Area A7)

`Work.KMTAreas.A7.LpNonAliasAtWindow`: for `ρ ≤ 1/8`, `d ≥ 2` and every `l₂, k₁, k₂`, the exact
height frequency set `diffFreqs ρ l₂` is non-aliased at the arc radius `2^{-2·d·u}` of the
*repaired* window `u = loMixedU ρ d l₂ k₁ k₂ = max (uScale ρ L) (d·l₂+3)`.

This is the hypothesis `hNA₂` of `Work.KMTPlan.A6.lpSymC_sub_symMWin_eq_symD`.  The proof splits
on the two regimes of `iwP ρ l₂`:

* `l₂ ≤ iwC0 ρ`: then `iwP ρ l₂ = [1, 2^{l₂}]`, so two distinct exact-height frequencies with
  denominators `q, q' ≤ 2^{l₂}` are separated by `≥ 2^{-2l₂} > 2^{1-2du}` (as `2du ≥ 8l₂+12`);
* `l₂ > iwC0 ρ`: every `q ∈ iwP ρ l₂` is at most `T = Q_0^{(l₂)}·(2^{l₂})^{D_ρ^2}`, and
  `lp_T_le` gives `4T² ≤ 2^{2·2^{2ρl₂}} ≤ 2^{2du}`; hence the separation `≥ 1/T² > 2^{1-2du}`.
-/
import Mathlib
import Submission.Work.KMTAreas.A7.LpNonAliasNum

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace Work.KMTAreas.A7

open MeasureTheory Finset
open scoped BigOperators
open Work.Analysis.IonescuWainger

noncomputable section

/-- The integer power `2^k` is the real power `2^{k:ℝ}`. -/
lemma lp_zpow_two_eq_rpow (k : ℤ) : (2 : ℝ) ^ k = (2 : ℝ) ^ (k : ℝ) :=
  (Real.rpow_intCast 2 k).symm

/-- The class in `ℝ/ℤ` of a real number has norm at most the absolute value. -/
lemma lp_norm_coe_circle_le_abs (u : ℝ) :
    ‖((u : ℝ) : Work.Analysis.IonescuWainger.Circle)‖ ≤ |u| := by
  have h := QuotientAddGroup.norm_mk_le_norm (S := AddSubgroup.zmultiples (1 : ℝ)) (m := u)
  simpa only [Work.Analysis.IonescuWainger.Circle, AddCircle, Real.norm_eq_abs] using h

/-- The exact-height frequencies at `l` are IW arithmetic frequencies at `l`. -/
lemma lp_diffFreqs_subset (ρ : ℝ) (l : ℕ) : diffFreqs ρ l ⊆ iwArithFreqs ρ l := by
  rw [diffFreqs]
  by_cases h : l = 0
  · rw [if_pos h, h]
  · rw [if_neg h]
    exact Finset.sdiff_subset

/-- **Separation of two distinct elements of `diffFreqs ρ l`**, given a common bound `B` on all
denominators in `iwP ρ l` that kill them. -/
lemma lp_sep_le_of_den {ρ : ℝ} {l : ℕ} {B : ℕ} (hB : 0 < B)
    {α β : Work.Analysis.IonescuWainger.Circle}
    (hα : α ∈ diffFreqs ρ l) (hβ : β ∈ diffFreqs ρ l)
    (hαB : ∀ q : ℕ, q ∈ iwP ρ l → q • α = 0 → q ≤ B)
    (hβB : ∀ q : ℕ, q ∈ iwP ρ l → q • β = 0 → q ≤ B) (hne : α ≠ β) :
    (1 : ℝ) / (B : ℝ) ^ 2 ≤ ‖α - β‖ := by
  obtain ⟨q, hq0, hqP, hqα⟩ := iwArithFreqs_exists_den (lp_diffFreqs_subset ρ l hα)
  obtain ⟨q', hq'0, hq'P, hq'β⟩ := iwArithFreqs_exists_den (lp_diffFreqs_subset ρ l hβ)
  have hqB : q ≤ B := hαB q hqP hqα
  have hq'B : q' ≤ B := hβB q' hq'P hq'β
  have hsep : (1 : ℝ) / ((q * q' : ℕ) : ℝ) ≤ ‖α - β‖ := by
    refine one_div_le_norm_of_ne (Nat.mul_pos hq0 hq'0) ?_ ?_ hne
    · rw [mul_comm, mul_smul, hqα, smul_zero]
    · rw [mul_smul, hq'β, smul_zero]
  have hqq : (1 : ℝ) / (B : ℝ) ^ 2 ≤ 1 / ((q * q' : ℕ) : ℝ) := by
    have h1 : (q : ℝ) ≤ (B : ℝ) := by exact_mod_cast hqB
    have h2 : (q' : ℝ) ≤ (B : ℝ) := by exact_mod_cast hq'B
    have hBnn : (0 : ℝ) ≤ (B : ℝ) := by positivity
    have h1' : (q : ℝ) * (q' : ℝ) ≤ (B : ℝ) * (B : ℝ) := mul_le_mul h1 h2 (by positivity) hBnn
    have hqq' : ((q * q' : ℕ) : ℝ) ≤ (B : ℝ) ^ 2 := by
      rw [Nat.cast_mul, sq]
      exact h1'
    exact one_div_le_one_div_of_le (by positivity) hqq'
  exact hqq.trans hsep

/-- In the first regime (`l ≤ iwC0 ρ`), the radius `2^{E+1}` with `E = -2du` is below the
separation `2^{-2l}`. -/
lemma lp_exp_case1 {d u l : ℕ} (hd : 2 ≤ d) (hu : d * l + 3 ≤ u) :
    (2 : ℝ) ^ (-(2 * (d : ℝ) * (u : ℝ)) + 1) < (2 : ℝ) ^ (-((2 * l : ℕ) : ℝ)) := by
  refine Real.rpow_lt_rpow_left_iff (by norm_num : (1 : ℝ) < 2) |>.mpr ?_
  have hud : ((d * l + 3 : ℕ) : ℝ) ≤ (u : ℝ) := by exact_mod_cast hu
  have hdR : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  push_cast at hud
  push_cast
  nlinarith [hud, hdR]

/-- In the second regime the radius `2^{E+1}` with `E = -2du` is below the separation `1/T²`. -/
lemma lp_exp_case2 {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1 / 8) {d u L l : ℕ} (hd : 2 ≤ d)
    (hLl : l ≤ L) (hLu : uScale ρ L ≤ u) (hl : iwC0 ρ < l) {T : ℕ} (hT : 0 < T)
    (hT4 : 4 * (T : ℝ) ^ 2 ≤ (2 : ℝ) ^ (2 * (2 : ℝ) ^ (2 * ρ * (l : ℝ)))) :
    (2 : ℝ) ^ (-(2 * (d : ℝ) * (u : ℝ)) + 1) < (1 : ℝ) / (T : ℝ) ^ 2 := by
  have hlR : (iwC0 ρ : ℝ) < (l : ℝ) := by exact_mod_cast hl
  have h4 : 4 / ρ ^ 2 ≤ (iwC0 ρ : ℝ) := lp_iwC0_ge hρ
  -- `Z ≥ 2`, where `Z = 2^{2ρl}`
  have hZ : 2 ≤ (2 : ℝ) ^ (2 * ρ * (l : ℝ)) := by
    have h1 : 64 ≤ 2 * ρ * (l : ℝ) := by
      have h2 : 4 / ρ ^ 2 < (l : ℝ) := lt_of_le_of_lt h4 hlR
      have h2' : 4 < (l : ℝ) * ρ ^ 2 := by
        rwa [div_lt_iff₀ (by positivity : (0 : ℝ) < ρ ^ 2)] at h2
      have h3 : 8 / ρ ≤ 2 * ρ * (l : ℝ) := by
        rw [div_le_iff₀ hρ]
        nlinarith [h2']
      have h5 : 64 ≤ 8 / ρ := by
        rw [le_div_iff₀ hρ]
        nlinarith [hρ1]
      linarith
    have h6 : (2 : ℝ) ^ ((6 : ℕ) : ℝ) ≤ (2 : ℝ) ^ (2 * ρ * (l : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (by push_cast; linarith)
    have h7 : (2 : ℝ) ≤ (2 : ℝ) ^ ((6 : ℕ) : ℝ) := by
      rw [Real.rpow_natCast]
      norm_num
    linarith
  -- `2^{2ρl} - 1 < uScale ρ L ≤ u`
  have hfloor : (2 : ℝ) ^ (2 * ρ * (L : ℝ)) - 1 < (uScale ρ L : ℝ) := by
    rw [uScale, Work.Analysis.EndVar.scaleCount, Int.floor_toNat, Nat.cast_one, one_mul]
    exact Nat.sub_one_lt_floor _
  have hmono : (2 : ℝ) ^ (2 * ρ * (l : ℝ)) ≤ (2 : ℝ) ^ (2 * ρ * (L : ℝ)) := by
    refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
    have : (l : ℝ) ≤ (L : ℝ) := by exact_mod_cast hLl
    nlinarith [hρ.le]
  -- `du ≥ 2^{2ρl}`
  have hdu : (2 : ℝ) ^ (2 * ρ * (l : ℝ)) ≤ (d : ℝ) * (u : ℝ) := by
    have h2 : (uScale ρ L : ℝ) ≤ (u : ℝ) := by exact_mod_cast hLu
    have hdR : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
    have hZnn : (0 : ℝ) < (2 : ℝ) ^ (2 * ρ * (l : ℝ)) := Real.rpow_pos_of_pos (by norm_num) _
    nlinarith [hfloor, hmono, h2, hdR, hZ, hZnn]
  have hTpos : (0 : ℝ) < (T : ℝ) ^ 2 := by positivity
  have hbig : 4 * (T : ℝ) ^ 2 ≤ (2 : ℝ) ^ (2 * (d : ℝ) * (u : ℝ)) :=
    hT4.trans (Real.rpow_le_rpow_of_exponent_le (by norm_num)
      (by linarith [hdu] : 2 * (2 : ℝ) ^ (2 * ρ * (l : ℝ)) ≤ 2 * (d : ℝ) * (u : ℝ)))
  -- `1/T² ≥ 4/2^{2du}`
  have hge : (4 : ℝ) / (2 : ℝ) ^ (2 * (d : ℝ) * (u : ℝ)) ≤ 1 / (T : ℝ) ^ 2 := by
    rw [div_le_div_iff₀ (Real.rpow_pos_of_pos (by norm_num) _) hTpos]
    linarith [hbig]
  -- `4/2^{2du} > 2^{E+1}`
  have hlt : (2 : ℝ) ^ (-(2 * (d : ℝ) * (u : ℝ)) + 1)
      < (4 : ℝ) / (2 : ℝ) ^ (2 * (d : ℝ) * (u : ℝ)) := by
    have hpos : (0 : ℝ) < (2 : ℝ) ^ (2 * (d : ℝ) * (u : ℝ)) :=
      Real.rpow_pos_of_pos (by norm_num) _
    have h2 : (2 : ℝ) ^ (-(2 * (d : ℝ) * (u : ℝ)) + 1)
        = 2 / (2 : ℝ) ^ (2 * (d : ℝ) * (u : ℝ)) := by
      rw [Real.rpow_add (by norm_num : (0 : ℝ) < 2), Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2),
        Real.rpow_one, inv_mul_eq_div]
    rw [h2]
    exact div_lt_div_of_pos_right (by norm_num) hpos
  linarith [hge, hlt]

/-- **The non-aliasing of the exact-height frequencies at the repaired window.** -/
theorem LpNonAliasAtWindow (ρ : ℝ) (d : ℕ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1 / 8) (hd : 2 ≤ d)
    (l₂ k₁ k₂ : ℕ) :
    NonAliasing (-((d : ℤ) * 2 * (loMixedU ρ d l₂ k₁ k₂ : ℤ))) (diffFreqs ρ l₂) := by
  intro α hα β hβ θ hθ θ' hθ' heq
  set u : ℕ := loMixedU ρ d l₂ k₁ k₂ with hudef
  set L : ℕ := max (max 0 l₂) (max k₁ k₂) with hLdef
  have hLunfold : L = max (max 0 l₂) (max k₁ k₂) := hLdef
  have hu_lc : uScale ρ L ≤ u := by
    rw [hudef, loMixedU, ← hLunfold]
    exact le_max_left _ _
  have hu_d : d * l₂ + 3 ≤ u := by
    rw [hudef, loMixedU, ← hLunfold]
    exact le_max_right _ _
  have hL : l₂ ≤ L := by
    rw [hLunfold]
    exact le_trans (le_max_right 0 l₂) (le_max_left _ _)
  -- `α - β` is the class of `θ' - θ`
  have hsub : α - β = ((θ' - θ : ℝ) : Work.Analysis.IonescuWainger.Circle) := by
    rw [AddCircle.coe_sub (1 : ℝ) θ' θ, sub_eq_sub_iff_add_eq_add, heq, add_comm]
  -- the exponent `E = -2du`
  have hEr : ((-((d : ℤ) * 2 * (u : ℤ)) : ℤ) : ℝ) = -(2 * (d : ℝ) * (u : ℝ)) := by
    push_cast
    ring
  have hθr : |θ| ≤ (2 : ℝ) ^ (-(2 * (d : ℝ) * (u : ℝ))) := by
    have h := hθ
    rw [realArc, Set.mem_Icc] at h
    have hb : |θ| ≤ (2 : ℝ) ^ (-((d : ℤ) * 2 * (u : ℤ))) := abs_le.mpr h
    rw [lp_zpow_two_eq_rpow, hEr] at hb
    exact hb
  have hθ'r : |θ'| ≤ (2 : ℝ) ^ (-(2 * (d : ℝ) * (u : ℝ))) := by
    have h := hθ'
    rw [realArc, Set.mem_Icc] at h
    have hb : |θ'| ≤ (2 : ℝ) ^ (-((d : ℤ) * 2 * (u : ℤ))) := abs_le.mpr h
    rw [lp_zpow_two_eq_rpow, hEr] at hb
    exact hb
  have hEadd : (2 : ℝ) ^ (-(2 * (d : ℝ) * (u : ℝ)) + 1)
      = 2 * (2 : ℝ) ^ (-(2 * (d : ℝ) * (u : ℝ))) := by
    rw [Real.rpow_add_one (by norm_num : (2 : ℝ) ≠ 0)]
    ring
  have hdd : |θ' - θ| ≤ (2 : ℝ) ^ (-(2 * (d : ℝ) * (u : ℝ)) + 1) := by
    have h1 : |θ' - θ| ≤ |θ'| + |θ| := abs_sub θ' θ
    have h2 : |θ'| + |θ| ≤ (2 : ℝ) ^ (-(2 * (d : ℝ) * (u : ℝ)))
        + (2 : ℝ) ^ (-(2 * (d : ℝ) * (u : ℝ))) := add_le_add hθ'r hθr
    rw [hEadd]
    linarith
  have hnorm : ‖α - β‖ ≤ |θ' - θ| := by
    rw [hsub]
    exact lp_norm_coe_circle_le_abs (θ' - θ)
  rcases eq_or_ne α β with hAB | hAB
  · refine ⟨hAB, ?_⟩
    have hdd1 : |θ' - θ| < 1 := by
      have hElt : -(2 * (d : ℝ) * (u : ℝ)) + 1 < 0 := by
        have hd1 : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast (by omega : 1 ≤ d)
        have hu1 : (1 : ℝ) ≤ (u : ℝ) := by
          have : 1 ≤ u := by omega
          exact_mod_cast this
        nlinarith
      have hlt : (2 : ℝ) ^ (-(2 * (d : ℝ) * (u : ℝ)) + 1) < 1 := by
        have h := (Real.rpow_lt_rpow_left_iff (by norm_num : (1 : ℝ) < 2)).mpr hElt
        rwa [Real.rpow_zero] at h
      linarith
    have h0 : ((θ' - θ : ℝ) : Work.Analysis.IonescuWainger.Circle) = 0 := by
      rw [← hsub, hAB, sub_self]
    obtain ⟨n, hn⟩ := (AddCircle.coe_eq_zero_iff (1 : ℝ)).mp h0
    have hnR : θ' - θ = (n : ℝ) := by rw [← hn, zsmul_one]
    have hnabs : |(n : ℝ)| < 1 := by rw [← hnR]; exact hdd1
    have hn0 : n = 0 := by
      obtain ⟨h1, h2⟩ := abs_lt.mp hnabs
      have h1' : (-1 : ℤ) < n := by exact_mod_cast h1
      have h2' : n < (1 : ℤ) := by exact_mod_cast h2
      omega
    have hθθ' : θ = θ' := by
      have hz : θ' - θ = 0 := by rw [hnR, hn0]; norm_num
      linarith
    exact hθθ'
  · exfalso
    have hsep : (2 : ℝ) ^ (-(2 * (d : ℝ) * (u : ℝ)) + 1) < ‖α - β‖ := by
      by_cases hlc : l₂ ≤ iwC0 ρ
      · have hB : 0 < 2 ^ l₂ := by positivity
        have hcast : (1 : ℝ) / ((2 ^ l₂ : ℕ) : ℝ) ^ 2 = (2 : ℝ) ^ (-((2 * l₂ : ℕ) : ℝ)) := by
          have h1 : ((2 ^ l₂ : ℕ) : ℝ) = (2 : ℝ) ^ l₂ := by push_cast; ring
          have h2 : ((2 : ℝ) ^ l₂) ^ 2 = (2 : ℝ) ^ (((2 * l₂ : ℕ)) : ℝ) := by
            rw [← Real.rpow_natCast (2 : ℝ) l₂]
            rw [lp_rpow_pow (2 : ℝ) (l₂ : ℝ) (by norm_num) 2]
            congr 1
            push_cast
            ring
          rw [h1, h2, one_div, Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
        have hsep1 : (1 : ℝ) / ((2 ^ l₂ : ℕ) : ℝ) ^ 2 ≤ ‖α - β‖ :=
          lp_sep_le_of_den (ρ := ρ) (l := l₂) (B := 2 ^ l₂) hB hα hβ
            (fun q hq _ => lp_iwP_le_two_pow hq hlc)
            (fun q hq _ => lp_iwP_le_two_pow hq hlc) hAB
        refine lt_of_lt_of_le ?_ hsep1
        rw [hcast]
        exact lp_exp_case1 hd hu_d
      · have hl' : iwC0 ρ < l₂ := not_le.mp hlc
        set T : ℕ := iwQ0 ρ l₂ * (2 ^ l₂) ^ (iwD ρ * iwD ρ) with hTdef
        have hTpos : 0 < T := by
          rw [hTdef]
          exact Nat.mul_pos (Nat.pos_of_ne_zero (iwQ0_ne_zero ρ l₂)) (by positivity)
        have hsep1 : (1 : ℝ) / (T : ℝ) ^ 2 ≤ ‖α - β‖ := by
          refine lp_sep_le_of_den (ρ := ρ) (l := l₂) (B := T) hTpos hα hβ ?_ ?_ hAB
          · intro q hq _
            rw [mem_iwP] at hq
            rcases hq with ⟨hl2, -, -⟩ | ⟨-, hq⟩
            · exact absurd hl2 (not_le.mpr hl')
            · exact lp_iwPconcrete_le hq
          · intro q hq _
            rw [mem_iwP] at hq
            rcases hq with ⟨hl2, -, -⟩ | ⟨-, hq⟩
            · exact absurd hl2 (not_le.mpr hl')
            · exact lp_iwPconcrete_le hq
        refine lt_of_lt_of_le ?_ hsep1
        have hT4 : 4 * (T : ℝ) ^ 2 ≤ (2 : ℝ) ^ (2 * (2 : ℝ) ^ (2 * ρ * (l₂ : ℝ))) := by
          rw [hTdef]
          exact lp_T_le hρ hρ1 hl'
        exact lp_exp_case2 hρ hρ1 hd hL hu_lc hl' hTpos hT4
    linarith [hsep, hnorm, hdd]

end

end Work.KMTAreas.A7
