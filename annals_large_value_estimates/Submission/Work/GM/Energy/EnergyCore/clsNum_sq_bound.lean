import Mathlib
import Submission.Work.GM.Energy.EnergyCore.FourthMomentDefs

/-!
# GM §11: `(clsNum W)² ⪅ 1`

In the proof of the discrete fourth moment (GM Lemma 11.6) the pairs `(t₁,t₂) ∈ W²` are
split into `clsNum W = ⌊log₂ |W|²⌋ + 1` dyadic classes.  Since `W ⊆ [0,T]` is `1`-separated,
`|W| ≤ T+1`, so `clsNum W ⪅ log T`, and `(log T)² ⪅ T^δ` for every `δ > 0`: this file
records that the factor `clsNum W` costs only `T^(ε/2)`.

The proof of the cardinality bound is the familiar one: the integer parts `⌊t⌋` of the
elements of `W` are pairwise distinct (two reals with the same integer part are at distance
`< 1`), and they all lie in `{0, …, ⌊T⌋}`.
-/

open Finset

set_option autoImplicit false

namespace Work.GM.Energy.EnergyCore

/-- Two reals with the same integer part are at distance `< 1`. -/
private lemma abs_sub_lt_one_of_floor_eq {x y : ℝ} (h : ⌊x⌋ = ⌊y⌋) : |x - y| < 1 := by
  rw [abs_lt]
  constructor
  · have hle : (⌊x⌋ : ℝ) ≤ x := Int.floor_le x
    have hlt : y < (⌊y⌋ : ℝ) + 1 := Int.lt_floor_add_one y
    rw [← h] at hlt
    linarith
  · have hle : (⌊y⌋ : ℝ) ≤ y := Int.floor_le y
    have hlt : x < (⌊x⌋ : ℝ) + 1 := Int.lt_floor_add_one x
    rw [h] at hlt
    linarith

/-- A `1`-separated finite set of reals contained in `[0,T]` has at most `T+1` elements. -/
theorem card_le_add_one_of_separated {W : Finset ℝ} {T : ℝ} (hT : 0 ≤ T)
    (hW : ∀ t ∈ W, t ∈ Set.Icc 0 T) (hsep : Submission.GM.Separated W 1) :
    (W.card : ℝ) ≤ T + 1 := by
  classical
  -- the integer parts are pairwise distinct, hence `|W| ≤ #{0, …, ⌊T⌋}`
  have hinj : Set.InjOn (fun x : ℝ => ⌊x⌋) (W : Set ℝ) := by
    intro x hx y hy hxy
    have hxy' : ⌊x⌋ = ⌊y⌋ := hxy
    by_contra hne
    have h1 : (1 : ℝ) ≤ |x - y| := hsep x hx y hy hne
    have h2 : |x - y| < 1 := abs_sub_lt_one_of_floor_eq hxy'
    linarith
  have hcard : W.card = (W.image (fun x : ℝ => ⌊x⌋)).card :=
    (Finset.card_image_of_injOn hinj).symm
  have hsub : W.image (fun x : ℝ => ⌊x⌋) ⊆ Finset.Icc (0 : ℤ) ⌊T⌋ := by
    intro n hn
    rcases Finset.mem_image.mp hn with ⟨x, hx, rfl⟩
    have hx' := hW x hx
    rw [Set.mem_Icc] at hx'
    simp only [Finset.mem_Icc]
    exact ⟨Int.floor_nonneg.mpr hx'.1, Int.floor_mono hx'.2⟩
  have hcardle : W.card ≤ (⌊T⌋ + 1).toNat := by
    calc W.card = (W.image (fun x : ℝ => ⌊x⌋)).card := hcard
      _ ≤ (Finset.Icc (0 : ℤ) ⌊T⌋).card := Finset.card_le_card hsub
      _ = (⌊T⌋ + 1).toNat := by
            rw [Int.card_Icc]
            congr 1
            ring
  have hZ : (W.card : ℤ) ≤ ⌊T⌋ + 1 := by
    have hTf : (0 : ℤ) ≤ ⌊T⌋ + 1 := by
      have := Int.floor_nonneg.mpr hT
      omega
    have hZ1 : (W.card : ℤ) ≤ ((⌊T⌋ + 1).toNat : ℤ) := by exact_mod_cast hcardle
    rwa [Int.toNat_of_nonneg hTf] at hZ1
  have hR : (W.card : ℝ) ≤ (⌊T⌋ : ℝ) + 1 := by exact_mod_cast hZ
  linarith [Int.floor_le T]

/-- GM §11: for any `ε > 0` the number of dyadic classes `clsNum W` costs only `T^(ε/2)`. -/
theorem clsNum_sq_bound (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (T : ℝ), 1 ≤ T → ∀ (W : Finset ℝ),
      (∀ t ∈ W, t ∈ Set.Icc 0 T) → Submission.GM.Separated W 1 →
      (clsNum W : ℝ) ^ 2 ≤ C * T ^ (ε / 2) := by
  refine ⟨(2 * 3 ^ (ε / 4) / ((ε / 4) * Real.log 2) + 3) ^ 2, ?_, ?_⟩
  · positivity
  · intro T hT W hW hsep
    have hT0 : 0 ≤ T := le_trans zero_le_one hT
    have hTpos : 0 < T := lt_of_lt_of_le zero_lt_one hT
    have hε4 : 0 < ε / 4 := by linarith
    have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hcard : (W.card : ℝ) ≤ T + 1 := card_le_add_one_of_separated hT0 hW hsep
    -- `log₂ |W| ≤ log (T+2)/log 2`
    have hk : (Nat.log 2 W.card : ℝ) ≤ Real.log (T + 2) / Real.log 2 := by
      have hpow : (2 : ℝ) ^ Nat.log 2 W.card ≤ (W.card : ℝ) + 1 := by
        have h := Nat.pow_log_le_add_one 2 W.card
        have h' : ((2 : ℕ) ^ Nat.log 2 W.card : ℝ) ≤ ((W.card + 1 : ℕ) : ℝ) := by
          exact_mod_cast h
        simpa [Nat.cast_pow, Nat.cast_add, Nat.cast_one] using h'
      have hlog : Real.log ((2 : ℝ) ^ Nat.log 2 W.card) ≤ Real.log (T + 2) := by
        apply Real.log_le_log (by positivity)
        linarith
      rw [Real.log_pow] at hlog
      rw [le_div_iff₀ hlog2]
      linarith
    -- `log (T+2) ≤ 3^(ε/4) T^(ε/4)/(ε/4)`
    have hlogbound : Real.log (T + 2) ≤ 3 ^ (ε / 4) * T ^ (ε / 4) / (ε / 4) := by
      have h1 : Real.log (T + 2) ≤ (T + 2) ^ (ε / 4) / (ε / 4) :=
        Real.log_le_rpow_div (by linarith) hε4
      have h2 : (T + 2) ^ (ε / 4) ≤ 3 ^ (ε / 4) * T ^ (ε / 4) := by
        have h3 : (T + 2) ≤ 3 * T := by linarith
        have h4 : (T + 2) ^ (ε / 4) ≤ (3 * T) ^ (ε / 4) :=
          Real.rpow_le_rpow (by linarith) h3 (le_of_lt hε4)
        rwa [Real.mul_rpow (by norm_num) (le_of_lt hTpos)] at h4
      calc Real.log (T + 2) ≤ (T + 2) ^ (ε / 4) / (ε / 4) := h1
        _ ≤ 3 ^ (ε / 4) * T ^ (ε / 4) / (ε / 4) :=
              div_le_div_of_nonneg_right h2 (le_of_lt hε4)
    have hk2 : (Nat.log 2 W.card : ℝ) ≤
        3 ^ (ε / 4) * T ^ (ε / 4) / ((ε / 4) * Real.log 2) := by
      calc (Nat.log 2 W.card : ℝ) ≤ Real.log (T + 2) / Real.log 2 := hk
        _ ≤ (3 ^ (ε / 4) * T ^ (ε / 4) / (ε / 4)) / Real.log 2 :=
              div_le_div_of_nonneg_right hlogbound (le_of_lt hlog2)
        _ = 3 ^ (ε / 4) * T ^ (ε / 4) / ((ε / 4) * Real.log 2) := by ring
    -- `clsNum W ≤ 2 log₂ |W| + 3`
    have hcls : (clsNum W : ℝ) ≤ 2 * (Nat.log 2 W.card : ℝ) + 3 := by
      have hnat : clsNum W ≤ 2 * Nat.log 2 W.card + 3 := by
        rw [clsNum]
        have hbase : W.card * W.card ≤ 2 ^ (2 * Nat.log 2 W.card + 2) := by
          have hlt : W.card < 2 ^ (Nat.log 2 W.card + 1) := by
            simpa [Nat.succ_eq_add_one] using
              (Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) W.card)
          calc W.card * W.card
              ≤ 2 ^ (Nat.log 2 W.card + 1) * 2 ^ (Nat.log 2 W.card + 1) :=
                Nat.mul_le_mul (le_of_lt hlt) (le_of_lt hlt)
            _ = 2 ^ (2 * Nat.log 2 W.card + 2) := by
                  rw [← Nat.pow_add]; ring_nf
        have hlog : Nat.log 2 (W.card * W.card)
            ≤ Nat.log 2 (2 ^ (2 * Nat.log 2 W.card + 2)) := Nat.log_mono_right hbase
        rw [Nat.log_pow (by norm_num)] at hlog
        omega
      calc (clsNum W : ℝ) ≤ ((2 * Nat.log 2 W.card + 3 : ℕ) : ℝ) := by exact_mod_cast hnat
        _ = 2 * (Nat.log 2 W.card : ℝ) + 3 := by push_cast; ring
    -- assemble: `clsNum W ≤ B · T^(ε/4)`
    have hTδ1 : 1 ≤ T ^ (ε / 4) := Real.one_le_rpow hT (le_of_lt hε4)
    have hclsB : (clsNum W : ℝ) ≤
        (2 * 3 ^ (ε / 4) / ((ε / 4) * Real.log 2) + 3) * T ^ (ε / 4) := by
      have h1 : 2 * (Nat.log 2 W.card : ℝ) + 3 ≤
          2 * (3 ^ (ε / 4) * T ^ (ε / 4) / ((ε / 4) * Real.log 2)) + 3 := by linarith
      have h2 : 2 * (3 ^ (ε / 4) * T ^ (ε / 4) / ((ε / 4) * Real.log 2)) =
          (2 * 3 ^ (ε / 4) / ((ε / 4) * Real.log 2)) * T ^ (ε / 4) := by ring
      rw [h2] at h1
      have h3 : (2 * 3 ^ (ε / 4) / ((ε / 4) * Real.log 2)) * T ^ (ε / 4) + 3 ≤
          (2 * 3 ^ (ε / 4) / ((ε / 4) * Real.log 2) + 3) * T ^ (ε / 4) := by
        rw [add_mul]
        refine add_le_add le_rfl ?_
        nlinarith [hTδ1]
      linarith [hcls, h1, h3]
    -- square
    have hsq : (clsNum W : ℝ) ^ 2 ≤
        ((2 * 3 ^ (ε / 4) / ((ε / 4) * Real.log 2) + 3) * T ^ (ε / 4)) ^ 2 :=
      pow_le_pow_left₀ (by positivity) hclsB 2
    have hpow : (T ^ (ε / 4)) ^ 2 = T ^ (ε / 2) := by
      rw [← Real.rpow_natCast (T ^ (ε / 4)) 2, ← Real.rpow_mul (le_of_lt hTpos)]
      congr 1
      push_cast
      ring
    calc (clsNum W : ℝ) ^ 2
        ≤ ((2 * 3 ^ (ε / 4) / ((ε / 4) * Real.log 2) + 3) * T ^ (ε / 4)) ^ 2 := hsq
      _ = (2 * 3 ^ (ε / 4) / ((ε / 4) * Real.log 2) + 3) ^ 2 * (T ^ (ε / 4)) ^ 2 := by
            rw [mul_pow]
      _ = (2 * 3 ^ (ε / 4) / ((ε / 4) * Real.log 2) + 3) ^ 2 * T ^ (ε / 2) := by rw [hpow]

end Work.GM.Energy.EnergyCore
