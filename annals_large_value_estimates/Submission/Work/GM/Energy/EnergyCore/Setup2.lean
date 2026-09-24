import Mathlib
import Submission.Work.GM.Energy.Defs

/-!
# Energy area, §11 large-GCD part: shared vocabulary

Small definitions and elementary facts shared by the `EnergyCore` lemmas:

* `Md N d = ⌈N/d⌉` (the scale at which the coprime parts of a pair of integers with
  `gcd = d` live),
* the basic arithmetic of `M N = N^{6/5}`,
* `|W| ≤ T + 1` for a `1`-separated `W ⊆ [0,T]`,
* one logarithmic loss `1 + log(2N) ≤ c_ε N^{ε/5}`.
-/

namespace Work.GM.Energy.EnergyCore

open Complex Finset
open scoped BigOperators
set_option autoImplicit false

/-- `⌈N/d⌉` as a natural number. -/
noncomputable def Md (N d : ℕ) : ℕ := ⌈(N : ℝ) / (d : ℝ)⌉₊

theorem le_Md (N d : ℕ) : (N : ℝ) / (d : ℝ) ≤ (Md N d : ℝ) := Nat.le_ceil _

theorem Md_lt_add_one (N d : ℕ) : (Md N d : ℝ) < (N : ℝ) / (d : ℝ) + 1 := by
  have h : (0 : ℝ) ≤ (N : ℝ) / (d : ℝ) :=
    div_nonneg (by positivity) (by positivity)
  exact Nat.ceil_lt_add_one_of_gt_neg_one (by linarith)

theorem Md_pos {N d : ℕ} (hN : 1 ≤ N) (hd : 1 ≤ d) : 1 ≤ Md N d := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hN)
  have hd' : (0 : ℝ) < d := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hd)
  have h : 0 < (N : ℝ) / (d : ℝ) := div_pos hN' hd'
  have := Nat.ceil_pos.mpr h
  unfold Md
  omega

theorem Md_le_div_add_one (N d : ℕ) : (Md N d : ℝ) ≤ (N : ℝ) / (d : ℝ) + 1 :=
  (Md_lt_add_one N d).le

/-- Two reals with equal integer parts are at distance strictly less than one. -/
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
theorem setup2_card_le_add_one {W : Finset ℝ} {T : ℝ} (hT : 0 ≤ T)
    (hW : ∀ t ∈ W, t ∈ Set.Icc 0 T) (hsep : Submission.GM.Separated W 1) :
    (W.card : ℝ) ≤ T + 1 := by
  classical
  have hmem : ∀ t ∈ W, (0 : ℝ) ≤ t ∧ t ≤ T := fun t ht => hW t ht
  have hinj : Set.InjOn (fun t : ℝ => ⌊t⌋₊) (W : Set ℝ) := by
    intro x hx y hy hxy
    have hf : ⌊x⌋₊ = ⌊y⌋₊ := hxy
    by_contra hne
    have h1 : 1 ≤ |x - y| := hsep x hx y hy hne
    have hx0 : (0 : ℝ) ≤ x := (hmem x hx).1
    have hy0 : (0 : ℝ) ≤ y := (hmem y hy).1
    have hx1 : ((⌊x⌋₊ : ℕ) : ℝ) ≤ x := Nat.floor_le hx0
    have hx2 : x < ((⌊x⌋₊ : ℕ) : ℝ) + 1 := Nat.lt_floor_add_one x
    have hy1 : ((⌊x⌋₊ : ℕ) : ℝ) ≤ y := by rw [hf]; exact Nat.floor_le hy0
    have hy2 : y < ((⌊x⌋₊ : ℕ) : ℝ) + 1 := by rw [hf]; exact Nat.lt_floor_add_one y
    have hlt : |x - y| < 1 := by
      rw [abs_lt]
      constructor <;> linarith
    linarith
  have hcard : (W.image (fun t : ℝ => ⌊t⌋₊)).card = W.card :=
    Finset.card_image_of_injOn hinj
  have hsub : W.image (fun t : ℝ => ⌊t⌋₊) ⊆ Finset.range (⌊T⌋₊ + 1) := by
    intro n hn
    rcases Finset.mem_image.mp hn with ⟨t, ht, rfl⟩
    rw [Finset.mem_range]
    have hmono : ⌊t⌋₊ ≤ ⌊T⌋₊ := Nat.floor_mono (hmem t ht).2
    omega
  have hnat : W.card ≤ ⌊T⌋₊ + 1 := by
    rw [← hcard]
    calc (W.image (fun t : ℝ => ⌊t⌋₊)).card ≤ (Finset.range (⌊T⌋₊ + 1)).card :=
          Finset.card_le_card hsub
      _ = ⌊T⌋₊ + 1 := Finset.card_range _
  have h4 : ((W.card : ℕ) : ℝ) ≤ ((⌊T⌋₊ + 1 : ℕ) : ℝ) := by exact_mod_cast hnat
  have hcast : ((⌊T⌋₊ + 1 : ℕ) : ℝ) = (⌊T⌋₊ : ℝ) + 1 := by push_cast; ring
  have hfl : (⌊T⌋₊ : ℝ) ≤ T := Nat.floor_le hT
  rw [hcast] at h4
  linarith

theorem one_le_MN {N : ℕ} (hN : 1 ≤ N) : 1 ≤ Submission.LargeValues.M N := by
  rw [Submission.LargeValues.M]
  exact Real.one_le_rpow (by exact_mod_cast hN) (by norm_num)

theorem MN_ge_N {N : ℕ} (hN : 1 ≤ N) : (N : ℝ) ≤ Submission.LargeValues.M N := by
  rw [Submission.LargeValues.M]
  have h : (1 : ℝ) ≤ N := by exact_mod_cast hN
  calc (N : ℝ) = (N : ℝ) ^ (1 : ℝ) := by rw [Real.rpow_one]
    _ ≤ (N : ℝ) ^ (6 / 5 : ℝ) := Real.rpow_le_rpow_of_exponent_le h (by norm_num)

theorem MN_rpow_half (N : ℕ) : (Submission.LargeValues.M N) ^ ((1 : ℝ) / 2) =
    (N : ℝ) ^ ((3 : ℝ) / 5) := by
  rw [Submission.LargeValues.M, ← Real.rpow_mul (by positivity : (0 : ℝ) ≤ (N : ℝ))]
  norm_num

theorem MN_rpow_quarter (N : ℕ) : (Submission.LargeValues.M N) ^ ((1 : ℝ) / 4) =
    (N : ℝ) ^ ((3 : ℝ) / 10) := by
  rw [Submission.LargeValues.M, ← Real.rpow_mul (by positivity : (0 : ℝ) ≤ (N : ℝ))]
  norm_num

theorem MN_rpow_eps (ε : ℝ) (N : ℕ) : (Submission.LargeValues.M N) ^ ε =
    (N : ℝ) ^ ((6 : ℝ) / 5 * ε) := by
  rw [Submission.LargeValues.M, ← Real.rpow_mul (by positivity : (0 : ℝ) ≤ (N : ℝ))]

theorem MN_rpow_half_le_N {N : ℕ} (hN : 1 ≤ N) :
    (Submission.LargeValues.M N) ^ ((1 : ℝ) / 2) ≤ (N : ℝ) := by
  rw [MN_rpow_half]
  have h : (1 : ℝ) ≤ N := by exact_mod_cast hN
  calc (N : ℝ) ^ ((3 : ℝ) / 5) ≤ (N : ℝ) ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le h (by norm_num)
    _ = (N : ℝ) := Real.rpow_one _

/-- One logarithmic loss, absorbed into `N^{ε/5}` with an explicit constant. -/
theorem exists_log_bound (ε : ℝ) (hε : 0 < ε) :
    ∃ c : ℝ, 0 < c ∧ ∀ N : ℕ, 1 ≤ N →
      1 + Real.log (2 * (N : ℝ)) ≤ c * (N : ℝ) ^ (ε / 5) := by
  have hε5 : (0 : ℝ) < ε / 5 := by linarith
  refine ⟨1 + 2 ^ (ε / 5) / (ε / 5), by positivity, ?_⟩
  intro N hN
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have h2N : (0 : ℝ) ≤ 2 * (N : ℝ) := by positivity
  have hlog : Real.log (2 * (N : ℝ)) ≤ (2 * (N : ℝ)) ^ (ε / 5) / (ε / 5) :=
    Real.log_le_rpow_div h2N hε5
  have hrw : (2 * (N : ℝ)) ^ (ε / 5) = 2 ^ (ε / 5) * (N : ℝ) ^ (ε / 5) :=
    Real.mul_rpow (by norm_num) hN0.le
  have hN1 : (1 : ℝ) ≤ (N : ℝ) ^ (ε / 5) := Real.one_le_rpow (by exact_mod_cast hN) hε5.le
  have hlog' : Real.log (2 * (N : ℝ)) ≤ (2 ^ (ε / 5) / (ε / 5)) * (N : ℝ) ^ (ε / 5) := by
    have h := hlog
    rw [hrw] at h
    calc Real.log (2 * (N : ℝ)) ≤ 2 ^ (ε / 5) * (N : ℝ) ^ (ε / 5) / (ε / 5) := h
      _ = (2 ^ (ε / 5) / (ε / 5)) * (N : ℝ) ^ (ε / 5) := by rw [div_mul_eq_mul_div]
  have h1 : (1 : ℝ) ≤ (N : ℝ) ^ (ε / 5) := hN1
  have h2 : (1 : ℝ) * (N : ℝ) ^ (ε / 5) ≤
      (1 + 2 ^ (ε / 5) / (ε / 5)) * (N : ℝ) ^ (ε / 5) := by
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    linarith [show (0:ℝ) ≤ 2 ^ (ε / 5) / (ε / 5) by positivity]
  linarith [hlog', h1, h2]

end Work.GM.Energy.EnergyCore
