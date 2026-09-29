import Mathlib
import Submission.Work.TMC16Core.Core.uni_res5_aux

/-!
# `Core.res_bij`: the resonant windows are the image of the index block `resK`

The site map `resSite q n h ℓ : k ↦ k + resLsh h ℓ k * q n` (with
`resLsh h ℓ k = 0` for `k < h` and `= ℓ - 1` for `k ≥ h`) sends the block of indices
`resK q n h = [-(h:ℤ), 2 q n - h - 1]` bijectively onto the union `resW q n h ℓ` of AJ's
two resonant windows; it is injective there, strictly shifts the second half of the block
by `(ℓ-1) q n`, and lands inside the range `[-(h:ℤ), (ℓ+1) q n - (h:ℤ) - 1]`.

The only arithmetic input is `h ≤ 5 q n / 8` (hence `h ≤ q n`); the hypothesis
`3 q n / 5 ≤ h` is not needed for these combinatorial statements.
-/

namespace Work.TMC16Core.Core

open Work.TMC16Core

noncomputable section

/-! ## Elementary properties of `resLsh` / `resSite` -/

private lemma resLsh_of_lt {h ℓ : ℕ} {k : ℤ} (hk : k < (h : ℤ)) : resLsh h ℓ k = 0 :=
  if_pos hk

private lemma resLsh_of_le {h ℓ : ℕ} {k : ℤ} (hk : (h : ℤ) ≤ k) :
    resLsh h ℓ k = (ℓ : ℤ) - 1 :=
  if_neg (not_lt.mpr hk)

private lemma resSite_of_lt {qn h ℓ : ℕ} {k : ℤ} (hk : k < (h : ℤ)) :
    resSite qn h ℓ k = k := by
  simp [resSite, resLsh_of_lt hk]

private lemma resSite_of_le {qn h ℓ : ℕ} {k : ℤ} (hk : (h : ℤ) ≤ k) :
    resSite qn h ℓ k = k + ((ℓ : ℤ) - 1) * (qn : ℤ) := by
  simp [resSite, resLsh_of_le hk]

/-- `h ≤ 5 q n / 8` gives `h ≤ q n` (in `ℤ`). -/
private lemma h_le_qn {qn h : ℕ} (hh' : h ≤ 5 * qn / 8) : (h : ℤ) ≤ (qn : ℤ) := by
  have h8 : h * 8 ≤ 5 * qn := (Nat.le_div_iff_mul_le (by norm_num : 0 < 8)).mp hh'
  have : h ≤ qn := by omega
  exact_mod_cast this

/-- From `h ≤ q n` and `1 ≤ ℓ`: `2 h ≤ (ℓ + 1) q n`. -/
private lemma two_h_le {qn h ℓ : ℕ} (hℓ : 1 ≤ ℓ) (hqn : (h : ℤ) ≤ (qn : ℤ)) :
    2 * (h : ℤ) ≤ ((ℓ : ℤ) + 1) * (qn : ℤ) := by
  have hl1 : (0 : ℤ) ≤ (ℓ : ℤ) - 1 := by omega
  have hq0 : (0 : ℤ) ≤ (qn : ℤ) := by omega
  nlinarith [mul_nonneg hl1 hq0, hqn]

private lemma add_shift {qn h ℓ : ℕ} :
    (2 * (qn : ℤ) - (h : ℤ) - 1) + ((ℓ : ℤ) - 1) * (qn : ℤ)
      = ((ℓ : ℤ) + 1) * (qn : ℤ) - (h : ℤ) - 1 := by ring

private lemma shift_nonneg {qn ℓ : ℕ} (hℓ : 1 ≤ ℓ) :
    (0 : ℤ) ≤ ((ℓ : ℤ) - 1) * (qn : ℤ) :=
  mul_nonneg (by omega) (by omega)

/-! ## The four combinatorial statements -/

/-- `resSite` maps the index block `resK` onto the union `resW` of AJ's windows. -/
private lemma image_resSite {qn h ℓ : ℕ} (hℓ : 1 ≤ ℓ) (hqn : (h : ℤ) ≤ (qn : ℤ)) :
    (resK qn h).image (resSite qn h ℓ) = resW qn h ℓ := by
  have hmul := shift_nonneg (qn := qn) hℓ
  have hsplit := add_shift (qn := qn) (h := h) (ℓ := ℓ)
  ext y
  simp only [Finset.mem_image, Finset.mem_Icc, resW, J1resG, J2resG, Finset.mem_union, resK]
  constructor
  · rintro ⟨k, ⟨hk1, hk2⟩, rfl⟩
    by_cases hk : k < (h : ℤ)
    · left
      rw [resSite_of_lt hk]
      omega
    · right
      rw [resSite_of_le (by omega : (h : ℤ) ≤ k)]
      omega
  · rintro (⟨hy1, hy2⟩ | ⟨hy1, hy2⟩)
    · refine ⟨y, ⟨by omega, by omega⟩, ?_⟩
      rw [resSite_of_lt (by omega : y < (h : ℤ))]
    · refine ⟨y - ((ℓ : ℤ) - 1) * (qn : ℤ), ⟨by omega, by omega⟩, ?_⟩
      rw [resSite_of_le (by omega : (h : ℤ) ≤ y - ((ℓ : ℤ) - 1) * (qn : ℤ))]
      ring

/-- `resSite` is injective on `resK`. -/
private lemma injOn_resSite {qn h ℓ : ℕ} (hℓ : 1 ≤ ℓ) :
    Set.InjOn (resSite qn h ℓ) ((resK qn h : Finset ℤ) : Set ℤ) := by
  have hmul := shift_nonneg (qn := qn) hℓ
  intro k1 _ k2 _ hkk
  by_cases h1 : k1 < (h : ℤ)
  · rw [resSite_of_lt h1] at hkk
    by_cases h2 : k2 < (h : ℤ)
    · rw [resSite_of_lt h2] at hkk
      exact hkk
    · rw [resSite_of_le (by omega : (h : ℤ) ≤ k2)] at hkk
      omega
  · rw [resSite_of_le (by omega : (h : ℤ) ≤ k1)] at hkk
    by_cases h2 : k2 < (h : ℤ)
    · rw [resSite_of_lt h2] at hkk
      omega
    · rw [resSite_of_le (by omega : (h : ℤ) ≤ k2)] at hkk
      omega

/-- `resSite k` belongs to the resonant windows for every `k ∈ resK`. -/
private lemma resSite_mem_resW {qn h ℓ : ℕ} (hℓ : 1 ≤ ℓ) (_hqn : (h : ℤ) ≤ (qn : ℤ)) :
    ∀ k ∈ resK qn h, resSite qn h ℓ k ∈ resW qn h ℓ := by
  have hmul := shift_nonneg (qn := qn) hℓ
  have hsplit := add_shift (qn := qn) (h := h) (ℓ := ℓ)
  intro k hk
  have hk' : -(h : ℤ) ≤ k ∧ k ≤ 2 * (qn : ℤ) - (h : ℤ) - 1 := by
    simpa only [resK, Finset.mem_Icc] using hk
  rw [resW, Finset.mem_union]
  by_cases hklt : k < (h : ℤ)
  · left
    rw [resSite_of_lt hklt]
    simp only [J1resG, Finset.mem_Icc]
    omega
  · right
    rw [resSite_of_le (by omega : (h : ℤ) ≤ k)]
    simp only [J2resG, Finset.mem_Icc]
    omega

/-- `resSite` maps `resK` into the range `[-(h:ℤ), (ℓ+1) q n - (h:ℤ) - 1]`. -/
private lemma resSite_bounds {qn h ℓ : ℕ} (hℓ : 1 ≤ ℓ) (hqn : (h : ℤ) ≤ (qn : ℤ)) :
    ∀ k ∈ resK qn h, -(h : ℤ) ≤ resSite qn h ℓ k ∧
      resSite qn h ℓ k ≤ ((ℓ : ℤ) + 1) * (qn : ℤ) - (h : ℤ) - 1 := by
  have hmul := shift_nonneg (qn := qn) hℓ
  have hsplit := add_shift (qn := qn) (h := h) (ℓ := ℓ)
  have h2h := two_h_le hℓ hqn
  intro k hk
  have hk' : -(h : ℤ) ≤ k ∧ k ≤ 2 * (qn : ℤ) - (h : ℤ) - 1 := by
    simpa only [resK, Finset.mem_Icc] using hk
  by_cases hklt : k < (h : ℤ)
  · rw [resSite_of_lt hklt]
    omega
  · rw [resSite_of_le (by omega : (h : ℤ) ≤ k)]
    omega

theorem res_bij {qn h ℓ : ℕ} (hℓ : 1 ≤ ℓ) (hh : 3 * qn / 5 ≤ h) (hh' : h ≤ 5 * qn / 8) :
    Work.TMC16Core.Core.resW qn h ℓ =
        (Work.TMC16Core.Core.resK qn h).image (Work.TMC16Core.Core.resSite qn h ℓ) ∧
    Set.InjOn (Work.TMC16Core.Core.resSite qn h ℓ)
        ((Work.TMC16Core.Core.resK qn h : Finset ℤ) : Set ℤ) ∧
    (∀ k : ℤ, |Work.TMC16Core.Core.resLsh h ℓ k| ≤ (ℓ : ℤ) - 1) ∧
    (∀ k ∈ Work.TMC16Core.Core.resK qn h,
        Work.TMC16Core.Core.resSite qn h ℓ k ∈ Work.TMC16Core.Core.resW qn h ℓ) ∧
    (∀ k ∈ Work.TMC16Core.Core.resK qn h, -(h : ℤ) ≤ Work.TMC16Core.Core.resSite qn h ℓ k ∧
      Work.TMC16Core.Core.resSite qn h ℓ k ≤ ((ℓ : ℤ) + 1) * (qn : ℤ) - (h : ℤ) - 1) := by
  have hqn : (h : ℤ) ≤ (qn : ℤ) := h_le_qn hh'
  have _ : 3 * qn / 5 ≤ h := hh
  have hnmul : (0 : ℤ) ≤ ((ℓ : ℤ) - 1) * (qn : ℤ) := shift_nonneg (qn := qn) hℓ
  have hnn : (0 : ℤ) ≤ (ℓ : ℤ) - 1 := by omega
  have hbase : (0 : ℤ) ≤ (qn : ℤ) := by omega
  have hres : ∀ k : ℤ, |resLsh h ℓ k| ≤ (ℓ : ℤ) - 1 := by
    intro k
    by_cases hk : k < (h : ℤ)
    · rw [resLsh_of_lt hk]
      simpa using hnn
    · rw [resLsh_of_le (by omega : (h : ℤ) ≤ k), abs_of_nonneg hnn]
  refine ⟨?_, ?_, hres, ?_, ?_⟩
  · rw [image_resSite hℓ hqn]
  · exact injOn_resSite hℓ
  · exact resSite_mem_resW hℓ hqn
  · exact resSite_bounds hℓ hqn

end

end Work.TMC16Core.Core
