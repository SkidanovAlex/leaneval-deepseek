import Mathlib
import Submission.Work.HP.Defs
import Submission.Work.HP.Vero
import Submission.Work.HP.Transf.Basic

/-!
# The "primitive pairing" step of the transference induction

If `v ∈ dualLat L` is a shortest dual vector up to a factor `3/2`, then the pairing
`⟨v, ·⟩ : L → ℤ` is onto: there is `w ∈ L` with `⟪v, w⟫ = 1`.
-/

set_option autoImplicit false

noncomputable section

open Finset

namespace Work.HP.Transf

variable {ι : Type*} [Fintype ι]

theorem exists_pairing_one (L : Submodule ℤ (ι → ℝ)) (v : ι → ℝ)
    (hv : v ∈ dualLat L) (hv0 : v ≠ 0) (μ : ℝ) (hμ : lamR (dualLat L) 1 = μ) (hμpos : 0 < μ)
    (hb : rNorm v ≤ 3 / 2 * μ) : ∃ w ∈ L, dotR v w = 1 := by
  classical
  -- the pairing with `v` takes integral values on `L`
  have hval : ∀ y : L, ∃ k : ℤ, dotR v (y : ι → ℝ) = k := fun y => hv.2 y y.2
  let φ : L → ℤ := fun y => Classical.choose (hval y)
  have hφ : ∀ y : L, dotR v (y : ι → ℝ) = (φ y : ℝ) := fun y => Classical.choose_spec (hval y)
  -- `v ∈ span ℝ L`
  have hvspan : v ∈ Submodule.span ℝ (L : Set (ι → ℝ)) := hv.1
  -- some value is nonzero
  have hex : ∃ y : L, φ y ≠ 0 := by
    by_contra hc
    push Not at hc
    have hzero : ∀ x ∈ Submodule.span ℝ (L : Set (ι → ℝ)), dotR v x = 0 := by
      intro x hx
      refine Submodule.span_induction (p := fun x _ => dotR v x = 0) ?_ ?_ ?_ ?_ hx
      · intro y hy
        have h1 := hφ ⟨y, hy⟩
        rw [h1, hc ⟨y, hy⟩]
        norm_num
      · simp
      · intro a b _ _ ha hb
        rw [dotR_add_right, ha, hb, add_zero]
      · intro c a _ ha
        rw [dotR_smul_right, ha, mul_zero]
    exact hv0 (dotR_self_eq_zero.mp (hzero v hvspan))
  -- least positive value of `|φ ·|`
  have hp : ∃ m : ℕ, m ≠ 0 ∧ ∃ y : L, (m : ℤ) = |φ y| := by
    obtain ⟨y, hy⟩ := hex
    exact ⟨(φ y).natAbs, by simpa [Int.natAbs_eq_zero] using hy, y, Int.natCast_natAbs (φ y)⟩
  obtain ⟨hn0, y₁, hy₁⟩ := Nat.find_spec hp
  -- the positive value is attained
  have hpos : (0 : ℤ) < (Nat.find hp : ℤ) := by
    have : 0 < Nat.find hp := Nat.pos_of_ne_zero hn0
    exact_mod_cast this
  have hcase : φ y₁ = (Nat.find hp : ℤ) ∨ φ y₁ = -(Nat.find hp : ℤ) := by
    rcases lt_trichotomy (φ y₁) 0 with h | h | h
    · right
      rw [abs_of_neg h] at hy₁
      linarith [hy₁]
    · left; rw [h] at hy₁ ⊢; simpa using hy₁.symm
    · left
      rw [abs_of_nonneg (le_of_lt h)] at hy₁
      linarith [hy₁]
  obtain ⟨y₂, hy₂⟩ : ∃ y₂ : L, φ y₂ = (Nat.find hp : ℤ) := by
    rcases hcase with h | h
    · exact ⟨y₁, h⟩
    · refine ⟨-y₁, ?_⟩
      have hneg : φ (-y₁) = -φ y₁ := by
        have hreal : (((φ (-y₁)) : ℤ) : ℝ) = ((-φ y₁ : ℤ) : ℝ) := by
          rw [Int.cast_neg, ← hφ (-y₁), ← hφ y₁, Submodule.coe_neg, dotR_neg_right]
        exact_mod_cast hreal
      rw [hneg, h]
      ring
  -- `n` divides every value
  have hdvd : ∀ y : L, (Nat.find hp : ℤ) ∣ φ y := by
    intro y
    set n : ℤ := (Nat.find hp : ℤ) with hn
    have hnpos : 0 < n := by rw [hn]; exact hpos
    set q : ℤ := φ y / n with hq
    set r : ℤ := φ y % n with hr
    have hqr : r + q * n = φ y := by
      rw [hr, hq]
      simpa [mul_comm] using Int.emod_add_mul_ediv (φ y) n
    have hr0 : 0 ≤ r := by rw [hr]; exact Int.emod_nonneg _ (ne_of_gt hnpos)
    have hrn : r < n := by
      rw [hr]; exact Int.emod_lt_of_pos _ hnpos
    have hry : ∃ y' : L, φ y' = r := by
      refine ⟨y - q • y₂, ?_⟩
      have hcomp : (φ (y - q • y₂) : ℤ) = φ y - q * φ y₂ := by
        have hreal : (((φ (y - q • y₂)) : ℤ) : ℝ) = ((φ y - q * φ y₂ : ℤ) : ℝ) := by
          rw [Int.cast_sub, Int.cast_mul, ← hφ (y - q • y₂), ← hφ y, ← hφ y₂]
          rw [Submodule.coe_sub, Submodule.coe_smul, dotR_sub_right, dotR_zsmul_right]
        exact_mod_cast hreal
      rw [hcomp, hy₂]
      linarith [hqr]
    by_contra hndvd
    have hrne : r ≠ 0 := by
      intro h0
      exact hndvd (by rw [hn]; exact Int.dvd_of_emod_eq_zero (by rw [hr] at h0; exact h0))
    have hrpos : 0 < r := lt_of_le_of_ne hr0 (Ne.symm hrne)
    obtain ⟨y', hy'⟩ := hry
    have hmem : (r.toNat ≠ 0 ∧ ∃ y : L, (r.toNat : ℤ) = |φ y|) := by
      refine ⟨by omega, y', ?_⟩
      rw [Int.toNat_of_nonneg hr0, hy', abs_of_pos hrpos]
    have := Nat.find_min' hp hmem
    have hlt : (r.toNat : ℤ) < (Nat.find hp : ℤ) := by
      rw [Int.toNat_of_nonneg hr0]
      exact hrn
    have : (Nat.find hp : ℤ) ≤ (r.toNat : ℤ) := by exact_mod_cast this
    linarith
  -- `v / n ∈ dualLat L`
  have hnne : ((Nat.find hp : ℕ) : ℝ) ≠ 0 := by
    have : Nat.find hp ≠ 0 := hn0
    exact_mod_cast this
  set n0 : ℝ := ((Nat.find hp : ℕ) : ℝ) with hn0def
  have hn0pos : 0 < n0 := by rw [hn0def]; exact_mod_cast Nat.pos_of_ne_zero hn0
  have hmemdual : (n0⁻¹) • v ∈ dualLat L := by
    refine ⟨?_, ?_⟩
    · exact Submodule.smul_mem _ _ hvspan
    · intro z hz
      obtain ⟨k, hk⟩ := hdvd ⟨z, hz⟩
      refine ⟨k, ?_⟩
      have h1 : (∑ x, ((n0⁻¹) • v) x * z x)
          = n0⁻¹ * (((Nat.find hp : ℤ) : ℝ) * (k : ℝ)) := by
        rw [← dotR, dotR_smul_left, hφ ⟨z, hz⟩, hk, Int.cast_mul]
      rw [h1]
      have hcast : (((Nat.find hp : ℤ) : ℝ)) = n0 := by
        rw [hn0def]; push_cast; ring
      rw [hcast]
      field_simp
  have hne : (n0⁻¹) • v ≠ 0 := by
    intro h
    exact hv0 (smul_eq_zero.mp h |>.resolve_left (inv_ne_zero (ne_of_gt hn0pos)))
  have hle : lamR (dualLat L) 1 ≤ rNorm ((n0⁻¹) • v) := lamR_le_rNorm _ hmemdual hne
  rw [hμ] at hle
  have hrnorm : rNorm ((n0⁻¹) • v) = rNorm v / n0 := by
    rw [rNorm_smul, abs_of_pos (inv_pos.mpr hn0pos)]
    field_simp
  rw [hrnorm] at hle
  have hbound : μ ≤ rNorm v / n0 := hle
  have hle2 : n0 * μ ≤ 3 / 2 * μ := by
    have hposn : 0 < n0 := hn0pos
    have := mul_le_mul_of_nonneg_left hb (le_of_lt hposn)
    have h2 : n0 * (rNorm v / n0) = rNorm v := by field_simp
    calc n0 * μ ≤ n0 * (rNorm v / n0) := mul_le_mul_of_nonneg_left hbound (le_of_lt hposn)
      _ = rNorm v := h2
      _ ≤ 3 / 2 * μ := hb
  have hn1 : Nat.find hp = 1 := by
    have hμn : (0 : ℝ) < μ := hμpos
    have : (Nat.find hp : ℝ) ≤ 3 / 2 := by
      rw [hn0def] at hle2
      nlinarith
    have hnat : (Nat.find hp : ℕ) ≤ 1 := by
      have hlt : Nat.find hp < 2 := by exact_mod_cast (by linarith : (Nat.find hp : ℝ) < 2)
      omega
    omega
  -- conclude
  rcases hcase with h | h
  · refine ⟨y₁, y₁.2, ?_⟩
    rw [hφ y₁, h, hn1]
    norm_num
  · refine ⟨-y₁, L.neg_mem y₁.2, ?_⟩
    rw [dotR_neg_right, hφ y₁, h, hn1]
    norm_num

end Work.HP.Transf
