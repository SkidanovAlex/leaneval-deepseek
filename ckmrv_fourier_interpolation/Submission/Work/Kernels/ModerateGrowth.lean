/-
# The class `𝒫` of holomorphic functions of moderate growth on `ℍ`

This file sets up the space `𝒫` of CKMRV (Cohn--Kumar--Miller--Radchenko--Viazovska,
*Universal optimality of the E8 and Leech lattices*, Ann. of Math. 196 (2022), Section 4.1):
the space of holomorphic functions `F : ℍ → ℂ` satisfying the moderate growth bound

  `|F τ| ≤ α * ((im τ) ^ (-β) + |τ| ^ γ)`   for some `α β γ ≥ 0`   (4.1)

for all `τ : ℍ`.  Because `im τ > 0` we may write `(im τ) ^ (-β) = ((im τ)⁻¹) ^ β`, and we
take the right-hand form as our definition (it is slightly more convenient in Lean); the
paper's form is recovered by `Work.Kernels.moderateGrowthOn_iff_paper`.

Following the paper we also use the equivalent *scale* form

  `|F τ| ≤ α * S τ ^ N`  where  `S τ = 1 + (im τ)⁻¹ + |τ|`,

which is the form in which the space is closed under products.

## Main definitions

* `Work.Kernels.ModerateGrowthOn S F` : moderate growth of `F` on the subset `S ⊆ ℍ`.
* `Work.Kernels.InP F` : `F ∈ 𝒫`, i.e. `F` is holomorphic on `ℍ` and has moderate growth
  on all of `ℍ`.

## Main results

* `Work.Kernels.moderateGrowthOn_iff_scale`, `Work.Kernels.moderateGrowthOn_iff_paper` :
  the three forms of the growth bound are equivalent.
* Closure of `ModerateGrowthOn`/`InP` under `0`, constants, `+`, `-`, `*`, scalar multiples,
  finite sums and products, powers, and `𝒫`-membership of every bounded function.
-/
import Mathlib

noncomputable section

open UpperHalfPlane ModularForm ModularGroup
open scoped MatrixGroups ModularForm Modular Manifold Bundle

namespace Work.Kernels

/-! ## The scale `1 + (im τ)⁻¹ + |τ|` -/

/-- The auxiliary scale `S τ = 1 + (im τ)⁻¹ + |τ|`.  On any subset `S ⊆ ℍ`, moderate growth
is equivalent to a bound `‖F τ‖ ≤ α * S τ ^ N` for some `0 ≤ α`, `0 ≤ N`. -/
def scale (τ : ℍ) : ℝ := 1 + (τ.im)⁻¹ + ‖(τ : ℂ)‖

lemma one_le_scale (τ : ℍ) : 1 ≤ scale τ := by
  have h1 : 0 ≤ (τ.im)⁻¹ := inv_nonneg.mpr τ.im_pos.le
  have h2 : 0 ≤ ‖(τ : ℂ)‖ := norm_nonneg _
  unfold scale; linarith

lemma scale_pos (τ : ℍ) : 0 < scale τ := lt_of_lt_of_le zero_lt_one (one_le_scale τ)

lemma inv_im_le_scale (τ : ℍ) : (τ.im)⁻¹ ≤ scale τ := by
  have h2 : 0 ≤ ‖(τ : ℂ)‖ := norm_nonneg _
  unfold scale; linarith

lemma coe_norm_le_scale (τ : ℍ) : ‖(τ : ℂ)‖ ≤ scale τ := by
  have h1 : 0 ≤ (τ.im)⁻¹ := inv_nonneg.mpr τ.im_pos.le
  unfold scale; linarith

lemma inv_im_nonneg (τ : ℍ) : 0 ≤ (τ.im)⁻¹ := inv_nonneg.mpr τ.im_pos.le

lemma im_le_coe_norm (τ : ℍ) : τ.im ≤ ‖(τ : ℂ)‖ := by
  have h := Complex.abs_im_le_norm (τ : ℂ)
  rw [coe_im τ, abs_of_pos τ.im_pos] at h
  exact h

private lemma rpow_max' {a b N : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hN : 0 ≤ N) :
    (max a b) ^ N = max (a ^ N) (b ^ N) := by
  rcases le_total a b with h | h
  · rw [max_eq_right h, max_eq_right (Real.rpow_le_rpow ha h hN)]
  · rw [max_eq_left h, max_eq_left (Real.rpow_le_rpow hb h hN)]

/-! ## The class `𝒫` -/

/-- `ModerateGrowthOn S F` : the function `F : ℍ → ℂ` satisfies the moderate growth bound
(4.1) of the paper on the subset `S ⊆ ℍ`. -/
def ModerateGrowthOn (S : Set ℍ) (F : ℍ → ℂ) : Prop :=
  ∃ α β γ : ℝ, 0 ≤ α ∧ 0 ≤ β ∧ 0 ≤ γ ∧
    ∀ τ ∈ S, ‖F τ‖ ≤ α * ((τ.im)⁻¹ ^ β + ‖(τ : ℂ)‖ ^ γ)

/-- `InP F` : `F` lies in the paper's class `𝒫`, i.e. `F` is holomorphic on `ℍ` and has
moderate growth there. -/
def InP (F : ℍ → ℂ) : Prop := MDiff F ∧ ModerateGrowthOn Set.univ F

/-- `ModerateGrowthOn` is exactly the paper's condition (4.1). -/
theorem moderateGrowthOn_iff_paper (S : Set ℍ) (F : ℍ → ℂ) :
    ModerateGrowthOn S F ↔ ∃ α β γ : ℝ, 0 ≤ α ∧ 0 ≤ β ∧ 0 ≤ γ ∧
      ∀ τ ∈ S, ‖F τ‖ ≤ α * ((τ.im) ^ (-β) + ‖(τ : ℂ)‖ ^ γ) := by
  constructor
  · rintro ⟨α, β, γ, hα, hβ, hγ, h⟩
    refine ⟨α, β, γ, hα, hβ, hγ, fun τ hτ => ?_⟩
    have heq : (τ.im)⁻¹ ^ β = (τ.im) ^ (-β) :=
      (Real.inv_rpow τ.im_pos.le β).trans (Real.rpow_neg τ.im_pos.le β).symm
    rw [← heq]
    exact h τ hτ
  · rintro ⟨α, β, γ, hα, hβ, hγ, h⟩
    refine ⟨α, β, γ, hα, hβ, hγ, fun τ hτ => ?_⟩
    have heq : (τ.im)⁻¹ ^ β = (τ.im) ^ (-β) :=
      (Real.inv_rpow τ.im_pos.le β).trans (Real.rpow_neg τ.im_pos.le β).symm
    rw [heq]
    exact h τ hτ

/-- Moderate growth in the paper's form is equivalent to the *scale* form
`‖F τ‖ ≤ α * S τ ^ N`. -/
theorem moderateGrowthOn_iff_scale (S : Set ℍ) (F : ℍ → ℂ) :
    ModerateGrowthOn S F ↔
      ∃ α N : ℝ, 0 ≤ α ∧ 0 ≤ N ∧ ∀ τ ∈ S, ‖F τ‖ ≤ α * (scale τ) ^ N := by
  constructor
  · rintro ⟨α, β, γ, hα, hβ, hγ, h⟩
    refine ⟨2 * α, max β γ, by positivity, le_max_of_le_left hβ, fun τ hτ => ?_⟩
    have h1 : (τ.im)⁻¹ ^ β ≤ (scale τ) ^ β :=
      Real.rpow_le_rpow (inv_nonneg.mpr τ.im_pos.le) (inv_im_le_scale τ) hβ
    have h2 : ‖(τ : ℂ)‖ ^ γ ≤ (scale τ) ^ γ :=
      Real.rpow_le_rpow (norm_nonneg _) (coe_norm_le_scale τ) hγ
    have h3 : (scale τ) ^ β ≤ (scale τ) ^ (max β γ) :=
      Real.rpow_le_rpow_of_exponent_le (one_le_scale τ) (le_max_left β γ)
    have h4 : (scale τ) ^ γ ≤ (scale τ) ^ (max β γ) :=
      Real.rpow_le_rpow_of_exponent_le (one_le_scale τ) (le_max_right β γ)
    have h5 : (τ.im)⁻¹ ^ β + ‖(τ : ℂ)‖ ^ γ ≤ 2 * (scale τ) ^ (max β γ) := by linarith
    calc ‖F τ‖ ≤ α * ((τ.im)⁻¹ ^ β + ‖(τ : ℂ)‖ ^ γ) := h τ hτ
      _ ≤ α * (2 * (scale τ) ^ (max β γ)) := mul_le_mul_of_nonneg_left h5 hα
      _ = 2 * α * (scale τ) ^ (max β γ) := by ring
  · rintro ⟨α, N, hα, hN, h⟩
    refine ⟨α * 3 ^ N, N, N, by positivity, hN, hN, fun τ hτ => ?_⟩
    have hlim : (0:ℝ) ≤ max ((τ.im)⁻¹) ‖(τ : ℂ)‖ :=
      le_trans (inv_nonneg.mpr τ.im_pos.le) (le_max_left _ _)
    have h3 : 1 ≤ max ((τ.im)⁻¹) ‖(τ : ℂ)‖ := by
      by_contra hlt
      rw [not_le, max_lt_iff] at hlt
      obtain ⟨ha, hb⟩ := hlt
      have hy : 1 < τ.im := by
        rcases (inv_lt_one_iff₀.mp ha) with h | h
        · exact absurd h (not_le.mpr τ.im_pos)
        · exact h
      have hle : τ.im ≤ ‖(τ : ℂ)‖ := im_le_coe_norm τ
      linarith
    have h4 : (τ.im)⁻¹ ≤ max ((τ.im)⁻¹) ‖(τ : ℂ)‖ := le_max_left _ _
    have h5 : ‖(τ : ℂ)‖ ≤ max ((τ.im)⁻¹) ‖(τ : ℂ)‖ := le_max_right _ _
    have hs : scale τ ≤ 3 * max ((τ.im)⁻¹) ‖(τ : ℂ)‖ := by unfold scale; linarith
    have hrw : (max ((τ.im)⁻¹) ‖(τ : ℂ)‖) ^ N
        = max (((τ.im)⁻¹) ^ N) (‖(τ : ℂ)‖ ^ N) :=
      rpow_max' (inv_nonneg.mpr τ.im_pos.le) (norm_nonneg _) hN
    have hmax : (max (((τ.im)⁻¹) ^ N) (‖(τ : ℂ)‖ ^ N))
        ≤ (τ.im)⁻¹ ^ N + ‖(τ : ℂ)‖ ^ N :=
      max_le (le_add_of_nonneg_right (Real.rpow_nonneg (norm_nonneg _) N))
        (le_add_of_nonneg_left (Real.rpow_nonneg (inv_nonneg.mpr τ.im_pos.le) N))
    have h3N : (0:ℝ) < 3 ^ N := Real.rpow_pos_of_pos (by norm_num) N
    have hstep : (scale τ) ^ N ≤ 3 ^ N * ((τ.im)⁻¹ ^ N + ‖(τ : ℂ)‖ ^ N) := by
      calc (scale τ) ^ N ≤ (3 * max ((τ.im)⁻¹) ‖(τ : ℂ)‖) ^ N :=
            Real.rpow_le_rpow (scale_pos τ).le hs hN
        _ = 3 ^ N * (max ((τ.im)⁻¹) ‖(τ : ℂ)‖) ^ N := Real.mul_rpow (by norm_num) hlim
        _ = 3 ^ N * max (((τ.im)⁻¹) ^ N) (‖(τ : ℂ)‖ ^ N) := by rw [hrw]
        _ ≤ 3 ^ N * ((τ.im)⁻¹ ^ N + ‖(τ : ℂ)‖ ^ N) :=
            mul_le_mul_of_nonneg_left hmax h3N.le
    calc ‖F τ‖ ≤ α * (scale τ) ^ N := h τ hτ
      _ ≤ α * (3 ^ N * ((τ.im)⁻¹ ^ N + ‖(τ : ℂ)‖ ^ N)) :=
            mul_le_mul_of_nonneg_left hstep hα
      _ = α * 3 ^ N * ((τ.im)⁻¹ ^ N + ‖(τ : ℂ)‖ ^ N) := by ring

namespace ModerateGrowthOn

lemma mono {S S' : Set ℍ} {F : ℍ → ℂ} (h : ModerateGrowthOn S F)
    (hSS : S' ⊆ S) : ModerateGrowthOn S' F := by
  obtain ⟨α, β, γ, hα, hβ, hγ, h⟩ := h
  exact ⟨α, β, γ, hα, hβ, hγ, fun τ hτ => h τ (hSS hτ)⟩

lemma zero (S : Set ℍ) : ModerateGrowthOn S (fun _ : ℍ => (0 : ℂ)) :=
  ⟨(0:ℝ), (0:ℝ), (0:ℝ), le_rfl, le_rfl, le_rfl, fun τ _ => by simp⟩

lemma const (S : Set ℍ) (c : ℂ) : ModerateGrowthOn S (fun _ : ℍ => c) :=
  ⟨‖c‖, (0:ℝ), (0:ℝ), norm_nonneg c, le_rfl, le_rfl, fun τ _ => by
    simp only [Real.rpow_zero]
    nlinarith [norm_nonneg c]⟩

lemma const_mul {S : Set ℍ} {F : ℍ → ℂ} (c : ℂ)
    (h : ModerateGrowthOn S F) : ModerateGrowthOn S (fun τ => c * F τ) := by
  obtain ⟨α, β, γ, hα, hβ, hγ, h⟩ := h
  refine ⟨‖c‖ * α, β, γ, by positivity, hβ, hγ, fun τ hτ => ?_⟩
  rw [norm_mul]
  calc ‖c‖ * ‖F τ‖ ≤ ‖c‖ * (α * ((τ.im)⁻¹ ^ β + ‖(τ : ℂ)‖ ^ γ)) :=
        mul_le_mul_of_nonneg_left (h τ hτ) (norm_nonneg c)
    _ = ‖c‖ * α * ((τ.im)⁻¹ ^ β + ‖(τ : ℂ)‖ ^ γ) := by ring

lemma neg {S : Set ℍ} {F : ℍ → ℂ} (h : ModerateGrowthOn S F) :
    ModerateGrowthOn S (fun τ => -F τ) := by
  obtain ⟨α, β, γ, hα, hβ, hγ, h⟩ := h
  exact ⟨α, β, γ, hα, hβ, hγ, fun τ hτ => by simpa using h τ hτ⟩

lemma add {S : Set ℍ} {F G : ℍ → ℂ} (hF : ModerateGrowthOn S F)
    (hG : ModerateGrowthOn S G) : ModerateGrowthOn S (fun τ => F τ + G τ) := by
  rw [moderateGrowthOn_iff_scale] at hF hG ⊢
  obtain ⟨α, N, hα, hN, hF⟩ := hF
  obtain ⟨α', N', hα', hN', hG⟩ := hG
  refine ⟨α + α', max N N', by positivity, le_max_of_le_left hN, fun τ hτ => ?_⟩
  have h1 : (scale τ) ^ N ≤ (scale τ) ^ (max N N') :=
    Real.rpow_le_rpow_of_exponent_le (one_le_scale τ) (le_max_left N N')
  have h2 : (scale τ) ^ N' ≤ (scale τ) ^ (max N N') :=
    Real.rpow_le_rpow_of_exponent_le (one_le_scale τ) (le_max_right N N')
  have hs : (0:ℝ) ≤ (scale τ) ^ (max N N') := Real.rpow_nonneg (scale_pos τ).le _
  calc ‖F τ + G τ‖ ≤ ‖F τ‖ + ‖G τ‖ := norm_add_le _ _
    _ ≤ α * (scale τ) ^ N + α' * (scale τ) ^ N' := add_le_add (hF τ hτ) (hG τ hτ)
    _ ≤ α * (scale τ) ^ (max N N') + α' * (scale τ) ^ (max N N') :=
          add_le_add (mul_le_mul_of_nonneg_left h1 hα) (mul_le_mul_of_nonneg_left h2 hα')
    _ = (α + α') * (scale τ) ^ (max N N') := by ring

lemma sub {S : Set ℍ} {F G : ℍ → ℂ} (hF : ModerateGrowthOn S F)
    (hG : ModerateGrowthOn S G) : ModerateGrowthOn S (fun τ => F τ - G τ) := by
  simpa [sub_eq_add_neg] using hF.add hG.neg

lemma mul {S : Set ℍ} {F G : ℍ → ℂ} (hF : ModerateGrowthOn S F)
    (hG : ModerateGrowthOn S G) : ModerateGrowthOn S (fun τ => F τ * G τ) := by
  rw [moderateGrowthOn_iff_scale] at hF hG ⊢
  obtain ⟨α, N, hα, hN, hF⟩ := hF
  obtain ⟨α', N', hα', hN', hG⟩ := hG
  refine ⟨α * α', N + N', by positivity, by positivity, fun τ hτ => ?_⟩
  have hsp : (0:ℝ) < scale τ := scale_pos τ
  calc ‖F τ * G τ‖ = ‖F τ‖ * ‖G τ‖ := norm_mul _ _
    _ ≤ (α * (scale τ) ^ N) * (α' * (scale τ) ^ N') :=
          mul_le_mul (hF τ hτ) (hG τ hτ) (by positivity) (by positivity)
    _ = α * α' * (scale τ) ^ (N + N') := by
          rw [Real.rpow_add hsp]; ring

lemma sum {S : Set ℍ} {ι : Type*} {F : ι → ℍ → ℂ} (s : Finset ι)
    (h : ∀ i ∈ s, ModerateGrowthOn S (F i)) :
    ModerateGrowthOn S (∑ i ∈ s, F i) := by
  classical
  induction s using Finset.induction with
  | empty => rw [Finset.sum_empty]; exact zero S
  | insert i s hi ih =>
      rw [Finset.sum_insert hi]
      exact (h i (Finset.mem_insert_self i s)).add
        (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

lemma prod {S : Set ℍ} {ι : Type*} {F : ι → ℍ → ℂ} (s : Finset ι)
    (h : ∀ i ∈ s, ModerateGrowthOn S (F i)) :
    ModerateGrowthOn S (∏ i ∈ s, F i) := by
  classical
  induction s using Finset.induction with
  | empty => rw [Finset.prod_empty]; exact const S 1
  | insert i s hi ih =>
      rw [Finset.prod_insert hi]
      exact (h i (Finset.mem_insert_self i s)).mul
        (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

lemma pow {S : Set ℍ} {F : ℍ → ℂ} (h : ModerateGrowthOn S F) (n : ℕ) :
    ModerateGrowthOn S (fun τ => F τ ^ n) := by
  induction n with
  | zero => simpa using const S 1
  | succ n ih => simpa [pow_succ] using ih.mul h

/-- Any function bounded on `S` has moderate growth on `S`. -/
lemma of_bound {S : Set ℍ} {F : ℍ → ℂ} {C : ℝ} (h : ∀ τ ∈ S, ‖F τ‖ ≤ C) :
    ModerateGrowthOn S F := by
  refine ⟨2 * (max C 0) + 1, (0:ℝ), (0:ℝ), by positivity, le_rfl, le_rfl, fun τ hτ => ?_⟩
  have h1 : ‖F τ‖ ≤ max C 0 := le_trans (h τ hτ) (le_max_left _ _)
  have h2 : (0:ℝ) ≤ max C 0 := le_max_right _ _
  simp only [Real.rpow_zero]
  nlinarith [h1, h2]

end ModerateGrowthOn

/-! ## Closure of `𝒫` -/

namespace InP

lemma const (c : ℂ) : InP (fun _ : ℍ => c) :=
  ⟨mdifferentiable_const, ModerateGrowthOn.const _ c⟩

lemma one : InP (fun _ : ℍ => 1) := InP.const 1

lemma zero : InP (fun _ : ℍ => 0) := InP.const 0

lemma add {F G : ℍ → ℂ} (hF : InP F) (hG : InP G) : InP (fun τ => F τ + G τ) :=
  ⟨hF.1.add hG.1, hF.2.add hG.2⟩

lemma neg {F : ℍ → ℂ} (hF : InP F) : InP (fun τ => -F τ) :=
  ⟨hF.1.neg, hF.2.neg⟩

lemma sub {F G : ℍ → ℂ} (hF : InP F) (hG : InP G) : InP (fun τ => F τ - G τ) :=
  ⟨hF.1.sub hG.1, hF.2.sub hG.2⟩

lemma mul {F G : ℍ → ℂ} (hF : InP F) (hG : InP G) : InP (fun τ => F τ * G τ) :=
  ⟨hF.1.mul hG.1, hF.2.mul hG.2⟩

lemma const_mul (c : ℂ) {F : ℍ → ℂ} (hF : InP F) : InP (fun τ => c * F τ) :=
  ⟨mdifferentiable_const.mul hF.1, hF.2.const_mul c⟩

lemma pow {F : ℍ → ℂ} (hF : InP F) (n : ℕ) : InP (fun τ => F τ ^ n) :=
  ⟨hF.1.pow n, hF.2.pow n⟩

lemma sum {ι : Type*} {F : ι → ℍ → ℂ} (s : Finset ι) (h : ∀ i ∈ s, InP (F i)) :
    InP (∑ i ∈ s, F i) := by
  classical
  induction s using Finset.induction with
  | empty => rw [Finset.sum_empty]; exact zero
  | insert i s hi ih =>
      rw [Finset.sum_insert hi]
      exact (h i (Finset.mem_insert_self i s)).add
        (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

lemma prod {ι : Type*} {F : ι → ℍ → ℂ} (s : Finset ι) (h : ∀ i ∈ s, InP (F i)) :
    InP (∏ i ∈ s, F i) := by
  classical
  induction s using Finset.induction with
  | empty => rw [Finset.prod_empty]; exact one
  | insert i s hi ih =>
      rw [Finset.prod_insert hi]
      exact (h i (Finset.mem_insert_self i s)).mul
        (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

end InP

end Work.Kernels
