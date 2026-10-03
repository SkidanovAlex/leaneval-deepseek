/-
Copyright (c) 2026 The AnnalsChallenge team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AnnalsChallenge team
-/
import Mathlib
import Submission.Work.Peluse.PET.pet_reindex
import Submission.Work.Peluse.PET.vdc_muL

/-!
# The single PET (Cauchy–Schwarz + van der Corput) step of Peluse's inverse theorem

This module proves `Work.Peluse.PET.pet_step` — Peluse, *Bounds for sets with no polynomial
progressions*, Forum Math. Pi **8** (2020), Lemma 4.2 (the abstract PET step), in the
specialised form needed by Krause–Mirek–Tao's §5.

Setting: `f` and the family `F i` (`i : ι`) are `1`-bounded and supported in `[-N,N]`,
`Q i : ℤ → ℤ` satisfies `|Q i y| ≤ Cne · N` for `y ∈ [1,M]`, and `γ ≤ ‖Λ‖²` where

`Λ = (NM)⁻¹ ∑_x f x ∑_{y ∈ [M]} ∏_{i} F i (x + Q i y)`.

The conclusion is that the van der Corput smoothing of the same average, in which the `i₀`-th
factor has been moved out by the change of variables `x ↦ x + Q i₀ y` and the `y`-shift `a` is
averaged against Peluse's weight `μ_H` (`H = ⌊γ' M⌋`), is at least `γ/1000`:

`γ/1000 ≤ ∑_{a ∈ [-H,H]} μ_H(a) · ‖(NM)⁻¹ ∑_x F i₀ x ∑_{y ∈ [M]} ∏_{i} ∏_{ε : Bool} (…)‖`.

The proof is the standard chain: Cauchy–Schwarz in `x`, van der Corput in `y` (the lemma
`vdc_muL`), and the change of variables `x ↦ x + Q i₀ y` (`pet_reindex`).
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

open scoped BigOperators

namespace Work.Peluse.PET

noncomputable section

/-! ## Two elementary helpers -/

/-- Cauchy–Schwarz for a complex-valued finite sum. -/
lemma pet_norm_sum_mul_sq_le (s : Finset ℤ) (u v : ℤ → ℂ) :
    ‖∑ x ∈ s, u x * v x‖ ^ 2 ≤ (∑ x ∈ s, ‖u x‖ ^ 2) * (∑ x ∈ s, ‖v x‖ ^ 2) := by
  have h1 : ‖∑ x ∈ s, u x * v x‖ ≤ ∑ x ∈ s, ‖u x‖ * ‖v x‖ := by
    refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum fun x _ => ?_)
    rw [norm_mul]
  calc ‖∑ x ∈ s, u x * v x‖ ^ 2
      ≤ (∑ x ∈ s, ‖u x‖ * ‖v x‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
    _ ≤ (∑ x ∈ s, ‖u x‖ ^ 2) * (∑ x ∈ s, ‖v x‖ ^ 2) :=
        Finset.sum_mul_sq_le_sq_mul_sq s (fun x => ‖u x‖) (fun x => ‖v x‖)

/-- If `x ∉ [-N,N]` then `N < |x|` (in the `natAbs` form used by `SupportIn`). -/
lemma pet_natAbs_lt_of_notMem_Icc {N : ℕ} {x : ℤ} (hx : x ∉ Finset.Icc (-(N : ℤ)) (N : ℤ)) :
    N < x.natAbs := by
  have hxabs : (N : ℤ) < |x| := by
    simp only [Finset.mem_Icc, not_and_or, not_le] at hx
    rcases hx with h1 | h1
    · rw [abs_of_neg (by omega)]; omega
    · rw [abs_of_pos (by omega)]; omega
  rw [← Int.natCast_natAbs] at hxabs
  exact_mod_cast hxabs

/-- A sum over an interval containing `[-N',N']` equals the sum over `[-N',N']`, for a function
vanishing off `[-N',N']`. -/
lemma pet_sum_Icc_eq_sum_Icc_of_support {N' : ℕ} {φ : ℤ → ℂ}
    (hφ : ∀ x : ℤ, (N' : ℤ) < |x| → φ x = 0) {l r : ℤ}
    (hl : l ≤ -(N' : ℤ)) (hr : (N' : ℤ) ≤ r) :
    ∑ x ∈ Finset.Icc l r, φ x = ∑ x ∈ Finset.Icc (-(N' : ℤ)) (N' : ℤ), φ x := by
  refine (Finset.sum_subset ?_ ?_).symm
  · intro x hx
    obtain ⟨h1, h2⟩ := Finset.mem_Icc.mp hx
    exact Finset.mem_Icc.mpr ⟨le_trans hl h1, le_trans h2 hr⟩
  · intro x hx hxn
    apply hφ x
    have hx' : x < -(N' : ℤ) ∨ (N' : ℤ) < x := by
      by_contra hcon
      push_neg at hcon
      exact hxn (Finset.mem_Icc.mpr hcon)
    rcases hx' with h | h
    · rw [abs_of_neg (by omega)]; omega
    · rw [abs_of_pos (by omega)]; omega


/-- `μ_H ≥ 0`. -/
lemma pet_muL_nonneg (H : ℕ) (a : ℤ) : 0 ≤ Work.Peluse.muL H a := by
  rw [Work.Peluse.muL]
  positivity

/-! ## The PET step -/

theorem pet_step {ι : Type} [Fintype ι] [DecidableEq ι] (i₀ : ι) {N M : ℕ} (Cne : ℕ) {γ γ' : ℝ}
    (Q : ι → ℤ → ℤ) (f : ℤ → ℂ) (F : ι → ℤ → ℂ)
    (hN : 0 < N) (hM : 0 < M) (hγ : 0 < γ) (hγ' : 0 < γ')
    (hγ'γ : γ' ≤ γ / (1000 * (Cne + 1)))
    (hH : 1 ≤ ⌊γ' * (M : ℝ)⌋.toNat)
    (hf : ∀ x : ℤ, ‖f x‖ ≤ 1) (hfs : Work.Peluse.SupportIn f N)
    (hF : ∀ i x, ‖F i x‖ ≤ 1) (hFs : ∀ i, Work.Peluse.SupportIn (F i) N)
    (hQ : ∀ i, ∀ y ∈ Finset.Icc 1 M, |Q i (y : ℤ)| ≤ (Cne : ℤ) * (N : ℤ))
    (hLam : γ ≤ ‖((N : ℂ) * (M : ℂ))⁻¹ * ∑' x : ℤ, f x *
        ∑ y ∈ Finset.Icc 1 M, ∏ i : ι, F i (x + Q i (y : ℤ))‖ ^ 2) :
    γ / 1000 ≤ ∑ a ∈ Finset.Icc (-(⌊γ' * (M : ℝ)⌋.toNat : ℤ)) (⌊γ' * (M : ℝ)⌋.toNat : ℤ),
        Work.Peluse.muL ⌊γ' * (M : ℝ)⌋.toNat a *
          ‖((N : ℂ) * (M : ℂ))⁻¹ * ∑' x : ℤ, F i₀ x *
            ∑ y ∈ Finset.Icc 1 M, ∏ i : ι, ∏ ε : Bool,
              (if ((i, ε) = (i₀, false)) then 1 else
                (if ε then star (F i (x + (Q i ((y : ℤ) + a) - Q i₀ (y : ℤ))))
                        else F i (x + (Q i (y : ℤ) - Q i₀ (y : ℤ)))))‖ := by
  set H : ℕ := ⌊γ' * (M : ℝ)⌋.toNat with hHdef
  let Z : Finset ℤ := Finset.Icc (-((N : ℤ) * (Cne + 1))) ((N : ℤ) * (Cne + 1))
  let Y : Finset ℕ := Finset.Icc 1 M
  let g : ℤ → ℤ → ℂ := fun x y => ∏ i : ι, F i (x + Q i y)
  let W : ℤ → ℂ := fun x => ∑ y ∈ Y, g x (y : ℤ)
  let A : Finset ℤ := Finset.Icc (-(H : ℤ)) (H : ℤ)
  let S : ℤ → ℝ := fun x => ∑ a ∈ A, Work.Peluse.muL H a *
      (∑ y ∈ Y, (star (g x ((y : ℤ) + a)) * g x (y : ℤ)).re)
  let Sf : ℤ → ℤ → ℂ := fun a x => ∑ y ∈ Y, ∏ i : ι, ∏ ε : Bool,
      (if ((i, ε) = (i₀, false)) then 1 else
        (if ε then star (F i (x + (Q i ((y : ℤ) + a) - Q i₀ (y : ℤ))))
                else F i (x + (Q i (y : ℤ) - Q i₀ (y : ℤ)))))
  let T : ℤ → ℂ := fun a => ((N : ℂ) * (M : ℂ))⁻¹ * ∑' x : ℤ, F i₀ x * Sf a x
  let R : ℝ := ∑ a ∈ A, Work.Peluse.muL H a * ‖T a‖
  change γ / 1000 ≤ R
  have hH1 : 1 ≤ H := hH
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hMpos : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM
  have hHcast : (H : ℤ) = ⌊γ' * (M : ℝ)⌋ := by
    rw [hHdef]; exact Int.toNat_of_nonneg (Int.floor_nonneg.mpr (by positivity))
  have hHle : (H : ℝ) ≤ γ' * (M : ℝ) := by
    have h2 : (⌊γ' * (M : ℝ)⌋ : ℝ) ≤ γ' * (M : ℝ) := Int.floor_le _
    calc (H : ℝ) = ((H : ℤ) : ℝ) := by simp
      _ = (⌊γ' * (M : ℝ)⌋ : ℝ) := by rw [hHcast]
      _ ≤ γ' * (M : ℝ) := h2
  have hHnn : (0 : ℝ) ≤ (H : ℝ) := by positivity
  have hg_le : ∀ x y : ℤ, ‖g x y‖ ≤ 1 := by
    intro x y
    have h1 : ‖g x y‖ = ∏ i : ι, ‖F i (x + Q i y)‖ := by
      rw [show g x y = ∏ i : ι, F i (x + Q i y) from rfl, norm_prod]
    rw [h1]
    exact Finset.prod_le_one₀ (fun i _ => norm_nonneg _) (fun i _ => hF i _)
  have hW_le : ∀ x : ℤ, ‖W x‖ ≤ (M : ℝ) := by
    intro x
    have h1 : ‖W x‖ ≤ ∑ y ∈ Y, ‖g x (y : ℤ)‖ := by
      rw [show W x = ∑ y ∈ Y, g x (y : ℤ) from rfl]
      exact norm_sum_le _ _
    have h2 : ∑ y ∈ Y, ‖g x (y : ℤ)‖ ≤ ∑ y ∈ Y, (1 : ℝ) :=
      Finset.sum_le_sum fun y _ => hg_le x (y : ℤ)
    have hY : Y = Finset.Icc 1 M := rfl
    have h3 : ∑ y ∈ Y, (1 : ℝ) = (M : ℝ) := by
      rw [Finset.sum_const, nsmul_eq_mul, mul_one, hY, Nat.card_Icc]
      norm_num
    linarith
  have htsumf : ∑' x : ℤ, f x * W x = ∑ x ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), f x * W x := by
    refine tsum_eq_sum ?_
    intro x hx
    rw [hfs x (pet_natAbs_lt_of_notMem_Icc hx), zero_mul]
  have hnormNM : ‖((N : ℂ) * (M : ℂ))⁻¹‖ = ((N : ℝ) * (M : ℝ))⁻¹ := by
    rw [norm_inv, norm_mul]; simp
  have hLamW : γ ≤ ‖((N : ℂ) * (M : ℂ))⁻¹ * ∑' x : ℤ, f x * W x‖ ^ 2 := hLam
  have hLam_bound : ‖((N : ℂ) * (M : ℂ))⁻¹ * ∑' x : ℤ, f x * W x‖ ≤ 3 := by
    rw [htsumf, norm_mul, hnormNM]
    have h1 : ‖∑ x ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), f x * W x‖
        ≤ (2 * (N : ℝ) + 1) * (M : ℝ) := by
      calc ‖∑ x ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), f x * W x‖
          ≤ ∑ x ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), ‖f x * W x‖ := norm_sum_le _ _
        _ ≤ ∑ x ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), (M : ℝ) :=
            Finset.sum_le_sum fun x _ => by
              rw [norm_mul]
              calc ‖f x‖ * ‖W x‖ ≤ 1 * (M : ℝ) :=
                    mul_le_mul (hf x) (hW_le x) (norm_nonneg _) zero_le_one
                _ = (M : ℝ) := by ring
        _ = ((Finset.Icc (-(N : ℤ)) (N : ℤ)).card : ℝ) * (M : ℝ) := by
            rw [Finset.sum_const, nsmul_eq_mul]
        _ = (2 * (N : ℝ) + 1) * (M : ℝ) := by
            rw [Int.card_Icc, show (N : ℤ) + 1 - (-(N : ℤ)) = 2 * (N : ℤ) + 1 by ring]
            have hcard : (↑(2 * (N : ℤ) + 1).toNat : ℤ) = 2 * (N : ℤ) + 1 :=
              Int.toNat_of_nonneg (by positivity)
            exact_mod_cast congrArg (fun z : ℤ => (z : ℝ) * (M : ℝ)) hcard
    calc ((N : ℝ) * (M : ℝ))⁻¹ * ‖∑ x ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), f x * W x‖
        ≤ ((N : ℝ) * (M : ℝ))⁻¹ * ((2 * (N : ℝ) + 1) * (M : ℝ)) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = (2 * (N : ℝ) + 1) / (N : ℝ) := by
          field_simp
      _ ≤ 3 := by
          rw [div_le_iff₀ hNpos]
          nlinarith [hNpos, hMpos, show (1 : ℝ) ≤ (N : ℝ) by exact_mod_cast hN]
  have hgamma9 : γ ≤ 9 := by
    have h2 : ‖((N : ℂ) * (M : ℂ))⁻¹ * ∑' x : ℤ, f x * W x‖ ^ 2 ≤ 9 := by
      calc ‖((N : ℂ) * (M : ℂ))⁻¹ * ∑' x : ℤ, f x * W x‖ ^ 2 ≤ (3 : ℝ) ^ 2 :=
            pow_le_pow_left₀ (norm_nonneg _) hLam_bound 2
        _ = 9 := by norm_num
    linarith
  have hγ'le : γ' ≤ 1 := by
    have h1 : γ' * (1000 * ((Cne : ℝ) + 1)) ≤ γ := by
      rw [le_div_iff₀ (by positivity)] at hγ'γ
      linarith [hγ'γ]
    have hcnonneg : (0 : ℝ) ≤ (Cne : ℝ) := by positivity
    have hγ'nn : (0 : ℝ) ≤ γ' := le_of_lt hγ'
    have h2 : γ' * 1000 ≤ γ := by nlinarith [h1, hcnonneg, hγ'nn]
    have h3 : γ' * 1000 ≤ 9 := by linarith
    nlinarith [h3, hγ'nn]
  have hR_nn : 0 ≤ R := by
    refine Finset.sum_nonneg fun a _ => ?_
    exact mul_nonneg (pet_muL_nonneg H a) (norm_nonneg _)
  -- ## Cauchy–Schwarz in the `x`-variable
  have hcard1 : ((Finset.Icc (-(N : ℤ)) (N : ℤ)).card : ℝ) = 2 * (N : ℝ) + 1 := by
    rw [Int.card_Icc, show (N : ℤ) + 1 - (-(N : ℤ)) = 2 * (N : ℤ) + 1 by ring]
    have hc : (↑(2 * (N : ℤ) + 1).toNat : ℤ) = 2 * (N : ℤ) + 1 :=
      Int.toNat_of_nonneg (by positivity)
    exact_mod_cast hc
  have hf2 : ∑ x ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), ‖f x‖ ^ 2 ≤ 2 * (N : ℝ) + 1 := by
    calc ∑ x ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), ‖f x‖ ^ 2
        ≤ ∑ x ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), (1 : ℝ) :=
          Finset.sum_le_sum fun x _ => by
            have h := hf x
            have h2 := norm_nonneg (f x)
            nlinarith
      _ = ((Finset.Icc (-(N : ℤ)) (N : ℤ)).card : ℝ) := by
          rw [Finset.sum_const, nsmul_eq_mul, mul_one]
      _ = 2 * (N : ℝ) + 1 := hcard1
  have hnorm2 : ‖∑ x ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), f x * W x‖ ^ 2
      ≤ (2 * (N : ℝ) + 1) * (∑ x ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), ‖W x‖ ^ 2) :=
    le_trans (pet_norm_sum_mul_sq_le _ f W)
      (mul_le_mul_of_nonneg_right hf2 (by positivity))
  have hsub : Finset.Icc (-(N : ℤ)) (N : ℤ) ⊆ Z := by
    intro x hx
    obtain ⟨hx1, hx2⟩ := Finset.mem_Icc.mp hx
    have hNle : (N : ℤ) ≤ (N : ℤ) * (Cne + 1) := by
      have h1 : (1 : ℤ) ≤ ((Cne + 1 : ℕ) : ℤ) := by
        have : (1 : ℤ) ≤ (Cne : ℤ) + 1 := by omega
        simpa using this
      have h2 : (0 : ℤ) ≤ (N : ℤ) := by positivity
      calc (N : ℤ) = (N : ℤ) * 1 := by ring
        _ ≤ (N : ℤ) * (Cne + 1) := mul_le_mul_of_nonneg_left h1 h2
    simp only [Z, Finset.mem_Icc]
    constructor <;> linarith
  have hsumW_le : ∑ x ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), ‖W x‖ ^ 2 ≤ ∑ x ∈ Z, ‖W x‖ ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub fun x _ _ => by positivity
  -- ## van der Corput in the `y`-variable, uniformly in `x`
  have hvdC : ∀ x ∈ Z, ‖W x‖ ^ 2 ≤ ((M : ℝ) + (H : ℝ)) * (S x + (H : ℝ)) := by
    intro x _
    exact vdc_muL H M hH1 hM (g x) (hg_le x)
  have hsumW : ∑ x ∈ Z, ‖W x‖ ^ 2
      ≤ ((M : ℝ) + (H : ℝ)) * (∑ x ∈ Z, S x + (Z.card : ℝ) * (H : ℝ)) := by
    calc ∑ x ∈ Z, ‖W x‖ ^ 2 ≤ ∑ x ∈ Z, ((M : ℝ) + (H : ℝ)) * (S x + (H : ℝ)) :=
          Finset.sum_le_sum fun x hx => hvdC x hx
      _ = ((M : ℝ) + (H : ℝ)) * ∑ x ∈ Z, (S x + (H : ℝ)) := by rw [Finset.mul_sum]
      _ = ((M : ℝ) + (H : ℝ)) * (∑ x ∈ Z, S x + (Z.card : ℝ) * (H : ℝ)) := by
          rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]
  -- ## the change of variables `x ↦ x + Q i₀ y`
  have hNM_ne : ((N : ℂ) * (M : ℂ)) ≠ 0 := by
    have h1 : (N : ℂ) ≠ 0 := by
      have : (N : ℝ) ≠ 0 := by positivity
      exact_mod_cast this
    have h2 : (M : ℂ) ≠ 0 := by
      have : (M : ℝ) ≠ 0 := by positivity
      exact_mod_cast this
    exact mul_ne_zero h1 h2
  have hS_le : ∑ x ∈ Z, S x ≤ ((N : ℝ) * (M : ℝ)) * R := by
    have e1 : ∑ x ∈ Z, S x = ∑ a ∈ A, Work.Peluse.muL H a *
        (∑ x ∈ Z, ∑ y ∈ Y, (star (g x ((y : ℤ) + a)) * g x (y : ℤ)).re) := by
      simp only [S]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [Finset.mul_sum]
    have e2 : ∀ a : ℤ, (∑ x ∈ Z, ∑ y ∈ Y, (star (g x ((y : ℤ) + a)) * g x (y : ℤ)).re)
        = (∑ x ∈ Z, ∑ y ∈ Y, star (g x ((y : ℤ) + a)) * g x (y : ℤ)).re := by
      intro a
      rw [Complex.re_sum]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [Complex.re_sum]
    have e3 : ∀ a : ℤ, (∑ x ∈ Z, ∑ y ∈ Y, star (g x ((y : ℤ) + a)) * g x (y : ℤ))
        = ∑ x ∈ Z, ∑ y ∈ Y,
            ∏ i : ι, (star (F i (x + Q i ((y : ℤ) + a))) * F i (x + Q i (y : ℤ))) := by
      intro a
      refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
      have h1 : star (g x ((y : ℤ) + a)) = ∏ i : ι, star (F i (x + Q i ((y : ℤ) + a))) := by
        rw [show g x ((y : ℤ) + a) = ∏ i : ι, F i (x + Q i ((y : ℤ) + a)) from rfl]
        exact map_prod (starRingEnd ℂ) (fun i : ι => F i (x + Q i ((y : ℤ) + a))) Finset.univ
      have h2 : g x (y : ℤ) = ∏ i : ι, F i (x + Q i (y : ℤ)) := rfl
      rw [h1, h2, Finset.prod_mul_distrib]
    have e4 : ∀ a : ℤ, (∑ x ∈ Z, ∑ y ∈ Y,
          ∏ i : ι, (star (F i (x + Q i ((y : ℤ) + a))) * F i (x + Q i (y : ℤ))))
        = ∑ x ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), F i₀ x * Sf a x := by
      intro a
      show (∑ x ∈ Finset.Icc (-((N : ℤ) * (Cne + 1))) ((N : ℤ) * (Cne + 1)),
          ∑ y ∈ Finset.Icc 1 M,
            ∏ i : ι, (star (F i (x + Q i ((y : ℤ) + a))) * F i (x + Q i (y : ℤ)))) = _
      exact pet_reindex i₀ Q F hFs hQ a
    have e5 : ∀ a : ℤ, (∑ x ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), F i₀ x * Sf a x)
        = ((N : ℂ) * (M : ℂ)) * T a := by
      intro a
      have htsum : (∑' x : ℤ, F i₀ x * Sf a x)
          = ∑ x ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), F i₀ x * Sf a x := by
        refine tsum_eq_sum ?_
        intro x hx
        rw [hFs i₀ x (pet_natAbs_lt_of_notMem_Icc hx), zero_mul]
      have hT : T a = ((N : ℂ) * (M : ℂ))⁻¹ *
          (∑ x ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), F i₀ x * Sf a x) := by
        show ((N : ℂ) * (M : ℂ))⁻¹ * (∑' x : ℤ, F i₀ x * Sf a x) = _
        rw [htsum]
      rw [hT, mul_inv_cancel_left₀ hNM_ne]
    have e6 : ∑ x ∈ Z, S x
        = ((N : ℝ) * (M : ℝ)) * ∑ a ∈ A, Work.Peluse.muL H a * (T a).re := by
      rw [e1, Finset.mul_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [e2 a, e3 a, e4 a, e5 a]
      have hcast : ((N : ℂ) * (M : ℂ)) = ((((N : ℝ) * (M : ℝ)) : ℝ) : ℂ) := by
        push_cast; ring
      rw [hcast, Complex.re_ofReal_mul]
      ring
    have e7 : ∑ a ∈ A, Work.Peluse.muL H a * (T a).re ≤ R := by
      simp only [R]
      refine Finset.sum_le_sum fun a _ => ?_
      have h1 : (T a).re ≤ ‖T a‖ := Complex.re_le_norm _
      have h2 : 0 ≤ Work.Peluse.muL H a := pet_muL_nonneg H a
      nlinarith
    calc ∑ x ∈ Z, S x
        = ((N : ℝ) * (M : ℝ)) * ∑ a ∈ A, Work.Peluse.muL H a * (T a).re := e6
      _ ≤ ((N : ℝ) * (M : ℝ)) * R := mul_le_mul_of_nonneg_left e7 (by positivity)
  -- ## bookkeeping of the constants
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hCne1 : (1 : ℝ) ≤ (Cne : ℝ) + 1 := by
    have : (0 : ℝ) ≤ (Cne : ℝ) := by positivity
    linarith
  have hZcard : (Z.card : ℝ) ≤ 3 * ((Cne : ℝ) + 1) * (N : ℝ) := by
    have hk : Z.card = 2 * (N * (Cne + 1)) + 1 := by
      simp only [Z]
      rw [Int.card_Icc]
      have hcast : ((N : ℤ) * (Cne + 1) + 1 - (-((N : ℤ) * (Cne + 1))))
          = ((2 * (N * (Cne + 1)) + 1 : ℕ) : ℤ) := by
        push_cast; ring
      rw [hcast, Int.toNat_natCast]
    rw [hk]
    have hcast2 : ((2 * (N * (Cne + 1)) + 1 : ℕ) : ℝ)
        = 2 * ((N : ℝ) * ((Cne : ℝ) + 1)) + 1 := by push_cast; ring
    rw [hcast2]
    have h1 : (1 : ℝ) ≤ (N : ℝ) * ((Cne : ℝ) + 1) := by nlinarith [hN1, hCne1]
    nlinarith [h1]
  have hγ'C : γ' * ((Cne : ℝ) + 1) ≤ γ / 1000 := by
    have hden : (0 : ℝ) < 1000 * ((Cne : ℝ) + 1) := by positivity
    rw [le_div_iff₀ hden] at hγ'γ
    have hX : γ' * ((Cne : ℝ) + 1) * 1000 ≤ γ := by linarith [hγ'γ]
    linarith [hX]
  let C : ℝ := ((N : ℝ) * (M : ℝ))⁻¹ ^ 2 * (2 * (N : ℝ) + 1) * ((M : ℝ) + (H : ℝ))
  have hCnn : 0 ≤ C := by simp only [C]; positivity
  have hbase : γ ≤ C * (((N : ℝ) * (M : ℝ)) * R + (Z.card : ℝ) * (H : ℝ)) := by
    have h1 : γ ≤ ((N : ℝ) * (M : ℝ))⁻¹ ^ 2
        * ‖∑ x ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), f x * W x‖ ^ 2 := by
      have h := hLamW
      rw [htsumf, norm_mul, hnormNM] at h
      calc γ ≤ (((N : ℝ) * (M : ℝ))⁻¹ * ‖∑ x ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), f x * W x‖) ^ 2 := h
        _ = ((N : ℝ) * (M : ℝ))⁻¹ ^ 2 * ‖∑ x ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), f x * W x‖ ^ 2 := by
            rw [mul_pow]
    have h2 : ((N : ℝ) * (M : ℝ))⁻¹ ^ 2 * ‖∑ x ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), f x * W x‖ ^ 2
        ≤ ((N : ℝ) * (M : ℝ))⁻¹ ^ 2 * ((2 * (N : ℝ) + 1)
            * (∑ x ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), ‖W x‖ ^ 2)) :=
      mul_le_mul_of_nonneg_left hnorm2 (by positivity)
    have h3 : ((N : ℝ) * (M : ℝ))⁻¹ ^ 2 * ((2 * (N : ℝ) + 1)
          * (∑ x ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), ‖W x‖ ^ 2))
        ≤ ((N : ℝ) * (M : ℝ))⁻¹ ^ 2 * ((2 * (N : ℝ) + 1) * (∑ x ∈ Z, ‖W x‖ ^ 2)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsumW_le (by positivity)) (by positivity)
    have h4 : ((N : ℝ) * (M : ℝ))⁻¹ ^ 2 * ((2 * (N : ℝ) + 1) * (∑ x ∈ Z, ‖W x‖ ^ 2))
        ≤ ((N : ℝ) * (M : ℝ))⁻¹ ^ 2 * ((2 * (N : ℝ) + 1)
            * (((M : ℝ) + (H : ℝ)) * (((N : ℝ) * (M : ℝ)) * R + (Z.card : ℝ) * (H : ℝ)))) := by
      refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ (by positivity)) (by positivity)
      calc ∑ x ∈ Z, ‖W x‖ ^ 2
          ≤ ((M : ℝ) + (H : ℝ)) * (∑ x ∈ Z, S x + (Z.card : ℝ) * (H : ℝ)) := hsumW
        _ ≤ ((M : ℝ) + (H : ℝ)) * (((N : ℝ) * (M : ℝ)) * R + (Z.card : ℝ) * (H : ℝ)) := by
            refine mul_le_mul_of_nonneg_left ?_ (by positivity)
            linarith [hS_le]
    calc γ ≤ ((N : ℝ) * (M : ℝ))⁻¹ ^ 2 * ‖∑ x ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), f x * W x‖ ^ 2 := h1
      _ ≤ ((N : ℝ) * (M : ℝ))⁻¹ ^ 2 * ((2 * (N : ℝ) + 1)
            * (∑ x ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), ‖W x‖ ^ 2)) := h2
      _ ≤ ((N : ℝ) * (M : ℝ))⁻¹ ^ 2 * ((2 * (N : ℝ) + 1) * (∑ x ∈ Z, ‖W x‖ ^ 2)) := h3
      _ ≤ ((N : ℝ) * (M : ℝ))⁻¹ ^ 2 * ((2 * (N : ℝ) + 1)
            * (((M : ℝ) + (H : ℝ)) * (((N : ℝ) * (M : ℝ)) * R + (Z.card : ℝ) * (H : ℝ)))) := h4
      _ = C * (((N : ℝ) * (M : ℝ)) * R + (Z.card : ℝ) * (H : ℝ)) := by simp only [C]; ring
  have hCNM : C * ((N : ℝ) * (M : ℝ)) ≤ 6 := by
    have hCMNm : C * ((N : ℝ) * (M : ℝ))
        = ((2 * (N : ℝ) + 1) / (N : ℝ)) * (((M : ℝ) + (H : ℝ)) / (M : ℝ)) := by
      have hNne : (N : ℝ) ≠ 0 := by positivity
      have hMne : (M : ℝ) ≠ 0 := by positivity
      simp only [C]
      field_simp
    rw [hCMNm]
    have hN2 : (2 * (N : ℝ) + 1) / (N : ℝ) ≤ 3 := by
      rw [div_le_iff₀ hNpos]
      linarith [hN1]
    have hMH : ((M : ℝ) + (H : ℝ)) / (M : ℝ) ≤ 1 + γ' := by
      rw [div_le_iff₀ hMpos]
      linarith [hHle]
    have h1 : (0 : ℝ) ≤ (2 * (N : ℝ) + 1) / (N : ℝ) := by positivity
    have h2 : (0 : ℝ) ≤ ((M : ℝ) + (H : ℝ)) / (M : ℝ) := by positivity
    calc ((2 * (N : ℝ) + 1) / (N : ℝ)) * (((M : ℝ) + (H : ℝ)) / (M : ℝ))
        ≤ 3 * (1 + γ') := mul_le_mul hN2 hMH h2 (by norm_num)
      _ ≤ 6 := by linarith [hγ'le]
  have hCZH : C * ((Z.card : ℝ) * (H : ℝ)) ≤ (18 / 1000) * γ := by
    have hsplit : C * ((Z.card : ℝ) * (H : ℝ))
        = (C * ((N : ℝ) * (M : ℝ)))
            * (((Z.card : ℝ) * (H : ℝ)) / ((N : ℝ) * (M : ℝ))) := by
      field_simp
    rw [hsplit]
    have hquot : ((Z.card : ℝ) * (H : ℝ)) / ((N : ℝ) * (M : ℝ)) ≤ (3 / 1000) * γ := by
      rw [div_le_iff₀ (by positivity : (0 : ℝ) < (N : ℝ) * (M : ℝ))]
      calc (Z.card : ℝ) * (H : ℝ) ≤ (Z.card : ℝ) * (γ' * (M : ℝ)) :=
            mul_le_mul_of_nonneg_left hHle (by positivity)
        _ ≤ (3 * ((Cne : ℝ) + 1) * (N : ℝ)) * (γ' * (M : ℝ)) :=
            mul_le_mul_of_nonneg_right hZcard (by positivity)
        _ = (3 * ((N : ℝ) * (M : ℝ))) * (γ' * ((Cne : ℝ) + 1)) := by ring
        _ ≤ (3 * ((N : ℝ) * (M : ℝ))) * (γ / 1000) :=
            mul_le_mul_of_nonneg_left hγ'C (by positivity)
        _ = (3 / 1000) * γ * ((N : ℝ) * (M : ℝ)) := by ring
    calc (C * ((N : ℝ) * (M : ℝ))) * (((Z.card : ℝ) * (H : ℝ)) / ((N : ℝ) * (M : ℝ)))
        ≤ 6 * ((3 / 1000) * γ) := mul_le_mul hCNM hquot (by positivity) (by norm_num)
      _ = (18 / 1000) * γ := by ring
  have hexp : C * (((N : ℝ) * (M : ℝ)) * R + (Z.card : ℝ) * (H : ℝ))
      = C * ((N : ℝ) * (M : ℝ)) * R + C * ((Z.card : ℝ) * (H : ℝ)) := by ring
  rw [hexp] at hbase
  have h1 : C * ((N : ℝ) * (M : ℝ)) * R ≤ 6 * R := by
    have := mul_le_mul_of_nonneg_right hCNM hR_nn
    linarith [this]
  nlinarith [hbase, h1, hCZH, hγ]

end

end Work.Peluse.PET
