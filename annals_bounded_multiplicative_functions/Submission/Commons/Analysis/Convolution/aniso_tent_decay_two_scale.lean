import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Real

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

open scoped BigOperators

namespace Commons.Analysis.Convolution

/-- Two-scale decay for the anisotropic tent weight.

If `δ₁ ≥ δ₂` and the tent weight of `x` at scale `δ₂` is `2^A` times smaller than
that of `y`, then `x - y` cannot be small at the (coarser) scale `δ₁`: the tent
weight of `x - y` at scale `δ₁` is bounded by `2^A` times the tent weight of `x`
at scale `δ₂`. -/
theorem aniso_tent_decay_two_scale (k : ℕ) (hk : 1 ≤ k) {A δ₁ δ₂ : ℝ}
    (hA : (k : ℝ) * (k + 1) / 2 ≤ A) (hδ20 : 0 < δ₂) (hδ21 : δ₂ ≤ 1)
    (hδ12 : δ₂ ≤ δ₁) (hδ11 : δ₁ ≤ 1) (x y : Fin k → ℝ)
    (h : 2 ^ A * (δ₂ ^ (k * (k + 1) / 2) *
          (max 1 ((Finset.univ : Finset (Fin k)).sup' ⟨⟨0, hk⟩, Finset.mem_univ _⟩
            fun i => δ₂ ^ (i.val + 1) * |x i|)) ^ (-A))
        < δ₂ ^ (k * (k + 1) / 2) *
          (max 1 ((Finset.univ : Finset (Fin k)).sup' ⟨⟨0, hk⟩, Finset.mem_univ _⟩
            fun i => δ₂ ^ (i.val + 1) * |y i|)) ^ (-A)) :
    δ₁ ^ (k * (k + 1) / 2) *
        (max 1 ((Finset.univ : Finset (Fin k)).sup' ⟨⟨0, hk⟩, Finset.mem_univ _⟩
          fun i => δ₁ ^ (i.val + 1) * |(x - y) i|)) ^ (-A)
      ≤ 2 ^ A * (δ₂ ^ (k * (k + 1) / 2) *
          (max 1 ((Finset.univ : Finset (Fin k)).sup' ⟨⟨0, hk⟩, Finset.mem_univ _⟩
            fun i => δ₂ ^ (i.val + 1) * |x i|)) ^ (-A)) := by
  classical
  have hδ1pos : 0 < δ₁ := lt_of_lt_of_le hδ20 hδ12
  set Dn : ℕ := k * (k + 1) / 2 with hDn
  set fx : Fin k → ℝ := fun i => δ₂ ^ (i.val + 1) * |x i| with hfx
  set fy : Fin k → ℝ := fun i => δ₂ ^ (i.val + 1) * |y i| with hfy
  set gz : Fin k → ℝ := fun i => δ₁ ^ (i.val + 1) * |(x - y) i| with hgz
  set Sx := (Finset.univ : Finset (Fin k)).sup' ⟨⟨0, hk⟩, Finset.mem_univ _⟩ fx with hSx
  set Sy := (Finset.univ : Finset (Fin k)).sup' ⟨⟨0, hk⟩, Finset.mem_univ _⟩ fy with hSy
  set Sz := (Finset.univ : Finset (Fin k)).sup' ⟨⟨0, hk⟩, Finset.mem_univ _⟩ gz with hSz
  set Mx := max 1 Sx with hMx
  set My := max 1 Sy with hMy
  set Mz := max 1 Sz with hMz
  have hApos : 0 < A := by
    have hpos : (0 : ℝ) < (k : ℝ) * (k + 1) / 2 := by
      have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
      nlinarith
    linarith
  have hArgneg : -A < 0 := by linarith
  have hMxpos : 0 < Mx := by rw [hMx]; exact lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hMypos : 0 < My := by rw [hMy]; exact lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hMy1 : 1 ≤ My := by rw [hMy]; exact le_max_left _ _
  have hDnpos : 0 < δ₂ ^ Dn := pow_pos hδ20 Dn
  -- Step 1: cancel the common factor `δ₂ ^ Dn` from the hypothesis.
  have h2 : 2 ^ A * Mx ^ (-A) < My ^ (-A) := by
    have hh : δ₂ ^ Dn * (2 ^ A * Mx ^ (-A)) < δ₂ ^ Dn * My ^ (-A) := by
      have h' := h
      rw [← mul_assoc, mul_comm (2 ^ A) (δ₂ ^ Dn), mul_assoc] at h'
      exact h'
    exact (mul_lt_mul_iff_right₀ hDnpos).1 hh
  have hkeyM : (Mx / 2) ^ (-A) = 2 ^ A * Mx ^ (-A) := by
    have h2A : (2⁻¹ : ℝ) ^ (-A) = 2 ^ A := by
      rw [Real.inv_rpow (by norm_num : (0 : ℝ) ≤ (2 : ℝ))]
      rw [← Real.rpow_neg (by norm_num : (0 : ℝ) ≤ (2 : ℝ)) (-A), neg_neg]
    rw [div_eq_mul_inv,
      Real.mul_rpow (le_of_lt hMxpos) (by positivity : (0 : ℝ) ≤ (2 : ℝ)⁻¹), h2A]
    exact mul_comm _ _
  -- Step 2: hence `My < Mx / 2`, so `Mx > 1` and `Sx = Mx`.
  have hMy_lt : My < Mx / 2 := by
    have hMx2pos : 0 < Mx / 2 := by linarith
    have h3 : (Mx / 2) ^ (-A) < My ^ (-A) := by rw [hkeyM]; exact h2
    exact (Real.rpow_lt_rpow_iff_of_neg hMx2pos hMypos hArgneg).1 h3
  have hMx_gt_one : 1 < Mx := by linarith
  have hSx_eq : Sx = Mx := by
    have hSx_ge : 1 ≤ Sx := by
      by_contra hc
      have hc' : Sx < 1 := not_le.mp hc
      have h1 : Mx = 1 := by rw [hMx, max_eq_left (le_of_lt hc')]
      linarith
    rw [hMx, max_eq_right hSx_ge]
  -- Step 3: a coordinate `i0` where the `δ₂`-weight of `x` is maximal.
  obtain ⟨i0, -, hi0⟩ := Finset.exists_mem_eq_sup' (s := (Finset.univ : Finset (Fin k)))
      (H := ⟨⟨0, hk⟩, Finset.mem_univ _⟩) fx
  have hi0_val : δ₂ ^ (i0.val + 1) * |x i0| = Mx := by
    have h1 : fx i0 = Mx := hi0.symm.trans hSx_eq
    simpa [hfx] using h1
  have hMy_bound : δ₂ ^ (i0.val + 1) * |y i0| < Mx / 2 := by
    have hle_Sy : fy i0 ≤ Sy := by
      rw [hSy]; exact Finset.le_sup' fy (Finset.mem_univ i0)
    have hle : fy i0 ≤ My := by
      rw [hMy]; exact le_trans hle_Sy (le_max_right _ _)
    have hle' : δ₂ ^ (i0.val + 1) * |y i0| ≤ My := by simpa [hfy] using hle
    linarith
  -- Step 4: at `i0` the difference `x - y` is bounded below at scale `δ₂`.
  have hdiff_low : Mx / 2 < δ₂ ^ (i0.val + 1) * |x i0 - y i0| := by
    have h1 : δ₂ ^ (i0.val + 1) * |x i0| - δ₂ ^ (i0.val + 1) * |y i0|
        ≤ δ₂ ^ (i0.val + 1) * |x i0 - y i0| := by
      rw [← mul_sub]
      exact mul_le_mul_of_nonneg_left (abs_sub_abs_le_abs_sub _ _) (le_of_lt (pow_pos hδ20 _))
    linarith [hi0_val, hMy_bound]
  -- the ratio `ρ = δ₁/δ₂ ≥ 1`
  set ρ : ℝ := δ₁ / δ₂ with hρ
  have hρpos : 0 < ρ := by rw [hρ]; positivity
  have hρge1 : 1 ≤ ρ := by rw [hρ, one_le_div hδ20]; exact hδ12
  have hxy_low : Mx / (2 * δ₂ ^ (i0.val + 1)) < |x i0 - y i0| := by
    rw [div_lt_iff₀ (by positivity : (0 : ℝ) < 2 * δ₂ ^ (i0.val + 1))]
    nlinarith [hdiff_low]
  -- Step 5: transfer to the coarser scale `δ₁`, extracting a factor `ρ ^ (i0+1)`.
  have hSz_low : ρ ^ (i0.val + 1) * (Mx / 2) < Sz := by
    have hgz_le : gz i0 ≤ Sz := by rw [hSz]; exact Finset.le_sup' gz (Finset.mem_univ i0)
    have hprod : ρ ^ (i0.val + 1) * (Mx / 2)
        = δ₁ ^ (i0.val + 1) * (Mx / (2 * δ₂ ^ (i0.val + 1))) := by
      rw [hρ, div_pow]
      field_simp
    rw [hprod]
    calc δ₁ ^ (i0.val + 1) * (Mx / (2 * δ₂ ^ (i0.val + 1)))
        < δ₁ ^ (i0.val + 1) * |x i0 - y i0| :=
          mul_lt_mul_of_pos_left hxy_low (pow_pos hδ1pos _)
      _ = gz i0 := by rw [hgz]; rfl
      _ ≤ Sz := hgz_le
  have hDn_cast : (Dn : ℝ) = (k : ℝ) * (k + 1) / 2 := by
    rw [hDn, Nat.cast_div (Nat.even_mul_succ_self k).two_dvd (by norm_num : (2 : ℝ) ≠ 0)]
    push_cast
    ring
  have hDn_le_A : (Dn : ℝ) ≤ A := by rw [hDn_cast]; exact hA
  -- Step 6: `ρ ^ ((Dn)/A) ≤ ρ ^ (i0+1)` because `Dn/A ≤ 1 ≤ i0+1`.
  have hExp : (Dn : ℝ) / A ≤ ((i0.val + 1 : ℕ) : ℝ) := by
    have h1 : (Dn : ℝ) / A ≤ 1 := (div_le_one hApos).2 hDn_le_A
    have h2 : (1 : ℝ) ≤ ((i0.val + 1 : ℕ) : ℝ) := by
      have : (1 : ℕ) ≤ i0.val + 1 := by omega
      exact_mod_cast this
    linarith
  have hρpow_le : ρ ^ ((Dn : ℝ) / A) ≤ ρ ^ (i0.val + 1 : ℕ) := by
    rw [← Real.rpow_natCast ρ (i0.val + 1)]
    exact Real.rpow_le_rpow_of_exponent_le hρge1 hExp
  -- Step 7: monotonicity of `z ↦ z ^ (-A)`.
  set c : ℝ := ρ ^ ((Dn : ℝ) / A) * (Mx / 2) with hc
  have hcpos : 0 < c := by rw [hc]; positivity
  have hc_lt_Sz : c < Sz := by
    rw [hc]
    exact lt_of_le_of_lt (mul_le_mul_of_nonneg_right hρpow_le (by positivity)) hSz_low
  have hc_lt_Mz : c < Mz := by
    rw [hMz]; exact lt_of_lt_of_le hc_lt_Sz (le_max_right 1 Sz)
  have hpow_lt : Mz ^ (-A) < c ^ (-A) := Real.rpow_lt_rpow_of_neg hcpos hc_lt_Mz hArgneg
  -- Step 8: evaluate `c ^ (-A)`.
  have hkeyc : c ^ (-A) = ρ ^ (-(Dn : ℝ)) * 2 ^ A * Mx ^ (-A) := by
    rw [hc, Real.mul_rpow (Real.rpow_nonneg (le_of_lt hρpos) _) (by positivity : (0 : ℝ) ≤ Mx / 2)]
    rw [← Real.rpow_mul (le_of_lt hρpos) ((Dn : ℝ) / A) (-A)]
    rw [show (Dn : ℝ) / A * (-A) = -(Dn : ℝ) by field_simp]
    rw [hkeyM]
    ring
  -- Step 9: `δ₁ ^ Dn * ρ ^ (-Dn) = δ₂ ^ Dn`.
  have hfinal : δ₁ ^ Dn * ρ ^ (-(Dn : ℝ)) = δ₂ ^ Dn := by
    rw [hρ, ← Real.rpow_natCast δ₁ Dn, ← Real.rpow_natCast δ₂ Dn]
    rw [Real.rpow_neg (by positivity : (0 : ℝ) ≤ δ₁ / δ₂)]
    rw [← Real.inv_rpow (by positivity : (0 : ℝ) ≤ δ₁ / δ₂)]
    rw [inv_div]
    rw [← Real.mul_rpow (by positivity : (0 : ℝ) ≤ δ₁) (by positivity : (0 : ℝ) ≤ δ₂ / δ₁)]
    congr 1
    field_simp
  have hδ1Dnnn : 0 ≤ δ₁ ^ Dn := pow_nonneg (le_of_lt hδ1pos) Dn
  calc δ₁ ^ Dn * Mz ^ (-A)
      ≤ δ₁ ^ Dn * c ^ (-A) := mul_le_mul_of_nonneg_left (le_of_lt hpow_lt) hδ1Dnnn
    _ = δ₁ ^ Dn * (ρ ^ (-(Dn : ℝ)) * 2 ^ A * Mx ^ (-A)) := by rw [hkeyc]
    _ = (δ₁ ^ Dn * ρ ^ (-(Dn : ℝ))) * (2 ^ A * Mx ^ (-A)) := by ring
    _ = δ₂ ^ Dn * (2 ^ A * Mx ^ (-A)) := by rw [hfinal]
    _ = 2 ^ A * (δ₂ ^ Dn * Mx ^ (-A)) := by ring

end Commons.Analysis.Convolution
