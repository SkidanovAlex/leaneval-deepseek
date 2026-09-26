import Mathlib
import Submission.Work.Asymptotics.CoincForm
import Submission.Work.Asymptotics.jInvariantFun_eq_smul_of_eq
import Submission.Work.Kernels.Kernels

namespace Work.Asymptotics.Tile

open UpperHalfPlane

set_option maxHeartbeats 1600000

/-- **The orbit points of `i t` of height `≥ 2` and `|Re| ≤ 1` are the translates `m + σ`.**

If `σ ∈ ℍ` has `|Re σ| ≤ 1` and `2 ≤ Im σ`, and `t ∈ [1,3]` with `j σ = j (i t)`, then
`σ = m + i t` for some `m ∈ {-1, 0, 1}`. -/
theorem tile_orbit_classification {σ : UpperHalfPlane} (hre : |σ.re| ≤ 1) (him : 2 ≤ σ.im)
    (t : ℝ) (ht : 0 < t) (h1 : 1 ≤ t) (h3 : t ≤ 3)
    (hj : Work.Kernels.jInvariantFun σ
      = Work.Kernels.jInvariantFun (Work.Kernels.imagAxis t ht)) :
    ∃ m : ℤ, (m = -1 ∨ m = 0 ∨ m = 1) ∧ σ = (m : ℝ) +ᵥ (Work.Kernels.imagAxis t ht) := by
  obtain ⟨γ, hγ⟩ := Work.Asymptotics.jInvariantFun_eq_smul_of_eq (τ := σ)
    (w := Work.Kernels.imagAxis t ht) hj
  obtain ⟨hE1, hE2⟩ := Work.Asymptotics.entries_of_smul_imagAxis_aux ht σ hγ
  set x : ℝ := σ.re with hx
  set y : ℝ := σ.im with hy
  set A : ℝ := ((γ 0 0 : ℤ) : ℝ) with hA
  set B : ℝ := ((γ 0 1 : ℤ) : ℝ) with hB
  set C : ℝ := ((γ 1 0 : ℤ) : ℝ) with hC
  set Dd : ℝ := ((γ 1 1 : ℤ) : ℝ) with hD
  have hE1' : B = x * Dd - y * C * t := by rw [hB, hx, hD, hy, hC]; exact hE1
  have hE2' : A * t = x * C * t + y * Dd := by rw [hA, hx, hC, hy, hD]; exact hE2
  have hdet : A * Dd - B * C = 1 := by
    have h := γ.2
    rw [Matrix.det_fin_two] at h
    have h' := congrArg (fun m : ℤ => ((m : ℝ))) h
    push_cast at h'
    rw [hA, hB, hC, hD]
    linarith [h']
  have hupper : y * (C ^ 2 * t ^ 2 + Dd ^ 2) = t := by
    have e1 : y * (C ^ 2 * t ^ 2 + Dd ^ 2)
        = Dd * (x * C * t + y * Dd) - (C * t) * (x * Dd - y * C * t) := by ring
    have e2 : Dd * (x * C * t + y * Dd) - (C * t) * (x * Dd - y * C * t)
        = Dd * (A * t) - (C * t) * B := by rw [← hE2', ← hE1']
    have e3 : Dd * (A * t) - (C * t) * B = t := by
      have h : Dd * (A * t) - (C * t) * B = t * (A * Dd - B * C) := by ring
      rw [h, hdet]; ring
    rw [e1, e2, e3]
  have hDne : C ^ 2 * t ^ 2 + Dd ^ 2 ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hupper
    linarith [ht]
  have hDpos : 0 < C ^ 2 * t ^ 2 + Dd ^ 2 :=
    lt_of_le_of_ne (by positivity) (Ne.symm hDne)
  have hyval : y = t / (C ^ 2 * t ^ 2 + Dd ^ 2) := by
    rw [eq_div_iff (ne_of_gt hDpos)]; exact hupper
  -- the height hypothesis forces `C = 0`
  have hden_le : C ^ 2 * t ^ 2 + Dd ^ 2 ≤ t / 2 := by
    have h2' : (2 : ℝ) ≤ t / (C ^ 2 * t ^ 2 + Dd ^ 2) := by rw [← hyval]; exact him
    have h3' : 2 * (C ^ 2 * t ^ 2 + Dd ^ 2) ≤ t := (le_div_iff₀ hDpos).mp h2'
    linarith
  have hCsq_half : C ^ 2 ≤ 1 / 2 := by
    have ht2pos : 0 < t ^ 2 := pow_pos ht 2
    have h1' : C ^ 2 * t ^ 2 ≤ t / 2 := by nlinarith [sq_nonneg Dd]
    have h2' : C ^ 2 ≤ (t / 2) / t ^ 2 := by rw [le_div_iff₀ ht2pos]; exact h1'
    have h3' : (t / 2) / t ^ 2 ≤ 1 / 2 := by
      rw [div_le_div_iff₀ ht2pos (by norm_num : (0 : ℝ) < 2)]
      nlinarith [mul_nonneg (le_of_lt ht) (by linarith : (0 : ℝ) ≤ t - 1)]
    linarith
  have hCeq0 : γ 1 0 = 0 := by
    have h1' : C ^ 2 < 1 := by linarith
    have h2' : |C| < 1 := by rw [abs_lt]; constructor <;> nlinarith [h1']
    have h3' : ((γ 1 0 : ℤ) : ℝ) < 1 := by rw [← hC]; exact (abs_lt.mp h2').2
    have h4' : -1 < ((γ 1 0 : ℤ) : ℝ) := by rw [← hC]; exact (abs_lt.mp h2').1
    have h5' : γ 1 0 < 1 := by exact_mod_cast h3'
    have h6' : -1 < γ 1 0 := by exact_mod_cast h4'
    omega
  have hCz : C = 0 := by rw [hC, hCeq0]; norm_num
  -- the determinant then forces `A * Dd = 1`
  have hAD : A * Dd = 1 := by
    have h := hdet
    rw [hCz, mul_zero, sub_zero] at h
    exact h
  have hADZ : γ 0 0 * γ 1 1 = 1 := by
    have h : ((γ 0 0 : ℤ) : ℝ) * ((γ 1 1 : ℤ) : ℝ) = 1 := by
      rw [← hA, ← hD]; exact hAD
    have h2 : ((γ 0 0 * γ 1 1 : ℤ) : ℝ) = 1 := by push_cast; exact h
    exact_mod_cast h2
  have hDdsq : Dd ^ 2 = 1 := by
    have h11 : γ 1 1 = 1 ∨ γ 1 1 = -1 := by
      rcases Int.eq_one_or_neg_one_of_mul_eq_one' hADZ with ⟨-, h⟩ | ⟨-, h⟩
      · exact Or.inl h
      · exact Or.inr h
    rw [hD]
    rcases h11 with h | h <;> rw [h] <;> norm_num
  -- the coordinates of `σ`
  have hy_t : y = t := by
    have h := hupper
    rw [hCz] at h
    have h' : y * Dd ^ 2 = t := by simpa using h
    rw [hDdsq, mul_one] at h'
    exact h'
  have hx_BD : x = B * Dd := by
    have hBxD : B = x * Dd := by
      have h := hE1'
      rw [hCz, hy_t] at h
      simpa using h
    have hxx : x * Dd ^ 2 = B * Dd := by
      have h1' : x * Dd ^ 2 = (x * Dd) * Dd := by ring
      rw [h1', ← hBxD]
    rw [hDdsq, mul_one] at hxx
    exact hxx
  have hBD : ((γ 0 1 * γ 1 1 : ℤ) : ℝ) = B * Dd := by
    rw [hB, hD]; push_cast; ring
  have hm_re : ((γ 0 1 * γ 1 1 : ℤ) : ℝ) = σ.re := by
    rw [hBD, ← hx, hx_BD]
  have hm_mem : γ 0 1 * γ 1 1 = -1 ∨ γ 0 1 * γ 1 1 = 0 ∨ γ 0 1 * γ 1 1 = 1 := by
    have habs : |((γ 0 1 * γ 1 1 : ℤ) : ℝ)| ≤ 1 := by rw [hm_re]; exact hre
    have habsZ : |(γ 0 1 * γ 1 1 : ℤ)| ≤ 1 := by
      rw [← Int.cast_abs] at habs
      exact_mod_cast habs
    have hle1 : γ 0 1 * γ 1 1 ≤ 1 := (abs_le.mp habsZ).2
    have hge1 : -1 ≤ γ 0 1 * γ 1 1 := (abs_le.mp habsZ).1
    omega
  have hσcoe : (σ : ℂ) = (σ.re : ℂ) + (σ.im : ℂ) * Complex.I := by
    have hh := Complex.re_add_im (σ : ℂ)
    rw [UpperHalfPlane.coe_re, UpperHalfPlane.coe_im] at hh
    exact hh.symm
  have hBDC : ((B * Dd : ℝ) : ℂ) = ((γ 0 1 * γ 1 1 : ℤ) : ℂ) := by
    rw [hB, hD]; push_cast; ring
  have hcomplex : (σ : ℂ) = ((γ 0 1 * γ 1 1 : ℤ) : ℂ) + (t : ℂ) * Complex.I := by
    rw [hσcoe, ← hx, ← hy, hy_t, hx_BD, hBDC]
  refine ⟨γ 0 1 * γ 1 1, hm_mem, ?_⟩
  apply UpperHalfPlane.ext
  rw [UpperHalfPlane.coe_vadd, hcomplex]
  rw [show ((Work.Kernels.imagAxis t ht : ℍ) : ℂ) = (t : ℂ) * Complex.I from rfl]
  push_cast
  ring

end Work.Asymptotics.Tile
