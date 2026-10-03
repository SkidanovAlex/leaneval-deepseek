import Mathlib

/-!
# Lower bounds for `1 / Γ` in vertical strips

We prove that on a vertical strip `0 ≤ Re s ≤ K`, the reciprocal Gamma function
grows at most exponentially in the imaginary part:

`‖(Γ (u + i t))⁻¹‖ ≤ c * exp (C * |t|)` for `0 ≤ u ≤ K`.

The proof strategy is:

* For `s` with `1 ≤ |Im s|` we bound `1/Γ(s) = Γ(1-s) sin(π s)/π` (reflection formula).
  The factor `|sin (π s)|` is at most `exp (π |Im s|)`, and `Γ(1-s)` is bounded by `1`
  in the relevant strips, using that `|Γ w| ≤ Γ (Re w)` for `Re w > 0` (Euler's integral)
  and that `Γ ≤ 1` on `[1,2]` (convexity of `Γ`).
* The general strip `0 ≤ u ≤ K` is reduced to the base strip `0 ≤ Re ≤ 2` by shifting
  down by an integer; each shifted factor has modulus `≥ |Im s| ≥ 1`, hence can be
  discarded when bounding above.
* Finally, the compact set `0 ≤ Re s ≤ K`, `|Im s| ≤ 1` is handled by continuity.
-/

namespace Work.FIArea5.S16Hecke

open MeasureTheory

/-- The fundamental bound `‖Γ w‖ ≤ Γ (Re w)` for `Re w > 0`, from Euler's integral. -/
lemma norm_GammaIntegral_le_Gamma_re (s : ℂ) (hs : 0 < s.re) :
    ‖Complex.GammaIntegral s‖ ≤ Real.Gamma s.re := by
  calc ‖Complex.GammaIntegral s‖
      = ‖∫ x in Set.Ioi (0:ℝ), ↑(Real.exp (-x)) * (↑x : ℂ) ^ (s - 1)‖ := rfl
    _ ≤ ∫ x in Set.Ioi (0:ℝ), ‖↑(Real.exp (-x)) * (↑x : ℂ) ^ (s - 1)‖ :=
        MeasureTheory.norm_integral_le_integral_norm _
    _ = ∫ x in Set.Ioi (0:ℝ), Real.exp (-x) * x ^ (s.re - 1) := by
        refine setIntegral_congr_fun measurableSet_Ioi ?_
        intro x hx
        have hx0 : 0 < x := hx
        show ‖↑(Real.exp (-x)) * (↑x : ℂ) ^ (s - 1)‖ = Real.exp (-x) * x ^ (s.re - 1)
        rw [norm_mul, Complex.norm_of_nonneg (Real.exp_pos (-x)).le,
            Complex.norm_cpow_eq_rpow_re_of_pos hx0 (s - 1)]
        simp
    _ = Real.Gamma s.re := by
        rw [Real.Gamma_eq_integral hs]

/-- `‖Γ s‖ ≤ Γ (Re s)` for `0 < Re s`. -/
lemma norm_Gamma_le_Gamma_re (s : ℂ) (hs : 0 < s.re) :
    ‖Complex.Gamma s‖ ≤ Real.Gamma s.re := by
  rw [Complex.Gamma_eq_integral hs]
  exact norm_GammaIntegral_le_Gamma_re s hs

/-- `Γ ≤ 1` on the interval `[1,2]`, by convexity of `Γ` and `Γ 1 = Γ 2 = 1`. -/
lemma Gamma_le_one_of_mem_Icc {x : ℝ} (hx : x ∈ Set.Icc 1 2) : Real.Gamma x ≤ 1 := by
  have h := Real.convexOn_Gamma.le_max_of_mem_Icc (by norm_num : (1:ℝ) ∈ Set.Ioi 0)
      (by norm_num : (2:ℝ) ∈ Set.Ioi 0) hx
  have h2 : Real.Gamma 2 = 1 := by
    rw [show (2:ℝ) = 1 + 1 by norm_num, Real.Gamma_add_one (s := 1) one_ne_zero,
      Real.Gamma_one, mul_one]
  rw [Real.Gamma_one, h2, max_self] at h
  exact h

/-- `‖sin z‖ ≤ exp |Im z|` for every complex `z`. -/
lemma norm_sin_le_exp_im (z : ℂ) : ‖Complex.sin z‖ ≤ Real.exp |z.im| := by
  rw [Complex.sin]
  have h1 : ‖Complex.exp (-z * Complex.I)‖ = Real.exp z.im := by
    rw [Complex.norm_exp]; simp
  have h2 : ‖Complex.exp (z * Complex.I)‖ = Real.exp (-z.im) := by
    rw [Complex.norm_exp]; simp
  calc ‖(Complex.exp (-z * Complex.I) - Complex.exp (z * Complex.I)) * Complex.I / 2‖
      = ‖Complex.exp (-z * Complex.I) - Complex.exp (z * Complex.I)‖ / 2 := by
        rw [norm_div, norm_mul, Complex.norm_I, Complex.norm_ofNat]; ring
    _ ≤ (‖Complex.exp (-z * Complex.I)‖ + ‖Complex.exp (z * Complex.I)‖) / 2 := by
        gcongr; exact norm_sub_le _ _
    _ = (Real.exp z.im + Real.exp (-z.im)) / 2 := by rw [h1, h2]
    _ = Real.cosh z.im := by rw [Real.cosh_eq]
    _ ≤ Real.exp |z.im| := by
        rw [Real.cosh_eq]
        have ha : Real.exp z.im ≤ Real.exp |z.im| := Real.exp_le_exp.mpr (le_abs_self _)
        have hb : Real.exp (-z.im) ≤ Real.exp |z.im| := Real.exp_le_exp.mpr (neg_le_abs _)
        linarith

/-- In the range `0 ≤ Re s ≤ 2`, `1 ≤ |Im s|`, the value `Γ (1 - s)` is bounded by `1`. -/
lemma Gamma_one_sub_le_one (s : ℂ) (hs0 : 0 ≤ s.re) (hs2 : s.re ≤ 2) (ht : 1 ≤ |s.im|) :
    ‖Complex.Gamma (1 - s)‖ ≤ 1 := by
  set z : ℂ := 1 - s with hz
  have hzre : z.re = 1 - s.re := by simp [hz]
  have hzim : z.im = -s.im := by simp [hz]
  have hznorm : 1 ≤ ‖z‖ := by
    have h := Complex.abs_im_le_norm z
    rw [hzim, abs_neg] at h
    linarith
  have hz0 : z ≠ 0 := by
    intro h0; rw [h0, norm_zero] at hznorm; linarith
  by_cases hle : s.re ≤ 1
  · have hz1re : (z + 1).re = 2 - s.re := by rw [hz]; simp; ring
    have hpos : 0 < (z + 1).re := by rw [hz1re]; linarith
    have hrec : Complex.Gamma z = Complex.Gamma (z + 1) / z := by
      rw [eq_div_iff hz0, mul_comm, ← Complex.Gamma_add_one z hz0]
    calc ‖Complex.Gamma z‖ = ‖Complex.Gamma (z + 1)‖ / ‖z‖ := by rw [hrec, norm_div]
      _ ≤ ‖Complex.Gamma (z + 1)‖ := by
          rw [div_le_iff₀ (by linarith : (0:ℝ) < ‖z‖)]
          exact le_mul_of_one_le_right (norm_nonneg _) hznorm
      _ ≤ Real.Gamma (z + 1).re := norm_Gamma_le_Gamma_re _ hpos
      _ ≤ 1 := Gamma_le_one_of_mem_Icc (by rw [hz1re]; constructor <;> linarith)
  · rw [not_le] at hle
    have hz2re : (z + 2).re = 3 - s.re := by rw [hz]; simp; ring
    have hz1im : (z + 1).im = -s.im := by
      rw [Complex.add_im, hzim, Complex.one_im, add_zero]
    have hz1norm : 1 ≤ ‖z + 1‖ := by
      have h := Complex.abs_im_le_norm (z + 1)
      rw [hz1im, abs_neg] at h
      linarith
    have hz10 : z + 1 ≠ 0 := by
      intro h0; rw [h0, norm_zero] at hz1norm; linarith
    have hrec : Complex.Gamma z = Complex.Gamma (z + 2) / (z * (z + 1)) := by
      have h1 : Complex.Gamma (z + 1) = z * Complex.Gamma z := Complex.Gamma_add_one z hz0
      have h2 : Complex.Gamma (z + 2) = (z + 1) * Complex.Gamma (z + 1) := by
        rw [show z + 2 = (z + 1) + 1 by ring]
        exact Complex.Gamma_add_one (z + 1) hz10
      rw [h2, h1, eq_div_iff (mul_ne_zero hz0 hz10)]
      ring
    have hpos : 0 < (z + 2).re := by rw [hz2re]; linarith
    have hprod : 1 ≤ ‖z * (z + 1)‖ := by
      rw [norm_mul]; nlinarith
    calc ‖Complex.Gamma z‖ = ‖Complex.Gamma (z + 2)‖ / ‖z * (z + 1)‖ := by rw [hrec, norm_div]
      _ ≤ ‖Complex.Gamma (z + 2)‖ := by
          rw [div_le_iff₀ (by linarith : (0:ℝ) < ‖z * (z + 1)‖)]
          exact le_mul_of_one_le_right (norm_nonneg _) hprod
      _ ≤ Real.Gamma (z + 2).re := norm_Gamma_le_Gamma_re _ hpos
      _ ≤ 1 := Gamma_le_one_of_mem_Icc (by rw [hz2re]; constructor <;> linarith)

/-- On the strip `0 ≤ Re s ≤ 2` and away from the real axis (`1 ≤ |Im s|`), the reciprocal
Gamma function is bounded by `exp (π |Im s|)`. -/
lemma inv_Gamma_le_exp_of_re_mem (s : ℂ) (hs0 : 0 ≤ s.re) (hs2 : s.re ≤ 2)
    (ht : 1 ≤ |s.im|) :
    ‖(Complex.Gamma s)⁻¹‖ ≤ Real.exp (Real.pi * |s.im|) := by
  have him0 : s.im ≠ 0 := by
    intro h; rw [h, abs_zero] at ht; linarith
  have hpi_ne : (↑Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  set S : ℂ := Complex.sin (↑Real.pi * s) with hS
  have hS_ne : S ≠ 0 := by
    rw [hS]
    intro hzero
    obtain ⟨k, hk⟩ := Complex.sin_eq_zero_iff.mp hzero
    rw [mul_comm ((k : ℤ) : ℂ) ((Real.pi : ℂ))] at hk
    have hs_eq : s = (k : ℂ) := mul_left_cancel₀ hpi_ne hk
    exact him0 (by rw [hs_eq]; simp)
  have hmain : Complex.Gamma s * (Complex.Gamma (1 - s) * S) = ↑Real.pi := by
    rw [← mul_assoc, Complex.Gamma_mul_Gamma_one_sub]
    exact div_mul_cancel₀ _ hS_ne
  have hGs : Complex.Gamma s ≠ 0 := by
    intro h0; rw [h0, zero_mul] at hmain; exact hpi_ne hmain.symm
  have key : (Complex.Gamma s)⁻¹ = Complex.Gamma (1 - s) * S / ↑Real.pi := by
    have h1 : Complex.Gamma s * (Complex.Gamma (1 - s) * S / ↑Real.pi) = 1 := by
      rw [← mul_div_assoc, hmain, div_self hpi_ne]
    calc (Complex.Gamma s)⁻¹ = (Complex.Gamma s)⁻¹ * 1 := (mul_one _).symm
      _ = (Complex.Gamma s)⁻¹ *
            (Complex.Gamma s * (Complex.Gamma (1 - s) * S / ↑Real.pi)) := by rw [h1]
      _ = Complex.Gamma (1 - s) * S / ↑Real.pi := by
            rw [← mul_assoc, inv_mul_cancel₀ hGs, one_mul]
  have hG1 : ‖Complex.Gamma (1 - s)‖ ≤ 1 := Gamma_one_sub_le_one s hs0 hs2 ht
  have hSb : ‖S‖ ≤ Real.exp (Real.pi * |s.im|) := by
    have h := norm_sin_le_exp_im ((↑Real.pi : ℂ) * s)
    rw [show ((↑Real.pi : ℂ) * s).im = Real.pi * s.im by simp] at h
    rwa [abs_mul, abs_of_pos Real.pi_pos] at h
  rw [key, norm_div, norm_mul, Complex.norm_of_nonneg Real.pi_pos.le]
  calc ‖Complex.Gamma (1 - s)‖ * ‖S‖ / Real.pi
      ≤ 1 * Real.exp (Real.pi * |s.im|) / Real.pi := by gcongr
    _ = Real.exp (Real.pi * |s.im|) / Real.pi := by ring
    _ ≤ Real.exp (Real.pi * |s.im|) := by
        rw [div_le_iff₀ Real.pi_pos]
        nlinarith [Real.exp_pos (Real.pi * |s.im|), Real.pi_gt_three]

/-- Iterated form of the recurrence `1/Γ(s) = s * 1/Γ(s+1)`. -/
lemma inv_Gamma_eq_prod_inv_Gamma_add (z : ℂ) (n : ℕ) :
    (Complex.Gamma z)⁻¹ = (∏ j ∈ Finset.range n, (z + j)) * (Complex.Gamma (z + n))⁻¹ := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [ih, Finset.prod_range_succ]
    rw [Complex.one_div_Gamma_eq_self_mul_one_div_Gamma_add_one (z + n)]
    rw [show ((z + (n:ℂ)) + 1) = z + ((n+1 : ℕ) : ℂ) by push_cast; ring]
    ring

/-- **Main bound.** For `0 ≤ u ≤ K` and any real `t`, the reciprocal Gamma function at
`u + i t` is at most `c * exp (C |t|)`. -/
theorem gammaVerticalLowerExp (K : ℝ) (hK : 0 ≤ K) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ (u t : ℝ), 0 ≤ u → u ≤ K →
      ‖(Complex.Gamma ((u : ℂ) + (t : ℂ) * Complex.I))⁻¹‖ ≤ c * Real.exp (C * |t|) := by
  set Y : Set ℂ := (fun p : ℝ × ℝ => (p.1 : ℂ) + (p.2 : ℂ) * Complex.I) ''
    (Set.Icc (0:ℝ) K ×ˢ Set.Icc (-1:ℝ) 1) with hY
  have hcomp : IsCompact Y := by
    rw [hY]
    exact (isCompact_Icc.prod isCompact_Icc).image
      ((Complex.continuous_ofReal.comp continuous_fst).add
        ((Complex.continuous_ofReal.comp continuous_snd).mul continuous_const))
  have hdiff : Continuous fun z : ℂ => ‖(Complex.Gamma z)⁻¹‖ :=
    continuous_norm.comp Complex.differentiable_one_div_Gamma.continuous
  obtain ⟨B, hB⟩ := hcomp.bddAbove_image hdiff.continuousOn
  have hB' : ∀ z ∈ Y, ‖(Complex.Gamma z)⁻¹‖ ≤ B :=
    fun z hz => (mem_upperBounds.mp hB) ‖(Complex.Gamma z)⁻¹‖ ⟨z, hz, rfl⟩
  refine ⟨max 1 B, Real.pi, lt_of_lt_of_le one_pos (le_max_left 1 B), Real.pi_pos, ?_⟩
  intro u t hu0 huK
  set s : ℂ := (u : ℂ) + (t : ℂ) * Complex.I with hs
  have hre : s.re = u := by simp [hs]
  have him : s.im = t := by simp [hs]
  by_cases ht : |t| ≤ 1
  · have htmem : t ∈ Set.Icc (-1:ℝ) 1 := by
      rw [Set.mem_Icc]
      exact ⟨by linarith [neg_abs_le t], by linarith [le_abs_self t]⟩
    have hmem : s ∈ Y := by
      rw [hY]
      exact ⟨(u, t), ⟨⟨hu0, huK⟩, htmem⟩, hs.symm⟩
    have h1 : ‖(Complex.Gamma s)⁻¹‖ ≤ B := hB' s hmem
    have h2 : B ≤ max 1 B := le_max_right 1 B
    have hexp : 1 ≤ Real.exp (Real.pi * |t|) := Real.one_le_exp (by positivity)
    have hmax0 : 0 ≤ max 1 B := le_trans zero_le_one (le_max_left 1 B)
    calc ‖(Complex.Gamma s)⁻¹‖ ≤ B := h1
      _ ≤ max 1 B := h2
      _ = max 1 B * 1 := (mul_one _).symm
      _ ≤ max 1 B * Real.exp (Real.pi * |t|) := mul_le_mul_of_nonneg_left hexp hmax0
  · rw [not_le] at ht
    by_cases hu2 : u ≤ 2
    · have hsm : ‖(Complex.Gamma s)⁻¹‖ ≤ Real.exp (Real.pi * |t|) := by
        have h := inv_Gamma_le_exp_of_re_mem s (by rw [hre]; exact hu0) (by rw [hre]; exact hu2)
          (by rw [him]; exact le_of_lt ht)
        rwa [him] at h
      exact hsm.trans (le_mul_of_one_le_left (Real.exp_pos _).le (le_max_left 1 B))
    · have hu2' : 2 < u := lt_of_not_ge hu2
      have hceil2 : 2 ≤ ⌈u⌉₊ := by
        have h1 : (2:ℝ) < (⌈u⌉₊ : ℝ) := lt_of_lt_of_le hu2' (Nat.le_ceil u)
        exact le_of_lt (Nat.cast_lt.mp h1)
      set m : ℕ := ⌈u⌉₊ - 2 with hm
      have hmcast : (m : ℝ) = (⌈u⌉₊ : ℝ) - 2 := by
        rw [hm]; exact Nat.cast_sub hceil2
      have hre' : (s - m).re = u - ((⌈u⌉₊ : ℝ) - 2) := by
        rw [Complex.sub_re, hre, Complex.natCast_re, hmcast]
      have him' : (s - m).im = t := by
        rw [Complex.sub_im, him, Complex.natCast_im, sub_zero]
      have hs0' : 0 ≤ (s - m).re := by
        have h1 := Nat.le_ceil u
        have h2 := Nat.ceil_lt_add_one hu0
        rw [hre']; linarith
      have hs2' : (s - m).re ≤ 2 := by
        have h1 := Nat.le_ceil u
        rw [hre']; linarith
      have ht' : 1 ≤ |(s - m).im| := by rw [him']; exact le_of_lt ht
      have hsm : ‖(Complex.Gamma (s - m))⁻¹‖ ≤ Real.exp (Real.pi * |t|) := by
        have h := inv_Gamma_le_exp_of_re_mem (s - m) hs0' hs2' ht'
        rwa [him'] at h
      set P : ℂ := ∏ j ∈ Finset.range m, ((s - m) + (j : ℂ)) with hP
      have hPnorm : 1 ≤ ‖P‖ := by
        rw [hP, norm_prod]
        refine Finset.one_le_prod₀ (fun j hj => ?_)
        have hz : ((s - m) + (j:ℂ)).im = t := by
          rw [Complex.add_im, Complex.sub_im, him, Complex.natCast_im, sub_zero,
            Complex.natCast_im, add_zero]
        have hle := Complex.abs_im_le_norm ((s - m) + (j:ℂ))
        rw [hz] at hle
        linarith [le_of_lt ht]
      have hPne : P ≠ 0 := by
        intro h0; rw [h0, norm_zero] at hPnorm; linarith
      have hkey : (Complex.Gamma s)⁻¹ = (Complex.Gamma (s - m))⁻¹ / P := by
        have hprod := inv_Gamma_eq_prod_inv_Gamma_add (s - m) m
        rw [show (s - m) + (m : ℂ) = s by ring] at hprod
        rw [eq_div_iff hPne, hP, mul_comm, ← hprod]
      calc ‖(Complex.Gamma s)⁻¹‖ = ‖(Complex.Gamma (s - m))⁻¹‖ / ‖P‖ := by rw [hkey, norm_div]
        _ ≤ ‖(Complex.Gamma (s - m))⁻¹‖ := by
            rw [div_le_iff₀ (by linarith : (0:ℝ) < ‖P‖)]
            exact le_mul_of_one_le_right (norm_nonneg _) hPnorm
        _ ≤ Real.exp (Real.pi * |t|) := hsm
        _ ≤ max 1 B * Real.exp (Real.pi * |t|) :=
            le_mul_of_one_le_left (Real.exp_pos _).le (le_max_left 1 B)

end Work.FIArea5.S16Hecke
