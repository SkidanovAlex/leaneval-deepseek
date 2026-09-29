import Mathlib
import Submission.Work.TMC14Core.Assembly

namespace Work.TMC14Core

/-- The Bloch matrix `blochMat p q lam θ k` is Hermitian whenever `θ` and `k` are real. -/
theorem blochMat_isHermitian (p : ℤ) (q : ℕ) (lam θ k : ℝ) :
    (blochMat p q lam θ k).IsHermitian := by
  have star_ite : ∀ (P : Prop) [Decidable P] (a b : ℂ),
      (starRingEnd ℂ) (if P then a else b)
        = if P then (starRingEnd ℂ) a else (starRingEnd ℂ) b := by
    intro P _ a b; by_cases h : P <;> simp [h]
  rw [Matrix.IsHermitian.ext_iff]
  intro i j
  simp only [blochMat, Complex.star_def]
  simp only [map_add, star_ite, Complex.conj_ofReal, ← Complex.exp_conj, Complex.conj_I, map_one,
    map_zero, map_mul, map_neg, map_ofNat]
  rw [show (2 : ℂ) * ↑Real.pi * -Complex.I * ↑k = -(2 * ↑Real.pi * Complex.I * ↑k) from by ring]
  simp only [neg_neg]
  rw [show (if ↑j = q - 1 ∧ ↑i = 0 then Complex.exp (-(2 * ↑Real.pi * Complex.I * ↑k)) else 0)
        = (if ↑i = 0 ∧ ↑j = q - 1 then Complex.exp (-(2 * ↑Real.pi * Complex.I * ↑k)) else 0) from by
      simp only [and_comm]]
  rw [show (if ↑j = 0 ∧ ↑i = q - 1 then Complex.exp (2 * ↑Real.pi * Complex.I * ↑k) else 0)
        = (if ↑i = q - 1 ∧ ↑j = 0 then Complex.exp (2 * ↑Real.pi * Complex.I * ↑k) else 0) from by
      simp only [and_comm]]
  rw [show (if j = i then (↑(2 * lam * Real.cos (2 * Real.pi * (θ + ↑↑j * ↑p / ↑q))) : ℂ) else 0)
        = (if i = j then (↑(2 * lam * Real.cos (2 * Real.pi * (θ + ↑↑i * ↑p / ↑q))) : ℂ) else 0) from by
      by_cases h : i = j
      · subst h; simp
      · have hji : ¬ (j = i) := fun h' => h h'.symm
        simp [h, hji]]
  ring_nf

/-- The oscillatory coefficient of Chambers' formula is real. -/
theorem chamCoef_star (p : ℤ) (q : ℕ) (lam : ℝ) :
    star (chamCoef p q lam) = chamCoef p q lam := by
  simp [chamCoef]

/-- The complex norm of the oscillatory coefficient is `2 λ^q`. -/
theorem chamCoef_norm' (p : ℤ) (q : ℕ) (lam : ℝ) (hlam : 0 < lam) :
    ‖chamCoef p q lam‖ = 2 * lam ^ q := by
  rw [chamCoef, norm_mul, norm_mul, norm_pow, norm_zpow, norm_neg]
  rw [show ‖(2 : ℂ)‖ = 2 by norm_num, show ‖(-1 : ℂ)‖ = 1 by norm_num]
  simp only [one_zpow, mul_one]
  rw [show ‖(↑lam : ℂ)‖ = |lam| by simp, abs_of_pos hlam]

/-- A complex number fixed by `star` is the coercion of its real part. -/
theorem eq_ofReal_re_of_star (z : ℂ) (h : (starRingEnd ℂ) z = z) :
    z = ((z.re : ℝ) : ℂ) := by
  rw [← Complex.re_add_im z]
  have him : z.im = 0 := by
    have := congrArg Complex.im h
    rw [Complex.conj_im] at this
    linarith
  rw [him]; simp

theorem discRootsReal (p : ℤ) (q : ℕ) (lam : ℝ) (hpq : Nat.Coprime p.natAbs q) (hq : 1 ≤ q)
    (hlam : 0 < lam) (c : ℝ) (hc : |c| ≤ 2 + 2*lam^q) {z : ℂ}
    (hz : (disc p q lam).eval z = (c : ℂ)) : ∃ x : ℝ, z = (x : ℂ) := by
  -- ### Step 1: a real number `s` with `|s| ≤ 2` and `|s - c| ≤ 2 λ^q`.
  obtain ⟨s, hs2, hsc⟩ : ∃ s : ℝ, |s| ≤ 2 ∧ |s - c| ≤ 2 * lam ^ q := by
    refine ⟨min 2 (max (-2) c), ?_, ?_⟩
    · rw [abs_le]
      exact ⟨le_min (by norm_num) (le_max_left _ _), min_le_left _ _⟩
    · have hle : 0 < 2 * lam ^ q := by positivity
      rcases lt_or_ge c 2 with hc2 | hc2
      · rcases lt_or_ge c (-2) with hc3 | hc3
        · have hs : min 2 (max (-2) c) = -2 := by
            rw [min_eq_right (max_le (by norm_num) (le_of_lt hc2)), max_eq_left (le_of_lt hc3)]
          rw [hs, abs_of_nonneg (by linarith : (0:ℝ) ≤ -2 - c)]
          rw [abs_of_neg (by linarith : c < 0)] at hc
          linarith
        · have hs : min 2 (max (-2) c) = c := by
            rw [max_eq_right hc3, min_eq_right (le_of_lt hc2)]
          rw [hs, sub_self, abs_zero]; linarith
      · have hs : min 2 (max (-2) c) = 2 := by
          rw [max_eq_right (by linarith : (-2:ℝ) ≤ c), min_eq_left hc2]
        rw [hs, abs_of_nonpos (by linarith : 2 - c ≤ 0)]
        rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ c)] at hc
        linarith
  -- ### Step 2: a phase `k` with `2 cos (2πk) = s`.
  obtain ⟨k, hk⟩ : ∃ k : ℝ, 2 * Real.cos (2 * Real.pi * k) = s := by
    have hs' : s / 2 ∈ Set.range Real.cos := by
      rw [Real.range_cos, Set.mem_Icc]
      exact abs_le.mp (by rw [abs_div, abs_two]; linarith [abs_le.mp hs2])
    obtain ⟨x, hx⟩ := hs'
    refine ⟨x / (2 * Real.pi), ?_⟩
    have harg : 2 * Real.pi * (x / (2 * Real.pi)) = x := by
      field_simp
    rw [harg, hx]; ring
  -- ### Step 3: a phase `θ` cancelling `chamCoef`.
  set γ := (chamCoef p q lam).re with hγdef
  have hcr : chamCoef p q lam = ((γ : ℝ) : ℂ) := by
    rw [hγdef]
    exact eq_ofReal_re_of_star _ (by simpa [Complex.star_def] using chamCoef_star p q lam)
  have habs : |γ| = 2 * lam ^ q := by
    have h1 : ‖chamCoef p q lam‖ = |γ| := by rw [hcr]; simp
    rw [← h1, chamCoef_norm' p q lam hlam]
  obtain ⟨θ, hθ⟩ : ∃ θ : ℝ,
      chamCoef p q lam * ((Real.cos (2 * Real.pi * (q : ℝ) * θ) : ℝ) : ℂ) = ((s - c : ℝ) : ℂ) := by
    have hγne : γ ≠ 0 := by
      intro h; rw [h, abs_zero] at habs; linarith [pow_pos hlam q]
    have ht1 : |(s - c) / γ| ≤ 1 := by
      rw [abs_div, div_le_one (by rw [habs]; positivity), habs]
      exact hsc
    have htmem : (s - c) / γ ∈ Set.range Real.cos := by
      rw [Real.range_cos, Set.mem_Icc]
      exact abs_le.mp ht1
    obtain ⟨x, hx⟩ := htmem
    have hqne : ((q : ℝ)) ≠ 0 := by exact_mod_cast (Nat.one_le_iff_ne_zero.mp hq)
    refine ⟨x / (2 * Real.pi * (q : ℝ)), ?_⟩
    have harg : 2 * Real.pi * (q : ℝ) * (x / (2 * Real.pi * (q : ℝ))) = x := by
      field_simp
    rw [harg, hx, hcr, ← Complex.ofReal_mul, Complex.ofReal_inj]
    field_simp
  -- ### Step 4: the Bloch determinant vanishes at `z`.
  set M := blochMat p q lam θ k with hMdef
  have hdet : (z • (1 : Matrix (Fin q) (Fin q) ℂ) - M).det = 0 := by
    rw [blochMat_chambers p q lam θ k z hpq hq, hz, hθ]
    have h2 : (2 : ℂ) * ((Real.cos (2 * Real.pi * k) : ℝ) : ℂ)
        = ((2 * Real.cos (2 * Real.pi * k) : ℝ) : ℂ) := by push_cast; ring
    rw [h2, hk, ← Complex.ofReal_add, ← Complex.ofReal_sub]
    simp only [Complex.ofReal_eq_zero]
    ring
  -- ### Step 5: `z` is an eigenvalue of the Hermitian matrix `M`, hence real.
  have hM := blochMat_isHermitian p q lam θ k
  have hscalar : Matrix.scalar (Fin q) z = z • (1 : Matrix (Fin q) (Fin q) ℂ) := by
    ext i j
    rw [Matrix.scalar_apply, Matrix.diagonal_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
    by_cases h : i = j <;> simp [h]
  have hchar : M.charpoly.eval z = 0 := by
    rw [Matrix.eval_charpoly, hscalar]
    exact hdet
  rw [hM.charpoly_eq] at hchar
  simp only [Polynomial.eval_prod, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C,
    Finset.prod_eq_zero_iff, Finset.mem_univ, true_and] at hchar
  obtain ⟨i, hi⟩ := hchar
  exact ⟨hM.eigenvalues i, sub_eq_zero.mp hi⟩

end Work.TMC14Core
