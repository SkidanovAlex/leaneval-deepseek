import Mathlib
import Submission.Work.EKLContract.Interfaces

/-!
# `Work.EKLC6Core.aeBall_path` — paths in `SL₃(ℝ)` inside entrywise balls

Every `v ∈ SL₃(ℝ)` that is within `s/100` of the identity (entrywise sup-distance) can be joined
to the identity by a continuous path staying within `s` of the identity (`0 < s ≤ 1`).

## Construction

For `v ∈ SL₃(ℝ)` put `N = v - 1`, `M θ = 1 + θ N` and `d θ = det (M θ)`.  Then

    γ θ = (d θ)^{-1/3} • M θ

has determinant `(d θ)^{-1}· d θ = 1` (so it is in `SL₃(ℝ)`), is continuous, starts at `1`,
ends at `v = M 1` (because `d 1 = det v = 1`), and its entries stay within a universal multiple
of the deviation of `v` from the identity (the determinant of a matrix within `ε` of `1` is
within `32 ε` of `1`, and `x ↦ x^{1/3}` is Lipschitz with constant `1` on `[0,∞)`).
-/

open Matrix

noncomputable section

namespace Work.EKLC6Core

open Work.EKLContract

/-! ## Elementary estimates -/

/-- If `|a - 1| ≤ ε` and `|b - 1| ≤ ε` then `|a * b - 1| ≤ 3 ε` (for `ε ≤ 1`). -/
theorem abs_mul_sub_one_le {a b ε : ℝ} (ha : |a - 1| ≤ ε) (hb : |b - 1| ≤ ε)
    (hε : 0 < ε) (hε1 : ε ≤ 1) : |a * b - 1| ≤ 3 * ε := by
  have h1 : a * b - 1 = (a - 1) + (b - 1) + (a - 1) * (b - 1) := by ring
  have h2 : |(a - 1) * (b - 1)| ≤ ε * ε := by
    rw [abs_mul]
    exact mul_le_mul ha hb (abs_nonneg _) hε.le
  rw [h1]
  refine abs_le.mpr ⟨?_, ?_⟩ <;> nlinarith [abs_le.mp ha, abs_le.mp hb, abs_le.mp h2, hε, hε1]

/-- If `|a - 1| ≤ ε`, `|b - 1| ≤ ε`, `|c - 1| ≤ ε` then `|a * b * c - 1| ≤ 7 ε` (for `ε ≤ 1`). -/
theorem abs_mul3_sub_one_le {a b c ε : ℝ} (ha : |a - 1| ≤ ε) (hb : |b - 1| ≤ ε)
    (hc : |c - 1| ≤ ε) (hε : 0 < ε) (hε1 : ε ≤ 1) : |a * b * c - 1| ≤ 7 * ε := by
  have h1 : a * b * c - 1 = (a * b - 1) * c + (c - 1) := by ring
  have hab : |a * b - 1| ≤ 3 * ε := abs_mul_sub_one_le ha hb hε hε1
  have hc2 : |c| ≤ 1 + ε := by
    have h := abs_add_le (c - 1) (1 : ℝ)
    rw [sub_add_cancel, abs_one] at h
    linarith [hc]
  have h2 : |(a * b - 1) * c| ≤ (3 * ε) * (1 + ε) := by
    rw [abs_mul]
    exact mul_le_mul hab hc2 (abs_nonneg _) (by positivity)
  rw [h1]
  refine abs_le.mpr ⟨?_, ?_⟩ <;> nlinarith [abs_le.mp h2, abs_le.mp hc, hε, hε1]

/-- Triangle inequality for six terms. -/
theorem abs_six_le (a b c d e f : ℝ) :
    |a - b - c + d + e - f| ≤ |a| + |b| + |c| + |d| + |e| + |f| := by
  have h1 : |a - b - c + d + e - f| ≤ |a - b - c + d + e| + |f| := by
    simpa using abs_sub_le (a - b - c + d + e) 0 f
  have h2 : |a - b - c + d + e| ≤ |a - b - c + d| + |e| := abs_add_le _ _
  have h3 : |a - b - c + d| ≤ |a - b - c| + |d| := abs_add_le _ _
  have h4 : |a - b - c| ≤ |a - b| + |c| := by
    simpa using abs_sub_le (a - b) 0 c
  have h5 : |a - b| ≤ |a| + |b| := by
    simpa using abs_sub_le a 0 b
  linarith

/-- The determinant of a `3 × 3` matrix within `ε` of the identity is within `32 ε` of `1`. -/
theorem abs_det_sub_one_le {B : Matrix (Fin 3) (Fin 3) ℝ} {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hB : ∀ i j, |B i j - (1 : Matrix (Fin 3) (Fin 3) ℝ) i j| ≤ ε) :
    |B.det - 1| ≤ 32 * ε := by
  have hε0 : (0 : ℝ) ≤ ε := hε.le
  have hd : ∀ i : Fin 3, |B i i - 1| ≤ ε := fun i => by simpa using hB i i
  have ho : ∀ i j : Fin 3, i ≠ j → |B i j| ≤ ε := by
    intro i j hij
    have := hB i j
    simpa [Matrix.one_apply, hij] using this
  have hdiag : ∀ i : Fin 3, |B i i| ≤ 1 + ε := by
    intro i
    have h := abs_add_le (B i i - 1) (1 : ℝ)
    rw [sub_add_cancel, abs_one] at h
    linarith [hd i]
  have h4 : (1 + ε) * ε * ε ≤ 4 * ε := by
    have hh : (0 : ℝ) ≤ ε * (1 - ε) * (3 + ε) := by positivity
    nlinarith [hh]
  have key_off : ∀ x y z : ℝ, |x| ≤ 1 + ε → |y| ≤ ε → |z| ≤ ε → |x * y * z| ≤ 4 * ε := by
    intro x y z hx hy hz
    have h1 : |x * y * z| ≤ (1 + ε) * ε * ε := by
      rw [abs_mul, abs_mul]
      exact mul_le_mul (mul_le_mul hx hy (abs_nonneg _) (by positivity)) hz (abs_nonneg _)
        (by positivity)
    linarith [h1, h4]
  have key1 : |B 0 0 * B 1 1 * B 2 2 - 1| ≤ 7 * ε :=
    abs_mul3_sub_one_le (hd 0) (hd 1) (hd 2) hε hε1
  have key2 : |B 0 0 * B 1 2 * B 2 1| ≤ 4 * ε :=
    key_off _ _ _ (hdiag 0) (ho 1 2 (by decide)) (ho 2 1 (by decide))
  have key3 : |B 0 1 * B 1 0 * B 2 2| ≤ 4 * ε := by
    rw [show B 0 1 * B 1 0 * B 2 2 = B 2 2 * B 0 1 * B 1 0 by ring]
    exact key_off _ _ _ (hdiag 2) (ho 0 1 (by decide)) (ho 1 0 (by decide))
  have key4 : |B 0 1 * B 1 2 * B 2 0| ≤ 4 * ε :=
    key_off _ _ _ (by linarith [ho 0 1 (by decide)] : |B 0 1| ≤ 1 + ε)
      (ho 1 2 (by decide)) (ho 2 0 (by decide))
  have key5 : |B 0 2 * B 1 0 * B 2 1| ≤ 4 * ε :=
    key_off _ _ _ (by linarith [ho 0 2 (by decide)] : |B 0 2| ≤ 1 + ε)
      (ho 1 0 (by decide)) (ho 2 1 (by decide))
  have key6 : |B 0 2 * B 1 1 * B 2 0| ≤ 4 * ε := by
    rw [show B 0 2 * B 1 1 * B 2 0 = B 1 1 * B 0 2 * B 2 0 by ring]
    exact key_off _ _ _ (hdiag 1) (ho 0 2 (by decide)) (ho 2 0 (by decide))
  have hdecomp : B.det - 1 = (B 0 0 * B 1 1 * B 2 2 - 1) - B 0 0 * B 1 2 * B 2 1
      - B 0 1 * B 1 0 * B 2 2 + B 0 1 * B 1 2 * B 2 0 + B 0 2 * B 1 0 * B 2 1
      - B 0 2 * B 1 1 * B 2 0 := by
    rw [Matrix.det_fin_three]; ring
  rw [hdecomp]
  have htri := abs_six_le (B 0 0 * B 1 1 * B 2 2 - 1) (B 0 0 * B 1 2 * B 2 1)
    (B 0 1 * B 1 0 * B 2 2) (B 0 1 * B 1 2 * B 2 0) (B 0 2 * B 1 0 * B 2 1)
    (B 0 2 * B 1 1 * B 2 0)
  linarith [htri, key1, key2, key3, key4, key5, key6, hε]

/-- For `d ≥ 0`, `x ↦ x^{1/3}` does not increase the distance to `1`. -/
theorem abs_rpow_third_sub_one_le (d : ℝ) (hd : 0 ≤ d) :
    |d ^ (1 / 3 : ℝ) - 1| ≤ |d - 1| := by
  set t := d ^ (1 / 3 : ℝ) with ht
  have h3 : t ^ 3 = d := by
    rw [ht, show (1 / 3 : ℝ) = ((3 : ℕ)⁻¹ : ℝ) by norm_num]
    exact Real.rpow_inv_natCast_pow hd (by norm_num)
  have ht0 : 0 ≤ t := by rw [ht]; exact Real.rpow_nonneg hd _
  have hkey : (t - 1) * (t ^ 2 + t + 1) = d - 1 := by rw [← h3]; ring
  have hden : (1 : ℝ) ≤ t ^ 2 + t + 1 := by nlinarith [sq_nonneg t, ht0]
  have hdenpos : (0 : ℝ) < t ^ 2 + t + 1 := by linarith
  have hmain : |t - 1| * (t ^ 2 + t + 1) = |d - 1| := by
    rw [← abs_of_nonneg (by linarith : (0 : ℝ) ≤ t ^ 2 + t + 1), ← abs_mul, hkey]
  calc |t - 1| = |t - 1| * 1 := by ring
    _ ≤ |t - 1| * (t ^ 2 + t + 1) := mul_le_mul_of_nonneg_left hden (abs_nonneg _)
    _ = |d - 1| := hmain

/-! ## The interpolating path -/

/-- The linear interpolation between `1` and `v` in the space of matrices. -/
def pathM (v : SL3) (θ : ℝ) : Matrix (Fin 3) (Fin 3) ℝ := 1 + θ • (toMat v - 1)

/-- The determinant of the interpolation. -/
def pathD (v : SL3) (θ : ℝ) : ℝ := (pathM v θ).det

/-- The normalising scalar `(det)^{1/3}`. -/
def pathC (v : SL3) (θ : ℝ) : ℝ := (pathD v θ) ^ (-(1 / 3) : ℝ)

/-- The clamped coordinate, so that the path is defined on all of `ℝ`. -/
def clamp (θ : ℝ) : ℝ := max 0 (min 1 θ)

theorem clamp_mem (θ : ℝ) : clamp θ ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨le_max_left _ _, max_le zero_le_one (min_le_left _ _)⟩

theorem clamp_abs (θ : ℝ) : |clamp θ| ≤ 1 := by
  rw [abs_of_nonneg (clamp_mem θ).1]
  exact (clamp_mem θ).2

theorem clamp_of_mem {θ : ℝ} (hθ : θ ∈ Set.Icc (0 : ℝ) 1) : clamp θ = θ := by
  rw [clamp, min_eq_right hθ.2, max_eq_right hθ.1]

theorem pathM_sub_one_eq (v : SL3) (θ : ℝ) (i j : Fin 3) :
    pathM v θ i j - (1 : Matrix (Fin 3) (Fin 3) ℝ) i j
      = θ * (toMat v i j - (1 : Matrix (Fin 3) (Fin 3) ℝ) i j) := by
  rw [pathM]
  simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply]
  ring

theorem pathM_entry_le {s : ℝ} (hs : 0 < s) {v : SL3} (hv : v ∈ V (s / 100)) (θ : ℝ)
    (hθ : |θ| ≤ 1) (i j : Fin 3) :
    |pathM v θ i j - (1 : Matrix (Fin 3) (Fin 3) ℝ) i j| ≤ s / 100 := by
  rw [pathM_sub_one_eq, abs_mul]
  have hvε : |toMat v i j - (1 : Matrix (Fin 3) (Fin 3) ℝ) i j| ≤ s / 100 :=
    le_of_lt (hv i j)
  calc |θ| * |toMat v i j - (1 : Matrix (Fin 3) (Fin 3) ℝ) i j|
      ≤ 1 * (s / 100) := mul_le_mul hθ hvε (abs_nonneg _) (by norm_num)
    _ = s / 100 := by ring

theorem pathD_bound {s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1) {v : SL3} (hv : v ∈ V (s / 100))
    (θ : ℝ) (hθ : |θ| ≤ 1) : |pathD v θ - 1| ≤ 32 * (s / 100) := by
  rw [pathD]
  refine abs_det_sub_one_le (by linarith) (by linarith) fun i j => ?_
  exact pathM_entry_le hs hv θ hθ i j

theorem pathD_pos {s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1) {v : SL3} (hv : v ∈ V (s / 100))
    (θ : ℝ) (hθ : |θ| ≤ 1) : 0 < pathD v θ := by
  have h := abs_le.mp (pathD_bound hs hs1 hv θ hθ)
  nlinarith [h.1, h.2]

theorem pathC_det {s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1) {v : SL3} (hv : v ∈ V (s / 100))
    (θ : ℝ) (hθ : |θ| ≤ 1) : (pathC v θ • pathM v θ).det = 1 := by
  have hdpos : 0 < pathD v θ := pathD_pos hs hs1 hv θ hθ
  rw [Matrix.det_smul, Fintype.card_fin]
  have hcu : pathC v θ = (pathD v θ ^ (1 / 3 : ℝ))⁻¹ := by
    rw [pathC, show (-(1 / 3 : ℝ)) = -((1 / 3 : ℝ)) by norm_num, Real.rpow_neg hdpos.le]
  have h13 : (pathD v θ ^ (1 / 3 : ℝ)) ^ 3 = pathD v θ := by
    rw [show (1 / 3 : ℝ) = ((3 : ℕ)⁻¹ : ℝ) by norm_num]
    exact Real.rpow_inv_natCast_pow hdpos.le (by norm_num)
  have hc3 : pathC v θ ^ 3 = (pathD v θ)⁻¹ := by
    rw [hcu, inv_pow, h13]
  rw [hc3, pathD]
  exact inv_mul_cancel₀ hdpos.ne'

theorem pathC_entry_lt {s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1) {v : SL3} (hv : v ∈ V (s / 100))
    (θ : ℝ) (hθ : |θ| ≤ 1) (i j : Fin 3) :
    |(pathC v θ • pathM v θ) i j - (1 : Matrix (Fin 3) (Fin 3) ℝ) i j| < s := by
  have hdpos : 0 < pathD v θ := pathD_pos hs hs1 hv θ hθ
  have hdbd : |pathD v θ - 1| ≤ 32 * (s / 100) := pathD_bound hs hs1 hv θ hθ
  have hεpos : 0 < s / 100 := by linarith
  have hεle : s / 100 ≤ 1 := by linarith
  have hd1_2 : (1 : ℝ) / 2 ≤ pathD v θ := by
    have h := (abs_le.mp hdbd).1
    linarith
  -- the cube root of the determinant
  set t := pathD v θ ^ (1 / 3 : ℝ) with htdef
  have htpos : 0 < t := Real.rpow_pos_of_pos hdpos _
  have htge : (1 : ℝ) / 2 ≤ t := by
    have h8 : ((1 : ℝ) / 2) ^ 3 ≤ pathD v θ := by norm_num; linarith
    have h := Real.rpow_le_rpow (by positivity : (0 : ℝ) ≤ ((1 : ℝ) / 2) ^ 3) h8
      (by norm_num : (0 : ℝ) ≤ (1 / 3 : ℝ))
    rwa [show (((1 : ℝ) / 2) ^ 3) ^ ((1 / 3 : ℝ)) = 1 / 2 by
      rw [show (1 / 3 : ℝ) = ((3 : ℕ)⁻¹ : ℝ) by norm_num]
      exact Real.pow_rpow_inv_natCast (by norm_num) (by norm_num)] at h
  have htbd : |t - 1| ≤ 32 * (s / 100) := by
    rw [htdef]
    exact le_trans (abs_rpow_third_sub_one_le _ hdpos.le) hdbd
  -- the normalising scalar
  have hcu : pathC v θ = t⁻¹ := by
    rw [pathC, htdef, show (-(1 / 3 : ℝ)) = -((1 / 3 : ℝ)) by norm_num, Real.rpow_neg hdpos.le]
  have hcpos : 0 < pathC v θ := by rw [hcu]; exact inv_pos.mpr htpos
  have hcabs : |pathC v θ| ≤ 2 := by
    rw [abs_of_pos hcpos, hcu, inv_eq_one_div, div_le_iff₀ htpos]
    linarith [htge]
  have hc1 : |pathC v θ - 1| ≤ 64 * (s / 100) := by
    have hcs : pathC v θ - 1 = (1 - t) / t := by rw [hcu]; field_simp
    rw [hcs, abs_div, abs_of_pos htpos]
    have h1t : |1 - t| ≤ 32 * (s / 100) := by rwa [abs_sub_comm] at htbd
    calc |1 - t| / t ≤ |1 - t| / (1 / 2) := by
          exact div_le_div_of_nonneg_left (abs_nonneg _) (by norm_num) htge
      _ = 2 * |1 - t| := by ring
      _ ≤ 2 * (32 * (s / 100)) := by linarith
      _ = 64 * (s / 100) := by ring
  have hM : |pathM v θ i j - (1 : Matrix (Fin 3) (Fin 3) ℝ) i j| ≤ s / 100 :=
    pathM_entry_le hs hv θ hθ i j
  have hsplit : (pathC v θ • pathM v θ) i j - (1 : Matrix (Fin 3) (Fin 3) ℝ) i j
      = pathC v θ * (pathM v θ i j - (1 : Matrix (Fin 3) (Fin 3) ℝ) i j)
        + (pathC v θ - 1) * (1 : Matrix (Fin 3) (Fin 3) ℝ) i j := by
    rw [Matrix.smul_apply]
    ring
  rw [hsplit]
  have hb1 : |pathC v θ * (pathM v θ i j - (1 : Matrix (Fin 3) (Fin 3) ℝ) i j)|
      ≤ 2 * (s / 100) := by
    rw [abs_mul]
    exact mul_le_mul hcabs hM (abs_nonneg _) (by positivity)
  have hb2 : |(pathC v θ - 1) * (1 : Matrix (Fin 3) (Fin 3) ℝ) i j| ≤ 64 * (s / 100) := by
    rw [abs_mul]
    have hone : |(1 : Matrix (Fin 3) (Fin 3) ℝ) i j| ≤ 1 := by
      rw [Matrix.one_apply]
      split_ifs <;> simp
    calc |pathC v θ - 1| * |(1 : Matrix (Fin 3) (Fin 3) ℝ) i j|
        ≤ (64 * (s / 100)) * 1 := mul_le_mul hc1 hone (abs_nonneg _) (by positivity)
      _ = 64 * (s / 100) := by ring
  have htri := abs_add_le (pathC v θ * (pathM v θ i j - (1 : Matrix (Fin 3) (Fin 3) ℝ) i j))
    ((pathC v θ - 1) * (1 : Matrix (Fin 3) (Fin 3) ℝ) i j)
  linarith [htri, hb1, hb2, hs]

theorem aeBall_path {s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1) {v : SL3} (hv : v ∈ V (s / 100)) :
    ∃ γ : ℝ → SL3, ContinuousOn γ (Set.Icc (0 : ℝ) 1) ∧ γ 0 = 1 ∧ γ 1 = v ∧
      ∀ θ ∈ Set.Icc (0 : ℝ) 1, γ θ ∈ V s := by
  have hdet : ∀ θ : ℝ, (pathC v (clamp θ) • pathM v (clamp θ)).det = 1 :=
    fun θ => pathC_det hs hs1 hv (clamp θ) (clamp_abs θ)
  have hMcont : Continuous fun θ : ℝ => pathM v θ := by
    refine continuous_pi fun i => continuous_pi fun j => ?_
    show Continuous fun θ : ℝ => pathM v θ i j
    simp only [pathM, Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply]
    fun_prop
  have hDcont : Continuous fun θ : ℝ => pathD v θ := by
    have h : (fun θ : ℝ => pathD v θ) = fun θ => (pathM v θ).det := by
      funext θ; rw [pathD]
    rw [h]
    exact hMcont.matrix_det
  have hCcont : ContinuousOn (fun θ : ℝ => pathC v θ) (Set.Icc (0 : ℝ) 1) := by
    exact ContinuousOn.rpow_const hDcont.continuousOn (p := (-(1 / 3) : ℝ)) fun θ hθ =>
      Or.inl (ne_of_gt (pathD_pos hs hs1 hv θ (by rw [abs_of_nonneg hθ.1]; exact hθ.2)))
  have hvec : ContinuousOn (fun θ : ℝ => pathC v θ • pathM v θ) (Set.Icc (0 : ℝ) 1) :=
    ContinuousOn.smul hCcont hMcont.continuousOn
  have hsl3 : ContinuousOn (fun θ : ℝ => (⟨pathC v (clamp θ) • pathM v (clamp θ), hdet θ⟩ : SL3))
      (Set.Icc (0 : ℝ) 1) := by
    change ContinuousOn (fun θ : ℝ => (⟨pathC v (clamp θ) • pathM v (clamp θ), hdet θ⟩ :
      {A : Matrix (Fin 3) (Fin 3) ℝ // A.det = 1})) (Set.Icc (0 : ℝ) 1)
    rw [continuousOn_iff_continuous_domRestrict]
    have hf : Continuous (Set.domRestrict (Set.Icc (0 : ℝ) 1)
        (fun θ : ℝ => pathC v (clamp θ) • pathM v (clamp θ))) := by
      refine hvec.domRestrict.congr fun θ => ?_
      show pathC v (θ : ℝ) • pathM v (θ : ℝ) = pathC v (clamp (θ : ℝ)) • pathM v (clamp (θ : ℝ))
      rw [clamp_of_mem θ.2]
    exact hf.subtype_mk fun θ => hdet (θ : ℝ)
  refine ⟨fun θ => (⟨pathC v (clamp θ) • pathM v (clamp θ), hdet θ⟩ : SL3), hsl3, ?_, ?_, ?_⟩
  · have h0 : clamp (0 : ℝ) = 0 := clamp_of_mem (by norm_num)
    have hM0 : pathM v 0 = (1 : Matrix (Fin 3) (Fin 3) ℝ) := by
      rw [pathM]; simp
    have hC0 : pathC v 0 = 1 := by
      rw [pathC, pathD, hM0, Matrix.det_one, Real.one_rpow]
    refine Subtype.ext ?_
    show pathC v (clamp 0) • pathM v (clamp 0) = (1 : Matrix (Fin 3) (Fin 3) ℝ)
    rw [h0, hC0, hM0]
    simp
  · have h1 : clamp (1 : ℝ) = 1 := clamp_of_mem (by norm_num)
    have hM1 : pathM v 1 = toMat v := by
      rw [pathM]; simp
    have hC1 : pathC v 1 = 1 := by
      rw [pathC, pathD, hM1, v.2, Real.one_rpow]
    refine Subtype.ext ?_
    show pathC v (clamp 1) • pathM v (clamp 1) = toMat v
    rw [h1, hC1, hM1]
    simp
  · intro θ hθ
    have h := pathC_entry_lt hs hs1 hv θ (by rw [abs_of_nonneg hθ.1]; exact hθ.2)
    have hclamp : clamp θ = θ := clamp_of_mem hθ
    intro i j
    simpa [hclamp] using h i j

end Work.EKLC6Core
