import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS_RegExport.RXR5L.ProdAux

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open Set Filter MeasureTheory

namespace Work.FTS_RegExport.RXR5L

open Work.FTS.Galerkin (Fn Fam slice)

set_option autoImplicit false

/-! ## §6 The `θ`-modulus of a product slot -/

/-- `x·d^{α−1} ≤ x^α` for `0 < x ≤ d` and `α ≤ 1`. -/
theorem Paux_mul_rpow_sub_one_le {x d α : ℝ} (hx : 0 < x) (hxd : x ≤ d) (hα : α ≤ 1) :
    x * d ^ (α - 1) ≤ x ^ α := by
  have hd0 : 0 < d := lt_of_lt_of_le hx hxd
  have h2 : d ^ (α - 1) ≤ x ^ (α - 1) :=
    (Real.antitoneOn_rpow_Ioi_of_exponent_nonpos (by linarith : α - 1 ≤ 0)) hx hd0 hxd
  have h3 : x * x ^ (α - 1) = x ^ α := by
    have h := Real.rpow_add hx 1 (α - 1)
    rw [Real.rpow_one] at h
    rw [← h]
    congr 1
    ring
  calc x * d ^ (α - 1) ≤ x * x ^ (α - 1) := mul_le_mul_of_nonneg_left h2 hx.le
    _ = x ^ α := h3

/-- The key one-variable inequality of the `θ`-case. -/
theorem Paux_min_mul_rpow {c B d x α : ℝ} (hc : 0 ≤ c) (hB : 0 ≤ B) (hd : 0 < d)
    (hx : 0 ≤ x) (hα0 : 0 < α) (hα1 : α ≤ 1) :
    min (2 * c) (c * (π / (4 * d)) * x) * (B * d ^ α) ≤ 2 * c * B * x ^ α := by
  have hdα : 0 ≤ d ^ α := Real.rpow_nonneg hd.le α
  have hxα : 0 ≤ x ^ α := Real.rpow_nonneg hx α
  rcases le_total x d with h | h
  · refine le_trans (mul_le_mul_of_nonneg_right (min_le_right _ _)
      (mul_nonneg hB hdα)) ?_
    have h2 : x * d ^ (α - 1) ≤ x ^ α := by
      rcases eq_or_lt_of_le hx with h0 | h0
      · rw [← h0, zero_mul, Real.zero_rpow hα0.ne']
      · exact Paux_mul_rpow_sub_one_le h0 h hα1
    have h3 : c * (π / (4 * d)) * x * (B * d ^ α)
        = c * B * (π / 4) * (x * d ^ (α - 1)) := by
      have hdiv : d ^ α / d = d ^ (α - 1) := by
        have h := Real.rpow_sub hd α 1
        rw [Real.rpow_one] at h
        exact h.symm
      rw [show c * (π / (4 * d)) * x * (B * d ^ α)
          = c * B * (π / 4) * (x * (d ^ α / d)) from by ring]
      rw [hdiv]
    rw [h3]
    have h4 : 0 ≤ c * B * (π / 4) := by positivity
    have h5 := mul_le_mul_of_nonneg_left h2 h4
    have h6 : c * B * (π / 4) * x ^ α ≤ 2 * c * B * x ^ α := by
      have h7 : 0 ≤ c * B * x ^ α := by positivity
      nlinarith [Real.pi_lt_four, h7]
    linarith
  · refine le_trans (mul_le_mul_of_nonneg_right (min_le_left _ _)
      (mul_nonneg hB hdα)) ?_
    have h2 : d ^ α ≤ x ^ α := Real.rpow_le_rpow hd.le h hα0.le
    have h5 : B * d ^ α ≤ B * x ^ α := mul_le_mul_of_nonneg_left h2 hB
    have h4 : 2 * c * (B * d ^ α) ≤ 2 * c * B * x ^ α := by nlinarith [h5, hc]
    linarith

/-- `|Q z θ τ| ≤ A·min z 1` for `z ≥ 0` and `θ` in the open interval. -/
theorem abs_Q_le_min {α S A B : ℝ} {Q R : ℝ → ℝ → ℝ → ℝ} (h : ProdData α S A B Q R)
    {z θ τ : ℝ} (hz : 0 ≤ z) (hθ : θ ∈ Set.Ioo 0 (π / 2)) (hτ : τ ∈ Set.Icc 0 S) :
    |Q z θ τ| ≤ A * min z 1 := by
  rcases eq_or_lt_of_le hz with hz0 | hz0
  · have hQ0 : Q z θ τ = 0 := by rw [← hz0]; exact h.Q0 θ τ ⟨hθ.1.le, hθ.2.le⟩ hτ
    rw [hQ0, abs_zero]
    rw [← hz0, min_eq_left (by norm_num : (0:ℝ) ≤ 1), mul_zero]
  · exact h.Qb z θ τ hz0 hθ.1 hθ.2 hτ

/-- `min (dang θ) (dang θ')` only depends on the unordered pair. -/
theorem Paux_min_dang_eq (θ θ' : ℝ) :
    min (dang θ) (dang θ') = min (dang (min θ θ')) (dang (max θ θ')) := by
  rcases le_total θ θ' with h | h
  · rw [min_eq_left h, max_eq_right h]
  · rw [min_eq_right h, max_eq_left h, min_comm]

/-- `(min x y)^α = min (x^α) (y^α)` for `x, y ≥ 0`, `α ≥ 0`. -/
theorem Paux_rpow_min {x y α : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hα : 0 ≤ α) :
    (min x y) ^ α = min (x ^ α) (y ^ α) := by
  rcases le_total x y with h | h
  · rw [min_eq_left h, min_eq_left (Real.rpow_le_rpow hx h hα)]
  · rw [min_eq_right h, min_eq_right (Real.rpow_le_rpow hy h hα)]

/-- `|∂_θQ| ≤ A·min z 1·π/(4d)` for `0 < d ≤ dang θ`. -/
theorem pth_abs_le {α S A B : ℝ} {Q R : ℝ → ℝ → ℝ → ℝ} (h : ProdData α S A B Q R)
    {z θ τ d : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (π / 2)) (hτ : τ ∈ Set.Icc 0 S)
    (hd : 0 < d) (hdθ : d ≤ dang θ) :
    |Work.Spaces.pth (fun z θ => Q z θ τ) z θ| ≤ A * min z 1 * (π / (4 * d)) := by
  have hsin : 0 < Real.sin (2 * θ) := by
    apply Real.sin_pos_of_pos_of_lt_pi <;> linarith [hθ.1, hθ.2]
  have h1 : Real.sin (2 * θ) * |Work.Spaces.pth (fun z θ => Q z θ τ) z θ| ≤ A * min z 1 := by
    have h := h.Qth z θ τ hz hθ.1 hθ.2 hτ
    rw [show Work.Spaces.Dth (fun z θ => Q z θ τ) z θ
        = Real.sin (2 * θ) * Work.Spaces.pth (fun z θ => Q z θ τ) z θ from rfl,
      abs_mul, abs_of_pos hsin] at h
    exact h
  have hinv := inv_sin_two_le hθ hd hdθ
  have hA0 : 0 ≤ A * min z 1 := mul_nonneg h.A_nonneg (le_min hz.le zero_le_one)
  calc |Work.Spaces.pth (fun z θ => Q z θ τ) z θ|
      = Real.sin (2 * θ) * |Work.Spaces.pth (fun z θ => Q z θ τ) z θ|
          * (1 / Real.sin (2 * θ)) := by
        field_simp
    _ ≤ (A * min z 1) * (1 / Real.sin (2 * θ)) :=
        mul_le_mul_of_nonneg_right h1 (by positivity)
    _ ≤ (A * min z 1) * (π / (4 * d)) := mul_le_mul_of_nonneg_left hinv hA0
    _ = A * min z 1 * (π / (4 * d)) := by ring

/-- The `θ`-modulus of the coefficient: the mean-value bound with the segment's endpoint
distance. -/
theorem abs_th_sub_le {α S A B : ℝ} {Q R : ℝ → ℝ → ℝ → ℝ} (h : ProdData α S A B Q R)
    {z θ θ' τ : ℝ} (hz : 0 ≤ z) (hθ : θ ∈ Set.Ioo 0 (π / 2)) (hθ' : θ' ∈ Set.Ioo 0 (π / 2))
    (hτ : τ ∈ Set.Icc 0 S) :
    |Q z θ τ - Q z θ' τ| ≤ A * min z 1 * (π / (4 * min (dang θ) (dang θ'))) * |θ - θ'| := by
  set d := min (dang θ) (dang θ') with hd
  have hd0 : 0 < d := lt_min (dang_pos_of_mem_Ioo hθ) (dang_pos_of_mem_Ioo hθ')
  rcases eq_or_lt_of_le hz with hz0 | hz0
  · have h1 : Q z θ τ = 0 := by rw [← hz0]; exact h.Q0 θ τ ⟨hθ.1.le, hθ.2.le⟩ hτ
    have h2 : Q z θ' τ = 0 := by rw [← hz0]; exact h.Q0 θ' τ ⟨hθ'.1.le, hθ'.2.le⟩ hτ
    rw [h1, h2, sub_self, abs_zero]
    refine mul_nonneg (mul_nonneg (mul_nonneg h.A_nonneg (le_min hz zero_le_one))
      (by positivity)) (abs_nonneg _)
  · have hmem : ∀ x ∈ Set.Icc (min θ θ') (max θ θ'), x ∈ Set.Ioo 0 (π / 2) := by
      intro x hx
      exact ⟨lt_of_lt_of_le (lt_min hθ.1 hθ'.1) hx.1, lt_of_le_of_lt hx.2 (max_lt hθ.2 hθ'.2)⟩
    have hf : ∀ x ∈ Set.Icc (min θ θ') (max θ θ'), DifferentiableAt ℝ (fun x => Q z x τ) x :=
      fun x hx => h.Qdth z x τ hz0 (hmem x hx).1 (hmem x hx).2 hτ
    have hb : ∀ x ∈ Set.Icc (min θ θ') (max θ θ'),
        ‖deriv (fun x => Q z x τ) x‖ ≤ A * min z 1 * (π / (4 * d)) := by
      intro x hx
      have hdx : d ≤ dang x := by
        rw [hd, Paux_min_dang_eq]
        exact le_dang_of_mem_Icc hx
      have := pth_abs_le (d := d) h hz0 (hmem x hx) hτ hd0 hdx
      simpa [Real.norm_eq_abs, Work.Spaces.pth] using this
    have hmain := Convex.norm_image_sub_le_of_norm_deriv_le hf hb (convex_Icc _ _)
      (⟨le_rfl, min_le_max⟩ : min θ θ' ∈ Set.Icc (min θ θ') (max θ θ'))
      (⟨min_le_max, le_rfl⟩ : max θ θ' ∈ Set.Icc (min θ θ') (max θ θ'))
    have h2 : max θ θ' - min θ θ' = |θ - θ'| := by
      rcases le_total θ θ' with hle | hle
      · rw [max_eq_right hle, min_eq_left hle, abs_of_nonpos (sub_nonpos.mpr hle)]
        ring
      · rw [max_eq_left hle, min_eq_right hle, abs_of_nonneg (sub_nonneg.mpr hle)]
    have h3 : |Q z (max θ θ') τ - Q z (min θ θ') τ| = |Q z θ τ - Q z θ' τ| := by
      rcases le_total θ θ' with hle | hle
      · rw [max_eq_right hle, min_eq_left hle, abs_sub_comm]
      · rw [max_eq_left hle, min_eq_right hle]
    have h4 : |Q z (max θ θ') τ - Q z (min θ θ') τ|
        ≤ A * min z 1 * (π / (4 * d)) * (max θ θ' - min θ θ') := by
      have h5 := hmain
      simp only [Real.norm_eq_abs] at h5
      rw [abs_of_nonneg (sub_nonneg.mpr min_le_max)] at h5
      exact h5
    rw [h3, h2] at h4
    exact h4

/-- `|a - d| ≤ |a - b| + |b - c| + |c - d|`. -/
theorem Paux_abs_sub_le_three (a b c d : ℝ) :
    |a - d| ≤ |a - b| + |b - c| + |c - d| := by
  have h1 : a - d = (a - b) + (b - c) + (c - d) := by ring
  rw [h1]
  have h2 := abs_add_le ((a - b) + (b - c)) (c - d)
  have h3 := abs_add_le (a - b) (b - c)
  linarith [h2, h3, abs_nonneg (a - b), abs_nonneg (b - c), abs_nonneg (c - d)]

/-- The `θ`-modulus of a product slot, in the ordered case `Γ θ ≤ Γ θ'`. -/
theorem prod_thmod_ordered {α S A B : ℝ} {Q R : ℝ → ℝ → ℝ → ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    (h : ProdData α S A B Q R) {z θ θ' τ : ℝ} (hz : 0 ≤ z) (hθ : θ ∈ Set.Ioo 0 (π / 2))
    (hθ' : θ' ∈ Set.Ioo 0 (π / 2)) (hτ : τ ∈ Set.Icc 0 S) (hcase : Gmp α θ ≤ Gmp α θ') :
    |Q z θ τ * R z θ τ - Q z θ' τ * R z θ' τ| ≤ 3 * A * B * |θ - θ'| ^ α := by
  have hθI : θ ∈ Work.Spaces.Iθ := ⟨hθ.1.le, hθ.2.le⟩
  have hθ'I : θ' ∈ Work.Spaces.Iθ := ⟨hθ'.1.le, hθ'.2.le⟩
  have hAB : 0 ≤ A * B := mul_nonneg h.A_nonneg h.B_nonneg
  set d := min (dang θ) (dang θ') with hd
  have hd0 : 0 < d := lt_min (dang_pos_of_mem_Ioo hθ) (dang_pos_of_mem_Ioo hθ')
  have hx0 : 0 ≤ |θ - θ'| := abs_nonneg _
  have hxα : 0 ≤ |θ - θ'| ^ α := Real.rpow_nonneg hx0 α
  have hc0 : 0 ≤ A * min z 1 := mul_nonneg h.A_nonneg (le_min hz zero_le_one)
  have hΓ : Gmp α θ ≤ d ^ α := by
    have h0 : Gmp α θ ≤ dang θ ^ α := Gmp_le_dang_rpow hα hθI
    have h1 : Gmp α θ' ≤ dang θ' ^ α := Gmp_le_dang_rpow hα hθ'I
    have h2 : min (Gmp α θ) (Gmp α θ') ≤ min (dang θ ^ α) (dang θ' ^ α) := min_le_min h0 h1
    have h3 : Gmp α θ = min (Gmp α θ) (Gmp α θ') := (min_eq_left hcase).symm
    have h4 : min (dang θ ^ α) (dang θ' ^ α) = d ^ α := by
      rw [hd]
      exact (Paux_rpow_min (dang_nonneg_of_mem hθI) (dang_nonneg_of_mem hθ'I) (le_of_lt hα)).symm
    rw [h3]
    exact le_trans h2 (le_of_eq h4)
  have hdmvt := abs_th_sub_le h hz hθ hθ' hτ
  have hdtriv : |Q z θ τ - Q z θ' τ| ≤ 2 * (A * min z 1) := by
    have h1 := abs_Q_le_min h hz hθ hτ
    have h2 := abs_Q_le_min h hz hθ' hτ
    have h3 := Paux_abs_sub_le_add_abs (Q z θ τ) (Q z θ' τ)
    linarith
  have hterm1 : |(Q z θ τ - Q z θ' τ) * R z θ τ| ≤ 2 * A * B * |θ - θ'| ^ α := by
    rw [abs_mul]
    have hR1 : |R z θ τ| ≤ B * d ^ α := by
      have h1 := h.RGam z θ τ hz hθI hτ
      exact le_trans h1 (mul_le_mul_of_nonneg_left hΓ h.B_nonneg)
    have hQmin : |Q z θ τ - Q z θ' τ| ≤ min (2 * (A * min z 1))
        (A * min z 1 * (π / (4 * d)) * |θ - θ'|) := le_min hdtriv hdmvt
    have h0 : 0 ≤ min (2 * (A * min z 1))
        (A * min z 1 * (π / (4 * d)) * |θ - θ'|) :=
      le_min (by positivity) (by positivity)
    have h1 : |Q z θ τ - Q z θ' τ| * |R z θ τ|
        ≤ min (2 * (A * min z 1))
            (A * min z 1 * (π / (4 * d)) * |θ - θ'|) * (B * d ^ α) :=
      mul_le_mul hQmin hR1 (abs_nonneg _) h0
    have h2 := Paux_min_mul_rpow hc0 h.B_nonneg hd0 hx0 hα hα1
    have h3 : 2 * (A * min z 1) * B * |θ - θ'| ^ α ≤ 2 * A * B * |θ - θ'| ^ α := by
      have h4 : min z 1 ≤ 1 := min_le_right _ _
      have h5 : A * min z 1 ≤ A * 1 := mul_le_mul_of_nonneg_left h4 h.A_nonneg
      rw [mul_one] at h5
      have h6 : 0 ≤ B * |θ - θ'| ^ α := mul_nonneg h.B_nonneg hxα
      have h7 := mul_le_mul_of_nonneg_right h5 h6
      linarith [h7]
    linarith
  have hterm2 : |Q z θ' τ * (R z θ τ - R z θ' τ)| ≤ A * B * |θ - θ'| ^ α := by
    rw [abs_mul]
    have h1 : |Q z θ' τ| * |R z θ τ - R z θ' τ| ≤ A * (B * |θ - θ'| ^ α) :=
      mul_le_mul (abs_Q_le h hz hθ' hτ) (R_th_mod h hz hθI hθ'I hτ) (abs_nonneg _) h.A_nonneg
    have h2 : A * (B * |θ - θ'| ^ α) = A * B * |θ - θ'| ^ α := by ring
    rw [h2] at h1
    exact h1
  have htel2 : |Q z θ τ * R z θ τ - Q z θ' τ * R z θ τ| ≤ 2 * A * B * |θ - θ'| ^ α := by
    have he : Q z θ τ * R z θ τ - Q z θ' τ * R z θ τ
        = (Q z θ τ - Q z θ' τ) * R z θ τ := by ring
    rw [he]
    exact hterm1
  have htel := Paux_abs_sub_le_three (Q z θ τ * R z θ τ) (Q z θ' τ * R z θ τ)
    (Q z θ' τ * R z θ' τ) (Q z θ' τ * R z θ' τ)
  have e1 : Q z θ τ * R z θ τ - Q z θ' τ * R z θ τ = (Q z θ τ - Q z θ' τ) * R z θ τ := by ring
  have e2 : Q z θ' τ * R z θ τ - Q z θ' τ * R z θ' τ = Q z θ' τ * (R z θ τ - R z θ' τ) := by ring
  have e3 : |Q z θ' τ * R z θ' τ - Q z θ' τ * R z θ' τ| = 0 := by rw [sub_self, abs_zero]
  rw [e1, e2, e3, add_zero] at htel
  have hfin : 2 * A * B * |θ - θ'| ^ α + A * B * |θ - θ'| ^ α ≤ 3 * A * B * |θ - θ'| ^ α := by
    nlinarith [hAB, hxα]
  linarith [htel, hterm1, hterm2, hfin]

/-- The `θ`-modulus of a product slot. -/
theorem prod_thmod {α S A B : ℝ} {Q R : ℝ → ℝ → ℝ → ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    (h : ProdData α S A B Q R) {z θ θ' τ : ℝ} (hz : 0 ≤ z) (hθ : θ ∈ Set.Ioo 0 (π / 2))
    (hθ' : θ' ∈ Set.Ioo 0 (π / 2)) (hτ : τ ∈ Set.Icc 0 S) :
    |Q z θ τ * R z θ τ - Q z θ' τ * R z θ' τ| ≤ 3 * A * B * |θ - θ'| ^ α := by
  rcases le_total (Gmp α θ) (Gmp α θ') with hcase | hcase
  · exact prod_thmod_ordered hα hα1 h hz hθ hθ' hτ hcase
  · have h1 := prod_thmod_ordered hα hα1 h hz hθ' hθ hτ hcase
    rw [abs_sub_comm θ' θ] at h1
    rw [abs_sub_comm (Q z θ τ * R z θ τ) (Q z θ' τ * R z θ' τ)]
    exact h1


end Work.FTS_RegExport.RXR5L
