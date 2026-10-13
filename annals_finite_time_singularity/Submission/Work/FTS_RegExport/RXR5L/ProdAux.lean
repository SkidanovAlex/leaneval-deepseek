/-
# `Work.FTS_RegExport.RXR5L.ProdAux` — the product lemma of `EllProd_C1JetFull`

`EllProd_C1JetFull` asks for `C1Jet`-regularity of the three product slots
`P₁ = Rop Φ̃·F_τ`, `P₂ = (Uop Φ̃/sin 2θ)·D_θF_τ`, `P₃ = Vop Φ̃·D_zF_τ` (see `ProdDefs`).
The coefficients alone are *not* continuous at `θ = π/2` (their `psiR`-junk value is `0` while the
one-sided limit is not), but each slot is the product of

* a **coefficient** `Q` with the `vanish0`-type data `|Q|, |D_zQ|, |D_θQ| ≤ A·min z 1`,
  `Q(0,·,·) = 0`, `τ`-Lipschitz constant `A`, and differentiable slices,
* a **factor** `R` which is a `C1Jet` *and* `Γ`-shaped: `|R| ≤ B·Γ(θ)`,
  `Γ(θ) = (sinθcos²θ)^α = Gmp α θ`.

Then the product is a `C1Jet`: the `Γ`-vanishing of the factor absorbs the `1/sin 2θ` of the
coefficient, and the endpoint values of the product are `0`.

This file proves the general statement `prod_C1Jet_of_vanish`, together with the two elementary
one-variable facts it needs:
`Γ(θ) ≤ dang θ ^ α` and `sin 2θ ≥ (4/π)·dang θ`, where `dang θ = min θ (π/2 − θ)`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS_RegExport.RXR5L.ProdDefs
import Submission.Work.FTS.H2.STBasic
import Submission.Work.FTS.RegPkgGal.Der.Defs

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

/-! ## §1 Elementary facts about the endpoint distance `dang` -/

theorem dang_le_self (θ : ℝ) : dang θ ≤ θ := min_le_left _ _

theorem dang_le_half (θ : ℝ) : dang θ ≤ π / 2 - θ := min_le_right _ _

theorem dang_nonneg_of_mem {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ dang θ :=
  le_min hθ.1 (by linarith [hθ.2])

theorem dang_pos_of_mem_Ioo {θ : ℝ} (h : θ ∈ Set.Ioo 0 (π / 2)) : 0 < dang θ :=
  lt_min h.1 (by linarith [h.2])

theorem dang_eq_self_of_le {θ : ℝ} (h : θ ≤ π / 4) : dang θ = θ :=
  min_eq_left (by linarith [Real.pi_gt_three])

theorem dang_eq_half_of_le {θ : ℝ} (h : π / 4 ≤ θ) : dang θ = π / 2 - θ :=
  min_eq_right (by linarith [Real.pi_gt_three])

theorem dang_le_one_of_mem {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : dang θ ≤ 1 := by
  rcases le_total θ (π / 4) with h | h
  · have := dang_le_self θ; linarith [Real.pi_lt_four]
  · have := dang_le_half θ; linarith [Real.pi_lt_four]

/-- `dang` has no interior minimum below the endpoints' values: on the segment between `a` and
`b`, `dang x ≥ min (dang a) (dang b)`. -/
theorem le_dang_of_mem_Icc {a b x : ℝ} (hx : x ∈ Set.Icc a b) :
    min (dang a) (dang b) ≤ dang x := by
  have h3 : min (dang a) (dang b) ≤ x :=
    le_trans (min_le_left _ _) (le_trans (dang_le_self a) hx.1)
  have h4 : min (dang a) (dang b) ≤ π / 2 - x :=
    le_trans (min_le_right _ _) (le_trans (dang_le_half b) (by linarith [hx.2]))
  exact le_min h3 h4

/-- `Γ(θ) = (sinθcos²θ)^α ≤ dang θ ^ α` on `Iθ`. -/
theorem Gmp_le_dang_rpow {α θ : ℝ} (hα : 0 < α) (hθ : θ ∈ Work.Spaces.Iθ) :
    Gmp α θ ≤ dang θ ^ α := by
  have hbase : 0 ≤ Real.sin θ * Real.cos θ ^ 2 := by
    have := Real.sin_nonneg_of_mem_Icc ⟨hθ.1, by linarith [hθ.2, Real.pi_pos]⟩
    positivity
  rcases le_total θ (π / 4) with h | h
  · rw [dang_eq_self_of_le h]
    have hsin : Real.sin θ * Real.cos θ ^ 2 ≤ θ := by
      have h1 : Real.sin θ ≤ θ := by
        rcases eq_or_lt_of_le hθ.1 with h0 | h0
        · rw [← h0, Real.sin_zero]
        · exact le_of_lt (Real.sin_lt h0)
      have h2 : Real.cos θ ^ 2 ≤ 1 := by
        nlinarith [Real.cos_le_one θ, Real.neg_one_le_cos θ]
      have h5 := Real.sin_nonneg_of_mem_Icc ⟨hθ.1, by linarith [hθ.2, Real.pi_pos]⟩
      nlinarith [sq_nonneg (Real.cos θ)]
    exact Real.rpow_le_rpow hbase hsin hα.le
  · rw [dang_eq_half_of_le h]
    have hcos : Real.cos θ = Real.sin (π / 2 - θ) := (Real.sin_pi_div_two_sub θ).symm
    have hsin1 : Real.sin θ * Real.cos θ ^ 2 ≤ π / 2 - θ := by
      have hδ0 : 0 ≤ π / 2 - θ := by linarith [hθ.2]
      have hδ1 : π / 2 - θ ≤ π / 4 := by linarith
      have h1 : Real.sin θ ≤ 1 := Real.sin_le_one θ
      have h2 : Real.cos θ ^ 2 ≤ (π / 2 - θ) ^ 2 := by
        rw [hcos, sq]
        have h3 : Real.sin (π / 2 - θ) ≤ π / 2 - θ := by
          rcases eq_or_lt_of_le hδ0 with h0 | h0
          · rw [← h0, Real.sin_zero]
          · exact le_of_lt (Real.sin_lt h0)
        have h4 := Real.sin_nonneg_of_mem_Icc ⟨hδ0, by linarith [Real.pi_pos]⟩
        nlinarith
      have h5 := Real.sin_nonneg_of_mem_Icc ⟨hθ.1, by linarith [hθ.2, Real.pi_pos]⟩
      have h6 : (π / 2 - θ) ^ 2 ≤ π / 2 - θ := by
        nlinarith [hδ0, hδ1, Real.pi_lt_four]
      nlinarith [sq_nonneg (Real.cos θ)]
    exact Real.rpow_le_rpow hbase hsin1 hα.le

/-- `sin 2θ ≥ (4/π)·dang θ` on `Iθ` (`Work.FTS.H2.sin_two_ge_min`). -/
theorem sin_two_ge_dang {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    (4 / π) * dang θ ≤ Real.sin (2 * θ) :=
  Work.FTS.H2.sin_two_ge_min θ hθ

/-- On the open angular interval, `1/sin 2θ ≤ π/(4·d)` for any `0 < d ≤ dang θ`. -/
theorem inv_sin_two_le {θ d : ℝ} (hθ : θ ∈ Set.Ioo 0 (π / 2)) (hd : 0 < d)
    (hdθ : d ≤ dang θ) : 1 / Real.sin (2 * θ) ≤ π / (4 * d) := by
  have hπ : (0 : ℝ) < π := Real.pi_pos
  have hpos : 0 < Real.sin (2 * θ) := by
    apply Real.sin_pos_of_pos_of_lt_pi
    · linarith [hθ.1]
    · linarith [hθ.2]
  have hge : (4 / π) * d ≤ Real.sin (2 * θ) := by
    have h := sin_two_ge_dang ⟨hθ.1.le, hθ.2.le⟩
    calc (4 / π) * d ≤ (4 / π) * dang θ :=
          mul_le_mul_of_nonneg_left hdθ (by positivity)
      _ ≤ Real.sin (2 * θ) := h
  have hkey : 4 * d ≤ π * Real.sin (2 * θ) := by
    have h := hge
    rw [div_mul_eq_mul_div, div_le_iff₀ hπ] at h
    linarith
  rw [div_le_iff₀ hpos, div_mul_eq_mul_div, le_div_iff₀ (by positivity : (0 : ℝ) < 4 * d),
    one_mul]
  linarith

/-! ## §2 The bundled data of the product lemma -/

/-- The data of the product lemma: a coefficient `Q` with the `vanish0`-type bounds and a
`Γ`-shaped `C1Jet` factor `R`. -/
structure ProdData (α S A B : ℝ) (Q R : ℝ → ℝ → ℝ → ℝ) : Prop where
  A_nonneg : 0 ≤ A
  B_nonneg : 0 ≤ B
  Qb : ∀ z θ τ, 0 < z → 0 < θ → θ < π / 2 → τ ∈ Set.Icc 0 S → |Q z θ τ| ≤ A * min z 1
  Q0 : ∀ θ τ, θ ∈ Work.Spaces.Iθ → τ ∈ Set.Icc 0 S → Q 0 θ τ = 0
  Qth : ∀ z θ τ, 0 < z → 0 < θ → θ < π / 2 → τ ∈ Set.Icc 0 S →
    |Work.Spaces.Dth (fun z θ => Q z θ τ) z θ| ≤ A * min z 1
  Qz : ∀ z θ τ, 0 < z → 0 < θ → θ < π / 2 → τ ∈ Set.Icc 0 S →
    |Work.Spaces.Dz (fun z θ => Q z θ τ) z θ| ≤ A * min z 1
  Qtau : ∀ z θ τ τ', 0 < z → 0 < θ → θ < π / 2 → τ ∈ Set.Icc 0 S → τ' ∈ Set.Icc 0 S →
    |Q z θ τ - Q z θ τ'| ≤ A * |τ - τ'|
  Qdz : ∀ z θ τ, 0 < z → 0 < θ → θ < π / 2 → τ ∈ Set.Icc 0 S →
    DifferentiableAt ℝ (fun z' => Q z' θ τ) z
  Qdth : ∀ z θ τ, 0 < z → 0 < θ → θ < π / 2 → τ ∈ Set.Icc 0 S →
    DifferentiableAt ℝ (fun θ' => Q z θ' τ) θ
  Rjet : Work.FTS.RegPkgGal.C1Jet α S B R
  RGam : ∀ z θ τ, 0 ≤ z → θ ∈ Work.Spaces.Iθ → τ ∈ Set.Icc 0 S → |R z θ τ| ≤ B * Gmp α θ

/-- `Γ` vanishes at the angular endpoints. -/
theorem Gmp_eq_zero_of_endpoint {α θ : ℝ} (hα : 0 < α) (hθ : θ = 0 ∨ θ = π / 2) :
    Gmp α θ = 0 := by
  have hΓ : ∀ θ : ℝ, Gmp α θ = (Real.sin θ * Real.cos θ ^ 2) ^ α := fun θ => rfl
  rcases hθ with rfl | rfl
  · rw [hΓ]
    have h : Real.sin 0 * Real.cos 0 ^ 2 = (0 : ℝ) := by norm_num
    rw [h]
    exact Real.zero_rpow hα.ne'
  · rw [hΓ]
    have h : Real.sin (π / 2) * Real.cos (π / 2) ^ 2 = (0 : ℝ) := by
      rw [Real.sin_pi_div_two, Real.cos_pi_div_two]
      norm_num
    rw [h]
    exact Real.zero_rpow hα.ne'

/-- The uniform bound of a product slot on the closed box. -/
theorem prod_abs_le {α S A B : ℝ} {Q R : ℝ → ℝ → ℝ → ℝ} (hα : 0 < α)
    (h : ProdData α S A B Q R) {z θ τ : ℝ} (hz : 0 ≤ z) (hθ : θ ∈ Work.Spaces.Iθ)
    (hτ : τ ∈ Set.Icc 0 S) : |Q z θ τ * R z θ τ| ≤ A * B := by
  have hAB : 0 ≤ A * B := mul_nonneg h.A_nonneg h.B_nonneg
  rw [abs_mul]
  rcases eq_or_lt_of_le hz with hz0 | hz0
  · have hQz0 : Q z θ τ = 0 := by rw [← hz0]; exact h.Q0 θ τ hθ hτ
    rw [hQz0, abs_zero, zero_mul]
    exact hAB
  · by_cases hθe : θ = 0 ∨ θ = π / 2
    · have hR0 : R z θ τ = 0 := by
        have hb := h.RGam z θ τ hz hθ hτ
        rw [Gmp_eq_zero_of_endpoint hα hθe, mul_zero] at hb
        exact abs_eq_zero.mp (le_antisymm hb (abs_nonneg _))
      rw [hR0, abs_zero, mul_zero]
      exact hAB
    · have hθ0 : 0 < θ := lt_of_le_of_ne hθ.1 (fun hc => hθe (Or.inl hc.symm))
      have hθ2 : θ < π / 2 := lt_of_le_of_ne hθ.2 (fun hc => hθe (Or.inr hc))
      have hQb := h.Qb z θ τ hz0 hθ0 hθ2 hτ
      have hRb := h.RGam z θ τ hz hθ hτ
      have hG1 : Gmp α θ ≤ 1 := Gmp_le_one hα.le hθ
      have hmin1 : min z 1 ≤ 1 := min_le_right _ _
      have hG0 : 0 ≤ Gmp α θ := Gmp_nonneg hθ
      have hAz0 : 0 ≤ A * min z 1 := mul_nonneg h.A_nonneg (le_min hz0.le zero_le_one)
      have h2 : A * min z 1 ≤ A * 1 := mul_le_mul_of_nonneg_left hmin1 h.A_nonneg
      have h3 : B * Gmp α θ ≤ B * 1 := mul_le_mul_of_nonneg_left hG1 h.B_nonneg
      have hB2 : 0 ≤ A * 1 := mul_nonneg h.A_nonneg zero_le_one
      calc |Q z θ τ| * |R z θ τ| ≤ (A * min z 1) * (B * Gmp α θ) :=
            mul_le_mul hQb hRb (abs_nonneg _) hAz0
        _ ≤ (A * 1) * (B * 1) :=
            mul_le_mul h2 h3 (mul_nonneg h.B_nonneg hG0) hB2
        _ = A * B := by ring

/-! ## §3 The one-variable moduli of the coefficient -/

/-- `|∂_zQ| ≤ A` on the open quadrant. -/
theorem pz_abs_le {α S A B : ℝ} {Q R : ℝ → ℝ → ℝ → ℝ} (h : ProdData α S A B Q R)
    {z θ τ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (π / 2)) (hτ : τ ∈ Set.Icc 0 S) :
    |Work.Spaces.pz (fun z θ => Q z θ τ) z θ| ≤ A := by
  have h1 : |z * Work.Spaces.pz (fun z θ => Q z θ τ) z θ| ≤ A * min z 1 :=
    h.Qz z θ τ hz hθ.1 hθ.2 hτ
  rw [abs_mul, abs_of_pos hz] at h1
  have h2 : A * min z 1 ≤ A * z := mul_le_mul_of_nonneg_left (min_le_left _ _) h.A_nonneg
  nlinarith [h1, h2, hz, abs_nonneg (Work.Spaces.pz (fun z θ => Q z θ τ) z θ), h.A_nonneg]

/-- `|Q z θ τ − Q z' θ τ| ≤ A·|z − z'|` for `z, z' > 0`. -/
theorem abs_z_sub_le {α S A B : ℝ} {Q R : ℝ → ℝ → ℝ → ℝ} (h : ProdData α S A B Q R)
    {z z' θ τ : ℝ} (hz : 0 < z) (hz' : 0 < z') (hθ : θ ∈ Set.Ioo 0 (π / 2))
    (hτ : τ ∈ Set.Icc 0 S) :
    |Q z θ τ - Q z' θ τ| ≤ A * |z - z'| := by
  have hzmin : 0 < min z z' := lt_min hz hz'
  have hf : ∀ x ∈ Set.Icc (min z z') (max z z'), DifferentiableAt ℝ (fun x => Q x θ τ) x :=
    fun x hx => h.Qdz x θ τ (lt_of_lt_of_le hzmin hx.1) hθ.1 hθ.2 hτ
  have hb : ∀ x ∈ Set.Icc (min z z') (max z z'),
      ‖deriv (fun x => Q x θ τ) x‖ ≤ A := by
    intro x hx
    have hx0 : 0 < x := lt_of_lt_of_le hzmin hx.1
    have := pz_abs_le h hx0 hθ hτ
    simpa [Real.norm_eq_abs, Work.Spaces.pz] using this
  have hmain := Convex.norm_image_sub_le_of_norm_deriv_le hf hb (convex_Icc _ _)
    (⟨le_rfl, min_le_max⟩ : min z z' ∈ Set.Icc (min z z') (max z z'))
    (⟨min_le_max, le_rfl⟩ : max z z' ∈ Set.Icc (min z z') (max z z'))
  have h2 : max z z' - min z z' = |z - z'| := by
    rcases le_total z z' with hle | hle
    · rw [max_eq_right hle, min_eq_left hle, abs_of_nonpos (sub_nonpos.mpr hle)]
      ring
    · rw [max_eq_left hle, min_eq_right hle, abs_of_nonneg (sub_nonneg.mpr hle)]
  have h3 : |Q (max z z') θ τ - Q (min z z') θ τ| = |Q z θ τ - Q z' θ τ| := by
    rcases le_total z z' with hle | hle
    · rw [max_eq_right hle, min_eq_left hle, abs_sub_comm]
    · rw [max_eq_left hle, min_eq_right hle]
  have h4 : |Q (max z z') θ τ - Q (min z z') θ τ| ≤ A * (max z z' - min z z') := by
    have h := hmain
    simp only [Real.norm_eq_abs] at h
    rw [abs_of_nonneg (sub_nonneg.mpr min_le_max)] at h
    exact h
  rw [h3, h2] at h4
  exact h4

/-- The sharper bound `|Q z θ τ·R z θ τ| ≤ A·B·z` for `z > 0` and `θ` in the open interval. -/
theorem prod_le_mul {α S A B : ℝ} {Q R : ℝ → ℝ → ℝ → ℝ} (hα : 0 < α)
    (h : ProdData α S A B Q R) {z θ τ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (π / 2))
    (hτ : τ ∈ Set.Icc 0 S) :
    |Q z θ τ * R z θ τ| ≤ A * B * z := by
  have hθI : θ ∈ Work.Spaces.Iθ := ⟨hθ.1.le, hθ.2.le⟩
  have hQb := h.Qb z θ τ hz hθ.1 hθ.2 hτ
  have hRb := h.RGam z θ τ hz.le hθI hτ
  have hG1 : Gmp α θ ≤ 1 := Gmp_le_one (le_of_lt hα) hθI
  have hG0 : 0 ≤ Gmp α θ := Gmp_nonneg hθI
  have hmin : min z 1 ≤ z := min_le_left _ _
  have hAz : 0 ≤ A * min z 1 := mul_nonneg h.A_nonneg (le_min hz.le zero_le_one)
  have hBz : 0 ≤ B * Gmp α θ := mul_nonneg h.B_nonneg hG0
  have h1 : |Q z θ τ| * |R z θ τ| ≤ (A * min z 1) * (B * Gmp α θ) :=
    mul_le_mul hQb hRb (abs_nonneg _) hAz
  have h2 : (A * min z 1) * (B * Gmp α θ) ≤ (A * z) * (B * 1) :=
    mul_le_mul (mul_le_mul_of_nonneg_left hmin h.A_nonneg)
      (mul_le_mul_of_nonneg_left hG1 h.B_nonneg) hBz (mul_nonneg h.A_nonneg hz.le)
  rw [abs_mul]
  calc |Q z θ τ| * |R z θ τ| ≤ (A * z) * (B * 1) := le_trans h1 h2
    _ = A * B * z := by ring

/-! ## §4 Two elementary inequalities -/

/-- `|a - b| ≤ |a| + |b|`. -/
theorem Paux_abs_sub_le_add_abs (a b : ℝ) : |a - b| ≤ |a| + |b| := by
  simpa [sub_eq_add_neg] using abs_add_le a (-b)

/-- The minimum of the trivial bound and the "linear plus `α`-power" bound is dominated by the
`α`-power (note `α ≤ 1` is needed). -/
theorem Paux_min_le_two_mul_rpow {c t α : ℝ} (hc : 0 ≤ c) (ht : 0 ≤ t) (hα0 : 0 < α)
    (hα1 : α ≤ 1) : min (2 * c) (c * t + c * t ^ α) ≤ 2 * c * t ^ α := by
  have htα : 0 ≤ t ^ α := Real.rpow_nonneg ht α
  rcases le_total t 1 with h | h
  · refine le_trans (min_le_right _ _) ?_
    have htle : t ≤ t ^ α := by
      rcases eq_or_lt_of_le ht with h0 | h0
      · rw [← h0, Real.zero_rpow hα0.ne']
      · have h1 : t ^ (1 : ℝ) ≤ t ^ α := Real.rpow_le_rpow_of_exponent_ge h0 h hα1
        rwa [Real.rpow_one] at h1
    nlinarith
  · refine le_trans (min_le_left _ _) ?_
    have h1 : 1 ≤ t ^ α := Real.one_le_rpow h hα0.le
    nlinarith

/-! ## §5 The one-variable moduli of a product slot -/

/-- `|Q z θ τ − Q z' θ τ| ≤ A·|z − z'|` for all `z, z' ≥ 0`. -/
theorem abs_z_sub_le' {α S A B : ℝ} {Q R : ℝ → ℝ → ℝ → ℝ} (h : ProdData α S A B Q R)
    {z z' θ τ : ℝ} (hz : 0 ≤ z) (hz' : 0 ≤ z') (hθ : θ ∈ Set.Ioo 0 (π / 2))
    (hτ : τ ∈ Set.Icc 0 S) :
    |Q z θ τ - Q z' θ τ| ≤ A * |z - z'| := by
  rcases eq_or_lt_of_le hz with hz0 | hz0
  · have hQ0 : Q z θ τ = 0 := by rw [← hz0]; exact h.Q0 θ τ ⟨hθ.1.le, hθ.2.le⟩ hτ
    rw [hQ0, zero_sub, abs_neg]
    rcases eq_or_lt_of_le hz' with hz0' | hz0'
    · have hQ0' : Q z' θ τ = 0 := by rw [← hz0']; exact h.Q0 θ τ ⟨hθ.1.le, hθ.2.le⟩ hτ
      rw [hQ0', abs_zero, ← hz0, ← hz0', sub_self, abs_zero, mul_zero]
    · have h1 := h.Qb z' θ τ hz0' hθ.1 hθ.2 hτ
      have h2 : A * min z' 1 ≤ A * z' := mul_le_mul_of_nonneg_left (min_le_left _ _) h.A_nonneg
      have h3 : |z - z'| = z' := by rw [← hz0, zero_sub, abs_neg, abs_of_pos hz0']
      rw [h3]
      exact le_trans h1 h2
  · rcases eq_or_lt_of_le hz' with hz0' | hz0'
    · have hQ0' : Q z' θ τ = 0 := by rw [← hz0']; exact h.Q0 θ τ ⟨hθ.1.le, hθ.2.le⟩ hτ
      rw [hQ0', sub_zero]
      have h1 := h.Qb z θ τ hz0 hθ.1 hθ.2 hτ
      have h2 : A * min z 1 ≤ A * z := mul_le_mul_of_nonneg_left (min_le_left _ _) h.A_nonneg
      have h3 : |z - z'| = z := by rw [← hz0', sub_zero, abs_of_pos hz0]
      rw [h3]
      exact le_trans h1 h2
    · exact abs_z_sub_le h hz0 hz0' hθ hτ

/-- `|Q z θ τ| ≤ A` for `z ≥ 0` and `θ` in the open interval. -/
theorem abs_Q_le {α S A B : ℝ} {Q R : ℝ → ℝ → ℝ → ℝ} (h : ProdData α S A B Q R)
    {z θ τ : ℝ} (hz : 0 ≤ z) (hθ : θ ∈ Set.Ioo 0 (π / 2)) (hτ : τ ∈ Set.Icc 0 S) :
    |Q z θ τ| ≤ A := by
  rcases eq_or_lt_of_le hz with hz0 | hz0
  · have hQ0 : Q z θ τ = 0 := by rw [← hz0]; exact h.Q0 θ τ ⟨hθ.1.le, hθ.2.le⟩ hτ
    rw [hQ0, abs_zero]; exact h.A_nonneg
  · have h1 := h.Qb z θ τ hz0 hθ.1 hθ.2 hτ
    have h2 : A * min z 1 ≤ A * 1 := mul_le_mul_of_nonneg_left (min_le_right _ _) h.A_nonneg
    have h3 : A * 1 = A := mul_one A
    rw [h3] at h2
    exact le_trans h1 h2

/-- `|R z θ τ| ≤ B` for `z ≥ 0` and `θ ∈ Iθ`. -/
theorem abs_R_le {α S A B : ℝ} {Q R : ℝ → ℝ → ℝ → ℝ} (hα : 0 < α)
    (h : ProdData α S A B Q R) {z θ τ : ℝ} (hz : 0 ≤ z) (hθ : θ ∈ Work.Spaces.Iθ)
    (hτ : τ ∈ Set.Icc 0 S) : |R z θ τ| ≤ B := by
  have h1 := h.RGam z θ τ hz hθ hτ
  have h2 : Gmp α θ ≤ 1 := Gmp_le_one (le_of_lt hα) hθ
  have h3 : B * Gmp α θ ≤ B * 1 := mul_le_mul_of_nonneg_left h2 h.B_nonneg
  rw [mul_one] at h3
  exact le_trans h1 h3

/-- The `θ`-modulus of `R` at fixed `(z,τ)`. -/
theorem R_th_mod {α S A B : ℝ} {Q R : ℝ → ℝ → ℝ → ℝ} (h : ProdData α S A B Q R)
    {z θ θ' τ : ℝ} (hz : 0 ≤ z) (hθ : θ ∈ Work.Spaces.Iθ) (hθ' : θ' ∈ Work.Spaces.Iθ)
    (hτ : τ ∈ Set.Icc 0 S) :
    |R z θ τ - R z θ' τ| ≤ B * |θ - θ'| ^ α := by
  have h1 := h.Rjet.1.2.2 z z θ θ' τ τ hz hz hθ hθ' hτ hτ
  simpa using h1

/-- The `z`-modulus of `R` at fixed `(θ,τ)`. -/
theorem R_z_mod {α S A B : ℝ} {Q R : ℝ → ℝ → ℝ → ℝ} (h : ProdData α S A B Q R)
    {z z' θ τ : ℝ} (hz : 0 ≤ z) (hz' : 0 ≤ z') (hθ : θ ∈ Work.Spaces.Iθ)
    (hτ : τ ∈ Set.Icc 0 S) :
    |R z θ τ - R z' θ τ| ≤ B * |z - z'| ^ α := by
  have h1 := h.Rjet.1.2.2 z z' θ θ τ τ hz hz' hθ hθ hτ hτ
  simpa using h1

/-- The `τ`-modulus of `R` at fixed `(z,θ)`. -/
theorem R_tau_mod {α S A B : ℝ} {Q R : ℝ → ℝ → ℝ → ℝ} (h : ProdData α S A B Q R)
    {z θ τ τ' : ℝ} (hz : 0 ≤ z) (hθ : θ ∈ Work.Spaces.Iθ) (hτ : τ ∈ Set.Icc 0 S)
    (hτ' : τ' ∈ Set.Icc 0 S) :
    |R z θ τ - R z θ τ'| ≤ B * |τ - τ'| ^ α := by
  have h1 := h.Rjet.1.2.2 z z θ θ τ τ' hz hz hθ hθ hτ hτ'
  simpa using h1

/-- The `z`-modulus of a product slot. -/
theorem prod_zmod {α S A B : ℝ} {Q R : ℝ → ℝ → ℝ → ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    (h : ProdData α S A B Q R) {z z' θ τ : ℝ} (hz : 0 ≤ z) (hz' : 0 ≤ z')
    (hθ : θ ∈ Set.Ioo 0 (π / 2)) (hτ : τ ∈ Set.Icc 0 S) :
    |Q z θ τ * R z θ τ - Q z' θ τ * R z' θ τ| ≤ 2 * A * B * |z - z'| ^ α := by
  have hθI : θ ∈ Work.Spaces.Iθ := ⟨hθ.1.le, hθ.2.le⟩
  have hAB : 0 ≤ A * B := mul_nonneg h.A_nonneg h.B_nonneg
  have hD0 : 0 ≤ |z - z'| := abs_nonneg _
  have hsup : |Q z θ τ * R z θ τ - Q z' θ τ * R z' θ τ| ≤ 2 * (A * B) := by
    have hP := prod_abs_le hα h hz hθI hτ
    have hP' := prod_abs_le hα h hz' hθI hτ
    have h4 := Paux_abs_sub_le_add_abs (Q z θ τ * R z θ τ) (Q z' θ τ * R z' θ τ)
    nlinarith [h4, hP, hP', hAB]
  have hcrude : |Q z θ τ * R z θ τ - Q z' θ τ * R z' θ τ|
      ≤ A * B * |z - z'| + A * B * |z - z'| ^ α := by
    have htel : Q z θ τ * R z θ τ - Q z' θ τ * R z' θ τ
        = (Q z θ τ - Q z' θ τ) * R z θ τ + Q z' θ τ * (R z θ τ - R z' θ τ) := by ring
    rw [htel]
    have h1 : |(Q z θ τ - Q z' θ τ) * R z θ τ| ≤ (A * |z - z'|) * B := by
      rw [abs_mul]
      exact mul_le_mul (abs_z_sub_le' h hz hz' hθ hτ) (abs_R_le hα h hz hθI hτ)
        (abs_nonneg _) (mul_nonneg h.A_nonneg hD0)
    have h2 : |Q z' θ τ * (R z θ τ - R z' θ τ)| ≤ A * (B * |z - z'| ^ α) := by
      rw [abs_mul]
      exact mul_le_mul (abs_Q_le h hz' hθ hτ) (R_z_mod h hz hz' hθI hτ) (abs_nonneg _) h.A_nonneg
    have h3 := abs_add_le ((Q z θ τ - Q z' θ τ) * R z θ τ)
      (Q z' θ τ * (R z θ τ - R z' θ τ))
    have h4 : (A * |z - z'|) * B + A * (B * |z - z'| ^ α)
        = A * B * |z - z'| + A * B * |z - z'| ^ α := by ring
    linarith [h3, h1, h2, h4]
  refine le_trans (le_min hsup hcrude) ?_
  have hmin := Paux_min_le_two_mul_rpow hAB hD0 hα hα1
  have h5 : 2 * (A * B) * |z - z'| ^ α = 2 * A * B * |z - z'| ^ α := by ring
  linarith [hmin, h5]

/-- The `τ`-modulus of a product slot. -/
theorem prod_taumod {α S A B : ℝ} {Q R : ℝ → ℝ → ℝ → ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    (h : ProdData α S A B Q R) {z θ τ τ' : ℝ} (hz : 0 ≤ z) (hθ : θ ∈ Set.Ioo 0 (π / 2))
    (hτ : τ ∈ Set.Icc 0 S) (hτ' : τ' ∈ Set.Icc 0 S) :
    |Q z θ τ * R z θ τ - Q z θ τ' * R z θ τ'| ≤ 2 * A * B * |τ - τ'| ^ α := by
  have hθI : θ ∈ Work.Spaces.Iθ := ⟨hθ.1.le, hθ.2.le⟩
  have hAB : 0 ≤ A * B := mul_nonneg h.A_nonneg h.B_nonneg
  have hD0 : 0 ≤ |τ - τ'| := abs_nonneg _
  have hsup : |Q z θ τ * R z θ τ - Q z θ τ' * R z θ τ'| ≤ 2 * (A * B) := by
    have hP := prod_abs_le hα h hz hθI hτ
    have hP' := prod_abs_le hα h hz hθI hτ'
    have h4 := Paux_abs_sub_le_add_abs (Q z θ τ * R z θ τ) (Q z θ τ' * R z θ τ')
    nlinarith [h4, hP, hP', hAB]
  have hcrude : |Q z θ τ * R z θ τ - Q z θ τ' * R z θ τ'|
      ≤ A * B * |τ - τ'| + A * B * |τ - τ'| ^ α := by
    have htel : Q z θ τ * R z θ τ - Q z θ τ' * R z θ τ'
        = (Q z θ τ - Q z θ τ') * R z θ τ + Q z θ τ' * (R z θ τ - R z θ τ') := by ring
    rw [htel]
    have hQtau : |Q z θ τ - Q z θ τ'| ≤ A * |τ - τ'| := by
      rcases eq_or_lt_of_le hz with hz0 | hz0
      · have hQ0 : Q z θ τ = 0 := by rw [← hz0]; exact h.Q0 θ τ hθI hτ
        have hQ0' : Q z θ τ' = 0 := by rw [← hz0]; exact h.Q0 θ τ' hθI hτ'
        rw [hQ0, hQ0', sub_self, abs_zero]
        exact mul_nonneg h.A_nonneg (abs_nonneg _)
      · exact h.Qtau z θ τ τ' hz0 hθ.1 hθ.2 hτ hτ'
    have h1 : |(Q z θ τ - Q z θ τ') * R z θ τ| ≤ (A * |τ - τ'|) * B := by
      rw [abs_mul]
      exact mul_le_mul hQtau (abs_R_le hα h hz hθI hτ) (abs_nonneg _)
        (mul_nonneg h.A_nonneg hD0)
    have h2 : |Q z θ τ' * (R z θ τ - R z θ τ')| ≤ A * (B * |τ - τ'| ^ α) := by
      rw [abs_mul]
      exact mul_le_mul (abs_Q_le h hz hθ hτ') (R_tau_mod h hz hθI hτ hτ') (abs_nonneg _)
        h.A_nonneg
    have h3 := abs_add_le ((Q z θ τ - Q z θ τ') * R z θ τ)
      (Q z θ τ' * (R z θ τ - R z θ τ'))
    have h4 : (A * |τ - τ'|) * B + A * (B * |τ - τ'| ^ α)
        = A * B * |τ - τ'| + A * B * |τ - τ'| ^ α := by ring
    linarith [h3, h1, h2, h4]
  refine le_trans (le_min hsup hcrude) ?_
  have hmin := Paux_min_le_two_mul_rpow hAB hD0 hα hα1
  have h5 : 2 * (A * B) * |τ - τ'| ^ α = 2 * A * B * |τ - τ'| ^ α := by ring
  linarith [hmin, h5]

end Work.FTS_RegExport.RXR5L
