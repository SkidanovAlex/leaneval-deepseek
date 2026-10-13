/-
# `Work.FTS_RegExport.RXT.st1_fb_theta` — fallback proof of the uniform `θ`-modulus engine

`Γ(θ) = (sinθ cos²θ)^α`.  Every `u` differentiable on `(0,π/2)` with `|u'| ≤ C·Γ/sin 2θ` there and
`|u| ≤ K·Γ` on `Iθ = [0,π/2]` is `α`-Hölder on `Iθ`, with a constant `L = L(α,C,K)` that does not
depend on `u`.

Route.  With `M`, `N` from `R4b.primBoundLeft` / `primBoundRight` one has the single global bound
`Γ(θ)/sin 2θ ≤ M·θ^{α-1} + N·(π/2-θ)^{2α-1}` on `(0,π/2)` (each summand dominates on its own half
of the interval and both are nonnegative), so for `0 < θ < θ' < π/2` the FTC gives

  `|u θ' - u θ| ≤ C·M·(θ'^α - θ^α)/α + C·N·((π/2-θ)^{2α} - (π/2-θ')^{2α})/(2α)`

and both differences are `≤ (θ'-θ)^α` resp. `≤ (π/2)^α·(θ'-θ)^α`; the two endpoint cases
(`θ = 0`, `θ' = π/2`) are read off the value bound using `Γ(θ) ≤ θ^α` and
`Γ(θ) ≤ (π/2)^α(π/2-θ)^α`.  (The hypothesis `α ≤ 1/3` is used only through `2α ≤ 1` in the
subadditivity of `t ↦ t^{2α}`.)
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Submission.Work.FTS.RegPkgGal.R4d.van_global
import Submission.Work.FTS.RegPkgGal.R4b.van_of_dthvan

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open Set Filter MeasureTheory
open scoped Real Topology

namespace Work.FTS_RegExport.RXT

/-- `Γ(θ) ≤ θ^α` on `Iθ`. -/
theorem fb_Gamma_le_self {α θ : ℝ} (hα : 0 < α) (hθ : θ ∈ Work.Spaces.Iθ) :
    Work.FTS.Regularity.Gamma α θ ≤ θ ^ α := by
  have hsin0 : 0 ≤ Real.sin θ :=
    Real.sin_nonneg_of_mem_Icc ⟨hθ.1, by linarith [hθ.2, Real.pi_pos]⟩
  have hcos2 : Real.cos θ ^ 2 ≤ 1 := by
    nlinarith [Real.sin_sq_add_cos_sq θ, sq_nonneg (Real.sin θ)]
  have hnn : 0 ≤ Real.sin θ * Real.cos θ ^ 2 := mul_nonneg hsin0 (sq_nonneg _)
  have hle : Real.sin θ * Real.cos θ ^ 2 ≤ θ := by
    have h1 : Real.sin θ * Real.cos θ ^ 2 ≤ Real.sin θ * 1 :=
      mul_le_mul_of_nonneg_left hcos2 hsin0
    have h2 : Real.sin θ ≤ θ := Real.sin_le hθ.1
    linarith
  have hG : Work.FTS.Regularity.Gamma α θ = (Real.sin θ * Real.cos θ ^ 2) ^ α := rfl
  rw [hG]
  exact Real.rpow_le_rpow hnn hle hα.le

/-- `Γ(θ) ≤ (π/2)^α·(π/2-θ)^α` on `Iθ`. -/
theorem fb_Gamma_le_endpoint {α θ : ℝ} (hα : 0 < α) (hθ : θ ∈ Work.Spaces.Iθ) :
    Work.FTS.Regularity.Gamma α θ ≤ (Real.pi / 2) ^ α * (Real.pi / 2 - θ) ^ α := by
  set y : ℝ := Real.pi / 2 - θ with hy
  have hy0 : 0 ≤ y := by rw [hy]; linarith [hθ.2, Real.pi_pos]
  have hyhalf : y ≤ Real.pi / 2 := by rw [hy]; linarith [hθ.1]
  have hsin0 : 0 ≤ Real.sin θ :=
    Real.sin_nonneg_of_mem_Icc ⟨hθ.1, by linarith [hθ.2, Real.pi_pos]⟩
  have hcos0 : 0 ≤ Real.cos θ := Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos], hθ.2⟩
  have hcosy : Real.cos θ = Real.sin y := by
    rw [hy]; exact (Real.sin_pi_div_two_sub θ).symm
  have h1 : Work.FTS.Regularity.Gamma α θ ≤ (Real.cos θ ^ 2) ^ α := by
    have hG : Work.FTS.Regularity.Gamma α θ = (Real.sin θ * Real.cos θ ^ 2) ^ α := rfl
    rw [hG]
    refine Real.rpow_le_rpow (mul_nonneg hsin0 (sq_nonneg _)) ?_ hα.le
    have hsin1 : Real.sin θ ≤ 1 := Real.sin_le_one θ
    nlinarith [sq_nonneg (Real.cos θ), hsin0]
  have h2 : (Real.cos θ ^ 2) ^ α = Real.sin y ^ (2 * α) := by
    have ha : (Real.cos θ ^ 2) ^ α = Real.cos θ ^ (((2:ℕ):ℝ) * α) := by
      rw [← Real.rpow_natCast (Real.cos θ) 2, ← Real.rpow_mul hcos0]
    rw [ha, show ((2:ℕ):ℝ) * α = 2 * α by norm_num, hcosy]
  have h3 : Real.sin y ^ (2 * α) ≤ y ^ (2 * α) :=
    Real.rpow_le_rpow (Real.sin_nonneg_of_mem_Icc ⟨hy0, by linarith [Real.pi_pos]⟩)
      (Real.sin_le hy0) (by positivity)
  have h4 : y ^ (2 * α) = (y * y) ^ α := by
    have ha : y ^ (2 * α) = (y ^ (2:ℝ)) ^ α := Real.rpow_mul hy0 2 α
    rw [ha, show y ^ (2:ℝ) = y * y by rw [Real.rpow_two]; ring]
  have h5 : (y * y) ^ α ≤ (y * (Real.pi / 2)) ^ α := by
    refine Real.rpow_le_rpow (mul_nonneg hy0 hy0) ?_ hα.le
    nlinarith [hy0, hyhalf]
  have h6 : (y * (Real.pi / 2)) ^ α = y ^ α * (Real.pi / 2) ^ α :=
    Real.mul_rpow hy0 (by linarith [Real.pi_pos])
  calc Work.FTS.Regularity.Gamma α θ ≤ (Real.cos θ ^ 2) ^ α := h1
    _ = Real.sin y ^ (2 * α) := h2
    _ ≤ y ^ (2 * α) := h3
    _ = (y * y) ^ α := h4
    _ ≤ (y * (Real.pi / 2)) ^ α := h5
    _ = y ^ α * (Real.pi / 2) ^ α := h6
    _ = (Real.pi / 2) ^ α * (Real.pi / 2 - θ) ^ α := by rw [hy]; ring

/-- `Γ(θ)/sin 2θ ≤ M·θ^{α-1} + N·(π/2-θ)^{2α-1}` on `(0,π/2)`, with the two rates of `R4b`. -/
theorem fb_density_le {α M N : ℝ} (hM0 : 0 ≤ M) (hN0 : 0 ≤ N)
    (hM : ∀ t : ℝ, 0 < t → t ≤ Real.pi / 4 →
      Work.FTS.Regularity.Gamma α t / Real.sin (2 * t) ≤ M * t ^ (α - 1))
    (hN : ∀ t : ℝ, Real.pi / 4 ≤ t → t < Real.pi / 2 →
      Work.FTS.Regularity.Gamma α t / Real.sin (2 * t) ≤ N * (Real.pi / 2 - t) ^ (2 * α - 1))
    {x : ℝ} (hx0 : 0 < x) (hx1 : x < Real.pi / 2) :
    Work.FTS.Regularity.Gamma α x / Real.sin (2 * x)
      ≤ M * x ^ (α - 1) + N * (Real.pi / 2 - x) ^ (2 * α - 1) := by
  rcases le_or_gt x (Real.pi / 4) with hxle | hxgt
  · have h1 := hM x hx0 hxle
    have h2 : 0 ≤ N * (Real.pi / 2 - x) ^ (2 * α - 1) :=
      mul_nonneg hN0 (Real.rpow_nonneg (by linarith) _)
    linarith
  · have h1 := hN x (le_of_lt hxgt) hx1
    have h2 : 0 ≤ M * x ^ (α - 1) := mul_nonneg hM0 (Real.rpow_nonneg hx0.le _)
    linarith

theorem theta_modulus_uniform_fb {α C K : ℝ} (hα : 0 < α) (hα13 : α ≤ 1 / 3) (hC : 0 ≤ C)
    (hK : 0 ≤ K) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ ⦃u u' : ℝ → ℝ⦄,
      (∀ x ∈ Set.Ioo (0:ℝ) (Real.pi / 2), HasDerivAt u (u' x) x) →
      (∀ x ∈ Set.Ioo (0:ℝ) (Real.pi / 2),
        |u' x| ≤ C * (Work.FTS.Regularity.Gamma α x / Real.sin (2 * x))) →
      (∀ x ∈ Work.Spaces.Iθ, |u x| ≤ K * Work.FTS.Regularity.Gamma α x) →
      ∀ θ ∈ Work.Spaces.Iθ, ∀ θ' ∈ Work.Spaces.Iθ, |u θ - u θ'| ≤ L * |θ - θ'| ^ α := by
  have hα1 : α ≤ 1 := by linarith
  have hα2 : 2 * α ≤ 1 := by linarith
  obtain ⟨M, hM0, hM⟩ := Work.FTS.RegPkgGal.R4b.primBoundLeft hα
  obtain ⟨N, hN0, hN⟩ := Work.FTS.RegPkgGal.R4b.primBoundRight hα
  set P : ℝ := (Real.pi / 2) ^ α with hP
  have hP0 : 0 ≤ P := by rw [hP]; positivity
  have hD0 : 0 ≤ (C * M + C * N * P) / α :=
    div_nonneg (add_nonneg (mul_nonneg hC hM0) (mul_nonneg (mul_nonneg hC hN0) hP0)) hα.le
  have hKP0 : 0 ≤ K * P := mul_nonneg hK hP0
  set L : ℝ := K + K * P + (C * M + C * N * P) / α with hL
  have hL0 : 0 ≤ L := by rw [hL]; linarith
  refine ⟨L, hL0, ?_⟩
  intro u u' hderiv hbd hval
  have hKL : K ≤ L := by rw [hL]; linarith
  have hKP : K * P ≤ L := by rw [hL]; linarith
  have hCD : ∀ T : ℝ, 0 ≤ T → C * (M * (T / α) + N * (P * T / (2 * α))) ≤ L * T := by
    intro T hT
    have hstep : C * (M * (T / α) + N * (P * T / (2 * α)))
        = (C * M * T + C * N * P * T / 2) / α := by
      field_simp
    have hLα : L * α = (K + K * P) * α + (C * M + C * N * P) := by
      rw [hL]; field_simp
    have hCNPT : 0 ≤ C * N * P * T := mul_nonneg (mul_nonneg (mul_nonneg hC hN0) hP0) hT
    have h1 : C * M * T + C * N * P * T / 2 ≤ (C * M + C * N * P) * T := by
      nlinarith [hCNPT]
    have h3 : 0 ≤ (K + K * P) * α := mul_nonneg (by linarith) hα.le
    have h4 : (C * M + C * N * P) * T
        ≤ ((K + K * P) * α + (C * M + C * N * P)) * T :=
      mul_le_mul_of_nonneg_right (le_add_of_nonneg_left h3) hT
    have h5 : ((K + K * P) * α + (C * M + C * N * P)) * T = (L * T) * α := by
      rw [← hLα]; ring
    rw [hstep, div_le_iff₀ hα, ← h5]
    linarith
  have key : ∀ a b : ℝ, a ∈ Work.Spaces.Iθ → b ∈ Work.Spaces.Iθ → a ≤ b →
      |u b - u a| ≤ L * (b - a) ^ α := by
    intro a b ha hb hab
    have hba0 : 0 ≤ b - a := sub_nonneg.mpr hab
    rcases eq_or_lt_of_le ha.1 with ha0 | hapos
    · have hz : u 0 = 0 := by
        have h := hval 0 ⟨le_rfl, by linarith [Real.pi_pos]⟩
        have hΓ0 : Work.FTS.Regularity.Gamma α 0 = 0 := by
          have hs : Real.sin (0:ℝ) * Real.cos (0:ℝ) ^ 2 = 0 := by
            rw [Real.sin_zero, Real.cos_zero]; ring
          rw [Work.FTS.Regularity.Gamma, Work.ConstructionInstance.Gamma, hs,
            Real.zero_rpow (ne_of_gt hα)]
        rw [hΓ0, mul_zero] at h
        exact abs_eq_zero.mp (le_antisymm h (abs_nonneg _))
      rw [← ha0, hz, sub_zero, sub_zero]
      have h1 : Work.FTS.Regularity.Gamma α b ≤ b ^ α := fb_Gamma_le_self hα hb
      calc |u b| ≤ K * Work.FTS.Regularity.Gamma α b := hval b hb
        _ ≤ K * b ^ α := mul_le_mul_of_nonneg_left h1 hK
        _ ≤ L * b ^ α := mul_le_mul_of_nonneg_right hKL (Real.rpow_nonneg hb.1 α)
    · rcases eq_or_lt_of_le hb.2 with hbπ | hblt
      · have hz : u (Real.pi / 2) = 0 := by
          have h := hval (Real.pi / 2) ⟨by linarith [Real.pi_pos], le_rfl⟩
          have hΓπ : Work.FTS.Regularity.Gamma α (Real.pi / 2) = 0 := by
            have hs : Real.sin (Real.pi / 2) * Real.cos (Real.pi / 2) ^ 2 = 0 := by
              rw [Real.sin_pi_div_two, Real.cos_pi_div_two]; ring
            rw [Work.FTS.Regularity.Gamma, Work.ConstructionInstance.Gamma, hs,
              Real.zero_rpow (ne_of_gt hα)]
          rw [hΓπ, mul_zero] at h
          exact abs_eq_zero.mp (le_antisymm h (abs_nonneg _))
        rw [hbπ, hz, zero_sub, abs_neg]
        have h1 : Work.FTS.Regularity.Gamma α a ≤ P * (Real.pi / 2 - a) ^ α :=
          fb_Gamma_le_endpoint hα ha
        have h2 : 0 ≤ (Real.pi / 2 - a) ^ α := Real.rpow_nonneg (by linarith [ha.2]) α
        calc |u a| ≤ K * Work.FTS.Regularity.Gamma α a := hval a ha
          _ ≤ K * (P * (Real.pi / 2 - a) ^ α) := mul_le_mul_of_nonneg_left h1 hK
          _ = (K * P) * (Real.pi / 2 - a) ^ α := by ring
          _ ≤ L * (Real.pi / 2 - a) ^ α := mul_le_mul_of_nonneg_right hKP h2
      · have hcont : ContinuousOn u (Set.Icc a b) := by
          have hd : DifferentiableOn ℝ u (Set.Ioo 0 (Real.pi / 2)) :=
            fun x hx => (hderiv x hx).differentiableAt.differentiableWithinAt
          exact hd.continuousOn.mono
            (fun x hx => ⟨lt_of_lt_of_le hapos hx.1, lt_of_le_of_lt hx.2 hblt⟩)
        have hmaj : ∀ x ∈ Set.Ioo a b,
            ‖u' x‖ ≤ C * (M * x ^ (α - 1) + N * (Real.pi / 2 - x) ^ (2 * α - 1)) := by
          intro x hx
          rw [Real.norm_eq_abs]
          have hx0 : 0 < x := lt_trans hapos hx.1
          have hx1 : x < Real.pi / 2 := lt_trans hx.2 hblt
          calc |u' x| ≤ C * (Work.FTS.Regularity.Gamma α x / Real.sin (2 * x)) :=
                hbd x ⟨hx0, hx1⟩
            _ ≤ C * (M * x ^ (α - 1) + N * (Real.pi / 2 - x) ^ (2 * α - 1)) :=
                mul_le_mul_of_nonneg_left (fb_density_le hM0 hN0 hM hN hx0 hx1) hC
        have hMint : IntervalIntegrable (fun x : ℝ => M * x ^ (α - 1)) volume a b :=
          (intervalIntegral.intervalIntegrable_rpow'
            (show (-1:ℝ) < α - 1 by linarith)).const_mul M
        have hNint : IntervalIntegrable
            (fun x : ℝ => N * (Real.pi / 2 - x) ^ (2 * α - 1)) volume a b := by
          have hbase : IntervalIntegrable (fun x : ℝ => x ^ (2 * α - 1)) volume
              (Real.pi / 2 - b) (Real.pi / 2 - a) :=
            intervalIntegral.intervalIntegrable_rpow' (show (-1:ℝ) < 2 * α - 1 by linarith)
          have hcomp := hbase.comp_sub_left (Real.pi / 2)
          rw [show Real.pi / 2 - (Real.pi / 2 - b) = b by ring,
            show Real.pi / 2 - (Real.pi / 2 - a) = a by ring] at hcomp
          exact hcomp.symm.const_mul N
        have hmaj_int : IntervalIntegrable
            (fun x : ℝ => C * (M * x ^ (α - 1) + N * (Real.pi / 2 - x) ^ (2 * α - 1)))
            volume a b := (hMint.add hNint).const_mul C
        have hftc := Work.FTS.RegPkgGal.R4d.abs_sub_le_integral_of_continuousOn hab hcont
          (fun x hx => hderiv x ⟨lt_trans hapos hx.1, lt_trans hx.2 hblt⟩)
          hmaj_int hmaj
        have hint1 : ∫ x in a..b, M * x ^ (α - 1) = M * ((b ^ α - a ^ α) / α) := by
          rw [intervalIntegral.integral_const_mul,
            integral_rpow (Or.inl (show (-1:ℝ) < α - 1 by linarith)),
            show α - 1 + 1 = α by ring]
        have hint2 : ∫ x in a..b, N * (Real.pi / 2 - x) ^ (2 * α - 1)
            = N * (((Real.pi / 2 - a) ^ (2 * α) - (Real.pi / 2 - b) ^ (2 * α)) / (2 * α)) := by
          rw [intervalIntegral.integral_const_mul,
            intervalIntegral.integral_comp_sub_left (fun x : ℝ => x ^ (2 * α - 1)) (Real.pi / 2),
            integral_rpow (Or.inl (show (-1:ℝ) < 2 * α - 1 by linarith)),
            show 2 * α - 1 + 1 = 2 * α by ring]
        have hInt : ∫ x in a..b, C * (M * x ^ (α - 1) + N * (Real.pi / 2 - x) ^ (2 * α - 1))
            = C * (M * ((b ^ α - a ^ α) / α)
              + N * (((Real.pi / 2 - a) ^ (2 * α) - (Real.pi / 2 - b) ^ (2 * α)) / (2 * α))) := by
          rw [intervalIntegral.integral_const_mul,
            intervalIntegral.integral_add hMint hNint, hint1, hint2]
        have hb1 : b ^ α - a ^ α ≤ (b - a) ^ α := by
          have h := Real.rpow_add_le_add_rpow ha.1 hba0 hα.le hα1
          rw [show a + (b - a) = b by ring] at h
          linarith
        have hb2 : (Real.pi / 2 - a) ^ (2 * α) - (Real.pi / 2 - b) ^ (2 * α)
            ≤ P * (b - a) ^ α := by
          have hx0 : 0 ≤ Real.pi / 2 - b := by linarith [hb.2, Real.pi_pos]
          have hsub := Real.rpow_add_le_add_rpow hx0 hba0 (by linarith : (0:ℝ) ≤ 2 * α) hα2
          have hid : Real.pi / 2 - a = (Real.pi / 2 - b) + (b - a) := by ring
          have hmain : (Real.pi / 2 - a) ^ (2 * α)
              ≤ (Real.pi / 2 - b) ^ (2 * α) + (b - a) ^ (2 * α) := by
            rw [hid]; exact hsub
          have hy : (b - a) ^ (2 * α) ≤ (b - a) ^ α * P := by
            have h1 : (b - a) ^ (2 * α) = ((b - a) * (b - a)) ^ α := by
              have ha' : (b - a) ^ (2 * α) = ((b - a) ^ (2:ℝ)) ^ α := Real.rpow_mul hba0 2 α
              rw [ha', show (b - a) ^ (2:ℝ) = (b - a) * (b - a) by rw [Real.rpow_two]; ring]
            rw [h1]
            have h2 : (b - a) * (b - a) ≤ (b - a) * (Real.pi / 2) :=
              mul_le_mul_of_nonneg_left (by linarith [ha.1, hb.2, Real.pi_pos]) hba0
            calc ((b - a) * (b - a)) ^ α ≤ ((b - a) * (Real.pi / 2)) ^ α :=
                  Real.rpow_le_rpow (mul_nonneg hba0 hba0) h2 hα.le
              _ = (b - a) ^ α * P := by
                  rw [Real.mul_rpow hba0 (by linarith [Real.pi_pos]), hP]
          have hT0 : 0 ≤ (b - a) ^ α := Real.rpow_nonneg hba0 α
          linarith
        refine le_trans hftc ?_
        rw [hInt]
        have hstep : C * (M * ((b ^ α - a ^ α) / α)
              + N * (((Real.pi / 2 - a) ^ (2 * α) - (Real.pi / 2 - b) ^ (2 * α)) / (2 * α)))
            ≤ C * (M * ((b - a) ^ α / α) + N * (P * (b - a) ^ α / (2 * α))) := by
          refine mul_le_mul_of_nonneg_left ?_ hC
          have h1 : M * ((b ^ α - a ^ α) / α) ≤ M * ((b - a) ^ α / α) :=
            mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hb1 hα.le) hM0
          have h2 : N * (((Real.pi / 2 - a) ^ (2 * α) - (Real.pi / 2 - b) ^ (2 * α)) / (2 * α))
              ≤ N * (P * (b - a) ^ α / (2 * α)) :=
            mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hb2 (by linarith)) hN0
          linarith
        exact le_trans hstep (hCD ((b - a) ^ α) (Real.rpow_nonneg hba0 α))
  intro θ hθ θ' hθ'
  rcases le_total θ θ' with hle | hle
  · have h := key θ θ' hθ hθ' hle
    have h1 : |θ - θ'| = θ' - θ := by
      rw [abs_sub_comm θ θ', abs_of_nonneg (sub_nonneg.mpr hle)]
    have h2 : |u θ - u θ'| = |u θ' - u θ| := abs_sub_comm _ _
    rw [h1, h2]
    exact h
  · have h := key θ' θ hθ' hθ hle
    have h1 : |θ - θ'| = θ - θ' := abs_of_nonneg (sub_nonneg.mpr hle)
    rw [h1]
    exact h

end Work.FTS_RegExport.RXT
