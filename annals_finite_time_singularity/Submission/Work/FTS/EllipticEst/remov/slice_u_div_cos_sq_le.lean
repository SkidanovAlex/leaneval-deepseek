import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Function.L2Space
import Submission.Work.Spaces.Defs
import Submission.Work.Spaces.cs_integral

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

set_option linter.style.haveILetI false

open MeasureTheory Set Filter
open scoped Real Topology

namespace Work.FTS.EllipticEst.remov

/-- `Real.rpow` and the `^` notation for real exponents are the same operation. -/
private lemma rpow_eq_hpow (x y : ℝ) : Real.rpow x y = x ^ y := rfl

/-- Cauchy–Schwarz for the set integral over a closed interval:
`(∫_{[a,b]} f)² ≤ (b-a) ∫_{[a,b]} f²` for `f` square integrable and a.e. strongly measurable. -/
private lemma sq_setIntegral_Icc_le {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hint : IntegrableOn (fun x => f x ^ 2) (Set.Icc a b))
    (hmeas : AEStronglyMeasurable f (volume.restrict (Set.Icc a b))) :
    (∫ x in Set.Icc a b, f x) ^ 2 ≤ (b - a) * (∫ x in Set.Icc a b, f x ^ 2) := by
  haveI : IsFiniteMeasure (volume.restrict (Set.Icc a b)) :=
    ⟨by rw [Measure.restrict_apply_univ, Real.volume_Icc]; exact ENNReal.ofReal_lt_top⟩
  have hm1 : MemLp (fun _ : ℝ => (1 : ℝ)) 2 (volume.restrict (Set.Icc a b)) := memLp_const 1
  have hmf : MemLp f 2 (volume.restrict (Set.Icc a b)) :=
    (memLp_two_iff_integrable_sq hmeas).mpr hint
  have h := Work.Spaces.cs_integral hm1 hmf
  have h1 : (∫ x in Set.Icc a b, (1 : ℝ) * f x) = ∫ x in Set.Icc a b, f x := by simp
  have h2 : (∫ x in Set.Icc a b, (1 : ℝ) ^ 2) = b - a := by
    rw [one_pow, MeasureTheory.integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le hab, intervalIntegral.integral_const, smul_eq_mul,
      mul_one]
  rw [h1, h2] at h
  exact h

/-- The angular weight bound: for `1 ≤ γ ≤ 3/2` and `θ ∈ (0, π/2)`,
`sin(2θ)^{2-γ}/cos²θ ≤ 2^{2-γ} (π/2)^γ (π/2 - θ)^{-γ}`. -/
private lemma sin2_div_cos_sq_le_aux (γ : ℝ) (hγ1 : 1 ≤ γ) (hγ2 : γ ≤ 3 / 2) :
    ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      (Real.sin (2 * θ)) ^ (2 - γ) / (Real.cos θ) ^ 2
        ≤ (2 ^ (2 - γ) * (Real.pi / 2) ^ γ) * (Real.pi / 2 - θ) ^ (-γ) := by
  intro θ hθ
  have hpi2 : (0 : ℝ) < Real.pi / 2 := Real.pi_div_two_pos
  have hsin : 0 < Real.sin θ :=
    Real.sin_pos_of_pos_of_lt_pi hθ.1 (by linarith [hθ.2, Real.pi_pos])
  have hcos : 0 < Real.cos θ := Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1], hθ.2⟩
  have hbase : 0 < Real.pi / 2 - θ := by linarith [hθ.2]
  have h2γ : (0 : ℝ) ≤ 2 - γ := by linarith
  -- `sin θ ^ (2-γ) ≤ 1`
  have hsin1 : (Real.sin θ) ^ (2 - γ) ≤ 1 :=
    Real.rpow_le_one hsin.le (Real.sin_le_one θ) h2γ
  -- `cos θ ^ (2-γ) = cos²θ * cos θ ^ (-γ)`
  have hsplit : (Real.cos θ) ^ (2 - γ) = (Real.cos θ) ^ 2 * (Real.cos θ) ^ (-γ) := by
    have h : (Real.cos θ) ^ (2 + (-γ)) = (Real.cos θ) ^ (2 : ℝ) * (Real.cos θ) ^ (-γ) :=
      Real.rpow_add hcos 2 (-γ)
    have h' : (2 : ℝ) + (-γ) = 2 - γ := by ring
    have h2 : (Real.cos θ) ^ (2 : ℝ) = (Real.cos θ) ^ 2 := Real.rpow_two _
    rw [h', h2] at h
    exact h
  -- Jordan's inequality: `π/2 - θ ≤ (π/2) cos θ`
  have hjordan : Real.pi / 2 - θ ≤ Real.pi / 2 * Real.cos θ := by
    have h := Real.mul_le_sin hbase.le (by linarith [hθ.1])
    rw [Real.sin_pi_div_two_sub] at h
    have h2 := mul_le_mul_of_nonneg_left h hpi2.le
    have h3 : Real.pi / 2 * (2 / Real.pi * (Real.pi / 2 - θ)) = Real.pi / 2 - θ := by
      field_simp
    linarith [h2, h3]
  -- `cos θ ^ (-γ) ≤ (π/2)^γ (π/2-θ)^(-γ)`
  have hcos_bound : (Real.cos θ) ^ (-γ)
      ≤ (Real.pi / 2) ^ γ * (Real.pi / 2 - θ) ^ (-γ) := by
    have h1 : (Real.pi / 2) ^ (-γ) * (Real.cos θ) ^ (-γ) ≤ (Real.pi / 2 - θ) ^ (-γ) := by
      have h2 : (Real.pi / 2 * Real.cos θ) ^ (-γ)
          = (Real.pi / 2) ^ (-γ) * (Real.cos θ) ^ (-γ) := Real.mul_rpow hpi2.le hcos.le
      rw [← h2]
      exact Real.rpow_le_rpow_of_nonpos hbase hjordan (by linarith : -γ ≤ (0 : ℝ))
    have h4 : 0 < (Real.pi / 2) ^ γ := Real.rpow_pos_of_pos hpi2 γ
    have h5 : (Real.pi / 2) ^ γ * (Real.pi / 2) ^ (-γ) = 1 := by
      have h6 : (Real.pi / 2) ^ (γ + (-γ)) = (Real.pi / 2) ^ γ * (Real.pi / 2) ^ (-γ) :=
        Real.rpow_add hpi2 γ (-γ)
      have hz : (Real.pi / 2) ^ (0 : ℝ) = 1 := Real.rpow_zero _
      rw [show γ + (-γ) = (0 : ℝ) by ring, hz] at h6
      exact h6.symm
    calc (Real.cos θ) ^ (-γ)
        = ((Real.pi / 2) ^ γ * (Real.pi / 2) ^ (-γ)) * (Real.cos θ) ^ (-γ) := by
            rw [h5, one_mul]
      _ = (Real.pi / 2) ^ γ * ((Real.pi / 2) ^ (-γ) * (Real.cos θ) ^ (-γ)) := by ring
      _ ≤ (Real.pi / 2) ^ γ * (Real.pi / 2 - θ) ^ (-γ) := mul_le_mul_of_nonneg_left h1 h4.le
  rw [div_le_iff₀ (pow_pos hcos 2)]
  calc (Real.sin (2 * θ)) ^ (2 - γ)
      = (2 * Real.sin θ * Real.cos θ) ^ (2 - γ) := by rw [Real.sin_two_mul]
    _ = (2 * Real.sin θ) ^ (2 - γ) * (Real.cos θ) ^ (2 - γ) :=
          Real.mul_rpow (by positivity) hcos.le
    _ = (2 ^ (2 - γ) * (Real.sin θ) ^ (2 - γ)) * (Real.cos θ) ^ (2 - γ) := by
          rw [show (2 * Real.sin θ) ^ (2 - γ)
              = 2 ^ (2 - γ) * (Real.sin θ) ^ (2 - γ) from
            Real.mul_rpow (by norm_num) hsin.le]
    _ ≤ (2 ^ (2 - γ) * 1) * (Real.cos θ) ^ (2 - γ) :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hsin1 (Real.rpow_nonneg (by norm_num) _))
            (Real.rpow_nonneg hcos.le _)
    _ = (2 ^ (2 - γ) * 1) * ((Real.cos θ) ^ 2 * (Real.cos θ) ^ (-γ)) := by rw [hsplit]
    _ ≤ (2 ^ (2 - γ) * 1) * ((Real.cos θ) ^ 2 *
          ((Real.pi / 2) ^ γ * (Real.pi / 2 - θ) ^ (-γ))) := by
          refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hcos_bound ?_)
            (le_of_lt (mul_pos (Real.rpow_pos_of_pos (by norm_num) _) one_pos))
          positivity
    _ = (2 ^ (2 - γ) * (Real.pi / 2) ^ γ) * (Real.pi / 2 - θ) ^ (-γ) * (Real.cos θ) ^ 2 := by
          ring

/-- Integrability of `θ ↦ (π/2 - θ)^{1-γ}` on `Iθ = [0, π/2]` for `γ < 2`. -/
private lemma integrableOn_pi_sub_rpow_aux {γ : ℝ} (hγ : γ < 2) :
    IntegrableOn (fun θ => (Real.pi / 2 - θ) ^ (1 - γ)) Work.Spaces.Iθ := by
  have hle : (0 : ℝ) ≤ Real.pi / 2 := by positivity
  rw [Work.Spaces.Iθ, ← intervalIntegrable_iff_integrableOn_Icc_of_le hle]
  have hbase : IntervalIntegrable (fun x : ℝ => x ^ (1 - γ)) volume (Real.pi / 2) 0 :=
    intervalIntegral.intervalIntegrable_rpow' (by linarith : (-1 : ℝ) < 1 - γ)
  have h := (IntervalIntegrable.comp_sub_left_iff (f := fun x : ℝ => x ^ (1 - γ))
    (a := Real.pi / 2) (b := 0) (Real.pi / 2)).mpr hbase
  simpa using h

/-- The value of `∫_{Iθ} (π/2 - θ)^{1-γ}` for `γ < 2`. -/
private lemma integral_pi_sub_rpow_aux {γ : ℝ} (hγ : γ < 2) :
    (∫ θ in Work.Spaces.Iθ, (Real.pi / 2 - θ) ^ (1 - γ))
      = (Real.pi / 2) ^ (2 - γ) / (2 - γ) := by
  have hle : (0 : ℝ) ≤ Real.pi / 2 := by positivity
  rw [Work.Spaces.Iθ, MeasureTheory.integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le hle]
  rw [intervalIntegral.integral_comp_sub_left (fun x : ℝ => x ^ (1 - γ)) (Real.pi / 2)]
  rw [show Real.pi / 2 - Real.pi / 2 = (0 : ℝ) by ring,
    show Real.pi / 2 - 0 = Real.pi / 2 by ring]
  have h := integral_rpow (a := (0 : ℝ)) (b := Real.pi / 2) (r := 1 - γ)
    (Or.inl (by linarith : (-1 : ℝ) < 1 - γ))
  have hz : (0 : ℝ) ^ (2 - γ) = 0 := Real.zero_rpow (by linarith : (2 : ℝ) - γ ≠ 0)
  rw [show (1 : ℝ) - γ + 1 = 2 - γ by ring, hz, sub_zero] at h
  exact h

/-- Fundamental theorem of calculus for a slice with the regularity hypotheses of the main
theorem: `u θ = -∫_θ^{π/2} deriv u` for `θ ∈ Iθ`, and `deriv u` is integrable on `Iθ`. -/
private lemma slice_ftc_aux {u : ℝ → ℝ}
    (hC3 : ContDiffOn ℝ 3 u (Set.Ioo 0 (Real.pi / 2)))
    (hcont : ContinuousOn u (Set.Icc 0 (Real.pi / 2)))
    (hpi : u (Real.pi / 2) = 0)
    (hint : IntegrableOn (fun θ => (deriv u θ) ^ 2) Work.Spaces.Iθ) :
    IntegrableOn (deriv u) Work.Spaces.Iθ ∧
      ∀ θ ∈ Work.Spaces.Iθ, u θ = -∫ s in θ..(Real.pi / 2), deriv u s := by
  have hIθ_ne_top : volume Work.Spaces.Iθ ≠ ⊤ := by
    rw [Work.Spaces.Iθ, Real.volume_Icc]
    exact ENNReal.ofReal_ne_top
  have hInt1 : IntegrableOn (fun _ : ℝ => (1 : ℝ)) Work.Spaces.Iθ :=
    integrableOn_const hIθ_ne_top
  have hdom : IntegrableOn (fun θ => (1 : ℝ) + (deriv u θ) ^ 2) Work.Spaces.Iθ := hInt1.add hint
  have hderivInt : IntegrableOn (deriv u) Work.Spaces.Iθ := by
    refine Integrable.mono' hdom (measurable_deriv u).aestronglyMeasurable ?_
    filter_upwards with x
    rw [Real.norm_eq_abs]
    nlinarith [abs_nonneg (deriv u x), sq_abs (deriv u x), sq_nonneg (|deriv u x| - 1 / 2)]
  constructor
  · exact hderivInt
  · intro θ hθ
    have hsub : Set.Icc θ (Real.pi / 2) ⊆ Work.Spaces.Iθ :=
      fun x hx => ⟨le_trans hθ.1 hx.1, hx.2⟩
    have hint' : IntegrableOn (deriv u) (Set.Icc θ (Real.pi / 2)) := hderivInt.mono_set hsub
    have hint'' : IntervalIntegrable (deriv u) volume θ (Real.pi / 2) :=
      (intervalIntegrable_iff_integrableOn_Icc_of_le hθ.2).mpr hint'
    have hderiv : ∀ x ∈ Set.Ioo θ (Real.pi / 2), HasDerivAt u (deriv u x) x := by
      intro x hx
      have hx' : x ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := ⟨lt_of_le_of_lt hθ.1 hx.1, hx.2⟩
      exact ((hC3.differentiableOn (by norm_num)).differentiableAt
        (isOpen_Ioo.mem_nhds hx')).hasDerivAt
    have hcont' : ContinuousOn u (Set.Icc θ (Real.pi / 2)) :=
      hcont.mono fun x hx => ⟨le_trans hθ.1 hx.1, hx.2⟩
    have hftc :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hθ.2 hcont' hderiv hint''
    rw [hpi, zero_sub] at hftc
    rw [hftc]
    ring

theorem slice_u_div_cos_sq_le (γ : ℝ) (hγ1 : 1 ≤ γ) (hγ2 : γ ≤ 3 / 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ u : ℝ → ℝ,
      ContDiffOn ℝ 3 u (Set.Ioo 0 (Real.pi / 2)) →
      ContinuousOn u (Set.Icc 0 (Real.pi / 2)) →
      u 0 = 0 → u (Real.pi / 2) = 0 →
      MeasureTheory.IntegrableOn (fun θ => (deriv u θ) ^ 2) Work.Spaces.Iθ →
      MeasureTheory.IntegrableOn (fun θ => (u θ) ^ 2) Work.Spaces.Iθ →
      (MeasureTheory.IntegrableOn (fun θ => (u θ / Real.cos θ) ^ 2 *
          Real.rpow (Real.sin (2 * θ)) (2 - γ)) Work.Spaces.Iθ ∧
        (∫ θ in Work.Spaces.Iθ, (u θ / Real.cos θ) ^ 2 *
            Real.rpow (Real.sin (2 * θ)) (2 - γ))
          ≤ C * ((∫ θ in Work.Spaces.Iθ, (deriv u θ) ^ 2)
              + (∫ θ in Work.Spaces.Iθ, (u θ) ^ 2))) := by
  simp only [rpow_eq_hpow]
  have hγ2' : γ < 2 := by linarith
  have h2γ : (0 : ℝ) ≤ 2 - γ := by linarith
  set M : ℝ := 2 ^ (2 - γ) * (Real.pi / 2) ^ γ with hM
  have hMpos : 0 < M := by
    rw [hM]
    exact mul_pos (Real.rpow_pos_of_pos (by norm_num) _)
      (Real.rpow_pos_of_pos (by positivity) _)
  have hCpos : 0 < 1 + M * Real.pi := by
    have h := mul_pos hMpos Real.pi_pos
    linarith
  refine ⟨1 + M * Real.pi, hCpos, ?_⟩
  intro u hC3 hcont hu0 hpi hIntd hIntu
  set A : ℝ := ∫ θ in Work.Spaces.Iθ, (deriv u θ) ^ 2 with hA
  set B : ℝ := ∫ θ in Work.Spaces.Iθ, (u θ) ^ 2 with hB
  have hA0 : 0 ≤ A := by rw [hA]; exact integral_nonneg fun θ => sq_nonneg _
  have hB0 : 0 ≤ B := by rw [hB]; exact integral_nonneg fun θ => sq_nonneg _
  obtain ⟨hderivInt, hftc⟩ := slice_ftc_aux hC3 hcont hpi hIntd
  -- pointwise bound for `u²`
  have hu_sq : ∀ θ ∈ Work.Spaces.Iθ, (u θ) ^ 2 ≤ (Real.pi / 2 - θ) * A := by
    intro θ hθ
    have hsub : Set.Icc θ (Real.pi / 2) ⊆ Work.Spaces.Iθ :=
      fun x hx => ⟨le_trans hθ.1 hx.1, hx.2⟩
    have hint' : IntegrableOn (fun x => (deriv u x) ^ 2) (Set.Icc θ (Real.pi / 2)) :=
      hIntd.mono_set hsub
    have hmeas' : AEStronglyMeasurable (deriv u)
        (volume.restrict (Set.Icc θ (Real.pi / 2))) :=
      (measurable_deriv u).aestronglyMeasurable
    have hcs := sq_setIntegral_Icc_le (f := deriv u) (a := θ) (b := Real.pi / 2) hθ.2 hint' hmeas'
    have e1 : (∫ s in θ..(Real.pi / 2), deriv u s) = ∫ s in Set.Icc θ (Real.pi / 2), deriv u s := by
      rw [intervalIntegral.integral_of_le hθ.2, MeasureTheory.integral_Icc_eq_integral_Ioc]
    have hu2 : (u θ) ^ 2 = (∫ s in Set.Icc θ (Real.pi / 2), deriv u s) ^ 2 := by
      rw [hftc θ hθ, e1]
      ring
    rw [hu2]
    refine le_trans hcs (mul_le_mul_of_nonneg_left ?_ (by linarith [hθ.2]))
    exact setIntegral_mono_set hIntd (Eventually.of_forall fun x => sq_nonneg _)
      (Eventually.of_forall fun x hx => hsub hx)
  -- pointwise bound for the integrand on the interior
  have hweight := sin2_div_cos_sq_le_aux γ hγ1 hγ2
  have key_int : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      (u θ / Real.cos θ) ^ 2 * (Real.sin (2 * θ)) ^ (2 - γ)
        ≤ M * A * (Real.pi / 2 - θ) ^ (1 - γ) := by
    intro θ hθ
    have hcos : 0 < Real.cos θ := Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩
    have hbase : 0 < Real.pi / 2 - θ := by linarith [hθ.2]
    have hwb := hweight θ hθ
    have hstep1 : (u θ / Real.cos θ) ^ 2 * (Real.sin (2 * θ)) ^ (2 - γ)
        ≤ (u θ) ^ 2 * (M * (Real.pi / 2 - θ) ^ (-γ)) := by
      have hfac : (u θ / Real.cos θ) ^ 2 * (Real.sin (2 * θ)) ^ (2 - γ)
          = (u θ) ^ 2 * ((Real.sin (2 * θ)) ^ (2 - γ) / (Real.cos θ) ^ 2) := by
        rw [div_pow]
        ring
      rw [hfac]
      exact mul_le_mul_of_nonneg_left hwb (sq_nonneg _)
    have hstep2 : (u θ) ^ 2 * (M * (Real.pi / 2 - θ) ^ (-γ))
        ≤ M * ((Real.pi / 2 - θ) * A) * (Real.pi / 2 - θ) ^ (-γ) := by
      have hw : 0 ≤ (Real.pi / 2 - θ) ^ (-γ) := Real.rpow_nonneg hbase.le _
      have hu := mul_le_mul_of_nonneg_right (hu_sq θ ⟨hθ.1.le, hθ.2.le⟩) hw
      calc (u θ) ^ 2 * (M * (Real.pi / 2 - θ) ^ (-γ))
          = M * ((u θ) ^ 2 * (Real.pi / 2 - θ) ^ (-γ)) := by ring
        _ ≤ M * (((Real.pi / 2 - θ) * A) * (Real.pi / 2 - θ) ^ (-γ)) :=
              mul_le_mul_of_nonneg_left hu hMpos.le
        _ = M * ((Real.pi / 2 - θ) * A) * (Real.pi / 2 - θ) ^ (-γ) := by ring
    have hstep3 : M * ((Real.pi / 2 - θ) * A) * (Real.pi / 2 - θ) ^ (-γ)
        = M * A * (Real.pi / 2 - θ) ^ (1 - γ) := by
      have h1 : (Real.pi / 2 - θ) * (Real.pi / 2 - θ) ^ (-γ)
          = (Real.pi / 2 - θ) ^ (1 - γ) := by
        have h := Real.rpow_add hbase (1 : ℝ) (-γ)
        have h' : (1 : ℝ) + (-γ) = 1 - γ := by ring
        rw [h', Real.rpow_one] at h
        exact h.symm
      rw [← h1]
      ring
    exact le_trans hstep1 (le_trans hstep2 (le_of_eq hstep3))
  -- the pointwise bound on all of `Iθ`
  have hpt : ∀ θ ∈ Work.Spaces.Iθ,
      (u θ / Real.cos θ) ^ 2 * (Real.sin (2 * θ)) ^ (2 - γ)
        ≤ M * A * (Real.pi / 2 - θ) ^ (1 - γ) := by
    intro θ hθ
    have hRHS0 : 0 ≤ M * A * (Real.pi / 2 - θ) ^ (1 - γ) :=
      mul_nonneg (mul_nonneg hMpos.le hA0) (Real.rpow_nonneg (by linarith [hθ.2]) _)
    rcases lt_trichotomy θ 0 with hlt | heq | hgt
    · exact absurd hθ.1 (not_le.mpr hlt)
    · subst heq
      have hs : Real.sin (2 * 0) = 0 := by simp
      have hz : (0 : ℝ) ^ (2 - γ) = 0 := Real.zero_rpow (by linarith : (2 : ℝ) - γ ≠ 0)
      have hzero : (u 0 / Real.cos 0) ^ 2 * (Real.sin (2 * 0)) ^ (2 - γ) = 0 := by
        rw [hu0, hs, hz]
        simp
      rw [hzero]
      simpa using hRHS0
    · rcases lt_trichotomy θ (Real.pi / 2) with h2 | heq2 | hgt2
      · exact key_int θ ⟨hgt, h2⟩
      · subst heq2
        have hs : Real.sin (2 * (Real.pi / 2)) = 0 := by
          rw [show 2 * (Real.pi / 2) = Real.pi by ring, Real.sin_pi]
        have hz : (0 : ℝ) ^ (2 - γ) = 0 := Real.zero_rpow (by linarith : (2 : ℝ) - γ ≠ 0)
        have hzero : (u (Real.pi / 2) / Real.cos (Real.pi / 2)) ^ 2 *
            (Real.sin (2 * (Real.pi / 2))) ^ (2 - γ) = 0 := by
          rw [hpi, hs, hz]
          simp
        rw [hzero]
        simpa using hRHS0
      · exact absurd hθ.2 (not_le.mpr hgt2)
  -- integrability of the dominating function
  have hIntW : IntegrableOn (fun θ => (Real.pi / 2 - θ) ^ (1 - γ)) Work.Spaces.Iθ :=
    integrableOn_pi_sub_rpow_aux hγ2'
  have hdomInt : Integrable (fun θ => M * A * (Real.pi / 2 - θ) ^ (1 - γ))
      (volume.restrict Work.Spaces.Iθ) :=
    Integrable.const_mul hIntW (M * A)
  -- integrability of the integrand
  have hIθ_meas : MeasurableSet Work.Spaces.Iθ := by
    rw [Work.Spaces.Iθ]
    exact measurableSet_Icc
  have hGint : Integrable (fun θ => (u θ / Real.cos θ) ^ 2 *
      (Real.sin (2 * θ)) ^ (2 - γ)) (volume.restrict Work.Spaces.Iθ) := by
    refine Integrable.mono' hdomInt ?_ ?_
    · have hu_meas : AEStronglyMeasurable u (volume.restrict Work.Spaces.Iθ) :=
        hcont.aestronglyMeasurable hIθ_meas
      have hcos_meas : AEStronglyMeasurable (fun θ : ℝ => Real.cos θ)
          (volume.restrict Work.Spaces.Iθ) :=
        Real.measurable_cos.aestronglyMeasurable
      have hdiv : AEStronglyMeasurable (fun θ : ℝ => u θ / Real.cos θ)
          (volume.restrict Work.Spaces.Iθ) :=
        (hu_meas.aemeasurable.div hcos_meas.aemeasurable).aestronglyMeasurable
      have hsin_cont : Continuous (fun θ : ℝ => (Real.sin (2 * θ)) ^ (2 - γ)) :=
        (Real.continuous_sin.comp (continuous_const.mul continuous_id)).rpow_const
          (fun x => Or.inr h2γ)
      exact (hdiv.pow 2).mul hsin_cont.aestronglyMeasurable
    · filter_upwards [MeasureTheory.ae_restrict_mem hIθ_meas] with θ hθmem
      have hg0 : 0 ≤ (u θ / Real.cos θ) ^ 2 * (Real.sin (2 * θ)) ^ (2 - γ) := by
        refine mul_nonneg (sq_nonneg _) (Real.rpow_nonneg ?_ _)
        exact Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθmem.1])
          (by linarith [hθmem.2, Real.pi_pos])
      rw [Real.norm_eq_abs, abs_of_nonneg hg0]
      exact hpt θ hθmem
  have hG_le : (∫ θ in Work.Spaces.Iθ, (u θ / Real.cos θ) ^ 2 * (Real.sin (2 * θ)) ^ (2 - γ))
      ≤ ∫ θ in Work.Spaces.Iθ, M * A * (Real.pi / 2 - θ) ^ (1 - γ) :=
    integral_mono_ae hGint hdomInt (by
      filter_upwards [MeasureTheory.ae_restrict_mem hIθ_meas] with θ hθmem
      exact hpt θ hθmem)
  have hval : (∫ θ in Work.Spaces.Iθ, M * A * (Real.pi / 2 - θ) ^ (1 - γ))
      = M * A * ((Real.pi / 2) ^ (2 - γ) / (2 - γ)) := by
    rw [integral_const_mul, integral_pi_sub_rpow_aux hγ2']
  have hnum : M * A * ((Real.pi / 2) ^ (2 - γ) / (2 - γ)) ≤ M * A * Real.pi := by
    apply mul_le_mul_of_nonneg_left _ (mul_nonneg hMpos.le hA0)
    have hP : (Real.pi / 2) ^ (2 - γ) ≤ Real.pi / 2 := by
      have h := Real.rpow_le_rpow_of_exponent_le (x := Real.pi / 2) (y := 2 - γ) (z := 1)
        Real.one_le_pi_div_two (by linarith)
      rw [Real.rpow_one] at h
      exact h
    have hden : 0 < 2 - γ := by linarith
    have hinv : (2 - γ)⁻¹ ≤ 2 := by
      rw [inv_le_iff_one_le_mul₀ hden, mul_comm]
      linarith
    calc (Real.pi / 2) ^ (2 - γ) / (2 - γ)
        = (Real.pi / 2) ^ (2 - γ) * (2 - γ)⁻¹ := by rw [div_eq_mul_inv]
      _ ≤ (Real.pi / 2) * 2 := mul_le_mul hP hinv (by positivity) (by positivity)
      _ = Real.pi := by ring
  have hfin : M * A * Real.pi ≤ (1 + M * Real.pi) * (A + B) := by
    have hMpi : 0 < M * Real.pi := mul_pos hMpos Real.pi_pos
    have hc : M * Real.pi ≤ 1 + M * Real.pi := by linarith
    calc M * A * Real.pi = (M * Real.pi) * A := by ring
      _ ≤ (1 + M * Real.pi) * A := mul_le_mul_of_nonneg_right hc hA0
      _ ≤ (1 + M * Real.pi) * (A + B) :=
            mul_le_mul_of_nonneg_left (by linarith [hB0]) (by linarith)
  exact ⟨hGint, le_trans hG_le (le_trans (le_of_eq hval) (le_trans hnum hfin))⟩

end Work.FTS.EllipticEst.remov
