import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Order.CompletePartialOrder
import Submission.Work.Spaces.Defs
import Submission.Work.Elliptic.Defs
import Submission.Work.FTS.EllipticEst.resid_expansion
import Submission.Work.FTS.EllipticEst.wirtinger_interval
import Submission.Work.FTS.EllipticEst.sin_integrals
import Submission.Work.FTS.EllipticEst.ibp_contdiffon
import Submission.Work.FTS.EllipticEst.trig_resid
import Submission.Work.FTS.EllipticEst.moment_eq_deriv_cos3
import Submission.Work.Elliptic.contDiffOn_one_bounds
import Submission.Work.Elliptic.intervalIntegrable_of_continuousOn_Ioo_of_bound

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst

set_option autoImplicit false

/-! ## Auxiliary facts for the slice coercivity -/

/-- `φ(θ) = sin 2θ`, the kernel direction of the `α = 0` angular operator `L₀`. -/
def phi2 (θ : ℝ) : ℝ := Real.sin (2 * θ)

/-- The constant `c = (1 + 225π²/2048)/16` of the slice coercivity. -/
def sliceC : ℝ := (1 + 225 * π ^ 2 / 2048) / 16

theorem sliceC_pos : 0 < sliceC := by
  rw [sliceC]; positivity

theorem sliceC_lt : sliceC < 1 / 6 := by
  have hpi : π ^ 2 < 15 := by nlinarith [Real.pi_lt_d4, Real.pi_pos]
  rw [sliceC]
  nlinarith [hpi]

/-- The set integral over `Iθ = [0,π/2]` written as an interval integral. -/
theorem Iθ_eq_interval (G : ℝ → ℝ) :
    (∫ θ in Work.Spaces.Iθ, G θ) = ∫ θ in (0 : ℝ)..(π / 2), G θ := by
  rw [Work.Spaces.Iθ, MeasureTheory.integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by positivity : (0 : ℝ) ≤ π / 2)]

/-- The first sine coefficient `a = (4/π)∫ f sin 2θ` of `f` on `[0,π/2]`. -/
def coeffF (f : ℝ → ℝ) : ℝ := (4 / π) * ∫ θ in (0 : ℝ)..(π / 2), f θ * Real.sin (2 * θ)

/-- The residue `g = f - a sin 2θ`, orthogonal to `sin 2θ`. -/
def residF (f : ℝ → ℝ) : ℝ → ℝ := fun θ => f θ - coeffF f * Real.sin (2 * θ)

/-- The final arithmetic step: given the two orthogonal decompositions
`∫f² = (π/4)a² + S`, `∫(f')² = πa² + R`, the bound on the first coefficient
`(π/4)a² ≤ (225π²/2048)S` and the spectral gap `16 S ≤ R`, deduce the coercivity bound. -/
theorem final_arith {A F2 F1 S R : ℝ} (hA0 : 0 ≤ A)
    (h2 : F2 = (π / 4) * A + S) (h1 : F1 = π * A + R)
    (hA : (π / 4) * A ≤ (225 * π ^ 2 / 2048) * S) (hgap : 16 * S ≤ R) :
    F2 ≤ sliceC * F1 := by
  have hpi := Real.pi_pos
  have hK : (0 : ℝ) < 1 + 225 * π ^ 2 / 2048 := by positivity
  have h1R : R ≤ F1 := by nlinarith [h1, hA0, hpi]
  have hfin : F2 ≤ (1 + 225 * π ^ 2 / 2048) * S := by nlinarith [h2, hA]
  rw [sliceC]
  nlinarith [hfin, hgap, h1R, hK]

/-- Agreement on the open interval implies a.e. agreement for the measure restricted to the
(oriented) closed interval. -/
private lemma ae_eq_of_eqOn_Ioo {f g : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (h : Set.EqOn f g (Set.Ioo a b)) : f =ᵐ[volume.restrict (Set.uIoc a b)] g := by
  rw [Set.uIoc_of_le hab, ← restrict_Ioo_eq_restrict_Ioc]
  exact ae_restrict_of_forall_mem measurableSet_Ioo (fun x hx => h hx)

/-- `(deriv f)²` is interval integrable on any subinterval `[a,b] ⊆ [0,π/2]` when `f` is `C²`
on `[0,π/2]` and vanishes at the endpoints (the derivative is continuous on the open interval
and bounded there). -/
private lemma intervalIntegrable_deriv_sq_Ioo {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (ha : 0 ≤ a) (hb : b ≤ π / 2)
    (hf : ContDiffOn ℝ 2 f (Set.Icc 0 (π / 2))) (h0 : f 0 = 0) (h1 : f (π / 2) = 0) :
    IntervalIntegrable (fun θ => (deriv f θ) ^ 2) volume a b := by
  have hf1 : ContDiffOn ℝ 1 f (Set.Icc 0 (π / 2)) := hf.of_le (by norm_num)
  have hcont : ContinuousOn (deriv f) (Set.Ioo (0 : ℝ) (π / 2)) :=
    continuousOn_deriv_Ioo_of_contDiffOn hf1
  obtain ⟨C, hC0, -, hCbnd⟩ := Work.Elliptic.contDiffOn_one_bounds hf1 h0 h1
  refine Work.Elliptic.intervalIntegrable_of_continuousOn_Ioo_of_bound hab ?_ (C ^ 2) ?_
  · refine (hcont.pow 2).mono ?_
    intro x hx
    exact ⟨lt_of_le_of_lt ha hx.1, lt_of_lt_of_le hx.2 hb⟩
  · intro x hx
    have hx' : x ∈ Set.Ioo (0 : ℝ) (π / 2) :=
      ⟨lt_of_le_of_lt ha hx.1, lt_of_lt_of_le hx.2 hb⟩
    have hb' := hCbnd x hx'
    rw [Real.norm_eq_abs] at hb'
    rw [abs_of_nonneg (sq_nonneg (deriv f x))]
    calc (deriv f x) ^ 2 = |deriv f x| ^ 2 := (sq_abs _).symm
      _ ≤ C ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hb' 2

/-- The angular moment of the residue `g = f - a sin 2θ` against `sin θ cos²θ` equals
`-(4/15) a`, and Cauchy–Schwarz with `∫ (sin θ cos²θ)² = π/32` bounds its square by
`(π/32) ∫ g²`. -/
private theorem residF_moment (f : ℝ → ℝ) (hf : ContDiffOn ℝ 2 f (Set.Icc 0 (π / 2)))
    (horth : (∫ θ in (0 : ℝ)..(π / 2), f θ * Work.Elliptic.sinCos2 θ) = 0) :
    (∫ θ in (0 : ℝ)..(π / 2), residF f θ * Work.Elliptic.sinCos2 θ
        = -(4 / 15) * coeffF f) ∧
    ((∫ θ in (0 : ℝ)..(π / 2), residF f θ * Work.Elliptic.sinCos2 θ) ^ 2
        ≤ (π / 32) * (∫ θ in (0 : ℝ)..(π / 2), (residF f θ) ^ 2)) := by
  have hpi : (0 : ℝ) ≤ π / 2 := by positivity
  obtain ⟨T1, T2, T3, T4⟩ := sin_integrals
  have hcont_f : ContinuousOn f (Set.uIcc 0 (π / 2)) := by
    rw [Set.uIcc_of_le hpi]; exact hf.continuousOn
  have hcont_w : ContinuousOn Work.Elliptic.sinCos2 (Set.uIcc 0 (π / 2)) := by
    unfold Work.Elliptic.sinCos2; fun_prop
  have hcont_g : ContinuousOn (residF f) (Set.uIcc 0 (π / 2)) := by
    unfold residF; fun_prop
  have hmom : (∫ θ in (0 : ℝ)..(π / 2), residF f θ * Work.Elliptic.sinCos2 θ)
      = -(4 / 15) * coeffF f := by
    have hpt : ∀ θ, residF f θ * Work.Elliptic.sinCos2 θ
        = f θ * Work.Elliptic.sinCos2 θ
          - coeffF f * (Real.sin (2 * θ) * Work.Elliptic.sinCos2 θ) := by
      intro θ; unfold residF; ring
    rw [intervalIntegral.integral_congr (fun θ _ => hpt θ)]
    have i1 : IntervalIntegrable (fun θ => f θ * Work.Elliptic.sinCos2 θ) volume 0 (π / 2) :=
      (hcont_f.mul hcont_w).intervalIntegrable
    have i2 : IntervalIntegrable
        (fun θ => coeffF f * (Real.sin (2 * θ) * Work.Elliptic.sinCos2 θ)) volume 0 (π / 2) := by
      refine ContinuousOn.intervalIntegrable ?_
      exact (((by fun_prop : ContinuousOn (fun θ : ℝ => Real.sin (2 * θ))
        (Set.uIcc 0 (π / 2)))).mul hcont_w).const_mul _
    rw [intervalIntegral.integral_sub i1 i2, intervalIntegral.integral_const_mul]
    have hswap : (∫ θ in (0 : ℝ)..(π / 2), Real.sin (2 * θ) * Work.Elliptic.sinCos2 θ)
        = 4 / 15 := by
      have heq : (∫ θ in (0 : ℝ)..(π / 2), Real.sin (2 * θ) * Work.Elliptic.sinCos2 θ)
          = ∫ θ in (0 : ℝ)..(π / 2), Work.Elliptic.sinCos2 θ * Real.sin (2 * θ) :=
        intervalIntegral.integral_congr (fun θ _ => by ring)
      rw [heq]; exact T4
    rw [hswap, horth]; ring
  refine ⟨hmom, ?_⟩
  have hquad0 : ∀ t : ℝ,
      0 ≤ (∫ θ in (0 : ℝ)..(π / 2), (residF f θ - t * Work.Elliptic.sinCos2 θ) ^ 2) := by
    intro t
    exact intervalIntegral.integral_nonneg hpi (fun θ _ => sq_nonneg _)
  have hpt_sq : ∀ (t θ : ℝ), (residF f θ - t * Work.Elliptic.sinCos2 θ) ^ 2
      = (residF f θ) ^ 2 - 2 * t * (residF f θ * Work.Elliptic.sinCos2 θ)
        + t ^ 2 * (Work.Elliptic.sinCos2 θ) ^ 2 := by
    intro t θ; ring
  have hexp : ∀ t : ℝ,
      (∫ θ in (0 : ℝ)..(π / 2), (residF f θ - t * Work.Elliptic.sinCos2 θ) ^ 2)
        = (∫ θ in (0 : ℝ)..(π / 2), (residF f θ) ^ 2)
          - 2 * t * (∫ θ in (0 : ℝ)..(π / 2), residF f θ * Work.Elliptic.sinCos2 θ)
          + t ^ 2 * (∫ θ in (0 : ℝ)..(π / 2), (Work.Elliptic.sinCos2 θ) ^ 2) := by
    intro t
    rw [intervalIntegral.integral_congr (fun θ _ => hpt_sq t θ)]
    have iA : IntervalIntegrable (fun θ => (residF f θ) ^ 2) volume 0 (π / 2) :=
      (hcont_g.pow 2).intervalIntegrable
    have iB : IntervalIntegrable (fun θ => 2 * t * (residF f θ * Work.Elliptic.sinCos2 θ))
        volume 0 (π / 2) :=
      ((hcont_g.mul hcont_w).const_mul _).intervalIntegrable
    have iC : IntervalIntegrable (fun θ => t ^ 2 * (Work.Elliptic.sinCos2 θ) ^ 2)
        volume 0 (π / 2) :=
      ((hcont_w.pow 2).const_mul _).intervalIntegrable
    rw [intervalIntegral.integral_add (iA.sub iB) iC, intervalIntegral.integral_sub iA iB,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  have hquad : ∀ x : ℝ, 0 ≤ (∫ θ in (0 : ℝ)..(π / 2), (Work.Elliptic.sinCos2 θ) ^ 2)
      * (x * x) + (-2 * (∫ θ in (0 : ℝ)..(π / 2), residF f θ * Work.Elliptic.sinCos2 θ)) * x
      + (∫ θ in (0 : ℝ)..(π / 2), (residF f θ) ^ 2) := by
    intro x
    have h := hquad0 x
    rw [hexp x] at h
    nlinarith [h]
  have hd := discrim_le_zero hquad
  rw [discrim, sq, T3] at hd
  nlinarith [hd]

/-- The sharp second Dirichlet eigenvalue on `[0,π/2]`: a `C²` function vanishing at the two
endpoints and orthogonal to `sin 2θ` satisfies `16 ∫ h² ≤ ∫ (h')²`.  Proof: split at `π/4`,
where `η = h - h(π/4) sin 2θ` vanishes, and apply Wirtinger's inequality with constant
`(π/(π/4))² = 16` on each half. -/
private theorem second_eigenvalue {h : ℝ → ℝ} (hh : ContDiffOn ℝ 2 h (Set.Icc 0 (π / 2)))
    (h0 : h 0 = 0) (h1 : h (π / 2) = 0)
    (hmean : (∫ θ in (0 : ℝ)..(π / 2), h θ * Real.sin (2 * θ)) = 0) :
    16 * (∫ θ in (0 : ℝ)..(π / 2), (h θ) ^ 2) ≤ ∫ θ in (0 : ℝ)..(π / 2), (deriv h θ) ^ 2 := by
  have hpi : (0 : ℝ) < π / 2 := by positivity
  have hpi4 : (0 : ℝ) < π / 4 := by positivity
  obtain ⟨T1, T2, T3, Dsin, Dcos⟩ := trig_resid
  -- the integration by parts `∫ h' (2 cos 2θ) = 4 ∫ h sin 2θ`
  have hcross : (∫ θ in (0 : ℝ)..(π / 2), deriv h θ * (2 * Real.cos (2 * θ))) = 0 := by
    have hIBP := ibp_contdiffon hpi hh
      (by fun_prop : ContDiff ℝ 2 (fun θ : ℝ => 2 * Real.cos (2 * θ)))
    have hint2 : (∫ x in (0 : ℝ)..(π / 2),
          h x * deriv (fun θ : ℝ => 2 * Real.cos (2 * θ)) x)
        = ∫ x in (0 : ℝ)..(π / 2), h x * (-4 * Real.sin (2 * x)) :=
      intervalIntegral.integral_congr (fun x _ => by rw [Dcos x])
    have hint : (∫ x in (0 : ℝ)..(π / 2), h x * (-4 * Real.sin (2 * x)))
        = -4 * (∫ x in (0 : ℝ)..(π / 2), h x * Real.sin (2 * x)) := by
      rw [← intervalIntegral.integral_const_mul]
      exact intervalIntegral.integral_congr (fun x _ => by ring)
    have h2pi : (2 : ℝ) * Real.cos (2 * (π / 2)) = -2 := by
      rw [show (2 : ℝ) * (π / 2) = π by ring, Real.cos_pi]; ring
    have h20 : (2 : ℝ) * Real.cos (2 * 0) = 2 := by
      rw [show (2 : ℝ) * 0 = 0 by ring, Real.cos_zero]; ring
    rw [hIBP, hint2, hint, hmean, h2pi, h20, h1, h0]; ring
  set c : ℝ := h (π / 4) with hc
  set η : ℝ → ℝ := fun θ => h θ - c * Real.sin (2 * θ) with heta
  have hηC : ContDiffOn ℝ 2 η (Set.Icc 0 (π / 2)) := by
    rw [heta]; fun_prop
  have hη0 : η 0 = 0 := by rw [heta]; simp [h0]
  have hη4 : η (π / 4) = 0 := by
    change h (π / 4) - c * Real.sin (2 * (π / 4)) = 0
    rw [← hc]
    have h2 : (2 : ℝ) * (π / 4) = π / 2 := by ring
    rw [h2, Real.sin_pi_div_two]; ring
  have hη1 : η (π / 2) = 0 := by
    change h (π / 2) - c * Real.sin (2 * (π / 2)) = 0
    have h2 : (2 : ℝ) * (π / 2) = π := by ring
    rw [h2, Real.sin_pi, h1]; ring
  have hsub1 : Set.Icc (0 : ℝ) (π / 4) ⊆ Set.Icc (0 : ℝ) (π / 2) := by
    intro x hx; exact ⟨hx.1, le_trans hx.2 (by linarith [Real.pi_pos])⟩
  have hsub2 : Set.Icc (π / 4) (π / 2) ⊆ Set.Icc (0 : ℝ) (π / 2) := by
    intro x hx; exact ⟨le_trans (by linarith [Real.pi_pos]) hx.1, hx.2⟩
  have hc4 : (π / ((π : ℝ) / 4 - 0)) ^ 2 = 16 := by
    have h1 : (π : ℝ) / (π / 4) = 4 := by field_simp
    rw [sub_zero, h1]; norm_num
  have hc4' : (π / ((π : ℝ) / 2 - π / 4)) ^ 2 = 16 := by
    have h1 : (π : ℝ) / (π / 2 - π / 4) = 4 := by
      rw [show (π : ℝ) / 2 - π / 4 = π / 4 by ring]
      field_simp
    rw [h1]; norm_num
  have hw1 : 16 * (∫ θ in (0 : ℝ)..(π / 4), (η θ) ^ 2)
      ≤ ∫ θ in (0 : ℝ)..(π / 4), (deriv η θ) ^ 2 := by
    have h := wirtinger_interval hpi4 (hηC.mono hsub1) hη0 hη4
    rwa [hc4] at h
  have hw2 : 16 * (∫ θ in (π / 4)..(π / 2), (η θ) ^ 2)
      ≤ ∫ θ in (π / 4)..(π / 2), (deriv η θ) ^ 2 := by
    have h := wirtinger_interval (by linarith [Real.pi_pos] : (π : ℝ) / 4 < π / 2)
      (hηC.mono hsub2) hη4 hη1
    rwa [hc4'] at h
  have iη1 : IntervalIntegrable (fun θ => (η θ) ^ 2) volume 0 (π / 4) := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hpi4.le]
    exact (hηC.continuousOn.pow 2).mono hsub1
  have iη2 : IntervalIntegrable (fun θ => (η θ) ^ 2) volume (π / 4) (π / 2) := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le (by linarith [Real.pi_pos] : (π : ℝ) / 4 ≤ π / 2)]
    exact (hηC.continuousOn.pow 2).mono hsub2
  have iD1 : IntervalIntegrable (fun θ => (deriv η θ) ^ 2) volume 0 (π / 4) :=
    intervalIntegrable_deriv_sq_Ioo hpi4.le le_rfl (by linarith [Real.pi_pos]) hηC hη0 hη1
  have iD2 : IntervalIntegrable (fun θ => (deriv η θ) ^ 2) volume (π / 4) (π / 2) :=
    intervalIntegrable_deriv_sq_Ioo (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])
      le_rfl hηC hη0 hη1
  have hsp1 : (∫ θ in (0 : ℝ)..(π / 2), (η θ) ^ 2)
      = (∫ θ in (0 : ℝ)..(π / 4), (η θ) ^ 2) + (∫ θ in (π / 4)..(π / 2), (η θ) ^ 2) :=
    (intervalIntegral.integral_add_adjacent_intervals iη1 iη2).symm
  have hsp2 : (∫ θ in (0 : ℝ)..(π / 2), (deriv η θ) ^ 2)
      = (∫ θ in (0 : ℝ)..(π / 4), (deriv η θ) ^ 2)
        + (∫ θ in (π / 4)..(π / 2), (deriv η θ) ^ 2) :=
    (intervalIntegral.integral_add_adjacent_intervals iD1 iD2).symm
  have hgapη : 16 * (∫ θ in (0 : ℝ)..(π / 2), (η θ) ^ 2)
      ≤ ∫ θ in (0 : ℝ)..(π / 2), (deriv η θ) ^ 2 := by
    rw [hsp1, hsp2]; linarith [hw1, hw2]
  -- expansion of `∫ η²`
  have hE1 : (∫ θ in (0 : ℝ)..(π / 2), (η θ) ^ 2)
      = (∫ θ in (0 : ℝ)..(π / 2), (h θ) ^ 2) + c ^ 2 * (π / 4) := by
    have hpt1 : ∀ θ, (η θ) ^ 2 = (h θ) ^ 2 - 2 * c * (h θ * Real.sin (2 * θ))
        + c ^ 2 * (Real.sin (2 * θ)) ^ 2 := by
      intro θ; rw [heta]; dsimp only; ring
    have hsq : (∫ θ in (0 : ℝ)..(π / 2), (η θ) ^ 2)
        = ∫ θ in (0 : ℝ)..(π / 2), ((h θ) ^ 2 - 2 * c * (h θ * Real.sin (2 * θ))
            + c ^ 2 * (Real.sin (2 * θ)) ^ 2) :=
      intervalIntegral.integral_congr (fun θ _ => hpt1 θ)
    rw [hsq]
    have hcont_h : ContinuousOn h (Set.uIcc 0 (π / 2)) := by
      rw [Set.uIcc_of_le hpi.le]; exact hh.continuousOn
    have hcont_s2 : ContinuousOn (fun θ : ℝ => Real.sin (2 * θ)) (Set.uIcc 0 (π / 2)) := by
      fun_prop
    have i1 : IntervalIntegrable (fun θ => (h θ) ^ 2) volume 0 (π / 2) :=
      (hcont_h.pow 2).intervalIntegrable
    have i2 : IntervalIntegrable (fun θ => 2 * c * (h θ * Real.sin (2 * θ)))
        volume 0 (π / 2) :=
      ((hcont_h.mul hcont_s2).const_mul (2 * c)).intervalIntegrable
    have i3 : IntervalIntegrable (fun θ => c ^ 2 * (Real.sin (2 * θ)) ^ 2)
        volume 0 (π / 2) :=
      ((hcont_s2.pow 2).const_mul (c ^ 2)).intervalIntegrable
    rw [intervalIntegral.integral_add (i1.sub i2) i3, intervalIntegral.integral_sub i1 i2,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul, hmean, T1]
    ring
  -- expansion of `∫ (η')²`
  have hdpt : ∀ θ ∈ Set.Ioo (0 : ℝ) (π / 2),
      deriv η θ = deriv h θ - 2 * c * Real.cos (2 * θ) := by
    have heq : η = h - fun θ : ℝ => c * Real.sin (2 * θ) := by rw [heta]; rfl
    intro θ hθ
    have hnhds : Set.Icc (0 : ℝ) (π / 2) ∈ 𝓝 θ := Icc_mem_nhds hθ.1 hθ.2
    have hhd : DifferentiableAt ℝ h θ := (hh.contDiffAt hnhds).differentiableAt (by norm_num)
    have hsd : DifferentiableAt ℝ (fun θ : ℝ => Real.sin (2 * θ)) θ := by fun_prop
    have hsd' : DifferentiableAt ℝ (fun θ : ℝ => c * Real.sin (2 * θ)) θ := hsd.const_mul c
    rw [heq, deriv_sub hhd hsd', deriv_const_mul c hsd, Dsin θ]
    ring
  have hE2 : (∫ θ in (0 : ℝ)..(π / 2), (deriv η θ) ^ 2)
      = (∫ θ in (0 : ℝ)..(π / 2), (deriv h θ) ^ 2) + π * c ^ 2 := by
    have hae : (fun θ => (deriv η θ) ^ 2)
        =ᵐ[volume.restrict (Set.uIoc (0 : ℝ) (π / 2))]
          (fun θ => (deriv h θ - 2 * c * Real.cos (2 * θ)) ^ 2) := by
      refine ae_eq_of_eqOn_Ioo hpi.le ?_
      intro θ hθ
      dsimp only
      rw [hdpt θ hθ]
    rw [intervalIntegral.integral_congr_ae_restrict hae]
    have hsq : (∫ θ in (0 : ℝ)..(π / 2), (deriv h θ - 2 * c * Real.cos (2 * θ)) ^ 2)
        = ∫ θ in (0 : ℝ)..(π / 2), ((deriv h θ) ^ 2
            - 2 * c * (deriv h θ * (2 * Real.cos (2 * θ)))
            + c ^ 2 * (2 * Real.cos (2 * θ)) ^ 2) :=
      intervalIntegral.integral_congr (fun θ _ => by ring)
    rw [hsq]
    have h1c : ContDiffOn ℝ 1 h (Set.Icc 0 (π / 2)) := hh.of_le (by norm_num)
    have iD : IntervalIntegrable (deriv h) volume 0 (π / 2) :=
      intervalIntegrable_deriv_of_contDiffOn h1c h0 h1
    have hcont_c2 : ContinuousOn (fun θ : ℝ => 2 * Real.cos (2 * θ)) (Set.uIcc 0 (π / 2)) := by
      fun_prop
    have i1 : IntervalIntegrable (fun θ => (deriv h θ) ^ 2) volume 0 (π / 2) :=
      intervalIntegrable_deriv_sq_Ioo hpi.le le_rfl le_rfl hh h0 h1
    have i2 : IntervalIntegrable (fun θ => 2 * c * (deriv h θ * (2 * Real.cos (2 * θ))))
        volume 0 (π / 2) :=
      ((iD.mul_continuousOn hcont_c2).const_mul (2 * c))
    have i3 : IntervalIntegrable (fun θ => c ^ 2 * (2 * Real.cos (2 * θ)) ^ 2)
        volume 0 (π / 2) :=
      ((hcont_c2.pow 2).const_mul (c ^ 2)).intervalIntegrable
    rw [intervalIntegral.integral_add (i1.sub i2) i3, intervalIntegral.integral_sub i1 i2,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul, hcross, T3]
    ring
  rw [hE1, hE2] at hgapη
  nlinarith [hgapη, sq_nonneg c, Real.pi_pos]

/-- The assembly: given the three analytic inputs (the orthogonal decomposition of `f` along
`sin 2θ`, the bound on the first coefficient from the solvability condition, and the spectral
gap `16` on the orthogonal complement), the slice coercivity follows with the constant `sliceC`. -/
theorem assembly
    (hres : ∀ f : ℝ → ℝ, ContDiffOn ℝ 2 f (Set.Icc 0 (π / 2)) → f 0 = 0 → f (π / 2) = 0 →
      (∫ θ in (0 : ℝ)..(π / 2), residF f θ * Real.sin (2 * θ) = 0) ∧
      (∫ θ in (0 : ℝ)..(π / 2), deriv (residF f) θ * (2 * Real.cos (2 * θ)) = 0) ∧
      (∫ θ in (0 : ℝ)..(π / 2), (f θ) ^ 2
        = (π / 4) * (coeffF f) ^ 2 + ∫ θ in (0 : ℝ)..(π / 2), (residF f θ) ^ 2) ∧
      (∫ θ in (0 : ℝ)..(π / 2), (deriv f θ) ^ 2
        = π * (coeffF f) ^ 2 + ∫ θ in (0 : ℝ)..(π / 2), (deriv (residF f) θ) ^ 2))
    (hmom : ∀ f : ℝ → ℝ, ContDiffOn ℝ 2 f (Set.Icc 0 (π / 2)) →
      (∫ θ in (0 : ℝ)..(π / 2), f θ * Work.Elliptic.sinCos2 θ) = 0 →
      (∫ θ in (0 : ℝ)..(π / 2), residF f θ * Work.Elliptic.sinCos2 θ
          = -(4 / 15) * coeffF f) ∧
      ((∫ θ in (0 : ℝ)..(π / 2), residF f θ * Work.Elliptic.sinCos2 θ) ^ 2
          ≤ (π / 32) * (∫ θ in (0 : ℝ)..(π / 2), (residF f θ) ^ 2)))
    (hgap : ∀ h : ℝ → ℝ, ContDiffOn ℝ 2 h (Set.Icc 0 (π / 2)) → h 0 = 0 → h (π / 2) = 0 →
      (∫ θ in (0 : ℝ)..(π / 2), h θ * Real.sin (2 * θ)) = 0 →
      16 * (∫ θ in (0 : ℝ)..(π / 2), (h θ) ^ 2) ≤ ∫ θ in (0 : ℝ)..(π / 2), (deriv h θ) ^ 2) :
    ∀ f : ℝ → ℝ, ContDiffOn ℝ 2 f (Set.Icc 0 (π / 2)) → f 0 = 0 → f (π / 2) = 0 →
      (∫ θ in Work.Spaces.Iθ, f θ * Work.Elliptic.sinCos2 θ) = 0 →
      (∫ θ in Work.Spaces.Iθ, (f θ) ^ 2) ≤ sliceC * ∫ θ in Work.Spaces.Iθ, (deriv f θ) ^ 2 := by
  intro f hf h0 h1 horth
  have horth' : (∫ θ in (0 : ℝ)..(π / 2), f θ * Work.Elliptic.sinCos2 θ) = 0 := by
    rw [← Iθ_eq_interval (fun θ => f θ * Work.Elliptic.sinCos2 θ)]
    exact horth
  rw [Iθ_eq_interval (fun θ => (f θ) ^ 2), Iθ_eq_interval (fun θ => (deriv f θ) ^ 2)]
  obtain ⟨hgphi, -, hf2, hf12⟩ := hres f hf h0 h1
  obtain ⟨hmom1, hmom2⟩ := hmom f hf horth'
  have hgc : ContDiffOn ℝ 2 (residF f) (Set.Icc 0 (π / 2)) := by
    unfold residF; fun_prop
  have hg0 : residF f 0 = 0 := by simp [residF, h0]
  have hg1 : residF f (π / 2) = 0 := by
    have h2pi : (2 : ℝ) * (π / 2) = π := by ring
    simp [residF, h1, h2pi, Real.sin_pi]
  have hgp := hgap (residF f) hgc hg0 hg1 hgphi
  have hA : (π / 4) * (coeffF f) ^ 2
      ≤ (225 * π ^ 2 / 2048) * (∫ θ in (0 : ℝ)..(π / 2), (residF f θ) ^ 2) := by
    have h1 : ((-(4 / 15) * coeffF f)) ^ 2
        ≤ (π / 32) * (∫ θ in (0 : ℝ)..(π / 2), (residF f θ) ^ 2) := by
      rw [← hmom1]; exact hmom2
    have h2 : (16 / 225) * (coeffF f) ^ 2
        ≤ (π / 32) * (∫ θ in (0 : ℝ)..(π / 2), (residF f θ) ^ 2) := by
      nlinarith [h1]
    have h3 := mul_le_mul_of_nonneg_left h2 (show (0 : ℝ) ≤ 225 * π / 64 by positivity)
    calc (π / 4) * (coeffF f) ^ 2
        = (225 * π / 64) * ((16 / 225) * (coeffF f) ^ 2) := by ring
      _ ≤ (225 * π / 64) * ((π / 32) * (∫ θ in (0 : ℝ)..(π / 2), (residF f θ) ^ 2)) := h3
      _ = (225 * π ^ 2 / 2048) * (∫ θ in (0 : ℝ)..(π / 2), (residF f θ) ^ 2) := by ring
  exact final_arith (sq_nonneg _) hf2 hf12 hA hgp



/-- **Slice-wise coercivity of the `α = 0` angular operator, away from its kernel.**

For a function `f` on `[0,π/2]` that is `C²`, vanishes at `θ = 0` and `θ = π/2`, and whose
angular moment against `sin θ cos²θ` vanishes (the paper's orthogonality condition
`OrthCond`), the unweighted `L²`-norm of `f` is dominated by that of `deriv f` with a
constant strictly below `1/6`.

This is the quantitative form of "`sin 2θ` spans the kernel of
`L₀ = -∂_θθ + ∂_θ(tan θ ·) - 6`, while `∫₀^{π/2} sin 2θ · sin θ cos²θ dθ = 4/15 ≠ 0`, so
the orthogonality condition excludes the kernel direction with a quantitative gain".  It is
Step 1/the Fourier step of the proof of Proposition `prop:L2` (Elgindi, Annals 194 (3) 2021,
tex 740-760), and it is what makes the naive energy inequality
`∫(f')² - 6∫f² ≤ (F,f)` (which loses a factor `α`) close in the constant `6`:
with `∫f² ≤ c ∫(f')²` and `6c < 1` one gets `∫(f')² ≲ (F,f)`.

A concrete route: expand `f` in the Dirichlet eigenbasis `sin(2kθ)` of `-d²/dθ²` on
`(0,π/2)` (Parseval: `∫f² = (π/4)Σa_k²`, `∫(f')² = (π/4)Σ4k²a_k²`), use the constraint
`Σ b_k a_k = 0` with `b_k = ∫₀^{π/2} sin(2kθ) sin θ cos²θ dθ`
(the explicit value `|b_k| = 4k/((4k²-1)|4k²-9|)` — the *corrected* form of the paper's
coefficient, already available in this workspace as
`Work.Elliptic.integral_sinCos2_mul_sin_two` — note `b₁ = 4/15`), Cauchy–Schwarz
`b₁²a₁² ≤ (Σ_{k≥2}a_k²)(Σ_{k≥2}b_k²)`, and `Σ_{k≥2}b_k² < b₁²/2`.  The sharp constant is
`≈ 1/15.09`, so the bound `1/6` has ample room: a cruder argument is welcome and no attempt
at the sharp constant is needed.

Downstream use: the slice-wise energy identity of the elliptic section produces
`∫(Ψ_θ)² - 6∫(Ψ)² ≤ (F,Ψ)` for `Ψ(z,·)`; combined with this result applied to each slice,
`6c < 1` gives `∫(Ψ_θ)² ≲ ∫F·Ψ`, hence `‖Ψ_θ‖ ≲ ‖F‖` by Cauchy–Schwarz. -/
theorem coercive_slice_fts : ∃ c : ℝ, 0 < c ∧ c < 1 / 6 ∧
    ∀ f : ℝ → ℝ, ContDiffOn ℝ 2 f (Set.Icc 0 (π / 2)) → f 0 = 0 → f (π / 2) = 0 →
      (∫ θ in Work.Spaces.Iθ, f θ * Work.Elliptic.sinCos2 θ) = 0 →
      (∫ θ in Work.Spaces.Iθ, (f θ) ^ 2) ≤ c * ∫ θ in Work.Spaces.Iθ, (deriv f θ) ^ 2 := by
  refine ⟨sliceC, sliceC_pos, sliceC_lt, ?_⟩
  refine assembly ?_ ?_ ?_
  · intro f hf h0 h1
    exact resid_expansion f hf h0 h1
  · intro f hf horth
    exact residF_moment f hf horth
  · intro h hh h0 h1 hmean
    exact second_eigenvalue hh h0 h1 hmean

end Work.FTS.EllipticEst
