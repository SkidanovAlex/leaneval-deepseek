/-
# The two-dimensional lift collapse of the circle integral

`Work.KMTAreas.A7.fold_lift_prod` is the identity

  `∫_{θ₁}∫_{θ₂} H (lift θ₁) (lift θ₂) · fourier (-a) θ₁ · fourier (-b) θ₂
      = ∫_{x₁}∫_{x₂} H x₁ x₂ · fourier (-a) x₁ · fourier (-b) x₂`

for `H : ℝ² → ℂ` measurable, bounded and supported in `[-1/4,1/4]²`, the circle integrals being
taken against the Haar probability measure `AddCircle.haarAddCircle` and the real ones against
Lebesgue measure.  It is used at `A7/coeff_spike.lean` (line 84) to collapse the coefficients of a
narrow spike symbol.

Proof: the one-dimensional fold `fold_lift_mul`, applied to the inner and then to the outer
integral (the technique is that of the one-dimensional `spikeAux_integral_lift_mul_eq` in
`A7/spikeFinsetMassBound.lean`: rewrite the Haar integral as an integral over the fundamental
domain `(-1/2, 1/2)` with `AddCircle.integral_preimage`, on which `lift ∘ coe = id`, and extend
the set integral over that domain to the integral over `ℝ` using that the integrand vanishes off
`[-1/4,1/4]`).
-/
import Mathlib
import Submission.Work.KMTAreas.A7.liftCollapse

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.KMTAreas.A7

noncomputable section

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal BigOperators
open Work.Analysis.IonescuWainger

/-- The canonical lift of the class of `a` is `a` for `a ∈ (-1/2, 1/2)`. -/
theorem lift_coe_of_mem (a : ℝ) (ha : -(1 / 2) < a) (ha' : a < 1 / 2) :
    lift ((a : ℝ) : AddCircle (1 : ℝ)) = a := by
  have hmem : a ∈ Set.Ico (-(1 / 2) : ℝ) (-(1 / 2) + 1) := by
    rw [Set.mem_Ico, show (-(1 / 2) : ℝ) + 1 = 1 / 2 by norm_num]
    exact ⟨le_of_lt ha, ha'⟩
  have h1 : lift ((a : ℝ) : AddCircle (1 : ℝ))
      ∈ Set.Ico (-(1 / 2) : ℝ) (-(1 / 2) + 1) := by
    rw [Set.mem_Ico, show (-(1 / 2) : ℝ) + 1 = 1 / 2 by norm_num]
    exact Set.mem_Ico.mp (lift_mem _)
  exact (AddCircle.coe_eq_coe_iff_of_mem_Ico (p := (1 : ℝ)) (a := -(1 / 2)) h1 hmem).mp
    (lift_coe _)

/-- `lift` of the class of `1/2` is `-1/2`. -/
theorem lift_coe_half : lift (((1 / 2 : ℝ)) : AddCircle (1 : ℝ)) = -(1 / 2) := by
  have hmem : (-(1 / 2) : ℝ) ∈ Set.Ico (-(1 / 2)) (-(1 / 2) + 1) := by
    rw [Set.mem_Ico, show (-(1 / 2) : ℝ) + 1 = 1 / 2 by norm_num]
    exact ⟨le_rfl, by norm_num⟩
  have h1 : lift (((1 / 2 : ℝ)) : AddCircle (1 : ℝ))
      ∈ Set.Ico (-(1 / 2) : ℝ) (-(1 / 2) + 1) := by
    rw [Set.mem_Ico, show (-(1 / 2) : ℝ) + 1 = 1 / 2 by norm_num]
    exact Set.mem_Ico.mp (lift_mem _)
  have hcoe : (((1 / 2 : ℝ)) : AddCircle (1 : ℝ)) = ((-(1 / 2) : ℝ) : AddCircle (1 : ℝ)) := by
    rw [← AddCircle.coe_add_period (x := (-(1 / 2) : ℝ))]
    congr 1
    norm_num
  exact (AddCircle.coe_eq_coe_iff_of_mem_Ico (p := (1 : ℝ)) (a := -(1 / 2)) h1 hmem).mp
    (by rw [lift_coe, hcoe])

/-- A function of `ℝ` supported in `[-1/4,1/4]` is zero off `[-1/4,1/4]` (in the form used by
the collapse). -/
theorem zero_of_supp_quarter {h : ℝ → ℂ} (hh : ∀ x : ℝ, h x ≠ 0 → |x| ≤ 1 / 4) :
    ∀ x : ℝ, x ∉ Set.Icc (-(1 / 4) : ℝ) (1 / 4) → h x = 0 := by
  intro x hx
  by_contra hne
  exact hx (by rw [Set.mem_Icc]; exact abs_le.mp (hh x hne))

/-- **The one-dimensional lift collapse.**  For `h` supported in `[-1/4,1/4]` and any
`c : 𝕋 → ℂ`, the Haar integral of `θ ↦ h (lift θ) * c θ` equals the Lebesgue integral of
`x ↦ h x * c (x mod 1)`. -/
theorem fold_lift_mul (h : ℝ → ℂ) (c : AddCircle (1 : ℝ) → ℂ)
    (hh : ∀ x : ℝ, h x ≠ 0 → |x| ≤ 1 / 4) :
    (∫ θ : AddCircle (1 : ℝ), h (lift θ) * c θ ∂AddCircle.haarAddCircle)
      = ∫ x : ℝ, h x * c ((x : ℝ) : AddCircle (1 : ℝ)) := by
  have hzero := zero_of_supp_quarter hh
  have hmain : (∫ θ : AddCircle (1 : ℝ), h (lift θ) * c θ)
      = ∫ x : ℝ, h x * c ((x : ℝ) : AddCircle (1 : ℝ)) := by
    have hpre := AddCircle.integral_preimage (T := (1 : ℝ)) (-(1 / 2))
      (fun θ : AddCircle (1 : ℝ) => h (lift θ) * c θ)
    rw [← hpre]
    rw [show (-(1 / 2) : ℝ) + 1 = 1 / 2 by norm_num]
    have hcongr : (∫ x in Set.Ioc (-(1 / 2)) (1 / 2),
          h (lift ((x : ℝ) : AddCircle (1 : ℝ))) * c ((x : ℝ) : AddCircle (1 : ℝ)))
        = ∫ x in Set.Ioc (-(1 / 2)) (1 / 2),
            h x * c ((x : ℝ) : AddCircle (1 : ℝ)) := by
      refine setIntegral_congr_fun measurableSet_Ioc fun x hx => ?_
      rw [Set.mem_Ioc] at hx
      rcases lt_or_eq_of_le hx.2 with hlt | heq
      · rw [lift_coe_of_mem x hx.1 hlt]
      · subst heq
        rw [lift_coe_half, hzero (-(1 / 2)) (by rw [Set.mem_Icc]; norm_num),
          hzero (1 / 2) (by rw [Set.mem_Icc]; norm_num)]
    rw [hcongr]
    refine setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => ?_
    have hx0 : h x = 0 := hzero x fun hmem => by
      rw [Set.mem_Icc] at hmem
      exact hx (Set.mem_Ioc.mpr ⟨by linarith [hmem.1], by linarith [hmem.2]⟩)
    rw [hx0, zero_mul]
  rw [AddCircle.integral_haarAddCircle]
  simp only [inv_one, one_smul]
  exact hmain

/-- **The two-dimensional lift collapse.** -/
theorem fold_lift_prod {H : ℝ → ℝ → ℂ} {C : ℝ}
    (hH : Measurable fun p : ℝ × ℝ => H p.1 p.2)
    (hb : ∀ x₁ x₂ : ℝ, ‖H x₁ x₂‖ ≤ C)
    (hsupp₁ : ∀ x₁ x₂ : ℝ, H x₁ x₂ ≠ 0 → |x₁| ≤ 1 / 4)
    (hsupp₂ : ∀ x₁ x₂ : ℝ, H x₁ x₂ ≠ 0 → |x₂| ≤ 1 / 4)
    (a b : ℤ) :
    (∫ θ₁ : AddCircle (1 : ℝ), ∫ θ₂ : AddCircle (1 : ℝ),
        H (lift θ₁) (lift θ₂) * fourier (T := 1) (-a) θ₁ * fourier (T := 1) (-b) θ₂
          ∂AddCircle.haarAddCircle ∂AddCircle.haarAddCircle)
      = ∫ x₁ : ℝ, ∫ x₂ : ℝ,
          H x₁ x₂ * fourier (T := 1) (-a) ((x₁ : ℝ) : AddCircle (1 : ℝ))
            * fourier (T := 1) (-b) ((x₂ : ℝ) : AddCircle (1 : ℝ)) := by
  -- the inner collapse: for every `θ₁`, the `θ₂`-integral folds
  have hinner : ∀ θ₁ : AddCircle (1 : ℝ),
      (∫ θ₂, H (lift θ₁) (lift θ₂) * fourier (T := 1) (-a) θ₁
          * fourier (T := 1) (-b) θ₂ ∂AddCircle.haarAddCircle)
        = fourier (T := 1) (-a) θ₁
          * ∫ x₂, H (lift θ₁) x₂ * fourier (T := 1) (-b) ((x₂ : ℝ) : AddCircle (1 : ℝ)) := by
    intro θ₁
    have hsupp : ∀ x : ℝ, (fun y => H (lift θ₁) y) x ≠ 0 → |x| ≤ 1 / 4 :=
      fun x hx => hsupp₂ (lift θ₁) x hx
    have hfold := fold_lift_mul (fun y : ℝ => H (lift θ₁) y)
      (fun θ₂ => fourier (T := 1) (-b) θ₂) hsupp
    have hconst : (∫ θ₂, H (lift θ₁) (lift θ₂) * fourier (T := 1) (-a) θ₁
          * fourier (T := 1) (-b) θ₂ ∂AddCircle.haarAddCircle)
        = fourier (T := 1) (-a) θ₁
          * ∫ θ₂, H (lift θ₁) (lift θ₂) * fourier (T := 1) (-b) θ₂
              ∂AddCircle.haarAddCircle := by
      rw [show (fun θ₂ : AddCircle (1 : ℝ) => H (lift θ₁) (lift θ₂)
            * fourier (T := 1) (-a) θ₁ * fourier (T := 1) (-b) θ₂)
          = (fun θ₂ => fourier (T := 1) (-a) θ₁
              * (H (lift θ₁) (lift θ₂) * fourier (T := 1) (-b) θ₂))
          from by funext θ₂; ring]
      rw [MeasureTheory.integral_const_mul]
    rw [hconst, hfold]
  -- the outer collapse
  have houter : (∫ θ₁ : AddCircle (1 : ℝ), (fourier (T := 1) (-a) θ₁
          * ∫ x₂, H (lift θ₁) x₂ * fourier (T := 1) (-b) ((x₂ : ℝ) : AddCircle (1 : ℝ)))
            ∂AddCircle.haarAddCircle)
      = ∫ x₁ : ℝ, ∫ x₂ : ℝ, H x₁ x₂
          * fourier (T := 1) (-a) ((x₁ : ℝ) : AddCircle (1 : ℝ))
          * fourier (T := 1) (-b) ((x₂ : ℝ) : AddCircle (1 : ℝ)) := by
    set G : ℝ → ℂ := fun y => ∫ x₂, H y x₂
        * fourier (T := 1) (-b) ((x₂ : ℝ) : AddCircle (1 : ℝ)) with hG
    have hGsupp : ∀ y : ℝ, G y ≠ 0 → |y| ≤ 1 / 4 := by
      intro y hy
      by_contra hcon
      refine hy ?_
      have hzero : (fun x₂ : ℝ => H y x₂
          * fourier (T := 1) (-b) ((x₂ : ℝ) : AddCircle (1 : ℝ))) = 0 := by
        funext x₂
        have hH0 : H y x₂ = 0 := by
          by_contra hc
          exact hcon (hsupp₁ y x₂ hc)
        rw [hH0, zero_mul]
        rfl
      rw [hG]
      show (∫ x₂, H y x₂ * fourier (T := 1) (-b) ((x₂ : ℝ) : AddCircle (1 : ℝ))) = 0
      rw [hzero]
      simp
    have hfold := fold_lift_mul G (fourier (T := 1) (-a)) hGsupp
    have hpt : (∫ θ₁ : AddCircle (1 : ℝ), fourier (T := 1) (-a) θ₁
          * (∫ x₂, H (lift θ₁) x₂ * fourier (T := 1) (-b) ((x₂ : ℝ) : AddCircle (1 : ℝ)))
            ∂AddCircle.haarAddCircle)
        = ∫ θ₁ : AddCircle (1 : ℝ), G (lift θ₁) * fourier (T := 1) (-a) θ₁
            ∂AddCircle.haarAddCircle := by
      refine integral_congr_ae (Eventually.of_forall fun θ₁ => ?_)
      show fourier (T := 1) (-a) θ₁
          * (∫ x₂, H (lift θ₁) x₂ * fourier (T := 1) (-b) ((x₂ : ℝ) : AddCircle (1 : ℝ)))
        = G (lift θ₁) * fourier (T := 1) (-a) θ₁
      rw [hG]
      simp only []
      ring
    rw [hpt, hfold]
    refine integral_congr_ae (Eventually.of_forall fun x₁ => ?_)
    show G x₁ * fourier (T := 1) (-a) ((x₁ : ℝ) : AddCircle (1 : ℝ))
        = ∫ x₂, H x₁ x₂ * fourier (T := 1) (-a) ((x₁ : ℝ) : AddCircle (1 : ℝ))
            * fourier (T := 1) (-b) ((x₂ : ℝ) : AddCircle (1 : ℝ))
    rw [hG]
    simp only []
    rw [show (fun x₂ : ℝ => H x₁ x₂ * fourier (T := 1) (-a) ((x₁ : ℝ) : AddCircle (1 : ℝ))
          * fourier (T := 1) (-b) ((x₂ : ℝ) : AddCircle (1 : ℝ)))
        = (fun x₂ => fourier (T := 1) (-a) ((x₁ : ℝ) : AddCircle (1 : ℝ))
            * (H x₁ x₂ * fourier (T := 1) (-b) ((x₂ : ℝ) : AddCircle (1 : ℝ))))
        from by funext x₂; ring]
    rw [MeasureTheory.integral_const_mul]
    ring
  have hfun : (fun θ₁ : AddCircle (1 : ℝ) => ∫ θ₂, H (lift θ₁) (lift θ₂)
        * fourier (T := 1) (-a) θ₁ * fourier (T := 1) (-b) θ₂ ∂AddCircle.haarAddCircle)
      = fun θ₁ => fourier (T := 1) (-a) θ₁
        * (∫ x₂, H (lift θ₁) x₂ * fourier (T := 1) (-b) ((x₂ : ℝ) : AddCircle (1 : ℝ))) := by
    funext θ₁
    exact hinner θ₁
  rw [hfun]
  exact houter

end

end Work.KMTAreas.A7
