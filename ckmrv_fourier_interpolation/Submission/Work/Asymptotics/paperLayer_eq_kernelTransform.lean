import Mathlib
import Submission.Work.Asymptotics.DomainD
import Submission.Work.Asymptotics.F2LayerDefs
import Submission.Work.Kernels.Kernels
import Submission.Work.Kernels.ModerateGrowth
import Submission.Work.Asymptotics.paperLayer_agreement
import Submission.Work.Asymptotics.measurable_Kaxis_Kfun

noncomputable section

open MeasureTheory UpperHalfPlane
open scoped Topology

namespace Work.Asymptotics

/-! ## Two integrability inputs, and the agreement of the layer with the contour integral -/

/-- The modulus of the Gaussian factor `e^{-Lt}`. -/
private lemma norm_exp_neg_mul (L t : ℝ) :
    ‖Complex.exp (-(L : ℂ) * (t : ℂ))‖ = Real.exp (-(L * t)) := by
  rw [Complex.norm_exp]
  congr 1
  simp

/-- **The tail of `K - Aexp` is integrable against the Gaussian.**  This is the only place where
the two-regime bound `TailBound` is used: on the window `[1, (scale τ)^{N₀}]` the difference is
bounded polynomially (so integrable against `e^{-Lt}` on a finite-measure set), and beyond the
threshold it decays like `t^M e^{-πt}`, which beats every polynomial. -/
private lemma integrableOn_diff_mul_exp (ℓ : Work.Kernels.LogLambdaData) (d : ℕ)
    (hd : d = 8 ∨ d = 24) (G : Fin 2 → Fin 2 → UpperHalfPlane → ℂ)
    (hT : TailBound ℓ d G) {τ : UpperHalfPlane} (hτ : τ ∈ DomainD) {L : ℝ} (hL : 0 < L) :
    IntegrableOn (fun t : ℝ => (Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t - Aexp G τ t)
      * Complex.exp (-(L : ℂ) * (t : ℂ))) (Set.Ioi (1 : ℝ)) := by
  obtain ⟨C, N, M, hC, hN, hM, hb1⟩ := hT.1
  obtain ⟨N₀, C', N', M', hN₀, hC', hN', hM', hb2⟩ := hT.2
  set S : ℝ := Work.Kernels.scale τ with hS
  have hSnn : 0 ≤ S := by rw [hS]; unfold Work.Kernels.scale; positivity
  set f : ℝ → ℂ := fun t : ℝ => (Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t - Aexp G τ t)
      * Complex.exp (-(L : ℂ) * (t : ℂ)) with hf
  have hmeasK : Measurable (fun t : ℝ => Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t) :=
    measurable_Kaxis_Kfun ℓ d hd τ
  have hmeasA : Measurable (fun t : ℝ => Aexp G τ t) := by unfold Aexp; fun_prop
  have hmeasE : Measurable (fun t : ℝ => Complex.exp (-(L : ℂ) * (t : ℂ))) := by fun_prop
  set p : ℝ := max (S ^ N₀) 1 with hp
  have hpS : S ^ N₀ ≤ p := le_max_left _ _
  have hp1 : (1 : ℝ) ≤ p := le_max_right _ _
  have hppos : 0 < p := lt_of_lt_of_le zero_lt_one hp1
  have hleft : IntegrableOn f (Set.Ioc (1 : ℝ) p) := by
    refine Integrable.mono' (integrableOn_const (C := C * S ^ N * (1 + p) ^ M) (by simp)) ?_ ?_
    · rw [hf]; exact ((hmeasK.sub hmeasA).mul hmeasE).aestronglyMeasurable
    · filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      obtain ⟨ht1, htp⟩ := ht
      have ht0 : 0 < t := lt_trans zero_lt_one ht1
      rw [hf, norm_mul, norm_exp_neg_mul]
      have hb := hb1 τ hτ t ht1.le
      have hexp_le : Real.exp (-(L * t)) ≤ 1 := by
        rw [← Real.exp_zero]
        exact Real.exp_le_exp.mpr (by nlinarith [hL, ht0])
      have hcoef : 0 ≤ C * S ^ N := mul_nonneg hC.le (Real.rpow_nonneg hSnn N)
      calc ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t - Aexp G τ t‖ * Real.exp (-(L * t))
          ≤ (C * S ^ N * (1 + t) ^ M) * 1 :=
            mul_le_mul hb hexp_le (Real.exp_nonneg _)
              (mul_nonneg hcoef (Real.rpow_nonneg (by linarith) M))
        _ ≤ (C * S ^ N * (1 + p) ^ M) := by
            rw [mul_one]
            exact mul_le_mul_of_nonneg_left
              (Real.rpow_le_rpow (by linarith) (by linarith) hM) hcoef
  have hright : IntegrableOn f (Set.Ioi p) := by
    have hdom : IntegrableOn (fun t : ℝ => C' * S ^ N' * (t ^ M' * Real.exp (-((Real.pi + L) * t))))
        (Set.Ioi p) :=
      integrableOn_const_mul_real
        (integrableOn_rpow_mul_exp_neg_mul_Ioi_pos M' hppos (by linarith [Real.pi_pos, hL]))
        (C' * S ^ N')
    refine Integrable.mono' hdom ?_ ?_
    · rw [hf]; exact ((hmeasK.sub hmeasA).mul hmeasE).aestronglyMeasurable
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      have htp : p < t := ht
      have htS : S ^ N₀ ≤ t := le_trans hpS htp.le
      have hb := hb2 τ hτ t htS
      rw [hf, norm_mul, norm_exp_neg_mul]
      have hcoef : 0 ≤ C' * S ^ N' := mul_nonneg hC'.le (Real.rpow_nonneg hSnn N')
      calc ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t - Aexp G τ t‖ * Real.exp (-(L * t))
          ≤ (C' * S ^ N' * t ^ M' * Real.exp (-(Real.pi * t))) * Real.exp (-(L * t)) :=
            mul_le_mul_of_nonneg_right hb (Real.exp_nonneg _)
        _ = C' * S ^ N' * (t ^ M' * Real.exp (-((Real.pi + L) * t))) := by
            rw [show Real.exp (-((Real.pi + L) * t))
                = Real.exp (-(Real.pi * t)) * Real.exp (-(L * t)) from by
              rw [← Real.exp_add]; congr 1; ring]
            ring
  have hunion : IntegrableOn f (Set.Ioc (1 : ℝ) p ∪ Set.Ioi p) := hleft.union hright
  have hset : Set.Ioc (1 : ℝ) p ∪ Set.Ioi p = Set.Ioi (1 : ℝ) := by
    ext t; simp only [Set.mem_union, Set.mem_Ioc, Set.mem_Ioi]
    constructor
    · rintro (⟨h1, h2⟩ | h3)
      · exact h1
      · exact lt_of_le_of_lt hp1 h3
    · intro h1
      by_cases h2 : t ≤ p
      · exact Or.inl ⟨h1, h2⟩
      · exact Or.inr (lt_of_not_ge h2)
  rwa [hset] at hunion

/-- **Integrability of the contour integrand in the range `r ≠ 0 ∧ (d = 8 ∨ 2 < r²)`.**

On `(0,1]` the kernel is bounded by `hflat` (with `N = 0`).  On `[1,∞)` the integrand is the sum of
`(K - Aexp)e^{-πr²t}`, which is integrable by `TailBound`, and of `Aexp·e^{-πr²t}`, whose two
exponential factors are `e^{-λt}` (`λ = πr² > 0`, always decaying since `r ≠ 0`) and
`e^{-μt}` (`μ = πr² - 2π`), the latter decaying exactly when `r² > 2`, and otherwise vanishing
identically in dimension `8` by `h8`. -/
private lemma integrableOn_kernelIntegrand (ℓ : Work.Kernels.LogLambdaData) (d : ℕ)
    (hd : d = 8 ∨ d = 24) (G : Fin 2 → Fin 2 → UpperHalfPlane → ℂ)
    (h8 : d = 8 → ∀ j : Fin 2, G 1 j = 0)
    (hflat : ∀ N : ℝ, 0 ≤ N → ∃ c N' : ℝ, 0 ≤ c ∧ ∀ (τ : UpperHalfPlane) (t : ℝ),
      τ ∈ DomainD → 0 < t → t ≤ 1 →
        ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t‖
          ≤ c * (Work.Kernels.scale τ) ^ N' * t ^ N)
    (hT : TailBound ℓ d G) {τ : UpperHalfPlane} (hτ : τ ∈ DomainD) {r : ℝ} (hr : r ≠ 0)
    (hcase : d = 8 ∨ 2 < r ^ 2) :
    IntegrableOn (fun t : ℝ => Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t
      * Complex.exp (-(Real.pi * (r : ℂ) ^ 2 * (t : ℂ)))) (Set.Ioi 0) := by
  set L : ℝ := Real.pi * r ^ 2 with hL
  have hLpos : 0 < L := by rw [hL]; positivity
  set Mu : ℝ := L - 2 * Real.pi with hMu
  have hargE : ∀ t : ℝ, Complex.exp (-(Real.pi * (r : ℂ) ^ 2 * (t : ℂ)))
      = Complex.exp (-(L : ℂ) * (t : ℂ)) := by
    intro t; rw [hL]; congr 1; push_cast; ring
  set F : ℝ → ℂ := fun t => Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t
      * Complex.exp (-(L : ℂ) * (t : ℂ)) with hF
  have hmeasK : Measurable (fun t : ℝ => Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t) :=
    measurable_Kaxis_Kfun ℓ d hd τ
  have hmeasE : Measurable (fun t : ℝ => Complex.exp (-(L : ℂ) * (t : ℂ))) := by fun_prop
  have hSnn : 0 ≤ Work.Kernels.scale τ := by unfold Work.Kernels.scale; positivity
  obtain ⟨c, N', hc, hflat0⟩ := hflat 0 le_rfl
  have hleft : IntegrableOn F (Set.Ioc (0 : ℝ) 1) := by
    refine Integrable.mono' (integrableOn_const (C := c * (Work.Kernels.scale τ) ^ N') (by simp))
      ?_ ?_
    · rw [hF]; exact (hmeasK.mul hmeasE).aestronglyMeasurable
    · filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      obtain ⟨ht0, ht1⟩ := ht
      rw [hF, norm_mul, norm_exp_neg_mul]
      have hb := hflat0 τ t hτ ht0 ht1
      have hexp_le : Real.exp (-(L * t)) ≤ 1 := by
        rw [← Real.exp_zero]
        exact Real.exp_le_exp.mpr (by nlinarith [hLpos, ht0])
      have hcS : 0 ≤ c * (Work.Kernels.scale τ) ^ N' :=
        mul_nonneg hc (Real.rpow_nonneg hSnn N')
      calc ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t‖ * Real.exp (-(L * t))
          ≤ (c * (Work.Kernels.scale τ) ^ N' * t ^ (0 : ℝ)) * 1 :=
            mul_le_mul hb hexp_le (Real.exp_nonneg _) (mul_nonneg hcS (Real.rpow_nonneg ht0.le 0))
        _ = c * (Work.Kernels.scale τ) ^ N' := by rw [mul_one, Real.rpow_zero, mul_one]
  have hPint : IntegrableOn (fun t : ℝ => (G 0 0 τ + (t : ℂ) * Complex.I * G 0 1 τ)
      * Complex.exp (-(L : ℂ) * (t : ℂ))) (Set.Ioi 1) :=
    integrableOn_affine_mul_exp_neg_mul_complex L hLpos _ _
  have hQint : IntegrableOn (fun t : ℝ => (G 1 0 τ + (t : ℂ) * Complex.I * G 1 1 τ)
      * Complex.exp (-(Mu : ℂ) * (t : ℂ))) (Set.Ioi 1) := by
    rcases hcase with h8d | h2
    · have hz10 : G 1 0 = 0 := h8 h8d 0
      have hz11 : G 1 1 = 0 := h8 h8d 1
      have hzero : (fun t : ℝ => (G 1 0 τ + (t : ℂ) * Complex.I * G 1 1 τ)
          * Complex.exp (-(Mu : ℂ) * (t : ℂ))) = fun _ => 0 := by
        funext t; rw [hz10, hz11]; simp
      rw [hzero]
      exact integrable_zero ℝ ℂ _
    · have hMu_pos : 0 < Mu := by
        rw [hMu, hL]
        have hr2 : 0 < r ^ 2 := by nlinarith
        nlinarith [Real.pi_pos, hr2]
      exact integrableOn_affine_mul_exp_neg_mul_complex Mu hMu_pos _ _
  have hAe_eq : ∀ t : ℝ, Aexp G τ t * Complex.exp (-(L : ℂ) * (t : ℂ))
      = (G 0 0 τ + (t : ℂ) * Complex.I * G 0 1 τ) * Complex.exp (-(L : ℂ) * (t : ℂ))
      + (G 1 0 τ + (t : ℂ) * Complex.I * G 1 1 τ) * Complex.exp (-(Mu : ℂ) * (t : ℂ)) := by
    intro t
    have hexp : Complex.exp (2 * Real.pi * t) * Complex.exp (-(L : ℂ) * (t : ℂ))
        = Complex.exp (-(Mu : ℂ) * (t : ℂ)) := by
      rw [← Complex.exp_add]
      congr 1
      rw [hMu, hL]
      push_cast
      ring
    simp only [Aexp]
    rw [add_mul, add_mul]
    rw [show (Complex.exp (2 * Real.pi * t) * (G 1 0 τ + (t : ℂ) * Complex.I * G 1 1 τ))
          * Complex.exp (-(L : ℂ) * (t : ℂ))
        = (G 1 0 τ + (t : ℂ) * Complex.I * G 1 1 τ)
          * (Complex.exp (2 * Real.pi * t) * Complex.exp (-(L : ℂ) * (t : ℂ))) from by ring,
      hexp]
  have hAeInt : IntegrableOn (fun t : ℝ => Aexp G τ t * Complex.exp (-(L : ℂ) * (t : ℂ)))
      (Set.Ioi 1) :=
    IntegrableOn.congr_fun (hPint.add hQint) (fun t _ => (hAe_eq t).symm) measurableSet_Ioi
  have hDiffInt : IntegrableOn (fun t : ℝ => (Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t
      - Aexp G τ t) * Complex.exp (-(L : ℂ) * (t : ℂ))) (Set.Ioi (1 : ℝ)) :=
    integrableOn_diff_mul_exp ℓ d hd G hT hτ hLpos
  have hFint1 : IntegrableOn F (Set.Ioi 1) := by
    have hpt : ∀ t : ℝ, Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t
        * Complex.exp (-(L : ℂ) * (t : ℂ))
        = Aexp G τ t * Complex.exp (-(L : ℂ) * (t : ℂ))
          + (Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t - Aexp G τ t)
            * Complex.exp (-(L : ℂ) * (t : ℂ)) := fun t => by ring
    exact IntegrableOn.congr_fun (hAeInt.add hDiffInt) (fun t _ => (hpt t).symm) measurableSet_Ioi
  have hunion : IntegrableOn F (Set.Ioc (0 : ℝ) 1 ∪ Set.Ioi 1) := hleft.union hFint1
  have hset : Set.Ioc (0 : ℝ) 1 ∪ Set.Ioi 1 = Set.Ioi 0 := by
    ext t; simp only [Set.mem_union, Set.mem_Ioc, Set.mem_Ioi]
    constructor
    · rintro (⟨h1, h2⟩ | h3)
      · exact h1
      · exact lt_trans zero_lt_one h3
    · intro h1
      by_cases h2 : t ≤ 1
      · exact Or.inl ⟨h1, h2⟩
      · exact Or.inr (lt_of_not_ge h2)
  rw [hset] at hunion
  refine IntegrableOn.congr_fun hunion (fun t _ => ?_) measurableSet_Ioi
  rw [hF, hargE t]


/-- **The `low + trunc + high` decomposition reproduces the contour integral, whenever the
Bochner integral converges.**  This is `Work.Asymptotics.paperLayer_agreement` with the hypothesis
on the tail replaced by the weaker consequences that hold under `TailBound`: the difference
`K - Aexp` is integrable against the Gaussian (from the two-regime bound), and the integral of
`Aexp·e^{-πr²t}` over `(1,∞)` is finite because it is the difference of the integrable
`t ↦ K(τ,it)e^{-πr²t}` and of that same integrable difference. -/
private lemma paperLayer_agreement_of_integrable (ℓ : Work.Kernels.LogLambdaData) (d : ℕ)
    (hd : d = 8 ∨ d = 24) (G : Fin 2 → Fin 2 → UpperHalfPlane → ℂ)
    (hG : ∀ i j : Fin 2, Work.Kernels.ModerateGrowthOn Work.Asymptotics.DomainD (G i j))
    (h8 : d = 8 → ∀ j : Fin 2, G 1 j = 0)
    (hT : Work.Asymptotics.TailBound ℓ d G) :
    ∀ (τ : UpperHalfPlane) (r : ℝ), τ ∈ Work.Asymptotics.DomainD → r ≠ 0 →
      MeasureTheory.IntegrableOn (fun t : ℝ => Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t
        * Complex.exp (-(Real.pi * (r : ℂ) ^ 2 * (t : ℂ)))) (Set.Ioi 0) →
      Work.Asymptotics.paperLayer G ℓ d τ r
        = Work.Kernels.kernelTransform (Work.Kernels.Kfun ℓ d) τ r := by
  intro τ r hτ hr hInt
  have hπpos : (0 : ℝ) < Real.pi := Real.pi_pos
  set L : ℝ := Real.pi * r ^ 2 with hL
  set Mu : ℝ := L - 2 * Real.pi with hMu
  have hLpos : 0 < L := by rw [hL]; positivity
  have hLne : L ≠ 0 := hLpos.ne'
  have hcosL : sinSq r = ((2 - 2 * Real.cos L : ℝ) : ℂ) := by
    rw [sinSq_eq_two_sub_two_cos r, hL]
  have hcosMu : sinSq r = ((2 - 2 * Real.cos Mu : ℝ) : ℂ) := by
    have h : Real.cos Mu = Real.cos (Real.pi * r ^ 2 - 2 * Real.pi) := by rw [hMu, hL]
    rw [sinSq_eq_two_sub_two_cos_sub r, h]
  set F : ℝ → ℂ := fun t => Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t
      * Complex.exp (-(Real.pi * (r : ℂ) ^ 2 * (t : ℂ))) with hF
  have hargE : ∀ t : ℝ, Complex.exp (-(Real.pi * (r : ℂ) ^ 2 * (t : ℂ)))
      = Complex.exp (-(L : ℂ) * (t : ℂ)) := by
    intro t
    congr 1
    rw [hL]; push_cast; ring
  have hF_eq : F = fun t : ℝ => Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t
      * Complex.exp (-(L : ℂ) * (t : ℂ)) := by
    funext t
    simp only [hF]
    rw [hargE t]
  set P : ℝ → ℂ := fun t => (G 0 0 τ + (t : ℂ) * Complex.I * G 0 1 τ)
      * Complex.exp (-(L : ℂ) * (t : ℂ)) with hP
  set Q : ℝ → ℂ := fun t => (G 1 0 τ + (t : ℂ) * Complex.I * G 1 1 τ)
      * Complex.exp (-(Mu : ℂ) * (t : ℂ)) with hQ
  have hAe_eq : ∀ t : ℝ, Aexp G τ t * Complex.exp (-(L : ℂ) * (t : ℂ)) = P t + Q t := by
    intro t
    have hexp : Complex.exp (2 * Real.pi * t) * Complex.exp (-(L : ℂ) * (t : ℂ))
        = Complex.exp (-(Mu : ℂ) * (t : ℂ)) := by
      rw [← Complex.exp_add]
      congr 1
      rw [hMu, hL]
      push_cast
      ring
    simp only [Aexp, hP, hQ]
    rw [add_mul, add_mul]
    rw [show (Complex.exp (2 * Real.pi * t) * (G 1 0 τ + (t : ℂ) * Complex.I * G 1 1 τ))
          * Complex.exp (-(L : ℂ) * (t : ℂ))
        = (G 1 0 τ + (t : ℂ) * Complex.I * G 1 1 τ)
          * (Complex.exp (2 * Real.pi * t) * Complex.exp (-(L : ℂ) * (t : ℂ))) from by ring,
      hexp]
  have hFint : IntegrableOn F (Set.Ioi 0) := by rw [hF]; exact hInt
  have hFint1 : IntegrableOn F (Set.Ioi 1) := hFint.mono_set (Set.Ioi_subset_Ioi zero_le_one)
  have hFint01 : IntegrableOn F (Set.Ioc 0 1) := hFint.mono_set Set.Ioc_subset_Ioi_self
  -- integrability of the tail `K - A`, from the two-regime tail bound
  have hDiffInt : IntegrableOn (fun t : ℝ => (Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t
      - Aexp G τ t) * Complex.exp (-(L : ℂ) * (t : ℂ))) (Set.Ioi (1 : ℝ)) :=
    integrableOn_diff_mul_exp ℓ d hd G hT hτ hLpos
  have hAeInt : IntegrableOn (fun t : ℝ => Aexp G τ t * Complex.exp (-(L : ℂ) * (t : ℂ)))
      (Set.Ioi 1) := by
    have h1 : IntegrableOn (fun t : ℝ => F t - (Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t
        - Aexp G τ t) * Complex.exp (-(L : ℂ) * (t : ℂ))) (Set.Ioi 1) :=
      Integrable.sub hFint1 hDiffInt
    refine IntegrableOn.congr_fun h1 (fun t _ => ?_) measurableSet_Ioi
    rw [hF_eq]
    ring
  -- the two moment integrals
  have hPint : IntegrableOn P (Set.Ioi 1) := by
    rw [hP]
    exact integrableOn_affine_mul_exp_neg_mul_complex L hLpos (G 0 0 τ) (G 0 1 τ)
  have hPval : ∫ t in Set.Ioi (1 : ℝ), P t
      = G 0 0 τ * (Complex.exp (-(L : ℂ)) / (L : ℂ))
        + (Complex.I * G 0 1 τ)
          * (Complex.exp (-(L : ℂ)) * ((L : ℂ) + 1) / (L : ℂ) ^ 2) := by
    rw [hP]
    exact integral_affine_mul_exp_neg_mul_Ioi_one hLpos (G 0 0 τ) (G 0 1 τ)
  have hmain : sinSq r * (∫ t in Set.Ioi (1 : ℝ),
        Aexp G τ t * Complex.exp (-(L : ℂ) * (t : ℂ))) = highPart G τ r := by
    by_cases hMu_pos : 0 < Mu
    · have hQint : IntegrableOn Q (Set.Ioi 1) := by
        rw [hQ]
        exact integrableOn_affine_mul_exp_neg_mul_complex Mu hMu_pos (G 1 0 τ) (G 1 1 τ)
      have hQval : ∫ t in Set.Ioi (1 : ℝ), Q t
          = G 1 0 τ * (Complex.exp (-(Mu : ℂ)) / (Mu : ℂ))
            + (Complex.I * G 1 1 τ)
              * (Complex.exp (-(Mu : ℂ)) * ((Mu : ℂ) + 1) / (Mu : ℂ) ^ 2) := by
        rw [hQ]
        exact integral_affine_mul_exp_neg_mul_Ioi_one hMu_pos (G 1 0 τ) (G 1 1 τ)
      have hAeval : ∫ t in Set.Ioi (1 : ℝ), Aexp G τ t * Complex.exp (-(L : ℂ) * (t : ℂ))
          = (∫ t in Set.Ioi (1 : ℝ), P t) + ∫ t in Set.Ioi (1 : ℝ), Q t := by
        rw [← integral_add hPint hQint]
        exact setIntegral_congr_fun measurableSet_Ioi (fun t _ => hAe_eq t)
      rw [hAeval, hPval, hQval, mul_add,
        sinSq_mul_closed hLne hcosL (Complex.exp (-(L : ℂ))) (G 0 0 τ) (Complex.I * G 0 1 τ),
        sinSq_mul_closed hMu_pos.ne' hcosMu (Complex.exp (-(Mu : ℂ))) (G 1 0 τ)
          (Complex.I * G 1 1 τ),
        highPart_eq_closed, hMu, hL]
      ring
    · have hMu_nonpos : Mu ≤ 0 := not_lt.mp hMu_pos
      have hQint : IntegrableOn Q (Set.Ioi 1) := by
        have h1 : IntegrableOn (fun t : ℝ =>
            Aexp G τ t * Complex.exp (-(L : ℂ) * (t : ℂ)) - P t) (Set.Ioi 1) :=
          Integrable.sub hAeInt hPint
        refine IntegrableOn.congr_fun h1 (fun t _ => ?_) measurableSet_Ioi
        rw [hAe_eq t]
        ring
      have hG10 : G 1 0 τ = 0 ∧ G 1 1 τ = 0 :=
        eq_zero_of_integrableOn_affine_mul_exp_neg hMu_nonpos hQint
      have hAevalP : ∫ t in Set.Ioi (1 : ℝ), Aexp G τ t * Complex.exp (-(L : ℂ) * (t : ℂ))
          = ∫ t in Set.Ioi (1 : ℝ), P t := by
        refine setIntegral_congr_fun measurableSet_Ioi (fun t _ => ?_)
        rw [hAe_eq t, hQ, hG10.1, hG10.2]
        ring
      rw [hAevalP, hPval,
        sinSq_mul_closed hLne hcosL (Complex.exp (-(L : ℂ))) (G 0 0 τ) (Complex.I * G 0 1 τ),
        highPart_eq_closed, hG10.1, hG10.2, hL]
      ring
  -- the telescoping
  have hsplit0 : ∫ t in Set.Ioi (0 : ℝ), F t
      = (∫ t in (0 : ℝ)..1, F t) + ∫ t in Set.Ioi (1 : ℝ), F t := by
    have hunion : ∫ t in Set.Ioc (0 : ℝ) 1 ∪ Set.Ioi (1 : ℝ), F t
        = (∫ t in Set.Ioc (0 : ℝ) 1, F t) + ∫ t in Set.Ioi (1 : ℝ), F t :=
      setIntegral_union (Set.disjoint_left.mpr (fun x hx1 hx2 => absurd hx1.2 (not_le.mpr hx2)))
        measurableSet_Ioi hFint01 hFint1
    have hset : Set.Ioc (0 : ℝ) 1 ∪ Set.Ioi (1 : ℝ) = Set.Ioi (0 : ℝ) := by
      ext x
      simp only [Set.mem_union, Set.mem_Ioc, Set.mem_Ioi]
      constructor
      · rintro (⟨h1, h2⟩ | h3)
        · exact h1
        · exact lt_trans zero_lt_one h3
      · intro h1
        by_cases h2 : x ≤ 1
        · exact Or.inl ⟨h1, h2⟩
        · exact Or.inr (lt_of_not_ge h2)
    rw [hset] at hunion
    rw [hunion, intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  have hsplit1 : ∫ t in Set.Ioi (1 : ℝ), F t
      = (∫ t in Set.Ioi (1 : ℝ), Aexp G τ t * Complex.exp (-(L : ℂ) * (t : ℂ)))
        + ∫ t in Set.Ioi (1 : ℝ), (Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t
          - Aexp G τ t) * Complex.exp (-(L : ℂ) * (t : ℂ)) := by
    rw [← integral_add hAeInt hDiffInt]
    exact setIntegral_congr_fun measurableSet_Ioi (fun t _ => by rw [hF_eq]; ring)
  have htruncIoi : ∫ t in Set.Ici (1 : ℝ), (Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t
        - Aexp G τ t) * Complex.exp (-(L : ℂ) * (t : ℂ))
      = ∫ t in Set.Ioi (1 : ℝ), (Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t
        - Aexp G τ t) * Complex.exp (-(L : ℂ) * (t : ℂ)) :=
    setIntegral_congr_set (Ioi_ae_eq_Ici' (by simp : volume ({(1 : ℝ)} : Set ℝ) = 0)).symm
  have hlow : layerLow ℓ d τ r = sinSq r * ∫ t in (0 : ℝ)..1, F t := by
    rw [layerLow, hF]
  have htrunc : layerTrunc G ℓ d τ r
      = sinSq r * ∫ t in Set.Ici (1 : ℝ), (Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t
          - Aexp G τ t) * Complex.exp (-(L : ℂ) * (t : ℂ)) := by
    rw [layerTrunc]
    congr 1
    exact setIntegral_congr_fun measurableSet_Ici (fun t _ => by rw [hargE t])
  rw [show Work.Kernels.kernelTransform (Work.Kernels.Kfun ℓ d) τ r
      = sinSq r * ∫ t in Set.Ioi (0 : ℝ), F t from by
        rw [Work.Kernels.kernelTransform, sinSq, hF]]
  rw [paperLayer, hlow, htrunc, htruncIoi, ← hmain, hsplit0, hsplit1]
  ring


/-- **The `low + trunc + high` decomposition reproduces the contour integral.**

The telescoping `∫_0^∞ = ∫_0^1 + ∫_1^∞ = ∫_0^1 + ∫_1^∞(K - A) + ∫_1^∞ A` together with the closed
form of `∫_1^∞ A(τ,it)e^{-πr²t}dt`, which is `highPart`: the double zeros of
`2 - 2cos(πr²) = 4 sin²(πr²/2)` at `λ = πr² = 0` and at `μ = πr² - 2π = 0` are exactly the factors
`psi1`, and `∫_1^∞ t^j e^{-νt}dt = e^{-ν}(ν+1)^j/ν^{j+1}`.

Clause 1 needs no `IntegrableOn` hypothesis: in the range `r ≠ 0 ∧ (d = 8 ∨ r² > 2)` the integrand
*is* integrable — on `(0,1]` by `hflat` (with `N = 0`), on `[1,∞)` because `K - Aexp` is polynomially
bounded and integrable against `e^{-πr²t}`, and the `Aexp` part converges exactly when `r² > 2` or
(the case `d = 8`) the coefficients `G 1 j` of `e^{2πt}` vanish by `h8`.  Clause 2 is the same
identity under a weaker hypothesis.  Note `r ≠ 0` is essential: at `r = 0` the layer takes the
finite value `i·G 0 1 τ ≠ 0` while `kernelTransform τ 0 = 0`. -/
theorem paperLayer_eq_kernelTransform (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (G : Fin 2 → Fin 2 → UpperHalfPlane → ℂ)
    (hG : ∀ i j : Fin 2, Work.Kernels.ModerateGrowthOn Work.Asymptotics.DomainD (G i j))
    (h8 : d = 8 → ∀ j : Fin 2, G 1 j = 0)
    (hflat : ∀ N : ℝ, 0 ≤ N → ∃ c N' : ℝ, 0 ≤ c ∧ ∀ (τ : UpperHalfPlane) (t : ℝ),
      τ ∈ Work.Asymptotics.DomainD → 0 < t → t ≤ 1 →
        ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t‖
          ≤ c * (Work.Kernels.scale τ) ^ N' * t ^ N)
    (hT : Work.Asymptotics.TailBound ℓ d G) :
    (∀ (τ : UpperHalfPlane) (r : ℝ), τ ∈ Work.Asymptotics.DomainD → r ≠ 0 →
      (d = 8 ∨ 2 < r ^ 2) →
      Work.Asymptotics.paperLayer G ℓ d τ r
        = Work.Kernels.kernelTransform (Work.Kernels.Kfun ℓ d) τ r) ∧
    (∀ (τ : UpperHalfPlane) (r : ℝ), τ ∈ Work.Asymptotics.DomainD → r ≠ 0 →
      MeasureTheory.IntegrableOn (fun t : ℝ => Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t
        * Complex.exp (-(Real.pi * (r : ℂ) ^ 2 * (t : ℂ)))) (Set.Ioi 0) →
      Work.Asymptotics.paperLayer G ℓ d τ r
        = Work.Kernels.kernelTransform (Work.Kernels.Kfun ℓ d) τ r) 
:= by
  constructor
  · intro τ r hτ hr hcase
    exact paperLayer_agreement_of_integrable ℓ d hd G hG h8 hT τ r hτ hr
      (integrableOn_kernelIntegrand ℓ d hd G h8 hflat hT hτ hr hcase)
  · intro τ r hτ hr hInt
    exact paperLayer_agreement_of_integrable ℓ d hd G hG h8 hT τ r hτ hr hInt

end Work.Asymptotics
