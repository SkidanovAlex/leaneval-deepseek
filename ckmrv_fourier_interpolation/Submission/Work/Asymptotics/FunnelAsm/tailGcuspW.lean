/-
# The funnel tail estimate with the cusp model `Gcusp ℓ d` (world-`A` copy)

A verbatim copy of `Work.Asymptotics.funnelKernelTailGcusp` from
`Submission/Work/Asymptotics/funnelTailSeminorm.lean`, with the import of the target module
`Submission.Work.Asymptotics.kernelTransform_seminorm_funnel` removed (the target module imports
*this* file, to break the import cycle) and the main theorem renamed to
`Work.Asymptotics.funnelKernelTailGcuspW`.  Nothing else is changed.
-/
import Mathlib
import Submission.Work.Asymptotics.funnelTailBasic
import Submission.Work.Asymptotics.funnelKernelTail
import Submission.Work.Asymptotics.EtailE.Assembly
import Submission.Work.Asymptotics.exists_seminorm_bound_of_iteratedDeriv_bound
import Submission.Work.Asymptotics.measurable_Kaxis_Kfun

namespace Work.Asymptotics

open UpperHalfPlane MeasureTheory Filter Topology
open scoped Topology ContDiff

noncomputable section

/-! ## The funnel tail estimate with the cusp model `Gcusp` -/

private theorem add_le_add_bounds' {S T e x1 x2 C1 C2 N1 N2 M1 M2 : ℝ}
    (hS : 1 ≤ S) (hT : 1 ≤ T) (he : 0 ≤ e) (hC1 : 0 ≤ C1) (hC2 : 0 ≤ C2)
    (h1 : x1 ≤ C1 * S ^ N1 * T ^ M1 * e) (h2 : x2 ≤ C2 * S ^ N2 * T ^ M2 * e) :
    x1 + x2 ≤ (C1 + C2) * S ^ (max N1 N2) * T ^ (max M1 M2) * e := by
  have hS0 : 0 ≤ S := le_trans zero_le_one hS
  have hT0 : 0 ≤ T := le_trans zero_le_one hT
  have hA : C1 * S ^ N1 * T ^ M1 * e ≤ C1 * S ^ (max N1 N2) * T ^ (max M1 M2) * e := by
    refine mul_le_mul_of_nonneg_right ?_ he
    have hs : S ^ N1 ≤ S ^ (max N1 N2) :=
      Real.rpow_le_rpow_of_exponent_le hS (le_max_left _ _)
    have ht : T ^ M1 ≤ T ^ (max M1 M2) :=
      Real.rpow_le_rpow_of_exponent_le hT (le_max_left _ _)
    calc C1 * S ^ N1 * T ^ M1 = (C1 * S ^ N1) * T ^ M1 := by ring
      _ ≤ (C1 * S ^ (max N1 N2)) * T ^ (max M1 M2) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hs hC1) ht
            (Real.rpow_nonneg hT0 _) (mul_nonneg hC1 (Real.rpow_nonneg hS0 _))
      _ = C1 * S ^ (max N1 N2) * T ^ (max M1 M2) := by ring
  have hB : C2 * S ^ N2 * T ^ M2 * e ≤ C2 * S ^ (max N1 N2) * T ^ (max M1 M2) * e := by
    refine mul_le_mul_of_nonneg_right ?_ he
    have hs : S ^ N2 ≤ S ^ (max N1 N2) :=
      Real.rpow_le_rpow_of_exponent_le hS (le_max_right _ _)
    have ht : T ^ M2 ≤ T ^ (max M1 M2) :=
      Real.rpow_le_rpow_of_exponent_le hT (le_max_right _ _)
    calc C2 * S ^ N2 * T ^ M2 = (C2 * S ^ N2) * T ^ M2 := by ring
      _ ≤ (C2 * S ^ (max N1 N2)) * T ^ (max M1 M2) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hs hC2) ht
            (Real.rpow_nonneg hT0 _) (mul_nonneg hC2 (Real.rpow_nonneg hS0 _))
      _ = C2 * S ^ (max N1 N2) * T ^ (max M1 M2) := by ring
  calc x1 + x2 ≤ C1 * S ^ N1 * T ^ M1 * e + C2 * S ^ N2 * T ^ M2 * e := add_le_add h1 h2
    _ ≤ C1 * S ^ (max N1 N2) * T ^ (max M1 M2) * e
          + C2 * S ^ (max N1 N2) * T ^ (max M1 M2) * e := add_le_add hA hB
    _ = (C1 + C2) * S ^ (max N1 N2) * T ^ (max M1 M2) * e := by ring

private theorem funnel_combine' {S T e x1 x2 C1 C2 N1 N2 M1 M2 : ℝ}
    (hS : 1 ≤ S) (hT : 1 ≤ T) (he : 0 ≤ e) (hC1 : 0 ≤ C1) (hC2 : 0 ≤ C2)
    (h1 : x1 ≤ C1 * S ^ N1 * T ^ M1 * e) (h2 : x2 ≤ C2 * S ^ N2 * T ^ M2 * e) :
    (x1 + x2) / 2 ≤ (C1 + C2) / 2 * S ^ (max N1 N2) * T ^ (max M1 M2) * e := by
  have h := add_le_add_bounds' hS hT he hC1 hC2 h1 h2
  have h2 := div_le_div_of_nonneg_right h (by norm_num : (0 : ℝ) ≤ 2)
  have hEq : ((C1 + C2) * S ^ (max N1 N2) * T ^ (max M1 M2) * e) / 2
      = (C1 + C2) / 2 * S ^ (max N1 N2) * T ^ (max M1 M2) * e := by ring
  rwa [hEq] at h2

set_option maxHeartbeats 1000000 in
/-- **The funnel tail estimate with the cusp model `Gcusp ℓ d`.** -/
theorem funnelKernelTailGcuspW (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24) :
    ∃ C N M : ℝ, 0 ≤ C ∧ 0 ≤ N ∧ 0 ≤ M ∧ ∀ (τ : UpperHalfPlane) (t : ℝ),
      Funnel τ → τ.im + 1 ≤ t →
      ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t - Aexp (Gcusp ℓ d) τ t‖
        ≤ C * (Work.Kernels.scale τ) ^ N * (1 + t) ^ M
            * Real.exp (-(Real.pi * (t - τ.im))) := by
  rcases hd with h8 | h24
  · subst h8
    obtain ⟨C1, N1, M1, hC1, hN1, hM1, hP⟩ := KPlus_funnel_tail_eight
    obtain ⟨C2, N2, M2, hC2, hN2, hM2, hM⟩ := KMinus_funnel_tail_eight ℓ
    refine ⟨(C1 + C2) / 2, max N1 N2, max M1 M2, by linarith, le_trans hN1 (le_max_left _ _),
      le_trans hM1 (le_max_left _ _), ?_⟩
    intro τ t hτ ht
    have ht0 : 0 < t := by have := hτ.2; linarith
    set z : UpperHalfPlane := Work.Kernels.imagAxis t ht0 with hzdef
    have hz : (z : ℂ) = (t : ℂ) * Complex.I := by rw [hzdef]; rfl
    have hKaxis : Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ 8) τ t
        = Work.Kernels.Kfun ℓ 8 τ z := by
      rw [Work.Kernels.Kaxis, dif_pos ht0, hzdef]
    have hA : Aexp (Gcusp ℓ 8) τ t = Compact.Gfun 8 ℓ τ z := by
      rw [Gcusp_eq_Gcoef ℓ 8 (Or.inl rfl), Aexp_Gcoef' ℓ 8 τ t ht0, hzdef]
    have hGfun : Compact.Gfun 8 ℓ τ z
        = (Compact.Gplus 8 τ z + Compact.Gminus 8 ℓ τ z) / 2 := by
      have h := Compact.gfun_eq ℓ 8 (Or.inl rfl) τ z
      rw [h]; ring
    have h1 := hP τ z t hτ ht hz
    have h2 := hM τ z t hτ ht hz
    rw [hKaxis, hA, Work.Kernels.Kfun_eq, hGfun]
    have hEq : ((Work.Kernels.KPlus 8 τ z + Work.Kernels.KMinus ℓ 8 τ z) / 2
          - (Compact.Gplus 8 τ z + Compact.Gminus 8 ℓ τ z) / 2)
        = ((Work.Kernels.KPlus 8 τ z - Compact.Gplus 8 τ z)
            + (Work.Kernels.KMinus ℓ 8 τ z - Compact.Gminus 8 ℓ τ z)) / 2 := by ring
    rw [hEq, norm_div, Complex.norm_ofNat]
    refine le_trans (div_le_div_of_nonneg_right (norm_add_le _ _) (by norm_num)) ?_
    exact funnel_combine' (Work.Kernels.one_le_scale τ) (by linarith) (Real.exp_nonneg _)
      hC1.le hC2.le h1 h2
  · subst h24
    obtain ⟨C1, N1, M1, hC1, hN1, hM1, hP⟩ := KPlus_funnel_tail_twentyfour
    obtain ⟨C2, N2, M2, hC2, hN2, hM2, hM⟩ := KMinus_funnel_tail_twentyfour ℓ
    refine ⟨(C1 + C2) / 2, max N1 N2, max M1 M2, by linarith, le_trans hN1 (le_max_left _ _),
      le_trans hM1 (le_max_left _ _), ?_⟩
    intro τ t hτ ht
    have ht0 : 0 < t := by have := hτ.2; linarith
    set z : UpperHalfPlane := Work.Kernels.imagAxis t ht0 with hzdef
    have hz : (z : ℂ) = (t : ℂ) * Complex.I := by rw [hzdef]; rfl
    have hKaxis : Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ 24) τ t
        = Work.Kernels.Kfun ℓ 24 τ z := by
      rw [Work.Kernels.Kaxis, dif_pos ht0, hzdef]
    have hA : Aexp (Gcusp ℓ 24) τ t = Compact.Gfun 24 ℓ τ z := by
      rw [Gcusp_eq_Gcoef ℓ 24 (Or.inr rfl), Aexp_Gcoef' ℓ 24 τ t ht0, hzdef]
    have hGfun : Compact.Gfun 24 ℓ τ z
        = (Compact.Gplus 24 τ z + Compact.Gminus 24 ℓ τ z) / 2 := by
      have h := Compact.gfun_eq ℓ 24 (Or.inr rfl) τ z
      rw [h]; ring
    have h1 := hP τ z t hτ ht hz
    have h2 := hM τ z t hτ ht hz
    rw [hKaxis, hA, Work.Kernels.Kfun_eq, hGfun]
    have hEq : ((Work.Kernels.KPlus 24 τ z + Work.Kernels.KMinus ℓ 24 τ z) / 2
          - (Compact.Gplus 24 τ z + Compact.Gminus 24 ℓ τ z) / 2)
        = ((Work.Kernels.KPlus 24 τ z - Compact.Gplus 24 τ z)
            + (Work.Kernels.KMinus ℓ 24 τ z - Compact.Gminus 24 ℓ τ z)) / 2 := by ring
    rw [hEq, norm_div, Complex.norm_ofNat]
    refine le_trans (div_le_div_of_nonneg_right (norm_add_le _ _) (by norm_num)) ?_
    exact funnel_combine' (Work.Kernels.one_le_scale τ) (by linarith) (Real.exp_nonneg _)
      hC1.le hC2.le h1 h2

/-! ## The shifted exponential factor `x ↦ e^{-π x c}` -/

/-- The exponential factor `x ↦ e^{-πxc}` of the funnel tail, written in the form in which its
iterated derivatives have a closed formula. -/
private def expFac (c : ℝ) : ℝ → ℂ := fun x => Complex.exp (((-(Real.pi * c)) * x : ℝ) : ℂ)

private lemma expFac_apply (c x : ℝ) :
    expFac c x = Complex.exp (((-(Real.pi * c)) * x : ℝ) : ℂ) := rfl

private lemma expFac_eq_ofReal (c x : ℝ) :
    expFac c x = (Real.exp (-(Real.pi * x * c)) : ℂ) := by
  show Complex.exp (((-(Real.pi * c)) * x : ℝ) : ℂ) = (Real.exp (-(Real.pi * x * c)) : ℂ)
  rw [← Complex.ofReal_exp]
  congr 1
  push_cast
  ring

private lemma expFac_add (c u x : ℝ) :
    expFac (u + c) x = expFac c x * expFac u x := by
  show Complex.exp (((-(Real.pi * (u + c))) * x : ℝ) : ℂ)
    = Complex.exp (((-(Real.pi * c)) * x : ℝ) : ℂ)
      * Complex.exp (((-(Real.pi * u)) * x : ℝ) : ℂ)
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

private lemma wgt_eq_expFac (x t : ℝ) : Complex.exp (-(Real.pi * x * t : ℝ)) = expFac t x := by
  show Complex.exp (-(Real.pi * x * t : ℝ)) = Complex.exp (((-(Real.pi * t)) * x : ℝ) : ℂ)
  congr 1
  push_cast
  ring

/-- The derivative of `y ↦ e^{ay}` (complex exponential of a real multiple of `y`). -/
private lemma hasDerivAt_expFac (a x : ℝ) :
    HasDerivAt (fun y : ℝ => Complex.exp (((a * y : ℝ)) : ℂ))
      (Complex.exp (((a * x : ℝ)) : ℂ) * (a : ℂ)) x := by
  have h1 : HasDerivAt (fun y : ℝ => a * y) a x := by
    simpa using (hasDerivAt_id x).const_mul a
  have h2 : HasDerivAt (fun y : ℝ => Real.exp (a * y)) (Real.exp (a * x) * a) x := h1.exp
  have h3 := h2.ofReal_comp
  have hfun : (fun y : ℝ => ((Real.exp (a * y)) : ℂ))
      = fun y : ℝ => Complex.exp (((a * y : ℝ)) : ℂ) := by
    funext y
    rw [Complex.ofReal_exp]
  have hval : ((Real.exp (a * x) * a : ℝ) : ℂ)
      = Complex.exp (((a * x : ℝ)) : ℂ) * (a : ℂ) := by
    have h1 : ((Real.exp (a * x) * a : ℝ) : ℂ) = ((Real.exp (a * x) : ℂ)) * (a : ℂ) := by
      push_cast
      ring
    rw [h1, Complex.ofReal_exp]
  rw [hfun, hval] at h3
  exact h3

/-- The iterated derivatives of `y ↦ e^{ay}`. -/
private lemma iteratedDeriv_expFac (a x : ℝ) (j : ℕ) :
    iteratedDeriv j (fun y : ℝ => Complex.exp (((a * y : ℝ)) : ℂ)) x
      = ((a : ℂ)) ^ j * Complex.exp (((a * x : ℝ)) : ℂ) := by
  induction j generalizing x with
  | zero => rw [iteratedDeriv_zero]; ring
  | succ k ih =>
    have hfun : iteratedDeriv k (fun y : ℝ => Complex.exp (((a * y : ℝ)) : ℂ))
        = fun y : ℝ => ((a : ℂ)) ^ k * Complex.exp (((a * y : ℝ)) : ℂ) := funext ih
    rw [iteratedDeriv_succ, hfun]
    have hd : HasDerivAt (fun y : ℝ => (a : ℂ) ^ k * Complex.exp (((a * y : ℝ)) : ℂ))
        ((a : ℂ) ^ k * (Complex.exp (((a * x : ℝ)) : ℂ) * (a : ℂ))) x :=
      (hasDerivAt_expFac a x).const_mul ((a : ℂ) ^ k)
    rw [hd.deriv]
    ring

/-- `‖(e^{-π x c})^{(j)}‖ ≤ (πc)^j` for `c, x ≥ 0`. -/
private lemma norm_iteratedDeriv_expFac_le (c : ℝ) (hc : 0 ≤ c) (j : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    ‖iteratedDeriv j (expFac c) x‖ ≤ (Real.pi * c) ^ j := by
  have hfuneq : expFac c = fun y : ℝ => Complex.exp ((((-(Real.pi * c)) * y : ℝ)) : ℂ) := rfl
  rw [hfuneq, iteratedDeriv_expFac, norm_mul, norm_pow]
  have h1 : ‖((-(Real.pi * c) : ℝ) : ℂ)‖ = Real.pi * c := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_neg, abs_of_nonneg (by positivity)]
  have h2 : ‖Complex.exp ((((-(Real.pi * c)) * x : ℝ)) : ℂ)‖ ≤ 1 := by
    rw [← Complex.ofReal_exp, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
      Real.exp_le_one_iff]
    have h3 : 0 ≤ Real.pi * c * x := mul_nonneg (mul_nonneg Real.pi_pos.le hc) hx
    linarith
  rw [h1]
  calc (Real.pi * c) ^ j * ‖Complex.exp ((((-(Real.pi * c)) * x : ℝ)) : ℂ)‖
      ≤ (Real.pi * c) ^ j * 1 := mul_le_mul_of_nonneg_left h2 (by positivity)
    _ = (Real.pi * c) ^ j := by ring

/-! ## Shifting the contour integral -/

/-- Change of variable `t = u + c` in a Bochner integral over `(c + 1, ∞)`. -/
private lemma setIntegral_Ioi_add (g : ℝ → ℂ) (c : ℝ) :
    ∫ t in Set.Ioi (c + 1), g t = ∫ u in Set.Ioi (1 : ℝ), g (u + c) := by
  have hshift : ∫ x : ℝ, (Set.Ioi (c + 1)).indicator g (x + c)
      = ∫ x : ℝ, (Set.Ioi (c + 1)).indicator g x :=
    integral_add_right_eq_self (μ := volume) ((Set.Ioi (c + 1)).indicator g) c
  have hfun : (fun x : ℝ => (Set.Ioi (c + 1)).indicator g (x + c))
      = (Set.Ioi (1 : ℝ)).indicator (fun u : ℝ => g (u + c)) := by
    funext x
    by_cases h : x + c ∈ Set.Ioi (c + 1)
    · have hx : x ∈ Set.Ioi (1 : ℝ) := by rw [Set.mem_Ioi] at h ⊢; linarith
      rw [Set.indicator_of_mem h, Set.indicator_of_mem hx]
    · have hx : x ∉ Set.Ioi (1 : ℝ) := by
        rw [Set.mem_Ioi, not_lt] at h ⊢
        linarith
      rw [Set.indicator_of_notMem h, Set.indicator_of_notMem hx]
  rw [← integral_indicator (s := Set.Ioi (1 : ℝ)) (f := fun u : ℝ => g (u + c)) measurableSet_Ioi,
    ← hfun, hshift,
    ← integral_indicator (s := Set.Ioi (c + 1)) (f := g) measurableSet_Ioi]

/-- `Set.Ioi 1` and `Set.Ici 1` agree almost everywhere. -/
private lemma ae_eq_Ioi_Ici_one : Set.Ioi (1 : ℝ) =ᵐ[volume] Set.Ici (1 : ℝ) := by
  rw [MeasureTheory.ae_eq_set]
  constructor
  · have h : Set.Ioi (1:ℝ) \ Set.Ici (1:ℝ) = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro x hx
      exact hx.2 (Set.mem_Ici.mpr (le_of_lt (Set.mem_Ioi.mp hx.1)))
    rw [h, measure_empty]
  · have h : Set.Ici (1:ℝ) \ Set.Ioi (1:ℝ) = {1} := by
      ext x
      constructor
      · intro hx
        rw [Set.mem_singleton_iff]
        refine le_antisymm ?_ (Set.mem_Ici.mp hx.1)
        exact not_lt.mp (fun hlt => hx.2 (Set.mem_Ioi.mpr hlt))
      · intro hx
        rw [Set.mem_singleton_iff] at hx
        subst hx
        exact ⟨Set.mem_Ici.mpr le_rfl, by simp⟩
    rw [h, MeasureTheory.measure_singleton]

/-- The tail integral as a shifted product of an exponential factor and the standard
`tailIntegral` on `(1, ∞)`. -/
private lemma tailIoi_eq_expFac_mul_tailIntegral (A : ℝ → ℂ) (c x : ℝ) :
    ∫ t in Set.Ioi (c + 1), A t * expFac t x
      = expFac c x * tailIntegral (fun u : ℝ => A (u + c)) x := by
  rw [setIntegral_Ioi_add (fun t : ℝ => A t * expFac t x) c]
  have h1 : (fun u : ℝ => A (u + c) * expFac (u + c) x)
      = fun u : ℝ => expFac c x * (A (u + c) * expFac u x) := by
    funext u
    rw [expFac_add c u x]
    ring
  rw [h1, MeasureTheory.integral_const_mul]
  congr 1
  rw [tailIntegral]
  refine (setIntegral_congr_set ae_eq_Ioi_Ici_one).trans ?_
  exact setIntegral_congr_fun measurableSet_Ici (fun u _ => by rw [expFac_eq_ofReal])

/-! ## The amplitude on the shifted contour -/

/-- The amplitude `t ↦ K(τ,it) - Aexp(τ,it)` of the funnel tail, evaluated at `t = u + Im τ`. -/
private def tailAmp (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (τ : UpperHalfPlane) : ℝ → ℂ :=
  fun u => Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ (u + τ.im)
    - Aexp (Gcusp ℓ d) τ (u + τ.im)

private lemma continuous_Aexp_t (G : Fin 2 → Fin 2 → UpperHalfPlane → ℂ) (τ : UpperHalfPlane) :
    Continuous fun t : ℝ => Aexp G τ t := by
  unfold Aexp
  fun_prop

end

end Work.Asymptotics
