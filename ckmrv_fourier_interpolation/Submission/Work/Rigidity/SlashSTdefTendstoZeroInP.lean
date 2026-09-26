import Mathlib
import Submission.Work.Rigidity.Diff
import Submission.Work.Rigidity.FstDiffTraceFour
import Submission.Work.Rigidity.boundedAtImInfty_of_periodic_inP
import Submission.Work.Rigidity.BoundedAtImInftyPeriodicInP
import Submission.Work.Kernels.Slash

namespace Work.Rigidity

open UpperHalfPlane ModularForm ModularGroup Matrix
open scoped MatrixGroups ModularForm Modular Manifold Bundle Topology

noncomputable section

open Filter

/-! ## Elementary helpers -/

/-- The slash action of `T` at any weight is translation by `1`. -/
lemma slash_T_eq_shift (k : ℤ) (F : ℍ → ℂ) :
    F ∣[k] ModularGroup.T = fun τ : ℍ => F ((1 : ℝ) +ᵥ τ) := by
  funext τ
  rw [Work.Kernels.slash_apply', Work.Kernels.jFun_apply, UpperHalfPlane.modular_T_smul]
  have h10 : (ModularGroup.T : Matrix.SpecialLinearGroup (Fin 2) ℤ) 1 0 = 0 := by decide
  have h11 : (ModularGroup.T : Matrix.SpecialLinearGroup (Fin 2) ℤ) 1 1 = 1 := by decide
  rw [h10, h11]
  simp

/-- Invariance under translation by a natural number, from invariance under `τ ↦ τ + 1`. -/
lemma vadd_nat_of_vadd_one {F : ℍ → ℂ} (h : ∀ τ : ℍ, F ((1 : ℝ) +ᵥ τ) = F τ)
    (n : ℕ) (τ : ℍ) : F ((n : ℝ) +ᵥ τ) = F τ := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show (((n + 1 : ℕ) : ℝ)) +ᵥ τ = (1 : ℝ) +ᵥ ((n : ℝ) +ᵥ τ) by
      ext <;> simp only [UpperHalfPlane.coe_vadd]; push_cast; ring]
    rw [h, ih]

/-- Invariance under translation by an integer. -/
lemma vadd_int_of_vadd_one {F : ℍ → ℂ} (h : ∀ τ : ℍ, F ((1 : ℝ) +ᵥ τ) = F τ)
    (m : ℤ) (τ : ℍ) : F ((m : ℝ) +ᵥ τ) = F τ := by
  rcases m with m | m
  · exact vadd_nat_of_vadd_one h m τ
  · have hcast : ((Int.negSucc m : ℤ) : ℝ) = -(((m + 1 : ℕ)) : ℝ) := by push_cast; ring
    rw [hcast]
    have hv : (((m + 1 : ℕ) : ℝ) +ᵥ ((-(((m + 1 : ℕ)) : ℝ)) +ᵥ τ) : ℍ) = τ := by
      rw [← add_vadd]; norm_num
    have hh := vadd_nat_of_vadd_one h (m + 1) ((-(((m + 1 : ℕ)) : ℝ)) +ᵥ τ)
    rw [hv] at hh
    exact hh.symm

/-- Every point of `ℍ` is an integer translate of a point of the strip `-1 ≤ Re ≤ 1`. -/
lemma exists_int_vadd_mem_strip (τ : ℍ) : ∃ n : ℤ, InStrip ((n : ℝ) +ᵥ τ) := by
  refine ⟨-(⌊τ.re⌋), ?_, ?_⟩
  · have h : (((-(⌊τ.re⌋) : ℤ) : ℝ) +ᵥ τ : ℍ).re = τ.re - ((⌊τ.re⌋ : ℤ) : ℝ) := by
      rw [← UpperHalfPlane.coe_re, UpperHalfPlane.coe_vadd]
      simp only [Complex.add_re, Complex.ofReal_re]
      rw [UpperHalfPlane.coe_re]
      push_cast
      ring
    rw [h]
    have := Int.floor_le τ.re
    linarith
  · have h : (((-(⌊τ.re⌋) : ℤ) : ℝ) +ᵥ τ : ℍ).re = τ.re - ((⌊τ.re⌋ : ℤ) : ℝ) := by
      rw [← UpperHalfPlane.coe_re, UpperHalfPlane.coe_vadd]
      simp only [Complex.add_re, Complex.ofReal_re]
      rw [UpperHalfPlane.coe_re]
      push_cast
      ring
    rw [h]
    have := Int.lt_floor_add_one τ.re
    linarith

/-- `𝕢 h` is multiplicative: `𝕢 h (z + w) = 𝕢 h z * 𝕢 h w`. -/
lemma qParam_add (h : ℝ) (z w : ℂ) :
    Function.Periodic.qParam h (z + w)
      = Function.Periodic.qParam h z * Function.Periodic.qParam h w := by
  simp only [Function.Periodic.qParam]
  rw [← Complex.exp_add]
  congr 1
  ring

/-- `𝕢 2 1 = -1`. -/
lemma qParam_two_one : Function.Periodic.qParam 2 (1 : ℂ) = -1 := by
  simp only [Function.Periodic.qParam]
  rw [show 2 * (↑Real.pi : ℂ) * Complex.I * (1 : ℂ) / ((2 : ℝ) : ℂ)
        = ↑Real.pi * Complex.I by
      rw [mul_one]; push_cast; ring]
  exact Complex.exp_pi_mul_I

/-- `𝕢 2 (z + 1) = -𝕢 2 z`. -/
lemma qParam_two_add_one (z : ℂ) :
    Function.Periodic.qParam 2 (z + 1) = -Function.Periodic.qParam 2 z := by
  rw [qParam_add, qParam_two_one]
  ring

/-- Periodicity with respect to translation `· +ᵥ ·` on `ℍ` descends to `Function.Periodic`
of the composition with `ofComplex`. -/
lemma periodic_comp_ofComplex_of_vadd {h : ℝ} {F : ℍ → ℂ}
    (hper : ∀ τ : ℍ, F (h +ᵥ τ) = F τ) :
    Function.Periodic (F ∘ UpperHalfPlane.ofComplex) h := by
  intro z
  simp only [Function.comp_apply]
  by_cases hz : 0 < z.im
  · have hz' : 0 < (z + h).im := by
      rw [Complex.add_im, Complex.ofReal_im, add_zero]; exact hz
    rw [UpperHalfPlane.ofComplex_apply_of_im_pos hz',
      UpperHalfPlane.ofComplex_apply_of_im_pos hz]
    have hcoe : (⟨z + h, hz'⟩ : ℍ) = h +ᵥ (⟨z, hz⟩ : ℍ) := by
      apply UpperHalfPlane.coe_inj.mp
      rw [UpperHalfPlane.coe_vadd]
      push_cast
      ring
    rw [hcoe, hper]
  · have hzle : z.im ≤ 0 := not_lt.mp hz
    have hz'' : (z + h).im ≤ 0 := by
      rw [Complex.add_im, Complex.ofReal_im, add_zero]; exact hzle
    rw [UpperHalfPlane.ofComplex_apply_eq_of_im_nonpos hz'' hzle]

/-! ## The main theorem -/

theorem SlashSTdefTendstoZeroInP {f : UpperHalfPlane → ℂ} (hP : Work.Kernels.InP f)
    (hT2 : Work.Rigidity.AnnT2 f) (hS : Work.Rigidity.SlashEigen 4 (1 : ℂ) f)
    (hdec : Work.Rigidity.StripDecay 0 f) :
    UpperHalfPlane.IsZeroAtImInfty
      (fun τ : UpperHalfPlane => (τ : ℂ) ^ (-4 : ℤ) * Work.Rigidity.fstDiff f (ModularGroup.S • τ)) := by
  set u : ℍ → ℂ := Work.Rigidity.fstDiff f with hu
  set H : ℍ → ℂ := fun τ => (τ : ℂ) ^ (-4 : ℤ) * u (ModularGroup.S • τ) with hH
  set K : ℍ → ℂ := fun τ => H τ + (1 / 2) * u τ with hK
  have hper_u : ∀ τ : ℍ, u ((1 : ℝ) +ᵥ τ) = u τ := by
    simpa only [hu] using (Work.Rigidity.fstDiff_vadd_one_iff f).mp hT2
  have hu2 : ∀ τ : ℍ, u ((2 : ℝ) +ᵥ τ) = u τ := by
    intro σ
    rw [show (2 : ℝ) +ᵥ σ = (1 : ℝ) +ᵥ ((1 : ℝ) +ᵥ σ) by rw [← add_vadd]; norm_num,
      hper_u ((1 : ℝ) +ᵥ σ), hper_u σ]
  have hP_u : Work.Kernels.InP u := by
    have h1 : Work.Rigidity.fstDiff f = f ∣[(4 : ℤ)] ModularGroup.T - f := by
      funext τ
      simp only [Pi.sub_apply, Work.Rigidity.fstDiff_apply, slash_T_eq_shift]
    rw [hu, h1]
    exact (Work.Kernels.InP.slash hP (4 : ℤ) ModularGroup.T).sub hP
  have hP_H : Work.Kernels.InP H := by
    have h2 : H = u ∣[(4 : ℤ)] ModularGroup.S := by
      funext τ
      simp only [hH, Work.Rigidity.slash_S_apply]
    rw [h2]
    exact Work.Kernels.InP.slash hP_u (4 : ℤ) ModularGroup.S
  have hP_K : Work.Kernels.InP K := by
    have h3 := hP_H.add (hP_u.const_mul (1 / 2))
    rw [hK]
    exact h3
  have hmd_K : MDiff K := hP_K.1
  have htrace : ∀ τ : ℍ, H τ + H ((1 : ℝ) +ᵥ τ) = -u τ := by
    intro τ
    have h := Work.Rigidity.FstDiffTraceFour hT2 hS τ
    have hcoe : ((((1 : ℝ) +ᵥ τ : ℍ)) : ℂ) = (τ : ℂ) + 1 := by
      rw [UpperHalfPlane.coe_vadd, Complex.ofReal_one]; ring
    have e1 : H τ
        = (τ : ℂ) ^ (-4 : ℤ) * Work.Rigidity.fstDiff f (ModularGroup.S • τ) := by
      simp only [hH, hu]
    have e2 : H ((1 : ℝ) +ᵥ τ)
        = ((τ : ℂ) + 1) ^ (-4 : ℤ)
            * Work.Rigidity.fstDiff f (ModularGroup.S • ((1 : ℝ) +ᵥ τ)) := by
      simp only [hH, hu]
      rw [hcoe]
    have e3 : u τ = Work.Rigidity.fstDiff f τ := by rw [hu]
    rw [e1, e2, e3]
    linear_combination h
  have hH2 : ∀ τ : ℍ, H ((2 : ℝ) +ᵥ τ) = H τ := by
    intro τ
    rw [show (2 : ℝ) +ᵥ τ = (1 : ℝ) +ᵥ ((1 : ℝ) +ᵥ τ) by rw [← add_vadd]; norm_num]
    have h1 := htrace ((1 : ℝ) +ᵥ τ)
    have h2 := htrace τ
    rw [hper_u τ] at h1
    linear_combination h1 - h2
  have hKper2 : ∀ τ : ℍ, K ((2 : ℝ) +ᵥ τ) = K τ := by
    intro τ
    simp only [hK]
    rw [hH2 τ, hu2 τ]
  have hKanti : ∀ τ : ℍ, K ((1 : ℝ) +ᵥ τ) = -K τ := by
    intro τ
    have h1 : H ((1 : ℝ) +ᵥ τ) = -u τ - H τ := by linear_combination htrace τ
    simp only [hK]
    rw [h1, hper_u τ]
    ring
  have hbdd_K : UpperHalfPlane.IsBoundedAtImInfty K :=
    Work.Rigidity.BoundedAtImInftyPeriodicInP (h := 2) (by norm_num) hP_K hKper2
  have hpercomp : Function.Periodic (K ∘ UpperHalfPlane.ofComplex) 2 :=
    periodic_comp_ofComplex_of_vadd hKper2
  have hana : AnalyticAt ℂ (UpperHalfPlane.cuspFunction 2 K) 0 :=
    UpperHalfPlane.analyticAt_cuspFunction_zero (h := 2) (by norm_num) hpercomp hmd_K hbdd_K
  have heq : ∀ τ : ℍ,
      K τ = UpperHalfPlane.cuspFunction 2 K (Function.Periodic.qParam 2 (τ : ℂ)) :=
    fun τ => (UpperHalfPlane.eq_cuspFunction (h := 2) τ (by norm_num) hpercomp).symm
  have hrel : ∀ τ : ℍ,
      UpperHalfPlane.cuspFunction 2 K (-(Function.Periodic.qParam 2 (τ : ℂ)))
        = -UpperHalfPlane.cuspFunction 2 K (Function.Periodic.qParam 2 (τ : ℂ)) := by
    intro τ
    have hq : Function.Periodic.qParam 2 ((((1 : ℝ) +ᵥ τ : ℍ)) : ℂ)
        = -(Function.Periodic.qParam 2 (τ : ℂ)) := by
      rw [UpperHalfPlane.coe_vadd, Complex.ofReal_one, add_comm]
      exact qParam_two_add_one (τ : ℂ)
    rw [← hq, ← heq ((1 : ℝ) +ᵥ τ), hKanti τ, heq τ]
  have hK0 : UpperHalfPlane.cuspFunction 2 K 0 = 0 := by
    have hcont : ContinuousAt (UpperHalfPlane.cuspFunction 2 K) 0 := hana.continuousAt
    have htend : Tendsto (fun τ : ℍ => Function.Periodic.qParam 2 (τ : ℂ)) atImInfty (𝓝 0) :=
      UpperHalfPlane.qParam_tendsto_atImInfty (h := 2) (by norm_num)
    have hneg : Tendsto (fun τ : ℍ => -(Function.Periodic.qParam 2 (τ : ℂ))) atImInfty (𝓝 0) := by
      simpa using htend.neg
    have hL : Tendsto
        (fun τ : ℍ => UpperHalfPlane.cuspFunction 2 K (Function.Periodic.qParam 2 (τ : ℂ))
          + UpperHalfPlane.cuspFunction 2 K (-(Function.Periodic.qParam 2 (τ : ℂ))))
        atImInfty (𝓝 ((UpperHalfPlane.cuspFunction 2 K) 0 + (UpperHalfPlane.cuspFunction 2 K) 0)) :=
      (hcont.tendsto.comp htend).add (hcont.tendsto.comp hneg)
    have hL0 : (fun τ : ℍ =>
          UpperHalfPlane.cuspFunction 2 K (Function.Periodic.qParam 2 (τ : ℂ))
          + UpperHalfPlane.cuspFunction 2 K (-(Function.Periodic.qParam 2 (τ : ℂ))))
        = fun _ => (0 : ℂ) := by
      funext τ
      rw [hrel τ]
      ring
    have hL' : Tendsto (fun _ : ℍ => (0 : ℂ)) atImInfty
        (𝓝 ((UpperHalfPlane.cuspFunction 2 K) 0 + (UpperHalfPlane.cuspFunction 2 K) 0)) := by
      rw [← hL0]; exact hL
    have hsum : (UpperHalfPlane.cuspFunction 2 K) 0 + (UpperHalfPlane.cuspFunction 2 K) 0 = 0 :=
      tendsto_nhds_unique hL' tendsto_const_nhds
    have h2 : (2 : ℂ) * (UpperHalfPlane.cuspFunction 2 K) 0 = 0 := by
      rw [two_mul]; exact hsum
    exact (mul_eq_zero.mp h2).resolve_left two_ne_zero
  have hzero_K : UpperHalfPlane.IsZeroAtImInfty K := by
    show Tendsto K atImInfty (𝓝 0)
    have htend : Tendsto (fun τ : ℍ => Function.Periodic.qParam 2 (τ : ℂ)) atImInfty (𝓝 0) :=
      UpperHalfPlane.qParam_tendsto_atImInfty (h := 2) (by norm_num)
    have h1 : Tendsto
        (fun τ : ℍ => UpperHalfPlane.cuspFunction 2 K (Function.Periodic.qParam 2 (τ : ℂ)))
        atImInfty (𝓝 0) := by
      have hh := hana.continuousAt.tendsto.comp htend
      rwa [hK0] at hh
    rw [show K = fun τ : ℍ =>
        UpperHalfPlane.cuspFunction 2 K (Function.Periodic.qParam 2 (τ : ℂ)) from funext heq]
    exact h1
  have hzero_u : UpperHalfPlane.IsZeroAtImInfty u := by
    have hdec_u : StripDecay 0 u := by
      rw [hu]; exact Work.Rigidity.fstDiff_stripDecay hT2 hdec
    obtain ⟨φ, hφ, hφ'⟩ := hdec_u
    rw [UpperHalfPlane.isZeroAtImInfty_iff]
    intro ε hε
    obtain ⟨A, hA⟩ : ∃ A : ℝ, ∀ y : ℝ, A ≤ y → φ y < ε := by
      obtain ⟨A, hA⟩ := Metric.tendsto_atTop.1 hφ ε hε
      exact ⟨A, fun y hy => by
        have h := hA y hy
        rw [Real.dist_eq, sub_zero, abs_lt] at h
        exact h.2⟩
    refine ⟨max A 1, fun τ hτ => ?_⟩
    obtain ⟨n, hn⟩ := exists_int_vadd_mem_strip τ
    have hσim : (((n : ℝ) +ᵥ τ : ℍ)).im = τ.im := Work.Rigidity.im_vadd n τ
    have huσ : u ((n : ℝ) +ᵥ τ) = u τ := vadd_int_of_vadd_one hper_u n τ
    have hb := hφ' ((n : ℝ) +ᵥ τ) hn
    have hexp : Real.exp (-(2 * Real.pi * 0 * (((n : ℝ) +ᵥ τ : ℍ)).im)) = 1 := by norm_num
    rw [hexp, mul_one] at hb
    rw [← huσ]
    exact le_trans hb (le_of_lt (hA _ (by rw [hσim]; exact le_trans (le_max_left _ _) hτ)))
  have hzero_H : UpperHalfPlane.IsZeroAtImInfty H := by
    have hmem : (K - (1 / 2 : ℂ) • u) ∈ UpperHalfPlane.zeroAtImInftySubmodule ℂ :=
      Submodule.sub_mem _ hzero_K (Submodule.smul_mem _ (1 / 2 : ℂ) hzero_u)
    have hfun : H = K - (1 / 2 : ℂ) • u := by
      funext τ
      rw [hK, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      ring
    rw [hfun]
    exact hmem
  simpa only [hH, hu] using hzero_H

end

end Work.Rigidity
