import Mathlib
import Submission.Work.Asymptotics.KhatE1.Kdev24Lead
import Submission.Work.Asymptotics.KhatE1Core.Kdev8_rem_sharp
import Submission.Work.Asymptotics.KhatE1.Kdev24LeadProp_proof
import Submission.Work.Asymptotics.KhatE1.Kdev8CoeffAux
import Submission.Work.Asymptotics.KhatE1.Kdev24RemCore
import Submission.Work.Asymptotics.KhatE1.KdevRem_strip_sharp
import Submission.Work.Asymptotics.KhatE1.KdevRemDefs
import Submission.Work.Asymptotics.KhatE1Defs
import Submission.Work.Asymptotics.KEpsilon
import Submission.Work.Asymptotics.KhatE1.STPure
import Submission.Work.Asymptotics.Compact.gfun_eq
import Submission.Work.Asymptotics.KhatE1.E1combo8_bound
import Submission.Work.Asymptotics.KhatE1.E1combo24_bound
import Submission.Work.Asymptotics.Compact.kminus_tail_core
import Submission.Work.Asymptotics.KMFDDefs
import Submission.Work.Asymptotics.EtailE.EtailE_KMinus24
import Submission.Work.Asymptotics.KhatE1.Kdev_funnel_of_leading_core
import Submission.Work.Kernels.LogLambda.ThetaLower.theta_lower_bound
import Submission.Work.Asymptotics.jInvariantFun_eq_smul_of_eq
import Submission.Work.Asymptotics.KPlusXiDefs
import Submission.Work.Asymptotics.CuspL_eq
import Submission.Work.Asymptotics.KhatE1.B0Defs
import Submission.Work.Asymptotics.KhatE1Core.psi_individual_first_order
import Submission.Work.Asymptotics.KhatE1Core.psi_combo_first_order
import Submission.Work.Asymptotics.funnelTailBasic

set_option maxHeartbeats 4000000

namespace Work.Asymptotics.KhatE1

open UpperHalfPlane


/-- `E₄ + 1 = O(1)`. -/
private lemma isBigOq_E4_add_one :
    Work.Asymptotics.IsBigOq (fun τ : ℍ => Work.Kernels.E4Fun τ + 1) 0 :=
  Work.Asymptotics.E4Fun_bdd.add (Work.Asymptotics.IsBigOq.bounded
    (f := fun _ : ℍ => (1 : ℂ)) 1 (by norm_num) (fun _ _ => by simp))


/-- `E₄² - 1 - 480q = O(q²)`. -/
private lemma isBigOq_E4sq_sub_one_sub :
    Work.Asymptotics.IsBigOq (fun τ : ℍ => (Work.Kernels.E4Fun τ) ^ 2 - 1
      - 480 * Work.Kernels.qParamFun τ) 2 := by
  have hA : Work.Asymptotics.IsBigOq (fun τ : ℍ => (Work.Kernels.E4Fun τ - 1 - 240
      * Work.Kernels.qParamFun τ) * (Work.Kernels.E4Fun τ + 1)) 2 :=
    (Work.Asymptotics.E4Fun_isBigOq.mul isBigOq_E4_add_one).mono (by norm_num : 2 ≤ 2 + 0)
  have hB : Work.Asymptotics.IsBigOq (fun τ : ℍ => 240 * Work.Kernels.qParamFun τ
      * (Work.Kernels.E4Fun τ - 1)) 2 := by
    have h := ((Work.Asymptotics.qParamFun_isBigOq.mul Work.Asymptotics.E4_minus_one).const_mul
      (240 : ℂ)).mono (by norm_num : 2 ≤ 1 + 1)
    exact h.congr (fun τ => by ring)
  refine ((hA.add hB).mono (by norm_num : 2 ≤ min 2 2)).congr (fun τ => ?_)
  ring



/-- `E₄Δ - q = O(q²)`. -/
private lemma isBigOq_E4Delta_sub_q :
    Work.Asymptotics.IsBigOq (fun τ : ℍ => Work.Kernels.E4Fun τ * Work.Kernels.DeltaFun τ
      - Work.Kernels.qParamFun τ) 2 := by
  have hA : Work.Asymptotics.IsBigOq (fun τ : ℍ => (Work.Kernels.E4Fun τ - 1)
      * Work.Kernels.DeltaFun τ) 2 :=
    Work.Asymptotics.E4_minus_one.mul Work.Asymptotics.DeltaFun_isBigOq_one
  refine ((hA.add Work.Asymptotics.DeltaFun_isBigOq).mono
    (by norm_num : 2 ≤ min 2 2)).congr (fun τ => ?_)
  ring


/-!
## The cusp-`0` strip bound for the deviation, by `S`-transport from the funnel

The deviation on the cusp-`0` tile `E = KEpsilon = S(𝔽)` is the `S`-transport of the funnel
deviation: with `τ = S • w` one has

  `Kfun ℓ d w z - 𝒢(w,z) = -τ^{d/2} (K̂(τ,z) - 𝒢̂(τ,z)) = -τ^{d/2} Kdev ℓ d τ z`,

as follows from `Kfun_S_smul`, `Gfun_S_smul` and `gfun_eq`.  Since on `E` we have
`‖τ‖ ≤ scale w` (`E_norm_S_le_scale`) and `scale τ ≤ 3 scale w` (`E_scale_S_le`), the
polynomial prefactor `(scale w)^N` is preserved, so the funnel statement with the sharp
`‖q(τ)‖` factor transfers verbatim.  Combined with the forward transport
`strip_sharp_of_cusp0` this makes the two statements equivalent.
-/

/-- **Reverse transport: the sharp funnel strip bound implies the sharp cusp-`0` strip bound.** -/
theorem cusp0_strip_of_funnel (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (h : ∃ C N M : ℝ, 0 < C ∧ 0 ≤ N ∧ 0 ≤ M ∧
      ∀ (τ z : UpperHalfPlane) (t : ℝ), Work.Asymptotics.Funnel τ → τ.im + 1 ≤ t →
        0 ≤ z.re → z.re ≤ 1 → z.im = t →
        ‖Work.Asymptotics.Kdev ℓ d τ z‖
          ≤ C * ‖Work.Kernels.qParamFun τ‖ * (Work.Kernels.scale τ) ^ N * (1 + t) ^ M
              * Real.exp (-(Real.pi * t))) :
    ∃ C N M : ℝ, 0 < C ∧ 0 ≤ N ∧ 0 ≤ M ∧
      ∀ (w z : UpperHalfPlane) (t : ℝ), w ∈ Work.Asymptotics.KEpsilon →
        (ModularGroup.S • w).im + 1 ≤ t → 0 ≤ z.re → z.re ≤ 1 → z.im = t →
        ‖Work.Kernels.Kfun ℓ d w z
            - (Work.Asymptotics.Compact.Gplus d w z
                + Work.Asymptotics.Compact.Gminus d ℓ w z) / 2‖
          ≤ C * ‖Work.Kernels.qParamFun (ModularGroup.S • w)‖ * (Work.Kernels.scale w) ^ N
              * (1 + t) ^ M * Real.exp (-(Real.pi * t)) := by
  obtain ⟨C, N, M, hC, hN, hM, hb⟩ := h
  have hN4 : (0:ℝ) ≤ N + 4 := by linarith
  have hN12 : (0:ℝ) ≤ N + 12 := by linarith
  rcases hd with rfl | rfl
  · -- ## `d = 8`
    refine ⟨(3:ℝ) ^ N * C + 1, N + 4, M, by positivity, hN4, hM, ?_⟩
    intro w z t hw ht hz0 hz1 hzim
    set τ : ℍ := ModularGroup.S • w with hτ
    have hτF : Work.Asymptotics.Funnel τ := by
      rw [hτ]; exact Work.Asymptotics.S_smul_mem_funnel hw
    have hSτ : ModularGroup.S • τ = w := by rw [hτ]; exact Work.Asymptotics.S_smul_S_smul w
    have ht' : τ.im + 1 ≤ t := by rw [hτ]; exact ht
    have hb' := hb τ z t hτF ht' hz0 hz1 hzim
    have hK : Work.Kernels.Kfun ℓ 8 w z
        = - ((τ : ℂ)) ^ 4 * Work.Kernels.Khat ℓ 8 τ z := by
      have hh := Work.Asymptotics.KhatE1.STPure.Kfun_S_smul ℓ 8 (Or.inl rfl) τ z
      rw [hSτ, show (((8:ℕ):ℤ)/2) = ((4:ℕ):ℤ) by norm_num, zpow_natCast] at hh
      exact hh
    have hG : Work.Asymptotics.Compact.Gfun 8 ℓ w z
        = - ((τ : ℂ)) ^ 4 * (Work.Asymptotics.Compact.Gplus 8 τ z
            - Work.Asymptotics.Compact.Gminus 8 ℓ τ z) / 2 := by
      have hh := Work.Asymptotics.KhatE1.STPure.Gfun_S_smul ℓ 8 (Or.inl rfl) τ z
      rw [hSτ, show (((8:ℕ):ℤ)/2) = ((4:ℕ):ℤ) by norm_num, zpow_natCast] at hh
      exact hh
    have hsum : (Work.Asymptotics.Compact.Gplus 8 w z
          + Work.Asymptotics.Compact.Gminus 8 ℓ w z) / 2
        = Work.Asymptotics.Compact.Gfun 8 ℓ w z := by
      have h1 := Work.Asymptotics.Compact.gfun_eq ℓ 8 (Or.inl rfl) w z
      rw [h1]; ring
    have hdev : Work.Kernels.Kfun ℓ 8 w z
          - (Work.Asymptotics.Compact.Gplus 8 w z
              + Work.Asymptotics.Compact.Gminus 8 ℓ w z) / 2
        = - ((τ : ℂ)) ^ 4 * Work.Asymptotics.Kdev ℓ 8 τ z := by
      rw [hsum, hK, hG, Work.Asymptotics.Kdev]
      ring
    rw [hdev, norm_mul, norm_neg, norm_pow]
    have hnorm : ‖(τ : ℂ)‖ ≤ Work.Kernels.scale w := by
      rw [hτ]; exact Work.Asymptotics.EtailE.E_norm_S_le_scale w
    have hnorm4 : ‖(τ : ℂ)‖ ^ 4 ≤ (Work.Kernels.scale w) ^ 4 :=
      pow_le_pow_left₀ (norm_nonneg _) hnorm 4
    have hsc : Work.Kernels.scale τ ≤ 3 * Work.Kernels.scale w := by
      rw [hτ]; exact Work.Asymptotics.EtailE.E_scale_S_le hw
    have hspos : (0:ℝ) < Work.Kernels.scale w := Work.Kernels.scale_pos w
    have hscN : (Work.Kernels.scale τ) ^ N ≤ (3 * Work.Kernels.scale w) ^ N :=
      Real.rpow_le_rpow (le_of_lt (Work.Kernels.scale_pos τ)) hsc hN
    have h3N : (3 * Work.Kernels.scale w) ^ N = 3 ^ N * (Work.Kernels.scale w) ^ N :=
      Real.mul_rpow (by norm_num) (le_of_lt hspos)
    have hq : ‖Work.Kernels.qParamFun τ‖ = ‖Work.Kernels.qParamFun (ModularGroup.S • w)‖ := by
      rw [hτ]
    have hlt1 : (0:ℝ) ≤ (1 + t) ^ M := by
      apply Real.rpow_nonneg
      have : (0:ℝ) ≤ t := by
        have := hτF.2
        linarith [hτF.1, τ.im_pos]
      linarith
    have hexp : (0:ℝ) ≤ Real.exp (-(Real.pi * t)) := (Real.exp_pos _).le
    have hq0 : (0:ℝ) ≤ ‖Work.Kernels.qParamFun (ModularGroup.S • w)‖ := norm_nonneg _
    have hNnn : (0:ℝ) ≤ (Work.Kernels.scale w) ^ N := Real.rpow_nonneg (le_of_lt hspos) N
    have hstep : ‖(τ : ℂ)‖ ^ 4
          * (C * ‖Work.Kernels.qParamFun τ‖ * (Work.Kernels.scale τ) ^ N * (1 + t) ^ M
              * Real.exp (-(Real.pi * t)))
        ≤ 3 ^ N * C * ‖Work.Kernels.qParamFun (ModularGroup.S • w)‖
            * (Work.Kernels.scale w) ^ (N + 4) * (1 + t) ^ M * Real.exp (-(Real.pi * t)) := by
      rw [hq] at hb'
      have h1 : C * ‖Work.Kernels.qParamFun (ModularGroup.S • w)‖ * (Work.Kernels.scale τ) ^ N
            * (1 + t) ^ M * Real.exp (-(Real.pi * t))
          ≤ C * ‖Work.Kernels.qParamFun (ModularGroup.S • w)‖
            * (3 ^ N * (Work.Kernels.scale w) ^ N) * (1 + t) ^ M
            * Real.exp (-(Real.pi * t)) := by
        have hA : C * ‖Work.Kernels.qParamFun (ModularGroup.S • w)‖ * (Work.Kernels.scale τ) ^ N
            ≤ C * ‖Work.Kernels.qParamFun (ModularGroup.S • w)‖
              * (3 ^ N * (Work.Kernels.scale w) ^ N) := by
          refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg hC.le hq0)
          rw [← h3N]; exact hscN
        have hB : (0:ℝ) ≤ (1 + t) ^ M * Real.exp (-(Real.pi * t)) :=
          mul_nonneg hlt1 hexp
        calc C * ‖Work.Kernels.qParamFun (ModularGroup.S • w)‖ * (Work.Kernels.scale τ) ^ N
              * (1 + t) ^ M * Real.exp (-(Real.pi * t))
            = (C * ‖Work.Kernels.qParamFun (ModularGroup.S • w)‖ * (Work.Kernels.scale τ) ^ N)
                * ((1 + t) ^ M * Real.exp (-(Real.pi * t))) := by ring
          _ ≤ (C * ‖Work.Kernels.qParamFun (ModularGroup.S • w)‖
                * (3 ^ N * (Work.Kernels.scale w) ^ N))
                * ((1 + t) ^ M * Real.exp (-(Real.pi * t))) :=
              mul_le_mul_of_nonneg_right hA hB
          _ = C * ‖Work.Kernels.qParamFun (ModularGroup.S • w)‖
                * (3 ^ N * (Work.Kernels.scale w) ^ N) * (1 + t) ^ M
                * Real.exp (-(Real.pi * t)) := by ring
      have h2 : ‖(τ : ℂ)‖ ^ 4
            * (C * ‖Work.Kernels.qParamFun (ModularGroup.S • w)‖ * (Work.Kernels.scale τ) ^ N
                * (1 + t) ^ M * Real.exp (-(Real.pi * t)))
          ≤ ‖(τ : ℂ)‖ ^ 4
            * (C * ‖Work.Kernels.qParamFun (ModularGroup.S • w)‖
                * (3 ^ N * (Work.Kernels.scale w) ^ N) * (1 + t) ^ M
                * Real.exp (-(Real.pi * t))) :=
        mul_le_mul_of_nonneg_left h1 (pow_nonneg (norm_nonneg _) 4)
      refine le_trans h2 ?_
      have h3 : ‖(τ : ℂ)‖ ^ 4 * (3 ^ N * C * (Work.Kernels.scale w) ^ N) ≤
          3 ^ N * C * (Work.Kernels.scale w) ^ (N + 4) := by
        have hpow : (Work.Kernels.scale w) ^ N * (Work.Kernels.scale w) ^ 4
            = (Work.Kernels.scale w) ^ (N + 4) := by
          rw [show (Work.Kernels.scale w) ^ 4 = (Work.Kernels.scale w) ^ ((4:ℝ)) from
                (Real.rpow_natCast _ 4).symm, ← Real.rpow_add hspos]
        have h4 : ‖(τ : ℂ)‖ ^ 4 * (3 ^ N * C * (Work.Kernels.scale w) ^ N)
            ≤ (Work.Kernels.scale w) ^ 4 * (3 ^ N * C * (Work.Kernels.scale w) ^ N) := by
          refine mul_le_mul_of_nonneg_right hnorm4 ?_
          have h3N0 : (0:ℝ) ≤ 3 ^ N := Real.rpow_nonneg (by norm_num) N
          positivity
        calc ‖(τ : ℂ)‖ ^ 4 * (3 ^ N * C * (Work.Kernels.scale w) ^ N)
            ≤ (Work.Kernels.scale w) ^ 4 * (3 ^ N * C * (Work.Kernels.scale w) ^ N) := h4
          _ = 3 ^ N * C * ((Work.Kernels.scale w) ^ N * (Work.Kernels.scale w) ^ 4) := by ring
          _ = 3 ^ N * C * (Work.Kernels.scale w) ^ (N + 4) := by rw [hpow]
      have h4 : ‖(τ : ℂ)‖ ^ 4 * (3 ^ N * C * (Work.Kernels.scale w) ^ N)
            * (‖Work.Kernels.qParamFun (ModularGroup.S • w)‖ * (1 + t) ^ M
              * Real.exp (-(Real.pi * t)))
          ≤ 3 ^ N * C * (Work.Kernels.scale w) ^ (N + 4)
            * (‖Work.Kernels.qParamFun (ModularGroup.S • w)‖ * (1 + t) ^ M
              * Real.exp (-(Real.pi * t))) :=
          mul_le_mul_of_nonneg_right h3 (by positivity)
      calc ‖(τ : ℂ)‖ ^ 4
            * (C * ‖Work.Kernels.qParamFun (ModularGroup.S • w)‖
                * (3 ^ N * (Work.Kernels.scale w) ^ N) * (1 + t) ^ M
                * Real.exp (-(Real.pi * t)))
          = (‖(τ : ℂ)‖ ^ 4 * (3 ^ N * C * (Work.Kernels.scale w) ^ N))
              * (‖Work.Kernels.qParamFun (ModularGroup.S • w)‖ * (1 + t) ^ M
                * Real.exp (-(Real.pi * t))) := by ring
        _ ≤ (3 ^ N * C * (Work.Kernels.scale w) ^ (N + 4))
              * (‖Work.Kernels.qParamFun (ModularGroup.S • w)‖ * (1 + t) ^ M
                * Real.exp (-(Real.pi * t))) := h4
        _ = 3 ^ N * C * ‖Work.Kernels.qParamFun (ModularGroup.S • w)‖
              * (Work.Kernels.scale w) ^ (N + 4) * (1 + t) ^ M
              * Real.exp (-(Real.pi * t)) := by ring
    calc ‖(τ : ℂ)‖ ^ 4 * ‖Work.Asymptotics.Kdev ℓ 8 τ z‖
        ≤ ‖(τ : ℂ)‖ ^ 4
            * (C * ‖Work.Kernels.qParamFun τ‖ * (Work.Kernels.scale τ) ^ N * (1 + t) ^ M
                * Real.exp (-(Real.pi * t))) :=
          mul_le_mul_of_nonneg_left hb' (pow_nonneg (norm_nonneg _) 4)
      _ ≤ 3 ^ N * C * ‖Work.Kernels.qParamFun (ModularGroup.S • w)‖
            * (Work.Kernels.scale w) ^ (N + 4) * (1 + t) ^ M
            * Real.exp (-(Real.pi * t)) := hstep
      _ ≤ ((3:ℝ) ^ N * C + 1) * ‖Work.Kernels.qParamFun (ModularGroup.S • w)‖
            * (Work.Kernels.scale w) ^ (N + 4) * (1 + t) ^ M
            * Real.exp (-(Real.pi * t)) := by
          have hbase : (0:ℝ) ≤ ‖Work.Kernels.qParamFun (ModularGroup.S • w)‖
              * (Work.Kernels.scale w) ^ (N + 4) * (1 + t) ^ M
              * Real.exp (-(Real.pi * t)) := by positivity
          have hle : 3 ^ N * C ≤ 3 ^ N * C + 1 := by linarith
          calc 3 ^ N * C * ‖Work.Kernels.qParamFun (ModularGroup.S • w)‖
                * (Work.Kernels.scale w) ^ (N + 4) * (1 + t) ^ M
                * Real.exp (-(Real.pi * t))
              = (3 ^ N * C) * (‖Work.Kernels.qParamFun (ModularGroup.S • w)‖
                * (Work.Kernels.scale w) ^ (N + 4) * (1 + t) ^ M
                * Real.exp (-(Real.pi * t))) := by ring
            _ ≤ (3 ^ N * C + 1) * (‖Work.Kernels.qParamFun (ModularGroup.S • w)‖
                * (Work.Kernels.scale w) ^ (N + 4) * (1 + t) ^ M
                * Real.exp (-(Real.pi * t))) := mul_le_mul_of_nonneg_right hle hbase
            _ = ((3:ℝ) ^ N * C + 1) * ‖Work.Kernels.qParamFun (ModularGroup.S • w)‖
                * (Work.Kernels.scale w) ^ (N + 4) * (1 + t) ^ M
                * Real.exp (-(Real.pi * t)) := by ring
  · -- ## `d = 24`
    refine ⟨(3:ℝ) ^ N * C + 1, N + 12, M, by positivity, hN12, hM, ?_⟩
    intro w z t hw ht hz0 hz1 hzim
    set τ : ℍ := ModularGroup.S • w with hτ
    have hτF : Work.Asymptotics.Funnel τ := by
      rw [hτ]; exact Work.Asymptotics.S_smul_mem_funnel hw
    have hSτ : ModularGroup.S • τ = w := by rw [hτ]; exact Work.Asymptotics.S_smul_S_smul w
    have ht' : τ.im + 1 ≤ t := by rw [hτ]; exact ht
    have hb' := hb τ z t hτF ht' hz0 hz1 hzim
    have hK : Work.Kernels.Kfun ℓ 24 w z
        = - ((τ : ℂ)) ^ 12 * Work.Kernels.Khat ℓ 24 τ z := by
      have hh := Work.Asymptotics.KhatE1.STPure.Kfun_S_smul ℓ 24 (Or.inr rfl) τ z
      rw [hSτ, show (((24:ℕ):ℤ)/2) = ((12:ℕ):ℤ) by norm_num, zpow_natCast] at hh
      exact hh
    have hG : Work.Asymptotics.Compact.Gfun 24 ℓ w z
        = - ((τ : ℂ)) ^ 12 * (Work.Asymptotics.Compact.Gplus 24 τ z
            - Work.Asymptotics.Compact.Gminus 24 ℓ τ z) / 2 := by
      have hh := Work.Asymptotics.KhatE1.STPure.Gfun_S_smul ℓ 24 (Or.inr rfl) τ z
      rw [hSτ, show (((24:ℕ):ℤ)/2) = ((12:ℕ):ℤ) by norm_num, zpow_natCast] at hh
      exact hh
    have hsum : (Work.Asymptotics.Compact.Gplus 24 w z
          + Work.Asymptotics.Compact.Gminus 24 ℓ w z) / 2
        = Work.Asymptotics.Compact.Gfun 24 ℓ w z := by
      have h1 := Work.Asymptotics.Compact.gfun_eq ℓ 24 (Or.inr rfl) w z
      rw [h1]; ring
    have hdev : Work.Kernels.Kfun ℓ 24 w z
          - (Work.Asymptotics.Compact.Gplus 24 w z
              + Work.Asymptotics.Compact.Gminus 24 ℓ w z) / 2
        = - ((τ : ℂ)) ^ 12 * Work.Asymptotics.Kdev ℓ 24 τ z := by
      rw [hsum, hK, hG, Work.Asymptotics.Kdev]
      ring
    rw [hdev, norm_mul, norm_neg, norm_pow]
    have hnorm : ‖(τ : ℂ)‖ ≤ Work.Kernels.scale w := by
      rw [hτ]; exact Work.Asymptotics.EtailE.E_norm_S_le_scale w
    have hnorm12 : ‖(τ : ℂ)‖ ^ 12 ≤ (Work.Kernels.scale w) ^ 12 :=
      pow_le_pow_left₀ (norm_nonneg _) hnorm 12
    have hsc : Work.Kernels.scale τ ≤ 3 * Work.Kernels.scale w := by
      rw [hτ]; exact Work.Asymptotics.EtailE.E_scale_S_le hw
    have hspos : (0:ℝ) < Work.Kernels.scale w := Work.Kernels.scale_pos w
    have hscN : (Work.Kernels.scale τ) ^ N ≤ (3 * Work.Kernels.scale w) ^ N :=
      Real.rpow_le_rpow (le_of_lt (Work.Kernels.scale_pos τ)) hsc hN
    have h3N : (3 * Work.Kernels.scale w) ^ N = 3 ^ N * (Work.Kernels.scale w) ^ N :=
      Real.mul_rpow (by norm_num) (le_of_lt hspos)
    have hq : ‖Work.Kernels.qParamFun τ‖ = ‖Work.Kernels.qParamFun (ModularGroup.S • w)‖ := by
      rw [hτ]
    have ht0 : (0:ℝ) ≤ t := by
      have := hτF.2
      linarith [hτF.1, τ.im_pos]
    have hlt1 : (0:ℝ) ≤ (1 + t) ^ M := Real.rpow_nonneg (by linarith) M
    have hexp : (0:ℝ) ≤ Real.exp (-(Real.pi * t)) := (Real.exp_pos _).le
    have hq0 : (0:ℝ) ≤ ‖Work.Kernels.qParamFun (ModularGroup.S • w)‖ := norm_nonneg _
    have hstep : ‖(τ : ℂ)‖ ^ 12
          * (C * ‖Work.Kernels.qParamFun τ‖ * (Work.Kernels.scale τ) ^ N * (1 + t) ^ M
              * Real.exp (-(Real.pi * t)))
        ≤ 3 ^ N * C * ‖Work.Kernels.qParamFun (ModularGroup.S • w)‖
            * (Work.Kernels.scale w) ^ (N + 12) * (1 + t) ^ M * Real.exp (-(Real.pi * t)) := by
      rw [hq] at hb'
      have h1 : C * ‖Work.Kernels.qParamFun (ModularGroup.S • w)‖ * (Work.Kernels.scale τ) ^ N
            * (1 + t) ^ M * Real.exp (-(Real.pi * t))
          ≤ C * ‖Work.Kernels.qParamFun (ModularGroup.S • w)‖
            * (3 ^ N * (Work.Kernels.scale w) ^ N) * (1 + t) ^ M
            * Real.exp (-(Real.pi * t)) := by
        have hA : C * ‖Work.Kernels.qParamFun (ModularGroup.S • w)‖ * (Work.Kernels.scale τ) ^ N
            ≤ C * ‖Work.Kernels.qParamFun (ModularGroup.S • w)‖
              * (3 ^ N * (Work.Kernels.scale w) ^ N) := by
          refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg hC.le hq0)
          rw [← h3N]; exact hscN
        have hB : (0:ℝ) ≤ (1 + t) ^ M * Real.exp (-(Real.pi * t)) :=
          mul_nonneg hlt1 hexp
        calc C * ‖Work.Kernels.qParamFun (ModularGroup.S • w)‖ * (Work.Kernels.scale τ) ^ N
              * (1 + t) ^ M * Real.exp (-(Real.pi * t))
            = (C * ‖Work.Kernels.qParamFun (ModularGroup.S • w)‖ * (Work.Kernels.scale τ) ^ N)
                * ((1 + t) ^ M * Real.exp (-(Real.pi * t))) := by ring
          _ ≤ (C * ‖Work.Kernels.qParamFun (ModularGroup.S • w)‖
                * (3 ^ N * (Work.Kernels.scale w) ^ N))
                * ((1 + t) ^ M * Real.exp (-(Real.pi * t))) :=
              mul_le_mul_of_nonneg_right hA hB
          _ = C * ‖Work.Kernels.qParamFun (ModularGroup.S • w)‖
                * (3 ^ N * (Work.Kernels.scale w) ^ N) * (1 + t) ^ M
                * Real.exp (-(Real.pi * t)) := by ring
      have h2 : ‖(τ : ℂ)‖ ^ 12
            * (C * ‖Work.Kernels.qParamFun (ModularGroup.S • w)‖ * (Work.Kernels.scale τ) ^ N
                * (1 + t) ^ M * Real.exp (-(Real.pi * t)))
          ≤ ‖(τ : ℂ)‖ ^ 12
            * (C * ‖Work.Kernels.qParamFun (ModularGroup.S • w)‖
                * (3 ^ N * (Work.Kernels.scale w) ^ N) * (1 + t) ^ M
                * Real.exp (-(Real.pi * t))) :=
        mul_le_mul_of_nonneg_left h1 (pow_nonneg (norm_nonneg _) 12)
      refine le_trans h2 ?_
      have h3 : ‖(τ : ℂ)‖ ^ 12 * (3 ^ N * C * (Work.Kernels.scale w) ^ N) ≤
          3 ^ N * C * (Work.Kernels.scale w) ^ (N + 12) := by
        have hpow : (Work.Kernels.scale w) ^ N * (Work.Kernels.scale w) ^ 12
            = (Work.Kernels.scale w) ^ (N + 12) := by
          rw [show (Work.Kernels.scale w) ^ 12 = (Work.Kernels.scale w) ^ ((12:ℝ)) from
                (Real.rpow_natCast _ 12).symm, ← Real.rpow_add hspos]
        have h3N0 : (0:ℝ) ≤ 3 ^ N := Real.rpow_nonneg (by norm_num) N
        have hstr : (0:ℝ) ≤ 3 ^ N * C * (Work.Kernels.scale w) ^ N := by positivity
        have h4 : ‖(τ : ℂ)‖ ^ 12 * (3 ^ N * C * (Work.Kernels.scale w) ^ N)
            ≤ (Work.Kernels.scale w) ^ 12 * (3 ^ N * C * (Work.Kernels.scale w) ^ N) :=
          mul_le_mul_of_nonneg_right hnorm12 hstr
        calc ‖(τ : ℂ)‖ ^ 12 * (3 ^ N * C * (Work.Kernels.scale w) ^ N)
            ≤ (Work.Kernels.scale w) ^ 12 * (3 ^ N * C * (Work.Kernels.scale w) ^ N) := h4
          _ = 3 ^ N * C * ((Work.Kernels.scale w) ^ N * (Work.Kernels.scale w) ^ 12) := by ring
          _ = 3 ^ N * C * (Work.Kernels.scale w) ^ (N + 12) := by rw [hpow]
      have h4 : ‖(τ : ℂ)‖ ^ 12 * (3 ^ N * C * (Work.Kernels.scale w) ^ N)
            * (‖Work.Kernels.qParamFun (ModularGroup.S • w)‖ * (1 + t) ^ M
              * Real.exp (-(Real.pi * t)))
          ≤ 3 ^ N * C * (Work.Kernels.scale w) ^ (N + 12)
            * (‖Work.Kernels.qParamFun (ModularGroup.S • w)‖ * (1 + t) ^ M
              * Real.exp (-(Real.pi * t))) :=
          mul_le_mul_of_nonneg_right h3 (by positivity)
      calc ‖(τ : ℂ)‖ ^ 12
            * (C * ‖Work.Kernels.qParamFun (ModularGroup.S • w)‖
                * (3 ^ N * (Work.Kernels.scale w) ^ N) * (1 + t) ^ M
                * Real.exp (-(Real.pi * t)))
          = (‖(τ : ℂ)‖ ^ 12 * (3 ^ N * C * (Work.Kernels.scale w) ^ N))
              * (‖Work.Kernels.qParamFun (ModularGroup.S • w)‖ * (1 + t) ^ M
                * Real.exp (-(Real.pi * t))) := by ring
        _ ≤ (3 ^ N * C * (Work.Kernels.scale w) ^ (N + 12))
              * (‖Work.Kernels.qParamFun (ModularGroup.S • w)‖ * (1 + t) ^ M
                * Real.exp (-(Real.pi * t))) := h4
        _ = 3 ^ N * C * ‖Work.Kernels.qParamFun (ModularGroup.S • w)‖
              * (Work.Kernels.scale w) ^ (N + 12) * (1 + t) ^ M
              * Real.exp (-(Real.pi * t)) := by ring
    calc ‖(τ : ℂ)‖ ^ 12 * ‖Work.Asymptotics.Kdev ℓ 24 τ z‖
        ≤ ‖(τ : ℂ)‖ ^ 12
            * (C * ‖Work.Kernels.qParamFun τ‖ * (Work.Kernels.scale τ) ^ N * (1 + t) ^ M
                * Real.exp (-(Real.pi * t))) :=
          mul_le_mul_of_nonneg_left hb' (pow_nonneg (norm_nonneg _) 12)
      _ ≤ 3 ^ N * C * ‖Work.Kernels.qParamFun (ModularGroup.S • w)‖
            * (Work.Kernels.scale w) ^ (N + 12) * (1 + t) ^ M
            * Real.exp (-(Real.pi * t)) := hstep
      _ ≤ ((3:ℝ) ^ N * C + 1) * ‖Work.Kernels.qParamFun (ModularGroup.S • w)‖
            * (Work.Kernels.scale w) ^ (N + 12) * (1 + t) ^ M
            * Real.exp (-(Real.pi * t)) := by
          have hbase : (0:ℝ) ≤ ‖Work.Kernels.qParamFun (ModularGroup.S • w)‖
              * (Work.Kernels.scale w) ^ (N + 12) * (1 + t) ^ M
              * Real.exp (-(Real.pi * t)) := by positivity
          have hle : 3 ^ N * C ≤ 3 ^ N * C + 1 := by linarith
          calc 3 ^ N * C * ‖Work.Kernels.qParamFun (ModularGroup.S • w)‖
                * (Work.Kernels.scale w) ^ (N + 12) * (1 + t) ^ M
                * Real.exp (-(Real.pi * t))
              = (3 ^ N * C) * (‖Work.Kernels.qParamFun (ModularGroup.S • w)‖
                * (Work.Kernels.scale w) ^ (N + 12) * (1 + t) ^ M
                * Real.exp (-(Real.pi * t))) := by ring
            _ ≤ (3 ^ N * C + 1) * (‖Work.Kernels.qParamFun (ModularGroup.S • w)‖
                * (Work.Kernels.scale w) ^ (N + 12) * (1 + t) ^ M
                * Real.exp (-(Real.pi * t))) := mul_le_mul_of_nonneg_right hle hbase
            _ = ((3:ℝ) ^ N * C + 1) * ‖Work.Kernels.qParamFun (ModularGroup.S • w)‖
                * (Work.Kernels.scale w) ^ (N + 12) * (1 + t) ^ M
                * Real.exp (-(Real.pi * t)) := by ring

/-! ## The exact decompositions at a point of the strip

The decompositions `Compact.Khat8_sub_Ghat8_eq`, `Compact.decomp8` /
`Compact.decomp24_sum` are stated with the hypothesis `Sh τ z ≠ 0`.  At every contour point of
the strip (`Im z ≥ Im τ + 1`, `τ` in the funnel) this holds: a point `z` with
`j(z) = j(τ)` is an `SL(2,ℤ)`-translate of `τ`, and every translate `γ • z` has
`Im (γ • z) ≤ max (Im z) (Im z)⁻¹ = Im z`, so `Im τ ≤ Im z`, contradicting `Im τ + 1 ≤ Im z`. -/

/-- The `E(z)¹`-coefficient of the reference bracket of `K₋^{(24)}` is `E1combo24`. -/
theorem R24_p0_eq_e1combo24 (ℓ : Work.Kernels.LogLambdaData) (τ : ℍ) :
    Work.Asymptotics.Compact.R24_p0 ℓ τ = E1combo24 ℓ τ := by
  have hΔ : Work.Kernels.DeltaFun τ ≠ 0 := Work.Kernels.ClassicalFacts.DeltaFun_ne_zero τ
  simp only [Work.Asymptotics.Compact.R24_p0, E1combo24]
  field_simp
  ring

/-- The leading coefficient `E1combo8/(288π)` of the funnel deviation satisfies the
coefficient bound required by the core, by `E1combo8_bound`. -/
theorem E1combo8_over_const_bound (ℓ : Work.Kernels.LogLambdaData) :
    ∃ C N : ℝ, 0 < C ∧ 0 ≤ N ∧ ∀ τ : ℍ, Work.Asymptotics.Funnel τ →
      ‖E1combo8 ℓ τ / (288 * (Real.pi : ℂ))‖
        ≤ C * (Work.Kernels.scale τ) ^ N * ‖Work.Kernels.qParamFun τ‖ := by
  obtain ⟨C, N, hC, hN, h⟩ := E1combo8_bound ℓ
  refine ⟨max C 1, N, by positivity, hN, fun τ hτ => ?_⟩
  have hπ : (1 : ℝ) ≤ 288 * Real.pi := by nlinarith [Real.pi_gt_three]
  have h1 : ‖E1combo8 ℓ τ / (288 * (Real.pi : ℂ))‖
      = ‖E1combo8 ℓ τ‖ / (288 * Real.pi) := by
    rw [norm_div, norm_mul, Complex.norm_ofNat, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos Real.pi_pos]
  rw [h1]
  have h2 : ‖E1combo8 ℓ τ‖ / (288 * Real.pi) ≤ ‖E1combo8 ℓ τ‖ := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith [norm_nonneg (E1combo8 ℓ τ), hπ]
  refine le_trans h2 (le_trans (h τ hτ) ?_)
  have h3 : C ≤ max C 1 := le_max_left C 1
  have h4 : (0 : ℝ) ≤ (Work.Kernels.scale τ) ^ N :=
    Real.rpow_nonneg (le_of_lt (Work.Kernels.scale_pos τ)) N
  calc C * (Work.Kernels.scale τ) ^ N * ‖Work.Kernels.qParamFun τ‖
      ≤ max C 1 * (Work.Kernels.scale τ) ^ N * ‖Work.Kernels.qParamFun τ‖ := by
        refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h3 h4) (norm_nonneg _)

/-!
## The remaining core: the sharp leading coefficient of the funnel deviation

Everything above is proved.  What remains is a statement about the *single* explicit expression
`Kdev ℓ d τ z = K̂(τ,z) - Ĝ(τ,z) = (K₊-𝒢₊)/2 - (K₋-𝒢₋)/2` (`KhatE1Defs.Kdev`), namely the
**sharp leading coefficient** form of the funnel deviation.

The two exact decompositions

* `Compact.KPlus8_sub_Gplus8_decomp` : `K₊^{(8)} - 𝒢₊^{(8)} = tailC⁻¹(Φ₁+Φ₂+Φ₃)`,
* `Compact.tail_identity`           : `3456π (K₋^{(d)} - 𝒢₋^{(d)}) = -(Sh)⁻¹ (br + Sh·br0)`,

together with the reference expansion `Compact.Tref8_eq` / `Compact.Tref24_eq` (the reference part
of the `K₋`-bracket, whose `E(z)^0` coefficient is `24·E1combo8`, resp. `E1combo24`, where
`E(z) = Ept z`), show that the deviation is, as a function of `z`,

`K̂(τ,z) - Ĝ(τ,z) = f(τ)·E(z) + O(‖q(τ)‖ (scale τ)^N (1+t)^M E(z)²)`

on the funnel, with `f(τ) = E1combo8(τ)/(288π)` (`E1combo8_bound`: `‖f τ‖ ≤ C (scale τ)^N ‖q τ‖`).
The `E(z)^0` coefficient of the deviation vanishes identically (`𝒢±` is the sum of the
`e^{nπiz}`, `n ≤ 0`, terms of `K±`), so no constant term survives; the content of the core is the
control of the *remaining* coefficients, whose natural size is `‖q(τ)‖^{-1}` (they are built from
the `τ`-atoms `Δ(τ)`, `j(τ)²Δ(τ)`, `j(τ)ψ₂(τ)E₁₀(τ)`, …) and which must cancel between the
`K₊`- and the `K₋`-piece down to the asserted order.
-/

/-- The `e²`-coefficient of the `K₊`-side of the matching identity, i.e. of
`tailC⁻¹(ΦMain + ΦDiv + ΦCorr)`. -/
noncomputable def M2plus (τ z : ℍ) : ℂ :=
  Work.Asymptotics.Compact.tailC⁻¹ *
    (-24 * ((τ : ℂ) * Work.Kernels.E6Fun τ
          * (-2 * (z : ℂ) ^ 2 + 12 * Complex.I * (z : ℂ) / (Real.pi : ℂ))
        + 2 * Work.Kernels.phi0 τ * Work.Kernels.E4Fun τ * (z : ℂ) ^ 2)
      - Work.Asymptotics.Compact.phi2t τ
          * ((Work.Kernels.E4Fun τ) ^ 2 * Work.Kernels.E6Fun τ / Work.Kernels.DeltaFun τ)
          * (z : ℂ) ^ 2
      - ((τ : ℂ) * Work.Kernels.E6Fun τ
            * ((z : ℂ) ^ 2 - 12 * Complex.I * (z : ℂ) / (Real.pi : ℂ)
              - 36 / (Real.pi : ℂ) ^ 2)
            * (Work.Kernels.jInvariantFun τ - 240)
          - 2 * Work.Kernels.phi0 τ * Work.Kernels.E4Fun τ
              * ((z : ℂ) ^ 2 - 6 * Complex.I * (z : ℂ) / (Real.pi : ℂ))
              * (Work.Kernels.jInvariantFun τ - 984)))

/-- The `e²`-coefficient of the `K₋`-side of the matching identity, i.e. of
`(3456π)⁻¹(e(R8-R8_p0) + Dev8Sum)`. -/
noncomputable def M2minus (ℓ : Work.Kernels.LogLambdaData) (τ z : ℍ) : ℂ :=
  ((3456 : ℂ) * (Real.pi : ℂ))⁻¹ *
    (Work.Asymptotics.Compact.Xc ℓ z * Work.Asymptotics.Compact.R8_q1 ℓ τ
      + Work.Asymptotics.Compact.R8_p1 ℓ τ)

/-!
-/

/-!
## Roadmap of what remains (state as of the last working session)

Everything below is proved and axiom-clean except the single remaining hole of
`Kdev_leading_core`:
`cusp0_strip_of_funnel`, `z2A_expand`, `z2_cleared`, `z2AB_bound` (the two `z²`-combinations
are `O(q²)`), `z2coef_bound` (`z²`-coefficient of the bracket is `O(q‖scale‖)`),
`Kdev8Z1_eq`, `Kdev8Z1_bound` (`z¹`-coefficient is `O(q‖scale‖)`), plus `ratio_third_order`
in `KhatE1/ratio_third_order.lean`.

Reduction of `Kdev_leading_core` (d = 8, `f := E1combo8/(288π)`): the funnel bracket
`Kdev8Bracket = 2·KdevRem` (`KhatE1Core/Kdev8_matching_bridge`) has E(z)²-coefficient
`c₂z²+c₁z+c₀` with `c₂ = z2coef` (bounded), `c₁ = Kdev8Z1` (bounded) and
`c₀ = B0 = -iτE₆(j-240) + (3456π)⁻¹(cuspC·R8_q1 + R8_p1)`; what is still missing is
1. `‖B0‖ ≤ C q_τ (scale τ)^N` on the funnel — this is *equivalent* to the reviewed statement
   `Asymptotics/KhatE1Core/psi_combo_first_order`
   (`‖2ψ₂+ψ₄-6Λ₀+(192Λ₀-72)q_τ‖ ≤ C scale^N‖q_τ‖²`, `Λ₀ = πiτ + cuspC`), whose proof needs
   the up-to-`E³` expansions of `𝓛`, of `𝓛_S = log(W/U)`, and of `U,V,W` (available in
   `Asymptotics/ThetaQExp`), together with the third-order cusp expansion of `𝓛 - Λ₀`
   (the `E³`-coefficient `-32/3` is essential);
2. the *tail* bound `‖Kdev8Bracket - E(z)²·(c₂z²+c₁z+c₀)‖ ≤ C q_τ scale^N (1+t)^M e^{-2πt}`
   (numerically the quotient by `‖E‖²` is `≈ 1.16 q_τ`), which requires the cancellation
   between `Dev8Sum` and `(Xc·R8_q1+R8_p1)`;
3. the d = 24 analogues of 1. and 2.
-/



/-! ## The `q`-expansions of the atoms occurring in `B0`

All are instances of `IsBigOq`, obtained from the two-term expansions of `E₄`, `E₆`, `Δ`
(`E4Fun_isBigOq`, `E6Fun_isBigOq`, `DeltaFun_isBigOq`) by multiplicativity. -/

/-- `E₄²E₆ = 1 - 24q + O(q²)`. -/
private lemma isBigOq_E14_sub_one_add :
    Work.Asymptotics.IsBigOq (fun τ : ℍ => (Work.Kernels.E4Fun τ) ^ 2 * Work.Kernels.E6Fun τ
      - 1 + 24 * Work.Kernels.qParamFun τ) 2 := by
  have hkey : (fun τ : ℍ => (Work.Kernels.E4Fun τ) ^ 2 * Work.Kernels.E6Fun τ
      - 1 + 24 * Work.Kernels.qParamFun τ)
      = fun τ : ℍ => ((Work.Kernels.E4Fun τ) ^ 2 - 1 - 480 * Work.Kernels.qParamFun τ)
          * Work.Kernels.E6Fun τ
        + (1 + 480 * Work.Kernels.qParamFun τ)
          * (Work.Kernels.E6Fun τ - 1 + 504 * Work.Kernels.qParamFun τ)
        + (-241920) * Work.Kernels.qParamFun τ ^ 2 := by
    funext τ; ring
  rw [hkey]
  have h1 : Work.Asymptotics.IsBigOq (fun τ : ℍ =>
      ((Work.Kernels.E4Fun τ) ^ 2 - 1 - 480 * Work.Kernels.qParamFun τ)
        * Work.Kernels.E6Fun τ) 2 :=
    (isBigOq_E4sq_sub_one_sub.mul Work.Asymptotics.E6Fun_bdd).mono (by norm_num)
  have h2 : Work.Asymptotics.IsBigOq (fun τ : ℍ =>
      (1 + 480 * Work.Kernels.qParamFun τ)
        * (Work.Kernels.E6Fun τ - 1 + 504 * Work.Kernels.qParamFun τ)) 2 :=
    ((Work.Asymptotics.isBigOq_one_add_const_mul_q (480 : ℂ)).mul
      Work.Asymptotics.E6Fun_isBigOq).mono (by norm_num)
  have h3 : Work.Asymptotics.IsBigOq (fun τ : ℍ =>
      (-241920 : ℂ) * Work.Kernels.qParamFun τ ^ 2) 2 :=
    Work.Asymptotics.qParamFun_sq_isBigOq.const_mul ((-241920 : ℂ))
  exact ((h1.add h2).add h3).mono (by norm_num)

/-- `E₄³ = 1 + 720q + O(q²)`. -/
private lemma isBigOq_E4cube_sub_one_sub :
    Work.Asymptotics.IsBigOq (fun τ : ℍ => (Work.Kernels.E4Fun τ) ^ 3 - 1
      - 720 * Work.Kernels.qParamFun τ) 2 := by
  have hkey : (fun τ : ℍ => (Work.Kernels.E4Fun τ) ^ 3 - 1
      - 720 * Work.Kernels.qParamFun τ)
      = fun τ : ℍ => Work.Kernels.E4Fun τ
          * ((Work.Kernels.E4Fun τ) ^ 2 - 1 - 480 * Work.Kernels.qParamFun τ)
        + (Work.Kernels.E4Fun τ - 1 - 240 * Work.Kernels.qParamFun τ)
          * (1 + 480 * Work.Kernels.qParamFun τ)
        + 115200 * Work.Kernels.qParamFun τ ^ 2 := by
    funext τ; ring
  rw [hkey]
  have h1 : Work.Asymptotics.IsBigOq (fun τ : ℍ => Work.Kernels.E4Fun τ
      * ((Work.Kernels.E4Fun τ) ^ 2 - 1 - 480 * Work.Kernels.qParamFun τ)) 2 :=
    (Work.Asymptotics.E4Fun_bdd.mul isBigOq_E4sq_sub_one_sub).mono (by norm_num)
  have h2 : Work.Asymptotics.IsBigOq (fun τ : ℍ =>
      (Work.Kernels.E4Fun τ - 1 - 240 * Work.Kernels.qParamFun τ)
        * (1 + 480 * Work.Kernels.qParamFun τ)) 2 :=
    (Work.Asymptotics.E4Fun_isBigOq.mul
      (Work.Asymptotics.isBigOq_one_add_const_mul_q (480 : ℂ))).mono (by norm_num)
  have h3 : Work.Asymptotics.IsBigOq (fun τ : ℍ =>
      (115200 : ℂ) * Work.Kernels.qParamFun τ ^ 2) 2 :=
    Work.Asymptotics.qParamFun_sq_isBigOq.const_mul ((115200 : ℂ))
  exact ((h1.add h2).add h3).mono (by norm_num)

/-- `E₆E₄³ = 1 + 216q + O(q²)`. -/
private lemma isBigOq_E6E4cube_sub_one_sub :
    Work.Asymptotics.IsBigOq (fun τ : ℍ => Work.Kernels.E6Fun τ * (Work.Kernels.E4Fun τ) ^ 3
      - 1 - 216 * Work.Kernels.qParamFun τ) 2 := by
  have hkey : (fun τ : ℍ => Work.Kernels.E6Fun τ * (Work.Kernels.E4Fun τ) ^ 3
      - 1 - 216 * Work.Kernels.qParamFun τ)
      = fun τ : ℍ => Work.Kernels.E6Fun τ
          * ((Work.Kernels.E4Fun τ) ^ 3 - 1 - 720 * Work.Kernels.qParamFun τ)
        + (Work.Kernels.E6Fun τ - 1 + 504 * Work.Kernels.qParamFun τ)
          * (1 + 720 * Work.Kernels.qParamFun τ)
        + (-362880) * Work.Kernels.qParamFun τ ^ 2 := by
    funext τ; ring
  rw [hkey]
  have h1 : Work.Asymptotics.IsBigOq (fun τ : ℍ => Work.Kernels.E6Fun τ
      * ((Work.Kernels.E4Fun τ) ^ 3 - 1 - 720 * Work.Kernels.qParamFun τ)) 2 :=
    (Work.Asymptotics.E6Fun_bdd.mul isBigOq_E4cube_sub_one_sub).mono (by norm_num)
  have h2 : Work.Asymptotics.IsBigOq (fun τ : ℍ =>
      (Work.Kernels.E6Fun τ - 1 + 504 * Work.Kernels.qParamFun τ)
        * (1 + 720 * Work.Kernels.qParamFun τ)) 2 :=
    (Work.Asymptotics.E6Fun_isBigOq.mul
      (Work.Asymptotics.isBigOq_one_add_const_mul_q (720 : ℂ))).mono (by norm_num)
  have h3 : Work.Asymptotics.IsBigOq (fun τ : ℍ =>
      (-362880 : ℂ) * Work.Kernels.qParamFun τ ^ 2) 2 :=
    Work.Asymptotics.qParamFun_sq_isBigOq.const_mul ((-362880 : ℂ))
  exact ((h1.add h2).add h3).mono (by norm_num)

/-- `ΔE₆ = q + O(q²)`. -/
private lemma isBigOq_DeltaE6_sub :
    Work.Asymptotics.IsBigOq (fun τ : ℍ => Work.Kernels.DeltaFun τ * Work.Kernels.E6Fun τ
      - Work.Kernels.qParamFun τ) 2 := by
  have hkey : (fun τ : ℍ => Work.Kernels.DeltaFun τ * Work.Kernels.E6Fun τ
      - Work.Kernels.qParamFun τ)
      = fun τ : ℍ => (Work.Kernels.DeltaFun τ - Work.Kernels.qParamFun τ)
          * Work.Kernels.E6Fun τ
        + Work.Kernels.qParamFun τ * (Work.Kernels.E6Fun τ - 1) := by
    funext τ; ring
  rw [hkey]
  have h1 : Work.Asymptotics.IsBigOq (fun τ : ℍ =>
      (Work.Kernels.DeltaFun τ - Work.Kernels.qParamFun τ) * Work.Kernels.E6Fun τ) 2 :=
    (Work.Asymptotics.DeltaFun_isBigOq.mul Work.Asymptotics.E6Fun_bdd).mono (by norm_num)
  have h2 : Work.Asymptotics.IsBigOq (fun τ : ℍ => Work.Kernels.qParamFun τ
      * (Work.Kernels.E6Fun τ - 1)) 2 :=
    (Work.Asymptotics.qParamFun_isBigOq.mul Work.Asymptotics.E6_minus_one).mono (by norm_num)
  exact (h1.add h2).mono (by norm_num)

/-- `E₄⁴ = 1 + 960q + O(q²)`. -/
private lemma isBigOq_E4four_sub_one_sub :
    Work.Asymptotics.IsBigOq (fun τ : ℍ => (Work.Kernels.E4Fun τ) ^ 4 - 1
      - 960 * Work.Kernels.qParamFun τ) 2 := by
  have hkey : (fun τ : ℍ => (Work.Kernels.E4Fun τ) ^ 4 - 1
      - 960 * Work.Kernels.qParamFun τ)
      = fun τ : ℍ => ((Work.Kernels.E4Fun τ) ^ 2 - 1 - 480 * Work.Kernels.qParamFun τ) ^ 2
        + 2 * ((Work.Kernels.E4Fun τ) ^ 2 - 1 - 480 * Work.Kernels.qParamFun τ)
          * (1 + 480 * Work.Kernels.qParamFun τ)
        + 230400 * Work.Kernels.qParamFun τ ^ 2 := by
    funext τ; ring
  rw [hkey]
  have h1 : Work.Asymptotics.IsBigOq (fun τ : ℍ =>
      ((Work.Kernels.E4Fun τ) ^ 2 - 1 - 480 * Work.Kernels.qParamFun τ) ^ 2) 4 := by
    have h := isBigOq_E4sq_sub_one_sub.mul isBigOq_E4sq_sub_one_sub
    exact h.congr (fun τ => by ring)
  have h2 : Work.Asymptotics.IsBigOq (fun τ : ℍ =>
      2 * ((Work.Kernels.E4Fun τ) ^ 2 - 1 - 480 * Work.Kernels.qParamFun τ)
        * (1 + 480 * Work.Kernels.qParamFun τ)) 2 := by
    have h := (isBigOq_E4sq_sub_one_sub.mul
      (Work.Asymptotics.isBigOq_one_add_const_mul_q (480 : ℂ))).const_mul (2 : ℂ)
    exact h.congr (fun τ => by ring)
  have h3 : Work.Asymptotics.IsBigOq (fun τ : ℍ =>
      (230400 : ℂ) * Work.Kernels.qParamFun τ ^ 2) 2 :=
    Work.Asymptotics.qParamFun_sq_isBigOq.const_mul ((230400 : ℂ))
  exact ((h1.mono (by norm_num : 2 ≤ 4)).add h2).add h3



/-! ## The explicit cancellation in `B0`

With `Λ₀ = πiτ + cuspC`, the `O(1)`- and `O(q)`-parts of `Δ·B0` cancel between the
`τ`-atoms and the `ψ`-atoms; after subtracting those explicit terms what remains is a sum of
`O(q²)` remainders.  This block isolates the *purely atomic* part of that cancellation. -/

/-- The atomic part of `Δ·B0` after adding the explicit `Λ₀`-terms. -/
private noncomputable def Term (ℓ : Work.Kernels.LogLambdaData) (τ : ℍ) : ℂ :=
  - Complex.I * (τ : ℂ) * Work.Kernels.E6Fun τ * (Work.Kernels.E4Fun τ) ^ 3
    + 240 * Complex.I * (τ : ℂ) * Work.Kernels.DeltaFun τ * Work.Kernels.E6Fun τ
    + ((3456 : ℂ) * (Real.pi : ℂ))⁻¹ * Work.Asymptotics.Compact.cuspC ℓ
        * (3400704 * Work.Kernels.E4Fun τ * Work.Kernels.DeltaFun τ
            - 3456 * (Work.Kernels.E4Fun τ) ^ 4)
    - ((3456 : ℂ) * (Real.pi : ℂ))⁻¹ * 41472 * Work.Kernels.E4Fun τ
        * Work.Kernels.DeltaFun τ
    + ((3456 : ℂ) * (Real.pi : ℂ))⁻¹ *
        (3456 * ((Real.pi : ℂ) * Complex.I * (τ : ℂ) + Work.Asymptotics.Compact.cuspC ℓ)
          + 576 * (-192 * ((Real.pi : ℂ) * Complex.I * (τ : ℂ)
              + Work.Asymptotics.Compact.cuspC ℓ) + 72) * Work.Kernels.qParamFun τ
          + 27648 * ((Real.pi : ℂ) * Complex.I * (τ : ℂ)
              + Work.Asymptotics.Compact.cuspC ℓ) * Work.Kernels.qParamFun τ)

/-- **The purely atomic cancellation.**  `Term` equals the sum of the four `O(q²)` remainders
`E₆E₄³-1-216q`, `ΔE₆-q`, `E₄Δ-q`, `E₄⁴-1-960q` weighted by `τ`-atoms. -/
private lemma Term_eq (ℓ : Work.Kernels.LogLambdaData) (τ : ℍ) :
    Term ℓ τ
      = - Complex.I * (τ : ℂ) * (Work.Kernels.E6Fun τ * (Work.Kernels.E4Fun τ) ^ 3 - 1
            - 216 * Work.Kernels.qParamFun τ)
        + 240 * Complex.I * (τ : ℂ) * (Work.Kernels.DeltaFun τ * Work.Kernels.E6Fun τ
            - Work.Kernels.qParamFun τ)
        + ((3456 : ℂ) * (Real.pi : ℂ))⁻¹ * Work.Asymptotics.Compact.cuspC ℓ
            * (3400704 * (Work.Kernels.E4Fun τ * Work.Kernels.DeltaFun τ
                - Work.Kernels.qParamFun τ)
              - 3456 * ((Work.Kernels.E4Fun τ) ^ 4 - 1
                - 960 * Work.Kernels.qParamFun τ))
        - ((3456 : ℂ) * (Real.pi : ℂ))⁻¹ * 41472
            * (Work.Kernels.E4Fun τ * Work.Kernels.DeltaFun τ
              - Work.Kernels.qParamFun τ) := by
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  rw [Term]
  field_simp
  ring

/-- **The bound for the atomic part.** -/
private lemma Term_bound (ℓ : Work.Kernels.LogLambdaData) :
    ∃ C N : ℝ, 0 < C ∧ 0 ≤ N ∧ ∀ τ : ℍ, Work.Asymptotics.Funnel τ →
      ‖Term ℓ τ‖ ≤ C * (Work.Kernels.scale τ) ^ N * ‖Work.Kernels.qParamFun τ‖ ^ 2 := by
  obtain ⟨C1, hC1, h1⟩ := isBigOq_E6E4cube_sub_one_sub
  obtain ⟨C2, hC2, h2⟩ := isBigOq_DeltaE6_sub
  obtain ⟨C3, hC3, h3⟩ := isBigOq_E4Delta_sub_q
  obtain ⟨C4, hC4, h4⟩ := isBigOq_E4four_sub_one_sub
  have hcc : ‖Work.Asymptotics.Compact.cuspC ℓ‖ = 4 * Real.log 2 := by
    have h1 : Work.Asymptotics.Compact.cuspC ℓ = Work.Asymptotics.cuspL ℓ := rfl
    rw [h1, Work.Asymptotics.CuspL_eq ℓ]
    rw [norm_mul, Complex.norm_ofNat]
    congr 1
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.log_pos (by norm_num))]
  have hL2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  set K : ℝ := C1 + 240 * C2 + ((3456 * Real.pi)⁻¹) * (4 * Real.log 2)
      * (3400704 * C3 + 3456 * C4) + ((3456 * Real.pi)⁻¹) * 41472 * C3 + 1 with hK
  have hKpos : 0 < K := by rw [hK]; positivity
  refine ⟨K, 1, hKpos, by norm_num, fun τ hτ => ?_⟩
  have him : (1 : ℝ) ≤ τ.im := Work.Asymptotics.Funnel.im_one hτ
  have hq0 : (0 : ℝ) ≤ ‖Work.Kernels.qParamFun τ‖ := norm_nonneg _
  have hs : (1 : ℝ) ≤ Work.Kernels.scale τ := Work.Kernels.one_le_scale τ
  have ht : ‖(τ : ℂ)‖ ≤ Work.Kernels.scale τ := Work.Kernels.coe_norm_le_scale τ
  have hspos : (0 : ℝ) < Work.Kernels.scale τ := Work.Kernels.scale_pos τ
  have hA := h1 τ him
  have hB := h2 τ him
  have hCc := h3 τ him
  have hD := h4 τ him
  have hpi0 : (0 : ℝ) < Real.pi := Real.pi_pos
  have h3456 : ‖(((3456 : ℂ) * (Real.pi : ℂ))⁻¹)‖ = (3456 * Real.pi)⁻¹ := by
    rw [norm_inv, norm_mul, Complex.norm_ofNat, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos Real.pi_pos]
  have hpio : (Real.pi : ℂ) * Complex.I * (τ : ℂ) = ((Real.pi : ℂ) * Complex.I) * (τ : ℂ) := by
    ring
  rw [Term_eq ℓ τ]
  have hnorm : ‖- Complex.I * (τ : ℂ) * (Work.Kernels.E6Fun τ * (Work.Kernels.E4Fun τ) ^ 3 - 1
          - 216 * Work.Kernels.qParamFun τ)
        + 240 * Complex.I * (τ : ℂ) * (Work.Kernels.DeltaFun τ * Work.Kernels.E6Fun τ
          - Work.Kernels.qParamFun τ)
        + ((3456 : ℂ) * (Real.pi : ℂ))⁻¹ * Work.Asymptotics.Compact.cuspC ℓ
            * (3400704 * (Work.Kernels.E4Fun τ * Work.Kernels.DeltaFun τ
                - Work.Kernels.qParamFun τ)
              - 3456 * ((Work.Kernels.E4Fun τ) ^ 4 - 1
                - 960 * Work.Kernels.qParamFun τ))
        - ((3456 : ℂ) * (Real.pi : ℂ))⁻¹ * 41472
            * (Work.Kernels.E4Fun τ * Work.Kernels.DeltaFun τ
              - Work.Kernels.qParamFun τ)‖
      ≤ ‖(τ : ℂ)‖ * (C1 * ‖Work.Kernels.qParamFun τ‖ ^ 2)
        + 240 * ‖(τ : ℂ)‖ * (C2 * ‖Work.Kernels.qParamFun τ‖ ^ 2)
        + ((3456 * Real.pi)⁻¹) * (4 * Real.log 2)
            * (3400704 * (C3 * ‖Work.Kernels.qParamFun τ‖ ^ 2)
              + 3456 * (C4 * ‖Work.Kernels.qParamFun τ‖ ^ 2))
        + ((3456 * Real.pi)⁻¹) * 41472 * (C3 * ‖Work.Kernels.qParamFun τ‖ ^ 2) := by
    have h1' : ‖- Complex.I * (τ : ℂ) * (Work.Kernels.E6Fun τ * (Work.Kernels.E4Fun τ) ^ 3
        - 1 - 216 * Work.Kernels.qParamFun τ)‖
        = ‖(τ : ℂ)‖ * ‖Work.Kernels.E6Fun τ * (Work.Kernels.E4Fun τ) ^ 3 - 1
            - 216 * Work.Kernels.qParamFun τ‖ := by
      rw [norm_mul, norm_mul, norm_neg, Complex.norm_I, one_mul, mul_comm]
    have h2' : ‖240 * Complex.I * (τ : ℂ) * (Work.Kernels.DeltaFun τ * Work.Kernels.E6Fun τ
        - Work.Kernels.qParamFun τ)‖
        = 240 * ‖(τ : ℂ)‖ * ‖Work.Kernels.DeltaFun τ * Work.Kernels.E6Fun τ
            - Work.Kernels.qParamFun τ‖ := by
      rw [norm_mul, norm_mul, norm_mul, Complex.norm_I, Complex.norm_ofNat, mul_one]
    have h3' : ‖((3456 : ℂ) * (Real.pi : ℂ))⁻¹ * Work.Asymptotics.Compact.cuspC ℓ
        * (3400704 * (Work.Kernels.E4Fun τ * Work.Kernels.DeltaFun τ
            - Work.Kernels.qParamFun τ)
          - 3456 * ((Work.Kernels.E4Fun τ) ^ 4 - 1
            - 960 * Work.Kernels.qParamFun τ))‖
        = ((3456 * Real.pi)⁻¹) * ‖Work.Asymptotics.Compact.cuspC ℓ‖
          * ‖3400704 * (Work.Kernels.E4Fun τ * Work.Kernels.DeltaFun τ
              - Work.Kernels.qParamFun τ)
            - 3456 * ((Work.Kernels.E4Fun τ) ^ 4 - 1
              - 960 * Work.Kernels.qParamFun τ)‖ := by
      rw [norm_mul, norm_mul, h3456]
    have h4' : ‖((3456 : ℂ) * (Real.pi : ℂ))⁻¹ * 41472
        * (Work.Kernels.E4Fun τ * Work.Kernels.DeltaFun τ - Work.Kernels.qParamFun τ)‖
        = ((3456 * Real.pi)⁻¹) * 41472
          * ‖Work.Kernels.E4Fun τ * Work.Kernels.DeltaFun τ
              - Work.Kernels.qParamFun τ‖ := by
      rw [norm_mul, norm_mul, h3456, Complex.norm_ofNat]
    have h34 : ‖3400704 * (Work.Kernels.E4Fun τ * Work.Kernels.DeltaFun τ
        - Work.Kernels.qParamFun τ)
        - 3456 * ((Work.Kernels.E4Fun τ) ^ 4 - 1 - 960 * Work.Kernels.qParamFun τ)‖
        ≤ 3400704 * (C3 * ‖Work.Kernels.qParamFun τ‖ ^ 2)
          + 3456 * (C4 * ‖Work.Kernels.qParamFun τ‖ ^ 2) := by
      refine le_trans (norm_sub_le _ _) ?_
      rw [norm_mul, norm_mul, Complex.norm_ofNat, Complex.norm_ofNat]
      have := mul_le_mul_of_nonneg_left hCc (by norm_num : (0:ℝ) ≤ 3400704)
      have hb := mul_le_mul_of_nonneg_left hD (by norm_num : (0:ℝ) ≤ 3456)
      linarith
    calc _ ≤ ‖- Complex.I * (τ : ℂ) * (Work.Kernels.E6Fun τ * (Work.Kernels.E4Fun τ) ^ 3
              - 1 - 216 * Work.Kernels.qParamFun τ)‖
            + ‖240 * Complex.I * (τ : ℂ) * (Work.Kernels.DeltaFun τ * Work.Kernels.E6Fun τ
                - Work.Kernels.qParamFun τ)‖
            + ‖((3456 : ℂ) * (Real.pi : ℂ))⁻¹ * Work.Asymptotics.Compact.cuspC ℓ
                * (3400704 * (Work.Kernels.E4Fun τ * Work.Kernels.DeltaFun τ
                    - Work.Kernels.qParamFun τ)
                  - 3456 * ((Work.Kernels.E4Fun τ) ^ 4 - 1
                    - 960 * Work.Kernels.qParamFun τ))‖
            + ‖((3456 : ℂ) * (Real.pi : ℂ))⁻¹ * 41472
                * (Work.Kernels.E4Fun τ * Work.Kernels.DeltaFun τ
                  - Work.Kernels.qParamFun τ)‖ := by
          have h7 := norm_add_le (- Complex.I * (τ : ℂ) * (Work.Kernels.E6Fun τ * (Work.Kernels.E4Fun τ) ^ 3
              - 1 - 216 * Work.Kernels.qParamFun τ)
            + 240 * Complex.I * (τ : ℂ) * (Work.Kernels.DeltaFun τ * Work.Kernels.E6Fun τ
              - Work.Kernels.qParamFun τ)
            + ((3456 : ℂ) * (Real.pi : ℂ))⁻¹ * Work.Asymptotics.Compact.cuspC ℓ
                * (3400704 * (Work.Kernels.E4Fun τ * Work.Kernels.DeltaFun τ
                    - Work.Kernels.qParamFun τ)
                  - 3456 * ((Work.Kernels.E4Fun τ) ^ 4 - 1
                    - 960 * Work.Kernels.qParamFun τ)))
            (- (((3456 : ℂ) * (Real.pi : ℂ))⁻¹ * 41472
                * (Work.Kernels.E4Fun τ * Work.Kernels.DeltaFun τ
                  - Work.Kernels.qParamFun τ)))
          have h8 := norm_add_le (- Complex.I * (τ : ℂ) * (Work.Kernels.E6Fun τ * (Work.Kernels.E4Fun τ) ^ 3
              - 1 - 216 * Work.Kernels.qParamFun τ)
            + 240 * Complex.I * (τ : ℂ) * (Work.Kernels.DeltaFun τ * Work.Kernels.E6Fun τ
              - Work.Kernels.qParamFun τ))
            (((3456 : ℂ) * (Real.pi : ℂ))⁻¹ * Work.Asymptotics.Compact.cuspC ℓ
                * (3400704 * (Work.Kernels.E4Fun τ * Work.Kernels.DeltaFun τ
                    - Work.Kernels.qParamFun τ)
                  - 3456 * ((Work.Kernels.E4Fun τ) ^ 4 - 1
                    - 960 * Work.Kernels.qParamFun τ)))
          have h9 := norm_add_le (- Complex.I * (τ : ℂ) * (Work.Kernels.E6Fun τ * (Work.Kernels.E4Fun τ) ^ 3
              - 1 - 216 * Work.Kernels.qParamFun τ))
            (240 * Complex.I * (τ : ℂ) * (Work.Kernels.DeltaFun τ * Work.Kernels.E6Fun τ
              - Work.Kernels.qParamFun τ))
          rw [norm_neg] at h7
          simp only [sub_eq_add_neg] at h7 h8 h9 ⊢
          linarith
      _ ≤ ‖(τ : ℂ)‖ * (C1 * ‖Work.Kernels.qParamFun τ‖ ^ 2)
            + 240 * ‖(τ : ℂ)‖ * (C2 * ‖Work.Kernels.qParamFun τ‖ ^ 2)
            + ((3456 * Real.pi)⁻¹) * (4 * Real.log 2)
                * (3400704 * (C3 * ‖Work.Kernels.qParamFun τ‖ ^ 2)
                  + 3456 * (C4 * ‖Work.Kernels.qParamFun τ‖ ^ 2))
            + ((3456 * Real.pi)⁻¹) * 41472 * (C3 * ‖Work.Kernels.qParamFun τ‖ ^ 2) := by
          rw [h1', h2', h3', h4', hcc]
          have ha := mul_le_mul_of_nonneg_left hA (norm_nonneg (τ : ℂ))
          have hb := mul_le_mul_of_nonneg_left hB (by positivity : (0:ℝ) ≤ 240 * ‖(τ : ℂ)‖)
          have hc := mul_le_mul_of_nonneg_left h34
            (by positivity : (0:ℝ) ≤ ((3456 * Real.pi)⁻¹) * (4 * Real.log 2))
          have hd := mul_le_mul_of_nonneg_left hCc
            (by positivity : (0:ℝ) ≤ ((3456 * Real.pi)⁻¹) * 41472)
          linarith
  refine le_trans hnorm ?_
  rw [Real.rpow_one, hK]
  set q2 : ℝ := ‖Work.Kernels.qParamFun τ‖ ^ 2 with hq2def
  have hq2 : (0 : ℝ) ≤ q2 := by rw [hq2def]; positivity
  have hqle : q2 ≤ Work.Kernels.scale τ * q2 := by nlinarith [hs, hq2, hspos]
  have hB : (0 : ℝ) ≤ ((3456 * Real.pi)⁻¹) * (4 * Real.log 2) := by positivity
  have hE : (0 : ℝ) ≤ ((3456 * Real.pi)⁻¹) := by positivity
  have hlast : (0 : ℝ) ≤ Work.Kernels.scale τ * q2 := mul_nonneg hspos.le hq2
  have e1 : ‖(τ : ℂ)‖ * (C1 * q2) ≤ Work.Kernels.scale τ * (C1 * q2) :=
    mul_le_mul_of_nonneg_right ht (by positivity)
  have e2 : 240 * ‖(τ : ℂ)‖ * (C2 * q2) ≤ 240 * Work.Kernels.scale τ * (C2 * q2) :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ht (by norm_num : (0 : ℝ) ≤ 240))
      (by positivity)
  have e3 : ((3456 * Real.pi)⁻¹) * (4 * Real.log 2) * (3400704 * (C3 * q2))
      ≤ ((3456 * Real.pi)⁻¹) * (4 * Real.log 2) * 3400704 * C3 * Work.Kernels.scale τ * q2 := by
    have h' : C3 * q2 ≤ C3 * (Work.Kernels.scale τ * q2) :=
      mul_le_mul_of_nonneg_left hqle hC3.le
    calc ((3456 * Real.pi)⁻¹) * (4 * Real.log 2) * (3400704 * (C3 * q2))
        ≤ ((3456 * Real.pi)⁻¹) * (4 * Real.log 2)
            * (3400704 * (C3 * (Work.Kernels.scale τ * q2))) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left h' (by norm_num : (0 : ℝ) ≤ 3400704)) hB
      _ = ((3456 * Real.pi)⁻¹) * (4 * Real.log 2) * 3400704 * C3
            * Work.Kernels.scale τ * q2 := by ring
  have e4 : ((3456 * Real.pi)⁻¹) * (4 * Real.log 2) * (3456 * (C4 * q2))
      ≤ ((3456 * Real.pi)⁻¹) * (4 * Real.log 2) * 3456 * C4 * Work.Kernels.scale τ * q2 := by
    have h' : C4 * q2 ≤ C4 * (Work.Kernels.scale τ * q2) :=
      mul_le_mul_of_nonneg_left hqle hC4.le
    calc ((3456 * Real.pi)⁻¹) * (4 * Real.log 2) * (3456 * (C4 * q2))
        ≤ ((3456 * Real.pi)⁻¹) * (4 * Real.log 2)
            * (3456 * (C4 * (Work.Kernels.scale τ * q2))) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left h' (by norm_num : (0 : ℝ) ≤ 3456)) hB
      _ = ((3456 * Real.pi)⁻¹) * (4 * Real.log 2) * 3456 * C4
            * Work.Kernels.scale τ * q2 := by ring
  have e5 : ((3456 * Real.pi)⁻¹) * (41472 * (C3 * q2))
      ≤ ((3456 * Real.pi)⁻¹) * 41472 * C3 * Work.Kernels.scale τ * q2 := by
    have h' : C3 * q2 ≤ C3 * (Work.Kernels.scale τ * q2) :=
      mul_le_mul_of_nonneg_left hqle hC3.le
    calc ((3456 * Real.pi)⁻¹) * (41472 * (C3 * q2))
        ≤ ((3456 * Real.pi)⁻¹) * (41472 * (C3 * (Work.Kernels.scale τ * q2))) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left h' (by norm_num : (0 : ℝ) ≤ 41472)) hE
      _ = ((3456 * Real.pi)⁻¹) * 41472 * C3 * Work.Kernels.scale τ * q2 := by ring
  linarith [e1, e2, e3, e4, e5, hlast]




/-! ## The `ψ`-correction in `B0`

`Ψcorr = 1152·ψ₂(E₁₄-1) + 576·ψ₄(E₄³-1) - 373248·Δψ₄` is the difference between
`Ψ = 1152ψ₂E₁₄ + 576E₄³ψ₄ - 373248Δψ₄` and `576(2ψ₂+ψ₄)`.  Subtracting the explicit
`27648Λ₀q` leaves an `O(q²)` quantity; the only analytic input is `ψ₂, ψ₄ = 2Λ₀ + O(q)`. -/

/-- The `ψ`-correction in the cleared form of `Δ·B0`. -/
private noncomputable def PsiCorr (ℓ : Work.Kernels.LogLambdaData) (τ : ℍ) : ℂ :=
  1152 * (Work.Kernels.psi2 ℓ τ * (Work.Kernels.E14Fun τ - 1))
    + 576 * (Work.Kernels.psi4 ℓ τ * ((Work.Kernels.E4Fun τ) ^ 3 - 1))
    - 373248 * (Work.Kernels.DeltaFun τ * Work.Kernels.psi4 ℓ τ)

/-- **The `ψ`-correction is `O(q²)`.** -/
private lemma PsiCorr_bound (ℓ : Work.Kernels.LogLambdaData) :
    ∃ C N : ℝ, 0 < C ∧ 0 ≤ N ∧ ∀ τ : ℍ, Work.Asymptotics.Funnel τ →
      ‖PsiCorr ℓ τ - 27648 * Lam0 ℓ τ * Work.Kernels.qParamFun τ‖
        ≤ C * (Work.Kernels.scale τ) ^ N * ‖Work.Kernels.qParamFun τ‖ ^ 2 := by
  obtain ⟨Cp, Np, hCp, hNp, hp⟩ :=
    Work.Asymptotics.KhatE1Core.psi_individual_first_order ℓ
  obtain ⟨C1, hC1, h1⟩ := isBigOq_E14_sub_one_add
  obtain ⟨C2, hC2, h2⟩ := isBigOq_E4cube_sub_one_sub
  obtain ⟨C3, hC3, h3⟩ := Work.Asymptotics.DeltaFun_isBigOq
  have hcc : ‖Work.Asymptotics.Compact.cuspC ℓ‖ = 4 * Real.log 2 := by
    have h1' : Work.Asymptotics.Compact.cuspC ℓ = Work.Asymptotics.cuspL ℓ := rfl
    rw [h1', Work.Asymptotics.CuspL_eq ℓ]
    rw [norm_mul, Complex.norm_ofNat]
    congr 1
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.log_pos (by norm_num))]
  have hpi4 : (0 : ℝ) < Real.pi + 4 * Real.log 2 := by
    have := Real.log_pos (by norm_num : (1:ℝ) < 2)
    nlinarith [Real.pi_pos]
  set M : ℝ := max Np 1 with hM
  have hNpM : Np ≤ M := le_max_left _ _
  have h1M : (1 : ℝ) ≤ M := le_max_right _ _
  set K : ℝ := 2 * (Real.pi + 4 * Real.log 2) + Cp with hK
  have hK0 : 0 < K := by rw [hK]; positivity
  refine ⟨1152 * ((K * C1 + 24 * Cp) + (K * C2 + 720 * Cp)) + 373248 * (K * C3 + Cp) + 1,
    M, by positivity, by positivity, fun τ hτ => ?_⟩
  have him : (1 : ℝ) ≤ τ.im := Work.Asymptotics.Funnel.im_one hτ
  have hs : (1 : ℝ) ≤ Work.Kernels.scale τ := Work.Kernels.one_le_scale τ
  have hspos : (0 : ℝ) < Work.Kernels.scale τ := Work.Kernels.scale_pos τ
  have hq0 : (0 : ℝ) ≤ ‖Work.Kernels.qParamFun τ‖ := norm_nonneg _
  have hq1 : ‖Work.Kernels.qParamFun τ‖ ≤ 1 := by
    rw [Work.Asymptotics.norm_qParamFun, Real.exp_le_one_iff]; nlinarith [Real.pi_pos, him]
  have hsM : (0 : ℝ) ≤ (Work.Kernels.scale τ) ^ M :=
    Real.rpow_nonneg (le_trans zero_le_one hs) M
  have hsM1 : (1 : ℝ) ≤ (Work.Kernels.scale τ) ^ M := Real.one_le_rpow hs (by linarith)
  have hNpM' : (Work.Kernels.scale τ) ^ Np ≤ (Work.Kernels.scale τ) ^ M :=
    Real.rpow_le_rpow_of_exponent_le hs hNpM
  have hLam : ‖Lam0 ℓ τ‖ ≤ (Real.pi + 4 * Real.log 2) * Work.Kernels.scale τ := by
    rw [Lam0]
    calc ‖(Real.pi : ℂ) * Complex.I * (τ : ℂ) + Work.Asymptotics.Compact.cuspC ℓ‖
        ≤ ‖(Real.pi : ℂ) * Complex.I * (τ : ℂ)‖
            + ‖Work.Asymptotics.Compact.cuspC ℓ‖ := norm_add_le _ _
      _ = Real.pi * ‖(τ : ℂ)‖ + 4 * Real.log 2 := by
          rw [norm_mul, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
            abs_of_pos Real.pi_pos, hcc]
      _ ≤ Real.pi * Work.Kernels.scale τ + 4 * Real.log 2 := by
          have hcs := Work.Kernels.coe_norm_le_scale τ
          have h := mul_le_mul_of_nonneg_left hcs (le_of_lt Real.pi_pos)
          linarith
      _ ≤ (Real.pi + 4 * Real.log 2) * Work.Kernels.scale τ := by
          have h1'' : Real.pi ≤ Real.pi * Work.Kernels.scale τ := by
            nlinarith [hs, Real.pi_pos]
          have h2'' : 4 * Real.log 2
              ≤ (4 * Real.log 2) * Work.Kernels.scale τ := by
            nlinarith [hs, Real.log_pos (by norm_num : (1:ℝ) < 2)]
          nlinarith [h1'', h2'']
  obtain ⟨hp2, hp4⟩ := hp τ hτ
  have he2 : ‖Work.Kernels.psi2 ℓ τ - 2 * Lam0 ℓ τ‖ ≤ Cp * (Work.Kernels.scale τ) ^ M
      * ‖Work.Kernels.qParamFun τ‖ := by
    refine le_trans hp2 (le_trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hNpM' hCp.le) hq0) ?_)
    rw [mul_assoc]
  have he4 : ‖Work.Kernels.psi4 ℓ τ - 2 * Lam0 ℓ τ‖ ≤ Cp * (Work.Kernels.scale τ) ^ M
      * ‖Work.Kernels.qParamFun τ‖ := by
    refine le_trans hp4 (le_trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hNpM' hCp.le) hq0) ?_)
    rw [mul_assoc]
  have hpsi2 : ‖Work.Kernels.psi2 ℓ τ‖ ≤ K * (Work.Kernels.scale τ) ^ M := by
    have h2 := he2
    have h3 : ‖2 * Lam0 ℓ τ‖ ≤ 2 * ((Real.pi + 4 * Real.log 2) * Work.Kernels.scale τ) := by
      rw [norm_mul, Complex.norm_ofNat]
      linarith [hLam]
    calc ‖Work.Kernels.psi2 ℓ τ‖
        = ‖(Work.Kernels.psi2 ℓ τ - 2 * Lam0 ℓ τ) + 2 * Lam0 ℓ τ‖ := by ring_nf
      _ ≤ ‖Work.Kernels.psi2 ℓ τ - 2 * Lam0 ℓ τ‖ + ‖2 * Lam0 ℓ τ‖ := norm_add_le _ _
      _ ≤ Cp * (Work.Kernels.scale τ) ^ M * ‖Work.Kernels.qParamFun τ‖
            + 2 * ((Real.pi + 4 * Real.log 2) * Work.Kernels.scale τ) := by linarith
      _ ≤ Cp * (Work.Kernels.scale τ) ^ M
            + 2 * ((Real.pi + 4 * Real.log 2) * Work.Kernels.scale τ) := by
          have := mul_le_mul_of_nonneg_left hq1
            (mul_nonneg hCp.le (Real.rpow_nonneg (le_trans zero_le_one hs) M))
          nlinarith [this]
      _ ≤ K * (Work.Kernels.scale τ) ^ M := by
          rw [hK]
          have hscaleM : Work.Kernels.scale τ ≤ (Work.Kernels.scale τ) ^ M := by
            calc Work.Kernels.scale τ = (Work.Kernels.scale τ) ^ (1 : ℝ) :=
                  (Real.rpow_one _).symm
              _ ≤ (Work.Kernels.scale τ) ^ M := Real.rpow_le_rpow_of_exponent_le hs h1M
          have h2'' : 2 * ((Real.pi + 4 * Real.log 2) * Work.Kernels.scale τ)
              ≤ 2 * (Real.pi + 4 * Real.log 2) * (Work.Kernels.scale τ) ^ M := by
            nlinarith [mul_le_mul_of_nonneg_left hscaleM hpi4.le, hpi4.le]
          nlinarith [h2'', hCp.le, hsM]
  have hpsi4 : ‖Work.Kernels.psi4 ℓ τ‖ ≤ K * (Work.Kernels.scale τ) ^ M := by
    have h2 := he4
    have h3 : ‖2 * Lam0 ℓ τ‖ ≤ 2 * ((Real.pi + 4 * Real.log 2) * Work.Kernels.scale τ) := by
      rw [norm_mul, Complex.norm_ofNat]
      linarith [hLam]
    calc ‖Work.Kernels.psi4 ℓ τ‖
        = ‖(Work.Kernels.psi4 ℓ τ - 2 * Lam0 ℓ τ) + 2 * Lam0 ℓ τ‖ := by ring_nf
      _ ≤ ‖Work.Kernels.psi4 ℓ τ - 2 * Lam0 ℓ τ‖ + ‖2 * Lam0 ℓ τ‖ := norm_add_le _ _
      _ ≤ Cp * (Work.Kernels.scale τ) ^ M * ‖Work.Kernels.qParamFun τ‖
            + 2 * ((Real.pi + 4 * Real.log 2) * Work.Kernels.scale τ) := by linarith
      _ ≤ Cp * (Work.Kernels.scale τ) ^ M
            + 2 * ((Real.pi + 4 * Real.log 2) * Work.Kernels.scale τ) := by
          have := mul_le_mul_of_nonneg_left hq1
            (mul_nonneg hCp.le (Real.rpow_nonneg (le_trans zero_le_one hs) M))
          nlinarith [this]
      _ ≤ K * (Work.Kernels.scale τ) ^ M := by
          rw [hK]
          have hscaleM : Work.Kernels.scale τ ≤ (Work.Kernels.scale τ) ^ M := by
            calc Work.Kernels.scale τ = (Work.Kernels.scale τ) ^ (1 : ℝ) :=
                  (Real.rpow_one _).symm
              _ ≤ (Work.Kernels.scale τ) ^ M := Real.rpow_le_rpow_of_exponent_le hs h1M
          have h2'' : 2 * ((Real.pi + 4 * Real.log 2) * Work.Kernels.scale τ)
              ≤ 2 * (Real.pi + 4 * Real.log 2) * (Work.Kernels.scale τ) ^ M := by
            nlinarith [mul_le_mul_of_nonneg_left hscaleM hpi4.le, hpi4.le]
          nlinarith [h2'', hCp.le, hsM]
  have hkey : PsiCorr ℓ τ - 27648 * Lam0 ℓ τ * Work.Kernels.qParamFun τ
      = 1152 * (Work.Kernels.psi2 ℓ τ
            * ((Work.Kernels.E4Fun τ) ^ 2 * Work.Kernels.E6Fun τ - 1
                + 24 * Work.Kernels.qParamFun τ)
          - 24 * Work.Kernels.qParamFun τ * (Work.Kernels.psi2 ℓ τ - 2 * Lam0 ℓ τ))
        + 576 * (Work.Kernels.psi4 ℓ τ * ((Work.Kernels.E4Fun τ) ^ 3 - 1
              - 720 * Work.Kernels.qParamFun τ)
            + 720 * Work.Kernels.qParamFun τ * (Work.Kernels.psi4 ℓ τ - 2 * Lam0 ℓ τ))
        - 373248 * ((Work.Kernels.DeltaFun τ - Work.Kernels.qParamFun τ) * Work.Kernels.psi4 ℓ τ
            + Work.Kernels.qParamFun τ * (Work.Kernels.psi4 ℓ τ - 2 * Lam0 ℓ τ)) := by
    rw [PsiCorr]
    ring
  rw [hkey]
  set P : ℂ := Work.Kernels.psi2 ℓ τ * ((Work.Kernels.E4Fun τ) ^ 2 * Work.Kernels.E6Fun τ
        - 1 + 24 * Work.Kernels.qParamFun τ)
      - 24 * Work.Kernels.qParamFun τ * (Work.Kernels.psi2 ℓ τ - 2 * Lam0 ℓ τ) with hP
  set Q : ℂ := Work.Kernels.psi4 ℓ τ * ((Work.Kernels.E4Fun τ) ^ 3 - 1
        - 720 * Work.Kernels.qParamFun τ)
      + 720 * Work.Kernels.qParamFun τ * (Work.Kernels.psi4 ℓ τ - 2 * Lam0 ℓ τ) with hQ
  set R : ℂ := (Work.Kernels.DeltaFun τ - Work.Kernels.qParamFun τ) * Work.Kernels.psi4 ℓ τ
      + Work.Kernels.qParamFun τ * (Work.Kernels.psi4 ℓ τ - 2 * Lam0 ℓ τ) with hR
  have hA1 := h1 τ him
  have hA2 := h2 τ him
  have hA3 := h3 τ him
  have hS1 : ‖Work.Kernels.psi2 ℓ τ * ((Work.Kernels.E4Fun τ) ^ 2 * Work.Kernels.E6Fun τ
        - 1 + 24 * Work.Kernels.qParamFun τ)‖
      ≤ K * (Work.Kernels.scale τ) ^ M * (C1 * ‖Work.Kernels.qParamFun τ‖ ^ 2) := by
    rw [norm_mul]
    exact mul_le_mul hpsi2 hA1 (by positivity) (by positivity)
  have hS2 : ‖24 * Work.Kernels.qParamFun τ * (Work.Kernels.psi2 ℓ τ - 2 * Lam0 ℓ τ)‖
      ≤ 24 * Cp * (Work.Kernels.scale τ) ^ M * ‖Work.Kernels.qParamFun τ‖ ^ 2 := by
    rw [norm_mul, norm_mul, Complex.norm_ofNat]
    have h := mul_le_mul_of_nonneg_left he2 hq0
    have h4 : (0 : ℝ) ≤ Cp * (Work.Kernels.scale τ) ^ M * ‖Work.Kernels.qParamFun τ‖ := by
      positivity
    nlinarith [h, hq0, h4, hCp.le, hsM]
  have hS3 : ‖Work.Kernels.psi4 ℓ τ * ((Work.Kernels.E4Fun τ) ^ 3 - 1
          - 720 * Work.Kernels.qParamFun τ)‖
      ≤ K * (Work.Kernels.scale τ) ^ M * (C2 * ‖Work.Kernels.qParamFun τ‖ ^ 2) := by
    rw [norm_mul]
    exact mul_le_mul hpsi4 hA2 (by positivity) (by positivity)
  have hS4 : ‖720 * Work.Kernels.qParamFun τ * (Work.Kernels.psi4 ℓ τ - 2 * Lam0 ℓ τ)‖
      ≤ 720 * Cp * (Work.Kernels.scale τ) ^ M * ‖Work.Kernels.qParamFun τ‖ ^ 2 := by
    rw [norm_mul, norm_mul, Complex.norm_ofNat]
    have h := mul_le_mul_of_nonneg_left he4 hq0
    have h4 : (0 : ℝ) ≤ Cp * (Work.Kernels.scale τ) ^ M * ‖Work.Kernels.qParamFun τ‖ := by
      positivity
    nlinarith [h, hq0, h4, hCp.le, hsM]
  have hS5 : ‖R‖ ≤ C3 * ‖Work.Kernels.qParamFun τ‖ ^ 2 * (K * (Work.Kernels.scale τ) ^ M)
      + Cp * (Work.Kernels.scale τ) ^ M * ‖Work.Kernels.qParamFun τ‖ ^ 2 := by
    rw [hR]
    refine le_trans (norm_add_le _ _) ?_
    refine add_le_add ?_ ?_
    · rw [norm_mul]
      exact mul_le_mul hA3 hpsi4 (by positivity) (by positivity)
    · rw [norm_mul]
      have h := mul_le_mul_of_nonneg_left he4 hq0
      have h4 : (0 : ℝ) ≤ Cp * (Work.Kernels.scale τ) ^ M * ‖Work.Kernels.qParamFun τ‖ := by
        positivity
      nlinarith [h, hq0, h4]
  have hPb : ‖P‖ ≤ K * (Work.Kernels.scale τ) ^ M * (C1 * ‖Work.Kernels.qParamFun τ‖ ^ 2)
      + 24 * Cp * (Work.Kernels.scale τ) ^ M * ‖Work.Kernels.qParamFun τ‖ ^ 2 := by
    rw [hP]
    have := norm_sub_le (Work.Kernels.psi2 ℓ τ * ((Work.Kernels.E4Fun τ) ^ 2
        * Work.Kernels.E6Fun τ - 1 + 24 * Work.Kernels.qParamFun τ))
      (24 * Work.Kernels.qParamFun τ * (Work.Kernels.psi2 ℓ τ - 2 * Lam0 ℓ τ))
    linarith [hS1, hS2, this, norm_nonneg (Work.Kernels.psi2 ℓ τ * ((Work.Kernels.E4Fun τ) ^ 2
        * Work.Kernels.E6Fun τ - 1 + 24 * Work.Kernels.qParamFun τ)),
      norm_nonneg (24 * Work.Kernels.qParamFun τ * (Work.Kernels.psi2 ℓ τ - 2 * Lam0 ℓ τ))]
  have hQb : ‖Q‖ ≤ K * (Work.Kernels.scale τ) ^ M * (C2 * ‖Work.Kernels.qParamFun τ‖ ^ 2)
      + 720 * Cp * (Work.Kernels.scale τ) ^ M * ‖Work.Kernels.qParamFun τ‖ ^ 2 := by
    rw [hQ]
    exact le_trans (norm_add_le (Work.Kernels.psi4 ℓ τ * ((Work.Kernels.E4Fun τ) ^ 3 - 1
        - 720 * Work.Kernels.qParamFun τ))
      (720 * Work.Kernels.qParamFun τ * (Work.Kernels.psi4 ℓ τ - 2 * Lam0 ℓ τ)))
      (add_le_add hS3 hS4)
  have hfinal : ‖1152 * P + 576 * Q - 373248 * R‖
      ≤ 1152 * (K * (Work.Kernels.scale τ) ^ M * (C1 * ‖Work.Kernels.qParamFun τ‖ ^ 2)
          + 24 * Cp * (Work.Kernels.scale τ) ^ M * ‖Work.Kernels.qParamFun τ‖ ^ 2)
        + 576 * (K * (Work.Kernels.scale τ) ^ M * (C2 * ‖Work.Kernels.qParamFun τ‖ ^ 2)
          + 720 * Cp * (Work.Kernels.scale τ) ^ M * ‖Work.Kernels.qParamFun τ‖ ^ 2)
        + 373248 * (C3 * ‖Work.Kernels.qParamFun τ‖ ^ 2 * (K * (Work.Kernels.scale τ) ^ M)
          + Cp * (Work.Kernels.scale τ) ^ M * ‖Work.Kernels.qParamFun τ‖ ^ 2) := by
    have h1 : ‖1152 * P‖ ≤ 1152 * (K * (Work.Kernels.scale τ) ^ M
        * (C1 * ‖Work.Kernels.qParamFun τ‖ ^ 2)
        + 24 * Cp * (Work.Kernels.scale τ) ^ M * ‖Work.Kernels.qParamFun τ‖ ^ 2) := by
      rw [norm_mul, Complex.norm_ofNat]
      exact mul_le_mul_of_nonneg_left hPb (by norm_num)
    have h2 : ‖576 * Q‖ ≤ 576 * (K * (Work.Kernels.scale τ) ^ M
        * (C2 * ‖Work.Kernels.qParamFun τ‖ ^ 2)
        + 720 * Cp * (Work.Kernels.scale τ) ^ M * ‖Work.Kernels.qParamFun τ‖ ^ 2) := by
      rw [norm_mul, Complex.norm_ofNat]
      exact mul_le_mul_of_nonneg_left hQb (by norm_num)
    have h3 : ‖373248 * R‖ ≤ 373248 * (C3 * ‖Work.Kernels.qParamFun τ‖ ^ 2
        * (K * (Work.Kernels.scale τ) ^ M)
        + Cp * (Work.Kernels.scale τ) ^ M * ‖Work.Kernels.qParamFun τ‖ ^ 2) := by
      rw [norm_mul, Complex.norm_ofNat]
      exact mul_le_mul_of_nonneg_left hS5 (by norm_num)
    calc ‖1152 * P + 576 * Q - 373248 * R‖
        ≤ ‖1152 * P + 576 * Q‖ + ‖373248 * R‖ := norm_sub_le _ _
      _ ≤ (‖1152 * P‖ + ‖576 * Q‖) + ‖373248 * R‖ := by
          linarith [norm_add_le (1152 * P) (576 * Q)]
      _ ≤ _ := by linarith [h1, h2, h3]
  refine le_trans hfinal ?_
  set q2 : ℝ := ‖Work.Kernels.qParamFun τ‖ ^ 2 with hq2def
  have hq2 : (0 : ℝ) ≤ q2 := by rw [hq2def]; positivity
  have hKM : (0 : ℝ) ≤ K * (Work.Kernels.scale τ) ^ M := mul_nonneg hK0.le hsM
  have hCpM : (0 : ℝ) ≤ Cp * (Work.Kernels.scale τ) ^ M := mul_nonneg hCp.le hsM
  rw [hq2def]
  nlinarith [hKM, hq2, hspos, hCp.le, hsM, hK0.le, hC1.le, hC2.le, hC3.le, hCpM,
    mul_nonneg hKM hq2, mul_nonneg hC1.le hq2, mul_nonneg hC2.le hq2, mul_nonneg hC3.le hq2,
    mul_nonneg hCpM hq2, mul_nonneg hC3.le (mul_nonneg hKM hq2)]






/-- **The bound for the `E(z)⁰`-coefficient `B0` of the funnel bracket.**

`Δ·B0 = (3456π)⁻¹·576·Eps + Term + (3456π)⁻¹·(Ψcorr - 27648Λ₀q)` with
`Eps = 2ψ₂+ψ₄-6Λ₀+(192Λ₀-72)q` (`psi_combo_first_order`), `Term` the atomic cancellation
(`Term_bound`) and `Ψcorr` the `ψ`-correction (`PsiCorr_bound`).  Hence `Δ·B0 = O(q² scale^N)`,
and dividing by `Δ` (`exists_Delta_Funnel_lower`) gives `B0 = O(q scale^N)`. -/
theorem B0_bound (ℓ : Work.Kernels.LogLambdaData) :
    ∃ C N : ℝ, 0 < C ∧ 0 ≤ N ∧ ∀ τ : ℍ, Work.Asymptotics.Funnel τ →
      ‖B0 ℓ τ‖ ≤ C * (Work.Kernels.scale τ) ^ N * ‖Work.Kernels.qParamFun τ‖ := by
  obtain ⟨Ce, Ne, hCe, hNe, he⟩ :=
    Work.Asymptotics.KhatE1Core.psi_combo_first_order ℓ
  obtain ⟨CT, NT, hCT, hNT, hT⟩ := Term_bound ℓ
  obtain ⟨CP, NP, hCP, hNP, hP⟩ := PsiCorr_bound ℓ
  obtain ⟨cd, hcd, hd⟩ := Work.Asymptotics.exists_Delta_Funnel_lower
  have hI2 : ‖(((3456 : ℂ) * (Real.pi : ℂ))⁻¹)‖ = (3456 * Real.pi)⁻¹ := by
    rw [norm_inv, norm_mul, Complex.norm_ofNat, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos Real.pi_pos]
  have hCpos : 0 < ((3456 * Real.pi)⁻¹ * (576 * Ce + CP) + CT) / cd + 1 := by positivity
  have hNpos : (0 : ℝ) ≤ max Ne (max NT NP) + 1 := by
    have h1 := le_max_left Ne (max NT NP)
    have h2 := le_max_right Ne (max NT NP)
    have h3 := le_max_left NT NP
    have h4 := le_max_right NT NP
    linarith
  refine ⟨((3456 * Real.pi)⁻¹ * (576 * Ce + CP) + CT) / cd + 1,
    max Ne (max NT NP) + 1, hCpos, hNpos, fun τ hτ => ?_⟩
  have him : (1 : ℝ) ≤ τ.im := Work.Asymptotics.Funnel.im_one hτ
  have hs : (1 : ℝ) ≤ Work.Kernels.scale τ := Work.Kernels.one_le_scale τ
  have hspos : (0 : ℝ) < Work.Kernels.scale τ := Work.Kernels.scale_pos τ
  have hq : (0 : ℝ) ≤ ‖Work.Kernels.qParamFun τ‖ := norm_nonneg _
  have hNle : (Work.Kernels.scale τ) ^ Ne ≤ (Work.Kernels.scale τ) ^ (max Ne (max NT NP)) :=
    Real.rpow_le_rpow_of_exponent_le hs (le_max_left Ne (max NT NP))
  have hNTle : (Work.Kernels.scale τ) ^ NT
      ≤ (Work.Kernels.scale τ) ^ (max Ne (max NT NP)) :=
    Real.rpow_le_rpow_of_exponent_le hs (le_trans (le_max_left NT NP) (le_max_right Ne (max NT NP)))
  have hNPle : (Work.Kernels.scale τ) ^ NP
      ≤ (Work.Kernels.scale τ) ^ (max Ne (max NT NP)) :=
    Real.rpow_le_rpow_of_exponent_le hs (le_trans (le_max_right NT NP) (le_max_right Ne (max NT NP)))
  have hSpos : (0 : ℝ) < (Work.Kernels.scale τ) ^ (max Ne (max NT NP) + 1) :=
    Real.rpow_pos_of_pos hspos _
  have hSle : (Work.Kernels.scale τ) ^ (max Ne (max NT NP)) ≤
      (Work.Kernels.scale τ) ^ (max Ne (max NT NP) + 1) := by
    have h1 : (1 : ℝ) ≤ Work.Kernels.scale τ ^ (max Ne (max NT NP)) :=
      Real.one_le_rpow hs (by positivity)
    calc Work.Kernels.scale τ ^ (max Ne (max NT NP))
        ≤ Work.Kernels.scale τ ^ (max Ne (max NT NP)) * Work.Kernels.scale τ := by
          nlinarith [h1, hspos]
      _ = Work.Kernels.scale τ ^ (max Ne (max NT NP) + 1) := by
          rw [Real.rpow_add_one hspos.ne']
  have he' : ‖2 * Work.Kernels.psi2 ℓ τ + Work.Kernels.psi4 ℓ τ
        - 6 * ((Real.pi : ℂ) * Complex.I * (τ : ℂ) + Work.Asymptotics.Compact.cuspC ℓ)
        + (192 * ((Real.pi : ℂ) * Complex.I * (τ : ℂ) + Work.Asymptotics.Compact.cuspC ℓ) - 72)
            * Work.Kernels.qParamFun τ‖
      ≤ Ce * (Work.Kernels.scale τ) ^ Ne * ‖Work.Kernels.qParamFun τ‖ ^ 2 := he τ hτ
  have hkey : Work.Kernels.DeltaFun τ * B0 ℓ τ
      = ((3456 : ℂ) * (Real.pi : ℂ))⁻¹ * 576 * (2 * Work.Kernels.psi2 ℓ τ
            + Work.Kernels.psi4 ℓ τ
            - 6 * ((Real.pi : ℂ) * Complex.I * (τ : ℂ) + Work.Asymptotics.Compact.cuspC ℓ)
            + (192 * ((Real.pi : ℂ) * Complex.I * (τ : ℂ) + Work.Asymptotics.Compact.cuspC ℓ) - 72)
                * Work.Kernels.qParamFun τ)
        + Term ℓ τ
        + ((3456 : ℂ) * (Real.pi : ℂ))⁻¹
            * (PsiCorr ℓ τ - 27648 * ((Real.pi : ℂ) * Complex.I * (τ : ℂ)
                + Work.Asymptotics.Compact.cuspC ℓ) * Work.Kernels.qParamFun τ) := by
    rw [Delta_mul_B0, Term, PsiCorr]
    ring_nf
  have hDne : Work.Kernels.DeltaFun τ ≠ 0 := Work.Kernels.ClassicalFacts.DeltaFun_ne_zero τ
  have hlow := hd τ hτ
  have hqpos : (0 : ℝ) < Real.exp (-(2 * Real.pi * τ.im)) := Real.exp_pos _
  have hbig : ‖Work.Kernels.DeltaFun τ * B0 ℓ τ‖
      ≤ ((3456 * Real.pi)⁻¹ * (576 * Ce + CP) + CT)
        * (Work.Kernels.scale τ) ^ (max Ne (max NT NP)) * ‖Work.Kernels.qParamFun τ‖ ^ 2 := by
    rw [hkey]
    have h1 : ‖(((3456 : ℂ) * (Real.pi : ℂ))⁻¹ * 576) * (2 * Work.Kernels.psi2 ℓ τ
          + Work.Kernels.psi4 ℓ τ
          - 6 * ((Real.pi : ℂ) * Complex.I * (τ : ℂ) + Work.Asymptotics.Compact.cuspC ℓ)
          + (192 * ((Real.pi : ℂ) * Complex.I * (τ : ℂ) + Work.Asymptotics.Compact.cuspC ℓ) - 72)
              * Work.Kernels.qParamFun τ)‖
        ≤ (3456 * Real.pi)⁻¹ * 576
          * (Ce * (Work.Kernels.scale τ) ^ (max Ne (max NT NP))
            * ‖Work.Kernels.qParamFun τ‖ ^ 2) := by
      rw [norm_mul, norm_mul, hI2, Complex.norm_ofNat]
      have hb : ‖2 * Work.Kernels.psi2 ℓ τ + Work.Kernels.psi4 ℓ τ
          - 6 * ((Real.pi : ℂ) * Complex.I * (τ : ℂ) + Work.Asymptotics.Compact.cuspC ℓ)
          + (192 * ((Real.pi : ℂ) * Complex.I * (τ : ℂ) + Work.Asymptotics.Compact.cuspC ℓ) - 72)
              * Work.Kernels.qParamFun τ‖
          ≤ Ce * (Work.Kernels.scale τ) ^ (max Ne (max NT NP))
            * ‖Work.Kernels.qParamFun τ‖ ^ 2 :=
        le_trans he' (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hNle hCe.le)
          (by positivity))
      exact mul_le_mul_of_nonneg_left hb (by positivity : (0 : ℝ) ≤ (3456 * Real.pi)⁻¹ * 576)
    have h2 : ‖Term ℓ τ‖ ≤ CT * (Work.Kernels.scale τ) ^ (max Ne (max NT NP))
        * ‖Work.Kernels.qParamFun τ‖ ^ 2 :=
      le_trans (hT τ hτ) (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hNTle hCT.le) (by positivity))
    have h3 : ‖((3456 : ℂ) * (Real.pi : ℂ))⁻¹
          * (PsiCorr ℓ τ - 27648 * ((Real.pi : ℂ) * Complex.I * (τ : ℂ)
              + Work.Asymptotics.Compact.cuspC ℓ) * Work.Kernels.qParamFun τ)‖
        ≤ (3456 * Real.pi)⁻¹ * (CP * (Work.Kernels.scale τ) ^ (max Ne (max NT NP))
            * ‖Work.Kernels.qParamFun τ‖ ^ 2) := by
      rw [norm_mul, hI2]
      exact mul_le_mul_of_nonneg_left (le_trans (hP τ hτ)
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hNPle hCP.le)
          (by positivity))) (by positivity)
    have h12 := norm_add_le ((((3456 : ℂ) * (Real.pi : ℂ))⁻¹ * 576) * (2 * Work.Kernels.psi2 ℓ τ
          + Work.Kernels.psi4 ℓ τ
          - 6 * ((Real.pi : ℂ) * Complex.I * (τ : ℂ) + Work.Asymptotics.Compact.cuspC ℓ)
          + (192 * ((Real.pi : ℂ) * Complex.I * (τ : ℂ) + Work.Asymptotics.Compact.cuspC ℓ) - 72)
              * Work.Kernels.qParamFun τ)) (Term ℓ τ)
    have h123 := norm_add_le ((((3456 : ℂ) * (Real.pi : ℂ))⁻¹ * 576) * (2 * Work.Kernels.psi2 ℓ τ
          + Work.Kernels.psi4 ℓ τ
          - 6 * ((Real.pi : ℂ) * Complex.I * (τ : ℂ) + Work.Asymptotics.Compact.cuspC ℓ)
          + (192 * ((Real.pi : ℂ) * Complex.I * (τ : ℂ) + Work.Asymptotics.Compact.cuspC ℓ) - 72)
              * Work.Kernels.qParamFun τ) + Term ℓ τ)
      (((3456 : ℂ) * (Real.pi : ℂ))⁻¹
        * (PsiCorr ℓ τ - 27648 * ((Real.pi : ℂ) * Complex.I * (τ : ℂ)
            + Work.Asymptotics.Compact.cuspC ℓ) * Work.Kernels.qParamFun τ))
    have hcomb : (3456 * Real.pi)⁻¹ * 576
          * (Ce * (Work.Kernels.scale τ) ^ (max Ne (max NT NP))
            * ‖Work.Kernels.qParamFun τ‖ ^ 2)
        + CT * (Work.Kernels.scale τ) ^ (max Ne (max NT NP)) * ‖Work.Kernels.qParamFun τ‖ ^ 2
        + (3456 * Real.pi)⁻¹ * (CP * (Work.Kernels.scale τ) ^ (max Ne (max NT NP))
              * ‖Work.Kernels.qParamFun τ‖ ^ 2)
        = (((3456 * Real.pi)⁻¹ * (576 * Ce + CP) + CT)
            * (Work.Kernels.scale τ) ^ (max Ne (max NT NP))
            * ‖Work.Kernels.qParamFun τ‖ ^ 2) := by ring
    have hsum : ‖(((3456 : ℂ) * (Real.pi : ℂ))⁻¹ * 576) * (2 * Work.Kernels.psi2 ℓ τ
            + Work.Kernels.psi4 ℓ τ
            - 6 * ((Real.pi : ℂ) * Complex.I * (τ : ℂ) + Work.Asymptotics.Compact.cuspC ℓ)
            + (192 * ((Real.pi : ℂ) * Complex.I * (τ : ℂ) + Work.Asymptotics.Compact.cuspC ℓ) - 72)
                * Work.Kernels.qParamFun τ)
          + Term ℓ τ
          + ((3456 : ℂ) * (Real.pi : ℂ))⁻¹
              * (PsiCorr ℓ τ - 27648 * ((Real.pi : ℂ) * Complex.I * (τ : ℂ)
                  + Work.Asymptotics.Compact.cuspC ℓ) * Work.Kernels.qParamFun τ)‖
        ≤ (3456 * Real.pi)⁻¹ * 576
            * (Ce * (Work.Kernels.scale τ) ^ (max Ne (max NT NP))
              * ‖Work.Kernels.qParamFun τ‖ ^ 2)
          + CT * (Work.Kernels.scale τ) ^ (max Ne (max NT NP)) * ‖Work.Kernels.qParamFun τ‖ ^ 2
          + (3456 * Real.pi)⁻¹
              * (CP * (Work.Kernels.scale τ) ^ (max Ne (max NT NP))
                * ‖Work.Kernels.qParamFun τ‖ ^ 2) := by
      calc ‖(((3456 : ℂ) * (Real.pi : ℂ))⁻¹ * 576) * (2 * Work.Kernels.psi2 ℓ τ
              + Work.Kernels.psi4 ℓ τ
              - 6 * ((Real.pi : ℂ) * Complex.I * (τ : ℂ) + Work.Asymptotics.Compact.cuspC ℓ)
              + (192 * ((Real.pi : ℂ) * Complex.I * (τ : ℂ) + Work.Asymptotics.Compact.cuspC ℓ) - 72)
                  * Work.Kernels.qParamFun τ)
            + Term ℓ τ
            + ((3456 : ℂ) * (Real.pi : ℂ))⁻¹
                * (PsiCorr ℓ τ - 27648 * ((Real.pi : ℂ) * Complex.I * (τ : ℂ)
                    + Work.Asymptotics.Compact.cuspC ℓ) * Work.Kernels.qParamFun τ)‖
          ≤ ‖(((3456 : ℂ) * (Real.pi : ℂ))⁻¹ * 576) * (2 * Work.Kernels.psi2 ℓ τ
              + Work.Kernels.psi4 ℓ τ
              - 6 * ((Real.pi : ℂ) * Complex.I * (τ : ℂ) + Work.Asymptotics.Compact.cuspC ℓ)
              + (192 * ((Real.pi : ℂ) * Complex.I * (τ : ℂ) + Work.Asymptotics.Compact.cuspC ℓ) - 72)
                  * Work.Kernels.qParamFun τ) + Term ℓ τ‖
            + ‖((3456 : ℂ) * (Real.pi : ℂ))⁻¹
                * (PsiCorr ℓ τ - 27648 * ((Real.pi : ℂ) * Complex.I * (τ : ℂ)
                    + Work.Asymptotics.Compact.cuspC ℓ) * Work.Kernels.qParamFun τ)‖ := h123
        _ ≤ (‖(((3456 : ℂ) * (Real.pi : ℂ))⁻¹ * 576) * (2 * Work.Kernels.psi2 ℓ τ
              + Work.Kernels.psi4 ℓ τ
              - 6 * ((Real.pi : ℂ) * Complex.I * (τ : ℂ) + Work.Asymptotics.Compact.cuspC ℓ)
              + (192 * ((Real.pi : ℂ) * Complex.I * (τ : ℂ) + Work.Asymptotics.Compact.cuspC ℓ) - 72)
                  * Work.Kernels.qParamFun τ)‖ + ‖Term ℓ τ‖)
            + ‖((3456 : ℂ) * (Real.pi : ℂ))⁻¹
                * (PsiCorr ℓ τ - 27648 * ((Real.pi : ℂ) * Complex.I * (τ : ℂ)
                    + Work.Asymptotics.Compact.cuspC ℓ) * Work.Kernels.qParamFun τ)‖ := by
            linarith [h12]
        _ ≤ _ := by linarith [h1, h2, h3]
    rw [hcomb] at hsum
    exact hsum
  have hstep : ‖B0 ℓ τ‖ ≤ (((3456 * Real.pi)⁻¹ * (576 * Ce + CP) + CT)
        * (Work.Kernels.scale τ) ^ (max Ne (max NT NP)) * ‖Work.Kernels.qParamFun τ‖ ^ 2)
      / (cd * Real.exp (-(2 * Real.pi * τ.im))) := by
    have hnorm : ‖B0 ℓ τ‖ = ‖Work.Kernels.DeltaFun τ * B0 ℓ τ‖
        / ‖Work.Kernels.DeltaFun τ‖ := by
      rw [norm_mul]; field_simp
    rw [hnorm]
    refine le_trans (div_le_div_of_nonneg_right hbig (norm_nonneg _)) ?_
    exact div_le_div_of_nonneg_left (by positivity) (mul_pos hcd hqpos) hlow
  have hqnorm : ‖Work.Kernels.qParamFun τ‖ = Real.exp (-(2 * Real.pi * τ.im)) :=
    Work.Asymptotics.norm_qParamFun τ
  have hfac : (((3456 * Real.pi)⁻¹ * (576 * Ce + CP) + CT)
        * (Work.Kernels.scale τ) ^ (max Ne (max NT NP)) * ‖Work.Kernels.qParamFun τ‖ ^ 2)
      / (cd * Real.exp (-(2 * Real.pi * τ.im)))
      = (((3456 * Real.pi)⁻¹ * (576 * Ce + CP) + CT) / cd)
        * (Work.Kernels.scale τ) ^ (max Ne (max NT NP)) * ‖Work.Kernels.qParamFun τ‖ := by
    rw [hqnorm]; field_simp
  rw [hfac] at hstep
  refine le_trans hstep ?_
  have hK0 : (0 : ℝ) ≤ ((3456 * Real.pi)⁻¹ * (576 * Ce + CP) + CT) / cd := by positivity
  have h1 : (((3456 * Real.pi)⁻¹ * (576 * Ce + CP) + CT) / cd)
      * (Work.Kernels.scale τ) ^ (max Ne (max NT NP))
      ≤ (((3456 * Real.pi)⁻¹ * (576 * Ce + CP) + CT) / cd + 1)
        * (Work.Kernels.scale τ) ^ (max Ne (max NT NP) + 1) :=
    calc (((3456 * Real.pi)⁻¹ * (576 * Ce + CP) + CT) / cd)
          * (Work.Kernels.scale τ) ^ (max Ne (max NT NP))
        ≤ (((3456 * Real.pi)⁻¹ * (576 * Ce + CP) + CT) / cd)
          * (Work.Kernels.scale τ) ^ (max Ne (max NT NP) + 1) :=
          mul_le_mul_of_nonneg_left hSle hK0
      _ ≤ (((3456 * Real.pi)⁻¹ * (576 * Ce + CP) + CT) / cd + 1)
          * (Work.Kernels.scale τ) ^ (max Ne (max NT NP) + 1) :=
          mul_le_mul_of_nonneg_right (by linarith [hK0])
            (Real.rpow_nonneg (by positivity) _)
  exact mul_le_mul_of_nonneg_right h1 hq

/-- **The sharp funnel remainder for `d = 8`**, in the `f`-form of `Kdev_leading_core`.

`f` is the `E(z)¹`-coefficient `KdevLead = E1combo8/(288π)`; the remainder `Kdev - KdevLead·Ept z`
is `KdevRem`, whose sharp funnel bound is `KdevRem_strip_sharp`. -/
theorem Kdev_leading_core_eight (ℓ : Work.Kernels.LogLambdaData) :
    ∃ (f : ℍ → ℂ) (C N M : ℝ), 0 < C ∧ 0 ≤ N ∧ 0 ≤ M ∧
      (∀ τ : ℍ, Work.Asymptotics.Funnel τ →
        ‖f τ‖ ≤ C * (Work.Kernels.scale τ) ^ N * ‖Work.Kernels.qParamFun τ‖) ∧
      ∀ (τ z : ℍ) (t : ℝ), Work.Asymptotics.Funnel τ → τ.im + 1 ≤ t →
        0 ≤ z.re → z.re ≤ 1 → z.im = t →
        ‖Work.Asymptotics.Kdev ℓ 8 τ z - f τ * Work.Residues.Ept z‖
          ≤ C * ‖Work.Kernels.qParamFun τ‖ * (Work.Kernels.scale τ) ^ N * (1 + t) ^ M
              * Real.exp (-(2 * Real.pi * t)) := by
  obtain ⟨C, N, M, hC, hN, hM, hb⟩ := Work.Asymptotics.KhatE1Core.Kdev8_rem_sharp ℓ
  obtain ⟨CL, NL, hCL, hNL, hL⟩ := E1combo8_over_const_bound ℓ
  refine ⟨KdevLead ℓ, max C CL + 1, max N NL, M, by positivity, by positivity, hM, ?_, ?_⟩
  · intro τ hτ
    have hscale1 : (1 : ℝ) ≤ Work.Kernels.scale τ := Work.Kernels.one_le_scale τ
    have hscale0 : (0 : ℝ) < Work.Kernels.scale τ := Work.Kernels.scale_pos τ
    have hq0 : (0 : ℝ) ≤ ‖Work.Kernels.qParamFun τ‖ := norm_nonneg _
    have hsN : (Work.Kernels.scale τ) ^ NL ≤ (Work.Kernels.scale τ) ^ (max N NL) :=
      Real.rpow_le_rpow_of_exponent_le hscale1 (le_max_right N NL)
    have h1 : CL * (Work.Kernels.scale τ) ^ NL
        ≤ (max C CL + 1) * (Work.Kernels.scale τ) ^ (max N NL) :=
      mul_le_mul (by linarith [le_max_right C CL]) hsN
        (Real.rpow_nonneg hscale0.le NL) (by positivity)
    calc ‖KdevLead ℓ τ‖
        ≤ CL * (Work.Kernels.scale τ) ^ NL * ‖Work.Kernels.qParamFun τ‖ := hL τ hτ
      _ ≤ (max C CL + 1) * (Work.Kernels.scale τ) ^ (max N NL)
            * ‖Work.Kernels.qParamFun τ‖ := mul_le_mul_of_nonneg_right h1 hq0
  · intro τ z t hτ ht hz0 hz1 hzt
    have h := hb τ z t hτ ht hz0 hz1 hzt
    rw [show Work.Asymptotics.KhatE1.KdevRem ℓ τ z
        = Work.Asymptotics.Kdev ℓ 8 τ z - KdevLead ℓ τ * Work.Residues.Ept z from rfl] at h
    refine le_trans h ?_
    have hscale1 : (1 : ℝ) ≤ Work.Kernels.scale τ := Work.Kernels.one_le_scale τ
    have hscale0 : (0 : ℝ) < Work.Kernels.scale τ := Work.Kernels.scale_pos τ
    have hq0 : (0 : ℝ) ≤ ‖Work.Kernels.qParamFun τ‖ := norm_nonneg _
    have ht0 : (0 : ℝ) ≤ 1 + t := by have := hτ.2; linarith
    have hsN : (Work.Kernels.scale τ) ^ N ≤ (Work.Kernels.scale τ) ^ (max N NL) :=
      Real.rpow_le_rpow_of_exponent_le hscale1 (le_max_left N NL)
    have hstep : C * (Work.Kernels.scale τ) ^ N
        ≤ (max C CL + 1) * (Work.Kernels.scale τ) ^ (max N NL) :=
      mul_le_mul (by linarith [le_max_left C CL]) hsN
        (Real.rpow_nonneg hscale0.le N) (by positivity)
    have h1 : C * (Work.Kernels.scale τ) ^ N * (1 + t) ^ M * Real.exp (-(2 * Real.pi * t))
        ≤ (max C CL + 1) * (Work.Kernels.scale τ) ^ (max N NL) * (1 + t) ^ M
            * Real.exp (-(2 * Real.pi * t)) := by
      calc C * (Work.Kernels.scale τ) ^ N * (1 + t) ^ M * Real.exp (-(2 * Real.pi * t))
          = (C * (Work.Kernels.scale τ) ^ N)
              * ((1 + t) ^ M * Real.exp (-(2 * Real.pi * t))) := by ring
        _ ≤ ((max C CL + 1) * (Work.Kernels.scale τ) ^ (max N NL))
              * ((1 + t) ^ M * Real.exp (-(2 * Real.pi * t))) :=
            mul_le_mul_of_nonneg_right hstep (by positivity)
        _ = (max C CL + 1) * (Work.Kernels.scale τ) ^ (max N NL) * (1 + t) ^ M
              * Real.exp (-(2 * Real.pi * t)) := by ring
    calc C * ‖Work.Kernels.qParamFun τ‖ * (Work.Kernels.scale τ) ^ N * (1 + t) ^ M
          * Real.exp (-(2 * Real.pi * t))
        = ‖Work.Kernels.qParamFun τ‖
            * (C * (Work.Kernels.scale τ) ^ N * (1 + t) ^ M
              * Real.exp (-(2 * Real.pi * t))) := by ring
      _ ≤ ‖Work.Kernels.qParamFun τ‖
            * ((max C CL + 1) * (Work.Kernels.scale τ) ^ (max N NL) * (1 + t) ^ M
              * Real.exp (-(2 * Real.pi * t))) := mul_le_mul_of_nonneg_left h1 hq0
      _ = (max C CL + 1) * ‖Work.Kernels.qParamFun τ‖ * (Work.Kernels.scale τ) ^ (max N NL)
            * (1 + t) ^ M * Real.exp (-(2 * Real.pi * t)) := by ring

/-- **The sharp funnel remainder for `d = 24`** (the remaining ingredient; the `E(z)¹`-coefficient
is `KdevLead24 = (E1combo24 + Am24)/(6912π)`, and the statement is `KhatE1.Kdev24LeadProp`). -/
theorem Kdev_leading_core_twentyfour (ℓ : Work.Kernels.LogLambdaData) :
    ∃ (f : ℍ → ℂ) (C N M : ℝ), 0 < C ∧ 0 ≤ N ∧ 0 ≤ M ∧
      (∀ τ : ℍ, Work.Asymptotics.Funnel τ →
        ‖f τ‖ ≤ C * (Work.Kernels.scale τ) ^ N * ‖Work.Kernels.qParamFun τ‖) ∧
      ∀ (τ z : ℍ) (t : ℝ), Work.Asymptotics.Funnel τ → τ.im + 1 ≤ t →
        0 ≤ z.re → z.re ≤ 1 → z.im = t →
        ‖Work.Asymptotics.Kdev ℓ 24 τ z - f τ * Work.Residues.Ept z‖
          ≤ C * ‖Work.Kernels.qParamFun τ‖ * (Work.Kernels.scale τ) ^ N * (1 + t) ^ M
              * Real.exp (-(2 * Real.pi * t)) := by
  obtain ⟨C, N, M, hC, hN, hM, hb⟩ :=
    (show ∃ C N M : ℝ, 0 < C ∧ 0 ≤ N ∧ 0 ≤ M ∧ _ from Kdev24LeadProp_proof ℓ)
  obtain ⟨CL, NL, hCL, hNL, hL⟩ := KdevLead24_bound ℓ
  refine ⟨KdevLead24 ℓ, max C CL + 1, max N NL, M, by positivity, by positivity, hM, ?_, ?_⟩
  · intro τ hτ
    have hscale1 : (1 : ℝ) ≤ Work.Kernels.scale τ := Work.Kernels.one_le_scale τ
    have hscale0 : (0 : ℝ) < Work.Kernels.scale τ := Work.Kernels.scale_pos τ
    have hq0 : (0 : ℝ) ≤ ‖Work.Kernels.qParamFun τ‖ := norm_nonneg _
    have hsN : (Work.Kernels.scale τ) ^ NL ≤ (Work.Kernels.scale τ) ^ (max N NL) :=
      Real.rpow_le_rpow_of_exponent_le hscale1 (le_max_right N NL)
    have h1 : CL * (Work.Kernels.scale τ) ^ NL
        ≤ (max C CL + 1) * (Work.Kernels.scale τ) ^ (max N NL) :=
      mul_le_mul (by linarith [le_max_right C CL]) hsN
        (Real.rpow_nonneg hscale0.le NL) (by positivity)
    calc ‖KdevLead24 ℓ τ‖
        ≤ CL * ‖Work.Kernels.qParamFun τ‖ * (Work.Kernels.scale τ) ^ NL := hL τ hτ
      _ = (CL * (Work.Kernels.scale τ) ^ NL) * ‖Work.Kernels.qParamFun τ‖ := by ring
      _ ≤ ((max C CL + 1) * (Work.Kernels.scale τ) ^ (max N NL))
            * ‖Work.Kernels.qParamFun τ‖ := mul_le_mul_of_nonneg_right h1 hq0
      _ = (max C CL + 1) * (Work.Kernels.scale τ) ^ (max N NL)
            * ‖Work.Kernels.qParamFun τ‖ := by ring
  · intro τ z t hτ ht hz0 hz1 hzt
    have h := hb τ z t hτ ht hz0 hz1 hzt
    refine le_trans h ?_
    have hscale1 : (1 : ℝ) ≤ Work.Kernels.scale τ := Work.Kernels.one_le_scale τ
    have hscale0 : (0 : ℝ) < Work.Kernels.scale τ := Work.Kernels.scale_pos τ
    have hq0 : (0 : ℝ) ≤ ‖Work.Kernels.qParamFun τ‖ := norm_nonneg _
    have ht0 : (0 : ℝ) ≤ 1 + t := by have := hτ.2; linarith
    have hsN : (Work.Kernels.scale τ) ^ N ≤ (Work.Kernels.scale τ) ^ (max N NL) :=
      Real.rpow_le_rpow_of_exponent_le hscale1 (le_max_left N NL)
    have hstep : C * (Work.Kernels.scale τ) ^ N
        ≤ (max C CL + 1) * (Work.Kernels.scale τ) ^ (max N NL) :=
      mul_le_mul (by linarith [le_max_left C CL]) hsN
        (Real.rpow_nonneg hscale0.le N) (by positivity)
    have h1 : C * (Work.Kernels.scale τ) ^ N * (1 + t) ^ M * Real.exp (-(2 * Real.pi * t))
        ≤ (max C CL + 1) * (Work.Kernels.scale τ) ^ (max N NL) * (1 + t) ^ M
            * Real.exp (-(2 * Real.pi * t)) := by
      calc C * (Work.Kernels.scale τ) ^ N * (1 + t) ^ M * Real.exp (-(2 * Real.pi * t))
          = (C * (Work.Kernels.scale τ) ^ N)
              * ((1 + t) ^ M * Real.exp (-(2 * Real.pi * t))) := by ring
        _ ≤ ((max C CL + 1) * (Work.Kernels.scale τ) ^ (max N NL))
              * ((1 + t) ^ M * Real.exp (-(2 * Real.pi * t))) :=
            mul_le_mul_of_nonneg_right hstep (by positivity)
        _ = (max C CL + 1) * (Work.Kernels.scale τ) ^ (max N NL) * (1 + t) ^ M
              * Real.exp (-(2 * Real.pi * t)) := by ring
    calc C * ‖Work.Kernels.qParamFun τ‖ * (Work.Kernels.scale τ) ^ N * (1 + t) ^ M
          * Real.exp (-(2 * Real.pi * t))
        = ‖Work.Kernels.qParamFun τ‖
            * (C * (Work.Kernels.scale τ) ^ N * (1 + t) ^ M
              * Real.exp (-(2 * Real.pi * t))) := by ring
      _ ≤ ‖Work.Kernels.qParamFun τ‖
            * ((max C CL + 1) * (Work.Kernels.scale τ) ^ (max N NL) * (1 + t) ^ M
              * Real.exp (-(2 * Real.pi * t))) := mul_le_mul_of_nonneg_left h1 hq0
      _ = (max C CL + 1) * ‖Work.Kernels.qParamFun τ‖ * (Work.Kernels.scale τ) ^ (max N NL)
            * (1 + t) ^ M * Real.exp (-(2 * Real.pi * t)) := by ring

/-- **The sharp leading coefficient of the funnel deviation (the remaining core).**

For `d = 8` one may take `f τ = E1combo8 ℓ τ / (288 π)`; `E1combo8_bound` then supplies the
bound `‖f τ‖ ≤ C (scale τ)^N ‖q(τ)‖`, and the statement is `KhatE1.Kdev_strip_sharp8_core`.
For `d = 24` the leading coefficient is only required to satisfy the same bound
(`E1combo24_bound` supplies it for `f τ = E1combo24 ℓ τ / (6912 π)`). -/
theorem Kdev_leading_core (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24) :
    ∃ (f : ℍ → ℂ) (C N M : ℝ), 0 < C ∧ 0 ≤ N ∧ 0 ≤ M ∧
      (∀ τ : ℍ, Work.Asymptotics.Funnel τ →
        ‖f τ‖ ≤ C * (Work.Kernels.scale τ) ^ N * ‖Work.Kernels.qParamFun τ‖) ∧
      ∀ (τ z : ℍ) (t : ℝ), Work.Asymptotics.Funnel τ → τ.im + 1 ≤ t →
        0 ≤ z.re → z.re ≤ 1 → z.im = t →
        ‖Work.Asymptotics.Kdev ℓ d τ z - f τ * Work.Residues.Ept z‖
          ≤ C * ‖Work.Kernels.qParamFun τ‖ * (Work.Kernels.scale τ) ^ N * (1 + t) ^ M
              * Real.exp (-(2 * Real.pi * t)) := by
  rcases hd with rfl | rfl
  · exact Kdev_leading_core_eight ℓ
  · exact Kdev_leading_core_twentyfour ℓ

/-- **The sharp strip bound for the deviation on the funnel**, from the core. -/
theorem Kdev_funnel_strip_sharp_of_leading_core (ℓ : Work.Kernels.LogLambdaData) (d : ℕ)
    (hd : d = 8 ∨ d = 24) :
    ∃ C N M : ℝ, 0 < C ∧ 0 ≤ N ∧ 0 ≤ M ∧
      ∀ (τ z : ℍ) (t : ℝ), Work.Asymptotics.Funnel τ → τ.im + 1 ≤ t →
        0 ≤ z.re → z.re ≤ 1 → z.im = t →
        ‖Work.Asymptotics.Kdev ℓ d τ z‖
          ≤ C * ‖Work.Kernels.qParamFun τ‖ * (Work.Kernels.scale τ) ^ N * (1 + t) ^ M
              * Real.exp (-(Real.pi * t)) :=
  funnel_strip_sharp_of_leading_core ℓ d hd (Kdev_leading_core ℓ d hd)

theorem Kdev_cusp0_strip_sharp (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24) :
    ∃ C N M : ℝ, 0 < C ∧ 0 ≤ N ∧ 0 ≤ M ∧
      ∀ (w z : UpperHalfPlane) (t : ℝ), w ∈ Work.Asymptotics.KEpsilon →
        (ModularGroup.S • w).im + 1 ≤ t → 0 ≤ z.re → z.re ≤ 1 → z.im = t →
        ‖Work.Kernels.Kfun ℓ d w z
            - (Work.Asymptotics.Compact.Gplus d w z
                + Work.Asymptotics.Compact.Gminus d ℓ w z) / 2‖
          ≤ C * ‖Work.Kernels.qParamFun (ModularGroup.S • w)‖ * (Work.Kernels.scale w) ^ N
              * (1 + t) ^ M * Real.exp (-(Real.pi * t)) := by
  exact cusp0_strip_of_funnel ℓ d hd (Kdev_funnel_strip_sharp_of_leading_core ℓ d hd)

end Work.Asymptotics.KhatE1
