import Mathlib
import Submission.Work.BourgainPlan.Maximal.mstFreezeDefs
import Submission.Work.BourgainPlan.Maximal.mstProf_scale_decay

namespace Work.BourgainPlan.Maximal

open Work.BourgainPlan.IonescuWainger

local notation "Circ" => Work.BourgainPlan.IonescuWainger.Circle

/-- **The Lipschitz bound on the freezing factor.**  For the level shift `u`,
`star (fourier u ζ) = e(−iwRep ζ · u)`, so
`‖star (fourier u ζ) − 1‖ ≤ 2π·u·|iwRep ζ| = 2π·u·‖ζ‖`. -/
private lemma norm_star_fourier_sub_one_le (u : ℕ) (ζ : Circ) :
    ‖star (fourier (u : ℤ) ζ) - 1‖ ≤ 2 * Real.pi * (u : ℝ) * ‖ζ‖ := by
  have hu0 : (0 : ℝ) ≤ (u : ℝ) := Nat.cast_nonneg u
  set F : ℝ := -(2 * Real.pi * (iwRep ζ * (u : ℝ))) with hF
  have hgoal : star (fourier (u : ℤ) ζ) - 1 = Complex.exp (Complex.I * (F : ℂ)) - 1 := by
    rw [star_fourier_eq_exp, hF]
    congr 1
    push_cast
    ring_nf
  rw [hgoal]
  have h := Real.norm_exp_I_mul_ofReal_sub_one_le (x := F)
  refine le_trans h ?_
  have hFabs : |F| = 2 * Real.pi * (u : ℝ) * |iwRep ζ| := by
    rw [hF, abs_neg, abs_mul, abs_of_nonneg (a := 2 * Real.pi) (by positivity),
      abs_mul, abs_of_nonneg (a := (u : ℝ)) hu0]
    ring
  rw [Real.norm_eq_abs, hFabs, norm_eq_abs_iwRep]

/-- **The sup-norm bound on the symbol of the freezing difference** (MST §4.3): for `d = P.natDegree ≥ 2`, any bound `M` on the level bumps, all levels `s, n, u` and all arcs `β`, `‖(star (fourier u (ξ-β)) - 1) · Φ_{2^n}(ξ-β) ψ_s(ξ-β)‖ ≤ C·M·u·2^{−n/d}` uniformly in `ξ` (and in `s ≥ 0`).
Route: `star (fourier u (ξ-β)) = exp(−2πi·(iwRep (ξ-β)·u))` (`star_fourier_eq_exp`, `Work.BourgainPlan.Maximal.mstKernel_helpers`) so `‖star (fourier u (ξ-β)) - 1‖ ≤ 2π·u·|iwRep (ξ-β)| = 2π·u·‖ξ-β‖` (`Real.norm_exp_I_mul_ofReal_sub_one_le`, `norm_eq_abs_iwRep`); then `2π·u·(‖ξ-β‖·‖mstProf P (2^n) (ξ-β)‖)·M ≤ 2π·u·C₀·2^{−n/d}·M` using `mstProf_scale_decay` at `d = P.natDegree` (its hypothesis `1 ≤ n` fails only for `n = 0`, where the claim is trivial since `‖mstProf P 1 ζ‖ ≤ 1` and `2^{−0/d} = 1`), and `‖mstEta P.natDegree χ η s (ξ-β)‖ ≤ M`. -/
theorem mstFreezeSym_bound (P : Polynomial ℤ) (hd : 2 ≤ P.natDegree) (χ : ℝ) (η : ℝ → ℂ)
    (hηc : ContDiff ℝ 2 η) (hηsup : ∀ x : ℝ, 1 / 2 ≤ |x| → η x = 0) :
    ∃ C : ℝ, 0 < C ∧ ∀ (M : ℝ), 0 ≤ M →
      (∀ (s : ℕ) (ζ : Work.BourgainPlan.IonescuWainger.Circle),
        ‖Work.BourgainPlan.Maximal.mstEta P.natDegree χ η s ζ‖ ≤ M) →
      ∀ (s n u : ℕ) (β ξ : Work.BourgainPlan.IonescuWainger.Circle),
        ‖Work.BourgainPlan.Maximal.mstFreezeSymFun P P.natDegree χ η s n u β ξ‖
          ≤ C * M * (u : ℝ) * (2 : ℝ) ^ (-(n : ℝ) / (P.natDegree : ℝ)) := by
  obtain ⟨C₀, hC₀pos, hC₀⟩ := mstProf_scale_decay P hd
  refine ⟨max (2 * Real.pi * C₀) Real.pi, ?_, ?_⟩
  · exact lt_of_lt_of_le Real.pi_pos (le_max_right _ _)
  · intro M hM0 hM s n u β ξ
    have hpi0 : (0 : ℝ) ≤ Real.pi := Real.pi_pos.le
    have hu0 : (0 : ℝ) ≤ (u : ℝ) := Nat.cast_nonneg u
    have hstar := norm_star_fourier_sub_one_le u (ξ - β)
    have heta := hM s (ξ - β)
    have hprof : ‖mstProf P (2 ^ n) (ξ - β)‖ ≤ 1 := by
      rw [mstProf_apply]
      exact norm_polyProfile_le_one P (2 ^ n) (iwRep (ξ - β))
    have hprof0 : (0 : ℝ) ≤ ‖mstProf P (2 ^ n) (ξ - β)‖ := norm_nonneg _
    have hLHS : ‖mstFreezeSymFun P P.natDegree χ η s n u β ξ‖
        = ‖star (fourier (u : ℤ) (ξ - β)) - 1‖
          * (‖mstProf P (2 ^ n) (ξ - β)‖ * ‖mstEta P.natDegree χ η s (ξ - β)‖) := by
      rw [mstFreezeSymFun_apply, mstProfBumpFun_apply, norm_mul, norm_mul]
    rw [hLHS]
    have hstep1 :
        ‖star (fourier (u : ℤ) (ξ - β)) - 1‖
            * (‖mstProf P (2 ^ n) (ξ - β)‖ * ‖mstEta P.natDegree χ η s (ξ - β)‖)
          ≤ (2 * Real.pi * (u : ℝ) * ‖ξ - β‖)
            * (‖mstProf P (2 ^ n) (ξ - β)‖ * M) :=
      mul_le_mul hstar (mul_le_mul_of_nonneg_left heta hprof0)
        (mul_nonneg hprof0 (norm_nonneg _))
        (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hpi0) hu0) (norm_nonneg _))
    set X : ℝ := (2 : ℝ) ^ (-(n : ℝ) / (P.natDegree : ℝ)) with hXdef
    have hX0 : (0 : ℝ) ≤ X := by
      rw [hXdef]
      exact Real.rpow_nonneg (by norm_num) _
    rcases Nat.eq_zero_or_pos n with hn | hn
    · -- the level `n = 0`: only the trivial bound `‖Φ_1‖ ≤ 1` is available
      subst hn
      have hzeta : ‖ξ - β‖ ≤ 1 / 2 := by
        rw [norm_eq_abs_iwRep (ξ - β)]
        exact abs_iwRep_le _
      have hX1 : X = 1 := by
        rw [hXdef]
        simp
      rw [hX1, mul_one]
      have hmul :
          (2 * Real.pi * (u : ℝ) * ‖ξ - β‖) * (‖mstProf P (2 ^ 0) (ξ - β)‖ * M)
            ≤ (2 * Real.pi * (u : ℝ) * (1 / 2)) * (1 * M) :=
        mul_le_mul
          (mul_le_mul_of_nonneg_left hzeta
            (mul_nonneg (mul_nonneg (by norm_num) hpi0) hu0))
          (mul_le_mul_of_nonneg_right hprof hM0)
          (mul_nonneg hprof0 hM0)
          (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hpi0) hu0) (by norm_num))
      refine le_trans hstep1 (le_trans hmul ?_)
      have hrew : (2 * Real.pi * (u : ℝ) * (1 / 2)) * (1 * M) = Real.pi * M * (u : ℝ) := by
        ring
      rw [hrew]
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_max_right (2 * Real.pi * C₀) Real.pi) hM0) hu0
    · -- the level `n ≥ 1`: the van der Corput decay `mstProf_scale_decay` applies
      have hn1 : 1 ≤ n := hn
      have hdec : ‖ξ - β‖ * ‖mstProf P (2 ^ n) (ξ - β)‖ ≤ C₀ * X := by
        rw [hXdef]
        exact hC₀ n hn1 (ξ - β)
      have hfac0 : (0 : ℝ) ≤ 2 * Real.pi * (u : ℝ) * M :=
        mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hpi0) hu0) hM0
      have hmid :
          (2 * Real.pi * (u : ℝ) * ‖ξ - β‖) * (‖mstProf P (2 ^ n) (ξ - β)‖ * M)
            ≤ 2 * Real.pi * (u : ℝ) * M * (C₀ * X) := by
        rw [show (2 * Real.pi * (u : ℝ) * ‖ξ - β‖) * (‖mstProf P (2 ^ n) (ξ - β)‖ * M)
            = 2 * Real.pi * (u : ℝ) * M * (‖ξ - β‖ * ‖mstProf P (2 ^ n) (ξ - β)‖)
            from by ring]
        exact mul_le_mul_of_nonneg_left hdec hfac0
      refine le_trans hstep1 (le_trans hmid ?_)
      have hC0le : 2 * Real.pi * C₀ ≤ max (2 * Real.pi * C₀) Real.pi :=
        le_max_left _ _
      calc 2 * Real.pi * (u : ℝ) * M * (C₀ * X)
          = 2 * Real.pi * C₀ * M * (u : ℝ) * X := by ring
        _ ≤ max (2 * Real.pi * C₀) Real.pi * M * (u : ℝ) * X :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_right hC0le hM0) hu0) hX0

end Work.BourgainPlan.Maximal
