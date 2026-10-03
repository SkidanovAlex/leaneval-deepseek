import Mathlib
import Submission.Work.KMTAreas.A7.ModelOps
import Submission.Work.KMTAreas.A7.Tle_varphitildeNt_bounded

namespace Work.KMTAreas.A7

noncomputable section

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal BigOperators FourierTransform
open Work.Analysis.IonescuWainger Work.Analysis.IWMultiplier

/-- **Quadratic decay, uniform in `t`, of the exact-height IW kernel of the modulated bump
`φ̃_{N,t}`.**

For the modulated second bump `varphitildeNt P P.natDegree N k t` of the §6/§7 model operator,
the kernel of its exact-height Ionescu--Wainger multiplier (`diffFreqs ρ l` frequency set) decays
like `j^{-2}`, with a constant *independent of* `t ∈ [1/2,1]`.

The proof is the same reduction as in `Work.KMTAreas.A7.Tle_varphitildeNt_bounded` (whose
`iwKernel_varphitildeNt_eq` factors the kernel as
`arithChar ρ l (-j) · 𝓕 φ̃_N (j - c_t)`, `c_t = PevalR P (N t)`, and whose §4 shows the shift costs
only a constant factor): `|(∑_{α ∈ (ℚ/ℤ)_{≤l}} e(-jα))| ≤ #(ℚ/ℤ)_{≤l}` and
`‖𝓕 φ̃_N‖ ≤ Cf/(1+|·|)²` (`Work.KMTAreas.A7.fourierDecay_varphitildeN`), `|c_t| ≤ M` uniformly in
`t ∈ [1/2,1]` (`Work.KMTAreas.A7.abs_PevalR_mul_le`), and `one_div_sq_le_of_abs_sub_le` converts
`1/(1+|j - c_t|)²` into `(2M+1)²/(1+|j|)²`.  Note `IwKernelArithChar` is stated for an arbitrary
finite frequency set, so the factorisation applies to `diffFreqs ρ l` verbatim (only
`(diffFreqs ρ l).card ≤ (iwArithFreqs ρ l).card` is used).  Alternatively, apply the general
`Work.KMTAreas.A7.iwKernel_decay_of_bump` to `F = varphitildeNt P P.natDegree N k t` after
proving the two `L¹` bounds `∫‖F‖ ≤ S`, `∫‖F''‖ ≤ S` with `S` independent of `t` (the second
derivative costs a factor `|c_t| ≤ M`, bounded uniformly).

Used in the target file to supply the `ℓ¹` (indeed `j^{-2}`) kernel bounds of the Fubini step
`Work.KMTAreas.A7.integral_bilinOp_convOp_comm`. -/
theorem tmKernel_varphitildeNt_decay (P : Polynomial ℤ) (ρ : ℝ) (l N k : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ t ∈ Set.Icc (1/2 : ℝ) 1, ∀ j : ℤ,
      ‖Work.Analysis.IWMultiplier.iwKernel (Work.Analysis.IonescuWainger.iwSymbolSet
          (Work.KMTAreas.A7.diffFreqs ρ l)
          (Work.Analysis.IonescuWainger.periodize
            (Work.KMTAreas.A7.varphitildeNt P P.natDegree N k t))) j‖
        ≤ C / (1 + |(j : ℝ)|)^2 := by
  classical
  obtain ⟨Cf, hCfpos, hCfdec⟩ := fourierDecay_varphitildeN P.natDegree N k
  set Mv : ℝ := max 1 ((∑ i ∈ Finset.range (P.natDegree + 1), |(P.coeff i : ℝ)|) *
    (1 + (N : ℝ)) ^ P.natDegree) with hMv
  set K : ℝ := (2 * Mv + 1) ^ 2 with hK
  have hMnonneg : 0 ≤ Mv := le_trans zero_le_one (le_max_left 1 _)
  set A : ℝ := ((diffFreqs ρ l).card : ℝ) * Cf * K with hA
  refine ⟨max 1 A, lt_max_of_lt_left zero_lt_one, ?_⟩
  intro t ht j
  have ht1 : |t| ≤ 1 := by
    obtain ⟨h1, h2⟩ := ht
    rw [abs_le]
    exact ⟨by linarith, h2⟩
  have hc : |PevalR P ((N : ℝ) * t)| ≤ Mv :=
    le_trans (abs_PevalR_mul_le P N ht1) (le_max_right 1 _)
  rw [Work.KMTPlan.A6.IwKernelArithChar (diffFreqs ρ l)
      (integrable_varphitildeNt_aux P P.natDegree N k t) j,
    cw_eq_fourierTransform,
    fourier_varphitildeNt_eq P P.natDegree N k t (j : ℝ)]
  have h1 : ‖∑ α ∈ diffFreqs ρ l, fourier (T := 1) (-j) α‖ ≤ ((diffFreqs ρ l).card : ℝ) := by
    calc ‖∑ α ∈ diffFreqs ρ l, fourier (T := 1) (-j) α‖
        ≤ ∑ α ∈ diffFreqs ρ l, ‖fourier (T := 1) (-j) α‖ := norm_sum_le _ _
      _ = ∑ _α ∈ diffFreqs ρ l, (1 : ℝ) := by
          refine Finset.sum_congr rfl (fun α _ => ?_)
          rw [fourier_apply]
          exact _root_.Circle.norm_coe _
      _ = ((diffFreqs ρ l).card : ℝ) := by simp
  have h2 : ‖FourierTransform.fourier (varphitildeN P.natDegree N k)
        ((j : ℝ) - PevalR P ((N : ℝ) * t))‖
      ≤ Cf * K / (1 + |(j : ℝ)|) ^ 2 := by
    refine le_trans (hCfdec ((j : ℝ) - PevalR P ((N : ℝ) * t))) ?_
    have hmaj := one_div_sq_le_of_abs_sub_le hMnonneg hc j
    calc Cf / (1 + |(j : ℝ) - PevalR P ((N : ℝ) * t)|) ^ 2
        = Cf * (1 / (1 + |(j : ℝ) - PevalR P ((N : ℝ) * t)|) ^ 2) := div_eq_mul_one_div _ _
      _ ≤ Cf * (K / (1 + |(j : ℝ)|) ^ 2) := by
          refine mul_le_mul_of_nonneg_left ?_ hCfpos.le
          rw [hK]
          exact hmaj
      _ = Cf * K / (1 + |(j : ℝ)|) ^ 2 := (mul_div_assoc _ _ _).symm
  calc ‖(∑ α ∈ diffFreqs ρ l, fourier (T := 1) (-j) α) *
          FourierTransform.fourier (varphitildeN P.natDegree N k)
            ((j : ℝ) - PevalR P ((N : ℝ) * t))‖
      = ‖∑ α ∈ diffFreqs ρ l, fourier (T := 1) (-j) α‖ *
          ‖FourierTransform.fourier (varphitildeN P.natDegree N k)
            ((j : ℝ) - PevalR P ((N : ℝ) * t))‖ := norm_mul _ _
    _ ≤ ((diffFreqs ρ l).card : ℝ) * (Cf * K / (1 + |(j : ℝ)|) ^ 2) :=
        mul_le_mul h1 h2 (norm_nonneg _) (Nat.cast_nonneg _)
    _ = A / (1 + |(j : ℝ)|) ^ 2 := by rw [hA]; ring
    _ ≤ max 1 A / (1 + |(j : ℝ)|) ^ 2 :=
        div_le_div_of_nonneg_right (le_max_right 1 A) (by positivity)


end

end Work.KMTAreas.A7
