/-
# The sharp `ℓ¹(ℤ)` mass of the unit difference of the §6 bumps

For the bumps `φ_N = varphiN N k₁` and `φ̃_N = varphitildeN P.natDegree N k₂` this module proves

  `∑_p ‖φ̂_N(u+1−p) − φ̂_N(u−p)‖ ≲ 2^{k₁}/N`,   `∑_p ‖φ̃̂_N(u+1−p) − φ̃̂_N(u−p)‖ ≲ 2^{dk₂}/N^d`,

i.e. the lattice mass of the *unit difference* of the bump's inverse Fourier transform is (like the
`θ`-weighted mass of `sharpBumpMassSum`) one order of the bump's width `a = 2^{k}/N` smaller than the
mass itself.

**The mechanism.**  `bumpFT φ` is the inverse Fourier transform of `φ`, whose derivative is
`2πi · bumpFT (θ ↦ θ φ θ)` (`hasDerivAt_bumpFT`), so by the fundamental theorem of calculus

  `bumpFT φ (v+1) − bumpFT φ v = 2πi ∫_0^1 bumpFT (θ ↦ θ φ θ) (v+s) ds`.

For a *finite* set of lattice points the sum of the norms of these integrals is bounded by
`2π` times the integral of the pointwise lattice mass of `bumpFT (θφ)`, which is `≲ a` uniformly in
the base point by the sharp `θ`-weighted mass sum `sharpBumpMassSum`; `Real.tsum_le_of_sum_le`
turns the finite bounds into the bound for the `tsum`.
-/
import Mathlib
import Submission.Work.KMTAreas.A7.sharpBumpMassSum
import Submission.Work.KMTAreas.A7.bumpFT_deriv
import Submission.Work.KMTAreas.A7.varphiNt_bounds
import Submission.Work.KMTAreas.A7.fourierDecay_varphitildeN

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace Work.KMTAreas.A7

noncomputable section

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal BigOperators
open Work.KMTPlan.A6

/-! ## The norm of the constant `2πi` -/

/-- The norm of a real number seen in `ℂ` is its absolute value. -/
private lemma norm_ofReal_abs_kmt (r : ℝ) : ‖((r : ℝ) : ℂ)‖ = |r| := by
  have h1 : ‖((r : ℝ) : ℂ)‖ ^ 2 = r ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_ofReal, sq]
  rw [← Real.sqrt_sq (norm_nonneg _), h1, Real.sqrt_sq_eq_abs]

/-- The norm of the constant `2πi`. -/
private lemma norm_two_pi_I_kmt : ‖(2 * (Real.pi : ℂ) * Complex.I)‖ = 2 * Real.pi := by
  have hcast : (2 * (Real.pi : ℂ)) = (((2 * Real.pi : ℝ)) : ℂ) := by
    push_cast
    ring
  rw [hcast, norm_mul, Complex.norm_I, mul_one, norm_ofReal_abs_kmt,
    abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)]

/-! ## The unit difference of `bumpFT` as the integral of its derivative -/

/-- **The unit difference of `bumpFT` is the integral of its derivative.**  For `φ` of class `C²`
with compact support and every `v : ℝ`,

  `bumpFT φ (v+1) − bumpFT φ v = 2πi ∫_0^1 bumpFT (θ ↦ θ φ θ) (v+s) ds`. -/
lemma bumpFT_add_one_sub_eq_integral (φ : ℝ → ℂ) (hφ : ContDiff ℝ 2 φ)
    (hcs : HasCompactSupport φ) (v : ℝ) :
    bumpFT φ (v + 1) - bumpFT φ v
      = (2 * (Real.pi : ℂ) * Complex.I)
        * ∫ s in (0 : ℝ)..1, bumpFT (fun θ : ℝ => (θ : ℂ) * φ θ) (v + s) := by
  have hψcd : ContDiff ℝ 2 (fun θ : ℝ => (θ : ℂ) * φ θ) := bfm_contDiff_mul_id φ hφ
  have hψcs : HasCompactSupport (fun θ : ℝ => (θ : ℂ) * φ θ) :=
    bfm_hasCompactSupport_mul_id φ hcs
  have hψint : Integrable (fun θ : ℝ => (θ : ℂ) * φ θ) :=
    hψcd.continuous.integrable_of_hasCompactSupport hψcs
  have hcont : Continuous (fun s : ℝ =>
      (2 * (Real.pi : ℂ) * Complex.I) * bumpFT (fun θ : ℝ => (θ : ℂ) * φ θ) (v + s)) :=
    (continuous_const : Continuous fun _ : ℝ => (2 * (Real.pi : ℂ) * Complex.I)).mul
      ((continuous_bumpFT hψint).comp
        ((continuous_const : Continuous fun _ : ℝ => v).add continuous_id))
  have hderiv : ∀ x : ℝ, HasDerivAt (fun s : ℝ => bumpFT φ (v + s))
      ((2 * (Real.pi : ℂ) * Complex.I) * bumpFT (fun θ : ℝ => (θ : ℂ) * φ θ) (v + x)) x := by
    intro x
    have h1 : HasDerivAt (fun s : ℝ => v + s) 1 x := (hasDerivAt_id x).const_add v
    have h2 := HasDerivAt.scomp x (g₁ := bumpFT φ) (h := fun s : ℝ => v + s)
      (hasDerivAt_bumpFT φ hφ hcs (v + x)) h1
    simpa only [Function.comp_def, one_smul] using h2
  have hint : IntervalIntegrable (fun s : ℝ =>
      (2 * (Real.pi : ℂ) * Complex.I) * bumpFT (fun θ : ℝ => (θ : ℂ) * φ θ) (v + s))
      volume (0 : ℝ) 1 := hcont.intervalIntegrable 0 1
  have hmain := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun s : ℝ => bumpFT φ (v + s))
    (f' := fun x : ℝ => (2 * (Real.pi : ℂ) * Complex.I)
      * bumpFT (fun θ : ℝ => (θ : ℂ) * φ θ) (v + x))
    (a := 0) (b := 1) (fun x _ => hderiv x) hint
  rw [intervalIntegral.integral_const_mul] at hmain
  simpa using hmain.symm

/-! ## The lattice mass of the unit difference -/

/-- **The lattice mass of the unit difference of a bump.**  If the lattice mass of the
`θ`-weighted bump is `≤ C a` at every base point, then the lattice mass of the unit difference of
the bump is `≤ 2π C a`. -/
lemma tsum_bumpFT_diff_le (φ : ℝ → ℂ) (hφ : ContDiff ℝ 2 φ) (hcs : HasCompactSupport φ)
    {C a : ℝ}
    (hmass : ∀ w : ℝ,
      (∑' p : ℤ, ‖bumpFT (fun θ : ℝ => (θ : ℂ) * φ θ) (w - (p : ℝ))‖) ≤ C * a)
    (u : ℝ) :
    (∑' p : ℤ, ‖bumpFT φ (u + 1 - (p : ℝ)) - bumpFT φ (u - (p : ℝ))‖)
      ≤ (2 * Real.pi) * (C * a) := by
  have hψcd : ContDiff ℝ 2 (fun θ : ℝ => (θ : ℂ) * φ θ) := bfm_contDiff_mul_id φ hφ
  have hψcs : HasCompactSupport (fun θ : ℝ => (θ : ℂ) * φ θ) :=
    bfm_hasCompactSupport_mul_id φ hcs
  have hψint : Integrable (fun θ : ℝ => (θ : ℂ) * φ θ) :=
    hψcd.continuous.integrable_of_hasCompactSupport hψcs
  have hsumm : ∀ w : ℝ,
      Summable (fun p : ℤ => ‖bumpFT (fun θ : ℝ => (θ : ℂ) * φ θ) (w - (p : ℝ))‖) :=
    fun w => summable_bumpFT _ hψcd hψcs w
  have hid : ∀ p : ℤ,
      bumpFT φ (u + 1 - (p : ℝ)) - bumpFT φ (u - (p : ℝ))
        = (2 * (Real.pi : ℂ) * Complex.I)
          * ∫ s in (0 : ℝ)..1,
              bumpFT (fun θ : ℝ => (θ : ℂ) * φ θ) (u - (p : ℝ) + s) := by
    intro p
    have h := bumpFT_add_one_sub_eq_integral φ hφ hcs (u - (p : ℝ))
    rw [show u - (p : ℝ) + 1 = u + 1 - (p : ℝ) by ring] at h
    exact h
  have hcont_p : ∀ p : ℤ, Continuous (fun s : ℝ =>
      ‖bumpFT (fun θ : ℝ => (θ : ℂ) * φ θ) (u - (p : ℝ) + s)‖) := by
    intro p
    refine Continuous.norm ?_
    exact (continuous_bumpFT hψint).comp
      ((continuous_const : Continuous fun _ : ℝ => u - (p : ℝ)).add continuous_id)
  refine Real.tsum_le_of_sum_le
    (f := fun p : ℤ => ‖bumpFT φ (u + 1 - (p : ℝ)) - bumpFT φ (u - (p : ℝ))‖)
    (fun p => norm_nonneg _) ?_
  intro s0
  have hpt : ∀ s : ℝ, (∑ p ∈ s0,
      ‖bumpFT (fun θ : ℝ => (θ : ℂ) * φ θ) (u - (p : ℝ) + s)‖) ≤ C * a := by
    intro s
    have heq : (∑ p ∈ s0,
        ‖bumpFT (fun θ : ℝ => (θ : ℂ) * φ θ) (u - (p : ℝ) + s)‖)
        = ∑ p ∈ s0,
            ‖bumpFT (fun θ : ℝ => (θ : ℂ) * φ θ) ((u + s) - (p : ℝ))‖ := by
      refine Finset.sum_congr rfl (fun p _ => ?_)
      rw [show u - (p : ℝ) + s = (u + s) - (p : ℝ) by ring]
    rw [heq]
    exact (Summable.sum_le_tsum s0 (fun p _ => norm_nonneg _) (hsumm (u + s))).trans
      (hmass (u + s))
  have hcont_sum : Continuous (fun s : ℝ => ∑ p ∈ s0,
      ‖bumpFT (fun θ : ℝ => (θ : ℂ) * φ θ) (u - (p : ℝ) + s)‖) :=
    continuous_finsetSum s0 (fun p _ => hcont_p p)
  have hint1 : IntervalIntegrable (fun s : ℝ => ∑ p ∈ s0,
      ‖bumpFT (fun θ : ℝ => (θ : ℂ) * φ θ) (u - (p : ℝ) + s)‖) volume (0 : ℝ) 1 :=
    hcont_sum.intervalIntegrable 0 1
  have hint2 : IntervalIntegrable (fun _ : ℝ => C * a) volume (0 : ℝ) 1 :=
    intervalIntegrable_const
  calc ∑ p ∈ s0, ‖bumpFT φ (u + 1 - (p : ℝ)) - bumpFT φ (u - (p : ℝ))‖
      = ∑ p ∈ s0, ‖(2 * (Real.pi : ℂ) * Complex.I)
          * ∫ s in (0 : ℝ)..1,
              bumpFT (fun θ : ℝ => (θ : ℂ) * φ θ) (u - (p : ℝ) + s)‖ :=
        Finset.sum_congr rfl (fun p _ => by rw [hid p])
    _ = ∑ p ∈ s0, (2 * Real.pi)
          * ‖∫ s in (0 : ℝ)..1,
              bumpFT (fun θ : ℝ => (θ : ℂ) * φ θ) (u - (p : ℝ) + s)‖ := by
        refine Finset.sum_congr rfl (fun p _ => ?_)
        rw [norm_mul, norm_two_pi_I_kmt]
    _ ≤ ∑ p ∈ s0, (2 * Real.pi)
          * ∫ s in (0 : ℝ)..1,
              ‖bumpFT (fun θ : ℝ => (θ : ℂ) * φ θ) (u - (p : ℝ) + s)‖ := by
        refine Finset.sum_le_sum (fun p _ => ?_)
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        exact intervalIntegral.norm_integral_le_integral_norm (by norm_num : (0 : ℝ) ≤ 1)
    _ = (2 * Real.pi) * ∑ p ∈ s0, ∫ s in (0 : ℝ)..1,
          ‖bumpFT (fun θ : ℝ => (θ : ℂ) * φ θ) (u - (p : ℝ) + s)‖ := by
        rw [Finset.mul_sum]
    _ = (2 * Real.pi) * ∫ s in (0 : ℝ)..1, ∑ p ∈ s0,
          ‖bumpFT (fun θ : ℝ => (θ : ℂ) * φ θ) (u - (p : ℝ) + s)‖ := by
        congr 1
        exact (intervalIntegral.integral_finsetSum (s := s0)
          (f := fun p : ℤ => fun s : ℝ =>
            ‖bumpFT (fun θ : ℝ => (θ : ℂ) * φ θ) (u - (p : ℝ) + s)‖)
          (fun p _ => (hcont_p p).intervalIntegrable 0 1)).symm
    _ ≤ (2 * Real.pi) * ∫ s in (0 : ℝ)..1, C * a := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        exact intervalIntegral.integral_mono (by norm_num : (0 : ℝ) ≤ 1) hint1 hint2
          (fun s => hpt s)
    _ = (2 * Real.pi) * (C * a) := by
        rw [intervalIntegral.integral_const, sub_zero, one_smul]

/-! ## The target -/

theorem diffMassSharp (P : Polynomial ℤ) : ∃ C : ℝ, 0 < C ∧
    (∀ (N k : ℕ), 1 ≤ N → (2 : ℝ) ^ k ≤ (N : ℝ) → ∀ u : ℝ,
      (∑' p : ℤ, ‖Work.KMTAreas.A7.bumpFT (Work.KMTAreas.A7.varphiN N k) (u + 1 - (p : ℝ))
          - Work.KMTAreas.A7.bumpFT (Work.KMTAreas.A7.varphiN N k) (u - (p : ℝ))‖)
        ≤ C * ((2 : ℝ) ^ k / (N : ℝ))) ∧
    (∀ (N k : ℕ), 1 ≤ N → (2 : ℝ) ^ (P.natDegree * k) ≤ (N : ℝ) ^ P.natDegree → ∀ u : ℝ,
      (∑' p : ℤ, ‖Work.KMTAreas.A7.bumpFT (Work.KMTAreas.A7.varphitildeN P.natDegree N k)
              (u + 1 - (p : ℝ))
          - Work.KMTAreas.A7.bumpFT (Work.KMTAreas.A7.varphitildeN P.natDegree N k)
              (u - (p : ℝ))‖)
        ≤ C * ((2 : ℝ) ^ (P.natDegree * k) / (N : ℝ) ^ P.natDegree)) := by
  obtain ⟨Cm, hCmpos, hm0, hm1, hm2, hn0, hn1, hn2⟩ := sharpBumpMassSum P
  refine ⟨max 1 (2 * Real.pi * Cm), ?_, ?_, ?_⟩
  · exact lt_max_of_lt_left one_pos
  · intro N k hN hk u
    have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
    have ha : (0 : ℝ) ≤ (2 : ℝ) ^ k / (N : ℝ) :=
      div_nonneg (by positivity) hNpos.le
    have hmass : ∀ w : ℝ,
        (∑' p : ℤ, ‖bumpFT (fun θ : ℝ => (θ : ℂ) * varphiN N k θ) (w - (p : ℝ))‖)
          ≤ Cm * ((2 : ℝ) ^ k / (N : ℝ)) := fun w => hm1 N k hN hk w
    have h := tsum_bumpFT_diff_le (varphiN N k) (contDiff_varphiN N k)
      (hasCompactSupport_varphiN N k) hmass u
    refine h.trans ?_
    have hrw : (2 * Real.pi) * (Cm * ((2 : ℝ) ^ k / (N : ℝ)))
        = (2 * Real.pi * Cm) * ((2 : ℝ) ^ k / (N : ℝ)) := by ring
    rw [hrw]
    exact mul_le_mul_of_nonneg_right (le_max_right _ _) ha
  · intro N k hN hk u
    have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
    have hNpow : (0 : ℝ) < (N : ℝ) ^ P.natDegree := pow_pos hNpos _
    have ha : (0 : ℝ) ≤ (2 : ℝ) ^ (P.natDegree * k) / (N : ℝ) ^ P.natDegree :=
      div_nonneg (by positivity) hNpow.le
    have hmass : ∀ w : ℝ,
        (∑' p : ℤ,
            ‖bumpFT (fun θ : ℝ => (θ : ℂ) * varphitildeN P.natDegree N k θ) (w - (p : ℝ))‖)
          ≤ Cm * ((2 : ℝ) ^ (P.natDegree * k) / (N : ℝ) ^ P.natDegree) :=
      fun w => hn1 N k hN hk w
    have h := tsum_bumpFT_diff_le (varphitildeN P.natDegree N k)
      (contDiff_varphitildeN P.natDegree N k)
      (hasCompactSupport_varphitildeN P.natDegree N k) hmass u
    refine h.trans ?_
    have hrw : (2 * Real.pi) * (Cm * ((2 : ℝ) ^ (P.natDegree * k) / (N : ℝ) ^ P.natDegree))
        = (2 * Real.pi * Cm)
          * ((2 : ℝ) ^ (P.natDegree * k) / (N : ℝ) ^ P.natDegree) := by ring
    rw [hrw]
    exact mul_le_mul_of_nonneg_right (le_max_right _ _) ha

end

end Work.KMTAreas.A7
