import Mathlib
import Submission.Work.KMTAreas.A7.lacunaryBump_mult_bound_k0_diff
import Submission.Work.KMTAreas.A7.lacunaryDiffSymbol_mikhlin_const
import Submission.Work.KMTAreas.A7.abs_PevalR_div_gScale_le

namespace Work.KMTAreas.A7

open MeasureTheory Finset
open scoped ENNReal NNReal BigOperators


section Helpers

/-- `gScale d N k₂` is the `d`-th power of the `f`-side scale `lacσ N k₂`. -/
private lemma gScale_eq_lacσ_pow (d N k₂ : ℕ) : gScale d N k₂ = (lacσ N k₂) ^ d := by
  rw [gScale, lacσ]
  rw [← zpow_natCast ((2 : ℝ) ^ ((Work.Analysis.EndVar.logN N : ℤ) - (k₂ : ℤ))) d, ← zpow_mul]
  congr 1
  ring

/-- The exponent `2 ^ (d Log N)` of `φ̃_N` at the bottom height is the scale `gScale d N 0`. -/
private lemma rpow_eq_gScale (d N : ℕ) :
    (2 : ℝ) ^ ((d : ℝ) * (Work.Analysis.EndVar.logN N : ℝ)) = gScale d N 0 := by
  have h1 : (2 : ℝ) ^ (Work.Analysis.EndVar.logN N : ℝ) = lacσ N 0 := by
    rw [lacσ]
    simp only [Nat.cast_zero, sub_zero, Real.rpow_intCast]
  have h2 : gScale d N 0 = (lacσ N 0) ^ d := gScale_eq_lacσ_pow d N 0
  rw [h2, ← h1, mul_comm, Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
  rw [Real.rpow_natCast]

/-- The unmodulated `g`-side bump at the bottom height: `φ̃_N = η(gScale d N 0 ·)`. -/
private lemma varphitildeN_zero (d N : ℕ) :
    varphitildeN d N 0 = fun ξ : ℝ => Work.KMTContract.kmtEta (gScale d N 0 * ξ) := by
  funext ξ
  simp only [varphitildeN, if_true]
  rw [rpow_eq_gScale]

/-- The difference symbol at the bottom height. -/
private lemma varphitildeNt_zero_sub (P : Polynomial ℤ) (d N : ℕ) (t ξ : ℝ) :
    varphitildeNt P d N 0 t ξ - varphitildeN d N 0 ξ
      = Work.KMTContract.kmtEta (gScale d N 0 * ξ)
          * (ee (PevalR P ((N : ℝ) * t) * ξ) - 1) := by
  rw [varphitildeNt, varphitildeN_zero]
  ring

/-- The `d`-th power of a `2`-lacunary scale family is again `2`-lacunary when `d ≥ 1`. -/
private lemma lacunaryFam_pow {ι : Type*} {d : ℕ} (hd : 1 ≤ d) {D : Finset ι} {σ : ι → ℝ}
    (h : Work.Analysis.CzShift.LacunaryFam 2 D σ) :
    Work.Analysis.CzShift.LacunaryFam 2 D (fun i => (σ i) ^ d) := by
  refine ⟨fun i hi => pow_pos (h.1 i hi) d, ?_⟩
  intro i hi j hj hij
  have hi0 : 0 < σ i := h.1 i hi
  have hj0 : 0 < σ j := h.1 j hj
  have h2 := h.2 i hi j hj hij
  have hmin : min ((σ i) ^ d) ((σ j) ^ d) = (min (σ i) (σ j)) ^ d := by
    rcases le_total (σ i) (σ j) with hle | hle
    · rw [min_eq_left hle, min_eq_left (pow_le_pow_left₀ hi0.le hle d)]
    · rw [min_eq_right hle, min_eq_right (pow_le_pow_left₀ hj0.le hle d)]
  have hmax : max ((σ i) ^ d) ((σ j) ^ d) = (max (σ i) (σ j)) ^ d := by
    rcases le_total (σ i) (σ j) with hle | hle
    · rw [max_eq_right hle, max_eq_right (pow_le_pow_left₀ hi0.le hle d)]
    · rw [max_eq_left hle, max_eq_left (pow_le_pow_left₀ hj0.le hle d)]
  rw [hmin, hmax]
  calc 2 * (min (σ i) (σ j)) ^ d ≤ 2 ^ d * (min (σ i) (σ j)) ^ d := by
        refine mul_le_mul_of_nonneg_right ?_ (by positivity)
        simpa using pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hd
    _ = (2 * min (σ i) (σ j)) ^ d := by rw [mul_pow]
    _ ≤ (max (σ i) (σ j)) ^ d := pow_le_pow_left₀ (by positivity) h2 d

end Helpers

/-
# The `g`-side low-frequency difference multiplier bound

The continuous (`ℝ`-multiplier) input of the `g`-side linear lacunary estimate: the signed sums of
the *differences* `φ̃_{N,t} − φ̃_N` at the bottom height `k₂ = 0` are `L^p(ℝ)`-multipliers with a
constant independent of the sign pattern `ε`, the set `U`, `t` and the lacunary family `a`.  This is
the `g`-side twin of the PROVED `Work.KMTAreas.A7.lacunaryBump_mult_bound_k0_diff`
(`Submission/Work/KMTAreas/A7/lacunaryBump_mult_bound_k0_diff.lean`: same statement with
`varphiNt`/`varphiN` in place of `varphitildeNt`/`varphitildeN`), and it is the statement of
`Work.KMTAreas.A7.varphitildeNt_diff_mult_bound`
(`Submission/Work/KMTAreas/A7/varphitildeNt_diff_mult_bound.lean`, currently a `sorry`); the consumer
will set `varphitildeNt_diff_mult_bound := VarphitildeDiffMultBound`.

## Route (with the crucial technical caveat)

Read the proof of `lacunaryBump_mult_bound_k0_diff` first: `Commons.Analysis.Fourier.mikhlin_multiplier_lp`
(Hörmander/Mikhlin criterion), `lacBumpDecimation` (decimation of the lacunary families),
`Work.KMTAreas.A7.kmtEta_deriv_bounds`, and the difference-symbol criterion
`Work.KMTAreas.A7.lacunaryDiffSymbol_mikhlin`.

Here `varphitildeNt P d N 0 t ξ − varphitildeN d N 0 ξ = kmtEta(2^{d·Log N}ξ)·(e(PevalR P(Nt)ξ)−1)`,
i.e. the same shape as the `f`-side with the `d`-scaled bump `σ_N = (lacσ N 0)^d` and the phase
coefficient `PevalR P(Nt)`.  **Caveat:** `lacunaryDiffSymbol_mikhlin` hard-wires the hypothesis
`|c_i| ≤ 2 σ_i`, whereas here `|PevalR P(Nt)| / gScale d N 0 ≤ K(P,d)` for a fixed `K` (this is where
`P.natDegree ≤ d` enters, via `abs_PevalR_div_gScale_le`).  So either *generalise*
`lacunaryDiffSymbol_mikhlin` to a general constant `K` (its `2`-lacunarity survives the `d`-th power:
`σ_{i+1}/σ_i ≥ 2` is preserved by `x ↦ x^d`), or redo its argument.  The cancellation at frequency
`0` (`φ̃_{N,t}(0) = φ̃_N(0) = 1`) is what the `k₂ = 0` case needs, exactly as on the `f`-side.

The *un-differenced* `g`-side bound at heights `k₂ ≥ 1` is
`Work.KMTAreas.A7.lacunaryBumpG_mult_bound_k2pos` (constant `C(1 + d k₂)`); its proof shows the
intended techniques and the shape of the estimate, but is not a substitute for this one.
-/
theorem VarphitildeDiffMultBound (P : Polynomial ℤ) (d : ℕ) (hd : 2 ≤ d)
    (hdP : P.natDegree ≤ d) (p : ℝ) (hp : 1 < p) (Λ : NNReal) (hΛ : 1 < Λ) :
    ∃ C : NNReal, 0 < C ∧
      ∀ (t : ℝ) (ht : t ∈ Set.Icc (1/2 : ℝ) 1) (a : ℕ → NNReal)
        (ha : PointwiseErgodicTheorems.Lacunary Λ a) (ha1 : ∀ n, 1 ≤ a n)
        (U : Finset ℕ) (ε : ℕ → ℂ) (hε : ∀ n, ‖ε n‖ ≤ 1),
        Work.Analysis.IWMultiplier.IsLqMultiplierBound (ENNReal.ofReal p)
          (fun ξ : ℝ => ∑ n ∈ U, ε n *
            (Work.KMTAreas.A7.varphitildeNt P d (Nat.floor (a n)) 0 t ξ
              - Work.KMTAreas.A7.varphitildeN d (Nat.floor (a n)) 0 ξ))
          C := by
  obtain ⟨Cm, hCmpos, hCm⟩ := Commons.Analysis.Fourier.mikhlin_multiplier_lp p hp
  obtain ⟨M, hMpos, hMlac⟩ := lacBumpDecimation Λ hΛ
  obtain ⟨M0, M1, M2, hM0, hM1, hM2, hηcd, hη0, hη1, hη2, hηs0, hηs1, hηs2, hηd, hηd2⟩ :=
    kmtEta_deriv_bounds
  have hd1 : 1 ≤ d := by omega
  set Kc : ℝ := ((∑ i ∈ Finset.range (P.natDegree + 1), |(P.coeff i : ℝ)|) + 1) * 3 ^ d * 2
    with hKcdef
  have hKcnn : 0 ≤ Kc := by rw [hKcdef]; positivity
  obtain ⟨A, hApos, hA⟩ := lacunaryDiffSymbol_mikhlin_const Work.KMTContract.kmtEta M0 M1 M2
    hM0 hM1 hM2 hηcd hη0 hη1 hη2 hηs0 hηs1 hηs2 hηd hηd2 Kc hKcnn 2 (by norm_num)
  have hCApos : (0 : ℝ) < (M : ℝ) * (Cm * A) := by
    have hMnn : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hMpos
    positivity
  refine ⟨⟨(M : ℝ) * (Cm * A), le_of_lt hCApos⟩, hCApos, ?_⟩
  intro t ht a ha ha1 U ε hε f
  have htabs : |t| ≤ 1 := by
    rw [abs_of_nonneg (by linarith [ht.1])]
    exact ht.2
  let ρ : ℕ → ℝ := fun n => gScale d (Nat.floor (a n)) 0
  let cc : ℕ → ℝ := fun n => PevalR P ((Nat.floor (a n) : ℝ) * t)
  have hsym : (fun ξ : ℝ => ∑ n ∈ U, ε n * (varphitildeNt P d (Nat.floor (a n)) 0 t ξ
        - varphitildeN d (Nat.floor (a n)) 0 ξ))
      = fun ξ : ℝ => ∑ n ∈ U, ε n * (Work.KMTContract.kmtEta (ρ n * ξ)
          * (Complex.exp (2 * Real.pi * Complex.I * (cc n * ξ)) - 1)) := by
    funext ξ
    refine Finset.sum_congr rfl (fun n _ => ?_)
    rw [varphitildeNt_zero_sub, ee_mul]
  rw [hsym]
  let fib : ℕ → ℝ → ℂ := fun r ξ => ∑ n ∈ U.filter (fun n => n % M = r), ε n *
      (Work.KMTContract.kmtEta (ρ n * ξ)
        * (Complex.exp (2 * Real.pi * Complex.I * (cc n * ξ)) - 1))
  have hΦeq : (fun ξ : ℝ => ∑ n ∈ U, ε n * (Work.KMTContract.kmtEta (ρ n * ξ)
        * (Complex.exp (2 * Real.pi * Complex.I * (cc n * ξ)) - 1)))
      = fun ξ : ℝ => ∑ r ∈ Finset.range M, fib r ξ := by
    funext ξ
    simp only [fib]
    exact (Finset.sum_fiberwise_of_maps_to (s := U) (t := Finset.range M)
      (g := fun n => n % M) (fun n _ => Finset.mem_range.mpr (Nat.mod_lt n hMpos))
      (fun n => ε n * (Work.KMTContract.kmtEta (ρ n * ξ)
        * (Complex.exp (2 * Real.pi * Complex.I * (cc n * ξ)) - 1)))).symm
  rw [hΦeq]
  have hfib : ∀ r ∈ Finset.range M, ContDiff ℝ 2 (fib r) ∧ (∀ ξ : ℝ, ‖fib r ξ‖ ≤ A) ∧
      (∀ ξ : ℝ, |ξ| * ‖deriv (fib r) ξ‖ ≤ A) ∧
      (∀ ξ : ℝ, |ξ| ^ 2 * ‖iteratedDeriv 2 (fib r) ξ‖ ≤ A) := by
    intro r hr
    have hlac : Work.Analysis.CzShift.LacunaryFam 2 (U.filter (fun n => n % M = r)) ρ := by
      have h0 := hMlac 0 a ha ha1 U r
      have h1 : Work.Analysis.CzShift.LacunaryFam 2 (U.filter (fun n => n % M = r))
          (fun n => (lacσ (Nat.floor (a n)) 0) ^ d) := lacunaryFam_pow hd1 h0
      simpa only [ρ, gScale_eq_lacσ_pow] using h1
    have hcb : ∀ i ∈ U.filter (fun n => n % M = r), |cc i| ≤ Kc * ρ i := by
      intro i _
      have hb := abs_PevalR_div_gScale_le P d (Nat.floor (a i)) 0 hdP htabs
      have hgpos : 0 < gScale d (Nat.floor (a i)) 0 := by rw [gScale]; positivity
      have h2 : (1 + (2 : ℝ) ^ (d * 0)) = 2 := by norm_num
      rw [h2, div_le_iff₀ hgpos] at hb
      rw [hKcdef]
      exact hb
    have heps : ∀ i ∈ U.filter (fun n => n % M = r), ‖ε i‖ ≤ 1 := fun i _ => hε i
    have hh := hA (U.filter (fun n => n % M = r)) ρ cc ε hlac hcb heps
    simpa only [fib] using hh
  have hMA : (0 : ℝ) ≤ (M : ℝ) * A :=
    mul_nonneg (Nat.cast_nonneg _) hApos.le
  have hcd : ContDiff ℝ 2 (fun ξ : ℝ => ∑ r ∈ Finset.range M, fib r ξ) :=
    ContDiff.sum (fun r hr => (hfib r hr).1)
  have hsup : ∀ ξ : ℝ, ‖∑ r ∈ Finset.range M, fib r ξ‖ ≤ (M : ℝ) * A := by
    intro ξ
    calc ‖∑ r ∈ Finset.range M, fib r ξ‖ ≤ ∑ r ∈ Finset.range M, ‖fib r ξ‖ := norm_sum_le _ _
      _ ≤ ∑ r ∈ Finset.range M, A := Finset.sum_le_sum (fun r hr => (hfib r hr).2.1 ξ)
      _ = (M : ℝ) * A := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hd1' : ∀ ξ : ℝ, |ξ| * ‖deriv (fun ξ : ℝ => ∑ r ∈ Finset.range M, fib r ξ) ξ‖
      ≤ (M : ℝ) * A := by
    intro ξ
    have hdiff : ∀ r ∈ Finset.range M, DifferentiableAt ℝ (fib r) ξ :=
      fun r hr => (((hfib r hr).1).differentiable (by norm_num)).differentiableAt
    have hsumfun : (fun ξ : ℝ => ∑ r ∈ Finset.range M, fib r ξ)
        = ∑ r ∈ Finset.range M, fib r := by
      funext ξ; simp only [Finset.sum_apply]
    rw [hsumfun, deriv_sum hdiff]
    calc |ξ| * ‖∑ r ∈ Finset.range M, deriv (fib r) ξ‖
        ≤ |ξ| * ∑ r ∈ Finset.range M, ‖deriv (fib r) ξ‖ :=
          mul_le_mul_of_nonneg_left (norm_sum_le _ _) (abs_nonneg ξ)
      _ = ∑ r ∈ Finset.range M, |ξ| * ‖deriv (fib r) ξ‖ := by rw [Finset.mul_sum]
      _ ≤ ∑ r ∈ Finset.range M, A := Finset.sum_le_sum (fun r hr => (hfib r hr).2.2.1 ξ)
      _ = (M : ℝ) * A := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hd2' : ∀ ξ : ℝ, |ξ| ^ 2 * ‖iteratedDeriv 2 (fun ξ : ℝ => ∑ r ∈ Finset.range M, fib r ξ) ξ‖
      ≤ (M : ℝ) * A := by
    intro ξ
    have hcdat : ∀ r ∈ Finset.range M, ContDiffAt ℝ 2 (fib r) ξ :=
      fun r hr => ((hfib r hr).1).contDiffAt
    have hsumfun : (fun ξ : ℝ => ∑ r ∈ Finset.range M, fib r ξ)
        = ∑ r ∈ Finset.range M, fib r := by
      funext ξ; simp only [Finset.sum_apply]
    rw [hsumfun, iteratedDeriv_sum hcdat]
    calc |ξ| ^ 2 * ‖∑ r ∈ Finset.range M, iteratedDeriv 2 (fib r) ξ‖
        ≤ |ξ| ^ 2 * ∑ r ∈ Finset.range M, ‖iteratedDeriv 2 (fib r) ξ‖ :=
          mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by positivity)
      _ = ∑ r ∈ Finset.range M, |ξ| ^ 2 * ‖iteratedDeriv 2 (fib r) ξ‖ := by rw [Finset.mul_sum]
      _ ≤ ∑ r ∈ Finset.range M, A := Finset.sum_le_sum (fun r hr => (hfib r hr).2.2.2 ξ)
      _ = (M : ℝ) * A := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hmain := hCm (fun ξ : ℝ => ∑ r ∈ Finset.range M, fib r ξ) ((M : ℝ) * A) hMA hcd hsup
    hd1' hd2' f
  have hbridge : Work.Analysis.IWMultiplier.contMulOp
      (fun ξ : ℝ => ∑ r ∈ Finset.range M, fib r ξ) (f : ℝ → ℂ)
      = fun x : ℝ => ∫ ξ : ℝ, ((∑ r ∈ Finset.range M, fib r ξ)
          * Complex.exp (2 * Real.pi * Complex.I * (x * ξ)))
          • (FourierTransform.fourier (f : ℝ → ℂ) ξ) := by
    funext x
    exact contMulOp_eq_integral _ f x
  rw [hbridge]
  calc MeasureTheory.eLpNorm (fun x : ℝ => ∫ ξ : ℝ, ((∑ r ∈ Finset.range M, fib r ξ)
          * Complex.exp (2 * Real.pi * Complex.I * (x * ξ)))
          • (FourierTransform.fourier (f : ℝ → ℂ) ξ))
        (ENNReal.ofReal p) MeasureTheory.volume
      ≤ ENNReal.ofReal (Cm * ((M : ℝ) * A))
          * MeasureTheory.eLpNorm (f : ℝ → ℂ) (ENNReal.ofReal p) MeasureTheory.volume := hmain
    _ = ENNReal.ofReal ((M : ℝ) * (Cm * A))
          * MeasureTheory.eLpNorm (f : ℝ → ℂ) (ENNReal.ofReal p) MeasureTheory.volume := by
        rw [show Cm * ((M : ℝ) * A) = (M : ℝ) * (Cm * A) by ring]

end Work.KMTAreas.A7
