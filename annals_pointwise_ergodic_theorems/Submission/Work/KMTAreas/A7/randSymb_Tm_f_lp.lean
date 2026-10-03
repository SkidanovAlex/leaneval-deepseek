import Mathlib
import Submission.Work.KMTAreas.A7.randSymb_coeff_data
import Submission.Work.KMTAreas.A7.randSymb_support_le
import Submission.Work.KMTAreas.A7.lacunaryBump_mult_bound_k1pos
import Submission.Work.KMTAreas.A7.lacunaryBump_mult_bound_k0_diff
import Submission.Work.KMTAreas.A7.lacunaryBumpExponent
import Submission.Work.KMTAreas.A7.IWLqBound_diffFreqs_of_arithFreqs
import Submission.Work.KMTAreas.A7.IsLqMultiplierBound_star
import Submission.Work.KMTAreas.A7.exists_interp_theta
import Submission.Work.KMTAreas.A7.eLpNorm_iwConv_le_of_IWLqBoundScalar_of_bounded
import Submission.Work.KMTAreas.A7.eLpNorm_finite_bounded
import Submission.Work.KMTAreas.A7rand.iwLqBound_of_even_continuous
import Submission.Work.KMTAreas.A7rand.smallCond_not_narrow_bounded
import Submission.Work.KMTAreas.A7rand.lowpass_lacunary_mult_bound
import Submission.Work.KMTAreas.A7rand.Tm_randSymb_crude_bound

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.KMTAreas.A7

noncomputable section

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal BigOperators FourierTransform
open PointwiseErgodicTheorems Submission.PointwiseErgodicTheorems
open Work.KMTContract Work.Analysis.EndVar
open Work.Analysis.IonescuWainger Work.Analysis.IWMultiplier


/-! ## Elementary helpers -/

/-- A `Λ`-lacunary sequence `a : ℕ → ℝ≥0` with `Λ > 1` and `1 ≤ a n` is monotone. -/
lemma monotone_of_lacunary {Λ : NNReal} {a : ℕ → NNReal} (hΛ : 1 < Λ)
    (ha : PointwiseErgodicTheorems.Lacunary Λ a) (ha1 : ∀ n, 1 ≤ a n) : Monotone a := by
  refine monotone_nat_of_le_succ (fun n => ?_)
  have hpos : (0 : NNReal) < a n := lt_of_lt_of_le zero_lt_one (ha1 n)
  have h1 : Λ * a n < a (n + 1) := by
    have h2 : Λ < a (n + 1) / a n := ha n
    rwa [lt_div_iff₀ hpos] at h2
  have h3 : a n ≤ Λ * a n := by nlinarith [ha1 n, hΛ]
  exact le_trans h3 h1.le

/-- **Good major arcs is monotone in the height**: if `(l,k)` has good major arcs, so does
`(l',k)` for every `l' ≤ l` (with `ρ, Cρ ≥ 0`). -/
lemma GoodMajorArcs.mono_l {ρ Cρ : ℝ} (hρ : 0 ≤ ρ) (hCρ : 0 ≤ Cρ) {l l' : ℕ} {k : ℤ}
    (hll : l' ≤ l) (h : GoodMajorArcs ρ Cρ l k) : GoodMajorArcs ρ Cρ l' k := by
  have hl : (l' : ℝ) ≤ (l : ℝ) := by exact_mod_cast hll
  have hρl : ρ * (l' : ℝ) ≤ ρ * (l : ℝ) := mul_le_mul_of_nonneg_left hl hρ
  have hxy : (2:ℝ) ^ (ρ * (l' : ℝ)) ≤ (2:ℝ) ^ (ρ * (l : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) hρl
  have h2 : -Cρ * (2:ℝ) ^ (ρ * (l : ℝ)) ≤ -Cρ * (2:ℝ) ^ (ρ * (l' : ℝ)) := by
    nlinarith [hxy]
  exact le_trans h h2

/-! ## Helpers for `IsLqMultiplierBound` -/

/-- `IsLqMultiplierBound` is monotone in the constant. -/
theorem IsLqMultiplierBound.mono {q : ENNReal} {φ : ℝ → ℂ} {M M' : NNReal}
    (h : IsLqMultiplierBound q φ M) (hMM' : M ≤ M') : IsLqMultiplierBound q φ M' := by
  intro f
  refine (h f).trans ?_
  exact mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal (by exact_mod_cast hMM')) zero_le

/-- **Additivity of the continuous multiplier bound in the symbol.** -/
theorem IsLqMultiplierBound.add {q : ENNReal} (hq : 1 ≤ q) {φ ψ : ℝ → ℂ} {M N : NNReal}
    (hφ : Integrable φ (volume : Measure ℝ)) (hψ : Integrable ψ (volume : Measure ℝ))
    (h1 : IsLqMultiplierBound q φ M) (h2 : IsLqMultiplierBound q ψ N) :
    IsLqMultiplierBound q (φ + ψ) (M + N) := by
  intro G
  have hFtop : MemLp (fun ξ : ℝ => 𝓕 (G : ℝ → ℂ) ξ) ⊤ (volume : Measure ℝ) := by
    simpa only [SchwartzMap.fourier_coe] using
      (SchwartzMap.memLp (𝓕 G) ⊤ (volume : Measure ℝ))
  have hF : Integrable (fun ξ : ℝ => φ ξ * 𝓕 (G : ℝ → ℂ) ξ) (volume : Measure ℝ) :=
    hφ.mul_of_top_left hFtop
  have hGs : Integrable (fun ξ : ℝ => ψ ξ * 𝓕 (G : ℝ → ℂ) ξ) (volume : Measure ℝ) :=
    hψ.mul_of_top_left hFtop
  have hlin : contMulOp (φ + ψ) (G : ℝ → ℂ)
      = fun x : ℝ => contMulOp φ (G : ℝ → ℂ) x + contMulOp ψ (G : ℝ → ℂ) x := by
    have hsum := lacBump_contMulOp_finsetSum (Finset.univ : Finset (Fin 2))
      (fun i : Fin 2 => if i = 0 then φ else ψ) G (fun i _ => by
        by_cases hi : i = 0
        · simpa [hi] using hφ
        · simpa [hi] using hψ)
    have hsym : (fun ξ : ℝ => ∑ i ∈ (Finset.univ : Finset (Fin 2)),
        (if i = 0 then φ else ψ) ξ) = φ + ψ := by
      funext ξ; rw [Fin.sum_univ_two]; simp
    rw [hsym, Fin.sum_univ_two] at hsum
    funext x
    simpa using congrFun hsum x
  have hcφ : Continuous (contMulOp φ (G : ℝ → ℂ)) := lacBump_contMulOp_continuous hF
  have hcψ : Continuous (contMulOp ψ (G : ℝ → ℂ)) := lacBump_contMulOp_continuous hGs
  rw [hlin]
  calc eLpNorm (fun x : ℝ => contMulOp φ (G : ℝ → ℂ) x + contMulOp ψ (G : ℝ → ℂ) x) q
        (volume : Measure ℝ)
      ≤ eLpNorm (contMulOp φ (G : ℝ → ℂ)) q (volume : Measure ℝ)
        + eLpNorm (contMulOp ψ (G : ℝ → ℂ)) q (volume : Measure ℝ) :=
        eLpNorm_add_le hq
    _ ≤ ENNReal.ofReal (M : ℝ) * eLpNorm (G : ℝ → ℂ) q volume
        + ENNReal.ofReal (N : ℝ) * eLpNorm (G : ℝ → ℂ) q volume := add_le_add (h1 G) (h2 G)
    _ = ENNReal.ofReal ((M + N : NNReal) : ℝ) * eLpNorm (G : ℝ → ℂ) q volume := by
        rw [← add_mul, ← ENNReal.ofReal_add (by positivity) (by positivity), NNReal.coe_add]

/-- **Natural multiples of a bounded multiplier symbol.** -/
theorem IsLqMultiplierBound.const_mul_nat {q : ENNReal} (m : ℕ) {φ : ℝ → ℂ} {M : NNReal}
    (h : IsLqMultiplierBound q φ M) :
    IsLqMultiplierBound q (fun x : ℝ => (m : ℂ) * φ x) ((m : NNReal) * M) := by
  intro G
  have h1 : contMulOp (fun x : ℝ => (m : ℂ) * φ x) (G : ℝ → ℂ)
      = (m : ℂ) • contMulOp φ (G : ℝ → ℂ) := by
    funext x
    rw [contMulOp, contMulOp]
    have h2 : (fun ξ : ℝ => ((m : ℂ) * φ ξ) * 𝓕 (G : ℝ → ℂ) ξ)
        = fun ξ : ℝ => (m : ℂ) * (φ ξ * 𝓕 (G : ℝ → ℂ) ξ) := by
      funext ξ; ring
    rw [h2, lacBump_fourierInv_const_mul]
    rfl
  rw [h1]
  calc eLpNorm ((m : ℂ) • contMulOp φ (G : ℝ → ℂ)) q (volume : Measure ℝ)
      = ‖(m : ℂ)‖ₑ * eLpNorm (contMulOp φ (G : ℝ → ℂ)) q (volume : Measure ℝ) :=
        eLpNorm_const_smul _ _ _ _
    _ ≤ ‖(m : ℂ)‖ₑ * (ENNReal.ofReal (M : ℝ) * eLpNorm (G : ℝ → ℂ) q volume) :=
        mul_le_mul_of_nonneg_left (h G) zero_le
    _ = ENNReal.ofReal (((m : NNReal) * M : NNReal) : ℝ) * eLpNorm (G : ℝ → ℂ) q volume := by
        have hm : ‖(m : ℂ)‖ₑ = (m : ENNReal) := by
          rw [← ofReal_norm, Complex.norm_natCast, ENNReal.ofReal_natCast]
        have hco : ENNReal.ofReal (((m : NNReal) * M : NNReal) : ℝ)
            = (m : ENNReal) * (M : ENNReal) := by
          rw [NNReal.coe_mul, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_coe_nnreal,
            ENNReal.ofReal_coe_nnreal, ENNReal.coe_natCast]
        rw [hm, hco, ENNReal.ofReal_coe_nnreal]
        ring

/-! ## The continuous multiplier bound for the randomised cut-off, `k₁ ≥ 1` -/

/-- **The continuous multiplier bound for the randomised cut-off, `k₁ ≥ 1`.** -/
theorem isLqMultiplierBound_randSymb_k1pos (Λ : NNReal) (hΛ : 1 < Λ) (q : ℝ) (hq : 1 < q) :
    ∃ C : NNReal, 0 < C ∧
      ∀ (ρ : ℝ) (C₀ : ℕ) (a : ℕ → NNReal) (l₁ l₂ k₁ k₂ K : ℕ) (t : ℝ) (ε : ℕ → ℂ),
        PointwiseErgodicTheorems.Lacunary Λ a → (∀ n, 1 ≤ a n) → 1 ≤ k₁ →
        t ∈ Set.Icc (1/2 : ℝ) 1 → (∀ n, ‖ε n‖ ≤ 1) →
        IsLqMultiplierBound (ENNReal.ofReal q)
          (randSymb (smallSymbF ρ C₀ a l₁ l₂ k₁ k₂ t) ε K) (C * (1 + k₁)) := by
  obtain ⟨Cq, hCqpos, hCq⟩ := lacunaryBump_mult_bound_k1pos q hq Λ hΛ
  refine ⟨2 * Cq, by positivity, ?_⟩
  intro ρ C₀ a l₁ l₂ k₁ k₂ K t ε ha ha1 hk1 ht hε
  have hmono : Monotone a := monotone_of_lacunary hΛ ha ha1
  obtain ⟨hcoeff, hnorm, -⟩ := randSymb_coeff_data ρ C₀ a l₁ l₂ k₁ k₂ t ε hε hmono K
  set c : ℕ → ℂ := fun n => randCoeff ρ C₀ a l₁ l₂ k₁ k₂ ε K n / 2 with hc
  have hcε : ∀ n, ‖c n‖ ≤ 1 := by
    intro n
    have hn := hnorm n
    simp only [hc]
    rw [norm_div]
    norm_num
    linarith
  have h := hCq k₁ hk1 t ht a ha ha1 (Finset.range (K + 1)) c hcε
  have hsym : randSymb (smallSymbF ρ C₀ a l₁ l₂ k₁ k₂ t) ε K
      = fun ξ : ℝ => (2 : ℂ) * ∑ m ∈ Finset.range (K + 1),
          c m * varphiNt (Nat.floor (a m)) k₁ t ξ := by
    rw [hcoeff]
    funext ξ
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun m _ => ?_)
    simp only [hc]
    ring
  rw [hsym]
  refine IsLqMultiplierBound.mono (IsLqMultiplierBound.const_mul_nat 2 h) ?_
  exact le_of_eq (mul_assoc 2 Cq (1 + (k₁ : NNReal))).symm

/-! ## The continuous multiplier bound for the randomised cut-off at `k₁ = 0` -/

/-- **The continuous multiplier bound for the randomised cut-off at `k₁ = 0`.**  The randomised
symbol splits into the *modulated differences* `φ_{N,t} − φ_N` (handled by
`lacunaryBump_mult_bound_k0_diff`) and the *low-pass* lacunary sum `∑ d_m φ_{N_m}` whose
coefficients have bounded interval sums (handled by `lowpass_lacunary_mult_bound`). -/
theorem isLqMultiplierBound_randSymb_k0 (Λ : NNReal) (hΛ : 1 < Λ) (q : ℝ) (hq : 1 < q) :
    ∃ C : NNReal, 0 < C ∧
      ∀ (ρ : ℝ) (C₀ : ℕ) (a : ℕ → NNReal) (l₁ l₂ k₂ K : ℕ) (t : ℝ) (ε : ℕ → ℂ),
        PointwiseErgodicTheorems.Lacunary Λ a → (∀ n, 1 ≤ a n) →
        t ∈ Set.Icc (1/2 : ℝ) 1 → (∀ n, ‖ε n‖ ≤ 1) →
        IsLqMultiplierBound (ENNReal.ofReal q)
          (randSymb (smallSymbF ρ C₀ a l₁ l₂ 0 k₂ t) ε K) C := by
  obtain ⟨C1, hC1pos, hC1⟩ := lacunaryBump_mult_bound_k0_diff q hq Λ hΛ
  obtain ⟨C2, hC2pos, hC2⟩ :=
    Work.KMTAreas.A7rand.lowpass_lacunary_mult_bound q hq Λ hΛ
  refine ⟨2 * C1 + C2, by positivity, ?_⟩
  intro ρ C₀ a l₁ l₂ k₂ K t ε ha ha1 ht hε
  have hmono : Monotone a := monotone_of_lacunary hΛ ha ha1
  obtain ⟨hcoeff, hnorm, hIcc⟩ := randSymb_coeff_data ρ C₀ a l₁ l₂ 0 k₂ t ε hε hmono K
  set r : ℕ → ℂ := fun m => randCoeff ρ C₀ a l₁ l₂ 0 k₂ ε K m with hr
  set c : ℕ → ℂ := fun m => r m / 2 with hc
  have hcε : ∀ n, ‖c n‖ ≤ 1 := by
    intro n
    have hn := hnorm n
    simp only [hc]
    rw [norm_div]
    norm_num
    linarith
  have hIcc' : ∀ u v : ℕ, ‖∑ m ∈ Finset.Icc u v, r m‖ ≤ 4 := by
    intro u v
    simpa only [hr] using hIcc u v
  have hA : IsLqMultiplierBound (ENNReal.ofReal q)
      (fun ξ : ℝ => ∑ m ∈ Finset.range (K + 1), c m *
        (varphiNt (Nat.floor (a m)) 0 t ξ - varphiN (Nat.floor (a m)) 0 ξ)) C1 :=
    hC1 t ht a ha ha1 (Finset.range (K + 1)) c hcε
  have hB : IsLqMultiplierBound (ENNReal.ofReal q)
      (fun ξ : ℝ => ∑ m ∈ Finset.range (K + 1), r m * varphiN (Nat.floor (a m)) 0 ξ) C2 :=
    hC2 a ha (K + 1) r hIcc'
  have hintA : Integrable (fun ξ : ℝ => ∑ m ∈ Finset.range (K + 1), c m *
      (varphiNt (Nat.floor (a m)) 0 t ξ - varphiN (Nat.floor (a m)) 0 ξ))
      (volume : Measure ℝ) := by
    have hmain : Integrable (fun ξ : ℝ => ∑ m ∈ Finset.range (K + 1),
        (c m * varphiNt (Nat.floor (a m)) 0 t ξ - c m * varphiN (Nat.floor (a m)) 0 ξ))
        (volume : Measure ℝ) := by
      refine integrable_finsetSum _ (fun m _ => ?_)
      have h1 : Integrable (fun ξ : ℝ => c m * varphiNt (Nat.floor (a m)) 0 t ξ)
          (volume : Measure ℝ) := lacBump_integrable_smul_varphiNt _ _ _ _
      have h2 : Integrable (fun ξ : ℝ => c m * varphiN (Nat.floor (a m)) 0 ξ)
          (volume : Measure ℝ) :=
        ((Work.A7.varphiN_integrable_measurable (Nat.floor (a m)) 0).1).const_mul (c m)
      exact h1.sub h2
    refine hmain.congr (Filter.Eventually.of_forall (fun ξ => ?_))
    exact Finset.sum_congr rfl (fun _ _ => by ring)
  have hintB : Integrable (fun ξ : ℝ => ∑ m ∈ Finset.range (K + 1),
      r m * varphiN (Nat.floor (a m)) 0 ξ) (volume : Measure ℝ) := by
    refine integrable_finsetSum _ (fun m _ => ?_)
    exact (((Work.A7.varphiN_integrable_measurable (Nat.floor (a m)) 0).1).const_mul (r m))
  have hsum := IsLqMultiplierBound.add (q := ENNReal.ofReal q)
    (by rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal (le_of_lt hq))
    (hintA.const_mul 2) hintB
    (IsLqMultiplierBound.const_mul_nat 2 hA) hB
  have heq : randSymb (smallSymbF ρ C₀ a l₁ l₂ 0 k₂ t) ε K
      = fun ξ : ℝ => (2 : ℂ) * (∑ m ∈ Finset.range (K + 1), c m *
          (varphiNt (Nat.floor (a m)) 0 t ξ - varphiN (Nat.floor (a m)) 0 ξ))
        + ∑ m ∈ Finset.range (K + 1), r m * varphiN (Nat.floor (a m)) 0 ξ := by
    rw [hcoeff]
    funext ξ
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun m _ => ?_)
    simp only [hc]
    ring
  rw [heq]
  exact hsum

/-! ## The uniform-in-the-exponent continuous bound -/

/-- **The continuous multiplier bound for the randomised cut-off, uniformly over the choice of the
truncation `K` and the signs, with the loss factor `(1 + k₁)`.** -/
theorem isLqMultiplierBound_randSymb (Λ : NNReal) (hΛ : 1 < Λ) (q : ℝ) (hq : 1 < q) :
    ∃ C : NNReal, 0 < C ∧
      ∀ (ρ : ℝ) (C₀ : ℕ) (a : ℕ → NNReal) (l₁ l₂ k₁ k₂ K : ℕ) (t : ℝ) (ε : ℕ → ℂ),
        PointwiseErgodicTheorems.Lacunary Λ a → (∀ n, 1 ≤ a n) →
        t ∈ Set.Icc (1/2 : ℝ) 1 → (∀ n, ‖ε n‖ ≤ 1) →
        IsLqMultiplierBound (ENNReal.ofReal q)
          (randSymb (smallSymbF ρ C₀ a l₁ l₂ k₁ k₂ t) ε K) (C * (1 + k₁)) := by
  obtain ⟨C1, hC1pos, hC1⟩ := isLqMultiplierBound_randSymb_k1pos Λ hΛ q hq
  obtain ⟨C0, hC0pos, hC0⟩ := isLqMultiplierBound_randSymb_k0 Λ hΛ q hq
  refine ⟨max C1 C0, lt_max_of_lt_left hC1pos, ?_⟩
  intro ρ C₀ a l₁ l₂ k₁ k₂ K t ε ha ha1 ht hε
  rcases Nat.eq_zero_or_pos k₁ with hk | hk
  · subst hk
    refine IsLqMultiplierBound.mono (hC0 ρ C₀ a l₁ l₂ k₂ K t ε ha ha1 ht hε) ?_
    simp
  · refine IsLqMultiplierBound.mono (hC1 ρ C₀ a l₁ l₂ k₁ k₂ K t ε ha ha1 hk ht hε) ?_
    exact mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)


/-! ## The scale-count arithmetic -/

/-- The scale count `uScale ρ L = ⌊2^{2ρL}⌋` dominates half of `2^{2ρL}`. -/
lemma rpow_two_le_two_uScale (ρ : ℝ) (hρ : 0 < ρ) (L : ℕ) :
    (2:ℝ) ^ (2 * ρ * (L:ℝ)) ≤ 2 * (Work.KMTAreas.A7.uScale ρ L : ℝ) := by
  have hdef : ((Work.KMTAreas.A7.uScale ρ L : ℕ) : ℝ)
      = (((⌊(2:ℝ) ^ (2 * ρ * (L:ℝ))⌋ : ℤ)).toNat : ℝ) := by
    rw [Work.KMTAreas.A7.uScale, Work.Analysis.EndVar.scaleCount]
    norm_num
  rw [hdef]
  set x : ℝ := (2:ℝ) ^ (2 * ρ * (L:ℝ)) with hx
  have hx1 : (1:ℝ) ≤ x := by
    rw [hx]
    exact Real.one_le_rpow (by norm_num) (by positivity)
  have hfl : (0:ℤ) ≤ ⌊x⌋ := Int.floor_nonneg.mpr (by linarith)
  have hnat : (((⌊x⌋ : ℤ)).toNat : ℝ) = ((⌊x⌋ : ℤ) : ℝ) := by
    have h : (((⌊x⌋ : ℤ)).toNat : ℤ) = ⌊x⌋ := Int.toNat_of_nonneg hfl
    exact_mod_cast h
  rw [hnat]
  have hle : x < ((⌊x⌋ : ℤ) : ℝ) + 1 := by
    have h := Int.lt_floor_add_one x
    push_cast at h
    linarith
  have h1 : (1:ℤ) ≤ ⌊x⌋ := Int.le_floor.mpr (by push_cast; linarith)
  have h2 : (1:ℝ) ≤ ((⌊x⌋ : ℤ) : ℝ) := by exact_mod_cast h1
  nlinarith [hle, h2]

/-! ## Extending the discrete `IWLqBound` to all sequences -/

/-- **Extension of an `IWLqBound` from finitely supported inputs to all of `ℓ^q`.**  For a
summable kernel this is Fatou's lemma driven by `eLpNorm_finite_bounded` (a finite `ℓ^q` function
on `ℤ` with counting measure is bounded). -/
theorem eLpNorm_iwConv_le_of_IWLqBound_all {A : Finset Work.Analysis.IonescuWainger.Circle}
    {Φ : Work.Analysis.IonescuWainger.Circle → ℂ} {q : ℝ} (hq : 1 < q) {C : NNReal}
    (hC : 0 < C)
    (hκ : Summable (fun j : ℤ => ‖Work.Analysis.IWMultiplier.iwKernel
      (Work.Analysis.IonescuWainger.iwSymbolSet A Φ) j‖))
    (hb : Work.Analysis.IWMultiplier.IWLqBound A Φ (ENNReal.ofReal q) C) (f : ℤ → ℂ) :
    MeasureTheory.eLpNorm (Work.Analysis.IWMultiplier.iwConv A Φ f) (ENNReal.ofReal q)
        MeasureTheory.Measure.count
      ≤ ENNReal.ofReal (C : ℝ) * MeasureTheory.eLpNorm f (ENNReal.ofReal q)
          MeasureTheory.Measure.count := by
  by_cases htop : MeasureTheory.eLpNorm f (ENNReal.ofReal q) MeasureTheory.Measure.count = ⊤
  · rw [htop, ENNReal.mul_top]
    · exact le_top
    · exact ENNReal.ofReal_ne_zero_iff.mpr hC
  · have hq1 : (1 : ENNReal) ≤ ENNReal.ofReal q := by
      rw [← ENNReal.ofReal_one]
      exact ENNReal.ofReal_le_ofReal (le_of_lt hq)
    have hfin : MeasureTheory.eLpNorm f (ENNReal.ofReal q) MeasureTheory.Measure.count < ⊤ :=
      lt_top_iff_ne_top.mpr htop
    obtain ⟨B, hB⟩ := eLpNorm_finite_bounded (ENNReal.ofReal q) hq1 f hfin
    exact eLpNorm_iwConv_le_of_IWLqBoundScalar_of_bounded hq hκ
      (Work.Analysis.IWMultiplier.IWLqBound.scalar hb) ⟨B, hB⟩



/-! ## Summability of the IW kernel of the randomised cut-off -/

/-- **The IW kernel of the randomised cut-off is summable.**  The randomised symbol is a finite sum
of modulated bumps, so it is `C²` with compact support with explicit `L¹` bounds for itself and
its second derivative (`integral_norm_sum_bumps_le`); the kernel-decay estimate
`iwKernel_decay_of_bump` then dominates it by the summable weight `kmtKernWeight`. -/
theorem summable_iwKernel_randSymb (ρ : ℝ) (C₀ : ℕ) (a : ℕ → NNReal) (l₁ l₂ k₁ k₂ : ℕ)
    (t : ℝ) (ht : t ∈ Set.Icc (1/2 : ℝ) 1) (ε : ℕ → ℂ) (K : ℕ)
    (hε : ∀ n, ‖ε n‖ ≤ 1) (ha : Monotone a) :
    Summable (fun j : ℤ => ‖iwKernel (iwSymbolSet (diffFreqs ρ l₁)
      (periodize (randSymb (smallSymbF ρ C₀ a l₁ l₂ k₁ k₂ t) ε K))) j‖) := by
  classical
  obtain ⟨hcoeff, hnorm, -⟩ := randSymb_coeff_data ρ C₀ a l₁ l₂ k₁ k₂ t ε hε ha K
  set S₀ : ℝ := ∑ j ∈ Finset.range (K + 1), (bumpS (Nat.floor (a j)) k₁ + 1) with hS₀
  have hS₀0 : 0 ≤ S₀ := by
    rw [hS₀]
    exact Finset.sum_nonneg (fun m _ => by
      have hb := bumpS_nonneg (Nat.floor (a m)) k₁
      linarith)
  have hS₀big : ∀ m ∈ Finset.range (K + 1), bumpS (Nat.floor (a m)) k₁ ≤ S₀ := by
    intro m hm
    have h1 : bumpS (Nat.floor (a m)) k₁ + 1 ≤ S₀ := by
      rw [hS₀]
      exact Finset.single_le_sum (s := Finset.range (K + 1))
        (f := fun j => bumpS (Nat.floor (a j)) k₁ + 1)
        (fun i _ => by
          have hb := bumpS_nonneg (Nat.floor (a i)) k₁
          linarith) hm
    linarith
  have hbump : ∀ m ∈ Finset.range (K + 1),
      ContDiff ℝ 2 (fun ξ => varphiNt (Nat.floor (a m)) k₁ t ξ) ∧
      HasCompactSupport (fun ξ => varphiNt (Nat.floor (a m)) k₁ t ξ) ∧
      (∫ y, ‖varphiNt (Nat.floor (a m)) k₁ t y‖) ≤ S₀ ∧
      (∫ y, ‖iteratedDeriv 2 (fun ξ => varphiNt (Nat.floor (a m)) k₁ t ξ) y‖) ≤ S₀ := by
    intro m hm
    obtain ⟨hb1, hb2⟩ := bumpS_spec (Nat.floor (a m)) k₁ t ht
    exact ⟨contDiff_varphiNt _ _ t, hasCompactSupport_varphiNt _ _ t,
      hb1.trans (hS₀big m hm), hb2.trans (hS₀big m hm)⟩
  obtain ⟨hint1, hint2⟩ := integral_norm_sum_bumps_le (Finset.range (K + 1))
    (randCoeff ρ C₀ a l₁ l₂ k₁ k₂ ε K) (fun m ξ => varphiNt (Nat.floor (a m)) k₁ t ξ)
    S₀ hS₀0 hnorm hbump
  have hI1 : (∫ y, ‖randSymb (smallSymbF ρ C₀ a l₁ l₂ k₁ k₂ t) ε K y‖)
      ≤ 2 * S₀ * ((Finset.range (K + 1)).card : ℝ) := by
    have hEq : (∫ y, ‖randSymb (smallSymbF ρ C₀ a l₁ l₂ k₁ k₂ t) ε K y‖)
        = ∫ y, ‖∑ m ∈ Finset.range (K + 1),
            randCoeff ρ C₀ a l₁ l₂ k₁ k₂ ε K m * varphiNt (Nat.floor (a m)) k₁ t y‖ := by
      rw [hcoeff]
    rw [hEq]
    exact hint1
  have hI2 : (∫ y, ‖iteratedDeriv 2 (randSymb (smallSymbF ρ C₀ a l₁ l₂ k₁ k₂ t) ε K) y‖)
      ≤ 2 * S₀ * ((Finset.range (K + 1)).card : ℝ) := by
    have hEq : (∫ y, ‖iteratedDeriv 2 (randSymb (smallSymbF ρ C₀ a l₁ l₂ k₁ k₂ t) ε K) y‖)
        = ∫ y, ‖iteratedDeriv 2 (fun y => ∑ m ∈ Finset.range (K + 1),
            randCoeff ρ C₀ a l₁ l₂ k₁ k₂ ε K m * varphiNt (Nat.floor (a m)) k₁ t y) y‖ := by
      rw [hcoeff]
    rw [hEq]
    exact hint2
  have hch := randSymb_contDiff_hasCompactSupport ρ C₀ a l₁ l₂ k₁ k₂ t ε K
  have hSnn : (0 : ℝ) ≤ 2 * S₀ * ((Finset.range (K + 1)).card : ℝ) := by positivity
  have hdec := iwKernel_decay_of_bump (diffFreqs ρ l₁) hch.1 hch.2 hSnn hI1 hI2
  exact Summable.of_nonneg_of_le (fun j => norm_nonneg _) hdec
    (summable_kmtKernWeight.mul_left _)

/-! ## Arithmetic core of the good-major-arc case -/

/-- **Arithmetic core of the good-major-arc case.**  Two multiplier bounds, each of size
`cw * (1 + L) * mev`, are dominated by `C * W` as soon as `mev ≤ (ms + 1) * (1 + L)`,
`(1 + L) ^ 2 ≤ W` and `2 * cw * (ms + 1) ≤ C`. -/
lemma Tm_const_arith {cw ms mev ab₁ ab₂ W L C : ℝ}
    (hcw : 0 ≤ cw) (hms : 0 ≤ ms) (hmev : 0 ≤ mev) (hW1 : 1 ≤ W) (hL0 : 0 ≤ L)
    (hab₁ : ab₁ ≤ 1 + L) (hab₂ : ab₂ ≤ 1 + L)
    (hmevle : mev ≤ (ms + 1) * (1 + L))
    (hWsq : (1 + L) ^ (2 : ℝ) ≤ W)
    (hC : 2 * cw * (ms + 1) ≤ C) :
    cw * ab₁ * mev + cw * ab₂ * mev ≤ C * W := by
  have h1L : (0 : ℝ) ≤ 1 + L := by linarith
  have hstep : cw * ab₁ * mev + cw * ab₂ * mev
      ≤ 2 * (cw * (1 + L) * ((ms + 1) * (1 + L))) := by
    have hA : cw * ab₁ * mev ≤ cw * (1 + L) * ((ms + 1) * (1 + L)) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hab₁ hcw) hmevle hmev (mul_nonneg hcw h1L)
    have hB : cw * ab₂ * mev ≤ cw * (1 + L) * ((ms + 1) * (1 + L)) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hab₂ hcw) hmevle hmev (mul_nonneg hcw h1L)
    linarith
  have hkey : 2 * (cw * (1 + L) * ((ms + 1) * (1 + L)))
      = 2 * cw * (ms + 1) * ((1 + L) * (1 + L)) := by ring
  have hfin : 2 * cw * (ms + 1) * ((1 + L) * (1 + L)) ≤ C * W := by
    rw [show (1 + L) * (1 + L) = (1 + L) ^ (2 : ℝ) by rw [Real.rpow_two, pow_two]]
    have h2 : (0 : ℝ) ≤ 2 * cw * (ms + 1) :=
      mul_nonneg (mul_nonneg (by norm_num) hcw) (by linarith)
    calc 2 * cw * (ms + 1) * (1 + L) ^ (2 : ℝ)
        ≤ 2 * cw * (ms + 1) * W := mul_le_mul_of_nonneg_left hWsq h2
      _ ≤ C * W := mul_le_mul_of_nonneg_right hC (by linarith)
  linarith [hstep, hkey, hfin]

/-! ## The target -/

theorem randSymb_Tm_f_lp (P : Polynomial ℤ) (p₁ p₂ : ENNReal) (hdeg : 2 ≤ P.natDegree)
    (hA1 : Work.KMTContract.AreaA1) (hp₁ : 1 < p₁) (htp₁ : p₁ < ⊤) (hp₂ : 1 < p₂)
    (htp₂ : p₂ < ⊤) (hsum : p₁⁻¹ + p₂⁻¹ ≤ 1) :
    ∀ (C₀ : ℕ), 1 ≤ C₀ →
      ∃ A : ℝ, 0 ≤ A ∧ ∃ ρ₀ : ℝ, 0 < ρ₀ ∧ ∀ ρ : ℝ, 0 < ρ → ρ ≤ ρ₀ → ∃ C : NNReal → NNReal,
        ∀ (a : ℕ → NNReal) (Λ : NNReal) (l₁ l₂ k₁ k₂ K : ℕ) (t : ℝ) (ε : ℕ → ℂ) (f : ℤ → ℂ),
          1 < Λ → PointwiseErgodicTheorems.Lacunary Λ a → (∀ n, 1 ≤ a n) →
          (∀ n, ‖ε n‖ ≤ 1) → t ∈ Set.Icc ((1:ℝ)/2) 1 →
          MeasureTheory.eLpNorm (fun x : ℤ =>
              Work.KMTAreas.A7.Tm ρ l₁
                (Work.KMTAreas.A7.randSymb (Work.KMTAreas.A7.smallSymbF ρ C₀ a l₁ l₂ k₁ k₂ t) ε K) f x)
            p₁ MeasureTheory.Measure.count
          ≤ (C Λ : ENNReal) *
              ENNReal.ofReal ((1 + Work.KMTAreas.A7.lmaxR l₁ l₂ k₁ k₂) ^ A *
                (2 : ℝ) ^ (A * ρ * Work.KMTAreas.A7.lmaxR l₁ l₂ k₁ k₂)) *
              MeasureTheory.eLpNorm f p₁ MeasureTheory.Measure.count := by
  intro C₀ hC₀
  set p : ℝ := p₁.toReal with hpdef
  have hp1 : 1 < p := by
    rw [hpdef]
    have h := (ENNReal.toReal_lt_toReal ENNReal.one_ne_top htp₁.ne).mpr hp₁
    simpa [ENNReal.toReal_one] using h
  obtain ⟨Kend, hKend2, hKendp, hKendp'⟩ := Work.KMTAreas.A7.exists_endpoint_exponent p hp1
  have hKendmax : max p (p / (p - 1)) ≤ 2 * (Kend : ℝ) := max_le hKendp hKendp'
  refine ⟨8, by norm_num, ?_⟩
  refine ⟨min (1 / 2) (1 / (4 * (C₀ : ℝ))), lt_min (by norm_num) (by positivity), ?_⟩
  intro ρ hρ hρle
  have hρ1 : ρ ≤ 1 := le_trans hρle (le_trans (min_le_left _ _) (by norm_num))
  have hρ4 : ρ ≤ 1 / (4 * (C₀ : ℝ)) := le_trans hρle (min_le_right _ _)
  obtain ⟨CρA, hCρApos, Cw, hCwpos, hCw⟩ :=
    Work.KMTAreas.A7rand.iwLqBound_of_even_continuous hA1 p hp1 ρ hρ hρ1
  obtain ⟨Bcase, hBcase⟩ :=
    Work.KMTAreas.A7rand.smallCond_not_narrow_bounded C₀ hC₀ ρ hρ hρ4
  set Blog : ℕ := Nat.ceil (Real.logb 2 CρA / ρ) + 1 with hBlog
  set Btot : ℕ := max Bcase Blog with hBtot
  obtain ⟨Ccrude, hCcrude⟩ :=
    Work.KMTAreas.A7rand.Tm_randSymb_crude_bound p hp1 ρ hρ C₀ Btot
  -- the parameter-free uniform multiplier bound, one for each pair `(Λ, k₀)`
  have hex_q : ∀ (Λ : NNReal), 1 < Λ → ∀ (k₀ : ℕ), 1 < (2 * (k₀ : ℝ)) → ∃ C : NNReal,
      ∀ (ρ : ℝ) (C₀ : ℕ) (a : ℕ → NNReal) (l₁ l₂ k₁ k₂ K : ℕ) (t : ℝ) (ε : ℕ → ℂ),
        PointwiseErgodicTheorems.Lacunary Λ a → (∀ n, 1 ≤ a n) →
        t ∈ Set.Icc (1/2 : ℝ) 1 → (∀ n, ‖ε n‖ ≤ 1) →
        IsLqMultiplierBound (ENNReal.ofReal (2 * (k₀ : ℝ)))
          (randSymb (smallSymbF ρ C₀ a l₁ l₂ k₁ k₂ t) ε K) (C * (1 + (k₁ : NNReal))) := by
    intro Λ hΛ k₀ hk
    obtain ⟨C, -, hC⟩ := isLqMultiplierBound_randSymb Λ hΛ (2 * (k₀ : ℝ)) hk
    exact ⟨C, fun ρ C₀ a l₁ l₂ k₁ k₂ K t ε ha ha1 ht hε =>
      hC ρ C₀ a l₁ l₂ k₁ k₂ K t ε ha ha1 ht hε⟩
  let Cbfun : NNReal → ℕ → NNReal := fun Λ k₀ =>
    if hΛ : 1 < Λ then
      (if hk : 1 < (2 * (k₀ : ℝ)) then
        Classical.choose (α := NNReal) (hex_q Λ hΛ k₀ hk) else 1)
    else 1
  let Csup : NNReal → NNReal := fun Λ => (Finset.Icc 2 Kend).sup (Cbfun Λ)
  have hCbspec : ∀ (Λ : NNReal) (hΛ : 1 < Λ) (k₀ : ℕ) (hk : 1 < (2 * (k₀ : ℝ)))
      (ρ : ℝ) (C₀ : ℕ) (a : ℕ → NNReal) (l₁ l₂ k₁ k₂ K : ℕ) (t : ℝ) (ε : ℕ → ℂ),
      PointwiseErgodicTheorems.Lacunary Λ a → (∀ n, 1 ≤ a n) →
      t ∈ Set.Icc (1/2 : ℝ) 1 → (∀ n, ‖ε n‖ ≤ 1) →
      IsLqMultiplierBound (ENNReal.ofReal (2 * (k₀ : ℝ)))
        (randSymb (smallSymbF ρ C₀ a l₁ l₂ k₁ k₂ t) ε K) (Cbfun Λ k₀ * (1 + (k₁ : NNReal))) := by
    intro Λ hΛ k₀ hk ρ C₀ a l₁ l₂ k₁ k₂ K t ε ha ha1 ht hε
    have hval : Cbfun Λ k₀ = Classical.choose (α := NNReal) (hex_q Λ hΛ k₀ hk) := by
      simp only [Cbfun, dif_pos hΛ, dif_pos hk]
    rw [hval]
    exact Classical.choose_spec (α := NNReal) (hex_q Λ hΛ k₀ hk) ρ C₀ a l₁ l₂ k₁ k₂ K t ε
      ha ha1 ht hε
  set Cconst : NNReal → NNReal := fun Λ => 8 * Cw * (Csup Λ + 1) + Ccrude Λ + 1 with hCconst_def
  refine ⟨Cconst, ?_⟩
  intro a Λ l₁ l₂ k₁ k₂ K t ε f hΛ ha ha1 hε ht
  set L : ℕ := Work.KMTAreas.A7.smallL l₁ l₂ k₁ k₂ with hL
  set u : ℕ := Work.KMTAreas.A7.uScale ρ L with hu
  set W : ℝ := (1 + (L : ℝ)) ^ (8 : ℝ) * (2 : ℝ) ^ (8 * ρ * (L : ℝ)) with hW
  have hLC : (0 : ℝ) ≤ (L : ℝ) := Nat.cast_nonneg L
  have h1LC : (1 : ℝ) ≤ 1 + (L : ℝ) := by linarith
  have h8L : (0 : ℝ) ≤ 8 * ρ * (L : ℝ) :=
    mul_nonneg (mul_nonneg (by norm_num) (le_of_lt hρ)) hLC
  have hpow8 : (0 : ℝ) ≤ (1 + (L : ℝ)) ^ (8 : ℝ) := Real.rpow_nonneg (by linarith) 8
  have hW1 : 1 ≤ W := by
    rw [hW]
    have h1 : (1 : ℝ) ≤ (1 + (L : ℝ)) ^ (8 : ℝ) := Real.one_le_rpow h1LC (by norm_num)
    have h2 : (1 : ℝ) ≤ (2 : ℝ) ^ (8 * ρ * (L : ℝ)) := Real.one_le_rpow (by norm_num) h8L
    calc (1 : ℝ) = 1 * 1 := (one_mul 1).symm
      _ ≤ _ := mul_le_mul h1 h2 (by norm_num) hpow8
  have hWsq : (1 + (L : ℝ)) ^ (2 : ℝ) ≤ W := by
    rw [hW]
    have h2 : (1 : ℝ) ≤ (2 : ℝ) ^ (8 * ρ * (L : ℝ)) := Real.one_le_rpow (by norm_num) h8L
    calc (1 + (L : ℝ)) ^ (2 : ℝ) ≤ (1 + (L : ℝ)) ^ (8 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le h1LC (by norm_num)
      _ = (1 + (L : ℝ)) ^ (8 : ℝ) * 1 := (mul_one _).symm
      _ ≤ (1 + (L : ℝ)) ^ (8 : ℝ) * (2 : ℝ) ^ (8 * ρ * (L : ℝ)) :=
          mul_le_mul_of_nonneg_left h2 hpow8
  have hLr : Work.KMTAreas.A7.lmaxR l₁ l₂ k₁ k₂ = (L : ℝ) := by
    rw [hL, Work.KMTAreas.A7.lmaxR, Work.Analysis.EndVar.lmax, Work.KMTAreas.A7.smallL]
    push_cast
    rfl
  have hgoalW : ENNReal.ofReal ((1 + Work.KMTAreas.A7.lmaxR l₁ l₂ k₁ k₂) ^ (8 : ℝ) *
      (2 : ℝ) ^ ((8 : ℝ) * ρ * Work.KMTAreas.A7.lmaxR l₁ l₂ k₁ k₂)) = ENNReal.ofReal W := by
    congr 1
    rw [hLr, hW]
  by_cases hcase : (∀ m : ℕ, Work.KMTAreas.A7.smallCond ρ C₀ a l₁ l₂ k₁ k₂ m →
        (2 : ℝ) ^ ((k₁ : ℤ) - Work.Analysis.EndVar.logN (Nat.floor (a m))) ≤
          (2 : ℝ) ^ (-((2 * u : ℕ) : ℤ)))
      ∧ CρA * (2 : ℝ) ^ (ρ * (l₁ : ℝ)) ≤ 2 * (u : ℝ)
  · -- ### the good (narrow support) case
    have hsupp : ∀ m : ℕ, Work.KMTAreas.A7.smallCond ρ C₀ a l₁ l₂ k₁ k₂ m →
        (2 : ℝ) ^ ((k₁ : ℤ) - Work.Analysis.EndVar.logN (Nat.floor (a m))) ≤
          (2 : ℝ) ^ (-((2 * u : ℕ) : ℤ)) := hcase.1
    have hgood : GoodMajorArcs ρ CρA l₁ (-((2 * u : ℕ) : ℤ)) := by
      rw [GoodMajorArcs]
      have hcast : (((-(2 * u : ℕ) : ℤ)) : ℝ) = -(2 * (u : ℝ)) := by push_cast; ring
      rw [hcast]
      linarith [hcase.2]
    obtain ⟨Φ, hΦ⟩ := randSymb_schwartz ρ C₀ a l₁ l₂ k₁ k₂ t ε K
    have hΦsupp : ∀ x : ℝ, Φ x ≠ 0 → x ∈ realArc (-((2 * u : ℕ) : ℤ)) := by
      intro x hx
      have h2 : |x| ≤ (2 : ℝ) ^ (-((2 * u : ℕ) : ℤ)) :=
        randSymb_support_le ρ C₀ a l₁ l₂ k₁ k₂ t ε K ((2 : ℝ) ^ (-((2 * u : ℕ) : ℤ)))
          hsupp x (fun h => hx (by rw [hΦ]; exact h))
      rw [realArc]
      exact abs_le.mp h2
    set Mev : NNReal := Csup Λ * (1 + (k₁ : NNReal)) + 1 with hMev
    have hmev_spec : ∀ k₀ : ℕ, 2 ≤ k₀ → k₀ ≤ Kend →
        IsLqMultiplierBound (ENNReal.ofReal ((2 * k₀ : ℕ) : ℝ)) (fun ξ : ℝ => Φ ξ) Mev := by
      intro k₀ hk2 hkK
      have hk1 : 1 < (2 * (k₀ : ℝ)) := by exact_mod_cast (by omega : 1 < 2 * k₀)
      have hle : Cbfun Λ k₀ ≤ Csup Λ := by
        show Cbfun Λ k₀ ≤ (Finset.Icc 2 Kend).sup (Cbfun Λ)
        exact Finset.le_sup (Finset.mem_Icc.mpr ⟨hk2, hkK⟩)
      have hexp : ENNReal.ofReal ((2 * k₀ : ℕ) : ℝ) = ENNReal.ofReal (2 * (k₀ : ℝ)) := by
        congr 1
        push_cast
        ring
      have hb : IsLqMultiplierBound (ENNReal.ofReal ((2 * k₀ : ℕ) : ℝ))
          (randSymb (smallSymbF ρ C₀ a l₁ l₂ k₁ k₂ t) ε K)
          (Cbfun Λ k₀ * (1 + (k₁ : NNReal))) := by
        rw [hexp]
        exact hCbspec Λ hΛ k₀ hk1 ρ C₀ a l₁ l₂ k₁ k₂ K t ε ha ha1 ht hε
      have hsym : (fun ξ : ℝ => Φ ξ) = randSymb (smallSymbF ρ C₀ a l₁ l₂ k₁ k₂ t) ε K := by
        rw [hΦ]
      rw [hsym]
      refine IsLqMultiplierBound.mono hb ?_
      rw [hMev]
      exact le_trans (mul_le_mul_of_nonneg_right hle (by positivity))
        (le_add_of_nonneg_right (show (0 : NNReal) ≤ 1 by norm_num))
    have hmev_star : ∀ k₀ : ℕ, 2 ≤ k₀ → k₀ ≤ Kend →
        IsLqMultiplierBound (ENNReal.ofReal ((2 * k₀ : ℕ) : ℝ)) (fun ξ : ℝ => star (Φ ξ)) Mev :=
      fun k₀ h1 h2 => IsLqMultiplierBound_star (hmev_spec k₀ h1 h2)
    have hb₁ := hCw l₁ (-((2 * u : ℕ) : ℤ)) hgood Φ hΦsupp Kend hKend2 hKendmax Mev
      hmev_spec hmev_star
    have hgood' : GoodMajorArcs ρ CρA (l₁ - 1) (-((2 * u : ℕ) : ℤ)) :=
      GoodMajorArcs.mono_l (le_of_lt hρ) (le_of_lt hCρApos) (Nat.pred_le l₁) hgood
    have hb₂ := hCw (l₁ - 1) (-((2 * u : ℕ) : ℤ)) hgood' Φ hΦsupp Kend hKend2 hKendmax Mev
      hmev_spec hmev_star
    have hq1 : (1 : ENNReal) < ENNReal.ofReal p := by
      rw [← ENNReal.ofReal_one]
      exact (ENNReal.ofReal_lt_ofReal_iff (by linarith : (0 : ℝ) < p)).mpr hp1
    have hb := IWLqBound_diffFreqs_of_arithFreqs ρ hρ hρ1 l₁ Φ hq1 hb₁ hb₂
    have hsumm : Summable (fun j : ℤ => ‖iwKernel
        (iwSymbolSet (diffFreqs ρ l₁) (periodize (Φ : ℝ → ℂ))) j‖) := by
      have h := summable_iwKernel_randSymb ρ C₀ a l₁ l₂ k₁ k₂ t ht ε K hε
        (monotone_of_lacunary hΛ ha ha1)
      rwa [← hΦ] at h
    have hCpos : (0 : NNReal) < Cw * angleBracket l₁ * Mev + Cw * angleBracket (l₁ - 1) * Mev := by
      have hM : (0 : NNReal) < Mev := by rw [hMev]; positivity
      have h1 : (0 : NNReal) < Cw * angleBracket l₁ * Mev :=
        mul_pos (mul_pos hCwpos (angleBracket_pos l₁)) hM
      exact lt_of_lt_of_le h1 (le_add_of_nonneg_right (by positivity))
    have hmain := eLpNorm_iwConv_le_of_IWLqBound_all (A := diffFreqs ρ l₁)
      (Φ := periodize (Φ : ℝ → ℂ)) hp1 hCpos hsumm hb f
    have hTm : Work.KMTAreas.A7.Tm ρ l₁
        (Work.KMTAreas.A7.randSymb (Work.KMTAreas.A7.smallSymbF ρ C₀ a l₁ l₂ k₁ k₂ t) ε K)
        = iwConv (diffFreqs ρ l₁) (periodize (Φ : ℝ → ℂ)) := by
      rw [← hΦ]
      rfl
    have hp' : p₁ = ENNReal.ofReal p := by
      rw [hpdef]
      exact (ENNReal.ofReal_toReal htp₁.ne).symm
    rw [hp', hTm, hgoalW]
    refine hmain.trans ?_
    refine mul_le_mul_of_nonneg_right ?_ zero_le
    -- the arithmetic: `W` absorbs the growth of the loss factor
    have hXeq : ((Cw * angleBracket l₁ * Mev + Cw * angleBracket (l₁ - 1) * Mev : NNReal) : ℝ)
        = (Cw : ℝ) * (angleBracket l₁ : ℝ) * (Mev : ℝ)
          + (Cw : ℝ) * (angleBracket (l₁ - 1) : ℝ) * (Mev : ℝ) := by
      push_cast
      ring
    have hAb1 : (angleBracket l₁ : ℝ) ≤ 1 + (L : ℝ) := by
      have h : l₁ ≤ L := by
        rw [hL, Work.KMTAreas.A7.smallL]
        exact le_trans (le_max_left l₁ l₂) (le_max_left _ _)
      have h2 : angleBracket l₁ ≤ (1 + L : NNReal) := by
        rw [angleBracket]
        refine max_le ?_ ?_
        · exact le_add_of_nonneg_right (by positivity)
        · calc (l₁ : NNReal) ≤ (L : NNReal) := by exact_mod_cast h
            _ ≤ 1 + (L : NNReal) := le_add_of_nonneg_left (by positivity)
      have h3 : (angleBracket l₁ : ℝ) ≤ ((1 + L : NNReal) : ℝ) := by exact_mod_cast h2
      push_cast at h3
      exact h3
    have hAb2 : (angleBracket (l₁ - 1) : ℝ) ≤ 1 + (L : ℝ) := by
      refine le_trans ?_ hAb1
      have h : angleBracket (l₁ - 1) ≤ angleBracket l₁ := by
        rw [angleBracket, angleBracket]
        exact_mod_cast (max_le_max le_rfl (Nat.pred_le l₁))
      exact_mod_cast h
    have hmevle : (Mev : ℝ) ≤ ((Csup Λ : ℝ) + 1) * (1 + (L : ℝ)) := by
      have hMevval : (Mev : ℝ) = (Csup Λ : ℝ) * (1 + (k₁ : ℝ)) + 1 := by
        rw [hMev]
        push_cast
        ring
      rw [hMevval]
      have hk1L : (1 : ℝ) + (k₁ : ℝ) ≤ 1 + (L : ℝ) := by
        have h : k₁ ≤ L := by
          rw [hL, Work.KMTAreas.A7.smallL]
          exact le_trans (le_max_left k₁ k₂) (le_max_right _ _)
        exact_mod_cast (by omega : 1 + k₁ ≤ 1 + L)
      have hcs0 : (0 : ℝ) ≤ (Csup Λ : ℝ) := by positivity
      have hstep1 : (Csup Λ : ℝ) * (1 + (k₁ : ℝ)) ≤ (Csup Λ : ℝ) * (1 + (L : ℝ)) :=
        mul_le_mul_of_nonneg_left hk1L hcs0
      have hstep2 : (1 : ℝ) ≤ 1 + (L : ℝ) := h1LC
      calc (Csup Λ : ℝ) * (1 + (k₁ : ℝ)) + 1
          ≤ (Csup Λ : ℝ) * (1 + (L : ℝ)) + (1 + (L : ℝ)) := by linarith [hstep1, hstep2]
        _ = ((Csup Λ : ℝ) + 1) * (1 + (L : ℝ)) := by ring
    have hCconst : 2 * (Cw : ℝ) * ((Csup Λ : ℝ) + 1) ≤ (Cconst Λ : ℝ) := by
      have hcast : (Cconst Λ : ℝ)
          = 8 * (Cw : ℝ) * ((Csup Λ : ℝ) + 1) + (Ccrude Λ : ℝ) + 1 := by
        simp only [hCconst_def]
        push_cast
        ring
      rw [hcast]
      have h5 : (0 : ℝ) ≤ (Cw : ℝ) * ((Csup Λ : ℝ) + 1) := by positivity
      have h4 : 2 * (Cw : ℝ) * ((Csup Λ : ℝ) + 1)
          ≤ 8 * (Cw : ℝ) * ((Csup Λ : ℝ) + 1) := by nlinarith [h5]
      have h6 : (0 : ℝ) ≤ (Ccrude Λ : ℝ) + 1 := by positivity
      linarith [h4, h6]
    have harith := Tm_const_arith (cw := (Cw : ℝ)) (ms := (Csup Λ : ℝ)) (mev := (Mev : ℝ))
      (ab₁ := (angleBracket l₁ : ℝ)) (ab₂ := (angleBracket (l₁ - 1) : ℝ))
      (W := W) (L := (L : ℝ)) (C := (Cconst Λ : ℝ))
      (by positivity) (by positivity) (by positivity) hW1 (Nat.cast_nonneg L)
      hAb1 hAb2 hmevle hWsq hCconst
    rw [hXeq]
    have hgoal : ENNReal.ofReal ((Cconst Λ : ℝ) * W)
        = (Cconst Λ : ENNReal) * ENNReal.ofReal W := by
      rw [ENNReal.ofReal_mul (NNReal.coe_nonneg _), ENNReal.ofReal_coe_nnreal]
    rw [← hgoal]
    exact ENNReal.ofReal_le_ofReal harith
  · -- ### the crude case: one of the two structural bounds fails
    have hLb : L ≤ Btot := by
      rw [not_and_or] at hcase
      rcases hcase with hcase | hcase
      · push_neg at hcase
        obtain ⟨m, hm, hm'⟩ := hcase
        have h1 : ¬ (k₁ + 2 * u ≤ (Work.Analysis.EndVar.logN (Nat.floor (a m))).toNat) := by
          intro hcon
          refine (not_le.mpr hm') ?_
          rw [zpow_le_zpow_iff_right₀ (by norm_num : (1 : ℝ) < 2)]
          have hcast : ((Work.Analysis.EndVar.logN (Nat.floor (a m))).toNat : ℤ)
              = Work.Analysis.EndVar.logN (Nat.floor (a m)) :=
            Int.toNat_of_nonneg (Work.Analysis.EndVar.logN_nonneg _)
          have h2 : ((k₁ + 2 * u : ℕ) : ℤ)
              ≤ Work.Analysis.EndVar.logN (Nat.floor (a m)) := by
            rw [← hcast]
            exact_mod_cast hcon
          have h2' : (k₁ : ℤ) + 2 * (u : ℤ)
              ≤ Work.Analysis.EndVar.logN (Nat.floor (a m)) := by
            calc (k₁ : ℤ) + 2 * (u : ℤ) = ((k₁ + 2 * u : ℕ) : ℤ) := by push_cast; ring
              _ ≤ _ := h2
          push_cast
          omega
        have hsmall := (hBcase a l₁ l₂ k₁ k₂ m hm h1).2
        rw [hL]
        exact le_trans hsmall (le_max_left _ _)
      · rw [not_le] at hcase
        have hle : (l₁ : ℝ) ≤ (L : ℝ) := by
          rw [hL, Work.KMTAreas.A7.smallL]
          exact_mod_cast le_trans (le_max_left l₁ l₂) (le_max_left _ _)
        have h1 : (2 : ℝ) ^ (2 * ρ * (L : ℝ)) < CρA * (2 : ℝ) ^ (ρ * (l₁ : ℝ)) :=
          lt_of_le_of_lt (rpow_two_le_two_uScale ρ hρ L) hcase
        have h2 : (2 : ℝ) ^ (2 * ρ * (L : ℝ)) < CρA * (2 : ℝ) ^ (ρ * (L : ℝ)) := by
          refine h1.trans_le ?_
          exact mul_le_mul_of_nonneg_left
            (Real.rpow_le_rpow_of_exponent_le (by norm_num) (by nlinarith))
            (le_of_lt hCρApos)
        have hpos : (0 : ℝ) < (2 : ℝ) ^ (ρ * (L : ℝ)) := Real.rpow_pos_of_pos (by norm_num) _
        have hmul : (2 : ℝ) ^ (2 * ρ * (L : ℝ))
            = ((2 : ℝ) ^ (ρ * (L : ℝ))) ^ (2 : ℝ) := by
          rw [← Real.rpow_mul (by norm_num)]
          congr 1
          ring
        have h3 : (2 : ℝ) ^ (ρ * (L : ℝ)) < CρA := by
          rw [hmul, Real.rpow_two] at h2
          by_contra hcon
          push_neg at hcon
          have h4 : CρA * (2 : ℝ) ^ (ρ * (L : ℝ))
              ≤ (2 : ℝ) ^ (ρ * (L : ℝ)) * (2 : ℝ) ^ (ρ * (L : ℝ)) :=
            mul_le_mul_of_nonneg_right hcon (le_of_lt hpos)
          linarith [h2, h4]
        have h4 : ρ * (L : ℝ) < Real.logb 2 CρA := by
          have h5 : Real.logb 2 ((2 : ℝ) ^ (ρ * (L : ℝ))) < Real.logb 2 CρA :=
            Real.logb_lt_logb (by norm_num : (1 : ℝ) < 2)
              (Real.rpow_pos_of_pos (by norm_num) _) h3
          rwa [Real.logb_rpow (b := 2) (by norm_num) (by norm_num)] at h5
        have h6 : (L : ℝ) < Real.logb 2 CρA / ρ := by
          rw [lt_div_iff₀ hρ]
          linarith
        have h7 : L ≤ Nat.ceil (Real.logb 2 CρA / ρ) := by
          have h7' : (L : ℝ) ≤ (Nat.ceil (Real.logb 2 CρA / ρ) : ℝ) :=
            le_trans h6.le (Nat.le_ceil _)
          exact_mod_cast h7'
        have h8 : L ≤ Blog := by
          rw [hBlog]
          omega
        rw [hBtot]
        exact le_trans h8 (le_max_right _ _)
    have hcr := hCcrude Λ a l₁ l₂ k₁ k₂ K t ε f hΛ ha ha1 hLb ht hε
    have hp' : p₁ = ENNReal.ofReal p := by
      rw [hpdef]
      exact (ENNReal.ofReal_toReal htp₁.ne).symm
    rw [hp', hgoalW]
    refine hcr.trans ?_
    refine mul_le_mul_of_nonneg_right ?_ zero_le
    have h1 : Ccrude Λ ≤ Cconst Λ := by
      have h2 : Ccrude Λ ≤ 8 * Cw * (Csup Λ + 1) + Ccrude Λ :=
        le_add_of_nonneg_left (by positivity)
      have h3 : 8 * Cw * (Csup Λ + 1) + Ccrude Λ
          ≤ 8 * Cw * (Csup Λ + 1) + Ccrude Λ + 1 :=
        le_add_of_nonneg_right (by positivity)
      exact le_trans h2 h3
    calc (Ccrude Λ : ENNReal)
        ≤ (Cconst Λ : ENNReal) := by exact_mod_cast h1
      _ = (Cconst Λ : ENNReal) * 1 := (mul_one _).symm
      _ ≤ (Cconst Λ : ENNReal) * ENNReal.ofReal W := by
          refine mul_le_mul_of_nonneg_left ?_ zero_le
          rw [← ENNReal.ofReal_one]
          exact ENNReal.ofReal_le_ofReal hW1

end

end Work.KMTAreas.A7
