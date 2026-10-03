/-
# Glue lemmas for the linear lacunary variational estimate (`Work.KMTAreas.A7.lacunaryBumpVarEstimate`)

This module assembles the elementary wiring of the target `lacunaryBumpVarEstimate`:

* `iwConv_sdiff_of_bounded` — additivity of `iwConv` in the *frequency set* (set difference);
* `Tex_eq_Tle_sub_of_bounded` — the exact-height multiplier `Tex ρ l` is the difference of the two
  height-`≤` multipliers `Tle ρ l` and `Tle ρ (l-1)` (for bounded input and `l ≥ 1`);
* `Tle_zero_sym`, `Tle_const_mul`, `Tle_ite` — linearity of `Tle` in the symbol;
* `varphiNt_mem_realArc` — the Farey/narrowness bridge: if `k₁ - Log N ≤ k` then the support of the
  modulated bump `varphiNt N k₁ t` lies in the narrow arc `realArc k`;
* `multBound_varphiNt_two_endpoints` / `multBound_varphiNt_diff_two_endpoints` — the two-endpoint
  continuous multiplier bounds for the signed sums of the modulated bumps of height `k₁ ≥ 1`
  (`lacunaryBump_mult_bound_k1pos`) and of the low-frequency differences at `k₁ = 0`
  (`lacunaryBump_mult_bound_k0_diff`), in the exact shape required by
  `Work.KMTAreas.A7.varEst_of_narrow_symbols_twoEndpoints`.
-/
import Mathlib
import Submission.Work.KMTAreas.A7.adm_of_bump
import Submission.Work.KMTAreas.A7.varEst_of_narrow_symbols_twoEndpoints
import Submission.Work.KMTAreas.A7.Tle_varphiNt_single_scale
import Submission.Work.KMTAreas.A7.randSymb_Tm_f_lp

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.KMTAreas.A7

noncomputable section

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal BigOperators
open PointwiseErgodicTheorems Submission.PointwiseErgodicTheorems
open Work.Analysis.IonescuWainger Work.Analysis.IWMultiplier
open Work.KMTContract Work.Analysis.EndVar

local notation "Circ" => Work.Analysis.IonescuWainger.Circle

/-! ## §1. Set-difference additivity of `iwConv` -/

/-- **Additivity of `iwConv` in the frequency set**, for bounded input: for `B ⊆ A`,
`iwConv (A \ B) Φ f = iwConv A Φ f - iwConv B Φ f` whenever the two IW symbols are integrable and
their kernels are in `ℓ¹`.  The proof is the `tsum`-level version of the pointwise kernel identity
`iwKernel_iwSymbolSet_sdiff`; the boundedness of `f` is what makes the `tsum`s absolutely
convergent, hence additive. -/
theorem iwConv_sdiff_of_bounded {A B : Finset Circ} (hsub : B ⊆ A)
    {Φ : Circ → ℂ} (hA : Integrable (iwSymbolSet A Φ) circleMeasure)
    (hB : Integrable (iwSymbolSet B Φ) circleMeasure)
    {f : ℤ → ℂ} {Bnd : ℝ} (hf : ∀ m : ℤ, ‖f m‖ ≤ Bnd)
    (hκA : Summable fun j : ℤ => ‖iwKernel (iwSymbolSet A Φ) j‖)
    (hκB : Summable fun j : ℤ => ‖iwKernel (iwSymbolSet B Φ) j‖) :
    iwConv (A \ B) Φ f = iwConv A Φ f - iwConv B Φ f := by
  funext n
  simp only [iwConv_apply, Pi.sub_apply]
  have hz : ∀ j : ℤ, ‖f (n - j)‖ ≤ Bnd := fun j => hf _
  have hs1 : Summable fun j : ℤ => iwKernel (iwSymbolSet A Φ) j • f (n - j) :=
    summable_mul_of_bounded hκA hz
  have hs2 : Summable fun j : ℤ => iwKernel (iwSymbolSet B Φ) j • f (n - j) :=
    summable_mul_of_bounded hκB hz
  rw [← hs1.tsum_sub hs2]
  refine tsum_congr (fun j => ?_)
  rw [iwKernel_iwSymbolSet_sdiff hsub hA hB j, sub_smul]

/-- **The exact-height multiplier is a difference of two height-`≤` multipliers**, for bounded input
and `1 ≤ l`.  This is the bridge that lets every estimate proved for the `Tle`-families (in
particular `varEst_of_narrow_symbols_twoEndpoints`) be applied to the exact-height family `Tex`
that occurs in `Hcl`. -/
theorem Tex_eq_Tle_sub_of_bounded (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) {l : ℕ} (_hl : 1 ≤ l)
    {φ : ℝ → ℂ} (hAdm : Adm (iwArithFreqs ρ l) φ) (hAdm' : Adm (iwArithFreqs ρ (l - 1)) φ)
    {f : ℤ → ℂ} {Bnd : ℝ} (hf : ∀ m : ℤ, ‖f m‖ ≤ Bnd) :
    Tex ρ l φ f = Tle ρ l φ f - Tle ρ (l - 1) φ f := by
  have hsub : iwArithFreqs ρ (l - 1) ⊆ iwArithFreqs ρ l :=
    iwArithFreqs_mono hρ hρ1 (Nat.pred_le l)
  have hmain := iwConv_sdiff_of_bounded hsub hAdm.2.1 hAdm'.2.1 hf hAdm.2.2 hAdm'.2.2
  simpa only [Tex, Tle, iwArithFreqsNew] using hmain

/-! ## §2. Linearity of `Tle` in the symbol -/

/-- `Tle` of the zero symbol is the zero sequence. -/
theorem Tle_zero_sym (ρ : ℝ) (l : ℕ) (f : ℤ → ℂ) :
    Tle ρ l (fun _ : ℝ => (0 : ℂ)) f = 0 := by
  funext n
  simp only [Tle, iwConv_apply]
  simp [iwKernel, fourierCoeff, periodize]

/-- **Scalar linearity of `Tle` in the symbol** (needs no boundedness of `f`). -/
theorem Tle_const_mul (ρ : ℝ) (l : ℕ) (c : ℂ) {φ : ℝ → ℂ} {f : ℤ → ℂ} :
    Tle ρ l (fun ξ : ℝ => c * φ ξ) f = fun n : ℤ => c * Tle ρ l φ f n := by
  have hper : periodize (fun ξ : ℝ => c * φ ξ) = fun ξ : Circ => c * periodize φ ξ := by
    funext ξ
    simp only [periodize]
    exact tsum_mul_left
  simp only [Tle, hper]
  exact iwConv_const_mul c

/-- **`Tle` of a clipped symbol**: multiplying the symbol by the `0/1` function of a proposition
clips the resulting sequence. -/
theorem Tle_ite (ρ : ℝ) (l : ℕ) (c : Prop) [Decidable c] {φ : ℝ → ℂ} {f : ℤ → ℂ} :
    Tle ρ l (fun ξ : ℝ => if c then φ ξ else 0) f
      = fun n : ℤ => if c then Tle ρ l φ f n else 0 := by
  have hsym : (fun ξ : ℝ => if c then φ ξ else 0)
      = fun ξ : ℝ => (if c then (1 : ℂ) else 0) * φ ξ := by
    funext ξ
    by_cases h : c <;> simp [h]
  rw [hsym, Tle_const_mul]
  funext n
  by_cases h : c <;> simp [h]

/-! ## §3. The Farey/narrowness bridge -/

/-- **Narrowness of the modulated bump.**  If the height satisfies `k₁ - Log N ≤ k` then the support
of `varphiNt N k₁ t` is contained in the narrow arc `realArc k = ℝ_{≤ k}`, which is the hypothesis
`hnarrow` of `varEst_of_narrow_symbols_twoEndpoints`. -/
theorem varphiNt_mem_realArc (k₁ N : ℕ) (t : ℝ) {k : ℤ}
    (hk : (k₁ : ℤ) - (logN N : ℤ) ≤ k) {ξ : ℝ} (hξ : varphiNt N k₁ t ξ ≠ 0) :
    ξ ∈ realArc k := by
  have h1 : |ξ| ≤ (2 : ℝ) ^ ((k₁ : ℝ) - (logN N : ℝ)) := varphiNt_support_le_all k₁ N t ξ hξ
  have h3 : ((k₁ : ℤ) - (logN N : ℤ) : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  push_cast at h3
  have h2 : (2 : ℝ) ^ ((k₁ : ℝ) - (logN N : ℝ)) ≤ (2 : ℝ) ^ ((k : ℤ) : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) h3
  have h4 : |ξ| ≤ (2 : ℝ) ^ ((k : ℤ) : ℝ) := le_trans h1 h2
  rw [Real.rpow_intCast] at h4
  rw [realArc, Set.mem_Icc]
  exact ⟨by linarith [(abs_le.mp h4).1], (abs_le.mp h4).2⟩

/-! ## §4. The two-endpoint multiplier bounds for the signed sums of the bumps -/

/-- `ENNReal.ofReal 2 = 2`: the two notations for the even exponent `q = 2`. -/
theorem ofReal_two_eq : ENNReal.ofReal (2 : ℝ) = (2 : ENNReal) := by
  simp

/-- **The two-endpoint multiplier input at `k₁ ≥ 1`.**  For every pair of even exponents `2` and
`2k₀` (`k₀ ≥ 2`) the signed sums `∑_{n ∈ U} ω n · φ_{⌊a n⌋,t}` satisfy the continuous multiplier
bound with the *same* constant `C (1 + k₁)`, uniformly in `U`, in the signs `ω`, and in the lacunary
sequence `a`.  This is `lacunaryBump_mult_bound_k1pos` applied at the two exponents and combined with
`IsLqMultiplierBound.mono`. -/
theorem multBound_varphiNt_two_endpoints (Λ : NNReal) (hΛ : 1 < Λ) (k₀ : ℕ) (hk₀ : 2 ≤ k₀) :
    ∃ C : NNReal, 0 < C ∧ ∀ (k₁ : ℕ) (hk₁ : 1 ≤ k₁) (t : ℝ) (ht : t ∈ Set.Icc (1/2 : ℝ) 1)
      (a : ℕ → NNReal) (ha : PointwiseErgodicTheorems.Lacunary Λ a) (ha1 : ∀ n, 1 ≤ a n)
      (U : Finset ℕ) (ω : ℕ → Bool),
      IsLqMultiplierBound (ENNReal.ofReal (2 : ℝ))
          (fun ξ : ℝ => ∑ n ∈ U, (if ω n then (1 : ℂ) else -1) *
            varphiNt (Nat.floor (a n)) k₁ t ξ) (C * (1 + k₁)) ∧
        IsLqMultiplierBound (ENNReal.ofReal (2 * (k₀ : ℝ)))
          (fun ξ : ℝ => ∑ n ∈ U, (if ω n then (1 : ℂ) else -1) *
            varphiNt (Nat.floor (a n)) k₁ t ξ) (C * (1 + k₁)) := by
  have hk₀1 : (1 : ℝ) < 2 * (k₀ : ℝ) := by
    have h1 : (1 : ℝ) ≤ (k₀ : ℝ) := by exact_mod_cast (by omega : 1 ≤ k₀)
    linarith
  obtain ⟨C₂, hC₂pos, hC₂⟩ := lacunaryBump_mult_bound_k1pos 2 (by norm_num) Λ hΛ
  obtain ⟨Ce, hCepos, hCe⟩ := lacunaryBump_mult_bound_k1pos (2 * (k₀ : ℝ)) hk₀1 Λ hΛ
  refine ⟨max C₂ Ce, lt_max_of_lt_left hC₂pos, ?_⟩
  intro k₁ hk₁ t ht a ha ha1 U ω
  have hε : ∀ n : ℕ, ‖(if ω n then (1 : ℂ) else -1)‖ ≤ 1 := by
    intro n
    by_cases h : ω n <;> simp [h]
  have hnn : (0 : NNReal) ≤ (1 + (k₁ : NNReal)) := by positivity
  refine ⟨?_, ?_⟩
  · exact Work.KMTAreas.A7.IsLqMultiplierBound.mono (hC₂ k₁ hk₁ t ht a ha ha1 U _ hε)
      (mul_le_mul_of_nonneg_right (le_max_left _ _) hnn)
  · exact Work.KMTAreas.A7.IsLqMultiplierBound.mono (hCe k₁ hk₁ t ht a ha ha1 U _ hε)
      (mul_le_mul_of_nonneg_right (le_max_right _ _) hnn)

/-- **The two-endpoint multiplier input at `k₁ = 0` for the low-frequency difference.**  The signed
sums `∑_{n ∈ U} ω n · (φ_{⌊a n⌋,t} − φ_{⌊a n⌋})` (at the bottom height `k₁ = 0`) satisfy the
continuous multiplier bound at the two exponents `2` and `2k₀` with a common constant, uniformly in
`U`, in the signs, and in `t` and `a`.  This is `lacunaryBump_mult_bound_k0_diff` applied at the two
exponents. -/
theorem multBound_varphiNt_diff_two_endpoints (Λ : NNReal) (hΛ : 1 < Λ) (k₀ : ℕ) (hk₀ : 2 ≤ k₀) :
    ∃ C : NNReal, 0 < C ∧ ∀ (t : ℝ) (ht : t ∈ Set.Icc (1/2 : ℝ) 1)
      (a : ℕ → NNReal) (ha : PointwiseErgodicTheorems.Lacunary Λ a) (ha1 : ∀ n, 1 ≤ a n)
      (U : Finset ℕ) (ω : ℕ → Bool),
      IsLqMultiplierBound (ENNReal.ofReal (2 : ℝ))
          (fun ξ : ℝ => ∑ n ∈ U, (if ω n then (1 : ℂ) else -1) *
            (varphiNt (Nat.floor (a n)) 0 t ξ - varphiN (Nat.floor (a n)) 0 ξ)) C ∧
        IsLqMultiplierBound (ENNReal.ofReal (2 * (k₀ : ℝ)))
          (fun ξ : ℝ => ∑ n ∈ U, (if ω n then (1 : ℂ) else -1) *
            (varphiNt (Nat.floor (a n)) 0 t ξ - varphiN (Nat.floor (a n)) 0 ξ)) C := by
  have hk₀1 : (1 : ℝ) < 2 * (k₀ : ℝ) := by
    have h1 : (1 : ℝ) ≤ (k₀ : ℝ) := by exact_mod_cast (by omega : 1 ≤ k₀)
    linarith
  obtain ⟨C₂, hC₂pos, hC₂⟩ := lacunaryBump_mult_bound_k0_diff 2 (by norm_num) Λ hΛ
  obtain ⟨Ce, hCepos, hCe⟩ := lacunaryBump_mult_bound_k0_diff (2 * (k₀ : ℝ)) hk₀1 Λ hΛ
  refine ⟨max C₂ Ce, lt_max_of_lt_left hC₂pos, ?_⟩
  intro t ht a ha ha1 U ω
  have hε : ∀ n : ℕ, ‖(if ω n then (1 : ℂ) else -1)‖ ≤ 1 := by
    intro n
    by_cases h : ω n <;> simp [h]
  refine ⟨?_, ?_⟩
  · exact Work.KMTAreas.A7.IsLqMultiplierBound.mono (hC₂ t ht a ha ha1 U _ hε) (le_max_left _ _)
  · exact Work.KMTAreas.A7.IsLqMultiplierBound.mono (hCe t ht a ha ha1 U _ hε) (le_max_right _ _)

end

end Work.KMTAreas.A7
