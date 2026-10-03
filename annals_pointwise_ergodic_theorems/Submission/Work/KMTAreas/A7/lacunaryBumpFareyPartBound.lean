/-
# The Farey (narrow) part of the linear lacunary variational estimate (Area A7, §8)

This is a piece of the paper's (lin-1) (Krause–Mirek–Tao, Annals 195 (2022), §8) in the *discrete*
`ℓ^p(ℤ)` setting: the `r`-variation of the family of Ionescu–Wainger modulated bumps
`T^{≤l}_{φ_{N,t}} f`, restricted to the scales `n` which are simultaneously

* `core ρ C₀ l₁ l₂ k₁ k₂ a n` — admissible, above the large-scale cut `splitCut` and in the main
  regime of the functional calculus, and
* `Farey Cρc ρ l₁ k₁ a n` — *narrow at level* `fareyK Cρc ρ l₁`: `k₁ - Log ⌊a n⌋ ≤ ⌊-Cρc·2^{ρ l₁}⌋`,

is bounded on `ℓ^p(ℤ)` by `C (1 + l₁) (1 + k₁) ‖f‖_{ℓ^p}`, uniformly in the data.  This is the
regime in which the Ionescu–Wainger endpoint bound for *narrow* symbols (with its
`GoodMajorArcs ρ Cρ l (fareyK Cρc ρ l₁)`, `2^{fareyK} < 1/2`) applies.

Route (assembly of the workspace's A7 chapter):

* `Work.KMTAreas.A7.varEst_of_narrow_symbols_twoEndpoints` — the variational estimate for a family
  `Φ : ℕ → 𝒮(ℝ,ℂ)` supported in a single narrow arc `realArc k`, from the continuous multiplier
  bounds at the two exponents `2` and `2k₀` for all finite signed sums of the family;
* the family is realised as the Schwartz family `fareyClippedSch` (the bumped scale `varphiNtSch`
  where both conditions hold, `0` elsewhere), whose support is narrow by
  `Work.KMTAreas.A7.narrow_of_farey` (narrowness of `varphiNt` from the Farey condition) and whose
  narrowness constants are supplied by `Work.KMTAreas.A7.goodMajorArcs_fareyK` and
  `Work.KMTAreas.A7.two_rpow_fareyK_lt_half`;
* the multiplier bound is `Work.KMTAreas.A7.multBound_varphiNt_two_endpoints` — the two-endpoint
  shifted-Calderón–Zygmund bound `O(1 + k₁)` for the signed sums of the *unclipped* bumps, valid
  for every signed finite sum (`k₁ ≥ 1` is exactly the hypothesis of this module's target); clipping
  to a subset of the index set is an instance of that bound;
* the endpoint exponent `k₀` with `p.toReal ≤ 2k₀`, `p.toReal/(p.toReal-1) ≤ 2k₀` is
  `Work.KMTAreas.A7.exists_endpoint_exponent`.
-/
import Mathlib
import Submission.Work.KMTAreas.A7.lacunaryBumpAux
import Submission.Work.KMTAreas.A7.varphiNSch

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.KMTAreas.A7

noncomputable section

open MeasureTheory Finset
open scoped ENNReal NNReal BigOperators
open PointwiseErgodicTheorems Submission.PointwiseErgodicTheorems
open Work.Analysis.IonescuWainger Work.Analysis.IWMultiplier

/-! ## The Schwartz family clipped at the Farey scales -/

/-- The family of modulated bumps clipped at the core-and-Farey scales: the `n`-th member is the
Schwartz bump `varphiNtSch (⌊a n⌋) k₁ t` when `core ρ C₀ l₁ l₂ k₁ k₂ a n ∧ Farey Cρc ρ l₁ k₁ a n`,
and `0` otherwise. -/
noncomputable def fareyClippedSch (ρ : ℝ) (C₀ : ℕ) (a : ℕ → NNReal) (Cρc : ℝ)
    (l₁ l₂ k₁ k₂ : ℕ) (t : ℝ) (n : ℕ) : SchwartzMap ℝ ℂ :=
  if core ρ C₀ l₁ l₂ k₁ k₂ a n ∧ Farey Cρc ρ l₁ k₁ a n then
    varphiNtSch (Nat.floor (a n)) k₁ t else 0

/-- The value of the clipped family: the modulated bump where both conditions hold, and `0`
otherwise. -/
@[simp] lemma fareyClippedSch_apply (ρ : ℝ) (C₀ : ℕ) (a : ℕ → NNReal) (Cρc : ℝ)
    (l₁ l₂ k₁ k₂ : ℕ) (t : ℝ) (n : ℕ) (ξ : ℝ) :
    (fareyClippedSch ρ C₀ a Cρc l₁ l₂ k₁ k₂ t n : ℝ → ℂ) ξ
      = if core ρ C₀ l₁ l₂ k₁ k₂ a n ∧ Farey Cρc ρ l₁ k₁ a n then
          varphiNt (Nat.floor (a n)) k₁ t ξ else 0 := by
  rw [fareyClippedSch]
  by_cases h : core ρ C₀ l₁ l₂ k₁ k₂ a n ∧ Farey Cρc ρ l₁ k₁ a n
  · rw [if_pos h, if_pos h, varphiNtSch_apply]
  · rw [if_neg h, if_neg h]
    simp

/-- The clipped family as a family of functions. -/
@[simp] lemma fareyClippedSch_coe (ρ : ℝ) (C₀ : ℕ) (a : ℕ → NNReal) (Cρc : ℝ)
    (l₁ l₂ k₁ k₂ : ℕ) (t : ℝ) (n : ℕ) :
    (fareyClippedSch ρ C₀ a Cρc l₁ l₂ k₁ k₂ t n : ℝ → ℂ)
      = fun ξ : ℝ => if core ρ C₀ l₁ l₂ k₁ k₂ a n ∧ Farey Cρc ρ l₁ k₁ a n then
          varphiNt (Nat.floor (a n)) k₁ t ξ else 0 :=
  funext (fareyClippedSch_apply ρ C₀ a Cρc l₁ l₂ k₁ k₂ t n)

/-- **The Farey part of the linear lacunary variational estimate.**  There are constants `Cρc ≥ 3`
and `K > 0` — depending on `C₀`, `r`, `ρ`, `Λ`, `p` only — such that for every `k₁ ≥ 1`, every
`l ≤ l₁`, every `t ∈ [1/2,1]`, every `Λ`-lacunary family `a` with `a n ≥ 1`, and every
`f : ℤ → ℂ`, the `ℓ^p(ℤ)` norm of the `r`-variation of the family

  `n ↦ T^{≤l}_{1_{core ∧ Farey} · φ_{⌊a n⌋,t}} f`

is bounded by `K (1 + l₁) (1 + k₁) ‖f‖_{ℓ^p}`. -/
theorem lacunaryBumpFareyPartBound (C₀ : ℕ) (r : NNReal) (hr : 2 < r) (ρ : ℝ) (hρ : 0 < ρ)
    (hρ1 : ρ ≤ 1) (Λ : NNReal) (hΛ : 1 < Λ) (p : ENNReal) (hp : 1 < p) (hptop : p < ⊤) :
    ∃ Cρc : ℝ, 3 ≤ Cρc ∧ ∃ K : ℝ, 0 < K ∧
      ∀ (k₁ : ℕ) (hk₁ : 1 ≤ k₁) (l l₁ l₂ k₂ : ℕ) (hl : l ≤ l₁)
        (t : ℝ) (ht : t ∈ Set.Icc (1/2 : ℝ) 1)
        (a : ℕ → NNReal) (ha : PointwiseErgodicTheorems.Lacunary Λ a) (ha1 : ∀ n, 1 ≤ a n)
        (f : ℤ → ℂ),
        MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
          (fun n : ℕ => Work.KMTAreas.A7.Tle ρ l (fun ξ : ℝ =>
            if Work.KMTAreas.A7.core ρ C₀ l₁ l₂ k₁ k₂ a n ∧
              Work.KMTAreas.A7.Farey Cρc ρ l₁ k₁ a n
            then Work.KMTAreas.A7.varphiNt (Nat.floor (a n)) k₁ t ξ else 0) f x))
          p MeasureTheory.Measure.count
        ≤ ENNReal.ofReal (K * (1 + (l₁ : ℝ)) * (1 + (k₁ : ℝ))) *
            MeasureTheory.eLpNorm f p MeasureTheory.Measure.count := by
  classical
  -- ## The endpoint exponent `k₀ ≥ 2` covering `p` and its Hölder dual
  have hq1 : 1 < p.toReal := by
    rw [← ENNReal.toReal_one]
    exact (ENNReal.toReal_lt_toReal ENNReal.one_ne_top (ne_of_lt hptop)).mpr hp
  obtain ⟨k₀, hk₀, hpmax, hpd⟩ := exists_endpoint_exponent p.toReal hq1
  -- ## The two inputs: the narrow-symbol variational estimate, and the two-endpoint multiplier bound
  obtain ⟨Cρ, hCρpos, Kvar, hKvarpos, hmain⟩ :=
    varEst_of_narrow_symbols_twoEndpoints ρ hρ hρ1 r hr p hp hptop k₀ hk₀ hpmax hpd
  obtain ⟨C, hCpos, hCbound⟩ := multBound_varphiNt_two_endpoints Λ hΛ k₀ hk₀
  refine ⟨max 3 Cρ, le_max_left _ _, Kvar * (C : ℝ),
    mul_pos hKvarpos (by exact_mod_cast hCpos), ?_⟩
  intro k₁ hk₁ l l₁ l₂ k₂ hl t ht a ha ha1 f
  set Cc : ℝ := max 3 Cρ with hCcdef
  set M : NNReal := C * (1 + k₁) with hMdef
  have hCc3 : 3 ≤ Cc := by rw [hCcdef]; exact le_max_left _ _
  have hCc1 : 1 < Cc := lt_of_lt_of_le (by norm_num) hCc3
  have hCρle : Cρ ≤ Cc := by rw [hCcdef]; exact le_max_right _ _
  have hCρ0 : (0 : ℝ) ≤ Cρ := hCρpos.le
  have hMpos : 0 < M := by
    rw [hMdef]
    exact mul_pos hCpos
      (lt_of_lt_of_le (by norm_num) (le_add_of_nonneg_right (zero_le : (0 : NNReal) ≤ (k₁ : NNReal))))
  -- ## Narrowness of the clipped family
  have hnarrow : ∀ n ξ, (fareyClippedSch ρ C₀ a Cc l₁ l₂ k₁ k₂ t n : ℝ → ℂ) ξ ≠ 0 →
      ξ ∈ realArc (fareyK Cc ρ l₁) := by
    intro n ξ hξ
    have hξ' := hξ
    rw [fareyClippedSch_apply] at hξ'
    by_cases h : core ρ C₀ l₁ l₂ k₁ k₂ a n ∧ Farey Cc ρ l₁ k₁ a n
    · rw [if_pos h] at hξ'
      exact narrow_of_farey (t := t) h.2 ξ hξ'
    · rw [if_neg h] at hξ'
      exact absurd rfl hξ'
  -- ## The two-endpoint multiplier bound for the clipped family
  have hMult : ∀ (U : Finset ℕ) (ω : ℕ → Bool),
      IsLqMultiplierBound 2 (fun ξ : ℝ => ∑ n ∈ U, (if ω n then (1 : ℂ) else -1) *
          (fareyClippedSch ρ C₀ a Cc l₁ l₂ k₁ k₂ t n : ℝ → ℂ) ξ) M ∧
      IsLqMultiplierBound (ENNReal.ofReal (2 * (k₀ : ℝ)))
        (fun ξ : ℝ => ∑ n ∈ U, (if ω n then (1 : ℂ) else -1) *
          (fareyClippedSch ρ C₀ a Cc l₁ l₂ k₁ k₂ t n : ℝ → ℂ) ξ) M := by
    intro U ω
    have hU : (fun ξ : ℝ => ∑ n ∈ U, (if ω n then (1 : ℂ) else -1) *
          (fareyClippedSch ρ C₀ a Cc l₁ l₂ k₁ k₂ t n : ℝ → ℂ) ξ)
        = (fun ξ : ℝ =>
            ∑ n ∈ U.filter (fun n => core ρ C₀ l₁ l₂ k₁ k₂ a n ∧ Farey Cc ρ l₁ k₁ a n),
              (if ω n then (1 : ℂ) else -1) * varphiNt (Nat.floor (a n)) k₁ t ξ) := by
      funext ξ
      rw [Finset.sum_filter]
      refine Finset.sum_congr rfl (fun n _ => ?_)
      rw [fareyClippedSch_apply]
      by_cases h : core ρ C₀ l₁ l₂ k₁ k₂ a n ∧ Farey Cc ρ l₁ k₁ a n <;> simp [h]
    obtain ⟨hb2, hbe⟩ := hCbound k₁ hk₁ t ht a ha ha1
      (U.filter (fun n => core ρ C₀ l₁ l₂ k₁ k₂ a n ∧ Farey Cc ρ l₁ k₁ a n)) ω
    rw [ofReal_two_eq] at hb2
    exact ⟨by rw [hU]; exact hb2, by rw [hU]; exact hbe⟩
  -- ## The narrow-symbol variational estimate at the narrowness level `fareyK Cc ρ l₁`
  have hgood : GoodMajorArcs ρ Cρ l (fareyK Cc ρ l₁) :=
    goodMajorArcs_fareyK hCρle hCρ0 hρ.le hl
  have hk : (2 : ℝ) ^ (fareyK Cc ρ l₁) < 1 / 2 := two_rpow_fareyK_lt_half hCc1 hρ.le l₁
  have hres := hmain l (fareyK Cc ρ l₁) hgood hk M hMpos
    (fareyClippedSch ρ C₀ a Cc l₁ l₂ k₁ k₂ t) hnarrow hMult f
  -- ## Rewriting the clipped family back to the explicit `if`
  have hInt : (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
        (fun n : ℕ => Tle ρ l (fun ξ : ℝ =>
          if core ρ C₀ l₁ l₂ k₁ k₂ a n ∧ Farey Cc ρ l₁ k₁ a n
          then varphiNt (Nat.floor (a n)) k₁ t ξ else 0) f x))
      = (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
        (fun n : ℕ => Tle ρ l
          (fareyClippedSch ρ C₀ a Cc l₁ l₂ k₁ k₂ t n : ℝ → ℂ) f x)) := by
    funext x
    refine congrArg (fun u : ℕ → ℂ => PointwiseErgodicTheorems.variationalNorm r u) ?_
    funext n
    rw [fareyClippedSch_coe]
  rw [hInt]
  -- ## The constant bookkeeping
  refine hres.trans ?_
  refine mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal ?_) zero_le
  have hMR : (M : ℝ) = (C : ℝ) * (1 + (k₁ : ℝ)) := by
    rw [hMdef]; push_cast; ring
  have hlR : (1 + (l : ℝ)) ≤ (1 + (l₁ : ℝ)) := by
    have hl' : (l : ℝ) ≤ (l₁ : ℝ) := by exact_mod_cast hl
    linarith
  have hCnn : (0 : ℝ) ≤ (C : ℝ) := by positivity
  have hk₁nn : (0 : ℝ) ≤ 1 + (k₁ : ℝ) := by positivity
  have hnn : (0 : ℝ) ≤ Kvar * (C : ℝ) * (1 + (k₁ : ℝ)) :=
    mul_nonneg (mul_nonneg hKvarpos.le hCnn) hk₁nn
  calc Kvar * (1 + (l : ℝ)) * (M : ℝ)
      = Kvar * (C : ℝ) * (1 + (k₁ : ℝ)) * (1 + (l : ℝ)) := by rw [hMR]; ring
    _ ≤ Kvar * (C : ℝ) * (1 + (k₁ : ℝ)) * (1 + (l₁ : ℝ)) :=
        mul_le_mul_of_nonneg_left hlR hnn
    _ = Kvar * (C : ℝ) * (1 + (l₁ : ℝ)) * (1 + (k₁ : ℝ)) := by ring

end

end Work.KMTAreas.A7
