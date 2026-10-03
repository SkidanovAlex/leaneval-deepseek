/-
# `fareyModKC`: the Farey-clipped modulated lacunary variational estimate at height `l₁ = 0`

**Provenance.**  This file is a verbatim copy of the statement and proof of
`Work.KMTAreas.A7LoLin.fareyModK` (a lemma requested for `Work.KMTAreas.A7.LoLinVar`), with two
mechanical repairs of steps that did not compile in the original file:

* `rw [fareyOnlySch_apply]`  →  `rw [fareyOnlySch_coe]`  (the `_apply` lemma is pointwise, the
  goal needed the function-level identity);
* `simp only [] at hξ` after rewriting with `fareyOnlySchC_coe` (beta-reduction of the resulting
  `(fun ξ => if …) ξ` redex), so that the subsequent `if_pos`/`if_neg` rewrites fire.

The declarations are renamed with a `C` suffix so that this file can coexist with the original.
-/
/-
# `fareyModK`: the Farey-clipped linear lacunary variational estimate at `l₁ = 0`

The target is the *Farey-only* (narrow-strata) form of the paper's (lin-1) at the arithmetic height
`l₁ = 0`: for the family of Ionescu–Wainger modulated bumps `varphiNt (⌊a n⌋) k t` clipped at the
scales `n` which are *narrow at level* `fareyK Cρc ρ 0`, i.e. `Farey Cρc ρ 0 k a n`, the `r`-variation
in `ℓ^p(ℤ)` is bounded by `K (1 + k) ‖f‖_{ℓ^p}`, uniformly in all the data.

This is the same estimate as `Work.KMTAreas.A7.lacunaryBumpFareyPartBound`, but the clipping is by
the Farey condition alone (there is no `core` cut): the two ingredients of the proof — the
narrowness of `varphiNt` on the Farey scales (`narrow_of_farey`, which uses
`varphiNt_mem_realArc`) and the two-endpoint shifted Calderón–Zygmund multiplier bound
`multBound_varphiNt_two_endpoints` for the signed sums of the *unclipped* bumps — are exactly the
hypotheses of `varEst_of_narrow_symbols_twoEndpoints`, and neither of them requires the `core`
condition (nor `l₁ ≥ 1`: the multiplier bound holds at every height `k ≥ 1`).  The arithmetic height
`l₁ = 0` is what makes the loss factor of `varEst_of_narrow_symbols_twoEndpoints` collapse to
`K (1 + k)`.
-/
import Mathlib
import Submission.Work.KMTAreas.A7.lacunaryBumpFareyPartBound

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.KMTAreas.A7LoLin

open MeasureTheory Finset
open scoped ENNReal NNReal BigOperators
open PointwiseErgodicTheorems Submission.PointwiseErgodicTheorems
open Work.Analysis.IonescuWainger Work.Analysis.IWMultiplier
open Work.KMTAreas.A7

noncomputable section

/-- The Schwartz family clipped at the Farey (narrowness) scales, at the arithmetic height
`l₁ = 0`: the `n`-th member is the bumped scale `varphiNtSch (⌊a n⌋) k t` when
`Farey Cρc ρ 0 k a n` holds, and `0` otherwise. -/
noncomputable def fareyOnlySchC (ρ : ℝ) (a : ℕ → NNReal) (Cρc : ℝ) (k : ℕ) (t : ℝ) :
    ℕ → SchwartzMap ℝ ℂ :=
  fun n => if Farey Cρc ρ 0 k a n then varphiNtSch (Nat.floor (a n)) k t else 0

/-- The value of the Farey-clipped family: the modulated bump where the Farey condition holds, and
`0` otherwise. -/
@[simp] lemma fareyOnlySchC_apply (ρ : ℝ) (a : ℕ → NNReal) (Cρc : ℝ) (k : ℕ) (t : ℝ) (n : ℕ)
    (ξ : ℝ) :
    (fareyOnlySchC ρ a Cρc k t n : ℝ → ℂ) ξ
      = if Farey Cρc ρ 0 k a n then varphiNt (Nat.floor (a n)) k t ξ else 0 := by
  rw [fareyOnlySchC]
  by_cases h : Farey Cρc ρ 0 k a n
  · rw [if_pos h, if_pos h, varphiNtSch_apply]
  · rw [if_neg h, if_neg h]
    simp

/-- The Farey-clipped family as a family of functions. -/
lemma fareyOnlySchC_coe (ρ : ℝ) (a : ℕ → NNReal) (Cρc : ℝ) (k : ℕ) (t : ℝ) (n : ℕ) :
    (fareyOnlySchC ρ a Cρc k t n : ℝ → ℂ)
      = fun ξ : ℝ => if Farey Cρc ρ 0 k a n then varphiNt (Nat.floor (a n)) k t ξ else 0 :=
  funext (fareyOnlySchC_apply ρ a Cρc k t n)

theorem fareyModKC (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (p : ENNReal) (hp : 1 < p) (hptop : p < ⊤)
    (r : NNReal) (hr : 2 < r) (Λ : NNReal) (hΛ : 1 < Λ) :
    ∃ Cρc : ℝ, 3 ≤ Cρc ∧ ∃ K : ℝ, 0 < K ∧
      ∀ (k : ℕ) (hk : 1 ≤ k) (t : ℝ) (ht : t ∈ Set.Icc (1 / 2 : ℝ) 1)
        (a : ℕ → NNReal) (ha : PointwiseErgodicTheorems.Lacunary Λ a) (ha1 : ∀ n, 1 ≤ a n)
        (f : ℤ → ℂ),
        MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
          (fun n : ℕ => Work.KMTAreas.A7.Tle ρ 0 (fun ξ : ℝ =>
            if Work.KMTAreas.A7.Farey Cρc ρ 0 k a n
            then Work.KMTAreas.A7.varphiNt (Nat.floor (a n)) k t ξ else 0) f x))
          p MeasureTheory.Measure.count
        ≤ ENNReal.ofReal (K * (1 + (k : ℝ))) *
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
  intro k hk t ht a ha ha1 f
  set Cc : ℝ := max 3 Cρ with hCcdef
  set M : NNReal := C * (1 + k) with hMdef
  have hCc3 : 3 ≤ Cc := by rw [hCcdef]; exact le_max_left _ _
  have hCc1 : 1 < Cc := lt_of_lt_of_le (by norm_num) hCc3
  have hCρle : Cρ ≤ Cc := by rw [hCcdef]; exact le_max_right _ _
  have hCρ0 : (0 : ℝ) ≤ Cρ := hCρpos.le
  have hMpos : 0 < M := by
    rw [hMdef]
    exact mul_pos hCpos
      (lt_of_lt_of_le (by norm_num) (le_add_of_nonneg_right (zero_le : (0 : NNReal) ≤ (k : NNReal))))
  -- ## Narrowness of the clipped family
  have hnarrow : ∀ n ξ, (fareyOnlySchC ρ a Cc k t n : ℝ → ℂ) ξ ≠ 0 →
      ξ ∈ realArc (fareyK Cc ρ 0) := by
    intro n ξ hξ
    rw [fareyOnlySchC_coe] at hξ
    simp only [] at hξ
    by_cases h : Farey Cc ρ 0 k a n
    · rw [if_pos h] at hξ
      exact narrow_of_farey (t := t) h ξ hξ
    · rw [if_neg h] at hξ
      exact absurd rfl hξ
  -- ## The two-endpoint multiplier bound for the clipped family
  have hMult : ∀ (U : Finset ℕ) (ω : ℕ → Bool),
      IsLqMultiplierBound 2 (fun ξ : ℝ => ∑ n ∈ U, (if ω n then (1 : ℂ) else -1) *
          (fareyOnlySchC ρ a Cc k t n : ℝ → ℂ) ξ) M ∧
      IsLqMultiplierBound (ENNReal.ofReal (2 * (k₀ : ℝ)))
        (fun ξ : ℝ => ∑ n ∈ U, (if ω n then (1 : ℂ) else -1) *
          (fareyOnlySchC ρ a Cc k t n : ℝ → ℂ) ξ) M := by
    intro U ω
    have hU : (fun ξ : ℝ => ∑ n ∈ U, (if ω n then (1 : ℂ) else -1) *
          (fareyOnlySchC ρ a Cc k t n : ℝ → ℂ) ξ)
        = (fun ξ : ℝ =>
            ∑ n ∈ U.filter (fun n => Farey Cc ρ 0 k a n),
              (if ω n then (1 : ℂ) else -1) * varphiNt (Nat.floor (a n)) k t ξ) := by
      funext ξ
      rw [Finset.sum_filter]
      refine Finset.sum_congr rfl (fun n _ => ?_)
      rw [fareyOnlySchC_coe]
      by_cases h : Farey Cc ρ 0 k a n <;> simp [h]
    obtain ⟨hb2, hbe⟩ := hCbound k hk t ht a ha ha1
      (U.filter (fun n => Farey Cc ρ 0 k a n)) ω
    rw [ofReal_two_eq] at hb2
    exact ⟨by rw [hU]; exact hb2, by rw [hU]; exact hbe⟩
  -- ## The narrow-symbol variational estimate at the narrowness level `fareyK Cc ρ 0`
  have hgood : GoodMajorArcs ρ Cρ 0 (fareyK Cc ρ 0) :=
    goodMajorArcs_fareyK hCρle hCρ0 hρ.le (Nat.zero_le 0)
  have hk' : (2 : ℝ) ^ (fareyK Cc ρ 0) < 1 / 2 := two_rpow_fareyK_lt_half hCc1 hρ.le 0
  have hres := hmain 0 (fareyK Cc ρ 0) hgood hk' M hMpos
    (fareyOnlySchC ρ a Cc k t) hnarrow hMult f
  -- ## Rewriting the clipped family back to the explicit `if`
  have hInt : (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
        (fun n : ℕ => Tle ρ 0 (fun ξ : ℝ =>
          if Farey Cc ρ 0 k a n
          then varphiNt (Nat.floor (a n)) k t ξ else 0) f x))
      = (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
        (fun n : ℕ => Tle ρ 0
          (fareyOnlySchC ρ a Cc k t n : ℝ → ℂ) f x)) := by
    funext x
    refine congrArg (fun u : ℕ → ℂ => PointwiseErgodicTheorems.variationalNorm r u) ?_
    funext n
    rw [fareyOnlySchC_coe]
  rw [hInt]
  -- ## The constant bookkeeping
  refine hres.trans (le_of_eq ?_)
  have hMR : (M : ℝ) = (C : ℝ) * (1 + (k : ℝ)) := by rw [hMdef]; push_cast; ring
  have hconst : Kvar * (1 + ((0 : ℕ) : ℝ)) * (M : ℝ) = (Kvar * (C : ℝ)) * (1 + (k : ℝ)) := by
    rw [hMR]; push_cast; ring
  rw [hconst]

end

end Work.KMTAreas.A7LoLin
