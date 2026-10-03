/-
# The Farey (narrow) part of the `g`-side linear lacunary variational estimate (Area A7)

This is the `g`-side companion of the proved `Work.KMTAreas.A7.lacunaryBumpFareyPartBound`: the
`r`-variation of the family of Ionescu–Wainger modulated `d`-fold bumps
`T^{≤l}_{1_{core ∧ Farey} · φ̃_{⌊a n⌋,t}} g`, restricted to the scales `n` which are simultaneously

* `core ρ C₀ l₁ l₂ k₁ k₂ a n` — admissible, above the large-scale cut `splitCut` and in the main
  regime of the functional calculus, and
* `Farey Cρc ρ l₂ k₂ a n` — *narrow at level* `fareyK Cρc ρ l₂`:
  `k₂ - Log ⌊a n⌋ ≤ ⌊-Cρc·2^{ρ l₂}⌋`,

is bounded on `ℓ^p(ℤ)` by `C (1 + l₂) (1 + d k₂) ‖g‖_{ℓ^p}`, uniformly in the data.  This is the
regime in which the Ionescu–Wainger endpoint bound for *narrow* symbols (with its
`GoodMajorArcs ρ Cρ l (fareyK Cρc ρ l₂)`, `2^{fareyK} < 1/2`) applies.

The proof follows the `f`-side proof (`Submission/Work/KMTAreas/A7/lacunaryBumpFareyPartBound.lean`)
line for line, with the substitutions

* `varphiNt` ↦ `varphitildeNt P d` (the `d`-fold rescaled bump of §6),
* `Farey Cρc ρ l₁ k₁` ↦ `Farey Cρc ρ l₂ k₂`,
* the two-endpoint input `multBound_varphiNt_two_endpoints` ↦ `LoGMultBoundTwoEndpoints`
  (which is `Work.KMTAreas.A7Hi.varphitildeNt_mult_bound_k2pos_hi` at the exponents `2` and `2k₀`),
* the loss `1 + k₁` ↦ `1 + d · k₂` (the `g`-side bump has `d` rescaled frequencies).

The three ingredients that are new relative to the `f`-side are proved in this file / imported:

* narrowness (`logNarrow_of_fareyG`): `varphitildeNt_support_all` gives
  `|ξ| ≤ 2^{d(k₂ - Log N)}`, and the Farey condition `k₂ - Log N ≤ fareyK Cρc ρ l₂` together with
  `d ≥ 1` and `fareyK ≤ 0` gives `d(k₂ - Log N) ≤ fareyK Cρc ρ l₂`, hence
  `ξ ∈ realArc (fareyK Cρc ρ l₂)`;
* the Schwartz realisation of the clipped family is `Work.KMTAreas.A7.gVarphitildeNtSch`
  (`Submission/Work/KMTAreas/A7/randSymb_Tle_g_bound.lean`);
* the variational estimate for narrow families is
  `Work.KMTAreas.A7.varEst_of_narrow_symbols_twoEndpoints`.
-/
import Mathlib
import Submission.Work.KMTAreas.A7.lacunaryBumpFareyPartBound
import Submission.Work.KMTAreas.A7.LoGMultBoundTwoEndpoints
import Submission.Work.KMTAreas.A7.randSymb_Tle_g_bound

set_option maxHeartbeats 2000000

open MeasureTheory Polynomial
open scoped ENNReal NNReal BigOperators

namespace Work.KMTAreas.A7

noncomputable section

open Finset
open PointwiseErgodicTheorems Submission.PointwiseErgodicTheorems
open Work.Analysis.IonescuWainger Work.Analysis.IWMultiplier
open Work.KMTContract Work.Analysis.EndVar

/-! ## §1.  Narrowness of the `d`-fold bump on the Farey scales -/

/-- The `rpow`/`zpow` bridge for the support exponent `d (k₂ - Log N)`. -/
lemma logSupport_rpow_zpow (d k N : ℕ) :
    (2 : ℝ) ^ ((d : ℝ) * ((k : ℝ) - (logN N : ℝ)))
      = (2 : ℝ) ^ ((d : ℤ) * ((k : ℤ) - logN N)) := by
  rw [← Real.rpow_intCast (2 : ℝ) ((d : ℤ) * ((k : ℤ) - logN N))]
  push_cast
  ring

/-- **Narrowness of the `d`-fold bump on the Farey scales.**  If `n` is a Farey scale for the
height `k₂` and the arithmetic level `l₂` (with `Cρc ≥ 0`), then the modulated `d`-fold bump
`φ̃_{N,t}` is supported in the narrow arc `realArc (fareyK Cρc ρ l₂)`. -/
theorem logNarrow_of_fareyG (P : Polynomial ℤ) (d : ℕ) (hd : 1 ≤ d) {Cρc ρ : ℝ}
    (hCρc : 0 ≤ Cρc) {l₂ k₂ : ℕ} {a : ℕ → NNReal} {n : ℕ} {t : ℝ}
    (h : Farey Cρc ρ l₂ k₂ a n) :
    ∀ ξ : ℝ, varphitildeNt P d (Nat.floor (a n)) k₂ t ξ ≠ 0 →
      ξ ∈ Work.Analysis.IonescuWainger.realArc (fareyK Cρc ρ l₂) := by
  intro ξ hξ
  have hsupp := varphitildeNt_support_all P d (Nat.floor (a n)) k₂ t ξ hξ
  rw [logSupport_rpow_zpow] at hsupp
  have hfk : fareyK Cρc ρ l₂ ≤ 0 := by
    rw [fareyK]
    refine Int.floor_nonpos ?_
    have h2 : (0 : ℝ) ≤ (2 : ℝ) ^ (ρ * (l₂ : ℝ)) := Real.rpow_nonneg (by norm_num) _
    nlinarith
  have hle : (d : ℤ) * ((k₂ : ℤ) - logN (Nat.floor (a n))) ≤ fareyK Cρc ρ l₂ := by
    have hdZ : (1 : ℤ) ≤ (d : ℤ) := by exact_mod_cast hd
    have hx : (k₂ : ℤ) - logN (Nat.floor (a n)) ≤ fareyK Cρc ρ l₂ := h
    have hx0 : (k₂ : ℤ) - logN (Nat.floor (a n)) ≤ 0 := le_trans hx hfk
    calc (d : ℤ) * ((k₂ : ℤ) - logN (Nat.floor (a n)))
        ≤ (1 : ℤ) * ((k₂ : ℤ) - logN (Nat.floor (a n))) :=
          mul_le_mul_of_nonpos_right hdZ hx0
      _ = (k₂ : ℤ) - logN (Nat.floor (a n)) := one_mul _
      _ ≤ fareyK Cρc ρ l₂ := hx
  have h2 : |ξ| ≤ (2 : ℝ) ^ (fareyK Cρc ρ l₂) :=
    le_trans hsupp (zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hle)
  exact Set.mem_Icc.mpr ⟨neg_le_of_abs_le h2, (abs_le.mp h2).2⟩

/-! ## §2.  The Schwartz family clipped at the core-and-Farey scales -/

/-- The `g`-side family of modulated `d`-fold bumps clipped at the core-and-Farey scales: the
`n`-th member is the Schwartz bump `gVarphitildeNtSch P d (⌊a n⌋) k₂ t` when
`core ρ C₀ l₁ l₂ k₁ k₂ a n ∧ Farey Cρc ρ l₂ k₂ a n`, and `0` otherwise. -/
noncomputable def loGFareyClippedSch (P : Polynomial ℤ) (d : ℕ) (ρ : ℝ) (C₀ : ℕ)
    (a : ℕ → NNReal) (Cρc : ℝ) (l₁ l₂ k₁ k₂ : ℕ) (t : ℝ) (n : ℕ) : SchwartzMap ℝ ℂ :=
  if core ρ C₀ l₁ l₂ k₁ k₂ a n ∧ Farey Cρc ρ l₂ k₂ a n then
    gVarphitildeNtSch P d (Nat.floor (a n)) k₂ t else 0

lemma loGFareyClippedSch_apply (P : Polynomial ℤ) (d : ℕ) (ρ : ℝ) (C₀ : ℕ)
    (a : ℕ → NNReal) (Cρc : ℝ) (l₁ l₂ k₁ k₂ : ℕ) (t : ℝ) (n : ℕ) (ξ : ℝ) :
    (loGFareyClippedSch P d ρ C₀ a Cρc l₁ l₂ k₁ k₂ t n : ℝ → ℂ) ξ
      = if core ρ C₀ l₁ l₂ k₁ k₂ a n ∧ Farey Cρc ρ l₂ k₂ a n then
          varphitildeNt P d (Nat.floor (a n)) k₂ t ξ else 0 := by
  rw [loGFareyClippedSch]
  by_cases h : core ρ C₀ l₁ l₂ k₁ k₂ a n ∧ Farey Cρc ρ l₂ k₂ a n
  · rw [if_pos h, if_pos h, gVarphitildeNtSch_coe]
  · rw [if_neg h, if_neg h]
    simp

lemma loGFareyClippedSch_coe (P : Polynomial ℤ) (d : ℕ) (ρ : ℝ) (C₀ : ℕ)
    (a : ℕ → NNReal) (Cρc : ℝ) (l₁ l₂ k₁ k₂ : ℕ) (t : ℝ) (n : ℕ) :
    (loGFareyClippedSch P d ρ C₀ a Cρc l₁ l₂ k₁ k₂ t n : ℝ → ℂ)
      = fun ξ : ℝ => if core ρ C₀ l₁ l₂ k₁ k₂ a n ∧ Farey Cρc ρ l₂ k₂ a n then
          varphitildeNt P d (Nat.floor (a n)) k₂ t ξ else 0 :=
  funext (loGFareyClippedSch_apply P d ρ C₀ a Cρc l₁ l₂ k₁ k₂ t n)

/-! ## §3.  The Farey part of the `g`-side linear lacunary variational estimate -/

/-- The Farey (narrow-symbol) part of the linear lacunary variational estimate for the `g`-side
modulated bump at `k₂ ≥ 1`: there are `Cρc ≥ 3` and `K > 0` such that for every `k₂ ≥ 1`, every
`l ≤ l₂`, every `t ∈ [1/2,1]`, every `Λ`-lacunary `a` with `a n ≥ 1` and every `g : ℤ → ℂ`, the
`ℓ^p(ℤ)` norm of the `r`-variation of the `core ∧ Farey`-clipped family
`n ↦ Tle ρ l (1_{core ∧ Farey} · varphitildeNt P d (⌊a n⌋) k₂ t) g`
is at most `K (1 + l₂) (1 + d k₂) ‖g‖_{ℓ^p}`.  This is the `g`-side analogue of the PROVED
`Work.KMTAreas.A7.lacunaryBumpFareyPartBound`
(`Submission/Work/KMTAreas/A7/lacunaryBumpFareyPartBound.lean`): copy its structure, replacing
`varphiNt` by `varphitildeNt P d`, `Farey Cρc ρ l₁ k₁` by `Farey Cρc ρ l₂ k₂`, the loss `1 + k₁` by
`1 + d * k₂`, and the two-endpoint input `multBound_varphiNt_two_endpoints` by
`Work.KMTAreas.A7.LoGMultBoundTwoEndpoints` (or `A7Hi/Gblock.lean`'s
`multBound_varphitildeNt_two_endpoints` if that file builds by the time you start).  Narrowness:
`varphitildeNt_support_all` gives `|ξ| ≤ 2^{d(k₂ - Log N)}` and the `Farey` condition
`k₂ - Log N ≤ fareyK Cρc ρ l₂` plus `d ≥ 2` gives `ξ ∈ realArc (fareyK Cρc ρ l₂)`; the Schwartz
realisation is `varphitildeNtSch` in `Submission/Work/KMTAreas/A7/randSymb_Tm_g_lp.lean`. -/
theorem LoGFareyPartBound (P : Polynomial ℤ) (d : ℕ) (hd : 2 ≤ d) (hdP : P.natDegree ≤ d)
    (C₀ : ℕ) (r : NNReal) (hr : 2 < r) (ρ : ℝ) (hρ : 0 < ρ)
    (hρ1 : ρ ≤ 1) (Λ : NNReal) (hΛ : 1 < Λ) (p : ENNReal) (hp : 1 < p) (hptop : p < ⊤) :
    ∃ Cρc : ℝ, 3 ≤ Cρc ∧ ∃ K : ℝ, 0 < K ∧
      ∀ (k₂ : ℕ) (hk₂ : 1 ≤ k₂) (l l₂ l₁ k₁ : ℕ) (hl : l ≤ l₂)
        (t : ℝ) (ht : t ∈ Set.Icc (1/2 : ℝ) 1)
        (a : ℕ → NNReal) (ha : PointwiseErgodicTheorems.Lacunary Λ a) (ha1 : ∀ n, 1 ≤ a n)
        (g : ℤ → ℂ),
        MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
          (fun n : ℕ => Work.KMTAreas.A7.Tle ρ l (fun ξ : ℝ =>
            if Work.KMTAreas.A7.core ρ C₀ l₁ l₂ k₁ k₂ a n ∧
              Work.KMTAreas.A7.Farey Cρc ρ l₂ k₂ a n
            then Work.KMTAreas.A7.varphitildeNt P d (Nat.floor (a n)) k₂ t ξ else 0) g x))
          p MeasureTheory.Measure.count
        ≤ ENNReal.ofReal (K * (1 + (l₂ : ℝ)) * (1 + (d : ℝ) * (k₂ : ℝ))) *
            MeasureTheory.eLpNorm g p MeasureTheory.Measure.count := by
  classical
  -- ## The endpoint exponent `k₀ ≥ 2` covering `p` and its Hölder dual
  have hq1 : 1 < p.toReal := by
    rw [← ENNReal.toReal_one]
    exact (ENNReal.toReal_lt_toReal ENNReal.one_ne_top (ne_of_lt hptop)).mpr hp
  obtain ⟨k₀, hk₀, hpmax, hpd⟩ := exists_endpoint_exponent p.toReal hq1
  -- ## The two inputs: the narrow-symbol variational estimate, and the two-endpoint multiplier bound
  obtain ⟨Cρ, hCρpos, Kvar, hKvarpos, hmain⟩ :=
    varEst_of_narrow_symbols_twoEndpoints ρ hρ hρ1 r hr p hp hptop k₀ hk₀ hpmax hpd
  obtain ⟨C, hCpos, hCbound⟩ := LoGMultBoundTwoEndpoints P d hd hdP Λ hΛ k₀ hk₀
  refine ⟨max 3 Cρ, le_max_left _ _, Kvar * (C : ℝ),
    mul_pos hKvarpos (by exact_mod_cast hCpos), ?_⟩
  intro k₂ hk₂ l l₂ l₁ k₁ hl t ht a ha ha1 g
  set Cc : ℝ := max 3 Cρ with hCcdef
  set M : NNReal := C * (1 + d * k₂) with hMdef
  have hCc3 : 3 ≤ Cc := by rw [hCcdef]; exact le_max_left _ _
  have hCc1 : 1 < Cc := lt_of_lt_of_le (by norm_num) hCc3
  have hCρle : Cρ ≤ Cc := by rw [hCcdef]; exact le_max_right _ _
  have hCρ0 : (0 : ℝ) ≤ Cρ := hCρpos.le
  have hCc0 : (0 : ℝ) ≤ Cc := le_trans hCρ0 hCρle
  have hMpos : 0 < M := by
    rw [hMdef]
    exact mul_pos hCpos (by positivity)
  -- ## Narrowness of the clipped family
  have hnarrow : ∀ n ξ, (loGFareyClippedSch P d ρ C₀ a Cc l₁ l₂ k₁ k₂ t n : ℝ → ℂ) ξ ≠ 0 →
      ξ ∈ Work.Analysis.IonescuWainger.realArc (fareyK Cc ρ l₂) := by
    intro n ξ hξ
    have hξ' := hξ
    rw [loGFareyClippedSch_apply] at hξ'
    by_cases h : core ρ C₀ l₁ l₂ k₁ k₂ a n ∧ Farey Cc ρ l₂ k₂ a n
    · rw [if_pos h] at hξ'
      exact logNarrow_of_fareyG P d (by omega) hCc0 h.2 ξ hξ'
    · rw [if_neg h] at hξ'
      exact absurd rfl hξ'
  -- ## The two-endpoint multiplier bound for the clipped family
  have hMult : ∀ (U : Finset ℕ) (ω : ℕ → Bool),
      IsLqMultiplierBound 2 (fun ξ : ℝ => ∑ n ∈ U, (if ω n then (1 : ℂ) else -1) *
          (loGFareyClippedSch P d ρ C₀ a Cc l₁ l₂ k₁ k₂ t n : ℝ → ℂ) ξ) M ∧
      IsLqMultiplierBound (ENNReal.ofReal (2 * (k₀ : ℝ)))
        (fun ξ : ℝ => ∑ n ∈ U, (if ω n then (1 : ℂ) else -1) *
          (loGFareyClippedSch P d ρ C₀ a Cc l₁ l₂ k₁ k₂ t n : ℝ → ℂ) ξ) M := by
    intro U ω
    have hU : (fun ξ : ℝ => ∑ n ∈ U, (if ω n then (1 : ℂ) else -1) *
          (loGFareyClippedSch P d ρ C₀ a Cc l₁ l₂ k₁ k₂ t n : ℝ → ℂ) ξ)
        = (fun ξ : ℝ =>
            ∑ n ∈ U.filter (fun n => core ρ C₀ l₁ l₂ k₁ k₂ a n ∧ Farey Cc ρ l₂ k₂ a n),
              (if ω n then (1 : ℂ) else -1) * varphitildeNt P d (Nat.floor (a n)) k₂ t ξ) := by
      funext ξ
      rw [Finset.sum_filter]
      refine Finset.sum_congr rfl (fun n _ => ?_)
      rw [loGFareyClippedSch_apply]
      by_cases h : core ρ C₀ l₁ l₂ k₁ k₂ a n ∧ Farey Cc ρ l₂ k₂ a n <;> simp [h]
    obtain ⟨hb2, hbe⟩ := hCbound k₂ hk₂ t ht a ha ha1
      (U.filter (fun n => core ρ C₀ l₁ l₂ k₁ k₂ a n ∧ Farey Cc ρ l₂ k₂ a n)) ω
    refine ⟨?_, ?_⟩
    · rw [hU]
      simpa only [ENNReal.ofReal_ofNat] using hb2
    · rw [hU]
      exact hbe
  -- ## The narrow-symbol variational estimate at the narrowness level `fareyK Cc ρ l₂`
  have hgood : GoodMajorArcs ρ Cρ l (fareyK Cc ρ l₂) :=
    goodMajorArcs_fareyK hCρle hCρ0 hρ.le hl
  have hk : (2 : ℝ) ^ (fareyK Cc ρ l₂) < 1 / 2 := two_rpow_fareyK_lt_half hCc1 hρ.le l₂
  have hres := hmain l (fareyK Cc ρ l₂) hgood hk M hMpos
    (loGFareyClippedSch P d ρ C₀ a Cc l₁ l₂ k₁ k₂ t) hnarrow hMult g
  -- ## Rewriting the clipped family back to the explicit `if`
  have hInt : (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
        (fun n : ℕ => Tle ρ l (fun ξ : ℝ =>
          if core ρ C₀ l₁ l₂ k₁ k₂ a n ∧ Farey Cc ρ l₂ k₂ a n
          then varphitildeNt P d (Nat.floor (a n)) k₂ t ξ else 0) g x))
      = (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
        (fun n : ℕ => Tle ρ l
          (loGFareyClippedSch P d ρ C₀ a Cc l₁ l₂ k₁ k₂ t n : ℝ → ℂ) g x)) := by
    funext x
    refine congrArg (fun u : ℕ → ℂ => PointwiseErgodicTheorems.variationalNorm r u) ?_
    funext n
    rw [loGFareyClippedSch_coe]
  rw [hInt]
  -- ## The constant bookkeeping
  refine hres.trans ?_
  refine mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal ?_) zero_le
  have hMR : (M : ℝ) = (C : ℝ) * (1 + (d : ℝ) * (k₂ : ℝ)) := by
    rw [hMdef]; push_cast; ring
  have hlR : (1 + (l : ℝ)) ≤ (1 + (l₂ : ℝ)) := by
    have hl' : (l : ℝ) ≤ (l₂ : ℝ) := by exact_mod_cast hl
    linarith
  have hCnn : (0 : ℝ) ≤ (C : ℝ) := by positivity
  have hconstnn : (0 : ℝ) ≤ Kvar * (C : ℝ) * (1 + (d : ℝ) * (k₂ : ℝ)) :=
    mul_nonneg (mul_nonneg hKvarpos.le hCnn) (by positivity)
  calc Kvar * (1 + (l : ℝ)) * (M : ℝ)
      = Kvar * (C : ℝ) * (1 + (d : ℝ) * (k₂ : ℝ)) * (1 + (l : ℝ)) := by
        rw [hMR]; ring
    _ ≤ Kvar * (C : ℝ) * (1 + (d : ℝ) * (k₂ : ℝ)) * (1 + (l₂ : ℝ)) :=
        mul_le_mul_of_nonneg_left hlR hconstnn
    _ = Kvar * (C : ℝ) * (1 + (l₂ : ℝ)) * (1 + (d : ℝ) * (k₂ : ℝ)) := by ring

end

end Work.KMTAreas.A7
