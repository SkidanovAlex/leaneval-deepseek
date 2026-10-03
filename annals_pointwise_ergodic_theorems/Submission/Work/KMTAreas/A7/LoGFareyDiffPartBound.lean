import Mathlib
import Submission.Work.KMTAreas.A7.lacunaryBumpAux
import Submission.Work.KMTAreas.A7.VarphitildeDiffMultBound
import Submission.Work.KMTAreas.A7.randSymb_Tle_g_bound

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.KMTAreas.A7

noncomputable section

open MeasureTheory Polynomial Finset
open scoped ENNReal NNReal BigOperators
open PointwiseErgodicTheorems Submission.PointwiseErgodicTheorems
open Work.Analysis.IonescuWainger Work.Analysis.IWMultiplier

/-! ## §1.  The Schwartz packaging of the `d`-fold bumps

The variational estimate `varEst_of_narrow_symbols_twoEndpoints` consumes a family of Schwartz
symbols, so the `g`-side bumps have to be realised as Schwartz maps.  `gVarphitildeNtSch` (the
modulated bump, from `randSymb_Tle_g_bound.lean`) is already available; the *unmodulated* bump
`φ̃_N` is packaged here. -/

/-- The unmodulated `d`-fold bump `φ̃_N` as a Schwartz function. -/
noncomputable def varphitildeNSchA (d N k₂ : ℕ) : SchwartzMap ℝ ℂ :=
  (hasCompactSupport_varphitildeN d N k₂).toSchwartzMap (gContDiff_varphitildeN_all d N k₂)

lemma varphitildeNSchA_apply (d N k₂ : ℕ) (ξ : ℝ) :
    varphitildeNSchA d N k₂ ξ = varphitildeN d N k₂ ξ :=
  HasCompactSupport.toSchwartzMap_toFun _ _ ξ

lemma varphitildeNSchA_coe (d N k₂ : ℕ) :
    (varphitildeNSchA d N k₂ : ℝ → ℂ) = varphitildeN d N k₂ :=
  funext (varphitildeNSchA_apply d N k₂)

/-! ## §2.  Narrowness of the `d`-fold bumps on the Farey scales

On the `Farey` scales the height is so low that `φ̃_N` is supported in the fixed narrow arc
`realArc (fareyK Cρc ρ l₂)`: the support bound `varphitildeNt_support_all` gives
`|ξ| ≤ 2^{d(k₂ - Log N)}` and `Farey` gives `k₂ - Log N ≤ fareyK Cρc ρ l₂`, which is `≤ 0`. -/

/-- The `rpow`/`zpow` bridge for the support exponent `d (k₂ - Log N)`. -/
lemma gSupport_rpow_zpowA (d k N : ℕ) :
    (2 : ℝ) ^ ((d : ℝ) * ((k : ℝ) - (Work.Analysis.EndVar.logN N : ℝ)))
      = (2 : ℝ) ^ ((d : ℤ) * ((k : ℤ) - Work.Analysis.EndVar.logN N)) := by
  rw [← Real.rpow_intCast (2 : ℝ) ((d : ℤ) * ((k : ℤ) - Work.Analysis.EndVar.logN N))]
  push_cast
  ring

/-- **Narrowness of the modulated `d`-fold bump on the Farey scales.** -/
theorem varphitildeNt_narrow_of_farey_A (P : Polynomial ℤ) (d : ℕ) (hd : 1 ≤ d) {Cρc ρ : ℝ}
    (hCρc : 0 ≤ Cρc) {l₂ k₂ : ℕ} {a : ℕ → NNReal} {n : ℕ} {t : ℝ}
    (h : Farey Cρc ρ l₂ k₂ a n) :
    ∀ ξ : ℝ, varphitildeNt P d (Nat.floor (a n)) k₂ t ξ ≠ 0 →
      ξ ∈ realArc (fareyK Cρc ρ l₂) := by
  intro ξ hξ
  have hsupp := varphitildeNt_support_all P d (Nat.floor (a n)) k₂ t ξ hξ
  rw [gSupport_rpow_zpowA] at hsupp
  have hfk : fareyK Cρc ρ l₂ ≤ 0 := by
    rw [fareyK]
    refine Int.floor_nonpos ?_
    have h2 : (0 : ℝ) ≤ (2 : ℝ) ^ (ρ * (l₂ : ℝ)) := Real.rpow_nonneg (by norm_num) _
    nlinarith
  have hle : (d : ℤ) * ((k₂ : ℤ) - Work.Analysis.EndVar.logN (Nat.floor (a n)))
      ≤ fareyK Cρc ρ l₂ := by
    have hdZ : (1 : ℤ) ≤ (d : ℤ) := by exact_mod_cast hd
    have hx : (k₂ : ℤ) - Work.Analysis.EndVar.logN (Nat.floor (a n)) ≤ fareyK Cρc ρ l₂ := h
    have hx0 : (k₂ : ℤ) - Work.Analysis.EndVar.logN (Nat.floor (a n)) ≤ 0 :=
      le_trans hx hfk
    calc (d : ℤ) * ((k₂ : ℤ) - Work.Analysis.EndVar.logN (Nat.floor (a n)))
        ≤ (1 : ℤ) * ((k₂ : ℤ) - Work.Analysis.EndVar.logN (Nat.floor (a n))) :=
          mul_le_mul_of_nonpos_right hdZ hx0
      _ = (k₂ : ℤ) - Work.Analysis.EndVar.logN (Nat.floor (a n)) := one_mul _
      _ ≤ fareyK Cρc ρ l₂ := hx
  have h2 : |ξ| ≤ (2 : ℝ) ^ (fareyK Cρc ρ l₂) :=
    le_trans hsupp (zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hle)
  exact Set.mem_Icc.mpr ⟨neg_le_of_abs_le h2, (abs_le.mp h2).2⟩

/-- **Narrowness of the unmodulated `d`-fold bump on the Farey scales.**  The modulation is
nowhere zero, so the support of `φ̃_N` is the support of `φ̃_{N,t}`. -/
theorem varphitildeN_narrow_of_farey_A (P : Polynomial ℤ) (d : ℕ) (hd : 1 ≤ d) {Cρc ρ : ℝ}
    (hCρc : 0 ≤ Cρc) {l₂ : ℕ} {a : ℕ → NNReal} {n : ℕ} {t : ℝ}
    (h : Farey Cρc ρ l₂ 0 a n) :
    ∀ ξ : ℝ, varphitildeN d (Nat.floor (a n)) 0 ξ ≠ 0 →
      ξ ∈ realArc (fareyK Cρc ρ l₂) := by
  intro ξ hξ
  have hξt : varphitildeNt P d (Nat.floor (a n)) 0 t ξ ≠ 0 := by
    show varphitildeN d (Nat.floor (a n)) 0 ξ *
      ee (PevalR P ((Nat.floor (a n) : ℝ) * t) * ξ) ≠ 0
    exact mul_ne_zero hξ (by simp [ee])
  exact varphitildeNt_narrow_of_farey_A P d hd hCρc h ξ hξt

/-! ## §3.  The two-endpoint multiplier input for the `k₂ = 0` difference family

This is the `g`-side twin of `multBound_varphiNt_diff_two_endpoints`: the Mikhlin argument of
`VarphitildeDiffMultBound` (`lacunaryDiffSymbol_mikhlin_const` applied to the difference symbol
`η(gScale d N 0 ·)(e(PevalR P (Nt)·) - 1)`, with the phase bound `abs_PevalR_div_gScale_le`)
gives the `L^q(ℝ)` multiplier bound for *every* `q > 1` at once; specialising to `q = 2` and
`q = 2 k₀` and taking the maximum of the two constants produces the shape required by
`varEst_of_narrow_symbols_twoEndpoints`. -/

/-- **The two-endpoint multiplier input at `k₂ = 0` for the low-frequency difference.** -/
theorem multBound_varphitildeNt_diff_two_endpoints_A (P : Polynomial ℤ) (d : ℕ) (hd : 2 ≤ d)
    (hdP : P.natDegree ≤ d) (Λ : NNReal) (hΛ : 1 < Λ) (k₀ : ℕ) (hk₀ : 2 ≤ k₀) :
    ∃ C : NNReal, 0 < C ∧ ∀ (t : ℝ) (ht : t ∈ Set.Icc (1/2 : ℝ) 1) (a : ℕ → NNReal)
      (ha : PointwiseErgodicTheorems.Lacunary Λ a) (ha1 : ∀ n, 1 ≤ a n)
      (U : Finset ℕ) (ω : ℕ → Bool),
      IsLqMultiplierBound (ENNReal.ofReal (2 : ℝ))
          (fun ξ : ℝ => ∑ n ∈ U, (if ω n then (1 : ℂ) else -1) *
            (varphitildeNt P d (Nat.floor (a n)) 0 t ξ
              - varphitildeN d (Nat.floor (a n)) 0 ξ)) C ∧
        IsLqMultiplierBound (ENNReal.ofReal (2 * (k₀ : ℝ)))
          (fun ξ : ℝ => ∑ n ∈ U, (if ω n then (1 : ℂ) else -1) *
            (varphitildeNt P d (Nat.floor (a n)) 0 t ξ
              - varphitildeN d (Nat.floor (a n)) 0 ξ)) C := by
  have hk₀1 : (1 : ℝ) < 2 * (k₀ : ℝ) := by
    have h1 : (1 : ℝ) ≤ (k₀ : ℝ) := by exact_mod_cast (by omega : 1 ≤ k₀)
    linarith
  obtain ⟨C₂, hC₂pos, hC₂⟩ := VarphitildeDiffMultBound P d hd hdP 2 (by norm_num) Λ hΛ
  obtain ⟨Ce, hCepos, hCe⟩ := VarphitildeDiffMultBound P d hd hdP (2 * (k₀ : ℝ)) hk₀1 Λ hΛ
  refine ⟨max C₂ Ce, lt_max_of_lt_left hC₂pos, ?_⟩
  intro t ht a ha ha1 U ω
  have hε : ∀ n : ℕ, ‖(if ω n then (1 : ℂ) else -1)‖ ≤ 1 := by
    intro n
    by_cases h : ω n <;> simp [h]
  refine ⟨?_, ?_⟩
  · exact IsLqMultiplierBound.mono (hC₂ t ht a ha ha1 U _ hε) (le_max_left _ _)
  · exact IsLqMultiplierBound.mono (hCe t ht a ha ha1 U _ hε) (le_max_right _ _)

/-! ## §4.  The clipped difference family as Schwartz symbols -/

/-- The clipped difference bump family `m ↦ (φ̃_{⌊a m⌋,t} − φ̃_{⌊a m⌋})·1_{core ∧ Farey}` as
Schwartz functions (at the bottom height `k₂ = 0`). -/
noncomputable def gFareyDiffSch (P : Polynomial ℤ) (d : ℕ) (ρ : ℝ) (C₀ : ℕ) (a : ℕ → NNReal)
    (Cρc : ℝ) (l₁ l₂ k₁ : ℕ) (m : ℕ) (t : ℝ) : SchwartzMap ℝ ℂ :=
  if core ρ C₀ l₁ l₂ k₁ 0 a m ∧ Farey Cρc ρ l₂ 0 a m then
    gVarphitildeNtSch P d (Nat.floor (a m)) 0 t - varphitildeNSchA d (Nat.floor (a m)) 0
  else 0

lemma gFareyDiffSch_coe (P : Polynomial ℤ) (d : ℕ) (ρ : ℝ) (C₀ : ℕ) (a : ℕ → NNReal)
    (Cρc : ℝ) (l₁ l₂ k₁ m : ℕ) (t : ℝ) :
    (gFareyDiffSch P d ρ C₀ a Cρc l₁ l₂ k₁ m t : ℝ → ℂ)
      = fun ξ : ℝ => if core ρ C₀ l₁ l₂ k₁ 0 a m ∧ Farey Cρc ρ l₂ 0 a m then
          varphitildeNt P d (Nat.floor (a m)) 0 t ξ - varphitildeN d (Nat.floor (a m)) 0 ξ
          else 0 := by
  unfold gFareyDiffSch
  by_cases h : core ρ C₀ l₁ l₂ k₁ 0 a m ∧ Farey Cρc ρ l₂ 0 a m
  · simp only [h]
    funext ξ
    simp [gVarphitildeNtSch_coe, varphitildeNSchA_coe]
  · simp only [h, if_false]
    funext ξ
    simp

/-- The Farey (narrow-symbol) part of the `k₂ = 0` low-frequency *difference* for the `g`-side:
there are `Cρc ≥ 3` and `K > 0` such that for every `l ≤ l₂`, every `t ∈ [1/2,1]`, every
`Λ`-lacunary `a` with `a n ≥ 1` and every `g : ℤ → ℂ`, the `ℓ^p(ℤ)` norm of the `r`-variation of the
`core ∧ Farey`-clipped family
`n ↦ Tle ρ l (1_{core ∧ Farey} · (varphitildeNt P d (⌊a n⌋) 0 t - varphitildeN d (⌊a n⌋) 0)) g`
is at most `K (1 + l₂) ‖g‖_{ℓ^p}`.  This is the `g`-side analogue of the PROVED
`Work.KMTAreas.A7.lacunaryBumpFareyDiffPartBound`
(`Submission/Work/KMTAreas/A7/lacunaryBumpFareyDiffPartBound.lean`): copy its structure with
`varphitildeNt P d` / `varphitildeN d` in place of `varphiNt` / `varphiN`, `Farey Cρc ρ l₂ 0` in
place of `Farey Cρc ρ l₁ 0`, and the loss `1 + l₂`.  The uniform-in-signs input is the `g`-side
difference multiplier bound `IsLqMultiplierBound q (∑_{n∈U} ε n · (varphitildeNt P d (⌊a n⌋) 0 t -
varphitildeN d (⌊a n⌋) 0)) C` at the two exponents `2` and `2 k₀` (the `g`-side analogue of the
proved `Work.KMTAreas.A7.lacunaryBump_mult_bound_k0_diff`).  That input is the Mikhlin argument of
`lacunaryBump_mult_bound_k0_diff.lean` (`lacunaryDiffSymbol_mikhlin` plus the phase bound
`abs_PevalR_div_gScale_le` for the polynomial modulation `ee (PevalR P (N t) ·)`), packaged for the
`g`-side difference symbol as `Work.KMTAreas.A7.VarphitildeDiffMultBound` and specialised to the two
endpoints `2` and `2 k₀` in `multBound_varphitildeNt_diff_two_endpoints_A` below.  The variational
estimate is then `Work.KMTAreas.A7.varEst_of_narrow_symbols_twoEndpoints`, applied exactly as the
`f`-side file does. -/
theorem LoGFareyDiffPartBound (P : Polynomial ℤ) (d : ℕ) (hd : 2 ≤ d) (hdP : P.natDegree ≤ d)
    (C₀ : ℕ) (r : NNReal) (hr : 2 < r) (ρ : ℝ) (hρ : 0 < ρ)
    (hρ1 : ρ ≤ 1) (Λ : NNReal) (hΛ : 1 < Λ) (p : ENNReal) (hp : 1 < p) (hptop : p < ⊤) :
    ∃ Cρc : ℝ, 3 ≤ Cρc ∧ ∃ K : ℝ, 0 < K ∧
      ∀ (l l₂ l₁ k₁ : ℕ) (hl : l ≤ l₂)
        (t : ℝ) (ht : t ∈ Set.Icc (1/2 : ℝ) 1)
        (a : ℕ → NNReal) (ha : PointwiseErgodicTheorems.Lacunary Λ a) (ha1 : ∀ n, 1 ≤ a n)
        (g : ℤ → ℂ),
        MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
          (fun n : ℕ => Work.KMTAreas.A7.Tle ρ l (fun ξ : ℝ =>
            if Work.KMTAreas.A7.core ρ C₀ l₁ l₂ k₁ 0 a n ∧
              Work.KMTAreas.A7.Farey Cρc ρ l₂ 0 a n
            then Work.KMTAreas.A7.varphitildeNt P d (Nat.floor (a n)) 0 t ξ -
              Work.KMTAreas.A7.varphitildeN d (Nat.floor (a n)) 0 ξ else 0) g x))
          p MeasureTheory.Measure.count
        ≤ ENNReal.ofReal (K * (1 + (l₂ : ℝ))) *
            MeasureTheory.eLpNorm g p MeasureTheory.Measure.count := by
  -- ## the endpoint exponent `2 k₀`
  set q : ℝ := p.toReal with hqdef
  have hq1 : 1 < q := by
    rw [hqdef, ← ENNReal.toReal_one]
    exact (ENNReal.toReal_lt_toReal ENNReal.one_ne_top (ne_of_lt hptop)).mpr hp
  obtain ⟨k₀, hk₀2, hk₀max, hk₀dual⟩ := exists_endpoint_exponent q hq1
  -- ## the narrow-symbol variational estimate at the two endpoints
  obtain ⟨Cρ, hCρpos, K0, hK0pos, hvar⟩ :=
    varEst_of_narrow_symbols_twoEndpoints ρ hρ hρ1 r hr p hp hptop k₀ hk₀2
      (by rw [← hqdef]; exact hk₀max) (by rw [← hqdef]; exact hk₀dual)
  -- ## the two-endpoint multiplier input for the difference family
  obtain ⟨C, hCpos, hCmult⟩ :=
    multBound_varphitildeNt_diff_two_endpoints_A P d hd hdP Λ hΛ k₀ hk₀2
  -- ## the narrowness constant
  obtain ⟨Cρc, hCρc3, hCρcCρ, hCρc1⟩ :
      ∃ Cρc : ℝ, 3 ≤ Cρc ∧ Cρ ≤ Cρc ∧ 1 < Cρc :=
    ⟨max Cρ 3 + 1, by linarith [le_max_right Cρ 3],
      by linarith [le_max_left Cρ 3], by linarith [le_max_right Cρ 3]⟩
  have hCρcnn : (0 : ℝ) ≤ Cρc := le_trans (by norm_num : (0 : ℝ) ≤ 3) hCρc3
  refine ⟨Cρc, hCρc3, K0 * C, mul_pos hK0pos hCpos, ?_⟩
  intro l l₂ l₁ k₁ hl t ht a ha ha1 g
  -- ## the narrowness height and its two properties
  have hCρ : GoodMajorArcs ρ Cρ l (fareyK Cρc ρ l₂) :=
    goodMajorArcs_fareyK hCρcCρ hCρpos.le hρ.le hl
  have hk : (2 : ℝ) ^ (fareyK Cρc ρ l₂) < 1 / 2 :=
    two_rpow_fareyK_lt_half hCρc1 hρ.le l₂
  -- ## the clipped difference family as Schwartz maps
  let Φ : ℕ → SchwartzMap ℝ ℂ := fun m => gFareyDiffSch P d ρ C₀ a Cρc l₁ l₂ k₁ m t
  have hΦcoe : ∀ m : ℕ, (Φ m : ℝ → ℂ)
      = fun ξ : ℝ => if core ρ C₀ l₁ l₂ k₁ 0 a m ∧ Farey Cρc ρ l₂ 0 a m then
          varphitildeNt P d (Nat.floor (a m)) 0 t ξ - varphitildeN d (Nat.floor (a m)) 0 ξ
          else 0 :=
    fun m => gFareyDiffSch_coe P d ρ C₀ a Cρc l₁ l₂ k₁ m t
  -- ## narrowness
  have hnarrow : ∀ m ξ, (Φ m : ℝ → ℂ) ξ ≠ 0 → ξ ∈ realArc (fareyK Cρc ρ l₂) := by
    intro m ξ hξ
    by_cases hc : core ρ C₀ l₁ l₂ k₁ 0 a m ∧ Farey Cρc ρ l₂ 0 a m
    · have hD : varphitildeNt P d (Nat.floor (a m)) 0 t ξ
          - varphitildeN d (Nat.floor (a m)) 0 ξ ≠ 0 := by
        simpa only [hΦcoe m, hc, and_self, if_true] using hξ
      by_cases h1 : varphitildeNt P d (Nat.floor (a m)) 0 t ξ = 0
      · refine varphitildeN_narrow_of_farey_A P d (by omega) hCρcnn (t := t) hc.2 ξ ?_
        intro h2
        rw [h1, h2, sub_zero] at hD
        exact hD rfl
      · exact varphitildeNt_narrow_of_farey_A P d (by omega) hCρcnn hc.2 ξ h1
    · have h0 : (0 : ℂ) ≠ 0 := by simpa only [hΦcoe m, hc, if_false] using hξ
      exact absurd rfl h0
  -- ## the two-endpoint multiplier bound for the clipped family
  have hMult : ∀ (U : Finset ℕ) (ω : ℕ → Bool),
      IsLqMultiplierBound (2 : ENNReal)
          (fun ξ : ℝ => ∑ m ∈ U, (if ω m then (1 : ℂ) else -1) * (Φ m : ℝ → ℂ) ξ) C ∧
        IsLqMultiplierBound (ENNReal.ofReal (2 * (k₀ : ℝ)))
          (fun ξ : ℝ => ∑ m ∈ U, (if ω m then (1 : ℂ) else -1) * (Φ m : ℝ → ℂ) ξ) C := by
    intro U ω
    have hsum : (fun ξ : ℝ => ∑ m ∈ U, (if ω m then (1 : ℂ) else -1) * (Φ m : ℝ → ℂ) ξ)
        = fun ξ : ℝ => ∑ m ∈ U.filter (fun m => core ρ C₀ l₁ l₂ k₁ 0 a m ∧
              Farey Cρc ρ l₂ 0 a m),
            (if ω m then (1 : ℂ) else -1) *
              (varphitildeNt P d (Nat.floor (a m)) 0 t ξ
                - varphitildeN d (Nat.floor (a m)) 0 ξ) := by
      funext ξ
      rw [Finset.sum_filter]
      refine Finset.sum_congr rfl (fun m _ => ?_)
      rw [hΦcoe m]
      by_cases hc : core ρ C₀ l₁ l₂ k₁ 0 a m ∧ Farey Cρc ρ l₂ 0 a m
      · simp only [hc, and_self, if_true]
      · simp only [hc, if_false, mul_zero]
    rw [hsum]
    refine ⟨?_, (hCmult t ht a ha ha1 (U.filter _) ω).2⟩
    rw [← ofReal_two_eq]
    exact (hCmult t ht a ha ha1 (U.filter _) ω).1
  -- ## the variational estimate at the chosen height
  have hmain := hvar l (fareyK Cρc ρ l₂) hCρ hk C hCpos Φ hnarrow hMult g
  -- ## transport the symbol family to the clipped difference family
  have hcongr : (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
        (fun n : ℕ => Tle ρ l (fun ξ : ℝ => if core ρ C₀ l₁ l₂ k₁ 0 a n ∧
            Farey Cρc ρ l₂ 0 a n then
            varphitildeNt P d (Nat.floor (a n)) 0 t ξ
              - varphitildeN d (Nat.floor (a n)) 0 ξ else 0) g x))
      = (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
        (fun n : ℕ => Tle ρ l (Φ n : ℝ → ℂ) g x)) := by
    funext x
    congr 1
    funext n
    rw [(hΦcoe n).symm]
  rw [hcongr]
  -- ## the constant bookkeeping `K0 (1+l) C ≤ (K0 C) (1+l₂)`
  refine hmain.trans ?_
  refine mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal ?_) bot_le
  have hlR : (l : ℝ) ≤ (l₂ : ℝ) := by exact_mod_cast hl
  have hK0C : (0 : ℝ) ≤ K0 * C := mul_nonneg hK0pos.le hCpos.le
  calc K0 * (1 + (l : ℝ)) * C = K0 * C * (1 + (l : ℝ)) := by ring
    _ ≤ K0 * C * (1 + (l₂ : ℝ)) := by nlinarith [hlR]

end

end Work.KMTAreas.A7
