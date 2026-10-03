/-
# The exceptional part of the large-scale half of the low case of area A6

`Work.KMTPlan.A6.LowExceptional` is the third of the three inputs of

  `Work.KMTPlan.A6.lcLarge_of_inputs`  (`Submission/Work/KMTPlan/A6/lowLargeScaled.lean`),

namely the estimate with the exponential gain `2^{-c·L}`, `L = max(max l₁ l₂)(max k₁ k₂)`, for the
*exceptional part* of the §5 columns: the contributions of the admissible large scales `N` which
are *not* in the main regime `k + 2u ≤ Log N` of the §6 functional calculus
(`Work.KMTAreas.A7.exceptionalPart ρ P C₀ a f g l₁ l₂ k₁ k₂`).

## The argument

The exceptional regime is *tiny*: if `N` is admissible (`l₁,l₂,k₁,k₂ ≤ l_(N) = C₀ LogLog N`),
large (`2^{2^u} < N`, `u = uScale ρ L`) and outside the main regime, then

  `N ≤ 2 ^ excBnd C₀`  and  `l₁,l₂,k₁,k₂ ≤ excBnd C₀`,

a bound depending on `C₀` alone, uniformly in `ρ ≤ 1`
(`Work.KMTAreas.A7.ExceptionalSupport`, proved in `KMTAreas/A7/ExceptionalSupport.lean`).

Consequently the exceptional part is supported on the *finitely many* lacunary scales with
`⌊a n⌋ ≤ 2^{excBnd C₀}`, and on each of them the parameters `l₁,l₂,k₁,k₂` run over a fixed finite
rectangle.  So:

* the number of contributing scales is at most `⌈(B₀+1)/log₂ Λ⌉ + 1`, `B₀ = excBnd C₀`;
* on each contributing scale the single-scale Hölder bound
  `‖Ã_N(F_N,G_N)‖_{ℓ¹} ≤ ‖F_N‖_{ℓ²}‖G_N‖_{ℓ²}` (`eLpNorm_AhalfR_le'` below, a form of (anf) which
  needs no `MemLp` hypothesis) together with the crude `ℓ²` bounds for the pieces
  (`Work.KMTPlan.A6.crude_Fpiece_of`, `crude_Gpiece_of`, obtained from the crude projection bound
  `KmtProjCrude` at `q = 2`) gives a bound `≤ C ‖f‖_{ℓ²}‖g‖_{ℓ²}` with a constant `C` independent
  of the quadruple;
* the `V^r`-norm of a family supported on finitely many scales is at most three times the sum of
  the `ℓ¹`-norms of its terms (`Work.KMTPlan.A6.eLpNorm_variationalNorm_one_le_tsum`), so the
  `ℓ¹`-norm of the variational norm of the exceptional part is at most a constant times
  `‖f‖₂‖g‖₂` — with a constant *independent of `L`*.

Finally the gain `2^{-cL}` comes for free: the estimate just proved has a constant independent of
`L`, while `L ≤ B₀` whenever the exceptional part is not identically zero; multiplying the
constant by `2^{cB₀}` therefore produces the required gain.  (For `L > B₀` the exceptional part
vanishes identically.)

The hypotheses `AreaA1` and `ImprovKMT P` of the statement are not needed by this argument: the
exceptional regime is handled by the crude single-scale bounds, the *deep* input `improv` being
used by the main-regime analysis (`A6/lowLargeScaled.lean`, `A6/lowSmallScaled.lean`).
-/
import Mathlib
import Submission.Work.KMTPlan.A6.LowLargeDefs
import Submission.Work.KMTPlan.A6.HHAux
import Submission.Work.KMTPlan.A6.kmtProj_l2_bound_finset
import Submission.Work.KMTPlan.A6.memLp_kmtProj
import Submission.Work.KMTPlan.A6.logN_le_of_le_pow
import Submission.Work.KMTAreas.A7.ExceptionalSupport
import Submission.Port.Aesm

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false

namespace Work.KMTPlan.A6

noncomputable section

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal BigOperators
open PointwiseErgodicTheorems
open Submission.PointwiseErgodicTheorems
open Work.Analysis.EndVar
open Work.KMTContract

/-! ## The lacunary scales below a fixed threshold are finite in number -/

/-- A sequence with `a (n+1) ≥ Λ * a n` and `a n ≥ 1` grows at least geometrically. -/
theorem lacunaryPowLe {Λ : ℝ≥0} {a : ℕ → ℝ≥0} (ha : ∀ n, Λ * a n ≤ a (n + 1))
    (ha1 : ∀ n, 1 ≤ a n) (n : ℕ) : Λ ^ n ≤ a n := by
  induction n with
  | zero => simpa using ha1 0
  | succ k ih =>
    calc Λ ^ (k + 1) = Λ * Λ ^ k := by ring
      _ ≤ Λ * a k := by gcongr
      _ ≤ a (k + 1) := ha k

/-- **The lacunary scales below a fixed threshold form a finite set.**  For a sequence with
`a (n+1) ≥ Λ a n`, `a n ≥ 1` and `Λ > 1`, the indices `n` with `⌊a n⌋ ≤ 2^B` are bounded by
`⌈(B+1)/log₂ Λ⌉ + 1`.

The *explicit* constant is what the assembly below needs, since the constant `K Λ` of
`LowBound` may depend on `Λ` (and on `ρ`, `C₀`) but not on the lacunary sequence `a`; the
existential form of the same statement is `Work.KMTPlan.A6.lacunary_smallIndex`
(`Submission/Work/KMTPlan/A6/lacunary_smallIndex.lean`). -/
theorem lacunarySmallIndex (Λ : ℝ≥0) (hΛ : 1 < Λ) (B : ℕ) :
    ∀ (a : ℕ → ℝ≥0), (∀ n, Λ * a n ≤ a (n + 1)) → (∀ n, 1 ≤ a n) →
      ∀ n : ℕ, Nat.floor (a n) ≤ 2 ^ B → n < ⌈(((B : ℝ) + 1) / Real.logb 2 (Λ : ℝ))⌉₊ + 1 := by
  intro a ha ha1 n hn
  have hΛR : (1 : ℝ) < (Λ : ℝ) := by exact_mod_cast hΛ
  have hlog : 0 < Real.logb 2 (Λ : ℝ) := Real.logb_pos (by norm_num) hΛR
  -- `a n < 2 ^ B + 1`
  have hlt : (a n : ℝ) < (2 : ℝ) ^ B + 1 := by
    have h1 : (a n : ℝ) < ((Nat.floor (a n) : ℕ) : ℝ) + 1 := by
      have h := Nat.lt_floor_add_one (a n)
      exact_mod_cast h
    have h2 : ((Nat.floor (a n) : ℕ) : ℝ) ≤ (2 : ℝ) ^ B := by
      exact_mod_cast hn
    linarith
  have h2B : (2 : ℝ) ^ B + 1 ≤ (2 : ℝ) ^ (B + 1) := by
    have h1 : (1 : ℝ) ≤ 2 ^ B := one_le_pow₀ (by norm_num)
    rw [pow_succ]
    linarith
  have hpow : (Λ : ℝ) ^ n ≤ (a n : ℝ) := by
    have h := lacunaryPowLe ha ha1 n
    exact_mod_cast h
  have hkey : ((n : ℝ)) * Real.logb 2 (Λ : ℝ) ≤ (B : ℝ) + 1 := by
    have h1 : (Λ : ℝ) ^ n ≤ (2 : ℝ) ^ (B + 1) := le_trans hpow (le_trans (le_of_lt hlt) h2B)
    have h2 := (Real.logb_le_logb (b := 2) (x := (Λ : ℝ) ^ n) (y := (2 : ℝ) ^ (B + 1))
      (by norm_num) (by positivity) (by positivity)).mpr h1
    rw [Real.logb_pow, Real.logb_pow, Real.logb_self_eq_one (by norm_num)] at h2
    push_cast at h2
    linarith
  have h3 : (n : ℝ) ≤ ((B : ℝ) + 1) / Real.logb 2 (Λ : ℝ) := by
    rw [le_div_iff₀ hlog]
    linarith
  have h4 : n ≤ ⌈(((B : ℝ) + 1) / Real.logb 2 (Λ : ℝ))⌉₊ := by
    exact_mod_cast le_trans h3 (Nat.le_ceil _)
  omega

/-! ## Two elementary comparison lemmas -/

/-- For the counting measure on `ℤ`, a function with vanishing `ℓ^p` seminorm vanishes
pointwise. -/
theorem eq_zero_of_eLpNorm_count_eq_zero {g : ℤ → ℂ} {p : ℝ≥0∞} (hp : p ≠ 0)
    (h : eLpNorm g p Measure.count = 0) : g = 0 := by
  have hae : AEStronglyMeasurable g (Measure.count : Measure ℤ) :=
    (measurable_of_countable g).aestronglyMeasurable
  have hae0 : g =ᵐ[Measure.count] 0 := (eLpNorm_eq_zero_iff hp).mp h
  have hnull : Measure.count {y : ℤ | g y ≠ 0} = 0 := by
    have h1 : ∀ᵐ y ∂(Measure.count), g y = 0 := hae0
    rw [MeasureTheory.ae_iff] at h1
    simpa using h1
  funext x
  by_contra hx
  have h1 : (Measure.count ({x} : Set ℤ)) ≤ Measure.count {y : ℤ | g y ≠ 0} :=
    MeasureTheory.measure_mono (Set.singleton_subset_iff.mpr hx)
  rw [Measure.count_singleton, hnull] at h1
  norm_num at h1

/-! ## The single-scale Hölder bound (anf) without `MemLp` hypotheses -/

/-- **(anf) at `(q₁,q₂,q) = (2,2,1)` for arbitrary inputs.**  The pointwise product structure of
`Ã_N` makes the single-scale bound `‖Ã_N(F,G)‖_{ℓ¹} ≤ ‖F‖_{ℓ²}‖G‖_{ℓ²}` valid for *all*
`F, G : ℤ → ℂ`: when both `ℓ²`-norms are finite this is Hölder's inequality, and when one of them
is infinite the only case needing an argument is the case where the other vanishes, in which the
corresponding function is zero (the counting measure has no non-empty null sets), so that
`Ã_N(F,G) = 0` as well. -/
theorem eLpNorm_AhalfR_le' (N : ℝ≥0) (P₁ P₂ : ℤ[X]) (F G : ℤ → ℂ) :
    eLpNorm (AhalfR TZ N P₁ P₂ F G) 1 Measure.count
      ≤ eLpNorm F 2 Measure.count * eLpNorm G 2 Measure.count := by
  by_cases hF : eLpNorm F 2 Measure.count = ⊤
  · by_cases hG : eLpNorm G 2 Measure.count = 0
    · have hG0 : G = 0 := eq_zero_of_eLpNorm_count_eq_zero (by norm_num) hG
      rw [hF, hG, hG0, AhalfR_zero_right, eLpNorm_zero]
      simp
    · rw [hF, ENNReal.top_mul hG]
      exact le_top
  · by_cases hG : eLpNorm G 2 Measure.count = ⊤
    · by_cases hF0 : eLpNorm F 2 Measure.count = 0
      · have hF0' : F = 0 := eq_zero_of_eLpNorm_count_eq_zero (by norm_num) hF0
        rw [hG, hF0, hF0', AhalfR_zero_left, eLpNorm_zero]
        simp
      · rw [hG, ENNReal.mul_top hF0]
        exact le_top
    · have hFmem : MemLp F 2 Measure.count :=
        MeasureTheory.memLp_iff.mpr (lt_top_iff_ne_top.mpr hF)
      have hGmem : MemLp G 2 Measure.count :=
        MeasureTheory.memLp_iff.mpr (lt_top_iff_ne_top.mpr hG)
      exact eLpNorm_AhalfR_le TZ measurePreserving_TZ N P₁ P₂ (q := 1) (q₁ := 2) (q₂ := 2)
        (by rw [ENNReal.inv_two_add_inv_two, inv_one]) le_rfl hFmem hGmem

/-! ## The exceptional part of the zero family -/

/-- A local form of `Work.KMTAreas.A7.exceptionalPart_eq_zero`, stated for the contract's
`excPart`. -/
theorem excPart_fun_eq_zero {ρ : ℝ} {P : ℤ[X]} {C₀ : ℕ} {a : ℕ → ℝ≥0} {f g : ℤ → ℂ}
    {l₁ l₂ k₁ k₂ n : ℕ}
    (h : ¬ Work.KMTAreas.A7.ExcPred ρ C₀ l₁ l₂ k₁ k₂ (Nat.floor (a n))) :
    (fun x : ℤ => excPart ρ P C₀ a f g l₁ l₂ k₁ k₂ n x) = 0 := by
  funext x
  show Work.KMTAreas.A7.exceptionalPart ρ P C₀ a f g l₁ l₂ k₁ k₂ n x = 0
  rw [Work.KMTAreas.A7.exceptionalPart_apply, if_neg h]

/-! ## The weights -/

/-- `lcWeight 1` is `2^{-L}`, `L = lcL l₁ l₂ k₁ k₂`. -/
theorem lcWeight_one_eq (l₁ l₂ k₁ k₂ : ℕ) :
    lcWeight 1 l₁ l₂ k₁ k₂ = (2 : ℝ) ^ (-(lcL l₁ l₂ k₁ k₂ : ℝ)) := by
  rw [lcWeight]
  have h : (Work.Analysis.EndVar.lmax l₁ l₂ (k₁ : ℤ) (k₂ : ℤ) : ℝ) = (lcL l₁ l₂ k₁ k₂ : ℝ) := by
    rw [← lcL_eq]
    push_cast
    ring
  rw [h, one_mul]

/-- The gain comparison `1 ≤ 2^{B} · 2^{-L}` for `L ≤ B`. -/
theorem one_le_two_pow_mul (B L : ℕ) (h : L ≤ B) :
    (1 : ℝ) ≤ (2 : ℝ) ^ (B : ℝ) * (2 : ℝ) ^ (-(L : ℝ)) := by
  rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
  have h1 : (B : ℝ) + -(L : ℝ) = ((B - L : ℕ) : ℝ) := by
    push_cast [Nat.cast_sub h]
    ring
  rw [h1, Real.rpow_natCast]
  exact one_le_pow₀ (by norm_num)

/-! ## The target -/

theorem LowExceptionalEstimate (P : Polynomial ℤ) (hd : 2 ≤ P.natDegree) (r : NNReal) (hr : 2 < r)
    (C₀ : ℕ) (hC₀ : 1 ≤ C₀) (hA1 : Work.KMTContract.AreaA1)
    (hI : Work.KMTContract.ImprovKMT P) :
    Work.KMTPlan.A6.LowExceptional P r C₀ := by
  have hr1 : (1 : ℝ≥0) ≤ r := le_of_lt (lt_trans (by norm_num) hr)
  have hbound : ∀ (ρ : ℝ) (S : Finset (ℕ × ℤ)), ∃ C : ℝ≥0, 0 < C ∧ ∀ p ∈ S, ∀ f : ℤ → ℂ,
      eLpNorm (kmtProj ρ p.1 p.2 f) 2 Measure.count ≤ (C : ℝ≥0∞) * eLpNorm f 2 Measure.count :=
    fun ρ S => kmtProj_l2_bound_finset ρ S
  unfold LowExceptional LowBound
  refine ⟨1, one_pos, 1, one_pos, ?_⟩
  intro ρ hρ hρ1
  set B₀ : ℕ := Work.KMTAreas.A7.excBnd C₀ with hB₀
  have hB₀one : 1 ≤ B₀ := by
    rw [hB₀, Work.KMTAreas.A7.excBnd]
    omega
  obtain ⟨CF, _hCFpos, hCF⟩ := crude_Fpiece_of hbound ρ B₀ (B₀ + 1)
  obtain ⟨CG, _hCGpos, hCG⟩ :=
    crude_Gpiece_of hbound ρ (P.natDegree : ℤ) (by positivity) (P.natDegree * B₀)
      (P.natDegree * (B₀ + 1))
  set Kid : ℝ≥0 → ℕ := fun Λ => ⌈(((B₀ : ℝ) + 1) / Real.logb 2 (Λ : ℝ))⌉₊ + 1 with hKid
  set Kf : ℝ≥0 → ℝ≥0 :=
    fun Λ => max ((3 : ℝ≥0) * (Kid Λ : ℝ≥0) * CF * CG * (2 : ℝ≥0) ^ B₀) 1 with hKf
  refine ⟨Kf, ?_⟩
  intro a Λ l₁ l₂ k₁ k₂ f g hΛ ha ha1 _hQ
  -- ### the growth form of lacunarity
  have hgr : ∀ n : ℕ, Λ * a n ≤ a (n + 1) := fun n =>
    le_of_lt ((lt_div_iff₀ (lt_of_lt_of_le zero_lt_one (ha1 n))).mp (ha n))
  -- ### the exceptional indices are bounded by `Kid Λ`
  have hidx : ∀ n : ℕ, Work.KMTAreas.A7.ExcPred ρ C₀ l₁ l₂ k₁ k₂ (Nat.floor (a n)) →
      n < Kid Λ := by
    intro n hn
    obtain ⟨hl₁, hl₂, hk₁, hk₂⟩ := Work.Analysis.EndVar.inIndexSet_iff_le.mp hn.1
    have hle := (Work.KMTAreas.A7.ExceptionalSupport C₀ ρ l₁ l₂ k₁ k₂ (Nat.floor (a n))
      hC₀ hρ hρ1 hl₁ hl₂ hk₁ hk₂ hn.2.1 hn.2.2).1
    rw [hKid]
    exact lacunarySmallIndex Λ hΛ B₀ a hgr ha1 n hle
  -- ### the per-scale bound
  set W : ℝ≥0∞ := ((CF * CG : ℝ≥0) : ℝ≥0∞) *
    (eLpNorm f 2 Measure.count * eLpNorm g 2 Measure.count) with hW
  have hper : ∀ n : ℕ,
      eLpNorm (fun x : ℤ => excPart ρ P C₀ a f g l₁ l₂ k₁ k₂ n x) 1 Measure.count ≤ W := by
    intro n
    by_cases h : Work.KMTAreas.A7.ExcPred ρ C₀ l₁ l₂ k₁ k₂ (Nat.floor (a n))
    · obtain ⟨hl₁, hl₂, hk₁, hk₂⟩ := Work.Analysis.EndVar.inIndexSet_iff_le.mp h.1
      obtain ⟨hNle, hb₁, hb₂, hb₃, hb₄⟩ :=
        Work.KMTAreas.A7.ExceptionalSupport C₀ ρ l₁ l₂ k₁ k₂ (Nat.floor (a n)) hC₀ hρ hρ1
          hl₁ hl₂ hk₁ hk₂ h.2.1 h.2.2
      have hlog : logN (Nat.floor (a n)) ≤ (B₀ : ℤ) := logN_le_of_le_pow hNle hB₀one
      have hlog0 : (0 : ℤ) ≤ logN (Nat.floor (a n)) := Work.Analysis.EndVar.logN_nonneg _
      -- the frequencies of the `F`-piece lie in the range of `crude_Fpiece_of`
      have hk₁Z : (k₁ : ℤ) ≤ (B₀ : ℤ) := by exact_mod_cast hb₃
      have hfr1 : -((B₀ + 1 : ℕ) : ℤ) ≤ (k₁ : ℤ) - logN (Nat.floor (a n)) - 1 := by omega
      have hfr2 : (k₁ : ℤ) - logN (Nat.floor (a n)) ≤ (B₀ : ℤ) := by omega
      have hFb := hCF l₁ k₁ (Nat.floor (a n)) f hb₁ hfr1 hfr2
      -- the frequencies of the `G`-piece
      have hd0 : (0 : ℤ) ≤ (P.natDegree : ℤ) := Int.natCast_nonneg _
      have hdl : l₂ ≤ P.natDegree * B₀ := by
        calc l₂ ≤ B₀ := hb₂
          _ ≤ P.natDegree * B₀ := Nat.le_mul_of_pos_left B₀ (by omega)
      have hk₂Z : (k₂ : ℤ) ≤ (B₀ : ℤ) := by exact_mod_cast hb₄
      have hgr2 : (P.natDegree : ℤ) * (-logN (Nat.floor (a n)) + (k₂ : ℤ))
          ≤ ((P.natDegree * B₀ : ℕ) : ℤ) := by
        have h1 : -logN (Nat.floor (a n)) + (k₂ : ℤ) ≤ (B₀ : ℤ) := by omega
        have h2 := mul_le_mul_of_nonneg_left h1 hd0
        push_cast
        simpa using h2
      have hgr1 : -((P.natDegree * (B₀ + 1) : ℕ) : ℤ)
          ≤ (P.natDegree : ℤ) * (-logN (Nat.floor (a n)) + (k₂ : ℤ)) - (P.natDegree : ℤ) := by
        have h1 : -((B₀ : ℤ)) ≤ -logN (Nat.floor (a n)) + (k₂ : ℤ) := by omega
        have h2 := mul_le_mul_of_nonneg_left h1 hd0
        have h3 : ((P.natDegree * (B₀ + 1) : ℕ) : ℤ)
            = (P.natDegree : ℤ) * (B₀ : ℤ) + (P.natDegree : ℤ) := by push_cast; ring
        rw [h3]
        linarith
      have hGb := hCG l₂ k₂ (Nat.floor (a n)) g hdl hgr1 hgr2
      -- the exceptional part is dominated by the column
      have hdom : ∀ x : ℤ, ‖excPart ρ P C₀ a f g l₁ l₂ k₁ k₂ n x‖ₑ
          ≤ ‖varpCol (kmtPj ρ) P P.natDegree C₀ a f g l₁ l₂ k₁ k₂ n x‖ₑ := by
        intro x
        show ‖Work.KMTAreas.A7.exceptionalPart ρ P C₀ a f g l₁ l₂ k₁ k₂ n x‖ₑ ≤ _
        rw [Work.KMTAreas.A7.exceptionalPart_apply, if_pos h,
          Work.Analysis.EndVar.varpCol_apply, if_pos h.1]
      calc eLpNorm (fun x : ℤ => excPart ρ P C₀ a f g l₁ l₂ k₁ k₂ n x) 1 Measure.count
          ≤ eLpNorm (fun x : ℤ =>
              varpCol (kmtPj ρ) P P.natDegree C₀ a f g l₁ l₂ k₁ k₂ n x) 1 Measure.count :=
            eLpNorm_mono_enorm (hf := by pw_aesm) hdom
        _ ≤ eLpNorm (Fpiece (kmtPj ρ) 0 l₁ (k₁ : ℤ) (Nat.floor (a n)) f) 2 Measure.count
              * eLpNorm (Gpiece (kmtPj ρ) (P.natDegree : ℤ) 0 l₂ (k₂ : ℤ)
                  (Nat.floor (a n)) g) 2 Measure.count := by
            rw [varpCol_eq_piece_of_indexSet (P := P) h.1]
            exact eLpNorm_AhalfR_le' (a n) X P _ _
        _ ≤ ((CF : ℝ≥0∞) * eLpNorm f 2 Measure.count)
              * ((CG : ℝ≥0∞) * eLpNorm g 2 Measure.count) := mul_le_mul' hFb hGb
        _ = W := by
            rw [hW, ENNReal.coe_mul]
            ring
    · have hzero : (fun x : ℤ => excPart ρ P C₀ a f g l₁ l₂ k₁ k₂ n x) = 0 :=
        excPart_fun_eq_zero h
      rw [hzero, eLpNorm_zero]
      exact zero_le
  -- ### the sum over the exceptional scales
  have hterm : ∀ n : ℕ, eLpNorm (fun x : ℤ => excPart ρ P C₀ a f g l₁ l₂ k₁ k₂ n x)
      1 Measure.count ≤ if n < Kid Λ then W else 0 := by
    intro n
    by_cases hn : n < Kid Λ
    · rw [if_pos hn]; exact hper n
    · rw [if_neg hn]
      have h : ¬ Work.KMTAreas.A7.ExcPred ρ C₀ l₁ l₂ k₁ k₂ (Nat.floor (a n)) :=
        fun hc => absurd (hidx n hc) hn
      rw [excPart_fun_eq_zero h, eLpNorm_zero]
  have hsum : (∑' n : ℕ,
        eLpNorm (fun x : ℤ => excPart ρ P C₀ a f g l₁ l₂ k₁ k₂ n x) 1 Measure.count)
      ≤ (Kid Λ : ℝ≥0∞) * W := by
    refine (ENNReal.tsum_le_tsum hterm).trans ?_
    have h1 : (∑' n : ℕ, (if n < Kid Λ then W else 0))
        = (∑' n : ℕ, (if n < Kid Λ then (1 : ℝ≥0∞) else 0)) * W := by
      rw [← ENNReal.tsum_mul_right]
      exact tsum_congr fun n => by split <;> simp
    rw [h1]
    exact mul_le_mul' (tsum_indicator_le (fun n : ℕ => n < Kid Λ) (Kid Λ)
      (fun n hn => hn)) le_rfl
  have hV : eLpNorm (fun x : ℤ => variationalNorm r
        (fun n : ℕ => excPart ρ P C₀ a f g l₁ l₂ k₁ k₂ n x)) 1 Measure.count
      ≤ 3 * ((Kid Λ : ℝ≥0∞) * W) :=
    (eLpNorm_variationalNorm_one_le_tsum hr1
      (fun n x => excPart ρ P C₀ a f g l₁ l₂ k₁ k₂ n x)).trans (mul_le_mul' le_rfl hsum)
  -- ### the two cases `L ≤ B₀` and `L > B₀`
  by_cases hL : lcL l₁ l₂ k₁ k₂ ≤ B₀
  · have hcoef : (((3 : ℝ≥0) * (Kid Λ : ℝ≥0) * CF * CG : ℝ≥0) : ℝ≥0∞)
        ≤ (Kf Λ : ℝ≥0∞) * ENNReal.ofReal (lcWeight 1 l₁ l₂ k₁ k₂) := by
      have hgain : (1 : ℝ≥0∞) ≤ ENNReal.ofReal ((2 : ℝ) ^ (B₀ : ℝ))
          * ENNReal.ofReal ((2 : ℝ) ^ (-(lcL l₁ l₂ k₁ k₂ : ℝ))) := by
        rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_mul (by positivity)]
        exact ENNReal.ofReal_le_ofReal (one_le_two_pow_mul B₀ _ hL)
      have hofB : ENNReal.ofReal ((2 : ℝ) ^ (B₀ : ℝ))
          = (((2 : ℝ≥0) ^ B₀ : ℝ≥0) : ℝ≥0∞) := by
        rw [Real.rpow_natCast, ENNReal.ofReal_pow (by norm_num)]
        norm_num
      have hmain : (((3 : ℝ≥0) * (Kid Λ : ℝ≥0) * CF * CG : ℝ≥0) : ℝ≥0∞)
            * ENNReal.ofReal ((2 : ℝ) ^ (B₀ : ℝ))
          = ((((3 : ℝ≥0) * (Kid Λ : ℝ≥0) * CF * CG * (2 : ℝ≥0) ^ B₀ : ℝ≥0)) : ℝ≥0∞) := by
        rw [hofB, ← ENNReal.coe_mul]
      have hKf' : ((((3 : ℝ≥0) * (Kid Λ : ℝ≥0) * CF * CG * (2 : ℝ≥0) ^ B₀ : ℝ≥0)) : ℝ≥0∞)
          ≤ (Kf Λ : ℝ≥0∞) := by
        rw [hKf]
        exact_mod_cast le_max_left _ 1
      calc (((3 : ℝ≥0) * (Kid Λ : ℝ≥0) * CF * CG : ℝ≥0) : ℝ≥0∞)
          = (((3 : ℝ≥0) * (Kid Λ : ℝ≥0) * CF * CG : ℝ≥0) : ℝ≥0∞) * 1 :=
            (mul_one _).symm
        _ ≤ (((3 : ℝ≥0) * (Kid Λ : ℝ≥0) * CF * CG : ℝ≥0) : ℝ≥0∞)
              * (ENNReal.ofReal ((2 : ℝ) ^ (B₀ : ℝ))
                * ENNReal.ofReal ((2 : ℝ) ^ (-(lcL l₁ l₂ k₁ k₂ : ℝ)))) :=
            mul_le_mul' le_rfl hgain
        _ = ((((3 : ℝ≥0) * (Kid Λ : ℝ≥0) * CF * CG * (2 : ℝ≥0) ^ B₀ : ℝ≥0)) : ℝ≥0∞)
              * ENNReal.ofReal ((2 : ℝ) ^ (-(lcL l₁ l₂ k₁ k₂ : ℝ))) := by
            rw [← mul_assoc, hmain]
        _ ≤ (Kf Λ : ℝ≥0∞) * ENNReal.ofReal ((2 : ℝ) ^ (-(lcL l₁ l₂ k₁ k₂ : ℝ))) :=
            mul_le_mul' hKf' le_rfl
        _ = (Kf Λ : ℝ≥0∞) * ENNReal.ofReal (lcWeight 1 l₁ l₂ k₁ k₂) := by
            rw [lcWeight_one_eq]
    calc eLpNorm (fun x : ℤ => variationalNorm r
          (fun n : ℕ => excPart ρ P C₀ a f g l₁ l₂ k₁ k₂ n x)) 1 Measure.count
        ≤ 3 * ((Kid Λ : ℝ≥0∞) * W) := hV
      _ = (((3 : ℝ≥0) * (Kid Λ : ℝ≥0) * CF * CG : ℝ≥0) : ℝ≥0∞)
            * (eLpNorm f 2 Measure.count * eLpNorm g 2 Measure.count) := by
          rw [hW]
          push_cast
          ring
      _ ≤ ((Kf Λ : ℝ≥0∞) * ENNReal.ofReal (lcWeight 1 l₁ l₂ k₁ k₂))
            * (eLpNorm f 2 Measure.count * eLpNorm g 2 Measure.count) :=
          mul_le_mul' hcoef le_rfl
      _ = (Kf Λ : ℝ≥0∞) * ENNReal.ofReal (lcWeight 1 l₁ l₂ k₁ k₂)
            * eLpNorm f 2 Measure.count * eLpNorm g 2 Measure.count := by ring_nf
  · -- `L > B₀`: the exceptional part vanishes identically
    have hzero : ∀ n : ℕ,
        eLpNorm (fun x : ℤ => excPart ρ P C₀ a f g l₁ l₂ k₁ k₂ n x) 1 Measure.count = 0 := by
      intro n
      have h : ¬ Work.KMTAreas.A7.ExcPred ρ C₀ l₁ l₂ k₁ k₂ (Nat.floor (a n)) := by
        intro hc
        obtain ⟨hl₁, hl₂, hk₁, hk₂⟩ := Work.Analysis.EndVar.inIndexSet_iff_le.mp hc.1
        obtain ⟨-, hb₁, hb₂, hb₃, hb₄⟩ :=
          Work.KMTAreas.A7.ExceptionalSupport C₀ ρ l₁ l₂ k₁ k₂ (Nat.floor (a n)) hC₀ hρ hρ1
            hl₁ hl₂ hk₁ hk₂ hc.2.1 hc.2.2
        exact hL (by rw [lcL]; exact max_le (max_le hb₁ hb₂) (max_le hb₃ hb₄))
      rw [excPart_fun_eq_zero h, eLpNorm_zero]
    refine (eLpNorm_variationalNorm_one_le_tsum hr1
      (fun n x => excPart ρ P C₀ a f g l₁ l₂ k₁ k₂ n x)).trans ?_
    rw [show (fun n : ℕ => eLpNorm (fun x : ℤ => excPart ρ P C₀ a f g l₁ l₂ k₁ k₂ n x)
        1 Measure.count) = fun _ => 0 from funext hzero, tsum_zero, mul_zero]
    exact zero_le

end

end Work.KMTPlan.A6
