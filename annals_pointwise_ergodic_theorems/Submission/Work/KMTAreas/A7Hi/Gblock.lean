import Mathlib
import Submission.Work.KMTAreas.A7Hi.varphitildeNtMultBound
import Submission.Work.KMTAreas.A7.lacunaryBumpAux
import Submission.Work.KMTAreas.A7.varphitildeNt_support_all

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace Work.KMTAreas.A7Hi

noncomputable section

open MeasureTheory Finset
open scoped ENNReal NNReal BigOperators
open PointwiseErgodicTheorems Submission.PointwiseErgodicTheorems
open Work.Analysis.IonescuWainger Work.Analysis.IWMultiplier
open Work.KMTAreas.A7

local notation "Circ" => Work.Analysis.IonescuWainger.Circle

/-! ## §1.  Narrowness of the `d`-fold bump on the Farey scales -/

/-- The `rpow`/`zpow` bridge for the support exponent `d (k₂ - Log N)`. -/
lemma gSupport_rpow_zpow (d k N : ℕ) :
    (2 : ℝ) ^ ((d : ℝ) * ((k : ℝ) - (Work.Analysis.EndVar.logN N : ℝ)))
      = (2 : ℝ) ^ ((d : ℤ) * ((k : ℤ) - Work.Analysis.EndVar.logN N)) := by
  rw [← Real.rpow_intCast (2 : ℝ) ((d : ℤ) * ((k : ℤ) - Work.Analysis.EndVar.logN N))]
  push_cast
  ring

/-- **Narrowness of the `d`-fold bump on the Farey scales.**  If `n` is a Farey scale for the
height `k₂` and the arithmetic level `l₂` (with `Cρc ≥ 0`), then the modulated `d`-fold bump
`φ̃_{N,t}` is supported in the narrow arc `realArc (fareyK Cρc ρ l₂)`. -/
theorem narrow_of_farey_g (P : Polynomial ℤ) (d : ℕ) (hd : 1 ≤ d) {Cρc ρ : ℝ} (hCρc : 0 ≤ Cρc)
    {l₂ k₂ : ℕ} {a : ℕ → NNReal} {n : ℕ} {t : ℝ} (h : Farey Cρc ρ l₂ k₂ a n) :
    ∀ ξ : ℝ, varphitildeNt P d (Nat.floor (a n)) k₂ t ξ ≠ 0 →
      ξ ∈ Work.Analysis.IonescuWainger.realArc (fareyK Cρc ρ l₂) := by
  intro ξ hξ
  have hsupp := varphitildeNt_support_all P d (Nat.floor (a n)) k₂ t ξ hξ
  rw [gSupport_rpow_zpow] at hsupp
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

/-! ## §2.  The two-endpoint multiplier bound for the `d`-fold bumps -/

/-- **The two-endpoint multiplier input for the `d`-fold bumps at `k₂ ≥ 1`.**  For every pair of
even exponents `2` and `2k₀` (`k₀ ≥ 2`) the signed sums `∑_{n ∈ U} ω n · φ̃_{⌊a n⌋,t}` satisfy the
continuous multiplier bound with the *same* constant `C (1 + d k₂)`, uniformly in `U`, in the signs
`ω`, and in the lacunary sequence `a`. -/
theorem multBound_varphitildeNt_two_endpoints (P : Polynomial ℤ) (d : ℕ) (hd : P.natDegree ≤ d)
    (Λ : NNReal) (hΛ : 1 < Λ) (k₀ : ℕ) (hk₀ : 2 ≤ k₀) :
    ∃ C : NNReal, 0 < C ∧ ∀ (k₂ : ℕ) (hk₂ : 1 ≤ k₂) (t : ℝ) (ht : t ∈ Set.Icc (1/2 : ℝ) 1)
      (a : ℕ → NNReal) (ha : PointwiseErgodicTheorems.Lacunary Λ a) (ha1 : ∀ n, 1 ≤ a n)
      (U : Finset ℕ) (ω : ℕ → Bool),
      IsLqMultiplierBound (ENNReal.ofReal (2 : ℝ))
          (fun ξ : ℝ => ∑ n ∈ U, (if ω n then (1 : ℂ) else -1) *
            varphitildeNt P d (Nat.floor (a n)) k₂ t ξ) (C * (1 + d * k₂)) ∧
        IsLqMultiplierBound (ENNReal.ofReal (2 * (k₀ : ℝ)))
          (fun ξ : ℝ => ∑ n ∈ U, (if ω n then (1 : ℂ) else -1) *
            varphitildeNt P d (Nat.floor (a n)) k₂ t ξ) (C * (1 + d * k₂)) := by
  have hk₀1 : (1 : ℝ) < 2 * (k₀ : ℝ) := by
    have h1 : (1 : ℝ) ≤ (k₀ : ℝ) := by exact_mod_cast (by omega : 1 ≤ k₀)
    linarith
  obtain ⟨C₂, hC₂pos, hC₂⟩ := varphitildeNt_mult_bound_k2pos_hi P d hd 2 (by norm_num) Λ hΛ
  obtain ⟨Ce, hCepos, hCe⟩ := varphitildeNt_mult_bound_k2pos_hi P d hd (2 * (k₀ : ℝ)) hk₀1 Λ hΛ
  refine ⟨max C₂ Ce, lt_max_of_lt_left hC₂pos, ?_⟩
  intro k₂ hk₂ t ht a ha ha1 U ω
  have hε : ∀ n : ℕ, ‖(if ω n then (1 : ℂ) else -1)‖ ≤ 1 := by
    intro n
    by_cases h : ω n <;> simp [h]
  have hkn : (0 : NNReal) ≤ (1 + d * k₂) := by positivity
  refine ⟨?_, ?_⟩
  · exact IsLqMultiplierBound.mono (hC₂ k₂ hk₂ t ht a ha ha1 U _ hε)
      (mul_le_mul_of_nonneg_right (le_max_left _ _) hkn)
  · exact IsLqMultiplierBound.mono (hCe k₂ hk₂ t ht a ha ha1 U _ hε)
      (mul_le_mul_of_nonneg_right (le_max_right _ _) hkn)

/-! ## §3.  The Schwartz packaging of the modulated `d`-fold bump -/

/-- `φ̃_N` is smooth to all orders. -/
lemma contDiff_varphitildeN_all (d N k : ℕ) :
    ContDiff ℝ (⊤ : ℕ∞) (varphitildeN d N k) := by
  unfold varphitildeN
  split_ifs with hk
  · exact contDiff_kmtEta_all.comp (contDiff_const.mul contDiff_id)
  · exact (contDiff_kmtEta_all.comp (contDiff_const.mul contDiff_id)).sub
      (contDiff_kmtEta_all.comp (contDiff_const.mul contDiff_id))

/-- The modulated `d`-fold bump is smooth to all orders. -/
lemma contDiff_varphitildeNt_g (P : Polynomial ℤ) (d N k₂ : ℕ) (t : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (varphitildeNt P d N k₂ t) := by
  rw [show varphitildeNt P d N k₂ t
      = fun ξ : ℝ => varphitildeN d N k₂ ξ * ee (PevalR P ((N : ℝ) * t) * ξ) from rfl]
  exact (contDiff_varphitildeN_all d N k₂).mul (contDiff_ee_all (PevalR P ((N : ℝ) * t)))

/-- The modulated `d`-fold bump has compact support. -/
lemma hasCompactSupport_varphitildeNt_g (P : Polynomial ℤ) (d N k₂ : ℕ) (t : ℝ) :
    HasCompactSupport (varphitildeNt P d N k₂ t) := by
  rw [show varphitildeNt P d N k₂ t
      = fun ξ : ℝ => varphitildeN d N k₂ ξ * ee (PevalR P ((N : ℝ) * t) * ξ) from rfl]
  exact (hasCompactSupport_varphitildeN d N k₂).mul_right

/-- The modulated `d`-fold bump as a Schwartz function. -/
noncomputable def varphitildeNtSch_g (P : Polynomial ℤ) (d N k₂ : ℕ) (t : ℝ) : SchwartzMap ℝ ℂ :=
  (hasCompactSupport_varphitildeNt_g P d N k₂ t).toSchwartzMap
    (contDiff_varphitildeNt_g P d N k₂ t)

lemma varphitildeNtSch_g_apply (P : Polynomial ℤ) (d N k₂ : ℕ) (t : ℝ) (ξ : ℝ) :
    varphitildeNtSch_g P d N k₂ t ξ = varphitildeNt P d N k₂ t ξ :=
  HasCompactSupport.toSchwartzMap_toFun _ _ ξ

lemma varphitildeNtSch_g_coe (P : Polynomial ℤ) (d N k₂ : ℕ) (t : ℝ) :
    (varphitildeNtSch_g P d N k₂ t : ℝ → ℂ) = varphitildeNt P d N k₂ t :=
  funext (varphitildeNtSch_g_apply P d N k₂ t)

/-! ## §3.  The Farey (narrow) part of the `g`-side linear estimate -/

/-- The `g`-side family of `d`-fold bumps clipped at the core-and-Farey scales. -/
noncomputable def fareyClippedSchG (P : Polynomial ℤ) (d : ℕ) (ρ : ℝ) (C₀ : ℕ) (a : ℕ → NNReal)
    (Cρc : ℝ) (l₁ l₂ k₁ k₂ : ℕ) (t : ℝ) (n : ℕ) : SchwartzMap ℝ ℂ :=
  if core ρ C₀ l₁ l₂ k₁ k₂ a n ∧ Farey Cρc ρ l₂ k₂ a n then
    varphitildeNtSch_g P d (Nat.floor (a n)) k₂ t else 0

@[simp] lemma fareyClippedSchG_apply (P : Polynomial ℤ) (d : ℕ) (ρ : ℝ) (C₀ : ℕ)
    (a : ℕ → NNReal) (Cρc : ℝ) (l₁ l₂ k₁ k₂ : ℕ) (t : ℝ) (n : ℕ) (ξ : ℝ) :
    (fareyClippedSchG P d ρ C₀ a Cρc l₁ l₂ k₁ k₂ t n : ℝ → ℂ) ξ
      = if core ρ C₀ l₁ l₂ k₁ k₂ a n ∧ Farey Cρc ρ l₂ k₂ a n then
          varphitildeNt P d (Nat.floor (a n)) k₂ t ξ else 0 := by
  rw [fareyClippedSchG]
  by_cases h : core ρ C₀ l₁ l₂ k₁ k₂ a n ∧ Farey Cρc ρ l₂ k₂ a n
  · rw [if_pos h, if_pos h, varphitildeNtSch_g_apply]
  · rw [if_neg h, if_neg h]
    simp

@[simp] lemma fareyClippedSchG_coe (P : Polynomial ℤ) (d : ℕ) (ρ : ℝ) (C₀ : ℕ)
    (a : ℕ → NNReal) (Cρc : ℝ) (l₁ l₂ k₁ k₂ : ℕ) (t : ℝ) (n : ℕ) :
    (fareyClippedSchG P d ρ C₀ a Cρc l₁ l₂ k₁ k₂ t n : ℝ → ℂ)
      = fun ξ : ℝ => if core ρ C₀ l₁ l₂ k₁ k₂ a n ∧ Farey Cρc ρ l₂ k₂ a n then
          varphitildeNt P d (Nat.floor (a n)) k₂ t ξ else 0 :=
  funext (fareyClippedSchG_apply P d ρ C₀ a Cρc l₁ l₂ k₁ k₂ t n)

/-- **The Farey part of the `g`-side linear lacunary variational estimate.** -/
theorem lacunaryBumpFareyPartBoundG (P : Polynomial ℤ) (d : ℕ) (hd : 2 ≤ d) (hdP : P.natDegree ≤ d)
    (C₀ : ℕ) (r : NNReal) (hr : 2 < r) (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (Λ : NNReal) (hΛ : 1 < Λ) (p : ENNReal) (hp : 1 < p) (hptop : p < ⊤) :
    ∃ Cρc : ℝ, 3 ≤ Cρc ∧ ∃ K : ℝ, 0 < K ∧
      ∀ (k₂ : ℕ) (hk₂ : 1 ≤ k₂) (l l₁ l₂ k₁ : ℕ) (hl : l ≤ l₂)
        (t : ℝ) (ht : t ∈ Set.Icc (1/2 : ℝ) 1)
        (a : ℕ → NNReal) (ha : PointwiseErgodicTheorems.Lacunary Λ a) (ha1 : ∀ n, 1 ≤ a n)
        (g : ℤ → ℂ),
        MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
          (fun n : ℕ => Tle ρ l (fun ξ : ℝ =>
            if core ρ C₀ l₁ l₂ k₁ k₂ a n ∧ Farey Cρc ρ l₂ k₂ a n
            then varphitildeNt P d (Nat.floor (a n)) k₂ t ξ else 0) g x))
          p MeasureTheory.Measure.count
        ≤ ENNReal.ofReal (K * (1 + (l₂ : ℝ)) * (1 + (k₂ : ℝ))) *
            MeasureTheory.eLpNorm g p MeasureTheory.Measure.count := by
  classical
  -- ## the endpoint exponent `k₀ ≥ 2` covering `p` and its Hölder dual
  have hq1 : 1 < p.toReal := by
    rw [← ENNReal.toReal_one]
    exact (ENNReal.toReal_lt_toReal ENNReal.one_ne_top (ne_of_lt hptop)).mpr hp
  obtain ⟨k₀, hk₀, hpmax, hpd⟩ := exists_endpoint_exponent p.toReal hq1
  -- ## the two inputs
  obtain ⟨Cρ, hCρpos, Kvar, hKvarpos, hmain⟩ :=
    varEst_of_narrow_symbols_twoEndpoints ρ hρ hρ1 r hr p hp hptop k₀ hk₀ hpmax hpd
  obtain ⟨C, hCpos, hCbound⟩ := multBound_varphitildeNt_two_endpoints P d hdP Λ hΛ k₀ hk₀
  refine ⟨max 3 Cρ, le_max_left _ _, Kvar * (C : ℝ) * (1 + (d : ℝ)),
    mul_pos (mul_pos hKvarpos (by exact_mod_cast hCpos)) (by positivity), ?_⟩
  intro k₂ hk₂ l l₁ l₂ k₁ hl t ht a ha ha1 g
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
  -- ## narrowness of the clipped family
  have hnarrow : ∀ n ξ, (fareyClippedSchG P d ρ C₀ a Cc l₁ l₂ k₁ k₂ t n : ℝ → ℂ) ξ ≠ 0 →
      ξ ∈ Work.Analysis.IonescuWainger.realArc (fareyK Cc ρ l₂) := by
    intro n ξ hξ
    have hξ' := hξ
    rw [fareyClippedSchG_apply] at hξ'
    by_cases h : core ρ C₀ l₁ l₂ k₁ k₂ a n ∧ Farey Cc ρ l₂ k₂ a n
    · rw [if_pos h] at hξ'
      exact narrow_of_farey_g P d (by omega) hCc0 h.2 ξ hξ'
    · rw [if_neg h] at hξ'
      exact absurd rfl hξ'
  -- ## the two-endpoint multiplier bound for the clipped family
  have hMult : ∀ (U : Finset ℕ) (ω : ℕ → Bool),
      IsLqMultiplierBound 2 (fun ξ : ℝ => ∑ n ∈ U, (if ω n then (1 : ℂ) else -1) *
          (fareyClippedSchG P d ρ C₀ a Cc l₁ l₂ k₁ k₂ t n : ℝ → ℂ) ξ) M ∧
      IsLqMultiplierBound (ENNReal.ofReal (2 * (k₀ : ℝ)))
        (fun ξ : ℝ => ∑ n ∈ U, (if ω n then (1 : ℂ) else -1) *
          (fareyClippedSchG P d ρ C₀ a Cc l₁ l₂ k₁ k₂ t n : ℝ → ℂ) ξ) M := by
    intro U ω
    have hU : (fun ξ : ℝ => ∑ n ∈ U, (if ω n then (1 : ℂ) else -1) *
          (fareyClippedSchG P d ρ C₀ a Cc l₁ l₂ k₁ k₂ t n : ℝ → ℂ) ξ)
        = (fun ξ : ℝ =>
            ∑ n ∈ U.filter (fun n => core ρ C₀ l₁ l₂ k₁ k₂ a n ∧ Farey Cc ρ l₂ k₂ a n),
              (if ω n then (1 : ℂ) else -1) *
                varphitildeNt P d (Nat.floor (a n)) k₂ t ξ) := by
      funext ξ
      rw [Finset.sum_filter]
      refine Finset.sum_congr rfl (fun n _ => ?_)
      rw [fareyClippedSchG_apply]
      by_cases h : core ρ C₀ l₁ l₂ k₁ k₂ a n ∧ Farey Cc ρ l₂ k₂ a n <;> simp [h]
    obtain ⟨hb2, hbe⟩ := hCbound k₂ hk₂ t ht a ha ha1
      (U.filter (fun n => core ρ C₀ l₁ l₂ k₁ k₂ a n ∧ Farey Cc ρ l₂ k₂ a n)) ω
    rw [ofReal_two_eq] at hb2
    exact ⟨by rw [hU]; exact hb2, by rw [hU]; exact hbe⟩
  -- ## the narrow-symbol variational estimate
  have hgood : GoodMajorArcs ρ Cρ l (fareyK Cc ρ l₂) :=
    goodMajorArcs_fareyK hCρle hCρ0 hρ.le hl
  have hk : (2 : ℝ) ^ (fareyK Cc ρ l₂) < 1 / 2 := two_rpow_fareyK_lt_half hCc1 hρ.le l₂
  have hres := hmain l (fareyK Cc ρ l₂) hgood hk M hMpos
    (fareyClippedSchG P d ρ C₀ a Cc l₁ l₂ k₁ k₂ t) hnarrow hMult g
  -- ## rewriting the clipped family back to the explicit `if`
  have hInt : (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
        (fun n : ℕ => Tle ρ l (fun ξ : ℝ =>
          if core ρ C₀ l₁ l₂ k₁ k₂ a n ∧ Farey Cc ρ l₂ k₂ a n
          then varphitildeNt P d (Nat.floor (a n)) k₂ t ξ else 0) g x))
      = (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
        (fun n : ℕ => Tle ρ l
          (fareyClippedSchG P d ρ C₀ a Cc l₁ l₂ k₁ k₂ t n : ℝ → ℂ) g x)) := by
    funext x
    refine congrArg (fun u : ℕ → ℂ => PointwiseErgodicTheorems.variationalNorm r u) ?_
    funext n
    rw [fareyClippedSchG_coe]
  rw [hInt]
  -- ## the constant bookkeeping
  refine hres.trans ?_
  refine mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal ?_) zero_le
  have hMR : (M : ℝ) = (C : ℝ) * (1 + (d : ℝ) * (k₂ : ℝ)) := by
    rw [hMdef]; push_cast; ring
  have hlR : (1 + (l : ℝ)) ≤ (1 + (l₂ : ℝ)) := by
    have hl' : (l : ℝ) ≤ (l₂ : ℝ) := by exact_mod_cast hl
    linarith
  have hCnn : (0 : ℝ) ≤ (C : ℝ) := by positivity
  have hk₂nn : (0 : ℝ) ≤ 1 + (k₂ : ℝ) := by positivity
  have hdnn : (0 : ℝ) ≤ 1 + (d : ℝ) := by positivity
  have hnn : (0 : ℝ) ≤ Kvar * (C : ℝ) * (1 + (d : ℝ)) :=
    mul_nonneg (mul_nonneg hKvarpos.le hCnn) hdnn
  have hMle : (M : ℝ) ≤ (C : ℝ) * (1 + (d : ℝ)) * (1 + (k₂ : ℝ)) := by
    rw [hMR]
    have h2 : (1 : ℝ) + (d : ℝ) * (k₂ : ℝ) ≤ (1 + (d : ℝ)) * (1 + (k₂ : ℝ)) := by
      nlinarith [Nat.cast_nonneg (α := ℝ) d, Nat.cast_nonneg (α := ℝ) k₂]
    calc (C : ℝ) * (1 + (d : ℝ) * (k₂ : ℝ))
        ≤ (C : ℝ) * ((1 + (d : ℝ)) * (1 + (k₂ : ℝ))) :=
          mul_le_mul_of_nonneg_left h2 hCnn
      _ = (C : ℝ) * (1 + (d : ℝ)) * (1 + (k₂ : ℝ)) := by ring
  calc Kvar * (1 + (l : ℝ)) * (M : ℝ)
      ≤ Kvar * (1 + (l₂ : ℝ)) * ((C : ℝ) * (1 + (d : ℝ)) * (1 + (k₂ : ℝ))) := by
        refine mul_le_mul ?_ hMle (by positivity) ?_
        · exact mul_le_mul_of_nonneg_left hlR hKvarpos.le
        · exact mul_nonneg hKvarpos.le (by positivity)
    _ = Kvar * (C : ℝ) * (1 + (d : ℝ)) * (1 + (l₂ : ℝ)) * (1 + (k₂ : ℝ)) := by ring

end

end Work.KMTAreas.A7Hi
