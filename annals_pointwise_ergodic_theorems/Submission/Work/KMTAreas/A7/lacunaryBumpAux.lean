/-
# Auxiliary definitions for the linear lacunary variational estimate

The target `Work.KMTAreas.A7.lacunaryBumpVarEstimate` bounds the `r`-variation of the clipped family
`n ↦ Hcl ρ C₀ a l₁ l₂ k₁ k₂ t f n`.  The assembly splits that family by the **narrowness** of the
modulated bump: the Ionescu–Wainger endpoint bound
(`Work.KMTAreas.A7.varEst_of_narrow_symbols_twoEndpoints`) applies only on the scales where the
bump `varphiNt (⌊a n⌋) k₁ t` is supported in a single narrow arc `realArc k` with
`GoodMajorArcs ρ Cρ l k`, i.e. `k ≤ -Cρ 2^{ρl}`.

This module fixes the two predicates

* `Farey Cρc ρ l₁ k₁ a n` — the scale `n` is *narrow at level* `k = ⌊-Cρc 2^{ρl₁}⌋`:
  `k₁ - Log (⌊a n⌋) ≤ k`, which by `varphiNt_mem_realArc` puts the support of the bump inside
  `realArc k`; together with `Cρ ≤ Cρc` it also gives `GoodMajorArcs ρ Cρ l (fareyK Cρc ρ l₁)` for
  every `l ≤ l₁`;
* `Bads ρ C₀ Cρc l₁ l₂ k₁ k₂ a n` — the *bad* scales: core but not narrow.
-/
import Mathlib
import Submission.Work.KMTAreas.A7.lacunaryBumpGlue

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.KMTAreas.A7

noncomputable section

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal BigOperators
open PointwiseErgodicTheorems Submission.PointwiseErgodicTheorems
open Work.Analysis.IonescuWainger Work.Analysis.IWMultiplier
open Work.KMTContract Work.Analysis.EndVar

/-- The narrowness level `k = ⌊-Cρc · 2^{ρ l₁}⌋` attached to the arithmetic height `l₁` and the
narrowness constant `Cρc`. -/
noncomputable def fareyK (Cρc ρ : ℝ) (l₁ : ℕ) : ℤ :=
  ⌊-(Cρc * (2 : ℝ) ^ (ρ * (l₁ : ℝ)))⌋

/-- **The Farey (narrowness) condition.**  The scale `n` is *narrow at level* `fareyK Cρc ρ l₁`:
the modulated bump of height `k₁` at the physical scale `⌊a n⌋` is supported in
`realArc (fareyK Cρc ρ l₁)`. -/
def Farey (Cρc ρ : ℝ) (l₁ k₁ : ℕ) (a : ℕ → NNReal) (n : ℕ) : Prop :=
  (k₁ : ℤ) - logN (Nat.floor (a n)) ≤ fareyK Cρc ρ l₁

/-- **The bad scales**: core scales which are *not* narrow, i.e. on which the Ionescu–Wainger
endpoint bound cannot be invoked. -/
def Bads (ρ : ℝ) (C₀ : ℕ) (Cρc : ℝ) (l₁ l₂ k₁ k₂ : ℕ) (a : ℕ → NNReal) (n : ℕ) : Prop :=
  core ρ C₀ l₁ l₂ k₁ k₂ a n ∧ ¬ Farey Cρc ρ l₁ k₁ a n

instance fareyDecidable (Cρc ρ : ℝ) (l₁ k₁ : ℕ) (a : ℕ → NNReal) (n : ℕ) :
    Decidable (Farey Cρc ρ l₁ k₁ a n) := by unfold Farey; infer_instance

instance badsDecidable (ρ : ℝ) (C₀ : ℕ) (Cρc : ℝ) (l₁ l₂ k₁ k₂ : ℕ) (a : ℕ → NNReal)
    (n : ℕ) : Decidable (Bads ρ C₀ Cρc l₁ l₂ k₁ k₂ a n) := by unfold Bads; infer_instance

/-! ## Elementary properties of `fareyK` -/

theorem fareyK_le (Cρc ρ : ℝ) (l₁ : ℕ) :
    (fareyK Cρc ρ l₁ : ℝ) ≤ -(Cρc * (2 : ℝ) ^ (ρ * (l₁ : ℝ))) :=
  Int.floor_le _

/-- `GoodMajorArcs ρ Cρ l (fareyK Cρc ρ l₁)` for every `Cρ ≤ Cρc` and every `l ≤ l₁`. -/
theorem goodMajorArcs_fareyK {Cρ Cρc ρ : ℝ} (h : Cρ ≤ Cρc) (hCρ : 0 ≤ Cρ) (hρ : 0 ≤ ρ)
    {l l₁ : ℕ} (hl : l ≤ l₁) : GoodMajorArcs ρ Cρ l (fareyK Cρc ρ l₁) := by
  have hCρc0 : 0 ≤ Cρc := le_trans hCρ h
  have h2 : (2 : ℝ) ^ (ρ * (l : ℝ)) ≤ (2 : ℝ) ^ (ρ * (l₁ : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) (by
      have : (l : ℝ) ≤ (l₁ : ℝ) := by exact_mod_cast hl
      nlinarith)
  have h3 : Cρ * (2 : ℝ) ^ (ρ * (l : ℝ)) ≤ Cρc * (2 : ℝ) ^ (ρ * (l₁ : ℝ)) :=
    (mul_le_mul_of_nonneg_right h (Real.rpow_nonneg (by norm_num) _)).trans
      (mul_le_mul_of_nonneg_left h2 hCρc0)
  have h4 := fareyK_le Cρc ρ l₁
  simp only [GoodMajorArcs]
  linarith

/-- The narrowness level is below `-2` when `Cρc > 1`, hence `2^{fareyK} < 1/2`: this is the
hypothesis `hk` of `varEst_of_narrow_symbols_twoEndpoints`. -/
theorem two_rpow_fareyK_lt_half {Cρc ρ : ℝ} (hCρc : 1 < Cρc) (hρ : 0 ≤ ρ) (l₁ : ℕ) :
    (2 : ℝ) ^ (fareyK Cρc ρ l₁) < 1 / 2 := by
  have h2 : (1 : ℝ) ≤ (2 : ℝ) ^ (ρ * (l₁ : ℝ)) := Real.one_le_rpow (by norm_num) (by positivity)
  have hx : 1 < Cρc * (2 : ℝ) ^ (ρ * (l₁ : ℝ)) := by nlinarith
  have hk : fareyK Cρc ρ l₁ ≤ -2 := by
    rw [fareyK]
    have hlt : -(Cρc * (2 : ℝ) ^ (ρ * (l₁ : ℝ))) < ((-1 : ℤ) : ℝ) := by
      push_cast
      linarith
    have h' : ⌊-(Cρc * (2 : ℝ) ^ (ρ * (l₁ : ℝ)))⌋ < (-1 : ℤ) := Int.floor_lt.mpr hlt
    omega
  have h1 : (2 : ℝ) ^ (fareyK Cρc ρ l₁) ≤ (2 : ℝ) ^ (-2 : ℤ) :=
    zpow_le_zpow_right₀ (by norm_num) hk
  have h3 : (2 : ℝ) ^ (-2 : ℤ) = 1 / 4 := by norm_num
  rw [h3] at h1
  linarith

/-- On the Farey scales the modulated bump is narrow at level `fareyK Cρc ρ l₁`. -/
theorem narrow_of_farey {Cρc ρ : ℝ} {l₁ k₁ : ℕ} {a : ℕ → NNReal} {n : ℕ} {t : ℝ}
    (h : Farey Cρc ρ l₁ k₁ a n) :
    ∀ ξ : ℝ, varphiNt (Nat.floor (a n)) k₁ t ξ ≠ 0 → ξ ∈ realArc (fareyK Cρc ρ l₁) :=
  fun ξ hξ => varphiNt_mem_realArc k₁ (Nat.floor (a n)) t h hξ

/-! ## Monotonicity of the core condition -/

/-- `Log` is monotone. -/
theorem logN_monotone : Monotone logN := by
  intro N M hNM
  simp only [logN]
  exact Int.ofNat_le.mpr (Nat.log_mono_right (by omega))

/-- `LogLog` is monotone. -/
theorem logLogN_monotone : Monotone logLogN := by
  intro N M hNM
  simp only [logLogN]
  refine Nat.log_mono_right ?_
  exact Nat.add_le_add_right (Nat.log_mono_right (by omega)) 2

/-- The height scale `l_{(N)} = C₀ LogLog N` is monotone in `N`. -/
theorem heightScale_monotone (C₀ : ℕ) : Monotone (heightScale C₀) := by
  intro N M hNM
  simp only [heightScale]
  exact Nat.mul_le_mul_left _ (logLogN_monotone hNM)

/-- Monotonicity of `Int.toNat`. -/
theorem int_toNat_mono {a b : ℤ} (h : a ≤ b) : a.toNat ≤ b.toNat := by
  rcases le_total a 0 with ha | ha
  · rw [Int.toNat_of_nonpos ha]
    exact Nat.zero_le _
  · have ha' : 0 ≤ a := ha
    have hb' : 0 ≤ b := le_trans ha' h
    have h1 : (a.toNat : ℤ) = a := Int.toNat_of_nonneg ha'
    have h2 : (b.toNat : ℤ) = b := Int.toNat_of_nonneg hb'
    omega

/-- The core condition is monotone in the physical scale. -/
theorem core_mono_N {ρ : ℝ} {C₀ : ℕ} {l₁ l₂ k₁ k₂ : ℕ} {a : ℕ → NNReal} {n m : ℕ}
    (hN : Nat.floor (a n) ≤ Nat.floor (a m)) :
    core ρ C₀ l₁ l₂ k₁ k₂ a n → core ρ C₀ l₁ l₂ k₁ k₂ a m := by
  intro hn
  obtain ⟨hin, hcut, hmain⟩ := hn
  obtain ⟨hi1, hi2, hi3⟩ := hin
  obtain ⟨hm1, hm2⟩ := hmain
  have hhs : ((heightScale C₀ (Nat.floor (a n)) : ℕ) : ℤ) ≤
      ((heightScale C₀ (Nat.floor (a m)) : ℕ) : ℤ) := by
    exact_mod_cast heightScale_monotone C₀ hN
  have hln : logN (Nat.floor (a n)) ≤ logN (Nat.floor (a m)) := logN_monotone hN
  exact ⟨⟨le_trans hi1 hhs, le_trans hi2 hhs, le_trans hi3 hhs⟩, lt_of_lt_of_le hcut hN,
    le_trans hm1 (int_toNat_mono hln), le_trans hm2 (int_toNat_mono hln)⟩

/-- The Farey condition is upward closed in the index. -/
theorem farey_mono {Cρc ρ : ℝ} {l₁ k₁ : ℕ} {a : ℕ → NNReal} (hamono : Monotone a) {n m : ℕ}
    (hnm : n ≤ m) (h : Farey Cρc ρ l₁ k₁ a n) : Farey Cρc ρ l₁ k₁ a m := by
  have h2 := logN_monotone (Nat.floor_mono (hamono hnm))
  simp only [Farey] at h ⊢
  linarith

theorem core_mono {ρ : ℝ} {C₀ : ℕ} {l₁ l₂ k₁ k₂ : ℕ} {a : ℕ → NNReal}
    (hamono : Monotone a) {n m : ℕ} (hnm : n ≤ m) :
    core ρ C₀ l₁ l₂ k₁ k₂ a n → core ρ C₀ l₁ l₂ k₁ k₂ a m :=
  core_mono_N (Nat.floor_mono (hamono hnm))

/-- The clipping set `core ∧ Farey` is upward closed in the index, so it is `{n : n₀ ≤ n}` as soon
as it is nonempty. -/
theorem core_and_farey_iff_le {ρ : ℝ} {C₀ : ℕ} {Cρc : ℝ} {l₁ l₂ k₁ k₂ : ℕ} {a : ℕ → NNReal}
    (hamono : Monotone a) (h : ∃ n, core ρ C₀ l₁ l₂ k₁ k₂ a n ∧ Farey Cρc ρ l₁ k₁ a n) :
    ∃ n₀ : ℕ, ∀ n : ℕ, (core ρ C₀ l₁ l₂ k₁ k₂ a n ∧ Farey Cρc ρ l₁ k₁ a n) ↔ n₀ ≤ n := by
  classical
  refine ⟨Nat.find h, fun n => ⟨fun hn => ?_, fun hn => ?_⟩⟩
  · by_contra hcon
    rw [not_le] at hcon
    exact Nat.find_min h hcon hn
  · exact ⟨core_mono hamono hn (Nat.find_spec h).1, farey_mono hamono hn (Nat.find_spec h).2⟩

end

end Work.KMTAreas.A7
