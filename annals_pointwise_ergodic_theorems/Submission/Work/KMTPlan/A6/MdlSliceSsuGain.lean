import Mathlib
import Submission.Work.A6Big.Defs
import Submission.Work.KMTPlan.A6.ssuCollapse
import Submission.Work.KMTPlan.A6.MdlPktMemLp
import Submission.Work.KMTPlan.A6.Tle_mdlF_eq_iwConv
import Submission.Work.KMTPlan.A6.varphitildeNtjPointwise
import Submission.Work.KMTPlan.A6.varphitildeNtj_support
import Submission.Work.KMTPlan.A6Bile.BtwistSumBandPiece
import Submission.Work.KMTPlan.A6Bile.Btwist_eLpNorm_le_crude
-- (2026-10-03) see the note in `MdlSliceGband.lean`: `MdlSliceCoreGainBig` now re-exports the
-- copied §8 chain of `Submission/Work/A6Big/` (declaring the same names as this file's own), so the
-- definitions `mdlSliceF/G` are taken from their new home `Submission.Work.A6Big.Defs` instead.

namespace Work.KMTPlan.A6

noncomputable section

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal BigOperators
open Work.Analysis.IonescuWainger Work.Analysis.IWMultiplier Work.KMTAreas.A7
open Work.Analysis.EndVar

/-! ## Elementary helpers -/

/-- `1 ≤ uScale ρ L` for `ρ ≥ 0`. -/
lemma one_le_uScale_ssu (ρ : ℝ) (hρ : 0 ≤ ρ) (L : ℕ) : 1 ≤ uScale ρ L := by
  rw [Work.KMTAreas.A7.uScale, Work.Analysis.EndVar.scaleCount]
  have h1 : (1 : ℝ) ≤ (2 : ℝ) ^ (2 * ρ * (L : ℝ)) :=
    Real.one_le_rpow (by norm_num) (by positivity)
  have h3 : (1 : ℤ) ≤ ⌊(2 : ℝ) ^ (2 * ρ * (L : ℝ))⌋ := by
    rw [Int.le_floor]; exact_mod_cast h1
  have h4 : (1 : ℕ) ≤ ⌊(2 : ℝ) ^ (2 * ρ * (L : ℝ))⌋.toNat := by omega
  simpa only [Nat.cast_one, one_mul] using h4

/-- `2^c ≤ 1/2` for `c ≤ -1`. -/
lemma two_zpow_le_half_ssu {c : ℤ} (hc : c ≤ -1) : (2 : ℝ) ^ c ≤ 1 / 2 := by
  have h2 : (2 : ℝ) ≤ (2 : ℝ) ^ (-c) := by
    calc (2 : ℝ) = (2 : ℝ) ^ (1 : ℤ) := by norm_num
      _ ≤ (2 : ℝ) ^ (-c) := zpow_le_zpow_right₀ (by norm_num) (by omega)
  have h := one_div_le_one_div_of_le (show (0 : ℝ) < 2 by norm_num) h2
  have h2c : (2 : ℝ) ^ c = 1 / (2 : ℝ) ^ (-c) := by
    rw [one_div, zpow_neg, inv_inv]
  rw [h2c]
  exact h

/-- Monotonicity of `SupportedInArc` in the scale. -/
lemma supportedInArc_mono_ssu {k k' : ℤ} (h : k ≤ k') {Φ : Circle → ℂ}
    (hΦ : SupportedInArc k Φ) : SupportedInArc k' Φ :=
  fun ξ hξ => let ⟨θ, hθ, hθ'⟩ := hΦ ξ hξ; ⟨θ, realArc_mono h hθ, hθ'⟩

/-- A bump supported in the closed ball of radius `2^K` has periodisation supported in the arc
`ℝ_{≤K}`. -/
lemma supportedInArc_periodize_of_abs {K : ℤ} {φ : ℝ → ℂ}
    (h : ∀ ξ : ℝ, φ ξ ≠ 0 → |ξ| ≤ (2 : ℝ) ^ K) :
    SupportedInArc K (periodize φ) := by
  refine supportedInArc_periodize_of_arc (fun x hx => ?_)
  rw [realArc, Set.mem_Icc]
  exact ⟨neg_le_of_abs_le (h x hx), le_of_abs_le (h x hx)⟩

/-! ## The functional calculus of the packet carriers -/

/-- **The functional calculus in general form.**  If `Φ = periodize φ` is bounded, supported in
the arc `ℝ_{≤c-1}`, the arithmetic frequencies of height `≤ l` are non-aliasing at scale `c`, and
`2^c ≤ 1/2`, then the composition of the height-`≤ l` multiplier with symbol `φ` with the narrow
exact-height shell `piExact l c` is the exact-height multiplier `Tm ρ l φ`. -/
theorem Tle_piExact_eq_Tm_ssu (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (l : ℕ) (c : ℤ)
    (φ : ℝ → ℂ) {f : ℤ → ℂ} (hφmem : MemLp (periodize φ) ⊤ circleMeasure)
    (hf : MemLp f 2 Measure.count) (hcplt : (2 : ℝ) ^ c ≤ 1 / 2)
    (hnA : NonAliasing c (iwArithFreqs ρ l))
    (hΦ : SupportedInArc (c - 1) (periodize φ)) :
    Tle ρ l φ (Work.Analysis.EndVar.piExact (Work.KMTContract.kmtPj ρ) l c f) = Tm ρ l φ f := by
  have hle : c - 1 ≤ c := by omega
  have hC1 := Tle_piExact_eq_iwConv' ρ hρ hρ1 l c φ hφmem hf hnA
    (supportedInArc_mono_ssu hle hΦ)
  have hfun : (fun ξ : Circle => periodize φ ξ
        * periodize (etaCut Work.KMTContract.kmtEta c) ξ)
      = periodize φ := by
    funext ξ
    by_cases hξ : periodize φ ξ = 0
    · rw [hξ, zero_mul]
    · obtain ⟨θ, hθ, rfl⟩ := hΦ ξ hξ
      have hθ' : |θ| ≤ (2 : ℝ) ^ c / 2 := by
        have h2 : |θ| ≤ (2 : ℝ) ^ (c - 1) := by
          have hθ'' := hθ
          rw [realArc, Set.mem_Icc] at hθ''
          rw [abs_le]
          exact ⟨by linarith [hθ''.1], by linarith [hθ''.2]⟩
        have he : (2 : ℝ) ^ (c - 1) = (2 : ℝ) ^ c / 2 := by
          rw [zpow_sub₀ (show (2 : ℝ) ≠ 0 by norm_num), zpow_one]
        rwa [he] at h2
      rw [Phi_eq_one_of_small hcplt hθ', mul_one]
  rw [hC1, hfun]
  rfl

/-- **The `f`-side functional calculus for the concrete shell `mdlF`.** -/
theorem Tle_mdlF_eq_Tm_ssu (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (u l : ℕ) (hu : 1 ≤ u)
    (φ : ℝ → ℂ) {f : ℤ → ℂ} (hφmem : MemLp (periodize φ) ⊤ circleMeasure)
    (hf : MemLp f 2 Measure.count)
    (hnA : NonAliasing (-(u : ℤ)) (iwArithFreqs ρ l))
    (hΦ : SupportedInArc (-(u : ℤ) - 1) (periodize φ)) :
    Tle ρ l φ (mdlF ρ u l f) = Tm ρ l φ f := by
  have hcplt : (2 : ℝ) ^ (-(u : ℤ)) ≤ 1 / 2 := two_zpow_le_half_ssu (by omega)
  rw [mdlF]
  exact Tle_piExact_eq_Tm_ssu ρ hρ hρ1 l (-(u : ℤ)) φ hφmem hf hcplt hnA hΦ

/-- **The `g`-side functional calculus for the concrete shell `mdlG`.** -/
theorem Tle_mdlG_eq_Tm_ssu (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (P : Polynomial ℤ) (u l : ℕ)
    (hd : 1 ≤ P.natDegree) (hu : 1 ≤ u)
    (φ : ℝ → ℂ) {g : ℤ → ℂ} (hφmem : MemLp (periodize φ) ⊤ circleMeasure)
    (hg : MemLp g 2 Measure.count)
    (hnA : NonAliasing (-((P.natDegree : ℤ) * (u : ℤ))) (iwArithFreqs ρ l))
    (hΦ : SupportedInArc (-((P.natDegree : ℤ) * (u : ℤ)) - 1) (periodize φ)) :
    Tle ρ l φ (mdlG ρ P u l g) = Tm ρ l φ g := by
  have hdz : (1 : ℤ) ≤ (P.natDegree : ℤ) := by exact_mod_cast hd
  have huz : (1 : ℤ) ≤ (u : ℤ) := by exact_mod_cast hu
  have hcplt : (2 : ℝ) ^ (-((P.natDegree : ℤ) * (u : ℤ))) ≤ 1 / 2 :=
    two_zpow_le_half_ssu (by nlinarith)
  rw [mdlG]
  exact Tle_piExact_eq_Tm_ssu ρ hρ hρ1 l (-((P.natDegree : ℤ) * (u : ℤ))) φ hφmem hg
    hcplt hnA hΦ

/-! ## The narrowness of the two modified bumps -/

/-- **The `f`-side modified bump is supported in the arc `ℝ_{≤K}` as soon as
`k - Log N ≤ K`.** -/
lemma varphiNtj_arc_ssu (N k : ℕ) (j : ℤ) (t : ℝ) (K : ℤ)
    (hlog : (k : ℤ) - logN N ≤ K) :
    ∀ ξ : ℝ, varphiNtj N k j t ξ ≠ 0 → |ξ| ≤ (2 : ℝ) ^ K := by
  intro ξ hξ
  have h := varphiNtj_support_le_pkt N k j t ξ hξ
  have hExp : (k : ℝ) - (logN N : ℝ) ≤ (K : ℝ) := by
    calc (k : ℝ) - (logN N : ℝ) = ((((k : ℤ) - logN N : ℤ)) : ℝ) := by push_cast; ring
      _ ≤ (K : ℝ) := by exact_mod_cast hlog
  have hb : (2 : ℝ) ^ ((k : ℝ) - (logN N : ℝ)) ≤ (2 : ℝ) ^ ((K : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) hExp
  rw [Real.rpow_intCast] at hb
  exact le_trans h hb

/-- **The `g`-side modified bump is supported in the arc `ℝ_{≤K}` as soon as
`d (k - Log N) ≤ K`.** -/
lemma varphitildeNtj_arc_ssu (P : Polynomial ℤ) (hd : 1 ≤ P.natDegree) (N k : ℕ) (j : ℤ)
    (t : ℝ) (K : ℤ) (hlog : (P.natDegree : ℤ) * ((k : ℤ) - logN N) ≤ K) :
    ∀ ξ : ℝ, varphitildeNtj P N k j t ξ ≠ 0 → |ξ| ≤ (2 : ℝ) ^ K := by
  intro ξ hξ
  obtain ⟨h1, -⟩ := varphitildeNtj_support P hd N k j t ξ hξ
  set e : ℝ := (P.natDegree : ℝ) * ((logN N : ℝ) - (k : ℝ)) with he
  have hpos : 0 < (2 : ℝ) ^ e := Real.rpow_pos_of_pos (by norm_num) _
  have habs : |ξ| ≤ (2 : ℝ) ^ (-e) := by
    rw [Real.rpow_neg (by norm_num), inv_eq_one_div, le_div_iff₀ hpos]
    simpa only [mul_comm] using h1
  have hexp : -e ≤ (K : ℝ) := by
    have he' : -e = (((P.natDegree : ℤ) * ((k : ℤ) - logN N) : ℤ) : ℝ) := by
      rw [he]; push_cast; ring
    rw [he']
    exact_mod_cast hlog
  have hb : (2 : ℝ) ^ (-e) ≤ (2 : ℝ) ^ ((K : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp
  rw [Real.rpow_intCast] at hb
  exact le_trans habs hb

/-- `MemLp (periodize (φ̃_{N,k,j})) ⊤` for the `g`-side modified bump. -/
theorem memLp_periodize_varphitildeNtj_ssu (P : Polynomial ℤ) (hd : 2 ≤ P.natDegree)
    (N k₂ : ℕ) (j₂ : ℤ) (t : ℝ) (hk : k₂ ≠ 0 ∨ 0 ≤ j₂) (hN : 1 ≤ N)
    (ht : t ∈ Set.Icc (1 / 2 : ℝ) 1) (hj : j₂ ∈ ({-1, 0, 1} : Finset ℤ)) :
    MemLp (periodize (varphitildeNtj P N k₂ j₂ t)) ⊤ circleMeasure := by
  obtain ⟨hbd, -⟩ := varphitildeNtjPointwise P hd
  obtain ⟨Cb, hCbpos, hCb⟩ := hbd
  obtain ⟨S, hSpos, hS⟩ := varphitildeNtj_bounds P N k₂ j₂ hk
  obtain ⟨hScd, hScs, -, -⟩ := hS t ht
  obtain ⟨R, hR⟩ := Work.KMTAreas.A7.exists_abs_le_of_hasCompactSupport hScs
  refine memLp_periodize hScd.continuous.measurable (R := max R 0) (C := Cb)
    (le_max_right R 0) ?_ ?_
  · intro x hx
    exact hR x (le_of_lt (lt_of_le_of_lt (le_max_left R 0) hx))
  · intro x
    have hnot : ¬(k₂ = 0 ∧ j₂ = -1) := by
      rintro ⟨h1, h2⟩
      rcases hk with h | h
      · exact h h1
      · omega
    exact hCb N k₂ j₂ t hj hnot hN x

/-! ## The threshold for non-aliasing at scale `-uScale ρ L` -/

/-- A power of two eventually dominates a positive constant. -/
lemma exists_two_rpow_gt_ssu (ρ : ℝ) (hρ : 0 < ρ) (C : ℝ) (hC : 0 < C) :
    ∃ B : ℕ, ∀ L : ℕ, B ≤ L → C < (2 : ℝ) ^ (ρ * (L : ℝ)) := by
  refine ⟨⌈Real.logb 2 C / ρ⌉₊ + 1, ?_⟩
  intro L hL
  have hLe : ((⌈Real.logb 2 C / ρ⌉₊ : ℕ) : ℝ) < (L : ℝ) := by
    have h1 : ⌈Real.logb 2 C / ρ⌉₊ + 1 ≤ L := hL
    have h2 : ((⌈Real.logb 2 C / ρ⌉₊ + 1 : ℕ) : ℝ) ≤ (L : ℝ) := by exact_mod_cast h1
    push_cast at h2
    linarith
  have hx : Real.logb 2 C / ρ < (L : ℝ) := lt_of_le_of_lt (Nat.le_ceil _) hLe
  have hlt : Real.logb 2 C < ρ * (L : ℝ) := by
    have hmul := mul_lt_mul_of_pos_left hx hρ
    rwa [mul_div_cancel₀ (Real.logb 2 C) (ne_of_gt hρ)] at hmul
  rw [← Real.rpow_logb (by norm_num : (0 : ℝ) < 2) (by norm_num : (2 : ℝ) ≠ 1) hC]
  exact Real.rpow_lt_rpow_of_exponent_lt (by norm_num : (1 : ℝ) < 2) hlt

/-- `2^{2ρL} - 1 ≤ uScale ρ L`. -/
lemma rpow_sub_one_le_uScale_ssu (ρ : ℝ) (hρ : 0 ≤ ρ) (L : ℕ) :
    (2 : ℝ) ^ (2 * ρ * (L : ℝ)) - 1 ≤ (uScale ρ L : ℝ) := by
  set x : ℝ := (2 : ℝ) ^ (2 * ρ * (L : ℝ)) with hx
  have hx1 : 1 ≤ x := Real.one_le_rpow (by norm_num) (by positivity)
  have hfl : x - 1 < (⌊x⌋ : ℝ) := by
    have := Int.lt_floor_add_one x
    linarith
  have hcast : (uScale ρ L : ℝ) = (⌊x⌋ : ℝ) := by
    rw [Work.KMTAreas.A7.uScale, Work.Analysis.EndVar.scaleCount, ← hx]
    simp only [Nat.cast_one, one_mul]
    have h0 : (0 : ℤ) ≤ ⌊x⌋ := by
      rw [Int.le_floor]; push_cast; linarith
    exact_mod_cast Int.toNat_of_nonneg h0
  rw [hcast]; linarith

/-- `2^{2ρL} ≤ 2 · uScale ρ L`. -/
lemma two_mul_uScale_ge_rpow_ssu (ρ : ℝ) (hρ : 0 ≤ ρ) (L : ℕ) :
    (2 : ℝ) ^ (2 * ρ * (L : ℝ)) ≤ 2 * (uScale ρ L : ℝ) := by
  have h1 := rpow_sub_one_le_uScale_ssu ρ hρ L
  have h2 : (1 : ℝ) ≤ (uScale ρ L : ℝ) := by
    have := one_le_uScale_ssu ρ hρ L
    exact_mod_cast this
  linarith

/-- **Non-aliasing at scale `-(uScale ρ L)`.** -/
theorem MdlSliceNonAliasing_ssu (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) :
    ∃ B : ℕ, ∀ L l : ℕ, B ≤ L → l ≤ L →
      NonAliasing (-(uScale ρ L : ℤ)) (iwArithFreqs ρ l) := by
  obtain ⟨C, hCpos, hC⟩ := nonAliasing_of_size ρ hρ hρ1
  obtain ⟨B, hB⟩ := exists_two_rpow_gt_ssu ρ hρ (2 * C + 1) (by linarith)
  refine ⟨B, ?_⟩
  intro L l hBL hlL
  have hx : 2 * C + 1 < (2 : ℝ) ^ (ρ * (L : ℝ)) := hB L hBL
  have hxpos : 0 < (2 : ℝ) ^ (ρ * (L : ℝ)) := Real.rpow_pos_of_pos (by norm_num) _
  have hlt : C * (2 : ℝ) ^ (ρ * max (l : ℝ) (L : ℝ)) < (uScale ρ L : ℝ) := by
    rw [max_eq_right (by exact_mod_cast hlL)]
    have hx2 := two_mul_uScale_ge_rpow_ssu ρ hρ.le L
    have hsq : (2 : ℝ) ^ (2 * ρ * (L : ℝ))
        = ((2 : ℝ) ^ (ρ * (L : ℝ))) ^ 2 := by
      rw [show 2 * ρ * (L : ℝ) = (ρ * (L : ℝ)) * ((2 : ℕ) : ℝ) by push_cast; ring,
        Real.rpow_mul (by norm_num), Real.rpow_natCast]
    have h2C : 2 * C < (2 : ℝ) ^ (ρ * (L : ℝ)) := by linarith
    have hCx : C * (2 : ℝ) ^ (ρ * (L : ℝ))
        < ((2 : ℝ) ^ (ρ * (L : ℝ))) ^ 2 / 2 := by
      have hpos : 0 < (2 : ℝ) ^ (ρ * (L : ℝ)) * ((2 : ℝ) ^ (ρ * (L : ℝ)) - 2 * C) :=
        mul_pos hxpos (by linarith)
      nlinarith [hpos]
    have hhalf : ((2 : ℝ) ^ (ρ * (L : ℝ))) ^ 2 / 2 ≤ (uScale ρ L : ℝ) := by
      rw [hsq] at hx2; linarith
    linarith
  have hK : ((↑(-(uScale ρ L : ℤ)) : ℝ))
      + C * (2 : ℝ) ^ (ρ * max (l : ℝ) (L : ℝ)) < 0 := by
    have h2 : ((↑(-(uScale ρ L : ℤ)) : ℝ)) = -(uScale ρ L : ℝ) := by push_cast; ring
    rw [h2]; linarith
  have hres := hC l L (-(uScale ρ L : ℤ)) hK
  exact fun α hα β hβ θ hθ θ' hθ' h =>
    hres α (Finset.mem_union_left _ hα) β (Finset.mem_union_left _ hβ) θ hθ θ' hθ' h

/-! ## The bounded exceptional scales -/

/-- Exponential beats linear. -/
lemma linear_le_two_rpow_ssu (σ : ℝ) (hσ : 0 < σ) :
    ∃ B : ℕ, ∀ L : ℕ, B ≤ L → 2 * (L : ℝ) + 2 ≤ (2 : ℝ) ^ (σ * (L : ℝ)) := by
  set c : ℝ := σ * Real.log 2 with hcdef
  have hcpos : 0 < c := mul_pos hσ (Real.log_pos (by norm_num))
  have hc2 : 0 < c ^ 2 := pow_pos hcpos 2
  refine ⟨max 1 ⌈max (6 / c ^ 2) (2 / c)⌉₊, ?_⟩
  intro L hL
  have hL1 : 1 ≤ L := le_trans (le_max_left _ _) hL
  have hLc : max (6 / c ^ 2) (2 / c) ≤ (L : ℝ) := by
    have h2 : ⌈max (6 / c ^ 2) (2 / c)⌉₊ ≤ L := le_trans (le_max_right _ _) hL
    exact le_trans (Nat.le_ceil _) (by exact_mod_cast h2)
  have hL6 : 6 / c ^ 2 ≤ (L : ℝ) := le_trans (le_max_left _ _) hLc
  have hL2 : 2 / c ≤ (L : ℝ) := le_trans (le_max_right _ _) hLc
  have hL6' : 6 ≤ c ^ 2 * (L : ℝ) := by
    have h := mul_le_mul_of_nonneg_left hL6 hc2.le
    rw [show c ^ 2 * (6 / c ^ 2) = 6 by field_simp] at h
    exact h
  have hL2' : 2 ≤ c * (L : ℝ) := by
    have h := mul_le_mul_of_nonneg_left hL2 hcpos.le
    rw [show c * (2 / c) = 2 by field_simp] at h
    exact h
  have hrpow : (2 : ℝ) ^ (σ * (L : ℝ)) = Real.exp (c * (L : ℝ)) := by
    rw [Real.rpow_def_of_pos (by norm_num), hcdef]; ring_nf
  rw [hrpow]
  have hsum := Real.sum_le_exp_of_nonneg (x := c * (L : ℝ)) (by positivity) 3
  have hsum' : (1 + c * (L : ℝ) + (c * (L : ℝ)) ^ 2 / 2) ≤ Real.exp (c * (L : ℝ)) := by
    have h := hsum
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_zero] at h
    norm_num at h
    linarith [h]
  have hkey : 2 * (L : ℝ) + 2 ≤ 1 + c * (L : ℝ) + (c * (L : ℝ)) ^ 2 / 2 := by
    have hLnn : (0 : ℝ) ≤ (L : ℝ) := by positivity
    nlinarith [hL6', hL2', hLnn, (by exact_mod_cast hL1 : (1 : ℝ) ≤ (L : ℝ))]
  linarith

/-- `uScale ρ L` eventually dominates `L`. -/
lemma le_uScale_ssu (ρ : ℝ) (hρ : 0 < ρ) : ∃ B : ℕ, ∀ L : ℕ, B ≤ L → L ≤ uScale ρ L := by
  obtain ⟨B, hB⟩ := linear_le_two_rpow_ssu (2 * ρ) (by linarith)
  refine ⟨B, fun L hL => ?_⟩
  have h1 : 2 * (L : ℝ) + 2 ≤ (2 : ℝ) ^ (2 * ρ * (L : ℝ)) := hB L hL
  have h2 := rpow_sub_one_le_uScale_ssu ρ hρ.le L
  have h3 : (L : ℝ) ≤ (uScale ρ L : ℝ) := by
    have hLnn : (0 : ℝ) ≤ (L : ℝ) := by positivity
    linarith
  exact_mod_cast h3

/-- `uScale ρ L` eventually dominates `2^{ρL}`. -/
lemma two_rpow_le_uScale_ssu (ρ : ℝ) (hρ : 0 < ρ) :
    ∃ B : ℕ, ∀ L : ℕ, B ≤ L → (2 : ℝ) ^ (ρ * (L : ℝ)) ≤ (uScale ρ L : ℝ) := by
  obtain ⟨B, hB⟩ := linear_le_two_rpow_ssu ρ hρ
  refine ⟨max B 1, fun L hL => ?_⟩
  have h1 : 2 * (L : ℝ) + 2 ≤ (2 : ℝ) ^ (ρ * (L : ℝ)) := hB L (le_trans (le_max_left _ _) hL)
  have h2 := rpow_sub_one_le_uScale_ssu ρ hρ.le L
  have hLnn : (0 : ℝ) ≤ (L : ℝ) := by positivity
  have h4 : (4 : ℝ) ≤ (2 : ℝ) ^ (ρ * (L : ℝ)) := by
    have hL1 : (1 : ℝ) ≤ (L : ℝ) := by
      exact_mod_cast (le_trans (le_max_right _ _) hL : 1 ≤ L)
    linarith
  have hsq : (2 : ℝ) ^ (2 * ρ * (L : ℝ)) = ((2 : ℝ) ^ (ρ * (L : ℝ))) ^ 2 := by
    rw [show 2 * ρ * (L : ℝ) = (ρ * (L : ℝ)) * ((2 : ℕ) : ℝ) by push_cast; ring,
      Real.rpow_mul (by norm_num), Real.rpow_natCast]
  have hstep : (2 : ℝ) ^ (ρ * (L : ℝ)) ≤ (2 : ℝ) ^ (2 * ρ * (L : ℝ)) - 1 := by
    rw [hsq]
    nlinarith [h4]
  linarith

/-- A uniform bound of `uScale ρ L` bounds `L`. -/
lemma le_of_uScale_le_ssu (ρ : ℝ) (hρ : 0 < ρ) :
    ∃ B : ℕ, ∀ L : ℕ, (uScale ρ L : ℝ) ≤ 4 → L ≤ B := by
  refine ⟨⌈Real.log 5 / (2 * ρ * Real.log 2)⌉₊, fun L hL => ?_⟩
  have h2 : (2 : ℝ) ^ (2 * ρ * (L : ℝ)) - 1 ≤ 4 := by
    have := rpow_sub_one_le_uScale_ssu ρ hρ.le L
    linarith
  have h3 : (2 : ℝ) ^ (2 * ρ * (L : ℝ)) ≤ 5 := by linarith
  have hlog : Real.log ((2 : ℝ) ^ (2 * ρ * (L : ℝ))) ≤ Real.log 5 :=
    Real.log_le_log (Real.rpow_pos_of_pos (by norm_num) _) h3
  rw [Real.log_rpow (by norm_num)] at hlog
  have hden : 0 < 2 * ρ * Real.log 2 := by
    have := Real.log_pos (by norm_num : (1 : ℝ) < 2)
    positivity
  have hLR : (L : ℝ) ≤ Real.log 5 / (2 * ρ * Real.log 2) := by
    rw [le_div_iff₀ hden]
    nlinarith [hlog]
  have hle : (L : ℝ) ≤ (⌈Real.log 5 / (2 * ρ * Real.log 2)⌉₊ : ℝ) :=
    le_trans hLR (Nat.le_ceil _)
  exact_mod_cast hle

/-- `4u + 3 < 2^u` for `u ≥ 5`. -/
lemma four_mul_add_three_lt_two_pow_ssu : ∀ u : ℕ, 5 ≤ u → 4 * (u : ℝ) + 3 < (2 : ℝ) ^ u := by
  intro u hu
  induction u, hu using Nat.le_induction with
  | base => norm_num
  | succ u hu ih =>
      have huR : (5 : ℝ) ≤ (u : ℝ) := by exact_mod_cast hu
      have hstep : 4 * ((u : ℝ) + 1) + 3 ≤ 2 * (4 * (u : ℝ) + 3) := by linarith
      have h2 : 2 * (4 * (u : ℝ) + 3) < 2 * (2 : ℝ) ^ u := by linarith
      have hcast : (((u + 1 : ℕ)) : ℝ) = (u : ℝ) + 1 := by push_cast; ring
      have hgoal : 4 * (((u + 1 : ℕ)) : ℝ) + 3 < 2 * (2 : ℝ) ^ u := by
        rw [hcast]; linarith
      rw [pow_succ]
      linarith

/-- **The bounded exceptional scales of the bad case.** -/
theorem MdlSliceBadScale_ssu (ρ : ℝ) (hρ : 0 < ρ) :
    ∃ B : ℕ, (∀ L : ℕ, (2 : ℕ) ^ (Work.KMTAreas.A7.uScale ρ L)
        ≤ L + 3 * Work.KMTAreas.A7.uScale ρ L + 3 → L ≤ B) ∧
      (∀ L m : ℕ, m ≤ L →
        (Work.KMTAreas.A7.uScale ρ L : ℝ) < (m : ℝ) → L ≤ B) ∧
      (∀ L m : ℕ, m ≤ L →
        (Work.KMTAreas.A7.uScale ρ L : ℝ) < (2 : ℝ) ^ (ρ * (m : ℝ)) → L ≤ B) := by
  obtain ⟨B₁, hB₁⟩ := le_uScale_ssu ρ hρ
  obtain ⟨B₂, hB₂⟩ := two_rpow_le_uScale_ssu ρ hρ
  obtain ⟨B₃, hB₃⟩ := le_of_uScale_le_ssu ρ hρ
  set B : ℕ := max (max B₁ B₂) B₃ + 1 with hBdef
  have hB₁B : B₁ ≤ B := by rw [hBdef]; omega
  have hB₂B : B₂ ≤ B := by rw [hBdef]; omega
  have hB₃B : B₃ ≤ B := by rw [hBdef]; omega
  refine ⟨B, ?_, ?_, ?_⟩
  · intro L hL
    by_contra hcon
    push Not at hcon
    have hLB₁ : B₁ ≤ L := le_trans hB₁B (le_of_lt hcon)
    have hLu : L ≤ Work.KMTAreas.A7.uScale ρ L := hB₁ L hLB₁
    by_cases hu : 5 ≤ Work.KMTAreas.A7.uScale ρ L
    · have h1 : (2 : ℝ) ^ (Work.KMTAreas.A7.uScale ρ L)
          ≤ (L : ℝ) + 3 * (Work.KMTAreas.A7.uScale ρ L : ℝ) + 3 := by
        have hcast : ((L + 3 * Work.KMTAreas.A7.uScale ρ L + 3 : ℕ) : ℝ)
            = (L : ℝ) + 3 * (Work.KMTAreas.A7.uScale ρ L : ℝ) + 3 := by push_cast; ring
        have h3 : ((2 : ℕ) ^ (Work.KMTAreas.A7.uScale ρ L) : ℝ)
            ≤ ((L + 3 * Work.KMTAreas.A7.uScale ρ L + 3 : ℕ) : ℝ) := by exact_mod_cast hL
        rw [hcast] at h3
        push_cast at h3
        exact h3
      have h4 : 4 * (Work.KMTAreas.A7.uScale ρ L : ℝ) + 3
          < (2 : ℝ) ^ (Work.KMTAreas.A7.uScale ρ L) := four_mul_add_three_lt_two_pow_ssu _ hu
      have h5 : (L : ℝ) ≤ (Work.KMTAreas.A7.uScale ρ L : ℝ) := by exact_mod_cast hLu
      linarith
    · push Not at hu
      have hle4 : (Work.KMTAreas.A7.uScale ρ L : ℝ) ≤ 4 := by
        have : Work.KMTAreas.A7.uScale ρ L ≤ 4 := by omega
        exact_mod_cast this
      have hLB₃ : B₃ ≤ L := le_trans hB₃B (le_of_lt hcon)
      exact absurd (hB₃ L hle4) (not_le.mpr (lt_of_le_of_lt hB₃B hcon))
  · intro L m hm hlt
    by_contra hcon
    push Not at hcon
    have hLB₁ : B₁ ≤ L := le_trans hB₁B (le_of_lt hcon)
    have hLu := hB₁ L hLB₁
    have hmr : (m : ℝ) ≤ (L : ℝ) := by exact_mod_cast hm
    have hLur : (L : ℝ) ≤ (Work.KMTAreas.A7.uScale ρ L : ℝ) := by exact_mod_cast hLu
    linarith
  · intro L m hm hlt
    by_contra hcon
    push Not at hcon
    have hLB₂ : B₂ ≤ L := le_trans hB₂B (le_of_lt hcon)
    have h2 := hB₂ L hLB₂
    have hmr : (m : ℝ) ≤ (L : ℝ) := by exact_mod_cast hm
    have hpow : (2 : ℝ) ^ (ρ * (m : ℝ)) ≤ (2 : ℝ) ^ (ρ * (L : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (by nlinarith [hρ.le, hmr])
    linarith

/-! ## A uniform crude bound for `Btwist` -/

lemma ssu_deriv_comp_mul_left (f : ℝ → ℂ) (c : ℝ) :
    deriv (fun y : ℝ => f (c * y)) = fun y => (c : ℂ) * deriv f (c * y) := by
  funext y
  rw [deriv_comp_mul_left, Complex.real_smul]

lemma ssu_deriv_deriv_comp_mul_left (f : ℝ → ℂ) (c x : ℝ) :
    deriv (deriv (fun y : ℝ => f (c * y))) x
      = (c : ℂ) * ((c : ℂ) * deriv (deriv f) (c * x)) := by
  rw [ssu_deriv_comp_mul_left f c, deriv_const_mul_field, deriv_comp_mul_left, Complex.real_smul]

lemma ssu_iteratedDeriv_two_eq_deriv (f : ℝ → ℂ) :
    iteratedDeriv 2 f = deriv (deriv f) := by
  rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one]

/-- The `ℓ¹` mass of the Fourier coefficients of `η_{≤c}`, `c ≤ 0`, is bounded uniformly. -/
theorem cw_etaCut_tsum_le_uniform_ssu :
    ∃ C : ℝ, 0 < C ∧ ∀ c : ℤ, c ≤ 0 →
      ∑' j : ℤ, ‖cw (etaCut Work.KMTContract.kmtEta c) j‖ ≤ C := by
  obtain ⟨Ccw, hCcwpos, hCcw⟩ := Work.KMTAreas.A7.CwTsumLe
  obtain ⟨M0, M1, M2, hM0, hM1, hM2, hcd, hb0, hb1, hb2, hz0, hz1, hz2, _, _⟩ :=
    Work.KMTAreas.A7.kmtEta_deriv_bounds
  have hη0 : ∀ y : ℝ, ‖Work.KMTContract.kmtEta y‖ ≤ M0 := by
    intro y
    rcases lt_or_ge (1 : ℝ) |y| with h | h
    · rw [hz0 y (le_of_lt h), norm_zero]; exact hM0
    · exact hb0 y h
  have hη1 : ∀ y : ℝ, ‖deriv Work.KMTContract.kmtEta y‖ ≤ M1 := by
    intro y
    rcases lt_or_ge (1 : ℝ) |y| with h | h
    · rw [hz1 y (le_of_lt h), norm_zero]; exact hM1
    · exact hb1 y h
  have hη2 : ∀ y : ℝ, ‖deriv (deriv Work.KMTContract.kmtEta) y‖ ≤ M2 := by
    intro y
    rw [← ssu_iteratedDeriv_two_eq_deriv]
    rcases lt_or_ge (1 : ℝ) |y| with h | h
    · rw [hz2 y (le_of_lt h), norm_zero]; exact hM2
    · exact hb2 y h
  set C0 : ℝ := max M0 (max M1 M2) with hC0def
  have h0C0 : M0 ≤ C0 := le_max_left _ _
  have h1C0 : M1 ≤ C0 := le_trans (le_max_left _ _) (le_max_right _ _)
  have h2C0 : M2 ≤ C0 := le_trans (le_max_right _ _) (le_max_right _ _)
  refine ⟨max (Ccw * C0) 0 + 1, by positivity, fun c hc => ?_⟩
  set R : ℝ := ((2 : ℝ) ^ c)⁻¹ with hRdef
  have hRpos : 0 < R := by
    rw [hRdef]; exact inv_pos.mpr (zpow_pos (by norm_num : (0 : ℝ) < 2) c)
  have hR1 : 1 ≤ R := by
    rw [hRdef, ← zpow_neg]
    exact one_le_zpow₀ (by norm_num : (1 : ℝ) ≤ 2) (by omega)
  have hR0 : 0 ≤ C0 := le_trans hM0 h0C0
  have hRnn : 0 ≤ R := hRpos.le
  have hRC : ‖((R : ℝ) : ℂ)‖ = R := by
    rw [Complex.norm_real, Real.norm_of_nonneg hRnn]
  have hE : ∀ θ : ℝ, etaCut Work.KMTContract.kmtEta c θ = Work.KMTContract.kmtEta (R * θ) := by
    intro θ
    simp only [etaCut, hRdef, div_eq_mul_inv]
    ring_nf
  have hbd : ∀ θ : ℝ, ‖etaCut Work.KMTContract.kmtEta c θ‖ ≤ C0 := by
    intro θ; rw [hE θ]; exact le_trans (hη0 _) h0C0
  have hbd1 : ∀ θ : ℝ, ‖deriv (etaCut Work.KMTContract.kmtEta c) θ‖ ≤ C0 * R := by
    intro θ
    have hfun : etaCut Work.KMTContract.kmtEta c
        = fun θ : ℝ => Work.KMTContract.kmtEta (R * θ) := funext hE
    rw [hfun, ssu_deriv_comp_mul_left, norm_mul, hRC]
    calc R * ‖deriv Work.KMTContract.kmtEta (R * θ)‖ ≤ R * M1 :=
          mul_le_mul_of_nonneg_left (hη1 (R * θ)) hRnn
      _ ≤ C0 * R := by
          rw [mul_comm C0 R]; exact mul_le_mul_of_nonneg_left h1C0 hRnn
  have hbd2 : ∀ θ : ℝ, ‖deriv (deriv (etaCut Work.KMTContract.kmtEta c)) θ‖ ≤ C0 * R ^ 2 := by
    intro θ
    have hfun : etaCut Work.KMTContract.kmtEta c
        = fun θ : ℝ => Work.KMTContract.kmtEta (R * θ) := funext hE
    rw [hfun, ssu_deriv_deriv_comp_mul_left Work.KMTContract.kmtEta R θ, norm_mul, norm_mul,
      hRC]
    calc R * (R * ‖deriv (deriv Work.KMTContract.kmtEta) (R * θ)‖) ≤ R * (R * M2) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hη2 (R * θ)) hRnn) hRnn
      _ ≤ C0 * R ^ 2 := by nlinarith [h2C0, hRnn, sq_nonneg R]
  have hsup : ∀ θ : ℝ, 1 / R < |θ| → etaCut Work.KMTContract.kmtEta c θ = 0 := by
    intro θ hθ
    rw [hE θ]
    refine hz0 _ ?_
    have hthis : 1 < R * |θ| := by
      have h2 := mul_lt_mul_of_pos_left hθ hRpos
      rwa [mul_div_cancel₀ _ (ne_of_gt hRpos)] at h2
    rw [abs_mul, abs_of_pos hRpos]
    exact le_of_lt hthis
  have hcdE : ContDiff ℝ 2 (etaCut Work.KMTContract.kmtEta c) := by
    have hfun : etaCut Work.KMTContract.kmtEta c
        = fun θ : ℝ => Work.KMTContract.kmtEta (R * θ) := funext hE
    rw [hfun]
    exact hcd.comp (contDiff_const.mul contDiff_id)
  refine (hCcw (etaCut Work.KMTContract.kmtEta c) C0 R hR0 hR1 hcdE hbd hbd1 hbd2 hsup).trans ?_
  exact le_trans (le_max_left _ _) (le_add_of_nonneg_right (by norm_num))

/-- **The uniform crude `ℓ² × ℓ² → ℓ¹` bound for `Btwist` at bounded height.** -/
theorem MdlSliceCrudeUniform_ssu (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (P : Polynomial ℤ) (B : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (l₁ l₂ u : ℕ), max l₁ l₂ ≤ B →
      ∀ h k : ℤ → ℂ, MeasureTheory.MemLp h 2 MeasureTheory.Measure.count →
        MeasureTheory.MemLp k 2 MeasureTheory.Measure.count →
        MeasureTheory.eLpNorm (fun x : ℤ => Work.KMTAreas.A7.Btwist ρ P l₁ l₂
            (Work.KMTAreas.A7.mStarF u) (Work.KMTAreas.A7.mStargF P.natDegree u) h k x)
          1 MeasureTheory.Measure.count
          ≤ ENNReal.ofReal C * MeasureTheory.eLpNorm h 2 MeasureTheory.Measure.count
              * MeasureTheory.eLpNorm k 2 MeasureTheory.Measure.count := by
  obtain ⟨Cw, hCwpos, hCw⟩ := cw_etaCut_tsum_le_uniform_ssu
  set N₁ : ℕ := (iwArithFreqs ρ B).card with hN₁
  have hNn : (0 : ℝ) ≤ (N₁ : ℝ) := by positivity
  refine ⟨Cw * Cw * ((N₁ : ℝ) * (N₁ : ℝ)) + 1, by positivity,
    fun l₁ l₂ u hB h k hh hk => ?_⟩
  have hl₁ : l₁ ≤ B := le_trans (le_max_left _ _) hB
  have hl₂ : l₂ ≤ B := le_trans (le_max_right _ _) hB
  have hcard₁ : ((iwArithFreqs ρ l₁).card : ℝ) ≤ (N₁ : ℝ) := by
    rw [hN₁]
    exact_mod_cast Finset.card_le_card (Work.Analysis.IonescuWainger.iwArithFreqs_mono hρ hρ1 hl₁)
  have hcard₂ : ((iwArithFreqs ρ l₂).card : ℝ) ≤ (N₁ : ℝ) := by
    rw [hN₁]
    exact_mod_cast Finset.card_le_card (Work.Analysis.IonescuWainger.iwArithFreqs_mono hρ hρ1 hl₂)
  have hsum₁ : (∑' j : ℤ, ‖cw (Work.KMTAreas.A7.mStarF u) j‖) ≤ Cw := by
    have hc : -(2 * (u : ℤ)) ≤ 0 := neg_nonpos.mpr (mul_nonneg (by norm_num) (by positivity))
    simpa only [Work.KMTAreas.A7.mStarF] using hCw (-(2 * (u : ℤ))) hc
  have hsum₂ : (∑' j : ℤ, ‖cw (Work.KMTAreas.A7.mStargF P.natDegree u) j‖) ≤ Cw := by
    have hc : -((P.natDegree : ℤ) * 2 * (u : ℤ)) ≤ 0 :=
      neg_nonpos.mpr (mul_nonneg (mul_nonneg (by positivity) (by norm_num)) (by positivity))
    simpa only [Work.KMTAreas.A7.mStargF] using hCw (-((P.natDegree : ℤ) * 2 * (u : ℤ))) hc
  refine (Work.KMTPlan.A6Bile.Btwist_eLpNorm_le_crude ρ P l₁ l₂
    (Work.KMTAreas.A7.mStarF u) (Work.KMTAreas.A7.mStargF P.natDegree u) 1 le_rfl
    (Work.KMTAreas.A7.summable_cw_mStarF u)
    (Work.KMTAreas.A7.summable_cw_mStargF P.natDegree u) h k hh hk).trans ?_
  refine mul_le_mul' (mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl) le_rfl
  have hs : (∑' j : ℤ, ‖cw (Work.KMTAreas.A7.mStarF u) j‖)
      * (∑' j : ℤ, ‖cw (Work.KMTAreas.A7.mStargF P.natDegree u) j‖) ≤ Cw * Cw :=
    mul_le_mul hsum₁ hsum₂ (by positivity) hCwpos.le
  have hcd : ((iwArithFreqs ρ l₁).card : ℝ) * ((iwArithFreqs ρ l₂).card : ℝ)
      ≤ (N₁ : ℝ) * (N₁ : ℝ) :=
    mul_le_mul hcard₁ hcard₂ (by positivity) hNn
  have hgoal : (∑' j : ℤ, ‖cw (Work.KMTAreas.A7.mStarF u) j‖)
        * (∑' j : ℤ, ‖cw (Work.KMTAreas.A7.mStargF P.natDegree u) j‖)
        * (((iwArithFreqs ρ l₁).card : ℝ) * ((iwArithFreqs ρ l₂).card : ℝ))
      ≤ Cw * Cw * ((N₁ : ℝ) * (N₁ : ℝ)) + 1 := by
    have := mul_le_mul hs hcd (by positivity) (by positivity)
    linarith
  exact hgoal

/-! ## Final helpers for the assembly -/

/-- Monotonicity of `NonAliasing` in the scale. -/
lemma nonAliasing_mono_ssu {k k' : ℤ} (h : k' ≤ k) {A : Finset Circle}
    (hA : NonAliasing k A) : NonAliasing k' A :=
  fun α hα β hβ θ hθ θ' hθ' heq =>
    hA α hα β hβ θ (realArc_mono h hθ) θ' (realArc_mono h hθ') heq

/-- The weight at `A = 0` is `1`. -/
lemma lossWeight_zero_ssu (ρ : ℝ) (l₁ l₂ k₁ k₂ : ℕ) :
    Work.KMTAreas.A7.lossWeight 0 ρ l₁ l₂ k₁ k₂ = 1 := by
  simp [Work.KMTAreas.A7.lossWeight]

/-- The paper's non-singularity condition. -/
lemma ne_zero_or_nonneg_ssu {k : ℕ} {j : ℤ} (hj : j ∈ ({-1, 0, 1} : Finset ℤ))
    (hk : k = 0 → j ≠ -1) : k ≠ 0 ∨ 0 ≤ j := by
  by_cases hk0 : k = 0
  · right
    have hj' := hk hk0
    simp only [Finset.mem_insert, Finset.mem_singleton] at hj
    rcases hj with h | h | h <;> omega
  · exact Or.inl hk0

/-- `logN` is nonnegative. -/
lemma logN_nonneg_ssu (N : ℕ) : 0 ≤ Work.Analysis.EndVar.logN N := by
  rw [Work.Analysis.EndVar.logN]
  exact Int.natCast_nonneg _

/-- The large-scale cut bounds the logarithm. -/
lemma two_pow_uScale_le_logN_ssu {ρ : ℝ} {L N : ℕ} (h : splitCut ρ L < N) :
    (2 : ℕ) ^ (uScale ρ L) ≤ (Work.Analysis.EndVar.logN N).toNat := by
  have h1 : (2 : ℕ) ^ (uScale ρ L) ≤ (2 : ℕ) ^ (2 ^ (uScale ρ L)) :=
    Nat.pow_le_pow_right (n := 2) (by norm_num)
      (le_of_lt (Nat.lt_two_pow_self : uScale ρ L < 2 ^ (uScale ρ L)))
  have h2 : (2 : ℕ) ^ (uScale ρ L) < N := by
    refine lt_of_le_of_lt h1 ?_
    simpa only [Work.KMTAreas.A7.splitCut, Work.KMTAreas.A7.uScale,
      Work.Analysis.EndVar.scaleCount, Nat.cast_one, one_mul] using h
  have h4 : N < (2 : ℕ) ^ ((Work.Analysis.EndVar.logN N).toNat + 1) := by
    have hlog : (Work.Analysis.EndVar.logN N).toNat = Nat.log 2 (max N 2) := by
      simp only [Work.Analysis.EndVar.logN, Int.toNat_natCast]
    rw [hlog]
    calc N ≤ max N 2 := le_max_left N 2
      _ < 2 ^ (Nat.log 2 (max N 2) + 1) :=
          Nat.lt_pow_succ_log_self (by norm_num : (1 : ℕ) < 2) (max N 2)
  by_contra hcon
  push Not at hcon
  have h5 : (2 : ℕ) ^ ((Work.Analysis.EndVar.logN N).toNat + 1)
      ≤ (2 : ℕ) ^ (2 ^ (uScale ρ L)) :=
    Nat.pow_le_pow_right (n := 2) (by norm_num) (by omega)
  have hsplit : Work.KMTAreas.A7.splitCut ρ L = 2 ^ (2 ^ (uScale ρ L)) := by
    simp only [Work.KMTAreas.A7.splitCut, Work.KMTAreas.A7.uScale,
      Work.Analysis.EndVar.scaleCount, Nat.cast_one, one_mul]
  rw [hsplit] at h
  omega

/-! ## The band-piece vanishing and the collapse -/

/-- **A band piece of `Tm ρ l φ f` at a frequency of height `< l` vanishes.** -/
theorem bandPiece_Tm_eq_zero_ssu (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (l : ℕ)
    (m : ℝ → ℂ) (φ : ℝ → ℂ) (f : ℤ → ℂ) (W : ℤ)
    (hm : Integrable m) (hmLp : MemLp (periodize m) ⊤ circleMeasure)
    (hφmem : MemLp (periodize φ) ⊤ circleMeasure)
    (hf : MemLp f 2 Measure.count)
    (hNA : NonAliasing W (iwArithFreqs ρ l))
    (hφarc : SupportedInArc W (periodize φ))
    (hmarc : SupportedInArc W (periodize m))
    (α : Circle) (hα : α ∈ iwArithFreqs ρ l) (hα' : α ∉ diffFreqs ρ l) :
    bandPiece m α (Tm ρ l φ f) = 0 := by
  set σ : Circle → ℂ := iwSymbolSet {α} (periodize m) with hσdef
  set τ : Circle → ℂ := iwSymbolSet (diffFreqs ρ l) (periodize φ) with hτdef
  have hσmem : MemLp σ ⊤ circleMeasure :=
    Work.Analysis.IWMultiplier.memLp_iwSymbolSet _ hmLp
  have hτmem : MemLp τ ⊤ circleMeasure :=
    Work.Analysis.IWMultiplier.memLp_iwSymbolSet _ hφmem
  have h0mem : MemLp (0 : Circle → ℂ) ⊤ circleMeasure := memLp_top_const (0 : ℂ)
  have hzero : σ * τ = 0 := by
    funext ξ
    rw [Pi.mul_apply]
    by_contra hne
    obtain ⟨h1, h2⟩ := mul_ne_zero_iff.mp hne
    have h1' : periodize m (ξ - α) ≠ 0 := by
      simpa only [hσdef, iwSymbolSet, Finset.sum_singleton] using h1
    obtain ⟨θ, hθarc, hθeq⟩ := hmarc (ξ - α) h1'
    have h2' : ∑ β ∈ diffFreqs ρ l, periodize φ (ξ - β) ≠ 0 := by
      simpa only [hτdef, iwSymbolSet] using h2
    obtain ⟨β, hβ, hβne⟩ := Finset.exists_ne_zero_of_sum_ne_zero h2'
    obtain ⟨θ', hθ'arc, hθ'eq⟩ := hφarc (ξ - β) hβne
    have heq : α + (θ : Circle) = β + (θ' : Circle) := by
      have e1 : α + (θ : Circle) = ξ := by rw [hθeq]; abel
      have e2 : β + (θ' : Circle) = ξ := by rw [hθ'eq]; abel
      rw [e1, e2]
    have hres := hNA α hα β (diffFreqs_subset ρ l hβ) θ hθarc θ' hθ'arc heq
    exact hα' (hres.1 ▸ hβ)
  have hTm : Tm ρ l φ f = ⇑(multiplierOf τ hτmem (toL2Z hf)) := by
    rw [Tm]
    exact iwConv_eq_multiplierOf (diffFreqs ρ l) (periodize φ) hφmem hf
  rw [hTm]
  rw [bandPiece_eq_iwConv m hm α (⇑(multiplierOf τ hτmem (toL2Z hf)))]
  rw [iwConvEqIwOpSetMemlp hσmem (multiplierOf τ hτmem (toL2Z hf))]
  have hcomp := multiplierOf_comp_mul hσmem hτmem h0mem hzero
  have happ := congrArg (fun T : L2Z →L[ℂ] L2Z => T (toL2Z hf)) hcomp
  simp only [ContinuousLinearMap.comp_apply] at happ
  have hσeq : iwOpSet {α} (periodize m) hσmem = multiplierOf σ hσmem := rfl
  rw [hσeq, happ]
  have hZ : multiplierOf (0 : Circle → ℂ) h0mem (toL2Z hf) = (0 : L2Z) :=
    multiplierOf_zero_eq (toL2Z hf) h0mem
  rw [hZ]
  exact funext (fun x => rfl)

/-- The sum over a superset of the terms supported on a subset. -/
lemma sum_ite_mem_eq_sum_ssu {ι M : Type*} [AddCommMonoid M] [DecidableEq ι]
    (s t : Finset ι) (w : ι → M) (hts : t ⊆ s) :
    (∑ x ∈ s, (if x ∈ t then w x else 0)) = ∑ x ∈ t, w x := by
  rw [← Finset.sum_filter]
  congr 1
  ext x
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨hxs, hxt⟩; exact hxt
  · intro hxt; exact ⟨hts hxt, hxt⟩

/-- **The collapse of the twisted bilinear multiplier on the exact-height packets.** -/
theorem Btwist_Tm_eq_sum_model_ssu (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (P : Polynomial ℤ)
    (l₁ l₂ u : ℕ) (φ ψ : ℝ → ℂ) (f g : ℤ → ℂ) (W₁ W₂ : ℤ)
    (hφmem : MemLp (periodize φ) ⊤ circleMeasure)
    (hψmem : MemLp (periodize ψ) ⊤ circleMeasure)
    (hf : MemLp f 2 Measure.count) (hg : MemLp g 2 Measure.count)
    (hNA₁ : NonAliasing W₁ (iwArithFreqs ρ l₁))
    (hNA₂ : NonAliasing W₂ (iwArithFreqs ρ l₂))
    (hφarc : SupportedInArc W₁ (periodize φ))
    (hψarc : SupportedInArc W₂ (periodize ψ))
    (hm₁arc : SupportedInArc W₁ (periodize (mStarF u)))
    (hm₂arc : SupportedInArc W₂ (periodize (mStargF P.natDegree u)))
    (hplat₁ : ∀ ξ : Circle, periodize φ ξ * periodize (mStarF u) ξ = periodize φ ξ)
    (hplat₂ : ∀ ξ : Circle,
      periodize ψ ξ * periodize (mStargF P.natDegree u) ξ = periodize ψ ξ) :
    ∀ x : ℤ, Btwist ρ P l₁ l₂ (mStarF u) (mStargF P.natDegree u)
        (Tm ρ l₁ φ f) (Tm ρ l₂ ψ g) x
      = ∑ α ∈ diffFreqs ρ l₁, ∑ β ∈ diffFreqs ρ l₂,
          mZ P (arithQ ρ (max l₁ l₂)) α β
            * Work.Analysis.IWMultiplier.iwConv {α} (periodize φ) f x
            * Work.Analysis.IWMultiplier.iwConv {β} (periodize ψ) g x := by
  have hNA₁' : NonAliasing W₁ (diffFreqs ρ l₁) :=
    fun a ha b hb => hNA₁ a (diffFreqs_subset ρ l₁ ha) b (diffFreqs_subset ρ l₁ hb)
  have hNA₂' : NonAliasing W₂ (diffFreqs ρ l₂) :=
    fun a ha b hb => hNA₂ a (diffFreqs_subset ρ l₂ ha) b (diffFreqs_subset ρ l₂ hb)
  have hmemF : MemLp (Tm ρ l₁ φ f) 2 Measure.count :=
    memLp_iwConv_count (diffFreqs ρ l₁) hφmem hf
  have hmemG : MemLp (Tm ρ l₂ ψ g) 2 Measure.count :=
    memLp_iwConv_count (diffFreqs ρ l₂) hψmem hg
  intro x
  rw [Work.KMTPlan.A6Bile.BtwistSumBandPiece ρ P l₁ l₂ (mStarF u) (mStargF P.natDegree u)
      (Tm ρ l₁ φ f) (Tm ρ l₂ ψ g) x hmemF hmemG
      (summable_cw_mStarF u) (summable_cw_mStargF P.natDegree u)]
  have hstep₁ : ∀ α ∈ iwArithFreqs ρ l₁,
      bandPiece (mStarF u) α (Tm ρ l₁ φ f) x
        = (if α ∈ diffFreqs ρ l₁
            then Work.Analysis.IWMultiplier.iwConv {α} (periodize φ) f x else 0) := by
    intro α hα
    by_cases hαD : α ∈ diffFreqs ρ l₁
    · rw [if_pos hαD]
      exact congrFun (bandPiece_Tm_eq_iwConv ρ l₁ W₁ (mStarF u) φ f
        (kmt_integrable_mStarF u) (kmt_MemLp_periodize_mStarF u) hm₁arc hφmem hφarc
        hplat₁ hNA₁' hf α hαD) x
    · rw [if_neg hαD]
      exact congrFun (bandPiece_Tm_eq_zero_ssu ρ hρ hρ1 l₁ (mStarF u) φ f W₁
        (kmt_integrable_mStarF u) (kmt_MemLp_periodize_mStarF u) hφmem hf hNA₁ hφarc
        hm₁arc α hα hαD) x
  have hstep₂ : ∀ β ∈ iwArithFreqs ρ l₂,
      bandPiece (mStargF P.natDegree u) β (Tm ρ l₂ ψ g) x
        = (if β ∈ diffFreqs ρ l₂
            then Work.Analysis.IWMultiplier.iwConv {β} (periodize ψ) g x else 0) := by
    intro β hβ
    by_cases hβD : β ∈ diffFreqs ρ l₂
    · rw [if_pos hβD]
      exact congrFun (bandPiece_Tm_eq_iwConv ρ l₂ W₂ (mStargF P.natDegree u) ψ g
        (kmt_integrable_mStargF P.natDegree u) (kmt_MemLp_periodize_mStargF P.natDegree u)
        hm₂arc hψmem hψarc hplat₂ hNA₂' hg β hβD) x
    · rw [if_neg hβD]
      exact congrFun (bandPiece_Tm_eq_zero_ssu ρ hρ hρ1 l₂ (mStargF P.natDegree u) ψ g W₂
        (kmt_integrable_mStargF P.natDegree u) (kmt_MemLp_periodize_mStargF P.natDegree u)
        hψmem hg hNA₂ hψarc hm₂arc β hβ hβD) x
  have hrow : ∀ α ∈ iwArithFreqs ρ l₁,
      (∑ β ∈ iwArithFreqs ρ l₂, mZ P (arithQ ρ (max l₁ l₂)) α β
          * bandPiece (mStarF u) α (Tm ρ l₁ φ f) x
          * bandPiece (mStargF P.natDegree u) β (Tm ρ l₂ ψ g) x)
        = (if α ∈ diffFreqs ρ l₁
            then ∑ β ∈ diffFreqs ρ l₂, mZ P (arithQ ρ (max l₁ l₂)) α β
              * Work.Analysis.IWMultiplier.iwConv {α} (periodize φ) f x
              * Work.Analysis.IWMultiplier.iwConv {β} (periodize ψ) g x
            else 0) := by
    intro α hα
    by_cases hαD : α ∈ diffFreqs ρ l₁
    · rw [if_pos hαD]
      have hsum1 : (∑ β ∈ iwArithFreqs ρ l₂, mZ P (arithQ ρ (max l₁ l₂)) α β
            * bandPiece (mStarF u) α (Tm ρ l₁ φ f) x
            * bandPiece (mStargF P.natDegree u) β (Tm ρ l₂ ψ g) x)
          = ∑ β ∈ iwArithFreqs ρ l₂, (if β ∈ diffFreqs ρ l₂ then
              mZ P (arithQ ρ (max l₁ l₂)) α β
                * Work.Analysis.IWMultiplier.iwConv {α} (periodize φ) f x
                * Work.Analysis.IWMultiplier.iwConv {β} (periodize ψ) g x else 0) := by
        refine Finset.sum_congr rfl (fun β hβ => ?_)
        rw [hstep₁ α hα, if_pos hαD, hstep₂ β hβ]
        by_cases hβD : β ∈ diffFreqs ρ l₂
        · simp only [hβD, if_true]
        · simp only [hβD, if_false]; ring
      rw [hsum1, sum_ite_mem_eq_sum_ssu _ _ _ (diffFreqs_subset ρ l₂)]
    · rw [if_neg hαD]
      refine Finset.sum_eq_zero (fun β _ => ?_)
      rw [hstep₁ α hα, if_neg hαD]
      ring
  rw [Finset.sum_congr rfl hrow]
  rw [sum_ite_mem_eq_sum_ssu _ _ _ (diffFreqs_subset ρ l₁)]


end

end Work.KMTPlan.A6
