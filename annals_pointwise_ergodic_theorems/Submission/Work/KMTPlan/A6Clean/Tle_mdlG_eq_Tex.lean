import Mathlib
import Submission.Work.KMTPlan.A6.Tle_mdlF_eq_iwConv
import Submission.Work.KMTPlan.A6.MdlSliceGband
import Submission.Work.KMTPlan.A6.MdlSliceLinGOne
import Submission.Work.KMTPlan.A6.LinfDefs

set_option maxHeartbeats 1000000

namespace Work.KMTPlan.A6Clean

open MeasureTheory

noncomputable section

/-!
## The `bn-ident` collapse of the model input `mdlG`

The requested identity is the composition of two proved ingredients of the tree:

* `Work.KMTPlan.A6.Tle_mdlG_eq_Tm`: the height-`≤ l₂` Ionescu--Wainger multiplier
  `T^{≤l₂}_{φ̃_{N,t,j₂}}` applied to the *narrow* exact-height projection
  `mdlG ρ P u l₂ g = Π_{l₂,≤-du} g` collapses to the exact-height multiplier `Tm ρ l₂ φ̃ g`
  (`bn-ident` of §6), provided the arc `ℝ_{≤-du}` is non-aliased and the bump `φ̃` is
  `L^∞` and supported in `ℝ_{≤-du-1}`;
* at height `l₂ ≠ 0` the exact-height carrier `Tm ρ l₂ φ̃` is the `Tex`-carrier of §8
  (`Work.KMTAreas.A7.diffFreqs_eq_iwArithFreqsNew`).

Three side conditions have to be produced from the hypotheses of the statement:

1. `2^{-du} ≤ 1/2`: from the non-aliasing `hnA` and `0 ∈ (ℚ/ℤ)_{≤l₂}`;
2. `SupportedInArc (-du) (periodize φ̃)`: from the pointwise support hypothesis `hsup`
   (`supportedInArc_periodize_of_arc` needs no summability hypothesis);
3. `MemLp (periodize φ̃) ⊤`: from the measurability and the uniform pointwise bound of `φ̃`,
   via `Work.KMTPlan.A6.Linf.memLp_periodize_of_arc`.

The pointwise bound is the only genuinely new brick: the tree's `varphitildeNtj_norm_le`
covers only `j₂ ∈ {0,1}` and `varphitildeNtj_pointwise` only `j₂ ∈ {-1,0,1}`, while the
statement allows every `j₂ : ℤ` subject to the paper's non-singularity condition
`k₂ ≠ 0 ∨ 0 ≤ j₂`.
-/

/-! ## §1.  Measurability of the modified bump for every twist `j : ℤ` -/

/-- The integer powers `z ↦ z^j` on `ℂ` are measurable. -/
private lemma measurable_zpow_int_c (j : ℤ) : Measurable fun z : ℂ => z ^ j := by
  rcases Int.eq_nat_or_neg j with ⟨n, h | h⟩
  · subst h; simpa using (continuous_pow (M := ℂ) n).measurable
  · subst h
    simp only [zpow_neg, zpow_natCast]
    exact ((continuous_pow (M := ℂ) n).measurable).inv

/-- `(t, ξ) ↦ φ̃_{N,t}(ξ)` is measurable in `ξ`. -/
private lemma measurable_varphitildeNt_c (P : Polynomial ℤ) (N k : ℕ) (t : ℝ) :
    Measurable (Work.KMTAreas.A7.varphitildeNt P P.natDegree N k t) := by
  rw [show Work.KMTAreas.A7.varphitildeNt P P.natDegree N k t
      = fun ξ : ℝ => Work.KMTAreas.A7.varphitildeN P.natDegree N k ξ
          * Work.KMTAreas.A7.ee (Work.KMTAreas.A7.PevalR P ((N : ℝ) * t) * ξ) from rfl]
  exact (Work.KMTPlan.A6.measurable_varphitildeN P.natDegree N k).mul
    ((Work.KMTAreas.A7.contDiff_ee_const_mul 1
      (Work.KMTAreas.A7.PevalR P ((N : ℝ) * t))).continuous.measurable)

/-- The modified bump `φ̃_{N,t,j}` is measurable in its frequency variable, for every `j : ℤ`. -/
private theorem measurable_varphitildeNtj_c (P : Polynomial ℤ) (N k : ℕ) (j : ℤ) (t : ℝ) :
    Measurable (Work.KMTPlan.A6.varphitildeNtj P N k j t) := by
  rw [show Work.KMTPlan.A6.varphitildeNtj P N k j t
      = fun x : ℝ => Work.KMTPlan.A6.gWeight P N k x j
          * Work.KMTAreas.A7.varphitildeNt P P.natDegree N k t x from rfl]
  refine Measurable.mul ?_ (measurable_varphitildeNt_c P N k t)
  unfold Work.KMTPlan.A6.gWeight
  exact (measurable_zpow_int_c j).comp
    (Complex.continuous_ofReal.measurable.comp (by fun_prop))

/-! ## §2.  The uniform pointwise bound of the modified bump, for every twist `j : ℤ` -/

/-- **The uniform pointwise bound** of the modified `g`-side bump
`φ̃_{N,t,j}(ξ) = (2^{-dk}N^dξ)^j φ̃_{N,t}(ξ)` under the paper's non-singularity condition
`k ≠ 0 ∨ 0 ≤ j`.

Outside the single forbidden pair `(k,j) = (0,-1)` the bump is bounded: for `j ≥ 0` the weight
is controlled on the support `|ξ| < 2^{d(k - Log N)}` of `φ̃_N` (`gWeight_one_norm_le`), while
for `j < 0` one has `k ≥ 1` and the two-sided support of the `k ≥ 1` bump
(`varphitildeNt_annulus_lower`) gives the matching lower bound (`gWeight_neg_one_norm_le`).
The two degenerate cases `d = P.natDegree = 0` (where `φ̃_N` is a single rescaled cutoff at
`k = 0` and vanishes identically for `k ≥ 1`) and `N = 0`, `j < 0` (where the weight itself
vanishes) are handled directly. -/
private theorem varphitildeNtj_norm_le_c (P : Polynomial ℤ) (N k : ℕ) (j : ℤ) (t : ℝ)
    (hk : k ≠ 0 ∨ 0 ≤ j) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ,
      ‖Work.KMTPlan.A6.varphitildeNtj P N k j t x‖ ≤ C := by
  by_cases hd0 : P.natDegree = 0
  · -- the polynomial is constant: `d = 0`
    by_cases hk0 : k = 0
    · -- `k = 0`: the weight is `ξ^j` with `j ≥ 0`, and the bump is `η(ξ)`
      subst hk0
      have hj0 : 0 ≤ j := by
        rcases hk with h | h
        · exact absurd rfl h
        · exact h
      refine ⟨1, zero_le_one, fun x => ?_⟩
      rw [Work.KMTPlan.A6.varphitildeNtj_eq_gWeight_mul, norm_mul]
      by_cases hx1 : |x| ≤ 1
      · have hgw : ‖Work.KMTPlan.A6.gWeight P N 0 x j‖ ≤ 1 := by
          have hval : Work.KMTPlan.A6.gWeight P N 0 x j = ((x : ℝ) : ℂ) ^ j := by
            rw [Work.KMTPlan.A6.gWeight, hd0]
            simp
          rw [hval, show j = (((j.toNat : ℕ) : ℤ)) from (Int.toNat_of_nonneg hj0).symm,
            zpow_natCast, Complex.norm_pow, Complex.norm_real, Real.norm_eq_abs]
          exact pow_le_one₀ (abs_nonneg x) hx1
        have hvt : ‖Work.KMTAreas.A7.varphitildeNt P P.natDegree N 0 t x‖ ≤ 1 :=
          Work.KMTPlan.A6.varphitildeNt_norm_le_one P P.natDegree N 0 t x
        calc ‖Work.KMTPlan.A6.gWeight P N 0 x j‖
              * ‖Work.KMTAreas.A7.varphitildeNt P P.natDegree N 0 t x‖
            ≤ 1 * 1 := mul_le_mul hgw hvt (norm_nonneg _) zero_le_one
          _ = 1 := mul_one 1
      · -- `|x| > 1`: the cutoff vanishes
        have hz : Work.KMTAreas.A7.varphitildeN P.natDegree N 0 x = 0 := by
          rw [Work.KMTAreas.A7.varphitildeN, if_pos rfl, hd0]
          simp only [Nat.cast_zero, zero_mul, Real.rpow_zero, one_mul]
          exact Work.KMTContract.kmtEta_zero (le_of_lt (not_le.mp hx1))
        have hz2 : Work.KMTAreas.A7.varphitildeNt P P.natDegree N 0 t x = 0 := by
          simp only [Work.KMTAreas.A7.varphitildeNt, hz, zero_mul]
        rw [hz2, norm_zero, mul_zero]
        exact zero_le_one
    · -- `k ≥ 1`: `φ̃_N = η(ξ) - η(ξ) = 0`
      refine ⟨0, le_rfl, fun x => ?_⟩
      have hz : Work.KMTAreas.A7.varphitildeN P.natDegree N k x = 0 := by
        rw [Work.KMTAreas.A7.varphitildeN, if_neg hk0, hd0]
        simp only [Nat.cast_zero, zero_mul, Real.rpow_zero, one_mul, sub_self]
      have hz2 : Work.KMTAreas.A7.varphitildeNt P P.natDegree N k t x = 0 := by
        simp only [Work.KMTAreas.A7.varphitildeNt, hz, zero_mul]
      rw [Work.KMTPlan.A6.varphitildeNtj_eq_gWeight_mul, hz2, mul_zero, norm_zero]
  · have hd1 : 1 ≤ P.natDegree := Nat.one_le_iff_ne_zero.mpr hd0
    by_cases hj0 : 0 ≤ j
    · -- `j ≥ 0`: the weight is bounded by `2^d` on the support
      refine ⟨(2 : ℝ) ^ ((P.natDegree + 1) * j.toNat), by positivity, fun x => ?_⟩
      by_cases hφ : Work.KMTPlan.A6.varphitildeNtj P N k j t x = 0
      · rw [hφ, norm_zero]; positivity
      · have hs := Work.KMTPlan.A6.varphitildeNtj_support_lt P N k j t x hφ
        have hxi : (2 : ℝ) ^ ((P.natDegree : ℝ)
              * ((Work.Analysis.EndVar.logN N : ℝ) - (k : ℝ))) * |x| ≤ 1 := by
          have h2 : (0 : ℝ) < 2 := by norm_num
          have hstep := mul_lt_mul_of_pos_left hs (Real.rpow_pos_of_pos h2
            ((P.natDegree : ℝ) * ((Work.Analysis.EndVar.logN N : ℝ) - (k : ℝ))))
          rw [← Real.rpow_add h2] at hstep
          have hexp : (P.natDegree : ℝ) * ((Work.Analysis.EndVar.logN N : ℝ) - (k : ℝ))
              + (P.natDegree : ℝ) * ((k : ℝ) - (Work.Analysis.EndVar.logN N : ℝ)) = 0 := by ring
          rw [hexp, Real.rpow_zero] at hstep
          exact hstep.le
        have hg1 := Work.KMTPlan.A6.gWeight_one_norm_le P hd1 N k x hxi
        have hgw : ‖Work.KMTPlan.A6.gWeight P N k x j‖
            ≤ (2 : ℝ) ^ ((P.natDegree + 1) * j.toNat) := by
          have hnat : ((j.toNat : ℕ) : ℤ) = j := Int.toNat_of_nonneg hj0
          have heq : Work.KMTPlan.A6.gWeight P N k x j
              = (Work.KMTPlan.A6.gWeight P N k x 1) ^ j.toNat := by
            unfold Work.KMTPlan.A6.gWeight
            rw [zpow_one]
            conv_lhs => rw [← hnat]
            rw [zpow_natCast]
          rw [heq, norm_pow]
          calc ‖Work.KMTPlan.A6.gWeight P N k x 1‖ ^ j.toNat
              ≤ ((2 : ℝ) ^ (P.natDegree + 1)) ^ j.toNat :=
                pow_le_pow_left₀ (norm_nonneg _) hg1 _
            _ = (2 : ℝ) ^ ((P.natDegree + 1) * j.toNat) := by rw [pow_mul]
        have hvt := Work.KMTPlan.A6.varphitildeNt_norm_le_one P P.natDegree N k t x
        rw [Work.KMTPlan.A6.varphitildeNtj_eq_gWeight_mul, norm_mul]
        calc ‖Work.KMTPlan.A6.gWeight P N k x j‖
              * ‖Work.KMTAreas.A7.varphitildeNt P P.natDegree N k t x‖
            ≤ (2 : ℝ) ^ ((P.natDegree + 1) * j.toNat) * 1 :=
              mul_le_mul hgw hvt (norm_nonneg _) (by positivity)
          _ = (2 : ℝ) ^ ((P.natDegree + 1) * j.toNat) := mul_one _
    · -- `j < 0`: then `k ≥ 1` and the bump vanishes near the origin
      have hjlt : j < 0 := not_le.mp hj0
      have hk1 : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr (hk.resolve_right hj0)
      rcases Nat.eq_zero_or_pos N with hN0 | hN1
      · -- `N = 0`, `d ≥ 1`: the weight vanishes
        subst hN0
        refine ⟨0, le_rfl, fun x => ?_⟩
        have hgw : Work.KMTPlan.A6.gWeight P 0 k x j = 0 := by
          unfold Work.KMTPlan.A6.gWeight
          have hz : ((0 : ℕ) : ℝ) ^ P.natDegree = 0 := by
            rw [Nat.cast_zero, zero_pow hd0]
          rw [hz]
          have hzero : (2 : ℝ) ^ (-((P.natDegree : ℝ) * (k : ℝ))) * 0 * x = 0 := by ring
          rw [hzero]
          exact zero_zpow j (ne_of_lt hjlt)
        rw [Work.KMTPlan.A6.varphitildeNtj_eq_gWeight_mul, hgw, zero_mul, norm_zero]
      · refine ⟨(2 : ℝ) ^ ((2 * P.natDegree + 1) * (-j).toNat), by positivity, fun x => ?_⟩
        by_cases hφ : Work.KMTPlan.A6.varphitildeNtj P N k j t x = 0
        · rw [hφ, norm_zero]; positivity
        · have hvt : Work.KMTAreas.A7.varphitildeNt P P.natDegree N k t x ≠ 0 := by
            intro h0
            exact hφ (by rw [Work.KMTPlan.A6.varphitildeNtj_eq_gWeight_mul, h0, mul_zero])
          have hlo := (Work.KMTPlan.A6.varphitildeNt_annulus_lower P hd1 N k t x hk1 hvt).le
          have hg1 := Work.KMTPlan.A6.gWeight_neg_one_norm_le P N k x hN1 hlo
          have hgw : ‖Work.KMTPlan.A6.gWeight P N k x j‖
              ≤ (2 : ℝ) ^ ((2 * P.natDegree + 1) * (-j).toNat) := by
            have hjm : j = -((((-j).toNat : ℕ) : ℤ)) := by
              rw [Int.toNat_of_nonneg (by omega : (0 : ℤ) ≤ -j)]
              ring
            have heq : Work.KMTPlan.A6.gWeight P N k x j
                = (Work.KMTPlan.A6.gWeight P N k x (-1)) ^ ((-j).toNat) := by
              unfold Work.KMTPlan.A6.gWeight
              rw [zpow_neg_one]
              conv_lhs => rw [hjm, zpow_neg, zpow_natCast]
              rw [inv_pow]
            rw [heq, norm_pow]
            calc ‖Work.KMTPlan.A6.gWeight P N k x (-1)‖ ^ (-j).toNat
                ≤ ((2 : ℝ) ^ (2 * P.natDegree + 1)) ^ (-j).toNat :=
                  pow_le_pow_left₀ (norm_nonneg _) hg1 _
              _ = (2 : ℝ) ^ ((2 * P.natDegree + 1) * (-j).toNat) := by rw [pow_mul]
          have hvt2 := Work.KMTPlan.A6.varphitildeNt_norm_le_one P P.natDegree N k t x
          rw [Work.KMTPlan.A6.varphitildeNtj_eq_gWeight_mul, norm_mul]
          calc ‖Work.KMTPlan.A6.gWeight P N k x j‖
                * ‖Work.KMTAreas.A7.varphitildeNt P P.natDegree N k t x‖
              ≤ (2 : ℝ) ^ ((2 * P.natDegree + 1) * (-j).toNat) * 1 :=
                mul_le_mul hgw hvt2 (norm_nonneg _) (by positivity)
            _ = (2 : ℝ) ^ ((2 * P.natDegree + 1) * (-j).toNat) := mul_one _

/-! ## §3.  Non-aliasing with the frequency origin forces a narrow arc -/

/-- **Non-aliasing plus `0 ∈ A` forces `2^k ≤ 1/2`.**  If `2^k ≥ 1/2` the arc `ℝ_{≤k}` has
length `≥ 1`, so the two (distinct) points `2^k` and `2^k - 1` of `ℝ_{≤k}` have the same image
in `ℝ/ℤ`; non-aliasing with `α = β = 0 ∈ A` forbids this. -/
private theorem two_zpow_le_half_of_nonAliasing {k : ℤ}
    {A : Finset Work.Analysis.IonescuWainger.Circle}
    (hA : Work.Analysis.IonescuWainger.NonAliasing k A)
    (h0 : (0 : Work.Analysis.IonescuWainger.Circle) ∈ A) :
    (2 : ℝ) ^ k ≤ 1 / 2 := by
  by_contra hcon
  rw [not_le] at hcon
  have hk0 : (0 : ℤ) ≤ k := by
    by_contra hneg
    rw [not_le] at hneg
    have hle : (2 : ℝ) ^ k ≤ (2 : ℝ) ^ (-1 : ℤ) :=
      zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (by omega)
    have h2 : (2 : ℝ) ^ (-1 : ℤ) = 1 / 2 := by norm_num
    rw [h2] at hle
    linarith
  have hpos : 0 < (2 : ℝ) ^ k := zpow_pos (by norm_num) k
  have hmem1 : (2 : ℝ) ^ k ∈ Work.Analysis.IonescuWainger.realArc k := by
    rw [Work.Analysis.IonescuWainger.realArc, Set.mem_Icc]
    exact ⟨neg_le_self hpos.le, le_rfl⟩
  have hmem2 : (2 : ℝ) ^ k - 1 ∈ Work.Analysis.IonescuWainger.realArc k := by
    rw [Work.Analysis.IonescuWainger.realArc, Set.mem_Icc]
    have h1 : (1 : ℝ) ≤ (2 : ℝ) ^ k := by
      simpa using zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hk0
    exact ⟨by linarith, by linarith⟩
  have hcoe : (0 : Work.Analysis.IonescuWainger.Circle)
        + (((2 : ℝ) ^ k : ℝ) : Work.Analysis.IonescuWainger.Circle)
      = (0 : Work.Analysis.IonescuWainger.Circle)
        + (((2 : ℝ) ^ k - 1 : ℝ) : Work.Analysis.IonescuWainger.Circle) := by
    rw [zero_add, zero_add, ← sub_eq_zero, ← AddCircle.coe_sub]
    have h1 : ((1 : ℝ) : Work.Analysis.IonescuWainger.Circle) = 0 := by
      rw [AddCircle.coe_eq_zero_iff]
      exact ⟨1, by simp⟩
    rw [show (2 : ℝ) ^ k - ((2 : ℝ) ^ k - 1) = 1 by ring, h1]
  have hres := (hA 0 h0 0 h0 ((2 : ℝ) ^ k) hmem1 ((2 : ℝ) ^ k - 1) hmem2 hcoe).2
  linarith

/-! ## §4.  `Tm = Tex` at positive height -/

/-- At height `l ≠ 0` the A6 `Tm`-carrier is the exact-height `Tex`-carrier of §8. -/
private theorem tm_eq_tex_c {ρ : ℝ} {l : ℕ} (hl : l ≠ 0) (φ : ℝ → ℂ) :
    Work.KMTAreas.A7.Tm ρ l φ = Work.KMTAreas.A7.Tex ρ l φ := by
  show Work.Analysis.IWMultiplier.iwConv (Work.KMTAreas.A7.diffFreqs ρ l)
      (Work.Analysis.IonescuWainger.periodize φ)
    = Work.Analysis.IWMultiplier.iwConv
        (Work.Analysis.IonescuWainger.iwArithFreqsNew ρ l)
        (Work.Analysis.IonescuWainger.periodize φ)
  rw [Work.KMTAreas.A7.diffFreqs_eq_iwArithFreqsNew hl]

/-! ## §5.  The target -/

theorem Tle_mdlG_eq_Tex (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (P : Polynomial ℤ) (u l₂ N k₂ : ℕ) (j₂ : ℤ) (t : ℝ) (g : ℤ → ℂ)
    (hl₂ : l₂ ≠ 0) (hk : k₂ ≠ 0 ∨ 0 ≤ j₂)
    (hg : MeasureTheory.MemLp g 2 MeasureTheory.Measure.count)
    (hnA : Work.Analysis.IonescuWainger.NonAliasing (-((P.natDegree : ℤ) * (u : ℤ)))
      (Work.Analysis.IonescuWainger.iwArithFreqs ρ l₂))
    (hsup : ∀ ξ : ℝ, Work.KMTPlan.A6.varphitildeNtj P N k₂ j₂ t ξ ≠ 0 →
      |ξ| ≤ (2 : ℝ) ^ (-((P.natDegree : ℤ) * (2 * (u : ℤ))) - 1)) :
    Work.KMTAreas.A7.Tle ρ l₂ (Work.KMTPlan.A6.varphitildeNtj P N k₂ j₂ t)
        (Work.KMTPlan.A6.mdlG ρ P u l₂ g)
      = Work.KMTAreas.A7.Tex ρ l₂ (Work.KMTPlan.A6.varphitildeNtj P N k₂ j₂ t) g := by
  set φ : ℝ → ℂ := Work.KMTPlan.A6.varphitildeNtj P N k₂ j₂ t with hφdef
  -- (1) the non-aliasing of the exact-height arc forces its radius to be at most `1/2`
  have h0A : (0 : Work.Analysis.IonescuWainger.Circle)
      ∈ Work.Analysis.IonescuWainger.iwArithFreqs ρ l₂ := by
    rw [Work.Analysis.IonescuWainger.mem_iwArithFreqs]
    exact ⟨1, Work.Analysis.IonescuWainger.one_mem_iwP ρ l₂, by simp⟩
  have hc : (2 : ℝ) ^ (-((P.natDegree : ℤ) * (u : ℤ))) ≤ 1 / 2 :=
    two_zpow_le_half_of_nonAliasing hnA h0A
  -- (2) the support hypothesis gives the arc support of the periodisation
  have hΦ : Work.Analysis.IonescuWainger.SupportedInArc
      (-((P.natDegree : ℤ) * (u : ℤ)) - 1)
      (Work.Analysis.IonescuWainger.periodize φ) := by
    refine Work.KMTPlan.A6.supportedInArc_periodize_of_arc fun x hx => ?_
    rw [Work.Analysis.IonescuWainger.realArc, Set.mem_Icc]
    have h1 := hsup x hx
    have h2 : (2 : ℝ) ^ (-((P.natDegree : ℤ) * (2 * (u : ℤ))) - 1)
        ≤ (2 : ℝ) ^ (-((P.natDegree : ℤ) * (u : ℤ)) - 1) := by
      refine zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 2) ?_
      have hu : (0 : ℤ) ≤ (u : ℤ) := Int.natCast_nonneg u
      have hd : (0 : ℤ) ≤ (P.natDegree : ℤ) := Int.natCast_nonneg _
      nlinarith
    have h3 : |x| ≤ (2 : ℝ) ^ (-((P.natDegree : ℤ) * (u : ℤ)) - 1) := le_trans h1 h2
    exact ⟨neg_le_of_abs_le h3, le_of_abs_le h3⟩
  -- (3) the bump is bounded, hence its periodisation is in `L^∞`
  obtain ⟨C, hC0, hC⟩ := varphitildeNtj_norm_le_c P N k₂ j₂ t hk
  have hR0 : (0 : ℝ) ≤ (2 : ℝ) ^ (-((P.natDegree : ℤ) * (2 * (u : ℤ))) - 1) :=
    zpow_nonneg (by norm_num) _
  have hφmem : MeasureTheory.MemLp
      (Work.Analysis.IonescuWainger.periodize φ) ⊤
      Work.Analysis.IonescuWainger.circleMeasure :=
    Work.KMTPlan.A6.Linf.memLp_periodize_of_arc φ
      (measurable_varphitildeNtj_c P N k₂ j₂ t) _ C hR0 hsup hC
  rw [hφdef] at hφmem hΦ ⊢
  rw [Work.KMTPlan.A6.Tle_mdlG_eq_Tm ρ hρ hρ1 P u l₂
      (Work.KMTPlan.A6.varphitildeNtj P N k₂ j₂ t) hc hg hnA hφmem hΦ, tm_eq_tex_c hl₂]

end

end Work.KMTPlan.A6Clean
