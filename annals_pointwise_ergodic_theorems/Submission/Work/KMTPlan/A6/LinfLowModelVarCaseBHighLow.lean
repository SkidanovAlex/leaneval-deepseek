/-
# Case B of the small-scale model estimate, high--low case, bounded-bump interface

A copy of `Submission/Work/KMTPlan/A6/lowModelVarCaseBHighLow.lean` in which the single-scale
estimate `hSS` is the `Linf` (bounded-bump) interface `Work.KMTPlan.A6.SSUBodyAtLinf`, the
frozen-`t` engine is `Work.KMTPlan.A6.Linf.lowFrozenBilinBound` (with the two extra pointwise
bounds on the two clamped bump families) and the spike bound is
`Work.KMTPlan.A6.Linf.caseBSpikeLeHighLow`.
-/
import Mathlib
import Submission.Work.KMTPlan.A6.caseBSliceWMeasInt
import Submission.Work.KMTPlan.A6.lowSmallSet_le_log_sharp_unif
import Submission.Work.KMTPlan.A6.mdlW3MaskedVarBound
import Submission.Work.KMTPlan.A6.lowWindowLarge
import Submission.Work.KMTPlan.A6.lowDecayBVarNorm
import Submission.Work.KMTPlan.A6.lowDecayWVarNorm
import Submission.Work.KMTPlan.A6.LinfLowFrozenBilinBound
import Submission.Work.KMTPlan.A6.LinfCaseBSpikeLeHighLow
import Submission.Port.Aesm

set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false

namespace Work.KMTPlan.A6.Linf

noncomputable section

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal BigOperators Interval
open PointwiseErgodicTheorems Submission.PointwiseErgodicTheorems
open Work.Analysis.IonescuWainger
open Work.KMTAreas.A7

/-! ## Elementary measure-theoretic helpers on `𝓁¹(ℤ)` -/

private lemma eLpNorm_le_of_le_int (A B : ℤ → ℝ≥0∞) (h : ∀ x, A x ≤ B x) :
    eLpNorm A 1 MeasureTheory.Measure.count ≤ eLpNorm B 1 MeasureTheory.Measure.count := by
  have hae : ∀ᵐ x ∂MeasureTheory.Measure.count, ‖A x‖ₑ ≤ (1 : ℝ≥0) * ‖B x‖ₑ := by
    filter_upwards with x
    simpa using h x
  have h' := MeasureTheory.eLpNorm_le_nnreal_smul_eLpNorm_of_ae_le_mul' (hf := by pw_aesm)
    (μ := MeasureTheory.Measure.count) (f := A) (g := B) (c := 1) hae 1
  simpa [ENNReal.smul_def, smul_eq_mul] using h'

private lemma eLpNorm_add_le_int (A B : ℤ → ℝ≥0∞) :
    eLpNorm (fun x : ℤ => A x + B x) 1 MeasureTheory.Measure.count
      ≤ eLpNorm A 1 MeasureTheory.Measure.count + eLpNorm B 1 MeasureTheory.Measure.count :=
  MeasureTheory.eLpNorm_add_le le_rfl

private lemma eLpNorm_const_mul_eq {c : ℝ≥0∞} (hc : c ≠ ⊤) (B : ℤ → ℝ≥0∞) :
    eLpNorm (fun x : ℤ => c * B x) 1 MeasureTheory.Measure.count
      = c * eLpNorm B 1 MeasureTheory.Measure.count := by
  rw [MeasureTheory.eLpNorm_one_eq_lintegral_enorm (hf := by pw_aesm),
    MeasureTheory.eLpNorm_one_eq_lintegral_enorm (hf := by pw_aesm)]
  simp only [enorm_eq_self]
  exact MeasureTheory.lintegral_const_mul' c _ hc

/-- **The variational norm of an affine combination.**  If a family `X` is, pointwise in `n`,
the combination `c₁(Aₙ − Bₙ) − c₂ Cₙ`, then its `r`-variational norm is at most
`‖c₁‖(V A + V B) + ‖c₂‖ V C`. -/
private lemma variationalNorm_affine_le {r : NNReal} (hr : 1 ≤ r) (X A B C : ℕ → ℂ)
    (c₁ c₂ : ℂ) (hid : ∀ n, X n = c₁ * (A n - B n) - c₂ * C n) :
    variationalNorm r X
      ≤ ‖c₁‖ₑ * (variationalNorm r A + variationalNorm r B) + ‖c₂‖ₑ * variationalNorm r C := by
  have hX : X = fun n => c₁ * (A n - B n) - c₂ * C n := funext hid
  rw [hX]
  have hsplit : (fun n => c₁ * (A n - B n) - c₂ * C n)
      = (fun n => c₁ * (A n - B n)) + (fun n => -(c₂ * C n)) := by
    funext n
    simp only [Pi.add_apply, Pi.sub_apply]
    ring
  rw [hsplit]
  refine (variationalNorm_add_le hr _ _).trans ?_
  have h2 : (fun n => -(c₂ * C n)) = (-c₂) • C := by
    funext n
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  have h1 : (fun n => c₁ * (A n - B n)) = c₁ • (fun n => A n - B n) := by
    funext n
    simp only [Pi.smul_apply, smul_eq_mul]
  have h3 : (fun n => A n - B n) = A + (fun n => -(B n)) := by
    funext n
    simp only [Pi.add_apply]
    ring
  have h4 : (fun n => -(B n)) = (-1 : ℂ) • B := by
    funext n
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  rw [h2, variationalNorm_smul hr (-c₂) C, enorm_neg, h1,
    variationalNorm_smul hr c₁ (fun n => A n - B n), h3]
  refine add_le_add (mul_le_mul' le_rfl ?_) le_rfl
  refine (variationalNorm_add_le hr _ _).trans ?_
  rw [h4, variationalNorm_smul hr (-1) B]
  simp

/-- **The masked constant family.**  If `p` is the tail `{n | n₀ ≤ n}` then the `r`-variational
norm of its indicator is at most `3`. -/
private lemma maskedConstVar {r : NNReal} (hr : 1 ≤ r) {p : ℕ → Prop} [DecidablePred p]
    {n₀ : ℕ} (hp : ∀ n, p n ↔ n₀ ≤ n) :
    variationalNorm r (fun n : ℕ => if p n then (1 : ℂ) else 0) ≤ ENNReal.ofReal 3 := by
  have hbase : variationalNorm r (fun _ : ℕ => (1 : ℂ)) ≤ ENNReal.ofReal 1 := by
    have h := Work.KMTAreas.A7.variationalNorm_const_le hr (1 : ℂ)
    simpa using h
  have h := Work.KMTPlan.A6.masked_le_tail hr n₀ hp (fun _ : ℕ => (1 : ℂ))
    (C := 1) hbase
  simpa using h

private lemma ofReal_frozenSplit (A B C D : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hD : 0 ≤ D) :
    ENNReal.ofReal A * (ENNReal.ofReal B * ENNReal.ofReal C * (ENNReal.ofReal D * ENNReal.ofReal D))
      = ENNReal.ofReal (A * B * C * (D * D)) := by
  have h1 : ENNReal.ofReal B * ENNReal.ofReal C = ENNReal.ofReal (B * C) :=
    (ENNReal.ofReal_mul hB).symm
  have h2 : ENNReal.ofReal D * ENNReal.ofReal D = ENNReal.ofReal (D * D) :=
    (ENNReal.ofReal_mul hD).symm
  calc ENNReal.ofReal A * (ENNReal.ofReal B * ENNReal.ofReal C * (ENNReal.ofReal D * ENNReal.ofReal D))
      = ENNReal.ofReal A * (ENNReal.ofReal (B * C) * ENNReal.ofReal (D * D)) := by rw [h1, h2]
    _ = ENNReal.ofReal A * ENNReal.ofReal (B * C * (D * D)) := by
        rw [← ENNReal.ofReal_mul (mul_nonneg hB hC)]
    _ = ENNReal.ofReal (A * (B * C * (D * D))) := (ENNReal.ofReal_mul hA).symm
    _ = ENNReal.ofReal (A * B * C * (D * D)) := by
        rw [show A * (B * C * (D * D)) = A * B * C * (D * D) from by ring]

private lemma ofReal_mul_ofReal_mul_eq (Y : ENNReal) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    ENNReal.ofReal a * (ENNReal.ofReal b * Y) = ENNReal.ofReal (a * b) * Y := by
  rw [← mul_assoc, ← ENNReal.ofReal_mul ha]

private lemma ofReal_add_eq (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    ENNReal.ofReal a + ENNReal.ofReal b = ENNReal.ofReal (a + b) :=
  (ENNReal.ofReal_add ha hb).symm

private lemma enorm_eq_ofReal_norm (c : ℂ) : ‖c‖ₑ = ENNReal.ofReal ‖c‖ := by
  rw [enorm_eq_nnnorm, ← ENNReal.ofReal_coe_nnreal]
  simp

/-- `‖(x : ℂ)‖ = x` for a nonnegative real `x`. -/
private lemma norm_ofReal_coe (x : ℝ) (hx : 0 ≤ x) : ‖((x : ℂ))‖ = x := by
  rw [Complex.norm_def, Complex.normSq_ofReal, Real.sqrt_mul_self hx]

theorem lowModelVarCaseBHighLowLinf
    (P : Polynomial ℤ) (hd : 2 ≤ P.natDegree) (r : NNReal) (hr : 2 < r)
    (hA1 : Work.KMTContract.AreaA1) (ρ : ℝ) (hρ : 0 < ρ) (hρ8 : 8 * ρ ≤ 1)
    (C₀ : ℕ) (hC₀ : 1 ≤ C₀) (hρC₀ : ρ * (C₀ : ℝ) ≤ 1 / 8)
    {cS : ℝ} (hcS : 0 < cS) {Cssu : NNReal}
    (hSS : Work.KMTPlan.A6.SSUBodyAtLinf P cS Cssu ρ)
    (B : ℕ) (C : NNReal → NNReal)
    (hRanF : Work.KMTPlan.A6.LowModRandL2FBody P C₀ ρ B C)
    (hRanG : Work.KMTPlan.A6.LowModRandL2GBody P C₀ ρ B C)
    {Cb : ℝ} (hCb : 0 < Cb)
    (hCbb : ∀ (N k : ℕ) (j : ℤ) (t : ℝ), j ∈ ({-1, 0, 1} : Finset ℤ) →
      ¬ (k = 0 ∧ j = -1) → 1 ≤ N → ∀ ξ : ℝ,
      ‖Work.KMTPlan.A6.varphitildeNtj P N k j t ξ‖ ≤ Cb) :
    ∃ Cc : NNReal → NNReal, ∃ Bc : ℕ,
      ∀ (a : ℕ → NNReal) (Λ : NNReal) (l₁ l₂ L : ℕ) (f g : ℤ → ℂ),
        1 < Λ → PointwiseErgodicTheorems.Lacunary Λ a → (∀ n, 1 ≤ a n) →
        max l₁ l₂ < L → Bc ≤ L →
        MeasureTheory.MemLp f 2 MeasureTheory.Measure.count →
        MeasureTheory.MemLp g 2 MeasureTheory.Measure.count →
        MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
            (fun n : ℕ => Work.KMTPlan.A6.lowModel ρ P C₀ a f g l₁ l₂ L 0 n x))
          1 MeasureTheory.Measure.count
          ≤ (Cc Λ : ENNReal) * ENNReal.ofReal
              (Work.KMTPlan.A6.lcWeight (min cS 1 / 2) l₁ l₂ L 0)
              * MeasureTheory.eLpNorm f 2 MeasureTheory.Measure.count
              * MeasureTheory.eLpNorm g 2 MeasureTheory.Measure.count := by
  classical
  have hdeg : 1 ≤ P.natDegree := by omega
  have hr2 : (2 : NNReal) ≤ r := le_of_lt hr
  have hr1 : (1 : NNReal) ≤ r := le_trans (by norm_num) hr2
  obtain ⟨C_RM, hC_RM, hFRZgen⟩ := Work.KMTPlan.A6.Linf.lowFrozenBilinBound P hd hA1
  obtain ⟨Bw, hBw0, Cw3, hCw3, hWmask⟩ := Work.KMTPlan.A6.mdlW3MaskedVarBound P hdeg r hr1
  obtain ⟨Bwin, hBwin1, hWin⟩ := Work.KMTPlan.A6.lowWindowLarge ρ hρ hρ8 C₀ hC₀ hρC₀ Bw
  obtain ⟨Busc, hUsc⟩ := Work.KMTPlan.A6.uScale_window ρ hρ
  obtain ⟨Bna, hNa⟩ := Work.KMTPlan.A6.nonAliasing_diffFreqs ρ hρ
  set Cbp : ℝ := max 8 Cb with hCbpdef
  set Aco : ℝ := 12 + 2 * Cw3 with hAcdef
  have hCbp_pos : 0 < Cbp := by rw [hCbpdef]; positivity
  have hAco_pos : 0 < Aco := by rw [hAcdef]; linarith
  set Kf : NNReal → ℝ := fun Λ => Aco * (Cssu : ℝ) *
      (4 * C_RM * Work.KMTPlan.A6.lowMfun Λ * (((C Λ : NNReal) : ℝ) * ((C Λ : NNReal) : ℝ))
        + 2 * (Cbp * Cbp)) with hKfdef
  have hKfnn : ∀ Λ : NNReal, 0 ≤ Kf Λ := by
    intro Λ
    rw [hKfdef]
    have h1 : 0 ≤ Aco := le_of_lt hAco_pos
    have h2 : 0 ≤ (Cssu : ℝ) := by positivity
    have h3 : (0 : ℝ) ≤ 4 * C_RM * Work.KMTPlan.A6.lowMfun Λ *
        (((C Λ : NNReal) : ℝ) * ((C Λ : NNReal) : ℝ)) + 2 * (Cbp * Cbp) := by
      have h4 : 0 ≤ C_RM := le_of_lt hC_RM
      have h5 : 0 ≤ Work.KMTPlan.A6.lowMfun Λ := Work.KMTPlan.A6.lowMfun_nonneg Λ
      have h6 : 0 ≤ ((C Λ : NNReal) : ℝ) := by positivity
      have h7 : 0 ≤ Cbp := le_of_lt hCbp_pos
      positivity
    exact mul_nonneg (mul_nonneg h1 h2) h3
  set Bc : ℕ := max B (max Bwin (max Busc (max Bna 1))) with hBcdef
  have hB_le_Bc : B ≤ Bc := by rw [hBcdef]; exact le_max_left _ _
  have hBwin_le_Bc : Bwin ≤ Bc := by
    rw [hBcdef]; exact le_trans (le_max_left _ _) (le_max_right _ _)
  have hBusc_le_Bc : Busc ≤ Bc := by
    rw [hBcdef]
    exact le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_right _ _)
  have hBna_le_Bc : Bna ≤ Bc := by
    rw [hBcdef]
    exact le_trans (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_right _ _))
      (le_max_right _ _)
  have hBc1 : 1 ≤ Bc := by rw [hBcdef]; omega
  refine ⟨fun Λ => (ENNReal.ofReal (Kf Λ)).toNNReal, Bc, ?_⟩
  intro a Λ l₁ l₂ L f g hΛ ha ha1 hmaxlt hBcL hf hg
  have hL1 : 1 ≤ L := le_trans hBc1 hBcL
  have hLc : Work.KMTPlan.A6.lcL l₁ l₂ L 0 = L := by
    rw [Work.KMTPlan.A6.lcL, max_eq_left (Nat.zero_le L), max_eq_right (le_of_lt hmaxlt)]
  have hN1 : ∀ n : ℕ, 1 ≤ Nat.floor (a n) := fun n =>
    Nat.le_floor (by simpa using ha1 n)
  have hwin : ∀ n : ℕ, Work.KMTPlan.A6.lowSmallSet ρ C₀ a l₁ l₂ L 0 n →
      L + 3 * Work.KMTAreas.A7.uScale ρ L
        ≤ (Work.Analysis.EndVar.logN (Nat.floor (a n))).toNat := by
    intro n hn
    obtain ⟨hidx, -⟩ := Work.KMTPlan.A6.lowSmallSet_iff.mp hn
    obtain ⟨-, hLh, -⟩ := hidx
    have hLh' : L ≤ Work.Analysis.EndVar.heightScale C₀ (Nat.floor (a n)) := by
      exact_mod_cast hLh
    exact (hWin L (Nat.floor (a n)) (le_trans hBwin_le_Bc hBcL) hLh').2
  have hlower : ∀ n : ℕ, Work.KMTPlan.A6.lowSmallSet ρ C₀ a l₁ l₂ L 0 n →
      Bw ≤ Nat.floor (a n) := by
    intro n hn
    obtain ⟨hidx, -⟩ := Work.KMTPlan.A6.lowSmallSet_iff.mp hn
    obtain ⟨-, hLh, -⟩ := hidx
    have hLh' : L ≤ Work.Analysis.EndVar.heightScale C₀ (Nat.floor (a n)) := by
      exact_mod_cast hLh
    exact (hWin L (Nat.floor (a n)) (le_trans hBwin_le_Bc hBcL) hLh').1
  have hLu : L ≤ Work.KMTAreas.A7.uScale ρ L := (hUsc L (le_trans hBusc_le_Bc hBcL)).1
  have hu1 : 1 ≤ Work.KMTAreas.A7.uScale ρ L := le_trans hL1 hLu
  have huL : (max l₁ l₂ : ℝ) ≤ (Work.KMTAreas.A7.uScale ρ (Work.KMTPlan.A6.lcL l₁ l₂ L 0) : ℝ) := by
    rw [hLc]
    have h1 : (max l₁ l₂ : ℝ) ≤ (L : ℝ) := by exact_mod_cast (le_of_lt hmaxlt)
    have h2 : (L : ℝ) ≤ (Work.KMTAreas.A7.uScale ρ L : ℝ) := by exact_mod_cast hLu
    linarith
  have hu2 : (2 : ℝ) ^ (ρ * (max l₁ l₂ : ℝ))
      ≤ (Work.KMTAreas.A7.uScale ρ (Work.KMTPlan.A6.lcL l₁ l₂ L 0) : ℝ) := by
    rw [hLc]
    have h := (hUsc L (le_trans hBusc_le_Bc hBcL)).2
    refine le_trans ?_ h
    refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
    have hmaxle : (max l₁ l₂ : ℝ) ≤ (L : ℝ) := by exact_mod_cast (le_of_lt hmaxlt)
    nlinarith [hρ]
  have hlogΛpos : 0 < Real.log (Λ : ℝ) := Real.log_pos (by exact_mod_cast hΛ)
  set D : ℝ := 2 * Real.log 2 / Real.log (Λ : ℝ) + 3 with hDdef
  have hDpos : 0 < D := by rw [hDdef]; positivity
  set Kv : ℕ := Work.KMTPlan.A6.lowTrunc D ρ L + 2 with hKvdef
  have hKv1 : 1 ≤ Kv := by
    rw [hKvdef, Work.KMTPlan.A6.lowTrunc]; omega
  have hlssK : ∀ k : ℕ, Kv ≤ k → ¬ Work.KMTPlan.A6.lowSmallSet ρ C₀ a l₁ l₂ L 0 k := by
    intro k hk hls
    have hb := Work.KMTPlan.A6.lowSmallSet_le_log_sharp_unif ρ hρ C₀ Λ hΛ a ha ha1
      l₁ l₂ L 0 k hls
    rw [hLc, ← hDdef] at hb
    have hceil : D * (2 : ℝ) ^ (Work.KMTAreas.A7.uScale ρ L)
        ≤ (Nat.ceil (D * (2 : ℝ) ^ (Work.KMTAreas.A7.uScale ρ L)) : ℝ) := Nat.le_ceil _
    have hKvR : (Kv : ℝ)
        = (Nat.ceil (D * (2 : ℝ) ^ (Work.KMTAreas.A7.uScale ρ L)) : ℝ) + 3 := by
      rw [hKvdef, Work.KMTPlan.A6.lowTrunc]; push_cast; ring
    have hkR : (Kv : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    linarith
  have hNA₁ : Work.Analysis.IonescuWainger.NonAliasing
      (-(3 * (Work.KMTAreas.A7.uScale ρ L : ℤ))) (Work.KMTAreas.A7.diffFreqs ρ l₁) := by
    exact hNa L l₁ (le_trans hBna_le_Bc hBcL) (le_trans (le_max_left l₁ l₂) (le_of_lt hmaxlt))
  have hNA₂ : Work.Analysis.IonescuWainger.NonAliasing
      (-(3 * (Work.KMTAreas.A7.uScale ρ L : ℤ))) (Work.KMTAreas.A7.diffFreqs ρ l₂) := by
    exact hNa L l₂ (le_trans hBna_le_Bc hBcL) (le_trans (le_max_right l₁ l₂) (le_of_lt hmaxlt))
  -- the arc support of the two frozen bump families
  have hsupF : ∀ (j : ℤ) (s : ℝ) (n : ℕ) (ξ : ℝ),
      Work.KMTPlan.A6.lowModSymbF ρ C₀ a l₁ l₂ L 0 j s n ξ ≠ 0 →
      |ξ| ≤ (2 : ℝ) ^ (-(3 * (Work.KMTAreas.A7.uScale ρ (Work.KMTPlan.A6.lcL l₁ l₂ L 0) : ℤ))) := by
    intro j s n ξ hξ
    have hval : (if n = 0 then (0 : ℂ) else if Work.KMTPlan.A6.lowSmallSet ρ C₀ a l₁ l₂ L 0 n
        then Work.KMTPlan.A6.varphiNtj (Nat.floor (a n)) L j s ξ else 0) ≠ 0 := hξ
    have hn0 : ¬ (n = 0) := by intro h; rw [if_pos h] at hval; exact hval rfl
    have hls : Work.KMTPlan.A6.lowSmallSet ρ C₀ a l₁ l₂ L 0 n := by
      by_contra h; rw [if_neg hn0, if_neg h] at hval; exact hval rfl
    have hφ : Work.KMTPlan.A6.varphiNtj (Nat.floor (a n)) L j s ξ ≠ 0 := by
      intro h; rw [if_neg hn0, if_pos hls, h] at hval; exact hval rfl
    have hφt : Work.KMTAreas.A7.varphiNt (Nat.floor (a n)) L s ξ ≠ 0 := by
      intro h; exact hφ (by rw [Work.KMTPlan.A6.varphiNtj, h, mul_zero])
    have hsup := Work.KMTAreas.A7.varphiNt_support (Nat.floor (a n)) L s ξ hφt
    have hw := hwin n hls
    have hexp : (L : ℝ) - (Work.Analysis.EndVar.logN (Nat.floor (a n)) : ℝ)
        ≤ (((-(3 * (Work.KMTAreas.A7.uScale ρ (Work.KMTPlan.A6.lcL l₁ l₂ L 0) : ℤ))) : ℤ) : ℝ) := by
      rw [hLc]
      have hZ : (L : ℤ) + 3 * (Work.KMTAreas.A7.uScale ρ L : ℤ)
          ≤ Work.Analysis.EndVar.logN (Nat.floor (a n)) := by
        have h3 : ((L + 3 * Work.KMTAreas.A7.uScale ρ L : ℕ) : ℤ)
            ≤ ((Work.Analysis.EndVar.logN (Nat.floor (a n))).toNat : ℕ) := by exact_mod_cast hw
        rw [Int.toNat_of_nonneg (Work.Analysis.EndVar.logN_nonneg _)] at h3
        push_cast at h3 ⊢
        exact h3
      have hZR : (L : ℝ) + 3 * (Work.KMTAreas.A7.uScale ρ L : ℝ)
          ≤ (Work.Analysis.EndVar.logN (Nat.floor (a n)) : ℝ) := by exact_mod_cast hZ
      push_cast
      linarith
    calc |ξ| ≤ (2 : ℝ) ^ ((L : ℝ) - (Work.Analysis.EndVar.logN (Nat.floor (a n)) : ℝ)) := hsup
      _ ≤ (2 : ℝ) ^ (-(3 * (Work.KMTAreas.A7.uScale ρ (Work.KMTPlan.A6.lcL l₁ l₂ L 0) : ℤ))) := by
          rw [← Real.rpow_intCast]
          exact Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp
  have hsupG : ∀ (j : ℤ) (s : ℝ) (n : ℕ) (ξ : ℝ),
      Work.KMTPlan.A6.lowModSymbG ρ P C₀ a l₁ l₂ L 0 j s n ξ ≠ 0 →
      |ξ| ≤ (2 : ℝ)
        ^ (-(3 * (P.natDegree : ℤ) * (Work.KMTAreas.A7.uScale ρ (Work.KMTPlan.A6.lcL l₁ l₂ L 0) : ℤ))) := by
    intro j s n ξ hξ
    have hval : (if n = 0 then (0 : ℂ) else if Work.KMTPlan.A6.lowSmallSet ρ C₀ a l₁ l₂ L 0 n
        then Work.KMTPlan.A6.varphitildeNtj P (Nat.floor (a n)) 0 j s ξ else 0) ≠ 0 := hξ
    have hn0 : ¬ (n = 0) := by intro h; rw [if_pos h] at hval; exact hval rfl
    have hls : Work.KMTPlan.A6.lowSmallSet ρ C₀ a l₁ l₂ L 0 n := by
      by_contra h; rw [if_neg hn0, if_neg h] at hval; exact hval rfl
    have hψ : Work.KMTPlan.A6.varphitildeNtj P (Nat.floor (a n)) 0 j s ξ ≠ 0 := by
      intro h; rw [if_neg hn0, if_pos hls, h] at hval; exact hval rfl
    have hψt : Work.KMTAreas.A7.varphitildeNt P P.natDegree (Nat.floor (a n)) 0 s ξ ≠ 0 := by
      intro h; exact hψ (by rw [Work.KMTPlan.A6.varphitildeNtj, h, mul_zero])
    have hsup := Work.KMTAreas.A7.varphitildeNt_support_all P P.natDegree (Nat.floor (a n)) 0 s ξ hψt
    have hw := hwin n hls
    have h3u : 3 * (Work.KMTAreas.A7.uScale ρ L : ℝ)
        ≤ (Work.Analysis.EndVar.logN (Nat.floor (a n)) : ℝ) := by
      have hZ : (L : ℤ) + 3 * (Work.KMTAreas.A7.uScale ρ L : ℤ)
          ≤ Work.Analysis.EndVar.logN (Nat.floor (a n)) := by
        have h3 : ((L + 3 * Work.KMTAreas.A7.uScale ρ L : ℕ) : ℤ)
            ≤ ((Work.Analysis.EndVar.logN (Nat.floor (a n))).toNat : ℕ) := by exact_mod_cast hw
        rw [Int.toNat_of_nonneg (Work.Analysis.EndVar.logN_nonneg _)] at h3
        push_cast at h3 ⊢
        exact h3
      have hZR : (L : ℝ) + 3 * (Work.KMTAreas.A7.uScale ρ L : ℝ)
          ≤ (Work.Analysis.EndVar.logN (Nat.floor (a n)) : ℝ) := by exact_mod_cast hZ
      linarith
    have hexp : (P.natDegree : ℝ) * (((0 : ℕ) : ℝ) - (Work.Analysis.EndVar.logN (Nat.floor (a n)) : ℝ))
        ≤ (((-(3 * (P.natDegree : ℤ) * (Work.KMTAreas.A7.uScale ρ (Work.KMTPlan.A6.lcL l₁ l₂ L 0) : ℤ))) : ℤ) : ℝ) := by
      rw [hLc]
      push_cast
      have hd0 : (0 : ℝ) ≤ (P.natDegree : ℝ) := by positivity
      have h := mul_le_mul_of_nonneg_left h3u hd0
      linarith
    calc |ξ| ≤ (2 : ℝ) ^ ((P.natDegree : ℝ) * (((0 : ℕ) : ℝ) - (Work.Analysis.EndVar.logN (Nat.floor (a n)) : ℝ))) := hsup
      _ ≤ (2 : ℝ) ^ (-(3 * (P.natDegree : ℤ) * (Work.KMTAreas.A7.uScale ρ (Work.KMTPlan.A6.lcL l₁ l₂ L 0) : ℤ))) := by
          rw [← Real.rpow_intCast]
          exact Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp

  set maxl : ℝ := max (l₁ : ℝ) (l₂ : ℝ) with hmaxldef
  have hmaxl_nonneg : 0 ≤ maxl := by rw [hmaxldef]; positivity
  set F2 : ENNReal := MeasureTheory.eLpNorm f 2 MeasureTheory.Measure.count with hF2def
  set G2 : ENNReal := MeasureTheory.eLpNorm g 2 MeasureTheory.Measure.count with hG2def
  set FRZ : ENNReal := ENNReal.ofReal (C_RM * ((Nat.log2 Kv : ℝ) + 2) ^ (2 : ℝ)) *
      ((Cssu : ENNReal) * ENNReal.ofReal ((2 : ℝ) ^ (-(cS * maxl)))
        * ((C Λ : ENNReal) * (C Λ : ENNReal))) * F2 * G2 with hFRZdef
  set SPK : ENNReal := (Cssu : ENNReal) * ENNReal.ofReal ((2 : ℝ) ^ (-(cS * maxl))) *
      (ENNReal.ofReal Cbp * F2) * (ENNReal.ofReal Cbp * G2) with hSPKdef
  have hFrzFam : ∀ (j₁ j₂ : ℤ) (s : ℝ), s ∈ Set.Icc (1 / 2 : ℝ) 1 →
      j₁ ∈ ({-1, 0, 1} : Finset ℤ) → j₂ ∈ ({-1, 0, 1} : Finset ℤ) → j₂ ≠ -1 →
      MeasureTheory.eLpNorm (fun x : ℤ => Work.Analysis.Variation.VrFull 2 Kv
        (fun n : ℕ => Work.KMTPlan.A6.caseBAnchored ρ P C₀ a f g l₁ l₂ L 0 j₁ j₂ s n x))
        1 MeasureTheory.Measure.count ≤ FRZ := by
    intro j₁ j₂ s hs hj₁ hj₂ hj₂ne
    have hkj₁ : ¬ (L = 0 ∧ j₁ = (-1 : ℤ)) := by rintro ⟨h1, -⟩; omega
    have hk₁ad : L ≠ 0 ∨ 0 ≤ j₁ := by
      by_cases hL : L = 0
      · right
        rcases (by simpa using hj₁ : j₁ = -1 ∨ j₁ = 0 ∨ j₁ = 1) with h | h | h
        · exact absurd ⟨hL, h⟩ hkj₁
        · omega
        · omega
      · exact Or.inl hL
    have hk₂ad : ¬ ((0 : ℕ) = 0 ∧ j₂ = -1) := by rintro ⟨-, h2⟩; exact hj₂ne h2
    have hbF : ∀ (n : ℕ) (ξ : ℝ),
        ‖lowModSymbF ρ C₀ a l₁ l₂ L 0 j₁ s n ξ‖ ≤ 8 := by
      intro n ξ
      simp only [lowModSymbF]
      split_ifs with hn hls
      · simp
      · exact norm_varphiNtj_le_eight (Nat.floor (a n)) L j₁ hj₁ hk₁ad
          (Nat.le_floor (by exact_mod_cast ha1 n)) s ξ
      · simp
    have hbG : ∀ (n : ℕ) (ξ : ℝ),
        ‖lowModSymbG ρ P C₀ a l₁ l₂ L 0 j₂ s n ξ‖ ≤ Cb := by
      intro n ξ
      simp only [lowModSymbG]
      split_ifs with hn hls
      · simp only [norm_zero]; exact hCb.le
      · exact hCbb (Nat.floor (a n)) 0 j₂ s hj₂ hk₂ad
          (Nat.le_floor (by exact_mod_cast ha1 n)) ξ
      · simp only [norm_zero]; exact hCb.le
    have h := hFRZgen C₀ hC₀ ρ hρ B C hRanF hRanG cS hcS Cssu hSS
      (Work.KMTAreas.A7.uScale ρ (Work.KMTPlan.A6.lcL l₁ l₂ L 0)) Λ hΛ a ha ha1
      l₁ l₂ L 0 Kv (by rw [hLc]; exact le_trans hB_le_Bc hBcL) huL hu2
      j₁ j₂ hj₁ hj₂ (by rintro ⟨h1, -⟩; omega) (by rintro ⟨-, h2⟩; exact hj₂ne h2)
      s hs f g hf hg (hsupF j₁ s) (hsupG j₂ s) 8 Cb hbF hbG
    simpa only [hFRZdef, hmaxldef, hF2def, hG2def, Work.KMTPlan.A6.caseBAnchored] using h
  have hSpkFam : ∀ (j₁ j₂ : ℤ) (s : ℝ), s ∈ Set.Icc (1 / 2 : ℝ) 1 →
      j₁ ∈ ({-1, 0, 1} : Finset ℤ) → j₂ ∈ ({-1, 0, 1} : Finset ℤ) → j₂ ≠ -1 →
      Work.KMTPlan.A6.lowSmallSet ρ C₀ a l₁ l₂ L 0 0 →
      MeasureTheory.eLpNorm (fun x : ℤ => ENNReal.ofReal
        ‖Work.KMTPlan.A6.caseBSpike ρ P a f g l₁ l₂ L 0 j₁ j₂ s x‖)
        1 MeasureTheory.Measure.count ≤ SPK := by
    intro j₁ j₂ s hs hj₁ hj₂ hj₂ne h0
    have hsupSpk : ∀ Nr : ℕ, Work.Analysis.EndVar.inIndexSet C₀ (max (l₁ : ℤ) (l₂ : ℤ))
        (L : ℤ) (0 : ℤ) Nr →
        Nr ≤ Work.KMTAreas.A7.splitCut ρ (Work.KMTPlan.A6.lcL l₁ l₂ L 0) →
        Bc ≤ Work.KMTPlan.A6.lcL l₁ l₂ L 0 →
        L + 3 * Work.KMTAreas.A7.uScale ρ (Work.KMTPlan.A6.lcL l₁ l₂ L 0)
          ≤ (Work.Analysis.EndVar.logN Nr).toNat := by
      intro Nr hidx hcut hBc'
      obtain ⟨-, hLh, -⟩ := hidx
      have hLh' : L ≤ Work.Analysis.EndVar.heightScale C₀ Nr := by exact_mod_cast hLh
      simpa only [hLc] using (hWin L Nr (le_trans hBwin_le_Bc hBcL) hLh').2
    have huL2 : (max l₁ l₂ : ℝ) ≤ (Work.KMTAreas.A7.uScale ρ L : ℝ) := by
      simpa only [hmaxldef, hLc] using huL
    have hu2L : (2 : ℝ) ^ (ρ * (max l₁ l₂ : ℝ)) ≤ (Work.KMTAreas.A7.uScale ρ L : ℝ) := by
      simpa only [hmaxldef, hLc] using hu2
    have h := Work.KMTPlan.A6.Linf.caseBSpikeLeHighLow P hd ρ hρ hcS hSS C₀ hC₀ hρC₀ a l₁ l₂ L
      j₁ j₂ s hs hj₁ hj₂ (by rintro ⟨h1, -⟩; omega)
      (by rintro ⟨-, h2⟩; exact hj₂ne h2)
      Bc hsupSpk hBcL hLc hu1 huL2 hu2L hNA₁ hNA₂ h0 hCb hCbb f g hf hg
    simpa only [hSPKdef, hCbpdef, hmaxldef, hF2def, hG2def] using h
  have hSpkMask : ∀ (j₁ j₂ : ℤ) (s : ℝ), s ∈ Set.Icc (1 / 2 : ℝ) 1 →
      j₁ ∈ ({-1, 0, 1} : Finset ℤ) → j₂ ∈ ({-1, 0, 1} : Finset ℤ) → j₂ ≠ -1 →
      MeasureTheory.eLpNorm (fun x : ℤ =>
        if Work.KMTPlan.A6.lowSmallSet ρ C₀ a l₁ l₂ L 0 0 then
          ENNReal.ofReal ‖Work.KMTPlan.A6.caseBSpike ρ P a f g l₁ l₂ L 0 j₁ j₂ s x‖ else 0)
        1 MeasureTheory.Measure.count ≤ SPK := by
    intro j₁ j₂ s hs hj₁ hj₂ hj₂ne
    by_cases h0 : Work.KMTPlan.A6.lowSmallSet ρ C₀ a l₁ l₂ L 0 0
    · simpa only [if_pos h0] using hSpkFam j₁ j₂ s hs hj₁ hj₂ hj₂ne h0
    · have hz : (fun x : ℤ => if Work.KMTPlan.A6.lowSmallSet ρ C₀ a l₁ l₂ L 0 0 then
          ENNReal.ofReal ‖Work.KMTPlan.A6.caseBSpike ρ P a f g l₁ l₂ L 0 j₁ j₂ s x‖ else 0)
          = (0 : ℤ → ENNReal) := by
        funext x; rw [if_neg h0]; rfl
      rw [hz, MeasureTheory.eLpNorm_zero]; exact bot_le
  have hwConst : PointwiseErgodicTheorems.variationalNorm r
      (fun n : ℕ => if Bw ≤ Nat.floor (a n) then (1 : ℂ) else 0) ≤ ENNReal.ofReal 3 := by
    by_cases hex : ∃ n : ℕ, Bw ≤ Nat.floor (a n)
    · have hmono : Monotone fun n : ℕ => Nat.floor (a n) :=
        Work.KMTPlan.A6.floor_monotone_of_lacunary hΛ ha
      set n₀ : ℕ := Nat.find hex with hn₀def
      have hspec : Bw ≤ Nat.floor (a n₀) := Nat.find_spec hex
      have hp : ∀ n : ℕ, (Bw ≤ Nat.floor (a n)) ↔ n₀ ≤ n := by
        intro n
        constructor
        · intro h; exact Nat.find_min' hex h
        · intro h; exact le_trans (le_trans hspec (hmono h)) le_rfl
      exact maskedConstVar hr1 hp
    · have hz : (fun n : ℕ => if Bw ≤ Nat.floor (a n) then (1 : ℂ) else 0)
          = (0 : ℕ → ℂ) := by
        funext n; rw [if_neg (fun h => hex ⟨n, h⟩)]; rfl
      rw [hz, Work.KMTPlan.A6.variationalNorm_zero_nat hr1]
      exact bot_le
  have hWM := Work.KMTPlan.A6.caseBSliceWMeasInt ρ P C₀ a f g l₁ l₂ L 0 (-1) 1
    (Work.KMTAreas.A7.uScale ρ (Work.KMTPlan.A6.lcL l₁ l₂ L 0))
    (fun n t => if Bw ≤ Nat.floor (a n) then Work.KMTPlan.A6.mdlW3 P (Nat.floor (a n)) t else 0)
    (fun n => by
      by_cases h : Bw ≤ Nat.floor (a n)
      · simpa only [if_pos h] using (Work.KMTPlan.A6.mdl_W3_continuous P (Nat.floor (a n))).measurable
      · simpa only [if_neg h] using measurable_const)
    (fun n hn => by
      obtain ⟨Cw, -, hCw⟩ := Work.KMTPlan.A6.mdl_W3_bound P (Nat.floor (a n))
      refine ⟨Cw, fun t ht => ?_⟩
      rw [if_pos (hlower n hn)]
      exact hCw t ht)
    (by simp) (by norm_num) (Or.inl (by omega)) (Or.inr (by norm_num)) hf hg
  have hB1 : MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
      (fun n : ℕ => Work.KMTPlan.A6.lowDecayB ρ P C₀ a f g l₁ l₂ L 0 (-1) 0 1 (fun _ => 1) n x))
      1 MeasureTheory.Measure.count ≤ ENNReal.ofReal 6 * (FRZ + 2 * SPK) := by
    have h := Work.KMTPlan.A6.lowDecayBVarNorm ρ P C₀ a f g l₁ l₂ L 0 (-1) 0 1 r hr2 Bw 3 (fun _ => 1)
      Kv hKv1 hlssK hlower hwConst hf hg
      (FRZ := FRZ) (SPK := SPK)
      (hFrzFam (-1) 0 1 (by norm_num) (by simp) (by norm_num) (by norm_num))
      (hSpkMask (-1) 0 1 (by norm_num) (by simp) (by norm_num) (by norm_num))
    refine h.trans ?_
    rw [show (2 : ENNReal) * ENNReal.ofReal 3 = ENNReal.ofReal 6 from by
      rw [show (2 : ENNReal) = ENNReal.ofReal 2 from (ENNReal.ofReal_natCast 2).symm,
        ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
      norm_num]
  have hB2 : MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
      (fun n : ℕ => Work.KMTPlan.A6.lowDecayB ρ P C₀ a f g l₁ l₂ L 0 (-1) 0 (1 / 2)
        (fun _ => 1) n x))
      1 MeasureTheory.Measure.count ≤ ENNReal.ofReal 6 * (FRZ + 2 * SPK) := by
    have h := Work.KMTPlan.A6.lowDecayBVarNorm ρ P C₀ a f g l₁ l₂ L 0 (-1) 0 (1 / 2) r hr2 Bw 3 (fun _ => 1)
      Kv hKv1 hlssK hlower hwConst hf hg
      (FRZ := FRZ) (SPK := SPK)
      (hFrzFam (-1) 0 (1 / 2) (by norm_num) (by simp) (by norm_num) (by norm_num))
      (hSpkMask (-1) 0 (1 / 2) (by norm_num) (by simp) (by norm_num) (by norm_num))
    refine h.trans ?_
    rw [show (2 : ENNReal) * ENNReal.ofReal 3 = ENNReal.ofReal 6 from by
      rw [show (2 : ENNReal) = ENNReal.ofReal 2 from (ENNReal.ofReal_natCast 2).symm,
        ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
      norm_num]
  have hWfam : MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
      (fun n : ℕ => Work.KMTPlan.A6.lowDecayW ρ P C₀ a f g l₁ l₂ L 0 (-1) 1
        (fun n t => Work.KMTPlan.A6.mdlW3 P (Nat.floor (a n)) t) n x))
      1 MeasureTheory.Measure.count ≤ ENNReal.ofReal (2 * Cw3) * (FRZ + 2 * SPK) := by
    have h := Work.KMTPlan.A6.lowDecayWVarNorm ρ P C₀ a f g l₁ l₂ L 0 (-1) 1 r hr2 Bw Cw3
      (fun n t => Work.KMTPlan.A6.mdlW3 P (Nat.floor (a n)) t) Kv hKv1 hlssK hlower
      (fun t ht => by simpa only [hmaxldef] using hWmask a Λ t hΛ ha ht)
      hWM.1 hWM.2 hf hg
      (fun t ht => hFrzFam (-1) 1 t ht (by simp) (by norm_num) (by norm_num))
      (fun t ht => hSpkMask (-1) 1 t ht (by simp) (by norm_num) (by norm_num))
    have h2Cw : (2 : ENNReal) * ENNReal.ofReal Cw3 = ENNReal.ofReal (2 * Cw3) := by
      rw [show (2 : ENNReal) = ENNReal.ofReal 2 from (ENNReal.ofReal_natCast 2).symm,
        ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
    rw [← h2Cw]
    exact h
  have hc1 : ‖(Work.KMTPlan.A6.mdlScaleF L : ℂ) * Work.KMTPlan.A6.mdlIota‖ₑ
      ≤ ENNReal.ofReal ((2 : ℝ) ^ (-(L : ℝ))) := by
    have hi : ‖Work.KMTPlan.A6.mdlIota‖ ≤ 1 := by
      rw [Work.KMTPlan.A6.mdlIota, norm_inv]
      refine inv_le_one_of_one_le₀ ?_
      rw [norm_mul, norm_mul, Complex.norm_I, mul_one]
      have hpi : (1 : ℝ) ≤ 2 * Real.pi := by linarith [Real.pi_gt_three]
      calc (1 : ℝ) = 1 * 1 := (mul_one 1).symm
        _ ≤ (2 * Real.pi) * (1 : ℝ) := by
            refine mul_le_mul hpi le_rfl (by norm_num) (by positivity)
        _ = ‖(2 : ℂ)‖ * ‖(Real.pi : ℂ)‖ := by
            have h2c : ‖(2 : ℂ)‖ = 2 := by norm_num
            have hpic : ‖(Real.pi : ℂ)‖ = Real.pi := by
              rw [show ((Real.pi : ℂ)) = ((Real.pi : ℝ) : ℂ) from rfl,
                norm_ofReal_coe _ Real.pi_pos.le]
            rw [h2c, hpic]
            ring
    have hval : Work.KMTPlan.A6.mdlScaleF L = (2 : ℝ) ^ (-(L : ℝ)) := by
      rw [Work.KMTPlan.A6.mdlScaleF]
    have h1 : ‖(((Work.KMTPlan.A6.mdlScaleF L : ℝ)) : ℂ)‖ₑ
        = ENNReal.ofReal ((2 : ℝ) ^ (-(L : ℝ))) := by
      rw [enorm_eq_ofReal_norm, norm_ofReal_coe _ (by rw [hval]; positivity), hval]
    rw [enorm_mul, h1]
    calc ENNReal.ofReal ((2 : ℝ) ^ (-(L : ℝ))) * ‖Work.KMTPlan.A6.mdlIota‖ₑ
        ≤ ENNReal.ofReal ((2 : ℝ) ^ (-(L : ℝ))) * 1 := by
          refine mul_le_mul' le_rfl ?_
          rw [enorm_eq_ofReal_norm]
          simpa using ENNReal.ofReal_le_ofReal hi
      _ = ENNReal.ofReal ((2 : ℝ) ^ (-(L : ℝ))) := mul_one _
  have hc2 : ‖(((Work.KMTPlan.A6.mdlScaleFG P L 0 : ℝ)) : ℂ)‖ₑ
      ≤ ENNReal.ofReal ((2 : ℝ) ^ (-(L : ℝ))) := by
    have hval : Work.KMTPlan.A6.mdlScaleFG P L 0 = (2 : ℝ) ^ (-(L : ℝ)) := by
      rw [Work.KMTPlan.A6.mdlScaleFG]; simp
    rw [enorm_eq_ofReal_norm, norm_ofReal_coe _ (by rw [hval]; positivity), hval]
  have hpt : ∀ x : ℤ, PointwiseErgodicTheorems.variationalNorm r
      (fun n : ℕ => Work.KMTPlan.A6.lowModel ρ P C₀ a f g l₁ l₂ L 0 n x)
      ≤ ‖(Work.KMTPlan.A6.mdlScaleF L : ℂ) * Work.KMTPlan.A6.mdlIota‖ₑ *
          (PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ =>
              Work.KMTPlan.A6.lowDecayB ρ P C₀ a f g l₁ l₂ L 0 (-1) 0 1 (fun _ => 1) n x)
            + PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ =>
              Work.KMTPlan.A6.lowDecayB ρ P C₀ a f g l₁ l₂ L 0 (-1) 0 (1 / 2) (fun _ => 1) n x))
        + ‖(((Work.KMTPlan.A6.mdlScaleFG P L 0 : ℝ)) : ℂ)‖ₑ *
          PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ =>
            Work.KMTPlan.A6.lowDecayW ρ P C₀ a f g l₁ l₂ L 0 (-1) 1
              (fun n t => Work.KMTPlan.A6.mdlW3 P (Nat.floor (a n)) t) n x) := by
    intro x
    exact variationalNorm_affine_le hr1 _ _ _ _
      ((Work.KMTPlan.A6.mdlScaleF L : ℂ) * Work.KMTPlan.A6.mdlIota)
      (((Work.KMTPlan.A6.mdlScaleFG P L 0 : ℝ)) : ℂ)
      (fun n => Work.KMTPlan.A6.lowModel_eq_decayHighLow ρ P C₀ a f g l₁ l₂ L hL1 hLc hN1 hf hg n x)
  have hE1 : MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
      (fun n : ℕ => Work.KMTPlan.A6.lowModel ρ P C₀ a f g l₁ l₂ L 0 n x))
      1 MeasureTheory.Measure.count
      ≤ ‖(Work.KMTPlan.A6.mdlScaleF L : ℂ) * Work.KMTPlan.A6.mdlIota‖ₑ *
          (MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
              (fun n : ℕ => Work.KMTPlan.A6.lowDecayB ρ P C₀ a f g l₁ l₂ L 0 (-1) 0 1
                (fun _ => 1) n x)) 1 MeasureTheory.Measure.count
            + MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
              (fun n : ℕ => Work.KMTPlan.A6.lowDecayB ρ P C₀ a f g l₁ l₂ L 0 (-1) 0 (1 / 2)
                (fun _ => 1) n x)) 1 MeasureTheory.Measure.count)
        + ‖(((Work.KMTPlan.A6.mdlScaleFG P L 0 : ℝ)) : ℂ)‖ₑ *
          MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
            (fun n : ℕ => Work.KMTPlan.A6.lowDecayW ρ P C₀ a f g l₁ l₂ L 0 (-1) 1
              (fun n t => Work.KMTPlan.A6.mdlW3 P (Nat.floor (a n)) t) n x))
            1 MeasureTheory.Measure.count := by
    refine (eLpNorm_le_of_le_int _ _ hpt).trans ?_
    refine (eLpNorm_add_le_int _ _).trans ?_
    refine add_le_add ?_ ?_
    · refine (eLpNorm_const_mul_eq (by
          rw [enorm_mul, enorm_eq_ofReal_norm, enorm_eq_ofReal_norm]
          exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top) _).le.trans ?_
      exact mul_le_mul' le_rfl (eLpNorm_add_le_int _ _)
    · exact (eLpNorm_const_mul_eq (by
          rw [enorm_eq_ofReal_norm]
          exact ENNReal.ofReal_ne_top) _).le
  have hcombm : ‖(Work.KMTPlan.A6.mdlScaleF L : ℂ) * Work.KMTPlan.A6.mdlIota‖ₑ *
        (MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
            (fun n : ℕ => Work.KMTPlan.A6.lowDecayB ρ P C₀ a f g l₁ l₂ L 0 (-1) 0 1
              (fun _ => 1) n x)) 1 MeasureTheory.Measure.count
          + MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
            (fun n : ℕ => Work.KMTPlan.A6.lowDecayB ρ P C₀ a f g l₁ l₂ L 0 (-1) 0 (1 / 2)
              (fun _ => 1) n x)) 1 MeasureTheory.Measure.count)
      + ‖(((Work.KMTPlan.A6.mdlScaleFG P L 0 : ℝ)) : ℂ)‖ₑ *
        MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
          (fun n : ℕ => Work.KMTPlan.A6.lowDecayW ρ P C₀ a f g l₁ l₂ L 0 (-1) 1
            (fun n t => Work.KMTPlan.A6.mdlW3 P (Nat.floor (a n)) t) n x))
          1 MeasureTheory.Measure.count
      ≤ ENNReal.ofReal ((2 : ℝ) ^ (-(L : ℝ)) * Aco) * (FRZ + 2 * SPK) := by
    refine le_trans (add_le_add
      (mul_le_mul' hc1 (add_le_add hB1 hB2)) (mul_le_mul' hc2 hWfam)) ?_
    rw [hAcdef, mul_add,
      ofReal_mul_ofReal_mul_eq (FRZ + 2 * SPK) (by positivity) (by norm_num : (0 : ℝ) ≤ 6),
      ofReal_mul_ofReal_mul_eq (FRZ + 2 * SPK) (by positivity) (by positivity : (0 : ℝ) ≤ 2 * Cw3),
      ← add_mul, ← add_mul]
    refine mul_le_mul' (le_of_eq ?_) le_rfl
    rw [ofReal_add_eq _ _ (by positivity) (by positivity),
      ofReal_add_eq _ _ (by positivity) (by positivity)]
    congr 1
    ring
  have hRMloss : ((Nat.log2 Kv : ℝ) + 2) ^ (2 : ℝ)
      ≤ 4 * Work.KMTPlan.A6.lowMfun Λ * (2 : ℝ) ^ (4 * ρ * (L : ℝ)) := by
    have h0 := Work.KMTPlan.A6.lowTruncLogBoundIndep ρ hρ Λ hΛ L
    have hbr : ((Nat.log2 Kv : ℝ) + 2) ^ (2 : ℝ) = ((Nat.log2 Kv : ℝ) + 2) ^ (2 : ℕ) := by
      rw [Real.rpow_two, pow_two]
    rw [hbr]
    simp only [hKvdef, hDdef]
    exact h0
  set FRZr : ℝ := C_RM * ((Nat.log2 Kv : ℝ) + 2) ^ (2 : ℝ) * (Cssu : ℝ) *
      (2 : ℝ) ^ (-(cS * maxl)) * (((C Λ : NNReal) : ℝ) * ((C Λ : NNReal) : ℝ)) with hFRZrdef
  set SPKr : ℝ := (Cssu : ℝ) * (2 : ℝ) ^ (-(cS * maxl)) * (Cbp * Cbp) with hSPKrdef
  have hFRZr_nn : 0 ≤ FRZr := by rw [hFRZrdef]; positivity
  have hSPKr_nn : 0 ≤ SPKr := by rw [hSPKrdef]; positivity
  have hFRZle : FRZ ≤ ENNReal.ofReal FRZr * F2 * G2 := by
    rw [hFRZdef, hFRZrdef, hmaxldef, hF2def, hG2def,
      ← ENNReal.ofReal_coe_nnreal (p := Cssu), ← ENNReal.ofReal_coe_nnreal (p := C Λ)]
    rw [ofReal_frozenSplit _ _ _ _ (by positivity) (by positivity) (by positivity) (by positivity)]
  have hSPKle : SPK ≤ ENNReal.ofReal SPKr * F2 * G2 := by
    rw [hSPKdef, hSPKrdef, hmaxldef, hCbpdef, hF2def, hG2def,
      ← ENNReal.ofReal_coe_nnreal (p := Cssu)]
    have hreass : ENNReal.ofReal ((Cssu : NNReal) : ℝ) *
          ENNReal.ofReal ((2 : ℝ) ^ (-(cS * max (l₁ : ℝ) (l₂ : ℝ)))) *
          (ENNReal.ofReal (max 8 Cb) * MeasureTheory.eLpNorm f 2 MeasureTheory.Measure.count) *
          (ENNReal.ofReal (max 8 Cb) * MeasureTheory.eLpNorm g 2 MeasureTheory.Measure.count)
        = (ENNReal.ofReal ((Cssu : NNReal) : ℝ) *
            ENNReal.ofReal ((2 : ℝ) ^ (-(cS * max (l₁ : ℝ) (l₂ : ℝ)))) *
            (ENNReal.ofReal (max 8 Cb) * ENNReal.ofReal (max 8 Cb))) *
          (MeasureTheory.eLpNorm f 2 MeasureTheory.Measure.count *
            MeasureTheory.eLpNorm g 2 MeasureTheory.Measure.count) := by ring
    rw [hreass,
      ← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ ((Cssu : NNReal) : ℝ)),
      ← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ max 8 Cb),
      ← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ ((Cssu : NNReal) : ℝ)
        * (2 : ℝ) ^ (-(cS * max (l₁ : ℝ) (l₂ : ℝ)))),
      ← mul_assoc]
  have hFSP : FRZ + 2 * SPK ≤ ENNReal.ofReal (FRZr + 2 * SPKr) * (F2 * G2) := by
    have h2 : (2 : ENNReal) = ENNReal.ofReal 2 := (ENNReal.ofReal_natCast 2).symm
    have h2SPKr : (0 : ℝ) ≤ 2 * SPKr := by linarith [hSPKr_nn]
    have hle1 : FRZ ≤ ENNReal.ofReal FRZr * (F2 * G2) :=
      le_trans hFRZle (le_of_eq (by ring))
    have hle2 : 2 * SPK ≤ ENNReal.ofReal (2 * SPKr) * (F2 * G2) := by
      calc (2 : ENNReal) * SPK ≤ 2 * (ENNReal.ofReal SPKr * F2 * G2) :=
            mul_le_mul' le_rfl hSPKle
        _ = ENNReal.ofReal 2 * (ENNReal.ofReal SPKr * (F2 * G2)) := by rw [h2]; ring
        _ = ENNReal.ofReal (2 * SPKr) * (F2 * G2) := by
            rw [show ENNReal.ofReal 2 * (ENNReal.ofReal SPKr * (F2 * G2))
                = (ENNReal.ofReal 2 * ENNReal.ofReal SPKr) * (F2 * G2) from by ring,
              ← ENNReal.ofReal_mul (show (0 : ℝ) ≤ 2 by norm_num)]
    calc FRZ + 2 * SPK
        ≤ ENNReal.ofReal FRZr * (F2 * G2) + ENNReal.ofReal (2 * SPKr) * (F2 * G2) :=
          add_le_add hle1 hle2
      _ = (ENNReal.ofReal FRZr + ENNReal.ofReal (2 * SPKr)) * (F2 * G2) := by rw [add_mul]
      _ = ENNReal.ofReal (FRZr + 2 * SPKr) * (F2 * G2) := by
          rw [← ENNReal.ofReal_add hFRZr_nn h2SPKr]
  have hAbsorb : (2 : ℝ) ^ (-(L : ℝ)) * Aco * (FRZr + 2 * SPKr)
      ≤ Kf Λ * (2 : ℝ) ^ (-((min cS 1 / 2) * (L : ℝ))) := by
    have hΔ : (2 : ℝ) ^ (-(L : ℝ)) * (2 : ℝ) ^ (4 * ρ * (L : ℝ))
        ≤ (2 : ℝ) ^ (-((min cS 1 / 2) * (L : ℝ))) := by
      rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
      refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
      have hc : min cS 1 / 2 ≤ 1 - 4 * ρ := by
        have h2 : 4 * ρ ≤ 1 / 2 := by linarith [hρ8]
        have h3 : min cS 1 ≤ 1 := min_le_right _ _
        linarith
      nlinarith
    have hΔ' : (2 : ℝ) ^ (-(L : ℝ))
        ≤ (2 : ℝ) ^ (-((min cS 1 / 2) * (L : ℝ))) := by
      refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
      have h3 : min cS 1 ≤ 1 := min_le_right _ _
      have hc : min cS 1 / 2 ≤ 1 := by linarith
      nlinarith
    have hps : (2 : ℝ) ^ (-(cS * maxl)) ≤ 1 := by
      rw [← Real.rpow_zero (2 : ℝ)]
      refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
      nlinarith [hcS, hmaxl_nonneg]
    have hZeq : FRZr + 2 * SPKr = (Cssu : ℝ) * (2 : ℝ) ^ (-(cS * maxl)) *
        (C_RM * ((Nat.log2 Kv : ℝ) + 2) ^ (2 : ℝ)
            * (((C Λ : NNReal) : ℝ) * ((C Λ : NNReal) : ℝ)) + 2 * (Cbp * Cbp)) := by
      rw [hFRZrdef, hSPKrdef]; ring
    have hKfΛ : Kf Λ = Aco * (Cssu : ℝ) *
        (4 * C_RM * Work.KMTPlan.A6.lowMfun Λ
          * (((C Λ : NNReal) : ℝ) * ((C Λ : NNReal) : ℝ)) + 2 * (Cbp * Cbp)) := by
      rw [hKfdef]
    rw [hZeq, hKfΛ]
    set pL : ℝ := (2 : ℝ) ^ (-(L : ℝ)) with hpLdef
    set pc : ℝ := (2 : ℝ) ^ (-((min cS 1 / 2) * (L : ℝ))) with hpcdef
    set pρ : ℝ := (2 : ℝ) ^ (4 * ρ * (L : ℝ)) with hpρdef
    set ps : ℝ := (2 : ℝ) ^ (-(cS * maxl)) with hpsdef
    set rr : ℝ := ((Nat.log2 Kv : ℝ) + 2) ^ (2 : ℝ) with hrrdef
    set mm : ℝ := Work.KMTPlan.A6.lowMfun Λ with hmmdef
    set DD : ℝ := ((C Λ : NNReal) : ℝ) * ((C Λ : NNReal) : ℝ) with hDDdef
    set BB : ℝ := Cbp * Cbp with hBBdef
    have hpL0 : 0 < pL := by rw [hpLdef]; positivity
    have hpc0 : 0 < pc := by rw [hpcdef]; positivity
    have hps0 : 0 < ps := by rw [hpsdef]; positivity
    have hmm0 : 0 ≤ mm := by rw [hmmdef]; exact Work.KMTPlan.A6.lowMfun_nonneg Λ
    have hDD0 : 0 ≤ DD := by rw [hDDdef]; positivity
    have hBB0 : 0 ≤ BB := by rw [hBBdef]; positivity
    have hCssu0 : 0 ≤ ((Cssu : NNReal) : ℝ) := by positivity
    have hps1 : ps ≤ 1 := by rw [hpsdef]; exact hps
    have hΔm : pL * pρ ≤ pc := by rw [hpLdef, hpρdef, hpcdef]; exact hΔ
    have hΔm' : pL ≤ pc := by rw [hpLdef, hpcdef]; exact hΔ'
    have hRMm : rr ≤ 4 * mm * pρ := by rw [hrrdef, hmmdef, hpρdef]; exact hRMloss
    have hACs : 0 ≤ Aco * (Cssu : ℝ) := mul_nonneg hAco_pos.le hCssu0
    have hA : C_RM * rr * DD + 2 * BB ≤ C_RM * (4 * mm * pρ) * DD + 2 * BB :=
      add_le_add (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hRMm hC_RM.le) hDD0) le_rfl
    have hB : (Cssu : ℝ) * ps * (C_RM * rr * DD + 2 * BB)
        ≤ (Cssu : ℝ) * ps * (C_RM * (4 * mm * pρ) * DD + 2 * BB) :=
      mul_le_mul_of_nonneg_left hA (mul_nonneg hCssu0 hps0.le)
    have hC : pL * Aco * ((Cssu : ℝ) * ps * (C_RM * rr * DD + 2 * BB))
        ≤ pL * Aco * ((Cssu : ℝ) * ps * (C_RM * (4 * mm * pρ) * DD + 2 * BB)) :=
      mul_le_mul_of_nonneg_left hB (mul_nonneg hpL0.le hAco_pos.le)
    have hD : pL * Aco * ((Cssu : ℝ) * ps * (C_RM * (4 * mm * pρ) * DD + 2 * BB))
        = Aco * (Cssu : ℝ) * ps * (4 * C_RM * mm * (pL * pρ) * DD + 2 * (pL * BB)) := by
      ring
    have hE : 4 * C_RM * mm * (pL * pρ) * DD + 2 * (pL * BB)
        ≤ 4 * C_RM * mm * pc * DD + 2 * (pc * BB) := by
      refine add_le_add ?_ ?_
      · rw [show 4 * C_RM * mm * (pL * pρ) * DD = 4 * C_RM * (mm * (pL * pρ) * DD) from by ring,
          show 4 * C_RM * mm * pc * DD = 4 * C_RM * (mm * pc * DD) from by ring]
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hΔm hmm0) hDD0)
          (by linarith [hC_RM] : (0 : ℝ) ≤ 4 * C_RM)
      · exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hΔm' hBB0)
          (by norm_num : (0 : ℝ) ≤ 2)
    have hF : Aco * (Cssu : ℝ) * ps * (4 * C_RM * mm * (pL * pρ) * DD + 2 * (pL * BB))
        ≤ Aco * (Cssu : ℝ) * ps * (4 * C_RM * mm * pc * DD + 2 * (pc * BB)) :=
      mul_le_mul_of_nonneg_left hE (mul_nonneg hACs hps0.le)
    have hG : Aco * (Cssu : ℝ) * ps * (4 * C_RM * mm * pc * DD + 2 * (pc * BB))
        = Aco * (Cssu : ℝ) * ps * (4 * C_RM * mm * DD + 2 * BB) * pc := by ring
    have hpsA : Aco * (Cssu : ℝ) * ps ≤ Aco * (Cssu : ℝ) := by
      simpa using mul_le_mul_of_nonneg_left hps1 hACs
    have hH : Aco * (Cssu : ℝ) * ps * (4 * C_RM * mm * DD + 2 * BB) * pc
        ≤ Aco * (Cssu : ℝ) * (4 * C_RM * mm * DD + 2 * BB) * pc :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hpsA
          (by positivity : (0 : ℝ) ≤ 4 * C_RM * mm * DD + 2 * BB)) hpc0.le
    exact le_trans hC (le_trans (le_of_eq hD) (le_trans hF (le_trans (le_of_eq hG) hH)))
  have hCc := ENNReal.coe_toNNReal (a := ENNReal.ofReal (Kf Λ)) ENNReal.ofReal_ne_top
  have hcW : Work.KMTPlan.A6.lcWeight (min cS 1 / 2) l₁ l₂ L 0
      = (2 : ℝ) ^ (-((min cS 1 / 2) * (L : ℝ))) := by
    have hLmax : Work.Analysis.EndVar.lmax l₁ l₂ ((L : ℕ) : ℤ) ((0 : ℕ) : ℤ) = (L : ℤ) := by
      simp only [Work.Analysis.EndVar.lmax]
      rw [max_eq_left (show ((0 : ℕ) : ℤ) ≤ ((L : ℕ) : ℤ) by omega)]
      exact max_eq_right (by omega)
    simp only [Work.KMTPlan.A6.lcWeight, hLmax, Int.cast_natCast]
  rw [hCc, hcW]
  calc MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
        (fun n : ℕ => Work.KMTPlan.A6.lowModel ρ P C₀ a f g l₁ l₂ L 0 n x))
        1 MeasureTheory.Measure.count
      ≤ ENNReal.ofReal ((2 : ℝ) ^ (-(L : ℝ)) * Aco) * (FRZ + 2 * SPK) := hE1.trans hcombm
    _ ≤ ENNReal.ofReal ((2 : ℝ) ^ (-(L : ℝ)) * Aco)
          * (ENNReal.ofReal (FRZr + 2 * SPKr) * (F2 * G2)) := mul_le_mul' le_rfl hFSP
    _ = ENNReal.ofReal ((2 : ℝ) ^ (-(L : ℝ)) * Aco * (FRZr + 2 * SPKr)) * (F2 * G2) := by
        rw [ofReal_mul_ofReal_mul_eq (F2 * G2) (by positivity) (by positivity)]
    _ ≤ ENNReal.ofReal (Kf Λ * (2 : ℝ) ^ (-((min cS 1 / 2) * (L : ℝ)))) * (F2 * G2) :=
        mul_le_mul' (ENNReal.ofReal_le_ofReal hAbsorb) le_rfl
    _ = ENNReal.ofReal (Kf Λ) * ENNReal.ofReal ((2 : ℝ) ^ (-((min cS 1 / 2) * (L : ℝ))))
          * F2 * G2 := by
        rw [ENNReal.ofReal_mul (hKfnn Λ)]
        ring

end

end Work.KMTPlan.A6.Linf
