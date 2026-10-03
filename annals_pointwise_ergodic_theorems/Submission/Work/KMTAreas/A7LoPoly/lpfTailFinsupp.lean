import Mathlib
import Submission.Work.KMTAreas.A7G.tailVarBound
import Submission.Work.KMTAreas.A7Hi.lpfTailArith
import Submission.Work.KMTPlan.A6.ContinuousVarFromLatticeR
import Submission.Port.Aesm

/-!
# The `ρ`-variation (`ρ = r > 2`) large-scale bound for the low-pass Ionescu--Wainger walk,
in a **name-clash-free** module

Target (`Work.KMTAreas.A7LoPoly.lpfTailFinsupp`): for `0 < ρ ≤ 1`, `2 < r`, `1 < p` there are
`Cρ, Cκ > 0` and `B ≥ 0` such that for every `l₁ m₀` with good major arcs there is `κ` with
`κ + 1 ≤ Cκ (1+l₁)²` and, for every finitely supported `f`,

`‖ V^r_{n ≥ 2^κ} (n ↦ Π_{≤l₁,≤-(m₀+n)} f) ‖_{ℓᵖ} ≤ B ‖f‖_{ℓᵖ}`,

with `B` **free of `l₁`** and the threshold `2^κ` allowed to grow like `2^{(1+l₁)²}`.

This is the statement of `Work.A7HiRep.lpfLargeScaleRhoRep`; it is re-proved here so that the
statement is available in a module whose import closure avoids
`Submission.Work.KMTAreas.A7Hi2.supBound` (which re-declares `abelCoef`, clashing with
`Submission.Work.KMTAreas.A7Hi2.abelAnnuli`); consequently nothing below imports
`Submission.Work.A7Hi2.supPartFinsuppOfLargeScale` nor `…A7Hi.largeScaleGather`.

## The route

The `2 < r` statement is proved **without any continuous estimate**, by the *single-decimation*
(KMSZ (6.22)) factorisation `Work.KMTAreas.A7Hi.lpf_decim_fact` together with the *proved*
decimated dilation variational estimate `Work.A7Hi2.decimDilVarUnif` (`dilVarRealScale_prop` =
JSW Theorem 1.1 for real lacunary scales).  The three points that make it work:

* **the threshold.**  `Work.KMTAreas.A7Hi.lpfTailArith` supplies `κ` with
  `κ + 1 ≤ Cκ (1+l₁)²` and `6 · iwQl ρ l₁ ≤ 2^{m₀ + 2^κ}`.  The factorisation
  `lpf_decim_fact` is available at every level `m₀ + n` with `n ≥ 2^κ` once the *coarse* level is
  tied to `m₀`: take `C₀ := m₀ + 2^κ - 1` (so `C₀ + 1 = m₀ + 2^κ ≤ m₀ + n`), and the narrowness
  `3 · iwQl ρ l₁ < 2^{C₀}` follows from the arithmetic tail bound;
* **no aliasing in the decimated kernel.**  The walk's fine symbol is the *compactly supported*
  bump `η(2^{m₀+n}·)`, so on the tail the decimated kernel is *exactly* `Q` times the sampled
  dilation kernel of the *fixed* Schwartz profile `kmtPhiSch = 𝓕 η` at the increasing lacunary
  scales `2^{m₀+n}` — the proved identity
  `Work.KMTAreas.A7G.iwConv_torsFinset_eq_smul_decimDilFam`;
* **the constant.**  `decimDilVarUnif` gives the variational estimate with the sharp constant
  `Cv / Q`, which cancels the factor `Q` of the decimated kernel; the coarse factor
  `Π_{≤l₁,≤-C₀}` is `ℓᵖ`-bounded with an `l₁`-free constant (`kmtProj_lp_bound_uniform`).
-/

namespace Work.KMTAreas.A7LoPoly

open MeasureTheory Finset
open scoped ENNReal NNReal BigOperators

set_option maxHeartbeats 1500000

/-- **The `r`-variation over the index tail `[lo, ∞)` is dominated by the `V^r`-norm of the
shifted sequence.** -/
theorem varRhoFrom_le_varNorm_shift (r : NNReal) (hr : 1 ≤ r) (lo : ℕ) (a : ℕ → ℂ) :
    Work.BourgainPlan.Maximal.varRhoFrom (r : ℝ) lo a
      ≤ PointwiseErgodicTheorems.variationalNorm r (fun j : ℕ => a (lo + j)) := by
  have hmain : Work.BourgainPlan.Maximal.varRhoFrom (r : ℝ) lo a
      ≤ Submission.PointwiseErgodicTheorems.varPart r (fun j : ℕ => a (lo + j)) := by
    rw [Work.BourgainPlan.Maximal.varRhoFrom]
    refine iSup_le fun hi => ?_
    rw [Work.BourgainPlan.Maximal.varRho]
    refine iSup_le fun J => iSup_le fun t => iSup_le fun ht => iSup_le fun hb => ?_
    have hlo : lo ≤ t 0 := (hb 0 (Nat.zero_le J)).1
    have ht'mono : Monotone (fun j => t j - lo) :=
      fun i j hij => Nat.sub_le_sub_right (ht hij) lo
    have hchain : Work.BourgainPlan.Maximal.chainLp (r : ℝ) J a t
        = Work.BourgainPlan.Maximal.chainLp (r : ℝ) J (fun j => a (lo + j))
            (fun j => t j - lo) :=
      Work.BourgainPlan.Maximal.chainLp_shift (r : ℝ) J lo a t ht hlo
    rw [hchain]
    refine le_iSup_of_le J (le_iSup_of_le (fun j => t j - lo) (le_iSup_of_le ht'mono ?_))
    exact le_of_eq (Work.KMTPlan.A6.ofReal_norm_toLp_eq_ofReal_chainLp r hr J
      (fun j => a (lo + j)) (fun j => t j - lo)).symm
  refine hmain.trans ?_
  rw [Submission.PointwiseErgodicTheorems.variationalNorm_eq_add]
  exact le_add_left le_rfl

theorem lpfTailFinsupp (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (r : ℝ) (hr : 2 < r)
    (p : ℝ) (hp : 1 < p) :
    ∃ Cρ : ℝ, 0 < Cρ ∧ ∃ Cκ : ℝ, 0 < Cκ ∧ ∃ B : ℝ, 0 ≤ B ∧
      ∀ (l₁ m₀ : ℕ), Work.Analysis.IonescuWainger.GoodMajorArcs ρ Cρ l₁ (-(m₀ : ℤ)) →
        ∃ κ : ℕ, (κ : ℝ) + 1 ≤ Cκ * (1 + (l₁ : ℝ)) ^ 2 ∧
          ∀ f : ℤ →₀ ℂ,
            MeasureTheory.eLpNorm (fun y : ℤ => Work.BourgainPlan.Maximal.varRhoFrom r (2 ^ κ)
                (fun n : ℕ => Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ n (⇑f) y))
              (ENNReal.ofReal p) MeasureTheory.Measure.count
            ≤ ENNReal.ofReal B *
                MeasureTheory.eLpNorm (⇑f) (ENNReal.ofReal p) MeasureTheory.Measure.count := by
  -- the `r`-variation exponent as an `NNReal`
  obtain ⟨rn, hrn⟩ : ∃ rn : NNReal, (rn : ℝ) = r := ⟨⟨r, le_of_lt (by linarith)⟩, rfl⟩
  have hr1 : (1 : NNReal) ≤ rn := by
    have : (1 : ℝ) ≤ (rn : ℝ) := by rw [hrn]; linarith
    exact_mod_cast this
  have hrn2 : 2 < rn := by
    have : (2 : ℝ) < (rn : ℝ) := by rw [hrn]; linarith
    exact_mod_cast this
  -- the uniform Ionescu--Wainger single-scale bound
  obtain ⟨Cρ_S, hCρ_S_pos, Cs, hCs_pos, hsingle⟩ :=
    Work.KMTAreas.A7.kmtProj_lp_bound_uniform ρ hρ hρ1 p hp
  -- the decimated dilation variational estimate, uniform in the decimation
  obtain ⟨Cv, hCv_pos, hdec⟩ :=
    Work.A7Hi2.decimDilVarUnif Work.KMTAreas.A7Hi2.dilVarRealScale_prop
      Work.KMTAreas.A7Hi.kmtPhiSch rn hrn2 p hp
  -- the threshold arithmetic
  obtain ⟨Cκ, hCκ_pos, harith⟩ := Work.KMTAreas.A7Hi.lpfTailArith ρ hρ hρ1
  refine ⟨Cρ_S, hCρ_S_pos, 2 * Cκ + 1, by positivity, Cv * Cs, by positivity, ?_⟩
  intro l₁ m₀ hgood
  obtain ⟨κ₀, hκ₀budget, hκ₀tail⟩ := harith l₁ m₀
  set κ : ℕ := κ₀ + 1 with hκdef
  have hbudget : (κ : ℝ) + 1 ≤ (2 * Cκ + 1) * (1 + (l₁ : ℝ)) ^ 2 := by
    have hl : (0 : ℝ) ≤ (l₁ : ℝ) := Nat.cast_nonneg l₁
    have h1 : (1 : ℝ) ≤ (1 + (l₁ : ℝ)) ^ 2 := by
      nlinarith [sq_nonneg (1 + (l₁ : ℝ)), hl]
    have h2 : (κ₀ : ℝ) + 1 ≤ Cκ * (1 + (l₁ : ℝ)) ^ 2 := hκ₀budget
    have h4 : (0 : ℝ) ≤ Cκ * (1 + (l₁ : ℝ)) ^ 2 := by positivity
    have h3 : (κ : ℝ) = (κ₀ : ℝ) + 1 := by rw [hκdef]; push_cast; ring
    rw [h3]; nlinarith [h1, h2, h4]
  refine ⟨κ, hbudget, ?_⟩
  intro f
  -- ### the arithmetic data
  set Q : ℕ := Work.Analysis.IonescuWainger.iwQl ρ l₁ with hQdef
  have hQ1 : 1 ≤ Q := hQdef ▸ Work.Analysis.IonescuWainger.iwQl_pos
  have hQpos : (0 : ℝ) < (Q : ℝ) := by exact_mod_cast hQ1
  have h2κ : 1 ≤ 2 ^ κ := Nat.one_le_two_pow
  have h2κ₀ : 1 ≤ 2 ^ κ₀ := Nat.one_le_two_pow
  set C₀ : ℕ := m₀ + 2 ^ κ - 1 with hC₀def
  have hpowκ : 2 ^ κ₀ + 1 ≤ 2 ^ κ := by
    rw [show κ = κ₀ + 1 from hκdef, pow_succ]
    have h2 : 1 ≤ 2 ^ κ₀ := Nat.one_le_two_pow
    omega
  have hC₀eq : C₀ + 1 = m₀ + 2 ^ κ := by rw [hC₀def]; omega
  have hC₀ge : m₀ ≤ C₀ := by rw [hC₀def]; omega
  have hC₀pos : 1 ≤ C₀ := by omega
  have hnarrow : 3 * Q < 2 ^ C₀ := by
    have h6 : 6 * Q ≤ 2 ^ (m₀ + 2 ^ κ₀) := hκ₀tail
    have hm : 2 ^ (m₀ + 2 ^ κ₀) ≤ 2 ^ C₀ := by
      refine Nat.pow_le_pow_right (by norm_num) ?_
      omega
    calc 3 * Q < 6 * Q := by omega
      _ ≤ 2 ^ (m₀ + 2 ^ κ₀) := h6
      _ ≤ 2 ^ C₀ := hm
  have hgood0 : Work.Analysis.IonescuWainger.GoodMajorArcs ρ Cρ_S l₁ (-(C₀ : ℤ)) := by
    rw [Work.Analysis.IonescuWainger.GoodMajorArcs] at hgood ⊢
    push_cast at hgood ⊢
    have h : (m₀ : ℝ) ≤ (C₀ : ℝ) := by exact_mod_cast hC₀ge
    linarith
  -- ### the coarse factor and the walk identity on the tail
  set h₀ : ℤ → ℂ := Work.KMTContract.kmtProj ρ l₁ (-(C₀ : ℤ)) (⇑f) with hh₀
  have hwalk : ∀ (j : ℕ) (y : ℤ),
      Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ (2 ^ κ + j) (⇑f) y
        = (Q : ℂ) * Work.A7Hi2.decimDilFam (m₀ + 2 ^ κ) Work.KMTAreas.A7Hi.kmtPhiSch Q h₀ j y := by
    intro j y
    set L : ℕ := (m₀ + 2 ^ κ) + j with hLdef
    have hL1 : 1 ≤ L := by omega
    have hfine : C₀ + 1 ≤ m₀ + (2 ^ κ + j) := by omega
    have hfac := congrFun (Work.KMTAreas.A7Hi.lpf_decim_fact ρ l₁ m₀ C₀ (2 ^ κ + j) Cρ_S
      hgood hnarrow hfine f) y
    have hlev : (-((m₀ : ℤ) + (((2 ^ κ + j : ℕ)) : ℤ))) = -(L : ℤ) := by
      rw [hLdef]; push_cast; ring
    rw [hlev] at hfac
    -- the kernel of the `Q`-torsion symbol is the decimated kernel
    have hker' : ∀ i : ℤ, Work.Analysis.IWMultiplier.iwKernel
        (Work.Analysis.IonescuWainger.iwSymbolSet (Work.KMTPlan.A6.Decim.torsFinset Q)
          (Work.KMTPlan.A6.Decim.bump L)) i
        = Work.BourgainPlan.Thm52.decimatedKernel Q
            (Work.Analysis.IonescuWainger.etaCut Work.KMTContract.kmtEta (-(L : ℤ))) i :=
      fun i => Work.KMTAreas.A7Hi.iwKernel_torsFinset_bump_eq_decimatedKernel Q L hQ1 hL1 i
    have hr : (∑' i : ℤ, Work.BourgainPlan.Thm52.decimatedKernel Q
          (Work.Analysis.IonescuWainger.etaCut Work.KMTContract.kmtEta (-(L : ℤ))) (y - i) * h₀ i)
        = Work.Analysis.IWMultiplier.iwConv (Work.KMTPlan.A6.Decim.torsFinset Q)
            (Work.KMTPlan.A6.Decim.bump L) h₀ y := by
      have hre : (∑' i : ℤ, Work.BourgainPlan.Thm52.decimatedKernel Q
            (Work.Analysis.IonescuWainger.etaCut Work.KMTContract.kmtEta (-(L : ℤ))) (y - i) * h₀ i)
          = ∑' i : ℤ, Work.BourgainPlan.Thm52.decimatedKernel Q
              (Work.Analysis.IonescuWainger.etaCut Work.KMTContract.kmtEta (-(L : ℤ))) i * h₀ (y - i) := by
        have h := Equiv.tsum_eq (Equiv.subLeft y) (fun i : ℤ =>
          Work.BourgainPlan.Thm52.decimatedKernel Q
            (Work.Analysis.IonescuWainger.etaCut Work.KMTContract.kmtEta (-(L : ℤ))) i * h₀ (y - i))
        simpa [Equiv.subLeft_apply, sub_sub_cancel] using h
      rw [hre, Work.Analysis.IWMultiplier.iwConv_apply]
      exact tsum_congr (fun i => by rw [hker' i, smul_eq_mul])
    rw [show Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ (2 ^ κ + j) (⇑f)
        = Work.KMTContract.kmtProj ρ l₁ (-((m₀ : ℤ) + ((2 ^ κ + j : ℕ) : ℤ))) (⇑f) from rfl,
      hlev, hfac, hr, hLdef]
    exact Work.KMTAreas.A7G.iwConv_torsFinset_eq_smul_decimDilFam Q (m₀ + 2 ^ κ) j hQ1
      (by omega) h₀ y
  -- ### the variational bound
  have hm₀' : Q ≤ Work.KMTAreas.A7Hi.lpfScale (m₀ + 2 ^ κ) 0 := by
    have hle : 2 ^ (m₀ + 2 ^ κ₀) ≤ 2 ^ (m₀ + 2 ^ κ) :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    refine le_trans (le_trans (by omega : Q ≤ 6 * Q) hκ₀tail) ?_
    rw [Work.KMTAreas.A7Hi.lpfScale, Nat.add_zero]
    exact hle
  have hdec' : MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm rn
        (fun j : ℕ => Work.A7Hi2.decimDilFam (m₀ + 2 ^ κ) Work.KMTAreas.A7Hi.kmtPhiSch Q h₀ j x))
        (ENNReal.ofReal p) MeasureTheory.Measure.count
      ≤ ENNReal.ofReal (Cv / (Q : ℝ)) *
        MeasureTheory.eLpNorm h₀ (ENNReal.ofReal p) MeasureTheory.Measure.count :=
    hdec Q hQ1 (m₀ + 2 ^ κ) hm₀' h₀
  -- the pointwise domination by the variational norm of the shifted family
  have hpt : ∀ y : ℤ, Work.BourgainPlan.Maximal.varRhoFrom r (2 ^ κ)
        (fun n : ℕ => Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ n (⇑f) y)
      ≤ ‖(Q : ℂ)‖ₑ * PointwiseErgodicTheorems.variationalNorm rn
          (fun j : ℕ => Work.A7Hi2.decimDilFam (m₀ + 2 ^ κ) Work.KMTAreas.A7Hi.kmtPhiSch Q h₀ j y) := by
    intro y
    have hshift := varRhoFrom_le_varNorm_shift rn hr1 (2 ^ κ)
      (fun n : ℕ => Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ n (⇑f) y)
    have hfam : (fun j : ℕ => Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ (2 ^ κ + j) (⇑f) y)
        = (Q : ℂ) • (fun j : ℕ =>
            Work.A7Hi2.decimDilFam (m₀ + 2 ^ κ) Work.KMTAreas.A7Hi.kmtPhiSch Q h₀ j y) := by
      funext j
      rw [Pi.smul_apply, smul_eq_mul]
      exact hwalk j y
    rw [hfam, Submission.PointwiseErgodicTheorems.variationalNorm_smul hr1] at hshift
    simpa only [hrn] using hshift
  -- ### the `eLpNorm` assembly
  have hQenorm : ‖(Q : ℂ)‖ₑ = ENNReal.ofReal (Q : ℝ) := by
    rw [← ofReal_norm, Complex.norm_natCast]
  have hp0E : ENNReal.ofReal p ≠ 0 := ENNReal.ofReal_ne_zero_iff.mpr (lt_trans zero_lt_one hp)
  have hmono : MeasureTheory.eLpNorm (fun y : ℤ => Work.BourgainPlan.Maximal.varRhoFrom r (2 ^ κ)
        (fun n : ℕ => Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ n (⇑f) y))
        (ENNReal.ofReal p) MeasureTheory.Measure.count
      ≤ MeasureTheory.eLpNorm (fun y : ℤ => ‖(Q : ℂ)‖ₑ *
          PointwiseErgodicTheorems.variationalNorm rn
            (fun j : ℕ => Work.A7Hi2.decimDilFam (m₀ + 2 ^ κ) Work.KMTAreas.A7Hi.kmtPhiSch Q h₀ j y))
        (ENNReal.ofReal p) MeasureTheory.Measure.count := by
    refine MeasureTheory.eLpNorm_mono_enorm (hf := by pw_aesm) (fun y => ?_)
    simpa only [enorm_eq_self] using hpt y
  have hconst : MeasureTheory.eLpNorm (fun y : ℤ => ‖(Q : ℂ)‖ₑ *
        PointwiseErgodicTheorems.variationalNorm rn
          (fun j : ℕ => Work.A7Hi2.decimDilFam (m₀ + 2 ^ κ) Work.KMTAreas.A7Hi.kmtPhiSch Q h₀ j y))
        (ENNReal.ofReal p) MeasureTheory.Measure.count
      = ‖(Q : ℂ)‖ₑ * MeasureTheory.eLpNorm (fun y : ℤ =>
          PointwiseErgodicTheorems.variationalNorm rn
            (fun j : ℕ => Work.A7Hi2.decimDilFam (m₀ + 2 ^ κ) Work.KMTAreas.A7Hi.kmtPhiSch Q h₀ j y))
        (ENNReal.ofReal p) MeasureTheory.Measure.count :=
    Commons.MeasureTheory.Lp.eLpNorm_const_mul_ennreal
      (by rw [hQenorm]; exact ENNReal.ofReal_ne_top) hp0E ENNReal.ofReal_ne_top
  calc MeasureTheory.eLpNorm (fun y : ℤ => Work.BourgainPlan.Maximal.varRhoFrom r (2 ^ κ)
        (fun n : ℕ => Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ n (⇑f) y))
        (ENNReal.ofReal p) MeasureTheory.Measure.count
      ≤ MeasureTheory.eLpNorm (fun y : ℤ => ‖(Q : ℂ)‖ₑ *
          PointwiseErgodicTheorems.variationalNorm rn
            (fun j : ℕ => Work.A7Hi2.decimDilFam (m₀ + 2 ^ κ) Work.KMTAreas.A7Hi.kmtPhiSch Q h₀ j y))
        (ENNReal.ofReal p) MeasureTheory.Measure.count := hmono
    _ = ‖(Q : ℂ)‖ₑ * MeasureTheory.eLpNorm (fun y : ℤ =>
          PointwiseErgodicTheorems.variationalNorm rn
            (fun j : ℕ => Work.A7Hi2.decimDilFam (m₀ + 2 ^ κ) Work.KMTAreas.A7Hi.kmtPhiSch Q h₀ j y))
        (ENNReal.ofReal p) MeasureTheory.Measure.count := hconst
    _ ≤ ‖(Q : ℂ)‖ₑ * (ENNReal.ofReal (Cv / (Q : ℝ)) *
          MeasureTheory.eLpNorm h₀ (ENNReal.ofReal p) MeasureTheory.Measure.count) :=
        mul_le_mul_of_nonneg_left hdec' bot_le
    _ = ENNReal.ofReal Cv *
          MeasureTheory.eLpNorm h₀ (ENNReal.ofReal p) MeasureTheory.Measure.count := by
        rw [hQenorm, ← mul_assoc, ← ENNReal.ofReal_mul hQpos.le,
          show (Q : ℝ) * (Cv / (Q : ℝ)) = Cv by field_simp]
    _ ≤ ENNReal.ofReal Cv * (ENNReal.ofReal Cs *
          MeasureTheory.eLpNorm (⇑f) (ENNReal.ofReal p) MeasureTheory.Measure.count) :=
        mul_le_mul_of_nonneg_left (hsingle l₁ (-(C₀ : ℤ)) hgood0 (⇑f)) bot_le
    _ = ENNReal.ofReal (Cv * Cs) *
          MeasureTheory.eLpNorm (⇑f) (ENNReal.ofReal p) MeasureTheory.Measure.count := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul hCv_pos.le]

end Work.KMTAreas.A7LoPoly
