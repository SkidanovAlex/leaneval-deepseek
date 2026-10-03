import Mathlib
import Submission.Work.KMTAreas.A7G.tailAbs
import Submission.Port.Aesm

/-!
# The low-pass variational estimate in the decimation ("large-scale") regime

This file proves `Work.KMTPlan.A6.lowpassVarFromDecim`: for `0 < ρ ≤ 1`, an exponent `R > 2`, a
lacunary sequence of scales `a` (`Λ`-lacunary, `Λ > 1`, `a n ≥ 1`) all of which are large compared
with the Ionescu–Wainger common denominator `iwQl ρ l` of the arithmetic height `l`, the
`R`-variational norm of the low-pass walk

`n ↦ Π_{≤l, ≤ -Log ⌊a n⌋} g = kmtProj ρ l (-(Log ⌊a n⌋)) g`

is bounded in `ℓ²(ℤ)` (counting measure) by `C (1+l)² ‖g‖_{ℓ²}`, with `C` free of `l` and of the
lacunary sequence, on the good major arcs.

## The mechanism: *no shallow window* — decimation everywhere

The tree's own route to the low-pass walk splits the index range into

* a **shallow window** `m ≲ log₂ (3 · iwQl ρ l) ≍ 2^l` (the levels where the fine bump is wider
  than the `Q = iwQl ρ l` lattice and the decimation identity *fails*), controlled by a
  Rademacher–Menshov argument with `l`-dependent cost; and
* the **tail** `m > log₂ (3 Q)`, where the KMSZ (6.22) decimation identity holds and the walk is
  homothetic to a genuine lacunary dilation family, giving an `l`-free bound.

Here the extra hypothesis `6 · iwQl ρ l ≤ 2^{Log ⌊a n⌋}` (i.e. every scale of the lacunary family
is `≥ 6 Q`) kills the shallow window entirely: *every* level of *every* family member is already in
the decimation regime.  The remaining content is the decimation identity plus the (proved)
decimated dilation variational estimate `Work.A7Hi2.decimDilVarUnif`, whose constant `C_v / Q` is
exactly cancelled by the factor `Q` of the decimated kernel — see the helper `walkDecimVarBound`
below.

## Main declarations

* `walkDecimVarBound` — the *large-scale* variational bound for the whole walk
  `n ↦ lpf ρ l C₀ (1+n) f` (all levels `> C₀`), with an absolute constant;
* `lowpassVarFromDecim` — the target, obtained from `walkDecimVarBound` by choosing the coarse level
  `C₀ = N 0 - 1` (`N n = (Log ⌊a n⌋).toNat`) and reindexing the lacunary family into the walk
  (`Work.KMTAreas.A7.variationalNorm_comp_mono_le`).
-/

namespace Work.KMTPlan.A6

open MeasureTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

/-! ## Elementary bookkeeping for lacunary scales -/

/-- **The levels of a lacunary sequence are monotone.**  `Λ > 1` and `a n ≥ 1` force
`a n < a (n+1)`, hence `⌊a n⌋ ≤ ⌊a (n+1)⌋`. -/
theorem monotone_floor_lacunary {Λ : NNReal} (hΛ : 1 < Λ) {a : ℕ → NNReal}
    (ha : PointwiseErgodicTheorems.Lacunary Λ a) (ha1 : ∀ n : ℕ, 1 ≤ a n) :
    Monotone fun n => Nat.floor (a n) := by
  refine monotone_nat_of_le_succ fun n => ?_
  have hpos : (0 : NNReal) < a n := lt_of_lt_of_le zero_lt_one (ha1 n)
  have hne : a n ≠ 0 := ne_of_gt hpos
  have h : Λ < a (n + 1) / a n := ha n
  have h2 : a n < a (n + 1) := by
    have h3 : a (n + 1) = (a (n + 1) / a n) * a n := by rw [div_mul_cancel₀ _ hne]
    rw [h3]
    calc a n = 1 * a n := (one_mul _).symm
      _ < (a (n + 1) / a n) * a n := mul_lt_mul_of_pos_right (lt_trans hΛ h) hpos
  exact Nat.floor_mono (le_of_lt h2)

/-- `Log N` is (the cast of) its own `toNat`. -/
theorem logN_eq_toNat (N : ℕ) :
    Work.Analysis.EndVar.logN N = (((Work.Analysis.EndVar.logN N).toNat : ℕ) : ℤ) :=
  (Int.toNat_of_nonneg (Work.Analysis.EndVar.logN_nonneg N)).symm

/-! ## The decimation-regime variational bound for the whole walk

This is `Work.KMTAreas.A7G.Abs.tailVarBoundCoarse` with the *height difference*
`lpf ρ l · - lpf ρ (l-1) ·` replaced by the single term `h₀ = kmtProj ρ l (-(C₀)) f`. -/

/-- **The large-scale (decimation-regime) `R`-variational bound for the low-pass walk.**

For `0 < ρ ≤ 1`, `2 < R`, `1 < p` there are `Cρ > 0` and `C > 0` such that for every `l` and every
coarse level `C₀` which is (i) coarser than the `Q = iwQl ρ l` lattice (`3 Q < 2^{C₀}`) and
(ii) good major arcs at the coarse level (`Cρ · 2^{ρl} ≤ C₀`), the `R`-variational norm of the walk
`n ↦ Π_{≤l,≤-(C₀+1+n)} f = lpf ρ l C₀ (1+n) f` is bounded in `ℓᵖ(ℤ)` by `C ‖f‖_{ℓᵖ}`, uniformly in
`l`, `C₀` and `f`. -/
theorem walkDecimVarBound (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (R : NNReal) (hR : 2 < R) (p : ℝ) (hp : 1 < p) :
    ∃ Cρ : ℝ, 0 < Cρ ∧ ∃ C : ℝ, 0 < C ∧
      ∀ (l C₀ : ℕ), Work.Analysis.IonescuWainger.GoodMajorArcs ρ Cρ l (-(C₀ : ℤ)) →
        3 * Work.Analysis.IonescuWainger.iwQl ρ l < 2 ^ C₀ → ∀ f : ℤ → ℂ,
        MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm R
            (fun n : ℕ => Work.KMTAreas.A7Hi.lpf ρ l C₀ (1 + n) f x))
          (ENNReal.ofReal p) MeasureTheory.Measure.count
        ≤ ENNReal.ofReal C * MeasureTheory.eLpNorm f (ENNReal.ofReal p)
            MeasureTheory.Measure.count := by
  -- the two analytic inputs: the uniform single-scale bound and the decimated dilation estimate
  obtain ⟨Cρ_S, hCρ_Spos, Cs, hCs_pos, hsingle⟩ :=
    Work.KMTAreas.A7.kmtProj_lp_bound_uniform ρ hρ hρ1 p hp
  obtain ⟨Cv, hCv_pos, hdec⟩ :=
    Work.A7Hi2.decimDilVarUnif Work.KMTAreas.A7Hi2.dilVarRealScale_prop
      Work.KMTAreas.A7Hi.kmtPhiSch R hR p hp
  have hp0 : (0 : ℝ) < p := lt_trans zero_lt_one hp
  have hp0' : ENNReal.ofReal p ≠ 0 := ENNReal.ofReal_ne_zero_iff.mpr hp0
  have hr1 : (1 : NNReal) ≤ R := le_trans (by norm_num) hR.le
  refine ⟨Cρ_S, hCρ_Spos, Cv * Cs, by positivity, ?_⟩
  intro l C₀ hgood hnarrow f
  by_cases hftop : MeasureTheory.eLpNorm f (ENNReal.ofReal p) MeasureTheory.Measure.count = ⊤
  · rw [hftop, ENNReal.mul_top
      (ENNReal.ofReal_ne_zero_iff.mpr (by positivity : (0 : ℝ) < Cv * Cs))]
    exact le_top
  · -- `f ∈ ℓᵖ` implies `f` is bounded, which is the hypothesis of the decimation identity
    obtain ⟨B, hB⟩ : ∃ B : ℝ, ∀ m : ℤ, ‖f m‖ ≤ B :=
      Work.KMTAreas.A7.bounded_of_eLpNorm_count_lt_top (p := ENNReal.ofReal p) hp0'
        (lt_top_iff_ne_top.mpr hftop)
    set Q : ℕ := Work.Analysis.IonescuWainger.iwQl ρ l with hQdef
    have hQ : 1 ≤ Q := by
      rw [hQdef]
      have hpos := Work.Analysis.IonescuWainger.iwQl_pos (ρ := ρ) (l := l)
      omega
    have hQpos : (0 : ℝ) < (Q : ℝ) := by exact_mod_cast hQ
    have hQenorm : ‖(Q : ℂ)‖ₑ = ENNReal.ofReal (Q : ℝ) := by
      rw [← ofReal_norm, Complex.norm_natCast]
    have hQle : Q ≤ Work.KMTAreas.A7Hi.lpfScale C₀ 0 := by
      rw [Work.KMTAreas.A7Hi.lpfScale, Nat.add_zero]
      refine le_of_lt (lt_of_le_of_lt ?_ hnarrow)
      omega
    have hAT : Work.Analysis.IonescuWainger.iwArithFreqs ρ l ⊆ Decim.torsFinset Q := by
      intro α hα
      rw [hQdef]
      exact DecimComp.mem_torsFinset_of_mem_iwArithFreqs hα
    -- the coarse projection
    set h₀ : ℤ → ℂ := Work.KMTContract.kmtProj ρ l (-(C₀ : ℤ)) f with hh₀
    -- the walk at every level of the tail is `Q` times a decimated dilation family
    have hwalk : ∀ (m : ℕ) (y : ℤ),
        Work.KMTAreas.A7Hi.lpf ρ l C₀ (1 + m) f y
          = (Q : ℂ) * Work.A7Hi2.decimDilFam C₀ Work.KMTAreas.A7Hi.kmtPhiSch Q h₀ (1 + m) y := by
      intro m y
      have h1 : Work.KMTAreas.A7Hi.lpf ρ l C₀ (1 + m) f
          = Work.KMTContract.kmtProj ρ l (-((C₀ + (1 + m) : ℕ) : ℤ)) f := rfl
      rw [h1, Work.KMTAreas.A7G.Abs.decimFactBdd ρ l C₀ Q hQ hAT hnarrow (C₀ + (1 + m))
        (by omega) f hB]
      exact Work.KMTAreas.A7G.Abs.iwConv_torsFinset_eq_smul_decimDilFam Q C₀ (1 + m) hQ
        (by omega) h₀ y
    -- the pointwise variational bound
    have hpoint : ∀ x : ℤ, PointwiseErgodicTheorems.variationalNorm R
          (fun n : ℕ => Work.KMTAreas.A7Hi.lpf ρ l C₀ (1 + n) f x)
        ≤ ‖(Q : ℂ)‖ₑ * PointwiseErgodicTheorems.variationalNorm R
            (fun m : ℕ => Work.A7Hi2.decimDilFam C₀ Work.KMTAreas.A7Hi.kmtPhiSch Q h₀ m x) := by
      intro x
      have hfam : (fun n : ℕ => Work.KMTAreas.A7Hi.lpf ρ l C₀ (1 + n) f x)
          = (Q : ℂ) • (fun n : ℕ =>
              Work.A7Hi2.decimDilFam C₀ Work.KMTAreas.A7Hi.kmtPhiSch Q h₀ (1 + n) x) := by
        funext n
        rw [Pi.smul_apply, smul_eq_mul]
        exact hwalk n x
      rw [hfam, Submission.PointwiseErgodicTheorems.variationalNorm_smul (r := R) hr1 (Q : ℂ) _]
      exact mul_le_mul_of_nonneg_left
        (Work.KMTAreas.A7.variationalNorm_comp_mono_le (r := R)
          (u := fun m : ℕ => Work.A7Hi2.decimDilFam C₀ Work.KMTAreas.A7Hi.kmtPhiSch Q h₀ m x)
          (φ := fun n : ℕ => 1 + n) (fun i j hij => Nat.add_le_add_left hij 1)) bot_le
    -- the `ℓᵖ` chain
    calc MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm R
            (fun n : ℕ => Work.KMTAreas.A7Hi.lpf ρ l C₀ (1 + n) f x))
          (ENNReal.ofReal p) MeasureTheory.Measure.count
        ≤ MeasureTheory.eLpNorm (fun x : ℤ => ‖(Q : ℂ)‖ₑ *
            PointwiseErgodicTheorems.variationalNorm R
              (fun m : ℕ => Work.A7Hi2.decimDilFam C₀ Work.KMTAreas.A7Hi.kmtPhiSch Q h₀ m x))
          (ENNReal.ofReal p) MeasureTheory.Measure.count :=
          MeasureTheory.eLpNorm_mono_enorm (hf := by pw_aesm) (fun x => by
            simpa only [enorm_eq_self] using hpoint x)
      _ = ‖(Q : ℂ)‖ₑ * MeasureTheory.eLpNorm (fun x : ℤ =>
            PointwiseErgodicTheorems.variationalNorm R
              (fun m : ℕ => Work.A7Hi2.decimDilFam C₀ Work.KMTAreas.A7Hi.kmtPhiSch Q h₀ m x))
          (ENNReal.ofReal p) MeasureTheory.Measure.count :=
          Commons.MeasureTheory.Lp.eLpNorm_const_mul_ennreal
            (by rw [hQenorm]; exact ENNReal.ofReal_ne_top) hp0' ENNReal.ofReal_ne_top
      _ ≤ ‖(Q : ℂ)‖ₑ * (ENNReal.ofReal (Cv / (Q : ℝ)) *
            MeasureTheory.eLpNorm h₀ (ENNReal.ofReal p) MeasureTheory.Measure.count) :=
          mul_le_mul_of_nonneg_left (hdec Q hQ C₀ hQle h₀) bot_le
      _ = ENNReal.ofReal Cv *
            MeasureTheory.eLpNorm h₀ (ENNReal.ofReal p) MeasureTheory.Measure.count := by
          rw [hQenorm, ← mul_assoc, ← ENNReal.ofReal_mul hQpos.le,
            show (Q : ℝ) * (Cv / (Q : ℝ)) = Cv by field_simp]
      _ ≤ ENNReal.ofReal Cv * (ENNReal.ofReal Cs *
            MeasureTheory.eLpNorm f (ENNReal.ofReal p) MeasureTheory.Measure.count) :=
          mul_le_mul_of_nonneg_left (hsingle l (-(C₀ : ℤ)) hgood f) bot_le
      _ = ENNReal.ofReal (Cv * Cs) *
            MeasureTheory.eLpNorm f (ENNReal.ofReal p) MeasureTheory.Measure.count := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul hCv_pos.le]

/-! ## The target: the lacunary low-pass estimate in the decimation regime -/

/-- **The lacunary low-pass variational estimate in the decimation (large-scale) regime.**

This is `Work.KMTPlan.A6.lacunaryProjLowpassVar2` with the *large-scale* hypothesis
`6 · iwQl ρ l ≤ 2^{Log ⌊a n⌋}` for every `n`, under which the shallow window of the walk is empty
and the whole estimate follows from the decimation identity plus the proved decimated dilation
variational estimate (no `MeanZeroVarFree`-type input, and no Rademacher–Menshov loss). -/
theorem lowpassVarFromDecim (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (R : NNReal) (hR : 2 < R)
    (Λ : NNReal) (hΛ : 1 < Λ) :
    ∃ Cρ : ℝ, 0 < Cρ ∧ ∃ C : ℝ, 0 < C ∧
      ∀ (k : ℤ) (l : ℕ) (a : ℕ → NNReal),
        PointwiseErgodicTheorems.Lacunary Λ a → (∀ n : ℕ, 1 ≤ a n) → ∀ g : ℤ → ℂ,
        Work.Analysis.IonescuWainger.GoodMajorArcs ρ Cρ l k →
        (∀ n : ℕ, -(Work.Analysis.EndVar.logN (Nat.floor (a n))) ≤ k) →
        (∀ n : ℕ, 6 * Work.Analysis.IonescuWainger.iwQl ρ l
            ≤ 2 ^ (Work.Analysis.EndVar.logN (Nat.floor (a n))).toNat) →
        MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm R
          (fun n : ℕ => Work.KMTContract.kmtProj ρ l
              (-(Work.Analysis.EndVar.logN (Nat.floor (a n)))) g x))
          2 MeasureTheory.Measure.count
        ≤ ENNReal.ofReal (C * (1 + (l : ℝ)) ^ 2) *
            MeasureTheory.eLpNorm g 2 MeasureTheory.Measure.count := by
  obtain ⟨Cρ_A, hCρ_A_pos, CA, hCA_pos, hwalkA⟩ :=
    walkDecimVarBound ρ hρ hρ1 R hR 2 (by norm_num)
  refine ⟨Cρ_A + 2, by linarith, CA, hCA_pos, ?_⟩
  intro k l a ha ha1 g hgood hk hbig
  -- the levels of the lacunary family
  set N : ℕ → ℕ := fun n => (Work.Analysis.EndVar.logN (Nat.floor (a n))).toNat with hNdef
  have hNval : ∀ n : ℕ, N n = (Work.Analysis.EndVar.logN (Nat.floor (a n))).toNat := fun n => by
    rw [hNdef]
  have hlogNval : ∀ n : ℕ, Work.Analysis.EndVar.logN (Nat.floor (a n)) = ((N n : ℕ) : ℤ) := by
    intro n
    rw [hNval n]
    exact (Int.toNat_of_nonneg (Work.Analysis.EndVar.logN_nonneg (Nat.floor (a n)))).symm
  have hmonoFloor : Monotone fun n => Nat.floor (a n) := monotone_floor_lacunary hΛ ha ha1
  have hmonoN : Monotone N := by
    intro m n hmn
    rw [hNval m, hNval n]
    exact Int.toNat_le_toNat (Work.Analysis.EndVar.logN_mono (hmonoFloor hmn))
  by_cases hgtop : MeasureTheory.eLpNorm g 2 MeasureTheory.Measure.count = ⊤
  · rw [hgtop, ENNReal.mul_top (ENNReal.ofReal_ne_zero_iff.mpr (by positivity))]
    exact le_top
  · -- ## the coarse level `C₀ = N 0 - 1` and its arithmetic
    set C₀ : ℕ := N 0 - 1 with hC₀def
    have hC₀val : C₀ = N 0 - 1 := by rw [hC₀def]
    have hQ1 : 1 ≤ Work.Analysis.IonescuWainger.iwQl ρ l := by
      have h := Work.Analysis.IonescuWainger.iwQl_pos (ρ := ρ) (l := l)
      omega
    have hN0ge2 : 2 ≤ N 0 := by
      have h6 : 6 ≤ 2 ^ N 0 := by
        calc (6 : ℕ) = 6 * 1 := (mul_one 6).symm
          _ ≤ 6 * Work.Analysis.IonescuWainger.iwQl ρ l := Nat.mul_le_mul_left 6 hQ1
          _ ≤ 2 ^ N 0 := by rw [hNval 0]; exact hbig 0
      by_contra hcon
      have hle : N 0 ≤ 1 := by omega
      have h2 : 2 ^ N 0 ≤ 2 := by
        simpa using Nat.pow_le_pow_right (by norm_num : 1 ≤ (2 : ℕ)) hle
      omega
    have hC₀eq : C₀ + 1 = N 0 := by rw [hC₀val]; omega
    have hlev : ∀ n : ℕ, C₀ + 1 ≤ N n := by
      intro n
      rw [hC₀eq]
      exact hmonoN (Nat.zero_le n)
    -- the level `C₀` is coarser than the `Q`-lattice, *strictly*
    have hnarrow : 3 * Work.Analysis.IonescuWainger.iwQl ρ l < 2 ^ C₀ := by
      have h6 : 6 * Work.Analysis.IonescuWainger.iwQl ρ l ≤ 2 ^ N 0 := by
        rw [hNval 0]; exact hbig 0
      have hne : 6 * Work.Analysis.IonescuWainger.iwQl ρ l ≠ 2 ^ N 0 := by
        intro hcon
        have h3 : (3 : ℕ) ∣ 6 * Work.Analysis.IonescuWainger.iwQl ρ l :=
          ⟨2 * Work.Analysis.IonescuWainger.iwQl ρ l, by ring⟩
        rw [hcon] at h3
        have h32 : (3 : ℕ) ∣ 2 := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3
        omega
      have hlt : 6 * Work.Analysis.IonescuWainger.iwQl ρ l < 2 ^ N 0 := lt_of_le_of_ne h6 hne
      have h2C : 2 ^ N 0 = 2 * 2 ^ C₀ := by rw [← hC₀eq, pow_succ]; ring
      have h6' : 2 * (3 * Work.Analysis.IonescuWainger.iwQl ρ l) < 2 * 2 ^ C₀ := by
        rw [show 2 * (3 * Work.Analysis.IonescuWainger.iwQl ρ l)
              = 6 * Work.Analysis.IonescuWainger.iwQl ρ l from by ring, ← h2C]
        exact hlt
      exact (Nat.mul_lt_mul_left (by norm_num : 0 < 2)).mp h6'
    -- the coarse level is good major arcs for the *single-scale* constant
    have hgoodC : Work.Analysis.IonescuWainger.GoodMajorArcs ρ Cρ_A l (-(C₀ : ℤ)) := by
      have hk0 : (-(N 0 : ℤ)) ≤ k := by
        have h := hk 0
        rwa [hlogNval 0] at h
      have h2k : (k : ℝ) ≤ -(Cρ_A + 2) * (2 : ℝ) ^ (ρ * (l : ℝ)) := hgood
      have h1 : ((-(N 0 : ℤ) : ℤ) : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk0
      push_cast at h1
      have hN0big : (Cρ_A + 2) * (2 : ℝ) ^ (ρ * (l : ℝ)) ≤ (N 0 : ℝ) := by linarith
      have ht : (1 : ℝ) ≤ (2 : ℝ) ^ (ρ * (l : ℝ)) :=
        Real.one_le_rpow (by norm_num) (by positivity)
      have hC₀R : (C₀ : ℝ) = (N 0 : ℝ) - 1 := by
        rw [hC₀val, Nat.cast_sub (by omega : 1 ≤ N 0)]
        simp
      have hgoal : Cρ_A * (2 : ℝ) ^ (ρ * (l : ℝ)) ≤ (C₀ : ℝ) := by
        rw [hC₀R]
        nlinarith [hN0big, ht, hCρ_A_pos]
      rw [Work.Analysis.IonescuWainger.GoodMajorArcs]
      simp only [Int.cast_neg, Int.cast_natCast]
      linarith
    -- ## the walk bound from the decimation theorem
    have hA := hwalkA l C₀ hgoodC hnarrow g
    rw [show ENNReal.ofReal (2 : ℝ) = (2 : ENNReal) from by norm_num] at hA
    -- ## reindexing the lacunary family into the walk
    have hlevel : ∀ n : ℕ, -(Work.Analysis.EndVar.logN (Nat.floor (a n)))
        = -(((C₀ : ℤ) + (((1 + (N n - (C₀ + 1)) : ℕ)) : ℤ))) := by
      intro n
      rw [hlogNval n]
      congr 1
      have hle' : C₀ ≤ N n := by have h := hlev n; omega
      have h1 : 1 + (N n - (C₀ + 1)) = N n - C₀ := by
        have h := hlev n
        omega
      rw [h1, Nat.cast_sub hle']
      ring
    have hpt : ∀ x : ℤ, PointwiseErgodicTheorems.variationalNorm R
          (fun n : ℕ => Work.KMTContract.kmtProj ρ l
              (-(Work.Analysis.EndVar.logN (Nat.floor (a n)))) g x)
        ≤ PointwiseErgodicTheorems.variationalNorm R
          (fun n : ℕ => Work.KMTAreas.A7Hi.lpf ρ l C₀ (1 + n) g x) := by
      intro x
      have hfam : (fun n : ℕ => Work.KMTContract.kmtProj ρ l
            (-(Work.Analysis.EndVar.logN (Nat.floor (a n)))) g x)
          = (fun n : ℕ => (fun m : ℕ => Work.KMTAreas.A7Hi.lpf ρ l C₀ (1 + m) g x)
              (N n - (C₀ + 1))) := by
        funext n
        rw [hlevel n]
        rfl
      rw [hfam]
      exact Work.KMTAreas.A7.variationalNorm_comp_mono_le (r := R)
        (u := fun m : ℕ => Work.KMTAreas.A7Hi.lpf ρ l C₀ (1 + m) g x)
        (φ := fun n : ℕ => N n - (C₀ + 1))
        (fun i j hij => Nat.sub_le_sub_right (hmonoN hij) (C₀ + 1))
    -- ## the assembly
    refine (MeasureTheory.eLpNorm_mono_enorm (hf := by pw_aesm) (p := (2 : ENNReal))
      (μ := MeasureTheory.Measure.count)
      (f := fun x : ℤ => PointwiseErgodicTheorems.variationalNorm R
        (fun n : ℕ => Work.KMTContract.kmtProj ρ l
            (-(Work.Analysis.EndVar.logN (Nat.floor (a n)))) g x))
      (g := fun x : ℤ => PointwiseErgodicTheorems.variationalNorm R
        (fun n : ℕ => Work.KMTAreas.A7Hi.lpf ρ l C₀ (1 + n) g x))
      (fun x => by simpa only [enorm_eq_self] using hpt x)).trans ?_
    refine hA.trans ?_
    refine mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal ?_) bot_le
    have hl : (0 : ℝ) ≤ (l : ℝ) := Nat.cast_nonneg l
    have h2 : (1 : ℝ) ≤ (1 + (l : ℝ)) ^ 2 := by nlinarith [sq_nonneg (l : ℝ), hl]
    have hle : CA ≤ CA * (1 + (l : ℝ)) ^ 2 := le_mul_of_one_le_right hCA_pos.le h2
    linarith

end
end Work.KMTPlan.A6
