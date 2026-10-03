import Mathlib
import Submission.Work.KMTAreas.A4.lip2GenDefs
import Submission.Work.KMTAreas.A4.arcMass_le_windowMass
import Submission.Work.KMTAreas.A4.lip2OmegaMass
import Submission.Work.KMTAreas.A4.iwSymbolSetNegEq
import Submission.Work.KMTAreas.A4.lip2Step1
import Submission.Work.KMTAreas.A4.levelSetMass
import Submission.Work.KMTAreas.A4.coverMassLe
import Submission.Work.KMTAreas.A4.exists_quarterArc_mass
import Submission.Work.KMTAreas.A4.kmtFhatInterval_eq_circleMass

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false

open scoped BigOperators
open MeasureTheory

namespace Work.KMTAreas.A4

open Work.Analysis.InverseTheory

/-- A polynomial of degree at least two has a nonzero leading coefficient. -/
theorem leadingCoeff_ne_zero_of_two_le_natDegree {P : Polynomial ℤ} (hP : 2 ≤ P.natDegree) :
    P.leadingCoeff ≠ 0 := by
  refine Polynomial.leadingCoeff_ne_zero.mpr (fun h => ?_)
  rw [h] at hP
  simp at hP

/-- Every `1 ≤ q ≤ 2^l` lies in the Ionescu--Wainger denominator set `P_{≤l}`. -/
theorem mem_iwP_of_le_two_pow {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) {l q : ℕ} (hq1 : 1 ≤ q)
    (hq2 : q ≤ 2 ^ l) : q ∈ Work.Analysis.IonescuWainger.iwP ρ l := by
  rw [Work.Analysis.IonescuWainger.mem_iwP]
  by_cases h : l ≤ Work.Analysis.IonescuWainger.iwC0 ρ
  · exact Or.inl ⟨h, hq1, hq2⟩
  · exact Or.inr ⟨not_le.mp h,
      Work.Analysis.IonescuWainger.iwPconcrete_contains_range hρ hρ1 (le_of_lt (not_le.mp h))
        hq1 hq2⟩

/-- The image in the frequency circle of `A / q` (with `A < q`) belongs to `(ℚ/ℤ)_{≤l}` as soon as
`q ≤ 2^l`. -/
theorem mem_iwArithFreqs_div {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) {l q A : ℕ} (hq1 : 1 ≤ q)
    (hA : A < q) (hq2 : q ≤ 2 ^ l) :
    (((A : ℝ) / (q : ℝ) : ℝ) : FreqCircle)
      ∈ Work.Analysis.IonescuWainger.iwArithFreqs ρ l := by
  show _ ∈ (Work.Analysis.IonescuWainger.iwP ρ l).biUnion (fun q : ℕ =>
    (Finset.range q).image (fun a : ℕ =>
      ((a : ℝ) / (q : ℝ) : Work.Analysis.IonescuWainger.Circle)))
  exact Finset.mem_biUnion.mpr ⟨q, mem_iwP_of_le_two_pow hρ hρ1 hq1 hq2,
    Finset.mem_image.mpr ⟨A, Finset.mem_range.mpr hA, rfl⟩⟩

/-- The image of an integer in the circle is zero. -/
theorem coe_int_eq_zero (m : ℤ) : ((m : ℝ) : FreqCircle) = 0 := by
  have h : ((m : ℝ) : FreqCircle) = m • ((1 : ℝ) : FreqCircle) := by
    rw [← AddCircle.coe_zsmul]
    congr 1
    rw [zsmul_eq_mul, mul_one]
  rw [h, AddCircle.coe_period, smul_zero]

/-- If `lcoef ≠ 0` then `(q * |lcoef|) · a / (q * lcoef) = ± a` is an integer. -/
theorem int_mul_div_int (lcoef : ℤ) (hlc : lcoef ≠ 0) (a : ℤ) (q : ℕ) (hq : 1 ≤ q) :
    ((q * lcoef.natAbs : ℕ) : ℝ) * ((a : ℝ) / ((q : ℝ) * (lcoef : ℝ)))
      = ((if 0 < lcoef then a else -a : ℤ) : ℝ) := by
  have hq0 : (q : ℝ) ≠ 0 := by positivity
  have hlcR : (lcoef : ℝ) ≠ 0 := by exact_mod_cast hlc
  have hLzR : ((lcoef.natAbs : ℕ) : ℝ) = |(lcoef : ℝ)| := by
    rw [Nat.cast_natAbs, Int.cast_abs]
  rcases lt_trichotomy lcoef 0 with hlt | heq | hgt
  · rw [if_neg (not_lt.mpr hlt.le)]
    push_cast
    rw [hLzR, abs_of_neg (by exact_mod_cast hlt)]
    field_simp
  · exact absurd heq hlc
  · rw [if_pos hgt]
    push_cast
    rw [hLzR, abs_of_pos (by exact_mod_cast hgt)]
    field_simp

/-- `a / (q * lcoef)` (as a point of the frequency circle) belongs to `(ℚ/ℤ)_{≤l}` whenever
`q * |lcoef| ≤ 2^l`. -/
theorem mem_iwArithFreqs_rat {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) {l : ℕ}
    {lcoef : ℤ} (hlc : lcoef ≠ 0) {q : ℕ} (hq : 1 ≤ q) {a : ℤ}
    (hQ : q * lcoef.natAbs ≤ 2 ^ l) :
    ((((a : ℝ) / ((q : ℝ) * (lcoef : ℝ)) : ℝ)) : FreqCircle)
      ∈ Work.Analysis.IonescuWainger.iwArithFreqs ρ l := by
  rw [Work.Analysis.IonescuWainger.mem_iwArithFreqs]
  refine ⟨q * lcoef.natAbs, mem_iwP_of_le_two_pow hρ hρ1 ?_ hQ, ?_⟩
  · exact Nat.one_le_iff_ne_zero.mpr (by positivity)
  · have hscal : (q * lcoef.natAbs : ℕ) •
        ((((a : ℝ) / ((q : ℝ) * (lcoef : ℝ)) : ℝ)) : FreqCircle)
        = (((((q * lcoef.natAbs : ℕ) : ℝ) *
            ((a : ℝ) / ((q : ℝ) * (lcoef : ℝ))) : ℝ)) : FreqCircle) := by
      rw [← AddCircle.coe_nsmul, nsmul_eq_mul]
    rw [hscal, int_mul_div_int lcoef hlc a q hq]
    split_ifs <;> exact coe_int_eq_zero _

/-- **The `ℓ²` bound for the Fourier transform of a `1`-bounded supported function.** -/
theorem kmtFhat_interval_mass_le {g : ℤ → ℂ} {N₀ : ℕ} (hg : Summable fun x : ℤ => ‖g x‖)
    (hsupp : SupportIn g N₀) (hbd : ∀ x : ℤ, ‖g x‖ ≤ 1) :
    ∫ t in (0 : ℝ)..1, ‖Work.A3.kmtFhat g t‖ ^ 2 ≤ 2 * (N₀ : ℝ) + 1 := by
  have hfin : ∃ s : Finset ℤ, ∀ x ∉ s, g x = 0 := FinSupp.of_supportIn hsupp
  have hpar := Work.A3.parseval_finsupp g hfin
  rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
    ← MeasureTheory.integral_Icc_eq_integral_Ioc, hpar]
  exact tsum_norm_sq_le_of_supportIn hsupp hbd

/-- Integrability of `‖𝓕_ℤ g‖²` against the Haar measure of the frequency circle. -/
theorem integrable_ZFourier_sq {g : ℤ → ℂ} (hg : Summable fun x : ℤ => ‖g x‖) :
    Integrable (fun ξ : FreqCircle => ‖ZFourier g ξ‖ ^ 2) AddCircle.haarAddCircle := by
  have haesm : AEStronglyMeasurable (fun ξ : FreqCircle => ZFourier g ξ) AddCircle.haarAddCircle := by
    refine MeasureTheory.AEStronglyMeasurable.tsum
      (f := fun x : ℤ => fun ξ : FreqCircle => g x * (fourier (-x) ξ : ℂ)) ?_
    intro x
    exact (continuous_const.mul ((fourier (-x) : C(FreqCircle, ℂ)).continuous)).aestronglyMeasurable
  have hbdd : ∀ ξ : FreqCircle, ‖ZFourier g ξ‖ ≤ ∑' x : ℤ, ‖g x‖ := by
    intro ξ
    have hsum : Summable fun x : ℤ => ‖g x * (fourier (-x) ξ : ℂ)‖ := by
      refine hg.congr fun x => ?_
      rw [norm_mul, norm_fourier_eq_one, mul_one]
    calc ‖ZFourier g ξ‖ = ‖∑' x : ℤ, g x * (fourier (-x) ξ : ℂ)‖ := rfl
      _ ≤ ∑' x : ℤ, ‖g x * (fourier (-x) ξ : ℂ)‖ := norm_tsum_le_tsum_norm hsum
      _ = ∑' x : ℤ, ‖g x‖ := tsum_congr fun x => by rw [norm_mul, norm_fourier_eq_one, mul_one]
  have h2 : AEStronglyMeasurable (fun ξ : FreqCircle => ‖ZFourier g ξ‖ ^ 2)
      AddCircle.haarAddCircle := haesm.norm.pow 2
  refine Integrable.of_bound h2 ((∑' x : ℤ, ‖g x‖) ^ 2)
    (Filter.Eventually.of_forall fun ξ => ?_)
  rw [Real.norm_of_nonneg (sq_nonneg _)]
  exact pow_le_pow_left₀ (norm_nonneg _) (hbdd ξ) 2

/-- **The circle geometry of the Weyl cover.**  If `|t * lc - a/q| ≤ r * |lc|` then the image of
`t` in the circle lies in the arc of radius `r` around the image of `a/(q * lc)`. -/
theorem mem_arcSet_div_leadingCoeff (P : Polynomial ℤ) {q : ℕ} {a : ℤ} {t r : ℝ} (hq : 1 ≤ q)
    (hlc : P.leadingCoeff ≠ 0)
    (h : |t * (P.leadingCoeff : ℝ) - (a : ℝ) / (q : ℝ)| ≤ r * |(P.leadingCoeff : ℝ)|) :
    ((t : ℝ) : FreqCircle)
      ∈ arcSet ((((a : ℝ) / ((q : ℝ) * (P.leadingCoeff : ℝ)) : ℝ)) : FreqCircle) r := by
  rw [mem_arcSet]
  have hlcabs : 0 < |(P.leadingCoeff : ℝ)| := abs_pos.mpr (by exact_mod_cast hlc)
  have hlcR : (P.leadingCoeff : ℝ) ≠ 0 := by exact_mod_cast hlc
  have hθ : |t - (a : ℝ) / ((q : ℝ) * (P.leadingCoeff : ℝ))| ≤ r := by
    have hkey : t - (a : ℝ) / ((q : ℝ) * (P.leadingCoeff : ℝ))
        = (t * (P.leadingCoeff : ℝ) - (a : ℝ) / (q : ℝ)) / (P.leadingCoeff : ℝ) := by
      rw [eq_div_iff hlcR]
      field_simp
    rw [hkey, abs_div, div_le_iff₀ hlcabs]
    exact h
  exact ⟨t - (a : ℝ) / ((q : ℝ) * (P.leadingCoeff : ℝ)), hθ, by
    rw [← AddCircle.coe_add]
    ring_nf⟩
theorem lip2GenArcMassA (P : Polynomial ℤ) (hP : 2 ≤ P.natDegree) : ∀ (A₀ : ℝ), 1 ≤ A₀ → ∀ (C_W K_W : ℝ), 0 < C_W → 0 < K_W → (∀ (M ε : ℝ) (γ : Work.Analysis.InverseTheory.FreqCircle) (ξ : ℝ) (s : ℤ) (a b : ℤ), 2 ≤ M → 0 < ε → ε ≤ 1 / 2 → ε ^ (-K_W) ≤ M → a ≤ b → ε ≤ ‖Work.KMTAreas.A4.winSumIcc M γ ξ P s a b‖ → ∃ (q : ℕ) (a' : ℤ), 1 ≤ q ∧ (q : ℝ) ≤ C_W * ε ^ (-K_W) ∧ |ξ * (P.leadingCoeff : ℝ) - (a' : ℝ) / (q : ℝ)| ≤ C_W * ε ^ (-K_W) / M ^ P.natDegree) → ∃ C K : ℝ, 0 < C ∧ 0 < K ∧ ∀ (ρ : ℝ), 0 < ρ → ρ ≤ 1 → ∀ {N N₀ : ℕ} {M : ℝ} {s : ℤ} {γ : Work.Analysis.InverseTheory.FreqCircle} {a b : ℤ} {g : ℤ → ℂ} {μ : ℝ}, 1 ≤ N → 1 ≤ N₀ → 2 ≤ M → a ≤ b → (N : ℝ) ^ P.natDegree / A₀ ≤ (N₀ : ℝ) → (N₀ : ℝ) ≤ A₀ * (N : ℝ) ^ P.natDegree → Work.Analysis.InverseTheory.SupportIn g N₀ → (∀ x : ℤ, ‖g x‖ ≤ 1) → Summable (fun x : ℤ => ‖g x‖) → 0 < μ → (8 * A₀) ^ K_W * (1 + (N₀ : ℝ) / μ) ^ K_W ≤ M → μ ≤ ∫ t in (0 : ℝ)..1, ‖Work.A3.kmtFhat g t‖ ^ 2 * ‖Work.KMTAreas.A4.winSumIcc M γ t P s a b‖ ^ 2 → ∃ (α : Work.Analysis.InverseTheory.FreqCircle) (r : ℝ) (l : ℕ) (k : ℤ), 0 < r ∧ r ≤ 1 / 4 ∧ 2 * r ≤ (2 : ℝ) ^ k ∧ α ∈ Work.Analysis.IonescuWainger.iwArithFreqs ρ l ∧ -α ∈ Work.Analysis.IonescuWainger.iwArithFreqs ρ l ∧ (2 : ℝ) ^ l ≤ C * (1 + (N₀ : ℝ) / μ) ^ K ∧ (2 : ℝ) ^ k ≤ C * (1 + (N₀ : ℝ) / μ) ^ K / M ^ P.natDegree ∧ μ / (C * (1 + (N₀ : ℝ) / μ) ^ K) ≤ ∫ ξ in Work.KMTAreas.A4.arcSet α r, ‖Work.Analysis.InverseTheory.ZFourier g ξ‖ ^ 2 ∂AddCircle.haarAddCircle := by
  intro A₀ hA₀ C_W K_W hCW hKW H
  obtain ⟨K0, hK0pos, hK0⟩ := winSumIcc_norm_bound
  have hlc0 : P.leadingCoeff ≠ 0 := leadingCoeff_ne_zero_of_two_le_natDegree hP
  set Lz : ℕ := P.leadingCoeff.natAbs with hLzdef
  have hLzpos : 0 < Lz := by rw [hLzdef]; exact Int.natAbs_pos.mpr hlc0
  set Lr : ℝ := (Lz : ℝ) with hLrdef
  have hLrpos : 0 < Lr := by rw [hLrdef]; exact_mod_cast hLzpos
  have hLr1 : 1 ≤ Lr := by rw [hLrdef]; exact_mod_cast hLzpos
  have hLrne : Lr ≠ 0 := ne_of_gt hLrpos
  have hLrabs : Lr = |(P.leadingCoeff : ℝ)| := by
    rw [hLrdef, hLzdef]
    rw [Nat.cast_natAbs, Int.cast_abs]
  set WB : ℝ := C_W * (3 : ℝ) ^ K_W + 1 with hWBdef
  have hWB1 : 1 ≤ WB := by
    rw [hWBdef]
    have : 0 < C_W * (3 : ℝ) ^ K_W := by positivity
    linarith
  set CC : ℝ := 2 + 2 * K0 ^ 2 + (2 * K0 ^ 2) * (4 * Lr + 2) * (WB + 1) ^ 2
    + 4 * C_W * ((3 : ℝ) ^ K_W) / Lr + 2 * WB * (Lr + 1) + 1 with hCCdef
  set KK : ℝ := 2 * K_W + 2 with hKKdef
  have hKKpos : 0 < KK := by rw [hKKdef]; linarith
  have hCCpos : 0 < CC := by
    rw [hCCdef]
    have h1 : (0 : ℝ) ≤ 2 * K0 ^ 2 := by positivity
    have h2 : (0 : ℝ) ≤ (2 * K0 ^ 2) * (4 * Lr + 2) * (WB + 1) ^ 2 := by positivity
    have h3 : (0 : ℝ) < 4 * C_W * ((3 : ℝ) ^ K_W) / Lr := by positivity
    have h4 : (0 : ℝ) ≤ 2 * WB * (Lr + 1) := by positivity
    linarith
  have hCC2K0 : 2 * K0 ^ 2 ≤ CC := by
    rw [hCCdef]
    have h2 : (0 : ℝ) ≤ (2 * K0 ^ 2) * (4 * Lr + 2) * (WB + 1) ^ 2 := by positivity
    have h3 : (0 : ℝ) < 4 * C_W * ((3 : ℝ) ^ K_W) / Lr := by positivity
    have h4 : (0 : ℝ) ≤ 2 * WB * (Lr + 1) := by positivity
    linarith
  have hCC2 : 2 ≤ CC := by
    rw [hCCdef]
    have h1 : (0 : ℝ) ≤ 2 * K0 ^ 2 := by positivity
    have h2 : (0 : ℝ) ≤ (2 * K0 ^ 2) * (4 * Lr + 2) * (WB + 1) ^ 2 := by positivity
    have h3 : (0 : ℝ) < 4 * C_W * ((3 : ℝ) ^ K_W) / Lr := by positivity
    have h4 : (0 : ℝ) ≤ 2 * WB * (Lr + 1) := by positivity
    linarith
  have hCC4 : 4 * C_W * ((3 : ℝ) ^ K_W) / Lr ≤ CC := by
    rw [hCCdef]
    have h1 : (0 : ℝ) ≤ 2 * K0 ^ 2 := by positivity
    have h2 : (0 : ℝ) ≤ (2 * K0 ^ 2) * (4 * Lr + 2) * (WB + 1) ^ 2 := by positivity
    have h4 : (0 : ℝ) ≤ 2 * WB * (Lr + 1) := by positivity
    linarith
  have hCCWB : 2 * WB * (Lr + 1) ≤ CC := by
    rw [hCCdef]
    have h1 : (0 : ℝ) ≤ 2 * K0 ^ 2 := by positivity
    have h2 : (0 : ℝ) ≤ (2 * K0 ^ 2) * (4 * Lr + 2) * (WB + 1) ^ 2 := by positivity
    have h3 : (0 : ℝ) < 4 * C_W * ((3 : ℝ) ^ K_W) / Lr := by positivity
    linarith
  have hCCM : (2 * K0 ^ 2) * (4 * Lr + 2) * (WB + 1) ^ 2 ≤ CC := by
    rw [hCCdef]
    have h1 : (0 : ℝ) ≤ 2 * K0 ^ 2 := by positivity
    have h3 : (0 : ℝ) < 4 * C_W * ((3 : ℝ) ^ K_W) / Lr := by positivity
    have h4 : (0 : ℝ) ≤ 2 * WB * (Lr + 1) := by positivity
    linarith
  have hCC2CW : 2 * C_W * ((3 : ℝ) ^ K_W) / Lr ≤ CC := by
    have hX : (0 : ℝ) ≤ C_W * ((3 : ℝ) ^ K_W) / Lr := by positivity
    have h5 : 2 * C_W * ((3 : ℝ) ^ K_W) / Lr ≤ 4 * C_W * ((3 : ℝ) ^ K_W) / Lr := by
      have he1 : 2 * C_W * ((3 : ℝ) ^ K_W) / Lr = 2 * (C_W * ((3 : ℝ) ^ K_W) / Lr) := by ring
      have he2 : 4 * C_W * ((3 : ℝ) ^ K_W) / Lr = 4 * (C_W * ((3 : ℝ) ^ K_W) / Lr) := by ring
      rw [he1, he2]
      linarith
    rw [hCCdef]
    have h1 : (0 : ℝ) ≤ 2 * K0 ^ 2 := by positivity
    have h2 : (0 : ℝ) ≤ (2 * K0 ^ 2) * (4 * Lr + 2) * (WB + 1) ^ 2 := by positivity
    have h4 : (0 : ℝ) ≤ 2 * WB * (Lr + 1) := by positivity
    linarith
  refine ⟨CC, KK, hCCpos, hKKpos, ?_⟩
  intro ρ hρ0 hρ1 N N₀ M s γ a b g μ hN hN₀ hM hab hN0lo hN0hi hsupp hgbd hgsum hμ0 hMY hμle
  set Y : ℝ := 1 + (N₀ : ℝ) / μ with hYdef
  have hY1 : 1 ≤ Y := by
    rw [hYdef]
    have : 0 ≤ (N₀ : ℝ) / μ := by positivity
    linarith
  have hYpos : 0 < Y := lt_of_lt_of_le one_pos hY1
  set Gf : ℝ := 2 * (N₀ : ℝ) + 1 with hGfdef
  have hGfpos : 0 < Gf := by rw [hGfdef]; positivity
  have hMY' : (8 * A₀) ^ K_W * Y ^ K_W ≤ M := by rw [hYdef]; exact hMY
  have hYkw1 : (1 : ℝ) ≤ Y ^ K_W := Real.one_le_rpow hY1 hKW.le
  have hYk1 : (1 : ℝ) ≤ Y ^ KK := Real.one_le_rpow hY1 (by rw [hKKdef]; linarith)
  have hYkk0 : (0 : ℝ) ≤ Y ^ KK := le_trans zero_le_one hYk1
  obtain ⟨hIntF, hIntFW, hIntCond⟩ := integrable_omega g hgsum γ P s a b (K := K0) (M := M)
    (fun t => hK0 M γ t P s a b hM)
  obtain ⟨ε, hε0, hεhalf, hεinv, hεsq, hmassE⟩ :=
    levelSetMass (fun t : ℝ => ‖Work.A3.kmtFhat g t‖ ^ 2)
      (fun t : ℝ => ‖winSumIcc M γ t P s a b‖) hK0pos hGfpos hμ0 hKW (fun t => sq_nonneg _)
      (fun t => norm_nonneg _) (fun t => hK0 M γ t P s a b hM) hIntF hIntFW
      (kmtFhat_interval_mass_le hgsum hsupp hgbd) hμle
  have hmax3 : max 2 (Real.sqrt (2 * Gf / μ)) ≤ 3 * Y := by
    apply max_le
    · linarith
    · have hN0R : (1 : ℝ) ≤ (N₀ : ℝ) := by exact_mod_cast hN₀
      have h1 : 2 * Gf ≤ 6 * (N₀ : ℝ) := by rw [hGfdef]; nlinarith
      have h2 : 6 * (N₀ : ℝ) ≤ 9 * Y ^ 2 * μ := by
        have hYsq : Y ^ 2 * μ = μ + 2 * (N₀ : ℝ) + (N₀ : ℝ) ^ 2 / μ := by
          rw [hYdef]
          field_simp
          ring
        have h3 : 9 * Y ^ 2 * μ = 9 * (μ + 2 * (N₀ : ℝ) + (N₀ : ℝ) ^ 2 / μ) := by
          rw [← hYsq]; ring
        have h4 : (0 : ℝ) ≤ 9 * ((N₀ : ℝ) ^ 2 / μ) := by positivity
        have h5 : (0 : ℝ) ≤ μ := hμ0.le
        rw [h3]
        nlinarith
      have h6 : 2 * Gf / μ ≤ 9 * Y ^ 2 := by
        rw [div_le_iff₀ hμ0]
        linarith
      calc Real.sqrt (2 * Gf / μ) ≤ Real.sqrt (9 * Y ^ 2) := Real.sqrt_le_sqrt h6
        _ = 3 * Y := by
            rw [show (9 : ℝ) * Y ^ 2 = (3 * Y) ^ 2 by ring, Real.sqrt_sq (by positivity)]
  have hε3Y : ε ^ (-K_W) ≤ (3 : ℝ) ^ K_W * Y ^ K_W := by
    have h2 : (max 2 (Real.sqrt (2 * Gf / μ))) ^ K_W ≤ (3 : ℝ) ^ K_W * Y ^ K_W := by
      have h := Real.rpow_le_rpow
        (le_trans (by norm_num : (0 : ℝ) ≤ 2) (le_max_left 2 (Real.sqrt (2 * Gf / μ))))
        hmax3 hKW.le
      rwa [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 3) hYpos.le] at h
    exact hεinv.trans h2
  have hεM : ε ^ (-K_W) ≤ M := by
    calc ε ^ (-K_W) ≤ (3 : ℝ) ^ K_W * Y ^ K_W := hε3Y
      _ ≤ (8 : ℝ) ^ K_W * Y ^ K_W := by
          have h := Real.rpow_le_rpow (by norm_num : (0 : ℝ) ≤ 3) (by norm_num : (3 : ℝ) ≤ 8)
            hKW.le
          nlinarith [Real.rpow_nonneg hYpos.le K_W]
      _ ≤ (8 * A₀) ^ K_W * Y ^ K_W := by
          have h := Real.rpow_le_rpow (by norm_num : (0 : ℝ) ≤ 8)
            (by nlinarith [hA₀] : (8 : ℝ) ≤ 8 * A₀) hKW.le
          nlinarith [Real.rpow_nonneg hYpos.le K_W]
      _ ≤ M := hMY'
  set Nq : ℕ := ⌈C_W * ε ^ (-K_W)⌉₊ with hNqdef
  have hNqarg : 0 < C_W * ε ^ (-K_W) := by
    have := Real.rpow_pos_of_pos hε0 (-K_W)
    positivity
  have hNq1 : 1 ≤ Nq := by
    rw [hNqdef, Nat.one_le_iff_ne_zero, ← Nat.pos_iff_ne_zero, Nat.ceil_pos]
    exact hNqarg
  have hNqle : (Nq : ℝ) ≤ WB * Y ^ K_W := by
    have h1 : (Nq : ℝ) < C_W * ε ^ (-K_W) + 1 := by
      rw [hNqdef]
      exact Nat.ceil_lt_add_one hNqarg.le
    have h2 : C_W * ε ^ (-K_W) ≤ C_W * ((3 : ℝ) ^ K_W * Y ^ K_W) :=
      mul_le_mul_of_nonneg_left hε3Y hCW.le
    have h3 : C_W * ((3 : ℝ) ^ K_W * Y ^ K_W) + 1 ≤ WB * Y ^ K_W := by
      rw [hWBdef]
      nlinarith [mul_nonneg hCW.le (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 3) K_W), hYkw1]
    linarith
  have hNq1R : (Nq : ℝ) + 1 ≤ (WB + 1) * Y ^ K_W := by
    have h : (Nq : ℝ) ≤ WB * Y ^ K_W := hNqle
    nlinarith [hYkw1, hWB1]
  set δ : ℝ := C_W * ε ^ (-K_W) / M ^ P.natDegree with hδdef
  set rc : ℝ := δ / Lr with hrcdef
  have hrcpos : 0 < rc := by
    rw [hrcdef, hδdef]
    have := Real.rpow_pos_of_pos hε0 (-K_W)
    positivity
  have h4CW : 4 * C_W * ε ^ (-K_W) / Lr ≤ CC * Y ^ KK := by
    have h1 : 4 * C_W * ε ^ (-K_W) / Lr ≤ (4 * C_W * ((3 : ℝ) ^ K_W) / Lr) * Y ^ K_W := by
      have h := mul_le_mul_of_nonneg_left hε3Y (by positivity : (0 : ℝ) ≤ 4 * C_W / Lr)
      calc 4 * C_W * ε ^ (-K_W) / Lr = (4 * C_W / Lr) * ε ^ (-K_W) := by ring
        _ ≤ (4 * C_W / Lr) * ((3 : ℝ) ^ K_W * Y ^ K_W) := h
        _ = (4 * C_W * ((3 : ℝ) ^ K_W) / Lr) * Y ^ K_W := by ring
    have h3 : Y ^ K_W ≤ Y ^ KK :=
      Real.rpow_le_rpow_of_exponent_le hY1 (by rw [hKKdef]; linarith)
    have h2 : (4 * C_W * ((3 : ℝ) ^ K_W) / Lr) * Y ^ K_W ≤ CC * Y ^ KK := by
      calc (4 * C_W * ((3 : ℝ) ^ K_W) / Lr) * Y ^ K_W ≤ CC * Y ^ K_W :=
            mul_le_mul_of_nonneg_right hCC4 (Real.rpow_nonneg hYpos.le K_W)
        _ ≤ CC * Y ^ KK := mul_le_mul_of_nonneg_left h3 hCCpos.le
    linarith
  by_cases hcase : rc ≤ 1 / 4
  · -- ================== Case 2 : the cover by the Weyl candidates ==================
    set pf : Finset (ℕ × ℤ) := (Finset.Icc 1 Nq).product
      (Finset.Icc (-(2 * (Lz : ℤ) * (Nq : ℤ))) (2 * (Lz : ℤ) * (Nq : ℤ))) with hpfdef
    have hpfne : pf.Nonempty := ⟨(1, 0), by
      refine Finset.mem_product.mpr ⟨Finset.mem_Icc.mpr ⟨le_rfl, hNq1⟩, ?_⟩
      refine Finset.mem_Icc.mpr ⟨?_, ?_⟩
      · have h0 : (0 : ℤ) ≤ 2 * (Lz : ℤ) * (Nq : ℤ) := by positivity
        omega
      · positivity⟩
    have hcover : ∀ t ∈ Set.Ioc (0 : ℝ) 1,
        t ∈ {t : ℝ | ε ≤ ‖winSumIcc M γ t P s a b‖} →
        ∃ p ∈ pf, ((t : ℝ) : FreqCircle) ∈
          arcSet ((((p.2 : ℝ) / ((p.1 : ℝ) * (P.leadingCoeff : ℝ)) : ℝ)) : FreqCircle) rc := by
      intro t ht hle
      obtain ⟨q, a', hq1, hqle, happ⟩ := H M ε γ t s a b hM hε0 hεhalf hεM hab hle
      have hqNq : q ≤ Nq := by
        have h1 : (q : ℝ) ≤ (Nq : ℝ) :=
          le_trans hqle (by rw [hNqdef]; exact Nat.le_ceil _)
        exact_mod_cast h1
      have ht0 : 0 < t := ht.1
      have ht1 : t ≤ 1 := ht.2
      have hrcL : rc * Lr = δ := by rw [hrcdef]; field_simp
      have hδb : |t * (P.leadingCoeff : ℝ) - (a' : ℝ) / (q : ℝ)| ≤ rc * Lr := by
        rw [hrcL, hδdef]
        exact happ
      have hrcL' : rc * Lr ≤ Lr / 4 := by
        have h := mul_le_mul_of_nonneg_right hcase hLrpos.le
        linarith
      have htlc : |t * (P.leadingCoeff : ℝ)| ≤ Lr := by
        have h1 : |t| ≤ 1 := by rw [abs_of_pos ht0]; exact ht1
        calc |t * (P.leadingCoeff : ℝ)| = |t| * |(P.leadingCoeff : ℝ)| := abs_mul _ _
          _ ≤ 1 * Lr := by
              rw [hLrabs]
              exact mul_le_mul h1 le_rfl (abs_nonneg _) (by norm_num)
          _ = Lr := one_mul _
      have ha'q : |(a' : ℝ)| / (q : ℝ) ≤ 2 * Lr := by
        have hq0 : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq1
        have h1 : |(a' : ℝ) / (q : ℝ)| ≤ 2 * Lr := by
          calc |(a' : ℝ) / (q : ℝ)|
              = |((a' : ℝ) / (q : ℝ) - t * (P.leadingCoeff : ℝ)) + t * (P.leadingCoeff : ℝ)| := by
                ring_nf
            _ ≤ |(a' : ℝ) / (q : ℝ) - t * (P.leadingCoeff : ℝ)| + |t * (P.leadingCoeff : ℝ)| :=
                abs_add_le _ _
            _ ≤ Lr / 4 + Lr := add_le_add (by rw [abs_sub_comm]; exact hδb.trans hrcL') htlc
            _ ≤ 2 * Lr := by linarith
        rw [abs_div, abs_of_pos hq0] at h1
        linarith
      have ha'bound : |a'| ≤ 2 * (Lz : ℤ) * (Nq : ℤ) := by
        have hqNqR : (q : ℝ) ≤ (Nq : ℝ) := by exact_mod_cast hqNq
        have hq0 : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq1
        have h1 : |(a' : ℝ)| ≤ 2 * Lr * (q : ℝ) := by
          rw [div_le_iff₀ hq0] at ha'q
          linarith
        have h2 : |(a' : ℝ)| ≤ ((2 * (Lz : ℤ) * (Nq : ℤ) : ℤ) : ℝ) := by
          calc |(a' : ℝ)| ≤ 2 * Lr * (q : ℝ) := h1
            _ ≤ 2 * Lr * (Nq : ℝ) := by nlinarith [hLrpos]
            _ = ((2 * (Lz : ℤ) * (Nq : ℤ) : ℤ) : ℝ) := by push_cast [hLrdef]; ring
        rw [← Int.cast_abs] at h2
        exact_mod_cast h2
      refine ⟨(q, a'), ?_, ?_⟩
      · refine Finset.mem_product.mpr ⟨Finset.mem_Icc.mpr ⟨hq1, hqNq⟩, ?_⟩
        exact Finset.mem_Icc.mpr (abs_le.mp ha'bound)
      · have hδb' : |t * (P.leadingCoeff : ℝ) - (a' : ℝ) / (q : ℝ)|
            ≤ rc * |(P.leadingCoeff : ℝ)| := by
          rw [← hLrabs]
          exact hδb
        exact mem_arcSet_div_leadingCoeff P hq1 hlc0 hδb'
    obtain ⟨p, hpmem, hmassp⟩ := coverMassLe (f := fun t : ℝ => ‖Work.A3.kmtFhat g t‖ ^ 2)
      (B := μ / (2 * K0 ^ 2)) pf hpfne (fun p _ => measurableSet_arcSet _ _) (fun t => sq_nonneg _)
      hIntF
      (by
        refine (hIntCond ε).congr (Filter.Eventually.of_forall fun t => ?_)
        simp only [Set.indicator_apply, Set.mem_ofPred_eq])
      (by positivity) hcover
      (by
        have heq : (fun t : ℝ => if ε ≤ ‖winSumIcc M γ t P s a b‖
              then ‖Work.A3.kmtFhat g t‖ ^ 2 else 0)
            = (Set.indicator {t : ℝ | ε ≤ ‖winSumIcc M γ t P s a b‖}
                (fun t : ℝ => ‖Work.A3.kmtFhat g t‖ ^ 2)) := by
          funext t
          rw [Set.indicator_apply]
          simp
        rw [← heq]
        exact hmassE)
    have hpmem' : p ∈ (Finset.Icc 1 Nq).product
        (Finset.Icc (-(2 * (Lz : ℤ) * (Nq : ℤ))) (2 * (Lz : ℤ) * (Nq : ℤ))) := by
      rwa [hpfdef] at hpmem
    have hp1 : 1 ≤ p.1 := (Finset.mem_Icc.mp (Finset.mem_product.mp hpmem').1).1
    have hp1le : p.1 ≤ Nq := (Finset.mem_Icc.mp (Finset.mem_product.mp hpmem').1).2
    have hpcardle : (pf.card : ℝ) ≤ (Nq : ℝ) * (4 * Lr * (Nq : ℝ) + 1) := by
      have hcardprod : pf.card = (Finset.Icc 1 Nq).card *
          (Finset.Icc (-(2 * (Lz : ℤ) * (Nq : ℤ))) (2 * (Lz : ℤ) * (Nq : ℤ))).card := by
        rw [hpfdef]
        exact Finset.card_product _ _
      have h1 : ((Finset.Icc (-(2 * (Lz : ℤ) * (Nq : ℤ))) (2 * (Lz : ℤ) * (Nq : ℤ))).card : ℝ)
          ≤ 4 * Lr * (Nq : ℝ) + 1 := by
        rw [Int.card_Icc]
        have hmeq : 2 * (Lz : ℤ) * (Nq : ℤ) + 1 - -(2 * (Lz : ℤ) * (Nq : ℤ))
            = 4 * (Lz : ℤ) * (Nq : ℤ) + 1 := by ring
        rw [hmeq]
        have hcast : (((4 * (Lz : ℤ) * (Nq : ℤ) + 1).toNat : ℕ) : ℝ)
            ≤ ((4 * (Lz : ℤ) * (Nq : ℤ) + 1 : ℤ) : ℝ) := by
          have h : ((4 * (Lz : ℤ) * (Nq : ℤ) + 1).toNat : ℤ) = 4 * (Lz : ℤ) * (Nq : ℤ) + 1 :=
            Int.toNat_of_nonneg (by positivity)
          exact_mod_cast (le_of_eq h)
        calc (((4 * (Lz : ℤ) * (Nq : ℤ) + 1).toNat : ℕ) : ℝ)
            ≤ ((4 * (Lz : ℤ) * (Nq : ℤ) + 1 : ℤ) : ℝ) := hcast
          _ = 4 * Lr * (Nq : ℝ) + 1 := by push_cast [← hLrdef]; ring
      have h2 : ((Finset.Icc 1 Nq).card : ℝ) ≤ (Nq : ℝ) := by
        rw [Nat.card_Icc]
        push_cast
        linarith
      rw [hcardprod]
      push_cast
      exact mul_le_mul h2 h1 (by positivity) (by positivity)
    have hmassS : μ / (2 * K0 ^ 2) / (pf.card : ℝ) ≤
        ∫ ξ in arcSet ((((p.2 : ℝ) / ((p.1 : ℝ) * (P.leadingCoeff : ℝ)) : ℝ)) : FreqCircle) rc,
          ‖ZFourier g ξ‖ ^ 2 ∂AddCircle.haarAddCircle := by
      rw [kmtFhatInterval_eq_circleMass g hgsum (measurableSet_arcSet _ _)]
      exact hmassp
    have hcard : (2 * K0 ^ 2) * (pf.card : ℝ) ≤ CC * Y ^ KK := by
      have h1 : (pf.card : ℝ) ≤ (4 * Lr + 2) * (WB + 1) ^ 2 * Y ^ (2 * K_W) := by
        have h2 : (Nq : ℝ) * (4 * Lr * (Nq : ℝ) + 1) ≤ (4 * Lr + 2) * ((Nq : ℝ) + 1) ^ 2 := by
          have hNqnn : (0 : ℝ) ≤ (Nq : ℝ) := Nat.cast_nonneg _
          nlinarith [hLrpos, hNqnn]
        have h3 : ((Nq : ℝ) + 1) ^ 2 ≤ ((WB + 1) * Y ^ K_W) ^ 2 :=
          pow_le_pow_left₀ (by positivity) hNq1R 2
        have h4 : ((WB + 1) * Y ^ K_W) ^ 2 = (WB + 1) ^ 2 * Y ^ (2 * K_W) := by
          rw [mul_pow]
          have h5 : (Y ^ K_W) ^ 2 = Y ^ (2 * K_W) := by
            have hexp : K_W * ((2 : ℕ) : ℝ) = 2 * K_W := by push_cast; ring
            rw [← Real.rpow_natCast, ← Real.rpow_mul hYpos.le, hexp]
          rw [h5]
        calc (pf.card : ℝ) ≤ (Nq : ℝ) * (4 * Lr * (Nq : ℝ) + 1) := hpcardle
          _ ≤ (4 * Lr + 2) * ((Nq : ℝ) + 1) ^ 2 := h2
          _ ≤ (4 * Lr + 2) * ((WB + 1) ^ 2 * Y ^ (2 * K_W)) := by
              have hm := mul_le_mul_of_nonneg_left h3 (by positivity : (0 : ℝ) ≤ 4 * Lr + 2)
              rwa [h4] at hm
          _ = (4 * Lr + 2) * (WB + 1) ^ 2 * Y ^ (2 * K_W) := by ring
      have h5 : Y ^ (2 * K_W) ≤ Y ^ KK :=
        Real.rpow_le_rpow_of_exponent_le hY1 (by rw [hKKdef]; linarith)
      have h6 : (4 * Lr + 2) * (WB + 1) ^ 2 * Y ^ (2 * K_W)
          ≤ (4 * Lr + 2) * (WB + 1) ^ 2 * Y ^ KK :=
        mul_le_mul_of_nonneg_left h5 (by positivity)
      have h7 : (2 * K0 ^ 2) * ((4 * Lr + 2) * (WB + 1) ^ 2 * Y ^ KK) ≤ CC * Y ^ KK := by
        have h8 : (2 * K0 ^ 2) * ((4 * Lr + 2) * (WB + 1) ^ 2 * Y ^ KK)
            = ((2 * K0 ^ 2) * (4 * Lr + 2) * (WB + 1) ^ 2) * Y ^ KK := by ring
        rw [h8]
        exact mul_le_mul_of_nonneg_right hCCM hYkk0
      calc (2 * K0 ^ 2) * (pf.card : ℝ)
          ≤ (2 * K0 ^ 2) * ((4 * Lr + 2) * (WB + 1) ^ 2 * Y ^ KK) :=
            mul_le_mul_of_nonneg_left (h1.trans h6) (by positivity)
        _ ≤ CC * Y ^ KK := h7
    have hmassFinal : μ / (CC * Y ^ KK) ≤
        ∫ ξ in arcSet ((((p.2 : ℝ) / ((p.1 : ℝ) * (P.leadingCoeff : ℝ)) : ℝ)) : FreqCircle) rc,
          ‖ZFourier g ξ‖ ^ 2 ∂AddCircle.haarAddCircle := by
      have hpos : (0 : ℝ) < (2 * K0 ^ 2) * (pf.card : ℝ) := by positivity
      have hstep : μ / (CC * Y ^ KK) ≤ μ / ((2 * K0 ^ 2) * (pf.card : ℝ)) :=
        div_le_div_of_nonneg_left hμ0.le hpos hcard
      refine hstep.trans ?_
      rw [← div_div]
      exact hmassS
    obtain ⟨k, hk1, hk2⟩ := lipExistsZpowTwo (show (0 : ℝ) < 2 * rc by linarith)
    have hMne : M ^ P.natDegree ≠ 0 := pow_ne_zero _ (by linarith : M ≠ 0)
    have hk_le : (2 : ℝ) ^ k ≤ CC * Y ^ KK / M ^ P.natDegree := by
      rw [le_div_iff₀ (by positivity : (0 : ℝ) < M ^ P.natDegree)]
      calc (2 : ℝ) ^ k * M ^ P.natDegree ≤ (2 * (2 * rc)) * M ^ P.natDegree :=
            mul_le_mul_of_nonneg_right hk2 (by positivity)
        _ = 4 * C_W * ε ^ (-K_W) / Lr := by
            rw [hrcdef, hδdef]
            field_simp
            ring
        _ ≤ CC * Y ^ KK := h4CW
    have hqLpos : 0 < ((p.1 * Lz : ℕ) : ℝ) := by
      have h1 : 0 < p.1 * Lz := Nat.mul_pos (by omega) hLzpos
      exact_mod_cast h1
    obtain ⟨l, hl1, hl2⟩ := lipExistsPowTwoGe hqLpos
    have hQl : p.1 * Lz ≤ 2 ^ l := by
      have h2 : ((p.1 * Lz : ℕ) : ℝ) ≤ (2 : ℝ) ^ l := hl1
      exact_mod_cast h2
    have hmemα : ((((p.2 : ℝ) / ((p.1 : ℝ) * (P.leadingCoeff : ℝ)) : ℝ)) : FreqCircle)
        ∈ Work.Analysis.IonescuWainger.iwArithFreqs ρ l :=
      mem_iwArithFreqs_rat hρ0 hρ1 hlc0 hp1 hQl
    have hlbound : (2 : ℝ) ^ l ≤ CC * Y ^ KK := by
      have h1 : (2 : ℝ) ^ l ≤ 2 * ((Nq : ℝ) * Lr) := by
        refine hl2.trans ?_
        have hmax : max ((p.1 * Lz : ℕ) : ℝ) 1 ≤ (Nq : ℝ) * Lr := by
          apply max_le
          · push_cast [hLrdef]
            have hp1R : (p.1 : ℝ) ≤ (Nq : ℝ) := by exact_mod_cast hp1le
            nlinarith [hLrpos]
          · have hNqLz : (1 : ℝ) ≤ (Nq : ℝ) * Lr := by
              have h1 : (1 : ℝ) ≤ (Nq : ℝ) := by exact_mod_cast hNq1
              nlinarith [hLr1]
            linarith
        linarith
      have h2 : 2 * ((Nq : ℝ) * Lr) ≤ 2 * ((WB * Y ^ K_W) * Lr) := by
        have hm := mul_le_mul_of_nonneg_right hNqle hLrpos.le
        linarith
      have h3 : 2 * ((WB * Y ^ K_W) * Lr) ≤ CC * Y ^ KK := by
        have h4 : 2 * ((WB * Y ^ K_W) * Lr) = (2 * WB * Lr) * Y ^ K_W := by ring
        have h5 : 2 * WB * Lr ≤ 2 * WB * (Lr + 1) := by nlinarith [hWB1]
        have h6 : (2 * WB * Lr) * Y ^ K_W ≤ CC * Y ^ KK := by
          calc (2 * WB * Lr) * Y ^ K_W ≤ (2 * WB * (Lr + 1)) * Y ^ K_W :=
                mul_le_mul_of_nonneg_right h5 (Real.rpow_nonneg hYpos.le K_W)
            _ ≤ CC * Y ^ K_W :=
                mul_le_mul_of_nonneg_right hCCWB (Real.rpow_nonneg hYpos.le K_W)
            _ ≤ CC * Y ^ KK := by
                have h7 : Y ^ K_W ≤ Y ^ KK :=
                  Real.rpow_le_rpow_of_exponent_le hY1 (by rw [hKKdef]; linarith)
                exact mul_le_mul_of_nonneg_left h7 hCCpos.le
        rwa [← h4] at h6
      linarith
    exact ⟨((((p.2 : ℝ) / ((p.1 : ℝ) * (P.leadingCoeff : ℝ)) : ℝ)) : FreqCircle), rc, l, k,
      hrcpos, hcase, hk1, hmemα, neg_mem_iwArithFreqs hmemα, hlbound, hk_le, hmassFinal⟩
  · -- ================== Case 1 : the two quarter arcs cover the circle ==================
    have hbig : 1 / 4 < rc := not_le.mp hcase
    have hMd : M ^ P.natDegree ≤ 4 * C_W * ε ^ (-K_W) / Lr := by
      have hrcval : rc = C_W * ε ^ (-K_W) / (Lr * M ^ P.natDegree) := by
        rw [hrcdef, hδdef]; ring
      rw [hrcval] at hbig
      have hpos : (0 : ℝ) < Lr * M ^ P.natDegree := by positivity
      have h1 : (1 / 4 : ℝ) * (Lr * M ^ P.natDegree) < C_W * ε ^ (-K_W) :=
        (lt_div_iff₀ hpos).mp hbig
      have h2 : M ^ P.natDegree * Lr < 4 * C_W * ε ^ (-K_W) := by linarith
      rw [le_div_iff₀ hLrpos]
      linarith
    have hcirc : (∫ ξ, ‖ZFourier g ξ‖ ^ 2 ∂AddCircle.haarAddCircle)
        = ∫ t in (0 : ℝ)..1, ‖Work.A3.kmtFhat g t‖ ^ 2 := by
      have h := kmtFhatInterval_eq_circleMass g hgsum (S := Set.univ) MeasurableSet.univ
      rw [MeasureTheory.setIntegral_univ] at h
      rw [h]
      have hset : {t : ℝ | ((t : ℝ) : FreqCircle) ∈ (Set.univ : Set FreqCircle)} = Set.univ := by
        ext t
        simp
      rw [hset]
      refine intervalIntegral.integral_congr fun t _ => ?_
      rw [Set.indicator_of_mem (Set.mem_univ t)]
    have hFmass : μ / K0 ^ 2 ≤ ∫ t in (0 : ℝ)..1, ‖Work.A3.kmtFhat g t‖ ^ 2 := by
      have h1 : ∫ t in (0 : ℝ)..1, ‖Work.A3.kmtFhat g t‖ ^ 2 * ‖winSumIcc M γ t P s a b‖ ^ 2
          ≤ K0 ^ 2 * ∫ t in (0 : ℝ)..1, ‖Work.A3.kmtFhat g t‖ ^ 2 := by
        rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
          intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
          ← MeasureTheory.integral_const_mul]
        refine MeasureTheory.integral_mono_of_nonneg (Filter.Eventually.of_forall fun t => ?_)
          (hIntF.const_mul (K0 ^ 2)) (Filter.Eventually.of_forall fun t => ?_)
        · positivity
        · have h2 : ‖winSumIcc M γ t P s a b‖ ^ 2 ≤ K0 ^ 2 :=
            pow_le_pow_left₀ (norm_nonneg _) (hK0 M γ t P s a b hM) 2
          nlinarith [sq_nonneg (‖Work.A3.kmtFhat g t‖)]
      rw [div_le_iff₀ (by positivity : (0 : ℝ) < K0 ^ 2)]
      linarith
    obtain ⟨α, hα0, hmassArc⟩ := exists_quarterArc_mass (φ := fun ξ : FreqCircle => ‖ZFourier g ξ‖ ^ 2)
      (fun ξ => sq_nonneg _) (integrable_ZFourier_sq hgsum)
    have hmassq : μ / (2 * K0 ^ 2) ≤
        ∫ ξ in arcSet α (1 / 4), ‖ZFourier g ξ‖ ^ 2 ∂AddCircle.haarAddCircle := by
      have h1 : μ / (2 * K0 ^ 2) ≤ (∫ ξ, ‖ZFourier g ξ‖ ^ 2 ∂AddCircle.haarAddCircle) / 2 := by
        rw [hcirc]
        have h2 : μ / (2 * K0 ^ 2) = (μ / K0 ^ 2) / 2 := by
          rw [div_div]
          congr 1
          ring
        rw [h2]
        exact div_le_div_of_nonneg_right hFmass (by norm_num)
      exact h1.trans hmassArc
    have hmem0 : (0 : FreqCircle) ∈ Work.Analysis.IonescuWainger.iwArithFreqs ρ 1 := by
      have h := mem_iwArithFreqs_div (ρ := ρ) hρ0 hρ1 (l := 1) (q := 1) (A := 0) le_rfl
        (by norm_num) (by norm_num)
      simpa using h
    have hmemhalf : ((((1 : ℝ) / 2 : ℝ)) : FreqCircle)
        ∈ Work.Analysis.IonescuWainger.iwArithFreqs ρ 1 := by
      have h := mem_iwArithFreqs_div (ρ := ρ) hρ0 hρ1 (l := 1) (q := 2) (A := 1) (by norm_num)
        (by norm_num) (by norm_num)
      simpa using h
    have hmemα : α ∈ Work.Analysis.IonescuWainger.iwArithFreqs ρ 1 :=
      hα0.elim (fun h => by rw [h]; exact hmem0) (fun h => by rw [h]; exact hmemhalf)
    have hCC2K0' : 2 * K0 ^ 2 ≤ CC * Y ^ KK := by
      calc 2 * K0 ^ 2 ≤ (2 * K0 ^ 2) * Y ^ KK :=
            le_mul_of_one_le_right (by positivity) hYk1
        _ ≤ CC * Y ^ KK := mul_le_mul_of_nonneg_right hCC2K0 hYkk0
    have hCC2' : (2 : ℝ) ≤ CC * Y ^ KK := by
      calc (2 : ℝ) ≤ 2 * Y ^ KK := le_mul_of_one_le_right (by norm_num) hYk1
        _ ≤ CC * Y ^ KK := mul_le_mul_of_nonneg_right hCC2 hYkk0
    have hCChalf : (1 / 2 : ℝ) ≤ CC * Y ^ KK / M ^ P.natDegree := by
      rw [le_div_iff₀ (by positivity : (0 : ℝ) < M ^ P.natDegree)]
      have h1 : (1 / 2 : ℝ) * M ^ P.natDegree ≤ 2 * C_W * ε ^ (-K_W) / Lr := by
        have h := mul_le_mul_of_nonneg_left hMd (by norm_num : (0 : ℝ) ≤ 1 / 2)
        have heq : (1 / 2 : ℝ) * (4 * C_W * ε ^ (-K_W) / Lr) = 2 * C_W * ε ^ (-K_W) / Lr := by
          ring
        rw [heq] at h
        exact h
      have h2 : 2 * C_W * ε ^ (-K_W) / Lr ≤ (2 * C_W * ((3 : ℝ) ^ K_W) / Lr) * Y ^ K_W := by
        have h := mul_le_mul_of_nonneg_left hε3Y (by positivity : (0 : ℝ) ≤ 2 * C_W / Lr)
        calc 2 * C_W * ε ^ (-K_W) / Lr = (2 * C_W / Lr) * ε ^ (-K_W) := by ring
          _ ≤ (2 * C_W / Lr) * ((3 : ℝ) ^ K_W * Y ^ K_W) := h
          _ = (2 * C_W * ((3 : ℝ) ^ K_W) / Lr) * Y ^ K_W := by ring
      have h3 : (2 * C_W * ((3 : ℝ) ^ K_W) / Lr) * Y ^ K_W ≤ CC * Y ^ KK := by
        have h6 : Y ^ K_W ≤ Y ^ KK :=
          Real.rpow_le_rpow_of_exponent_le hY1 (by rw [hKKdef]; linarith)
        calc (2 * C_W * ((3 : ℝ) ^ K_W) / Lr) * Y ^ K_W ≤ CC * Y ^ K_W :=
              mul_le_mul_of_nonneg_right hCC2CW (Real.rpow_nonneg hYpos.le K_W)
          _ ≤ CC * Y ^ KK := mul_le_mul_of_nonneg_left h6 hCCpos.le
      linarith
    refine ⟨α, 1 / 4, 1, -1, by norm_num, le_rfl, ?_, hmemα, neg_mem_iwArithFreqs hmemα, ?_, ?_, ?_⟩
    · have h : (2 : ℝ) ^ (-1 : ℤ) = 1 / 2 := by norm_num
      rw [h]; norm_num
    · rw [pow_one]
      exact hCC2'
    · have h : (2 : ℝ) ^ (-1 : ℤ) = 1 / 2 := by norm_num
      rw [h]
      exact hCChalf
    · exact (div_le_div_of_nonneg_left hμ0.le (by positivity : (0 : ℝ) < 2 * K0 ^ 2) hCC2K0').trans
        hmassq

end Work.KMTAreas.A4
