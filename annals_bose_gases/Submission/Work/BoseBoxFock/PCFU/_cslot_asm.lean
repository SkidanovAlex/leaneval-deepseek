import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseBoxFock.PCFU._cslot_arith
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-! Scratch: the assembly of `chCslot_le` from the two pieces (hypotheses `hA`, `hB` here). -/

noncomputable section
open MeasureTheory
open scoped BigOperators

namespace Work.BoseBoxFock.PCFU

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "ellH" => Work.BoseBoxFock.ellH

theorem chCslot_le_of_children (v : E3 → ℝ) (h : Work.UBB.ScatSol v) (hv : 0 ≤ v)
    (hv1 : MeasureTheory.MemLp v 1) (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : E3) R) (hav : 0 < _root_.BoseGases.a v)
    (fc fu : Work.BoseBoxFix.LowCut) (J ε₀ : ℝ)
    (hA : ∃ C : ℝ, 0 ≤ C ∧ ∀ {μ : ℝ}, 0 < μ → ∀ {N n : ℕ} {i j : Fin n}, i ≠ j →
      ∀ (Φ : Work.BoseKinLoc.BoxState n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))) (P : ℝ),
        ChKerPair v h μ fu N P →
        ‖chCslot v h fc fu μ N i j
            (Work.BoseBoxFock.boxRestrictR (ellH v μ) (Φ : Submission.BoseGases.X n → ℝ))‖
          ≤ C * (P * (1 + ellH v μ ^ 3)) * Work.BoseBoxFix.normB v μ n Φ)
    (hB : ∃ C : ℝ, 0 ≤ C ∧ ∀ {μ : ℝ}, 0 < μ →
      R ≤ ellH v μ * Submission.BoseGases.chiR0 → 2 * R ≤ ellH v μ →
      ∀ η : ℝ, 0 < η → ∃ T : ℕ, ∀ {N : ℕ}, T ≤ N →
        ChKerPair v h μ fu N
          (η * ellH v μ ^ 3 + C * ellH v μ ^ 3 * (R / ellH v μ) ^ 12)) :
    Work.BoseBoxFock.SlotPiece v h fc fu R J ε₀
      (fun n μ N i j Θ => chCslot v h fc fu μ N i j Θ) := by
  obtain ⟨C_A, hCA0, hA⟩ := hA
  obtain ⟨C_B, hCB0, hB⟩ := hB
  set Kc : ℝ := 64 * (max C_A 1) * (max C_B 1) * R ^ 12 *
      (max ε₀ 1 / ((_root_.BoseGases.a v) ^ 4 * (2 * R) ^ 3)
        + max ε₀ 1 / ((_root_.BoseGases.a v) ^ 4 * (2 * R) ^ 9)) + 1 with hKc
  have hKcpos : 0 < Kc := by
    rw [hKc]; positivity
  set Af : ℝ → ℝ := fun μ => if 0 < μ then
      Kc * _root_.BoseGases.a v / (8 * μ * (1 + ellH v μ ^ 3)) else 0 with hAf
  set ηf : ℝ → ℝ := fun μ => Kc * _root_.BoseGases.a v /
      (16 * (max C_A 1) * μ * (1 + ellH v μ ^ 3) ^ 2 * ellH v μ ^ 3) with hηf
  have hηfpos : ∀ μ : ℝ, 0 < μ → 0 < ηf μ := by
    intro μ hμ
    have hℓpos : 0 < ellH v μ := ellH_pos v μ
    rw [hηf]
    exact div_pos (mul_pos hKcpos hav) (by positivity)
  set Tf : ℝ → ℕ := fun μ => if hh : (0 < μ ∧ R ≤ ellH v μ * Submission.BoseGases.chiR0
      ∧ 2 * R ≤ ellH v μ)
      then Classical.choose (hB (μ := μ) hh.1 hh.2.1 hh.2.2 (ηf μ) (hηfpos μ hh.1)) else 0 with hTf
  have hTfspec : ∀ μ (hμ : 0 < μ)
      (h1 : R ≤ ellH v μ * Submission.BoseGases.chiR0) (h2 : 2 * R ≤ ellH v μ) {N : ℕ},
      Tf μ ≤ N → ChKerPair v h μ fu N
        (ηf μ * ellH v μ ^ 3 + C_B * ellH v μ ^ 3 * (R / ellH v μ) ^ 12) := by
    intro μ hμ h1 h2 N hN
    have hh : (0 < μ ∧ R ≤ ellH v μ * Submission.BoseGases.chiR0 ∧ 2 * R ≤ ellH v μ) :=
      ⟨hμ, h1, h2⟩
    simp only [hTf, dif_pos hh] at hN ⊢
    exact Classical.choose_spec (hB (μ := μ) hμ h1 h2 (ηf μ) (hηfpos μ hμ)) hN
  refine ⟨Kc, hKcpos, Af, Tf, ?_, ?_, ?_⟩
  · intro μ
    have hℓpos : 0 < ellH v μ := ellH_pos v μ
    rw [hAf]
    dsimp only
    by_cases hμ : 0 < μ
    · rw [if_pos hμ]
      exact div_nonneg (mul_nonneg hKcpos.le hav.le) (by positivity)
    · rw [if_neg hμ]
  · intro μ hμ
    rw [hAf]
    dsimp only
    rw [if_pos hμ]
    have hℓpos : 0 < ellH v μ := ellH_pos v μ
    have hbud : 2 * (ellH v μ) ^ (-3 : ℤ)
          * (4 * μ ^ 2 * (ellH v μ) ^ 6 * (1 + (ellH v μ) ^ (-3 : ℤ)) *
              (Kc * _root_.BoseGases.a v / (8 * μ * (1 + ellH v μ ^ 3))))
        = Kc * (μ * _root_.BoseGases.a v) := by
      simp only [zpow_neg]
      field_simp
      ring
    exact le_of_eq hbud
  · intro Nmin hNth hTN hreg HM hMono μ hAdm hJ n Φ hn hnorm hlowB hspec i j hij
    obtain ⟨hμ, hμa3, hparams⟩ := hAdm
    have hℓpos : 0 < ellH v μ := ellH_pos v μ
    have hε₀ : 0 < max ε₀ 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
    have hε₀le : ε₀ ≤ max ε₀ 1 := le_max_left _ _
    have hreg1 : R ≤ ellH v μ * Submission.BoseGases.chiR0 := (hreg μ ⟨hμ, hμa3, hparams⟩).1
    have hreg2 : 2 * R ≤ ellH v μ := by
      have h4 := (hreg μ ⟨hμ, hμa3, hparams⟩).2
      linarith
    have hmono : Tf μ ≤ (HM μ).N := le_trans (hTN μ) (hMono μ)
    have hker := hTfspec μ hμ hreg1 hreg2 hmono
    have hslot := hA (μ := μ) hμ (N := (HM μ).N) (n := n) (i := i) (j := j) hij Φ
      (ηf μ * ellH v μ ^ 3 + C_B * ellH v μ ^ 3 * (R / ellH v μ) ^ 12) hker
    -- the two key estimates
    have hμle : μ ≤ max ε₀ 1 / (_root_.BoseGases.a v) ^ 3 := by
      rw [le_div_iff₀ (by positivity : (0:ℝ) < (_root_.BoseGases.a v) ^ 3)]
      exact le_trans hμa3 hε₀le
    have h2Rpos : 0 < 2 * R := by linarith
    have hinv3 : (ellH v μ ^ 3)⁻¹ ≤ ((2 * R) ^ 3)⁻¹ :=
      (inv_le_inv₀ (pow_pos hℓpos 3) (pow_pos h2Rpos 3)).mpr
        (pow_le_pow_left₀ h2Rpos.le hreg2 3)
    have hinv9 : (ellH v μ ^ 9)⁻¹ ≤ ((2 * R) ^ 9)⁻¹ :=
      (inv_le_inv₀ (pow_pos hℓpos 9) (pow_pos h2Rpos 9)).mpr
        (pow_le_pow_left₀ h2Rpos.le hreg2 9)
    have hkey1 : μ * (ellH v μ ^ 3)⁻¹ / _root_.BoseGases.a v
        ≤ max ε₀ 1 / ((_root_.BoseGases.a v) ^ 4 * (2 * R) ^ 3) := by
      have hab : (0:ℝ) < _root_.BoseGases.a v := hav
      have h1 : μ * (ellH v μ ^ 3)⁻¹ ≤ (max ε₀ 1 / (_root_.BoseGases.a v) ^ 3) * ((2 * R) ^ 3)⁻¹ :=
        mul_le_mul hμle hinv3 (inv_nonneg.mpr (pow_nonneg hℓpos.le 3))
          (div_nonneg hε₀.le (pow_nonneg hav.le 3))
      calc μ * (ellH v μ ^ 3)⁻¹ / _root_.BoseGases.a v
          ≤ ((max ε₀ 1 / (_root_.BoseGases.a v) ^ 3) * ((2 * R) ^ 3)⁻¹) / _root_.BoseGases.a v :=
            div_le_div_of_nonneg_right h1 hab.le
        _ = max ε₀ 1 / ((_root_.BoseGases.a v) ^ 4 * (2 * R) ^ 3) := by
            first | (field_simp; ring) | field_simp
    have hkey2 : μ * (ellH v μ ^ 9)⁻¹ / _root_.BoseGases.a v
        ≤ max ε₀ 1 / ((_root_.BoseGases.a v) ^ 4 * (2 * R) ^ 9) := by
      have hab : (0:ℝ) < _root_.BoseGases.a v := hav
      have h1 : μ * (ellH v μ ^ 9)⁻¹ ≤ (max ε₀ 1 / (_root_.BoseGases.a v) ^ 3) * ((2 * R) ^ 9)⁻¹ :=
        mul_le_mul hμle hinv9 (inv_nonneg.mpr (pow_nonneg hℓpos.le 9))
          (div_nonneg hε₀.le (pow_nonneg hav.le 3))
      calc μ * (ellH v μ ^ 9)⁻¹ / _root_.BoseGases.a v
          ≤ ((max ε₀ 1 / (_root_.BoseGases.a v) ^ 3) * ((2 * R) ^ 9)⁻¹) / _root_.BoseGases.a v :=
            div_le_div_of_nonneg_right h1 hab.le
        _ = max ε₀ 1 / ((_root_.BoseGases.a v) ^ 4 * (2 * R) ^ 9) := by
            first | (field_simp; ring) | field_simp
    have harith := cslot_arith (a := _root_.BoseGases.a v) (R := R) (μ := μ)
      (ℓ := ellH v μ) (C_A := C_A) (C_B := C_B) (K0 := Kc) (η := ηf μ) (ε₀ := max ε₀ 1)
      hav hR hμ (ellH_pos v μ) hε₀ hCA0 hCB0 hkey1 hkey2 hKc (by rw [hηf])
    obtain ⟨-, -, harith'⟩ := harith
    have hAfμ : Af μ = Kc * _root_.BoseGases.a v / (8 * μ * (1 + ellH v μ ^ 3)) := by
      rw [hAf]; exact dif_pos hμ
    have hnormBnn : 0 ≤ Work.BoseBoxFix.normB v μ n Φ := by
      rw [Work.BoseBoxFix.normB, Work.BoseKinLoc.sqNormB]
      exact integral_nonneg (fun x => by positivity)
    have hstep : C_A * ((ηf μ * ellH v μ ^ 3 + C_B * ellH v μ ^ 3 * (R / ellH v μ) ^ 12)
          * (1 + ellH v μ ^ 3))
        ≤ Kc * _root_.BoseGases.a v / (8 * μ * (1 + ellH v μ ^ 3)) := by
      have := harith'
      linarith [this]
    calc ‖chCslot v h fc fu μ (HM μ).N i j
          (Work.BoseBoxFock.boxRestrictR (ellH v μ) (Φ : Submission.BoseGases.X n → ℝ))‖
        ≤ C_A * ((ηf μ * ellH v μ ^ 3 + C_B * ellH v μ ^ 3 * (R / ellH v μ) ^ 12)
              * (1 + ellH v μ ^ 3)) * Work.BoseBoxFix.normB v μ n Φ := hslot
      _ ≤ (Kc * _root_.BoseGases.a v / (8 * μ * (1 + ellH v μ ^ 3)))
            * Work.BoseBoxFix.normB v μ n Φ :=
          mul_le_mul_of_nonneg_right hstep hnormBnn
      _ = Af μ * Work.BoseBoxFix.normB v μ n Φ := by rw [hAfμ]

end Work.BoseBoxFock.PCFU
