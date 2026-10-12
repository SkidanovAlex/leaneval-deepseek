import ChallengeDeps
import Submission.Work.BoseBoxFock.gapRowSum
import Submission.Work.BoseBoxFock.momRowSum
import Submission.Work.BoseBoxFock.slotLeReserve
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.bf3a_kin_reserve` — the kinetic rows *with the reserve*

BF3a (`Submission.Work.BoseBoxFock.bf3a_kin`) compares the first-quantised kinetic word

`W2kinB v μ n Φ = kinTauB + (b/2ℓ²)·cnPlus + (ε_Tb/2d²ℓ²)·nPlusHB`

— only **half** of each of the two box gaps `bℓ⁻²cnPlus`, `bε_T(dℓ)⁻²nPlusHB` — with the sharp
box kinetic word `kinFormB`.  FS `prop:Hamilton2ndQuant`'s *other* halves of those two gaps are
the **reserve** used to pay its error terms.  This module proves that the reserve is not needed:
in the same admissible regime the kinetic rows can be paid at **full strength**,

    `W2kinB + (b/2ℓ²)·cnPlus + (ε_Tb/2d²ℓ²)·nPlusHB ≤ kinFormB`,

i.e. `kinTauB + bℓ⁻²·cnPlus + bε_T(dℓ)⁻²·nPlusHB ≤ kinFormB` (no error term at all).  The
mechanism is that the fibre-wise symbol comparison `τ̃ ≤ mainWord` (`bf3a_fibre`) leaves the two
gap rows `gapWord`, `momWord` *untouched*: `fsT = neuWord + gapWord + momWord + mainWord` with all
four pieces nonnegative (`Work.BoseKinLoc.Word.fsT_nonneg`), so the full gaps may sit on the left
and the pointwise inequality

    `bsOneBody ℓ τ̃ 0 ψ + gapWord ℓ b 0 ψ + momWord ℓ d ε_T b 0 ψ ≤ fsT ℓ d s ε_T b 0 ψ`

holds fibre by fibre.  `bf3a_kin`'s per-slot inequality only had the halves because it discarded
the slack `½gapWord + ½momWord`; here the slack is kept.

## The slot bookkeeping

* per slot `i`, `slotLeReserve` (`Submission.Work.BoseBoxFock.slotLeReserve`) is the *integrated*
  fibre inequality, obtained from the pointwise one by `integral_mono_of_nonneg` (the dominating
  integrand `1_Λ(xᵢ)·(fsT − gapWord − momWord)` is integrable on `abox n ℓ`,
  `integrableOn_fsT_fibre_smooth` minus the two pieces of `pieces_integrableOn_fibre`);
* summing `ℓ⁻³·(·)` over the slots turns the three rows into `kinTauB`,
  `ℓ⁻³·Σᵢ∫ 1_Λ(xᵢ)·gapWord = bℓ⁻²·cnPlus` (`gapRowSum`) and
  `ℓ⁻³·Σᵢ∫ 1_Λ(xᵢ)·momWord = bε_T(dℓ)⁻²·nPlusHB` (`momRowSum`), while the right-hand side is
  `kinFormB` by definition;
* the coefficient arithmetic at the parameters `P = paramsAt μ (a v)`, `ℓ = sideAt μ (a v)`
  (`field_simp`, `ring`) matches the doubled halves with `bℓ⁻²cnPlus` and `bε_T(dℓ)⁻²nPlusHB`.
-/

noncomputable section
open scoped Real Topology BigOperators
open MeasureTheory Metric Filter

namespace Work.BoseBoxFock

open _root_.BoseGases Submission.BoseGases Work.UBB Work.BoseBox Work.BoseBoxFix
open Work.BoseKinLoc Work.BSKinetic

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 2000000

/-! ## 1. The kinetic-row comparison at full gap strength -/

/-- **The kinetic rows with the full gaps.**  For every box state `Φ` and every positive
`ℓ, s, d`, `0 ≤ ε_T ≤ 1`, `b ≥ 0`, the first-quantised kinetic rows at *full* strength are
dominated by the box kinetic word:

`kinTauB + bℓ⁻²·cnPlus + bε_T(dℓ)⁻²·nPlusHB ≤ kinFormB`. -/
theorem kinRowB_reserve {ℓ d s eT b : ℝ} (hℓ : 0 < ℓ) (hs : 0 < s) (hd : 0 < d)
    (heT0 : 0 ≤ eT) (heT1 : eT ≤ 1) (hb : 0 ≤ b)
    {n : ℕ} {Φ : Submission.BoseGases.X n → ℝ} (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) :
    kinTauB n ℓ d s eT Φ + b * ℓ ^ (-2 : ℤ) * cnPlus ℓ Φ
        + b * eT * (d * ℓ) ^ (-2 : ℤ) * nPlusHB ℓ d Φ
      ≤ kinFormB n ℓ d s eT b Φ := by
  have hℓne : ℓ ≠ 0 := ne_of_gt hℓ
  -- the power identity `ℓ⁻³ℓ³ = 1`
  have hz : ℓ ^ (-3 : ℤ) * ℓ ^ 3 = 1 := by
    rw [← zpow_natCast ℓ 3, ← zpow_add₀ hℓne]
    norm_num
  -- `kinTauB` as a slot sum
  have hA : (∑ i : Fin n, ℓ ^ (-3 : ℤ) *
        (∫ x in abox n ℓ,
          indU ℓ 0 (x i) * bsOneBody ℓ (tauSmRad eT s d ℓ) 0 (fibre n i Φ x)))
      = kinTauB n ℓ d s eT Φ := by
    simp only [kinTauB, slotFormB]
  -- `kinFormB` as a slot sum
  have hD : (∑ i : Fin n, ℓ ^ (-3 : ℤ) *
        (∫ x in abox n ℓ, indU ℓ 0 (x i) * fsT ℓ d s eT b 0 (fibre n i Φ x)))
      = kinFormB n ℓ d s eT b Φ := by
    rw [kinFormB, ← Finset.mul_sum]
  -- the gap slot sum
  have hB : (∑ i : Fin n, ℓ ^ (-3 : ℤ) *
        (∫ x in abox n ℓ, indU ℓ 0 (x i) * gapWord ℓ b 0 (fibre n i Φ x)))
      = b * ℓ ^ (-2 : ℤ) * cnPlus ℓ Φ := by
    rw [← Finset.mul_sum, gapRowSum (ℓ := ℓ) (b := b) hℓ hΦ]
    rw [show ℓ ^ (-3 : ℤ) * (b * ℓ ^ (-2 : ℤ) * (ℓ ^ 3 * cnPlus ℓ Φ))
        = (ℓ ^ (-3 : ℤ) * ℓ ^ 3) * (b * ℓ ^ (-2 : ℤ) * cnPlus ℓ Φ) by ring, hz, one_mul]
  -- the momentum slot sum
  have hC : (∑ i : Fin n, ℓ ^ (-3 : ℤ) *
        (∫ x in abox n ℓ, indU ℓ 0 (x i) * momWord ℓ d eT b 0 (fibre n i Φ x)))
      = b * eT * (d * ℓ) ^ (-2 : ℤ) * nPlusHB ℓ d Φ := by
    rw [← Finset.mul_sum, momRowSum (ℓ := ℓ) (d := d) (eT := eT) (b := b) hℓ (Φ := Φ)]
    rw [show ℓ ^ (-3 : ℤ) * (b * eT * (d * ℓ) ^ (-2 : ℤ) * (ℓ ^ 3 * nPlusHB ℓ d Φ))
        = (ℓ ^ (-3 : ℤ) * ℓ ^ 3) * (b * eT * (d * ℓ) ^ (-2 : ℤ) * nPlusHB ℓ d Φ) by ring,
      hz, one_mul]
  -- the summed slot inequality
  have hsum0 := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) =>
    mul_le_mul_of_nonneg_left
      (slotLeReserve (ℓ := ℓ) (d := d) (s := s) (eT := eT) (b := b) hℓ hs hd heT0 heT1 hb i hΦ)
      (zpow_nonneg hℓ.le (-3 : ℤ)))
  -- distribute `ℓ⁻³` over the three rows of the slot integrand
  have hstep : (∑ i : Fin n, ℓ ^ (-3 : ℤ) *
        ((∫ x in abox n ℓ,
            indU ℓ 0 (x i) * bsOneBody ℓ (tauSmRad eT s d ℓ) 0 (fibre n i Φ x))
          + (∫ x in abox n ℓ, indU ℓ 0 (x i) * gapWord ℓ b 0 (fibre n i Φ x))
          + (∫ x in abox n ℓ, indU ℓ 0 (x i) * momWord ℓ d eT b 0 (fibre n i Φ x))))
      = ∑ i : Fin n, (ℓ ^ (-3 : ℤ) *
              (∫ x in abox n ℓ,
                indU ℓ 0 (x i) * bsOneBody ℓ (tauSmRad eT s d ℓ) 0 (fibre n i Φ x))
          + ℓ ^ (-3 : ℤ) * (∫ x in abox n ℓ, indU ℓ 0 (x i) * gapWord ℓ b 0 (fibre n i Φ x))
          + ℓ ^ (-3 : ℤ) *
              (∫ x in abox n ℓ, indU ℓ 0 (x i) * momWord ℓ d eT b 0 (fibre n i Φ x))) :=
    Finset.sum_congr rfl fun i _ => by ring
  have hL : (∑ i : Fin n, ℓ ^ (-3 : ℤ) *
        ((∫ x in abox n ℓ,
            indU ℓ 0 (x i) * bsOneBody ℓ (tauSmRad eT s d ℓ) 0 (fibre n i Φ x))
          + (∫ x in abox n ℓ, indU ℓ 0 (x i) * gapWord ℓ b 0 (fibre n i Φ x))
          + (∫ x in abox n ℓ, indU ℓ 0 (x i) * momWord ℓ d eT b 0 (fibre n i Φ x))))
      = (∑ i : Fin n, ℓ ^ (-3 : ℤ) *
            (∫ x in abox n ℓ,
              indU ℓ 0 (x i) * bsOneBody ℓ (tauSmRad eT s d ℓ) 0 (fibre n i Φ x)))
        + (∑ i : Fin n, ℓ ^ (-3 : ℤ) *
            (∫ x in abox n ℓ, indU ℓ 0 (x i) * gapWord ℓ b 0 (fibre n i Φ x)))
        + (∑ i : Fin n, ℓ ^ (-3 : ℤ) *
            (∫ x in abox n ℓ, indU ℓ 0 (x i) * momWord ℓ d eT b 0 (fibre n i Φ x))) := by
    rw [hstep, Finset.sum_add_distrib, Finset.sum_add_distrib]
  rw [hL] at hsum0
  rw [hA, hB, hC, hD] at hsum0
  exact hsum0

/-! ## 2. The target: the kinetic rows at BoxFS's parameters -/

theorem bf3a_kin_reserve (v : ℝ³ → ℝ) (h : Work.UBB.ScatSol v) (hav : 0 < BoseGases.a v) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧
      ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
        ∀ (n : ℕ) (Φ : Work.BoseKinLoc.BoxState n (Work.BoseBox.sideAt μ (BoseGases.a v))),
          (n : ℝ) ≤ 2 * μ * Work.BoseBox.sideAt μ (BoseGases.a v) ^ 3 →
          Work.BoseBoxFock.W2kinB v μ n (Φ : Submission.BoseGases.X n → ℝ)
              + (Work.BoseBox.paramsAt μ (BoseGases.a v)).b / 2
                  * Work.BoseBox.sideAt μ (BoseGases.a v) ^ (-2 : ℤ)
                  * Submission.BoseGases.cnPlus (Work.BoseBox.sideAt μ (BoseGases.a v))
                      (Φ : Submission.BoseGases.X n → ℝ)
              + ((Work.BoseBox.paramsAt μ (BoseGases.a v)).eT
                    * (Work.BoseBox.paramsAt μ (BoseGases.a v)).b
                    / (2 * (Work.BoseBox.paramsAt μ (BoseGases.a v)).d ^ 2
                        * Work.BoseBox.sideAt μ (BoseGases.a v) ^ 2))
                  * Work.BoseBoxFix.nPlusHB (Work.BoseBox.sideAt μ (BoseGases.a v))
                      (Work.BoseBox.paramsAt μ (BoseGases.a v)).d
                      (Φ : Submission.BoseGases.X n → ℝ)
            ≤ Work.BoseKinLoc.kinFormB n (Work.BoseBox.sideAt μ (BoseGases.a v))
                (Work.BoseBox.paramsAt μ (BoseGases.a v)).d
                (Work.BoseBox.paramsAt μ (BoseGases.a v)).s
                (Work.BoseBox.paramsAt μ (BoseGases.a v)).eT
                (Work.BoseBox.paramsAt μ (BoseGases.a v)).b
                (Φ : Submission.BoseGases.X n → ℝ) := by
  refine ⟨1, one_pos, ?_⟩
  intro μ hAdm n Φ _
  obtain ⟨hμ, ht1, _⟩ := hAdm
  have ha : 0 < BoseGases.a v := hav
  have hμa : 0 < μ * (BoseGases.a v) ^ 3 := by positivity
  let P : Work.BoseBox.FSParams := Work.BoseBox.paramsAt μ (BoseGases.a v)
  let ℓ : ℝ := Work.BoseBox.sideAt μ (BoseGases.a v)
  have hpar : P = Work.BoseBox.fsParams (μ * (BoseGases.a v) ^ 3) := rfl
  have hs : 0 < P.s := by
    rw [hpar]; exact Work.BoseBox.fsXp_pos hμa
  have hd : 0 < P.d := by
    rw [hpar]; exact Work.BoseBox.fsXp_pos hμa
  have hKl : 0 < P.Kl := by
    rw [hpar]; exact Work.BoseBox.fsXp_pos hμa
  have heT0 : 0 ≤ P.eT := by
    rw [hpar]
    exact le_of_lt (Work.BoseBox.fsXp_pos hμa)
  have heT1 : P.eT ≤ 1 := by
    rw [hpar]
    exact Work.BoseBox.fsXp_le_one hμa ht1 (by norm_num)
  have hb : 0 ≤ P.b := by
    rw [hpar]
    simp only [Work.BoseBox.fsParams, Work.BoseBox.bValue]
    norm_num
  have hℓpos : 0 < ℓ := by
    show 0 < Work.BoseBox.sideAt μ (BoseGases.a v)
    rw [Work.BoseBox.sideAt, Work.BoseBox.boxSide]
    exact mul_pos hKl (Real.rpow_pos_of_pos (by positivity) _)
  have hΦ : ContDiff ℝ (⊤ : ℕ∞) (Φ : Submission.BoseGases.X n → ℝ) := Φ.contDiff
  -- `W2kinB` unfolds to the three rows, spelled as in the goal
  have hexp : W2kinB v μ n (Φ : Submission.BoseGases.X n → ℝ)
      = kinTauB n ℓ P.d P.s P.eT (Φ : Submission.BoseGases.X n → ℝ)
        + (P.b / 2) * ℓ ^ (-2 : ℤ) * cnPlus ℓ (Φ : Submission.BoseGases.X n → ℝ)
        + (P.eT * P.b / (2 * P.d ^ 2 * ℓ ^ 2)) * nPlusHB ℓ P.d
            (Φ : Submission.BoseGases.X n → ℝ) := rfl
  -- the full-gap kinetic-row bound at the parameters
  have hmain := kinRowB_reserve (ℓ := ℓ) (d := P.d) (s := P.s) (eT := P.eT) (b := P.b)
    hℓpos hs hd heT0 heT1 hb hΦ
  -- the two reserve halves combine into the full gap coefficients
  have hA2 : (P.b / 2) * ℓ ^ (-2 : ℤ) * cnPlus ℓ (Φ : Submission.BoseGases.X n → ℝ)
        + (P.b / 2) * ℓ ^ (-2 : ℤ) * cnPlus ℓ (Φ : Submission.BoseGases.X n → ℝ)
      = P.b * ℓ ^ (-2 : ℤ) * cnPlus ℓ (Φ : Submission.BoseGases.X n → ℝ) := by
    ring
  have hB2 : (P.eT * P.b / (2 * P.d ^ 2 * ℓ ^ 2)) * nPlusHB ℓ P.d
          (Φ : Submission.BoseGases.X n → ℝ)
        + (P.eT * P.b / (2 * P.d ^ 2 * ℓ ^ 2)) * nPlusHB ℓ P.d
          (Φ : Submission.BoseGases.X n → ℝ)
      = P.b * P.eT * (P.d * ℓ) ^ (-2 : ℤ) * nPlusHB ℓ P.d
          (Φ : Submission.BoseGases.X n → ℝ) := by
    field_simp
    ring
  rw [hexp]
  linarith [hmain, hA2, hB2]

end Work.BoseBoxFock
