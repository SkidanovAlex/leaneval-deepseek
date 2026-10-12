import ChallengeDeps
import Submission.Work.BoseBogFS.bogSumAux
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBogFS.bogVmaxt_le_decay` — the decaying far-side bound of the `β`-interval

The three rows

* `bogVmaxt ≤ 4·bogVs/(1+√(ρ a)‖tSca‖)`,
* `−2·bogVs ≤ bogVlot`,
* `bogVhit − bogVlot ≤ 4·bogOscM/(1+√(ρ a)‖tSca‖)`

of the clean Riemann row.  They are the *decaying* companions of `bogBeta_le_decay`: on a far cell
the whole interval `[v_lo,v_hi]`, and not merely its centre `β_s(t_n)`, is controlled by the
decaying denominator `1+√(ρ·a v)‖tSca‖`.

The proof has three ingredients, all elementary:

* `bogOm = bogOscM/(1+√(ρa)·r_lo)` (the definitions of `bogOm`/`bogOscK`/`bogOscM`),
* `(1+√(ρa)‖tSca‖)/2 ≤ 1+√(ρa)·r_lo`, i.e. `√(ρa)·Δ ≤ √(ρa)‖tSca‖/2`, which is
  **exactly** the hypothesis `2·bogHalf ≤ ‖tSca‖` (no use of `√(ρ/a)Δ ≤ 1` is made),
* the scalar comparison `1/X ≤ 2/Y` from `Y/2 ≤ X`, and the arithmetic of
  `|β ± o| ≤ |β| + o ≤ B/Y + 2O/Y ≤ 4(B+O)/Y`.
-/

noncomputable section

open scoped Real Topology BigOperators

namespace Work.BoseBogFS

open _root_.BoseGases Work.UBB Work.BoseFixR

set_option autoImplicit false
set_option linter.unusedVariables false

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-! ## 1. Auxiliary facts -/

/-- `bogOm` is `bogOscM` divided by the honest lower-radius denominator. -/
lemma bogOm_eq_oscM_div (v : E3 → ℝ) (h : ScatSol v) (R ρ μ : ℝ) (n : Fin 3 → ℤ) :
    bogOm v h R ρ μ n
      = bogOscM v R ρ μ / (1 + Real.sqrt (ρ * a v) * bogRLot v ρ μ n) := by
  rw [bogOm, bogOscK, bogOscM]

/-- The `bogOm` denominator is at least half of the `tSca` denominator, on cells with
`2Δ ≤ ‖tSca‖`. -/
lemma half_le_rlo_den {v : E3 → ℝ} {ρ μ : ℝ} {n : Fin 3 → ℤ}
    (hΔ : 2 * bogHalf v ρ μ ≤ ‖tSca v ρ μ n‖) :
    (1 + Real.sqrt (ρ * a v) * ‖tSca v ρ μ n‖) / 2
      ≤ 1 + Real.sqrt (ρ * a v) * bogRLot v ρ μ n := by
  have hP : 0 ≤ Real.sqrt (ρ * a v) := Real.sqrt_nonneg _
  have hle : bogHalf v ρ μ ≤ ‖tSca v ρ μ n‖ / 2 := by linarith
  have hmul : Real.sqrt (ρ * a v) * bogHalf v ρ μ
      ≤ Real.sqrt (ρ * a v) * ‖tSca v ρ μ n‖ / 2 := by
    calc Real.sqrt (ρ * a v) * bogHalf v ρ μ
        ≤ Real.sqrt (ρ * a v) * (‖tSca v ρ μ n‖ / 2) := mul_le_mul_of_nonneg_left hle hP
      _ = Real.sqrt (ρ * a v) * ‖tSca v ρ μ n‖ / 2 := by ring
  rw [bogRLot]
  linarith [hmul]

/-- `O/X ≤ 2·O/Y` as soon as `0 ≤ O` and `Y/2 ≤ X`. -/
lemma div_le_two_div_of_half {O X Y : ℝ} (hO : 0 ≤ O) (hY : 0 < Y)
    (h : Y / 2 ≤ X) : O / X ≤ 2 * O / Y := by
  have hY2 : 0 < Y / 2 := by linarith
  have hratio : 1 / X ≤ 2 / Y := by
    have h1 : 1 / X ≤ 1 / (Y / 2) := one_div_le_one_div_of_le hY2 h
    have h2 : 1 / (Y / 2) = 2 / Y := by ring
    linarith
  calc O / X = O * (1 / X) := by rw [div_eq_mul_one_div]
    _ ≤ O * (2 / Y) := mul_le_mul_of_nonneg_left hratio hO
    _ = 2 * O / Y := by ring

/-- The scalar arithmetic core of the far-side decay: from the decaying bounds on the centre
`|β| ≤ B/Y` and on the oscillation `o ≤ 2·O/Y` one gets all three rows of
`bogVmaxt_le_decay`, in abstract variables. -/
lemma bog_decay_core {B O β om Y : ℝ} (hβ : |β| ≤ B / Y)
    (hom : om ≤ 2 * O / Y) (hom0 : 0 ≤ om) (hB : 0 < B) (hO : 0 ≤ O) (hY : 1 ≤ Y) :
    max |β - om| |β + om| ≤ 4 * (B + O) / Y
      ∧ om - β ≤ (B + 2 * O) / Y
      ∧ 2 * om ≤ 4 * O / Y := by
  have hY0 : 0 < Y := lt_of_lt_of_le one_pos hY
  have hBO : 0 ≤ B + 2 * O := by linarith
  have hsum : B / Y + 2 * O / Y = (B + 2 * O) / Y := by ring
  have hab : |β| + om ≤ (B + 2 * O) / Y := by
    have h := add_le_add hβ hom
    rw [hsum] at h
    exact h
  have h1 : |β - om| ≤ (B + 2 * O) / Y := by
    have h := abs_sub β om
    rw [abs_of_nonneg hom0] at h
    exact le_trans h hab
  have h2 : |β + om| ≤ (B + 2 * O) / Y := by
    have h := abs_add_le β om
    rw [abs_of_nonneg hom0] at h
    exact le_trans h hab
  have h3 : (B + 2 * O) / Y ≤ 4 * (B + O) / Y :=
    div_le_div_of_nonneg_right (by linarith) hY0.le
  have h4 : om - β ≤ (B + 2 * O) / Y := by
    have hsum2 : 2 * O / Y + B / Y = (B + 2 * O) / Y := by ring
    have h := add_le_add hom hβ
    rw [hsum2] at h
    have h5 : om - β ≤ om + |β| := by linarith [neg_le_abs β]
    linarith
  have h9 : 2 * (2 * O / Y) = 4 * O / Y := by ring
  exact ⟨max_le (le_trans h1 h3) (le_trans h2 h3), h4, by linarith [hom, h9]⟩

/-! ## 2. The target -/

theorem bogVmaxt_le_decay {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : Work.UBB.ScatSol v} {R ρ μ : ℝ}
    {n : Fin 3 → ℤ}
    (hR : 0 < R) (hρ : 0 < ρ) (hav : 0 < _root_.BoseGases.a v)
    (hv : ∀ x, 0 ≤ v x) (hvrad : _root_.BoseGases.IsRadial v)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    (hRℓ : R ≤ Work.BoseFixR.ell v μ * Submission.BoseGases.chiR0)
    (hδ : 0 < Work.BoseBogFS.bogMesh v ρ μ) (hn : n ≠ 0)
    (hΔ : 2 * Work.BoseBogFS.bogHalf v ρ μ ≤ ‖Work.BoseBogFS.tSca v ρ μ n‖)
    (hOs : Real.sqrt (ρ / _root_.BoseGases.a v) * Work.BoseBogFS.bogHalf v ρ μ ≤ 1) :
    Work.BoseBogFS.bogVmaxt v h R ρ μ n
        ≤ 4 * Work.BoseBogFS.bogVs v R ρ μ
          / (1 + Real.sqrt (ρ * _root_.BoseGases.a v) * ‖Work.BoseBogFS.tSca v ρ μ n‖)
      ∧ -(2 * Work.BoseBogFS.bogVs v R ρ μ) ≤ Work.BoseBogFS.bogVlot v h R ρ μ n
      ∧ Work.BoseBogFS.bogVhit v h R ρ μ n - Work.BoseBogFS.bogVlot v h R ρ μ n
        ≤ 4 * Work.BoseBogFS.bogOscM v R ρ μ
          / (1 + Real.sqrt (ρ * _root_.BoseGases.a v) * ‖Work.BoseBogFS.tSca v ρ μ n‖) := by
  have hO : 0 ≤ bogOscM v R ρ μ := bogOscM_nonneg hR.le hav hρ hδ
  have hB : 0 < bogBs v R := bogBs_pos v R
  have hYpos : 0 < 1 + Real.sqrt (ρ * a v) * ‖tSca v ρ μ n‖ := by
    have h := mul_nonneg (Real.sqrt_nonneg (ρ * a v)) (norm_nonneg (tSca v ρ μ n))
    linarith
  have hY1 : 1 ≤ 1 + Real.sqrt (ρ * a v) * ‖tSca v ρ μ n‖ := by
    have h := mul_nonneg (Real.sqrt_nonneg (ρ * a v)) (norm_nonneg (tSca v ρ μ n))
    linarith
  have hβ : |betaSc v h ρ μ (tSca v ρ μ n)|
      ≤ bogBs v R / (1 + Real.sqrt (ρ * a v) * ‖tSca v ρ μ n‖) :=
    bogBeta_le_decay (h := h) hR hρ hav hv hvrad hv_supp hRℓ (tSca v ρ μ n)
  have hden := half_le_rlo_den (v := v) (ρ := ρ) (μ := μ) (n := n) hΔ
  have hom : bogOm v h R ρ μ n
      ≤ 2 * bogOscM v R ρ μ / (1 + Real.sqrt (ρ * a v) * ‖tSca v ρ μ n‖) := by
    rw [bogOm_eq_oscM_div]
    exact div_le_two_div_of_half hO hYpos hden
  have hom0 : 0 ≤ bogOm v h R ρ μ n := bogOm_nonneg hρ hav hR.le hδ hn
  obtain ⟨hc1, hc2, hc3⟩ := bog_decay_core hβ hom hom0 hB hO hY1
  have hVs : bogVs v R ρ μ = bogBs v R + bogOscM v R ρ μ := by
    rw [bogVs, max_eq_right hO]
  have hVmaxt : bogVmaxt v h R ρ μ n
      = max |betaSc v h ρ μ (tSca v ρ μ n) - bogOm v h R ρ μ n|
          |betaSc v h ρ μ (tSca v ρ μ n) + bogOm v h R ρ μ n| := by
    rw [bogVmaxt, bogVlot, bogVhit, bogVNt]
  have hVlot : bogVlot v h R ρ μ n
      = betaSc v h ρ μ (tSca v ρ μ n) - bogOm v h R ρ μ n := by
    rw [bogVlot, bogVNt]
  have hVhit : bogVhit v h R ρ μ n - bogVlot v h R ρ μ n = 2 * bogOm v h R ρ μ n := by
    rw [bogVhit, bogVlot]
    ring
  have hZ : (bogBs v R + 2 * bogOscM v R ρ μ)
        / (1 + Real.sqrt (ρ * a v) * ‖tSca v ρ μ n‖)
      ≤ bogBs v R + 2 * bogOscM v R ρ μ :=
    div_le_self (by linarith [hB, hO]) hY1
  refine ⟨?_, ?_, ?_⟩
  · rw [hVmaxt, hVs]
    exact hc1
  · rw [hVlot, hVs]
    linarith [hc2, hZ, hB]
  · rw [hVhit]
    exact hc3

end Work.BoseBogFS
