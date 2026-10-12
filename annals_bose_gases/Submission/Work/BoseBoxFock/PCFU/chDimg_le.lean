import ChallengeDeps
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseBoxFock.PCFU.SlotPieceDefs
import Submission.Work.BoseBoxFock.PCFU.chDimg_arith
import Submission.Work.BoseBoxFock.PCFU.chDimg_norm_le
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseBoxFock.PCFU.chDimg_le` — the `(D)`-channel lattice-image slot

Holder of the target `Work.BoseBoxFock.PCFU.chDimg_le` (the `SlotPiece` bound for the channel piece
`PCFU.chDimg`, one of the eight pieces of `PotCubicFreeU_exists`).

## The two explicit identifications of the FS parameters

At `μ > 0` the dictionary's low-momentum cut-off `chKappa v μ` and the box side `ellH v μ` are, with
`t := μ · (a v)³`,

    κ = chKappa v μ = t^{151/323}/(a v) ,      ℓ = ellH v μ = (a v)·t^{−163/323} ,

equivalently `κ·ℓ = (t^{6/323})^{−2}` (because `chKappa = (d²ℓ)^{−1}` with `d = fsXp t 6 = t^{6/323}`)
and `ℓ = (a v)·t^{−163/323}` (because `ℓ = K_ℓ(μ a v)^{−1/2}` with `K_ℓ = t^{−3/646}`).  These two
relations are what the arithmetic input `PCFU.chDimg_arith` consumes.

## The assembly

`chDimg_le_of_inputs` proves the `SlotPiece` statement from the per-state estimate
`PCFU.chDimg_norm_le` (the analytic slot bound, whose constant is
`C₁(1+κ^{38})(κℓ)^{−35}ℓ^{3/2}` with `C₁` cut-off- and `μ`-independent) and the arithmetic input
`PCFU.chDimg_arith` (bounding `8C₁(1+ℓ⁻³)(1+κ^{38})(κℓ)^{−35}μℓ^{9/2}` by `K0·a` uniformly over the
admissible window).  The budget clause is discharged with equality by taking `A μ` to be the
*minimum* of the analytic constant and the maximal budget-compatible constant.  The final theorem
`chDimg_le` applies the two inputs.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace Work.BoseBoxFock.PCFU

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- **The box side at FS's parameters, explicitly**: `ℓ = K_ℓ(μa)^{−1/2} = (a v)·t^{−163/323}`
with `t = μ(a v)³`. -/
theorem ellH_eq_of_pos (v : E3 → ℝ) {μ : ℝ} (hμ : 0 < μ) (hav : 0 < BoseGases.a v) :
    ellH v μ = BoseGases.a v * (μ * (BoseGases.a v) ^ 3) ^ (-(163 / 323) : ℝ) := by
  have ht : 0 < μ * (BoseGases.a v) ^ 3 := by positivity
  have hμa : 0 < μ * BoseGases.a v := mul_pos hμ hav
  have ha0 : BoseGases.a v ≠ 0 := ne_of_gt hav
  have hpos : 0 < Work.BoseBox.sideAt μ (BoseGases.a v) := Work.BoseBox.sideAt_pos hμ hav
  have hell : ellH v μ = Work.BoseBox.sideAt μ (BoseGases.a v) := by rw [ellH, if_pos hpos]
  rw [hell]
  show Work.BoseBox.fsXp (μ * BoseGases.a v ^ 3) (-(3 / 2))
        * (μ * BoseGases.a v) ^ (-(1 / 2 : ℝ))
      = BoseGases.a v * (μ * BoseGases.a v ^ 3) ^ (-(163 / 323) : ℝ)
  rw [Work.BoseBox.fsXp]
  -- `(μa³)^{−1/2} = (μa)^{−1/2}·a^{−1}`
  have h3 : (μ * (BoseGases.a v) ^ 3) ^ (-(1 / 2 : ℝ))
      = (μ * BoseGases.a v) ^ (-(1 / 2 : ℝ)) * (BoseGases.a v)⁻¹ := by
    calc (μ * (BoseGases.a v) ^ 3) ^ (-(1 / 2 : ℝ))
        = ((μ * BoseGases.a v) * (BoseGases.a v) ^ 2) ^ (-(1 / 2 : ℝ)) := by ring_nf
      _ = (μ * BoseGases.a v) ^ (-(1 / 2 : ℝ)) * ((BoseGases.a v) ^ 2) ^ (-(1 / 2 : ℝ)) :=
          Real.mul_rpow hμa.le (by positivity)
      _ = (μ * BoseGases.a v) ^ (-(1 / 2 : ℝ)) * (BoseGases.a v)⁻¹ := by
          rw [← Real.rpow_natCast (BoseGases.a v) 2, ← Real.rpow_mul hav.le,
            show ((2 : ℕ) : ℝ) * (-(1 / 2 : ℝ)) = -1 by norm_num, Real.rpow_neg_one]
  -- hence `(μa)^{−1/2} = (μa³)^{−1/2}·a`
  have h1 : (μ * BoseGases.a v) ^ (-(1 / 2 : ℝ))
      = (μ * (BoseGases.a v) ^ 3) ^ (-(1 / 2 : ℝ)) * BoseGases.a v := by
    have h := congrArg (fun t : ℝ => t * BoseGases.a v) h3
    simp only [mul_assoc] at h
    rw [inv_mul_cancel₀ ha0, mul_one] at h
    exact h.symm
  have h4 : (μ * (BoseGases.a v) ^ 3) ^ (-(3 / 2 : ℝ) / 323)
        * (μ * (BoseGases.a v) ^ 3) ^ (-(1 / 2 : ℝ))
      = (μ * (BoseGases.a v) ^ 3) ^ (-(163 / 323) : ℝ) := by
    rw [← Real.rpow_add ht,
      show (-(3 / 2 : ℝ) / 323) + (-(1 / 2 : ℝ)) = -(163 / 323) by norm_num]
  rw [h1]
  calc (μ * (BoseGases.a v) ^ 3) ^ (-(3 / 2 : ℝ) / 323)
        * ((μ * (BoseGases.a v) ^ 3) ^ (-(1 / 2 : ℝ)) * BoseGases.a v)
      = ((μ * (BoseGases.a v) ^ 3) ^ (-(3 / 2 : ℝ) / 323)
          * (μ * (BoseGases.a v) ^ 3) ^ (-(1 / 2 : ℝ))) * BoseGases.a v := by ring
    _ = (μ * (BoseGases.a v) ^ 3) ^ (-(163 / 323) : ℝ) * BoseGases.a v := by rw [h4]
    _ = BoseGases.a v * (μ * (BoseGases.a v) ^ 3) ^ (-(163 / 323) : ℝ) := by ring

/-- **The cut-off/box-side relation**: `chKappa v μ · ellH v μ = 1/d²` with `d = t^{6/323}`,
`t = μ(a v)³`. -/
theorem chKappa_mul_ellH (v : E3 → ℝ) {μ : ℝ} (hμ : 0 < μ) (hav : 0 < BoseGases.a v) :
    chKappa v μ * ellH v μ
      = (((μ * (BoseGases.a v) ^ 3) ^ (6 / 323 : ℝ))⁻¹) ^ 2 := by
  have hpos : 0 < Work.BoseBox.sideAt μ (BoseGases.a v) := Work.BoseBox.sideAt_pos hμ hav
  have hside : Work.BoseBox.sideAt μ (BoseGases.a v) ≠ 0 := ne_of_gt hpos
  have hell : ellH v μ = Work.BoseBox.sideAt μ (BoseGases.a v) := by rw [ellH, if_pos hpos]
  rw [hell]
  show ((Work.BoseBox.fsXp (μ * BoseGases.a v ^ 3) 6) ^ 2
        * Work.BoseBox.sideAt μ (BoseGases.a v))⁻¹ * Work.BoseBox.sideAt μ (BoseGases.a v)
      = (((μ * BoseGases.a v ^ 3) ^ (6 / 323 : ℝ))⁻¹) ^ 2
  rw [Work.BoseBox.fsXp, mul_inv, inv_pow, mul_assoc, inv_mul_cancel₀ hside, mul_one]

/-- Positivity of the low-momentum cut-off. -/
theorem chKappa_pos (v : E3 → ℝ) {μ : ℝ} (hμ : 0 < μ) (hav : 0 < BoseGases.a v) :
    0 < chKappa v μ := by
  have hpos : 0 < Work.BoseBox.sideAt μ (BoseGases.a v) := Work.BoseBox.sideAt_pos hμ hav
  have ht : 0 < μ * (BoseGases.a v) ^ 3 := by positivity
  have hd : 0 < Work.BoseBox.fsXp (μ * BoseGases.a v ^ 3) 6 := by
    rw [Work.BoseBox.fsXp]
    exact Real.rpow_pos_of_pos ht _
  have hck : chKappa v μ
      = ((Work.BoseBox.fsXp (μ * BoseGases.a v ^ 3) 6) ^ 2
          * Work.BoseBox.sideAt μ (BoseGases.a v))⁻¹ := by
    simp only [chKappa, Work.BoseBox.paramsAt, Work.BoseBox.fsParams]
  rw [hck]
  exact inv_pos.mpr (mul_pos (pow_pos hd 2) hpos)

/-- **The assembly of the `(D)`-channel lattice-image slot.**  From the per-state analytic bound
(`hnorm`, with the constant `C₁(1+κ^{38})(κℓ)^{−35}ℓ^{3/2}`) and the arithmetic window bound
(`harith`), the whole `SlotPiece` statement follows. -/
private theorem chDimg_le_of_inputs (v : E3 → ℝ) (h : Work.UBB.ScatSol v)
    (hav : 0 < BoseGases.a v) {R : ℝ} (hR : 0 < R) (fc fu : Work.BoseBoxFix.LowCut)
    (J ε₀ : ℝ) {C₁ K0 : ℝ} (hC₁ : 0 ≤ C₁) (hK0 : 0 < K0)
    (hnorm : ∀ {μ : ℝ}, 0 < μ →
      R ≤ ellH v μ * Submission.BoseGases.chiR0 → 2 * R ≤ ellH v μ →
      ∀ (N n : ℕ),
        ∀ (Φ : Work.BoseKinLoc.BoxState n (Work.BoseBox.sideAt μ (BoseGases.a v)))
        (i j : Fin n), i ≠ j →
        ‖chDimg v h fc fu μ N i j
            (boxRestrictR (ellH v μ) (Φ : Submission.BoseGases.X n → ℝ))‖
          ≤ C₁ * (1 + (chKappa v μ) ^ (2 * 19))
              * ((chKappa v μ * ellH v μ)⁻¹) ^ (2 * 19 - 3)
              * (ellH v μ) ^ (3 / 2 : ℝ)
              * Work.BoseBoxFix.normB v μ n Φ)
    (harith : ∀ {μ : ℝ}, 0 < μ → Work.BoseBoxFix.Adm v ε₀ μ → 2 * R ≤ ellH v μ →
      8 * C₁ * (1 + (ellH v μ) ^ (-3 : ℤ)) * (1 + (chKappa v μ) ^ (2 * 19))
        * ((chKappa v μ * ellH v μ)⁻¹) ^ (2 * 19 - 3)
        * (μ * (ellH v μ) ^ (9 / 2 : ℝ)) ≤ K0 * BoseGases.a v) :
    Work.BoseBoxFock.SlotPiece v h fc fu R J ε₀
      (fun n μ N i j Θ => chDimg v h fc fu μ N i j Θ) := by
  classical
  let b1 : ℝ → ℝ := fun μ => C₁ * (1 + (chKappa v μ) ^ (2 * 19))
      * ((chKappa v μ * ellH v μ)⁻¹) ^ (2 * 19 - 3) * (ellH v μ) ^ (3 / 2 : ℝ)
  let b2 : ℝ → ℝ := fun μ => K0 * (μ * BoseGases.a v)
      / (8 * μ ^ 2 * (ellH v μ) ^ 3 * (1 + (ellH v μ) ^ (-3 : ℤ)))
  let A : ℝ → ℝ := fun μ => if 0 < μ then min (b1 μ) (b2 μ) else 0
  have hA : ∀ μ : ℝ, A μ = if 0 < μ then min (b1 μ) (b2 μ) else 0 := fun μ => rfl
  have hb1 : ∀ μ : ℝ, b1 μ = C₁ * (1 + (chKappa v μ) ^ (2 * 19))
      * ((chKappa v μ * ellH v μ)⁻¹) ^ (2 * 19 - 3) * (ellH v μ) ^ (3 / 2 : ℝ) := fun μ => rfl
  have hb2 : ∀ μ : ℝ, b2 μ = K0 * (μ * BoseGases.a v)
      / (8 * μ ^ 2 * (ellH v μ) ^ 3 * (1 + (ellH v μ) ^ (-3 : ℤ))) := fun μ => rfl
  refine ⟨K0, hK0, A, fun _ => 0, ?_, ?_, ?_⟩
  · -- nonnegativity of `A`
    intro μ
    rw [hA μ]
    by_cases hμ : 0 < μ
    · rw [if_pos hμ]
      refine le_min ?_ ?_
      · have hκℓ : 0 < chKappa v μ * ellH v μ := mul_pos (chKappa_pos v hμ hav) (ellH_pos v μ)
        have h1 : (0 : ℝ) ≤ ((chKappa v μ * ellH v μ)⁻¹) ^ (2 * 19 - 3) :=
          pow_nonneg (le_of_lt (inv_pos.mpr hκℓ)) _
        have h2 : (0 : ℝ) ≤ (ellH v μ) ^ (3 / 2 : ℝ) :=
          Real.rpow_nonneg (ellH_pos v μ).le _
        have h3 : (0 : ℝ) ≤ 1 + (chKappa v μ) ^ (2 * 19) := by
          have := pow_nonneg (le_of_lt (chKappa_pos v hμ hav)) (2 * 19)
          linarith
        exact mul_nonneg (mul_nonneg (mul_nonneg hC₁ h3) h1) h2
      · have hℓ : 0 < ellH v μ := ellH_pos v μ
        have h4 : (0 : ℝ) ≤ (ellH v μ) ^ (-3 : ℤ) := by
          simp only [zpow_neg]
          positivity
        have h5 : (0 : ℝ) < 1 + (ellH v μ) ^ (-3 : ℤ) := by linarith
        refine div_nonneg (mul_nonneg hK0.le (mul_nonneg hμ.le hav.le)) ?_
        exact mul_nonneg (by positivity) (by linarith)
    · rw [if_neg hμ]
  · -- the budget clause (equality at the budget-compatible branch)
    intro μ hμ
    rw [hA μ, if_pos hμ]
    have hℓ : 0 < ellH v μ := ellH_pos v μ
    have h4 : (0 : ℝ) ≤ (ellH v μ) ^ (-3 : ℤ) := by
      simp only [zpow_neg]
      positivity
    have h5 : (0 : ℝ) < 1 + (ellH v μ) ^ (-3 : ℤ) := by linarith
    have hX : (0 : ℝ) ≤ 2 * (ellH v μ) ^ (-3 : ℤ) := by linarith
    have hY : (0 : ℝ) ≤ 4 * μ ^ 2 * (ellH v μ) ^ 6 * (1 + (ellH v μ) ^ (-3 : ℤ)) := by
      have h1 : (0 : ℝ) < 4 * μ ^ 2 * (ellH v μ) ^ 6 := by positivity
      nlinarith [h1, h5]
    calc 2 * (ellH v μ) ^ (-3 : ℤ)
          * (4 * μ ^ 2 * (ellH v μ) ^ 6 * (1 + (ellH v μ) ^ (-3 : ℤ)) * min (b1 μ) (b2 μ))
        = 2 * (ellH v μ) ^ (-3 : ℤ)
          * ((4 * μ ^ 2 * (ellH v μ) ^ 6 * (1 + (ellH v μ) ^ (-3 : ℤ))) * min (b1 μ) (b2 μ)) := by
          ring
      _ ≤ 2 * (ellH v μ) ^ (-3 : ℤ)
          * ((4 * μ ^ 2 * (ellH v μ) ^ 6 * (1 + (ellH v μ) ^ (-3 : ℤ))) * b2 μ) := by
          refine mul_le_mul_of_nonneg_left ?_ hX
          exact mul_le_mul_of_nonneg_left (min_le_right _ _) hY
      _ = K0 * (μ * BoseGases.a v) := by
          rw [hb2 μ]
          have h6 : (ellH v μ) ^ 6 = ((ellH v μ) ^ 3) ^ 2 := by ring
          rw [show (ellH v μ) ^ (-3 : ℤ) = ((ellH v μ) ^ 3)⁻¹ from by
            rw [zpow_neg (ellH v μ) 3]; norm_num, h6]
          have hL : (ellH v μ) ^ 3 ≠ 0 := pow_ne_zero _ (ne_of_gt hℓ)
          have hL1 : 1 + ((ellH v μ) ^ 3)⁻¹ ≠ 0 := by
            refine ne_of_gt ?_
            have : (0 : ℝ) ≤ ((ellH v μ) ^ 3)⁻¹ := by positivity
            linarith
          field_simp
          ring
  · -- the per-state clause
    intro Nmin _hNmin _hT hreg HM hmono μ hAdm hJ n Φ _hn hnormB _hlowB _hspec i j hij
    rw [hA μ, if_pos hAdm.1]
    obtain ⟨hRℓ, h4R⟩ := hreg μ hAdm
    have h2R : 2 * R ≤ ellH v μ := by linarith
    have hb := hnorm (μ := μ) hAdm.1 hRℓ h2R (HM μ).N n Φ i j hij
    rw [← hb1 μ] at hb
    have hμpos : 0 < μ := hAdm.1
    have hℓ : 0 < ellH v μ := ellH_pos v μ
    have h4 : (0 : ℝ) ≤ (ellH v μ) ^ (-3 : ℤ) := by
      simp only [zpow_neg]
      positivity
    have h5 : (0 : ℝ) < 1 + (ellH v μ) ^ (-3 : ℤ) := by linarith
    have hden : (0 : ℝ) < 8 * μ ^ 2 * (ellH v μ) ^ 3 * (1 + (ellH v μ) ^ (-3 : ℤ)) := by
      have h1 : (0 : ℝ) < 8 * μ ^ 2 * (ellH v μ) ^ 3 := by
        have h2 : (0 : ℝ) < μ ^ 2 := by positivity
        have h3 : (0 : ℝ) < (ellH v μ) ^ 3 := by positivity
        nlinarith [h2, h3]
      nlinarith [h1, h5]
    have hbr : b1 μ ≤ b2 μ := by
      rw [hb1 μ, hb2 μ, le_div_iff₀ hden]
      have h9 : (ellH v μ) ^ (9 / 2 : ℝ)
          = (ellH v μ) ^ (3 / 2 : ℝ) * (ellH v μ) ^ 3 := by
        rw [show (9 / 2 : ℝ) = 3 / 2 + 3 by norm_num, Real.rpow_add hℓ]
        norm_num
      have hkey : (C₁ * (1 + (chKappa v μ) ^ (2 * 19))
            * ((chKappa v μ * ellH v μ)⁻¹) ^ (2 * 19 - 3) * (ellH v μ) ^ (3 / 2 : ℝ))
            * (8 * μ ^ 2 * (ellH v μ) ^ 3 * (1 + (ellH v μ) ^ (-3 : ℤ)))
          = μ * (8 * C₁ * (1 + (ellH v μ) ^ (-3 : ℤ)) * (1 + (chKappa v μ) ^ (2 * 19))
              * ((chKappa v μ * ellH v μ)⁻¹) ^ (2 * 19 - 3)
              * (μ * (ellH v μ) ^ (9 / 2 : ℝ))) := by
        rw [h9]
        ring
      rw [hkey]
      calc μ * (8 * C₁ * (1 + (ellH v μ) ^ (-3 : ℤ)) * (1 + (chKappa v μ) ^ (2 * 19))
              * ((chKappa v μ * ellH v μ)⁻¹) ^ (2 * 19 - 3)
              * (μ * (ellH v μ) ^ (9 / 2 : ℝ)))
          ≤ μ * (K0 * BoseGases.a v) :=
            mul_le_mul_of_nonneg_left (harith hAdm.1 hAdm h2R) hAdm.1.le
        _ = K0 * (μ * BoseGases.a v) := by ring
    have h2 : b1 μ * Work.BoseBoxFix.normB v μ n Φ
        = min (b1 μ) (b2 μ) * Work.BoseBoxFix.normB v μ n Φ := by rw [min_eq_left hbr]
    exact le_trans hb (le_of_eq h2)

end Work.BoseBoxFock.PCFU

namespace Work.BoseBoxFock.PCFU

theorem chDimg_le (v : EuclideanSpace ℝ (Fin 3) → ℝ) (h : Work.UBB.ScatSol v) (hv : 0 ≤ v)
    (hv1 : MeasureTheory.MemLp v 1) (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    (hav : 0 < BoseGases.a v) (fc fu : Work.BoseBoxFix.LowCut) (J ε₀ : ℝ) :
    Work.BoseBoxFock.SlotPiece v h fc fu R J ε₀
      (fun n μ N i j Θ => Work.BoseBoxFock.PCFU.chDimg v h fc fu μ N i j Θ) := by
  classical
  by_cases hε₀ : 0 < ε₀
  · -- the admissible window is nonempty: the two inputs (analytic + arithmetic) close the piece
    obtain ⟨C₁, hC₁0, hC₁⟩ :=
      chDimg_norm_le v h hv hv1 hvrad hR hv_supp hav fc fu 19 (le_refl 19)
    obtain ⟨K0, hK0, hK0bound⟩ :=
      chDimg_arith (M₀ := 19) le_rfl (C := C₁) hC₁0 hav hR hε₀
    refine chDimg_le_of_inputs v h hav hR fc fu J ε₀ hC₁0 hK0 ?_ ?_
    · -- the per-state analytic bound
      intro μ hμ hRℓ h2R N n Φ i j hij
      exact hC₁ hμ hRℓ h2R N n Φ i j hij
    · -- the arithmetic window bound, at the explicit FS parameters
      intro μ hμ hAdm h2R
      exact hK0bound hμ hAdm.2.1 h2R (chKappa_mul_ellH v hμ hav) (ellH_eq_of_pos v hμ hav)
  · -- `ε₀ ≤ 0`: `Adm v ε₀` is empty, so the piece is vacuous (`A = T = 0`, `K0 = 1`)
    refine ⟨1, one_pos, fun _ => 0, fun _ => 0, fun μ => le_refl 0, ?_, ?_⟩
    · intro μ hμ
      have h1 : (0 : ℝ) ≤ μ * BoseGases.a v := mul_nonneg hμ.le hav.le
      simpa using h1
    · intro Nmin _ _ hreg HM _ μ hAdm _ n Φ _ _ _ _ i j hij
      exfalso
      have h1 : 0 < μ * (BoseGases.a v) ^ 3 := by
        have h2 : 0 < μ := hAdm.1
        positivity
      have h2 : μ * (BoseGases.a v) ^ 3 ≤ ε₀ := hAdm.2.1
      linarith

end Work.BoseBoxFock.PCFU
