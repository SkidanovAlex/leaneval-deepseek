import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseBoxFock.PCFU.SlotPieceDefs
import Submission.Work.BoseBoxFock.PCFU.chCimg_key
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseBoxFock.PCFU

open MeasureTheory

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-!
# The `(C)`-channel lattice-image slot `chCimg`

This file closes the piece bound `SlotPiece v h fc fu R J ε₀ (chCimg ·)`.

The mathematics: the `d ≠ 0` lattice `lowKer`-images of the slot are controlled by the pointwise
bound `chiScale_lowKer_image_le fc M` (with the *rescaled* cutoff `κ = (d²ℓ)⁻¹` it reads
`χ_ℓ(b)·‖Σ'_{e≠0} lowKer fc κ (u−b+ℓ•latVec e)‖ ≤ C_M d^{2M}/ℓ³` for `u ∈ acube ℓ`), their
`L¹`-mass over the cube is at most `∫|lowKer fc κ|`, and the `KfrU` frame is localised by the
periodisation `KfrU = ℓ³Σ_d uvSmear(·+ℓd)`.  The arithmetic then chooses
`A μ = CE·16π·(a v)·ℓ³·d^110` on the regime and the explicit `K0` of `chCimgK0`.
-/

set_option maxHeartbeats 1600000

/-- The exponent `M` used for the image smallness (`d^{2M}` in the kernel bound, `d^M` after the
Cauchy–Schwarz square root).  The threshold of the arithmetic is `6M ≥ 655`, i.e. `M ≥ 110`. -/
def chCimgM : ℕ := 110

/-- The bound constant of the slot: `CE·a·ℓ³·d^M` (the `CE` produced by `chCimg_key` already
absorbs the `L¹`-constant `C` of `W1fun`: in the assembly one passes `CE·C`). -/
private noncomputable def chCimgABnd (v : E3 → ℝ) (CE : ℝ) (μ : ℝ) : ℝ :=
  CE * _root_.BoseGases.a v * (ellH v μ) ^ 3
    * ((Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d) ^ chCimgM

/-- The budget allowance for a single slot piece. -/
private noncomputable def chCimgAllow (v : E3 → ℝ) (K0 : ℝ) (μ : ℝ) : ℝ :=
  K0 * (μ * _root_.BoseGases.a v)
    / (2 * (ellH v μ) ^ (-3 : ℤ)
        * (4 * μ ^ 2 * (ellH v μ) ^ 6 * (1 + (ellH v μ) ^ (-3 : ℤ))))

/-- The explicit `K0`: it dominates `8·CE·μ ℓ⁶ d^110 (1+ℓ⁻³)` on the regime `2R ≤ ℓ`
(there `t = μa³ ≤ (a/(2R))^{323/163}`, and the quantity is monotone in `t`). -/
private noncomputable def chCimgK0 (v : E3 → ℝ) (R CE : ℝ) : ℝ :=
  8 * CE
      * (_root_.BoseGases.a v ^ 3 * ((_root_.BoseGases.a v / (2 * R)) ^ ((5 : ℝ) / 163))
        + ((_root_.BoseGases.a v / (2 * R)) ^ ((494 : ℝ) / 163)))
    + 1

/-- `A μ`: on the regime it is the bound constant, otherwise the (smaller) budget allowance
(guarded by `max · 0` so that `A μ ≥ 0` for *every* real `μ`). -/
private noncomputable def chCimgA (v : E3 → ℝ) (R CE K0 : ℝ) (μ : ℝ) : ℝ :=
  if R ≤ ellH v μ * Submission.BoseGases.chiR0 ∧ 2 * R ≤ ellH v μ then
    chCimgABnd v CE μ
  else min (chCimgABnd v CE μ) (max (chCimgAllow v K0 μ) 0)

/-- `ℓ = sideAt μ (a v) = a·t^{-163/323}` at `μ > 0`, `a > 0`. -/
private lemma chCimg_ellH_eq {v : E3 → ℝ} {μ : ℝ} (hav : 0 < _root_.BoseGases.a v)
    (hμ : 0 < μ) :
    ellH v μ
      = _root_.BoseGases.a v * Work.BoseBox.fsXp (μ * (_root_.BoseGases.a v) ^ 3) (-163) := by
  have h : 0 < Work.BoseBox.sideAt μ (_root_.BoseGases.a v) := Work.BoseBox.sideAt_pos hμ hav
  rw [ellH, if_pos h, Work.BoseFixB1.sideAt_eq_fsXp hav hμ]

/-- On the regime `2R ≤ ℓ`, the diluteness is bounded by `(a/(2R))^{323/163}`. -/
private lemma chCimg_t_le {v : E3 → ℝ} {R μ : ℝ} (hav : 0 < _root_.BoseGases.a v) (hμ : 0 < μ)
    (hR : 0 < R) (hreg : 2 * R ≤ ellH v μ) :
    μ * (_root_.BoseGases.a v) ^ 3 ≤ (_root_.BoseGases.a v / (2 * R)) ^ ((323 : ℝ) / 163) := by
  set a := _root_.BoseGases.a v with ha
  set t := μ * a ^ 3 with ht
  have ha0 : 0 < a := hav
  have ht0 : 0 < t := by rw [ht]; positivity
  rw [chCimg_ellH_eq hav hμ] at hreg
  have h2 : 2 * R / a ≤ t ^ (-(163 : ℝ) / 323) := by
    have h1 : 2 * R ≤ t ^ (-(163 : ℝ) / 323) * a := by
      have := hreg
      rw [Work.BoseBox.fsXp] at this
      linarith [this]
    rw [div_le_iff₀ ha0]
    linarith [h1]
  have h3 : t ^ ((163 : ℝ) / 323) ≤ a / (2 * R) := by
    have h4 : t ^ (-(163 : ℝ) / 323) = (t ^ ((163 : ℝ) / 323))⁻¹ := by
      rw [show -(163 : ℝ) / 323 = -((163 : ℝ) / 323) by ring, Real.rpow_neg ht0.le]
    have h2' : 2 * R / a ≤ (t ^ ((163 : ℝ) / 323))⁻¹ := by rw [← h4]; exact h2
    have h5 := (le_inv_comm₀ (by positivity : (0 : ℝ) < 2 * R / a)
      (Real.rpow_pos_of_pos ht0 _)).mp h2'
    rwa [inv_div] at h5
  have hmm : t = (t ^ ((163 : ℝ) / 323)) ^ ((323 : ℝ) / 163) := by
    rw [← Real.rpow_mul ht0.le]
    norm_num
  rw [hmm]
  refine Real.rpow_le_rpow (Real.rpow_nonneg ht0.le _) h3 ?_
  norm_num

/-- **The budget arithmetic**: on the regime `2R ≤ ℓ` the bound constant `CE·16π·a·ℓ³·d^110` is
dominated by the allowance `K0·μa/(2ℓ⁻³(4μ²ℓ⁶(1+ℓ⁻³)))` with the explicit `K0 = chCimgK0 v R CE`. -/
private lemma chCimg_budget_arith {v : E3 → ℝ} {R μ CE : ℝ}
    (hav : 0 < _root_.BoseGases.a v) (hμ : 0 < μ) (hR : 0 < R) (hreg : 2 * R ≤ ellH v μ)
    (hCE : 0 ≤ CE) :
    chCimgABnd v CE μ ≤ chCimgAllow v (chCimgK0 v R CE) μ := by
  set a := _root_.BoseGases.a v with ha
  set t := μ * a ^ 3 with ht
  set ℓ := ellH v μ with hℓ
  set d := (Work.BoseBox.paramsAt μ a).d with hd
  set T := (a / (2 * R)) ^ ((323 : ℝ) / 163) with hT
  have ha0 : 0 < a := hav
  have ht0 : 0 < t := by rw [ht]; positivity
  have hℓ0 : 0 < ℓ := by rw [hℓ]; exact ellH_pos v μ
  have h2R : 0 < 2 * R := by linarith
  have hT0 : 0 < T := by rw [hT]; exact Real.rpow_pos_of_pos (by positivity) _
  have hdell : ℓ = a * Work.BoseBox.fsXp t (-163) := by
    rw [hℓ, ht]; exact chCimg_ellH_eq hav hμ
  have hdeq : d = Work.BoseBox.fsXp t 6 := by rw [hd, ht]; exact Work.BoseFixB1.d_eq_fsXp μ a
  have htt : t = Work.BoseBox.fsXp t 323 := Work.BoseBox.delta_eq_fsXp ht0.le
  have htT : t ≤ T := by
    rw [← hT] at *
    exact chCimg_t_le hav hμ hR hreg
  have hF : ∀ c : ℝ, Work.BoseBox.fsXp t c = t ^ (c / 323) := fun c => rfl
  have hℓ6 : ℓ ^ 6 = a ^ 6 * Work.BoseBox.fsXp t (-978) := by
    rw [hdell, mul_pow, Work.BoseBox.fsXp_pow ht0.le]
    norm_num
  have hd110 : d ^ chCimgM = Work.BoseBox.fsXp t 660 := by
    show d ^ 110 = _
    rw [hdeq, Work.BoseBox.fsXp_pow ht0.le]
    norm_num
  have hℓinv : ℓ ^ (-3 : ℤ) = a ^ (-3 : ℤ) * Work.BoseBox.fsXp t 489 := by
    rw [hdell, mul_zpow]
    have h1 : (Work.BoseBox.fsXp t (-163)) ^ (-3 : ℤ) = (Work.BoseBox.fsXp t (-489))⁻¹ := by
      rw [zpow_neg, zpow_ofNat, Work.BoseBox.fsXp_pow ht0.le]
      norm_num
    rw [h1, Work.BoseBox.fsXp_inv ht0]
    norm_num
  have hμeq : μ = t / a ^ 3 := by
    rw [ht]; field_simp
  have hkey : μ * ℓ ^ 6 * d ^ chCimgM * (1 + ℓ ^ (-3 : ℤ))
      = a ^ 3 * Work.BoseBox.fsXp t 5 + Work.BoseBox.fsXp t 494 := by
    have hA : Work.BoseBox.fsXp t (-978) * Work.BoseBox.fsXp t 660
        = Work.BoseBox.fsXp t (-318) := by
      rw [hF (-978), hF 660, hF (-318), ← Real.rpow_add ht0]; norm_num
    have hB : t * Work.BoseBox.fsXp t (-318) = Work.BoseBox.fsXp t 5 := by
      rw [hF (-318), hF 5, ← Real.rpow_one t, ← Real.rpow_mul ht0.le, ← Real.rpow_mul ht0.le]
      rw [← Real.rpow_add ht0]; norm_num
    have hC : Work.BoseBox.fsXp t 5 * Work.BoseBox.fsXp t 489
        = Work.BoseBox.fsXp t 494 := by
      rw [hF 5, hF 489, hF 494, ← Real.rpow_add ht0]; norm_num
    have hD : a ^ (-3 : ℤ) * a ^ 3 = 1 := by
      rw [← zpow_natCast a 3, ← zpow_add₀ (ne_of_gt ha0)]
      norm_num
    have hAeq : t / a ^ 3 * (a ^ 6 * Work.BoseBox.fsXp t (-978))
        * Work.BoseBox.fsXp t 660 = a ^ 3 * Work.BoseBox.fsXp t 5 := by
      have h1 : t / a ^ 3 * (a ^ 6 * Work.BoseBox.fsXp t (-978))
          * Work.BoseBox.fsXp t 660
          = a ^ 3 * (t * (Work.BoseBox.fsXp t (-978) * Work.BoseBox.fsXp t 660)) := by
        field_simp
      rw [h1, hA, hB]
    have hBeq' : a ^ 3 * Work.BoseBox.fsXp t 5 * (a ^ (-3 : ℤ) * Work.BoseBox.fsXp t 489)
        = Work.BoseBox.fsXp t 494 := by
      have h1 : a ^ 3 * Work.BoseBox.fsXp t 5 * (a ^ (-3 : ℤ) * Work.BoseBox.fsXp t 489)
          = (a ^ (-3 : ℤ) * a ^ 3) * (Work.BoseBox.fsXp t 5 * Work.BoseBox.fsXp t 489) := by
        field_simp
      rw [h1, hD, one_mul, hC]
    rw [hℓ6, hd110, hℓinv, hμeq, mul_add, mul_one, hAeq, hBeq']
  have hmono : ∀ {c : ℝ}, 0 ≤ c → Work.BoseBox.fsXp t c ≤ (a / (2 * R)) ^ (c / 163) := by
    intro c hc
    have h1 : Work.BoseBox.fsXp t c ≤ Work.BoseBox.fsXp T c := by
      rw [Work.BoseBox.fsXp, Work.BoseBox.fsXp]
      exact Real.rpow_le_rpow ht0.le htT (by positivity)
    have h2 : Work.BoseBox.fsXp T c = (a / (2 * R)) ^ (c / 163) := by
      rw [hT, Work.BoseBox.fsXp, ← Real.rpow_mul (by positivity : (0 : ℝ) ≤ a / (2 * R))]
      congr 1
      ring
    exact h1.trans (le_of_eq h2)
  have hF5 : Work.BoseBox.fsXp t 5 ≤ (a / (2 * R)) ^ ((5 : ℝ) / 163) := hmono (by norm_num)
  have hF494 : Work.BoseBox.fsXp t 494 ≤ (a / (2 * R)) ^ ((494 : ℝ) / 163) :=
    hmono (by norm_num)
  have hz : ℓ ^ (-3 : ℤ) = (ℓ ^ 3)⁻¹ := by
    rw [show (-3 : ℤ) = -((3 : ℕ) : ℤ) by norm_num, zpow_neg, zpow_natCast]
  have hDpos : 0 < 2 * ℓ ^ (-3 : ℤ) * (4 * μ ^ 2 * ℓ ^ 6 * (1 + ℓ ^ (-3 : ℤ))) := by
    rw [hz]
    have h1 : (0 : ℝ) < (ℓ ^ 3)⁻¹ := by positivity
    have h2 : (0 : ℝ) < 1 + (ℓ ^ 3)⁻¹ := by linarith
    positivity
  rw [chCimgABnd, chCimgAllow, chCimgK0]
  rw [le_div_iff₀ hDpos, hz]
  have hEq : CE * a * ℓ ^ 3 * d ^ chCimgM
        * (2 * (ℓ ^ 3)⁻¹ * (4 * μ ^ 2 * ℓ ^ 6 * (1 + (ℓ ^ 3)⁻¹)))
      = 8 * CE * a * μ * (μ * ℓ ^ 6 * d ^ chCimgM * (1 + (ℓ ^ 3)⁻¹)) := by
    field_simp
    ring
  rw [hEq]
  rw [hz] at hkey
  have hstep : 8 * CE * a * μ * (μ * ℓ ^ 6 * d ^ chCimgM * (1 + (ℓ ^ 3)⁻¹))
      ≤ 8 * CE * a * μ
          * (a ^ 3 * (a / (2 * R)) ^ ((5 : ℝ) / 163)
            + (a / (2 * R)) ^ ((494 : ℝ) / 163)) := by
    rw [hkey]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    linarith [mul_le_mul_of_nonneg_left hF5 (by positivity : (0 : ℝ) ≤ a ^ 3), hF494]
  have hfinal : 8 * CE * a * μ
        * (a ^ 3 * (a / (2 * R)) ^ ((5 : ℝ) / 163)
          + (a / (2 * R)) ^ ((494 : ℝ) / 163))
      ≤ (8 * CE
            * (a ^ 3 * ((a / (2 * R)) ^ ((5 : ℝ) / 163))
              + ((a / (2 * R)) ^ ((494 : ℝ) / 163)))
          + 1) * (μ * a) := by
    nlinarith [mul_nonneg hCE ha0.le,
      Real.rpow_pos_of_pos (by positivity : (0 : ℝ) < a / (2 * R)) ((5 : ℝ) / 163),
      Real.rpow_pos_of_pos (by positivity : (0 : ℝ) < a / (2 * R)) ((494 : ℝ) / 163),
      le_of_lt hR]
  exact le_trans hstep hfinal

/-- The `zpow` in the budget is positive. -/
private lemma chCimg_zpow_pos (v : E3 → ℝ) (μ : ℝ) : (0 : ℝ) < (ellH v μ) ^ (-3 : ℤ) := by
  rw [show (-3 : ℤ) = -((3 : ℕ) : ℤ) by norm_num, zpow_neg, zpow_natCast]
  exact inv_pos.mpr (pow_pos (ellH_pos v μ) 3)

/-- The other factor of the budget is nonnegative. -/
private lemma chCimg_four_nonneg (v : E3 → ℝ) (μ : ℝ) :
    0 ≤ 4 * μ ^ 2 * (ellH v μ) ^ 6 * (1 + (ellH v μ) ^ (-3 : ℤ)) := by
  have h6 : 0 ≤ (ellH v μ) ^ 6 := pow_nonneg (le_of_lt (ellH_pos v μ)) 6
  have h2 : 0 < 1 + (ellH v μ) ^ (-3 : ℤ) := by
    have := chCimg_zpow_pos v μ; linarith
  have hsq : (0 : ℝ) ≤ μ ^ 2 := sq_nonneg μ
  exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hsq) h6) (le_of_lt h2)

/-- `K0` is positive. -/
private lemma chCimgK0_pos {v : E3 → ℝ} {R CE : ℝ} (hav : 0 < _root_.BoseGases.a v)
    (hR : 0 < R) (hCE : 0 ≤ CE) : 0 < chCimgK0 v R CE := by
  rw [chCimgK0]
  have h1 : 0 ≤ (8 : ℝ) * CE *
      (_root_.BoseGases.a v ^ 3 * ((_root_.BoseGases.a v / (2 * R)) ^ ((5 : ℝ) / 163))
        + ((_root_.BoseGases.a v / (2 * R)) ^ ((494 : ℝ) / 163))) := by
    refine mul_nonneg (mul_nonneg (by norm_num) hCE) ?_
    refine add_nonneg ?_ ?_
    · exact mul_nonneg (by positivity) (Real.rpow_nonneg (by positivity) _)
    · exact Real.rpow_nonneg (by positivity) _
  linarith

/-- **The budget clause**: if `A μ` is dominated by the allowance, the budget of
`SlotPieceBound` holds. -/
private lemma chCimg_budget_clause {v : E3 → ℝ} {R CE K0 μ : ℝ} (hμ : 0 < μ)
    (hle : chCimgA v R CE K0 μ ≤ chCimgAllow v K0 μ) :
    2 * (ellH v μ) ^ (-3 : ℤ)
        * (4 * μ ^ 2 * (ellH v μ) ^ 6 * (1 + (ellH v μ) ^ (-3 : ℤ))
            * chCimgA v R CE K0 μ)
      ≤ K0 * (μ * _root_.BoseGases.a v) := by
  have h1 := mul_le_mul_of_nonneg_left hle (chCimg_four_nonneg v μ)
  have hz0pos : (0 : ℝ) < 2 * (ellH v μ) ^ (-3 : ℤ) :=
    mul_pos (by norm_num : (0 : ℝ) < 2) (chCimg_zpow_pos v μ)
  have h2 := mul_le_mul_of_nonneg_left h1 hz0pos.le
  refine le_trans h2 (le_of_eq ?_)
  have hDpos : 0 < 2 * (ellH v μ) ^ (-3 : ℤ)
      * (4 * μ ^ 2 * (ellH v μ) ^ 6 * (1 + (ellH v μ) ^ (-3 : ℤ))) := by
    have h1 : (0 : ℝ) < 2 := by norm_num
    have h2 : (0 : ℝ) < (ellH v μ) ^ (-3 : ℤ) := chCimg_zpow_pos v μ
    have h3 : (0 : ℝ) < μ ^ 2 := pow_pos hμ 2
    have h4 : (0 : ℝ) < (ellH v μ) ^ 6 := pow_pos (ellH_pos v μ) 6
    have h5 : (0 : ℝ) < 1 + (ellH v μ) ^ (-3 : ℤ) := by linarith
    positivity
  rw [chCimgAllow]
  have hDne : 2 * (ellH v μ) ^ (-3 : ℤ)
      * (4 * μ ^ 2 * (ellH v μ) ^ 6 * (1 + (ellH v μ) ^ (-3 : ℤ))) ≠ 0 := ne_of_gt hDpos
  rw [show 2 * (ellH v μ) ^ (-3 : ℤ)
        * (4 * μ ^ 2 * (ellH v μ) ^ 6 * (1 + (ellH v μ) ^ (-3 : ℤ))
          * (K0 * (μ * _root_.BoseGases.a v)
            / (2 * (ellH v μ) ^ (-3 : ℤ)
              * (4 * μ ^ 2 * (ellH v μ) ^ 6 * (1 + (ellH v μ) ^ (-3 : ℤ))))))
      = (K0 * (μ * _root_.BoseGases.a v)
            / (2 * (ellH v μ) ^ (-3 : ℤ)
              * (4 * μ ^ 2 * (ellH v μ) ^ 6 * (1 + (ellH v μ) ^ (-3 : ℤ)))))
        * (2 * (ellH v μ) ^ (-3 : ℤ)
            * (4 * μ ^ 2 * (ellH v μ) ^ 6 * (1 + (ellH v μ) ^ (-3 : ℤ)))) from by ring]
  exact div_mul_cancel₀ _ hDne

/-- `A μ` is nonnegative for **every** real `μ`. -/
private lemma chCimgA_nonneg {v : E3 → ℝ} {R CE K0 : ℝ} (hav : 0 < _root_.BoseGases.a v)
    (hCE : 0 ≤ CE) (μ : ℝ) : 0 ≤ chCimgA v R CE K0 μ := by
  have hdnn : 0 ≤ ((Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d) ^ chCimgM := by
    have h : ((Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d) ^ chCimgM
        = (((Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d) ^ 55) ^ 2 := by
      rw [show chCimgM = 110 by rfl, show (110 : ℕ) = 55 * 2 by norm_num, pow_mul]
    rw [h]
    exact sq_nonneg _
  have hAB : 0 ≤ chCimgABnd v CE μ := by
    rw [chCimgABnd]
    exact mul_nonneg (mul_nonneg (mul_nonneg hCE (le_of_lt hav))
      (pow_nonneg (le_of_lt (ellH_pos v μ)) 3)) hdnn
  rw [chCimgA]
  split_ifs with hc
  · exact hAB
  · exact le_min hAB (le_max_right _ _)

theorem chCimg_le (v : EuclideanSpace ℝ (Fin 3) → ℝ) (h : Work.UBB.ScatSol v) (hv : 0 ≤ v)
    (hv1 : MeasureTheory.MemLp v 1) (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    (hav : 0 < BoseGases.a v) (fc fu : Work.BoseBoxFix.LowCut) (J ε₀ : ℝ) :
    Work.BoseBoxFock.SlotPiece v h fc fu R J ε₀
      (fun n μ N i j Θ => Work.BoseBoxFock.PCFU.chCimg v h fc fu μ N i j Θ) := by
  have _ := hv1
  obtain ⟨CE, hCE0, hKEY⟩ := chCimg_key v h hv hvrad hR hv_supp hav fc fu
  obtain ⟨hW1C, hW1C0, hW1⟩ :=
    Work.BoseBoxFock.W1fun_L1_le v h hv hvrad hR hv_supp
  have ha0 : 0 ≤ _root_.BoseGases.a v := le_of_lt hav
  have hCE'0 : 0 ≤ CE * hW1C := mul_nonneg hCE0 hW1C0
  refine ⟨chCimgK0 v R (CE * hW1C), chCimgK0_pos hav hR hCE'0,
    chCimgA v R (CE * hW1C) (chCimgK0 v R (CE * hW1C)), fun _ => 0, ?_, ?_, ?_⟩
  · -- `0 ≤ A μ`
    intro μ
    exact chCimgA_nonneg hav hCE'0 μ
  · -- the budget
    intro μ hμ
    refine chCimg_budget_clause hμ ?_
    rw [chCimgA]
    split_ifs with hc
    · exact chCimg_budget_arith hav hμ hR hc.2 hCE'0
    · refine le_trans (min_le_right _ _) ?_
      rw [max_eq_left]
      refine div_nonneg (mul_nonneg (chCimgK0_pos hav hR hCE'0).le
        (mul_nonneg (le_of_lt hμ) ha0)) ?_
      exact mul_nonneg (mul_nonneg (by norm_num) (le_of_lt (chCimg_zpow_pos v μ)))
        (chCimg_four_nonneg v μ)
  · -- the state bound
    intro Nmin hNth hT hreg HM hMono μ hAdm hJ n Φ hn hnorm hlowB _hspec i j hij
    obtain ⟨hreg1, hreg4⟩ := hreg μ hAdm
    have hreg2 : 2 * R ≤ ellH v μ := by linarith
    obtain ⟨hμ0, _, _⟩ := hAdm
    -- `1 ≤ (HM μ).N`
    have hN1 : 1 ≤ (HM μ).N := by
      refine le_trans ?_ (le_trans (hNth μ) (hMono μ))
      have h2 : (2 : ℝ) ≤ chNThresh v μ := by
        rw [chNThresh]
        have h3 : 0 ≤ 4 * ((Work.BoseBox.paramsAt μ (BoseGases.a v)).d ^ 2 * ellH v μ)⁻¹
            * ellH v μ / (2 * Real.pi) := by
          refine div_nonneg (mul_nonneg (mul_nonneg (by norm_num) ?_)
            (le_of_lt (ellH_pos v μ))) (by positivity)
          exact inv_nonneg.mpr (mul_nonneg (sq_nonneg _) (le_of_lt (ellH_pos v μ)))
        linarith
      have h3 : (1 : ℝ) ≤ (⌈chNThresh v μ⌉₊ : ℝ) :=
        le_trans (by norm_num) (le_trans h2 (Nat.le_ceil _))
      exact_mod_cast h3
    -- the analytic bound
    have hraw := hKEY hμ0 hN1 hreg1 hreg2 i j hij Φ
    have hw₁ : (∫ x : E3, |Work.BoseFixR.W1fun v h (ellH v μ) x|)
        ≤ hW1C * _root_.BoseGases.a v := hW1 _ hreg1
    have hnormnn : 0 ≤ Work.BoseBoxFix.normB v μ n Φ := by
      rw [Work.BoseBoxFix.normB, Work.BoseKinLoc.sqNormB]
      exact integral_nonneg (fun x => by positivity)
    have hdnn : 0 ≤ ((Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d) ^ chCimgM := by
      have h : ((Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d) ^ chCimgM
          = (((Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d) ^ 55) ^ 2 := by
        rw [show chCimgM = 110 by rfl, show (110 : ℕ) = 55 * 2 by norm_num, pow_mul]
      rw [h]
      exact sq_nonneg _
    have hℓ3nn : 0 ≤ (ellH v μ) ^ 3 := pow_nonneg (le_of_lt (ellH_pos v μ)) 3
    have hbound : CE * (ellH v μ) ^ 3
          * (∫ x : E3, |Work.BoseFixR.W1fun v h (ellH v μ) x|)
          * ((Work.BoseBox.paramsAt μ (BoseGases.a v)).d) ^ chCimgM
          * Work.BoseBoxFix.normB v μ n Φ
        ≤ chCimgABnd v (CE * hW1C) μ * Work.BoseBoxFix.normB v μ n Φ := by
      rw [chCimgABnd]
      have h2 : CE * (ellH v μ) ^ 3 * (∫ x : E3, |Work.BoseFixR.W1fun v h (ellH v μ) x|)
          ≤ CE * (hW1C * _root_.BoseGases.a v) * (ellH v μ) ^ 3 := by
        have h3 := mul_le_mul_of_nonneg_left hw₁ (mul_nonneg hCE0 hℓ3nn)
        linarith [h3]
      have h4 : CE * (ellH v μ) ^ 3 * (∫ x : E3, |Work.BoseFixR.W1fun v h (ellH v μ) x|)
            * ((Work.BoseBox.paramsAt μ (BoseGases.a v)).d) ^ chCimgM
          ≤ (CE * hW1C) * _root_.BoseGases.a v * (ellH v μ) ^ 3
              * ((Work.BoseBox.paramsAt μ (BoseGases.a v)).d) ^ chCimgM := by
        refine le_trans (mul_le_mul_of_nonneg_right h2 hdnn) ?_
        exact le_of_eq (by ring)
      exact mul_le_mul_of_nonneg_right h4 hnormnn
    rw [chCimgA, if_pos ⟨hreg1, hreg2⟩]
    exact le_trans hraw hbound

end Work.BoseBoxFock.PCFU
