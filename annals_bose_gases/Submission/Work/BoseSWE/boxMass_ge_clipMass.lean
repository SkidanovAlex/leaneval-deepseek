import ChallengeDeps
import Submission.Work.BoseSWE.Defs
import Submission.Work.BoseSWE.chiSmallB_eq_zero_of_two_clip
import Submission.Work.BoseSWE.prod_shortSide_ge
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseSWE.boxMass_ge_clipMass` — the clipping geometry of a sliding box

The per-box statement of the `BoseSWE` route is used on the *good set*
`u ∈ goodSet ℓ d μ` (`‖(ℓd)•u‖_∞ ≤ ½ℓ(1+d) − μ^{-1/3}`) of the sliding localisation, and on that
set the box `B(u) = dlBox ℓ d u = acube ℓ ∩ ((ℓd)•u + acube (ℓd))` is guaranteed to be *large*,
`μ·|B(u)| ≥ 1000`, once the diluteness `μ(a v)³` is small.  That is the third conjunct of
`Work.BoseSWE.Regular` (`1000 ≤ μ · bV v μ u`), the box-size hypothesis of FS `thm:smallbox`.

This file proves it (`boxMass_ge_clipMass`).  The ingredients are

* `Work.BoseFixB1S.oneBodyB1.sqrtW.boxMassProdB1` — `|B(u)| = ∏_j max 0 (shortSide ℓ d u j)`
  (valid for `0 < d ≤ 1`), where
  `shortSide ℓ d u j = min (ℓd) (½ℓ(1+d) − |((ℓd)•u)_j|)` is the length of the `j`-th coordinate
  interval of `B(u)`; the box is *clipped* in the coordinate `j` exactly when
  `shortSide ℓ d u j < ℓd`;
* `Work.SmallBoxSliding.goodSet_shortSide` — on the good set every side is at least `μ^{-1/3}`
  (in the regime `μ^{-1/3} ≤ ℓd`, which holds at FS's parameters, `Regime.sideAt_mul_d_ge`);
* `Work.BoseSWE.chiSmallB_eq_zero_of_two_clip` — **two** clipped coordinates force the sliding
  cutoff `chiSmallB M ℓ d u` to vanish identically: `chiSmallB ≠ 0` forces `‖x‖ < ℓ/2` (the
  `χ(x/ℓ)` factor is the ball-supported corpus bump) and `|x_i − ((ℓd)•u)_i| ≤ ℓd/2`, so two clipped
  coordinates give `‖x‖² > 2(ℓ/2 − ℓd)² ≥ ℓ²/4` once `8d ≤ 1`.  Hence `0 < chiMass M ℓ d u`
  (which is `∫ (chiSmallB)² > 0`) implies that *at most one* side is clipped;
* `Work.BoseSWE.prod_shortSide_ge` — therefore `|B(u)| ≥ (ℓd)² μ^{-1/3}`: two sides are exactly
  `ℓd`, the third is at least `μ^{-1/3}`;
* `clipMass_arith` (below) — the diluteness arithmetic: for `μ(a v)³ ≤ 2^{-323}` the small-box
  parameter is tiny (`d ≤ 1/8`) and `μ·(ℓd)²μ^{-1/3} = (μ(ℓd)³)^{2/3} ≥ (2^{148})^{2/3} ≥ 1000`,
  where `μ(ℓd)³ = (μ(a v)³)^{-148/323}`.

-/

noncomputable section

open MeasureTheory Metric Filter
open scoped Topology Real BigOperators ENNReal

namespace Work.BoseSWE

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## 1. The diluteness arithmetic -/

/-- `2^{-323} ≤ 1`: the diluteness threshold used below. -/
lemma two_rpow_neg_le_one : ((2 : ℝ) ^ ((-323 : ℝ))) ≤ 1 := by
  have h : (2 : ℝ) ^ ((-323 : ℝ)) ≤ (2 : ℝ) ^ ((0 : ℝ)) :=
    (Real.rpow_le_rpow_left_iff (by norm_num : (1 : ℝ) < 2)).mpr (by norm_num)
  rwa [Real.rpow_zero] at h

/-- **The diluteness arithmetic of the clipping bound.**  At FS's parameters
(`d = (μa³)^{6/323}`, `ℓ·d = a(μa³)^{-157/323}`, so `μ(ℓd)³ = (μa³)^{-148/323}`), diluteness
`μa³ ≤ 2^{-323}` gives

* `d ≤ 1/8` — the small-box parameter is tiny (so `8d ≤ 1`, the hypothesis of the two-clip
  geometry), and
* `1000 ≤ μ (ℓd)² μ^{-1/3} = (μ(ℓd)³)^{2/3} ≥ (2^{148})^{2/3} ≥ 1000`. -/
lemma clipMass_arith {a μ : ℝ} (ha : 0 < a) (hμ : 0 < μ)
    (ht : μ * a ^ 3 ≤ (2 : ℝ) ^ ((-323 : ℝ))) :
    (Work.BoseBox.paramsAt μ a).d ≤ 1 / 8 ∧
      1000 ≤ μ * (Work.BoseBox.sideAt μ a * (Work.BoseBox.paramsAt μ a).d) ^ 2
        * μ ^ (-(1 / 3 : ℝ)) := by
  have ht0 : (0 : ℝ) < μ * a ^ 3 := by positivity
  constructor
  · -- `d = (μa³)^{6/323} ≤ (2^{-323})^{6/323} = 2^{-6} = 1/64 ≤ 1/8`
    rw [Work.BoseFixB1.d_eq_fsXp]
    have h1 : Work.BoseBox.fsXp (μ * a ^ 3) 6 ≤ Work.BoseBox.fsXp ((2 : ℝ) ^ ((-323 : ℝ))) 6 := by
      rw [Work.BoseBox.fsXp, Work.BoseBox.fsXp]
      exact Real.rpow_le_rpow ht0.le ht (by norm_num)
    refine le_trans h1 ?_
    rw [Work.BoseBox.fsXp]
    have h2 : ((2 : ℝ) ^ ((-323 : ℝ))) ^ ((6 : ℝ) / 323) = (2 : ℝ) ^ ((-6 : ℝ)) := by
      rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
      norm_num
    rw [h2, show (-6 : ℝ) = -((6 : ℕ) : ℝ) by norm_num,
      Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), Real.rpow_natCast]
    norm_num
  · -- `μ(ℓd)³ ≥ 2^{148}`, then `(μ^{2/3}(ℓd)²)³ = (μ(ℓd)³)² ≥ (2^{148})² = 2^{296} ≥ 1000³`
    have hcube : (2 : ℝ) ^ (148 : ℝ)
        ≤ μ * (Work.BoseBox.sideAt μ a * (Work.BoseBox.paramsAt μ a).d) ^ 3 := by
      have h := Work.BoseFixB1.mu_d_mul_sideAt_cube_eq (A := a) (μ := μ) ha hμ
      rw [mul_comm (Work.BoseBox.paramsAt μ a).d (Work.BoseBox.sideAt μ a)] at h
      rw [h]
      rw [show Work.BoseBox.fsXp (μ * a ^ 3) (-148) = (μ * a ^ 3) ^ ((-148 : ℝ) / 323)
        from rfl]
      show (2 : ℝ) ^ (148 : ℝ) ≤ (μ * a ^ 3) ^ ((-148 : ℝ) / 323)
      have h2 : ((2 : ℝ) ^ ((-323 : ℝ))) ^ ((-148 : ℝ) / 323)
          ≤ (μ * a ^ 3) ^ ((-148 : ℝ) / 323) :=
        Real.rpow_le_rpow_of_nonpos ht0 ht (by norm_num)
      have h3 : ((2 : ℝ) ^ ((-323 : ℝ))) ^ ((-148 : ℝ) / 323) = (2 : ℝ) ^ (148 : ℝ) := by
        rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
        norm_num
      rw [← h3]
      exact h2
    set s : ℝ := Work.BoseBox.sideAt μ a * (Work.BoseBox.paramsAt μ a).d with hsdef
    have hs : 0 < s := mul_pos (Work.BoseBox.sideAt_pos hμ ha) (by
      rw [Work.BoseFixB1.d_eq_fsXp]; exact Work.BoseBox.fsXp_pos ht0)
    have hμ1 : μ * μ ^ (-(1 / 3 : ℝ)) = μ ^ ((2 : ℝ) / 3) := by
      calc μ * μ ^ (-(1 / 3 : ℝ)) = μ ^ 1 * μ ^ (-(1 / 3 : ℝ)) := by rw [Real.rpow_one]
        _ = μ ^ (1 + -(1 / 3 : ℝ)) := (Real.rpow_add hμ 1 (-(1 / 3 : ℝ))).symm
        _ = μ ^ ((2 : ℝ) / 3) := by norm_num
    have h1 : μ * s ^ 2 * μ ^ (-(1 / 3 : ℝ)) = (μ * s ^ 3) ^ ((2 : ℝ) / 3) := by
      have hLs : (s ^ 3 : ℝ) = s ^ (3 : ℝ) := (Real.rpow_natCast s 3).symm
      rw [hLs, Real.mul_rpow hμ.le (Real.rpow_nonneg hs.le 3), ← Real.rpow_mul hs.le]
      rw [show μ * s ^ 2 * μ ^ (-(1 / 3 : ℝ)) = (μ * μ ^ (-(1 / 3 : ℝ))) * s ^ 2 by ring, hμ1]
      norm_num
    rw [h1]
    have h2 : ((2 : ℝ) ^ (148 : ℝ)) ^ ((2 : ℝ) / 3) ≤ (μ * s ^ 3) ^ ((2 : ℝ) / 3) :=
      Real.rpow_le_rpow (by positivity) hcube (by norm_num)
    have h3 : ((2 : ℝ) ^ (148 : ℝ)) ^ ((2 : ℝ) / 3) = (2 : ℝ) ^ ((296 : ℝ) / 3) := by
      rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
      norm_num
    rw [h3] at h2
    have h4 : (1000 : ℝ) ≤ (2 : ℝ) ^ ((296 : ℝ) / 3) := by
      have h10 : (2 : ℝ) ^ (10 : ℝ) ≤ (2 : ℝ) ^ ((296 : ℝ) / 3) :=
        (Real.rpow_le_rpow_left_iff (by norm_num : (1 : ℝ) < 2)).mpr (by norm_num)
      have h1000 : (1000 : ℝ) ≤ (2 : ℝ) ^ (10 : ℝ) := by norm_num
      linarith
    linarith

/-! ## 2. The clipping geometry at general parameters -/

/-- **The clipping geometry.**  Let `0 < μ`, `0 < ℓ`, `0 < d ≤ 1`, `μ^{-1/3} ≤ ℓd` (so that on the
good set every side of `B(u)` is at least `μ^{-1/3}`, `goodSet_shortSide`) and `8d ≤ 1`.  If the
sliding cutoff has positive `χ`-mass, then at most one coordinate of `B(u)` is clipped
(`chiSmallB_eq_zero_of_two_clip`), so `|B(u)| ≥ (ℓd)²μ^{-1/3}` (`prod_shortSide_ge` +
`boxMassProdB1`), and the arithmetic bound `1000 ≤ μ(ℓd)²μ^{-1/3}` finishes. -/
lemma boxMass_ge_of_clip {M : ℕ} (hM : 1 ≤ M) {μ ℓ d : ℝ}
    (hμ : 0 < μ) (hℓpos : 0 < ℓ) (hdpos : 0 < d) (hd1 : d ≤ 1)
    (hreg : μ ^ (-(1 / 3 : ℝ)) ≤ ℓ * d) (hd8 : 8 * d ≤ 1) {u : E3}
    (hu : u ∈ Work.SmallBoxSliding.goodSet ℓ d μ)
    (hchi : 0 < Work.SmallBoxSliding.chiMass M ℓ d u)
    (hnum : 1000 ≤ μ * (ℓ * d) ^ 2 * μ ^ (-(1 / 3 : ℝ))) :
    1000 ≤ μ * Work.SmallBoxSliding.boxMass ℓ d u := by
  -- no two coordinates are clipped
  have hnotwo : ¬ ∃ j j' : Fin 3, j ≠ j' ∧
      Work.SmallBoxSliding.shortSide ℓ d u j < ℓ * d ∧
      Work.SmallBoxSliding.shortSide ℓ d u j' < ℓ * d := by
    rintro ⟨j, j', hne, h1, h2⟩
    have hzero : Work.SmallBoxSliding.chiMass M ℓ d u = 0 := by
      have hfun : ∀ x : E3, Submission.BoseGases.chiSmallB M ℓ d u x = 0 :=
        fun x => chiSmallB_eq_zero_of_two_clip hM hℓpos hdpos hd8 ⟨j, j', hne, h1, h2⟩
      simp only [Work.SmallBoxSliding.chiMass]
      simp [hfun]
    linarith
  -- the volume bound.  (`-(1/3)` and `-1/3` are the same real number but not the same term, so the
  -- regime hypothesis is transported across `hexp` for `goodSet_shortSide`.)
  have hexp : μ ^ (-1 / 3 : ℝ) = μ ^ (-(1 / 3 : ℝ)) := by norm_num
  have hreg' : μ ^ (-1 / 3 : ℝ) ≤ ℓ * d := by rw [hexp]; exact hreg
  have hside₁ : ∀ j : Fin 3, μ ^ (-1 / 3 : ℝ) ≤ Work.SmallBoxSliding.shortSide ℓ d u j :=
    fun j => Work.SmallBoxSliding.goodSet_shortSide hreg' hu j
  have hside : ∀ j : Fin 3, μ ^ (-(1 / 3 : ℝ)) ≤ Work.SmallBoxSliding.shortSide ℓ d u j :=
    fun j => by rw [← hexp]; exact hside₁ j
  have hvol : (ℓ * d) ^ 2 * μ ^ (-(1 / 3 : ℝ)) ≤ Work.SmallBoxSliding.boxMass ℓ d u := by
    rw [Work.BoseFixB1S.oneBodyB1.sqrtW.boxMassProdB1 hℓpos hdpos hd1 u]
    exact prod_shortSide_ge hμ (mul_pos hℓpos hdpos) hreg hside hnotwo
  calc 1000 ≤ μ * (ℓ * d) ^ 2 * μ ^ (-(1 / 3 : ℝ)) := hnum
    _ = μ * ((ℓ * d) ^ 2 * μ ^ (-(1 / 3 : ℝ))) := by ring
    _ ≤ μ * Work.SmallBoxSliding.boxMass ℓ d u := mul_le_mul_of_nonneg_left hvol hμ.le

/-! ## 3. The target -/

/-- **The clipping geometry: a massive box has `μ·|B(u)| ≥ 1000`.**

If the sliding cutoff has positive `χ`-mass (`0 < chiMass M ℓ d u`), then the box `B(u)=dlBox ℓ d u`
meets the support ball of the `ℓ`-scale factor, `ball 0 (ℓ/2)`; since the box's shortest side is
`≥ μ^{-1/3}` on `goodSet` (`Work.SmallBoxSliding.goodSet_shortSide`) and the box has diameter
`√3 ℓd ≪ ℓ/4`, at most one of its three sides can be clipped, so
`|B(u)| = ∏_j max 0 (shortSide ℓ d u j) ≥ μ^{-1/3}·(ℓd)²`
(`Work.BoseFixB1S.oneBodyB1.sqrtW.boxMassProdB1`) and hence `μ·|B(u)| ≥ μ^{2/3}(ℓd)²`, which is
`≥ 1000` once `μ(a v)³ ≤ ε₀` with `ε₀` small (`ℓd = aX^{−157}`, `X = (μa³)^{1/323}`). -/
theorem boxMass_ge_clipMass {v : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hav : 0 < _root_.BoseGases.a v) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
      ∀ u ∈ Work.SmallBoxSliding.goodSet (Work.BoseFixB1.bSide v μ) (Work.BoseFixB1.bD v μ) μ,
        0 < Work.SmallBoxSliding.chiMass (Work.BoseFixB1.bM v μ) (Work.BoseFixB1.bSide v μ)
              (Work.BoseFixB1.bD v μ) u →
        1000 ≤ μ * Work.BoseFixB1.bV v μ u := by
  refine ⟨(2 : ℝ) ^ ((-323 : ℝ)),
    show (0 : ℝ) < (2 : ℝ) ^ ((-323 : ℝ)) by positivity, ?_⟩
  intro μ hAdm u hu hchi
  have hμ : 0 < μ := hAdm.1
  have ht1 : μ * (_root_.BoseGases.a v) ^ 3 ≤ 1 := le_trans hAdm.2.1 two_rpow_neg_le_one
  -- rewrite the (definitional) abbreviations `bSide`, `bD`, `bV` into `sideAt`/`paramsAt`
  have hu' : u ∈ Work.SmallBoxSliding.goodSet (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
      ((Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d) μ := by
    simpa only [Work.BoseFixB1.bSide, Work.BoseFixB1.bD] using hu
  have hchi' : 0 < Work.SmallBoxSliding.chiMass (Work.BoseFixB1.bM v μ)
      (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
      ((Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d) u := by
    simpa only [Work.BoseFixB1.bSide, Work.BoseFixB1.bD] using hchi
  have hM : 1 ≤ Work.BoseFixB1.bM v μ := by
    rw [Work.BoseFixB1.bM, Work.BoseFixB1.M_eq_mValue]
    norm_num [Work.BoseBox.mValue]
  -- the parameter facts
  have hℓpos : 0 < Work.BoseBox.sideAt μ (_root_.BoseGases.a v) :=
    Work.BoseBox.sideAt_pos hμ hav
  have hdpos : 0 < (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d := by
    rw [Work.BoseFixB1.d_eq_fsXp]
    exact Work.BoseBox.fsXp_pos (by positivity)
  have hd1 : (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d ≤ 1 := by
    rw [Work.BoseFixB1.d_eq_fsXp]
    exact Work.BoseBox.fsXp_le_one (by positivity) ht1 (by norm_num)
  have hreg : μ ^ (-(1 / 3 : ℝ))
      ≤ Work.BoseBox.sideAt μ (_root_.BoseGases.a v)
        * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d :=
    Work.BoseFixB1.sideAt_mul_d_ge hav hμ ht1
  obtain ⟨hd8, hnum⟩ := clipMass_arith hav hμ hAdm.2.1
  have hd8' : 8 * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d ≤ 1 := by linarith
  have hmain := boxMass_ge_of_clip hM hμ hℓpos hdpos hd1 hreg hd8' hu' hchi' hnum
  rw [Work.BoseFixB1.bV, Work.BoseFixB1.bSide, Work.BoseFixB1.bD]
  exact hmain

end Work.BoseSWE
