import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseFixB1.boxMass_ge_deltaScale_of_goodSet
import Submission.Work.BoseFixB1S.mfBoxAbbrev
import Submission.Work.BoseFixB1S.mf_boxMass_pos_of_mem_interiorSet
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1S.mfGatesV2B1` — the per-box gates at the sliding box

The twelve elementary facts about an admissible sliding box that the flat-branch
residual `Work.BoseFixB1S.perBoxMeanFieldB1` consumes:

* positivity of `μ`, of the box side `ℓ`, of `d`, of the box mass `mfV = |B(u)|`,
  and the standing small-box hypothesis `1 ≤ μ|B(u)|`;
* the two `R`-bounds (`R ≤ ℓd/16` and `R ≤ ℓ·chiR0`) of the dilution regime;
* `1 ≤ M`, `1 ≤ n` (from `0 < mfQ`), the two one-body mass bounds
  `0 ≤ mfM1 ≤ mfM2` and the pair count `0 ≤ mfPc`.

This is the statement `Work.BoseFixB1S.mfGatesB1` with its (false) thirteenth conjunct
`0 < mfChi v μ u` removed and replaced by `0 ≤ mfPc v μ n Φ u` — see the FINDING in
`mfGatesB1.lean` for why the cutoff gate is false at the corner points of `interiorSet`.

The mathematics is entirely in the corpus: `Work.BoseFixB1.regime_sideAt_ge` (the two
`R`-bounds), `Work.BoseFixB1.Regime.one_le_mu_d_mul_sideAt_cube` +
`Work.BoseFixB1.boxMass_ge_deltaScale_of_goodSet` (`1 ≤ μ|B(u)|` on `interiorSet ⊆ goodSet`),
`Work.BoseFixB1S.mf_boxMass_pos_of_mem_interiorSet`, `Work.BoseFixB1S.boxM1Info`.
-/

namespace Work.BoseFixB1S

open _root_.BoseGases Submission.BoseGases Work.BoseBoxFix Work.BoseBox Work.UBB
open Work.SmallBoxSliding Work.BoseFixB1

set_option autoImplicit false
set_option linter.unusedVariables false

noncomputable section

/-! ## Elementary real-analysis pieces -/

/-- `-(1/3)` and `-1/3` are the same real number, so the two spellings of the exponent
`μ^{-1/3}` used by the corpus (`goodSet` uses one, `boxMass_ge_deltaScale_of_goodSet` the
other) can be converted into each other. -/
lemma rpow_neg_third_eq (μ : ℝ) : μ ^ (-(1 / 3) : ℝ) = μ ^ (-1 / 3 : ℝ) := by
  congr 1
  norm_num

/-- **From `1 ≤ μ x³` to `μ^{-1/3} ≤ x`** (for `x ≥ 0`, `μ > 0`): cube both sides. -/
lemma inv_third_le_of_one_le_mul_cube {μ x : ℝ} (hμ : 0 < μ) (hx : 0 ≤ x)
    (h : 1 ≤ μ * x ^ 3) : μ ^ (-1 / 3 : ℝ) ≤ x := by
  have hx3 : μ⁻¹ ≤ x ^ 3 := by
    refine (inv_le_iff_one_le_mul₀ hμ).mpr ?_
    calc (1 : ℝ) ≤ μ * x ^ 3 := h
      _ = x ^ 3 * μ := by ring
  have hp : (μ⁻¹) ^ ((1 : ℝ) / 3) ≤ (x ^ 3) ^ ((1 : ℝ) / 3) :=
    Real.rpow_le_rpow (inv_nonneg.mpr hμ.le) hx3 (by norm_num)
  have h1 : (μ⁻¹) ^ ((1 : ℝ) / 3) = μ ^ (-1 / 3 : ℝ) := by
    rw [Real.inv_rpow hμ.le, ← Real.rpow_neg hμ.le]
    congr 1
    norm_num
  have h2 : (x ^ 3) ^ ((1 : ℝ) / 3) = x := by
    rw [← Real.rpow_natCast x 3, ← Real.rpow_mul (x := x) hx ((3 : ℕ) : ℝ) ((1 : ℝ) / 3),
      show (((3 : ℕ) : ℝ) * ((1 : ℝ) / 3)) = 1 by norm_num, Real.rpow_one]
  rwa [h1, h2] at hp

/-- **The standing small-box hypothesis `1 ≤ μ|B(u)|`.**  On the interior of the sliding
region the box `B(u) = dlBox ℓ d u` has every side at least `μ^{-1/3}`, hence volume at least
`(μ^{-1/3})³` and `μ|B(u)| ≥ 1`.

Inputs: the regime `1 ≤ μ(ℓd)³` and `d ≤ 1`. -/
lemma one_le_mu_mul_boxMass {μ ℓ d : ℝ} (hμ : 0 < μ) (hℓ : 0 < ℓ) (hd : 0 < d)
    (hd1 : d ≤ 1) (hreg : 1 ≤ μ * (ℓ * d) ^ 3) {u : EuclideanSpace ℝ (Fin 3)}
    (hu : u ∈ interiorSet ℓ d μ) :
    1 ≤ μ * boxMass ℓ d u := by
  have hld : 0 < ℓ * d := mul_pos hℓ hd
  have h13 : μ ^ (-1 / 3 : ℝ) ≤ ℓ * d := inv_third_le_of_one_le_mul_cube hμ hld.le hreg
  have h13' : μ ^ (-(1 / 3) : ℝ) ≤ ℓ * d := by
    rw [rpow_neg_third_eq]; exact h13
  have hvol : (μ ^ (-(1 / 3) : ℝ)) ^ 3 ≤ boxMass ℓ d u :=
    boxMass_ge_deltaScale_of_goodSet hℓ hd hd1 hμ h13' (interiorSet_subset_goodSet hμ hu)
  have hcube : μ * (μ ^ (-1 / 3 : ℝ)) ^ 3 = 1 := by
    rw [← Real.rpow_natCast (μ ^ (-1 / 3 : ℝ)) 3,
      ← Real.rpow_mul (x := μ) hμ.le (-1 / 3) ((3 : ℕ) : ℝ),
      show ((-1 / 3 : ℝ) * ((3 : ℕ) : ℝ)) = -1 by norm_num, Real.rpow_neg_one]
    exact mul_inv_cancel₀ (ne_of_gt hμ)
  have hcube' : μ * (μ ^ (-(1 / 3) : ℝ)) ^ 3 = 1 := by
    rw [rpow_neg_third_eq]; exact hcube
  calc (1 : ℝ) = μ * (μ ^ (-(1 / 3) : ℝ)) ^ 3 := hcube'.symm
    _ ≤ μ * boxMass ℓ d u := mul_le_mul_of_nonneg_left hvol hμ.le

/-- The box pair count is a sum of integrals of squares, hence nonnegative. -/
lemma mfPc_nonneg {v : EuclideanSpace ℝ (Fin 3) → ℝ} (μ : ℝ) (n : ℕ)
    (Φ : Submission.BoseGases.X n → ℝ) (u : EuclideanSpace ℝ (Fin 3)) :
    0 ≤ mfPc v μ n Φ u := by
  simp only [mfPc, Work.BoseFixB1S.boxPairCount]
  exact Finset.sum_nonneg
    (fun p _ => MeasureTheory.integral_nonneg (fun x => sq_nonneg _))

/-- `mfQ` vanishes when there is no slot: for `n = 0` the defining sum is empty. -/
lemma mfQ_eq_zero_of_eq_zero {v : EuclideanSpace ℝ (Fin 3) → ℝ} {μ : ℝ} {n : ℕ}
    {Φ : Submission.BoseGases.X n → ℝ} {u : EuclideanSpace ℝ (Fin 3)} (hn : n = 0) :
    mfQ v μ n Φ u = 0 := by
  subst hn
  rw [Work.BoseFixB1S.mfQ_def, Work.UBBInputs8.cnPlusBoxInd]
  exact Fin.sum_univ_zero _

/-! ## The gates -/

theorem mfGatesV2B1 {v : EuclideanSpace ℝ (Fin 3) → ℝ} {R : ℝ}
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R) (hR0 : 0 < R)
    (hv : 0 ≤ v) (hvrad : _root_.BoseGases.IsRadial v) (hv1 : MeasureTheory.MemLp v 1)
    (h : Work.UBB.ScatSol v) (hav : 0 < _root_.BoseGases.a v) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧
      ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ → ∀ u : EuclideanSpace ℝ (Fin 3),
        u ∈ Work.SmallBoxSliding.interiorSet (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
              (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d μ →
        ∀ {n : ℕ} {Φ : Submission.BoseGases.X n → ℝ},
          0 < mfQ v μ n Φ u →
          0 < μ
            ∧ 0 < Work.BoseBox.sideAt μ (_root_.BoseGases.a v)
            ∧ 0 < (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d
            ∧ 0 < mfV v μ u
            ∧ 1 ≤ μ * mfV v μ u
            ∧ R ≤ Work.BoseBox.sideAt μ (_root_.BoseGases.a v)
                  * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d / 16
            ∧ R ≤ Work.BoseBox.sideAt μ (_root_.BoseGases.a v) * Submission.BoseGases.chiR0
            ∧ 1 ≤ (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
            ∧ 1 ≤ n
            ∧ 0 ≤ mfM1 h μ u
            ∧ mfM1 h μ u ≤ mfM2 h μ u
            ∧ 0 ≤ mfPc v μ n Φ u := by
  -- the two thresholds: the regime for the `R`-bounds, and the one-body mass gates
  obtain ⟨εreg, hεreg, hreg⟩ := Work.BoseFixB1.regime_sideAt_ge (v := v) hav hR0
  obtain ⟨εM, _K, hεM, _hK, hboxM⟩ := boxM1Info (v := v) h hv hv1 hvrad hR0 hv_supp hav
  refine ⟨min (min εreg 1) εM, lt_min (lt_min hεreg one_pos) hεM, ?_⟩
  intro μ hAdm u hu n Φ hQ
  -- the three admissible points obtained by relaxing the threshold
  have hεle1 : min (min εreg 1) εM ≤ 1 := le_trans (min_le_left _ _) (min_le_right _ _)
  have hεleM : min (min εreg 1) εM ≤ εM := min_le_right _ _
  have hεlereg : min (min εreg 1) εM ≤ εreg := le_trans (min_le_left _ _) (min_le_left _ _)
  have hAdm1 : Work.BoseBoxFix.Adm v 1 μ := Work.BoseFixB1.Adm.mono hAdm hεle1
  have hAdmM : Work.BoseBoxFix.Adm v εM μ := Work.BoseFixB1.Adm.mono hAdm hεleM
  have hAdmreg : Work.BoseBoxFix.Adm v εreg μ := Work.BoseFixB1.Adm.mono hAdm hεlereg
  have ht1 : μ * (_root_.BoseGases.a v) ^ 3 ≤ 1 := Work.BoseFixB1.adm_dilute_le_one hAdm1 le_rfl
  have htreg : μ * (_root_.BoseGases.a v) ^ 3 ≤ εreg := Work.BoseFixB1.adm_dilute hAdmreg
  have htM : μ * (_root_.BoseGases.a v) ^ 3 ≤ εM := Work.BoseFixB1.adm_dilute hAdmM
  have hμ : 0 < μ := Work.BoseFixB1.adm_mu_pos hAdm
  have hav' : 0 < _root_.BoseGases.a v := Work.BoseFixB1.adm_a_pos hAdm
  have hℓ : 0 < Work.BoseBox.sideAt μ (_root_.BoseGases.a v) := Work.BoseFixB1.adm_ell_pos hAdm
  have hd : 0 < (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d :=
    Work.BoseFixB1.adm_d_pos hAdm
  -- the two `R`-bounds of the dilution regime
  obtain ⟨hR16, hRχ⟩ := hreg μ hμ htreg
  -- `d ≤ 1`
  have hd1 : (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d ≤ 1 := by
    rw [Work.BoseFixB1.d_eq_fsXp]
    exact Work.BoseBox.fsXp_le_one (mul_pos hμ (pow_pos hav' 3)) ht1 (by norm_num)
  -- the regime `1 ≤ μ(ℓd)³`
  have hμcube : 1 ≤ μ * (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)
      * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d) ^ 3 := by
    have := Work.BoseFixB1.Regime.one_le_mu_d_mul_sideAt_cube (A := _root_.BoseGases.a v)
      (μ := μ) hav' hμ ht1
    simpa only [mul_comm] using this
  -- the four "mass" gates
  have hVpos : 0 < mfV v μ u :=
    mf_boxMass_pos_of_mem_interiorSet (v := v) (ε₀ := 1) (μ := μ) hAdm1 le_rfl hu
  have hμV : 1 ≤ μ * mfV v μ u :=
    one_le_mu_mul_boxMass hμ hℓ hd hd1 hμcube hu
  have hM : 1 ≤ (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M := by
    rw [Work.BoseFixB1.M_eq_mValue]; decide
  obtain ⟨hM1nn, _hM1ub, hM1leM2⟩ := hboxM μ hAdmM u
  have hn : 1 ≤ n := by
    by_contra hcon
    have hn0 : n = 0 := by omega
    rw [mfQ_eq_zero_of_eq_zero hn0] at hQ
    exact lt_irrefl 0 hQ
  exact ⟨hμ, hℓ, hd, hVpos, hμV, hR16, hRχ, hM, hn, hM1nn, hM1leM2,
    mfPc_nonneg μ n Φ u⟩

end

end Work.BoseFixB1S
