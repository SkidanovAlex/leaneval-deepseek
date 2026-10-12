import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseB1Cube.gammaRegimeAt
import Submission.Work.BoseFixB1B.coreMassLower
import Submission.Work.BoseFixB1B.sectorCountDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseB1Cube

open scoped Real Topology BigOperators

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

/-! ## Elementary real/rpow bookkeeping

Everything below is a *threshold* statement: each of the finitely many smallness conditions
is monotone in the diluteness `t = μ(a v)³`, so the minimum of the finitely many explicit
thresholds works.  The two helpers convert between `t ≤ C^q` and `t^p ≤ C`
(`q p = 1`), and between `t ≤ C^(-1/p)` and `C ≤ t^(-p)`. -/

/-- `t ^ p ≤ C` from `t ≤ C ^ q` when `q * p = 1` (`C ≥ 0`, `p ≥ 0`, `t > 0`). -/
private lemma rpow_le_threshold {t p q C : ℝ} (ht : 0 < t) (hC : 0 ≤ C) (hp : 0 ≤ p)
    (hpq : q * p = 1) (h : t ≤ C ^ q) : t ^ p ≤ C := by
  calc t ^ p ≤ (C ^ q) ^ p := Real.rpow_le_rpow ht.le h hp
    _ = C ^ (q * p) := (Real.rpow_mul hC q p).symm
    _ = C := by rw [hpq, Real.rpow_one]

/-- `C ≤ t ^ (-p)` from `t ≤ C ^ (-(1/p))` (`t > 0`, `C > 0`, `p > 0`). -/
private lemma rpow_neg_ge_of_le {t C p : ℝ} (ht : 0 < t) (hC : 0 < C) (hp : 0 < p)
    (h : t ≤ C ^ (-(1 / p))) : C ≤ t ^ (-p) := by
  have h1 : t ^ p ≤ C ^ (-(1 / p) * p) := by
    calc t ^ p ≤ (C ^ (-(1 / p))) ^ p := Real.rpow_le_rpow ht.le h hp.le
      _ = C ^ (-(1 / p) * p) := (Real.rpow_mul hC.le (-(1 / p)) p).symm
  have h2 : -(1 / p) * p = -1 := by field_simp
  rw [h2, Real.rpow_neg_one] at h1
  have h3 : (0 : ℝ) < C⁻¹ := inv_pos.mpr hC
  have h4 : (C⁻¹)⁻¹ ≤ (t ^ p)⁻¹ :=
    (inv_le_inv₀ h3 (Real.rpow_pos_of_pos ht p)).mpr h1
  rw [inv_inv] at h4
  rwa [Real.rpow_neg ht.le]

/-- The diluteness threshold for the **mass** smallness: for every prescribed `B > 0` and every
`Kc` there is `e > 0` with `Kc ≤ B · t^{-148/323}` for all `0 < t ≤ e` (the exponent `-148/323`
is `μ(ℓd)³` at FS's parameters). -/
private lemma mass_threshold {B Kc : ℝ} (hB : 0 < B) :
    ∃ e : ℝ, 0 < e ∧ ∀ t : ℝ, 0 < t → t ≤ e → Kc ≤ B * t ^ (-(148 / 323) : ℝ) := by
  have hmax : (0 : ℝ) < max Kc 1 := lt_of_lt_of_le one_pos (le_max_right Kc 1)
  refine ⟨(max Kc 1 / B) ^ (-(323 / 148) : ℝ),
    Real.rpow_pos_of_pos (div_pos hmax hB) _, ?_⟩
  intro t ht hle
  have hC : 0 < max Kc 1 / B := div_pos hmax hB
  have hp : (0 : ℝ) < (148 / 323 : ℝ) := by norm_num
  have hq : -(1 / (148 / 323 : ℝ)) = -(323 / 148 : ℝ) := by norm_num
  rw [← hq] at hle
  have h1 := rpow_neg_ge_of_le ht hC hp hle
  calc Kc ≤ max Kc 1 := le_max_left Kc 1
    _ = B * (max Kc 1 / B) := by field_simp
    _ ≤ B * t ^ (-(148 / 323) : ℝ) := mul_le_mul_of_nonneg_left h1 hB.le

/-- The diluteness threshold for the **spectral** smallness: for every prescribed `δ > 0` there is
`e > 0` with `t^{287/646} ≤ δ` for all `0 < t ≤ e`. -/
private lemma gamma_threshold {δ : ℝ} (hδ : 0 < δ) :
    ∃ e : ℝ, 0 < e ∧ ∀ t : ℝ, 0 < t → t ≤ e → t ^ (287 / 646 : ℝ) ≤ δ :=
  ⟨δ ^ (646 / 287 : ℝ), Real.rpow_pos_of_pos hδ _,
   fun t ht hle => rpow_le_threshold ht hδ.le (by norm_num) (by norm_num) hle⟩

/-- `Adm` is monotone in the diluteness threshold. -/
private lemma adm_mono {v : EuclideanSpace ℝ (Fin 3) → ℝ} {ε ε' μ : ℝ}
    (h : Work.BoseBoxFix.Adm v ε μ) (hle : ε ≤ ε') : Work.BoseBoxFix.Adm v ε' μ :=
  ⟨h.1, le_trans h.2.1 hle, h.2.2⟩

/-! ## The core geometry (the deep-interior condition)

These two lemmas are the core hypothesis `|((ℓd)•u)_j| ≤ ℓ/16` converted into the
deep-interior hypothesis `‖d•u‖ + √3 d/2 ≤ 1/4` of `chiMass_eq_deep`. -/

/-- The core hypothesis `|((ℓd)•u)_j| ≤ ℓ/16` gives `‖d•u‖ ≤ √3/16`. -/
private lemma core_norm_d_smul_le {ℓ d : ℝ} (hℓ : 0 < ℓ) {u : EuclideanSpace ℝ (Fin 3)}
    (hu : ∀ j : Fin 3, |((ℓ * d) • u).ofLp j| ≤ ℓ / 16) :
    ‖d • u‖ ≤ Real.sqrt 3 * (1 / 16) := by
  refine Work.BoseFixB1S.norm_le_sqrt3_mul (by norm_num) ?_
  intro j
  have h1 : ((ℓ * d) • u).ofLp j = ℓ * (d • u).ofLp j := by
    rw [show (ℓ * d) • u = ℓ • (d • u) by rw [smul_smul]]
    rfl
  have h2 : ℓ * |(d • u).ofLp j| ≤ ℓ * (1 / 16) := by
    calc ℓ * |(d • u).ofLp j| = |((ℓ * d) • u).ofLp j| := by rw [h1, abs_mul, abs_of_pos hℓ]
      _ ≤ ℓ / 16 := hu j
      _ = ℓ * (1 / 16) := by ring
  have h3 : ℓ⁻¹ * (ℓ * |(d • u).ofLp j|) ≤ ℓ⁻¹ * (ℓ * (1 / 16)) :=
    mul_le_mul_of_nonneg_left h2 (le_of_lt (inv_pos.mpr hℓ))
  calc |(d • u).ofLp j| = ℓ⁻¹ * (ℓ * |(d • u).ofLp j|) := by field_simp
    _ ≤ ℓ⁻¹ * (ℓ * (1 / 16)) := h3
    _ = 1 / 16 := by field_simp

/-- `s + √3 d/2 ≤ 1/4` for `d ≤ 1/16` and `s ≤ √3/16` (the bound `3√3 ≤ 8`). -/
private lemma core_sqrt3_arith {d s : ℝ} (hd16 : d ≤ 1 / 16)
    (hs : s ≤ Real.sqrt 3 * (1 / 16)) : s + Real.sqrt 3 * d / 2 ≤ 1 / 4 := by
  have hd32 : Real.sqrt 3 * d / 2 ≤ Real.sqrt 3 * (1 / 16) / 2 := by
    have := mul_le_mul_of_nonneg_left hd16 (Real.sqrt_nonneg 3)
    linarith
  have hs3 : 3 * Real.sqrt 3 ≤ 8 := by
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num), Real.sqrt_nonneg 3,
      sq_nonneg (Real.sqrt 3 - 2)]
  linarith

/-- Two diluteness-smallness facts on the **core** positions of the sliding box, at ARBITRARY
prescribed constants, that the row-1 surplus of the cube ledger needs: the localised one-body mass
`PBW h μ u = w1MassB` satisfies `Kc ≤ μ * PBW h μ u`, and the spectral parameter
`PBΓ v μ = K_B³(μ(a v)³)^{1/2}` satisfies `PBΓ v μ ≤ δ`.

On the core (`|((ℓd)•u)_j| ≤ ℓ/16`) the *untruncated* small cube `(ℓd)•u + acube(ℓd)` lies inside
`acube ℓ`, so `boxMass = (ℓd)³` and `ℓ d = (a v) t^{-157/323}` (`Work.BoseFixB1.d_mul_sideAt_eq`),
giving `μ (ℓd)³ = t^{-148/323} → ∞`; `chiMass = chiSupAbs²(ℓd)³`
(`Work.BoseFixB1B.chiMass_eq_deep`) and `8π(a v) chiMass ≤ PBW` (`Work.BoseFixB1B.coreMassLower`)
make `μ * PBW` exceed any prescribed `Kc` as `t = μ(a v)³ → 0⁺`.  `PBΓ = t^{287/646} → 0` via
`Work.BoseFixB1.KB3_half_eq` + `Work.BoseBox.fsXp`.  (`coreMassLower` needs `d ≤ 1/16` and
`R ≤ ℓd/16`: `Work.BoseB1Cube.gammaRegimeAt` gives `d ≤ 1/8`, `R ≤ ℓd/16`, and one further shrink
via `d_eq_fsXp` gives `d ≤ 1/16`.) -/
theorem coreSmallA {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v) (hv : 0 ≤ v)
    (hv1 : MeasureTheory.MemLp v 1) (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    (hav : 0 < _root_.BoseGases.a v)
    {Kc δ : ℝ} (hKc : 0 ≤ Kc) (hδ : 0 < δ) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
      ∀ u : EuclideanSpace ℝ (Fin 3),
        (∀ j : Fin 3, |((Work.BoseFixB1B.PBℓ v μ * Work.BoseFixB1B.PBd v μ) • u).ofLp j|
            ≤ Work.BoseFixB1B.PBℓ v μ / 16) →
        Kc ≤ μ * Work.BoseFixB1B.PBW h μ u ∧ Work.BoseFixB1B.PBΓ v μ ≤ δ := by
  classical
  obtain ⟨ε₁, hε₁pos, hregime⟩ := gammaRegimeAt (v := v) hav hR
  have hχpos : 0 < Submission.BoseGases.chiSupAbs := Work.BoseFixB1B.chiSupAbs_pos
  have hBpos : 0 < 8 * Real.pi * (_root_.BoseGases.a v) * Submission.BoseGases.chiSupAbs ^ 2 := by
    positivity
  obtain ⟨εK, hεKpos, hεK⟩ := mass_threshold (Kc := Kc) hBpos
  obtain ⟨εΓ, hεΓpos, hεΓ⟩ := gamma_threshold (δ := δ) hδ
  have hεdpos : (0 : ℝ) < (1 / 16) ^ (323 / 6 : ℝ) := Real.rpow_pos_of_pos (by norm_num) _
  refine ⟨min (min ε₁ ((1 / 16) ^ (323 / 6 : ℝ))) (min εΓ εK), ?_, ?_⟩
  · exact lt_min (lt_min hε₁pos hεdpos) (lt_min hεΓpos hεKpos)
  · intro μ hAdm u hu
    have hμpos : 0 < μ := hAdm.1
    have htle : μ * (_root_.BoseGases.a v) ^ 3
        ≤ min (min ε₁ ((1 / 16) ^ (323 / 6 : ℝ))) (min εΓ εK) := hAdm.2.1
    have ht0 : 0 < μ * (_root_.BoseGases.a v) ^ 3 := mul_pos hμpos (pow_pos hav 3)
    have htle1 : μ * (_root_.BoseGases.a v) ^ 3 ≤ ε₁ :=
      le_trans htle (le_trans (min_le_left _ _) (min_le_left _ _))
    have htle2 : μ * (_root_.BoseGases.a v) ^ 3 ≤ (1 / 16) ^ (323 / 6 : ℝ) :=
      le_trans htle (le_trans (min_le_left _ _) (min_le_right _ _))
    have htle3 : μ * (_root_.BoseGases.a v) ^ 3 ≤ εΓ :=
      le_trans htle (le_trans (min_le_right _ _) (min_le_left _ _))
    have htle4 : μ * (_root_.BoseGases.a v) ^ 3 ≤ εK :=
      le_trans htle (le_trans (min_le_right _ _) (min_le_right _ _))
    have hAdm1 : Work.BoseBoxFix.Adm v ε₁ μ := ⟨hμpos, htle1, hAdm.2.2⟩
    -- ## the spectral parameter: `PBΓ = t^{287/646} ≤ δ`
    have hΓeq : Work.BoseFixB1B.PBΓ v μ = (μ * (_root_.BoseGases.a v) ^ 3) ^ (287 / 646 : ℝ) := by
      rw [Work.BoseFixB1B.PBΓ, Work.BoseFixB1B.PBKB, Work.FockBridge.dlGamma,
        Work.BoseFixB1.KB3_half_eq hav hμpos]
      simp only [Work.BoseBox.fsXp]
      norm_num
    have hΓ : Work.BoseFixB1B.PBΓ v μ ≤ δ := by
      rw [hΓeq]
      exact hεΓ (μ * (_root_.BoseGases.a v) ^ 3) ht0 htle3
    -- ## the size bundle at the small diluteness
    have hM1 : 1 ≤ Work.BoseFixB1B.PBM v μ := by
      show 1 ≤ (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
      rw [Work.BoseFixB1.M_eq_mValue]
      norm_num [Work.BoseBox.mValue]
    have hℓpos : 0 < Work.BoseFixB1B.PBℓ v μ := Work.BoseBox.sideAt_pos hμpos hav
    have hdpos : 0 < Work.BoseFixB1B.PBd v μ := by
      show 0 < (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d
      rw [Work.BoseFixB1.d_eq_fsXp]
      exact Work.BoseBox.fsXp_pos ht0
    have hd16 : Work.BoseFixB1B.PBd v μ ≤ 1 / 16 := by
      show (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d ≤ 1 / 16
      rw [Work.BoseFixB1.d_eq_fsXp]
      exact rpow_le_threshold ht0 (by norm_num) (by norm_num) (by norm_num) htle2
    have hR16 : R ≤ Work.BoseFixB1B.PBℓ v μ * Work.BoseFixB1B.PBd v μ / 16 :=
      (hregime hAdm1).1
    -- ## the core mass bound `8π(a v)(ℓd)³chiSupAbs² ≤ PBW`
    have hdup : ‖Work.BoseFixB1B.PBd v μ • u‖
        + Real.sqrt 3 * Work.BoseFixB1B.PBd v μ / 2 ≤ 1 / 4 :=
      core_sqrt3_arith hd16 (core_norm_d_smul_le hℓpos hu)
    have hchiMass : Work.SmallBoxSliding.chiMass (Work.BoseFixB1B.PBM v μ)
        (Work.BoseFixB1B.PBℓ v μ) (Work.BoseFixB1B.PBd v μ) u
        = Submission.BoseGases.chiSupAbs ^ 2
            * (Work.BoseFixB1B.PBℓ v μ * Work.BoseFixB1B.PBd v μ) ^ 3 :=
      Work.BoseFixB1B.chiMass_eq_deep hM1 hℓpos hdpos hdup
    have hcore := Work.BoseFixB1B.coreMassLower h hv hvrad hR hv_supp hav hM1 hℓpos hdpos hd16 hR16 hu
    have hWge : 8 * Real.pi * (_root_.BoseGases.a v) *
        (Submission.BoseGases.chiSupAbs ^ 2
          * (Work.BoseFixB1B.PBℓ v μ * Work.BoseFixB1B.PBd v μ) ^ 3)
        ≤ Work.BoseFixB1B.PBW h μ u := by
      rw [← hchiMass]
      exact hcore
    -- ## the box volume `μ(ℓd)³ = t^{-148/323}`
    have hmass : μ * ((Work.BoseFixB1B.PBℓ v μ) * (Work.BoseFixB1B.PBd v μ)) ^ 3
        = (μ * (_root_.BoseGases.a v) ^ 3) ^ (-(148 / 323) : ℝ) := by
      have hcomm : (Work.BoseFixB1B.PBℓ v μ) * (Work.BoseFixB1B.PBd v μ)
          = (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d
              * (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) := by
        show (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
            * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d = _
        ring
      rw [hcomm, Work.BoseFixB1.mu_d_mul_sideAt_cube_eq hav hμpos, Work.BoseBox.fsXp]
      norm_num
    -- ## assembly
    refine ⟨?_, hΓ⟩
    calc Kc ≤ 8 * Real.pi * (_root_.BoseGases.a v) * Submission.BoseGases.chiSupAbs ^ 2
            * (μ * (_root_.BoseGases.a v) ^ 3) ^ (-(148 / 323) : ℝ) :=
          hεK (μ * (_root_.BoseGases.a v) ^ 3) ht0 htle4
      _ = μ * (8 * Real.pi * (_root_.BoseGases.a v) *
            (Submission.BoseGases.chiSupAbs ^ 2
              * ((Work.BoseFixB1B.PBℓ v μ) * (Work.BoseFixB1B.PBd v μ)) ^ 3)) := by
          rw [← hmass]; ring
      _ ≤ μ * Work.BoseFixB1B.PBW h μ u := mul_le_mul_of_nonneg_left hWge hμpos.le

end Work.BoseB1Cube
