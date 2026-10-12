import ChallengeDeps
import Submission.Work.BoseBogFS.honestFsCore
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

noncomputable section

open scoped Real Topology BigOperators
open MeasureTheory Filter Metric

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Work.BoseBogFS

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-! ## The support thresholds of `honestFsSupp`

Both rows of `honestFsSupp` are monomial comparisons in the diluteness `D = dil v μ = μ(a v)³`.
Writing `cT = 2·10⁶(323/156)` for the constant of `Core.hTup`:

* row 2 (`D^{1/2}`): `T·D^{1/2} ≤ cT·D^{645/1292} ≤ D^{-156/323}` as soon as
  `D^{1269/1292} ≤ cT⁻¹`;
* row 1 (`√(ρa)R`): `T·√(ρa)·R ≤ cT·(√(11/10)R/a)·D^{645/1292} ≤ a·D^{-156/323}` as soon as
  `D^{1269/1292} ≤ a²/(cT·√(11/10)·R)`.

So the diluteness threshold is `min (K₁^{1292/1269}) (min (K₂^{1292/1269}) (coreBound v R))`
with `K₁ = a²/(cT√(11/10)R)` and `K₂ = cT⁻¹`. -/

/-- The numeric factor `2·10⁶·(323/156)` of `Core.hTup`. -/
def suppC : ℝ := 2 * 10 ^ 6 * (323 / 156)

/-- The factor `√(11/10)` of `Core.hsqρa`. -/
def suppK : ℝ := Real.sqrt (11 / 10)

/-- The diluteness threshold of `honestFsSupp`. -/
def suppEps (v : E3 → ℝ) (R : ℝ) : ℝ :=
  min ((_root_.BoseGases.a v ^ 2 / (suppC * suppK * R)) ^ ((1292 : ℝ) / 1269))
    (min ((suppC⁻¹) ^ ((1292 : ℝ) / 1269)) (coreBound v R))

lemma suppC_pos : 0 < suppC := by norm_num [suppC]

lemma suppK_pos : 0 < suppK := Real.sqrt_pos.mpr (by norm_num)

lemma suppEps_pos {v : E3 → ℝ} {R : ℝ} (hR : 0 < R) (hav : 0 < _root_.BoseGases.a v) :
    0 < suppEps v R := by
  have h1 : 0 < _root_.BoseGases.a v ^ 2 / (suppC * suppK * R) :=
    div_pos (pow_pos hav 2) (mul_pos (mul_pos suppC_pos suppK_pos) hR)
  have h2 : 0 < suppC⁻¹ := inv_pos.mpr suppC_pos
  exact lt_min (Real.rpow_pos_of_pos h1 _)
    (lt_min (Real.rpow_pos_of_pos h2 _) (coreBound_pos hR hav))

lemma suppEps_le_coreBound (v : E3 → ℝ) (R : ℝ) : suppEps v R ≤ coreBound v R :=
  le_trans (min_le_right _ _) (min_le_right _ _)

lemma suppEps_le_thr1 (v : E3 → ℝ) (R : ℝ) :
    suppEps v R ≤ (_root_.BoseGases.a v ^ 2 / (suppC * suppK * R)) ^ ((1292 : ℝ) / 1269) :=
  min_le_left _ _

lemma suppEps_le_thr2 (v : E3 → ℝ) (R : ℝ) :
    suppEps v R ≤ (suppC⁻¹) ^ ((1292 : ℝ) / 1269) :=
  le_trans (min_le_right _ _) (min_le_left _ _)

/-- `D ≤ K^{1292/1269}` implies `D^{1269/1292} ≤ K`. -/
lemma rpow_thresh {D K : ℝ} (hD : 0 < D) (hK : 0 < K)
    (h : D ≤ K ^ ((1292 : ℝ) / 1269)) : D ^ ((1269 : ℝ) / 1292) ≤ K := by
  calc D ^ ((1269 : ℝ) / 1292) ≤ (K ^ ((1292 : ℝ) / 1269)) ^ ((1269 : ℝ) / 1292) :=
        Real.rpow_le_rpow hD.le h (by norm_num)
    _ = K := by
        rw [← Real.rpow_mul hK.le]
        rw [show (1292 : ℝ) / 1269 * (1269 / 1292) = 1 by norm_num, Real.rpow_one]

/-- **The monomial core of the two support rows**: if `cT·D^{1269/1292} ≤ A/M` then
`cT·M·D^{645/1292} ≤ A·D^{-156/323}`.  The extra factor `M` is `1` in the `D^{1/2}` row and
`√(11/10)R/a` in the `√(ρa)R` row. -/
lemma supp_mono {D cT M A : ℝ} (hD0 : 0 < D) (hM : 0 < M) (hA : 0 ≤ A)
    (h1 : cT * D ^ ((1269 : ℝ) / 1292) ≤ A / M) :
    cT * M * D ^ ((645 : ℝ) / 1292) ≤ A * D ^ (-(156 / 323 : ℝ)) := by
  have hE : -(624 / 1292 : ℝ) = -(156 / 323) := by norm_num
  have h624 : 0 ≤ D ^ (-(624 / 1292 : ℝ)) := Real.rpow_nonneg hD0.le _
  calc cT * M * D ^ ((645 : ℝ) / 1292)
      = (cT * D ^ ((1269 : ℝ) / 1292)) * (M * D ^ (-(624 / 1292 : ℝ))) := by
        rw [show (645 : ℝ) / 1292 = (1269 : ℝ) / 1292 + (-(624 / 1292)) by norm_num,
          Real.rpow_add hD0]
        ring
    _ ≤ (A / M) * (M * D ^ (-(624 / 1292 : ℝ))) :=
        mul_le_mul_of_nonneg_right h1 (mul_nonneg hM.le h624)
    _ = A * D ^ (-(156 / 323 : ℝ)) := by
        rw [hE, ← mul_assoc, div_mul_cancel₀ _ (ne_of_gt hM)]

/-- **The two kernel-support rows of `FsI1Regime` at the honest kernel.**

FS's rows `hTsupp` and `hTm`: the momentum cutoff `T = max 0 (bogT v R μ)` times
`√(ρa)R` (resp. `D^{1/2}`, `D = dil v μ = μ(a v)³`) is at most `K_ℓ d s/√(μa)`
(resp. `K_ℓ d s/D^{1/2}`), where `K_ℓ,d,s` are the parameters of `paramsAt μ (a v)`.

Route: by the proved parameter lemmas of `Work.BoseBogFS.honestFsCore`
(`Work.BoseBogFS.dsKl_eq`: `K_ℓ·d·s = D^{11/646}`, `Work.BoseBogFS.sqrt_mua`) together
with `Core.hTup` (`T ≤ 2·10⁶(323/156)·D^{-1/1292}`), `Core.hsqρa`
(`√(ρa) ≤ √(11/10)√D/a`), `Core.hsqμa` (`√(μa) = √D/a`), `Core.hD1`, `Core.hTpos`,
`Core.hη0` (to collapse the `max 0`).  Both rows reduce to a monomial comparison
`D^{1269/1292} ≤ C(a,R)`, giving `ε₀ = min (threshold) (coreBound v R) > 0`. -/
theorem honestFsSupp {v : EuclideanSpace ℝ (Fin 3) → ℝ} {R : ℝ} (hR : 0 < R)
    (hav : 0 < _root_.BoseGases.a v) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ → ∀ ρ : ℝ,
      Work.BoseBoxFock.CloseCondFS v μ ρ →
      (Work.BoseBogFS.bogKernel v R ρ μ).T * Real.sqrt (ρ * _root_.BoseGases.a v) * R
          ≤ (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).Kl
            * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d
            * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s
            / Real.sqrt (μ * _root_.BoseGases.a v) ∧
      (Work.BoseBogFS.bogKernel v R ρ μ).T * (μ * (_root_.BoseGases.a v) ^ 3) ^ (1 / 2 : ℝ)
          ≤ (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).Kl
            * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d
            * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s
            / (μ * (_root_.BoseGases.a v) ^ 3) ^ (1 / 2 : ℝ) := by
  refine ⟨suppEps v R, suppEps_pos hR hav, ?_⟩
  intro μ hAdm ρ hclose
  have hμ : 0 < μ := hAdm.1
  have hDδ : Work.BoseFixR.dil v μ ≤ suppEps v R := hAdm.2.1
  have hcore : Core v R μ ρ :=
    core_bounds hR hav (suppEps_le_coreBound v R) μ ρ hμ hDδ hclose
  have hD0 : 0 < Work.BoseFixR.dil v μ := hcore.hD0
  -- write the diluteness `μ(a v)³` of the statement as `dil v μ`
  have hDil : μ * _root_.BoseGases.a v ^ 3 = Work.BoseFixR.dil v μ := rfl
  rw [hDil]
  -- the cutoff bound of `Core.hTup`, with the `max 0` collapsed by positivity of `bogT`
  have hTle : (bogKernel v R ρ μ).T ≤ suppC * (Work.BoseFixR.dil v μ) ^ (-(1 / 1292 : ℝ)) := by
    rw [bogKernel_T, max_eq_right hcore.hTpos.le]
    exact hcore.hTup
  -- the parameter monomial `K_ℓ d s = D^{11/646}`
  have hKDS : (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).Kl
      * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d
      * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s
      = (Work.BoseFixR.dil v μ) ^ ((11 : ℝ) / 646) := by
    rw [← dsKl_eq v μ hD0]
    ring
  constructor
  · -- ## row 1: the `√(ρa)·R` row
    have hsρ : Real.sqrt (ρ * _root_.BoseGases.a v)
        ≤ suppK * (Work.BoseFixR.dil v μ) ^ (1 / 2 : ℝ) / _root_.BoseGases.a v :=
      hcore.hsqρa
    have hDle1 : Work.BoseFixR.dil v μ
        ≤ (_root_.BoseGases.a v ^ 2 / (suppC * suppK * R)) ^ ((1292 : ℝ) / 1269) :=
      le_trans hDδ (suppEps_le_thr1 v R)
    have hmono1 : (Work.BoseFixR.dil v μ) ^ ((1269 : ℝ) / 1292)
        ≤ _root_.BoseGases.a v ^ 2 / (suppC * suppK * R) :=
      rpow_thresh hD0
        (div_pos (pow_pos hav 2) (mul_pos (mul_pos suppC_pos suppK_pos) hR)) hDle1
    have hL1 : (bogKernel v R ρ μ).T * Real.sqrt (ρ * _root_.BoseGases.a v) * R
        ≤ suppC * (suppK * R / _root_.BoseGases.a v)
          * (Work.BoseFixR.dil v μ) ^ ((645 : ℝ) / 1292) := by
      calc (bogKernel v R ρ μ).T * Real.sqrt (ρ * _root_.BoseGases.a v) * R
          ≤ (suppC * (Work.BoseFixR.dil v μ) ^ (-(1 / 1292 : ℝ)))
              * (suppK * (Work.BoseFixR.dil v μ) ^ (1 / 2 : ℝ) / _root_.BoseGases.a v)
              * R := by
            have h1 := mul_le_mul hTle hsρ (Real.sqrt_nonneg _)
              (mul_nonneg suppC_pos.le (Real.rpow_nonneg hD0.le _))
            exact mul_le_mul_of_nonneg_right h1 hR.le
        _ = suppC * (suppK * R / _root_.BoseGases.a v)
              * (Work.BoseFixR.dil v μ) ^ ((645 : ℝ) / 1292) := by
            rw [show (suppC * (Work.BoseFixR.dil v μ) ^ (-(1 / 1292 : ℝ)))
                  * (suppK * (Work.BoseFixR.dil v μ) ^ (1 / 2 : ℝ) / _root_.BoseGases.a v)
                  * R
                = suppC * (suppK * R / _root_.BoseGases.a v)
                  * ((Work.BoseFixR.dil v μ) ^ (-(1 / 1292 : ℝ))
                    * (Work.BoseFixR.dil v μ) ^ (1 / 2 : ℝ)) by ring]
            rw [← Real.rpow_add hD0]
            rw [show -(1 / 1292 : ℝ) + 1 / 2 = 645 / 1292 by norm_num]
    have hkey1 : suppC * (suppK * R / _root_.BoseGases.a v)
          * (Work.BoseFixR.dil v μ) ^ ((645 : ℝ) / 1292)
        ≤ _root_.BoseGases.a v * (Work.BoseFixR.dil v μ) ^ (-(156 / 323 : ℝ)) := by
      refine supp_mono hD0 (div_pos (mul_pos suppK_pos hR) hav) hav.le ?_
      calc suppC * (Work.BoseFixR.dil v μ) ^ ((1269 : ℝ) / 1292)
          ≤ suppC * (_root_.BoseGases.a v ^ 2 / (suppC * suppK * R)) :=
            mul_le_mul_of_nonneg_left hmono1 suppC_pos.le
        _ = _root_.BoseGases.a v / (suppK * R / _root_.BoseGases.a v) := by
            have hane : _root_.BoseGases.a v ≠ 0 := ne_of_gt hav
            have hRne : R ≠ 0 := ne_of_gt hR
            have hKne : suppK ≠ 0 := ne_of_gt suppK_pos
            have hCne : suppC ≠ 0 := ne_of_gt suppC_pos
            field_simp
    have hrhs1 : (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).Kl
        * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d
        * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s / Real.sqrt (μ * _root_.BoseGases.a v)
        = _root_.BoseGases.a v * (Work.BoseFixR.dil v μ) ^ (-(156 / 323 : ℝ)) := by
      rw [hKDS, hcore.hsqμa, div_div_eq_mul_div]
      rw [show (Work.BoseFixR.dil v μ) ^ ((11 : ℝ) / 646) * _root_.BoseGases.a v
            / (Work.BoseFixR.dil v μ) ^ (1 / 2 : ℝ)
          = _root_.BoseGases.a v * ((Work.BoseFixR.dil v μ) ^ ((11 : ℝ) / 646)
            / (Work.BoseFixR.dil v μ) ^ (1 / 2 : ℝ)) by ring]
      rw [← Real.rpow_sub hD0, show (11 : ℝ) / 646 - 1 / 2 = -(156 / 323) by norm_num]
    rw [hrhs1]
    exact le_trans hL1 hkey1
  · -- ## row 2: the `D^{1/2}` row
    have hDle2 : Work.BoseFixR.dil v μ ≤ (suppC⁻¹) ^ ((1292 : ℝ) / 1269) :=
      le_trans hDδ (suppEps_le_thr2 v R)
    have hmono2 : (Work.BoseFixR.dil v μ) ^ ((1269 : ℝ) / 1292) ≤ suppC⁻¹ :=
      rpow_thresh hD0 (inv_pos.mpr suppC_pos) hDle2
    have h1row2 : suppC * (Work.BoseFixR.dil v μ) ^ ((1269 : ℝ) / 1292) ≤ (1 : ℝ) / 1 := by
      rw [div_one]
      have h := mul_le_mul_of_nonneg_left hmono2 suppC_pos.le
      rwa [mul_inv_cancel₀ (ne_of_gt suppC_pos)] at h
    have hk2 : suppC * (1 : ℝ) * (Work.BoseFixR.dil v μ) ^ ((645 : ℝ) / 1292)
        ≤ (1 : ℝ) * (Work.BoseFixR.dil v μ) ^ (-(156 / 323 : ℝ)) :=
      supp_mono hD0 (by norm_num) (by norm_num) h1row2
    have hkey2 : suppC * (Work.BoseFixR.dil v μ) ^ ((645 : ℝ) / 1292)
        ≤ (Work.BoseFixR.dil v μ) ^ (-(156 / 323 : ℝ)) := by simpa using hk2
    have hL2 : (bogKernel v R ρ μ).T * (Work.BoseFixR.dil v μ) ^ (1 / 2 : ℝ)
        ≤ suppC * (Work.BoseFixR.dil v μ) ^ ((645 : ℝ) / 1292) := by
      calc (bogKernel v R ρ μ).T * (Work.BoseFixR.dil v μ) ^ (1 / 2 : ℝ)
          ≤ (suppC * (Work.BoseFixR.dil v μ) ^ (-(1 / 1292 : ℝ)))
              * (Work.BoseFixR.dil v μ) ^ (1 / 2 : ℝ) :=
            mul_le_mul_of_nonneg_right hTle (Real.rpow_nonneg hD0.le _)
        _ = suppC * ((Work.BoseFixR.dil v μ) ^ (-(1 / 1292 : ℝ))
              * (Work.BoseFixR.dil v μ) ^ (1 / 2 : ℝ)) := by ring
        _ = suppC * (Work.BoseFixR.dil v μ) ^ ((645 : ℝ) / 1292) := by
            rw [← Real.rpow_add hD0]
            rw [show -(1 / 1292 : ℝ) + 1 / 2 = 645 / 1292 by norm_num]
    have hrhs2 : (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).Kl
        * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d
        * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s
        / (Work.BoseFixR.dil v μ) ^ (1 / 2 : ℝ)
        = (Work.BoseFixR.dil v μ) ^ (-(156 / 323 : ℝ)) := by
      rw [hKDS, ← Real.rpow_sub hD0,
        show (11 : ℝ) / 646 - 1 / 2 = -(156 / 323) by norm_num]
    rw [hrhs2]
    exact le_trans hL2 hkey2

end Work.BoseBogFS
