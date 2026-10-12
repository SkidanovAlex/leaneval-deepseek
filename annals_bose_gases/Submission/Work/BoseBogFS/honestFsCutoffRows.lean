import ChallengeDeps
import Submission.Work.BoseBogFS.honestFsCore
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseBogFS

noncomputable section
open scoped Real Topology BigOperators

set_option autoImplicit false

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-! ## The cutoff rows, in the diluteness monomial `D = μ(a v)³`

At the honest parameter block `paramsAt μ (a v)` the two kinetic cutoffs are

  `c₁ = (2 s ℓ √(ρa))⁻¹ = ½ (K_ℓ s)⁻¹ √(μ/ρ) = ½ D^{1/646} √(μ/ρ)`,
  `c₂ = (2 d s ℓ √(ρa))⁻¹ = ½ (K_ℓ d s)⁻¹ √(μ/ρ) = ½ D^{-11/646} √(μ/ρ)`

and `ε_T = D^{23/1292}`, so that `ε_T c₂ = ½ D^{1/1292} √(μ/ρ)`.  The three rows of
`FsI1Regime` (`hc1`, `hc12`, `hcc1`) are then immediate from `0 < D ≤ 1` and the numeric
core bound `D^{1/1292} ≤ 1/1024`. -/

/-- The first cutoff in the diluteness monomial: `c₁ = ½ D^{1/646} √(μ/ρ)`. -/
lemma bogC1_eq_dil (v : E3 → ℝ) (ρ μ : ℝ) (hav : 0 < _root_.BoseGases.a v)
    (hμ : 0 < μ) (hρ : 0 < ρ) (hD : 0 < Work.BoseFixR.dil v μ) :
    bogC1 v ρ μ = (1 / 2) * (Work.BoseFixR.dil v μ) ^ ((1 : ℝ) / 646)
      * Real.sqrt (μ / ρ) := by
  rw [bogC1_eq v ρ μ hav hμ hρ,
    show (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).Kl
        * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s
      = (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s
        * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).Kl from by ring,
    sKl_inv v μ hD]

/-- `(K_ℓ d s)⁻¹ = D^{-11/646}`. -/
lemma dsKl_inv (v : E3 → ℝ) (μ : ℝ) (hD : 0 < Work.BoseFixR.dil v μ) :
    ((Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).Kl
        * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d
        * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s)⁻¹
      = (Work.BoseFixR.dil v μ) ^ (-(11 / 646) : ℝ) := by
  rw [show (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).Kl
        * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d
        * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s
      = (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d
        * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s
        * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).Kl from by ring,
    dsKl_eq v μ hD, Real.rpow_neg hD.le]

/-- The second cutoff in the diluteness monomial: `c₂ = ½ D^{-11/646} √(μ/ρ)`. -/
lemma bogC2_eq_dil (v : E3 → ℝ) (ρ μ : ℝ) (hav : 0 < _root_.BoseGases.a v)
    (hμ : 0 < μ) (hρ : 0 < ρ) (hD : 0 < Work.BoseFixR.dil v μ) :
    bogC2 v ρ μ = (1 / 2) * (Work.BoseFixR.dil v μ) ^ (-(11 / 646) : ℝ)
      * Real.sqrt (μ / ρ) := by
  rw [bogC2_eq v ρ μ hav hμ hρ, dsKl_inv v μ hD]

/-- `D^{-11/646} = (d s K_ℓ)⁻¹`, the shape in which FS's `ε_T`-identity
`Work.BoseBogFS.eT_dsKl_inv` is stated. -/
lemma dil_neg11_646_eq_dsKl_inv (v : E3 → ℝ) (μ : ℝ) (hD : 0 < Work.BoseFixR.dil v μ) :
    (Work.BoseFixR.dil v μ) ^ (-(11 / 646) : ℝ)
      = ((Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d
        * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s
        * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).Kl)⁻¹ := by
  rw [dsKl_eq v μ hD, Real.rpow_neg hD.le]

/-- `ε_T (K_ℓ d s)⁻¹ = D^{1/1292}`, i.e. the `ε_T`-weighted second cutoff is
`½ D^{1/1292} √(μ/ρ)`. -/
lemma eT_mul_dil (v : E3 → ℝ) (μ : ℝ) (hD : 0 < Work.BoseFixR.dil v μ) :
    (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).eT
        * (Work.BoseFixR.dil v μ) ^ (-(11 / 646) : ℝ)
      = (Work.BoseFixR.dil v μ) ^ ((1 : ℝ) / 1292) := by
  rw [dil_neg11_646_eq_dsKl_inv v μ hD]
  exact eT_dsKl_inv v μ hD

/-- `D^{1/646} ≤ D^{-11/646}` for `0 < D ≤ 1`: equivalently `D^{6/323} ≤ 1`, since
`D^{-11/646} = D^{1/646} (D^{6/323})^{-1}`.  This is the second cutoff row `c₁ ≤ c₂`. -/
lemma dil_rpow_646_le_neg11_646 (v : E3 → ℝ) (μ : ℝ) (hD0 : 0 < Work.BoseFixR.dil v μ)
    (hD1 : Work.BoseFixR.dil v μ ≤ 1) :
    (Work.BoseFixR.dil v μ) ^ ((1 : ℝ) / 646) ≤ (Work.BoseFixR.dil v μ) ^ (-(11 / 646) : ℝ) := by
  have hd1 : (Work.BoseFixR.dil v μ) ^ ((6 : ℝ) / 323) ≤ 1 :=
    Real.rpow_le_one hD0.le hD1 (by norm_num)
  have hdpos : 0 < (Work.BoseFixR.dil v μ) ^ ((6 : ℝ) / 323) :=
    Real.rpow_pos_of_pos hD0 _
  have hinv : 1 ≤ ((Work.BoseFixR.dil v μ) ^ ((6 : ℝ) / 323))⁻¹ := (one_le_inv₀ hdpos).mpr hd1
  have hstep : (Work.BoseFixR.dil v μ) ^ ((1 : ℝ) / 646)
      ≤ (Work.BoseFixR.dil v μ) ^ ((1 : ℝ) / 646)
        * ((Work.BoseFixR.dil v μ) ^ ((6 : ℝ) / 323))⁻¹ := by
    simpa using mul_le_mul_of_nonneg_left hinv (Real.rpow_nonneg hD0.le ((1 : ℝ) / 646))
  have heq : (Work.BoseFixR.dil v μ) ^ ((1 : ℝ) / 646)
        * ((Work.BoseFixR.dil v μ) ^ ((6 : ℝ) / 323))⁻¹
      = (Work.BoseFixR.dil v μ) ^ (-(11 / 646) : ℝ) := by
    rw [← Real.rpow_neg hD0.le ((6 : ℝ) / 323), ← Real.rpow_add hD0,
      show (1 : ℝ) / 646 + -(6 / 323) = -(11 / 646) by norm_num]
  exact le_trans hstep heq.le

/-- `D^{1/646} ≤ D^{1/1292}` for `0 < D ≤ 1`: the exponent `1/646` is twice `1/1292`. -/
lemma dil_rpow_646_le_1292 (v : E3 → ℝ) (μ : ℝ) (hD0 : 0 < Work.BoseFixR.dil v μ)
    (hD1 : Work.BoseFixR.dil v μ ≤ 1) :
    (Work.BoseFixR.dil v μ) ^ ((1 : ℝ) / 646) ≤ (Work.BoseFixR.dil v μ) ^ ((1 : ℝ) / 1292) := by
  have hb : (Work.BoseFixR.dil v μ) ^ ((1 : ℝ) / 1292) ≤ 1 :=
    Real.rpow_le_one hD0.le hD1 (by norm_num)
  have hb0 : (0 : ℝ) ≤ (Work.BoseFixR.dil v μ) ^ ((1 : ℝ) / 1292) :=
    Real.rpow_nonneg hD0.le _
  rw [show (1 : ℝ) / 646 = (1 : ℝ) / 1292 + (1 : ℝ) / 1292 by norm_num]
  rw [Real.rpow_add hD0]
  exact mul_le_of_le_one_right hb0 hb

/-- The third cutoff row: `c₁ + ε_T c₂ ≤ 1` from `0 < D ≤ 1`, `D^{1/1292} ≤ 1/1024` and
`√(μ/ρ) ≤ 2`. -/
lemma bogC1_add_eT_mul_bogC2_le_one (v : E3 → ℝ) (ρ μ : ℝ) (hav : 0 < _root_.BoseGases.a v)
    (hμ : 0 < μ) (hρ : 0 < ρ) (hD0 : 0 < Work.BoseFixR.dil v μ)
    (hD1 : Work.BoseFixR.dil v μ ≤ 1)
    (hDs : (Work.BoseFixR.dil v μ) ^ ((1 : ℝ) / 1292) ≤ 1 / 1024)
    (hs : Real.sqrt (μ / ρ) ≤ 2) :
    bogC1 v ρ μ + (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).eT * bogC2 v ρ μ ≤ 1 := by
  have hc1 := bogC1_eq_dil v ρ μ hav hμ hρ hD0
  have hc2 := bogC2_eq_dil v ρ μ hav hμ hρ hD0
  have heT := eT_mul_dil v μ hD0
  have hD := dil_rpow_646_le_1292 v μ hD0 hD1
  have hA0 : (0 : ℝ) ≤ (Work.BoseFixR.dil v μ) ^ ((1 : ℝ) / 646) := Real.rpow_nonneg hD0.le _
  have hB0 : (0 : ℝ) ≤ (Work.BoseFixR.dil v μ) ^ ((1 : ℝ) / 1292) := Real.rpow_nonneg hD0.le _
  have hc : (0 : ℝ) ≤ (1 / 2) * ((Work.BoseFixR.dil v μ) ^ ((1 : ℝ) / 646)
      + (Work.BoseFixR.dil v μ) ^ ((1 : ℝ) / 1292)) :=
    mul_nonneg (by norm_num) (add_nonneg hA0 hB0)
  rw [hc1, hc2]
  have hpull : (1 / 2) * (Work.BoseFixR.dil v μ) ^ ((1 : ℝ) / 646) * Real.sqrt (μ / ρ)
        + (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).eT
          * ((1 / 2) * (Work.BoseFixR.dil v μ) ^ (-(11 / 646) : ℝ) * Real.sqrt (μ / ρ))
      = (1 / 2) * ((Work.BoseFixR.dil v μ) ^ ((1 : ℝ) / 646)
          + (Work.BoseFixR.dil v μ) ^ ((1 : ℝ) / 1292)) * Real.sqrt (μ / ρ) := by
    rw [show (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).eT
          * ((1 / 2) * (Work.BoseFixR.dil v μ) ^ (-(11 / 646) : ℝ) * Real.sqrt (μ / ρ))
        = (1 / 2) * ((Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).eT
            * (Work.BoseFixR.dil v μ) ^ (-(11 / 646) : ℝ)) * Real.sqrt (μ / ρ) from by ring,
      heT]
    ring
  rw [hpull]
  calc (1 / 2) * ((Work.BoseFixR.dil v μ) ^ ((1 : ℝ) / 646)
          + (Work.BoseFixR.dil v μ) ^ ((1 : ℝ) / 1292)) * Real.sqrt (μ / ρ)
      ≤ (1 / 2) * ((Work.BoseFixR.dil v μ) ^ ((1 : ℝ) / 646)
          + (Work.BoseFixR.dil v μ) ^ ((1 : ℝ) / 1292)) * 2 :=
        mul_le_mul_of_nonneg_left hs hc
    _ = (Work.BoseFixR.dil v μ) ^ ((1 : ℝ) / 646)
          + (Work.BoseFixR.dil v μ) ^ ((1 : ℝ) / 1292) := by ring
    _ ≤ 1 := by linarith [hD, hDs]

/-- **The three cutoff rows of `FsI1Regime` at the honest kernel.**

`0 ≤ c₁`, `c₁ ≤ c₂` and `c₁ + ε_T c₂ ≤ 1` for `c₁ = bogC1 v ρ μ`, `c₂ = bogC2 v ρ μ`,
`ε_T = (paramsAt μ (a v)).eT`.

Route.  `Work.BoseBogFS.core_bounds` gives `Core v R μ ρ`, in particular `0 < ρ`,
`0 < μ`, `0 ≤ √(μ/ρ) ≤ 2` (`Core.hρsqrt`), `d ≤ 1` (`Core.hD1` + `paramsAt_d`) and
`B := D^{1/1292} ≤ 1/1024` (`Core.hDs`).  The two identities
`Work.BoseBogFS.bogC1_eq` and `Work.BoseBogFS.bogC2_eq` give
`c₁ = ½(K_ℓs)⁻¹√(μ/ρ) = ½D^{1/646}√(μ/ρ)` (`Work.BoseBogFS.sKl_inv`) and
`c₂ = ½(K_ℓds)⁻¹√(μ/ρ) = ½D^{-11/646}√(μ/ρ)` (`Work.BoseBogFS.dsKl_eq`), so
`0 ≤ c₁` and `c₁ ≤ c₂` follow from `d ≤ 1` and positivity.  For the third row use
`Work.BoseBogFS.eT_dsKl_inv` (`ε_T(K_ℓds)⁻¹ = D^{1/1292}`) plus `sKl_inv`:
`c₁ + ε_Tc₂ = ½(D^{1/646} + D^{1/1292})√(μ/ρ) ≤ D^{1/646} + D^{1/1292} ≤ 2·(1/1024) ≤ 1`
(`D^{1/646} = (D^{1/1292})² ≤ D^{1/1292}` since `D ≤ 1`).  No threshold beyond
`coreBound v R`; `ε₀ = coreBound v R` works. -/
theorem honestFsCutoffRows {v : EuclideanSpace ℝ (Fin 3) → ℝ} {R : ℝ} (hR : 0 < R)
    (hav : 0 < _root_.BoseGases.a v) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ → ∀ ρ : ℝ,
      Work.BoseBoxFock.CloseCondFS v μ ρ →
      0 ≤ Work.BoseBogFS.bogC1 v ρ μ ∧
      Work.BoseBogFS.bogC1 v ρ μ ≤ Work.BoseBogFS.bogC2 v ρ μ ∧
      Work.BoseBogFS.bogC1 v ρ μ
          + (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).eT
            * Work.BoseBogFS.bogC2 v ρ μ ≤ 1 := by
  refine ⟨coreBound v R, coreBound_pos hR hav, ?_⟩
  intro μ hAdm ρ hclose
  have hμ : 0 < μ := hAdm.1
  have hcore : Core v R μ ρ :=
    core_bounds hR hav (le_refl (coreBound v R)) μ ρ hμ hAdm.2.1 hclose
  have hD0 : 0 < Work.BoseFixR.dil v μ := hcore.hD0
  have hc1 := bogC1_eq_dil v ρ μ hav hμ hcore.hρ0 hD0
  have hc2 := bogC2_eq_dil v ρ μ hav hμ hcore.hρ0 hD0
  have hD := dil_rpow_646_le_neg11_646 v μ hD0 hcore.hD1
  refine ⟨?_, ?_, ?_⟩
  · rw [hc1]
    exact mul_nonneg (mul_nonneg (by norm_num) (Real.rpow_nonneg hD0.le _))
      (Real.sqrt_nonneg _)
  · rw [hc1, hc2]
    have hs : (0 : ℝ) ≤ (1 / 2) * Real.sqrt (μ / ρ) :=
      mul_nonneg (by norm_num) (Real.sqrt_nonneg _)
    calc (1 / 2) * (Work.BoseFixR.dil v μ) ^ ((1 : ℝ) / 646) * Real.sqrt (μ / ρ)
        = (Work.BoseFixR.dil v μ) ^ ((1 : ℝ) / 646)
            * ((1 / 2) * Real.sqrt (μ / ρ)) := by ring
      _ ≤ (Work.BoseFixR.dil v μ) ^ (-(11 / 646) : ℝ)
            * ((1 / 2) * Real.sqrt (μ / ρ)) :=
          mul_le_mul_of_nonneg_right hD hs
      _ = (1 / 2) * (Work.BoseFixR.dil v μ) ^ (-(11 / 646) : ℝ) * Real.sqrt (μ / ρ) := by ring
  · exact bogC1_add_eT_mul_bogC2_le_one v ρ μ hav hμ hcore.hρ0 hD0 hcore.hD1 hcore.hDs
      hcore.hρsqrt

end

end Work.BoseBogFS
