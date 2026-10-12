import ChallengeDeps
import Submission.Work.BoseB1Cube.CubeRows
import Submission.Work.BoseB1Cube.gammaRegimeAt
import Submission.Work.BoseFixB1.boxMass_pos_of_goodSet
import Submission.Work.BoseFixB1B.coreMassLower
import Submission.Work.BoseFixB1B.sectorCountDefs
import Submission.Work.BoseFixB1S.sbCut_cube_eq
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseB1Cube.r3RowOfMassRow`

The `R₃` column of the cube Bogoliubov port, in the **free-mass-row** form: instead of deriving
the one-body mass row `c·(a v)·∫χ_B² ≤ ∬w_{1,B(u)}` from deep-position geometry (as
`Work.BoseB1Cube.coreR3A` does, through `Work.BoseB1Cube.deepW1MassGe` and the centre hypothesis
`|((ℓd)•u)_j| ≤ ℓ/16`), the row is taken as a **hypothesis** with an *arbitrary* positive constant
`K`:

    K·(a v)·χ ≤ W ,   n ≤ 2·Cₙ·μ·|B(u)|      ⟹      2·c³·(n/|B(u)|)·χ ≤ μ²·Γ·W ,

where `c = sbCut μ (a v)`, `χ = chiMass (PBM,PBℓ,PBd) u`, `W = PBW h μ u = ∬w_{1,B(u)}` and
`Γ = PBΓ v μ = K_B³(μ(a v)³)^{1/2}`.

The proof is the pure-real accounting already isolated inside `coreR3A`: the monomial gate
`Cₙ·c³ ≤ (K/4)·(a v)·(μΓ)`, i.e. `X^{3/2} ≤ K(a v)/(4Cₙ)` with `X = (μ(a v)³)^{1/323}`, holds below
the diluteness threshold `(K(a v)/(4Cₙ))^{646/3}`; then

    2·c³·(n/V)·χ ≤ 4Cₙ·c³·μ·χ ≤ (4Cₙ·c³·μ/(K a v))·W ≤ μ²Γ·W ,

the middle step using the mass row, the last one the gate.  Both inputs
(`sbCut_cube_le_gamma`, `coreR3_accounting`) are `private` in `Submission/Work/BoseB1Cube/coreR3A.lean`
and are therefore re-established here verbatim, with the arbitrary `K` in place of the fixed
`cdeep` of `deepW1MassGe`.
-/

namespace Work.BoseB1Cube

open MeasureTheory Metric
open scoped Real BigOperators ENNReal Topology

set_option autoImplicit false
set_option linter.unusedVariables false

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-! ## 1. The diluteness monomial `Cₙ c³ ≤ (K/4)·a·(μΓ)` -/

/-- **The monomial gate of the `R₃` column** (free mass-row constant `K`).  For fixed `A > 0`,
`Cₙ > 0`, `K > 0`, if the diluteness is at most `(KA/(4Cₙ))^{646/3}` then FS's spectral cut-off
is dominated by the (free) mass row:

    `Cₙ · (sbCut μ A)³  ≤  (K/4) · (A · (μ · K_B³(μA³)^{1/2}))`.

Indeed `(sbCut μ A)³ = A^{-3}X^{468}` and `μ K_B³(μA³)^{1/2} = A^{-3}X^{933/2}`
(`X = (μA³)^{1/323}`, `μ = X^{323}/A³`), so the claim is exactly `X^{3/2} ≤ KA/(4Cₙ)`. -/
private lemma sbCut_cube_le_gammaR {A Cn K μ : ℝ} (hA : 0 < A) (hCn : 0 < Cn) (hK : 0 < K)
    (hμ : 0 < μ)
    (ht : μ * A ^ 3 ≤ (K * A / (4 * Cn)) ^ (646 / 3 : ℝ)) :
    Cn * (Work.BoseFixB1.sbCut μ A) ^ 3
      ≤ (K / 4) * (A * (μ * ((Work.BoseBox.paramsAt μ A).KB ^ 3
          * (μ * A ^ 3) ^ (1 / 2 : ℝ)))) := by
  have ht0 : 0 < μ * A ^ 3 := by positivity
  have hA3 : 0 < A ^ 3 := by positivity
  have hA3ne : A ^ 3 ≠ 0 := ne_of_gt hA3
  -- ## the cutoff side as a monomial in `fsXp (μA³)`
  have hcut : (Work.BoseFixB1.sbCut μ A) ^ 3
      = (A ^ 3)⁻¹ * (Work.BoseBox.fsXp (μ * A ^ 3) (933 / 2)
          * Work.BoseBox.fsXp (μ * A ^ 3) (3 / 2)) := by
    rw [Work.BoseFixB1S.sbCut_cube_eq hA hμ]
    show (A ^ 3)⁻¹ * (Work.BoseBox.fsXp (μ * A ^ 3) 1) ^ 468
        = (A ^ 3)⁻¹ * (Work.BoseBox.fsXp (μ * A ^ 3) (933 / 2)
            * Work.BoseBox.fsXp (μ * A ^ 3) (3 / 2))
    rw [Work.BoseBox.fsXp_pow ht0.le]
    rw [show (1 : ℝ) * ((468 : ℕ) : ℝ) = 933 / 2 + 3 / 2 by norm_num,
      Work.BoseBox.fsXp_mul ht0]
  have hΓ : (Work.BoseBox.paramsAt μ A).KB ^ 3 * (μ * A ^ 3) ^ (1 / 2 : ℝ)
      = Work.BoseBox.fsXp (μ * A ^ 3) (287 / 2) := Work.BoseFixB1.KB3_half_eq hA hμ
  have hsplit : Work.BoseBox.fsXp (μ * A ^ 3) 323 * Work.BoseBox.fsXp (μ * A ^ 3) (287 / 2)
      = Work.BoseBox.fsXp (μ * A ^ 3) (933 / 2) := by
    rw [Work.BoseBox.fsXp_mul ht0]
    norm_num
  -- ## the mass-row side as a monomial in `fsXp (μA³)`
  have hmuΓ : μ * ((Work.BoseBox.paramsAt μ A).KB ^ 3 * (μ * A ^ 3) ^ (1 / 2 : ℝ))
      = (A ^ 3)⁻¹ * Work.BoseBox.fsXp (μ * A ^ 3) (933 / 2) := by
    rw [hΓ, ← hsplit, ← Work.BoseBox.delta_eq_fsXp ht0.le]
    rw [show (A ^ 3)⁻¹ * (μ * A ^ 3 * Work.BoseBox.fsXp (μ * A ^ 3) (287 / 2))
        = (A ^ 3)⁻¹ * (A ^ 3 * (μ * Work.BoseBox.fsXp (μ * A ^ 3) (287 / 2))) by ring,
      inv_mul_cancel_left₀ hA3ne]
  -- ## the monomial comparison `X^{3/2} ≤ KA/(4Cn)`
  have hx0 : 0 ≤ K * A / (4 * Cn) :=
    div_nonneg (mul_nonneg hK.le hA.le) (mul_pos (by norm_num) hCn).le
  have hpow : Work.BoseBox.fsXp (μ * A ^ 3) (3 / 2) ≤ K * A / (4 * Cn) := by
    have h1 : Work.BoseBox.fsXp (μ * A ^ 3) (3 / 2) = (μ * A ^ 3) ^ (3 / 646 : ℝ) := by
      rw [Work.BoseBox.fsXp]
      norm_num
    have h2 : ((K * A / (4 * Cn)) ^ (646 / 3 : ℝ)) ^ (3 / 646 : ℝ) = K * A / (4 * Cn) := by
      rw [← Real.rpow_mul hx0 (646 / 3) (3 / 646),
        show (646 / 3 : ℝ) * (3 / 646) = 1 by norm_num, Real.rpow_one]
    rw [h1]
    calc (μ * A ^ 3) ^ (3 / 646 : ℝ)
        ≤ ((K * A / (4 * Cn)) ^ (646 / 3 : ℝ)) ^ (3 / 646 : ℝ) :=
          Real.rpow_le_rpow ht0.le ht (by norm_num)
      _ = K * A / (4 * Cn) := h2
  have hmain : Cn * Work.BoseBox.fsXp (μ * A ^ 3) (3 / 2) ≤ (K / 4) * A := by
    have h := mul_le_mul_of_nonneg_left hpow hCn.le
    have he : Cn * (K * A / (4 * Cn)) = (K / 4) * A := by
      field_simp [ne_of_gt hCn]
    linarith [h, he]
  -- ## assemble
  have hKf : 0 ≤ (A ^ 3)⁻¹ * Work.BoseBox.fsXp (μ * A ^ 3) (933 / 2) :=
    mul_nonneg (inv_nonneg.mpr (pow_nonneg hA.le 3)) (Work.BoseBox.fsXp_nonneg ht0.le)
  calc Cn * (Work.BoseFixB1.sbCut μ A) ^ 3
      = (Cn * Work.BoseBox.fsXp (μ * A ^ 3) (3 / 2))
          * ((A ^ 3)⁻¹ * Work.BoseBox.fsXp (μ * A ^ 3) (933 / 2)) := by
        rw [hcut]
        ring
    _ ≤ ((K / 4) * A) * ((A ^ 3)⁻¹ * Work.BoseBox.fsXp (μ * A ^ 3) (933 / 2)) :=
        mul_le_mul_of_nonneg_right hmain hKf
    _ = (K / 4) * (A * (μ * ((Work.BoseBox.paramsAt μ A).KB ^ 3
          * (μ * A ^ 3) ^ (1 / 2 : ℝ)))) := by
        rw [hmuΓ]
        ring

/-! ## 2. The pure-real accounting of the two mechanisms -/

/-- **The `R₃` accounting** (free mass-row constant `K`).  Given the three inequalities

* `n ≤ 2 C_n μ V` (the count window),
* `K a χ ≤ W` (the free one-body mass row),
* `C_n c³ ≤ (K/4)·a·(μ Γ)` (the monomial gate of §1),

one has `2 c³ (n/V) χ ≤ μ² Γ W`. -/
private lemma coreR3_accountingR {c Cn μ V chi Γ W av K : ℝ} {n : ℕ}
    (hc : 0 < c) (hCn : 0 < Cn) (hK : 0 < K) (hav : 0 < av) (hμ : 0 < μ) (hV : 0 < V)
    (hchi : 0 ≤ chi) (hW : 0 ≤ W)
    (hn : (n : ℝ) ≤ 2 * Cn * μ * V)
    (hmass : K * av * chi ≤ W)
    (hgate : Cn * c ^ 3 ≤ (K / 4) * (av * (μ * Γ))) :
    2 * c ^ 3 * ((n : ℝ) / V) * chi ≤ μ ^ 2 * Γ * W := by
  have hKavne : K * av ≠ 0 := ne_of_gt (mul_pos hK hav)
  have hdiv : (n : ℝ) / V ≤ 2 * Cn * μ := (div_le_iff₀ hV).mpr hn
  have hchi_le : chi ≤ W / (K * av) := by
    rw [le_div_iff₀ (mul_pos hK hav), mul_comm]
    exact hmass
  have hcoef : 4 * Cn * c ^ 3 * μ / (K * av) ≤ μ ^ 2 * Γ := by
    have h1 : 0 ≤ 4 * μ / (K * av) := by positivity
    have h2 := mul_le_mul_of_nonneg_left hgate h1
    have e1 : 4 * μ / (K * av) * (Cn * c ^ 3) = 4 * Cn * c ^ 3 * μ / (K * av) := by
      field_simp [hKavne]
    have e2 : 4 * μ / (K * av) * (K / 4 * (av * (μ * Γ))) = μ ^ 2 * Γ := by
      field_simp [hKavne]
    linarith [h2, e1, e2]
  have hstep1 : 2 * c ^ 3 * ((n : ℝ) / V) * chi ≤ 4 * Cn * c ^ 3 * μ * chi := by
    have hnn : 0 ≤ 2 * c ^ 3 * chi :=
      mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hc.le 3)) hchi
    calc 2 * c ^ 3 * ((n : ℝ) / V) * chi = (2 * c ^ 3 * chi) * ((n : ℝ) / V) := by ring
      _ ≤ (2 * c ^ 3 * chi) * (2 * Cn * μ) := mul_le_mul_of_nonneg_left hdiv hnn
      _ = 4 * Cn * c ^ 3 * μ * chi := by ring
  have hstep2 : 4 * Cn * c ^ 3 * μ * chi ≤ (4 * Cn * c ^ 3 * μ / (K * av)) * W := by
    have hnn : 0 ≤ 4 * Cn * c ^ 3 * μ :=
      mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hCn.le) (pow_nonneg hc.le 3)) hμ.le
    calc 4 * Cn * c ^ 3 * μ * chi ≤ 4 * Cn * c ^ 3 * μ * (W / (K * av)) :=
          mul_le_mul_of_nonneg_left hchi_le hnn
      _ = (4 * Cn * c ^ 3 * μ / (K * av)) * W := by ring
  linarith [hstep1, hstep2, mul_le_mul_of_nonneg_right hcoef hW]

/-! ## 3. The row -/

theorem r3RowOfMassRow {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v)
    (hv : 0 ≤ v) (hv1 : MeasureTheory.MemLp v 1) (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ}
    (hR : 0 < R) (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    (hav : 0 < _root_.BoseGases.a v) (K : ℝ) (hK : 0 < K) {Cn : ℝ} (hCn : 4 ≤ Cn) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ {μ : ℝ}, Work.BoseBoxFix.Adm v ε₀ μ →
      ∀ u : EuclideanSpace ℝ (Fin 3),
        u ∈ Work.SmallBoxSliding.goodSet (Work.BoseFixB1B.PBℓ v μ) (Work.BoseFixB1B.PBd v μ) μ →
        ∀ {n : ℕ}, (n : ℝ) ≤ 2 * Cn * μ * Work.BoseFixB1B.PBBV v μ u →
          K * (_root_.BoseGases.a v)
              * Work.SmallBoxSliding.chiMass (Work.BoseFixB1B.PBM v μ)
                  (Work.BoseFixB1B.PBℓ v μ) (Work.BoseFixB1B.PBd v μ) u
            ≤ Work.BoseFixB1B.PBW h μ u →
          2 * (Work.BoseFixB1.sbCut μ (_root_.BoseGases.a v)) ^ 3
              * ((n : ℝ) / Work.BoseFixB1B.PBBV v μ u)
              * Work.SmallBoxSliding.chiMass (Work.BoseFixB1B.PBM v μ)
                  (Work.BoseFixB1B.PBℓ v μ) (Work.BoseFixB1B.PBd v μ) u
            ≤ μ ^ 2 * Work.BoseFixB1B.PBΓ v μ * Work.BoseFixB1B.PBW h μ u := by
  have hCnpos : 0 < Cn := lt_of_lt_of_le (by norm_num) hCn
  have hx0 : 0 < K * (_root_.BoseGases.a v) / (4 * Cn) :=
    div_pos (mul_pos hK hav) (mul_pos (by norm_num) hCnpos)
  refine ⟨(K * (_root_.BoseGases.a v) / (4 * Cn)) ^ (646 / 3 : ℝ),
    Real.rpow_pos_of_pos hx0 _, ?_⟩
  intro μ hAdm u hu n hn hmassRow
  have hμ : 0 < μ := hAdm.1
  have hℓ : 0 < Work.BoseFixB1B.PBℓ v μ := Work.BoseFixB1.adm_ell_pos hAdm
  have hd : 0 < Work.BoseFixB1B.PBd v μ := Work.BoseFixB1.adm_d_pos hAdm
  -- ## the gate, at the fixed `K`
  have hgate := sbCut_cube_le_gammaR (A := _root_.BoseGases.a v) (Cn := Cn) (K := K) (μ := μ)
    hav hCnpos hK hμ hAdm.2.1
  have hgate' : Cn * (Work.BoseFixB1.sbCut μ (_root_.BoseGases.a v)) ^ 3
      ≤ (K / 4) * (_root_.BoseGases.a v * (μ * Work.BoseFixB1B.PBΓ v μ)) := by
    simpa only [Work.BoseFixB1B.PBΓ, Work.BoseFixB1B.PBKB, Work.FockBridge.dlGamma] using hgate
  -- ## the elementary facts of the box
  have hV : 0 < Work.BoseFixB1B.PBBV v μ u :=
    Work.BoseFixB1.boxMass_pos_of_goodSet hℓ hd hμ hu
  have hchi0 : 0 ≤ Work.SmallBoxSliding.chiMass (Work.BoseFixB1B.PBM v μ)
      (Work.BoseFixB1B.PBℓ v μ) (Work.BoseFixB1B.PBd v μ) u :=
    Work.SmallBoxSliding.chiMass_nonneg _ _ _ _
  have hW0 : 0 ≤ Work.BoseFixB1B.PBW h μ u := by
    simpa only [Work.BoseFixB1B.PBW] using
      Work.BoseFixB1.w1MassB_nonneg h hv hvrad hR hv_supp hℓ hd u
  have hc0 : 0 < Work.BoseFixB1.sbCut μ (_root_.BoseGases.a v) := by
    rw [Work.BoseFixB1.sbCut]
    exact inv_pos.mpr (mul_pos (mul_pos hd (Work.BoseFixB1.adm_s_pos hAdm)) hℓ)
  exact coreR3_accountingR (c := Work.BoseFixB1.sbCut μ (_root_.BoseGases.a v)) (Cn := Cn)
    (μ := μ) (V := Work.BoseFixB1B.PBBV v μ u) (chi := Work.SmallBoxSliding.chiMass
      (Work.BoseFixB1B.PBM v μ) (Work.BoseFixB1B.PBℓ v μ) (Work.BoseFixB1B.PBd v μ) u)
    (Γ := Work.BoseFixB1B.PBΓ v μ) (W := Work.BoseFixB1B.PBW h μ u)
    (av := _root_.BoseGases.a v) (K := K)
    hc0 hCnpos hK hav hμ hV hchi0 hW0 hn hmassRow hgate'

end Work.BoseB1Cube
