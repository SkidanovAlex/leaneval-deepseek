import ChallengeDeps
import Submission.Work.BoseFixB1B.perBoxIntegrated
import Submission.Work.BoseFixB1B.trimOffInterior
import Submission.Work.BoseFixB1B.w1MassB_integral_le_holds
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseFixB1.smallBoxCollectedC_holds` — FS `thm:smallbox` integrated

Target (unchanged, as handed over): FS's Appendix per-small-box bound
(`thm:smallbox`, `final_v2.tex` l.3907) summed over the sliding boxes
`B(u) = dlBox ℓ d u`, with FS's convexity constant `c` carried *explicitly* on
`R_Ψ` (route (2) of `FINDING_RPsiB_c_normalisation.md`: the coefficient-`1`
form `SmallBoxCollected` is false because the per-box bound only produces
`c·R_Ψ ≤ ∫_u H_{B(u)} + …` with `c ≤ 1/2`).

## Decomposition

Writing `A := 4πμ²(a v)ℓ³`, `κ := K_B³(μ(a v)³)^{1/2}`, `nB := ‖Φ‖²` and `I₋`
for the interior set, the three analytic pieces are

* `Work.BoseFixB1B.perBoxIntegrated` — FS `thm:smallbox` integrated over `I₋`:

    `c₁·R_Ψ ≤ ∫_{I₋} H_{B(u)}(Φ) du + ½μ²(∫_{I₋}∬w_{1,B(u)})nB + C₁·μ²(a v)ℓ³κ·nB`;

* `Work.BoseFixB1B.w1MassB_integral_le_holds` — FS `eq:appw1sliding` with error:

    `∫_{I₋}∬w_{1,B(u)} du ≤ 8π(a v)ℓ³(1 + C₂κ)`;

  the point of the `½` and the `8π` is exactly `½μ²·8π(a v)ℓ³ = A`;

* `Work.BoseFixB1B.trimOffInterior` — the band/far-set bookkeeping (FS
  `eq:badset`), replacing `∫_{I₋}` by `∫_{ℝ³}`:

    `∫_{I₋} H_{B(u)} ≤ ∫_{ℝ³} H_{B(u)} + C₃·μ²(a v)ℓ³κ·nB`.

The constants are then pure arithmetic:
`c₁ R_Ψ ≤ ∫_{ℝ³} H_{B(u)} + A(1 + C₂κ)nB + (C₁+C₃)μ²(a v)ℓ³κ nB`, and
`μ²(a v)ℓ³κ = (A/4π)κ` folds the last two into `A(1 + (C₂ + (C₁+C₃)/4π)κ)nB`.
Finally `0 ≤ R_Ψ` is `Work.BoseFixB1.rPsiB_nonneg`.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped Topology Real BigOperators ENNReal

namespace Work.BoseFixB1

open _root_.BoseGases Submission.BoseGases Work.BoseBoxFix Work.BoseBox Work.UBB
open Work.SmallBoxSliding

set_option autoImplicit false
set_option linter.unusedVariables false

/-- **The constant arithmetic of the assembly.**  Given FS's three numeric inputs
at `A = 4πμ²aℓ³` and `κ` (an arbitrary nonnegative number here),

* `W ≤ 8πaℓ³(1 + C₂κ)` (`eq:appw1sliding`),
* `c * R ≤ I + ½μ²·W·nB + C₁·(μ²aℓ³κ)·nB` (`thm:smallbox`),
* `I ≤ I' + C₃·(μ²aℓ³κ)·nB` (`eq:badset`),

the target's inequality `c * R ≤ I' + A(1 + Cκ)nB` follows with
`C := C₂ + (C₁+C₃)/(4π)`.  The only content is `½μ²·8πaℓ³ = A` and
`μ²aℓ³κ = (A/4π)·κ`. -/
private lemma arith_absorb {a ℓ KB t μ nB I I' R W Cp Cm Ct c : ℝ}
    (hπ : 0 < Real.pi) (hκ : 0 ≤ KB ^ 3 * t) (hnB : 0 ≤ nB) (hμ : 0 < μ)
    (ha : 0 ≤ a) (hℓ : 0 ≤ ℓ)
    (hW : W ≤ 8 * Real.pi * a * ℓ ^ 3 * (1 + Cm * KB ^ 3 * t))
    (hcore : c * R ≤ I + (1 / 2) * μ ^ 2 * W * nB
        + Cp * (μ ^ 2 * a * ℓ ^ 3 * KB ^ 3 * t) * nB)
    (htrim : I ≤ I' + Ct * (μ ^ 2 * a * ℓ ^ 3 * KB ^ 3 * t) * nB) :
    c * R ≤ I' + 4 * Real.pi * μ ^ 2 * a * ℓ ^ 3
        * (1 + (Cm + (Cp + Ct) / (4 * Real.pi)) * KB ^ 3 * t) * nB := by
  -- `½μ²·W·nB ≤ A(1+C₂κ)nB`
  have hf : 0 ≤ (1 / 2) * μ ^ 2 := by positivity
  have h1 : (1 / 2) * μ ^ 2 * W * nB
      ≤ (1 / 2) * μ ^ 2 * (8 * Real.pi * a * ℓ ^ 3 * (1 + Cm * KB ^ 3 * t)) * nB :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hW hf) hnB
  have h2 : (1 / 2) * μ ^ 2 * (8 * Real.pi * a * ℓ ^ 3 * (1 + Cm * KB ^ 3 * t)) * nB
      = 4 * Real.pi * μ ^ 2 * a * ℓ ^ 3 * (1 + Cm * KB ^ 3 * t) * nB := by ring
  -- the three terms combine into the target coefficient
  have h5 : 4 * Real.pi * μ ^ 2 * a * ℓ ^ 3 * (1 + Cm * KB ^ 3 * t) * nB
        + Cp * (μ ^ 2 * a * ℓ ^ 3 * KB ^ 3 * t) * nB
        + Ct * (μ ^ 2 * a * ℓ ^ 3 * KB ^ 3 * t) * nB
      = 4 * Real.pi * μ ^ 2 * a * ℓ ^ 3
        * (1 + (Cm + (Cp + Ct) / (4 * Real.pi)) * KB ^ 3 * t) * nB := by
    have hπ' : Real.pi ≠ 0 := ne_of_gt hπ
    field_simp
    ring
  linarith [hcore, htrim, h1, h2.le, h5.le]

/-- FS `thm:smallbox` summed over the sliding small boxes (with FS's convexity
constant `c` on `R_Ψ`), see the module docstring for the decomposition. -/
theorem smallBoxCollectedC_holds {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v)
    (hv : 0 ≤ v) (hv1 : MeasureTheory.MemLp v 1) (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ}
    (hR : 0 < R) (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    (hav : 0 < _root_.BoseGases.a v) {J : ℝ} (hJ : Work.UBB.lhyC ≤ J) :
    ∃ ε₀ C c : ℝ, 0 < ε₀ ∧ 0 ≤ C ∧ 0 < c ∧ ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
      J ≤ (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).KB ^ 3 →
      ∀ (n : ℕ) (Φ : Work.BoseKinLoc.BoxState n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))),
        Work.BoseBoxFix.IsLowB v h J μ n Φ →
          0 ≤ Work.BoseFixB1.RPsi v h μ (Φ : Submission.BoseGases.X n → ℝ) ∧
          c * Work.BoseFixB1.RPsi v h μ (Φ : Submission.BoseGases.X n → ℝ)
            ≤ (∫ u : EuclideanSpace ℝ (Fin 3),
                Work.BoseFixB1.sbWord h μ u (Φ : Submission.BoseGases.X n → ℝ))
              + 4 * Real.pi * μ ^ 2 * (_root_.BoseGases.a v)
                  * Work.BoseBox.sideAt μ (_root_.BoseGases.a v) ^ 3
                  * (1 + C * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).KB ^ 3
                      * (μ * (_root_.BoseGases.a v) ^ 3) ^ (1 / 2 : ℝ))
                  * Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ) := by
  obtain ⟨εp, cp, Cp, hεp, hcp, hCp, hP⟩ :=
    Work.BoseFixB1B.perBoxIntegrated h hv hv1 hvrad hR hv_supp hav hJ
  obtain ⟨εm, Cm, hεm, hCm, hm⟩ :=
    Work.BoseFixB1B.w1MassB_integral_le_holds h hv hv1 hvrad hR hv_supp hav
  obtain ⟨εt, Ct, hεt, hCt, ht⟩ :=
    Work.BoseFixB1B.trimOffInterior h hv hv1 hvrad hR hv_supp hav hJ
  refine ⟨min εp (min εm εt), Cm + (Cp + Ct) / (4 * Real.pi), cp,
    lt_min hεp (lt_min hεm hεt), ?_, hcp, ?_⟩
  · have hnum : 0 ≤ Cp + Ct := by linarith
    have : 0 ≤ (Cp + Ct) / (4 * Real.pi) := div_nonneg hnum (by positivity)
    linarith
  · intro μ hAdm hJK n Φ hlow
    have hAdmp : Work.BoseBoxFix.Adm v εp μ := Work.BoseFixB1.Adm.mono hAdm (min_le_left _ _)
    have hAdmm : Work.BoseBoxFix.Adm v εm μ :=
      Work.BoseFixB1.Adm.mono hAdm (le_trans (min_le_right _ _) (min_le_left _ _))
    have hAdmt : Work.BoseBoxFix.Adm v εt μ :=
      Work.BoseFixB1.Adm.mono hAdm (le_trans (min_le_right _ _) (min_le_right _ _))
    have hcore := hP μ hAdmp n Φ hlow
    have hmass := hm μ hAdmm
    have htrim := ht μ hAdmt hJK n Φ hlow
    refine ⟨?_, ?_⟩
    · have hM : 1 ≤ (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M := by
        rw [Work.BoseFixB1.paramsAt_eq_fsParams]
        norm_num [Work.BoseBox.fsParams, Work.BoseBox.mValue]
      have hMu : 0 < μ := Work.BoseFixB1.adm_mu_pos hAdm
      have hℓ : 0 < Work.BoseBox.sideAt μ (_root_.BoseGases.a v) :=
        Work.BoseFixB1.adm_ell_pos hAdm
      have hd : 0 < (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d :=
        Work.BoseFixB1.adm_d_pos hAdm
      exact Work.BoseFixB1.rPsiB_nonneg h hv hv1 hvrad hR hv_supp hMu hM (by norm_num) hℓ hd
        (Φ : Submission.BoseGases.X n → ℝ)
    · have hκ : 0 ≤ (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).KB ^ 3
          * (μ * (_root_.BoseGases.a v) ^ 3) ^ (1 / 2 : ℝ) :=
        mul_nonneg (pow_nonneg (le_of_lt (Work.BoseFixB1.paramsAt_KB_pos hAdm)) 3)
          (Real.rpow_nonneg (mul_nonneg (le_of_lt (Work.BoseFixB1.adm_mu_pos hAdm))
            (pow_nonneg (le_of_lt hav) 3)) _)
      have hnB : 0 ≤ Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ) :=
        Work.BoseFixB1.normB_nonneg _
      exact arith_absorb (μ := μ) (a := _root_.BoseGases.a v)
        (ℓ := Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
        (KB := (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).KB)
        (t := (μ * (_root_.BoseGases.a v) ^ 3) ^ (1 / 2 : ℝ))
        (nB := Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ))
        (I := ∫ u in Work.SmallBoxSliding.interiorSet
                (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d μ,
                Work.BoseFixB1.sbWord h μ u (Φ : Submission.BoseGases.X n → ℝ))
        (I' := ∫ u : EuclideanSpace ℝ (Fin 3),
                Work.BoseFixB1.sbWord h μ u (Φ : Submission.BoseGases.X n → ℝ))
        (R := Work.BoseFixB1.RPsi v h μ (Φ : Submission.BoseGases.X n → ℝ))
        (W := ∫ u in Work.SmallBoxSliding.interiorSet
                (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d μ,
                Work.BoseFixB1.w1MassB h (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
                  (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                  (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
        (Cp := Cp) (Cm := Cm) (Ct := Ct) (c := cp)
        Real.pi_pos hκ hnB (Work.BoseFixB1.adm_mu_pos hAdm) (le_of_lt hav)
        (le_of_lt (Work.BoseFixB1.adm_ell_pos hAdm)) hmass hcore htrim

end Work.BoseFixB1
