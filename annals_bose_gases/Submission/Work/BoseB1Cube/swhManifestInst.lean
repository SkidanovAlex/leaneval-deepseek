import ChallengeDeps
import Mathlib.Algebra.Order.Ring.Star
import Submission.Work.BoseB1Cube.smallWinNodes
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseB1Cube.swhManifestInst` — the manifest fibre instance

The per-`u` fibre bound of the sliding box at FS's parameters: the localised one-body fibre
integral `fibSum` is dominated by the manifest flat term `(W/V)·S` plus an `O(a)`-error carried by
the excited count `n₊ = bQ`:

    μ·fibSum ≤ μ·( (W/V)·flat + C·(a v)·(√(bQ·(W/V)·flat) + bQ) ) ,

uniformly over all admissible `μ`, all `u ∈ goodSet`, and all normalised box-supported smooth
states `Ψ`.

The proof is the instantiation of the PROVED `Work.BoseFixB1S.fibSum_le_manifest` (the
slot-decomposition `Φ = PᵢΦ + QᵢΦ`, with the `Q`-line paid by the count `n₊` and the cross line by
Cauchy–Schwarz) at the parameters of the sliding box, together with

* `Work.AprioriCount.boxM1_eq_w1MassB` — the box fibre mass `boxM1` of the localised kernel
  `wSmall1Pair` is the FS box mass `w1MassB` of `bW`,
* `Work.BoseFixB1S.boxQCount_eq_cnPlusBoxInd` and `bFlat = boxFlatCount` (definitional),
* the admissibility/regime gates `Work.BoseFixB1.regime_sideAt_ge` (`R ≤ ℓd/16`, `R ≤ ℓ·chiR0`),
  `Work.BoseFixB1.adm_{ell,d}_pos`, and `Work.BoseFixB1.boxMass_ge_deltaScale_of_goodSet`
  (`0 < |B(u)|` on the good set, so the volume normalisation is legitimate).
-/

namespace Work.BoseB1Cube

open MeasureTheory

set_option linter.unusedVariables false

theorem swhManifestInst {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v)
    (hv : 0 ≤ v) (hv1 : MeasureTheory.MemLp v 1) (hvrad : _root_.BoseGases.IsRadial v)
    {R : ℝ} (hR : 0 < R) (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    (hav : 0 < _root_.BoseGases.a v) (η : ℝ) (hη : 0 < η) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
      ∀ u : EuclideanSpace ℝ (Fin 3), u ∈ Work.SmallBoxSliding.goodSet (Work.BoseFixB1.bSide v μ)
          (Work.BoseFixB1.bD v μ) μ →
      ∀ {n : ℕ} (Ψ : Submission.BoseGases.X n → ℝ) (hΨc : ContDiff ℝ (⊤ : ℕ∞) Ψ)
        (hsupp : ∀ᵐ x ∂(MeasureTheory.volume.restrict (Submission.BoseGases.abox n
            (Work.BoseFixB1.bSide v μ))),
          Ψ x ≠ 0 → ∀ i : Fin n, x i ∈ Work.BoseFixB1.bA v μ u)
        (hnorm : (∫ x in Submission.BoseGases.abox n (Work.BoseFixB1.bSide v μ),
            (Ψ x) ^ 2) = 1),
        μ * Work.BoseFixB1.fibSum h (Work.BoseFixB1.bM v μ) (Work.BoseFixB1.bSide v μ)
            (Work.BoseFixB1.bD v μ) u Ψ
          ≤ μ * ((Work.BoseFixB1.bW v h μ u / Work.BoseFixB1.bV v μ u)
                * Work.BoseFixB1.bFlat v μ Ψ u
              + C * (_root_.BoseGases.a v)
                * (Real.sqrt (Work.BoseFixB1.bQ v μ Ψ u
                      * (Work.BoseFixB1.bW v h μ u / Work.BoseFixB1.bV v μ u)
                      * Work.BoseFixB1.bFlat v μ Ψ u)
                  + Work.BoseFixB1.bQ v μ Ψ u)) := by
  classical
  -- the manifest fibre bound at the box regularity `M = 48 = bM v μ`
  obtain ⟨C₁, hC₁0, hfib⟩ :=
    Work.BoseFixB1S.fibSum_le_manifest (v := v) h hv hv1 hvrad hR hv_supp hav (M := 48)
      (by norm_num)
  -- the dilute-regime threshold: `R ≤ ℓd/16` and `R ≤ ℓ·chiR0`
  obtain ⟨ε₁, hε₁0, hreg⟩ := Work.BoseFixB1.regime_sideAt_ge (v := v) hav hR
  refine ⟨C₁, hC₁0, min 1 ε₁, lt_min one_pos hε₁0, ?_⟩
  intro μ hAdm u hu n Ψ hΨc hsupp hnorm
  have hμ : 0 < μ := Work.BoseFixB1.adm_mu_pos hAdm
  have hℓ : 0 < Work.BoseFixB1.bSide v μ := Work.BoseFixB1.adm_ell_pos hAdm
  have hd : 0 < Work.BoseFixB1.bD v μ := Work.BoseFixB1.adm_d_pos hAdm
  have hAdm1 : Work.BoseBoxFix.Adm v 1 μ := Work.BoseFixB1.Adm.mono hAdm (min_le_left _ _)
  have hd1 : Work.BoseFixB1.bD v μ ≤ 1 := by
    change (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d ≤ 1
    rw [Work.BoseFixB1.d_eq_fsXp]
    exact Work.BoseBox.fsXp_le_one (mul_pos hμ (pow_pos hav 3))
      (Work.BoseFixB1.adm_dilute_le_one hAdm1 le_rfl) (by norm_num)
  obtain ⟨hR16, hRχ⟩ := hreg μ hμ (le_trans hAdm.2.1 (min_le_right _ _))
  -- `1 ≤ μ(ℓd)³`, hence `μ^{-1/3} ≤ ℓd`
  have hregMu : 1 ≤ μ * (Work.BoseFixB1.bSide v μ * Work.BoseFixB1.bD v μ) ^ 3 := by
    have h' := Work.BoseFixB1.Regime.one_le_mu_d_mul_sideAt_cube (A := _root_.BoseGases.a v)
      (μ := μ) hav hμ (Work.BoseFixB1.adm_dilute_le_one hAdm1 le_rfl)
    simpa only [Work.BoseFixB1.bSide, Work.BoseFixB1.bD, mul_comm] using h'
  have h13 : μ ^ (-(1 / 3 : ℝ)) ≤ Work.BoseFixB1.bSide v μ * Work.BoseFixB1.bD v μ := by
    have h' := Work.BoseFixB1S.inv_third_le_of_one_le_mul_cube hμ (mul_pos hℓ hd).le hregMu
    rwa [← Work.BoseFixB1S.rpow_neg_third_eq μ] at h'
  -- the box volume is positive on the good set
  have hvol : 0 < Work.BoseFixB1.bV v μ u := by
    have hδ : 0 < (μ ^ (-(1 / 3 : ℝ))) ^ 3 := by positivity
    have h' := Work.BoseFixB1.boxMass_ge_deltaScale_of_goodSet hℓ hd hd1 hμ h13 hu
    exact lt_of_lt_of_le hδ (by simpa only [Work.BoseFixB1.bV] using h')
  have hgo := hfib (ℓ := Work.BoseFixB1.bSide v μ) (d := Work.BoseFixB1.bD v μ) (μ := μ)
    hℓ hd hR16 hRχ u hvol (n := n) (Φ := Ψ) hΨc.continuous
  -- the box fibre mass `M₁` is FS's `W = w1MassB`
  have hM1 : Work.BoseFixB1S.boxM1 (Work.BoseFixB1.bSide v μ)
        (Submission.BoseGases.dlBox (Work.BoseFixB1.bSide v μ) (Work.BoseFixB1.bD v μ) u)
        (Submission.BoseGases.wSmall1Pair h 48 (Work.BoseFixB1.bSide v μ) (Work.BoseFixB1.bD v μ) u)
      = Work.BoseFixB1.bW v h μ u := by
    rw [Work.AprioriCount.boxM1_eq_w1MassB (h := h) (M := 48) (by norm_num) hℓ hd u]
    simp only [Work.BoseFixB1.bW, Work.BoseFixB1.bM, Work.BoseBox.paramsAt, Work.BoseBox.fsParams,
      Work.BoseBox.mValue]
  rw [hM1] at hgo
  -- rewrite the manifest bound into the vocabulary of the target
  have key : Work.BoseFixB1.fibSum h (Work.BoseFixB1.bM v μ) (Work.BoseFixB1.bSide v μ)
        (Work.BoseFixB1.bD v μ) u Ψ
      ≤ (Work.BoseFixB1.bW v h μ u / Work.BoseFixB1.bV v μ u) * Work.BoseFixB1.bFlat v μ Ψ u
        + C₁ * (_root_.BoseGases.a v) * (Real.sqrt (Work.BoseFixB1.bQ v μ Ψ u
              * (Work.BoseFixB1.bW v h μ u / Work.BoseFixB1.bV v μ u)
              * Work.BoseFixB1.bFlat v μ Ψ u)
            + Work.BoseFixB1.bQ v μ Ψ u) := by
    simpa only [Work.BoseFixB1.bW, Work.BoseFixB1.bV, Work.BoseFixB1.bFlat, Work.BoseFixB1.bQ,
      Work.BoseFixB1.bA, Work.BoseFixB1.bSide, Work.BoseFixB1.bD, Work.BoseFixB1.bM,
      Work.BoseBox.paramsAt, Work.BoseBox.fsParams, Work.BoseBox.mValue,
      Work.BoseFixB1S.boxFlatCount, Work.BoseFixB1S.boxQCount, Work.UBBInputs8.cnPlusBoxInd,
      Work.SmallBoxSliding.boxMass, mul_assoc] using hgo
  exact mul_le_mul_of_nonneg_left key hμ.le

end Work.BoseB1Cube
