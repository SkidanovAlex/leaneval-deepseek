import ChallengeDeps
import Submission.Work.BoseB1Cube.r3RowOfMassRow
import Submission.Work.BoseB1Cube.shiftMassLower
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseB1Cube.shiftR3Row`

The `R₃` column of the cube Bogoliubov port, paid by the one-body mass row **under the
fibre-shift (autocorrelation) hypothesis** instead of the deep-position centre hypothesis of
`Work.BoseB1Cube.coreR3A`.

The port row itself is the PROVED `Work.BoseB1Cube.r3RowOfMassRow`, which is stated with an
*arbitrary* positive constant `K` in the free mass row

    K·(a v)·χ_{B(u)} ≤ ∬ w_{1,B(u)} ,      χ = chiMass (PBM,PBℓ,PBd) u ,  W = PBW h μ u .

So the only remaining input is the mass row at a *fixed* `K`.  The shift hypothesis

    (1 − 2Γ)·chiMass ≤ ∫ x, χ(x)·χ(x − z)      (‖z‖ ≤ R,  Γ = PBΓ v μ)

is exactly the hypothesis of the PROVED `Work.BoseB1Cube.shiftMassLower`, which gives

    (1 − 2Γ)·8π(a v)·chiMass ≤ W .

Since `2Γ ≤ 1/2` at an admissible `μ` (`Work.BoseB1Cube.gammaRegimeAt`), we have
`1 − 2Γ ≥ 1/2`, hence

    4π·(a v)·chiMass ≤ (1 − 2Γ)·8π(a v)·chiMass ≤ W ,

i.e. the mass row at the **fixed** constant `K = 4π`.  Feeding that constant into
`r3RowOfMassRow` closes the row.
-/

namespace Work.BoseB1Cube

set_option linter.unusedVariables false

theorem shiftR3Row {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v) (hv : 0 ≤ v)
    (hv1 : MeasureTheory.MemLp v 1) (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    (hav : 0 < _root_.BoseGases.a v) {Cn : ℝ} (hCn : 4 ≤ Cn) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ {μ : ℝ}, Work.BoseBoxFix.Adm v ε₀ μ →
      ∀ u : EuclideanSpace ℝ (Fin 3),
        u ∈ Work.SmallBoxSliding.goodSet (Work.BoseFixB1B.PBℓ v μ) (Work.BoseFixB1B.PBd v μ) μ →
        (∀ z : EuclideanSpace ℝ (Fin 3), ‖z‖ ≤ R →
          (1 - 2 * Work.BoseFixB1B.PBΓ v μ) * Work.SmallBoxSliding.chiMass (Work.BoseFixB1B.PBM v μ)
              (Work.BoseFixB1B.PBℓ v μ) (Work.BoseFixB1B.PBd v μ) u
            ≤ ∫ x : EuclideanSpace ℝ (Fin 3),
                Submission.BoseGases.chiSmallB (Work.BoseFixB1B.PBM v μ) (Work.BoseFixB1B.PBℓ v μ)
                  (Work.BoseFixB1B.PBd v μ) u x
                * Submission.BoseGases.chiSmallB (Work.BoseFixB1B.PBM v μ) (Work.BoseFixB1B.PBℓ v μ)
                  (Work.BoseFixB1B.PBd v μ) u (x - z)) →
        ∀ {n : ℕ}, (n : ℝ) ≤ 2 * Cn * μ * Work.BoseFixB1B.PBBV v μ u →
          2 * (Work.BoseFixB1.sbCut μ (_root_.BoseGases.a v)) ^ 3
              * ((n : ℝ) / Work.BoseFixB1B.PBBV v μ u)
              * Work.SmallBoxSliding.chiMass (Work.BoseFixB1B.PBM v μ) (Work.BoseFixB1B.PBℓ v μ)
                  (Work.BoseFixB1B.PBd v μ) u
            ≤ μ ^ 2 * Work.BoseFixB1B.PBΓ v μ * Work.BoseFixB1B.PBW h μ u := by
  -- ### the port at the fixed free-mass-row constant `K₀ = 4π`
  obtain ⟨ε₁, hε₁, H⟩ :=
    r3RowOfMassRow h hv hv1 hvrad hR hv_supp hav (4 * Real.pi) (by positivity) hCn
  -- ### the parameter bundle at small diluteness
  obtain ⟨εg, hεg, hgamma⟩ := gammaRegimeAt (v := v) hav hR
  refine ⟨min ε₁ εg, lt_min hε₁ hεg, ?_⟩
  intro μ hAdm u hu hshift n hn
  have hAdm₁ : Work.BoseBoxFix.Adm v ε₁ μ :=
    Work.BoseFixB1.Adm.mono hAdm (min_le_left _ _)
  have hAdm_g : Work.BoseBoxFix.Adm v εg μ :=
    Work.BoseFixB1.Adm.mono hAdm (min_le_right _ _)
  obtain ⟨hR16, hRχ, _hd8, _hΓpos, h2Γle, _hRsb⟩ := hgamma hAdm_g
  have hμ : 0 < μ := hAdm.1
  have hℓ : 0 < Work.BoseFixB1B.PBℓ v μ := Work.BoseFixB1.adm_ell_pos hAdm
  have hd : 0 < Work.BoseFixB1B.PBd v μ := Work.BoseFixB1.adm_d_pos hAdm
  have hM : 1 ≤ Work.BoseFixB1B.PBM v μ := by
    rw [Work.BoseFixB1B.PBM, Work.BoseFixB1.M_eq_mValue]
    norm_num [Work.BoseBox.mValue]
  -- ### the shift mass row `(1 − 2Γ)·8π(a v)·χ ≤ W`
  have hrow := shiftMassLower (v := v) (R := R) hv_supp hR hv hvrad hv1 h
    (M := Work.BoseFixB1B.PBM v μ) (ℓ := Work.BoseFixB1B.PBℓ v μ)
    (d := Work.BoseFixB1B.PBd v μ) (θ := 2 * Work.BoseFixB1B.PBΓ v μ)
    hM hℓ hd hR16 hRχ u hshift
  have hrow' : (1 - 2 * Work.BoseFixB1B.PBΓ v μ)
        * (8 * Real.pi * _root_.BoseGases.a v)
        * Work.SmallBoxSliding.chiMass (Work.BoseFixB1B.PBM v μ) (Work.BoseFixB1B.PBℓ v μ)
            (Work.BoseFixB1B.PBd v μ) u
      ≤ Work.BoseFixB1B.PBW h μ u := by
    simpa only [Work.BoseFixB1B.PBW] using hrow
  -- ### lower the coefficient to the fixed constant `4π`
  have hmass : (4 * Real.pi) * (_root_.BoseGases.a v)
        * Work.SmallBoxSliding.chiMass (Work.BoseFixB1B.PBM v μ) (Work.BoseFixB1B.PBℓ v μ)
            (Work.BoseFixB1B.PBd v μ) u
      ≤ Work.BoseFixB1B.PBW h μ u := by
    have ht : (1 / 2 : ℝ) ≤ 1 - 2 * Work.BoseFixB1B.PBΓ v μ := by linarith
    have h8 : (4 : ℝ) ≤ (1 - 2 * Work.BoseFixB1B.PBΓ v μ) * 8 := by
      have h := mul_le_mul_of_nonneg_right ht (by norm_num : (0 : ℝ) ≤ 8)
      linarith
    have hcoef : (4 * Real.pi) ≤ (1 - 2 * Work.BoseFixB1B.PBΓ v μ) * (8 * Real.pi) := by
      calc (4 : ℝ) * Real.pi = 4 * Real.pi := rfl
        _ ≤ ((1 - 2 * Work.BoseFixB1B.PBΓ v μ) * 8) * Real.pi :=
            mul_le_mul_of_nonneg_right h8 Real.pi_pos.le
        _ = (1 - 2 * Work.BoseFixB1B.PBΓ v μ) * (8 * Real.pi) := by ring
    have hχ : 0 ≤ Work.SmallBoxSliding.chiMass (Work.BoseFixB1B.PBM v μ)
        (Work.BoseFixB1B.PBℓ v μ) (Work.BoseFixB1B.PBd v μ) u :=
      Work.SmallBoxSliding.chiMass_nonneg _ _ _ _
    have hnn : 0 ≤ (_root_.BoseGases.a v)
        * Work.SmallBoxSliding.chiMass (Work.BoseFixB1B.PBM v μ) (Work.BoseFixB1B.PBℓ v μ)
            (Work.BoseFixB1B.PBd v μ) u := mul_nonneg hav.le hχ
    have hstep : (4 * Real.pi) * (_root_.BoseGases.a v)
          * Work.SmallBoxSliding.chiMass (Work.BoseFixB1B.PBM v μ) (Work.BoseFixB1B.PBℓ v μ)
              (Work.BoseFixB1B.PBd v μ) u
        ≤ (1 - 2 * Work.BoseFixB1B.PBΓ v μ) * (8 * Real.pi * _root_.BoseGases.a v)
            * Work.SmallBoxSliding.chiMass (Work.BoseFixB1B.PBM v μ) (Work.BoseFixB1B.PBℓ v μ)
                (Work.BoseFixB1B.PBd v μ) u := by
      calc (4 * Real.pi) * (_root_.BoseGases.a v)
            * Work.SmallBoxSliding.chiMass (Work.BoseFixB1B.PBM v μ)
                (Work.BoseFixB1B.PBℓ v μ) (Work.BoseFixB1B.PBd v μ) u
          = (4 * Real.pi) * ((_root_.BoseGases.a v)
              * Work.SmallBoxSliding.chiMass (Work.BoseFixB1B.PBM v μ)
                  (Work.BoseFixB1B.PBℓ v μ) (Work.BoseFixB1B.PBd v μ) u) := by ring
        _ ≤ ((1 - 2 * Work.BoseFixB1B.PBΓ v μ) * (8 * Real.pi))
              * ((_root_.BoseGases.a v)
                * Work.SmallBoxSliding.chiMass (Work.BoseFixB1B.PBM v μ)
                    (Work.BoseFixB1B.PBℓ v μ) (Work.BoseFixB1B.PBd v μ) u) :=
            mul_le_mul_of_nonneg_right hcoef hnn
        _ = (1 - 2 * Work.BoseFixB1B.PBΓ v μ) * (8 * Real.pi * _root_.BoseGases.a v)
              * Work.SmallBoxSliding.chiMass (Work.BoseFixB1B.PBM v μ)
                  (Work.BoseFixB1B.PBℓ v μ) (Work.BoseFixB1B.PBd v μ) u := by ring
    exact le_trans hstep hrow'
  -- ### the row
  exact H (μ := μ) (n := n) hAdm₁ u hu hn hmass

end Work.BoseB1Cube
