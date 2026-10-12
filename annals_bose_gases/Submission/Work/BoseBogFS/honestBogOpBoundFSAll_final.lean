import ChallengeDeps
import Submission.Work.BoseBogFS.hZP_of_lattice
import Submission.Work.BoseBogFS.honest_denRow_view
import Submission.Work.BoseBogFS.honest_linHi
import Submission.Work.BoseBogFSAllPort.AssemblyAll
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseBogFS

theorem honestBogOpBoundFSAll_final {v : ℝ³ → ℝ} {h : Work.UBB.ScatSol v}
    {fc fu : Work.BoseBoxFix.LowCut}
    {HM : ∀ μ : ℝ, Work.BoseBoxFock.HonestModes v μ} {R : ℝ}
    (hR : 0 < R) (hv : ∀ x, 0 ≤ v x) (hv1 : MeasureTheory.MemLp v 1)
    (hvrad : _root_.BoseGases.IsRadial v)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : ℝ³) R) (hav : 0 < _root_.BoseGases.a v)
    (hL : Work.BoseBogFS.ZPLatticeRow v h R) :
    Work.BoseBoxFock.BogOpBoundFSAll v h R
      (Work.BoseBoxFock.HonestBoxFam v h fc fu HM) := by
  -- the `χ ⋆ χ` second-order bound
  obtain ⟨C, hC, r₁, hr₁, hT⟩ := Submission.BoseGases.conv3chi_second_order_bound
  -- the regime rows (`R ≤ ℓχ_{R₀}`, `R/ℓ ≤ r₁`, `C(R/ℓ)² ≤ 1/4`, `δ_D ≤ 1/2`)
  obtain ⟨εr, hεr, hRℓ, hreg, hcond, hδD1⟩ :=
    honestRegimeRows (v := v) (h := h) (R := R) (r₁ := r₁) (C := C)
      hR hv hv1 hvrad hv_supp hav hC hr₁
  -- the three `N`-free analytic rows
  obtain ⟨εz, C₄, hεz, hC₄, hZProw⟩ := hZP_of_lattice (v := v) (h := h)
    (fc := fc) (fu := fu) (HM := HM) (R := R) hR hv hvrad hv_supp hav hL
  obtain ⟨εd₀, hεd₀, hdenrow⟩ := honest_denRow_view (v := v) (h := h)
    (fc := fc) (fu := fu) (HM := HM) (R := R) hR hv hvrad hv_supp hav
  obtain ⟨εl, Cl, hεl, hCl, hlinrow⟩ := honest_linHi (v := v) (h := h)
    (fc := fc) (fu := fu) (HM := HM) (R := R) hR hv hvrad hv_supp hav
  -- the rows read off the view / the honest family, at the threshold `εd := min εd₀ εr`
  refine Work.BoseBogFSAllPort.bogOpBoundFSAll_of_B
    (Work.BoseBogFSAllPort.bogOpBoundFSAll_of_analytic
      (D := Work.BoseBoxFock.HonestBoxFam v h fc fu HM) hR hv hv1 hvrad hv_supp hav hC hr₁ hT
      εr hεr hRℓ hreg hcond hδD1 εz C₄ hεz hC₄ ?_ (min εd₀ εr)
      (lt_min hεd₀ hεr) ?_ εl Cl hεl hCl ?_ ?_ ?_ ?_)
  · -- the zero-point row
    intro μ hadm hview ρ hclose
    exact hZProw μ hadm hview ρ hclose
  · -- FS's denominator row (transported to `min εd₀ εr`)
    intro μ hadm hview ρ hclose k
    exact hdenrow μ (Work.BoseBogFS.adm_mono (min_le_left _ _) hadm) hview ρ hclose k
  · -- the `𝒞`-form bound
    intro μ hadm hview ρ hclose f hf
    exact hlinrow μ hadm hview ρ hclose f hf
  · -- the `χ̂`-normalisation row
    intro μ hadm hview
    exact Work.BoseBoxFock.Clean.honest_hatChi_sum_le v h fc fu HM μ
  · -- the mass row, positivity
    intro μ hadm hview
    have hμ : 0 < μ := hadm.1
    have hreg' : R / Work.BoseBox.sideAt μ (_root_.BoseGases.a v) ≤ r₁ :=
      hreg μ (Work.BoseBogFS.adm_mono (min_le_right _ _) hadm)
    have hcond' : C * (R / Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) ^ 2 ≤ 1 / 2 := by
      have h := hcond μ (Work.BoseBogFS.adm_mono (min_le_right _ _) hadm)
      linarith
    exact (honest_W1_mass_rows (v := v) (h := h) (fc := fc) (fu := fu) (HM := HM)
      (R := R) (r₁ := r₁) (C := C) hR hv hvrad hv_supp hC hr₁ hT μ hμ hav hreg' hcond').1
  · -- the mass row, upper bound
    intro μ hadm hview
    have hμ : 0 < μ := hadm.1
    have hreg' : R / Work.BoseBox.sideAt μ (_root_.BoseGases.a v) ≤ r₁ :=
      hreg μ (Work.BoseBogFS.adm_mono (min_le_right _ _) hadm)
    have hcond' : C * (R / Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) ^ 2 ≤ 1 / 2 := by
      have h := hcond μ (Work.BoseBogFS.adm_mono (min_le_right _ _) hadm)
      linarith
    have hrow := (honest_W1_mass_rows (v := v) (h := h) (fc := fc) (fu := fu) (HM := HM)
      (R := R) (r₁ := r₁) (C := C) hR hv hvrad hv_supp hC hr₁ hT μ hμ hav hreg' hcond').2
    rw [honestDW]
    exact hrow

end Work.BoseBogFS
