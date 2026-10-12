import ChallengeDeps
import Mathlib.Data.ZMod.ValMinAbs
import Submission.Work.BoseBogFS.ZPLatticeDefs
import Submission.Work.BoseBogFS.hZP_highMode
import Submission.Work.BoseBogFS.zpCutMul_le
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBogFS.hZP_of_lattice`

The honest cube/cut-off zero-point sum is dominated by the `N`-free lattice row
`Work.BoseBogFS.ZPLatticeRow`: the cut factor `ζ ∈ [0,1]` of the view is dropped
(`Work.BoseBogFS.zpCutMul_le`, with the high-momentum domination
`Work.BoseBogFS.hZP_highMode` supplying `2|ℬ| ≤ 𝒜` exactly where the cut is strict), and
`labVec : Lab N → (Fin 3 → ℤ)` is injective, so the honest sum is a sub-sum of a finite part of
the full dual lattice.  Plan and recipe: `FINDING_hZP_of_lattice_plan.md`.

`open scoped Real` is needed for `π` in the statement (the project sets `autoImplicit = false`);
the statement is otherwise the frozen one, verbatim.
-/

noncomputable section

open scoped Real Topology BigOperators

open MeasureTheory Filter Metric

namespace Work.BoseBogFS

open _root_.BoseGases Submission.BoseGases Work.UBB Work.BoseBox Work.BoseBoxFix Work.BoseFixR

set_option autoImplicit false
set_option linter.unusedVariables false

theorem hZP_of_lattice {v : ℝ³ → ℝ} {h : Work.UBB.ScatSol v}
    {fc fu : Work.BoseBoxFix.LowCut}
    {HM : ∀ μ : ℝ, Work.BoseBoxFock.HonestModes v μ} {R : ℝ}
    (hR : 0 < R) (hv : ∀ x, 0 ≤ v x) (hvrad : _root_.BoseGases.IsRadial v)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : ℝ³) R) (hav : 0 < _root_.BoseGases.a v)
    (hL : Work.BoseBogFS.ZPLatticeRow v h R) :
    ∃ ε₁ C₄ : ℝ, 0 < ε₁ ∧ 0 ≤ C₄ ∧ ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₁ μ →
      (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).viewFSAll v h μ → ∀ ρ : ℝ,
      Work.BoseBoxFock.CloseCondFS v μ ρ →
      (∑ k : (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).Mode,
          (1 / 2 : ℝ) * Work.BoseB6.bogZeroPoint
            (Work.BoseBogFS.bogA (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E ρ k)
            (Work.BoseBogFS.bogB (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E ρ k))
        ≤ -(4 * π * Work.UBB.lhyC * ρ ^ 2 * (_root_.BoseGases.a v) * Work.BoseFixR.ell3 v μ
              * Real.sqrt (ρ * (_root_.BoseGases.a v) ^ 3))
          + (1 / 2) * Work.BoseFixR.ell3 v μ * ρ ^ 2
              * (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E.W1omega0
          + C₄ * Work.BoseBogFS.errBracket v R μ := by
  obtain ⟨εa, C4, hεa, hC4, hrow⟩ := hL
  obtain ⟨εr, hεr, hRrow⟩ := exists_adm_sideAt_div_le v hav hR Submission.BoseGases.chiR0_pos
  refine ⟨min εa (min εr ((1 / 2) ^ 1000)), C4,
    lt_min hεa (lt_min hεr (by norm_num)), hC4, ?_⟩
  intro μ hAdm hview ρ hclose
  set D : Work.BoseFixR.KzDatum := Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ with hD
  have hAdm_a : Work.BoseBoxFix.Adm v εa μ :=
    adm_mono (min_le_left _ _) hAdm
  have hAdm_r : Work.BoseBoxFix.Adm v εr μ :=
    adm_mono (le_trans (min_le_right _ _) (min_le_left _ _)) hAdm
  have hAdm_1 : Work.BoseBoxFix.Adm v ((1 / 2) ^ 1000) μ :=
    adm_mono (le_trans (min_le_right _ _) (min_le_right _ _)) hAdm
  have hRℓ : R ≤ Work.BoseFixR.ell v μ * Submission.BoseGases.chiR0 := by
    have h := hRrow μ hAdm_r
    rw [div_le_iff₀ (Work.BoseBox.sideAt_pos hAdm_r.1 hav)] at h
    rw [Work.BoseFixR.ell_eq]
    exact le_trans h (le_of_eq (mul_comm _ _))
  -- the view
  have hview' : Work.BoseBoxFock.RViewFSAll v h μ D.F D.T D.E D.gHat0 := hview
  unfold Work.BoseBoxFock.RViewFSAll at hview'
  obtain ⟨hFSP, hmu, hac, hell, -, -, hdP, hsP, heTP, -, -, htau, -, -, hcut, -,
    hW1omega0, -⟩ := hview'
  obtain ⟨fuc, Λ, hΛ, hW1eq⟩ := hcut
  have hEℓpos : 0 < Work.BoseFixR.ell v μ := by
    have h1 : 0 < Work.BoseFixR.ell v μ * Submission.BoseGases.chiR0 :=
      lt_of_lt_of_le hR hRℓ
    exact pos_of_mul_pos_left h1 Submission.BoseGases.chiR0_pos.le
  have hellH : Work.BoseBoxFock.ellH v μ = Work.BoseFixR.ell v μ := by
    rw [Work.BoseBoxFock.ellH, if_pos (Work.BoseBox.sideAt_pos hAdm.1 hav)]
    rfl
  have hkm : ∀ k : D.Mode, D.F.kmom k
      = (Work.BoseFixR.ell v μ)⁻¹
        • Work.BoseB4.vec (Work.BoseBoxFock.labVec (HM μ).N k) := by
    intro k
    show Work.BoseBoxFock.kmomLab (Work.BoseBoxFock.ellH v μ) (HM μ).N k = _
    rw [hellH]
    rfl
  -- the row summand
  set g : (Fin 3 → ℤ) → ℝ := fun n => (1 / 2 : ℝ) * Work.BoseB6.bogZeroPoint
      (Work.BoseBoxFock.tauSm (paramsAt μ (a v)).eT (paramsAt μ (a v)).s
          (paramsAt μ (a v)).d (ell v μ) ((ell v μ)⁻¹ • Work.BoseB4.vec n)
        + ρ * chat (W1fun v h (ell v μ)) ((ell v μ)⁻¹ • Work.BoseB4.vec n))
      (ρ * chat (W1fun v h (ell v μ)) ((ell v μ)⁻¹ • Work.BoseB4.vec n)) with hg
  have hstep1 : (∑ k : D.Mode, (1 / 2 : ℝ) * Work.BoseB6.bogZeroPoint
        (bogA D.E ρ k) (bogB D.E ρ k))
      ≤ ∑ k : D.Mode, g (Work.BoseBoxFock.labVec (HM μ).N k) := by
    refine Finset.sum_le_sum (fun k _ => ?_)
    set ζ : ℝ := Work.BoseBoxFock.uvCut fuc Λ (D.F.kmom k) with hζdef
    -- the row-form of the mode data
    set Aform : ℝ := Work.BoseBoxFock.tauSm (paramsAt μ (a v)).eT (paramsAt μ (a v)).s
        (paramsAt μ (a v)).d (ell v μ) ((ell v μ)⁻¹ • Work.BoseB4.vec
          (Work.BoseBoxFock.labVec (HM μ).N k)) with hAform
    set cform : ℝ := chat (W1fun v h (ell v μ)) ((ell v μ)⁻¹ • Work.BoseB4.vec
          (Work.BoseBoxFock.labVec (HM μ).N k)) with hcform
    have hEW1 : D.E.W1 k = ζ * chat (W1fun v h (ell v μ)) (D.F.kmom k) := by
      rw [hζdef, congrFun hW1eq k]
    have hA : bogA D.E ρ k = Aform + ζ * (ρ * cform) := by
      rw [bogA, hEW1, congrFun htau k, hkm k, hAform, hcform]
      ring
    have hB : bogB D.E ρ k = ζ * (ρ * cform) := by
      rw [bogB, hEW1, hkm k, hcform]
      ring
    have hlast : (1 / 2 : ℝ) * Work.BoseB6.bogZeroPoint (Aform + ρ * cform) (ρ * cform)
        = g (Work.BoseBoxFock.labVec (HM μ).N k) := by
      rw [hg, hAform, hcform]
    by_cases hζone : ζ = 1
    · rw [hA, hB, hζone, one_mul, hlast]
    · have hζ0 : 0 ≤ ζ := by
        rw [hζdef, Work.BoseBoxFock.uvCut]
        exact Work.BoseBoxFix.LowCut.nonneg fuc _
      have hζ1 : ζ ≤ 1 := by
        rw [hζdef, Work.BoseBoxFock.uvCut]
        exact Work.BoseBoxFix.LowCut.le_one fuc _
      have hζlt : ζ < 1 := lt_of_le_of_ne hζ1 hζone
      have hZPhi := hZP_highMode hR hv hvrad hv_supp hav (le_refl ((1 / 2) ^ 1000)) hAdm_1
        hview hRℓ hclose hΛ k hζlt
      have hhigh : 2 * |ρ * cform| ≤ Aform := by
        rw [congrFun htau k, hkm k] at hZPhi
        simpa only [hcform, hAform] using hZPhi
      have hτ0 : 0 ≤ Aform := le_trans (by positivity) hhigh
      have hzpcut : Work.BoseB6.bogZeroPoint (Aform + ζ * (ρ * cform)) (ζ * (ρ * cform))
          ≤ Work.BoseB6.bogZeroPoint (Aform + ρ * cform) (ρ * cform) :=
        zpCutMul_le hτ0 hζ0 hζ1 (Or.inr hhigh)
      calc (1 / 2 : ℝ) * Work.BoseB6.bogZeroPoint (bogA D.E ρ k) (bogB D.E ρ k)
          = (1 / 2 : ℝ) * Work.BoseB6.bogZeroPoint (Aform + ζ * (ρ * cform))
              (ζ * (ρ * cform)) := by rw [hA, hB]
        _ ≤ (1 / 2 : ℝ) * Work.BoseB6.bogZeroPoint (Aform + ρ * cform) (ρ * cform) :=
              mul_le_mul_of_nonneg_left hzpcut (by norm_num)
        _ ≤ g (Work.BoseBoxFock.labVec (HM μ).N k) := le_of_eq hlast
  have hstep2 : (∑ k : D.Mode, g (Work.BoseBoxFock.labVec (HM μ).N k))
      = ∑ n ∈ (Finset.univ.image (Work.BoseBoxFock.labVec (HM μ).N)), g n := by
    exact (Finset.sum_image
      (s := (Finset.univ : Finset (Work.BoseBoxFock.Lab (HM μ).N)))
      (f := g) (g := Work.BoseBoxFock.labVec (HM μ).N)
      (fun x _ y _ hxy => by
        funext i
        exact ZMod.valMinAbs_inj.mp (congrFun hxy i))).symm
  have hstep3 : (∑ n ∈ (Finset.univ.image (Work.BoseBoxFock.labVec (HM μ).N)), g n)
      ≤ -(4 * π * lhyC * ρ ^ 2 * (a v) * ell3 v μ * Real.sqrt (ρ * (a v) ^ 3))
        + (1 / 2) * ell3 v μ * ρ ^ 2 * chat (W1omegaFun v h (ell v μ)) 0
        + C4 * errBracket v R μ := by
    simpa only [hg] using hrow μ hAdm_a ρ hclose
      (Finset.univ.image (Work.BoseBoxFock.labVec (HM μ).N))
  calc (∑ k : D.Mode, (1 / 2 : ℝ) * Work.BoseB6.bogZeroPoint
        (bogA D.E ρ k) (bogB D.E ρ k))
      ≤ ∑ k : D.Mode, g (Work.BoseBoxFock.labVec (HM μ).N k) := hstep1
    _ = ∑ n ∈ (Finset.univ.image (Work.BoseBoxFock.labVec (HM μ).N)), g n := hstep2
    _ ≤ -(4 * π * lhyC * ρ ^ 2 * (a v) * ell3 v μ * Real.sqrt (ρ * (a v) ^ 3))
        + (1 / 2) * ell3 v μ * ρ ^ 2 * chat (W1omegaFun v h (ell v μ)) 0
        + C4 * errBracket v R μ := hstep3
    _ = -(4 * π * lhyC * ρ ^ 2 * (a v) * ell3 v μ * Real.sqrt (ρ * (a v) ^ 3))
        + (1 / 2) * ell3 v μ * ρ ^ 2 * D.E.W1omega0 + C4 * errBracket v R μ := by
        rw [hW1omega0]

end Work.BoseBogFS
