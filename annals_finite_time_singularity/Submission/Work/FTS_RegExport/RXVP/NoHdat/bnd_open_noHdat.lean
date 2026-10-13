import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS_RegExport.RXVP3.bnd_open

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_RegExport.RXVP.NoHdat

open scoped Real Topology NNReal
open Set Filter
open Work.FTS.Galerkin (Fn Fam slice)
open Work.FTS.Nonlin (PsiCan)
open Work.FTS.Regularity (pExp Jet)
open Work.FTS.RegPkgGal (extG RegPkg' St1Class R5Parts Avort Bdyn)
open Work.FTS.FinalV2 (gS tauExt LimApprox DynOK' EllLimOK3 Sol)
open Work.FTS.RegExportIface

set_option autoImplicit false
set_option maxHeartbeats 800000

/-- `|c2m θ| ≤ 2` (`c2m θ = cos 2θ - sin²θ`). -/
private lemma abs_c2m_le_two (θ : ℝ) : |Work.Construction.c2m θ| ≤ 2 := by
  rw [Work.Construction.c2m]
  have h1 : |Real.cos (2 * θ)| ≤ 1 := Real.abs_cos_le_one _
  have h2 : |Real.sin θ ^ 2| ≤ 1 := by
    rw [abs_of_nonneg (sq_nonneg _)]
    exact Real.sin_sq_le_one θ
  linarith [abs_sub (Real.cos (2 * θ)) (Real.sin θ ^ 2)]

private lemma abs_add_three' (a b c : ℝ) : |a + b + c| ≤ |a| + |b| + |c| := by
  have h1 : |a + b + c| ≤ |a + b| + |c| := abs_add_le _ _
  have h2 : |a + b| ≤ |a| + |b| := abs_add_le _ _
  linarith


theorem bnd_open_noHdat {α C₀ Ce Cs : ℝ} {Φs : Work.FTS.Galerkin.Fn}
    {E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn} {g : Work.FTS.Galerkin.Fam}
    (hα : 0 < α) (hα13 : α ≤ 1 / 3)
    (hEll : ∀ u : Work.FTS.Galerkin.Fn, Work.FTS.ClassC.ClassC (Work.FTS.Regularity.pExp α) u →
      Work.FTS.Final.EllPkgGo (Work.FTS.Regularity.pExp α) Ce u (E u) ∧
        Work.FTS.ClassC.EllPkgK (Work.FTS.Regularity.pExp α) 6 Ce u (E u))
    (hEL3 : Work.FTS.FinalV2.EllLimOK3 (Work.FTS.Regularity.pExp α) E)
    (hStar : Work.FTS.Final.StarPkgo2 (Work.FTS.Regularity.pExp α) Cs Φs)
    (hSol : Work.FTS.FinalV2.Sol (Work.FTS.Regularity.pExp α) Φs E g)
    (hOK : Work.FTS.FinalV2.DynOK' (Work.FTS.Regularity.pExp α) C₀ Φs E g)
    (hμ : Work.FTS.RegExportIface.ClockBd α Φs E g) :
    ∃ M : ℝ, ∀ z θ τ, 0 < z → 0 < θ → θ < Real.pi / 2 → 0 ≤ τ →
      |Work.FTS.RegExportIface.Vz7 (Work.FTS.Regularity.pExp α)
          (Work.FTS.Final.maxMu (Work.FTS.Regularity.pExp α)
            (Work.FTS.Nonlin.PsiCan Φs E g) g)
          (Work.FTS.FinalV2.gS α (Work.FTS.FinalV2.tauExt g))
          (Work.FTS.RegExportIface.psiR α Φs E (Work.FTS.FinalV2.tauExt g)) z θ τ| ≤ M ∧
      |Work.FTS.RegExportIface.Vθ7 (Work.FTS.Regularity.pExp α)
          (Work.FTS.RegExportIface.psiR α Φs E (Work.FTS.FinalV2.tauExt g)) z θ τ|
        ≤ M * Real.sin (2 * θ) ∧
      |Work.FTS.RegExportIface.cs7 (Work.FTS.Regularity.pExp α)
          (Work.FTS.Final.maxMu (Work.FTS.Regularity.pExp α)
            (Work.FTS.Nonlin.PsiCan Φs E g) g)
          (Work.FTS.FinalV2.gS α (Work.FTS.FinalV2.tauExt g))
          (Work.FTS.RegExportIface.psiR α Φs E (Work.FTS.FinalV2.tauExt g)) z θ τ| ≤ M := by
  -- the two τ-uniform inputs: the slot bounds of `Φ̃` and the datum of `F(τ)`
  obtain ⟨Mv, hMv⟩ := Work.FTS_RegExport.RXVP3.velVanish2_unif (α := α) (Ce := Ce) (C₀ := C₀) (Cs := Cs)
    (Φs := Φs) (E := E) (g := g) hα hα13 hEll hEL3 hStar hSol hOK hμ
  obtain ⟨Cd, hCd1, hCd⟩ := Work.FTS_RegExport.RXVP3.Ftau_datum_unif (α := α) (C₀ := C₀) (Φs := Φs) (E := E) (g := g)
    hα hα13 hOK
  obtain ⟨K, hK0, hK⟩ := Work.FTS_RegExport.RXT.Sys.L12_FK_jets_of_datum
  have hαG : 0 < pExp α := Work.FTS.Regularity.pExp_pos hα
  -- `Mv ≥ 0`
  have hMv0 : 0 ≤ Mv := by
    have hpi : (0 : ℝ) < Real.pi / 4 := by linarith [Real.pi_pos]
    have hpi2 : Real.pi / 4 < Real.pi / 2 := by linarith [Real.pi_pos]
    have h := hMv 0 le_rfl 1 (Real.pi / 4) one_pos hpi hpi2
      (Work.Construction.Vop (Work.FTS.RegExportIface.phiTil (pExp α)
        (Work.FTS.RegExportIface.RXT.GR α g) (Work.FTS.RegExportIface.RXT.ΦR α Φs E g) 0))
      (by simp) 0 0 (by norm_num)
    have h2 : 0 ≤ Mv * min (1 : ℝ) 1 := le_trans (abs_nonneg _) h
    simpa using h2
  have hCd4 : 0 ≤ K * Cd ^ 4 := mul_nonneg hK0.le (by positivity)
  refine ⟨max (3 / 2 + 2 * (K * Cd ^ 4) + 2 * pExp α * Mv)
    (max (2 * (Mv + (3 / (4 * pExp α) + 1 / 4) * (K * Cd ^ 4)))
      (3 / 2 + (K * Cd ^ 4) / pExp α + (K * Cd ^ 4) + 2 * Mv)), ?_⟩
  intro z θ τ hz hθ hθ2 hτ
  -- the three slot bounds at the given `(z, θ, τ)`
  have hslotV : |Work.Construction.Vop
      (Work.FTS.RegExportIface.phiTil (pExp α) (Work.FTS.RegExportIface.RXT.GR α g)
        (Work.FTS.RegExportIface.RXT.ΦR α Φs E g) τ) z θ| ≤ Mv := by
    have h := hMv τ hτ z θ hz hθ hθ2
      (Work.Construction.Vop (Work.FTS.RegExportIface.phiTil (pExp α)
        (Work.FTS.RegExportIface.RXT.GR α g)
        (Work.FTS.RegExportIface.RXT.ΦR α Φs E g) τ)) (by simp) 0 0 (by norm_num)
    have h2 : Mv * min z 1 ≤ Mv := by
      have := mul_le_mul_of_nonneg_left (min_le_right z (1 : ℝ)) hMv0
      simpa using this
    calc |Work.Construction.Vop (Work.FTS.RegExportIface.phiTil (pExp α)
          (Work.FTS.RegExportIface.RXT.GR α g)
          (Work.FTS.RegExportIface.RXT.ΦR α Φs E g) τ) z θ|
        = |Work.Spaces.mixed 0 0 (Work.Construction.Vop
            (Work.FTS.RegExportIface.phiTil (pExp α)
              (Work.FTS.RegExportIface.RXT.GR α g)
              (Work.FTS.RegExportIface.RXT.ΦR α Φs E g) τ)) z θ| := by simp
      _ ≤ Mv * min z 1 := h
      _ ≤ Mv := h2
  have hslotR : |Work.Construction.Rop (pExp α)
      (Work.FTS.RegExportIface.phiTil (pExp α) (Work.FTS.RegExportIface.RXT.GR α g)
        (Work.FTS.RegExportIface.RXT.ΦR α Φs E g) τ) z θ| ≤ Mv := by
    have h := hMv τ hτ z θ hz hθ hθ2
      (Work.Construction.Rop (pExp α) (Work.FTS.RegExportIface.phiTil (pExp α)
        (Work.FTS.RegExportIface.RXT.GR α g)
        (Work.FTS.RegExportIface.RXT.ΦR α Φs E g) τ)) (by simp) 0 0 (by norm_num)
    have h2 : Mv * min z 1 ≤ Mv := by
      have := mul_le_mul_of_nonneg_left (min_le_right z (1 : ℝ)) hMv0
      simpa using this
    calc |Work.Construction.Rop (pExp α) (Work.FTS.RegExportIface.phiTil (pExp α)
          (Work.FTS.RegExportIface.RXT.GR α g)
          (Work.FTS.RegExportIface.RXT.ΦR α Φs E g) τ) z θ|
        = |Work.Spaces.mixed 0 0 (Work.Construction.Rop (pExp α)
            (Work.FTS.RegExportIface.phiTil (pExp α)
              (Work.FTS.RegExportIface.RXT.GR α g)
              (Work.FTS.RegExportIface.RXT.ΦR α Φs E g) τ)) z θ| := by simp
      _ ≤ Mv * min z 1 := h
      _ ≤ Mv := h2
  have hslotU : |Work.Construction.Uop (pExp α)
      (Work.FTS.RegExportIface.phiTil (pExp α) (Work.FTS.RegExportIface.RXT.GR α g)
        (Work.FTS.RegExportIface.RXT.ΦR α Φs E g) τ) z θ / Real.sin (2 * θ)| ≤ Mv := by
    have h := hMv τ hτ z θ hz hθ hθ2
      (fun z θ => Work.Construction.Uop (pExp α) (Work.FTS.RegExportIface.phiTil (pExp α)
        (Work.FTS.RegExportIface.RXT.GR α g)
        (Work.FTS.RegExportIface.RXT.ΦR α Φs E g) τ) z θ / Real.sin (2 * θ))
      (by simp) 0 0 (by norm_num)
    have h2 : Mv * min z 1 ≤ Mv := by
      have := mul_le_mul_of_nonneg_left (min_le_right z (1 : ℝ)) hMv0
      simpa using this
    calc |Work.Construction.Uop (pExp α) (Work.FTS.RegExportIface.phiTil (pExp α)
          (Work.FTS.RegExportIface.RXT.GR α g)
          (Work.FTS.RegExportIface.RXT.ΦR α Φs E g) τ) z θ / Real.sin (2 * θ)|
        = |Work.Spaces.mixed 0 0 (fun z θ => Work.Construction.Uop (pExp α)
            (Work.FTS.RegExportIface.phiTil (pExp α)
              (Work.FTS.RegExportIface.RXT.GR α g)
              (Work.FTS.RegExportIface.RXT.ΦR α Φs E g) τ) z θ
            / Real.sin (2 * θ)) z θ| := by simp
      _ ≤ Mv * min z 1 := h
      _ ≤ Mv := h2
  -- the radial facts for `F(τ)`
  have hJ := hK (Work.Construction.Ftau (pExp α) (Work.FTS.RegExportIface.RXT.GR α g) τ)
    Cd hCd1 (hCd τ hτ) z hz
  have hL12bd : |Work.Construction.L12
      (Work.Construction.Ftau (pExp α) (Work.FTS.RegExportIface.RXT.GR α g) τ) z|
      ≤ K * Cd ^ 4 := by
    have h := (hJ.1 0 (by norm_num)).1
    simpa using h
  have hFKbd : |Work.Construction.FK
      (Work.Construction.Ftau (pExp α) (Work.FTS.RegExportIface.RXT.GR α g) τ) z|
      ≤ K * Cd ^ 4 := by
    have h := (hJ.1 0 (by norm_num)).2.1
    simpa using h
  have hder : HasDerivAt (fun z' => Work.Construction.L12
      (Work.Construction.Ftau (pExp α) (Work.FTS.RegExportIface.RXT.GR α g) τ) z')
      (-(Work.Construction.FK (Work.Construction.Ftau (pExp α)
        (Work.FTS.RegExportIface.RXT.GR α g) τ) z) / z) z := hJ.2.2.1
  -- smoothness of the two pieces of `Φ`
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hsmPsi, hsmTheta⟩ :=
    Work.FTS_RegExport.RXT.Sys.coeff_pieces_contDiffOn (C₀ := C₀) (Cs := Cs) (g := g)
      hα hα13 hEL3 hStar hOK hτ
  have hQ0 : (z, θ) ∈ Work.FTS.EllipticEst.Q0 := ⟨hz, hθ, hθ2⟩
  have hs : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])
  -- the clock at `τ` (unfold `maxMu`)
  have hμbdG : ∀ s : ℝ, 0 ≤ s → |Work.FTS.RegExportIface.RXT.μR α Φs E g s| ≤ 1 / 2 := by
    intro s hs'
    have h : Work.FTS.RegExportIface.RXT.μR α Φs E g s
        = Work.FTS.Galerkin.muDyn (pExp α) (PsiCan Φs E g) g s := by
      simp only [Work.FTS.RegExportIface.RXT.μR, Work.FTS.Final.maxMu, max_eq_left hs']
    rw [h]
    exact hμ.1 s hs'
  -- ## `Vz7`
  have hVz : |Vz7 (pExp α) (Work.FTS.RegExportIface.RXT.μR α Φs E g)
      (Work.FTS.RegExportIface.RXT.GR α g) (Work.FTS.RegExportIface.RXT.ΦR α Φs E g) z θ τ|
      ≤ 3 / 2 + 2 * (K * Cd ^ 4) + 2 * pExp α * Mv := by
    have hμbd : |Work.FTS.RegExportIface.RXT.μR α Φs E g τ| ≤ 1 / 2 := hμbdG τ hτ
    have h1 : |1 - Work.FTS.RegExportIface.RXT.μR α Φs E g τ| ≤ 3 / 2 :=
      Work.FTS_RegExport.RXT.Sys.one_sub_abs_le hμbd
    have h2 : |Work.Construction.L12 (Work.Construction.Ftau (pExp α)
        (Work.FTS.RegExportIface.RXT.GR α g) τ) z * Work.Construction.c2m θ|
        ≤ 2 * (K * Cd ^ 4) := by
      rw [abs_mul]
      have h := mul_le_mul hL12bd (abs_c2m_le_two θ) (abs_nonneg _) hCd4
      linarith [h]
    have h3 : |2 * pExp α * Work.Construction.Vop
        (Work.FTS.RegExportIface.phiTil (pExp α) (Work.FTS.RegExportIface.RXT.GR α g)
          (Work.FTS.RegExportIface.RXT.ΦR α Φs E g) τ) z θ|
        ≤ 2 * pExp α * Mv := by
      rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * pExp α)]
      exact mul_le_mul_of_nonneg_left hslotV (by positivity)
    have hdef : Vz7 (pExp α) (Work.FTS.RegExportIface.RXT.μR α Φs E g)
        (Work.FTS.RegExportIface.RXT.GR α g) (Work.FTS.RegExportIface.RXT.ΦR α Φs E g) z θ τ
        = (1 - Work.FTS.RegExportIface.RXT.μR α Φs E g τ)
          + Work.Construction.L12 (Work.Construction.Ftau (pExp α)
              (Work.FTS.RegExportIface.RXT.GR α g) τ) z * Work.Construction.c2m θ
          + 2 * pExp α * Work.Construction.Vop
              (Work.FTS.RegExportIface.phiTil (pExp α)
                (Work.FTS.RegExportIface.RXT.GR α g)
                (Work.FTS.RegExportIface.RXT.ΦR α Φs E g) τ) z θ := rfl
    rw [hdef]
    have hsum := abs_add_three' (1 - Work.FTS.RegExportIface.RXT.μR α Φs E g τ)
      (Work.Construction.L12 (Work.Construction.Ftau (pExp α)
        (Work.FTS.RegExportIface.RXT.GR α g) τ) z * Work.Construction.c2m θ)
      (2 * pExp α * Work.Construction.Vop
        (Work.FTS.RegExportIface.phiTil (pExp α) (Work.FTS.RegExportIface.RXT.GR α g)
          (Work.FTS.RegExportIface.RXT.ΦR α Φs E g) τ) z θ)
    linarith [hsum, h1, h2, h3]
  -- ## `Vθ7`
  have hVth : |Vθ7 (pExp α) (Work.FTS.RegExportIface.RXT.ΦR α Φs E g) z θ τ|
      ≤ 2 * (Mv + (3 / (4 * pExp α) + 1 / 4) * (K * Cd ^ 4)) * Real.sin (2 * θ) := by
    have hdef : Vθ7 (pExp α) (Work.FTS.RegExportIface.RXT.ΦR α Φs E g) z θ τ
        = 2 * Work.Construction.Uop (pExp α)
            (slice (Work.FTS.RegExportIface.RXT.ΦR α Φs E g) τ) z θ := rfl
    rw [hdef]
    rw [Work.FTS_RegExport.RXT.Sys.uop_split_theta (Φs := Φs) (E := E) (g := g)
      hQ0 hsmPsi hsmTheta]
    have hA : |Work.Construction.Uop (pExp α) (Work.FTS.RegExportIface.phiTil (pExp α)
        (Work.FTS.RegExportIface.RXT.GR α g)
        (Work.FTS.RegExportIface.RXT.ΦR α Φs E g) τ) z θ| ≤ Mv * Real.sin (2 * θ) := by
      have heq : |Work.Construction.Uop (pExp α) (Work.FTS.RegExportIface.phiTil (pExp α)
          (Work.FTS.RegExportIface.RXT.GR α g)
          (Work.FTS.RegExportIface.RXT.ΦR α Φs E g) τ) z θ|
          = |Work.Construction.Uop (pExp α) (Work.FTS.RegExportIface.phiTil (pExp α)
              (Work.FTS.RegExportIface.RXT.GR α g)
              (Work.FTS.RegExportIface.RXT.ΦR α Φs E g) τ) z θ / Real.sin (2 * θ)|
            * Real.sin (2 * θ) := by
        rw [abs_div, abs_of_pos hs, div_mul_cancel₀ _ (ne_of_gt hs)]
      rw [heq]
      exact mul_le_mul_of_nonneg_right hslotU hs.le
    have hB : |Work.Construction.Uop (pExp α) (Work.Construction.Theta (pExp α)
        (Work.Construction.Ftau (pExp α) (Work.FTS.RegExportIface.RXT.GR α g) τ)) z θ|
        ≤ (3 / (4 * pExp α) + 1 / 4) * (K * Cd ^ 4) * Real.sin (2 * θ) := by
      have hdiv : Work.Construction.Uop (pExp α) (Work.Construction.Theta (pExp α)
          (Work.Construction.Ftau (pExp α) (Work.FTS.RegExportIface.RXT.GR α g) τ)) z θ
          / Real.sin (2 * θ)
          = -(3 / (4 * pExp α)) * Work.Construction.L12 (Work.Construction.Ftau (pExp α)
              (Work.FTS.RegExportIface.RXT.GR α g) τ) z
            + (1 / 4) * Work.Construction.FK (Work.Construction.Ftau (pExp α)
              (Work.FTS.RegExportIface.RXT.GR α g) τ) z :=
        Work.FTS_RegExport.RXT.Sys.Uop_Theta_div hαG hz hθ hθ2 hder
      have hb : |Work.Construction.Uop (pExp α) (Work.Construction.Theta (pExp α)
          (Work.Construction.Ftau (pExp α) (Work.FTS.RegExportIface.RXT.GR α g) τ)) z θ
          / Real.sin (2 * θ)| ≤ (3 / (4 * pExp α) + 1 / 4) * (K * Cd ^ 4) := by
        rw [hdiv]
        have h4 : |-(3 / (4 * pExp α)) * Work.Construction.L12 (Work.Construction.Ftau
              (pExp α) (Work.FTS.RegExportIface.RXT.GR α g) τ) z
            + (1 / 4) * Work.Construction.FK (Work.Construction.Ftau (pExp α)
              (Work.FTS.RegExportIface.RXT.GR α g) τ) z|
            ≤ |-(3 / (4 * pExp α)) * Work.Construction.L12 (Work.Construction.Ftau (pExp α)
                (Work.FTS.RegExportIface.RXT.GR α g) τ) z|
              + |(1 / 4) * Work.Construction.FK (Work.Construction.Ftau (pExp α)
                (Work.FTS.RegExportIface.RXT.GR α g) τ) z| := abs_add_le _ _
        have h5 : |-(3 / (4 * pExp α)) * Work.Construction.L12 (Work.Construction.Ftau (pExp α)
              (Work.FTS.RegExportIface.RXT.GR α g) τ) z|
            = (3 / (4 * pExp α)) * |Work.Construction.L12 (Work.Construction.Ftau (pExp α)
              (Work.FTS.RegExportIface.RXT.GR α g) τ) z| := by
          rw [abs_mul, abs_neg, abs_of_pos (by positivity : (0 : ℝ) < 3 / (4 * pExp α))]
        have h6 : |(1 / 4) * Work.Construction.FK (Work.Construction.Ftau (pExp α)
              (Work.FTS.RegExportIface.RXT.GR α g) τ) z|
            = (1 / 4) * |Work.Construction.FK (Work.Construction.Ftau (pExp α)
              (Work.FTS.RegExportIface.RXT.GR α g) τ) z| := by
          rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 4)]
        rw [h5, h6] at h4
        have h7 : 3 / (4 * pExp α) * |Work.Construction.L12 (Work.Construction.Ftau (pExp α)
              (Work.FTS.RegExportIface.RXT.GR α g) τ) z|
            ≤ 3 / (4 * pExp α) * (K * Cd ^ 4) :=
          mul_le_mul_of_nonneg_left hL12bd (by positivity)
        have h8 : (1 / 4) * |Work.Construction.FK (Work.Construction.Ftau (pExp α)
              (Work.FTS.RegExportIface.RXT.GR α g) τ) z| ≤ (1 / 4) * (K * Cd ^ 4) :=
          mul_le_mul_of_nonneg_left hFKbd (by norm_num)
        calc |-(3 / (4 * pExp α)) * Work.Construction.L12 (Work.Construction.Ftau (pExp α)
              (Work.FTS.RegExportIface.RXT.GR α g) τ) z
            + (1 / 4) * Work.Construction.FK (Work.Construction.Ftau (pExp α)
              (Work.FTS.RegExportIface.RXT.GR α g) τ) z|
            ≤ 3 / (4 * pExp α) * |Work.Construction.L12 (Work.Construction.Ftau (pExp α)
                (Work.FTS.RegExportIface.RXT.GR α g) τ) z|
              + (1 / 4) * |Work.Construction.FK (Work.Construction.Ftau (pExp α)
                (Work.FTS.RegExportIface.RXT.GR α g) τ) z| := h4
          _ ≤ 3 / (4 * pExp α) * (K * Cd ^ 4) + (1 / 4) * (K * Cd ^ 4) := add_le_add h7 h8
          _ = (3 / (4 * pExp α) + 1 / 4) * (K * Cd ^ 4) := by ring
      have heq : |Work.Construction.Uop (pExp α) (Work.Construction.Theta (pExp α)
          (Work.Construction.Ftau (pExp α) (Work.FTS.RegExportIface.RXT.GR α g) τ)) z θ|
          = |Work.Construction.Uop (pExp α) (Work.Construction.Theta (pExp α)
              (Work.Construction.Ftau (pExp α) (Work.FTS.RegExportIface.RXT.GR α g) τ)) z θ
              / Real.sin (2 * θ)| * Real.sin (2 * θ) := by
        rw [abs_div, abs_of_pos hs, div_mul_cancel₀ _ (ne_of_gt hs)]
      rw [heq]
      exact mul_le_mul_of_nonneg_right hb hs.le
    have hsum := abs_add_le (Work.Construction.Uop (pExp α)
        (Work.FTS_RegExport.RXT.v2_PhiT α Φs E g τ) z θ)
      (Work.Construction.Uop (pExp α) (Work.Construction.Theta (pExp α)
        (Work.Construction.Ftau (pExp α) (Work.FTS.RegExportIface.RXT.GR α g) τ)) z θ)
    have hA' : |Work.Construction.Uop (pExp α)
        (Work.FTS_RegExport.RXT.v2_PhiT α Φs E g τ) z θ| ≤ Mv * Real.sin (2 * θ) :=
      hA
    have hmul : |2 * (Work.Construction.Uop (pExp α)
          (Work.FTS_RegExport.RXT.v2_PhiT α Φs E g τ) z θ
        + Work.Construction.Uop (pExp α) (Work.Construction.Theta (pExp α)
            (Work.Construction.Ftau (pExp α)
              (Work.FTS.RegExportIface.RXT.GR α g) τ)) z θ)|
        = 2 * |Work.Construction.Uop (pExp α)
            (Work.FTS_RegExport.RXT.v2_PhiT α Φs E g τ) z θ
          + Work.Construction.Uop (pExp α) (Work.Construction.Theta (pExp α)
              (Work.Construction.Ftau (pExp α)
                (Work.FTS.RegExportIface.RXT.GR α g) τ)) z θ| := by
      rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    rw [hmul]
    have hA'' : |Work.Construction.Uop (pExp α)
        (Work.FTS_RegExport.RXT.v2_PhiT α Φs E g τ) z θ|
        ≤ Mv * Real.sin (2 * θ) := by
      simpa only [Work.FTS.RegExportIface.phiTil, Work.FTS_RegExport.RXT.v2_PhiT] using hA'
    linarith [hsum, hA'', hB]
  -- ## `cs7`
  have hCs : |cs7 (pExp α) (Work.FTS.RegExportIface.RXT.μR α Φs E g)
      (Work.FTS.RegExportIface.RXT.GR α g) (Work.FTS.RegExportIface.RXT.ΦR α Φs E g) z θ τ|
      ≤ 3 / 2 + (K * Cd ^ 4) / pExp α + (K * Cd ^ 4) + 2 * Mv := by
    have hμbd : |Work.FTS.RegExportIface.RXT.μR α Φs E g τ| ≤ 1 / 2 := hμbdG τ hτ
    have h1 : |1 + Work.FTS.RegExportIface.RXT.μR α Φs E g τ| ≤ 3 / 2 :=
      Work.FTS_RegExport.RXT.Sys.one_add_abs_le hμbd
    have h2 : |Work.Construction.L12 (Work.Construction.Ftau (pExp α)
        (Work.FTS.RegExportIface.RXT.GR α g) τ) z / pExp α|
        ≤ (K * Cd ^ 4) / pExp α := by
      rw [abs_div, abs_of_pos hαG]
      exact div_le_div_of_nonneg_right hL12bd hαG.le
    have h3 : |Real.sin θ ^ 2 * Work.Construction.FK (Work.Construction.Ftau (pExp α)
        (Work.FTS.RegExportIface.RXT.GR α g) τ) z| ≤ K * Cd ^ 4 := by
      rw [abs_mul, abs_of_nonneg (sq_nonneg _)]
      have h := mul_le_mul (Real.sin_sq_le_one θ) hFKbd (abs_nonneg _) (by norm_num :
        (0 : ℝ) ≤ 1)
      linarith [h]
    have h4 : |2 * Work.Construction.Rop (pExp α)
        (Work.FTS.RegExportIface.phiTil (pExp α) (Work.FTS.RegExportIface.RXT.GR α g)
          (Work.FTS.RegExportIface.RXT.ΦR α Φs E g) τ) z θ| ≤ 2 * Mv := by
      rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
      exact mul_le_mul_of_nonneg_left hslotR (by norm_num)
    have hdef : cs7 (pExp α) (Work.FTS.RegExportIface.RXT.μR α Φs E g)
        (Work.FTS.RegExportIface.RXT.GR α g) (Work.FTS.RegExportIface.RXT.ΦR α Φs E g) z θ τ
        = (1 + Work.FTS.RegExportIface.RXT.μR α Φs E g τ)
          - Work.Construction.L12 (Work.Construction.Ftau (pExp α)
              (Work.FTS.RegExportIface.RXT.GR α g) τ) z / pExp α
          + Real.sin θ ^ 2 * Work.Construction.FK (Work.Construction.Ftau (pExp α)
              (Work.FTS.RegExportIface.RXT.GR α g) τ) z
          - 2 * Work.Construction.Rop (pExp α)
              (Work.FTS.RegExportIface.phiTil (pExp α)
                (Work.FTS.RegExportIface.RXT.GR α g)
                (Work.FTS.RegExportIface.RXT.ΦR α Φs E g) τ) z θ := rfl
    rw [hdef]
    have e1 : |(1 + Work.FTS.RegExportIface.RXT.μR α Φs E g τ)
        - Work.Construction.L12 (Work.Construction.Ftau (pExp α)
            (Work.FTS.RegExportIface.RXT.GR α g) τ) z / pExp α|
        ≤ |1 + Work.FTS.RegExportIface.RXT.μR α Φs E g τ|
          + |Work.Construction.L12 (Work.Construction.Ftau (pExp α)
              (Work.FTS.RegExportIface.RXT.GR α g) τ) z / pExp α| := abs_sub _ _
    have e2 : |((1 + Work.FTS.RegExportIface.RXT.μR α Φs E g τ)
          - Work.Construction.L12 (Work.Construction.Ftau (pExp α)
              (Work.FTS.RegExportIface.RXT.GR α g) τ) z / pExp α)
        + Real.sin θ ^ 2 * Work.Construction.FK (Work.Construction.Ftau (pExp α)
            (Work.FTS.RegExportIface.RXT.GR α g) τ) z|
        ≤ |(1 + Work.FTS.RegExportIface.RXT.μR α Φs E g τ)
            - Work.Construction.L12 (Work.Construction.Ftau (pExp α)
                (Work.FTS.RegExportIface.RXT.GR α g) τ) z / pExp α|
          + |Real.sin θ ^ 2 * Work.Construction.FK (Work.Construction.Ftau (pExp α)
              (Work.FTS.RegExportIface.RXT.GR α g) τ) z| := abs_add_le _ _
    have e3 : |(((1 + Work.FTS.RegExportIface.RXT.μR α Φs E g τ)
            - Work.Construction.L12 (Work.Construction.Ftau (pExp α)
                (Work.FTS.RegExportIface.RXT.GR α g) τ) z / pExp α)
          + Real.sin θ ^ 2 * Work.Construction.FK (Work.Construction.Ftau (pExp α)
              (Work.FTS.RegExportIface.RXT.GR α g) τ) z)
        - 2 * Work.Construction.Rop (pExp α)
            (Work.FTS.RegExportIface.phiTil (pExp α)
              (Work.FTS.RegExportIface.RXT.GR α g)
              (Work.FTS.RegExportIface.RXT.ΦR α Φs E g) τ) z θ|
        ≤ |((1 + Work.FTS.RegExportIface.RXT.μR α Φs E g τ)
            - Work.Construction.L12 (Work.Construction.Ftau (pExp α)
                (Work.FTS.RegExportIface.RXT.GR α g) τ) z / pExp α)
          + Real.sin θ ^ 2 * Work.Construction.FK (Work.Construction.Ftau (pExp α)
              (Work.FTS.RegExportIface.RXT.GR α g) τ) z|
          + |2 * Work.Construction.Rop (pExp α)
              (Work.FTS.RegExportIface.phiTil (pExp α)
                (Work.FTS.RegExportIface.RXT.GR α g)
                (Work.FTS.RegExportIface.RXT.ΦR α Φs E g) τ) z θ| := abs_sub _ _
    linarith [e1, e2, e3, h1, h2, h3, h4]
  -- ## assembly
  have hVthle : 2 * (Mv + (3 / (4 * pExp α) + 1 / 4) * (K * Cd ^ 4))
      ≤ max (3 / 2 + 2 * (K * Cd ^ 4) + 2 * pExp α * Mv)
        (max (2 * (Mv + (3 / (4 * pExp α) + 1 / 4) * (K * Cd ^ 4)))
          (3 / 2 + (K * Cd ^ 4) / pExp α + (K * Cd ^ 4) + 2 * Mv)) :=
    le_trans (le_max_left _ _) (le_max_right _ _)
  refine ⟨le_trans hVz (le_max_left _ _), ?_,
    le_trans hCs (le_trans (le_max_right _ _) (le_max_right _ _))⟩
  calc |Vθ7 (pExp α) (psiR α Φs E (tauExt g)) z θ τ|
      = |Vθ7 (pExp α) (Work.FTS.RegExportIface.RXT.ΦR α Φs E g) z θ τ| := rfl
    _ ≤ 2 * (Mv + (3 / (4 * pExp α) + 1 / 4) * (K * Cd ^ 4)) * Real.sin (2 * θ) := hVth
    _ ≤ max (3 / 2 + 2 * (K * Cd ^ 4) + 2 * pExp α * Mv)
        (max (2 * (Mv + (3 / (4 * pExp α) + 1 / 4) * (K * Cd ^ 4)))
          (3 / 2 + (K * Cd ^ 4) / pExp α + (K * Cd ^ 4) + 2 * Mv)) * Real.sin (2 * θ) :=
      mul_le_mul_of_nonneg_right hVthle hs.le

end Work.FTS_RegExport.RXVP.NoHdat
