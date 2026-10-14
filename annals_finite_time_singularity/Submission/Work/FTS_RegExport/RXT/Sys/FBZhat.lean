import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS_RegExport.RXB.l12_aux
import Submission.Work.FTS_RegExport.RXT.Sys.FBDefs
import Submission.Work.FTS_RegExport.RXT.Sys.L12FKaux.L12_limit_bound
import Submission.Work.FTS_RegExport.RXT.Sys.mixed_integral_identity
import Submission.Work.FTS_RegExport.RXT.SysAux.LgKg_Ftau_facts
import Submission.Work.FTS_RegExport.RXT.SysAux.bR_decomp
import Submission.Work.FTS_RegExport.RXT.SysAux.explicit_piece_bounds
import Submission.Work.FTS_RegExport.RXT.SysAux.pertSlot_contDiffOn
import Submission.Work.FTS_RegExport.RXT.st1_stdata
import Submission.Work.FTS_RegExport.RXT.st1_stdata2
import Submission.Work.FTS_RegExport.RXT0.RXJets.jetBasic
import Submission.Work.FTS_RegExport.RXVP3.velVanish2_unif
import Submission.Work.FTS_RegExport.THL.Defs
-- ===== merged: Submission.Work.FTS_RegExport.RXR7.r7Block_proved =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_RegExport.RXR7

open scoped Real Topology NNReal
open Set Filter
open Work.FTS.Galerkin (Fn Fam slice IsDynGSolWith)
open Work.FTS.Nonlin (PsiCan)
open Work.FTS.Regularity (pExp Jet)
open Work.FTS.RegPkgGal (extG RegPkg' St1Class R5Parts Avort Bdyn)
open Work.FTS.FinalV2 (gS tauExt LimApprox DynOK' EllLimOK3 Sol)
open Work.FTS.RegExportIface

variable {α C₀ Cs : ℝ} {Φs : Fn} {E : Fn →ₗ[ℝ] Fn}

/-- **RX-R7, re-proved 2026-10-11** for the repaired `VelPkg` (open-θ + `thLip`) and the
edge-extended coefficients `edgeExt Vz7`, `Vθ7`, `edgeExt cs7` (`cbc/fts_velpkg_fix.md` + REVIEW):
`r7Init` (`hInit`, `Lz7`), `r7HEq` (`hEq`), `r7Joint` (`hFjoint`), `r7VelLip` (`hVlipU`) on the open
quadrant, and `RegExportIface.R7Block_edgeExt` (the engine of `R7Block_of_velPkgF`) for the
closed-box `hVjoint`/`hcscont`. The constants `a = b = c = max M 0` come from `bnd` at horizon 1,
which is `S`-free, so they are uniform in `S`. -/
theorem r7Block_proved (hα : 0 < α) (hα13 : α ≤ 1 / 3)
    {g : Fam} (hSol : Sol (pExp α) Φs E g) (hOK : DynOK' (pExp α) C₀ Φs E g)
    (hdat : ∃ L β : ℝ, 1 ≤ L ∧ ∀ z θ, g z θ 0 = Work.FTS.LocData6.locG6 (pExp α) L β z θ)
    (hμ : ClockBd α Φs E g)
    (hVP : ∀ S > 0, VelPkg (pExp α) (Work.FTS.Final.maxMu (pExp α) (PsiCan Φs E g) g)
      (gS α (tauExt g)) (psiR α Φs E (tauExt g)) S) :
    ∃ a b c Lz7 : ℝ, ∀ S > 0, R7Block α S (gS α (tauExt g))
      (edgeExt (Vz7 (pExp α) (Work.FTS.Final.maxMu (pExp α) (PsiCan Φs E g) g) (gS α (tauExt g))
        (psiR α Φs E (tauExt g))))
      (Vθ7 (pExp α) (psiR α Φs E (tauExt g)))
      (edgeExt (cs7 (pExp α) (Work.FTS.Final.maxMu (pExp α) (PsiCan Φs E g) g) (gS α (tauExt g))
        (psiR α Φs E (tauExt g))))
      a b c Lz7 := by
  -- 1. the initial support radius of the profile (the `hInit` field), and the `Lz7` of the block
  obtain ⟨Lz7, hLz7pos, hInit⟩ := r7Init (α := α) (g := g) hdat
  -- 2. a fake-time-uniform bound `M` on the three coefficients: `bnd` does not mention `S`
  obtain ⟨M, hbnd⟩ := (hVP 1 one_pos).bnd
  have hpi : (0:ℝ) < Real.pi / 4 ∧ Real.pi / 4 < Real.pi / 2 :=
    ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
  have hMnn : 0 ≤ M :=
    le_trans (abs_nonneg _) ((hbnd 1 (Real.pi / 4) 0 one_pos hpi.1 hpi.2 le_rfl).1)
  have hMle : M ≤ max M 0 := le_max_left _ _
  have h0le : (0 : ℝ) ≤ max M 0 := le_max_right _ _
  refine ⟨max M 0, max M 0, max M 0, Lz7, fun S hS => ?_⟩
  have hEq := r7HEq (α := α) (C₀ := C₀) (Φs := Φs) (E := E) (g := g)
    hS hα hα13 hSol hOK hμ hVP
  have hVPS := hVP S hS
  have hcont := hVPS.cont
  refine R7Block_edgeExt (M := M)
    (r7Joint (α := α) (C₀ := C₀) (Φs := Φs) (E := E) (g := g) hS hα hα13 hSol hOK hμ hVP hEq)
    (ContinuousOn.prodMk (continuous_fst.comp_continuousOn hcont)
      ((continuous_fst.comp continuous_snd).comp_continuousOn hcont))
    ((continuous_snd.comp continuous_snd).comp_continuousOn hcont)
    hVPS.thHol
    (fun z θ τ hz h0 h1 hτ => (hbnd z θ τ hz h0 h1 hτ.1).2.1)
    (fun z τ hz hτ => hVPS.vth_ends z τ hz hτ.1)
    (r7VelLip (α := α) (C₀ := C₀) (Φs := Φs) (E := E) (g := g)
      hS hLz7pos hα hα13 hSol hOK hμ hVP)
    hEq
    (fun z θ τ hz h0 h1 hτ _ => hVPS.vz0 z θ τ hz h0 h1 hτ.le)
    (fun z θ τ hz h0 h1 hτ _ =>
      le_trans (le_trans (le_abs_self _) (hbnd z θ τ hz h0 h1 hτ.le).1) hMle)
    (fun z θ τ hz h0 h1 hτ _ => by
      have h1' := (hbnd z θ τ hz h0 h1 hτ.le).2.1
      have h4 : M * Real.sin (2 * θ) ≤ M := by
        simpa using mul_le_mul_of_nonneg_left (Real.sin_le_one (2 * θ)) hMnn
      exact le_trans (le_trans h1' h4) hMle)
    (fun z θ τ hz h0 h1 hτ _ => le_trans (hbnd z θ τ hz h0 h1 hτ.le).2.2 hMle)
    hInit hLz7pos.le h0le h0le h0le

end Work.FTS_RegExport.RXR7
end
-- ===== merged: Submission.Work.FTS_RegExport.RXT.Sys.FBZhat =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS_RegExport.RXT.Sys.FBZhat` — the six pieces of `Ẑ` and their weight bounds

`Ẑ = VR·A1 + bR·B1 + cR·F̂` decomposes (`Sys.FBDecomp.forcing_decomp`) into six pieces
(`Pp0` … `Pp5` below).  This file defines them and proves, for each, the bound in the weight
`z²/(1+z)²` for all `mixed`-jets of order `≤ 2`; the assembly into the bound for `Ẑ` itself is
in `Sys.FBZhatB.Zhat_bound`.
-/

noncomputable section
open scoped Real Topology NNReal
open Set Filter

namespace Work.FTS_RegExport.RXT.Sys

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-! ## §0  Elementary facts about the weight `z^{3/2}/(1+z)²` -/

theorem one_le_sqrt_rpow {z : ℝ} (hz : 1 ≤ z) : (1 : ℝ) ≤ z ^ ((1 : ℝ) / 2) :=
  Real.one_le_rpow hz (by norm_num)

theorem sqrt_rpow_le_self {z : ℝ} (hz : 1 ≤ z) : z ^ ((1 : ℝ) / 2) ≤ z := by
  have hz0 : 0 < z := lt_of_lt_of_le one_pos hz
  have h2 : (1 : ℝ) ≤ z ^ ((1 : ℝ) / 2) := one_le_sqrt_rpow hz
  calc z ^ ((1 : ℝ) / 2) = z ^ ((1 : ℝ) / 2) * 1 := (mul_one _).symm
    _ ≤ z ^ ((1 : ℝ) / 2) * z ^ ((1 : ℝ) / 2) := by nlinarith
    _ = z ^ ((1 : ℝ) / 2 + (1 : ℝ) / 2) := (Real.rpow_add hz0 _ _).symm
    _ = z ^ (1 : ℝ) := by norm_num
    _ = z := Real.rpow_one z

theorem sqrt_rpow_le_sq_one_add {z : ℝ} (hz : 0 < z) : z ^ ((1 : ℝ) / 2) ≤ (1 + z) ^ 2 := by
  by_cases h : z ≤ 1
  · calc z ^ ((1 : ℝ) / 2) ≤ (1 : ℝ) ^ ((1 : ℝ) / 2) := Real.rpow_le_rpow hz.le h (by norm_num)
      _ = 1 := by norm_num
      _ ≤ (1 + z) ^ 2 := by nlinarith
  · push_neg at h
    have h3 := sqrt_rpow_le_self h.le
    nlinarith [h3, h.le, sq_nonneg (1 + z)]

/-- `z^{3/2}/(1+z)² ≤ 1`. -/
theorem wt_le_one {z : ℝ} (hz : 0 < z) : z ^ ((3 : ℝ) / 2) / (1 + z) ^ 2 ≤ 1 := by
  rw [div_le_one (by positivity)]
  by_cases h : z ≤ 1
  · calc z ^ ((3 : ℝ) / 2) ≤ (1 : ℝ) ^ ((3 : ℝ) / 2) :=
        Real.rpow_le_rpow hz.le h (by norm_num)
      _ = 1 := by norm_num
      _ ≤ (1 + z) ^ 2 := by nlinarith
  · push_neg at h
    have h3 := sqrt_rpow_le_self h.le
    have h5 : z ^ ((3 : ℝ) / 2) = z * z ^ ((1 : ℝ) / 2) := by
      rw [show ((3 : ℝ) / 2) = 1 + 1 / 2 by norm_num, Real.rpow_add hz, Real.rpow_one]
    rw [h5]
    nlinarith [h3, h.le, sq_nonneg (1 + z)]

/-- `(z^{3/2}/(1+z)²)·(z/(1+z)²) ≤ z²/(1+z)²`. -/
theorem wt_mul_le {z : ℝ} (hz : 0 < z) :
    z ^ ((3 : ℝ) / 2) / (1 + z) ^ 2 * (z / (1 + z) ^ 2) ≤ z ^ 2 / (1 + z) ^ 2 := by
  have h4 : z ^ ((1 : ℝ) / 2) ≤ (1 + z) ^ 2 := sqrt_rpow_le_sq_one_add hz
  have h5 : z ^ ((5 : ℝ) / 2) ≤ z ^ 2 * (1 + z) ^ 2 := by
    have h6 : z ^ ((5 : ℝ) / 2) = z ^ (2 : ℝ) * z ^ ((1 : ℝ) / 2) := by
      rw [← Real.rpow_add hz]; norm_num
    have hz2 : z ^ (2 : ℝ) = z * z := by
      rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.rpow_add hz, Real.rpow_one]
    rw [h6, hz2]
    nlinarith [h4, hz.le]
  have hL : z ^ ((3 : ℝ) / 2) / (1 + z) ^ 2 * (z / (1 + z) ^ 2)
      = z ^ ((5 : ℝ) / 2) / (1 + z) ^ 4 := by
    rw [div_mul_div_comm]
    have hn : z ^ ((3 : ℝ) / 2) * z = z ^ ((5 : ℝ) / 2) := by
      calc z ^ ((3 : ℝ) / 2) * z = z ^ ((3 : ℝ) / 2) * z ^ (1 : ℝ) := by rw [Real.rpow_one]
        _ = z ^ ((3 : ℝ) / 2 + 1) := (Real.rpow_add hz _ _).symm
        _ = z ^ ((5 : ℝ) / 2) := by norm_num
    have hd : (1 + z) ^ 2 * (1 + z) ^ 2 = (1 + z) ^ 4 := by ring
    rw [hn, hd]
  have hR : z ^ 2 / (1 + z) ^ 2 = z ^ 2 * (1 + z) ^ 2 / (1 + z) ^ 4 := by
    field_simp
  rw [hL, hR]
  exact div_le_div_of_nonneg_right h5 (by positivity)

/-- `min z 1 · (z/(1+z)²) ≤ z²/(1+z)²`. -/
theorem min_mul_le {z : ℝ} (hz : 0 < z) : min z 1 * (z / (1 + z) ^ 2) ≤ z ^ 2 / (1 + z) ^ 2 := by
  have hmin : min z 1 ≤ z := min_le_left _ _
  calc min z 1 * (z / (1 + z) ^ 2) ≤ z * (z / (1 + z) ^ 2) :=
        mul_le_mul_of_nonneg_right hmin (by positivity)
    _ = z ^ 2 / (1 + z) ^ 2 := by ring

/-- Triangle inequality for a six-term sum. -/
theorem abs_add_six_le (a b c d e f : ℝ) :
    |a + b + c + d + e + f| ≤ |a| + |b| + |c| + |d| + |e| + |f| := by
  have h1 : |a + b + c + d + e + f| ≤ |a + b + c + d + e| + |f| := abs_add_le _ _
  have h2 : |a + b + c + d + e| ≤ |a + b + c + d| + |e| := abs_add_le _ _
  have h3 : |a + b + c + d| ≤ |a + b + c| + |d| := abs_add_le _ _
  have h4 : |a + b + c| ≤ |a + b| + |c| := abs_add_le _ _
  have h5 : |a + b| ≤ |a| + |b| := abs_add_le _ _
  linarith

/-! ## §1  The six pieces of `Ẑ` -/

/-- `Φ̃(σ) = phiTil β (GR α g) (ΦR α Φs E g) σ`. -/
def PtF (α : ℝ) (Φs : Work.FTS.Galerkin.Fn)
    (E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn) (g : Work.FTS.Galerkin.Fam)
    (σ : ℝ) : ℝ → ℝ → ℝ :=
  Work.FTS.RegExportIface.phiTil (Work.FTS.Regularity.pExp α)
    (Work.FTS.RegExportIface.RXT.GR α g) (Work.FTS.RegExportIface.RXT.ΦR α Φs E g) σ

/-- `Lg = L₁₂(slice (GR α g) σ)`. -/
def LgF (α : ℝ) (g : Work.FTS.Galerkin.Fam) (σ : ℝ) : ℝ → ℝ :=
  fun z => Work.Construction.L12 (Work.FTS.Galerkin.slice
    (Work.FTS.RegExportIface.RXT.GR α g) σ) z

/-- `Kg = 𝔽K(slice (GR α g) σ)`. -/
def KgF (α : ℝ) (g : Work.FTS.Galerkin.Fam) (σ : ℝ) : ℝ → ℝ :=
  fun z => Work.Construction.FK (Work.FTS.Galerkin.slice
    (Work.FTS.RegExportIface.RXT.GR α g) σ) z

def Pp0 (α : ℝ) (Φs : Work.FTS.Galerkin.Fn)
    (E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn) (g : Work.FTS.Galerkin.Fam)
    (σ : ℝ) : ℝ → ℝ → ℝ :=
  Ef (Work.FTS.RegExportIface.RXT.μR α Φs E g σ) (Work.FTS.Regularity.pExp α)

def Pp1 (α : ℝ) (g : Work.FTS.Galerkin.Fam) (σ : ℝ) : ℝ → ℝ → ℝ :=
  fun z θ => LgF α g σ z * al1f (Work.FTS.Regularity.pExp α) z θ

def Pp2 (α : ℝ) (g : Work.FTS.Galerkin.Fam) (σ : ℝ) : ℝ → ℝ → ℝ :=
  fun z θ => KgF α g σ z * al2f (Work.FTS.Regularity.pExp α) z θ

def Pp3 (α : ℝ) (Φs : Work.FTS.Galerkin.Fn)
    (E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn) (g : Work.FTS.Galerkin.Fam)
    (σ : ℝ) : ℝ → ℝ → ℝ :=
  fun z θ => (2 * Work.FTS.Regularity.pExp α
    * Work.Construction.Vop (PtF α Φs E g σ) z θ) * A1f z θ

def Pp4 (α : ℝ) (Φs : Work.FTS.Galerkin.Fn)
    (E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn) (g : Work.FTS.Galerkin.Fam)
    (σ : ℝ) : ℝ → ℝ → ℝ :=
  fun z θ => (2 * (Work.Construction.Uop (Work.FTS.Regularity.pExp α) (PtF α Φs E g σ) z θ
    / Real.sin (2 * θ))) * B1f (Work.FTS.Regularity.pExp α) z θ

def Pp5 (α : ℝ) (Φs : Work.FTS.Galerkin.Fn)
    (E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn) (g : Work.FTS.Galerkin.Fam)
    (σ : ℝ) : ℝ → ℝ → ℝ :=
  fun z θ => (-2 * Work.Construction.Rop (Work.FTS.Regularity.pExp α) (PtF α Φs E g σ) z θ)
    * Fhf z θ

def SSF (α : ℝ) (Φs : Work.FTS.Galerkin.Fn)
    (E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn) (g : Work.FTS.Galerkin.Fam)
    (σ : ℝ) : ℝ → ℝ → ℝ :=
  fun z θ => Pp0 α Φs E g σ z θ + Pp1 α g σ z θ + Pp2 α g σ z θ + Pp3 α Φs E g σ z θ
    + Pp4 α Φs E g σ z θ + Pp5 α Φs E g σ z θ

end Work.FTS_RegExport.RXT.Sys
end
end
