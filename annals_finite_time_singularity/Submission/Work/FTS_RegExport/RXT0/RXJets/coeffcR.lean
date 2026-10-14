import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Order.CompletePartialOrder
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.LocData6.zfarR_jet_le6_of_jets
import Submission.Work.FTS.RegExportIface.RXT.Leaves
import Submission.Work.FTS_RegExport.RXT.Ftau_bounds
import Submission.Work.FTS_RegExport.RXT.Sys.FBZhatP
import Submission.Work.FTS_RegExport.RXT.Sys.L12FK_family_jets
import Submission.Work.FTS_RegExport.RXT.Sys.pth_vop_slot_bd
import Submission.Work.FTS_RegExport.RXT.SysAux.bR_decomp
import Submission.Work.FTS_RegExport.RXT.coeff_C2
import Submission.Work.FTS_RegExport.RXT.velVanish2
import Submission.Work.FTS_RegExport.RXT0.RXJets.CJShared
import Submission.Work.FTS_RegExport.RXT0.RXJets.jetBasic
import Submission.Work.FTS_RegExport.RXVPMain
import Submission.Work.FTS_RegExport.THL.Defs
import Submission.Work.R1G.DecayInZ_gA
-- ===== merged: Submission.Work.FTS_RegExport.RXT.Sys.CoeffBnd =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS_RegExport.RXT.Sys.CoeffBnd` — the `dbnd` half of `CoeffJets`

The order-`≤ 2` jet bounds of the three transport coefficient slices, uniformly in the fake time
`τ ∈ [0,S]`, assembled from

* `RXT.velVanish2` — the uniform order-`≤ 2` bounds of the three slots of the residual;
* `Sys.explicit_pieces_coeff` — the bounds of the four explicit (radial/angular) pieces;
* `Sys.pth_vop_slot_bd` — the `∂_θ`-slot used by the fourth conjunct;
* `Sys.L12FK_family_jets` — the uniform bound of `L₁₂(F_τ)`;
* `Sys.CoeffSmooth`/`Sys.CoeffBounds` — the `C²`-regularity of the pieces and the four
  coefficient bounds themselves.
-/

noncomputable section
open scoped Real Topology
open Set Filter

namespace Work.FTS_RegExport.RXT.Sys

open Work.FTS.Galerkin (Fn Fam slice)
open Work.FTS.RegExportIface (Vz7 Vθ7 cs7)
open Work.FTS.RegExportIface.RXT (GR ΦR μR)
open Work.FTS_RegExport.RXT (v2_PhiT v2_SlotR v2_SlotV v2_SlotU)
open Work.FTS.Regularity (pExp)
open Work.Construction (L12 FK Ftau Theta Uop Vop Rop c2m Fstar)

set_option autoImplicit false

variable {α Ce C₀ Cs : ℝ} {Φs : Fn} {E : Fn →ₗ[ℝ] Fn}

/-- `v2_PhiT` is the `phiTil` of the sanitised data. -/
theorem v2_PhiT_eq_phiTil (g : Fam) (τ : ℝ) :
    v2_PhiT α Φs E g τ = Work.FTS.RegExportIface.phiTil (pExp α) (GR α g) (ΦR α Φs E g) τ := by
  funext z θ
  simp only [v2_PhiT, Work.FTS.RegExportIface.phiTil, Work.Construction.PhiTil]

/-- **The `dbnd` clause of `CoeffJets`.** -/
theorem coeff_dbnd {g : Fam}
    (hα : 0 < α) (hα13 : α ≤ 1 / 3)
    (hEll : ∀ u : Fn, Work.FTS.ClassC.ClassC (pExp α) u →
      Work.FTS.Final.EllPkgGo (pExp α) Ce u (E u) ∧
        Work.FTS.ClassC.EllPkgK (pExp α) 6 Ce u (E u))
    (hEL3 : Work.FTS.FinalV2.EllLimOK3 (pExp α) E)
    (hStar : Work.FTS.Final.StarPkgo2 (pExp α) Cs Φs)
    (hSol : Work.FTS.FinalV2.Sol (pExp α) Φs E g)
    (hOK : Work.FTS.FinalV2.DynOK' (pExp α) C₀ Φs E g)
    (hμ : Work.FTS.RegExportIface.ClockBd α Φs E g) :
    ∀ S > 0, ∃ M : ℝ, ∀ τ ∈ Set.Icc (0:ℝ) S, ∀ j i : ℕ, j + i ≤ 2 → ∀ z θ : ℝ,
      0 < z → 0 < θ → θ < π / 2 →
      |Work.Spaces.mixed j i (fun z θ => Vz7 (pExp α) (μR α Φs E g) (GR α g)
        (ΦR α Φs E g) z θ τ) z θ| ≤ M ∧
      |Work.Spaces.mixed j i (fun z θ => Vθ7 (pExp α) (ΦR α Φs E g) z θ τ
        / Real.sin (2 * θ)) z θ| ≤ M ∧
      |Work.Spaces.mixed j i (fun z θ => cs7 (pExp α) (μR α Φs E g) (GR α g)
        (ΦR α Φs E g) z θ τ) z θ| ≤ M ∧
      |Work.Spaces.pth (fun z θ => Vz7 (pExp α) (μR α Φs E g) (GR α g)
        (ΦR α Φs E g) z θ τ) z θ| ≤ M := by
  intro S hS
  have hαG : (0 : ℝ) < pExp α := Work.FTS.Regularity.pExp_pos hα
  have hS0 : (0 : ℝ) < max S 1 := lt_max_of_lt_right zero_lt_one
  have hVS : S ≤ max S 1 := le_max_left S 1
  -- the uniform slot bounds, the explicit-piece bounds, the `∂_θ`-slot and the `L₁₂`-bound
  obtain ⟨Mv, hMv⟩ := Work.FTS_RegExport.RXT.velVanish2 hα hα13 hEll hEL3 hStar hSol hOK hμ
    (max S 1) hS0
  have hMv0 : 0 ≤ Mv := by
    have hmem : (0 : ℝ) ∈ Set.Icc (0 : ℝ) (max S 1) := ⟨le_refl 0, le_of_lt hS0⟩
    have hpi2 : (1 : ℝ) < Real.pi / 2 := by linarith [Real.pi_gt_three]
    have h := hMv 0 hmem 1 1 (by norm_num) (by norm_num) hpi2
      (Work.Construction.Rop (pExp α) (Work.FTS.RegExportIface.phiTil (pExp α) (GR α g)
        (ΦR α Φs E g) 0)) (by simp) 0 0 (by norm_num)
    have h2 : 0 ≤ Mv * min (1 : ℝ) 1 := le_trans (abs_nonneg _) h
    simpa using h2
  obtain ⟨Cexp, hCexp0, hexp⟩ := explicit_pieces_coeff hα hα13 hOK.2 (max S 1) hS0
  obtain ⟨Mpth, hMpth0, hMpth⟩ := pth_vop_slot_bd hα hα13 hEll hEL3 hStar hSol hOK hμ
    (max S 1) hS0
  obtain ⟨CF, hCF0, -, hL12bd0, -, -, -⟩ := L12FK_family_jets hα hα13 hOK.2 (max S 1) hS0
  refine ⟨max (max (3 / 2 + Cexp + 2 * pExp α * Mv) (2 * Mv + 2 * Cexp))
    (max (3 / 2 + Cexp / pExp α + Cexp + 2 * Mv) (CF * 4 + 2 * pExp α * Mpth)), ?_⟩
  intro τ hτ j i hji z θ hz hθ hθ2
  have hτS : τ ∈ Set.Icc (0 : ℝ) (max S 1) := ⟨hτ.1, le_trans hτ.2 hVS⟩
  -- smoothness of the pieces, at this `τ`
  obtain ⟨hsmA, hsmB, hsmP1, -, hsmLdiv, hsmA', hsmB', hsmA'B', hsmC', hsmU1, hsmU2,
    hsmPsi, hsmTheta⟩ :=
    coeff_pieces_contDiffOn (C₀ := C₀) (Cs := Cs) (g := g) hα hα13 hEL3 hStar hOK hτ.1
  -- the clock
  have hμbd : |μR α Φs E g τ| ≤ 1 / 2 := hμ.1 (max τ 0) (le_max_right τ 0)
  have hphi := v2_PhiT_eq_phiTil (α := α) (Φs := Φs) (E := E) g τ
  -- the three slot bounds
  have hslotV : ∀ j i : ℕ, j + i ≤ 2 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      |Work.Spaces.mixed j i (v2_SlotV α (v2_PhiT α Φs E g τ)) z θ| ≤ Mv := by
    intro j i hji z θ hz hθ hθ2
    have h := hMv τ hτS z θ hz hθ hθ2 (Work.Construction.Vop
      (Work.FTS.RegExportIface.phiTil (pExp α) (GR α g) (ΦR α Φs E g) τ)) (by simp) j i hji
    show |Work.Spaces.mixed j i (Work.Construction.Vop (v2_PhiT α Φs E g τ)) z θ| ≤ Mv
    rw [hphi]
    exact le_trans h (mul_le_of_le_one_right hMv0 (min_le_right z 1))
  have hslotU : ∀ j i : ℕ, j + i ≤ 2 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      |Work.Spaces.mixed j i (v2_SlotU α (v2_PhiT α Φs E g τ)) z θ| ≤ Mv := by
    intro j i hji z θ hz hθ hθ2
    have h := hMv τ hτS z θ hz hθ hθ2 (fun z θ => Work.Construction.Uop (pExp α)
      (Work.FTS.RegExportIface.phiTil (pExp α) (GR α g) (ΦR α Φs E g) τ) z θ
        / Real.sin (2 * θ)) (by simp) j i hji
    show |Work.Spaces.mixed j i (fun z θ => Work.Construction.Uop (pExp α)
      (v2_PhiT α Φs E g τ) z θ / Real.sin (2 * θ)) z θ| ≤ Mv
    rw [hphi]
    exact le_trans h (mul_le_of_le_one_right hMv0 (min_le_right z 1))
  have hslotR : ∀ j i : ℕ, j + i ≤ 2 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      |Work.Spaces.mixed j i (v2_SlotR α (v2_PhiT α Φs E g τ)) z θ| ≤ Mv := by
    intro j i hji z θ hz hθ hθ2
    have h := hMv τ hτS z θ hz hθ hθ2 (Work.Construction.Rop (pExp α)
      (Work.FTS.RegExportIface.phiTil (pExp α) (GR α g) (ΦR α Φs E g) τ)) (by simp) j i hji
    show |Work.Spaces.mixed j i (Work.Construction.Rop (pExp α)
      (v2_PhiT α Φs E g τ)) z θ| ≤ Mv
    rw [hphi]
    exact le_trans h (mul_le_of_le_one_right hMv0 (min_le_right z 1))
  -- the explicit-piece bounds
  have hexp1 : ∀ j i : ℕ, j + i ≤ 2 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      |Work.Spaces.mixed j i (fun z θ => L12 (Ftau (pExp α) (GR α g) τ) z * c2m θ) z θ|
        ≤ Cexp :=
    fun j i hji z θ hz hθ hθ2 => (hexp τ hτS j i hji z θ hz hθ hθ2).1
  have hexp2 : ∀ j i : ℕ, j + i ≤ 2 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      |Work.Spaces.mixed j i (fun z θ => L12 (Ftau (pExp α) (GR α g) τ) z) z θ| ≤ Cexp :=
    fun j i hji z θ hz hθ hθ2 => (hexp τ hτS j i hji z θ hz hθ hθ2).2.1
  have hexp3 : ∀ j i : ℕ, j + i ≤ 2 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      |Work.Spaces.mixed j i (fun z θ => (Real.sin θ) ^ 2 * FK
        (Ftau (pExp α) (GR α g) τ) z) z θ| ≤ Cexp :=
    fun j i hji z θ hz hθ hθ2 => (hexp τ hτS j i hji z θ hz hθ hθ2).2.2.1
  have hexp4 : ∀ j i : ℕ, j + i ≤ 2 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      |Work.Spaces.mixed j i (fun z θ => Uop (pExp α) (Theta (pExp α)
        (Ftau (pExp α) (GR α g) τ)) z θ / Real.sin (2 * θ)) z θ| ≤ Cexp :=
    fun j i hji z θ hz hθ hθ2 => (hexp τ hτS j i hji z θ hz hθ hθ2).2.2.2
  -- the four bounds
  have hV := Vz7_jets_le (Mslot := Mv) (Cexp := Cexp) hαG hsmA hsmB hsmP1 hμbd hslotV hexp1
    j i hji z θ hz hθ hθ2
  have hVth := Vth_jets_le (Mslot := Mv) (Cexp := Cexp) hαG hsmU1 hsmU2 hsmPsi hsmTheta hslotU
    hexp4 j i hji z θ hz hθ hθ2
  have hCs := Cs_jets_le (Mslot := Mv) (Cexp := Cexp) hαG hsmA' hsmB' hsmA'B' hsmC' hsmLdiv
    hμbd hslotR hexp2 hexp3 j i hji z θ hz hθ hθ2
  have hPth := Vz7_pth_le (CF := CF) (Mpth := Mpth) hαG hsmA hsmB
    (hMpth τ hτS) hCF0 (fun z hz => hL12bd0 τ hτS z hz) z θ hz hθ hθ2
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact le_trans hV (le_trans (le_max_left _ _) (le_max_left _ _))
  · exact le_trans hVth (le_trans (le_max_right _ _) (le_max_left _ _))
  · exact le_trans hCs (le_trans (le_max_left _ _) (le_max_right _ _))
  · exact le_trans hPth (le_trans (le_max_right _ _) (le_max_right _ _))

end Work.FTS_RegExport.RXT.Sys
end
end
-- ===== merged: Submission.Work.FTS_RegExport.RXT.Sys.forcing_bound =====
section

set_option synthInstance.maxHeartbeats 400000 -- v435-synth

namespace Work.FTS_RegExport.RXT.Sys

theorem forcing_bound {S α C₀ : ℝ} {Φs : Work.FTS.Galerkin.Fn}
    {E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn} {g : Work.FTS.Galerkin.Fam}
    (hS : 0 < S) (hα : 0 < α) (hα13 : α ≤ 1 / 3)
    (hOK : Work.FTS.FinalV2.DynOK' (Work.FTS.Regularity.pExp α) C₀ Φs E g)
    (hVP : Work.FTS_RegExport.RXT.CoeffJets (Work.FTS.Regularity.pExp α)
      (Work.FTS.RegExportIface.RXT.μR α Φs E g) (Work.FTS.RegExportIface.RXT.GR α g)
      (Work.FTS.RegExportIface.RXT.ΦR α Φs E g) S)
    (hV2 : ∃ M : ℝ, ∀ τ ∈ Set.Icc (0:ℝ) S, ∀ z θ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      ∀ Q ∈ ({(Work.Construction.Rop (Work.FTS.Regularity.pExp α)
            (Work.FTS.RegExportIface.phiTil (Work.FTS.Regularity.pExp α)
              (Work.FTS.RegExportIface.RXT.GR α g) (Work.FTS.RegExportIface.RXT.ΦR α Φs E g) τ)),
          Work.Construction.Vop
            (Work.FTS.RegExportIface.phiTil (Work.FTS.Regularity.pExp α)
              (Work.FTS.RegExportIface.RXT.GR α g) (Work.FTS.RegExportIface.RXT.ΦR α Φs E g) τ),
          fun z θ => Work.Construction.Uop (Work.FTS.Regularity.pExp α)
            (Work.FTS.RegExportIface.phiTil (Work.FTS.Regularity.pExp α)
              (Work.FTS.RegExportIface.RXT.GR α g) (Work.FTS.RegExportIface.RXT.ΦR α Φs E g) τ) z θ
            / Real.sin (2 * θ)} : Set (ℝ → ℝ → ℝ)),
        ∀ j i : ℕ, j + i ≤ 2 → |Work.Spaces.mixed j i Q z θ| ≤ M * min z 1)
    (hC2 : ∀ τ : ℝ, 0 ≤ τ →
      ContDiffOn ℝ 2 (Function.uncurry (fun z θ => Work.FTS.RegExportIface.RXT.VR α Φs E g z θ τ))
        Work.FTS.EllipticEst.Q0 ∧
      ContDiffOn ℝ 2 (Function.uncurry (fun z θ => Work.FTS.RegExportIface.RXT.bR α Φs E g z θ τ))
        Work.FTS.EllipticEst.Q0 ∧
      ContDiffOn ℝ 2 (Function.uncurry (fun z θ => Work.FTS.RegExportIface.RXT.cR α Φs E g z θ τ))
        Work.FTS.EllipticEst.Q0)
    (hL12 : ∀ τ : ℝ, 0 ≤ τ → Work.Construction.L12 (Work.FTS.Galerkin.slice g τ) 0 = 0)
    (hw : ∃ C : ℝ, ∀ τ ∈ Set.Icc (0:ℝ) S, ∀ b a : ℕ, a + b ≤ 2 → ∀ z θ : ℝ, 0 < z → 0 < θ →
      θ < Real.pi / 2 → |Work.Spaces.mixed b a (Work.FTS.Galerkin.slice g τ) z θ|
        ≤ C * (z ^ ((3 : ℝ) / 2) / (1 + z) ^ 2)) :
    ∃ KS : ℝ, 0 ≤ KS ∧ ∀ k : Fin 6, ∀ z θ σ, 0 < z → 0 < θ → θ < Real.pi / 2 → 0 ≤ σ → σ ≤ S →
      |Work.Spaces.mixed (Work.FTS.RegExportIface.RXT.idx k).1
        (Work.FTS.RegExportIface.RXT.idx k).2
        (Work.FTS.RegExportIface.RXT.SigR α Φs E g σ) z θ|
        ≤ KS * Work.FTS.RegExportIface.ω α z θ := by
  obtain ⟨K, hK0, hK⟩ :=
    Zhat_bound (C₀ := C₀) hα hα13 hS hOK hVP hV2 hC2 hL12 hw
  have hβ0 : 0 < Work.FTS.Regularity.pExp α := Work.FTS.Regularity.pExp_pos hα
  have hβ1 : Work.FTS.Regularity.pExp α ≤ 1 := Work.FTS.Regularity.pExp_le_one hα13
  have hc0 : 0 < Work.Spaces.c (Work.FTS.Regularity.pExp α) := by
    have := (Work.Spaces.c_bounds (Work.FTS.Regularity.pExp α) hβ0 hβ1).1
    linarith
  refine ⟨(Work.FTS.Regularity.pExp α / Work.Spaces.c (Work.FTS.Regularity.pExp α))
      * 4 * 100000 * K, by positivity, ?_⟩
  intro k z θ σ hz hθ0 hθ1 hσ0 hσS
  have hσ : σ ∈ Set.Icc (0:ℝ) S := ⟨hσ0, hσS⟩
  have hji : (Work.FTS.RegExportIface.RXT.idx k).1
      + (Work.FTS.RegExportIface.RXT.idx k).2 ≤ 2 := by
    fin_cases k <;> decide
  have hzθ : (z, θ) ∈ Work.FTS.EllipticEst.Q0 := ⟨hz, hθ0, hθ1⟩
  have hZc : ContDiffOn ℝ 2 (Function.uncurry (fun z θ =>
      Work.FTS.RegExportIface.RXT.VR α Φs E g z θ σ * A1f z θ
        + Work.FTS.RegExportIface.RXT.bR α Φs E g z θ σ
            * B1f (Work.FTS.Regularity.pExp α) z θ
        + Work.FTS.RegExportIface.RXT.cR α Φs E g z θ σ * Fhf z θ))
      Work.FTS.EllipticEst.Q0 :=
    Zhat_contDiffOn (C₀ := C₀) hα hα13 hS hC2 σ hσ
  have hZb : |Work.Spaces.mixed (Work.FTS.RegExportIface.RXT.idx k).1
      (Work.FTS.RegExportIface.RXT.idx k).2 (fun z θ =>
      Work.FTS.RegExportIface.RXT.VR α Φs E g z θ σ * A1f z θ
        + Work.FTS.RegExportIface.RXT.bR α Φs E g z θ σ
            * B1f (Work.FTS.Regularity.pExp α) z θ
        + Work.FTS.RegExportIface.RXT.cR α Φs E g z θ σ * Fhf z θ) z θ|
      ≤ K * (z ^ 2 / (1 + z) ^ 2) :=
    hK σ hσ (Work.FTS.RegExportIface.RXT.idx k).1 (Work.FTS.RegExportIface.RXT.idx k).2
      hji z θ hz hθ0 hθ1
  have hEq : Set.EqOn (Function.uncurry (Work.FTS.RegExportIface.RXT.SigR α Φs E g σ))
      (Function.uncurry (fun z θ => (Work.FTS.Regularity.pExp α
        / Work.Spaces.c (Work.FTS.Regularity.pExp α))
        * Work.Spaces.Gam (Work.FTS.Regularity.pExp α) θ
        * (Work.FTS.RegExportIface.RXT.VR α Φs E g z θ σ * A1f z θ
            + Work.FTS.RegExportIface.RXT.bR α Φs E g z θ σ
                * B1f (Work.FTS.Regularity.pExp α) z θ
            + Work.FTS.RegExportIface.RXT.cR α Φs E g z θ σ * Fhf z θ)))
      Work.FTS.EllipticEst.Q0 := by
    intro p hp
    obtain ⟨z', θ'⟩ := p
    exact Work.FTS_RegExport.RXT.SysAux.SigR_eq_reduced hα hα13 hS σ ⟨hσ0, hσS⟩
      z' θ' hp.1 hp.2.1 hp.2.2
  have hfGam : ContDiffOn ℝ ((Work.FTS.RegExportIface.RXT.idx k).1
      + (Work.FTS.RegExportIface.RXT.idx k).2)
      (Function.uncurry (fun _ θ : ℝ => Work.Spaces.Gam (Work.FTS.Regularity.pExp α) θ))
      Work.FTS.EllipticEst.Q0 := by
    have hG := Work.FTS_RegExport.RXT.ftau_contDiffOn_Gam_Q0 (Work.FTS.Regularity.pExp α)
      ((Work.FTS.RegExportIface.RXT.idx k).1 + (Work.FTS.RegExportIface.RXT.idx k).2)
    rw [Nat.cast_add] at hG
    exact hG
  have hbfGam : ∀ a b : ℕ, a + b ≤ (Work.FTS.RegExportIface.RXT.idx k).1
      + (Work.FTS.RegExportIface.RXT.idx k).2 →
      |Work.Spaces.mixed b a (fun z θ : ℝ => Work.Spaces.Gam (Work.FTS.Regularity.pExp α) θ) z θ|
        ≤ 100000 * Work.Spaces.Gam (Work.FTS.Regularity.pExp α) θ := by
    intro a b hab
    rcases Nat.eq_zero_or_pos b with hb | hb
    · subst hb
      rw [Work.Spaces.mixed, Work.Spaces.DzIter_zero]
      rw [show Work.Spaces.DthIter a (fun z θ : ℝ => Work.Spaces.Gam (Work.FTS.Regularity.pExp α) θ) z θ
          = Work.Spaces.DthIter a (fun _ θ' : ℝ => Work.Spaces.Gam (Work.FTS.Regularity.pExp α) θ') z θ
          from rfl]
      rw [DthIter_z_indep (fun θ' => Work.Spaces.Gam (Work.FTS.Regularity.pExp α) θ') a z 0 θ]
      exact Work.FTS.LocData6.DthIter_Gam_abs_le6 a (by omega)
        (Work.FTS.Regularity.pExp α) hβ0 hβ1 ⟨hθ0.le, hθ1.le⟩
    · rw [mixed_theta_only (fun θ' => Work.Spaces.Gam (Work.FTS.Regularity.pExp α) θ') hb z θ,
        abs_zero]
      exact mul_nonneg (by norm_num) (Work.Spaces.Gam_bounds (Work.FTS.Regularity.pExp α)
        θ hβ0 ⟨hθ0.le, hθ1.le⟩).1
  have hbhZ : ∀ a b : ℕ, a + b ≤ (Work.FTS.RegExportIface.RXT.idx k).1
      + (Work.FTS.RegExportIface.RXT.idx k).2 →
      |Work.Spaces.mixed b a (fun z θ =>
        Work.FTS.RegExportIface.RXT.VR α Φs E g z θ σ * A1f z θ
          + Work.FTS.RegExportIface.RXT.bR α Φs E g z θ σ
              * B1f (Work.FTS.Regularity.pExp α) z θ
          + Work.FTS.RegExportIface.RXT.cR α Φs E g z θ σ * Fhf z θ) z θ|
        ≤ K * (z ^ 2 / (1 + z) ^ 2) :=
      fun a b hab => hK σ hσ b a (by omega) z θ hz hθ0 hθ1
  have hGam : |Work.Spaces.mixed (Work.FTS.RegExportIface.RXT.idx k).1
      (Work.FTS.RegExportIface.RXT.idx k).2 (fun z θ =>
        Work.Spaces.Gam (Work.FTS.Regularity.pExp α) θ
        * (Work.FTS.RegExportIface.RXT.VR α Φs E g z θ σ * A1f z θ
            + Work.FTS.RegExportIface.RXT.bR α Φs E g z θ σ
                * B1f (Work.FTS.Regularity.pExp α) z θ
            + Work.FTS.RegExportIface.RXT.cR α Φs E g z θ σ * Fhf z θ)) z θ|
      ≤ 4 * (100000 * Work.Spaces.Gam (Work.FTS.Regularity.pExp α) θ)
        * (K * (z ^ 2 / (1 + z) ^ 2)) := by
    refine le_trans (abs_mixed_mul_bound (j := (Work.FTS.RegExportIface.RXT.idx k).1)
      (i := (Work.FTS.RegExportIface.RXT.idx k).2) (V := Work.FTS.EllipticEst.Q0)
      Work.FTS.EllipticEst.isOpen_Q0
      (by
        have hG := Work.FTS_RegExport.RXT.ftau_contDiffOn_Gam_Q0 (Work.FTS.Regularity.pExp α)
          ((Work.FTS.RegExportIface.RXT.idx k).1 + (Work.FTS.RegExportIface.RXT.idx k).2)
        rw [Nat.cast_add] at hG
        exact hG)
      (hZc.of_le (Nat.cast_le.mpr hji)) hzθ
      (Cf := 100000 * Work.Spaces.Gam (Work.FTS.Regularity.pExp α) θ)
      (Cg := K * (z ^ 2 / (1 + z) ^ 2))
      (mul_nonneg (by norm_num) (Work.Spaces.Gam_bounds (Work.FTS.Regularity.pExp α) θ hβ0
        ⟨hθ0.le, hθ1.le⟩).1)
      (mul_nonneg hK0 (by positivity)) hbfGam hbhZ) ?_
    have hpow : (2 : ℝ) ^ ((Work.FTS.RegExportIface.RXT.idx k).1
        + (Work.FTS.RegExportIface.RXT.idx k).2) ≤ 4 := by
      calc (2 : ℝ) ^ ((Work.FTS.RegExportIface.RXT.idx k).1
            + (Work.FTS.RegExportIface.RXT.idx k).2) ≤ 2 ^ 2 :=
            pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2) hji
        _ = 4 := by norm_num
    have hCfCg : 0 ≤ (100000 * Work.Spaces.Gam (Work.FTS.Regularity.pExp α) θ)
        * (K * (z ^ 2 / (1 + z) ^ 2)) :=
      mul_nonneg (mul_nonneg (by norm_num) (Work.Spaces.Gam_bounds (Work.FTS.Regularity.pExp α)
        θ hβ0 ⟨hθ0.le, hθ1.le⟩).1) (mul_nonneg hK0 (by positivity))
    calc (2 : ℝ) ^ ((Work.FTS.RegExportIface.RXT.idx k).1
          + (Work.FTS.RegExportIface.RXT.idx k).2)
          * ((100000 * Work.Spaces.Gam (Work.FTS.Regularity.pExp α) θ)
            * (K * (z ^ 2 / (1 + z) ^ 2)))
        ≤ 4 * ((100000 * Work.Spaces.Gam (Work.FTS.Regularity.pExp α) θ)
            * (K * (z ^ 2 / (1 + z) ^ 2))) := mul_le_mul_of_nonneg_right hpow hCfCg
      _ = 4 * (100000 * Work.Spaces.Gam (Work.FTS.Regularity.pExp α) θ)
            * (K * (z ^ 2 / (1 + z) ^ 2)) := by ring
  calc |Work.Spaces.mixed (Work.FTS.RegExportIface.RXT.idx k).1
        (Work.FTS.RegExportIface.RXT.idx k).2
        (Work.FTS.RegExportIface.RXT.SigR α Φs E g σ) z θ|
      = |Work.Spaces.mixed (Work.FTS.RegExportIface.RXT.idx k).1
          (Work.FTS.RegExportIface.RXT.idx k).2 (fun z θ => (Work.FTS.Regularity.pExp α
            / Work.Spaces.c (Work.FTS.Regularity.pExp α))
            * Work.Spaces.Gam (Work.FTS.Regularity.pExp α) θ
            * (Work.FTS.RegExportIface.RXT.VR α Φs E g z θ σ * A1f z θ
                + Work.FTS.RegExportIface.RXT.bR α Φs E g z θ σ
                    * B1f (Work.FTS.Regularity.pExp α) z θ
                + Work.FTS.RegExportIface.RXT.cR α Φs E g z θ σ * Fhf z θ)) z θ| := by
        rw [Work.FTS_RegExport.RXT.SysAux.mixed_congr_of_isOpen
          Work.FTS.EllipticEst.isOpen_Q0 hEq _ _ z θ hzθ]
    _ = |(Work.FTS.Regularity.pExp α / Work.Spaces.c (Work.FTS.Regularity.pExp α))
          * Work.Spaces.mixed (Work.FTS.RegExportIface.RXT.idx k).1
              (Work.FTS.RegExportIface.RXT.idx k).2 (fun z θ =>
              Work.Spaces.Gam (Work.FTS.Regularity.pExp α) θ
              * (Work.FTS.RegExportIface.RXT.VR α Φs E g z θ σ * A1f z θ
                  + Work.FTS.RegExportIface.RXT.bR α Φs E g z θ σ
                      * B1f (Work.FTS.Regularity.pExp α) z θ
                  + Work.FTS.RegExportIface.RXT.cR α Φs E g z θ σ * Fhf z θ)) z θ| := by
        rw [show (fun z θ => (Work.FTS.Regularity.pExp α
              / Work.Spaces.c (Work.FTS.Regularity.pExp α))
              * Work.Spaces.Gam (Work.FTS.Regularity.pExp α) θ
              * (Work.FTS.RegExportIface.RXT.VR α Φs E g z θ σ * A1f z θ
                  + Work.FTS.RegExportIface.RXT.bR α Φs E g z θ σ
                      * B1f (Work.FTS.Regularity.pExp α) z θ
                  + Work.FTS.RegExportIface.RXT.cR α Φs E g z θ σ * Fhf z θ))
            = fun z θ => (Work.FTS.Regularity.pExp α
              / Work.Spaces.c (Work.FTS.Regularity.pExp α))
              * (Work.Spaces.Gam (Work.FTS.Regularity.pExp α) θ
              * (Work.FTS.RegExportIface.RXT.VR α Φs E g z θ σ * A1f z θ
                  + Work.FTS.RegExportIface.RXT.bR α Φs E g z θ σ
                      * B1f (Work.FTS.Regularity.pExp α) z θ
                  + Work.FTS.RegExportIface.RXT.cR α Φs E g z θ σ * Fhf z θ)) from by
            funext z' θ'; ring,
          mixed_const_mul]
    _ = (Work.FTS.Regularity.pExp α / Work.Spaces.c (Work.FTS.Regularity.pExp α))
          * |Work.Spaces.mixed (Work.FTS.RegExportIface.RXT.idx k).1
              (Work.FTS.RegExportIface.RXT.idx k).2 (fun z θ =>
              Work.Spaces.Gam (Work.FTS.Regularity.pExp α) θ
              * (Work.FTS.RegExportIface.RXT.VR α Φs E g z θ σ * A1f z θ
                  + Work.FTS.RegExportIface.RXT.bR α Φs E g z θ σ
                      * B1f (Work.FTS.Regularity.pExp α) z θ
                  + Work.FTS.RegExportIface.RXT.cR α Φs E g z θ σ * Fhf z θ)) z θ| := by
        rw [abs_mul, abs_of_nonneg (by positivity)]
    _ ≤ (Work.FTS.Regularity.pExp α / Work.Spaces.c (Work.FTS.Regularity.pExp α))
          * (4 * (100000 * Work.Spaces.Gam (Work.FTS.Regularity.pExp α) θ)
              * (K * (z ^ 2 / (1 + z) ^ 2))) :=
        mul_le_mul_of_nonneg_left hGam (by positivity)
    _ = ((Work.FTS.Regularity.pExp α / Work.Spaces.c (Work.FTS.Regularity.pExp α))
          * 4 * 100000 * K) * Work.FTS.RegExportIface.ω α z θ := by
        rw [Work.FTS_RegExport.RXT.Gam_pExp_eq_Gamma, Work.FTS.RegExportIface.ω]
        ring

end Work.FTS_RegExport.RXT.Sys
end
-- ===== merged: Submission.Work.FTS_RegExport.RXT0.RXJets.coeffVR =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS_RegExport.RXT0.RXJets.coeffVR` — the joint continuity of the jets of `VR`

The `VR` conjunct of `coeffJetsJointCont`.  `VR = (1-μ) + L₁₂(F_τ)·c2m + 2α·𝒱(Φ̃_τ)` with
`Φ̃_τ = Φ̃_* + Ξ_τ` on the open quadrant; each of the four pieces is handled by the generic
lemmas of `jetBasic` and the star/perturbation slot continuities, and the mixed jets are
expanded with the additivity `RXT.Sys.mixed_add_lam`.
-/

noncomputable section

open scoped Real Topology
open Set Filter

namespace Work.FTS_RegExport.RXT0.RXJets

set_option autoImplicit false
set_option maxHeartbeats 3800000

open Work.FTS_RegExport.RXT (v2_PhiT v2_PhiStar v2_PhiPert)

/-- **The `VR` conjunct of `coeffJetsJointCont`.** -/
theorem coeffVR {α C₀ Ce Cs : ℝ} {Φs : Work.FTS.Galerkin.Fn}
    {E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn} {g : Work.FTS.Galerkin.Fam}
    (H : CJHyps α C₀ Ce Cs Φs E g) :
    ∀ S > 0, ∀ k l : ℕ, k + l ≤ 2 →
      ContinuousOn (fun p : ℝ × ℝ × ℝ => Work.Spaces.mixed k l
        (fun z θ => Work.FTS.RegExportIface.RXT.VR α Φs E g z θ p.2.2) p.1 p.2.1)
        (Set.Ioi (0:ℝ) ×ˢ (Set.Ioo (0:ℝ) (Real.pi / 2) ×ˢ Set.Icc (0:ℝ) S)) := by
  have hα := H.hα
  have hα13 := H.hα13
  have hEll := H.hEll
  have hEL3 := H.hEL3
  have hStar := H.hStar
  have hSol := H.hSol
  have hOK := H.hOK
  have hμ := H.hμ
  have hL12 := H.hL12
  have hSlot := H.hSlot
  obtain ⟨hMixedConst, hConstCont, hCdC2m, hCdSinsq, hDthAng, hRadialCont, hRadAngCont⟩ :=
    Work.FTS_RegExport.RXT0.RXJets.jetBasic
  have hStar3 := CJHyps.hStar3 H
  have hStar1 := CJHyps.hStar1 H
  have hPert3 := CJHyps.hPert3 H
  intro S hS k l hkl
  have hk2 : k ≤ 2 := by omega
  have hl2 : l ≤ 2 := by omega
  have hdzd := CJHyps.hdzd H S hS
  have hμRc := CJHyps.hμRc H S
  obtain ⟨hStarVop, hStarRop, hStarUdiv⟩ := CJHyps.hStarSlots H S k l hkl
  -- ## the `C²` facts of the VR pieces
  have hVRc2 : ∀ τ ∈ Set.Icc (0:ℝ) S,
      ContDiffOn ℝ 2 (Function.uncurry (fun z θ => (1 : ℝ)
        - Work.FTS.RegExportIface.RXT.μR α Φs E g τ
        + Work.Construction.L12 (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
            (Work.FTS.RegExportIface.RXT.GR α g) τ) z * Work.Construction.c2m θ))
        Work.FTS.EllipticEst.Q0 ∧
      ContDiffOn ℝ 2 (Function.uncurry (fun z θ => Work.Construction.L12
          (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
            (Work.FTS.RegExportIface.RXT.GR α g) τ) z * Work.Construction.c2m θ))
        Work.FTS.EllipticEst.Q0 ∧
      ContDiffOn ℝ 2 (Function.uncurry (fun z θ => ((2 : ℝ) * Work.FTS.Regularity.pExp α)
          * Work.Construction.Vop (v2_PhiStar α Φs) z θ)) Work.FTS.EllipticEst.Q0 ∧
      ContDiffOn ℝ 2 (Function.uncurry (fun z θ => ((2 : ℝ) * Work.FTS.Regularity.pExp α)
          * Work.Construction.Vop (v2_PhiPert α E g τ) z θ)) Work.FTS.EllipticEst.Q0 ∧
      ContDiffOn ℝ 2 (Function.uncurry (fun _ _ : ℝ => (1 : ℝ)
          - Work.FTS.RegExportIface.RXT.μR α Φs E g τ)) Work.FTS.EllipticEst.Q0 := by
    intro τ hτ
    obtain ⟨h1, -, h3, -, -, -, -, -, -, -, -, -, -⟩ :=
      Work.FTS_RegExport.RXT.Sys.coeff_pieces_contDiffOn (τ := τ) hα hα13 hEL3 hStar hOK hτ.1
    exact ⟨h1, h3,
      (contDiffOn_const (c := (2 : ℝ) * Work.FTS.Regularity.pExp α)).mul
        (Work.FTS_RegExport.RXT.contDiffOn_uncurry_Vop hStar3),
      (contDiffOn_const (c := (2 : ℝ) * Work.FTS.Regularity.pExp α)).mul
        (Work.FTS_RegExport.RXT.contDiffOn_uncurry_Vop (hPert3 τ hτ.1)),
      contDiffOn_const⟩
  refine ContinuousOn.congr (f := fun p : ℝ × ℝ × ℝ =>
      Work.Spaces.mixed k l (fun _ _ : ℝ => (1 : ℝ)
          - Work.FTS.RegExportIface.RXT.μR α Φs E g p.2.2) p.1 p.2.1
      + Work.Spaces.mixed k l (fun z θ => Work.Construction.L12
          (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
            (Work.FTS.RegExportIface.RXT.GR α g) p.2.2) z * Work.Construction.c2m θ) p.1 p.2.1
      + Work.Spaces.mixed k l (fun z θ => ((2 : ℝ) * Work.FTS.Regularity.pExp α)
          * Work.Construction.Vop (v2_PhiStar α Φs) z θ) p.1 p.2.1
      + Work.Spaces.mixed k l (fun z θ => ((2 : ℝ) * Work.FTS.Regularity.pExp α)
          * Work.Construction.Vop (v2_PhiPert α E g p.2.2) z θ) p.1 p.2.1) ?_ ?_
  · have hc0 : ContinuousOn (fun p : ℝ × ℝ × ℝ => Work.Spaces.mixed k l
          (fun _ _ : ℝ => (1 : ℝ) - Work.FTS.RegExportIface.RXT.μR α Φs E g p.2.2) p.1 p.2.1)
          (Work.FTS_RegExport.RXT0.RXJets.slb S) :=
        hConstCont (c := fun τ : ℝ => (1 : ℝ) - Work.FTS.RegExportIface.RXT.μR α Φs E g τ)
          ((continuousOn_const (c := (1 : ℝ))).sub hμRc) k l
    have hc1 : ContinuousOn (fun p : ℝ × ℝ × ℝ => Work.Spaces.mixed k l
          (fun z θ => Work.Construction.L12 (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
              (Work.FTS.RegExportIface.RXT.GR α g) p.2.2) z * Work.Construction.c2m θ)
          p.1 p.2.1) (Work.FTS_RegExport.RXT0.RXJets.slb S) :=
        hRadAngCont (a := fun z τ => Work.Construction.L12
            (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
              (Work.FTS.RegExportIface.RXT.GR α g) τ) z) (b := Work.Construction.c2m)
          (hdzd k hk2).1 (hDthAng hCdC2m l hl2)
    have hc2 : ContinuousOn (fun p : ℝ × ℝ × ℝ => Work.Spaces.mixed k l
          (fun z θ => ((2 : ℝ) * Work.FTS.Regularity.pExp α)
            * Work.Construction.Vop (v2_PhiStar α Φs) z θ) p.1 p.2.1)
          (Work.FTS_RegExport.RXT0.RXJets.slb S) :=
        (hStarVop.const_mul (2 * Work.FTS.Regularity.pExp α)).congr (fun p hp => by
          rw [Work.FTS_RegExport.RXT.Sys.coeff_mixed_const_mul])
    have hc3 : ContinuousOn (fun p : ℝ × ℝ × ℝ => Work.Spaces.mixed k l
          (fun z θ => ((2 : ℝ) * Work.FTS.Regularity.pExp α)
            * Work.Construction.Vop (v2_PhiPert α E g p.2.2) z θ) p.1 p.2.1)
          (Work.FTS_RegExport.RXT0.RXJets.slb S) :=
        ((hSlot S hS k l hkl).1.const_mul (2 * Work.FTS.Regularity.pExp α)).congr
          (fun p hp => by
            rw [Work.FTS_RegExport.RXT.Sys.coeff_mixed_const_mul])
    exact ((hc0.add hc1).add hc2).add hc3
  · intro p hp
    show Work.Spaces.mixed k l (fun z θ =>
          Work.FTS.RegExportIface.RXT.VR α Φs E g z θ p.2.2) p.1 p.2.1
        = Work.Spaces.mixed k l (fun _ _ : ℝ => (1 : ℝ)
              - Work.FTS.RegExportIface.RXT.μR α Φs E g p.2.2) p.1 p.2.1
          + Work.Spaces.mixed k l (fun z θ => Work.Construction.L12
              (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
                (Work.FTS.RegExportIface.RXT.GR α g) p.2.2) z * Work.Construction.c2m θ)
              p.1 p.2.1
          + Work.Spaces.mixed k l (fun z θ => ((2 : ℝ) * Work.FTS.Regularity.pExp α)
              * Work.Construction.Vop (v2_PhiStar α Φs) z θ) p.1 p.2.1
          + Work.Spaces.mixed k l (fun z θ => ((2 : ℝ) * Work.FTS.Regularity.pExp α)
              * Work.Construction.Vop (v2_PhiPert α E g p.2.2) z θ) p.1 p.2.1
    obtain ⟨hz, hθ, hθ2, hτ0, hτS⟩ := mem_slb.mp hp
    have hzθ : (p.1, p.2.1) ∈ Work.FTS.EllipticEst.Q0 := ⟨hz, hθ, hθ2⟩
    have hC2τ := hVRc2 p.2.2 ⟨hτ0, hτS⟩
    have hPert1 := CJHyps.hPert1g H p.2.2 hτ0
    have hag := CJHyps.hagQ H p.2.2 hτ0
    have hsplit : Set.EqOn (Function.uncurry (fun z θ =>
          Work.FTS.RegExportIface.RXT.VR α Φs E g z θ p.2.2))
        (Function.uncurry (fun z θ => (((1 : ℝ)
            - Work.FTS.RegExportIface.RXT.μR α Φs E g p.2.2)
          + Work.Construction.L12 (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
              (Work.FTS.RegExportIface.RXT.GR α g) p.2.2) z * Work.Construction.c2m θ)
          + (((2 : ℝ) * Work.FTS.Regularity.pExp α) * Work.Construction.Vop (v2_PhiStar α Φs) z θ
            + ((2 : ℝ) * Work.FTS.Regularity.pExp α)
              * Work.Construction.Vop (v2_PhiPert α E g p.2.2) z θ)))
        Work.FTS.EllipticEst.Q0 := by
      intro q hq
      obtain ⟨hz', hθ', hθ2'⟩ := Work.FTS.EllipticEst.mem_Q0.mp hq
      simp only [Function.uncurry]
      have hVc := Work.FTS_RegExport.RXR5.Vop_congr_of_agreeOnQ hag hz' hθ' hθ2'
      have hVa : Work.Construction.Vop (v2_PhiStar α Φs + v2_PhiPert α E g p.2.2) q.1 q.2
          = Work.Construction.Vop (v2_PhiStar α Φs) q.1 q.2
            + Work.Construction.Vop (v2_PhiPert α E g p.2.2) q.1 q.2 :=
        Work.FTS_RegExport.RXT.v2_vop_add_at hStar1 hPert1 ⟨hz', hθ', hθ2'⟩
      rw [show Work.FTS.RegExportIface.RXT.VR α Φs E g q.1 q.2 p.2.2
          = (1 - Work.FTS.RegExportIface.RXT.μR α Φs E g p.2.2)
            + Work.Construction.L12 (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
                (Work.FTS.RegExportIface.RXT.GR α g) p.2.2) q.1 * Work.Construction.c2m q.2
            + 2 * Work.FTS.Regularity.pExp α
              * Work.Construction.Vop (v2_PhiT α Φs E g p.2.2) q.1 q.2 from rfl]
      rw [hVc, hVa]
      ring
    have hstepA : Work.Spaces.mixed k l (fun z θ => (((1 : ℝ)
            - Work.FTS.RegExportIface.RXT.μR α Φs E g p.2.2)
          + Work.Construction.L12 (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
              (Work.FTS.RegExportIface.RXT.GR α g) p.2.2) z * Work.Construction.c2m θ)
          + (((2 : ℝ) * Work.FTS.Regularity.pExp α) * Work.Construction.Vop (v2_PhiStar α Φs) z θ
            + ((2 : ℝ) * Work.FTS.Regularity.pExp α)
              * Work.Construction.Vop (v2_PhiPert α E g p.2.2) z θ)) p.1 p.2.1
        = Work.Spaces.mixed k l (fun z θ => ((1 : ℝ)
              - Work.FTS.RegExportIface.RXT.μR α Φs E g p.2.2)
            + Work.Construction.L12 (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
                (Work.FTS.RegExportIface.RXT.GR α g) p.2.2) z * Work.Construction.c2m θ)
            p.1 p.2.1
          + Work.Spaces.mixed k l (fun z θ =>
              ((2 : ℝ) * Work.FTS.Regularity.pExp α) * Work.Construction.Vop (v2_PhiStar α Φs) z θ
              + ((2 : ℝ) * Work.FTS.Regularity.pExp α)
                * Work.Construction.Vop (v2_PhiPert α E g p.2.2) z θ) p.1 p.2.1 :=
      Work.FTS_RegExport.RXT.Sys.mixed_add_lam (f := fun z θ => ((1 : ℝ)
            - Work.FTS.RegExportIface.RXT.μR α Φs E g p.2.2)
            + Work.Construction.L12 (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
                (Work.FTS.RegExportIface.RXT.GR α g) p.2.2) z * Work.Construction.c2m θ)
        (h := fun z θ =>
            ((2 : ℝ) * Work.FTS.Regularity.pExp α) * Work.Construction.Vop (v2_PhiStar α Φs) z θ
            + ((2 : ℝ) * Work.FTS.Regularity.pExp α)
              * Work.Construction.Vop (v2_PhiPert α E g p.2.2) z θ)
        hC2τ.1 (hC2τ.2.2.1.add hC2τ.2.2.2.1) hkl hzθ
    have hstepB : Work.Spaces.mixed k l (fun z θ => ((1 : ℝ)
          - Work.FTS.RegExportIface.RXT.μR α Φs E g p.2.2)
          + Work.Construction.L12 (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
              (Work.FTS.RegExportIface.RXT.GR α g) p.2.2) z * Work.Construction.c2m θ) p.1 p.2.1
        = Work.Spaces.mixed k l (fun _ _ : ℝ => (1 : ℝ)
              - Work.FTS.RegExportIface.RXT.μR α Φs E g p.2.2) p.1 p.2.1
          + Work.Spaces.mixed k l (fun z θ => Work.Construction.L12
              (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
                (Work.FTS.RegExportIface.RXT.GR α g) p.2.2) z * Work.Construction.c2m θ)
              p.1 p.2.1 :=
      Work.FTS_RegExport.RXT.Sys.mixed_add_lam
        (f := fun _ _ : ℝ => (1 : ℝ) - Work.FTS.RegExportIface.RXT.μR α Φs E g p.2.2)
        (h := fun z θ => Work.Construction.L12 (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
              (Work.FTS.RegExportIface.RXT.GR α g) p.2.2) z * Work.Construction.c2m θ)
        hC2τ.2.2.2.2 hC2τ.2.1 hkl hzθ
    have hstepC : Work.Spaces.mixed k l (fun z θ =>
          ((2 : ℝ) * Work.FTS.Regularity.pExp α) * Work.Construction.Vop (v2_PhiStar α Φs) z θ
          + ((2 : ℝ) * Work.FTS.Regularity.pExp α)
            * Work.Construction.Vop (v2_PhiPert α E g p.2.2) z θ) p.1 p.2.1
        = Work.Spaces.mixed k l (fun z θ => ((2 : ℝ) * Work.FTS.Regularity.pExp α)
            * Work.Construction.Vop (v2_PhiStar α Φs) z θ) p.1 p.2.1
          + Work.Spaces.mixed k l (fun z θ => ((2 : ℝ) * Work.FTS.Regularity.pExp α)
            * Work.Construction.Vop (v2_PhiPert α E g p.2.2) z θ) p.1 p.2.1 :=
      Work.FTS_RegExport.RXT.Sys.mixed_add_lam
        (f := fun z θ => ((2 : ℝ) * Work.FTS.Regularity.pExp α)
            * Work.Construction.Vop (v2_PhiStar α Φs) z θ)
        (h := fun z θ => ((2 : ℝ) * Work.FTS.Regularity.pExp α)
            * Work.Construction.Vop (v2_PhiPert α E g p.2.2) z θ)
        hC2τ.2.2.1 hC2τ.2.2.2.1 hkl hzθ
    rw [Work.FTS_EllLimOK.mixed_congr_of_eqOn_isOpen Work.FTS.EllipticEst.isOpen_Q0 hsplit
      hzθ k l, hstepA, hstepB, hstepC]
    ring

end Work.FTS_RegExport.RXT0.RXJets
end
end
-- ===== merged: Submission.Work.FTS_RegExport.RXT0.RXJets.coeffbR =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS_RegExport.RXT0.RXJets.coeffbR` — the joint continuity of the jets of `bR`

The `bR` conjunct of `coeffJetsJointCont`.  `bR = 2·𝒰(ΦR_τ)/sin 2θ` with
`ΦR_τ = Φ̃_τ + Θ(F_τ)` and `Φ̃_τ = Φ̃_* + Ξ_τ` on the open quadrant; the `Θ`-part is evaluated in
closed form with `Uop_Theta_div`, which reduces it to the radial combination
`-(3/(2β))·L₁₂(F_τ) + (1/2)·𝔽K(F_τ)`.
-/

noncomputable section

open scoped Real Topology
open Set Filter

namespace Work.FTS_RegExport.RXT0.RXJets

set_option autoImplicit false
set_option maxHeartbeats 3800000

open Work.FTS_RegExport.RXT (v2_PhiT v2_PhiStar v2_PhiPert)

/-- **The `bR` conjunct of `coeffJetsJointCont`.** -/
theorem coeffbR {α C₀ Ce Cs : ℝ} {Φs : Work.FTS.Galerkin.Fn}
    {E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn} {g : Work.FTS.Galerkin.Fam}
    (H : CJHyps α C₀ Ce Cs Φs E g) :
    ∀ S > 0, ∀ k l : ℕ, k + l ≤ 2 →
      ContinuousOn (fun p : ℝ × ℝ × ℝ => Work.Spaces.mixed k l
        (fun z θ => Work.FTS.RegExportIface.RXT.bR α Φs E g z θ p.2.2) p.1 p.2.1)
        (Set.Ioi (0:ℝ) ×ˢ (Set.Ioo (0:ℝ) (Real.pi / 2) ×ˢ Set.Icc (0:ℝ) S)) := by
  have hα := H.hα
  have hα13 := H.hα13
  have hEL3 := H.hEL3
  have hStar := H.hStar
  have hOK := H.hOK
  obtain ⟨hMixedConst, hConstCont, hCdC2m, hCdSinsq, hDthAng, hRadialCont, hRadAngCont⟩ :=
    Work.FTS_RegExport.RXT0.RXJets.jetBasic
  have hStar3 := CJHyps.hStar3 H
  have hStar1 := CJHyps.hStar1 H
  have hPert3 := CJHyps.hPert3 H
  have hPert1g := CJHyps.hPert1g H
  have hagQ := CJHyps.hagQ H
  have hSliceFun := CJHyps.hSliceFun H
  intro S hS k l hkl
  have hk2 : k ≤ 2 := by omega
  have hl2 : l ≤ 2 := by omega
  have hResC3 := CJHyps.hResC3 H S
  have hRegR := CJHyps.hRegR H S
  have hderL12 := CJHyps.hderL12 H S
  have hdzd := CJHyps.hdzd H S hS
  obtain ⟨hStarVop, hStarRop, hStarUdiv⟩ := CJHyps.hStarSlots H S k l hkl
  refine ContinuousOn.congr (f := fun p : ℝ × ℝ × ℝ =>
      Work.Spaces.mixed k l (fun z θ => (2 : ℝ) * (Work.Construction.Uop
          (Work.FTS.Regularity.pExp α) (v2_PhiStar α Φs) z θ / Real.sin (2 * θ))) p.1 p.2.1
      + Work.Spaces.mixed k l (fun z θ => (2 : ℝ) * (Work.Construction.Uop
          (Work.FTS.Regularity.pExp α) (v2_PhiPert α E g p.2.2) z θ
          / Real.sin (2 * θ))) p.1 p.2.1
      + Work.Spaces.mixed k l (fun z θ => (2 : ℝ) * (Work.Construction.Uop
          (Work.FTS.Regularity.pExp α) (Work.Construction.Theta (Work.FTS.Regularity.pExp α)
            (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
              (Work.FTS.RegExportIface.RXT.GR α g) p.2.2)) z θ
          / Real.sin (2 * θ))) p.1 p.2.1) ?_ ?_
  · have hQ0 : ContinuousOn (fun p : ℝ × ℝ × ℝ => Work.Spaces.mixed k l
          (fun z θ => (2 : ℝ) * (Work.Construction.Uop (Work.FTS.Regularity.pExp α)
            (v2_PhiStar α Φs) z θ / Real.sin (2 * θ))) p.1 p.2.1)
          (Work.FTS_RegExport.RXT0.RXJets.slb S) :=
        (hStarUdiv.const_mul 2).congr (fun p hp => by
          rw [Work.FTS_RegExport.RXT.Sys.coeff_mixed_const_mul])
    have hQ1 : ContinuousOn (fun p : ℝ × ℝ × ℝ => Work.Spaces.mixed k l
          (fun z θ => (2 : ℝ) * (Work.Construction.Uop (Work.FTS.Regularity.pExp α)
            (v2_PhiPert α E g p.2.2) z θ / Real.sin (2 * θ))) p.1 p.2.1)
          (Work.FTS_RegExport.RXT0.RXJets.slb S) :=
        ((H.hSlot S hS k l hkl).2.2.const_mul 2).congr (fun p hp => by
          rw [Work.FTS_RegExport.RXT.Sys.coeff_mixed_const_mul])
    have hQ2 : ContinuousOn (fun p : ℝ × ℝ × ℝ => Work.Spaces.mixed k l
          (fun z θ => (2 : ℝ) * (Work.Construction.Uop (Work.FTS.Regularity.pExp α)
            (Work.Construction.Theta (Work.FTS.Regularity.pExp α)
              (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
                (Work.FTS.RegExportIface.RXT.GR α g) p.2.2)) z θ / Real.sin (2 * θ)))
          p.1 p.2.1) (Work.FTS_RegExport.RXT0.RXJets.slb S) := by
      have hsum := (hRadialCont (c := (2 : ℝ) * (-(3 / (4 * Work.FTS.Regularity.pExp α))))
            (a := fun z τ => Work.Construction.L12 (Work.Construction.Ftau
              (Work.FTS.Regularity.pExp α) (Work.FTS.RegExportIface.RXT.GR α g) τ) z)
            (hdzd k hk2).1 hkl).add
          (hRadialCont (c := (2 : ℝ) * (1 / 4))
            (a := fun z τ => Work.Construction.FK (Work.Construction.Ftau
              (Work.FTS.Regularity.pExp α) (Work.FTS.RegExportIface.RXT.GR α g) τ) z)
            (hdzd k hk2).2 hkl)
      refine hsum.congr (fun p hp => ?_)
      obtain ⟨hz, hθ, hθ2, hτ0, hτS⟩ := mem_slb.mp hp
      have hzθ : (p.1, p.2.1) ∈ Work.FTS.EllipticEst.Q0 := ⟨hz, hθ, hθ2⟩
      show Work.Spaces.mixed k l (fun z θ => (2 : ℝ) * (Work.Construction.Uop
            (Work.FTS.Regularity.pExp α) (Work.Construction.Theta (Work.FTS.Regularity.pExp α)
              (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
                (Work.FTS.RegExportIface.RXT.GR α g) p.2.2)) z θ
            / Real.sin (2 * θ))) p.1 p.2.1
        = Work.Spaces.mixed k l (fun z θ => ((2 : ℝ)
              * (-(3 / (4 * Work.FTS.Regularity.pExp α))))
              * Work.Construction.L12 (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
                (Work.FTS.RegExportIface.RXT.GR α g) p.2.2) z) p.1 p.2.1
          + Work.Spaces.mixed k l (fun z θ => ((2 : ℝ) * (1 / 4))
              * Work.Construction.FK (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
                (Work.FTS.RegExportIface.RXT.GR α g) p.2.2) z) p.1 p.2.1
      have hL2s : ContDiffOn ℝ 2 (Function.uncurry (fun z θ => ((2 : ℝ)
            * (-(3 / (4 * Work.FTS.Regularity.pExp α))))
            * Work.Construction.L12 (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
              (Work.FTS.RegExportIface.RXT.GR α g) p.2.2) z)) Work.FTS.EllipticEst.Q0 :=
        (contDiffOn_const (c := (2 : ℝ) * (-(3 / (4 * Work.FTS.Regularity.pExp α))))).mul
          (Work.FTS_RegExport.RXT.contDiffOn_slice_fst (hRegR p.2.2 ⟨hτ0, hτS⟩).1)
      have hF2s : ContDiffOn ℝ 2 (Function.uncurry (fun z θ => ((2 : ℝ) * (1 / 4))
            * Work.Construction.FK (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
              (Work.FTS.RegExportIface.RXT.GR α g) p.2.2) z)) Work.FTS.EllipticEst.Q0 :=
        (contDiffOn_const (c := (2 : ℝ) * (1 / 4))).mul
          (Work.FTS_RegExport.RXT.contDiffOn_slice_fst (hRegR p.2.2 ⟨hτ0, hτS⟩).2)
      have hcl : Set.EqOn (Function.uncurry (fun z θ => (2 : ℝ) * (Work.Construction.Uop
            (Work.FTS.Regularity.pExp α) (Work.Construction.Theta (Work.FTS.Regularity.pExp α)
              (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
                (Work.FTS.RegExportIface.RXT.GR α g) p.2.2)) z θ / Real.sin (2 * θ))))
          (Function.uncurry (fun z θ => ((2 : ℝ)
              * (-(3 / (4 * Work.FTS.Regularity.pExp α))))
              * Work.Construction.L12 (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
                (Work.FTS.RegExportIface.RXT.GR α g) p.2.2) z
            + ((2 : ℝ) * (1 / 4)) * Work.Construction.FK (Work.Construction.Ftau
                (Work.FTS.Regularity.pExp α) (Work.FTS.RegExportIface.RXT.GR α g) p.2.2) z))
          Work.FTS.EllipticEst.Q0 := by
        intro q hq
        obtain ⟨hz', hθ', hθ2'⟩ := Work.FTS.EllipticEst.mem_Q0.mp hq
        simp only [Function.uncurry]
        rw [Work.FTS_RegExport.RXT.Sys.Uop_Theta_div (Work.FTS.Regularity.pExp_pos hα)
          hz' hθ' hθ2' (hderL12 p.2.2 ⟨hτ0, hτS⟩ q.1 hz')]
        ring
      have hstep : Work.Spaces.mixed k l (fun z θ => ((2 : ℝ)
              * (-(3 / (4 * Work.FTS.Regularity.pExp α))))
              * Work.Construction.L12 (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
                (Work.FTS.RegExportIface.RXT.GR α g) p.2.2) z
            + ((2 : ℝ) * (1 / 4)) * Work.Construction.FK (Work.Construction.Ftau
                (Work.FTS.Regularity.pExp α) (Work.FTS.RegExportIface.RXT.GR α g) p.2.2) z)
            p.1 p.2.1
          = Work.Spaces.mixed k l (fun z θ => ((2 : ℝ)
              * (-(3 / (4 * Work.FTS.Regularity.pExp α))))
              * Work.Construction.L12 (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
                (Work.FTS.RegExportIface.RXT.GR α g) p.2.2) z) p.1 p.2.1
            + Work.Spaces.mixed k l (fun z θ => ((2 : ℝ) * (1 / 4))
              * Work.Construction.FK (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
                (Work.FTS.RegExportIface.RXT.GR α g) p.2.2) z) p.1 p.2.1 :=
        Work.FTS_RegExport.RXT.Sys.mixed_add_lam hL2s hF2s hkl hzθ
      rw [Work.FTS_EllLimOK.mixed_congr_of_eqOn_isOpen Work.FTS.EllipticEst.isOpen_Q0 hcl
        hzθ k l, hstep]
    exact (hQ0.add hQ1).add hQ2
  · intro p hp
    show Work.Spaces.mixed k l (fun z θ =>
          Work.FTS.RegExportIface.RXT.bR α Φs E g z θ p.2.2) p.1 p.2.1
        = Work.Spaces.mixed k l (fun z θ => (2 : ℝ) * (Work.Construction.Uop
            (Work.FTS.Regularity.pExp α) (v2_PhiStar α Φs) z θ / Real.sin (2 * θ))) p.1 p.2.1
          + Work.Spaces.mixed k l (fun z θ => (2 : ℝ) * (Work.Construction.Uop
              (Work.FTS.Regularity.pExp α) (v2_PhiPert α E g p.2.2) z θ
              / Real.sin (2 * θ))) p.1 p.2.1
          + Work.Spaces.mixed k l (fun z θ => (2 : ℝ) * (Work.Construction.Uop
              (Work.FTS.Regularity.pExp α) (Work.Construction.Theta (Work.FTS.Regularity.pExp α)
                (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
                  (Work.FTS.RegExportIface.RXT.GR α g) p.2.2)) z θ
              / Real.sin (2 * θ))) p.1 p.2.1
    obtain ⟨hz, hθ, hθ2, hτ0, hτS⟩ := mem_slb.mp hp
    have hzθ : (p.1, p.2.1) ∈ Work.FTS.EllipticEst.Q0 := ⟨hz, hθ, hθ2⟩
    have hag := hagQ p.2.2 hτ0
    have hP1 := hPert1g p.2.2 hτ0
    have hV2C1 : ContDiffOn ℝ 1 (Function.uncurry (v2_PhiT α Φs E g p.2.2))
        Work.FTS.EllipticEst.Q0 := (hResC3 p.2.2 ⟨hτ0, hτS⟩).1.of_le (by norm_num)
    have hThC1 : ContDiffOn ℝ 1 (Function.uncurry (Work.Construction.Theta
        (Work.FTS.Regularity.pExp α) (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
          (Work.FTS.RegExportIface.RXT.GR α g) p.2.2))) Work.FTS.EllipticEst.Q0 :=
      (hResC3 p.2.2 ⟨hτ0, hτS⟩).2.of_le (by norm_num)
    have hQ2c : ContDiffOn ℝ 2 (Function.uncurry (fun z θ => (2 : ℝ)
          * (Work.Construction.Uop (Work.FTS.Regularity.pExp α) (Work.Construction.Theta
              (Work.FTS.Regularity.pExp α) (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
                (Work.FTS.RegExportIface.RXT.GR α g) p.2.2)) z θ / Real.sin (2 * θ))))
        Work.FTS.EllipticEst.Q0 :=
      (contDiffOn_const (c := (2 : ℝ))).mul
        (Work.FTS_RegExport.RXT.contDiffOn_uncurry_div_sin_two
          (Work.FTS_RegExport.RXT.contDiffOn_uncurry_Uop (hResC3 p.2.2 ⟨hτ0, hτS⟩).2))
    have hsplit : Set.EqOn (Function.uncurry (fun z θ =>
          Work.FTS.RegExportIface.RXT.bR α Φs E g z θ p.2.2))
        (Function.uncurry (fun z θ => ((2 : ℝ) * (Work.Construction.Uop
              (Work.FTS.Regularity.pExp α) (v2_PhiStar α Φs) z θ / Real.sin (2 * θ))
            + (2 : ℝ) * (Work.Construction.Uop (Work.FTS.Regularity.pExp α)
                (v2_PhiPert α E g p.2.2) z θ / Real.sin (2 * θ)))
          + (2 : ℝ) * (Work.Construction.Uop (Work.FTS.Regularity.pExp α)
              (Work.Construction.Theta (Work.FTS.Regularity.pExp α)
                (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
                  (Work.FTS.RegExportIface.RXT.GR α g) p.2.2)) z θ / Real.sin (2 * θ))))
        Work.FTS.EllipticEst.Q0 := by
      intro q hq
      obtain ⟨hz', hθ', hθ2'⟩ := Work.FTS.EllipticEst.mem_Q0.mp hq
      simp only [Function.uncurry]
      have hUc := Work.FTS_RegExport.RXR5.Uop_congr_of_agreeOnQ
        (α := Work.FTS.Regularity.pExp α) hag hz' hθ' hθ2'
      have hSplit1 : Work.Construction.Uop (Work.FTS.Regularity.pExp α)
            (fun z θ => v2_PhiT α Φs E g p.2.2 z θ + Work.Construction.Theta
              (Work.FTS.Regularity.pExp α) (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
                (Work.FTS.RegExportIface.RXT.GR α g) p.2.2) z θ) q.1 q.2
            / Real.sin (2 * q.2)
          = Work.Construction.Uop (Work.FTS.Regularity.pExp α) (v2_PhiT α Φs E g p.2.2) q.1 q.2
              / Real.sin (2 * q.2)
            + Work.Construction.Uop (Work.FTS.Regularity.pExp α) (Work.Construction.Theta
                (Work.FTS.Regularity.pExp α) (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
                  (Work.FTS.RegExportIface.RXT.GR α g) p.2.2)) q.1 q.2
              / Real.sin (2 * q.2) :=
        Work.FTS_RegExport.RXT.v2_uop_div_add_at hV2C1 hThC1 ⟨hz', hθ', hθ2'⟩
      have hUa : Work.Construction.Uop (Work.FTS.Regularity.pExp α)
            (v2_PhiStar α Φs + v2_PhiPert α E g p.2.2) q.1 q.2 / Real.sin (2 * q.2)
          = Work.Construction.Uop (Work.FTS.Regularity.pExp α) (v2_PhiStar α Φs) q.1 q.2
              / Real.sin (2 * q.2)
            + Work.Construction.Uop (Work.FTS.Regularity.pExp α) (v2_PhiPert α E g p.2.2)
                q.1 q.2 / Real.sin (2 * q.2) :=
        Work.FTS_RegExport.RXT.v2_uop_div_add_at hStar1 hP1 ⟨hz', hθ', hθ2'⟩
      rw [show Work.FTS.RegExportIface.RXT.bR α Φs E g q.1 q.2 p.2.2
          = (2 * Work.Construction.Uop (Work.FTS.Regularity.pExp α)
              (Work.FTS.Galerkin.slice (Work.FTS.RegExportIface.RXT.ΦR α Φs E g) p.2.2)
              q.1 q.2) / Real.sin (2 * q.2) from rfl]
      rw [mul_div_assoc]
      rw [hSliceFun p.2.2, hSplit1, hUc, hUa]
      ring
    have hQ0c : ContDiffOn ℝ 2 (Function.uncurry (fun z θ => (2 : ℝ)
          * (Work.Construction.Uop (Work.FTS.Regularity.pExp α) (v2_PhiStar α Φs) z θ
            / Real.sin (2 * θ)))) Work.FTS.EllipticEst.Q0 :=
      (contDiffOn_const (c := (2 : ℝ))).mul
        (Work.FTS_RegExport.RXT.contDiffOn_uncurry_div_sin_two
          (Work.FTS_RegExport.RXT.contDiffOn_uncurry_Uop hStar3))
    have hQ1c : ContDiffOn ℝ 2 (Function.uncurry (fun z θ => (2 : ℝ)
          * (Work.Construction.Uop (Work.FTS.Regularity.pExp α) (v2_PhiPert α E g p.2.2) z θ
            / Real.sin (2 * θ)))) Work.FTS.EllipticEst.Q0 :=
      (contDiffOn_const (c := (2 : ℝ))).mul
        (Work.FTS_RegExport.RXT.contDiffOn_uncurry_div_sin_two
          (Work.FTS_RegExport.RXT.contDiffOn_uncurry_Uop (hPert3 p.2.2 hτ0)))
    have hstepA : Work.Spaces.mixed k l (fun z θ =>
          ((2 : ℝ) * (Work.Construction.Uop (Work.FTS.Regularity.pExp α) (v2_PhiStar α Φs) z θ
              / Real.sin (2 * θ))
            + (2 : ℝ) * (Work.Construction.Uop (Work.FTS.Regularity.pExp α)
                (v2_PhiPert α E g p.2.2) z θ / Real.sin (2 * θ)))
          + (2 : ℝ) * (Work.Construction.Uop (Work.FTS.Regularity.pExp α)
              (Work.Construction.Theta (Work.FTS.Regularity.pExp α)
                (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
                  (Work.FTS.RegExportIface.RXT.GR α g) p.2.2)) z θ / Real.sin (2 * θ)))
          p.1 p.2.1
        = Work.Spaces.mixed k l (fun z θ =>
            (2 : ℝ) * (Work.Construction.Uop (Work.FTS.Regularity.pExp α) (v2_PhiStar α Φs) z θ
              / Real.sin (2 * θ))
            + (2 : ℝ) * (Work.Construction.Uop (Work.FTS.Regularity.pExp α)
                (v2_PhiPert α E g p.2.2) z θ / Real.sin (2 * θ))) p.1 p.2.1
          + Work.Spaces.mixed k l (fun z θ => (2 : ℝ) * (Work.Construction.Uop
              (Work.FTS.Regularity.pExp α) (Work.Construction.Theta (Work.FTS.Regularity.pExp α)
                (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
                  (Work.FTS.RegExportIface.RXT.GR α g) p.2.2)) z θ / Real.sin (2 * θ)))
            p.1 p.2.1 :=
      Work.FTS_RegExport.RXT.Sys.mixed_add_lam
        (f := fun z θ =>
            (2 : ℝ) * (Work.Construction.Uop (Work.FTS.Regularity.pExp α) (v2_PhiStar α Φs) z θ
              / Real.sin (2 * θ))
            + (2 : ℝ) * (Work.Construction.Uop (Work.FTS.Regularity.pExp α)
                (v2_PhiPert α E g p.2.2) z θ / Real.sin (2 * θ)))
        (h := fun z θ => (2 : ℝ) * (Work.Construction.Uop (Work.FTS.Regularity.pExp α)
            (Work.Construction.Theta (Work.FTS.Regularity.pExp α)
              (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
                (Work.FTS.RegExportIface.RXT.GR α g) p.2.2)) z θ / Real.sin (2 * θ)))
        (hQ0c.add hQ1c) hQ2c hkl hzθ
    have hstepB : Work.Spaces.mixed k l (fun z θ =>
            (2 : ℝ) * (Work.Construction.Uop (Work.FTS.Regularity.pExp α) (v2_PhiStar α Φs) z θ
              / Real.sin (2 * θ))
            + (2 : ℝ) * (Work.Construction.Uop (Work.FTS.Regularity.pExp α)
                (v2_PhiPert α E g p.2.2) z θ / Real.sin (2 * θ))) p.1 p.2.1
        = Work.Spaces.mixed k l (fun z θ => (2 : ℝ) * (Work.Construction.Uop
            (Work.FTS.Regularity.pExp α) (v2_PhiStar α Φs) z θ / Real.sin (2 * θ))) p.1 p.2.1
          + Work.Spaces.mixed k l (fun z θ => (2 : ℝ) * (Work.Construction.Uop
              (Work.FTS.Regularity.pExp α) (v2_PhiPert α E g p.2.2) z θ
              / Real.sin (2 * θ))) p.1 p.2.1 :=
      Work.FTS_RegExport.RXT.Sys.mixed_add_lam
        (f := fun z θ => (2 : ℝ) * (Work.Construction.Uop (Work.FTS.Regularity.pExp α)
            (v2_PhiStar α Φs) z θ / Real.sin (2 * θ)))
        (h := fun z θ => (2 : ℝ) * (Work.Construction.Uop (Work.FTS.Regularity.pExp α)
            (v2_PhiPert α E g p.2.2) z θ / Real.sin (2 * θ)))
        hQ0c hQ1c hkl hzθ
    rw [Work.FTS_EllLimOK.mixed_congr_of_eqOn_isOpen Work.FTS.EllipticEst.isOpen_Q0 hsplit
      hzθ k l, hstepA, hstepB]

end Work.FTS_RegExport.RXT0.RXJets
end
end
-- ===== merged: Submission.Work.FTS_RegExport.RXT0.RXJets.coeffcR =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS_RegExport.RXT0.RXJets.coeffcR` — the joint continuity of the jets of `cR`

The `cR` conjunct of `coeffJetsJointCont`.  `cs7 = (1+μ) - L₁₂(F_τ)/β + sin²θ·𝔽K(F_τ) - 2ℛ(Φ̃_τ)`
with `Φ̃_τ = Φ̃_* + Ξ_τ` on the open quadrant; the sum of the first three pieces, the two radial
pieces and the two `ℛ`-slots are handled separately.
-/

noncomputable section

open scoped Real Topology
open Set Filter

namespace Work.FTS_RegExport.RXT0.RXJets

set_option autoImplicit false
set_option maxHeartbeats 3800000

open Work.FTS_RegExport.RXT (v2_PhiT v2_PhiStar v2_PhiPert)

/-- **The `cR` conjunct of `coeffJetsJointCont`.** -/
theorem coeffcR {α C₀ Ce Cs : ℝ} {Φs : Work.FTS.Galerkin.Fn}
    {E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn} {g : Work.FTS.Galerkin.Fam}
    (H : CJHyps α C₀ Ce Cs Φs E g) :
    ∀ S > 0, ∀ k l : ℕ, k + l ≤ 2 →
      ContinuousOn (fun p : ℝ × ℝ × ℝ => Work.Spaces.mixed k l
        (fun z θ => Work.FTS.RegExportIface.RXT.cR α Φs E g z θ p.2.2) p.1 p.2.1)
        (Set.Ioi (0:ℝ) ×ˢ (Set.Ioo (0:ℝ) (Real.pi / 2) ×ˢ Set.Icc (0:ℝ) S)) := by
  have hα := H.hα
  have hα13 := H.hα13
  have hEL3 := H.hEL3
  have hStar := H.hStar
  have hOK := H.hOK
  have hμRc := CJHyps.hμRc H
  obtain ⟨hMixedConst, hConstCont, hCdC2m, hCdSinsq, hDthAng, hRadialCont, hRadAngCont⟩ :=
    Work.FTS_RegExport.RXT0.RXJets.jetBasic
  have hStar3 := CJHyps.hStar3 H
  have hStar1 := CJHyps.hStar1 H
  have hPert3 := CJHyps.hPert3 H
  have hPert1g := CJHyps.hPert1g H
  have hagQ := CJHyps.hagQ H
  intro S hS k l hkl
  have hk2 : k ≤ 2 := by omega
  have hl2 : l ≤ 2 := by omega
  have hRegR := CJHyps.hRegR H S
  have hdzd := CJHyps.hdzd H S hS
  obtain ⟨hStarVop, hStarRop, hStarUdiv⟩ := CJHyps.hStarSlots H S k l hkl
  refine ContinuousOn.congr (f := fun p : ℝ × ℝ × ℝ =>
      Work.Spaces.mixed k l (fun _ _ : ℝ => (1 : ℝ)
          + Work.FTS.RegExportIface.RXT.μR α Φs E g p.2.2) p.1 p.2.1
      + Work.Spaces.mixed k l (fun z θ => (-(1 / Work.FTS.Regularity.pExp α))
          * Work.Construction.L12 (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
            (Work.FTS.RegExportIface.RXT.GR α g) p.2.2) z) p.1 p.2.1
      + Work.Spaces.mixed k l (fun z θ => Work.Construction.FK (Work.Construction.Ftau
            (Work.FTS.Regularity.pExp α) (Work.FTS.RegExportIface.RXT.GR α g) p.2.2) z
          * Real.sin θ ^ 2) p.1 p.2.1
      + Work.Spaces.mixed k l (fun z θ => (-2 : ℝ) * Work.Construction.Rop
          (Work.FTS.Regularity.pExp α) (v2_PhiStar α Φs) z θ) p.1 p.2.1
      + Work.Spaces.mixed k l (fun z θ => (-2 : ℝ) * Work.Construction.Rop
          (Work.FTS.Regularity.pExp α) (v2_PhiPert α E g p.2.2) z θ) p.1 p.2.1) ?_ ?_
  · have hP0 : ContinuousOn (fun p : ℝ × ℝ × ℝ => Work.Spaces.mixed k l
          (fun _ _ : ℝ => (1 : ℝ) + Work.FTS.RegExportIface.RXT.μR α Φs E g p.2.2)
          p.1 p.2.1) (Work.FTS_RegExport.RXT0.RXJets.slb S) :=
        hConstCont (c := fun τ : ℝ => (1 : ℝ) + Work.FTS.RegExportIface.RXT.μR α Φs E g τ)
          ((continuousOn_const (c := (1 : ℝ))).add (hμRc S)) k l
    have hP1 : ContinuousOn (fun p : ℝ × ℝ × ℝ => Work.Spaces.mixed k l
          (fun z θ => (-(1 / Work.FTS.Regularity.pExp α)) * Work.Construction.L12
            (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
              (Work.FTS.RegExportIface.RXT.GR α g) p.2.2) z) p.1 p.2.1)
          (Work.FTS_RegExport.RXT0.RXJets.slb S) :=
        hRadialCont (c := -(1 / Work.FTS.Regularity.pExp α))
          (a := fun z τ => Work.Construction.L12 (Work.Construction.Ftau
            (Work.FTS.Regularity.pExp α) (Work.FTS.RegExportIface.RXT.GR α g) τ) z)
          (hdzd k hk2).1 hkl
    have hP2 : ContinuousOn (fun p : ℝ × ℝ × ℝ => Work.Spaces.mixed k l
          (fun z θ => Work.Construction.FK (Work.Construction.Ftau
            (Work.FTS.Regularity.pExp α) (Work.FTS.RegExportIface.RXT.GR α g) p.2.2) z
            * Real.sin θ ^ 2) p.1 p.2.1) (Work.FTS_RegExport.RXT0.RXJets.slb S) :=
        hRadAngCont (a := fun z τ => Work.Construction.FK (Work.Construction.Ftau
            (Work.FTS.Regularity.pExp α) (Work.FTS.RegExportIface.RXT.GR α g) τ) z)
          (b := fun θ => Real.sin θ ^ 2) (hdzd k hk2).2 (hDthAng hCdSinsq l hl2)
    have hP3 : ContinuousOn (fun p : ℝ × ℝ × ℝ => Work.Spaces.mixed k l
          (fun z θ => (-2 : ℝ) * Work.Construction.Rop (Work.FTS.Regularity.pExp α)
            (v2_PhiStar α Φs) z θ) p.1 p.2.1) (Work.FTS_RegExport.RXT0.RXJets.slb S) :=
        (hStarRop.const_mul (-2)).congr (fun p hp => by
          rw [Work.FTS_RegExport.RXT.Sys.coeff_mixed_const_mul])
    have hP4 : ContinuousOn (fun p : ℝ × ℝ × ℝ => Work.Spaces.mixed k l
          (fun z θ => (-2 : ℝ) * Work.Construction.Rop (Work.FTS.Regularity.pExp α)
            (v2_PhiPert α E g p.2.2) z θ) p.1 p.2.1)
          (Work.FTS_RegExport.RXT0.RXJets.slb S) :=
        ((H.hSlot S hS k l hkl).2.1.const_mul (-2)).congr (fun p hp => by
          rw [Work.FTS_RegExport.RXT.Sys.coeff_mixed_const_mul])
    exact (((hP0.add hP1).add hP2).add hP3).add hP4
  · intro p hp
    show Work.Spaces.mixed k l (fun z θ => Work.FTS.RegExportIface.RXT.cR α Φs E g z θ p.2.2)
          p.1 p.2.1
        = Work.Spaces.mixed k l (fun _ _ : ℝ => (1 : ℝ)
            + Work.FTS.RegExportIface.RXT.μR α Φs E g p.2.2) p.1 p.2.1
          + Work.Spaces.mixed k l (fun z θ => (-(1 / Work.FTS.Regularity.pExp α))
              * Work.Construction.L12 (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
                (Work.FTS.RegExportIface.RXT.GR α g) p.2.2) z) p.1 p.2.1
          + Work.Spaces.mixed k l (fun z θ => Work.Construction.FK (Work.Construction.Ftau
              (Work.FTS.Regularity.pExp α) (Work.FTS.RegExportIface.RXT.GR α g) p.2.2) z
              * Real.sin θ ^ 2) p.1 p.2.1
          + Work.Spaces.mixed k l (fun z θ => (-2 : ℝ) * Work.Construction.Rop
              (Work.FTS.Regularity.pExp α) (v2_PhiStar α Φs) z θ) p.1 p.2.1
          + Work.Spaces.mixed k l (fun z θ => (-2 : ℝ) * Work.Construction.Rop
              (Work.FTS.Regularity.pExp α) (v2_PhiPert α E g p.2.2) z θ) p.1 p.2.1
    obtain ⟨hz, hθ, hθ2, hτ0, hτS⟩ := mem_slb.mp hp
    have hzθ : (p.1, p.2.1) ∈ Work.FTS.EllipticEst.Q0 := ⟨hz, hθ, hθ2⟩
    have hP1b := hPert1g p.2.2 hτ0
    have hP0b : ContDiffOn ℝ 2 (Function.uncurry (fun _ _ : ℝ => (1 : ℝ)
          + Work.FTS.RegExportIface.RXT.μR α Φs E g p.2.2)) Work.FTS.EllipticEst.Q0 :=
      contDiffOn_const
    have hP1c : ContDiffOn ℝ 2 (Function.uncurry (fun z θ => (-(1 / Work.FTS.Regularity.pExp α))
          * Work.Construction.L12 (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
            (Work.FTS.RegExportIface.RXT.GR α g) p.2.2) z)) Work.FTS.EllipticEst.Q0 :=
      (contDiffOn_const (c := -(1 / Work.FTS.Regularity.pExp α))).mul
        (Work.FTS_RegExport.RXT.contDiffOn_slice_fst (hRegR p.2.2 ⟨hτ0, hτS⟩).1)
    have hP2c : ContDiffOn ℝ 2 (Function.uncurry (fun z θ => Work.Construction.FK
          (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
            (Work.FTS.RegExportIface.RXT.GR α g) p.2.2) z * Real.sin θ ^ 2))
        Work.FTS.EllipticEst.Q0 :=
      (Work.FTS_RegExport.RXT.contDiffOn_slice_fst (hRegR p.2.2 ⟨hτ0, hτS⟩).2).mul
        ((hCdSinsq.comp contDiffOn_snd (fun q hq => hq.2)).congr (fun q _ => rfl))
    have hP3b : ContDiffOn ℝ 2 (Function.uncurry (fun z θ => (-2 : ℝ)
          * Work.Construction.Rop (Work.FTS.Regularity.pExp α) (v2_PhiStar α Φs) z θ))
        Work.FTS.EllipticEst.Q0 :=
      (contDiffOn_const (c := (-2 : ℝ))).mul
        (Work.FTS_RegExport.RXT.contDiffOn_uncurry_Rop hStar3)
    have hP4b : ContDiffOn ℝ 2 (Function.uncurry (fun z θ => (-2 : ℝ)
          * Work.Construction.Rop (Work.FTS.Regularity.pExp α) (v2_PhiPert α E g p.2.2) z θ))
        Work.FTS.EllipticEst.Q0 :=
      (contDiffOn_const (c := (-2 : ℝ))).mul
        (Work.FTS_RegExport.RXT.contDiffOn_uncurry_Rop (hPert3 p.2.2 hτ0))
    have hsplit : Set.EqOn (Function.uncurry (fun z θ =>
          Work.FTS.RegExportIface.RXT.cR α Φs E g z θ p.2.2))
        (Function.uncurry (fun z θ => (((1 : ℝ)
            + Work.FTS.RegExportIface.RXT.μR α Φs E g p.2.2)
          + (-(1 / Work.FTS.Regularity.pExp α)) * Work.Construction.L12
              (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
                (Work.FTS.RegExportIface.RXT.GR α g) p.2.2) z)
          + Work.Construction.FK (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
              (Work.FTS.RegExportIface.RXT.GR α g) p.2.2) z * Real.sin θ ^ 2
          + ((-2 : ℝ) * Work.Construction.Rop (Work.FTS.Regularity.pExp α)
              (v2_PhiStar α Φs) z θ
            + (-2 : ℝ) * Work.Construction.Rop (Work.FTS.Regularity.pExp α)
                (v2_PhiPert α E g p.2.2) z θ))) Work.FTS.EllipticEst.Q0 := by
      intro q hq
      obtain ⟨hz', hθ', hθ2'⟩ := Work.FTS.EllipticEst.mem_Q0.mp hq
      simp only [Function.uncurry]
      have hRcT : Work.Construction.Rop (Work.FTS.Regularity.pExp α)
            (v2_PhiT α Φs E g p.2.2) q.1 q.2
          = Work.Construction.Rop (Work.FTS.Regularity.pExp α)
              (v2_PhiStar α Φs + v2_PhiPert α E g p.2.2) q.1 q.2 :=
        Work.FTS_RegExport.RXR5.Rop_congr_of_agreeOnQ (α := Work.FTS.Regularity.pExp α)
          (hagQ p.2.2 hτ0) hz' hθ' hθ2'
      have hRcB : Work.Construction.Rop (Work.FTS.Regularity.pExp α)
            (v2_PhiStar α Φs + v2_PhiPert α E g p.2.2) q.1 q.2
          = Work.Construction.Rop (Work.FTS.Regularity.pExp α) (v2_PhiStar α Φs) q.1 q.2
            + Work.Construction.Rop (Work.FTS.Regularity.pExp α)
                (v2_PhiPert α E g p.2.2) q.1 q.2 :=
        Work.FTS_RegExport.RXT.v2_rop_add_at (αG := Work.FTS.Regularity.pExp α)
          hStar1 hP1b ⟨hz', hθ', hθ2'⟩
      rw [show Work.FTS.RegExportIface.RXT.cR α Φs E g q.1 q.2 p.2.2
          = (1 + Work.FTS.RegExportIface.RXT.μR α Φs E g p.2.2)
            - Work.Construction.L12 (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
                (Work.FTS.RegExportIface.RXT.GR α g) p.2.2) q.1 / Work.FTS.Regularity.pExp α
            + Real.sin q.2 ^ 2 * Work.Construction.FK (Work.Construction.Ftau
                (Work.FTS.Regularity.pExp α) (Work.FTS.RegExportIface.RXT.GR α g) p.2.2) q.1
            - 2 * Work.Construction.Rop (Work.FTS.Regularity.pExp α)
                (v2_PhiT α Φs E g p.2.2) q.1 q.2 from rfl]
      rw [hRcT, hRcB]
      ring
    have hstepA : Work.Spaces.mixed k l (fun z θ => (((1 : ℝ)
            + Work.FTS.RegExportIface.RXT.μR α Φs E g p.2.2)
          + (-(1 / Work.FTS.Regularity.pExp α)) * Work.Construction.L12
              (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
                (Work.FTS.RegExportIface.RXT.GR α g) p.2.2) z)
          + Work.Construction.FK (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
              (Work.FTS.RegExportIface.RXT.GR α g) p.2.2) z * Real.sin θ ^ 2
          + ((-2 : ℝ) * Work.Construction.Rop (Work.FTS.Regularity.pExp α)
              (v2_PhiStar α Φs) z θ
            + (-2 : ℝ) * Work.Construction.Rop (Work.FTS.Regularity.pExp α)
                (v2_PhiPert α E g p.2.2) z θ)) p.1 p.2.1
        = Work.Spaces.mixed k l (fun z θ => ((1 : ℝ)
              + Work.FTS.RegExportIface.RXT.μR α Φs E g p.2.2)
            + (-(1 / Work.FTS.Regularity.pExp α)) * Work.Construction.L12
                (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
                  (Work.FTS.RegExportIface.RXT.GR α g) p.2.2) z
            + Work.Construction.FK (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
                (Work.FTS.RegExportIface.RXT.GR α g) p.2.2) z * Real.sin θ ^ 2)
            p.1 p.2.1
          + Work.Spaces.mixed k l (fun z θ => (-2 : ℝ) * Work.Construction.Rop
              (Work.FTS.Regularity.pExp α) (v2_PhiStar α Φs) z θ
              + (-2 : ℝ) * Work.Construction.Rop (Work.FTS.Regularity.pExp α)
                  (v2_PhiPert α E g p.2.2) z θ) p.1 p.2.1 :=
      Work.FTS_RegExport.RXT.Sys.mixed_add_lam
        (f := fun z θ => ((1 : ℝ)
              + Work.FTS.RegExportIface.RXT.μR α Φs E g p.2.2)
            + (-(1 / Work.FTS.Regularity.pExp α)) * Work.Construction.L12
                (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
                  (Work.FTS.RegExportIface.RXT.GR α g) p.2.2) z
            + Work.Construction.FK (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
                (Work.FTS.RegExportIface.RXT.GR α g) p.2.2) z * Real.sin θ ^ 2)
        (h := fun z θ => (-2 : ℝ) * Work.Construction.Rop (Work.FTS.Regularity.pExp α)
              (v2_PhiStar α Φs) z θ
            + (-2 : ℝ) * Work.Construction.Rop (Work.FTS.Regularity.pExp α)
                (v2_PhiPert α E g p.2.2) z θ)
        ((hP0b.add hP1c).add hP2c) (hP3b.add hP4b) hkl hzθ
    have hstepB : Work.Spaces.mixed k l (fun z θ => ((1 : ℝ)
              + Work.FTS.RegExportIface.RXT.μR α Φs E g p.2.2)
            + (-(1 / Work.FTS.Regularity.pExp α)) * Work.Construction.L12
                (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
                  (Work.FTS.RegExportIface.RXT.GR α g) p.2.2) z
            + Work.Construction.FK (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
                (Work.FTS.RegExportIface.RXT.GR α g) p.2.2) z * Real.sin θ ^ 2)
            p.1 p.2.1
        = Work.Spaces.mixed k l (fun z θ => ((1 : ℝ)
              + Work.FTS.RegExportIface.RXT.μR α Φs E g p.2.2)
            + (-(1 / Work.FTS.Regularity.pExp α)) * Work.Construction.L12
                (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
                  (Work.FTS.RegExportIface.RXT.GR α g) p.2.2) z) p.1 p.2.1
          + Work.Spaces.mixed k l (fun z θ => Work.Construction.FK
              (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
                (Work.FTS.RegExportIface.RXT.GR α g) p.2.2) z * Real.sin θ ^ 2)
              p.1 p.2.1 :=
      Work.FTS_RegExport.RXT.Sys.mixed_add_lam
        (f := fun z θ => ((1 : ℝ)
              + Work.FTS.RegExportIface.RXT.μR α Φs E g p.2.2)
            + (-(1 / Work.FTS.Regularity.pExp α)) * Work.Construction.L12
                (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
                  (Work.FTS.RegExportIface.RXT.GR α g) p.2.2) z)
        (h := fun z θ => Work.Construction.FK (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
              (Work.FTS.RegExportIface.RXT.GR α g) p.2.2) z * Real.sin θ ^ 2)
        (hP0b.add hP1c) hP2c hkl hzθ
    have hstepC : Work.Spaces.mixed k l (fun z θ => ((1 : ℝ)
            + Work.FTS.RegExportIface.RXT.μR α Φs E g p.2.2)
          + (-(1 / Work.FTS.Regularity.pExp α)) * Work.Construction.L12
              (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
                (Work.FTS.RegExportIface.RXT.GR α g) p.2.2) z) p.1 p.2.1
        = Work.Spaces.mixed k l (fun _ _ : ℝ => (1 : ℝ)
              + Work.FTS.RegExportIface.RXT.μR α Φs E g p.2.2) p.1 p.2.1
          + Work.Spaces.mixed k l (fun z θ => (-(1 / Work.FTS.Regularity.pExp α))
              * Work.Construction.L12 (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
                (Work.FTS.RegExportIface.RXT.GR α g) p.2.2) z) p.1 p.2.1 :=
      Work.FTS_RegExport.RXT.Sys.mixed_add_lam
        (f := fun _ _ : ℝ => (1 : ℝ) + Work.FTS.RegExportIface.RXT.μR α Φs E g p.2.2)
        (h := fun z θ => (-(1 / Work.FTS.Regularity.pExp α)) * Work.Construction.L12
              (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
                (Work.FTS.RegExportIface.RXT.GR α g) p.2.2) z)
        hP0b hP1c hkl hzθ
    have hstepD : Work.Spaces.mixed k l (fun z θ => (-2 : ℝ) * Work.Construction.Rop
            (Work.FTS.Regularity.pExp α) (v2_PhiStar α Φs) z θ
          + (-2 : ℝ) * Work.Construction.Rop (Work.FTS.Regularity.pExp α)
              (v2_PhiPert α E g p.2.2) z θ) p.1 p.2.1
        = Work.Spaces.mixed k l (fun z θ => (-2 : ℝ) * Work.Construction.Rop
            (Work.FTS.Regularity.pExp α) (v2_PhiStar α Φs) z θ) p.1 p.2.1
          + Work.Spaces.mixed k l (fun z θ => (-2 : ℝ) * Work.Construction.Rop
              (Work.FTS.Regularity.pExp α) (v2_PhiPert α E g p.2.2) z θ) p.1 p.2.1 :=
      Work.FTS_RegExport.RXT.Sys.mixed_add_lam
        (f := fun z θ => (-2 : ℝ) * Work.Construction.Rop (Work.FTS.Regularity.pExp α)
            (v2_PhiStar α Φs) z θ)
        (h := fun z θ => (-2 : ℝ) * Work.Construction.Rop (Work.FTS.Regularity.pExp α)
            (v2_PhiPert α E g p.2.2) z θ)
        hP3b hP4b hkl hzθ
    rw [Work.FTS_EllLimOK.mixed_congr_of_eqOn_isOpen Work.FTS.EllipticEst.isOpen_Q0 hsplit
      hzθ k l, hstepA, hstepB, hstepC, hstepD]
    ring

end Work.FTS_RegExport.RXT0.RXJets
end
end
