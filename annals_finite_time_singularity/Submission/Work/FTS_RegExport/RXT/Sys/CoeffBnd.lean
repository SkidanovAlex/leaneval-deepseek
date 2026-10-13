import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Real.Pi.Bounds
import Submission.Work.FTS.RegExportIface.RXT.Leaves
import Submission.Work.FTS_RegExport.RXT.velVanish2
import Submission.Work.FTS_RegExport.RXT.Sys.CoeffCore
import Submission.Work.FTS_RegExport.RXT.Sys.CoeffSmooth
import Submission.Work.FTS_RegExport.RXT.Sys.CoeffBounds
import Submission.Work.FTS_RegExport.RXT.Sys.explicit_pieces_coeff
import Submission.Work.FTS_RegExport.RXT.Sys.pth_vop_slot_bd
import Submission.Work.FTS_RegExport.RXT.Sys.L12FK_family_jets

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
