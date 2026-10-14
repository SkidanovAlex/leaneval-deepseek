import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.RegExportIface.RXT.Leaves
import Submission.Work.FTS_RegExport.RXT.Sys.L12FK_family_jets
import Submission.Work.FTS_RegExport.RXT.coeff_C2
import Submission.Work.FTS_RegExport.RXT0.RXJets.coeffcR
import Submission.Work.FTS_RegExport.RXT0.SJC.slotJetLipschitzApprox
import Submission.Work.R1G.DecayInZ_gA

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS_RegExport.RXT.Sys.CoeffCont` — the `cont` half of `CoeffJets`

The `τ`-continuity of the three coefficient slices at a fixed point of the open quadrant.
Every coefficient is written as an explicit sum of pieces, each of which is `τ`-continuous:

* `μ` (`maxMu (pExp α) (PsiCan Φs E g) g`) under the clock hypothesis;
* `L₁₂(F_τ) z`, `𝔽K(F_τ) z` from the `τ`-Lipschitz bounds of `Sys.L12FK_family_jets`;
* the `D_z`-slots `Vop`, `Rop` and `Uop/sin 2θ` of the residual from
  `Sys.slot_tau_cont_alpha`;
* the `Θ`-part of `Uop`, in closed form via `SysAux.Theta_ops`.
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

/-- **The `cont` clause of `CoeffJets`.** -/
theorem coeff_cont {g : Fam}
    (hα : 0 < α) (hα13 : α ≤ 1 / 3)
    (hEll : ∀ u : Fn, Work.FTS.ClassC.ClassC (pExp α) u →
      Work.FTS.Final.EllPkgGo (pExp α) Ce u (E u) ∧
        Work.FTS.ClassC.EllPkgK (pExp α) 6 Ce u (E u))
    (hEL3 : Work.FTS.FinalV2.EllLimOK3 (pExp α) E)
    (hStar : Work.FTS.Final.StarPkgo2 (pExp α) Cs Φs)
    (hSol : Work.FTS.FinalV2.Sol (pExp α) Φs E g)
    (hOK : Work.FTS.FinalV2.DynOK' (pExp α) C₀ Φs E g)
    (hμ : Work.FTS.RegExportIface.ClockBd α Φs E g) :
    ∀ S > 0, ∀ z θ, 0 < z → 0 < θ → θ < π / 2 →
      ContinuousOn (fun τ => (Vz7 (pExp α) (μR α Φs E g) (GR α g) (ΦR α Φs E g) z θ τ,
        Vθ7 (pExp α) (ΦR α Φs E g) z θ τ / Real.sin (2 * θ),
        cs7 (pExp α) (μR α Φs E g) (GR α g) (ΦR α Φs E g) z θ τ)) (Set.Icc 0 S) := by
  intro S hS z θ hz hθ hθ2
  have hαG : (0 : ℝ) < pExp α := Work.FTS.Regularity.pExp_pos hα
  have hS0 : (0 : ℝ) < max S 1 := lt_max_of_lt_right zero_lt_one
  have hVS : S ≤ max S 1 := le_max_left S 1
  have hs2 : Real.sin (2 * θ) ≠ 0 :=
    ne_of_gt (Work.FTS_RegExport.RXT.sin_two_pos_Q0 ⟨hz, hθ, hθ2⟩)
  -- the `τ`-Lipschitz bounds of the radial pieces
  obtain ⟨CF, hCF0, -, -, hL12der, hLipL, hLipF⟩ :=
    L12FK_family_jets (C₀ := C₀) (Φs := Φs) (E := E) (g := g) hα hα13 hOK.2 (max S 1) hS0
  -- the `τ`-continuity of the three slots of the residual
  obtain ⟨hRs0, hVs0, hUs0⟩ :=
    slot_tau_cont_alpha (Ce := Ce) (C₀ := C₀) (Cs := Cs) (Φs := Φs) (E := E) (g := g)
      hα hα13 hEll hEL3 hStar hSol hOK hμ (max S 1) hS0 z θ hz hθ hθ2
  have hsub : Set.Icc (0 : ℝ) S ⊆ Set.Icc (0 : ℝ) (max S 1) :=
    fun τ hτ => ⟨hτ.1, le_trans hτ.2 hVS⟩
  have hVslot : ContinuousOn (fun τ => Vop (v2_PhiT α Φs E g τ) z θ) (Set.Icc 0 S) := by
    refine (hVs0.mono hsub).congr (fun τ hτ => ?_)
    unfold Work.FTS_RegExport.RXT.v2_SlotV
    rfl
  have hRslot : ContinuousOn (fun τ => Rop (pExp α) (v2_PhiT α Φs E g τ) z θ) (Set.Icc 0 S) := by
    refine (hRs0.mono hsub).congr (fun τ hτ => ?_)
    unfold Work.FTS_RegExport.RXT.v2_SlotR
    rfl
  have hUslot : ContinuousOn (fun τ => Uop (pExp α) (v2_PhiT α Φs E g τ) z θ
      / Real.sin (2 * θ)) (Set.Icc 0 S) := by
    refine (hUs0.mono hsub).congr (fun τ hτ => ?_)
    unfold Work.FTS_RegExport.RXT.v2_SlotU
    rfl
  -- `μ`
  have hμc : ContinuousOn (fun τ => μR α Φs E g τ) (Set.Icc 0 S) := by
    refine (hμ.2.mono (fun τ hτ => hτ.1)).congr (fun τ hτ => ?_)
    show Work.FTS.Galerkin.muDyn (pExp α) (Work.FTS.Nonlin.PsiCan Φs E g) g (max τ 0)
      = Work.FTS.Galerkin.muDyn (pExp α) (Work.FTS.Nonlin.PsiCan Φs E g) g τ
    rw [max_eq_left hτ.1]
  -- `L₁₂(F_τ) z` and `𝔽K(F_τ) z`
  have hL12c : ContinuousOn (fun τ => L12 (Ftau (pExp α) (GR α g) τ) z) (Set.Icc 0 S) := by
    refine continuousOn_of_abs_sub_le hCF0 (fun τ hτ τ' hτ' => ?_)
    exact hLipL τ ⟨hτ.1, le_trans hτ.2 hVS⟩ τ' ⟨hτ'.1, le_trans hτ'.2 hVS⟩ z hz
  have hFKc : ContinuousOn (fun τ => FK (Ftau (pExp α) (GR α g) τ) z) (Set.Icc 0 S) := by
    refine continuousOn_of_abs_sub_le hCF0 (fun τ hτ τ' hτ' => ?_)
    exact hLipF τ ⟨hτ.1, le_trans hτ.2 hVS⟩ τ' ⟨hτ'.1, le_trans hτ'.2 hVS⟩ z hz
  -- the `Θ`-part of the `Uop`-slot, in closed form
  have hThetaUc : ContinuousOn (fun τ => 2 * Uop (pExp α)
      (Theta (pExp α) (Ftau (pExp α) (GR α g) τ)) z θ / Real.sin (2 * θ)) (Set.Icc 0 S) := by
    refine (((continuousOn_const (c := -(3 / (2 * pExp α)))).mul hL12c).add
      ((continuousOn_const (c := (1 / 2 : ℝ))).mul hFKc)).congr (fun τ hτ => ?_)
    have hτS : τ ∈ Set.Icc (0 : ℝ) (max S 1) := ⟨hτ.1, le_trans hτ.2 hVS⟩
    have hL12d : ∀ z' : ℝ, 0 < z' → z' * deriv (fun z'' => L12 (Ftau (pExp α) (GR α g) τ) z'') z'
        = -FK (Ftau (pExp α) (GR α g) τ) z' := by
      intro z' hz'
      have h := hL12der τ hτS z' hz'
      have h2 : Work.Spaces.DzIter 1 (fun z _ => L12 (Ftau (pExp α) (GR α g) τ) z) z' 0
          = z' * deriv (fun z'' => L12 (Ftau (pExp α) (GR α g) τ) z'') z' := by
        rw [Work.Spaces.DzIter_succ, Work.Spaces.DzIter_zero]
        rfl
      rwa [h2] at h
    have hOps := Work.FTS_RegExport.RXT.SysAux.Theta_ops (αG := pExp α) hαG
      (F := Ftau (pExp α) (GR α g) τ) hL12d z θ hz hθ hθ2
    rw [hOps.2.1, div_eq_iff hs2]
    simp only [Pi.add_apply, Pi.mul_apply]
    ring
  -- the three coefficients
  have hVzc : ContinuousOn (fun τ => Vz7 (pExp α) (μR α Φs E g) (GR α g)
      (ΦR α Φs E g) z θ τ) (Set.Icc 0 S) := by
    refine (((continuousOn_const (c := (1 : ℝ))).sub hμc).add
      (hL12c.mul_const (c2m θ))).add
      (hVslot.const_mul (2 * pExp α)) |>.congr (fun τ hτ => ?_)
    show Vz7 (pExp α) (μR α Φs E g) (GR α g) (ΦR α Φs E g) z θ τ
      = (1 - μR α Φs E g τ) + L12 (Ftau (pExp α) (GR α g) τ) z * c2m θ
        + 2 * pExp α * Vop (v2_PhiT α Φs E g τ) z θ
    simp only [Vz7]
    rw [← v2_PhiT_eq_phiTil (α := α) (Φs := Φs) (E := E) (g := g) τ]
  have hVthc : ContinuousOn (fun τ => Vθ7 (pExp α) (ΦR α Φs E g) z θ τ
      / Real.sin (2 * θ)) (Set.Icc 0 S) := by
    refine ((hUslot.const_mul 2).add hThetaUc).congr (fun τ hτ => ?_)
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hsmPsi, hsmTheta⟩ :=
      coeff_pieces_contDiffOn (C₀ := C₀) (Cs := Cs) (g := g) hα hα13 hEL3 hStar hOK hτ.1
    simp only [Vθ7, Work.FTS.Galerkin.slice]
    rw [uop_split_theta (Φs := Φs) (E := E) (g := g) (τ := τ) (z := z) (θ := θ)
      ⟨hz, hθ, hθ2⟩ hsmPsi hsmTheta]
    simp only [Pi.add_apply, Pi.mul_apply]
    ring
  have hCsc : ContinuousOn (fun τ => cs7 (pExp α) (μR α Φs E g) (GR α g)
      (ΦR α Φs E g) z θ τ) (Set.Icc 0 S) := by
    refine ((((continuousOn_const (c := (1 : ℝ))).add hμc).sub
      (hL12c.div_const (pExp α))).add
      (hFKc.const_mul ((Real.sin θ) ^ 2))).sub
      (hRslot.const_mul 2) |>.congr (fun τ hτ => ?_)
    show cs7 (pExp α) (μR α Φs E g) (GR α g) (ΦR α Φs E g) z θ τ
      = (1 + μR α Φs E g τ) - L12 (Ftau (pExp α) (GR α g) τ) z / pExp α
        + (Real.sin θ) ^ 2 * FK (Ftau (pExp α) (GR α g) τ) z
        - 2 * Rop (pExp α) (v2_PhiT α Φs E g τ) z θ
    simp only [cs7]
    rw [← v2_PhiT_eq_phiTil (α := α) (Φs := Φs) (E := E) (g := g) τ]
  exact hVzc.prodMk (hVthc.prodMk hCsc)

end Work.FTS_RegExport.RXT.Sys
