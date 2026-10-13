import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS_RegExport.RXR5L.ProdDefs
import Submission.Work.FTS_RegExport.RXT.Sys.slot_tau_cont_alpha
import Submission.Work.FTS_RegExport.RXT.SysAux.pertSlot_lip_approx

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open Set Filter
open scoped Topology Real

namespace Work.FTS_RegExport.RXR5L

open Work.FTS.Galerkin (Fn Fam slice)

/-- The `τ`-Lipschitz data of the three slots `CoefR/CoefV/CoefU` of `PhiT α Φs E g τ`, uniform
in `(z,θ)` on the open quadrant.  This is the *Lipschitz* form of
`RXT.Sys.slot_tau_cont_alpha` (which only states continuity), with the same constant `K`.

Route (`Submission/Work/FTS_RegExport/RXT/Sys/slot_tau_cont_alpha.lean`, whose proof already
establishes these three Lipschitz bounds internally before discarding them in favour of
`ContinuousOn`): on the quadrant `PhiT α Φs E g τ = v2_PhiStar α Φs + v2_PhiPert α E g τ`
(`v2_phiTil_split`), the star slot is `τ`-independent, and the three slots are additive
(`v2_rop_add_at` / `v2_vop_add_at` / `v2_uop_div_add_at`), so it suffices to bound the difference of
the perturbation slots.  The approximants `Ξ_n(τ) = PhiTil (slice (gn n) τ) (E (slice (gn n) τ))`
of `hOK.2 = LimApprox` are uniformly Lipschitz in `τ` with one constant `K` for all `n`
(`SysAux.pertSlot_lip_approx`, from `EllPkgGo` applied to the class-`C` difference
`slice (gn n) τ - slice (gn n) τ'`), and converge pointwise to the limit slots
(`SysAux.pertSlot_tendsto`); `lipschitz_of_approx` then transfers the bound to the limit. -/
theorem coef_tau_lip {α Ce C₀ Cs : ℝ} {Φs : Work.FTS.Galerkin.Fn}
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
    ∀ S > 0, ∃ K : ℝ, 0 ≤ K ∧ ∀ τ ∈ Set.Icc 0 S, ∀ τ' ∈ Set.Icc 0 S, ∀ z θ : ℝ,
      0 < z → 0 < θ → θ < π / 2 →
      |Work.FTS_RegExport.RXR5L.CoefR α Φs E g τ z θ
          - Work.FTS_RegExport.RXR5L.CoefR α Φs E g τ' z θ| ≤ K * |τ - τ'| ∧
      |Work.FTS_RegExport.RXR5L.CoefV α Φs E g τ z θ
          - Work.FTS_RegExport.RXR5L.CoefV α Φs E g τ' z θ| ≤ K * |τ - τ'| ∧
      |Work.FTS_RegExport.RXR5L.CoefU α Φs E g τ z θ
          - Work.FTS_RegExport.RXR5L.CoefU α Φs E g τ' z θ| ≤ K * |τ - τ'| := by
  intro S hS
  have hαG : 0 < Work.FTS.Regularity.pExp α := Work.FTS.Regularity.pExp_pos hα
  have hαG1 : Work.FTS.Regularity.pExp α ≤ 1 := Work.FTS.Regularity.pExp_le_one hα13
  obtain ⟨gn, B, L, hAppx, hLipC, hJetC, _hμc⟩ := hOK.2 S hS
  -- the uniform Lipschitz bound for the approximant slots
  obtain ⟨K, hK0, hB⟩ := Work.FTS_RegExport.RXT.SysAux.pertSlot_lip_approx
    (α := α) (Ce := Ce) (L := L) (E := E) hα hα13 hEll
    (fun n τ hτ => (hAppx n τ hτ).1) (fun n τ hτ τ' hτ' => hLipC n τ hτ τ' hτ')
  refine ⟨K, hK0, ?_⟩
  intro τ hτ τ' hτ' z θ hz hθ hθ2
  -- ## the pointwise convergence of the approximant slots
  have hC : ∀ τ ∈ Set.Icc (0:ℝ) S,
      (Filter.Tendsto (fun n : ℕ => Work.Construction.Rop (Work.FTS.Regularity.pExp α)
          (Work.Construction.PhiTil (Work.FTS.Regularity.pExp α) (slice (gn n) τ)
            (E (slice (gn n) τ))) z θ) Filter.atTop
        (nhds (Work.Construction.Rop (Work.FTS.Regularity.pExp α)
          (Work.Construction.PhiTil (Work.FTS.Regularity.pExp α) (slice g τ)
            (E (slice g τ))) z θ))) ∧
      (Filter.Tendsto (fun n : ℕ => Work.Construction.Vop
          (Work.Construction.PhiTil (Work.FTS.Regularity.pExp α) (slice (gn n) τ)
            (E (slice (gn n) τ))) z θ) Filter.atTop
        (nhds (Work.Construction.Vop
          (Work.Construction.PhiTil (Work.FTS.Regularity.pExp α) (slice g τ)
            (E (slice g τ))) z θ))) ∧
      (Filter.Tendsto (fun n : ℕ => Work.Construction.Uop (Work.FTS.Regularity.pExp α)
          (Work.Construction.PhiTil (Work.FTS.Regularity.pExp α) (slice (gn n) τ)
            (E (slice (gn n) τ))) z θ / Real.sin (2 * θ)) Filter.atTop
        (nhds (Work.Construction.Uop (Work.FTS.Regularity.pExp α)
          (Work.Construction.PhiTil (Work.FTS.Regularity.pExp α) (slice g τ)
            (E (slice g τ))) z θ / Real.sin (2 * θ)))) :=
    fun τ hτ => Work.FTS_RegExport.RXT.SysAux.pertSlot_tendsto
      (α := α) (Ce := Ce) (C₀ := C₀) (Φs := Φs) (E := E) (g := g)
      hα hα13 hEll hEL3 hOK hS hAppx hJetC hτ z θ hz hθ hθ2
  -- ## regularity of the split pieces
  have hStar3 : ContDiffOn ℝ 3 (Function.uncurry (Work.FTS_RegExport.RXT.v2_PhiStar α Φs))
      Work.FTS.EllipticEst.Q0 :=
    (Work.FTS.PhiStar.CoreAux.fields_smooth hαG hαG1 hStar.smooth).1.of_le
      (by simp [Work.Stability.smoothOrder])
  have hStar1 : ContDiffOn ℝ 1 (Function.uncurry (Work.FTS_RegExport.RXT.v2_PhiStar α Φs))
      Work.FTS.EllipticEst.Q0 := hStar3.of_le (by norm_num)
  have hTheta3 : ∀ τ : ℝ, 0 ≤ τ → ContDiffOn ℝ 3 (Function.uncurry
      (Work.Construction.Theta (Work.FTS.Regularity.pExp α)
        (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
          (Work.FTS.RegExportIface.RXT.GR α g) τ))) Work.FTS.EllipticEst.Q0 := by
    intro τ hτ
    refine Work.FTS_RegExport.RXT.velPert_contDiffOn_Theta
      (α := Work.FTS.Regularity.pExp α) ?_
    refine Work.FTS_RegExport.RXT.contDiffOn_three_L12 ?_
    obtain ⟨C, _hC0, hCb⟩ := Work.FTS_RegExport.RXT.Ftau_bounds
      (Φs := Φs) (E := E) hα hα13 hOK τ hτ
    exact Work.FTS_RegExport.RXT.contDiffOn_two_integral_Itheta (φ := Work.Spaces.K)
      Work.FTS_RegExport.RXT.v2_continuousOn_K_Iθ
      (Work.FTS_RegExport.RXT.contDiffOn_Ftau_Q0 (Φs := Φs) (E := E) hα hα13 hOK τ hτ)
      (fun z₁ θ₁ hz₁ hθ₁ hθ₁2 => ⟨(hCb z₁ θ₁ hz₁ hθ₁ hθ₁2).1,
        (hCb z₁ θ₁ hz₁ hθ₁ hθ₁2).2.1, (hCb z₁ θ₁ hz₁ hθ₁ hθ₁2).2.2⟩)
  have hFull3 : ∀ τ : ℝ, 0 ≤ τ →
      ContDiffOn ℝ 3 (Function.uncurry (Work.FTS_RegExport.RXT.v2_PhiT α Φs E g τ))
        Work.FTS.EllipticEst.Q0 := by
    intro τ hτ
    have hP := Work.FTS_RegExport.RXT.contDiffOn_slice_PhiR_Q0
      (α := α) (C₀ := C₀) (Cs := Cs) hEL3 hStar hOK τ hτ
    exact hP.sub (hTheta3 τ hτ)
  have hPert3 : ∀ τ : ℝ, 0 ≤ τ →
      ContDiffOn ℝ 3 (Function.uncurry (Work.FTS_RegExport.RXT.v2_PhiPert α E g τ))
        Work.FTS.EllipticEst.Q0 := by
    intro τ hτ
    refine ((hFull3 τ hτ).sub hStar3).congr ?_
    intro p hp
    obtain ⟨z₁, θ₁⟩ := p
    simp only [Function.uncurry]
    linarith [Work.FTS_RegExport.RXT.v2_phiTil_split (C₀ := C₀) hα hα13 hOK hτ z₁ θ₁ hp]
  have hPert1 : ∀ τ : ℝ, 0 ≤ τ →
      ContDiffOn ℝ 1 (Function.uncurry (Work.FTS_RegExport.RXT.v2_PhiPert α E g τ))
        Work.FTS.EllipticEst.Q0 := fun τ hτ => (hPert3 τ hτ).of_le (by norm_num)
  -- ## the split identities of the three slots at `(z,θ)`
  have hsplitFun : ∀ τ : ℝ, 0 ≤ τ → Work.FTS_RegExport.RXR5.AgreeOnQ
      (Work.FTS_RegExport.RXT.v2_PhiT α Φs E g τ)
      (Work.FTS_RegExport.RXT.v2_PhiStar α Φs + Work.FTS_RegExport.RXT.v2_PhiPert α E g τ) :=
    fun τ hτ z₁ θ₁ hz₁ hθ₁ hθ₁2 =>
      Work.FTS_RegExport.RXT.v2_phiTil_split (C₀ := C₀) hα hα13 hOK hτ z₁ θ₁
        (Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz₁, hθ₁, hθ₁2⟩)
  have hsplitR : ∀ τ ∈ Set.Icc (0:ℝ) S, Work.FTS_RegExport.RXT.v2_SlotR α
        (Work.FTS_RegExport.RXT.v2_PhiT α Φs E g τ) z θ
      = Work.FTS_RegExport.RXT.v2_SlotR α (Work.FTS_RegExport.RXT.v2_PhiStar α Φs) z θ
        + Work.FTS_RegExport.RXT.v2_SlotR α (Work.FTS_RegExport.RXT.v2_PhiPert α E g τ) z θ := by
    intro τ hτ
    show Work.Construction.Rop (Work.FTS.Regularity.pExp α)
        (Work.FTS_RegExport.RXT.v2_PhiT α Φs E g τ) z θ
      = Work.Construction.Rop (Work.FTS.Regularity.pExp α)
          (Work.FTS_RegExport.RXT.v2_PhiStar α Φs) z θ
        + Work.Construction.Rop (Work.FTS.Regularity.pExp α)
          (Work.FTS_RegExport.RXT.v2_PhiPert α E g τ) z θ
    rw [Work.FTS_RegExport.RXR5.Rop_congr_of_agreeOnQ (α := Work.FTS.Regularity.pExp α)
      (h := hsplitFun τ hτ.1) hz hθ hθ2]
    exact Work.FTS_RegExport.RXT.v2_rop_add_at hStar1 (hPert1 τ hτ.1) ⟨hz, hθ, hθ2⟩
  have hsplitV : ∀ τ ∈ Set.Icc (0:ℝ) S, Work.FTS_RegExport.RXT.v2_SlotV α
        (Work.FTS_RegExport.RXT.v2_PhiT α Φs E g τ) z θ
      = Work.FTS_RegExport.RXT.v2_SlotV α (Work.FTS_RegExport.RXT.v2_PhiStar α Φs) z θ
        + Work.FTS_RegExport.RXT.v2_SlotV α (Work.FTS_RegExport.RXT.v2_PhiPert α E g τ) z θ := by
    intro τ hτ
    show Work.Construction.Vop (Work.FTS_RegExport.RXT.v2_PhiT α Φs E g τ) z θ
      = Work.Construction.Vop (Work.FTS_RegExport.RXT.v2_PhiStar α Φs) z θ
        + Work.Construction.Vop (Work.FTS_RegExport.RXT.v2_PhiPert α E g τ) z θ
    rw [Work.FTS_RegExport.RXR5.Vop_congr_of_agreeOnQ (h := hsplitFun τ hτ.1) hz hθ hθ2]
    exact Work.FTS_RegExport.RXT.v2_vop_add_at hStar1 (hPert1 τ hτ.1) ⟨hz, hθ, hθ2⟩
  have hsplitU : ∀ τ ∈ Set.Icc (0:ℝ) S, Work.FTS_RegExport.RXT.v2_SlotU α
        (Work.FTS_RegExport.RXT.v2_PhiT α Φs E g τ) z θ
      = Work.FTS_RegExport.RXT.v2_SlotU α (Work.FTS_RegExport.RXT.v2_PhiStar α Φs) z θ
        + Work.FTS_RegExport.RXT.v2_SlotU α (Work.FTS_RegExport.RXT.v2_PhiPert α E g τ) z θ := by
    intro τ hτ
    show Work.Construction.Uop (Work.FTS.Regularity.pExp α)
          (Work.FTS_RegExport.RXT.v2_PhiT α Φs E g τ) z θ / Real.sin (2 * θ)
      = Work.Construction.Uop (Work.FTS.Regularity.pExp α)
            (Work.FTS_RegExport.RXT.v2_PhiStar α Φs) z θ / Real.sin (2 * θ)
        + Work.Construction.Uop (Work.FTS.Regularity.pExp α)
            (Work.FTS_RegExport.RXT.v2_PhiPert α E g τ) z θ / Real.sin (2 * θ)
    rw [Work.FTS_RegExport.RXR5.Uop_congr_of_agreeOnQ (α := Work.FTS.Regularity.pExp α)
      (h := hsplitFun τ hτ.1) hz hθ hθ2]
    exact Work.FTS_RegExport.RXT.v2_uop_div_add_at (αG := Work.FTS.Regularity.pExp α)
      hStar1 (hPert1 τ hτ.1) ⟨hz, hθ, hθ2⟩
  -- ## the Lipschitz bound for the limit slot families
  have hLR : ∀ τ ∈ Set.Icc (0:ℝ) S, ∀ τ' ∈ Set.Icc (0:ℝ) S,
      |Work.Construction.Rop (Work.FTS.Regularity.pExp α)
          (Work.Construction.PhiTil (Work.FTS.Regularity.pExp α) (slice g τ)
            (E (slice g τ))) z θ
        - Work.Construction.Rop (Work.FTS.Regularity.pExp α)
          (Work.Construction.PhiTil (Work.FTS.Regularity.pExp α) (slice g τ')
            (E (slice g τ'))) z θ| ≤ K * |τ - τ'| :=
    Work.FTS_RegExport.RXT.Sys.lipschitz_of_approx
      (A := fun n τ => Work.Construction.Rop (Work.FTS.Regularity.pExp α)
        (Work.Construction.PhiTil (Work.FTS.Regularity.pExp α) (slice (gn n) τ)
          (E (slice (gn n) τ))) z θ)
      (Alim := fun τ => Work.Construction.Rop (Work.FTS.Regularity.pExp α)
        (Work.Construction.PhiTil (Work.FTS.Regularity.pExp α) (slice g τ)
          (E (slice g τ))) z θ)
      (fun n τ hτ τ' hτ' => (hB n τ hτ τ' hτ' z θ hz hθ hθ2).1)
      (fun τ hτ => (hC τ hτ).1)
  have hLV : ∀ τ ∈ Set.Icc (0:ℝ) S, ∀ τ' ∈ Set.Icc (0:ℝ) S,
      |Work.Construction.Vop
          (Work.Construction.PhiTil (Work.FTS.Regularity.pExp α) (slice g τ)
            (E (slice g τ))) z θ
        - Work.Construction.Vop
          (Work.Construction.PhiTil (Work.FTS.Regularity.pExp α) (slice g τ')
            (E (slice g τ'))) z θ| ≤ K * |τ - τ'| :=
    Work.FTS_RegExport.RXT.Sys.lipschitz_of_approx
      (A := fun n τ => Work.Construction.Vop
        (Work.Construction.PhiTil (Work.FTS.Regularity.pExp α) (slice (gn n) τ)
          (E (slice (gn n) τ))) z θ)
      (Alim := fun τ => Work.Construction.Vop
        (Work.Construction.PhiTil (Work.FTS.Regularity.pExp α) (slice g τ)
          (E (slice g τ))) z θ)
      (fun n τ hτ τ' hτ' => (hB n τ hτ τ' hτ' z θ hz hθ hθ2).2.1)
      (fun τ hτ => (hC τ hτ).2.1)
  have hLU : ∀ τ ∈ Set.Icc (0:ℝ) S, ∀ τ' ∈ Set.Icc (0:ℝ) S,
      |Work.Construction.Uop (Work.FTS.Regularity.pExp α)
          (Work.Construction.PhiTil (Work.FTS.Regularity.pExp α) (slice g τ)
            (E (slice g τ))) z θ / Real.sin (2 * θ)
        - Work.Construction.Uop (Work.FTS.Regularity.pExp α)
          (Work.Construction.PhiTil (Work.FTS.Regularity.pExp α) (slice g τ')
            (E (slice g τ'))) z θ / Real.sin (2 * θ)| ≤ K * |τ - τ'| :=
    Work.FTS_RegExport.RXT.Sys.lipschitz_of_approx
      (A := fun n τ => Work.Construction.Uop (Work.FTS.Regularity.pExp α)
        (Work.Construction.PhiTil (Work.FTS.Regularity.pExp α) (slice (gn n) τ)
          (E (slice (gn n) τ))) z θ / Real.sin (2 * θ))
      (Alim := fun τ => Work.Construction.Uop (Work.FTS.Regularity.pExp α)
        (Work.Construction.PhiTil (Work.FTS.Regularity.pExp α) (slice g τ)
          (E (slice g τ))) z θ / Real.sin (2 * θ))
      (fun n τ hτ τ' hτ' => (hB n τ hτ τ' hτ' z θ hz hθ hθ2).2.2)
      (fun τ hτ => (hC τ hτ).2.2)
  -- ## the τ-Lipschitz bounds of the perturbation slots at the two times
  have hPR : |Work.FTS_RegExport.RXT.v2_SlotR α
        (Work.FTS_RegExport.RXT.v2_PhiPert α E g τ) z θ
      - Work.FTS_RegExport.RXT.v2_SlotR α
        (Work.FTS_RegExport.RXT.v2_PhiPert α E g τ') z θ| ≤ K * |τ - τ'| := by
    simpa only [Work.FTS_RegExport.RXT.v2_SlotR, Work.FTS_RegExport.RXT.v2_PhiPert]
      using hLR τ hτ τ' hτ'
  have hPV : |Work.FTS_RegExport.RXT.v2_SlotV α
        (Work.FTS_RegExport.RXT.v2_PhiPert α E g τ) z θ
      - Work.FTS_RegExport.RXT.v2_SlotV α
        (Work.FTS_RegExport.RXT.v2_PhiPert α E g τ') z θ| ≤ K * |τ - τ'| := by
    simpa only [Work.FTS_RegExport.RXT.v2_SlotV, Work.FTS_RegExport.RXT.v2_PhiPert]
      using hLV τ hτ τ' hτ'
  have hPU : |Work.FTS_RegExport.RXT.v2_SlotU α
        (Work.FTS_RegExport.RXT.v2_PhiPert α E g τ) z θ
      - Work.FTS_RegExport.RXT.v2_SlotU α
        (Work.FTS_RegExport.RXT.v2_PhiPert α E g τ') z θ| ≤ K * |τ - τ'| := by
    simpa only [Work.FTS_RegExport.RXT.v2_SlotU, Work.FTS_RegExport.RXT.v2_PhiPert]
      using hLU τ hτ τ' hτ'
  -- ## the target slots are the `RXT` slots of `v2_PhiT`, and the star part cancels
  have eR : CoefR α Φs E g τ z θ = Work.FTS_RegExport.RXT.v2_SlotR α
        (Work.FTS_RegExport.RXT.v2_PhiT α Φs E g τ) z θ := rfl
  have eR' : CoefR α Φs E g τ' z θ = Work.FTS_RegExport.RXT.v2_SlotR α
        (Work.FTS_RegExport.RXT.v2_PhiT α Φs E g τ') z θ := rfl
  have eV : CoefV α Φs E g τ z θ = Work.FTS_RegExport.RXT.v2_SlotV α
        (Work.FTS_RegExport.RXT.v2_PhiT α Φs E g τ) z θ := rfl
  have eV' : CoefV α Φs E g τ' z θ = Work.FTS_RegExport.RXT.v2_SlotV α
        (Work.FTS_RegExport.RXT.v2_PhiT α Φs E g τ') z θ := rfl
  have eU : CoefU α Φs E g τ z θ = Work.FTS_RegExport.RXT.v2_SlotU α
        (Work.FTS_RegExport.RXT.v2_PhiT α Φs E g τ) z θ := rfl
  have eU' : CoefU α Φs E g τ' z θ = Work.FTS_RegExport.RXT.v2_SlotU α
        (Work.FTS_RegExport.RXT.v2_PhiT α Φs E g τ') z θ := rfl
  refine ⟨?_, ?_, ?_⟩
  · have harg : CoefR α Φs E g τ z θ - CoefR α Φs E g τ' z θ
        = Work.FTS_RegExport.RXT.v2_SlotR α (Work.FTS_RegExport.RXT.v2_PhiPert α E g τ) z θ
          - Work.FTS_RegExport.RXT.v2_SlotR α
              (Work.FTS_RegExport.RXT.v2_PhiPert α E g τ') z θ := by
      rw [eR, eR', hsplitR τ hτ, hsplitR τ' hτ']
      ring
    rw [harg]
    exact hPR
  · have harg : CoefV α Φs E g τ z θ - CoefV α Φs E g τ' z θ
        = Work.FTS_RegExport.RXT.v2_SlotV α (Work.FTS_RegExport.RXT.v2_PhiPert α E g τ) z θ
          - Work.FTS_RegExport.RXT.v2_SlotV α
              (Work.FTS_RegExport.RXT.v2_PhiPert α E g τ') z θ := by
      rw [eV, eV', hsplitV τ hτ, hsplitV τ' hτ']
      ring
    rw [harg]
    exact hPV
  · have harg : CoefU α Φs E g τ z θ - CoefU α Φs E g τ' z θ
        = Work.FTS_RegExport.RXT.v2_SlotU α (Work.FTS_RegExport.RXT.v2_PhiPert α E g τ) z θ
          - Work.FTS_RegExport.RXT.v2_SlotU α
              (Work.FTS_RegExport.RXT.v2_PhiPert α E g τ') z θ := by
      rw [eU, eU', hsplitU τ hτ, hsplitU τ' hτ']
      ring
    rw [harg]
    exact hPU

end Work.FTS_RegExport.RXR5L
