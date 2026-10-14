import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.c2mGam_Wt_bound
import Submission.Work.FTS_RegExport.RXT.C2Radial
import Submission.Work.FTS_RegExport.RXT.omega_facts
import Submission.Work.FTS_RegExport.VPOpen
import Submission.Work.FTS_StreamBdry.SB6.clauses3
import Submission.Work.GalerkinFix.RegQ.HkMem_mono_Q
-- ===== merged: Submission.Work.FTS_EllLimOK.ProducerH.abs_pzIterTwo_psiP_le =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_EllLimOK.ProducerH

/-- **The `z²∂_z²` bound for the particular solution `psiP` at `z = 1`.**
`SlotBd α Ψ M` bounds `|D_z^j psiP| ≤ M·sin 2θ` for `j ≤ 2` (`SB3.psiP_DzLe`, which needs
`0 < α`, `ContDiffOn ℝ 3 (uncurry Ψ) Qd` and `SlotBd α Ψ M`), and on the open quadrant
`z²∂_z² h = D_z²h - D_zh` (`ClassC.seven_zsq_pzIter_two_eq`, from `SmoothOpen h`).
At `z = 1` (`1² = 1`) this gives `|∂_z² psiP| = |D_z² psiP − D_z psiP| ≤ M sin 2θ + M sin 2θ =
2 M sin 2θ` by the triangle inequality (no sign hypothesis on `M` is needed for that step).
Consumed by `Work.FTS.EllLimOK.ProducerH.kappa_eq_zero`. -/
theorem abs_pzIterTwo_psiP_le {α M : ℝ} (hα : 0 < α) {Ψ : ℝ → ℝ → ℝ}
    (h3 : ContDiffOn ℝ 3 (Function.uncurry Ψ) Work.Construction.Qd)
    (hslot : Work.FTS.StreamBdryIface.SlotBd α Ψ M)
    (hP : Work.FTS.EllipticEst.SmoothOpen (Work.FTS.StreamBdryIface.psiP α Ψ))
    {θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    |Work.Spaces.pzIter 2 (Work.FTS.StreamBdryIface.psiP α Ψ) 1 θ|
      ≤ 2 * M * Real.sin (2 * θ) := by
  -- SB3: `|D_z^j psiP| ≤ M·sin 2θ` on the open quadrant, for `j ≤ 2`.
  have hPsi : Work.FTS_StreamBdry.PsiPDzLe α M Ψ :=
    Work.FTS_StreamBdry.SB3.psiP_DzLe hα h3 hslot
  have hmem : ((1 : ℝ), θ) ∈ Work.Construction.Qd :=
    ⟨by norm_num, hθ.1, hθ.2⟩
  have h2 : |Work.Spaces.DzIter 2 (Work.FTS.StreamBdryIface.psiP α Ψ) 1 θ|
      ≤ M * Real.sin (2 * θ) := by
    simpa only [Work.Construction.s2_eq] using hPsi 1 θ hmem 2 (by norm_num)
  have h1 : |Work.Spaces.DzIter 1 (Work.FTS.StreamBdryIface.psiP α Ψ) 1 θ|
      ≤ M * Real.sin (2 * θ) := by
    simpa only [Work.Construction.s2_eq] using hPsi 1 θ hmem 1 (by norm_num)
  -- The level-0 identity `z²∂_z²h = D_z²h − D_zh`, at `z = 1`.
  have heq := Work.FTS.ClassC.seven_zsq_pzIter_two_eq
    (Work.FTS.StreamBdryIface.psiP α Ψ) hP 1 θ (by norm_num) hθ.1 hθ.2
  have hkey : Work.Spaces.pzIter 2 (Work.FTS.StreamBdryIface.psiP α Ψ) 1 θ
      = Work.Spaces.DzIter 2 (Work.FTS.StreamBdryIface.psiP α Ψ) 1 θ
        - Work.Spaces.DzIter 1 (Work.FTS.StreamBdryIface.psiP α Ψ) 1 θ := by
    simpa using heq
  rw [hkey]
  calc |Work.Spaces.DzIter 2 (Work.FTS.StreamBdryIface.psiP α Ψ) 1 θ
          - Work.Spaces.DzIter 1 (Work.FTS.StreamBdryIface.psiP α Ψ) 1 θ|
      ≤ |Work.Spaces.DzIter 2 (Work.FTS.StreamBdryIface.psiP α Ψ) 1 θ|
        + |Work.Spaces.DzIter 1 (Work.FTS.StreamBdryIface.psiP α Ψ) 1 θ| := abs_sub _ _
    _ ≤ M * Real.sin (2 * θ) + M * Real.sin (2 * θ) := add_le_add h2 h1
    _ = 2 * M * Real.sin (2 * θ) := by ring

end Work.FTS_EllLimOK.ProducerH
end
-- ===== merged: Submission.Work.FTS_RegExport.RXVP3.vz0_of_vopLower =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS_RegExport.RXVP3.vz0_of_vopLower`

The `vz0` clause of `Work.FTS_RegExport.VelPkgOpen` at the sanitised family
`(gS α (tauExt g), psiR α Φs E (tauExt g))`, reduced to the *lower bound*

  `hVop : -(1 - maxMu τ) ≤ 2 α·V(Φ)(z,θ)`   (`Φ = slice (psiR α Φs E (tauExt g)) τ`)

on the `V`-slot of the stream function itself.

On the open quadrant `RXDiag.closedFormOpen` writes the coefficient as

  `Vz7 = (1 - μ τ) + L₁₂(F)·c2m(θ) + 2α·V(Φ̃)`,   `Φ̃ = Φ − Θ(F)`,  `F = Ftau αG G τ`,

and the `Θ`-identity `2α·V(Θ αG F) = L₁₂(F)·c2m(θ)` (whose proof needs only the *value* of
`∂_θΘ`, i.e. `Construction.pth_Theta_eq`) collapses this to

  `Vz7 = (1 - μ τ) + 2α·V(Φ)`.

The `Θ`-identity only asks for the differentiability of the `θ`-slice of `Φ` at the point,
which is supplied here by `RXT.contDiffOn_slice_PhiR_Q0` (`slice (psiR …) τ` is `C³` on the
open quadrant, from `EllLimOK3`, `StarPkgo2`, `DynOK'`).  Hence

  `0 ≤ Vz7  ⟺  -(1 - μ τ) ≤ 2α·V(Φ)`,   which is exactly `hVop`.
-/

noncomputable section
open scoped Real Topology

namespace Work.FTS_RegExport.RXVP3

set_option autoImplicit false

/-- The `θ`-slice of a function which is `C^n` on the open quadrant is `C^n` on `(0, π/2)`. -/
theorem vz7_contDiffOn_thslice {f : ℝ → ℝ → ℝ} {n : ℕ} {z : ℝ} (hz : 0 < z)
    (hf : ContDiffOn ℝ n (Function.uncurry f) Work.FTS.EllipticEst.Q0) :
    ContDiffOn ℝ n (fun θ => f z θ) (Set.Ioo 0 (π / 2)) :=
  (hf.comp (((contDiffOn_const (c := z) :
      ContDiffOn ℝ n (fun _ : ℝ => z) (Set.Ioo 0 (π / 2)))).prodMk
    (contDiffOn_id : ContDiffOn ℝ n (fun θ : ℝ => θ) (Set.Ioo 0 (π / 2))))
    (fun _ hθ => ⟨hz, hθ⟩)).congr (fun _ _ => rfl)

/-- The `θ`-slice of a function which is `C³` on the open quadrant is differentiable at every
interior point of the quadrant. -/
theorem vz7_differentiableAt_tslice {f : ℝ → ℝ → ℝ}
    (hf : ContDiffOn ℝ 3 (Function.uncurry f) Work.FTS.EllipticEst.Q0) {z θ : ℝ}
    (hz : 0 < z) (h0 : 0 < θ) (h1 : θ < π / 2) :
    DifferentiableAt ℝ (fun θ' => f z θ') θ := by
  have h1c : ContDiffOn ℝ 1 (fun θ' : ℝ => f z θ') (Set.Ioo 0 (π / 2)) :=
    vz7_contDiffOn_thslice (n := 1) hz (hf.of_le (by norm_num))
  exact (h1c.differentiableOn (by norm_num)).differentiableAt
    (isOpen_Ioo.mem_nhds ⟨h0, h1⟩)

/-- **The closed form of `V(Θ)`**: `2 α·V(Θ α F) = L₁₂(F)·c2m(θ)` on the open quadrant
(no differentiability of `F` is needed: only the explicit `∂_θ`-derivative of `sin 2θ`).  This
is the `V`-half of `RXDiag.closedFormOpen`'s `two_mul_Vop_Theta`, extracted so that it can be
used with a mere `DifferentiableAt` hypothesis on the `θ`-slice. -/
theorem vz7_two_mul_Vop_Theta {αG : ℝ} (hαG : 0 < αG) {F : ℝ → ℝ → ℝ} {z θ : ℝ}
    (hθ : 0 < θ) (hθ2 : θ < π / 2) :
    2 * αG * Work.Construction.Vop (Work.Construction.Theta αG F) z θ
      = Work.Construction.L12 F z * Work.Construction.c2m θ := by
  have hcos : Real.cos θ ≠ 0 := ne_of_gt (Real.cos_pos_of_mem_Ioo
    ⟨by linarith [Real.pi_pos], hθ2⟩)
  have hpth := Work.Construction.pth_Theta_eq (α := αG) (F := F) hαG z θ
  simp only [Work.Construction.Vop, hpth, Work.Construction.Theta, Work.Construction.s2,
    Work.Construction.c2m, Real.tan_eq_sin_div_cos]
  rw [Real.sin_two_mul, Real.cos_two_mul']
  field_simp
  rw [Real.sin_sq]
  ring

/-- **The `Θ`-split of `V`**: `V(Φ̃) = V(Φ) − V(Θ α F)` for `Φ̃ = Φ − Θ α F`, at any point where
the `θ`-slice of `Φ` is differentiable (`V` is `∂_θ − tan θ`, and the `θ`-dependence of `Θ` is
the explicit factor `sin 2θ`). -/
theorem vz7_vop_phiTil_eq {αG : ℝ} {F Ψ : ℝ → ℝ → ℝ} {z θ : ℝ}
    (hΨ : DifferentiableAt ℝ (fun θ' => Ψ z θ') θ) :
    Work.Construction.Vop (Work.Construction.PhiTil αG F Ψ) z θ
      = Work.Construction.Vop Ψ z θ
        - Work.Construction.Vop (Work.Construction.Theta αG F) z θ := by
  have hΘ : DifferentiableAt ℝ (fun θ' => Work.Construction.Theta αG F z θ') θ := by
    have hfun : (fun θ' => Work.Construction.Theta αG F z θ')
        = fun θ' => ((1 / (4 * αG)) * Work.Construction.L12 F z) * Real.sin (2 * θ') := by
      funext θ'
      simp only [Work.Construction.Theta, Work.Construction.s2]
      ring
    rw [hfun]
    fun_prop
  have hpth : Work.Spaces.pth (Work.Construction.PhiTil αG F Ψ) z θ
      = Work.Spaces.pth Ψ z θ - Work.Spaces.pth (Work.Construction.Theta αG F) z θ := by
    simp only [Work.Spaces.pth]
    rw [show (fun θ' => Work.Construction.PhiTil αG F Ψ z θ')
          = (fun θ' => Ψ z θ') - (fun θ' => Work.Construction.Theta αG F z θ') from by
        funext θ'; rfl,
      deriv_sub hΨ hΘ]
  have hval : Work.Construction.PhiTil αG F Ψ z θ
      = Ψ z θ - Work.Construction.Theta αG F z θ := rfl
  simp only [Work.Construction.Vop]
  rw [hpth, hval]
  ring

/-- **The closed form of `Vz7` on the open quadrant.**  For any families `G`, `Φ` and any clock
`μ`, at a point of the open quadrant where the `θ`-slice of `Φ` (at time `τ`) is differentiable,

  `Vz7 αG μ G Φ z θ τ = (1 - μ τ) + 2 αG·V (slice Φ τ) z θ`.

So the `Θ`-part of the coefficient contributes exactly `L₁₂(F)·c2m(θ) = 2αG·V(Θ)`. -/
theorem vz7_eq_of_vop {αG : ℝ} (hαG : 0 < αG) {μ : ℝ → ℝ} {G Φ : Work.FTS.Galerkin.Fam}
    {z θ τ : ℝ} (hθ : 0 < θ) (hθ2 : θ < Real.pi / 2)
    (hd : DifferentiableAt ℝ (fun θ' => Work.FTS.Galerkin.slice Φ τ z θ') θ) :
    Work.FTS.RegExportIface.Vz7 αG μ G Φ z θ τ
      = (1 - μ τ) + 2 * αG * Work.Construction.Vop (Work.FTS.Galerkin.slice Φ τ) z θ := by
  have hsub : Work.Construction.Vop (Work.FTS.RegExportIface.phiTil αG G Φ τ) z θ
      = Work.Construction.Vop (Work.FTS.Galerkin.slice Φ τ) z θ
        - Work.Construction.Vop
            (Work.Construction.Theta αG (Work.Construction.Ftau αG G τ)) z θ :=
    vz7_vop_phiTil_eq (αG := αG) (F := Work.Construction.Ftau αG G τ) hd
  have hΘ : 2 * αG * Work.Construction.Vop
        (Work.Construction.Theta αG (Work.Construction.Ftau αG G τ)) z θ
      = Work.Construction.L12 (Work.Construction.Ftau αG G τ) z * Work.Construction.c2m θ :=
    vz7_two_mul_Vop_Theta (αG := αG) hαG hθ hθ2
  simp only [Work.FTS.RegExportIface.Vz7]
  rw [hsub, mul_sub, hΘ]
  ring

theorem vz0_of_vopLower {α C₀ Ce Cs : ℝ} {Φs : Work.FTS.Galerkin.Fn} {E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn} {g : Work.FTS.Galerkin.Fam} (hα : 0 < α) (hα13 : α ≤ 1 / 3)
    (hEll : ∀ u : Work.FTS.Galerkin.Fn, Work.FTS.ClassC.ClassC (Work.FTS.Regularity.pExp α) u →
      Work.FTS.Final.EllPkgGo (Work.FTS.Regularity.pExp α) Ce u (E u) ∧
        Work.FTS.ClassC.EllPkgK (Work.FTS.Regularity.pExp α) 6 Ce u (E u))
    (hEL3 : Work.FTS.FinalV2.EllLimOK3 (Work.FTS.Regularity.pExp α) E)
    (hStar : Work.FTS.Final.StarPkgo2 (Work.FTS.Regularity.pExp α) Cs Φs)
    (hSol : Work.FTS.FinalV2.Sol (Work.FTS.Regularity.pExp α) Φs E g)
    (hOK : Work.FTS.FinalV2.DynOK' (Work.FTS.Regularity.pExp α) C₀ Φs E g)
    (hdat : ∃ L β : ℝ, 1 ≤ L ∧ ∀ z θ, g z θ 0 =
      Work.FTS.LocData6.locG6 (Work.FTS.Regularity.pExp α) L β z θ)
    (hμ : Work.FTS.RegExportIface.ClockBd α Φs E g)
    (hVop : ∀ z θ τ, 0 < z → 0 < θ → θ < Real.pi / 2 → 0 ≤ τ →
      -(1 - Work.FTS.Final.maxMu (Work.FTS.Regularity.pExp α)
            (Work.FTS.Nonlin.PsiCan Φs E g) g τ)
        ≤ 2 * Work.FTS.Regularity.pExp α *
          Work.Construction.Vop (Work.FTS.Galerkin.slice
            (Work.FTS.RegExportIface.psiR α Φs E (Work.FTS.FinalV2.tauExt g)) τ) z θ) :
    ∀ z θ τ, 0 < z → 0 < θ → θ < Real.pi / 2 → 0 ≤ τ →
      0 ≤ Work.FTS.RegExportIface.Vz7 (Work.FTS.Regularity.pExp α)
        (Work.FTS.Final.maxMu (Work.FTS.Regularity.pExp α)
          (Work.FTS.Nonlin.PsiCan Φs E g) g)
        (Work.FTS.FinalV2.gS α (Work.FTS.FinalV2.tauExt g))
        (Work.FTS.RegExportIface.psiR α Φs E (Work.FTS.FinalV2.tauExt g)) z θ τ := by
  intro z θ τ hz hθ hθ2 hτ
  have hαG : 0 < Work.FTS.Regularity.pExp α := Work.FTS.Regularity.pExp_pos hα
  -- the stream function `slice (psiR α Φs E (tauExt g)) τ` is `C³` on the open quadrant
  have hsm : ContDiffOn ℝ 3
      (Function.uncurry (Work.FTS.Galerkin.slice
        (Work.FTS.RegExportIface.RXT.ΦR α Φs E g) τ)) Work.FTS.EllipticEst.Q0 :=
    Work.FTS_RegExport.RXT.contDiffOn_slice_PhiR_Q0 (α := α) (C₀ := C₀) (Cs := Cs)
      (Φs := Φs) (E := E) (g := g) hEL3 hStar hOK τ hτ
  -- hence its `θ`-slice is differentiable at the point
  have hd : DifferentiableAt ℝ
      (fun θ' => Work.FTS.Galerkin.slice
        (Work.FTS.RegExportIface.psiR α Φs E (Work.FTS.FinalV2.tauExt g)) τ z θ') θ :=
    vz7_differentiableAt_tslice hsm hz hθ hθ2
  -- the closed form of `Vz7` on the open quadrant
  have hcf : Work.FTS.RegExportIface.Vz7 (Work.FTS.Regularity.pExp α)
        (Work.FTS.Final.maxMu (Work.FTS.Regularity.pExp α)
          (Work.FTS.Nonlin.PsiCan Φs E g) g)
        (Work.FTS.FinalV2.gS α (Work.FTS.FinalV2.tauExt g))
        (Work.FTS.RegExportIface.psiR α Φs E (Work.FTS.FinalV2.tauExt g)) z θ τ
      = (1 - Work.FTS.Final.maxMu (Work.FTS.Regularity.pExp α)
            (Work.FTS.Nonlin.PsiCan Φs E g) g τ)
        + 2 * Work.FTS.Regularity.pExp α *
          Work.Construction.Vop (Work.FTS.Galerkin.slice
            (Work.FTS.RegExportIface.psiR α Φs E (Work.FTS.FinalV2.tauExt g)) τ) z θ :=
    vz7_eq_of_vop (αG := Work.FTS.Regularity.pExp α) hαG hθ hθ2 hd
  rw [hcf]
  linarith [hVop z θ τ hz hθ hθ2 hτ]

end Work.FTS_RegExport.RXVP3
end
end
