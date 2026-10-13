import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.RegExportIface.RXT.Leaves
import Submission.Work.FTS.FinalV2.Defs
import Submission.Work.FTS_RegExport.RXT.CoeffJetsDefs
import Submission.Work.FTS_RegExport.RXT.Sys.CoeffBnd
import Submission.Work.FTS_RegExport.RXT.Sys.CoeffCont
import Submission.Work.FTS_RegExport.RXT.coeff_C2
import Submission.Work.FTS_RegExport.RXT.velVanish2Aux
import Submission.Work.FTS_RegExport.RXT.SysAux.Theta_ops
import Submission.Work.FTS_RegExport.RXT.SysAux.bR_decomp
import Submission.Work.FTS_RegExport.RXT.SysAux.pertSlot_contDiffOn
import Submission.Work.FTS_RegExport.RXT0.slotJetsJointCont
import Submission.Work.FTS_RegExport.RXT.Sys.pert_tilde_contDiffOn
import Submission.Work.FTS_RegExport.RXT.Sys.GdotCore
import Submission.Work.FTS_RegExport.RXT.Sys.JetCalc.OpFacts
import Submission.Work.FTS_RegExport.RXT0.RXJets.CJDefs
import Submission.Work.FTS_RegExport.RXT0.RXJets.coeffVR
import Submission.Work.FTS_RegExport.RXT0.RXJets.coeffbR
import Submission.Work.FTS_RegExport.RXT0.RXJets.coeffcR

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_RegExport.RXT0.RXJets

-- *** The mixed jets of the three transport coefficients are jointly continuous on the slab. ***
--
-- Taking as hypotheses (i) the (z,τ)-joint continuity of the `D_z`-jets of `L₁₂(F_τ)` and
-- `𝔽K(F_τ)` of the profile `F_τ = F_* + slice (GR α g) τ` (`hL12`), and (ii) the joint continuity
-- of the order-`≤ 2` mixed jets of the three slots of the *perturbation* residual
-- `PhiTil (pExp α) (slice g τ) (E (slice g τ))` (`hSlot`), the order-`≤ 2` mixed jets of the
-- three transport coefficients `VR = Vz7 (pExp α) (μR α Φs E g) (GR α g) (ΦR α Φs E g)`,
-- `bR = Vθ7 (pExp α) (ΦR α Φs E g)/sin 2θ`, `cR = cs7 ...` are jointly continuous on the slab
-- `(0,∞) × (0,π/2) × [0,S]`, for every `S > 0`.
--
-- Route (all the identities are on disk, `sorry`-free).
--  * Closed forms (`RegExportIface.Defs`): `Vz7 = (1−μ) + L₁₂(F)·c2m + 2αG·Vop Φ̃`,
--    `Vθ7 = 2·Uop Φ`, `cs7 = (1+μ) − L₁₂(F)/αG + sin²θ·𝔽K(F) − 2·Rop Φ̃`, with
--    `F = Ftau αG (GR α g) τ`, `Φ̃ = phiTil αG (GR α g) (ΦR α Φs E g) τ`; on the quadrant
--    `Φ̃ = v2_PhiT = v2_PhiStar + v2_PhiPert` (`velVanish2Aux.v2_phiTil_split`), and the slots are
--    additive there (`velVanish2Aux.v2_{rop,vop,uop_div}_add_at`, `SysAux.pertSlot_contDiffOn`);
--    the star part is a fixed smooth function of `(z,θ)`
--    (`Work.FTS.PhiStar.CoreAux.fields_smooth` from `hStar.smooth`).
--  * The `Θ`-part of `bR` is in closed form: `2·Uop(Θ β F)/sin 2θ = -(3/(2β))·L₁₂(F) + (1/2)·𝔽K(F)`
--    (`SysAux.Theta_ops`; `SysAux.bR_decomp` shows the split of `bR` and the theorem
--    `SysAux.L12FK_of_DynOK` in that same module gives the regularity of `L₁₂(F)`, `𝔽K(F)`).
--  * Algebraic assembly: for each of the 6 index pairs `(k,l)`, `k + l ≤ 2`, expand the
--    coefficient's mixed jet with the linearity of `mixed` on sums
--    (`E2pkg.mixed_add_of_contDiffOn`, `Sys.GdotCore.mixed_add_pt`,
--    `FTS.StrongEps.mixed_const_mul`), the Leibniz rule for products
--    (`Sys.JetCalc.mixed_mul_fin` / the `C²` instance `Sys.GdotAux.mixed_mul_le2`), the trivial
--    jets of the pure `θ`-functions `c2m`, `sin²`, and the `θ`-independence of the radial pieces
--    (`mixed j 0 f = DzIter j f`, `Work.Spaces.mixed_zero_right/left`), converting `hL12`'s
--    `DzIter j (L₁₂(F_τ)) z 0` into `mixed j 0 (fun z θ => L₁₂(F_τ) z) z θ` and the `l ≥ 1`
--    slots into `0`.
--  * `hSlot`/the star part give the `Vop`/`Rop`/`Uop/sin 2θ`-slot jets; the products with the
--    `θ`-factors and the sums are then jointly continuous by the continuity of each factor.
-- The `τ = 0` endpoint is included.

theorem coeffJetsJointCont {α C₀ Ce Cs : ℝ} {Φs : Work.FTS.Galerkin.Fn}
    {E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn} {g : Work.FTS.Galerkin.Fam}
    (hα : 0 < α) (hα13 : α ≤ 1 / 3)
    (hEll : ∀ u : Work.FTS.Galerkin.Fn, Work.FTS.ClassC.ClassC (Work.FTS.Regularity.pExp α) u →
      Work.FTS.Final.EllPkgGo (Work.FTS.Regularity.pExp α) Ce u (E u) ∧
        Work.FTS.ClassC.EllPkgK (Work.FTS.Regularity.pExp α) 6 Ce u (E u))
    (hEL3 : Work.FTS.FinalV2.EllLimOK3 (Work.FTS.Regularity.pExp α) E)
    (hStar : Work.FTS.Final.StarPkgo2 (Work.FTS.Regularity.pExp α) Cs Φs)
    (hSol : Work.FTS.FinalV2.Sol (Work.FTS.Regularity.pExp α) Φs E g)
    (hOK : Work.FTS.FinalV2.DynOK' (Work.FTS.Regularity.pExp α) C₀ Φs E g)
    (hμ : Work.FTS.RegExportIface.ClockBd α Φs E g)
    (hL12 : ∀ S > 0, ∀ j : ℕ, j ≤ 2 →
      ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.DzIter j
        (fun z (_ : ℝ) => Work.Construction.L12
          (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
            (Work.FTS.RegExportIface.RXT.GR α g) p.2) z) p.1 0)
        (Set.Ioi (0:ℝ) ×ˢ Set.Icc (0:ℝ) S) ∧
      ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.DzIter j
        (fun z (_ : ℝ) => Work.Construction.FK
          (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
            (Work.FTS.RegExportIface.RXT.GR α g) p.2) z) p.1 0)
        (Set.Ioi (0:ℝ) ×ˢ Set.Icc (0:ℝ) S))
    (hSlot : ∀ S > 0, ∀ j i : ℕ, j + i ≤ 2 →
      (ContinuousOn (fun p : ℝ × ℝ × ℝ => Work.Spaces.mixed j i
        (fun z θ => Work.Construction.Vop
          (Work.Construction.PhiTil (Work.FTS.Regularity.pExp α)
            (Work.FTS.Galerkin.slice g p.2.2) (E (Work.FTS.Galerkin.slice g p.2.2))) z θ)
        p.1 p.2.1)
        (Set.Ioi (0:ℝ) ×ˢ (Set.Ioo (0:ℝ) (Real.pi / 2) ×ˢ Set.Icc (0:ℝ) S))) ∧
      (ContinuousOn (fun p : ℝ × ℝ × ℝ => Work.Spaces.mixed j i
        (fun z θ => Work.Construction.Rop (Work.FTS.Regularity.pExp α)
          (Work.Construction.PhiTil (Work.FTS.Regularity.pExp α)
            (Work.FTS.Galerkin.slice g p.2.2) (E (Work.FTS.Galerkin.slice g p.2.2))) z θ)
        p.1 p.2.1)
        (Set.Ioi (0:ℝ) ×ˢ (Set.Ioo (0:ℝ) (Real.pi / 2) ×ˢ Set.Icc (0:ℝ) S))) ∧
      (ContinuousOn (fun p : ℝ × ℝ × ℝ => Work.Spaces.mixed j i
        (fun z θ => Work.Construction.Uop (Work.FTS.Regularity.pExp α)
          (Work.Construction.PhiTil (Work.FTS.Regularity.pExp α)
            (Work.FTS.Galerkin.slice g p.2.2) (E (Work.FTS.Galerkin.slice g p.2.2))) z θ
          / Real.sin (2 * θ)) p.1 p.2.1)
        (Set.Ioi (0:ℝ) ×ˢ (Set.Ioo (0:ℝ) (Real.pi / 2) ×ˢ Set.Icc (0:ℝ) S)))) :
    ∀ S > 0, ∀ k l : ℕ, k + l ≤ 2 →
      ContinuousOn (fun p : ℝ × ℝ × ℝ => Work.Spaces.mixed k l
        (fun z θ => Work.FTS.RegExportIface.RXT.VR α Φs E g z θ p.2.2) p.1 p.2.1)
        (Set.Ioi (0:ℝ) ×ˢ (Set.Ioo (0:ℝ) (Real.pi / 2) ×ˢ Set.Icc (0:ℝ) S)) ∧
      ContinuousOn (fun p : ℝ × ℝ × ℝ => Work.Spaces.mixed k l
        (fun z θ => Work.FTS.RegExportIface.RXT.bR α Φs E g z θ p.2.2) p.1 p.2.1)
        (Set.Ioi (0:ℝ) ×ˢ (Set.Ioo (0:ℝ) (Real.pi / 2) ×ˢ Set.Icc (0:ℝ) S)) ∧
      ContinuousOn (fun p : ℝ × ℝ × ℝ => Work.Spaces.mixed k l
        (fun z θ => Work.FTS.RegExportIface.RXT.cR α Φs E g z θ p.2.2) p.1 p.2.1)
        (Set.Ioi (0:ℝ) ×ˢ (Set.Ioo (0:ℝ) (Real.pi / 2) ×ˢ Set.Icc (0:ℝ) S)) := by
  intro S hS k l hkl
  have H : Work.FTS_RegExport.RXT0.RXJets.CJHyps α C₀ Ce Cs Φs E g :=
    ⟨hα, hα13, hEll, hEL3, hStar, hSol, hOK, hμ, hL12, hSlot⟩
  exact ⟨Work.FTS_RegExport.RXT0.RXJets.coeffVR H S hS k l hkl,
    Work.FTS_RegExport.RXT0.RXJets.coeffbR H S hS k l hkl,
    Work.FTS_RegExport.RXT0.RXJets.coeffcR H S hS k l hkl⟩

end Work.FTS_RegExport.RXT0.RXJets
