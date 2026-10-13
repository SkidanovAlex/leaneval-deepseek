import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS_RegExport.RXT0.RXJets.slabDefs
import Submission.Work.FTS.PhiStar.CoreAux.fields_smooth
import Submission.Work.FTS_RegExport.RXT.velVanish2Aux
import Submission.Work.FTS_RegExport.RXT.SysAux.pertSlot_contDiffOn
import Submission.Work.FTS.PhiStar.StarPkgo2Aux.FieldRegularity

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS_RegExport.RXT0.RXJets.starSlots` — the star slots are continuous on the slab

The three transport slots of the *star* residual `Φ̃_* = v2_PhiStar α Φs` — namely
`𝒱(Φ̃_*)`, `ℛ(Φ̃_*)` and `𝒰(Φ̃_*)/sin 2θ` — are `C^∞` on the open quadrant `Q0`, so all their
mixed jets of order `≤ 2` are jointly continuous there.  Since the slab
`slb S = (0,∞) × (0,π/2) × [0,S]` only carries an extra `τ`-coordinate (the functions do not
depend on `p.2.2`) and projects into `Q0`, the jets are jointly continuous on the slab.

The smoothness inputs are the `StarPkgo2`-witness smoothness `hStar.smooth : SmoothOpen Φs`
together with

* `Work.FTS.PhiStar.CoreAux.smoothOpen_PhiTs` for `Φ̃_*`,
* `Work.FTS.NonlinRows.Rl1.smoothOpen_Vop_open` / `…smoothOpen_Uop_open` and
  `Work.FTS.NonlinRows.smoothOpen_Rop` for the three operators,
* `Work.FTS.PhiStar.StarPkgo2Aux.smoothOpen_div_sin2` for the division by `sin 2θ`,

and the jet continuity from `Work.FTS.StrongEps.continuousOn_mixed_of_contDiffOn`.
-/

namespace Work.FTS_RegExport.RXT0.RXJets

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-- **Slab lift.**  A mixed jet `D_z^kD_θ^l` of a function which is continuous on the open
quadrant is continuous on the slab `(0,∞) × (0,π/2) × [0,S]`: the slab maps into `Q0` under the
projection `p ↦ (p.1, p.2.1)`, and the `τ`-coordinate is not used. -/
theorem slabLift {f : ℝ → ℝ → ℝ} {S : ℝ} {k l : ℕ}
    (h : ContinuousOn (Function.uncurry (Work.Spaces.mixed k l f))
      Work.FTS.EllipticEst.Q0) :
    ContinuousOn (fun p : ℝ × ℝ × ℝ => Work.Spaces.mixed k l f p.1 p.2.1) (slb S) :=
  h.comp ((continuous_fst.prodMk (continuous_fst.comp continuous_snd)).continuousOn)
    (fun p hp => by
      obtain ⟨h1, h2, h3, -, -⟩ := mem_slb.mp hp
      exact Work.FTS.EllipticEst.mem_Q0.mpr ⟨h1, h2, h3⟩)

theorem starSlots {α Cs : ℝ} {Φs : Work.FTS.Galerkin.Fn} (hα : 0 < α) (hα13 : α ≤ 1 / 3)
    (hStar : Work.FTS.Final.StarPkgo2 (Work.FTS.Regularity.pExp α) Cs Φs)
    (S : ℝ) (k l : ℕ) (hkl : k + l ≤ 2) :
    ContinuousOn (fun p : ℝ × ℝ × ℝ => Work.Spaces.mixed k l
        (fun z θ => Work.Construction.Vop (Work.FTS_RegExport.RXT.v2_PhiStar α Φs) z θ)
        p.1 p.2.1) (Work.FTS_RegExport.RXT0.RXJets.slb S) ∧
      ContinuousOn (fun p : ℝ × ℝ × ℝ => Work.Spaces.mixed k l
        (fun z θ => Work.Construction.Rop (Work.FTS.Regularity.pExp α)
          (Work.FTS_RegExport.RXT.v2_PhiStar α Φs) z θ) p.1 p.2.1)
        (Work.FTS_RegExport.RXT0.RXJets.slb S) ∧
      ContinuousOn (fun p : ℝ × ℝ × ℝ => Work.Spaces.mixed k l
        (fun z θ => Work.Construction.Uop (Work.FTS.Regularity.pExp α)
          (Work.FTS_RegExport.RXT.v2_PhiStar α Φs) z θ / Real.sin (2 * θ)) p.1 p.2.1)
        (Work.FTS_RegExport.RXT0.RXJets.slb S) := by
  have hβ : 0 < Work.FTS.Regularity.pExp α := Work.FTS.Regularity.pExp_pos hα
  have hβ1 : Work.FTS.Regularity.pExp α ≤ 1 := Work.FTS.Regularity.pExp_le_one hα13
  have hsm : Work.FTS.EllipticEst.SmoothOpen Φs := hStar.smooth
  -- the star residual is `C^∞` on the open quadrant
  have hPs : Work.FTS.EllipticEst.SmoothOpen (Work.FTS.VocabO2.PhiTs (Work.FTS.Regularity.pExp α) Φs) :=
    (Work.FTS.PhiStar.CoreAux.smoothOpen_PhiTs (α := Work.FTS.Regularity.pExp α) (Φs := Φs)
      hβ hβ1 hsm).1
  -- the three slots are `C^∞` on the open quadrant
  have hV : Work.FTS.EllipticEst.SmoothOpen
      (Work.Construction.Vop (Work.FTS.VocabO2.PhiTs (Work.FTS.Regularity.pExp α) Φs)) :=
    Work.FTS.NonlinRows.Rl1.smoothOpen_Vop_open hPs
  have hR : Work.FTS.EllipticEst.SmoothOpen
      (Work.Construction.Rop (Work.FTS.Regularity.pExp α)
        (Work.FTS.VocabO2.PhiTs (Work.FTS.Regularity.pExp α) Φs)) :=
    Work.FTS.NonlinRows.smoothOpen_Rop hPs
  have hU : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => Work.Construction.Uop (Work.FTS.Regularity.pExp α)
        (Work.FTS.VocabO2.PhiTs (Work.FTS.Regularity.pExp α) Φs) z θ / Real.sin (2 * θ)) :=
    Work.FTS.PhiStar.StarPkgo2Aux.smoothOpen_div_sin2
      (Work.FTS.NonlinRows.Rl1.smoothOpen_Uop_open (α := Work.FTS.Regularity.pExp α) hPs)
  -- their mixed jets of order `≤ 2` are continuous on the open quadrant
  have hVc : ContinuousOn (Function.uncurry (Work.Spaces.mixed k l
      (Work.Construction.Vop (Work.FTS.VocabO2.PhiTs (Work.FTS.Regularity.pExp α) Φs))))
      Work.FTS.EllipticEst.Q0 :=
    Work.FTS.StrongEps.continuousOn_mixed_of_contDiffOn (k := 3) (j := k) (i := l)
      (hV.forall 3) (by omega)
  have hRc : ContinuousOn (Function.uncurry (Work.Spaces.mixed k l
      (Work.Construction.Rop (Work.FTS.Regularity.pExp α)
        (Work.FTS.VocabO2.PhiTs (Work.FTS.Regularity.pExp α) Φs))))
      Work.FTS.EllipticEst.Q0 :=
    Work.FTS.StrongEps.continuousOn_mixed_of_contDiffOn (k := 3) (j := k) (i := l)
      (hR.forall 3) (by omega)
  have hUc : ContinuousOn (Function.uncurry (Work.Spaces.mixed k l
      (fun z θ => Work.Construction.Uop (Work.FTS.Regularity.pExp α)
        (Work.FTS.VocabO2.PhiTs (Work.FTS.Regularity.pExp α) Φs) z θ / Real.sin (2 * θ))))
      Work.FTS.EllipticEst.Q0 :=
    Work.FTS.StrongEps.continuousOn_mixed_of_contDiffOn (k := 3) (j := k) (i := l)
      (hU.forall 3) (by omega)
  exact ⟨slabLift hVc, slabLift hRc, slabLift hUc⟩

end Work.FTS_RegExport.RXT0.RXJets
