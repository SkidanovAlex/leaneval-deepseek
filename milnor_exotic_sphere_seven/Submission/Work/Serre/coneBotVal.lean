import Mathlib
import Submission.Work.Serre.coneBotSetup

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

namespace Work.Serre

/-- **The homeomorphism of the bottom parts of the two cone-fibres agrees with the restriction of the
map of mapping cylinders induced by the pullback square of the path.** -/
theorem coneBotVal {X B : Type} [TopologicalSpace X] [TopologicalSpace B]
    (q : C(X, B)) (p : C(unitInterval, B)) (t : unitInterval)
    (a : ↥(Work.Serre.coneFibreBot (Work.StemsB.pullbackSnd q p) t)) :
    ((Work.Serre.coneBotHomeo q p t a : ↥(Work.Serre.coneFibreBot q (p t))) : Work.Serre.cyl q)
      = (Work.Serre.pathPsiFibre q p t
          (a : ↥(Work.Serre.coneFibre (Work.StemsB.pullbackSnd q p) t)) : Work.Serre.cyl q) := by
  classical
  -- The bottom part of `coneFibre (pullbackSnd q p) t` is (the image of) the bottom copy of the
  -- mapping cylinder `cyl (pullbackSnd q p)`; pick the point `x` of the source with
  -- `cylIncl (pullbackSnd q p) x = a`.
  obtain ⟨x, hx⟩ := a.2
  -- The two explicit homeomorphisms used in `coneBotHomeo`, with their defining properties.
  have he' : ∀ y : X, ((Classical.choose (cylHomeoExplicit q)) y : cyl q) = cylIncl q y :=
    Classical.choose_spec (cylHomeoExplicit q)
  have he : ∀ y : Work.StemsB.Pullback q p,
      ((Classical.choose (cylHomeoExplicit (Work.StemsB.pullbackSnd q p))) y :
        cyl (Work.StemsB.pullbackSnd q p)) = cylIncl (Work.StemsB.pullbackSnd q p) y :=
    Classical.choose_spec (cylHomeoExplicit (Work.StemsB.pullbackSnd q p))
  -- The left-hand side, computed along the chain of homeomorphisms defining `coneBotHomeo`.
  have hL : ((coneBotHomeo q p t a : ↥(coneFibreBot q (p t))) : cyl q)
      = cylIncl q x.1.1 := by
    have hsub : ((coneBotSwap (Work.StemsB.pullbackSnd q p) t).symm a :
        ↥(Set.range (cylIncl (Work.StemsB.pullbackSnd q p)))) = ⟨a.1.1, a.2⟩ := rfl
    have hxe : (Classical.choose (cylHomeoExplicit (Work.StemsB.pullbackSnd q p))) x
        = ⟨a.1.1, a.2⟩ := Subtype.ext ((he x).trans hx)
    have hzx : (Classical.choose (cylHomeoExplicit (Work.StemsB.pullbackSnd q p))).symm
        ⟨a.1.1, a.2⟩ = x := by rw [← hxe, Homeomorph.symm_apply_apply]
    simp only [coneBotHomeo, Homeomorph.trans_apply, coneBotSwap_val,
      rangeBotHomeoFibre_val, rangeBotHomeoFibre_symm_val, fibrePullbackHomeo_val, he']
    rw [hsub, hzx]
  -- The right-hand side: `pathPsiFibre` is the restriction of `pathPsi`, which is `cylIncl` on the
  -- bottom copies.
  have hR : (Work.Serre.pathPsiFibre q p t
          (a : ↥(Work.Serre.coneFibre (Work.StemsB.pullbackSnd q p) t)) : Work.Serre.cyl q)
      = cylIncl q x.1.1 := by
    rw [show (Work.Serre.pathPsiFibre q p t
        (a : ↥(Work.Serre.coneFibre (Work.StemsB.pullbackSnd q p) t)) : Work.Serre.cyl q)
      = Work.Serre.pathPsi q p (a.1.1) from rfl]
    rw [← hx, Work.Serre.pathPsi_cylIncl]
    rfl
  rw [hL, hR]

end Work.Serre
