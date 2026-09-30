import Mathlib
import Submission.Work.EMFG.commonPiOneKill

/-!
# Killing a common `π₁`-kernel of two maps, simultaneously — the path connected version

`Work.EMFG.commonPiOneKill` attaches, for every element of the common kernel of the two
`π₁`-surjections `π₁(g)` and `π₁(h)`, a `2`-cell to `Γ` along the representing loop
`killFamily 0 Γ γ₀ α`, and extends both `g` and `h` over the attached cells; the two extensions are
`π₁`-bijections.  That construction produces the space `attachCells 0 Γ ι f`, which — `Γ` being
path connected — is again path connected (`Work.Serre.CWModel.pathConnectedSpace_attachCells`).
This file records that extra connectivity, which the consumers of the two-map killing step need.

The proof is the construction of `commonPiOneKill` carried out with the explicit model
`Y := attachCells 0 Γ ι f`, so that the path connectedness of `Y` is visible.
-/

open scoped Topology Topology.Homotopy unitInterval
open Work.RatHurewicz Work.Serre.CWModel

namespace Work.EMFG

noncomputable section

theorem commonPiOneKillConnected {Γ Z P : Type} [TopologicalSpace Γ] [TopologicalSpace Z] [TopologicalSpace P] [PathConnectedSpace Γ]
    (γ₀ : Γ) (g : C(Γ, Z)) (h : C(Γ, P))
    (hsurj_g : Function.Surjective (Work.Serre.piMapN g 1 γ₀))
    (hsurj_h : Function.Surjective (Work.Serre.piMapN h 1 γ₀))
    (hker : ∀ a : HomotopyGroup (Fin 1) Γ γ₀,
      Work.Serre.piMapN g 1 γ₀ a = 1 ↔ Work.Serre.piMapN h 1 γ₀ a = 1) :
    ∃ (Y : Type) (_ : TopologicalSpace Y) (y₀ : Y) (f : C(Y, Z)) (g' : C(Y, P)),
      PathConnectedSpace Y ∧ Function.Bijective (Work.Serre.piMapN f 1 y₀)
        ∧ Function.Bijective (Work.Serre.piMapN g' 1 y₀) := by
  classical
  -- the index type: the common kernel of `π₁(g)` and `π₁(h)`
  let ι := {α : HomotopyGroup (Fin 1) Γ γ₀ // Work.Serre.piMapN g 1 γ₀ α = 1}
  let f : ι → C(cellSphere 0, Γ) := fun k => killFamily 0 Γ γ₀ k.1
  -- the attaching maps become null-homotopic after composition with `g` (resp. `h`)
  have hnull_g : ∀ k : ι, (g.comp (f k)).Homotopic (ContinuousMap.const (cellSphere 0) (g γ₀)) :=
    fun k => killFamily_comp_homotopic_const γ₀ g k.1 k.2
  have hnull_h : ∀ k : ι, (h.comp (f k)).Homotopic (ContinuousMap.const (cellSphere 0) (h γ₀)) :=
    fun k => killFamily_comp_homotopic_const γ₀ h k.1 ((hker k.1).mp k.2)
  -- the attached classes die in `π₁` of the attached space
  have hkill_g : ∀ α : HomotopyGroup (Fin 1) Γ γ₀, Work.Serre.piMapN g 1 γ₀ α = 1 →
      Work.Serre.piMapN (attachIncl 0 Γ ι f) 1 γ₀ α = 1 :=
    fun α hα => Work.Serre.CWModel.killSub (n := 0) Γ γ₀ ι (fun k : ι => k.1) ⟨α, hα⟩
  have hkill_h : ∀ α : HomotopyGroup (Fin 1) Γ γ₀, Work.Serre.piMapN h 1 γ₀ α = 1 →
      Work.Serre.piMapN (attachIncl 0 Γ ι f) 1 γ₀ α = 1 :=
    fun α hα => hkill_g α ((hker α).mpr hα)
  obtain ⟨G, hG, hbij_g⟩ := piOne_bijective_attachG γ₀ f g hnull_g hsurj_g hkill_g
  obtain ⟨G', hG', hbij_h⟩ := piOne_bijective_attachG γ₀ f h hnull_h hsurj_h hkill_h
  refine ⟨attachCells 0 Γ ι f, inferInstance, attachIncl 0 Γ ι f γ₀,
    attachG 0 Γ ι f g G hG, attachG 0 Γ ι f h G' hG', ?_, hbij_g, hbij_h⟩
  exact Work.Serre.CWModel.pathConnectedSpace_attachCells 0 Γ ι f

end

end Work.EMFG
