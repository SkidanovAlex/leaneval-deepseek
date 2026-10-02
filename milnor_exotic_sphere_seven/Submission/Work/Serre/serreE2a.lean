import Submission.Work.Serre.Engine
import Submission.Work.StemsB.exists_lift_rel

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# E2(a): the relative cube HLP of a Serre fibration

`Work.Serre.SerreE2a` is the gluing form of `Work.StemsB.HasHLPRel` (proved in that directory by
`Work.StemsB.exists_lift_rel`): the prescribed lift is given on the whole *hat*
`Iⁿ × 0 ∪ ∂Iⁿ × I` of the cube-cylinder rather than on its two pieces separately.
-/

open scoped Topology unitInterval

namespace Work.Serre

noncomputable section

/-- The point `(x, 0)` of the hat. -/
def hatBottom {n : ℕ} (x : Work.Stems.Cubical.IC n) : ↥(hatSet n) :=
  ⟨(x, 0), Or.inl rfl⟩

/-- The point `(y, t)` of the hat, `y ∈ ∂Iⁿ`. -/
def hatLateral {n : ℕ} (y : Work.StemsB.CubeBdry n) (t : unitInterval) : ↥(hatSet n) :=
  ⟨(y.1, t), Or.inr y.2⟩

theorem hatBottom_continuous (n : ℕ) : Continuous (hatBottom (n := n)) := by
  refine Continuous.subtype_mk ?_ _; fun_prop

theorem hatLateral_continuous (n : ℕ) : Continuous (fun y : Work.StemsB.CubeBdry n × unitInterval =>
    hatLateral y.1 y.2) := by
  refine Continuous.subtype_mk ?_ _; fun_prop

/-- **E2(a)**, by gluing `Work.StemsB.exists_lift_rel`. -/
theorem serreE2a : SerreE2a := by
  intro E B _ _ p n hp H g hg
  let f : C(Work.Stems.Cubical.IC n, E) :=
    g.comp ⟨hatBottom, hatBottom_continuous n⟩
  let gl : C(Work.StemsB.CubeBdry n × unitInterval, E) :=
    g.comp ⟨fun y => hatLateral y.1 y.2, hatLateral_continuous n⟩
  have hf : p.comp f = H.comp (Work.StemsB.zeroIncl n) := by
    ext x
    exact congrFun (congrArg DFunLike.coe hg) (hatBottom x)
  have hgl : p.comp gl = H.comp (Work.StemsB.bdryIncl n) := by
    ext y
    exact congrFun (congrArg DFunLike.coe hg) (hatLateral y.1 y.2)
  have hgl0 : ∀ x : Work.StemsB.CubeBdry n, gl (x, 0) = f x.1 := fun x =>
    congrArg g (Subtype.ext rfl)
  obtain ⟨G, hGp, hG0, hGl⟩ := Work.StemsB.exists_lift_rel p hp n H f hf gl hgl hgl0
  refine ⟨G, hGp, fun x => ?_⟩
  obtain ⟨⟨v, t⟩, hx⟩ := x
  rcases hx with hx | hx
  · have hx' : (⟨(v, t), Or.inl hx⟩ : ↥(hatSet n)) = hatBottom v :=
      Subtype.ext (Prod.ext rfl hx)
    rw [hx']
    change G ((v, (0 : unitInterval))) = g (hatBottom v)
    exact hG0 v
  · exact hGl ⟨v, hx⟩ t

end

end Work.Serre
