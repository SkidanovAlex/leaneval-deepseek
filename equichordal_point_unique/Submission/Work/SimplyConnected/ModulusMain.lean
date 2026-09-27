import Submission.UnifDeps
import Submission.Work.SimplyConnected.ModulusDefs
import Submission.Commons.Topology.Covering.section_of_monodromy_eq_self_weak

/-!
# The multivalued modulus of a Green function on a simply connected surface

This module carries out the step of the hyperbolic case of uniformization in which the **simple
connectivity of `X`** is used.

`Work.SC.ModulusDefs` materialises the multivalued function `Φ = exp (-(E + iE*))` attached to a
Green function `E` with pole `z₀` (see `Submission.HasGreenFunctionE`) as a covering space
`Work.SC.branchProj : Work.SC.ModulusBundle z₀ E → X` whose points are the *branches* of `Φ`
(encoded, over the pole, by their derivatives, `Work.SC.chartDeriv`).

Since `X` is simply connected, the monodromy of every loop is trivial, so
`Commons.Topology.Covering.section_of_monodromy_eq_self_weak` produces a global continuous section
`σ` of the bundle; the value coordinate `Φ x := (σ x).₂` is then the global branch of the modulus:
it is holomorphic because σ is locally contained in the graph of a local branch (the graphs are
open by definition of the topology of the bundle), and its modulus is `exp (-E)` off the pole by
the very definition of a branch.

The covering-theory input is isolated as an explicit hypothesis `hcov` in the theorem below, and is
provided by `Work.SC.isCoveringMap_branchProj`.
-/

open LeanEval.Geometry
open scoped Manifold ContDiff Topology

set_option linter.unusedSectionVars false

noncomputable section

open Filter Set
open Classical

namespace Work.SC

variable {X : Type*} [TopologicalSpace X] [T2Space X] [ConnectedSpace X]
  [SecondCountableTopology X] [ChartedSpace ℂ X]
  [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]

/-- **A branch realisation of a point of the bundle.**  Every point `p` of the modulus bundle lies
on the graph of some local branch: this is precisely the definition of the bundle. -/
theorem exists_isModulusBranch_of_mem_branchSet {z₀ : X} {E : X → ℝ} {p : X × ℂ × ℂ}
    (hp : p ∈ branchSet z₀ E) :
    ∃ (U : Set X) (Φ : X → ℂ), IsModulusBranch z₀ E U Φ ∧ p ∈ branchGraph U Φ := hp

/-- **The global branch of the modulus, from the triviality of the monodromy.**  If the modulus
bundle is a covering space of `X` and is non-empty, then, `X` being simply connected, it has a
global continuous section, and the value coordinate of that section is a global holomorphic
function which does not vanish off the pole and has modulus `exp (-E)` there. -/
theorem exists_holomorphic_modulus_of_isCoveringMap [SimplyConnectedSpace X] {z₀ : X} {E : X → ℝ}
    (hcov : @IsCoveringMap (ModulusBundle z₀ E) X (modulusBundleTopology z₀ E) _
      (branchProj z₀ E))
    (hne : (branchSet z₀ E).Nonempty) :
    ∃ Φ : X → ℂ, Submission.HolomorphicOnX Φ Set.univ ∧
      (∀ x : X, x ≠ z₀ → Φ x ≠ 0) ∧
      (∀ x : X, x ≠ z₀ → ‖Φ x‖ = Real.exp (-(E x))) := by
  classical
  letI : TopologicalSpace (X × ℂ × ℂ) := branchTopology z₀ E
  letI : TopologicalSpace (ModulusBundle z₀ E) := modulusBundleTopology z₀ E
  haveI : LocallyPathConnectedSpace X := ChartedSpace.locallyPathConnectedSpace (H := ℂ) (M := X)
  obtain ⟨e₀, he₀⟩ := hne
  have hmono : ∀ γ : FundamentalGroup X (branchProj z₀ E ⟨e₀, he₀⟩),
      hcov.monodromy γ ⟨⟨e₀, he₀⟩, rfl⟩ = ⟨⟨e₀, he₀⟩, rfl⟩ := by
    intro γ
    haveI : Subsingleton (FundamentalGroup X (branchProj z₀ E ⟨e₀, he₀⟩)) := inferInstance
    rw [Subsingleton.elim γ 1]
    exact congrFun hcov.monodromy_refl _
  obtain ⟨σ, hσ0, hσp⟩ :=
    Commons.Topology.Covering.section_of_monodromy_eq_self_weak hcov ⟨e₀, he₀⟩ hmono
  set Φ : X → ℂ := fun x => ((σ x : ModulusBundle z₀ E).1).2.1 with hΦdef
  have hσval : ∀ x : X, (σ x : ModulusBundle z₀ E).1.1 = x := fun x => hσp x
  -- the section is locally contained in the graph of a local branch, whence holomorphy of `Φ`
  have hloc : ∀ x : X, Submission.HolomorphicOnXAt Φ x := by
    intro x
    obtain ⟨U, ΦU, hbr, hmem⟩ := exists_isModulusBranch_of_mem_branchSet (σ x).2
    have hxU : x ∈ U := by rw [← hσval x]; exact hmem.1
    let G : Set (ModulusBundle z₀ E) := Subtype.val ⁻¹' (branchGraph U ΦU)
    have hGmem : (σ x : ModulusBundle z₀ E) ∈ G := hmem
    have hGopen : IsOpen G := by
      have hgen : branchGraph U ΦU ∈ branchFamily z₀ E := ⟨U, ΦU, hbr, rfl⟩
      exact (TopologicalSpace.isOpen_generateFrom_of_mem hgen).preimage continuous_subtype_val
    have hev : ∀ᶠ y in 𝓝 x, ΦU y = Φ y := by
      filter_upwards [((σ.continuous.continuousAt (x := x)).eventually (hGopen.mem_nhds hGmem))]
        with y hy
      have hy1 : (σ y : ModulusBundle z₀ E).1.1 = y := hσval y
      show ΦU y = ((σ y : ModulusBundle z₀ E).1).2.1
      rw [hy.2.1, hσval y]
    refine (hbr.holomorphic x hxU).congr ?_
    have hcx : (chartAt ℂ x) x ∈ (chartAt ℂ x).target :=
      (chartAt ℂ x).map_source (mem_chart_source ℂ x)
    have hsymm : (chartAt ℂ x).symm ((chartAt ℂ x) x) = x :=
      (chartAt ℂ x).left_inv (mem_chart_source ℂ x)
    have htend : Filter.Tendsto (chartAt ℂ x).symm (𝓝 ((chartAt ℂ x) x)) (𝓝 x) := by
      have h' : Filter.Tendsto (chartAt ℂ x).symm (𝓝 ((chartAt ℂ x) x))
          (𝓝 ((chartAt ℂ x).symm ((chartAt ℂ x) x))) :=
        (chartAt ℂ x).continuousAt_symm hcx
      rw [hsymm] at h'
      exact h'
    exact htend.eventually hev
  refine ⟨Φ, fun x _ => hloc x, ?_, ?_⟩
  · intro x hx
    obtain ⟨U, ΦU, hbr, hmem⟩ := exists_isModulusBranch_of_mem_branchSet (σ x).2
    have hxU : x ∈ U := by rw [← hσval x]; exact hmem.1
    have : Φ x = ΦU x := by
      show ((σ x : ModulusBundle z₀ E).1).2.1 = ΦU x
      rw [hmem.2.1, hσval x]
    rw [this]
    exact hbr.ne_zero x hxU hx
  · intro x hx
    obtain ⟨U, ΦU, hbr, hmem⟩ := exists_isModulusBranch_of_mem_branchSet (σ x).2
    have hxU : x ∈ U := by rw [← hσval x]; exact hmem.1
    have : Φ x = ΦU x := by
      show ((σ x : ModulusBundle z₀ E).1).2.1 = ΦU x
      rw [hmem.2.1, hσval x]
    rw [this]
    exact hbr.norm_eq x hxU hx

end Work.SC
