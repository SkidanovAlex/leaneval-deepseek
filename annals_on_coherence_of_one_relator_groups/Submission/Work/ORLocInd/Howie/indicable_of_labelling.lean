/-
# A presentation with an indicable labelling has an indicable vertex group

Howie's *Case 1* of the proof of Brodskii's theorem (`A short proof of a theorem of Brodskii`,
Publ. Mat. 44 (2000), Theorem 3.1) starts from a *labelling* `θ` of the graph `Γ` of a groupoid
presentation `⟨Γ | R⟩` which *vanishes on the relators*: the level of every relator is `0`, so
every relator lifts to a *closed* path of the cyclic cover of `Γ` defined by `θ`.

The labelling induces a homomorphism

`pathSumHom θ hθ x : F(Γ)_x →* Multiplicative ℤ`

(`Submission/Work/ORLocInd/Howie/PathSumHom.lean`) whose kernel contains the relators
(`relatorNormalClosure_le_ker_pathSumHom`), so that it descends to the presented vertex group

`φ : π₁(⟨Γ | R⟩, x) →* Multiplicative ℤ`.

If moreover some closed path `p` at `x` has non-zero level, then `φ` is non-trivial; since the
non-zero subgroups of `ℤ` are exactly the infinite cyclic ones, a non-trivial homomorphism to `ℤ`
produces a *surjective* one (`exists_surjective_of_ne_one`).  This is the statement proved here:
the existence of a closed path of non-zero level is exactly the condition under which the vertex
group of the presentation is *indicable*.

Together with the converse direction (a surjection onto `ℤ` yields a labelling with a non-zero
closed path — the labelling `labOf` of `Howie/exists_labelling.lean`) this identifies Howie's
hypothesis "the cyclic cover is non-trivial" with indicability of the vertex group.
-/
import Mathlib
import Submission.Work.ORLocInd.Howie.Defs2
import Submission.Work.ORLocInd.Howie.exists_labelling
import Submission.Work.ORLocInd.Howie.LabellingAux
import Submission.Work.ORLocInd.Howie.PathSumHom
import Submission.Work.ORLocInd.Howie.relatorNormalClosure_le_ker_pathSumHom
import Submission.Work.ORLocInd.Howie.exists_surjective_of_ne_one

namespace Work.ORLocInd.Howie

theorem indicable_of_labelling {V : Type*} [Quiver V] [Quiver.HasInvolutiveReverse V]
    (P : Work.ORLocInd.Howie.Presentation V) (L : Work.ORLocInd.Howie.Labelling V)
    (hL : Work.ORLocInd.Howie.VanishOnRelators L P) {x : V} (p : Quiver.Path x x)
    (hp : Work.ORLocInd.Howie.pathSum L.toFun p ≠ 0) :
    ∃ φ : P.vertexGroup x →* Multiplicative ℤ, Function.Surjective φ := by
  classical
  -- the homomorphism `F(Γ)_x →* ℤ` given by the level of a reduced closed path
  let ψ : VertexGroup x →* Multiplicative ℤ := pathSumHom L.toFun L.isBalanced x
  -- the labelling vanishes on the relators, hence `ψ` descends to the presented vertex group
  have hker : P.relatorNormalClosure x ≤ ψ.ker := relatorNormalClosure_le_ker_pathSumHom P L hL x
  let φ : P.vertexGroup x →* Multiplicative ℤ :=
    QuotientGroup.lift (P.relatorNormalClosure x) ψ hker
  -- `φ` is non-trivial: the reduced form of `p` has level `pathSum L p ≠ 0`
  have hne : ∃ g : P.vertexGroup x, φ g ≠ 1 := by
    have hφval : ∀ g : VertexGroup x, φ (QuotientGroup.mk g) =
        Multiplicative.ofAdd (pathSum L.toFun g.1) := by
      intro g
      change (QuotientGroup.lift (P.relatorNormalClosure x) ψ hker) (QuotientGroup.mk g) = _
      rw [QuotientGroup.lift_mk]
      rfl
    let g₀ : VertexGroup x := ⟨red p, isReduced_red p⟩
    have hp' : pathSum L.toFun (red p) ≠ 0 := by
      rwa [← pathSum_of_reducesTo L.toFun L.isBalanced (reducesTo_red p)]
    refine ⟨QuotientGroup.mk g₀, ?_⟩
    rw [hφval g₀]
    intro h1
    have h2 : pathSum L.toFun (red p) = 0 := by
      have h3 := congrArg Multiplicative.toAdd h1
      dsimp only [g₀] at h3
      simpa using h3
    exact hp' h2
  -- a non-trivial homomorphism to the infinite cyclic group can be corrected to a surjection
  exact exists_surjective_of_ne_one φ hne

end Work.ORLocInd.Howie
