import Mathlib
import Submission.Work.Whitney.TCMDefs
import Submission.Work.Whitney.ballPairMapDefs
import Submission.Work.Whitney.ballPairValSurj
import Submission.Work.Thom.stepDefs
import Submission.Work.Cohomology.SmallChains

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The continuous surjection `Δᵖ → Y × Dᵖ` carrying `∂Δᵖ` onto `Y × Sᵖ⁻¹`

`Work.Whitney.ballPairVal` (`Submission/Work/Whitney/ballPairMapDefs.lean`) is the explicit
"cone" map of the standard `p`-simplex onto the closed unit ball of `ℝᵖ`, with `‖ballPairVal p z‖`
equal to the level `1 - (p+1)·minᵢ zᵢ`; it is continuous (`continuous_ballPairVal_simplex`) and
onto (`Work.Whitney.ballPairVal_surj`), and the level is `1` exactly on `∂Δᵖ`
(`ballPairVal_mem_sph_iff`).

Here the fibre coordinate is paired with a fixed point `y₀` of `Y` (which is a subsingleton, so the
pairing is onto as soon as the fibre coordinate is), producing the map of pairs
`(Δᵖ, ∂Δᵖ) → (Y × Dᵖ, DiscB Y p)` requested by `Work.Whitney.ballPairMap`.
-/

namespace Work.Whitney

open Work.Thom

theorem ballPairMap (Y : Type) [TopologicalSpace Y] [Subsingleton Y] [Nonempty Y]
    (p : ℕ) (hp : 1 ≤ p) :
    ∃ f : C(stdSimplex ℝ (Fin (p+1)), TopCat.of (Y × Work.Thom.MBall p)),
      (∀ (z : stdSimplex ℝ (Fin (p+1))),
          (∃ i : Fin (p+1), (z : Fin (p+1) → ℝ) i = 0) → f z ∈ Work.Thom.DiscB Y p)
      ∧ (∀ (z : stdSimplex ℝ (Fin (p+1))),
          (∀ i : Fin (p+1), (z : Fin (p+1) → ℝ) i ≠ 0) → f z ∉ Work.Thom.DiscB Y p)
      ∧ Function.Surjective f := by
  classical
  refine ⟨⟨fun z => (Classical.arbitrary Y,
    (⟨ballPairVal p (z : Fin (p+1) → ℝ), ballPairVal_mem_ball p z⟩ : Work.Thom.MBall p)),
    Continuous.prodMk continuous_const
      (Continuous.subtype_mk (continuous_ballPairVal_simplex p)
        (fun z => ballPairVal_mem_ball p z))⟩, ?_, ?_, ?_⟩
  · intro z hz
    show ballPairVal p (z : Fin (p+1) → ℝ) ∈ mSph p
    exact (ballPairVal_mem_sph_iff p z).mpr hz
  · intro z hz hsph
    obtain ⟨i, hi⟩ := (ballPairVal_mem_sph_iff p z).mp hsph
    exact hz i hi
  · intro q
    obtain ⟨z, hz⟩ := ballPairVal_surj p hp q.2
    refine ⟨z, ?_⟩
    have h1 : Classical.arbitrary Y = q.1 := Subsingleton.elim _ _
    have h2 : (⟨ballPairVal p (z : Fin (p+1) → ℝ),
        ballPairVal_mem_ball p z⟩ : Work.Thom.MBall p) = q.2 := hz
    show (Classical.arbitrary Y, (⟨ballPairVal p (z : Fin (p+1) → ℝ),
      ballPairVal_mem_ball p z⟩ : Work.Thom.MBall p)) = q
    rw [h1, h2]

end Work.Whitney
