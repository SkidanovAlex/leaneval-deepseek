import Mathlib
import Submission.NK.LocalReciprocityLubinTate.Eval.TorsionRing

open scoped ValuativeRel

namespace NK.LocalReciprocityLubinTate.Eval

universe u

/-- A ring homomorphism `R → S` which sends the ideal `I` into the ideal `J` is continuous for the
`I`-adic topology on `R` and the `J`-adic topology on `S`.  (Only the additive structure is used,
via `continuous_of_continuousAt_zero`, so it suffices to check continuity at `0`, where the adic
neighbourhood bases are the powers of `I` and `J`.) -/
theorem continuous_algebraMap_adicTopology_of_map_le {R S : Type*} [CommRing R] [CommRing S]
    [Algebra R S] (I : Ideal R) (J : Ideal S)
    (h : I.map (algebraMap R S : R →+* S) ≤ J) :
    @Continuous R S I.adicTopology J.adicTopology (algebraMap R S) := by
  letI : TopologicalSpace R := I.adicTopology
  letI : TopologicalSpace S := J.adicTopology
  haveI : IsTopologicalRing R := (Ideal.nonarchimedean I).toIsTopologicalRing
  haveI : IsTopologicalRing S := (Ideal.nonarchimedean J).toIsTopologicalRing
  refine continuous_of_continuousAt_zero (algebraMap R S : R →+* S) ?_
  rw [ContinuousAt]
  simp only [map_zero]
  rw [(I.hasBasis_nhds_zero_adic).tendsto_iff (J.hasBasis_nhds_zero_adic)]
  intro m _
  refine ⟨m, trivial, fun y hy => ?_⟩
  have hmap : (I ^ m).map (algebraMap R S : R →+* S) ≤ J ^ m := by
    rw [Ideal.map_pow]
    exact Ideal.pow_right_mono h m
  exact hmap (Ideal.mem_map_of_mem (algebraMap R S : R →+* S) hy)

/-- The structure map `𝒪[F] → 𝒪[F][T]/(f^{(n)}(T))` is continuous for the `(π)`-adic topology on
`𝒪[F]` and the `𝔪[F]`-adic topology on the ambient ring of the Lubin–Tate torsion-point
evaluation.  Indeed the defining ideal `(π)` of the source is mapped to the defining ideal
`(π) = (π̄)` of the target. -/
theorem continuous_algebraMap_ltTorsionRing {F : Type u} [Field F] [ValuativeRel F]
    (π : ↥(ValuativeRel.valuation F).integer) (q n : ℕ) :
    @Continuous (↥(ValuativeRel.valuation F).integer)
      (NK.LocalReciprocityLubinTate.Eval.LTtorsionRing F π q n)
      (NK.LocalReciprocityLubinTate.Eval.adicTopologyO π)
      (NK.LocalReciprocityLubinTate.Eval.instTopologicalSpace π q n)
      (algebraMap (↥(ValuativeRel.valuation F).integer)
        (NK.LocalReciprocityLubinTate.Eval.LTtorsionRing F π q n)) := by
  have h : (Ideal.span ({π} : Set (O F))).map
      (algebraMap (O F) (LTtorsionRing F π q n) : O F →+* LTtorsionRing F π q n) ≤
      LTtorsionRing.adicIdeal π q n := by
    rw [LTtorsionRing.adicIdeal, Ideal.map_span]
    rw [show (algebraMap (O F) (LTtorsionRing F π q n)) '' ({π} : Set (O F))
        = {LTtorsionRing.piT π q n} from by
      rw [Set.image_singleton]; rfl]
  exact continuous_algebraMap_adicTopology_of_map_le _ _ h

end NK.LocalReciprocityLubinTate.Eval
