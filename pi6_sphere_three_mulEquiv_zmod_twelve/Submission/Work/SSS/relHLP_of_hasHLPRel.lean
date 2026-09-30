import Mathlib
import Submission.Work.SSS.HornDefs

namespace Work.SSS

open scoped Topology unitInterval

/-- **The relative homotopy lifting property from the cube-wise relative HLP.**

`Work.StemsB.HasHLPRel p n` prescribes a lift on the "cup"
`L_n = (I^n × {0}) ∪ (∂I^n × I) ⊆ I^n × I`.  The relative HLP `Work.SSS.RelHLP p X A` prescribes
the lift on an arbitrary subspace `A ⊆ X`; for `X = I^n × I`, `A = L_n = Work.StemsB.LSet n` the
two conditions are the same: restrict the given partial lift `u : L_n → E` to the bottom face and
to the lateral boundary (they agree on their intersection, which is `∂I^n × {0}`). -/
theorem relHLP_of_hasHLPRel {E B : Type} [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E, B)) (n : ℕ) (h : Work.StemsB.HasHLPRel p n) :
    Work.SSS.RelHLP p ((Fin n → unitInterval) × unitInterval) (Work.StemsB.LSet n) := by
  intro v u hu
  -- The two constructions of the prescribed lift: on the bottom face resp. lateral boundary.
  let izero : C(Fin n → I, ↥(Work.StemsB.LSet n)) :=
    ⟨fun x => ⟨(x, 0), Or.inl rfl⟩,
      Continuous.subtype_mk (Work.StemsB.zeroIncl n).continuous (fun _ => Or.inl rfl)⟩
  let ibdry : C(Work.StemsB.CubeBdry n × I, ↥(Work.StemsB.LSet n)) :=
    ⟨fun y => ⟨(y.1.1, y.2), Or.inr y.1.2⟩,
      Continuous.subtype_mk (Work.StemsB.bdryIncl n).continuous (fun y => Or.inr y.1.2)⟩
  -- The composite lifts cover the corresponding inclusions into `I^n × I`.
  have hf : p.comp (u.comp izero) = v.comp (Work.StemsB.zeroIncl n) := by
    ext x
    exact DFunLike.congr_fun hu (izero x)
  have hg : p.comp (u.comp ibdry) = v.comp (Work.StemsB.bdryIncl n) := by
    ext y
    exact DFunLike.congr_fun hu (ibdry y)
  -- On the overlap `∂I^n × {0}` the two prescriptions agree.
  have hg0 : ∀ x : Work.StemsB.CubeBdry n, (u.comp ibdry) (x, 0) = (u.comp izero) x.1 := by
    intro x
    exact congrArg u (Subtype.ext rfl)
  obtain ⟨G, hG, hG0, hGlat⟩ := h v (u.comp izero) hf (u.comp ibdry) hg hg0
  refine ⟨G, hG, ?_⟩
  ext q
  show G q.1 = u q
  rcases q.2 with hq | hq
  · -- the point lies on the bottom face
    have hqe : q.1 = (q.1.1, (0 : I)) := Prod.ext rfl hq
    rw [hqe, hG0 q.1.1]
    exact congrArg u (Subtype.ext hqe.symm)
  · -- the point lies on the lateral boundary
    rw [show q.1 = (((⟨q.1.1, hq⟩ : Work.StemsB.CubeBdry n).1), q.1.2) from rfl,
      hGlat ⟨q.1.1, hq⟩ q.1.2]
    exact congrArg u (Subtype.ext rfl)

end Work.SSS
