import Mathlib
import Submission.Work.ANALYTIC.Bounded

namespace Work.ANALYTIC

theorem boundedSeq_descend {X B : LightProfinite} (π : X ⟶ B)
    (hπ : ∀ y : B, ∃ x : X, π x = y) (a : boundedSeqSet X)
    (ha : ∀ (n : ℕ) (x y : X), π x = π y → a.1 n x = a.1 n y) :
    ∃ b : boundedSeqSet B, ∀ (n : ℕ) (x : X), b.1 n (π x) = a.1 n x := by
  classical
  have hsurj : Function.Surjective (π : X → B) := fun y => hπ y
  have hquot : Topology.IsQuotientMap (π : X → B) :=
    Topology.IsQuotientMap.of_surjective_continuous hsurj π.hom.hom.continuous
  -- a choice of preimage for every point of `B`
  let c : B → X := fun y => Classical.choose (hπ y)
  have hc : ∀ y : B, π (c y) = y := fun y => Classical.choose_spec (hπ y)
  -- the descended candidate is constant on the fibres of `π`
  have hcomp : ∀ n : ℕ,
      (fun y : B => a.1 n (c y)) ∘ (π : X → B) = fun x : X => a.1 n x := by
    intro n
    funext x
    exact ha n (c (π x)) x (hc (π x))
  -- hence it is continuous, because `π` is a quotient map
  have hcont : ∀ n : ℕ, Continuous (fun y : B => a.1 n (c y)) := by
    intro n
    refine (Topology.IsQuotientMap.continuous_iff hquot).mpr ?_
    rw [hcomp n]
    exact (a.1 n).continuous
  obtain ⟨N, hN⟩ := a.2
  refine ⟨⟨fun n => ⟨fun y => a.1 n (c y), hcont n⟩, ⟨N, fun n y => hN n (c y)⟩⟩, ?_⟩
  intro n x
  exact congrFun (hcomp n) x

end Work.ANALYTIC
