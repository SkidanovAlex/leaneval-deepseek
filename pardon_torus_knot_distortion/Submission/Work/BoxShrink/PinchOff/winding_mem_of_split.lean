import Mathlib
import Submission.Work.BoxShrink.PinchOff.PairingData
import Submission.Work.BoxShrink.PinchOff.windingSpan_union_le_sup_of_alternatingPartitionData_general
import Submission.Work.PinchLemma3.ClosedDiscA.exists_functional_kernel_eq

/-!
# The winding vector of a split curve lies in the span of the two pieces

`Work.BoxShrink.PinchOff.winding_mem_of_split`: if a closed curve `γ` of a parametrised torus
`P` lies entirely in `A`, entirely in `B`, or splits into finitely many monochromatic arcs
alternating between `A` and `B` whose `A`-arcs close up inside `A ∩ B`, then its winding vector
lies in `WindingSpan P A ⊔ WindingSpan P B`.

This is the one-curve form of `windingSpan_union_le_sup_of_alternatingPartitionData_general`,
and the engine `winding_mem_of_alternatingPartitionData` does all the work: it produces the
conclusion for any `ℚ`-subspace `V ⊇ WindingSpan P A, WindingSpan P B` which is the kernel of a
linear functional on integer vectors.  Three cases of the two-dimensional subspace
`V = WindingSpan P A ⊔ WindingSpan P B` remain:

* `V = ⊤`: nothing to prove;
* `V = ⊥`: `V` is the kernel of the identity of `ℝ × ℝ` on integer vectors, so the engine with
  `ψ = id` gives `windingOf γ = 0`;
* otherwise `V` is a line and `exists_functional_kernel_eq` produces the functional.
-/

open LeanEval.KnotTheory.PardonDistortion Set

namespace Work.BoxShrink.PinchOff

noncomputable section

theorem winding_mem_of_split {P : Work.CoreTopology.ParamTorus} {A B : Set LeanEval.KnotTheory.PardonDistortion.R3}
    (hAc : A ⊆ P.carrier) (hBc : B ⊆ P.carrier)
    (γ : Work.CoreTopology.ClosedCurve P)
    (hsplit : (∀ t : ℝ, γ t ∈ A) ∨ (∀ t : ℝ, γ t ∈ B) ∨
      ∃ (k : ℕ) (_ : 0 < k) (s : ℕ → ℝ),
        s 0 ∈ Set.Ico 0 (2 * Real.pi) ∧ s (2 * k) = s 0 + 2 * Real.pi ∧
        (∀ i j, i ≤ 2 * k → j ≤ 2 * k → i < j → s i < s j) ∧
        (∀ j, j < k → ∀ t : ℝ, s (2 * j) ≤ t → t ≤ s (2 * j + 1) → γ t ∈ A) ∧
        (∀ j, j < k → ∀ t : ℝ, s (2 * j + 1) ≤ t → t ≤ s (2 * j + 2) → γ t ∈ B) ∧
        (∀ j, j < k → JoinedIn (A ∩ B) (γ (s (2 * j))) (γ (s (2 * j + 1))))) :
    (((Work.SurgeryInvariance.windingOf P γ).1 : ℚ), ((Work.SurgeryInvariance.windingOf P γ).2 : ℚ)) ∈
      Work.SurgeryInvariance.WindingSpan P A ⊔ Work.SurgeryInvariance.WindingSpan P B := by
  classical
  set W : Submodule ℚ (ℚ × ℚ) :=
    Work.SurgeryInvariance.WindingSpan P A ⊔ Work.SurgeryInvariance.WindingSpan P B with hW
  rcases hsplit with hA | hB | ⟨k, hk, s, hs0, hslast, hmono, hArcA, hArcB, hJoined⟩
  · exact Submodule.mem_sup_left (Submodule.subset_span ⟨γ, hA, rfl⟩)
  · exact Submodule.mem_sup_right (Submodule.subset_span ⟨γ, hB, rfl⟩)
  · -- the alternating case: the winding vector lies in every `V` which is the kernel of a
    -- linear functional on integer vectors and contains the two spans
    by_cases hbot : W = ⊥
    · -- `V = ⊥`: the identity of `ℝ × ℝ` is such a functional
      rw [hbot]
      have hVA : Work.SurgeryInvariance.WindingSpan P A ≤ (⊥ : Submodule ℚ (ℚ × ℚ)) :=
        hbot ▸ le_sup_left
      have hVB : Work.SurgeryInvariance.WindingSpan P B ≤ (⊥ : Submodule ℚ (ℚ × ℚ)) :=
        hbot ▸ le_sup_right
      have hψid : ∀ v : ℤ × ℤ,
          (((v.1 : ℚ), (v.2 : ℚ)) ∈ (⊥ : Submodule ℚ (ℚ × ℚ))) →
          (LinearMap.id : (ℝ × ℝ) →ₗ[ℝ] (ℝ × ℝ)) ((v.1 : ℝ), (v.2 : ℝ)) = 0 := by
        intro v hv
        have hv0 : (((v.1 : ℚ), (v.2 : ℚ)) : ℚ × ℚ) = 0 := (Submodule.mem_bot (R := ℚ)).mp hv
        have hvz : v = 0 :=
          (Work.SurgeryInvariance.intPair_cast_eq_zero_iff v).mp hv0
        rw [hvz]
        simp
      have hψid' : ∀ v : ℤ × ℤ,
          (LinearMap.id : (ℝ × ℝ) →ₗ[ℝ] (ℝ × ℝ)) ((v.1 : ℝ), (v.2 : ℝ)) = 0 →
          (((v.1 : ℚ), (v.2 : ℚ)) ∈ (⊥ : Submodule ℚ (ℚ × ℚ))) := by
        intro v hv
        have hv' : ((v.1 : ℝ), (v.2 : ℝ)) = 0 := hv
        have h1 : (v.1 : ℝ) = 0 := congrArg Prod.fst hv'
        have h2 : (v.2 : ℝ) = 0 := congrArg Prod.snd hv'
        have h1' : v.1 = 0 := by exact_mod_cast h1
        have h2' : v.2 = 0 := by exact_mod_cast h2
        rw [h1', h2']
        simp
      exact winding_mem_of_alternatingPartitionData hAc hBc
        (LinearMap.id : (ℝ × ℝ) →ₗ[ℝ] (ℝ × ℝ)) hψid hψid' hVA hVB γ hk hs0 hslast
        hmono hArcA hArcB hJoined
    · by_cases htop : W = ⊤
      · rw [htop]
        exact Submodule.mem_top
      · -- `V` is a line: `exists_functional_kernel_eq` produces the functional
        rcases Work.PinchLemma3.ClosedDiscA.exists_functional_kernel_eq W hbot htop with ⟨a', b', _hab, hker⟩
        let ψ : (ℝ × ℝ) →ₗ[ℝ] ℝ :=
          { toFun := fun p => (b' : ℝ) * p.1 - (a' : ℝ) * p.2
            map_add' := by intro p q; simp only [Prod.fst_add, Prod.snd_add]; ring
            map_smul' := by
              intro c p
              simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul, RingHom.id_apply]; ring }
        have hψ : ∀ w : ℤ × ℤ, (((w.1 : ℚ), (w.2 : ℚ)) ∈ W) →
            ψ ((w.1 : ℝ), (w.2 : ℝ)) = 0 := by
          intro w hw
          have h := (hker w).mp hw
          show (b' : ℝ) * (w.1 : ℝ) - (a' : ℝ) * (w.2 : ℝ) = 0
          exact_mod_cast h
        have hψ' : ∀ w : ℤ × ℤ, ψ ((w.1 : ℝ), (w.2 : ℝ)) = 0 →
            (((w.1 : ℚ), (w.2 : ℚ)) ∈ W) := by
          intro w hw
          refine (hker w).mpr ?_
          have h : (b' : ℝ) * (w.1 : ℝ) - (a' : ℝ) * (w.2 : ℝ) = 0 := hw
          exact_mod_cast h
        exact winding_mem_of_alternatingPartitionData hAc hBc ψ hψ hψ'
          le_sup_left le_sup_right γ hk hs0 hslast hmono hArcA hArcB hJoined

end

end Work.BoxShrink.PinchOff
