import Mathlib
import Submission.Work.SSGRoute.ZDataTwo.TwoRec.PreTwo_step
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Existence of the history of the `p = 2` §4 recursion

`Work.SSGRoute.ZDataTwo.TwoRec.preTwoExists`: the one-stage step `TwoRec.PreTwo_step` iterated by
`Nat.rec`, producing a history satisfying the prefix invariant `TwoRec.PreTwo` at every stage.  This
is the `p = 2` mirror of the final argument of
`Work.SSGRoute.H9.swHistKExists_proved`
(`Submission/Work/SSGRoute/H9/swHistKExists_proved.lean`).
-/

open scoped Pointwise

namespace Work.SSGRoute.ZDataTwo.TwoRec

open _root_.SSGRoute

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 2000000

variable {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
  [IsAlgClosed Ω]
variable {K : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K] [NumberField ↥K]
  [IsSepClosure ↥K Ω]

/-- **The prefix invariant holds at every stage.**  Iterating the one-stage step `PreTwo_step`. -/
theorem preTwoExists {Λ : IntermediateField k Ω} [FiniteDimensional k Λ] [IsGalois k Λ]
    (hKΛ : K ≤ Λ)
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ 2) (hζK : ζ ∈ K)
    (S : Finset (ValuationSubring Ω)) (hSfin : ∀ A ∈ S, SSGRoute.IsFinPlace k A)
    (hSram : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (SSGRoute.IsRamifiedIn k Λ B ∨ B.valuation (2 : Ω) < 1) →
      ∃ A ∈ S, SSGRoute.IsConjPlace k A B)
    (y : (Ω ≃ₐ[k] Ω) → ZMod 2)
    (hy : ∀ g ∈ K.fixingSubgroup, ∀ h ∈ K.fixingSubgroup, y (g * h) = y g + y h)
    (hyc : SSGRoute.IsLocConstOn K.fixingSubgroup y)
    (hyS : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (∀ A ∈ S, ¬ SSGRoute.IsConjPlace k A B) → ¬ SSGRoute.IsSplitIn k Λ B →
      ∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B σ → y σ = 0)
    (hyT : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (∃ A ∈ S, SSGRoute.IsConjPlace k A B) →
      ∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B σ → y σ = 0)
    (hyinf : ∀ c ∈ K.fixingSubgroup, c ^ 2 = 1 → y c = 0)
    (O : Oracle (K := K) Λ ζ hζ hζK) :
    ∃ s : St (k := k) (Ω := Ω) (K := K),
      ∀ n, PreTwo (K := K) Λ ζ hζ hζK S y n s := by
  classical
  have hstep : ∀ (n : ℕ) (s : St (k := k) (Ω := Ω) (K := K)),
      PreTwo (K := K) Λ ζ hζ hζK S y n s →
      ∃ s' : St (k := k) (Ω := Ω) (K := K), (∀ m < n, s'.f m = s.f m) ∧
        PreTwo (K := K) Λ ζ hζ hζK S y (n + 1) s' :=
    fun n s hs => PreTwo_step (K := K) hKΛ ζ hζ hζK S hSfin hSram y hy hyc hyS hyT hyinf O hs
  have hbase : PreTwo (K := K) Λ ζ hζ hζK S y 0
      ⟨fun _ => (default : ValuationSubring Ω × (↥K)ˣ)⟩ := by
    refine ⟨fun m hm => absurd hm (Nat.not_lt_zero m), fun m hm => absurd hm (Nat.not_lt_zero m),
      fun m l hml hl => absurd hl (Nat.not_lt_zero l),
      fun m l hml hl => absurd hl (Nat.not_lt_zero l), fun m hm => absurd hm (Nat.not_lt_zero m),
      fun m hm => absurd hm (Nat.not_lt_zero m), fun m hm => absurd hm (Nat.not_lt_zero m),
      fun m hm => absurd hm (Nat.not_lt_zero m), fun m hm => absurd hm (Nat.not_lt_zero m)⟩
  let seq : (n : ℕ) → {s : St (k := k) (Ω := Ω) (K := K) //
      PreTwo (K := K) Λ ζ hζ hζK S y n s} :=
    Nat.rec (motive := fun n => {s : St (k := k) (Ω := Ω) (K := K) //
        PreTwo (K := K) Λ ζ hζ hζK S y n s})
      ⟨⟨fun _ => (default : ValuationSubring Ω × (↥K)ˣ)⟩, hbase⟩
      (fun n ih => ⟨Classical.choose (hstep n ih.1 ih.2),
        (Classical.choose_spec (hstep n ih.1 ih.2)).2⟩)
  let F : ℕ → (ValuationSubring Ω × (↥K)ˣ) := fun m => (seq (m + 1)).1.f m
  have hagree : ∀ n i, i < n → (seq n).1.f i = F i := by
    intro n
    induction n with
    | zero => intro i hi; exact absurd hi (Nat.not_lt_zero i)
    | succ n ih =>
      intro i hi
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | hi
      · have hupd := (Classical.choose_spec (hstep n (seq n).1 (seq n).2)).1 i hi
        rw [show (seq (n + 1)).1 = Classical.choose (hstep n (seq n).1 (seq n).2) from rfl]
        rw [hupd]
        exact ih i hi
      · rw [hi]
  refine ⟨⟨F⟩, fun n => ?_⟩
  have hcongr : ∀ i < n, (seq n).1.f i = F i := fun i hi => hagree n i hi
  exact PreTwo_congr (K := K) (ζ := ζ) (hζ := hζ) (hζK := hζK)
    (fun i hi => (hcongr i hi).symm) (seq n).2

end Work.SSGRoute.ZDataTwo.TwoRec
