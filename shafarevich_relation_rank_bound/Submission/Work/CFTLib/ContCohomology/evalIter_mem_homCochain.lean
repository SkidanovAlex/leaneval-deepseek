import Mathlib
import Submission.Work.CFTLib.ContCohomology.Setup

namespace Work.CFTLib.ContCohomology

variable {k Γ : Type} [CommRing k] [TopologicalSpace k] [Group Γ] [TopologicalSpace Γ]
  [IsTopologicalGroup Γ] [LocallyCompactSpace Γ]

/-- The iterated evaluation `evalIter` is jointly continuous in the element of the
`coind₁`-resolution and in the tuple of group elements. We prove it by induction on `n`; the
successor step uses that evaluation `C(Γ, V) × Γ → V` is continuous, which holds because `Γ` is
locally compact. -/
theorem continuous_evalIter (X : TopRep k Γ) (n : ℕ) :
    Continuous fun p : ↥(TopRep.resolutionX X n) × (Fin n → Γ) => evalIter X n p.1 p.2 := by
  induction n with
  | zero => exact continuous_fst
  | succ n ih =>
    have hg : Continuous fun p : ↥(TopRep.resolutionX X (n+1)) × (Fin (n+1) → Γ) =>
        (p.1 (p.2 0), Fin.tail p.2) := by
      refine Continuous.prodMk ?_ ?_
      · exact continuous_eval.comp
          (continuous_fst.prodMk ((continuous_apply 0).comp continuous_snd))
      · exact (continuous_pi fun j => continuous_apply (Fin.succ j)).comp continuous_snd
    have heq : (fun p : ↥(TopRep.resolutionX X (n+1)) × (Fin (n+1) → Γ) =>
          evalIter X (n+1) p.1 p.2)
        = (fun q : ↥(TopRep.resolutionX X n) × (Fin n → Γ) => evalIter X n q.1 q.2) ∘
          (fun p : ↥(TopRep.resolutionX X (n+1)) × (Fin (n+1) → Γ) =>
            (p.1 (p.2 0), Fin.tail p.2)) := by
      funext p; simp [evalIter_succ]
    rw [heq]
    exact ih.comp hg

/-- The iterated evaluation of an invariant element of the `coind₁`-resolution is an invariant
continuous function. -/
theorem evalIter_mem_homCochain
    {k Γ : Type} [CommRing k] [TopologicalSpace k] [Group Γ] [TopologicalSpace Γ]
    [IsTopologicalGroup Γ] [LocallyCompactSpace Γ]
    (X : TopRep k Γ) (n : ℕ) (Φ : ↥(TopRep.resolutionX X (n+1)))
    (hinv : Φ ∈ (TopRep.resolutionX X (n+1)).ρ.invariants) :
    (fun x : Fin (n+1) → Γ => Work.CFTLib.ContCohomology.evalIter X (n+1) Φ x)
      ∈ Work.CFTLib.ContCohomology.homCochain X n := by
  refine ⟨?_, ?_⟩
  · exact (continuous_evalIter X (n+1)).comp (continuous_const.prodMk continuous_id)
  · intro g x
    show evalIter X (n+1) Φ (fun i => g * x i) = X.ρ g (evalIter X (n+1) Φ x)
    have hφ : (TopRep.resolutionX X (n+1)).ρ g⁻¹ Φ = Φ :=
      (ContRepresentation.mem_invariants (π := (TopRep.resolutionX X (n+1)).ρ) Φ).mp hinv g⁻¹
    have hact := evalIter_act X (n+1) Φ g⁻¹ x
    rw [hφ, inv_inv] at hact
    have h3 : X.ρ g (X.ρ g⁻¹ (evalIter X (n+1) Φ (g • x)))
        = evalIter X (n+1) Φ (g • x) := by
      rw [← mul_apply_eq_comp, ← map_mul, mul_inv_cancel, map_one, one_apply_eq_self]
    rw [hact, h3]
    congr 1

end Work.CFTLib.ContCohomology
