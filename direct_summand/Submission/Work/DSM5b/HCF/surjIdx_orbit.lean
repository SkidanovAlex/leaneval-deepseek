import Mathlib
import Submission.Work.DSM5b.HCF.SurjTopDefs

namespace Work.DSM5b.HCF

/-- Every bijection `σ : Fin (p+2) → S₀` (i.e. every element of the top-degree index type)
is a permutation of the positions of the increasing enumeration `incTupleE S₀ (p+1) hp`.

Route: `E := S₀.orderIsoOfFin hp.symm : Fin (p+2) ≃o ↥S₀` satisfies
`(incTupleE S₀ (p+1) hp).1 = fun i => (E i : Fin n)` (definitionally).
The map `f := fun i => (⟨σ.1 i, _⟩ : ↥S₀)` is surjective (because `tupRng σ.1 = S₀`) and hence
bijective (`Fintype.bijective_iff_surjective_and_card`, `Fintype.card_coe`, `hp`); take
`π := (Equiv.ofBijective f _).trans E.symm`. -/
theorem surjIdx_orbit {n : ℕ} (S₀ : Finset (Fin n)) (p : ℕ) (hp : p + 2 = S₀.card)
    (σ : Work.DSM5b.SurjIdx S₀ (p + 1)) :
    ∃ π : Equiv.Perm (Fin (p + 2)), σ.1 = (Work.DSM5b.incTupleE S₀ (p + 1) hp).1 ∘ π := by
  have hmem : ∀ i, σ.1 i ∈ S₀ := fun i => by
    have h : σ.1 i ∈ Work.DSM5b.tupRng σ.1 :=
      Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩
    rwa [σ.2] at h
  let f : Fin (p + 2) → ↥S₀ := fun i => ⟨σ.1 i, hmem i⟩
  have hf_surj : Function.Surjective f := by
    intro y
    have hy : y.1 ∈ Work.DSM5b.tupRng σ.1 := by rw [σ.2]; exact y.2
    obtain ⟨i, -, hi⟩ := Finset.mem_image.mp hy
    exact ⟨i, Subtype.ext hi⟩
  have hcard : Fintype.card (Fin (p + 2)) = Fintype.card ↥S₀ := by
    simp only [Fintype.card_fin, Fintype.card_coe]
    exact hp
  have hbij : Function.Bijective f :=
    (Fintype.bijective_iff_surjective_and_card f).mpr ⟨hf_surj, hcard⟩
  let E : Fin (p + 2) ≃o ↥S₀ := S₀.orderIsoOfFin hp.symm
  refine ⟨(Equiv.ofBijective f hbij).trans E.symm, ?_⟩
  have he : (Work.DSM5b.incTupleE S₀ (p + 1) hp).1 = (fun i => (E i : Fin n)) := rfl
  rw [he]
  funext j
  simp only [Function.comp_apply]
  rw [Equiv.trans_apply, Equiv.ofBijective_apply]
  exact (congrArg (fun z : ↥S₀ => (z : Fin n)) (OrderIso.apply_symm_apply E (f j))).symm

end Work.DSM5b.HCF
