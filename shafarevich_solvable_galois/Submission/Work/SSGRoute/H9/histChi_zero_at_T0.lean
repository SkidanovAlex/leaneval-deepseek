import Mathlib
import Submission.Work.SSGRoute.H9.swHistChi_aux
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.H9

/-- **The stage-`m` class kills the inertia at the `T₀`-blocks.**  At a representative `A` of a
`K`-class above `S` the accumulated datum of the history vanishes
(`Work.SSGRoute.H9.histDatumK_eq_zero_on_T0`), so the realisation clause prescribes the value `½y`
there, and `y` — hence `½y` — kills the inertia at every `k`-conjugate of a place of `S` (`hyT`). -/
theorem histChi_zero_at_T0 {p : ℕ} [Fact p.Prime] {k Ω : Type} [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] [IsAlgClosed Ω]
    (K N : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    [FiniteDimensional k N] [IsGalois k N]
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (S : Finset (ValuationSubring Ω)) (y : (Ω ≃ₐ[k] Ω) → ZMod p)
    (hyT : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (∃ A ∈ S, SSGRoute.IsConjPlace k A B) →
      ∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B σ → y σ = 0)
    (f : ℕ → (ValuationSubring Ω × (↥K)ˣ))
    (hf : Work.SSGRoute.H9.HistK (p := p) K N ζ hζ hζK S y f) (m : ℕ)
    {A : ValuationSubring Ω} (hA : A ∈ Work.SSGRoute.ZDataMup.kleadReps K S)
    (hAfin : SSGRoute.IsFinPlace k A)
    {σ : Ω ≃ₐ[k] Ω} (hσK : σ ∈ K.fixingSubgroup) (hσI : SSGRoute.IsInertia k A σ) :
    Work.SSGRoute.H9.histChi K ζ hζK hζ f m σ = 0 := by
  -- `A` is a block of the place set `T_m` of the history (it lies in `T₀ = kleadReps K S`)
  have hA' : A ∈ Work.SSGRoute.H9.histPlacesK (p := p) K S ζ hζK hζ m f := by
    simp only [histPlacesK, Work.SSGRoute.ZDataMup.histPlaces, Finset.mem_union]
    exact Or.inl hA
  -- the accumulated datum of the history vanishes at the `T₀`-blocks
  have hd : Work.SSGRoute.H9.histDatumK (p := p) K ζ hζK hζ S y m f A σ = 0 := by
    have h := congrFun (histDatumK_eq_zero_on_T0 K N S ζ hζ hζK y f hf m hA) σ
    simpa using h
  -- the realisation clause therefore prescribes the value `½y` at `A`
  have hval : Work.SSGRoute.H9.histChi K ζ hζK hζ f m σ = (2 : ZMod p)⁻¹ * y σ := by
    have h := hf.2.2.2.2.1 m A hA' σ (Subgroup.mem_inf.mpr ⟨hσI.1, hσK⟩)
    simp only [histChi]
    rw [h, hd, add_zero]
  -- and `y` kills the inertia at the `k`-conjugates of the places of `S`
  obtain ⟨A₀, hA₀, hconj⟩ := Work.SSGRoute.ZDataMup.kleadReps_mem_conjPlace (p := p) K hA
  have hy : y σ = 0 := hyT A hAfin ⟨A₀, hA₀, hconj⟩ σ hσK hσI
  rw [hval, hy, mul_zero]

end Work.SSGRoute.H9
