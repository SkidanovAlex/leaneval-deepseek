import Mathlib
import Submission.Work.SSGRoute.H9.swHistChi_aux
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.H9

/-- **The stage-`m` class at a `k`-conjugate of the `l`-th escape prime that is not a
`K`-conjugate.**  At such a place `A` the accumulated datum of the history is `−χ_{b_l} − ½y`
(`Work.SSGRoute.H9.histDatumK_escape_block_sibling`, all the other corrections vanishing because the
escape primes have pairwise distinct `k`-places), so the realisation clause prescribes
`χ_m = ½y − χ_{b_l} − ½y = −χ_{b_l}`; this vanishes at the inertia as soon as the `l`-th class does. -/
theorem histChi_sibling_escape {p : ℕ} [Fact p.Prime] {k Ω : Type} [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] [IsAlgClosed Ω]
    (K N : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    [FiniteDimensional k N] [IsGalois k N]
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (S : Finset (ValuationSubring Ω)) (y : (Ω ≃ₐ[k] Ω) → ZMod p)
    (f : ℕ → (ValuationSubring Ω × (↥K)ˣ))
    (hf : Work.SSGRoute.H9.HistK (p := p) K N ζ hζ hζK S y f) (m : ℕ)
    {l : ℕ} (hlm : l < m) {A : ValuationSubring Ω}
    (hA : A ∈ Work.SSGRoute.H9.histPlacesK (p := p) K S ζ hζK hζ m f)
    (hAconj : SSGRoute.IsConjPlace k ((f l).1) A)
    (hnconj : ¬ Work.SSGRoute.gesKConj K ((f l).1) A)
    (hsep : ∀ j : ℕ, j ≠ l → ¬ SSGRoute.IsConjPlace k ((f j).1) A)
    {σ : Ω ≃ₐ[k] Ω} (hσK : σ ∈ K.fixingSubgroup) (hσI : SSGRoute.IsInertia k A σ)
    (hconf_l : Work.SSGRoute.H9.histChi K ζ hζK hζ f l σ = 0) :
    Work.SSGRoute.H9.histChi K ζ hζK hζ f m σ = 0 := by
  -- the realisation clause of the history at the block `A` of `T_m`
  have hreal := hf.2.2.2.2.1 m A hA σ (Subgroup.mem_inf.mpr ⟨hσI.1, hσK⟩)
  -- the accumulated datum at the sibling `A` of the `l`-th escape prime
  have hd := congrFun
    (histDatumK_escape_block_sibling (p := p) K S ζ hζ hζK y f m hlm hnconj hAconj hsep) σ
  -- unfold the stage-`m` class so that the realisation clause applies
  simp only [histChi] at hreal ⊢
  rw [hreal, hd]
  have hkey : (2 : ZMod p)⁻¹ * y σ + (- Work.SSGRoute.H9.histChi K ζ hζK hζ f l σ
      - (2 : ZMod p)⁻¹ * y σ) = - Work.SSGRoute.H9.histChi K ζ hζK hζ f l σ := by ring
  rw [hkey, hconf_l, neg_zero]

end Work.SSGRoute.H9
