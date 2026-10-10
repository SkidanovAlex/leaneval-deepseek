import Mathlib.RingTheory.Henselian
import Mathlib.Algebra.Field.ZMod
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.Valuation.ValuationSubring
import Submission.Work.SSGRoute.H9.swHistChi_aux
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.H9

/-- **Conjugation invariance of the Kummer cochain on `K.fixingSubgroup`.**  The level-`K` Kummer
cochain of `b ∈ Kˣ` is invariant under conjugation by `K.fixingSubgroup`
(`Work.SSGRoute.ZDataMup.nodeKummerCocharZMod_conj`), so a vanishing at `τ⁻¹ σ τ` transports to a
vanishing at `σ`. -/
theorem histChi_conj_transport {p : ℕ} [Fact p.Prime] {k Ω : Type} [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] [IsAlgClosed Ω]
    (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (f : ℕ → (ValuationSubring Ω × (↥K)ˣ)) (m : ℕ)
    {τ σ : Ω ≃ₐ[k] Ω} (hτ : τ ∈ K.fixingSubgroup)
    (hzero : Work.SSGRoute.H9.histChi K ζ hζK hζ f m (τ⁻¹ * σ * τ) = 0) :
    Work.SSGRoute.H9.histChi K ζ hζK hζ f m σ = 0 := by
  have hτ' : τ⁻¹ ∈ K.fixingSubgroup := K.fixingSubgroup.inv_mem hτ
  have h := Work.SSGRoute.ZDataMup.nodeKummerCocharZMod_conj K ζ hζ hζK (f m).2 hτ' σ
  simp only [inv_inv] at h
  simp only [histChi]
  rw [← h]
  exact hzero

end Work.SSGRoute.H9
