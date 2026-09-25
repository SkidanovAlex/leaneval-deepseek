import Submission.NeukirchUchida.Conjugation

namespace Submission.NeukirchUchida

open scoped Topology

variable {K₁ K₂ K₁' K₂' : Type*} [Field K₁] [Field K₂] [Field K₁'] [Field K₂']
  [Algebra K₁ K₁'] [Algebra K₂ K₂']

/-- **Uniqueness, reduced to a centralizer statement.**  If every ring
automorphism `c` of `K₁'` which preserves the embedded copy of `K₁` and commutes
with `Gal(K₁'/K₁)` is the identity, then the field isomorphism inducing a given
isomorphism `ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂)` is unique. -/
theorem unique_sigma_of_centralizer_trivial
    (hC : ∀ c : K₁' ≃+* K₁', (∀ x ∈ (algebraMap K₁ K₁').range, c x ∈ (algebraMap K₁ K₁').range) →
      (∀ g : Gal(K₁'/K₁), c.trans (g.toRingEquiv.trans c.symm) = g.toRingEquiv) → c = 1)
    (ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂))
    {σ₁ σ₂ : K₂' ≃+* K₁'} (h₁ : Conjugates σ₁ ϕ) (h₂ : Conjugates σ₂ ϕ) : σ₁ = σ₂ := by
  let η : K₁' ≃+* K₁' := σ₁.symm.trans σ₂
  have hpres : ∀ x ∈ (algebraMap K₁ K₁').range, η x ∈ (algebraMap K₁ K₁').range := by
    intro x hx
    exact mapsBase_mem (algebraMap K₁ K₁') (algebraMap K₂ K₂') h₂.1
      (mapsBase_mem_symm (algebraMap K₁ K₁') (algebraMap K₂ K₂') h₁.1 hx)
  have hrel : ∀ (g : Gal(K₁'/K₁)) (y : K₂'), σ₁.symm (g (σ₁ y)) = σ₂.symm (g (σ₂ y)) := by
    intro g y
    have hEq : σ₁.trans (g.toRingEquiv.trans σ₁.symm) = σ₂.trans (g.toRingEquiv.trans σ₂.symm) :=
      (h₁.2 g).symm.trans (h₂.2 g)
    have h := congrArg (fun (e : K₂' ≃+* K₂') => e y) hEq
    simpa [RingEquiv.trans_apply] using h
  have hcomm : ∀ g : Gal(K₁'/K₁), η.trans (g.toRingEquiv.trans η.symm) = g.toRingEquiv := by
    intro g
    ext x
    show η.symm (g (η x)) = g x
    have hx : η x = σ₂ (σ₁.symm x) := rfl
    have hy : η.symm (g (σ₂ (σ₁.symm x))) = σ₁ (σ₂.symm (g (σ₂ (σ₁.symm x)))) := rfl
    rw [hx, hy, ← hrel g (σ₁.symm x)]
    simp
  have hη : η = 1 := hC η hpres hcomm
  have hcomp : σ₁.trans η = σ₂ := by
    ext x
    simp [η]
  have hone : σ₁.trans (1 : K₁' ≃+* K₁') = σ₁ := by
    ext x
    simp
  rw [hη] at hcomp
  rw [hone] at hcomp
  exact hcomp

end Submission.NeukirchUchida
