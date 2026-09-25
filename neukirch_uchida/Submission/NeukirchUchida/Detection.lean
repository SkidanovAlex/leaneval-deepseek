import Submission.NeukirchUchida.Conjugation
import Submission.NK.FieldTheory.Galois.stabilizer_iSup_eq_top
import Submission.NK.NeukirchUchida.isHomeomorph_conjHomEquiv

/-!
# The decomposition groups detect isomorphisms of absolute Galois groups

The local correspondence of CoNF XII §12.2 is used in the following form: an isomorphism of
absolute Galois groups is determined by what it does to the decomposition groups of the places of
the separable closure.  This is the "local to global" step of Neukirch's proof: the
decomposition groups *topologically generate* `G_K`
(`NK.FieldTheory.Galois.stabilizer_iSup_eq_top`, proved via Čebotarev-type input), so two
continuous isomorphisms agreeing on each of them agree everywhere.

The proof is compact: the set where two continuous isomorphisms agree is closed (it is the
preimage of the diagonal in `G × G`, a closed set in a Hausdorff space) and contains every
decomposition group, hence is everything.
-/

namespace Submission.NeukirchUchida

open scoped Pointwise

variable {K₁ K₂ K₁' K₂' : Type*} [Field K₁] [Field K₂] [Field K₁'] [Field K₂']
  [NumberField K₁] [NumberField K₂] [Algebra K₁ K₁'] [Algebra K₂ K₂']
  [IsSepClosure K₁ K₁'] [IsSepClosure K₂ K₂']

/-- **The decomposition groups detect isomorphisms.**  If two homeomorphic isomorphisms
`ϕ ψ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂)` agree on the decomposition group of every place of `K₁'` over a
finite prime of `K₁`, then they are equal. -/
theorem eq_of_eq_on_decompositionGroup (ϕ ψ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂))
    (hϕ : IsHomeomorph ϕ) (hψ : IsHomeomorph ψ)
    (h : ∀ A : ValuationSubring K₁', A.comap (algebraMap K₁ K₁') ≠ ⊤ →
      ∀ g : Gal(K₁'/K₁), A.comap (g : K₁' →+* K₁') = A → ϕ g = ψ g) : ϕ = ψ := by
  -- the set where `ϕ` and `ψ` agree, as a subgroup
  let H : Subgroup Gal(K₁'/K₁) :=
    { carrier := {g | ϕ g = ψ g}
      one_mem' := by show ϕ 1 = ψ 1; rw [map_one, map_one]
      mul_mem' := by
        intro a b ha hb
        show ϕ (a * b) = ψ (a * b)
        rw [map_mul, map_mul, ha, hb]
      inv_mem' := by
        intro a ha
        show ϕ a⁻¹ = ψ a⁻¹
        rw [map_inv, map_inv, ha] }
  have hHcoe : (H : Set Gal(K₁'/K₁)) = {g | ϕ g = ψ g} := rfl
  -- it is closed: the equaliser of two continuous maps into a Hausdorff space
  have hcl : IsClosed (H : Set Gal(K₁'/K₁)) := by
    rw [hHcoe]
    exact isClosed_eq hϕ.continuous hψ.continuous
  -- it contains every decomposition group, so it is everything
  have htop : H = ⊤ :=
    NK.FieldTheory.Galois.stabilizer_iSup_eq_top (K := K₁) (K' := K₁') H hcl
      (fun A hA g hg => h A hA g hg)
  refine MulEquiv.ext fun g => ?_
  have : g ∈ H := by rw [htop]; trivial
  exact this

/-- **The local realisation of a field isomorphism.**  If `σ : K₂' ≃+* K₁'` maps the base field
onto the base field and its conjugation agrees with `ϕ` on every decomposition group, then `σ`
induces `ϕ`, i.e. `Conjugates σ ϕ`. -/
theorem conjugates_of_eq_on_decompositionGroup {ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂)}
    {σ : K₂' ≃+* K₁'} (hσ : MapsBase (algebraMap K₁ K₁') (algebraMap K₂ K₂') σ)
    (hϕ : IsHomeomorph ϕ) (hconj : IsHomeomorph (conjHomEquiv hσ))
    (h : ∀ A : ValuationSubring K₁', A.comap (algebraMap K₁ K₁') ≠ ⊤ →
      ∀ g : Gal(K₁'/K₁), A.comap (g : K₁' →+* K₁') = A →
        (ϕ g : K₂' ≃+* K₂') = σ.trans (g.toRingEquiv.trans σ.symm)) :
    Conjugates σ ϕ := by
  refine ⟨hσ, fun g => ?_⟩
  have heq : ϕ = conjHomEquiv hσ :=
    eq_of_eq_on_decompositionGroup ϕ (conjHomEquiv hσ) hϕ hconj
      (fun A hA g hg => by
        have h1 : (ϕ g : K₂' ≃+* K₂') = σ.trans (g.toRingEquiv.trans σ.symm) := h A hA g hg
        have h2 : ((conjHomEquiv hσ) g : K₂' ≃+* K₂') =
            σ.trans (g.toRingEquiv.trans σ.symm) := conj_toRingEquiv hσ g
        ext y
        exact (congrArg (fun e : K₂' ≃+* K₂' => e y) h1).trans
          (congrArg (fun e : K₂' ≃+* K₂' => e y) h2).symm)
  have h1 : (ϕ g : K₂' ≃+* K₂') = ((conjHomEquiv hσ) g : K₂' ≃+* K₂') :=
    congrArg (fun e : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂) => (e g : K₂' ≃+* K₂')) heq
  exact h1.trans (conj_toRingEquiv hσ g)

open NK.NeukirchUchida in
/-- **The local realisation of a field isomorphism**, with the homeomorphism hypothesis on the
conjugation discharged by `NK.NeukirchUchida.isHomeomorph_conjHomEquiv`. -/
theorem conjugates_of_eq_on_decompositionGroup' {ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂)}
    {σ : K₂' ≃+* K₁'} (hσ : MapsBase (algebraMap K₁ K₁') (algebraMap K₂ K₂') σ)
    (hϕ : IsHomeomorph ϕ)
    (h : ∀ A : ValuationSubring K₁', A.comap (algebraMap K₁ K₁') ≠ ⊤ →
      ∀ g : Gal(K₁'/K₁), A.comap (g : K₁' →+* K₁') = A →
        (ϕ g : K₂' ≃+* K₂') = σ.trans (g.toRingEquiv.trans σ.symm)) :
    Conjugates σ ϕ :=
  conjugates_of_eq_on_decompositionGroup hσ hϕ
    (NK.NeukirchUchida.isHomeomorph_conjHomEquiv σ hσ) h

end Submission.NeukirchUchida
